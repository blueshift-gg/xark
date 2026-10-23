//! A wasm interpreter whose values may be *symbolic*.
//!
//! Concrete values (constants, loop counters, indices, addresses) execute exactly
//! as wasm specifies. A value derived from a witness is a [`Sym`]: a wire (a
//! `{0,1}` comparison result, a range-checked `uN` input) or a select between two
//! values on a witness `bool` ([`Sym::Ite`]). `Field` values never need this: the
//! host hands them out as concrete handles (see `host.rs`), so they flow through
//! memory and locals as plain bytes.
//!
//! A branch on a symbolic `bool` runs **both** paths from the branch to the point
//! where they rejoin (the exit of the innermost block both leave), recording each
//! path's memory writes in a journal and undoing them, then merges the two states:
//! every value that differs becomes `Ite(cond, then, else)`. The host turns an
//! `Ite` into a mux constraint when an intrinsic reads it. Each path runs under a
//! guard (the host's `arm_begin`/`arm_end`): its requirements hold only when it is
//! taken and its hints are pinned to 0 when it isn't (see the frontend README). An
//! arm that can only panic is pruned by requiring the condition to the other way.

use std::collections::HashMap;

use wasmparser::{
    BlockType, CompositeInnerType, DataKind, ElementItems, ElementKind, ExternalKind, Operator,
    Parser, Payload, TypeRef, ValType,
};

use crate::error::{CompileError, CompileResult};

// ---------------------------------------------------------------------------
// Values
// ---------------------------------------------------------------------------

/// A wasm value: concrete bits (`i32` zero-extended, `f32`/`f64` raw bits) or, when
/// `s != 0`, the symbolic value `syms[s]` (the bits are then meaningless).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct V {
    pub b: u64,
    pub s: u32,
}

impl V {
    #[inline]
    pub const fn c(b: u64) -> V {
        V { b, s: 0 }
    }
    #[inline]
    pub const fn i32(x: u32) -> V {
        V { b: x as u64, s: 0 }
    }
    #[inline]
    pub fn is_sym(self) -> bool {
        self.s != 0
    }
}

/// A symbolic value.
#[derive(Clone, Debug)]
pub enum Sym {
    /// Placeholder for id 0 (concrete).
    None,
    /// An integer wire whose value is `< 2^width` — opaque to the interpreter;
    /// the host knows its linear combination (`id` indexes the host's table).
    Wire { id: u32, width: u32 },
    /// `cond ? t : e`, `cond` a `{0,1}` wire.
    Ite { cond: u32, t: V, e: V },
    /// Little-endian bytes mixed from several values (a word-sized load that
    /// spans byte-sized witnesses): each byte concrete or a byte of a symbolic value.
    Bytes(Vec<(u8, Option<SymByte>)>),
}

// ---------------------------------------------------------------------------
// Module
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq)]
enum Ty {
    I32,
    I64,
    F32,
    F64,
}

fn ty_of(v: ValType) -> CompileResult<Ty> {
    Ok(match v {
        ValType::I32 => Ty::I32,
        ValType::I64 => Ty::I64,
        ValType::F32 => Ty::F32,
        ValType::F64 => Ty::F64,
        other => {
            return Err(CompileError::new(format!(
                "unsupported wasm value type {other:?}"
            )));
        }
    })
}

#[derive(Clone, Debug, PartialEq)]
struct FuncType {
    params: Vec<Ty>,
    results: Vec<Ty>,
}

#[derive(Clone, Copy, Debug)]
enum Mem {
    I32,
    I64,
    F32,
    F64,
    I32_8S,
    I32_8U,
    I32_16S,
    I32_16U,
    I64_8S,
    I64_8U,
    I64_16S,
    I64_16U,
    I64_32S,
    I64_32U,
}

impl Mem {
    fn size(self) -> u32 {
        match self {
            Mem::I32 | Mem::F32 | Mem::I64_32S | Mem::I64_32U => 4,
            Mem::I64 | Mem::F64 => 8,
            Mem::I32_8S | Mem::I32_8U | Mem::I64_8S | Mem::I64_8U => 1,
            Mem::I32_16S | Mem::I32_16U | Mem::I64_16S | Mem::I64_16U => 2,
        }
    }
}

/// Decoded instruction. Branch targets are resolved to code offsets up front.
#[derive(Clone, Debug)]
enum Op {
    Unreachable,
    Nop,
    /// `end_pc` is the index of the matching `End`; `arity` the block's result count.
    Block {
        end_pc: u32,
        params: u16,
        arity: u16,
    },
    Loop {
        params: u16,
    },
    If {
        else_pc: u32,
        end_pc: u32,
        params: u16,
        arity: u16,
    },
    Else {
        end_pc: u32,
    },
    End,
    Br(u32),
    BrIf(u32),
    BrTable(u32), // index into `Func::tables`
    Return,
    Call(u32),
    CallIndirect(u32),
    Drop,
    Select,
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),
    GlobalGet(u32),
    GlobalSet(u32),
    Load(Mem, u32),
    Store(Mem, u32),
    MemorySize,
    MemoryGrow,
    MemoryCopy,
    MemoryFill,
    Const(u64),
    // i32
    I32Eqz,
    I32Bin(Bin),
    I32Cmp(Cmp),
    I32Un(Un),
    // i64
    I64Eqz,
    I64Bin(Bin),
    I64Cmp(Cmp),
    I64Un(Un),
    // conversions
    I32WrapI64,
    I64ExtendI32S,
    I64ExtendI32U,
    I32Extend8S,
    I32Extend16S,
    I64Extend8S,
    I64Extend16S,
    I64Extend32S,
    // floats (rarely reached; supported for completeness)
    FBin(bool, FBin),
    FCmp(bool, FCmp),
    FUn(bool, FUn),
    FConvert(Conv),
    // Fused sequences (the first op of a straight-line run; the rest stay as-is
    // and are skipped). Branches only target block boundaries, never inside one.
    /// `local.get x; <load kind off>`.
    LoadL(u32, Mem, u32),
    /// `local.get a; local.get v; <store kind off>`.
    StoreLL(u32, u32, Mem, u32),
    /// `local.get x; i32.const c; i32.add`.
    AddLC(u32, u32),
    /// `local.get a; local.get x; <load k1 o1>; <store k2 o2>` — a memory-to-memory
    /// word copy (how a `Field` moves, limb by limb): `(a, x, k1, k2, o1, o2)`.
    CopyLL(u32, u32, Mem, Mem, u16, u16),
    /// `n` consecutive `CopyLL(a, x, I64, I64, o1 ± 8k, o2 ± 8k)` (`k = 0..n`; `−`
    /// when `desc`) — a whole `Field` copied word by word: `(a, x, o1, o2, n, desc)`.
    CopyN(u32, u32, u16, u16, u8, bool),
    /// `local.get l₀ … local.get lₙ₋₁; call f` (`n ≤ 3`): `(f, n, [l₀, l₁, l₂])`.
    CallL(u32, u8, [u16; 3]),
    /// `global.get g; i32.const c; i32.sub; local.tee l; global.set g` — a stack
    /// frame's prologue: `(g, c, l)`.
    SpSub(u32, u32, u32),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum Bin {
    Add,
    Sub,
    Mul,
    DivS,
    DivU,
    RemS,
    RemU,
    And,
    Or,
    Xor,
    Shl,
    ShrS,
    ShrU,
    Rotl,
    Rotr,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum Cmp {
    Eq,
    Ne,
    LtS,
    LtU,
    GtS,
    GtU,
    LeS,
    LeU,
    GeS,
    GeU,
}

#[derive(Clone, Copy, Debug)]
enum Un {
    Clz,
    Ctz,
    Popcnt,
}

#[derive(Clone, Copy, Debug)]
enum FBin {
    Add,
    Sub,
    Mul,
    Div,
    Min,
    Max,
    Copysign,
}

#[derive(Clone, Copy, Debug)]
enum FCmp {
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
}

#[derive(Clone, Copy, Debug)]
enum FUn {
    Abs,
    Neg,
    Sqrt,
    Ceil,
    Floor,
    Trunc,
    Nearest,
}

#[derive(Clone, Copy, Debug)]
enum Conv {
    I32TruncF32S,
    I32TruncF32U,
    I32TruncF64S,
    I32TruncF64U,
    I64TruncF32S,
    I64TruncF32U,
    I64TruncF64S,
    I64TruncF64U,
    F32ConvertI32S,
    F32ConvertI32U,
    F32ConvertI64S,
    F32ConvertI64U,
    F64ConvertI32S,
    F64ConvertI32U,
    F64ConvertI64S,
    F64ConvertI64U,
    F32DemoteF64,
    F64PromoteF32,
    I32ReinterpretF32,
    I64ReinterpretF64,
    F32ReinterpretI32,
    F64ReinterpretI64,
    I32TruncSatF32S,
    I32TruncSatF32U,
    I32TruncSatF64S,
    I32TruncSatF64U,
    I64TruncSatF32S,
    I64TruncSatF32U,
    I64TruncSatF64S,
    I64TruncSatF64U,
}

struct Func {
    ty: u32,
    n_locals: u32, // excluding params
    code: Vec<Op>,
    /// `br_table` target lists (label depths, default last).
    tables: Vec<Vec<u32>>,
    /// Per op (pre-fusion index), its byte offset in the module, for mapping a pc
    /// to source (DWARF).
    offsets: Vec<u32>,
}

pub struct Import {
    pub module: String,
    pub name: String,
    ty: u32,
}

pub struct Module {
    types: Vec<FuncType>,
    pub imports: Vec<Import>,
    funcs: Vec<Func>,
    globals: Vec<u64>,
    mem_pages: u32,
    data: Vec<(u32, Vec<u8>)>,
    table: Vec<Option<u32>>,
    exports: HashMap<String, u32>,
    /// Function index → name (from the `name` section), for diagnostics.
    names: HashMap<u32, String>,
    /// The `#[circuit]` fn's name (the `xark.entry` custom section).
    pub entry: Option<String>,
    /// Byte offset of the code section's contents (DWARF addresses are relative to it).
    pub code_start: u32,
    /// DWARF custom sections (`.debug_info`, `.debug_line`, …), when built with them.
    pub debug_sections: HashMap<String, Vec<u8>>,
}

fn const_expr(r: wasmparser::ConstExpr<'_>) -> CompileResult<u64> {
    let mut ops = r.get_operators_reader();
    let op = ops.read().map_err(werr)?;
    Ok(match op {
        Operator::I32Const { value } => value as u32 as u64,
        Operator::I64Const { value } => value as u64,
        other => {
            return Err(CompileError::new(format!(
                "unsupported constant expression {other:?}"
            )));
        }
    })
}

fn werr(e: wasmparser::BinaryReaderError) -> CompileError {
    CompileError::new(format!("malformed circuit module: {e}"))
}

impl Module {
    pub fn parse(bytes: &[u8]) -> CompileResult<Module> {
        let mut m = Module {
            types: Vec::new(),
            imports: Vec::new(),
            funcs: Vec::new(),
            globals: Vec::new(),
            mem_pages: 0,
            data: Vec::new(),
            table: Vec::new(),
            exports: HashMap::new(),
            names: HashMap::new(),
            entry: None,
            code_start: 0,
            debug_sections: HashMap::new(),
        };
        let mut func_types: Vec<u32> = Vec::new();
        let mut code_i = 0usize;
        for payload in Parser::new(0).parse_all(bytes) {
            match payload.map_err(werr)? {
                Payload::TypeSection(r) => {
                    for rg in r {
                        for sub in rg.map_err(werr)?.into_types() {
                            match &sub.composite_type.inner {
                                CompositeInnerType::Func(ft) => m.types.push(FuncType {
                                    params: ft
                                        .params()
                                        .iter()
                                        .map(|&t| ty_of(t))
                                        .collect::<CompileResult<_>>()?,
                                    results: ft
                                        .results()
                                        .iter()
                                        .map(|&t| ty_of(t))
                                        .collect::<CompileResult<_>>()?,
                                }),
                                _ => return Err(CompileError::new("unsupported wasm GC type")),
                            }
                        }
                    }
                }
                Payload::ImportSection(r) => {
                    for imp in r {
                        let imp = imp.map_err(werr)?;
                        match imp.ty {
                            TypeRef::Func(ty) => m.imports.push(Import {
                                module: imp.module.to_string(),
                                name: imp.name.to_string(),
                                ty,
                            }),
                            _ => {
                                return Err(CompileError::new(format!(
                                    "unsupported import `{}.{}` (only functions)",
                                    imp.module, imp.name
                                )));
                            }
                        }
                    }
                }
                Payload::FunctionSection(r) => {
                    for t in r {
                        func_types.push(t.map_err(werr)?);
                    }
                }
                Payload::TableSection(r) => {
                    for t in r {
                        let t = t.map_err(werr)?;
                        m.table = vec![None; t.ty.initial as usize];
                    }
                }
                Payload::MemorySection(r) => {
                    for mem in r {
                        m.mem_pages = mem.map_err(werr)?.initial as u32;
                    }
                }
                Payload::GlobalSection(r) => {
                    for g in r {
                        m.globals.push(const_expr(g.map_err(werr)?.init_expr)?);
                    }
                }
                Payload::ExportSection(r) => {
                    for e in r {
                        let e = e.map_err(werr)?;
                        if e.kind == ExternalKind::Func {
                            m.exports.insert(e.name.to_string(), e.index);
                        }
                    }
                }
                Payload::ElementSection(r) => {
                    for el in r {
                        let el = el.map_err(werr)?;
                        if let ElementKind::Active { offset_expr, .. } = el.kind {
                            let off = const_expr(offset_expr)? as usize;
                            if let ElementItems::Functions(fs) = el.items {
                                for (i, f) in fs.into_iter().enumerate() {
                                    let f = f.map_err(werr)?;
                                    if off + i >= m.table.len() {
                                        m.table.resize(off + i + 1, None);
                                    }
                                    m.table[off + i] = Some(f);
                                }
                            }
                        }
                    }
                }
                Payload::DataSection(r) => {
                    for d in r {
                        let d = d.map_err(werr)?;
                        if let DataKind::Active { offset_expr, .. } = d.kind {
                            m.data
                                .push((const_expr(offset_expr)? as u32, d.data.to_vec()));
                        }
                    }
                }
                Payload::CodeSectionEntry(body) => {
                    let ty = func_types[code_i];
                    code_i += 1;
                    let mut n_locals = 0u32;
                    for l in body.get_locals_reader().map_err(werr)? {
                        let (n, t) = l.map_err(werr)?;
                        ty_of(t)?;
                        n_locals += n;
                    }
                    let (code, tables, offsets) = decode_body(&m.types, body)?;
                    m.funcs.push(Func {
                        ty,
                        n_locals,
                        code,
                        tables,
                        offsets,
                    });
                }
                Payload::CodeSectionStart { range, .. } => m.code_start = range.start as u32,
                Payload::CustomSection(c) => {
                    if c.name().starts_with(".debug_") {
                        m.debug_sections
                            .insert(c.name().to_string(), c.data().to_vec());
                    }
                    if c.name() == "xark.entry" {
                        m.entry = Some(String::from_utf8_lossy(c.data()).into_owned());
                    }
                    if let wasmparser::KnownCustom::Name(n) = c.as_known() {
                        for sub in n {
                            if let Ok(wasmparser::Name::Function(map)) = sub {
                                for naming in map.into_iter().flatten() {
                                    m.names.insert(naming.index, naming.name.to_string());
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        Ok(m)
    }

    /// Code-section-relative address of the op just before `pc` in function `f`
    /// (`pc` as [`Machine::call_stack`] reports it); `None` for imports.
    pub fn address(&self, f: u32, pc: u32) -> Option<u64> {
        let func = self
            .funcs
            .get(f.checked_sub(self.imports.len() as u32)? as usize)?;
        let off = *func.offsets.get(pc.checked_sub(1)? as usize)?;
        Some(off.checked_sub(self.code_start)? as u64)
    }

    pub fn func_name(&self, f: u32) -> String {
        self.names
            .get(&f)
            .cloned()
            .unwrap_or_else(|| format!("func[{f}]"))
    }
}

fn block_arity(types: &[FuncType], bt: BlockType) -> (u16, u16) {
    match bt {
        BlockType::Empty => (0, 0),
        BlockType::Type(_) => (0, 1),
        BlockType::FuncType(i) => {
            let t = &types[i as usize];
            (t.params.len() as u16, t.results.len() as u16)
        }
    }
}

type Decoded = (Vec<Op>, Vec<Vec<u32>>, Vec<u32>);

fn decode_body(types: &[FuncType], body: wasmparser::FunctionBody<'_>) -> CompileResult<Decoded> {
    let mut code: Vec<Op> = Vec::new();
    let mut offsets: Vec<u32> = Vec::new();
    let mut tables: Vec<Vec<u32>> = Vec::new();
    // Open blocks: index of their opening op (Block/If/Loop) for end patching.
    let mut open: Vec<usize> = Vec::new();
    use Operator as O;
    let mut ops = body.get_operators_reader().map_err(werr)?;
    while !ops.eof() {
        let (op, offset) = ops.read_with_offset().map_err(werr)?;
        offsets.push(offset as u32);
        let pc = code.len();
        let d = match op {
            O::Unreachable => Op::Unreachable,
            O::Nop => Op::Nop,
            O::Block { blockty } => {
                open.push(pc);
                let (params, arity) = block_arity(types, blockty);
                Op::Block {
                    end_pc: 0,
                    params,
                    arity,
                }
            }
            O::Loop { blockty } => {
                open.push(pc);
                let (params, _) = block_arity(types, blockty);
                Op::Loop { params }
            }
            O::If { blockty } => {
                open.push(pc);
                let (params, arity) = block_arity(types, blockty);
                Op::If {
                    else_pc: 0,
                    end_pc: 0,
                    params,
                    arity,
                }
            }
            O::Else => {
                let at = *open.last().expect("else inside if");
                if let Op::If { else_pc, .. } = &mut code[at] {
                    *else_pc = pc as u32;
                }
                Op::Else { end_pc: 0 }
            }
            O::End => {
                if let Some(at) = open.pop() {
                    let end = pc as u32;
                    match &mut code[at] {
                        Op::Block { end_pc, .. } => *end_pc = end,
                        Op::If {
                            else_pc, end_pc, ..
                        } => {
                            *end_pc = end;
                            if *else_pc != 0 {
                                let e = *else_pc as usize;
                                if let Op::Else { end_pc } = &mut code[e] {
                                    *end_pc = end;
                                }
                            }
                        }
                        _ => {}
                    }
                }
                Op::End
            }
            O::Br { relative_depth } => Op::Br(relative_depth),
            O::BrIf { relative_depth } => Op::BrIf(relative_depth),
            O::BrTable { targets } => {
                let mut t: Vec<u32> = targets.targets().collect::<Result<_, _>>().map_err(werr)?;
                t.push(targets.default());
                tables.push(t);
                Op::BrTable(tables.len() as u32 - 1)
            }
            O::Return => Op::Return,
            O::Call { function_index } => Op::Call(function_index),
            O::CallIndirect { type_index, .. } => Op::CallIndirect(type_index),
            O::Drop => Op::Drop,
            O::Select | O::TypedSelect { .. } => Op::Select,
            O::LocalGet { local_index } => Op::LocalGet(local_index),
            O::LocalSet { local_index } => Op::LocalSet(local_index),
            O::LocalTee { local_index } => Op::LocalTee(local_index),
            O::GlobalGet { global_index } => Op::GlobalGet(global_index),
            O::GlobalSet { global_index } => Op::GlobalSet(global_index),
            O::I32Load { memarg } => Op::Load(Mem::I32, memarg.offset as u32),
            O::I64Load { memarg } => Op::Load(Mem::I64, memarg.offset as u32),
            O::F32Load { memarg } => Op::Load(Mem::F32, memarg.offset as u32),
            O::F64Load { memarg } => Op::Load(Mem::F64, memarg.offset as u32),
            O::I32Load8S { memarg } => Op::Load(Mem::I32_8S, memarg.offset as u32),
            O::I32Load8U { memarg } => Op::Load(Mem::I32_8U, memarg.offset as u32),
            O::I32Load16S { memarg } => Op::Load(Mem::I32_16S, memarg.offset as u32),
            O::I32Load16U { memarg } => Op::Load(Mem::I32_16U, memarg.offset as u32),
            O::I64Load8S { memarg } => Op::Load(Mem::I64_8S, memarg.offset as u32),
            O::I64Load8U { memarg } => Op::Load(Mem::I64_8U, memarg.offset as u32),
            O::I64Load16S { memarg } => Op::Load(Mem::I64_16S, memarg.offset as u32),
            O::I64Load16U { memarg } => Op::Load(Mem::I64_16U, memarg.offset as u32),
            O::I64Load32S { memarg } => Op::Load(Mem::I64_32S, memarg.offset as u32),
            O::I64Load32U { memarg } => Op::Load(Mem::I64_32U, memarg.offset as u32),
            O::I32Store { memarg } => Op::Store(Mem::I32, memarg.offset as u32),
            O::I64Store { memarg } => Op::Store(Mem::I64, memarg.offset as u32),
            O::F32Store { memarg } => Op::Store(Mem::F32, memarg.offset as u32),
            O::F64Store { memarg } => Op::Store(Mem::F64, memarg.offset as u32),
            O::I32Store8 { memarg } => Op::Store(Mem::I32_8U, memarg.offset as u32),
            O::I32Store16 { memarg } => Op::Store(Mem::I32_16U, memarg.offset as u32),
            O::I64Store8 { memarg } => Op::Store(Mem::I64_8U, memarg.offset as u32),
            O::I64Store16 { memarg } => Op::Store(Mem::I64_16U, memarg.offset as u32),
            O::I64Store32 { memarg } => Op::Store(Mem::I64_32U, memarg.offset as u32),
            O::MemorySize { .. } => Op::MemorySize,
            O::MemoryGrow { .. } => Op::MemoryGrow,
            O::MemoryCopy { .. } => Op::MemoryCopy,
            O::MemoryFill { .. } => Op::MemoryFill,
            O::I32Const { value } => Op::Const(value as u32 as u64),
            O::I64Const { value } => Op::Const(value as u64),
            O::F32Const { value } => Op::Const(value.bits() as u64),
            O::F64Const { value } => Op::Const(value.bits()),
            O::I32Eqz => Op::I32Eqz,
            O::I32Eq => Op::I32Cmp(Cmp::Eq),
            O::I32Ne => Op::I32Cmp(Cmp::Ne),
            O::I32LtS => Op::I32Cmp(Cmp::LtS),
            O::I32LtU => Op::I32Cmp(Cmp::LtU),
            O::I32GtS => Op::I32Cmp(Cmp::GtS),
            O::I32GtU => Op::I32Cmp(Cmp::GtU),
            O::I32LeS => Op::I32Cmp(Cmp::LeS),
            O::I32LeU => Op::I32Cmp(Cmp::LeU),
            O::I32GeS => Op::I32Cmp(Cmp::GeS),
            O::I32GeU => Op::I32Cmp(Cmp::GeU),
            O::I64Eqz => Op::I64Eqz,
            O::I64Eq => Op::I64Cmp(Cmp::Eq),
            O::I64Ne => Op::I64Cmp(Cmp::Ne),
            O::I64LtS => Op::I64Cmp(Cmp::LtS),
            O::I64LtU => Op::I64Cmp(Cmp::LtU),
            O::I64GtS => Op::I64Cmp(Cmp::GtS),
            O::I64GtU => Op::I64Cmp(Cmp::GtU),
            O::I64LeS => Op::I64Cmp(Cmp::LeS),
            O::I64LeU => Op::I64Cmp(Cmp::LeU),
            O::I64GeS => Op::I64Cmp(Cmp::GeS),
            O::I64GeU => Op::I64Cmp(Cmp::GeU),
            O::I32Clz => Op::I32Un(Un::Clz),
            O::I32Ctz => Op::I32Un(Un::Ctz),
            O::I32Popcnt => Op::I32Un(Un::Popcnt),
            O::I64Clz => Op::I64Un(Un::Clz),
            O::I64Ctz => Op::I64Un(Un::Ctz),
            O::I64Popcnt => Op::I64Un(Un::Popcnt),
            O::I32Add => Op::I32Bin(Bin::Add),
            O::I32Sub => Op::I32Bin(Bin::Sub),
            O::I32Mul => Op::I32Bin(Bin::Mul),
            O::I32DivS => Op::I32Bin(Bin::DivS),
            O::I32DivU => Op::I32Bin(Bin::DivU),
            O::I32RemS => Op::I32Bin(Bin::RemS),
            O::I32RemU => Op::I32Bin(Bin::RemU),
            O::I32And => Op::I32Bin(Bin::And),
            O::I32Or => Op::I32Bin(Bin::Or),
            O::I32Xor => Op::I32Bin(Bin::Xor),
            O::I32Shl => Op::I32Bin(Bin::Shl),
            O::I32ShrS => Op::I32Bin(Bin::ShrS),
            O::I32ShrU => Op::I32Bin(Bin::ShrU),
            O::I32Rotl => Op::I32Bin(Bin::Rotl),
            O::I32Rotr => Op::I32Bin(Bin::Rotr),
            O::I64Add => Op::I64Bin(Bin::Add),
            O::I64Sub => Op::I64Bin(Bin::Sub),
            O::I64Mul => Op::I64Bin(Bin::Mul),
            O::I64DivS => Op::I64Bin(Bin::DivS),
            O::I64DivU => Op::I64Bin(Bin::DivU),
            O::I64RemS => Op::I64Bin(Bin::RemS),
            O::I64RemU => Op::I64Bin(Bin::RemU),
            O::I64And => Op::I64Bin(Bin::And),
            O::I64Or => Op::I64Bin(Bin::Or),
            O::I64Xor => Op::I64Bin(Bin::Xor),
            O::I64Shl => Op::I64Bin(Bin::Shl),
            O::I64ShrS => Op::I64Bin(Bin::ShrS),
            O::I64ShrU => Op::I64Bin(Bin::ShrU),
            O::I64Rotl => Op::I64Bin(Bin::Rotl),
            O::I64Rotr => Op::I64Bin(Bin::Rotr),
            O::I32WrapI64 => Op::I32WrapI64,
            O::I64ExtendI32S => Op::I64ExtendI32S,
            O::I64ExtendI32U => Op::I64ExtendI32U,
            O::I32Extend8S => Op::I32Extend8S,
            O::I32Extend16S => Op::I32Extend16S,
            O::I64Extend8S => Op::I64Extend8S,
            O::I64Extend16S => Op::I64Extend16S,
            O::I64Extend32S => Op::I64Extend32S,
            O::F32Add => Op::FBin(false, FBin::Add),
            O::F32Sub => Op::FBin(false, FBin::Sub),
            O::F32Mul => Op::FBin(false, FBin::Mul),
            O::F32Div => Op::FBin(false, FBin::Div),
            O::F32Min => Op::FBin(false, FBin::Min),
            O::F32Max => Op::FBin(false, FBin::Max),
            O::F32Copysign => Op::FBin(false, FBin::Copysign),
            O::F64Add => Op::FBin(true, FBin::Add),
            O::F64Sub => Op::FBin(true, FBin::Sub),
            O::F64Mul => Op::FBin(true, FBin::Mul),
            O::F64Div => Op::FBin(true, FBin::Div),
            O::F64Min => Op::FBin(true, FBin::Min),
            O::F64Max => Op::FBin(true, FBin::Max),
            O::F64Copysign => Op::FBin(true, FBin::Copysign),
            O::F32Eq => Op::FCmp(false, FCmp::Eq),
            O::F32Ne => Op::FCmp(false, FCmp::Ne),
            O::F32Lt => Op::FCmp(false, FCmp::Lt),
            O::F32Gt => Op::FCmp(false, FCmp::Gt),
            O::F32Le => Op::FCmp(false, FCmp::Le),
            O::F32Ge => Op::FCmp(false, FCmp::Ge),
            O::F64Eq => Op::FCmp(true, FCmp::Eq),
            O::F64Ne => Op::FCmp(true, FCmp::Ne),
            O::F64Lt => Op::FCmp(true, FCmp::Lt),
            O::F64Gt => Op::FCmp(true, FCmp::Gt),
            O::F64Le => Op::FCmp(true, FCmp::Le),
            O::F64Ge => Op::FCmp(true, FCmp::Ge),
            O::F32Abs => Op::FUn(false, FUn::Abs),
            O::F32Neg => Op::FUn(false, FUn::Neg),
            O::F32Sqrt => Op::FUn(false, FUn::Sqrt),
            O::F32Ceil => Op::FUn(false, FUn::Ceil),
            O::F32Floor => Op::FUn(false, FUn::Floor),
            O::F32Trunc => Op::FUn(false, FUn::Trunc),
            O::F32Nearest => Op::FUn(false, FUn::Nearest),
            O::F64Abs => Op::FUn(true, FUn::Abs),
            O::F64Neg => Op::FUn(true, FUn::Neg),
            O::F64Sqrt => Op::FUn(true, FUn::Sqrt),
            O::F64Ceil => Op::FUn(true, FUn::Ceil),
            O::F64Floor => Op::FUn(true, FUn::Floor),
            O::F64Trunc => Op::FUn(true, FUn::Trunc),
            O::F64Nearest => Op::FUn(true, FUn::Nearest),
            O::I32TruncF32S => Op::FConvert(Conv::I32TruncF32S),
            O::I32TruncF32U => Op::FConvert(Conv::I32TruncF32U),
            O::I32TruncF64S => Op::FConvert(Conv::I32TruncF64S),
            O::I32TruncF64U => Op::FConvert(Conv::I32TruncF64U),
            O::I64TruncF32S => Op::FConvert(Conv::I64TruncF32S),
            O::I64TruncF32U => Op::FConvert(Conv::I64TruncF32U),
            O::I64TruncF64S => Op::FConvert(Conv::I64TruncF64S),
            O::I64TruncF64U => Op::FConvert(Conv::I64TruncF64U),
            O::F32ConvertI32S => Op::FConvert(Conv::F32ConvertI32S),
            O::F32ConvertI32U => Op::FConvert(Conv::F32ConvertI32U),
            O::F32ConvertI64S => Op::FConvert(Conv::F32ConvertI64S),
            O::F32ConvertI64U => Op::FConvert(Conv::F32ConvertI64U),
            O::F64ConvertI32S => Op::FConvert(Conv::F64ConvertI32S),
            O::F64ConvertI32U => Op::FConvert(Conv::F64ConvertI32U),
            O::F64ConvertI64S => Op::FConvert(Conv::F64ConvertI64S),
            O::F64ConvertI64U => Op::FConvert(Conv::F64ConvertI64U),
            O::F32DemoteF64 => Op::FConvert(Conv::F32DemoteF64),
            O::F64PromoteF32 => Op::FConvert(Conv::F64PromoteF32),
            O::I32ReinterpretF32 => Op::FConvert(Conv::I32ReinterpretF32),
            O::I64ReinterpretF64 => Op::FConvert(Conv::I64ReinterpretF64),
            O::F32ReinterpretI32 => Op::FConvert(Conv::F32ReinterpretI32),
            O::F64ReinterpretI64 => Op::FConvert(Conv::F64ReinterpretI64),
            O::I32TruncSatF32S => Op::FConvert(Conv::I32TruncSatF32S),
            O::I32TruncSatF32U => Op::FConvert(Conv::I32TruncSatF32U),
            O::I32TruncSatF64S => Op::FConvert(Conv::I32TruncSatF64S),
            O::I32TruncSatF64U => Op::FConvert(Conv::I32TruncSatF64U),
            O::I64TruncSatF32S => Op::FConvert(Conv::I64TruncSatF32S),
            O::I64TruncSatF32U => Op::FConvert(Conv::I64TruncSatF32U),
            O::I64TruncSatF64S => Op::FConvert(Conv::I64TruncSatF64S),
            O::I64TruncSatF64U => Op::FConvert(Conv::I64TruncSatF64U),
            other => {
                return Err(CompileError::new(format!(
                    "unsupported wasm instruction `{other:?}` in the circuit module"
                ))
                .with_help(
                    "build the circuit for plain `wasm32-unknown-unknown` (no SIMD/atomics)",
                ));
            }
        };
        code.push(d);
    }
    fuse(&mut code);
    Ok((code, tables, offsets))
}

/// Rewrite common straight-line sequences into fused ops (see `Op::LoadL` …).
fn fuse(code: &mut [Op]) {
    // Calls whose arguments are all `local.get`s, and stack-frame prologues.
    for i in 0..code.len() {
        if let Op::Call(f) = code[i] {
            let mut n = 0;
            while n < 3
                && n < i
                && matches!(code[i - n - 1], Op::LocalGet(l) if l <= u16::MAX as u32)
            {
                n += 1;
            }
            if n > 0 {
                let mut l = [0u16; 3];
                for (k, slot) in l.iter_mut().enumerate().take(n) {
                    let Op::LocalGet(x) = code[i - n + k] else {
                        unreachable!()
                    };
                    *slot = x as u16;
                }
                code[i - n] = Op::CallL(f, n as u8, l);
            }
        }
        if let (
            Op::GlobalGet(g),
            Some(Op::Const(c)),
            Some(Op::I32Bin(Bin::Sub)),
            Some(Op::LocalTee(l)),
            Some(Op::GlobalSet(g2)),
        ) = (
            &code[i],
            code.get(i + 1),
            code.get(i + 2),
            code.get(i + 3),
            code.get(i + 4),
        ) && g == g2
            && *c <= u32::MAX as u64
        {
            code[i] = Op::SpSub(*g, *c as u32, *l);
        }
    }
    fuse_basic(code);
    // Runs of word copies between the same two pointers at consecutive offsets.
    // Each `CopyLL` stands for 4 ops (it is followed by 3 skipped ones).
    let mut i = 0;
    while i < code.len() {
        if let Op::CopyLL(a, x, Mem::I64, Mem::I64, o1, o2) = code[i] {
            let at = |n: usize, desc: bool| -> Option<(i64, i64)> {
                let d = if desc { -8 * n as i64 } else { 8 * n as i64 };
                Some((o1 as i64 + d, o2 as i64 + d))
            };
            let mut best = (1usize, false);
            for desc in [false, true] {
                let mut n = 1usize;
                while n < 255
                    && let Some(Op::CopyLL(a2, x2, Mem::I64, Mem::I64, p1, p2)) =
                        code.get(i + 4 * n)
                    && (*a2, *x2) == (a, x)
                    && at(n, desc) == Some((*p1 as i64, *p2 as i64))
                {
                    n += 1;
                }
                if n > best.0 {
                    best = (n, desc);
                }
            }
            let (n, desc) = best;
            if n > 1 {
                code[i] = Op::CopyN(a, x, o1, o2, n as u8, desc);
            }
            i += 4 * n;
        } else {
            i += 1;
        }
    }
}

fn fuse_basic(code: &mut [Op]) {
    let mut i = 0;
    while i < code.len() {
        if let (
            Op::LocalGet(a),
            Some(Op::LocalGet(x)),
            Some(Op::Load(k1, o1)),
            Some(Op::Store(k2, o2)),
        ) = (&code[i], code.get(i + 1), code.get(i + 2), code.get(i + 3))
            && let (Ok(o1), Ok(o2)) = (u16::try_from(*o1), u16::try_from(*o2))
        {
            code[i] = Op::CopyLL(*a, *x, *k1, *k2, o1, o2);
            i += 4;
            continue;
        }
        match (&code[i], code.get(i + 1), code.get(i + 2)) {
            (Op::LocalGet(a), Some(Op::LocalGet(v)), Some(Op::Store(k, off))) => {
                code[i] = Op::StoreLL(*a, *v, *k, *off);
                i += 3;
            }
            (Op::LocalGet(x), Some(Op::Const(c)), Some(Op::I32Bin(Bin::Add))) => {
                code[i] = Op::AddLC(*x, *c as u32);
                i += 3;
            }
            (Op::LocalGet(x), Some(Op::Load(k, off)), _) => {
                code[i] = Op::LoadL(*x, *k, *off);
                i += 2;
            }
            _ => i += 1,
        }
    }
}

// ---------------------------------------------------------------------------
// Machine
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
struct Ctl {
    /// Where `br` to this label jumps: a loop's first op, or a block's `End`.
    br_pc: u32,
    is_loop: bool,
    /// Value-stack height below the label's params.
    height: u32,
    /// Values a branch to this label carries (loop: params, block: results).
    br_arity: u16,
}

#[derive(Clone, Debug)]
struct Frame {
    func: u32,
    pc: u32,
    locals_base: u32,
    ctl_base: u32,
}

/// The non-memory machine state a branch path diverges in.
#[derive(Clone)]
struct State {
    stack: Vec<V>,
    locals: Vec<V>,
    ctl: Vec<Ctl>,
    frames: Vec<Frame>,
    globals: Vec<V>,
    /// A `match` on a witness integer (a `br_table`) runs as `c == 0 ? … : c == 1 ?
    /// … : default`: on the fall-through path, the `br_table` is re-run with the
    /// remaining cases — `(k, {c == k wire})`, computed up front (branch arms must not
    /// emit constraints) — here.
    table_rest: Option<std::rc::Rc<[(u32, u32)]>>,
}

/// A branch path's memory writes: `(address, byte, symbolic content)`.
type Writes = Vec<(u32, u8, Option<SymByte>)>;

/// One byte's symbolic content: byte `k` of symbolic value `sym`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SymByte {
    pub sym: u32,
    pub k: u8,
}

/// The pre-write contents of a memory range, for undoing a branch path.
struct JournalEntry {
    addr: u32,
    old: Vec<(u8, Option<SymByte>)>,
}

const PAGE: usize = 65536;
/// Unroll/termination budget: wasm instructions executed per compile.
const MAX_STEPS: u64 = 10_000_000_000;
/// Call-depth limit (unbounded recursion fails fast instead of spinning).
const MAX_DEPTH: usize = 10_000;
/// Instruction budget for probing a branch arm (a panic path is short).
const PROBE_STEPS: u64 = 100_000;

/// The (non-diverging) error that ends a probe.
fn probe_end() -> CompileError {
    CompileError::new("probe: the arm does more than panic")
}

pub struct Machine {
    st: State,
    pub mem: Vec<u8>,
    shadow: HashMap<u32, SymByte>,
    /// Per 8-byte granule, how many of its bytes are symbolic (exact, so the
    /// all-concrete fast paths stay fast).
    gran: Vec<u8>,
    pub syms: Vec<Sym>,
    journals: Vec<Vec<JournalEntry>>,
    steps: u64,
    /// Branch-path nesting depth (> 0 while exploring a witness-dependent branch).
    pub path_depth: u32,
    pub host_ns: u64,
    /// Time host calls (`XARK_FRONTEND_TIME`).
    pub timing: bool,
    pub forks: u64,
    /// Probing a branch arm for an immediate panic (see [`Machine::probe`]): any
    /// import other than `panic`, or a nested witness branch, ends the probe.
    pub(crate) probing: bool,
    probe_steps: u64,
}

/// Host side of the `xark.*` imports.
pub trait Host {
    /// Handle an import call; `args` are the call's arguments in order.
    fn call(&mut self, m: &mut Machine, import: u32, args: &[V]) -> CompileResult<Option<V>>;
    /// Bind import indices before execution.
    fn link(&mut self, module: &Module) -> CompileResult<()>;
    /// A `{0,1}` wire's negation `1 − c` (for `!cond` on a witness `bool`).
    fn not(&mut self, m: &mut Machine, c: V) -> CompileResult<V>;
    /// Boolean `a ∧ b`, `a ∨ b`, `a ⊕ b` on `{0,1}` values (each may be concrete).
    fn bool_op(&mut self, m: &mut Machine, op: BoolOp, a: V, b: V) -> CompileResult<V>;
    /// How many partial intrinsics (ones some inputs can't satisfy) ran outside a
    /// guard, for the branch check: inside an arm every constraint and hint is
    /// guarded, so the count moves only if an arm declares a circuit input.
    fn emitted(&self) -> usize;
    /// Describe the current source location (for diagnostics).
    fn location(&self) -> Option<String>;
    /// Native integer arithmetic / comparison / truncation on witness integers
    /// (`wide`: i64, else i32).
    fn int_bin(&mut self, m: &mut Machine, o: Bin, wide: bool, a: V, b: V) -> CompileResult<V>;
    fn int_cmp(&mut self, m: &mut Machine, o: Cmp, wide: bool, a: V, b: V) -> CompileResult<V>;
    fn int_trunc(&mut self, m: &mut Machine, v: V, bits: u32) -> CompileResult<V>;
    /// A witness pointer as `base + o`, with `o` (returned as its own wire) known to
    /// take only the listed values — at most 1024: a variable of known width
    /// (`c·j`), or a sum of pinned-boolean variables (`(x & 7)`, `x as u8`).
    fn index_form(&mut self, m: &mut Machine, p: V) -> Option<(u64, Vec<u64>, V)>;
    /// Sign-extend a `width`-bit witness integer to `reg` bits.
    fn sign_extend(&mut self, m: &mut Machine, x: V, width: u32, reg: u32) -> CompileResult<V>;
    /// Constrain the `{0,1}` wire `cond` to `value` (where the current path is taken).
    fn require_cond(&mut self, m: &mut Machine, cond: u32, value: bool) -> CompileResult<()>;
    /// Enter / leave the arm of a witness branch where `cond == value`: until the
    /// matching `arm_end`, `require`s bind only when that arm is taken.
    fn arm_begin(&mut self, m: &mut Machine, cond: u32, value: bool) -> CompileResult<()>;
    fn arm_end(&mut self);
    /// A wasm function was entered / returned (outside branch exploration).
    fn call_begin(&mut self);
    fn call_end(&mut self);
}

#[derive(Clone, Copy, Debug)]
pub enum BoolOp {
    And,
    Or,
    Xor,
}

#[cold]
#[inline(never)]
fn oob(addr: u64) -> CompileError {
    trap(&format!("memory access out of bounds at {addr:#x}"))
}

fn trap(msg: &str) -> CompileError {
    CompileError::new(format!("circuit execution trapped: {msg}")).diverging()
}

impl Machine {
    pub fn new(module: &Module) -> CompileResult<Machine> {
        let mut mem = vec![0u8; module.mem_pages as usize * PAGE];
        for (off, bytes) in &module.data {
            let off = *off as usize;
            mem.get_mut(off..off + bytes.len())
                .ok_or_else(|| trap("data segment out of bounds"))?
                .copy_from_slice(bytes);
        }
        let gran = vec![0u8; mem.len() / 8 + 1];
        Ok(Machine {
            st: State {
                stack: Vec::with_capacity(1024),
                locals: Vec::with_capacity(4096),
                ctl: Vec::with_capacity(1024),
                frames: Vec::new(),
                globals: module.globals.iter().map(|&g| V::c(g)).collect(),
                table_rest: None,
            },
            mem,
            shadow: HashMap::new(),
            gran,
            syms: vec![Sym::None],
            journals: Vec::new(),
            steps: 0,
            path_depth: 0,
            host_ns: 0,
            timing: std::env::var_os("XARK_FRONTEND_TIME").is_some(),
            forks: 0,
            probing: false,
            probe_steps: 0,
        })
    }

    /// Wasm instructions executed so far.
    pub fn steps(&self) -> u64 {
        self.steps
    }

    pub fn new_sym(&mut self, s: Sym) -> V {
        self.syms.push(s);
        V {
            b: 0,
            s: self.syms.len() as u32 - 1,
        }
    }

    /// `cond ? t : e`, folding the trivial cases.
    pub fn ite(&mut self, cond: u32, t: V, e: V) -> V {
        if t == e {
            return t;
        }
        self.new_sym(Sym::Ite { cond, t, e })
    }

    /// Call export `name` (no args, no results) to completion.
    pub fn run_export(
        &mut self,
        module: &Module,
        name: &str,
        host: &mut dyn Host,
    ) -> CompileResult<()> {
        host.link(module)?;
        let f = *module.exports.get(name).ok_or_else(|| {
            CompileError::new(format!("the circuit module exports no `{name}`")).with_help(
                "is the crate's entry function marked `#[circuit]`, and was it built with \
                 `--cfg xark` for wasm32?",
            )
        })?;
        self.call(module, f, host)?;
        self.run(module, host, 0)?;
        Ok(())
    }

    // --- memory -------------------------------------------------------------

    #[inline]
    fn has_shadow(&self, addr: u32, size: u32) -> bool {
        let g0 = (addr >> 3) as usize;
        let g1 = ((addr + size.max(1) - 1) >> 3) as usize;
        self.gran[g0..=g1].iter().any(|&c| c != 0)
    }

    /// Set (or clear) byte `a`'s symbolic content, keeping the granule counts exact.
    #[inline]
    fn set_shadow(&mut self, a: u32, sb: Option<SymByte>) {
        let g = (a >> 3) as usize;
        match sb {
            Some(sb) => {
                if self.shadow.insert(a, sb).is_none() {
                    self.gran[g] += 1;
                }
            }
            None => {
                if self.gran[g] != 0 && self.shadow.remove(&a).is_some() {
                    self.gran[g] -= 1;
                }
            }
        }
    }

    /// Clear the symbolic content of `[addr, addr+size)`, visiting only granules that have any.
    fn clear_shadow(&mut self, addr: u32, size: u32) {
        if size == 0 {
            return;
        }
        let g0 = addr >> 3;
        let g1 = (addr + size - 1) >> 3;
        for g in g0..=g1 {
            if self.gran[g as usize] == 0 {
                continue;
            }
            let lo = (g << 3).max(addr);
            let hi = ((g << 3) + 8).min(addr + size);
            for a in lo..hi {
                self.set_shadow(a, None);
            }
        }
    }

    #[inline]
    fn check(&self, addr: u64, size: u32) -> CompileResult<u32> {
        if addr + size as u64 > self.mem.len() as u64 {
            return Err(oob(addr));
        }
        Ok(addr as u32)
    }

    #[inline]
    fn journal(&mut self, addr: u32, size: u32) {
        if self.journals.is_empty() {
            return;
        }
        if let Some(j) = self.journals.last_mut() {
            let old = (addr..addr + size)
                .map(|a| (self.mem[a as usize], self.shadow.get(&a).copied()))
                .collect();
            j.push(JournalEntry { addr, old });
        }
    }

    /// The byte width a symbolic value occupies in memory (`Wire` bytes past its
    /// width are concrete zeros).
    fn sym_bytes(&self, v: V, size: u32) -> u32 {
        match &self.syms[v.s as usize] {
            Sym::Wire { width, .. } => width.div_ceil(8).min(size),
            _ => size,
        }
    }

    /// Store `v`'s low `size` bytes at `addr`.
    #[inline]
    pub fn store(&mut self, addr: u32, size: u32, v: V) -> CompileResult<()> {
        self.journal(addr, size);
        let a = addr as usize;
        if !v.is_sym() {
            self.mem[a..a + size as usize].copy_from_slice(&v.b.to_le_bytes()[..size as usize]);
            if self.has_shadow(addr, size) {
                self.clear_shadow(addr, size);
            }
            return Ok(());
        }
        if let Sym::Bytes(bytes) = &self.syms[v.s as usize] {
            let bytes = bytes.clone();
            for i in 0..size {
                let (byte, sb) = bytes.get(i as usize).copied().unwrap_or((0, None));
                self.mem[a + i as usize] = byte;
                self.set_shadow(addr + i, sb);
            }
            return Ok(());
        }
        let n = self.sym_bytes(v, size);
        for i in 0..size {
            self.mem[a + i as usize] = 0;
            let sb = (i < n).then_some(SymByte {
                sym: v.s,
                k: i as u8,
            });
            self.set_shadow(addr + i, sb);
        }
        Ok(())
    }

    /// Load `size` bytes at `addr` as a value (zero-extended).
    #[inline]
    pub fn load(&mut self, addr: u32, size: u32) -> CompileResult<V> {
        let a = addr as usize;
        if !self.has_shadow(addr, size) {
            let mut buf = [0u8; 8];
            buf[..size as usize].copy_from_slice(&self.mem[a..a + size as usize]);
            return Ok(V::c(u64::from_le_bytes(buf)));
        }
        let bytes: Vec<(u8, Option<SymByte>)> = (0..size)
            .map(|i| {
                (
                    self.mem[a + i as usize],
                    self.shadow.get(&(addr + i)).copied(),
                )
            })
            .collect();
        self.assemble(&bytes)
            .map_err(|e| e.with_note(format!("{size}-byte load at {addr:#x}")))
    }

    /// Byte `k` of `v` (concrete, or a reference to a symbolic value's byte).
    fn byte_of(&self, v: V, k: u8) -> (u8, Option<SymByte>) {
        if !v.is_sym() {
            return ((v.b >> (8 * k as u32)) as u8, None);
        }
        match &self.syms[v.s as usize] {
            Sym::Wire { width, .. } if (k as u32) * 8 >= *width => return (0, None),
            Sym::Bytes(b) => return b.get(k as usize).copied().unwrap_or((0, None)),
            _ => {}
        }
        (0, Some(SymByte { sym: v.s, k }))
    }

    /// A value from its little-endian bytes. Symbolic bytes must form one wire in
    /// place (bytes past its width concrete zeros); bytes of a select resolve
    /// arm-wise into a select of the two assembled values.
    fn assemble(&mut self, bytes: &[(u8, Option<SymByte>)]) -> CompileResult<V> {
        let Some(first) = bytes.iter().find_map(|b| b.1) else {
            let mut buf = [0u8; 8];
            for (i, b) in bytes.iter().enumerate() {
                buf[i] = b.0;
            }
            return Ok(V::c(u64::from_le_bytes(buf)));
        };
        // A select among the bytes: substitute each arm and assemble both.
        if let Some(sb) = bytes
            .iter()
            .filter_map(|b| b.1)
            .find(|sb| matches!(self.syms[sb.sym as usize], Sym::Ite { .. }))
        {
            let Sym::Ite { cond, t, e } = self.syms[sb.sym as usize].clone() else {
                unreachable!()
            };
            let ite_sym = sb.sym;
            let arm = |m: &Machine, x: V| -> Vec<(u8, Option<SymByte>)> {
                bytes
                    .iter()
                    .map(|&(byte, s)| match s {
                        Some(s) if s.sym == ite_sym => m.byte_of(x, s.k),
                        other => (byte, other),
                    })
                    .collect()
            };
            let tb = arm(self, t);
            let eb = arm(self, e);
            let tv = self.assemble(&tb)?;
            let ev = self.assemble(&eb)?;
            return Ok(self.ite(cond, tv, ev));
        }
        // One wire, in place from byte 0, nothing else nonzero.
        let ok = bytes.iter().enumerate().all(|(i, &(byte, s))| match s {
            Some(s) => s.sym == first.sym && s.k as usize == i,
            None => byte == 0,
        });
        if ok
            && first.k == 0
            && let Sym::Wire { width, .. } = self.syms[first.sym as usize]
        {
            // Every byte of the wire must be here: a prefix of a wider wire is a
            // truncation, not the wire.
            let need = width.div_ceil(8) as usize;
            if bytes.len() >= need && bytes[..need].iter().all(|b| b.1.is_some()) {
                return Ok(V { b: 0, s: first.sym });
            }
        }
        // Bytes of different values in one word: keep them as bytes.
        Ok(self.new_sym(Sym::Bytes(bytes.to_vec())))
    }

    /// A store through a witness pointer: through a select of pointers
    /// ([`Self::store_select`]), or to `base + o` with `o` a witness taking few values
    /// (`t[i] = v` for a narrow `i`; see [`Host::index_form`]) — every candidate slot
    /// becomes `idx == o ? v : old`, and an out-of-bounds one (a trap) is ruled out.
    fn store_any(
        &mut self,
        a: V,
        off: u32,
        size: u32,
        v: V,
        host: &mut dyn Host,
    ) -> CompileResult<()> {
        if matches!(self.syms[a.s as usize], Sym::Wire { .. })
            && let Some((base, offsets, idx)) = host.index_form(self, a)
        {
            if self.probing {
                return Err(probe_end());
            }
            let mut any = false;
            for o in offsets {
                let addr = (base + o) & 0xffff_ffff;
                let eq = host.int_cmp(self, Cmp::Eq, true, idx, V::c(o))?;
                if addr + off as u64 + size as u64 > self.mem.len() as u64 {
                    if eq.is_sym() {
                        host.require_cond(self, eq.s, false)?;
                    }
                    continue;
                }
                any = true;
                let p = addr as u32 + off;
                if !eq.is_sym() {
                    if eq.b != 0 {
                        self.store(p, size, v)?;
                    }
                    continue;
                }
                let old = self.load(p, size)?;
                let new = self.ite(eq.s, v, old);
                self.store(p, size, new)?;
            }
            if !any {
                return Err(
                    CompileError::new("circuit execution trapped: out-of-bounds store").diverging(),
                );
            }
            return Ok(());
        }
        self.store_select(a, off, size, v, host)
    }

    /// Every address a witness pointer can hold (concrete, a narrow `base + index`,
    /// or a select of those), deduplicated; `None` if one isn't bounded that way.
    fn pointer_candidates(&mut self, host: &mut dyn Host, p: V) -> Option<Vec<u64>> {
        if !p.is_sym() {
            return Some(vec![p.b & 0xffff_ffff]);
        }
        match self.syms[p.s as usize].clone() {
            Sym::Ite { t, e, .. } => {
                let mut c = self.pointer_candidates(host, t)?;
                c.extend(self.pointer_candidates(host, e)?);
                c.sort_unstable();
                c.dedup();
                Some(c)
            }
            Sym::Wire { .. } => {
                let (base, offsets, _) = host.index_form(self, p)?;
                Some(offsets.iter().map(|o| (base + o) & 0xffff_ffff).collect())
            }
            _ => None,
        }
    }

    /// A store through `cond ? p : q`: each target keeps its old contents unless
    /// it is the selected one (`*p = cond ? v : *p`, `*q = cond ? *q : v`).
    fn store_select(
        &mut self,
        a: V,
        off: u32,
        size: u32,
        v: V,
        host: &mut dyn Host,
    ) -> CompileResult<()> {
        let Sym::Ite { cond, t, e } = self.syms[a.s as usize].clone() else {
            return Err(CompileError::new(
                "a store through a witness-dependent pointer is not supported",
            ));
        };
        if t.is_sym() || e.is_sym() {
            // A select of witness pointers: every address it can hold becomes
            // `a == addr ? v : old`; an out-of-bounds one (a trap) is ruled out.
            if self.probing {
                return Err(probe_end());
            }
            let Some(addrs) = self.pointer_candidates(host, a) else {
                return Err(CompileError::new(
                    "a store through a nested witness-dependent pointer is not supported",
                ));
            };
            let mut any = false;
            for addr in addrs {
                let eq = host.int_cmp(self, Cmp::Eq, false, a, V::c(addr))?;
                if addr + off as u64 + size as u64 > self.mem.len() as u64 {
                    if eq.is_sym() {
                        host.require_cond(self, eq.s, false)?;
                    }
                    continue;
                }
                any = true;
                let p = addr as u32 + off;
                if !eq.is_sym() {
                    if eq.b != 0 {
                        self.store(p, size, v)?;
                    }
                    continue;
                }
                let old = self.load(p, size)?;
                let new = self.ite(eq.s, v, old);
                self.store(p, size, new)?;
            }
            if !any {
                return Err(
                    CompileError::new("circuit execution trapped: out-of-bounds store").diverging(),
                );
            }
            return Ok(());
        }
        let pt = self.check(t.b as u32 as u64 + off as u64, size)?;
        let pe = self.check(e.b as u32 as u64 + off as u64, size)?;
        if pe == pt {
            // Both arms are the same address: the store happens either way.
            return self.store(pt, size, v);
        }
        // Sequential, so overlapping targets see the first store: the `else`
        // target's old bytes are read after the `then` store.
        let old_t = self.load(pt, size)?;
        let nt = self.ite(cond, v, old_t);
        self.store(pt, size, nt)?;
        let old_e = self.load(pe, size)?;
        let ne = self.ite(cond, old_e, v);
        self.store(pe, size, ne)
    }

    /// Bytes `off..off+len` of `v` as a value.
    fn slice(&mut self, v: V, off: u32, len: u32) -> CompileResult<V> {
        if !v.is_sym() {
            let x = v.b >> (8 * off);
            let mask = if len >= 8 {
                u64::MAX
            } else {
                (1u64 << (8 * len)) - 1
            };
            return Ok(V::c(x & mask));
        }
        match self.syms[v.s as usize].clone() {
            Sym::Ite { cond, t, e } => {
                let t2 = self.slice(t, off, len)?;
                let e2 = self.slice(e, off, len)?;
                Ok(self.ite(cond, t2, e2))
            }
            Sym::Wire { width, .. } => {
                if off == 0 && 8 * len >= width {
                    Ok(v)
                } else if 8 * off >= width {
                    Ok(V::c(0))
                } else {
                    let bytes: Vec<_> =
                        (off..off + len).map(|k| self.byte_of(v, k as u8)).collect();
                    Ok(self.new_sym(Sym::Bytes(bytes)))
                }
            }
            Sym::Bytes(b) => {
                let bytes: Vec<_> = (off..off + len)
                    .map(|k| b.get(k as usize).copied().unwrap_or((0, None)))
                    .collect();
                self.assemble(&bytes)
            }
            Sym::None => unreachable!(),
        }
    }

    // --- control ------------------------------------------------------------

    fn call(&mut self, module: &Module, f: u32, host: &mut dyn Host) -> CompileResult<()> {
        let n_imports = module.imports.len() as u32;
        if f < n_imports {
            if self.probing && module.imports[f as usize].name != "panic" {
                return Err(probe_end());
            }
            let ty = &module.types[module.imports[f as usize].ty as usize];
            let n = ty.params.len();
            let base = self.st.stack.len() - n;
            let mut buf = [V::c(0); 12];
            buf[..n].copy_from_slice(&self.st.stack[base..]);
            self.st.stack.truncate(base);
            let args = &buf[..n];
            let t0 = self.timing.then(std::time::Instant::now);
            let r = host
                .call(self, f, args)
                .map_err(|e| e.or_location(|| host.location()))?;
            if let Some(t0) = t0 {
                self.host_ns += t0.elapsed().as_nanos() as u64;
            }
            if let Some(v) = r {
                self.st.stack.push(v);
            }
            return Ok(());
        }
        let func = &module.funcs[(f - n_imports) as usize];
        let ty = &module.types[func.ty as usize];
        let n_params = ty.params.len();
        let locals_base = self.st.locals.len();
        let base = self.st.stack.len() - n_params;
        self.st.locals.extend(self.st.stack.drain(base..));
        self.st
            .locals
            .extend(std::iter::repeat_n(V::c(0), func.n_locals as usize));
        if self.st.frames.len() >= MAX_DEPTH {
            return Err(CompileError::new(format!(
                "call depth exceeded {MAX_DEPTH}: unbounded recursion is not supported"
            ))
            .with_help("recursion must have a compile-time-constant depth"));
        }
        if self.path_depth == 0 {
            host.call_begin();
        }
        let ctl_base = self.st.ctl.len();
        // The function body is an implicit block ending at its final `End`.
        self.st.ctl.push(Ctl {
            br_pc: func.code.len() as u32 - 1,
            is_loop: false,
            height: self.st.stack.len() as u32,
            br_arity: ty.results.len() as u16,
        });
        self.st.frames.push(Frame {
            func: f,
            pc: 0,
            locals_base: locals_base as u32,
            ctl_base: ctl_base as u32,
        });
        Ok(())
    }

    /// Branch to label `depth` (0 = innermost): unwind the value stack to the
    /// label's height keeping its branch arity, and jump.
    fn branch(&mut self, depth: u32) -> u32 {
        let idx = self.st.ctl.len() - 1 - depth as usize;
        let c = self.st.ctl[idx].clone();
        let keep = c.br_arity as usize;
        let top = self.st.stack.len();
        if top - keep != c.height as usize {
            self.st
                .stack
                .copy_within(top - keep..top, c.height as usize);
            self.st.stack.truncate(c.height as usize + keep);
        }
        if c.is_loop {
            // Re-entering the loop: keep its label.
            self.st.ctl.truncate(idx + 1);
            c.br_pc
        } else {
            // Leaving the block: drop its label and continue after its `End`.
            self.st.ctl.truncate(idx);
            c.br_pc + 1
        }
    }

    /// Execute until the control stack drops to `stop` labels (or the call stack
    /// empties). Returns with the current frame's pc at the next instruction.
    fn run(&mut self, module: &Module, host: &mut dyn Host, stop: usize) -> CompileResult<()> {
        let mut cur = 0u32;
        self.run_body(module, host, stop, &mut cur)
            .map_err(|mut e| {
                // The innermost failing run records where it stopped (the wasm call
                // stack, the top frame at the failing instruction), for diagnostics.
                if e.site.is_none() && !self.st.frames.is_empty() {
                    let mut site = self.call_stack();
                    if let Some(top) = site.last_mut() {
                        top.1 = cur;
                    }
                    e.site = Some(Box::new(crate::error::ErrorSite {
                        stack: site,
                        span: None,
                    }));
                }
                e
            })
    }

    /// The wasm call stack, outermost first: `(function index, pc)` per frame, `pc`
    /// just past the instruction it's at (a call: the call).
    pub fn call_stack(&self) -> Vec<(u32, u32)> {
        self.st.frames.iter().map(|f| (f.func, f.pc)).collect()
    }

    /// [`Self::call_stack`] into a reused buffer.
    pub fn call_stack_into(&self, out: &mut Vec<(u32, u32)>) {
        out.clear();
        out.extend(self.st.frames.iter().map(|f| (f.func, f.pc)));
    }

    fn run_body(
        &mut self,
        module: &Module,
        host: &mut dyn Host,
        stop: usize,
        cur: &mut u32,
    ) -> CompileResult<()> {
        let n_imports = module.imports.len() as u32;
        loop {
            if self.st.ctl.len() <= stop || self.st.frames.is_empty() {
                return Ok(());
            }
            let fi = self.st.frames.len() - 1;
            let fidx = self.st.frames[fi].func;
            let func = &module.funcs[(fidx - n_imports) as usize];
            let lb = self.st.frames[fi].locals_base as usize;
            let mut pc = self.st.frames[fi].pc as usize;
            // Inner loop: run this frame until a call, return or the stop height.
            loop {
                self.steps += 1;
                if self.probing {
                    self.probe_steps += 1;
                    if self.probe_steps > PROBE_STEPS {
                        return Err(probe_end());
                    }
                }
                if self.steps > MAX_STEPS {
                    return Err(CompileError::new(
                        "circuit execution did not terminate within the step budget",
                    )
                    .with_note(
                        "only loops with compile-time-constant bounds can be unrolled; \
                         unbounded recursion is not supported (it may compile to a loop)",
                    ));
                }
                let op = &func.code[pc];
                pc += 1;
                *cur = pc as u32;
                match op {
                    Op::Nop => {}
                    Op::Unreachable => {
                        return Err(CompileError::new(
                            "the circuit reached `unreachable` (a panic or an impossible case)",
                        )
                        .diverging()
                        .or_location(|| host.location())
                        .with_note(format!("in `{}`", module.func_name(fidx))));
                    }
                    Op::Block {
                        end_pc,
                        params,
                        arity,
                    } => {
                        self.st.ctl.push(Ctl {
                            br_pc: *end_pc,
                            is_loop: false,
                            height: (self.st.stack.len() - *params as usize) as u32,
                            br_arity: *arity,
                        });
                    }
                    Op::Loop { params } => {
                        self.st.ctl.push(Ctl {
                            br_pc: (pc - 1) as u32 + 1,
                            is_loop: true,
                            height: (self.st.stack.len() - *params as usize) as u32,
                            br_arity: *params,
                        });
                    }
                    Op::If {
                        else_pc,
                        end_pc,
                        params,
                        arity,
                    } => {
                        let c = self.st.stack.pop().unwrap();
                        let ctl = Ctl {
                            br_pc: *end_pc,
                            is_loop: false,
                            height: (self.st.stack.len() - *params as usize) as u32,
                            br_arity: *arity,
                        };
                        let else_start = if *else_pc != 0 { *else_pc + 1 } else { *end_pc };
                        match self.cond(c, host)? {
                            Cond::Known(true) => self.st.ctl.push(ctl),
                            Cond::Known(false) => {
                                self.st.ctl.push(ctl);
                                pc = else_start as usize;
                            }
                            Cond::Sym(cond) => {
                                // Both arms run inside the `if` block; they rejoin at its end.
                                let stop_h = self.st.ctl.len();
                                self.st.ctl.push(ctl);
                                self.st.frames[fi].pc = pc as u32;
                                let mut then_st = self.st.clone();
                                then_st.frames[fi].pc = pc as u32;
                                let mut else_st = self.st.clone();
                                else_st.frames[fi].pc = else_start;
                                then_st.ctl = self.st.ctl.clone();
                                else_st.ctl = self.st.ctl.clone();
                                self.fork(module, host, cond, then_st, else_st, stop_h)?;
                                break;
                            }
                        }
                    }
                    Op::Else { end_pc } => {
                        // Reached the end of the then-arm: skip the else-arm.
                        pc = *end_pc as usize;
                    }
                    Op::End => {
                        let c = self.st.ctl.pop().expect("label for end");
                        let _ = c;
                        if self.st.ctl.len() == self.st.frames[fi].ctl_base as usize {
                            // Function end: return.
                            self.ret(fi, Some(host));
                            break;
                        }
                        if self.st.ctl.len() <= stop {
                            self.st.frames[fi].pc = pc as u32;
                            return Ok(());
                        }
                    }
                    Op::Br(d) => {
                        let depth = *d;
                        let target_idx = self.st.ctl.len() - 1 - depth as usize;
                        if target_idx == self.st.frames[fi].ctl_base as usize {
                            // Branch to the function label = return.
                            self.branch(depth);
                            self.ret(fi, Some(host));
                            break;
                        }
                        pc = self.branch(depth) as usize;
                        if self.st.ctl.len() <= stop {
                            self.st.frames[fi].pc = pc as u32;
                            return Ok(());
                        }
                    }
                    Op::BrIf(d) => {
                        let c = self.st.stack.pop().unwrap();
                        match self.cond(c, host)? {
                            Cond::Known(false) => {}
                            Cond::Known(true) => {
                                let depth = *d;
                                let target_idx = self.st.ctl.len() - 1 - depth as usize;
                                if target_idx == self.st.frames[fi].ctl_base as usize {
                                    self.branch(depth);
                                    self.ret(fi, Some(host));
                                    break;
                                }
                                pc = self.branch(depth) as usize;
                                if self.st.ctl.len() <= stop {
                                    self.st.frames[fi].pc = pc as u32;
                                    return Ok(());
                                }
                            }
                            Cond::Sym(cond) => {
                                let depth = *d;
                                let target_idx = self.st.ctl.len() - 1 - depth as usize;
                                if self.st.ctl[target_idx].is_loop {
                                    return Err(witness_loop().or_location(|| host.location()));
                                }
                                self.st.frames[fi].pc = pc as u32;
                                let else_st = self.st.clone(); // fall through
                                // Taken: perform the branch, paused just past the target block.
                                let mut then_st = self.st.clone();
                                std::mem::swap(&mut self.st, &mut then_st);
                                let to_return = target_idx == self.st.frames[fi].ctl_base as usize;
                                let npc = self.branch(depth);
                                if to_return {
                                    // The taken path's return: notified after the merge.
                                    self.ret(fi, None);
                                } else {
                                    self.st.frames[fi].pc = npc;
                                }
                                std::mem::swap(&mut self.st, &mut then_st);
                                let stop_h = target_idx;
                                self.fork(module, host, cond, then_st, else_st, stop_h)?;
                                break;
                            }
                        }
                    }
                    Op::BrTable(t) => {
                        let c = self.st.stack.pop().unwrap();
                        let targets = &func.tables[*t as usize];
                        let rest = self.st.table_rest.take();
                        // A case the witness provably equals (can't happen; be safe).
                        let mut forced = None;
                        if c.is_sym() {
                            if self.probing {
                                return Err(probe_end());
                            }
                            let rest = match rest {
                                Some(r) => r,
                                None => {
                                    let mut conds = Vec::new();
                                    for k in 0..targets.len() as u32 - 1 {
                                        let eq =
                                            host.int_cmp(self, Cmp::Eq, true, c, V::c(k as u64))?;
                                        match self.cond(eq, host)? {
                                            Cond::Sym(s) => conds.push((k, s)),
                                            Cond::Known(false) => {}
                                            Cond::Known(true) => {
                                                forced = Some(k as usize);
                                                conds.clear();
                                                break;
                                            }
                                        }
                                    }
                                    conds.into()
                                }
                            };
                            if let Some((&(k, cond), more)) = rest.split_first() {
                                let depth = targets[k as usize];
                                let target_idx = self.st.ctl.len() - 1 - depth as usize;
                                if self.st.ctl[target_idx].is_loop {
                                    return Err(witness_loop().or_location(|| host.location()));
                                }
                                // Fall through: back to this op, `c` on the stack, case
                                // `k` ruled out.
                                self.st.frames[fi].pc = pc as u32 - 1;
                                let mut else_st = self.st.clone();
                                else_st.stack.push(c);
                                else_st.table_rest = Some(more.into());
                                // Taken: branch to case `k`'s label.
                                self.st.frames[fi].pc = pc as u32;
                                let mut then_st = self.st.clone();
                                std::mem::swap(&mut self.st, &mut then_st);
                                let to_return = target_idx == self.st.frames[fi].ctl_base as usize;
                                let npc = self.branch(depth);
                                if to_return {
                                    self.ret(fi, None);
                                } else {
                                    self.st.frames[fi].pc = npc;
                                }
                                std::mem::swap(&mut self.st, &mut then_st);
                                self.fork(module, host, cond, then_st, else_st, target_idx)?;
                                break;
                            }
                        }
                        // Concrete (or every case but the default ruled out).
                        let i = if c.is_sym() {
                            forced.unwrap_or(targets.len() - 1)
                        } else {
                            (c.b as u32 as usize).min(targets.len() - 1)
                        };
                        let depth = targets[i];
                        let target_idx = self.st.ctl.len() - 1 - depth as usize;
                        if target_idx == self.st.frames[fi].ctl_base as usize {
                            self.branch(depth);
                            self.ret(fi, Some(host));
                            break;
                        }
                        pc = self.branch(depth) as usize;
                        if self.st.ctl.len() <= stop {
                            self.st.frames[fi].pc = pc as u32;
                            return Ok(());
                        }
                    }
                    Op::Return => {
                        let depth =
                            (self.st.ctl.len() - 1 - self.st.frames[fi].ctl_base as usize) as u32;
                        self.branch(depth);
                        self.ret(fi, Some(host));
                        break;
                    }
                    Op::Call(f) => {
                        let f = *f;
                        self.st.frames[fi].pc = pc as u32;
                        if f < n_imports {
                            self.call(module, f, host)?;
                            continue;
                        }
                        self.call(module, f, host)?;
                        break;
                    }
                    Op::CallL(f, n, l) => {
                        // The `local.get`s, then the call (as `Op::Call`).
                        let (f, n) = (*f, *n as usize);
                        for &x in &l[..n] {
                            let v = self.st.locals[lb + x as usize];
                            self.st.stack.push(v);
                        }
                        pc += n;
                        self.st.frames[fi].pc = pc as u32;
                        if f < n_imports {
                            self.call(module, f, host)?;
                            continue;
                        }
                        self.call(module, f, host)?;
                        break;
                    }
                    Op::SpSub(g, c, l) => {
                        let v = self.st.globals[*g as usize];
                        let r = if v.is_sym() {
                            self.sym_bin(Bin::Sub, false, v, V::i32(*c), host)?
                        } else {
                            V::i32(i32_bin(Bin::Sub, v.b as u32, *c)?)
                        };
                        self.st.locals[lb + *l as usize] = r;
                        self.st.globals[*g as usize] = r;
                        pc += 4;
                    }
                    Op::CallIndirect(ty) => {
                        let i = self.st.stack.pop().unwrap();
                        if i.is_sym() {
                            return Err(CompileError::new(
                                "an indirect call on a witness value is not supported",
                            ));
                        }
                        let f = module
                            .table
                            .get(i.b as u32 as usize)
                            .copied()
                            .flatten()
                            .ok_or_else(|| trap("indirect call to a null table entry"))?;
                        // Wasm traps when the callee's signature isn't the expected one.
                        let fty = if f < n_imports {
                            module.imports[f as usize].ty
                        } else {
                            module.funcs[(f - n_imports) as usize].ty
                        };
                        if module.types[fty as usize] != module.types[*ty as usize] {
                            return Err(trap("indirect call signature mismatch"));
                        }
                        self.st.frames[fi].pc = pc as u32;
                        self.call(module, f, host)?;
                        if f < n_imports {
                            continue;
                        }
                        break;
                    }
                    Op::Drop => {
                        self.st.stack.pop();
                    }
                    Op::Select => {
                        let c = self.st.stack.pop().unwrap();
                        let b = self.st.stack.pop().unwrap();
                        let a = self.st.stack.pop().unwrap();
                        let r = match self.cond(c, host)? {
                            Cond::Known(true) => a,
                            Cond::Known(false) => b,
                            Cond::Sym(cond) => self.ite(cond, a, b),
                        };
                        self.st.stack.push(r);
                    }
                    Op::LocalGet(i) => {
                        let v = self.st.locals[lb + *i as usize];
                        self.st.stack.push(v);
                    }
                    Op::LocalSet(i) => {
                        let v = self.st.stack.pop().unwrap();
                        self.st.locals[lb + *i as usize] = v;
                    }
                    Op::LocalTee(i) => {
                        let v = *self.st.stack.last().unwrap();
                        self.st.locals[lb + *i as usize] = v;
                    }
                    Op::GlobalGet(i) => {
                        let v = self.st.globals[*i as usize];
                        self.st.stack.push(v);
                    }
                    Op::GlobalSet(i) => {
                        let v = self.st.stack.pop().unwrap();
                        self.st.globals[*i as usize] = v;
                    }
                    Op::Load(kind, off) => {
                        let a = self.st.stack.pop().unwrap();
                        // Fast path: a concrete 8/4-byte load of concrete memory.
                        let addr = a.b as u32 as u64 + *off as u64;
                        let v = match kind {
                            Mem::I64 | Mem::I32
                                if !a.is_sym()
                                    && addr + 8 <= self.mem.len() as u64
                                    && !self.has_shadow(addr as u32, kind.size()) =>
                            {
                                let p = addr as usize;
                                let w = u64::from_le_bytes(self.mem[p..p + 8].try_into().unwrap());
                                V::c(if matches!(kind, Mem::I32) {
                                    w as u32 as u64
                                } else {
                                    w
                                })
                            }
                            _ => self.load_any(a, *off, *kind, host)?,
                        };
                        self.st.stack.push(v);
                    }
                    Op::Store(kind, off) => {
                        let v = self.st.stack.pop().unwrap();
                        let a = self.st.stack.pop().unwrap();
                        let size = kind.size();
                        if a.is_sym() {
                            self.store_any(a, *off, size, v, host)
                                .map_err(|e| e.or_location(|| host.location()))?;
                            continue;
                        }
                        let addr = self.check(a.b as u32 as u64 + *off as u64, size)?;
                        if !v.is_sym() && self.journals.is_empty() && !self.has_shadow(addr, size) {
                            let p = addr as usize;
                            self.mem[p..p + size as usize]
                                .copy_from_slice(&v.b.to_le_bytes()[..size as usize]);
                        } else {
                            self.store(addr, size, v)?;
                        }
                    }
                    Op::MemorySize => {
                        self.st.stack.push(V::i32((self.mem.len() / PAGE) as u32));
                    }
                    Op::MemoryGrow => {
                        let n = self.st.stack.pop().unwrap();
                        if n.is_sym() {
                            return Err(CompileError::new(
                                "a witness-dependent memory grow is not supported",
                            ));
                        }
                        let n = n.b as u32;
                        let old = (self.mem.len() / PAGE) as u32;
                        if old + n > 65536 / 2 {
                            self.st.stack.push(V::i32(u32::MAX));
                        } else {
                            self.mem.resize((old + n) as usize * PAGE, 0);
                            self.gran.resize(self.mem.len() / 8 + 1, 0);
                            self.st.stack.push(V::i32(old));
                        }
                    }
                    Op::MemoryCopy => {
                        let n = self.st.stack.pop().unwrap();
                        let s = self.st.stack.pop().unwrap();
                        let d = self.st.stack.pop().unwrap();
                        if n.is_sym() || d.is_sym() {
                            return Err(CompileError::new(
                                "a witness-dependent memory copy is not supported",
                            ));
                        }
                        self.copy(d.b as u32, s, n.b as u32)?;
                    }
                    Op::MemoryFill => {
                        let n = self.st.stack.pop().unwrap();
                        let v = self.st.stack.pop().unwrap();
                        let d = self.st.stack.pop().unwrap();
                        if n.is_sym() || d.is_sym() || v.is_sym() {
                            return Err(CompileError::new(
                                "a witness-dependent memory fill is not supported",
                            ));
                        }
                        let (d, n) = (d.b as u32, n.b as u32);
                        self.check(d as u64, n)?;
                        self.journal(d, n);
                        self.mem[d as usize..(d + n) as usize].fill(v.b as u8);
                        if n > 0 && self.has_shadow(d, n) {
                            self.clear_shadow(d, n);
                        }
                    }
                    Op::Const(c) => self.st.stack.push(V::c(*c)),
                    Op::LoadL(x, kind, off) => {
                        let a = self.st.locals[lb + *x as usize];
                        let addr = a.b as u32 as u64 + *off as u64;
                        let v = match kind {
                            Mem::I64 | Mem::I32
                                if !a.is_sym()
                                    && addr + 8 <= self.mem.len() as u64
                                    && !self.has_shadow(addr as u32, kind.size()) =>
                            {
                                let p = addr as usize;
                                let w = u64::from_le_bytes(self.mem[p..p + 8].try_into().unwrap());
                                V::c(if matches!(kind, Mem::I32) {
                                    w as u32 as u64
                                } else {
                                    w
                                })
                            }
                            _ => self.load_any(a, *off, *kind, host)?,
                        };
                        self.st.stack.push(v);
                        pc += 1;
                    }
                    Op::StoreLL(av, vv, kind, off) => {
                        let a = self.st.locals[lb + *av as usize];
                        let v = self.st.locals[lb + *vv as usize];
                        let size = kind.size();
                        if a.is_sym() {
                            self.store_any(a, *off, size, v, host)
                                .map_err(|e| e.or_location(|| host.location()))?;
                            pc += 2;
                            continue;
                        }
                        let addr = self.check(a.b as u32 as u64 + *off as u64, size)?;
                        if !v.is_sym() && self.journals.is_empty() && !self.has_shadow(addr, size) {
                            let p = addr as usize;
                            self.mem[p..p + size as usize]
                                .copy_from_slice(&v.b.to_le_bytes()[..size as usize]);
                        } else {
                            self.store(addr, size, v)?;
                        }
                        pc += 2;
                    }
                    Op::CopyLL(av, xv, k1, k2, o1, o2) => {
                        let a = self.st.locals[lb + *av as usize];
                        let x = self.st.locals[lb + *xv as usize];
                        pc += 3;
                        self.copy_ll(a, x, *k1, *k2, *o1 as u32, *o2 as u32, host)?;
                    }
                    Op::CopyN(av, xv, o1, o2, n, desc) => {
                        let a = self.st.locals[lb + *av as usize];
                        let x = self.st.locals[lb + *xv as usize];
                        let (o1, o2, n, desc) = (*o1 as u32, *o2 as u32, *n as u32, *desc);
                        pc += 4 * n as usize - 1;
                        // The lowest offsets the run touches.
                        let (l1, l2) = if desc {
                            (o1 - 8 * (n - 1), o2 - 8 * (n - 1))
                        } else {
                            (o1, o2)
                        };
                        // Concrete, non-overlapping, outside branch exploration, no
                        // symbolic bytes either side: one block copy, exactly what the
                        // word-by-word copies do then (in either order).
                        let (src, dst, len) = (
                            x.b as u32 as u64 + l1 as u64,
                            a.b as u32 as u64 + l2 as u64,
                            8 * n as u64,
                        );
                        let mem_len = self.mem.len() as u64;
                        if !x.is_sym()
                            && !a.is_sym()
                            && self.journals.is_empty()
                            && src + len <= mem_len
                            && dst + len <= mem_len
                            && (src + len <= dst || dst + len <= src)
                            && !self.has_shadow(src as u32, len as u32)
                            && !self.has_shadow(dst as u32, len as u32)
                        {
                            let (src, dst, len) = (src as usize, dst as usize, len as usize);
                            self.mem.copy_within(src..src + len, dst);
                        } else {
                            for k in 0..n {
                                let (p1, p2) = if desc {
                                    (o1 - 8 * k, o2 - 8 * k)
                                } else {
                                    (o1 + 8 * k, o2 + 8 * k)
                                };
                                self.copy_ll(a, x, Mem::I64, Mem::I64, p1, p2, host)?;
                            }
                        }
                    }
                    Op::AddLC(x, c) => {
                        let a = self.st.locals[lb + *x as usize];
                        let r = if a.is_sym() {
                            self.sym_bin(Bin::Add, false, a, V::i32(*c), host)?
                        } else {
                            V::i32((a.b as u32).wrapping_add(*c))
                        };
                        self.st.stack.push(r);
                        pc += 2;
                    }
                    Op::I32Eqz | Op::I64Eqz => {
                        let a = self.st.stack.pop().unwrap();
                        let r = if a.is_sym() {
                            self.sym_eqz(a, host)?
                        } else {
                            let x = if matches!(op, Op::I32Eqz) {
                                a.b as u32 as u64
                            } else {
                                a.b
                            };
                            V::i32((x == 0) as u32)
                        };
                        self.st.stack.push(r);
                    }
                    Op::I32Bin(o) => {
                        let b = self.st.stack.pop().unwrap();
                        let a = self.st.stack.pop().unwrap();
                        let r = if a.is_sym() || b.is_sym() {
                            self.sym_bin(*o, false, a, b, host)?
                        } else {
                            V::i32(i32_bin(*o, a.b as u32, b.b as u32)?)
                        };
                        self.st.stack.push(r);
                    }
                    Op::I64Bin(o) => {
                        let b = self.st.stack.pop().unwrap();
                        let a = self.st.stack.pop().unwrap();
                        let r = if a.is_sym() || b.is_sym() {
                            self.sym_bin(*o, true, a, b, host)?
                        } else {
                            V::c(i64_bin(*o, a.b, b.b)?)
                        };
                        self.st.stack.push(r);
                    }
                    Op::I32Cmp(o) => {
                        let b = self.st.stack.pop().unwrap();
                        let a = self.st.stack.pop().unwrap();
                        let r = if a.is_sym() || b.is_sym() {
                            self.sym_cmp(*o, false, a, b, host)?
                        } else {
                            V::i32(i32_cmp(*o, a.b as u32, b.b as u32) as u32)
                        };
                        self.st.stack.push(r);
                    }
                    Op::I64Cmp(o) => {
                        let b = self.st.stack.pop().unwrap();
                        let a = self.st.stack.pop().unwrap();
                        let r = if a.is_sym() || b.is_sym() {
                            self.sym_cmp(*o, true, a, b, host)?
                        } else {
                            V::i32(i64_cmp(*o, a.b, b.b) as u32)
                        };
                        self.st.stack.push(r);
                    }
                    Op::I32Un(o) => {
                        let a = self.concrete_top(host, "a bit-count")?;
                        let x = a as u32;
                        let r = match o {
                            Un::Clz => x.leading_zeros(),
                            Un::Ctz => x.trailing_zeros(),
                            Un::Popcnt => x.count_ones(),
                        };
                        self.st.stack.push(V::i32(r));
                    }
                    Op::I64Un(o) => {
                        let x = self.concrete_top(host, "a bit-count")?;
                        let r = match o {
                            Un::Clz => x.leading_zeros(),
                            Un::Ctz => x.trailing_zeros(),
                            Un::Popcnt => x.count_ones(),
                        };
                        self.st.stack.push(V::c(r as u64));
                    }
                    Op::I32WrapI64 => {
                        let a = self.st.stack.pop().unwrap();
                        let r = if a.is_sym() {
                            match self.syms[a.s as usize] {
                                Sym::Wire { width, .. } if width > 32 => {
                                    host.int_trunc(self, a, 32)?
                                }
                                _ => self.slice(a, 0, 4)?,
                            }
                        } else {
                            V::i32(a.b as u32)
                        };
                        self.st.stack.push(r);
                    }
                    Op::I64ExtendI32U => {
                        let a = self.st.stack.pop().unwrap();
                        let r = if a.is_sym() {
                            a // a wire / select of non-negative values is width-agnostic
                        } else {
                            V::c(a.b as u32 as u64)
                        };
                        self.st.stack.push(r);
                    }
                    Op::I64ExtendI32S => {
                        let a = self.st.stack.pop().unwrap();
                        let r = if a.is_sym() {
                            self.sym_sext(a, 32, 64, Some(&mut *host))?
                        } else {
                            V::c(a.b as u32 as i32 as i64 as u64)
                        };
                        self.st.stack.push(r);
                    }
                    Op::I32Extend8S
                    | Op::I32Extend16S
                    | Op::I64Extend8S
                    | Op::I64Extend16S
                    | Op::I64Extend32S => {
                        let a = self.st.stack.pop().unwrap();
                        let (bits, wide) = match op {
                            Op::I32Extend8S => (8, false),
                            Op::I32Extend16S => (16, false),
                            Op::I64Extend8S => (8, true),
                            Op::I64Extend16S => (16, true),
                            _ => (32, true),
                        };
                        let r = if a.is_sym() {
                            self.sym_sext(a, bits, if wide { 64 } else { 32 }, Some(&mut *host))?
                        } else {
                            let x = ((a.b << (64 - bits)) as i64 >> (64 - bits)) as u64;
                            if wide { V::c(x) } else { V::i32(x as u32) }
                        };
                        self.st.stack.push(r);
                    }
                    Op::FBin(wide, o) => {
                        let b = self.concrete_top(host, "a float operation")?;
                        let a = self.concrete_top(host, "a float operation")?;
                        self.st.stack.push(V::c(f_bin(*wide, *o, a, b)));
                    }
                    Op::FCmp(wide, o) => {
                        let b = self.concrete_top(host, "a float comparison")?;
                        let a = self.concrete_top(host, "a float comparison")?;
                        self.st.stack.push(V::i32(f_cmp(*wide, *o, a, b) as u32));
                    }
                    Op::FUn(wide, o) => {
                        let a = self.concrete_top(host, "a float operation")?;
                        self.st.stack.push(V::c(f_un(*wide, *o, a)));
                    }
                    Op::FConvert(c) => {
                        let a = self.concrete_top(host, "a float conversion")?;
                        self.st.stack.push(V::c(f_conv(*c, a)?));
                    }
                }
            }
        }
    }

    fn concrete_top(&mut self, host: &dyn Host, what: &str) -> CompileResult<u64> {
        let v = self.st.stack.pop().unwrap();
        if v.is_sym() {
            return Err(
                CompileError::new(format!("{what} on a witness value is not supported"))
                    .or_location(|| host.location()),
            );
        }
        Ok(v.b)
    }

    /// `local.get a; local.get x; <load k1 o1>; <store k2 o2>` with the locals'
    /// values `a`, `x`: the load as `Op::Load` does it, then the store as `Op::Store`.
    #[inline]
    #[allow(clippy::too_many_arguments)]
    fn copy_ll(
        &mut self,
        a: V,
        x: V,
        k1: Mem,
        k2: Mem,
        o1: u32,
        o2: u32,
        host: &mut dyn Host,
    ) -> CompileResult<()> {
        let addr = x.b as u32 as u64 + o1 as u64;
        let v = match k1 {
            Mem::I64 | Mem::I32
                if !x.is_sym()
                    && addr + 8 <= self.mem.len() as u64
                    && !self.has_shadow(addr as u32, k1.size()) =>
            {
                let p = addr as usize;
                let w = u64::from_le_bytes(self.mem[p..p + 8].try_into().unwrap());
                V::c(if matches!(k1, Mem::I32) {
                    w as u32 as u64
                } else {
                    w
                })
            }
            _ => self.load_any(x, o1, k1, host)?,
        };
        let size = k2.size();
        if a.is_sym() {
            return self
                .store_any(a, o2, size, v, host)
                .map_err(|e| e.or_location(|| host.location()));
        }
        let addr = self.check(a.b as u32 as u64 + o2 as u64, size)?;
        if !v.is_sym() && self.journals.is_empty() && !self.has_shadow(addr, size) {
            let p = addr as usize;
            self.mem[p..p + size as usize].copy_from_slice(&v.b.to_le_bytes()[..size as usize]);
        } else {
            self.store(addr, size, v)?;
        }
        Ok(())
    }

    #[inline]
    /// [`Self::load_op`], also through a pointer `base + o` with `o` a witness taking
    /// few values (a lookup table LLVM made of a `match`, or `a[i]` for a narrow `i`;
    /// see [`Host::index_form`]): the value is the select over every possible `o` —
    /// one whose address is out of bounds (a trap) is ruled out.
    fn load_any(&mut self, a: V, off: u32, kind: Mem, host: &mut dyn Host) -> CompileResult<V> {
        // A select of pointers: load through each.
        if a.is_sym()
            && let Sym::Ite { cond, t, e } = self.syms[a.s as usize].clone()
        {
            let tv = self.load_any(t, off, kind, host)?;
            let ev = self.load_any(e, off, kind, host)?;
            return Ok(self.ite(cond, tv, ev));
        }
        if a.is_sym()
            && matches!(self.syms[a.s as usize], Sym::Wire { .. })
            && let Some((base, offsets, idx)) = host.index_form(self, a)
        {
            if self.probing {
                return Err(probe_end());
            }
            let size = kind.size() as u64;
            let mut vals: Vec<(V, V)> = Vec::new(); // (idx == o, value)
            for o in offsets {
                let addr = (base + o) & 0xffff_ffff;
                let eq = host.int_cmp(self, Cmp::Eq, true, idx, V::c(o))?;
                if addr + off as u64 + size > self.mem.len() as u64 {
                    // Out of bounds traps: this offset is impossible.
                    if eq.is_sym() {
                        host.require_cond(self, eq.s, false)?;
                    }
                    continue;
                }
                let v = self.load_op(V::c(addr), off, kind)?;
                vals.push((eq, v));
            }
            let Some(&(_, mut r)) = vals.last() else {
                return Err(
                    CompileError::new("circuit execution trapped: out-of-bounds load").diverging(),
                );
            };
            for &(eq, v) in vals.iter().rev().skip(1) {
                r = if eq.is_sym() {
                    self.ite(eq.s, v, r)
                } else if eq.b != 0 {
                    v
                } else {
                    r
                };
            }
            return Ok(r);
        }
        self.load_op(a, off, kind)
    }

    fn load_op(&mut self, a: V, off: u32, kind: Mem) -> CompileResult<V> {
        let size = kind.size();
        if a.is_sym() {
            // A load through a select of two pointers: load both.
            if let Sym::Ite { cond, t, e } = self.syms[a.s as usize].clone() {
                let tv = self.load_op(t, off, kind)?;
                let ev = self.load_op(e, off, kind)?;
                return Ok(self.ite(cond, tv, ev));
            }
            return Err(CompileError::new(
                "a load through a witness-dependent pointer is not supported",
            )
            .with_help(
                "a witness index works when it takes at most 1024 values: index with a \
                 narrow integer (e.g. `table[x as u8 as usize]`, `table[(x & 7) as usize]`)",
            ));
        }
        let addr = self.check(a.b as u32 as u64 + off as u64, size)?;
        let v = self.load(addr, size)?;
        if v.is_sym() {
            return match kind {
                // `reg`: the result register's width, so a concrete arm of a select
                // sign-extends to 32 bits for an `i32` load (not 64).
                Mem::I32_8S | Mem::I32_16S => self.sym_sext(v, 8 * size, 32, None),
                Mem::I64_8S | Mem::I64_16S | Mem::I64_32S => self.sym_sext(v, 8 * size, 64, None),
                _ => Ok(v),
            };
        }
        let x = v.b;
        Ok(V::c(match kind {
            Mem::I32_8S => (x as u8 as i8 as i32) as u32 as u64,
            Mem::I32_16S => (x as u16 as i16 as i32) as u32 as u64,
            Mem::I64_8S => x as u8 as i8 as i64 as u64,
            Mem::I64_16S => x as u16 as i16 as i64 as u64,
            Mem::I64_32S => x as u32 as i32 as i64 as u64,
            _ => x,
        }))
    }

    fn copy(&mut self, d: u32, s: V, n: u32) -> CompileResult<()> {
        if n == 0 {
            return Ok(());
        }
        if s.is_sym() {
            // memcpy from a select of pointers (nested selects too): load every word
            // through the select (`load_op` recurses into each arm), then store, so an
            // overlapping destination can't clobber a word before it is read.
            if !matches!(self.syms[s.s as usize], Sym::Ite { .. }) {
                return Err(CompileError::new(
                    "a memory copy from a witness-dependent pointer is not supported",
                ));
            }
            let mut words = Vec::new();
            let mut i = 0;
            while i < n {
                let w = [8, 4, 2, 1].into_iter().find(|&w| w <= n - i).unwrap();
                words.push((i, w, self.load_op(s, i, word_mem(w))?));
                i += w;
            }
            for (i, w, v) in words {
                self.store(d + i, w, v)?;
            }
            return Ok(());
        }
        let s = s.b as u32;
        self.check(s as u64, n)?;
        self.check(d as u64, n)?;
        self.journal(d, n);
        let sym_src = self.has_shadow(s, n);
        let sym_dst = self.has_shadow(d, n);
        // Symbolic bytes of the source (only granules that hold any), read before the
        // bytes move (the ranges may overlap).
        let moved: Vec<(u32, SymByte)> = if sym_src {
            let (g0, g1) = (s >> 3, (s + n - 1) >> 3);
            (g0..=g1)
                .filter(|&g| self.gran[g as usize] != 0)
                .flat_map(|g| (g << 3).max(s)..((g << 3) + 8).min(s + n))
                .filter_map(|a| self.shadow.get(&a).map(|&sb| (a - s, sb)))
                .collect()
        } else {
            Vec::new()
        };
        self.mem
            .copy_within(s as usize..(s + n) as usize, d as usize);
        if sym_dst {
            self.clear_shadow(d, n);
        }
        for (off, sb) in moved {
            self.set_shadow(d + off, Some(sb));
        }
        Ok(())
    }

    fn ret(&mut self, fi: usize, host: Option<&mut dyn Host>) {
        // Results are already on top of the stack (the function block's End).
        let fr = self.st.frames.pop().expect("frame");
        debug_assert_eq!(fi, self.st.frames.len());
        self.st.locals.truncate(fr.locals_base as usize);
        if let Some(h) = host
            && self.path_depth == 0
        {
            h.call_end();
        }
    }

    // --- symbolic operations --------------------------------------------------

    /// Classify a branch condition.
    fn cond(&mut self, c: V, host: &mut dyn Host) -> CompileResult<Cond> {
        if !c.is_sym() {
            return Ok(Cond::Known(c.b as u32 != 0));
        }
        match self.syms[c.s as usize].clone() {
            Sym::Wire { width: 1, .. } => Ok(Cond::Sym(c.s)),
            Sym::Ite { cond, t, e } => {
                // `cond ? t : e` used as a condition: fold the boolean selects.
                match (self.cond(t, host)?, self.cond(e, host)?) {
                    (Cond::Known(true), Cond::Known(false)) => Ok(Cond::Sym(cond)),
                    (Cond::Known(false), Cond::Known(true)) => {
                        let n = host.not(self, V { b: 0, s: cond })?;
                        Ok(Cond::Sym(n.s))
                    }
                    (Cond::Known(a), Cond::Known(b)) if a == b => Ok(Cond::Known(a)),
                    _ => {
                        // `cond ? t : e` with a witness arm: its truth value is the
                        // boolean mux `(cond ∧ t′) ∨ (¬cond ∧ e′)` (`x′` = `x ≠ 0`).
                        if self.probing {
                            return Err(probe_end());
                        }
                        let c = V { b: 0, s: cond };
                        let tb = self.truthy(t, host)?;
                        let eb = self.truthy(e, host)?;
                        let a = host.bool_op(self, BoolOp::And, c, tb)?;
                        let nc = host.not(self, c)?;
                        let b = host.bool_op(self, BoolOp::And, nc, eb)?;
                        let o = host.bool_op(self, BoolOp::Or, a, b)?;
                        self.cond(o, host)
                    }
                }
            }
            // A branch on an integer means "is it nonzero" (LLVM branches on `x`,
            // `x & mask`, `x >> k`, … for overflow and bounds checks): make that a
            // `{0,1}` wire with the is-zero gadget and branch on it.
            Sym::Wire { .. } | Sym::Bytes(_) => {
                if self.probing {
                    return Err(probe_end());
                }
                let nz = host.int_cmp(self, Cmp::Ne, true, c, V::c(0))?;
                self.cond(nz, host)
            }
            Sym::None => unreachable!(),
        }
    }

    fn bool_like(&self, v: V) -> bool {
        if !v.is_sym() {
            return v.b <= 1;
        }
        match &self.syms[v.s as usize] {
            Sym::Wire { width, .. } => *width == 1,
            Sym::Ite { t, e, .. } => self.bool_like(*t) && self.bool_like(*e),
            Sym::Bytes(_) | Sym::None => false,
        }
    }

    fn sym_eqz(&mut self, a: V, host: &mut dyn Host) -> CompileResult<V> {
        if let Sym::Ite { cond, t, e } = self.syms[a.s as usize].clone() {
            let t2 = self.eqz_any(t, host)?;
            let e2 = self.eqz_any(e, host)?;
            return Ok(self.ite(cond, t2, e2));
        }
        if self.bool_like(a) {
            return host.not(self, a);
        }
        host.int_cmp(self, Cmp::Eq, true, a, V::c(0))
    }

    /// `a ≠ 0` as a `{0,1}` value.
    fn truthy(&mut self, a: V, host: &mut dyn Host) -> CompileResult<V> {
        if !a.is_sym() {
            return Ok(V::i32((a.b != 0) as u32));
        }
        if self.bool_like(a) {
            return Ok(a);
        }
        let z = self.eqz_any(a, host)?;
        host.not(self, z)
    }

    fn eqz_any(&mut self, a: V, host: &mut dyn Host) -> CompileResult<V> {
        if a.is_sym() {
            self.sym_eqz(a, host)
        } else {
            Ok(V::i32((a.b == 0) as u32))
        }
    }

    /// Sign-extend the low `bits` of `a` to `reg` bits. Without a host (a load) only
    /// values that are non-negative as `bits`-bit integers are supported.
    fn sym_sext(
        &mut self,
        a: V,
        bits: u32,
        reg: u32,
        host: Option<&mut dyn Host>,
    ) -> CompileResult<V> {
        let sext_c = |x: u64| {
            let x = ((x << (64 - bits)) as i64 >> (64 - bits)) as u64;
            if reg == 32 { V::i32(x as u32) } else { V::c(x) }
        };
        match self.syms[a.s as usize].clone() {
            Sym::Wire { width, .. } if width < bits => Ok(a),
            Sym::Ite { cond, t, e } => {
                let arm = |m: &mut Self, v: V, h: Option<&mut dyn Host>| {
                    if v.is_sym() {
                        m.sym_sext(v, bits, reg, h)
                    } else {
                        Ok(sext_c(v.b))
                    }
                };
                let (t2, e2) = match host {
                    Some(h) => (arm(self, t, Some(&mut *h))?, arm(self, e, Some(&mut *h))?),
                    None => (arm(self, t, None)?, arm(self, e, None)?),
                };
                Ok(self.ite(cond, t2, e2))
            }
            _ => match host {
                Some(h) if reg > 0 => {
                    let low = h.int_trunc(self, a, bits)?;
                    if low.is_sym() {
                        h.sign_extend(self, low, bits, reg)
                    } else {
                        Ok(sext_c(low.b))
                    }
                }
                _ => Err(CompileError::new(
                    "sign extension of a witness integer is not supported",
                )),
            },
        }
    }

    fn sym_bin(&mut self, o: Bin, wide: bool, a: V, b: V, host: &mut dyn Host) -> CompileResult<V> {
        // A select with a concrete other operand: apply the op to both arms. Not a
        // select divisor: dividing by the untaken arm (which may be 0) would demand
        // a quotient for it — the divisor is muxed instead, and divided once.
        let divides = matches!(o, Bin::DivU | Bin::RemU | Bin::DivS | Bin::RemS)
            && !matches!(
                self.syms.get(b.s as usize),
                Some(Sym::Ite { t, e, .. }) if !t.is_sym() && !e.is_sym() && t.b != 0 && e.b != 0
            );
        for (x, y, x_left) in [(a, b, true), (b, a, false)] {
            if (x_left || !divides)
                && x.is_sym()
                && let Sym::Ite { cond, t, e } = self.syms[x.s as usize].clone()
                && (!y.is_sym() || matches!(self.syms[y.s as usize], Sym::Wire { .. }))
            {
                let (ta, tb) = if x_left { (t, y) } else { (y, t) };
                let (ea, eb) = if x_left { (e, y) } else { (y, e) };
                let t2 = self.bin_any(o, wide, ta, tb, host)?;
                let e2 = self.bin_any(o, wide, ea, eb, host)?;
                return Ok(self.ite(cond, t2, e2));
            }
        }
        // Boolean algebra on `{0,1}` values.
        if self.bool_like(a) && self.bool_like(b) {
            match o {
                Bin::And => return host.bool_op(self, BoolOp::And, a, b),
                Bin::Or => return host.bool_op(self, BoolOp::Or, a, b),
                Bin::Xor => {
                    if !b.is_sym() && b.b == 1 {
                        return host.not(self, a);
                    }
                    if !a.is_sym() && a.b == 1 {
                        return host.not(self, b);
                    }
                    if !b.is_sym() && b.b == 0 {
                        return Ok(a);
                    }
                    if !a.is_sym() && a.b == 0 {
                        return Ok(b);
                    }
                    return host.bool_op(self, BoolOp::Xor, a, b);
                }
                _ => {}
            }
        }
        // A mask that keeps all of a narrow wire's bits is the identity.
        if let Bin::And = o {
            for (x, y) in [(a, b), (b, a)] {
                if x.is_sym()
                    && !y.is_sym()
                    && let Sym::Wire { width, .. } = self.syms[x.s as usize]
                    && width < 64
                    && y.b & ((1u64 << width) - 1) == (1u64 << width) - 1
                {
                    return Ok(x);
                }
            }
        }
        // `x | 0`, `x ^ 0`, `x + 0`, `x - 0`, `x * 1`, shifts by 0: identities.
        if !b.is_sym() {
            let ident = match o {
                Bin::Or | Bin::Xor | Bin::Add | Bin::Sub | Bin::Shl | Bin::ShrU | Bin::ShrS => {
                    b.b == 0
                }
                Bin::Mul => b.b == 1,
                _ => false,
            };
            if ident {
                return Ok(a);
            }
        }
        host.int_bin(self, o, wide, a, b)
            .map_err(|e| e.or_location(|| host.location()))
    }

    fn bin_any(&mut self, o: Bin, wide: bool, a: V, b: V, host: &mut dyn Host) -> CompileResult<V> {
        if a.is_sym() || b.is_sym() {
            return self.sym_bin(o, wide, a, b, host);
        }
        Ok(if wide {
            V::c(i64_bin(o, a.b, b.b)?)
        } else {
            V::i32(i32_bin(o, a.b as u32, b.b as u32)?)
        })
    }

    fn sym_cmp(&mut self, o: Cmp, wide: bool, a: V, b: V, host: &mut dyn Host) -> CompileResult<V> {
        for (x, y, x_left) in [(a, b, true), (b, a, false)] {
            if x.is_sym()
                && let Sym::Ite { cond, t, e } = self.syms[x.s as usize].clone()
                && !y.is_sym()
            {
                let (ta, tb) = if x_left { (t, y) } else { (y, t) };
                let (ea, eb) = if x_left { (e, y) } else { (y, e) };
                let t2 = self.cmp_any(o, wide, ta, tb, host)?;
                let e2 = self.cmp_any(o, wide, ea, eb, host)?;
                return Ok(self.ite(cond, t2, e2));
            }
        }
        // A `{0,1}` value compared with 0 or 1.
        if self.bool_like(a) && !b.is_sym() && b.b <= 1 {
            let eq_one = b.b == 1;
            return match (o, eq_one) {
                (Cmp::Eq, true) | (Cmp::Ne, false) | (Cmp::GtU, false) | (Cmp::GeU, true) => Ok(a),
                (Cmp::Eq, false) | (Cmp::Ne, true) | (Cmp::LtU, true) | (Cmp::LeU, false) => {
                    host.not(self, a)
                }
                _ => Err(CompileError::new(
                    "unsupported comparison of a witness `bool`",
                )),
            };
        }
        if self.bool_like(b) && !a.is_sym() && a.b <= 1 {
            let flipped = match o {
                Cmp::LtU => Cmp::GtU,
                Cmp::GtU => Cmp::LtU,
                Cmp::LeU => Cmp::GeU,
                Cmp::GeU => Cmp::LeU,
                other => other,
            };
            return self.sym_cmp(flipped, wide, b, a, host);
        }
        host.int_cmp(self, o, wide, a, b)
            .map_err(|e| e.or_location(|| host.location()))
    }

    fn cmp_any(&mut self, o: Cmp, wide: bool, a: V, b: V, host: &mut dyn Host) -> CompileResult<V> {
        if a.is_sym() || b.is_sym() {
            return self.sym_cmp(o, wide, a, b, host);
        }
        Ok(V::i32(if wide {
            i64_cmp(o, a.b, b.b)
        } else {
            i32_cmp(o, a.b as u32, b.b as u32)
        } as u32))
    }

    // --- fork / merge ---------------------------------------------------------

    /// Whether the path from `st` panics or traps before calling any import other
    /// than `panic` or branching on a witness value (so no constraint, no witness
    /// data touched) — following it past the current block to wherever it leads.
    /// State and memory are left as they were.
    fn probe(&mut self, module: &Module, host: &mut dyn Host, st: State) -> Option<CompileError> {
        self.probing = true;
        self.probe_steps = 0;
        let r = self.run_probe(module, host, st);
        self.probing = false;
        r
    }

    fn run_probe(
        &mut self,
        module: &Module,
        host: &mut dyn Host,
        st: State,
    ) -> Option<CompileError> {
        match self.run_path(module, host, st, &[], 0) {
            Err(e) if e.diverged => Some(e),
            _ => None,
        }
    }

    /// Run one path from `st` until the control stack is at most `stop`,
    /// recording and then undoing its memory writes. Returns the paused state
    /// and the path's writes (address → final byte contents).
    fn run_path(
        &mut self,
        module: &Module,
        host: &mut dyn Host,
        st: State,
        apply: &[(u32, u8, Option<SymByte>)],
        stop: usize,
    ) -> CompileResult<(State, Writes)> {
        let saved = std::mem::replace(&mut self.st, st);
        self.journals.push(Vec::new());
        for &(a, byte, sb) in apply {
            self.journal(a, 1);
            self.put_byte(a, byte, sb);
        }
        self.path_depth += 1;
        let r = if self.st.ctl.len() > stop {
            self.run(module, host, stop)
        } else {
            Ok(())
        };
        self.path_depth -= 1;
        let journal = self.journals.pop().expect("journal");
        // The path's writes: the final contents of every touched byte.
        let mut touched: Vec<u32> = journal
            .iter()
            .flat_map(|j| j.addr..j.addr + j.old.len() as u32)
            .collect();
        touched.sort_unstable();
        touched.dedup();
        let writes: Vec<(u32, u8, Option<SymByte>)> = touched
            .iter()
            .map(|&a| (a, self.mem[a as usize], self.shadow.get(&a).copied()))
            .collect();
        // Undo, newest first.
        for j in journal.into_iter().rev() {
            for (i, (byte, sb)) in j.old.into_iter().enumerate() {
                self.put_byte(j.addr + i as u32, byte, sb);
            }
        }
        let paused = std::mem::replace(&mut self.st, saved);
        r?;
        Ok((paused, writes))
    }

    /// [`Self::run_path`] for the arm of a witness branch where `cond == value`.
    #[allow(clippy::too_many_arguments)]
    fn run_arm(
        &mut self,
        module: &Module,
        host: &mut dyn Host,
        cond: u32,
        value: bool,
        st: State,
        apply: &[(u32, u8, Option<SymByte>)],
        stop: usize,
    ) -> CompileResult<(State, Writes)> {
        host.arm_begin(self, cond, value)?;
        let r = self.run_path(module, host, st, apply, stop);
        host.arm_end();
        r
    }

    fn put_byte(&mut self, a: u32, byte: u8, sb: Option<SymByte>) {
        self.mem[a as usize] = byte;
        self.set_shadow(a, sb);
    }

    fn fork(
        &mut self,
        module: &Module,
        host: &mut dyn Host,
        cond: u32,
        then_st: State,
        else_st: State,
        stop: usize,
    ) -> CompileResult<()> {
        if self.probing {
            // A witness branch inside a probe: the probed path panics iff both ways
            // on from here do (same budget).
            if self.run_probe(module, host, then_st).is_none() {
                return Err(probe_end());
            }
            return Err(self
                .run_probe(module, host, else_st)
                .unwrap_or_else(probe_end));
        }
        self.forks += 1;
        // Witness branches nest only when a path doesn't rejoin before the next one —
        // in practice a loop whose exit depends on a witness, which would otherwise
        // recurse without end.
        if self.path_depth >= MAX_PATH_DEPTH {
            return Err(CompileError::new(
                "witness-dependent branches nest too deeply (a loop whose length depends on a witness?)",
            )
            .with_help("loops must have compile-time-constant bounds")
            .or_location(|| host.location()));
        }
        // The common case — `assert!`, checked arithmetic, bounds checks — is an arm
        // that goes straight to a panic, with the other arm carrying on through the
        // rest of the circuit (emitting more constraints). Find that cheaply first:
        // probe each arm, stopping at the first import that isn't `panic`.
        // A probe runs past the rejoin point (`rustc` often places the panic call
        // after it): a path that reaches a panic without touching witness data or
        // branching on it is impossible for any valid witness, wherever the call is.
        let (t_probe, e_probe) = (
            self.probe(module, host, then_st.clone()),
            self.probe(module, host, else_st.clone()),
        );
        let (t_div, e_div) = (t_probe.is_some(), e_probe.is_some());
        if let (Some(e), true) = (t_probe, e_div) {
            // Every way on from here panics: this point is unreachable.
            return Err(e);
        }
        if t_div != e_div {
            let frames_before = self.st.frames.len();
            host.require_cond(self, cond, e_div)?;
            self.st = if t_div { else_st } else { then_st };
            if self.st.ctl.len() > stop {
                self.run(module, host, stop)?;
            }
            if self.path_depth == 0 {
                for _ in self.st.frames.len()..frames_before {
                    host.call_end();
                }
            }
            return Ok(());
        }
        let before = host.emitted();
        let frames_before = self.st.frames.len();
        let t_run = self.run_arm(module, host, cond, true, then_st.clone(), &[], stop);
        let t_emitted = host.emitted();
        let e_run = self.run_arm(module, host, cond, false, else_st.clone(), &[], stop);
        // An arm that can only panic/trap is impossible for a valid witness: pin the
        // condition to the other arm and continue down it alone (this is how
        // `assert!` and checked arithmetic on witnesses become constraints).
        let diverged = |r: &CompileResult<(State, Writes)>| matches!(r, Err(e) if e.diverged);
        let (t_div, e_div) = (diverged(&t_run), diverged(&e_run));

        if t_div || e_div {
            if t_div && e_div {
                return t_run.map(|_| ());
            }
            if t_emitted != before || host.emitted() != t_emitted {
                return Err(unguardable(host));
            }
            host.require_cond(self, cond, e_div)?;
            // Resume the surviving arm where it paused, its writes replayed: what it
            // emitted (guarded by the condition, now pinned) already binds.
            let (live, writes) = if t_div { e_run? } else { t_run? };
            self.st = live;
            for (a, byte, sb) in writes {
                self.journal(a, 1);
                self.put_byte(a, byte, sb);
            }
            if self.st.ctl.len() > stop {
                self.run(module, host, stop)?;
            }
            if self.path_depth == 0 {
                for _ in self.st.frames.len()..frames_before {
                    host.call_end();
                }
            }
            return Ok(());
        }
        let (mut t, mut tw) = t_run?;
        let (mut e, mut ew) = e_run?;
        // Rejoin at the same point: resume the path that paused deeper.
        loop {
            let (th, eh) = (t.ctl.len(), e.ctl.len());
            if th == eh {
                break;
            }
            let (deeper_then, h) = (th > eh, th.min(eh));
            let r = if deeper_then {
                self.run_arm(module, host, cond, true, t.clone(), &tw, h)
            } else {
                self.run_arm(module, host, cond, false, e.clone(), &ew, h)
            };
            match r {
                Ok(next) if deeper_then => (t, tw) = next,
                Ok(next) => (e, ew) = next,
                // That arm panics further on: as above, the other one is taken.
                Err(err) if err.diverged => {
                    if host.emitted() != before {
                        return Err(unguardable(host));
                    }
                    host.require_cond(self, cond, !deeper_then)?;
                    let (live, writes) = if deeper_then { (e, ew) } else { (t, tw) };
                    self.st = live;
                    for (a, byte, sb) in writes {
                        self.journal(a, 1);
                        self.put_byte(a, byte, sb);
                    }
                    if self.st.ctl.len() > stop {
                        self.run(module, host, stop)?;
                    }
                    if self.path_depth == 0 {
                        for _ in self.st.frames.len()..frames_before {
                            host.call_end();
                        }
                    }
                    return Ok(());
                }
                Err(err) => return Err(err),
            }
        }
        if host.emitted() != before {
            return Err(unguardable(host));
        }
        self.merge(cond, t, e, tw, ew)?;
        if self.path_depth == 0 {
            for _ in self.st.frames.len()..frames_before {
                host.call_end();
            }
        }
        Ok(())
    }

    fn merge(
        &mut self,
        cond: u32,
        t: State,
        e: State,
        tw: Writes,
        ew: Writes,
    ) -> CompileResult<()> {
        if t.stack.len() != e.stack.len()
            || t.locals.len() != e.locals.len()
            || t.frames.len() != e.frames.len()
            || t.frames.last().map(|f| (f.func, f.pc)) != e.frames.last().map(|f| (f.func, f.pc))
        {
            return Err(CompileError::new(
                "the two arms of a witness-dependent branch don't rejoin",
            )
            .with_help("both arms must end at the same point"));
        }
        let mut st = t.clone();
        for i in 0..st.stack.len() {
            st.stack[i] = self.ite(cond, t.stack[i], e.stack[i]);
        }
        for i in 0..st.locals.len() {
            st.locals[i] = self.ite(cond, t.locals[i], e.locals[i]);
        }
        for i in 0..st.globals.len() {
            st.globals[i] = self.ite(cond, t.globals[i], e.globals[i]);
        }
        self.st = st;
        // Memory: per touched 8-byte word, select between the two paths' contents.
        let tmap: HashMap<u32, (u8, Option<SymByte>)> =
            tw.into_iter().map(|(a, b, s)| (a, (b, s))).collect();
        let emap: HashMap<u32, (u8, Option<SymByte>)> =
            ew.into_iter().map(|(a, b, s)| (a, (b, s))).collect();
        let mut words: Vec<u32> = tmap.keys().chain(emap.keys()).map(|a| a & !7).collect();
        words.sort_unstable();
        words.dedup();
        for w in words {
            let size = 8.min(self.mem.len() as u32 - w);
            let tv = self.word_with(w, size, &tmap)?;
            let ev = self.word_with(w, size, &emap)?;
            let v = self.ite(cond, tv, ev);
            self.store(w, size, v)?;
        }
        Ok(())
    }

    /// The `size`-byte word at `w` with a path's writes overlaid on memory.
    fn word_with(
        &mut self,
        w: u32,
        size: u32,
        writes: &HashMap<u32, (u8, Option<SymByte>)>,
    ) -> CompileResult<V> {
        let saved: Vec<(u8, Option<SymByte>)> = (w..w + size)
            .map(|a| (self.mem[a as usize], self.shadow.get(&a).copied()))
            .collect();
        for a in w..w + size {
            if let Some(&(b, s)) = writes.get(&a) {
                self.put_byte(a, b, s);
            }
        }
        let v = self.load(w, size);
        for (i, (b, s)) in saved.into_iter().enumerate() {
            self.put_byte(w + i as u32, b, s);
        }
        v
    }

    // --- host-facing memory helpers ------------------------------------------

    /// Report every value that may hold a host handle index: each value on the
    /// stack, in locals and globals, and in symbolic selects (conservatively, any
    /// value — a `Field` may sit in locals limb by limb), and each `Field` in
    /// memory, recognized by its two marker limbs (`found(index, kind_word)`).
    pub fn scan_handles(
        &self,
        marker: (u64, u64),
        mut maybe: impl FnMut(u64),
        mut found: impl FnMut(u64, u64),
    ) {
        for v in self
            .st
            .stack
            .iter()
            .chain(&self.st.locals)
            .chain(&self.st.globals)
        {
            maybe(v.b);
        }
        for s in &self.syms {
            if let Sym::Ite { t, e, .. } = s {
                maybe(t.b);
                maybe(e.b);
            }
        }
        let words = self.mem.len() / 8;
        let w = |i: usize| u64::from_le_bytes(self.mem[8 * i..8 * i + 8].try_into().unwrap());
        for i in 0..words.saturating_sub(3) {
            if w(i + 3) == marker.1 && w(i + 2) == marker.0 {
                found(w(i), w(i + 1));
            }
        }
    }

    /// The four limbs of the `Field` at `addr`.
    #[inline]
    pub fn read_field(&mut self, addr: u32) -> CompileResult<[V; 4]> {
        self.check(addr as u64, 32)?;
        if !self.has_shadow(addr, 32) {
            let a = addr as usize;
            let w = |i: usize| {
                V::c(u64::from_le_bytes(
                    self.mem[a + 8 * i..a + 8 * i + 8].try_into().unwrap(),
                ))
            };
            return Ok([w(0), w(1), w(2), w(3)]);
        }
        Ok([
            self.load(addr, 8)?,
            self.load(addr + 8, 8)?,
            self.load(addr + 16, 8)?,
            self.load(addr + 24, 8)?,
        ])
    }

    /// Read `n` consecutive 8-byte words at `addr`.
    pub fn read_words(&mut self, addr: u32, n: u32) -> CompileResult<Vec<V>> {
        self.check(addr as u64, 8 * n)?;
        (0..n).map(|i| self.load(addr + 8 * i, 8)).collect()
    }

    /// Write concrete 8-byte words at `addr`.
    pub fn write_words(&mut self, addr: u32, words: &[u64]) -> CompileResult<()> {
        self.check(addr as u64, 8 * words.len() as u32)?;
        // Outside branch exploration, onto concrete memory: a plain copy (what
        // `store` does then, minus the per-word checks).
        if self.journals.is_empty() && !self.has_shadow(addr, 8 * words.len() as u32) {
            let a = addr as usize;
            for (i, &w) in words.iter().enumerate() {
                self.mem[a + 8 * i..a + 8 * i + 8].copy_from_slice(&w.to_le_bytes());
            }
            return Ok(());
        }
        for (i, &w) in words.iter().enumerate() {
            self.store(addr + 8 * i as u32, 8, V::c(w))?;
        }
        Ok(())
    }

    /// Read `len` concrete bytes (a string argument).
    pub fn read_bytes(&self, addr: u32, len: u32) -> CompileResult<Vec<u8>> {
        self.check(addr as u64, len)?;
        Ok(self.mem[addr as usize..(addr + len) as usize].to_vec())
    }
}

fn word_mem(w: u32) -> Mem {
    match w {
        8 => Mem::I64,
        4 => Mem::I32,
        2 => Mem::I32_16U,
        1 => Mem::I32_8U,
        _ => unreachable!("word widths are 1, 2, 4 or 8"),
    }
}

/// An arm did something that can't run under a guard (`Host::emitted` counts it:
/// declaring a circuit input); every constraint and hint intrinsic is guarded.
fn unguardable(host: &dyn Host) -> CompileError {
    CompileError::new("a branch on a witness value declares a circuit input inside an arm")
        .with_help("read every input before branching on witness values")
        .or_location(|| host.location())
}

/// How many witness branches may be open at once (see `fork`).
const MAX_PATH_DEPTH: u32 = 48;

fn witness_loop() -> CompileError {
    CompileError::new("a loop whose exit depends on a witness value can't be unrolled")
        .with_help("loops must have compile-time-constant bounds")
}

enum Cond {
    Known(bool),
    Sym(u32),
}

// ---------------------------------------------------------------------------
// Concrete arithmetic
// ---------------------------------------------------------------------------

fn i32_bin(o: Bin, a: u32, b: u32) -> CompileResult<u32> {
    Ok(match o {
        Bin::Add => a.wrapping_add(b),
        Bin::Sub => a.wrapping_sub(b),
        Bin::Mul => a.wrapping_mul(b),
        Bin::DivS => {
            if b == 0 || (a as i32 == i32::MIN && b as i32 == -1) {
                return Err(trap("integer divide by zero or overflow"));
            }
            (a as i32 / b as i32) as u32
        }
        Bin::DivU => a
            .checked_div(b)
            .ok_or_else(|| trap("integer divide by zero"))?,
        Bin::RemS => {
            if b == 0 {
                return Err(trap("integer remainder by zero"));
            }
            (a as i32).wrapping_rem(b as i32) as u32
        }
        Bin::RemU => a
            .checked_rem(b)
            .ok_or_else(|| trap("integer remainder by zero"))?,
        Bin::And => a & b,
        Bin::Or => a | b,
        Bin::Xor => a ^ b,
        Bin::Shl => a.wrapping_shl(b),
        Bin::ShrS => (a as i32).wrapping_shr(b) as u32,
        Bin::ShrU => a.wrapping_shr(b),
        Bin::Rotl => a.rotate_left(b % 32),
        Bin::Rotr => a.rotate_right(b % 32),
    })
}

fn i64_bin(o: Bin, a: u64, b: u64) -> CompileResult<u64> {
    Ok(match o {
        Bin::Add => a.wrapping_add(b),
        Bin::Sub => a.wrapping_sub(b),
        Bin::Mul => a.wrapping_mul(b),
        Bin::DivS => {
            if b == 0 || (a as i64 == i64::MIN && b as i64 == -1) {
                return Err(trap("integer divide by zero or overflow"));
            }
            (a as i64 / b as i64) as u64
        }
        Bin::DivU => a
            .checked_div(b)
            .ok_or_else(|| trap("integer divide by zero"))?,
        Bin::RemS => {
            if b == 0 {
                return Err(trap("integer remainder by zero"));
            }
            (a as i64).wrapping_rem(b as i64) as u64
        }
        Bin::RemU => a
            .checked_rem(b)
            .ok_or_else(|| trap("integer remainder by zero"))?,
        Bin::And => a & b,
        Bin::Or => a | b,
        Bin::Xor => a ^ b,
        Bin::Shl => a.wrapping_shl(b as u32),
        Bin::ShrS => (a as i64).wrapping_shr(b as u32) as u64,
        Bin::ShrU => a.wrapping_shr(b as u32),
        Bin::Rotl => a.rotate_left((b % 64) as u32),
        Bin::Rotr => a.rotate_right((b % 64) as u32),
    })
}

fn i32_cmp(o: Cmp, a: u32, b: u32) -> bool {
    let (sa, sb) = (a as i32, b as i32);
    match o {
        Cmp::Eq => a == b,
        Cmp::Ne => a != b,
        Cmp::LtS => sa < sb,
        Cmp::LtU => a < b,
        Cmp::GtS => sa > sb,
        Cmp::GtU => a > b,
        Cmp::LeS => sa <= sb,
        Cmp::LeU => a <= b,
        Cmp::GeS => sa >= sb,
        Cmp::GeU => a >= b,
    }
}

fn i64_cmp(o: Cmp, a: u64, b: u64) -> bool {
    let (sa, sb) = (a as i64, b as i64);
    match o {
        Cmp::Eq => a == b,
        Cmp::Ne => a != b,
        Cmp::LtS => sa < sb,
        Cmp::LtU => a < b,
        Cmp::GtS => sa > sb,
        Cmp::GtU => a > b,
        Cmp::LeS => sa <= sb,
        Cmp::LeU => a <= b,
        Cmp::GeS => sa >= sb,
        Cmp::GeU => a >= b,
    }
}

fn f_bin(wide: bool, o: FBin, a: u64, b: u64) -> u64 {
    if wide {
        let (x, y) = (f64::from_bits(a), f64::from_bits(b));
        let r = match o {
            FBin::Add => x + y,
            FBin::Sub => x - y,
            FBin::Mul => x * y,
            FBin::Div => x / y,
            FBin::Min => x.min(y),
            FBin::Max => x.max(y),
            FBin::Copysign => x.copysign(y),
        };
        r.to_bits()
    } else {
        let (x, y) = (f32::from_bits(a as u32), f32::from_bits(b as u32));
        let r = match o {
            FBin::Add => x + y,
            FBin::Sub => x - y,
            FBin::Mul => x * y,
            FBin::Div => x / y,
            FBin::Min => x.min(y),
            FBin::Max => x.max(y),
            FBin::Copysign => x.copysign(y),
        };
        r.to_bits() as u64
    }
}

fn f_cmp(wide: bool, o: FCmp, a: u64, b: u64) -> bool {
    let (x, y) = if wide {
        (f64::from_bits(a), f64::from_bits(b))
    } else {
        (
            f32::from_bits(a as u32) as f64,
            f32::from_bits(b as u32) as f64,
        )
    };
    match o {
        FCmp::Eq => x == y,
        FCmp::Ne => x != y,
        FCmp::Lt => x < y,
        FCmp::Gt => x > y,
        FCmp::Le => x <= y,
        FCmp::Ge => x >= y,
    }
}

fn f_un(wide: bool, o: FUn, a: u64) -> u64 {
    if wide {
        let x = f64::from_bits(a);
        let r = match o {
            FUn::Abs => x.abs(),
            FUn::Neg => -x,
            FUn::Sqrt => x.sqrt(),
            FUn::Ceil => x.ceil(),
            FUn::Floor => x.floor(),
            FUn::Trunc => x.trunc(),
            FUn::Nearest => x.round_ties_even(),
        };
        r.to_bits()
    } else {
        let x = f32::from_bits(a as u32);
        let r = match o {
            FUn::Abs => x.abs(),
            FUn::Neg => -x,
            FUn::Sqrt => x.sqrt(),
            FUn::Ceil => x.ceil(),
            FUn::Floor => x.floor(),
            FUn::Trunc => x.trunc(),
            FUn::Nearest => x.round_ties_even(),
        };
        r.to_bits() as u64
    }
}

fn f_conv(c: Conv, a: u64) -> CompileResult<u64> {
    let f32v = || f32::from_bits(a as u32);
    let f64v = || f64::from_bits(a);
    Ok(match c {
        Conv::I32TruncF32S | Conv::I32TruncSatF32S => f32v() as i32 as u32 as u64,
        Conv::I32TruncF32U | Conv::I32TruncSatF32U => f32v() as u32 as u64,
        Conv::I32TruncF64S | Conv::I32TruncSatF64S => f64v() as i32 as u32 as u64,
        Conv::I32TruncF64U | Conv::I32TruncSatF64U => f64v() as u32 as u64,
        Conv::I64TruncF32S | Conv::I64TruncSatF32S => f32v() as i64 as u64,
        Conv::I64TruncF32U | Conv::I64TruncSatF32U => f32v() as u64,
        Conv::I64TruncF64S | Conv::I64TruncSatF64S => f64v() as i64 as u64,
        Conv::I64TruncF64U | Conv::I64TruncSatF64U => f64v() as u64,
        Conv::F32ConvertI32S => (a as u32 as i32 as f32).to_bits() as u64,
        Conv::F32ConvertI32U => (a as u32 as f32).to_bits() as u64,
        Conv::F32ConvertI64S => (a as i64 as f32).to_bits() as u64,
        Conv::F32ConvertI64U => (a as f32).to_bits() as u64,
        Conv::F64ConvertI32S => (a as u32 as i32 as f64).to_bits(),
        Conv::F64ConvertI32U => (a as u32 as f64).to_bits(),
        Conv::F64ConvertI64S => (a as i64 as f64).to_bits(),
        Conv::F64ConvertI64U => (a as f64).to_bits(),
        Conv::F32DemoteF64 => (f64v() as f32).to_bits() as u64,
        Conv::F64PromoteF32 => (f32v() as f64).to_bits(),
        Conv::I32ReinterpretF32 | Conv::F32ReinterpretI32 => a as u32 as u64,
        Conv::I64ReinterpretF64 | Conv::F64ReinterpretI64 => a,
    })
}
