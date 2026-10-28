//! Source attribution from the circuit module's DWARF line tables.
//!
//! `xark profile` / `xark check` build the circuit with `debug = "line-tables-only"`
//! (normal builds don't: the circuit is the same, the build just does less). A wasm
//! call stack — `(function, pc)` per frame, from [`crate::interp::Machine::call_stack`]
//! — maps to source frames, inlined ones included: each wasm frame's address goes
//! through `addr2line`, which yields the inlined callees innermost-first.
//!
//! The attribution: the line is the statement in the `#[circuit]` fn, the chain the
//! functions it expanded into (short names, arithmetic operator impls elided).

use std::collections::HashMap;

use addr2line::gimli;
use xark_ir::profile::ConstraintKind;

use crate::interp::Module;

type Reader<'m> = gimli::EndianSlice<'m, gimli::LittleEndian>;

/// One source frame, outermost first.
#[derive(Clone, Debug)]
pub struct SrcFrame {
    /// Demangled function path (`xark_sha256::sha256_block`), or the wasm name.
    pub function: String,
    pub file: Option<String>,
    pub line: u32,
    pub col: u32,
}

/// A resolved attribution.
#[derive(Clone, Debug, Default)]
pub struct Attribution {
    pub file: String,
    pub line: u32,
    pub col: u32,
    pub chain: Vec<String>,
    /// A kind a function on the chain fixes (`require_bool` → booleanity).
    pub kind_hint: Option<ConstraintKind>,
}

pub struct Resolver<'m> {
    module: &'m Module,
    ctx: Option<addr2line::Context<Reader<'m>>>,
    frames: HashMap<(u32, u32), Vec<SrcFrame>>,
}

impl<'m> Resolver<'m> {
    pub fn new(module: &'m Module) -> Self {
        let ctx = (!module.debug_sections.is_empty())
            .then(|| {
                let dwarf = gimli::Dwarf::load(|id| -> Result<Reader<'m>, gimli::Error> {
                    let data = module
                        .debug_sections
                        .get(id.name())
                        .map(|d| d.as_slice())
                        .unwrap_or(&[]);
                    Ok(gimli::EndianSlice::new(data, gimli::LittleEndian))
                })
                .ok()?;
                addr2line::Context::from_dwarf(dwarf).ok()
            })
            .flatten();
        Resolver {
            module,
            ctx,
            frames: HashMap::new(),
        }
    }

    /// Whether the module carries line tables.
    pub fn has_lines(&self) -> bool {
        self.ctx.is_some()
    }

    /// The source frames of one wasm frame, outermost first.
    fn wasm_frame(&mut self, f: u32, pc: u32) -> Vec<SrcFrame> {
        if let Some(v) = self.frames.get(&(f, pc)) {
            return v.clone();
        }
        let mut out = Vec::new();
        if let (Some(ctx), Some(addr)) = (&self.ctx, self.module.address(f, pc)) {
            if let Ok(mut it) = ctx.find_frames(addr).skip_all_loads() {
                while let Ok(Some(fr)) = it.next() {
                    let function = fr
                        .function
                        .as_ref()
                        .and_then(|n| n.demangle().ok().map(|s| s.into_owned()))
                        .unwrap_or_else(|| demangle(&self.module.func_name(f)));
                    let (file, line, col) = match &fr.location {
                        Some(l) => (
                            l.file.map(str::to_string),
                            l.line.unwrap_or(0),
                            l.column.unwrap_or(0),
                        ),
                        None => (None, 0, 0),
                    };
                    out.push(SrcFrame {
                        function,
                        file,
                        line,
                        col,
                    });
                }
            }
            out.reverse();
        }
        if out.is_empty() {
            out.push(SrcFrame {
                function: demangle(&self.module.func_name(f)),
                file: None,
                line: 0,
                col: 0,
            });
        }
        self.frames.insert((f, pc), out.clone());
        out
    }

    /// The source frames of a whole wasm call stack, outermost first.
    pub fn stack(&mut self, site: &[(u32, u32)]) -> Vec<SrcFrame> {
        site.iter()
            .flat_map(|&(f, pc)| self.wasm_frame(f, pc))
            .collect()
    }

    /// Attribute a call stack: the `#[circuit]` fn's line, and the chain below it.
    pub fn attribute(&mut self, site: &[(u32, u32)]) -> Attribution {
        let frames = self.stack(site);
        let entry = self.module.entry.clone();
        // The `#[circuit]` fn's frame (else the outermost frame with a location
        // outside the toolchain's sources).
        let root = entry
            .as_deref()
            .and_then(|e| {
                let wrapper = format!("__{e}_entry");
                frames.iter().position(|f| {
                    let n = short_name(&f.function);
                    n == wrapper || n == e
                })
            })
            .or_else(|| {
                frames
                    .iter()
                    .position(|f| f.file.as_deref().is_some_and(|p| !is_toolchain(p)))
            });
        let Some(root) = root else {
            return Attribution {
                chain: chain_of(&frames),
                kind_hint: kind_hint(&frames),
                ..Attribution::default()
            };
        };
        let r = &frames[root];
        let below = &frames[root + 1..];
        Attribution {
            file: r.file.clone().unwrap_or_default(),
            line: r.line,
            col: r.col,
            chain: chain_of(below),
            kind_hint: kind_hint(below),
        }
    }

    /// Where an error happened, for a diagnostic: the innermost line in the
    /// circuit crate itself (the crate the `#[circuit]` entry is in), and — when
    /// that differs — the innermost line in a dependency (a gadget) below it, as
    /// `function (file:line)`.
    pub fn error_location(
        &mut self,
        site: &[(u32, u32)],
    ) -> (Option<(String, u32, u32)>, Option<String>) {
        let frames = self.stack(site);
        let real = |f: &&SrcFrame| {
            f.line > 0
                && f.file
                    .as_deref()
                    .is_some_and(|p| !is_toolchain(p) && !is_xark_lang(p))
        };
        // The circuit crate: where the outermost frame (the `#[circuit]` entry) is.
        let root = frames
            .iter()
            .find_map(|f| f.file.as_deref())
            .and_then(|p| p.rfind("/src/").map(|i| p[..i + 1].to_string()));
        let own = frames
            .iter()
            .rev()
            .filter(real)
            .find(|f| match (&root, f.file.as_deref()) {
                (Some(r), Some(p)) => p.starts_with(r.as_str()),
                (None, Some(p)) => !p.starts_with('/'),
                _ => false,
            });
        let inner = frames.iter().rev().find(real);
        match (own, inner) {
            (Some(o), Some(i)) if !std::ptr::eq(o, i) => (
                Some((o.file.clone().unwrap(), o.line, o.col)),
                Some(format!(
                    "inside `{}` ({}:{})",
                    short_name(&i.function),
                    i.file.as_deref().unwrap_or("?"),
                    i.line
                )),
            ),
            _ => (self.user_location(site), None),
        }
    }

    /// The innermost source location in user code (not the toolchain's sources,
    /// not the `xark` crate's own), for a diagnostic.
    pub fn user_location(&mut self, site: &[(u32, u32)]) -> Option<(String, u32, u32)> {
        let frames = self.stack(site);
        let at = |f: &SrcFrame| f.file.clone().filter(|_| f.line > 0);
        frames
            .iter()
            .rev()
            .find(|f| at(f).is_some_and(|p| !is_toolchain(&p) && !is_xark_lang(&p)))
            .or_else(|| frames.iter().rev().find(|f| at(f).is_some()))
            .map(|f| (f.file.clone().unwrap(), f.line, f.col))
    }
}

/// `core`/`alloc`/`std` sources (`/rustc/<hash>/library/…`) and cargo's registry.
fn is_toolchain(path: &str) -> bool {
    path.starts_with("/rustc/") || path.contains("/rustlib/src/rust/library/")
}

/// The `xark` language crate's own sources (`crates/lang`, or the published crate).
fn is_xark_lang(path: &str) -> bool {
    path.contains("/crates/lang/src/") || path.contains("/xark-0.")
}

/// The functions below the attributed line: user and gadget functions, down to
/// the `xark` API function they called (`pow`, `to_bits`, `require_bool`, …) —
/// not that function's own internals, nor the toolchain's.
fn chain_frames(frames: &[SrcFrame]) -> Vec<&SrcFrame> {
    let mut out = Vec::new();
    for f in frames {
        let in_lang = f.file.as_deref().is_some_and(is_xark_lang);
        if f.file.as_deref().is_some_and(is_toolchain)
            || is_internal(&f.function)
            || f.function.starts_with('{')
        {
            continue;
        }
        out.push(f);
        if in_lang {
            break;
        }
    }
    out
}

fn chain_of(frames: &[SrcFrame]) -> Vec<String> {
    let mut chain: Vec<String> = Vec::new();
    for f in chain_frames(frames) {
        let n = short_name(&f.function).to_string();
        if is_operator_impl_name(&n) || chain.last() == Some(&n) {
            continue;
        }
        chain.push(n);
    }
    chain
}

/// Toolchain and frontend plumbing frames that never belong in a chain.
fn is_internal(function: &str) -> bool {
    let p = function.trim_start_matches('<');
    p.starts_with("core::")
        || p.starts_with("alloc::")
        || p.starts_with("compiler_builtins::")
        || p.starts_with("xark::wasm::")
        || p.starts_with("xark::input::")
        || p.starts_with("xark::intrinsics::")
        || function == "__xark_main"
        || function.starts_with("__xark_")
        || function.starts_with("xark_")
}

/// Operator impls elided from attribution chains.
fn is_operator_impl_name(name: &str) -> bool {
    matches!(
        name,
        "add" | "sub" | "mul" | "neg" | "bitxor" | "from" | "into"
    )
}

/// The kind the innermost hinting function on the chain fixes.
fn kind_hint(frames: &[SrcFrame]) -> Option<ConstraintKind> {
    chain_frames(frames)
        .into_iter()
        .rev()
        .find_map(|f| match short_name(&f.function) {
            "require_bool" => Some(ConstraintKind::Booleanity),
            "inv" => Some(ConstraintKind::HintPin),
            _ => None,
        })
}

/// The last path segment of a demangled path, without generic arguments
/// (`<xark::Field as core::ops::Mul>::mul` → `mul`, `foo::bar::<8>` → `bar`).
pub fn short_name(path: &str) -> &str {
    let mut depth = 0i32;
    let mut end = path.len();
    // Strip a trailing generic argument list.
    if path.ends_with('>') {
        for (i, c) in path.char_indices().rev() {
            match c {
                '>' => depth += 1,
                '<' => {
                    depth -= 1;
                    if depth == 0 {
                        end = i;
                        break;
                    }
                }
                _ => {}
            }
        }
    }
    let s = path[..end].trim_end_matches("::");
    // The segment after the last top-level `::`.
    let mut depth = 0i32;
    let b = s.as_bytes();
    let mut start = 0;
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'<' => depth += 1,
            b'>' => depth -= 1,
            b':' if depth == 0 && i + 1 < b.len() && b[i + 1] == b':' => {
                start = i + 2;
                i += 1;
            }
            _ => {}
        }
        i += 1;
    }
    let n = &s[start..];
    if n.is_empty() { path } else { n }
}

fn demangle(name: &str) -> String {
    format!("{:#}", rustc_demangle::demangle(name))
}

#[cfg(test)]
mod tests {
    use super::short_name;

    #[test]
    fn short_names() {
        assert_eq!(short_name("xark_sha256::sha256_block"), "sha256_block");
        assert_eq!(
            short_name("<xark::lang::Field as core::ops::arith::Mul>::mul"),
            "mul"
        );
        assert_eq!(short_name("xark_bits::to_bits::<32>"), "to_bits");
        assert_eq!(short_name("cube"), "cube");
    }
}
