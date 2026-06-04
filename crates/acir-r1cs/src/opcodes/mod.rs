//! Opcode-coverage analysis and classification.

pub mod arithmetic;
pub mod blackbox;
pub mod brillig;
pub mod call;
pub mod memory;
pub mod unsupported;

use acir::circuit::Opcode;
use acir::FieldElement;

/// Coarse classification of an ACIR opcode for inspection/diagnostic purposes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OpcodeClass {
    /// `AssertZero(Expression)` — supported.
    Arithmetic,
    /// Black-box function call — not supported in MVP.
    BlackBox(String),
    /// Memory init — supported by the constant-index lowering shipped in
    /// ROADMAP step WS-C.4. See `docs/memory.md`.
    MemoryInit,
    /// Memory op (read / write) — supported when the index witness is
    /// pinned to a constant by a preceding `AssertZero` (WS-C.4).
    /// Variable-index ops surface a "see WS-C.5" error at lowering time,
    /// not at classification time, because constant-pinning detection
    /// requires the full opcode stream.
    MemoryOp,
    /// `BrilligCall` — supported via the **trust-outputs** strategy. The
    /// hint outputs are allocated as witnesses; the surrounding `AssertZero`
    /// opcodes pin their values. See `docs/brillig.md` for the soundness
    /// argument (ROADMAP step WS-C.2).
    Brillig,
    /// Cross-circuit call — not supported in MVP.
    Call,
}

impl OpcodeClass {
    pub fn is_supported(&self) -> bool {
        match self {
            OpcodeClass::Arithmetic => true,
            OpcodeClass::BlackBox(name) => {
                matches!(
                    name.as_str(),
                    "range"
                        | "sha256_compression"
                        | "and"
                        | "xor"
                        | "poseidon2_permutation"
                        | "keccakf1600"
                        | "blake2s"
                        | "blake3"
                        | "aes128_encrypt"
                        | "embedded_curve_add"
                        | "multi_scalar_mul"
                        | "ecdsa_secp256k1"
                        | "ecdsa_secp256r1"
                )
            }
            OpcodeClass::Brillig => true,
            // Memory ops are accepted at classification time; variable-index
            // ops are rejected later by the lowering pass (it needs the full
            // opcode stream to know whether the index is constant). See
            // `docs/memory.md` and ROADMAP step WS-C.4.
            OpcodeClass::MemoryInit | OpcodeClass::MemoryOp => true,
            // Call opcodes are accepted at classification time. The lowering
            // pass inlines the callee with witness-index shifting (ROADMAP
            // step WS-B.5); predicated or nested calls are rejected later
            // with a clear error pointing back to ROADMAP.
            OpcodeClass::Call => true,
        }
    }

    pub fn display_name(&self) -> String {
        match self {
            OpcodeClass::Arithmetic => "AssertZero".to_string(),
            OpcodeClass::BlackBox(name) => format!("BlackBoxFuncCall::{name}"),
            OpcodeClass::MemoryInit => "MemoryInit".to_string(),
            OpcodeClass::MemoryOp => "MemoryOp".to_string(),
            OpcodeClass::Brillig => "BrilligCall".to_string(),
            OpcodeClass::Call => "Call".to_string(),
        }
    }

    /// User-facing remediation hint for unsupported opcodes.
    pub fn help(&self) -> String {
        match self {
            OpcodeClass::Arithmetic => String::new(),
            OpcodeClass::BlackBox(name) => {
                match name.as_str() {
                    "recursive_aggregation" => {
                        "Recursive Groth16 aggregation is not supported and will not be added in \
                         the BN254-only configuration. Recursive Groth16 needs a *cycle of curves* \
                         (e.g. BLS12-377 / BW6-761) — verifying a BN254 Groth16 proof inside another \
                         BN254 Groth16 circuit requires foreign-field arithmetic over BN254 Fq, which \
                         costs >10M constraints per recursive step and is not the right architecture \
                         for this. If you need proof aggregation, switch to a PLONK-family backend or \
                         a curve cycle. See ROADMAP step WS-D.8."
                            .to_string()
                    }
                    "ecdsa_secp256r1_legacy_help_unused" => String::new(),
                    "bigint_add" | "bigint_sub" | "bigint_mul" | "bigint_div"
                    | "bigint_from_le_bytes" | "bigint_to_le_bytes" => {
                        format!(
                            "BlackBoxFuncCall::{name} (non-native arbitrary-modulus bigint \
                             arithmetic) is not implemented.\n\n\
                             Noir 1.0.0-beta.21 — the pinned version this backend targets — does \
                             not expose a `std::bigint` module and its compiler emits zero BigInt \
                             opcodes from source. If you produced an artifact that contains one, \
                             you are either:\n  \
                             - on a different Noir version (bump NOIR_VERSION.md and re-test), or\n  \
                             - using an unreleased Noir feature.\n\n\
                             File an issue with the offending artifact attached and we'll wire up \
                             non-native bigint constraints. Until then this opcode is rejected at \
                             setup time so you don't waste setup on a circuit that would crash."
                        )
                    }
                    _ => format!(
                        "This backend does not support black-box function `{name}` yet.\n\
                         Try:\n  \
                         - use a circuit that does not call `{name}`, or\n  \
                         - implement support in crates/acir-r1cs/src/gadgets/, or\n  \
                         - run `xark inspect --artifact ...` to see full opcode coverage."
                    ),
                }
            }
            OpcodeClass::MemoryInit => "MemoryInit is supported by the constant-index lowering \
                                       (ROADMAP step WS-C.4). See `docs/memory.md`."
                .to_string(),
            OpcodeClass::MemoryOp => "MemoryOp is supported when the index witness is pinned to \
                                     a constant by a preceding AssertZero (ROADMAP step WS-C.4). \
                                     Variable-index ops are rejected at lowering time with a \
                                     pointer to ROADMAP step WS-C.5."
                .to_string(),
            OpcodeClass::Brillig => {
                // BrilligCall is supported via the trust-outputs strategy
                // (see docs/brillig.md). This help text is unreachable from
                // the normal unsupported-opcode error path, but is kept for
                // debug callers that introspect `OpcodeClass::help` directly.
                "BrilligCall is supported via the trust-outputs strategy: hint outputs are \
                 allocated as witnesses and the surrounding AssertZero opcodes pin their \
                 values. See docs/brillig.md for the soundness argument."
                    .to_string()
            }
            OpcodeClass::Call => {
                "Cross-circuit `Call` opcodes are not yet lowered (ROADMAP step **WS-B.5**). \
                 The artifact parses (WS-B.4 accepts multi-function programs), but each call \
                 site needs (a) the callee's witness map loaded from the witness stack, (b) the \
                 callee's opcodes inlined with the input/output `Witness` substitution, and (c) \
                 every emitted constraint gated by the call's `predicate` Expression. None of \
                 those are wired yet. Until B.5 ships, either inline the helper at the Noir \
                 source level (drop `#[fold]` / similar attributes) or constrain the call shape \
                 so Noir's compiler inlines it before emitting ACIR."
                    .to_string()
            }
        }
    }
}

pub fn classify(opcode: &Opcode<FieldElement>) -> OpcodeClass {
    match opcode {
        Opcode::AssertZero(_) => OpcodeClass::Arithmetic,
        Opcode::BlackBoxFuncCall(bb) => OpcodeClass::BlackBox(blackbox::name_of(bb)),
        Opcode::MemoryInit { .. } => OpcodeClass::MemoryInit,
        Opcode::MemoryOp { .. } => OpcodeClass::MemoryOp,
        Opcode::BrilligCall { .. } => OpcodeClass::Brillig,
        Opcode::Call { .. } => OpcodeClass::Call,
    }
}

/// Summary of opcode classifications for an artifact.
#[derive(Clone, Debug, Default)]
pub struct CoverageSummary {
    pub total: usize,
    pub supported: usize,
    pub unsupported: usize,
    pub unsupported_kinds: Vec<String>,
}

pub fn summarize(opcodes: &[Opcode<FieldElement>]) -> CoverageSummary {
    let mut summary = CoverageSummary {
        total: opcodes.len(),
        ..Default::default()
    };
    for op in opcodes {
        let class = classify(op);
        if class.is_supported() {
            summary.supported += 1;
        } else {
            summary.unsupported += 1;
            let name = class.display_name();
            if !summary.unsupported_kinds.contains(&name) {
                summary.unsupported_kinds.push(name);
            }
        }
    }
    summary
}
