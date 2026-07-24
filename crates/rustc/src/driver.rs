//! `rustc_driver` glue: run the compiler through analysis, then extract, validate,
//! lower, and emit the circuit.

use std::path::PathBuf;

use rustc_hir::def_id::DefId;
use rustc_middle::mir::Body;
use rustc_middle::ty::TyCtxt;

use crate::diagnostics::CompileResult;
use crate::find_entry::find_circuit;
use crate::lower_mir::lower;
use crate::validate::validate;

pub struct R1csCallbacks {
    pub output_dir: PathBuf,
    pub field: xark_ir::FieldSpec,
    /// `--check`: validate + lower to surface every rejection as a rustc
    /// diagnostic, but skip writing artifacts (no r1cs.json / circuit.json /
    /// graph.dot). A clean run prints nothing.
    pub check_only: bool,
    /// `--profile`: additionally build the per-constraint attribution buffer and
    /// write it to a **separate** `profile.json` (never mixed into the R1CS).
    /// Only `xark profile` sets this; a normal build leaves it `false` (no
    /// span-resolution overhead, no extra file).
    pub profile: bool,
    /// `--emit-json`: also write the human-readable `circuit.json` (the primitive
    /// program as JSON). Off by default: the prover/checker load the compact
    /// binary `circuit.xbc` instead, so a normal build skips the (potentially
    /// multi-GB) `serde_json` serialization entirely. The snapshot suite and the
    /// `xark expand --ab` benchmark opt in so `circuit.json` still exists.
    pub emit_json: bool,
}

/// Isolate the rest of the compiler from rustc query churn: obtain the MIR body
/// we lower. With `-Z mir-opt-level=0` this is predictable, unoptimized MIR.
fn get_mir_body<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> &'tcx Body<'tcx> {
    tcx.optimized_mir(def_id)
}

impl rustc_driver::Callbacks for R1csCallbacks {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        match self.run(tcx) {
            Ok(()) => {
                // Let the compile finish. In `--check` mode this lets rustc emit
                // the crate metadata `cargo check` expects; in build mode it
                // proceeds to produce the rlib. A clean check prints nothing.
                rustc_driver::Compilation::Continue
            }
            Err(err) => {
                // Route the rejection through rustc's diagnostic context so it
                // becomes a real error (with a source span when known). This
                // reaches `--error-format=json` consumers like rust-analyzer,
                // and marks the session as failed so the process exits non-zero.
                let dcx = tcx.dcx();
                let mut diag = match err.span {
                    Some(span) => dcx.struct_span_err(span, err.message.clone()),
                    None => dcx.struct_err(err.message.clone()),
                };
                if let Some(help) = &err.help {
                    diag.help(help.clone());
                }
                if let Some(note) = &err.note {
                    diag.note(note.clone());
                }
                diag.emit();
                // Guarantee a non-zero exit: turn the emitted error into a fatal
                // abort that `catch_fatal_errors` (in `main`) converts to exit 1.
                // The JSON diagnostic above is already flushed to the emitter.
                dcx.abort_if_errors();
                rustc_driver::Compilation::Stop
            }
        }
    }
}

impl R1csCallbacks {
    fn run<'tcx>(&self, tcx: TyCtxt<'tcx>) -> CompileResult<()> {
        // `XARK_BUILD_TIME=1` prints a per-phase breakdown of the xark-specific
        // work inside the compile (everything after rustc's own analysis). The
        // rustc frontend cost is the `cargo build` wall time minus these.
        let timing = crate::dbg_flag("XARK_BUILD_TIME");
        let t = std::time::Instant::now();
        let entry = find_circuit(tcx)?;
        let def_id = entry.def_id.to_def_id();

        // Resolve every recognized call to an exact `DefId` once, up front.
        let registry = crate::lower_mir::build_call_registry(tcx);

        let body = get_mir_body(tcx, def_id);
        if timing {
            eprintln!("BUILD_TIME: find+registry+mir = {:?}", t.elapsed());
        }

        let t = std::time::Instant::now();
        validate(tcx, &registry, body)?;
        if timing {
            eprintln!("BUILD_TIME: validate        = {:?}", t.elapsed());
        }

        // Lower even in `--check` mode so lowering-stage rejections (e.g.
        // witness-dependent control flow) are reported too.
        let t = std::time::Instant::now();
        let output = lower(
            tcx,
            &entry,
            body,
            self.field.clone(),
            registry,
            self.profile,
        );
        if timing {
            eprintln!(
                "BUILD_TIME: lower (MIR->IR)  = {:?}{}",
                t.elapsed(),
                if output.is_err() { " [errored]" } else { "" }
            );
        }
        let output = output?;

        // When `--check --profile` both present: also write `profile.json` so
        // downstream tooling (editor extensions, CI) can consume per-line
        // constraint attribution. A plain `--check` (no `--profile`) still
        // writes nothing. Writes go to `target/xark/<pkg>/profile.json`.
        if self.check_only && self.profile {
            self.write_profile_only(&output);
        }

        if !self.check_only {
            self.emit_outputs(&output);
            // Record the entry fn name beside the artifacts so downstream (proof
            // bundle, generated client) can name things after the circuit, not
            // the crate dir. Not fatal (a correct dir-name fallback exists), but
            // warn rather than silently degrade to the wrong name.
            let entry_path = self.output_dir.join("entry");
            if let Err(e) = std::fs::write(&entry_path, &entry.name) {
                eprintln!(
                    "xark: warning: could not write {}: {e}",
                    entry_path.display()
                );
            }
        }
        Ok(())
    }

    fn emit_outputs(&self, output: &crate::lower_mir::LowerOutput) {
        std::fs::create_dir_all(&self.output_dir)
            .unwrap_or_else(|e| panic!("failed to create output dir {:?}: {e}", self.output_dir));

        // Binary "bytecode" — the compact, offset-addressed opcode stream and the
        // SOLE circuit artifact a normal build writes. It encodes the R1CS `a·b=c`
        // rows (the lossless constraint form) plus the witness-gen program, so
        // BOTH consumer views are derived from it on load: the Groth16 backend's
        // `R1csProgram` (`CircuitProgram::to_r1cs`) and the solver's
        // `PrimitiveProgram` (`to_primitive`). `roll_loops` collapses periodic
        // runs (bit decompositions, scalar ladders, hash rounds) into `REPEAT`
        // items — lossless compression that `expand` replays exactly.
        let timing = crate::dbg_flag("XARK_BUILD_TIME");
        // The compact DAG-function container is the SOLE circuit artifact. It rolls
        // periodic runs of inline rows (bit decompositions, scalar ladders, hash
        // rounds) into `REPEAT` items and captures reused functions as templates —
        // lossless compression the decoder replays exactly.
        let blob = output
            .function_xbc
            .as_ref()
            .expect("the DAG-function artifact is built for every circuit");
        if crate::dbg_flag("XARK_VERIFY") {
            verify_function_artifact(&output.r1cs, &output.primitive, blob);
        }
        if timing {
            eprintln!("BUILD_TIME: encode xbc      = {} bytes", blob.len());
        }
        let xbc_bytes: &[u8] = blob;
        let t = std::time::Instant::now();
        let xbc_path = self.output_dir.join("circuit.xbc");
        std::fs::write(&xbc_path, xbc_bytes)
            .unwrap_or_else(|e| panic!("failed to write {xbc_path:?}: {e}"));
        if timing {
            eprintln!("BUILD_TIME: write xbc       = {:?}", t.elapsed());
        }

        // JSON siblings of `circuit.xbc` — opt-in (`--emit-json`). Now that the
        // `.xbc` carries the R1CS itself, `r1cs.json` and `circuit.json` are both
        // derivable and nothing at prove/check/setup time reads them; serializing
        // them is the dominant build cost on large circuits (multi-GB for
        // ed25519). The snapshot suite and `xark expand --ab` opt in, so the
        // byte-for-byte JSON bridges (written here from `output` directly, exactly
        // as before) still hold. Compact `circuit.json`: machine-consumed, and
        // pretty-printing more than doubled it for no benefit.
        if self.emit_json {
            let circuit_json = xark_ir::primitive::to_json(&output.primitive);
            let circuit_path = self.output_dir.join("circuit.json");
            std::fs::write(&circuit_path, format!("{circuit_json}\n"))
                .unwrap_or_else(|e| panic!("failed to write {circuit_path:?}: {e}"));

            // For very large circuits skip only the *pretty-print* (multi-GB) and
            // the human-oriented DOT graph, emitting compact JSON instead.
            const DEBUG_R1CS_MAX_CONSTRAINTS: usize = 1_000_000;
            let n_r1cs = output.r1cs.constraints.len();
            let json_path = self.output_dir.join("r1cs.json");
            if n_r1cs <= DEBUG_R1CS_MAX_CONSTRAINTS {
                let json = xark_ir::to_json_pretty(&output.r1cs);
                std::fs::write(&json_path, format!("{json}\n"))
                    .unwrap_or_else(|e| panic!("failed to write {json_path:?}: {e}"));

                let dot = xark_ir::to_dot(&output.r1cs);
                let dot_path = self.output_dir.join("graph.dot");
                std::fs::write(&dot_path, dot)
                    .unwrap_or_else(|e| panic!("failed to write {dot_path:?}: {e}"));
            } else {
                let json = xark_ir::json::to_json(&output.r1cs);
                std::fs::write(&json_path, format!("{json}\n"))
                    .unwrap_or_else(|e| panic!("failed to write {json_path:?}: {e}"));
                eprintln!(
                    "xark: wrote compact r1cs.json ({n_r1cs} R1CS constraints > \
                     {DEBUG_R1CS_MAX_CONSTRAINTS}); skipped the pretty-print and the \
                     debug graph.dot"
                );
            }
        }

        eprintln!(
            "{} {} vars, {} constraints, {} witness-gen ops",
            crate::style::tag(),
            output.primitive.vars.len(),
            output.primitive.constraints.len(),
            output.primitive.witness_gen.len(),
        );

        // `--profile` only: the per-constraint attribution, in a SEPARATE file so
        // r1cs.json / circuit.json stay byte-identical.
        if self.profile {
            let source_root = std::env::current_dir()
                .map(|p| p.display().to_string())
                .unwrap_or_default();
            let prof = xark_ir::ProfileProgram {
                source_root,
                constraints: output.profile.clone(),
            };
            let profile_json = xark_ir::profile::to_json_pretty(&prof);
            let profile_path = self.output_dir.join("profile.json");
            std::fs::write(&profile_path, format!("{profile_json}\n"))
                .unwrap_or_else(|e| panic!("failed to write {profile_path:?}: {e}"));
        }
    }

    /// Write only `profile.json` — used by `--check --profile` so editors can
    /// consume per-line constraint attribution without running a full build.
    /// The output directory comes from `XARK_OUT` (set by `xark check --profile`).
    fn write_profile_only(&self, output: &crate::lower_mir::LowerOutput) {
        if self.output_dir.as_os_str().is_empty() {
            return;
        }
        let _ = std::fs::create_dir_all(&self.output_dir);
        let source_root = std::env::current_dir()
            .map(|p| p.display().to_string())
            .unwrap_or_default();
        let prof = xark_ir::ProfileProgram {
            source_root,
            constraints: output.profile.clone(),
        };
        let profile_json = xark_ir::profile::to_json_pretty(&prof);
        let profile_path = self.output_dir.join("profile.json");
        if let Err(e) = std::fs::write(&profile_path, format!("{profile_json}\n")) {
            eprintln!(
                "xark: warning: could not write {}: {e}",
                profile_path.display()
            );
        }

        // Also write a small metadata.json with variable table + circuit stats
        // so editor extensions can show stats (vars, witness ops, field).
        let meta = serde_json::json!({
            "field": self.field.name,
            "num_vars": output.primitive.vars.len(),
            "num_constraints": output.primitive.constraints.len(),
            "num_witness_ops": output.primitive.witness_gen.len(),
            "inputs": output.primitive.vars.iter()
                .filter(|v| matches!(v.role, xark_ir::primitive::VarRole::PublicInput | xark_ir::primitive::VarRole::PrivateInput))
                .map(|v| serde_json::json!({
                    "name": v.name,
                    "role": match v.role {
                        xark_ir::primitive::VarRole::PublicInput => "public",
                        xark_ir::primitive::VarRole::PrivateInput => "private",
                        _ => "derived",
                    }
                }))
                .collect::<Vec<_>>(),
        });
        let meta_path = self.output_dir.join("metadata.json");
        if let Err(e) = std::fs::write(&meta_path, serde_json::to_string_pretty(&meta).unwrap() + "\n") {
            eprintln!(
                "xark: warning: could not write {}: {e}",
                meta_path.display()
            );
        }
    }
}

/// Build-time faithfulness gate (`XARK_VERIFY`): decode the DAG-compact artifact
/// and require it reproduces the flat lowering EXACTLY — same constraints (`a·b=c`),
/// same witness program, same variable roles. The decoder is an independent
/// reimplementation of the encoding, so agreement here means the compact
/// artifact and the trusted flat form describe the identical circuit. Any
/// divergence (e.g. the multi-output var-prune bug) aborts the build with a
/// precise diff — on *this* circuit, immediately, not in a later sweep. Var names
/// are synthetic in the decoded form, so only `(id, role)` is compared.
fn verify_function_artifact(
    r1cs: &xark_ir::R1csProgram,
    primitive: &xark_ir::primitive::PrimitiveProgram,
    blob: &[u8],
) {
    let flat = xark_ir::CircuitProgram::from_lowered(r1cs, primitive);
    let art = xark_ir::function_decode::expand_function_blob(blob)
        .expect("XARK_VERIFY: the just-built function artifact must decode");

    assert_eq!(
        flat.constraints.len(),
        art.constraints.len(),
        "XARK_VERIFY: constraint count flat={} vs artifact={}",
        flat.constraints.len(),
        art.constraints.len()
    );
    for (i, (f, a)) in flat.constraints.iter().zip(&art.constraints).enumerate() {
        assert!(
            f.a == a.a && f.b == a.b && f.c == a.c,
            "XARK_VERIFY: constraint #{i} differs between flat lowering and artifact"
        );
    }

    assert_eq!(
        flat.witness_gen.len(),
        art.witness_gen.len(),
        "XARK_VERIFY: witness-op count flat={} vs artifact={}",
        flat.witness_gen.len(),
        art.witness_gen.len()
    );
    for (i, (f, a)) in flat.witness_gen.iter().zip(&art.witness_gen).enumerate() {
        assert!(
            f == a,
            "XARK_VERIFY: witness op #{i} differs between flat lowering and artifact"
        );
    }

    assert_eq!(
        flat.vars.len(),
        art.vars.len(),
        "XARK_VERIFY: variable count flat={} vs artifact={}",
        flat.vars.len(),
        art.vars.len()
    );
    for (f, a) in flat.vars.iter().zip(&art.vars) {
        assert!(
            f.id == a.id && f.role == a.role,
            "XARK_VERIFY: variable differs — flat (id={}, {:?}) vs artifact (id={}, {:?})",
            f.id,
            f.role,
            a.id,
            a.role
        );
    }

    eprintln!(
        "XARK_VERIFY: artifact ≡ flat lowering ✓ ({} constraints, {} witness ops, {} vars)",
        flat.constraints.len(),
        flat.witness_gen.len(),
        flat.vars.len()
    );
}
