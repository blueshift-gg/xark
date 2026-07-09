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
        let entry = find_circuit(tcx)?;
        let def_id = entry.def_id.to_def_id();

        // Resolve every recognized call to an exact `DefId` once, up front.
        let registry = crate::lower_mir::build_call_registry(tcx);

        let body = get_mir_body(tcx, def_id);
        validate(tcx, &registry, body)?;

        // Lower even in `--check` mode so lowering-stage rejections (e.g.
        // witness-dependent control flow) are reported too.
        let output = lower(
            tcx,
            &entry,
            body,
            self.field.clone(),
            registry,
            self.profile,
        )?;

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

        // Primitive IR — the artifact the backend lowering consumes (and the
        // sole circuit description now).
        let circuit = xark_ir::primitive::to_json_pretty(&output.primitive);
        let circuit_path = self.output_dir.join("circuit.json");
        std::fs::write(&circuit_path, format!("{circuit}\n"))
            .unwrap_or_else(|e| panic!("failed to write {circuit_path:?}: {e}"));

        // Fully-lowered R1CS. `xark setup` / `xark prove` build the Groth16
        // constraint system from r1cs.json, so it MUST always be written —
        // skipping it above a size threshold would make circuits with >1M
        // constraints impossible to set up or prove. For very large circuits we
        // skip only the *pretty-print* (which is multi-gigabyte) and the
        // human-oriented DOT graph, emitting compact JSON that the backend
        // consumes identically.
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
}
