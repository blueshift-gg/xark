//! End-to-end prover benchmark: arkworks baseline vs the streaming prover, with a
//! peak-heap-tracking allocator so every phase reports its own high-water mark.
//!
//! ```text
//! bench_prove setup-reduced <circuit.xbc> <out pk.bin>     # key the template-reduced circuit
//! bench_prove ark    <circuit.xbc> <pk.bin> <inputs.json> [--reduced]
//! bench_prove stream <circuit.xbc> <pk.bin> <inputs.json> [--source xbc|min] [--tile N] [--chunk N]
//! ```
//! `--reduced` / `--source xbc` prove the template-reduced circuit (key from
//! `setup-reduced`); otherwise the boundary-minimized circuit `xark setup` keys.

use std::alloc::{GlobalAlloc, Layout, System};
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use std::time::Instant;

use ark_bn254::{Bn254, Fr};
use ark_groth16::Groth16;
use ark_serialize::{CanonicalSerialize, Compress};
use ark_snark::SNARK;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use xark_groth16::{
    BytecodeSource, ConstraintSource, FftConfig, Probe, ProgramSource, ProverConfig, SerializedPk,
};
use xark_ir::VarId;
use xark_prover::XarkCircuit;

#[path = "../tests/support/ark.rs"]
mod ark;
use ark::{ArkCircuit, convert};

struct PeakAlloc;
static CUR: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);
/// Heap tracking costs two contended atomics per allocation, which slows the
/// allocation-heavy (multi-threaded) phases several-fold. `BENCH_TIME=1` turns it
/// off so the same binary reports honest wall-clock; memory runs leave it on.
static TRACK: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(true);

#[inline(always)]
fn tracking() -> bool {
    TRACK.load(Relaxed)
}

unsafe impl GlobalAlloc for PeakAlloc {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let p = unsafe { System.alloc(l) };
        if tracking() && !p.is_null() {
            PEAK.fetch_max(CUR.fetch_add(l.size(), Relaxed) + l.size(), Relaxed);
        }
        p
    }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        let p = unsafe { System.alloc_zeroed(l) };
        if tracking() && !p.is_null() {
            PEAK.fetch_max(CUR.fetch_add(l.size(), Relaxed) + l.size(), Relaxed);
        }
        p
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        unsafe { System.dealloc(p, l) };
        if tracking() {
            CUR.fetch_sub(l.size(), Relaxed);
        }
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, new: usize) -> *mut u8 {
        let q = unsafe { System.realloc(p, l, new) };
        if tracking() && !q.is_null() {
            if new > l.size() {
                let d = new - l.size();
                PEAK.fetch_max(CUR.fetch_add(d, Relaxed) + d, Relaxed);
            } else {
                CUR.fetch_sub(l.size() - new, Relaxed);
            }
        }
        q
    }
}

#[global_allocator]
static A: PeakAlloc = PeakAlloc;

const MB: f64 = 1024.0 * 1024.0;

/// Records `(phase, ms, peak heap during the phase, live heap after)`.
struct Phases {
    t: Instant,
    t0: Instant,
    overall_peak: usize,
    rows: Vec<(String, f64, usize, usize)>,
}

impl Phases {
    fn new() -> Self {
        PEAK.store(CUR.load(Relaxed), Relaxed);
        Phases {
            t: Instant::now(),
            t0: Instant::now(),
            overall_peak: 0,
            rows: Vec::new(),
        }
    }
    fn mark(&mut self, name: &str) {
        let peak = PEAK.load(Relaxed);
        let cur = CUR.load(Relaxed);
        self.overall_peak = self.overall_peak.max(peak);
        self.rows.push((
            name.to_string(),
            self.t.elapsed().as_secs_f64() * 1e3,
            peak,
            cur,
        ));
        PEAK.store(cur, Relaxed);
        self.t = Instant::now();
    }
    fn print(&self, label: &str) {
        eprintln!("── {label}");
        eprintln!(
            "  {:<22} {:>10} {:>14} {:>12}",
            "phase", "ms", "peak heap MB", "live MB"
        );
        for (n, ms, p, c) in &self.rows {
            eprintln!(
                "  {:<22} {:>10.1} {:>14.1} {:>12.1}",
                n,
                ms,
                *p as f64 / MB,
                *c as f64 / MB
            );
        }
        eprintln!(
            "  {:<22} {:>10.1} {:>14.1}",
            "TOTAL",
            self.t0.elapsed().as_secs_f64() * 1e3,
            self.overall_peak as f64 / MB
        );
        println!(
            "{{\"label\":{label:?},\"total_ms\":{:.1},\"peak_heap_mb\":{:.1},\"phases\":[{}]}}",
            self.t0.elapsed().as_secs_f64() * 1e3,
            self.overall_peak as f64 / MB,
            self.rows
                .iter()
                .map(|(n, ms, p, _)| format!(
                    "{{\"phase\":{n:?},\"ms\":{ms:.1},\"peak_mb\":{:.1}}}",
                    *p as f64 / MB
                ))
                .collect::<Vec<_>>()
                .join(",")
        );
    }
}

impl Probe for Phases {
    fn mark(&mut self, phase: &'static str) {
        if phase != "start" {
            Phases::mark(self, phase);
        }
    }
}

fn arg_val(args: &[String], k: &str) -> Option<String> {
    args.iter()
        .position(|a| a == k)
        .map(|i| args[i + 1].clone())
}

fn solve(xbc: &[u8], inputs_path: &str) -> BTreeMap<VarId, Fr> {
    let json: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(inputs_path).unwrap()).unwrap();
    let names: BTreeMap<String, String> = json
        .as_object()
        .unwrap()
        .iter()
        .map(|(k, v)| (k.clone(), v.as_str().unwrap().to_string()))
        .collect();
    let vars = xark_ir::function_decode::decode_input_vars(xbc);
    let ids = xark_prover::resolve_input_ids(&vars, &names).unwrap();
    drop(vars);
    let (fp, _) = xark_ir::function_decode::stream_solve_verify(xbc, &ids).unwrap();
    xark_prover::lower_witness(&fp)
}

fn reduced(xbc: &[u8]) -> xark_ir::R1csProgram {
    xark_ir::function_decode::expand_function_blob_reduced(xbc)
        .unwrap()
        .into_r1cs()
}

fn main() {
    // Must be decided before any allocation is tracked (CUR would underflow if
    // tracking switched off/on mid-run).
    if std::env::var("BENCH_TIME").is_ok() {
        TRACK.store(false, Relaxed);
    }
    if std::env::var("NO_BATCH_AFFINE").is_ok() {
        xark_groth16::msm::BATCH_AFFINE.store(false, Relaxed);
    }
    let args: Vec<String> = std::env::args().collect();
    let mode = args[1].as_str();
    let xbc = std::fs::read(&args[2]).unwrap();
    let pk_path = std::path::PathBuf::from(&args[3]);

    if mode == "setup-reduced" {
        let prog = reduced(&xbc);
        eprintln!("reduced circuit: {} constraints", prog.constraints.len());
        let circ = XarkCircuit::for_setup_preminimized(prog);
        let (pk, _) = Groth16::<Bn254>::circuit_specific_setup(
            ArkCircuit::of(&circ),
            &mut ChaCha20Rng::seed_from_u64(7),
        )
        .unwrap();
        let mut buf = b"XKPK\x01\x00".to_vec();
        pk.serialize_with_mode(&mut buf, Compress::Yes).unwrap();
        std::fs::write(&pk_path, buf).unwrap();
        return;
    }
    if mode == "counts" {
        let r = reduced(&xbc);
        let m = XarkCircuit::for_setup(r.clone()).prog().clone();
        let s = BytecodeSource::new(&xbc).unwrap();
        let nnz = |p: &xark_ir::R1csProgram| {
            p.constraints
                .iter()
                .map(|c| c.a.terms.len() + c.b.terms.len() + c.c.terms.len())
                .sum::<usize>()
        };
        println!(
            "reduced: {} rows {} vars {} nnz | minimized: {} rows {} vars {} nnz | xbc items: {} (largest {} rows)",
            r.constraints.len(),
            r.variables.len(),
            nnz(&r),
            m.constraints.len(),
            m.variables.len(),
            nnz(&m),
            s.stream().num_items(),
            s.max_item_rows()
        );
        return;
    }

    if mode == "rows" {
        // ⟨A_i,z⟩, ⟨B_i,z⟩, ⟨C_i,z⟩ for every row: compiled templates vs expansion.
        let assign = solve(&xbc, &args[4]);
        let mut src = BytecodeSource::new(&xbc).unwrap();
        let z = src.layout().assignment_from_map(&assign);
        let m = src.num_constraints();
        for threads in [1usize, 16] {
            let pool = rayon::ThreadPoolBuilder::new()
                .num_threads(threads)
                .build()
                .unwrap();
            for compiled in [false, true] {
                src.set_compiled(compiled);
                let best = (0..3)
                    .map(|_| {
                        pool.install(|| {
                            let (mut a, mut b, mut c) = (
                                vec![Fr::from(0u64); m],
                                vec![Fr::from(0u64); m],
                                vec![Fr::from(0u64); m],
                            );
                            let t = Instant::now();
                            xark_groth16::r1cs::eval_rows(
                                &src,
                                &z,
                                1 << 14,
                                [Some(&mut a), Some(&mut b), Some(&mut c)],
                            );
                            t.elapsed().as_secs_f64()
                        })
                    })
                    .fold(f64::MAX, f64::min);
                println!(
                    "threads {threads:2} {:>9}: {best:.3}s per pass ({m} rows)",
                    if compiled { "compiled" } else { "expanded" }
                );
            }
        }
        return;
    }
    if mode == "srcmem" {
        let before = CUR.load(Relaxed);
        PEAK.store(before, Relaxed);
        let src = BytecodeSource::new(&xbc).unwrap();
        println!(
            "BytecodeSource: live {:.1} MB, peak during build {:.1} MB, {} items",
            (CUR.load(Relaxed) - before) as f64 / MB,
            (PEAK.load(Relaxed) - before) as f64 / MB,
            src.stream().num_items()
        );
        return;
    }
    if mode == "solve" {
        let json: serde_json::Value =
            serde_json::from_str(&std::fs::read_to_string(&args[4]).unwrap()).unwrap();
        let names: BTreeMap<String, String> = json
            .as_object()
            .unwrap()
            .iter()
            .map(|(k, v)| (k.clone(), v.as_str().unwrap().to_string()))
            .collect();
        let vars = xark_ir::function_decode::decode_input_vars(&xbc);
        let ids = xark_prover::resolve_input_ids(&vars, &names).unwrap();
        for _ in 0..2 {
            let t = Instant::now();
            xark_ir::function_decode::stream_solve(&xbc, &ids).unwrap();
            let solve = t.elapsed().as_secs_f64();
            let t = Instant::now();
            xark_ir::function_decode::stream_solve_verify(&xbc, &ids).unwrap();
            println!(
                "stream_solve {solve:.2}s  solve+check+analyze {:.2}s",
                t.elapsed().as_secs_f64()
            );
        }
        return;
    }
    if mode == "warm" {
        // Key already resident (prove-many server): prove time only, both provers.
        let assign = solve(&xbc, &args[4]);
        let pk = xark_backend::Groth16Keys::read_proving_key(&pk_path).unwrap();
        let circ = XarkCircuit::for_proving_preminimized(reduced(&xbc), assign.clone());
        let src = BytecodeSource::new(&xbc).unwrap();
        let z = src.layout().assignment_from_map(&assign);
        let ark_pk: ark_groth16::ProvingKey<Bn254> = convert(&pk);
        for i in 0..3 {
            let t = Instant::now();
            Groth16::<Bn254>::prove(
                &ark_pk,
                ArkCircuit::of(&circ),
                &mut ChaCha20Rng::seed_from_u64(i),
            )
            .unwrap();
            let ark = t.elapsed().as_secs_f64();
            let t = Instant::now();
            xark_groth16::prove(
                &src,
                &z,
                &mut xark_groth16::InMemoryPk::new(&pk),
                &mut ChaCha20Rng::seed_from_u64(i),
                &ProverConfig::default(),
            )
            .unwrap();
            println!(
                "warm prove: arkworks {ark:.2}s  streaming {:.2}s",
                t.elapsed().as_secs_f64()
            );
        }
        return;
    }
    if mode == "proof-hex" {
        // Cross-runtime oracle: arkworks (CLI-equivalent minimized circuit) vs the
        // streaming prover from bytecode, same seed → same (r, s).
        let seed: u64 = args[5].parse().unwrap();
        let assign = solve(&xbc, &args[4]);
        let pk = xark_backend::Groth16Keys::read_proving_key(&pk_path).unwrap();
        // Key the arkworks side to whichever form this key was generated for.
        let red = reduced(&xbc);
        let circ = if pk.a_query.len() == red.variables.len() + 1 {
            XarkCircuit::for_proving_preminimized(red, assign.clone())
        } else {
            XarkCircuit::for_proving(red, assign.clone())
        };
        let ark_pk: ark_groth16::ProvingKey<Bn254> = convert(&pk);
        let ark = Groth16::<Bn254>::prove(
            &ark_pk,
            ArkCircuit::of(&circ),
            &mut ChaCha20Rng::seed_from_u64(seed),
        )
        .unwrap();
        let src = BytecodeSource::new(&xbc).unwrap();
        let z = src.layout().assignment_from_map(&assign);
        let ours = xark_groth16::prove(
            &src,
            &z,
            &mut SerializedPk::open(&pk_path).unwrap(),
            &mut ChaCha20Rng::seed_from_u64(seed),
            &ProverConfig::default(),
        )
        .unwrap();
        fn hex(p: &impl CanonicalSerialize) -> String {
            let mut b = Vec::new();
            p.serialize_compressed(&mut b).unwrap();
            b.iter().map(|x| format!("{x:02x}")).collect::<String>()
        }
        println!("arkworks  {}", hex(&ark));
        println!("streaming {}", hex(&ours));
        return;
    }

    let inputs = &args[4];
    let use_reduced = args.iter().any(|a| a == "--reduced");
    let source = arg_val(&args, "--source").unwrap_or_else(|| "min".into());
    let mut ph = Phases::new();

    let assign = solve(&xbc, inputs);
    ph.mark("solve_witness");

    match mode {
        "ark" => {
            let prog = reduced(&xbc);
            let circ = if use_reduced {
                XarkCircuit::for_proving_preminimized(prog, assign)
            } else {
                XarkCircuit::for_proving(prog, assign)
            };
            let public = circ.public_inputs();
            ph.mark("expand+minimize");
            let pk = xark_backend::Groth16Keys::read_proving_key(&pk_path).unwrap();
            ph.mark("load_pk");
            let ark_pk: ark_groth16::ProvingKey<Bn254> = convert(&pk);
            let _ = public;
            let proof = Groth16::<Bn254>::prove(
                &ark_pk,
                ArkCircuit::of(&circ),
                &mut ChaCha20Rng::seed_from_u64(1),
            )
            .unwrap();
            ph.mark("groth16_prove");
            drop(pk);
            let _ = proof;
            ph.print(if use_reduced {
                "arkworks (reduced key)"
            } else {
                "arkworks (minimized key)"
            });
        }
        "stream" => {
            let mut cfg = ProverConfig::default();
            if let Some(t) = arg_val(&args, "--tile") {
                cfg.fft = FftConfig {
                    tile: t.parse().unwrap(),
                    ..cfg.fft
                };
            }
            if let Some(c) = arg_val(&args, "--chunk") {
                cfg.msm_chunk = c.parse().unwrap();
            }
            if let Some(d) = arg_val(&args, "--spill") {
                cfg.spill_dir = Some(d.into());
            }
            let mut spk = SerializedPk::open(&pk_path).unwrap();
            let run = |src: &dyn ConstraintSource, ph: &mut Phases, spk: &mut SerializedPk<_>| {
                let z = src.layout().assignment_from_map(&assign);
                ph.mark("witness_vector");
                let mut rng = ChaCha20Rng::seed_from_u64(1);
                use ark_ff::UniformRand;
                let (r, s) = (Fr::rand(&mut rng), Fr::rand(&mut rng));
                xark_groth16::prove_with_randomness(src, &z, spk, r, s, &cfg, ph).unwrap()
            };
            if source == "xbc" {
                let src = BytecodeSource::new(&xbc).unwrap();
                ph.mark("bytecode_source");
                drop(xbc);
                run(&src, &mut ph, &mut spk);
                ph.print("streaming (bytecode source, reduced key)");
            } else {
                let prog = XarkCircuit::for_setup(reduced(&xbc)).prog().clone();
                ph.mark("expand+minimize");
                let src = ProgramSource::new(&prog);
                run(&src, &mut ph, &mut spk);
                ph.print("streaming (minimized program, existing key)");
            }
        }
        m => panic!("unknown mode {m}"),
    }
}
