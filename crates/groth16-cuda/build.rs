use std::env;
use std::path::PathBuf;

fn main() {
    if env::var_os("CARGO_FEATURE_CUSTOM_CUDA").is_none() {
        return;
    }

    let crate_dir = PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").expect("manifest dir"));
    let kernel_dir = crate_dir.join("../groth16/cuda");
    for file in [
        "msm_custom_g1.cu",
        "msm_accumulate.cuh",
        "msm_buckets.cuh",
        "msm_digits.cuh",
        "msm_plan.hpp",
        "bn254_fq.cuh",
        "bn254_g1.cuh",
    ] {
        println!("cargo:rerun-if-changed={}", kernel_dir.join(file).display());
    }

    cc::Build::new()
        .cuda(true)
        .cudart("shared")
        .include(&kernel_dir)
        .file(kernel_dir.join("msm_custom_g1.cu"))
        .flag("-std=c++17")
        .flag("-O3")
        .warnings(true)
        .compile("xark_custom_g1_msm");
}
