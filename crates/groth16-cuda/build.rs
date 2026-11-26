//! With the `cuda` feature, compiles the kernels with nvcc (cc-rs finds it
//! through `NVCC` or `CUDA_PATH`, else on `PATH`). `NVCC_APPEND_FLAGS` reaches
//! nvcc as usual, e.g. `-arch=sm_89` for the GPU it will run on.

fn main() {
    println!("cargo:rerun-if-changed=kernels");
    if std::env::var_os("CARGO_FEATURE_CUDA").is_none() {
        return;
    }
    cc::Build::new()
        .cuda(true)
        .cudart("shared")
        .file("kernels/msm_sorted.cu")
        .file("kernels/fft.cu")
        .flag("-std=c++17")
        .flag("-O3")
        .warnings(true)
        .compile("xark_groth16_cuda");
}
