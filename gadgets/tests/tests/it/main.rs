//! The CLI and prover end-to-end tests, one binary: each file a module, so the
//! suite links once rather than once per file (23 binaries were 40% of the
//! workspace's test build). `sbpf.rs` and `differential_alt_bn128.rs` stay their
//! own binaries: `#[svm_test]` builds them for SBF (solana-ci.yml).

mod batch;
mod cache;
mod ceremony_cli;
mod cli_errors;
mod client_functions;
mod common;
mod end_to_end;
mod export;
mod fuzz;
mod host;
mod init;
mod keyed_rows;
mod minimize_analysis;
mod multi_function;
mod ptau;
mod regen_fixtures;
mod rust_prove;
mod serialization;
mod solana_format;
mod stale_builds;
mod xark_ir_e2e;
