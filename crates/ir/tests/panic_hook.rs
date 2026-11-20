//! Decoding a malformed `circuit.xbc` keeps its own panics quiet without touching
//! the host's panic hook, however many decodes overlap (#68). Its own test binary:
//! the host hook has to be the process's first, installed before any decode.

use std::sync::atomic::{AtomicUsize, Ordering};
use xark_ir::function_decode::{
    ReducedRowStream, expand_function_blob, expand_function_blob_reduced,
};

static HOST_CALLS: AtomicUsize = AtomicUsize::new(0);

#[test]
fn concurrent_decodes_leave_the_host_hook_installed() {
    std::panic::set_hook(Box::new(|_| {
        HOST_CALLS.fetch_add(1, Ordering::SeqCst);
    }));
    // Past the magic and version, a name length that overruns the buffer: every
    // decode panics inside the parser and returns `Err`.
    let mut bad = xark_ir::bytecode::MAGIC.to_vec();
    bad.extend_from_slice(&2u16.to_le_bytes());
    bad.push(0x7f);

    let threads = 8;
    let barrier = std::sync::Barrier::new(threads);
    std::thread::scope(|s| {
        for _ in 0..threads {
            s.spawn(|| {
                barrier.wait();
                for _ in 0..200 {
                    assert!(expand_function_blob(&bad).is_err());
                    assert!(expand_function_blob_reduced(&bad).is_err());
                    assert!(ReducedRowStream::new(&bad).is_err());
                }
            });
        }
    });
    // The decodes' own panics never reached the host hook ...
    assert_eq!(HOST_CALLS.load(Ordering::SeqCst), 0);
    // ... and a panic of the host's own still does.
    let _ = std::panic::catch_unwind(|| panic!("the host's own panic"));
    assert_eq!(HOST_CALLS.load(Ordering::SeqCst), 1);
}
