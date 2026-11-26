//! Device buffers kept from call to call, one per role.
//!
//! On unified memory (Apple silicon) the GPU's buffers are the host's pages,
//! and a new allocation's pages fault in on first touch: filling 32 MB took
//! 5–7 ms in a fresh `CL_MEM_ALLOC_HOST_PTR` buffer and 0.6 ms in one already
//! touched (an M3 Max), while a copy into a device buffer took 3.4–4.4 ms. An
//! H MSM of 2^19 points allocates about 150 MB across its stages. So each
//! stage leases its buffer by role: a lease reuses the kept buffer when it is
//! big enough, and gives it back when dropped. [`OpenClMsm::prepare`] leases
//! every role at the coming proof's size once, beside the witness solve, so
//! the proof's own leases find their pages in place.
//!
//! [`OpenClMsm::prepare`]: crate::OpenClMsm

use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::ops::{Deref, DerefMut};
use std::sync::Mutex;

use opencl3::context::Context;
use opencl3::memory::Buffer;

struct Kept<T> {
    buf: Buffer<T>,
    cap: usize,
}

/// The kept buffers by role and element type, each a `Kept<T>`.
type Free = HashMap<(&'static str, TypeId), Box<dyn Any + Send>>;

#[derive(Default)]
pub(crate) struct Pool {
    free: Mutex<Free>,
}

impl Pool {
    /// A buffer of at least `len` elements for `role`, allocated with `flags`
    /// if none is kept or the kept one is too small. A role always asks with
    /// the same flags.
    pub(crate) fn lease<T: Send + 'static>(
        &self,
        context: &Context,
        role: &'static str,
        flags: u64,
        len: usize,
    ) -> Option<Lease<'_, T>> {
        let len = len.max(1);
        let kept = self
            .free
            .lock()
            .ok()?
            .remove(&(role, TypeId::of::<T>()))
            .and_then(|b| b.downcast::<Kept<T>>().ok())
            .filter(|k| k.cap >= len);
        let kept = match kept {
            Some(k) => *k,
            None => Kept {
                // SAFETY: a null host pointer asks the runtime to allocate.
                buf: unsafe { Buffer::<T>::create(context, flags, len, std::ptr::null_mut()) }
                    .ok()?,
                cap: len,
            },
        };
        Some(Lease {
            pool: self,
            role,
            kept: Some(kept),
        })
    }
}

/// A leased buffer; dropping it gives it back to the pool (the larger of it
/// and any other kept for the role stays).
pub(crate) struct Lease<'a, T: Send + 'static> {
    pool: &'a Pool,
    role: &'static str,
    kept: Option<Kept<T>>,
}

impl<T: Send + 'static> Deref for Lease<'_, T> {
    type Target = Buffer<T>;
    fn deref(&self) -> &Buffer<T> {
        &self.kept.as_ref().expect("held until dropped").buf
    }
}

impl<T: Send + 'static> DerefMut for Lease<'_, T> {
    fn deref_mut(&mut self) -> &mut Buffer<T> {
        &mut self.kept.as_mut().expect("held until dropped").buf
    }
}

impl<T: Send + 'static> Drop for Lease<'_, T> {
    fn drop(&mut self) {
        let Some(kept) = self.kept.take() else { return };
        let Ok(mut free) = self.pool.free.lock() else {
            return;
        };
        let key = (self.role, TypeId::of::<T>());
        let keep = match free.get(&key).and_then(|b| b.downcast_ref::<Kept<T>>()) {
            Some(other) => other.cap < kept.cap,
            None => true,
        };
        if keep {
            free.insert(key, Box::new(kept));
        }
    }
}
