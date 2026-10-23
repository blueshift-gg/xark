//! The circuit build for the stable frontend (`--cfg xark`, `wasm32`): every circuit
//! operation is a call to an `xark.*` wasm import, which the compiler implements as
//! the constraint builder while it runs the module. The imports are opaque to
//! `rustc`/LLVM, so optimization can't drop, duplicate or reorder them, and every
//! witness value only ever exists inside them.
//!
//! The ABI (pointers are wasm `i32`s; a `Field` is 4 `u64` limbs passed by pointer)
//! must match `xark-frontend`'s `host.rs`.

use core::mem::MaybeUninit;

use crate::lang::Field;

mod ffi {
    use crate::lang::Field;

    #[cfg_attr(target_arch = "wasm32", link(wasm_import_module = "xark"))]
    unsafe extern "C" {
        #[cfg_attr(target_arch = "wasm32", link_name = "add")]
        pub fn xark_add(out: *mut Field, a: *const Field, b: *const Field);
        #[cfg_attr(target_arch = "wasm32", link_name = "sub")]
        pub fn xark_sub(out: *mut Field, a: *const Field, b: *const Field);
        #[cfg_attr(target_arch = "wasm32", link_name = "mul")]
        pub fn xark_mul(out: *mut Field, a: *const Field, b: *const Field);
        #[cfg_attr(target_arch = "wasm32", link_name = "neg")]
        pub fn xark_neg(out: *mut Field, a: *const Field);
        #[cfg_attr(target_arch = "wasm32", link_name = "pow")]
        pub fn xark_pow(out: *mut Field, a: *const Field, exp: u64);
        #[cfg_attr(target_arch = "wasm32", link_name = "xor")]
        pub fn xark_xor(out: *mut Field, a: *const Field, b: *const Field);
        #[cfg_attr(target_arch = "wasm32", link_name = "or")]
        pub fn xark_or(out: *mut Field, a: *const Field, b: *const Field);
        #[cfg_attr(target_arch = "wasm32", link_name = "eq")]
        pub fn xark_eq(a: *const Field, b: *const Field) -> bool;
        #[cfg_attr(target_arch = "wasm32", link_name = "ult")]
        pub fn xark_ult(a: *const Field, b: *const Field, n: u32) -> bool;
        #[cfg_attr(target_arch = "wasm32", link_name = "bool_to_field")]
        pub fn xark_bool_to_field(out: *mut Field, b: bool);
        #[cfg_attr(target_arch = "wasm32", link_name = "advice")]
        pub fn xark_advice(out: *mut Field);
        #[cfg_attr(target_arch = "wasm32", link_name = "hint_inverse")]
        pub fn xark_hint_inverse(out: *mut Field, x: *const Field);
        #[cfg_attr(target_arch = "wasm32", link_name = "hint_inverse_or_zero")]
        pub fn xark_hint_inverse_or_zero(out: *mut Field, x: *const Field);
        #[cfg_attr(target_arch = "wasm32", link_name = "hint_bit")]
        pub fn xark_hint_bit(out: *mut Field, x: *const Field, index: u32);
        #[cfg_attr(target_arch = "wasm32", link_name = "hint_div_rem")]
        pub fn xark_hint_div_rem(out: *mut Field, a: *const Field, b: *const Field);
        #[cfg_attr(target_arch = "wasm32", link_name = "hint_mulmod_divmod")]
        pub fn xark_hint_mulmod_divmod(
            q: *mut Field,
            r: *mut Field,
            a: *const Field,
            b: *const Field,
            m: *const Field,
            n: u32,
            bits: u32,
        );
        #[cfg_attr(target_arch = "wasm32", link_name = "hint_mod_inverse")]
        pub fn xark_hint_mod_inverse(
            out: *mut Field,
            a: *const Field,
            m: *const Field,
            n: u32,
            bits: u32,
        );
        #[cfg_attr(target_arch = "wasm32", link_name = "hint_sub2")]
        pub fn xark_hint_sub2(
            qabs: *mut Field,
            r: *mut Field,
            a: *const Field,
            b: *const Field,
            c: *const Field,
            m: *const Field,
            n: u32,
            bits: u32,
        );
        #[cfg_attr(target_arch = "wasm32", link_name = "require_eq")]
        pub fn xark_require_eq(a: *const Field, b: *const Field);
        #[cfg_attr(target_arch = "wasm32", link_name = "witness_begin")]
        pub fn xark_witness_begin();
        #[cfg_attr(target_arch = "wasm32", link_name = "witness_end")]
        pub fn xark_witness_end();
        #[cfg_attr(target_arch = "wasm32", link_name = "to_bits_lookup")]
        pub fn xark_to_bits_lookup(x: *const Field, n: u32, out: *mut Field) -> bool;
        #[cfg_attr(target_arch = "wasm32", link_name = "to_bits_record")]
        pub fn xark_to_bits_record(x: *const Field, n: u32, bits: *const Field);
        #[cfg_attr(target_arch = "wasm32", link_name = "input_field")]
        pub fn xark_input_field(out: *mut Field, name: *const u8, len: usize, vis: u32);
        #[cfg_attr(target_arch = "wasm32", link_name = "input_uint")]
        pub fn xark_input_uint(name: *const u8, len: usize, vis: u32, width: u32) -> u64;
        #[cfg_attr(target_arch = "wasm32", link_name = "input_schema")]
        pub fn xark_input_schema(json: *const u8, len: usize);
        #[cfg_attr(target_arch = "wasm32", link_name = "input_bool")]
        pub fn xark_input_bool(name: *const u8, len: usize, vis: u32) -> bool;
        #[cfg_attr(target_arch = "wasm32", link_name = "input_uint_hi")]
        pub fn xark_input_uint_hi() -> u64;
        #[cfg_attr(target_arch = "wasm32", link_name = "inputs_done")]
        pub fn xark_inputs_done();
        #[cfg_attr(target_arch = "wasm32", link_name = "panic")]
        pub fn xark_panic(
            msg: *const u8,
            len: usize,
            file: *const u8,
            file_len: usize,
            line: u32,
            col: u32,
        );
    }
}

#[inline(always)]
fn out1(f: impl FnOnce(*mut Field)) -> Field {
    let mut o = MaybeUninit::<Field>::uninit();
    f(o.as_mut_ptr());
    // SAFETY: the host writes the whole `Field` before returning.
    unsafe { o.assume_init() }
}

#[inline(always)]
fn out_n<const N: usize>(f: impl FnOnce(*mut Field)) -> [Field; N] {
    let mut o = MaybeUninit::<[Field; N]>::uninit();
    f(o.as_mut_ptr().cast());
    // SAFETY: the host writes all `N` fields before returning.
    unsafe { o.assume_init() }
}

pub(crate) fn add(a: Field, b: Field) -> Field {
    out1(|o| unsafe { ffi::xark_add(o, &a, &b) })
}
pub(crate) fn sub(a: Field, b: Field) -> Field {
    out1(|o| unsafe { ffi::xark_sub(o, &a, &b) })
}
pub(crate) fn mul(a: Field, b: Field) -> Field {
    out1(|o| unsafe { ffi::xark_mul(o, &a, &b) })
}
pub(crate) fn neg(a: Field) -> Field {
    out1(|o| unsafe { ffi::xark_neg(o, &a) })
}
pub(crate) fn pow_u64(a: Field, exp: u64) -> Field {
    out1(|o| unsafe { ffi::xark_pow(o, &a, exp) })
}
pub(crate) fn xor(a: Field, b: Field) -> Field {
    out1(|o| unsafe { ffi::xark_xor(o, &a, &b) })
}
pub(crate) fn or(a: Field, b: Field) -> Field {
    out1(|o| unsafe { ffi::xark_or(o, &a, &b) })
}
pub(crate) fn eq(a: Field, b: Field) -> bool {
    unsafe { ffi::xark_eq(&a, &b) }
}
pub(crate) fn ult<const N: usize>(a: Field, b: Field) -> bool {
    unsafe { ffi::xark_ult(&a, &b, N as u32) }
}
pub(crate) fn bool_to_field(b: bool) -> Field {
    out1(|o| unsafe { ffi::xark_bool_to_field(o, b) })
}
pub(crate) fn advice() -> Field {
    out1(|o| unsafe { ffi::xark_advice(o) })
}
pub(crate) fn hint_inverse(x: Field) -> Field {
    out1(|o| unsafe { ffi::xark_hint_inverse(o, &x) })
}
pub(crate) fn hint_inverse_or_zero(x: Field) -> Field {
    out1(|o| unsafe { ffi::xark_hint_inverse_or_zero(o, &x) })
}
pub(crate) fn hint_bit(x: Field, index: usize) -> Field {
    out1(|o| unsafe { ffi::xark_hint_bit(o, &x, index as u32) })
}
pub(crate) fn hint_div_rem(a: Field, b: Field) -> [Field; 2] {
    out_n(|o| unsafe { ffi::xark_hint_div_rem(o, &a, &b) })
}
pub(crate) fn hint_mulmod_divmod<const N: usize>(
    a: [Field; N],
    b: [Field; N],
    m: [Field; N],
    bits: usize,
) -> ([Field; N], [Field; N]) {
    let mut q = MaybeUninit::<[Field; N]>::uninit();
    let mut r = MaybeUninit::<[Field; N]>::uninit();
    unsafe {
        ffi::xark_hint_mulmod_divmod(
            q.as_mut_ptr().cast(),
            r.as_mut_ptr().cast(),
            a.as_ptr(),
            b.as_ptr(),
            m.as_ptr(),
            N as u32,
            bits as u32,
        );
        (q.assume_init(), r.assume_init())
    }
}
pub(crate) fn hint_mod_inverse<const N: usize>(
    a: [Field; N],
    m: [Field; N],
    bits: usize,
) -> [Field; N] {
    out_n(|o| unsafe {
        ffi::xark_hint_mod_inverse(o, a.as_ptr(), m.as_ptr(), N as u32, bits as u32)
    })
}
pub(crate) fn hint_sub2<const N: usize>(
    a: [Field; N],
    b: [Field; N],
    c: [Field; N],
    m: [Field; N],
    bits: usize,
) -> (Field, [Field; N]) {
    let mut q = MaybeUninit::<Field>::uninit();
    let mut r = MaybeUninit::<[Field; N]>::uninit();
    unsafe {
        ffi::xark_hint_sub2(
            q.as_mut_ptr(),
            r.as_mut_ptr().cast(),
            a.as_ptr(),
            b.as_ptr(),
            c.as_ptr(),
            m.as_ptr(),
            N as u32,
            bits as u32,
        );
        (q.assume_init(), r.assume_init())
    }
}
pub(crate) fn require_eq(a: Field, b: Field) {
    unsafe { ffi::xark_require_eq(&a, &b) }
}
pub(crate) fn witness_begin() {
    unsafe { ffi::xark_witness_begin() }
}
pub(crate) fn witness_end() {
    unsafe { ffi::xark_witness_end() }
}

/// `to_bits::<N>` memo: `Some(bits)` when `x`'s bits are already known (a constant,
/// a sum of proven bits, or an earlier decomposition), else `None` and the caller
/// decomposes and then calls [`to_bits_record`].
pub(crate) fn to_bits_lookup<const N: usize>(x: &Field) -> Option<[Field; N]> {
    let mut o = MaybeUninit::<[Field; N]>::uninit();
    // SAFETY: on `true` the host wrote all `N` fields.
    unsafe { ffi::xark_to_bits_lookup(x, N as u32, o.as_mut_ptr().cast()).then(|| o.assume_init()) }
}
pub(crate) fn to_bits_record<const N: usize>(x: &Field, bits: &[Field; N]) {
    unsafe { ffi::xark_to_bits_record(x, N as u32, bits.as_ptr()) }
}

/// [`to_bits_lookup`] for a width known as a value: on a hit, fills `out[..n]`.
pub(crate) fn to_bits_lookup_n(x: &Field, n: usize, out: &mut [Field; 253]) -> bool {
    // SAFETY: on `true` the host wrote `n ≤ 253` fields to `out`.
    unsafe { ffi::xark_to_bits_lookup(x, n as u32, out.as_mut_ptr()) }
}
pub(crate) fn to_bits_record_n(x: &Field, n: usize, bits: &[Field; 253]) {
    unsafe { ffi::xark_to_bits_record(x, n as u32, bits.as_ptr()) }
}

// --- inputs ------------------------------------------------------------------

/// Bind the input leaf `name` (a field element). See [`crate::input::bind`].
pub(crate) fn bind_field(name: &str, public: bool) -> Field {
    out1(|o| unsafe { ffi::xark_input_field(o, name.as_ptr(), name.len(), public as u32) })
}

/// Bind the input leaf `name` as a `bits`-bit unsigned integer (`bits ≤ 64`).
pub(crate) fn bind_uint(name: &str, public: bool, bits: u32) -> u64 {
    unsafe { ffi::xark_input_uint(name.as_ptr(), name.len(), public as u32, bits) }
}

/// Bind the input leaf `name` as a `bool` (a `{0, 1}` wire, range-checked once every
/// input is bound).
pub(crate) fn bind_bool(name: &str, public: bool) -> bool {
    unsafe { ffi::xark_input_bool(name.as_ptr(), name.len(), public as u32) }
}

/// Bind the input leaf `name` as a `u128`: two wasm registers, the low half first,
/// then the high half of the same input.
pub(crate) fn bind_u128(name: &str, public: bool) -> u128 {
    let lo = unsafe { ffi::xark_input_uint(name.as_ptr(), name.len(), public as u32, 128) };
    let hi = unsafe { ffi::xark_input_uint_hi() };
    (hi as u128) << 64 | lo as u128
}

/// Hand the compiler the circuit's `schema.json`.
pub(crate) fn record_schema(json: &str) {
    unsafe { ffi::xark_input_schema(json.as_ptr(), json.len()) }
}

/// All inputs are bound: the compiler range-checks the `uN` ones now.
pub(crate) fn inputs_done() {
    unsafe { ffi::xark_inputs_done() }
}

// --- runtime -----------------------------------------------------------------

/// Report panics to the compiler: the message and where, through the `panic`
/// import, which never returns (a panicking arm of a witness branch is ruled out,
/// so `assert!` on a witness value becomes a constraint, and a build that panics
/// names the line). A hook rather than a `#[panic_handler]`, so a circuit crate may
/// use `std`: installed by the `#[circuit]` entry before anything can panic.
#[cfg(target_arch = "wasm32")]
pub(crate) fn install_panic_hook() {
    extern crate std;
    std::panic::set_hook(alloc::boxed::Box::new(|info| {
        // `payload_as_str` is only stable from 1.91; the oldest supported rustc is 1.89.
        let payload = info.payload();
        let msg = payload
            .downcast_ref::<&str>()
            .copied()
            .or_else(|| {
                payload
                    .downcast_ref::<alloc::string::String>()
                    .map(|s| s.as_str())
            })
            .unwrap_or("panic");
        let (file, line, col) = info
            .location()
            .map(|l| (l.file(), l.line(), l.column()))
            .unwrap_or(("", 0, 0));
        unsafe {
            ffi::xark_panic(
                msg.as_ptr(),
                msg.len(),
                file.as_ptr(),
                file.len(),
                line,
                col,
            );
        }
    }));
}

/// A bump allocator over wasm linear memory (a circuit build is one short run).
#[cfg(target_arch = "wasm32")]
struct Bump;

#[cfg(target_arch = "wasm32")]
static mut NEXT: usize = 0;
#[cfg(target_arch = "wasm32")]
static mut END: usize = 0;

#[cfg(target_arch = "wasm32")]
unsafe impl core::alloc::GlobalAlloc for Bump {
    unsafe fn alloc(&self, layout: core::alloc::Layout) -> *mut u8 {
        unsafe {
            let start = (NEXT + layout.align() - 1) & !(layout.align() - 1);
            let end = start + layout.size();
            if NEXT == 0 || end > END {
                let pages = layout.size().div_ceil(65536) + 1;
                let base = core::arch::wasm32::memory_grow(0, pages);
                if base == usize::MAX {
                    return core::ptr::null_mut();
                }
                NEXT = base * 65536;
                END = NEXT + pages * 65536;
                return self.alloc(layout);
            }
            NEXT = end;
            start as *mut u8
        }
    }
    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: core::alloc::Layout) {}
}

#[cfg(target_arch = "wasm32")]
#[global_allocator]
static ALLOC: Bump = Bump;
