//! Rust functions a generated client calls: `#[input]` on an `impl` block
//! makes its methods (constructors such as `Policy::default`, helpers such as
//! `Identity::commitment`) callable from a client, running this same code.
//!
//! `xark client` builds the circuit crate's host code a second time, as a plain wasm
//! module (`--cfg xark_client`, no JS glue), and generates typed wrappers that call
//! it. Values cross as JSON in their natural forms (a date as `"YYYY-MM-DD"`, a
//! country as `"US"`), converted here with the same codec as circuit inputs
//! ([`from_json`], [`to_json`]), so any [`Input`] type can be a parameter or result.
//!
//! The wasm ABI (client builds only): `xark_alloc(len) -> ptr`, `xark_free(ptr, len)`,
//! and per exported method `"<Type>.<method>"(ptr, len) -> u64`, taking the arguments
//! as a JSON array and returning `ptr << 32 | len` of `{"ok": value}` or
//! `{"err": message}`. A panic traps; `xark_panic()` then returns its message the
//! same way.

use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use serde_json::{Value, json};

use crate::input::{Input, Type, from_fields, leaf_names, schema_json, write_fields};
use crate::lang::Field;
pub use xark_schema::InputError;

/// The one-input schema describing a `ty` value named `v`.
fn schema(ty: Type) -> Result<xark_schema::Schema, InputError> {
    xark_schema::Schema::parse(&schema_json("value", &[("v", true, ty)])).map_err(InputError::from)
}

/// A `T` from its natural JSON form, as a client gives it (and as `--inputs` takes
/// a circuit input of that type). An error's `path` is inside the value (`document`;
/// empty for the value itself).
pub fn from_json<T: Input>(value: &Value) -> Result<T, InputError> {
    let leaves = schema(T::TYPE)?
        .leaves(&json!({ "v": value }))
        .map_err(|e| InputError {
            // Paths are under the one input `v`: name what's inside the value.
            path: e
                .path
                .strip_prefix('v')
                .unwrap_or(&e.path)
                .trim_start_matches('.')
                .to_string(),
            message: e.message,
        })?;
    let fields: Vec<Field> = leaf_names(&T::TYPE, "v")
        .iter()
        .map(|n| {
            leaves
                .get(n)
                .copied()
                .map(Field::from)
                .ok_or_else(|| InputError::from(format!("missing `{n}`")))
        })
        .collect::<Result<_, _>>()?;
    Ok(from_fields(&fields))
}

/// `value` in its natural JSON form, as a client reads it back (struct fields
/// `camelCase`, as generated clients name them; [`from_json`] takes either case).
pub fn to_json<T: Input>(value: &T) -> Result<Value, String> {
    let mut fields = alloc::vec![Field::zero(); T::LEN];
    write_fields(value, &mut fields);
    let frs: Vec<ark_bn254::Fr> = fields.into_iter().map(Into::into).collect();
    let mut out = schema(T::TYPE)
        .map_err(|e| e.to_string())?
        .decode_public(&frs, true)?;
    Ok(out["v"].take())
}

/// Argument `i` of an exported call, named `name` (as the client names it), as a
/// `T`. An error's `path` starts with that name (`policy.today`).
#[doc(hidden)]
pub fn arg<T: Input>(args: &[Value], i: usize, name: &str) -> Result<T, InputError> {
    let v = args
        .get(i)
        .ok_or_else(|| format!("expected at least {} arguments, got {}", i + 1, args.len()))?;
    from_json(v).map_err(|e| {
        let e = e.camel_case();
        let name = xark_schema::camel(name);
        InputError {
            path: if e.path.is_empty() {
                name
            } else {
                alloc::format!("{name}.{}", e.path)
            },
            message: e.message,
        }
    })
}

#[cfg(xark_client)]
pub use abi::call;

#[cfg(xark_client)]
mod abi {
    extern crate std;

    use alloc::string::{String, ToString};
    use alloc::vec::Vec;
    use std::sync::{Mutex, Once};

    use serde_json::{Value, json};

    use super::InputError;

    static PANIC: Mutex<Option<String>> = Mutex::new(None);
    static HOOK: Once = Once::new();

    /// `bytes`, leaked, as `ptr << 32 | len` for the host to read and `xark_free`.
    fn hand_over(bytes: Vec<u8>) -> u64 {
        let bytes = bytes.into_boxed_slice();
        let len = bytes.len();
        let ptr = alloc::boxed::Box::into_raw(bytes) as *mut u8 as usize;
        (ptr as u64) << 32 | len as u64
    }

    #[unsafe(no_mangle)]
    pub extern "C" fn xark_alloc(len: usize) -> *mut u8 {
        alloc::boxed::Box::into_raw(alloc::vec![0u8; len].into_boxed_slice()) as *mut u8
    }

    /// # Safety
    /// `ptr` and `len` are a buffer from `xark_alloc` or a call's result.
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn xark_free(ptr: *mut u8, len: usize) {
        drop(unsafe { alloc::boxed::Box::from_raw(core::ptr::slice_from_raw_parts_mut(ptr, len)) });
    }

    /// The last panic's message (after a call trapped).
    #[unsafe(no_mangle)]
    pub extern "C" fn xark_panic() -> u64 {
        let msg = PANIC
            .lock()
            .ok()
            .and_then(|mut p| p.take())
            .unwrap_or_default();
        hand_over(msg.into_bytes())
    }

    /// Run an exported method: decode the JSON argument array at `ptr`, call `f`,
    /// and hand back `{"ok": result}`, or `{"err": message, "path": input}` (no
    /// `path` for an error that isn't about one argument).
    #[doc(hidden)]
    pub fn call(
        ptr: *const u8,
        len: usize,
        f: impl FnOnce(&[Value]) -> Result<Value, InputError>,
    ) -> u64 {
        HOOK.call_once(|| {
            std::panic::set_hook(alloc::boxed::Box::new(|info| {
                // Not `payload_as_str`: only stable from 1.91, and 1.89 is supported.
                let payload = info.payload();
                let msg = payload
                    .downcast_ref::<&str>()
                    .map(|s| s.to_string())
                    .or_else(|| payload.downcast_ref::<String>().cloned())
                    .unwrap_or_else(|| "panic".into());
                if let Ok(mut p) = PANIC.lock() {
                    *p = Some(msg);
                }
            }))
        });
        // SAFETY: the host wrote `len` bytes at `ptr` (from `xark_alloc`).
        let input = unsafe { core::slice::from_raw_parts(ptr, len) };
        let out = match serde_json::from_slice::<Vec<Value>>(input) {
            Ok(args) => match f(&args) {
                Ok(v) => json!({ "ok": v }),
                Err(e) if e.path.is_empty() => json!({ "err": e.message }),
                Err(e) => json!({ "err": e.to_string(), "path": e.path }),
            },
            Err(e) => json!({ "err": alloc::format!("arguments: {e}") }),
        };
        hand_over(serde_json::to_vec(&out).unwrap_or_default())
    }
}

#[cfg(all(test, not(xark)))]
mod tests {
    use super::*;
    use crate::{Bitfield, Country, Date};

    #[test]
    fn values_round_trip_through_json() {
        let d: Date = from_json(&json!("2026-10-20")).unwrap();
        assert_eq!(to_json(&d).unwrap(), json!("2026-10-20"));
        let set: Bitfield<Country> = from_json(&json!(["US", "GB"])).unwrap();
        assert_eq!(to_json(&set).unwrap(), json!(["GB", "US"]));
        let pair: (u16, Field) = from_json(&json!([7, "9"])).unwrap();
        assert_eq!(to_json(&pair).unwrap(), json!([7, "9"]));
        assert!(from_json::<Date>(&json!("2023-02-29")).is_err());
        let e = arg::<u8>(&[json!(1)], 1, "years").unwrap_err();
        assert!(
            e.path.is_empty() && e.message.contains("at least 2 arguments"),
            "{e}"
        );
    }

    #[test]
    fn argument_errors_name_the_argument() {
        // A path from the argument's (camelCase) name into the value.
        let e = arg::<Bitfield<Country>>(&[json!(["XX"])], 0, "allowed").unwrap_err();
        assert_eq!(e.path, "allowed");
        assert!(e.message.contains("\"XX\" is not a Country"), "{e}");
        let e = arg::<(u16, Date)>(&[json!([7, "2023-02-29"])], 0, "born_by").unwrap_err();
        assert_eq!(e.path, "bornBy.1");
        assert!(e.message.contains("not a calendar day"), "{e}");
    }
}
