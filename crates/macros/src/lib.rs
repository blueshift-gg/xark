//! `#[circuit]` — declare a circuit entry — and `#[input]` — make a type a circuit
//! input, or an `impl` block's methods client functions.
//!
//! ```ignore
//! #[circuit]
//! pub fn sha256(msg: Private<[u8; 3]>, digest: Public<Hash>) {
//!     require_eq(xark_sha256::sha256(msg), digest);
//! }
//! ```
//!
//! Every parameter type implements `xark::Input`, which says how its value maps to
//! field elements and how clients see it. `#[circuit]`: (1) binds each parameter
//! through it in the circuit build (`[u8; N]` enters as real bytes, range-checked by
//! the compiler, and the body sees `[Field; N]`), emitting the body verbatim; (2)
//! generates a typed `<Fn>Inputs` struct, named so parameters can't be transposed;
//! (3) implements `ProveInputs` for it from the same impls; (4) generates
//! `<Fn>Inputs::schema()`, the circuit's `schema.json`.
//!
//! `#[input]` — see [`input`] — implements `xark::Input` for a struct (its fields in
//! order) and `xark::Enum` for a fieldless enum, and on an `impl` block makes its
//! methods callable from generated clients.

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use syn::ext::IdentExt;
use syn::{
    Attribute, Data, DataEnum, DataStruct, DeriveInput, Expr, ExprLit, FnArg, GenericArgument,
    ImplItem, ItemFn, ItemImpl, Lit, LitInt, LitStr, Pat, PathArguments, ReturnType, Type,
    TypeImplTrait, TypeParamBound, parse_macro_input,
};

#[proc_macro_attribute]
pub fn circuit(attr: TokenStream, item: TokenStream) -> TokenStream {
    // Rejected, not ignored: an option like `max_constraints = …` would
    // otherwise compile and look enforced.
    if !attr.is_empty() {
        let attr = TokenStream2::from(attr);
        return syn::Error::new_spanned(attr, "`#[circuit]` takes no arguments")
            .to_compile_error()
            .into();
    }
    let func = parse_macro_input!(item as ItemFn);
    match circuit_impl(&func) {
        Ok(ts) => ts.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

/// How the host-side validator takes a parameter.
enum HostArg {
    /// `impl Into<T>`: a `Field` from an integer or string, a gadget type from its
    /// natural form, a `Date` from `"YYYY-MM-DD"`.
    Into,
    /// `[impl Into<Elem>; N]`: an array of such.
    IntoArray(usize),
    /// Exactly the type: native integers and byte arrays, so untyped literals infer.
    Exact,
    /// `[u8; N]`, exactly; the circuit body sees it as `[Field; N]`.
    Bytes(usize),
}

/// One resolved entry parameter.
struct CircuitParam {
    /// Struct field name *and* leaf-name root.
    name: syn::Ident,
    /// `Private` / `Public`, as the author wrote it.
    wrapper: syn::Ident,
    /// The parameter's type, as written (an `xark::Input`).
    ty: Type,
    host: HostArg,
}

/// Rewrite a `#[circuit]` entry: bind every parameter through its `Input` impl in
/// the circuit build, and emit a typed `<Fn>Inputs` struct whose `ProveInputs`
/// writes each parameter's leaves for the prover.
fn circuit_impl(func: &ItemFn) -> syn::Result<TokenStream2> {
    let params = func
        .sig
        .inputs
        .iter()
        .map(resolve_param)
        .collect::<syn::Result<Vec<_>>>()?;

    let attrs = &func.attrs;
    let vis = &func.vis;
    let fn_ident = &func.sig.ident;
    let stmts = &func.block.stmts;
    let sig_params: Vec<TokenStream2> = params
        .iter()
        .map(|p| {
            let (name, wrapper, ty) = (&p.name, &p.wrapper, &p.ty);
            quote! { #name: #wrapper<#ty> }
        })
        .collect();
    // The real `Field` circuit body (the one `__xark_main` binds the inputs for and
    // calls), emitted under a hidden name so it is **never cfg-gated** — it compiles in
    // every build; `cargo`/host builds just carry it as present-but-unused code, which also
    // keeps the circuit's `use`s live (no separate `__circuit_def` shim needed).
    //
    // Keeping it un-gated is what stops rust-analyzer greying the body you wrote: every
    // item the macro emits at the `#[circuit]` span is active under the editor's cfg, so
    // none of them mark the span inactive. The user's `fn` name is reused below for the
    // native-typed validator, which is what host/test code calls — no collision, since
    // the entry carries a distinct hidden name.
    let entry_ident = format_ident!("__{}_entry", fn_ident);
    // A `[u8; N]` parameter enters the circuit as real `u8`s, so the compiler range-checks
    // each byte on entry and records the true type in `schema.json`; the body then sees
    // it as `[Field; N]` (what the byte gadgets take). The conversion is free, and a
    // gadget's own `to_bits::<8>` of a byte hits the bit cache the entry check filled.
    let byte_convs = params.iter().filter_map(|p| match p.host {
        HostArg::Bytes(n) => {
            let name = &p.name;
            Some(quote! {
                let #name: [::xark::Field; #n] = ::xark::bytes_to_fields(#name);
            })
        }
        _ => None,
    });
    let entry = quote! {
        #[doc(hidden)]
        #(#attrs)*
        #vis fn #entry_ident(#(#sig_params),*) {
            #(#byte_convs)*
            #(#stmts)*
        }
    };

    let fn_name_lit = LitStr::new(&fn_ident.unraw().to_string(), fn_ident.span());
    // `(name, public, TYPE)` per parameter: the circuit's `schema.json`.
    let schema_params: Vec<TokenStream2> = params
        .iter()
        .map(|p| {
            let (ty, public) = (&p.ty, p.wrapper == "Public");
            let lit = LitStr::new(&p.name.unraw().to_string(), p.name.span());
            quote! { (#lit, #public, <#ty as ::xark::Input>::TYPE) }
        })
        .collect();

    // Stable-frontend entry (`--cfg xark` on `wasm32`): bind every input leaf through
    // the compiler's input import — in parameter order, each in its `Input` order —
    // then hand over the schema and run the body. The compiler executes this export.
    let wasm_binds = params.iter().enumerate().map(|(i, p)| {
        let (name, ty) = (&p.name, &p.ty);
        let public = p.wrapper == "Public";
        quote! {
            let #name: #ty = __binder.bind::<#i, #ty>(#public);
        }
    });
    let wasm_args = params.iter().map(|p| &p.name);
    let entry_name = fn_ident.unraw().to_string();
    let entry_len = entry_name.len();
    let entry_bytes = syn::LitByteStr::new(entry_name.as_bytes(), fn_ident.span());
    let wasm_main = quote! {
        // The circuit's name, for the compiler (a custom wasm section).
        #[cfg(all(xark, target_arch = "wasm32"))]
        #[unsafe(link_section = "xark.entry")]
        #[used]
        static __XARK_ENTRY: [u8; #entry_len] = *#entry_bytes;

        #[cfg(all(xark, target_arch = "wasm32"))]
        #[doc(hidden)]
        #[unsafe(no_mangle)]
        pub extern "C" fn __xark_main() {
            let __params = &[#(#schema_params),*];
            let mut __binder = ::xark::input::Binder::new(#fn_name_lit, __params);
            #(#wasm_binds)*
            __binder.inputs_done();
            #entry_ident(#(#wasm_args),*);
            __binder.finish(__params);
        }
    };

    let struct_name = format_ident!("{}Inputs", to_pascal(&fn_ident.unraw().to_string()));
    let field_defs = params.iter().map(|p| {
        let (name, ty) = (&p.name, &p.ty);
        quote! { pub #name: #ty }
    });
    let leaves = params.iter().map(|p| {
        let name = &p.name;
        let lit = LitStr::new(&name.unraw().to_string(), name.span());
        quote! { out.extend(::xark::input::leaves(&self.#name, #lit)); }
    });

    // The native-typed validator replacing the entry `fn` in test/host builds: same
    // name, the entry's parameter types in order, returning the check result.
    let host_generics: Vec<TokenStream2> = params
        .iter()
        .filter(|p| matches!(p.host, HostArg::IntoArray(_)))
        .map(|p| {
            let t = format_ident!("__T_{}", p.name);
            let arr = &p.ty;
            quote! { #t: ::core::convert::Into<<#arr as ::core::iter::IntoIterator>::Item> }
        })
        .collect();
    let host_params = params.iter().map(|p| {
        let (name, ty) = (&p.name, &p.ty);
        match p.host {
            HostArg::Into => quote! { #name: impl ::core::convert::Into<#ty> },
            HostArg::IntoArray(n) => {
                let t = format_ident!("__T_{}", name);
                quote! { #name: [#t; #n] }
            }
            HostArg::Exact | HostArg::Bytes(_) => quote! { #name: #ty },
        }
    });
    let host_ctor = params.iter().map(|p| {
        let name = &p.name;
        match p.host {
            HostArg::Into => quote! { #name: #name.into() },
            HostArg::IntoArray(_) => quote! { #name: #name.map(::core::convert::Into::into) },
            HostArg::Exact | HostArg::Bytes(_) => quote! { #name },
        }
    });

    Ok(quote! {
        #entry

        #wasm_main

        /// Native-typed validator for this circuit, carrying the name you gave the `#[circuit]`
        /// fn. In host/test builds this *is* `<fn>` (the real `Field` body lives under a hidden
        /// name): it takes the entry's native inputs, loads the built circuit from
        /// `target/xark/<package>/`, and returns `Ok(())` if they satisfy it. Dropped from the
        /// `xark` build, where the hidden entry is what gets compiled to a circuit.
        #[cfg(not(xark))]
        ::xark::__with_prover! {
            #(#attrs)*
            #[allow(non_camel_case_types)]
            #vis fn #fn_ident<#(#host_generics),*>(#(#host_params),*) -> ::core::result::Result<(), ::xark::prover::ProveError> {
                // Where `xark build` writes it: `target/xark/<package name>/` (the
                // package's name, which can differ from the fn's: `my-circuit`).
                ::xark::prover::circuit(::core::env!("CARGO_PKG_NAME")).check(#struct_name { #(#host_ctor),* })
            }
        }

        /// Typed inputs for this circuit (generated by `#[circuit]`), one field per
        /// entry parameter. For a custom artifact location:
        /// `xark::prover::circuit_at(dir).check(<Fn>Inputs { .. })` — or `.prove(..)`.
        #[cfg(not(xark))]
        #[derive(Clone, Debug)]
        pub struct #struct_name {
            #(#field_defs,)*
        }

        #[cfg(not(xark))]
        ::xark::__with_prover! {
            impl ::xark::prover::ProveInputs for #struct_name {
                fn into_inputs(self) -> ::std::vec::Vec<(::std::string::String, ::xark::prover::Fr)> {
                    let mut out: ::std::vec::Vec<(::std::string::String, ::xark::prover::Fr)> =
                        ::std::vec::Vec::new();
                    #(#leaves)*
                    out
                }
            }
        }

        #[cfg(not(xark))]
        impl #struct_name {
            /// This circuit's `schema.json`, the same document `xark build` writes: its
            /// inputs in declaration order, every named type they reach, and the public
            /// leaves in proof order. See `xark::input::schema_json`.
            pub fn schema() -> ::std::string::String {
                ::xark::input::schema_json(#fn_name_lit, &[#(#schema_params),*])
            }
        }
    })
}

/// Resolve one entry parameter: a plain identifier wrapped in `Private<_>` /
/// `Public<_>`.
fn resolve_param(arg: &FnArg) -> syn::Result<CircuitParam> {
    let pt = match arg {
        FnArg::Typed(pt) => pt,
        FnArg::Receiver(r) => {
            return Err(syn::Error::new_spanned(
                r,
                "#[circuit] cannot take a `self` parameter",
            ));
        }
    };
    let name = match &*pt.pat {
        Pat::Ident(pi) => pi.ident.clone(),
        other => {
            return Err(syn::Error::new_spanned(
                other,
                "#[circuit] parameters must be plain identifiers (no `_`, no patterns)",
            ));
        }
    };
    let (wrapper, ty) = unwrap_visibility(&pt.ty)?;
    let host = host_arg(&ty)?;
    Ok(CircuitParam {
        name,
        wrapper,
        ty,
        host,
    })
}

/// Peel `Private<Inner>` / `Public<Inner>`, returning the wrapper ident and inner
/// type. A circuit input must declare visibility, so anything else is an error.
fn unwrap_visibility(ty: &Type) -> syn::Result<(syn::Ident, Type)> {
    if let Type::Path(tp) = ty
        && let Some(seg) = tp.path.segments.last()
        && (seg.ident == "Private" || seg.ident == "Public")
        && let PathArguments::AngleBracketed(ab) = &seg.arguments
        && let Some(GenericArgument::Type(inner)) = ab.args.first()
    {
        return Ok((seg.ident.clone(), inner.clone()));
    }
    let t = quote::quote!(#ty).to_string().replace(' ', "");
    Err(syn::Error::new_spanned(
        ty,
        format!(
            "unsupported circuit parameter type `{t}`: #[circuit] parameters must be \
             wrapped in `Private<..>` or `Public<..>`\n\
             help: declare its visibility, e.g. `Private<{t}>` (a witness) or \
             `Public<{t}>` (a public input)"
        ),
    ))
}

/// How the validator takes a parameter of type `ty`. Any `xark::Input` type is a
/// parameter; a type that isn't one is a compile error at its `Input` bound.
fn host_arg(ty: &Type) -> syn::Result<HostArg> {
    match ty {
        _ if uint_type_bits(ty).is_some() || is_ident(ty, "bool") => Ok(HostArg::Exact),
        Type::Array(arr) => {
            let n = eval_usize_lit(&arr.len)?;
            Ok(if is_ident(&arr.elem, "u8") {
                HostArg::Bytes(n)
            } else if uint_type_bits(&arr.elem).is_some() {
                HostArg::Exact
            } else {
                HostArg::IntoArray(n)
            })
        }
        Type::Path(_) => Ok(HostArg::Into),
        Type::Tuple(_) => Ok(HostArg::Exact),
        other => Err(syn::Error::new_spanned(
            other,
            "unsupported #[circuit] parameter type; a parameter is any `xark::Input` type: \
             `Field`, `u8`..`u128`, `bool`, `[T; N]`, a tuple, a struct with `#[input]`, a \
             standard type (`Date`, `Text`, `Choice<E>`, `Bitfield<E>`) or a gadget type",
        )),
    }
}

fn is_ident(ty: &Type, name: &str) -> bool {
    matches!(ty, Type::Path(tp) if tp.qself.is_none() && tp.path.is_ident(name))
}

/// Bit width of a native unsigned integer type name (`"u64"` → `64`).
fn uint_bits(ident: &str) -> Option<u32> {
    Some(match ident {
        "u8" => 8,
        "u16" => 16,
        "u32" => 32,
        "u64" => 64,
        "u128" => 128,
        _ => return None,
    })
}

/// Whether `ty` is a native unsigned integer, returning its width.
fn uint_type_bits(ty: &Type) -> Option<u32> {
    match ty {
        Type::Path(tp) if tp.qself.is_none() && tp.path.segments.len() == 1 => {
            uint_bits(&tp.path.segments[0].ident.to_string())
        }
        _ => None,
    }
}

/// `my_square` → `MySquare` (for the `<Name>Inputs` struct). Falls back to
/// `Circuit` for a degenerate all-separator name (e.g. `__`), so the struct is
/// never named just `Inputs`.
fn to_pascal(s: &str) -> String {
    let pascal: String = s
        .split('_')
        .filter(|seg| !seg.is_empty())
        .map(|seg| {
            let mut chars = seg.chars();
            match chars.next() {
                Some(first) => first.to_ascii_uppercase().to_string() + chars.as_str(),
                None => String::new(),
            }
        })
        .collect();
    if pascal.is_empty() {
        "Circuit".to_string()
    } else {
        pascal
    }
}

/// `#[input]` — make a type a circuit input, or an `impl` block's methods client
/// functions. One attribute, three places:
///
/// **On a struct** it implements `xark::Input`: its fields (each an `Input` type) in
/// declaration order, named `name.field`, given by clients as an object of its
/// fields. It also gets `to_fields()`, its field elements in that order (to hash it),
/// and `require_eq(a, b)` (every field element equal).
///
/// ```ignore
/// #[input]
/// pub struct Identity { pub born: Date, pub nationality: Choice<Country>, pub salt: Field }
/// ```
///
/// It derives `Clone`, `Copy` and `Debug` unless the type lists them already (an
/// enum also `PartialEq` and `Eq`); `#[input(no_derive)]` leaves them to you, for a
/// type with its own impl of one.
///
/// A struct can be given in a standard encoding instead, with host conversions to
/// match:
///
/// * `#[input(number(bits = B))]` on `{ limbs: [Field; N] }`: a whole number in
///   `N` little-endian `B`-bit limbs (a non-native field element). On the host it
///   comes from its big-endian bytes, a decimal or `0x`-hex string, or a `u128`.
/// * `#[input(bytes)]` on a struct of byte-encoded fields: their bytes back to back
///   (a point's `x ‖ y`), from a `[u8; N]` on the host.
///
/// **On a fieldless enum** it implements `xark::Enum`, so `Choice<E>` holds one
/// variant and `Bitfield<E>` a set of them. A variant's position is its value:
/// append, never reorder.
///
/// ```ignore
/// #[input]
/// pub enum Tier { Retail, Accredited, Institutional }
/// ```
///
/// **On an `impl` block** its `pub fn`s (every function, for a trait's impl) become
/// functions a generated client (`xark client`) calls, running this Rust code: write
/// a constructor or helper once.
///
/// ```ignore
/// #[input]
/// impl Default for Policy {
///     /// A policy every holder passes.
///     fn default() -> Policy { /* … */ }
/// }
///
/// #[input]
/// impl Policy {
///     /// Checked on `today`.
///     pub fn on(self, today: impl Into<Date>) -> Policy { /* … */ }
///     /// At least `years` old on `today`.
///     pub fn min_age(self, years: u16) -> Policy { /* … */ }
/// }
/// ```
///
/// TypeScript gets `Policy.default().on(new Date()).minAge(18)`, typed from the
/// signature, its docs from these comments. Each parameter and the result must be an
/// `xark::Input` type (`Field`, `uN`, `bool`, `Date`, a struct with `#[input]`, …;
/// `impl Into<T>` and `&T` take a `T`, and `Self` is the type); the receiver may be
/// `self` or `&self`. The block itself compiles as
/// written; a client build (`--cfg xark_client`) also gives each method a wasm export
/// taking and returning JSON (see `xark::client`), described in the module's
/// `xark.exports` section. That works from any crate, so a gadget's types bring their
/// functions to every circuit that takes them.
#[proc_macro_attribute]
pub fn input(attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut item = parse_macro_input!(item as syn::Item);
    let args = match InputArgs::parse(attr.into()) {
        Ok(a) => a,
        Err(e) => return e.to_compile_error().into(),
    };
    let out = match &mut item {
        syn::Item::Struct(_) | syn::Item::Enum(_) => {
            let derive: DeriveInput = match syn::parse2(quote! { #item }) {
                Ok(d) => d,
                Err(e) => return e.to_compile_error().into(),
            };
            let attrs = match &mut item {
                syn::Item::Struct(s) => &mut s.attrs,
                syn::Item::Enum(e) => &mut e.attrs,
                _ => unreachable!(),
            };
            let enum_ = matches!(derive.data, Data::Enum(_));
            if !args.no_derive {
                add_derives(attrs, enum_);
            }
            match &derive.data {
                Data::Struct(d) => struct_input(&derive, d, args.encoding),
                Data::Enum(d) if matches!(args.encoding, StructEncoding::Fields) => {
                    enum_input(&derive, d)
                }
                _ => Err(syn::Error::new_spanned(
                    &derive.ident,
                    "an enum's `#[input]` takes no encoding",
                )),
            }
        }
        syn::Item::Impl(block)
            if !args.no_derive && matches!(args.encoding, StructEncoding::Fields) =>
        {
            export_impl(block)
        }
        syn::Item::Impl(block) => Err(syn::Error::new_spanned(
            &block.self_ty,
            "an `impl` block's `#[input]` takes no arguments",
        )),
        other => Err(syn::Error::new_spanned(
            &*other,
            "#[input] goes on a struct, a fieldless enum or an `impl` block",
        )),
    };
    match out {
        Ok(ts) => quote! { #item #ts }.into(),
        Err(e) => {
            let e = e.to_compile_error();
            quote! { #item #e }.into()
        }
    }
}

/// `#[input(..)]`'s arguments: an encoding, and `no_derive`.
struct InputArgs {
    encoding: StructEncoding,
    no_derive: bool,
}

impl InputArgs {
    fn parse(args: TokenStream2) -> syn::Result<InputArgs> {
        let mut out = InputArgs {
            encoding: StructEncoding::Fields,
            no_derive: false,
        };
        let parser = syn::meta::parser(|meta| {
            if meta.path.is_ident("no_derive") {
                out.no_derive = true;
                Ok(())
            } else if meta.path.is_ident("bytes") {
                out.encoding = StructEncoding::Bytes;
                Ok(())
            } else if meta.path.is_ident("number") {
                meta.parse_nested_meta(|m| {
                    if m.path.is_ident("bits") {
                        let lit: LitInt = m.value()?.parse()?;
                        out.encoding = StructEncoding::Number(lit.base10_parse()?);
                        Ok(())
                    } else {
                        Err(m.error("expected `bits = <n>`"))
                    }
                })
            } else {
                Err(meta.error("expected `number(bits = <n>)`, `bytes` or `no_derive`"))
            }
        });
        syn::parse::Parser::parse2(parser, args)?;
        Ok(out)
    }
}

/// Derive what an input type needs and doesn't list yet: `Clone`, `Copy` and
/// `Debug` (`<Fn>Inputs` debug-prints its fields), and for an enum `PartialEq` and
/// `Eq` too. One already in a `#[derive(..)]` is left alone; `#[input(no_derive)]`
/// skips this for a type with its own impls.
fn add_derives(attrs: &mut Vec<Attribute>, enum_: bool) {
    let mut have = Vec::new();
    for a in attrs.iter().filter(|a| a.path().is_ident("derive")) {
        let _ = a.parse_nested_meta(|m| {
            if let Some(seg) = m.path.segments.last() {
                have.push(seg.ident.to_string());
            }
            Ok(())
        });
    }
    let mut want = vec![
        ("Clone", quote! { ::core::clone::Clone }),
        ("Copy", quote! { ::core::marker::Copy }),
        ("Debug", quote! { ::core::fmt::Debug }),
    ];
    if enum_ {
        want.push(("PartialEq", quote! { ::core::cmp::PartialEq }));
        want.push(("Eq", quote! { ::core::cmp::Eq }));
    }
    let missing: Vec<_> = want
        .into_iter()
        .filter(|(n, _)| !have.iter().any(|h| h == n))
        .map(|(_, p)| p)
        .collect();
    if !missing.is_empty() {
        attrs.push(syn::parse_quote! { #[derive(#(#missing),*)] });
    }
}

/// A struct's encoding, from `#[input(..)]`.
enum StructEncoding {
    Fields,
    Number(u32),
    Bytes,
}

fn struct_input(
    input: &DeriveInput,
    data: &DataStruct,
    enc: StructEncoding,
) -> syn::Result<TokenStream2> {
    let name = &input.ident;
    if !input.generics.params.is_empty() {
        return Err(syn::Error::new_spanned(
            &input.generics,
            "#[input] does not support generic types; implement `xark::Input` by \
             hand (a `TYPE`, and `read`/`write` of the fields in order)",
        ));
    }
    let name_lit = LitStr::new(&name.unraw().to_string(), name.span());
    let fields: Vec<(String, TokenStream2, &Type)> = data
        .fields
        .iter()
        .enumerate()
        .map(|(i, f)| match &f.ident {
            Some(id) => (id.unraw().to_string(), quote! { #id }, &f.ty),
            None => {
                let idx = syn::Index::from(i);
                (i.to_string(), quote! { #idx }, &f.ty)
            }
        })
        .collect();
    let members = fields.iter().map(|(fname, _, ty)| {
        let lit = LitStr::new(fname, name.span());
        quote! { ::xark::input::Member::new(#lit, <#ty as ::xark::Input>::TYPE) }
    });
    let reads = fields.iter().map(|(_, acc, _)| match &data.fields {
        syn::Fields::Named(_) => quote! { #acc: __r.read() },
        _ => quote! { __r.read() },
    });
    let ctor = match &data.fields {
        syn::Fields::Named(_) => quote! { #name { #( #reads ),* } },
        syn::Fields::Unnamed(_) => quote! { #name ( #( #reads ),* ) },
        syn::Fields::Unit => quote! { #name },
    };
    let writes = fields
        .iter()
        .map(|(_, acc, _)| quote! { __w.write(&self.#acc); });

    let encoding = match enc {
        StructEncoding::Fields => quote! { ::xark::input::Encoding::Fields },
        StructEncoding::Number(bits) => {
            let bits = bits as usize;
            quote! { ::xark::input::Encoding::Number { bits: #bits } }
        }
        StructEncoding::Bytes => {
            quote! { ::xark::input::Encoding::Bytes(::xark::input::Bytes::Concat) }
        }
    };
    let host = match enc {
        StructEncoding::Fields => quote! {},
        StructEncoding::Number(bits) => number_host(name, data, bits)?,
        StructEncoding::Bytes => bytes_host(name, data, &fields)?,
    };

    Ok(quote! {
        #[automatically_derived]
        impl ::xark::Input for #name {
            const TYPE: ::xark::input::Type = ::xark::input::Type::Named(&::xark::input::Named {
                name: #name_lit,
                arg: ::core::option::Option::None,
                layout: ::xark::input::Layout::Struct(&[#( #members ),*]),
                encoding: #encoding,
            });
            fn read(__r: &mut ::xark::input::Reader<'_>) -> Self {
                #ctor
            }
            fn write(&self, __w: &mut ::xark::input::Writer<'_>) {
                #( #writes )*
            }
        }

        /// `require_eq(a, b)`: every field element equal, in input order (one equality
        /// constraint each).
        #[automatically_derived]
        impl ::xark::RequireEqCircuit<#name> for #name {
            #[cfg_attr(not(xark), track_caller)]
            fn require_eq_circuit(self, rhs: #name) {
                let (a, b) = (self.to_fields(), rhs.to_fields());
                let mut i = 0;
                while i < <Self as ::xark::Input>::LEN {
                    ::xark::__xark_require_eq_scalar(a[i], b[i]);
                    i += 1;
                }
            }
        }

        #[automatically_derived]
        impl #name {
            /// The value's field elements in input order (fields in declaration order,
            /// arrays by index, nested values inline): feed it to a hash gadget.
            pub fn to_fields(&self) -> [::xark::Field; <Self as ::xark::Input>::LEN] {
                let mut out = [::xark::Field::zero(); <Self as ::xark::Input>::LEN];
                ::xark::input::write_fields(self, &mut out);
                out
            }
        }

        #host
    })
}

/// Host conversions for a `#[input(number(bits = B))]` `{ limbs: [Field; N] }`.
fn number_host(name: &syn::Ident, data: &DataStruct, bits: u32) -> syn::Result<TokenStream2> {
    let (acc, n) = match data.fields.iter().next() {
        Some(f) if data.fields.len() == 1 => {
            let acc = match &f.ident {
                Some(id) => quote! { #id },
                None => quote! { 0 },
            };
            match &f.ty {
                Type::Array(arr) if is_ident(&arr.elem, "Field") => {
                    (acc, eval_usize_lit(&arr.len)?)
                }
                other => {
                    return Err(syn::Error::new_spanned(
                        other,
                        "an `#[input(number(..))]` struct holds its limbs as one `[Field; N]`",
                    ));
                }
            }
        }
        _ => {
            return Err(syn::Error::new_spanned(
                name,
                "an `#[input(number(..))]` struct has one field, `limbs: [Field; N]`",
            ));
        }
    };
    let nbytes = if n * bits as usize <= 264 {
        32
    } else {
        (n * bits as usize).div_ceil(8)
    };
    let build = |v: TokenStream2| match &data.fields {
        syn::Fields::Named(_) => quote! { #name { #acc: #v } },
        _ => quote! { #name(#v) },
    };
    let from_bytes = build(quote! { ::xark::host::limb_fields::<#n>(bytes, #bits) });
    let from_str = build(quote! { ::xark::host::limb_fields_str::<#n>(value, #bits) });
    let from_u128 = build(quote! { ::xark::host::limb_fields::<#n>(&value.to_be_bytes(), #bits) });
    Ok(host_block(quote! {
        #[automatically_derived]
        impl ::xark::host::FromBeBytes for #name {
            const BYTES: usize = #nbytes;
            fn from_be_bytes(bytes: &[u8]) -> Self {
                assert_eq!(bytes.len(), #nbytes, "wrong encoding length");
                #from_bytes
            }
        }
        /// From the number's big-endian bytes.
        #[automatically_derived]
        impl ::core::convert::From<[u8; #nbytes]> for #name {
            fn from(bytes: [u8; #nbytes]) -> Self {
                <Self as ::xark::host::FromBeBytes>::from_be_bytes(&bytes)
            }
        }
        /// From the number, as a decimal or `0x`-hex string.
        #[automatically_derived]
        impl ::core::convert::From<&str> for #name {
            fn from(value: &str) -> Self {
                #from_str
            }
        }
        #[automatically_derived]
        impl ::core::convert::From<String> for #name {
            fn from(value: String) -> Self {
                Self::from(value.as_str())
            }
        }
        #[automatically_derived]
        impl ::core::convert::From<u128> for #name {
            fn from(value: u128) -> Self {
                #from_u128
            }
        }
    }))
}

/// Host conversions for a `#[input(bytes)]` struct: its fields' bytes back to back.
fn bytes_host(
    name: &syn::Ident,
    data: &DataStruct,
    fields: &[(String, TokenStream2, &Type)],
) -> syn::Result<TokenStream2> {
    if !matches!(data.fields, syn::Fields::Named(_)) {
        return Err(syn::Error::new_spanned(
            name,
            "an `#[input(bytes)]` struct needs named fields",
        ));
    }
    let tys: Vec<&Type> = fields.iter().map(|(_, _, t)| *t).collect();
    let mut offset = quote! { 0usize };
    let mut parts = Vec::new();
    for (_, acc, ty) in fields {
        let size = quote! { <#ty as ::xark::host::FromBeBytes>::BYTES };
        parts.push(quote! {
            #acc: <#ty as ::xark::host::FromBeBytes>::from_be_bytes(&bytes[#offset..#offset + #size])
        });
        offset = quote! { #offset + #size };
    }
    let bytes = quote! { 0usize #( + <#tys as ::xark::host::FromBeBytes>::BYTES )* };
    Ok(host_block(quote! {
        #[automatically_derived]
        impl ::xark::host::FromBeBytes for #name {
            const BYTES: usize = #bytes;
            fn from_be_bytes(bytes: &[u8]) -> Self {
                assert_eq!(bytes.len(), #bytes, "wrong encoding length");
                #name { #( #parts ),* }
            }
        }
        /// From the fields' big-endian encodings, back to back.
        #[automatically_derived]
        impl ::core::convert::From<[u8; #bytes]> for #name {
            fn from(bytes: [u8; #bytes]) -> Self {
                <Self as ::xark::host::FromBeBytes>::from_be_bytes(&bytes)
            }
        }
    }))
}

/// Host-only items, with `std` in scope (circuit crates are `no_std`).
fn host_block(items: TokenStream2) -> TokenStream2 {
    quote! {
        #[cfg(not(xark))]
        const _: () = {
            extern crate std;
            use std::string::String;
            #items
        };
    }
}

fn enum_input(input: &DeriveInput, data: &DataEnum) -> syn::Result<TokenStream2> {
    let name = &input.ident;
    if !input.generics.params.is_empty() {
        return Err(syn::Error::new_spanned(
            &input.generics,
            "#[input] does not support generic enums",
        ));
    }
    for v in &data.variants {
        if !matches!(v.fields, syn::Fields::Unit) {
            return Err(syn::Error::new_spanned(
                v,
                "#[input] on an enum needs fieldless variants: each is one value \
                 of a `Choice` or one bit of a `Bitfield`",
            ));
        }
        if let Some((_, d)) = &v.discriminant {
            return Err(syn::Error::new_spanned(
                d,
                "#[input] numbers variants by position; remove the explicit value",
            ));
        }
    }
    let name_lit = LitStr::new(&name.unraw().to_string(), name.span());
    let idents: Vec<&syn::Ident> = data.variants.iter().map(|v| &v.ident).collect();
    let names = idents
        .iter()
        .map(|i| LitStr::new(&i.unraw().to_string(), i.span()));
    Ok(quote! {
        #[automatically_derived]
        impl ::xark::Enum for #name {
            const VARIANTS: ::xark::input::Variants = ::xark::input::Variants {
                name: #name_lit,
                names: &[#( #names ),*],
            };
            fn index(self) -> usize {
                self as usize
            }
            fn from_index(index: usize) -> ::core::option::Option<Self> {
                const ALL: &[#name] = &[#( #name::#idents ),*];
                ALL.get(index).copied()
            }
        }
    })
}

/// A `usize` from an integer-literal length expression (`[Field; 32]` → `32`).
fn eval_usize_lit(e: &Expr) -> syn::Result<usize> {
    match e {
        Expr::Lit(ExprLit {
            lit: Lit::Int(li), ..
        }) => li.base10_parse::<usize>(),
        other => Err(syn::Error::new_spanned(
            other,
            "array lengths must be integer literals",
        )),
    }
}

fn export_impl(block: &ItemImpl) -> syn::Result<TokenStream2> {
    if !block.generics.params.is_empty() {
        return Err(syn::Error::new_spanned(
            &block.self_ty,
            "#[input] goes on a plain `impl Type { .. }` or `impl Trait for Type { .. }` block",
        ));
    }
    let self_ty = &block.self_ty;
    let type_name = type_string(self_ty);
    // `Type::f`, or `<Type as Trait>::f` for a trait's (`impl Default for Policy`).
    let path = match &block.trait_ {
        Some((_, tr, _)) => quote! { <#self_ty as #tr> },
        None => quote! { <#self_ty> },
    };
    let mut items = Vec::new();
    for item in &block.items {
        let ImplItem::Fn(f) = item else { continue };
        // A trait's functions are as public as the trait; an inherent one, if `pub`.
        if block.trait_.is_none() && !matches!(f.vis, syn::Visibility::Public(_)) {
            continue;
        }
        let name = &f.sig.ident;
        // A client can't pick a type for a generic: say so here, not in the
        // `client.wasm` build.
        if let Some(g) = f
            .sig
            .generics
            .params
            .iter()
            .find(|g| !matches!(g, syn::GenericParam::Lifetime(_)))
        {
            return Err(syn::Error::new_spanned(
                g,
                "an exported function can't be generic (a client can't choose its type): \
                 take a concrete type, or `impl Into<T>`",
            ));
        }
        let cfgs: Vec<&Attribute> = f
            .attrs
            .iter()
            .filter(|a| a.path().is_ident("cfg"))
            .collect();
        let doc = f
            .attrs
            .iter()
            .filter_map(|a| match &a.meta {
                syn::Meta::NameValue(nv) if nv.path.is_ident("doc") => match &nv.value {
                    Expr::Lit(ExprLit {
                        lit: Lit::Str(s), ..
                    }) => Some(s.value().trim().to_string()),
                    _ => None,
                },
                _ => None,
            })
            .collect::<Vec<_>>()
            .join("\n");
        let mut receiver = None;
        let mut decode = Vec::new();
        let mut call_args = Vec::new();
        let mut params = Vec::new();
        for input in &f.sig.inputs {
            let i = decode.len();
            match input {
                FnArg::Receiver(r) => {
                    if r.mutability.is_some() && r.reference.is_some() {
                        return Err(syn::Error::new_spanned(
                            r,
                            "an exported method takes `self` or `&self`, not `&mut self`",
                        ));
                    }
                    receiver = Some(if r.reference.is_some() {
                        "ref"
                    } else {
                        "value"
                    });
                    // Named as the client names it (`policy`).
                    let this = type_name.to_lowercase();
                    decode.push(
                        quote! { let __self: #self_ty = ::xark::client::arg(__args, #i, #this)?; },
                    );
                    call_args.push(if r.reference.is_some() {
                        quote! { &__self }
                    } else {
                        quote! { __self }
                    });
                }
                FnArg::Typed(pt) => {
                    let Pat::Ident(pi) = &*pt.pat else {
                        return Err(syn::Error::new_spanned(
                            &pt.pat,
                            "an exported method's parameters are plain names",
                        ));
                    };
                    // `&T` is a `T`, lent to the call.
                    let (ty, by_ref) = match &*pt.ty {
                        Type::Reference(r) if r.mutability.is_some() => {
                            return Err(syn::Error::new_spanned(
                                r,
                                "an exported function takes `T` or `&T`, not `&mut T`",
                            ));
                        }
                        Type::Reference(r) => (&*r.elem, true),
                        ty => (ty, false),
                    };
                    let ty = into_target(ty).unwrap_or(ty);
                    // `Self` means nothing in the export, outside the `impl`.
                    let ty: Type = syn::parse2(replace_self(quote!(#ty), self_ty))?;
                    let v = format_ident!("__a{i}");
                    let pname = pi.ident.unraw().to_string();
                    decode.push(quote! { let #v: #ty = ::xark::client::arg(__args, #i, #pname)?; });
                    call_args.push(if by_ref {
                        quote! { &#v }
                    } else {
                        quote! { #v }
                    });
                    params.push(format!(
                        "{{\"name\":{},\"type\":{}}}",
                        json_str(&pi.ident.unraw().to_string()),
                        json_str(&type_string(&ty)),
                    ));
                }
            }
        }
        let returns = match &f.sig.output {
            ReturnType::Type(_, t) if !is_ident(t, "Self") => type_string(t),
            ReturnType::Type(..) => type_name.clone(),
            ReturnType::Default => {
                return Err(syn::Error::new_spanned(
                    &f.sig,
                    "an exported method returns a value (an `xark::Input` type)",
                ));
            }
        };
        // Named as written, without a raw identifier's `r#`.
        let fn_name = name.unraw().to_string();
        let export = format!("{type_name}.{fn_name}");
        let desc = format!(
            "{{\"export\":{},\"type\":{},\"name\":{},\"self\":{},\"params\":[{}],\"returns\":{},\"doc\":{}}}\n",
            json_str(&export),
            json_str(&type_name),
            json_str(&fn_name),
            receiver.map_or("null".to_string(), json_str),
            params.join(","),
            json_str(&returns),
            json_str(&doc),
        );
        let bytes = syn::LitByteStr::new(desc.as_bytes(), name.span());
        let len = desc.len();
        let shim = format_ident!("__xark_export_{}_{}", ident_part(&type_name), fn_name);
        let stat = format_ident!("__XARK_EXPORT_{}_{}", ident_part(&type_name), fn_name);
        let export_lit = LitStr::new(&export, name.span());
        items.push(quote! {
            #(#cfgs)*
            #[doc(hidden)]
            #[allow(non_snake_case)]
            #[unsafe(export_name = #export_lit)]
            pub extern "C" fn #shim(__ptr: *const u8, __len: usize) -> u64 {
                ::xark::client::call(__ptr, __len, |__args| {
                    #(#decode)*
                    ::core::result::Result::Ok(::xark::client::to_json(&#path::#name(#(#call_args),*))?)
                })
            }
            #(#cfgs)*
            #[unsafe(link_section = "xark.exports")]
            #[used]
            #[allow(non_upper_case_globals)]
            static #stat: [u8; #len] = *#bytes;
        });
    }
    Ok(quote! {
        ::xark::__client_export! {
            #(#items)*
        }
    })
}

/// `tokens` with every `Self` as `self_ty` (`Option<Self>` → `Option<Policy>`).
fn replace_self(tokens: TokenStream2, self_ty: &Type) -> TokenStream2 {
    use proc_macro2::{Group, TokenTree};
    tokens
        .into_iter()
        .flat_map(|t| match t {
            TokenTree::Ident(i) if i == "Self" => quote!(#self_ty),
            TokenTree::Group(g) => {
                let mut out = Group::new(g.delimiter(), replace_self(g.stream(), self_ty));
                out.set_span(g.span());
                TokenTree::Group(out).into()
            }
            t => t.into(),
        })
        .collect()
}

/// `T` of an `impl Into<T>` parameter.
fn into_target(ty: &Type) -> Option<&Type> {
    let Type::ImplTrait(TypeImplTrait { bounds, .. }) = ty else {
        return None;
    };
    bounds.iter().find_map(|b| match b {
        TypeParamBound::Trait(t) => {
            let seg = t.path.segments.last()?;
            if seg.ident != "Into" {
                return None;
            }
            match &seg.arguments {
                PathArguments::AngleBracketed(ab) => match ab.args.first()? {
                    GenericArgument::Type(t) => Some(t),
                    _ => None,
                },
                _ => None,
            }
        }
        _ => None,
    })
}

/// A type as written, without spaces: `Date`, `Choice<Country>`, `[u8;4]`.
fn type_string(ty: &Type) -> String {
    quote!(#ty).to_string().replace(' ', "")
}

/// A type name as an identifier fragment (`Choice<Country>` → `Choice_Country_`).
fn ident_part(s: &str) -> String {
    s.chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect()
}

fn json_str(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
