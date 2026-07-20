//! `#[circuit]` — declare a circuit entry with **native** input types and
//! generate a native-typed input struct for its `xark_prover` tests.
//!
//! An entry names its inputs with ordinary Rust types wrapped in
//! `Private`/`Public`, e.g.
//!
//! ```ignore
//! #[circuit]
//! pub fn xark_sha256_test(input: Private<[u8; 56]>, result: Public<[u8; 32]>) {
//!     assert_eq(sha256(input), result);
//! }
//! ```
//!
//! The macro does three things:
//!
//! 1. **Rewrites the signature** into the Field-backed types the compiler lowers:
//!    `Field` stays `Field`, `[u8; N]` becomes `[Field; N]`, and `[u8; 32]`
//!    becomes a [`Hash`](xark::Hash) — a 256-bit hash packed into 2 field
//!    elements, so a public expected hash is 2 public inputs, not 256. The body is
//!    emitted verbatim except for a `use` that shadows `assert_eq` with the
//!    composite-aware [`__circuit_assert_eq`](xark::__circuit_assert_eq), so
//!    `assert_eq(sha256(x), hash)` type-checks alongside scalar equalities.
//! 2. **Generates `<Fn>Inputs`** — a `#[cfg(test)]` struct whose fields are the
//!    *native* types (`input: [u8; 56]`, `result: [u8; 32]`), so tests read
//!    `check(XarkSha256TestInputs { input, result }).unwrap()`, named so
//!    parameters can't be transposed.
//! 3. **Implements `ProveInputs`** — fanning each parameter out to its witness
//!    leaves with the compiler's structural-flatten leaf names and decimal values.
//!
//! The struct and impl are `#[cfg(test)]`-gated (`xark_prover` is a dev-dependency,
//! proving is a test-time convenience). The entry itself lowers exactly as a plain
//! `fn circuit` would, so `xark build` is unaffected.
//!
//! `#[derive(CircuitInput)]` — see [`derive_circuit_input`] — generates the
//! `Into<[Field; N]>` that makes a Field-composed struct a typed circuit input
//! whose flatten order is *mechanically* the compiler's structural-flatten order.

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use syn::{
    parse_macro_input, Attribute, Data, DataStruct, DeriveInput, Expr, ExprLit, FnArg,
    GenericArgument, ItemFn, Lit, LitInt, LitStr, Pat, PathArguments, Type,
};

#[proc_macro_attribute]
pub fn circuit(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let func = parse_macro_input!(item as ItemFn);
    match circuit_impl(&func) {
        Ok(ts) => ts.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

/// How a `#[circuit]` parameter fans out to witness leaves — the compiler names
/// leaves by structurally flattening the *circuit* type (`flatten_field_leaves`),
/// so this must reproduce those exact names and their values.
enum Fanout {
    /// A `Field` scalar: one leaf named exactly `name`.
    Scalar,
    /// `[u8; N]` (N != 32) → `[Field; N]`: `N` byte leaves `name[0..N]`.
    ByteArray(usize),
    /// `[u8; 32]` → `Hash`: 2 packed leaves `name.hi` / `name.lo`, the top and low
    /// 16 bytes of the hash read big-endian. Two field public inputs, not 256 bits.
    Hash,
    /// A custom transparent gadget type (e.g. `Fq`, `Point`) that implements
    /// [`xark_prover::NativeInput`]: the fan-out delegates to its `leaves`, and the
    /// native struct field is its `NativeInput::Native` associated type.
    Native,
}

/// One resolved entry parameter.
struct CircuitParam {
    /// Identifier — the struct field name *and* the leaf-name root.
    name: syn::Ident,
    /// `Private` / `Public`, kept as the author wrote it.
    wrapper: syn::Ident,
    /// The generated `<Fn>Inputs` field type — the **native** type (`[u8; 32]`, `String`).
    native_ty: TokenStream2,
    /// The compiler-visible inner type (`::xark::Field`, `::xark::Digest`, `[::xark::Field; N]`).
    circuit_ty: TokenStream2,
    fanout: Fanout,
}

/// Rewrite a `#[circuit]` entry: map its **native** parameter types
/// (`Private<[u8; 56]>`, `Public<[u8; 32]>`, `Private<Field>`) to the Field-backed
/// circuit types the compiler accepts, shadow `assert_eq` in the body with the
/// composite-aware dispatcher, and emit a native-typed `<Fn>Inputs` struct whose
/// `ProveInputs` fans each parameter out to its witness leaves for `check`.
fn circuit_impl(func: &ItemFn) -> syn::Result<TokenStream2> {
    let params = func
        .sig
        .inputs
        .iter()
        .map(resolve_param)
        .collect::<syn::Result<Vec<_>>>()?;

    // The compiler-visible entry: native param types rewritten to circuit types,
    // body prefixed with a `use` that shadows the scalar `assert_eq` intrinsic
    // with the trait-dispatched one (so `assert_eq(sha256(x), digest)` compiles).
    // The entry is otherwise emitted verbatim, so the driver extracts it exactly.
    let attrs = &func.attrs;
    let vis = &func.vis;
    let fn_ident = &func.sig.ident;
    let stmts = &func.block.stmts;
    let sig_params: Vec<TokenStream2> = params
        .iter()
        .map(|p| {
            let (name, wrapper, cty) = (&p.name, &p.wrapper, &p.circuit_ty);
            quote! { #name: #wrapper<#cty> }
        })
        .collect();
    // The compiler-visible circuit entry (the real `Field` body the xark compiler
    // lowers to MIR). It is compiled only when *not* a `test`/`host` build — in
    // those, the same `fn` name is instead the native-typed validator below, so a
    // downstream crate calls `mycircuit::<fn>(a, b, c)` to check inputs without a
    // rename. The two are `cfg`-exclusive, so there is never a name collision.
    let entry = quote! {
        #[cfg(xark)]
        #(#attrs)*
        #vis fn #fn_ident(#(#sig_params),*) {
            #[allow(unused_imports)]
            use ::xark::__circuit_assert_eq as assert_eq;
            #(#stmts)*
        }
    };

    // In a `test`/`host` build the entry above is cfg'd out, which would leave the
    // circuit's own `use`s (its `Private`/`Public` wrappers and gadget fns) unused.
    // Emit a hidden, never-called copy of the body there so those imports stay used
    // (no spurious warnings) — it type-checks but never runs.
    let circuit_def_ident = format_ident!("__{}_circuit_def", fn_ident);
    let sig_params_def = sig_params.clone();
    let circuit_def = quote! {
        #[cfg(not(xark))]
        #[doc(hidden)]
        #[allow(dead_code, unused_imports)]
        fn #circuit_def_ident(#(#sig_params_def),*) {
            #[allow(unused_imports)]
            use ::xark::__circuit_assert_eq as assert_eq;
            #(#stmts)*
        }
    };

    let struct_name = format_ident!("{}Inputs", to_pascal(&fn_ident.to_string()));
    let field_defs = params.iter().map(|p| {
        let (name, nty) = (&p.name, &p.native_ty);
        quote! { pub #name: #nty }
    });
    let fanouts = params.iter().map(fanout_code);

    let fn_name_lit = LitStr::new(&fn_ident.to_string(), fn_ident.span());
    // The native-typed validator that *replaces* the entry `fn` in `test`/`host`
    // builds: same name, the entry's **native** parameter types in order, returning
    // the check result — so `mycircuit::<fn>(a, b, c).unwrap()` checks inputs against
    // the built circuit (`target/xark/<fn>/`) with no struct literal and no rename.
    let host_params = params.iter().map(|p| {
        let (name, nty) = (&p.name, &p.native_ty);
        quote! { #name: #nty }
    });
    let host_ctor = params.iter().map(|p| &p.name);

    Ok(quote! {
        #entry
        #circuit_def

        /// The native-typed validator for this circuit. In a `test`/`host` build the
        /// circuit `fn` *is* this function (the `Field` body is compiled only for the
        /// xark compiler): it takes the entry's native inputs, loads the built
        /// circuit from `target/xark/<name>/`, and returns `Ok(())` if they satisfy
        /// it (else an actionable `Err`). So `mycircuit::<fn>(a, b, c).unwrap()`.
        #[cfg(not(xark))]
        #(#attrs)*
        #vis fn #fn_ident(#(#host_params),*) -> ::core::result::Result<(), ::xark_prover::ProveError> {
            ::xark_prover::circuit(#fn_name_lit).check(#struct_name { #(#host_ctor),* })
        }

        /// Typed inputs for this circuit (generated by `#[circuit]`), one field per
        /// entry parameter with its **native** type. For a custom artifact location
        /// (e.g. a downstream crate), use it directly:
        /// `xark_prover::circuit_at(dir).check(<Fn>Inputs { .. })` — or `.prove(..)`.
        #[cfg(not(xark))]
        #[derive(Clone, Debug)]
        pub struct #struct_name {
            #(#field_defs,)*
        }

        #[cfg(not(xark))]
        impl ::xark_prover::ProveInputs for #struct_name {
            fn into_inputs(self) -> ::std::vec::Vec<(::std::string::String, ::std::string::String)> {
                let mut out: ::std::vec::Vec<(::std::string::String, ::std::string::String)> =
                    ::std::vec::Vec::new();
                #(#fanouts)*
                out
            }
        }
    })
}

/// Resolve one entry parameter: a plain identifier wrapped in `Private<_>` /
/// `Public<_>`, whose inner native type maps to a supported circuit type.
fn resolve_param(arg: &FnArg) -> syn::Result<CircuitParam> {
    let pt = match arg {
        FnArg::Typed(pt) => pt,
        FnArg::Receiver(r) => {
            return Err(syn::Error::new_spanned(
                r,
                "#[circuit] cannot take a `self` parameter",
            ))
        }
    };
    let name = match &*pt.pat {
        Pat::Ident(pi) => pi.ident.clone(),
        other => {
            return Err(syn::Error::new_spanned(
                other,
                "#[circuit] parameters must be plain identifiers (no `_`, no patterns)",
            ))
        }
    };
    let (wrapper, inner) = unwrap_visibility(&pt.ty)?;
    let (native_ty, circuit_ty, fanout) = map_inner(&inner)?;
    Ok(CircuitParam {
        name,
        wrapper,
        native_ty,
        circuit_ty,
        fanout,
    })
}

/// Peel `Private<Inner>` / `Public<Inner>`, returning the wrapper ident and inner
/// type. A circuit input must declare its visibility, so anything else is an error.
fn unwrap_visibility(ty: &Type) -> syn::Result<(syn::Ident, Type)> {
    if let Type::Path(tp) = ty {
        if let Some(seg) = tp.path.segments.last() {
            if seg.ident == "Private" || seg.ident == "Public" {
                if let PathArguments::AngleBracketed(ab) = &seg.arguments {
                    if let Some(GenericArgument::Type(inner)) = ab.args.first() {
                        return Ok((seg.ident.clone(), inner.clone()));
                    }
                }
            }
        }
    }
    Err(syn::Error::new_spanned(
        ty,
        "#[circuit] parameters must be wrapped in `Private<..>` or `Public<..>`",
    ))
}

/// Map a native inner type to `(native struct-field type, circuit inner type, fanout)`.
/// Supported: `Field`, `[u8; 32]` (a SHA-256 digest), and `[u8; N]` (byte string).
fn map_inner(inner: &Type) -> syn::Result<(TokenStream2, TokenStream2, Fanout)> {
    if let Type::Path(tp) = inner {
        if tp.path.segments.last().is_some_and(|s| s.ident == "Field") {
            // A `Field` value is a full field element — up to ~254 bits, well past
            // `i128` — so the struct takes it as a `String` (a decimal or `0x`-hex
            // value, `"2".into()` for a literal or a runtime-computed reference).
            // That also matches how the CLI `--inputs` takes scalars.
            return Ok((quote! { String }, quote! { ::xark::Field }, Fanout::Scalar));
        }
    }
    if let Type::Array(arr) = inner {
        if let Type::Path(elem) = &*arr.elem {
            if elem.path.segments.last().is_some_and(|s| s.ident == "u8") {
                let n = eval_usize_lit(&arr.len)?;
                if n == 32 {
                    return Ok((quote! { [u8; 32] }, quote! { ::xark::Hash }, Fanout::Hash));
                }
                return Ok((
                    quote! { [u8; #n] },
                    quote! { [::xark::Field; #n] },
                    Fanout::ByteArray(n),
                ));
            }
        }
    }
    // Fallback: any other named type is treated as a **transparent gadget type**
    // (e.g. a curve `Fq`/`Point`) that implements `xark_prover::NativeInput`. Its
    // `<Ty as NativeInput>::Native` associated type is the native struct field, and
    // its `leaves` produce the compiler's flatten names. A type that doesn't impl
    // the trait is a (reasonably clear) compile error at the delegation site.
    if let Type::Path(_) = inner {
        return Ok((
            quote! { <#inner as ::xark_prover::NativeInput>::Native },
            quote! { #inner },
            Fanout::Native,
        ));
    }
    Err(syn::Error::new_spanned(
        inner,
        "unsupported #[circuit] parameter type; supported: `Field`, `[u8; N]`, \
         `[u8; 32]` (a SHA-256 digest), or a gadget type implementing `NativeInput`",
    ))
}

/// The `ProveInputs` fan-out statements for one parameter: push `(leaf-name,
/// decimal-value)` pairs whose names match the compiler's structural-flatten
/// names for the circuit type, in flatten order.
fn fanout_code(p: &CircuitParam) -> TokenStream2 {
    let name = &p.name;
    let name_lit = LitStr::new(&name.to_string(), name.span());
    match p.fanout {
        Fanout::Scalar => quote! {
            out.push((
                ::std::string::String::from(#name_lit),
                ::std::string::ToString::to_string(&self.#name),
            ));
        },
        Fanout::ByteArray(n) => quote! {
            {
                let mut __i = 0usize;
                while __i < #n {
                    out.push((
                        ::std::format!("{}[{}]", #name_lit, __i),
                        ::std::string::ToString::to_string(&self.#name[__i]),
                    ));
                    __i += 1;
                }
            }
        },
        // The hash packs into two 128-bit field halves: `hi` = the top 16 bytes,
        // `lo` = the low 16 bytes, each big-endian (16 bytes = 128 bits fits a
        // `u128` exactly). These are the `name.hi` / `name.lo` public inputs; the
        // circuit's `pack` recomposes the same two halves from the digest bits.
        Fanout::Hash => quote! {
            {
                let __b = self.#name;
                let mut __hi = 0u128;
                let mut __k = 0usize;
                while __k < 16usize {
                    __hi = (__hi << 8) | (__b[__k] as u128);
                    __k += 1;
                }
                let mut __lo = 0u128;
                while __k < 32usize {
                    __lo = (__lo << 8) | (__b[__k] as u128);
                    __k += 1;
                }
                out.push((
                    ::std::format!("{}.hi", #name_lit),
                    ::std::string::ToString::to_string(&__hi),
                ));
                out.push((
                    ::std::format!("{}.lo", #name_lit),
                    ::std::string::ToString::to_string(&__lo),
                ));
            }
        },
        // A transparent gadget type: delegate to its `NativeInput::leaves`, which
        // produces the compiler's flatten names (`name.x.limbs[i]`, `name[i]`, …).
        Fanout::Native => {
            let ty = &p.circuit_ty;
            quote! {
                out.extend(
                    <#ty as ::xark_prover::NativeInput>::leaves(&self.#name, #name_lit),
                );
            }
        }
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

/// `#[derive(CircuitInput)]` — make a Field-composed struct usable as a typed
/// circuit input by generating its `Into<[Field; N]>` (i.e. `From<Self> for
/// [Field; N]`), **in the compiler's structural-flatten order**: fields in
/// declaration order, arrays in index order, bottoming out at `Field`.
///
/// This is the piece that turns host↔circuit layout agreement from *discipline*
/// into a *mechanical guarantee*. The compiler flattens an input type by walking
/// its fields (index order) and arrays (index order) down to each `Field` leaf;
/// this derive emits an `Into` that traverses the exact same way, so leaf `k` of
/// the produced array is always leaf `k` of the input — a host-side witness
/// builder can then drive the input from a native value with no hand-written
/// per-type fan-out and no chance of an order skew.
///
/// ```ignore
/// #[derive(Clone, Copy, CircuitInput)]
/// struct Digest { bits: [[Field; 32]; 8] }   // ⇒ impl From<Digest> for [Field; 256]
/// ```
///
/// Supported field types: `Field`, and (possibly nested) fixed arrays of `Field`
/// with **integer-literal** lengths. Generic types (const-generic lengths) are
/// rejected — the flattened `N` must be a compile-time literal; write the `From`
/// by hand for those.
#[proc_macro_derive(CircuitInput)]
pub fn derive_circuit_input(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as DeriveInput);
    match circuit_input_impl(&input) {
        Ok(ts) => ts.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

fn circuit_input_impl(input: &DeriveInput) -> syn::Result<TokenStream2> {
    let name = &input.ident;
    if !input.generics.params.is_empty() {
        return Err(syn::Error::new_spanned(
            &input.generics,
            "#[derive(CircuitInput)] does not support generic types: the flattened length \
             must be a compile-time literal. Implement `From<Self> for [Field; N]` by hand.",
        ));
    }
    let data = match &input.data {
        Data::Struct(d) => d,
        _ => {
            return Err(syn::Error::new_spanned(
                name,
                "#[derive(CircuitInput)] only supports structs",
            ))
        }
    };

    let mut total = 0usize;
    let mut blocks = Vec::new();
    for (i, field) in data.fields.iter().enumerate() {
        let access = match &field.ident {
            Some(id) => quote! { __v.#id },
            None => {
                let idx = syn::Index::from(i);
                quote! { __v.#idx }
            }
        };
        let (count, stmts) = walk_type(&field.ty, &access, 0)?;
        total += count;
        blocks.push(stmts);
    }
    let n = total;

    Ok(quote! {
        #[automatically_derived]
        impl ::core::convert::From<#name> for [::xark::Field; #n] {
            fn from(__v: #name) -> [::xark::Field; #n] {
                let mut out = [<::xark::Field as ::core::convert::From<u8>>::from(0u8); #n];
                let mut __i = 0usize;
                #( #blocks )*
                let _ = __i;
                out
            }
        }
    })
}

/// Emit the flatten statements for one field/element `access` of type `ty`, and
/// return `(leaf count, statements)`. Recurses through arrays; a `Field` is one
/// leaf. `depth` names the per-level loop variable so nested arrays don't collide.
fn walk_type(ty: &Type, access: &TokenStream2, depth: usize) -> syn::Result<(usize, TokenStream2)> {
    match ty {
        Type::Path(tp) if tp.path.segments.last().is_some_and(|s| s.ident == "Field") => {
            Ok((1, quote! { out[__i] = #access; __i += 1; }))
        }
        Type::Array(arr) => {
            let len = eval_usize_lit(&arr.len)?;
            let kv = format_ident!("__k{depth}");
            let (inner_count, inner) = walk_type(&arr.elem, &quote! { #access[#kv] }, depth + 1)?;
            let block = quote! {
                {
                    let mut #kv = 0usize;
                    while #kv < #len {
                        #inner
                        #kv += 1;
                    }
                }
            };
            Ok((len * inner_count, block))
        }
        other => Err(syn::Error::new_spanned(
            other,
            "#[derive(CircuitInput)] fields must be `Field` or fixed arrays of `Field` \
             (nesting allowed); array lengths must be integer literals",
        )),
    }
}

/// `#[derive(Transparent)]` — generate the host-side [`NativeInput`] fan-out for a
/// transparent circuit type, so a gadget author declares the type once and the
/// leaf-name / limb contract (which must match the compiler's structural flatten)
/// is *generated*, not hand-written and hand-duplicated across gadgets.
///
/// Two shapes:
///  * a **leaf** field element `{ limbs: [Field; N] }` marked `#[transparent(bits = B)]`:
///    native form `[u8; N*B/8]` (big-endian), flattening to `<prefix>.limbs[i]`.
///  * a **composite** of transparent fields (e.g. `{ x: Fq, y: Fq }`): native form is
///    the fields' native bytes concatenated, flattening by recursing into each field
///    under `<prefix>.<field>`.
///
/// The generated impl is `#[cfg(not(xark))]` — `NativeInput` is host-only.
///
/// [`NativeInput`]: xark_prover::NativeInput
#[proc_macro_derive(Transparent, attributes(transparent))]
pub fn derive_transparent(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as DeriveInput);
    match transparent_impl(&input) {
        Ok(ts) => ts.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

/// Parse `#[transparent(bits = B)]` → `Some(B)` (leaf mode); `None` = composite.
fn parse_transparent_bits(attrs: &[Attribute]) -> syn::Result<Option<u32>> {
    for attr in attrs {
        if attr.path().is_ident("transparent") {
            let mut bits = None;
            attr.parse_nested_meta(|meta| {
                if meta.path.is_ident("bits") {
                    let lit: LitInt = meta.value()?.parse()?;
                    bits = Some(lit.base10_parse::<u32>()?);
                    Ok(())
                } else {
                    Err(meta.error("expected `bits = <n>`"))
                }
            })?;
            return Ok(bits);
        }
    }
    Ok(None)
}

/// A leaf transparent type is `{ limbs: [Field; N] }`; return `N`.
fn leaf_limb_count(data: &DataStruct) -> syn::Result<usize> {
    let field = data.fields.iter().next().ok_or_else(|| {
        syn::Error::new_spanned(
            &data.fields,
            "a `#[transparent(bits = ..)]` leaf needs a `limbs: [Field; N]` field",
        )
    })?;
    match &field.ty {
        Type::Array(arr) => eval_usize_lit(&arr.len),
        other => Err(syn::Error::new_spanned(
            other,
            "a `#[transparent(bits = ..)]` leaf's field must be `[Field; N]`",
        )),
    }
}

fn transparent_impl(input: &DeriveInput) -> syn::Result<TokenStream2> {
    let name = &input.ident;
    if !input.generics.params.is_empty() {
        return Err(syn::Error::new_spanned(
            &input.generics,
            "#[derive(Transparent)] does not support generic types",
        ));
    }
    let data = match &input.data {
        Data::Struct(d) => d,
        _ => {
            return Err(syn::Error::new_spanned(
                name,
                "#[derive(Transparent)] only supports structs",
            ))
        }
    };

    let (native_ty, leaves_body) = if let Some(bits) = parse_transparent_bits(&input.attrs)? {
        // LEAF: `{ limbs: [Field; N] }`, native = big-endian `[u8; N*B/8]`.
        let n = leaf_limb_count(data)?;
        let bytes = n * (bits as usize) / 8;
        (
            quote! { [u8; #bytes] },
            quote! { ::xark_prover::limb_leaves(native, prefix, #n, #bits) },
        )
    } else {
        // COMPOSITE: native = concatenation of the fields' native bytes; recurse.
        let field_size = |fty: &Type| {
            quote! { ::core::mem::size_of::<<#fty as ::xark_prover::NativeInput>::Native>() }
        };
        let sizes: Vec<_> = data.fields.iter().map(|f| field_size(&f.ty)).collect();
        let native_ty = quote! { [u8; { 0usize #( + #sizes )* }] };

        let mut stmts = Vec::new();
        let mut offset = quote! { 0usize };
        for (i, field) in data.fields.iter().enumerate() {
            let fty = &field.ty;
            let fname = match &field.ident {
                Some(id) => id.to_string(),
                None => i.to_string(),
            };
            let size = field_size(fty);
            stmts.push(quote! {
                {
                    let __start = #offset;
                    let __end = __start + #size;
                    let __chunk: &<#fty as ::xark_prover::NativeInput>::Native =
                        ::core::convert::TryFrom::try_from(&native[__start..__end]).unwrap();
                    __out.extend(<#fty as ::xark_prover::NativeInput>::leaves(
                        __chunk,
                        &std::format!("{}.{}", prefix, #fname),
                    ));
                }
            });
            offset = quote! { #offset + #size };
        }
        (
            native_ty,
            quote! {
                let mut __out = Vec::new();
                #( #stmts )*
                __out
            },
        )
    };

    // `NativeInput` lives in `xark_prover` (a `std` crate), but a gadget crate is
    // `#![no_std]` — so bring `std` in inside an anonymous const (the hygienic-derive
    // pattern), mirroring what the hand-written host modules did with `extern crate std`.
    Ok(quote! {
        #[cfg(not(xark))]
        const _: () = {
            extern crate std;
            use std::string::String;
            use std::vec::Vec;
            #[automatically_derived]
            impl ::xark_prover::NativeInput for #name {
                type Native = #native_ty;
                fn leaves(native: &Self::Native, prefix: &str) -> Vec<(String, String)> {
                    #leaves_body
                }
            }
        };
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
            "#[derive(CircuitInput)] array lengths must be integer literals",
        )),
    }
}
