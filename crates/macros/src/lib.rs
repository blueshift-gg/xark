//! `#[circuit]` — declare a circuit entry with **native** input types and
//! generate the native validator and typed host inputs used by `xark test`.
//!
//! ```ignore
//! #[circuit]
//! pub fn sha256(msg: Private<[u8; 3]>, digest: Public<Hash>) {
//!     require_eq(xark_sha256::sha256(msg), digest);
//! }
//! ```
//!
//! The macro: (1) rewrites the signature into the Field-backed types the compiler
//! lowers (`[u8; N]` → `[Field; N]`, a `NativeInput` gadget → its native form),
//! emitting the body verbatim; (2) generates a native-typed `<Fn>Inputs` struct,
//! named so parameters can't be transposed; (3) implements `ProveInputs`, fanning
//! each parameter out to its witness leaves using the compiler's structural-flatten
//! leaf names and decimal values. Core stays gadget-agnostic — `Hash` packing lives
//! in `xark-hash`, not here.
//!
//! `#[derive(CircuitInput)]` — see [`derive_circuit_input`] — generates the
//! `Into<[Field; N]>` whose flatten order mechanically matches the compiler's
//! structural-flatten order.
//!
//! The attribute must sit on a **module-scope** function: the expansion wraps
//! the entry in a sibling module that resolves the surrounding scope via
//! `use super::*;`, which has no meaning inside a function body or an `impl`
//! block.

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use syn::{
    Attribute, Data, DataStruct, DeriveInput, Expr, ExprLit, FnArg, GenericArgument, ItemFn, Lit,
    LitInt, LitStr, Pat, PathArguments, Type, parse_macro_input,
};

#[proc_macro_attribute]
pub fn circuit(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let func = parse_macro_input!(item as ItemFn);
    match circuit_impl(&func) {
        Ok(ts) => ts.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

/// How a `#[circuit]` parameter fans out to witness leaves. The compiler names
/// leaves by structurally flattening the *circuit* type (`flatten_field_leaves`),
/// so this must reproduce those exact names and their values.
enum Fanout {
    /// A `Field` scalar: one leaf named exactly `name`, rendered canonically.
    FieldScalar,
    /// A native unsigned integer scalar: one leaf named exactly `name`.
    UIntScalar,
    /// `[u8; N]` → `[Field; N]`: `N` byte leaves `name[0..N]`.
    ByteArray(Expr),
    /// `[Field; N]` → `[Field; N]`: `N` field leaves `name[0..N]`.
    FieldArray(Expr),
    /// A transparent gadget type (`Fq`, `Point`) implementing
    /// Xark's hidden `NativeInput`: fan-out delegates to its `leaves`, native
    /// struct field is its `NativeInput::Native` associated type.
    Native,
}

/// One resolved entry parameter.
struct CircuitParam {
    /// Struct field name *and* leaf-name root.
    name: syn::Ident,
    /// `Private` / `Public`, as the author wrote it.
    wrapper: syn::Ident,
    /// Generated `<Fn>Inputs` field type — the **native** type (`Field`, `[u8; 32]`).
    native_ty: TokenStream2,
    /// Compiler-visible inner type (`::xark::Field`, `[::xark::Field; N]`, a gadget type).
    circuit_ty: TokenStream2,
    fanout: Fanout,
}

/// Rewrite a `#[circuit]` entry: map native parameter types to the Field-backed
/// circuit types the compiler accepts, and emit a native-typed `<Fn>Inputs` struct
/// whose `ProveInputs` fans each parameter out to its witness leaves for `check`.
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
    let module_ident = format_ident!("__xark_generated_{}", fn_ident);
    let stmts = &func.block.stmts;
    let sig_params: Vec<TokenStream2> = params
        .iter()
        .map(|p| {
            let (name, wrapper, cty) = (&p.name, &p.wrapper, &p.circuit_ty);
            quote! { #name: #wrapper<#cty> }
        })
        .collect();
    // The compiler-visible circuit entry (the real `Field` body the xark compiler
    // lowers to MIR), compiled only under `cfg(xark)`. In test/host builds the same
    // `fn` name is instead the native-typed validator below — the two are
    // cfg-exclusive, so `mycircuit::<fn>(a, b, c)` needs no rename and never collides.
    let entry = quote! {
        #[cfg(xark)]
        #(#attrs)*
        #vis fn #fn_ident(#(#sig_params),*) {
            #(#stmts)*
        }
    };

    // In test/host builds the entry above is cfg'd out, leaving the circuit's own
    // `use`s (its `Private`/`Public` wrappers and gadget fns) unused. Emit a hidden,
    // never-called copy of the body so those imports stay used (no spurious warnings).
    let circuit_def_ident = format_ident!("__{}_circuit_def", fn_ident);
    let sig_params_def = sig_params.clone();
    let circuit_def = quote! {
        #[cfg(not(xark))]
        #[doc(hidden)]
        #[allow(dead_code, unused_imports, clippy::assign_op_pattern)]
        fn #circuit_def_ident(#(#sig_params_def),*) {
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
    // The native-typed validator replacing the entry `fn` in test/host builds: same
    // name, the entry's native parameter types in order, returning the check result.
    let host_params = params.iter().map(|p| {
        let (name, nty) = (&p.name, &p.native_ty);
        quote! { #name: #nty }
    });
    let host_ctor = params.iter().map(|p| &p.name);

    Ok(quote! {
        // Keep the custom cfg entirely inside an always-present, lint-scoped module.
        // A proc macro cannot register `cfg(xark)` in the downstream manifest, but
        // it can own the lint locally so circuit authors need no `[lints]` ceremony.
        // Only `unexpected_cfgs` is module-wide (the cfgs sit on items that contain
        // the author's body, so no tighter scope exists); other allows are pinned
        // to the exact generated construct that needs them.
        #[doc(hidden)]
        #[allow(unexpected_cfgs)]
        mod #module_ident {
            #[allow(unused_imports)]
            use super::*;

            #entry
            #circuit_def

            /// Native-typed validator for this circuit. In test/host builds the circuit
            /// function loads its built artifacts and checks the supplied inputs.
            #[cfg(not(xark))]
            #(#attrs)*
            pub fn #fn_ident(#(#host_params),*) -> ::core::result::Result<(), ::xark::__private::ProveError> {
                ::xark::__private::circuit(#fn_name_lit).check(#struct_name { #(#host_ctor),* })
            }

            /// Typed host inputs generated from the circuit entry signature.
            #[cfg(not(xark))]
            #[derive(Clone, Debug)]
            pub struct #struct_name {
                #(#field_defs,)*
            }

            // Keep the type name available to the unconditional re-export during a
            // circuit build; its host-only fields and impl are never needed there.
            #[cfg(xark)]
            #[doc(hidden)]
            pub struct #struct_name;

            #[cfg(not(xark))]
            impl ::xark::__private::ProveInputs for #struct_name {
                fn into_inputs(self) -> ::std::vec::Vec<(::std::string::String, ::std::string::String)> {
                    let mut out: ::std::vec::Vec<(::std::string::String, ::std::string::String)> =
                        ::std::vec::Vec::new();
                    #(#fanouts)*
                    out
                }
            }
        }

        #vis use #module_ident::#fn_ident;
        #vis use #module_ident::#struct_name;
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
    Err(syn::Error::new_spanned(
        ty,
        "#[circuit] parameters must be wrapped in `Private<..>` or `Public<..>`",
    ))
}

/// Map a native inner type to `(native struct-field type, circuit inner type, fanout)`.
/// Supported: `Field`, `[u8; N]`, `[Field; N]`, or a type implementing `NativeInput`.
fn map_inner(inner: &Type) -> syn::Result<(TokenStream2, TokenStream2, Fanout)> {
    if let Type::Path(tp) = inner
        && tp.path.segments.last().is_some_and(|s| s.ident == "Field")
    {
        // The host and circuit APIs use the same type. `Field` can represent the
        // entire scalar field and renders itself canonically at the prover boundary.
        return Ok((
            quote! { ::xark::Field },
            quote! { ::xark::Field },
            Fanout::FieldScalar,
        ));
    }
    // Native unsigned integers are first-class circuit witnesses: the `<Fn>Inputs`
    // field takes the native `uN` (fits `u128`, so no `String` needed), the circuit
    // body sees the same `uN` (the compiler range-checks it `< 2^N` on entry and
    // lowers its comparisons), and it fans out to one decimal leaf. Must precede the
    // gadget-type fallback, else `u64` would be treated as a `NativeInput` type.
    if let Type::Path(tp) = inner
        && let Some(seg) = tp.path.segments.last()
        && matches!(
            seg.ident.to_string().as_str(),
            "u8" | "u16" | "u32" | "u64" | "u128"
        )
    {
        return Ok((quote! { #inner }, quote! { #inner }, Fanout::UIntScalar));
    }
    if let Type::Array(arr) = inner
        && let Type::Path(elem) = &*arr.elem
    {
        if elem.path.segments.last().is_some_and(|s| s.ident == "u8") {
            let n = arr.len.clone();
            return Ok((
                quote! { [u8; #n] },
                quote! { [::xark::Field; #n] },
                Fanout::ByteArray(n),
            ));
        }
        if elem
            .path
            .segments
            .last()
            .is_some_and(|s| s.ident == "Field")
        {
            // A field-valued array (hash siblings, bignum limbs, …) has the same
            // type on the host and in the circuit.
            let n = arr.len.clone();
            return Ok((
                quote! { [::xark::Field; #n] },
                quote! { [::xark::Field; #n] },
                Fanout::FieldArray(n),
            ));
        }
    }
    // Fallback: any other named type is a transparent gadget type (`Fq`/`Point`)
    // implementing Xark's hidden `NativeInput`. Its `Native` associated type is the
    // struct field, and its `leaves` produce the compiler's flatten names. A type
    // that doesn't impl the trait is a compile error at the delegation site.
    if let Type::Path(_) = inner {
        return Ok((
            quote! { <#inner as ::xark::__private::NativeInput>::Native },
            quote! { #inner },
            Fanout::Native,
        ));
    }
    Err(syn::Error::new_spanned(
        inner,
        "unsupported #[circuit] parameter type; supported: `Field`, `[u8; N]`, \
         `[u8; 32]` (a SHA-256 digest), `[Field; N]`, or a gadget type \
         implementing `NativeInput`",
    ))
}

/// The `ProveInputs` fan-out statements for one parameter: push `(leaf-name,
/// decimal-value)` pairs whose names match the compiler's structural-flatten
/// names for the circuit type, in flatten order.
fn fanout_code(p: &CircuitParam) -> TokenStream2 {
    let name = &p.name;
    let name_lit = LitStr::new(&name.to_string(), name.span());
    match &p.fanout {
        Fanout::FieldScalar => quote! {
            out.push((
                ::std::string::String::from(#name_lit),
                self.#name.to_decimal(),
            ));
        },
        Fanout::UIntScalar => quote! {
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
        Fanout::FieldArray(n) => quote! {
            {
                let mut __i = 0usize;
                while __i < #n {
                    out.push((
                        ::std::format!("{}[{}]", #name_lit, __i),
                        self.#name[__i].to_decimal(),
                    ));
                    __i += 1;
                }
            }
        },
        // Transparent gadget type: delegate to `NativeInput::leaves`, which produces
        // the compiler's flatten names (`name.x.limbs[i]`, `name[i]`, …).
        Fanout::Native => {
            let ty = &p.circuit_ty;
            quote! {
                out.extend(
                    <#ty as ::xark::__private::NativeInput>::leaves(&self.#name, #name_lit),
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
/// circuit input by generating its `From<Self> for [Field; N]`, **in the compiler's
/// structural-flatten order**: fields in declaration order, arrays in index order,
/// bottoming out at `Field`. The compiler flattens the input type the same way, so
/// leaf `k` of the produced array is always leaf `k` of the input — making
/// host↔circuit layout agreement a mechanical guarantee, not discipline.
///
/// ```ignore
/// #[derive(Clone, Copy, CircuitInput)]
/// struct Digest { bits: [[Field; 32]; 8] }   // ⇒ impl From<Digest> for [Field; 256]
/// ```
///
/// Supported field types: `Field` and (nested) fixed arrays of `Field` with
/// concrete const-expression lengths. Generic types (including const generics)
/// are rejected; use named constants when a layout size deserves a name.
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
    let host_module = format_ident!("__xark_native_input_for_{}", name);
    if !input.generics.params.is_empty() {
        return Err(syn::Error::new_spanned(
            &input.generics,
            "#[derive(CircuitInput)] does not support generic types; use concrete named \
             constants for array lengths, or implement `From<Self> for [Field; N]` by hand.",
        ));
    }
    let data = match &input.data {
        Data::Struct(d) => d,
        _ => {
            return Err(syn::Error::new_spanned(
                name,
                "#[derive(CircuitInput)] only supports structs",
            ));
        }
    };

    let mut counts = Vec::new();
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
        counts.push(count);
        blocks.push(stmts);
    }
    let n = quote! { 0usize #( + (#counts) )* };

    // Host-side `NativeInput`: the native form IS this `Field`-composed struct itself
    // (built host-side with `Field` values — no `String` mirror), and `leaves` renders
    // each field to its decimal under the compiler's structural-flatten names, so a
    // `#[circuit]` param of this type binds by name exactly as a gadget input does.
    let mut leaf_stmts = Vec::new();
    for (i, field) in data.fields.iter().enumerate() {
        let (fname, access) = match &field.ident {
            Some(id) => (id.to_string(), quote! { native.#id }),
            None => {
                let idx = syn::Index::from(i);
                (i.to_string(), quote! { native.#idx })
            }
        };
        let field_prefix = quote! { std::format!("{}.{}", prefix, #fname) };
        leaf_stmts.push(circuit_leaves(&field.ty, &access, &field_prefix, 0)?);
    }

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

        // Scope the host-only cfg under an always-present module so downstream
        // crates do not need to register Xark's private cfg with check-cfg.
        #[doc(hidden)]
        #[allow(unexpected_cfgs, non_snake_case)]
        mod #host_module {
            #[allow(unused_imports)]
            use super::*;

            #[cfg(not(xark))]
            const _: () = {
                extern crate std;
                use std::string::String;
                use std::vec::Vec;
                #[automatically_derived]
                impl ::xark::__private::NativeInput for #name {
                    type Native = #name;
                    fn leaves(native: &Self::Native, prefix: &str) -> Vec<(String, String)> {
                        let mut __out = Vec::new();
                        #( #leaf_stmts )*
                        __out
                    }
                }
            };
        }
    })
}

/// Emit the flatten statements for one field/element `access` of type `ty`, returning
/// `(leaf-count expression, statements)`. Recurses through arrays; a `Field` is one leaf.
/// `depth` names the per-level loop variable so nested arrays don't collide.
fn walk_type(
    ty: &Type,
    access: &TokenStream2,
    depth: usize,
) -> syn::Result<(TokenStream2, TokenStream2)> {
    match ty {
        Type::Path(tp) if tp.path.segments.last().is_some_and(|s| s.ident == "Field") => {
            Ok((quote! { 1usize }, quote! { out[__i] = #access; __i += 1; }))
        }
        Type::Array(arr) => {
            let len = &arr.len;
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
            Ok((quote! { (#len) * (#inner_count) }, block))
        }
        other => Err(syn::Error::new_spanned(
            other,
            "#[derive(CircuitInput)] fields must be `Field` or fixed arrays of `Field` \
             (nesting allowed)",
        )),
    }
}

/// `#[derive(Transparent)]` — generate the host-side [`NativeInput`] fan-out for a
/// transparent circuit type, so the leaf-name / limb contract (which must match the
/// compiler's structural flatten) is generated once, not hand-duplicated per gadget.
///
/// Two shapes:
///  * a **leaf** field element `{ limbs: [Field; N] }` marked `#[transparent(bits = B)]`:
///    native form `[u8; N*B/8]` (big-endian), flattening to `<prefix>.limbs[i]`.
///  * a **composite** of transparent fields (e.g. `{ x: Fq, y: Fq }`): native form is
///    the fields' native bytes concatenated, recursing under `<prefix>.<field>`.
///
/// The generated impl is `#[cfg(not(xark))]` — `NativeInput` is host-only.
///
/// [`NativeInput`]: xark::__private::NativeInput
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
    let host_module = format_ident!("__xark_transparent_input_for_{}", name);
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
            ));
        }
    };

    let (native_ty, leaves_body) = if let Some(bits) = parse_transparent_bits(&input.attrs)? {
        // LEAF: `{ limbs: [Field; N] }`, native = big-endian `[u8; N*B/8]`.
        let n = leaf_limb_count(data)?;
        let bytes = n * (bits as usize) / 8;
        (
            quote! { [u8; #bytes] },
            quote! { ::xark::__private::limb_leaves(native, prefix, #n, #bits) },
        )
    } else {
        // COMPOSITE: native = concatenation of the fields' native bytes; recurse.
        let field_size = |fty: &Type| {
            quote! { ::core::mem::size_of::<<#fty as ::xark::__private::NativeInput>::Native>() }
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
                    let __chunk: &<#fty as ::xark::__private::NativeInput>::Native =
                        ::core::convert::TryFrom::try_from(&native[__start..__end]).unwrap();
                    __out.extend(<#fty as ::xark::__private::NativeInput>::leaves(
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

    // The runtime is re-exported privately by `xark`; keep the custom cfg inside
    // an always-present module so downstream crates need no lint configuration.
    Ok(quote! {
        #[doc(hidden)]
        #[allow(unexpected_cfgs, non_snake_case)]
        mod #host_module {
            #[allow(unused_imports)]
            use super::*;

            #[cfg(not(xark))]
            const _: () = {
                extern crate std;
                use std::string::String;
                use std::vec::Vec;
                #[automatically_derived]
                impl ::xark::__private::NativeInput for #name {
                    type Native = #native_ty;
                    fn leaves(native: &Self::Native, prefix: &str) -> Vec<(String, String)> {
                        #leaves_body
                    }
                }
            };
        }
    })
}

/// Emit `NativeInput::leaves` push statements for a `Field`-composed value `access` of
/// circuit type `ty`, whose flatten prefix is the `String` expression `prefix`. A `Field`
/// renders to its decimal via [`Field::to_decimal`]; arrays recurse under `prefix[i]`; a
/// nested `NativeInput` type delegates under its own `prefix`. `depth` names loop vars.
/// Used by `#[derive(CircuitInput)]` to build the host-side leaf fan-out.
fn circuit_leaves(
    ty: &Type,
    access: &TokenStream2,
    prefix: &TokenStream2,
    depth: usize,
) -> syn::Result<TokenStream2> {
    match ty {
        Type::Path(tp) if tp.path.segments.last().is_some_and(|s| s.ident == "Field") => {
            Ok(quote! { __out.push((#prefix, #access.to_decimal())); })
        }
        Type::Array(arr) => {
            let len = &arr.len;
            let kv = format_ident!("__k{depth}");
            let pv = format_ident!("__p{depth}");
            let inner = circuit_leaves(
                &arr.elem,
                &quote! { #access[#kv] },
                &quote! { std::format!("{}[{}]", #pv, #kv) },
                depth + 1,
            )?;
            Ok(quote! {
                {
                    let #pv = #prefix;
                    let mut #kv = 0usize;
                    while #kv < #len {
                        #inner
                        #kv += 1;
                    }
                }
            })
        }
        Type::Path(_) => Ok(quote! {
            __out.extend(<#ty as ::xark::__private::NativeInput>::leaves(&#access, &#prefix));
        }),
        other => Err(syn::Error::new_spanned(
            other,
            "#[derive(CircuitInput)] fields must be `Field`, fixed arrays of them, \
             or a type implementing `NativeInput`",
        )),
    }
}

/// A `usize` from the integer-literal limb count required by `Transparent`.
fn eval_usize_lit(e: &Expr) -> syn::Result<usize> {
    match e {
        Expr::Lit(ExprLit {
            lit: Lit::Int(li), ..
        }) => li.base10_parse::<usize>(),
        other => Err(syn::Error::new_spanned(
            other,
            "#[derive(Transparent)] limb-array lengths must be integer literals",
        )),
    }
}
