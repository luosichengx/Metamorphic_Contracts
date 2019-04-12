/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

//! A crate implementing ["Design by Contract"][dbc] via procedural macros.
//!
//! This crate is heavily inspired by the [`libhoare`] compiler plugin.
//!
//! The main use of this crate is to annotate functions and methods using
//! "contracts" in the form of [*pre-conditions*][precond],
//! [*post-conditions*][postcond] and [*invariants*][invariant].
//!
//! Each "contract" annotation that is violated will cause an assertion failure.
//!
//! The attributes use "function call form" and can contain 1 or more conditions
//! to check.
//! If the last argument to an attribute is a string constant it will be inserted
//! into the assertion message.
//!
//! ## Example
//!
//! ```rust
//! # use contracts::*;
//! #[pre(x > 0, "x must be in the valid input range")]
//! #[post(ret.map(|s| s * s == x).unwrap_or(true))]
//! fn integer_sqrt(x: u64) -> Option<u64> {
//!    // ...
//! # unimplemented!()
//! }
//! ```
//!
//! ## Feature flags
//!
//! Following feature flags are available:
//!  - `disable_contracts` - disables all checks and assertions.
//!  - `override_debug` - changes all contracts (except `test_` ones) into `debug_*` versions
//!  - `override_log` - changes all contracts (except `test_` ones) into a `log::error!()` call if the condition is violated.
//!    No abortion happens.
//!
//! [dbc]: https://en.wikipedia.org/wiki/Design_by_contract
//! [`libhoare`]: https://github.com/nrc/libhoare
//! [precond]: attr.pre.html
//! [postcond]: attr.post.html
//! [invariant]: attr.invariant.html

extern crate proc_macro;

use proc_macro::TokenStream;
use syn::parse::Parser;
use syn::punctuated::Punctuated;
use syn::{
    Block, Expr, ExprLit, FnArg, ImplItem, ImplItemMethod, Item, ItemFn, ItemImpl, Lit, ReturnType,
};
use syn::{ItemTrait, Pat, Token, TraitItem, TraitItemMethod};

//
//
// Utiliy types
//
//

/// Checking-mode of a contract.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum ContractMode {
    /// Always check contract
    Always,
    /// Never check contract
    Disabled,
    /// Check contract only in debug builds
    Debug,
    /// Check contract only in `#[cfg(test)]` configurations
    Test,
    /// Check the contract and print information upon violation, but don't abort the program.
    LogOnly,
}

impl ContractMode {
    /// Return the prefix of attributes of `self` mode.
    fn name(self) -> Option<&'static str> {
        match self {
            ContractMode::Always => Some(""),
            ContractMode::Disabled => None,
            ContractMode::Debug => Some("debug_"),
            ContractMode::Test => Some("test_"),
            ContractMode::LogOnly => None,
        }
    }
}

/// Computes the contract type based on feature flags.
fn final_mode(mode: ContractMode) -> ContractMode {
    // disabled ones can't be "forced", test ones should stay test, no matter what.
    if mode == ContractMode::Disabled || mode == ContractMode::Test {
        return mode;
    }

    if cfg!(feature = "disable_contracts") {
        ContractMode::Disabled
    } else if cfg!(feature = "override_debug") {
        // log is "weaker" than debug, so keep log
        if mode == ContractMode::LogOnly {
            mode
        } else {
            ContractMode::Debug
        }
    } else if cfg!(feature = "override_log") {
        ContractMode::LogOnly
    } else {
        mode
    }
}

//
//
// contract attributes
//
//

/// Pre-conditions are checked before the function body is run.
///
/// ## Example
///
/// ```rust
/// # use contracts::*;
/// #[pre(elems.len() >= 1)]
/// fn max<T: Ord + Copy>(elems: &[T]) -> T {
///    // ...
/// # unimplemented!()
/// }
/// ```
#[proc_macro_attribute]
pub fn pre(attr: TokenStream, toks: TokenStream) -> TokenStream {
    let mode = final_mode(ContractMode::Always);
    impl_pre(mode, attr, toks)
}

/// Same as [`pre`], but uses `debug_assert!`.
///
/// [`pre`]: attr.pre.html
#[proc_macro_attribute]
pub fn debug_pre(attr: TokenStream, toks: TokenStream) -> TokenStream {
    let mode = final_mode(ContractMode::Debug);
    impl_pre(mode, attr, toks)
}

/// Same as [`pre`], but is only enabled in `#[cfg(test)]` environments.
///
/// [`pre`]: attr.pre.html
#[proc_macro_attribute]
pub fn test_pre(attr: TokenStream, toks: TokenStream) -> TokenStream {
    let mode = final_mode(ContractMode::Test);
    impl_pre(mode, attr, toks)
}

fn impl_pre(mode: ContractMode, attr: TokenStream, toks: TokenStream) -> TokenStream {
    let (conds, desc) = parse_attributes(attr);

    let item: ItemFn = syn::parse_macro_input!(toks as ItemFn);
    let fn_name = item.ident.to_string();

    let desc = if let Some(desc) = desc {
        format!("Pre-condition of {} violated - {:?}", fn_name, desc)
    } else {
        format!("Pre-condition of {} violated", fn_name)
    };

    let pre = attributes_to_asserts(mode, conds, desc);
    let post = quote::quote! {};

    impl_fn_checks(item, pre, post)
}

/// Post-conditions are checked after the function body is run.
///
/// The result of the function call is accessible in conditions using the `ret` identifier.
///
/// ## Example
///
/// ```rust
/// # use contracts::*;
/// #[post(ret > x)]
/// fn incr(x: usize) -> usize {
///     x + 1
/// }
/// ```
#[proc_macro_attribute]
pub fn post(attr: TokenStream, toks: TokenStream) -> TokenStream {
    let mode = final_mode(ContractMode::Always);
    impl_post(mode, attr, toks)
}

/// Same as [`post`], but uses `debug_assert!`.
///
/// [`post`]: attr.post.html
#[proc_macro_attribute]
pub fn debug_post(attr: TokenStream, toks: TokenStream) -> TokenStream {
    let mode = final_mode(ContractMode::Debug);
    impl_post(mode, attr, toks)
}

/// Same as [`post`], but is only enabled in `#[cfg(test)]` environments.
///
/// [`post`]: attr.post.html
#[proc_macro_attribute]
pub fn test_post(attr: TokenStream, toks: TokenStream) -> TokenStream {
    let mode = final_mode(ContractMode::Test);
    impl_post(mode, attr, toks)
}

fn impl_post(mode: ContractMode, attr: TokenStream, toks: TokenStream) -> TokenStream {
    let (conds, desc) = parse_attributes(attr);

    let item: ItemFn = syn::parse_macro_input!(toks as ItemFn);
    let fn_name = item.ident.to_string();

    let desc = if let Some(desc) = desc {
        format!("Post-condition of {} violated - {:?}", fn_name, desc)
    } else {
        format!("Post-condition of {} violated", fn_name)
    };

    let pre = quote::quote! {};
    let post = attributes_to_asserts(mode, conds, desc);

    impl_fn_checks(item, pre, post)
}

/// Invariants are conditions that have to be maintained at the "interface boundaries".
///
/// Invariants can be supplied to functions (and "methods"), as well as on `impl` blocks.
///
/// When applied to an `impl`-block all methods taking `self` (either by value or reference)
/// will be checked for the invariant.
///
/// ## Example
///
/// On a function:
///
/// ```rust
/// # use contracts::*;
/// /// Update `num` to the next bigger even number.
/// #[invariant(*num % 2 == 0)]
/// fn advance_even(num: &mut usize) {
///     *num += 2;
/// }
/// ```
///
/// On an `impl`-block:
///
/// ```rust
/// # use contracts::*;
/// struct EvenAdder {
///     count: usize,
/// }
///
/// #[invariant(self.count % 2 == 0)]
/// impl EvenAdder {
///     pub fn tell(&self) -> usize {
///         self.count
///     }
///
///     pub fn advance(&mut self) {
///         self.count += 2;
///     }
/// }
/// ```
#[proc_macro_attribute]
pub fn invariant(attr: TokenStream, toks: TokenStream) -> TokenStream {
    // Invariant attributes might apply to `impl` blocks as well, where the same
    // level is simply replicated on all methods.
    // Function expansions will resolve the actual mode themselves, so the actual
    // "raw" mode is passed here
    //
    // TODO: update comment for traits
    let mode = ContractMode::Always;
    impl_invariant(mode, attr, toks)
}

/// Same as [`invariant`], but uses `debug_assert!`.
///
/// [`invariant`]: attr.invariant.html
#[proc_macro_attribute]
pub fn debug_invariant(attr: TokenStream, toks: TokenStream) -> TokenStream {
    let mode = ContractMode::Debug;
    impl_invariant(mode, attr, toks)
}

/// Same as [`invariant`], but is only enabled in `#[cfg(test)]` environments.
///
/// [`invariant`]: attr.invariant.html
#[proc_macro_attribute]
pub fn test_invariant(attr: TokenStream, toks: TokenStream) -> TokenStream {
    let mode = ContractMode::Test;
    impl_invariant(mode, attr, toks)
}

fn impl_invariant(mode: ContractMode, attr: TokenStream, toks: TokenStream) -> TokenStream {
    let item: Item = syn::parse_macro_input!(toks as Item);

    let name = mode.name().unwrap().to_string() + "invariant";

    match item {
        Item::Fn(fn_) => impl_invariant_fn(mode, attr, fn_),
        Item::Impl(impl_) => impl_impl_invariant(mode, attr, impl_),
        _ => unimplemented!(
            "The #[{}] attribute only works on functions and impl-blocks.",
            name
        ),
    }
}

fn impl_invariant_fn(mode: ContractMode, attr: TokenStream, fn_: ItemFn) -> TokenStream {
    let mode = final_mode(mode);

    let (conds, desc) = parse_attributes(attr);

    let fn_name = fn_.ident.to_string();

    let desc = if let Some(desc) = desc {
        format!("Invariant of {} violated - {:?}", fn_name, desc)
    } else {
        format!("Invariant of {} violated", fn_name)
    };

    let pre = attributes_to_asserts(mode, conds, desc);
    let post = pre.clone();

    impl_fn_checks(fn_, pre, post)
}

//
//
// Trait stuff
//
//

/// A "contract_trait" is a trait which ensures all implementors respect all provided contracts.
///
/// When this attribute is applied to a `trait` definition, the trait gets modified so that all
/// invocations of methods are checked.
///
/// When this attribute is applied to an `impl Trait for Type` item, the implementation gets
/// modified so it matches the trait definition.
///
/// **When the `#[contract_trait]` is not applied to either the trait or an `impl` it will cause
/// compile errors**.
///
/// ## Example
///
/// ```rust
/// # use contracts::*;
/// #[contract_trait]
/// trait MyRandom {
///     #[pre(min < max)]
///     #[post(min <= ret, ret <= max)]
///     fn gen(min: f64, max: f64) -> f64;
/// }
///
/// // Not a very useful random number generator, but a valid one!
/// struct AlwaysMax;
///
/// #[contract_trait]
/// impl MyRandom for AlwaysMax {
///     fn gen(min: f64, max: f64) -> f64 {
///         max
///     }
/// }
/// ```
#[proc_macro_attribute]
pub fn contract_trait(attrs: TokenStream, toks: TokenStream) -> TokenStream {
    let item: Item = syn::parse_macro_input!(toks);

    match item {
        Item::Trait(trait_) => contract_trait_item_trait(attrs, trait_),
        Item::Impl(impl_) => {
            assert!(
                impl_.trait_.is_some(),
                "#[contract_trait] can only be applied to `trait` and `impl ... for` items"
            );
            contract_trait_item_impl(attrs, impl_)
        }
        _ => panic!("#[contract_trait] can only be applied to `trait` and `impl ... for` items"),
    }
}

/// Name used for the "re-routed" method.
fn contract_method_impl_name(name: &str) -> String {
    format!("__contracts_impl_{}", name)
}

/// Modifies a trait item in a way that it includes contracts.
fn contract_trait_item_trait(_attrs: TokenStream, mut trait_: ItemTrait) -> TokenStream {
    /// Just rename the method to have an internal, generated name.
    fn create_method_rename(method: &TraitItemMethod) -> TraitItemMethod {
        let mut m: TraitItemMethod = (*method).clone();

        // transform method
        {
            // remove all attributes and rename
            let name = m.sig.ident.to_string();

            let new_name = contract_method_impl_name(&name);

            m.attrs.clear();
            m.sig.ident = syn::Ident::new(&new_name, m.sig.ident.span());
        }

        m
    }

    /// Create a wrapper function which has a default implementation and includes contracts.
    ///
    /// This new function forwards the call to the actual implementation.
    fn create_method_wrapper(method: &TraitItemMethod) -> TraitItemMethod {
        struct ArgInfo {
            call_toks: proc_macro2::TokenStream,
        }

        // Calculate name and pattern tokens
        fn arg_pat_info(pat: &Pat) -> ArgInfo {
            match pat {
                Pat::Ident(ident) => {
                    let toks = quote::quote! {
                        #ident
                    };
                    ArgInfo { call_toks: toks }
                }
                Pat::Tuple(tup) => {
                    let infos = tup.front.iter().map(arg_pat_info);

                    let toks = {
                        let mut toks = proc_macro2::TokenStream::new();

                        for info in infos {
                            toks.extend(info.call_toks);
                            toks.extend(quote::quote!(,));
                        }

                        toks
                    };

                    ArgInfo {
                        call_toks: quote::quote!((#toks)),
                    }
                }
                Pat::TupleStruct(_tup) => unimplemented!(),
                p => panic!("Unsupported pattern type: {:?}", p),
            }
        }

        let mut m: TraitItemMethod = (*method).clone();

        let argument_data = m
            .sig
            .decl
            .inputs
            .clone()
            .into_iter()
            .map(|t: FnArg| match &t {
                FnArg::SelfRef(_) | FnArg::SelfValue(_) => quote::quote!(self),
                FnArg::Captured(c) => {
                    let info = arg_pat_info(&c.pat);

                    info.call_toks
                }
                FnArg::Inferred(inf) => unimplemented!("Inferred pattern: {:?}", inf),
                FnArg::Ignored(_ty) => {
                    unimplemented!("Ignored patterns are not allowed in contract trait methods");
                }
            })
            .collect::<Vec<_>>();

        let arguments = {
            let mut toks = proc_macro2::TokenStream::new();

            for arg in argument_data {
                toks.extend(arg);
                toks.extend(quote::quote!(,));
            }

            toks
        };

        let body: TokenStream = {
            let name = contract_method_impl_name(&m.sig.ident.to_string());
            let name = syn::Ident::new(&name, m.sig.ident.span());

            let toks = quote::quote! {
                {
                    Self::#name(#arguments)
                }
            };

            toks.into()
        };

        {
            let block: syn::Block = syn::parse_macro_input::parse(body).unwrap();
            m.default = Some(block);
            m.semi_token = None;
        }

        m
    }

    // create method wrappers and renamed items
    let funcs = trait_
        .items
        .iter()
        .filter_map(|item| {
            if let TraitItem::Method(m) = item {
                let rename = create_method_rename(m);
                let wrapper = create_method_wrapper(m);

                Some(vec![TraitItem::Method(rename), TraitItem::Method(wrapper)])
            } else {
                None
            }
        })
        .flatten()
        .collect::<Vec<_>>();

    // remove all previous methods
    trait_.items = trait_
        .items
        .into_iter()
        .filter(|item| {
            if let TraitItem::Method(_) = item {
                false
            } else {
                true
            }
        })
        .collect();

    // add back new methods
    trait_.items.extend(funcs);

    let toks = quote::quote! {
        #trait_
    };

    toks.into()
}

/// Rename all methods inside an `impl` to use the "internal implementation" name.
fn contract_trait_item_impl(_attrs: TokenStream, impl_: ItemImpl) -> TokenStream {
    let new_impl = {
        let mut impl_: ItemImpl = impl_.clone();

        impl_.items.iter_mut().for_each(|it| {
            if let ImplItem::Method(method) = it {
                let new_name = contract_method_impl_name(&method.sig.ident.to_string());
                let new_ident = syn::Ident::new(&new_name, method.sig.ident.span());

                method.sig.ident = new_ident;
            }
        });

        impl_
    };

    let toks = quote::quote! {
        #new_impl
    };

    toks.into()
}

//
//
// implementation helpers
//
//

/// Parse attributes into a list of expression and an optional description of the assert
fn parse_attributes(attrs: TokenStream) -> (Vec<Expr>, Option<String>) {
    let mut conds: Punctuated<Expr, Token![,]> = {
        let tokens = attrs;

        let parser = Punctuated::<Expr, Token![,]>::parse_separated_nonempty;

        let terminated = parser.parse(tokens.clone());

        if let Ok(res) = terminated {
            res
        } else {
            let parser = Punctuated::<Expr, Token![,]>::parse_terminated;

            parser.parse(tokens).unwrap()
        }
    };

    let desc = conds
        .last()
        .map(|x| {
            let expr = *x.value();

            if let Expr::Lit(ExprLit {
                lit: Lit::Str(str), ..
            }) = expr
            {
                Some(str.value())
            } else {
                None
            }
        })
        .unwrap_or(None);

    if desc.is_some() {
        conds.pop();
    }

    let exprs = conds.into_iter().map(|e| e).collect();

    (exprs, desc)
}

/// Create the token-stream for assert statements.
fn attributes_to_asserts(
    mode: ContractMode,
    exprs: Vec<Expr>,
    desc: String,
) -> proc_macro2::TokenStream {
    let mut stream = proc_macro2::TokenStream::new();

    let generate = |expr: &Expr, desc: &str| {
        let format_args = quote::quote! {
            concat!(concat!(#desc, ": "), stringify!(#expr))
        };

        match mode {
            ContractMode::Always => {
                quote::quote! {
                    assert!(#expr, #format_args);
                }
            }
            ContractMode::Disabled => {
                quote::quote! {}
            }
            ContractMode::Debug => {
                quote::quote! {
                    debug_assert!(#expr, #format_args);
                }
            }
            ContractMode::Test => {
                quote::quote! {
                    #[cfg(test)]
                    {
                        assert!(#expr, #format_args);
                    }
                }
            }
            ContractMode::LogOnly => {
                quote::quote! {
                    if !(#expr) {
                        log::error!(#format_args);
                    }
                }
            }
        }
    };

    for expr in exprs {
        stream.extend(generate(&expr, &desc));
        /*
        stream.extend(quote::quote! {
            assert!(#expr, concat!(concat!(#desc, ": "), stringify!(#expr)));
        });
        */
    }

    stream
}

/// Generate the token-stream for the new function implementation
fn impl_fn_checks(
    mut fn_def: ItemFn,
    pre: proc_macro2::TokenStream,
    post: proc_macro2::TokenStream,
) -> TokenStream {
    let block = fn_def.block.clone();

    let ret_ty = if let ReturnType::Type(_, ty) = &fn_def.decl.output {
        quote::quote! {
            #ty
        }
    } else {
        quote::quote! { () }
    };

    let new_block = quote::quote! {

        {
            #pre

            let ret: #ret_ty = {
                #block
            };

            #post

            ret
        }

    }
    .into();

    fn_def.block = Box::new(syn::parse_macro_input!(new_block as Block));

    let res = quote::quote! {
        #fn_def
    };

    res.into()
}

/// Generate the token-stream for an `impl` block with a "global" invariant.
fn impl_impl_invariant(
    mode: ContractMode,
    invariant: TokenStream,
    mut impl_def: ItemImpl,
) -> TokenStream {
    // all that is done is prefix all the function definitions with
    // the invariant attribute.
    // The following expansion of the attributes will then implement the invariant
    // just like it's done for functions.

    // The mode received is "raw", so it can't be "Disabled" or "LogOnly"
    // but it can't hurt to deal with it anyway.
    let name = match mode.name() {
        Some(n) => n.to_string() + "invariant",
        None => {
            return quote::quote!( #impl_def ).into();
        }
    };

    let invariant_ident = syn::Ident::new(&name, proc_macro2::Span::call_site());

    let invariant: proc_macro2::TokenStream = invariant.into();

    fn method_uses_self(method: &ImplItemMethod) -> bool {
        let inputs = &method.sig.decl.inputs;

        if !inputs.is_empty() {
            match inputs[0] {
                FnArg::SelfValue(_) | FnArg::SelfRef(_) => true,
                _ => false,
            }
        } else {
            false
        }
    }

    for item in &mut impl_def.items {
        if let ImplItem::Method(method) = item {
            // only implement invariants for methods that take `self`
            if !method_uses_self(method) {
                continue;
            }

            let method_toks = quote::quote! {
                #[#invariant_ident(#invariant)]
                #method
            }
            .into();

            let met = syn::parse_macro_input!(method_toks as ImplItemMethod);

            *method = met;
        }
    }

    let toks = quote::quote! {
        #impl_def
    };
    toks.into()
}
