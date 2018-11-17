//! lru-cache-macros
//! ================
//!
//! An attribute procedural macro to automatically cache the result of a function given a set of inputs.
//!
//! # Example:
//!
//! ```rust
//! use lru_cache_macros::lru_cache;
//!
//! #[lru_cache(20)]
//! fn fib(x: u32) -> u64 {
//!     println!("{:?}", x);
//!     if x <= 1 {
//!         1
//!     } else {
//!         fib(x - 1) + fib(x - 2)
//!     }
//! }
//!
//! #[test]
//! fn test_fib() {
//!     assert_eq!(fib(19), 6765);
//! }
//! ```
//!
//! The above example only calls `fib` twenty times, with the values from 0 to 19. All intermediate
//! results because of the recursion hit the cache.
//!
//! # Usage:
//!
//! Simply place `#[lru_cache([size])]` above your function. The function must obey a few properties
//! to use lru_cache:
//!
//! * All arguments and return values must implement `Clone`.
//! * The function may not take `self` in any form.
//! * Reference arguments are not supported.
//!
//! The macro will use the LruCache at `::lru_cache::LruCache`. This may be made configurable in the future.
//!
//! The `LruCache` type used must accept two generic parameters `<Args, Return>` and must support methods
//! `get_mut(&K)` and `insert(K, V)`. The `lru-cache` crate meets these requirements.
//!
//! # Details
//!
//! The above example will generate the following code:
//!
//! ```rust
//! fn __lru_base_fib(x: u32) -> u64 {
//!     if x <= 1 { 1 } else { fib(x - 1) + fib(x - 2) }
//! }
//! fn fib(x: u32) -> u64 {
//!     static mut cache: Option<::lru_cache::LruCache<(u32,), u64>> = None;
//!     unsafe {
//!         if cache.is_none() {
//!             cache = Some(::lru_cache::LruCache::new(20usize));
//!         }
//!     }
//!     let mut cache_ref = unsafe { cache.as_mut().unwrap() };
//!     let cloned_args = (x.clone(),);
//!     let stored_result = cache_ref.get_mut(&cloned_args);
//!     if let Some(stored_result) = stored_result {
//!         *stored_result
//!     } else {
//!         let ret = __lru_base_fib(x);
//!         cache_ref.insert(cloned_args, ret);
//!         ret
//!     }
//! }
//! ```
//!
//! Note that the current implementation is not thread safe. A mutex may be supported in the future.


#![feature(extern_crate_item_prelude)]
#![feature(proc_macro_diagnostic)]
#![recursion_limit="128"]
extern crate proc_macro;

use proc_macro::TokenStream;
use syn;
use syn::{Token, parse_quote};
use syn::spanned::Spanned;
use syn::punctuated::Punctuated;
use quote::quote;
use proc_macro2;

#[proc_macro_attribute]
pub fn lru_cache(attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut original_fn: syn::ItemFn = syn::parse(item.clone()).unwrap();
    let mut new_fn = original_fn.clone();

    let cache_size = get_lru_size(attr);
    if cache_size.is_none() {
        return item;
    }
    let cache_size = cache_size.unwrap();

    let return_type =
        if let syn::ReturnType::Type(_, ref ty) = original_fn.decl.output {
            Some(ty.clone())
        } else {

            original_fn.ident.span().unstable()
                .error("There's no point of caching the output of a function that has no output")
                .emit();
            return item;
        };

    let new_name = format!("__lru_base_{}", original_fn.ident.to_string());
    original_fn.ident = syn::Ident::new(&new_name[..], original_fn.ident.span());

    let result = get_args_and_types(&original_fn);
    let call_args;
    let types;
    if let Some((args_inner, types_inner)) = result {
        call_args = args_inner;
        types = types_inner;
    } else {
        return item;
    }

    let cloned_args = make_cloned_args_tuple(&call_args);

    let fn_path = path_from_ident(original_fn.ident.clone());

    let fn_call = syn::ExprCall {
        attrs: Vec::new(),
        paren_token: syn::token::Paren { span: proc_macro2::Span::call_site() },
        args: call_args.clone(),
        func: Box::new(fn_path)
    };

    let tuple_type = syn::TypeTuple {
        paren_token: syn::token::Paren { span: proc_macro2::Span::call_site() },
        elems: types,
    };

    let lru_body: syn::Block = parse_quote! {
        {
            static mut cache: Option<::lru_cache::LruCache<#tuple_type, #return_type>> = None;
            unsafe {
                if cache.is_none() {
                    cache = Some(::lru_cache::LruCache::new(#cache_size));
                }
            }
            let mut cache_ref = unsafe { cache.as_mut().unwrap() };
            let cloned_args = #cloned_args;

            let stored_result = cache_ref.get_mut(&cloned_args);
            if let Some(stored_result) = stored_result {
                *stored_result
            } else {
                let ret = #fn_call;
                cache_ref.insert(cloned_args, ret);
                ret
            }
        }
    };

    new_fn.block = Box::new(lru_body);
    let out = quote! {
        #original_fn

        #new_fn
    };
    out.into()
}

fn path_from_ident(ident: syn::Ident) -> syn::Expr {
    let mut segments: Punctuated<_, Token![::]> = Punctuated::new();
    segments.push(syn::PathSegment { ident: ident, arguments: syn::PathArguments::None });
    syn::Expr::Path(syn::ExprPath { attrs: Vec::new(), qself: None, path: syn::Path { leading_colon: None, segments: segments} })
}

fn get_lru_size(attr: TokenStream) -> Option<usize> {
    let value: Result<syn::LitInt, _> = syn::parse(attr.clone());

    if let Ok(val) = value {
        Some(val.value() as usize)
    } else {
        proc_macro2::Span::call_site().unstable()
            .error("The lru_cache macro must specify a maximum cache size as an argument")
            .emit();
        None
    }
}

fn make_cloned_args_tuple(args: &Punctuated<syn::Expr, Token![,]>) -> syn::ExprTuple {
    let mut cloned_args = Punctuated::<_, Token![,]>::new();
    for arg in args {
        let call = syn::ExprMethodCall {
            attrs: Vec::new(),
            receiver: Box::new(arg.clone()),
            dot_token: syn::token::Dot { spans: [arg.span(); 1] },
            method: syn::Ident::new("clone", proc_macro2::Span::call_site()),
            turbofish: None,
            paren_token: syn::token::Paren { span: proc_macro2::Span::call_site() },
            args: Punctuated::new(),
        };
        cloned_args.push(syn::Expr::MethodCall(call));
    }
    syn::ExprTuple {
        attrs: Vec::new(),
        paren_token: syn::token::Paren { span: proc_macro2::Span::call_site() },
        elems: cloned_args,
    }
}

fn get_args_and_types(f: &syn::ItemFn) -> Option<(Punctuated<syn::Expr, Token![,]>, Punctuated<syn::Type, Token![,]>)> {
    let mut call_args = Punctuated::<_, Token![,]>::new();
    let mut types = Punctuated::<_, Token![,]>::new();
    for input in &f.decl.inputs {
        match input {
            syn::FnArg::SelfValue(p) => {
                p.span().unstable()
                    .error("`self` arguments are currently unsupported by lru_cache")
                    .emit();
                return None;
            }
            syn::FnArg::SelfRef(p) => {
                p.span().unstable()
                    .error("`&self` arguments are currently unsupported by lru_cache")
                    .emit();
                return None;
            }
            syn::FnArg::Captured(p) => {
                let mut segments: syn::punctuated::Punctuated<_, Token![::]> = syn::punctuated::Punctuated::new();
                if let syn::Pat::Ident(ref x) = p.pat {
                    if let Some(m) = x.mutability {
                        m.span.unstable()
                            .error("`mut` arguments are not supported with lru_cache as this could lead to incorrect results being stored")
                            .emit();
                        return None;
                    }
                    segments.push(syn::PathSegment { ident: x.ident.clone(), arguments: syn::PathArguments::None });
                }
                types.push(p.ty.clone());
                call_args.push(syn::Expr::Path(syn::ExprPath { attrs: Vec::new(), qself: None, path: syn::Path { leading_colon: None, segments } }));
            },
            syn::FnArg::Inferred(p) => {
                p.span().unstable()
                    .error("inferred arguments are currently unsupported by lru_cache")
                    .emit();
                return None;
            }
            syn::FnArg::Ignored(p) => {
                p.span().unstable()
                    .error("ignored arguments are currently unsupported by lru_cache")
                    .emit();
                return None;
            }
        }
    }

    if types.len() == 1 {
        types.push_punct(syn::token::Comma { spans: [proc_macro2::Span::call_site(); 1] })
    }

    Some((call_args, types))
}