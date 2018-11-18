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
//! assert_eq!(fib(19), 6765);
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
//!
//! The macro will use the LruCache at `::lru_cache::LruCache` by default. This can be changed by
//! setting the `cache_type` config variable as shown in the configuration section.
//!
//! The `LruCache` type used must accept two generic parameters `<Args, Return>` and must support methods
//! `get_mut(&K)` and `insert(K, V)`. The `lru-cache` crate meets these requirements.
//!
//! Currently, this crate only works on nightly rust. However, once the 2018 edition stabilizes as well as the
//! procedural macro diagnostic interface, it should be able to run on stable.
//!
//! # Configuration:
//!
//! The lru_cache macro can be configured by adding additional attributes under `#[lru_cache(size)]`.
//!
//! All configuration attributes take the form `#[lru_config(...)]`. The available attributes are:
//!
//! * `#[lru_config(cache_type = ...)]`
//!     This allows the cache type used internally to be changed. The default is equivalent to
//!     `#[lru_config(cache_type = ::lru_cache::LruCache)]`
//!
//! # Details
//!
//! The created cache resides in thread-local storage so that multiple threads may simultaneously call
//! the decorated function, but will not share cached results with each other.
//!
//! The above example will generate the following code:
//!
//! ```rust
//! fn __lru_base_fib(x: u32) -> u64 {
//!     if x <= 1 { 1 } else { fib(x - 1) + fib(x - 2) }
//! }
//! fn fib(x: u32) -> u64 {
//!     use std::cell::UnsafeCell;
//!     use std::thread_local;
//!
//!     thread_local!(
//!          static cache: UnsafeCell<::lru_cache::LruCache<(u32,), u64>> =
//!              UnsafeCell::new(::lru_cache::LruCache::new(20usize));
//!     );
//!
//!     cache.with(|c|
//!         {
//!             let mut cache_ref = unsafe { &mut *c.get() };
//!             let cloned_args = (x.clone(),);
//!             let stored_result = cache_ref.get_mut(&cloned_args);
//!             if let Some(stored_result) = stored_result {
//!                 stored_result.clone()
//!             } else {
//!                 let ret = __lru_base_fib(x);
//!                 cache_ref.insert(cloned_args, ret);
//!                 ret
//!             }
//!         })
//! }
//! ```


#![feature(extern_crate_item_prelude)]
#![feature(proc_macro_diagnostic)]
#![recursion_limit="128"]
extern crate proc_macro;

use std::result;

use proc_macro::TokenStream;
use syn;
use syn::{Token, parse_quote};
use syn::spanned::Spanned;
use syn::punctuated::Punctuated;
use quote::quote;
use proc_macro2;

mod config;
mod error;

use self::error::{DiagnosticError, Result};

#[proc_macro_attribute]
pub fn lru_cache(attr: TokenStream, item: TokenStream) -> TokenStream {
    match lru_cache_impl(attr, item.clone()) {
        Ok(tokens) => return tokens,
        Err(e) => {
            e.emit();
            return item;
        }
    }
}

fn lru_cache_impl(attr: TokenStream, item: TokenStream) -> Result<TokenStream> {
    let mut original_fn: syn::ItemFn = match syn::parse(item.clone()) {
        Ok(ast) => ast,
        Err(e) => {
            let diag = proc_macro2::Span::call_site().unstable()
                .error("lru_cache may only be used on functions");
            return Err(DiagnosticError::new_with_syn_error(diag, e));
        }
    };

    let macro_config;
    {
        let attribs = &original_fn.attrs[..];
        println!("{:?}", attribs);
        macro_config = config::Config::parse_from_attributes(attribs)?;
    }
    original_fn.attrs = Vec::new();

    let mut new_fn = original_fn.clone();

    let cache_size = get_lru_size(attr)?;

    let return_type =
        if let syn::ReturnType::Type(_, ref ty) = original_fn.decl.output {
            Some(ty.clone())
        } else {
            let diag = original_fn.ident.span().unstable()
                .error("There's no point of caching the output of a function that has no output");
            return Err(DiagnosticError::new(diag));
        };

    let new_name = format!("__lru_base_{}", original_fn.ident.to_string());
    original_fn.ident = syn::Ident::new(&new_name[..], original_fn.ident.span());

    let (call_args, types) = get_args_and_types(&original_fn)?;

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

    let cache_type = macro_config.cache_type;

    let lru_body: syn::Block = parse_quote! {
        {
            use std::cell::UnsafeCell;
            use std::thread_local;
            thread_local!(
                // We use `UnsafeCell` here to allow recursion. Since it is in the TLS, it should
                // not introduce any actual unsafety.
                static cache: UnsafeCell<#cache_type<#tuple_type, #return_type>> =
                    UnsafeCell::new(#cache_type::new(#cache_size));
            );
            cache.with(|c| {
                let mut cache_ref = unsafe { &mut *c.get() };
                let cloned_args = #cloned_args;

                let stored_result = cache_ref.get_mut(&cloned_args);
                if let Some(stored_result) = stored_result {
                    stored_result.clone()
                } else {
                    let ret = #fn_call;
                    cache_ref.insert(cloned_args, ret);
                    ret
                }
            })
        }
    };

    new_fn.block = Box::new(lru_body);
    let out = quote! {
        #original_fn

        #new_fn
    };
    Ok(out.into())
}

fn path_from_ident(ident: syn::Ident) -> syn::Expr {
    let mut segments: Punctuated<_, Token![::]> = Punctuated::new();
    segments.push(syn::PathSegment { ident: ident, arguments: syn::PathArguments::None });
    syn::Expr::Path(syn::ExprPath { attrs: Vec::new(), qself: None, path: syn::Path { leading_colon: None, segments: segments} })
}

fn get_lru_size(attr: TokenStream) -> Result<usize> {
    let value: result::Result<syn::LitInt, _> = syn::parse(attr.clone());

    if let Ok(val) = value {
        Ok(val.value() as usize)
    } else {
        let diag = proc_macro2::Span::call_site().unstable()
            .error("The lru_cache macro must specify a maximum cache size as an argument");
        Err(DiagnosticError::new_with_syn_error(diag, value.err().unwrap()))
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

fn get_args_and_types(f: &syn::ItemFn) -> Result<(Punctuated<syn::Expr, Token![,]>, Punctuated<syn::Type, Token![,]>)> {
    let mut call_args = Punctuated::<_, Token![,]>::new();
    let mut types = Punctuated::<_, Token![,]>::new();
    for input in &f.decl.inputs {
        match input {
            syn::FnArg::SelfValue(p) => {
                let diag = p.span().unstable()
                    .error("`self` arguments are currently unsupported by lru_cache");
                return Err(DiagnosticError::new(diag));
            }
            syn::FnArg::SelfRef(p) => {
                let diag = p.span().unstable()
                    .error("`&self` arguments are currently unsupported by lru_cache");
                return Err(DiagnosticError::new(diag));
            }
            syn::FnArg::Captured(arg_captured) => {
                let mut segments: syn::punctuated::Punctuated<_, Token![::]> = syn::punctuated::Punctuated::new();
                if let syn::Pat::Ident(ref pat_ident) = arg_captured.pat {
                    if let Some(m) = pat_ident.mutability {
                        let diag = m.span.unstable()
                            .error("`mut` arguments are not supported with lru_cache as this could lead to incorrect results being stored");
                        return Err(DiagnosticError::new(diag));
                    }
                    segments.push(syn::PathSegment { ident: pat_ident.ident.clone(), arguments: syn::PathArguments::None });
                }

                // If the arg type is a reference, remove the reference because the arg will be cloned
                if let syn::Type::Reference(type_reference) = &arg_captured.ty {
                    types.push(type_reference.elem.as_ref().to_owned()); // as_ref -> to_owned unboxes the type
                } else {
                    types.push(arg_captured.ty.clone());
                }

                call_args.push(syn::Expr::Path(syn::ExprPath { attrs: Vec::new(), qself: None, path: syn::Path { leading_colon: None, segments } }));
            },
            syn::FnArg::Inferred(p) => {
                let diag = p.span().unstable()
                    .error("inferred arguments are currently unsupported by lru_cache");
                return Err(DiagnosticError::new(diag));
            }
            syn::FnArg::Ignored(p) => {
                let diag = p.span().unstable()
                    .error("ignored arguments are currently unsupported by lru_cache");
                return Err(DiagnosticError::new(diag));
            }
        }
    }

    if types.len() == 1 {
        types.push_punct(syn::token::Comma { spans: [proc_macro2::Span::call_site(); 1] })
    }

    Ok((call_args, types))
}
