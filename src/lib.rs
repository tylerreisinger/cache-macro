//! lru-cache-macros
//! ================
//!
//! An attribute procedural macro to automatically cache the result of a function given a set of inputs.
//!
//! **This crate has been deprecated in favor of [cache-macro](https://crates.io/crates/cache-macro) which maintains
//! the same functionality, but supports more than just lru caches. New code should use that crate instead.**
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
//!
//! This allows the cache type used internally to be changed. The default is equivalent to
//!
//! ```#[lru_config(cache_type = ::lru_cache::LruCache)]```
//!
//! * `#[lru_config(ignore_args = ...)]`
//!
//! This allows certain arguments to be ignored for the purposes of caching. That means they are not part of the
//! hash table key and thus should never influence the output of the function. It can be useful for diagnostic settings,
//! returning the number of times executed, or other introspection purposes.
//!
//! `ignore_args` takes a comma-separated list of variable identifiers to ignore.
//!
//! ### Example:
//! ```rust
//! use lru_cache_macros::lru_cache;
//! #[lru_cache(20)]
//! #[lru_config(ignore_args = call_count)]
//! fn fib(x: u64, call_count: &mut u32) -> u64 {
//!     *call_count += 1;
//!     if x <= 1 {
//!         1
//!     } else {
//!         fib(x - 1, call_count) + fib(x - 2, call_count)
//!     }
//! }
//!
//! let mut call_count = 0;
//! assert_eq!(fib(39, &mut call_count), 102_334_155);
//! assert_eq!(call_count, 40);
//! ```
//!
//! The `call_count` argument can vary, caching is only done based on `x`.
//!
//! * `#[lru_config(thread_local)]`
//!
//! Store the cache in thread-local storage instead of global static storage. This avoids the overhead of Mutex locking,
//! but each thread will be given its own cache, and all caching will not affect any other thread.
//!
//! Expanding on the first example:
//!
//! ```rust
//! use lru_cache_macros::lru_cache;
//!
//! #[lru_cache(20)]
//! #[lru_config(thread_local)]
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
//! # Details
//! The created cache is stored as a static variable protected by a mutex unless the `#[lru_config(thread_local)]` configuration
//! is added.
//!
//! With the default settings, the fibonacci example will generate the following code:
//!
//! ```rust
//! fn __lru_base_fib(x: u32) -> u64 {
//!     if x <= 1 { 1 } else { fib(x - 1) + fib(x - 2) }
//! }
//! fn fib(x: u32) -> u64 {
//!     use lazy_static::lazy_static;
//!     use std::sync::Mutex;
//!
//!     lazy_static! {
//!         static ref cache: Mutex<::lru_cache::LruCache<(u32,), u64>> =
//!             Mutex::new(::lru_cache::LruCache::new(20usize));
//!     }
//!
//!     let cloned_args = (x.clone(),);
//!     let mut cache_unlocked = cache.lock().unwrap();
//!     let stored_result = cache_unlocked.get_mut(&cloned_args);
//!     if let Some(stored_result) = stored_result {
//!         return stored_result.clone();
//!     };
//!     drop(cache_unlocked);
//!     let ret = __lru_base_fib(x);
//!     let mut cache_unlocked = cache.lock().unwrap();
//!     cache_unlocked.insert(cloned_args, ret.clone());
//!     ret
//! }
//!
//! ```
//!
//! Whereas, if you use the `#[lru_config(thread_local)]` the generated code will look like:
//!
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
//!                 cache_ref.insert(cloned_args, ret.clone());
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

// Function shim to allow us to use `Result` and the `?` operator.
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

// The main entry point for the macro.
fn lru_cache_impl(attr: TokenStream, item: TokenStream) -> Result<TokenStream> {
    let mut original_fn: syn::ItemFn = match syn::parse(item.clone()) {
        Ok(ast) => ast,
        Err(e) => {
            let diag = proc_macro2::Span::call_site().unstable()
                .error("lru_cache may only be used on functions");
            return Err(DiagnosticError::new_with_syn_error(diag, e));
        }
    };

    let (macro_config, out_attributes) =
        {
            let attribs = &original_fn.attrs[..];
            config::Config::parse_from_attributes(attribs)?
        };
    original_fn.attrs = out_attributes;

    let mut new_fn = original_fn.clone();

    let cache_size = get_lru_size(attr)?;
    let return_type = get_cache_fn_return_type(&original_fn)?;

    let new_name = format!("__lru_base_{}", original_fn.ident.to_string());
    original_fn.ident = syn::Ident::new(&new_name[..], original_fn.ident.span());

    let (call_args, types, cache_args) = get_args_and_types(&original_fn, &macro_config)?;
    let cloned_args = make_cloned_args_tuple(&cache_args);
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

    // Build all common types needed for each body impl.
    let cache_type = &macro_config.cache_type;
    let cache_type_with_generics: syn::Type = parse_quote! {
        #cache_type<#tuple_type, #return_type>
    };
    let cache_new: syn::Expr = parse_quote! {
        #cache_type::new(#cache_size)
    };

    let lru_body = build_cache_body(&cache_type_with_generics, &cache_new, &cloned_args,
        &fn_call, &macro_config);


    new_fn.block = Box::new(lru_body);

    let out = quote! {
        #original_fn

        #new_fn
    };
    Ok(out.into())
}

// Build the body of the caching function. What is constructed depends on the config value.
fn build_cache_body(full_cache_type: &syn::Type, cache_new: &syn::Expr,
                    cloned_args: &syn::ExprTuple, inner_fn_call: &syn::ExprCall,
                    config: &config::Config) -> syn::Block
{
    if config.use_tls {
        build_tls_cache_body(full_cache_type, cache_new, cloned_args, inner_fn_call)
    } else {
        build_mutex_cache_body(full_cache_type, cache_new, cloned_args, inner_fn_call)
    }
}

// Build the body of the caching function which puts the cache in thread-local storage.
fn build_tls_cache_body(full_cache_type: &syn::Type, cache_new: &syn::Expr,
                     cloned_args: &syn::ExprTuple, inner_fn_call: &syn::ExprCall) -> syn::Block
{
    parse_quote! {
        {
            use std::cell::UnsafeCell;
            use std::thread_local;
            thread_local!(
                // We use `UnsafeCell` here to allow recursion. Since it is in the TLS, it should
                // not introduce any actual unsafety.
                static cache: UnsafeCell<#full_cache_type> =
                    UnsafeCell::new(#cache_new);
            );
            cache.with(|c| {
                let mut cache_ref = unsafe { &mut *c.get() };
                let cloned_args = #cloned_args;

                let stored_result = cache_ref.get_mut(&cloned_args);
                if let Some(stored_result) = stored_result {
                    stored_result.clone()
                } else {
                    let ret = #inner_fn_call;
                    cache_ref.insert(cloned_args, ret.clone());
                    ret
                }
            })
        }
    }
}

// Build the body of the caching function which guards the static cache with a mutex.
fn build_mutex_cache_body(full_cache_type: &syn::Type, cache_new: &syn::Expr,
                     cloned_args: &syn::ExprTuple, inner_fn_call: &syn::ExprCall) -> syn::Block
{
    parse_quote! {
        {
            use lazy_static::lazy_static;
            use std::sync::Mutex;

            lazy_static! {
                static ref cache: Mutex<#full_cache_type> =
                    Mutex::new(#cache_new);
            }

            let cloned_args = #cloned_args;

            let mut cache_unlocked = cache.lock().unwrap();
            let stored_result = cache_unlocked.get_mut(&cloned_args);
            if let Some(stored_result) = stored_result {
                return stored_result.clone();
            };

            // must unlock here to allow potentially recursive call
            drop(cache_unlocked);

            let ret = #inner_fn_call;
            let mut cache_unlocked = cache.lock().unwrap();
            cache_unlocked.insert(cloned_args, ret.clone());
            ret
        }
    }
}

fn get_cache_fn_return_type(original_fn: &syn::ItemFn) -> Result<Box<syn::Type>> {
    if let syn::ReturnType::Type(_, ref ty) = original_fn.decl.output {
        Ok(ty.clone())
    } else {
        let diag = original_fn.ident.span().unstable()
            .error("There's no point of caching the output of a function that has no output");
        return Err(DiagnosticError::new(diag));
    }
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

fn get_args_and_types(f: &syn::ItemFn, config: &config::Config) ->
        Result<(Punctuated<syn::Expr, Token![,]>, Punctuated<syn::Type, Token![,]>, Punctuated<syn::Expr, Token![,]>)>
{
    let mut call_args = Punctuated::<_, Token![,]>::new();
    let mut types = Punctuated::<_, Token![,]>::new();
    let mut cache_args = Punctuated::<_, Token![,]>::new();

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
                let arg_name;
                if let syn::Pat::Ident(ref pat_ident) = arg_captured.pat {
                    arg_name = pat_ident.ident.clone();
                    if let Some(m) = pat_ident.mutability {
                        if !config.ignore_args.contains(&arg_name) {
                            let diag = m.span.unstable()
                                .error("`mut` arguments are not supported with lru_cache as this could lead to incorrect results being stored");
                            return Err(DiagnosticError::new(diag));
                        }
                    }
                    segments.push(syn::PathSegment { ident: pat_ident.ident.clone(), arguments: syn::PathArguments::None });
                } else {
                    let diag = arg_captured.span().unstable()
                        .error("unsupported argument kind");
                    return Err(DiagnosticError::new(diag));
                }

                let arg_path = syn::Expr::Path(syn::ExprPath { attrs: Vec::new(), qself: None, path: syn::Path { leading_colon: None, segments } });

                if !config.ignore_args.contains(&arg_name) {

                    // If the arg type is a reference, remove the reference because the arg will be cloned
                    if let syn::Type::Reference(type_reference) = &arg_captured.ty {
                        types.push(type_reference.elem.as_ref().to_owned()); // as_ref -> to_owned unboxes the type
                    } else {
                        types.push(arg_captured.ty.clone());
                    }

                    cache_args.push(arg_path.clone());
                }


                call_args.push(arg_path);
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

    Ok((call_args, types, cache_args))
}
