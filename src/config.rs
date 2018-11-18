use std::default::Default;
use std::collections::HashSet;

use proc_macro2;
use syn::{self, Token, parenthesized};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;

use crate::error::{DiagnosticError, Result};

pub struct Config {
    pub cache_type: syn::Path,
    pub ignore_args: HashSet<syn::Ident>,
}

struct IgnoreArgsAttrib {
    ignore_args: HashSet<syn::Ident>,
}

struct CacheTypeAttrib {
    type_path: syn::Path,
}

enum ConfigAttrib {
    CacheType(CacheTypeAttrib),
    IgnoreArgs(IgnoreArgsAttrib),
}

impl Config {
    pub fn parse_from_attributes(attribs: &[syn::Attribute]) -> Result<Config> {
        let mut parsed_attributes = Vec::new();
        for attrib in attribs {
            let segs = &attrib.path.segments;
            if segs.len() > 0 {
                if segs[0].ident.to_string() == "lru_config" {
                    let tokens = attrib.tts.clone();
                    let parsed = syn::parse2::<ConfigAttrib>(tokens);
                    match parsed {
                        Ok(parsed_attrib) => parsed_attributes.push(parsed_attrib),
                        Err(e) => {
                            let diag = e.span().unstable()
                                .error(format!("{}", e));
                            return Err(DiagnosticError::new_with_syn_error(diag, e));
                        }
                    }
                }
            }
        }

        let mut config: Config = Default::default();

        for parsed_attrib in parsed_attributes {
            match parsed_attrib {
                ConfigAttrib::CacheType(val) => config.cache_type = val.type_path,
                ConfigAttrib::IgnoreArgs(val) => config.ignore_args = val.ignore_args,
            }
        }

        Ok(config)
    }
}

impl Default for Config {
    fn default() -> Config {
        Config {
            cache_type: make_path_from_segments(&["lru_cache", "LruCache"], true, proc_macro2::Span::call_site()),
            ignore_args: HashSet::new(),
        }
    }
}

fn make_path_from_segments(segments: &[&str], has_leading_colon: bool, span: proc_macro2::Span) -> syn::Path {
    let leading_colon = if has_leading_colon {
        Some(syn::token::Colon2 { spans: [span; 2] })
    } else {
        None
    };
    let mut segments_ast = Punctuated::<syn::PathSegment, Token![::]>::new();
    for name in segments {
        let ident = syn::Ident::new(name, span);
        let seg = syn::PathSegment {
            ident,
            arguments: syn::PathArguments::None,
        };
        segments_ast.push(seg);
    }

    syn::Path {
        leading_colon,
        segments: segments_ast,
    }
}

impl Parse for ConfigAttrib {
    fn parse(input: ParseStream) -> syn::parse::Result<Self> {
        let content;
        let _paren = parenthesized!(content in input);
        let name = content.parse::<syn::Ident>()?;

        match &name.to_string()[..] {
            "cache_type" => Ok(ConfigAttrib::CacheType(content.parse::<CacheTypeAttrib>()?)),
            "ignore_args" => Ok(ConfigAttrib::IgnoreArgs(content.parse::<IgnoreArgsAttrib>()?)),
            _ => Err(syn::parse::Error::new(
                name.span(), format!("unrecognized config option '{}'", name.to_string())
            ))
        }
    }
}

impl Parse for CacheTypeAttrib {
    fn parse(input: ParseStream) -> syn::parse::Result<Self> {
        input.parse::<Token![=]>()?;
        Ok(CacheTypeAttrib {
            type_path: input.parse::<syn::Path>()?
        })
    }
}

impl Parse for IgnoreArgsAttrib {
    fn parse(input: ParseStream) -> syn::parse::Result<Self> {
        input.parse::<Token![=]>()?;
        let elems = syn::punctuated::Punctuated::<syn::Ident, Token![,]>::parse_terminated(input)?;
        Ok(IgnoreArgsAttrib {
            ignore_args: elems.into_iter().collect(),
        })
    }
}