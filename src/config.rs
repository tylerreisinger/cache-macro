use std::default::Default;
use std::collections::HashSet;

use proc_macro2;
use syn::{self, Token, parenthesized};
use syn::parse::{Parse, ParseStream};

use crate::error::{DiagnosticError, Result};

pub struct Config {
    pub ignore_args: HashSet<syn::Ident>,
    pub use_tls: bool,
}

struct IgnoreArgsAttrib {
    ignore_args: HashSet<syn::Ident>,
}

enum ConfigAttrib {
    IgnoreArgs(IgnoreArgsAttrib),
    UseTls,
}

const CONFIG_ATTRIBUTE_NAME: &'static str = "cache_cfg";

impl Config {
    // Parse any additional attributes present after `lru_cache` and return a configuration object
    // created from their contents. Additionally, return any attributes that were not handled here.
    pub fn parse_from_attributes(attribs: &[syn::Attribute]) -> Result<(Config, Vec<syn::Attribute>)> {
        let mut parsed_attributes = Vec::new();
        let mut remaining_attributes = Vec::new();

        for attrib in attribs {
            let segs = &attrib.path.segments;
            if segs.len() > 0 {
                if segs[0].ident == CONFIG_ATTRIBUTE_NAME {
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
                else {
                    remaining_attributes.push(attrib.clone());
                }
            }
        }

        let mut config: Config = Default::default();

        for parsed_attrib in parsed_attributes {
            match parsed_attrib {
                ConfigAttrib::IgnoreArgs(val) => config.ignore_args = val.ignore_args,
                ConfigAttrib::UseTls => config.use_tls = true,
            }
        }

        Ok((config, remaining_attributes))
    }
}

impl Default for Config {
    fn default() -> Config {
        Config {
            ignore_args: HashSet::new(),
            use_tls: false,
        }
    }
}

impl Parse for ConfigAttrib {
    fn parse(input: ParseStream) -> syn::parse::Result<Self> {
        let content;
        let _paren = parenthesized!(content in input);
        let name = content.parse::<syn::Ident>()?;

        match &name.to_string()[..] {
            "ignore_args" => Ok(ConfigAttrib::IgnoreArgs(content.parse::<IgnoreArgsAttrib>()?)),
            "thread_local" => Ok(ConfigAttrib::UseTls),
            _ => Err(syn::parse::Error::new(
                name.span(), format!("unrecognized config option '{}'", name.to_string())
            ))
        }
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