// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::source::parser::Parser;
use crate::source::SourceError;
use crate::trait_defaults::DefaultMethodBody;
use crate::types::{FunctionSignature, ReceiverMode, RustType};

impl Parser {
    pub(super) fn parse_trait_method_with_optional_default(
        &mut self,
        method: syn::TraitItemFn,
    ) -> Result<(FunctionSignature, Option<DefaultMethodBody>), SourceError> {
        let method_name = method.sig.ident.to_string();
        if method.sig.constness.is_some()
            || method.sig.unsafety.is_some()
            || method.sig.abi.is_some()
            || method.sig.variadic.is_some()
        {
            return Err(Self::unsupported(
                "trait method",
                format!("unsupported modifiers on `{method_name}`"),
            ));
        }
        let method_type_params =
            self.assign_type_param_ids(Self::parse_generics(&method.sig.generics)?);

        self.with_type_params(&method_type_params, |parser| {
            let receiver = match method.sig.inputs.first() {
                Some(syn::FnArg::Receiver(receiver)) => {
                    Self::parse_trait_receiver_mode(receiver, &method_name)?
                }
                Some(syn::FnArg::Typed(_)) | None => ReceiverMode::Static,
            };
            let receiver_inputs = usize::from(receiver.has_self_receiver());
            let params = method
                .sig
                .inputs
                .iter()
                .skip(receiver_inputs)
                .map(|arg| match arg {
                    syn::FnArg::Typed(pat_ty) => parser.parse_type(&pat_ty.ty),
                    syn::FnArg::Receiver(_) => Err(SourceError::Invalid {
                        context: "trait method",
                        detail: format!("multiple receivers in `{method_name}`"),
                    }),
                })
                .collect::<Result<Vec<_>, _>>()?;

            let ret = parser.parse_return_type(&method.sig.output)?;

            let sig = FunctionSignature {
                name: method_name.clone(),
                receiver,
                params: params.clone(),
                ret: ret.clone(),
                is_async: method.sig.asyncness.is_some(),
                type_params: method_type_params.clone(),
            };

            let default_body = if let Some(block) = method.default {
                let mut fn_params = Vec::new();
                if receiver.has_self_receiver() {
                    let self_type = Self::receiver_mode_to_self_type(receiver);
                    fn_params.push(("self".to_string(), self_type));
                }

                for arg in method.sig.inputs.iter().skip(receiver_inputs) {
                    if let syn::FnArg::Typed(pat_ty) = arg {
                        let name = Self::pat_ident_name(&pat_ty.pat)?;
                        let ty = parser.parse_type(&pat_ty.ty)?;
                        fn_params.push((name, ty));
                    }
                }

                let body = parser.parse_block(&block)?;
                Some(DefaultMethodBody {
                    params: fn_params,
                    ret_ty: ret,
                    body,
                })
            } else {
                None
            };

            Ok((sig, default_body))
        })
    }

    pub(super) fn placeholder_self_type() -> RustType {
        RustType::Named {
            name: "Self".to_string(),
            type_args: vec![],
            lifetime_args: vec![],
            const_args: vec![],
        }
    }

    /// Convert a receiver mode to a placeholder Self type for default method bodies.
    fn receiver_mode_to_self_type(mode: ReceiverMode) -> RustType {
        debug_assert!(mode.has_self_receiver());
        let self_ty = Self::placeholder_self_type();
        match mode {
            ReceiverMode::Static => Self::placeholder_self_type(),
            ReceiverMode::ByValue => self_ty,
            ReceiverMode::ByRef => RustType::Reference {
                lifetime: crate::types::Lifetime::Anonymous(0),
                mutability: crate::types::Mutability::Shared,
                inner: Box::new(self_ty),
            },
            ReceiverMode::ByMut => RustType::Reference {
                lifetime: crate::types::Lifetime::Anonymous(0),
                mutability: crate::types::Mutability::Mutable,
                inner: Box::new(self_ty),
            },
        }
    }

    fn parse_trait_receiver_mode(
        receiver: &syn::Receiver,
        method_name: &str,
    ) -> Result<ReceiverMode, SourceError> {
        if receiver.colon_token.is_some() {
            return Err(Self::unsupported(
                "trait method",
                format!("typed self receiver in `{method_name}`"),
            ));
        }
        Ok(match receiver.reference.as_ref() {
            Some(_) if receiver.mutability.is_some() => ReceiverMode::ByMut,
            Some(_) => ReceiverMode::ByRef,
            None => ReceiverMode::ByValue,
        })
    }
}
