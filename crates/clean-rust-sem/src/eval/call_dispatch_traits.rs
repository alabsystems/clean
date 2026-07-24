// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trait signature validation and method resolution for call dispatch.
//!
//! Extracted from `call_dispatch.rs` to keep that module under the 500-line
//! limit. Contains impl-signature checking, trait method resolution, and
//! the helper that materializes `Self` types inside signatures.

use super::Interpreter;
use crate::error::RustSemError;
use crate::types::{FunctionSignature, RustType};

impl Interpreter {
    /// Validate that an impl function's signature matches a trait method signature.
    ///
    /// Returns an error if there's a mismatch in parameter count, parameter types,
    /// or return type. Impl functions have +1 param for self.
    pub(super) fn validate_impl_signature(
        &self,
        impl_fn_name: &str,
        trait_method_name: &str,
        trait_sig: &FunctionSignature,
        concrete_self_ty: &RustType,
    ) -> Result<(), RustSemError> {
        let Some(impl_def) = self.ctx.get_function(impl_fn_name) else {
            return Ok(());
        };

        let has_self_receiver = trait_sig.receiver.has_self_receiver();

        // Check parameter count (impl has +1 for self-receiver methods)
        let impl_param_count = impl_def.params.len();
        let trait_param_count = trait_sig.params.len() + usize::from(has_self_receiver);
        if impl_param_count != trait_param_count {
            return Err(RustSemError::impl_method_param_count_mismatch(
                impl_fn_name,
                trait_method_name,
                impl_param_count,
                trait_sig.params.len(),
                has_self_receiver,
            ));
        }

        let impl_params = impl_def.params.iter().skip(usize::from(has_self_receiver));

        // Check parameter types (skip first param only for self-receiver methods)
        for (i, ((_name, impl_ty), trait_ty)) in
            impl_params.zip(trait_sig.params.iter()).enumerate()
        {
            let actual_impl_ty = self.materialize_trait_type(impl_ty, concrete_self_ty);
            let expected_trait_ty = self.materialize_trait_type(trait_ty, concrete_self_ty);
            if actual_impl_ty != expected_trait_ty {
                return Err(RustSemError::ImplMethodParamTypeMismatch {
                    impl_fn_name: impl_fn_name.to_string(),
                    param_index: i + 1,
                    actual: actual_impl_ty,
                    expected: expected_trait_ty,
                });
            }
        }

        // Check return type
        let actual_ret_ty = self.materialize_trait_type(&impl_def.ret_ty, concrete_self_ty);
        let expected_ret_ty = self.materialize_trait_type(&trait_sig.ret, concrete_self_ty);
        if actual_ret_ty != expected_ret_ty {
            return Err(RustSemError::ImplMethodReturnTypeMismatch {
                impl_fn_name: impl_fn_name.to_string(),
                actual: actual_ret_ty,
                expected: expected_ret_ty,
            });
        }

        Ok(())
    }

    pub(super) fn resolve_receiver_trait_method(
        &self,
        type_name: &str,
        method_name: &str,
    ) -> Option<(&String, &str)> {
        for (trait_name, impl_fn) in self.ctx.get_trait_method_impls(type_name, method_name)? {
            let Some(sig) = self.ctx.get_trait_method_signature(trait_name, method_name) else {
                continue;
            };
            if !sig.receiver.has_self_receiver() {
                continue;
            }
            return Some((impl_fn, trait_name.as_str()));
        }
        None
    }

    pub(super) fn materialize_trait_type(
        &self,
        ty: &RustType,
        concrete_self_ty: &RustType,
    ) -> RustType {
        let substituted = ty.substitute_self_type(concrete_self_ty);
        let normalized = self.ctx.normalize_type(&substituted);
        // Erase anonymous (elided) lifetime IDs so that signature
        // comparisons ignore parser-assigned lifetime counters.  Trait
        // definitions and impl blocks allocate anonymous lifetimes
        // independently, producing different IDs for the same elided
        // position. Semantic validation should not distinguish them.
        normalized.erase_anonymous_lifetimes()
    }
}
