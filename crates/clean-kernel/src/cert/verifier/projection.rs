// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Projection certificate verification.
//!
//! Handles `ProofCert::Proj` and the soundness-critical `derive_proj_field_type`
//! helper that independently derives field types from the environment definition
//! instead of trusting the certificate's claim (#2064).

use crate::expr::{Expr, ExprKind};
use crate::name::Name;

use super::super::types::{CertError, ProofCert};
use super::CertVerifier;

impl<'env> CertVerifier<'env> {
    /// Proj rule: verify projection from a structure
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn verify_proj(
        &mut self,
        struct_name: &Name,
        idx: u32,
        expr_cert: &ProofCert,
        expr_type: &Expr,
        field_type: &Expr,
        proj_name: &Name,
        proj_idx: u32,
        proj_expr: &Expr,
    ) -> Result<Expr, CertError> {
        // Verify struct name matches
        if struct_name != proj_name {
            return Err(CertError::StructureMismatch {
                expected: format!("Proj({})", struct_name),
                actual: format!("Proj({})", proj_name),
            });
        }

        // Verify field index matches
        if idx != proj_idx {
            return Err(CertError::StructureMismatch {
                expected: format!("Proj index {}", idx),
                actual: format!("Proj index {}", proj_idx),
            });
        }

        // Recursively verify the inner expression certificate
        let inferred_expr_type = self.verify_impl(expr_cert, proj_expr)?;

        // Verify the inner expression's type matches what the cert claims
        if !self.def_eq_impl(&inferred_expr_type, expr_type) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(inferred_expr_type.clone()),
                actual: Box::new(expr_type.clone()),
                location: "Proj expression type".to_string(),
            });
        }

        // SOUNDNESS FIX (#2064): Independently derive field_type from
        // the environment's structure definition instead of trusting the
        // certificate's claimed field_type.
        let derived_field_type =
            self.derive_proj_field_type(struct_name, idx, proj_expr, &inferred_expr_type)?;

        // Verify the cert's claimed field_type matches our derivation
        // (catches bugs in the generator)
        if !self.def_eq_impl(&derived_field_type, field_type) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(derived_field_type),
                actual: Box::new(field_type.clone()),
                location: "Proj field_type: cert claim differs from independent derivation"
                    .to_string(),
            });
        }

        Ok(derived_field_type)
    }

    /// Independently derive the field type for a Proj certificate.
    ///
    /// SOUNDNESS-CRITICAL: The verifier must NOT trust the `field_type`
    /// claimed by the certificate. Instead, it looks up the structure
    /// definition in the environment and computes the field type from
    /// the constructor's type telescope.
    ///
    /// Mirrors the logic in `TypeChecker::infer_proj_type_from_impl`
    /// (tc/infer.rs) but uses only verifier-available infrastructure.
    fn derive_proj_field_type(
        &self,
        struct_name: &Name,
        idx: u32,
        inner_expr: &Expr,
        verified_expr_type: &Expr,
    ) -> Result<Expr, CertError> {
        // 1. WHNF the expression type to expose the inductive application
        let expr_type_whnf = self.whnf_impl(verified_expr_type);

        // 2. Extract the type arguments from the application spine
        let type_args = expr_type_whnf.get_app_args();
        let type_fn = expr_type_whnf.get_app_fn();

        let (type_name, type_levels) = match &type_fn.kind {
            ExprKind::Const(name, levels) => (name, levels),
            _ => {
                return Err(CertError::InvalidCert(format!(
                    "Proj: expression type WHNF is not a Const application: {:?}",
                    expr_type_whnf
                )))
            }
        };

        // Verify the type matches struct_name
        if type_name != struct_name {
            return Err(CertError::StructureMismatch {
                expected: format!("Proj type {}", struct_name),
                actual: format!("Proj type {}", type_name),
            });
        }

        // 3. Look up the inductive type
        let ind_val = self.env.get_inductive(struct_name).ok_or_else(|| {
            CertError::InvalidCert(format!("Proj: unknown inductive type {}", struct_name))
        })?;

        // Structures must have exactly one constructor
        if ind_val.constructor_names.len() != 1 {
            return Err(CertError::InvalidCert(format!(
                "Proj: {} has {} constructors, expected 1",
                struct_name,
                ind_val.constructor_names.len()
            )));
        }

        // 4. Look up the constructor
        let ctor_name = &ind_val.constructor_names[0];
        let ctor_val = self.env.get_constructor(ctor_name).ok_or_else(|| {
            CertError::InvalidCert(format!("Proj: unknown constructor {}", ctor_name))
        })?;

        // Check index is in bounds
        if idx >= ctor_val.num_fields {
            return Err(CertError::InvalidCert(format!(
                "Proj: field index {} out of bounds ({} has {} fields)",
                idx, struct_name, ctor_val.num_fields
            )));
        }

        // 5. Instantiate constructor type: first universe levels, then term parameters.
        //    Per Lean 4 (type_checker.cpp:241): instantiate_type_lparams(c_info, const_levels(I))
        //    before walking the Pi telescope. Without this, field types with
        //    Level::Param(...) remain unsubstituted (#2172).
        let num_params = ctor_val.num_params as usize;
        if ind_val.level_params.len() != type_levels.len() {
            return Err(CertError::InvalidCert(format!(
                "Proj: level_params ({}) != type_levels ({}) for {}",
                ind_val.level_params.len(),
                type_levels.len(),
                struct_name
            )));
        }
        let mut current = if ind_val.level_params.is_empty() {
            ctor_val.type_.clone()
        } else {
            ctor_val
                .type_
                .instantiate_level_params_direct(&ind_val.level_params, type_levels.as_slice())
        };
        for i in 0..num_params {
            let current_whnf = self.whnf_impl(&current);
            match &current_whnf.kind {
                ExprKind::Pi(_, _, body) => {
                    if i < type_args.len() {
                        current = body.instantiate(type_args[i]);
                    } else {
                        return Err(CertError::InvalidCert(format!(
                            "Proj: not enough type arguments ({}) for {} parameters",
                            type_args.len(),
                            num_params
                        )));
                    }
                }
                _ => {
                    return Err(CertError::InvalidCert(format!(
                        "Proj: constructor type ran out of Pi binders at parameter {}",
                        i
                    )));
                }
            }
        }

        // 6. Walk the telescope to the target field, substituting projections
        //    for earlier dependent fields (per Lean 4 type_checker.cpp:252-258).
        for field_idx in 0..idx {
            let current_whnf = self.whnf_impl(&current);
            match &current_whnf.kind {
                ExprKind::Pi(_, _, body) => {
                    if body.has_loose_bvars() {
                        // Dependent field: substitute projection of inner_expr at this field
                        let proj_field =
                            Expr::proj(struct_name.clone(), field_idx, inner_expr.clone());
                        current = body.instantiate(&proj_field);
                    } else {
                        // Non-dependent: body doesn't reference this binder
                        current = (**body).clone();
                    }
                }
                _ => {
                    return Err(CertError::InvalidCert(format!(
                        "Proj: constructor type ran out of Pi binders at field {}",
                        field_idx
                    )));
                }
            }
        }

        // 7. Extract the target field's domain
        let current_whnf = self.whnf_impl(&current);
        match &current_whnf.kind {
            ExprKind::Pi(_, domain, _) => Ok((**domain).clone()),
            _ => Err(CertError::InvalidCert(format!(
                "Proj: constructor type missing Pi at target field index {}",
                idx
            ))),
        }
    }
}
