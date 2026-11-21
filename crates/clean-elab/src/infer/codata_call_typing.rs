// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Check authored mutual corecursive calls before publishing their candidates.

use super::*;

pub(crate) struct CodefSignature<'a> {
    pub(crate) name: &'a SurfaceName,
    pub(crate) levels: &'a [Name],
    pub(crate) params: &'a [Name],
    pub(crate) ty: &'a Expr,
}

pub(crate) struct CodefCall<'a> {
    pub(crate) owner: usize,
    pub(crate) callee: usize,
    pub(crate) field: &'a SurfaceName,
    pub(crate) value: &'a SurfaceExpr,
}

/// Completed, checked candidate headers become local hypotheses in the
/// ORIGINAL environment. Candidate bodies are unavailable here. No declaration
/// or proof is installed, and no expression containing these hypotheses escapes.
pub(crate) fn validate_mutual_codef_calls(
    env: &Environment,
    signatures: &[CodefSignature<'_>],
    calls: &[CodefCall<'_>],
) -> Result<(), ElabError> {
    for signature in signatures {
        let ty = signature.ty;
        if ty.has_fvar_quick() || MetaState::expr_has_meta(ty) || ty.has_level_mvar_quick() {
            return Err(ElabError::CannotInfer);
        }
        let context = ElabCtx::new(env);
        if !matches!(
            context.whnf(&context.infer_type_full(ty)?).kind(),
            ExprKind::Sort(_)
        ) {
            return Err(ElabError::TypeMismatch {
                expected: "a well-formed mutual codef signature".into(),
                actual: format!("{ty}"),
            });
        }
    }

    for call in calls {
        let mut context = ElabCtx::new(env);
        context.in_decl_context = true;
        let mut functions = Vec::with_capacity(signatures.len());
        let mut types = Vec::with_capacity(signatures.len());
        for signature in signatures {
            let substitution: Vec<_> = signature
                .levels
                .iter()
                .map(|level| (level.clone(), context.fresh_universe_param()))
                .collect();
            let ty = signature.ty.instantiate_level_params(&substitution);
            functions.push(context.push_local(signature.name.clone(), ty.clone()));
            types.push(ty);
        }
        let owner = signatures
            .get(call.owner)
            .ok_or_else(|| ElabError::InternalInvariant("mutual codef call has no owner".into()))?;
        let mut result = types[call.owner].clone();
        // Open the COMPLETED telescope, preserving implicit generic parameters
        // and state types inferred from observations, including `(s : _)`.
        for name in owner.params {
            let ExprKind::Pi(binder, domain, body) = result.kind() else {
                return Err(ElabError::InternalInvariant(
                    "mutual codef header parameter mismatch".into(),
                ));
            };
            let ty = domain.as_ref().clone();
            let fvar = context.push_local(SurfaceName::from_name(name.clone()), ty.clone());
            if context.binder_is_local_instance(binder.info, &ty) {
                context.push_local_instance(fvar, ty);
            }
            result = body.instantiate(&Expr::fvar(fvar));
        }
        if matches!(result.kind(), ExprKind::Pi(..)) {
            return Err(ElabError::InternalInvariant(
                "mutual codef header parameter mismatch".into(),
            ));
        }

        // A local receiver exposes the REAL accessor's instantiated result
        // type. Only its type is used; no arbitrary accessor body is trusted.
        let (receiver_id, receiver_name) = loop {
            let id = context.fresh_fvar();
            let name =
                SurfaceName::from_name(Name::anon().num(id.as_u64()).str("mutual_codef_receiver"));
            if context.lookup_local(&name).is_none() {
                break (id, name);
            }
        };
        context.push_local_with_fvar(receiver_name.clone(), receiver_id, result);
        let projection = SurfaceExpr::Proj(
            clean_parser::Span::dummy(),
            Box::new(SurfaceExpr::Ident(
                clean_parser::Span::dummy(),
                receiver_name,
            )),
            Projection::Named(call.field.clone()),
        );
        let projection = context.elaborate(&projection)?;
        let expected = context.infer_type(&projection)?;
        let value = context.elaborate_with_type(call.value, expected.clone())?;
        let Some(callee) = functions.get(call.callee) else {
            return Err(ElabError::InternalInvariant(
                "mutual codef call has no callee".into(),
            ));
        };
        // Result coercions cannot justify erasing a call: lowering retains
        // only the state, so a coercion around that call would be lost.
        if !matches!(value.get_app_fn().kind(), ExprKind::FVar(id) if id == callee) {
            return Err(ElabError::Unsupported {
                feature: "mutual codef: recursive clause must remain a direct declared call".into(),
            });
        }
        let actual = context.infer_type_full(&value)?;
        // Compare the declared member and EACH parameter before unfolding
        // the carrier: an M-type encoding can erase phantom parameters, so
        // whole-type definitional equality alone would accept Nat/Bool here.
        let actual = context
            .metas
            .instantiate_levels(&context.metas.instantiate(&actual));
        let expected = context
            .metas
            .instantiate_levels(&context.metas.instantiate(&expected));
        let mismatch = || ElabError::TypeMismatch {
            expected: format!("{expected}"),
            actual: format!("{actual}"),
        };
        let (
            ExprKind::Const(actual_member, actual_levels),
            ExprKind::Const(expected_member, expected_levels),
        ) = (actual.get_app_fn().kind(), expected.get_app_fn().kind())
        else {
            return Err(mismatch());
        };
        let actual_parameters = actual.get_app_args();
        let expected_parameters = expected.get_app_args();
        if actual_member != expected_member
            || actual_levels.len() != expected_levels.len()
            || actual_parameters.len() != expected_parameters.len()
        {
            return Err(mismatch());
        }
        for (left, right) in actual_levels.iter().zip(expected_levels) {
            check_argument(
                &mut context,
                &Expr::sort(left.clone()),
                &Expr::sort(right.clone()),
            )?;
        }
        for (left, right) in actual_parameters.iter().zip(&expected_parameters) {
            check_argument(&mut context, left, right)?;
        }
        context.commit_pending_level_assigns();
        let actual = context
            .metas
            .instantiate_levels(&context.metas.instantiate(&actual));
        let expected = context
            .metas
            .instantiate_levels(&context.metas.instantiate(&expected));
        if MetaState::expr_has_meta(&actual)
            || MetaState::expr_has_meta(&expected)
            || !context.is_def_eq(&actual, &expected)
        {
            return Err(ElabError::TypeMismatch {
                expected: format!("{expected}"),
                actual: format!("{actual}"),
            });
        }
    }
    Ok(())
}

fn check_argument(
    context: &mut ElabCtx<'_>,
    actual: &Expr,
    expected: &Expr,
) -> Result<(), ElabError> {
    let unified = {
        let locals = context.build_local_ctx();
        let mut unifier = Unifier::with_env(&mut context.metas, context.env, locals);
        matches!(unifier.unify(actual, expected), UnifyResult::Success)
    };
    if unified || context.is_def_eq(actual, expected) {
        Ok(())
    } else {
        Err(ElabError::TypeMismatch {
            expected: format!("{expected}"),
            actual: format!("{actual}"),
        })
    }
}
