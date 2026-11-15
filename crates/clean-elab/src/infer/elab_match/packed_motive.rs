// Copyright 2026 Andrew Yates | Apache-2.0
//! Dependent motives for the parser's right-nested `Prod.mk` discriminants.
//!
//! A tuple match must generalize its local components, not keep them fixed in
//! every minor. For `match a, b with`, the motive is
//! `fun pair => expected[a := pair.1, b := pair.2]`. The ordinary column
//! compiler then specializes the fields through its existing dependent matches.
//! This does not weaken arm conversion, recursor authentication or registration.

use super::*;

/// Only literal tuples of distinct locals are generalized. Repeated locals
/// need diagonal equalities; nonlocal components need a different abstraction
/// strategy. Those shapes retain the existing lowering rather than guessing.
fn collect_local_projections(
    value: &Expr,
    projected: Expr,
    fields: &mut Vec<(FVarId, Expr)>,
) -> bool {
    let mut pending = vec![(value, projected)];
    let mut seen = std::collections::HashSet::new();
    while let Some((value, projected)) = pending.pop() {
        if let ExprKind::FVar(id) = value.kind() {
            if !seen.insert(*id) {
                return false;
            }
            fields.push((*id, projected));
            continue;
        }
        let ExprKind::Const(name, _) = value.get_app_fn().kind() else {
            return false;
        };
        if *name != Name::from_string("Prod.mk") {
            return false;
        }
        let args = value.get_app_args();
        if args.len() != 4 {
            return false;
        }
        let prod = Name::from_string("Prod");
        // A work list avoids adding a native-stack recursion for long tuples.
        pending.push((args[3], Expr::proj(prod.clone(), 1, projected.clone())));
        pending.push((args[2], Expr::proj(prod, 0, projected)));
    }
    true
}

impl<'a> ElabCtx<'a> {
    pub(super) fn packed_match_motive(
        &mut self,
        scrutinee: &Expr,
        scrutinee_ty: &Expr,
        expected: &Expr,
    ) -> Result<Option<Expr>, ElabError> {
        if self.has_metavars(expected)
            || !matches!(scrutinee.get_app_fn().kind(),
                ExprKind::Const(name, _) if *name == Name::from_string("Prod.mk"))
        {
            return Ok(None);
        }
        self.with_temporary_local_scope(|this| {
            let pair = this.push_local(
                SurfaceName::unspellable("_packed_motive", 0),
                scrutinee_ty.clone(),
            );
            let mut fields = Vec::new();
            if !collect_local_projections(scrutinee, Expr::fvar(pair), &mut fields) {
                return Ok(None);
            }
            // Generalizing a discriminant also requires generalizing locals
            // whose types/let values depend on it. Until that telescope
            // transport is implemented, preserve the existing constant route.
            //
            // A let-bound discriminant is generalized like any other local:
            // Lean's motive abstracts the discriminant `c` and does not keep
            // its value, so after `let c := a`, `match c, b with | false, _ =>
            // rfl` must prove `false = a` and is refused (pinned 4.8.0,
            // 4.30.0-rc2, 4.36.0-rc2), as the single-discriminant route here
            // already refuses it. The constant route would zeta `c` to `a` in
            // every arm and accept it.
            for (field, _) in &fields {
                for (_, local, ty) in &this.locals {
                    let ty = this.metas.instantiate_levels(&this.metas.instantiate(ty));
                    if this.has_metavars(&ty) || ty.abstract_fvar(*field) != ty {
                        return Ok(None);
                    }
                    if let Some(value) = this.locals.reduction_value(*local) {
                        let value = this.metas.instantiate(value);
                        if this.has_metavars(&value) || value.abstract_fvar(*field) != value {
                            return Ok(None);
                        }
                    }
                }
            }
            let mut refined = expected.clone();
            for (field, projection) in fields {
                // Use a FREE pair local here: subst_fvar does not lift loose
                // BVars. Abstract only after substitution, so expected types
                // containing Pi/lambda binders cannot capture the projections.
                refined = refined.subst_fvar(field, &projection);
            }
            if refined == *expected {
                return Ok(None);
            }
            // Check that this is a type family in the actual pair context.
            // In particular, no ill-typed dependent component is smuggled into
            // the motive. The completed eliminator is still kernel-checked.
            let _ = this.infer_sort(&refined)?;
            let body = refined.abstract_fvar(pair);
            if !this.is_def_eq(&body.instantiate(scrutinee), expected) {
                return Err(ElabError::InternalInvariant(
                    "packed match motive does not recover its expected type".into(),
                ));
            }
            Ok(Some(body))
        })
    }
}
