// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructor-order lowering helpers for do-notation matches.

use super::*;
use crate::infer::elab_match::{
    desugar_nat_numeral_add_pattern, desugar_nonzero_nat_lit, prepend_do_alias_binding,
};

impl<'a> ElabCtx<'a> {
    fn rewrite_top_level_do_match_ctor_dispatch_arm(
        &mut self,
        arm: &DoMatchArm,
        scrutinee_ty: &Expr,
    ) -> Result<DoMatchArm, ElabError> {
        if arm.patterns.len() != 1 {
            return Ok(arm.clone());
        }

        match &arm.patterns[0] {
            SurfacePattern::As(name, inner_pat) => {
                let (pattern, alias_value) =
                    self.rewrite_as_pattern_inner("do-match arm pattern", scrutinee_ty, inner_pat)?;
                Ok(DoMatchArm {
                    span: arm.span,
                    patterns: vec![pattern],
                    body: prepend_do_alias_binding(name, alias_value, &arm.body),
                })
            }
            _ => Ok(arm.clone()),
        }
    }

    pub(super) fn try_build_ctor_ordered_do_match_alts(
        &mut self,
        arms: &[DoMatchArm],
        type_name: &str,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
    ) -> Result<Option<Vec<Expr>>, ElabError> {
        // Build exactly one minor premise per constructor, in the inductive's
        // declaration order — the order `T.casesOn` expects. For each
        // constructor we GROUP every do-arm whose head names it (including a
        // trailing wildcard/var catch-all) and fold them into a single minor,
        // dispatching the inner sub-patterns via a chained casesOn whose
        // fallback is the next same-constructor arm. This mirrors the plain-match
        // `try_build_ctor_ordered_match_alts` / `compile_ctor_dispatch_alt_chain`
        // and is what lets `requireArcRef` (two `some` arms) and `semEndBorrow`
        // (the `0` / `1` / `n+2` numeral arms that all desugar to `Nat.succ`)
        // lower correctly: the historic builder rejected any repeated head
        // constructor and the legacy source-order loop then placed arms in the
        // wrong `casesOn` slots, leaving an unreduced motive beta-redex the
        // kernel rejected (the App(Lam …) type-mismatch cluster).
        let ind_name = Name::from_string(type_name);
        let Some(ind_info) = self.env.get_inductive(&ind_name).cloned() else {
            return Ok(None);
        };

        let mut ordered = Vec::with_capacity(ind_info.constructor_names.len());
        for ctor_name in &ind_info.constructor_names {
            let Some(alt) = self.compile_do_ctor_dispatch_alt_chain(
                ctor_name,
                arms,
                type_name,
                scrutinee_ty,
                branch_ty,
            )?
            else {
                return Ok(None);
            };
            ordered.push(alt);
        }

        Ok(Some(ordered))
    }

    /// Do-block analogue of `compile_ctor_dispatch_alt_chain`: gather every
    /// do-arm whose head pattern names `ctor_name` (plus the first catch-all
    /// wildcard/var that subsumes it) and fold them right-to-left into a single
    /// `casesOn` minor for that constructor. Each later same-constructor arm
    /// becomes the fallback of the earlier one's nested sub-pattern dispatch.
    ///
    /// Returns `Ok(None)` (caller falls back to the legacy source-order loop) for
    /// any arm shape outside the handled envelope, never a mis-typed minor.
    fn compile_do_ctor_dispatch_alt_chain(
        &mut self,
        ctor_name: &Name,
        arms: &[DoMatchArm],
        type_name: &str,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
    ) -> Result<Option<Expr>, ElabError> {
        let ctor_name_str = ctor_name.to_string();
        // (arm, is_catch_all) in source order. A catch-all terminates collection
        // for this constructor (everything after it is shadowed).
        let mut relevant: Vec<(DoMatchArm, bool)> = Vec::new();

        for arm in arms.iter() {
            let normalized =
                self.rewrite_top_level_do_match_ctor_dispatch_arm(arm, scrutinee_ty)?;
            if normalized.patterns.len() != 1 {
                return Ok(None);
            }
            match &normalized.patterns[0] {
                SurfacePattern::Wildcard | SurfacePattern::Inaccessible(_) => {
                    relevant.push((normalized, true));
                    break;
                }
                SurfacePattern::Var(name) => {
                    // A bare `Var` is either a nullary constructor name or a
                    // catch-all binder. A nullary ctor only matches its own slot;
                    // a non-ctor name is a catch-all subsuming every constructor.
                    let resolved = self.resolve_ctor_name(name, type_name);
                    let nullary_ctor = resolved.filter(|full_ctor| {
                        self.env
                            .get_constructor(&Name::from_string(full_ctor))
                            .is_some_and(|info| info.num_fields == 0)
                    });
                    if let Some(full_ctor) = nullary_ctor {
                        if full_ctor == ctor_name_str {
                            relevant.push((normalized, false));
                            break;
                        }
                    } else {
                        relevant.push((normalized, true));
                        break;
                    }
                }
                pattern => {
                    let Some(full_ctor) = self.top_level_ctor_target_name(type_name, pattern)
                    else {
                        return Ok(None);
                    };
                    if full_ctor == ctor_name_str {
                        relevant.push((normalized, false));
                    }
                }
            }
        }

        if relevant.is_empty() {
            // No arm names this constructor and no catch-all reached it: the match
            // is non-exhaustive in the handled envelope. Defer to the legacy loop.
            return Ok(None);
        }

        let mut compiled: Option<Expr> = None;
        for (arm, catch_all) in relevant.into_iter().rev() {
            let alt = if catch_all {
                let Some(alt) =
                    self.compile_do_ctor_catch_all_alt(ctor_name, &arm, scrutinee_ty, branch_ty)?
                else {
                    return Ok(None);
                };
                alt
            } else {
                match &arm.patterns[0] {
                    SurfacePattern::Ctor(inner_ctor, sub_pats) => self
                        .elab_do_match_ctor_arm_with_fallback(
                            inner_ctor,
                            sub_pats,
                            &arm,
                            scrutinee_ty,
                            type_name,
                            branch_ty,
                            compiled.as_ref(),
                        )?,
                    SurfacePattern::Lit(SurfaceLit::Nat(0)) => {
                        // `0` is the nullary `Nat.zero`; no sub-pattern dispatch.
                        self.elab_do_match_arm(&arm, scrutinee_ty, type_name, branch_ty)?
                    }
                    SurfacePattern::Lit(SurfaceLit::Nat(k)) => {
                        let desugared = desugar_nonzero_nat_lit(*k);
                        let SurfacePattern::Ctor(inner_ctor, sub_pats) = desugared else {
                            unreachable!("desugar_nonzero_nat_lit returns Ctor for k > 0")
                        };
                        self.elab_do_match_ctor_arm_with_fallback(
                            &inner_ctor,
                            &sub_pats,
                            &arm,
                            scrutinee_ty,
                            type_name,
                            branch_ty,
                            compiled.as_ref(),
                        )?
                    }
                    SurfacePattern::NumeralAdd(_, k) if *k <= 1 => {
                        // `n` (k=0) / `n+1` (k=1) bind the field directly; the
                        // legacy single-arm path handles the `Nat.succ` field bind.
                        self.elab_do_match_arm(&arm, scrutinee_ty, type_name, branch_ty)?
                    }
                    SurfacePattern::NumeralAdd(inner_pat, k) => {
                        let desugared = desugar_nat_numeral_add_pattern(inner_pat.as_ref(), *k);
                        let SurfacePattern::Ctor(inner_ctor, sub_pats) = desugared else {
                            unreachable!("desugar_nat_numeral_add_pattern returns Ctor for k > 1")
                        };
                        self.elab_do_match_ctor_arm_with_fallback(
                            &inner_ctor,
                            &sub_pats,
                            &arm,
                            scrutinee_ty,
                            type_name,
                            branch_ty,
                            compiled.as_ref(),
                        )?
                    }
                    SurfacePattern::Var(_) => {
                        // Bare nullary constructor name (e.g. `Option.none`): no
                        // fields, no sub-pattern dispatch.
                        self.elab_do_match_arm(&arm, scrutinee_ty, type_name, branch_ty)?
                    }
                    _ => return Ok(None),
                }
            };
            compiled = Some(alt);
        }

        Ok(compiled)
    }

    /// Do-block catch-all minor for `ctor_name`: the wildcard/var arm body wrapped
    /// in one lambda per constructor field. Mirrors `compile_ctor_catch_all_alt`.
    fn compile_do_ctor_catch_all_alt(
        &mut self,
        ctor_name: &Name,
        arm: &DoMatchArm,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
    ) -> Result<Option<Expr>, ElabError> {
        match &arm.patterns[0] {
            SurfacePattern::Wildcard | SurfacePattern::Inaccessible(_) => {
                let arm_body = self.elab_do_body_with_outer_continuation(&arm.body)?;
                let arm_body = self.metas.instantiate(&arm_body);
                self.wrap_ctor_fallback_alt(arm_body, ctor_name, scrutinee_ty)
                    .map(Some)
            }
            SurfacePattern::Var(name) => {
                // `| x => body` catch-all: bind `x` to the reconstructed ctor value
                // `ctor field₀ … fieldₙ` so the body sees the matched scrutinee.
                let field_tys = self.compute_ctor_field_types(ctor_name, scrutinee_ty)?;
                let mut field_fvars: Vec<(FVarId, Expr)> = Vec::with_capacity(field_tys.len());
                for (idx, field_ty) in field_tys.iter().enumerate() {
                    let prior_fvars: Vec<FVarId> = field_fvars.iter().map(|(f, _)| *f).collect();
                    let field_ty = Self::open_field_type_with_fvars(field_ty, &prior_fvars);
                    let fvar =
                        self.push_local(format!("_do_match_ctor_field_{idx}"), field_ty.clone());
                    field_fvars.push((fvar, field_ty));
                }
                let field_ids: Vec<FVarId> = field_fvars.iter().map(|(fvar, _)| *fvar).collect();
                let ctor_value = self.build_ctor_value(ctor_name, scrutinee_ty, &field_ids)?;
                let alias_fvar = self.push_local(name.clone(), scrutinee_ty.clone());
                let arm_body = self.elab_do_body_with_outer_continuation(&arm.body)?;
                let arm_body = self.metas.instantiate(&arm_body);
                self.pop_local();
                let mut result = Expr::let_named(
                    Name::from_string(name),
                    scrutinee_ty.clone(),
                    ctor_value,
                    arm_body.abstract_fvar(alias_fvar),
                    false,
                );
                let _ = branch_ty;
                for (fvar, field_ty) in field_fvars.iter().rev() {
                    self.pop_local();
                    result = result.abstract_fvar(*fvar);
                    result = Expr::lam(BinderInfo::Default, field_ty.clone(), result);
                }
                Ok(Some(result))
            }
            _ => Ok(None),
        }
    }
}
