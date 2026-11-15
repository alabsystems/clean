// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Column-split lowering of ONE recursor minor whose arms differ in their
//! nested field sub-patterns.
//!
//! A structurally recursive match is lowered to `T.rec` with one minor per
//! constructor. When several arms share a constructor and differ only in a
//! field's sub-pattern, the legacy lowering (`try_build_nested_head_rec_alts`)
//! folds them into a fallback chain: each arm's nested `casesOn` sends its
//! non-matching constructors to the next arm's compiled minor. The LAST arm
//! has nothing to fall back to, so a cover that is exhaustive only jointly —
//!
//! ```text
//! def filterSome : List (Option α) → List α
//!   | []             => []
//!   | none :: rest   => filterSome rest
//!   | some b :: rest => b :: filterSome rest
//! ```
//!
//! — failed with "non-exhaustive nested constructor pattern `Option.some`",
//! although the `none` minor of the last arm's `Option.casesOn` is reachable
//! only from the first arm, which already handles it. Lean 4's match compiler
//! (`Lean.Meta.Match.mkMatcher`) never chains alternatives this way: it
//! specializes the whole alternative list column by column, so every
//! `casesOn` it emits has a minor for every constructor drawn from the rows
//! that cover it.
//!
//! This module does the same for the recursive minor: it binds the
//! constructor's fields (and the induction hypotheses for its recursive
//! fields) exactly as `ElabCtx::elaborate_rec_arm` does for any arm, and
//! elaborates, as that arm's body, the decision tree that
//! `ElabCtx::build_column_split_surface` builds over the field columns — the
//! same decision-tree builder the non-recursive lowering already uses
//! (`compile_ctor_field_column_split`). A self-call on a recursive field
//! reaches its induction hypothesis through the pattern variable's `let`
//! alias of the field (`recursive_call.rs` follows such aliases).
//!
//! The lowering is a RESCUE: the caller runs it only after the fallback chain
//! failed, so every definition the chain already compiled keeps its term
//! byte-for-byte. It is transactional (locals, metas, levels) and its result
//! is re-checked by the kernel like any other minor.

use super::*;

/// One arm of a constructor minor: its field sub-patterns (one per field,
/// implicit fields expanded) and its body.
pub(in crate::infer) type CtorFieldRow = (Vec<SurfacePattern>, SurfaceExpr);

impl<'a> ElabCtx<'a> {
    /// Whether some field column of `rows` actually dispatches on a
    /// constructor: a constructor, `Nat` literal or `n + k` sub-pattern, or a
    /// bare variable that resolves to a constructor of that field's type
    /// (`true` on a `Bool` field). An all-binder cover needs no field split.
    pub(in crate::infer) fn ctor_field_rows_dispatch(
        &self,
        ctor_name: &Name,
        rows: &[CtorFieldRow],
        scrutinee_ty: &Expr,
    ) -> Result<bool, ElabError> {
        let field_type_names: Vec<Option<SurfaceName>> = self
            .compute_ctor_field_types(ctor_name, scrutinee_ty)?
            .iter()
            .map(|ft| self.get_type_name(ft).ok())
            .collect();
        Ok(rows.iter().any(|(sub_pats, _)| {
            sub_pats.iter().enumerate().any(|(idx, p)| {
                let mut p = p;
                while let SurfacePattern::As(_, inner) = p {
                    p = inner;
                }
                match p {
                    SurfacePattern::Ctor(_, _)
                    | SurfacePattern::Lit(_)
                    | SurfacePattern::NumeralAdd(_, _) => true,
                    SurfacePattern::Var(name) => field_type_names
                        .get(idx)
                        .and_then(|tn| tn.as_ref())
                        .and_then(|tn| self.resolve_ctor_name(name, tn))
                        .is_some(),
                    _ => false,
                }
            })
        }))
    }

    /// The rows the field decision-tree rescue would compile the minor for
    /// `ctor_name` from, with the source index of each row's arm. `None` when
    /// the rescue does not apply: a catch-all covers the constructor (the
    /// chain then ends in a total arm), fewer than two arms cover it (a lone
    /// partial arm is genuinely non-exhaustive), an arm's fields cannot be
    /// read as sub-patterns, or no field column dispatches.
    pub(in crate::infer) fn nested_head_rec_split_rows(
        &mut self,
        ctor_name: &Name,
        covering: &[(usize, &clean_parser::SurfaceMatchArm, bool)],
        type_name: &SurfaceName,
        scrutinee_ty: &Expr,
    ) -> Result<Option<(Vec<CtorFieldRow>, Vec<usize>)>, ElabError> {
        if covering.len() < 2 || covering.iter().any(|(_, _, catch_all)| *catch_all) {
            return Ok(None);
        }
        let mut rows = Vec::with_capacity(covering.len());
        for (_, arm, _) in covering {
            let Some(sub_pats) =
                self.ctor_dispatch_arm_field_pats(ctor_name, &arm.pattern, type_name)?
            else {
                return Ok(None);
            };
            rows.push((sub_pats, arm.body.clone()));
        }
        if !self.ctor_field_rows_dispatch(ctor_name, &rows, scrutinee_ty)? {
            return Ok(None);
        }
        let alts = covering.iter().map(|(idx, _, _)| *idx).collect();
        Ok(Some((rows, alts)))
    }

    /// Which of `rows` (the arms covering `ctor_name`, as
    /// `nested_head_rec_split_rows` reads them) the field decision tree
    /// selects, and whether it covers every value — read off the tree the
    /// rescue would elaborate, before anything is elaborated. Both answers
    /// hold for the minor whichever lowering compiles it: a row the tree never
    /// selects is one Lean refuses ("redundant alternative"), and a tree that
    /// covers every value means a failure to compile it is not a missing
    /// constructor. `None` outside the tree's envelope (a dependent field
    /// telescope, a sub-pattern it does not take).
    pub(in crate::infer) fn rec_ctor_field_split_reach(
        &mut self,
        ctor_name: &Name,
        rows: &[CtorFieldRow],
        scrutinee_ty: &Expr,
    ) -> Result<Option<RowReach>, ElabError> {
        let Some(num_fields) = self
            .env
            .get_constructor(ctor_name)
            .map(|info| info.num_fields as usize)
        else {
            return Ok(None);
        };
        if num_fields == 0 || rows.is_empty() || rows.iter().any(|(p, _)| p.len() != num_fields) {
            return Ok(None);
        }
        let field_tys = self.compute_ctor_field_types(ctor_name, scrutinee_ty)?;
        if field_tys.len() != num_fields || field_tys.iter().any(Expr::has_loose_bvars) {
            return Ok(None);
        }
        // The tree is only read, never elaborated, so its column names need
        // not be fresh.
        let field_names: Vec<SurfaceName> = (0..num_fields)
            .map(|idx| SurfaceName::from_name(Name::anon().str("__rreach").num(idx as u64)))
            .collect();
        let split_rows: Vec<ColumnSplitRow> = rows
            .iter()
            .enumerate()
            .map(|(origin, (pats, body))| (pats.clone(), Vec::new(), body.clone(), origin))
            .collect();
        let mut reach = RowReach::new(split_rows.len());
        Ok(self
            .build_column_split_surface(&field_names, &field_tys, &split_rows, &mut reach)?
            .map(|_| reach))
    }

    /// The Track G3 fallback chain for the `T.rec` minor of `ctor_name`: fold
    /// the `covering` arms (source order) lowest-priority first, so each
    /// higher-priority arm's nested dispatch falls back to the minor already
    /// built for the same constructor. A catch-all binds all `num_fields`
    /// fields as wildcards.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::infer) fn fold_nested_head_rec_chain(
        &mut self,
        ctor_name: &Name,
        num_fields: usize,
        covering: &[(usize, &clean_parser::SurfaceMatchArm, bool)],
        type_name: &SurfaceName,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        extra_param_info: &[ExtraParamBinding],
    ) -> Result<Option<Expr>, ElabError> {
        let mut compiled: Option<Expr> = None;
        for &(arm_idx, arm, is_catch_all) in covering.iter().rev() {
            let alt = if is_catch_all {
                // A genuine catch-all minor: build the body (which may itself
                // recurse — it needs the IH too) wrapped in the constructor's
                // field binders followed by its IH binders, exactly as a
                // `T.rec` minor premise expects. `elaborate_rec_arm` over a
                // freshly synthesized all-wildcard sub-pattern installs the IHs
                // and routes a self-call on the recursive field to them.
                let wildcard_pats = vec![SurfacePattern::Wildcard; num_fields];
                self.elaborate_rec_arm(
                    &SurfaceName::from_name(ctor_name.clone()),
                    &wildcard_pats,
                    &arm.body,
                    scrutinee_ty,
                    branch_ty,
                    arm_idx,
                    extra_param_info,
                )?
            } else {
                let SurfacePattern::Ctor(pat_ctor, sub_pats) = &arm.pattern else {
                    return Ok(None);
                };
                let full_ctor = self.ctor_pattern_full_name(pat_ctor, type_name);
                let normalized_sub_pats = self.expand_implicit_ctor_field_patterns(
                    "match arm pattern",
                    &full_ctor,
                    sub_pats,
                )?;
                if normalized_sub_pats.is_empty() {
                    // Nullary constructor: plain value, no field/IH binders.
                    let arm_ty =
                        self.dependent_arm_branch_ty(branch_ty, &full_ctor, scrutinee_ty, &[])?;
                    let arm_body =
                        self.elaborate_with_expected_type(&arm.body, Some(arm_ty.clone()))?;
                    wrap_with_extra_params(arm_body, extra_param_info)
                } else {
                    self.elaborate_rec_arm_with_fallback(
                        &full_ctor,
                        &normalized_sub_pats,
                        &arm.body,
                        scrutinee_ty,
                        branch_ty,
                        arm_idx,
                        extra_param_info,
                        compiled.as_ref(),
                    )?
                }
            };
            compiled = Some(alt);
        }
        Ok(compiled)
    }

    /// Compile the `T.rec` minor for `ctor_name` from `rows` (the arms that
    /// cover it, in source order, none of them a catch-all) as one field
    /// decision tree. `Ok(None)` when the shape is outside this lowering's
    /// envelope (a dependent field type, a sub-pattern the decision-tree
    /// builder does not take, a minor that would need a compiler-minted
    /// `sorry`); `Err` when
    /// elaborating the tree failed. Either way every local/meta/level effect
    /// is rolled back.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::infer) fn compile_rec_ctor_field_column_split(
        &mut self,
        ctor_name: &Name,
        rows: &[CtorFieldRow],
        first_arm_idx: usize,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        extra_param_info: &[ExtraParamBinding],
    ) -> Result<Option<Expr>, ElabError> {
        self.with_optional_temporary_local_scope(|this| {
            this.compile_rec_ctor_field_column_split_inner(
                ctor_name,
                rows,
                first_arm_idx,
                scrutinee_ty,
                branch_ty,
                extra_param_info,
            )
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn compile_rec_ctor_field_column_split_inner(
        &mut self,
        ctor_name: &Name,
        rows: &[CtorFieldRow],
        first_arm_idx: usize,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        extra_param_info: &[ExtraParamBinding],
    ) -> Result<Option<Expr>, ElabError> {
        let Some(ctor_info) = self.env.get_constructor(ctor_name).cloned() else {
            return Ok(None);
        };
        let num_fields = ctor_info.num_fields as usize;
        if num_fields == 0 || rows.is_empty() || rows.iter().any(|(p, _)| p.len() != num_fields) {
            return Ok(None);
        }
        // The decision tree is built BEFORE the fields are bound (the minor's
        // field binders are opened by `elaborate_rec_arm`), so its column
        // types must not mention earlier fields. A dependent field telescope
        // stays with the legacy lowering.
        let field_tys = self.compute_ctor_field_types(ctor_name, scrutinee_ty)?;
        if field_tys.len() != num_fields || field_tys.iter().any(Expr::has_loose_bvars) {
            return Ok(None);
        }
        // Field names end in a numeric component, so no source identifier can
        // name (or capture) them; the salt keeps nested splits apart.
        let salt = self.next_fvar;
        let field_names: Vec<SurfaceName> = (0..num_fields)
            .map(|idx| {
                SurfaceName::from_name(Name::anon().str(format!("__rsplit_{salt}")).num(idx as u64))
            })
            .collect();
        let split_rows: Vec<ColumnSplitRow> = rows
            .iter()
            .enumerate()
            .map(|(origin, (pats, body))| (pats.clone(), Vec::new(), body.clone(), origin))
            .collect();
        // Redundancy was decided on this same tree before the chain ran
        // (`rec_ctor_field_split_reach`); this build only elaborates it.
        let mut reach = RowReach::new(split_rows.len());
        let Some(tree) =
            self.build_column_split_surface(&field_names, &field_tys, &split_rows, &mut reach)?
        else {
            return Ok(None);
        };
        // Bind the fields under the tree's column names and their induction
        // hypotheses in recursor-minor order, then elaborate the tree as the
        // minor's body. Every field is named, so every recursive field gets
        // an IH entry and a pattern variable aliasing it reaches that IH.
        let field_pats: Vec<SurfacePattern> =
            field_names.into_iter().map(SurfacePattern::Var).collect();
        let minor = self.elaborate_rec_arm(
            &SurfaceName::from_name(ctor_name.clone()),
            &field_pats,
            &tree,
            scrutinee_ty,
            branch_ty,
            first_arm_idx,
            extra_param_info,
        )?;
        // Only a sorry the compiler minted (synthetic) marks a minor this
        // lowering cannot build. A user-written `sorry` arm is the program
        // itself and stays in the term for the audit to report, as in Lean.
        if minor.has_synthetic_sorry() {
            return Ok(None);
        }
        Ok(Some(minor))
    }
}
