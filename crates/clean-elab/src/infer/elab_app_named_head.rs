// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Named arguments on a head that is not a declared constant with its own
//! binders: Lean matches `(x := e)` against the binder names of the head's
//! TYPE after `whnf` (`ElabAppArgs`, `Lean/Elab/App.lean:803-815`, with
//! `normalizeFunType`), whatever the head is. Called from
//! `resolve_named_args` (`elab_app_support.rs`).

use super::*;
use crate::tactic::op_projection::head_beta;

impl<'a> ElabCtx<'a> {
    /// The named-argument slots of a head whose type UNFOLDS to a `∀`:
    /// `h (a₁ := fun _ ↦ b₁) (a₂ := fun _ ↦ b₂) e` with `h : Injective (g ∘ ·)`
    /// names binders that exist only in `Function.Injective`'s value
    /// (`Function.injective_comp_left_iff`, `Mathlib/Logic/Function/Basic.lean`).
    ///
    /// The kernel keeps no binder names, so they come from the table the
    /// importer and the `def` elaborator fill
    /// (`Environment::get_value_forall_binder_names`): the head's type is unfolded
    /// one definition at a time, as `resolve_field_through_consumed_implicits`
    /// does, and when a step lands on a `∀` the names are the ones recorded
    /// for the definition just unfolded — provided it was applied to exactly
    /// as many arguments as its value has lambdas, so the `∀` reached IS the
    /// recorded one. Binder kinds are read off the unfolded kernel type.
    ///
    /// A head whose type already IS a `∀` is named by the surface `∀` that
    /// type was elaborated from: first the one a binder of the local itself
    /// wrote (`h : ∀ {n m : Nat}, …`,
    /// [`Self::note_local_forall_binder_names`]), then any surface `∀` of this
    /// declaration that elaborated to exactly that kernel term (`intro h`,
    /// `fun h => …` against the statement's `∀`,
    /// [`Self::note_surface_forall_binder_names`]). The second reading is by
    /// TYPE, so where Lean would name such a head after a `∀` written in
    /// another declaration, the names a structurally identical `∀` of this
    /// one spelled are used instead; positions are read off the same kernel
    /// telescope either way.
    ///
    /// `None` when the names are not known: a `∀` this declaration never
    /// spelled (an instantiated lemma statement, a recursor's hypothesis) or
    /// spelled with two different name lists, a head that does not unfold to
    /// a `∀`, or an unrecorded definition. The caller then refuses loudly; a
    /// named argument is never bound by position.
    pub(in crate::infer) fn named_arg_slots_from_head_type(
        &self,
        func_expr: &Expr,
    ) -> Option<Vec<(Option<SurfaceName>, Option<BinderInfo>)>> {
        // A δ-chain in a well-formed environment is finite; the bound only
        // keeps a malformed one from looping.
        const MAX_UNFOLD_STEPS: usize = 64;
        let ty = self.infer_type(func_expr).ok()?;
        let mut ty = head_beta(&self.metas.instantiate(&ty));
        if let Some(slots) = self
            .named_arg_slots_of_local_forall(func_expr, &ty)
            .or_else(|| self.named_arg_slots_of_surface_forall(&ty))
        {
            return Some(slots);
        }
        for _ in 0..MAX_UNFOLD_STEPS {
            let ExprKind::Const(head, _) = ty.get_app_fn().kind() else {
                return None;
            };
            let shape = self.env.get_value_forall_binder_names(head).cloned();
            let applied = ty.get_app_num_args();
            let unfolded = self.unfold_definition_step(&ty)?;
            if matches!(unfolded.kind(), ExprKind::Pi(..)) {
                let shape = shape.filter(|shape| shape.lambdas == applied)?;
                let kinds = Self::pi_telescope_binder_infos(&unfolded, shape.names.len());
                if kinds.len() != shape.names.len() {
                    return None;
                }
                return Some(
                    shape
                        .names
                        .into_iter()
                        .zip(kinds)
                        .map(|(name, kind)| {
                            let name = (!name.is_anon()).then(|| SurfaceName::from_name(name));
                            (name, Some(kind))
                        })
                        .collect(),
                );
            }
            ty = unfolded;
        }
        None
    }

    /// Record the binder names of a local whose type is a `∀` written in
    /// place: `(h : ∀ {n m : Nat}, n = m → m = n)`, `have h : ∀ x, p x := …`,
    /// `fun (h : ∀ ⦃a b⦄, …) => …`. Lean matches `h (n := 1)` against
    /// `fType.bindingName!` (`Lean/Elab/App.lean:803-815`); Clean's kernel
    /// `Pi` keeps no name, so the surface binder is the only place they
    /// exist.
    ///
    /// Recorded only when the elaborated type really is a `∀` of the same
    /// binder kind at every surface position (an elaborator that wrapped or
    /// rewrote the type records nothing), and together with that type: the
    /// reader compares it with the local's current type, so an entry left
    /// behind by a popped local can never name the binders of a later local
    /// that reuses the id with a different type.
    pub(in crate::infer) fn note_local_forall_binder_names(
        &mut self,
        fvar: FVarId,
        surface_ty: Option<&SurfaceExpr>,
        ty: &Expr,
    ) {
        let Some(names) =
            surface_ty.and_then(|surface_ty| self.checked_forall_names(surface_ty, ty))
        else {
            return;
        };
        self.local_forall_binder_names
            .insert(fvar, (ty.clone(), names));
    }

    /// The binder names of the surface `∀`/`→` telescope `surface_ty`, when
    /// the kernel type it elaborated to really is a `∀` of the same binder
    /// kind at every surface position and at least one binder has a name a
    /// named argument could spell.
    fn checked_forall_names(&self, surface_ty: &SurfaceExpr, ty: &Expr) -> Option<Vec<Name>> {
        let telescope = crate::value_binder_names::surface_forall_telescope(surface_ty);
        if telescope.iter().all(|(name, _)| name.is_anon()) {
            // Nothing a named argument could spell (`p → q`, or no `∀`).
            return None;
        }
        let kinds = Self::pi_telescope_binder_infos(&self.metas.instantiate(ty), telescope.len());
        if kinds.len() != telescope.len()
            || kinds.iter().zip(&telescope).any(|(k, (_, info))| k != info)
        {
            return None;
        }
        Some(telescope.into_iter().map(|(name, _)| name).collect())
    }

    /// Record the binder names of a surface `∀` beside the kernel `∀` it
    /// elaborated to, for a head whose type is that `∀` without any binder of
    /// its own having spelled it: `intro h` on a goal `(∀ {n m : Nat}, …) → …`
    /// and `fun h => …` typed by the expected type both hand `h` the
    /// statement's `∀`, whose names Lean keeps in the kernel term and Clean
    /// does not. Read by [`Self::named_arg_slots_of_surface_forall`].
    pub(in crate::infer) fn note_surface_forall_binder_names(
        &mut self,
        surface_ty: &SurfaceExpr,
        ty: &Expr,
    ) {
        /// A declaration that elaborates more surface `∀`s than this stops
        /// recording; the reader then finds nothing and the call stays the
        /// loud refusal it was.
        const MAX_RECORDED: usize = 4096;
        if self.surface_forall_binder_names.len() >= MAX_RECORDED {
            return;
        }
        if let Some(names) = self.checked_forall_names(surface_ty, ty) {
            self.surface_forall_binder_names.push((ty.clone(), names));
        }
    }

    /// The names recorded for a surface `∀` that elaborated to exactly `ty`.
    ///
    /// The kernel cannot tell `∀ {n m}, n = m → m = n` from
    /// `∀ {m n}, m = n → n = m`, so when two recorded spellings of the same
    /// kernel `∀` disagree on the names the answer is `None`: the call is
    /// refused rather than bound by the wrong spelling's positions.
    pub(in crate::infer) fn named_arg_slots_of_surface_forall(
        &self,
        ty: &Expr,
    ) -> Option<Vec<(Option<SurfaceName>, Option<BinderInfo>)>> {
        if !matches!(ty.kind(), ExprKind::Pi(..)) {
            return None;
        }
        let mut found: Option<&Vec<Name>> = None;
        for (recorded_ty, names) in &self.surface_forall_binder_names {
            if head_beta(&self.metas.instantiate(recorded_ty)) != *ty {
                continue;
            }
            match found {
                Some(earlier) if earlier != names => return None,
                _ => found = Some(names),
            }
        }
        Self::slots_of_names(found?, ty)
    }

    /// Named-argument slots for `names` over the leading binders of `ty`,
    /// binder kinds read off the kernel type.
    fn slots_of_names(
        names: &[Name],
        ty: &Expr,
    ) -> Option<Vec<(Option<SurfaceName>, Option<BinderInfo>)>> {
        let kinds = Self::pi_telescope_binder_infos(ty, names.len());
        if kinds.len() != names.len() {
            return None;
        }
        Some(
            names
                .iter()
                .zip(kinds)
                .map(|(name, kind)| {
                    let name = (!name.is_anon()).then(|| SurfaceName::from_name(name.clone()));
                    (name, Some(kind))
                })
                .collect(),
        )
    }

    /// The slots [`Self::note_local_forall_binder_names`] recorded for the
    /// local `func_expr`, when its type is still the recorded one.
    fn named_arg_slots_of_local_forall(
        &self,
        func_expr: &Expr,
        ty: &Expr,
    ) -> Option<Vec<(Option<SurfaceName>, Option<BinderInfo>)>> {
        let ExprKind::FVar(fvar) = func_expr.kind() else {
            return None;
        };
        let (recorded_ty, names) = self.local_forall_binder_names.get(fvar)?;
        if head_beta(&self.metas.instantiate(recorded_ty)) != *ty {
            return None;
        }
        Self::slots_of_names(names, ty)
    }
}
