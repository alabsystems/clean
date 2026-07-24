// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Term-level `▸` (subst) elaboration — Lean's `elabSubst`
//! (`Lean/Elab/BuiltinNotation.lean:457`, v4.30.0-rc2) ported to Clean.
//!
//! The parser desugars `heq ▸ h` to `App(Ident("Eq.rec"), [heq, h])`
//! (`clean-parser/src/grammar/expr_operators.rs::subst_expr`). A plain
//! application cannot elaborate that shape: `@Eq.rec` takes the minor premise
//! BEFORE the equation, and its motive must be inferred from the *expected
//! type*. `elab_app_inner` therefore re-routes the exact desugar shape (head
//! `Ident("Eq.rec")`, exactly two positional args, non-explicit mode) here.
//! A source-level dotted `Eq.rec …` parses as a projection-headed application
//! (the lexer does not join `.`-separated names), so the re-route cannot
//! capture hand-written `Eq.rec` calls.
//!
//! Orientation fidelity (the silent-wrong guard): in computational cast
//! positions (`h ▸ (v : F a) : F b`) a wrong-orientation motive would produce
//! a well-typed but WRONG value, which the kernel re-check cannot catch. This
//! arm replicates Lean's orientation search exactly:
//!
//! * expected type known (`elabSubst:478-489`): abstract occurrences of `rhs`
//!   FIRST (:479); if only `lhs` occurs, `symm` the equation and swap the
//!   sides (:481-485); the cast source is `expected[rhs ↦ lhs]` (:486);
//! * value's type mentions `rhs` but the direct check fails
//!   (`elabSubst:490-505`): pre-cast the value backwards along `symm heq`,
//!   then cast forward with the main motive;
//! * no expected type (`elabSubst:524-537`): abstract the value's type at
//!   `lhs` first (:527), falling back to `rhs` + `symm` (:528-533);
//! * a motive that is not type-correct is REJECTED loudly (:506/:535) — Lean's
//!   `by subst …; exact …` tactic fallback (:508-519) is descoped in Clean, so
//!   those programs fail loud instead of falling back; the motive is never
//!   guessed.
//!
//! Soundness: the resulting `@Eq.rec` term is ordinary kernel syntax and is
//! re-checked by the kernel on registration; this arm can only affect *which*
//! well-typed term is produced, which is exactly why the orientation search
//! above must be Lean-faithful.

use clean_kernel::{BinderInfo, Expr, ExprKind, Level, Name};
use clean_parser::SurfaceExpr;

use super::ElabCtx;
use crate::error::ElabError;
use crate::tactic::bvar_ops::{instantiate, lift_bvars};
use crate::tactic::equality::{
    abstract_over, contains_expr, find_defeq_subterm_with, match_equality,
};
use crate::unify::MetaState;

/// `@Eq.rec.{u_motive, u_alpha} α a motive minor b heq` — Clean's kernel uses
/// Lean's recursor layout (params `α a`, then motive, minor, index `b`, major
/// `heq`) and Lean's level order (motive sort first, carrier sort second).
#[allow(clippy::too_many_arguments)] // one parameter per @Eq.rec argument slot
fn mk_eq_rec(
    u_motive: Level,
    u_alpha: Level,
    alpha: Expr,
    a: Expr,
    motive: Expr,
    minor: Expr,
    b: Expr,
    heq: Expr,
) -> Expr {
    let head = Expr::const_(Name::from_string("Eq.rec"), vec![u_motive, u_alpha]);
    let mut e = Expr::app(head, alpha);
    e = Expr::app(e, a);
    e = Expr::app(e, motive);
    e = Expr::app(e, minor);
    e = Expr::app(e, b);
    Expr::app(e, heq)
}

/// `@Eq.symm.{u} α lhs rhs heq : rhs = lhs`.
fn mk_eq_symm(u: &Level, alpha: &Expr, lhs: &Expr, rhs: &Expr, heq: Expr) -> Expr {
    let head = Expr::const_(Name::from_string("Eq.symm"), vec![u.clone()]);
    let mut e = Expr::app(head, alpha.clone());
    e = Expr::app(e, lhs.clone());
    e = Expr::app(e, rhs.clone());
    Expr::app(e, heq)
}

/// Lean's `mkMotive` (`elabSubst:473-476`): `fun (x : α) (h : base = x) =>
/// B[x]` where `B` is `type_with_loose_bvar` (loose bvar 0 = the abstracted
/// occurrences). Under the two motive binders the abstracted occurrence sits
/// at bvar 1 (`x`), so the loose indices are lifted by one.
fn mk_subst_motive(u_eq: &Level, alpha: &Expr, base: &Expr, type_with_loose_bvar: &Expr) -> Expr {
    let body = lift_bvars(type_with_loose_bvar, 1);
    let eq_head = Expr::const_(Name::from_string("Eq"), vec![u_eq.clone()]);
    let eq_ty = Expr::app(
        Expr::app(Expr::app(eq_head, alpha.clone()), base.clone()),
        Expr::bvar(0),
    );
    Expr::lam(
        BinderInfo::Default,
        alpha.clone(),
        Expr::lam(BinderInfo::Default, eq_ty, body),
    )
}

/// The `@Eq α lhs rhs` decomposition of an equation type: carrier, sides, and
/// the carrier's universe level.
struct EqSides {
    alpha: Expr,
    lhs: Expr,
    rhs: Expr,
    u: Level,
}

impl<'a> ElabCtx<'a> {
    /// Elaborate the `▸` desugar `App(Ident("Eq.rec"), [heq, h])`.
    ///
    /// Returns `Ok(None)` when the first operand's type is not an equality —
    /// subst semantics are then impossible and the caller falls through to the
    /// generic application path, whose failure is equally loud (Lean's
    /// `elabSubst` errors "equality expected" at the same point, :464-468).
    /// Every other failure is a hard, loud `Err`.
    pub(in crate::infer) fn try_elab_subst(
        &mut self,
        heq_stx: &SurfaceExpr,
        h_stx: &SurfaceExpr,
    ) -> Result<Option<Expr>, ElabError> {
        // Lean :458 `tryPostponeIfHasMVars?` — Clean cannot postpone; take the
        // expected type as currently known (metas instantiated). A still-bare
        // metavariable gives the occurrence search nothing to abstract, so
        // route it through the no-expected-type branch and let the caller
        // unify the inferred result type with the meta afterwards.
        let expected = self.current_expected_type.clone().and_then(|ty| {
            let ty = self.metas.instantiate(&ty);
            let ty = self.metas.instantiate_levels(&ty);
            match ty.kind() {
                ExprKind::FVar(id) if MetaState::from_fvar(*id).is_some() => None,
                _ => Some(ty),
            }
        });

        // Lean :461-462 — elaborate the equation with NO expected type.
        let heq = self.elaborate_with_expected_type(heq_stx, None)?;
        let heq_ty = self.infer_type(&heq)?;
        let Some(eq) = self.match_eq_type(&heq_ty) else {
            return Ok(None);
        };

        match expected {
            Some(expected) => self
                .elab_subst_with_expected(heq, eq, &expected, h_stx)
                .map(Some),
            None => self.elab_subst_infer(heq, eq, h_stx).map(Some),
        }
    }

    /// Match `ty` (whnf'ing if needed, mirroring `Meta.matchEq?`) against
    /// `@Eq α lhs rhs`.
    fn match_eq_type(&self, ty: &Expr) -> Option<EqSides> {
        let (alpha, lhs, rhs, levels) = match_equality(ty)
            .or_else(|_| match_equality(&self.whnf(ty)))
            .ok()?;
        let u = levels.into_iter().next().unwrap_or_else(Level::zero);
        Some(EqSides { alpha, lhs, rhs, u })
    }

    /// Clean's `kabstract` approximation (`elabSubst:479/:481/:495`): abstract
    /// every syntactic occurrence of `side` in `ty` to a loose bvar; when
    /// `side` does not occur syntactically, fall back to the first def-eq
    /// subterm (the same head-keyed search `rw` uses) and abstract that
    /// subterm's occurrences. `None` when nothing occurs (Lean's
    /// `hasLooseBVars` guard).
    fn abstract_occurrences(&self, ty: &Expr, side: &Expr) -> Option<Expr> {
        if contains_expr(ty, side) {
            return Some(abstract_over(ty, side));
        }
        let surface = find_defeq_subterm_with(ty, side, &mut |a, b| self.is_def_eq(a, b))?;
        Some(abstract_over(ty, &surface))
    }

    /// Lean's `isTypeCorrect motive` (`elabSubst:506/:501/:535`): strict
    /// (`infer_only = false`) kernel inference over the assembled motive.
    fn motive_type_correct(&self, motive: &Expr) -> bool {
        self.infer_type_full(motive).is_ok()
    }

    /// `elabSubst:478-523` — the expected type is known.
    fn elab_subst_with_expected(
        &mut self,
        heq: Expr,
        eq: EqSides,
        expected: &Expr,
        h_stx: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        let EqSides { alpha, lhs, rhs, u } = eq;

        // Orientation search (:479-485): abstract `rhs` occurrences FIRST;
        // when only `lhs` occurs, `symm` the equation and swap the sides. This
        // ordering is semantically load-bearing for computational casts — it
        // decides which occurrences the cast rewrites when both sides occur.
        let (heq, lhs, rhs, expected_abst) =
            if let Some(abst) = self.abstract_occurrences(expected, &rhs) {
                (heq, lhs, rhs, abst)
            } else if let Some(abst) = self.abstract_occurrences(expected, &lhs) {
                let symm = mk_eq_symm(&u, &alpha, &lhs, &rhs, heq);
                (symm, rhs, lhs, abst)
            } else {
                return Err(ElabError::InvalidSubst {
                    detail: format!(
                        "the expected result type of the cast is `{expected}`, but neither \
                         the left hand side `{lhs}` nor the right hand side `{rhs}` of the \
                         equality occurs in it"
                    ),
                });
            };

        // :486 — the cast source type: expected with the abstracted
        // occurrences instantiated at `lhs`.
        let h_expected = instantiate(&expected_abst, &lhs);

        // :487-505 — elaborate the value against the cast-source type; if the
        // result does not land there, try the value's-own-type pre-cast.
        let h = match self.elab_value_ensure(h_stx, &h_expected) {
            Ok(h) => h,
            Err(primary_err) => self.elab_subst_precast(
                &heq,
                &u,
                &alpha,
                &lhs,
                &rhs,
                h_stx,
                &h_expected,
                primary_err,
            )?,
        };

        // :506-507 — the main motive; :508-519 (`by subst`) is descoped, so a
        // non-type-correct motive fails loud here.
        let motive = mk_subst_motive(&u, &alpha, &lhs, &expected_abst);
        if !self.motive_type_correct(&motive) {
            return Err(ElabError::InvalidSubst {
                detail: "failed to compute motive for the substitution".to_string(),
            });
        }
        let u_motive = self.infer_sort(expected)?;
        // :523 `mkEqRec motive h heq`.
        Ok(mk_eq_rec(u_motive, u, alpha, lhs, motive, h, rhs, heq))
    }

    /// Elaborate the cast value against the cast-source type and verify it
    /// landed there (Lean's `elabTerm` + `ensureHasType`, :488-489).
    fn elab_value_ensure(
        &mut self,
        h_stx: &SurfaceExpr,
        h_expected: &Expr,
    ) -> Result<Expr, ElabError> {
        let h = self.elaborate_with_expected_type(h_stx, Some(h_expected.clone()))?;
        let h_ty = self.infer_type(&h)?;
        if self.is_def_eq(&h_ty, h_expected) {
            Ok(h)
        } else {
            Err(ElabError::TypeMismatch {
                expected: h_expected.to_string(),
                actual: h_ty.to_string(),
            })
        }
    }

    /// `elabSubst:490-505` — the catch path: "if `rhs` occurs in hType, we try
    /// to apply `heq` to `h` too". When the value's own type mentions `rhs`
    /// and rewriting it to `lhs` reaches the cast-source type, pre-cast the
    /// value backwards along `symm heq`; the caller then applies the main
    /// motive to the pre-cast value.
    ///
    /// `primary_err` is the direct-check failure; it is re-raised whenever
    /// this path does not apply (Lean's `throw ex`, :497/:500). Deviation from
    /// Lean: the value is re-elaborated without an expected type (Clean's
    /// checking-mode failures do not hand back a term), which only affects
    /// elaboration side effects, not the accepted language.
    #[allow(clippy::too_many_arguments)] // mirrors Lean's elabSubst catch-path state
    fn elab_subst_precast(
        &mut self,
        heq: &Expr,
        u: &Level,
        alpha: &Expr,
        lhs: &Expr,
        rhs: &Expr,
        h_stx: &SurfaceExpr,
        h_expected: &Expr,
        primary_err: ElabError,
    ) -> Result<Expr, ElabError> {
        let Ok(h) = self.elaborate_with_expected_type(h_stx, None) else {
            return Err(primary_err);
        };
        let h_ty = self.infer_type(&h)?;
        // :495-497 — `rhs` must occur in the value's type.
        let Some(h_ty_abst) = self.abstract_occurrences(&h_ty, rhs) else {
            return Err(primary_err);
        };
        // :498-500 — rewriting those occurrences to `lhs` must reach the
        // cast-source type.
        let h_ty_new = instantiate(&h_ty_abst, lhs);
        if !self.is_def_eq(h_expected, &h_ty_new) {
            return Err(primary_err);
        }
        // :501-504 — motive based at `rhs`; cast backwards along `symm heq`.
        let motive = mk_subst_motive(u, alpha, rhs, &h_ty_abst);
        if !self.motive_type_correct(&motive) {
            // Lean records `badMotive?` and later falls back to `by subst`
            // (:508-519), which Clean descopes: fail loud.
            return Err(ElabError::InvalidSubst {
                detail: "failed to compute motive for the substitution".to_string(),
            });
        }
        let u_motive = self.infer_sort(&h_ty)?;
        let symm = mk_eq_symm(u, alpha, lhs, rhs, heq.clone());
        Ok(mk_eq_rec(
            u_motive,
            u.clone(),
            alpha.clone(),
            rhs.clone(),
            motive,
            h,
            lhs.clone(),
            symm,
        ))
    }

    /// `elabSubst:524-537` — no expected type: infer the result by
    /// transporting the value's type along the equation. Note the orientation
    /// order is REVERSED relative to the expected-type branch: `lhs` first
    /// (:527), then `rhs` + `symm` (:528-533) — the value sits at the
    /// equation's source, not at the cast target.
    fn elab_subst_infer(
        &mut self,
        heq: Expr,
        eq: EqSides,
        h_stx: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        let EqSides { alpha, lhs, rhs, u } = eq;
        let h = self.elaborate_with_expected_type(h_stx, None)?;
        let h_ty = self.infer_type(&h)?;

        let (heq, lhs, rhs, h_ty_abst) = if let Some(abst) = self.abstract_occurrences(&h_ty, &lhs)
        {
            (heq, lhs, rhs, abst)
        } else if let Some(abst) = self.abstract_occurrences(&h_ty, &rhs) {
            let symm = mk_eq_symm(&u, &alpha, &lhs, &rhs, heq);
            (symm, rhs, lhs, abst)
        } else {
            return Err(ElabError::InvalidSubst {
                detail: format!(
                    "neither side of the equality (`{lhs}` / `{rhs}`) is mentioned in the \
                     type `{h_ty}` of the value being cast"
                ),
            });
        };

        let motive = mk_subst_motive(&u, &alpha, &lhs, &h_ty_abst);
        if !self.motive_type_correct(&motive) {
            return Err(ElabError::InvalidSubst {
                detail: "failed to compute motive for the substitution".to_string(),
            });
        }
        let u_motive = self.infer_sort(&h_ty)?;
        Ok(mk_eq_rec(u_motive, u, alpha, lhs, motive, h, rhs, heq))
    }

    /// Transport an already-elaborated value `h` along an already-elaborated
    /// equality proof `heq` (`heq ▸ h`), mirroring the no-expected-type
    /// orientation search of `elab_subst_infer` but for a value that is already
    /// a term (not surface syntax).
    ///
    /// Used by the `calc` elaborator to compose an equality step with a
    /// non-equality relation step: there are no carrier `le_of_le_of_eq`-style
    /// transitivity lemmas, and the Lean-idiomatic composition of `x R b` with
    /// `b = c` (or `a = b` with `b R c`) IS exactly this rewrite. Returns
    /// `Ok(None)` when `heq`'s type is not an equality or neither side occurs in
    /// `h`'s type / the motive is not type-correct — the caller then falls
    /// through to its other composition paths. The resulting `@Eq.rec` term is
    /// ordinary kernel syntax and is re-checked by the kernel on registration.
    ///
    /// Returns `(cast, result_type)` where `result_type` is the SURFACE form of
    /// the transported type (`h`'s type with the transported endpoint replaced),
    /// not the un-reduced `@Eq.rec` inferred type — so the caller (calc) can feed
    /// it straight into the next step's relation matcher.
    pub(in crate::infer) fn subst_transport_elaborated(
        &mut self,
        heq: Expr,
        h: Expr,
    ) -> Result<Option<(Expr, Expr)>, ElabError> {
        let heq_ty = self.infer_type(&heq)?;
        let Some(eq) = self.match_eq_type(&heq_ty) else {
            return Ok(None);
        };
        let EqSides { alpha, lhs, rhs, u } = eq;
        let h_ty = self.infer_type(&h)?;

        // Orientation (mirrors `elab_subst_infer`): abstract `lhs` occurrences
        // first, else `rhs` + `symm`. For a `x R b` value cast along `b = c`,
        // `lhs = b` occurs → transport `b → c`. For a `b R c` value cast along
        // `a = b`, `lhs = a` does not occur, so `rhs = b` + `symm` transports
        // `b → a`.
        let (heq, lhs, rhs, h_ty_abst) = if let Some(abst) = self.abstract_occurrences(&h_ty, &lhs)
        {
            (heq, lhs, rhs, abst)
        } else if let Some(abst) = self.abstract_occurrences(&h_ty, &rhs) {
            let symm = mk_eq_symm(&u, &alpha, &lhs, &rhs, heq);
            (symm, rhs, lhs, abst)
        } else {
            return Ok(None);
        };

        let motive = mk_subst_motive(&u, &alpha, &lhs, &h_ty_abst);
        if !self.motive_type_correct(&motive) {
            return Ok(None);
        }
        let u_motive = self.infer_sort(&h_ty)?;
        // Surface result type: `h_ty` with the transported endpoint replaced —
        // `instantiate(h_ty_abst, rhs)` fills the abstracted hole with the target
        // side, preserving the surface `LE.le`/`LT.lt`/… head.
        let result_ty = instantiate(&h_ty_abst, &rhs);
        let cast = mk_eq_rec(u_motive, u, alpha, lhs, motive, h, rhs, heq);
        Ok(Some((cast, result_ty)))
    }
}
