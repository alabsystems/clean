// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Simp lemmas built from a LOCAL hypothesis or an arbitrary proof term:
//! Lean's `mkSimpTheorems` preprocessing (`p = True`, `¬p ↦ p = False`, the
//! halves of a conjunction) and the proof builders it needs.
//!
//! Split out of `lemmas.rs` to keep that file under the paragon 1000-line
//! limit.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

use super::expr::{collect_binder_types_in_conclusion, leading_pi_binder_count};
use super::lemmas::{extract_local_equality_template, mk_local_proof_template};
use super::types::{SimpIndexMode, SimpLemma};
use crate::tactic::core::{Goal, ProofState};

/// A NON-equational local `h : P` (under binders, `h : ∀ x, P x`) as the
/// rewrite Lean's `mkSimpTheorems` makes of it: `P = True` proved by
/// `eq_true h`, `P = False` for `h : ¬P` (`eq_false h`), and `a = b` for
/// `h : a ↔ b` (`propext h`). Spelled from the prelude's `propext`,
/// `Iff.intro`, `True.intro` and `False.elim` — `eq_true`/`eq_false` exist
/// only after `import Init`. Measured 2026-09-11: `simpa only [H] using h₂`
/// with `H : h₁` (`Prop.exists_iff`, `Prop.forall_iff` in
/// `Mathlib/Logic/Basic.lean`) rewrote nothing because the hypothesis was
/// silently skipped as "not an equality".
///
/// A conjunction `h : P ∧ Q` (under binders too) is SPLIT into the rules of
/// `P` (proved by `h.1`) and of `Q` (`h.2`), recursively, exactly as a global
/// theorem's is — Lean's `preprocess` is one function for both
/// (`SimpTheorems.lean`, `type.and?`), and `prop_lemmas::preprocess` is
/// Clean's. Measured 2026-09-20: `simp only [h]` with `h : a ∧ b` made no
/// progress on the goal `a`, which pinned v4.30.0-rc2 closes; the single rule
/// `(a ∧ b) = True` built here matches neither conjunct.
///
/// A disequality `h : a ≠ b` goes through the same function: it becomes
/// `(a = b) = False` (Lean's `type.ne?` branch, with its `Bool`-literal
/// special case), never `(a ≠ b) = True`. Measured 2026-11-13 against pinned
/// Lean 4.8.0 and v4.30.0-rc2: `simp [h]` with `h : a ≠ 0` closes the goal
/// `a ≠ 0` (through `ne_eq`) and `simp only [h]` refuses it.
///
/// Only Prop-valued locals qualify (the local's type must live in `Prop`,
/// which `∀`-quantified propositions do too); anything else yields no rule.
pub(super) fn local_prop_hyp_lemma(
    state: &ProofState,
    goal: &Goal,
    decl: &crate::tactic::LocalDecl,
    priority: u32,
) -> Vec<SimpLemma> {
    let hyp_ty = state.metas.instantiate(&decl.ty);
    if !type_is_prop(state, goal, &hyp_ty) {
        return Vec::new();
    }
    prop_simp_lemmas_from_proof(
        state,
        decl.name.name(),
        &Expr::fvar(decl.fvar),
        &hyp_ty,
        priority,
    )
}

/// Whether `ty` is a proposition in `goal`'s context.
pub(super) fn type_is_prop(state: &ProofState, goal: &Goal, ty: &Expr) -> bool {
    let Ok(sort) = state.infer_type(goal, ty) else {
        return false;
    };
    let sort = state.whnf(goal, &sort);
    matches!(sort.kind(), ExprKind::Sort(l) if l.is_zero())
}

/// The rules Lean's `preprocess` makes of a PROOF of a non-equational
/// proposition — the body of [`local_prop_hyp_lemma`], over an arbitrary
/// proof term rather than a local hypothesis' fvar.
///
/// `proof` may carry loose de Bruijn indices (a term simp argument's
/// abstracted metavariables); they are lifted over the statement's own
/// binders exactly as the fvar case is, so the caller's index layout is
/// preserved.
///
/// REQUIRES: `ty` is a proposition (the caller checked with [`type_is_prop`],
///   which cannot run once `ty` carries loose indices).
pub(super) fn prop_simp_lemmas_from_proof(
    state: &ProofState,
    name: &Name,
    proof: &Expr,
    hyp_ty: &Expr,
    priority: u32,
) -> Vec<SimpLemma> {
    let hyp_ty = hyp_ty.clone();
    let false_ = Expr::const_(Name::from_string("False"), vec![]);
    let true_ = Expr::const_(Name::from_string("True"), vec![]);
    let prop = Expr::prop();

    // Peel every universally quantified binder, a closing `P → False`
    // arrow's `P` included: Lean's `preprocess` matches `¬P` on the `Not`
    // head (`type.not?`, after a `whnfR` that does not unfold `Not`), so an
    // arrow into `False` takes its `isForall` branch and becomes the
    // CONDITIONAL rule `P → (False = True)`, never `P = False`. The rule is
    // stated over every leading binder, as a global theorem's is
    // (`prop_lemmas::mk_prop_simp_lemmas`). Measured 2026-11-13 against
    // pinned Lean 4.8.0 and v4.30.0-rc2 (`tests_simp_lemma_sources`).
    let Ok(binder_count) = u32::try_from(leading_pi_binder_count(&hyp_ty)) else {
        return Vec::new();
    };
    let mut body = hyp_ty.clone();
    for _ in 0..binder_count {
        let ExprKind::Pi(_, _, codomain) = body.kind() else {
            break;
        };
        body = codomain.as_ref().clone();
    }
    let h_app = mk_local_proof_template(
        crate::tactic::bvar_ops::lift_bvars(proof, binder_count),
        binder_count,
    );
    let head_name = match body.get_app_fn().kind() {
        ExprKind::Const(n, _) => Some(n.clone()),
        _ => None,
    };
    let args = body.get_app_args();
    let propext = Expr::const_(Name::from_string("propext"), vec![]);
    let is_and = head_name.as_ref() == Some(&Name::from_string("And")) && args.len() == 2;
    let is_ne = head_name.as_ref() == Some(&Name::from_string("Ne")) && args.len() == 3;
    if is_and || is_ne {
        // `h : P ∧ Q` — the rules of each conjunct, from `h.1` / `h.2`.
        // `h : a ≠ b` — `(a = b) = False` (`b = false` / `b = true` for a
        // `Bool` literal `b`), Lean's `type.ne?` branch; reading it as
        // `(a ≠ b) = True` instead left the rule unable to fire once the
        // default set's `ne_eq` had turned a goal `a ≠ b` into `¬(a = b)`,
        // and let `simp only [h]` close a goal `a ≠ b` that pinned Lean
        // refuses ("simp made no progress").
        let mut rules = Vec::new();
        super::prop_lemmas::preprocess(state, name, &body, h_app, priority, &mut rules);
        for rule in &mut rules {
            rule.lhs = state.metas.instantiate(&rule.lhs);
            rule.proof_expr = rule.proof_expr.as_ref().map(|p| state.metas.instantiate(p));
            rule.index_mode = SimpIndexMode::NoIndexAtArgs;
        }
        return rules;
    }
    let (lhs, rhs, proof) =
        if head_name.as_ref() == Some(&Name::from_string("Not")) && args.len() == 1 {
            let p = args[0].clone();
            (p.clone(), false_.clone(), prop_false_proof(&p, &h_app))
        } else if head_name.as_ref() == Some(&Name::from_string("Iff")) && args.len() == 2 {
            let (a, b) = (args[0].clone(), args[1].clone());
            let proof = Expr::app(Expr::app(Expr::app(propext, a.clone()), b.clone()), h_app);
            (a, b, proof)
        } else if head_name.as_ref() == Some(&Name::from_string("Eq")) {
            // Equations are the equality template's business.
            return Vec::new();
        } else {
            // `h : P` — `P = True` by `propext ⟨fun _ => True.intro, fun _ => h⟩`.
            let p = body.clone();
            let proof = prop_true_proof(&p, &h_app);
            (p, true_, proof)
        };
    vec![SimpLemma {
        name: name.clone(),
        lhs: state.metas.instantiate(&lhs),
        rhs,
        eq_type: Some(prop),
        proof_expr: Some(state.metas.instantiate(&proof)),
        index_mode: SimpIndexMode::NoIndexAtArgs,
        priority,
    }]
}

/// The binder types of the hypothesis a LOCAL rule was made of, indexed like
/// the rule's own de Bruijn variables (`collect_binder_types_in_conclusion`'s
/// indexing), or `None` when that hypothesis is no longer in `goal` — a rule
/// built before `simp_all` replaced it, say; nothing can be discharged then.
///
/// It re-derives the telescope exactly as the rule's constructor read it
/// ([`collect_local_extra_lemma`], [`collect_hypothesis_lemmas`],
/// `rw::collect_local_rw_simp_lemmas`: an equation is read off the WHNF of
/// the hypothesis's type; [`local_prop_hyp_lemma`] reads any other
/// proposition off the type as written, every leading `∀` peeled), so
/// index `i` here is `BVar i` of the rule's pattern and template.
pub(super) fn local_rule_binder_types(
    state: &ProofState,
    goal: &Goal,
    lemma: &SimpLemma,
) -> Option<Vec<Expr>> {
    let template = lemma.proof_expr.as_ref()?;
    let decl = goal.local_ctx.iter().rev().find(|decl| {
        decl.name.name() == &lemma.name
            && crate::let_rec::count_fvar_occurrences(template, decl.fvar) > 0
    })?;
    let whnf_ty = state.whnf(goal, &decl.ty);
    if let Some((binder_count, ..)) = extract_local_equality_template(&whnf_ty) {
        return Some(super::expr::collect_leading_binder_types(
            &whnf_ty,
            binder_count as usize,
        ));
    }
    let hyp_ty = state.metas.instantiate(&decl.ty);
    Some(collect_binder_types_in_conclusion(&hyp_ty))
}

/// `@propext P True ⟨fun _ => True.intro, fun _ => h⟩ : P = True` for
/// `h : P` — Lean's `eq_true`, spelled from prelude constants (`eq_true`
/// exists only after `import Init`). `h_app` is `h` applied to the lemma's
/// binders, so it lives one binder shallower than the lambda body it is used
/// in.
pub(super) fn prop_true_proof(p: &Expr, h_app: &Expr) -> Expr {
    let true_ = Expr::const_(Name::from_string("True"), vec![]);
    let mp = Expr::lam(
        BinderInfo::Default,
        p.clone(),
        Expr::const_(Name::from_string("True.intro"), vec![]),
    );
    let mpr = Expr::lam(BinderInfo::Default, true_.clone(), h_app.lift(1));
    let iff = Expr::apps(
        Expr::const_(Name::from_string("Iff.intro"), vec![]),
        [p.clone(), true_.clone(), mp, mpr],
    );
    Expr::apps(
        Expr::const_(Name::from_string("propext"), vec![]),
        [p.clone(), true_, iff],
    )
}

/// `@propext P False ⟨fun hp => h hp, fun hf => False.elim hf⟩ : P = False`
/// for `h : ¬P` — Lean's `eq_false`, spelled from prelude constants. `h_app`
/// is `h` applied to the lemma's binders, so it lives one binder shallower
/// than the lambda bodies it is used in. `h : a ≠ b` works the same way with
/// `P := a = b`: `Ne` unfolds to that negation.
pub(super) fn prop_false_proof(p: &Expr, h_app: &Expr) -> Expr {
    let false_ = Expr::const_(Name::from_string("False"), vec![]);
    let mp = Expr::lam(
        BinderInfo::Default,
        p.clone(),
        Expr::app(h_app.lift(1), Expr::bvar(0)),
    );
    let false_elim = Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);
    let mpr = Expr::lam(
        BinderInfo::Default,
        false_.clone(),
        Expr::app(Expr::app(false_elim, p.lift(1)), Expr::bvar(0)),
    );
    let iff = Expr::apps(
        Expr::const_(Name::from_string("Iff.intro"), vec![]),
        [p.clone(), false_.clone(), mp, mpr],
    );
    Expr::apps(
        Expr::const_(Name::from_string("propext"), vec![]),
        [p.clone(), false_, iff],
    )
}
