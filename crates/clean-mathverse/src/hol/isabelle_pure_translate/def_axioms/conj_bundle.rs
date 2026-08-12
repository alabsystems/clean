// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Conjunction-bundle prover for the Isabelle Pure definitional-axiom translator.
//!
//! Isabelle ships large *bundles* of simp laws as a single theorem whose statement
//! is a `Pure.conjunction` tree under a run of `OFCLASS(_, type)` sort premises —
//! e.g. `simp_thms` (a ~40-conjunct tower, the single biggest reject family in the
//! V3 grand) and `all_simps` (its 6-conjunct quantifier-miniscoping sibling). Under
//! the embedding a bundle becomes
//!
//! ```text
//!   True → … → True →  And L₁ (And L₂ (… Lₙ))
//! ```
//!
//! where each `Lᵢ` is a standard object-logic simp equation (`@Eq Prop …`) and the
//! leading `True`s are the erased `OFCLASS` premises. The recorded proof of such a
//! bundle is pathological (the `simp_thms` box is 1.35M nodes and `BudgetExceeds`
//! even at 200M), so it never translates. This module proves the bundle DIRECTLY:
//! it flattens the `And` tree, discharges every leaf from a small foundational
//! library ([`prove_simp_leaf`]), chains the leaf proofs with `And.intro`, and binds
//! the leading `True` premises away.
//!
//! **Soundness.** The whole assembled term is kernel-re-checked against the stored
//! bundle type (each leaf pinned as an explicit `And.intro` type argument), so a
//! wrong or mis-shaped leaf proof rejects the ENTIRE bundle — it can never
//! miscount. Every leaf arm is built from `propext`/`Classical.em`/`Eq.{mp,mpr}` /
//! the impredicative-connective encodings only, whose transitive axiom closure is
//! `⊆ FOUNDATIONAL_AXIOMS`. Strictly additive: gated on the statement being an
//! `And`-tree of recognized simp leaves (returns `None` on any surprise, so the
//! recorded-proof path is preserved for everything else).
//!
//! **Coverage.** The leaf library covers the *propositional* simp laws (the
//! `And`/`Or`/`Not`/`True`/`False` unit / absorption / idempotence / complement /
//! double-negation / implication identities and the `= True`/`= False`/`¬`-congruence
//! rewrites). The *quantifier* leaves that require HOL's universal type-nonemptiness
//! (`(∀x. P) = P`, `(∃x. P) = P`, and the `∧`-miniscoping laws of `all_simps`) are
//! NOT covered — under the faithful embedding the erased `OFCLASS → True` premise
//! carries no nonemptiness witness, so those specific leaves are not foundationally
//! provable (they are false over an empty sort). See `docs/analysis/zproof-conj-bundles.md`.

use clean_kernel::expr::{ExprKind, FVarId};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr};

use super::super::*;

// ── de-Bruijn-free term builders ───────────────────────────────────────────

/// `λ(x:dom). body[x]` via a fresh fvar (abstracted immediately; the id need only
/// be locally distinct while the fvar is free).
fn lam_fv(id: u64, dom: Expr, body: impl FnOnce(Expr) -> Expr) -> Expr {
    let fv = FVarId::new(id);
    let b = body(Expr::fvar(fv));
    Expr::lam(BinderInfo::Default, dom, b.abstract_fvar(fv))
}

fn prop() -> Expr {
    Expr::prop()
}

fn arrow(a: Expr, b: Expr) -> Expr {
    Expr::arrow(a, b)
}

// ── embedded-connective constructors ───────────────────────────────────────

/// The embedded `HOL.True` (`isabelle.def.HOL.True`, δ→ `(λx.x)=(λx.x)`).
#[cfg(test)]
fn c_true() -> Expr {
    Expr::const_str("isabelle.def.HOL.True")
}

/// The embedded `HOL.False` (`isabelle.def.HOL.False`, δ→ `∀R.R`).
fn c_false() -> Expr {
    Expr::const_str("isabelle.def.HOL.False")
}

/// A closed inhabitant of `isabelle.def.HOL.True` (the `True_enc` reflexivity proof;
/// the kernel accepts it against the def-const via δ-unfolding).
fn true_pf() -> Expr {
    true_enc_and_proof().1
}

/// `isabelle.def.HOL.conj a b` (δ→ `∀C.(a→b→C)→C`).
fn mk_conj(a: &Expr, b: &Expr) -> Expr {
    Expr::apps(conj_def_const(), [a.clone(), b.clone()])
}

/// `isabelle.def.HOL.disj a b` (δ→ `∀C.(a→C)→(b→C)→C`).
fn mk_disj(a: &Expr, b: &Expr) -> Expr {
    Expr::apps(disj_def_const(), [a.clone(), b.clone()])
}

/// `isabelle.def.HOL.Not a` (δ→ `a → ∀R.R`).
fn mk_not(a: &Expr) -> Expr {
    Expr::app(Expr::const_str("isabelle.def.HOL.Not"), a.clone())
}

// ── impredicative-connective proof combinators ─────────────────────────────

/// Inhabit `conj a b` from `ha:a`, `hb:b`: `λ(C:Prop)(k:a→b→C). k ha hb`.
fn conj_intro(a: &Expr, b: &Expr, ha: Expr, hb: Expr) -> Expr {
    let (a, b) = (a.clone(), b.clone());
    lam_fv(0x0C01, prop(), move |cc| {
        let k_ty = arrow(a.clone(), arrow(b.clone(), cc));
        lam_fv(0x0C02, k_ty, move |k| Expr::apps(k, [ha, hb]))
    })
}

/// Project the left of `h:conj a b`: `h a (λ(x:a)(y:b). x)`.
fn conj_left(a: &Expr, b: &Expr, h: Expr) -> Expr {
    let sel = lam_fv(0x0C03, a.clone(), |x| {
        lam_fv(0x0C04, b.clone(), move |_y| x)
    });
    Expr::apps(h, [a.clone(), sel])
}

/// Project the right of `h:conj a b`: `h b (λ(x:a)(y:b). y)`.
fn conj_right(a: &Expr, b: &Expr, h: Expr) -> Expr {
    let sel = lam_fv(0x0C05, a.clone(), |_x| lam_fv(0x0C06, b.clone(), |y| y));
    Expr::apps(h, [b.clone(), sel])
}

/// Inject left into `disj a b` from `ha:a`: `λ(C:Prop)(f:a→C)(g:b→C). f ha`.
fn disj_inl(a: &Expr, b: &Expr, ha: Expr) -> Expr {
    let (a, b) = (a.clone(), b.clone());
    lam_fv(0x0D01, prop(), move |cc| {
        let (fa, gb) = (arrow(a.clone(), cc.clone()), arrow(b.clone(), cc));
        lam_fv(0x0D02, fa, move |f| {
            lam_fv(0x0D03, gb, move |_g| Expr::app(f, ha))
        })
    })
}

/// Inject right into `disj a b` from `hb:b`: `λ(C:Prop)(f:a→C)(g:b→C). g hb`.
fn disj_inr(a: &Expr, b: &Expr, hb: Expr) -> Expr {
    let (a, b) = (a.clone(), b.clone());
    lam_fv(0x0D04, prop(), move |cc| {
        let (fa, gb) = (arrow(a.clone(), cc.clone()), arrow(b.clone(), cc));
        lam_fv(0x0D05, fa, move |_f| {
            lam_fv(0x0D06, gb, move |g| Expr::app(g, hb))
        })
    })
}

/// Eliminate `h:disj a b` into `goal` with case proofs `fa:a→goal`, `fb:b→goal`:
/// `h goal fa fb`.
fn disj_elim(goal: &Expr, h: Expr, fa: Expr, fb: Expr) -> Expr {
    Expr::apps(h, [goal.clone(), fa, fb])
}

/// From `hfalse : false_def` (δ→ `∀R.R`), derive `goal`: `hfalse goal`.
fn false_elim_at(goal: &Expr, hfalse: Expr) -> Expr {
    Expr::app(hfalse, goal.clone())
}

// ── `@Eq Prop` transport helpers (level-0 `Eq.mp`/`Eq.mpr`) ────────────────

/// `@Eq.mp.{0} a b heq h : b` (transport `h:a` along `heq:a=b`).
fn eq_mp(a: &Expr, b: &Expr, heq: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq.mp", vec![Level::zero()]),
        [a.clone(), b.clone(), heq, h],
    )
}

/// `@Eq.mpr.{0} a b heq h : a` (transport `h:b` back along `heq:a=b`).
fn eq_mpr(a: &Expr, b: &Expr, heq: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq.mpr", vec![Level::zero()]),
        [a.clone(), b.clone(), heq, h],
    )
}

// ── object-level (`Sort 1`) equality combinators (one-point rules) ──────────
//
// HOL object types embed at `Type` (`Sort 1 = obj_level()`), so the object
// equations the one-point rules quantify over (`x = t` at an object sort `α`)
// use `Eq`/`Eq.refl`/`Eq.symm`/`Eq.subst` instantiated at `obj_level()`.

/// `@Eq.{obj} α a b : Prop`.
fn eq_obj(alpha: &Expr, a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![obj_level()]),
        [alpha.clone(), a.clone(), b.clone()],
    )
}

/// `@Eq.refl.{obj} α a : Eq α a a`.
fn eq_refl_obj(alpha: &Expr, a: &Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq.refl", vec![obj_level()]),
        [alpha.clone(), a.clone()],
    )
}

/// `@Eq.symm.{obj} α a b h : Eq α b a` (from `h : Eq α a b`).
fn eq_symm_obj(alpha: &Expr, a: &Expr, b: &Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq.symm", vec![obj_level()]),
        [alpha.clone(), a.clone(), b.clone(), h],
    )
}

/// `@Eq.subst.{obj} α motive a b h m : motive b` (transport `m : motive a` along
/// `h : Eq α a b`; `motive : α → Prop`).
fn eq_subst_obj(alpha: &Expr, motive: &Expr, a: &Expr, b: &Expr, h: Expr, m: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq.subst", vec![obj_level()]),
        [alpha.clone(), motive.clone(), a.clone(), b.clone(), h, m],
    )
}

/// `@False.elim.{0} goal absurd : goal` — eliminate the *kernel* `False` `absurd`
/// (as produced by [`em_case_split`]'s negative arm `hnp : p → False`) into any goal.
fn false_elim_kernel(goal: &Expr, absurd: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
        [goal.clone(), absurd],
    )
}

/// `true` iff the free variable `fx` occurs in `e`. Every term tested here is
/// loose-bvar-free (fully instantiated with fvars), so `abstract_fvar` is a no-op
/// exactly when `fx` is absent.
fn mentions_fvar(e: &Expr, fx: FVarId) -> bool {
    e.abstract_fvar(fx) != *e
}

/// One β-step at the head: `(λ_. body) arg ↦ body[arg]`, else `e` unchanged. The
/// `ex_encoding` predicate is stored applied (`(λx. P x) x`), so decoding an `∃`
/// leaf's per-`x` predicate needs this one reduction to expose the `conj` head.
fn beta1(e: &Expr) -> Expr {
    if let ExprKind::App(f, arg) = e.kind() {
        if let ExprKind::Lam(_, _, body) = f.kind() {
            return body.instantiate(arg);
        }
    }
    e.clone()
}

// ── shape decoders ─────────────────────────────────────────────────────────

/// If `e = isabelle.def.HOL.conj a b`, return `(a, b)`.
fn as_conj(e: &Expr) -> Option<(Expr, Expr)> {
    binop_const(e, "isabelle.def.HOL.conj")
}

/// If `e = isabelle.def.HOL.disj a b`, return `(a, b)`.
fn as_disj(e: &Expr) -> Option<(Expr, Expr)> {
    binop_const(e, "isabelle.def.HOL.disj")
}

/// If `e = App(App(Const name, a), b)`, return `(a, b)`.
fn binop_const(e: &Expr, name: &str) -> Option<(Expr, Expr)> {
    let ExprKind::App(f, b) = e.kind() else {
        return None;
    };
    let ExprKind::App(g, a) = f.kind() else {
        return None;
    };
    matches!(g.kind(), ExprKind::Const(n, _) if *n == Name::from_string(name))
        .then(|| ((**a).clone(), (**b).clone()))
}

/// If `ty = A → B` (non-dependent `Pi`), return `(A, B)`.
fn as_arrow(ty: &Expr) -> Option<(Expr, Expr)> {
    match ty.kind() {
        ExprKind::Pi(_, dom, cod) if !cod.has_loose_bvar(0) => {
            Some(((**dom).clone(), (**cod).clone()))
        }
        _ => None,
    }
}

/// Decode `@Eq.{u} α a b`, returning `(u, α, a, b)` (the sort level kept, unlike
/// [`eq_three_parts`] which drops it). Used by the eq-commute leaf so `Eq.symm` is
/// instantiated at the *actual* object/Prop level of the equated sort.
fn as_eq_leveled(e: &Expr) -> Option<(Level, Expr, Expr, Expr)> {
    let ExprKind::App(eq_a, b) = e.kind() else {
        return None;
    };
    let ExprKind::App(eq, a) = eq_a.kind() else {
        return None;
    };
    let ExprKind::App(head, alpha) = eq.kind() else {
        return None;
    };
    let ExprKind::Const(name, levels) = head.kind() else {
        return None;
    };
    if *name != Name::from_string("Eq") {
        return None;
    }
    let u = levels.first()?.clone();
    Some((u, (**alpha).clone(), (**a).clone(), (**b).clone()))
}

/// `@Eq.symm.{u} α a b h : Eq α b a` (from `h : Eq α a b`), at an arbitrary sort
/// level `u` read from the leaf (the level-general sibling of [`eq_symm_obj`]).
fn eq_symm_lvl(u: &Level, alpha: &Expr, a: &Expr, b: &Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq.symm", vec![u.clone()]),
        [alpha.clone(), a.clone(), b.clone(), h],
    )
}

/// If `e = @Eq Prop x y` (a Prop-sort equality / iff), return `(x, y)`. The
/// building block of the iff-algebra decider.
fn as_prop_eq(e: &Expr) -> Option<(Expr, Expr)> {
    let (alpha, x, y) = eq_three_parts(e)?;
    (alpha == prop()).then_some((x, y))
}

// ── the bundle prover ──────────────────────────────────────────────────────

/// If `prop` is an `OFCLASS`-guarded `Pure.conjunction` bundle of recognized
/// propositional simp leaves, return its full kernel proof; otherwise `None`.
///
/// The statement shape is `True → … → True → And L₁ (And L₂ (… Lₙ))`. Leading
/// `True →` premises (erased `OFCLASS(_, type)`) are peeled and re-bound with
/// `λ(_:True) =>`; the `And` tree is flattened right-associatively; each leaf `Lᵢ`
/// is discharged by [`prove_simp_leaf`]; and the leaf proofs are chained with
/// `And.intro`. If ANY leaf is unrecognized, returns `None` — the whole bundle is
/// all-or-nothing (its statement is the conjunction of every conjunct). The kernel
/// re-checks the assembled term against the stored type, so a mis-proof rejects the
/// bundle and is never miscounted.
pub(crate) fn prove_conjunction_bundle(prop: &Expr) -> Option<Expr> {
    // Peel the leading sort-constraint premises. In the historical `Erase` mode these
    // are `True →` (vacuous OFCLASS erasure); in the trailing `NonemptyErase` mode
    // they are `Nonempty α →` — the faithfulness-restoring carrier that supplies the
    // quantifier witness. We bind each with a fresh fvar (abstracted back at the end),
    // so a `Nonempty α` premise's witness `Classical.choice α hne` is available to the
    // vacuous-quantifier / ∧-miniscoping leaves. A `True` premise's fvar is simply
    // unused, so an all-`True` bundle produces a value byte-identical to the historical
    // `λ(_:True). …` re-binding (the closed leaf chain has no loose bvars to shift).
    let PeeledPremises {
        prem_doms,
        prem_fvs,
        witnesses,
        conclusion,
    } = peel_sort_premises(prop);
    // The conclusion must be a genuine `And` tree (≥1 nesting) — a single leaf is
    // NOT a bundle (those are the province of the existing per-law arms and the
    // dedicated [`prove_nonempty_single_leaf`] routing).
    let (leaves, _) = flatten_and(&conclusion);
    if leaves.len() < 2 {
        return None;
    }
    // Discharge every leaf; bail on the first unrecognized one.
    let proofs: Vec<Expr> = leaves
        .iter()
        .map(|l| prove_simp_leaf_wit(l, &witnesses))
        .collect::<Option<Vec<_>>>()?;
    // Chain with `And.intro`, then re-bind the peeled premises (innermost-last).
    let body = and_chain(&leaves, &proofs);
    Some(rebind_premises(body, &prem_doms, &prem_fvs))
}

/// Prove a `Pure.conjunction` simp-law bundle whose embedded `And` tree may have
/// **any associativity** — the corpus-faithful sibling of [`prove_conjunction_bundle`].
///
/// [`prove_conjunction_bundle`] flattens only the RIGHT spine of the tree
/// ([`flatten_and`]), so it discharges only *right-associated* bundles — which is all
/// every fixture builds ([`check_bundle`] assembles `And(l, And(l, …))`). The corpus
/// `simp_thms` (44 conjuncts) / `all_simps` / `ex_simps` bundles are exported as
/// **non-right-associated** `Pure.conjunction` trees (a left child is itself a
/// `Pure.conjunction`), which embed to non-right-associated `And` trees. The
/// right-spine walk then treats such a left conjunction as one opaque
/// non-equational leaf, [`prove_simp_leaf_wit`] declines it, and the whole bundle
/// falls through to the pathological (un-translatable, 1.35M-node) recorded proof —
/// the `node=AbsP` reject that keeps `simp_thms` from flipping at corpus scale.
///
/// This variant discharges the tree **structurally** ([`prove_and_tree_wit`]),
/// recursing into both `And` children, so it lands the bundle regardless of tree
/// shape; the assembled `And.intro` term reproduces the stored tree EXACTLY, so the
/// kernel re-check against the stored (non-right-associated) statement succeeds — a
/// wrong leaf still rejects the whole bundle (all-or-nothing), never miscounts.
///
/// The caller gates this on the trailing [`ClassMembership::NonemptyErase`] mode
/// (`ctx.nonempty_erase`), which runs strictly after every historical mode
/// kernel-rejected: so it can only ADD verifications, never preempt an accepted line,
/// and every historical mode stays byte-identical (they keep using the right-spine
/// [`prove_conjunction_bundle`], and right-associated bundles produce the identical
/// term either way).
pub(crate) fn prove_conjunction_bundle_tree(prop: &Expr) -> Option<Expr> {
    let PeeledPremises {
        prem_doms,
        prem_fvs,
        witnesses,
        conclusion,
    } = peel_sort_premises(prop);
    // Prove the whole `And` tree structurally; require a genuine tree (≥2 leaves) — a
    // single leaf is not a bundle (those are the province of the per-law arms and the
    // dedicated [`prove_nonempty_single_leaf`] routing).
    let (body, n_leaves) = prove_and_tree_wit(&conclusion, &witnesses)?;
    if n_leaves < 2 {
        return None;
    }
    Some(rebind_premises(body, &prem_doms, &prem_fvs))
}

/// Recursively discharge an `And` tree of ANY associativity, returning the proof term
/// and its leaf count. An `And L R` node recurses into both children and combines
/// them with `And.intro L R pL pR` — so the proof's type is EXACTLY the input tree
/// (a non-right-associated stored statement re-checks unchanged); a non-`And` node is
/// a single leaf, discharged by [`prove_simp_leaf_wit`]. All-or-nothing: the first
/// unrecognized leaf returns `None`. (A recognized leaf is always `@Eq Prop …` or a
/// bare-proposition/`⋀`-wrapped law — never bare-`And`-headed — so the node/leaf
/// split is unambiguous.)
fn prove_and_tree_wit(node: &Expr, witnesses: &[(Expr, Expr)]) -> Option<(Expr, usize)> {
    if let Some((l, r)) = binop_const(node, "And") {
        let (pl, nl) = prove_and_tree_wit(&l, witnesses)?;
        let (pr, nr) = prove_and_tree_wit(&r, witnesses)?;
        let proof = Expr::apps(Expr::const_str("And.intro"), [l, r, pl, pr]);
        Some((proof, nl + nr))
    } else {
        Some((prove_simp_leaf_wit(node, witnesses)?, 1))
    }
}

/// A standalone (non-bundle) simp leaf under one-or-more erased sort premises —
/// the single-leaf sibling of [`prove_conjunction_bundle`], used to route a whole
/// theorem whose conclusion is a *single* quantifier simp equation (a vacuous
/// `(∀x. P) = P` / `(∃x. P) = P`, a one-point rule, or a `∨`/`⟶` miniscoping law)
/// rather than a `Pure.conjunction` bundle conjunct.
///
/// Peels the leading `True →` / `Nonempty α →` premises (collecting the `Nonempty`
/// witnesses), requires the conclusion to be exactly ONE recognized leaf, discharges
/// it via [`prove_simp_leaf_wit`], and re-binds the premises. Returns `None` unless
/// **at least one** premise is a genuine `Nonempty α` carrier — this keeps the arm
/// scoped to the trailing `NonemptyErase` mode (the caller also gates on
/// `ctx.nonempty_erase`), so it never disturbs a historical `True`-erased line.
/// Kernel-re-checked by the caller against the stored statement, so a mis-shape
/// rejects — never miscounts.
pub(crate) fn prove_nonempty_single_leaf(prop: &Expr) -> Option<Expr> {
    let PeeledPremises {
        prem_doms,
        prem_fvs,
        witnesses,
        conclusion,
    } = peel_sort_premises(prop);
    // Scope to the NonemptyErase mode: require a real `Nonempty α` carrier, and a
    // conclusion that is a SINGLE leaf (a bundle is `prove_conjunction_bundle`'s job).
    if witnesses.is_empty() {
        return None;
    }
    let (leaves, _) = flatten_and(&conclusion);
    if leaves.len() != 1 {
        return None;
    }
    let proof = prove_simp_leaf_wit(&leaves[0], &witnesses)?;
    Some(rebind_premises(proof, &prem_doms, &prem_fvs))
}

/// The peeled leading sort-constraint premises of a bundle/leaf statement.
struct PeeledPremises {
    prem_doms: Vec<Expr>,
    prem_fvs: Vec<FVarId>,
    /// `(α, Classical.choice α hne)` for each peeled `Nonempty α` premise.
    witnesses: Vec<(Expr, Expr)>,
    /// The statement past all peeled premises.
    conclusion: Expr,
}

/// Peel the leading sort-constraint premises (`True →` historical / `Nonempty α →`
/// trailing `NonemptyErase`). Each is bound with a fresh fvar (re-abstracted by
/// [`rebind_premises`]); a `Nonempty α` premise records its witness element
/// `@Classical.choice.{obj} α hne : α`. A `True` premise's fvar is simply unused, so
/// an all-`True` prefix re-binds byte-identically to the historical `λ(_:True). …`.
fn peel_sort_premises(prop: &Expr) -> PeeledPremises {
    let mut prem_doms: Vec<Expr> = Vec::new();
    let mut prem_fvs: Vec<FVarId> = Vec::new();
    let mut witnesses: Vec<(Expr, Expr)> = Vec::new();
    let mut next_id: u64 = 0x9000;
    let mut cur = prop.clone();
    while let ExprKind::Pi(_, dom, cod) = cur.kind() {
        if cod.has_loose_bvar(0) {
            break; // a genuine dependent Π (not a peelable premise)
        }
        let is_true = **dom == Expr::const_str("True");
        let alpha = as_nonempty(dom);
        if !is_true && alpha.is_none() {
            break;
        }
        let fv = FVarId::new(next_id);
        next_id += 1;
        if let Some(a) = alpha {
            let w = Expr::apps(
                Expr::const_str_levels("Classical.choice", vec![obj_level()]),
                [a.clone(), Expr::fvar(fv)],
            );
            witnesses.push((a, w));
        }
        prem_doms.push((**dom).clone());
        prem_fvs.push(fv);
        cur = (**cod).clone();
    }
    PeeledPremises {
        prem_doms,
        prem_fvs,
        witnesses,
        conclusion: cur,
    }
}

/// Re-bind the peeled premises around `body` (innermost-last), abstracting each
/// premise's fvar.
fn rebind_premises(mut body: Expr, prem_doms: &[Expr], prem_fvs: &[FVarId]) -> Expr {
    for (dom, fv) in prem_doms.iter().zip(prem_fvs.iter()).rev() {
        body = Expr::lam(BinderInfo::Default, dom.clone(), body.abstract_fvar(*fv));
    }
    body
}

/// If `e = @Nonempty.{_} α`, return `α`. The [`ClassMembership::NonemptyErase`]
/// spelling of an `OFCLASS` sort premise.
fn as_nonempty(e: &Expr) -> Option<Expr> {
    let ExprKind::App(f, a) = e.kind() else {
        return None;
    };
    matches!(f.kind(), ExprKind::Const(n, _) if *n == Name::from_string("Nonempty"))
        .then(|| (**a).clone())
}

/// The witness element (`Classical.choice α hne : α`) for a bound sort `alpha`, if a
/// `Nonempty alpha` premise was peeled.
fn witness_for(alpha: &Expr, witnesses: &[(Expr, Expr)]) -> Option<Expr> {
    witnesses
        .iter()
        .find(|(a, _)| a == alpha)
        .map(|(_, w)| w.clone())
}

/// Flatten a right-associated `And L₁ (And L₂ …)` tree into its leaves. A non-`And`
/// term is a single leaf. Returns `(leaves, depth)`.
fn flatten_and(e: &Expr) -> (Vec<Expr>, usize) {
    let mut out = Vec::new();
    let mut cur = e.clone();
    while let Some((l, r)) = binop_const(&cur, "And") {
        out.push(l);
        cur = r;
    }
    let depth = out.len();
    out.push(cur);
    (out, depth)
}

/// Build the right-associated `And.intro` chain proving `And l₀ (And l₁ …)` from the
/// per-leaf proofs. `leaves` and `proofs` have equal length ≥ 1.
fn and_chain(leaves: &[Expr], proofs: &[Expr]) -> Expr {
    // The last leaf's proof is the base; fold from the right.
    let mut acc_ty = leaves[leaves.len() - 1].clone();
    let mut acc = proofs[proofs.len() - 1].clone();
    for i in (0..leaves.len() - 1).rev() {
        let l = &leaves[i];
        acc = Expr::apps(
            Expr::const_str("And.intro"),
            [l.clone(), acc_ty.clone(), proofs[i].clone(), acc],
        );
        acc_ty = Expr::apps(Expr::const_str("And"), [l.clone(), acc_ty]);
    }
    acc
}

/// Discharge one propositional simp leaf `@Eq Prop L R` foundationally, or `None`
/// if the leaf is not one of the recognized laws. Every returned term is a
/// `propext`/`Classical.em`/`Eq.{mp,mpr}` derivation with foundational closure; the
/// kernel re-checks it against `leaf`, so a mis-match rejects (never miscounts).
#[cfg(any(test, doc))]
pub(crate) fn prove_simp_leaf(leaf: &Expr) -> Option<Expr> {
    prove_simp_leaf_wit(leaf, &[])
}

/// Witness-aware leaf discharge. `witnesses` maps each bound sort `α` (whose
/// `Nonempty α` premise was peeled by the bundle prover) to a choice witness
/// `Classical.choice α hne : α`. When non-empty it unlocks the **quantifier** simp
/// leaves — the vacuous `(∀x. P) = P` / `(∃x. P) = P` and the `∧`-miniscoping laws of
/// `all_simps` — which are *false-as-embedded* over a possibly-empty sort and so
/// cannot be discharged in the historical `True`-erased mode (`witnesses` empty →
/// this reduces byte-identically to the propositional [`prove_simp_leaf`]). Every
/// returned term is kernel-re-checked against `leaf` by the bundle prover, so a
/// mis-shaped witness proof rejects the whole bundle — never miscounts.
pub(crate) fn prove_simp_leaf_wit(leaf: &Expr, witnesses: &[(Expr, Expr)]) -> Option<Expr> {
    // ── bare-proposition (non-equational) simp leaves ─────────────────────
    // The `simp_thms` conjuncts that are NOT an equation: the negated-self-eq
    // laws `¬((¬P) = P)` / `¬(P = (¬P))` and the `∃`-reflexivity witnesses
    // `∃x. x = t` / `∃x. t = x`. Tried first so an `∃`-encoding (structurally a
    // `Π(Q:Prop)…`) is not mis-routed into the meta-universal peel below.
    if let Some(p) = prove_bare_prop_leaf(leaf) {
        return Some(p);
    }

    // ── meta-universal `⋀y. body` peel (per-conjunct `Pure.all` binders) ──
    // The one-point conjuncts of `simp_thms` (`⋀P. (∃x. x=t ∧ P x) = P t`, …) and
    // every `all_simps` conjunct (`⋀P Q. …`) carry per-conjunct `Pure.all`
    // binders that embed as a leading `Π`. Peel each, prove the inner leaf, and
    // re-bind with `λ`. A non-meta `Π` leaf whose body is unprovable simply
    // declines; the kernel re-checks the assembled `λ`, so a mis-peel can never
    // miscount.
    if let Some(p) = prove_meta_universal(leaf, witnesses) {
        return Some(p);
    }

    // ── equational leaves `@Eq Prop l r` ─────────────────────────────────
    let (alpha, l, r) = eq_three_parts(leaf)?;
    if alpha != prop() {
        return None;
    }
    // `(x = x) = True` at ANY object sort α (`simp_thms`'s `eq_self`): `l` is an
    // object-level `@Eq α x x` whose sort is NOT Prop, so it never reaches the
    // Prop-gated eq-rewrite arms below.
    if let Some(p) = prove_eq_self_true(&l, &r) {
        return Some(p);
    }

    // ── classical/constructive propositional normal-form laws ─────────────
    // De Morgan, `⟶`-as-`∨`, iff/not-iff DNF, `∧`/`∨` commutativity, and
    // `∧`-over-`∨` distributivity — the normal-form bundles (`s95156`,
    // `s2325842`, `s2325932`) the base unit/absorption library did not cover.
    if let Some(p) = prove_classical_prop_leaf(&l, &r) {
        return Some(p);
    }

    // ── witness-FREE quantifier laws (one-point rules; ∨/⟶ miniscoping) ───
    // Provable with NO nonemptiness witness — the one-point equation `x = t`
    // supplies `t` as its own witness, and the ∨/⟶ miniscoping laws hold even
    // over an empty sort (both sides collapse to the same value). Tried on every
    // leaf, so they also flip standalone / propositional-bundle occurrences.
    if let Some(p) = prove_quantifier_leaf_witfree(&l, &r) {
        return Some(p);
    }

    // ── quantifier laws (need a `Nonempty` witness for the bound sort) ─────
    if !witnesses.is_empty() {
        if let Some(p) = prove_quantifier_leaf(&l, &r, witnesses) {
            return Some(p);
        }
    }

    // ── conjunction laws: L = conj a b ────────────────────────────────────
    if let Some((a, b)) = as_conj(&l) {
        // (P ∧ True) = P
        if is_true_def_const(&b) && r == a {
            let mp = lam_fv(0x1001, l.clone(), |h| conj_left(&a, &b, h));
            let mpr = {
                let (a, b) = (a.clone(), b.clone());
                lam_fv(0x1002, a.clone(), move |hp| {
                    conj_intro(&a, &b, hp, true_pf())
                })
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        // (True ∧ P) = P
        if is_true_def_const(&a) && r == b {
            let mp = lam_fv(0x1003, l.clone(), |h| conj_right(&a, &b, h));
            let mpr = {
                let (a, b) = (a.clone(), b.clone());
                lam_fv(0x1004, b.clone(), move |hp| {
                    conj_intro(&a, &b, true_pf(), hp)
                })
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        // (P ∧ False) = False
        if is_false_def_const(&b) && is_false_def_const(&r) {
            let mp = lam_fv(0x1005, l.clone(), |h| conj_right(&a, &b, h));
            let mpr = {
                let ltyp = l.clone();
                lam_fv(0x1006, r.clone(), move |hf| false_elim_at(&ltyp, hf))
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        // (False ∧ P) = False
        if is_false_def_const(&a) && is_false_def_const(&r) {
            let mp = lam_fv(0x1007, l.clone(), |h| conj_left(&a, &b, h));
            let mpr = {
                let ltyp = l.clone();
                lam_fv(0x1008, r.clone(), move |hf| false_elim_at(&ltyp, hf))
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        // (P ∧ P) = P
        if a == b && r == a {
            let mp = lam_fv(0x1009, l.clone(), |h| conj_left(&a, &b, h));
            let mpr = {
                let (a, b) = (a.clone(), b.clone());
                lam_fv(0x100a, a.clone(), move |hp| {
                    conj_intro(&a, &b, hp.clone(), hp)
                })
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        // (P ∧ (P ∧ Q)) = (P ∧ Q)   (left-absorption)
        if let Some((ba, bq)) = as_conj(&b) {
            if ba == a && r == b {
                // mp : (P ∧ (P ∧ Q)) → (P ∧ Q)  =  conj_right
                let mp = lam_fv(0x100b, l.clone(), |h| conj_right(&a, &b, h));
                // mpr : (P ∧ Q) → (P ∧ (P ∧ Q))  =  λh. conj_intro P (P∧Q) (P-of-h) h
                let mpr = {
                    let (a, b, ba, bq) = (a.clone(), b.clone(), ba.clone(), bq.clone());
                    lam_fv(0x100c, b.clone(), move |hb| {
                        let hp = conj_left(&ba, &bq, hb.clone());
                        conj_intro(&a, &b, hp, hb)
                    })
                };
                return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
            }
        }
        // (P ∧ ¬P) = False   /   (¬P ∧ P) = False   (contradiction)
        if is_false_def_const(&r) {
            let left_neg = b == mk_not(&a); // a ∧ ¬a
            let right_neg = a == mk_not(&b); // ¬b ∧ b
            if left_neg || right_neg {
                // mp : (a ∧ b) → False_enc  =  apply the negation to its witness.
                let mp = {
                    let (a, b) = (a.clone(), b.clone());
                    lam_fv(0x100d, l.clone(), move |h| {
                        let ha = conj_left(&a, &b, h.clone());
                        let hb = conj_right(&a, &b, h);
                        if left_neg {
                            // b = ¬a (δ a → False_enc); apply to ha.
                            Expr::app(hb, ha)
                        } else {
                            // a = ¬b (δ b → False_enc); apply to hb.
                            Expr::app(ha, hb)
                        }
                    })
                };
                // mpr : False → (a ∧ b)  =  False.elim.
                let mpr = {
                    let ltyp = l.clone();
                    lam_fv(0x100e, r.clone(), move |hf| false_elim_at(&ltyp, hf))
                };
                return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
            }
        }
        return None;
    }

    // ── disjunction laws: L = disj a b ────────────────────────────────────
    if let Some((a, b)) = as_disj(&l) {
        // (P ∨ True) = True   /   (True ∨ P) = True
        if (is_true_def_const(&b) || is_true_def_const(&a)) && is_true_def_const(&r) {
            let mp = lam_fv(0x2001, l.clone(), |_h| true_pf());
            let mpr = {
                let (a, b) = (a.clone(), b.clone());
                let left = is_true_def_const(&a);
                lam_fv(0x2002, r.clone(), move |_h| {
                    if left {
                        disj_inl(&a, &b, true_pf())
                    } else {
                        disj_inr(&a, &b, true_pf())
                    }
                })
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        // (P ∨ False) = P
        if is_false_def_const(&b) && r == a {
            let mp = {
                let (a, b, r2) = (a.clone(), b.clone(), r.clone());
                lam_fv(0x2003, l.clone(), move |h| {
                    let fa = lam_fv(0x2004, a.clone(), |hp| hp);
                    let fb = {
                        let r3 = r2.clone();
                        lam_fv(0x2005, b.clone(), move |hf| false_elim_at(&r3, hf))
                    };
                    disj_elim(&r2, h, fa, fb)
                })
            };
            let mpr = {
                let (a, b) = (a.clone(), b.clone());
                lam_fv(0x2006, a.clone(), move |hp| disj_inl(&a, &b, hp))
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        // (False ∨ P) = P
        if is_false_def_const(&a) && r == b {
            let mp = {
                let (a, b, r2) = (a.clone(), b.clone(), r.clone());
                lam_fv(0x2007, l.clone(), move |h| {
                    let fa = {
                        let r3 = r2.clone();
                        lam_fv(0x2008, a.clone(), move |hf| false_elim_at(&r3, hf))
                    };
                    let fb = lam_fv(0x2009, b.clone(), |hp| hp);
                    disj_elim(&r2, h, fa, fb)
                })
            };
            let mpr = {
                let (a, b) = (a.clone(), b.clone());
                lam_fv(0x200a, b.clone(), move |hp| disj_inr(&a, &b, hp))
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        // (P ∨ P) = P
        if a == b && r == a {
            let mp = {
                let (a, b, r2) = (a.clone(), b.clone(), r.clone());
                lam_fv(0x200b, l.clone(), move |h| {
                    let fa = lam_fv(0x200c, a.clone(), |hp| hp);
                    let fb = lam_fv(0x200d, b.clone(), |hp| hp);
                    disj_elim(&r2, h, fa, fb)
                })
            };
            let mpr = {
                let (a, b) = (a.clone(), b.clone());
                lam_fv(0x200e, a.clone(), move |hp| disj_inl(&a, &b, hp))
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        // (P ∨ ¬P) = True   /   (¬P ∨ P) = True   (excluded middle)
        if is_true_def_const(&r) {
            let left_neg = b == mk_not(&a); // a ∨ ¬a
            let right_neg = a == mk_not(&b); // ¬b ∨ b
            if left_neg || right_neg {
                // mp : (a ∨ b) → True.
                let mp = lam_fv(0x200f, l.clone(), |_h| true_pf());
                // mpr : True → (a ∨ b)  by `Classical.em` on the un-negated base.
                let base = if left_neg { a.clone() } else { b.clone() };
                let mpr = {
                    let (a, b, base, l2) = (a.clone(), b.clone(), base.clone(), l.clone());
                    lam_fv(0x2010, r.clone(), move |_h| {
                        let pos = {
                            let (a, b) = (a.clone(), b.clone());
                            lam_fv(0x2011, base.clone(), move |hp| {
                                if left_neg {
                                    disj_inl(&a, &b, hp) // base = a
                                } else {
                                    disj_inr(&a, &b, hp) // base = b
                                }
                            })
                        };
                        let neg = {
                            let (a, b, base) = (a.clone(), b.clone(), base.clone());
                            lam_fv(
                                0x2012,
                                arrow(base.clone(), Expr::const_str("False")),
                                move |hnp| {
                                    // coerce the kernel negation to a HOL `Not base`,
                                    // which is exactly the negated disjunct.
                                    let hol = kernel_not_to_hol_not(&base, hnp);
                                    if left_neg {
                                        disj_inr(&a, &b, hol) // ¬base = b
                                    } else {
                                        disj_inl(&a, &b, hol) // ¬base = a
                                    }
                                },
                            )
                        };
                        em_case_split(&base, &l2, pos, neg)
                    })
                };
                return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
            }
        }
        // (P ∨ (P ∨ Q)) = (P ∨ Q)   (left-absorption)
        if let Some((ba, bq)) = as_disj(&b) {
            if ba == a && r == b {
                // mp : (P ∨ (P ∨ Q)) → (P ∨ Q).
                let mp = {
                    let (a, b, ba, bq) = (a.clone(), b.clone(), ba.clone(), bq.clone());
                    lam_fv(0x2013, l.clone(), move |h| {
                        let fa = {
                            let (ba, bq) = (ba.clone(), bq.clone());
                            lam_fv(0x2014, a.clone(), move |ha| disj_inl(&ba, &bq, ha))
                        };
                        let fb = lam_fv(0x2015, b.clone(), |hb| hb);
                        disj_elim(&b, h, fa, fb)
                    })
                };
                // mpr : (P ∨ Q) → (P ∨ (P ∨ Q))  =  inject on the right.
                let mpr = {
                    let (a, b) = (a.clone(), b.clone());
                    lam_fv(0x2016, b.clone(), move |hb| disj_inr(&a, &b, hb))
                };
                return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
            }
        }
        return None;
    }

    // ── negation laws: L = not x ──────────────────────────────────────────
    if let Some(inner) = hol_not_arg(&l) {
        // ¬¬P = P
        if let Some(p) = hol_not_arg(&inner) {
            if r == p {
                // mp : ¬¬P → P  (classical: em on P).
                let mp = {
                    let p = p.clone();
                    lam_fv(0x3001, l.clone(), move |h| {
                        let pos = lam_fv(0x3002, p.clone(), |hp| hp);
                        let neg = {
                            let (p2, h2) = (p.clone(), h.clone());
                            lam_fv(
                                0x3003,
                                arrow(p.clone(), Expr::const_str("False")),
                                move |hnp| {
                                    // hol ¬P : inner (= not_def p, δ p→false_enc)
                                    let hol_np = kernel_not_to_hol_not(&p2, hnp);
                                    // h (hol ¬P) : false_enc; apply to P
                                    let f = Expr::app(h2, hol_np);
                                    Expr::app(f, p2)
                                },
                            )
                        };
                        em_case_split(&p, &p, pos, neg)
                    })
                };
                // mpr : P → ¬¬P  =  λhp. λ(hn:¬P). hn hp
                let mpr = {
                    let (p, inner2) = (p.clone(), inner.clone());
                    lam_fv(0x3004, p.clone(), move |hp| {
                        lam_fv(0x3005, inner2.clone(), move |hn| Expr::app(hn, hp))
                    })
                };
                return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
            }
        }
        // (¬True) = False
        if is_true_def_const(&inner) && is_false_def_const(&r) {
            let mp = lam_fv(0x3006, l.clone(), |h| Expr::app(h, true_pf()));
            let mpr = {
                let ltyp = l.clone();
                lam_fv(0x3007, r.clone(), move |hf| false_elim_at(&ltyp, hf))
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        // (¬False) = True
        if is_false_def_const(&inner) && is_true_def_const(&r) {
            let mp = lam_fv(0x3008, l.clone(), |_h| true_pf());
            // mpr : True → ¬False  =  λ_. λ(hf:False). hf   (False defeq false_enc)
            let mpr = lam_fv(0x3009, r.clone(), move |_h| {
                lam_fv(0x300a, c_false(), |hf| hf)
            });
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        // (¬(P = Q)) = (P = ¬Q)   (not_iff)
        if let Some((ea, ip, iq)) = eq_three_parts(&inner) {
            if ea == prop() {
                if let Some((ra, rp, rq)) = eq_three_parts(&r) {
                    if ra == prop() && rp == ip {
                        if let Some(nq) = hol_not_arg(&rq) {
                            if nq == iq {
                                return Some(not_iff_leaf(&l, &r, &ip, &iq));
                            }
                        }
                    }
                }
            }
        }
        // fall through to eq laws below (¬ can also appear as the RHS of an eq law)
    }

    // ── equality-rewrite laws: L = @Eq Prop x y ───────────────────────────
    if let Some((ea, ex, ey)) = eq_three_parts(&l) {
        if ea == prop() {
            // (P = True) = P
            if is_true_def_const(&ey) && r == ex {
                let mp = {
                    let (ex2, ey2) = (ex.clone(), ey.clone());
                    lam_fv(0x4001, l.clone(), move |h| eq_mpr(&ex2, &ey2, h, true_pf()))
                };
                let mpr = {
                    let (ex2, ey2) = (ex.clone(), ey.clone());
                    lam_fv(0x4002, r.clone(), move |hp| {
                        let fwd = lam_fv(0x4003, ex2.clone(), |_x| true_pf());
                        let bwd = lam_fv(0x4004, ey2.clone(), move |_t| hp);
                        propext_iff(ex2.clone(), ey2.clone(), fwd, bwd)
                    })
                };
                return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
            }
            // (True = P) = P
            if is_true_def_const(&ex) && r == ey {
                let mp = {
                    let (ex2, ey2) = (ex.clone(), ey.clone());
                    lam_fv(0x4005, l.clone(), move |h| eq_mp(&ex2, &ey2, h, true_pf()))
                };
                let mpr = {
                    let (ex2, ey2) = (ex.clone(), ey.clone());
                    lam_fv(0x4006, r.clone(), move |hp| {
                        let fwd = lam_fv(0x4007, ex2.clone(), move |_t| hp);
                        let bwd = lam_fv(0x4008, ey2.clone(), |_x| true_pf());
                        propext_iff(ex2.clone(), ey2.clone(), fwd, bwd)
                    })
                };
                return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
            }
            // (P = False) = ¬P
            if is_false_def_const(&ey) {
                if let Some(rp) = hol_not_arg(&r) {
                    if rp == ex {
                        let mp = {
                            let (ex2, ey2) = (ex.clone(), ey.clone());
                            lam_fv(0x4009, l.clone(), move |h| {
                                lam_fv(0x400a, ex2.clone(), move |hp| {
                                    eq_mp(&ex2, &ey2, h.clone(), hp)
                                })
                            })
                        };
                        let mpr = {
                            let (ex2, ey2) = (ex.clone(), ey.clone());
                            lam_fv(0x400b, r.clone(), move |hn| {
                                let fwd = {
                                    let hn2 = hn.clone();
                                    lam_fv(0x400c, ex2.clone(), move |hp| Expr::app(hn2, hp))
                                };
                                let bwd = {
                                    let ex3 = ex2.clone();
                                    lam_fv(0x400d, ey2.clone(), move |hf| false_elim_at(&ex3, hf))
                                };
                                propext_iff(ex2.clone(), ey2.clone(), fwd, bwd)
                            })
                        };
                        return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
                    }
                }
            }
            // (False = P) = ¬P
            if is_false_def_const(&ex) {
                if let Some(rp) = hol_not_arg(&r) {
                    if rp == ey {
                        let mp = {
                            let (ex2, ey2) = (ex.clone(), ey.clone());
                            lam_fv(0x400e, l.clone(), move |h| {
                                lam_fv(0x400f, ey2.clone(), move |hp| {
                                    eq_mpr(&ex2, &ey2, h.clone(), hp)
                                })
                            })
                        };
                        let mpr = {
                            let (ex2, ey2) = (ex.clone(), ey.clone());
                            lam_fv(0x4010, r.clone(), move |hn| {
                                let fwd = {
                                    let ey3 = ey2.clone();
                                    lam_fv(0x4011, ex2.clone(), move |hf| false_elim_at(&ey3, hf))
                                };
                                let bwd = {
                                    let hn2 = hn.clone();
                                    lam_fv(0x4012, ey2.clone(), move |hp| Expr::app(hn2, hp))
                                };
                                propext_iff(ex2.clone(), ey2.clone(), fwd, bwd)
                            })
                        };
                        return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
                    }
                }
            }
            // ((¬P) = (¬Q)) = (P = Q)   (negation congruence, classical)
            if let (Some(p), Some(q)) = (hol_not_arg(&ex), hol_not_arg(&ey)) {
                if let Some((rb, rp, rq)) = eq_three_parts(&r) {
                    if rb == prop() && rp == p && rq == q {
                        let proof = neg_cong_leaf(&l, &r, &p, &q, &ex, &ey);
                        return Some(proof);
                    }
                }
            }
            return None;
        }
    }

    // ── implication laws: L = A → B ───────────────────────────────────────
    if let Some((d, cod)) = as_arrow(&l) {
        // (True → P) = P
        if is_true_def_const(&d) && r == cod {
            let mp = lam_fv(0x5001, l.clone(), |h| Expr::app(h, true_pf()));
            let mpr = {
                let d2 = d.clone();
                lam_fv(0x5002, r.clone(), move |hp| {
                    lam_fv(0x5003, d2.clone(), move |_t| hp)
                })
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        // (P → True) = True
        if is_true_def_const(&cod) && is_true_def_const(&r) {
            let mp = lam_fv(0x5004, l.clone(), |_h| true_pf());
            let mpr = {
                let d2 = d.clone();
                lam_fv(0x5005, r.clone(), move |_t| {
                    lam_fv(0x5006, d2.clone(), |_p| true_pf())
                })
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        // (False → P) = True
        if is_false_def_const(&d) && is_true_def_const(&r) {
            let mp = lam_fv(0x5007, l.clone(), |_h| true_pf());
            let mpr = {
                let (d2, cod2) = (d.clone(), cod.clone());
                lam_fv(0x5008, r.clone(), move |_t| {
                    let cod3 = cod2.clone();
                    lam_fv(0x5009, d2.clone(), move |hf| false_elim_at(&cod3, hf))
                })
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        // (P → P) = True
        if d == cod && is_true_def_const(&r) {
            let mp = lam_fv(0x500a, l.clone(), |_h| true_pf());
            let mpr = {
                let d2 = d.clone();
                lam_fv(0x500b, r.clone(), move |_t| {
                    lam_fv(0x500c, d2.clone(), |hp| hp)
                })
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        // (P → False) = ¬P
        if is_false_def_const(&cod) && r == mk_not(&d) {
            // mp : (P → False) → ¬P  =  λh. λ(hp:P). h hp   (False defeq False_enc)
            let mp = {
                let d2 = d.clone();
                lam_fv(0x500d, l.clone(), move |h| {
                    lam_fv(0x500e, d2.clone(), move |hp| Expr::app(h.clone(), hp))
                })
            };
            // mpr : ¬P → (P → False)  =  λhn. λ(hp:P). hn hp
            let mpr = {
                let d2 = d.clone();
                lam_fv(0x500f, r.clone(), move |hn| {
                    lam_fv(0x5010, d2.clone(), move |hp| Expr::app(hn.clone(), hp))
                })
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        // (P → ¬P) = ¬P
        if cod == mk_not(&d) && r == cod {
            // mp : (P → ¬P) → ¬P  =  λh. λ(hp:P). (h hp) hp
            let mp = {
                let d2 = d.clone();
                lam_fv(0x5011, l.clone(), move |h| {
                    lam_fv(0x5012, d2.clone(), move |hp| {
                        Expr::app(Expr::app(h.clone(), hp.clone()), hp)
                    })
                })
            };
            // mpr : ¬P → (P → ¬P)  =  λhn. λ(_:P). hn
            let mpr = {
                let d2 = d.clone();
                lam_fv(0x5013, r.clone(), move |hn| {
                    lam_fv(0x5014, d2.clone(), move |_hp| hn.clone())
                })
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        return None;
    }

    None
}

/// `(a = b) = (b = a)` — equality commutativity at an ARBITRARY sort `α` (object
/// or `Prop`). `l = @Eq.{u} α a b`, `r = @Eq.{u} α b a`; both directions are
/// `Eq.symm` at the leaf's own level `u` (so an object-sort `α : Type` uses
/// `Eq.symm.{1}`, a `Prop` sort uses `Eq.symm.{1}` at `Prop = Sort 0`). Foundational
/// (`propext` + `Eq.symm`). The single object-sort conjunct of the `eq_ac` bundle
/// (s83088 C1). Returns `None` unless `r` is exactly `l` with the two sides swapped.
fn prove_eq_commute_leaf(l: &Expr, r: &Expr) -> Option<Expr> {
    let (u, alpha, a, b) = as_eq_leveled(l)?;
    let (u2, alpha2, rb, ra) = as_eq_leveled(r)?;
    if u != u2 || alpha != alpha2 || rb != b || ra != a {
        return None;
    }
    // mp : (a = b) → (b = a)  =  λ(h). Eq.symm α a b h
    let mp = {
        let (u, alpha, a, b) = (u.clone(), alpha.clone(), a.clone(), b.clone());
        lam_fv(0x9A01, l.clone(), move |h| {
            eq_symm_lvl(&u, &alpha, &a, &b, h)
        })
    };
    // mpr : (b = a) → (a = b)  =  λ(h). Eq.symm α b a h
    let mpr = {
        let (u, alpha, a, b) = (u.clone(), alpha.clone(), a.clone(), b.clone());
        lam_fv(0x9A02, r.clone(), move |h| {
            eq_symm_lvl(&u, &alpha, &b, &a, h)
        })
    };
    Some(propext_iff(l.clone(), r.clone(), mp, mpr))
}

/// The truth value of an atom under a case-split assignment: either a `Proof` of
/// the atom or a kernel `Refutation` (`atom → False`).
#[derive(Clone)]
enum IffVal {
    /// A proof term inhabiting the proposition.
    Proof(Expr),
    /// A kernel negation `prop → False` (as produced by `Classical.em`'s negative
    /// arm).
    Refut(Expr),
}

/// Collect the maximal non-`@Eq Prop` sub-propositions ("atoms") of `e` into `out`
/// (dedup by structural equality), recursing through `@Eq Prop` nodes only. These
/// are the propositions the iff-algebra decider `Classical.em`-splits.
fn collect_iff_atoms(e: &Expr, out: &mut Vec<Expr>) {
    if let Some((x, y)) = as_prop_eq(e) {
        collect_iff_atoms(&x, out);
        collect_iff_atoms(&y, out);
    } else if !out.contains(e) {
        out.push(e.clone());
    }
}

/// Decide the truth of `e` (an `@Eq Prop`-tree over assigned atoms) under `assign`,
/// returning a `Proof`/`Refut` witness. For a composite `x ≐ y` it recurses and
/// combines: both-true / both-false give a `propext`-`Proof` of `x ≐ y`; a
/// true/false mismatch gives a `Refut` (via `Eq.mp`/`Eq.mpr`). An atom is looked up
/// in `assign` (declining — `None` — if unassigned). Every combinator is
/// `propext`/`Eq.{mp,mpr}`/`False.elim`, foundational closure.
fn iff_decide(e: &Expr, assign: &[(Expr, IffVal)]) -> Option<IffVal> {
    let Some((x, y)) = as_prop_eq(e) else {
        return assign
            .iter()
            .rev()
            .find(|(a, _)| a == e)
            .map(|(_, v)| v.clone());
    };
    let dx = iff_decide(&x, assign)?;
    let dy = iff_decide(&y, assign)?;
    let exy = eq_prop(x.clone(), y.clone());
    Some(match (dx, dy) {
        // both hold → `x ≐ y` by `propext` of the constant-function iff.
        (IffVal::Proof(px), IffVal::Proof(py)) => {
            let mp = lam_fv(0x9B01, x.clone(), move |_h| py);
            let mpr = lam_fv(0x9B02, y.clone(), move |_h| px);
            IffVal::Proof(propext_iff(x, y, mp, mpr))
        }
        // both false → `x ≐ y` by `propext` of the ex-falso iff.
        (IffVal::Refut(nx), IffVal::Refut(ny)) => {
            let mp = {
                let (y2, nx) = (y.clone(), nx);
                lam_fv(0x9B03, x.clone(), move |h| {
                    false_elim_kernel(&y2, Expr::app(nx, h))
                })
            };
            let mpr = {
                let (x2, ny) = (x.clone(), ny);
                lam_fv(0x9B04, y.clone(), move |h| {
                    false_elim_kernel(&x2, Expr::app(ny, h))
                })
            };
            IffVal::Proof(propext_iff(x, y, mp, mpr))
        }
        // true / false → `x ≐ y` is refutable: from `h : x ≐ y` transport `px` to
        // `y` and contradict `ny`.
        (IffVal::Proof(px), IffVal::Refut(ny)) => {
            let (x2, y2) = (x.clone(), y.clone());
            IffVal::Refut(lam_fv(0x9B05, exy, move |h| {
                Expr::app(ny, eq_mp(&x2, &y2, h, px))
            }))
        }
        // false / true → symmetric refutation via `Eq.mpr`.
        (IffVal::Refut(nx), IffVal::Proof(py)) => {
            let (x2, y2) = (x.clone(), y.clone());
            IffVal::Refut(lam_fv(0x9B06, exy, move |h| {
                Expr::app(nx, eq_mpr(&x2, &y2, h, py))
            }))
        }
    })
}

/// Build the proof of `@Eq Prop l r` under the fully-assigned atoms: decide both
/// sides and combine (both-true / both-false → `propext`; a mismatch declines,
/// which cannot happen for a genuine biconditional-algebra identity).
fn iff_goal(l: &Expr, r: &Expr, assign: &[(Expr, IffVal)]) -> Option<Expr> {
    Some(match (iff_decide(l, assign)?, iff_decide(r, assign)?) {
        (IffVal::Proof(pl), IffVal::Proof(pr)) => {
            let mp = lam_fv(0x9C01, l.clone(), move |_h| pr);
            let mpr = lam_fv(0x9C02, r.clone(), move |_h| pl);
            propext_iff(l.clone(), r.clone(), mp, mpr)
        }
        (IffVal::Refut(nl), IffVal::Refut(nr)) => {
            let mp = {
                let (r2, nl) = (r.clone(), nl);
                lam_fv(0x9C03, l.clone(), move |h| {
                    false_elim_kernel(&r2, Expr::app(nl, h))
                })
            };
            let mpr = {
                let (l2, nr) = (l.clone(), nr);
                lam_fv(0x9C04, r.clone(), move |h| {
                    false_elim_kernel(&l2, Expr::app(nr, h))
                })
            };
            propext_iff(l.clone(), r.clone(), mp, mpr)
        }
        _ => return None,
    })
}

/// Recursively `Classical.em`-split each atom (index `idx`), building a proof of
/// `@Eq Prop l r` in every leaf branch via [`iff_goal`]. `assign` threads the
/// per-atom `Proof`/`Refut` witness (pushed/popped as the case tree descends).
fn iff_build(
    l: &Expr,
    r: &Expr,
    atoms: &[Expr],
    idx: usize,
    assign: &mut Vec<(Expr, IffVal)>,
) -> Option<Expr> {
    if idx == atoms.len() {
        return iff_goal(l, r, assign);
    }
    let p = &atoms[idx];
    let goal = eq_prop(l.clone(), r.clone());
    // positive branch: `p` holds.
    let fv_pos = FVarId::new(0x0A00_0000 + (idx as u64) * 2);
    assign.push((p.clone(), IffVal::Proof(Expr::fvar(fv_pos))));
    let pos_inner = iff_build(l, r, atoms, idx + 1, assign)?;
    assign.pop();
    let pos = Expr::lam(
        BinderInfo::Default,
        p.clone(),
        pos_inner.abstract_fvar(fv_pos),
    );
    // negative branch: `p → False` (kernel negation).
    let fv_neg = FVarId::new(0x0A00_0000 + (idx as u64) * 2 + 1);
    let notp = arrow(p.clone(), Expr::const_str("False"));
    assign.push((p.clone(), IffVal::Refut(Expr::fvar(fv_neg))));
    let neg_inner = iff_build(l, r, atoms, idx + 1, assign)?;
    assign.pop();
    let neg = Expr::lam(BinderInfo::Default, notp, neg_inner.abstract_fvar(fv_neg));
    Some(em_case_split(p, &goal, pos, neg))
}

/// Discharge a nested Prop-equality identity `@Eq Prop l r` (both `l` and `r` are
/// themselves `@Eq Prop` trees) by a full `Classical.em` case-split over the atomic
/// propositions — the decision procedure for the `{atoms, ≐}` biconditional algebra.
/// Covers iff-associativity `((P=Q)=R)=(P=(Q=R))` and iff-left-commutativity
/// `(P=(Q=R))=(Q=(P=R))` (the two `Prop`-sort conjuncts of `eq_ac`, s83088 C2/C3),
/// and any further identity of that fragment. Gated on both sides being `@Eq Prop`
/// (so it never steals an atomic-prop leaf), capped at 6 atoms (a genuine simp
/// bundle has ≤3), and all-or-nothing: a mismatch branch or an unassigned atom
/// declines. Every branch is `propext`/`Classical.em`/`Eq.{mp,mpr}`/`False.elim`,
/// foundational closure; the caller kernel-re-checks against the stored leaf.
fn prove_iff_algebra_leaf(l: &Expr, r: &Expr) -> Option<Expr> {
    // Both sides must be Prop-equalities (the nested-iff shape).
    if as_prop_eq(l).is_none() || as_prop_eq(r).is_none() {
        return None;
    }
    let mut atoms: Vec<Expr> = Vec::new();
    collect_iff_atoms(l, &mut atoms);
    collect_iff_atoms(r, &mut atoms);
    if atoms.is_empty() || atoms.len() > 6 {
        return None;
    }
    let mut assign: Vec<(Expr, IffVal)> = Vec::new();
    iff_build(l, r, &atoms, 0, &mut assign)
}

/// Classical/constructive **propositional normal-form** simp leaves that the base
/// unit/absorption/complement library did not yet cover: the two De Morgan laws,
/// `⟶`-as-`∨`, iff-as-DNF, not-iff-as-DNF, `∧`/`∨` commutativity, and `∧`-over-`∨`
/// distributivity (both orientations). `l`/`r` are the operands of the outer
/// `@Eq Prop l r`. Every branch is a pure `Prop` tautology built from
/// `propext` + `Classical.em` + the impredicative-connective encodings only
/// (transitive axiom closure ⊆ `FOUNDATIONAL_AXIOMS`). All shape-gated and
/// all-or-nothing: returns `None` on any other shape, and the caller kernel-re-checks
/// the returned term against the stored leaf, so a mis-shape rejects the whole
/// bundle — never miscounts. Discharges (with the base library) the corpus
/// normal-form bundles `s95156`, `s2325842`, and `s2325932`.
fn prove_classical_prop_leaf(l: &Expr, r: &Expr) -> Option<Expr> {
    let kfalse_arrow = |p: &Expr| arrow(p.clone(), Expr::const_str("False"));

    // ── (a = b) = (b = a)  (eq-commute at ANY sort — `eq_ac`, s83088 C1) ──
    // The object-sort equality commute `@Eq α a b ≐ @Eq α b a`; the leaf proof is
    // `propext (Iff.intro Eq.symm Eq.symm)` with `Eq.symm` at the sort's own level.
    if let Some(p) = prove_eq_commute_leaf(l, r) {
        return Some(p);
    }

    // ── nested Prop-equality (iff) identities: iff-assoc / iff-left-commute ─
    // The `eq_ac` iff conjuncts (`(P=(Q=R))=(Q=(P=R))`, `((P=Q)=R)=(P=(Q=R))`,
    // s83088 C2/C3) and any other identity of the `{atoms, ≐}` biconditional
    // algebra: decided by a full `Classical.em` case-split over the atoms.
    if let Some(p) = prove_iff_algebra_leaf(l, r) {
        return Some(p);
    }

    // ── (P ∧ Q) = (Q ∧ P)  (conj commutativity) ──────────────────────────
    if let (Some((a, b)), Some((rb, ra))) = (as_conj(l), as_conj(r)) {
        if rb == b && ra == a {
            let mp = {
                let (a, b) = (a.clone(), b.clone());
                lam_fv(0x9101, l.clone(), move |h| {
                    conj_intro(&b, &a, conj_right(&a, &b, h.clone()), conj_left(&a, &b, h))
                })
            };
            let mpr = {
                let (a, b) = (a.clone(), b.clone());
                lam_fv(0x9102, r.clone(), move |h| {
                    conj_intro(&a, &b, conj_right(&b, &a, h.clone()), conj_left(&b, &a, h))
                })
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
    }

    // ── (P ∨ Q) = (Q ∨ P)  (disj commutativity) ──────────────────────────
    if let (Some((a, b)), Some((rb, ra))) = (as_disj(l), as_disj(r)) {
        if rb == b && ra == a {
            let mp = {
                let (a, b, r2) = (a.clone(), b.clone(), r.clone());
                lam_fv(0x9201, l.clone(), move |h| {
                    let fa = {
                        let (a, b) = (a.clone(), b.clone());
                        lam_fv(0x9202, a.clone(), move |ha| disj_inr(&b, &a, ha))
                    };
                    let fb = {
                        let (a, b) = (a.clone(), b.clone());
                        lam_fv(0x9203, b.clone(), move |hb| disj_inl(&b, &a, hb))
                    };
                    disj_elim(&r2, h, fa, fb)
                })
            };
            let mpr = {
                let (a, b, l2) = (a.clone(), b.clone(), l.clone());
                lam_fv(0x9204, r.clone(), move |h| {
                    let fb = {
                        let (a, b) = (a.clone(), b.clone());
                        lam_fv(0x9205, b.clone(), move |hb| disj_inr(&a, &b, hb))
                    };
                    let fa = {
                        let (a, b) = (a.clone(), b.clone());
                        lam_fv(0x9206, a.clone(), move |ha| disj_inl(&a, &b, ha))
                    };
                    disj_elim(&l2, h, fb, fa)
                })
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
    }

    // ── (P ∧ (Q ∨ R)) = ((P ∧ Q) ∨ (P ∧ R))  (left distributivity) ───────
    if let Some((a, b)) = as_conj(l) {
        if let (Some((q, rr)), Some((rl, rr2))) = (as_disj(&b), as_disj(r)) {
            let caq = mk_conj(&a, &q);
            let carr = mk_conj(&a, &rr);
            if rl == caq && rr2 == carr {
                let mp = {
                    let (a, b, q, rr, caq, carr, r2) = (
                        a.clone(),
                        b.clone(),
                        q.clone(),
                        rr.clone(),
                        caq.clone(),
                        carr.clone(),
                        r.clone(),
                    );
                    lam_fv(0x9301, l.clone(), move |h| {
                        let hp = conj_left(&a, &b, h.clone());
                        let hqr = conj_right(&a, &b, h);
                        let fa = {
                            let (a, q, caq, carr, hp) =
                                (a.clone(), q.clone(), caq.clone(), carr.clone(), hp.clone());
                            lam_fv(0x9302, q.clone(), move |hq| {
                                disj_inl(&caq, &carr, conj_intro(&a, &q, hp, hq))
                            })
                        };
                        let fb = {
                            let (a, rr, caq, carr) =
                                (a.clone(), rr.clone(), caq.clone(), carr.clone());
                            lam_fv(0x9303, rr.clone(), move |hr| {
                                disj_inr(&caq, &carr, conj_intro(&a, &rr, hp, hr))
                            })
                        };
                        disj_elim(&r2, hqr, fa, fb)
                    })
                };
                let mpr = {
                    let (a, b, q, rr, l2) =
                        (a.clone(), b.clone(), q.clone(), rr.clone(), l.clone());
                    lam_fv(0x9304, r.clone(), move |h| {
                        let faq = {
                            let (a, b, q, rr) = (a.clone(), b.clone(), q.clone(), rr.clone());
                            lam_fv(0x9305, mk_conj(&a, &q), move |haq| {
                                conj_intro(
                                    &a,
                                    &b,
                                    conj_left(&a, &q, haq.clone()),
                                    disj_inl(&q, &rr, conj_right(&a, &q, haq)),
                                )
                            })
                        };
                        let far = {
                            let (a, b, q, rr) = (a.clone(), b.clone(), q.clone(), rr.clone());
                            lam_fv(0x9306, mk_conj(&a, &rr), move |har| {
                                conj_intro(
                                    &a,
                                    &b,
                                    conj_left(&a, &rr, har.clone()),
                                    disj_inr(&q, &rr, conj_right(&a, &rr, har)),
                                )
                            })
                        };
                        disj_elim(&l2, h, faq, far)
                    })
                };
                return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
            }
        }
    }

    // ── ((P ∨ Q) ∧ R) = ((P ∧ R) ∨ (Q ∧ R))  (right distributivity) ──────
    if let Some((a, b)) = as_conj(l) {
        if let (Some((p, q)), Some((rl, rr2))) = (as_disj(&a), as_disj(r)) {
            let cpr = mk_conj(&p, &b);
            let cqr = mk_conj(&q, &b);
            if rl == cpr && rr2 == cqr {
                let mp = {
                    let (a, b, p, q, cpr, cqr, r2) = (
                        a.clone(),
                        b.clone(),
                        p.clone(),
                        q.clone(),
                        cpr.clone(),
                        cqr.clone(),
                        r.clone(),
                    );
                    lam_fv(0x9401, l.clone(), move |h| {
                        let hpq = conj_left(&a, &b, h.clone());
                        let hc = conj_right(&a, &b, h);
                        let fp = {
                            let (b, p, cpr, cqr, hc) =
                                (b.clone(), p.clone(), cpr.clone(), cqr.clone(), hc.clone());
                            lam_fv(0x9402, p.clone(), move |hp| {
                                disj_inl(&cpr, &cqr, conj_intro(&p, &b, hp, hc))
                            })
                        };
                        let fq = {
                            let (b, q, cpr, cqr) = (b.clone(), q.clone(), cpr.clone(), cqr.clone());
                            lam_fv(0x9403, q.clone(), move |hq| {
                                disj_inr(&cpr, &cqr, conj_intro(&q, &b, hq, hc))
                            })
                        };
                        disj_elim(&r2, hpq, fp, fq)
                    })
                };
                let mpr = {
                    let (a, b, p, q, l2) = (a.clone(), b.clone(), p.clone(), q.clone(), l.clone());
                    lam_fv(0x9404, r.clone(), move |h| {
                        let fpr = {
                            let (a, b, p, q) = (a.clone(), b.clone(), p.clone(), q.clone());
                            lam_fv(0x9405, mk_conj(&p, &b), move |hpc| {
                                conj_intro(
                                    &a,
                                    &b,
                                    disj_inl(&p, &q, conj_left(&p, &b, hpc.clone())),
                                    conj_right(&p, &b, hpc),
                                )
                            })
                        };
                        let fqr = {
                            let (a, b, p, q) = (a.clone(), b.clone(), p.clone(), q.clone());
                            lam_fv(0x9406, mk_conj(&q, &b), move |hqc| {
                                conj_intro(
                                    &a,
                                    &b,
                                    disj_inr(&p, &q, conj_left(&q, &b, hqc.clone())),
                                    conj_right(&q, &b, hqc),
                                )
                            })
                        };
                        disj_elim(&l2, h, fpr, fqr)
                    })
                };
                return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
            }
        }
    }

    // ── ¬(P ∧ Q) = (¬P ∨ ¬Q)  (De Morgan, conj) ──────────────────────────
    if let Some(inner) = hol_not_arg(l) {
        if let (Some((a, b)), Some((na, nb))) = (as_conj(&inner), as_disj(r)) {
            if na == mk_not(&a) && nb == mk_not(&b) {
                let mp = {
                    let (a, b, na, nb, r2) =
                        (a.clone(), b.clone(), na.clone(), nb.clone(), r.clone());
                    lam_fv(0x9501, l.clone(), move |h| {
                        let pos_a = {
                            let (a, b, na, nb, r3, h) = (
                                a.clone(),
                                b.clone(),
                                na.clone(),
                                nb.clone(),
                                r2.clone(),
                                h.clone(),
                            );
                            lam_fv(0x9502, a.clone(), move |ha| {
                                let pos_b = {
                                    let (a, b, r4, h) =
                                        (a.clone(), b.clone(), r3.clone(), h.clone());
                                    lam_fv(0x9503, b.clone(), move |hb| {
                                        let contra =
                                            Expr::app(h, conj_intro(&a, &b, ha.clone(), hb));
                                        false_elim_at(&r4, contra)
                                    })
                                };
                                let neg_b = {
                                    let (b, na, nb) = (b.clone(), na.clone(), nb.clone());
                                    lam_fv(0x9504, kfalse_arrow(&b), move |hnb| {
                                        disj_inr(&na, &nb, kernel_not_to_hol_not(&b, hnb))
                                    })
                                };
                                em_case_split(&b, &r3, pos_b, neg_b)
                            })
                        };
                        let neg_a = {
                            let (a, na, nb) = (a.clone(), na.clone(), nb.clone());
                            lam_fv(0x9505, kfalse_arrow(&a), move |hna| {
                                disj_inl(&na, &nb, kernel_not_to_hol_not(&a, hna))
                            })
                        };
                        em_case_split(&a, &r2, pos_a, neg_a)
                    })
                };
                let mpr = {
                    let (a, b, _na, _nb) = (a.clone(), b.clone(), na.clone(), nb.clone());
                    lam_fv(0x9506, r.clone(), move |h| {
                        let (a2, b2) = (a.clone(), b.clone());
                        lam_fv(0x9507, mk_conj(&a2, &b2), move |hpq| {
                            let fa = {
                                let (a, b, hpq) = (a.clone(), b.clone(), hpq.clone());
                                lam_fv(0x9508, mk_not(&a), move |hna| {
                                    Expr::app(hna, conj_left(&a, &b, hpq))
                                })
                            };
                            let fb = {
                                let (a, b, hpq) = (a.clone(), b.clone(), hpq.clone());
                                lam_fv(0x9509, mk_not(&b), move |hnb| {
                                    Expr::app(hnb, conj_right(&a, &b, hpq))
                                })
                            };
                            disj_elim(&false_enc(), h.clone(), fa, fb)
                        })
                    })
                };
                return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
            }
        }
    }

    // ── ¬(P ∨ Q) = (¬P ∧ ¬Q)  (De Morgan, disj — constructive) ───────────
    if let Some(inner) = hol_not_arg(l) {
        if let (Some((a, b)), Some((na, nb))) = (as_disj(&inner), as_conj(r)) {
            if na == mk_not(&a) && nb == mk_not(&b) {
                let mp = {
                    let (a, b, na, nb) = (a.clone(), b.clone(), na.clone(), nb.clone());
                    lam_fv(0x9601, l.clone(), move |h| {
                        let pna = {
                            let (a, b, h) = (a.clone(), b.clone(), h.clone());
                            lam_fv(0x9602, a.clone(), move |ha| {
                                Expr::app(h, disj_inl(&a, &b, ha))
                            })
                        };
                        let pnb = {
                            let (a, b) = (a.clone(), b.clone());
                            lam_fv(0x9603, b.clone(), move |hb| {
                                Expr::app(h, disj_inr(&a, &b, hb))
                            })
                        };
                        conj_intro(&na, &nb, pna, pnb)
                    })
                };
                let mpr = {
                    let (a, b, na, nb) = (a.clone(), b.clone(), na.clone(), nb.clone());
                    lam_fv(0x9604, r.clone(), move |h| {
                        let (a2, b2) = (a.clone(), b.clone());
                        lam_fv(0x9605, mk_disj(&a2, &b2), move |hpq| {
                            let fa = {
                                let (a, _b, na, nb, h) =
                                    (a.clone(), b.clone(), na.clone(), nb.clone(), h.clone());
                                lam_fv(0x9606, a.clone(), move |ha| {
                                    Expr::app(conj_left(&na, &nb, h), ha)
                                })
                            };
                            let fb = {
                                let (_a, b, na, nb) =
                                    (a.clone(), b.clone(), na.clone(), nb.clone());
                                lam_fv(0x9607, b.clone(), move |hb| {
                                    Expr::app(conj_right(&na, &nb, h), hb)
                                })
                            };
                            disj_elim(&false_enc(), hpq, fa, fb)
                        })
                    })
                };
                return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
            }
        }
    }

    // ── ¬(P = Q) = ((P ∧ ¬Q) ∨ (¬P ∧ Q))  (not-iff DNF) ──────────────────
    if let Some(inner) = hol_not_arg(l) {
        if let (Some((ea, a, b)), Some((c1, c2))) = (eq_three_parts(&inner), as_disj(r)) {
            if ea == prop() && c1 == mk_conj(&a, &mk_not(&b)) && c2 == mk_conj(&mk_not(&a), &b) {
                let na = mk_not(&a);
                let nb = mk_not(&b);
                let mp = {
                    let (a, b, na, nb, c1, c2, r2) = (
                        a.clone(),
                        b.clone(),
                        na.clone(),
                        nb.clone(),
                        c1.clone(),
                        c2.clone(),
                        r.clone(),
                    );
                    lam_fv(0x9701, l.clone(), move |h| {
                        // h : ¬(a=b) = (a=b) → False_enc
                        let pos_a = {
                            let (a, b, nb, c1, c2, h) = (
                                a.clone(),
                                b.clone(),
                                nb.clone(),
                                c1.clone(),
                                c2.clone(),
                                h.clone(),
                            );
                            lam_fv(0x9702, a.clone(), move |ha| {
                                // ¬b : b → False_enc  =  λhb. h (propext-ish (a=b))
                                let nb_pf = {
                                    let (a, b, ha, h) =
                                        (a.clone(), b.clone(), ha.clone(), h.clone());
                                    lam_fv(0x9703, b.clone(), move |hb| {
                                        let eqab = propext_iff(
                                            a.clone(),
                                            b.clone(),
                                            {
                                                let hb = hb.clone();
                                                lam_fv(0x9704, a.clone(), move |_x| hb.clone())
                                            },
                                            {
                                                let ha = ha.clone();
                                                lam_fv(0x9705, b.clone(), move |_y| ha.clone())
                                            },
                                        );
                                        Expr::app(h, eqab)
                                    })
                                };
                                disj_inl(&c1, &c2, conj_intro(&a, &nb, ha, nb_pf))
                            })
                        };
                        let neg_a = {
                            let (a, b, na, c1, c2, r3, h) = (
                                a.clone(),
                                b.clone(),
                                na.clone(),
                                c1.clone(),
                                c2.clone(),
                                r2.clone(),
                                h.clone(),
                            );
                            lam_fv(0x9706, kfalse_arrow(&a), move |hna_k| {
                                let hna = kernel_not_to_hol_not(&a, hna_k);
                                // Need `b` to build (¬P ∧ Q); split on b.
                                let pos_b = {
                                    let (_a, b, na, c1, c2, hna) = (
                                        a.clone(),
                                        b.clone(),
                                        na.clone(),
                                        c1.clone(),
                                        c2.clone(),
                                        hna.clone(),
                                    );
                                    lam_fv(0x9707, b.clone(), move |hb| {
                                        disj_inr(&c1, &c2, conj_intro(&na, &b, hna, hb))
                                    })
                                };
                                let neg_b = {
                                    let (a, b, _na, r4, h, hna) = (
                                        a.clone(),
                                        b.clone(),
                                        na.clone(),
                                        r3.clone(),
                                        h.clone(),
                                        hna.clone(),
                                    );
                                    lam_fv(0x9708, kfalse_arrow(&b), move |hnb_k| {
                                        // a=b via double-negation: both false → equal.
                                        let hnb = kernel_not_to_hol_not(&b, hnb_k);
                                        let eqab = propext_iff(
                                            a.clone(),
                                            b.clone(),
                                            {
                                                let (a, b, hna) =
                                                    (a.clone(), b.clone(), hna.clone());
                                                lam_fv(0x9709, a.clone(), move |ha2| {
                                                    false_elim_at(&b, Expr::app(hna, ha2))
                                                })
                                            },
                                            {
                                                let (a, b, hnb) =
                                                    (a.clone(), b.clone(), hnb.clone());
                                                lam_fv(0x970a, b.clone(), move |hb2| {
                                                    false_elim_at(&a, Expr::app(hnb, hb2))
                                                })
                                            },
                                        );
                                        false_elim_at(&r4, Expr::app(h, eqab))
                                    })
                                };
                                em_case_split(&b, &r3, pos_b, neg_b)
                            })
                        };
                        em_case_split(&a, &r2, pos_a, neg_a)
                    })
                };
                let mpr = {
                    let (a, b, na, nb, _c1, _c2) = (
                        a.clone(),
                        b.clone(),
                        na.clone(),
                        nb.clone(),
                        c1.clone(),
                        c2.clone(),
                    );
                    lam_fv(0x970b, r.clone(), move |h| {
                        // From either disjunct build (a=b) → False_enc.
                        let (a2, b2) = (a.clone(), b.clone());
                        lam_fv(0x970c, mk_iff_eq(&a2, &b2), move |heq| {
                            let f1 = {
                                let (a, b, nb, heq) =
                                    (a.clone(), b.clone(), nb.clone(), heq.clone());
                                lam_fv(0x970d, mk_conj(&a, &nb), move |h1| {
                                    // h1 : a ∧ ¬b ; from heq:a=b and (a from h1) get b, contra ¬b.
                                    let ha = conj_left(&a, &nb, h1.clone());
                                    let hnb = conj_right(&a, &nb, h1);
                                    let hb = eq_mp(&a, &b, heq.clone(), ha);
                                    Expr::app(hnb, hb)
                                })
                            };
                            let f2 = {
                                let (a, b, na, heq) =
                                    (a.clone(), b.clone(), na.clone(), heq.clone());
                                lam_fv(0x970e, mk_conj(&na, &b), move |h2| {
                                    let hna = conj_left(&na, &b, h2.clone());
                                    let hb = conj_right(&na, &b, h2);
                                    let ha = eq_mpr(&a, &b, heq.clone(), hb);
                                    Expr::app(hna, ha)
                                })
                            };
                            disj_elim(&false_enc(), h.clone(), f1, f2)
                        })
                    })
                };
                return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
            }
        }
    }

    // ── (P ⟶ Q) = (¬P ∨ Q)  (implication as disjunction) ─────────────────
    if let (Some((a, b)), Some((na, b2))) = (as_arrow(l), as_disj(r)) {
        if na == mk_not(&a) && b2 == b {
            let mp = {
                let (a, b, na, r2) = (a.clone(), b.clone(), na.clone(), r.clone());
                lam_fv(0x9801, l.clone(), move |h| {
                    let pos = {
                        let (a, b, na, h) = (a.clone(), b.clone(), na.clone(), h.clone());
                        lam_fv(0x9802, a.clone(), move |hp| {
                            disj_inr(&na, &b, Expr::app(h, hp))
                        })
                    };
                    let neg = {
                        let (a, b, na) = (a.clone(), b.clone(), na.clone());
                        lam_fv(0x9803, kfalse_arrow(&a), move |hnp| {
                            disj_inl(&na, &b, kernel_not_to_hol_not(&a, hnp))
                        })
                    };
                    em_case_split(&a, &r2, pos, neg)
                })
            };
            let mpr = {
                let (a, b, na) = (a.clone(), b.clone(), na.clone());
                lam_fv(0x9804, r.clone(), move |h| {
                    let (a2, b2) = (a.clone(), b.clone());
                    lam_fv(0x9805, a2.clone(), move |hp| {
                        let fna = {
                            let (b, na, hp) = (b.clone(), na.clone(), hp.clone());
                            lam_fv(0x9806, na.clone(), move |hna| {
                                false_elim_at(&b, Expr::app(hna, hp))
                            })
                        };
                        let fq = lam_fv(0x9807, b2.clone(), |hq| hq);
                        disj_elim(&b2, h.clone(), fna, fq)
                    })
                })
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
    }

    // ── (P = Q) = ((P ∧ Q) ∨ (¬P ∧ ¬Q))  (iff as DNF) ────────────────────
    if let (Some((ea, a, b)), Some((c1, c2))) = (eq_three_parts(l), as_disj(r)) {
        if ea == prop() && c1 == mk_conj(&a, &b) && c2 == mk_conj(&mk_not(&a), &mk_not(&b)) {
            let na = mk_not(&a);
            let nb = mk_not(&b);
            let mp = {
                let (a, b, na, nb, c1, c2, r2) = (
                    a.clone(),
                    b.clone(),
                    na.clone(),
                    nb.clone(),
                    c1.clone(),
                    c2.clone(),
                    r.clone(),
                );
                lam_fv(0x9901, l.clone(), move |h| {
                    let pos = {
                        let (a, b, c1, c2, h) =
                            (a.clone(), b.clone(), c1.clone(), c2.clone(), h.clone());
                        lam_fv(0x9902, a.clone(), move |hp| {
                            let hq = eq_mp(&a, &b, h, hp.clone());
                            disj_inl(&c1, &c2, conj_intro(&a, &b, hp, hq))
                        })
                    };
                    let neg = {
                        let (a, b, na, nb, c1, c2, h) = (
                            a.clone(),
                            b.clone(),
                            na.clone(),
                            nb.clone(),
                            c1.clone(),
                            c2.clone(),
                            h.clone(),
                        );
                        lam_fv(0x9903, kfalse_arrow(&a), move |hnp_k| {
                            let hna = kernel_not_to_hol_not(&a, hnp_k);
                            let hnb = {
                                let (a, b, hna, h) = (a.clone(), b.clone(), hna.clone(), h.clone());
                                lam_fv(0x9904, b.clone(), move |hq| {
                                    let hp = eq_mpr(&a, &b, h, hq);
                                    Expr::app(hna, hp)
                                })
                            };
                            disj_inr(&c1, &c2, conj_intro(&na, &nb, hna, hnb))
                        })
                    };
                    em_case_split(&a, &r2, pos, neg)
                })
            };
            let mpr = {
                let (a, b, na, nb, c1, c2, l2) = (
                    a.clone(),
                    b.clone(),
                    na.clone(),
                    nb.clone(),
                    c1.clone(),
                    c2.clone(),
                    l.clone(),
                );
                lam_fv(0x9905, r.clone(), move |h| {
                    let fboth = {
                        let (a, b, c1, c2) = (a.clone(), b.clone(), c1.clone(), c2.clone());
                        let _ = (&c2,);
                        lam_fv(0x9906, c1.clone(), move |hpq| {
                            let fwd = {
                                let (a, b, hpq) = (a.clone(), b.clone(), hpq.clone());
                                lam_fv(0x9907, a.clone(), move |_x| conj_right(&a, &b, hpq))
                            };
                            let bwd = {
                                let (a, b, hpq) = (a.clone(), b.clone(), hpq.clone());
                                lam_fv(0x9908, b.clone(), move |_y| conj_left(&a, &b, hpq))
                            };
                            propext_iff(a.clone(), b.clone(), fwd, bwd)
                        })
                    };
                    let fneither = {
                        let (a, b, na, nb, c2) =
                            (a.clone(), b.clone(), na.clone(), nb.clone(), c2.clone());
                        lam_fv(0x9909, c2.clone(), move |hnn| {
                            let hna = conj_left(&na, &nb, hnn.clone());
                            let hnb = conj_right(&na, &nb, hnn);
                            let fwd = {
                                let (a, b, hna) = (a.clone(), b.clone(), hna.clone());
                                lam_fv(0x990a, a.clone(), move |ha| {
                                    false_elim_at(&b, Expr::app(hna, ha))
                                })
                            };
                            let bwd = {
                                let (a, b, hnb) = (a.clone(), b.clone(), hnb.clone());
                                lam_fv(0x990b, b.clone(), move |hb| {
                                    false_elim_at(&a, Expr::app(hnb, hb))
                                })
                            };
                            propext_iff(a.clone(), b.clone(), fwd, bwd)
                        })
                    };
                    disj_elim(&l2, h, fboth, fneither)
                })
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
    }

    None
}

/// The embedded HOL `@Eq Prop a b` (bool-equality / iff), as it appears as the LHS
/// of the `iff`-DNF leaves. Delegates to the shared Prop-eq builder.
fn mk_iff_eq(a: &Expr, b: &Expr) -> Expr {
    eq_prop(a.clone(), b.clone())
}

/// Discharge a **quantifier** simp leaf `@Eq Prop l r` using an available
/// `Nonempty α` witness. Covers the vacuous `(∀x. P) = P` / `(∃x. P) = P` and the
/// two `∧`-miniscoping laws of `all_simps`. Returns `None` for any other shape (the
/// caller then tries the propositional arms). Every branch is `propext` of an
/// `Iff.intro` whose two directions are pure λ-terms + `Classical.choice` (via the
/// pre-built witness element) — foundational closure. Kernel-re-checked by the caller.
fn prove_quantifier_leaf(l: &Expr, r: &Expr, witnesses: &[(Expr, Expr)]) -> Option<Expr> {
    // ── ∃-miniscoping (ex_simps conjuncts): the `∃`-duals of `all_simps` ───
    // `l` is an `ex_encoding` (structurally a `Π(Q:Prop). …`), so try it before the
    // `∀`-shaped arms below.
    if let Some(p) = ex_miniscope_leaf(l, r, witnesses) {
        return Some(p);
    }

    let ExprKind::Pi(_, dom, body) = l.kind() else {
        return None;
    };

    // ── vacuous ∀:  (∀x:α. P) = P  ≡  (Π(_:α). r) = r ────────────────────
    // `body` is `r` re-embedded under the α binder; a vacuous body ignores the bound
    // variable, so it carries no loose `BVar(0)` and equals `r` structurally.
    if !body.has_loose_bvar(0) && **body == *r {
        if let Some(w) = witness_for(dom, witnesses) {
            let alpha = (**dom).clone();
            // mp : (Π_:α.r) → r   =   λ(h). h w
            let mp = lam_fv(0x7001, l.clone(), move |h| Expr::app(h, w));
            // mpr : r → (Π_:α.r)  =   λ(hp). λ(_:α). hp
            let mpr = lam_fv(0x7002, r.clone(), move |hp| {
                Expr::lam(BinderInfo::Default, alpha, hp)
            });
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
    }

    // ── vacuous ∃:  (∃x:α. P) = P ─────────────────────────────────────────
    // LHS = ∀(Q:Prop). (∀(x:α). P → Q) → Q with a constant predicate `λx. r`.
    if **dom == prop() {
        for (alpha, w) in witnesses {
            let pred = Expr::lam(BinderInfo::Default, alpha.clone(), r.clone());
            if ex_encoding(alpha, &pred) == *l {
                return Some(vacuous_ex_proof(l, r, alpha, w));
            }
        }
    }

    // ── ∧-miniscoping (all_simps conjuncts 1–2) ───────────────────────────
    conj_miniscope_leaf(l, r, dom, body, witnesses)
}

/// `(∃x:α. P) = P` (vacuous existential). `l` is the `ex_encoding` LHS, `r = P`,
/// `w : α` the choice witness.
fn vacuous_ex_proof(l: &Expr, r: &Expr, alpha: &Expr, w: &Expr) -> Expr {
    let (alpha, w, p) = (alpha.clone(), w.clone(), r.clone());
    // mp : LHS → P  =  λ(h). h P (λ(x:α)(hp:P). hp)
    let mp = {
        let (alpha, p) = (alpha.clone(), p.clone());
        lam_fv(0x7101, l.clone(), move |h| {
            let k = {
                let p2 = p.clone();
                lam_fv(0x7102, alpha.clone(), move |_x| {
                    lam_fv(0x7103, p2.clone(), |hp| hp)
                })
            };
            Expr::apps(h, [p.clone(), k])
        })
    };
    // mpr : P → LHS  =  λ(hp). λ(Q:Prop). λ(k:Π(_:α).P→Q). k w hp
    let mpr = {
        let (alpha, p, w) = (alpha.clone(), p.clone(), w.clone());
        lam_fv(0x7104, p.clone(), move |hp| {
            let (alpha, p, w) = (alpha.clone(), p.clone(), w.clone());
            lam_fv(0x7105, prop(), move |cq| {
                let k_ty = Expr::pi(
                    BinderInfo::Default,
                    alpha.clone(),
                    arrow(p.clone(), cq.clone()),
                );
                let (w, hp) = (w.clone(), hp.clone());
                lam_fv(0x7106, k_ty, move |k| Expr::apps(k, [w, hp]))
            })
        })
    };
    propext_iff(l.clone(), r.clone(), mp, mpr)
}

/// The two `∧`-miniscoping laws of `all_simps`:
/// `(∀x. P x ∧ Q) = ((∀x. P x) ∧ Q)` (right-const) and
/// `(∀x. P ∧ Q x) = (P ∧ (∀x. Q x))` (left-const), where the const conjunct does not
/// mention the bound variable. `l = Π(x:α). conj A B` (one of `A`,`B` carries `BVar 0`),
/// `r = conj RA RB`. Needs a `Nonempty α` witness (the forward map extracts the const
/// conjunct at the witness). Returns `None` when the shape is not a recognised
/// miniscoping law.
fn conj_miniscope_leaf(
    l: &Expr,
    r: &Expr,
    dom: &Expr,
    body: &Expr,
    witnesses: &[(Expr, Expr)],
) -> Option<Expr> {
    let alpha = dom.clone();
    let w = witness_for(&alpha, witnesses)?;
    let (a_b, b_b) = as_conj(body)?; // conjuncts under the α binder (may carry BVar 0)
    let (ra, rb) = as_conj(r)?;
    let a_dep = a_b.has_loose_bvar(0);
    let b_dep = b_b.has_loose_bvar(0);

    // right-const: `(∀x. P x ∧ Q) = ((∀x. P x) ∧ Q)` — A depends on x, B constant.
    if a_dep && !b_dep {
        let q = b_b.clone();
        let all_px = Expr::pi(BinderInfo::Default, alpha.clone(), a_b.clone());
        // r must be `conj (Πx. P x) Q`.
        if ra != all_px || rb != q {
            return None;
        }
        // mp : l → r  =  λ(h). conj_intro (Πx.Px) Q left right
        let mp = {
            let (alpha, q, all_px, w) = (alpha.clone(), q.clone(), all_px.clone(), w.clone());
            let a_b = a_b.clone();
            lam_fv(0x7201, l.clone(), move |h| {
                // left : Πx. Px  =  λ(x:α). conj_left (Px) Q (h x)
                let left = {
                    let (a_b, q, h) = (a_b.clone(), q.clone(), h.clone());
                    lam_fv(0x7202, alpha.clone(), move |x| {
                        let px = a_b.instantiate(&x);
                        conj_left(&px, &q, Expr::app(h.clone(), x))
                    })
                };
                // right : Q  =  conj_right (P w) Q (h w)
                let pw = a_b.instantiate(&w);
                let right = conj_right(&pw, &q, Expr::app(h, w.clone()));
                conj_intro(&all_px, &q, left, right)
            })
        };
        // mpr : r → l  =  λ(hr). λ(x:α). conj_intro (Px) Q ((left hr) x) (right hr)
        let mpr = {
            let (alpha, q, all_px) = (alpha.clone(), q.clone(), all_px.clone());
            let a_b = a_b.clone();
            lam_fv(0x7203, r.clone(), move |hr| {
                let hl = conj_left(&all_px, &q, hr.clone()); // : Πx.Px
                let hrr = conj_right(&all_px, &q, hr); // : Q
                let (a_b, q, hl, hrr) = (a_b.clone(), q.clone(), hl.clone(), hrr.clone());
                lam_fv(0x7204, alpha.clone(), move |x| {
                    let px = a_b.instantiate(&x);
                    conj_intro(&px, &q, Expr::app(hl.clone(), x), hrr.clone())
                })
            })
        };
        return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
    }

    // left-const: `(∀x. P ∧ Q x) = (P ∧ (∀x. Q x))` — B depends on x, A constant.
    if b_dep && !a_dep {
        let p = a_b.clone();
        let all_qx = Expr::pi(BinderInfo::Default, alpha.clone(), b_b.clone());
        if ra != p || rb != all_qx {
            return None;
        }
        // mp : l → r  =  λ(h). conj_intro P (Πx.Qx) left right
        let mp = {
            let (alpha, p, all_qx, w) = (alpha.clone(), p.clone(), all_qx.clone(), w.clone());
            let b_b = b_b.clone();
            lam_fv(0x7211, l.clone(), move |h| {
                // left : P  =  conj_left P (Q w) (h w)
                let qw = b_b.instantiate(&w);
                let left = conj_left(&p, &qw, Expr::app(h.clone(), w.clone()));
                // right : Πx. Qx  =  λ(x:α). conj_right P (Qx) (h x)
                let right = {
                    let (b_b, p, h) = (b_b.clone(), p.clone(), h.clone());
                    lam_fv(0x7212, alpha.clone(), move |x| {
                        let qx = b_b.instantiate(&x);
                        conj_right(&p, &qx, Expr::app(h.clone(), x))
                    })
                };
                conj_intro(&p, &all_qx, left, right)
            })
        };
        // mpr : r → l  =  λ(hr). λ(x:α). conj_intro P (Qx) (left hr) ((right hr) x)
        let mpr = {
            let (alpha, p, all_qx) = (alpha.clone(), p.clone(), all_qx.clone());
            let b_b = b_b.clone();
            lam_fv(0x7213, r.clone(), move |hr| {
                let hl = conj_left(&p, &all_qx, hr.clone()); // : P
                let hrr = conj_right(&p, &all_qx, hr); // : Πx.Qx
                let (b_b, p, hl, hrr) = (b_b.clone(), p.clone(), hl.clone(), hrr.clone());
                lam_fv(0x7214, alpha.clone(), move |x| {
                    let qx = b_b.instantiate(&x);
                    conj_intro(&p, &qx, hl.clone(), Expr::app(hrr.clone(), x))
                })
            })
        };
        return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
    }

    None
}

// ── ∃-encoding miniscoping (ex_simps: the ∃-duals of all_simps) ─────────────

/// Decode `l = ex_encoding(α, pred)` into `(α, body_at_x, fx)` where `body_at_x` is
/// `pred` applied to a fresh fvar `fx` and β-reduced (exposing the `conj`/`disj`/`→`
/// head under the binder). Mirrors the `ex_encoding` shape produced by `embed_term`;
/// returns `None` for any other shape.
fn decode_ex_enc(l: &Expr) -> Option<(Expr, Expr, FVarId)> {
    let ExprKind::Pi(_, qdom, lbody) = l.kind() else {
        return None;
    };
    if **qdom != prop() {
        return None;
    }
    let fq = FVarId::new(0x7401);
    let q = Expr::fvar(fq);
    let body = lbody.instantiate(&q);
    let (inner, q2) = as_arrow(&body)?;
    if q2 != q {
        return None;
    }
    let ExprKind::Pi(_, adom, inner_body) = inner.kind() else {
        return None;
    };
    let alpha = (**adom).clone();
    let fx = FVarId::new(0x7402);
    let x = Expr::fvar(fx);
    let ib = inner_body.instantiate(&x);
    let (pred_app, q3) = as_arrow(&ib)?;
    if q3 != q {
        return None;
    }
    Some((alpha, beta1(&pred_app), fx))
}

/// `λx. body[fx:=x]` — the predicate lambda for an `ex_encoding` from an under-binder
/// `body` mentioning the fvar `fx`.
fn pred_lam(alpha: &Expr, fx: FVarId, body: &Expr) -> Expr {
    Expr::lam(BinderInfo::Default, alpha.clone(), body.abstract_fvar(fx))
}

/// `body[fx:=xval]`.
fn inst_fx(body: &Expr, fx: FVarId, xval: &Expr) -> Expr {
    body.abstract_fvar(fx).instantiate(xval)
}

/// `ex_intro`: `λ(C:Prop)(k:Π(x:α).pred x→C). k w hpw : ex_encoding α pred`, from a
/// witness `w:α` and a proof `hpw : pred w`.
fn ex_intro(id: u64, alpha: Expr, pred: &Expr, w: &Expr, hpw: Expr) -> Expr {
    let (pred, w) = (pred.clone(), w.clone());
    lam_fv(id, prop(), move |c| {
        let k_ty = {
            let fx = FVarId::new(id + 1);
            let x = Expr::fvar(fx);
            let px = Expr::app(pred.clone(), x.clone());
            Expr::pi(
                BinderInfo::Default,
                alpha,
                arrow(px, c.clone()).abstract_fvar(fx),
            )
        };
        lam_fv(id + 2, k_ty, move |k| Expr::apps(k, [w, hpw]))
    })
}

/// `ex_elim`: `h C k : C` from `h : ex_encoding α pred` and `k : Π(x:α). pred x → C`.
fn ex_elim(h: Expr, c: &Expr, k: Expr) -> Expr {
    Expr::apps(h, [c.clone(), k])
}

/// `Π(x:α). pred x → c` — the `∃`-eliminator arm type (matches `ex_encoding`'s inner
/// arm structurally).
fn ex_arm_ty(id: u64, alpha: Expr, pred: &Expr, c: &Expr) -> Expr {
    let fx = FVarId::new(id);
    let x = Expr::fvar(fx);
    let px = Expr::app(pred.clone(), x.clone());
    Expr::pi(
        BinderInfo::Default,
        alpha,
        arrow(px, c.clone()).abstract_fvar(fx),
    )
}

/// `λ(x:α)(hc: pred_src x). f(x, hc)` — an `∃`-eliminator continuation.
fn elim_k(id: u64, alpha: Expr, pred_src: &Expr, f: impl FnOnce(Expr, Expr) -> Expr) -> Expr {
    let pred_src = pred_src.clone();
    lam_fv(id, alpha, move |x| {
        let px = Expr::app(pred_src.clone(), x.clone());
        lam_fv(id + 1, px, move |hc| f(x, hc))
    })
}

/// The `∃`-map combinator: from `h : ex_encoding α pred_src` build
/// `ex_encoding α pred_dst` by remapping each witness's evidence with
/// `f(x, hc) : pred_dst x`. `λC k. h C (λx hc. k x (f x hc))`.
fn ex_map(
    id: u64,
    alpha: Expr,
    pred_src: &Expr,
    pred_dst: &Expr,
    h: Expr,
    f: impl FnOnce(Expr, Expr) -> Expr,
) -> Expr {
    let (pred_src, pred_dst) = (pred_src.clone(), pred_dst.clone());
    lam_fv(id, prop(), move |c| {
        let k_ty = ex_arm_ty(id + 1, alpha.clone(), &pred_dst, &c);
        lam_fv(id + 3, k_ty, move |k| {
            let inner = elim_k(id + 4, alpha, &pred_src, move |x, hc| {
                Expr::apps(k, [x.clone(), f(x, hc)])
            });
            ex_elim(h, &c, inner)
        })
    })
}

/// The six `ex_simps` conjuncts — the `∃`-duals of `all_simps` — after the
/// per-conjunct `⋀P Q` meta-binders are peeled. `l = ex_encoding(α, λx. B)` with `B`
/// a `conj`/`disj`/`→` whose one operand mentions `x`; the discharge follows the
/// standard impredicative `∃`-intro/elim. The `∃∧` pair is true even over an empty
/// sort (witness-free), while the `∃∨`/`∃⟶` quartet genuinely needs the `Nonempty α`
/// witness (over an empty sort the constant operand can force the two sides apart).
/// Returns `None` for any other shape. Every branch is `propext` of an `Iff.intro`
/// built from the impredicative encodings + `Classical.em`/`Classical.choice`
/// (foundational closure); the caller kernel-re-checks against the stored leaf.
#[allow(clippy::too_many_lines)]
fn ex_miniscope_leaf(l: &Expr, r: &Expr, witnesses: &[(Expr, Expr)]) -> Option<Expr> {
    let (alpha, body, fx) = decode_ex_enc(l)?;
    let pred_l = pred_lam(&alpha, fx, &body); // λx. B  (the LHS ∃ predicate)
    let px_at = |x: &Expr, e: &Expr| inst_fx(e, fx, x); // operand `e` at witness `x`

    // ── ∃∧ miniscoping (witness-free) ─────────────────────────────────────
    if let Some((aa, bb)) = as_conj(&body) {
        let (a_dep, b_dep) = (mentions_fvar(&aa, fx), mentions_fvar(&bb, fx));
        // right-const: (∃x. Px ∧ Q) = ((∃x. Px) ∧ Q)
        if a_dep && !b_dep {
            let q = bb.clone();
            let pred_p = pred_lam(&alpha, fx, &aa);
            let (ex_px, rq) = as_conj(r)?;
            if ex_px != ex_encoding(&alpha, &pred_p) || rq != q {
                return None;
            }
            // mp : l → conj(ExPx, Q)
            let mp = {
                let (alpha, aa, q, pred_l, pred_p, ex_px) = (
                    alpha.clone(),
                    aa.clone(),
                    q.clone(),
                    pred_l.clone(),
                    pred_p.clone(),
                    ex_px.clone(),
                );
                lam_fv(0x7500, l.clone(), move |h| {
                    let qproof = {
                        let (aa2, q2) = (aa.clone(), q.clone());
                        let k = elim_k(0x7502, alpha.clone(), &pred_l, move |x, hc| {
                            conj_right(&px_at(&x, &aa2), &q2, hc)
                        });
                        ex_elim(h.clone(), &q, k)
                    };
                    let ex_p = {
                        let (aa3, q3) = (aa.clone(), q.clone());
                        ex_map(0x7504, alpha.clone(), &pred_l, &pred_p, h, move |x, hc| {
                            conj_left(&px_at(&x, &aa3), &q3, hc)
                        })
                    };
                    conj_intro(&ex_px, &q, ex_p, qproof)
                })
            };
            // mpr : conj(ExPx, Q) → l
            let mpr = {
                let (alpha, aa, q, pred_l, pred_p, ex_px) = (alpha, aa, q, pred_l, pred_p, ex_px);
                lam_fv(0x7510, r.clone(), move |hr| {
                    let hex = conj_left(&ex_px, &q, hr.clone());
                    let hq = conj_right(&ex_px, &q, hr);
                    ex_map(
                        0x7512,
                        alpha.clone(),
                        &pred_p,
                        &pred_l,
                        hex,
                        move |x, hpx| conj_intro(&px_at(&x, &aa), &q, hpx, hq),
                    )
                })
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        // left-const: (∃x. P ∧ Qx) = (P ∧ (∃x. Qx))
        if b_dep && !a_dep {
            let p = aa.clone();
            let pred_q = pred_lam(&alpha, fx, &bb);
            let (rp, ex_qx) = as_conj(r)?;
            if rp != p || ex_qx != ex_encoding(&alpha, &pred_q) {
                return None;
            }
            let mp = {
                let (alpha, bb, p, pred_l, pred_q, ex_qx) = (
                    alpha.clone(),
                    bb.clone(),
                    p.clone(),
                    pred_l.clone(),
                    pred_q.clone(),
                    ex_qx.clone(),
                );
                lam_fv(0x7520, l.clone(), move |h| {
                    let pproof = {
                        let (bb2, p2) = (bb.clone(), p.clone());
                        let k = elim_k(0x7522, alpha.clone(), &pred_l, move |x, hc| {
                            conj_left(&p2, &px_at(&x, &bb2), hc)
                        });
                        ex_elim(h.clone(), &p, k)
                    };
                    let ex_q = {
                        let (bb3, p3) = (bb.clone(), p.clone());
                        ex_map(0x7524, alpha.clone(), &pred_l, &pred_q, h, move |x, hc| {
                            conj_right(&p3, &px_at(&x, &bb3), hc)
                        })
                    };
                    conj_intro(&p, &ex_qx, pproof, ex_q)
                })
            };
            let mpr = {
                let (alpha, bb, p, pred_l, pred_q, ex_qx) = (alpha, bb, p, pred_l, pred_q, ex_qx);
                lam_fv(0x7530, r.clone(), move |hr| {
                    let hp = conj_left(&p, &ex_qx, hr.clone());
                    let hex = conj_right(&p, &ex_qx, hr);
                    ex_map(
                        0x7532,
                        alpha.clone(),
                        &pred_q,
                        &pred_l,
                        hex,
                        move |x, hqx| conj_intro(&p, &px_at(&x, &bb), hp, hqx),
                    )
                })
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        return None;
    }

    // ── ∃∨ miniscoping (needs the Nonempty witness) ───────────────────────
    if let Some((aa, bb)) = as_disj(&body) {
        let w = witness_for(&alpha, witnesses)?;
        let (a_dep, b_dep) = (mentions_fvar(&aa, fx), mentions_fvar(&bb, fx));
        // right-const: (∃x. Px ∨ Q) = ((∃x. Px) ∨ Q)
        if a_dep && !b_dep {
            let q = bb.clone();
            let pred_p = pred_lam(&alpha, fx, &aa);
            let (ex_px, rq) = as_disj(r)?;
            if ex_px != ex_encoding(&alpha, &pred_p) || rq != q {
                return None;
            }
            let goal = r.clone();
            // mp : l → disj(ExPx, Q)  =  λh. h GOAL (λx hc. disj_elim hc (inl (ex_intro x)) (inr))
            let mp = {
                let (alpha, aa, q, pred_l, pred_p, ex_px, goal) = (
                    alpha.clone(),
                    aa.clone(),
                    q.clone(),
                    pred_l.clone(),
                    pred_p.clone(),
                    ex_px.clone(),
                    goal.clone(),
                );
                lam_fv(0x7540, l.clone(), move |h| {
                    let k = {
                        let (alpha, aa, q, pred_p, ex_px, goal) = (
                            alpha.clone(),
                            aa.clone(),
                            q.clone(),
                            pred_p.clone(),
                            ex_px.clone(),
                            goal.clone(),
                        );
                        elim_k(0x7542, alpha.clone(), &pred_l, move |x, hc| {
                            let pxx = px_at(&x, &aa);
                            let fa = {
                                let (alpha, pred_p, ex_px, q, pxx) = (
                                    alpha.clone(),
                                    pred_p.clone(),
                                    ex_px.clone(),
                                    q.clone(),
                                    pxx.clone(),
                                );
                                lam_fv(0x7544, pxx.clone(), move |hpx| {
                                    disj_inl(
                                        &ex_px,
                                        &q,
                                        ex_intro(0x7546, alpha.clone(), &pred_p, &x, hpx),
                                    )
                                })
                            };
                            let fb = {
                                let (ex_px, q) = (ex_px.clone(), q.clone());
                                lam_fv(0x7548, q.clone(), move |hq| disj_inr(&ex_px, &q, hq))
                            };
                            disj_elim(&goal, hc, fa, fb)
                        })
                    };
                    ex_elim(h, &goal, k)
                })
            };
            // mpr : disj(ExPx, Q) → l   (needs witness w)
            let mpr = {
                let (alpha, aa, q, pred_l, pred_p, ex_px, w) = (
                    alpha.clone(),
                    aa.clone(),
                    q.clone(),
                    pred_l.clone(),
                    pred_p.clone(),
                    ex_px.clone(),
                    w.clone(),
                );
                lam_fv(0x7550, r.clone(), move |hr| {
                    lam_fv(0x7551, prop(), move |c| {
                        let k_ty = ex_arm_ty(0x7552, alpha.clone(), &pred_l, &c);
                        lam_fv(0x7554, k_ty, move |k| {
                            let k_fb = k.clone();
                            let fa = {
                                let (alpha, aa, q, pred_p, c) = (
                                    alpha.clone(),
                                    aa.clone(),
                                    q.clone(),
                                    pred_p.clone(),
                                    c.clone(),
                                );
                                lam_fv(0x7556, ex_px.clone(), move |hex| {
                                    let inner =
                                        elim_k(0x7558, alpha.clone(), &pred_p, move |x, hpx| {
                                            Expr::apps(
                                                k,
                                                [x.clone(), disj_inl(&px_at(&x, &aa), &q, hpx)],
                                            )
                                        });
                                    ex_elim(hex, &c, inner)
                                })
                            };
                            let fb = {
                                let (aa, q, w) = (aa.clone(), q.clone(), w.clone());
                                lam_fv(0x755A, q.clone(), move |hq| {
                                    let pw = px_at(&w, &aa);
                                    Expr::apps(k_fb, [w.clone(), disj_inr(&pw, &q, hq)])
                                })
                            };
                            disj_elim(&c, hr, fa, fb)
                        })
                    })
                })
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        // left-const: (∃x. P ∨ Qx) = (P ∨ (∃x. Qx))
        if b_dep && !a_dep {
            let p = aa.clone();
            let pred_q = pred_lam(&alpha, fx, &bb);
            let (rp, ex_qx) = as_disj(r)?;
            if rp != p || ex_qx != ex_encoding(&alpha, &pred_q) {
                return None;
            }
            let goal = r.clone();
            let mp = {
                let (alpha, bb, p, pred_l, pred_q, ex_qx, goal) = (
                    alpha.clone(),
                    bb.clone(),
                    p.clone(),
                    pred_l.clone(),
                    pred_q.clone(),
                    ex_qx.clone(),
                    goal.clone(),
                );
                lam_fv(0x7560, l.clone(), move |h| {
                    let goal_inner = goal.clone();
                    let k = elim_k(0x7562, alpha.clone(), &pred_l, move |x, hc| {
                        let qxx = px_at(&x, &bb);
                        let fa = {
                            let (p, ex_qx) = (p.clone(), ex_qx.clone());
                            lam_fv(0x7564, p.clone(), move |hp| disj_inl(&p, &ex_qx, hp))
                        };
                        let fb = {
                            let (alpha, pred_q, p, ex_qx, qxx) = (
                                alpha.clone(),
                                pred_q.clone(),
                                p.clone(),
                                ex_qx.clone(),
                                qxx.clone(),
                            );
                            lam_fv(0x7566, qxx.clone(), move |hqx| {
                                disj_inr(
                                    &p,
                                    &ex_qx,
                                    ex_intro(0x7568, alpha.clone(), &pred_q, &x, hqx),
                                )
                            })
                        };
                        disj_elim(&goal_inner, hc, fa, fb)
                    });
                    ex_elim(h, &goal, k)
                })
            };
            let mpr = {
                let (alpha, bb, p, pred_l, pred_q, ex_qx, w) = (
                    alpha.clone(),
                    bb.clone(),
                    p.clone(),
                    pred_l.clone(),
                    pred_q.clone(),
                    ex_qx.clone(),
                    w.clone(),
                );
                lam_fv(0x7570, r.clone(), move |hr| {
                    lam_fv(0x7571, prop(), move |c| {
                        let k_ty = ex_arm_ty(0x7572, alpha.clone(), &pred_l, &c);
                        lam_fv(0x7574, k_ty, move |k| {
                            let k_fa = k.clone();
                            let fa = {
                                let (bb, p, w) = (bb.clone(), p.clone(), w.clone());
                                lam_fv(0x7576, p.clone(), move |hp| {
                                    let qw = px_at(&w, &bb);
                                    Expr::apps(k_fa, [w.clone(), disj_inl(&p, &qw, hp)])
                                })
                            };
                            let fb = {
                                let (alpha, bb, p, pred_q, c) = (
                                    alpha.clone(),
                                    bb.clone(),
                                    p.clone(),
                                    pred_q.clone(),
                                    c.clone(),
                                );
                                lam_fv(0x7578, ex_qx.clone(), move |hex| {
                                    let inner =
                                        elim_k(0x757A, alpha.clone(), &pred_q, move |x, hqx| {
                                            Expr::apps(
                                                k,
                                                [x.clone(), disj_inr(&p, &px_at(&x, &bb), hqx)],
                                            )
                                        });
                                    ex_elim(hex, &c, inner)
                                })
                            };
                            disj_elim(&c, hr, fa, fb)
                        })
                    })
                })
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        return None;
    }

    // ── ∃⟶ miniscoping (needs the Nonempty witness) ───────────────────────
    if let Some((aa, bb)) = as_arrow(&body) {
        let w = witness_for(&alpha, witnesses)?;
        let (a_dep, b_dep) = (mentions_fvar(&aa, fx), mentions_fvar(&bb, fx));
        // ante-dep: (∃x. Px ⟶ Q) = ((∀x. Px) ⟶ Q)
        if a_dep && !b_dep {
            let q = bb.clone();
            let all_px = Expr::pi(BinderInfo::Default, alpha.clone(), aa.abstract_fvar(fx));
            let (rl, rq) = as_arrow(r)?;
            if rl != all_px || rq != q {
                return None;
            }
            // mp : l → (all_px → Q)  =  λh. λhall. h Q (λx himp. himp (hall x))
            let mp = {
                let (alpha, q, pred_l, all_px) =
                    (alpha.clone(), q.clone(), pred_l.clone(), all_px.clone());
                lam_fv(0x7580, l.clone(), move |h| {
                    let (alpha, q, pred_l) = (alpha.clone(), q.clone(), pred_l.clone());
                    lam_fv(0x7581, all_px.clone(), move |hall| {
                        let k = elim_k(0x7582, alpha.clone(), &pred_l, move |x, himp| {
                            Expr::app(himp, Expr::app(hall, x))
                        });
                        ex_elim(h, &q, k)
                    })
                })
            };
            // mpr : (all_px → Q) → l   (needs witness w; the drinker-paradox branch)
            let mpr = {
                let (alpha, aa, q, pred_l, all_px, w) = (
                    alpha.clone(),
                    aa.clone(),
                    q.clone(),
                    pred_l.clone(),
                    all_px.clone(),
                    w.clone(),
                );
                lam_fv(0x7590, r.clone(), move |himp2| {
                    lam_fv(0x7591, prop(), move |c| {
                        let k_ty = ex_arm_ty(0x7592, alpha.clone(), &pred_l, &c);
                        lam_fv(0x7594, k_ty, move |k| {
                            // pos : all_px → C   =  λhall. k w (λ_:Pw. himp2 hall)
                            let pos = {
                                let (aa, _q, w, himp2, k) =
                                    (aa.clone(), q.clone(), w.clone(), himp2.clone(), k.clone());
                                lam_fv(0x7596, all_px.clone(), move |hall| {
                                    let pw = px_at(&w, &aa);
                                    let pwq = {
                                        let hq = Expr::app(himp2, hall);
                                        lam_fv(0x7597, pw, move |_hpw| hq)
                                    };
                                    Expr::apps(k, [w.clone(), pwq])
                                })
                            };
                            // neg : (all_px → False) → C  (by_contra: em C, build all_px)
                            let neg = {
                                let (alpha, aa, q, pred_l, all_px, k, c) = (
                                    alpha.clone(),
                                    aa.clone(),
                                    q.clone(),
                                    pred_l.clone(),
                                    all_px.clone(),
                                    k.clone(),
                                    c.clone(),
                                );
                                lam_fv(
                                    0x7598,
                                    arrow(all_px.clone(), Expr::const_str("False")),
                                    move |hn_all| {
                                        // inner em on C:  λnc. False.elim C (hn_all all_px_proof)
                                        let neg_c = {
                                            let (alpha, aa, q, pred_l, _all_px, k, c, hn_all) = (
                                                alpha.clone(),
                                                aa.clone(),
                                                q.clone(),
                                                pred_l.clone(),
                                                all_px.clone(),
                                                k.clone(),
                                                c.clone(),
                                                hn_all.clone(),
                                            );
                                            lam_fv(
                                                0x759A,
                                                arrow(c.clone(), Expr::const_str("False")),
                                                move |nc| {
                                                    // all_px_proof : Π(x:α). Px
                                                    let all_px_proof = {
                                                        let (aa, q, pred_l, k, nc) = (
                                                            aa.clone(),
                                                            q.clone(),
                                                            pred_l.clone(),
                                                            k.clone(),
                                                            nc.clone(),
                                                        );
                                                        lam_fv(0x759C, alpha.clone(), move |x| {
                                                            let pxx = px_at(&x, &aa);
                                                            let neg_px = {
                                                                let (q, pxx, _pred_l, k, nc, x) = (
                                                                    q.clone(),
                                                                    pxx.clone(),
                                                                    pred_l.clone(),
                                                                    k.clone(),
                                                                    nc.clone(),
                                                                    x.clone(),
                                                                );
                                                                lam_fv(
                                                                    0x759E,
                                                                    arrow(
                                                                        pxx.clone(),
                                                                        Expr::const_str("False"),
                                                                    ),
                                                                    move |hnpx| {
                                                                        // pxq : Px → Q  = λhpx. False.elim Q (hnpx hpx)
                                                                        let pxq = {
                                                                            let (q, pxx, hnpx) = (
                                                                                q.clone(),
                                                                                pxx.clone(),
                                                                                hnpx.clone(),
                                                                            );
                                                                            lam_fv(
                                                                                0x75A0,
                                                                                pxx.clone(),
                                                                                move |hpx| {
                                                                                    false_elim_kernel(&q, Expr::app(hnpx, hpx))
                                                                                },
                                                                            )
                                                                        };
                                                                        let kc = Expr::apps(
                                                                            k,
                                                                            [x.clone(), pxq],
                                                                        );
                                                                        false_elim_kernel(
                                                                            &pxx,
                                                                            Expr::app(nc, kc),
                                                                        )
                                                                    },
                                                                )
                                                            };
                                                            let pos_px = lam_fv(
                                                                0x75A2,
                                                                pxx.clone(),
                                                                move |hpx| hpx,
                                                            );
                                                            em_case_split(
                                                                &pxx, &pxx, pos_px, neg_px,
                                                            )
                                                        })
                                                    };
                                                    false_elim_kernel(
                                                        &c,
                                                        Expr::app(hn_all, all_px_proof),
                                                    )
                                                },
                                            )
                                        };
                                        let pos_c = lam_fv(0x75A4, c.clone(), move |hc| hc);
                                        em_case_split(&c, &c, pos_c, neg_c)
                                    },
                                )
                            };
                            em_case_split(&all_px, &c, pos, neg)
                        })
                    })
                })
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        // cons-dep: (∃x. P ⟶ Qx) = (P ⟶ (∃x. Qx))
        if b_dep && !a_dep {
            let p = aa.clone();
            let pred_q = pred_lam(&alpha, fx, &bb);
            let (rp, ex_qx) = as_arrow(r)?;
            if rp != p || ex_qx != ex_encoding(&alpha, &pred_q) {
                return None;
            }
            // mp : l → (P → ExQx)  =  λh. λhp. h ExQx (λx himp. ex_intro x (himp hp))
            let mp = {
                let (alpha, p, pred_l, pred_q, ex_qx) = (
                    alpha.clone(),
                    p.clone(),
                    pred_l.clone(),
                    pred_q.clone(),
                    ex_qx.clone(),
                );
                lam_fv(0x75B0, l.clone(), move |h| {
                    let (alpha, p, pred_l, pred_q, ex_qx) = (
                        alpha.clone(),
                        p.clone(),
                        pred_l.clone(),
                        pred_q.clone(),
                        ex_qx.clone(),
                    );
                    lam_fv(0x75B1, p.clone(), move |hp| {
                        let k = elim_k(0x75B2, alpha.clone(), &pred_l, move |x, himp| {
                            ex_intro(0x75B4, alpha.clone(), &pred_q, &x, Expr::app(himp, hp))
                        });
                        ex_elim(h, &ex_qx, k)
                    })
                })
            };
            // mpr : (P → ExQx) → l   (needs witness w in the ¬P branch)
            let mpr = {
                let (alpha, bb, p, pred_l, pred_q, _ex_qx, w) = (
                    alpha.clone(),
                    bb.clone(),
                    p.clone(),
                    pred_l.clone(),
                    pred_q.clone(),
                    ex_qx.clone(),
                    w.clone(),
                );
                lam_fv(0x75C0, r.clone(), move |himp2| {
                    lam_fv(0x75C1, prop(), move |c| {
                        let k_ty = ex_arm_ty(0x75C2, alpha.clone(), &pred_l, &c);
                        lam_fv(0x75C4, k_ty, move |k| {
                            // pos : P → C  = λhp. (himp2 hp) C (λx hqx. k x (λ_:P. hqx))
                            let pos = {
                                let (alpha, p, pred_q, c, k, himp2) = (
                                    alpha.clone(),
                                    p.clone(),
                                    pred_q.clone(),
                                    c.clone(),
                                    k.clone(),
                                    himp2.clone(),
                                );
                                lam_fv(0x75C6, p.clone(), move |hp| {
                                    let hex = Expr::app(himp2, hp);
                                    let inner =
                                        elim_k(0x75C8, alpha.clone(), &pred_q, move |x, hqx| {
                                            let pxq = lam_fv(0x75CA, p.clone(), move |_hp| hqx);
                                            Expr::apps(k, [x, pxq])
                                        });
                                    ex_elim(hex, &c, inner)
                                })
                            };
                            // neg : (P → False) → C  = λhnp. k w (λhp:P. False.elim Qw (hnp hp))
                            let neg = {
                                let (bb, p, w, k) = (bb.clone(), p.clone(), w.clone(), k.clone());
                                lam_fv(
                                    0x75CC,
                                    arrow(p.clone(), Expr::const_str("False")),
                                    move |hnp| {
                                        let qw = px_at(&w, &bb);
                                        let pwq = {
                                            let (p, qw) = (p.clone(), qw.clone());
                                            lam_fv(0x75CE, p.clone(), move |hp| {
                                                false_elim_kernel(&qw, Expr::app(hnp, hp))
                                            })
                                        };
                                        Expr::apps(k, [w.clone(), pwq])
                                    },
                                )
                            };
                            em_case_split(&p, &c, pos, neg)
                        })
                    })
                })
            };
            return Some(propext_iff(l.clone(), r.clone(), mp, mpr));
        }
        return None;
    }

    None
}

// ── witness-free quantifier leaves (one-point rules; ∨/⟶ miniscoping) ───────

// ── witness-free quantifier leaves (one-point rules; ∨/⟶ miniscoping) ───────

/// Discharge a **witness-free** quantifier simp leaf `@Eq Prop l r`: the one-point
/// rules `(∃x. x = t ∧ P x) = P t` / `(∀x. x = t ⟶ P x) = P t` (and their `t = x`
/// twins) and the `∨`/`⟶` miniscoping laws of `all_simps` (conjuncts 3–6). None of
/// these need a nonemptiness witness — the one-point equation supplies `t` as its
/// own witness, and the `∨`/`⟶` laws are true even over an empty sort. Returns
/// `None` for any other shape (the caller then tries the witnessed / propositional
/// arms). Every branch is `propext` of an `Iff.intro` whose two directions are pure
/// λ-terms + `Classical.em` / `Eq.{refl,symm,subst}` — foundational closure. Kernel
/// re-checked by the caller against the stored leaf, so a mis-shape rejects.
fn prove_quantifier_leaf_witfree(l: &Expr, r: &Expr) -> Option<Expr> {
    if let Some(p) = forall_onepoint_leaf(l, r) {
        return Some(p);
    }
    if let Some(p) = exists_onepoint_leaf(l, r) {
        return Some(p);
    }
    if let Some(p) = forall_not_eq_leaf(l, r) {
        return Some(p);
    }
    disj_imp_miniscope_leaf(l, r)
}

/// The `all_not_eq` law `(∀x:α. x ≠ t) = False` (and its `t ≠ x` twin). `l =
/// Π(x:α). ¬(Eq α x t)`, `r = HOL.False`. Witness-free: the witness is `t` itself
/// (instantiating the universal at `t` yields `t ≠ t`, refuted by `Eq.refl`).
fn forall_not_eq_leaf(l: &Expr, r: &Expr) -> Option<Expr> {
    if !is_false_def_const(r) {
        return None;
    }
    let ExprKind::Pi(_, dom, body) = l.kind() else {
        return None;
    };
    let alpha = (**dom).clone();
    let fx = FVarId::new(0x8501);
    let x = Expr::fvar(fx);
    let cod = body.instantiate(&x);
    // body[x] must be `¬(Eq α x t)` / `¬(Eq α t x)` with `t` not mentioning `x`.
    let inner = hol_not_arg(&cod)?;
    let (ea, e1, e2) = eq_three_parts(&inner)?;
    if ea != alpha {
        return None;
    }
    let (t, _xside_left) = onepoint_witness(&e1, &e2, &x, fx)?;
    // mp : (∀x. x ≠ t) → False  =  λh. (h t) (Eq.refl α t)
    //   `h t : ¬(Eq α t t)` (δ→ `Eq α t t → False_enc`); apply to `Eq.refl`.
    let mp = {
        let (alpha, t) = (alpha.clone(), t.clone());
        lam_fv(0x8502, l.clone(), move |h| {
            let ht = Expr::app(h, t.clone());
            Expr::app(ht, eq_refl_obj(&alpha, &t))
        })
    };
    // mpr : False → (∀x. x ≠ t)  =  λhf. λ(x:α). λ(he:Eq α x t). hf <False_enc>
    let mpr = {
        let (alpha, body2) = (alpha.clone(), (**body).clone());
        lam_fv(0x8503, r.clone(), move |hf| {
            let (alpha, body2, hf) = (alpha.clone(), body2.clone(), hf.clone());
            lam_fv(0x8504, alpha.clone(), move |x| {
                // The per-`x` goal is exactly `body[x] = ¬(Eq α x t)` (δ→ eq→False_enc).
                let notgoal = body2.instantiate(&x);
                false_elim_at(&notgoal, hf.clone())
            })
        })
    };
    Some(propext_iff(l.clone(), r.clone(), mp, mpr))
}

/// The `∀` one-point rule `(∀x:α. x = t ⟶ P x) = P t` (and its `t = x` twin).
/// `l = Π(x:α). (Eq α x t) → P x`, `r = P t`. Witness-free: `t` is the witness.
fn forall_onepoint_leaf(l: &Expr, r: &Expr) -> Option<Expr> {
    let ExprKind::Pi(_, dom, body) = l.kind() else {
        return None;
    };
    let alpha = (**dom).clone();
    let fx = FVarId::new(0x8001);
    let x = Expr::fvar(fx);
    let cod = body.instantiate(&x);
    let (eqt, px) = as_arrow(&cod)?;
    let (ea, e1, e2) = eq_three_parts(&eqt)?;
    if ea != alpha {
        return None;
    }
    // `x = t` (xside_left): e1 == x, e2 == t; or the `t = x` twin: e2 == x.
    let (t, xside_left) = onepoint_witness(&e1, &e2, &x, fx)?;
    let px_body = px.abstract_fvar(fx); // P as a body under x (bvar 0)
    if px_body.instantiate(&t) != *r {
        return None;
    }
    let motive = Expr::lam(BinderInfo::Default, alpha.clone(), px_body);
    // mp : (∀x. (x=t)→P x) → P t   =   λh. h t (Eq.refl α t)
    let mp = {
        let (alpha, t) = (alpha.clone(), t.clone());
        lam_fv(0x8002, l.clone(), move |h| {
            let ht = Expr::app(h, t.clone());
            Expr::app(ht, eq_refl_obj(&alpha, &t))
        })
    };
    // mpr : P t → (∀x. (x=t)→P x)  =  λhp. λx. λhe. Eq.subst α motive t x (he:t=x) hp
    let mpr = {
        let (alpha, motive, t) = (alpha.clone(), motive.clone(), t.clone());
        lam_fv(0x8003, r.clone(), move |hp| {
            let (alpha, motive, t, hp) = (alpha.clone(), motive.clone(), t.clone(), hp.clone());
            lam_fv(0x8004, alpha.clone(), move |x| {
                let eqty = if xside_left {
                    eq_obj(&alpha, &x, &t)
                } else {
                    eq_obj(&alpha, &t, &x)
                };
                let (alpha, motive, t, hp, x) = (
                    alpha.clone(),
                    motive.clone(),
                    t.clone(),
                    hp.clone(),
                    x.clone(),
                );
                lam_fv(0x8005, eqty, move |he| {
                    let he_tx = if xside_left {
                        eq_symm_obj(&alpha, &x, &t, he) // (x=t) ⟹ t=x
                    } else {
                        he // already t=x
                    };
                    eq_subst_obj(&alpha, &motive, &t, &x, he_tx, hp) // motive x = P x
                })
            })
        })
    };
    Some(propext_iff(l.clone(), r.clone(), mp, mpr))
}

/// Identify the one-point witness `t` from a decoded equation's two operands and
/// the bound-variable fvar `x`. Returns `(t, xside_left)` where `xside_left` is
/// `true` for `x = t` and `false` for the `t = x` twin. `t` must not mention `x`.
fn onepoint_witness(e1: &Expr, e2: &Expr, x: &Expr, fx: FVarId) -> Option<(Expr, bool)> {
    if e1 == x && !mentions_fvar(e2, fx) {
        Some((e2.clone(), true))
    } else if e2 == x && !mentions_fvar(e1, fx) {
        Some((e1.clone(), false))
    } else {
        None
    }
}

/// The `∃` one-point rule `(∃x:α. x = t ∧ P x) = P t` (and its `t = x` twin).
/// `l = ex_encoding(α, λx. conj (Eq α x t) (P x))`, `r = P t`. Witness-free.
fn exists_onepoint_leaf(l: &Expr, r: &Expr) -> Option<Expr> {
    // l = Π(Q:Prop). (Π(x:α). conj(Eq α x t, P x) → Q) → Q
    let ExprKind::Pi(_, qdom, lbody) = l.kind() else {
        return None;
    };
    if **qdom != prop() {
        return None;
    }
    let fq = FVarId::new(0x8101);
    let q = Expr::fvar(fq);
    let body = lbody.instantiate(&q);
    let (inner, q2) = as_arrow(&body)?;
    if q2 != q {
        return None;
    }
    let ExprKind::Pi(_, adom, inner_body) = inner.kind() else {
        return None;
    };
    let alpha = (**adom).clone();
    let fx = FVarId::new(0x8102);
    let x = Expr::fvar(fx);
    let ib = inner_body.instantiate(&x);
    let (pred, q3) = as_arrow(&ib)?;
    if q3 != q {
        return None;
    }
    // `ex_encoding` stores the predicate applied (`(λx. …) x`); β-reduce to expose
    // the `conj` head.
    let (eqt, px) = as_conj(&beta1(&pred))?;
    let (ea, e1, e2) = eq_three_parts(&eqt)?;
    if ea != alpha {
        return None;
    }
    let (t, xside_left) = onepoint_witness(&e1, &e2, &x, fx)?;
    let px_body = px.abstract_fvar(fx);
    if px_body.instantiate(&t) != *r {
        return None;
    }
    let motive = Expr::lam(BinderInfo::Default, alpha.clone(), px_body.clone());
    // mp : l → P t  =  λh. h (P t) (λx. λhc. Eq.subst α motive x t (x=t) (conj_right hc))
    let mp = {
        let (alpha, t, r, motive, pxb) = (
            alpha.clone(),
            t.clone(),
            r.clone(),
            motive.clone(),
            px_body.clone(),
        );
        lam_fv(0x8103, l.clone(), move |h| {
            let k = {
                let (alpha, t, motive, pxb) =
                    (alpha.clone(), t.clone(), motive.clone(), pxb.clone());
                lam_fv(0x8104, alpha.clone(), move |x| {
                    let px = pxb.instantiate(&x);
                    let eqxt = if xside_left {
                        eq_obj(&alpha, &x, &t)
                    } else {
                        eq_obj(&alpha, &t, &x)
                    };
                    let predx = mk_conj(&eqxt, &px);
                    let (alpha, t, motive, x, px, eqxt) = (
                        alpha.clone(),
                        t.clone(),
                        motive.clone(),
                        x.clone(),
                        px.clone(),
                        eqxt.clone(),
                    );
                    lam_fv(0x8105, predx, move |hc| {
                        let he = conj_left(&eqxt, &px, hc.clone()); // Eq α x t / t x
                        let hpx = conj_right(&eqxt, &px, hc); // P x
                        let he_xt = if xside_left {
                            he
                        } else {
                            eq_symm_obj(&alpha, &t, &x, he) // (t=x) ⟹ x=t
                        };
                        eq_subst_obj(&alpha, &motive, &x, &t, he_xt, hpx) // motive t = P t
                    })
                })
            };
            Expr::apps(h, [r.clone(), k])
        })
    };
    // mpr : P t → l  =  λhp. λQ. λk. k t (conj_intro (Eq α t t) (P t) (Eq.refl α t) hp)
    let mpr = {
        let (alpha, t, r, pxb) = (alpha.clone(), t.clone(), r.clone(), px_body.clone());
        lam_fv(0x8106, r.clone(), move |hp| {
            let (alpha, t, r, pxb, hp) =
                (alpha.clone(), t.clone(), r.clone(), pxb.clone(), hp.clone());
            lam_fv(0x8107, prop(), move |cq| {
                let k_ty = {
                    let fx2 = FVarId::new(0x8108);
                    let x2 = Expr::fvar(fx2);
                    let px2 = pxb.instantiate(&x2);
                    let eqx = if xside_left {
                        eq_obj(&alpha, &x2, &t)
                    } else {
                        eq_obj(&alpha, &t, &x2)
                    };
                    let arm = arrow(mk_conj(&eqx, &px2), cq.clone());
                    Expr::pi(BinderInfo::Default, alpha.clone(), arm.abstract_fvar(fx2))
                };
                let (alpha, t, r, hp) = (alpha.clone(), t.clone(), r.clone(), hp.clone());
                lam_fv(0x8109, k_ty, move |k| {
                    let eqtt = eq_obj(&alpha, &t, &t);
                    let witpair = conj_intro(&eqtt, &r, eq_refl_obj(&alpha, &t), hp);
                    Expr::app(Expr::app(k, t.clone()), witpair)
                })
            })
        })
    };
    Some(propext_iff(l.clone(), r.clone(), mp, mpr))
}

/// The `∨`/`⟶` miniscoping laws of `all_simps` (conjuncts 3–6). All witness-free
/// (true even over an empty sort). `l = Π(x:α). <body>`; the recognised bodies are
/// `disj`/arrow with exactly one operand mentioning the bound `x`. Returns `None`
/// for any other shape.
fn disj_imp_miniscope_leaf(l: &Expr, r: &Expr) -> Option<Expr> {
    let ExprKind::Pi(_, dom, body) = l.kind() else {
        return None;
    };
    let alpha = (**dom).clone();
    let fx = FVarId::new(0x8201);
    let x = Expr::fvar(fx);
    let cod = body.instantiate(&x);

    // ── ∨ miniscoping (conjuncts 3, 4) ────────────────────────────────────
    if let Some((da, db)) = as_disj(&cod) {
        let (a_dep, b_dep) = (mentions_fvar(&da, fx), mentions_fvar(&db, fx));
        // conjunct 3 — right-const: `(∀x. P x ∨ Q) = ((∀x. P x) ∨ Q)`.
        if a_dep && !b_dep {
            let q = db;
            let px_body = da.abstract_fvar(fx);
            let all_px = Expr::pi(BinderInfo::Default, alpha.clone(), px_body.clone());
            let (ra, rb) = as_disj(r)?;
            if ra != all_px || rb != q {
                return None;
            }
            return Some(disj_miniscope_proof(
                l, r, &alpha, &q, &px_body, &all_px, true,
            ));
        }
        // conjunct 4 — left-const: `(∀x. P ∨ Q x) = (P ∨ (∀x. Q x))`.
        if b_dep && !a_dep {
            let p = da;
            let qx_body = db.abstract_fvar(fx);
            let all_qx = Expr::pi(BinderInfo::Default, alpha.clone(), qx_body.clone());
            let (ra, rb) = as_disj(r)?;
            if ra != p || rb != all_qx {
                return None;
            }
            return Some(disj_miniscope_proof(
                l, r, &alpha, &p, &qx_body, &all_qx, false,
            ));
        }
        return None;
    }

    // ── ⟶ miniscoping (conjuncts 5, 6) ────────────────────────────────────
    if let Some((ca, cc)) = as_arrow(&cod) {
        let (a_dep, c_dep) = (mentions_fvar(&ca, fx), mentions_fvar(&cc, fx));
        // conjunct 5 — antecedent-dep: `(∀x. P x ⟶ Q) = ((∃x. P x) ⟶ Q)`.
        if a_dep && !c_dep {
            let q = cc;
            let px_body = ca.abstract_fvar(fx);
            let pred = Expr::lam(BinderInfo::Default, alpha.clone(), px_body.clone());
            let ex_lhs = ex_encoding(&alpha, &pred);
            let (ra, rc) = as_arrow(r)?;
            if ra != ex_lhs || rc != q {
                return None;
            }
            return Some(imp_miniscope_ante_dep_proof(
                l, r, &alpha, &q, &px_body, &ex_lhs,
            ));
        }
        // conjunct 6 — consequent-dep: `(∀x. P ⟶ Q x) = (P ⟶ (∀x. Q x))`.
        if c_dep && !a_dep {
            let p = ca;
            let qx_body = cc.abstract_fvar(fx);
            let all_qx = Expr::pi(BinderInfo::Default, alpha.clone(), qx_body.clone());
            let (ra, rc) = as_arrow(r)?;
            if ra != p || rc != all_qx {
                return None;
            }
            return Some(imp_miniscope_cons_dep_proof(l, r, &alpha, &p, &all_qx));
        }
        return None;
    }

    None
}

/// The two `∨`-miniscoping laws. `right_const` selects conjunct 3
/// `(∀x. P x ∨ Q) = ((∀x. P x) ∨ Q)` (`const = Q`, `dep_body = P` under `x`,
/// `all_dep = ∀x. P x`); `!right_const` selects conjunct 4
/// `(∀x. P ∨ Q x) = (P ∨ (∀x. Q x))` (`const = P`, `dep_body = Q`).
fn disj_miniscope_proof(
    l: &Expr,
    r: &Expr,
    alpha: &Expr,
    const_op: &Expr,
    dep_body: &Expr,
    all_dep: &Expr,
    right_const: bool,
) -> Expr {
    // For a bound `x`, the per-`x` disjunction operands in source order.
    let ops_at = |dep_x: &Expr, right_const: bool| -> (Expr, Expr) {
        if right_const {
            (dep_x.clone(), const_op.clone()) // P x ∨ Q
        } else {
            (const_op.clone(), dep_x.clone()) // P ∨ Q x
        }
    };
    // mp : l → r  (excluded middle on the constant operand `const_op`).
    let mp = {
        let (alpha, const_op, dep_body, all_dep, r) = (
            alpha.clone(),
            const_op.clone(),
            dep_body.clone(),
            all_dep.clone(),
            r.clone(),
        );
        lam_fv(0x8301, l.clone(), move |h| {
            // pos : const_op → r  (inject the const side).
            let pos = {
                let (const_op, all_dep) = (const_op.clone(), all_dep.clone());
                lam_fv(0x8302, const_op.clone(), move |hc| {
                    if right_const {
                        disj_inr(&all_dep, &const_op, hc)
                    } else {
                        disj_inl(&const_op, &all_dep, hc)
                    }
                })
            };
            // neg : (const_op → False) → r  (prove the ∀-side, then inject it).
            let neg = {
                let (alpha, const_op, dep_body, all_dep, h) = (
                    alpha.clone(),
                    const_op.clone(),
                    dep_body.clone(),
                    all_dep.clone(),
                    h.clone(),
                );
                lam_fv(
                    0x8303,
                    arrow(const_op.clone(), Expr::const_str("False")),
                    move |hnc| {
                        // all_proof : ∀x. dep(x)  =  λx. disj_elim (dep x) (h x) id (absurd).
                        let all_proof = {
                            let (const_op, dep_body, hnc) =
                                (const_op.clone(), dep_body.clone(), hnc.clone());
                            lam_fv(0x8304, alpha.clone(), move |x| {
                                let depx = dep_body.instantiate(&x);
                                let (da, db) = ops_at(&depx, right_const);
                                let hx = Expr::app(h.clone(), x.clone()); // disj(da, db)
                                let fa = {
                                    let (depx, _const_op, hnc) =
                                        (depx.clone(), const_op.clone(), hnc.clone());
                                    lam_fv(0x8305, da.clone(), move |hl| {
                                        if right_const {
                                            hl // da == depx
                                        } else {
                                            // da == const_op; contradiction.
                                            false_elim_kernel(&depx, Expr::app(hnc.clone(), hl))
                                        }
                                    })
                                };
                                let fb = {
                                    let (depx, _const_op, hnc) =
                                        (depx.clone(), const_op.clone(), hnc.clone());
                                    lam_fv(0x8306, db.clone(), move |hr| {
                                        if right_const {
                                            // db == const_op; contradiction.
                                            false_elim_kernel(&depx, Expr::app(hnc.clone(), hr))
                                        } else {
                                            hr // db == depx
                                        }
                                    })
                                };
                                let _ = &const_op;
                                disj_elim(&depx, hx, fa, fb)
                            })
                        };
                        if right_const {
                            disj_inl(&all_dep, &const_op, all_proof)
                        } else {
                            disj_inr(&const_op, &all_dep, all_proof)
                        }
                    },
                )
            };
            em_case_split(&const_op, &r, pos, neg)
        })
    };
    // mpr : r → l  =  λhr. λx. disj_elim (dep x ∨ const) hr (inject) (inject).
    let mpr = {
        let (alpha, const_op, dep_body, all_dep) = (
            alpha.clone(),
            const_op.clone(),
            dep_body.clone(),
            all_dep.clone(),
        );
        lam_fv(0x8307, r.clone(), move |hr| {
            let (alpha, const_op, dep_body, all_dep, hr) = (
                alpha.clone(),
                const_op.clone(),
                dep_body.clone(),
                all_dep.clone(),
                hr.clone(),
            );
            lam_fv(0x8308, alpha.clone(), move |x| {
                let depx = dep_body.instantiate(&x);
                let (da, db) = ops_at(&depx, right_const);
                let goal = mk_disj(&da, &db);
                // arm_all : all_dep → goal  (inject `depx = hall x` on its side).
                let arm_all = {
                    let (da, db, x) = (da.clone(), db.clone(), x.clone());
                    lam_fv(0x8309, all_dep.clone(), move |hall| {
                        let inj = Expr::app(hall, x.clone()); // : depx
                        if right_const {
                            disj_inl(&da, &db, inj) // depx == da
                        } else {
                            disj_inr(&da, &db, inj) // depx == db
                        }
                    })
                };
                // arm_const : const_op → goal  (inject `const_op` on its side).
                let arm_const = {
                    let (da, db) = (da.clone(), db.clone());
                    lam_fv(0x830a, const_op.clone(), move |hc| {
                        if right_const {
                            disj_inr(&da, &db, hc) // const_op == db
                        } else {
                            disj_inl(&da, &db, hc) // const_op == da
                        }
                    })
                };
                // `hr` eliminand is `all_dep ∨ const_op` (conjunct 3) or
                // `const_op ∨ all_dep` (conjunct 4); order the case arms to match.
                if right_const {
                    disj_elim(&goal, hr.clone(), arm_all, arm_const)
                } else {
                    disj_elim(&goal, hr.clone(), arm_const, arm_all)
                }
            })
        })
    };
    propext_iff(l.clone(), r.clone(), mp, mpr)
}

/// Conjunct 5 — `(∀x. P x ⟶ Q) = ((∃x. P x) ⟶ Q)`. `px_body` is `P` under `x`,
/// `q` the constant consequent, `ex_lhs = ex_encoding(α, λx. P x)`.
fn imp_miniscope_ante_dep_proof(
    l: &Expr,
    r: &Expr,
    alpha: &Expr,
    q: &Expr,
    px_body: &Expr,
    ex_lhs: &Expr,
) -> Expr {
    // mp : l → r  =  λh. λhex. hex Q h   (`h : ∀x. P x → Q` is the eliminator arm).
    let mp = {
        let (q, ex_lhs) = (q.clone(), ex_lhs.clone());
        lam_fv(0x8401, l.clone(), move |h| {
            let (q, h) = (q.clone(), h.clone());
            lam_fv(0x8402, ex_lhs.clone(), move |hex| {
                Expr::apps(hex, [q.clone(), h.clone()])
            })
        })
    };
    // mpr : r → l  =  λhr. λx. λhpx. hr (λQ'. λk. k x hpx).
    let mpr = {
        let (alpha, px_body) = (alpha.clone(), px_body.clone());
        lam_fv(0x8403, r.clone(), move |hr| {
            let (alpha, px_body, hr) = (alpha.clone(), px_body.clone(), hr.clone());
            lam_fv(0x8404, alpha.clone(), move |x| {
                let px = px_body.instantiate(&x);
                let (alpha, px_body, hr, x) =
                    (alpha.clone(), px_body.clone(), hr.clone(), x.clone());
                lam_fv(0x8405, px, move |hpx| {
                    let exi = {
                        let (alpha, px_body, x, hpx) =
                            (alpha.clone(), px_body.clone(), x.clone(), hpx.clone());
                        lam_fv(0x8406, prop(), move |cq| {
                            let k_ty = {
                                let fy = FVarId::new(0x8407);
                                let y = Expr::fvar(fy);
                                let py = px_body.instantiate(&y);
                                let arm = arrow(py, cq.clone());
                                Expr::pi(BinderInfo::Default, alpha.clone(), arm.abstract_fvar(fy))
                            };
                            let (x, hpx) = (x.clone(), hpx.clone());
                            lam_fv(0x8408, k_ty, move |k| {
                                Expr::apps(k, [x.clone(), hpx.clone()])
                            })
                        })
                    };
                    Expr::app(hr.clone(), exi)
                })
            })
        })
    };
    propext_iff(l.clone(), r.clone(), mp, mpr)
}

/// Conjunct 6 — `(∀x. P ⟶ Q x) = (P ⟶ (∀x. Q x))`. `p` the constant antecedent,
/// `all_qx = ∀x. Q x`.
fn imp_miniscope_cons_dep_proof(l: &Expr, r: &Expr, alpha: &Expr, p: &Expr, all_qx: &Expr) -> Expr {
    // mp : l → r  =  λh. λhp. λx. h x hp.
    let mp = {
        let (alpha, p) = (alpha.clone(), p.clone());
        lam_fv(0x8501, l.clone(), move |h| {
            let (alpha, p, h) = (alpha.clone(), p.clone(), h.clone());
            lam_fv(0x8502, p.clone(), move |hp| {
                let (alpha, h, hp) = (alpha.clone(), h.clone(), hp.clone());
                lam_fv(0x8503, alpha.clone(), move |x| {
                    Expr::app(Expr::app(h.clone(), x.clone()), hp.clone())
                })
            })
        })
    };
    // mpr : r → l  =  λhr. λx. λhp. hr hp x.
    let mpr = {
        let (alpha, p, all_qx) = (alpha.clone(), p.clone(), all_qx.clone());
        lam_fv(0x8504, r.clone(), move |hr| {
            let _ = &all_qx;
            let (alpha, p, hr) = (alpha.clone(), p.clone(), hr.clone());
            lam_fv(0x8505, alpha.clone(), move |x| {
                let (p, hr, x) = (p.clone(), hr.clone(), x.clone());
                lam_fv(0x8506, p.clone(), move |hp| {
                    Expr::app(Expr::app(hr.clone(), hp.clone()), x.clone())
                })
            })
        })
    };
    propext_iff(l.clone(), r.clone(), mp, mpr)
}

/// `((¬P) = (¬Q)) = (P = Q)`: the propositional-equality congruence of negation.
/// Proved by `propext` of `(¬P = ¬Q) ↔ (P = Q)`; each direction transports one
/// side's `em` case-analysis across the hypothesis equation. `l = @Eq Prop (¬P)
/// (¬Q)`, `r = @Eq Prop P Q`, `ex = ¬P`, `ey = ¬Q`.
fn neg_cong_leaf(l: &Expr, r: &Expr, p: &Expr, q: &Expr, ex: &Expr, ey: &Expr) -> Expr {
    // From `heq : x = y` and a proof `hnx : ¬X` build `¬Y`: `λ(hy:Y). (transported
    // ¬Y-as-¬X) hy`. But we transport at the object level via `Eq.mp`/`Eq.mpr` on
    // the negations themselves. Here it is cleaner to build `P = Q` directly.
    //
    // mp : (¬P = ¬Q) → (P = Q).  Given h : ¬P = ¬Q, prove P = Q by propext:
    //   P → Q:  λhp. em Q  (Q ⇒ hq;  ¬Q ⇒ ¬P (= Eq.mpr h (holNotQ)) applied to hp
    //                       gives false_enc, apply to Q).
    //   Q → P:  symmetric with Eq.mp.
    let mp = {
        let (p, q, ex, ey) = (p.clone(), q.clone(), ex.clone(), ey.clone());
        lam_fv(0x6001, l.clone(), move |h| {
            // P → Q
            let fwd = {
                let (p, q, ex, ey, h) = (p.clone(), q.clone(), ex.clone(), ey.clone(), h.clone());
                lam_fv(0x6002, p.clone(), move |hp| {
                    let pos = lam_fv(0x6003, q.clone(), |hq| hq);
                    let neg = {
                        let (_p, q, ex, ey, h, hp) = (
                            p.clone(),
                            q.clone(),
                            ex.clone(),
                            ey.clone(),
                            h.clone(),
                            hp.clone(),
                        );
                        lam_fv(
                            0x6004,
                            arrow(q.clone(), Expr::const_str("False")),
                            move |hnq| {
                                let hol_nq = kernel_not_to_hol_not(&q, hnq); // : ¬Q (= ey)
                                                                             // hnp : ¬P  = Eq.mpr (¬P) (¬Q) h hol_nq
                                let hnp = eq_mpr(&ex, &ey, h.clone(), hol_nq);
                                // hnp hp : false_enc; apply to Q
                                let f = Expr::app(hnp, hp.clone());
                                Expr::app(f, q.clone())
                            },
                        )
                    };
                    em_case_split(&q, &q, pos, neg)
                })
            };
            // Q → P
            let bwd = {
                let (p, q, ex, ey, h) = (p.clone(), q.clone(), ex.clone(), ey.clone(), h.clone());
                lam_fv(0x6005, q.clone(), move |hq| {
                    let pos = lam_fv(0x6006, p.clone(), |hp| hp);
                    let neg = {
                        let (p, _q, ex, ey, h, hq) = (
                            p.clone(),
                            q.clone(),
                            ex.clone(),
                            ey.clone(),
                            h.clone(),
                            hq.clone(),
                        );
                        lam_fv(
                            0x6007,
                            arrow(p.clone(), Expr::const_str("False")),
                            move |hnp| {
                                let hol_np = kernel_not_to_hol_not(&p, hnp); // : ¬P (= ex)
                                                                             // hnq : ¬Q = Eq.mp (¬P) (¬Q) h hol_np
                                let hnq = eq_mp(&ex, &ey, h.clone(), hol_np);
                                let f = Expr::app(hnq, hq.clone());
                                Expr::app(f, p.clone())
                            },
                        )
                    };
                    em_case_split(&p, &p, pos, neg)
                })
            };
            propext_iff(p.clone(), q.clone(), fwd, bwd)
        })
    };
    // mpr : (P = Q) → (¬P = ¬Q).  Given h : P = Q, prove ¬P = ¬Q by propext:
    //   ¬P → ¬Q:  λ(hnp:¬P). λ(hq:Q). hnp (Eq.mpr h hq)     [transport Q→P]
    //   ¬Q → ¬P:  λ(hnq:¬Q). λ(hp:P). hnq (Eq.mp h hp)      [transport P→Q]
    let mpr = {
        let (p, q, ex, ey) = (p.clone(), q.clone(), ex.clone(), ey.clone());
        lam_fv(0x6008, r.clone(), move |h| {
            let fwd = {
                let (p, q, ex, h) = (p.clone(), q.clone(), ex.clone(), h.clone());
                lam_fv(0x6009, ex.clone(), move |hnp| {
                    lam_fv(0x600a, q.clone(), move |hq| {
                        let hp = eq_mpr(&p, &q, h.clone(), hq); // : P
                        Expr::app(hnp.clone(), hp)
                    })
                })
            };
            let bwd = {
                let (p, q, ey, h) = (p.clone(), q.clone(), ey.clone(), h.clone());
                lam_fv(0x600b, ey.clone(), move |hnq| {
                    lam_fv(0x600c, p.clone(), move |hp| {
                        let hq = eq_mp(&p, &q, h.clone(), hp); // : Q
                        Expr::app(hnq.clone(), hq)
                    })
                })
            };
            propext_iff(ex.clone(), ey.clone(), fwd, bwd)
        })
    };
    propext_iff(l.clone(), r.clone(), mp, mpr)
}

// ── bare-proposition (non-equational) simp leaves ───────────────────────────

/// The `simp_thms` conjuncts that are **not** an `@Eq Prop` equation: the
/// negated-self-eq laws `¬((¬P) = P)` / `¬(P = (¬P))` and the `∃`-reflexivity
/// witnesses `∃x. x = t` / `∃x. t = x`. Returns `None` for any other shape, so a
/// genuine equation / meta-universal falls through to the equational path.
fn prove_bare_prop_leaf(leaf: &Expr) -> Option<Expr> {
    // ¬((¬P) = P) / ¬(P = (¬P))  — the leaf is itself a `HOL.Not`.
    if let Some(inner) = hol_not_arg(leaf) {
        let (ea, x, y) = eq_three_parts(&inner)?;
        if ea != prop() {
            return None;
        }
        // `(¬P) = P`: x = ¬P, y = P.
        if let Some(p) = hol_not_arg(&x) {
            if y == p {
                return Some(neg_self_eq_proof(leaf, &p, &x, &y, true));
            }
        }
        // `P = (¬P)`: y = ¬P, x = P.
        if let Some(p) = hol_not_arg(&y) {
            if x == p {
                return Some(neg_self_eq_proof(leaf, &p, &x, &y, false));
            }
        }
        return None;
    }
    // ∃x. x = t / ∃x. t = x  — the leaf is an `ex_encoding`.
    prove_exists_refl(leaf)
}

/// `¬((¬P) = P)` (`not_on_left`) / `¬(P = (¬P))`. `inner = @Eq Prop x y` is the
/// negated equation, `p` the un-negated operand. The leaf is `HOL.Not inner`
/// (δ→ `inner → False_enc`), so the proof is `λ(h:inner). <False_enc>` built by a
/// `Classical.em` on `P`. Foundational (em + `Eq.{mp,mpr}`).
fn neg_self_eq_proof(_leaf: &Expr, p: &Expr, x: &Expr, y: &Expr, not_on_left: bool) -> Expr {
    // The hypothesis type is `inner = @Eq Prop x y` (= the `hol_not_arg` of the leaf).
    let inner = eq_prop(x.clone(), y.clone());
    lam_fv(0x6201, inner, move |h| {
        let (p, x, y, h) = (p.clone(), x.clone(), y.clone(), h.clone());
        let pos = {
            // hp : P.  Transport to ¬P, then apply to hp → False_enc.
            let (p, x, y, h) = (p.clone(), x.clone(), y.clone(), h.clone());
            lam_fv(0x6202, p.clone(), move |hp| {
                let hnp = if not_on_left {
                    eq_mpr(&x, &y, h.clone(), hp.clone()) // h:(¬P)=P, mpr: P→¬P
                } else {
                    eq_mp(&x, &y, h.clone(), hp.clone()) // h:P=(¬P), mp: P→¬P
                };
                Expr::app(hnp, hp) // ¬P applied to P : False_enc
            })
        };
        let neg = {
            // hnpk : P → False (kernel).  Coerce to ¬P, transport to P, apply → False.
            let (p, x, y, h) = (p.clone(), x.clone(), y.clone(), h.clone());
            lam_fv(
                0x6203,
                arrow(p.clone(), Expr::const_str("False")),
                move |hnpk| {
                    let hnp_hol = kernel_not_to_hol_not(&p, hnpk.clone()); // : ¬P
                    let hp = if not_on_left {
                        eq_mp(&x, &y, h.clone(), hnp_hol) // h:(¬P)=P, mp: ¬P→P
                    } else {
                        eq_mpr(&x, &y, h.clone(), hnp_hol) // h:P=(¬P), mpr: ¬P→P
                    };
                    false_elim_kernel(&false_enc(), Expr::app(hnpk, hp))
                },
            )
        };
        em_case_split(&p, &false_enc(), pos, neg)
    })
}

/// `∃x:α. x = t` / `∃x:α. t = x`. The leaf is `ex_encoding(α, λx. Eq α x t)` =
/// `Π(Q:Prop). (Π(x:α). (x = t) → Q) → Q`; the proof supplies the witness `t` and
/// `Eq.refl α t`. Returns `None` for any predicate that is not a bare `x = t` /
/// `t = x` equation (an `∃x. x = t ∧ P x` has a `conj`, not an `Eq`, so declines).
fn prove_exists_refl(leaf: &Expr) -> Option<Expr> {
    let ExprKind::Pi(_, qdom, lbody) = leaf.kind() else {
        return None;
    };
    if **qdom != prop() {
        return None;
    }
    let fq = FVarId::new(0x8601);
    let q = Expr::fvar(fq);
    let body = lbody.instantiate(&q);
    let (inner, q2) = as_arrow(&body)?;
    if q2 != q {
        return None;
    }
    let ExprKind::Pi(_, adom, ibody) = inner.kind() else {
        return None;
    };
    let alpha = (**adom).clone();
    let fx = FVarId::new(0x8602);
    let x = Expr::fvar(fx);
    let ib = ibody.instantiate(&x);
    let (pred, q3) = as_arrow(&ib)?;
    if q3 != q {
        return None;
    }
    // `pred` is `(λx. Eq α x t) x` (stored applied by `ex_encoding`); β-reduce.
    let (ea, e1, e2) = eq_three_parts(&beta1(&pred))?;
    if ea != alpha {
        return None;
    }
    let (t, _xside_left) = onepoint_witness(&e1, &e2, &x, fx)?;
    // proof : Π(Q:Prop). (Π(x:α). (x = t) → Q) → Q  =  λQ. λk. k t (Eq.refl α t)
    let proof = {
        let (alpha, t, inner) = (alpha.clone(), t.clone(), inner.clone());
        lam_fv(0x8603, prop(), move |cq| {
            // The `k` argument type is `inner` with the abstract `Q` replaced by `cq`.
            let kty = inner.clone().abstract_fvar(fq).instantiate(&cq);
            let (alpha, t) = (alpha.clone(), t.clone());
            lam_fv(0x8604, kty, move |k| {
                Expr::apps(k, [t.clone(), eq_refl_obj(&alpha, &t)])
            })
        })
    };
    Some(proof)
}

/// `(x = x) = True` at ANY object sort α (`simp_thms`'s `eq_self`): the leaf is
/// `@Eq Prop (@Eq α x x) HOL.True`. Foundational: `propext` of the trivial `Iff`.
/// Returns `None` unless `l` is a reflexive object equation and `r` is `True`.
fn prove_eq_self_true(l: &Expr, r: &Expr) -> Option<Expr> {
    let (ea, ex, ey) = eq_three_parts(l)?;
    if ex != ey || !is_true_def_const(r) {
        return None;
    }
    // mp : (x = x) → True  =  λ_. True.
    let mp = lam_fv(0x8701, l.clone(), |_h| true_pf());
    // mpr : True → (x = x)  =  λ_. Eq.refl α x.
    let mpr = {
        let refl = eq_refl_obj(&ea, &ex);
        lam_fv(0x8702, r.clone(), move |_h| refl.clone())
    };
    Some(propext_iff(l.clone(), r.clone(), mp, mpr))
}

// ── meta-universal (`⋀y. body`) peeling ─────────────────────────────────────

/// Count the leading `Π` binders of `e` (the embedded `Pure.all`/`⋀` prefix of a
/// per-conjunct simp leaf). Used only to mint collision-free peel fvar ids.
fn count_leading_pis(e: &Expr) -> u64 {
    let mut n = 0u64;
    let mut cur = e.clone();
    while let ExprKind::Pi(_, _, body) = cur.kind() {
        n += 1;
        cur = (**body).clone();
    }
    n
}

/// Peel a leading meta-universal `⋀y. body` (embedded `Π(y:σ). body`), prove the
/// inner leaf via [`prove_simp_leaf_wit`] (threading the witnesses), and re-bind
/// with `λ(y:σ)`. Fires only when `leaf` is a `Π`; a `Π` whose body is not a
/// recognized leaf declines (returns `None`). The peel fvar id is derived from the
/// residual `Π`-depth so nested `⋀P Q.` binders never collide.
fn prove_meta_universal(leaf: &Expr, witnesses: &[(Expr, Expr)]) -> Option<Expr> {
    let ExprKind::Pi(_, dom, body) = leaf.kind() else {
        return None;
    };
    let depth = count_leading_pis(leaf);
    let fv = FVarId::new(0xE100_0000 + depth);
    let inner = body.instantiate(&Expr::fvar(fv));
    let inner_pf = prove_simp_leaf_wit(&inner, witnesses)?;
    Some(Expr::lam(
        BinderInfo::Default,
        (**dom).clone(),
        inner_pf.abstract_fvar(fv),
    ))
}

/// `(¬(P = Q)) = (P = ¬Q)` (`not_iff`). Both directions are `Classical.em`
/// case-splits feeding `propext` / `Eq.{mp,mpr}`; foundational closure. `l = ¬(P=Q)`
/// (δ→ `(P=Q) → False_enc`), `r = (P = ¬Q)`.
fn not_iff_leaf(l: &Expr, r: &Expr, p: &Expr, q: &Expr) -> Expr {
    let not_q = mk_not(q);
    let p_eq_q = eq_prop(p.clone(), q.clone());
    // mp : ¬(P=Q) → (P=¬Q)
    let mp = {
        let (p, q, not_q) = (p.clone(), q.clone(), not_q.clone());
        lam_fv(0x6301, l.clone(), move |h| {
            // fwd : P → ¬Q  =  λhp. λhq. h (propext (Iff.intro (λ_.hq) (λ_.hp)))
            let fwd = {
                let (p, q, h) = (p.clone(), q.clone(), h.clone());
                lam_fv(0x6302, p.clone(), move |hp| {
                    let (p, q, h, hp) = (p.clone(), q.clone(), h.clone(), hp.clone());
                    lam_fv(0x6303, q.clone(), move |hq| {
                        let p2q = {
                            let hq = hq.clone();
                            lam_fv(0x6304, p.clone(), move |_x| hq.clone())
                        };
                        let q2p = {
                            let hp = hp.clone();
                            lam_fv(0x6305, q.clone(), move |_x| hp.clone())
                        };
                        let peq = propext_iff(p.clone(), q.clone(), p2q, q2p);
                        Expr::app(h.clone(), peq)
                    })
                })
            };
            // bwd : ¬Q → P  by em on P.
            let bwd = {
                let (p, q, not_q, h) = (p.clone(), q.clone(), not_q.clone(), h.clone());
                lam_fv(0x6306, not_q.clone(), move |hnq| {
                    let pos = lam_fv(0x6307, p.clone(), |hp| hp);
                    let neg = {
                        let (p, q, h, hnq) = (p.clone(), q.clone(), h.clone(), hnq.clone());
                        lam_fv(
                            0x6308,
                            arrow(p.clone(), Expr::const_str("False")),
                            move |hnp| {
                                let p2q = {
                                    let (q, hnp) = (q.clone(), hnp.clone());
                                    lam_fv(0x6309, p.clone(), move |hp2| {
                                        false_elim_kernel(&q, Expr::app(hnp.clone(), hp2))
                                    })
                                };
                                let q2p = {
                                    let (p, hnq) = (p.clone(), hnq.clone());
                                    lam_fv(0x630a, q.clone(), move |hq2| {
                                        false_elim_at(&p, Expr::app(hnq.clone(), hq2))
                                    })
                                };
                                let peq = propext_iff(p.clone(), q.clone(), p2q, q2p);
                                false_elim_at(&p, Expr::app(h.clone(), peq))
                            },
                        )
                    };
                    em_case_split(&p, &p, pos, neg)
                })
            };
            propext_iff(p.clone(), not_q.clone(), fwd, bwd)
        })
    };
    // mpr : (P=¬Q) → ¬(P=Q)  =  λh. λ(he:P=Q). <False_enc>
    let mpr = {
        let (p, q, not_q, p_eq_q) = (p.clone(), q.clone(), not_q.clone(), p_eq_q.clone());
        lam_fv(0x630b, r.clone(), move |h| {
            let (p, q, not_q, h) = (p.clone(), q.clone(), not_q.clone(), h.clone());
            lam_fv(0x630c, p_eq_q.clone(), move |he| {
                // em on Q.
                let pos = {
                    let (p, q, not_q, h, he) =
                        (p.clone(), q.clone(), not_q.clone(), h.clone(), he.clone());
                    lam_fv(0x630d, q.clone(), move |hq| {
                        let hp = eq_mpr(&p, &q, he.clone(), hq.clone()); // : P
                        let hnq = eq_mp(&p, &not_q, h.clone(), hp); // : ¬Q
                        Expr::app(hnq, hq) // : False_enc
                    })
                };
                let neg = {
                    let (p, q, not_q, h, he) =
                        (p.clone(), q.clone(), not_q.clone(), h.clone(), he.clone());
                    lam_fv(
                        0x630e,
                        arrow(q.clone(), Expr::const_str("False")),
                        move |hnq| {
                            // em on P.
                            let pos2 = {
                                let (p, q, he, hnq) =
                                    (p.clone(), q.clone(), he.clone(), hnq.clone());
                                lam_fv(0x630f, p.clone(), move |hp| {
                                    let hq = eq_mp(&p, &q, he.clone(), hp); // : Q
                                    false_elim_kernel(&false_enc(), Expr::app(hnq.clone(), hq))
                                })
                            };
                            let neg2 = {
                                let (p, not_q, h, hnq) =
                                    (p.clone(), not_q.clone(), h.clone(), hnq.clone());
                                lam_fv(
                                    0x6310,
                                    arrow(p.clone(), Expr::const_str("False")),
                                    move |hnp| {
                                        let hnq_hol = kernel_not_to_hol_not(&q, hnq.clone()); // : ¬Q
                                        let hp = eq_mpr(&p, &not_q, h.clone(), hnq_hol); // : P
                                        false_elim_kernel(&false_enc(), Expr::app(hnp.clone(), hp))
                                    },
                                )
                            };
                            em_case_split(&p, &false_enc(), pos2, neg2)
                        },
                    )
                };
                em_case_split(&q, &false_enc(), pos, neg)
            })
        })
    };
    propext_iff(l.clone(), r.clone(), mp, mpr)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{is_foundational_axiom, Declaration, Environment};

    /// A test environment: prelude + `Or` + the monomorphic HOL connective
    /// def-consts (`isabelle.def.HOL.True/False/Not/conj/disj`), exactly as the
    /// verifier registers them before replaying the closure.
    fn base_env() -> Environment {
        let mut env = Environment::with_prelude();
        let _ = env.init_or();
        for d in connective_definition_decls() {
            let _ = env.add_decl(d);
        }
        env
    }

    /// `add_decl` the theorem and assert (a) the kernel accepts the value against
    /// the type and (b) its transitive axiom closure is ⊆ FOUNDATIONAL_AXIOMS.
    fn add_check(env: &mut Environment, name: &str, ty: Expr, val: Expr) {
        env.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: Vec::new(),
            type_: ty,
            value: val,
        })
        .unwrap_or_else(|e| panic!("kernel rejected `{name}`: {e:?}"));
        let deps = env
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_else(|| panic!("no axiom_deps for `{name}`"));
        let bad: Vec<String> = deps
            .iter()
            .filter(|n| !is_foundational_axiom(n))
            .map(ToString::to_string)
            .collect();
        assert!(bad.is_empty(), "`{name}` non-foundational axioms: {bad:?}");
    }

    /// Close `body` (which may reference the two Prop atoms `p`, `q`) under
    /// `⋀P Q. …` (`is_pi`) or `λP Q. …` (value).
    fn close2(fp: FVarId, fq: FVarId, body: Expr, is_pi: bool) -> Expr {
        let mk = |dom: Expr, b: Expr| {
            if is_pi {
                Expr::pi(BinderInfo::Default, dom, b)
            } else {
                Expr::lam(BinderInfo::Default, dom, b)
            }
        };
        let inner = mk(prop(), body.abstract_fvar(fq));
        mk(prop(), inner.abstract_fvar(fp))
    }

    /// Build the leaf from two fresh Prop atoms, prove it, and kernel-check the
    /// `⋀P Q.`-closed theorem with foundational closure.
    fn check_leaf(name: &str, leaf_of: impl Fn(&Expr, &Expr) -> Expr) {
        let mut env = base_env();
        let (fp, fq) = (FVarId::new(0xAA01), FVarId::new(0xAA02));
        let (p, q) = (Expr::fvar(fp), Expr::fvar(fq));
        let leaf = leaf_of(&p, &q);
        let proof = prove_simp_leaf(&leaf)
            .unwrap_or_else(|| panic!("`{name}`: prove_simp_leaf returned None"));
        let ty = close2(fp, fq, leaf, true);
        let val = close2(fp, fq, proof, false);
        add_check(&mut env, name, ty, val);
    }

    fn eqp(a: Expr, b: Expr) -> Expr {
        eq_prop(a, b)
    }

    // ── conjunction laws ──────────────────────────────────────────────────
    #[test]
    fn leaf_conj_true_right() {
        check_leaf("(P∧True)=P", |p, _q| {
            eqp(mk_conj(p, &c_true()), p.clone())
        });
    }
    #[test]
    fn leaf_conj_true_left() {
        check_leaf("(True∧P)=P", |p, _q| {
            eqp(mk_conj(&c_true(), p), p.clone())
        });
    }
    #[test]
    fn leaf_conj_false_right() {
        check_leaf("(P∧False)=False", |p, _q| {
            eqp(mk_conj(p, &c_false()), c_false())
        });
    }
    #[test]
    fn leaf_conj_false_left() {
        check_leaf("(False∧P)=False", |p, _q| {
            eqp(mk_conj(&c_false(), p), c_false())
        });
    }
    #[test]
    fn leaf_conj_idem() {
        check_leaf("(P∧P)=P", |p, _q| eqp(mk_conj(p, p), p.clone()));
    }

    // ── disjunction laws ──────────────────────────────────────────────────
    #[test]
    fn leaf_disj_true_right() {
        check_leaf("(P∨True)=True", |p, _q| {
            eqp(mk_disj(p, &c_true()), c_true())
        });
    }
    #[test]
    fn leaf_disj_true_left() {
        check_leaf("(True∨P)=True", |p, _q| {
            eqp(mk_disj(&c_true(), p), c_true())
        });
    }
    #[test]
    fn leaf_disj_false_right() {
        check_leaf("(P∨False)=P", |p, _q| {
            eqp(mk_disj(p, &c_false()), p.clone())
        });
    }
    #[test]
    fn leaf_disj_false_left() {
        check_leaf("(False∨P)=P", |p, _q| {
            eqp(mk_disj(&c_false(), p), p.clone())
        });
    }
    #[test]
    fn leaf_disj_idem() {
        check_leaf("(P∨P)=P", |p, _q| eqp(mk_disj(p, p), p.clone()));
    }

    // ── negation laws ─────────────────────────────────────────────────────
    #[test]
    fn leaf_double_neg() {
        check_leaf("¬¬P=P", |p, _q| eqp(mk_not(&mk_not(p)), p.clone()));
    }
    #[test]
    fn leaf_not_true() {
        check_leaf("¬True=False", |_p, _q| eqp(mk_not(&c_true()), c_false()));
    }
    #[test]
    fn leaf_not_false() {
        check_leaf("¬False=True", |_p, _q| eqp(mk_not(&c_false()), c_true()));
    }

    // ── implication laws ──────────────────────────────────────────────────
    #[test]
    fn leaf_imp_true_left() {
        check_leaf("(True→P)=P", |p, _q| {
            eqp(arrow(c_true(), p.clone()), p.clone())
        });
    }
    #[test]
    fn leaf_imp_true_right() {
        check_leaf("(P→True)=True", |p, _q| {
            eqp(arrow(p.clone(), c_true()), c_true())
        });
    }
    #[test]
    fn leaf_imp_false_left() {
        check_leaf("(False→P)=True", |p, _q| {
            eqp(arrow(c_false(), p.clone()), c_true())
        });
    }
    #[test]
    fn leaf_imp_self() {
        check_leaf("(P→P)=True", |p, _q| {
            eqp(arrow(p.clone(), p.clone()), c_true())
        });
    }

    // ── equality-rewrite laws ─────────────────────────────────────────────
    #[test]
    fn leaf_eq_true_right() {
        check_leaf("(P=True)=P", |p, _q| {
            eqp(eqp(p.clone(), c_true()), p.clone())
        });
    }
    #[test]
    fn leaf_eq_true_left() {
        check_leaf("(True=P)=P", |p, _q| {
            eqp(eqp(c_true(), p.clone()), p.clone())
        });
    }
    #[test]
    fn leaf_eq_false_right() {
        check_leaf("(P=False)=¬P", |p, _q| {
            eqp(eqp(p.clone(), c_false()), mk_not(p))
        });
    }
    #[test]
    fn leaf_eq_false_left() {
        check_leaf("(False=P)=¬P", |p, _q| {
            eqp(eqp(c_false(), p.clone()), mk_not(p))
        });
    }
    #[test]
    fn leaf_neg_cong() {
        check_leaf("((¬P)=(¬Q))=(P=Q)", |p, q| {
            eqp(eqp(mk_not(p), mk_not(q)), eqp(p.clone(), q.clone()))
        });
    }

    // ── whole-bundle assembly ─────────────────────────────────────────────
    #[test]
    fn bundle_three_leaves_under_two_ofclass() {
        // True → True → And ((P∧True)=P) (And (¬¬Q=Q) ((P∨False)=P))
        let mut env = base_env();
        let (fp, fq) = (FVarId::new(0xBB01), FVarId::new(0xBB02));
        let (p, q) = (Expr::fvar(fp), Expr::fvar(fq));
        let l1 = eqp(mk_conj(&p, &c_true()), p.clone());
        let l2 = eqp(mk_not(&mk_not(&q)), q.clone());
        let l3 = eqp(mk_disj(&p, &c_false()), p.clone());
        let and_ = |a: Expr, b: Expr| Expr::apps(Expr::const_str("And"), [a, b]);
        let body = and_(l1.clone(), and_(l2.clone(), l3.clone()));
        let stmt = arrow(
            Expr::const_str("True"),
            arrow(Expr::const_str("True"), body),
        );
        let proof = prove_conjunction_bundle(&stmt).expect("bundle recognized");
        let ty = close2(fp, fq, stmt, true);
        let val = close2(fp, fq, proof, false);
        add_check(&mut env, "simp_bundle_demo", ty, val);
    }

    // ── boundary / negative cases (soundness floor) ───────────────────────
    #[test]
    fn unrecognized_leaf_returns_none() {
        // (P ∧ Q) = Q is NOT a simp law we cover — must decline, not fabricate.
        let (p, q) = (
            Expr::fvar(FVarId::new(0xCC01)),
            Expr::fvar(FVarId::new(0xCC02)),
        );
        let leaf = eqp(mk_conj(&p, &q), q.clone());
        assert!(
            prove_simp_leaf(&leaf).is_none(),
            "must decline an unrecognized conjunction rewrite"
        );
    }
    #[test]
    fn single_leaf_is_not_a_bundle() {
        // A lone equation under no `And` nesting is not a bundle (handled by the
        // per-law arms), so the bundle prover declines.
        let p = Expr::fvar(FVarId::new(0xCC03));
        let stmt = eqp(mk_conj(&p, &c_true()), p.clone());
        assert!(
            prove_conjunction_bundle(&stmt).is_none(),
            "single leaf is not a conjunction bundle"
        );
    }
    #[test]
    fn vacuous_forall_leaf_is_not_covered() {
        // `(∀x. P) = P` requires HOL type-nonemptiness (false over an empty sort);
        // the erased `OFCLASS → True` premise carries no witness, so we MUST decline
        // rather than mint an unsound proof. Here `∀x:Prop. P` embeds as a
        // dependent `Pi` whose body ignores the bound var.
        let p = Expr::fvar(FVarId::new(0xCC04));
        let forall_p = Expr::pi(BinderInfo::Default, prop(), p.clone());
        let leaf = eqp(forall_p, p.clone());
        assert!(
            prove_simp_leaf(&leaf).is_none(),
            "vacuous-quantifier leaf must be declined (nonemptiness gap)"
        );
    }

    // ── NonemptyErase mode: witness-carrying quantifier leaves ─────────────

    /// `@Nonempty.{1} α`.
    fn nonempty_ty(alpha: &Expr) -> Expr {
        Expr::apps(
            Expr::const_str_levels("Nonempty", vec![obj_level()]),
            [alpha.clone()],
        )
    }

    /// Build the bundle `Nonempty α → And L1 L2`, prove it via the bundle prover, and
    /// kernel-check it closed under the given binders (outermost-first) with a
    /// foundational axiom closure. Every quantifier leaf's proof references the peeled
    /// `Nonempty α` premise (through `Classical.choice`), so this exercises the whole
    /// witness plumbing end-to-end against clean's kernel.
    fn check_wit_bundle(name: &str, binders: &[(Expr, FVarId)], l1: Expr, l2: Expr, alpha: &Expr) {
        let mut env = base_env();
        let and_ = |x: Expr, y: Expr| Expr::apps(Expr::const_str("And"), [x, y]);
        let stmt = arrow(nonempty_ty(alpha), and_(l1, l2));
        let proof = prove_conjunction_bundle(&stmt)
            .unwrap_or_else(|| panic!("`{name}`: bundle not recognized"));
        let close = |mut b: Expr, is_pi: bool| {
            for (dom, fv) in binders.iter().rev() {
                b = if is_pi {
                    Expr::pi(BinderInfo::Default, dom.clone(), b.abstract_fvar(*fv))
                } else {
                    Expr::lam(BinderInfo::Default, dom.clone(), b.abstract_fvar(*fv))
                };
            }
            b
        };
        let ty = close(stmt.clone(), true);
        let val = close(proof, false);
        add_check(&mut env, name, ty, val);
    }

    #[test]
    fn leaf_vacuous_forall() {
        // (∀x:α. P) = P  under  Nonempty α.
        let (fa, fp, fq) = (
            FVarId::new(0xDD01),
            FVarId::new(0xDD02),
            FVarId::new(0xDD03),
        );
        let (a, p, q) = (Expr::fvar(fa), Expr::fvar(fp), Expr::fvar(fq));
        let l1 = eqp(
            Expr::pi(BinderInfo::Default, a.clone(), p.clone()),
            p.clone(),
        );
        let l2 = eqp(mk_conj(&q, &c_true()), q.clone());
        check_wit_bundle(
            "(∀x:α.P)=P",
            &[(Expr::type_(), fa), (prop(), fp), (prop(), fq)],
            l1,
            l2,
            &a,
        );
    }

    #[test]
    fn leaf_vacuous_exists() {
        // (∃x:α. P) = P  under  Nonempty α.
        let (fa, fp, fq) = (
            FVarId::new(0xDE01),
            FVarId::new(0xDE02),
            FVarId::new(0xDE03),
        );
        let (a, p, q) = (Expr::fvar(fa), Expr::fvar(fp), Expr::fvar(fq));
        let pred = Expr::lam(BinderInfo::Default, a.clone(), p.clone());
        let l1 = eqp(ex_encoding(&a, &pred), p.clone());
        let l2 = eqp(mk_conj(&q, &c_true()), q.clone());
        check_wit_bundle(
            "(∃x:α.P)=P",
            &[(Expr::type_(), fa), (prop(), fp), (prop(), fq)],
            l1,
            l2,
            &a,
        );
    }

    #[test]
    fn leaf_conj_miniscope_right_const() {
        // (∀x. P x ∧ Q) = ((∀x. P x) ∧ Q)  under  Nonempty α.
        let (fa, fpp, fq) = (
            FVarId::new(0xDF01),
            FVarId::new(0xDF02),
            FVarId::new(0xDF03),
        );
        let (a, pp, q) = (Expr::fvar(fa), Expr::fvar(fpp), Expr::fvar(fq));
        let fx = FVarId::new(0xDF0A);
        let x = Expr::fvar(fx);
        let px = Expr::app(pp.clone(), x.clone());
        let all_conj = Expr::pi(
            BinderInfo::Default,
            a.clone(),
            mk_conj(&px, &q).abstract_fvar(fx),
        );
        let all_px = Expr::pi(BinderInfo::Default, a.clone(), px.abstract_fvar(fx));
        let l1 = eqp(all_conj, mk_conj(&all_px, &q));
        let l2 = eqp(mk_conj(&q, &c_true()), q.clone());
        check_wit_bundle(
            "(∀x.Px∧Q)=((∀x.Px)∧Q)",
            &[
                (Expr::type_(), fa),
                (Expr::arrow(a.clone(), prop()), fpp),
                (prop(), fq),
            ],
            l1,
            l2,
            &a,
        );
    }

    #[test]
    fn leaf_conj_miniscope_left_const() {
        // (∀x. P ∧ Q x) = (P ∧ (∀x. Q x))  under  Nonempty α.
        let (fa, fp, fqq) = (
            FVarId::new(0xE001),
            FVarId::new(0xE002),
            FVarId::new(0xE003),
        );
        let (a, p, qq) = (Expr::fvar(fa), Expr::fvar(fp), Expr::fvar(fqq));
        let fx = FVarId::new(0xE00A);
        let x = Expr::fvar(fx);
        let qx = Expr::app(qq.clone(), x.clone());
        let all_conj = Expr::pi(
            BinderInfo::Default,
            a.clone(),
            mk_conj(&p, &qx).abstract_fvar(fx),
        );
        let all_qx = Expr::pi(BinderInfo::Default, a.clone(), qx.abstract_fvar(fx));
        let l1 = eqp(all_conj, mk_conj(&p, &all_qx));
        let l2 = eqp(mk_conj(&p, &c_true()), p.clone());
        check_wit_bundle(
            "(∀x.P∧Qx)=(P∧(∀x.Qx))",
            &[
                (Expr::type_(), fa),
                (prop(), fp),
                (Expr::arrow(a.clone(), prop()), fqq),
            ],
            l1,
            l2,
            &a,
        );
    }

    #[test]
    fn vacuous_forall_still_declined_without_witness() {
        // Soundness floor: with an EMPTY witness set (the historical `True`-erased
        // mode) the vacuous-∀ leaf MUST still decline — it is false over an empty sort.
        let (a, p) = (
            Expr::fvar(FVarId::new(0xE101)),
            Expr::fvar(FVarId::new(0xE102)),
        );
        let leaf = eqp(Expr::pi(BinderInfo::Default, a, p.clone()), p);
        assert!(
            prove_simp_leaf_wit(&leaf, &[]).is_none(),
            "no witness ⇒ vacuous-∀ must decline"
        );
    }

    #[test]
    fn nonempty_erase_mode_embeds_ofclass_as_nonempty() {
        use super::super::super::super::isabelle_pure::{IsaTerm, IsaType};
        // Build `OFCLASS('a, type)` = `HOL.type_class (Pure.type : itself('a))`.
        let alpha = IsaType::TFree { n: "'a".into() };
        let itself = IsaType::Type {
            n: "itself".into(),
            a: vec![alpha.clone()],
        };
        let ofclass = IsaTerm::App {
            f: Box::new(IsaTerm::Const {
                n: "HOL.type_class".into(),
                t: IsaType::Type {
                    n: "fun".into(),
                    a: vec![],
                },
            }),
            a: Box::new(IsaTerm::Const {
                n: "Pure.type".into(),
                t: itself,
            }),
        };
        // NonemptyErase Ctx: nonempty_erase on, class_membership off.
        let mut ctx = Ctx {
            nonempty_erase: true,
            ..Ctx::default()
        };
        let e = ctx
            .embed_class_membership(&ofclass)
            .expect("embed OFCLASS in NonemptyErase mode");
        // Head must be the `Nonempty` constant applied to the object type.
        let ExprKind::App(f, _) = e.kind() else {
            panic!("expected `Nonempty α` application, got {e:?}");
        };
        assert!(
            matches!(f.kind(), ExprKind::Const(n, _) if *n == Name::from_string("Nonempty")),
            "OFCLASS must embed to `Nonempty α` under NonemptyErase, got {e:?}"
        );
    }

    #[test]
    fn erase_mode_embeds_ofclass_as_true() {
        use super::super::super::super::isabelle_pure::{IsaTerm, IsaType};
        // The historical `Erase` mode (both flags off) must stay byte-identical: `True`.
        let ofclass = IsaTerm::App {
            f: Box::new(IsaTerm::Const {
                n: "HOL.type_class".into(),
                t: IsaType::Type {
                    n: "fun".into(),
                    a: vec![],
                },
            }),
            a: Box::new(IsaTerm::Const {
                n: "Pure.type".into(),
                t: IsaType::Type {
                    n: "itself".into(),
                    a: vec![IsaType::TFree { n: "'a".into() }],
                },
            }),
        };
        let mut ctx = Ctx::default();
        let e = ctx
            .embed_class_membership(&ofclass)
            .expect("embed OFCLASS in Erase mode");
        assert_eq!(e, Expr::const_str("True"), "Erase must stay `True`");
    }

    // ── witness-free quantifier leaves (one-point rules; ∨/⟶ miniscoping) ──
    //
    // These need NO nonemptiness witness, so they are proved through the
    // propositional `prove_simp_leaf` entry (`witnesses = []`) — closed under
    // `⋀(α:Type) …` and kernel-checked with a foundational axiom closure.

    fn pred_ty(a: &Expr) -> Expr {
        Expr::arrow(a.clone(), prop())
    }

    /// Prove `leaf` via witness-free `prove_simp_leaf`, close it under `binders`
    /// (outermost-first), and kernel-check the theorem with foundational closure.
    fn check_witfree_leaf(name: &str, binders: &[(Expr, FVarId)], leaf: Expr) {
        let mut env = base_env();
        let proof = prove_simp_leaf(&leaf)
            .unwrap_or_else(|| panic!("`{name}`: prove_simp_leaf returned None"));
        let close = |mut b: Expr, is_pi: bool| {
            for (dom, fv) in binders.iter().rev() {
                b = if is_pi {
                    Expr::pi(BinderInfo::Default, dom.clone(), b.abstract_fvar(*fv))
                } else {
                    Expr::lam(BinderInfo::Default, dom.clone(), b.abstract_fvar(*fv))
                };
            }
            b
        };
        add_check(
            &mut env,
            name,
            close(leaf.clone(), true),
            close(proof, false),
        );
    }

    /// `∀(x:α). body[x]` with `body` built from the bound `x` (a fresh fvar `fx`).
    fn all_x(a: &Expr, fx: FVarId, body: Expr) -> Expr {
        Expr::pi(BinderInfo::Default, a.clone(), body.abstract_fvar(fx))
    }

    #[test]
    fn leaf_forall_onepoint_x_eq_t() {
        // ⋀(α:Type)(P:α→Prop)(t:α). (∀x. x = t ⟶ P x) = P t
        let (fa, fp, ft, fx) = (
            FVarId::new(0xF001),
            FVarId::new(0xF002),
            FVarId::new(0xF003),
            FVarId::new(0xF00A),
        );
        let (a, pp, t, x) = (
            Expr::fvar(fa),
            Expr::fvar(fp),
            Expr::fvar(ft),
            Expr::fvar(fx),
        );
        let px = Expr::app(pp.clone(), x.clone());
        let l = all_x(&a, fx, arrow(eq_obj(&a, &x, &t), px));
        let leaf = eqp(l, Expr::app(pp.clone(), t.clone()));
        check_witfree_leaf(
            "(∀x. x=t⟶P x)=P t",
            &[(Expr::type_(), fa), (pred_ty(&a), fp), (a.clone(), ft)],
            leaf,
        );
    }

    #[test]
    fn leaf_forall_onepoint_t_eq_x() {
        // ⋀(α:Type)(P:α→Prop)(t:α). (∀x. t = x ⟶ P x) = P t  (symmetric twin)
        let (fa, fp, ft, fx) = (
            FVarId::new(0xF011),
            FVarId::new(0xF012),
            FVarId::new(0xF013),
            FVarId::new(0xF01A),
        );
        let (a, pp, t, x) = (
            Expr::fvar(fa),
            Expr::fvar(fp),
            Expr::fvar(ft),
            Expr::fvar(fx),
        );
        let px = Expr::app(pp.clone(), x.clone());
        let l = all_x(&a, fx, arrow(eq_obj(&a, &t, &x), px));
        let leaf = eqp(l, Expr::app(pp.clone(), t.clone()));
        check_witfree_leaf(
            "(∀x. t=x⟶P x)=P t",
            &[(Expr::type_(), fa), (pred_ty(&a), fp), (a.clone(), ft)],
            leaf,
        );
    }

    #[test]
    fn leaf_exists_onepoint_x_eq_t() {
        // ⋀(α:Type)(P:α→Prop)(t:α). (∃x. x = t ∧ P x) = P t
        let (fa, fp, ft, fx) = (
            FVarId::new(0xF021),
            FVarId::new(0xF022),
            FVarId::new(0xF023),
            FVarId::new(0xF02A),
        );
        let (a, pp, t, x) = (
            Expr::fvar(fa),
            Expr::fvar(fp),
            Expr::fvar(ft),
            Expr::fvar(fx),
        );
        let px = Expr::app(pp.clone(), x.clone());
        let pred = Expr::lam(
            BinderInfo::Default,
            a.clone(),
            mk_conj(&eq_obj(&a, &x, &t), &px).abstract_fvar(fx),
        );
        let leaf = eqp(ex_encoding(&a, &pred), Expr::app(pp.clone(), t.clone()));
        check_witfree_leaf(
            "(∃x. x=t∧P x)=P t",
            &[(Expr::type_(), fa), (pred_ty(&a), fp), (a.clone(), ft)],
            leaf,
        );
    }

    #[test]
    fn leaf_exists_onepoint_t_eq_x() {
        // ⋀(α:Type)(P:α→Prop)(t:α). (∃x. t = x ∧ P x) = P t  (symmetric twin)
        let (fa, fp, ft, fx) = (
            FVarId::new(0xF031),
            FVarId::new(0xF032),
            FVarId::new(0xF033),
            FVarId::new(0xF03A),
        );
        let (a, pp, t, x) = (
            Expr::fvar(fa),
            Expr::fvar(fp),
            Expr::fvar(ft),
            Expr::fvar(fx),
        );
        let px = Expr::app(pp.clone(), x.clone());
        let pred = Expr::lam(
            BinderInfo::Default,
            a.clone(),
            mk_conj(&eq_obj(&a, &t, &x), &px).abstract_fvar(fx),
        );
        let leaf = eqp(ex_encoding(&a, &pred), Expr::app(pp.clone(), t.clone()));
        check_witfree_leaf(
            "(∃x. t=x∧P x)=P t",
            &[(Expr::type_(), fa), (pred_ty(&a), fp), (a.clone(), ft)],
            leaf,
        );
    }

    #[test]
    fn leaf_disj_miniscope_right_const() {
        // ⋀(α:Type)(P:α→Prop)(Q:Prop). (∀x. P x ∨ Q) = ((∀x. P x) ∨ Q)
        let (fa, fp, fq, fx) = (
            FVarId::new(0xF041),
            FVarId::new(0xF042),
            FVarId::new(0xF043),
            FVarId::new(0xF04A),
        );
        let (a, pp, q, x) = (
            Expr::fvar(fa),
            Expr::fvar(fp),
            Expr::fvar(fq),
            Expr::fvar(fx),
        );
        let px = Expr::app(pp.clone(), x.clone());
        let all_conj = all_x(&a, fx, mk_disj(&px, &q));
        let all_px = all_x(&a, fx, px.clone());
        let leaf = eqp(all_conj, mk_disj(&all_px, &q));
        check_witfree_leaf(
            "(∀x. P x∨Q)=((∀x.P x)∨Q)",
            &[(Expr::type_(), fa), (pred_ty(&a), fp), (prop(), fq)],
            leaf,
        );
    }

    #[test]
    fn leaf_disj_miniscope_left_const() {
        // ⋀(α:Type)(P:Prop)(Q:α→Prop). (∀x. P ∨ Q x) = (P ∨ (∀x. Q x))
        let (fa, fp, fq, fx) = (
            FVarId::new(0xF051),
            FVarId::new(0xF052),
            FVarId::new(0xF053),
            FVarId::new(0xF05A),
        );
        let (a, p, qq, x) = (
            Expr::fvar(fa),
            Expr::fvar(fp),
            Expr::fvar(fq),
            Expr::fvar(fx),
        );
        let qx = Expr::app(qq.clone(), x.clone());
        let all_conj = all_x(&a, fx, mk_disj(&p, &qx));
        let all_qx = all_x(&a, fx, qx.clone());
        let leaf = eqp(all_conj, mk_disj(&p, &all_qx));
        check_witfree_leaf(
            "(∀x. P∨Q x)=(P∨(∀x.Q x))",
            &[(Expr::type_(), fa), (prop(), fp), (pred_ty(&a), fq)],
            leaf,
        );
    }

    #[test]
    fn leaf_imp_miniscope_ante_dep() {
        // ⋀(α:Type)(P:α→Prop)(Q:Prop). (∀x. P x ⟶ Q) = ((∃x. P x) ⟶ Q)
        let (fa, fp, fq, fx) = (
            FVarId::new(0xF061),
            FVarId::new(0xF062),
            FVarId::new(0xF063),
            FVarId::new(0xF06A),
        );
        let (a, pp, q, x) = (
            Expr::fvar(fa),
            Expr::fvar(fp),
            Expr::fvar(fq),
            Expr::fvar(fx),
        );
        let px = Expr::app(pp.clone(), x.clone());
        let all_conj = all_x(&a, fx, arrow(px.clone(), q.clone()));
        let pred = Expr::lam(BinderInfo::Default, a.clone(), px.abstract_fvar(fx));
        let ex_lhs = ex_encoding(&a, &pred);
        let leaf = eqp(all_conj, arrow(ex_lhs, q.clone()));
        check_witfree_leaf(
            "(∀x. P x⟶Q)=((∃x.P x)⟶Q)",
            &[(Expr::type_(), fa), (pred_ty(&a), fp), (prop(), fq)],
            leaf,
        );
    }

    #[test]
    fn leaf_imp_miniscope_cons_dep() {
        // ⋀(α:Type)(P:Prop)(Q:α→Prop). (∀x. P ⟶ Q x) = (P ⟶ (∀x. Q x))
        let (fa, fp, fq, fx) = (
            FVarId::new(0xF071),
            FVarId::new(0xF072),
            FVarId::new(0xF073),
            FVarId::new(0xF07A),
        );
        let (a, p, qq, x) = (
            Expr::fvar(fa),
            Expr::fvar(fp),
            Expr::fvar(fq),
            Expr::fvar(fx),
        );
        let qx = Expr::app(qq.clone(), x.clone());
        let all_conj = all_x(&a, fx, arrow(p.clone(), qx.clone()));
        let all_qx = all_x(&a, fx, qx.clone());
        let leaf = eqp(all_conj, arrow(p.clone(), all_qx));
        check_witfree_leaf(
            "(∀x. P⟶Q x)=(P⟶(∀x.Q x))",
            &[(Expr::type_(), fa), (prop(), fp), (pred_ty(&a), fq)],
            leaf,
        );
    }

    // ── whole-bundle preflight: the two headline inventories, end-to-end ────

    /// Build a right-associated `And`-tree of `leaves` under the premises `prems`,
    /// prove it through [`prove_conjunction_bundle`], and kernel-check it closed
    /// under `binders` (outermost-first) with a foundational axiom closure. THIS is
    /// the fixture-scale pre-flight for the corpus bundle flip.
    fn check_bundle(name: &str, binders: &[(Expr, FVarId)], prems: &[Expr], leaves: &[Expr]) {
        let mut env = base_env();
        assert!(leaves.len() >= 2, "a bundle needs ≥2 leaves");
        let and_ = |x: Expr, y: Expr| Expr::apps(Expr::const_str("And"), [x, y]);
        let mut body = leaves[leaves.len() - 1].clone();
        for l in leaves[..leaves.len() - 1].iter().rev() {
            body = and_(l.clone(), body);
        }
        for p in prems.iter().rev() {
            body = arrow(p.clone(), body);
        }
        let stmt = body;
        let proof = prove_conjunction_bundle(&stmt)
            .unwrap_or_else(|| panic!("`{name}`: bundle not recognized"));
        let close = |mut b: Expr, is_pi: bool| {
            for (dom, fv) in binders.iter().rev() {
                b = if is_pi {
                    Expr::pi(BinderInfo::Default, dom.clone(), b.abstract_fvar(*fv))
                } else {
                    Expr::lam(BinderInfo::Default, dom.clone(), b.abstract_fvar(*fv))
                };
            }
            b
        };
        add_check(
            &mut env,
            name,
            close(stmt.clone(), true),
            close(proof, false),
        );
    }

    #[test]
    fn bundle_all_simps_six_conjuncts() {
        // The exact `all_simps` inventory (HOL.thy): the ∧-miniscoping pair (needs
        // the `Nonempty α` witness) + the ∨/⟶ miniscoping quartet (witness-free),
        // assembled end-to-end under one `Nonempty α` premise.
        let (fa, fpd, fqc, fpc, fqd, fx) = (
            FVarId::new(0xA001),
            FVarId::new(0xA002),
            FVarId::new(0xA003),
            FVarId::new(0xA004),
            FVarId::new(0xA005),
            FVarId::new(0xA00A),
        );
        let (a, pd, qc, pc, qd, x) = (
            Expr::fvar(fa),
            Expr::fvar(fpd), // Pd : α→Prop (dependent)
            Expr::fvar(fqc), // Qc : Prop (const)
            Expr::fvar(fpc), // Pc : Prop (const)
            Expr::fvar(fqd), // Qd : α→Prop (dependent)
            Expr::fvar(fx),
        );
        let pdx = Expr::app(pd.clone(), x.clone());
        let qdx = Expr::app(qd.clone(), x.clone());
        let all_pdx = all_x(&a, fx, pdx.clone());
        let all_qdx = all_x(&a, fx, qdx.clone());
        let pred_pd = Expr::lam(
            BinderInfo::Default,
            a.clone(),
            pdx.clone().abstract_fvar(fx),
        );
        // 1: (∀x. Pd x ∧ Qc) = ((∀x. Pd x) ∧ Qc)
        let c1 = eqp(all_x(&a, fx, mk_conj(&pdx, &qc)), mk_conj(&all_pdx, &qc));
        // 2: (∀x. Pc ∧ Qd x) = (Pc ∧ (∀x. Qd x))
        let c2 = eqp(all_x(&a, fx, mk_conj(&pc, &qdx)), mk_conj(&pc, &all_qdx));
        // 3: (∀x. Pd x ∨ Qc) = ((∀x. Pd x) ∨ Qc)
        let c3 = eqp(all_x(&a, fx, mk_disj(&pdx, &qc)), mk_disj(&all_pdx, &qc));
        // 4: (∀x. Pc ∨ Qd x) = (Pc ∨ (∀x. Qd x))
        let c4 = eqp(all_x(&a, fx, mk_disj(&pc, &qdx)), mk_disj(&pc, &all_qdx));
        // 5: (∀x. Pd x ⟶ Qc) = ((∃x. Pd x) ⟶ Qc)
        let c5 = eqp(
            all_x(&a, fx, arrow(pdx.clone(), qc.clone())),
            arrow(ex_encoding(&a, &pred_pd), qc.clone()),
        );
        // 6: (∀x. Pc ⟶ Qd x) = (Pc ⟶ (∀x. Qd x))
        let c6 = eqp(
            all_x(&a, fx, arrow(pc.clone(), qdx.clone())),
            arrow(pc.clone(), all_qdx),
        );
        check_bundle(
            "all_simps",
            &[
                (Expr::type_(), fa),
                (pred_ty(&a), fpd),
                (prop(), fqc),
                (prop(), fpc),
                (pred_ty(&a), fqd),
            ],
            &[nonempty_ty(&a)],
            &[c1, c2, c3, c4, c5, c6],
        );
    }

    #[test]
    fn bundle_simp_thms_full_inventory() {
        // A faithful `simp_thms`-scale reconstruction: the 22 propositional laws +
        // the two vacuous-quantifier conjuncts (witnessed) + the two one-point
        // conjuncts (witness-free), assembled end-to-end under one `Nonempty α`
        // premise. Proving THIS through the bundle prover is the corpus pre-flight.
        let (fa, fp, fq, fpp, ft, fx) = (
            FVarId::new(0xB001),
            FVarId::new(0xB002),
            FVarId::new(0xB003),
            FVarId::new(0xB004),
            FVarId::new(0xB005),
            FVarId::new(0xB00A),
        );
        let (a, p, q, pp, t, x) = (
            Expr::fvar(fa),
            Expr::fvar(fp),  // P : Prop
            Expr::fvar(fq),  // Q : Prop
            Expr::fvar(fpp), // Pp : α→Prop
            Expr::fvar(ft),  // t : α
            Expr::fvar(fx),
        );
        // 22 propositional laws (P, Q : Prop), then the vacuous-∀ law;
        // vacuous ∃ (witnessed) and one-point ∀ / ∃ (witness-free) follow.
        let mut leaves: Vec<Expr> = vec![
            eqp(mk_conj(&p, &c_true()), p.clone()),
            eqp(mk_conj(&c_true(), &p), p.clone()),
            eqp(mk_conj(&p, &c_false()), c_false()),
            eqp(mk_conj(&c_false(), &p), c_false()),
            eqp(mk_conj(&p, &p), p.clone()),
            eqp(mk_disj(&p, &c_true()), c_true()),
            eqp(mk_disj(&c_true(), &p), c_true()),
            eqp(mk_disj(&p, &c_false()), p.clone()),
            eqp(mk_disj(&c_false(), &p), p.clone()),
            eqp(mk_disj(&p, &p), p.clone()),
            eqp(mk_not(&mk_not(&p)), p.clone()),
            eqp(mk_not(&c_true()), c_false()),
            eqp(mk_not(&c_false()), c_true()),
            eqp(arrow(c_true(), p.clone()), p.clone()),
            eqp(arrow(p.clone(), c_true()), c_true()),
            eqp(arrow(c_false(), p.clone()), c_true()),
            eqp(arrow(p.clone(), p.clone()), c_true()),
            eqp(eqp(p.clone(), c_true()), p.clone()),
            eqp(eqp(c_true(), p.clone()), p.clone()),
            eqp(eqp(p.clone(), c_false()), mk_not(&p)),
            eqp(eqp(c_false(), p.clone()), mk_not(&p)),
            eqp(eqp(mk_not(&p), mk_not(&q)), eqp(p.clone(), q.clone())),
            eqp(all_x(&a, fx, p.clone()), p.clone()), // (∀x:α. P) = P
        ];
        let pred_const = Expr::lam(BinderInfo::Default, a.clone(), p.clone());
        leaves.push(eqp(ex_encoding(&a, &pred_const), p.clone())); // (∃x:α. P) = P
        let ppx = Expr::app(pp.clone(), x.clone());
        leaves.push(eqp(
            all_x(&a, fx, arrow(eq_obj(&a, &x, &t), ppx.clone())),
            Expr::app(pp.clone(), t.clone()),
        )); // (∀x. x=t⟶Pp x)=Pp t
        let pred_op = Expr::lam(
            BinderInfo::Default,
            a.clone(),
            mk_conj(&eq_obj(&a, &x, &t), &ppx).abstract_fvar(fx),
        );
        leaves.push(eqp(
            ex_encoding(&a, &pred_op),
            Expr::app(pp.clone(), t.clone()),
        )); // (∃x. x=t∧Pp x)=Pp t
        check_bundle(
            "simp_thms",
            &[
                (Expr::type_(), fa),
                (prop(), fp),
                (prop(), fq),
                (pred_ty(&a), fpp),
                (a.clone(), ft),
            ],
            &[nonempty_ty(&a)],
            &leaves,
        );
    }

    // ── single-leaf NonemptyErase routing (standalone quantifier laws) ──────

    #[test]
    fn single_leaf_vacuous_forall_under_nonempty() {
        // ⋀(α:Type)(P:Prop). Nonempty α → ((∀x:α. P) = P)  — a WHOLE theorem whose
        // conclusion is a single vacuous-∀ equation, routed through the single-leaf
        // arm (not a `Pure.conjunction` bundle).
        let mut env = base_env();
        let (fa, fp, fx) = (
            FVarId::new(0xC001),
            FVarId::new(0xC002),
            FVarId::new(0xC00A),
        );
        let (a, p) = (Expr::fvar(fa), Expr::fvar(fp));
        let leaf = eqp(all_x(&a, fx, p.clone()), p.clone());
        let stmt = arrow(nonempty_ty(&a), leaf);
        let proof = prove_nonempty_single_leaf(&stmt).expect("single vacuous-∀ leaf recognized");
        let close = |mut b: Expr, is_pi: bool| {
            for (dom, fv) in [(prop(), fp), (Expr::type_(), fa)] {
                b = if is_pi {
                    Expr::pi(BinderInfo::Default, dom.clone(), b.abstract_fvar(fv))
                } else {
                    Expr::lam(BinderInfo::Default, dom.clone(), b.abstract_fvar(fv))
                };
            }
            b
        };
        add_check(
            &mut env,
            "standalone_vacuous_forall",
            close(stmt.clone(), true),
            close(proof, false),
        );
    }

    #[test]
    fn single_leaf_declines_without_nonempty_witness() {
        // Soundness floor: under a bare `True →` premise (historical Erase spelling)
        // the single-leaf arm MUST decline the vacuous-∀ law — no witness ⇒ false
        // over an empty sort.
        let (a, p) = (
            Expr::fvar(FVarId::new(0xC011)),
            Expr::fvar(FVarId::new(0xC012)),
        );
        let fx = FVarId::new(0xC01A);
        let leaf = eqp(all_x(&a, fx, p.clone()), p.clone());
        let stmt = arrow(Expr::const_str("True"), leaf);
        assert!(
            prove_nonempty_single_leaf(&stmt).is_none(),
            "no `Nonempty` premise ⇒ single vacuous-∀ leaf must decline"
        );
    }

    #[test]
    fn single_leaf_declines_a_bundle() {
        // A ≥2-leaf `And` conclusion is the bundle prover's job; the single-leaf arm
        // declines it (leaf count ≠ 1).
        let (a, p, q) = (
            Expr::fvar(FVarId::new(0xC021)),
            Expr::fvar(FVarId::new(0xC022)),
            Expr::fvar(FVarId::new(0xC023)),
        );
        let fx = FVarId::new(0xC02A);
        let and_ = |x: Expr, y: Expr| Expr::apps(Expr::const_str("And"), [x, y]);
        let l1 = eqp(all_x(&a, fx, p.clone()), p.clone());
        let l2 = eqp(mk_conj(&q, &c_true()), q.clone());
        let stmt = arrow(nonempty_ty(&a), and_(l1, l2));
        assert!(
            prove_nonempty_single_leaf(&stmt).is_none(),
            "a 2-leaf bundle is not a single leaf"
        );
    }

    // ── straggler leaf arms (the un-enumerated `simp_thms` conjuncts) ───────

    #[test]
    fn leaf_not_iff() {
        // (¬(P = Q)) = (P = ¬Q)
        check_leaf("(¬(P=Q))=(P=¬Q)", |p, q| {
            eqp(
                mk_not(&eqp(p.clone(), q.clone())),
                eqp(p.clone(), mk_not(q)),
            )
        });
    }
    // ── classical/constructive normal-form laws (prove_classical_prop_leaf) ──

    /// Close `body` (over three Prop atoms `p`,`q`,`r`) under `⋀P Q R.` / `λP Q R.`.
    fn close3(fp: FVarId, fq: FVarId, fr: FVarId, body: Expr, is_pi: bool) -> Expr {
        let mk = |dom: Expr, b: Expr| {
            if is_pi {
                Expr::pi(BinderInfo::Default, dom, b)
            } else {
                Expr::lam(BinderInfo::Default, dom, b)
            }
        };
        let i0 = mk(prop(), body.abstract_fvar(fr));
        let i1 = mk(prop(), i0.abstract_fvar(fq));
        mk(prop(), i1.abstract_fvar(fp))
    }

    /// Build a leaf from three fresh Prop atoms, prove it, and kernel-check the
    /// `⋀P Q R.`-closed theorem with foundational closure.
    fn check_leaf3(name: &str, leaf_of: impl Fn(&Expr, &Expr, &Expr) -> Expr) {
        let mut env = base_env();
        let (fp, fq, fr) = (
            FVarId::new(0xBB01),
            FVarId::new(0xBB02),
            FVarId::new(0xBB03),
        );
        let (p, q, r) = (Expr::fvar(fp), Expr::fvar(fq), Expr::fvar(fr));
        let leaf = leaf_of(&p, &q, &r);
        let proof = prove_simp_leaf(&leaf)
            .unwrap_or_else(|| panic!("`{name}`: prove_simp_leaf returned None"));
        add_check(
            &mut env,
            name,
            close3(fp, fq, fr, leaf, true),
            close3(fp, fq, fr, proof, false),
        );
    }

    #[test]
    fn leaf_conj_comm() {
        // (P ∧ Q) = (Q ∧ P)
        check_leaf("(P∧Q)=(Q∧P)", |p, q| eqp(mk_conj(p, q), mk_conj(q, p)));
    }
    #[test]
    fn leaf_disj_comm() {
        // (P ∨ Q) = (Q ∨ P)
        check_leaf("(P∨Q)=(Q∨P)", |p, q| eqp(mk_disj(p, q), mk_disj(q, p)));
    }
    #[test]
    fn leaf_demorgan_conj() {
        // ¬(P ∧ Q) = (¬P ∨ ¬Q)
        check_leaf("¬(P∧Q)=(¬P∨¬Q)", |p, q| {
            eqp(mk_not(&mk_conj(p, q)), mk_disj(&mk_not(p), &mk_not(q)))
        });
    }
    #[test]
    fn leaf_demorgan_disj() {
        // ¬(P ∨ Q) = (¬P ∧ ¬Q)
        check_leaf("¬(P∨Q)=(¬P∧¬Q)", |p, q| {
            eqp(mk_not(&mk_disj(p, q)), mk_conj(&mk_not(p), &mk_not(q)))
        });
    }
    #[test]
    fn leaf_imp_as_disj() {
        // (P ⟶ Q) = (¬P ∨ Q)
        check_leaf("(P⟶Q)=(¬P∨Q)", |p, q| {
            eqp(arrow(p.clone(), q.clone()), mk_disj(&mk_not(p), q))
        });
    }
    #[test]
    fn leaf_iff_as_dnf() {
        // (P = Q) = ((P ∧ Q) ∨ (¬P ∧ ¬Q))
        check_leaf("(P=Q)=((P∧Q)∨(¬P∧¬Q))", |p, q| {
            eqp(
                eqp(p.clone(), q.clone()),
                mk_disj(&mk_conj(p, q), &mk_conj(&mk_not(p), &mk_not(q))),
            )
        });
    }
    #[test]
    fn leaf_not_iff_as_dnf() {
        // ¬(P = Q) = ((P ∧ ¬Q) ∨ (¬P ∧ Q))
        check_leaf("¬(P=Q)=((P∧¬Q)∨(¬P∧Q))", |p, q| {
            eqp(
                mk_not(&eqp(p.clone(), q.clone())),
                mk_disj(&mk_conj(p, &mk_not(q)), &mk_conj(&mk_not(p), q)),
            )
        });
    }
    #[test]
    fn leaf_distrib_conj_over_disj_left() {
        // (P ∧ (Q ∨ R)) = ((P ∧ Q) ∨ (P ∧ R))
        check_leaf3("(P∧(Q∨R))=((P∧Q)∨(P∧R))", |p, q, r| {
            eqp(
                mk_conj(p, &mk_disj(q, r)),
                mk_disj(&mk_conj(p, q), &mk_conj(p, r)),
            )
        });
    }
    #[test]
    fn leaf_distrib_conj_over_disj_right() {
        // ((P ∨ Q) ∧ R) = ((P ∧ R) ∨ (Q ∧ R))
        check_leaf3("((P∨Q)∧R)=((P∧R)∨(Q∧R))", |p, q, r| {
            eqp(
                mk_conj(&mk_disj(p, q), r),
                mk_disj(&mk_conj(p, r), &mk_conj(q, r)),
            )
        });
    }

    #[test]
    fn leaf_excluded_middle_right() {
        // (P ∨ ¬P) = True
        check_leaf("(P∨¬P)=True", |p, _q| {
            eqp(mk_disj(p, &mk_not(p)), c_true())
        });
    }
    #[test]
    fn leaf_excluded_middle_left() {
        // (¬P ∨ P) = True
        check_leaf("(¬P∨P)=True", |p, _q| {
            eqp(mk_disj(&mk_not(p), p), c_true())
        });
    }
    #[test]
    fn leaf_imp_false_is_not() {
        // (P → False) = ¬P
        check_leaf("(P→False)=¬P", |p, _q| {
            eqp(arrow(p.clone(), c_false()), mk_not(p))
        });
    }
    #[test]
    fn leaf_imp_not_self() {
        // (P → ¬P) = ¬P
        check_leaf("(P→¬P)=¬P", |p, _q| {
            eqp(arrow(p.clone(), mk_not(p)), mk_not(p))
        });
    }
    #[test]
    fn leaf_conj_absorb() {
        // (P ∧ (P ∧ Q)) = (P ∧ Q)
        check_leaf("(P∧(P∧Q))=(P∧Q)", |p, q| {
            eqp(mk_conj(p, &mk_conj(p, q)), mk_conj(p, q))
        });
    }
    #[test]
    fn leaf_conj_contradiction_right() {
        // (P ∧ ¬P) = False
        check_leaf("(P∧¬P)=False", |p, _q| {
            eqp(mk_conj(p, &mk_not(p)), c_false())
        });
    }
    #[test]
    fn leaf_conj_contradiction_left() {
        // (¬P ∧ P) = False
        check_leaf("(¬P∧P)=False", |p, _q| {
            eqp(mk_conj(&mk_not(p), p), c_false())
        });
    }
    #[test]
    fn leaf_disj_absorb() {
        // (P ∨ (P ∨ Q)) = (P ∨ Q)
        check_leaf("(P∨(P∨Q))=(P∨Q)", |p, q| {
            eqp(mk_disj(p, &mk_disj(p, q)), mk_disj(p, q))
        });
    }
    #[test]
    fn leaf_neg_self_eq_left() {
        // ¬((¬P) = P)   — a bare (non-equational) proposition leaf.
        check_leaf("¬((¬P)=P)", |p, _q| mk_not(&eqp(mk_not(p), p.clone())));
    }
    #[test]
    fn leaf_neg_self_eq_right() {
        // ¬(P = (¬P))
        check_leaf("¬(P=(¬P))", |p, _q| mk_not(&eqp(p.clone(), mk_not(p))));
    }

    #[test]
    fn leaf_eq_self_true() {
        // ⋀(α:Type)(x:α). (x = x) = True   — reflexivity at an object sort.
        let (fa, fx) = (FVarId::new(0xF201), FVarId::new(0xF202));
        let (a, x) = (Expr::fvar(fa), Expr::fvar(fx));
        let leaf = eqp(eq_obj(&a, &x, &x), c_true());
        check_witfree_leaf("(x=x)=True", &[(Expr::type_(), fa), (a.clone(), fx)], leaf);
    }
    #[test]
    fn leaf_exists_refl_x_eq_t() {
        // ⋀(α:Type)(t:α). ∃x. x = t   — a bare `∃`-reflexivity witness.
        let (fa, ft, fx) = (
            FVarId::new(0xF211),
            FVarId::new(0xF212),
            FVarId::new(0xF21A),
        );
        let (a, t, x) = (Expr::fvar(fa), Expr::fvar(ft), Expr::fvar(fx));
        let pred = Expr::lam(
            BinderInfo::Default,
            a.clone(),
            eq_obj(&a, &x, &t).abstract_fvar(fx),
        );
        let leaf = ex_encoding(&a, &pred);
        check_witfree_leaf("∃x. x=t", &[(Expr::type_(), fa), (a.clone(), ft)], leaf);
    }
    #[test]
    fn leaf_exists_refl_t_eq_x() {
        // ⋀(α:Type)(t:α). ∃x. t = x
        let (fa, ft, fx) = (
            FVarId::new(0xF221),
            FVarId::new(0xF222),
            FVarId::new(0xF22A),
        );
        let (a, t, x) = (Expr::fvar(fa), Expr::fvar(ft), Expr::fvar(fx));
        let pred = Expr::lam(
            BinderInfo::Default,
            a.clone(),
            eq_obj(&a, &t, &x).abstract_fvar(fx),
        );
        let leaf = ex_encoding(&a, &pred);
        check_witfree_leaf("∃x. t=x", &[(Expr::type_(), fa), (a.clone(), ft)], leaf);
    }
    #[test]
    fn leaf_all_not_eq_x_eq_t() {
        // ⋀(α:Type)(t:α). (∀x. x ≠ t) = False
        let (fa, ft, fx) = (
            FVarId::new(0xF231),
            FVarId::new(0xF232),
            FVarId::new(0xF23A),
        );
        let (a, t, x) = (Expr::fvar(fa), Expr::fvar(ft), Expr::fvar(fx));
        let leaf = eqp(all_x(&a, fx, mk_not(&eq_obj(&a, &x, &t))), c_false());
        check_witfree_leaf(
            "(∀x. x≠t)=False",
            &[(Expr::type_(), fa), (a.clone(), ft)],
            leaf,
        );
    }
    #[test]
    fn leaf_all_not_eq_t_eq_x() {
        // ⋀(α:Type)(t:α). (∀x. t ≠ x) = False
        let (fa, ft, fx) = (
            FVarId::new(0xF241),
            FVarId::new(0xF242),
            FVarId::new(0xF24A),
        );
        let (a, t, x) = (Expr::fvar(fa), Expr::fvar(ft), Expr::fvar(fx));
        let leaf = eqp(all_x(&a, fx, mk_not(&eq_obj(&a, &t, &x))), c_false());
        check_witfree_leaf(
            "(∀x. t≠x)=False",
            &[(Expr::type_(), fa), (a.clone(), ft)],
            leaf,
        );
    }

    #[test]
    fn leaf_meta_universal_onepoint_forall() {
        // ⋀(α:Type)(t:α). [⋀P. (∀x. x = t ⟶ P x) = P t]  — the per-conjunct `⋀P`
        // meta-binder peeled by `prove_meta_universal`, inner discharged witness-free.
        let (fa, ft, fpp, fx) = (
            FVarId::new(0xF251),
            FVarId::new(0xF252),
            FVarId::new(0xF253),
            FVarId::new(0xF25A),
        );
        let (a, t, pp, x) = (
            Expr::fvar(fa),
            Expr::fvar(ft),
            Expr::fvar(fpp),
            Expr::fvar(fx),
        );
        let ppx = Expr::app(pp.clone(), x.clone());
        let inner = eqp(
            all_x(&a, fx, arrow(eq_obj(&a, &x, &t), ppx)),
            Expr::app(pp.clone(), t.clone()),
        );
        let leaf = Expr::pi(BinderInfo::Default, pred_ty(&a), inner.abstract_fvar(fpp));
        check_witfree_leaf(
            "⋀P. (∀x. x=t⟶P x)=P t",
            &[(Expr::type_(), fa), (a.clone(), ft)],
            leaf,
        );
    }

    // ── whole-bundle preflight: the EXACT corpus conjunct inventories ───────

    /// The EXACT `simp_thms` (corpus serial 82306) inventory: all **44** conjuncts
    /// in source order, under the four `Nonempty α` sort premises (`'a,'b,'c,'d`),
    /// with the per-conjunct `⋀P` binders on the one-point conjuncts preserved.
    /// Proving THIS end-to-end guarantees the corpus flip (modulo mode routing).
    #[test]
    fn bundle_simp_thms_exact_corpus_82306() {
        let (fa, fb, fc, fd) = (
            FVarId::new(0xAB01),
            FVarId::new(0xAB02),
            FVarId::new(0xAB03),
            FVarId::new(0xAB04),
        );
        let (fp, fq, fx, ft) = (
            FVarId::new(0xAB10),
            FVarId::new(0xAB11),
            FVarId::new(0xAB12),
            FVarId::new(0xAB13),
        );
        let (a, b, c, d) = (
            Expr::fvar(fa),
            Expr::fvar(fb),
            Expr::fvar(fc),
            Expr::fvar(fd),
        );
        let (p, q, x, t) = (
            Expr::fvar(fp), // P : Prop
            Expr::fvar(fq), // Q : Prop
            Expr::fvar(fx), // x : 'a  (eq_self)
            Expr::fvar(ft), // t : 'd  (one-point / ∃-refl / all_not_eq witness)
        );
        // Per-conjunct `⋀P` binder over `'d → Prop` for the one-point conjuncts.
        let fpp = FVarId::new(0xAB20);
        let pp = Expr::fvar(fpp);
        let fbx = FVarId::new(0xAB2A); // bound `x : 'd` inside the meta conjuncts
        let bx = Expr::fvar(fbx);
        let meta_all = |inner: Expr| -> Expr {
            Expr::pi(BinderInfo::Default, pred_ty(&d), inner.abstract_fvar(fpp))
        };
        let ppbx = Expr::app(pp.clone(), bx.clone());
        let ppt = Expr::app(pp.clone(), t.clone());

        let leaves: Vec<Expr> = vec![
            eqp(mk_not(&mk_not(&p)), p.clone()),                         // 0
            eqp(eqp(mk_not(&p), mk_not(&q)), eqp(p.clone(), q.clone())), // 1
            eqp(
                mk_not(&eqp(p.clone(), q.clone())),
                eqp(p.clone(), mk_not(&q)),
            ), // 2
            eqp(mk_disj(&p, &mk_not(&p)), c_true()),                     // 3
            eqp(mk_disj(&mk_not(&p), &p), c_true()),                     // 4
            eqp(eq_obj(&a, &x, &x), c_true()),                           // 5
            eqp(mk_not(&c_true()), c_false()),                           // 6
            eqp(mk_not(&c_false()), c_true()),                           // 7
            mk_not(&eqp(mk_not(&p), p.clone())),                         // 8
            mk_not(&eqp(p.clone(), mk_not(&p))),                         // 9
            eqp(eqp(c_true(), p.clone()), p.clone()),                    // 10
            eqp(eqp(p.clone(), c_true()), p.clone()),                    // 11
            eqp(eqp(c_false(), p.clone()), mk_not(&p)),                  // 12
            eqp(eqp(p.clone(), c_false()), mk_not(&p)),                  // 13
            eqp(arrow(c_true(), p.clone()), p.clone()),                  // 14
            eqp(arrow(c_false(), p.clone()), c_true()),                  // 15
            eqp(arrow(p.clone(), c_true()), c_true()),                   // 16
            eqp(arrow(p.clone(), p.clone()), c_true()),                  // 17
            eqp(arrow(p.clone(), c_false()), mk_not(&p)),                // 18
            eqp(arrow(p.clone(), mk_not(&p)), mk_not(&p)),               // 19
            eqp(mk_conj(&p, &c_true()), p.clone()),                      // 20
            eqp(mk_conj(&c_true(), &p), p.clone()),                      // 21
            eqp(mk_conj(&p, &c_false()), c_false()),                     // 22
            eqp(mk_conj(&c_false(), &p), c_false()),                     // 23
            eqp(mk_conj(&p, &p), p.clone()),                             // 24
            eqp(mk_conj(&p, &mk_conj(&p, &q)), mk_conj(&p, &q)),         // 25
            eqp(mk_conj(&p, &mk_not(&p)), c_false()),                    // 26
            eqp(mk_conj(&mk_not(&p), &p), c_false()),                    // 27
            eqp(mk_disj(&p, &c_true()), c_true()),                       // 28
            eqp(mk_disj(&c_true(), &p), c_true()),                       // 29
            eqp(mk_disj(&p, &c_false()), p.clone()),                     // 30
            eqp(mk_disj(&c_false(), &p), p.clone()),                     // 31
            eqp(mk_disj(&p, &p), p.clone()),                             // 32
            eqp(mk_disj(&p, &mk_disj(&p, &q)), mk_disj(&p, &q)),         // 33
            eqp(
                Expr::pi(BinderInfo::Default, b.clone(), p.clone()),
                p.clone(),
            ), // 34 (∀x:'b.P)=P
            eqp(
                ex_encoding(&c, &Expr::lam(BinderInfo::Default, c.clone(), p.clone())),
                p.clone(),
            ), // 35 (∃x:'c.P)=P
            ex_encoding(
                &d,
                &Expr::lam(
                    BinderInfo::Default,
                    d.clone(),
                    eq_obj(&d, &bx, &t).abstract_fvar(fbx),
                ),
            ), // 36 ∃x. x=t
            ex_encoding(
                &d,
                &Expr::lam(
                    BinderInfo::Default,
                    d.clone(),
                    eq_obj(&d, &t, &bx).abstract_fvar(fbx),
                ),
            ), // 37 ∃x. t=x
            meta_all(eqp(
                ex_encoding(
                    &d,
                    &Expr::lam(
                        BinderInfo::Default,
                        d.clone(),
                        mk_conj(&eq_obj(&d, &bx, &t), &ppbx).abstract_fvar(fbx),
                    ),
                ),
                ppt.clone(),
            )), // 38 ⋀P. (∃x. x=t ∧ P x)=P t
            meta_all(eqp(
                ex_encoding(
                    &d,
                    &Expr::lam(
                        BinderInfo::Default,
                        d.clone(),
                        mk_conj(&eq_obj(&d, &t, &bx), &ppbx).abstract_fvar(fbx),
                    ),
                ),
                ppt.clone(),
            )), // 39 ⋀P. (∃x. t=x ∧ P x)=P t
            meta_all(eqp(
                all_x(&d, fbx, arrow(eq_obj(&d, &bx, &t), ppbx.clone())),
                ppt.clone(),
            )), // 40 ⋀P. (∀x. x=t ⟶ P x)=P t
            meta_all(eqp(
                all_x(&d, fbx, arrow(eq_obj(&d, &t, &bx), ppbx.clone())),
                ppt.clone(),
            )), // 41 ⋀P. (∀x. t=x ⟶ P x)=P t
            eqp(all_x(&d, fbx, mk_not(&eq_obj(&d, &bx, &t))), c_false()), // 42 (∀x. x≠t)=False
            eqp(all_x(&d, fbx, mk_not(&eq_obj(&d, &t, &bx))), c_false()), // 43 (∀x. t≠x)=False
        ];
        assert_eq!(leaves.len(), 44, "simp_thms has exactly 44 conjuncts");
        check_bundle(
            "simp_thms_exact_82306",
            &[
                (Expr::type_(), fa),
                (Expr::type_(), fb),
                (Expr::type_(), fc),
                (Expr::type_(), fd),
                (prop(), fp),
                (prop(), fq),
                (a.clone(), fx),
                (d.clone(), ft),
            ],
            &[
                nonempty_ty(&a),
                nonempty_ty(&b),
                nonempty_ty(&c),
                nonempty_ty(&d),
            ],
            &leaves,
        );
    }

    /// The EXACT `all_simps` (corpus serial 88136) inventory: all **6** miniscoping
    /// conjuncts, each under its own per-conjunct `⋀P Q` binder, over six distinct
    /// sort premises (`'a…'f`). The ∧-miniscoping pair consumes the `Nonempty`
    /// witness; the ∨/⟶ quartet is witness-free. End-to-end corpus pre-flight.
    #[test]
    fn bundle_all_simps_exact_corpus_88136() {
        let sorts: Vec<(FVarId, Expr)> = (0..6)
            .map(|i| {
                let fv = FVarId::new(0xAC01 + i);
                (fv, Expr::fvar(fv))
            })
            .collect();
        let s = |i: usize| sorts[i].1.clone();
        // Per-conjunct meta binders `⋀P Q` (fresh fvars) and the bound `x`.
        let fpp = FVarId::new(0xAC20);
        let fqq = FVarId::new(0xAC21);
        let fx = FVarId::new(0xAC2A);
        let (pp, qq, x) = (Expr::fvar(fpp), Expr::fvar(fqq), Expr::fvar(fx));
        // `⋀(P:pty) (Q:qty). body`
        let meta2 = |pty: Expr, qty: Expr, body: Expr| -> Expr {
            let inner = Expr::pi(BinderInfo::Default, qty, body.abstract_fvar(fqq));
            Expr::pi(BinderInfo::Default, pty, inner.abstract_fvar(fpp))
        };

        // 0: ⋀P Q. (∀x:'a. P x ∧ Q) = ((∀x:'a. P x) ∧ Q)   — right-const (needs 'a witness)
        let c0 = {
            let sort = s(0);
            let px = Expr::app(pp.clone(), x.clone());
            let body = eqp(
                all_x(&sort, fx, mk_conj(&px, &qq)),
                mk_conj(&all_x(&sort, fx, px.clone()), &qq),
            );
            meta2(pred_ty(&sort), prop(), body)
        };
        // 1: ⋀P Q. (∀x:'b. P ∧ Q x) = (P ∧ (∀x:'b. Q x))    — left-const (needs 'b witness)
        let c1 = {
            let sort = s(1);
            let qx = Expr::app(qq.clone(), x.clone());
            let body = eqp(
                all_x(&sort, fx, mk_conj(&pp, &qx)),
                mk_conj(&pp, &all_x(&sort, fx, qx.clone())),
            );
            meta2(prop(), pred_ty(&sort), body)
        };
        // 2: ⋀P Q. (∀x:'c. P x ∨ Q) = ((∀x:'c. P x) ∨ Q)    — right-const (witness-free)
        let c2 = {
            let sort = s(2);
            let px = Expr::app(pp.clone(), x.clone());
            let body = eqp(
                all_x(&sort, fx, mk_disj(&px, &qq)),
                mk_disj(&all_x(&sort, fx, px.clone()), &qq),
            );
            meta2(pred_ty(&sort), prop(), body)
        };
        // 3: ⋀P Q. (∀x:'d. P ∨ Q x) = (P ∨ (∀x:'d. Q x))    — left-const (witness-free)
        let c3 = {
            let sort = s(3);
            let qx = Expr::app(qq.clone(), x.clone());
            let body = eqp(
                all_x(&sort, fx, mk_disj(&pp, &qx)),
                mk_disj(&pp, &all_x(&sort, fx, qx.clone())),
            );
            meta2(prop(), pred_ty(&sort), body)
        };
        // 4: ⋀P Q. (∀x:'e. P x ⟶ Q) = ((∃x:'e. P x) ⟶ Q)   — ante-dep (witness-free)
        let c4 = {
            let sort = s(4);
            let px = Expr::app(pp.clone(), x.clone());
            let pred = Expr::lam(
                BinderInfo::Default,
                sort.clone(),
                px.clone().abstract_fvar(fx),
            );
            let body = eqp(
                all_x(&sort, fx, arrow(px.clone(), qq.clone())),
                arrow(ex_encoding(&sort, &pred), qq.clone()),
            );
            meta2(pred_ty(&sort), prop(), body)
        };
        // 5: ⋀P Q. (∀x:'f. P ⟶ Q x) = (P ⟶ (∀x:'f. Q x))    — cons-dep (witness-free)
        let c5 = {
            let sort = s(5);
            let qx = Expr::app(qq.clone(), x.clone());
            let body = eqp(
                all_x(&sort, fx, arrow(pp.clone(), qx.clone())),
                arrow(pp.clone(), all_x(&sort, fx, qx.clone())),
            );
            meta2(prop(), pred_ty(&sort), body)
        };

        let binders: Vec<(Expr, FVarId)> =
            sorts.iter().map(|(fv, _)| (Expr::type_(), *fv)).collect();
        let prems: Vec<Expr> = sorts.iter().map(|(_, s)| nonempty_ty(s)).collect();
        check_bundle(
            "all_simps_exact_88136",
            &binders,
            &prems,
            &[c0, c1, c2, c3, c4, c5],
        );
    }

    // ── ex_simps (s87998): the ∃-miniscoping duals of all_simps ─────────────

    /// Build `ex_encoding(sort, λx. body[fx:=x])` from an under-binder `body`.
    fn ex_x(sort: &Expr, fx: FVarId, body: Expr) -> Expr {
        ex_encoding(
            sort,
            &Expr::lam(BinderInfo::Default, sort.clone(), body.abstract_fvar(fx)),
        )
    }

    /// The EXACT `ex_simps` bundle (corpus serial 87998): all **6** `∃`-miniscoping
    /// conjuncts — the `∃`-duals of `all_simps` — each under its own `⋀P Q` meta-binder,
    /// over six distinct sort premises (`'a…'f`). The `∃∧` pair is witness-free; the
    /// `∃∨`/`∃⟶` quartet consumes the `Nonempty` witness. End-to-end corpus pre-flight.
    #[test]
    fn bundle_ex_simps_exact_corpus_87998() {
        // Six sorts 'a…'f, each with its own `Nonempty` premise.
        let sorts: Vec<(FVarId, Expr)> = (0..6)
            .map(|i| {
                let fv = FVarId::new(0xEC01 + i);
                (fv, Expr::fvar(fv))
            })
            .collect();
        let s = |i: usize| sorts[i].1.clone();
        let (fpp, fqq, fx) = (
            FVarId::new(0xEC20),
            FVarId::new(0xEC21),
            FVarId::new(0xEC2A),
        );
        let (pp, qq, x) = (Expr::fvar(fpp), Expr::fvar(fqq), Expr::fvar(fx));
        // `⋀(P:pty)(Q:qty). body`
        let meta2 = |pty: Expr, qty: Expr, body: Expr| -> Expr {
            let inner = Expr::pi(BinderInfo::Default, qty, body.abstract_fvar(fqq));
            Expr::pi(BinderInfo::Default, pty, inner.abstract_fvar(fpp))
        };

        // C1: ⋀P Q. (∃x:'a. P x ∧ Q) = ((∃x:'a. P x) ∧ Q)   — ∃∧ right-const (witness-free)
        let c1 = {
            let sort = s(0);
            let px = Expr::app(pp.clone(), x.clone());
            let body = eqp(
                ex_x(&sort, fx, mk_conj(&px, &qq)),
                mk_conj(&ex_x(&sort, fx, px.clone()), &qq),
            );
            meta2(pred_ty(&sort), prop(), body)
        };
        // C2: ⋀P Q. (∃x:'b. P ∧ Q x) = (P ∧ (∃x:'b. Q x))   — ∃∧ left-const (witness-free)
        let c2 = {
            let sort = s(1);
            let qx = Expr::app(qq.clone(), x.clone());
            let body = eqp(
                ex_x(&sort, fx, mk_conj(&pp, &qx)),
                mk_conj(&pp, &ex_x(&sort, fx, qx.clone())),
            );
            meta2(prop(), pred_ty(&sort), body)
        };
        // C3: ⋀P Q. (∃x:'c. P x ∨ Q) = ((∃x:'c. P x) ∨ Q)   — ∃∨ right-const (needs 'c witness)
        let c3 = {
            let sort = s(2);
            let px = Expr::app(pp.clone(), x.clone());
            let body = eqp(
                ex_x(&sort, fx, mk_disj(&px, &qq)),
                mk_disj(&ex_x(&sort, fx, px.clone()), &qq),
            );
            meta2(pred_ty(&sort), prop(), body)
        };
        // C4: ⋀P Q. (∃x:'d. P ∨ Q x) = (P ∨ (∃x:'d. Q x))   — ∃∨ left-const (needs 'd witness)
        let c4 = {
            let sort = s(3);
            let qx = Expr::app(qq.clone(), x.clone());
            let body = eqp(
                ex_x(&sort, fx, mk_disj(&pp, &qx)),
                mk_disj(&pp, &ex_x(&sort, fx, qx.clone())),
            );
            meta2(prop(), pred_ty(&sort), body)
        };
        // C5: ⋀P Q. (∃x:'e. P x ⟶ Q) = ((∀x:'e. P x) ⟶ Q)  — ∃⟶ ante-dep (needs 'e witness)
        let c5 = {
            let sort = s(4);
            let px = Expr::app(pp.clone(), x.clone());
            let body = eqp(
                ex_x(&sort, fx, arrow(px.clone(), qq.clone())),
                arrow(all_x(&sort, fx, px.clone()), qq.clone()),
            );
            meta2(pred_ty(&sort), prop(), body)
        };
        // C6: ⋀P Q. (∃x:'f. P ⟶ Q x) = (P ⟶ (∃x:'f. Q x))  — ∃⟶ cons-dep (needs 'f witness)
        let c6 = {
            let sort = s(5);
            let qx = Expr::app(qq.clone(), x.clone());
            let body = eqp(
                ex_x(&sort, fx, arrow(pp.clone(), qx.clone())),
                arrow(pp.clone(), ex_x(&sort, fx, qx.clone())),
            );
            meta2(prop(), pred_ty(&sort), body)
        };

        let binders: Vec<(Expr, FVarId)> =
            sorts.iter().map(|(fv, _)| (Expr::type_(), *fv)).collect();
        let prems: Vec<Expr> = sorts.iter().map(|(_, s)| nonempty_ty(s)).collect();
        check_bundle(
            "ex_simps_exact_87998",
            &binders,
            &prems,
            &[c1, c2, c3, c4, c5, c6],
        );
    }

    /// Exercise a single `∃`-miniscope leaf `l1` inside a real 2-leaf `Nonempty α`
    /// bundle (paired with `¬¬R=R`), so its proof is kernel-re-checked with
    /// foundational closure in isolation. The closure receives `α`, a predicate fvar
    /// `pd : α→Prop` (the x-dependent operand) and a Prop fvar `pc` (the constant
    /// operand), plus the bound-var id `fx`.
    fn check_ex_leaf(name: &str, l1_of: impl Fn(&Expr, &Expr, &Expr, FVarId) -> Expr) {
        let (fa, fpd, fpc, frr, fx) = (
            FVarId::new(0xED01),
            FVarId::new(0xED02),
            FVarId::new(0xED03),
            FVarId::new(0xED04),
            FVarId::new(0xED0A),
        );
        let (a, pd, pc, rr) = (
            Expr::fvar(fa),
            Expr::fvar(fpd),
            Expr::fvar(fpc),
            Expr::fvar(frr),
        );
        let l1 = l1_of(&a, &pd, &pc, fx);
        let l2 = eqp(mk_not(&mk_not(&rr)), rr.clone());
        check_wit_bundle(
            name,
            &[
                (Expr::type_(), fa),
                (pred_ty(&a), fpd),
                (prop(), fpc),
                (prop(), frr),
            ],
            l1,
            l2,
            &a,
        );
    }

    #[test]
    fn leaf_ex_conj_miniscope_right_const() {
        // (∃x. Pd x ∧ Pc) = ((∃x. Pd x) ∧ Pc)
        check_ex_leaf("(∃x.Px∧Q)=((∃x.Px)∧Q)", |a, pd, pc, fx| {
            let px = Expr::app(pd.clone(), Expr::fvar(fx));
            eqp(
                ex_x(a, fx, mk_conj(&px, pc)),
                mk_conj(&ex_x(a, fx, px.clone()), pc),
            )
        });
    }
    #[test]
    fn leaf_ex_conj_miniscope_left_const() {
        // (∃x. Pc ∧ Pd x) = (Pc ∧ (∃x. Pd x))
        check_ex_leaf("(∃x.P∧Qx)=(P∧(∃x.Qx))", |a, pd, pc, fx| {
            let qx = Expr::app(pd.clone(), Expr::fvar(fx));
            eqp(
                ex_x(a, fx, mk_conj(pc, &qx)),
                mk_conj(pc, &ex_x(a, fx, qx.clone())),
            )
        });
    }
    #[test]
    fn leaf_ex_disj_miniscope_right_const() {
        // (∃x. Pd x ∨ Pc) = ((∃x. Pd x) ∨ Pc)
        check_ex_leaf("(∃x.Px∨Q)=((∃x.Px)∨Q)", |a, pd, pc, fx| {
            let px = Expr::app(pd.clone(), Expr::fvar(fx));
            eqp(
                ex_x(a, fx, mk_disj(&px, pc)),
                mk_disj(&ex_x(a, fx, px.clone()), pc),
            )
        });
    }
    #[test]
    fn leaf_ex_disj_miniscope_left_const() {
        // (∃x. Pc ∨ Pd x) = (Pc ∨ (∃x. Pd x))
        check_ex_leaf("(∃x.P∨Qx)=(P∨(∃x.Qx))", |a, pd, pc, fx| {
            let qx = Expr::app(pd.clone(), Expr::fvar(fx));
            eqp(
                ex_x(a, fx, mk_disj(pc, &qx)),
                mk_disj(pc, &ex_x(a, fx, qx.clone())),
            )
        });
    }
    #[test]
    fn leaf_ex_imp_miniscope_ante_dep() {
        // (∃x. Pd x ⟶ Pc) = ((∀x. Pd x) ⟶ Pc)
        check_ex_leaf("(∃x.Px⟶Q)=((∀x.Px)⟶Q)", |a, pd, pc, fx| {
            let px = Expr::app(pd.clone(), Expr::fvar(fx));
            eqp(
                ex_x(a, fx, arrow(px.clone(), pc.clone())),
                arrow(all_x(a, fx, px.clone()), pc.clone()),
            )
        });
    }
    #[test]
    fn leaf_ex_imp_miniscope_cons_dep() {
        // (∃x. Pc ⟶ Pd x) = (Pc ⟶ (∃x. Pd x))
        check_ex_leaf("(∃x.P⟶Qx)=(P⟶(∃x.Qx))", |a, pd, pc, fx| {
            let qx = Expr::app(pd.clone(), Expr::fvar(fx));
            eqp(
                ex_x(a, fx, arrow(pc.clone(), qx.clone())),
                arrow(pc.clone(), ex_x(a, fx, qx.clone())),
            )
        });
    }

    // ── additional exact-corpus normal-form bundles (bundle-sweep-prep) ──────
    //
    // The three purely-propositional `Pure.conjunction` bundles in the V3 reject
    // pool that the classical/constructive normal-form arms newly unblock, each
    // reconstructed at its EXACT corpus conjunct inventory + order (no OFCLASS
    // premises → no witness needed). Proving these end-to-end through
    // `prove_conjunction_bundle` is the corpus flip guarantee.

    /// EXACT corpus bundle **s2325932** (4 conjuncts, no premises): `∧`-over-`∨`
    /// distributivity (both orientations) + `∧`/`∨` commutativity — all constructive.
    #[test]
    fn bundle_distrib_comm_exact_corpus_2325932() {
        let (fp, fq, fr) = (
            FVarId::new(0xAD01),
            FVarId::new(0xAD02),
            FVarId::new(0xAD03),
        );
        let (p, q, r) = (Expr::fvar(fp), Expr::fvar(fq), Expr::fvar(fr));
        let leaves = vec![
            eqp(
                mk_conj(&p, &mk_disj(&q, &r)),
                mk_disj(&mk_conj(&p, &q), &mk_conj(&p, &r)),
            ), // 0 (P∧(Q∨R))=((P∧Q)∨(P∧R))
            eqp(
                mk_conj(&mk_disj(&p, &q), &r),
                mk_disj(&mk_conj(&p, &r), &mk_conj(&q, &r)),
            ), // 1 ((P∨Q)∧R)=((P∧R)∨(Q∧R))
            eqp(mk_conj(&p, &q), mk_conj(&q, &p)), // 2 (P∧Q)=(Q∧P)
            eqp(mk_disj(&p, &q), mk_disj(&q, &p)), // 3 (P∨Q)=(Q∨P)
        ];
        assert_eq!(leaves.len(), 4, "s2325932 has exactly 4 conjuncts");
        check_bundle(
            "distrib_comm_exact_2325932",
            &[(prop(), fp), (prop(), fq), (prop(), fr)],
            &[],
            &leaves,
        );
    }

    /// EXACT corpus bundle **s2325842** (5 conjuncts, no premises): the two De
    /// Morgan laws, `⟶`-as-`∨`, iff-DNF, and double-negation.
    #[test]
    fn bundle_classical_nf5_exact_corpus_2325842() {
        let (fp, fq) = (FVarId::new(0xAE01), FVarId::new(0xAE02));
        let (p, q) = (Expr::fvar(fp), Expr::fvar(fq));
        let leaves = vec![
            eqp(mk_not(&mk_conj(&p, &q)), mk_disj(&mk_not(&p), &mk_not(&q))), // 0 ¬(P∧Q)=(¬P∨¬Q)
            eqp(mk_not(&mk_disj(&p, &q)), mk_conj(&mk_not(&p), &mk_not(&q))), // 1 ¬(P∨Q)=(¬P∧¬Q)
            eqp(arrow(p.clone(), q.clone()), mk_disj(&mk_not(&p), &q)),       // 2 (P⟶Q)=(¬P∨Q)
            eqp(
                eqp(p.clone(), q.clone()),
                mk_disj(&mk_conj(&p, &q), &mk_conj(&mk_not(&p), &mk_not(&q))),
            ), // 3 (P=Q)=((P∧Q)∨(¬P∧¬Q))
            eqp(mk_not(&mk_not(&p)), p.clone()),                              // 4 ¬¬P=P
        ];
        assert_eq!(leaves.len(), 5, "s2325842 has exactly 5 conjuncts");
        check_bundle(
            "classical_nf5_exact_2325842",
            &[(prop(), fp), (prop(), fq)],
            &[],
            &leaves,
        );
    }

    /// EXACT corpus bundle **s95156** (6 conjuncts, no premises): the s2325842
    /// inventory plus the not-iff-DNF conjunct (before double-negation).
    #[test]
    fn bundle_classical_nf6_exact_corpus_95156() {
        let (fp, fq) = (FVarId::new(0xAF01), FVarId::new(0xAF02));
        let (p, q) = (Expr::fvar(fp), Expr::fvar(fq));
        let leaves = vec![
            eqp(mk_not(&mk_conj(&p, &q)), mk_disj(&mk_not(&p), &mk_not(&q))), // 0 ¬(P∧Q)=(¬P∨¬Q)
            eqp(mk_not(&mk_disj(&p, &q)), mk_conj(&mk_not(&p), &mk_not(&q))), // 1 ¬(P∨Q)=(¬P∧¬Q)
            eqp(arrow(p.clone(), q.clone()), mk_disj(&mk_not(&p), &q)),       // 2 (P⟶Q)=(¬P∨Q)
            eqp(
                eqp(p.clone(), q.clone()),
                mk_disj(&mk_conj(&p, &q), &mk_conj(&mk_not(&p), &mk_not(&q))),
            ), // 3 (P=Q)=((P∧Q)∨(¬P∧¬Q))
            eqp(
                mk_not(&eqp(p.clone(), q.clone())),
                mk_disj(&mk_conj(&p, &mk_not(&q)), &mk_conj(&mk_not(&p), &q)),
            ), // 4 ¬(P=Q)=((P∧¬Q)∨(¬P∧Q))
            eqp(mk_not(&mk_not(&p)), p.clone()),                              // 5 ¬¬P=P
        ];
        assert_eq!(leaves.len(), 6, "s95156 has exactly 6 conjuncts");
        check_bundle(
            "classical_nf6_exact_95156",
            &[(prop(), fp), (prop(), fq)],
            &[],
            &leaves,
        );
    }

    // ── eq_ac (s83088): object-sort eq-commute + iff-algebra leaves ─────────

    #[test]
    fn leaf_eq_commute_obj() {
        // (a = b) = (b = a) at an object sort α : Type (`Eq.symm` at obj level).
        let (falpha, fa, fb) = (
            FVarId::new(0xB101),
            FVarId::new(0xB102),
            FVarId::new(0xB103),
        );
        let alpha = Expr::fvar(falpha);
        let (a, b) = (Expr::fvar(fa), Expr::fvar(fb));
        let leaf = eqp(eq_obj(&alpha, &a, &b), eq_obj(&alpha, &b, &a));
        check_witfree_leaf(
            "(a=b)=(b=a)@obj",
            &[(Expr::type_(), falpha), (alpha.clone(), fa), (alpha, fb)],
            leaf,
        );
    }

    #[test]
    fn leaf_iff_assoc() {
        // ((P = Q) = R) = (P = (Q = R))  (iff-associativity).
        check_leaf3("((P=Q)=R)=(P=(Q=R))", |p, q, r| {
            eqp(
                eqp(eqp(p.clone(), q.clone()), r.clone()),
                eqp(p.clone(), eqp(q.clone(), r.clone())),
            )
        });
    }

    #[test]
    fn leaf_iff_left_commute() {
        // (P = (Q = R)) = (Q = (P = R))  (iff-left-commutativity).
        check_leaf3("(P=(Q=R))=(Q=(P=R))", |p, q, r| {
            eqp(
                eqp(p.clone(), eqp(q.clone(), r.clone())),
                eqp(q.clone(), eqp(p.clone(), r.clone())),
            )
        });
    }

    /// The EXACT `eq_ac` bundle (corpus serial 83088): 3 conjuncts under one erased
    /// `OFCLASS('a, type)` (→ `True →`) premise — object-sort eq-commute
    /// `(a=b)=(b=a)`, iff-left-commute `(P=(Q=R))=(Q=(P=R))`, iff-assoc
    /// `((P=Q)=R)=(P=(Q=R))`. All witness-free, so the bundle flips in the historical
    /// `Erase` mode. Proving THIS end-to-end guarantees the corpus flip.
    #[test]
    fn bundle_eq_ac_exact_corpus_83088() {
        let (falpha, fa, fb) = (
            FVarId::new(0xB201),
            FVarId::new(0xB202),
            FVarId::new(0xB203),
        );
        let (fp, fq, fr) = (
            FVarId::new(0xB210),
            FVarId::new(0xB211),
            FVarId::new(0xB212),
        );
        let alpha = Expr::fvar(falpha);
        let (a, b) = (Expr::fvar(fa), Expr::fvar(fb));
        let (p, q, r) = (Expr::fvar(fp), Expr::fvar(fq), Expr::fvar(fr));
        let leaves = vec![
            // C1: (a = b) = (b = a)   at object sort 'a
            eqp(eq_obj(&alpha, &a, &b), eq_obj(&alpha, &b, &a)),
            // C2: (P = (Q = R)) = (Q = (P = R))   (iff-left-commute)
            eqp(
                eqp(p.clone(), eqp(q.clone(), r.clone())),
                eqp(q.clone(), eqp(p.clone(), r.clone())),
            ),
            // C3: ((P = Q) = R) = (P = (Q = R))   (iff-assoc)
            eqp(
                eqp(eqp(p.clone(), q.clone()), r.clone()),
                eqp(p.clone(), eqp(q.clone(), r.clone())),
            ),
        ];
        assert_eq!(leaves.len(), 3, "s83088 has exactly 3 conjuncts");
        check_bundle(
            "eq_ac_exact_83088",
            &[
                (Expr::type_(), falpha),
                (alpha.clone(), fa),
                (alpha, fb),
                (prop(), fp),
                (prop(), fq),
                (prop(), fr),
            ],
            &[Expr::const_str("True")],
            &leaves,
        );
    }

    // ── non-right-associated tree shape ─────────────────────────────────────
    // The corpus-scale root cause of the s82306 / s88136 / s87998 rejects: the
    // exported `Pure.conjunction` bundles are NON-right-associated `And` trees (a
    // left child is itself a conjunction). Every [`check_bundle`] fixture assembles
    // a RIGHT-associated tree, so the right-spine [`prove_conjunction_bundle`] +
    // [`flatten_and`] passed them all while silently declining the corpus shape.
    // These tests exercise the shape the fixtures missed.

    /// Assemble `leaves` into a **balanced** `And` tree. For ≥4 leaves this is
    /// guaranteed non-right-associated (the root's left child is itself an `And`) —
    /// exactly the corpus bundle shape the right-spine walker cannot flatten.
    fn balanced_and(leaves: &[Expr]) -> Expr {
        if leaves.len() == 1 {
            return leaves[0].clone();
        }
        let mid = leaves.len() / 2;
        Expr::apps(
            Expr::const_str("And"),
            [balanced_and(&leaves[..mid]), balanced_and(&leaves[mid..])],
        )
    }

    /// Like [`check_bundle`] but assembles the leaves into a BALANCED (non-right-
    /// associated) `And` tree and discharges it through the structural
    /// [`prove_conjunction_bundle_tree`]. When the tree is genuinely non-right-
    /// associated it also asserts the historical right-spine [`prove_conjunction_bundle`]
    /// DECLINES it — locking in the corpus-scale root cause. End-to-end kernel-checked.
    fn check_bundle_tree(name: &str, binders: &[(Expr, FVarId)], prems: &[Expr], leaves: &[Expr]) {
        let mut env = base_env();
        assert!(leaves.len() >= 2, "a bundle needs ≥2 leaves");
        let tree = balanced_and(leaves);
        // Confirm the tree is non-right-associated, then assert the right-spine prover
        // cannot walk it (the exact reason the corpus bundles die at `node=AbsP`).
        if let Some((left, _)) = binop_const(&tree, "And") {
            if binop_const(&left, "And").is_some() {
                let mut probe = tree.clone();
                for p in prems.iter().rev() {
                    probe = arrow(p.clone(), probe);
                }
                assert!(
                    prove_conjunction_bundle(&probe).is_none(),
                    "`{name}`: right-spine prover must decline the non-right-associated tree"
                );
            }
        }
        let mut body = tree;
        for p in prems.iter().rev() {
            body = arrow(p.clone(), body);
        }
        let stmt = body;
        let proof = prove_conjunction_bundle_tree(&stmt)
            .unwrap_or_else(|| panic!("`{name}`: structural bundle prover declined"));
        let close = |mut b: Expr, is_pi: bool| {
            for (dom, fv) in binders.iter().rev() {
                b = if is_pi {
                    Expr::pi(BinderInfo::Default, dom.clone(), b.abstract_fvar(*fv))
                } else {
                    Expr::lam(BinderInfo::Default, dom.clone(), b.abstract_fvar(*fv))
                };
            }
            b
        };
        add_check(
            &mut env,
            name,
            close(stmt.clone(), true),
            close(proof, false),
        );
    }

    #[test]
    fn non_right_assoc_bundle_witfree() {
        // Four witness-free propositional simp laws in a balanced tree under two erased
        // `True →` premises — the minimal reproduction of the tree-shape bug.
        let (fp, fq) = (FVarId::new(0xDD01), FVarId::new(0xDD02));
        let (p, q) = (Expr::fvar(fp), Expr::fvar(fq));
        let leaves = vec![
            eqp(mk_conj(&p, &c_true()), p.clone()),  // (P∧True)=P
            eqp(mk_not(&mk_not(&q)), q.clone()),     // ¬¬Q=Q
            eqp(mk_disj(&p, &c_false()), p.clone()), // (P∨False)=P
            eqp(mk_not(&mk_conj(&p, &q)), mk_disj(&mk_not(&p), &mk_not(&q))), // ¬(P∧Q)=(¬P∨¬Q)
        ];
        check_bundle_tree(
            "non_right_assoc_bundle_witfree",
            &[(prop(), fp), (prop(), fq)],
            &[Expr::const_str("True"), Expr::const_str("True")],
            &leaves,
        );
    }

    #[test]
    fn non_right_assoc_all_simps_witnessed() {
        // The full `all_simps` inventory (the ∧-miniscoping pair needs the `Nonempty α`
        // witness), assembled into a NON-right-associated tree under one `Nonempty α`
        // premise — a corpus-faithful analogue of s88136 in the shape the right-spine
        // prover declines.
        let (fa, fpd, fqc, fpc, fqd, fx) = (
            FVarId::new(0xDE01),
            FVarId::new(0xDE02),
            FVarId::new(0xDE03),
            FVarId::new(0xDE04),
            FVarId::new(0xDE05),
            FVarId::new(0xDE0A),
        );
        let (a, pd, qc, pc, qd, x) = (
            Expr::fvar(fa),
            Expr::fvar(fpd),
            Expr::fvar(fqc),
            Expr::fvar(fpc),
            Expr::fvar(fqd),
            Expr::fvar(fx),
        );
        let pdx = Expr::app(pd.clone(), x.clone());
        let qdx = Expr::app(qd.clone(), x.clone());
        let all_pdx = all_x(&a, fx, pdx.clone());
        let all_qdx = all_x(&a, fx, qdx.clone());
        let pred_pd = Expr::lam(
            BinderInfo::Default,
            a.clone(),
            pdx.clone().abstract_fvar(fx),
        );
        let c1 = eqp(all_x(&a, fx, mk_conj(&pdx, &qc)), mk_conj(&all_pdx, &qc));
        let c2 = eqp(all_x(&a, fx, mk_conj(&pc, &qdx)), mk_conj(&pc, &all_qdx));
        let c3 = eqp(all_x(&a, fx, mk_disj(&pdx, &qc)), mk_disj(&all_pdx, &qc));
        let c4 = eqp(all_x(&a, fx, mk_disj(&pc, &qdx)), mk_disj(&pc, &all_qdx));
        let c5 = eqp(
            all_x(&a, fx, arrow(pdx.clone(), qc.clone())),
            arrow(ex_encoding(&a, &pred_pd), qc.clone()),
        );
        let c6 = eqp(
            all_x(&a, fx, arrow(pc.clone(), qdx.clone())),
            arrow(pc.clone(), all_qdx),
        );
        check_bundle_tree(
            "non_right_assoc_all_simps_witnessed",
            &[
                (Expr::type_(), fa),
                (pred_ty(&a), fpd),
                (prop(), fqc),
                (prop(), fpc),
                (pred_ty(&a), fqd),
            ],
            &[nonempty_ty(&a)],
            &[c1, c2, c3, c4, c5, c6],
        );
    }
}
