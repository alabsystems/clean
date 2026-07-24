// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Definitional discharge of **locale-predicate projection** nodes
//! (`type_class α ⟹ class.C args ⟹ class.subpredᵢ subargs`).
//!
//! A structured type class's `class.C_def` axiom equates the locale predicate
//! with a right-associated conjunction of its superclass locale predicates and
//! its own axioms predicate (`class.semiring ?plus ?times ≡
//! class.ab_semigroup_add ?plus ∧ (class.semigroup_mult ?times ∧
//! class.semiring_axioms ?plus ?times)`). Isabelle exports, for each conjunct, a
//! PROJECTION node deriving `class.subpredᵢ subargs` from the `class.C args`
//! hypothesis. Its recorded proof reconstructs the def equation via chained
//! `HOL.atomize_conj` + `Pure.combination` + `Pure.transitive` (the meta↔object
//! conjunction bridge), which the translator reconstructs for a 2-way
//! conjunction (`order`, `linorder`, `order_bot`, `monoid_add`, …) but NOT for
//! the deeper 3-way+ nestings (`semiring`, `comm_ring`, the `Fields`/`Rings`
//! families) — those bottom in the `expected=Eq got=Eq @thm AbsP` congruence
//! tower.
//!
//! Under [`Ctx::instance_unfold`] the hypothesis `class.C args` embeds to its
//! registered `isabelle.polyinst.<c>` def-const, which δ-unfolds to exactly the
//! embedded conjunction whose i-th conjunct is the conclusion. So the projection
//! is a DEFINITIONAL conjunct extraction: the impredicative `conj_def`
//! projection (`isabelle.def.HOL.conj A B` δ= `∀C.(A→B→C)→C`) descends the
//! right spine and selects the matched conjunct — no recorded-proof
//! reconstruction, no congruence tower. FAITHFUL: the stored type is the REAL
//! projection statement (distinct `class.C` premise / `class.subpred`
//! conclusion, never a tautology); the kernel re-checks `value : type` against
//! it (δβ-reducing the def-const), so a wrong extraction is rejected — never
//! miscounted. Gated on `instance_unfold`, so strictly additive (earlier opaque
//! passes are unchanged).

use clean_kernel::expr::{ExprKind, FVarId};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr};

use super::super::super::isabelle_pure::{IsaProvenTheorem, IsaTerm, IsaType};
use super::super::*;

/// Defensive recursion cap for the conclusion-side nested-locale-predicate
/// reassembly ([`Ctx::discharge_pred_conjunct`] step 4). The Isabelle locale
/// hierarchy is well-founded (a predicate's body references strictly-smaller
/// predicates), so this is never approached in practice — it only guards against
/// a hypothetically cyclic registry.
const LOCALE_REASSEMBLE_MAX_DEPTH: usize = 16;

/// Defensive recursion cap for the OfClass→membership **superclass projection**
/// ([`Ctx::project_membership_conjunct`]). The type-class hierarchy is
/// well-founded (a class membership's body references strictly-smaller superclass
/// memberships), so this is never approached in practice — it only guards against
/// a hypothetically cyclic class registry.
const MEMBERSHIP_PROJ_MAX_DEPTH: usize = 16;

/// The impredicative `conj_def` def-const applied to its two operands
/// (`isabelle.def.HOL.conj A B`, δ-equal to `∀C.(A→B→C)→C`).
pub(crate) fn conj_def(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("isabelle.def.HOL.conj"), [a, b])
}

/// Match an **object-level** conjunction `And P Q` (`App(App(Const "And", P), Q)`),
/// returning `(P, Q)`. This is the shape a structured class membership's
/// `Pure.conjunction` body embeds to (`embed_term` maps `Pure.conjunction → And`),
/// so a membership def-const δ-unfolds to a right-nested `And` tree of its
/// superclass memberships + the class's own axioms predicate.
fn as_and_node(e: &Expr) -> Option<(&Expr, &Expr)> {
    if let ExprKind::App(app_a, q) = e.kind() {
        if let ExprKind::App(and_head, p) = app_a.kind() {
            if matches!(and_head.kind(), ExprKind::Const(n, _) if *n == Name::from_string("And")) {
                return Some((p, q));
            }
        }
    }
    None
}

/// `And.left P Q h : P` — the object-level conjunction's first projection
/// (`conjunctionD1` under the `Pure.conjunction → And` embedding).
fn and_left_obj(p: Expr, q: Expr, h: Expr) -> Expr {
    Expr::apps(Expr::const_str("And.left"), [p, q, h])
}

/// `And.right P Q h : Q` — the object-level conjunction's second projection
/// (`conjunctionD2`).
fn and_right_obj(p: Expr, q: Expr, h: Expr) -> Expr {
    Expr::apps(Expr::const_str("And.right"), [p, q, h])
}

/// `And.left` for the impredicative conjunction: `h : conj_def A B ⊢ h A (λa b. a) : A`.
pub(crate) fn and_left(a: Expr, b: Expr, h: Expr) -> Expr {
    let sel = Expr::lam(
        BinderInfo::Default,
        a.clone(),
        Expr::lam(BinderInfo::Default, b, Expr::bvar(1)),
    );
    Expr::apps(h, [a, sel])
}

/// `And.right` for the impredicative conjunction: `h : conj_def A B ⊢ h B (λa b. b) : B`.
pub(crate) fn and_right(a: Expr, b: Expr, h: Expr) -> Expr {
    let sel = Expr::lam(
        BinderInfo::Default,
        a,
        Expr::lam(BinderInfo::Default, b.clone(), Expr::bvar(0)),
    );
    Expr::apps(h, [b, sel])
}

/// `And.intro` for the impredicative conjunction: given `ha : A`, `hb : B`
/// (both CLOSED w.r.t. the local binders), build a proof of `conj_def A B`
/// (`isabelle.def.HOL.conj A B` δ= `∀C. (A → B → C) → C`):
/// `λ(C:Prop) (f: A → B → C). f ha hb`. `A`/`B`/`ha`/`hb` reference only the
/// premise-binder fvars and the object type/operation params (no de Bruijn
/// bvars in this context), so no lifting of them over the `C`/`f` binders is
/// needed; the `bvar` indices below are the local `C`/`f` references.
fn and_intro(a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
    // f's domain, built under the `C` binder (so `C = bvar 0` at its root):
    // `A → B → C` = `Pi(_:A). Pi(_:B). bvar 2` (C seen through the two arrows).
    let f_dom = Expr::pi(
        BinderInfo::Default,
        a,
        Expr::pi(BinderInfo::Default, b, Expr::bvar(2)),
    );
    // Under the `C` (bvar 1) and `f` (bvar 0) binders: `f ha hb`.
    let body = Expr::apps(Expr::bvar(0), [ha, hb]);
    Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::lam(BinderInfo::Default, f_dom, body),
    )
}

/// The impredicative conjunction INTRO of a right-nested `conj_def` from proofs
/// of each conjunct: given `conjs = [E₀, …, Eₙ]` (embedded conjunct types) and
/// `hyps = [h₀, …, hₙ]` (proofs, `hᵢ : Eᵢ`), build a proof of
/// `conj_def(E₀, conj_def(E₁, … Eₙ))` (a single `Eₙ` proof when `n == 0`).
fn conj_def_intro(conjs: &[Expr], hyps: &[Expr]) -> Expr {
    let n = conjs.len();
    if n == 1 {
        return hyps[0].clone();
    }
    let rest_ty = right_nested_conj_def(&conjs[1..]);
    let rest_proof = conj_def_intro(&conjs[1..], &hyps[1..]);
    and_intro(conjs[0].clone(), rest_ty, hyps[0].clone(), rest_proof)
}

/// The right-nested `conj_def` TYPE of `[E₀, …, Eₙ]`:
/// `conj_def(E₀, conj_def(E₁, … Eₙ))` (just `Eₙ` when a singleton).
fn right_nested_conj_def(conjs: &[Expr]) -> Expr {
    let n = conjs.len();
    if n == 1 {
        return conjs[0].clone();
    }
    conj_def(conjs[0].clone(), right_nested_conj_def(&conjs[1..]))
}

/// The number of leading universal quantifiers (`∀`/`⋀`) of a (Trueprop-
/// stripped) HOL/Pure term — the count of `HOL.All (λ…)` / `Pure.all (λ…)`
/// binders before the first non-quantifier head. These are the **operand
/// binders** of a class-body conjunct (`∀x y. lt x y = …`): the number of
/// leading clean `Pi` a specialized (schematic-instantiated) projection must
/// instantiate to reach its use-site conclusion (see [`conjunct_instance_apply`]).
fn count_leading_hol_all(tm: &IsaTerm) -> usize {
    let t = strip_prop_wrappers(tm);
    if let IsaTerm::App { f, a } = t {
        if is_const(f, "HOL.All") || is_const(f, "Pure.all") {
            if let IsaTerm::Abs { b, .. } = a.as_ref() {
                return 1 + count_leading_hol_all(b);
            }
        }
    }
    0
}

/// First-order structural match of `pat` against `tgt`, treating every `FVar`
/// whose id is in `sentinels` as a match variable (recording its `tgt`
/// counterpart in `subst`, and requiring later occurrences to be identical).
/// Every non-sentinel position must be structurally equal. Returns `false` on
/// any mismatch. Used to recover the use-site operands of a schematic-
/// instantiated class-body conjunct: the conjunct's `∀`-bound operands are
/// opened with sentinel fvars, and matching the opened body against the
/// projection's conclusion pins each sentinel to its actual operand.
fn fo_match(pat: &Expr, tgt: &Expr, sentinels: &[FVarId], subst: &mut Vec<(FVarId, Expr)>) -> bool {
    if let ExprKind::FVar(id) = pat.kind() {
        if sentinels.contains(id) {
            return match subst.iter().find(|(s, _)| s == id) {
                Some((_, e)) => e == tgt,
                None => {
                    subst.push((*id, tgt.clone()));
                    true
                }
            };
        }
    }
    match (pat.kind(), tgt.kind()) {
        (ExprKind::App(pf, pa), ExprKind::App(tf, ta)) => {
            fo_match(pf, tf, sentinels, subst) && fo_match(pa, ta, sentinels, subst)
        }
        (ExprKind::Pi(_, pd, pb), ExprKind::Pi(_, td, tb))
        | (ExprKind::Lam(_, pd, pb), ExprKind::Lam(_, td, tb)) => {
            fo_match(pd, td, sentinels, subst) && fo_match(pb, tb, sentinels, subst)
        }
        (ExprKind::Proj(pn, pi, pe), ExprKind::Proj(tn, ti, te)) => {
            pn == tn && pi == ti && fo_match(pe, te, sentinels, subst)
        }
        _ => pat == tgt,
    }
}

/// If `target` is a **schematic instance** of the class-body conjunct
/// `clean_cj` (`isa_cj` its ISA spelling) — i.e. `clean_cj = ∀x₀…xₖ. body` and
/// `target = body[xᵢ := opᵢ]` for some use-site operands `opᵢ` — return the
/// proof `proof op₀ … opₖ : target` (where `proof : clean_cj`). This is the
/// specialized dual of the exact-match case in [`Ctx::extract_conjunct`]: a
/// class axiom exported at *specific* schematic operands (`less ?x.0 ?y.0 ≡ …`,
/// `times (plus ?a ?b) ?c = …`) rather than universally (`∀x y. …`) needs the
/// conjunct proof *applied* to those operands. The operands are recovered by
/// opening the conjunct's `∀`-telescope with sentinel fvars and first-order
/// matching the opened body against `target` ([`fo_match`]). Returns `None` when
/// the shape does not match; the kernel re-checks `proof ops : target`, so a
/// wrong recovery rejects — never miscounts.
fn conjunct_instance_apply(
    isa_cj: &IsaTerm,
    clean_cj: &Expr,
    proof: &Expr,
    target: &Expr,
) -> Option<Expr> {
    let nq = count_leading_hol_all(isa_cj);
    if nq == 0 {
        // No operand binders to instantiate: the exact-match case (handled by
        // the caller) is the only applicable discharge.
        return None;
    }
    // Open the conjunct's `∀`-telescope with fresh sentinel fvars (a distinct id
    // range from the projection's premise binders / recursion — collision would
    // only be caught by the kernel re-check anyway, but the range keeps them
    // disjoint by construction).
    let mut cur = clean_cj.clone();
    let mut sentinels: Vec<FVarId> = Vec::with_capacity(nq);
    for d in 0..nq {
        let ExprKind::Pi(_, _, cod) = cur.kind() else {
            return None;
        };
        let s = FVarId::new(0x9c06_0000 + d as u64);
        sentinels.push(s);
        cur = cod.instantiate(&Expr::fvar(s));
    }
    let mut subst: Vec<(FVarId, Expr)> = Vec::new();
    if !fo_match(&cur, target, &sentinels, &mut subst) {
        return None;
    }
    // Read the operands off the substitution in binder order; every sentinel
    // must have been pinned (an unused binder would leave it free — decline).
    let mut operands: Vec<Expr> = Vec::with_capacity(nq);
    for s in &sentinels {
        operands.push(subst.iter().find(|(x, _)| x == s).map(|(_, e)| e.clone())?);
    }
    Some(Expr::apps(proof.clone(), operands))
}

/// Apply a **type-variable substitution** to every carried HOL type inside a
/// term (`Const`/`Free`/`Var` annotations and `Abs` binder types), leaving the
/// term structure otherwise intact. The dual of [`subst_isa_vars`]: that helper
/// substitutes a locale predicate's formal TERM arguments, but a registered
/// predicate whose def-side object type variables are instantiated NON-trivially
/// at a use-site (the `Typedef.type_definition` `'a ↔ 'b` swap — `obj_tvars =
/// [('b,0),('a,0)]`) leaves residual def-side TYPE variables in the body
/// conjuncts that `subst_isa_vars` never touches: the `∀`-binder domain, the
/// `HOL.eq` / `Set.member` operator type instances. Those must be mapped through
/// the same [`match_tvars`] solution the use-site's def-const application
/// δ-unfolds under, or the projected conjunct's operator instances leak the
/// def's raw `'a`/`'b` and the kernel re-check rejects. Used only by
/// [`Ctx::guarded_conjunct_projection`]; the exact-match / bare schematic-instance
/// passes (whose registered predicates have identity type instantiation) are
/// unaffected.
fn subst_term_tvars(tm: &IsaTerm, subs: &[((String, i64), IsaType)]) -> IsaTerm {
    match tm {
        IsaTerm::Const { n, t } => IsaTerm::Const {
            n: n.clone(),
            t: subst_tvars(t, subs),
        },
        IsaTerm::Free { n, t } => IsaTerm::Free {
            n: n.clone(),
            t: subst_tvars(t, subs),
        },
        IsaTerm::Var { n, i, t } => IsaTerm::Var {
            n: n.clone(),
            i: *i,
            t: subst_tvars(t, subs),
        },
        IsaTerm::Bound { i } => IsaTerm::Bound { i: *i },
        IsaTerm::Abs { n, t, b } => IsaTerm::Abs {
            n: n.clone(),
            t: subst_tvars(t, subs),
            b: Box::new(subst_term_tvars(b, subs)),
        },
        IsaTerm::App { f, a } => IsaTerm::App {
            f: Box::new(subst_term_tvars(f, subs)),
            a: Box::new(subst_term_tvars(a, subs)),
        },
    }
}

/// Substitute each schematic `Var { n, i }` matching a `subst` key with the
/// paired actual term (the use-site operand). The formal arguments of a locale
/// predicate are schematic `Var`s (never bound), so no capture is possible.
pub(crate) fn subst_isa_vars(tm: &IsaTerm, subst: &[((String, i64), IsaTerm)]) -> IsaTerm {
    match tm {
        IsaTerm::Var { n, i, .. } => subst
            .iter()
            .find(|((kn, ki), _)| kn == n && ki == i)
            .map(|(_, v)| v.clone())
            .unwrap_or_else(|| tm.clone()),
        IsaTerm::App { f, a } => IsaTerm::App {
            f: Box::new(subst_isa_vars(f, subst)),
            a: Box::new(subst_isa_vars(a, subst)),
        },
        IsaTerm::Abs { n, t, b } => IsaTerm::Abs {
            n: n.clone(),
            t: t.clone(),
            b: Box::new(subst_isa_vars(b, subst)),
        },
        _ => tm.clone(),
    }
}

impl Ctx {
    /// If `thm` is a **locale-predicate projection** node whose hypothesis
    /// `class.C args` is a registered poly-inst locale predicate with a
    /// conjunction body containing the conclusion `class.subpred subargs` as a
    /// conjunct, return `(proof_value, stored_type)` discharging it by the
    /// impredicative `conj_def` projection (see the module header). Returns
    /// `None` (caller falls through to the recorded-proof translation) when the
    /// shape does not match or the discharge is not applicable in this pass.
    ///
    /// Only fires under [`Self::instance_unfold`]: the discharge relies on the
    /// hypothesis's def-const δ-unfolding to the conjunction, which happens only
    /// in an Unfold pass. Strictly additive.
    pub(crate) fn prove_locale_projection(
        &mut self,
        thm: &IsaProvenTheorem,
    ) -> Result<Option<(Expr, Expr)>, TranslateError> {
        if !self.instance_unfold {
            return Ok(None);
        }
        let prop = &thm.prop;
        // Peel ONLY the leading `⟹` premises (`type_class α ⟹ class.C args ⟹ …`)
        // as the value's lambda binders. We deliberately do NOT peel a leading
        // `⋀x:T.` universal here: for a **raw class-axiom** conjunct (`⋀x y. lt x y
        // ≡ (le x y ∧ ¬ le y x)`, the `less_le_not_le`/`order_refl`/… axioms lifted
        // to standalone projections) the `⋀x y` belongs to the CONCLUSION, not the
        // premise list — it is exactly the `HOL.All x y.` the class body's conjunct
        // spells (both embed to the same clean `Pi`), so it must stay part of the
        // matched conclusion `cod`, not become an extra lambda. (r10-ofclassfam's
        // locale-predicate conclusions `class.subpred subargs` carry no leading
        // `⋀`, so this is a pure generalization — those still peel the same premises
        // and match the same way.)
        let mut prems: Vec<IsaTerm> = Vec::new();
        let mut cur = strip_prop_wrappers(prop);
        while let Some((lhs, rhs)) = split_pure_imp(cur) {
            prems.push(lhs.clone());
            cur = strip_prop_wrappers(rhs);
        }
        let m = prems.len();
        if m == 0 {
            return Ok(None);
        }
        // The conclusion (after `Pure.prop`/`Trueprop` stripping) must be a
        // `Const`-headed application — either a superclass **locale-predicate**
        // (`class.subpred subargs`, r10-ofclassfam) OR a **raw class-axiom**
        // conjunct (`∀x y. lt x y ≡ (le x y ∧ ¬ le y x)`, head `Pure.all`/`HOL.eq`/
        // `HOL.All`/…). Both are conjuncts of the `class.C_def` right-associated
        // body, so both are dischargeable by the SAME impredicative `conj_def`
        // projection: the recorded congruence-tower reconstruction of the
        // meta↔object bridge (the `expected=Eq got=Eq @thm AbsP` wall, r10-congruence
        // root B) is UNNECESSARY under `instance_unfold` — the hypothesis's def-const
        // δ-unfolds to the conjunction and the i-th conjunct is extracted directly.
        // The exact `cod == conjuncts[k]` match below (line ~180) is the real gate:
        // a conclusion that is NOT structurally one of the registered class body's
        // conjuncts declines the discharge and falls through unchanged, so widening
        // the admitted conclusion head is strictly additive (kernel re-checks
        // `value : type` δβ-reducing the def-const, so a wrong extraction rejects).
        // The conclusion head may be a `Const` (`HOL.eq` for a `less ?x ?y ≡ …` /
        // `times … = …` axiom, or a superclass locale predicate) OR a `Free`/`Var`
        // — the class OPERATION itself for an operation-headed raw axiom
        // (reflexivity `le ?x ?x`, transitivity `le ?x ?z`, commutativity's
        // operand `…`). These are all conjuncts of the `class.C_def` body; the
        // exact/instance `extract_conjunct` match is the real gate, so admitting an
        // atomic (Const/Free/Var) head is strictly additive (the kernel re-checks
        // `value : type`, so a non-conjunct conclusion rejects). An App/Abs/Bound
        // head is never a projection conclusion — decline early.
        let concl_inner = strip_prop_wrappers(strip_leading_imps(prop));
        let (concl_head, _) = term_app_spine(concl_inner);
        if !matches!(
            concl_head,
            IsaTerm::Const { .. } | IsaTerm::Free { .. } | IsaTerm::Var { .. }
        ) {
            return Ok(None);
        }
        // Embed the whole statement to the stored type, and peel its `m` leading
        // `Pi` binders into fresh proof-binder fvars (the value's lambdas).
        let mut binders: Vec<Binder> = Vec::new();
        let stored_ty = self.embed_term(prop, &mut binders)?;
        let mut cod = stored_ty.clone();
        let mut binder_doms: Vec<Expr> = Vec::with_capacity(m);
        let mut binder_fvars: Vec<FVarId> = Vec::with_capacity(m);
        for i in 0..m {
            let ExprKind::Pi(_, dom, c) = cod.kind() else {
                return Ok(None);
            };
            let fv = FVarId::new(0x9c04_0000 + i as u64);
            binder_doms.push((**dom).clone());
            binder_fvars.push(fv);
            cod = c.instantiate(&Expr::fvar(fv));
        }
        // `cod` is now the embedded conclusion (a locale-predicate application, a
        // raw class-axiom, …). Find the premise that is a registered locale
        // predicate `class.C args` from whose conjunction body — **recursively**,
        // descending nested locale-predicate conjuncts (`class.C ⊇ class.C_axioms ⊇
        // axiomᵢ`) — `cod` is reachable as a leaf. `extract_conjunct` returns the
        // impredicative `conj_def` extraction (a chain of `And.left`/`And.right`).
        for (idx, prem) in prems.iter().enumerate() {
            let (phead, pargs) = term_app_spine(strip_prop_wrappers(prem));
            let IsaTerm::Const { n: c_name, .. } = phead else {
                continue;
            };
            let pargs_owned: Vec<IsaTerm> = pargs.iter().map(|&a| a.clone()).collect();
            // **Pass 1** — target = the bare conclusion `cod`. Covers the r10/r11
            // exact-match cases (locale-predicate + universally-quantified `∀x y`
            // raw-axiom conjuncts) AND the r12 schematic-instance conjuncts with
            // NO extra premises (`less ?x.0 ?y.0 ≡ …`, `times (plus ?a ?b) ?c =
            // …`), which `extract_conjunct`'s instance discharge handles. Wrap the
            // extraction in one lambda per premise (the class.C binder is `idx`;
            // the others — sort hypotheses — are unused).
            let h = Expr::fvar(binder_fvars[idx]);
            if let Some(result) =
                self.extract_conjunct(c_name, &pargs_owned, h, &cod, &mut binders)?
            {
                let mut value = result;
                for i in (0..m).rev() {
                    value = Expr::lam(
                        BinderInfo::Default,
                        binder_doms[i].clone(),
                        value.abstract_fvar(binder_fvars[i]),
                    );
                }
                return Ok(Some((value, stored_ty)));
            }
            // **Pass 2 (r12)** — the conjunct's OWN implication premises exported
            // as trailing Pure premises. A conditional class axiom (transitivity
            // `∀x y z. le x y ⟹ le y z ⟹ le x z`, antisymmetry `∀x y. le x y ⟹
            // le y x ⟹ x = y`) is exported specialized as `… ⟹ class.C args ⟹
            // le ?x ?y ⟹ le ?y ?z ⟹ (le ?x ?z)`: the conjunct's `⟹` premises
            // become Pure premises AFTER the `class.C` hypothesis. Fold those
            // trailing premises back onto `cod` to reconstruct the conjunct's full
            // (instantiated) conclusion, discharge THAT, then re-apply the trailing
            // hypotheses. Only runs when there ARE trailing premises → strictly
            // additive over Pass 1.
            if idx + 1 < m {
                let mut full_cod = cod.clone();
                for j in (idx + 1..m).rev() {
                    full_cod = Expr::arrow(binder_doms[j].clone(), full_cod);
                }
                let h = Expr::fvar(binder_fvars[idx]);
                if let Some(result) =
                    self.extract_conjunct(c_name, &pargs_owned, h, &full_cod, &mut binders)?
                {
                    // `result : full_cod = binder_doms[idx+1] → … → cod`. Apply the
                    // trailing hypotheses (in order) to reach a proof of `cod`.
                    let mut value = result;
                    for fv in &binder_fvars[idx + 1..m] {
                        value = Expr::app(value, Expr::fvar(*fv));
                    }
                    for i in (0..m).rev() {
                        value = Expr::lam(
                            BinderInfo::Default,
                            binder_doms[i].clone(),
                            value.abstract_fvar(binder_fvars[i]),
                        );
                    }
                    return Ok(Some((value, stored_ty)));
                }
            }
        }
        // **Pass 3 (r13 — guarded-universal conjunct).** Pass 1/2 both exhausted:
        // the `Typedef` roundtrip family (`Abs_inverse`, …) has a conclusion that
        // is the BODY-CONCLUSION of a `∀y⃗. P → Q` conjunct with the guard `P`
        // supplied by a SEPARATE hypothesis premise (either side of the predicate),
        // AND a NON-identity object-tvar swap the shared `extract_conjunct` cannot
        // instantiate. Strictly additive over Pass 1/2 (fires only where they both
        // returned `None`). See [`Self::guarded_conjunct_projection`].
        self.guarded_conjunct_projection(
            &prems,
            m,
            &cod,
            &binder_doms,
            &binder_fvars,
            &stored_ty,
            &mut binders,
        )
    }

    /// **Pass 3 of [`Self::prove_locale_projection`] — guarded-universal conjunct
    /// projection.** Discharges a projection node whose conclusion is the
    /// body-conclusion `Q` of a registered predicate's GUARDED-UNIVERSAL conjunct
    /// `∀y⃗. P y⃗ → Q y⃗`, with the guard `P` supplied by a SEPARATE premise
    /// hypothesis. The flagship instance is the HOL `typedef` roundtrip family —
    /// `type_definition Rep Abs A ⟹ y ∈ A ⟹ Rep (Abs y) = y` (`Abs_inverse`),
    /// whose third `type_definition` conjunct is `∀y. y ∈ A ⟶ Rep (Abs y) = y`.
    ///
    /// Neither of `prove_locale_projection`'s earlier passes matches it:
    ///   - Pass 1's target `cod` is `Q` (`Rep (Abs y) = y`), NOT the `∀y.→`
    ///     conjunct, so the exact / bare schematic-instance match declines.
    ///   - Pass 2 folds only the premises TRAILING the predicate premise, but the
    ///     guard membership premise may LEAD it (it does for `s311396`), and —
    ///     decisively — `type_definition`'s object type variables are instantiated
    ///     by a NON-identity swap (`'a ↔ 'b`; `obj_tvars = [('b,0),('a,0)]`), so the
    ///     def-side conjunct's operator instances (`HOL.eq`, `Set.member`) leak the
    ///     def's raw `'a`/`'b`. The shared [`Self::extract_conjunct`] /
    ///     [`conjunct_instance_apply`] (byte-identical, funnelling every historical
    ///     locale/class projection) substitute only the formal TERM arguments, never
    ///     the object type variables, so their `fo_match` mismatches on the leaked
    ///     eq-type fvar.
    ///
    /// This pass composes the two named precedents: the [`conjunct_instance_apply`]
    /// sentinel-fvar ∀-telescope opener and the [`Self::discharge_pred_conjunct`]
    /// reassembly. It (1) solves the object-tvar instantiation from the use-site
    /// head type via [`match_tvars`], (2) instantiates the conjunct through BOTH the
    /// type swap ([`subst_term_tvars`]) and the formal term arguments
    /// ([`subst_isa_vars`]), (3) opens the `∀`-telescope with sentinel fvars and
    /// peels the non-dependent guard arrows, (4) first-order matches the guarded
    /// conclusion against `cod` to pin the operands, (5) projects the conjunct out
    /// of the predicate hypothesis by the impredicative `conj_def` right-spine
    /// descent (`and_left`/`and_right` — the SAME primitives Pass 1 uses, over the
    /// type-instantiated `conjs` the predicate's def-const δ-unfolds to), and (6)
    /// applies the pinned operands then threads each guard from the matching premise
    /// hypothesis. The kernel re-checks `value : stored_ty` δβ-reducing the
    /// predicate's def-const, so a wrong tvar solution / operand recovery / guard
    /// thread is rejected — never miscounted. FAITHFUL: the stored type is the REAL
    /// projection statement (distinct premises / conclusion, never a tautology).
    /// Returns `None` when no premise / conjunct matches the guarded shape.
    #[allow(clippy::too_many_arguments)]
    fn guarded_conjunct_projection(
        &mut self,
        prems: &[IsaTerm],
        m: usize,
        cod: &Expr,
        binder_doms: &[Expr],
        binder_fvars: &[FVarId],
        stored_ty: &Expr,
        binders: &mut Vec<Binder>,
    ) -> Result<Option<(Expr, Expr)>, TranslateError> {
        for (src_idx, prem) in prems.iter().enumerate() {
            let (phead, pargs) = term_app_spine(strip_prop_wrappers(prem));
            let IsaTerm::Const {
                n: c_name,
                t: use_ty,
            } = phead
            else {
                continue;
            };
            let Some(info) = self.poly_inst_registry.get(c_name).cloned() else {
                continue;
            };
            if info.conjuncts.is_empty() || info.arg_vars.len() != pargs.len() {
                continue;
            }
            // (1) Solve the object-type-variable instantiation from the use-site head
            // type — the NON-identity `'a ↔ 'b` swap for `type_definition`. Without
            // it the conjunct's operator instances leak the def's raw tvars and the
            // `conj_def` projection fails to type-check against the def-const's
            // δ-unfolding.
            let Some(tsubs) = match_tvars(&info.fn_ty, use_ty, &info.obj_tvars) else {
                continue;
            };
            let term_subst: Vec<((String, i64), IsaTerm)> = info
                .arg_vars
                .iter()
                .cloned()
                .zip(pargs.iter().map(|&a| a.clone()))
                .collect();
            // (2) Instantiate every conjunct through the type swap AND the formal
            // term arguments, embedding each — these are EXACTLY the terms the
            // predicate's def-const δ-unfolds to (so the `conj_def` descent below
            // kernel-type-checks).
            let mut isa_insts: Vec<IsaTerm> = Vec::with_capacity(info.conjuncts.len());
            let mut conjs: Vec<Expr> = Vec::with_capacity(info.conjuncts.len());
            for c in &info.conjuncts {
                let ci = subst_isa_vars(&subst_term_tvars(c, &tsubs), &term_subst);
                let emb = self.embed_term(&ci, binders)?;
                isa_insts.push(ci);
                conjs.push(emb);
            }
            let n = conjs.len() - 1;
            let mut rest = vec![conjs[n].clone(); conjs.len()];
            for i in (0..n).rev() {
                rest[i] = conj_def(conjs[i].clone(), rest[i + 1].clone());
            }
            for (k, isa_cj) in isa_insts.iter().enumerate() {
                let nq = count_leading_hol_all(isa_cj);
                if nq == 0 {
                    continue; // bare conjuncts are Pass 1/2's job
                }
                // (3) Open the k-th conjunct's `∀`-telescope with sentinel fvars.
                let mut cur = conjs[k].clone();
                let mut sentinels: Vec<FVarId> = Vec::with_capacity(nq);
                let mut opened = true;
                for d in 0..nq {
                    let ExprKind::Pi(_, _, body) = cur.kind() else {
                        opened = false;
                        break;
                    };
                    let s = FVarId::new(0x9c07_0000 + d as u64);
                    sentinels.push(s);
                    cur = body.instantiate(&Expr::fvar(s));
                }
                if !opened {
                    continue;
                }
                // Peel the leading NON-DEPENDENT guard arrows (`P →`); a dependent
                // `Pi` would be a further universal (not a guard), so stop there.
                let placeholder = Expr::fvar(FVarId::new(0x9c07_ff00));
                let mut guard_doms: Vec<Expr> = Vec::new();
                while let ExprKind::Pi(_, dom, body) = cur.kind() {
                    if body.loose_bvar_range() != 0 {
                        break;
                    }
                    guard_doms.push((**dom).clone());
                    cur = body.instantiate(&placeholder);
                }
                if guard_doms.is_empty() {
                    continue; // an UNGUARDED universal — leave to Pass 1/2
                }
                // (4) First-order match the guarded conclusion against `cod`, pinning
                // each sentinel to its use-site operand.
                let mut ssub: Vec<(FVarId, Expr)> = Vec::new();
                if !fo_match(&cur, cod, &sentinels, &mut ssub) {
                    continue;
                }
                let mut operands: Vec<Expr> = Vec::with_capacity(nq);
                let mut all_pinned = true;
                for s in &sentinels {
                    match ssub.iter().find(|(x, _)| x == s) {
                        Some((_, e)) => operands.push(e.clone()),
                        None => {
                            all_pinned = false;
                            break;
                        }
                    }
                }
                if !all_pinned {
                    continue;
                }
                // (6a) Thread each guard: instantiate its sentinels with the pinned
                // operands, then find a premise hypothesis whose embedded type IS the
                // resulting guard proposition.
                let mut guard_proofs: Vec<Expr> = Vec::with_capacity(guard_doms.len());
                let mut threaded = true;
                for g in &guard_doms {
                    let mut gi = g.clone();
                    for (s, op) in sentinels.iter().zip(operands.iter()) {
                        gi = gi.subst_fvar(*s, op);
                    }
                    match binder_doms.iter().position(|d| d == &gi) {
                        Some(pos) => guard_proofs.push(Expr::fvar(binder_fvars[pos])),
                        None => {
                            threaded = false;
                            break;
                        }
                    }
                }
                if !threaded {
                    continue;
                }
                // (5) Project the k-th conjunct out of the predicate hypothesis by the
                // impredicative `conj_def` right-spine descent.
                let mut hk = Expr::fvar(binder_fvars[src_idx]);
                for (j, c) in conjs.iter().enumerate().take(k) {
                    hk = and_right(c.clone(), rest[j + 1].clone(), hk);
                }
                let proof_k = if k < n {
                    and_left(conjs[k].clone(), rest[k + 1].clone(), hk)
                } else {
                    hk
                };
                // (6b) Apply the pinned operands (instantiate the `∀`s) then the guard
                // proofs (discharge the implication premises) — reaching a proof of
                // `cod`. Wrap in one lambda per statement premise.
                let mut value = proof_k;
                for op in &operands {
                    value = Expr::app(value, op.clone());
                }
                for gp in &guard_proofs {
                    value = Expr::app(value, gp.clone());
                }
                for i in (0..m).rev() {
                    value = Expr::lam(
                        BinderInfo::Default,
                        binder_doms[i].clone(),
                        value.abstract_fvar(binder_fvars[i]),
                    );
                }
                return Ok(Some((value, stored_ty.clone())));
            }
        }
        Ok(None)
    }

    /// The specialized (arg-substituted) embedded conjuncts of a registered
    /// locale predicate `c_name` applied to `pargs`, or `None` when `c_name` is
    /// not a registered poly-inst locale predicate with a conjunction body of the
    /// matching arity.
    fn locale_pred_conjuncts(
        &mut self,
        c_name: &str,
        pargs: &[IsaTerm],
        binders: &mut Vec<Binder>,
    ) -> Result<Option<Vec<Expr>>, TranslateError> {
        let Some(info) = self.poly_inst_registry.get(c_name).cloned() else {
            return Ok(None);
        };
        if info.conjuncts.is_empty() || info.arg_vars.len() != pargs.len() {
            return Ok(None);
        }
        let subst: Vec<((String, i64), IsaTerm)> = info
            .arg_vars
            .iter()
            .cloned()
            .zip(pargs.iter().cloned())
            .collect();
        let mut conjs: Vec<Expr> = Vec::with_capacity(info.conjuncts.len());
        for cj in &info.conjuncts {
            let specialized = subst_isa_vars(cj, &subst);
            conjs.push(self.embed_term(&specialized, binders)?);
        }
        Ok(Some(conjs))
    }

    /// As [`Self::locale_pred_conjuncts`], but returns each specialized conjunct
    /// as a `(ISA term, embedding)` pair — the ISA spelling is needed to recurse
    /// into a conjunct that is itself a registered locale predicate (its head
    /// const name + operand args key the nested `class.C_def` body), which the
    /// embedded def-const alone hides. The embedding is exactly what
    /// [`Self::locale_pred_conjuncts`] would yield, in lockstep — so a caller that
    /// only reads the `.1`s is byte-identical to the plain helper.
    fn locale_pred_conjuncts_pairs(
        &mut self,
        c_name: &str,
        pargs: &[IsaTerm],
        binders: &mut Vec<Binder>,
    ) -> Result<Option<Vec<(IsaTerm, Expr)>>, TranslateError> {
        let Some(info) = self.poly_inst_registry.get(c_name).cloned() else {
            return Ok(None);
        };
        if info.conjuncts.is_empty() || info.arg_vars.len() != pargs.len() {
            return Ok(None);
        }
        let subst: Vec<((String, i64), IsaTerm)> = info
            .arg_vars
            .iter()
            .cloned()
            .zip(pargs.iter().cloned())
            .collect();
        let mut out: Vec<(IsaTerm, Expr)> = Vec::with_capacity(info.conjuncts.len());
        for cj in &info.conjuncts {
            let specialized = subst_isa_vars(cj, &subst);
            let emb = self.embed_term(&specialized, binders)?;
            out.push((specialized, emb));
        }
        Ok(Some(out))
    }

    /// Extract a proof of `target` from `h : class.<c_name> pargs` by the
    /// impredicative `conj_def` projection, **recursively descending** any conjunct
    /// that is itself a registered locale predicate. A structured class's body is a
    /// right-associated `HOL.conj` chain of superclass locale predicates + its own
    /// axioms predicate, each of which may in turn be a conjunction (`class.C ≡
    /// class.super ∧ class.C_axioms`, `class.C_axioms ≡ axiom₀ ∧ …`), so a raw
    /// class axiom or a deep superclass predicate is a LEAF of that forest. We walk
    /// the `class.<c_name>` conjuncts, and for the one whose embedding equals
    /// `target` return its `And.left`/`And.right` extraction; otherwise, if a
    /// conjunct is a registered locale predicate, recurse into it with the proof of
    /// that conjunct as the new hypothesis. Returns `None` when `target` is not a
    /// reachable leaf (caller falls through). The kernel re-checks `value : type`
    /// δβ-reducing every def-const, so a wrong extraction rejects — never miscounts.
    pub(crate) fn extract_conjunct(
        &mut self,
        c_name: &str,
        pargs: &[IsaTerm],
        h: Expr,
        target: &Expr,
        binders: &mut Vec<Binder>,
    ) -> Result<Option<Expr>, TranslateError> {
        // The ISA-level conjuncts (for recursion into nested locale preds) and
        // their embeddings (for matching + the descent types), in lockstep.
        let Some(info) = self.poly_inst_registry.get(c_name).cloned() else {
            return Ok(None);
        };
        if info.conjuncts.is_empty() || info.arg_vars.len() != pargs.len() {
            return Ok(None);
        }
        let subst: Vec<((String, i64), IsaTerm)> = info
            .arg_vars
            .iter()
            .cloned()
            .zip(pargs.iter().cloned())
            .collect();
        let isa_conjs: Vec<IsaTerm> = info
            .conjuncts
            .iter()
            .map(|cj| subst_isa_vars(cj, &subst))
            .collect();
        let mut conjs: Vec<Expr> = Vec::with_capacity(isa_conjs.len());
        for cj in &isa_conjs {
            conjs.push(self.embed_term(cj, binders)?);
        }
        let n = conjs.len() - 1;
        // Rest types `t[i] = conj_def(Eᵢ, t[i+1])`, `t[n] = Eₙ`.
        let mut rest = vec![conjs[n].clone(); conjs.len()];
        for i in (0..n).rev() {
            rest[i] = conj_def(conjs[i].clone(), rest[i + 1].clone());
        }
        for k in 0..conjs.len() {
            // Descend the right spine `k` times, then project the left conjunct
            // (or take the residue for the last).
            let mut hk = h.clone();
            for (j, cj) in conjs.iter().enumerate().take(k) {
                hk = and_right(cj.clone(), rest[j + 1].clone(), hk);
            }
            let proof_k = if k < n {
                and_left(conjs[k].clone(), rest[k + 1].clone(), hk)
            } else {
                hk
            };
            if conjs[k] == *target {
                return Ok(Some(proof_k));
            }
            // **Schematic-instance discharge (r12).** A class axiom exported at
            // SPECIFIC schematic operands (`less ?x.0 ?y.0 ≡ …`, `times (plus ?a
            // ?b) ?c = …`) is the conjunct `∀x y. …` INSTANTIATED, so the exact
            // match above declines. Recover the operands and apply the conjunct
            // proof to them (see [`conjunct_instance_apply`]). The kernel
            // re-checks `proof_k ops : target`, so a wrong recovery rejects.
            if let Some(inst) = conjunct_instance_apply(&isa_conjs[k], &conjs[k], &proof_k, target)
            {
                return Ok(Some(inst));
            }
            // Recurse into a nested locale-predicate conjunct — type-class
            // (`Thy.class.c_axioms`) or plain (`Orderings.preordering` inside
            // `Orderings.ordering`, the G2 extension): any conjunct whose head is
            // itself a REGISTERED predicate with recorded conjuncts descends the
            // same way (the recursive call declines unregistered heads).
            let (sub_head, sub_args) = term_app_spine(strip_prop_wrappers(&isa_conjs[k]));
            if let IsaTerm::Const { n: sub_name, .. } = sub_head {
                if self.poly_inst_registry.contains_key(sub_name) {
                    let sub_args_owned: Vec<IsaTerm> =
                        sub_args.iter().map(|&a| a.clone()).collect();
                    let sub_name = sub_name.clone();
                    if let Some(p) =
                        self.extract_conjunct(&sub_name, &sub_args_owned, proof_k, target, binders)?
                    {
                        return Ok(Some(p));
                    }
                }
            }
        }
        Ok(None)
    }

    /// The **dual** of [`Self::prove_locale_projection`]: a locale-predicate
    /// CONSTRUCTION node whose conclusion is a registered locale predicate
    /// `class.C args` and whose leading `⟹` premises are EXACTLY the (specialized,
    /// flattened) conjuncts of `class.C`'s body, in order — e.g. `type_class α ⟹
    /// axiom₀ ⟹ … ⟹ axiomₙ ⟹ class.C_axioms args`, the `class.C_axioms.intro`
    /// that bundles a class's own assumptions into its axioms predicate. Under
    /// `instance_unfold` the conclusion embeds to the def-const `polyinst.C args`,
    /// δ= `conj_def(E₀', conj_def(…Eₙ'))`; the proof is the impredicative
    /// conjunction INTRO built from the premise hypotheses (`λC f. f h₀ hR`).
    /// FAITHFUL (real distinct premises/conclusion, never a tautology); the kernel
    /// re-checks `value : type` δβ-reducing the def-const, so a mismatch rejects.
    /// Gated on `instance_unfold` → strictly additive. Returns `None` when the
    /// shape does not match.
    pub(crate) fn prove_locale_construction(
        &mut self,
        thm: &IsaProvenTheorem,
    ) -> Result<Option<(Expr, Expr)>, TranslateError> {
        if !self.instance_unfold {
            return Ok(None);
        }
        let prop = &thm.prop;
        let mut prems: Vec<IsaTerm> = Vec::new();
        let mut cur = strip_prop_wrappers(prop);
        while let Some((lhs, rhs)) = split_pure_imp(cur) {
            prems.push(lhs.clone());
            cur = strip_prop_wrappers(rhs);
        }
        let m = prems.len();
        if m == 0 {
            return Ok(None);
        }
        // The conclusion must be a registered locale-predicate application
        // `class.C args` whose conjunction body has `n` conjuncts.
        let concl = strip_prop_wrappers(strip_leading_imps(prop));
        let (chead, cargs) = term_app_spine(concl);
        let IsaTerm::Const { n: c_name, .. } = chead else {
            return Ok(None);
        };
        // The conclusion head must be a registered predicate with recorded
        // conjuncts — type-class (`Thy.class.c`) or plain (`Finite_Set.
        // folding_on`, the G2 extension). [`Self::locale_pred_conjuncts`] below
        // is the real gate (registry membership + non-empty conjuncts + arity);
        // an explicit `.class.`-name check would only re-exclude the plain
        // locales this round admits.
        let c_name = c_name.clone();
        let cargs_owned: Vec<IsaTerm> = cargs.iter().map(|&a| a.clone()).collect();
        let mut binders: Vec<Binder> = Vec::new();
        let Some(conjs) = self.locale_pred_conjuncts(&c_name, &cargs_owned, &mut binders)? else {
            return Ok(None);
        };
        let n = conjs.len();
        // The TRAILING `n` premises must be exactly the conjuncts (the leading
        // `m - n` are sort hypotheses like `type_class`, unused).
        if m < n {
            return Ok(None);
        }
        // Embed the whole statement to the stored type and peel its `m` leading
        // `Pi` binders into fresh proof-binder fvars.
        let stored_ty = self.embed_term(prop, &mut binders)?;
        let mut cod = stored_ty.clone();
        let mut binder_doms: Vec<Expr> = Vec::with_capacity(m);
        let mut binder_fvars: Vec<FVarId> = Vec::with_capacity(m);
        for i in 0..m {
            let ExprKind::Pi(_, dom, c) = cod.kind() else {
                return Ok(None);
            };
            let fv = FVarId::new(0x9c05_0000 + i as u64);
            binder_doms.push((**dom).clone());
            binder_fvars.push(fv);
            cod = c.instantiate(&Expr::fvar(fv));
        }
        // The trailing `n` premise domains must match the conjuncts in order.
        for i in 0..n {
            if binder_doms[m - n + i] != conjs[i] {
                return Ok(None);
            }
        }
        // Build the impredicative conjunction intro from the trailing hypotheses.
        let hyps: Vec<Expr> = (m - n..m).map(|i| Expr::fvar(binder_fvars[i])).collect();
        let intro = conj_def_intro(&conjs, &hyps);
        let mut value = intro;
        for i in (0..m).rev() {
            value = Expr::lam(
                BinderInfo::Default,
                binder_doms[i].clone(),
                value.abstract_fvar(binder_fvars[i]),
            );
        }
        Ok(Some((value, stored_ty)))
    }

    /// Discharge ONE conclusion conjunct `dj` (ISA `isa_dj`, embedding
    /// `embedded_dj`) of a [`Self::prove_locale_to_locale`] reassembly, returning
    /// its proof or `None` (decline the whole build). Tries, in order:
    ///   1. a discharged premise whose embedded type IS `dj` → its bound var;
    ///   2. a vacuous `True` conjunct → `True.intro`;
    ///   3. projection out of a locale-predicate premise via
    ///      [`Self::extract_conjunct`] (exact / schematic-instance / premise-side
    ///      nested-descent match);
    ///   4. **conclusion-side reassembly** — when `dj` is ITSELF a registered
    ///      locale predicate (`partial_preordering le`, `preordering_axioms le lt`
    ///      inside `preordering le lt`; `class.C_axioms` inside `class.C`), whose
    ///      def-const body is a conjunction of sub-conjuncts NOT present as a unit
    ///      in any premise but each individually projectable: recurse on every
    ///      sub-conjunct and recombine with the impredicative `conj_def` INTRO.
    ///
    /// Step 4 is the additive lever the `class.preorder le lt ⟹ preordering le lt`
    /// shape (r-eta-operand s107054) needs: `preordering`'s conjuncts are the
    /// nested locale predicates `partial_preordering le` (δ= `refl ∧ trans`) and
    /// `preordering_axioms le lt` (δ= the `Not`-carrying strict-order axiom), while
    /// `class.preorder`'s body is the FLAT `strict ∧ refl ∧ trans`. `extract_conjunct`
    /// only descends nested predicates on the PREMISE side, so it cannot match a
    /// nested-predicate CONCLUSION conjunct against flat premise conjuncts; step 4
    /// rebuilds each nested predicate's body from those flat conjuncts. The kernel
    /// re-checks `conj_def_intro : embedded_dj` δβ-reducing the conclusion
    /// def-const, so a wrong reassembly is rejected — never miscounted. `depth`
    /// caps the (well-founded, strictly-decreasing) nesting recursion defensively.
    fn discharge_pred_conjunct(
        &mut self,
        isa_dj: &IsaTerm,
        embedded_dj: &Expr,
        prems: &[IsaTerm],
        binder_fvars: &[FVarId],
        binder_doms: &[Expr],
        binders: &mut Vec<Binder>,
        depth: usize,
    ) -> Result<Option<Expr>, TranslateError> {
        // 1. A discharged premise whose embedded type IS this conjunct.
        if let Some(pos) = binder_doms.iter().position(|d| d == embedded_dj) {
            return Ok(Some(Expr::fvar(binder_fvars[pos])));
        }
        // 2. A vacuous `True` conjunct.
        if *embedded_dj == Expr::const_str("True") {
            return Ok(Some(Expr::const_str("True.intro")));
        }
        // 3. Project it from a locale-predicate premise.
        for (idx, prem) in prems.iter().enumerate() {
            let (phead, pargs) = term_app_spine(strip_prop_wrappers(prem));
            let IsaTerm::Const { n: c_name, .. } = phead else {
                continue;
            };
            if !self.poly_inst_registry.contains_key(c_name) {
                continue;
            }
            let c_name = c_name.clone();
            let pargs_owned: Vec<IsaTerm> = pargs.iter().map(|&a| a.clone()).collect();
            let h = Expr::fvar(binder_fvars[idx]);
            if let Some(p) =
                self.extract_conjunct(&c_name, &pargs_owned, h, embedded_dj, binders)?
            {
                return Ok(Some(p));
            }
        }
        // 4. Conclusion-side reassembly: `dj` is itself a registered locale
        //    predicate whose sub-conjuncts must be rebuilt from the premises.
        if depth == 0 {
            return Ok(None);
        }
        let (dhead, dargs) = term_app_spine(strip_prop_wrappers(isa_dj));
        if let IsaTerm::Const { n: sub_name, .. } = dhead {
            if self.poly_inst_registry.contains_key(sub_name) {
                let sub_name = sub_name.clone();
                let dargs_owned: Vec<IsaTerm> = dargs.iter().map(|&a| a.clone()).collect();
                if let Some(pairs) =
                    self.locale_pred_conjuncts_pairs(&sub_name, &dargs_owned, binders)?
                {
                    let embedded: Vec<Expr> = pairs.iter().map(|(_, e)| e.clone()).collect();
                    let mut sub_proofs: Vec<Expr> = Vec::with_capacity(pairs.len());
                    for (isa_sub, emb_sub) in &pairs {
                        match self.discharge_pred_conjunct(
                            isa_sub,
                            emb_sub,
                            prems,
                            binder_fvars,
                            binder_doms,
                            binders,
                            depth - 1,
                        )? {
                            Some(p) => sub_proofs.push(p),
                            None => return Ok(None),
                        }
                    }
                    return Ok(Some(conj_def_intro(&embedded, &sub_proofs)));
                }
            }
        }
        Ok(None)
    }

    /// A **locale-to-locale** projection node
    /// (`[sort α ⟹] class.C args ⟹ … ⟹ pred_D dargs`) whose CONCLUSION is a
    /// registered locale predicate `pred_D` whose EVERY conjunct is derivable from
    /// a locale-predicate PREMISE by the impredicative `conj_def` projection.
    ///
    /// Unlike [`Self::prove_locale_projection`] — which extracts the conclusion as
    /// a SINGLE conjunct of one premise — this REASSEMBLES the conclusion
    /// predicate's whole conjunction from conjuncts projected out of the premises.
    /// It is the shape HOL exports for a **weaker structure predicate derived from
    /// a stronger class**: `class.preorder le lt ⟹ preordering le lt`,
    /// `class.semigroup_add (+) ⟹ semigroup (+)`, … where the weaker predicate
    /// (`preordering`/`semigroup`, a bare `bool`-result locale registered by the G2
    /// extension) shares the stronger class's axioms but is NOT itself a conjunct
    /// of it, so [`Self::prove_locale_projection`]'s `extract_conjunct(target =
    /// whole pred_D)` finds nothing and declines. Its recorded proof reconstructs
    /// the meta↔object congruence tower (`atomize_conj` + `Pure.combination`), which
    /// bottoms in the `expected=isabelle.def.HOL.Not got=FVar` / `expected=Eq
    /// got=Eq` wall — so keying on the statement shape sidesteps it.
    ///
    /// For each conjunct `Dⱼ` of `pred_D`'s δ-unfolded body we obtain a proof:
    ///   - a discharged premise whose embedded type equals `Dⱼ` → its bound var;
    ///   - `True` → `True.intro`;
    ///   - else a locale-predicate premise `class.Cᵢ argsᵢ` from which
    ///     [`Self::extract_conjunct`] yields `Dⱼ` (exact / schematic-instance /
    ///     nested-descent match).
    /// If every conjunct is discharged, the witness is the impredicative `conj_def`
    /// INTRO of the conjunct proofs, whose type δ= the conclusion def-const
    /// `polyinst.pred_D dargs`. Any undischarged conjunct declines the whole build
    /// (`None`) — never a partial witness. Gated on [`Self::instance_unfold`] →
    /// strictly additive; the kernel re-checks `value : type` δβ-reducing every
    /// def-const, so a wrong assembly is rejected — never miscounted. FAITHFUL
    /// (real distinct premise/conclusion predicates, never a `B = B` tautology;
    /// foundational `conj_def`/`And`/`True.intro` closure).
    pub(crate) fn prove_locale_to_locale(
        &mut self,
        thm: &IsaProvenTheorem,
    ) -> Result<Option<(Expr, Expr)>, TranslateError> {
        if !self.instance_unfold {
            return Ok(None);
        }
        let prop = &thm.prop;
        // Peel the leading `⟹` premises (the value's lambda binders).
        let mut prems: Vec<IsaTerm> = Vec::new();
        let mut cur = strip_prop_wrappers(prop);
        while let Some((lhs, rhs)) = split_pure_imp(cur) {
            prems.push(lhs.clone());
            cur = strip_prop_wrappers(rhs);
        }
        let m = prems.len();
        if m == 0 {
            return Ok(None);
        }
        // The conclusion must be a registered locale predicate `pred_D dargs` with
        // a recorded conjunction body.
        let concl = strip_prop_wrappers(strip_leading_imps(prop));
        let (dhead, dargs) = term_app_spine(concl);
        let IsaTerm::Const { n: d_name, .. } = dhead else {
            return Ok(None);
        };
        let d_name = d_name.clone();
        let dargs_owned: Vec<IsaTerm> = dargs.iter().map(|&a| a.clone()).collect();
        let mut binders: Vec<Binder> = Vec::new();
        let Some(d_pairs) =
            self.locale_pred_conjuncts_pairs(&d_name, &dargs_owned, &mut binders)?
        else {
            return Ok(None);
        };
        let d_conjs: Vec<Expr> = d_pairs.iter().map(|(_, e)| e.clone()).collect();
        // At least one premise must be a registered locale predicate (the source of
        // the projected conjuncts); else there is nothing to reassemble from and we
        // must not shadow the recorded-proof path.
        let has_locale_prem = prems.iter().any(|p| {
            let (ph, _) = term_app_spine(strip_prop_wrappers(p));
            matches!(ph, IsaTerm::Const { n, .. } if self.poly_inst_registry.contains_key(n))
        });
        if !has_locale_prem {
            return Ok(None);
        }
        // Embed the whole statement to the stored type; peel its `m` leading `Pi`
        // binders into fresh proof-binder fvars.
        let stored_ty = self.embed_term(prop, &mut binders)?;
        let mut cod = stored_ty.clone();
        let mut binder_doms: Vec<Expr> = Vec::with_capacity(m);
        let mut binder_fvars: Vec<FVarId> = Vec::with_capacity(m);
        for i in 0..m {
            let ExprKind::Pi(_, dom, c) = cod.kind() else {
                return Ok(None);
            };
            let fv = FVarId::new(0x9c06_0000 + i as u64);
            binder_doms.push((**dom).clone());
            binder_fvars.push(fv);
            cod = c.instantiate(&Expr::fvar(fv));
        }
        // Discharge every conclusion conjunct. Steps 1–3 (premise-identity /
        // `True` / [`Self::extract_conjunct`] out of a locale-predicate premise)
        // are exactly the historical discharge; a trailing step 4 (conclusion-side
        // reassembly of a nested-locale-predicate conjunct) is strictly additive —
        // it fires only where the old path returned `None` (declined the whole
        // theorem). See [`Self::discharge_pred_conjunct`].
        let mut proofs: Vec<Expr> = Vec::with_capacity(d_pairs.len());
        for (isa_dj, emb_dj) in &d_pairs {
            match self.discharge_pred_conjunct(
                isa_dj,
                emb_dj,
                &prems,
                &binder_fvars,
                &binder_doms,
                &mut binders,
                LOCALE_REASSEMBLE_MAX_DEPTH,
            )? {
                Some(p) => proofs.push(p),
                None => return Ok(None),
            }
        }
        // Reassemble the conclusion predicate's conjunction; wrap in premise lambdas.
        let mut value = conj_def_intro(&d_conjs, &proofs);
        for i in (0..m).rev() {
            value = Expr::lam(
                BinderInfo::Default,
                binder_doms[i].clone(),
                value.abstract_fvar(binder_fvars[i]),
            );
        }
        Ok(Some((value, stored_ty)))
    }

    /// If `ty` is a **registered class-membership** proposition — a def-const
    /// application `isabelle.def.<c>_class α extra… op₁…opₙ` whose head names a
    /// class in [`Self::class_registry`] — return its [`ClassDefInfo`] and the
    /// application arguments. `None` for `True`, a bare `Const`, a locale
    /// predicate, or any non-membership.
    fn class_membership_info(&self, ty: &Expr) -> Option<(ClassDefInfo, Vec<Expr>)> {
        let ExprKind::Const(def_name, _) = ty.get_app_fn().kind() else {
            return None;
        };
        let def_name = def_name.to_string();
        let info = self
            .class_registry
            .values()
            .find(|i| i.def_name == def_name)?
            .clone();
        let args: Vec<Expr> = ty.get_app_args().into_iter().cloned().collect();
        Some((info, args))
    }

    /// Whether `ty` is a registered (non-`True`) class-membership proposition —
    /// the gate for the OfClass→membership projection (a `True` expectation keeps
    /// `True.intro`, byte-identical).
    pub(crate) fn is_registered_class_membership(&self, ty: &Expr) -> bool {
        self.class_membership_info(ty).is_some()
    }

    /// β-reduce a registered class membership `ty`'s def-const to its concrete
    /// class **body** `B` — the object-level `And`/`True` tree of the superclass
    /// memberships + the class's own axioms predicate (exactly the tree the kernel
    /// obtains by δ-unfolding `ty`, since [`ClassDefInfo::def_value`] IS the
    /// registered `Definition`'s value). Returns `None` when `ty` is not a
    /// registered membership or the metadata's binder count does not match the
    /// applied arguments (stale registry → decline rather than mis-build).
    fn class_membership_body(&self, ty: &Expr) -> Option<Expr> {
        let (info, args) = self.class_membership_info(ty)?;
        let mut body = info.def_value.clone();
        for arg in &args {
            let ExprKind::Lam(_, _, b) = body.kind() else {
                return None;
            };
            body = b.instantiate(arg);
        }
        Some(body)
    }

    /// Project a proof of `target` (a class-membership proposition) out of a
    /// hypothesis `h : h_ty`, where `h_ty` is a registered class membership (or an
    /// object-level `And` node reached while descending one) whose δ-unfolded body
    /// CONTAINS `target` as a (possibly nested) conjunct. Builds the
    /// `And.left`/`And.right` projection path (`conjunctionD1`/`D2`), δ-unfolding
    /// each membership conjunct on the way down. Returns `None` when `target` is
    /// not a reachable conjunct. The kernel re-checks `proof : target` (δ-unfolding
    /// every membership def-const), so a wrong projection is rejected — never
    /// miscounted.
    fn project_membership_conjunct(
        &self,
        h: Expr,
        h_ty: &Expr,
        target: &Expr,
        depth: usize,
    ) -> Option<Expr> {
        if h_ty == target {
            return Some(h);
        }
        if depth == 0 {
            return None;
        }
        // An object-level `And P Q` node → project each side and recurse (`h : And
        // P Q` gives `And.left P Q h : P` / `And.right P Q h : Q`).
        if let Some((p, q)) = as_and_node(h_ty) {
            let (p, q) = (p.clone(), q.clone());
            let hp = and_left_obj(p.clone(), q.clone(), h.clone());
            if let Some(r) = self.project_membership_conjunct(hp, &p, target, depth - 1) {
                return Some(r);
            }
            let hq = and_right_obj(p, q.clone(), h);
            return self.project_membership_conjunct(hq, &q, target, depth - 1);
        }
        // A registered class membership → δ-unfold to its `And` body and recurse
        // with the SAME hypothesis (`h : h_ty` is definitionally `h : body`).
        let body = self.class_membership_body(h_ty)?;
        self.project_membership_conjunct(h, &body, target, depth - 1)
    }

    /// **OfClass→membership superclass projection** — the faithful `conjunctionD1`
    /// discharge of an `IsaProof::OfClass` sort-witness leaf under a bidirectional
    /// expectation. When `expected` is a non-`True` registered class-membership
    /// predicate and an in-scope PROOF hypothesis carries a SUBCLASS membership
    /// whose def-body conjunction contains `expected` as a superclass conjunct,
    /// return the `And.left`/`And.right` projection of `expected` out of that
    /// hypothesis — instead of the vacuous `True.intro` (which kernel-rejects at a
    /// real-membership expectation, the residual `expected=<c>_class got=True`
    /// blocker of the `contains-free-var` Orderings family). Returns `None` (caller
    /// keeps `True.intro`, byte-identical) when `expected` is not a registered
    /// membership or no in-scope hypothesis projects it.
    pub(crate) fn project_ofclass_membership(
        &self,
        expected: &Expr,
        binders: &[Binder],
    ) -> Option<Expr> {
        // A/B no-preemption toggle (default ON — the production behaviour): a test
        // flips it OFF in-thread to measure the baseline and assert the anchor
        // closures' KV count is identical either way. Zero-cost `true` read
        // otherwise.
        if !ofclass_proj_enabled() {
            return None;
        }
        // Gate: fire ONLY when the expected type is a non-`True` registered
        // class-membership predicate (`True`-expectation OfClass leaves keep
        // `True.intro`, exactly as before).
        if !self.is_registered_class_membership(expected) {
            return None;
        }
        // Scan the in-scope proof binders (innermost first) for a class-membership
        // hypothesis from which `expected` projects. The clean bvar depth counts
        // only the binders that emit a clean lambda (an elided sort-hyp slot
        // occupies a `PBound` index but no bvar depth), mirroring
        // [`proof_bvar_slot`].
        let mut depth: u32 = 0;
        for b in binders.iter().rev() {
            if matches!(b.kind, BKind::Proof) && self.is_registered_class_membership(&b.ty) {
                if let Some(proof) = self.project_membership_conjunct(
                    Expr::bvar(depth),
                    &b.ty,
                    expected,
                    MEMBERSHIP_PROJ_MAX_DEPTH,
                ) {
                    return Some(proof);
                }
            }
            if !matches!(b.kind, BKind::ElidedSortHyp) {
                depth += 1;
            }
        }
        None
    }
}
