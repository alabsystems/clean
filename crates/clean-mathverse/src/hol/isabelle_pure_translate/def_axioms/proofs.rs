// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-builder helpers for the Isabelle Pure definitional-axiom translator
//! (`prop_lam`/`prop_pi`, `propext_iff`, the Pure-conjunction and classical
//! `…_first` arms, `def_unfold_body`, `prove_not_atomize`, …). Moved verbatim
//! from the original single-file `def_axioms` module; behaviour is byte-identical.

use std::collections::BTreeMap;

use clean_kernel::expr::FVarId;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr};

use super::super::super::isabelle_pure::IsaProvenTheorem;
use super::super::*;
/// `λ(x:Prop). body[x]` built via a fresh fvar (no manual de Bruijn).
pub(crate) fn prop_lam(id: u64, body: impl FnOnce(Expr) -> Expr) -> Expr {
    let fv = FVarId::new(id);
    let b = body(Expr::fvar(fv));
    Expr::lam(BinderInfo::Default, Expr::prop(), b.abstract_fvar(fv))
}

/// `∀(x:Prop). body[x]` built via a fresh fvar.
pub(crate) fn prop_pi(id: u64, body: impl FnOnce(Expr) -> Expr) -> Expr {
    let fv = FVarId::new(id);
    let b = body(Expr::fvar(fv));
    Expr::pi(BinderInfo::Default, Expr::prop(), b.abstract_fvar(fv))
}

/// Build a `propext`-based proof of `@Eq Prop a b` from the two implications
/// `mp : a → b` and `mpr : b → a`. Upstream `propext` is Iff-shaped
/// (`{a b : Prop} → (a ↔ b) → a = b`), so the bridge is
/// `propext a b (Iff.intro a b mp mpr)`.
pub(crate) fn propext_iff(a: Expr, b: Expr, mp: Expr, mpr: Expr) -> Expr {
    let iff = Expr::apps(
        Expr::const_str("Iff.intro"),
        [a.clone(), b.clone(), mp, mpr],
    );
    Expr::apps(Expr::const_str("propext"), [a, b, iff])
}

/// The kernel declaration name of the registered clean `Definition` for a
/// monomorphic HOL connective (`isabelle.def.HOL.conj`, …), or `None` for a name
/// we do not encode. Embedding `Const HOL.conj` as this *definition's const*
/// (rather than inlining [`connective_encoding`] at each occurrence) keeps the
/// connective **consistent** wherever it appears — abstract (a `Pure.all`-bound
/// `Bound`) and concrete (`Const HOL.conj`) occurrences now share one head symbol,
/// so the connective `_def` proofs no longer hit a fold/unfold mismatch. The
/// kernel unfolds the definition to the encoding via defeq only when needed.
/// The registered `HOL.conj` definition const (`isabelle.def.HOL.conj`) as a
/// clean `Expr`, used by the set-op encodings (`Bex`/`image`) so a `∧` they build
/// shares the same defeq-unfolding head as every other connective occurrence.
pub(crate) fn conj_def_const() -> Expr {
    // `connective_def_name("HOL.conj")` is `Some("isabelle.def.HOL.conj")` by
    // construction; fall back to the literal name rather than panic.
    Expr::const_str(connective_def_name("HOL.conj").unwrap_or("isabelle.def.HOL.conj"))
}

/// The registered `HOL.disj` definition const (`isabelle.def.HOL.disj`) as a clean
/// `Expr`, used by the `Set.insert` encoding so a `∨` it builds shares the same
/// defeq-unfolding head as every other `HOL.disj` occurrence (the RHS of
/// `insert_compr`). Mirrors [`conj_def_const`].
pub(crate) fn disj_def_const() -> Expr {
    Expr::const_str(connective_def_name("HOL.disj").unwrap_or("isabelle.def.HOL.disj"))
}

/// Statement-level proof attempted **before** translating the recorded proof:
/// only the pure premise-identity / conclusion-reflexivity arms (no definitional
/// unfold). Snapshots `ctx`'s discovered parameters and restores them if no proof
/// is produced, so a non-matching probe leaves no phantom binders behind. The
/// kernel re-checks any produced term, so this is soundness-neutral.
pub(crate) fn prove_from_premises_first(
    ctx: &mut Ctx,
    thm: &IsaProvenTheorem,
) -> Result<Option<Expr>, TranslateError> {
    let snap_types = ctx.type_params.clone();
    let snap_terms = ctx.term_params.clone();
    let snap_hyps = ctx.hyp_params.clone();
    let r = ctx.prove_from_premises_inner(&thm.prop, false)?;
    if r.is_none() {
        ctx.type_params = snap_types;
        ctx.term_params = snap_terms;
        ctx.hyp_params = snap_hyps;
    }
    Ok(r)
}

/// Statement-level proof of the Pure **meta-conjunction** rules
/// (`Pure.conjunctionD1`/`D2`/`I`), attempted before the recorded proof. Their
/// recorded proofs bottom out in the unmappable `Pure.conjunction_def` def-raw
/// chain, but under our embedding `Pure.conjunction → And` they are *exactly*
/// clean's `And.left`/`And.right`/`And.intro`. Keying on the well-known theorem
/// name, we build the direct proof; the kernel re-checks it against the embedded
/// statement, so a mis-key is rejected (never miscounted). Verifying these here
/// lands them in the closure, so the (very many) `c_class.super`/`.axioms`/
/// `.intro` projections that reference them as `PThm`s resolve.
pub(crate) fn prove_pure_conjunction_rule(
    ctx: &mut Ctx,
    thm: &IsaProvenTheorem,
) -> Result<Option<Expr>, TranslateError> {
    let (head, arity) = match thm.name.as_str() {
        "Pure.conjunctionD1" => ("And.left", 1usize),
        "Pure.conjunctionD2" => ("And.right", 1),
        "Pure.conjunctionI" => ("And.intro", 2),
        _ => return Ok(None),
    };
    let snap_types = ctx.type_params.clone();
    let snap_terms = ctx.term_params.clone();
    let snap_hyps = ctx.hyp_params.clone();
    // Embed the statement so the two propositional parameters `A`, `B` (the
    // schematic `Var`s) are discovered and quantified by the final wrap; the body
    // references them as the embedded `And` operands.
    let mut binders: Vec<Binder> = Vec::new();
    let prop = ctx.embed_term(&thm.prop, &mut binders)?;
    // Pull `A`, `B` out of the embedded conclusion: the statement is
    // `And A B → A` / `And A B → B` (D1/D2) or `A → B → And A B` (I); in all
    // cases the embedding contains an `And A B` sub-term whose operands are `A`,
    // `B`. Recover them from the `And`-application.
    let Some((a_e, b_e)) = find_and_operands(&prop) else {
        ctx.type_params = snap_types;
        ctx.term_params = snap_terms;
        ctx.hyp_params = snap_hyps;
        return Ok(None);
    };
    // Build `head A B <hyp(s)>` under `arity` enclosing `fun (h:_) =>` binders.
    // Their domain types come from the statement's leading `Pure.imp` premises;
    // since `translate_theorem` wraps the discovered params, the simplest robust
    // construction is a closed lambda over the premises whose types are read from
    // the embedded statement's leading arrows.
    let mut prem_tys: Vec<Expr> = Vec::new();
    let mut cur = &prop;
    for _ in 0..arity {
        match cur.kind() {
            clean_kernel::expr::ExprKind::Pi(_, dom, cod) => {
                prem_tys.push((**dom).clone());
                cur = cod;
            }
            _ => {
                ctx.type_params = snap_types;
                ctx.term_params = snap_terms;
                ctx.hyp_params = snap_hyps;
                return Ok(None);
            }
        }
    }
    // body: head A B  applied to the bound hyps (innermost bound = last premise).
    let mut body = Expr::apps(Expr::const_str(head), [a_e, b_e]);
    for j in 0..arity {
        body = Expr::app(body, Expr::bvar((arity - 1 - j) as u32));
    }
    // Wrap the premise binders (outermost-first).
    let mut e = body;
    for ty in prem_tys.into_iter().rev() {
        e = Expr::lam(BinderInfo::Default, ty, e);
    }
    Ok(Some(e))
}

/// Find an `And a b` sub-application in an embedded `Expr`, returning `(a, b)`.
pub(crate) fn find_and_operands(e: &Expr) -> Option<(Expr, Expr)> {
    use clean_kernel::expr::ExprKind;
    if let ExprKind::App(f, b) = e.kind() {
        if let ExprKind::App(g, a) = f.kind() {
            if let ExprKind::Const(n, _) = g.kind() {
                if *n == Name::from_string("And") {
                    return Some(((**a).clone(), (**b).clone()));
                }
            }
        }
    }
    // Recurse into sub-expressions.
    match e.kind() {
        ExprKind::App(f, a) => find_and_operands(f).or_else(|| find_and_operands(a)),
        ExprKind::Pi(_, d, c) | ExprKind::Lam(_, d, c) => {
            find_and_operands(d).or_else(|| find_and_operands(c))
        }
        _ => None,
    }
}

/// `λ(x:dom). body[x]` built via a fresh fvar (no manual de Bruijn), the
/// arbitrary-domain sibling of [`prop_lam`]. The fvar `id` need only be distinct
/// within the term (it is abstracted away immediately).
fn lam_fv(id: u64, dom: Expr, body: impl FnOnce(Expr) -> Expr) -> Expr {
    let fv = FVarId::new(id);
    let b = body(Expr::fvar(fv));
    Expr::lam(BinderInfo::Default, dom, b.abstract_fvar(fv))
}

/// If `e` is a top-level application `Const c $ a $ b`, return `(a, b)`.
fn bin_const_app(e: &Expr, c: &str) -> Option<(Expr, Expr)> {
    use clean_kernel::expr::ExprKind;
    let ExprKind::App(f, b) = e.kind() else {
        return None;
    };
    let ExprKind::App(g, a) = f.kind() else {
        return None;
    };
    if matches!(g.kind(), ExprKind::Const(n, _) if *n == Name::from_string(c)) {
        Some(((**a).clone(), (**b).clone()))
    } else {
        None
    }
}

/// Peel the leading **non-dependent** `Pi` (`→`) premises off an embedded
/// statement `Expr`, returning `(premise_domains, conclusion)`. A `Pi` is
/// peeled only when its codomain does not reference the bound variable
/// (`!has_loose_bvar(0)`) — so the recovered domains/conclusion are all
/// closed and usable verbatim (every atom in these HOL logic laws is an
/// fvar param). Dependent binders (a genuine `⋀x. …` quantifier) stop the walk.
fn peel_arrow_premises(prop: &Expr) -> (Vec<Expr>, Expr) {
    use clean_kernel::expr::ExprKind;
    let mut doms = Vec::new();
    let mut cur = prop.clone();
    loop {
        let next = match cur.kind() {
            ExprKind::Pi(_, dom, cod) if !cod.has_loose_bvar(0) => {
                doms.push((**dom).clone());
                (**cod).clone()
            }
            _ => break,
        };
        cur = next;
    }
    (doms, cur)
}

/// Statement-level proof of the basic HOL **connective introduction / elimination
/// laws** at the meta level — `disjI1`/`disjI2`/`conjI`/`FalseE` and their many
/// anonymous derivation-box twins. Each embeds to a premise chain ending in an
/// impredicative connective def-const:
/// ```text
///   P ⟹ P ∨ Q                (disjI1)   →  disj_def P Q ≡ ∀C.(P→C)→(Q→C)→C
///   Q ⟹ P ∨ Q                (disjI2)
///   P ⟹ Q ⟹ P ∧ Q           (conjI)    →  conj_def P Q ≡ ∀C.(P→Q→C)→C
///   False ⟹ C                 (FalseE)   →  False_def     ≡ ∀C. C
/// ```
/// Under the connective embedding the conclusion is the reducible def-const
/// (`isabelle.def.HOL.disj`/`conj`/`False`), so each law has a **direct
/// impredicative inhabitant** — a closed lambda that supplies the encoding's
/// continuation, e.g. disjI1 is `λ(hp:P)(C:Prop)(f:P→C)(g:Q→C). f hp`. These are
/// FOUNDATIONAL (pure λ-terms, no axioms) and FAITHFUL: the operands are read
/// from the SAME embedded `prop` that becomes the stored theorem type, so the
/// proof's inferred type is `P → disj_def P Q` — bit-identical to the stored
/// type, which the kernel re-checks δ-unfolding the reducible def-const (a
/// mis-shape is rejected, never miscounted).
///
/// The recorded proofs of these laws reconstruct the connective *definition* via
/// an `equal_elim` congruence tower whose generic-reference legs leak an
/// unsolved schematic (`Pi[1]->Sort` vs `Pi[1]->FVar` — the r10 phantom-parameter
/// wall), so the recorded path rejects; keying on the statement shape sidesteps
/// the tower entirely (the r11 definitional-discharge pattern). These laws are
/// heavily depended upon (`FalseE` alone sole-blocks thousands), so landing them
/// unblocks a large cascade.
///
/// Returns `None` on any shape surprise so the caller keeps the recorded-proof
/// path; SHAPE-gated (exact def-const conclusion + matching premise operands),
/// never a name gate — it catches the anonymous box twins too.
pub(crate) fn prove_connective_law(prop: &Expr) -> Option<Expr> {
    use clean_kernel::expr::ExprKind;
    // Distinct fvar ids for the local binders (abstracted away immediately).
    const HP: u64 = 0x5f20_0001;
    const HQ: u64 = 0x5f20_0002;
    const CC: u64 = 0x5f20_0003;
    const FF: u64 = 0x5f20_0004;
    const GG: u64 = 0x5f20_0005;
    let (prems, concl) = peel_arrow_premises(prop);
    // disjI: conclusion `disj_def A B`.
    if let Some((a, b)) = bin_const_app(&concl, "isabelle.def.HOL.disj") {
        if prems.len() != 1 {
            return None;
        }
        let p = &prems[0];
        // λ(h:P). λ(C:Prop). λ(f:A→C). λ(g:B→C). f h   (disjI1, P ≡ A)
        //                                       g h   (disjI2, P ≡ B)
        let (dom, use_left) = if *p == a {
            (a.clone(), true)
        } else if *p == b {
            (b.clone(), false)
        } else {
            return None;
        };
        let (a2, b2) = (a.clone(), b.clone());
        return Some(lam_fv(HP, dom, move |h| {
            lam_fv(CC, Expr::prop(), move |c| {
                let (fa, gb) = (Expr::arrow(a2, c.clone()), Expr::arrow(b2, c));
                lam_fv(FF, fa, move |f| {
                    lam_fv(GG, gb, move |g| Expr::app(if use_left { f } else { g }, h))
                })
            })
        }));
    }
    // conjI: conclusion `conj_def A B`, premises [A, B].
    if let Some((a, b)) = bin_const_app(&concl, "isabelle.def.HOL.conj") {
        if prems.len() != 2 || prems[0] != a || prems[1] != b {
            return None;
        }
        // λ(hp:A). λ(hq:B). λ(C:Prop). λ(f:A→B→C). f hp hq
        let (a2, b2) = (a.clone(), b.clone());
        return Some(lam_fv(HP, a, move |hp| {
            lam_fv(HQ, b, move |hq| {
                lam_fv(CC, Expr::prop(), move |c| {
                    let f_ty = Expr::arrow(a2, Expr::arrow(b2, c));
                    lam_fv(FF, f_ty, move |f| Expr::apps(f, [hp, hq]))
                })
            })
        }));
    }
    // FalseE: single premise `False_def` (≡ ∀C.C), arbitrary conclusion.
    if prems.len() == 1 {
        if let ExprKind::Const(n, _) = prems[0].kind() {
            if *n == Name::from_string("isabelle.def.HOL.False") {
                // λ(h:False). h C   (h : ∀C.C applied to the conclusion prop)
                let false_dom = prems[0].clone();
                return Some(lam_fv(HP, false_dom, move |h| Expr::app(h, concl)));
            }
        }
    }
    // Connective ELIMINATION laws — `conjunct1`/`conjunct2`/`conjE`/`disjE`
    // (and `conj_comm`/`disj_comm`/`disj_forward`) plus their anonymous
    // derivation-box twins. Here the connective is a PREMISE (the reducible
    // `isabelle.def.HOL.conj`/`disj` def-const applied to two operands), and the
    // conclusion follows by APPLYING the impredicative-encoding hypothesis to the
    // goal and the case/selector proofs. [`connective_elim_body`] builds exactly
    // that body under `n = prems.len()` premise binders (de Bruijn indices); we
    // wrap it in the premise lambdas here, byte-identically to
    // [`Ctx::prove_from_premises_inner`].
    //
    // These are the SAME `equal_elim` congruence-tower family as the intro laws
    // above, so their recorded proofs reconstruct the connective *definition* and
    // translate to a term the kernel rejects (`Pi[1]->Sort` vs `Pi[1]->FVar`, the
    // r10 phantom-parameter wall). The existing `connective_elim_body` arm lives
    // ONLY on the POST-translate `prove_from_premises` fallback, which is reached
    // only when `translate_proof` returns `Err` — and these laws' recorded proofs
    // return `Ok(rejecting-term)` instead, so that arm never fires for them.
    // Hoisting the SAME body builder to this PRE-translate arm (alongside the
    // intro laws) is what catches them. Foundational (pure λ-terms, no axioms) and
    // SHAPE-gated on the def-const connective premise; the kernel re-checks the
    // built term δ-unfolding the connective definition, so a mis-shape is rejected
    // — never miscounted. Strictly additive: the intro/FalseE arms above already
    // returned on their shapes, and this fires only when a `conj`/`disj` def-const
    // *premise* is present (never on an intro law, whose connective is the
    // conclusion). `conjunct1`/`conjE` alone gate large downstream cascades.
    if !prems.is_empty() {
        if let Some(body) = connective_elim_body(&prems, &concl, prems.len()) {
            let mut e = body;
            for ty in prems.into_iter().rev() {
                e = Expr::lam(BinderInfo::Default, ty, e);
            }
            return Some(e);
        }
    }
    None
}

/// Statement-level proof of Pure's meta-conjunction **definition** axiom
/// `Pure.conjunction_def`:
/// ```text
/// Pure.conjunction A B ≡ (⋀C. (A ⟹ B ⟹ C) ⟹ C)
/// ```
/// Its recorded proof is the bare unmapped `Pure.conjunction_def` axm (a
/// `def_raw` definitional leaf), so the recorded path fails. Under our embedding
/// `Pure.conjunction → And`, `Pure.all → Π`, `Pure.imp → →`, the statement embeds
/// to `@Eq Prop (And A B) E` where `E = ∀(C:Prop). (A → B → C) → C` is the
/// impredicative conjunction encoding. `And A B` and `E` are *propositionally
/// equal but NOT definitionally equal* (`And` is the inductive conjunction), so a
/// reflexive `Eq.refl` would NOT verify — instead we prove the genuine equality by
/// `propext` of the constructive isomorphism (foundational closure: `And.intro` /
/// `And.left` / `And.right` + `propext`):
///   - forward  `And A B → E`:  `λ(h:And A B)(C:Prop)(k:A→B→C). k (And.left A B h) (And.right A B h)`
///   - backward `E → And A B`:  `λ(h:E). h (And A B) (And.intro A B)`
/// The kernel re-checks the produced `propext … : @Eq Prop (And A B) E` against the
/// embedded statement, so a mis-shaped statement is rejected — never miscounted.
/// `Pure.conjunction` is the conjunction used in EVERY structured type-class
/// `…c_class_def` body, so landing this def in the closure resolves the PThm
/// references its dependents carry.
///
/// Takes the **already-embedded** statement `prop` (the exact `Expr` that becomes
/// the stored theorem type), NOT a re-embed of `thm.prop`: the proof's `propext`
/// operands `(And A B, E)` are read from THIS `prop`, so the proof's inferred type
/// is `@Eq Prop (And A B) E` — bit-identical to the stored type. (Re-embedding
/// inside this function risks a different embedding of the impredicative RHS, which
/// is exactly the type mismatch a faithful arm must avoid.)
pub(crate) fn prove_pure_conjunction_def(name: &str, prop: &Expr) -> Option<Expr> {
    if name != "Pure.conjunction_def" {
        return None;
    }
    // The embedded statement must be `@Eq Prop (And A B) E`. Decompose it.
    let (_alpha, lhs, e, _levels) = eq_app_three(prop)?;
    let (a_e, b_e) = and_app_operands(&lhs)?;
    let and_ab = lhs.clone();
    // forward `mp : And A B → E`. Under binders `h:And A B` (bvar2), `C:Prop`
    // (bvar1), `k:A→B→C` (bvar0): `k (And.left A B h) (And.right A B h)`.
    // `k`'s domain `A → B → C` is built at the depth where the context is `[h, C]`
    // (h=bvar1, C=bvar0). Each `Expr::arrow` introduces a fresh non-lifting `Pi`
    // binder WITHOUT shifting the body, so inside `arrow(A, arrow(B, <C>))` the
    // reference to the outer `C` sits under TWO arrow binders → `bvar(0 + 2)`.
    // (`A`/`B` are param fvars, unaffected by binder depth.)
    let a_to_b_to_c = Expr::arrow(a_e.clone(), Expr::arrow(b_e.clone(), Expr::bvar(2)));
    let mp_body = {
        let h = Expr::bvar(2);
        let left = Expr::apps(
            Expr::const_str("And.left"),
            [a_e.clone(), b_e.clone(), h.clone()],
        );
        let right = Expr::apps(Expr::const_str("And.right"), [a_e.clone(), b_e.clone(), h]);
        // k (= bvar0) applied to the two projections.
        Expr::apps(Expr::bvar(0), [left, right])
    };
    let mp = Expr::lam(
        BinderInfo::Default,
        and_ab.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::lam(BinderInfo::Default, a_to_b_to_c, mp_body),
        ),
    );
    // backward `mpr : E → And A B`. `h (And A B) (And.intro A B)`. `h` is bvar0.
    let intro = Expr::apps(Expr::const_str("And.intro"), [a_e.clone(), b_e.clone()]);
    let mpr_body = Expr::apps(Expr::bvar(0), [and_ab.clone(), intro]);
    let mpr = Expr::lam(BinderInfo::Default, e.clone(), mpr_body);
    Some(propext_iff(and_ab, e, mp, mpr))
}

/// Statement-level proof of HOL's **conjunction atomization** rule
/// `HOL.atomize_conj` (and its anonymous derivation-box twins, which carry the
/// same statement with box-internal `Free` spellings — hence the SHAPE gate,
/// not a name gate):
/// ```text
/// (A &&& B) ≡ Trueprop (A ∧ B)
/// ```
/// Under the embedding `Pure.conjunction → And` (the inductive conjunction)
/// and `HOL.conj → isabelle.def.HOL.conj` (the impredicative-encoding
/// def-const), the statement embeds to `@Eq Prop (And A B) (conj_def A B)` —
/// two DISTINCT operands (never a `B=B` tautology) that are *propositionally
/// but not definitionally* equal, so no reflexive arm can land it and its
/// recorded proof bottoms out in the unmappable `atomize_conj`-family box
/// chain. Proved exactly like [`prove_pure_conjunction_def`]: `propext` of the
/// constructive isomorphism (`And.intro`/`.left`/`.right` — foundational
/// closure), with the RHS taken verbatim from the embedded statement (the
/// kernel δ-unfolds `conj_def A B` to the `∀C.(A→B→C)→C` encoding when
/// checking the two directions). The operands are read from the SAME embedded
/// `prop` that becomes the stored type, so the proof's inferred type is
/// bit-identical; a mis-shape is kernel-rejected — never miscounted.
/// `atomize_conj` is the meta↔object conjunction bridge every locale-predicate
/// projection chain (`class.order → class.preorder`, …) routes through, so
/// landing it unblocks the OFCLASS `intro_of_class` family for every class
/// with a structured superclass.
pub(crate) fn prove_atomize_conj(prop: &Expr) -> Option<Expr> {
    use clean_kernel::expr::ExprKind;
    let (_alpha, lhs, rhs, _levels) = eq_app_three(prop)?;
    let (a_e, b_e) = and_app_operands(&lhs)?;
    // RHS must be the `isabelle.def.HOL.conj` def-const applied to the SAME
    // embedded operands (`conj_def A B`).
    let ExprKind::App(f, b2) = rhs.kind() else {
        return None;
    };
    let ExprKind::App(g, a2) = f.kind() else {
        return None;
    };
    let ExprKind::Const(n, _) = g.kind() else {
        return None;
    };
    if *n != Name::from_string("isabelle.def.HOL.conj") || **a2 != a_e || **b2 != b_e {
        return None;
    }
    let and_ab = lhs.clone();
    // forward `mp : And A B → conj_def A B` (defeq `∀C.(A→B→C)→C`); see
    // [`prove_pure_conjunction_def`] for the binder-depth accounting.
    let a_to_b_to_c = Expr::arrow(a_e.clone(), Expr::arrow(b_e.clone(), Expr::bvar(2)));
    let mp_body = {
        let h = Expr::bvar(2);
        let left = Expr::apps(
            Expr::const_str("And.left"),
            [a_e.clone(), b_e.clone(), h.clone()],
        );
        let right = Expr::apps(Expr::const_str("And.right"), [a_e.clone(), b_e.clone(), h]);
        Expr::apps(Expr::bvar(0), [left, right])
    };
    let mp = Expr::lam(
        BinderInfo::Default,
        and_ab.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::lam(BinderInfo::Default, a_to_b_to_c, mp_body),
        ),
    );
    // backward `mpr : conj_def A B → And A B` — `h (And A B) (And.intro A B)`.
    let intro = Expr::apps(Expr::const_str("And.intro"), [a_e.clone(), b_e.clone()]);
    let mpr_body = Expr::apps(Expr::bvar(0), [and_ab.clone(), intro]);
    let mpr = Expr::lam(BinderInfo::Default, rhs.clone(), mpr_body);
    Some(propext_iff(and_ab, rhs.clone(), mp, mpr))
}

/// Statement-level proof of Pure's sort-constraint **definition** axiom
/// `Pure.sort_constraint_def`:
/// ```text
/// Pure.sort_constraint TYPE('a) ≡ Pure.term TYPE('a)
/// ```
/// Its recorded proof is the bare unmapped `Pure.sort_constraint_def` axm. Under
/// the embedding the LHS `Pure.sort_constraint TYPE('a)` is a **sort constraint**
/// ([`is_class_app`]), which `embed_term` erases to the vacuous `True` (like
/// `OFCLASS`), while the RHS `Pure.term TYPE('a)` embeds (via the `Pure.term`
/// def-const routing) to a term δβ-equal to the meta-truth `∀A. A → A`. So the
/// statement embeds to `@Eq Prop True R` with `R` the (def-const-unfolded) marker
/// application. `True` and `R` are *propositionally equal but NOT definitionally
/// equal* (both are inhabited truths, but `True = (λx.x)=(λx.x)` is not defeq to
/// `∀A. A → A`), so a reflexive `Eq.refl` would NOT verify — we prove the genuine
/// equality by `propext` of the trivial `True ↔ R` isomorphism (both sides
/// inhabited; foundational closure `propext` + `True.intro`):
///   - forward  `True → R`:  `λ(_:True)(A:Prop)(h:A). h`   (an inhabitant of `∀A. A → A`)
///   - backward `R → True`:  `λ(_:R). True.intro`
/// The `propext` operands `(True, R)` are read from the SAME embedded `prop` that
/// becomes the stored type, so the proof's inferred type is `@Eq Prop True R` —
/// bit-identical and FAITHFUL (the real `sort_constraint = term`, never a `B=B`
/// tautology). The kernel re-checks it (defeq-reducing `R` to `∀A. A → A` when
/// type-checking the `mp` body), so a mis-shape is rejected — never miscounted.
pub(crate) fn prove_sort_constraint_def(name: &str, prop: &Expr) -> Option<Expr> {
    if name != "Pure.sort_constraint_def" {
        return None;
    }
    // The embedded statement must be `@Eq Prop lhs rhs` with `lhs` the erased
    // `True` and `rhs` the `Pure.term`-def-const application.
    let (_alpha, lhs, rhs, _levels) = eq_app_three(prop)?;
    // Confirm the LHS is exactly the erased-sort-constraint `True` const, so this
    // arm only ever fires on the genuine `sort_constraint_def` shape.
    if !matches!(lhs.kind(), clean_kernel::expr::ExprKind::Const(n, _) if *n == Name::from_string("True"))
    {
        return None;
    }
    // forward `mp : True → R`. Under `_:True` (bvar2, unused), `A:Prop` (bvar1),
    // `h:A` (bvar0): the body is `h`. Typed `True → ∀A. A → A`, which is defeq `R`.
    let mp = Expr::lam(
        BinderInfo::Default,
        lhs.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
        ),
    );
    // backward `mpr : R → True`.  `λ(_:R). True.intro`.
    let mpr = Expr::lam(
        BinderInfo::Default,
        rhs.clone(),
        Expr::const_str("True.intro"),
    );
    Some(propext_iff(lhs, rhs, mp, mpr))
}

/// If `e` is an embedded binary `And A B` application (`App(App(Const "And", A), B)`),
/// return `(A, B)`. Unlike [`find_and_operands`] this matches ONLY the top-level
/// application (no recursion), which is exactly the shape of `Pure.conjunction_def`'s
/// embedded LHS.
fn and_app_operands(e: &Expr) -> Option<(Expr, Expr)> {
    use clean_kernel::expr::ExprKind;
    let ExprKind::App(app_a, b) = e.kind() else {
        return None;
    };
    let ExprKind::App(head, a) = app_a.kind() else {
        return None;
    };
    if matches!(head.kind(), ExprKind::Const(n, _) if *n == Name::from_string("And")) {
        Some(((**a).clone(), (**b).clone()))
    } else {
        None
    }
}

/// [`prove_pure_conjunction_rule`] with parameter snapshot/restore on a no-match,
/// for use as a `…_first` statement-level arm.
pub(crate) fn prove_pure_conjunction_rule_first(
    ctx: &mut Ctx,
    thm: &IsaProvenTheorem,
) -> Result<Option<Expr>, TranslateError> {
    let snap_types = ctx.type_params.clone();
    let snap_terms = ctx.term_params.clone();
    let snap_hyps = ctx.hyp_params.clone();
    let r = prove_pure_conjunction_rule(ctx, thm)?;
    if r.is_none() {
        ctx.type_params = snap_types;
        ctx.term_params = snap_terms;
        ctx.hyp_params = snap_hyps;
    }
    Ok(r)
}

/// Classical-rule statement-level proof attempted **before** the recorded proof.
/// Snapshots the discovered parameters and restores them if no proof is produced
/// (a non-matching probe leaves no phantom binders behind). The kernel re-checks
/// any produced term, so this is soundness-neutral.
pub(crate) fn prove_classical_rule_first(
    ctx: &mut Ctx,
    thm: &IsaProvenTheorem,
) -> Result<Option<Expr>, TranslateError> {
    let snap_types = ctx.type_params.clone();
    let snap_terms = ctx.term_params.clone();
    let snap_hyps = ctx.hyp_params.clone();
    let r = ctx.prove_classical_rule(&thm.prop)?;
    if r.is_none() {
        ctx.type_params = snap_types;
        ctx.term_params = snap_terms;
        ctx.hyp_params = snap_hyps;
    }
    Ok(r)
}

/// Build the body of a `def-raw` node `(c ≡ HOL.c) ⟹ (lhs ≡ rhs)` whose
/// conclusion follows from the single equality premise by *rewriting* `c` to its
/// definition. Under this embedding `HOL.c` IS the connective encoding `enc`, so
/// substituting `c := enc` into `lhs` yields a term β-equal to `rhs`. The proof
/// is therefore
///
/// ```text
/// @Eq.subst τ (fun z => @Eq α lhs[c:=z] rhs) enc c (@Eq.symm τ c enc h) (@Eq.refl α rhs)
/// ```
///
/// which has type `@Eq α lhs[c:=c] rhs` = `@Eq α lhs rhs` (the goal). The kernel
/// re-checks it (including that `lhs[c:=enc]` is definitionally `rhs`), so a node
/// that is not in fact a definitional unfolding is rejected, never miscounted.
///
/// Exactly one premise must be an equality `@Eq τ c enc` over a bare `fvar` `c`
/// (the others — e.g. a leading `True` sort constraint — are ignored, already
/// discharged by enclosing lambdas); returns `None` if there is no unique such
/// premise. The eq premise at position `pos` occupies de Bruijn `bvar(n-1-pos)`
/// under the `n` premise binders.
pub(crate) fn def_unfold_body(premise_tys: &[Expr], concl_e: &Expr, n: usize) -> Option<Expr> {
    let mut eq_premise = None;
    for (pos, ty) in premise_tys.iter().enumerate() {
        if let Some(parts) = eq_parts_fvar_lhs(ty) {
            if eq_premise.is_some() {
                return None; // ambiguous: more than one eq premise
            }
            eq_premise = Some((pos, parts));
        }
    }
    let (pos, (tau, c_fvar, enc)) = eq_premise?;
    let (alpha, lhs, rhs) = eq_three_parts(concl_e)?;
    // motive: fun (z : τ) => @Eq α lhs[c:=z] rhs (built by abstracting the `c`
    // fvar out of the embedded equation `@Eq α lhs rhs`).
    let motive = {
        let eq_body = Expr::apps(
            Expr::const_str_levels("Eq", vec![obj_level()]),
            [alpha.clone(), lhs.clone(), rhs.clone()],
        );
        Expr::lam(
            BinderInfo::Default,
            tau.clone(),
            eq_body.abstract_fvar(c_fvar),
        )
    };
    let h = Expr::bvar((n - 1 - pos) as u32); // the eq premise binder
    let h_sym = Expr::apps(
        Expr::const_str_levels("Eq.symm", vec![obj_level()]),
        [tau.clone(), Expr::fvar(c_fvar), enc.clone(), h],
    );
    let refl = Expr::apps(
        Expr::const_str_levels("Eq.refl", vec![obj_level()]),
        [alpha.clone(), rhs.clone()],
    );
    Some(Expr::apps(
        Expr::const_str_levels("Eq.subst", vec![obj_level()]),
        [tau, motive, enc, Expr::fvar(c_fvar), h_sym, refl],
    ))
}

/// If `e` is `@Eq τ (FVar c) enc` (an equation whose LHS is a bare free
/// variable), return `(τ, c, enc)`. Used to recognise a `c ≡ def(c)` premise.
pub(crate) fn eq_parts_fvar_lhs(e: &Expr) -> Option<(Expr, FVarId, Expr)> {
    let (tau, lhs, rhs) = eq_three_parts(e)?;
    if let clean_kernel::expr::ExprKind::FVar(id) = lhs.kind() {
        Some((tau, *id, rhs))
    } else {
        None
    }
}

/// Decompose an embedded equation `@Eq α a b` into `(α, a, b)`.
pub(crate) fn eq_three_parts(e: &Expr) -> Option<(Expr, Expr, Expr)> {
    use clean_kernel::expr::ExprKind;
    let ExprKind::App(eq_a, b) = e.kind() else {
        return None;
    };
    let ExprKind::App(eq, a) = eq_a.kind() else {
        return None;
    };
    let ExprKind::App(head, alpha) = eq.kind() else {
        return None;
    };
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    if *name != Name::from_string("Eq") {
        return None;
    }
    Some(((**alpha).clone(), (**a).clone(), (**b).clone()))
}

/// Split an embedded non-dependent function type `Pi (_:α) β` into `(α, β)`.
/// `β` must not depend on the binder (HOL function types never do), so it is
/// returned as-is.
pub(crate) fn split_arrow(ty: &Expr) -> Option<(Expr, Expr)> {
    use clean_kernel::expr::ExprKind;
    match ty.kind() {
        ExprKind::Pi(_, dom, cod) => Some(((**dom).clone(), (**cod).clone())),
        _ => None,
    }
}

/// First-order matching that solves the `sentinels` (the leading type binders of
/// a referenced theorem) by structurally aligning a binder's `pattern` domain
/// (which may mention sentinel fvars) with the `actual` embedded type of the
/// supplied term argument. Each newly-solved sentinel is recorded in `solution`;
/// already-solved or non-sentinel positions are left untouched. This is a
/// one-sided match (`actual` carries no sentinels), so no occurs-check or
/// unification of `actual`'s own structure is needed.
/// Whether a closure entry's clean type is a **registered class-def axiom** — a
/// `Π`-telescope whose conclusion is `@Eq Prop (isabelle.def.* …) …` (the LHS
/// head being one of the registered `isabelle.def.<c_class>` consts). Used to gate
/// the operation-binder fill in [`Ctx::apply_thm_expecting`] to exactly these
/// entries, so no other PThm path changes behaviour.
pub(crate) fn is_class_def_entry(ty: &Expr) -> bool {
    use clean_kernel::expr::ExprKind;
    let mut concl = ty.clone();
    while let ExprKind::Pi(_, _, cod) = concl.kind() {
        concl = (**cod).clone();
    }
    // concl = @Eq u T lhs rhs  →  App(App(App(App(Eq,T),lhs),rhs))? Actually
    // `@Eq T a b` is App(App(App(Eq,T),a),b). Peel to find the LHS `a` and check
    // its head const name.
    let ExprKind::App(eq_a_lhs, _rhs) = concl.kind() else {
        return false;
    };
    let ExprKind::App(eq_a, lhs) = eq_a_lhs.kind() else {
        return false;
    };
    // eq_a = App(Eq, T); confirm head is `Eq`.
    let ExprKind::App(eq_head, _t) = eq_a.kind() else {
        return false;
    };
    if !matches!(eq_head.kind(), ExprKind::Const(n, _) if *n == Name::from_string("Eq")) {
        return false;
    }
    // The LHS's head const must be a registered class def-const.
    let mut head: Expr = (**lhs).clone();
    while let ExprKind::App(f, _) = head.kind() {
        let f = (**f).clone();
        head = f;
    }
    matches!(head.kind(), ExprKind::Const(n, _) if n.to_string().starts_with("isabelle.def."))
}

/// Structural compatibility test between a binder domain `pattern` (which may
/// still mention unsolved `sentinels`) and a candidate argument type `actual`.
/// An unsolved sentinel position in `pattern` is a wildcard (matches anything);
/// otherwise the two must agree shape-by-shape — a `Pi` only matches a `Pi`, a
/// `Const` only the same `Const`, a `Sort` only the same `Sort`. Used by
/// [`crate::hol::isabelle_pure_translate::Ctx::apply_thm_expecting`] to decide
/// whether the next spine *term* argument fills a given binder (explicit) or the
/// binder is an implicit operation the conclusion determines. A conservative
/// `false` (mismatch) simply makes the binder implicit; the kernel re-checks the
/// assembled term, so neither answer can make an unsound proof pass.
pub(crate) fn types_compatible(pattern: &Expr, actual: &Expr, sentinels: &[FVarId]) -> bool {
    use clean_kernel::expr::ExprKind;
    // A bare unsolved sentinel matches anything.
    if let ExprKind::FVar(id) = pattern.kind() {
        if sentinels.contains(id) {
            return true;
        }
    }
    match (pattern.kind(), actual.kind()) {
        (ExprKind::Pi(_, pdom, pcod), ExprKind::Pi(_, adom, acod)) => {
            types_compatible(pdom, adom, sentinels) && types_compatible(pcod, acod, sentinels)
        }
        (ExprKind::App(pf, pa), ExprKind::App(af, aa)) => {
            types_compatible(pf, af, sentinels) && types_compatible(pa, aa, sentinels)
        }
        (ExprKind::Const(pn, _), ExprKind::Const(an, _)) => pn == an,
        (ExprKind::Sort(pl), ExprKind::Sort(al)) => pl == al,
        (ExprKind::FVar(pi), ExprKind::FVar(ai)) => pi == ai,
        (ExprKind::BVar(pi), ExprKind::BVar(ai)) => pi == ai,
        // A `Pi` against a non-`Pi` (or any other head clash) is incompatible —
        // this is exactly the signal that the candidate argument does not fill the
        // binder (so the binder is implicit).
        _ => false,
    }
}

pub(crate) fn unify_sentinels(
    pattern: &Expr,
    actual: &Expr,
    sentinels: &[FVarId],
    solution: &mut BTreeMap<FVarId, Expr>,
) {
    use clean_kernel::expr::ExprKind;
    // A bare sentinel fvar in the pattern is solved directly by `actual`.
    if let ExprKind::FVar(id) = pattern.kind() {
        if sentinels.contains(id) {
            solution.entry(*id).or_insert_with(|| actual.clone());
            return;
        }
    }
    match (pattern.kind(), actual.kind()) {
        (ExprKind::Pi(_, pdom, pcod), ExprKind::Pi(_, adom, acod)) => {
            unify_sentinels(pdom, adom, sentinels, solution);
            unify_sentinels(pcod, acod, sentinels, solution);
        }
        (ExprKind::App(pf, pa), ExprKind::App(af, aa)) => {
            unify_sentinels(pf, af, sentinels, solution);
            unify_sentinels(pa, aa, sentinels, solution);
        }
        // Other shapes (Const/Sort/BVar/FVar non-sentinel) carry no sentinels to
        // solve from this position; nothing to do.
        _ => {}
    }
}

/// If `e` is an application spine `((head a₁) a₂) … aₙ` (`n ≥ 1`) whose **head**
/// is one of `sentinels` (a still-unsolved schematic binder fvar), return
/// `(head_fvar, [a₁, …, aₙ])`. This is the **flex head** shape that the strictly
/// first-order [`unify_sentinels`] mis-splits (it would descend `App(pf, pa)`
/// and solve the head to a partial application of the actual), so callers detect
/// it here and route the position to the higher-order (Miller-pattern) solve
/// instead. A non-application, or an application whose head is not a sentinel,
/// returns `None`. The stage-3 `bidir_redex` HO lane is the only caller.
pub(crate) fn app_head_sentinel(e: &Expr, sentinels: &[FVarId]) -> Option<(FVarId, Vec<Expr>)> {
    use clean_kernel::expr::ExprKind;
    let mut args: Vec<Expr> = Vec::new();
    let mut cur = e;
    while let ExprKind::App(f, a) = cur.kind() {
        args.push((**a).clone());
        cur = f;
    }
    if args.is_empty() {
        return None;
    }
    args.reverse();
    match cur.kind() {
        ExprKind::FVar(id) if sentinels.contains(id) => Some((*id, args)),
        _ => None,
    }
}

/// **Miller-pattern abstraction.** Abstract `e` over every occurrence of the
/// loose de Bruijn variable `BVar(target)`, producing the BODY of one fresh
/// innermost `λ`: the target maps to `BVar(0)` (the new binder) and every other
/// loose bvar is shifted up by one (to account for the inserted binder), while
/// bvars bound INSIDE `e`'s own binders are left untouched. `depth` is the
/// number of binders already descended (callers pass `0`).
///
/// This is the exact solution of the **Miller (higher-order pattern) fragment**
/// `?P x = e` where `x = BVar(target)` is a distinct bound variable: the unique
/// solution is `?P ↦ λz. e[x ↦ z]`. Returns `None` for any `Expr` shape outside
/// the HOL-embedding subset actually produced by this translator (`Let`/`Proj`/
/// `MData`/impredicative/cubical nodes), so the caller declines the HO solve
/// rather than guessing — keeping the lane strictly additive. The kernel
/// re-checks the assembled application, so a wrong abstraction is rejected.
pub(crate) fn abstract_loose_bvar(e: &Expr, target: u32, depth: u32) -> Option<Expr> {
    use clean_kernel::expr::ExprKind;
    Some(match e.kind() {
        ExprKind::BVar(i) => {
            if *i == target + depth {
                // The abstracted variable, referenced under `depth` inner binders.
                Expr::bvar(depth)
            } else if *i >= depth {
                // A variable free relative to `e`'s top (outer context): shifted
                // up by one for the inserted binder.
                Expr::bvar(i + 1)
            } else {
                // Bound by a binder we descended into `e`: unchanged.
                Expr::bvar(*i)
            }
        }
        ExprKind::App(f, a) => Expr::app(
            abstract_loose_bvar(f, target, depth)?,
            abstract_loose_bvar(a, target, depth)?,
        ),
        ExprKind::Lam(bd, ty, b) => Expr::lam(
            *bd,
            abstract_loose_bvar(ty, target, depth)?,
            abstract_loose_bvar(b, target, depth + 1)?,
        ),
        ExprKind::Pi(bd, ty, b) => Expr::pi(
            *bd,
            abstract_loose_bvar(ty, target, depth)?,
            abstract_loose_bvar(b, target, depth + 1)?,
        ),
        ExprKind::Const(..) | ExprKind::FVar(..) | ExprKind::Sort(..) | ExprKind::Lit(..) => {
            e.clone()
        }
        // Any other shape (Let/Proj/MData/MVar/impredicative/cubical) is outside
        // the HOL-embedding subset — decline the Miller solve.
        _ => return None,
    })
}

/// **Miller-pattern abstraction over a context PARAM.** Like
/// [`abstract_loose_bvar`], but abstracts `e` over every occurrence of the free
/// variable `FVar(target)` — a statement-schematic ctx param (the flavor the
/// Isabelle statement embeds its schematics as, see [`Ctx::term_param`]) — rather
/// than a de Bruijn bound variable. Produces the BODY of one fresh innermost `λ`:
/// the target param maps to `BVar(depth)` (the new binder, referenced under
/// `depth` inner binders), every loose bvar free relative to `e`'s top shifts up
/// by one (to account for the inserted binder), and bvars bound INSIDE `e`'s own
/// binders are left untouched. `depth` is the number of binders already descended
/// (callers pass `0`).
///
/// This is the exact solution of the Miller-fragment problem `?P x = e` where
/// `x = FVar(target)` is the pinned first-order operand (`?t`): the solution
/// `?P ↦ λz. e[FVar(target) ↦ z]` β-reduces `?P (FVar target)` back to `e`.
/// Returns `None` for any `Expr` shape outside the HOL-embedding subset (as
/// [`abstract_loose_bvar`]), so the caller declines rather than guessing. The
/// kernel re-checks the assembled application, so a wrong abstraction is rejected.
pub(crate) fn abstract_loose_fvar(e: &Expr, target: FVarId, depth: u32) -> Option<Expr> {
    use clean_kernel::expr::ExprKind;
    Some(match e.kind() {
        ExprKind::FVar(id) if *id == target => {
            // The abstracted param, referenced under `depth` inner binders.
            Expr::bvar(depth)
        }
        ExprKind::BVar(i) => {
            if *i >= depth {
                // Free relative to `e`'s top: shifted up for the inserted binder.
                Expr::bvar(i + 1)
            } else {
                // Bound by a binder we descended into `e`: unchanged.
                Expr::bvar(*i)
            }
        }
        ExprKind::App(f, a) => Expr::app(
            abstract_loose_fvar(f, target, depth)?,
            abstract_loose_fvar(a, target, depth)?,
        ),
        ExprKind::Lam(bd, ty, b) => Expr::lam(
            *bd,
            abstract_loose_fvar(ty, target, depth)?,
            abstract_loose_fvar(b, target, depth + 1)?,
        ),
        ExprKind::Pi(bd, ty, b) => Expr::pi(
            *bd,
            abstract_loose_fvar(ty, target, depth)?,
            abstract_loose_fvar(b, target, depth + 1)?,
        ),
        ExprKind::Const(..) | ExprKind::FVar(..) | ExprKind::Sort(..) | ExprKind::Lit(..) => {
            e.clone()
        }
        // Any other shape (Let/Proj/MData/MVar/impredicative/cubical) is outside
        // the HOL-embedding subset — decline the Miller solve.
        _ => return None,
    })
}

/// `true` iff `e` has at most `limit` sub-nodes (counting every `App`/`Lam`/`Pi`
/// binder and leaf), with an EARLY EXIT the moment the count exceeds `limit` so a
/// huge term is rejected in `O(limit)` rather than fully traversed. Used to bound
/// the stage-3 Miller solve: the genuine `subst`-family predicate `?P` is built by
/// abstracting the (tiny) leg conclusion `expected` (`P = Q` — a handful of
/// nodes), so capping `expected`'s size keeps every real discharge-chain flip
/// while DECLINING the rare root whose leg conclusion is a large proposition —
/// there the assembled `?P ↦ λz. big` produces a leg β-redex `(λz. big) arg`
/// nested in the root proof that is pathologically expensive for the kernel to
/// reduce/refute (measured: a single such root burned 60+ CPU-minutes). Declining
/// is strictly additive: that root simply falls back to the pre-stage-3 path.
pub(crate) fn expr_within_size(e: &Expr, limit: usize) -> bool {
    fn go(e: &Expr, budget: &mut usize) -> bool {
        use clean_kernel::expr::ExprKind;
        if *budget == 0 {
            return false;
        }
        *budget -= 1;
        match e.kind() {
            ExprKind::App(f, a) => go(f, budget) && go(a, budget),
            ExprKind::Lam(_, ty, b) | ExprKind::Pi(_, ty, b) => go(ty, budget) && go(b, budget),
            _ => true,
        }
    }
    let mut budget = limit;
    go(e, &mut budget)
}

/// One abstraction target for the **multi-argument** Miller-pattern solve
/// ([`abstract_loose_multi`]): a distinct pinned operand the flex predicate is
/// applied to — either a de Bruijn bound variable (`BVar`) or a
/// statement-schematic ctx param (`FVar`, the flavor the Isabelle statement
/// embeds its schematics as). The stage-4 `subst`-family predicate with arity
/// `n ≥ 2` is applied to `n` such targets; abstracting `expected` over all of
/// them simultaneously yields `?P ↦ λz₀…z_{n-1}. body`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum AbsTarget {
    /// A loose de Bruijn bound variable `BVar(idx)` (measured on the real
    /// population: never occurs — the operands resolve to ctx params).
    Bvar(u32),
    /// A statement-schematic ctx param `FVar(id)` (the whole discharge-chain
    /// operand population).
    Fvar(FVarId),
}

/// **Multi-argument Miller-pattern abstraction** (stage-4 `nargs ≥ 2`
/// generalization of [`abstract_loose_bvar`] / [`abstract_loose_fvar`]).
/// Abstract `e` over `targets` — `n` DISTINCT pinned leaf operands — producing
/// the BODY of `n` nested lambdas `λz₀ … λz_{n-1}` (`z₀` OUTERMOST). Target
/// `targets[i]` maps to binder `z_i`, which is `BVar(n-1-i)` at the body top
/// (so `?P a₀ … a_{n-1}` β-reduces `(λz₀ … λz_{n-1}. body) a₀ … a_{n-1}` back to
/// `e`), i.e. `BVar(n-1-i+depth)` under `depth` descended binders. A loose bvar
/// free relative to `e`'s top (not a target) shifts up by `n` to make room for
/// the inserted binders; a bvar bound INSIDE `e`'s own binders is unchanged.
/// `depth` is the number of binders already descended (callers pass `0`).
///
/// This is the exact solution of the Miller (higher-order pattern) fragment
/// `?P a₀ … a_{n-1} = e` when the `aᵢ` are DISTINCT variables/params. Returns
/// `None` for any `Expr` shape outside the HOL-embedding subset (as the
/// single-target helpers), so the caller declines rather than guessing. The
/// kernel re-checks the assembled application, so a wrong abstraction is
/// rejected, never miscounted.
pub(crate) fn abstract_loose_multi(e: &Expr, targets: &[AbsTarget], depth: u32) -> Option<Expr> {
    use clean_kernel::expr::ExprKind;
    let n = targets.len() as u32;
    Some(match e.kind() {
        ExprKind::FVar(id) => {
            match targets
                .iter()
                .position(|t| matches!(t, AbsTarget::Fvar(f) if *f == *id))
            {
                Some(pos) => Expr::bvar(n - 1 - pos as u32 + depth),
                None => e.clone(),
            }
        }
        ExprKind::BVar(i) => {
            // A bvar target `b` appears as `BVar(b + depth)` under `depth`
            // descended binders; that reference maps to its binder `z_pos`.
            match targets
                .iter()
                .position(|t| matches!(t, AbsTarget::Bvar(b) if *b + depth == *i))
            {
                Some(pos) => Expr::bvar(n - 1 - pos as u32 + depth),
                None if *i >= depth => Expr::bvar(*i + n),
                None => Expr::bvar(*i),
            }
        }
        ExprKind::App(f, a) => Expr::app(
            abstract_loose_multi(f, targets, depth)?,
            abstract_loose_multi(a, targets, depth)?,
        ),
        ExprKind::Lam(bd, ty, b) => Expr::lam(
            *bd,
            abstract_loose_multi(ty, targets, depth)?,
            abstract_loose_multi(b, targets, depth + 1)?,
        ),
        ExprKind::Pi(bd, ty, b) => Expr::pi(
            *bd,
            abstract_loose_multi(ty, targets, depth)?,
            abstract_loose_multi(b, targets, depth + 1)?,
        ),
        ExprKind::Const(..) | ExprKind::Sort(..) | ExprKind::Lit(..) => e.clone(),
        // Any other shape (Let/Proj/MData/MVar/impredicative/cubical) is outside
        // the HOL-embedding subset — decline the Miller solve.
        _ => return None,
    })
}

/// **Cheap structural pre-check** for a stage-4 Miller candidate: a bounded
/// lockstep head-symbol + arity walk over two propositions, returning `false`
/// ONLY on a DEFINITE head clash discovered within `budget` nodes (two aligned
/// spine positions whose heads are different `Const`s, or a modeled-shape
/// mismatch such as `App` vs `Pi`). Any position touching an `FVar`/`BVar`/`Lam`/
/// literal — or exhausting the budget — is treated as **compatible** (`true`),
/// so this NEVER rejects a candidate whose prediction merely differs
/// definitionally from the actual premise proposition; it only prunes the
/// obviously-wrong "almost-right" candidates whose full-defeq kernel refutation
/// is pathologically expensive (measured: 60+ CPU-min roots). Because the kernel
/// re-check remains the sole faithfulness arbiter and a `false` here only makes
/// the leg fall back to the pre-stage path (identical to the Miller-OFF
/// baseline), this can lose a would-be flip but can never admit an unsound proof
/// or a 0-lost regression.
pub(crate) fn head_arity_compatible(a: &Expr, b: &Expr, budget: &mut usize) -> bool {
    use clean_kernel::expr::ExprKind;
    if *budget == 0 {
        return true;
    }
    *budget -= 1;
    match (a.kind(), b.kind()) {
        (ExprKind::Const(na, _), ExprKind::Const(nb, _)) => na == nb,
        (ExprKind::App(fa, aa), ExprKind::App(fb, ab)) => {
            head_arity_compatible(fa, fb, budget) && head_arity_compatible(aa, ab, budget)
        }
        (ExprKind::Pi(_, da, ca), ExprKind::Pi(_, db, cb)) => {
            head_arity_compatible(da, db, budget) && head_arity_compatible(ca, cb, budget)
        }
        (ExprKind::Sort(la), ExprKind::Sort(lb)) => la == lb,
        // Both sides are modeled shapes but DIFFERENT ones (App vs Pi, Const vs
        // App, arity mismatch surfacing as App vs Const, …): an obvious clash.
        (
            ExprKind::Const(..) | ExprKind::App(..) | ExprKind::Pi(..) | ExprKind::Sort(..),
            ExprKind::Const(..) | ExprKind::App(..) | ExprKind::Pi(..) | ExprKind::Sort(..),
        ) => false,
        // At least one side is FVar/BVar/Lam/Lit/other — unknown at this cheap
        // altitude; conservatively compatible (the kernel is the arbiter).
        _ => true,
    }
}

/// `true` iff `e` is exactly the `True` definition const `isabelle.def.HOL.True`
/// (the embedded form of HOL's `True`). Used so `HOL.TrueI` is proved by the
/// `True_enc` reflexivity proof, which the kernel accepts against the def-const
/// type via definitional unfolding.
pub(crate) fn is_true_def_const(e: &Expr) -> bool {
    use clean_kernel::expr::ExprKind;
    matches!(e.kind(), ExprKind::Const(name, _) if *name == Name::from_string("isabelle.def.HOL.True"))
}

/// `true` iff `e` is the embedded Pure judgement marker `Pure.term x`, i.e. the
/// `isabelle.def.Pure.term` definition const applied to its type/argument
/// (`@isabelle.def.Pure.term α x`, possibly with only the leading `α` applied).
///
/// The `Pure.term` def-const has body `λ(α:Type)(_:α). ∀(A:Prop). A → A` (see
/// [`super::super::connectives::pure_meta_true_value_and_type`]), so `Pure.term x`
/// δβ-reduces to the trivially-inhabited meta-truth `∀A. A → A`. Detecting this
/// shape lets [`translate_theorem`] prove a bare `Pure.term x` judgement DIRECTLY
/// with its canonical inhabitant ([`pure_term_proof`]) — independent of the
/// intricate recorded `equal_elim (symmetric term_def) …` proof, which references
/// a long `Pure.termI`/`sort_constraintI` closure spine that is often unresolved.
/// This is the *root* of the `Pure.term`/`sort_constraint` cascade: verifying it
/// unblocks `Pure.termI`, `sort_constraintI`, `sort_constraint_eq`, and every
/// downstream consumer. The kernel re-checks the inhabitant against the stored
/// statement type (via def-unfolding), so a mis-detection is rejected — never
/// miscounted.
pub(crate) fn is_pure_term_app(e: &Expr) -> bool {
    use clean_kernel::expr::ExprKind;
    // Peel the application spine to the head const.
    let head = e.get_app_fn();
    matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("isabelle.def.Pure.term"))
        // Require at least the leading type argument applied (a bare, unapplied
        // marker const is not a judgement to prove).
        && !matches!(e.kind(), ExprKind::Const(_, _))
}

/// The canonical inhabitant of the Pure judgement `Pure.term x` — which δβ-reduces
/// to `∀(A:Prop). A → A` — namely the polymorphic identity `λ(A:Prop)(h:A). h`.
/// The kernel accepts this against the stored `@isabelle.def.Pure.term α x` type
/// by δβ-unfolding the def-const to `∀A. A → A`. No axiom content (pure λ), so the
/// consumer stays foundational.
pub(crate) fn pure_term_proof() -> Expr {
    // λ(A:Prop). λ(h:A). h   (h = BVar(0) under the inner binder).
    let inner = Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0));
    Expr::lam(BinderInfo::Default, Expr::prop(), inner)
}

/// `true` iff the embedded statement `e` is exactly the vacuous `True` constant —
/// the erased form of a bare **sort-constraint** judgement `Pure.sort_constraint
/// TYPE('a)` (embedded by [`Ctx::embed_class_membership`] to `Const "True"` in the
/// erase pass). Such a node's recorded proof is an intricate
/// `equal_elim (symmetric sort_constraint_def) …` spine, but the erased statement
/// IS just `True`, provable directly by `True.intro`. This unblocks the standalone
/// `sort_constraint TYPE` nodes (`Pure.sort_constraintI` spine) that seed the
/// sort-constraint cascade. The kernel re-checks `True.intro : True`, so a
/// mis-detection cannot be miscounted.
pub(crate) fn is_true_const(e: &Expr) -> bool {
    use clean_kernel::expr::ExprKind;
    matches!(e.kind(), ExprKind::Const(name, _) if *name == Name::from_string("True"))
}

/// If `e` is the embedded HOL negation `isabelle.def.HOL.Not P` (the `Not`
/// definition const applied to one argument), return the embedded operand `P`.
/// In this embedding `HOL.Not P` is defeq to `P → False_enc` (`False_enc = ∀Q.Q`).
pub(crate) fn hol_not_arg(e: &Expr) -> Option<Expr> {
    use clean_kernel::expr::ExprKind;
    let ExprKind::App(head, arg) = e.kind() else {
        return None;
    };
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    if *name != Name::from_string("isabelle.def.HOL.Not") {
        return None;
    }
    Some((**arg).clone())
}

#[cfg(test)]
mod stage4_miller_tests {
    use super::*;
    use clean_kernel::expr::ExprKind;

    /// Two-argument imitation: abstracting `H a b` over the two distinct fvar
    /// operands `a, b` yields `H (BVar 1) (BVar 0)` (`a → z₀` outermost `BVar 1`,
    /// `b → z₁` innermost `BVar 0`) so `(λz₀ z₁. body) a b` β-reduces back.
    #[test]
    fn test_abstract_loose_multi_two_fvars_maps_to_bvars() {
        let (h, a, b) = (FVarId::new(100), FVarId::new(101), FVarId::new(102));
        let expected = Expr::app(Expr::app(Expr::fvar(h), Expr::fvar(a)), Expr::fvar(b));
        let targets = [AbsTarget::Fvar(a), AbsTarget::Fvar(b)];
        let body = abstract_loose_multi(&expected, &targets, 0).expect("in HOL subset");
        // body should be `H (BVar 1) (BVar 0)`.
        let ExprKind::App(f, arg1) = body.kind() else {
            panic!("expected App at top");
        };
        assert!(
            matches!(arg1.kind(), ExprKind::BVar(0)),
            "second operand → BVar 0"
        );
        let ExprKind::App(head, arg0) = f.kind() else {
            panic!("expected nested App");
        };
        assert!(
            matches!(arg0.kind(), ExprKind::BVar(1)),
            "first operand → BVar 1"
        );
        // The non-target head `H` is left untouched (an fvar, not abstracted).
        assert!(
            matches!(head.kind(), ExprKind::FVar(id) if *id == h),
            "head fvar unchanged"
        );
    }

    /// A loose bvar in `expected` that is NOT a target shifts up by `n = 2` to
    /// make room for the two inserted binders.
    #[test]
    fn test_abstract_loose_multi_shifts_free_bvar_by_n() {
        let a = FVarId::new(200);
        // `H (BVar 0) a` where BVar 0 is free relative to expected's top.
        let h = FVarId::new(201);
        let expected = Expr::app(Expr::app(Expr::fvar(h), Expr::bvar(0)), Expr::fvar(a));
        let targets = [AbsTarget::Fvar(a), AbsTarget::Bvar(5)];
        let body = abstract_loose_multi(&expected, &targets, 0).expect("in HOL subset");
        let ExprKind::App(f, arg1) = body.kind() else {
            panic!("expected App");
        };
        // `a` is target index 0 → BVar(n-1-0) = BVar 1.
        assert!(matches!(arg1.kind(), ExprKind::BVar(1)), "a → BVar 1");
        let ExprKind::App(_h, arg0) = f.kind() else {
            panic!("expected nested App");
        };
        // free BVar 0 shifts up by n = 2 → BVar 2.
        assert!(
            matches!(arg0.kind(), ExprKind::BVar(2)),
            "free BVar 0 → BVar 2"
        );
    }

    /// The cheap pre-check rejects a definite const-head clash and accepts a
    /// structurally-matching pair.
    #[test]
    fn test_head_arity_compatible_detects_clash() {
        let c1 = Expr::const_str_levels("Foo", vec![]);
        let c2 = Expr::const_str_levels("Bar", vec![]);
        let mut b = 256usize;
        assert!(
            !head_arity_compatible(&c1, &c2, &mut b),
            "different const heads clash"
        );
        let mut b2 = 256usize;
        assert!(
            head_arity_compatible(&c1, &c1.clone(), &mut b2),
            "same const heads compatible"
        );
        // An fvar position is unknown → conservatively compatible (never a clash).
        let mut b3 = 256usize;
        assert!(
            head_arity_compatible(&Expr::fvar(FVarId::new(1)), &c1, &mut b3),
            "fvar vs const is conservatively compatible"
        );
    }
}
