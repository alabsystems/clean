// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Embedded-equation shape helpers and the reflexive/telescoped-equality and
//! connective-elimination proof builders for the Isabelle Pure translator
//! (`reflexive_eq_parts`, `eq_app_three`, `prove_telescoped_eq_refl`,
//! `binary_connective_parts`, `connective_elim_body`, …). Moved verbatim from the
//! original single-file `def_axioms` module; behaviour is byte-identical.

use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr};

use super::super::*;
/// If `e` is a *syntactically reflexive* embedded equation `@Eq α a a` (the two
/// operands structurally identical), return `(α, a)`. Used to prove such a
/// statement by `@Eq.refl α a` directly — the case for genuine `a = a` lemmas
/// and for HOL constants (`True`) whose encoding unfolds to one.
pub(crate) fn reflexive_eq_parts(e: &Expr) -> Option<(Expr, Expr)> {
    use clean_kernel::expr::ExprKind;
    // `@Eq α a b` = App(App(App(Const "Eq", α), a), b).
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
    if *name != Name::from_string("Eq") || a != b {
        return None;
    }
    Some(((**alpha).clone(), (**a).clone()))
}

/// Decompose an embedded equation `@Eq α a b` into `(α, a, b)` (the Eq level read
/// off the `Const "Eq"` head), **without** requiring `a == b` (unlike
/// [`reflexive_eq_parts`]). Returns `None` if `e` is not an `Eq` application.
pub(crate) fn eq_app_three(e: &Expr) -> Option<(Expr, Expr, Expr, Vec<Level>)> {
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
    let ExprKind::Const(name, levels) = head.kind() else {
        return None;
    };
    if *name != Name::from_string("Eq") {
        return None;
    }
    Some((
        (**alpha).clone(),
        (**a).clone(),
        (**b).clone(),
        levels.to_vec(),
    ))
}

/// Prove an embedded **Pi-telescoped reflexive equation** by reflexivity: a
/// proposition of the shape
/// ```text
/// Π(x₁:T₁) … (xₙ:Tₙ). @Eq α lhs rhs
/// ```
/// (the leading `Π` binders are the discharged sort premises — `True →` — and the
/// `⋀`-universals of a HOL datatype computation rule), where `lhs` is
/// **definitionally equal** to `rhs` (e.g. `case_sum f g (Inl a)` ι-reduces to
/// `f a`, `case_option`/`rec_*`/`map_*.simps`, …). The proof is
/// `λ(x₁:T₁) … (xₙ:Tₙ). @Eq.refl α lhs`, which the kernel accepts **iff** `lhs`
/// genuinely δ/ι/β-reduces to `rhs` under the binder context — so a non-reducible
/// (genuinely different) equation is kernel-rejected and can never be miscounted.
/// This is faithful: the stored statement keeps the REAL `lhs = rhs` shape (it is
/// `prop` itself), and the `Eq.refl lhs` proof is sound exactly when the two sides
/// coincide definitionally. Returns `None` if the core is not an `Eq` application.
pub(crate) fn prove_telescoped_eq_refl(prop: &Expr) -> Option<Expr> {
    use clean_kernel::expr::ExprKind;
    // Peel leading `Pi` binders, remembering each `(info, domain)` to rebuild the
    // matching `λ` wrapper. The core must be an `@Eq α lhs rhs`.
    let mut binders: Vec<(BinderInfo, Expr)> = Vec::new();
    let mut core = prop.clone();
    while let ExprKind::Pi(data, dom, body) = core.kind() {
        binders.push((data.info, (**dom).clone()));
        core = (**body).clone();
    }
    let (alpha, lhs, _rhs, levels) = eq_app_three(&core)?;
    // SCOPE GUARD (faithful + regression-safe): only attempt the reflexivity proof
    // when the LHS is headed by a **datatype recursor** we map (`Sum.rec`,
    // `Option.rec`, `Nat.rec`, `Num.rec`, `Prod.rec`). That is exactly the shape of
    // a datatype *computation rule* (`case_sum f g (Inl a)`, `rec_*`, `*.simps`),
    // whose LHS genuinely ι-reduces to the RHS. Restricting to this head keeps the
    // arm from re-proving unrelated definitional equations (`bot = Collect …`) by
    // reflexivity — which, even when the kernel accepts them, perturb the shared
    // closure and can flip a downstream consumer onto a worse translation arm. The
    // kernel still re-checks `Eq.refl lhs : lhs = rhs`, so this only ever narrows
    // (never loosens) what is accepted.
    if !lhs_head_is_datatype_recursor(&lhs) {
        return None;
    }
    let mut proof = Expr::apps(Expr::const_str_levels("Eq.refl", levels), [alpha, lhs]);
    for (info, dom) in binders.into_iter().rev() {
        proof = Expr::lam(info, dom, proof);
    }
    Some(proof)
}

/// Like [`prove_telescoped_eq_refl`] but **without** the datatype-recursor scope
/// guard — for a caller that has ALREADY confirmed (by ISA statement shape) that
/// the equation is a genuine definitional `_def` whose LHS β/δ-reduces to the RHS
/// (e.g. [`is_pointwise_instance_def`] for the pointwise `…_fun_inst.…_fun_def` /
/// `equal_itself_def` / `ord.max`/`min` instance defs). Peels the leading `Pi`
/// binders (the discharged `True →`/`⋀` sort premises), then proves the core
/// `@Eq α lhs rhs` by `λ…. Eq.refl α lhs`. The kernel re-checks
/// `Eq.refl α lhs : @Eq α lhs rhs`, accepting **iff** `lhs` genuinely
/// definitionally equals `rhs` — so a non-reflexive equation is kernel-rejected,
/// never a `B=B` tautology, never miscounted. Returns `None` if the core is not an
/// `@Eq` application.
pub(crate) fn prove_scoped_telescoped_eq_refl(prop: &Expr) -> Option<Expr> {
    use clean_kernel::expr::ExprKind;
    let mut binders: Vec<(BinderInfo, Expr)> = Vec::new();
    let mut core = prop.clone();
    while let ExprKind::Pi(data, dom, body) = core.kind() {
        binders.push((data.info, (**dom).clone()));
        core = (**body).clone();
    }
    let (alpha, lhs, _rhs, levels) = eq_app_three(&core)?;
    let mut proof = Expr::apps(Expr::const_str_levels("Eq.refl", levels), [alpha, lhs]);
    for (info, dom) in binders.into_iter().rev() {
        proof = Expr::lam(info, dom, proof);
    }
    Some(proof)
}

/// Whether the embedded term `lhs` mentions a **datatype recursor** the HOL
/// datatype mappings introduce (`Sum.rec`, `Option.rec`, `Nat.rec`, `Num.rec`,
/// `Prod.rec`). The mapped `case_*`/`rec_*` combinators embed to a `λ…. <rec> …`
/// lambda, so on a computation rule the recursor appears as the redex head of the
/// LHS (e.g. `(λf g s. Sum.rec … s) f g (Inl a)`); we therefore look for the
/// recursor anywhere in the LHS rather than only as the top App-spine head (which
/// is the enclosing lambda). Used to scope [`prove_telescoped_eq_refl`] to genuine
/// datatype computation rules, keeping it from re-proving unrelated definitional
/// equations (which, even when kernel-valid, perturb the shared closure and can
/// flip a downstream consumer onto a worse translation arm).
pub(crate) fn lhs_head_is_datatype_recursor(lhs: &Expr) -> bool {
    use clean_kernel::expr::ExprKind;
    pub(crate) fn is_rec(name: &Name) -> bool {
        *name == Name::from_string("Sum.rec")
            || *name == Name::from_string("Option.rec")
            || *name == Name::from_string("Nat.rec")
            || *name == Name::from_string("Num.rec")
            || *name == Name::from_string("Prod.rec")
            // `case_prod`'s embedding folds through the projections rather than
            // `Prod.rec`, so a `case_prod f (Pair a b) = f a b`-shaped computation
            // rule's LHS mentions `Prod.fst`/`Prod.snd`/`Prod.mk`, not `Prod.rec`.
            || *name == Name::from_string("Prod.fst")
            || *name == Name::from_string("Prod.snd")
            || *name == Name::from_string("Prod.mk")
    }
    pub(crate) fn mentions(e: &Expr) -> bool {
        match e.kind() {
            ExprKind::Const(name, _) => is_rec(name),
            ExprKind::App(f, a) => mentions(f) || mentions(a),
            ExprKind::Lam(_, dom, body) | ExprKind::Pi(_, dom, body) => {
                mentions(dom) || mentions(body)
            }
            _ => false,
        }
    }
    mentions(lhs)
}

/// Decompose an embedded application `App(f, x)` into `(f, x)`.
pub(crate) fn app_parts(e: &Expr) -> Option<(Expr, Expr)> {
    use clean_kernel::expr::ExprKind;
    let ExprKind::App(f, x) = e.kind() else {
        return None;
    };
    Some(((**f).clone(), (**x).clone()))
}

/// Decompose an embedded binary connective application
/// `App(App(Const "isabelle.def.HOL.<conn>", P), Q)` into `(conn, P, Q)`, where
/// `conn` is the bare connective name (`HOL.conj` / `HOL.disj`).
pub(crate) fn binary_connective_parts(e: &Expr) -> Option<(&'static str, Expr, Expr)> {
    use clean_kernel::expr::ExprKind;
    let ExprKind::App(app_pq, q) = e.kind() else {
        return None;
    };
    let ExprKind::App(head, p) = app_pq.kind() else {
        return None;
    };
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    let conn = if *name == Name::from_string("isabelle.def.HOL.conj") {
        "HOL.conj"
    } else if *name == Name::from_string("isabelle.def.HOL.disj") {
        "HOL.disj"
    } else {
        return None;
    };
    Some((conn, (**p).clone(), (**q).clone()))
}

/// Build the body of a connective-elimination rule from its discharged premises,
/// using the impredicative encoding of the connective hypothesis (registered as a
/// defeq-unfolding `Definition`):
///
/// - `conj P Q ≡ ∀C. (P → Q → C) → C` — a `conj P Q` hypothesis `h`, applied to
///   the goal `R` and a case proof `P → Q → R`, yields `R`:
///   - `conjunct1` (`conj P Q ⟹ P`): `h P (fun (p:P)(q:Q) => p)`;
///   - `conjunct2` (`conj P Q ⟹ Q`): `h Q (fun (p:P)(q:Q) => q)`;
///   - `conjE`     (`conj P Q ⟹ (P ⟹ Q ⟹ R) ⟹ R`): `h R hpqr`.
/// - `disj P Q ≡ ∀C. (P → C) → (Q → C) → C` — a `disj P Q` hypothesis applied to
///   the goal and the two case proofs:
///   - `disjE` (`disj P Q ⟹ (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R`): `h R hp hq`.
///
/// `premise_tys` are the embedded premises under the `n` premise binders. Returns
/// `None` unless a unique connective premise and matching case-proof premises are
/// found. The kernel unfolds the connective definition by defeq and re-checks.
pub(crate) fn connective_elim_body(premise_tys: &[Expr], concl_e: &Expr, n: usize) -> Option<Expr> {
    let bvar = |pos: usize| Expr::bvar((n - 1 - pos) as u32);
    // Locate the (unique) binary-connective premise.
    let mut conn_premise = None;
    for (pos, ty) in premise_tys.iter().enumerate() {
        if let Some((conn, p, q)) = binary_connective_parts(ty) {
            if conn_premise.is_some() {
                return None; // ambiguous
            }
            conn_premise = Some((pos, conn, p, q));
        }
    }
    let (pos_h, conn, p, q) = conn_premise?;
    let h = bvar(pos_h);
    match conn {
        "HOL.conj" => {
            // case proof premise `P ⟹ Q ⟹ R` (for conjE), if present.
            let case = premise_tys.iter().enumerate().find_map(|(pos, ty)| {
                let (pa, rest) = split_arrow(ty)?;
                let (qb, r) = split_arrow(&rest)?;
                (pa == p && qb == q && r == *concl_e).then(|| bvar(pos))
            });
            if let Some(case) = case {
                // conjE: `h R case`.
                return Some(Expr::apps(h, [concl_e.clone(), case]));
            }
            // conj_comm (`conj P Q ⟹ conj Q P`): the conclusion is the *commuted*
            // conjunction `conj Q P ≡ ∀C.(Q→P→C)→C`. Build
            // `fun (C:Prop)(k:Q→P→C) => h C (fun (p:P)(q:Q) => k q p)`, where
            // `h C : (P→Q→C)→C`. The kernel re-checks via the `conj` defeq.
            if let Some(("HOL.conj", r, s)) = binary_connective_parts(concl_e) {
                if r == q && s == p {
                    return Some(conn_comm_conj(&h, &p, &q));
                }
            }
            // conjunct1 / conjunct2: the conclusion is `P` or `Q`. Build the
            // selector `fun (p:P)(q:Q) => p|q` and apply `h` to the goal + selector.
            let selector = if *concl_e == p {
                // fun (p:P)(q:Q) => p  → under 2 binders, p is bvar 1.
                Expr::lam(
                    BinderInfo::Default,
                    p.clone(),
                    Expr::lam(BinderInfo::Default, q.clone(), Expr::bvar(1)),
                )
            } else if *concl_e == q {
                // fun (p:P)(q:Q) => q  → q is bvar 0.
                Expr::lam(
                    BinderInfo::Default,
                    p.clone(),
                    Expr::lam(BinderInfo::Default, q.clone(), Expr::bvar(0)),
                )
            } else {
                return None;
            };
            Some(Expr::apps(h, [concl_e.clone(), selector]))
        }
        "HOL.disj" => {
            // disjE: case proofs `P ⟹ R` and `Q ⟹ R`.
            let case_proofs = (|| {
                let hp = premise_tys.iter().enumerate().find_map(|(pos, ty)| {
                    let (a, r) = split_arrow(ty)?;
                    (a == p && r == *concl_e).then(|| bvar(pos))
                })?;
                let hq = premise_tys.iter().enumerate().find_map(|(pos, ty)| {
                    let (a, r) = split_arrow(ty)?;
                    (a == q && r == *concl_e).then(|| bvar(pos))
                })?;
                Some(Expr::apps(h.clone(), [concl_e.clone(), hp, hq]))
            })();
            if case_proofs.is_some() {
                return case_proofs;
            }
            // disj_comm (`disj P Q ⟹ disj Q P`): the conclusion is the *commuted*
            // disjunction `disj Q P ≡ ∀C.(Q→C)→(P→C)→C`. Build
            // `fun (C:Prop)(hq:Q→C)(hp:P→C) => h C hp hq`, where
            // `h C : (P→C)→(Q→C)→C`. The kernel re-checks via the `disj` defeq.
            if let Some(("HOL.disj", r, s)) = binary_connective_parts(concl_e) {
                // `r`/`s` are the conclusion's left/right disjuncts.
                if r == q && s == p {
                    // disj_comm: conclusion `disj Q P` (operands swapped).
                    return Some(conn_comm_disj(&h, &p, &q));
                }
                // disj_forward (`disj P Q ⟹ (P ⟹ R) ⟹ (Q ⟹ S) ⟹ disj R S`):
                // the conclusion is `disj R S`, with implication premises `P→R` and
                // `Q→S` mapping each disjunct forward. Build
                // `fun (C:Prop)(hr:R→C)(hs:S→C) => h C (fun p => hr (f p)) (fun q => hs (g q))`.
                let f = premise_tys.iter().enumerate().find_map(|(pos, ty)| {
                    let (a, b) = split_arrow(ty)?;
                    (a == p && b == r).then(|| bvar(pos))
                });
                let g = premise_tys.iter().enumerate().find_map(|(pos, ty)| {
                    let (a, b) = split_arrow(ty)?;
                    (a == q && b == s).then(|| bvar(pos))
                });
                if let (Some(f), Some(g)) = (f, g) {
                    return Some(conn_forward_disj(&h, &p, &q, &r, &s, &f, &g));
                }
            }
            None
        }
        _ => None,
    }
}
