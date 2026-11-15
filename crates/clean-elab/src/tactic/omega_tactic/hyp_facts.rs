// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What omega's hypothesis splitter does with each propositional hypothesis.
//!
//! Lean 4.8's `omega` reads its facts through `MetaProblem.addFact` and
//! `pushNot` (`Lean/Elab/Tactic/Omega/Frontend.lean`): a conjunction becomes
//! both conjuncts, a disjunction is queued for a case split, and `≠`, `¬(p ∨
//! q)`, `p → q` and `p ↔ q` are first turned into one of those two shapes.
//! [`classify`] makes the same reading of one local; the casts it returns are
//! closed terms over the local, re-checked strictly here and again by
//! `replace_local_decl_with_cast`, so a wrong cast is skipped, never trusted.
//!
//! Classical reasoning appears exactly where Lean's `omega` uses it:
//! `p → q` and `p ↔ q` go through `Classical.em` (Lean:
//! `Decidable.not_or_of_imp` / `Decidable.and_or_not_and_not_of_iff` at
//! `Classical.propDecidable`). `≠` and `¬(p ∨ q)` are constructive.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

use super::super::decide_eq::match_ne;
use super::super::{
    match_and, match_eq, match_ge, match_gt, match_iff, match_le_any, match_lt_any, match_not,
    match_or,
};
use super::{Goal, ProofState};
use crate::tactic::LocalDecl;

/// What the splitter does with one hypothesis.
pub(super) enum HypAction {
    /// `h : A ∧ B` — destructure into both conjuncts (one goal).
    Destructure,
    /// `h : A ∨ B` — case split (two goals).
    Split,
    /// Replace `h` by `new_ty`, proved by `cast` (a term over `h`).
    Replace { new_ty: Expr, cast: Expr },
}

/// How omega's splitter reads `decl`, or `None` when the local carries no
/// linear-arithmetic content omega could use (Lean's "no new facts" test, read
/// syntactically: a split whose branches add nothing linear only costs time).
pub(super) fn classify(state: &ProofState, goal: &Goal, decl: &LocalDecl) -> Option<HypAction> {
    if decl.value.is_some() {
        return None;
    }
    let ty = state.metas.instantiate(&decl.ty);
    let h = Expr::fvar(decl.fvar);
    if let Some((p, q)) = match_and(&ty) {
        return (yields_fact(&p) || yields_fact(&q)).then_some(HypAction::Destructure);
    }
    if let Some((p, _)) = match_or(&ty) {
        // Lean's `splitDisjunction` splits only when the LEFT disjunct adds a
        // fact (`processFacts` count > 0); otherwise it drops the disjunction.
        return yields_fact(&p).then_some(HypAction::Split);
    }
    if let Some((p, q)) = match_iff(&ty) {
        if !(yields_fact(&p) || yields_fact(&q)) {
            return None;
        }
        return validated(state, goal, iff_cast(h, p, q));
    }
    if let Some((carrier, a, b)) = disequality(&ty) {
        return ne_cast(state, goal, h, &carrier, a, b);
    }
    if let Some(inner) = match_not_app(&ty) {
        if !yields_fact(&inner) {
            return None;
        }
        if let Some((p, q)) = match_or(&inner) {
            return validated(state, goal, not_or_cast(h, p, q));
        }
        if let Some((p, q)) = match_and(&inner) {
            return validated(state, goal, not_and_cast(h, p, q));
        }
        if let Some(p) = match_not(&inner) {
            return validated(state, goal, not_not_cast(h, p));
        }
        return None;
    }
    if let ExprKind::Pi(_, dom, cod) = ty.kind() {
        if cod.has_loose_bvars() || !(yields_fact(dom) || yields_fact(cod)) {
            return None;
        }
        if !is_prop(state, goal, dom) || !is_prop(state, goal, cod) {
            return None;
        }
        return validated(state, goal, imp_cast(h, (**dom).clone(), (**cod).clone()));
    }
    None
}

/// Cheap pre-test for [`classify`]: `true` when `decl` has a shape the
/// splitter acts on, without building or checking any cast. `classify` may
/// still decline it (a cast the environment cannot type).
pub(super) fn may_act(state: &ProofState, goal: &Goal, decl: &LocalDecl) -> bool {
    if decl.value.is_some() {
        return false;
    }
    let ty = state.metas.instantiate(&decl.ty);
    if let Some((p, _)) = match_or(&ty) {
        return yields_fact(&p);
    }
    if let Some((p, q)) = match_and(&ty).or_else(|| match_iff(&ty)) {
        return yields_fact(&p) || yields_fact(&q);
    }
    if disequality(&ty).is_some() {
        return true;
    }
    if let Some(inner) = match_not_app(&ty) {
        let compound = match_or(&inner).is_some()
            || match_and(&inner).is_some()
            || match_not(&inner).is_some();
        return compound && yields_fact(&inner);
    }
    matches!(ty.kind(), ExprKind::Pi(_, dom, cod)
        if !cod.has_loose_bvars() && (yields_fact(dom) || yields_fact(cod)))
        && is_pi_of_props(state, goal, &ty)
}

fn is_pi_of_props(state: &ProofState, goal: &Goal, ty: &Expr) -> bool {
    match ty.kind() {
        ExprKind::Pi(_, dom, cod) => is_prop(state, goal, dom) && is_prop(state, goal, cod),
        _ => false,
    }
}

/// `true` when splitting or destructuring `ty` can hand omega a linear fact:
/// a `Nat`/`Int` comparison, possibly under `¬`, `∧`, `∨`, `↔` or `→`.
pub(super) fn yields_fact(ty: &Expr) -> bool {
    if is_arith_atom(ty) {
        return true;
    }
    if let Some(inner) = match_not(ty) {
        return yields_fact(&inner);
    }
    if let Some((p, q)) = match_and(ty)
        .or_else(|| match_or(ty))
        .or_else(|| match_iff(ty))
    {
        return yields_fact(&p) || yields_fact(&q);
    }
    if let ExprKind::Pi(_, dom, cod) = ty.kind() {
        return !cod.has_loose_bvars() && (yields_fact(dom) || yields_fact(cod));
    }
    false
}

/// A `=`/`≠`/`≤`/`<`/`≥`/`>` between `Nat`s or `Int`s.
fn is_arith_atom(ty: &Expr) -> bool {
    match_le_any(ty)
        .or_else(|| match_lt_any(ty))
        .or_else(|| match_ge(ty))
        .or_else(|| match_gt(ty))
        .or_else(|| match_eq(ty))
        .map(|(carrier, _, _)| carrier)
        .or_else(|| match_ne(ty).map(|(_, carrier, _, _)| carrier))
        .is_some_and(|carrier| carrier_name(&carrier).is_some())
}

/// `a ≠ b` / `¬(a = b)` over `Nat` or `Int`, as `(carrier, a, b)`.
fn disequality(ty: &Expr) -> Option<(Expr, Expr, Expr)> {
    let (carrier, a, b) = match_ne(ty)
        .map(|(_, carrier, a, b)| (carrier, a, b))
        .or_else(|| match_not_app(ty).and_then(|inner| match_eq(&inner)))?;
    carrier_name(&carrier)?;
    Some((carrier, a, b))
}

/// `p` when `ty` is the APPLICATION `Not p`.
///
/// Lean's `addFact` matches `Not` by name and reads a written-out `p → False`
/// as an implication (`¬p ∨ False`, whose `False` branch carries no fact), so
/// the two spellings are kept apart here; `match_not` accepts both.
pub(super) fn match_not_app(ty: &Expr) -> Option<Expr> {
    match ty.kind() {
        ExprKind::App(f, p) if matches!(f.kind(), ExprKind::Const(n, _) if n.to_string() == "Not") => {
            Some((**p).clone())
        }
        _ => None,
    }
}

/// `"Nat"` / `"Int"` for those carrier constants, else `None`.
pub(super) fn carrier_name(carrier: &Expr) -> Option<&'static str> {
    match carrier.kind() {
        ExprKind::Const(n, _) if n.to_string() == "Nat" => Some("Nat"),
        ExprKind::Const(n, _) if n.to_string() == "Int" => Some("Int"),
        _ => None,
    }
}

pub(super) fn is_prop(state: &ProofState, goal: &Goal, ty: &Expr) -> bool {
    state
        .infer_type(goal, ty)
        .map(|sort| state.whnf(goal, &sort))
        .is_ok_and(|sort| matches!(sort.kind(), ExprKind::Sort(l) if l.is_zero()))
}

/// Keep a `(new_ty, cast)` pair only when `cast` strictly infers to a type
/// definitionally equal to `new_ty`.
fn validated(state: &ProofState, goal: &Goal, pair: (Expr, Expr)) -> Option<HypAction> {
    let (new_ty, cast) = pair;
    let inferred = state.infer_type_strict(goal, &cast).ok()?;
    state
        .is_def_eq(goal, &inferred, &new_ty)
        .then_some(HypAction::Replace { new_ty, cast })
}

/// `h : a ≠ b` ⟶ `a < b ∨ b < a` (Lean: `Nat.lt_or_gt_of_ne` /
/// `Int.lt_or_gt_of_ne`). Uses that lemma when the environment has it, else
/// derives the same disjunction from `lt_trichotomy`, refuting its middle
/// `a = b` arm with `h` — Clean's builtin prelude states trichotomy for both
/// carriers but not `lt_or_gt_of_ne`.
fn ne_cast(
    state: &ProofState,
    goal: &Goal,
    h: Expr,
    carrier: &Expr,
    a: Expr,
    b: Expr,
) -> Option<HypAction> {
    let c = carrier_name(carrier)?;
    let direct = Name::from_string(&format!("{c}.lt_or_gt_of_ne"));
    if state.env().get_const(&direct).is_some() {
        let cast = Expr::apps(
            Expr::const_(direct, vec![]),
            [a.clone(), b.clone(), h.clone()],
        );
        if let Ok(new_ty) = state.infer_type_strict(goal, &cast) {
            if match_or(&new_ty).is_some() {
                return Some(HypAction::Replace { new_ty, cast });
            }
        }
    }
    let tri_name = Name::from_string(&format!("{c}.lt_trichotomy"));
    state.env().get_const(&tri_name)?;
    let tri = Expr::apps(Expr::const_(tri_name, vec![]), [a.clone(), b.clone()]);
    let tri_ty = state.infer_type_strict(goal, &tri).ok()?;
    let (lt_raw, rest) = match_or(&tri_ty)?;
    let (eq, gt_raw) = match_or(&rest)?;
    // The builtin `Int.lt_trichotomy` states its disjuncts with the raw
    // `Int.lt`, which omega's readers do not recognise as a comparison, so the
    // split it feeds would never happen. Restate them through `LT.lt` (a
    // definitional retyping, re-checked by `validated`).
    let restate = |raw: Expr, x: &Expr, y: &Expr| {
        if is_arith_atom(&raw) {
            raw
        } else {
            typeclass_lt(state, c, carrier, x, y).unwrap_or(raw)
        }
    };
    let lt = restate(lt_raw, &a, &b);
    let gt = restate(gt_raw, &b, &a);
    let new_ty = or(lt.clone(), gt.clone());
    // λ (r : a = b ∨ b < a). Or.rec (λ e. False.elim (h e)) (λ g. Or.inr g) r
    let middle = Expr::apps(
        cst("Or.rec"),
        [
            eq.clone(),
            gt.clone(),
            Expr::lam(BinderInfo::Default, rest.clone(), new_ty.clone()),
            Expr::lam(
                BinderInfo::Default,
                eq,
                false_elim(new_ty.clone(), Expr::app(h, Expr::bvar(0))),
            ),
            Expr::lam(
                BinderInfo::Default,
                gt.clone(),
                or_inr(lt.clone(), gt.clone(), Expr::bvar(0)),
            ),
            Expr::bvar(0),
        ],
    );
    let cast = Expr::apps(
        cst("Or.rec"),
        [
            lt.clone(),
            rest.clone(),
            Expr::lam(BinderInfo::Default, tri_ty, new_ty.clone()),
            Expr::lam(
                BinderInfo::Default,
                lt.clone(),
                or_inl(lt, gt, Expr::bvar(0)),
            ),
            Expr::lam(BinderInfo::Default, rest, middle),
            tri,
        ],
    );
    validated(state, goal, (new_ty, cast))
}

/// `@LT.lt.{0} C inst x y` with the environment's `LT C` instance, when the
/// raw spelling would not read as a comparison.
fn typeclass_lt(state: &ProofState, c: &str, carrier: &Expr, x: &Expr, y: &Expr) -> Option<Expr> {
    let inst = [format!("instLT{c}"), format!("{c}.instLT{c}")]
        .into_iter()
        .map(|n| Name::from_string(&n))
        .find(|n| state.env().get_const(n).is_some())?;
    Some(Expr::apps(
        Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
        [
            carrier.clone(),
            Expr::const_(inst, vec![]),
            x.clone(),
            y.clone(),
        ],
    ))
}

/// `h : ¬(p ∨ q)` ⟶ `¬p ∧ ¬q` (Lean: `and_not_not_of_not_or`).
fn not_or_cast(h: Expr, p: Expr, q: Expr) -> (Expr, Expr) {
    let new_ty = and(not(p.clone()), not(q.clone()));
    let left = Expr::lam(
        BinderInfo::Default,
        p.clone(),
        Expr::app(h.clone(), or_inl(p.clone(), q.clone(), Expr::bvar(0))),
    );
    let right = Expr::lam(
        BinderInfo::Default,
        q.clone(),
        Expr::app(h, or_inr(p.clone(), q.clone(), Expr::bvar(0))),
    );
    (new_ty, and_intro(not(p), not(q), left, right))
}

/// `h : ¬(p ∧ q)` ⟶ `¬p ∨ ¬q`, by cases on `Classical.em p` (Lean:
/// `Decidable.or_not_not_of_not_and` at `Classical.propDecidable`).
fn not_and_cast(h: Expr, p: Expr, q: Expr) -> (Expr, Expr) {
    let new_ty = or(not(p.clone()), not(q.clone()));
    // λ (hp : p). Or.inr (λ hq. h ⟨hp, hq⟩)
    let yes = Expr::lam(
        BinderInfo::Default,
        p.clone(),
        or_inr(
            not(p.clone()),
            not(q.clone()),
            Expr::lam(
                BinderInfo::Default,
                q.clone(),
                Expr::app(
                    h,
                    and_intro(p.clone(), q.clone(), Expr::bvar(1), Expr::bvar(0)),
                ),
            ),
        ),
    );
    let no = Expr::lam(
        BinderInfo::Default,
        not(p.clone()),
        or_inl(not(p.clone()), not(q), Expr::bvar(0)),
    );
    (new_ty.clone(), em_cases(p, new_ty, yes, no))
}

/// `h : ¬¬p` ⟶ `p`, by cases on `Classical.em p` (Lean: `Decidable.of_not_not`
/// at `Classical.propDecidable`).
fn not_not_cast(h: Expr, p: Expr) -> (Expr, Expr) {
    let yes = Expr::lam(BinderInfo::Default, p.clone(), Expr::bvar(0));
    let no = Expr::lam(
        BinderInfo::Default,
        not(p.clone()),
        false_elim(p.clone(), Expr::app(h, Expr::bvar(0))),
    );
    (p.clone(), em_cases(p.clone(), p, yes, no))
}

/// `Or.rec (motive := λ _. goal) yes no (Classical.em p)`.
fn em_cases(p: Expr, goal: Expr, yes: Expr, no: Expr) -> Expr {
    Expr::apps(
        cst("Or.rec"),
        [
            p.clone(),
            not(p.clone()),
            Expr::lam(BinderInfo::Default, or(p.clone(), not(p.clone())), goal),
            yes,
            no,
            Expr::app(cst("Classical.em"), p),
        ],
    )
}

/// `h : p → q` ⟶ `¬p ∨ q`, by cases on `Classical.em p` (Lean:
/// `Decidable.not_or_of_imp` at `Classical.propDecidable`).
fn imp_cast(h: Expr, p: Expr, q: Expr) -> (Expr, Expr) {
    let new_ty = or(not(p.clone()), q.clone());
    let yes = Expr::lam(
        BinderInfo::Default,
        p.clone(),
        or_inr(not(p.clone()), q.clone(), Expr::app(h, Expr::bvar(0))),
    );
    let no = Expr::lam(
        BinderInfo::Default,
        not(p.clone()),
        or_inl(not(p.clone()), q, Expr::bvar(0)),
    );
    (new_ty.clone(), em_cases(p, new_ty, yes, no))
}

/// `h : p ↔ q` ⟶ `(p ∧ q) ∨ (¬p ∧ ¬q)`, by cases on `Classical.em q` (Lean:
/// `Decidable.and_or_not_and_not_of_iff` at `Classical.propDecidable`).
fn iff_cast(h: Expr, p: Expr, q: Expr) -> (Expr, Expr) {
    let both = and(p.clone(), q.clone());
    let neither = and(not(p.clone()), not(q.clone()));
    let new_ty = or(both.clone(), neither.clone());
    // λ (hq : q). Or.inl ⟨Iff.mpr h hq, hq⟩
    let yes = Expr::lam(
        BinderInfo::Default,
        q.clone(),
        or_inl(
            both.clone(),
            neither.clone(),
            and_intro(
                p.clone(),
                q.clone(),
                Expr::apps(
                    cst("Iff.mpr"),
                    [p.clone(), q.clone(), h.clone(), Expr::bvar(0)],
                ),
                Expr::bvar(0),
            ),
        ),
    );
    // λ (hnq : ¬q). Or.inr ⟨λ hp. hnq (Iff.mp h hp), hnq⟩
    let not_p = Expr::lam(
        BinderInfo::Default,
        p.clone(),
        Expr::app(
            Expr::bvar(1),
            Expr::apps(cst("Iff.mp"), [p.clone(), q.clone(), h, Expr::bvar(0)]),
        ),
    );
    let no = Expr::lam(
        BinderInfo::Default,
        not(q.clone()),
        or_inr(
            both,
            neither,
            and_intro(not(p.clone()), not(q.clone()), not_p, Expr::bvar(0)),
        ),
    );
    (new_ty.clone(), em_cases(q, new_ty, yes, no))
}

fn cst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn or(a: Expr, b: Expr) -> Expr {
    Expr::apps(cst("Or"), [a, b])
}

fn and(a: Expr, b: Expr) -> Expr {
    Expr::apps(cst("And"), [a, b])
}

fn not(a: Expr) -> Expr {
    Expr::app(cst("Not"), a)
}

fn or_inl(a: Expr, b: Expr, pf: Expr) -> Expr {
    Expr::apps(cst("Or.inl"), [a, b, pf])
}

fn or_inr(a: Expr, b: Expr, pf: Expr) -> Expr {
    Expr::apps(cst("Or.inr"), [a, b, pf])
}

fn and_intro(a: Expr, b: Expr, pa: Expr, pb: Expr) -> Expr {
    Expr::apps(cst("And.intro"), [a, b, pa, pb])
}

/// `@False.elim.{0} ty pf` — `ty` is a proposition here.
fn false_elim(ty: Expr, pf: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
        [ty, pf],
    )
}
