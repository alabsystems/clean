// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reprove-lane **eliminator / case-split** proof builders.
//!
//! These prove the *statements* of hole lines (`ZNop`-proof tool-internal
//! lemmas — see [`crate::hol::isabelle_reprove`]) whose recorded proof was
//! dropped, in the reprove lane (`ISA_REPROVE=1`, default-OFF). The target is the
//! **datatype-exhaust / eliminator** family measured over the 710 hole lines: a
//! `⋀`-telescoped goal of the shape
//!
//! ```text
//! ⋀P y. [sort-premises] ⟹ (case₁ ⟹ P) ⟹ … ⟹ (caseₙ ⟹ P) ⟹ P
//! ```
//!
//! Two foundationally-provable subfamilies are handled here, both built entirely
//! from `Classical.em` / `propext` / `Or.rec` / `True.intro` (closure
//! `⊆ FOUNDATIONAL_AXIOMS`), and both **re-checked by the kernel** against the
//! embedded statement so a wrong build is rejected — never miscounted:
//!
//! 1. **Classical dichotomy** — exactly two case premises `(A ⟹ P)` and
//!    `(¬A ⟹ P)` (the second's antecedent is the embedded HOL negation of the
//!    first's). This is HOL's `n = 0 ∨ n ≠ 0` / `isl s ∨ ¬ isl s` split
//!    (`Nat`-zero, `Sum`-`isl`, …). Proved by excluded middle on `A`.
//! 2. **Boolean exhaust** — exactly two case premises `(b = True ⟹ P)` and
//!    `(b = False ⟹ P)` over a `b : Prop` scrutinee (`HOL.bool` embeds to
//!    `Prop`). Proved by excluded middle on `b` plus `propext` to turn `b`
//!    (resp. `¬b`) into the equation `b = True` (resp. `b = False`).
//!
//! The remaining eliminator holes are constructor-exhaust rules over datatypes
//! whose recursor is registered in the kernel env (`Option`/`List`/`Num`) or NOT
//! registered (the `Enum.finite_*`/`String.char`/`Quickcheck_*`/`Nitpick.*`
//! typedef-based families, which have no recursor and therefore cannot close
//! foundationally). Those are out of scope here — the kernel simply rejects a
//! build we do not produce, so they stay honest rejects.

use clean_kernel::expr::{ExprKind, FVarId};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr};

use super::super::*;

/// A leading-`Pi` telescope binder captured with a fresh `FVarId` substituted for
/// its bound variable, so domains and the goal are expressed with fvars (no de
/// Bruijn juggling); rebuilt into a matching `λ` telescope by [`rebind`].
struct TeleBinder {
    info: BinderInfo,
    dom: Expr,
    fv: FVarId,
}

/// Peel the leading `Pi` telescope of `prop`, substituting a fresh fvar for each
/// binder. Returns the captured binders (outermost first) and the goal (the
/// innermost body, fvar-expressed).
fn peel_pi_telescope(prop: &Expr) -> (Vec<TeleBinder>, Expr) {
    peel_pi_telescope_from(prop, 0xE11E_0000)
}

/// [`peel_pi_telescope`] starting the fresh-fvar counter at `base`, so a *nested*
/// peel (e.g. a case premise's own `⋀`-field telescope) does not reuse the outer
/// peel's fvar ids. The nested fvars are used only to *inspect* the shape, never
/// retained in the built term.
fn peel_pi_telescope_from(prop: &Expr, base: u64) -> (Vec<TeleBinder>, Expr) {
    let mut binders: Vec<TeleBinder> = Vec::new();
    let mut core = prop.clone();
    let mut counter: u64 = base;
    while let ExprKind::Pi(data, dom, body) = core.kind() {
        let fv = FVarId::new(counter);
        counter += 1;
        let dom_c = (**dom).clone();
        binders.push(TeleBinder {
            info: data.info,
            dom: dom_c,
            fv,
        });
        core = body.instantiate(&Expr::fvar(fv));
    }
    (binders, core)
}

/// Decompose an application spine `f a₁ … aₙ` into `(f, [a₁, …, aₙ])` (head, args
/// in left-to-right order). A non-application returns `(e, [])`.
fn app_spine(e: &Expr) -> (Expr, Vec<Expr>) {
    let mut args: Vec<Expr> = Vec::new();
    let mut cur = e.clone();
    while let ExprKind::App(f, a) = cur.kind() {
        args.push((**a).clone());
        cur = (**f).clone();
    }
    args.reverse();
    (cur, args)
}

/// Rebuild the `λ` telescope: abstract each captured binder's fvar out of `body`,
/// innermost binder first — the mirror of [`peel_pi_telescope`], so the result
/// inhabits the original `Pi`-telescoped `prop`.
fn rebind(mut body: Expr, binders: Vec<TeleBinder>) -> Expr {
    for b in binders.into_iter().rev() {
        body = Expr::lam(b.info, b.dom, body.abstract_fvar(b.fv));
    }
    body
}

/// The `(fvar, antecedent A)` of every **case premise** binder — one whose domain
/// is a non-dependent arrow `A → goal` (codomain syntactically the goal). Sort
/// premises (`True`), the scrutinee, and the goal binder itself are not arrows to
/// the goal and are skipped.
fn case_premises(binders: &[TeleBinder], goal: &Expr) -> Vec<(FVarId, Expr)> {
    binders
        .iter()
        .filter_map(|b| {
            let (a, cod) = split_arrow(&b.dom)?;
            (cod == *goal).then_some((b.fv, a))
        })
        .collect()
}

/// Statement-level proof of a **datatype-exhaust / eliminator** hole
/// (`⋀P y. … ⟹ (caseᵢ ⟹ P) ⟹ … ⟹ P`), for the two foundationally-provable
/// subfamilies — the classical dichotomy and the boolean exhaust (see the module
/// docs). `prop` is the fully-embedded statement (the `Pi`-telescoped kernel
/// `Expr`). Returns `None` when the shape is neither; the kernel re-checks any
/// returned term against `prop`, so a wrong build is rejected — never miscounted.
///
/// Foundational closure: `Classical.em` / `propext` / `Or.rec` / `False.elim` /
/// `True.intro` / `Eq` only — all `⊆ FOUNDATIONAL_AXIOMS`.
pub(crate) fn prove_eliminator(prop: &Expr) -> Option<Expr> {
    let (binders, goal) = peel_pi_telescope(prop);
    // The goal must be a bare `Prop` atom (the quantified `P`): an fvar (a peeled
    // `⋀P` binder or a discovered schematic term-param). Anything applied/compound
    // is not the eliminator shape.
    if !matches!(goal.kind(), ExprKind::FVar(_)) {
        return None;
    }
    let cases = case_premises(&binders, &goal);
    if cases.len() != 2 {
        return None;
    }
    let body = prove_dichotomy(&cases, &goal).or_else(|| prove_bool_exhaust(&cases, &goal))?;
    Some(rebind(body, binders))
}

/// Classical dichotomy: two case premises `(A ⟹ P)` and `(¬A ⟹ P)`, proved by
/// `Or.rec … (Classical.em A)`. `cases[i] = (premise-fvar, antecedent)`.
fn prove_dichotomy(cases: &[(FVarId, Expr)], goal: &Expr) -> Option<Expr> {
    let (f0, a0) = &cases[0];
    let (f1, a1) = &cases[1];
    // Orient: `(pos_fv : A → P)`, `(neg_fv : ¬A → P)` where the neg antecedent is
    // the embedded HOL negation `isabelle.def.HOL.Not A` of the pos antecedent.
    let (pos_fv, a, neg_fv) = if hol_not_arg(a1).as_ref() == Some(a0) {
        (*f0, a0.clone(), *f1)
    } else if hol_not_arg(a0).as_ref() == Some(a1) {
        (*f1, a1.clone(), *f0)
    } else {
        return None;
    };
    // pos : A → P — the positive case premise directly.
    let pos = Expr::fvar(pos_fv);
    // neg : (A → False) → P — coerce the kernel negation `hnp : A → False` into the
    // HOL negation `¬A` (defeq `A → False_enc`) and apply the ¬A case premise.
    let fh = FVarId::new(0xE11E_F00D);
    let hol_not = kernel_not_to_hol_not(&a, Expr::fvar(fh)); // : ¬A (defeq A → False_enc)
    let applied = Expr::app(Expr::fvar(neg_fv), hol_not);
    let neg = Expr::lam(
        BinderInfo::Default,
        Expr::arrow(a.clone(), Expr::const_str("False")),
        applied.abstract_fvar(fh),
    );
    Some(em_case_split(&a, goal, pos, neg))
}

/// Boolean exhaust: two case premises `(b = True ⟹ P)` and `(b = False ⟹ P)`
/// over a `b : Prop` scrutinee (`HOL.bool` embeds to `Prop`). Proved by
/// `Or.rec … (Classical.em b)`: the `b` branch turns `hb : b` into `b = True` by
/// `propext`, the `¬b` branch turns `hnb : b → False` into `b = False` by
/// `propext`. `cases[i] = (premise-fvar, antecedent)`, each antecedent a
/// `@Eq Prop b <True|False def-const>`.
fn prove_bool_exhaust(cases: &[(FVarId, Expr)], goal: &Expr) -> Option<Expr> {
    // Each antecedent must be `@Eq Prop b X` with the SAME `b` and `X` a boolean
    // literal def-const; identify which premise is the `True` case and which the
    // `False` case.
    let (b0, x0) = eq_prop_bool_lit(&cases[0].1)?;
    let (b1, x1) = eq_prop_bool_lit(&cases[1].1)?;
    if b0 != b1 {
        return None;
    }
    let b = b0;
    let (true_fv, false_fv) = match (x0, x1) {
        (BoolLit::True, BoolLit::False) => (cases[0].0, cases[1].0),
        (BoolLit::False, BoolLit::True) => (cases[1].0, cases[0].0),
        _ => return None,
    };
    // pos : b → P.  From `hb : b`, `b = True` by `propext b True (Iff.intro
    // (λ_:b. <True proof>) (λ_:True. hb))`, then apply the True case premise.
    let (true_enc, true_pf) = true_enc_and_proof();
    let true_dc = Expr::const_str("isabelle.def.HOL.True");
    let fhb = FVarId::new(0xB001_0001);
    let hb = Expr::fvar(fhb);
    // Iff.intro (b → True) (True → b): mp ignores b and returns the True witness;
    // mpr ignores the True proof and returns hb.
    let mp_true = Expr::lam(BinderInfo::Default, b.clone(), true_pf.clone());
    let mpr_true = Expr::lam(BinderInfo::Default, true_enc.clone(), hb.clone());
    let iff_true = Expr::apps(
        Expr::const_str("Iff.intro"),
        [b.clone(), true_dc.clone(), mp_true, mpr_true],
    );
    let eq_b_true = Expr::apps(
        Expr::const_str("propext"),
        [b.clone(), true_dc.clone(), iff_true],
    );
    let pos_body = Expr::app(Expr::fvar(true_fv), eq_b_true);
    let pos = Expr::lam(BinderInfo::Default, b.clone(), pos_body.abstract_fvar(fhb));
    // neg : (b → False) → P.  From `hnb : b → False`, `b = False` by `propext b
    // False (Iff.intro (λhb:b. False.elim (hnb hb)) (λhf:False. False.elim hf))`,
    // then apply the False case premise. The RHS operand is the HOL `False`
    // def-const (defeq `False_enc = ∀Q.Q`); `False.elim` discharges both directions.
    // The HOL `False` def-const `isabelle.def.HOL.False` is the IMPREDICATIVE
    // encoding `∀(Q:Prop). Q` (NOT the kernel `False` inductive), so a hypothesis
    // `hf : False_dc` yields any `Q` by APPLICATION (`hf Q`), and the kernel
    // `False` from `Classical.em`'s negation coerces INTO it via `False.elim`.
    let false_dc = Expr::const_str("isabelle.def.HOL.False");
    let fhnb = FVarId::new(0xB001_0002);
    let hnb = Expr::fvar(fhnb);
    let fhb2 = FVarId::new(0xB001_0003);
    let fhf = FVarId::new(0xB001_0004);
    // mp : b → False_dc  = λhb:b. False.elim False_dc (hnb hb)  (kernel False → ∀Q.Q)
    let absurd = Expr::app(hnb.clone(), Expr::fvar(fhb2));
    let mp_false_body = Expr::apps(
        Expr::const_str_levels("False.elim", vec![Level::zero()]),
        [false_dc.clone(), absurd],
    );
    let mp_false = Expr::lam(
        BinderInfo::Default,
        b.clone(),
        mp_false_body.abstract_fvar(fhb2),
    );
    // mpr : False_dc → b = λhf:False_dc. hf b  (`∀Q.Q` instantiated at `b` gives `b`;
    // the kernel δ-unfolds the def-const to the `∀` before applying).
    let mpr_false_body = Expr::app(Expr::fvar(fhf), b.clone());
    let mpr_false = Expr::lam(
        BinderInfo::Default,
        false_dc.clone(),
        mpr_false_body.abstract_fvar(fhf),
    );
    let iff_false = Expr::apps(
        Expr::const_str("Iff.intro"),
        [b.clone(), false_dc.clone(), mp_false, mpr_false],
    );
    let eq_b_false = Expr::apps(
        Expr::const_str("propext"),
        [b.clone(), false_dc.clone(), iff_false],
    );
    let neg_body = Expr::app(Expr::fvar(false_fv), eq_b_false);
    let neg = Expr::lam(
        BinderInfo::Default,
        Expr::arrow(b.clone(), Expr::const_str("False")),
        neg_body.abstract_fvar(fhnb),
    );
    Some(em_case_split(&b, goal, pos, neg))
}

/// Statement-level proof of a **constructor-exhaust** eliminator hole over a
/// registered kernel inductive `T` (`Option`/`List`/`Sum`/`Prod`/`Nat`/`Num`) — the
/// `⋀`-telescoped goal
///
/// ```text
/// ⋀P y. (y = C₁ ⟹ P) ⟹ (⋀args. y = C₂ args ⟹ P) ⟹ … ⟹ P
/// ```
///
/// in its **fresh-binder** form: each case premise's constructor is applied to that
/// premise's own `⋀`-bound field variables (NOT projections of `y`). This is the
/// datatype `.exhaust` rule (`option.exhaust`, `list.exhaust`, …).
///
/// Proof — the kernel's auto-generated `T.casesOn` with the motive
/// `fun x => (y = x) → P` (`P` is constant in `x`; the equation carries the case
/// information):
///
/// ```text
/// @T.casesOn.{0, ‹T-levels›} ‹tparams› (fun x:D => @Eq D y x → P) y
///     prem₁ … premₙ  (@Eq.refl D y)
/// ```
///
/// `casesOn` substitutes `y := Cᵢ fields` into the motive, so branch `i`'s expected
/// type is exactly `⋀fields. @Eq D y (Cᵢ fields) → P` — which is premise `i`
/// verbatim, so we pass the premise binders straight through as the minors.
/// Applying the whole `casesOn` (of type `motive y = (@Eq D y y → P)`) to
/// `@Eq.refl D y` discharges the motive at `y` and yields `P`.
///
/// Foundational closure: `T.casesOn` of a kernel inductive + `Eq`/`Eq.refl` only —
/// all `⊆ FOUNDATIONAL_AXIOMS` (a non-`Prop` datatype eliminating INTO `Prop` is
/// the always-allowed small-elimination direction). The kernel re-checks the built
/// term against `prop` (constructor order, field types, universe levels), so a
/// wrong build is rejected and never miscounted. The **projection** form
/// (`y = Suc (pred y)` / `y = Inl (projl y)`, whose `casesOn` minor would need a
/// `⋀fields` binder the premise lacks) is declined up front — its constructor
/// arguments mention `y`.
pub(crate) fn prove_ctor_exhaust(prop: &Expr) -> Option<Expr> {
    let (binders, goal) = peel_pi_telescope(prop);
    // The goal must be a bare `Prop` atom (the quantified motive `P`).
    if !matches!(goal.kind(), ExprKind::FVar(_)) {
        return None;
    }
    // Walk the telescope collecting the case premises (in telescope order, which is
    // constructor order for an `.exhaust` rule) and the shared scrutinee + `Eq`
    // operand type/levels.
    let mut minors: Vec<FVarId> = Vec::new();
    let mut scrut: Option<FVarId> = None;
    let mut eq_ty_lvls: Option<(Expr, Vec<Level>)> = None;
    for (idx, b) in binders.iter().enumerate() {
        // A case premise is `⋀fields. (@Eq D y (Cᵢ fields)) → P`. Both the `⋀`-field
        // binders and the trailing `→` are `Pi`, so peel the WHOLE `Pi` telescope
        // (disjoint fvar base): the antecedent `@Eq …` is the last binder's domain
        // and the final body must be the goal `P`. (A binder that is not a case
        // premise — the motive, scrutinee, type param, or sort premise — has no
        // leading `Pi`, so it peels to an empty telescope and is skipped.)
        let (inner_binders, inner_body) =
            peel_pi_telescope_from(&b.dom, 0x0CE0_0000 + (idx as u64) * 0x1000);
        let Some(ante_binder) = inner_binders.last() else {
            continue;
        };
        if inner_body != goal {
            continue;
        }
        let ante = &ante_binder.dom;
        let Some((alpha, lhs, rhs, lvls)) = eq_app_three(ante) else {
            continue;
        };
        // The equation's LHS is the scrutinee (a peeled `⋀y` binder fvar).
        let ExprKind::FVar(s_fv) = lhs.kind() else {
            continue;
        };
        let s_fv = *s_fv;
        // Fresh-binder form only: the constructor's arguments must NOT mention the
        // scrutinee. The projection form `Cᵢ (projᵢ y)` does — decline it (its
        // `casesOn` minor needs a `⋀fields` binder the premise lacks; the kernel
        // would reject the build anyway).
        if rhs.abstract_fvar(s_fv) != rhs {
            continue;
        }
        // The RHS must be constructor-headed (`Const` applied to tparams + fields).
        let (head, _args) = app_spine(&rhs);
        if !matches!(head.kind(), ExprKind::Const(_, _)) {
            continue;
        }
        match scrut {
            Some(prev) if prev != s_fv => return None, // mixed scrutinees ⇒ not this shape
            None => {
                scrut = Some(s_fv);
                eq_ty_lvls = Some((alpha, lvls));
            }
            _ => {}
        }
        minors.push(b.fv);
    }
    let scrut_fv = scrut?;
    let (d_ty, eq_levels) = eq_ty_lvls?;
    // An exhaust rule has ≥ 2 constructor cases (the arity/order is re-checked by
    // the kernel against `T.casesOn`, so this is only a cheap pre-filter).
    if minors.len() < 2 {
        return None;
    }
    // `D = T tparams…`: read `T`'s name + its universe args and the type params off
    // the `Eq` operand type (the fully-embedded scrutinee type).
    let (t_head, t_args) = app_spine(&d_ty);
    let ExprKind::Const(t_name, t_levels) = t_head.kind() else {
        return None;
    };
    let cases_name = Name::from_string(&format!("{t_name}.casesOn"));
    // `T.casesOn.{motive_univ, T-levels}` — the motive lands in `Prop` (Sort 0).
    let mut cases_levels: Vec<Level> = Vec::with_capacity(t_levels.len() + 1);
    cases_levels.push(Level::zero());
    cases_levels.extend(t_levels.iter().cloned());
    // motive := fun (x : D) => @Eq D y x → P
    let fx = FVarId::new(0x0CE0_FFFF);
    let eq_x = Expr::apps(
        Expr::const_str_levels("Eq", eq_levels.clone()),
        [d_ty.clone(), Expr::fvar(scrut_fv), Expr::fvar(fx)],
    );
    let motive_body = Expr::arrow(eq_x, goal.clone());
    let motive = Expr::lam(
        BinderInfo::Default,
        d_ty.clone(),
        motive_body.abstract_fvar(fx),
    );
    // @T.casesOn ‹tparams› motive y minor₁ … minorₙ   :   (@Eq D y y → P)
    let mut app_args: Vec<Expr> = Vec::with_capacity(t_args.len() + 2 + minors.len());
    app_args.extend(t_args);
    app_args.push(motive);
    app_args.push(Expr::fvar(scrut_fv));
    app_args.extend(minors.iter().map(|fv| Expr::fvar(*fv)));
    let cases_applied = Expr::apps(Expr::const_(cases_name, cases_levels), app_args);
    // … applied to `@Eq.refl D y : @Eq D y y` discharges the motive at `y` ⇒ `P`.
    let eq_refl = Expr::apps(
        Expr::const_str_levels("Eq.refl", eq_levels),
        [d_ty, Expr::fvar(scrut_fv)],
    );
    let body = Expr::app(cases_applied, eq_refl);
    Some(rebind(body, binders))
}

/// A boolean literal on the RHS of a `b = <lit>` case-premise antecedent.
enum BoolLit {
    True,
    False,
}

/// If `e` is `@Eq Prop b X` with `X` the HOL `True`/`False` def-const, return
/// `(b, which-literal)`. The `Eq` operand type must be `Prop` (`HOL.bool`).
fn eq_prop_bool_lit(e: &Expr) -> Option<(Expr, BoolLit)> {
    let (alpha, lhs, rhs, _levels) = eq_app_three(e)?;
    if !matches!(alpha.kind(), ExprKind::Sort(l) if *l == Level::zero()) {
        return None;
    }
    let ExprKind::Const(name, _) = rhs.kind() else {
        return None;
    };
    if *name == Name::from_string("isabelle.def.HOL.True") {
        Some((lhs, BoolLit::True))
    } else if *name == Name::from_string("isabelle.def.HOL.False") {
        Some((lhs, BoolLit::False))
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `Π(P:Prop)(A:Prop)(h1:A→P)(h2:(¬A)→P). P` — a classical dichotomy — is
    /// recognized and a `λ`-telescope proof of the right arity is produced. Built
    /// by fvar-abstraction (as the real embedding does) so the de Bruijn structure
    /// is correct by construction.
    #[test]
    fn test_prove_eliminator_dichotomy_shape_produces_lambda_telescope() {
        let fp = FVarId::new(1);
        let fa = FVarId::new(2);
        let fh1 = FVarId::new(3);
        let fh2 = FVarId::new(4);
        let goal = Expr::fvar(fp);
        let a = Expr::fvar(fa);
        let h1_dom = Expr::arrow(a.clone(), goal.clone());
        let not_a = Expr::app(Expr::const_str("isabelle.def.HOL.Not"), a);
        let h2_dom = Expr::arrow(not_a, goal.clone());
        // Wrap innermost-first: goal, then Π(h2), Π(h1), Π(A), Π(P).
        let mut prop = goal;
        prop = Expr::pi(BinderInfo::Default, h2_dom, prop.abstract_fvar(fh2));
        prop = Expr::pi(BinderInfo::Default, h1_dom, prop.abstract_fvar(fh1));
        prop = Expr::pi(BinderInfo::Default, Expr::prop(), prop.abstract_fvar(fa));
        prop = Expr::pi(BinderInfo::Default, Expr::prop(), prop.abstract_fvar(fp));
        let proof = prove_eliminator(&prop).expect("dichotomy shape should be recognized");
        // The proof must be a 4-deep `λ` telescope mirroring the `Π` telescope.
        let mut e = &proof;
        for _ in 0..4 {
            match e.kind() {
                ExprKind::Lam(_, _, body) => e = body,
                other => panic!("expected 4 nested lambdas, got {other:?}"),
            }
        }
    }

    /// A non-eliminator statement (a bare reflexive equation telescope) is
    /// declined (`None`), so the arm never fires outside its shape.
    #[test]
    fn test_prove_eliminator_declines_non_eliminator() {
        // Π(x:Nat). x  (goal is a bound var but there are no case premises).
        let prop = Expr::pi(BinderInfo::Default, Expr::const_str("Nat"), Expr::bvar(0));
        assert!(
            prove_eliminator(&prop).is_none(),
            "no case premises ⇒ declined"
        );
    }

    /// Build `@Eq (Option Nat) y rhs` with a fixed level, as the embedding spells a
    /// case-premise antecedent.
    fn eq_opt_nat(y: Expr, rhs: Expr) -> Expr {
        let d = Expr::apps(
            Expr::const_str_levels("Option", vec![Level::zero()]),
            [Expr::const_str("Nat")],
        );
        Expr::apps(
            Expr::const_str_levels("Eq", vec![Level::zero()]),
            [d, y, rhs],
        )
    }

    fn option_none() -> Expr {
        Expr::apps(
            Expr::const_str_levels("Option.none", vec![Level::zero()]),
            [Expr::const_str("Nat")],
        )
    }

    fn option_some(a: Expr) -> Expr {
        Expr::apps(
            Expr::const_str_levels("Option.some", vec![Level::zero()]),
            [Expr::const_str("Nat"), a],
        )
    }

    /// `option.exhaust` in fresh-binder form —
    /// `⋀P y. (y=None ⟹ P) ⟹ (⋀a. y=Some a ⟹ P) ⟹ P` — is recognized and a
    /// `λ`-telescope proof headed by `Option.casesOn` is produced. Built by
    /// fvar-abstraction so the de Bruijn structure is correct by construction.
    #[test]
    fn test_prove_ctor_exhaust_option_fresh_binder_produces_cases_on() {
        let fp = FVarId::new(1);
        let fy = FVarId::new(2);
        let fh1 = FVarId::new(3);
        let fh2 = FVarId::new(4);
        let fa = FVarId::new(5);
        let goal = Expr::fvar(fp);
        let opt_nat = Expr::apps(
            Expr::const_str_levels("Option", vec![Level::zero()]),
            [Expr::const_str("Nat")],
        );
        // h1 : (y = None) → P
        let h1_dom = Expr::arrow(eq_opt_nat(Expr::fvar(fy), option_none()), goal.clone());
        // h2 : Π(a:Nat). (y = Some a) → P
        let h2_inner = Expr::arrow(
            eq_opt_nat(Expr::fvar(fy), option_some(Expr::fvar(fa))),
            goal.clone(),
        );
        let h2_dom = Expr::pi(
            BinderInfo::Default,
            Expr::const_str("Nat"),
            h2_inner.abstract_fvar(fa),
        );
        // Wrap innermost-first: goal, Π(h2), Π(h1), Π(y:Option Nat), Π(P:Prop).
        let mut prop = goal;
        prop = Expr::pi(BinderInfo::Default, h2_dom, prop.abstract_fvar(fh2));
        prop = Expr::pi(BinderInfo::Default, h1_dom, prop.abstract_fvar(fh1));
        prop = Expr::pi(BinderInfo::Default, opt_nat, prop.abstract_fvar(fy));
        prop = Expr::pi(BinderInfo::Default, Expr::prop(), prop.abstract_fvar(fp));
        let proof =
            prove_ctor_exhaust(&prop).expect("fresh-binder option.exhaust should be recognized");
        // 4-deep `λ` telescope mirroring the `Π` telescope …
        let mut e = &proof;
        for _ in 0..4 {
            match e.kind() {
                ExprKind::Lam(_, _, body) => e = body,
                other => panic!("expected 4 nested lambdas, got {other:?}"),
            }
        }
        // … whose body is headed by `Option.casesOn` (applied to Eq.refl).
        let (head, _) = app_spine(e);
        let (head2, _) = app_spine(&head); // peel the trailing Eq.refl application
        assert!(
            matches!(head2.kind(), ExprKind::Const(n, _) if *n == Name::from_string("Option.casesOn")),
            "ctor-exhaust proof must be headed by Option.casesOn, got {:?}",
            head2.kind()
        );
    }

    /// The **projection** form — `⋀P y. (y=None ⟹ P) ⟹ (y = Some (the y) ⟹ P) ⟹ P`
    /// — is declined (`None`): its second case's constructor argument mentions the
    /// scrutinee, so `casesOn` cannot supply the missing `⋀a` field binder.
    #[test]
    fn test_prove_ctor_exhaust_declines_projection_form() {
        let fp = FVarId::new(1);
        let fy = FVarId::new(2);
        let fh1 = FVarId::new(3);
        let fh2 = FVarId::new(4);
        let goal = Expr::fvar(fp);
        let opt_nat = Expr::apps(
            Expr::const_str_levels("Option", vec![Level::zero()]),
            [Expr::const_str("Nat")],
        );
        let the_y = Expr::apps(
            Expr::const_str_levels("Option.option.the", vec![Level::zero()]),
            [Expr::const_str("Nat"), Expr::fvar(fy)],
        );
        let h1_dom = Expr::arrow(eq_opt_nat(Expr::fvar(fy), option_none()), goal.clone());
        let h2_dom = Expr::arrow(eq_opt_nat(Expr::fvar(fy), option_some(the_y)), goal.clone());
        let mut prop = goal;
        prop = Expr::pi(BinderInfo::Default, h2_dom, prop.abstract_fvar(fh2));
        prop = Expr::pi(BinderInfo::Default, h1_dom, prop.abstract_fvar(fh1));
        prop = Expr::pi(BinderInfo::Default, opt_nat, prop.abstract_fvar(fy));
        prop = Expr::pi(BinderInfo::Default, Expr::prop(), prop.abstract_fvar(fp));
        assert!(
            prove_ctor_exhaust(&prop).is_none(),
            "projection form (Some (the y)) must be declined"
        );
    }
}
