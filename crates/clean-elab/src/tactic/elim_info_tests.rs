// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for [`super::elim_info`] — the port of Lean's `getElimExprInfo`.
//!
//! Every eliminator type here is built by hand from the *real* Lean 4
//! declaration it names, so the analysis is checked against the shapes it must
//! serve rather than against convenient fictions.

use super::elim_info::{get_elim_info, match_pattern, telescope, ElimInfoError, ElimSolution};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

fn nat() -> Expr {
    Expr::const_str("Nat")
}

fn u() -> Level {
    Level::Param(Name::from_string("u"))
}

/// `Nat.strongRecOn.{u} {motive : Nat → Sort u} (n : Nat)
///     (ind : ∀ n, (∀ m, m < n → motive m) → motive n) : motive n`
///
/// Verbatim from `Init/WF.lean:246`. The motive PRECEDES the target and the
/// alternative's telescope is nested — the two properties that the fixed
/// recursor order in `induction.rs` cannot express.
fn nat_strong_rec_on_type() -> Expr {
    // Inside `ind`'s type, after descending k binders, `motive` is BVar(1 + k).
    // ∀ m, m < n → motive m   (n is BVar(0) at the point `ind`'s body starts)
    let lt = |a: Expr, b: Expr| Expr::apps(Expr::const_str("Nat.lt"), [a, b]);
    let ih = Expr::pi(
        BinderInfo::Default,
        nat(),
        // m : BVar(0), n : BVar(1), motive : BVar(3)
        Expr::pi(
            BinderInfo::Default,
            lt(Expr::bvar(0), Expr::bvar(1)),
            Expr::app(Expr::bvar(4), Expr::bvar(1)),
        ),
    );
    let ind_ty = Expr::pi(
        BinderInfo::Default,
        nat(),
        // motive is BVar(1) here (past `n`), BVar(2) after `ih`
        Expr::pi(
            BinderInfo::Default,
            ih,
            Expr::app(Expr::bvar(3), Expr::bvar(1)),
        ),
    );
    Expr::pi(
        BinderInfo::Implicit,
        Expr::pi(BinderInfo::Default, nat(), Expr::sort(u())),
        Expr::pi(
            BinderInfo::Default,
            nat(),
            Expr::pi(
                BinderInfo::Default,
                ind_ty,
                // conclusion: motive n — motive = BVar(2), n = BVar(1)
                Expr::app(Expr::bvar(2), Expr::bvar(1)),
            ),
        ),
    )
}

/// `Nat.caseStrongRecOn.{u} {motive : Nat → Sort u} (a : Nat) (zero : motive 0)
///     (ind : ∀ n, (∀ m, m ≤ n → motive m) → motive (succ n)) : motive a`
///
/// From `Init/WF.lean:255`. Two alternatives with different arities, and the
/// second one's conclusion is `motive (succ n)` — a motive application whose
/// argument is *not* a binder, which is fine inside an alternative (only the
/// eliminator's own conclusion must apply the motive to binders).
fn nat_case_strong_rec_on_type() -> Expr {
    let le = |a: Expr, b: Expr| Expr::apps(Expr::const_str("Nat.le"), [a, b]);
    let succ = |a: Expr| Expr::app(Expr::const_str("Nat.succ"), a);
    let ih = Expr::pi(
        BinderInfo::Default,
        nat(),
        Expr::pi(
            BinderInfo::Default,
            le(Expr::bvar(0), Expr::bvar(1)),
            Expr::app(Expr::bvar(5), Expr::bvar(1)),
        ),
    );
    let ind_ty = Expr::pi(
        BinderInfo::Default,
        nat(),
        Expr::pi(
            BinderInfo::Default,
            ih,
            Expr::app(Expr::bvar(4), succ(Expr::bvar(1))),
        ),
    );
    Expr::pi(
        BinderInfo::Implicit,
        Expr::pi(BinderInfo::Default, nat(), Expr::sort(u())),
        Expr::pi(
            BinderInfo::Default,
            nat(),
            Expr::pi(
                BinderInfo::Default,
                // zero : motive 0
                Expr::app(Expr::bvar(1), Expr::const_str("Nat.zero")),
                Expr::pi(
                    BinderInfo::Default,
                    ind_ty,
                    Expr::app(Expr::bvar(3), Expr::bvar(2)),
                ),
            ),
        ),
    )
}

#[test]
fn test_elim_info_nat_strong_rec_on_shape() {
    let info = get_elim_info(&nat_strong_rec_on_type()).expect("strongRecOn is an eliminator");
    assert_eq!(info.num_binders, 3);
    assert_eq!(info.motive_pos, 0, "motive precedes the target");
    assert_eq!(info.targets_pos, vec![1]);
    assert_eq!(info.num_complex_motive_args, 0);
    assert_eq!(info.alts_info.len(), 1, "one alternative, not one per ctor");
    assert_eq!(info.alts_info[0].binder_pos, 2);
    assert_eq!(
        info.alts_info[0].num_fields, 2,
        "`ind` binds n and the strong induction hypothesis"
    );
    assert!(info.alts_info[0].proves_motive);
}

#[test]
fn test_elim_info_nat_case_strong_rec_on_shape() {
    let info =
        get_elim_info(&nat_case_strong_rec_on_type()).expect("caseStrongRecOn is an eliminator");
    assert_eq!(info.num_binders, 4);
    assert_eq!(info.motive_pos, 0);
    assert_eq!(info.targets_pos, vec![1]);
    let arities: Vec<usize> = info.alts_info.iter().map(|a| a.num_fields).collect();
    assert_eq!(
        arities,
        vec![0, 2],
        "zero binds nothing, ind binds n and ih"
    );
    assert!(info.alts_info.iter().all(|a| a.proves_motive));
}

/// A recursor-ordered eliminator (motive, alternatives, target LAST) must be
/// read just as well — the analysis is order-independent, which is what lets
/// the same code serve `Nat.rec`-shaped and `strongRecOn`-shaped eliminators.
#[test]
fn test_elim_info_recursor_order_target_last() {
    // {motive : Nat → Sort u} (zero : motive 0)
    //   (succ : ∀ n, motive n → motive (succ n)) (t : Nat) : motive t
    let succ = |a: Expr| Expr::app(Expr::const_str("Nat.succ"), a);
    let succ_ty = Expr::pi(
        BinderInfo::Default,
        nat(),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(Expr::bvar(2), Expr::bvar(0)),
            Expr::app(Expr::bvar(3), succ(Expr::bvar(1))),
        ),
    );
    let ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::pi(BinderInfo::Default, nat(), Expr::sort(u())),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(Expr::bvar(0), Expr::const_str("Nat.zero")),
            Expr::pi(
                BinderInfo::Default,
                succ_ty,
                Expr::pi(
                    BinderInfo::Default,
                    nat(),
                    Expr::app(Expr::bvar(3), Expr::bvar(0)),
                ),
            ),
        ),
    );
    let info = get_elim_info(&ty).expect("recursor-shaped eliminator");
    assert_eq!(info.motive_pos, 0);
    assert_eq!(info.targets_pos, vec![3], "target is the LAST binder");
    assert_eq!(
        info.alts_info
            .iter()
            .map(|a| a.binder_pos)
            .collect::<Vec<_>>(),
        vec![1, 2]
    );
}

/// Implicit binders that are neither motive nor target are NOT alternatives —
/// Lean only collects explicit ones (`xDecl.binderInfo.isExplicit`).
#[test]
fn test_elim_info_implicit_parameter_is_not_an_alternative() {
    // {α : Type u} {motive : α → Prop} (a : α) (h : motive a) : motive a
    let ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(Level::succ(u())),
        Expr::pi(
            BinderInfo::Implicit,
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::prop()),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(Expr::bvar(1), Expr::bvar(0)),
                    Expr::app(Expr::bvar(2), Expr::bvar(1)),
                ),
            ),
        ),
    );
    let info = get_elim_info(&ty).expect("eliminator with an implicit type parameter");
    assert_eq!(info.motive_pos, 1);
    assert_eq!(info.targets_pos, vec![2]);
    assert_eq!(
        info.alts_info
            .iter()
            .map(|a| a.binder_pos)
            .collect::<Vec<_>>(),
        vec![3],
        "the implicit `α` at position 0 is a parameter, not an alternative"
    );
}

/// A plain function is not an eliminator: its conclusion's head is a constant,
/// not one of its own binders. Must be rejected, never guessed at.
#[test]
fn test_elim_info_rejects_non_eliminator() {
    // (n : Nat) (m : Nat) : Nat
    let ty = Expr::pi(
        BinderInfo::Default,
        nat(),
        Expr::pi(BinderInfo::Default, nat(), nat()),
    );
    assert_eq!(
        get_elim_info(&ty),
        Err(ElimInfoError::ConclusionNotMotiveApplication)
    );
}

/// A binder applied to nothing in the conclusion cannot be a motive.
#[test]
fn test_elim_info_rejects_unapplied_motive() {
    // {p : Prop} (h : p) : p
    let ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::prop(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    assert_eq!(get_elim_info(&ty), Err(ElimInfoError::MotiveNotApplied));
}

/// The motive's declared arity must match how the conclusion applies it.
#[test]
fn test_elim_info_rejects_motive_arity_mismatch() {
    // {motive : Nat → Nat → Prop} (n : Nat) : motive n
    let ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::pi(
            BinderInfo::Default,
            nat(),
            Expr::pi(BinderInfo::Default, nat(), Expr::prop()),
        ),
        Expr::pi(
            BinderInfo::Default,
            nat(),
            Expr::app(Expr::bvar(1), Expr::bvar(0)),
        ),
    );
    assert_eq!(
        get_elim_info(&ty),
        Err(ElimInfoError::MotiveTypeMismatch {
            motive_params: 2,
            motive_args: 1,
        })
    );
}

/// A motive applied to a computed expression yields a "complex" motive
/// argument, which the bounded driver refuses (it needs index unification).
#[test]
fn test_elim_info_counts_complex_motive_args() {
    // {motive : Nat → Prop} (n : Nat) (h : motive (succ n)) : motive (succ n)
    let succ = |a: Expr| Expr::app(Expr::const_str("Nat.succ"), a);
    let ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::pi(BinderInfo::Default, nat(), Expr::prop()),
        Expr::pi(
            BinderInfo::Default,
            nat(),
            Expr::pi(
                BinderInfo::Default,
                Expr::app(Expr::bvar(1), succ(Expr::bvar(0))),
                Expr::app(Expr::bvar(2), succ(Expr::bvar(1))),
            ),
        ),
    );
    let info = get_elim_info(&ty).expect("well-formed, just not one we serve");
    assert_eq!(info.targets_pos, Vec::<usize>::new());
    assert_eq!(info.num_complex_motive_args, 1);
}

#[test]
fn test_telescope_stops_at_non_pi() {
    let ty = Expr::pi(BinderInfo::Default, nat(), nat());
    let (binders, conclusion) = telescope(&ty);
    assert_eq!(binders.len(), 1);
    assert!(matches!(conclusion.kind(), ExprKind::Const(_, _)));
}

// ---------------------------------------------------------------------------
// First-order matching — the level solver. Clean's `Level` has no metavariable
// constructor, so these assignments are the only way universes get determined.
// ---------------------------------------------------------------------------

#[test]
fn test_match_pattern_solves_motive_universe_to_prop() {
    let params = vec![Name::from_string("u")];
    let mut sol = ElimSolution::default();
    match_pattern(&Expr::sort(u()), &Expr::prop(), 0, &params, &mut sol);
    assert_eq!(sol.levels.len(), 1);
    assert_eq!(sol.levels[0].0, Name::from_string("u"));
    assert_eq!(sol.levels[0].1, Level::zero(), "Prop is Sort 0");
}

#[test]
fn test_match_pattern_solves_type_parameter_from_major_premise() {
    // Pattern `List α` where α is telescope binder 0, actual `List Nat`.
    let params: Vec<Name> = Vec::new();
    let pattern = Expr::app(Expr::const_str("List"), Expr::bvar(0));
    let actual = Expr::app(Expr::const_str("List"), nat());
    let mut sol = ElimSolution::default();
    match_pattern(&pattern, &actual, 1, &params, &mut sol);
    assert_eq!(sol.binder(0), Some(&nat()));
}

#[test]
fn test_match_pattern_solves_level_through_a_constant() {
    // `List.{u} α` against `List.{0} Nat` pins u := 0.
    let params = vec![Name::from_string("u")];
    let pattern = Expr::app(Expr::const_str_levels("List", vec![u()]), Expr::bvar(0));
    let actual = Expr::app(Expr::const_str_levels("List", vec![Level::zero()]), nat());
    let mut sol = ElimSolution::default();
    match_pattern(&pattern, &actual, 1, &params, &mut sol);
    assert_eq!(sol.binder(0), Some(&nat()));
    assert_eq!(sol.levels, vec![(Name::from_string("u"), Level::zero())]);
}

/// A pattern variable bound by a binder the walk descended under is NOT an
/// eliminator parameter, and an actual term that mentions a local binder must
/// never escape into a solution. Getting this wrong would substitute a
/// scope-escaping term into the proof.
#[test]
fn test_match_pattern_does_not_capture_locally_bound_variables() {
    let params: Vec<Name> = Vec::new();
    // Pattern `∀ x : Nat, f x` vs actual `∀ x : Nat, f x`: the inner BVar(0) is
    // the local `x` in both, not telescope binder 0.
    let pattern = Expr::pi(
        BinderInfo::Default,
        nat(),
        Expr::app(Expr::const_str("f"), Expr::bvar(0)),
    );
    let actual = pattern.clone();
    let mut sol = ElimSolution::default();
    match_pattern(&pattern, &actual, 1, &params, &mut sol);
    assert_eq!(
        sol.binder(0),
        None,
        "the local binder must not be read as eliminator parameter 0"
    );
}

/// REGRESSION: an explicit binder that PRECEDES the motive must not be given a
/// fabricated motive index.
///
/// Found by sweeping all 93,251 constants of the real imported `Init`: the
/// first version used `u32::MAX` as the "cannot mention the motive" sentinel
/// and `altArity` incremented it once per binder, so any such alternative
/// panicked with `attempt to add with overflow` in debug and silently wrapped
/// to `BVar(0)` in release — which could then report `proves_motive = true` for
/// an alternative that proves nothing of the sort.
#[test]
fn test_alt_arity_explicit_binder_before_motive_does_not_overflow() {
    // (b : Nat → Nat) {motive : Nat → Prop} (n : Nat) (step : motive n) : motive n
    // `b` is explicit, precedes the motive, and its type has a Pi binder.
    let ty = Expr::pi(
        BinderInfo::Default,
        Expr::pi(BinderInfo::Default, nat(), nat()),
        Expr::pi(
            BinderInfo::Implicit,
            Expr::pi(BinderInfo::Default, nat(), Expr::prop()),
            Expr::pi(
                BinderInfo::Default,
                nat(),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(Expr::bvar(1), Expr::bvar(0)),
                    Expr::app(Expr::bvar(2), Expr::bvar(1)),
                ),
            ),
        ),
    );
    let info = get_elim_info(&ty).expect("well-formed eliminator");
    assert_eq!(info.motive_pos, 1);
    assert_eq!(info.targets_pos, vec![2]);
    let before_motive = info
        .alts_info
        .iter()
        .find(|a| a.binder_pos == 0)
        .expect("`b` is an explicit non-motive non-target binder, so an alternative");
    assert!(
        !before_motive.proves_motive,
        "a binder declared before the motive cannot conclude with it"
    );
    assert_eq!(before_motive.num_fields, 1);
}
