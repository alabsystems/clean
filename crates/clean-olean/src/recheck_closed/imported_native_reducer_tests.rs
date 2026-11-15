// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! An imported declaration whose NAME the consumer's base also evaluates by a
//! native reducer: admitted, and given exactly one meaning.
//!
//! Until 2026-09-28 the gate refused every such declaration
//! (`NativeReducerCollision`), because the kernel once fired a reducer on the
//! name alone and would have computed with it instead of the declaration.
//! Since the kernel's native-fold authority (`clean-kernel/src/env/
//! native_fold_authority.rs`) a reducer fires only when its head's δ-closure
//! in the checking environment is canonical, so the refusal protected nothing
//! and refused Lean's own `Init` (v4.30's `BitVec.ofFin`, and through it every
//! `String`- or `autoParam`-reaching cone of Mathlib). These arms pin both
//! halves: the honest citation is re-admitted, and the reducer's meaning is
//! NOT available to a citation that needs it.

use super::ImportedConeGate;
use crate::recheck_closed::ClosedRecheckRefusal;
use clean_kernel::env::{
    ConstantInfo, ConstantKind, Environment, Reducibility, TrustedEnvExt as _,
};
use clean_kernel::expr::{BinderInfo, Expr, ExprKind, Literal};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use std::collections::BTreeSet;

fn n(s: &str) -> Name {
    Name::interned(s)
}

fn nat() -> Expr {
    Expr::const_(n("Nat"), vec![])
}

fn one() -> Level {
    Level::succ(Level::zero())
}

/// `@Eq.{1} Nat a b`.
fn nat_eq(a: Expr, b: Expr) -> Expr {
    [nat(), a, b]
        .into_iter()
        .fold(Expr::const_(n("Eq"), vec![one()]), Expr::app)
}

/// `@Eq.refl.{1} Nat a`.
fn nat_refl(a: Expr) -> Expr {
    [nat(), a]
        .into_iter()
        .fold(Expr::const_(n("Eq.refl"), vec![one()]), Expr::app)
}

/// `V.f n ↦ 0` on a literal: a reducer that gives `V.f` a meaning its
/// declaration (`fun n => n`) does not have.
fn to_zero(args: &[&Expr]) -> Option<Expr> {
    match args {
        [arg] if matches!(arg.kind(), ExprKind::Lit(Literal::Nat(_))) => Some(Expr::nat_lit(0)),
        _ => None,
    }
}

/// A base holding Lean's `Eq` and `Nat` (through the kernel's own checking
/// path) and a native reducer registered for `V.f`, a name it does not
/// declare — the prelude does this for real names (`BitVec.ofFin`, …).
fn base() -> Environment {
    let mut env = Environment::default();
    let u = Level::param(n("u"));
    let eq_u = Expr::const_(n("Eq"), vec![u.clone()]);
    env.add_inductive_core(InductiveDecl {
        level_params: vec![n("u")],
        num_params: 2,
        types: vec![InductiveType {
            name: n("Eq"),
            type_: Expr::pi(
                BinderInfo::Implicit,
                Expr::sort(u.clone()),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(0),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::bvar(1),
                        Expr::sort(Level::zero()),
                    ),
                ),
            ),
            constructors: vec![Constructor {
                name: n("Eq.refl"),
                type_: Expr::pi(
                    BinderInfo::Implicit,
                    Expr::sort(u),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::bvar(0),
                        [Expr::bvar(1), Expr::bvar(0), Expr::bvar(0)]
                            .into_iter()
                            .fold(eq_u, Expr::app),
                    ),
                ),
            }],
        }],
    })
    .expect("Eq must be admissible");
    env.add_inductive_core(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: n("Nat"),
            type_: Expr::sort(one()),
            constructors: vec![
                Constructor {
                    name: n("Nat.zero"),
                    type_: nat(),
                },
                Constructor {
                    name: n("Nat.succ"),
                    type_: Expr::pi(BinderInfo::Default, nat(), nat()),
                },
            ],
        }],
    })
    .expect("Nat must be admissible");
    env.register_native_reducer(n("V.f"), to_zero);
    env
}

fn import(env: &mut Environment, name: &str, kind: ConstantKind, type_: Expr, value: Expr) {
    let rejected = env.extend_constants_structural(std::iter::once(ConstantInfo {
        name: n(name),
        level_params: vec![],
        type_,
        value: Some(value),
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind,
    }));
    assert!(
        rejected.is_empty(),
        "structural tier refused {name}: {rejected:?}"
    );
}

/// The consumer's environment after an import supplies `V.f := fun n => n`
/// and two citations of it: `V.good : V.f 5 = 5` (true of the declaration)
/// and `V.bad : V.f 5 = 0` (true only of the base's reducer). Both are
/// `Eq.refl`, so each checks only if `V.f 5` reduces to its right-hand side.
fn imported(base: &Environment) -> Environment {
    let mut env = base.clone();
    import(
        &mut env,
        "V.f",
        ConstantKind::Definition,
        Expr::pi(BinderInfo::Default, nat(), nat()),
        Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)),
    );
    let f5 = Expr::app(Expr::const_(n("V.f"), vec![]), Expr::nat_lit(5));
    import(
        &mut env,
        "V.good",
        ConstantKind::Theorem,
        nat_eq(f5.clone(), Expr::nat_lit(5)),
        nat_refl(Expr::nat_lit(5)),
    );
    import(
        &mut env,
        "V.bad",
        ConstantKind::Theorem,
        nat_eq(f5, Expr::nat_lit(0)),
        nat_refl(Expr::nat_lit(0)),
    );
    env
}

/// The attack is real: the base's reducer computes `V.f 5 = 0`.
#[test]
fn the_fixture_reducer_computes_a_meaning_the_declaration_does_not_have() {
    let base = base();
    let reducer = base
        .get_native_reducer(&n("V.f"))
        .expect("the base registers a reducer for V.f");
    assert_eq!(reducer(&[&Expr::nat_lit(5)]), Some(Expr::nat_lit(0)));
}

/// The honest citation is re-admitted over the base: `V.f` is not refused for
/// sharing its name with a reducer (it was, as `NativeReducerCollision`,
/// before 2026-09-28).
#[test]
fn a_declaration_sharing_a_native_reducer_name_is_readmitted() {
    let base = base();
    let env = imported(&base);
    let mut gate = ImportedConeGate::new(&base);
    let verdict = gate.check(&env, &BTreeSet::from([n("V.good")]));
    assert!(
        verdict.passed(false),
        "V.f is Lean-shaped and V.good true of it: {}",
        verdict.refusal_summary(false)
    );
    assert!(verdict.untrusted_in_cone.iter().any(|m| m == "V.f"));
}

/// The reducer's meaning is not available to a citation: `V.bad`, which holds
/// only if the kernel computed `V.f 5` with the reducer, is refused by the
/// kernel itself — and so is it after `V.f` was admitted by an earlier check.
#[test]
fn the_reducer_meaning_is_not_available_to_a_citation() {
    let base = base();
    let env = imported(&base);
    for warm in [false, true] {
        let mut gate = ImportedConeGate::new(&base);
        if warm {
            assert!(gate
                .check(&env, &BTreeSet::from([n("V.good")]))
                .passed(false));
        }
        let verdict = gate.check(&env, &BTreeSet::from([n("V.bad")]));
        assert!(!verdict.passed(true), "warm={warm}: V.bad must be refused");
        assert!(
            verdict.refusals.iter().any(|r| matches!(
                r,
                ClosedRecheckRefusal::DeclarationRefused { name, .. } if name == "V.bad"
            )),
            "warm={warm}: the kernel refuses V.bad itself: {:?}",
            verdict.refusals
        );
    }
}

// ---------------------------------------------------------------------------
// The same attack with a REAL reducer over the REAL base `clean check
// --imports-prefer-olean` snapshots. The arms above register a fixture
// reducer for a name the kernel's fold-key universe does not contain, so the
// authority refuses it for want of any canonical digest at all. `List.length`
// is the hard case: the import-mode prelude registers its reducer, does NOT
// declare it, runs in `KernelTheory::Extended` (so the theory admits every
// reducer), and the kernel's canon DOES hold a digest for it — Lean v4.30's
// own `List.length` over that prelude is authorized and the reducer fires.
// The only thing between a forged `List.length` and the reducer's meaning is
// the digest of the forged closure.
// ---------------------------------------------------------------------------

const LIST_LENGTH: &str = "List.length";

fn list_u(u: Level, elem: Expr) -> Expr {
    Expr::app(Expr::const_(n("List"), vec![u]), elem)
}

/// `@List.cons.{0} Nat 1 (… (@List.nil.{0} Nat))` for `[1, 2, 3]`.
fn nat_list_1_2_3() -> Expr {
    [3u64, 2, 1].into_iter().fold(
        Expr::app(Expr::const_(n("List.nil"), vec![Level::zero()]), nat()),
        |tail, k| {
            [nat(), Expr::nat_lit(k), tail]
                .into_iter()
                .fold(Expr::const_(n("List.cons"), vec![Level::zero()]), Expr::app)
        },
    )
}

/// `@List.length.{0} Nat [1, 2, 3]`.
fn length_1_2_3() -> Expr {
    [nat(), nat_list_1_2_3()]
        .into_iter()
        .fold(Expr::const_(n(LIST_LENGTH), vec![Level::zero()]), Expr::app)
}

/// `List.length.{u} : {α : Type u} → List α → Nat`, imported structurally
/// (never type-checked, as an `.olean` payload is) with `value`, or as a
/// value-less axiom when `value` is `None`.
fn import_list_length(env: &mut Environment, value: Option<Expr>) {
    let u = Level::param(n("u"));
    let type_u = Expr::sort(Level::succ(u.clone()));
    let ty = Expr::pi(
        BinderInfo::Implicit,
        type_u,
        Expr::pi(BinderInfo::Default, list_u(u, Expr::bvar(0)), nat()),
    );
    let kind = if value.is_some() {
        ConstantKind::Definition
    } else {
        ConstantKind::Axiom
    };
    let rejected = env.extend_constants_structural(std::iter::once(ConstantInfo {
        name: n(LIST_LENGTH),
        level_params: vec![n("u")],
        type_: ty,
        value,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind,
    }));
    assert!(
        rejected.is_empty(),
        "structural tier refused List.length: {rejected:?}"
    );
}

/// `fun {α : Type u} (_ : List α) => 0`: a `List.length` that is not length.
fn forged_length_value() -> Expr {
    let u = Level::param(n("u"));
    Expr::lam(
        BinderInfo::Implicit,
        Expr::sort(Level::succ(u.clone())),
        Expr::lam(
            BinderInfo::Default,
            list_u(u, Expr::bvar(0)),
            Expr::nat_lit(0),
        ),
    )
}

/// The consumer's environment after an import supplies `List.length` (forged
/// as `forged`) and two `rfl` citations of it: `L.zero : [1,2,3].length = 0`
/// (true of the forged declaration) and `L.three : [1,2,3].length = 3` (true
/// only of the base's reducer).
fn imported_list_length(base: &Environment, forged: Option<Expr>) -> Environment {
    let mut env = base.clone();
    import_list_length(&mut env, forged);
    import(
        &mut env,
        "L.zero",
        ConstantKind::Theorem,
        nat_eq(length_1_2_3(), Expr::nat_lit(0)),
        nat_refl(Expr::nat_lit(0)),
    );
    import(
        &mut env,
        "L.three",
        ConstantKind::Theorem,
        nat_eq(length_1_2_3(), Expr::nat_lit(3)),
        nat_refl(Expr::nat_lit(3)),
    );
    env
}

fn import_prelude_base() -> Environment {
    let base = Environment::try_with_prelude_for_import().expect("import-mode prelude");
    let length = n(LIST_LENGTH);
    let reducer = base
        .get_native_reducer(&length)
        .expect("the import-mode prelude registers a List.length reducer");
    assert!(
        base.get_const(&length).is_none(),
        "the fixture's premise: the import-mode prelude does not declare List.length"
    );
    assert_eq!(
        base.kernel_theory(),
        clean_kernel::env::KernelTheory::Extended,
        "the fixture's premise: the kernel theory admits every reducer, so only the \
         fold authority stands between a forged head and its reducer"
    );
    // The reducer's meaning, on the citation's own arguments.
    assert_eq!(
        reducer(&[&nat(), &nat_list_1_2_3()]),
        Some(Expr::nat_lit(3)),
        "the base's reducer computes [1, 2, 3].length = 3"
    );
    base
}

/// The control that makes the forged arms mean something: over the SAME base,
/// Lean v4.30's own `List.length` is authorized, so the reducer is live on the
/// name — the forged arms below are stopped by their digest and nothing else.
#[test]
fn lean_list_length_over_the_import_prelude_is_a_live_reducer_head() {
    let base = import_prelude_base();
    let lib = crate::pinned_lean_lib_path().expect(crate::test_support::PINNED_LEAN_REQUIRED);
    let mut env = base.clone();
    crate::load_module_with_deps(&mut env, "Init.Prelude", std::slice::from_ref(&lib))
        .unwrap_or_else(|e| panic!("load Init.Prelude ({}): {e}", lib.display()));
    let length = n(LIST_LENGTH);
    assert!(
        env.native_fold_authorized(&length),
        "Lean's List.length over the import prelude must be canonical: {:?}",
        env.native_fold_verdict(&length)
    );
}

/// A forged `List.length` DEFINITION under the real reducer's name, over the
/// real import-mode prelude: the reducer's meaning (`L.three`) is refused by
/// the kernel — cold, and after the forged head was admitted by an earlier
/// check of the same gate. Against a kernel that fires a reducer on its name
/// alone (`tc/fold_admission.rs` without the authority), `L.three` is
/// re-admitted and this arm fails: it is the soundness half of dropping the
/// gate's `NativeReducerCollision` refusal.
#[test]
fn a_forged_list_length_does_not_lend_a_citation_the_reducer_meaning() {
    let base = import_prelude_base();
    let env = imported_list_length(&base, Some(forged_length_value()));
    assert!(
        !env.native_fold_authorized(&n(LIST_LENGTH)),
        "a forged List.length must never be canonical"
    );
    for warm in [false, true] {
        let mut gate = ImportedConeGate::new(&base);
        if warm {
            // Admit the forged head first (the verdict is the other arm's).
            let _ = gate.check(&env, &BTreeSet::from([n("L.zero")]));
        }
        let verdict = gate.check(&env, &BTreeSet::from([n("L.three")]));
        assert!(
            !verdict.passed(true),
            "warm={warm}: L.three must be refused"
        );
        assert!(
            verdict.refusals.iter().any(|r| matches!(
                r,
                ClosedRecheckRefusal::DeclarationRefused { name, .. } if name == "L.three"
            )),
            "warm={warm}: the kernel refuses L.three itself: {:?}",
            verdict.refusals
        );
    }
}

/// The same forged `List.length` is admitted with ITS meaning: `L.zero`, true
/// of the declaration and false of the reducer, is credited.
#[test]
fn a_forged_list_length_over_the_import_prelude_keeps_its_own_meaning() {
    let base = import_prelude_base();
    let env = imported_list_length(&base, Some(forged_length_value()));
    let mut gate = ImportedConeGate::new(&base);
    let verdict = gate.check(&env, &BTreeSet::from([n("L.zero")]));
    assert!(
        verdict.passed(false),
        "the forged List.length is admitted with its own meaning: {}",
        verdict.refusal_summary(false)
    );
    assert!(verdict.untrusted_in_cone.iter().any(|m| m == LIST_LENGTH));
}

/// A value-less `List.length` (an axiom under the reducer's name) computes
/// nothing: `L.three` is refused by the kernel, not merely by the gate's
/// imported-axiom policy — and so is `L.zero`, which no definition supports.
/// Against a kernel that fires a reducer on its name alone, the kernel
/// re-admits `L.three` and only the imported-axiom policy stands; this arm
/// fails there.
#[test]
fn an_axiom_under_a_reducer_name_computes_nothing_over_the_import_prelude() {
    let base = import_prelude_base();
    let env = imported_list_length(&base, None);
    for citation in ["L.three", "L.zero"] {
        let mut gate = ImportedConeGate::new(&base);
        let verdict = gate.check(&env, &BTreeSet::from([n(citation)]));
        assert!(!verdict.passed(true), "{citation} must be refused");
        assert!(
            verdict.refusals.iter().any(|r| matches!(
                r,
                ClosedRecheckRefusal::DeclarationRefused { name, .. } if name == citation
            )),
            "the kernel refuses {citation} itself: {:?}",
            verdict.refusals
        );
    }
}
