// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Self-proof unit F1: the kernel's own folds that Lean's kernel does not
//! have are refused by the reference entry's THEORY, not only by native-fold
//! authority.
//!
//! The folds: `reduce_int` (`Int.add`/`Int.sub`/`Int.mul` over a literal above
//! `u64`), the `Nat.pred` arm of `reduce_nat`, and the evaluation of
//! `Lean.reduceBool`/`Lean.reduceNat` by whnf. They are compiled into the type
//! checker, outside the native-reducer registry, and until 2026-11-12 they
//! asked native-fold authority alone, so they fired in every kernel theory.
//!
//! Over a canonical definition such a fold computes what δ computes, so no
//! verdict shows whether it fired. This battery therefore separates the two
//! the way the pinned-Lean experiment does
//! (`reports/fence-folds-2026-11-12/KernelFoldsByName.lean`): it FORGES each
//! head with a definition that disagrees with the arithmetic (`Nat.pred a :=
//! 0`, `Int.add a b := a`, ...), so the arithmetic answer is accepted exactly
//! when the fold fires and the definition's answer exactly when δ decides.
//! Authority refuses a forged head in every theory, so the battery opens that
//! gate (`native_fold_mint_bypass`, the door
//! `reference_entry_fold_controls.rs` uses) and leaves the theory as the only
//! thing between the fold and the entry.
//!
//! Every row has both halves: `Extended` on the same environment accepts the
//! arithmetic answer (the fold exists and is reachable), and the entry
//! refuses it and accepts the definition's answer (the term is well formed;
//! only the fold is missing). The control row is `Nat.add`, one of the
//! fourteen heads Lean's `reduce_nat` has: the entry folds it, forged or not,
//! as pinned Lean does. The entry's column for the ten arithmetic rows is
//! pinned Lean's own, recorded in `reports/fence-folds-2026-11-12/README.md`.
//!
//! The bypass is process-global, so every test here takes one lock and this
//! file is its own binary.

use std::sync::{Mutex, MutexGuard};

use clean_kernel::env::{native_fold_mint_bypass, KernelTheory};
use clean_kernel::{
    BinderInfo, Constructor, Declaration, Environment, Expr, InductiveDecl, InductiveType, Level,
    Name, ReferenceKernel, ReferenceRefusal, TheoryId,
};

static SERIAL: Mutex<()> = Mutex::new(());

fn serial() -> MutexGuard<'static, ()> {
    SERIAL
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(name(s), vec![])
}

fn lit(n: u128) -> Expr {
    Expr::nat_lit_u128(n)
}

/// `2^64`: the smallest literal `reduce_int`'s scope guard fires on.
const BIG: u128 = 1 << 64;

fn of_nat(n: u128) -> Expr {
    Expr::app(c("Int.ofNat"), lit(n))
}

fn app2(f: &str, a: Expr, b: Expr) -> Expr {
    Expr::apps(c(f), [a, b])
}

/// `theorem f1_probe : @Eq.{1} ty lhs rhs := @Eq.refl.{1} ty rhs`.
fn by_refl(ty: &str, lhs: Expr, rhs: Expr) -> Declaration {
    let one = || vec![Level::succ(Level::zero())];
    Declaration::Theorem {
        name: name("f1_probe"),
        level_params: vec![],
        type_: Expr::apps(Expr::const_(name("Eq"), one()), [c(ty), lhs, rhs.clone()]),
        value: Expr::apps(Expr::const_(name("Eq.refl"), one()), [c(ty), rhs]),
    }
}

fn inductive(n: &str, constructors: &[(&str, Expr)]) -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name(n),
            type_: Expr::type_(),
            constructors: constructors
                .iter()
                .map(|(ctor, ty)| Constructor {
                    name: name(ctor),
                    type_: ty.clone(),
                })
                .collect(),
        }],
    }
}

fn definition(n: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Definition {
        name: name(n),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    }
}

/// The environment of the pinned-Lean experiment, admitted declaration by
/// declaration through the entry from an EMPTY base: `Eq`, `Nat`, `Int`,
/// `Bool`; every arithmetic head forged; `Lean.reduceBool`/`Lean.reduceNat`
/// as the opaque identities Lean's `Init` states; and two closed constants.
fn forged_entry() -> ReferenceKernel {
    let mut k = ReferenceKernel::new(Environment::default()).expect("an empty base");
    let u = || Level::param(name("u"));
    let eq_refl_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(u()),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::apps(
                Expr::const_(name("Eq"), vec![u()]),
                [Expr::bvar(1), Expr::bvar(0), Expr::bvar(0)],
            ),
        ),
    );
    k.add_inductive_checked(InductiveDecl {
        level_params: vec![name("u")],
        num_params: 2,
        types: vec![InductiveType {
            name: name("Eq"),
            type_: Expr::pi(
                BinderInfo::Implicit,
                Expr::sort(u()),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(0),
                    Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::prop()),
                ),
            ),
            constructors: vec![Constructor {
                name: name("Eq.refl"),
                type_: eq_refl_type,
            }],
        }],
    })
    .expect("Eq");
    let unary = |t: &str| Expr::arrow(c(t), c(t));
    k.add_inductive_checked(inductive(
        "Nat",
        &[("Nat.zero", c("Nat")), ("Nat.succ", unary("Nat"))],
    ))
    .expect("Nat");
    k.add_inductive_checked(inductive(
        "Int",
        &[
            ("Int.ofNat", Expr::arrow(c("Nat"), c("Int"))),
            ("Int.negSucc", Expr::arrow(c("Nat"), c("Int"))),
        ],
    ))
    .expect("Int");
    k.add_inductive_checked(inductive(
        "Bool",
        &[("Bool.false", c("Bool")), ("Bool.true", c("Bool"))],
    ))
    .expect("Bool");

    let binary = |t: &str| Expr::arrow(c(t), Expr::arrow(c(t), c(t)));
    let first = |t: &str| {
        Expr::lam(
            BinderInfo::Default,
            c(t),
            Expr::lam(BinderInfo::Default, c(t), Expr::bvar(1)),
        )
    };
    k.add_checked(definition("Nat.add", binary("Nat"), first("Nat")))
        .expect("forged Nat.add");
    k.add_checked(definition(
        "Nat.pred",
        unary("Nat"),
        Expr::lam(BinderInfo::Default, c("Nat"), c("Nat.zero")),
    ))
    .expect("forged Nat.pred");
    for head in ["Int.add", "Int.sub", "Int.mul"] {
        k.add_checked(definition(head, binary("Int"), first("Int")))
            .expect("forged Int head");
    }
    for (head, t) in [("Lean.reduceBool", "Bool"), ("Lean.reduceNat", "Nat")] {
        k.add_checked(Declaration::Opaque {
            name: name(head),
            level_params: vec![],
            type_: unary(t),
            value: Expr::lam(BinderInfo::Default, c(t), Expr::bvar(0)),
        })
        .expect("the opaque identity");
    }
    k.add_checked(definition("f1BoolTrue", c("Bool"), c("Bool.true")))
        .expect("f1BoolTrue");
    k.add_checked(definition("f1NatSeven", c("Nat"), lit(7)))
        .expect("f1NatSeven");
    k
}

/// The verdicts on `d` over the forged environment: `Extended` on a copy of
/// the entry's own environment, and the entry itself.
fn verdicts(d: &Declaration) -> (bool, Result<TheoryId, ReferenceRefusal>) {
    let mut k = forged_entry();
    let mut extended = k.environment().clone();
    extended.set_kernel_theory(KernelTheory::Extended);
    let extended = extended.check_decl_readonly(d).is_ok();
    assert_eq!(k.environment().kernel_theory(), KernelTheory::LeanReference);
    let entry = k.add_checked(d.clone()).map(|token| token.theory_id());
    (extended, entry)
}

/// A fold Lean's kernel lacks: `Extended` takes the arithmetic answer and
/// refuses the definition's, the entry does the reverse, and its refusal is
/// the kernel's own type mismatch.
fn assert_clean_only_fold(label: &str, ty: &str, lhs: &Expr, arithmetic: Expr, defined: Expr) {
    let (extended, entry) = verdicts(&by_refl(ty, lhs.clone(), arithmetic));
    assert!(
        extended,
        "{label}: control, the fold fires in Extended and gives the arithmetic answer"
    );
    let err = entry.expect_err(&format!(
        "{label}: the fold fired inside the reference entry (arithmetic answer accepted)"
    ));
    assert!(
        matches!(err, ReferenceRefusal::Kernel(_)),
        "{label}: expected the kernel's refusal, got {err:?}"
    );
    let (extended, entry) = verdicts(&by_refl(ty, lhs.clone(), defined));
    assert!(
        !extended,
        "{label}: control, Extended folds, so the definition's answer is refused there"
    );
    let theory = entry.unwrap_or_else(|e| {
        panic!("{label}: the entry decides by δ, the definition's answer: {e:?}")
    });
    assert_eq!(theory, TheoryId::LeanReferenceV1);
}

/// CONTROL. `Nat.add` is one of the fourteen heads Lean's `reduce_nat` has,
/// so with authority open the entry folds it by name, as pinned Lean's kernel
/// does over the same forged definition: `2 + 3 = 5` is accepted and the
/// definition's `2` refused. A fold firing inside the entry is therefore
/// visible to this battery, and the refusals below are not an artifact.
#[test]
fn test_control_forged_nat_add_folds_by_name_in_the_entry_as_in_lean() {
    let _serial = serial();
    native_fold_mint_bypass::run(|| {
        let lhs = app2("Nat.add", lit(2), lit(3));
        let (extended, entry) = verdicts(&by_refl("Nat", lhs.clone(), lit(5)));
        assert!(extended, "Extended folds Nat.add");
        entry.expect("the entry folds Nat.add: it is Lean's own extension");
        let (extended, entry) = verdicts(&by_refl("Nat", lhs, lit(2)));
        assert!(!extended);
        let err = entry.expect_err("the forged definition's answer is refused, as in Lean");
        assert!(matches!(err, ReferenceRefusal::Kernel(_)), "got {err:?}");
    });
}

/// `Nat.pred` on a literal. Pinned Lean: `Nat.pred 5 = 4` refused, `= 0`
/// (the forged definition) accepted.
#[test]
fn test_nat_pred_literal_fold_is_refused_in_the_entry() {
    let _serial = serial();
    native_fold_mint_bypass::run(|| {
        let lhs = Expr::app(c("Nat.pred"), lit(5));
        assert_clean_only_fold("Nat.pred 5", "Nat", &lhs, lit(4), lit(0));
        // Above `u64` too, where the fold's arbitrary-precision path runs.
        let lhs = Expr::app(c("Nat.pred"), lit(BIG));
        assert_clean_only_fold("Nat.pred 2^64", "Nat", &lhs, lit(BIG - 1), lit(0));
    });
}

/// `Int.add` over a literal above `u64`. Pinned Lean: the arithmetic answer
/// refused, the forged definition's accepted.
#[test]
fn test_int_add_big_literal_fold_is_refused_in_the_entry() {
    let _serial = serial();
    native_fold_mint_bypass::run(|| {
        let lhs = app2("Int.add", of_nat(BIG), of_nat(1));
        assert_clean_only_fold("Int.add", "Int", &lhs, of_nat(BIG + 1), of_nat(BIG));
    });
}

/// `Int.sub` over a literal above `u64`.
#[test]
fn test_int_sub_big_literal_fold_is_refused_in_the_entry() {
    let _serial = serial();
    native_fold_mint_bypass::run(|| {
        let lhs = app2("Int.sub", of_nat(BIG), of_nat(1));
        assert_clean_only_fold("Int.sub", "Int", &lhs, of_nat(BIG - 1), of_nat(BIG));
    });
}

/// `Int.mul` over a literal above `u64`.
#[test]
fn test_int_mul_big_literal_fold_is_refused_in_the_entry() {
    let _serial = serial();
    native_fold_mint_bypass::run(|| {
        let lhs = app2("Int.mul", of_nat(BIG), of_nat(3));
        assert_clean_only_fold("Int.mul", "Int", &lhs, of_nat(BIG * 3), of_nat(BIG));
    });
}

/// `Lean.reduceBool c` / `Lean.reduceNat c` over the opaque identities.
/// `Extended` evaluates `c` by whnf once authority admits the head; the entry
/// leaves the opaque stuck, so it refuses the true statement as well as the
/// false one. (Pinned Lean accepts the true one by running `c`'s compiled
/// code, and the theorem then rests on `Lean.trustCompiler`, which no
/// reference closure may reach: `KernelReduceBool.lean`.)
#[test]
fn test_reduce_bool_and_reduce_nat_are_refused_in_the_entry() {
    let _serial = serial();
    native_fold_mint_bypass::run(|| {
        let rb = Expr::app(c("Lean.reduceBool"), c("f1BoolTrue"));
        let rn = Expr::app(c("Lean.reduceNat"), c("f1NatSeven"));
        for (label, ty, lhs, truth, falsity) in [
            (
                "Lean.reduceBool",
                "Bool",
                rb.clone(),
                c("Bool.true"),
                c("Bool.false"),
            ),
            ("Lean.reduceNat", "Nat", rn.clone(), lit(7), lit(8)),
        ] {
            let (extended, entry) = verdicts(&by_refl(ty, lhs.clone(), truth));
            assert!(
                extended,
                "{label}: control, Extended evaluates the constant by whnf"
            );
            let err = entry.expect_err(&format!(
                "{label}: the evaluation fired inside the reference entry"
            ));
            assert!(
                matches!(err, ReferenceRefusal::Kernel(_)),
                "{label}: got {err:?}"
            );
            let (extended, entry) = verdicts(&by_refl(ty, lhs.clone(), falsity));
            assert!(!extended, "{label}: control, the false value is refused");
            entry.expect_err("the false value is refused in the entry too");
            // Control: the stuck term is well formed; reflexivity on it checks.
            let (extended, entry) = verdicts(&by_refl(ty, lhs.clone(), lhs));
            assert!(extended);
            entry.expect("reflexivity on the stuck opaque application is accepted");
        }
    });
}

/// With authority as shipped (no bypass), no forged ARITHMETIC head folds in
/// either theory: every row is decided by δ, so the arithmetic answers are
/// refused by `Extended` too. This is what the bypass above removes, and why
/// the rows above measure the theory alone.
#[test]
fn test_without_the_bypass_authority_refuses_every_forged_arithmetic_fold() {
    let _serial = serial();
    let rows = [
        ("Nat", Expr::app(c("Nat.pred"), lit(5)), lit(4), lit(0)),
        (
            "Int",
            app2("Int.add", of_nat(BIG), of_nat(1)),
            of_nat(BIG + 1),
            of_nat(BIG),
        ),
        (
            "Int",
            app2("Int.sub", of_nat(BIG), of_nat(1)),
            of_nat(BIG - 1),
            of_nat(BIG),
        ),
        (
            "Int",
            app2("Int.mul", of_nat(BIG), of_nat(3)),
            of_nat(BIG * 3),
            of_nat(BIG),
        ),
    ];
    for (ty, lhs, arithmetic, defined) in rows {
        let (extended, entry) = verdicts(&by_refl(ty, lhs.clone(), arithmetic));
        assert!(
            !extended,
            "authority refuses a forged fold in Extended: {lhs:?}"
        );
        entry.expect_err("and in the entry");
        let (extended, entry) = verdicts(&by_refl(ty, lhs.clone(), defined));
        assert!(extended, "δ decides in Extended: {lhs:?}");
        entry.expect("and in the entry");
    }
}

/// `Lean.reduceBool` / `Lean.reduceNat` need NO bypass: authority admits an
/// opaque identity structurally (world `identity`), and the entry itself
/// admits the declaration. So this is the production shape of the defect unit
/// F1 found: before 2026-11-12 the entry, having accepted `opaque
/// Lean.reduceBool (b : Bool) : Bool := b` and `def c : Bool := true`,
/// accepted `Lean.reduceBool c = true` by reflexivity, a statement pinned
/// Lean's kernel accepts only by running compiled code under
/// `Lean.trustCompiler`. `Extended` still accepts it; the entry refuses.
#[test]
fn test_reduce_bool_and_reduce_nat_are_refused_in_the_entry_under_shipped_authority() {
    let _serial = serial();
    let k = forged_entry();
    for head in ["Lean.reduceBool", "Lean.reduceNat"] {
        assert_eq!(
            k.environment().native_fold_verdict(&name(head)).ok(),
            Some("identity"),
            "{head}: control, shipped authority admits the opaque identity"
        );
    }
    for (label, ty, lhs, truth) in [
        (
            "Lean.reduceBool",
            "Bool",
            Expr::app(c("Lean.reduceBool"), c("f1BoolTrue")),
            c("Bool.true"),
        ),
        (
            "Lean.reduceNat",
            "Nat",
            Expr::app(c("Lean.reduceNat"), c("f1NatSeven")),
            lit(7),
        ),
    ] {
        let (extended, entry) = verdicts(&by_refl(ty, lhs.clone(), truth));
        assert!(
            extended,
            "{label}: control, Extended evaluates the constant by whnf"
        );
        let err = entry.expect_err(&format!(
            "{label}: the evaluation fired inside the reference entry"
        ));
        assert!(
            matches!(err, ReferenceRefusal::Kernel(_)),
            "{label}: got {err:?}"
        );
        let (extended, entry) = verdicts(&by_refl(ty, lhs.clone(), lhs));
        assert!(extended);
        entry.expect("reflexivity on the stuck opaque application is accepted");
    }
}

/// KNOWN DIVERGENCE, pinned so it fails the day it closes. Under shipped
/// authority a forged `Nat.add` (not Lean's definition) is refused its fold in
/// every theory, so the entry decides `Nat.add 2 3` by δ and takes the forged
/// definition's `2`, where pinned Lean's kernel folds by name and takes `5`
/// (`reports/fence-folds-2026-11-12/README.md`, the control rows). The entry
/// is not Lean-exact over an environment that redefines a head Lean computes
/// by name; R128 (`docs/DECISIONS.md`) declines such an export at the front
/// door, and the entry itself does not refuse the declaration. Not one of the
/// four folds of unit F1; reported there.
#[test]
fn test_known_divergence_forged_nat_add_is_decided_by_delta_under_shipped_authority() {
    let _serial = serial();
    let lhs = app2("Nat.add", lit(2), lit(3));
    let (extended, entry) = verdicts(&by_refl("Nat", lhs.clone(), lit(2)));
    assert!(extended, "δ decides in Extended");
    entry.expect("the entry takes the forged definition's answer; pinned Lean refuses it");
    let (extended, entry) = verdicts(&by_refl("Nat", lhs, lit(5)));
    assert!(!extended);
    entry.expect_err("the entry refuses the arithmetic answer; pinned Lean accepts it");
}
