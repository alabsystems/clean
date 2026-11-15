// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Self-proof unit F1, the production half: the reference entry over
//! `Environment::with_prelude`, native-fold authority as shipped.
//!
//! Four of the checker's compiled-in folds are rules Lean's kernel does not
//! have: `reduce_int` (`Int.add`/`Int.sub`/`Int.mul` over a literal above
//! `u64`), the `Nat.pred` arm of `reduce_nat`, and the evaluation of
//! `Lean.reduceBool`/`Lean.reduceNat` by whnf. Until 2026-11-12 they asked
//! native-fold authority alone, and the prelude's `Nat.pred` and `Int` heads
//! hold `fold` rows, so in production they fired inside the entry. They are
//! gated on the kernel theory now (`tc/fold_admission.rs`).
//!
//! Over a canonical definition a fold and δ reach the same value, so for the
//! arithmetic heads a verdict cannot show which of them ran. What this file
//! pins is what the entry must still do WITHOUT the folds, and what it must
//! refuse:
//!
//! * authority admits the four arithmetic heads here (so the theory, and
//!   nothing else, is what keeps their folds out of the entry);
//! * the entry still decides the true statements, by unfolding the
//!   definitions as Lean's kernel does, and still refuses the false ones;
//! * `Lean.reduceBool c = true` and `Lean.reduceNat c = 7`, over the opaque
//!   identities declared THROUGH the entry, are refused by it, where
//!   `Extended` on the same environment accepts them (authority admits an
//!   opaque identity structurally, so no test door is involved). Before
//!   2026-11-12 the entry accepted both; pinned Lean accepts them only by
//!   running compiled code under `Lean.trustCompiler`.
//!
//! The fold functions themselves are asked under each theory in
//! `src/tc/fold_admission_tests.rs`; the verdict-level separation for the
//! arithmetic heads, over forged definitions with authority open, is
//! `crates/clean-olean/tests/reference_entry_fold_theory.rs`, with pinned
//! Lean's verdicts on the same rows in `reports/fence-folds-2026-11-12/`.

use clean_kernel::env::KernelTheory;
use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, Level, Name, ReferenceKernel, ReferenceRefusal,
    TheoryId,
};

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

fn neg_succ(n: u128) -> Expr {
    Expr::app(c("Int.negSucc"), lit(n))
}

fn app2(f: &str, a: Expr, b: Expr) -> Expr {
    Expr::apps(c(f), [a, b])
}

/// `theorem <thm> : @Eq.{1} ty lhs rhs := @Eq.refl.{1} ty rhs`.
fn by_refl(thm: &str, ty: &str, lhs: Expr, rhs: Expr) -> Declaration {
    let one = || vec![Level::succ(Level::zero())];
    Declaration::Theorem {
        name: name(thm),
        level_params: vec![],
        type_: Expr::apps(Expr::const_(name("Eq"), one()), [c(ty), lhs, rhs.clone()]),
        value: Expr::apps(Expr::const_(name("Eq.refl"), one()), [c(ty), rhs]),
    }
}

/// The reference entry over the prelude, built once per test.
struct Rig {
    entry: ReferenceKernel,
}

impl Rig {
    fn new() -> Self {
        let base = Environment::with_prelude();
        assert_eq!(base.kernel_theory(), KernelTheory::Extended);
        let entry = ReferenceKernel::new(base).expect("the prelude passes the entry's walk");
        assert_eq!(
            entry.environment().kernel_theory(),
            KernelTheory::LeanReference
        );
        Self { entry }
    }

    /// The verdicts on `d`: `Extended` on a copy of the entry's environment,
    /// and the entry itself (a refused declaration leaves it unchanged; an
    /// accepted one is a theorem under a name of its own).
    fn verdicts(&mut self, d: &Declaration) -> (bool, Result<TheoryId, ReferenceRefusal>) {
        let mut extended = self.entry.environment().clone();
        extended.set_kernel_theory(KernelTheory::Extended);
        let extended = extended.check_decl_readonly(d).is_ok();
        let entry = self
            .entry
            .add_checked(d.clone())
            .map(|token| token.theory_id());
        (extended, entry)
    }

    /// A true statement is accepted by `Extended` and by the entry; the false
    /// one beside it is refused by both, the entry's refusal being the
    /// kernel's.
    fn assert_decided(&mut self, label: &str, ty: &str, lhs: &Expr, truth: Expr, falsity: Expr) {
        let stem = format!(
            "f1_{}",
            label.replace(|ch: char| !ch.is_alphanumeric(), "_")
        );
        let (extended, entry) =
            self.verdicts(&by_refl(&format!("{stem}_true"), ty, lhs.clone(), truth));
        assert!(
            extended,
            "{label}: control, Extended accepts the true statement"
        );
        let theory = entry.unwrap_or_else(|e| {
            panic!("{label}: the entry decides it by unfolding, as Lean's kernel does: {e:?}")
        });
        assert_eq!(theory, TheoryId::LeanReferenceV1);
        let (extended, entry) =
            self.verdicts(&by_refl(&format!("{stem}_false"), ty, lhs.clone(), falsity));
        assert!(
            !extended,
            "{label}: the false statement is refused in Extended"
        );
        let err = entry.expect_err(&format!(
            "{label}: the false statement is refused in the entry"
        ));
        assert!(
            matches!(err, ReferenceRefusal::Kernel(_)),
            "{label}: expected the kernel's refusal, got {err:?}"
        );
    }
}

/// Authority admits the four arithmetic heads over the prelude, in the
/// entry's own environment. So their folds are not kept out of the entry by
/// authority: the theory gate is what does it.
#[test]
fn test_authority_admits_the_arithmetic_heads_in_the_entry() {
    let rig = Rig::new();
    for head in ["Nat.pred", "Int.add", "Int.sub", "Int.mul"] {
        assert!(
            rig.entry.environment().native_fold_authorized(&name(head)),
            "{head}: the prelude's definition holds a fold row"
        );
    }
}

/// `Nat.pred` on a literal, small and above `u64`.
#[test]
fn test_entry_decides_nat_pred_on_a_literal_without_the_fold() {
    let mut rig = Rig::new();
    let pred = |n: u128| Expr::app(c("Nat.pred"), lit(n));
    rig.assert_decided("Nat.pred 5", "Nat", &pred(5), lit(4), lit(5));
    rig.assert_decided("Nat.pred 0", "Nat", &pred(0), lit(0), lit(1));
    rig.assert_decided("Nat.pred 2^64", "Nat", &pred(BIG), lit(BIG - 1), lit(BIG));
}

/// `Int.add` / `Int.sub` / `Int.mul` over a literal above `u64`, both signs.
#[test]
fn test_entry_decides_int_big_literal_arithmetic_without_the_fold() {
    let mut rig = Rig::new();
    let rows = [
        (
            "Int.add",
            app2("Int.add", of_nat(BIG), of_nat(1)),
            of_nat(BIG + 1),
            of_nat(BIG),
        ),
        (
            "Int.add, mixed signs",
            app2("Int.add", of_nat(1), neg_succ(BIG)),
            neg_succ(BIG - 1),
            neg_succ(BIG),
        ),
        (
            "Int.sub",
            app2("Int.sub", of_nat(BIG), of_nat(1)),
            of_nat(BIG - 1),
            of_nat(BIG),
        ),
        (
            "Int.sub, negative result",
            app2("Int.sub", of_nat(1), of_nat(BIG)),
            neg_succ(BIG - 2),
            neg_succ(BIG - 1),
        ),
        (
            "Int.mul",
            app2("Int.mul", of_nat(BIG), of_nat(3)),
            of_nat(BIG * 3),
            of_nat(BIG),
        ),
        (
            "Int.mul, two negatives",
            app2("Int.mul", neg_succ(BIG), neg_succ(1)),
            of_nat((BIG + 1) * 2),
            of_nat(BIG * 2),
        ),
    ];
    for (label, lhs, truth, falsity) in rows {
        rig.assert_decided(label, "Int", &lhs, truth, falsity);
    }
}

/// `Lean.reduceBool c = true` and `Lean.reduceNat c = 7`, in production shape:
/// the opaque identities and the two constants are declared THROUGH the
/// entry, and native-fold authority, as shipped, admits an opaque identity
/// (world `identity`). `Extended` evaluates `c` by whnf and accepts; the
/// entry leaves the opaque stuck and refuses, where before 2026-11-12 it
/// accepted. Pinned Lean accepts the same statements only by running `c`'s
/// compiled code, and the theorem then rests on `Lean.trustCompiler`
/// (`reports/fence-folds-2026-11-12/KernelReduceBool.lean`), an axiom no
/// reference closure may reach.
#[test]
fn test_reduce_bool_and_reduce_nat_are_refused_through_the_entry() {
    let mut rig = Rig::new();
    for (head, ty) in [("Lean.reduceBool", "Bool"), ("Lean.reduceNat", "Nat")] {
        assert!(rig.entry.environment().get_const(&name(head)).is_none());
        rig.entry
            .add_checked(Declaration::Opaque {
                name: name(head),
                level_params: vec![],
                type_: Expr::pi(BinderInfo::Default, c(ty), c(ty)),
                value: Expr::lam(BinderInfo::Default, c(ty), Expr::bvar(0)),
            })
            .expect("the entry admits the opaque identity");
        assert_eq!(
            rig.entry
                .environment()
                .native_fold_verdict(&name(head))
                .ok(),
            Some("identity"),
            "{head}: control, shipped authority admits the opaque identity"
        );
    }
    for (constant, ty, value) in [
        ("f1BoolTrue", "Bool", c("Bool.true")),
        ("f1NatSeven", "Nat", lit(7)),
    ] {
        rig.entry
            .add_checked(Declaration::Definition {
                name: name(constant),
                level_params: vec![],
                type_: c(ty),
                value,
                is_reducible: false,
            })
            .expect("a closed constant");
    }
    for (head, ty, constant, truth, falsity) in [
        (
            "Lean.reduceBool",
            "Bool",
            "f1BoolTrue",
            c("Bool.true"),
            c("Bool.false"),
        ),
        ("Lean.reduceNat", "Nat", "f1NatSeven", lit(7), lit(8)),
    ] {
        let stem = format!("f1_{}", head.replace('.', "_"));
        let lhs = Expr::app(c(head), c(constant));
        let (extended, entry) =
            rig.verdicts(&by_refl(&format!("{stem}_true"), ty, lhs.clone(), truth));
        assert!(
            extended,
            "{head}: control, Extended evaluates the constant by whnf"
        );
        let err = entry.expect_err(&format!("{head}: evaluated inside the reference entry"));
        assert!(
            matches!(err, ReferenceRefusal::Kernel(_)),
            "{head}: expected the kernel's refusal, got {err:?}"
        );
        let (extended, entry) =
            rig.verdicts(&by_refl(&format!("{stem}_false"), ty, lhs.clone(), falsity));
        assert!(!extended, "{head}: the false value is refused in Extended");
        entry.expect_err("and in the entry");
        // Control: the stuck application is well formed.
        let (extended, entry) =
            rig.verdicts(&by_refl(&format!("{stem}_refl"), ty, lhs.clone(), lhs));
        assert!(extended, "{head}: reflexivity on the stuck term, Extended");
        entry.unwrap_or_else(|e| panic!("{head}: reflexivity on the stuck term: {e:?}"));
    }
}
