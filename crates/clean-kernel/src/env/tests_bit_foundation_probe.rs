// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Track CC (axiom-free bit-arithmetic foundation) — verified foundation facts.
//!
//! These tests pin the EMPIRICAL state of the well-founded recursion stack that
//! the bit-arithmetic foundation builds on, and document the boundary of what
//! reduces definitionally. They are kernel-level regression guards.
//!
//! Headline findings (Track CC, this wave):
//!  1. `Acc` is a real inductive; `Acc.rec` is a genuine kernel-generated
//!     recursor (NOT axiom-stubbed); `WellFounded.fix`/`fixF` are axiom-free
//!     `Definition`s whose `axiom_deps` are EMPTY.
//!  2. `WellFounded.fixF` iota-reduces on an `Acc.intro` proof — so the
//!     well-founded unfolding equation holds DEFINITIONALLY (no `fixFEq`
//!     axiom is required to unfold WF-recursive definitions).
//!  3. The pair-carry `div2` encoding's two-step equation
//!     `div2 (n+2) = succ (div2 n)` does NOT hold by `rfl` for SYMBOLIC `n`
//!     (the `Bool.rec` on the parity flag is stuck) — the kernel correctly
//!     reports them as not def-eq. (This is why a sound `div2_lt_self`
//!     needs proven parity lemmas, not a symbolic two-step `rfl`.)

use super::types::ConstantKind;
use super::*;
use crate::tc::TypeChecker;

fn kind_of(env: &Environment, name: &str) -> &'static str {
    match env.get_const(&Name::from_string(name)) {
        Some(info) => match info.kind {
            ConstantKind::Axiom => "Axiom",
            ConstantKind::Definition => "Definition",
            ConstantKind::Theorem => "Theorem",
            ConstantKind::Opaque => "Opaque",
        },
        None => {
            if env.get_inductive(&Name::from_string(name)).is_some() {
                "Inductive"
            } else if env.get_recursor(&Name::from_string(name)).is_some() {
                "Recursor"
            } else {
                "MISSING"
            }
        }
    }
}

/// Finding 1: the WF recursion stack is real and axiom-free.
#[test]
fn wf_stack_is_axiom_free() {
    let mut env = Environment::with_prelude();
    env.init_well_founded().unwrap();

    // Acc.rec is a genuine kernel recursor with a real reduction rule.
    let acc_rec = env
        .get_recursor(&Name::from_string("Acc.rec"))
        .expect("Acc.rec is a kernel recursor");
    assert_eq!(acc_rec.rules.len(), 1, "Acc.rec has one reduction rule");
    assert_eq!(
        acc_rec.rules[0].constructor_name,
        Name::from_string("Acc.intro")
    );

    // WellFounded.fix / fixF are Definitions (not Axioms) with EMPTY axiom_deps.
    assert_eq!(kind_of(&env, "WellFounded.fix"), "Definition");
    assert_eq!(kind_of(&env, "WellFounded.fixF"), "Definition");
    for n in ["WellFounded.fix", "WellFounded.fixF"] {
        let deps = env.axiom_deps(&Name::from_string(n)).unwrap_or_default();
        assert!(
            deps.is_empty(),
            "{n} must be axiom-free, found deps: {deps:?}"
        );
    }

    // `Nat.testBit` has been DISCHARGED to a real axiom-free Definition (the
    // parity of the i-fold `Nat.div2` of n) — see `algebra_nat_testbit_def.rs`.
    assert_eq!(kind_of(&env, "Nat.testBit"), "Definition");
    let testbit_deps = env
        .axiom_deps(&Name::from_string("Nat.testBit"))
        .unwrap_or_default();
    assert!(
        testbit_deps.is_empty(),
        "Nat.testBit must be axiom-free, found deps: {testbit_deps:?}"
    );
    // Track II: the bitwise ops have been DISCHARGED to real axiom-free
    // Definitions `Nat.bitwise and/or/xor` (see `algebra_nat_bitwise_def.rs`).
    // `Nat.land`/`lor`/`xor` are now reducible Definitions, not Axioms, and
    // `Nat.bitwise` itself is a Definition with an empty axiom closure.
    for n in ["Nat.land", "Nat.lor", "Nat.xor", "Nat.bitwise"] {
        assert_eq!(
            kind_of(&env, n),
            "Definition",
            "{n} should be discharged to a Definition"
        );
        let deps = env.axiom_deps(&Name::from_string(n)).unwrap_or_default();
        assert!(
            deps.is_empty(),
            "{n} must be axiom-free, found deps: {deps:?}"
        );
    }
}

/// Finding 2 (THE CRUX): `WellFounded.fixF` iota-reduces on `Acc.intro`.
///
/// We build a concrete WF "recursion" over the empty relation
/// `r := fun _ _ => False` on `Nat`, with `C := fun _ => Nat`,
/// `F := fun _ _ => 5`, and `acc0 := Acc.intro 0 (fun y p => False.elim _ p)`.
/// Then `fixF F 0 acc0` must reduce to `5` — which can only happen if
/// `Acc.rec` genuinely iota-reduces on `Acc.intro`.
#[test]
fn fixf_iota_reduces_on_acc_intro() {
    use super::decl_builder::EnvDeclBuilder;
    use crate::expr::BinderInfo;
    use crate::level::Level;

    let mut env = Environment::with_prelude();
    env.init_well_founded().unwrap();

    let nat = Expr::const_str("Nat");
    let false_const = Expr::const_str("False");
    let zero = Expr::nat_lit(0);
    let lvl1 = Level::succ(Level::zero());
    let acc_const = Expr::const_(Name::from_string("Acc"), vec![lvl1.clone()]);
    let acc_intro = Expr::const_(Name::from_string("Acc.intro"), vec![lvl1.clone()]);
    let false_elim = Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);

    // emptyRel : Nat → Nat → Prop := fun _ _ => False
    let empty_rel = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, _x) = b.fresh_local(nat.clone());
        let (y_id, _y) = b.fresh_local(nat.clone());
        let t = b.mk_lam(y_id, BinderInfo::Default, nat.clone(), false_const.clone());
        let t = b.mk_lam(x_id, BinderInfo::Default, nat.clone(), t);
        b.finish(t)
    };
    // C : Nat → Sort 1 := fun _ => Nat
    let c_fun = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, _a) = b.fresh_local(nat.clone());
        let t = b.mk_lam(a_id, BinderInfo::Default, nat.clone(), nat.clone());
        b.finish(t)
    };
    // F := fun (x : Nat) (_ih : (y:Nat) → emptyRel y x → Nat) => 5
    let f_fun = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(nat.clone());
        let ih_type = {
            let mut s = EnvDeclBuilder::child_of(&b);
            let (y_id, y) = s.fresh_local(nat.clone());
            let rel_y_x = Expr::app(Expr::app(empty_rel.clone(), y.clone()), x.clone());
            let inner = {
                let mut s2 = EnvDeclBuilder::child_of(&s);
                let (p_id, _p) = s2.fresh_local(rel_y_x.clone());
                let t = s2.mk_pi(p_id, BinderInfo::Default, rel_y_x.clone(), nat.clone());
                s2.finish_child(t)
            };
            let t = s.mk_pi(y_id, BinderInfo::Default, nat.clone(), inner);
            s.finish_child(t)
        };
        let (ih_id, _ih) = b.fresh_local(ih_type.clone());
        let t = b.mk_lam(ih_id, BinderInfo::Default, ih_type, Expr::nat_lit(5));
        let t = b.mk_lam(x_id, BinderInfo::Default, nat.clone(), t);
        b.finish(t)
    };
    // acc0 := Acc.intro {Nat} emptyRel 0 (fun y (p : emptyRel y 0) => False.elim (Acc emptyRel y) p)
    let acc0 = {
        let b = EnvDeclBuilder::new();
        let h = {
            let mut s = EnvDeclBuilder::child_of(&b);
            let (y_id, y) = s.fresh_local(nat.clone());
            let rel_y_0 = Expr::app(Expr::app(empty_rel.clone(), y.clone()), zero.clone());
            let acc_rel_y = Expr::app(
                Expr::app(Expr::app(acc_const.clone(), nat.clone()), empty_rel.clone()),
                y.clone(),
            );
            let inner = {
                let mut s2 = EnvDeclBuilder::child_of(&s);
                let (p_id, p) = s2.fresh_local(rel_y_0.clone());
                let body = Expr::app(Expr::app(false_elim.clone(), acc_rel_y.clone()), p.clone());
                let t = s2.mk_lam(p_id, BinderInfo::Default, rel_y_0.clone(), body);
                s2.finish_child(t)
            };
            let t = s.mk_lam(y_id, BinderInfo::Default, nat.clone(), inner);
            s.finish_child(t)
        };
        let t = Expr::apps(acc_intro, [nat.clone(), empty_rel.clone(), zero.clone(), h]);
        b.finish(t)
    };

    let tc = TypeChecker::new(&env);
    let _ = tc.infer_type(&acc0).expect("acc0 type-checks");

    let fix_f = Expr::const_(
        Name::from_string("WellFounded.fixF"),
        vec![lvl1.clone(), lvl1.clone()],
    );
    let lhs = Expr::apps(fix_f, [nat.clone(), empty_rel, c_fun, f_fun, zero, acc0]);
    let _ = tc.infer_type(&lhs).expect("fixF application type-checks");

    assert!(
        tc.is_def_eq(&lhs, &Expr::nat_lit(5)),
        "WellFounded.fixF must iota-reduce on Acc.intro (Acc.rec computes)"
    );
}
