// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Regression: the prelude's `Trans` must be Lean's `Trans`, not a stub.**
//!
//! # What broke
//!
//! `.olean` import is first-registered-wins — "Duplicate constants (already in
//! `env`) are skipped, not overwritten" (`clean-olean/src/import/load.rs`,
//! enforced at `import/load_register.rs`). The kernel prelude used to seed a
//! *simplified* `Trans`: THREE universe params, all three relations hardcoded
//! `Prop`-valued, and no `outParam` on `t`. Lean's real `Trans` has SIX universe
//! params, `Sort`-valued relations, and `t : outParam (α → γ → Sort w)`.
//!
//! The stub therefore shadowed Lean's class permanently, and every imported
//! `Trans` instance — whose type is spelled `Trans.{u,v,w,u_1,u_2,u_3} …` —
//! stopped matching. Measured on a real `import Init` (Lean v4.30.0-rc2) before
//! the fix: `Trans.trans h₁ h₂` applied DIRECTLY, with no `calc` anywhere,
//! failed on `Nat ≤`, on mixed `Nat < / ≤`, on `List.Sublist`, on `List.Perm`,
//! and `inferInstance` for a `Trans` instance failed, with
//!
//! ```text
//! expected `Trans {1, 1, 1} …` … got `Trans {0, 0, 0, 1, 1, 1} …`
//! ```
//!
//! # Why the decoys below are `Axiom`-kind and value-less
//!
//! This is the shape an imported declaration actually has when Clean re-checks
//! it: a `Declaration::Axiom` with a type and **no value**, and NOT one of
//! Clean's own `@[reducible]` prelude instances. A test written against Clean's
//! reducible Nat instances would pass either way — the elaborator can unfold its
//! way out of a universe mismatch there — so it would prove nothing. Every decoy
//! constant in this file is deliberately `Declaration::Axiom`, value-less, and
//! spelled the way the `.olean` spells it.
//!
//! Each test in this file FAILS against the pre-fix 3-universe stub.

use crate::env::{Declaration, Environment};
use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

/// `Sort 1` = `Type 0`.
fn type0() -> Expr {
    Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
}

/// `Prop` = `Sort 0`.
fn prop() -> Expr {
    Expr::from_kind(ExprKind::Sort(Level::zero()))
}

/// Lean's six universe arguments for a `Prop`-valued relation on a `Type 0`
/// carrier: `Trans.{0, 0, 0, 1, 1, 1}`.
fn lean_trans_levels() -> Vec<Level> {
    vec![
        Level::zero(),
        Level::zero(),
        Level::zero(),
        Level::succ(Level::zero()),
        Level::succ(Level::zero()),
        Level::succ(Level::zero()),
    ]
}

/// Seed a prelude plus three VALUE-LESS `Declaration::Axiom` decoys standing in
/// for imported constants:
///
/// * `TestCarrier : Type`
/// * `TestRel : TestCarrier → TestCarrier → Prop`
/// * `instTransTestRel : Trans.{0,0,0,1,1,1} TestCarrier … TestRel TestRel TestRel`
///
/// The third one is the load-bearing decoy: registering it AT ALL requires the
/// environment's `Trans` to accept six universe arguments, which the old stub
/// did not.
fn env_with_imported_shaped_decoys() -> Result<Environment, crate::env::EnvError> {
    let mut env = Environment::with_prelude();

    let carrier = Expr::const_(Name::from_string("TestCarrier"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("TestCarrier"),
        level_params: vec![],
        type_: type0(),
    })?;

    // TestRel : TestCarrier → TestCarrier → Prop
    let rel_type = Expr::arrow(carrier.clone(), Expr::arrow(carrier.clone(), prop()));
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("TestRel"),
        level_params: vec![],
        type_: rel_type,
    })?;
    let rel = Expr::const_(Name::from_string("TestRel"), vec![]);

    // instTransTestRel : Trans.{0,0,0,1,1,1} C C C TestRel TestRel TestRel
    let inst_type = Expr::apps(
        Expr::const_(Name::from_string("Trans"), lean_trans_levels()),
        [
            carrier.clone(),
            carrier.clone(),
            carrier.clone(),
            rel.clone(),
            rel.clone(),
            rel.clone(),
        ],
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("instTransTestRel"),
        level_params: vec![],
        type_: inst_type,
    })?;

    Ok(env)
}

/// The prelude's `Trans` must accept Lean's SIX universe arguments.
///
/// Pre-fix this fails at `add_decl` with a level-count mismatch, because the
/// stub declared only `[u_1, u_2, u_3]`.
#[test]
fn test_trans_accepts_lean_six_universe_instance_axiom() {
    let env = env_with_imported_shaped_decoys()
        .expect("a value-less Trans instance axiom spelled the way Lean spells it must register");
    assert!(
        env.get_const(&Name::from_string("instTransTestRel"))
            .is_some(),
        "the imported-shape Trans instance decoy must be in the environment"
    );
}

/// `Trans.trans` applied to a VALUE-LESS imported-shape instance must produce
/// `TestRel a c` — the direct, `calc`-free composition that the stub blocked.
#[test]
fn test_trans_trans_composes_over_value_less_instance_axiom() {
    let mut env = env_with_imported_shaped_decoys().expect("decoy environment");

    let carrier = Expr::const_(Name::from_string("TestCarrier"), vec![]);
    let rel = Expr::const_(Name::from_string("TestRel"), vec![]);
    let inst = Expr::const_(Name::from_string("instTransTestRel"), vec![]);
    let rel_app = |x: &Expr, y: &Expr| Expr::apps(rel.clone(), [x.clone(), y.clone()]);

    // Three value-less endpoint axioms and two value-less hypothesis axioms —
    // again the imported shape, so nothing here can be discharged by unfolding
    // one of Clean's own reducible definitions.
    for name in ["ta", "tb", "tc"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: carrier.clone(),
        })
        .expect("endpoint axiom");
    }
    let a = Expr::const_(Name::from_string("ta"), vec![]);
    let b = Expr::const_(Name::from_string("tb"), vec![]);
    let c = Expr::const_(Name::from_string("tc"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hab"),
        level_params: vec![],
        type_: rel_app(&a, &b),
    })
    .expect("hab axiom");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hbc"),
        level_params: vec![],
        type_: rel_app(&b, &c),
    })
    .expect("hbc axiom");

    // @Trans.trans.{0,0,0,1,1,1} C C C TestRel TestRel TestRel inst a b c hab hbc
    let term = Expr::apps(
        Expr::const_(Name::from_string("Trans.trans"), lean_trans_levels()),
        [
            carrier.clone(),
            carrier.clone(),
            carrier.clone(),
            rel.clone(),
            rel.clone(),
            rel.clone(),
            inst,
            a.clone(),
            b.clone(),
            c.clone(),
            Expr::const_(Name::from_string("hab"), vec![]),
            Expr::const_(Name::from_string("hbc"), vec![]),
        ],
    );

    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(&term)
        .expect("Trans.trans over an imported-shape instance must type-check");
    assert_eq!(
        inferred,
        rel_app(&a, &c),
        "Trans.trans h₁ h₂ must have type `TestRel ta tc`"
    );
}

/// `Trans`'s `t` parameter must carry Lean's `outParam` marker, and `outParam`
/// itself must be a reducible identity in the prelude.
///
/// Without the marker, instance synthesis has to MATCH a `t` the caller already
/// fixed instead of letting the instance determine it — which is precisely why
/// Lean marks it. `clean-olean`'s class-extension decoder pins Lean's value for
/// this class at `out_params == vec![5]`
/// (`crates/clean-olean/src/import/tests_class_ext_import.rs`).
#[test]
fn test_trans_third_relation_is_an_out_param() {
    let env = Environment::with_prelude();

    let out_param = env
        .get_const(&Name::from_string("outParam"))
        .expect("the prelude must define `outParam`");
    assert_eq!(
        out_param.level_params.len(),
        1,
        "outParam is universe-polymorphic in exactly one level"
    );
    assert!(
        out_param.value.is_some(),
        "outParam must be a reducible IDENTITY (it has a body), not an opaque axiom"
    );

    let trans = env
        .get_const(&Name::from_string("Trans"))
        .expect("the prelude must define `Trans`");
    assert_eq!(
        trans.level_params.len(),
        6,
        "Lean's `Trans` carries six universe params [u, v, w, u_1, u_2, u_3]; a \
         smaller count silently discards Lean's class on import"
    );

    // Walk to the sixth binder (α, β, γ, r, s, t) and check its domain is
    // `outParam _`.
    let mut ty = &trans.type_;
    let mut domain = None;
    for _ in 0..6 {
        match ty.kind() {
            ExprKind::Pi(_, dom, body) => {
                domain = Some(dom.as_ref().clone());
                ty = body;
            }
            other => panic!("Trans should have six leading binders, found {other:?}"),
        }
    }
    let t_domain = domain.expect("sixth binder");
    let head = match t_domain.kind() {
        ExprKind::App(f, _) => f.as_ref().clone(),
        other => panic!("`t`'s domain should be `outParam _`, found {other:?}"),
    };
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name.to_string(),
            "outParam",
            "`t` must be wrapped in Lean's `outParam` marker"
        ),
        other => panic!("`t`'s domain head should be `outParam`, found {other:?}"),
    }

    // And the class registry must agree with the serialized Lean value.
    let class_info = env
        .get_class_info(&Name::from_string("Trans"))
        .expect("Trans must be registered as a type class");
    assert_eq!(class_info.num_params, 6);
    assert_eq!(
        class_info.out_params,
        vec![5],
        "Lean serializes `Trans`'s out-param set as {{5}} (the `t` relation)"
    );
}

/// The kernel's own Nat `Trans` instances must be spelled at Lean's universe
/// arity too — otherwise they would be the new shadowing stub.
#[test]
fn test_kernel_nat_trans_instances_use_lean_universe_arity() {
    let env = Environment::with_prelude();

    for inst in ["instTransNatLt", "instTransNatLtLeLt", "instTransNatLeLtLt"] {
        let name = Name::from_string(inst);
        let Some(info) = env.get_const(&name) else {
            continue; // not seeded in this prelude configuration
        };
        // The instance type is `Trans.{…} Nat Nat Nat r s t`; walk to the head.
        let mut head = &info.type_;
        while let ExprKind::App(f, _) = head.kind() {
            head = f;
        }
        let ExprKind::Const(head_name, levels) = head.kind() else {
            panic!("{inst}: instance type head should be a constant");
        };
        assert_eq!(
            head_name.to_string(),
            "Trans",
            "{inst}: head should be Trans"
        );
        assert_eq!(
            levels.len(),
            6,
            "{inst}: must spell `Trans` with Lean's six universe arguments"
        );
    }
}
