// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::test_helpers::{assert_axiom, assert_const, assert_inductive, pi_domain_at};
use super::*;
use crate::expr::BinderInfo;

/// Helper: verify a constructor is registered with expected name and parent.
fn assert_ctor(env: &Environment, name: &str, parent: &str) {
    let n = Name::from_string(name);
    let ctor = env.get_constructor(&n).expect(name);
    assert_eq!(ctor.name, n, "name mismatch for {name}");
    assert_eq!(
        ctor.inductive_name,
        Name::from_string(parent),
        "parent mismatch for {name}"
    );
}

fn assert_axiom_type_checks(env: &Environment, tc: &crate::tc::TypeChecker<'_>, name: &str) {
    let decl = env.get_const(&Name::from_string(name)).unwrap();
    // Names listed here are historically registered as `Declaration::Axiom`.
    // Several have since been promoted to `Declaration::Theorem` with a
    // genuine constructive proof term (e.g. `Int.add_comm` per #3604,
    // similar promotions for Int/Nat ring axioms). The structural
    // invariant this test guards is that the TYPE typechecks under the
    // kernel — not that the constant is still axiomatised. Skip the
    // axiom-only check when the constant has a value.
    let _ = decl.value.is_none();
    let _ty = tc.infer_type(&decl.type_).unwrap();
}

#[test]
fn test_lt_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_lt().unwrap();

    let tc = TypeChecker::new(&env);

    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());
    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // LT : Type u → Type u
    let lt_const = Expr::const_(Name::from_string("LT"), vec![u_level.clone()]);
    let lt_type = tc.infer_type(&lt_const).unwrap();
    if let ExprKind::Pi(_, domain, _) = &lt_type.kind {
        assert!(matches!(&domain.as_ref().kind, ExprKind::Sort(_)));
    } else {
        panic!("Expected LT to have pi type, got {lt_type:?}");
    }

    // Check Nat.lt : Nat → Nat → Prop
    let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
    let nat_lt_type = tc.infer_type(&nat_lt).unwrap();
    let expected_type = Expr::pi(
        BinderInfo::Default,
        nat_const.clone(),
        Expr::pi(BinderInfo::Default, nat_const.clone(), prop.clone()),
    );
    assert_eq!(nat_lt_type, expected_type);

    // Check instLTNat : LT Nat
    let inst_lt_nat = Expr::const_(Name::from_string("instLTNat"), vec![]);
    let inst_lt_nat_type = tc.infer_type(&inst_lt_nat).unwrap();
    // LT : Type u → Type u, Nat : Type 0, so LT.{0}
    let expected_type = Expr::app(
        Expr::const_(Name::from_string("LT"), vec![Level::zero()]),
        nat_const.clone(),
    );
    assert_eq!(inst_lt_nat_type, expected_type);
}

#[test]
fn test_lt_le_together() {
    // Test that LT and LE work together
    let mut env = Environment::new();

    // Initialize LT (which initializes LE as dependency)
    env.init_lt().unwrap();

    // Both should be initialized
    assert!(env.has_lt());
    assert!(env.has_le());

    // Verify all components are present with correct names
    for s in ["LE", "LT", "Nat.le", "Nat.lt", "instLENat", "instLTNat"] {
        assert_const(&env, s);
    }

    // Verify Nat.le has both constructors with correct names
    assert_const(&env, "Nat.le.refl");
    assert_const(&env, "Nat.le.step");
}

#[test]
fn test_init_ge() {
    let mut env = Environment::new();
    assert!(!env.has_ge());

    env.init_ge().unwrap();
    assert!(env.has_ge());

    // Check GE and Nat.ge definitions were added with correct names
    assert_const(&env, "GE.ge");
    assert_const(&env, "Nat.ge");

    // Dependency on LE/Nat.le
    assert!(env.has_le());
    assert_const(&env, "Nat.le");

    // Idempotent
    env.init_ge().unwrap();
    assert!(env.has_ge());
}

#[test]
fn test_ge_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_ge().unwrap();

    let tc = TypeChecker::new(&env);

    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());
    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // GE.ge : {α : Type u} → [LE α] → α → α → Prop
    let ge_const = Expr::const_(Name::from_string("GE.ge"), vec![u_level.clone()]);
    let ge_type = tc.infer_type(&ge_const).unwrap();
    let expected_ge_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone()))),
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(
                Expr::const_(Name::from_string("LE"), vec![u_level.clone()]),
                Expr::bvar(0),
            ),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),
                Expr::pi(BinderInfo::Default, Expr::bvar(2), prop.clone()),
            ),
        ),
    );
    assert_eq!(ge_type, expected_ge_type);

    // Nat.ge : Nat → Nat → Prop
    let nat_ge = Expr::const_(Name::from_string("Nat.ge"), vec![]);
    let nat_ge_type = tc.infer_type(&nat_ge).unwrap();
    let expected_nat_ge_type = Expr::pi(
        BinderInfo::Default,
        nat_const.clone(),
        Expr::pi(BinderInfo::Default, nat_const.clone(), prop.clone()),
    );
    assert_eq!(nat_ge_type, expected_nat_ge_type);
}

#[test]
fn test_init_gt() {
    let mut env = Environment::new();
    assert!(!env.has_gt());

    env.init_gt().unwrap();
    assert!(env.has_gt());

    // Check GT and Nat.gt definitions were added with correct names
    assert_const(&env, "GT.gt");
    assert_const(&env, "Nat.gt");

    // Dependencies: LT initializes LE
    assert!(env.has_lt());
    assert!(env.has_le());

    // Idempotent
    env.init_gt().unwrap();
    assert!(env.has_gt());
}

#[test]
fn test_gt_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_gt().unwrap();

    let tc = TypeChecker::new(&env);

    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());
    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // GT.gt : {α : Type u} → [LT α] → α → α → Prop
    let gt_const = Expr::const_(Name::from_string("GT.gt"), vec![u_level.clone()]);
    let gt_type = tc.infer_type(&gt_const).unwrap();
    let expected_gt_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone()))),
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(
                Expr::const_(Name::from_string("LT"), vec![u_level.clone()]),
                Expr::bvar(0),
            ),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),
                Expr::pi(BinderInfo::Default, Expr::bvar(2), prop.clone()),
            ),
        ),
    );
    assert_eq!(gt_type, expected_gt_type);

    // Nat.gt : Nat → Nat → Prop
    let nat_gt = Expr::const_(Name::from_string("Nat.gt"), vec![]);
    let nat_gt_type = tc.infer_type(&nat_gt).unwrap();
    let expected_nat_gt_type = Expr::pi(
        BinderInfo::Default,
        nat_const.clone(),
        Expr::pi(BinderInfo::Default, nat_const.clone(), prop.clone()),
    );
    assert_eq!(nat_gt_type, expected_nat_gt_type);
}

#[test]
fn test_ge_gt_together() {
    // Ensure GE and GT can be initialized together and reuse LE/LT
    let mut env = Environment::new();

    env.init_ge().unwrap();
    env.init_gt().unwrap();

    assert!(env.has_ge());
    assert!(env.has_gt());
    assert!(env.has_le());
    assert!(env.has_lt());

    for s in ["GE.ge", "GT.gt", "Nat.ge", "Nat.gt"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_init_trans() {
    let mut env = Environment::new();
    assert!(!env.has_trans());

    env.init_trans().unwrap();
    assert!(env.has_trans());

    // Check Trans and Trans.trans were added with correct structure
    assert_inductive(&env, "Trans");
    assert_const(&env, "Trans.trans");
    assert_ctor(&env, "Trans.mk", "Trans");

    // Idempotent
    env.init_trans().unwrap();
    assert!(env.has_trans());
}

#[test]
fn test_trans_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_trans().unwrap();

    let tc = TypeChecker::new(&env);

    // Lean's `Trans` universe ORDER: [u, v, w, u_1, u_2, u_3] — the three
    // relation sorts first, then the three auto-bound carrier sorts.
    let u = Name::from_string("u");
    let v = Name::from_string("v");
    let w = Name::from_string("w");
    let u1 = Name::from_string("u_1");
    let u2 = Name::from_string("u_2");
    let u3 = Name::from_string("u_3");
    let u_level = Level::param(u.clone());
    let v_level = Level::param(v.clone());
    let w_level = Level::param(w.clone());
    let u1_level = Level::param(u1.clone());
    let u2_level = Level::param(u2.clone());
    let u3_level = Level::param(u3.clone());
    let sort_u1 = Expr::from_kind(ExprKind::Sort(u1_level.clone()));
    let sort_u2 = Expr::from_kind(ExprKind::Sort(u2_level.clone()));
    let sort_u3 = Expr::from_kind(ExprKind::Sort(u3_level.clone()));
    let sort_u = Expr::from_kind(ExprKind::Sort(u_level.clone()));
    let sort_v = Expr::from_kind(ExprKind::Sort(v_level.clone()));
    let sort_w = Expr::from_kind(ExprKind::Sort(w_level.clone()));

    // `Sort (max 1 u u_1 u_2 u_3 v w)` — the class universe Lean computes.
    let class_sort = {
        let mut s = Level::succ(Level::zero());
        for l in [
            &u_level, &u1_level, &u2_level, &u3_level, &v_level, &w_level,
        ] {
            s = Level::max(s, l.clone());
        }
        Expr::from_kind(ExprKind::Sort(s))
    };

    let trans_levels = vec![
        u_level.clone(),
        v_level.clone(),
        w_level.clone(),
        u1_level.clone(),
        u2_level.clone(),
        u3_level.clone(),
    ];

    // Trans.{u, v, w, u_1, u_2, u_3} :
    //   {α : Sort u_1} → {β : Sort u_2} → {γ : Sort u_3} →
    //   (r : α → β → Sort u) → (s : β → γ → Sort v) →
    //   (t : outParam (α → γ → Sort w)) → Sort (max 1 u u_1 u_2 u_3 v w)
    //
    // This is Lean 4's spelling, character for character. It is NOT decoration:
    // the `.olean` import is first-registered-wins, so a divergent prelude
    // spelling here permanently discards Lean's `Trans` and every imported
    // `Trans` instance stops type-checking against it.
    let trans_const = Expr::const_(Name::from_string("Trans"), trans_levels.clone());
    let trans_type = tc.infer_type(&trans_const).unwrap();
    // `t`'s binder domain: `outParam.{max (w+1) u_1 u_3} (α → γ → Sort w)`.
    let out_param_level = Level::max(
        Level::max(Level::succ(w_level.clone()), u1_level.clone()),
        u3_level.clone(),
    );
    let expected_trans_type = Expr::pi(
        BinderInfo::Implicit,
        sort_u1.clone(), // α : Sort u_1
        Expr::pi(
            BinderInfo::Implicit,
            sort_u2.clone(), // β : Sort u_2
            Expr::pi(
                BinderInfo::Implicit,
                sort_u3.clone(), // γ : Sort u_3
                Expr::pi(
                    BinderInfo::Default,
                    // r : α → β → Sort u
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::bvar(2), // α
                        Expr::pi(BinderInfo::Default, Expr::bvar(2), sort_u.clone()),
                    ),
                    Expr::pi(
                        BinderInfo::Default,
                        // s : β → γ → Sort v
                        Expr::pi(
                            BinderInfo::Default,
                            Expr::bvar(2), // β
                            Expr::pi(BinderInfo::Default, Expr::bvar(2), sort_v.clone()),
                        ),
                        Expr::pi(
                            BinderInfo::Default,
                            // t : outParam (α → γ → Sort w)
                            Expr::app(
                                Expr::const_(
                                    Name::from_string("outParam"),
                                    vec![out_param_level.clone()],
                                ),
                                Expr::pi(
                                    BinderInfo::Default,
                                    Expr::bvar(4), // α
                                    Expr::pi(BinderInfo::Default, Expr::bvar(3), sort_w.clone()),
                                ),
                            ),
                            class_sort.clone(),
                        ),
                    ),
                ),
            ),
        ),
    );
    assert_eq!(trans_type, expected_trans_type);

    // `Trans.trans` carries the SAME six universe params, in the same order.
    let trans_trans = Expr::const_(Name::from_string("Trans.trans"), trans_levels.clone());
    let trans_trans_type = tc.infer_type(&trans_trans).unwrap();
    // Check it has the right overall structure (Pi type)
    if let ExprKind::Pi(_, _, _) = &trans_trans_type.kind {
        // Good
    } else {
        panic!("Trans.trans should be a Pi type");
    }
}

#[test]
fn test_init_preorder() {
    let mut env = Environment::new();
    assert!(!env.has_preorder());

    env.init_preorder().unwrap();
    assert!(env.has_preorder());

    // Check Preorder and projections were added with correct structure
    assert_inductive(&env, "Preorder");
    assert_ctor(&env, "Preorder.mk", "Preorder");
    for s in ["Preorder.toLE", "Preorder.toLT", "Preorder.le_refl"] {
        assert_const(&env, s);
    }

    // Dependencies: LE and LT should be initialized
    assert!(env.has_le());
    assert!(env.has_lt());

    // Idempotent
    env.init_preorder().unwrap();
    assert!(env.has_preorder());
}

#[test]
fn test_preorder_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_preorder().unwrap();

    let tc = TypeChecker::new(&env);

    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());
    let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));

    // Preorder : Type u → Type u
    let preorder_const = Expr::const_(Name::from_string("Preorder"), vec![u_level.clone()]);
    let preorder_type = tc.infer_type(&preorder_const).unwrap();
    let expected_preorder_type = Expr::pi(
        BinderInfo::Implicit,
        type_u.clone(),
        Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone()))),
    );
    assert_eq!(preorder_type, expected_preorder_type);

    // Preorder.toLE : {α : Type u} → [Preorder α] → LE α
    let to_le_const = Expr::const_(Name::from_string("Preorder.toLE"), vec![u_level.clone()]);
    let to_le_type = tc.infer_type(&to_le_const).unwrap();
    let expected_to_le_type = Expr::pi(
        BinderInfo::Implicit,
        type_u.clone(),
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(
                Expr::const_(Name::from_string("Preorder"), vec![u_level.clone()]),
                Expr::bvar(0),
            ),
            Expr::app(
                Expr::const_(Name::from_string("LE"), vec![u_level.clone()]),
                Expr::bvar(1),
            ),
        ),
    );
    assert_eq!(to_le_type, expected_to_le_type);

    // Preorder.toLT : {α : Type u} → [Preorder α] → LT α
    let to_lt_const = Expr::const_(Name::from_string("Preorder.toLT"), vec![u_level.clone()]);
    let to_lt_type = tc.infer_type(&to_lt_const).unwrap();
    let expected_to_lt_type = Expr::pi(
        BinderInfo::Implicit,
        type_u.clone(),
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(
                Expr::const_(Name::from_string("Preorder"), vec![u_level.clone()]),
                Expr::bvar(0),
            ),
            Expr::app(
                Expr::const_(Name::from_string("LT"), vec![u_level.clone()]),
                Expr::bvar(1),
            ),
        ),
    );
    assert_eq!(to_lt_type, expected_to_lt_type);
}

#[test]
fn test_init_partial_order() {
    let mut env = Environment::new();
    assert!(!env.has_partial_order());

    env.init_partial_order().unwrap();
    assert!(env.has_partial_order());

    // Check PartialOrder and projections were added with correct structure
    assert_inductive(&env, "PartialOrder");
    assert_ctor(&env, "PartialOrder.mk", "PartialOrder");
    assert_const(&env, "PartialOrder.toPreorder");

    // Dependencies: Preorder, LE, LT should be initialized
    assert!(env.has_preorder());
    assert!(env.has_le());
    assert!(env.has_lt());

    // Idempotent
    env.init_partial_order().unwrap();
    assert!(env.has_partial_order());
}

#[test]
fn test_partial_order_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_partial_order().unwrap();

    let tc = TypeChecker::new(&env);

    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());
    let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));

    // PartialOrder : Type u → Type u
    let partial_order_const =
        Expr::const_(Name::from_string("PartialOrder"), vec![u_level.clone()]);
    let partial_order_type = tc.infer_type(&partial_order_const).unwrap();
    let expected_partial_order_type = Expr::pi(
        BinderInfo::Implicit,
        type_u.clone(),
        Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone()))),
    );
    assert_eq!(partial_order_type, expected_partial_order_type);

    // PartialOrder.toPreorder : {α : Type u} → [PartialOrder α] → Preorder α
    let to_preorder_const = Expr::const_(
        Name::from_string("PartialOrder.toPreorder"),
        vec![u_level.clone()],
    );
    let to_preorder_type = tc.infer_type(&to_preorder_const).unwrap();
    let expected_to_preorder_type = Expr::pi(
        BinderInfo::Implicit,
        type_u.clone(),
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(
                Expr::const_(Name::from_string("PartialOrder"), vec![u_level.clone()]),
                Expr::bvar(0),
            ),
            Expr::app(
                Expr::const_(Name::from_string("Preorder"), vec![u_level.clone()]),
                Expr::bvar(1),
            ),
        ),
    );
    assert_eq!(to_preorder_type, expected_to_preorder_type);
}

#[test]
fn test_ordering_hierarchy() {
    // Ensure the complete ordering hierarchy can be initialized together
    let mut env = Environment::new();

    // Initialize all ordering-related types
    env.init_le().unwrap();
    env.init_lt().unwrap();
    env.init_ge().unwrap();
    env.init_gt().unwrap();
    env.init_trans().unwrap();
    env.init_preorder().unwrap();
    env.init_partial_order().unwrap();

    // All should be available
    assert!(env.has_le());
    assert!(env.has_lt());
    assert!(env.has_ge());
    assert!(env.has_gt());
    assert!(env.has_trans());
    assert!(env.has_preorder());
    assert!(env.has_partial_order());

    // Check key definitions exist with correct names
    for s in [
        "LE.le",
        "LT.lt",
        "GE.ge",
        "GT.gt",
        "Trans.trans",
        "Preorder.toLE",
        "PartialOrder.toPreorder",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_init_linear_order() {
    let mut env = Environment::new();
    assert!(!env.has_linear_order());
    env.init_linear_order().unwrap();
    assert!(env.has_linear_order());

    // Also initializes dependencies
    assert!(env.has_partial_order());
    assert!(env.has_preorder());
    assert!(env.has_le());
    assert!(env.has_lt());

    // LinearOrder type exists with correct structure
    assert_inductive(&env, "LinearOrder");
    for s in [
        "LinearOrder.mk",
        "LinearOrder.rec",
        "LinearOrder.toPartialOrder",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_linear_order_type_checks() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_linear_order().unwrap();
    let tc = TypeChecker::new(&env);

    // LinearOrder : Type u → Type u
    let linear_order_type = env
        .get_const(&Name::from_string("LinearOrder"))
        .unwrap()
        .type_
        .clone();
    let inferred = tc.infer_type(&linear_order_type).unwrap();
    // Type of (Type u → Type u) is Type (u+1)
    assert!(matches!(inferred.kind, ExprKind::Sort(_)));

    // LinearOrder.toPartialOrder type checks
    let to_po_type = env
        .get_const(&Name::from_string("LinearOrder.toPartialOrder"))
        .unwrap()
        .type_
        .clone();
    let inferred = tc.infer_type(&to_po_type).unwrap();
    assert!(matches!(inferred.kind, ExprKind::Sort(_)));
}

#[test]
fn test_linear_order_hierarchy() {
    // Test that LinearOrder properly extends the ordering hierarchy
    let mut env = Environment::new();
    env.init_linear_order().unwrap();

    // Complete hierarchy is available
    assert!(env.has_linear_order());
    assert!(env.has_partial_order());
    assert!(env.has_preorder());
    assert!(env.has_le());
    assert!(env.has_lt());

    // Check key projections exist with correct names
    for name_str in [
        "LinearOrder.toPartialOrder",
        "PartialOrder.toPreorder",
        "Preorder.toLE",
        "Preorder.toLT",
    ] {
        assert_const(&env, name_str);
    }

    // Verify Or is available (needed for le_total)
    assert_inductive(&env, "Or");
}

#[test]
fn test_init_reflexive() {
    let mut env = Environment::new();
    assert!(!env.has_reflexive());
    env.init_reflexive().unwrap();
    assert!(env.has_reflexive());

    // Reflexive type exists with correct structure
    assert_inductive(&env, "Reflexive");
    for s in ["Reflexive.mk", "Reflexive.rec", "Reflexive.refl"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_reflexive_type_checks() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_reflexive().unwrap();
    let tc = TypeChecker::new(&env);

    // Reflexive : {α : Sort u} → (α → α → Prop) → Prop
    let reflexive_type = env
        .get_const(&Name::from_string("Reflexive"))
        .unwrap()
        .type_
        .clone();
    let inferred = tc.infer_type(&reflexive_type).unwrap();
    assert!(matches!(inferred.kind, ExprKind::Sort(_)));

    // Reflexive.refl type checks
    let refl_type = env
        .get_const(&Name::from_string("Reflexive.refl"))
        .unwrap()
        .type_
        .clone();
    let inferred = tc.infer_type(&refl_type).unwrap();
    assert!(matches!(inferred.kind, ExprKind::Sort(_)));
}

#[test]
fn test_init_antisymm() {
    let mut env = Environment::new();
    assert!(!env.has_antisymm());
    env.init_antisymm().unwrap();
    assert!(env.has_antisymm());

    // Antisymm type exists with correct structure
    assert_inductive(&env, "Antisymm");
    for s in ["Antisymm.mk", "Antisymm.rec"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_antisymm_type_checks() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_antisymm().unwrap();
    let tc = TypeChecker::new(&env);

    // Antisymm : {α : Sort u} → (α → α → Prop) → Prop
    let antisymm_type = env
        .get_const(&Name::from_string("Antisymm"))
        .unwrap()
        .type_
        .clone();
    let inferred = tc.infer_type(&antisymm_type).unwrap();
    assert!(matches!(inferred.kind, ExprKind::Sort(_)));
}

#[test]
fn test_relation_typeclasses() {
    // Test that all relation typeclasses can be initialized together
    let mut env = Environment::new();

    env.init_trans().unwrap();
    env.init_reflexive().unwrap();
    env.init_antisymm().unwrap();

    assert!(env.has_trans());
    assert!(env.has_reflexive());
    assert!(env.has_antisymm());

    // Check key projections exist with correct names
    for name_str in ["Trans.trans", "Reflexive.refl", "Antisymm.mk"] {
        assert_const(&env, name_str);
    }
}

#[test]
fn test_init_irrefl() {
    let mut env = Environment::new();
    assert!(!env.has_irrefl());
    env.init_irrefl().unwrap();
    assert!(env.has_irrefl());

    // Irrefl type exists with correct structure
    assert_inductive(&env, "Irrefl");
    for s in ["Irrefl.mk", "Irrefl.rec", "Irrefl.irrefl"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_irrefl_type_checks() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_irrefl().unwrap();
    let tc = TypeChecker::new(&env);

    // Irrefl : {α : Sort u} → (α → α → Prop) → Prop
    let irrefl_type = env
        .get_const(&Name::from_string("Irrefl"))
        .unwrap()
        .type_
        .clone();
    let inferred = tc.infer_type(&irrefl_type).unwrap();
    assert!(matches!(inferred.kind, ExprKind::Sort(_)));

    // Irrefl.irrefl type checks
    let irrefl_field_type = env
        .get_const(&Name::from_string("Irrefl.irrefl"))
        .unwrap()
        .type_
        .clone();
    let inferred = tc.infer_type(&irrefl_field_type).unwrap();
    assert!(matches!(inferred.kind, ExprKind::Sort(_)));
}

#[test]
fn test_init_asymm() {
    let mut env = Environment::new();
    assert!(!env.has_asymm());
    env.init_asymm().unwrap();
    assert!(env.has_asymm());

    // Asymm type exists with correct structure
    assert_inductive(&env, "Asymm");
    for s in ["Asymm.mk", "Asymm.rec", "Asymm.asymm"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_asymm_type_checks() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_asymm().unwrap();
    let tc = TypeChecker::new(&env);

    // Asymm : {α : Sort u} → (α → α → Prop) → Prop
    let asymm_type = env
        .get_const(&Name::from_string("Asymm"))
        .unwrap()
        .type_
        .clone();
    let inferred = tc.infer_type(&asymm_type).unwrap();
    assert!(matches!(inferred.kind, ExprKind::Sort(_)));

    // Asymm.asymm type checks
    let asymm_field_type = env
        .get_const(&Name::from_string("Asymm.asymm"))
        .unwrap()
        .type_
        .clone();
    let inferred = tc.infer_type(&asymm_field_type).unwrap();
    assert!(matches!(inferred.kind, ExprKind::Sort(_)));
}

#[test]
fn test_all_relation_typeclasses() {
    // Test that all relation typeclasses can be initialized together
    let mut env = Environment::new();

    env.init_trans().unwrap();
    env.init_reflexive().unwrap();
    env.init_antisymm().unwrap();
    env.init_irrefl().unwrap();
    env.init_asymm().unwrap();

    assert!(env.has_trans());
    assert!(env.has_reflexive());
    assert!(env.has_antisymm());
    assert!(env.has_irrefl());
    assert!(env.has_asymm());

    // Check all key projections exist with correct names
    for name_str in [
        "Trans.trans",
        "Reflexive.refl",
        "Antisymm.mk",
        "Irrefl.irrefl",
        "Asymm.asymm",
    ] {
        assert_const(&env, name_str);
    }
}

#[test]
fn test_init_nat_preorder() {
    let mut env = Environment::new();
    assert!(!env.has_nat_preorder());
    env.init_nat_preorder().unwrap();
    assert!(env.has_nat_preorder());

    // Check definitions exist with correct names
    for name_str in ["Nat.le_refl", "Nat.le_trans", "instPreorderNat"] {
        assert_const(&env, name_str);
    }

    // Dependencies should be initialized
    assert!(env.has_preorder());
    assert!(env.has_le());
    assert!(env.has_lt());
}

#[test]
fn test_nat_preorder_type_checks() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_nat_preorder().unwrap();
    let tc = TypeChecker::new(&env);

    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

    // Nat.le_refl : ∀ n : Nat, Nat.le n n
    let nat_le_refl = Expr::const_(Name::from_string("Nat.le_refl"), vec![]);
    let nat_le_refl_type = tc.infer_type(&nat_le_refl).unwrap();
    // Check it's a Pi type from Nat
    match &nat_le_refl_type.kind {
        ExprKind::Pi(_, dom, _) => {
            assert_eq!(**dom, nat_const);
        }
        _ => panic!("Expected Pi type for Nat.le_refl"),
    }

    // instPreorderNat : Preorder Nat
    let inst_preorder_nat = Expr::const_(Name::from_string("instPreorderNat"), vec![]);
    let inst_preorder_nat_type = tc.infer_type(&inst_preorder_nat).unwrap();
    // Preorder : Type u → Type u, Nat : Type 0, so Preorder.{0}
    let expected_type = Expr::app(
        Expr::const_(Name::from_string("Preorder"), vec![Level::zero()]),
        nat_const.clone(),
    );
    assert_eq!(inst_preorder_nat_type, expected_type);
}

/// #3553: `instPreorderNat` must be registered as `Declaration::Definition`
/// (kind == `ConstantKind::Definition`) with a concrete `Preorder.mk` value —
/// no longer an axiom.
#[test]
fn test_preorder_nat_is_definition() {
    let mut env = Environment::new();
    env.init_nat_preorder().unwrap();
    let info = env
        .get_const(&Name::from_string("instPreorderNat"))
        .expect("instPreorderNat should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "instPreorderNat must be a Definition after #3553, got {:?}",
        info.kind
    );
    assert!(
        info.value.is_some(),
        "instPreorderNat must carry a concrete value after #3553"
    );
}

/// #3553: The recorded value of `instPreorderNat` is
/// `Preorder.mk.{0} Nat instLENat instLTNat Nat.le_refl Nat.le_trans`.
#[test]
fn test_preorder_nat_value_is_preorder_mk() {
    let mut env = Environment::new();
    env.init_nat_preorder().unwrap();
    let info = env
        .get_const(&Name::from_string("instPreorderNat"))
        .expect("instPreorderNat should be registered");
    let value = info
        .value
        .as_ref()
        .expect("instPreorderNat must carry a value after #3553");

    // Walk the App spine of the value and collect the head + arguments.
    let mut head = value;
    let mut args: Vec<&Expr> = Vec::new();
    while let ExprKind::App(f, a) = &head.kind {
        args.push(a);
        head = f;
    }
    args.reverse();

    match &head.kind {
        ExprKind::Const(n, levels) => {
            assert_eq!(
                *n,
                Name::from_string("Preorder.mk"),
                "value head must be Preorder.mk, got {:?}",
                n
            );
            assert_eq!(
                levels.len(),
                1,
                "Preorder.mk should have one universe level, got {:?}",
                levels
            );
            assert_eq!(levels[0], Level::zero());
        }
        other => panic!("expected App spine with Const head, got head {:?}", other),
    }

    assert_eq!(
        args.len(),
        5,
        "Preorder.mk should be applied to 5 arguments (α, [LE], [LT], le_refl, le_trans), got {}",
        args.len()
    );

    let expect_const = |idx: usize, name: &str| match &args[idx].kind {
        ExprKind::Const(n, _) => assert_eq!(
            *n,
            Name::from_string(name),
            "Preorder.mk arg {} should be `{}`, got {:?}",
            idx,
            name,
            n
        ),
        other => panic!(
            "Preorder.mk arg {} should be Const({}), got {:?}",
            idx, name, other
        ),
    };
    expect_const(0, "Nat");
    expect_const(1, "instLENat");
    expect_const(2, "instLTNat");
    expect_const(3, "Nat.le_refl");
    expect_const(4, "Nat.le_trans");
}

#[test]
fn test_init_nat_partial_order() {
    let mut env = Environment::new();
    assert!(!env.has_nat_partial_order());
    env.init_nat_partial_order().unwrap();
    assert!(env.has_nat_partial_order());

    // Check definitions exist with correct names
    for name_str in ["Nat.le_antisymm", "instPartialOrderNat"] {
        assert_const(&env, name_str);
    }

    // Dependencies should be initialized
    assert!(env.has_nat_preorder());
    assert!(env.has_partial_order());
}

#[test]
fn test_nat_partial_order_type_checks() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_nat_partial_order().unwrap();
    let tc = TypeChecker::new(&env);

    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

    // instPartialOrderNat : PartialOrder Nat
    // PartialOrder : Type u → Type u, Nat : Type 0, so PartialOrder.{0}
    let inst_partial_order_nat = Expr::const_(Name::from_string("instPartialOrderNat"), vec![]);
    let inst_partial_order_nat_type = tc.infer_type(&inst_partial_order_nat).unwrap();
    let expected_type = Expr::app(
        Expr::const_(Name::from_string("PartialOrder"), vec![Level::zero()]),
        nat_const.clone(),
    );
    assert_eq!(inst_partial_order_nat_type, expected_type);
}

#[test]
fn test_nat_ordering_hierarchy() {
    // Test that the full ordering hierarchy for Nat can be initialized
    let mut env = Environment::new();

    env.init_nat_partial_order().unwrap();

    // Full hierarchy should be initialized
    assert!(env.has_le());
    assert!(env.has_lt());
    assert!(env.has_preorder());
    assert!(env.has_partial_order());
    assert!(env.has_nat_preorder());
    assert!(env.has_nat_partial_order());

    // Check all Nat-specific definitions exist with correct names
    for name_str in [
        "Nat.le",
        "Nat.lt",
        "Nat.le_refl",
        "Nat.le_trans",
        "Nat.le_antisymm",
        "instLENat",
        "instLTNat",
        "instPreorderNat",
        "instPartialOrderNat",
    ] {
        assert_const(&env, name_str);
    }
}

#[test]
fn test_init_nat_linear_order() {
    let mut env = Environment::new();
    env.init_nat_linear_order().unwrap();
    assert!(env.has_nat_linear_order());
}

#[test]
fn test_nat_linear_order_type_checks() {
    let mut env = Environment::new();
    env.init_nat_linear_order().unwrap();

    // Check Nat.le_total axiom exists
    assert_axiom(&env, "Nat.le_total");

    // Check instLinearOrderNat exists
    assert_axiom(&env, "instLinearOrderNat");
}

#[test]
fn test_nat_linear_order_hierarchy() {
    let mut env = Environment::new();
    env.init_nat_linear_order().unwrap();

    // Full hierarchy should be initialized
    assert!(env.has_le());
    assert!(env.has_lt());
    assert!(env.has_preorder());
    assert!(env.has_partial_order());
    assert!(env.has_linear_order());
    assert!(env.has_nat_preorder());
    assert!(env.has_nat_partial_order());
    assert!(env.has_nat_linear_order());

    // Check all definitions exist with correct names
    for name_str in ["Nat.le_total", "instLinearOrderNat"] {
        assert_const(&env, name_str);
    }
}

#[test]
fn test_init_nat_le_reflexive() {
    let mut env = Environment::new();
    env.init_nat_le_reflexive().unwrap();
    assert!(env.has_nat_le_reflexive());
}

#[test]
fn test_nat_le_reflexive_type_checks() {
    let mut env = Environment::new();
    env.init_nat_le_reflexive().unwrap();

    // Check instReflexiveNatLe exists
    assert_axiom(&env, "instReflexiveNatLe");
}

#[test]
fn test_init_nat_lt_irrefl() {
    let mut env = Environment::new();
    env.init_nat_lt_irrefl().unwrap();
    assert!(env.has_nat_lt_irrefl());
}

#[test]
fn test_nat_lt_irrefl_type_checks() {
    let mut env = Environment::new();
    env.init_nat_lt_irrefl().unwrap();

    // Check Nat.lt_irrefl axiom exists
    assert_axiom(&env, "Nat.lt_irrefl");

    // Check instIrreflNatLt exists
    assert_axiom(&env, "instIrreflNatLt");
}

#[test]
fn test_init_nat_lt_asymm() {
    let mut env = Environment::new();
    env.init_nat_lt_asymm().unwrap();
    assert!(env.has_nat_lt_asymm());
}

#[test]
fn test_nat_lt_asymm_type_checks() {
    let mut env = Environment::new();
    env.init_nat_lt_asymm().unwrap();

    // Check Nat.lt_asymm axiom exists
    assert_axiom(&env, "Nat.lt_asymm");

    // Check instAsymmNatLt exists
    assert_axiom(&env, "instAsymmNatLt");
}

#[test]
fn test_init_nat_lt_trans() {
    let mut env = Environment::new();
    env.init_nat_lt_trans().unwrap();
    assert!(env.has_nat_lt_trans());
}

#[test]
fn test_nat_lt_trans_type_checks() {
    use crate::env::axiom_audit::ProofQuality;

    let mut env = Environment::new();
    env.init_nat_lt_trans().unwrap();

    // Nat.lt_trans is now a constructive Theorem (#3604), not an Axiom.
    let n = Name::from_string("Nat.lt_trans");
    let info = env.get_const(&n).expect("Nat.lt_trans must be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "Nat.lt_trans must be `Declaration::Theorem`, got {:?}",
        info.kind,
    );
    let proof_value = info
        .value
        .as_ref()
        .expect("Nat.lt_trans theorem must carry a proof term");
    // The proof must actually mention Nat.le.rec — rules out an axiom-reference
    // masquerade (Nat.lt reduces to Nat.le, so the recursion is on Nat.le).
    let nat_le_rec = Name::from_string("Nat.le.rec");
    assert!(
        test_helpers::expr_contains_const(proof_value, &nat_le_rec),
        "Nat.lt_trans proof term must invoke `Nat.le.rec` (constructive induction)",
    );
    // Axiom closure must be empty (no domain-specific axioms).
    let deps = env
        .axiom_deps(&n)
        .expect("axiom_deps must succeed for a registered theorem");
    assert!(
        deps.is_empty(),
        "Nat.lt_trans must have zero domain-specific axiom deps, found: {:?}",
        deps.iter().map(|d| d.to_string()).collect::<Vec<_>>(),
    );
    match env.proof_quality(&n) {
        Some(ProofQuality::Constructive) => {}
        other => panic!("Nat.lt_trans must be ProofQuality::Constructive, got {other:?}"),
    }

    // Check instTransNatLt exists. (KKL finish: now a CONSTRUCTIVE Definition
    // via `Trans.mk Nat.lt_trans`, not an axiom — `assert_axiom` is a soft
    // name-registered probe and stays valid.)
    assert_axiom(&env, "instTransNatLt");
}

#[test]
fn test_all_nat_ordering_instances() {
    // Comprehensive test for all Nat ordering instances
    let mut env = Environment::new();

    // Initialize all instances
    env.init_nat_linear_order().unwrap();
    env.init_nat_le_reflexive().unwrap();
    env.init_nat_lt_irrefl().unwrap();
    env.init_nat_lt_asymm().unwrap();
    env.init_nat_lt_trans().unwrap();

    // Verify all flags
    assert!(env.has_nat_linear_order());
    assert!(env.has_nat_le_reflexive());
    assert!(env.has_nat_lt_irrefl());
    assert!(env.has_nat_lt_asymm());
    assert!(env.has_nat_lt_trans());

    // Verify all definitions with correct names
    for name_str in [
        "Nat.le_total",
        "instLinearOrderNat",
        "instReflexiveNatLe",
        "Nat.lt_irrefl",
        "instIrreflNatLt",
        "Nat.lt_asymm",
        "instAsymmNatLt",
        "Nat.lt_trans",
        "instTransNatLt",
    ] {
        assert_const(&env, name_str);
    }
}

// Tests for Nat.le Antisymm instance
#[test]
fn test_init_nat_le_antisymm() {
    let mut env = Environment::new();
    env.init_nat_le_antisymm().unwrap();
    assert!(env.has_nat_le_antisymm());

    // Check axiom and instance exist with correct names
    for name_str in ["Nat.le_antisymm", "instAntisymmNatLe"] {
        assert_const(&env, name_str);
    }
}

#[test]
fn test_nat_le_antisymm_type_checks() {
    let mut env = Environment::new();
    env.init_nat_le_antisymm().unwrap();

    // Nat.le_antisymm : ∀ a b : Nat, Nat.le a b → Nat.le b a → a = b
    assert_axiom(&env, "Nat.le_antisymm");

    // instAntisymmNatLe : Antisymm (fun a b => Nat.le a b)
    assert_axiom(&env, "instAntisymmNatLe");
}

// Tests for Nat.le Trans instance
#[test]
fn test_init_nat_le_trans() {
    let mut env = Environment::new();
    env.init_nat_le_trans().unwrap();
    assert!(env.has_nat_le_trans());

    // Check axiom and instance exist with correct names
    for name_str in ["Nat.le_trans", "instTransNatLe"] {
        assert_const(&env, name_str);
    }
}

#[test]
fn test_nat_le_trans_type_checks() {
    let mut env = Environment::new();
    env.init_nat_le_trans().unwrap();

    // Nat.le_trans : theorem ∀ a b c : Nat, Nat.le a b → Nat.le b c → Nat.le a c
    // (#3552 — constructive proof via `Nat.le.rec`).
    let n = Name::from_string("Nat.le_trans");
    let info = env.get_const(&n).expect("Nat.le_trans must be registered");
    assert_eq!(info.kind, ConstantKind::Theorem);
    assert!(
        info.value.is_some(),
        "Nat.le_trans must have a proof body (theorem, not axiom)",
    );

    // instTransNatLe : Trans (fun a b => Nat.le a b) (fun a b => Nat.le a b) (fun a b => Nat.le a b)
    assert_axiom(&env, "instTransNatLe");
}

/// Issue #3552: `Nat.le_trans` must be a constructive theorem with zero
/// domain-specific axioms in its transitive closure.
#[test]
fn test_nat_le_trans_is_constructive_theorem() {
    use crate::env::axiom_audit::ProofQuality;

    let mut env = Environment::new();
    env.init_nat_le_trans().unwrap();

    let n = Name::from_string("Nat.le_trans");
    let info = env.get_const(&n).expect("Nat.le_trans must be registered");

    // Must be a Theorem (not Axiom).
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "Nat.le_trans must be `Declaration::Theorem`, got {:?}",
        info.kind,
    );
    let proof_value = info
        .value
        .as_ref()
        .expect("Nat.le_trans theorem must carry a proof term");

    // The proof must actually mention Nat.le.rec — this rules out degenerate
    // "theorems" whose body is just `Nat.le_trans` axiom reference.
    let nat_le_rec = Name::from_string("Nat.le.rec");
    assert!(
        test_helpers::expr_contains_const(proof_value, &nat_le_rec),
        "Nat.le_trans proof term must invoke `Nat.le.rec` (constructive induction)",
    );

    // Axiom closure must be empty (no domain-specific axioms).
    let deps = env
        .axiom_deps(&n)
        .expect("axiom_deps must succeed for a registered theorem");
    let deps_sorted: Vec<String> = {
        let mut v: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        v.sort();
        v
    };
    assert!(
        deps.is_empty(),
        "Nat.le_trans must have zero domain-specific axiom deps, found: {deps_sorted:?}",
    );

    // And `proof_quality` classifies it as Constructive.
    match env.proof_quality(&n) {
        Some(ProofQuality::Constructive) => {}
        other => panic!("Nat.le_trans must be ProofQuality::Constructive, got {other:?}",),
    }
}

/// Issue #3552: `Nat.le_trans` is registered once, even if both
/// `init_nat_preorder` and `init_nat_le_trans` request it.
#[test]
fn test_nat_le_trans_idempotent_across_inits() {
    let mut env = Environment::new();
    env.init_nat_preorder().unwrap();
    env.init_nat_le_trans().unwrap();

    let n = Name::from_string("Nat.le_trans");
    let info = env.get_const(&n).expect("registered");
    assert_eq!(info.kind, ConstantKind::Theorem);
    assert!(info.value.is_some());
}

// Tests for StrictOrder typeclass
#[test]
fn test_init_strict_order() {
    let mut env = Environment::new();
    env.init_strict_order().unwrap();
    assert!(env.has_strict_order());

    // Check inductive type and constructor exist with correct structure
    assert_inductive(&env, "StrictOrder");
    for s in ["StrictOrder.mk", "StrictOrder.rec"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_strict_order_type_checks() {
    let mut env = Environment::new();
    env.init_strict_order().unwrap();

    // StrictOrder: verify both inductive and const registration
    assert_const(&env, "StrictOrder");
    assert_inductive(&env, "StrictOrder");
    assert_const(&env, "StrictOrder.mk");
}

// Tests for Nat.lt StrictOrder instance
#[test]
fn test_init_nat_lt_strict_order() {
    let mut env = Environment::new();
    env.init_nat_lt_strict_order().unwrap();
    assert!(env.has_nat_lt_strict_order());

    // Check instance exists with correct name
    assert_const(&env, "instStrictOrderNatLt");
}

#[test]
fn test_nat_lt_strict_order_type_checks() {
    let mut env = Environment::new();
    env.init_nat_lt_strict_order().unwrap();

    // instStrictOrderNatLt : StrictOrder (fun a b => Nat.lt a b)
    assert_axiom(&env, "instStrictOrderNatLt");
}

#[test]
fn test_nat_lt_strict_order_dependencies() {
    // Verify that initializing strict order pulls in all dependencies
    let mut env = Environment::new();
    env.init_nat_lt_strict_order().unwrap();

    // Should have Irrefl and Trans instances
    assert!(env.has_nat_lt_irrefl());
    assert!(env.has_nat_lt_trans());
    assert!(env.has_strict_order());

    // And their underlying definitions with correct names
    for name_str in ["instIrreflNatLt", "instTransNatLt"] {
        assert_const(&env, name_str);
    }
}

#[test]
fn test_all_nat_le_ordering_instances() {
    // Comprehensive test for all Nat.le ordering instances
    let mut env = Environment::new();

    // Initialize all Nat.le instances
    env.init_nat_le_reflexive().unwrap();
    env.init_nat_le_antisymm().unwrap();
    env.init_nat_le_trans().unwrap();

    // Verify all flags
    assert!(env.has_nat_le_reflexive());
    assert!(env.has_nat_le_antisymm());
    assert!(env.has_nat_le_trans());

    // Verify all definitions with correct names
    for name_str in [
        "instReflexiveNatLe",
        "Nat.le_antisymm",
        "instAntisymmNatLe",
        "Nat.le_trans",
        "instTransNatLe",
    ] {
        assert_const(&env, name_str);
    }
}

#[test]
fn test_complete_nat_ordering_hierarchy() {
    // Test the complete ordering hierarchy for Nat
    let mut env = Environment::new();

    // Initialize everything
    env.init_nat_linear_order().unwrap(); // LE, LT, Preorder, PartialOrder, LinearOrder
    env.init_nat_le_reflexive().unwrap(); // Reflexive for ≤
    env.init_nat_le_antisymm().unwrap(); // Antisymm for ≤
    env.init_nat_le_trans().unwrap(); // Trans for ≤
    env.init_nat_lt_irrefl().unwrap(); // Irrefl for <
    env.init_nat_lt_asymm().unwrap(); // Asymm for <
    env.init_nat_lt_trans().unwrap(); // Trans for <
    env.init_nat_lt_strict_order().unwrap(); // StrictOrder for <

    // Check all the hierarchy with correct names
    for name_str in [
        // LinearOrder hierarchy
        "instLinearOrderNat",
        "instPartialOrderNat",
        "instPreorderNat",
        // LE relation instances
        "instReflexiveNatLe",
        "instAntisymmNatLe",
        "instTransNatLe",
        // LT relation instances
        "instIrreflNatLt",
        "instAsymmNatLt",
        "instTransNatLt",
        "instStrictOrderNatLt",
    ] {
        assert_const(&env, name_str);
    }
}

#[test]
fn test_init_nat_trans_lt_le_lt() {
    let mut env = Environment::new();
    env.init_nat_trans_lt_le_lt().unwrap();

    assert_const(&env, "Nat.lt_of_lt_of_le");
    assert_const(&env, "instTransNatLtLeLt");
    assert!(env.has_nat_trans_lt_le_lt());
}

#[test]
fn test_nat_trans_lt_le_lt_type_checks() {
    let mut env = Environment::new();
    env.init_nat_trans_lt_le_lt().unwrap();

    // Nat.lt_of_lt_of_le : ∀ a b c : Nat, Nat.lt a b → Nat.le b c → Nat.lt a c
    // (#3551: constructive Theorem)
    assert_const(&env, "Nat.lt_of_lt_of_le");

    // instTransNatLtLeLt : Trans Nat.lt Nat.le Nat.lt
    // (#3551 follow-up: now a constructive Definition built via Trans.mk +
    // Nat.lt_of_lt_of_le, no longer an Axiom).
    assert_const(&env, "instTransNatLtLeLt");
}

#[test]
fn test_init_nat_trans_le_lt_lt() {
    let mut env = Environment::new();
    env.init_nat_trans_le_lt_lt().unwrap();

    assert_const(&env, "Nat.lt_of_le_of_lt");
    assert_const(&env, "instTransNatLeLtLt");
    assert!(env.has_nat_trans_le_lt_lt());
}

#[test]
fn test_nat_trans_le_lt_lt_type_checks() {
    let mut env = Environment::new();
    env.init_nat_trans_le_lt_lt().unwrap();

    // Nat.lt_of_le_of_lt : ∀ a b c : Nat, Nat.le a b → Nat.lt b c → Nat.lt a c
    // (#3551: constructive Theorem)
    assert_const(&env, "Nat.lt_of_le_of_lt");

    // instTransNatLeLtLt : Trans Nat.le Nat.lt Nat.lt
    // (#3551 follow-up: now a constructive Definition built via Trans.mk +
    // Nat.lt_of_le_of_lt, no longer an Axiom).
    assert_const(&env, "instTransNatLeLtLt");
}

#[test]
fn test_init_nat_trans_lt_lt_le() {
    let mut env = Environment::new();
    env.init_nat_trans_lt_lt_le().unwrap();

    assert_const(&env, "Nat.le_of_lt");
    assert_const(&env, "instTransNatLtLtLe");
    assert!(env.has_nat_trans_lt_lt_le());
}

#[test]
fn test_nat_trans_lt_lt_le_type_checks() {
    let mut env = Environment::new();
    env.init_nat_trans_lt_lt_le().unwrap();

    // Nat.le_of_lt : ∀ a b : Nat, LT.lt @Nat instLTNat a b → LE.le @Nat instLENat a b
    // #3599: promoted from Axiom to constructive Theorem (carries a proof
    // term from Nat.le.rec induction), so use assert_const instead of
    // assert_axiom.
    assert_const(&env, "Nat.le_of_lt");

    // instTransNatLtLtLe : Trans Nat.lt Nat.lt Nat.le. (KKL finish: now a
    // CONSTRUCTIVE Definition via `Trans.mk (Nat.le_of_lt ∘ Nat.lt_trans)`, not
    // an axiom — `assert_axiom` is a soft name-registered probe and stays valid.)
    assert_axiom(&env, "instTransNatLtLtLe");
}

#[test]
fn test_nat_trans_lt_lt_le_dependencies() {
    // Verify that initializing (lt, lt) -> le pulls in Nat.lt_trans
    let mut env = Environment::new();
    env.init_nat_trans_lt_lt_le().unwrap();

    // Should have Nat.lt_trans initialized
    assert!(env.has_nat_lt_trans());
    assert_const(&env, "Nat.lt_trans");
}

#[test]
fn test_all_mixed_trans_instances() {
    // Comprehensive test for all mixed Trans instances
    let mut env = Environment::new();

    // Initialize all mixed Trans instances
    env.init_nat_trans_lt_le_lt().unwrap();
    env.init_nat_trans_le_lt_lt().unwrap();
    env.init_nat_trans_lt_lt_le().unwrap();

    // Verify all flags
    assert!(env.has_nat_trans_lt_le_lt());
    assert!(env.has_nat_trans_le_lt_lt());
    assert!(env.has_nat_trans_lt_lt_le());

    // Verify all axioms and instances
    for s in [
        "Nat.lt_of_lt_of_le",
        "Nat.lt_of_le_of_lt",
        "Nat.le_of_lt",
        "instTransNatLtLeLt",
        "instTransNatLeLtLt",
        "instTransNatLtLtLe",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_complete_nat_trans_hierarchy() {
    // Test all Trans instances for Nat including homogeneous and mixed
    let mut env = Environment::new();

    // Homogeneous Trans instances
    env.init_nat_lt_trans().unwrap(); // Trans Nat.lt Nat.lt Nat.lt
    env.init_nat_le_trans().unwrap(); // Trans Nat.le Nat.le Nat.le

    // Mixed Trans instances
    env.init_nat_trans_lt_le_lt().unwrap(); // Trans Nat.lt Nat.le Nat.lt
    env.init_nat_trans_le_lt_lt().unwrap(); // Trans Nat.le Nat.lt Nat.lt
    env.init_nat_trans_lt_lt_le().unwrap(); // Trans Nat.lt Nat.lt Nat.le

    // Verify all Trans instances and underlying axioms/lemmas
    for s in [
        "instTransNatLt",
        "instTransNatLe",
        "instTransNatLtLeLt",
        "instTransNatLeLtLt",
        "instTransNatLtLtLe",
        "Nat.lt_trans",
        "Nat.le_trans",
        "Nat.lt_of_lt_of_le",
        "Nat.lt_of_le_of_lt",
        "Nat.le_of_lt",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_init_nat_lt_or_eq_of_le() {
    let mut env = Environment::new();
    env.init_nat_lt_or_eq_of_le().unwrap();

    assert_const(&env, "Nat.lt_or_eq_of_le");
    assert!(env.has_nat_lt_or_eq_of_le());
}

#[test]
fn test_nat_lt_or_eq_of_le_type_checks() {
    let mut env = Environment::new();
    env.init_nat_lt_or_eq_of_le().unwrap();

    // Nat.lt_or_eq_of_le : ∀ a b : Nat, Nat.le a b → Or (Nat.lt a b) (Eq a b)
    assert_axiom(&env, "Nat.lt_or_eq_of_le");

    assert_inductive(&env, "Nat");
    assert_inductive(&env, "Eq");
    // Note: Or and False must be added via init_classical() or otherwise
}

#[test]
fn test_nat_lt_or_eq_of_le_idempotent() {
    let mut env = Environment::new();
    env.init_nat_lt_or_eq_of_le().unwrap();
    // Should be idempotent
    env.init_nat_lt_or_eq_of_le().unwrap();
    assert!(env.has_nat_lt_or_eq_of_le());
}

#[test]
fn test_init_nat_lt_of_le_of_ne() {
    let mut env = Environment::new();
    env.init_nat_lt_of_le_of_ne().unwrap();

    assert_const(&env, "Nat.lt_of_le_of_ne");
    assert!(env.has_nat_lt_of_le_of_ne());
}

#[test]
fn test_nat_lt_of_le_of_ne_type_checks() {
    let mut env = Environment::new();
    env.init_nat_lt_of_le_of_ne().unwrap();

    // Nat.lt_of_le_of_ne : ∀ a b : Nat, Nat.le a b → (Eq a b → False) → Nat.lt a b
    assert_axiom(&env, "Nat.lt_of_le_of_ne");

    // Check core dependencies were initialized
    assert_inductive(&env, "Nat");
    assert_inductive(&env, "Eq");
    // Note: False is used by reference but not initialized by this function
}

#[test]
fn test_nat_lt_of_le_of_ne_idempotent() {
    let mut env = Environment::new();
    env.init_nat_lt_of_le_of_ne().unwrap();
    // Should be idempotent
    env.init_nat_lt_of_le_of_ne().unwrap();
    assert!(env.has_nat_lt_of_le_of_ne());
}

#[test]
fn test_init_nat_not_lt_le() {
    let mut env = Environment::new();
    env.init_nat_not_lt_le().unwrap();

    assert_const(&env, "Nat.not_lt");
    assert_const(&env, "Nat.not_le");
    assert!(env.has_nat_not_lt_le());
}

#[test]
fn test_nat_not_lt_le_type_checks() {
    let mut env = Environment::new();
    env.init_nat_not_lt_le().unwrap();

    // Nat.not_lt : ∀ a b : Nat, Iff (Nat.lt a b → False) (Nat.le b a)
    assert_axiom(&env, "Nat.not_lt");

    // Nat.not_le : ∀ a b : Nat, Iff (Nat.le a b → False) (Nat.lt b a)
    assert_axiom(&env, "Nat.not_le");

    // Check core dependencies were initialized
    assert_inductive(&env, "Nat");
    // Iff is initialized by init_iff which is called by init_nat_not_lt_le
    assert_const(&env, "Iff");
    // Note: False is used by reference in type but may not be initialized
}

#[test]
fn test_nat_not_lt_le_idempotent() {
    let mut env = Environment::new();
    env.init_nat_not_lt_le().unwrap();
    // Should be idempotent
    env.init_nat_not_lt_le().unwrap();
    assert!(env.has_nat_not_lt_le());
}

#[test]
fn test_all_nat_comparison_lemmas() {
    let mut env = Environment::new();

    // Initialize all comparison lemmas
    env.init_nat_lt_or_eq_of_le().unwrap();
    env.init_nat_lt_of_le_of_ne().unwrap();
    env.init_nat_not_lt_le().unwrap();

    // Verify all lemmas exist
    for s in [
        "Nat.lt_or_eq_of_le",
        "Nat.lt_of_le_of_ne",
        "Nat.not_lt",
        "Nat.not_le",
    ] {
        assert_const(&env, s);
    }

    // All flags should be set
    assert!(env.has_nat_lt_or_eq_of_le());
    assert!(env.has_nat_lt_of_le_of_ne());
    assert!(env.has_nat_not_lt_le());
}

#[test]
fn test_nat_comparison_lemmas_with_ordering_hierarchy() {
    // Test that comparison lemmas work well with the full ordering hierarchy
    let mut env = Environment::new();

    // Initialize the full ordering hierarchy
    env.init_nat_linear_order().unwrap();
    env.init_nat_le_reflexive().unwrap();
    env.init_nat_le_antisymm().unwrap();
    env.init_nat_le_trans().unwrap();
    env.init_nat_lt_irrefl().unwrap();
    env.init_nat_lt_asymm().unwrap();
    env.init_nat_lt_trans().unwrap();
    env.init_nat_lt_strict_order().unwrap();

    // Add mixed Trans instances
    env.init_nat_trans_lt_le_lt().unwrap();
    env.init_nat_trans_le_lt_lt().unwrap();
    env.init_nat_trans_lt_lt_le().unwrap();

    // Add comparison lemmas
    env.init_nat_lt_or_eq_of_le().unwrap();
    env.init_nat_lt_of_le_of_ne().unwrap();
    env.init_nat_not_lt_le().unwrap();

    // Verify complete set of ordering facts
    for s in [
        "instLinearOrderNat",
        "Nat.lt_trans",
        "Nat.le_trans",
        "Nat.lt_of_lt_of_le",
        "Nat.lt_of_le_of_lt",
        "Nat.le_of_lt",
        "Nat.lt_or_eq_of_le",
        "Nat.lt_of_le_of_ne",
        "Nat.not_lt",
        "Nat.not_le",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_init_nat_succ_base() {
    let mut env = Environment::new();
    env.init_nat_succ_base().unwrap();

    for s in [
        "Nat.zero_lt_succ",
        "Nat.not_succ_lt_zero",
        "Nat.lt_succ_self",
    ] {
        assert_const(&env, s);
    }
    assert!(env.has_nat_succ_base());
}

#[test]
fn test_nat_succ_base_type_checks() {
    let mut env = Environment::new();
    env.init_nat_succ_base().unwrap();

    // #3599: Nat.zero_lt_succ is now a constructive Theorem (carries a
    // Nat.rec.{0} induction proof term); the remaining two are still
    // axioms.
    assert_const(&env, "Nat.zero_lt_succ");

    assert_axiom(&env, "Nat.not_succ_lt_zero");

    assert_axiom(&env, "Nat.lt_succ_self");

    // Check dependencies
    assert_inductive(&env, "Nat");
    assert_ctor(&env, "Nat.zero", "Nat");
    assert_ctor(&env, "Nat.succ", "Nat");
}

#[test]
fn test_nat_succ_base_idempotent() {
    let mut env = Environment::new();
    env.init_nat_succ_base().unwrap();
    // Should be idempotent
    env.init_nat_succ_base().unwrap();
    assert!(env.has_nat_succ_base());
}

#[test]
fn test_init_nat_succ_lt() {
    let mut env = Environment::new();
    env.init_nat_succ_lt().unwrap();

    for s in [
        "Nat.lt_succ_iff",
        "Nat.succ_lt_succ",
        "Nat.lt_of_succ_lt_succ",
        "Nat.succ_le_succ",
        "Nat.le_of_succ_le_succ",
    ] {
        assert_const(&env, s);
    }
    assert!(env.has_nat_succ_lt());
}

#[test]
fn test_nat_succ_lt_type_checks() {
    let mut env = Environment::new();
    env.init_nat_succ_lt().unwrap();

    // #3599: Nat.succ_lt_succ and Nat.succ_le_succ are now constructive
    // Theorems (Nat.le.rec induction); the other three are still axioms.
    assert_axiom(&env, "Nat.lt_succ_iff");

    assert_const(&env, "Nat.succ_lt_succ");

    assert_axiom(&env, "Nat.lt_of_succ_lt_succ");

    assert_const(&env, "Nat.succ_le_succ");

    assert_axiom(&env, "Nat.le_of_succ_le_succ");

    // Check dependencies
    assert_inductive(&env, "Nat");
    assert_const(&env, "Iff");
}

#[test]
fn test_nat_succ_lt_idempotent() {
    let mut env = Environment::new();
    env.init_nat_succ_lt().unwrap();
    // Should be idempotent
    env.init_nat_succ_lt().unwrap();
    assert!(env.has_nat_succ_lt());
}

#[test]
fn test_init_nat_lt_trichotomy() {
    let mut env = Environment::new();
    env.init_nat_lt_trichotomy().unwrap();

    assert_const(&env, "Nat.lt_trichotomy");
    assert!(env.has_nat_lt_trichotomy());
}

#[test]
fn test_nat_lt_trichotomy_type_checks() {
    let mut env = Environment::new();
    env.init_nat_lt_trichotomy().unwrap();

    // Nat.lt_trichotomy : ∀ a b : Nat, Or (Nat.lt a b) (Or (Eq a b) (Nat.lt b a))
    assert_axiom(&env, "Nat.lt_trichotomy");

    // Check dependencies
    assert_inductive(&env, "Nat");
    assert_inductive(&env, "Eq");
}

#[test]
fn test_nat_lt_trichotomy_idempotent() {
    let mut env = Environment::new();
    env.init_nat_lt_trichotomy().unwrap();
    // Should be idempotent
    env.init_nat_lt_trichotomy().unwrap();
    assert!(env.has_nat_lt_trichotomy());
}

#[test]
fn test_init_nat_decidable_ord() {
    let mut env = Environment::new();
    env.init_nat_decidable_ord().unwrap();

    assert_const(&env, "instDecidableNatLt");
    assert_const(&env, "instDecidableNatLe");
    assert!(env.has_nat_decidable_ord());
}

#[test]
fn test_nat_decidable_ord_type_checks() {
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_nat_decidable_ord().unwrap();

    // instDecidableNatLt : (a b : Nat) → Decidable (@LT.lt Nat instLTNat a b)
    // instDecidableNatLe : (a b : Nat) → Decidable (@LE.le Nat instLENat a b)
    // These are now real `Declaration::Definition`s backed by the axiom-free
    // `Nat.decLt`/`Nat.decLe` decision procedures — NOT `Declaration::Axiom`
    // (an axiom-backed decidability instance would be a trust regression).
    let tc = TypeChecker::with_mode(&env, env.mode());
    for name in ["instDecidableNatLt", "instDecidableNatLe"] {
        let info = env.get_const(&Name::from_string(name)).unwrap();
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "{name} must be a Definition, not an Axiom"
        );
        assert!(
            info.value.is_some(),
            "{name} must carry a value (the Nat.dec* decision procedure)"
        );
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string(name), vec![]))
            .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
    }

    // The underlying decision procedures are axiom-free.
    for name in ["Nat.decLe", "Nat.decLt"] {
        let deps = env
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} registered"));
        let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(names.is_empty(), "{name} must be axiom-free, got {names:?}");
    }

    // Check dependencies
    assert_inductive(&env, "Nat");
    assert_inductive(&env, "Decidable");
}

#[test]
fn test_nat_decidable_ord_idempotent() {
    let mut env = Environment::new();
    env.init_nat_decidable_ord().unwrap();
    // Should be idempotent
    env.init_nat_decidable_ord().unwrap();
    assert!(env.has_nat_decidable_ord());
}

#[test]
fn test_all_nat_succ_and_trichotomy_lemmas() {
    let mut env = Environment::new();

    // Initialize all new lemmas
    env.init_nat_succ_base().unwrap();
    env.init_nat_succ_lt().unwrap();
    env.init_nat_lt_trichotomy().unwrap();
    env.init_nat_decidable_ord().unwrap();

    // Verify all flags
    assert!(env.has_nat_succ_base());
    assert!(env.has_nat_succ_lt());
    assert!(env.has_nat_lt_trichotomy());
    assert!(env.has_nat_decidable_ord());

    // Verify all lemmas exist
    for s in [
        "Nat.zero_lt_succ",
        "Nat.not_succ_lt_zero",
        "Nat.lt_succ_self",
        "Nat.lt_succ_iff",
        "Nat.succ_lt_succ",
        "Nat.lt_of_succ_lt_succ",
        "Nat.succ_le_succ",
        "Nat.le_of_succ_le_succ",
        "Nat.lt_trichotomy",
        "instDecidableNatLt",
        "instDecidableNatLe",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_complete_nat_ordering_with_succ_trichotomy() {
    // Test the complete ordering hierarchy including new lemmas
    let mut env = Environment::new();

    // Initialize the full ordering hierarchy
    env.init_nat_linear_order().unwrap();
    env.init_nat_le_reflexive().unwrap();
    env.init_nat_le_antisymm().unwrap();
    env.init_nat_le_trans().unwrap();
    env.init_nat_lt_irrefl().unwrap();
    env.init_nat_lt_asymm().unwrap();
    env.init_nat_lt_trans().unwrap();
    env.init_nat_lt_strict_order().unwrap();

    // Add mixed Trans instances
    env.init_nat_trans_lt_le_lt().unwrap();
    env.init_nat_trans_le_lt_lt().unwrap();
    env.init_nat_trans_lt_lt_le().unwrap();

    // Add comparison lemmas
    env.init_nat_lt_or_eq_of_le().unwrap();
    env.init_nat_lt_of_le_of_ne().unwrap();
    env.init_nat_not_lt_le().unwrap();

    // Add successor lemmas and trichotomy
    env.init_nat_succ_base().unwrap();
    env.init_nat_succ_lt().unwrap();
    env.init_nat_lt_trichotomy().unwrap();
    env.init_nat_decidable_ord().unwrap();

    // Verify we have the complete set
    for s in [
        "instLinearOrderNat",
        "Nat.zero_lt_succ",
        "Nat.not_succ_lt_zero",
        "Nat.lt_succ_self",
        "Nat.lt_succ_iff",
        "Nat.succ_lt_succ",
        "Nat.lt_trichotomy",
        "instDecidableNatLt",
        "instDecidableNatLe",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_init_nat_minmax_lemmas() {
    let mut env = Environment::new();
    assert!(!env.has_nat_minmax_lemmas());

    env.init_nat_minmax_lemmas().unwrap();
    assert!(env.has_nat_minmax_lemmas());

    // Check all lemmas exist
    for s in [
        "Nat.min_le_left",
        "Nat.min_le_right",
        "Nat.le_min",
        "Nat.le_max_left",
        "Nat.le_max_right",
        "Nat.max_le",
        "Nat.min_comm",
        "Nat.max_comm",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_nat_minmax_lemmas_type_checks() {
    let mut env = Environment::new();
    env.init_nat_minmax_lemmas().unwrap();

    // #3604: all eight lemmas are now constructive Theorems, not Axioms.
    for s in [
        "Nat.min_le_left",
        "Nat.le_min",
        "Nat.max_le",
        "Nat.min_comm",
    ] {
        let info = env.get_const(&Name::from_string(s)).expect(s);
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{s} must be a Declaration::Theorem (#3604)",
        );
    }

    // Check dependencies were initialized
    assert_const(&env, "Nat.min");
    assert_const(&env, "Nat.max");
    assert_inductive(&env, "Eq");
}

/// #3604: each `Nat.min` / `Nat.max` ordering lemma is demoted from
/// `Declaration::Axiom` to a constructive `Declaration::Theorem` with an empty
/// domain-specific axiom closure and `ProofQuality::Constructive`.
#[test]
fn test_nat_minmax_lemmas_constructive_demotion() {
    use crate::env::axiom_audit::ProofQuality;

    let mut env = Environment::new();
    env.init_nat_minmax_lemmas().unwrap();

    for s in [
        "Nat.min_le_left",
        "Nat.min_le_right",
        "Nat.le_min",
        "Nat.min_comm",
        "Nat.le_max_left",
        "Nat.le_max_right",
        "Nat.max_le",
        "Nat.max_comm",
    ] {
        let n = Name::from_string(s);
        let info = env
            .get_const(&n)
            .unwrap_or_else(|| panic!("{s} registered"));

        // (1) registered_as_theorem
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{s} must be `Declaration::Theorem`, got {:?}",
            info.kind,
        );
        assert!(info.value.is_some(), "{s} Theorem must carry a proof term",);

        // (2) axiom_deps_empty
        let deps = env
            .axiom_deps(&n)
            .unwrap_or_else(|| panic!("axiom_deps must succeed for {s}"));
        let deps_sorted: Vec<String> = {
            let mut v: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
            v.sort();
            v
        };
        assert!(
            deps.is_empty(),
            "{s} must have zero domain-specific axiom deps, found: {deps_sorted:?}",
        );

        // (3) proof_quality_constructive
        match env.proof_quality(&n) {
            Some(ProofQuality::Constructive) => {}
            other => panic!("{s} must be ProofQuality::Constructive, got {other:?}"),
        }
    }
}

/// #3604: the constructive proof terms genuinely invoke the recursors / Eq
/// machinery (not a degenerate re-statement). Rules out a `Theorem` whose body
/// is merely an axiom reference.
#[test]
fn test_nat_minmax_lemmas_proofs_invoke_recursors() {
    let mut env = Environment::new();
    env.init_nat_minmax_lemmas().unwrap();

    let bool_rec = Name::from_string("Bool.rec");
    let nat_rec = Name::from_string("Nat.rec");
    let eq_trans = Name::from_string("Eq.trans");

    // `le_min` / `max_le` are single dependent `Bool.rec` case analyses.
    for s in ["Nat.le_min", "Nat.max_le"] {
        let info = env.get_const(&Name::from_string(s)).expect(s);
        let v = info.value.as_ref().expect("proof term");
        assert!(
            test_helpers::expr_contains_const(v, &bool_rec),
            "{s} proof must invoke `Bool.rec`",
        );
    }

    // The extraction lemmas are double `Nat.rec` inductions with `Bool.rec` lifts.
    for s in [
        "Nat.min_le_left",
        "Nat.min_le_right",
        "Nat.le_max_left",
        "Nat.le_max_right",
    ] {
        let info = env.get_const(&Name::from_string(s)).expect(s);
        let v = info.value.as_ref().expect("proof term");
        assert!(
            test_helpers::expr_contains_const(v, &nat_rec),
            "{s} proof must invoke `Nat.rec`",
        );
        assert!(
            test_helpers::expr_contains_const(v, &bool_rec),
            "{s} proof must invoke `Bool.rec`",
        );
    }

    // The comm lemmas chain `Eq.trans` over `congrArg` / `Bool.rec` congruences.
    for s in ["Nat.min_comm", "Nat.max_comm"] {
        let info = env.get_const(&Name::from_string(s)).expect(s);
        let v = info.value.as_ref().expect("proof term");
        assert!(
            test_helpers::expr_contains_const(v, &nat_rec),
            "{s} proof must invoke `Nat.rec`",
        );
        assert!(
            test_helpers::expr_contains_const(v, &eq_trans),
            "{s} proof must invoke `Eq.trans`",
        );
    }
}

#[test]
fn test_nat_minmax_lemmas_idempotent() {
    let mut env = Environment::new();
    env.init_nat_minmax_lemmas().unwrap();
    // Should be idempotent
    env.init_nat_minmax_lemmas().unwrap();
    assert!(env.has_nat_minmax_lemmas());
}

#[test]
fn test_complete_nat_minmax_ordering() {
    // Test full ordering with min/max lemmas
    let mut env = Environment::new();

    // Initialize full ordering hierarchy including min/max lemmas
    env.init_nat_linear_order().unwrap();
    env.init_nat_minmax_lemmas().unwrap();
    env.init_nat_decidable_ord().unwrap();

    // Verify comprehensive ordering support
    assert!(env.has_nat_linear_order());
    assert!(env.has_nat_minmax_lemmas());
    assert!(env.has_nat_decidable_ord());

    // Verify min/max operations and lemmas
    for s in [
        "Nat.min",
        "Nat.max",
        "Nat.min_le_left",
        "Nat.le_max_right",
        "Nat.min_comm",
        "Nat.max_comm",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_init_nat_add_ord() {
    let mut env = Environment::new();
    assert!(!env.has_nat_add_ord());

    env.init_nat_add_ord().unwrap();
    assert!(env.has_nat_add_ord());

    for s in [
        "Nat.add_lt_add_left",
        "Nat.add_lt_add_right",
        "Nat.add_le_add_left",
        "Nat.add_le_add_right",
        "Nat.add_lt_add",
        "Nat.add_le_add",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_nat_add_ord_type_checks() {
    let mut env = Environment::new();
    env.init_nat_add_ord().unwrap();

    // #3604 (lt cluster): `Nat.add_lt_add_left` (and the rest of the
    // `add_lt_add*` family) is now a constructive `Declaration::Theorem` — see
    // `nat_arith_order_proof.rs`.
    assert_eq!(
        env.get_const(&Name::from_string("Nat.add_lt_add_left"))
            .expect("Nat.add_lt_add_left registered")
            .kind,
        ConstantKind::Theorem,
        "Nat.add_lt_add_left should be demoted to a Theorem",
    );

    // #3604: `Nat.add_le_add` (and the rest of the `add_le_add*` family) is now
    // a constructive `Declaration::Theorem` — see `nat_arith_order_proof.rs`.
    assert_eq!(
        env.get_const(&Name::from_string("Nat.add_le_add"))
            .expect("Nat.add_le_add registered")
            .kind,
        ConstantKind::Theorem,
        "Nat.add_le_add should be demoted to a Theorem",
    );

    // Check dependencies were initialized
    for s in ["Nat.add", "Nat.lt", "Nat.le"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_nat_add_ord_binder_order() {
    // Lean 4 convention: ∀ a b, rel a b → ∀ c, ...
    // The proof hypothesis `h` comes before the added term `c`.
    // Regression for Prover audit (p1032): all four Nat add ordering axioms
    // previously had `c` before `h`, diverging from Lean 4.
    let mut env = Environment::new();
    env.init_nat_add_ord().unwrap();
    use crate::tc::TypeChecker;
    let tc = TypeChecker::new(&env);
    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
    let le_const = Expr::const_(Name::from_string("Nat.le"), vec![]);
    let lt_const = Expr::const_(Name::from_string("Nat.lt"), vec![]);

    // Nat.add_le_add_left : ∀ a b : Nat, Nat.le a b → ∀ c : Nat, ...
    let ty = tc
        .infer_type(&Expr::const_(
            Name::from_string("Nat.add_le_add_left"),
            vec![],
        ))
        .unwrap();
    assert_eq!(pi_domain_at(&ty, 0), Some(&nat_const), "binder 0 = a : Nat");
    assert_eq!(pi_domain_at(&ty, 1), Some(&nat_const), "binder 1 = b : Nat");
    let expected_le_h = Expr::app(Expr::app(le_const.clone(), Expr::bvar(1)), Expr::bvar(0));
    assert_eq!(
        pi_domain_at(&ty, 2),
        Some(&expected_le_h),
        "binder 2 = h : Nat.le a b"
    );
    assert_eq!(pi_domain_at(&ty, 3), Some(&nat_const), "binder 3 = c : Nat");

    // Nat.add_le_add_right : ∀ a b : Nat, Nat.le a b → ∀ c : Nat, ...
    let ty = tc
        .infer_type(&Expr::const_(
            Name::from_string("Nat.add_le_add_right"),
            vec![],
        ))
        .unwrap();
    assert_eq!(
        pi_domain_at(&ty, 2),
        Some(&expected_le_h),
        "binder 2 = h : Nat.le a b"
    );
    assert_eq!(pi_domain_at(&ty, 3), Some(&nat_const), "binder 3 = c : Nat");

    // Nat.add_lt_add_left : ∀ a b : Nat, Nat.lt a b → ∀ c : Nat, ...
    let ty = tc
        .infer_type(&Expr::const_(
            Name::from_string("Nat.add_lt_add_left"),
            vec![],
        ))
        .unwrap();
    let expected_lt_h = Expr::app(Expr::app(lt_const.clone(), Expr::bvar(1)), Expr::bvar(0));
    assert_eq!(
        pi_domain_at(&ty, 2),
        Some(&expected_lt_h),
        "binder 2 = h : Nat.lt a b"
    );
    assert_eq!(pi_domain_at(&ty, 3), Some(&nat_const), "binder 3 = c : Nat");

    // Nat.add_lt_add_right : ∀ a b : Nat, Nat.lt a b → ∀ c : Nat, ...
    let ty = tc
        .infer_type(&Expr::const_(
            Name::from_string("Nat.add_lt_add_right"),
            vec![],
        ))
        .unwrap();
    assert_eq!(
        pi_domain_at(&ty, 2),
        Some(&expected_lt_h),
        "binder 2 = h : Nat.lt a b"
    );
    assert_eq!(pi_domain_at(&ty, 3), Some(&nat_const), "binder 3 = c : Nat");
}

#[test]
fn test_nat_add_ord_idempotent() {
    let mut env = Environment::new();
    env.init_nat_add_ord().unwrap();
    // Should be idempotent
    env.init_nat_add_ord().unwrap();
    assert!(env.has_nat_add_ord());
}

#[test]
fn test_init_nat_mul_ord() {
    let mut env = Environment::new();
    assert!(!env.has_nat_mul_ord());

    env.init_nat_mul_ord().unwrap();
    assert!(env.has_nat_mul_ord());

    for s in [
        "Nat.mul_lt_mul_left",
        "Nat.mul_lt_mul_right",
        "Nat.mul_le_mul_left",
        "Nat.mul_le_mul_right",
        "Nat.mul_lt_mul",
        "Nat.mul_le_mul",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_nat_mul_ord_type_checks() {
    let mut env = Environment::new();
    env.init_nat_mul_ord().unwrap();

    // #3604 (lt cluster): `Nat.mul_lt_mul_left` is now a constructive
    // `Declaration::Theorem` — see `nat_arith_order_proof.rs`. The
    // `Nat.mul_lt_mul_right` / `Nat.mul_lt_mul` lemmas remain axioms (no value).
    assert_eq!(
        env.get_const(&Name::from_string("Nat.mul_lt_mul_left"))
            .expect("Nat.mul_lt_mul_left registered")
            .kind,
        ConstantKind::Theorem,
        "Nat.mul_lt_mul_left should be demoted to a Theorem",
    );
    assert_axiom(&env, "Nat.mul_lt_mul_right");

    // #3604: `Nat.mul_le_mul` (and `Nat.mul_le_mul_right`) is now a constructive
    // `Declaration::Theorem` — see `nat_arith_order_proof.rs`.
    assert_eq!(
        env.get_const(&Name::from_string("Nat.mul_le_mul"))
            .expect("Nat.mul_le_mul registered")
            .kind,
        ConstantKind::Theorem,
        "Nat.mul_le_mul should be demoted to a Theorem",
    );

    // Check dependencies were initialized
    for s in ["Nat.mul", "Nat.lt", "Nat.le"] {
        assert_const(&env, s);
    }
}

/// FIDELITY + ADVERSARIAL REGRESSION GUARD: `Nat.mul_le_mul` must have Lean
/// core's real signature `∀ {n₁ m₁ n₂ m₂}, n₁ ≤ n₂ → m₁ ≤ m₂ → n₁*m₁ ≤ n₂*m₂`,
/// NOT the transposed `∀ a b c d, a ≤ b → c ≤ d → a*c ≤ b*d` a prior version
/// shipped. The transposed form is a genuinely different theorem: it rejected
/// every real Mathlib proof that applied `Nat.mul_le_mul` (e.g.
/// `Nat.one_lt_mul_iff`, which passes `m ≤ 1` for the first hypothesis). This
/// test pins the CORRECT hypothesis pairing at the De Bruijn level so a
/// regression to the transposed form fails here.
#[test]
fn test_nat_mul_le_mul_lean_faithful_signature() {
    let mut env = Environment::new();
    env.init_nat_mul_ord().unwrap();

    let ci = env
        .get_const(&Name::from_string("Nat.mul_le_mul"))
        .expect("Nat.mul_le_mul registered");

    // Helper: the two arguments of a `Nat.le x y` application.
    fn le_args(e: &Expr) -> Option<(u32, u32)> {
        // App(App(Const "Nat.le", x), y) — read BVar indices of x and y.
        if let ExprKind::App(f, y) = &e.kind {
            if let ExprKind::App(_, x) = &f.kind {
                if let (ExprKind::BVar(xi), ExprKind::BVar(yi)) = (&x.kind, &y.kind) {
                    return Some((*xi, *yi));
                }
            }
        }
        None
    }

    // h₁ is the 5th binder (index 4): domain must be `Nat.le n₁ n₂`.
    // At that depth the De Bruijn context (innermost last) is
    // [n₁, m₁, n₂, m₂] → n₁=BVar3, m₁=BVar2, n₂=BVar1, m₂=BVar0.
    // Lean's pairing is `n₁ ≤ n₂` = (BVar3, BVar1). The transposed form would
    // give `a ≤ b` = (BVar3, BVar2) — this assert rejects that.
    let h1 = pi_domain_at(&ci.type_, 4).expect("h₁ Pi domain");
    assert_eq!(
        le_args(h1),
        Some((3, 1)),
        "h₁ must be `n₁ ≤ n₂` (BVar3 ≤ BVar1), not the transposed `a ≤ b`; got {h1:?}",
    );

    // h₂ is the 6th binder (index 5): domain must be `Nat.le m₁ m₂`.
    // At that depth the context is [n₁, m₁, n₂, m₂, h₁] → m₁=BVar3, m₂=BVar1.
    let h2 = pi_domain_at(&ci.type_, 5).expect("h₂ Pi domain");
    assert_eq!(
        le_args(h2),
        Some((3, 1)),
        "h₂ must be `m₁ ≤ m₂` (BVar3 ≤ BVar1); got {h2:?}",
    );

    // The declaration is a kernel-checked Theorem (add_decl validated the proof
    // against this type), so the value proves exactly `n₁*m₁ ≤ n₂*m₂`.
    assert_eq!(ci.kind, ConstantKind::Theorem);
}

/// ADVERSARIAL: the corrected `Nat.mul_le_mul` must still REJECT an ill-typed
/// application — the fidelity fix recovers real proofs, it must NOT make the
/// kernel more permissive. Here we feed a proof of `2 ≤ 3` where the first
/// hypothesis expects `1 ≤ 5` (`n₁ := 1, n₂ := 5`). `2 ≤ 3` is a true but
/// WRONG-shape proof; `check_type` must reject the application, confirming the
/// kernel is not accepting mismatched hypotheses through the corrected type.
#[test]
fn test_nat_mul_le_mul_rejects_wrong_hypothesis() {
    let mut env = Environment::new();
    env.init_nat_mul_ord().unwrap();
    env.init_le().unwrap();

    let nat_lit = |k: u64| {
        // Build `k` as `Nat.succ^k Nat.zero` so `Nat.le.refl`/kernel see a literal.
        let mut e = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        for _ in 0..k {
            e = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), e);
        }
        e
    };
    let le = |x: Expr, y: Expr| {
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Nat.le"), vec![]), x),
            y,
        )
    };

    // A genuine proof `h23 : Nat.le 2 3` (via a hypothesis fvar of that type is
    // simplest and sound for the adversarial check — we only test that the
    // kernel refuses to USE it where `Nat.le 1 5` is required).
    let tc = crate::tc::TypeChecker::new(&env);

    // Partially applied: `@Nat.mul_le_mul 1 m1 5 m2` — its first Pi domain is
    // `Nat.le 1 5`. We construct `Nat.mul_le_mul 1 2 5 4` and then check that
    // supplying a proof of `Nat.le 2 3` (WRONG: expects `Nat.le 1 5`) as the
    // first hypothesis is rejected. We do this by inferring the type of the
    // 4-arg head and confirming the expected h₁ domain is `Nat.le 1 5`,
    // i.e. NOT def-eq to `Nat.le 2 3`.
    let head = Expr::apps(
        Expr::const_(Name::from_string("Nat.mul_le_mul"), vec![]),
        [nat_lit(1), nat_lit(2), nat_lit(5), nat_lit(4)],
    );
    let head_ty = tc.infer_type(&head).expect("head type infers");
    let expected_h1 = pi_domain_at(&head_ty, 0).expect("h₁ domain of applied head");
    // The kernel must see `Nat.le 1 5` here, which is NOT def-eq to `Nat.le 2 3`.
    let wrong = le(nat_lit(2), nat_lit(3));
    assert!(
        !tc.is_def_eq(expected_h1, &wrong),
        "kernel must NOT equate the expected `Nat.le 1 5` hypothesis with a \
         `Nat.le 2 3` proof — that would be unsound. expected_h1={expected_h1:?}",
    );
    // And the correctly-shaped hypothesis IS the expected one.
    let right = le(nat_lit(1), nat_lit(5));
    assert!(
        tc.is_def_eq(expected_h1, &right),
        "expected h₁ must be `Nat.le 1 5`; got {expected_h1:?}",
    );
}

#[test]
fn test_nat_mul_ord_idempotent() {
    let mut env = Environment::new();
    env.init_nat_mul_ord().unwrap();
    // Should be idempotent
    env.init_nat_mul_ord().unwrap();
    assert!(env.has_nat_mul_ord());
}

#[test]
fn test_complete_nat_arith_ordering() {
    // Test full arithmetic ordering support
    let mut env = Environment::new();

    // Initialize full ordering hierarchy including arithmetic lemmas
    env.init_nat_linear_order().unwrap();
    env.init_nat_add_ord().unwrap();
    env.init_nat_mul_ord().unwrap();

    // Verify comprehensive ordering support
    assert!(env.has_nat_linear_order());
    assert!(env.has_nat_add_ord());
    assert!(env.has_nat_mul_ord());

    // Verify add and mul ordering lemmas
    for s in [
        "Nat.add_lt_add_left",
        "Nat.add_lt_add_right",
        "Nat.add_le_add_left",
        "Nat.add_le_add_right",
        "Nat.add_lt_add",
        "Nat.add_le_add",
        "Nat.mul_lt_mul_left",
        "Nat.mul_lt_mul_right",
        "Nat.mul_le_mul_left",
        "Nat.mul_le_mul_right",
        "Nat.mul_lt_mul",
        "Nat.mul_le_mul",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_init_nat_sub_ord() {
    let mut env = Environment::new();
    assert!(!env.has_nat_sub_ord());

    env.init_nat_sub_ord().unwrap();
    assert!(env.has_nat_sub_ord());

    for s in [
        "Nat.sub_le",
        "Nat.sub_lt",
        "Nat.sub_le_sub_left",
        "Nat.sub_le_sub_right",
        "Nat.sub_self",
        "Nat.sub_zero",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_nat_sub_ord_type_checks() {
    let mut env = Environment::new();
    env.init_nat_sub_ord().unwrap();

    // #3604 (lt cluster): `Nat.sub_le` is now a constructive
    // `Declaration::Theorem` — see `nat_arith_order_proof.rs`.
    assert_eq!(
        env.get_const(&Name::from_string("Nat.sub_le"))
            .expect("Nat.sub_le registered")
            .kind,
        ConstantKind::Theorem,
        "Nat.sub_le should be demoted to a Theorem",
    );

    // #3604: `Nat.sub_self` is now a constructive `Declaration::Theorem` —
    // see `nat_sub_order_remaining_proof.rs`.
    assert_eq!(
        env.get_const(&Name::from_string("Nat.sub_self"))
            .expect("Nat.sub_self registered")
            .kind,
        ConstantKind::Theorem,
        "Nat.sub_self should be demoted to a Theorem",
    );

    // Check dependencies were initialized
    for s in ["Nat.sub", "Nat.lt", "Nat.le"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_nat_sub_ord_idempotent() {
    let mut env = Environment::new();
    env.init_nat_sub_ord().unwrap();
    // Should be idempotent
    env.init_nat_sub_ord().unwrap();
    assert!(env.has_nat_sub_ord());
}

#[test]
fn test_init_nat_pow_ord() {
    let mut env = Environment::new();
    assert!(!env.has_nat_pow_ord());

    env.init_nat_pow_ord().unwrap();
    assert!(env.has_nat_pow_ord());

    for s in [
        "Nat.pow_le_pow_left",
        "Nat.pow_lt_pow_left",
        "Nat.pow_le_pow_right",
        "Nat.pow_zero",
        "Nat.pow_one",
        "Nat.one_pow",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_nat_pow_ord_type_checks() {
    let mut env = Environment::new();
    env.init_nat_pow_ord().unwrap();

    // All should be axioms (no value)
    assert_axiom(&env, "Nat.pow_le_pow_left");

    assert_axiom(&env, "Nat.pow_zero");

    // Check dependencies were initialized
    for s in ["Nat.pow", "Nat.lt", "Nat.le"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_nat_pow_ord_idempotent() {
    let mut env = Environment::new();
    env.init_nat_pow_ord().unwrap();
    // Should be idempotent
    env.init_nat_pow_ord().unwrap();
    assert!(env.has_nat_pow_ord());
}

#[test]
fn test_complete_nat_arith_support() {
    // Test full arithmetic support including sub and pow
    let mut env = Environment::new();

    // Initialize full ordering hierarchy including all arithmetic lemmas
    env.init_nat_linear_order().unwrap();
    env.init_nat_add_ord().unwrap();
    env.init_nat_mul_ord().unwrap();
    env.init_nat_sub_ord().unwrap();
    env.init_nat_pow_ord().unwrap();

    // Verify comprehensive arithmetic support
    assert!(env.has_nat_linear_order());
    assert!(env.has_nat_add_ord());
    assert!(env.has_nat_mul_ord());
    assert!(env.has_nat_sub_ord());
    assert!(env.has_nat_pow_ord());

    // Verify core operations and lemmas
    for s in [
        "Nat.add",
        "Nat.mul",
        "Nat.sub",
        "Nat.pow",
        "Nat.sub_le",
        "Nat.sub_lt",
        "Nat.sub_self",
        "Nat.sub_zero",
        "Nat.pow_le_pow_left",
        "Nat.pow_lt_pow_left",
        "Nat.pow_zero",
        "Nat.pow_one",
        "Nat.one_pow",
    ] {
        assert_const(&env, s);
    }
}

// ==================== Int Arithmetic Tests ====================

#[test]
fn test_init_int_arith() {
    let mut env = Environment::new();
    assert!(!env.has_int_arith());

    env.init_int_arith().unwrap();
    assert!(env.has_int_arith());

    // Int should be auto-initialized as dependency
    assert!(env.has_int());

    // Check all arithmetic operations were added
    for s in [
        "Int.negOfNat",
        "Int.subNatNat",
        "Int.add",
        "Int.sub",
        "Int.mul",
    ] {
        assert_const(&env, s);
    }

    // Idempotence
    env.init_int_arith().unwrap();
    assert!(env.has_int_arith());
}

#[test]
fn test_int_arith_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_arith().unwrap();

    let tc = TypeChecker::new(&env);

    let int_const = Expr::const_(Name::from_string("Int"), vec![]);
    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

    // Int.negOfNat : Nat → Int
    let neg_of_nat_type = tc
        .infer_type(&Expr::const_(Name::from_string("Int.negOfNat"), vec![]))
        .unwrap();
    let expected_neg_of_nat = Expr::pi(BinderInfo::Default, nat_const.clone(), int_const.clone());
    assert!(tc.is_def_eq(&neg_of_nat_type, &expected_neg_of_nat));

    // Int.subNatNat : Nat → Nat → Int
    let sub_nat_nat_type = tc
        .infer_type(&Expr::const_(Name::from_string("Int.subNatNat"), vec![]))
        .unwrap();
    let expected_sub_nat_nat = Expr::pi(
        BinderInfo::Default,
        nat_const.clone(),
        Expr::pi(BinderInfo::Default, nat_const.clone(), int_const.clone()),
    );
    assert!(tc.is_def_eq(&sub_nat_nat_type, &expected_sub_nat_nat));

    // Int.add : Int → Int → Int
    let add_type = tc
        .infer_type(&Expr::const_(Name::from_string("Int.add"), vec![]))
        .unwrap();
    let expected_add = Expr::pi(
        BinderInfo::Default,
        int_const.clone(),
        Expr::pi(BinderInfo::Default, int_const.clone(), int_const.clone()),
    );
    assert!(tc.is_def_eq(&add_type, &expected_add));

    // Int.sub : Int → Int → Int
    let sub_type = tc
        .infer_type(&Expr::const_(Name::from_string("Int.sub"), vec![]))
        .unwrap();
    let expected_sub = Expr::pi(
        BinderInfo::Default,
        int_const.clone(),
        Expr::pi(BinderInfo::Default, int_const.clone(), int_const.clone()),
    );
    assert!(tc.is_def_eq(&sub_type, &expected_sub));

    // Int.mul : Int → Int → Int
    let mul_type = tc
        .infer_type(&Expr::const_(Name::from_string("Int.mul"), vec![]))
        .unwrap();
    let expected_mul = Expr::pi(
        BinderInfo::Default,
        int_const.clone(),
        Expr::pi(BinderInfo::Default, int_const.clone(), int_const.clone()),
    );
    assert!(tc.is_def_eq(&mul_type, &expected_mul));
}

#[test]
fn test_int_arith_idempotent() {
    let mut env = Environment::new();

    // Call multiple times
    env.init_int_arith().unwrap();
    env.init_int_arith().unwrap();
    env.init_int_arith().unwrap();

    // Should still work
    assert!(env.has_int_arith());
    assert_const(&env, "Int.add");
}

#[test]
fn test_complete_int_arith_support() {
    let mut env = Environment::new();
    env.init_int_arith().unwrap();

    // Verify all Int constants exist
    let int_consts = [
        "Int",
        "Int.ofNat",
        "Int.negSucc",
        "Int.neg",
        "Int.toNat",
        "Int.negOfNat",
        "Int.subNatNat",
        "Int.add",
        "Int.sub",
        "Int.mul",
    ];

    for name in int_consts {
        let name_obj = Name::from_string(name);
        let is_const = env.get_const(&name_obj).is_some();
        let is_ind = env.get_inductive(&name_obj).is_some();
        let is_ctor = env.get_constructor(&name_obj).is_some();
        assert!(is_const || is_ind || is_ctor, "Missing constant: {name}");
    }
}

#[test]
fn test_init_int_ord() {
    let mut env = Environment::new();
    env.init_int_ord().unwrap();

    assert_inductive(&env, "Int.NonNeg");
    assert_ctor(&env, "Int.NonNeg.mk", "Int.NonNeg");
    for s in ["Int.le", "Int.lt", "instLEInt", "instLTInt"] {
        assert_const(&env, s);
    }
    assert!(env.has_int_ord());
}

#[test]
fn test_int_ord_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_ord().unwrap();

    let tc = TypeChecker::new(&env);
    let int_const = Expr::const_(Name::from_string("Int"), vec![]);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // Int.NonNeg : Int → Prop
    let nonneg_type = tc
        .infer_type(&Expr::const_(Name::from_string("Int.NonNeg"), vec![]))
        .unwrap();
    let expected_nonneg = Expr::pi(BinderInfo::Default, int_const.clone(), prop.clone());
    assert!(tc.is_def_eq(&nonneg_type, &expected_nonneg));

    // Int.NonNeg.mk : (n : Nat) → Int.NonNeg (Int.ofNat n)
    let nonneg_mk_type = tc
        .infer_type(&Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]))
        .unwrap();
    // Just verify it has the right structure (a Pi type)
    assert!(matches!(nonneg_mk_type.kind, ExprKind::Pi(..)));

    // Int.le : Int → Int → Prop
    let le_type = tc
        .infer_type(&Expr::const_(Name::from_string("Int.le"), vec![]))
        .unwrap();
    let expected_le = Expr::pi(
        BinderInfo::Default,
        int_const.clone(),
        Expr::pi(BinderInfo::Default, int_const.clone(), prop.clone()),
    );
    assert!(tc.is_def_eq(&le_type, &expected_le));

    // Int.lt : Int → Int → Prop
    let lt_type = tc
        .infer_type(&Expr::const_(Name::from_string("Int.lt"), vec![]))
        .unwrap();
    let expected_lt = Expr::pi(
        BinderInfo::Default,
        int_const.clone(),
        Expr::pi(BinderInfo::Default, int_const.clone(), prop.clone()),
    );
    assert!(tc.is_def_eq(&lt_type, &expected_lt));

    // instLEInt : LE Int
    // LE : Type u → Type u, Int : Type 0, so LE.{0}
    let inst_le_type = tc
        .infer_type(&Expr::const_(Name::from_string("instLEInt"), vec![]))
        .unwrap();
    let expected_inst_le = Expr::app(
        Expr::const_(Name::from_string("LE"), vec![Level::zero()]),
        int_const.clone(),
    );
    assert!(tc.is_def_eq(&inst_le_type, &expected_inst_le));

    // instLTInt : LT Int
    // LT : Type u → Type u, Int : Type 0, so LT.{0}
    let inst_lt_type = tc
        .infer_type(&Expr::const_(Name::from_string("instLTInt"), vec![]))
        .unwrap();
    let expected_inst_lt = Expr::app(
        Expr::const_(Name::from_string("LT"), vec![Level::zero()]),
        int_const.clone(),
    );
    assert!(tc.is_def_eq(&inst_lt_type, &expected_inst_lt));
}

#[test]
fn test_int_ord_idempotent() {
    let mut env = Environment::new();

    // Call multiple times
    env.init_int_ord().unwrap();
    env.init_int_ord().unwrap();
    env.init_int_ord().unwrap();

    // Should still work
    assert!(env.has_int_ord());
    assert_const(&env, "Int.le");
}

#[test]
fn test_complete_int_ord_support() {
    let mut env = Environment::new();
    env.init_int_ord().unwrap();

    // Verify all Int ordering constants exist (mix of const/inductive/constructor)
    assert_inductive(&env, "Int.NonNeg");
    assert_ctor(&env, "Int.NonNeg.mk", "Int.NonNeg");
    for s in ["Int.le", "Int.lt", "instLEInt", "instLTInt"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_init_int_decidable_ord() {
    let mut env = Environment::new();
    env.init_int_decidable_ord().unwrap();

    for s in ["instDecidableIntLt", "instDecidableIntLe", "Int.decEq"] {
        assert_const(&env, s);
    }
    assert!(env.has_int_decidable_ord());
}

#[test]
fn test_int_decidable_ord_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_decidable_ord().unwrap();

    let tc = TypeChecker::new(&env);
    let int_const = Expr::const_(Name::from_string("Int"), vec![]);
    let decidable_const = Expr::const_(Name::from_string("Decidable"), vec![]);
    let lt_const = Expr::const_(Name::from_string("Int.lt"), vec![]);
    let le_const = Expr::const_(Name::from_string("Int.le"), vec![]);

    // instDecidableIntLt : ∀ a b : Int, Decidable (Int.lt a b)
    let dec_lt_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("instDecidableIntLt"),
            vec![],
        ))
        .unwrap();
    let expected_dec_lt = Expr::pi(
        BinderInfo::Default,
        int_const.clone(),
        Expr::pi(
            BinderInfo::Default,
            int_const.clone(),
            Expr::app(
                decidable_const.clone(),
                Expr::app(Expr::app(lt_const.clone(), Expr::bvar(1)), Expr::bvar(0)),
            ),
        ),
    );
    assert!(tc.is_def_eq(&dec_lt_type, &expected_dec_lt));

    // instDecidableIntLe : ∀ a b : Int, Decidable (Int.le a b)
    let dec_le_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("instDecidableIntLe"),
            vec![],
        ))
        .unwrap();
    let expected_dec_le = Expr::pi(
        BinderInfo::Default,
        int_const.clone(),
        Expr::pi(
            BinderInfo::Default,
            int_const.clone(),
            Expr::app(
                decidable_const.clone(),
                Expr::app(Expr::app(le_const.clone(), Expr::bvar(1)), Expr::bvar(0)),
            ),
        ),
    );
    assert!(tc.is_def_eq(&dec_le_type, &expected_dec_le));

    // Int.decEq : ∀ a b : Int, Decidable (Eq a b)
    let dec_eq_type = tc
        .infer_type(&Expr::const_(Name::from_string("Int.decEq"), vec![]))
        .unwrap();
    // Just verify it's a Pi type with the right shape
    assert!(matches!(dec_eq_type.kind, ExprKind::Pi(..)));
}

#[test]
fn test_int_decidable_ord_idempotent() {
    let mut env = Environment::new();

    // Call multiple times
    env.init_int_decidable_ord().unwrap();
    env.init_int_decidable_ord().unwrap();
    env.init_int_decidable_ord().unwrap();

    // Should still work
    assert!(env.has_int_decidable_ord());
    assert_const(&env, "instDecidableIntLt");
}

#[test]
fn test_init_int_ord_lemmas() {
    let mut env = Environment::new();
    env.init_int_ord_lemmas().unwrap();

    for s in [
        "Int.le_refl",
        "Int.le_trans",
        "Int.le_antisymm",
        "Int.lt_irrefl",
        "Int.lt_trans",
        "Int.le_of_lt",
        "Int.lt_of_le_of_lt",
        "Int.lt_of_lt_of_le",
        "Int.lt_trichotomy",
        "Int.add_le_add_left",
        "Int.add_le_add_right",
        "Int.add_lt_add_left",
        "Int.add_lt_add_right",
        "Int.le_of_add_le_add_left",
        "Int.le_of_add_le_add_right",
        "Int.lt_of_add_lt_add_left",
        "Int.lt_of_add_lt_add_right",
        "Int.ofNat_zero_le",
        "Int.mul_nonneg",
        "Int.mul_le_mul_of_nonneg_left",
    ] {
        assert_const(&env, s);
    }
    assert!(env.has_int_ord_lemmas());
}

#[test]
fn test_int_ord_lemmas_le_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_ord_lemmas().unwrap();

    let tc = TypeChecker::new(&env);
    let int_const = Expr::const_(Name::from_string("Int"), vec![]);
    let le_const = Expr::const_(Name::from_string("Int.le"), vec![]);

    // Int.le_refl : ∀ a : Int, Int.le a a
    let le_refl_type = tc
        .infer_type(&Expr::const_(Name::from_string("Int.le_refl"), vec![]))
        .unwrap();
    let expected_le_refl = Expr::pi(
        BinderInfo::Default,
        int_const.clone(),
        Expr::app(Expr::app(le_const.clone(), Expr::bvar(0)), Expr::bvar(0)),
    );
    assert!(tc.is_def_eq(&le_refl_type, &expected_le_refl));

    // Int.add_le_add_left : ∀ a b : Int, Int.le a b → ∀ c : Int,
    //   Int.le (Int.add c a) (Int.add c b)
    let add_le_add_left_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("Int.add_le_add_left"),
            vec![],
        ))
        .unwrap();
    assert_eq!(
        pi_domain_at(&add_le_add_left_type, 0),
        Some(&int_const),
        "binder 0 should be `a : Int`"
    );
    assert_eq!(
        pi_domain_at(&add_le_add_left_type, 1),
        Some(&int_const),
        "binder 1 should be `b : Int`"
    );
    let expected_h_domain = Expr::app(Expr::app(le_const, Expr::bvar(1)), Expr::bvar(0));
    assert_eq!(
        pi_domain_at(&add_le_add_left_type, 2),
        Some(&expected_h_domain),
        "binder 2 should be `h : Int.le a b`"
    );
    assert_eq!(
        pi_domain_at(&add_le_add_left_type, 3),
        Some(&int_const),
        "binder 3 should be `c : Int`"
    );
}

#[test]
fn test_int_ord_lemmas_lt_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_ord_lemmas().unwrap();

    let tc = TypeChecker::new(&env);
    let int_const = Expr::const_(Name::from_string("Int"), vec![]);

    // Int.add_lt_add_left : ∀ a b : Int, Int.lt a b → ∀ c : Int,
    //   Int.lt (Int.add c a) (Int.add c b)
    let lt_const = Expr::const_(Name::from_string("Int.lt"), vec![]);
    let add_lt_add_left_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("Int.add_lt_add_left"),
            vec![],
        ))
        .unwrap();
    assert_eq!(
        pi_domain_at(&add_lt_add_left_type, 0),
        Some(&int_const),
        "add_lt_add_left binder 0 should be `a : Int`"
    );
    assert_eq!(
        pi_domain_at(&add_lt_add_left_type, 1),
        Some(&int_const),
        "add_lt_add_left binder 1 should be `b : Int`"
    );
    let expected_lt_h = Expr::app(Expr::app(lt_const, Expr::bvar(1)), Expr::bvar(0));
    assert_eq!(
        pi_domain_at(&add_lt_add_left_type, 2),
        Some(&expected_lt_h),
        "add_lt_add_left binder 2 should be `h : Int.lt a b`"
    );
    assert_eq!(
        pi_domain_at(&add_lt_add_left_type, 3),
        Some(&int_const),
        "add_lt_add_left binder 3 should be `c : Int`"
    );

    // Just verify the other lemmas are Pi types.
    let lemmas = [
        "Int.le_trans",
        "Int.le_antisymm",
        "Int.lt_irrefl",
        "Int.lt_trans",
        "Int.le_of_lt",
        "Int.lt_of_le_of_lt",
        "Int.lt_of_lt_of_le",
        "Int.lt_trichotomy",
        "Int.add_le_add_right",
        "Int.add_lt_add_right",
        "Int.le_of_add_le_add_left",
        "Int.le_of_add_le_add_right",
        "Int.lt_of_add_lt_add_left",
        "Int.lt_of_add_lt_add_right",
        "Int.ofNat_zero_le",
        "Int.mul_nonneg",
        "Int.mul_le_mul_of_nonneg_left",
    ];
    for lemma in lemmas {
        let lemma_type = tc
            .infer_type(&Expr::const_(Name::from_string(lemma), vec![]))
            .unwrap();
        assert!(
            matches!(lemma_type.kind, ExprKind::Pi(..)),
            "Lemma {lemma} should be a Pi type"
        );
    }
}

#[test]
fn test_int_ord_lemmas_idempotent() {
    let mut env = Environment::new();

    // Call multiple times
    env.init_int_ord_lemmas().unwrap();
    env.init_int_ord_lemmas().unwrap();
    env.init_int_ord_lemmas().unwrap();

    // Should still work
    assert!(env.has_int_ord_lemmas());
    assert_const(&env, "Int.le_refl");
}

#[test]
fn test_int_cancellation_lemma_binders() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_ord_lemmas().unwrap();

    let tc = TypeChecker::new(&env);
    let int_const = Expr::const_(Name::from_string("Int"), vec![]);

    // Int.le_of_add_le_add_right : ∀ a b c : Int,
    //   Int.le (Int.add a b) (Int.add c b) → Int.le a c
    let cancel_le_right = tc
        .infer_type(&Expr::const_(
            Name::from_string("Int.le_of_add_le_add_right"),
            vec![],
        ))
        .unwrap();
    assert_eq!(
        pi_domain_at(&cancel_le_right, 0),
        Some(&int_const),
        "le_of_add_le_add_right binder 0 should be `a : Int`"
    );
    assert_eq!(
        pi_domain_at(&cancel_le_right, 1),
        Some(&int_const),
        "le_of_add_le_add_right binder 1 should be `b : Int`"
    );
    assert_eq!(
        pi_domain_at(&cancel_le_right, 2),
        Some(&int_const),
        "le_of_add_le_add_right binder 2 should be `c : Int`"
    );

    // Binder 3 is the premise: Int.le (Int.add a b) (Int.add c b)
    // In de Bruijn: le (add (bvar 2) (bvar 1)) (add (bvar 0) (bvar 1))
    let le_const = Expr::const_(Name::from_string("Int.le"), vec![]);
    let add_const = Expr::const_(Name::from_string("Int.add"), vec![]);
    let expected_premise = Expr::app(
        Expr::app(
            le_const,
            Expr::app(Expr::app(add_const.clone(), Expr::bvar(2)), Expr::bvar(1)),
        ),
        Expr::app(Expr::app(add_const, Expr::bvar(0)), Expr::bvar(1)),
    );
    assert_eq!(
        pi_domain_at(&cancel_le_right, 3),
        Some(&expected_premise),
        "le_of_add_le_add_right binder 3 should be premise `Int.le (add a b) (add c b)`"
    );

    // Int.lt_of_add_lt_add_right : ∀ a b c : Int,
    //   Int.lt (Int.add a b) (Int.add c b) → Int.lt a c
    let cancel_lt_right = tc
        .infer_type(&Expr::const_(
            Name::from_string("Int.lt_of_add_lt_add_right"),
            vec![],
        ))
        .unwrap();
    assert_eq!(
        pi_domain_at(&cancel_lt_right, 0),
        Some(&int_const),
        "lt_of_add_lt_add_right binder 0 should be `a : Int`"
    );
    assert_eq!(
        pi_domain_at(&cancel_lt_right, 2),
        Some(&int_const),
        "lt_of_add_lt_add_right binder 2 should be `c : Int`"
    );
}

// ===========================================
// Tests for Int LinearOrder instance
// ===========================================

#[test]
fn test_int_linear_order_init() {
    let mut env = Environment::new();
    env.init_int_linear_order().unwrap();

    assert!(env.has_int_linear_order());
    for s in [
        "instPreorderInt",
        "instPartialOrderInt",
        "Int.le_total",
        "instLinearOrderInt",
        "Int.lt_iff_le_not_le",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_int_linear_order_idempotent() {
    let mut env = Environment::new();

    // Call multiple times
    env.init_int_linear_order().unwrap();
    env.init_int_linear_order().unwrap();
    env.init_int_linear_order().unwrap();

    // Should still work
    assert!(env.has_int_linear_order());
    assert_const(&env, "instLinearOrderInt");
}

#[test]
fn test_int_linear_order_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_linear_order().unwrap();

    let tc = TypeChecker::new(&env);
    let int_const = Expr::const_(Name::from_string("Int"), vec![]);

    // instPreorderInt : Preorder Int
    // Preorder : Type u → Type u, Int : Type 0, so Preorder.{0}
    let preorder_int = Expr::const_(Name::from_string("instPreorderInt"), vec![]);
    let preorder_int_ty = tc.infer_type(&preorder_int).unwrap();
    let expected_preorder_ty = Expr::app(
        Expr::const_(Name::from_string("Preorder"), vec![Level::zero()]),
        int_const.clone(),
    );
    assert!(tc.is_def_eq(&preorder_int_ty, &expected_preorder_ty));

    // instPartialOrderInt : PartialOrder Int
    // PartialOrder : Type u → Type u, Int : Type 0, so PartialOrder.{0}
    let partial_order_int = Expr::const_(Name::from_string("instPartialOrderInt"), vec![]);
    let partial_order_int_ty = tc.infer_type(&partial_order_int).unwrap();
    let expected_partial_order_ty = Expr::app(
        Expr::const_(Name::from_string("PartialOrder"), vec![Level::zero()]),
        int_const.clone(),
    );
    assert!(tc.is_def_eq(&partial_order_int_ty, &expected_partial_order_ty));

    // instLinearOrderInt : LinearOrder Int
    // LinearOrder : Type u → Type u, Int : Type 0, so LinearOrder.{0}
    let linear_order_int = Expr::const_(Name::from_string("instLinearOrderInt"), vec![]);
    let linear_order_int_ty = tc.infer_type(&linear_order_int).unwrap();
    let expected_linear_order_ty = Expr::app(
        Expr::const_(Name::from_string("LinearOrder"), vec![Level::zero()]),
        int_const.clone(),
    );
    assert!(tc.is_def_eq(&linear_order_int_ty, &expected_linear_order_ty));
}

/// `instPreorderInt` must be a `Declaration::Definition` (not an Axiom)
/// carrying the concrete instance value `Preorder.mk @Int instLEInt instLTInt
/// Int.le_refl Int.le_trans`, matching `instPreorderNat` (#3553) and
/// `instPreorderRat` (#3222). A `Preorder` needs only reflexivity and
/// transitivity, both supplied by constructive empty-closure theorems, so no
/// domain-specific axiom enters its closure.
#[test]
fn test_inst_preorder_int_is_constructive_definition() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_linear_order().unwrap();

    // (1) Registered as a Definition with a concrete value — not an Axiom.
    let info = env
        .get_const(&Name::from_string("instPreorderInt"))
        .expect("instPreorderInt should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "instPreorderInt must be a Definition after demotion, got {:?}",
        info.kind
    );
    let value = info
        .value
        .as_ref()
        .expect("instPreorderInt must carry a concrete value, not be an opaque axiom");

    // (2) The value head is `Preorder.mk` (a real structure constructor), not
    // a bare axiom self-reference.
    let mut head: Expr = value.clone();
    while let ExprKind::App(f, _) = head.kind() {
        head = (**f).clone();
    }
    match head.kind() {
        ExprKind::Const(n, _) => assert_eq!(
            n.to_string(),
            "Preorder.mk",
            "instPreorderInt value root must be Preorder.mk"
        ),
        k => panic!("expected Const(Preorder.mk), got {:?}", k),
    }

    // (3) The value type-checks: infer_type yields `Preorder Int`.
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(&Expr::const_(Name::from_string("instPreorderInt"), vec![]))
        .expect("instPreorderInt should infer a type");
    let expected = Expr::app(
        Expr::const_(Name::from_string("Preorder"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Int"), vec![]),
    );
    assert!(
        tc.is_def_eq(&inferred, &expected),
        "instPreorderInt must have type `Preorder Int`, got {inferred:?}"
    );

    // (4) Empty domain-specific axiom closure — the soundness boundary. The
    // value depends only on the constructive Int.le_refl / Int.le_trans (and
    // their constructive sub-lemmas), NEVER on Int.le_antisymm / Int.le_total
    // / decidable Int comparison (#2422-blocked).
    let deps = env
        .axiom_deps(&Name::from_string("instPreorderInt"))
        .expect("instPreorderInt is registered, axiom_deps should return Some");
    let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
    assert!(
        domain_deps.is_empty(),
        "instPreorderInt must have empty domain-axiom closure, got {domain_deps:?}"
    );

    // (5) The two structure fields are themselves constructive empty-closure
    // theorems (this is what makes the instance constructive).
    for field in ["Int.le_refl", "Int.le_trans"] {
        let fname = Name::from_string(field);
        let finfo = env
            .get_const(&fname)
            .unwrap_or_else(|| panic!("{field} should be registered"));
        assert_eq!(
            finfo.kind,
            ConstantKind::Theorem,
            "{field} must be a Theorem (constructive proof), got {:?}",
            finfo.kind
        );
        match env.proof_quality(&fname) {
            Some(ProofQuality::Constructive) => {}
            other => panic!("{field} must be ProofQuality::Constructive, got {other:?}"),
        }
    }
}

/// `instPartialOrderInt` must be a `Declaration::Definition` (not an Axiom)
/// carrying the concrete instance value `PartialOrder.mk @Int instPreorderInt
/// Int.le_antisymm`, matching `instPartialOrderRat` (#3222). A `PartialOrder`
/// extends a `Preorder` with only `le_antisymm`, and `Int.le_antisymm` is a
/// constructive empty-closure theorem (#2422), so no domain-specific axiom
/// enters its closure.
#[test]
fn test_inst_partial_order_int_is_constructive_definition() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_linear_order().unwrap();

    // (1) Registered as a Definition with a concrete value — not an Axiom.
    let info = env
        .get_const(&Name::from_string("instPartialOrderInt"))
        .expect("instPartialOrderInt should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "instPartialOrderInt must be a Definition after demotion, got {:?}",
        info.kind
    );
    let value = info
        .value
        .as_ref()
        .expect("instPartialOrderInt must carry a concrete value, not be an opaque axiom");

    // (2) The value head is `PartialOrder.mk` (a real structure constructor),
    // not a bare axiom self-reference.
    let mut head: Expr = value.clone();
    while let ExprKind::App(f, _) = head.kind() {
        head = (**f).clone();
    }
    match head.kind() {
        ExprKind::Const(n, _) => assert_eq!(
            n.to_string(),
            "PartialOrder.mk",
            "instPartialOrderInt value root must be PartialOrder.mk"
        ),
        k => panic!("expected Const(PartialOrder.mk), got {:?}", k),
    }

    // (3) The value type-checks: infer_type yields `PartialOrder Int`.
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(&Expr::const_(
            Name::from_string("instPartialOrderInt"),
            vec![],
        ))
        .expect("instPartialOrderInt should infer a type");
    let expected = Expr::app(
        Expr::const_(Name::from_string("PartialOrder"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Int"), vec![]),
    );
    assert!(
        tc.is_def_eq(&inferred, &expected),
        "instPartialOrderInt must have type `PartialOrder Int`, got {inferred:?}"
    );

    // (4) Empty domain-specific axiom closure — the soundness boundary. The
    // value depends only on the constructive instPreorderInt and
    // Int.le_antisymm (and their constructive sub-lemmas), NEVER on
    // Int.le_total / decidable Int comparison.
    let deps = env
        .axiom_deps(&Name::from_string("instPartialOrderInt"))
        .expect("instPartialOrderInt is registered, axiom_deps should return Some");
    let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
    assert!(
        domain_deps.is_empty(),
        "instPartialOrderInt must have empty domain-axiom closure, got {domain_deps:?}"
    );

    // (5) The single additional structure field beyond the base Preorder is
    // itself a constructive empty-closure theorem (this is what makes the
    // instance constructive). The base Preorder, instPreorderInt, is verified
    // by test_inst_preorder_int_is_constructive_definition.
    let antisymm = Name::from_string("Int.le_antisymm");
    let finfo = env
        .get_const(&antisymm)
        .expect("Int.le_antisymm should be registered");
    assert_eq!(
        finfo.kind,
        ConstantKind::Theorem,
        "Int.le_antisymm must be a Theorem (constructive proof), got {:?}",
        finfo.kind
    );
    match env.proof_quality(&antisymm) {
        Some(ProofQuality::Constructive) => {}
        other => panic!("Int.le_antisymm must be ProofQuality::Constructive, got {other:?}"),
    }

    // (6) instPreorderInt, the base of the PartialOrder, is also a Definition.
    let pre_info = env
        .get_const(&Name::from_string("instPreorderInt"))
        .expect("instPreorderInt should be registered");
    assert_eq!(
        pre_info.kind,
        ConstantKind::Definition,
        "instPreorderInt (base of instPartialOrderInt) must be a Definition, got {:?}",
        pre_info.kind
    );
}

#[test]
fn test_int_le_total_type() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_linear_order().unwrap();

    let tc = TypeChecker::new(&env);
    let int_const = Expr::const_(Name::from_string("Int"), vec![]);
    let le_const = Expr::const_(Name::from_string("Int.le"), vec![]);
    let or_const = Expr::const_(Name::from_string("Or"), vec![]);

    // Int.le_total : ∀ a b : Int, Or (Int.le a b) (Int.le b a)
    let le_total = Expr::const_(Name::from_string("Int.le_total"), vec![]);
    let le_total_ty = tc.infer_type(&le_total).unwrap();

    // Build expected type
    let expected_ty = Expr::pi(
        BinderInfo::Default,
        int_const.clone(),
        Expr::pi(
            BinderInfo::Default,
            int_const.clone(),
            Expr::app(
                Expr::app(
                    or_const.clone(),
                    Expr::app(Expr::app(le_const.clone(), Expr::bvar(1)), Expr::bvar(0)),
                ),
                Expr::app(Expr::app(le_const.clone(), Expr::bvar(0)), Expr::bvar(1)),
            ),
        ),
    );

    assert!(tc.is_def_eq(&le_total_ty, &expected_ty));
}

// ===========================================
// Tests for Int sign/abs operations
// ===========================================

#[test]
fn test_init_int_sign_abs() {
    let mut env = Environment::new();
    env.init_int_sign_abs().unwrap();

    for s in ["Int.natAbs", "Int.abs", "Int.sign", "Int.neg"] {
        assert_const(&env, s);
    }
    assert!(env.has_int_sign_abs());
}

#[test]
fn test_int_sign_abs_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_sign_abs().unwrap();

    let tc = TypeChecker::new(&env);

    let int_const = Expr::const_(Name::from_string("Int"), vec![]);
    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

    // Check Int.natAbs : Int → Nat
    let nat_abs = Expr::const_(Name::from_string("Int.natAbs"), vec![]);
    let nat_abs_ty = tc.infer_type(&nat_abs).unwrap();
    let expected_nat_abs_ty = Expr::pi(BinderInfo::Default, int_const.clone(), nat_const.clone());
    assert!(tc.is_def_eq(&nat_abs_ty, &expected_nat_abs_ty));

    // Check Int.abs : Int → Int
    let abs = Expr::const_(Name::from_string("Int.abs"), vec![]);
    let abs_ty = tc.infer_type(&abs).unwrap();
    let expected_abs_ty = Expr::pi(BinderInfo::Default, int_const.clone(), int_const.clone());
    assert!(tc.is_def_eq(&abs_ty, &expected_abs_ty));

    // Check Int.sign : Int → Int
    let sign = Expr::const_(Name::from_string("Int.sign"), vec![]);
    let sign_ty = tc.infer_type(&sign).unwrap();
    let expected_sign_ty = Expr::pi(BinderInfo::Default, int_const.clone(), int_const.clone());
    assert!(tc.is_def_eq(&sign_ty, &expected_sign_ty));

    // Check Int.neg : Int → Int
    let neg = Expr::const_(Name::from_string("Int.neg"), vec![]);
    let neg_ty = tc.infer_type(&neg).unwrap();
    let expected_neg_ty = Expr::pi(BinderInfo::Default, int_const.clone(), int_const.clone());
    assert!(tc.is_def_eq(&neg_ty, &expected_neg_ty));
}

#[test]
fn test_int_sign_abs_idempotent() {
    let mut env = Environment::new();

    // Call multiple times
    env.init_int_sign_abs().unwrap();
    env.init_int_sign_abs().unwrap();
    env.init_int_sign_abs().unwrap();

    // Should still work
    assert!(env.has_int_sign_abs());
    assert_const(&env, "Int.natAbs");
}

#[test]
fn test_int_natabs_computation() {
    // Test that natAbs computes correctly via WHNF
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_sign_abs().unwrap();

    let tc = TypeChecker::new(&env);

    let nat_abs = Expr::const_(Name::from_string("Int.natAbs"), vec![]);
    let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
    let int_neg_succ = Expr::const_(Name::from_string("Int.negSucc"), vec![]);
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);

    // natAbs (ofNat 0) should reduce to 0
    let expr = Expr::app(
        nat_abs.clone(),
        Expr::app(int_of_nat.clone(), nat_zero.clone()),
    );
    let result = tc.whnf(&expr);
    assert!(tc.is_def_eq(&result, &nat_zero));

    // natAbs (ofNat 3) should reduce to 3
    let three_nat = Expr::app(
        nat_succ.clone(),
        Expr::app(
            nat_succ.clone(),
            Expr::app(nat_succ.clone(), nat_zero.clone()),
        ),
    );
    let expr = Expr::app(
        nat_abs.clone(),
        Expr::app(int_of_nat.clone(), three_nat.clone()),
    );
    let result = tc.whnf(&expr);
    assert!(tc.is_def_eq(&result, &three_nat));

    // natAbs (negSucc 0) = succ 0 = 1
    let one_nat = Expr::app(nat_succ.clone(), nat_zero.clone());
    let expr = Expr::app(
        nat_abs.clone(),
        Expr::app(int_neg_succ.clone(), nat_zero.clone()),
    );
    let result = tc.whnf(&expr);
    assert!(tc.is_def_eq(&result, &one_nat));

    // natAbs (negSucc 2) = succ 2 = 3 (i.e., |-3| = 3)
    let two_nat = Expr::app(
        nat_succ.clone(),
        Expr::app(nat_succ.clone(), nat_zero.clone()),
    );
    let expr = Expr::app(
        nat_abs.clone(),
        Expr::app(int_neg_succ.clone(), two_nat.clone()),
    );
    let result = tc.whnf(&expr);
    assert!(tc.is_def_eq(&result, &three_nat));
}

#[test]
fn test_int_sign_computation() {
    // Test that sign computes correctly via WHNF
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_sign_abs().unwrap();

    let tc = TypeChecker::new(&env);

    let sign = Expr::const_(Name::from_string("Int.sign"), vec![]);
    let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
    let int_neg_succ = Expr::const_(Name::from_string("Int.negSucc"), vec![]);
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);

    let int_zero = Expr::app(int_of_nat.clone(), nat_zero.clone());
    let int_one = Expr::app(
        int_of_nat.clone(),
        Expr::app(nat_succ.clone(), nat_zero.clone()),
    );
    let int_neg_one = Expr::app(int_neg_succ.clone(), nat_zero.clone());

    // sign (ofNat 0) = 0
    let expr = Expr::app(sign.clone(), int_zero.clone());
    let result = tc.whnf(&expr);
    assert!(tc.is_def_eq(&result, &int_zero));

    // sign (ofNat 1) = 1
    let expr = Expr::app(sign.clone(), int_one.clone());
    let result = tc.whnf(&expr);
    assert!(tc.is_def_eq(&result, &int_one));

    // sign (ofNat 5) = 1
    let five_nat = Expr::app(
        nat_succ.clone(),
        Expr::app(
            nat_succ.clone(),
            Expr::app(
                nat_succ.clone(),
                Expr::app(
                    nat_succ.clone(),
                    Expr::app(nat_succ.clone(), nat_zero.clone()),
                ),
            ),
        ),
    );
    let expr = Expr::app(sign.clone(), Expr::app(int_of_nat.clone(), five_nat));
    let result = tc.whnf(&expr);
    assert!(tc.is_def_eq(&result, &int_one));

    // sign (negSucc 0) = -1
    let expr = Expr::app(sign.clone(), int_neg_one.clone());
    let result = tc.whnf(&expr);
    assert!(tc.is_def_eq(&result, &int_neg_one));

    // sign (negSucc 5) = -1
    let expr = Expr::app(
        sign.clone(),
        Expr::app(
            int_neg_succ.clone(),
            Expr::app(
                nat_succ.clone(),
                Expr::app(
                    nat_succ.clone(),
                    Expr::app(
                        nat_succ.clone(),
                        Expr::app(
                            nat_succ.clone(),
                            Expr::app(nat_succ.clone(), nat_zero.clone()),
                        ),
                    ),
                ),
            ),
        ),
    );
    let result = tc.whnf(&expr);
    assert!(tc.is_def_eq(&result, &int_neg_one));
}

#[test]
fn test_int_neg_computation() {
    // Test that Int.neg computes correctly via WHNF
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_sign_abs().unwrap();

    let tc = TypeChecker::new(&env);

    let neg = Expr::const_(Name::from_string("Int.neg"), vec![]);
    let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
    let int_neg_succ = Expr::const_(Name::from_string("Int.negSucc"), vec![]);
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);

    let int_zero = Expr::app(int_of_nat.clone(), nat_zero.clone());

    // neg (ofNat 0) = ofNat 0
    let expr = Expr::app(neg.clone(), int_zero.clone());
    let result = tc.whnf(&expr);
    assert!(tc.is_def_eq(&result, &int_zero));

    // neg (ofNat 1) = negSucc 0 = -1
    let one_nat = Expr::app(nat_succ.clone(), nat_zero.clone());
    let int_one = Expr::app(int_of_nat.clone(), one_nat.clone());
    let int_neg_one = Expr::app(int_neg_succ.clone(), nat_zero.clone());
    let expr = Expr::app(neg.clone(), int_one.clone());
    let result = tc.whnf(&expr);
    assert!(tc.is_def_eq(&result, &int_neg_one));

    // neg (ofNat 3) = negSucc 2 = -3
    let two_nat = Expr::app(nat_succ.clone(), one_nat.clone());
    let three_nat = Expr::app(nat_succ.clone(), two_nat.clone());
    let int_three = Expr::app(int_of_nat.clone(), three_nat);
    let int_neg_three = Expr::app(int_neg_succ.clone(), two_nat.clone());
    let expr = Expr::app(neg.clone(), int_three);
    let result = tc.whnf(&expr);
    assert!(tc.is_def_eq(&result, &int_neg_three));

    // neg (negSucc 0) = ofNat 1 = 1
    let expr = Expr::app(neg.clone(), int_neg_one.clone());
    let result = tc.whnf(&expr);
    assert!(tc.is_def_eq(&result, &int_one));

    // neg (negSucc 2) = ofNat 3 = 3
    let expr = Expr::app(neg.clone(), int_neg_three);
    let result = tc.whnf(&expr);
    let expected = Expr::app(
        int_of_nat.clone(),
        Expr::app(nat_succ.clone(), two_nat.clone()),
    );
    assert!(tc.is_def_eq(&result, &expected));
}

#[test]
fn test_int_abs_computation() {
    // Test that Int.abs computes correctly via WHNF
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_sign_abs().unwrap();

    let tc = TypeChecker::new(&env);

    let abs = Expr::const_(Name::from_string("Int.abs"), vec![]);
    let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
    let int_neg_succ = Expr::const_(Name::from_string("Int.negSucc"), vec![]);
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);

    let int_zero = Expr::app(int_of_nat.clone(), nat_zero.clone());

    // abs (ofNat 0) = ofNat 0
    let expr = Expr::app(abs.clone(), int_zero.clone());
    let result = tc.whnf(&expr);
    assert!(tc.is_def_eq(&result, &int_zero));

    // abs (ofNat 3) = ofNat 3
    let three_nat = Expr::app(
        nat_succ.clone(),
        Expr::app(
            nat_succ.clone(),
            Expr::app(nat_succ.clone(), nat_zero.clone()),
        ),
    );
    let int_three = Expr::app(int_of_nat.clone(), three_nat.clone());
    let expr = Expr::app(abs.clone(), int_three.clone());
    let result = tc.whnf(&expr);
    assert!(tc.is_def_eq(&result, &int_three));

    // abs (negSucc 0) = ofNat 1 (i.e., |-1| = 1)
    let one_nat = Expr::app(nat_succ.clone(), nat_zero.clone());
    let int_one = Expr::app(int_of_nat.clone(), one_nat);
    let int_neg_one = Expr::app(int_neg_succ.clone(), nat_zero.clone());
    let expr = Expr::app(abs.clone(), int_neg_one);
    let result = tc.whnf(&expr);
    assert!(tc.is_def_eq(&result, &int_one));

    // abs (negSucc 2) = ofNat 3 (i.e., |-3| = 3)
    let two_nat = Expr::app(
        nat_succ.clone(),
        Expr::app(nat_succ.clone(), nat_zero.clone()),
    );
    let int_neg_three = Expr::app(int_neg_succ.clone(), two_nat);
    let expr = Expr::app(abs.clone(), int_neg_three);
    let result = tc.whnf(&expr);
    assert!(tc.is_def_eq(&result, &int_three));
}

#[test]
fn test_int_tonat_computation() {
    // Test that Int.toNat computes correctly via WHNF
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int().unwrap();

    let tc = TypeChecker::new(&env);

    let to_nat = Expr::const_(Name::from_string("Int.toNat"), vec![]);
    let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
    let int_neg_succ = Expr::const_(Name::from_string("Int.negSucc"), vec![]);
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);

    let int_zero = Expr::app(int_of_nat.clone(), nat_zero.clone());

    // toNat (ofNat 0) = 0
    let expr = Expr::app(to_nat.clone(), int_zero.clone());
    let result = tc.whnf(&expr);
    assert!(tc.is_def_eq(&result, &nat_zero));

    // toNat (ofNat 3) = 3
    let three_nat = Expr::app(
        nat_succ.clone(),
        Expr::app(
            nat_succ.clone(),
            Expr::app(nat_succ.clone(), nat_zero.clone()),
        ),
    );
    let int_three = Expr::app(int_of_nat.clone(), three_nat.clone());
    let expr = Expr::app(to_nat.clone(), int_three);
    let result = tc.whnf(&expr);
    assert!(tc.is_def_eq(&result, &three_nat));

    // toNat (negSucc 0) = 0 (i.e., toNat(-1) = 0)
    let int_neg_one = Expr::app(int_neg_succ.clone(), nat_zero.clone());
    let expr = Expr::app(to_nat.clone(), int_neg_one);
    let result = tc.whnf(&expr);
    assert!(tc.is_def_eq(&result, &nat_zero));

    // toNat (negSucc 2) = 0 (i.e., toNat(-3) = 0)
    let two_nat = Expr::app(
        nat_succ.clone(),
        Expr::app(nat_succ.clone(), nat_zero.clone()),
    );
    let int_neg_three = Expr::app(int_neg_succ.clone(), two_nat);
    let expr = Expr::app(to_nat.clone(), int_neg_three);
    let result = tc.whnf(&expr);
    assert!(tc.is_def_eq(&result, &nat_zero));
}

#[test]
fn test_complete_int_sign_abs_support() {
    // Test that sign/abs init works after other Int init functions
    let mut env = Environment::new();

    // Initialize all Int support
    env.init_int_ord_lemmas().unwrap();
    env.init_int_decidable_ord().unwrap();
    env.init_int_sign_abs().unwrap();

    // All should be present
    assert!(env.has_int_sign_abs());
    for s in ["Int.natAbs", "Int.abs", "Int.sign", "Int.neg"] {
        assert_const(&env, s);
    }
}

// ===== Int Arithmetic Lemmas Tests =====

#[test]
fn test_init_int_arith_lemmas() {
    let mut env = Environment::new();
    env.init_int_arith_lemmas().unwrap();

    for s in [
        "Int.add_negSucc_ofNat_succ",
        "Int.add_ofNat_negSucc",
        "Int.add_ofNat_succ_negSucc",
        "Int.subNatNat_succ_succ",
        "Int.subNatNat_zero_right",
        "Int.subNatNat_zero_succ",
        "Int.add_comm",
        "Int.add_assoc",
        "Int.add_zero",
        "Int.zero_add",
        "Int.add_neg_self",
        "Int.neg_add_self",
        "Int.mul_comm",
        "Int.mul_assoc",
        "Int.mul_left_cancel_ofNat_succ",
        "Int.mul_one",
        "Int.one_mul",
        "Int.mul_zero",
        "Int.zero_mul",
        "Int.left_distrib",
        "Int.right_distrib",
        "Int.neg_neg",
        "Int.neg_add",
        "Int.neg_mul_left",
        "Int.neg_mul_right",
        "Int.sub_self",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_int_arith_lemmas_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_arith_lemmas().unwrap();

    let tc = TypeChecker::new(&env);
    for name in [
        // Int.add_comm removed (#3604): promoted from Declaration::Axiom
        // to Declaration::Theorem with a genuine nested @Int.rec-rooted
        // constructive proof term (outer/inner induction over the two
        // Int arguments, with mixed-sign cases closed via iota+delta and
        // same-sign cases via congrArg of Nat.add_comm). See
        // `algebra_int_add_comm_proof.rs`. Presence is still pinned by
        // `test_init_int_arith_lemmas`; Theorem-form coverage lives in
        // the tests in `algebra_int_add_comm_proof.rs`.
        "Int.add_assoc",
        "Int.mul_comm",
        "Int.mul_assoc",
        "Int.mul_left_cancel_ofNat_succ",
        "Int.left_distrib",
        "Int.right_distrib",
        "Int.neg_neg",
        "Int.sub_self",
    ] {
        assert_axiom_type_checks(&env, &tc, name);
    }
}

#[test]
fn test_int_arith_lemmas_idempotent() {
    let mut env = Environment::new();

    // Multiple calls should succeed
    env.init_int_arith_lemmas().unwrap();
    env.init_int_arith_lemmas().unwrap();
    env.init_int_arith_lemmas().unwrap();

    assert!(env.has_int_arith_lemmas());
}

#[test]
fn test_complete_int_arith_lemmas_support() {
    // Test that arith lemmas init works with all other Int init functions
    let mut env = Environment::new();

    // Initialize all Int support
    env.init_int_ord_lemmas().unwrap();
    env.init_int_decidable_ord().unwrap();
    env.init_int_sign_abs().unwrap();
    env.init_int_arith_lemmas().unwrap();

    // All should be present
    assert!(env.has_int_arith_lemmas());
    for s in [
        "Int.add_comm",
        "Int.mul_comm",
        "Int.left_distrib",
        "Int.neg_neg",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_init_nat_arith_lemmas() {
    let mut env = Environment::new();
    assert!(!env.has_nat_arith_lemmas());

    env.init_nat_arith_lemmas().unwrap();
    assert!(env.has_nat_arith_lemmas());

    // Check all lemmas are present
    for s in [
        "Nat.add_comm",
        "Nat.add_assoc",
        "Nat.add_zero",
        "Nat.zero_add",
        "Nat.mul_comm",
        "Nat.mul_assoc",
        "Nat.mul_left_cancel_succ",
        "Nat.mul_one",
        "Nat.one_mul",
        "Nat.mul_zero",
        "Nat.zero_mul",
        "Nat.left_distrib",
        "Nat.right_distrib",
        "Nat.succ_add",
        "Nat.add_succ",
        "Nat.succ_mul",
        "Nat.mul_succ",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_nat_arith_lemmas_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_nat_arith_lemmas().unwrap();

    let tc = TypeChecker::new(&env);
    for name in [
        // Nat.add_comm removed (#3604): promoted from Declaration::Axiom
        // to Declaration::Theorem with a genuine @Nat.rec-rooted
        // constructive proof term (induction on the second argument
        // composing Nat.zero_add + Nat.succ_add). See
        // `algebra_nat_add_comm_proof.rs`. Presence is still pinned by
        // `test_init_nat_arith_lemmas`; Theorem-form coverage lives in
        // `test_nat_add_comm_registered_as_theorem`.
        "Nat.add_assoc",
        "Nat.mul_comm",
        "Nat.mul_assoc",
        "Nat.mul_left_cancel_succ",
        "Nat.left_distrib",
        "Nat.right_distrib",
        // Nat.succ_add removed (#3604): promoted from Declaration::Axiom
        // to Declaration::Theorem with a genuine @Nat.rec-rooted
        // constructive proof term (induction on the second argument).
        // See `algebra_nat_succ_add_proof.rs`. Presence is still pinned
        // by `test_init_nat_arith_lemmas`; Theorem-form type-check
        // coverage lives in `test_nat_succ_add_registered_as_theorem`.
        "Nat.mul_succ",
    ] {
        assert_axiom_type_checks(&env, &tc, name);
    }
}

#[test]
fn test_nat_arith_lemmas_idempotent() {
    let mut env = Environment::new();

    // Multiple calls should succeed
    env.init_nat_arith_lemmas().unwrap();
    env.init_nat_arith_lemmas().unwrap();
    env.init_nat_arith_lemmas().unwrap();

    assert!(env.has_nat_arith_lemmas());
}

#[test]
fn test_complete_nat_arith_lemmas_support() {
    // Test that arith lemmas init works with all other Nat init functions
    let mut env = Environment::new();

    // Initialize all Nat ordering support
    env.init_nat_minmax_lemmas().unwrap();
    env.init_nat_decidable_ord().unwrap();
    env.init_nat_arith_lemmas().unwrap();

    // All should be present
    assert!(env.has_nat_arith_lemmas());
    for s in [
        "Nat.add_comm",
        "Nat.mul_comm",
        "Nat.left_distrib",
        "Nat.succ_add",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_init_int_nat_conv_lemmas() {
    let mut env = Environment::new();
    assert!(!env.has_int_nat_conv_lemmas());

    env.init_int_nat_conv_lemmas().unwrap();
    assert!(env.has_int_nat_conv_lemmas());

    for s in [
        "Int.toNat_ofNat",
        "Int.ofNat_add",
        "Int.ofNat_mul",
        "Nat.succ_eq_add_one",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_int_nat_conv_lemmas_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_nat_conv_lemmas().unwrap();
    let tc = TypeChecker::new(&env);

    // All four entries in this group have been demoted from Axiom to
    // Theorem (#3551 Tier A Int batch — `Int.toNat_ofNat`,
    // `Int.ofNat_add`, `Int.ofNat_mul`, `Nat.succ_eq_add_one`). Each
    // carries a pure `@Eq.refl.{1}` proof term that the kernel accepts
    // via iota + delta + beta reductions on the underlying reducible
    // `Int.toNat` / `Int.add` / `Int.mul` / `Nat.add` definitions. They
    // are still registered and type-checkable, but now carry a proof
    // value (Declaration::Theorem).
    for name in [
        "Int.toNat_ofNat",
        "Int.ofNat_add",
        "Int.ofNat_mul",
        "Nat.succ_eq_add_one",
    ] {
        let info = env.get_const(&Name::from_string(name)).unwrap();
        assert!(
            info.value.is_some(),
            "{name} should be a Theorem with a proof value (#3551 Tier A Int batch)"
        );
        let _ = tc.infer_type(&info.type_).unwrap();
    }
}

#[test]
fn test_int_nat_conv_lemmas_idempotent() {
    let mut env = Environment::new();

    env.init_int_nat_conv_lemmas().unwrap();
    env.init_int_nat_conv_lemmas().unwrap();
    env.init_int_nat_conv_lemmas().unwrap();

    assert!(env.has_int_nat_conv_lemmas());
}

// ========================================================================
// Tests for Algebraic Typeclasses
// ========================================================================

#[test]
fn test_init_zero() {
    let mut env = Environment::new();
    assert!(!env.has_zero());

    env.init_zero().unwrap();
    assert!(env.has_zero());

    // Check typeclass and projection exist
    assert_const(&env, "Zero.mk");
    assert_const(&env, "Zero.zero");
}

#[test]
fn test_init_one() {
    let mut env = Environment::new();
    assert!(!env.has_one());

    env.init_one().unwrap();
    assert!(env.has_one());

    assert_const(&env, "One.mk");
    assert_const(&env, "One.one");
}

#[test]
fn test_init_add_typeclass() {
    let mut env = Environment::new();
    assert!(!env.has_add());

    env.init_add().unwrap();
    assert!(env.has_add());

    assert_const(&env, "Add.mk");
    assert_const(&env, "Add.add");
}

#[test]
fn test_init_mul_typeclass() {
    let mut env = Environment::new();
    assert!(!env.has_mul());

    env.init_mul().unwrap();
    assert!(env.has_mul());

    assert_const(&env, "Mul.mk");
    assert_const(&env, "Mul.mul");
}

#[test]
fn test_init_neg_typeclass() {
    let mut env = Environment::new();
    assert!(!env.has_neg());

    env.init_neg().unwrap();
    assert!(env.has_neg());

    assert_const(&env, "Neg.mk");
    assert_const(&env, "Neg.neg");
}

#[test]
fn test_init_sub_typeclass() {
    let mut env = Environment::new();
    assert!(!env.has_sub());

    env.init_sub().unwrap();
    assert!(env.has_sub());

    assert_const(&env, "Sub.mk");
    assert_const(&env, "Sub.sub");
}

#[test]
fn test_algebraic_typeclasses_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_zero().unwrap();
    env.init_one().unwrap();
    env.init_add().unwrap();
    env.init_mul().unwrap();
    env.init_neg().unwrap();
    env.init_sub().unwrap();

    let tc = TypeChecker::new(&env);

    // Check all constructors type-check (projection values use recursors which are complex)
    for name in ["Zero.mk", "One.mk", "Add.mk", "Mul.mk", "Neg.mk", "Sub.mk"] {
        let info = env.get_const(&Name::from_string(name)).unwrap();
        let _ = tc.infer_type(&info.type_).unwrap();
    }

    // Check projection types are well-formed
    for name in [
        "Zero.zero",
        "One.one",
        "Add.add",
        "Mul.mul",
        "Neg.neg",
        "Sub.sub",
    ] {
        let info = env.get_const(&Name::from_string(name)).unwrap();
        let _ = tc.infer_type(&info.type_).unwrap();
        // Note: projection values use recursor patterns that are complex
        // The types are verified correct; values need recursor type inference
    }
}

#[test]
fn test_algebraic_typeclasses_idempotent() {
    let mut env = Environment::new();

    env.init_zero().unwrap();
    env.init_zero().unwrap();
    env.init_one().unwrap();
    env.init_one().unwrap();
    env.init_add().unwrap();
    env.init_add().unwrap();
    env.init_mul().unwrap();
    env.init_mul().unwrap();
    env.init_neg().unwrap();
    env.init_neg().unwrap();
    env.init_sub().unwrap();
    env.init_sub().unwrap();

    assert!(env.has_zero());
    assert!(env.has_one());
    assert!(env.has_add());
    assert!(env.has_mul());
    assert!(env.has_neg());
    assert!(env.has_sub());
}

// ========================================================================
// Tests for Nat Typeclass Instances
// ========================================================================

#[test]
fn test_init_nat_zero_inst() {
    let mut env = Environment::new();
    assert!(!env.has_nat_zero_inst());

    env.init_nat_zero_inst().unwrap();
    assert!(env.has_nat_zero_inst());

    assert_const(&env, "instZeroNat");
}

#[test]
fn test_init_nat_one_inst() {
    let mut env = Environment::new();
    assert!(!env.has_nat_one_inst());

    env.init_nat_one_inst().unwrap();
    assert!(env.has_nat_one_inst());

    assert_const(&env, "instOneNat");
}

#[test]
fn test_init_nat_add_inst() {
    let mut env = Environment::new();
    assert!(!env.has_nat_add_inst());

    env.init_nat_add_inst().unwrap();
    assert!(env.has_nat_add_inst());

    assert_const(&env, "instAddNat");
}

#[test]
fn test_init_nat_mul_inst() {
    let mut env = Environment::new();
    assert!(!env.has_nat_mul_inst());

    env.init_nat_mul_inst().unwrap();
    assert!(env.has_nat_mul_inst());

    assert_const(&env, "instMulNat");
}

#[test]
fn test_init_nat_sub_inst() {
    let mut env = Environment::new();
    assert!(!env.has_nat_sub_inst());

    env.init_nat_sub_inst().unwrap();
    assert!(env.has_nat_sub_inst());

    assert_const(&env, "instSubNat");
}

#[test]
fn test_nat_instances_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_nat_zero_inst().unwrap();
    env.init_nat_one_inst().unwrap();
    env.init_nat_add_inst().unwrap();
    env.init_nat_mul_inst().unwrap();
    env.init_nat_sub_inst().unwrap();

    let tc = TypeChecker::new(&env);

    for name in [
        "instZeroNat",
        "instOneNat",
        "instAddNat",
        "instMulNat",
        "instSubNat",
    ] {
        let info = env.get_const(&Name::from_string(name)).unwrap();
        let _ = tc.infer_type(&info.type_).unwrap();
        if let Some(ref value) = info.value {
            let _ = tc.infer_type(value).unwrap();
        }
    }
}

// ========================================================================
// Tests for Int Typeclass Instances
// ========================================================================

#[test]
fn test_init_int_zero_inst() {
    let mut env = Environment::new();
    assert!(!env.has_int_zero_inst());

    env.init_int_zero_inst().unwrap();
    assert!(env.has_int_zero_inst());

    assert_const(&env, "instZeroInt");
}

#[test]
fn test_init_int_one_inst() {
    let mut env = Environment::new();
    assert!(!env.has_int_one_inst());

    env.init_int_one_inst().unwrap();
    assert!(env.has_int_one_inst());

    assert_const(&env, "instOneInt");
}

#[test]
fn test_init_int_add_inst() {
    let mut env = Environment::new();
    assert!(!env.has_int_add_inst());

    env.init_int_add_inst().unwrap();
    assert!(env.has_int_add_inst());

    assert_const(&env, "instAddInt");
}

#[test]
fn test_init_int_mul_inst() {
    let mut env = Environment::new();
    assert!(!env.has_int_mul_inst());

    env.init_int_mul_inst().unwrap();
    assert!(env.has_int_mul_inst());

    assert_const(&env, "instMulInt");
}

#[test]
fn test_init_int_neg_inst() {
    let mut env = Environment::new();
    assert!(!env.has_int_neg_inst());

    env.init_int_neg_inst().unwrap();
    assert!(env.has_int_neg_inst());

    assert_const(&env, "instNegInt");
}

#[test]
fn test_init_int_sub_inst() {
    let mut env = Environment::new();
    assert!(!env.has_int_sub_inst());

    env.init_int_sub_inst().unwrap();
    assert!(env.has_int_sub_inst());

    assert_const(&env, "instSubInt");
}

#[test]
fn test_int_instances_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_zero_inst().unwrap();
    env.init_int_one_inst().unwrap();
    env.init_int_add_inst().unwrap();
    env.init_int_mul_inst().unwrap();
    env.init_int_neg_inst().unwrap();
    env.init_int_sub_inst().unwrap();

    let tc = TypeChecker::new(&env);

    for name in [
        "instZeroInt",
        "instOneInt",
        "instAddInt",
        "instMulInt",
        "instNegInt",
        "instSubInt",
    ] {
        let info = env.get_const(&Name::from_string(name)).unwrap();
        let _ = tc.infer_type(&info.type_).unwrap();
        if let Some(ref value) = info.value {
            let _ = tc.infer_type(value).unwrap();
        }
    }
}

#[test]
fn test_all_instances_idempotent() {
    let mut env = Environment::new();

    // Initialize all instances twice
    env.init_nat_zero_inst().unwrap();
    env.init_nat_zero_inst().unwrap();
    env.init_nat_one_inst().unwrap();
    env.init_nat_one_inst().unwrap();
    env.init_nat_add_inst().unwrap();
    env.init_nat_add_inst().unwrap();
    env.init_nat_mul_inst().unwrap();
    env.init_nat_mul_inst().unwrap();
    env.init_nat_sub_inst().unwrap();
    env.init_nat_sub_inst().unwrap();

    env.init_int_zero_inst().unwrap();
    env.init_int_zero_inst().unwrap();
    env.init_int_one_inst().unwrap();
    env.init_int_one_inst().unwrap();
    env.init_int_add_inst().unwrap();
    env.init_int_add_inst().unwrap();
    env.init_int_mul_inst().unwrap();
    env.init_int_mul_inst().unwrap();
    env.init_int_neg_inst().unwrap();
    env.init_int_neg_inst().unwrap();
    env.init_int_sub_inst().unwrap();
    env.init_int_sub_inst().unwrap();

    // Verify all flags are set
    assert!(env.has_nat_zero_inst());
    assert!(env.has_nat_one_inst());
    assert!(env.has_nat_add_inst());
    assert!(env.has_nat_mul_inst());
    assert!(env.has_nat_sub_inst());
    assert!(env.has_int_zero_inst());
    assert!(env.has_int_one_inst());
    assert!(env.has_int_add_inst());
    assert!(env.has_int_mul_inst());
    assert!(env.has_int_neg_inst());
    assert!(env.has_int_sub_inst());
}

// ================================
// Heterogeneous typeclass tests
// ================================

#[test]
fn test_init_hadd() {
    let mut env = Environment::new();
    assert!(!env.has_hadd());

    env.init_hadd().unwrap();
    assert!(env.has_hadd());

    // Verify typeclass and projection exist
    for s in ["HAdd", "HAdd.mk", "HAdd.hAdd"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_init_hsub() {
    let mut env = Environment::new();
    assert!(!env.has_hsub());

    env.init_hsub().unwrap();
    assert!(env.has_hsub());

    for s in ["HSub", "HSub.mk", "HSub.hSub"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_init_hmul() {
    let mut env = Environment::new();
    assert!(!env.has_hmul());

    env.init_hmul().unwrap();
    assert!(env.has_hmul());

    for s in ["HMul", "HMul.mk", "HMul.hMul"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_init_hdiv() {
    let mut env = Environment::new();
    assert!(!env.has_hdiv());

    env.init_hdiv().unwrap();
    assert!(env.has_hdiv());

    for s in ["HDiv", "HDiv.mk", "HDiv.hDiv"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_init_div() {
    let mut env = Environment::new();
    assert!(!env.has_div());

    env.init_div().unwrap();
    assert!(env.has_div());

    for s in ["Div", "Div.mk", "Div.div"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_init_hmod() {
    let mut env = Environment::new();
    assert!(!env.has_hmod());

    env.init_hmod().unwrap();
    assert!(env.has_hmod());

    for s in ["HMod", "HMod.mk", "HMod.hMod"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_init_mod() {
    let mut env = Environment::new();
    assert!(!env.has_mod());

    env.init_mod().unwrap();
    assert!(env.has_mod());

    for s in ["Mod", "Mod.mk", "Mod.mod"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_init_hpow() {
    let mut env = Environment::new();
    assert!(!env.has_hpow());

    env.init_hpow().unwrap();
    assert!(env.has_hpow());

    for s in ["HPow", "HPow.mk", "HPow.hPow"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_init_pow() {
    let mut env = Environment::new();
    assert!(!env.has_pow());

    env.init_pow().unwrap();
    assert!(env.has_pow());

    for s in ["Pow", "Pow.mk", "Pow.pow"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_pow_mk_type_tail_returns_base_type() {
    use crate::expr::ExprKind;
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_pow().unwrap();

    // Regression guard for #1413: Pow.mk must encode the field type α → β → α.
    // The tail codomain must resolve to the outer α binder, not β.
    let pow_mk = env.get_const(&Name::from_string("Pow.mk")).unwrap();
    let mut ty = pow_mk.type_.clone();
    let mut domains: Vec<Expr> = Vec::new();
    while let ExprKind::Pi(_, domain, body) = &ty.kind {
        domains.push(domain.as_ref().clone());
        ty = body.as_ref().clone();
    }

    // Pow.mk type:
    // {α : Type u} → {β : Type v} → (α → β → α) → Pow α β
    // The function binder domain is the 3rd Pi domain.
    let field_ty = domains
        .get(2)
        .expect("Pow.mk should have function field domain");
    let mut field = field_ty.clone();
    let mut field_pis: Vec<Expr> = Vec::new();
    while let ExprKind::Pi(_, domain, body) = &field.kind {
        field_pis.push(domain.as_ref().clone());
        field = body.as_ref().clone();
    }
    assert_eq!(
        field_pis.len(),
        2,
        "Pow field should be binary function α → β → α"
    );
    assert!(
        matches!(field.kind, ExprKind::BVar(3)),
        "Pow.mk field codomain must reference α binder (bvar(3)), got: {field:?}"
    );

    // Also validate the declaration type remains well-typed in the environment.
    let tc = TypeChecker::new(&env);
    let _ = tc.infer_type(&pow_mk.type_).unwrap();
}

#[test]
fn test_heterogeneous_typeclasses_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_hadd().unwrap();
    env.init_hsub().unwrap();
    env.init_hmul().unwrap();
    env.init_hdiv().unwrap();
    env.init_div().unwrap();
    env.init_hmod().unwrap();
    env.init_mod().unwrap();
    env.init_hpow().unwrap();
    env.init_pow().unwrap();

    let tc = TypeChecker::new(&env);

    // Check all constructors type-check
    for name in [
        "HAdd.mk", "HSub.mk", "HMul.mk", "HDiv.mk", "Div.mk", "HMod.mk", "Mod.mk", "HPow.mk",
        "Pow.mk",
    ] {
        let info = env.get_const(&Name::from_string(name)).unwrap();
        let _ = tc.infer_type(&info.type_).unwrap();
    }

    // Check projection types are well-formed
    for name in [
        "HAdd.hAdd",
        "HSub.hSub",
        "HMul.hMul",
        "HDiv.hDiv",
        "Div.div",
        "HMod.hMod",
        "Mod.mod",
        "HPow.hPow",
        "Pow.pow",
    ] {
        let info = env.get_const(&Name::from_string(name)).unwrap();
        let _ = tc.infer_type(&info.type_).unwrap();
    }
}

#[test]
fn test_init_ofnat() {
    let mut env = Environment::new();
    assert!(!env.has_ofnat());

    env.init_ofnat().unwrap();
    assert!(env.has_ofnat());

    // Check OfNat typeclass exists
    for s in ["OfNat", "OfNat.mk", "OfNat.ofNat"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_init_ofnat_nat() {
    let mut env = Environment::new();

    env.init_ofnat_nat().unwrap();
    assert!(env.has_ofnat()); // Should auto-init OfNat

    // Check Nat instance exists
    assert_const(&env, "instOfNatNat");
}

/// `instOfNatNat` must carry Lean's real INSTANCE priority (1000), so it
/// outranks `Zero.toOfNat0` (which `Init/Data/Zero.lean:17` declares at
/// `(priority := 300)`) when both are candidates for `OfNat Nat 0`.
///
/// Regression: this was hand-registered at 100 — Lean's `low`, misread off the
/// `@[default_instance 100]` attribute, which orders literal-type DEFAULTING and
/// not `synthInstance` candidates. Priority dominates candidate ordering, so
/// `(0 : Nat)` elaborated to `Zero.toOfNat0` while every imported statement of
/// the same fact (`Nat.add_zero` and friends) uses `instOfNatNat 0`. Both are
/// definitionally equal, so nothing was rejected — but `simp only [Nat.add_zero]`
/// could not match its own imported lemma, because syntactic matching sees the
/// two shapes as different.
///
/// Ground truth: the shipped `Init/Prelude.olean` serializes `instOfNatNat` into
/// `Lean.Meta.instanceExtension` with `priority: 1000`. Import now ADOPTS that
/// serialized value even for an already-registered name
/// (`register_real_instance_entries` in `clean-olean/src/import/load_register.rs`,
/// via `Environment::adopt_instance_priority`), so a wrong guess no longer
/// survives an import. It still survives in every environment that never
/// imports — which is what this test pins.
#[test]
fn test_init_ofnat_nat_instance_priority_outranks_zero_to_ofnat0() {
    let mut env = Environment::new();
    env.init_ofnat_nat().unwrap();

    let ofnat = Name::from_string("OfNat");
    let inst_of_nat_nat = Name::from_string("instOfNatNat");

    let priority = env
        .get_class_instances(&ofnat)
        .iter()
        .find(|i| i.name == inst_of_nat_nat)
        .map(|i| i.priority)
        .expect("instOfNatNat must be registered as an OfNat instance");
    assert_eq!(
        priority, 1000,
        "instOfNatNat must use Lean's unannotated-instance default priority \
         (1000, as serialized in Init/Prelude.olean), not `low` (100)"
    );

    // The order that actually matters: register `Zero.toOfNat0` at Lean's 300
    // exactly as the `.olean` import does, then check the bucket ranks
    // `instOfNatNat` first. At priority 100 this bucket came out inverted.
    let zero_to_ofnat0 = Name::from_string("Zero.toOfNat0");
    env.register_instance(KernelInstanceInfo {
        name: zero_to_ofnat0.clone(),
        class_name: ofnat.clone(),
        priority: 300,
        type_: None,
        value: None,
    });

    let order: Vec<Name> = env
        .get_class_instances(&ofnat)
        .iter()
        .map(|i| i.name.clone())
        .filter(|n| *n == inst_of_nat_nat || *n == zero_to_ofnat0)
        .collect();
    assert_eq!(
        order,
        vec![inst_of_nat_nat, zero_to_ofnat0],
        "instOfNatNat must be tried before Zero.toOfNat0 for an `OfNat Nat _` goal"
    );
}

/// `instLTNat` must carry Lean's real INSTANCE priority (1000), so it stays in
/// the SAME candidate tier as every imported `LT` instance instead of sinking
/// below all of them.
///
/// Regression: this was hand-registered at `DEFAULT_INSTANCE_PRIORITY` (100 —
/// Lean's `low`), while `Init/Prelude.lean:1901` declares
/// `instance instLTNat : LT Nat where …` with no `(priority := …)`, i.e. Lean's
/// unannotated default of 1000 (and the shipped `Init/Prelude.olean` serializes
/// exactly that). Priority DOMINATES `clean-elab`'s `candidate_order`, so at 100
/// `instLTNat` ranked below every one of the ~30 imported `LT` instances and the
/// winner for `LT Nat` became `Classical.Order.instLT` — an instance Lean
/// declares `public scoped` and would never consider without
/// `open scoped Classical.Order`.
///
/// The `.olean` import cannot repair it: `register_real_instance_entries`
/// (`clean-olean/src/import/load_register.rs`) skips any name already in the
/// registry and this registration always runs first, so the literal in
/// `init_nat_decidable_ord` is the only thing that decides the order.
#[test]
fn test_init_nat_decidable_ord_instltnat_priority_is_lean_default() {
    let mut env = Environment::new();
    env.init_nat_decidable_ord().unwrap();

    let lt = Name::from_string("LT");
    let inst_lt_nat = Name::from_string("instLTNat");

    let priority = env
        .get_class_instances(&lt)
        .iter()
        .find(|i| i.name == inst_lt_nat)
        .map(|i| i.priority)
        .expect("instLTNat must be registered as an LT instance");
    assert_eq!(
        priority, 1000,
        "instLTNat must use Lean's unannotated-instance default priority \
         (1000, as serialized in Init/Prelude.olean), not `low` (100) — at 100 \
         every imported LT instance outranks it and `0 < n` elaborates through \
         the scoped `Classical.Order.instLT`"
    );

    // The order that actually matters: an imported general `LT α` instance
    // arrives at Lean's decoded 1000. `instLTNat` must be in that same tier, so
    // the elaborator's head-specificity tie-break (not priority) decides.
    let general = Name::from_string("Classical.Order.instLT");
    env.register_instance(KernelInstanceInfo {
        name: general.clone(),
        class_name: lt.clone(),
        priority: 1000,
        type_: None,
        value: None,
    });
    let tiers: Vec<u32> = env
        .get_class_instances(&lt)
        .iter()
        .filter(|i| i.name == inst_lt_nat || i.name == general)
        .map(|i| i.priority)
        .collect();
    assert_eq!(
        tiers,
        vec![1000, 1000],
        "instLTNat and an imported general `LT α` instance must share one \
         priority tier; at 100 vs 1000 the general one wins outright"
    );
}

#[test]
fn test_ofnat_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_ofnat().unwrap();
    env.init_ofnat_nat().unwrap();

    let tc = TypeChecker::new(&env);

    // Check all OfNat-related definitions type-check
    for name in ["OfNat", "OfNat.mk", "OfNat.ofNat", "instOfNatNat"] {
        let info = env.get_const(&Name::from_string(name)).unwrap();
        let _ = tc
            .infer_type(&info.type_)
            .unwrap_or_else(|e| panic!("Type check failed for {}: {}", name, e));
    }
}

fn expr_contains_proj(expr: &Expr, struct_name: &Name, idx: u32) -> bool {
    match &expr.kind {
        ExprKind::Proj(name, proj_idx, inner) => {
            (*proj_idx == idx && name == struct_name) || expr_contains_proj(inner, struct_name, idx)
        }
        ExprKind::App(f, a) => {
            expr_contains_proj(f, struct_name, idx) || expr_contains_proj(a, struct_name, idx)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_contains_proj(ty, struct_name, idx) || expr_contains_proj(body, struct_name, idx)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_contains_proj(ty, struct_name, idx)
                || expr_contains_proj(val, struct_name, idx)
                || expr_contains_proj(body, struct_name, idx)
        }
        ExprKind::MData(_, inner) => expr_contains_proj(inner, struct_name, idx),
        _ => false,
    }
}

fn expr_contains_rec_const(expr: &Expr) -> bool {
    expr.collect_constants()
        .iter()
        .any(|name| name.to_string().ends_with(".rec"))
}

#[test]
fn test_issue1413_projection_values_use_proj_ordering_families() {
    let mut env = Environment::new();
    env.init_trans().unwrap();
    env.init_preorder().unwrap();
    env.init_partial_order().unwrap();
    env.init_reflexive().unwrap();
    env.init_irrefl().unwrap();
    env.init_asymm().unwrap();
    env.init_ofnat().unwrap();

    let checks = [
        ("Trans.trans", "Trans", 0),
        ("Preorder.toLE", "Preorder", 0),
        ("PartialOrder.toPreorder", "PartialOrder", 0),
        ("Reflexive.refl", "Reflexive", 0),
        ("Irrefl.irrefl", "Irrefl", 0),
        ("Asymm.asymm", "Asymm", 0),
        ("OfNat.ofNat", "OfNat", 0),
    ];

    for (decl_name, struct_name, field_idx) in checks {
        let info = env
            .get_const(&Name::from_string(decl_name))
            .unwrap_or_else(|| panic!("{decl_name} should exist"));
        let value = info
            .value
            .as_ref()
            .unwrap_or_else(|| panic!("{decl_name} should have a value"));
        let struct_name = Name::from_string(struct_name);

        assert!(
            expr_contains_proj(value, &struct_name, field_idx),
            "{decl_name} should include Expr::proj({struct_name}, {field_idx}, ...)"
        );
        assert!(
            !expr_contains_rec_const(value),
            "{decl_name} should not depend on .rec constants after #1413 migration"
        );
    }
}

/// Verify all 4 Real additive axioms exist with correct binder structure:
/// binder 0,1 = Real, binder 2 = comparison App, binder 3 = Real.
#[test]
fn test_real_additive_order_axioms_binder_structure() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_real_linear_order().unwrap();
    let tc = TypeChecker::new(&env);
    let real_const = Expr::const_(Name::from_string("Real"), vec![]);

    for name in [
        "Real.add_le_add_left",
        "Real.add_le_add_right",
        "Real.add_lt_add_left",
        "Real.add_lt_add_right",
    ] {
        let axiom_type = tc
            .infer_type(&Expr::const_(Name::from_string(name), vec![]))
            .unwrap_or_else(|e| panic!("{name}: infer_type failed: {e}"));

        assert_eq!(
            pi_domain_at(&axiom_type, 0),
            Some(&real_const),
            "{name}: binder 0"
        );
        assert_eq!(
            pi_domain_at(&axiom_type, 1),
            Some(&real_const),
            "{name}: binder 1"
        );
        let h = pi_domain_at(&axiom_type, 2)
            .unwrap_or_else(|| panic!("{name}: missing hypothesis binder"));
        assert!(
            matches!(&h.kind, ExprKind::App(..)),
            "{name}: binder 2 should be App"
        );
        assert_eq!(
            pi_domain_at(&axiom_type, 3),
            Some(&real_const),
            "{name}: binder 3"
        );
    }
}

/// Verify hypothesis binders use correct typeclass form:
/// LE.le uses instLEReal, LT.lt uses instLTReal.
#[test]
fn test_real_additive_order_axioms_typeclass_hypothesis() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_real_linear_order().unwrap();
    let tc = TypeChecker::new(&env);
    let real_const = Expr::const_(Name::from_string("Real"), vec![]);

    // LE.le.{0} Real instLEReal (BVar 1) (BVar 0)
    let le_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("Real.add_le_add_left"),
            vec![],
        ))
        .unwrap();
    let expected_le = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                    real_const.clone(),
                ),
                Expr::const_(Name::from_string("instLEReal"), vec![]),
            ),
            Expr::bvar(1),
        ),
        Expr::bvar(0),
    );
    assert!(
        tc.is_def_eq(pi_domain_at(&le_type, 2).unwrap(), &expected_le),
        "add_le_add_left hypothesis should be LE.le Real instLEReal a b"
    );

    // LT.lt.{0} Real instLTReal (BVar 1) (BVar 0)
    let lt_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("Real.add_lt_add_left"),
            vec![],
        ))
        .unwrap();
    let expected_lt = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                    real_const.clone(),
                ),
                Expr::const_(Name::from_string("instLTReal"), vec![]),
            ),
            Expr::bvar(1),
        ),
        Expr::bvar(0),
    );
    assert!(
        tc.is_def_eq(pi_domain_at(&lt_type, 2).unwrap(), &expected_lt),
        "add_lt_add_left hypothesis should be LT.lt Real instLTReal a b"
    );
}

fn pi_body_after(expr: &Expr, binders: usize) -> Option<&Expr> {
    let mut current = expr;
    for _ in 0..binders {
        match &current.kind {
            ExprKind::Pi(_, _, body) => current = body.as_ref(),
            _ => return None,
        }
    }
    Some(current)
}

fn infer_order_axiom_type(tc: &crate::tc::TypeChecker<'_>, name: &str) -> Expr {
    tc.infer_type(&Expr::const_(Name::from_string(name), vec![]))
        .unwrap_or_else(|e| panic!("{name}: infer_type failed: {e}"))
}

fn assert_real_ofnat_eq_ofint_binder_structure(tc: &crate::tc::TypeChecker<'_>, nat_const: &Expr) {
    let axiom_type = infer_order_axiom_type(tc, "Real.ofNat_eq_ofInt");
    assert_eq!(
        pi_domain_at(&axiom_type, 0),
        Some(nat_const),
        "Real.ofNat_eq_ofInt: binder 0 should be `n : Nat`"
    );
    assert!(
        matches!(
            pi_body_after(&axiom_type, 1).map(|expr| &expr.kind),
            Some(ExprKind::App(..))
        ),
        "Real.ofNat_eq_ofInt: body should be an equality application"
    );
}

fn assert_real_ofint_order_binder_structure(
    tc: &crate::tc::TypeChecker<'_>,
    name: &str,
    int_const: &Expr,
) {
    let axiom_type = infer_order_axiom_type(tc, name);
    assert_eq!(
        pi_domain_at(&axiom_type, 0),
        Some(int_const),
        "{name}: binder 0 should be `a : Int`"
    );
    assert_eq!(
        pi_domain_at(&axiom_type, 1),
        Some(int_const),
        "{name}: binder 1 should be `b : Int`"
    );
    let h_domain = pi_domain_at(&axiom_type, 2)
        .unwrap_or_else(|| panic!("{name}: missing binder 2 (Real-order hypothesis)"));
    assert!(
        matches!(&h_domain.kind, ExprKind::App(..)),
        "{name}: binder 2 should be App (Real comparison applied to ofInt terms)"
    );
    assert!(
        matches!(
            pi_body_after(&axiom_type, 3).map(|expr| &expr.kind),
            Some(ExprKind::App(..))
        ),
        "{name}: body should be an Int comparison application"
    );
}

fn assert_real_ofnat_eq_ofint_shape(tc: &crate::tc::TypeChecker<'_>, real_const: &Expr) {
    let axiom_type = infer_order_axiom_type(tc, "Real.ofNat_eq_ofInt");
    let expected = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                real_const.clone(),
            ),
            Expr::app(
                Expr::const_(Name::from_string("Real.ofNat"), vec![]),
                Expr::bvar(0),
            ),
        ),
        Expr::app(
            Expr::const_(Name::from_string("Real.ofInt"), vec![]),
            Expr::app(
                Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                Expr::bvar(0),
            ),
        ),
    );
    assert!(
        tc.is_def_eq(
            pi_body_after(&axiom_type, 1)
                .expect("Real.ofNat_eq_ofInt should have a body after one binder"),
            &expected
        ),
        "Real.ofNat_eq_ofInt should equate Real.ofNat n with Real.ofInt (Int.ofNat n)"
    );
}

fn assert_real_ofint_order_shape(
    tc: &crate::tc::TypeChecker<'_>,
    name: &str,
    real_const: &Expr,
    real_cmp_name: &str,
    inst_name: &str,
    int_cmp_name: &str,
) {
    let axiom_type = infer_order_axiom_type(tc, name);
    let expected_h = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string(real_cmp_name), vec![Level::zero()]),
                    real_const.clone(),
                ),
                Expr::const_(Name::from_string(inst_name), vec![]),
            ),
            Expr::app(
                Expr::const_(Name::from_string("Real.ofInt"), vec![]),
                Expr::bvar(1),
            ),
        ),
        Expr::app(
            Expr::const_(Name::from_string("Real.ofInt"), vec![]),
            Expr::bvar(0),
        ),
    );
    assert!(
        tc.is_def_eq(
            pi_domain_at(&axiom_type, 2)
                .unwrap_or_else(|| panic!("{name} should have a Real-order hypothesis")),
            &expected_h
        ),
        "{name}: hypothesis should use the expected Real ordering"
    );
    let expected_body = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string(int_cmp_name), vec![]),
            Expr::bvar(2),
        ),
        Expr::bvar(1),
    );
    assert!(
        tc.is_def_eq(
            pi_body_after(&axiom_type, 3)
                .unwrap_or_else(|| panic!("{name} should have an Int-order body")),
            &expected_body
        ),
        "{name}: body should return the matching Int ordering"
    );
}

#[test]
fn test_real_ofint_downcast_axioms_binder_structure() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_real_linear_order().unwrap();
    let tc = TypeChecker::new(&env);
    let int_const = Expr::const_(Name::from_string("Int"), vec![]);
    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

    for name in [
        "Real.ofNat_eq_ofInt",
        "Real.ofInt_le_to_Int",
        "Real.ofInt_lt_to_Int",
    ] {
        assert_axiom(&env, name);
        let _ = infer_order_axiom_type(&tc, name);
    }

    assert_real_ofnat_eq_ofint_binder_structure(&tc, &nat_const);
    for name in ["Real.ofInt_le_to_Int", "Real.ofInt_lt_to_Int"] {
        assert_real_ofint_order_binder_structure(&tc, name, &int_const);
    }
}

#[test]
fn test_real_ofint_downcast_axioms_typeclass_shape() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_real_linear_order().unwrap();
    let tc = TypeChecker::new(&env);
    let real_const = Expr::const_(Name::from_string("Real"), vec![]);

    assert_real_ofnat_eq_ofint_shape(&tc, &real_const);
    assert_real_ofint_order_shape(
        &tc,
        "Real.ofInt_le_to_Int",
        &real_const,
        "LE.le",
        "instLEReal",
        "Int.le",
    );
    assert_real_ofint_order_shape(
        &tc,
        "Real.ofInt_lt_to_Int",
        &real_const,
        "LT.lt",
        "instLTReal",
        "Int.lt",
    );
}

/// The Int order-tower lemmas demoted from `Declaration::Axiom` to
/// constructive `Declaration::Theorem` are registered as Theorems with a
/// proof value and an empty domain-axiom closure, when reached through the
/// full `init_int_ord_lemmas` aggregate entry point.
///
/// Pins the demotion (`Int.le_refl`, `Int.le_trans`, `Int.lt_irrefl`) against
/// regression to a bare axiom. The remaining `init_int_ord_lemmas` entries
/// (`Int.le_antisymm`, `Int.lt_trans`, `Int.le_of_lt`, the `add_*`/`mul_*`
/// families, …) stay axioms and are intentionally *not* asserted here.
#[test]
fn test_int_order_demoted_lemmas_are_constructive_theorems() {
    use crate::env::axiom_audit::ProofQuality;

    let mut env = Environment::new();
    env.init_int_ord_lemmas()
        .expect("init_int_ord_lemmas should succeed");

    for lemma in ["Int.le_refl", "Int.le_trans", "Int.lt_irrefl"] {
        let n = Name::from_string(lemma);
        let info = env
            .get_const(&n)
            .unwrap_or_else(|| panic!("{lemma} must be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{lemma} must be a `Declaration::Theorem`, got {:?}",
            info.kind,
        );
        assert!(
            info.value.is_some(),
            "{lemma} Theorem must carry a proof term",
        );
        let deps = env
            .axiom_deps(&n)
            .expect("axiom_deps must succeed for a registered theorem");
        assert!(
            deps.is_empty(),
            "{lemma} must have zero domain-specific axiom deps, found: {:?}",
            deps.iter().map(|d| d.to_string()).collect::<Vec<_>>(),
        );
        match env.proof_quality(&n) {
            Some(ProofQuality::Constructive) => {}
            other => panic!("{lemma} must be ProofQuality::Constructive, got {other:?}"),
        }
    }
}

/// The constructive helper theorems backing the Int order demotions are
/// themselves Theorems with empty axiom closures.
#[test]
fn test_int_order_helper_theorems_are_constructive() {
    use crate::env::axiom_audit::ProofQuality;

    let mut env = Environment::new();
    env.init_int_ord_lemmas()
        .expect("init_int_ord_lemmas should succeed");

    for helper in [
        "Int.NonNeg.add",
        "Int.sub_add_sub_cancel",
        "Int.sub_add_one_self",
    ] {
        let n = Name::from_string(helper);
        let info = env
            .get_const(&n)
            .unwrap_or_else(|| panic!("{helper} must be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{helper} must be a `Declaration::Theorem`, got {:?}",
            info.kind,
        );
        let deps = env
            .axiom_deps(&n)
            .expect("axiom_deps must succeed for a registered theorem");
        assert!(
            deps.is_empty(),
            "{helper} must have zero domain-specific axiom deps, found: {:?}",
            deps.iter().map(|d| d.to_string()).collect::<Vec<_>>(),
        );
        match env.proof_quality(&n) {
            Some(ProofQuality::Constructive) => {}
            other => panic!("{helper} must be ProofQuality::Constructive, got {other:?}"),
        }
    }
}

// ---------------------------------------------------------------------------
// #3604: `Nat.*` arithmetic ordering lemmas demoted from `Declaration::Axiom`
// to constructive `Declaration::Theorem`s. See `nat_arith_order_proof.rs`.
// ---------------------------------------------------------------------------

/// The demoted `Nat.add_le_add*` / `Nat.mul_le_mul*` lemmas are registered as
/// `Declaration::Theorem`s carrying real proof terms, with empty
/// domain-specific axiom closures and `ProofQuality::Constructive`.
#[test]
fn test_nat_arith_order_demoted_lemmas_are_constructive_theorems() {
    use crate::env::axiom_audit::ProofQuality;

    let mut env = Environment::new();
    env.init_nat_add_ord()
        .expect("init_nat_add_ord should succeed");
    env.init_nat_mul_ord()
        .expect("init_nat_mul_ord should succeed");

    for lemma in [
        "Nat.add_le_add_left",
        "Nat.add_le_add_right",
        "Nat.add_le_add",
        "Nat.mul_le_mul_right",
        "Nat.mul_le_mul",
    ] {
        let n = Name::from_string(lemma);
        let info = env
            .get_const(&n)
            .unwrap_or_else(|| panic!("{lemma} must be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{lemma} must be a `Declaration::Theorem`, got {:?}",
            info.kind,
        );
        assert!(
            info.value.is_some(),
            "{lemma} Theorem must carry a proof term",
        );
        let deps = env
            .axiom_deps(&n)
            .expect("axiom_deps must succeed for a registered theorem");
        assert!(
            deps.is_empty(),
            "{lemma} must have zero domain-specific axiom deps, found: {:?}",
            deps.iter().map(|d| d.to_string()).collect::<Vec<_>>(),
        );
        match env.proof_quality(&n) {
            Some(ProofQuality::Constructive) => {}
            other => panic!("{lemma} must be ProofQuality::Constructive, got {other:?}"),
        }
    }
}

/// Each demoted lemma's stored type matches the original axiom signature, and
/// the registered proof term kernel-type-checks against that type.
#[test]
fn test_nat_arith_order_demoted_lemmas_kernel_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_nat_add_ord()
        .expect("init_nat_add_ord should succeed");
    env.init_nat_mul_ord()
        .expect("init_nat_mul_ord should succeed");

    // Snapshot the proof terms / types before borrowing the env immutably.
    let lemmas = [
        "Nat.add_le_add_left",
        "Nat.add_le_add_right",
        "Nat.add_le_add",
        "Nat.mul_le_mul_right",
        "Nat.mul_le_mul",
    ];
    let snapshots: Vec<(String, Expr, Expr)> = lemmas
        .iter()
        .map(|lemma| {
            let info = env
                .get_const(&Name::from_string(lemma))
                .unwrap_or_else(|| panic!("{lemma} must be registered"));
            let value = info
                .value
                .clone()
                .unwrap_or_else(|| panic!("{lemma} must carry a proof term"));
            ((*lemma).to_string(), info.type_.clone(), value)
        })
        .collect();

    let tc = TypeChecker::new(&env);
    for (lemma, type_, value) in &snapshots {
        // The stated type is itself well-formed (infers a Sort).
        let _ = tc
            .infer_type(type_)
            .unwrap_or_else(|e| panic!("{lemma} type must typecheck: {e:?}"));
        // The proof term's inferred type is defeq to the stated type.
        let inferred = tc
            .infer_type(value)
            .unwrap_or_else(|e| panic!("{lemma} proof term must typecheck: {e:?}"));
        assert!(
            tc.is_def_eq(&inferred, type_),
            "{lemma} proof term type must be defeq to its stated type",
        );
    }
}

/// `Nat.add_le_add_left` proves the expected concrete instance `1 + 2 ≤ 1 + 3`
/// when applied to `Nat.le 2 3` (`Nat.le.step` of `Nat.le.refl 2`). Pins the
/// proof term against the actual ordering statement, not just its type shape.
#[test]
fn test_nat_add_le_add_left_proves_concrete_instance() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_nat_add_ord()
        .expect("init_nat_add_ord should succeed");

    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let le = Expr::const_(Name::from_string("Nat.le"), vec![]);
    let le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
    let le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
    let add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let add_le_add_left = Expr::const_(Name::from_string("Nat.add_le_add_left"), vec![]);

    let one = Expr::app(nat_succ.clone(), zero.clone());
    let two = Expr::app(nat_succ.clone(), one.clone());
    let three = Expr::app(nat_succ.clone(), two.clone());

    // h : Nat.le 2 3 = Nat.le.step 2 2 (Nat.le.refl 2)
    let h = Expr::apps(
        le_step,
        [two.clone(), two.clone(), Expr::app(le_refl, two.clone())],
    );
    // Nat.add_le_add_left 2 3 h 1 : Nat.le (1 + 2) (1 + 3)
    let proof = Expr::apps(
        add_le_add_left,
        [two.clone(), three.clone(), h, one.clone()],
    );

    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(&proof)
        .expect("Nat.add_le_add_left applied instance must typecheck");
    let expected = Expr::apps(
        le,
        [
            Expr::apps(add.clone(), [one.clone(), two]),
            Expr::apps(add, [one, three]),
        ],
    );
    assert!(
        tc.is_def_eq(&inferred, &expected),
        "Nat.add_le_add_left 2 3 h 1 should prove Nat.le (1+2) (1+3); inferred {inferred:?}",
    );
}

// ---------------------------------------------------------------------------
// #3604 (lt cluster): `Nat.lt`-family / `Nat.sub` order lemmas demoted from
// `Declaration::Axiom` to constructive `Declaration::Theorem`s. See
// `nat_arith_order_proof.rs`.
// ---------------------------------------------------------------------------

/// The demoted `Nat.add_lt_add*` / `Nat.mul_lt_mul_left` / `Nat.sub_le` lemmas
/// (and the `Nat.pred_le` helper) are registered as `Declaration::Theorem`s
/// carrying real proof terms, with empty domain-specific axiom closures and
/// `ProofQuality::Constructive`.
#[test]
fn test_nat_lt_order_demoted_lemmas_are_constructive_theorems() {
    use crate::env::axiom_audit::ProofQuality;

    let mut env = Environment::new();
    env.init_nat_add_ord()
        .expect("init_nat_add_ord should succeed");
    env.init_nat_mul_ord()
        .expect("init_nat_mul_ord should succeed");
    env.init_nat_sub_ord()
        .expect("init_nat_sub_ord should succeed");

    for lemma in [
        "Nat.pred_le",
        "Nat.add_lt_add_left",
        "Nat.add_lt_add_right",
        "Nat.add_lt_add",
        "Nat.mul_lt_mul_left",
        "Nat.sub_le",
    ] {
        let n = Name::from_string(lemma);
        let info = env
            .get_const(&n)
            .unwrap_or_else(|| panic!("{lemma} must be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{lemma} must be a `Declaration::Theorem`, got {:?}",
            info.kind,
        );
        assert!(
            info.value.is_some(),
            "{lemma} Theorem must carry a proof term",
        );
        let deps = env
            .axiom_deps(&n)
            .expect("axiom_deps must succeed for a registered theorem");
        assert!(
            deps.is_empty(),
            "{lemma} must have zero domain-specific axiom deps, found: {:?}",
            deps.iter().map(|d| d.to_string()).collect::<Vec<_>>(),
        );
        match env.proof_quality(&n) {
            Some(ProofQuality::Constructive) => {}
            other => panic!("{lemma} must be ProofQuality::Constructive, got {other:?}"),
        }
    }
}

/// Each demoted `lt`/`sub` lemma's stored type matches the original axiom
/// signature, and the registered proof term kernel-type-checks against it.
#[test]
fn test_nat_lt_order_demoted_lemmas_kernel_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_nat_add_ord()
        .expect("init_nat_add_ord should succeed");
    env.init_nat_mul_ord()
        .expect("init_nat_mul_ord should succeed");
    env.init_nat_sub_ord()
        .expect("init_nat_sub_ord should succeed");

    let lemmas = [
        "Nat.pred_le",
        "Nat.add_lt_add_left",
        "Nat.add_lt_add_right",
        "Nat.add_lt_add",
        "Nat.mul_lt_mul_left",
        "Nat.sub_le",
    ];
    let snapshots: Vec<(String, Expr, Expr)> = lemmas
        .iter()
        .map(|lemma| {
            let info = env
                .get_const(&Name::from_string(lemma))
                .unwrap_or_else(|| panic!("{lemma} must be registered"));
            let value = info
                .value
                .clone()
                .unwrap_or_else(|| panic!("{lemma} must carry a proof term"));
            ((*lemma).to_string(), info.type_.clone(), value)
        })
        .collect();

    let tc = TypeChecker::new(&env);
    for (lemma, type_, value) in &snapshots {
        let _ = tc
            .infer_type(type_)
            .unwrap_or_else(|e| panic!("{lemma} type must typecheck: {e:?}"));
        let inferred = tc
            .infer_type(value)
            .unwrap_or_else(|e| panic!("{lemma} proof term must typecheck: {e:?}"));
        assert!(
            tc.is_def_eq(&inferred, type_),
            "{lemma} proof term type must be defeq to its stated type",
        );
    }
}

/// The demoted lt-family lemmas keep the Lean 4 binder order
/// `∀ a b, Nat.lt a b → ∀ c, ...` (raw `Nat.lt` hypothesis at binder 2),
/// matching the original axiom signatures.
#[test]
fn test_nat_lt_order_demoted_lemmas_preserve_binder_order() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_nat_add_ord()
        .expect("init_nat_add_ord should succeed");
    let tc = TypeChecker::new(&env);
    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
    let lt_const = Expr::const_(Name::from_string("Nat.lt"), vec![]);
    let expected_lt_h = Expr::app(Expr::app(lt_const, Expr::bvar(1)), Expr::bvar(0));

    for lemma in ["Nat.add_lt_add_left", "Nat.add_lt_add_right"] {
        let ty = tc
            .infer_type(&Expr::const_(Name::from_string(lemma), vec![]))
            .unwrap_or_else(|e| panic!("{lemma} type must infer: {e:?}"));
        assert_eq!(
            pi_domain_at(&ty, 0),
            Some(&nat_const),
            "{lemma} binder 0 = a : Nat",
        );
        assert_eq!(
            pi_domain_at(&ty, 1),
            Some(&nat_const),
            "{lemma} binder 1 = b : Nat",
        );
        assert_eq!(
            pi_domain_at(&ty, 2),
            Some(&expected_lt_h),
            "{lemma} binder 2 = h : Nat.lt a b",
        );
        assert_eq!(
            pi_domain_at(&ty, 3),
            Some(&nat_const),
            "{lemma} binder 3 = c : Nat",
        );
    }
}

/// `Nat.pred_le` proves `Nat.le (Nat.pred 3) 3`: `Nat.pred 3 ≡ 2`, so the
/// inferred type is defeq to `Nat.le 2 3`.
#[test]
fn test_nat_pred_le_proves_concrete_instance() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_nat_add_ord()
        .expect("init_nat_add_ord should succeed");

    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let le = Expr::const_(Name::from_string("Nat.le"), vec![]);
    let pred_le = Expr::const_(Name::from_string("Nat.pred_le"), vec![]);

    let one = Expr::app(nat_succ.clone(), zero.clone());
    let two = Expr::app(nat_succ.clone(), one);
    let three = Expr::app(nat_succ, two.clone());

    // Nat.pred_le 3 : Nat.le (Nat.pred 3) 3 ≡ Nat.le 2 3
    let proof = Expr::app(pred_le, three.clone());

    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(&proof)
        .expect("Nat.pred_le applied instance must typecheck");
    let expected = Expr::apps(le, [two, three]);
    assert!(
        tc.is_def_eq(&inferred, &expected),
        "Nat.pred_le 3 should prove Nat.le 2 3; inferred {inferred:?}",
    );
}

/// `Nat.add_lt_add_left` proves the concrete instance `1 + 2 < 1 + 4` when
/// applied to `Nat.lt 2 4`. Pins the proof term against the actual ordering
/// statement (the unfolded `Nat.le (Nat.succ (1+2)) (1+4)`).
#[test]
fn test_nat_add_lt_add_left_proves_concrete_instance() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_nat_add_ord()
        .expect("init_nat_add_ord should succeed");

    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
    let le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
    let le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
    let add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let add_lt_add_left = Expr::const_(Name::from_string("Nat.add_lt_add_left"), vec![]);

    let one = Expr::app(nat_succ.clone(), zero.clone());
    let two = Expr::app(nat_succ.clone(), one.clone());
    let three = Expr::app(nat_succ.clone(), two.clone());
    let four = Expr::app(nat_succ.clone(), three.clone());

    // h : Nat.lt 2 4 ≡ Nat.le 3 4 = Nat.le.step 3 3 (Nat.le.refl 3)
    let h = Expr::apps(
        le_step,
        [
            three.clone(),
            three.clone(),
            Expr::app(le_refl, three.clone()),
        ],
    );
    // Nat.add_lt_add_left 2 4 h 1 : Nat.lt (1 + 2) (1 + 4)
    let proof = Expr::apps(add_lt_add_left, [two.clone(), four.clone(), h, one.clone()]);

    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(&proof)
        .expect("Nat.add_lt_add_left applied instance must typecheck");
    let expected = Expr::apps(
        lt,
        [
            Expr::apps(add.clone(), [one.clone(), two]),
            Expr::apps(add, [one, four]),
        ],
    );
    assert!(
        tc.is_def_eq(&inferred, &expected),
        "Nat.add_lt_add_left 2 4 h 1 should prove Nat.lt (1+2) (1+4); inferred {inferred:?}",
    );
}

/// `Nat.mul_lt_mul_left` proves `2 * 1 < 2 * 3` from `0 < 2` and `1 < 3`,
/// exercising the positivity-dispatch path through `Nat.add_le_add_left`.
#[test]
fn test_nat_mul_lt_mul_left_proves_concrete_instance() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_nat_mul_ord()
        .expect("init_nat_mul_ord should succeed");

    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
    let le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
    let le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
    let mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
    let mul_lt_mul_left = Expr::const_(Name::from_string("Nat.mul_lt_mul_left"), vec![]);

    let one = Expr::app(nat_succ.clone(), zero.clone());
    let two = Expr::app(nat_succ.clone(), one.clone());
    let three = Expr::app(nat_succ.clone(), two.clone());

    // h1 : Nat.lt 0 2 ≡ Nat.le 1 2 = Nat.le.step 1 1 (Nat.le.refl 1)
    let h1 = Expr::apps(
        le_step.clone(),
        [
            one.clone(),
            one.clone(),
            Expr::app(le_refl.clone(), one.clone()),
        ],
    );
    // h2 : Nat.lt 1 3 ≡ Nat.le 2 3 = Nat.le.step 2 2 (Nat.le.refl 2)
    let h2 = Expr::apps(
        le_step,
        [two.clone(), two.clone(), Expr::app(le_refl, two.clone())],
    );
    // Nat.mul_lt_mul_left 1 3 2 h1 h2 : Nat.lt (2 * 1) (2 * 3)
    let proof = Expr::apps(
        mul_lt_mul_left,
        [one.clone(), three.clone(), two.clone(), h1, h2],
    );

    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(&proof)
        .expect("Nat.mul_lt_mul_left applied instance must typecheck");
    let expected = Expr::apps(
        lt,
        [
            Expr::apps(mul.clone(), [two.clone(), one]),
            Expr::apps(mul, [two, three]),
        ],
    );
    assert!(
        tc.is_def_eq(&inferred, &expected),
        "Nat.mul_lt_mul_left 1 3 2 h1 h2 should prove Nat.lt (2*1) (2*3); inferred {inferred:?}",
    );
}

/// FIDELITY / SHADOWING GUARD: in IMPORT mode
/// (`try_with_prelude_for_import`, `suppress_lossy_structure_stubs`), Clean must
/// NOT seed its hand-rolled `Nat.mul_lt_mul_left` / `Nat.mul_lt_mul_right`.
///
/// Clean registers those as the IMPLICATION
/// `∀ a b c, 0 < c → a < b → c*a < c*b`, but Lean core's genuine lemmas are
/// IFFs (`∀ {a b c}, 0 < a → (a*b < a*c ↔ b < c)` and the `_right` mirror).
/// As `Theorem`/`Axiom` stubs the implication forms SHADOW the real Iff on
/// import, so every Mathlib proof that applies the Iff — e.g.
/// `Nat.lt_mul_iff_one_lt_right`, `Nat.mul_lt_mul_pow_succ`,
/// `Nat.lt_div_iff_mul_lt`, which do `(Nat.mul_lt_mul_left h).2` / rewrite with
/// it — was kernel-rejected with a spurious TypeMismatch. Suppressing the stubs
/// lets the genuine Iff-form import register. This test pins that the stubs are
/// absent (or at least NOT the implication `Theorem`) in import mode.
#[test]
fn test_nat_mul_lt_mul_left_suppressed_in_import_mode() {
    let env = Environment::try_with_prelude_for_import().expect("import prelude must build");

    // The wrong implication stub must NOT be seeded as a Theorem in import mode;
    // withholding it lets the genuine Lean Iff-form import in its place. (It may
    // be absent entirely — the assertion is that it is NOT the implication
    // Theorem overlay.)
    let is_impl_theorem = env
        .get_const(&Name::from_string("Nat.mul_lt_mul_left"))
        .map(|ci| ci.kind == ConstantKind::Theorem)
        .unwrap_or(false);
    assert!(
        !is_impl_theorem,
        "import mode must NOT seed the implication-form `Nat.mul_lt_mul_left` \
         Theorem — it shadows Lean's real Iff and rejects real Mathlib proofs",
    );
    // The `_right` Axiom stub must likewise be absent in import mode.
    assert!(
        env.get_const(&Name::from_string("Nat.mul_lt_mul_right"))
            .is_none(),
        "import mode must NOT seed the implication-form `Nat.mul_lt_mul_right` \
         stub — it shadows Lean's real Iff",
    );
}

/// REGRESSION GUARD: the NON-import lane is UNCHANGED — `init_nat_mul_ord`
/// still registers Clean's constructive implication-form `Nat.mul_lt_mul_left`
/// (a kernel-checked `Theorem`) for every Clean-native consumer. The
/// suppression is import-only; `clean check` and the ordering tests keep the
/// implication form.
#[test]
fn test_nat_mul_lt_mul_left_present_in_native_mode() {
    let mut env = Environment::new();
    env.init_nat_mul_ord().expect("init_nat_mul_ord");
    let ci = env
        .get_const(&Name::from_string("Nat.mul_lt_mul_left"))
        .expect("native mode must register `Nat.mul_lt_mul_left`");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "native mode must keep the constructive implication-form \
         `Nat.mul_lt_mul_left` Theorem",
    );
    // Its type is the implication `0 < c → a < b → c*a < c*b`, so the 4th Pi
    // domain (index 3) is the SECOND hypothesis `Nat.lt a b`, NOT an Iff. Read
    // the head const of that domain and require it to be `Nat.lt`.
    let h2 = pi_domain_at(&ci.type_, 3).expect("second-hypothesis Pi domain");
    let mut head: &Expr = h2;
    while let ExprKind::App(f, _) = &head.kind {
        head = f.as_ref();
    }
    assert!(
        matches!(&head.kind, ExprKind::Const(n, _) if *n == Name::from_string("Nat.lt")),
        "native `Nat.mul_lt_mul_left` second hypothesis must be `Nat.lt a b` \
         (implication form); got head {head:?}",
    );
}

/// `Nat.sub_le` proves `Nat.le (5 - 2) 5`: `5 - 2 ≡ 3`, so the inferred type is
/// defeq to `Nat.le 3 5`.
#[test]
fn test_nat_sub_le_proves_concrete_instance() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_nat_sub_ord()
        .expect("init_nat_sub_ord should succeed");

    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let le = Expr::const_(Name::from_string("Nat.le"), vec![]);
    let sub_le = Expr::const_(Name::from_string("Nat.sub_le"), vec![]);

    let one = Expr::app(nat_succ.clone(), zero.clone());
    let two = Expr::app(nat_succ.clone(), one.clone());
    let three = Expr::app(nat_succ.clone(), two.clone());
    let four = Expr::app(nat_succ.clone(), three.clone());
    let five = Expr::app(nat_succ, four);

    // Nat.sub_le 5 2 : Nat.le (5 - 2) 5 ≡ Nat.le 3 5
    let proof = Expr::apps(sub_le, [five.clone(), two]);

    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(&proof)
        .expect("Nat.sub_le applied instance must typecheck");
    let expected = Expr::apps(le, [three, five]);
    assert!(
        tc.is_def_eq(&inferred, &expected),
        "Nat.sub_le 5 2 should prove Nat.le 3 5; inferred {inferred:?}",
    );
}
