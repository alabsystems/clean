// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Regression: `Trans.trans h₁ h₂` must compose over an IMPORTED-shape
//! instance.**
//!
//! The kernel prelude used to seed a lossy `Trans` (three universe params,
//! `Prop`-hardcoded relations, no `outParam`), and `.olean` import is
//! first-registered-wins, so that stub permanently shadowed Lean's six-universe
//! `Trans`. Direct `Trans.trans` composition — no `calc` involved — then failed
//! for every imported relation.
//!
//! # These decoys are `Axiom`-kind and VALUE-LESS on purpose
//!
//! An imported constant reaches Clean as a `Declaration::Axiom` with a type and
//! no body, and it is NOT `@[reducible]`. A version of this test written against
//! Clean's own reducible Nat instances passes with or without the fix, because
//! the elaborator can unfold its way around the universe mismatch — it would be
//! a decoy that never exercises the mechanism. Every constant below is
//! deliberately a value-less `Declaration::Axiom` whose type is spelled the way
//! the `.olean` spells it: `Trans.{0, 0, 0, 1, 1, 1} …`.
//!
//! Both tests here FAIL against the pre-fix 3-universe stub.

use super::*;

use clean_kernel::env::{KernelInstanceInfo, LEAN_DEFAULT_INSTANCE_PRIORITY};
use clean_kernel::Level;

/// Lean's six universe arguments for a `Prop`-valued relation on a `Type 0`
/// carrier.
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

/// Prelude + value-less `Axiom` decoys mirroring an imported relation and its
/// imported `Trans` instance.
fn env_with_imported_trans_instance() -> Environment {
    let mut env = Environment::with_prelude();

    let type0 = Expr::sort(Level::succ(Level::zero()));
    let prop = Expr::sort(Level::zero());

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("TCarrier"),
        level_params: vec![],
        type_: type0,
    })
    .expect("carrier axiom");
    let carrier = Expr::const_(Name::from_string("TCarrier"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("TRel"),
        level_params: vec![],
        type_: Expr::arrow(carrier.clone(), Expr::arrow(carrier.clone(), prop)),
    })
    .expect("relation axiom");
    let rel = Expr::const_(Name::from_string("TRel"), vec![]);

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
        name: Name::from_string("instTransTRel"),
        level_params: vec![],
        type_: inst_type.clone(),
    })
    .expect("Trans instance axiom spelled at Lean's universe arity must register");
    env.register_instance(KernelInstanceInfo {
        name: Name::from_string("instTransTRel"),
        class_name: Name::from_string("Trans"),
        priority: LEAN_DEFAULT_INSTANCE_PRIORITY,
        type_: Some(inst_type),
        value: None,
    });

    // Endpoints and hypotheses, all value-less axioms.
    for name in ["tx", "ty", "tz"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: carrier.clone(),
        })
        .expect("endpoint axiom");
    }
    let rel_app = |a: &str, b: &str| {
        Expr::apps(
            rel.clone(),
            [
                Expr::const_(Name::from_string(a), vec![]),
                Expr::const_(Name::from_string(b), vec![]),
            ],
        )
    };
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hxy"),
        level_params: vec![],
        type_: rel_app("tx", "ty"),
    })
    .expect("hxy axiom");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hyz"),
        level_params: vec![],
        type_: rel_app("ty", "tz"),
    })
    .expect("hyz axiom");

    env
}

/// `Trans.trans hxy hyz` elaborates and infers `TRel tx tz`: the implicit
/// `{α β γ r s t}` and the `[Trans r s t]` instance are all filled from the two
/// value-less proof axioms.
#[test]
fn test_trans_trans_direct_composition_over_imported_shape_instance() {
    let env = env_with_imported_trans_instance();
    let mut ctx = ElabCtx::new(&env);
    let surface = parse_expr("Trans.trans hxy hyz").expect("expression should parse");
    let expr = ctx
        .elaborate(&surface)
        .expect("direct Trans.trans composition must elaborate");
    let ty = ctx
        .infer_type(&expr)
        .expect("the composed term must have an inferable type");
    let expected = Expr::apps(
        Expr::const_(Name::from_string("TRel"), vec![]),
        [
            Expr::const_(Name::from_string("tx"), vec![]),
            Expr::const_(Name::from_string("tz"), vec![]),
        ],
    );
    assert_eq!(
        ctx.metas.instantiate(&ty),
        expected,
        "Trans.trans hxy hyz must have type `TRel tx tz`"
    );
}

/// The prelude's `Trans` must be applicable at Lean's arity from surface syntax,
/// and the environment must expose it as a class with `t` as an out-param.
#[test]
fn test_prelude_trans_is_lean_shaped_for_the_elaborator() {
    let env = Environment::with_prelude();
    let info = env
        .get_const(&Name::from_string("Trans"))
        .expect("prelude must define Trans");
    assert_eq!(
        info.level_params.len(),
        6,
        "Lean's `Trans` is six-universe; a narrower prelude spelling discards \
         Lean's class on import"
    );
    let class_info = env
        .get_class_info(&Name::from_string("Trans"))
        .expect("Trans must be a registered class so `Trans r s ?t` goals are searched");
    assert_eq!(class_info.out_params, vec![5]);
}
