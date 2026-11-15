// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! An instance whose class level is a `max` of two SUCCESSORS must resolve at
//! two distinct rigid universe parameters even when the candidate spells that
//! `max` in the OTHER order.
//!
//! `max` is commutative, and the two orders are the same level. Lean's
//! serializer normalises: `#check @instInhabitedProd` on the pinned
//! v4.30.0-rc2 prints
//!
//! ```text
//! @instInhabitedProd.{u_1, u_2} : {α : Type u_1} → {β : Type u_2} →
//!   [Inhabited.{u_1 + 1} α] → [Inhabited.{u_2 + 1} β] →
//!   Inhabited.{max (u_2 + 1) (u_1 + 1)} (Prod.{u_1, u_2} α β)
//! ```
//!
//! — `u_2` FIRST in the class level, `u_1` first in `Prod`. Clean builds its
//! GOAL from `Prod`'s own result sort (`env/core.rs`:
//! `Sort (max (u+1) (v+1))`), so the goal's `max` is in source order and the
//! decoded candidate's is not.
//!
//! The `Max`/`Max` congruence split in `unify/level_solve.rs` pairs operands
//! POSITIONALLY, so it solved `max (?b+1) (?a+1) =?= max (u+1) (v+1)` as
//! `?b := u`, `?a := v` — a solution of that equation, but the CROSSED one —
//! and the argument unification that follows then posed
//! `Prod.{?a, ?b} ?m0 ?m1 =?= Prod.{u, v} A A'` and died
//! `cannot assign rigid universe parameter v := u`
//! (`Mathlib/Logic/Function/Basic.lean`: `Function.curry_update`,
//! `Function.uncurry_update_update`, both of which need
//! `DecidableEq (α × α')` at `{α α' : Type*}`).
//!
//! The controls below are what make the class invisible to ordinary tests: a
//! candidate written in SOURCE order passes, and so does every same-universe
//! or `Type 0` instantiation, because there the crossed pairing and the
//! straight one agree. Clean-native candidates are always in source order,
//! which is why the bug only ever showed up under a real `.olean`.

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::env::Declaration;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, KernelInstanceInfo};
use clean_parser::parse_file;

/// `{α : Type u} → {β : Type v} → Inhabited.{<class level>} (Prod.{u, v} α β)`,
/// registered as an `Inhabited` instance exactly the way `clean-olean`'s
/// `register_instances_from_extension` registers a decoded one: by NAME, with
/// `type_`/`value` left `None` so the elaborator reads the constant's own type.
///
/// `class_level` is the only thing that varies between the two arms.
fn register_prod_inhabited(env: &mut Environment, name: &str, class_level: Level) {
    let u = Name::from_string("u");
    let v = Name::from_string("v");
    let lu = Level::param(u.clone());
    let lv = Level::param(v.clone());

    let conclusion = Expr::app(
        Expr::const_(Name::from_string("Inhabited"), vec![class_level]),
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Prod"), vec![lu.clone(), lv.clone()]),
                Expr::bvar(1),
            ),
            Expr::bvar(0),
        ),
    );
    let type_ = Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(Level::succ(lu)),
        Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::succ(lv)),
            conclusion,
        ),
    );

    let inst_name = Name::from_string(name);
    env.add_decl(Declaration::Axiom {
        name: inst_name.clone(),
        level_params: vec![u, v],
        type_,
    })
    .expect("the hand-built instance axiom must kernel-check");
    env.register_instance(KernelInstanceInfo {
        name: inst_name,
        class_name: Name::from_string("Inhabited"),
        priority: clean_kernel::DEFAULT_INSTANCE_PRIORITY,
        type_: None,
        value: None,
    });
}

/// `max (u+1) (v+1)` — the order Clean's own elaborator produces.
fn source_order_class_level() -> Level {
    Level::max(
        Level::succ(Level::param(Name::from_string("u"))),
        Level::succ(Level::param(Name::from_string("v"))),
    )
}

/// `max (v+1) (u+1)` — the order Lean's serializer produces, and so the order
/// a decoded `.olean` candidate arrives in.
fn lean_normalised_class_level() -> Level {
    Level::max(
        Level::succ(Level::param(Name::from_string("v"))),
        Level::succ(Level::param(Name::from_string("u"))),
    )
}

/// Elaborate `src` against `env`; `Some(message)` for the first failure.
fn elab(env: &mut Environment, src: &str) -> Option<String> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(env, d) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

/// The consumer: two DISTINCT rigid universe parameters, which is the only
/// instantiation that can tell the two pairings apart.
const DISTINCT_UNIVERSES: &str =
    "noncomputable def probeDiff {A : Type u} {A' : Type v} : Inhabited (Prod A A') :=\n\
     \x20 inferInstance\n";

/// Both universes the SAME — the crossed pairing and the straight one agree
/// here, so this arm cannot see the defect and passed all along.
const SAME_UNIVERSE: &str =
    "noncomputable def probeSame {A A' : Type u} : Inhabited (Prod A A') := inferInstance\n";

#[test]
fn test_lean_normalised_max_order_resolves_at_distinct_universes() {
    let mut env = Environment::with_prelude();
    register_prod_inhabited(&mut env, "probeInhProd", lean_normalised_class_level());
    if let Some(e) = elab(&mut env, DISTINCT_UNIVERSES) {
        panic!(
            "a candidate whose class level spells `max` in the other order must still \
             resolve at two distinct universes — `max` is commutative: {e}"
        );
    }
}

#[test]
fn test_source_order_max_resolves_at_distinct_universes() {
    let mut env = Environment::with_prelude();
    register_prod_inhabited(&mut env, "probeInhProd", source_order_class_level());
    if let Some(e) = elab(&mut env, DISTINCT_UNIVERSES) {
        panic!("the source-order control must resolve: {e}");
    }
}

#[test]
fn test_lean_normalised_max_order_resolves_at_one_universe() {
    let mut env = Environment::with_prelude();
    register_prod_inhabited(&mut env, "probeInhProd", lean_normalised_class_level());
    if let Some(e) = elab(&mut env, SAME_UNIVERSE) {
        panic!("the same-universe control must resolve: {e}");
    }
}
