// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: PRIORITY-disambiguated resolution among IMPORTED instances.
//!
//! This is the priority/"diamond" analogue of the imported-instance-method
//! probe in `import_e2e_instance_method_tests.rs`. That probe proved instance
//! synthesis discriminates by *carrier type* for imported instances. Here we
//! exercise the orthogonal disambiguation axis: when TWO instances exist for
//! the *same* class *and* the *same* carrier, resolution must pick the one with
//! the higher numeric **priority** — exactly as Lean 4 does — and that priority
//! must survive the `.olean` import path into the elaborator's `InstanceTable`.
//!
//! ## Why this is a real risk for imported instances
//!
//! Priority lives in `KernelInstanceInfo.priority`. The kernel's
//! `Environment::register_instance` keeps each class's instance list sorted
//! highest-priority-first via a *stable* insertion
//! (`position(|i| i.priority < new.priority)`). The elaborator then *rebuilds*
//! its own `InstanceTable` from that kernel registry in
//! `clean_elab::infer::init_instances_from_env`, iterating
//! `env.get_class_instances(class)` (already sorted) and calling
//! `InstanceTable::add_instance` — which performs a *second* stable
//! priority-insertion. The resolution loop in `infer/instance.rs` then returns
//! the *first* instance (in that table order) whose result type unifies with
//! the goal.
//!
//! Three things therefore have to be right for an imported priority to win:
//!
//! 1. The importer must carry `priority` through to `register_instance`
//!    (rather than defaulting it). We register with explicit non-default
//!    priorities to pin this.
//! 2. The kernel's sort and the elaborator's *re-sort* must agree, so that
//!    a higher-priority instance registered *later* still ends up ahead of a
//!    lower-priority instance registered *earlier* (a double-sort that
//!    accidentally reversed equal/near ties would surface here).
//! 3. The resolution loop must take the first *unifying* candidate in priority
//!    order — not the first *registered* one.
//!
//! ## The trap (so a wrong pick is observable)
//!
//! Carrier `B : Type` has two distinct nullary constructors `B.lo` and `B.hi`.
//! Two instances, both `: Pick B`, are registered in the order that would give
//! the WRONG answer if priority were ignored and registration order won:
//!
//! ```text
//! instPickBLo : Pick B := Pick.mk B B.lo   -- registered FIRST,  priority  50
//! instPickBHi : Pick B := Pick.mk B B.hi   -- registered SECOND,  priority 200
//! ```
//!
//! `Pick.chosen : {α} → [Pick α] → α` selected for `: B` must synthesize the
//! HIGHER-priority `instPickBHi` and reduce to `B.hi`. If priority were dropped
//! on import (or the re-sort reversed it), the first-registered low-priority
//! `instPickBLo` would win and the def would reduce to `B.lo` — a directly
//! observable wrong head constructor, not a silent pass.
//!
//! Everything is registered *exactly the way `clean_olean` import does*: kernel
//! registries only, instances with `type_: None, value: None` (the elaborator
//! reconstructs them from `env.get_const`, the #443 path), and NO
//! `register_structure_fields`.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{
    BinderInfo, Declaration, Expr, ExprKind, KernelClassInfo, KernelInstanceInfo, Name, TypeChecker,
};
use clean_parser::parse_file;

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// Reduce `expr` to weak-head normal form and, if the head is a `Const`, return
/// its name. Used to observe which constructor the resolved instance yields.
fn whnf_head_const(env: &Environment, expr: &Expr) -> Option<String> {
    let tc = TypeChecker::new(env);
    let reduced = tc.whnf(expr);
    match reduced.kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

/// Add a nullary, two-constructor enum inductive `name : Type`.
fn add_enum(env: &mut Environment, name: &str, c0: &str, c1: &str) {
    let ind = Name::from_string(name);
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: ind.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string(c0),
                    type_: Expr::const_(ind.clone(), vec![]),
                },
                Constructor {
                    name: Name::from_string(c1),
                    type_: Expr::const_(ind, vec![]),
                },
            ],
        }],
    };
    env.add_inductive(decl)
        .unwrap_or_else(|e| panic!("add_inductive {name} should succeed: {e:?}"));
}

/// Build the `Pick` class + method projection + carrier `B`, then register two
/// `Pick B` instances whose registration order is the OPPOSITE of their
/// priority order — all via the kernel registries, import-style.
///
/// `lo_priority` / `hi_priority` parametrize the two priorities so a second
/// test can flip the registration/priority relationship and confirm the result
/// tracks *priority*, not registration order.
fn imported_priority_env(lo_first_priority: u32, hi_second_priority: u32) -> Environment {
    let mut env = Environment::new();

    // Carrier B with two distinct nullary constructors.
    add_enum(&mut env, "B", "B.lo", "B.hi");

    // class Pick (α : Type) where chosen : α
    //   Pick    : Type → Type
    //   Pick.mk : (α : Type) → α → Pick α
    let pick = Name::from_string("Pick");
    let pick_ty = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
    let mk_ty = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0), // field `chosen : α`
            Expr::app(Expr::const_(pick.clone(), vec![]), Expr::bvar(1)),
        ),
    );
    let pick_decl = InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: pick.clone(),
            type_: pick_ty,
            constructors: vec![Constructor {
                name: Name::from_string("Pick.mk"),
                type_: mk_ty,
            }],
        }],
    };
    env.add_inductive(pick_decl)
        .unwrap_or_else(|e| panic!("add_inductive Pick should succeed: {e:?}"));

    // Pick.chosen : {α : Type} → [self : Pick α] → α := fun {α} [self] => self.0
    let chosen_ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(Expr::const_(pick.clone(), vec![]), Expr::bvar(0)),
            Expr::bvar(1),
        ),
    );
    let chosen_val = Expr::lam(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::lam(
            BinderInfo::InstImplicit,
            Expr::app(Expr::const_(pick.clone(), vec![]), Expr::bvar(0)),
            Expr::proj(pick.clone(), 0, Expr::bvar(0)),
        ),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("Pick.chosen"),
        level_params: vec![],
        type_: chosen_ty,
        value: chosen_val,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("add_decl Pick.chosen should succeed: {e:?}"));

    // Two competing instances, BOTH `: Pick B`, distinct chosen fields.
    let inst_lo_val = Expr::app(Expr::app(const_("Pick.mk"), const_("B")), const_("B.lo"));
    env.add_decl(Declaration::Definition {
        name: Name::from_string("instPickBLo"),
        level_params: vec![],
        type_: Expr::app(Expr::const_(pick.clone(), vec![]), const_("B")),
        value: inst_lo_val,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("add_decl instPickBLo should succeed: {e:?}"));

    let inst_hi_val = Expr::app(Expr::app(const_("Pick.mk"), const_("B")), const_("B.hi"));
    env.add_decl(Declaration::Definition {
        name: Name::from_string("instPickBHi"),
        level_params: vec![],
        type_: Expr::app(Expr::const_(pick.clone(), vec![]), const_("B")),
        value: inst_hi_val,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("add_decl instPickBHi should succeed: {e:?}"));

    env.register_class(KernelClassInfo {
        name: pick.clone(),
        num_params: 1,
        out_params: vec![],
        semi_out_params: vec![],
    });

    // Register LOW priority FIRST, HIGH priority SECOND. If priority is honored,
    // the kernel/elaborator sort moves the HIGH one ahead despite later
    // registration; if registration order leaked through, the LOW one would win.
    env.register_instance(KernelInstanceInfo {
        name: Name::from_string("instPickBLo"),
        class_name: pick.clone(),
        priority: lo_first_priority,
        type_: None,
        value: None,
    });
    env.register_instance(KernelInstanceInfo {
        name: Name::from_string("instPickBHi"),
        class_name: pick,
        priority: hi_second_priority,
        type_: None,
        value: None,
    });

    env
}

/// Elaborate and register `source` against `env`; runs the full kernel check.
fn elaborate_decls_into(env: &mut Environment, source: &str) {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("source should parse");
    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed)
            .unwrap_or_else(|e| panic!("declaration {i} should elaborate and kernel-check: {e}"));
    }
}

// =============================================================================
// Test 1: precondition — the kernel registry exposes BOTH `Pick B` instances,
// highest priority first, with priorities preserved (NOT defaulted/dropped).
// This pins that the import-style registration carried `priority` through and
// that the kernel's priority sort already orders HIGH ahead of LOW even though
// LOW was registered first.
// =============================================================================

#[test]
fn test_imported_priority_kernel_registry_orders_by_priority() {
    let env = imported_priority_env(50, 200);
    let pick = Name::from_string("Pick");

    let instances = env.get_class_instances(&pick);
    assert_eq!(
        instances.len(),
        2,
        "both competing Pick B instances must be registered"
    );

    // Highest priority must come first regardless of registration order.
    assert_eq!(
        instances[0].name,
        Name::from_string("instPickBHi"),
        "the kernel registry must order the higher-priority instance first \
         (it was registered SECOND, so this fails if registration order leaked)"
    );
    assert_eq!(
        instances[0].priority, 200,
        "the high-priority instance's priority must be preserved, not defaulted"
    );
    assert_eq!(
        instances[1].priority, 50,
        "the low-priority instance's priority must be preserved, not defaulted"
    );
    assert!(
        instances
            .iter()
            .all(|i| i.type_.is_none() && i.value.is_none()),
        "imported instances carry no type_/value; the elaborator reconstructs \
         them from env.get_const (the #443 import path)"
    );
}

// =============================================================================
// Test 2: control — the two instance constants reduce to DISTINCT constructors,
// so a mis-selection in Test 3 is observable as a wrong head rather than a
// silent pass. Isolates any Test-3 failure to instance *priority resolution*,
// not to kernel reduction or the hand-built layout.
// =============================================================================

#[test]
fn test_imported_priority_instances_are_distinct() {
    let env = imported_priority_env(50, 200);

    let proj_lo = Expr::proj(Name::from_string("Pick"), 0, const_("instPickBLo"));
    assert_eq!(
        whnf_head_const(&env, &proj_lo).as_deref(),
        Some("B.lo"),
        "Proj(Pick, 0, instPickBLo) must reduce to B.lo"
    );

    let proj_hi = Expr::proj(Name::from_string("Pick"), 0, const_("instPickBHi"));
    assert_eq!(
        whnf_head_const(&env, &proj_hi).as_deref(),
        Some("B.hi"),
        "Proj(Pick, 0, instPickBHi) must reduce to B.hi"
    );
}

// =============================================================================
// Test 3: THE PROBE. A clean-elab-elaborated def that uses `Pick.chosen`
// without naming an instance, for carrier `B` which has TWO competing imported
// instances, must synthesize the HIGHER-priority one and reduce to `B.hi`.
// The low-priority instance was registered first, so a registration-order /
// dropped-priority bug would reduce to `B.lo` instead.
// =============================================================================

#[test]
fn test_method_call_on_imported_instance_respects_priority() {
    let mut env = imported_priority_env(50, 200);

    elaborate_decls_into(&mut env, "def pickedByPriority : B := Pick.chosen");

    let info = env
        .get_const(&Name::from_string("pickedByPriority"))
        .expect("pickedByPriority should be registered after elaboration");
    let body = info
        .value
        .as_ref()
        .expect("pickedByPriority is a definition with a body");

    // Lean keeps the synthesized instance as the constant `instPickBHi`; its
    // `Pick.mk B B.hi` body unfolds only when the method projection reduces.
    let referenced = body.collect_constants();
    assert!(
        referenced.contains(&Name::from_string("Pick.chosen")),
        "body should go through the imported method projection Pick.chosen, got: {referenced:?}"
    );
    assert!(
        referenced.contains(&Name::from_string("instPickBHi"))
            && !referenced.contains(&Name::from_string("Pick.mk"))
            && !referenced.contains(&Name::from_string("B.hi")),
        "body should retain the HIGH-priority imported instance constant, got: {referenced:?}"
    );
    assert!(
        !referenced.contains(&Name::from_string("instPickBLo"))
            && !referenced.contains(&Name::from_string("B.lo")),
        "the LOW-priority instance must NOT be selected, got: {referenced:?}"
    );

    assert_eq!(
        whnf_head_const(&env, &const_("pickedByPriority")).as_deref(),
        Some("B.hi"),
        "pickedByPriority := (Pick.chosen : B) must reduce to B.hi — the HIGHER-priority \
         imported instance — even though the LOW-priority instance was registered first"
    );
}

// =============================================================================
// Test 4: the symmetric case — flip the priorities so the FIRST-registered
// instance is now the HIGH-priority one. Resolution must then yield `B.lo`.
// Together with Test 3 this proves the result tracks PRIORITY specifically and
// is not an artifact of registration order coinciding with the right answer.
// =============================================================================

#[test]
fn test_method_call_on_imported_instance_priority_flip() {
    // instPickBLo registered first now has the HIGH priority (200);
    // instPickBHi registered second has the LOW priority (50).
    let mut env = imported_priority_env(200, 50);

    elaborate_decls_into(&mut env, "def pickedFlip : B := Pick.chosen");

    let info = env
        .get_const(&Name::from_string("pickedFlip"))
        .expect("pickedFlip should be registered after elaboration");
    let referenced = info
        .value
        .as_ref()
        .expect("pickedFlip is a definition with a body")
        .collect_constants();
    assert!(
        referenced.contains(&Name::from_string("instPickBLo"))
            && !referenced.contains(&Name::from_string("B.lo")),
        "with priorities flipped, the now-HIGH-priority instPickBLo constant must win, \
         got: {referenced:?}"
    );
    assert!(
        !referenced.contains(&Name::from_string("instPickBHi"))
            && !referenced.contains(&Name::from_string("B.hi")),
        "the now-LOW-priority instPickBHi must NOT be selected, got: {referenced:?}"
    );

    assert_eq!(
        whnf_head_const(&env, &const_("pickedFlip")).as_deref(),
        Some("B.lo"),
        "with priorities flipped, pickedFlip must reduce to B.lo (the higher-priority instance)"
    );
}
