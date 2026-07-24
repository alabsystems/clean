// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: INSERTING an IMPORTED `Coe` coercion instance.
//!
//! This is the coercion analogue of the imported-`match` (B43),
//! imported-structure-projection (B44), and imported-instance-method probes
//! (`import_e2e_instance_method_tests.rs`). Those found cases where clean-elab's
//! lowering assumed *native* clean-side metadata that a real Lean `.olean` does
//! not carry. Here we exercise coercion *insertion*: when an `A` is used where a
//! `B` is expected, the elaborator must find an imported `Coe A B` instance and
//! wrap the term so it reduces to `coe applied to the A`.
//!
//! ## What "imported" means here (and why we synthesize it by hand)
//!
//! A real Lean `.olean` carries no clean-side native-`class`-command metadata.
//! The importer (`clean_olean::import::load_register`) materializes a typeclass
//! purely through the *kernel* registries:
//!
//! 1. The `@[class]` structure `Coe` is a plain single-constructor inductive
//!    (`register_class` with empty `out_params`/`semi_out_params`, `num_params`
//!    read off the inductive). No `register_structure_fields` table is created.
//! 2. The method projection (`Coe.coe`) is a plain imported `def` whose body is
//!    a kernel `Proj`, exactly like Lean's own projection functions.
//! 3. Each instance is registered via `register_instance` with
//!    `type_: None, value: None`; the elaborator reconstructs the instance from
//!    `env.get_const(name)` (see `infer/elab_init.rs::init_instances_from_env`,
//!    #443).
//!
//! We reproduce *exactly* that configuration with the same primitive kernel APIs
//! the importer calls, and *deliberately do not* register any clean-side
//! coercion-attribute / structure-field metadata. This is faithful to the import
//! path: an imported `Coe` instance is only visible through the kernel instance
//! registry, NOT through any `@[coe]` attribute table (the importer never runs
//! the `@[coe]` attribute handler over imported decls).
//!
//! ## The carriers, the class, and the coercion
//!
//! Carrier `A : Type` has one value `A.a`. Target `B : Type` is a
//! two-constructor enum (`B.b1`, `B.b2`) — distinct nullary values so a wrong
//! coercion / wrong projection is *observable* in the reduced head constructor.
//!
//! Class `Coe (α β : Type)` has a single method field `coe : α → β`. Its
//! projection is `Coe.coe : {α β : Type} → [self : Coe α β] → α → β`, body
//! `fun {α β} [self] => self.0` (`Proj("Coe", 0, self)`).
//!
//! The coercion function `aToB : A → B := fun _ => B.b2` always yields `B.b2`
//! (NOT `B.b1`), so a coercion that landed on the wrong constructor is visible.
//!
//! Instance `instCoeAB : Coe A B := Coe.mk A B aToB`.
//!
//! A decoy target `D : Type` (value `D.d1`) with its own coercion
//! `aToD : A → D := fun _ => D.d1` and instance `instCoeAD : Coe A D :=
//! Coe.mk A D aToD` is also registered, so coercion insertion must
//! *discriminate by the target type* rather than grabbing the first `Coe A _`
//! instance.
//!
//! ## The end-to-end def under test
//!
//! ```text
//! def coercedB : B := (A.a : B)   -- A.a : A used where B is expected
//! ```
//!
//! The inner ascription `(A.a : B)` makes the elaborator unify `A` with the
//! expected `B`; that fails, so it must consult coercion insertion, find the
//! imported `Coe A B` instance (NOT the decoy `Coe A D`), and wrap `A.a` so the
//! whole thing reduces — through the imported instance's reconstructed body and
//! the kernel `Proj` reduction — to `B.b2`.

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
/// its name. Used to observe which constructor the coercion reduces to.
fn whnf_head_const(env: &Environment, expr: &Expr) -> Option<String> {
    let tc = TypeChecker::new(env);
    let reduced = tc.whnf(expr);
    match reduced.kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

/// Add a nullary single-constructor enum inductive `name : Type` with the given
/// constructor `: name`.
fn add_unit_enum(env: &mut Environment, name: &str, ctor: &str) {
    let ind = Name::from_string(name);
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: ind.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string(ctor),
                type_: Expr::const_(ind, vec![]),
            }],
        }],
    };
    env.add_inductive(decl)
        .unwrap_or_else(|e| panic!("add_inductive {name} should succeed: {e:?}"));
}

/// Add a nullary two-constructor enum inductive `name : Type`.
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

/// Build an environment containing the `Coe` typeclass, its `coe` method
/// projection, the carriers (`A`, `B`, decoy `D`), two coercion functions, and
/// two instances — all registered *exactly the way `clean_olean` import does*
/// (kernel registries only, `register_instance { type_: None, value: None }`,
/// and NO `register_structure_fields`, NO `@[coe]` attribute table).
fn imported_coe_env() -> Environment {
    let mut env = Environment::new();

    // Carriers: source A (a), target B (b1, b2), decoy target D (d1).
    add_unit_enum(&mut env, "A", "A.a");
    add_enum(&mut env, "B", "B.b1", "B.b2");
    add_unit_enum(&mut env, "D", "D.d1");

    // class Coe (α β : Type) where coe : α → β
    //
    // As a kernel inductive (single constructor, two explicit type parameters):
    //   Coe : Type → Type → Type
    //   Coe.mk : (α β : Type) → (α → β) → Coe α β
    let coe = Name::from_string("Coe");
    let coe_ty = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
    );
    // Coe.mk : (α β : Type) → (α → β) → Coe α β
    //   Under the two type binders, bvar 1 = α, bvar 0 = β.
    //   The field is `α → β` = Pi(bvar 2 = α (shifted under the field binder is
    //   not needed; field type is a non-dependent arrow so use bvar indices
    //   relative to its own scope): we build `α → β` as Pi(_ : α, β).
    //   In the constructor's scope (under α, β): α = bvar 1, β = bvar 0.
    //   The arrow `α → β` adds one binder, so inside the arrow body β = bvar 1.
    let field_arrow = Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(1));
    let mk_ty = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::type_(),
            Expr::pi(
                BinderInfo::Default,
                field_arrow,
                // Result: Coe α β.  Under (α, β, field), α = bvar 2, β = bvar 1.
                Expr::app(
                    Expr::app(Expr::const_(coe.clone(), vec![]), Expr::bvar(2)),
                    Expr::bvar(1),
                ),
            ),
        ),
    );
    let coe_decl = InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: coe.clone(),
            type_: coe_ty,
            constructors: vec![Constructor {
                name: Name::from_string("Coe.mk"),
                type_: mk_ty,
            }],
        }],
    };
    env.add_inductive(coe_decl)
        .unwrap_or_else(|e| panic!("add_inductive Coe should succeed: {e:?}"));

    // Method projection, as the importer carries it (a plain def whose body is a
    // kernel Proj):
    //   Coe.coe : {α β : Type} → [self : Coe α β] → α → β
    //   Coe.coe := fun {α β} [self] => self.0
    // Under (α, β, self): α = bvar 2, β = bvar 1, self = bvar 0 (when fully
    // bound). The result type `α → β` lives under the three binders.
    let coe_self_ty = Expr::app(
        Expr::app(Expr::const_(coe.clone(), vec![]), Expr::bvar(1)),
        Expr::bvar(0),
    );
    let chosen_ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Implicit,
            Expr::type_(),
            Expr::pi(
                BinderInfo::InstImplicit,
                coe_self_ty,
                // result type `α → β`: under (α, β, self), α = bvar 2, β = bvar 1.
                Expr::pi(BinderInfo::Default, Expr::bvar(2), Expr::bvar(2)),
            ),
        ),
    );
    let chosen_self_ty_val = Expr::app(
        Expr::app(Expr::const_(coe.clone(), vec![]), Expr::bvar(1)),
        Expr::bvar(0),
    );
    let chosen_val = Expr::lam(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::lam(
            BinderInfo::Implicit,
            Expr::type_(),
            Expr::lam(
                BinderInfo::InstImplicit,
                chosen_self_ty_val,
                // self.0 : α → β  (self is bvar 0 under the three lambdas)
                Expr::proj(coe.clone(), 0, Expr::bvar(0)),
            ),
        ),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("Coe.coe"),
        level_params: vec![],
        type_: chosen_ty,
        value: chosen_val,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("add_decl Coe.coe should succeed: {e:?}"));

    // aToB : A → B := fun _ => B.b2
    env.add_decl(Declaration::Definition {
        name: Name::from_string("aToB"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, const_("A"), const_("B")),
        value: Expr::lam(BinderInfo::Default, const_("A"), const_("B.b2")),
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("add_decl aToB should succeed: {e:?}"));

    // aToD : A → D := fun _ => D.d1  (decoy coercion, different target)
    env.add_decl(Declaration::Definition {
        name: Name::from_string("aToD"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, const_("A"), const_("D")),
        value: Expr::lam(BinderInfo::Default, const_("A"), const_("D.d1")),
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("add_decl aToD should succeed: {e:?}"));

    // instCoeAB : Coe A B := Coe.mk A B aToB
    let inst_ab_val = Expr::app(
        Expr::app(Expr::app(const_("Coe.mk"), const_("A")), const_("B")),
        const_("aToB"),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("instCoeAB"),
        level_params: vec![],
        type_: Expr::app(
            Expr::app(Expr::const_(coe.clone(), vec![]), const_("A")),
            const_("B"),
        ),
        value: inst_ab_val,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("add_decl instCoeAB should succeed: {e:?}"));

    // instCoeAD : Coe A D := Coe.mk A D aToD  (decoy; different target)
    let inst_ad_val = Expr::app(
        Expr::app(Expr::app(const_("Coe.mk"), const_("A")), const_("D")),
        const_("aToD"),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("instCoeAD"),
        level_params: vec![],
        type_: Expr::app(
            Expr::app(Expr::const_(coe.clone(), vec![]), const_("A")),
            const_("D"),
        ),
        value: inst_ad_val,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("add_decl instCoeAD should succeed: {e:?}"));

    // Register the class + instances through the kernel registries the way the
    // importer's `register_classes_from_extension` /
    // `register_instances_from_extension` do. Crucially: NO
    // `register_structure_fields`, and the instances are registered with
    // `type_: None, value: None` so the elaborator must reconstruct them from
    // `env.get_const(name)`.
    env.register_class(KernelClassInfo {
        name: coe.clone(),
        num_params: 2,
        out_params: vec![],
        semi_out_params: vec![],
    });
    env.register_instance(KernelInstanceInfo {
        name: Name::from_string("instCoeAB"),
        class_name: coe.clone(),
        priority: clean_kernel::DEFAULT_INSTANCE_PRIORITY,
        type_: None,
        value: None,
    });
    env.register_instance(KernelInstanceInfo {
        name: Name::from_string("instCoeAD"),
        class_name: coe,
        priority: clean_kernel::DEFAULT_INSTANCE_PRIORITY,
        type_: None,
        value: None,
    });

    env
}

/// Elaborate and register `source` against `env`, threading a `FileContext`.
/// `elaborate_decl_and_register` runs the full kernel type check.
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
// Test 1: the imported class + projection + instances were registered the way
// the importer does, with NO clean-side coercion-attribute / structure-field
// table. This pins the precondition: an imported `Coe` is ONLY visible through
// the kernel instance registry.
// =============================================================================

#[test]
fn test_imported_coe_env_registered_through_kernel_registry() {
    let env = imported_coe_env();
    let coe = Name::from_string("Coe");

    assert!(
        env.is_class(&coe),
        "Coe should be a registered class (via register_class, import-style)"
    );
    assert!(
        env.get_structure_field_names(&coe).is_none(),
        "imported class must NOT carry a clean-side structure_fields table"
    );

    let instances = env.get_class_instances(&coe);
    assert_eq!(instances.len(), 2, "two Coe instances are registered");
    assert!(
        instances
            .iter()
            .all(|i| i.type_.is_none() && i.value.is_none()),
        "imported instances carry no type_/value; the elaborator reconstructs \
         them from env.get_const (the #443 import path)"
    );

    assert!(
        env.get_const(&Name::from_string("instCoeAB")).is_some()
            && env.get_const(&Name::from_string("Coe.coe")).is_some(),
        "the instance constant and the method projection must both be present"
    );
}

// =============================================================================
// Test 2: control — the imported `Coe.coe` projection, applied to the imported
// instance and an `A`, reduces to the correct `B` value at the KERNEL level.
// This isolates any failure in Test 3 to coercion *insertion* (elaboration),
// not to kernel reduction or the hand-built layout.
// =============================================================================

#[test]
fn test_imported_coe_kernel_reduction_is_sound() {
    let env = imported_coe_env();

    // Projecting field 0 of the instance yields the coercion function, applied
    // to A.a it must reduce to B.b2.
    //   @Coe.coe A B instCoeAB A.a  ==>  (Proj Coe 0 instCoeAB) A.a
    //                              ==>  aToB A.a  ==>  B.b2
    let coe_applied = Expr::app(
        Expr::app(
            Expr::app(Expr::app(const_("Coe.coe"), const_("A")), const_("B")),
            const_("instCoeAB"),
        ),
        const_("A.a"),
    );
    assert_eq!(
        whnf_head_const(&env, &coe_applied).as_deref(),
        Some("B.b2"),
        "Coe.coe A B instCoeAB A.a must reduce to B.b2 through the imported projection"
    );

    // The decoy coercion for D reduces to D.d1 — confirms the two instances are
    // genuinely distinct so a mis-selection in Test 3 would be observable.
    let coe_applied_d = Expr::app(
        Expr::app(
            Expr::app(Expr::app(const_("Coe.coe"), const_("A")), const_("D")),
            const_("instCoeAD"),
        ),
        const_("A.a"),
    );
    assert_eq!(
        whnf_head_const(&env, &coe_applied_d).as_deref(),
        Some("D.d1"),
        "Coe.coe A D instCoeAD A.a must reduce to D.d1"
    );
}

// =============================================================================
// Test 3: THE PROBE. A clean-elab-elaborated def that uses an `A` where a `B`
// is expected must (a) find and insert the IMPORTED `Coe A B` coercion, and
// (b) reduce — through that imported coercion — to the CORRECT result (B.b2).
// A decoy `Coe A D` makes a wrong target selection observable.
// =============================================================================

#[test]
fn test_coercion_insertion_uses_imported_coe_instance_and_reduces_correctly() {
    let mut env = imported_coe_env();

    // The inner ascription `(A.a : B)` forces a type mismatch (A vs B); the
    // elaborator must consult coercion insertion, find the imported `Coe A B`
    // instance via the kernel-registry-backed InstanceTable, and wrap A.a.
    elaborate_decls_into(&mut env, "def coercedB : B := (A.a : B)");

    let info = env
        .get_const(&Name::from_string("coercedB"))
        .expect("coercedB should be registered after elaboration");
    let body = info
        .value
        .as_ref()
        .expect("coercedB is a definition with a body");

    // The elaborated body must go through the imported coercion machinery:
    // `Coe.coe` (the projection) applied to the synthesized imported instance,
    // whose reconstructed content names `Coe.mk` and the target-B coercion fn
    // `aToB` — NOT the decoy target D's `aToD`.
    let referenced = body.collect_constants();
    assert!(
        referenced.contains(&Name::from_string("Coe.coe")),
        "coercedB's body should go through the imported coercion projection Coe.coe, \
         got: {referenced:?}"
    );
    assert!(
        referenced.contains(&Name::from_string("aToB")),
        "coercedB's body should inline the synthesized IMPORTED Coe A B instance \
         (which references the B-targeting coercion fn aToB), got: {referenced:?}"
    );
    assert!(
        !referenced.contains(&Name::from_string("aToD"))
            && !referenced.contains(&Name::from_string("D")),
        "coercion insertion must NOT pull in the decoy target D's coercion content, \
         got: {referenced:?}"
    );

    // The payoff: reduce the elaborated def. It must land on B.b2 — the value
    // the imported A→B coercion produces. A wrong coercion (the decoy for D)
    // would fail to type-check against `: B`; a stuck or mis-projected coercion
    // would surface here as the wrong head rather than passing silently.
    assert_eq!(
        whnf_head_const(&env, &const_("coercedB")).as_deref(),
        Some("B.b2"),
        "coercedB := (A.a : B) must reduce to B.b2 through the imported Coe A B coercion"
    );
}

// =============================================================================
// Test 4: the symmetric case — an `A` used where the DECOY target `D` is
// expected must insert the imported `Coe A D` coercion (NOT `Coe A B`) and
// reduce to D.d1. Together with Test 3 this proves coercion insertion genuinely
// discriminates by *target* type rather than grabbing the first `Coe A _`
// instance — the exact trap a native-metadata assumption could fall into.
// =============================================================================

#[test]
fn test_coercion_insertion_discriminates_target_type() {
    let mut env = imported_coe_env();
    elaborate_decls_into(&mut env, "def coercedD : D := (A.a : D)");

    let info = env
        .get_const(&Name::from_string("coercedD"))
        .expect("coercedD should be registered after elaboration");
    let referenced = info
        .value
        .as_ref()
        .expect("coercedD is a definition with a body")
        .collect_constants();
    assert!(
        referenced.contains(&Name::from_string("Coe.coe"))
            && referenced.contains(&Name::from_string("aToD")),
        "coercedD : D must insert the imported Coe A D coercion (referencing aToD), \
         got: {referenced:?}"
    );
    assert!(
        !referenced.contains(&Name::from_string("aToB"))
            && !referenced.contains(&Name::from_string("B")),
        "coercedD : D must NOT pull in target B's coercion content, got: {referenced:?}"
    );

    assert_eq!(
        whnf_head_const(&env, &const_("coercedD")).as_deref(),
        Some("D.d1"),
        "coercedD := (A.a : D) must reduce to D.d1 through the imported Coe A D coercion"
    );
}
