// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: an IMPORTED class that EXTENDS a parent class, used where the
//! PARENT is needed.
//!
//! This is the marquee imported-usage path for real Mathlib: Mathlib's entire
//! algebraic hierarchy is `class extends` (`Monoid extends Semigroup`,
//! `CommRing extends Ring`, …). When a `.olean` is imported, a child class
//! `C2 extends C1` becomes a plain Lean inductive whose constructor carries the
//! parent instance as a field, plus a **parent-projection** `C2.toC1` that Lean
//! generates and marks `@[instance]`. Instance synthesis for a `C1` goal must
//! traverse `inst2 : C2 T  ->  C2.toC1  ->  C1 T`, i.e. resolve the *child*
//! instance as a nested dependency of the parent projection.
//!
//! ## What "imported" means here (and why we synthesize it by hand)
//!
//! Following the sibling probe `import_e2e_instance_method_tests.rs`, we
//! reproduce *exactly* the configuration a real `.olean` produces, going only
//! through the kernel registries the importer calls
//! (`clean_olean::import::load_register`):
//!
//! 1. The `@[class]` structures `C1`/`C2` are plain single-constructor
//!    inductives registered via `register_class` (`out_params`/`semi_out_params`
//!    empty, `num_params` read off the inductive). No `register_structure_fields`
//!    table — that is a *native*-command-only artifact (the gap B44 hit).
//! 2. Each method/parent projection (`C1.m1`, `C2.toC1`) is a plain imported
//!    `def` whose body is a kernel `Proj`, exactly like Lean's own projection
//!    functions.
//! 3. Each instance — including the parent projection `C2.toC1`, which Lean
//!    registers `@[instance]` — is registered via `register_instance` with
//!    `type_: None, value: None`; the elaborator reconstructs the instance
//!    type and keeps the Lean-faithful constant expression from
//!    `env.get_const(name)` (see
//!    `clean_elab::infer::init_instances_from_env`, #443).
//!
//! Crucially, we do NOT call the native `class … extends …` elaborator, which
//! would register `C2.toC1` *with* its `type_`/`value` carrying
//! Implicit/InstImplicit binders (the path `test_issue140_typeclass_inheritance_extends`
//! covers). On import there is no such override: the instance is reconstructed
//! from the imported const's own signature.
//!
//! ## The carriers, classes, parent projection, and the method
//!
//! Carrier `T : Type` is a two-constructor enum (`T.a`, `T.b`) — distinct nullary
//! values so a wrong instance / wrong projection is *observable* in the reduced
//! head constructor rather than passing silently (the trap B43 fell into).
//!
//! Parent class `C1 (α : Type)` has a single method field `m1 : α → α`. Its
//! projection `C1.m1 : {α : Type} → [self : C1 α] → α → α` has body
//! `fun {α} [self] => Proj(C1, 0, self)`.
//!
//! Child class `C2 (α : Type) extends C1 α` — as a kernel inductive its
//! constructor is `C2.mk : (α) → (toC1 : C1 α) → (extra : α) → C2 α`, so the
//! parent `C1 α` is field 0. The parent projection is
//! `C2.toC1 : {α : Type} → [self : C2 α] → C1 α`, body
//! `fun {α} [self] => Proj(C2, 0, self)`, registered `@[instance]`.
//!
//! Instance `inst2 : C2 T := C2.mk T (C1.mk T m1impl) T.a`, where `m1impl`
//! maps everything to `T.b`. So `m1` applied to any `T` through this hierarchy
//! must reduce to `T.b`.
//!
//! ## The end-to-end probe
//!
//! ```text
//! def parentM1 : T := C1.m1 T.a
//! ```
//!
//! No instance is named. The `: T` annotation pins the carrier `α := T`.
//! Instance synthesis must find a `C1 T` instance — and the ONLY way is via the
//! imported parent projection: `C2.toC1` is a `C1` instance whose own signature
//! demands a nested `[self : C2 T]`, which synthesis resolves to `inst2`. The
//! whole thing must reduce — through the imported parent projection and the
//! kernel `Proj` reductions — to `T.b` (the result of `m1impl` applied to
//! `T.a`), NOT get stuck on an unresolved `self` metavariable and NOT land on
//! the wrong constructor.

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
/// its name. Used to observe which constructor the imported method reduces to.
fn whnf_head_const(env: &Environment, expr: &Expr) -> Option<String> {
    let tc = TypeChecker::new(env);
    let reduced = tc.whnf(expr);
    match reduced.kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

/// Reduce `expr` to weak-head normal form, then return the name of the head
/// constant of the resulting application spine (`get_app_fn`). Unlike
/// [`whnf_head_const`], this sees through applied constructors such as
/// `C1.mk T m1impl` (head `C1.mk`), where the WHNF is an `App`, not a bare
/// `Const`.
fn whnf_app_head_const(env: &Environment, expr: &Expr) -> Option<String> {
    let tc = TypeChecker::new(env);
    let reduced = tc.whnf(expr);
    match reduced.get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

/// Add a nullary, two-constructor enum inductive `name : Type` with the two
/// given constructor names, both `: name`.
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

/// `C1 α` applied to a carrier expression.
fn c1_of(carrier: Expr) -> Expr {
    Expr::app(const_("C1"), carrier)
}

/// `C2 α` applied to a carrier expression.
fn c2_of(carrier: Expr) -> Expr {
    Expr::app(const_("C2"), carrier)
}

/// Build an environment containing the imported class hierarchy:
/// parent class `C1` (method `m1`), child class `C2 extends C1`, the carrier
/// enum `T`, and a single instance `inst2 : C2 T` — all registered *exactly the
/// way `clean_olean` import does* (kernel registries only,
/// `register_instance { type_: None, value: None }`, NO
/// `register_structure_fields`, and the parent projection `C2.toC1` registered
/// `@[instance]`).
fn imported_class_hierarchy_env() -> Environment {
    let mut env = Environment::new();

    // Carrier: T (a, b). Distinct nullary constructors so a wrong reduction is
    // observable.
    add_enum(&mut env, "T", "T.a", "T.b");

    // ---- Parent class C1 (α : Type) where m1 : α → α --------------------------
    //   C1 : Type → Type
    //   C1.mk : (α : Type) → (α → α) → C1 α
    let c1 = Name::from_string("C1");
    let c1_ty = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
    let c1_mk_ty = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            // field `m1 : α → α`
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
            Expr::app(const_("C1"), Expr::bvar(1)),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: c1.clone(),
            type_: c1_ty,
            constructors: vec![Constructor {
                name: Name::from_string("C1.mk"),
                type_: c1_mk_ty,
            }],
        }],
    })
    .unwrap_or_else(|e| panic!("add_inductive C1 should succeed: {e:?}"));

    // ---- Child class C2 (α : Type) extends C1 α -------------------------------
    // As a kernel inductive the parent becomes the first field of the
    // constructor:
    //   C2 : Type → Type
    //   C2.mk : (α : Type) → (toC1 : C1 α) → (extra : α) → C2 α
    let c2 = Name::from_string("C2");
    let c2_ty = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
    let c2_mk_ty = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            // field 0: `toC1 : C1 α`
            Expr::app(const_("C1"), Expr::bvar(0)),
            Expr::pi(
                BinderInfo::Default,
                // field 1: `extra : α`
                Expr::bvar(1),
                Expr::app(const_("C2"), Expr::bvar(2)),
            ),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: c2.clone(),
            type_: c2_ty,
            constructors: vec![Constructor {
                name: Name::from_string("C2.mk"),
                type_: c2_mk_ty,
            }],
        }],
    })
    .unwrap_or_else(|e| panic!("add_inductive C2 should succeed: {e:?}"));

    // ---- Method projection C1.m1 (imported as a plain def whose body is Proj) --
    //   C1.m1 : {α : Type} → [self : C1 α] → α → α
    //   C1.m1 := fun {α} [self] => Proj(C1, 0, self)
    let m1_ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(
            BinderInfo::InstImplicit,
            c1_of(Expr::bvar(0)),
            // result: α → α
            Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(2)),
        ),
    );
    let m1_val = Expr::lam(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::lam(
            BinderInfo::InstImplicit,
            c1_of(Expr::bvar(0)),
            // self.0 : α → α  (self is bvar 0 under the two lambdas)
            Expr::proj(c1.clone(), 0, Expr::bvar(0)),
        ),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("C1.m1"),
        level_params: vec![],
        type_: m1_ty,
        value: m1_val,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("add_decl C1.m1 should succeed: {e:?}"));

    // ---- Parent projection C2.toC1 (imported, plain def whose body is Proj) ----
    //   C2.toC1 : {α : Type} → [self : C2 α] → C1 α
    //   C2.toC1 := fun {α} [self] => Proj(C2, 0, self)
    //
    // This faithfully mirrors what Lean emits for an `extends` parent: a
    // projection function carrying the *implicit* type parameter and an
    // *instance-implicit* self, registered `@[instance]`.
    let to_c1_ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(
            BinderInfo::InstImplicit,
            c2_of(Expr::bvar(0)),
            // result: C1 α
            c1_of(Expr::bvar(1)),
        ),
    );
    let to_c1_val = Expr::lam(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::lam(
            BinderInfo::InstImplicit,
            c2_of(Expr::bvar(0)),
            Expr::proj(c2.clone(), 0, Expr::bvar(0)),
        ),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("C2.toC1"),
        level_params: vec![],
        type_: to_c1_ty,
        value: to_c1_val,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("add_decl C2.toC1 should succeed: {e:?}"));

    // ---- The single instance: inst2 : C2 T -----------------------------------
    //   m1impl : T → T := fun _ => T.b   (constant function landing on T.b)
    //   inst2  : C2 T  := C2.mk T (C1.mk T m1impl) T.a
    let m1impl = Expr::lam(BinderInfo::Default, const_("T"), const_("T.b"));
    let c1_inst = Expr::app(Expr::app(const_("C1.mk"), const_("T")), m1impl);
    let inst2_val = Expr::app(
        Expr::app(Expr::app(const_("C2.mk"), const_("T")), c1_inst),
        const_("T.a"),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("inst2"),
        level_params: vec![],
        type_: c2_of(const_("T")),
        value: inst2_val,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("add_decl inst2 should succeed: {e:?}"));

    // ---- Register classes + instances the import way --------------------------
    env.register_class(KernelClassInfo {
        name: c1.clone(),
        num_params: 1,
        out_params: vec![],
        semi_out_params: vec![],
    });
    env.register_class(KernelClassInfo {
        name: c2.clone(),
        num_params: 1,
        out_params: vec![],
        semi_out_params: vec![],
    });
    // The child instance.
    env.register_instance(KernelInstanceInfo {
        name: Name::from_string("inst2"),
        class_name: c2,
        priority: clean_kernel::DEFAULT_INSTANCE_PRIORITY,
        type_: None,
        value: None,
    });
    // The parent projection registered `@[instance]` (this is what Lean does for
    // an `extends` parent: `C2.toC1` is an instance of class `C1`).
    env.register_instance(KernelInstanceInfo {
        name: Name::from_string("C2.toC1"),
        class_name: c1,
        priority: clean_kernel::DEFAULT_INSTANCE_PRIORITY,
        type_: None,
        value: None,
    });

    env
}

/// Elaborate and register `source` against `env`, threading a `FileContext`.
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
// Test 1: precondition — the imported class hierarchy was registered the way the
// importer does, and the parent projection is visible as a C1 instance.
// =============================================================================

#[test]
fn test_imported_class_hierarchy_registered_through_kernel_registry() {
    let env = imported_class_hierarchy_env();
    let c1 = Name::from_string("C1");
    let c2 = Name::from_string("C2");

    assert!(
        env.is_class(&c1) && env.is_class(&c2),
        "C1 and C2 are classes"
    );
    assert!(
        env.get_structure_field_names(&c1).is_none()
            && env.get_structure_field_names(&c2).is_none(),
        "imported classes must NOT carry a clean-side structure_fields table"
    );

    // The parent projection C2.toC1 must be registered as a C1 instance — this is
    // the bridge that lets a C1 goal be satisfied from a C2 instance.
    let c1_instances = env.get_class_instances(&c1);
    assert!(
        c1_instances
            .iter()
            .any(|i| i.name == Name::from_string("C2.toC1")),
        "C2.toC1 must be registered as a C1 instance (the @[instance] parent projection); got: {:?}",
        c1_instances.iter().map(|i| i.name.to_string()).collect::<Vec<_>>()
    );
    assert!(
        c1_instances
            .iter()
            .all(|i| i.type_.is_none() && i.value.is_none()),
        "imported instances carry no type_/value; the elaborator reconstructs them \
         from env.get_const (the #443 import path)"
    );

    let c2_instances = env.get_class_instances(&c2);
    assert!(
        c2_instances
            .iter()
            .any(|i| i.name == Name::from_string("inst2")),
        "inst2 must be registered as a C2 instance"
    );
}

// =============================================================================
// Test 2: control — kernel reduction through the hand-built hierarchy is sound,
// isolating any Test 3 failure to instance *synthesis* rather than kernel
// reduction or the layout. We apply C1.m1 to the parent projected out of inst2.
// =============================================================================

#[test]
fn test_imported_class_hierarchy_kernel_reduction_is_sound() {
    let env = imported_class_hierarchy_env();

    // C2.toC1 inst2 reduces to the C1 instance inside inst2 (Proj field 0 of
    // C2.mk T (C1.mk T m1impl) T.a == C1.mk T m1impl).
    let to_c1_applied = Expr::app(Expr::app(const_("C2.toC1"), const_("T")), const_("inst2"));
    assert_eq!(
        whnf_app_head_const(&env, &to_c1_applied).as_deref(),
        Some("C1.mk"),
        "C2.toC1 T inst2 must reduce to the embedded C1.mk parent instance"
    );

    // Fully manual chain: C1.m1 T (C2.toC1 T inst2) T.a must reduce to T.b,
    // through the parent projection and the m1impl constant function.
    let manual_chain = Expr::app(
        Expr::app(Expr::app(const_("C1.m1"), const_("T")), to_c1_applied),
        const_("T.a"),
    );
    assert_eq!(
        whnf_head_const(&env, &manual_chain).as_deref(),
        Some("T.b"),
        "C1.m1 T (C2.toC1 T inst2) T.a must reduce to T.b through the imported hierarchy"
    );
}

// =============================================================================
// Test 3: THE PROBE. A clean-elab-elaborated def calls the parent method `m1`
// WITHOUT naming an instance. Instance synthesis must traverse the imported
// parent projection (inst2 : C2 T -> C2.toC1 -> C1 T) and the result must
// reduce, through that imported hierarchy, to the CORRECT method body (T.b).
// =============================================================================

#[test]
fn test_method_call_through_imported_parent_projection_reduces_correctly() {
    let mut env = imported_class_hierarchy_env();

    // `C1.m1`'s self is a `C1 T` instance-implicit and there is NO direct `C1 T`
    // instance — the only path is through the parent projection `C2.toC1` applied
    // to the child instance `inst2 : C2 T`. The `: T` annotation pins α := T; the
    // argument `T.a` supplies the `α → α` method's input.
    elaborate_decls_into(&mut env, "def parentM1 : T := C1.m1 T.a");

    let info = env
        .get_const(&Name::from_string("parentM1"))
        .expect("parentM1 should be registered after elaboration");
    let body = info
        .value
        .as_ref()
        .expect("parentM1 is a definition with a body");

    // Lean's `synthInstance` keeps instance CONSTANTS in the elaborated term;
    // their bodies unfold only when the projection reduces. The exact chain is
    // therefore `C2.toC1 T inst2`, not beta-inlined `C2.mk`/`C1.mk` content.
    // This is both the discriminating parent-projection path and the term shape
    // the Lean↔Clean bridge requires (#8dfb89bb9).
    let referenced = body.collect_constants();
    assert!(
        referenced.contains(&Name::from_string("C1.m1")),
        "parentM1's body should go through the imported method projection C1.m1, \
         got: {referenced:?}"
    );
    assert!(
        referenced.contains(&Name::from_string("C2.toC1")),
        "instance synthesis must traverse the imported parent projection (C2.toC1) \
         to satisfy the C1 goal from the C2 instance, got: {referenced:?}"
    );
    assert!(
        referenced.contains(&Name::from_string("inst2"))
            && !referenced.contains(&Name::from_string("C2.mk"))
            && !referenced.contains(&Name::from_string("C1.mk")),
        "the child must remain the Lean-faithful inst2 constant until reduction, \
         without inlining either class constructor, got: {referenced:?}"
    );

    // The payoff: reduce the elaborated def. It must land on T.b — the result of
    // the parent method body applied to T.a. A failure to resolve the nested
    // child instance would leave `self` an unassigned metavariable and the term
    // stuck on a Proj (head not a Const); a wrong projection field would surface
    // as the wrong head — neither passes silently.
    assert_eq!(
        whnf_head_const(&env, &const_("parentM1")).as_deref(),
        Some("T.b"),
        "parentM1 := (C1.m1 T.a : T) must reduce to T.b through the imported parent \
         projection C2.toC1 and the child instance inst2"
    );
}
