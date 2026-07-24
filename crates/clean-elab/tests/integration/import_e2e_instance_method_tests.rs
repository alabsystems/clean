// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: USING an IMPORTED typeclass instance's method.
//!
//! This is the typeclass-instance analogue of the imported-`match` (B43) and
//! imported-structure-projection (B44) probes in `import_elab_e2e_tests.rs`.
//! Those found cases where clean-elab's lowering assumed *native* clean-side
//! metadata that a real Lean `.olean` does not carry. Here we exercise the
//! third such surface: resolving and *reducing* a call through an imported
//! instance's method.
//!
//! ## What "imported" means here (and why we synthesize it by hand)
//!
//! A real Lean `.olean` does not carry clean-side native-`class`-command
//! metadata. The importer (`clean_olean::import::load_register`) materializes a
//! typeclass purely through the *kernel* registries:
//!
//! 1. The `@[class]` structure is a plain single-constructor inductive
//!    (`register_classes_from_extension` -> `Environment::register_class` with
//!    `out_params`/`semi_out_params` empty, `num_params` read off the
//!    inductive). No `register_structure_fields` table is created — that is a
//!    *native*-command-only artifact (the same gap B44 hit for projections).
//! 2. Each method projection (`C.m`) is a plain imported `def` whose body is a
//!    kernel `Proj`, exactly like Lean's own projection functions.
//! 3. Each instance is registered via
//!    `register_instances_from_extension` -> `Environment::register_instance`
//!    with `type_: None, value: None`; the elaborator reconstructs the instance
//!    expression from `env.get_const(name)` (see
//!    `clean_elab::infer::init_instances_from_env`, #443).
//!
//! We reproduce *exactly* that configuration by building the kernel decls with
//! the same primitive APIs the importer calls (`add_inductive`, `add_decl`,
//! `register_class`, `register_instance { type_: None, value: None }`) and
//! *deliberately not* calling `register_structure_fields`. This is faithful to
//! the import path and avoids depending on a Lean-version-specific `.olean`
//! fixture for a class (the checked-in fixtures are v4.13.0 and carry no class).
//!
//! ## The carrier and the method
//!
//! Carrier `B : Type` is a two-constructor enum (`B.b1`, `B.b2`) — distinct
//! nullary values so a wrong instance / wrong projection is *observable* in the
//! reduced head constructor rather than passing silently (the trap the B43
//! match bug fell into).
//!
//! Class `Pick (α : Type)` has a single method field `chosen : α`. Its
//! projection is `Pick.chosen : {α : Type} → [self : Pick α] → α`, body
//! `fun {α} [self] => self.0` (`Proj("Pick", 0, self)`).
//!
//! Instance `instPickB : Pick B := Pick.mk B B.b2` — its method yields `B.b2`
//! (NOT `B.b1`), so selecting the right instance *and* the right projection
//! field is required to land on `B.b2`.
//!
//! A decoy carrier `C : Type` with its own instance `instPickC : Pick C :=
//! Pick.mk C C.c1` is also registered, so instance synthesis must *discriminate
//! by the carrier type* rather than blindly grabbing the first `Pick` instance.
//!
//! The end-to-end def under test:
//!
//! ```text
//! def pickedB : B := Pick.chosen   -- (with α := B inferred from the B annotation)
//! ```
//!
//! `Pick.chosen` is a method whose result type *is* the carrier, so the
//! `B` return annotation pins `α := B`, instance synthesis must find
//! `instPickB` (not `instPickC`), and the whole thing must reduce — through the
//! imported instance's reconstructed body and the kernel `Proj` reduction — to
//! `B.b2`.
//!
//! ## The bug this probe found (and the fix)
//!
//! With the carrier `α` left as a metavariable, clean-elab's
//! `apply_implicit_to_expected_type` used to insert the `[self : Pick ?α]`
//! instance-implicit and resolve it *eagerly* (via `insert_implicit_args`)
//! before the expected type had a chance to pin `?α`. Instance resolution then
//! matched the *first* registered `Pick` instance, binding `?α := B`
//! regardless of the goal. For `def pickedC : C := Pick.chosen` that produced a
//! term of type `B` and the kernel rejected it (`expected C, got B`); for
//! `def pickedB : B := ...` it only worked by luck (B was registered first).
//!
//! This is the instance-resolution analogue of the B43/B44 import bugs: a
//! lowering step ran before the information that disambiguates it was
//! available. The fix (in `infer/elab_app.rs` +
//! `infer/elab_app_support.rs`) defers instance-implicit resolution: it fills
//! each instance binder with a metavariable, unifies the result type with the
//! expected type *first* (solving `?α := C` or `?α := B`), and only then
//! resolves the now-ground instance goals — mirroring Lean 4's postponement of
//! typeclass resolution. It falls back to the old eager path (in a speculative
//! metavariable scope) when deferral cannot resolve every instance, so no
//! previously-working elaboration regresses.

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

/// Build an environment that contains the `Pick` typeclass, its method
/// projection, two carrier enums (`B`, `C`) and one instance for each — all
/// registered *exactly the way `clean_olean` import does* (kernel registries
/// only, `register_instance { type_: None, value: None }`, and NO
/// `register_structure_fields`).
fn imported_instance_env() -> Environment {
    let mut env = Environment::new();

    // Carriers: B (b1, b2) and decoy C (c1, c2).
    add_enum(&mut env, "B", "B.b1", "B.b2");
    add_enum(&mut env, "C", "C.c1", "C.c2");

    // class Pick (α : Type) where chosen : α
    //
    // As a kernel inductive (single constructor, one explicit type parameter):
    //   Pick : Type → Type
    //   Pick.mk : (α : Type) → α → Pick α
    let pick = Name::from_string("Pick");
    let pick_ty = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
    // Pick.mk : (α : Type) → α → Pick α
    //   bvar 0 in the field slot refers to α; Pick (bvar 1) refers to α from the
    //   outer binder once we are under the field binder.
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

    // Method projection, as the importer would carry it (a plain def whose body
    // is a kernel Proj):
    //   Pick.chosen : {α : Type} → [self : Pick α] → α
    //   Pick.chosen := fun {α : Type} [self : Pick α] => self.0
    let chosen_ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(Expr::const_(pick.clone(), vec![]), Expr::bvar(0)),
            Expr::bvar(1), // result type α
        ),
    );
    let chosen_val = Expr::lam(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::lam(
            BinderInfo::InstImplicit,
            Expr::app(Expr::const_(pick.clone(), vec![]), Expr::bvar(0)),
            // self.0 : α  (self is bvar 0 under the two lambdas)
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

    // instPickB : Pick B := Pick.mk B B.b2
    let inst_b_val = Expr::app(Expr::app(const_("Pick.mk"), const_("B")), const_("B.b2"));
    env.add_decl(Declaration::Definition {
        name: Name::from_string("instPickB"),
        level_params: vec![],
        type_: Expr::app(Expr::const_(pick.clone(), vec![]), const_("B")),
        value: inst_b_val,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("add_decl instPickB should succeed: {e:?}"));

    // instPickC : Pick C := Pick.mk C C.c1  (decoy; different carrier)
    let inst_c_val = Expr::app(Expr::app(const_("Pick.mk"), const_("C")), const_("C.c1"));
    env.add_decl(Declaration::Definition {
        name: Name::from_string("instPickC"),
        level_params: vec![],
        type_: Expr::app(Expr::const_(pick.clone(), vec![]), const_("C")),
        value: inst_c_val,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("add_decl instPickC should succeed: {e:?}"));

    // Register the class + instances through the kernel registries the way the
    // importer's `register_classes_from_extension` /
    // `register_instances_from_extension` do. Crucially: NO
    // `register_structure_fields` (import path has none), and the instances are
    // registered with `type_: None, value: None` so the elaborator must
    // reconstruct them from `env.get_const(name)`.
    env.register_class(KernelClassInfo {
        name: pick.clone(),
        num_params: 1,
        out_params: vec![],
        semi_out_params: vec![],
    });
    env.register_instance(KernelInstanceInfo {
        name: Name::from_string("instPickB"),
        class_name: pick.clone(),
        priority: clean_kernel::DEFAULT_INSTANCE_PRIORITY,
        type_: None,
        value: None,
    });
    env.register_instance(KernelInstanceInfo {
        name: Name::from_string("instPickC"),
        class_name: pick,
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
// the importer does — and the elaborator's InstanceTable (rebuilt from the
// kernel registry on `ElabCtx::new`) sees them. This pins the precondition.
// =============================================================================

#[test]
fn test_imported_instance_env_registered_through_kernel_registry() {
    let env = imported_instance_env();
    let pick = Name::from_string("Pick");

    assert!(
        env.is_class(&pick),
        "Pick should be a registered class (via register_class, import-style)"
    );
    // No native structure-field table — the exact configuration a real .olean
    // produces and the one that routed B44 through the dot-notation fallback.
    assert!(
        env.get_structure_field_names(&pick).is_none(),
        "imported class must NOT carry a clean-side structure_fields table"
    );

    let instances = env.get_class_instances(&pick);
    assert_eq!(instances.len(), 2, "two Pick instances are registered");
    assert!(
        instances
            .iter()
            .all(|i| i.type_.is_none() && i.value.is_none()),
        "imported instances carry no type_/value; the elaborator reconstructs \
         them from env.get_const (the #443 import path)"
    );

    assert!(
        env.get_const(&Name::from_string("instPickB")).is_some()
            && env.get_const(&Name::from_string("Pick.chosen")).is_some(),
        "the instance constant and the method projection must both be present"
    );
}

// =============================================================================
// Test 2: control — the imported method projection and the underlying kernel
// `Proj` agree, and the imported instance constant reduces to the expected
// constructor. This isolates any failure in Test 3 to instance *synthesis* /
// method-call *elaboration*, not to kernel reduction or the hand-built layout.
// =============================================================================

#[test]
fn test_imported_instance_kernel_reduction_is_sound() {
    let env = imported_instance_env();

    // The instance constant itself reduces to `Pick.mk B B.b2`; projecting field
    // 0 yields `B.b2`.
    let proj_inst_b = Expr::proj(Name::from_string("Pick"), 0, const_("instPickB"));
    assert_eq!(
        whnf_head_const(&env, &proj_inst_b).as_deref(),
        Some("B.b2"),
        "Proj(Pick, 0, instPickB) must reduce to B.b2 (the instance's chosen field)"
    );

    // The decoy instance for C reduces to C.c1 — confirms the two instances are
    // genuinely distinct so a mis-selection in Test 3 would be observable.
    let proj_inst_c = Expr::proj(Name::from_string("Pick"), 0, const_("instPickC"));
    assert_eq!(
        whnf_head_const(&env, &proj_inst_c).as_deref(),
        Some("C.c1"),
        "Proj(Pick, 0, instPickC) must reduce to C.c1"
    );

    // Fully applying the imported method projection to (B, instPickB) must agree
    // with the direct projection above.
    let chosen_applied = Expr::app(
        Expr::app(const_("Pick.chosen"), const_("B")),
        const_("instPickB"),
    );
    assert_eq!(
        whnf_head_const(&env, &chosen_applied).as_deref(),
        Some("B.b2"),
        "Pick.chosen B instPickB must reduce to B.b2 through the imported projection"
    );
}

// =============================================================================
// Test 3: THE PROBE. A clean-elab-elaborated def that uses the method WITHOUT
// naming an instance must (a) synthesize the IMPORTED instance for the carrier
// pinned by the expected type, and (b) reduce — through that imported instance
// — to the CORRECT method result. Distinct constructors + a decoy carrier make
// a wrong instance / wrong projection observable.
// =============================================================================

#[test]
fn test_method_call_on_imported_instance_reduces_to_correct_result() {
    let mut env = imported_instance_env();

    // `Pick.chosen`'s result type is the carrier α, so the `: B` annotation pins
    // α := B; instance synthesis must select `instPickB` (NOT the decoy
    // `instPickC`). No instance is named explicitly — the elaborator must find
    // the imported one via the kernel-registry-backed InstanceTable.
    elaborate_decls_into(&mut env, "def pickedB : B := Pick.chosen");

    let info = env
        .get_const(&Name::from_string("pickedB"))
        .expect("pickedB should be registered after elaboration");
    let body = info
        .value
        .as_ref()
        .expect("pickedB is a definition with a body");

    // Proof the chain is genuinely wired through the imported pieces. The
    // elaborator resolves the instance-implicit and *inlines* the imported
    // instance's reconstructed value (`Pick.mk B B.b2` — its body, recovered
    // from `env.get_const` per #443's import path) rather than leaving the bare
    // `instPickB` constant. So the discriminating signal is the instance's
    // *content*: the carrier `B` and the chosen field `B.b2` — NOT the decoy's
    // `C` / `C.c1`.
    let referenced = body.collect_constants();
    assert!(
        referenced.contains(&Name::from_string("Pick.chosen")),
        "pickedB's body should go through the imported method projection Pick.chosen, \
         got: {referenced:?}"
    );
    assert!(
        referenced.contains(&Name::from_string("Pick.mk"))
            && referenced.contains(&Name::from_string("B.b2")),
        "pickedB's body should inline the synthesized IMPORTED instance for B \
         (Pick.mk B B.b2), got: {referenced:?}"
    );
    assert!(
        !referenced.contains(&Name::from_string("C.c1"))
            && !referenced.contains(&Name::from_string("C")),
        "instance synthesis must NOT pull in the decoy carrier C's instance content, \
         got: {referenced:?}"
    );

    // The payoff: reduce the elaborated def. It must land on B.b2 — the chosen
    // field of the imported instance for B. A wrong instance (the decoy for C)
    // would fail to type-check against `: B`; a wrong projection field/off-by-one,
    // or a failure to synthesize the imported instance, would surface here as the
    // wrong head (or a stuck redex) rather than passing silently.
    assert_eq!(
        whnf_head_const(&env, &const_("pickedB")).as_deref(),
        Some("B.b2"),
        "pickedB := (Pick.chosen : B) must reduce to B.b2 through the imported instance for B"
    );
}

// =============================================================================
// Test 4: a method call whose carrier is pinned to the DECOY type C must
// synthesize instPickC and reduce to C.c1 — the symmetric case. Together with
// Test 3 this proves instance synthesis genuinely discriminates by carrier.
// =============================================================================

#[test]
fn test_method_call_on_imported_instance_discriminates_carrier() {
    let mut env = imported_instance_env();
    elaborate_decls_into(&mut env, "def pickedC : C := Pick.chosen");

    let info = env
        .get_const(&Name::from_string("pickedC"))
        .expect("pickedC should be registered after elaboration");
    let referenced = info
        .value
        .as_ref()
        .expect("pickedC is a definition with a body")
        .collect_constants();
    // The synthesized instance is inlined as its content `Pick.mk C C.c1`; the
    // discriminating signal is the carrier C and chosen field C.c1, NOT B.b2.
    assert!(
        referenced.contains(&Name::from_string("Pick.mk"))
            && referenced.contains(&Name::from_string("C.c1")),
        "pickedC : C must synthesize the imported instance for C (Pick.mk C C.c1), \
         got: {referenced:?}"
    );
    assert!(
        !referenced.contains(&Name::from_string("B.b2"))
            && !referenced.contains(&Name::from_string("B")),
        "pickedC : C must NOT pull in carrier B's instance content, got: {referenced:?}"
    );

    assert_eq!(
        whnf_head_const(&env, &const_("pickedC")).as_deref(),
        Some("C.c1"),
        "pickedC := (Pick.chosen : C) must reduce to C.c1 through the imported instance for C"
    );
}
