// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: NOTATION / operators attached to an *imported* declaration.
//!
//! ## What a real `.olean` ships for notation
//!
//! In Lean, notation is exported in the `.olean` and is meant to be usable in a
//! downstream module. There are two distinct flavours that reach the elaborator
//! by completely different routes in clean:
//!
//! 1. **Standard arithmetic notation** (`a + b`, `a * b`, …) is *not* a
//!    user-extensible parser table in clean — the surface parser hardwires `+`
//!    to `HAdd.hAdd a b`, `*` to `HMul.hMul a b`, etc. So `a + b` for an
//!    *imported* type routes entirely through **typeclass resolution**: the
//!    elaborator must find an `HAdd α α α` instance for the operand type. That
//!    instance, for an import, is shipped as an ordinary `register_instance`
//!    entry with NO clean-side notation/structure metadata, and the method body
//!    reduces through the kernel's generic structure projection.
//!
//! 2. **Custom mixfix notation** (`infixl:65 " ⊕ " => Foo.bar`,
//!    `notation:65 a " ⊕ " b => Foo.bar a b`) is a user-extensible parser
//!    extension. clean's `notation`/`infixl`/… commands parse and *register* the
//!    notation into the dynamic custom-operator registry, and the surface parser
//!    DOES consult that registry while parsing a *later* expression: a custom
//!    operator symbol like `⊕` is recognized and `x ⊕ y` is expanded to the
//!    registered target, so `Color.red ⊕ Color.green` routes to
//!    `Color.combine Color.red Color.green` and reaches the kernel. Locked in
//!    below against an imported target.
//!
//! 3. **Zero-variable atom aliases** (`notation "GG" => Color.green`) DO work
//!    end-to-end: the elaborator's `expand_simple_notation_aliases` pass rewrites
//!    the bare identifier `GG` to the imported `Color.green` before elaboration.
//!    Locked in below against an imported target.
//!
//! ## Synthesize-as-import
//!
//! There is no shipped `.olean` fixture, so we build the environment by hand. We
//! take the *genuine* `HAdd` class and `HAdd.hAdd` projection from kernel init
//! (this is exactly the class/projection a real `.olean` would carry), then ship
//! the piece that is genuinely "imported": an `HAdd Color Color Color` instance
//! for a fresh carrier type `Color`, registered through `register_instance` ONLY
//! — never via clean-side structure_fields for the carrier and never as a native
//! shortcut. The kernel's `HAdd.hAdd` native reducer fires only for
//! `instHAddNatNatNat`; our `Color` carrier deliberately routes through the
//! generic projection path so the test exercises real import-shaped reduction.
//!
//! Preconditions assert that configuration so the test stays honest if the
//! importer ever changes.
//!
//! ## What is asserted (distinct observable values)
//!
//! `Color.combine` always returns `Color.green` regardless of arguments, and
//! `Color.red ≠ Color.green` are distinct constructors, so a wrong/missing
//! instance resolution is visible:
//!
//! - Precondition: `HAdd` is a class, `instHAddColor` is a registered instance,
//!   the `Color` carrier carries NO clean-side structure_fields, and `Color.red`
//!   / `Color.green` / `Color.combine` exist.
//! - Control: the hand-built `HAdd.hAdd … instHAddColor red red` reduces to
//!   `green` at the kernel level (isolates elaboration from reduction).
//! - LOCK-IN: `def usesPlus : Color := red + red` elaborates, kernel-checks, its
//!   body references the hardwired `HAdd.hAdd`, and it reduces to `green`
//!   (NOT `red`), proving the `+` notation resolved the imported instance.
//! - LOCK-IN: a zero-variable atom alias `notation "GG" => Color.green` is
//!   usable in a new def and reduces to the imported `green`.
//! - LOCK-IN (custom infix): a custom infix `infixl … " ⊕ " => Color.combine`
//!   used as `x ⊕ y` DOES route to `Color.combine` (the parser consults the
//!   dynamic custom-operator registry), elaborates, kernel-checks, its body
//!   references `Color.combine`, and it reduces to the imported `green`.

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{
    BinderInfo, Declaration, Expr, KernelInstanceInfo, Level, Name, TypeChecker,
    DEFAULT_INSTANCE_PRIORITY,
};
use clean_parser::parse_file;

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// Definitional equality against a reference kernel expression (the reduced shape).
fn def_eq(env: &Environment, expr: &Expr, reference: &Expr) -> bool {
    let tc = TypeChecker::new(env);
    tc.is_def_eq(expr, reference)
}

/// Build the imported environment by hand, in the exact shape a real `.olean`
/// ships for notation-via-typeclass:
///   * the GENUINE `HAdd` class and `HAdd.hAdd` projection (from kernel init —
///     a `.olean` carries these identically),
///   * a fresh carrier `Color : Type` with values `Color.red`, `Color.green`,
///     and a binary `Color.combine : Color → Color → Color := fun _ _ => green`
///     (constant `green`, distinct from `red`, so the result is observable),
///   * the genuinely-imported instance `instHAddColor : HAdd Color Color Color`
///     `:= HAdd.mk Color Color Color Color.combine`, registered ONLY via
///     `register_instance` — no clean-side notation/structure metadata.
fn imported_notation_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    // The genuine HAdd class + HAdd.hAdd projection (what a real .olean carries).
    env.init_hadd().expect("init_hadd");

    let ty = Expr::type_();

    // ---- Color : Type, with Color.red and Color.green ----
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Color"),
            type_: ty.clone(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Color.red"),
                    type_: const_("Color"),
                },
                Constructor {
                    name: Name::from_string("Color.green"),
                    type_: const_("Color"),
                },
            ],
        }],
    })
    .expect("add Color");

    // Color.combine : Color → Color → Color := fun _ _ => Color.green
    // (constant green — a wrong/missing instance can never accidentally produce
    // green from red, so the reduced value is a faithful witness.)
    let color = const_("Color");
    let combine_ty = Expr::pi(
        BinderInfo::Default,
        color.clone(),
        Expr::pi(BinderInfo::Default, color.clone(), color.clone()),
    );
    let combine_val = Expr::lam(
        BinderInfo::Default,
        color.clone(),
        Expr::lam(BinderInfo::Default, color.clone(), const_("Color.green")),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("Color.combine"),
        level_params: vec![],
        type_: combine_ty,
        value: combine_val,
        is_reducible: true,
    })
    .expect("add Color.combine");

    // instHAddColor : HAdd Color Color Color
    //   := HAdd.mk Color Color Color Color.combine
    // The HAdd.mk constructor takes (α β γ) then the op (α → β → γ). For the
    // homogeneous carrier all three are `Color`. Universe args are all 0 (Type).
    let levels = vec![Level::zero(), Level::zero(), Level::zero()];
    let hadd_const = Expr::const_(Name::from_string("HAdd"), levels.clone());
    let hadd_mk = Expr::const_(Name::from_string("HAdd.mk"), levels);
    let inst_type = Expr::apps(hadd_const, [color.clone(), color.clone(), color.clone()]);
    let inst_value = Expr::apps(
        hadd_mk,
        [
            color.clone(),
            color.clone(),
            color.clone(),
            const_("Color.combine"),
        ],
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("instHAddColor"),
        level_params: vec![],
        type_: inst_type.clone(),
        value: inst_value.clone(),
        is_reducible: true,
    })
    .expect("add instHAddColor");

    // The genuinely-imported piece: register the instance through the kernel's
    // instance registry only. The elaborator's InstanceTable is built purely
    // from env.classes()/env.get_class_instances(), so this is the sole path by
    // which `+` on Color can resolve.
    env.register_instance(KernelInstanceInfo {
        name: Name::from_string("instHAddColor"),
        class_name: Name::from_string("HAdd"),
        priority: DEFAULT_INSTANCE_PRIORITY,
        type_: Some(inst_type),
        value: Some(inst_value),
    });

    env
}

/// Elaborate and register `source` against `env`, threading a `FileContext`.
///
/// We use the `_with_context` entry point on purpose: it persists the macro
/// context (and thus any registered notation) across declarations, exactly as a
/// real file is processed. The plain `elaborate_decl_and_register` rebuilds a
/// fresh macro context per declaration, which would drop a `notation` registered
/// by an earlier declaration before a later declaration could use it.
/// `elaborate_decl_and_register_with_context` runs the full kernel type check, so
/// reaching the end means every body kernel-checked.
fn try_elaborate_decls_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse: {e:?}"))?;
    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register_with_context(env, &processed, &mut file_ctx)
            .map_err(|e| format!("declaration {i}: {e}"))?;
    }
    Ok(())
}

fn elaborate_decls_into(env: &mut Environment, source: &str) {
    try_elaborate_decls_into(env, source)
        .unwrap_or_else(|e| panic!("declarations should elaborate and kernel-check: {e}"));
}

// =============================================================================
// Precondition: this is genuinely the imported configuration — `HAdd` is a
// class, `instHAddColor` is a registered instance, the `Color` carrier has NO
// clean-side structure_fields table, and the carrier/op constants are present.
// =============================================================================

#[test]
fn test_imported_notation_env_is_import_shaped() {
    let env = imported_notation_env();

    assert!(
        env.is_class(&Name::from_string("HAdd")),
        "HAdd must be a registered class (the notation target's class)"
    );
    assert!(
        env.is_instance(&Name::from_string("instHAddColor")),
        "instHAddColor must be a registered instance reachable by `+` resolution"
    );
    // The carrier deliberately carries NO clean-side structure field table — it
    // is an ordinary inductive, exactly as an imported data type would be.
    assert!(
        env.get_structure_field_names(&Name::from_string("Color"))
            .is_none(),
        "imported Color carrier must NOT carry a clean-side structure_fields table"
    );
    for c in ["Color.red", "Color.green", "Color.combine", "HAdd.hAdd"] {
        assert!(
            env.get_const(&Name::from_string(c)).is_some(),
            "{c} should be present in the imported env"
        );
    }
    // The two carrier values are genuinely distinct, so reducing to one rather
    // than the other is observable.
    assert!(
        !def_eq(&env, &const_("Color.red"), &const_("Color.green")),
        "Color.red and Color.green must be distinct constructors"
    );
}

// =============================================================================
// Control: the hand-built `HAdd.hAdd … instHAddColor red red` reduces to `green`
// at the KERNEL level via the generic projection path (no native shortcut for a
// custom carrier). This isolates the elaboration probes from reduction.
// =============================================================================

#[test]
fn test_hadd_projection_reduces_through_imported_instance() {
    let env = imported_notation_env();

    // HAdd.hAdd Color Color Color instHAddColor red red
    let levels = vec![Level::zero(), Level::zero(), Level::zero()];
    let hadd_hadd = Expr::const_(Name::from_string("HAdd.hAdd"), levels);
    let applied = Expr::apps(
        hadd_hadd,
        [
            const_("Color"),
            const_("Color"),
            const_("Color"),
            const_("instHAddColor"),
            const_("Color.red"),
            const_("Color.red"),
        ],
    );
    assert!(
        def_eq(&env, &applied, &const_("Color.green")),
        "HAdd.hAdd through instHAddColor must reduce to green, got {:?}",
        TypeChecker::new(&env).whnf(&applied).kind()
    );
    assert!(
        !def_eq(&env, &applied, &const_("Color.red")),
        "the reduced value must be green, never red"
    );
}

// =============================================================================
// LOCK-IN: standard `+` notation on an imported type. `red + red` is hardwired
// by the parser to `HAdd.hAdd red red`; the elaborator must synthesize the
// imported `instHAddColor` and the result must reduce to `green` (NOT red).
// =============================================================================

#[test]
fn test_plus_notation_resolves_imported_instance_and_reduces() {
    let mut env = imported_notation_env();

    elaborate_decls_into(&mut env, "def usesPlus : Color := Color.red + Color.red");

    // The stored body must reference the hardwired `HAdd.hAdd` — proving `+`
    // routed through typeclass resolution rather than some other path.
    let body = env
        .get_const(&Name::from_string("usesPlus"))
        .and_then(|i| i.value.clone())
        .expect("usesPlus body");
    let referenced = body.collect_constants();
    assert!(
        referenced.contains(&Name::from_string("HAdd.hAdd")),
        "`+` must elaborate through HAdd.hAdd, got: {referenced:?}"
    );

    // It must reduce to the imported instance's result `green`, not `red`.
    assert!(
        def_eq(&env, &const_("usesPlus"), &const_("Color.green")),
        "red + red on the imported instance must reduce to green, got {:?}",
        TypeChecker::new(&env).whnf(&const_("usesPlus")).kind()
    );
    assert!(
        !def_eq(&env, &const_("usesPlus"), &const_("Color.red")),
        "the `+` result must be green, never red"
    );
}

// =============================================================================
// LOCK-IN: a zero-variable atom-alias `notation "GG" => Color.green` is usable
// in a new def and resolves to the imported `Color.green`. This exercises the
// elaborator's `expand_simple_notation_aliases` pass against an imported target.
// =============================================================================

#[test]
fn test_atom_alias_notation_resolves_imported_const() {
    let mut env = imported_notation_env();

    elaborate_decls_into(
        &mut env,
        "notation \"GG\" => Color.green\ndef usesAlias : Color := GG",
    );

    let body = env
        .get_const(&Name::from_string("usesAlias"))
        .and_then(|i| i.value.clone())
        .expect("usesAlias body");
    let referenced = body.collect_constants();
    assert!(
        referenced.contains(&Name::from_string("Color.green")),
        "the atom alias GG must expand to the imported Color.green, got: {referenced:?}"
    );
    assert!(
        def_eq(&env, &const_("usesAlias"), &const_("Color.green")),
        "the atom alias must reduce to green, got {:?}",
        TypeChecker::new(&env).whnf(&const_("usesAlias")).kind()
    );
    assert!(
        !def_eq(&env, &const_("usesAlias"), &const_("Color.red")),
        "the atom alias must be green, never red"
    );
}

// =============================================================================
// LOCK-IN (custom infix): a custom infix notation attached to an imported decl
// IS usable in a later expression, because the surface parser consults the
// dynamically-registered custom-operator registry — the operator symbol `⊕` is
// recognized and `x ⊕ y` is expanded to the registered `Color.combine` target.
//
// We probe the FULL `notation` + use flow and lock in the outcome: the `def`
// elaborates and kernel-checks, its stored body references the intended target
// `Color.combine`, and it reduces to the notation's intended result `green`
// (NOT red) — i.e. the `⊕` routed all the way through the registered expansion.
// =============================================================================

#[test]
fn test_custom_infix_notation_on_imported_decl_routes_and_reduces() {
    let mut env = imported_notation_env();

    let result = try_elaborate_decls_into(
        &mut env,
        "infixl:65 \" ⊕ \" => Color.combine\n\
         def usesInfix : Color := Color.red ⊕ Color.green",
    );

    // The custom infix works end-to-end: the declaration elaborates and
    // kernel-checks, `usesInfix`'s stored body references the intended target
    // `Color.combine` (proving `⊕` routed to the registered expansion rather
    // than dropping the operator), and it reduces to the notation's intended
    // result `green`.
    let routed_correctly = result.is_ok()
        && env
            .get_const(&Name::from_string("usesInfix"))
            .and_then(|i| i.value.clone())
            .map(|body| {
                body.collect_constants()
                    .contains(&Name::from_string("Color.combine"))
            })
            .unwrap_or(false)
        && def_eq(&env, &const_("usesInfix"), &const_("Color.green"));

    assert!(
        routed_correctly,
        "LOCK-IN: custom infix `⊕` on an imported decl must route to \
         Color.combine and reduce to green — the parser consults the dynamic \
         custom-operator registry, so `Color.red ⊕ Color.green` expands to \
         `Color.combine Color.red Color.green` and reaches the kernel."
    );

    // Value witness, mirroring the other lock-in tests: the result is green,
    // never the distinct constructor red.
    assert!(
        !def_eq(&env, &const_("usesInfix"), &const_("Color.red")),
        "the custom infix result must be green, never red"
    );
}
