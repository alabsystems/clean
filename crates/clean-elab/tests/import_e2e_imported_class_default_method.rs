// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: a DEFAULT METHOD on an *imported* type class.
//!
//! ## What a default method is, and how a real `.olean` ships it
//!
//! In Lean a class field may declare a *default* implementation:
//!
//! ```lean
//! class Widget (α : Type) where
//!   render : α → Nat
//!   tag    : Nat := 7        -- default method
//! ```
//!
//! An instance that *omits* `tag` inherits the default `7`; an instance that
//! *provides* `tag` overrides it. Lean compiles the default not as inline
//! metadata on the class but as an ordinary **sibling definition** named
//! `<Class>.<field>._default`, whose signature is the structure's parameters
//! followed by the *preceding* fields (so a later default may depend on an
//! earlier field). For the class above:
//!
//! ```text
//! Widget.tag._default : {α : Type} → (render : α → Nat) → Nat := fun _ _ => 7
//! ```
//!
//! Crucially, a real `.olean` carries **none** of clean's own class metadata:
//! no `structure_fields` name table, and no `structure_field_defaults` entry.
//! The class is a single-constructor inductive registered via `register_class`;
//! the methods are imported projection *functions* whose bodies are kernel
//! `Proj`s; the default is the standalone `<Class>.<field>._default` def. So an
//! elaborator that fills omitted fields from clean-side default metadata sees
//! nothing for an import — the default must be discovered from the shipped
//! `_default` definition instead.
//!
//! ## Synthesize-as-import
//!
//! No shipped `Widget` `.olean` fixture exists, so we build the kernel
//! declarations by hand in a fresh environment and register **only** the
//! inductive, `register_class`, Lean's projection *functions*, and the
//! `Widget.tag._default` definition — never a `structure_fields` table and never
//! a `register_structure_field_default` entry. That reproduces the real `.olean`
//! condition byte-for-byte at the elaborator's decision points. Preconditions
//! assert that configuration explicitly so the test stays honest if the importer
//! ever starts shipping clean-side default metadata.
//!
//! ## The bug this probe found, and the fix
//!
//! Before this change, `crates/clean-elab/src/infer/elab_struct_lit.rs` reported
//! every omitted field as a hard `MissingStructureFields` error and never
//! consulted any default. So constructing a `Widget Foo` that omits `tag`
//! (i.e. relying on the default method) failed to elaborate — the default method
//! could not be used at all on an imported class. The fix teaches the struct /
//! instance-literal path to fill an omitted field from a discoverable default:
//! the imported `<Class>.<field>._default` definition (applied to the structure
//! parameters and the preceding fields' values), falling back to clean-native
//! `structure_field_defaults` for native structures. The kernel re-checks the
//! produced constructor application, so a wrongly-typed default is rejected
//! rather than passing silently.
//!
//! ## What is asserted (distinct values so a wrong/missing default is visible)
//!
//! - Precondition: `Widget` is a class with no clean field table and no
//!   clean-side default metadata, but the `Widget.tag._default` def IS present
//!   (the imported shape).
//! - Control: applying the projections to a hand-built constructor reduces
//!   correctly at the kernel level (isolates elaboration from reduction).
//! - The OMITTING instance `{ render := … }` elaborates, kernel-checks, and
//!   `Widget.tag` of it reduces to the default `7` (NOT the override 3).
//! - The OVERRIDING instance `{ render := …, tag := 3 }` reduces to `3`.
//! - A no-default field that is omitted is still a hard error (the missing-field
//!   path is not over-broadened).
//! - The long-form `instance … where` path on an imported class is probed:
//!   locked in if it works, honestly pinned with a flip-on-fix assertion if it
//!   is a genuine remaining gap.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{BinderInfo, Declaration, Expr, ExprKind, KernelClassInfo, Name, TypeChecker};
use clean_parser::parse_file;

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn nat_lit(n: u32) -> Expr {
    let mut e = const_("Nat.zero");
    for _ in 0..n {
        e = Expr::app(const_("Nat.succ"), e);
    }
    e
}

/// Definitional equality against a kernel `Nat` literal (the reduced shape).
fn def_eq(env: &Environment, expr: &Expr, reference: &Expr) -> bool {
    let tc = TypeChecker::new(env);
    tc.is_def_eq(expr, reference)
}

/// The `Widget` class type `Type → Type`.
fn widget_class_type() -> Expr {
    Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_())
}

/// Build the imported `Widget α` class environment by hand, in the exact shape a
/// real Lean `.olean` ships:
///   * a carrier `Foo : Type` with a single value `Foo.mk`,
///   * `Widget α : Type` a single-constructor inductive (1 param),
///     `Widget.mk (α : Type) (render : α → Nat) (tag : Nat) : Widget α`,
///   * `register_class Widget` (no out-params, no structure_fields table),
///   * Lean's projection *functions* `Widget.render` and `Widget.tag`,
///   * the default-method definition `Widget.tag._default`,
///   * NO clean field-name table and NO `register_structure_field_default`.
fn imported_widget_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");

    let ty = Expr::type_();
    let widget = Name::from_string("Widget");
    let nat = const_("Nat");

    // ---- Foo : Type, Foo.mk : Foo ----
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Foo"),
            type_: ty.clone(),
            constructors: vec![Constructor {
                name: Name::from_string("Foo.mk"),
                type_: const_("Foo"),
            }],
        }],
    })
    .expect("add Foo");

    // ---- Widget : Type → Type ----
    // Widget.mk : (α : Type) → (render : α → Nat) → (tag : Nat) → Widget α
    // In the ctor scope under α: α = bvar 0. The `render : α → Nat` field adds a
    // binder; the `tag : Nat` field adds another. Result `Widget α`: under
    // (α, render, tag), α = bvar 2.
    let render_field = Expr::pi(BinderInfo::Default, Expr::bvar(0), nat.clone());
    let mk_ty = Expr::pi(
        BinderInfo::Default,
        ty.clone(),
        Expr::pi(
            BinderInfo::Default,
            render_field,
            Expr::pi(
                BinderInfo::Default,
                nat.clone(),
                Expr::app(Expr::const_(widget.clone(), vec![]), Expr::bvar(2)),
            ),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: widget.clone(),
            type_: widget_class_type(),
            constructors: vec![Constructor {
                name: Name::from_string("Widget.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("add Widget");

    // Widget.render : {α : Type} → [self : Widget α] → α → Nat
    //   := fun {α} [self] => Proj(Widget, 0, self)
    let widget_self_ty = Expr::app(Expr::const_(widget.clone(), vec![]), Expr::bvar(0));
    let render_ty = Expr::pi(
        BinderInfo::Implicit,
        ty.clone(),
        Expr::pi(
            BinderInfo::InstImplicit,
            widget_self_ty.clone(),
            // result `α → Nat`: under (α, self), α = bvar 1.
            Expr::pi(BinderInfo::Default, Expr::bvar(1), nat.clone()),
        ),
    );
    let render_val = Expr::lam(
        BinderInfo::Implicit,
        ty.clone(),
        Expr::lam(
            BinderInfo::InstImplicit,
            widget_self_ty.clone(),
            Expr::proj(widget.clone(), 0, Expr::bvar(0)),
        ),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("Widget.render"),
        level_params: vec![],
        type_: render_ty,
        value: render_val,
        is_reducible: true,
    })
    .expect("add Widget.render");

    // Widget.tag : {α : Type} → [self : Widget α] → Nat
    //   := fun {α} [self] => Proj(Widget, 1, self)
    let tag_ty = Expr::pi(
        BinderInfo::Implicit,
        ty.clone(),
        Expr::pi(
            BinderInfo::InstImplicit,
            widget_self_ty.clone(),
            nat.clone(),
        ),
    );
    let tag_val = Expr::lam(
        BinderInfo::Implicit,
        ty.clone(),
        Expr::lam(
            BinderInfo::InstImplicit,
            widget_self_ty,
            Expr::proj(widget.clone(), 1, Expr::bvar(0)),
        ),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("Widget.tag"),
        level_params: vec![],
        type_: tag_ty,
        value: tag_val,
        is_reducible: true,
    })
    .expect("add Widget.tag");

    // Widget.tag._default : {α : Type} → (render : α → Nat) → Nat := fun _ _ => 7
    // The Lean default-method shape: the structure's params (α) followed by the
    // preceding fields (render), returning the field type (Nat). Body is the
    // constant 7 (distinct from every other value so a wrong default is visible).
    let default_ty = Expr::pi(
        BinderInfo::Implicit,
        ty.clone(),
        Expr::pi(
            BinderInfo::Default,
            // render : α → Nat ; under α, α = bvar 0.
            Expr::pi(BinderInfo::Default, Expr::bvar(0), nat.clone()),
            nat.clone(),
        ),
    );
    let default_val = Expr::lam(
        BinderInfo::Implicit,
        ty.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::pi(BinderInfo::Default, Expr::bvar(0), nat.clone()),
            nat_lit(7),
        ),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("Widget.tag._default"),
        level_params: vec![],
        type_: default_ty,
        value: default_val,
        is_reducible: true,
    })
    .expect("add Widget.tag._default");

    // register_class, import-style (no out_params, no structure_fields).
    env.register_class(KernelClassInfo {
        name: widget,
        num_params: 1,
        out_params: vec![],
        semi_out_params: vec![],
    });

    env
}

/// Elaborate and register `source` against `env`, threading a `FileContext`.
/// `elaborate_decl_and_register` runs the full kernel type check, so reaching the
/// end means every body kernel-checked.
fn try_elaborate_decls_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse: {e:?}"))?;
    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed)
            .map_err(|e| format!("declaration {i}: {e}"))?;
    }
    Ok(())
}

fn elaborate_decls_into(env: &mut Environment, source: &str) {
    try_elaborate_decls_into(env, source)
        .unwrap_or_else(|e| panic!("declarations should elaborate and kernel-check: {e}"));
}

// =============================================================================
// Precondition: this is genuinely the imported class configuration — a class
// (via register_class), its projection functions, and the `_default` definition
// are present, but there is NO clean-side structure_fields table and NO
// clean-side structure_field_default. That forces default resolution through the
// shipped `Widget.tag._default` definition (the import path), not metadata.
// =============================================================================

#[test]
fn test_imported_widget_class_has_default_def_but_no_clean_metadata() {
    let env = imported_widget_env();
    let widget = Name::from_string("Widget");

    assert!(
        env.is_class(&widget),
        "Widget should be a registered class (via register_class, import-style)"
    );
    assert!(
        env.get_structure_field_names(&widget).is_none(),
        "imported Widget must NOT carry a clean-side structure_fields name table"
    );
    // No clean-side recorded default for the `tag` field — the only default is
    // the shipped definition.
    assert!(
        env.get_structure_field_default(&widget, &Name::from_string("tag"))
            .is_none(),
        "imported Widget must NOT carry a clean-side structure_field_default — \
         the default is discoverable only through Widget.tag._default"
    );

    for c in [
        "Widget.render",
        "Widget.tag",
        "Widget.tag._default",
        "Widget.mk",
    ] {
        assert!(
            env.get_const(&Name::from_string(c)).is_some(),
            "{c} should be present in the imported env"
        );
    }
    // There is deliberately no default for the non-defaulted `render` field.
    assert!(
        env.get_const(&Name::from_string("Widget.render._default"))
            .is_none(),
        "render has no default — only tag does"
    );
}

// =============================================================================
// Control: a hand-built constructor with explicit fields reduces correctly at
// the KERNEL level. This isolates any failure in the elaboration probes from
// kernel reduction or the hand-built layout. The default value 7 and the
// override 3 are distinct, and distinct from the render result, so any wrong
// slot is observable.
// =============================================================================

#[test]
fn test_widget_kernel_projections_reduce_correctly() {
    let env = imported_widget_env();

    // w = Widget.mk Foo (fun _ => 1) 3
    let render_fn = Expr::lam(BinderInfo::Default, const_("Foo"), nat_lit(1));
    let w = Expr::apps(
        const_("Widget.mk"),
        [const_("Foo"), render_fn.clone(), nat_lit(3)],
    );

    // Widget.tag Foo w  ⇝  Proj(Widget, 1, w)  ⇝  3
    let tag = Expr::apps(const_("Widget.tag"), [const_("Foo"), w.clone()]);
    assert!(
        def_eq(&env, &tag, &nat_lit(3)),
        "Widget.tag of the hand-built ctor must reduce to 3, got {:?}",
        TypeChecker::new(&env).whnf(&tag).kind()
    );

    // The default definition applied to (Foo, render) reduces to 7.
    let default_applied = Expr::apps(const_("Widget.tag._default"), [const_("Foo"), render_fn]);
    assert!(
        def_eq(&env, &default_applied, &nat_lit(7)),
        "Widget.tag._default Foo render must reduce to 7, got {:?}",
        TypeChecker::new(&env).whnf(&default_applied).kind()
    );
}

// =============================================================================
// THE PROBE / regression guard: an instance that OMITS the default method.
//
// `{ render := fun _ => 1 : Widget Foo }` omits `tag`. Before the fix this was a
// hard `MissingStructureFields` error; now the omitted `tag` is filled from the
// imported `Widget.tag._default` definition. `Widget.tag` of it must reduce to
// the default 7 (NOT 3, which only an override would produce).
// =============================================================================

#[test]
fn test_instance_omitting_default_method_uses_default_value() {
    let mut env = imported_widget_env();

    elaborate_decls_into(
        &mut env,
        "def wDefault : Widget Foo := { render := fun _ => Nat.succ Nat.zero }",
    );

    // The stored body must reference the imported default definition, proving we
    // filled the omitted field from `Widget.tag._default` (the import path).
    let body = env
        .get_const(&Name::from_string("wDefault"))
        .and_then(|i| i.value.clone())
        .expect("wDefault body");
    let referenced = body.collect_constants();
    assert!(
        referenced.contains(&Name::from_string("Widget.tag._default")),
        "the omitted default method must be filled from Widget.tag._default, got: {referenced:?}"
    );

    // Widget.tag wDefault must reduce to the default 7.
    let tag = Expr::apps(const_("Widget.tag"), [const_("Foo"), const_("wDefault")]);
    assert!(
        def_eq(&env, &tag, &nat_lit(7)),
        "an instance omitting the default method must take tag = 7 (the default), got {:?}",
        TypeChecker::new(&env).whnf(&tag).kind()
    );
    // Guard: the default must NOT be confused with the override value.
    assert!(
        !def_eq(&env, &tag, &nat_lit(3)),
        "the omitted default must be 7, never the override 3"
    );

    // The render field the instance DID provide still reduces correctly: applied
    // to any Foo value it yields 1 (so the default fill didn't disturb the
    // provided field's slot).
    let rendered = Expr::apps(
        const_("Widget.render"),
        [const_("Foo"), const_("wDefault"), const_("Foo.mk")],
    );
    assert!(
        def_eq(&env, &rendered, &nat_lit(1)),
        "the provided render field must reduce to 1, got {:?}",
        TypeChecker::new(&env).whnf(&rendered).kind()
    );
}

// =============================================================================
// An instance that OVERRIDES the default method. `{ render := …, tag := 3 }`
// supplies `tag` explicitly, so it must reduce to 3 (the override), NOT 7.
// =============================================================================

#[test]
fn test_instance_overriding_default_method_uses_override_value() {
    let mut env = imported_widget_env();

    // Override tag with 3 (distinct from the default 7 and from render's 1).
    elaborate_decls_into(
        &mut env,
        "def wOverride : Widget Foo := \
         { render := fun _ => Nat.succ Nat.zero, \
           tag := Nat.succ (Nat.succ (Nat.succ Nat.zero)) }",
    );

    // The override must NOT pull in the default definition.
    let body = env
        .get_const(&Name::from_string("wOverride"))
        .and_then(|i| i.value.clone())
        .expect("wOverride body");
    let referenced = body.collect_constants();
    assert!(
        !referenced.contains(&Name::from_string("Widget.tag._default")),
        "an explicit tag must NOT pull in Widget.tag._default, got: {referenced:?}"
    );

    let tag = Expr::apps(const_("Widget.tag"), [const_("Foo"), const_("wOverride")]);
    assert!(
        def_eq(&env, &tag, &nat_lit(3)),
        "an instance overriding the default method must take tag = 3, got {:?}",
        TypeChecker::new(&env).whnf(&tag).kind()
    );
    assert!(
        !def_eq(&env, &tag, &nat_lit(7)),
        "the override must be 3, never the default 7"
    );
}

// =============================================================================
// Negative control: omitting a field that has NO default is still a hard error.
// The missing-field path must not be over-broadened by the default-fill fix.
// `{ tag := 5 }` provides `tag` but omits the no-default `render` field.
// =============================================================================

#[test]
fn test_omitting_non_default_field_is_still_rejected() {
    let mut env = imported_widget_env();

    let result = try_elaborate_decls_into(
        &mut env,
        "def wBad : Widget Foo := { tag := Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) }",
    );
    assert!(
        result.is_err(),
        "omitting the no-default `render` field must still be a missing-field error, got Ok"
    );
    assert!(
        env.get_const(&Name::from_string("wBad")).is_none(),
        "the rejected literal must not register `wBad`"
    );
}

// =============================================================================
// Long-form `instance … where` on an imported class — NOW LOCKED IN.
//
// This was pinned as a known gap when B51 fixed the struct-literal path: the
// long-form path keyed off the clean-side field-name table (absent for an
// imported class), so it rejected imported classes outright. That gap is now
// fixed (`crates/clean-elab/src/infer/elab_instance.rs`): when a class has no
// field-name table the long-form `where` block is desugared into the structure
// literal `({ field := val, … } : Class T)` and routed through the SAME
// `elab_struct_lit` machinery used here — so the omitted defaulted method is
// filled from `Widget.tag._default`, exactly like the literal path.
//
// We lock in the previously-omitting case: a long-form instance that omits the
// defaulted `tag` now elaborates and `Widget.tag` of it reduces to the default
// 7. (The dedicated probe `import_e2e_longform_instance_where.rs` exercises the
// override / negative / native cases in depth.)
// =============================================================================

#[test]
fn test_longform_instance_where_on_imported_class_fills_default() {
    let mut env = imported_widget_env();

    elaborate_decls_into(
        &mut env,
        "instance instWidgetFoo : Widget Foo where\n  render := fun _ => Nat.succ Nat.zero",
    );

    // The omitted `tag` is filled from the imported default definition.
    let body = env
        .get_const(&Name::from_string("instWidgetFoo"))
        .and_then(|i| i.value.clone())
        .expect("instWidgetFoo body");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("Widget.tag._default")),
        "the long-form path must fill the omitted default from Widget.tag._default"
    );

    let tag = Expr::apps(
        const_("Widget.tag"),
        [const_("Foo"), const_("instWidgetFoo")],
    );
    assert!(
        def_eq(&env, &tag, &nat_lit(7)),
        "long-form instance omitting the default method must take tag = 7, got {:?}",
        TypeChecker::new(&env).whnf(&tag).kind()
    );
    assert!(
        !def_eq(&env, &tag, &nat_lit(3)),
        "the omitted default must be 7, never an override 3"
    );
}
