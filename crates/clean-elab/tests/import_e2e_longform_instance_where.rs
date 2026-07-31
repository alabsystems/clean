// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: the LONG-FORM `instance : C T where method := …` command on an
//! *imported* type class — the gap B51 explicitly PINNED.
//!
//! ## Background: what B51 fixed, and what it pinned
//!
//! B51 taught the structure / instance-LITERAL path
//! (`crates/clean-elab/src/infer/elab_struct_lit.rs`) to construct an imported
//! class while filling an omitted *default method* from the shipped
//! `<Class>.<field>._default` definition (the real `.olean` shape: a
//! single-constructor inductive registered via `register_class`, projection
//! *functions* whose bodies are kernel `Proj`s, and a sibling `_default`
//! definition — NO clean-side `structure_fields` name table and NO
//! `structure_field_defaults` entry). That made
//! `def w : Widget Foo := { render := … }` (anonymous-constructor / literal
//! form) work for imports.
//!
//! B51 could NOT make the LONG-FORM command path work for imports:
//!
//! ```lean
//! instance instWidgetFoo : Widget Foo where
//!   render := fun _ => 1
//! ```
//!
//! The long-form path in `crates/clean-elab/src/infer/elab_instance.rs` keyed
//! off `Environment::get_structure_field_names`, which is `None` for an imported
//! class (no clean-side field table). With no field-name table it could not
//! iterate the class fields and rejected the declaration with a hard
//! `class … not found` error — regardless of whether a default existed. B51
//! pinned this with a flip-on-fix assertion in
//! `import_e2e_imported_class_default_method.rs`.
//!
//! ## What THIS batch implements
//!
//! The long-form path now detects the missing field-name table (the import
//! condition) and *desugars* the `where` block into the structure literal
//! `({ field := val, … } : Class T)`, routing through `elab_struct_lit` — the
//! exact B51-fixed machinery. So an imported class's long-form instance:
//!   * resolves provided fields positionally through the projection functions,
//!   * fills an omitted defaulted method from `<Class>.<field>._default`, and
//!   * kernel-checks the produced constructor application.
//!
//! Native classes (which DO carry a field-name table) keep the original
//! field-name-driven path unchanged — this fallback only fires when the table
//! is absent.
//!
//! ## Synthesize-as-import
//!
//! No shipped `Widget` `.olean` fixture exists, so we build the kernel
//! declarations by hand and register **only** the inductive, `register_class`,
//! Lean's projection *functions*, and `Widget.tag._default` — never a
//! `structure_fields` table and never a `register_structure_field_default`
//! entry. That reproduces the real `.olean` condition byte-for-byte at the
//! elaborator's decision points. Preconditions assert that configuration so the
//! test stays honest if the importer ever starts shipping clean-side metadata.
//!
//! ## What is asserted (distinct values so a wrong/missing default is visible)
//!
//! - Precondition: `Widget` is a class with no clean field table and no
//!   clean-side default metadata, but `Widget.tag._default` IS present.
//! - Control: a hand-built constructor reduces correctly at the kernel level.
//! - The OVERRIDING long-form instance `where render := … tag := 3` reduces its
//!   `tag` to `3`.
//! - The OMITTING long-form instance `where render := …` (no `tag`) fills `tag`
//!   from the default and reduces to `7` (NOT `3`).
//! - A no-default field omitted in long-form is still a hard error (the
//!   missing-field path is not over-broadened).
//! - Native control: a long-form instance on a NATIVE class still works (the
//!   field-name-driven path is untouched).

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{BinderInfo, Declaration, Expr, KernelClassInfo, Name, TypeChecker};
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
///
/// This is the same fixture shape as B51's
/// `import_e2e_imported_class_default_method.rs`.
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
    let default_ty = Expr::pi(
        BinderInfo::Implicit,
        ty.clone(),
        Expr::pi(
            BinderInfo::Default,
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
// clean-side structure_field_default. That is exactly the condition under which
// the long-form `where` path used to bail out (it keyed off the field table).
// =============================================================================

#[test]
fn test_imported_widget_has_no_field_table_but_has_default_def() {
    let env = imported_widget_env();
    let widget = Name::from_string("Widget");

    assert!(
        env.is_class(&widget),
        "Widget should be a registered class (via register_class, import-style)"
    );
    assert!(
        env.get_structure_field_names(&widget).is_none(),
        "imported Widget must NOT carry a clean-side structure_fields name table — \
         this is precisely the condition that made the long-form path bail out"
    );
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
    assert!(
        env.get_const(&Name::from_string("Widget.render._default"))
            .is_none(),
        "render has no default — only tag does"
    );
}

// =============================================================================
// Control: a hand-built constructor with explicit fields reduces correctly at
// the KERNEL level (isolates any elaboration failure from kernel reduction).
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

    let tag = Expr::apps(const_("Widget.tag"), [const_("Foo"), w.clone()]);
    assert!(
        def_eq(&env, &tag, &nat_lit(3)),
        "Widget.tag of the hand-built ctor must reduce to 3, got {:?}",
        TypeChecker::new(&env).whnf(&tag).kind()
    );

    let default_applied = Expr::apps(const_("Widget.tag._default"), [const_("Foo"), render_fn]);
    assert!(
        def_eq(&env, &default_applied, &nat_lit(7)),
        "Widget.tag._default Foo render must reduce to 7, got {:?}",
        TypeChecker::new(&env).whnf(&default_applied).kind()
    );
}

// =============================================================================
// THE PROBE (override): a long-form `instance … where` on an imported class
// that PROVIDES the `tag` field. This is the path B51 pinned as failing; it now
// elaborates, kernel-checks, registers, and `Widget.tag` of it reduces to the
// override 3 (NOT the default 7).
// =============================================================================

#[test]
fn test_longform_instance_where_override_on_imported_class() {
    let mut env = imported_widget_env();

    // Keep the lambda field last here; the dedicated regression below covers
    // the opposite order and proves the parser terminates the lambda body at the
    // next field-assignment boundary.
    elaborate_decls_into(
        &mut env,
        "instance instWidgetFoo : Widget Foo where\n  \
         tag := Nat.succ (Nat.succ (Nat.succ Nat.zero))\n  \
         render := fun _ => Nat.succ Nat.zero",
    );

    // The instance must be registered under a global name. The long-form path
    // generates `inst<ClassName><TypeArg>` when a name is given we use that.
    let inst = env
        .get_const(&Name::from_string("instWidgetFoo"))
        .expect("instWidgetFoo should be registered as a definition");
    // An explicit tag must NOT pull in the default definition.
    let referenced = inst
        .value
        .as_ref()
        .expect("instWidgetFoo body")
        .collect_constants();
    assert!(
        !referenced.contains(&Name::from_string("Widget.tag._default")),
        "an explicit tag must NOT pull in Widget.tag._default, got: {referenced:?}"
    );

    let tag = Expr::apps(
        const_("Widget.tag"),
        [const_("Foo"), const_("instWidgetFoo")],
    );
    assert!(
        def_eq(&env, &tag, &nat_lit(3)),
        "long-form override instance must take tag = 3, got {:?}",
        TypeChecker::new(&env).whnf(&tag).kind()
    );
    assert!(
        !def_eq(&env, &tag, &nat_lit(7)),
        "the override must be 3, never the default 7"
    );

    // The provided render field still reduces correctly.
    let rendered = Expr::apps(
        const_("Widget.render"),
        [const_("Foo"), const_("instWidgetFoo"), const_("Foo.mk")],
    );
    assert!(
        def_eq(&env, &rendered, &nat_lit(1)),
        "the provided render field must reduce to 1, got {:?}",
        TypeChecker::new(&env).whnf(&rendered).kind()
    );
}

// =============================================================================
// THE PROBE (default fill): a long-form `instance … where` on an imported class
// that OMITS the defaulted `tag` method. The omitted field must be filled from
// `Widget.tag._default` (routed through the B51 struct-literal machinery), so
// `Widget.tag` of it reduces to the default 7 (NOT the override 3).
// =============================================================================

#[test]
fn test_longform_instance_where_omitting_default_uses_default_value() {
    let mut env = imported_widget_env();

    elaborate_decls_into(
        &mut env,
        "instance instWidgetFooDefault : Widget Foo where\n  \
         render := fun _ => Nat.succ Nat.zero",
    );

    // The stored body must reference the imported default definition, proving the
    // long-form path filled the omitted field from `Widget.tag._default`.
    let body = env
        .get_const(&Name::from_string("instWidgetFooDefault"))
        .and_then(|i| i.value.clone())
        .expect("instWidgetFooDefault body");
    let referenced = body.collect_constants();
    assert!(
        referenced.contains(&Name::from_string("Widget.tag._default")),
        "the omitted default method must be filled from Widget.tag._default \
         on the long-form path, got: {referenced:?}"
    );

    let tag = Expr::apps(
        const_("Widget.tag"),
        [const_("Foo"), const_("instWidgetFooDefault")],
    );
    assert!(
        def_eq(&env, &tag, &nat_lit(7)),
        "a long-form instance omitting the default method must take tag = 7, got {:?}",
        TypeChecker::new(&env).whnf(&tag).kind()
    );
    assert!(
        !def_eq(&env, &tag, &nat_lit(3)),
        "the omitted default must be 7, never the override 3"
    );

    let rendered = Expr::apps(
        const_("Widget.render"),
        [
            const_("Foo"),
            const_("instWidgetFooDefault"),
            const_("Foo.mk"),
        ],
    );
    assert!(
        def_eq(&env, &rendered, &nat_lit(1)),
        "the provided render field must reduce to 1, got {:?}",
        TypeChecker::new(&env).whnf(&rendered).kind()
    );
}

// =============================================================================
// Negative control: a long-form instance omitting a field that has NO default
// is still a hard error. The default-fill route must not over-broaden the
// missing-field check. `where tag := 5` omits the no-default `render` field.
// =============================================================================

#[test]
fn test_longform_instance_where_omitting_non_default_field_is_rejected() {
    let mut env = imported_widget_env();

    let result = try_elaborate_decls_into(
        &mut env,
        "instance instWidgetFooBad : Widget Foo where\n  \
         tag := Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))",
    );
    assert!(
        result.is_err(),
        "omitting the no-default `render` field on the long-form path must still \
         be a missing-field error, got Ok"
    );
    assert!(
        env.get_const(&Name::from_string("instWidgetFooBad"))
            .is_none(),
        "the rejected long-form instance must not register instWidgetFooBad"
    );
}

// =============================================================================
// Native control: the long-form `where` path on a NATIVE class (one that DOES
// carry a clean-side field-name table) is UNCHANGED — the import fallback only
// fires when the table is absent. We declare a class natively (via the surface
// `class … where` command, which registers the field table) and define a
// long-form instance, then check it reduces correctly. This proves the fix is a
// pure fallback and does not regress the native path.
// =============================================================================

#[test]
fn test_longform_instance_where_on_native_class_unchanged() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");

    elaborate_decls_into(
        &mut env,
        "class Gadget (α : Type) where\n  \
         size : Nat\n\
         instance instGadgetNat : Gadget Nat where\n  \
         size := Nat.succ (Nat.succ Nat.zero)",
    );

    // The native class carries a field-name table (the path the import fallback
    // deliberately does not touch).
    assert!(
        env.get_structure_field_names(&Name::from_string("Gadget"))
            .is_some(),
        "a natively-declared class must carry a clean-side field-name table"
    );

    let size = Expr::apps(
        const_("Gadget.size"),
        [const_("Nat"), const_("instGadgetNat")],
    );
    assert!(
        def_eq(&env, &size, &nat_lit(2)),
        "native long-form instance must reduce Gadget.size to 2, got {:?}",
        TypeChecker::new(&env).whnf(&size).kind()
    );
}

// Parser/elaborator regression: a lambda-valued field followed by another field
// must stop at the assignment boundary, register both fields, and preserve the
// explicit override.
#[test]
fn test_longform_instance_where_lambda_field_before_next_field() {
    let mut env = imported_widget_env();

    elaborate_decls_into(
        &mut env,
        "instance instWidgetFooLambdaFirst : Widget Foo where\n  \
         render := fun _ => Nat.succ Nat.zero\n  \
         tag := Nat.succ (Nat.succ (Nat.succ Nat.zero))",
    );

    let tag = Expr::apps(
        const_("Widget.tag"),
        [const_("Foo"), const_("instWidgetFooLambdaFirst")],
    );
    assert!(
        def_eq(&env, &tag, &nat_lit(3)),
        "lambda-first long-form instance must preserve the following tag = 3, got {:?}",
        TypeChecker::new(&env).whnf(&tag).kind()
    );
}
