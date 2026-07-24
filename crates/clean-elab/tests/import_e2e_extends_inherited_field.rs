// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: an *imported* structure with `extends` — projecting an
//! **inherited** (parent) field, and structure-update on an inherited field.
//!
//! ## The Lean `extends` layout (what a real `.olean` ships)
//!
//! For `structure Child extends Parent where co : Nat`, Lean compiles `Child`
//! with a **nested** parent: the constructor is
//! `Child.mk (toParent : Parent) (co : Nat)`, not a flattened
//! `Child.mk (pf : Nat) (co : Nat)`. The inherited projection
//! `Child.pf : Child → Nat` is *not* a kernel `Proj` on `Child`; it is the
//! **composition** `Parent.pf (Child.toParent self)`. Lean ships these as
//! ordinary projection *functions*:
//!   - `Parent.pf  : Parent → Nat := fun s => Proj(Parent, 0, s)`
//!   - `Child.toParent : Child → Parent := fun s => Proj(Child, 0, s)`
//!   - `Child.co   : Child  → Nat := fun s => Proj(Child, 1, s)`
//!   - `Child.pf   : Child  → Nat := fun s => Parent.pf (Child.toParent s)`
//!
//! Critically, a real `.olean` carries **no** clean-side `structure_fields`
//! table (that table is produced only by clean's own structure elaborator /
//! exporter — the same condition the B43/B44/B45/B47 imported work had to
//! handle). So clean-elab must answer `c.pf` (an *inherited* field) and
//! `{ c with pf := v }` by routing through Lean's projection functions, not by
//! consulting an (absent) field table on `Child`.
//!
//! Note that clean's *native* `extends` elaborator (`structure_extend.rs`)
//! **flattens** parent fields into the child constructor, so the native `Child`
//! would be `Child.mk (pf : Nat) (co : Nat)` with `pf` a direct field. The
//! imported layout here (nested `toParent`) is deliberately the *non*-flattened
//! Lean shape — this is exactly the native-vs-import divergence the scenario
//! targets.
//!
//! ## Synthesize-as-import
//!
//! No shipped `Parent`/`Child` `.olean` fixture exists, so we build the kernel
//! declarations by hand in a fresh environment and register **only** the
//! inductives and Lean's projection *functions* — never a `structure_fields`
//! table and never `register_structure_fields`. That reproduces the real
//! `.olean` condition byte-for-byte at the elaborator's decision points. We
//! assert the precondition (no field table on either struct) explicitly so the
//! test stays honest if the importer ever starts shipping one.
//!
//! ## What is asserted
//!
//! - `def getInherited (c : Child) : Nat := c.pf` elaborates, kernel-checks,
//!   and *reduces* to the genuine inherited value (distinct from the child's
//!   own field, so a slot mix-up is observable).
//! - `def getOwn (c : Child) : Nat := c.co` reduces to the child's own value.
//! - `def getParentDirect (p : Parent) : Nat := p.pf` (the non-inherited
//!   control) reduces correctly.
//! - Structure-update on an inherited field, `{ c with pf := v }`, is probed:
//!   if it elaborates + reduces correctly it is locked in; if it is a genuine
//!   missing feature (rather than a wrong reduction) the failure mode is pinned
//!   with a flip-on-fix assertion and explained.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::{
    BinderInfo, Constructor, Declaration, Expr, ExprKind, InductiveDecl, InductiveType, Name,
    TypeChecker,
};
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

/// Reduce `expr` to WHNF and return the head constant's name, if any.
fn whnf_head_const(env: &Environment, expr: &Expr) -> Option<String> {
    let tc = TypeChecker::new(env);
    let reduced = tc.whnf(expr);
    match reduced.kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

/// Definitional equality (used where the result normalizes to a kernel `Nat`
/// literal rather than a `Const`-headed term).
fn def_eq(env: &Environment, expr: &Expr, reference: &Expr) -> bool {
    let tc = TypeChecker::new(env);
    tc.is_def_eq(expr, reference)
}

/// Elaborate and register a sequence of declarations from `source`, threading a
/// shared `FileContext`. `elaborate_decl_and_register` runs the full kernel type
/// check, so reaching the end means every body kernel-checked.
fn elaborate_decls_into(env: &mut Environment, source: &str) {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("source should parse");
    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed)
            .unwrap_or_else(|e| panic!("declaration {i} should elaborate and kernel-check: {e}"));
    }
}

/// Try-version: returns the elaboration/registration error instead of panicking.
fn try_elaborate_decls_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse: {e}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed).map_err(|e| format!("{e}"))?;
    }
    Ok(())
}

/// Build the imported `Parent` / `Child extends Parent` environment by hand,
/// in the exact shape a real Lean `.olean` ships:
///   * monomorphic single-constructor inductives `Parent`, `Child : Type`,
///   * `Child.mk` takes a NESTED `toParent : Parent` (not flattened parent
///     fields),
///   * Lean's projection *functions* for every field (own and inherited),
///   * **no** `structure_fields` table for either structure.
fn imported_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");

    let ty = Expr::type_();
    let parent = const_("Parent");
    let child = const_("Child");
    let nat = const_("Nat");

    // ---- Parent : Type, Parent.mk (pf : Nat) : Parent ----
    // Parent.mk : Nat → Parent
    let parent_mk_type = Expr::pi(BinderInfo::Default, nat.clone(), parent.clone());
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Parent"),
            type_: ty.clone(),
            constructors: vec![Constructor {
                name: Name::from_string("Parent.mk"),
                type_: parent_mk_type,
            }],
        }],
    })
    .expect("add Parent inductive");

    // Parent.pf : Parent → Nat := fun s => Proj(Parent, 0, s)
    env.add_decl(Declaration::Definition {
        name: Name::from_string("Parent.pf"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, parent.clone(), nat.clone()),
        value: Expr::lam(
            BinderInfo::Default,
            parent.clone(),
            Expr::proj(Name::from_string("Parent"), 0, Expr::bvar(0)),
        ),
        is_reducible: true,
    })
    .expect("add Parent.pf");

    // ---- Child : Type, Child.mk (toParent : Parent) (co : Nat) : Child ----
    // Child.mk : Parent → Nat → Child
    let child_mk_type = Expr::pi(
        BinderInfo::Default,
        parent.clone(),
        Expr::pi(BinderInfo::Default, nat.clone(), child.clone()),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Child"),
            type_: ty.clone(),
            constructors: vec![Constructor {
                name: Name::from_string("Child.mk"),
                type_: child_mk_type,
            }],
        }],
    })
    .expect("add Child inductive");

    // Child.toParent : Child → Parent := fun s => Proj(Child, 0, s)
    env.add_decl(Declaration::Definition {
        name: Name::from_string("Child.toParent"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, child.clone(), parent.clone()),
        value: Expr::lam(
            BinderInfo::Default,
            child.clone(),
            Expr::proj(Name::from_string("Child"), 0, Expr::bvar(0)),
        ),
        is_reducible: true,
    })
    .expect("add Child.toParent");

    // Child.co : Child → Nat := fun s => Proj(Child, 1, s)
    env.add_decl(Declaration::Definition {
        name: Name::from_string("Child.co"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, child.clone(), nat.clone()),
        value: Expr::lam(
            BinderInfo::Default,
            child.clone(),
            Expr::proj(Name::from_string("Child"), 1, Expr::bvar(0)),
        ),
        is_reducible: true,
    })
    .expect("add Child.co");

    // Child.pf : Child → Nat := fun s => Parent.pf (Child.toParent s)
    // This is the INHERITED projection — the defining Lean shape (composition
    // through `toParent`), NOT a direct `Proj(Child, _, s)`.
    let child_pf_body = Expr::lam(
        BinderInfo::Default,
        child.clone(),
        Expr::app(
            const_("Parent.pf"),
            Expr::app(const_("Child.toParent"), Expr::bvar(0)),
        ),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("Child.pf"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, child.clone(), nat.clone()),
        value: child_pf_body,
        is_reducible: true,
    })
    .expect("add Child.pf");

    env
}

/// `Child.mk (Parent.mk pf) co` — a concrete child with distinct field values.
fn child_value(pf: u32, co: u32) -> Expr {
    let parent = Expr::app(const_("Parent.mk"), nat_lit(pf));
    Expr::apps(const_("Child.mk"), [parent, nat_lit(co)])
}

// =============================================================================
// Precondition: this is genuinely the imported `extends` configuration —
// inductives + Lean projection functions present, no clean-side field table,
// and `Child.pf` is the *composition* through `toParent` (not a direct Proj).
// =============================================================================

#[test]
fn test_imported_extends_has_no_clean_field_table_and_composed_inherited_proj() {
    let env = imported_env();

    for ind in ["Parent", "Child"] {
        assert!(
            env.get_inductive(&Name::from_string(ind)).is_some(),
            "{ind} inductive should be imported"
        );
        assert!(
            env.get_structure_field_names(&Name::from_string(ind))
                .is_none(),
            "imported {ind} must NOT carry a clean-side structure_fields table — \
             this is the exact condition that forces inherited-field resolution \
             through Lean's projection functions"
        );
    }

    for proj in ["Parent.pf", "Child.toParent", "Child.co", "Child.pf"] {
        assert!(
            env.get_const(&Name::from_string(proj)).is_some(),
            "{proj} projection function should be imported"
        );
    }

    // `Child.mk` must take the NESTED parent (`toParent : Parent`) as its first
    // field, i.e. it is NOT the flattened `Nat → Nat → Child` native shape.
    let mk = env
        .get_const(&Name::from_string("Child.mk"))
        .expect("Child.mk should be imported");
    match mk.type_.kind() {
        ExprKind::Pi(_, dom, _) => {
            assert_eq!(
                dom.get_app_fn().kind(),
                Expr::const_(Name::from_string("Parent"), vec![]).kind(),
                "Child.mk's first field must be the nested `toParent : Parent`, \
                 confirming the (non-flattened) Lean `extends` layout"
            );
        }
        other => panic!("Child.mk should be a Pi, got {other:?}"),
    }

    // `Child.pf`'s body must be the COMPOSITION `Parent.pf (Child.toParent …)`,
    // not a kernel `Proj(Child, _, …)`. This is what makes the inherited field
    // genuinely "inherited" rather than a flattened own field.
    let child_pf = env
        .get_const(&Name::from_string("Child.pf"))
        .expect("Child.pf should be imported");
    let body = child_pf
        .value
        .as_ref()
        .expect("Child.pf has a body")
        .collect_constants();
    assert!(
        body.contains(&Name::from_string("Parent.pf"))
            && body.contains(&Name::from_string("Child.toParent")),
        "Child.pf must compose Parent.pf through Child.toParent (inherited \
         projection), got constants: {body:?}"
    );
}

// =============================================================================
// Dot-notation on an INHERITED field: `c.pf` must resolve through Lean's
// `Child.pf` function and reduce to the parent's stored value.
// =============================================================================

#[test]
fn test_dot_notation_on_inherited_field_reduces_to_parent_value() {
    let mut env = imported_env();

    // getInherited c = c.pf ; getOwn c = c.co.
    // Distinct values (pf = 7, co = 3) so a field mix-up is observable.
    elaborate_decls_into(
        &mut env,
        "def getInherited (c : Child) : Nat := c.pf\n\
         def getOwn (c : Child) : Nat := c.co",
    );

    // `c.pf` must lower to the imported inherited projection `Child.pf`
    // (dot-notation fallback), proving we are on the import path, not a Proj.
    let get_inherited = env
        .get_const(&Name::from_string("getInherited"))
        .expect("getInherited registered");
    let body = get_inherited
        .value
        .as_ref()
        .expect("getInherited has a body")
        .collect_constants();
    assert!(
        body.contains(&Name::from_string("Child.pf")),
        "c.pf on an imported `extends` struct must resolve to the inherited \
         projection function Child.pf, got: {body:?}"
    );

    // c = Child.mk (Parent.mk 7) 3  →  c.pf = 7, c.co = 3.
    let c = child_value(7, 3);

    let inherited = Expr::app(const_("getInherited"), c.clone());
    assert!(
        def_eq(&env, &inherited, &nat_lit(7)),
        "c.pf must reduce to the inherited parent value 7, got {:?}",
        TypeChecker::new(&env).whnf(&inherited).kind()
    );
    // Guard against reading the child's own slot instead of the parent's.
    assert!(
        !def_eq(&env, &inherited, &nat_lit(3)),
        "c.pf must NOT read the child's own field (3)"
    );

    let own = Expr::app(const_("getOwn"), c);
    assert!(
        def_eq(&env, &own, &nat_lit(3)),
        "c.co must reduce to the child's own value 3, got {:?}",
        TypeChecker::new(&env).whnf(&own).kind()
    );
}

// =============================================================================
// Control: dot-notation on the parent's OWN field (`p.pf`, non-inherited) must
// reduce correctly too — isolates any inherited-specific regression.
// =============================================================================

#[test]
fn test_dot_notation_on_parent_own_field_reduces_correctly() {
    let mut env = imported_env();

    elaborate_decls_into(&mut env, "def getParentDirect (p : Parent) : Nat := p.pf");

    let p = Expr::app(const_("Parent.mk"), nat_lit(5));
    let direct = Expr::app(const_("getParentDirect"), p);
    assert!(
        def_eq(&env, &direct, &nat_lit(5)),
        "p.pf on the parent itself must reduce to 5, got {:?}",
        TypeChecker::new(&env).whnf(&direct).kind()
    );
}

// =============================================================================
// Structure-update on an INHERITED field: `{ c with pf := v }`.
//
// This is the structure-update analogue of the inherited-projection path. The
// struct-update elaborator (`elab_struct_lit.rs`) rebuilds the constructor,
// taking the updated field from `v` and *unchanged* fields by projecting the
// base. For an imported `extends` struct, `pf` is NOT a direct constructor
// field of `Child` (the fields are `toParent` and `co`): it is reachable only
// through the nested `toParent` subobject. The fix rewrites such an inherited
// update into a nested update of the parent subobject:
//   `{ c with pf := v }` ⇝ `{ c with toParent := { c.toParent with pf := v } }`
// so it must now elaborate, kernel-check, and reduce correctly.
// =============================================================================

#[test]
fn test_structure_update_on_inherited_field_replaces_and_preserves() {
    let mut env = imported_env();

    // c = Child.mk (Parent.mk 7) 3. `{ c with pf := 2 }` keeps `co = 3` and
    // rebuilds the nested parent so the inherited `pf` becomes 2.
    elaborate_decls_into(
        &mut env,
        "def upd (c : Child) : Child := { c with pf := Nat.succ (Nat.succ Nat.zero) }",
    );

    let c = child_value(7, 3);
    let upd_c = Expr::app(const_("upd"), c);

    // pf must be REPLACED with 2 (read back through the inherited projection).
    // Distinct from the original 7 (so a no-op update fails) and from co=3
    // (so writing into the wrong subobject/slot fails).
    let upd_pf = Expr::app(const_("Child.pf"), upd_c.clone());
    assert!(
        def_eq(&env, &upd_pf, &nat_lit(2)),
        "{{ c with pf := 2 }} must set the inherited pf to 2, got {:?}",
        TypeChecker::new(&env).whnf(&upd_pf).kind()
    );
    assert!(
        !def_eq(&env, &upd_pf, &nat_lit(7)),
        "{{ c with pf := 2 }} must actually replace pf (not leave it at 7)"
    );

    // co must be PRESERVED as 3 (the child's own field is untouched by an
    // inherited-field update).
    let upd_co = Expr::app(const_("Child.co"), upd_c);
    assert!(
        def_eq(&env, &upd_co, &nat_lit(3)),
        "{{ c with pf := 2 }} must preserve the child's own co (= 3), got {:?}",
        TypeChecker::new(&env).whnf(&upd_co).kind()
    );
}

// =============================================================================
// Mixed update: an inherited field AND an own field at once.
// `{ c with pf := 1, co := 4 }` must rebuild the nested parent for `pf` while
// directly replacing `co`. Distinct target values pin every slot.
// =============================================================================

#[test]
fn test_structure_update_mixed_inherited_and_own_fields() {
    let mut env = imported_env();

    elaborate_decls_into(
        &mut env,
        "def upd2 (c : Child) : Child := \
         { c with pf := Nat.succ Nat.zero, co := Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))) }",
    );

    let c = child_value(7, 3);
    let upd_c = Expr::app(const_("upd2"), c);

    let upd_pf = Expr::app(const_("Child.pf"), upd_c.clone());
    assert!(
        def_eq(&env, &upd_pf, &nat_lit(1)),
        "mixed update must set the inherited pf to 1, got {:?}",
        TypeChecker::new(&env).whnf(&upd_pf).kind()
    );

    let upd_co = Expr::app(const_("Child.co"), upd_c);
    assert!(
        def_eq(&env, &upd_co, &nat_lit(4)),
        "mixed update must set the own co to 4, got {:?}",
        TypeChecker::new(&env).whnf(&upd_co).kind()
    );
}

// =============================================================================
// Structure-update on the child's OWN field: `{ c with co := v }`. This uses a
// direct `Child` constructor field, so it should work via the existing imported
// struct-update path (B47). Locks that in for the `extends` shape and confirms
// the unchanged inherited parent is preserved.
// =============================================================================

#[test]
fn test_structure_update_on_own_field_behavior() {
    let mut env = imported_env();

    let result = try_elaborate_decls_into(
        &mut env,
        "def updOwn (c : Child) : Child := { c with co := Nat.succ (Nat.succ Nat.zero) }",
    );

    if result.is_ok() {
        // co := 2 (replaced), pf := 7 (preserved through the unchanged toParent).
        let c = child_value(7, 3);
        let upd_c = Expr::app(const_("updOwn"), c);

        let upd_co = Expr::app(const_("Child.co"), upd_c.clone());
        assert!(
            def_eq(&env, &upd_co, &nat_lit(2)),
            "{{ c with co := 2 }} must set co to 2, got {:?}",
            TypeChecker::new(&env).whnf(&upd_co).kind()
        );

        let upd_pf = Expr::app(const_("Child.pf"), upd_c);
        assert!(
            def_eq(&env, &upd_pf, &nat_lit(7)),
            "{{ c with co := 2 }} must preserve the inherited pf (= 7 via the \
             unchanged toParent), got {:?}",
            TypeChecker::new(&env).whnf(&upd_pf).kind()
        );
    } else {
        // Pin the failure mode if even the own-field update regresses on the
        // `extends` (nested-toParent) shape.
        let err = result.expect_err("branch invariant: result is Err here");
        panic!(
            "structure-update on the child's OWN field `co` should work on an \
             imported `extends` struct (direct constructor field), got: {err}"
        );
    }
}
