// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: construction, dependent-field PROJECTION, and dependency-
//! preserving structure-UPDATE on an *imported* structure whose later field's
//! TYPE depends on an earlier field's VALUE (dependent_struct_field scenario).
//!
//! ## The structure
//!
//! ```text
//! inductive Box : Nat -> Type        -- Box.mk : (n : Nat) -> Box n
//!   | mk : (n : Nat) -> Box n
//!
//! structure DPair where              -- single-constructor inductive
//!   tag  : Nat
//!   data : Box tag                   -- DEPENDENT: data's type mentions tag's value
//! ```
//!
//! `DPair.mk : (tag : Nat) -> (data : Box tag) -> DPair`. The second field's
//! type `Box tag` is a *loose telescope-relative* reference to the earlier
//! field: in the constructor's Pi telescope it is `Box (BVar 0)` (the `tag`
//! binder). `Box` is a genuine indexed family — `Box Nat.zero` and
//! `Box (Nat.succ Nat.zero)` are *distinct* types — so a mis-instantiation of
//! the dependent field's type (the bug class) is observable: the kernel either
//! rejects the construction/projection, or a wrong slot reduces to a witness at
//! the wrong index.
//!
//! ## Why this differs from the existing `subtype_sigma` / `indexed_family`
//! probes
//!
//! `import_e2e_subtype_sigma` exercises `Sigma.snd` but with a *constant*
//! `β := fun _ => Nat`, so the genuine dependency `β (Sigma.fst p)` is masked.
//! `import_e2e_indexed_family_recursor` (B48) pins the dependent-field bug in
//! the **match-arm** binding path (`IVec.icons`'s `tail : IVec n`). This file
//! targets the *analogous* path in structure **construction** (`elab_struct_lit`),
//! dependent-field **projection** (`elab_proj` dot-notation fallback), and a
//! dependency-preserving structure **update** (`{ s with data := ... }`), where
//! the same B48-class issue (a loose telescope-relative field-type reference
//! mis-instantiated for an import) could independently persist.
//!
//! ## Synthesize-as-import (mirrors `import_e2e_subtype_sigma`)
//!
//! A real Lean `.olean` registers `DPair` as a single-constructor inductive
//! together with Lean's own projection *functions* (`DPair.tag : DPair -> Nat`,
//! `DPair.data : (s : DPair) -> Box (DPair.tag s)`) whose bodies are kernel
//! `Proj` nodes — but it carries **no** clean-side `structure_fields` table
//! (that table is produced only by clean's own structure elaborator). With no
//! field table, `Environment::get_structure_field_names(DPair)` is `None`, so
//! `s.data` routes through the dot-notation fallback (`elab_proj.rs`) and a
//! struct literal `{ tag := .., data := .. }` resolves its field indices through
//! Lean's projection functions (`elab_struct_lit.rs::struct_field_index`).
//!
//! We build `Box`, `DPair`, and the two projection functions with the kernel in
//! a scratch env (so everything is kernel-checked and bit-identical to native),
//! then copy them verbatim into a fresh env **without** calling
//! `register_structure_fields`. The declarations are identical to native ones;
//! the *only* difference is the missing field table — exactly the import
//! condition. We assert that precondition so the test stays honest if the
//! importer ever starts shipping a field table.
//!
//! The native path (which *does* register `structure_fields`, lowering `s.data`
//! to a kernel `Proj`) is exercised as a control so any regression is isolated
//! to the elaborator's struct-literal / dot-notation lowering rather than to
//! kernel projection reduction.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::{
    BinderInfo, Constructor, Declaration, Expr, ExprKind, InductiveDecl, InductiveType, Name,
    TypeChecker,
};
use clean_parser::parse_file;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn succ(n: Expr) -> Expr {
    Expr::app(const_("Nat.succ"), n)
}

/// `Box n` (the family applied to its single index).
fn box_at(n: Expr) -> Expr {
    Expr::app(const_("Box"), n)
}

/// `Box.mk n : Box n`.
fn box_mk(n: Expr) -> Expr {
    Expr::app(const_("Box.mk"), n)
}

/// Reduce `expr` to WHNF and return its head `Const` name (handles both bare
/// constants and constructor applications).
fn whnf_head_const(env: &Environment, expr: &Expr) -> Option<String> {
    let tc = TypeChecker::new(env);
    let reduced = tc.whnf(expr);
    match reduced.get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

/// Whether `expr` is definitionally equal to `reference`.
fn def_eq(env: &Environment, expr: &Expr, reference: &Expr) -> bool {
    let tc = TypeChecker::new(env);
    tc.is_def_eq(expr, reference)
}

// ---------------------------------------------------------------------------
// Building the dependent structure with the kernel (then importing it).
// ---------------------------------------------------------------------------

/// `Box : Nat -> Type` with `Box.mk : (n : Nat) -> Box n`.
fn box_decl() -> InductiveDecl {
    // Box : Nat -> Type
    let box_ty = Expr::pi(BinderInfo::Default, const_("Nat"), Expr::type_());
    // Box.mk : (n : Nat) -> Box n   (n = BVar(0) under [n])
    let mk_ty = Expr::pi(BinderInfo::Default, const_("Nat"), box_at(Expr::bvar(0)));
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Box"),
            type_: box_ty,
            constructors: vec![Constructor {
                name: Name::from_string("Box.mk"),
                type_: mk_ty,
            }],
        }],
    }
}

/// `DPair` single-constructor inductive with the dependent constructor
/// `DPair.mk : (tag : Nat) -> (data : Box tag) -> DPair`.
fn dpair_decl() -> InductiveDecl {
    // DPair : Type
    let dpair_ty = Expr::type_();
    // DPair.mk : (tag : Nat) -> (data : Box tag) -> DPair
    //   `data`'s type is `Box tag`; under [tag] the `tag` binder is BVar(0).
    let data_ty = box_at(Expr::bvar(0));
    let mk_ty = Expr::pi(BinderInfo::Default, data_ty, const_("DPair")); // data
    let mk_ty = Expr::pi(BinderInfo::Default, const_("Nat"), mk_ty); // tag
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("DPair"),
            type_: dpair_ty,
            constructors: vec![Constructor {
                name: Name::from_string("DPair.mk"),
                type_: mk_ty,
            }],
        }],
    }
}

/// Build a scratch env holding the kernel-checked `Box`, `DPair`, and Lean's two
/// projection functions:
///
/// ```text
/// DPair.tag  : DPair -> Nat               := fun s => Proj(DPair, 0, s)
/// DPair.data : (s : DPair) -> Box (DPair.tag s) := fun s => Proj(DPair, 1, s)
/// ```
///
/// `DPair.data`'s declared return type is `Box (DPair.tag s)` — the *dependent*
/// projection shape a real `.olean` ships.
fn native_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.add_inductive(box_decl()).expect("add Box");
    env.add_inductive(dpair_decl()).expect("add DPair");

    // DPair.tag : DPair -> Nat := fun s => Proj(DPair, 0, s)
    let tag_type = Expr::pi(BinderInfo::Default, const_("DPair"), const_("Nat"));
    let tag_value = Expr::lam(
        BinderInfo::Default,
        const_("DPair"),
        Expr::proj(Name::from_string("DPair"), 0, Expr::bvar(0)),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("DPair.tag"),
        level_params: vec![],
        type_: tag_type,
        value: tag_value,
        is_reducible: true,
    })
    .expect("add DPair.tag");

    // DPair.data : (s : DPair) -> Box (DPair.tag s) := fun s => Proj(DPair, 1, s)
    //   return type: `Box (DPair.tag s)` with s = BVar(0).
    let data_ret = box_at(Expr::app(const_("DPair.tag"), Expr::bvar(0)));
    let data_type = Expr::pi(BinderInfo::Default, const_("DPair"), data_ret);
    let data_value = Expr::lam(
        BinderInfo::Default,
        const_("DPair"),
        Expr::proj(Name::from_string("DPair"), 1, Expr::bvar(0)),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("DPair.data"),
        level_params: vec![],
        type_: data_type,
        value: data_value,
        is_reducible: true,
    })
    .expect("add DPair.data");

    // Match a real `.olean`: clean's own structure elaborator would register a
    // field table here, so `native_env` does it to serve as the control. The
    // imported env below deliberately skips it.
    env.register_structure_fields(
        Name::from_string("DPair"),
        vec![Name::from_string("tag"), Name::from_string("data")],
    )
    .expect("register DPair fields (native control)");

    env
}

/// Build an environment that has `Box`, `DPair`, and the two projection
/// functions the way a real `.olean` import does: the inductives + projection
/// *functions* are present, but there is **no** clean-side `structure_fields`
/// table for `DPair`. The declarations are copied verbatim from a kernel-built
/// scratch env, so they are bit-identical to the native ones — the only
/// difference is the missing field table.
fn imported_env() -> Environment {
    let src = native_env();

    let mut dst = Environment::new();
    dst.init_nat().expect("init_nat");

    for ind_name in ["Box", "DPair"] {
        let ind = src
            .get_inductive(&Name::from_string(ind_name))
            .unwrap_or_else(|| panic!("scratch env has {ind_name}"));
        let ctor_name = ind
            .constructor_names
            .first()
            .expect("single-constructor inductive should have one constructor");
        let ctor = src
            .get_constructor(ctor_name)
            .expect("scratch env has the constructor");
        dst.add_inductive(InductiveDecl {
            level_params: ind.level_params.clone(),
            num_params: ind.num_params,
            types: vec![InductiveType {
                name: ind.name.clone(),
                type_: ind.type_.clone(),
                constructors: vec![Constructor {
                    name: ctor.name.clone(),
                    type_: ctor.type_.clone(),
                }],
            }],
        })
        .unwrap_or_else(|e| panic!("re-adding imported {ind_name}: {e}"));
    }

    for fn_name in ["DPair.tag", "DPair.data"] {
        let info = src
            .get_const(&Name::from_string(fn_name))
            .unwrap_or_else(|| panic!("scratch env has {fn_name}"));
        let value = info
            .value
            .clone()
            .unwrap_or_else(|| panic!("{fn_name} should have a body"));
        dst.add_decl(Declaration::Definition {
            name: info.name.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value,
            is_reducible: true,
        })
        .unwrap_or_else(|e| panic!("re-adding imported {fn_name}: {e}"));
    }

    dst
}

/// Elaborate + register a sequence of declarations from `source`. Reaching the
/// end means every body kernel-checked (`elaborate_decl_and_register` runs the
/// full kernel type check for each definition).
fn elaborate_decls_into(env: &mut Environment, source: &str) {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("source should parse");
    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed)
            .unwrap_or_else(|e| panic!("declaration {i} should elaborate and kernel-check: {e}"));
    }
}

/// Try-version: returns the first elaboration/registration error instead of
/// panicking, for diagnostics that want to pin a failure mode with a message.
fn try_elaborate_decls_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse: {e}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed).map_err(|e| format!("{e}"))?;
    }
    Ok(())
}

// ===========================================================================
// Precondition: the synthesized environment matches the *import* configuration
// (inductives + projection functions present, no clean-side field table).
// ===========================================================================

#[test]
fn test_imported_dpair_has_no_clean_field_table() {
    let env = imported_env();

    for ind in ["Box", "DPair"] {
        assert!(
            env.get_inductive(&Name::from_string(ind)).is_some(),
            "{ind} inductive should be imported"
        );
    }
    assert!(
        env.get_structure_field_names(&Name::from_string("DPair"))
            .is_none(),
        "an imported DPair must NOT carry a clean-side structure_fields table — \
         this is the exact condition that routes `.data` through the dot-notation \
         fallback and drives the struct literal off Lean's projection functions"
    );
    for proj in ["DPair.tag", "DPair.data"] {
        assert!(
            env.get_const(&Name::from_string(proj)).is_some(),
            "{proj} projection function should be imported"
        );
    }
    // The dependent-projection function carries the genuinely dependent return
    // type `Box (DPair.tag s)` — so this really is the dependent-field shape.
    let data_ty = env
        .get_const(&Name::from_string("DPair.data"))
        .expect("DPair.data present")
        .type_
        .clone();
    assert!(
        data_ty
            .collect_constants()
            .contains(&Name::from_string("DPair.tag")),
        "DPair.data's type must mention DPair.tag (the dependency on the earlier \
         field's value), got: {data_ty:?}"
    );
}

// ===========================================================================
// Construction: a struct literal `{ tag := k, data := Box.mk k }` on the
// imported DPair must elaborate, kernel-check (so `data`'s expected type
// `Box tag` is correctly instantiated to `Box k`), and reduce so that each
// field selects the correct, distinct value.
// ===========================================================================

#[test]
fn test_imported_dpair_struct_literal_constructs_dependent_field() {
    let mut env = imported_env();

    // tag := 1, data := Box.mk 1 : Box 1. The literal must instantiate the
    // dependent field type `Box tag` to `Box 1` for `data` to type-check.
    // A wrong instantiation (e.g. `Box 0`, the un-substituted telescope shape)
    // would make `Box.mk 1 : Box 1` mismatch and the kernel reject it.
    elaborate_decls_into(
        &mut env,
        "def one : Nat := Nat.succ Nat.zero\n\
         def p : DPair := { tag := one, data := Box.mk one }",
    );

    // `p` must reduce to `DPair.mk 1 (Box.mk 1)`.
    let p = const_("p");
    assert_eq!(
        whnf_head_const(&env, &p).as_deref(),
        Some("DPair.mk"),
        "p must reduce to a DPair.mk application"
    );

    // tag field projects to 1.
    let tag = Expr::proj(Name::from_string("DPair"), 0, const_("p"));
    let one = succ(const_("Nat.zero"));
    assert!(
        def_eq(&env, &tag, &one),
        "p.tag must be 1, got {:?}",
        TypeChecker::new(&env).whnf(&tag).kind()
    );

    // data field projects to `Box.mk 1` — and crucially its *index* is 1,
    // matching the tag (so the dependent field carries the correct index).
    let data = Expr::proj(Name::from_string("DPair"), 1, const_("p"));
    assert_eq!(
        whnf_head_const(&env, &data).as_deref(),
        Some("Box.mk"),
        "p.data must reduce to a Box.mk value"
    );
    // The index carried by the projected `Box` value must be 1 (matching tag),
    // not 0 — a dependent-field mis-instantiation that lost the substitution of
    // `tag` into `Box tag` would surface the wrong-index witness `Box.mk 0`.
    assert!(
        def_eq(&env, &data, &box_mk(one.clone())),
        "p.data must be Box.mk 1 (index matching tag), got {:?}",
        TypeChecker::new(&env).whnf(&data).kind()
    );
    assert!(
        !def_eq(&env, &data, &box_mk(const_("Nat.zero"))),
        "p.data must not collapse to Box.mk 0 (lost the tag dependency)"
    );
}

// ===========================================================================
// Negative control: an *inconsistent* construction whose `data` index disagrees
// with `tag` (`{ tag := 1, data := Box.mk 0 }`, i.e. `Box.mk 0 : Box 0` against
// the expected field type `Box 1`) must be REJECTED. This proves the struct
// literal genuinely *instantiates* the dependent field type `Box tag` with the
// `tag` value rather than ignoring the dependency — without it, the positive
// reductions above could be vacuous.
// ===========================================================================

#[test]
fn test_imported_dpair_struct_literal_rejects_index_mismatch() {
    let mut env = imported_env();
    let result = try_elaborate_decls_into(
        &mut env,
        "def one : Nat := Nat.succ Nat.zero\n\
         def bad : DPair := { tag := one, data := Box.mk Nat.zero }",
    );
    assert!(
        result.is_err(),
        "a struct literal whose dependent field index (Box 0) disagrees with tag \
         (= 1) must be rejected: the field type `Box tag` must be instantiated to \
         `Box 1`, so `Box.mk 0 : Box 0` cannot fill it"
    );
}

// ===========================================================================
// Projection: a def returning the *dependent* field with the dependent return
// type `Box (DPair.tag s)` must elaborate + kernel-check (so `s.data` lowered
// through dot-notation has the correctly-instantiated dependent type) and the
// projected value must carry the right index.
// ===========================================================================

#[test]
fn test_imported_dpair_dependent_projection_reduces_correctly() {
    let mut env = imported_env();

    // getData's *declared* return type `Box (DPair.tag s)` is dependent: it
    // mentions the projection of an earlier field. Reaching the end of
    // elaboration means `s.data : Box (DPair.tag s)` kernel-checked, i.e. the
    // dependent projection lowered with the right type.
    elaborate_decls_into(
        &mut env,
        "def two : Nat := Nat.succ (Nat.succ Nat.zero)\n\
         def p2 : DPair := DPair.mk two (Box.mk two)\n\
         def getTag (s : DPair) : Nat := s.tag\n\
         def getData (s : DPair) : Box (DPair.tag s) := s.data",
    );

    // The dependent projection must lower to the imported `DPair.data` function
    // (the dot-notation fallback), proving we are genuinely on the import path
    // rather than a kernel `Proj`.
    let get_data = env
        .get_const(&Name::from_string("getData"))
        .expect("getData registered");
    let body = get_data.value.as_ref().expect("getData has a body");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("DPair.data")),
        "getData's body must compile against the imported DPair.data function, got: {:?}",
        body.collect_constants()
    );

    // getTag p2 reduces to 2.
    let get_tag = Expr::app(const_("getTag"), const_("p2"));
    let two = succ(succ(const_("Nat.zero")));
    assert!(
        def_eq(&env, &get_tag, &two),
        "getTag p2 must be 2, got {:?}",
        TypeChecker::new(&env).whnf(&get_tag).kind()
    );

    // getData p2 reduces to `Box.mk 2`. The index must be 2 — observing that the
    // dependent projection selected the right slot at the right index.
    let get_data_app = Expr::app(const_("getData"), const_("p2"));
    assert_eq!(
        whnf_head_const(&env, &get_data_app).as_deref(),
        Some("Box.mk"),
        "getData p2 must reduce to a Box.mk value"
    );
    let box_mk_two = box_mk(two.clone());
    assert!(
        def_eq(&env, &get_data_app, &box_mk_two),
        "getData p2 must be Box.mk 2 (right slot, right index), got {:?}",
        TypeChecker::new(&env).whnf(&get_data_app).kind()
    );
    // And NOT Box.mk 0 (a mis-instantiated dependency that lost the index).
    assert!(
        !def_eq(&env, &get_data_app, &box_mk(const_("Nat.zero"))),
        "getData p2 must not collapse to Box.mk 0 (lost dependency)"
    );
}

// ===========================================================================
// Update: a dependency-preserving structure update `{ s with data := .. }`
// replaces the dependent field (whose new value must satisfy `Box (s.tag)`)
// while PRESERVING `tag` (projected from the base). This keeps the dependency
// intact and exercises the unchanged-field projection of an earlier field that
// a *later* dependent field's type refers to.
// ===========================================================================

#[test]
fn test_imported_dpair_update_dependent_field_preserves_dependency() {
    let mut env = imported_env();

    // Base p3 : tag = 1, data = Box.mk 1.
    // `upd` updates only `data`. The new `data := Box.mk s.tag` must type-check
    // against `Box (s.tag)` — i.e. the update path must give the updated
    // dependent field the dependency-correct expected type `Box tag`, where
    // `tag` is *preserved from the base*. We set the new data to `Box.mk one`
    // (still index 1, matching the preserved tag) so the update is well-typed
    // and reduces with the tag preserved.
    elaborate_decls_into(
        &mut env,
        "def one : Nat := Nat.succ Nat.zero\n\
         def p3 : DPair := DPair.mk one (Box.mk one)\n\
         def upd (s : DPair) : DPair := { s with data := Box.mk s.tag }",
    );

    let upd_p3 = Expr::app(const_("upd"), const_("p3"));

    // The whole update must reduce to a DPair.mk application.
    assert_eq!(
        whnf_head_const(&env, &upd_p3).as_deref(),
        Some("DPair.mk"),
        "upd p3 must reduce to a DPair.mk application"
    );

    // tag must be PRESERVED from the base (= 1), not dropped or zeroed.
    let upd_tag = Expr::proj(Name::from_string("DPair"), 0, upd_p3.clone());
    let one = succ(const_("Nat.zero"));
    assert!(
        def_eq(&env, &upd_tag, &one),
        "upd p3 must preserve tag = 1, got {:?}",
        TypeChecker::new(&env).whnf(&upd_tag).kind()
    );

    // data must be the new `Box.mk s.tag` = `Box.mk 1`, carrying index 1
    // (consistent with the preserved tag — the dependency held through update).
    let upd_data = Expr::proj(Name::from_string("DPair"), 1, upd_p3);
    assert_eq!(
        whnf_head_const(&env, &upd_data).as_deref(),
        Some("Box.mk"),
        "upd p3 data must reduce to a Box.mk value"
    );
    assert!(
        def_eq(&env, &upd_data, &box_mk(one)),
        "upd p3 data must be Box.mk 1 (index consistent with preserved tag), got {:?}",
        TypeChecker::new(&env).whnf(&upd_data).kind()
    );
}

// ===========================================================================
// Diagnostic: surface (don't panic) whether each imported-structure operation
// reaches the kernel at all, pinning the failure mode with a clear message so a
// regression on the no-field-table dependent-field path is caught explicitly.
// ===========================================================================

#[test]
fn test_imported_dpair_dependent_operations_elaborate_at_all() {
    let mut env = imported_env();
    let result = try_elaborate_decls_into(
        &mut env,
        "def one : Nat := Nat.succ Nat.zero\n\
         def lit : DPair := { tag := one, data := Box.mk one }\n\
         def proj (s : DPair) : Box (DPair.tag s) := s.data\n\
         def upd (s : DPair) : DPair := { s with data := Box.mk s.tag }",
    );
    assert!(
        result.is_ok(),
        "dependent-field construction / projection / update on an imported \
         structure should elaborate + kernel-check, got: {result:?}"
    );
}

// ===========================================================================
// Control: the NATIVE path (a registered field table lowers `.data` to a kernel
// `Proj`) constructs / projects / updates the dependent field correctly too.
// This isolates any regression to the import-only struct-literal / dot-notation
// lowering rather than to kernel projection reduction.
// ===========================================================================

#[test]
fn test_native_dpair_dependent_field_reduces_correctly() {
    let mut env = native_env();

    assert!(
        env.get_structure_field_names(&Name::from_string("DPair"))
            .is_some(),
        "native DPair should register a structure_fields table"
    );

    elaborate_decls_into(
        &mut env,
        "def one : Nat := Nat.succ Nat.zero\n\
         def pn : DPair := { tag := one, data := Box.mk one }\n\
         def getDataN (s : DPair) : Box (DPair.tag s) := s.data\n\
         def updN (s : DPair) : DPair := { s with data := Box.mk s.tag }",
    );

    // Native `.data` lowers to a kernel `Proj`, not the projection function.
    let get_data_n = env
        .get_const(&Name::from_string("getDataN"))
        .and_then(|i| i.value.clone())
        .expect("getDataN body");
    assert!(
        !get_data_n
            .collect_constants()
            .contains(&Name::from_string("DPair.data")),
        "native getDataN should lower s.data to a kernel Proj, not the DPair.data function"
    );

    // Construction reduces with the correct, distinct field values.
    let data = Expr::proj(Name::from_string("DPair"), 1, const_("pn"));
    assert_eq!(
        whnf_head_const(&env, &data).as_deref(),
        Some("Box.mk"),
        "native pn.data must reduce to Box.mk"
    );
    let one = succ(const_("Nat.zero"));
    assert!(
        def_eq(&env, &data, &box_mk(one.clone())),
        "native pn.data must be Box.mk 1"
    );

    // Dependent projection reduces correctly.
    let get_data_app = Expr::app(const_("getDataN"), const_("pn"));
    assert!(
        def_eq(&env, &get_data_app, &box_mk(one.clone())),
        "native getDataN pn must be Box.mk 1"
    );

    // Update preserves tag and replaces data, keeping the dependency.
    let upd_pn = Expr::app(const_("updN"), const_("pn"));
    let upd_tag = Expr::proj(Name::from_string("DPair"), 0, upd_pn.clone());
    assert!(
        def_eq(&env, &upd_tag, &one),
        "native updN pn must preserve tag = 1"
    );
    let upd_data = Expr::proj(Name::from_string("DPair"), 1, upd_pn);
    assert!(
        def_eq(&env, &upd_data, &box_mk(one)),
        "native updN pn data must be Box.mk 1"
    );
}
