// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: a CHAINED dot-notation projection `p.x.y` through *imported*
//! nested structures.
//!
//! ## The Lean `.olean` shape (what a real import ships)
//!
//! A real Lean `.olean` for a structure ships the projection *functions* plus a
//! definitional `T.casesOn`, and registers **none** of the clean-side metadata —
//! in particular **no** `structure_fields` table. With no field table,
//! `Environment::get_structure_field_names` is `None`, so clean-elab's
//! projection elaboration (`infer/elab_proj.rs`) declines the kernel-`Proj`
//! path (`resolve_projection_target` returns `InvalidProjectionTarget`) and
//! routes `s.field` through the dot-notation fallback, resolving it to the
//! imported projection function `T.field` applied to `s` via
//! `apply_dot_receiver` (the B44/B47 imported-projection path).
//!
//! ## What this scenario exercises
//!
//! Two nested imported structures:
//!   * `Inner` with field `iv : Nat` — projection fn `Inner.iv`,
//!   * `Outer` with fields `inner : Inner` and `ov : Nat` — projection fns
//!     `Outer.inner` and `Outer.ov`,
//!   * (for the 3-level chain) `Wrap` with field `outer : Outer` — `Wrap.outer`.
//!
//! and a `def` using a CHAIN:
//!   * `def get (o : Outer) : Nat := o.inner.iv` — two projection steps where the
//!     *first* (`o.inner`) yields an imported-struct value (`Inner`) and the
//!     *second* (`.iv`) projects a field from it.
//!   * `def get3 (w : Wrap) : Nat := w.outer.inner.iv` — three steps.
//!
//! The likely bug class (B44/B47 fixed *single* imported projections): the
//! SECOND projection in the chain receives an already-projected imported value
//! (`Outer.inner o : Inner`, an `App`, not a bare local) and must re-resolve the
//! field against the *inner* type (`Inner`), not the outer one (`Outer`), and
//! must place the receiver in the correct slot. A mis-step would either
//! type-fail or — worse — silently project the wrong field.
//!
//! ## Synthesize-as-import
//!
//! No shipped `Inner`/`Outer` `.olean` fixture exists, so we build the kernel
//! declarations by hand in a fresh environment and register **only** the
//! inductives and Lean's projection *functions* — never a `structure_fields`
//! table and never `register_structure_fields`. We assert the precondition (no
//! field table on any struct) explicitly so the test stays honest if the
//! importer ever starts shipping one. Distinct `Nat` values pin every slot so a
//! wrong step / field is observable rather than masked.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::{
    BinderInfo, Constructor, Declaration, Expr, InductiveDecl, InductiveType, Name, TypeChecker,
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

/// Definitional equality (results normalize to a kernel `Nat` literal rather
/// than a `Const`-headed term, so a head-name comparison would not suffice).
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

/// Build the imported nested-structure environment by hand, in the exact shape a
/// real Lean `.olean` ships:
///   * monomorphic single-constructor inductives `Inner`, `Outer`, `Wrap : Type`,
///   * Lean's projection *functions* for every field (kernel `Proj` bodies),
///   * **no** `structure_fields` table for any structure.
fn imported_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");

    let ty = Expr::type_();
    let inner = const_("Inner");
    let outer = const_("Outer");
    let wrap = const_("Wrap");
    let nat = const_("Nat");

    // ---- Inner : Type, Inner.mk (iv : Nat) : Inner ----
    let inner_mk_type = Expr::pi(BinderInfo::Default, nat.clone(), inner.clone());
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Inner"),
            type_: ty.clone(),
            constructors: vec![Constructor {
                name: Name::from_string("Inner.mk"),
                type_: inner_mk_type,
            }],
        }],
    })
    .expect("add Inner inductive");

    // Inner.iv : Inner → Nat := fun s => Proj(Inner, 0, s)
    env.add_decl(Declaration::Definition {
        name: Name::from_string("Inner.iv"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, inner.clone(), nat.clone()),
        value: Expr::lam(
            BinderInfo::Default,
            inner.clone(),
            Expr::proj(Name::from_string("Inner"), 0, Expr::bvar(0)),
        ),
        is_reducible: true,
    })
    .expect("add Inner.iv");

    // ---- Outer : Type, Outer.mk (inner : Inner) (ov : Nat) : Outer ----
    let outer_mk_type = Expr::pi(
        BinderInfo::Default,
        inner.clone(),
        Expr::pi(BinderInfo::Default, nat.clone(), outer.clone()),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Outer"),
            type_: ty.clone(),
            constructors: vec![Constructor {
                name: Name::from_string("Outer.mk"),
                type_: outer_mk_type,
            }],
        }],
    })
    .expect("add Outer inductive");

    // Outer.inner : Outer → Inner := fun s => Proj(Outer, 0, s)
    env.add_decl(Declaration::Definition {
        name: Name::from_string("Outer.inner"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, outer.clone(), inner.clone()),
        value: Expr::lam(
            BinderInfo::Default,
            outer.clone(),
            Expr::proj(Name::from_string("Outer"), 0, Expr::bvar(0)),
        ),
        is_reducible: true,
    })
    .expect("add Outer.inner");

    // Outer.ov : Outer → Nat := fun s => Proj(Outer, 1, s)
    env.add_decl(Declaration::Definition {
        name: Name::from_string("Outer.ov"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, outer.clone(), nat.clone()),
        value: Expr::lam(
            BinderInfo::Default,
            outer.clone(),
            Expr::proj(Name::from_string("Outer"), 1, Expr::bvar(0)),
        ),
        is_reducible: true,
    })
    .expect("add Outer.ov");

    // ---- Wrap : Type, Wrap.mk (outer : Outer) : Wrap ----
    let wrap_mk_type = Expr::pi(BinderInfo::Default, outer.clone(), wrap.clone());
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Wrap"),
            type_: ty.clone(),
            constructors: vec![Constructor {
                name: Name::from_string("Wrap.mk"),
                type_: wrap_mk_type,
            }],
        }],
    })
    .expect("add Wrap inductive");

    // Wrap.outer : Wrap → Outer := fun s => Proj(Wrap, 0, s)
    env.add_decl(Declaration::Definition {
        name: Name::from_string("Wrap.outer"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, wrap.clone(), outer.clone()),
        value: Expr::lam(
            BinderInfo::Default,
            wrap.clone(),
            Expr::proj(Name::from_string("Wrap"), 0, Expr::bvar(0)),
        ),
        is_reducible: true,
    })
    .expect("add Wrap.outer");

    env
}

/// `Inner.mk iv` — a concrete inner with a distinct field value.
fn inner_value(iv: u32) -> Expr {
    Expr::app(const_("Inner.mk"), nat_lit(iv))
}

/// `Outer.mk (Inner.mk iv) ov` — a concrete outer with distinct field values.
fn outer_value(iv: u32, ov: u32) -> Expr {
    Expr::apps(const_("Outer.mk"), [inner_value(iv), nat_lit(ov)])
}

/// `Wrap.mk (Outer.mk (Inner.mk iv) ov)` — a concrete 3-level value.
fn wrap_value(iv: u32, ov: u32) -> Expr {
    Expr::app(const_("Wrap.mk"), outer_value(iv, ov))
}

// =============================================================================
// Precondition: this is genuinely the imported nested-structure configuration —
// inductives + Lean projection functions present, no clean-side field table on
// ANY of the three structures. This is the exact condition that forces every
// projection step (including the *second* in a chain) to route through the
// dot-notation fallback rather than a kernel `Proj`.
// =============================================================================

#[test]
fn test_imported_nested_structs_have_no_clean_field_table() {
    let env = imported_env();

    for ind in ["Inner", "Outer", "Wrap"] {
        assert!(
            env.get_inductive(&Name::from_string(ind)).is_some(),
            "{ind} inductive should be imported"
        );
        assert!(
            env.get_structure_field_names(&Name::from_string(ind))
                .is_none(),
            "imported {ind} must NOT carry a clean-side structure_fields table — \
             this is the exact import condition that forces chained-projection \
             resolution through Lean's projection functions"
        );
    }

    for proj in ["Inner.iv", "Outer.inner", "Outer.ov", "Wrap.outer"] {
        assert!(
            env.get_const(&Name::from_string(proj)).is_some(),
            "{proj} projection function should be imported"
        );
    }
}

// =============================================================================
// Control: each SINGLE projection step reduces correctly on its own. Isolates a
// chained-specific regression from a single-projection regression.
// =============================================================================

#[test]
fn test_single_imported_projection_steps_reduce_correctly() {
    let mut env = imported_env();

    elaborate_decls_into(
        &mut env,
        "def getInnerIv (i : Inner) : Nat := i.iv\n\
         def getOuterInnerIv (i : Inner) : Nat := i.iv\n\
         def getOuterOv (o : Outer) : Nat := o.ov",
    );

    // i.iv on a bare Inner = 9.
    let i = inner_value(9);
    let iv = Expr::app(const_("getInnerIv"), i);
    assert!(
        def_eq(&env, &iv, &nat_lit(9)),
        "i.iv must reduce to 9, got {:?}",
        TypeChecker::new(&env).whnf(&iv).kind()
    );

    // o.ov on Outer (Inner.mk 4, ov = 6) = 6 — the *second* field of Outer, so a
    // slot/index mix-up at the single-projection level is observable.
    let o = outer_value(4, 6);
    let ov = Expr::app(const_("getOuterOv"), o);
    assert!(
        def_eq(&env, &ov, &nat_lit(6)),
        "o.ov must reduce to 6 (Outer's second field), got {:?}",
        TypeChecker::new(&env).whnf(&ov).kind()
    );
}

// =============================================================================
// The headline probe: a 2-step CHAIN `o.inner.iv` on an imported nested struct.
// The first step yields an imported-struct value (`Outer.inner o : Inner`); the
// second must re-resolve `.iv` against `Inner` (NOT `Outer`) and place the
// receiver correctly. Distinct values pin every step.
// =============================================================================

#[test]
fn test_chained_projection_two_levels_reduces_to_innermost_value() {
    let mut env = imported_env();

    // get o = o.inner.iv. Outer (Inner.mk 7, ov = 3): the chain must read the
    // INNER field (7), distinct from the outer's own field (3) so reading the
    // wrong type's field at the second step is observable.
    elaborate_decls_into(&mut env, "def getChain (o : Outer) : Nat := o.inner.iv");

    // The body must compose the two imported projection functions
    // (`Inner.iv (Outer.inner o)`), proving we are on the import dot-notation
    // path at *both* steps, not a kernel `Proj`.
    let get_chain = env
        .get_const(&Name::from_string("getChain"))
        .expect("getChain registered");
    let body_consts = get_chain
        .value
        .as_ref()
        .expect("getChain has a body")
        .collect_constants();
    assert!(
        body_consts.contains(&Name::from_string("Inner.iv"))
            && body_consts.contains(&Name::from_string("Outer.inner")),
        "o.inner.iv on imported nested structs must compose Inner.iv with \
         Outer.inner (chained dot-notation fallback), got: {body_consts:?}"
    );

    let o = outer_value(7, 3);
    let chain = Expr::app(const_("getChain"), o);
    assert!(
        def_eq(&env, &chain, &nat_lit(7)),
        "o.inner.iv must reduce to the innermost value 7, got {:?}",
        TypeChecker::new(&env).whnf(&chain).kind()
    );
    // Guard against the second projection mis-resolving against `Outer` and
    // reading the outer's own field (3).
    assert!(
        !def_eq(&env, &chain, &nat_lit(3)),
        "o.inner.iv must NOT read the outer's own field (3) — the second \
         projection must re-resolve against Inner, not Outer"
    );
}

// =============================================================================
// Deeper 3-level chain: `w.outer.inner.iv`. Each step yields an imported-struct
// value until the innermost `Nat`. Pins that the chain composes correctly at
// arbitrary depth (not just one extra step).
// =============================================================================

#[test]
fn test_chained_projection_three_levels_reduces_to_innermost_value() {
    let mut env = imported_env();

    elaborate_decls_into(
        &mut env,
        "def getChain3 (w : Wrap) : Nat := w.outer.inner.iv",
    );

    let get_chain3 = env
        .get_const(&Name::from_string("getChain3"))
        .expect("getChain3 registered");
    let body_consts = get_chain3
        .value
        .as_ref()
        .expect("getChain3 has a body")
        .collect_constants();
    assert!(
        body_consts.contains(&Name::from_string("Inner.iv"))
            && body_consts.contains(&Name::from_string("Outer.inner"))
            && body_consts.contains(&Name::from_string("Wrap.outer")),
        "w.outer.inner.iv must compose all three imported projection functions, \
         got: {body_consts:?}"
    );

    // Wrap (Outer (Inner.mk 5, ov = 8)) → w.outer.inner.iv = 5. Distinct from the
    // outer's own field (8) so a wrong step is observable.
    let w = wrap_value(5, 8);
    let chain = Expr::app(const_("getChain3"), w);
    assert!(
        def_eq(&env, &chain, &nat_lit(5)),
        "w.outer.inner.iv must reduce to the innermost value 5, got {:?}",
        TypeChecker::new(&env).whnf(&chain).kind()
    );
    assert!(
        !def_eq(&env, &chain, &nat_lit(8)),
        "w.outer.inner.iv must NOT read an intermediate own field (8)"
    );
}

// =============================================================================
// Mixed chain that ENDS on the intermediate own field: `w.outer.ov`. Confirms
// the chain can stop at a non-deepest field and still pick the correct slot
// (the second field of the intermediate `Outer`, not the inner's field).
// =============================================================================

#[test]
fn test_chained_projection_to_intermediate_own_field() {
    let mut env = imported_env();

    elaborate_decls_into(&mut env, "def getMid (w : Wrap) : Nat := w.outer.ov");

    // Wrap (Outer (Inner.mk 5, ov = 8)) → w.outer.ov = 8 (Outer's own field).
    let w = wrap_value(5, 8);
    let mid = Expr::app(const_("getMid"), w);
    assert!(
        def_eq(&env, &mid, &nat_lit(8)),
        "w.outer.ov must reduce to the intermediate own field 8, got {:?}",
        TypeChecker::new(&env).whnf(&mid).kind()
    );
    assert!(
        !def_eq(&env, &mid, &nat_lit(5)),
        "w.outer.ov must NOT read the inner field (5)"
    );
}

// =============================================================================
// Diagnostic: surface (don't panic) whether the chained projection even reaches
// the kernel. Pins the failure mode with a clear message so a regression on the
// chained dot-notation fallback is caught explicitly.
// =============================================================================

#[test]
fn test_chained_projection_elaborates_at_all() {
    let mut env = imported_env();
    let result = try_elaborate_decls_into(&mut env, "def probe (o : Outer) : Nat := o.inner.iv");
    assert!(
        result.is_ok(),
        "chained projection `o.inner.iv` on imported nested structs should \
         elaborate + kernel-check, got: {result:?}"
    );
}
