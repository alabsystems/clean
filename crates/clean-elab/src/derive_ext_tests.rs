// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended derive handler framework.

use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, ExprKind, InductiveDecl, InductiveType,
    InductiveVal, Level, Name,
};

use crate::derive::{DeriveError, DeriveHandler, DeriveRegistry};
use crate::derive_ext::{
    build_derive_input, derive_beq_ext, derive_decidable_eq_ext, derive_hashable_ext,
    derive_inhabited_ext, derive_ord_ext, derive_repr_ext, register_all_handlers,
    register_ext_handlers, DeriveExtHandlers, DeriveOrd,
};

// ---------------------------------------------------------------------------
// Test environment helpers
// ---------------------------------------------------------------------------

/// Build a simple two-constructor enum (like `data Color := Red | Blue`).
fn make_color_env() -> (Environment, InductiveVal) {
    let mut env = Environment::new();

    let color_name = Name::from_string("Color");
    let red_name = Name::from_string("Color.Red");
    let blue_name = Name::from_string("Color.Blue");

    let color_type = Expr::sort(Level::succ(Level::zero()));

    let ind_type = InductiveType {
        name: color_name.clone(),
        type_: color_type,
        constructors: vec![
            clean_kernel::Constructor {
                name: red_name,
                type_: Expr::const_(color_name.clone(), vec![]),
            },
            clean_kernel::Constructor {
                name: blue_name,
                type_: Expr::const_(color_name.clone(), vec![]),
            },
        ],
    };

    let ind_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![ind_type],
    };

    env.add_inductive(ind_decl)
        .expect("should add Color inductive");

    let ind_val = env
        .get_inductive(&color_name)
        .expect("Color should be in env")
        .clone();

    (env, ind_val)
}

/// Build a single-constructor struct (like `structure Point := (x : Nat) (y : Nat)`).
fn make_point_env() -> (Environment, InductiveVal) {
    let mut env = Environment::new();
    env.init_nat().expect("should init Nat");

    let point_name = Name::from_string("Point");
    let mk_name = Name::from_string("Point.mk");
    let nat = Expr::const_str("Nat");

    let point_type = Expr::sort(Level::succ(Level::zero()));

    // Point.mk : Nat -> Nat -> Point
    let mk_type = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(
            BinderInfo::Default,
            nat,
            Expr::const_(point_name.clone(), vec![]),
        ),
    );

    let ind_type = InductiveType {
        name: point_name.clone(),
        type_: point_type,
        constructors: vec![clean_kernel::Constructor {
            name: mk_name,
            type_: mk_type,
        }],
    };

    let ind_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![ind_type],
    };

    env.add_inductive(ind_decl)
        .expect("should add Point inductive");

    let ind_val = env
        .get_inductive(&point_name)
        .expect("Point should be in env")
        .clone();

    (env, ind_val)
}

/// Build an empty inductive (no constructors).
fn make_empty_env() -> (Environment, InductiveVal) {
    let mut env = Environment::new();
    let empty_name = Name::from_string("Empty");

    let ind_type = InductiveType {
        name: empty_name.clone(),
        type_: Expr::sort(Level::succ(Level::zero())),
        constructors: vec![],
    };

    let ind_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![ind_type],
    };

    env.add_inductive(ind_decl)
        .expect("should add Empty inductive");

    let ind_val = env
        .get_inductive(&empty_name)
        .expect("Empty should be in env")
        .clone();

    (env, ind_val)
}

fn assert_unsupported<T: std::fmt::Debug>(result: Result<T, DeriveError>, class_name: &str) {
    match result {
        Err(DeriveError::Unsupported {
            class_name: got, ..
        }) => assert_eq!(got, class_name),
        other => panic!("expected Unsupported for {class_name}, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// DeriveExtHandlers registry tests
// ---------------------------------------------------------------------------

#[test]
fn test_ext_handlers_register_and_lookup() {
    let mut registry = DeriveExtHandlers::new();
    register_ext_handlers(&mut registry);

    assert!(registry.has_handler("BEq"));
    assert!(registry.has_handler("Hashable"));
    assert!(registry.has_handler("Repr"));
    assert!(registry.has_handler("Inhabited"));
    assert!(registry.has_handler("DecidableEq"));
    assert!(registry.has_handler("Ord"));
    assert!(!registry.has_handler("Functor"));
}

#[test]
fn test_ext_handlers_registered_classes_count() {
    let mut registry = DeriveExtHandlers::new();
    register_ext_handlers(&mut registry);

    assert_eq!(registry.registered_classes().len(), 6);
}

#[test]
fn test_ext_handlers_get_returns_handler() {
    let mut registry = DeriveExtHandlers::new();
    register_ext_handlers(&mut registry);

    assert!(registry.get("BEq").is_some());
    assert!(registry.get("Ord").is_some());
    assert!(registry.get("Unknown").is_none());
}

// ---------------------------------------------------------------------------
// DeriveOrd trait-based handler tests
// ---------------------------------------------------------------------------

#[test]
fn test_derive_ord_enum_fails_closed() {
    let (env, ind) = make_color_env();
    let handler = DeriveOrd;

    assert_unsupported(handler.derive(&ind, &env), "Ord");
}

#[test]
fn test_derive_ord_struct_fails_closed() {
    let (env, ind) = make_point_env();
    let handler = DeriveOrd;

    assert_unsupported(handler.derive(&ind, &env), "Ord");
}

#[test]
fn test_derive_ord_reflexive_rejected() {
    let ind = InductiveVal {
        name: Name::from_string("Tree"),
        level_params: vec![],
        type_: Expr::sort(Level::succ(Level::zero())),
        num_params: 0,
        num_indices: 0,
        all_names: vec![Name::from_string("Tree")],
        constructor_names: vec![],
        is_recursive: true,
        is_reflexive: true,
        is_large_elim: false,
        is_nested: false,
    };

    let env = Environment::new();
    let handler = DeriveOrd;

    let result = handler.derive(&ind, &env);
    assert!(result.is_err());
    match result.unwrap_err() {
        DeriveError::Unsupported {
            class_name, reason, ..
        } => {
            assert_eq!(class_name, "Ord");
            assert!(reason.contains("reflexive"));
        }
        other => panic!("expected Unsupported, got {other:?}"),
    }
}

#[test]
fn test_derive_ord_declaration_shape() {
    let (env, ind) = make_empty_env();
    let handler = DeriveOrd;

    let decls = handler.derive(&ind, &env).unwrap();
    match &decls[0] {
        Declaration::Definition {
            name,
            level_params,
            is_reducible,
            value,
            ..
        } => {
            assert_eq!(name.to_string(), "instOrdEmpty");
            assert!(level_params.is_empty());
            assert!(is_reducible);
            // Ord.mk wraps a lambda, so the value should be an application.
            assert!(
                matches!(value.kind(), ExprKind::App(..)),
                "Ord value should be an application (Ord.mk <lam>)"
            );
        }
        other => panic!("expected Definition, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// build_derive_input tests
// ---------------------------------------------------------------------------

#[test]
fn test_build_derive_input_color_enum() {
    let (env, ind) = make_color_env();
    let input = build_derive_input(&ind, &env).expect("should build input");

    assert_eq!(input.type_name, "Color");
    assert_eq!(input.constructors.len(), 2);
    assert_eq!(input.constructors[0].name, "Color.Red");
    assert_eq!(input.constructors[1].name, "Color.Blue");
    // Enum constructors with no fields
    assert!(input.constructors[0].fields.is_empty());
    assert!(input.constructors[1].fields.is_empty());
}

#[test]
fn test_build_derive_input_point_struct() {
    let (env, ind) = make_point_env();
    let input = build_derive_input(&ind, &env).expect("should build input");

    assert_eq!(input.type_name, "Point");
    assert_eq!(input.constructors.len(), 1);
    assert_eq!(input.constructors[0].name, "Point.mk");
    assert_eq!(input.constructors[0].fields.len(), 2);
}

#[test]
fn test_build_derive_input_empty_type() {
    let (env, ind) = make_empty_env();
    let input = build_derive_input(&ind, &env).expect("should build input");

    assert_eq!(input.type_name, "Empty");
    assert!(input.constructors.is_empty());
    assert!(input.fields.is_empty());
}

// ---------------------------------------------------------------------------
// Standalone function-pointer handler tests
// ---------------------------------------------------------------------------

#[test]
fn test_derive_beq_ext_empty_type_produces_output() {
    let (env, ind) = make_empty_env();
    let input = build_derive_input(&ind, &env).unwrap();

    let output = derive_beq_ext(&input, &env).expect("BEq ext should succeed");
    assert!(output.instance_name.contains("BEq"));
    assert!(output.instance_name.contains("Empty"));
}

#[test]
fn test_derive_hashable_ext_fails_closed() {
    let (env, ind) = make_color_env();
    let input = build_derive_input(&ind, &env).unwrap();

    assert_unsupported(derive_hashable_ext(&input, &env), "Hashable");
}

#[test]
fn test_derive_repr_ext_fails_closed() {
    let (env, ind) = make_color_env();
    let input = build_derive_input(&ind, &env).unwrap();

    assert_unsupported(derive_repr_ext(&input, &env), "Repr");
}

#[test]
fn test_derive_inhabited_ext_produces_output() {
    let (env, ind) = make_color_env();
    let input = build_derive_input(&ind, &env).unwrap();

    let output = derive_inhabited_ext(&input, &env).expect("Inhabited ext should succeed");
    assert!(output.instance_name.contains("Inhabited"));
    assert!(output.instance_name.contains("Color"));
}

#[test]
fn test_derive_inhabited_ext_no_constructors_error() {
    let (env, ind) = make_empty_env();
    let input = build_derive_input(&ind, &env).unwrap();

    let result = derive_inhabited_ext(&input, &env);
    assert!(result.is_err());
    match result.unwrap_err() {
        DeriveError::Unsupported {
            class_name, reason, ..
        } => {
            assert_eq!(class_name, "Inhabited");
            assert!(reason.contains("no constructors"));
        }
        other => panic!("expected Unsupported, got {other:?}"),
    }
}

#[test]
fn test_derive_decidable_eq_ext_fails_closed() {
    let (env, ind) = make_color_env();
    let input = build_derive_input(&ind, &env).unwrap();

    assert_unsupported(derive_decidable_eq_ext(&input, &env), "DecidableEq");
}

#[test]
fn test_derive_ord_ext_empty_type_produces_output() {
    let (env, ind) = make_empty_env();
    let input = build_derive_input(&ind, &env).unwrap();

    let output = derive_ord_ext(&input, &env).expect("Ord ext should succeed");
    assert!(output.instance_name.contains("Ord"));
    assert!(output.instance_name.contains("Empty"));
}

#[test]
fn test_derive_ord_ext_struct_fails_closed() {
    let (env, ind) = make_point_env();
    let input = build_derive_input(&ind, &env).unwrap();

    assert_unsupported(derive_ord_ext(&input, &env), "Ord");
}

// ---------------------------------------------------------------------------
// register_all_handlers integration test
// ---------------------------------------------------------------------------

#[test]
fn test_register_all_handlers_includes_ord() {
    let mut registry = DeriveRegistry::new();
    register_all_handlers(&mut registry);

    // Original 5 + Ord + Nonempty + SizeOf + Fintype + ToExpr + OfScientific = 11
    assert!(registry.has_handler("BEq"));
    assert!(registry.has_handler("Repr"));
    assert!(registry.has_handler("Hashable"));
    assert!(registry.has_handler("Inhabited"));
    assert!(registry.has_handler("DecidableEq"));
    assert!(registry.has_handler("Ord"));
    assert_eq!(registry.registered_classes().len(), 11);
}

#[test]
fn test_register_all_handlers_includes_nonempty_and_sizeof() {
    let mut registry = DeriveRegistry::new();
    register_all_handlers(&mut registry);

    // Previously implemented (in alternate registries) but unregistered in the
    // canonical dispatch. Wiring them is the fix under test.
    assert!(
        registry.has_handler("Nonempty"),
        "Nonempty must be wired into register_all_handlers"
    );
    assert!(
        registry.has_handler("SizeOf"),
        "SizeOf must be wired into register_all_handlers"
    );
}

/// Soundness guard: `Countable` is a *proof-obligation* derive class
/// (injection-to-`Nat`) whose only implementation lives in the
/// `ExtDeriveHandler2` family and unconditionally emits a `@sorryAx _ false`
/// instance body (see `derive_handlers_ext.rs`) — it has no genuine
/// proof-producing path. Wiring it into the canonical `DeriveRegistry` (even
/// through the sorry-rejecting adapter) would yield a handler that *always*
/// errors, providing no derivation value, so it is deliberately left UNWIRED
/// until a real proof path exists. This test pins that decision: if a future
/// change wires it, this assertion fails and forces a soundness review.
///
/// (`Fintype`, `ToExpr` and `OfScientific` ARE wired — via
/// `ExtDeriveHandler2Adapter`, which converts any residual `sorry` body into a
/// hard `DeriveError` before registration, so only genuine sorry-free instances
/// ever reach the kernel. `Fintype` gained a real `Finset` + completeness-proof
/// construction for the nullary-enum shape; see `fintype_nullary_enum_value`.)
#[test]
fn test_register_all_handlers_excludes_proof_obligation_candidates() {
    let mut registry = DeriveRegistry::new();
    register_all_handlers(&mut registry);

    assert!(
        !registry.has_handler("Countable"),
        "`Countable` must NOT be wired into register_all_handlers: it is a proof \
         obligation whose only implementation emits a sorryAx-backed instance \
         with no genuine proof path. Add a real proof-producing path before \
         wiring."
    );
    // `Fintype` IS now wired: it has a genuine, sorry-free nullary-enum path.
    assert!(
        registry.has_handler("Fintype"),
        "`Fintype` should be wired: it now produces a genuine, kernel-checkable \
         instance for the nullary-enum shape and errors (no sorry) otherwise."
    );
}

/// Pin the exact roster of canonical derive handlers wired into the main
/// dispatch. Wiring a new handler must be a deliberate, reviewed change that
/// also updates this list (and adds a sorry-free / errors-on-unsupported
/// derivation test), guarding against accidental registration of an unsound
/// handler.
///
/// `ToExpr` and `OfScientific` are wired through the sorry-rejecting
/// `ExtDeriveHandler2Adapter`: accepted shapes produce kernel-checked, sorry-free
/// instances and every other shape errors (it never registers a sorry body).
#[test]
fn test_register_all_handlers_roster_is_exactly_the_sound_eleven() {
    let mut registry = DeriveRegistry::new();
    register_all_handlers(&mut registry);

    let mut classes = registry.registered_classes();
    classes.sort_unstable();
    assert_eq!(
        classes,
        vec![
            "BEq",
            "DecidableEq",
            "Fintype",
            "Hashable",
            "Inhabited",
            "Nonempty",
            "OfScientific",
            "Ord",
            "Repr",
            "SizeOf",
            "ToExpr",
        ],
        "canonical derive dispatch roster changed; ensure any added handler is \
         sorry-free-or-errors and kernel-checkable before updating this list"
    );
}

#[test]
fn test_ext_handlers_on_enum_fail_closed_except_inhabited() {
    let (env, ind) = make_color_env();
    let input = build_derive_input(&ind, &env).unwrap();

    let mut registry = DeriveExtHandlers::new();
    register_ext_handlers(&mut registry);

    for class in &["BEq", "Hashable", "Repr", "DecidableEq", "Ord"] {
        let handler = registry
            .get(class)
            .unwrap_or_else(|| panic!("{class} handler should be registered"));
        assert_unsupported(handler(&input, &env), class);
    }

    let output = registry
        .get("Inhabited")
        .expect("Inhabited handler should be registered")(&input, &env)
    .expect("Inhabited should derive from a nullary constructor");
    assert!(output.instance_name.contains("Inhabited"));
}

#[test]
fn test_derive_beq_ext_struct_with_fields_fails_closed() {
    let (env, ind) = make_point_env();
    let input = build_derive_input(&ind, &env).unwrap();

    assert_unsupported(derive_beq_ext(&input, &env), "BEq");
}

#[test]
fn test_derive_inhabited_ext_struct_with_fields_fails_closed() {
    let (env, ind) = make_point_env();
    let input = build_derive_input(&ind, &env).unwrap();

    assert_unsupported(derive_inhabited_ext(&input, &env), "Inhabited");
}
