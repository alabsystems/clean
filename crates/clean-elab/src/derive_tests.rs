// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the derive handler framework.

use clean_kernel::{
    BinderInfo, ConstantInfo, ConstantKind, Declaration, Environment, Expr, ExprKind, FVarId,
    InductiveDecl, InductiveType, InductiveVal, Level, Name,
};

use crate::derive::{DeriveError, DeriveHandler, DeriveRegistry};
use crate::derive_handlers::{
    register_builtin_handlers, DeriveBEq, DeriveDecidableEq, DeriveHashable, DeriveInhabited,
    DeriveNonempty, DeriveRepr, DeriveSizeOf,
};
use crate::infer::{DerivedInstance, ElabResult};

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
    // Nat must be in the environment for Point.mk's type to type-check.
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

/// Build a parametric single-field structure with Hashable available:
/// `structure Box (α : Type) where value : α`.
fn make_parametric_box_env_with_hashable() -> (Environment, InductiveVal) {
    let mut env = Environment::new();
    env.init_nat().expect("should init Nat");

    let type0 = Expr::sort(Level::succ(Level::zero()));
    let nat = Expr::const_str("Nat");

    let hashable_name = Name::from_string("Hashable");
    let hashable_mk_name = Name::from_string("Hashable.mk");
    let hashable_type = Expr::pi(BinderInfo::Implicit, type0.clone(), type0.clone());
    let hashable_mk_type = Expr::pi(
        BinderInfo::Implicit,
        type0.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::pi(BinderInfo::Default, Expr::bvar(0), nat),
            Expr::app(Expr::const_(hashable_name.clone(), vec![]), Expr::bvar(1)),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: hashable_name,
            type_: hashable_type,
            constructors: vec![clean_kernel::Constructor {
                name: hashable_mk_name,
                type_: hashable_mk_type,
            }],
        }],
    })
    .expect("should add Hashable inductive");

    let box_name = Name::from_string("Box");
    let box_mk_name = Name::from_string("Box.mk");
    let box_type = Expr::pi(BinderInfo::Implicit, type0.clone(), type0.clone());
    let box_mk_type = Expr::pi(
        BinderInfo::Implicit,
        type0.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::app(Expr::const_(box_name.clone(), vec![]), Expr::bvar(1)),
        ),
    );

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: box_name.clone(),
            type_: box_type,
            constructors: vec![clean_kernel::Constructor {
                name: box_mk_name,
                type_: box_mk_type,
            }],
        }],
    })
    .expect("should add Box inductive");

    let ind_val = env
        .get_inductive(&box_name)
        .expect("Box should be in env")
        .clone();

    (env, ind_val)
}

fn expr_any(expr: &Expr, pred: &impl Fn(&Expr) -> bool) -> bool {
    if pred(expr) {
        return true;
    }
    match expr.kind() {
        ExprKind::App(f, a) => expr_any(f, pred) || expr_any(a, pred),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_any(ty, pred) || expr_any(body, pred)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_any(ty, pred) || expr_any(val, pred) || expr_any(body, pred)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            expr_any(inner, pred)
        }
        ExprKind::CubicalPath { ty, left, right } => {
            expr_any(ty, pred) || expr_any(left, pred) || expr_any(right, pred)
        }
        ExprKind::CubicalPathLam { body } => expr_any(body, pred),
        ExprKind::CubicalPathApp { path, arg } => expr_any(path, pred) || expr_any(arg, pred),
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            expr_any(ty, pred) || expr_any(phi, pred) || expr_any(u, pred) || expr_any(base, pred)
        }
        ExprKind::CubicalTransp { ty, phi, base } => {
            expr_any(ty, pred) || expr_any(phi, pred) || expr_any(base, pred)
        }
        ExprKind::ZFCMem { element, set } => expr_any(element, pred) || expr_any(set, pred),
        ExprKind::ZFCComprehension { domain, pred: p } => {
            expr_any(domain, pred) || expr_any(p, pred)
        }
        _ => false,
    }
}

fn expr_contains_const(expr: &Expr, needle: &str) -> bool {
    expr_any(
        expr,
        &|subexpr| matches!(subexpr.kind(), ExprKind::Const(name, _) if name.to_string() == needle),
    )
}

fn expr_contains_sorry_const(expr: &Expr) -> bool {
    expr_contains_const(expr, "sorry") || expr_contains_const(expr, "sorryAx")
}

#[derive(Clone)]
struct FixedDeclarationsHandler {
    declarations: Vec<Declaration>,
}

impl DeriveHandler for FixedDeclarationsHandler {
    fn derive(
        &self,
        _ind: &InductiveVal,
        _env: &Environment,
    ) -> Result<Vec<Declaration>, DeriveError> {
        Ok(self.declarations.clone())
    }

    fn class_name(&self) -> &str {
        "Audit"
    }
}

fn audit_definition(name: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    }
}

fn assert_admission_error(error: DeriveError, expected_detail: &str) {
    match error {
        DeriveError::Unsupported {
            class_name,
            ind_name,
            reason,
        } => {
            assert_eq!(class_name, "Audit");
            assert_eq!(ind_name, "Color");
            assert!(
                reason.contains("automatic deriving admission rejected"),
                "error should identify the derive trust boundary: {reason}"
            );
            assert!(
                reason.contains(expected_detail),
                "error should identify `{expected_detail}`: {reason}"
            );
        }
        other => panic!("expected typed admission error, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Registry tests
// ---------------------------------------------------------------------------

#[test]
fn test_derive_registry_empty_has_no_handlers() {
    let registry = DeriveRegistry::new();
    assert!(!registry.has_handler("BEq"));
    assert!(!registry.has_handler("Repr"));
}

#[test]
fn test_derive_registry_register_and_lookup() {
    let mut registry = DeriveRegistry::new();
    register_builtin_handlers(&mut registry);

    assert!(registry.has_handler("BEq"));
    assert!(registry.has_handler("Repr"));
    assert!(registry.has_handler("Hashable"));
    assert!(registry.has_handler("Inhabited"));
    assert!(registry.has_handler("DecidableEq"));
    assert!(!registry.has_handler("Functor"));
}

#[test]
fn test_derive_registry_registered_classes() {
    let mut registry = DeriveRegistry::new();
    register_builtin_handlers(&mut registry);

    let classes = registry.registered_classes();
    assert_eq!(classes.len(), 5);
    assert!(classes.contains(&"BEq"));
    assert!(classes.contains(&"Repr"));
    assert!(classes.contains(&"Hashable"));
    assert!(classes.contains(&"Inhabited"));
    assert!(classes.contains(&"DecidableEq"));
}

#[test]
fn test_derive_registry_no_handler_error() {
    let registry = DeriveRegistry::new();
    let (mut env, ind) = make_color_env();

    let result = registry.run_derive("Functor", &ind, &mut env);
    assert!(result.is_err());
    match result.unwrap_err() {
        DeriveError::NoHandler(name) => assert_eq!(name, "Functor"),
        other => panic!("expected NoHandler, got {other:?}"),
    }
}

#[test]
fn test_run_derive_admission_rejects_trust_and_open_terms_without_mutation() {
    let cases = [
        (
            "auditSorry",
            Expr::type_(),
            Expr::const_str("sorryAx"),
            "sorry",
        ),
        (
            "auditTrusted",
            Expr::type_(),
            // Metadata must not hide a namespaced trusted primitive from the
            // exact constant traversal.
            Expr::mdata(vec![], Expr::const_str("Internal.trustedAy")),
            "trusted primitive",
        ),
        (
            "auditFree",
            Expr::type_(),
            Expr::fvar(FVarId::new(7)),
            "free variable",
        ),
        (
            "auditLooseType",
            Expr::bvar(0),
            Expr::type_(),
            "loose bound variable",
        ),
    ];

    for (name, type_, value, detail) in cases {
        let (mut env, ind) = make_color_env();
        let mut registry = DeriveRegistry::new();
        registry.register_handler(
            "Audit",
            Box::new(FixedDeclarationsHandler {
                declarations: vec![audit_definition(name, type_, value)],
            }),
        );

        let error = registry
            .run_derive("Audit", &ind, &mut env)
            .expect_err("forbidden generated term must fail closed");
        assert_admission_error(error, detail);
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "rejected generated declaration `{name}` must not mutate the environment"
        );
    }
}

#[test]
fn test_run_derive_admission_validates_batch_transactionally() {
    let first_name = Name::from_string("auditBatchFirst");
    let forbidden_name = Name::from_string("auditBatchForbidden");
    let (mut env, ind) = make_color_env();
    let mut registry = DeriveRegistry::new();
    registry.register_handler(
        "Audit",
        Box::new(FixedDeclarationsHandler {
            declarations: vec![
                audit_definition(&first_name.to_string(), Expr::type_(), Expr::type_()),
                audit_definition(
                    &forbidden_name.to_string(),
                    Expr::type_(),
                    Expr::const_str("trustedArith"),
                ),
            ],
        }),
    );

    let error = registry
        .run_derive("Audit", &ind, &mut env)
        .expect_err("a forbidden later declaration must reject the entire batch");
    assert_admission_error(error, "trusted primitive");
    assert!(env.get_const(&first_name).is_none());
    assert!(env.get_const(&forbidden_name).is_none());
}

#[test]
fn test_run_derive_admission_rejects_non_definition_declaration() {
    let rejected_name = Name::from_string("auditAxiom");
    let (mut env, ind) = make_color_env();
    let mut registry = DeriveRegistry::new();
    registry.register_handler(
        "Audit",
        Box::new(FixedDeclarationsHandler {
            declarations: vec![Declaration::Axiom {
                name: rejected_name.clone(),
                level_params: vec![],
                type_: Expr::prop(),
            }],
        }),
    );

    let error = registry
        .run_derive("Audit", &ind, &mut env)
        .expect_err("automatic deriving must not register axioms");
    assert_admission_error(error, "non-definition");
    assert!(env.get_const(&rejected_name).is_none());
}

#[test]
fn test_run_derive_admission_rejects_transitive_axiom_bridge() {
    let (mut env, ind) = make_color_env();
    let axiom = Name::from_string("Audit.secret");
    let bridge = Name::from_string("Audit.bridge");
    env.add_decl(Declaration::Axiom {
        name: axiom.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("test axiom should register");
    env.add_decl(audit_definition(
        &bridge.to_string(),
        Expr::prop(),
        Expr::const_(axiom.clone(), vec![]),
    ))
    .expect("axiom bridge should be a well-typed definition");

    let derived = Name::from_string("auditTransitiveAxiom");
    let mut registry = DeriveRegistry::new();
    registry.register_handler(
        "Audit",
        Box::new(FixedDeclarationsHandler {
            declarations: vec![audit_definition(
                &derived.to_string(),
                Expr::prop(),
                Expr::const_(bridge, vec![]),
            )],
        }),
    );

    let error = registry
        .run_derive("Audit", &ind, &mut env)
        .expect_err("a definition alias must not hide a transitive axiom dependency");
    assert_admission_error(error, "dependency closure");
    assert!(env.get_const(&derived).is_none());
    assert!(
        env.get_const(&axiom).is_some(),
        "pre-existing state is preserved"
    );
}

#[test]
fn test_run_derive_admission_rejects_transitively_elided_proof_body() {
    let (mut env, ind) = make_color_env();
    let hidden = Name::from_string("Audit.hiddenProof");
    let bridge = Name::from_string("Audit.elidedBridge");

    let mut hidden_info = ConstantInfo::new(hidden.clone(), vec![], Expr::prop(), None, false);
    hidden_info.kind = ConstantKind::Theorem;
    env.add_constant_unchecked_for_test(hidden_info);
    env.add_constant_unchecked_for_test(ConstantInfo::new(
        bridge.clone(),
        vec![],
        Expr::prop(),
        Some(Expr::const_(hidden.clone(), vec![])),
        true,
    ));

    let derived = Name::from_string("auditTransitiveElidedProof");
    let mut registry = DeriveRegistry::new();
    registry.register_handler(
        "Audit",
        Box::new(FixedDeclarationsHandler {
            declarations: vec![audit_definition(
                &derived.to_string(),
                Expr::prop(),
                Expr::const_(bridge, vec![]),
            )],
        }),
    );

    let error = registry
        .run_derive("Audit", &ind, &mut env)
        .expect_err("an intermediary must not hide an elided proof body");
    assert_admission_error(error.clone(), "elided body");
    assert_admission_error(error, &hidden.to_string());
    assert!(env.get_const(&derived).is_none());
}

#[test]
fn test_run_derive_admission_rejects_transitive_trusted_definition() {
    let (mut env, ind) = make_color_env();
    let trusted = Name::from_string("Audit.trustedHidden");
    let bridge = Name::from_string("Audit.authorityAlias");
    env.add_constant_unchecked_for_test(ConstantInfo::new(
        trusted.clone(),
        vec![],
        Expr::prop(),
        Some(Expr::prop()),
        true,
    ));
    env.add_constant_unchecked_for_test(ConstantInfo::new(
        bridge.clone(),
        vec![],
        Expr::prop(),
        Some(Expr::const_(trusted.clone(), vec![])),
        true,
    ));

    let derived = Name::from_string("auditTransitiveTrusted");
    let mut registry = DeriveRegistry::new();
    registry.register_handler(
        "Audit",
        Box::new(FixedDeclarationsHandler {
            declarations: vec![audit_definition(
                &derived.to_string(),
                Expr::prop(),
                Expr::const_(bridge, vec![]),
            )],
        }),
    );

    let error = registry
        .run_derive("Audit", &ind, &mut env)
        .expect_err("an intermediary must not hide a trusted definition");
    assert_admission_error(error.clone(), "trusted primitive");
    assert_admission_error(error, &trusted.to_string());
    assert!(env.get_const(&derived).is_none());
}

#[test]
fn test_run_derive_kernel_failure_rolls_back_earlier_batch_members() {
    let (mut env, ind) = make_color_env();
    let good = Name::from_string("auditKernelBatchGood");
    let bad = Name::from_string("auditKernelBatchBad");
    let color = Expr::const_str("Color");
    let mut registry = DeriveRegistry::new();
    registry.register_handler(
        "Audit",
        Box::new(FixedDeclarationsHandler {
            declarations: vec![
                audit_definition(
                    &good.to_string(),
                    color.clone(),
                    Expr::const_str("Color.Red"),
                ),
                // Structurally clean but ill-typed: `Type` is not a `Color`.
                audit_definition(&bad.to_string(), color, Expr::type_()),
            ],
        }),
    );

    let error = registry
        .run_derive("Audit", &ind, &mut env)
        .expect_err("a late kernel failure must reject the complete derive batch");
    assert!(matches!(error, DeriveError::RegistrationFailed { .. }));
    assert!(env.get_const(&good).is_none());
    assert!(env.get_const(&bad).is_none());
}

#[test]
fn test_derived_name_collision_rolls_back_parent_inductive() {
    let mut env = Environment::new();
    let parent = Name::from_string("CollisionParent");
    let ctor = Name::from_string("CollisionParent.mk");
    let parent_ty = Expr::const_(parent.clone(), vec![]);
    let result = ElabResult::Inductive {
        name: parent.clone(),
        universe_params: vec![],
        num_params: 0,
        ty: Expr::type_(),
        constructors: vec![(ctor.clone(), parent_ty.clone())],
        wants_deep_induction: false,
        derived_instances: vec![DerivedInstance {
            // Deliberately collide with the constructor created by add_inductive.
            name: ctor.clone(),
            class_name: Name::from_string("AuditClass"),
            ty: parent_ty,
            val: Expr::const_(ctor.clone(), vec![]),
            priority: 100,
            level_params: vec![],
        }],
        modifiers: clean_parser::DeclModifiers::default(),
    };

    let error = crate::register::register_elab_result(&mut env, &result)
        .expect_err("derived declaration collisions must fail closed");
    assert!(error.to_string().contains("collides"));
    assert!(
        env.get_inductive(&parent).is_none(),
        "late derive failure must roll back the parent inductive"
    );
    assert!(env.get_const(&ctor).is_none());
}

#[test]
fn test_multiple_registration_surfaces_failed_leaf_transactionally() {
    let mut env = Environment::new();
    let good = Name::from_string("multipleGood");
    let failed_decl = clean_parser::parse_file("axiom multipleBad : Prop")
        .expect("failed-leaf fixture should parse")
        .into_iter()
        .next()
        .expect("fixture contains one declaration");
    let result = ElabResult::Multiple(vec![
        ElabResult::Axiom {
            name: good.clone(),
            universe_params: vec![],
            ty: Expr::prop(),
            modifiers: clean_parser::DeclModifiers::default(),
        },
        ElabResult::Failed {
            name: "multipleBad".to_owned(),
            decl: Box::new(failed_decl),
            error: Box::new(crate::ElabError::UnknownIdent("missing".to_owned())),
        },
    ]);

    let error = crate::register::register_elab_result(&mut env, &result)
        .expect_err("Failed leaves must never be converted to registration success");
    assert!(matches!(error, crate::ElabError::UnknownIdent(_)));
    assert!(
        env.get_const(&good).is_none(),
        "Multiple registration must roll back earlier leaves on failure"
    );
}

// ---------------------------------------------------------------------------
// BEq derive tests
// ---------------------------------------------------------------------------

#[test]
fn test_first_generation_beq_multi_ctor_is_structural_and_sorry_free() {
    let (env, ind) = make_color_env();
    let handler = DeriveBEq;

    let decls = handler
        .derive(&ind, &env)
        .expect("canonical BEq should use the structural batch-2 enum builder");
    match &decls[0] {
        Declaration::Definition { value, .. } => {
            assert!(expr_contains_const(value, "Color.rec"));
            assert!(!expr_contains_sorry_const(value));
        }
        other => panic!("expected Definition, got {other:?}"),
    }
}

#[test]
fn test_first_generation_beq_fielded_type_fails_closed() {
    let (env, ind) = make_point_env();
    let handler = DeriveBEq;

    let error = handler
        .derive(&ind, &env)
        .expect_err("legacy BEq must not ignore structure fields");
    match error {
        DeriveError::Unsupported { reason, .. } => {
            assert!(reason.contains("no structural BEq construction"));
        }
        other => panic!("expected Unsupported, got {other:?}"),
    }
}

#[test]
fn test_first_generation_beq_subsingleton_is_exact_and_sorry_free() {
    let mut env = Environment::new();
    let solo_name = Name::from_string("Solo");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: solo_name.clone(),
            type_: Expr::type_(),
            constructors: vec![clean_kernel::Constructor {
                name: Name::from_string("Solo.mk"),
                type_: Expr::const_(solo_name.clone(), vec![]),
            }],
        }],
    })
    .expect("should add singleton inductive");
    let ind = env
        .get_inductive(&solo_name)
        .expect("Solo should be in env")
        .clone();
    let handler = DeriveBEq;

    let decls = handler
        .derive(&ind, &env)
        .expect("constant true is exact for a singleton type");

    match &decls[0] {
        Declaration::Definition { value, .. } => {
            assert!(
                expr_contains_const(value, "Bool.true"),
                "subsingleton equality should be the exact constant-true function"
            );
            assert!(
                !expr_contains_sorry_const(value),
                "exact singleton BEq must not introduce sorry/sorryAx"
            );
        }
        other => panic!("expected Definition, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Repr derive tests
// ---------------------------------------------------------------------------

#[test]
fn test_derive_repr_produces_valid_declaration() {
    let (env, ind) = make_color_env();
    let handler = DeriveRepr;

    let decls = handler
        .derive(&ind, &env)
        .expect("Repr derive should succeed");
    assert_eq!(decls.len(), 1);

    match &decls[0] {
        Declaration::Definition { name, value, .. } => {
            assert_eq!(name.to_string(), "instReprColor");
            // The value should contain a lambda (Repr.mk wraps fun val prec => ...)
            // The outer node is App(Repr.mk, lam(...)), so check for App.
            assert!(
                matches!(value.kind(), ExprKind::App(..)),
                "repr value should be an application (Repr.mk <lam>)"
            );
        }
        other => panic!("expected Definition, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Hashable derive tests
// ---------------------------------------------------------------------------

#[test]
fn test_derive_hashable_produces_declaration() {
    let (env, ind) = make_color_env();
    let handler = DeriveHashable;

    let decls = handler
        .derive(&ind, &env)
        .expect("Hashable derive should succeed");
    assert_eq!(decls.len(), 1);

    match &decls[0] {
        Declaration::Definition { name, .. } => {
            assert_eq!(name.to_string(), "instHashableColor");
        }
        other => panic!("expected Definition, got {other:?}"),
    }
}

#[test]
fn test_derive_hashable_enum_is_constructor_sensitive_without_sorry() {
    let (env, ind) = make_color_env();
    let handler = DeriveHashable;

    let decls = handler
        .derive(&ind, &env)
        .expect("Hashable derive should succeed");

    match &decls[0] {
        Declaration::Definition { value, .. } => {
            assert!(
                expr_contains_const(value, "Color.rec"),
                "Hashable enum should dispatch on the constructor"
            );
            assert!(
                !expr_contains_sorry_const(value),
                "Hashable derivation must not introduce sorry/sorryAx"
            );
        }
        other => panic!("expected Definition, got {other:?}"),
    }
}

#[test]
fn test_derive_hashable_parametric_struct_fails_closed() {
    let (env, ind) = make_parametric_box_env_with_hashable();
    let handler = DeriveHashable;

    let error = handler
        .derive(&ind, &env)
        .expect_err("parametric Hashable must not install a constant-zero placeholder");
    match error {
        DeriveError::Unsupported { reason, .. } => {
            assert!(reason.contains("no structural Hashable construction"));
        }
        other => panic!("expected Unsupported, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Inhabited derive tests
// ---------------------------------------------------------------------------

#[test]
fn test_derive_inhabited_picks_first_constructor() {
    let (env, ind) = make_color_env();
    let handler = DeriveInhabited;

    let decls = handler
        .derive(&ind, &env)
        .expect("Inhabited derive should succeed");
    assert_eq!(decls.len(), 1);

    match &decls[0] {
        Declaration::Definition { name, value, .. } => {
            assert_eq!(name.to_string(), "instInhabitedColor");
            // The value should be an App node (Inhabited.mk <ctor>).
            assert!(
                matches!(value.kind(), ExprKind::App(..)),
                "inhabited value should be an application"
            );
        }
        other => panic!("expected Definition, got {other:?}"),
    }
}

#[test]
fn test_derive_inhabited_struct_with_fields_fails_closed() {
    let (env, ind) = make_point_env();
    let handler = DeriveInhabited;

    let error = handler
        .derive(&ind, &env)
        .expect_err("field defaults require actual Inhabited instance synthesis");
    match error {
        DeriveError::Unsupported { reason, .. } => {
            assert!(reason.contains("first constructor has fields"));
        }
        other => panic!("expected Unsupported, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// DecidableEq derive tests
// ---------------------------------------------------------------------------

#[test]
fn test_first_generation_decidable_eq_is_proof_producing_and_sorry_free() {
    let (env, ind) = make_color_env();
    let handler = DeriveDecidableEq;

    let decls = handler
        .derive(&ind, &env)
        .expect("canonical DecidableEq should use the proof-producing batch-2 builder");
    match &decls[0] {
        Declaration::Definition { value, .. } => {
            assert!(expr_contains_const(value, "Color.noConfusion"));
            assert!(!expr_contains_sorry_const(value));
        }
        other => panic!("expected Definition, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Error case tests
// ---------------------------------------------------------------------------

#[test]
fn test_derive_beq_reflexive_inductive_rejected() {
    // Build a reflexive inductive (one that contains Ind -> Ind in a
    // constructor argument).
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
    let handler = DeriveBEq;

    let result = handler.derive(&ind, &env);
    assert!(result.is_err());
    match result.unwrap_err() {
        DeriveError::Unsupported {
            class_name,
            ind_name,
            reason,
        } => {
            assert_eq!(class_name, "BEq");
            assert_eq!(ind_name, "Tree");
            assert!(reason.contains("reflexive"));
        }
        other => panic!("expected Unsupported, got {other:?}"),
    }
}

#[test]
fn test_derive_inhabited_no_constructors_error() {
    // Build an inductive with no constructors (like Empty/False).
    let empty_name = Name::from_string("Empty");
    let mut env = Environment::new();

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

    let handler = DeriveInhabited;
    let result = handler.derive(&ind_val, &env);
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

// ---------------------------------------------------------------------------
// Full registry integration test
// ---------------------------------------------------------------------------

#[test]
fn test_derive_registry_full_run_beq() {
    let mut registry = DeriveRegistry::new();
    register_builtin_handlers(&mut registry);

    let (mut env, ind) = make_color_env_with_prelude();
    registry
        .run_derive("BEq", &ind, &mut env)
        .expect("canonical BEq should generate and kernel-register structural equality");

    let registered = env
        .get_const(&Name::from_string("instBEqColor"))
        .expect("canonical registry should add instBEqColor");
    assert!(!registered.type_.has_sorry());
    assert!(!registered.value.as_ref().is_some_and(Expr::has_sorry));
}

#[test]
fn test_derive_all_handlers_on_enum() {
    let (env, ind) = make_color_env();
    let mut registry = DeriveRegistry::new();
    register_builtin_handlers(&mut registry);

    // Each handler should produce exactly one declaration for the simple enum.
    for class in &["BEq", "Repr", "Hashable", "Inhabited", "DecidableEq"] {
        let handler = registry
            .handlers
            .get(*class)
            .unwrap_or_else(|| panic!("{class} handler should be registered"));
        let decls = handler
            .derive(&ind, &env)
            .unwrap_or_else(|e| panic!("{class} derive failed: {e}"));
        assert_eq!(
            decls.len(),
            1,
            "{class} should produce exactly 1 declaration"
        );
    }
}

#[test]
fn test_derive_debug_format() {
    let mut registry = DeriveRegistry::new();
    register_builtin_handlers(&mut registry);

    let debug_str = format!("{registry:?}");
    assert!(debug_str.contains("DeriveRegistry"));
    assert!(debug_str.contains("BEq"));
}

#[test]
fn test_derive_default_impl() {
    let registry = DeriveRegistry::default();
    assert!(registry.registered_classes().is_empty());
}

// ---------------------------------------------------------------------------
// Issue #3417: DecidableEq strict kernel type-check regression
// ---------------------------------------------------------------------------

/// Build a simple enum in an environment with full prelude so kernel type
/// checking has access to Eq, Decidable, DecidableEq, sorryAx, etc.
fn make_color_env_with_prelude() -> (Environment, InductiveVal) {
    let mut env = Environment::with_prelude();

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

/// Regression test for #3417: DeriveDecidableEq handler must produce
/// declarations that pass strict kernel type checking (add_decl).
///
/// Before the fix, Eq/DecidableEq/sorryAx were created with empty universe
/// levels via Expr::const_str, causing "expected Sort(Succ(Zero)), got
/// Const(Nat)" type mismatches when the kernel tried to check the instance.
#[test]
fn test_issue3417_derive_decidable_eq_strict_kernel_check() {
    let (mut env, ind) = make_color_env_with_prelude();
    let mut registry = DeriveRegistry::new();
    register_builtin_handlers(&mut registry);

    registry
        .run_derive("DecidableEq", &ind, &mut env)
        .expect("canonical DecidableEq should pass strict kernel registration");
    let registered = env
        .get_const(&Name::from_string("instDecidableEqColor"))
        .expect("canonical registry should add instDecidableEqColor");
    assert!(!registered.type_.has_sorry());
    assert!(!registered.value.as_ref().is_some_and(Expr::has_sorry));
}

/// Same as above but for a struct with Nat fields (the original #3417 scenario).
#[test]
fn test_issue3417_derive_decidable_eq_struct_with_nat_strict_kernel_check() {
    let mut env = Environment::with_prelude();

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

    let mut registry = DeriveRegistry::new();
    register_builtin_handlers(&mut registry);
    registry
        .run_derive("DecidableEq", &ind_val, &mut env)
        .expect("canonical Point DecidableEq should pass strict kernel registration");
    let registered = env
        .get_const(&Name::from_string("instDecidableEqPoint"))
        .expect("canonical registry should add instDecidableEqPoint");
    assert!(!registered.type_.has_sorry());
    assert!(!registered.value.as_ref().is_some_and(Expr::has_sorry));
}

// ---------------------------------------------------------------------------
// Nonempty derive tests (newly wired canonical handler)
// ---------------------------------------------------------------------------

#[test]
fn test_derive_nonempty_enum_produces_declaration() {
    let (env, ind) = make_color_env();
    let handler = DeriveNonempty;

    let decls = handler
        .derive(&ind, &env)
        .expect("Nonempty derive should succeed for nullary enum");
    assert_eq!(decls.len(), 1);

    match &decls[0] {
        Declaration::Definition { name, value, .. } => {
            assert_eq!(name.to_string(), "instNonemptyColor");
            assert!(
                expr_contains_const(value, "Nonempty.intro"),
                "Nonempty instance value should use Nonempty.intro"
            );
            assert!(
                !expr_contains_sorry_const(value),
                "Nonempty witness must not introduce sorry/sorryAx"
            );
        }
        other => panic!("expected Definition, got {other:?}"),
    }
}

#[test]
fn test_derive_nonempty_enum_strict_kernel_check() {
    let (mut env, ind) = make_color_env_with_prelude();
    let handler = DeriveNonempty;

    let decls = handler
        .derive(&ind, &env)
        .expect("Nonempty derive should succeed");
    assert_eq!(decls.len(), 1);

    // add_decl runs full strict kernel type checking against the prelude
    // (which provides Nonempty / Nonempty.intro via init_classical).
    let add_result = env.add_decl(decls.into_iter().next().unwrap());
    assert!(
        add_result.is_ok(),
        "Nonempty instance from DeriveNonempty must pass strict kernel type \
         check: {:?}",
        add_result.err()
    );
}

#[test]
fn test_derive_nonempty_struct_with_fields_is_unsupported() {
    // Point.mk has Nat fields, so no closed witness can be synthesized.
    let (env, ind) = make_point_env();
    let handler = DeriveNonempty;

    let result = handler.derive(&ind, &env);
    match result {
        Err(DeriveError::Unsupported {
            class_name, reason, ..
        }) => {
            assert_eq!(class_name, "Nonempty");
            assert!(reason.contains("fields"));
        }
        other => panic!("expected Unsupported for struct with fields, got {other:?}"),
    }
}

#[test]
fn test_derive_nonempty_empty_type_is_unsupported() {
    let mut env = Environment::new();
    let empty_name = Name::from_string("Empty");
    let empty_type = Expr::sort(Level::succ(Level::zero()));
    let ind_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: empty_name.clone(),
            type_: empty_type,
            constructors: vec![],
        }],
    };
    env.add_inductive(ind_decl)
        .expect("should add Empty inductive");
    let ind = env
        .get_inductive(&empty_name)
        .expect("Empty should be in env")
        .clone();

    let handler = DeriveNonempty;
    match handler.derive(&ind, &env) {
        Err(DeriveError::Unsupported {
            class_name, reason, ..
        }) => {
            assert_eq!(class_name, "Nonempty");
            assert!(reason.contains("no constructors"));
        }
        other => panic!("expected Unsupported for empty type, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// SizeOf derive tests (newly wired canonical handler)
// ---------------------------------------------------------------------------

#[test]
fn test_derive_sizeof_enum_fails_closed() {
    let (env, ind) = make_color_env();
    let handler = DeriveSizeOf;

    let error = handler
        .derive(&ind, &env)
        .expect_err("SizeOf must not use a constant-zero implementation");
    match error {
        DeriveError::Unsupported { reason, .. } => {
            assert!(reason.contains("no structural SizeOf construction"));
        }
        other => panic!("expected Unsupported, got {other:?}"),
    }
}

#[test]
fn test_derive_sizeof_struct_fails_closed() {
    let (env, ind) = make_point_env();
    let handler = DeriveSizeOf;

    let error = handler
        .derive(&ind, &env)
        .expect_err("SizeOf must not ignore structure fields");
    match error {
        DeriveError::Unsupported { reason, .. } => {
            assert!(reason.contains("no structural SizeOf construction"));
        }
        other => panic!("expected Unsupported, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// End-to-end dispatch through register_all_handlers (the main dispatch)
// ---------------------------------------------------------------------------

#[test]
fn test_run_derive_nonempty_via_register_all_handlers() {
    let mut registry = DeriveRegistry::new();
    crate::derive_ext::register_all_handlers(&mut registry);

    let (mut env, ind) = make_color_env_with_prelude();

    // run_derive both invokes the handler and adds the (kernel-checked)
    // declaration to the environment. Before wiring, this returned NoHandler.
    registry
        .run_derive("Nonempty", &ind, &mut env)
        .expect("deriving Nonempty should succeed through the main dispatch");

    assert!(
        env.get_const(&Name::from_string("instNonemptyColor"))
            .is_some(),
        "derived Nonempty instance should be registered in the environment"
    );
}

#[test]
fn test_run_derive_nonempty_without_wiring_would_have_no_handler() {
    // Documents the pre-fix behavior: a registry with only the original
    // builtin handlers has no Nonempty handler, so `deriving Nonempty`
    // silently fails with NoHandler.
    let mut registry = DeriveRegistry::new();
    register_builtin_handlers(&mut registry);

    let (mut env, ind) = make_color_env();
    match registry.run_derive("Nonempty", &ind, &mut env) {
        Err(DeriveError::NoHandler(name)) => assert_eq!(name, "Nonempty"),
        other => panic!("expected NoHandler before wiring, got {other:?}"),
    }
}
