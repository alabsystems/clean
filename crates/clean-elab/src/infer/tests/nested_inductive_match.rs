// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for #3406: pattern matching on nested inductives.
//!
//! When an inductive type uses a container like `List` in a constructor field
//! (e.g., `aggregate : List Value -> Value`), the kernel eliminates this into
//! a temporary mutual block. Kernel restore erases the auxiliary public type,
//! restores constructor fields to `List Value`, and retains its computation as
//! `Value.rec_1`. The primary eliminator still expects every motive and minor;
//! the elaborator must supply them from the restored recursor signature.

use super::*;
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};

/// Build an environment with List, Nat, Bool, and Value (nested inductive).
///
/// Value has 4 constructors:
///   | int : Nat -> Nat -> Value
///   | float : Nat -> Value
///   | bool : Bool -> Value
///   | aggregate : List Value -> Value
///
/// After restore, Value's public block contains only Value, while Value.casesOn
/// still has num_motives=2 and num_minors=6 (4 Value + 2 restored List rules).
fn make_value_env() -> Environment {
    let mut env = Environment::new();
    let u = Name::from_string("u");

    // --- List : Type u → Type u ---
    let list = Name::from_string("List");
    let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone()))));
    let list_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());
    let list_a = Expr::app(
        Expr::const_(list.clone(), vec![Level::param(u.clone())]),
        Expr::bvar(0),
    );
    let nil_type = Expr::pi(BinderInfo::Default, type_u.clone(), list_a.clone());
    let cons_body = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(0), // A
        Expr::pi(
            BinderInfo::Default,
            Expr::app(
                Expr::const_(list.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(1),
            ),
            Expr::app(
                Expr::const_(list.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(2),
            ),
        ),
    );
    let cons_type = Expr::pi(BinderInfo::Default, type_u, cons_body);
    env.add_inductive(InductiveDecl {
        level_params: vec![u],
        num_params: 1,
        types: vec![InductiveType {
            name: list.clone(),
            type_: list_type,
            constructors: vec![
                Constructor {
                    name: Name::from_string("List.nil"),
                    type_: nil_type,
                },
                Constructor {
                    name: Name::from_string("List.cons"),
                    type_: cons_type,
                },
            ],
        }],
    })
    .unwrap();

    // --- Nat ---
    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: nat_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::arrow(nat_ref.clone(), nat_ref.clone()),
                },
            ],
        }],
    })
    .unwrap();

    // --- Bool ---
    let bool_name = Name::from_string("Bool");
    let bool_ref = Expr::const_(bool_name.clone(), vec![]);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: bool_name.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Bool.true"),
                    type_: bool_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Bool.false"),
                    type_: bool_ref.clone(),
                },
            ],
        }],
    })
    .unwrap();

    // --- Value (nested: uses List Value) ---
    let value = Name::from_string("Value");
    let value_ref = Expr::const_(value.clone(), vec![]);
    // List.{0} Value — universe 0 because Value : Type 0
    let list_value = Expr::app(Expr::const_(list, vec![Level::zero()]), value_ref.clone());
    let int_type = Expr::pi(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::pi(BinderInfo::Default, nat_ref.clone(), value_ref.clone()),
    );
    let float_type = Expr::pi(BinderInfo::Default, nat_ref.clone(), value_ref.clone());
    let bool_type = Expr::pi(BinderInfo::Default, bool_ref, value_ref.clone());
    let aggregate_type = Expr::pi(BinderInfo::Default, list_value, value_ref.clone());

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: value.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Value.int"),
                    type_: int_type,
                },
                Constructor {
                    name: Name::from_string("Value.float"),
                    type_: float_type,
                },
                Constructor {
                    name: Name::from_string("Value.bool"),
                    type_: bool_type,
                },
                Constructor {
                    name: Name::from_string("Value.aggregate"),
                    type_: aggregate_type,
                },
            ],
        }],
    })
    .expect("Value nested inductive should be added");

    // Sanity: verify the restored nested-block structure.
    let val_info = env
        .get_inductive(&value)
        .expect("Value should be registered");
    assert!(val_info.is_nested, "Value should be marked nested");
    assert_eq!(
        val_info.all_names.len(),
        1,
        "nested restore must erase the auxiliary type from Value.all_names"
    );
    assert!(
        env.get_recursor(&Name::from_string("Value.rec_1"))
            .is_some(),
        "nested restore must retain the auxiliary computation as Value.rec_1"
    );

    // Add a Value axiom as the scrutinee
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("v"),
        level_params: vec![],
        type_: value_ref,
    })
    .unwrap();

    env
}

/// Reproduce the `.olean` shape for a restored nested inductive: the public
/// block contains only `ImportedValue`, the primitive recursor retains two
/// motives/six minors plus `ImportedValue.rec_1`, and `casesOn` is present only
/// as a value-bearing definition that delegates to `.rec`.
fn make_import_shaped_restored_nested_env() -> Environment {
    let mut donor = Environment::with_prelude();
    let decl = parse_decl_for_elab(
        r"inductive ImportedValue where
            | atom : Nat -> ImportedValue
            | pair : Nat -> Nat -> ImportedValue
            | aggregate : List ImportedValue -> ImportedValue",
    )
    .expect("import-shaped nested donor should parse");
    crate::elaborate_decl_and_register(&mut donor, &decl)
        .expect("import-shaped nested donor should register");

    let value_name = Name::from_string("ImportedValue");
    let cases_name = Name::from_string("ImportedValue.casesOn");
    let value_info = donor
        .get_inductive(&value_name)
        .cloned()
        .expect("donor ImportedValue metadata");
    assert!(value_info.is_nested);
    assert_eq!(value_info.all_names, vec![value_name.clone()]);

    let mut env = Environment::with_prelude();
    env.register_inductive(value_info.clone());
    for ctor_name in &value_info.constructor_names {
        env.register_constructor(
            donor
                .get_constructor(ctor_name)
                .cloned()
                .unwrap_or_else(|| panic!("donor constructor {ctor_name}")),
        );
    }
    for rec_name in ["ImportedValue.rec", "ImportedValue.rec_1"] {
        env.register_recursor(
            donor
                .get_recursor(&Name::from_string(rec_name))
                .cloned()
                .unwrap_or_else(|| panic!("donor recursor {rec_name}")),
        );
    }

    let cases_const = donor
        .get_const(&cases_name)
        .cloned()
        .expect("donor casesOn definition");
    assert!(
        cases_const.value.is_some(),
        "generated casesOn must supply the imported definition body"
    );
    env.extend_constants_unchecked(std::iter::once(cases_const));

    let rec = env
        .get_recursor(&Name::from_string("ImportedValue.rec"))
        .expect("imported primitive recursor");
    assert_eq!(rec.num_motives, 2);
    assert_eq!(rec.num_minors, 5);
    assert!(env
        .get_recursor(&Name::from_string("ImportedValue.rec_1"))
        .is_some());
    assert!(env.get_recursor(&cases_name).is_none());
    assert!(env.get_const(&cases_name).is_some());
    env
}

fn register_checked(env: &mut Environment, source: &str, label: &str) {
    let decl = parse_decl_for_elab(source).unwrap_or_else(|err| panic!("{label}: {err:?}"));
    crate::elaborate_decl_and_register(env, &decl)
        .unwrap_or_else(|err| panic!("{label} should elaborate and kernel-check: {err:?}"));
}

#[test]
fn imported_restored_nested_plain_match_uses_rec_authority() {
    let mut env = make_import_shaped_restored_nested_env();
    register_checked(
        &mut env,
        r"def importedNestedPlain : ImportedValue -> Nat
            | .atom n => n
            | .pair a _ => a
            | .aggregate _ => 0",
        "plain match over imported restored nested inductive",
    );
    let value = env
        .get_const(&Name::from_string("importedNestedPlain"))
        .and_then(|decl| decl.value.as_ref())
        .expect("registered plain match value");
    assert!(!value.has_sorry());
}

#[test]
fn imported_restored_nested_do_match_uses_rec_authority() {
    let mut env = make_import_shaped_restored_nested_env();
    register_checked(
        &mut env,
        r"def importedNestedDo (v : ImportedValue) : Except String Nat := do
            match v with
            | .atom n => Except.ok n
            | .pair a _ => Except.ok a
            | .aggregate _ => Except.ok 0",
        "do-match over imported restored nested inductive",
    );
    let value = env
        .get_const(&Name::from_string("importedNestedDo"))
        .and_then(|decl| decl.value.as_ref())
        .expect("registered do-match value");
    assert!(!value.has_sorry());
}

#[test]
fn imported_restored_nested_nested_pattern_uses_rec_authority() {
    let mut env = make_import_shaped_restored_nested_env();
    register_checked(
        &mut env,
        "inductive ImportedHolder where\n  | mk : ImportedValue -> ImportedHolder",
        "holder fixture",
    );
    register_checked(
        &mut env,
        r"def importedNestedPattern : ImportedHolder -> Nat
            | .mk (.atom n) => n
            | _ => 0",
        "nested pattern over imported restored nested inductive",
    );
    let value = env
        .get_const(&Name::from_string("importedNestedPattern"))
        .and_then(|decl| decl.value.as_ref())
        .expect("registered nested-pattern value");
    assert!(!value.has_sorry());
}

#[test]
fn recursive_arm_rejects_non_inductive_scrutinee_without_fabricating_lambdas() {
    use clean_parser::{Span, SurfaceLit, SurfacePattern};

    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let depth_before = ctx.metas.scope_depth();
    let body = SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0));
    let result = ctx.elaborate_rec_arm(
        "Nat.succ",
        &[SurfacePattern::Var("n".to_string())],
        &body,
        &Expr::type_(),
        &Expr::const_(Name::from_string("Nat"), vec![]),
        0,
        &[],
    );
    assert!(
        matches!(result, Err(ElabError::TypeMismatch { .. })),
        "recursive lowering must reject a non-inductive scrutinee instead of wrapping fresh-meta lambdas, got {result:?}"
    );
    assert!(ctx.locals.is_empty());
    assert_eq!(ctx.metas.scope_depth(), depth_before);
}

#[test]
fn recursive_arm_rejects_truncated_constructor_field_telescope() {
    use clean_parser::{Span, SurfaceLit, SurfacePattern};

    let mut env = Environment::with_prelude();
    register_checked(
        &mut env,
        r"inductive ExactRec where
            | leaf : ExactRec
            | next : Nat -> ExactRec -> ExactRec",
        "recursive telescope fixture",
    );
    let next_name = Name::from_string("ExactRec.next");
    let mut malformed = env
        .get_constructor(&next_name)
        .cloned()
        .expect("ExactRec.next metadata");
    // Keep `num_fields = 2` and the authentic recursor rule, but truncate the
    // constructor metadata after one field. The constant map still contains
    // the genuine kernel-checked constructor type, reproducing disagreement at
    // the metadata authority boundary.
    malformed.type_ = Expr::arrow(
        Expr::const_(Name::from_string("Nat"), vec![]),
        Expr::const_(Name::from_string("ExactRec"), vec![]),
    );
    env.register_constructor(malformed);

    let mut ctx = ElabCtx::new(&env);
    let depth_before = ctx.metas.scope_depth();
    let body = SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0));
    let result = ctx.elaborate_rec_arm(
        "ExactRec.next",
        &[
            SurfacePattern::Var("n".to_string()),
            SurfacePattern::Var("tail".to_string()),
        ],
        &body,
        &Expr::const_(Name::from_string("ExactRec"), vec![]),
        &Expr::const_(Name::from_string("Nat"), vec![]),
        0,
        &[],
    );
    assert!(
        matches!(&result, Err(ElabError::InternalInvariant(message))
            if message.contains("ExactRec.next")
                && (message.contains("disagrees with its constant declaration")
                    || message.contains("telescope ends before field"))),
        "truncated field evidence must fail closed rather than inventing a Type metavariable, got {result:?}"
    );
    assert!(ctx.locals.is_empty(), "failed arm leaked field locals");
    assert_eq!(ctx.metas.scope_depth(), depth_before);
}

#[test]
fn metadata_fail_closed_constructor_disagreement_rolls_back_match_state() {
    use clean_parser::{Span, SurfaceLit, SurfaceMatchArm, SurfacePattern};

    let mut env = Environment::with_prelude();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // First pin the positive strict path: exact metadata recovers the genuine
    // field domain and expands the explicit pattern without fabricating data.
    let valid_ctx = ElabCtx::new(&env);
    assert_eq!(
        valid_ctx
            .compute_ctor_field_types(&Name::from_string("Nat.succ"), &nat)
            .expect("authentic Nat.succ fields"),
        vec![nat.clone()]
    );
    assert_eq!(
        valid_ctx
            .expand_implicit_ctor_field_patterns(
                "metadata positive control",
                "Nat.succ",
                &[SurfacePattern::Var("n".to_string())],
            )
            .expect("authentic explicit field packet")
            .len(),
        1
    );

    let succ_name = Name::from_string("Nat.succ");
    let mut malformed = env
        .get_constructor(&succ_name)
        .cloned()
        .expect("Nat.succ metadata");
    // Preserve num_fields=1 and the authentic recursor rule, but truncate the
    // trusted registry telescope. register_constructor preserves the existing
    // constant, so both the short telescope and authority disagreement exist.
    malformed.type_ = nat.clone();
    env.register_constructor(malformed);

    let mut ctx = ElabCtx::new(&env);
    let sentinel = ctx.push_local("sentinel".to_string(), nat.clone());
    ctx.current_expected_type = Some(nat.clone());
    let locals_before = ctx.locals.clone();
    let let_values_before = ctx.local_let_values.clone();
    let instances_before = ctx.local_instances.clone();
    let expected_before = ctx.current_expected_type.clone();
    let universes_before = ctx.universe_params.clone();
    let pending_before = ctx.pending_level_assigns.borrow().clone();
    let holes_before = ctx.hole_names.clone();
    let meta_depth_before = ctx.metas.scope_depth();
    let meta_trail_before = ctx.metas.undo_trail_len_for_tests();

    let expansion = ctx.expand_implicit_ctor_field_patterns(
        "constructor dispatch regression",
        "Nat.succ",
        &[SurfacePattern::Var("n".to_string())],
    );
    assert!(
        matches!(&expansion, Err(ElabError::InternalInvariant(message))
            if message.contains("Nat.succ")
                && (message.contains("disagrees with its constant declaration")
                    || message.contains("telescope ends before field"))),
        "constructor dispatch must propagate malformed binder metadata instead of converting it to an optional miss, got {expansion:?}"
    );

    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(SurfaceExpr::Ident(Span::dummy(), "sentinel".to_string())),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor("Nat.zero".to_string(), vec![]),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(
                    "Nat.succ".to_string(),
                    vec![SurfacePattern::Var("n".to_string())],
                ),
                body: SurfaceExpr::Ident(Span::dummy(), "n".to_string()),
            },
        ],
    );
    let result = ctx.elaborate(&match_expr);
    assert!(
        matches!(&result, Err(ElabError::InternalInvariant(message))
            if (message.contains("Nat.succ")
                    && message.contains("disagrees with its constant declaration"))
                || (message.contains("Nat.casesOn")
                    && message.contains("ended before")
                    && message.contains("field_0"))),
        "malformed constructor metadata must fail as a typed invariant, got {result:?}"
    );
    assert_eq!(ctx.locals, locals_before);
    assert_eq!(ctx.local_let_values, let_values_before);
    assert_eq!(ctx.local_instances, instances_before);
    assert_eq!(ctx.current_expected_type, expected_before);
    assert_eq!(ctx.universe_params, universes_before);
    assert_eq!(*ctx.pending_level_assigns.borrow(), pending_before);
    assert_eq!(ctx.hole_names, holes_before);
    assert_eq!(ctx.metas.scope_depth(), meta_depth_before);
    assert_eq!(ctx.metas.undo_trail_len_for_tests(), meta_trail_before);
    assert_eq!(
        ctx.elaborate(&SurfaceExpr::Ident(Span::dummy(), "sentinel".to_string(),))
            .expect("same context remains usable after failed match"),
        Expr::fvar(sentinel)
    );
}

#[test]
fn metadata_fail_closed_missing_default_constructor_mints_no_state() {
    // The compact nested-inductive fixture includes an ordinary Nat packet and
    // keeps the editable JSON below well under serde's nesting limit.
    let env = make_value_env();
    let mut json: clean_kernel::env::JsonEnvironment =
        serde_json::from_str(&env.to_json().expect("serialize prelude environment"))
            .expect("decode editable environment");
    json.constructors
        .retain(|ctor| ctor.name != Name::from_string("Nat.zero"));
    let env = Environment::from_json(
        &serde_json::to_string(&json).expect("encode malformed environment"),
    )
    .expect("load intentionally malformed environment");

    let ctx = ElabCtx::new(&env);
    let result = ctx.try_default_value_of_type(&Expr::const_(Name::from_string("Nat"), vec![]));
    assert!(
        matches!(&result, Err(ElabError::InternalInvariant(message))
            if message.contains("missing registered constructor metadata `Nat.zero`")),
        "missing nullary-constructor metadata must not be treated as no default, got {result:?}"
    );
    assert!(ctx.locals.is_empty());
    assert!(ctx.universe_params.is_empty());
    assert!(ctx.pending_level_assigns.borrow().is_empty());
    assert_eq!(ctx.metas.scope_depth(), 0);
    assert_eq!(ctx.metas.undo_trail_len_for_tests(), 0);
}

#[test]
fn index_discriminator_rejects_constructor_universe_mismatch_transactionally() {
    let mut env = Environment::with_prelude();
    register_checked(
        &mut env,
        r"inductive IndexedBox : Nat -> Type where
            | zero : IndexedBox 0
            | succ : (n : Nat) -> IndexedBox (Nat.succ n)",
        "indexed discriminator fixture",
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("indexWitness"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .expect("index witness axiom should register");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let succ_index = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("indexWitness"), vec![]),
    );
    let scrutinee_ty = Expr::app(
        Expr::const_(Name::from_string("IndexedBox"), vec![]),
        succ_index,
    );

    let mut valid_ctx = ElabCtx::new(&env);
    assert!(
        valid_ctx
            .build_index_discriminating_motive_body(&scrutinee_ty, "IndexedBox", &nat)
            .expect("valid discriminator probe")
            .is_some(),
        "fixture must exercise the positive discriminator path"
    );

    let succ_name = Name::from_string("Nat.succ");
    let mut malformed = env
        .get_constructor(&succ_name)
        .cloned()
        .expect("Nat.succ metadata");
    malformed
        .level_params
        .push(Name::from_string("fabricated_level"));
    env.register_constructor(malformed);

    let mut ctx = ElabCtx::new(&env);
    let locals_before = ctx.locals.clone();
    let depth_before = ctx.metas.scope_depth();
    let result = ctx
        .build_index_discriminating_motive_body(&scrutinee_ty, "IndexedBox", &nat)
        .expect("metadata mismatch is an optional-probe miss");
    assert!(
        result.is_none(),
        "constructor level-count mismatch must not be repaired with zero universes"
    );
    assert_eq!(ctx.locals, locals_before);
    assert_eq!(ctx.metas.scope_depth(), depth_before);
}

#[test]
fn do_match_respects_registered_major_after_minors_layout() {
    let mut env = Environment::with_prelude();
    let rec_name = Name::from_string("Bool.rec");
    let cases_name = Name::from_string("Bool.casesOn");

    // Install a coherent rec-layout eliminator under the casesOn name. This is
    // the non-default but supported registered shape: motive → minors → major.
    // The old do-match lowering unconditionally placed the major after the
    // motive and therefore fed `b` to the false-minor slot.
    let mut rec_const = env
        .get_const(&rec_name)
        .cloned()
        .expect("Bool.rec constant");
    rec_const.name = cases_name.clone();
    assert!(env.forget_decl(&cases_name));
    env.extend_constants_unchecked(std::iter::once(rec_const));
    let mut rec = env
        .get_recursor(&rec_name)
        .cloned()
        .expect("Bool.rec metadata");
    rec.name = cases_name.clone();
    assert_eq!(
        rec.arg_order,
        clean_kernel::RecursorArgOrder::MajorAfterMinors
    );
    env.register_recursor(rec);

    register_checked(
        &mut env,
        r"def registeredRecLayoutDo (b : Bool) : Except String Nat := do
            match b with
            | Bool.false => Except.ok 0
            | Bool.true => Except.ok 1",
        "do-match registered MajorAfterMinors layout",
    );
    let value = env
        .get_const(&Name::from_string("registeredRecLayoutDo"))
        .and_then(|decl| decl.value.as_ref())
        .expect("registered rec-layout do-match value");
    assert!(!value.has_sorry());
}

/// #3406: Pattern matching on a nested inductive (Value with List Value) should
/// supply extra motives and minors for the auxiliary types in the mutual block.
#[test]
fn test_match_nested_inductive_value_elaborates() {
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let env = make_value_env();
    let scrutinee = SurfaceExpr::Ident(Span::dummy(), "v".to_string());
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(scrutinee),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(
                    "Value.int".to_string(),
                    vec![
                        SurfacePattern::Var("a".to_string()),
                        SurfacePattern::Var("b".to_string()),
                    ],
                ),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(
                    "Value.float".to_string(),
                    vec![SurfacePattern::Var("x".to_string())],
                ),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(2)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(
                    "Value.bool".to_string(),
                    vec![SurfacePattern::Var("b".to_string())],
                ),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(3)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(
                    "Value.aggregate".to_string(),
                    vec![SurfacePattern::Var("items".to_string())],
                ),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(4)),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr);
    assert!(
        result.is_ok(),
        "Pattern match on nested inductive Value should elaborate (#3406), got: {result:?}"
    );
}

/// #3406 end-to-end: Parse and register Value inductive, then register a def
/// that pattern-matches on it. This is the exact repro from the issue.
#[test]
fn test_3406_end_to_end_def_match_on_nested_inductive() {
    let mut env = Environment::with_prelude();

    // Register Value inductive with nested List Value
    let decls = [
        r"inductive Value where
            | int : Nat -> Nat -> Value
            | float : Nat -> Value
            | bool : Bool -> Value
            | ptr : Nat -> Value
            | nullPtr : Value
            | undef : Value
            | aggregate : List Value -> Value",
        r"def Value.isPtr : Value -> Bool
            | Value.ptr _ => Bool.true
            | _ => Bool.false",
    ];

    for decl_src in decls {
        let decl =
            parse_decl_for_elab(decl_src).unwrap_or_else(|_| panic!("should parse: {decl_src}"));
        let result = crate::elaborate_decl_and_register(&mut env, &decl);
        assert!(
            result.is_ok(),
            "#3406: pattern match on nested inductive Value should elaborate and register, got {result:?} for:\n{decl_src}"
        );
    }

    assert!(
        env.get_const(&Name::from_string("Value.isPtr")).is_some(),
        "Value.isPtr should be registered"
    );
}

/// #3406: Matching on each constructor individually, including aggregate.
#[test]
fn test_3406_end_to_end_match_all_ctors() {
    let mut env = Environment::with_prelude();

    let decls = [
        r"inductive Value where
            | int : Nat -> Nat -> Value
            | float : Nat -> Value
            | bool : Bool -> Value
            | ptr : Nat -> Value
            | nullPtr : Value
            | undef : Value
            | aggregate : List Value -> Value",
        r"def Value.tag : Value -> Nat
            | Value.int _ _ => 0
            | Value.float _ => 1
            | Value.bool _ => 2
            | Value.ptr _ => 3
            | Value.nullPtr => 4
            | Value.undef => 5
            | Value.aggregate _ => 6",
    ];

    for decl_src in decls {
        let decl =
            parse_decl_for_elab(decl_src).unwrap_or_else(|_| panic!("should parse: {decl_src}"));
        let result = crate::elaborate_decl_and_register(&mut env, &decl);
        assert!(
            result.is_ok(),
            "#3406: full constructor match should elaborate and register, got {result:?} for:\n{decl_src}"
        );
    }

    assert!(
        env.get_const(&Name::from_string("Value.tag")).is_some(),
        "Value.tag should be registered"
    );
}

/// #3406: Verify the elaborated match expression type-checks in the kernel.
/// This directly checks that the casesOn application has the correct number
/// of arguments (including extra motives and minors for the mutual block).
#[test]
fn test_3406_kernel_typecheck_match_on_nested() {
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let env = make_value_env();
    let scrutinee = SurfaceExpr::Ident(Span::dummy(), "v".to_string());
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(scrutinee),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(
                    "Value.int".to_string(),
                    vec![
                        SurfacePattern::Var("a".to_string()),
                        SurfacePattern::Var("b".to_string()),
                    ],
                ),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(
                    "Value.float".to_string(),
                    vec![SurfacePattern::Var("x".to_string())],
                ),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(2)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(
                    "Value.bool".to_string(),
                    vec![SurfacePattern::Var("b".to_string())],
                ),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(3)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(
                    "Value.aggregate".to_string(),
                    vec![SurfacePattern::Var("items".to_string())],
                ),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(4)),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx
        .elaborate(&match_expr)
        .expect("elaboration should succeed");

    // Now kernel-typecheck the result
    let ty = ctx.infer_type(&result);
    assert!(
        ty.is_ok(),
        "Kernel type inference should succeed on elaborated match (#3406), got: {ty:?}"
    );
}

/// #3406: Even a simple wildcard match on a nested inductive should work.
#[test]
fn test_match_nested_inductive_value_wildcard() {
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let env = make_value_env();
    let scrutinee = SurfaceExpr::Ident(Span::dummy(), "v".to_string());
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(scrutinee),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(
                    "Value.int".to_string(),
                    vec![SurfacePattern::Wildcard, SurfacePattern::Wildcard],
                ),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr);
    assert!(
        result.is_ok(),
        "Wildcard match on nested inductive Value should elaborate (#3406), got: {result:?}"
    );
}

/// #3420: Wildcard match on nested inductive should NOT use sorry for
/// auxiliary minors. When a wildcard/catch-all arm exists, the elaborator
/// uses the wildcard body instead of sorry for auxiliary type constructors.
///
/// Uses `#[serial]` because `SORRY_COUNTER` is a process-global atomic that
/// other parallel tests can increment between our reset and the assertion.
#[test]
#[serial_test::serial]
fn test_3420_wildcard_match_no_sorry_for_aux_minors() {
    use clean_kernel::sorry::{reset_sorry_counter, sorry_count, synthetic_sorry_count};

    // Use with_prelude() so the full parse+register flow works.
    // make_value_env() has manually-created Nat/Bool/List but
    // lacks the prelude infrastructure for the parse+register path.
    let mut prelude_env = Environment::with_prelude();
    let value_decl_src = r"inductive Value where
        | int : Nat -> Nat -> Value
        | float : Nat -> Value
        | bool : Bool -> Value
        | ptr : Nat -> Value
        | nullPtr : Value
        | undef : Value
        | aggregate : List Value -> Value";

    let decl = parse_decl_for_elab(value_decl_src).expect("should parse Value");
    crate::elaborate_decl_and_register(&mut prelude_env, &decl).expect("should register Value");

    // Capture baseline counts AFTER inductive registration — registering
    // `Value` generates nested-inductive infrastructure that may legitimately
    // emit sorry terms unrelated to our match compilation test.
    reset_sorry_counter();
    let baseline_sorry = sorry_count();
    let baseline_synth = synthetic_sorry_count();

    let isptr_src = r"def Value.isPtr : Value -> Bool
        | Value.ptr _ => Bool.true
        | _ => Bool.false";
    let isptr_decl = parse_decl_for_elab(isptr_src).expect("should parse Value.isPtr");
    let result = crate::elaborate_decl_and_register(&mut prelude_env, &isptr_decl);
    assert!(
        result.is_ok(),
        "#3420: Value.isPtr should elaborate, got: {result:?}"
    );

    let total_sorry = sorry_count().saturating_sub(baseline_sorry);
    let synth_sorry = synthetic_sorry_count().saturating_sub(baseline_synth);
    assert_eq!(
        synth_sorry, 0,
        "#3420: Wildcard match on nested inductive should produce 0 synthetic sorry \
         (auxiliary minors should use wildcard body), got {synth_sorry} synthetic sorry \
         ({total_sorry} total)"
    );
}

/// #3420 extended: Exhaustive match (no wildcard) on nested inductive should
/// fall back to a nullary constructor of `branch_ty` (e.g., `Nat.zero`,
/// `Bool.false`) instead of sorry for the auxiliary minor premises.
#[test]
#[serial_test::serial]
fn test_3420_exhaustive_match_no_sorry_for_aux_minors() {
    use clean_kernel::sorry::{reset_sorry_counter, sorry_count, synthetic_sorry_count};

    let mut prelude_env = Environment::with_prelude();
    let value_decl_src = r"inductive Value where
        | int : Nat -> Nat -> Value
        | float : Nat -> Value
        | bool : Bool -> Value
        | ptr : Nat -> Value
        | nullPtr : Value
        | undef : Value
        | aggregate : List Value -> Value";

    let decl = parse_decl_for_elab(value_decl_src).expect("should parse Value");
    crate::elaborate_decl_and_register(&mut prelude_env, &decl).expect("should register Value");

    reset_sorry_counter();
    let baseline_sorry = sorry_count();
    let baseline_synth = synthetic_sorry_count();

    // Exhaustive match — every constructor matched, no wildcard. The
    // elaborator must synthesize aux-minor bodies of type `Nat` without
    // falling back to `sorry`. `Nat.zero` is the natural choice.
    let tag_src = r"def Value.tag : Value -> Nat
        | Value.int _ _ => 0
        | Value.float _ => 1
        | Value.bool _ => 2
        | Value.ptr _ => 3
        | Value.nullPtr => 4
        | Value.undef => 5
        | Value.aggregate _ => 6";
    let tag_decl = parse_decl_for_elab(tag_src).expect("should parse Value.tag");
    let result = crate::elaborate_decl_and_register(&mut prelude_env, &tag_decl);
    assert!(
        result.is_ok(),
        "#3420: Value.tag should elaborate, got: {result:?}"
    );

    let total_sorry = sorry_count().saturating_sub(baseline_sorry);
    let synth_sorry = synthetic_sorry_count().saturating_sub(baseline_synth);
    assert_eq!(
        synth_sorry, 0,
        "#3420: Exhaustive match on nested inductive should produce 0 synthetic sorry \
         (auxiliary minors should use nullary ctor of branch_ty), got {synth_sorry} synthetic sorry \
         ({total_sorry} total)"
    );
}

/// A nested constructor pattern is a real second dispatch. If it does not
/// cover the field type and no later same-constructor/wildcard arm supplies a
/// fallback, elaboration must fail rather than filling the missing minor with
/// `sorryAx`. A covering arm must still compile to an axiom-free term.
#[test]
#[serial_test::serial]
fn partial_nested_match_fails_closed_and_real_fallback_stays_sorry_free() {
    use clean_kernel::sorry::{reset_sorry_counter, sorry_count, synthetic_sorry_count};

    let mut env = Environment::with_prelude();
    let box_decl = parse_decl_for_elab(
        r"inductive NestedBox where
            | box : Option Nat -> NestedBox",
    )
    .expect("should parse NestedBox");
    crate::elaborate_decl_and_register(&mut env, &box_decl).expect("should register NestedBox");

    reset_sorry_counter();
    let baseline_sorry = sorry_count();
    let baseline_synth = synthetic_sorry_count();
    let partial_decl = parse_decl_for_elab(
        r"def NestedBox.partial : NestedBox -> Nat
            | .box (Option.some n) => n",
    )
    .expect("should parse partial nested match");
    let partial = crate::elaborate_decl_and_register(&mut env, &partial_decl);
    assert!(
        partial.is_err(),
        "partial nested match must fail closed, got {partial:?}"
    );
    assert_eq!(
        synthetic_sorry_count().saturating_sub(baseline_synth),
        0,
        "rejecting a partial nested match must not mint a synthetic sorry"
    );
    assert_eq!(
        sorry_count().saturating_sub(baseline_sorry),
        0,
        "rejecting a partial nested match must not mint any sorry"
    );
    assert!(
        env.get_const(&Name::from_string("NestedBox.partial"))
            .is_none(),
        "failed declaration must not be registered"
    );

    reset_sorry_counter();
    let baseline_sorry = sorry_count();
    let baseline_synth = synthetic_sorry_count();
    let total_decl = parse_decl_for_elab(
        r"def NestedBox.total : NestedBox -> Nat
            | .box (Option.some n) => n
            | .box _ => 0",
    )
    .expect("should parse covered nested match");
    crate::elaborate_decl_and_register(&mut env, &total_decl)
        .expect("real same-constructor fallback should elaborate");
    let total = env
        .get_const(&Name::from_string("NestedBox.total"))
        .and_then(|info| info.value.as_ref())
        .expect("NestedBox.total should have a value");
    assert!(
        !total.has_sorry(),
        "covered nested match must be sorry-free"
    );
    assert_eq!(
        synthetic_sorry_count().saturating_sub(baseline_synth),
        0,
        "covered nested match must not mint a synthetic sorry"
    );
    assert_eq!(
        sorry_count().saturating_sub(baseline_sorry),
        0,
        "covered nested match must not mint any sorry"
    );
}

/// Directly exercise the no-fallback nested-casesOn entry point. This guards
/// the production site that formerly minted a synthetic sorry before higher
/// level row compilation had a chance to reject a partial match.
#[test]
#[serial_test::serial]
fn nested_caseson_without_fallback_rejects_missing_minors_without_sorry() {
    use clean_kernel::sorry::{reset_sorry_counter, sorry_count, synthetic_sorry_count};

    let env = make_value_env();
    let mut ctx = ElabCtx::new(&env);
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let field = ctx.push_local("field".to_string(), bool_ty.clone());

    reset_sorry_counter();
    let baseline_sorry = sorry_count();
    let baseline_synth = synthetic_sorry_count();
    let result = ctx.wrap_with_nested_ctor_caseson(
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
        Expr::fvar(field),
        &bool_ty,
        "Bool.true",
        &nat_ty,
    );
    assert!(
        matches!(&result, Err(ElabError::NotImplemented(message))
            if message.contains("non-exhaustive nested constructor pattern")
                && message.contains("Bool.true")),
        "missing nested minor must be rejected explicitly, got {result:?}"
    );
    assert_eq!(
        synthetic_sorry_count().saturating_sub(baseline_synth),
        0,
        "no-fallback nested casesOn must not mint a synthetic sorry"
    );
    assert_eq!(
        sorry_count().saturating_sub(baseline_sorry),
        0,
        "no-fallback nested casesOn must not mint any sorry"
    );
    assert_eq!(
        ctx.locals.len(),
        1,
        "rejection must preserve the field local"
    );
    ctx.pop_local();
}

/// Auxiliary members of a nested mutual eliminator are unreachable from a
/// primary-typed major, but their motives still need inhabitants. Exercise
/// both plain and do-match lowering with result types that have no nullary
/// constructor, forcing the sound PUnit motive/minor path rather than the older
/// synthetic-sorry fallback.
#[test]
#[serial_test::serial]
fn auxiliary_punit_motives_cover_plain_and_do_matches_without_sorry() {
    use clean_kernel::sorry::{reset_sorry_counter, sorry_count, synthetic_sorry_count};

    let mut env = Environment::with_prelude();
    for source in [
        r"inductive Witness where
            | mk : Nat -> Witness",
        r"inductive PValue where
            | atom : Nat -> PValue
            | aggregate : List PValue -> PValue",
        r"abbrev TestM := Except String",
    ] {
        let decl = parse_decl_for_elab(source).expect("fixture declaration should parse");
        crate::elaborate_decl_and_register(&mut env, &decl)
            .unwrap_or_else(|err| panic!("fixture declaration should register: {err:?}"));
    }

    reset_sorry_counter();
    let baseline_sorry = sorry_count();
    let baseline_synth = synthetic_sorry_count();
    let plain_decl = parse_decl_for_elab(
        r"def PValue.toWitness : PValue -> Witness
            | .atom n => Witness.mk n
            | .aggregate _ => Witness.mk 0",
    )
    .expect("plain PUnit-motive regression should parse");
    crate::elaborate_decl_and_register(&mut env, &plain_decl)
        .expect("plain nested match should use sound PUnit aux slots");
    let plain = env
        .get_const(&Name::from_string("PValue.toWitness"))
        .and_then(|info| info.value.as_ref())
        .expect("PValue.toWitness should have a value");
    assert!(
        !plain.has_sorry(),
        "plain PUnit aux path must be sorry-free"
    );
    assert_eq!(
        synthetic_sorry_count().saturating_sub(baseline_synth),
        0,
        "plain PUnit aux path must not mint a synthetic sorry"
    );
    assert_eq!(
        sorry_count().saturating_sub(baseline_sorry),
        0,
        "plain PUnit aux path must not mint any sorry"
    );

    reset_sorry_counter();
    let baseline_sorry = sorry_count();
    let baseline_synth = synthetic_sorry_count();
    let do_decl = parse_decl_for_elab(
        r"def PValue.toWitnessM (v : PValue) : TestM Witness := do
            match v with
            | .atom n => Except.ok (Witness.mk n)
            | .aggregate _ => Except.ok (Witness.mk 0)",
    )
    .expect("do PUnit-motive regression should parse");
    crate::elaborate_decl_and_register(&mut env, &do_decl)
        .expect("do nested match should use sound PUnit aux slots");
    let do_value = env
        .get_const(&Name::from_string("PValue.toWitnessM"))
        .and_then(|info| info.value.as_ref())
        .expect("PValue.toWitnessM should have a value");
    assert!(
        !do_value.has_sorry(),
        "do PUnit aux path must be sorry-free"
    );
    assert_eq!(
        synthetic_sorry_count().saturating_sub(baseline_synth),
        0,
        "do PUnit aux path must not mint a synthetic sorry"
    );
    assert_eq!(
        sorry_count().saturating_sub(baseline_sorry),
        0,
        "do PUnit aux path must not mint any sorry"
    );
}

/// A missing constructor of the selected type is never an auxiliary minor.
/// This is especially important when the result is PUnit: before the boundary
/// was authenticated, `PUnit.unit` could type-check in both the accidentally
/// skipped primary slot and the genuine auxiliary slots, silently totalizing a
/// non-exhaustive match.
#[test]
#[serial_test::serial]
fn non_exhaustive_primary_punit_match_is_not_filled_as_auxiliary() {
    use clean_kernel::sorry::{reset_sorry_counter, sorry_count, synthetic_sorry_count};

    let mut env = Environment::with_prelude();
    let value_decl = parse_decl_for_elab(
        r"inductive BoundaryValue where
            | atom : Nat -> BoundaryValue
            | aggregate : List BoundaryValue -> BoundaryValue",
    )
    .expect("boundary fixture should parse");
    crate::elaborate_decl_and_register(&mut env, &value_decl)
        .expect("boundary fixture should register");

    reset_sorry_counter();
    let baseline_sorry = sorry_count();
    let baseline_synth = synthetic_sorry_count();
    let partial_decl = parse_decl_for_elab(
        r"def BoundaryValue.partialUnit : BoundaryValue -> PUnit
            | .atom _ => PUnit.unit",
    )
    .expect("partial PUnit match should parse");
    let result = crate::elaborate_decl_and_register(&mut env, &partial_decl);

    assert!(
        matches!(&result, Err(ElabError::NotImplemented(message))
            if message.contains("non-exhaustive or non-declaration-order primary match")
                && message.contains("BoundaryValue.aggregate")),
        "missing primary constructor must fail at the authenticated primary/aux boundary, got {result:?}"
    );
    assert!(
        env.get_const(&Name::from_string("BoundaryValue.partialUnit"))
            .is_none(),
        "failed non-exhaustive declaration must not be registered"
    );
    assert_eq!(
        synthetic_sorry_count().saturating_sub(baseline_synth),
        0,
        "primary/aux boundary rejection must not mint a synthetic sorry"
    );
    assert_eq!(
        sorry_count().saturating_sub(baseline_sorry),
        0,
        "primary/aux boundary rejection must not mint any sorry"
    );
}

/// Simple Tree (single constructor with List Tree) match should work.
/// Uses the parse+register flow for an end-to-end test.
#[test]
fn test_match_nested_tree_single_ctor() {
    let mut env = Environment::with_prelude();

    let decls = [
        r"inductive Tree where
            | node : List Tree -> Tree",
        r"def Tree.depth : Tree -> Nat
            | Tree.node _ => 0",
    ];

    for decl_src in decls {
        let decl =
            parse_decl_for_elab(decl_src).unwrap_or_else(|_| panic!("should parse: {decl_src}"));
        let result = crate::elaborate_decl_and_register(&mut env, &decl);
        assert!(
            result.is_ok(),
            "Tree match should elaborate and register (#3406), got {result:?} for:\n{decl_src}"
        );
    }

    assert!(
        env.get_const(&Name::from_string("Tree.depth")).is_some(),
        "Tree.depth should be registered"
    );
}

/// #3406 structural regression: the elaborated body of a pattern match on a
/// nested inductive must dispatch via the parent type's casesOn/rec eliminator,
/// NOT the auxiliary `_List` type. The original bug report showed the
/// elaborator resolving to `Value._List` instead of `Value`, causing the kernel
/// type checker to reject the def with a `Pi(_, Value._List, ...)` type
/// mismatch.
///
/// Existing regression tests for #3406 assert that elaboration succeeds, but
/// they do not verify HOW the match was elaborated — a regression could
/// substitute `Value._List.casesOn` and still satisfy type checking by pushing
/// the mismatch into unreachable sorry branches. This test inspects the
/// registered body directly and asserts:
///   1. `Value.casesOn` (or `.rec`/`.brecOn`) appears in the body.
///   2. `Value._List.casesOn` (or `.rec`/`.brecOn`) does NOT appear.
#[test]
fn test_3406_match_body_uses_parent_caseson_not_aux() {
    use clean_kernel::expr::ExprKind;

    let mut env = Environment::with_prelude();

    let value_decl_src = r"inductive Value where
  | int : Nat -> Nat -> Value
  | float : Nat -> Value
  | bool : Bool -> Value
  | ptr : Nat -> Value
  | nullPtr : Value
  | undef : Value
  | aggregate : List Value -> Value";
    let value_decl = parse_decl_for_elab(value_decl_src).expect("should parse Value");
    crate::elaborate_decl_and_register(&mut env, &value_decl)
        .expect("Value inductive with nested List should register");

    let isptr_decl = parse_decl_for_elab(
        r"def Value.isPtr : Value -> Bool
  | Value.ptr _ => Bool.true
  | _ => Bool.false",
    )
    .expect("should parse Value.isPtr");
    crate::elaborate_decl_and_register(&mut env, &isptr_decl)
        .expect("Value.isPtr should elaborate (#3406)");

    // Collect every Const name mentioned in the def body.
    fn collect_consts(expr: &Expr, out: &mut Vec<String>) {
        match expr.kind() {
            ExprKind::Const(name, _) => out.push(name.to_string()),
            ExprKind::App(f, a) => {
                collect_consts(f, out);
                collect_consts(a, out);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                collect_consts(ty, out);
                collect_consts(body, out);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                collect_consts(ty, out);
                collect_consts(val, out);
                collect_consts(body, out);
            }
            ExprKind::Proj(_, _, inner) => collect_consts(inner, out),
            ExprKind::MData(_, inner) => collect_consts(inner, out),
            _ => {}
        }
    }

    let info = env
        .get_const(&Name::from_string("Value.isPtr"))
        .expect("Value.isPtr should be registered");
    let body = info
        .value
        .clone()
        .expect("Value.isPtr should have a defining value (not an axiom)");

    let mut consts = Vec::new();
    collect_consts(&body, &mut consts);

    let has_parent_elim = consts
        .iter()
        .any(|n| n == "Value.casesOn" || n == "Value.rec" || n == "Value.brecOn");
    assert!(
        has_parent_elim,
        "#3406: Value.isPtr body should dispatch via Value.casesOn/rec/brecOn. \
         Consts in body: {consts:?}"
    );

    let uses_aux_elim = consts
        .iter()
        .any(|n| n == "Value._List.casesOn" || n == "Value._List.rec" || n == "Value._List.brecOn");
    assert!(
        !uses_aux_elim,
        "#3406: Value.isPtr body must NOT dispatch on the auxiliary Value._List type. \
         Consts in body: {consts:?}"
    );
}

/// Track V: a surface list literal expected at a nested-inductive auxiliary type
/// must coerce into that aux type's constructors.
///
/// For `inductive Ty | tuple : List Ty -> Ty`, the kernel eliminates the nested
/// `List Ty` into an auxiliary `Ty._List` (ctors `Ty._List.nil` / `Ty._List.cons`).
/// A surface `Ty.tuple [Ty.int, ...]` elaborates its argument as a `List Ty`
/// value (`List.cons`/`List.nil` chain), which is not defeq to `Ty._List`. The
/// structural list→aux coercion rewrites the chain into the aux constructors so
/// the def elaborates and the kernel re-checks the produced term.
#[test]
fn test_trackv_list_literal_coerces_to_nested_aux() {
    let mut env = Environment::with_prelude();

    let decls = [
        r"inductive Ty where
            | int : Ty
            | vector : Nat -> Ty -> Ty
            | tuple : List Ty -> Ty",
        // Non-empty literal with a recursive (nested) element.
        r"def tupTy : Ty := Ty.tuple [Ty.int, Ty.vector 2 Ty.int]",
        // Empty literal must coerce to the aux nil constructor.
        r"def emptyTy : Ty := Ty.tuple []",
        // A nested tuple literal: the inner list literal recursively coerces too.
        r"def nestedTy : Ty := Ty.tuple [Ty.tuple [Ty.int], Ty.int]",
    ];

    for decl_src in decls {
        let decl =
            parse_decl_for_elab(decl_src).unwrap_or_else(|_| panic!("should parse: {decl_src}"));
        let result = crate::elaborate_decl_and_register(&mut env, &decl);
        assert!(
            result.is_ok(),
            "Track V: list literal at nested-aux type should elaborate and \
             kernel-check, got {result:?} for:\n{decl_src}"
        );
    }

    for name in ["tupTy", "emptyTy", "nestedTy"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

/// Track V soundness guard: the list→aux coercion must NOT mis-coerce when the
/// list literal's elements have the wrong type. The structural rewrite keeps
/// non-recursive element fields verbatim, so a `Nat` where a `Ty` is required is
/// caught by the kernel re-check rather than silently accepted.
#[test]
fn test_trackv_wrong_element_type_still_rejected() {
    let mut env = Environment::with_prelude();

    let ty_decl = r"inductive Ty where
        | int : Ty
        | tuple : List Ty -> Ty";
    let decl = parse_decl_for_elab(ty_decl).expect("should parse Ty");
    crate::elaborate_decl_and_register(&mut env, &decl).expect("should register Ty");

    // `[42]` puts a Nat element where a Ty is required; must be rejected.
    let bad_src = r"def bad : Ty := Ty.tuple [42]";
    let bad_decl = parse_decl_for_elab(bad_src).expect("should parse bad");
    let result = crate::elaborate_decl_and_register(&mut env, &bad_decl);
    assert!(
        result.is_err(),
        "Track V: a list literal with a wrong-typed element must be rejected, \
         not silently coerced; got {result:?}"
    );
}

/// Track V regression guard: ordinary `List` values must be unaffected by the
/// list→aux coercion. A plain `List Nat` literal and explicit `List.cons` usage
/// must continue to elaborate at type `List Nat`.
#[test]
fn test_trackv_plain_list_unaffected() {
    let mut env = Environment::with_prelude();

    let decls = [
        r"def xs : List Nat := [1, 2, 3]",
        r"def ys : List Nat := List.cons 0 xs",
        r"def zs : List Nat := []",
    ];

    for decl_src in decls {
        let decl =
            parse_decl_for_elab(decl_src).unwrap_or_else(|_| panic!("should parse: {decl_src}"));
        let result = crate::elaborate_decl_and_register(&mut env, &decl);
        assert!(
            result.is_ok(),
            "Track V: plain List usage must be unaffected by the aux coercion, \
             got {result:?} for:\n{decl_src}"
        );
    }
}

/// Track VV — a *nested constructor pattern* whose inner argument is itself a
/// constructor pattern, matched on a NESTED-AUX inductive, returning a
/// structured result. This is the shape of trust-ir's
/// `Ty.executableIntVectorWidth?` (`.Vector 16 .I8 => some (16, 8)`).
///
/// `Ty` has `Tuple : List Ty`, so elimination creates the aux `Ty._List`, and
/// `Ty.casesOn` carries TWO motives + minors for every constructor across the
/// block. The inner `.I8` constructor pattern lowers through
/// `wrap_with_nested_ctor_caseson_with_fallback`, which previously supplied only
/// the primary motive and primary minors — leaving the aux motive slot filled by
/// the next supplied minor, so the kernel saw `Option (Nat × Nat)` where
/// `Ty._List → Sort` was expected. After the fix the wrapper supplies the aux
/// motive and aux-constructor fallback minors, and the def elaborates and
/// kernel-checks (the produced term is re-checked by `add_decl`).
#[test]
fn test_trackvv_nested_ctor_pattern_on_nested_aux_inductive() {
    let mut env = Environment::with_prelude();

    let decls = [
        r"inductive Ty where
            | I8 : Ty
            | I16 : Ty
            | Bool : Ty
            | Vector : Nat -> Ty -> Ty
            | Tuple : List Ty -> Ty",
        // Literal lane count + nested inner constructor, structured result
        // (the exact executableIntVectorWidth? shape).
        r"def Ty.execWidth? : Ty -> Option (Nat × Nat)
            | .Vector 16 .I8 => some (16, 8)
            | .Vector 8 .I16 => some (8, 16)
            | _ => none",
        // Bool-lane variant (executableBoolVectorLanes? shape).
        r"def Ty.boolLanes? : Ty -> Option Nat
            | .Vector 16 .Bool => some 16
            | .Vector 4 .Bool => some 4
            | _ => none",
    ];

    for decl_src in decls {
        let decl =
            parse_decl_for_elab(decl_src).unwrap_or_else(|_| panic!("should parse: {decl_src}"));
        let result = crate::elaborate_decl_and_register(&mut env, &decl);
        assert!(
            result.is_ok(),
            "Track VV: nested-ctor pattern on a nested-aux inductive must \
             elaborate and kernel-check, got {result:?} for:\n{decl_src}"
        );
    }

    for name in ["Ty.execWidth?", "Ty.boolLanes?"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }

    // PERF ROOT FIX (trk-yy) structural guard. The nested-ctor fallback wrapper
    // (`wrap_with_nested_ctor_caseson_with_fallback`) used to splat the accumulated
    // `fallback` branch into EVERY non-matching minor. With `Ty` carrying ~5
    // constructors plus the aux `Ty._List` block, that duplicated the fallback far
    // more than once per `casesOn` level, and the literal-lane + inner-ctor nesting
    // compounded it — making the term exponential when walked as a tree (whnf /
    // def-eq / infer_type / the debug ProofCert tree blow up to heartbeat/OOM).
    //
    // The fix lifts the duplicated fallback into ONE shared `let fb := <fallback> in
    // <casesOn … fb …>` binder, so the fallback appears once syntactically and the
    // term is linear-as-tree. This must be semantically transparent (the `let`
    // zeta-reduces to the inlined form and the kernel re-checks it — which it did
    // above, since elaboration + `add_decl` succeeded).
    //
    // Assert at least one `Let` binder is present in `Ty.execWidth?`'s body: the
    // shared-fallback lift. Without the fix the body has NO such `let` (the
    // fallback is inlined and duplicated). This catches a regression that reverts to
    // the exponential duplication even if it still type-checks.
    {
        use clean_kernel::expr::ExprKind;

        fn count_lets(expr: &Expr) -> usize {
            match expr.kind() {
                ExprKind::Let(_, ty, val, body, _) => {
                    1 + count_lets(ty) + count_lets(val) + count_lets(body)
                }
                ExprKind::App(f, a) => count_lets(f) + count_lets(a),
                ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                    count_lets(ty) + count_lets(body)
                }
                ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => count_lets(inner),
                _ => 0,
            }
        }

        let info = env
            .get_const(&Name::from_string("Ty.execWidth?"))
            .expect("Ty.execWidth? should be registered");
        let body = info
            .value
            .clone()
            .expect("Ty.execWidth? should have a defining value (not an axiom)");
        assert!(
            count_lets(&body) >= 1,
            "trk-yy perf root fix: the nested-ctor fallback must be let-shared \
             (>= 1 `let` binder lifting the duplicated fallback out of the casesOn); \
             found none, so the fallback is being inlined+duplicated again \
             (exponential-as-tree). Body: {body:?}"
        );
    }
}

/// Error recovery must not retain the let-sharing placeholder used while
/// building nested constructor fallbacks. Restored recursor metadata comes
/// from imported/trusted environment state, so diagnose a malformed field
/// count without contaminating the elaborator's local context for the next
/// declaration.
#[test]
fn malformed_restored_nested_minor_does_not_leak_fallback_local() {
    let env = make_value_env();
    let mut json: clean_kernel::env::JsonEnvironment =
        serde_json::from_str(&env.to_json().expect("serialize Value environment"))
            .expect("decode editable JSON environment");
    let value_rec = json
        .recursors
        .iter_mut()
        .find(|rec| rec.name == Name::from_string("Value.rec"))
        .expect("Value.rec metadata");
    let float_rule = value_rec
        .rules
        .iter_mut()
        .find(|rule| rule.constructor_name == Name::from_string("Value.float"))
        .expect("Value.float recursor rule");
    assert_eq!(float_rule.num_fields, 1, "fixture field count");
    float_rule.num_fields = 2;
    let env = Environment::from_json(
        &serde_json::to_string(&json).expect("encode malformed test environment"),
    )
    .expect("load malformed test environment without validation");

    let value_ty = Expr::const_(Name::from_string("Value"), vec![]);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let matching_int_minor = Expr::lam(
        BinderInfo::Default,
        nat_ty.clone(),
        Expr::lam(BinderInfo::Default, nat_ty.clone(), nat_zero.clone()),
    );

    let mut ctx = ElabCtx::new(&env);
    let major = ctx.push_local("major".to_string(), value_ty.clone());
    let locals_before = ctx.locals.len();
    let result = ctx.wrap_with_nested_ctor_caseson_with_fallback(
        matching_int_minor,
        Expr::fvar(major),
        &value_ty,
        "Value.int",
        &nat_ty,
        nat_zero,
    );

    assert!(
        matches!(&result, Err(ElabError::InternalInvariant(message))
            if message.contains("Value.rec")
                && message.contains("Value.float")
                && message.contains("num_fields=2")),
        "malformed restored minor must fail with the field-telescope diagnostic, got {result:?}"
    );
    assert_eq!(
        ctx.locals.len(),
        locals_before,
        "nested fallback placeholder must be removed on every error path"
    );
    assert!(
        ctx.locals
            .iter()
            .all(|(name, _, _)| name != "_nested_fallback"),
        "error recovery must not retain the internal fallback local"
    );

    // Applying a plan pops its nested field locals before the fallible
    // telescope validation above.  A failed application must reconstruct that
    // exact entry stack so its caller can either retry or clean the plan up.
    let plan = ctx
        .bind_nested_pattern_plan(
            "transaction regression",
            &SurfacePattern::Ctor(
                "Value.int".to_string(),
                vec![
                    SurfacePattern::Var("a".to_string()),
                    SurfacePattern::Var("b".to_string()),
                ],
            ),
            Expr::fvar(major),
            &value_ty,
        )
        .expect("valid nested pattern should bind a plan");
    let locals_before_apply = ctx.locals.clone();
    let apply_result = ctx.apply_nested_pattern_plan(
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
        &plan,
        &nat_ty,
        Some(&Expr::const_(Name::from_string("Nat.zero"), vec![])),
    );
    assert!(
        matches!(&apply_result, Err(ElabError::InternalInvariant(message))
            if message.contains("Value.rec")
                && message.contains("Value.float")
                && message.contains("num_fields=2")),
        "malformed restored minor must fail after plan fields are visited, got {apply_result:?}"
    );
    assert_eq!(
        ctx.locals, locals_before_apply,
        "failed nested-plan application must restore already-popped locals exactly"
    );
    ctx.cleanup_nested_field_plans(std::slice::from_ref(&plan));
    assert_eq!(ctx.locals.len(), locals_before);
    let major_again = ctx
        .elaborate(&SurfaceExpr::Ident(
            clean_parser::Span::dummy(),
            "major".to_string(),
        ))
        .expect("same ElabCtx must remain usable after failed plan application");
    assert_eq!(major_again, Expr::fvar(major));
}

/// Binding a nested plan can fail after both an `As` alias and constructor
/// fields have been pushed.  The entire binding transaction — locals,
/// expected type, recursive IH map, dependent-motive context and metavariable
/// scope — must roll back before the same `ElabCtx` is reused.
#[test]
fn malformed_nested_subpattern_restores_complete_elab_context() {
    let env = make_value_env();
    let mut ctx = ElabCtx::new(&env);
    let value_ty = Expr::const_(Name::from_string("Value"), vec![]);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let sentinel = ctx.push_local("sentinel".to_string(), nat_ty.clone());
    let major = ctx.push_local("major".to_string(), value_ty.clone());

    ctx.current_expected_type = Some(nat_ty.clone());
    ctx.match_dependent_motive = Some(Expr::bvar(0));
    ctx.match_dependent_motive_indices = 1;
    ctx.match_index_discriminating_punit = Some(Level::zero());
    ctx.recursive_def_ctx = Some(RecursiveDefContext {
        func_name: "Value.audit".to_string(),
        decreasing_arg_pos: 0,
        decreasing_arg_name: "major".to_string(),
        inductive_type_name: Some(Name::from_string("Value")),
        ih_fvar: Some(sentinel),
        ih_type: Some(nat_ty.clone()),
        ih_map: HashMap::from([("major".to_string(), sentinel)]),
        sibling_names: vec!["Value.auditSibling".to_string()],
        extra_params: Vec::new(),
        wf_measure: None,
    });

    let locals_before = ctx.locals.clone();
    let let_values_before = ctx.local_let_values.clone();
    let local_instances_before = ctx.local_instances.clone();
    let cache_before = ctx.instance_cache.clone();
    let expected_before = ctx.current_expected_type.clone();
    let recursive_before = format!("{:?}", ctx.recursive_def_ctx);
    let motive_before = ctx.match_dependent_motive.clone();
    let motive_indices_before = ctx.match_dependent_motive_indices;
    let punit_before = ctx.match_index_discriminating_punit.clone();
    let universes_before = ctx.universe_params.clone();
    let pending_levels_before = ctx.pending_level_assigns.borrow().clone();
    let meta_scope_depth_before = ctx.metas.scope_depth();

    let malformed = SurfacePattern::Ctor(
        "Value.int".to_string(),
        vec![
            SurfacePattern::As("alias".to_string(), Box::new(SurfacePattern::Wildcard)),
            SurfacePattern::Or(
                Box::new(SurfacePattern::Wildcard),
                Box::new(SurfacePattern::Wildcard),
            ),
        ],
    );
    let result = ctx.with_local_scope_rollback(|this| {
        // Exercise the failure-only portions of the checkpoint as part of the
        // same malformed-pattern transaction. Fresh universe IDs remain
        // monotone, but neither the declaration's parameter packet nor pending
        // level-equality callback assignments may leak out of the failed arm.
        let leaked_level = this.fresh_universe_param();
        this.pending_level_assigns
            .borrow_mut()
            .push((Name::from_string("transaction_pending"), leaked_level));
        this.bind_nested_pattern_plan(
            "transaction regression",
            &malformed,
            Expr::fvar(major),
            &value_ty,
        )
    });
    let result_summary = match &result {
        Ok(_) => "Ok(NestedPatternPlan)".to_string(),
        Err(error) => format!("Err({error:?})"),
    };
    assert!(
        matches!(&result, Err(ElabError::NotImplemented(message)) if message.contains("nested constructor field pattern") && message.contains("Or")),
        "malformed nested subpattern should report the exact unsupported-pattern boundary, got {result_summary}"
    );

    assert_eq!(
        ctx.locals, locals_before,
        "local stack changed after rollback"
    );
    assert_eq!(ctx.local_let_values, let_values_before);
    assert_eq!(ctx.local_instances, local_instances_before);
    assert_eq!(ctx.instance_cache, cache_before);
    assert_eq!(ctx.current_expected_type, expected_before);
    assert_eq!(format!("{:?}", ctx.recursive_def_ctx), recursive_before);
    assert_eq!(ctx.match_dependent_motive, motive_before);
    assert_eq!(ctx.match_dependent_motive_indices, motive_indices_before);
    assert_eq!(ctx.match_index_discriminating_punit, punit_before);
    assert_eq!(ctx.universe_params, universes_before);
    assert_eq!(
        *ctx.pending_level_assigns.borrow(),
        pending_levels_before,
        "failed nested arm leaked pending level assignments"
    );
    assert_eq!(ctx.metas.scope_depth(), meta_scope_depth_before);

    let sentinel_again = ctx
        .elaborate(&SurfaceExpr::Ident(
            clean_parser::Span::dummy(),
            "sentinel".to_string(),
        ))
        .expect("same ElabCtx must elaborate after malformed nested subpattern");
    assert_eq!(sentinel_again, Expr::fvar(sentinel));
}
