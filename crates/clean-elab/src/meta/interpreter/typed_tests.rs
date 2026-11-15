// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::{FVarId, Level, MDataValue};
use clean_parser::SurfaceName;

fn marker() -> (Name, MDataValue) {
    (
        Name::anon().str("qq_runtime_check_v2"),
        MDataValue::Bool(true),
    )
}

fn row(name: Name, id: FVarId) -> (Name, MDataValue) {
    (
        SurfaceName::generated_path("qq_binding_v2")
            .append(&SurfaceName::from_name(name))
            .into_name(),
        MDataValue::Nat(id.as_u64()),
    )
}

fn pair(left: Expr, right: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::anon().str("Prod").str("mk"), vec![]),
            left,
        ),
        right,
    )
}

fn placeholder(name: Name) -> Expr {
    Expr::mdata(
        vec![(
            Name::anon().str("qq_runtime_binding_v2"),
            MDataValue::Name(name),
        )],
        Expr::prop(),
    )
}

#[test]
fn typed_binding_keys_preserve_quoted_numeric_and_reserved_twins() {
    let names = [
        Name::anon().str("x.dot"),
        Name::anon().str("x").str("dot"),
        Name::anon().str("7"),
        Name::anon().num(7),
    ];
    for name in &names {
        assert_eq!(
            RuntimeInterpreter::typed_binding_key(&row(name.clone(), FVarId::new(0)).0),
            Some(name.clone())
        );
    }
    assert_eq!(
        RuntimeInterpreter::typed_binding_key(&Name::anon().str("qq_binding_v2.x")),
        None
    );
    assert_eq!(
        RuntimeInterpreter::typed_binding_key(&Name::anon().str("qq_binding_v2")),
        None
    );
    assert_eq!(
        RuntimeInterpreter::typed_binding_key(&Name::anon().str("qq_binding_x")),
        None
    );
}

#[test]
fn typed_bindings_retain_all_exact_names_and_never_populate_legacy_map() {
    let env = Environment::default();
    let mut interpreter = RuntimeInterpreter::new(&env);
    let names = [
        Name::anon().str("x.dot"),
        Name::anon().str("x").str("dot"),
        Name::anon().str("7"),
        Name::anon().num(7),
    ];
    let mut metadata = vec![marker()];
    let mut values = Vec::new();
    for (i, name) in names.iter().enumerate() {
        let mut level = Level::zero();
        for _ in 0..i {
            level = Level::succ(level);
        }
        let meta = interpreter
            .meta_ctx_mut()
            .metas_mut()
            .fresh(Expr::sort(Level::succ(level.clone())));
        let value = Expr::sort(level);
        interpreter
            .meta_ctx_mut()
            .metas_mut()
            .assign(meta, value.clone());
        metadata.push(row(name.clone(), MetaState::to_fvar(meta)));
        values.push(value);
    }
    let check = Expr::mdata(metadata, pair(Expr::prop(), Expr::prop()));
    assert!(
        matches!(interpreter.interpret(&check), RuntimeInterpretResult::Value(value) if value == Expr::const_(Name::anon().str("Bool").str("true"), vec![]))
    );
    assert_eq!(interpreter.typed_bindings().len(), 4);
    assert!(interpreter.bindings().is_empty());
    for (name, expected) in names.into_iter().zip(values) {
        assert!(
            matches!(interpreter.interpret(&placeholder(name)), RuntimeInterpretResult::Value(value) if value == expected)
        );
    }
}

#[test]
fn typed_check_performs_real_metavariable_unification() {
    let env = Environment::default();
    let mut interpreter = RuntimeInterpreter::new(&env);
    let meta = interpreter.meta_ctx_mut().metas_mut().fresh(Expr::type_());
    let id = MetaState::to_fvar(meta);
    let name = Name::anon().str("v.dot");
    let check = Expr::mdata(
        vec![marker(), row(name.clone(), id)],
        pair(Expr::prop(), Expr::fvar(id)),
    );
    assert!(matches!(
        interpreter.interpret(&check),
        RuntimeInterpretResult::Value(_)
    ));
    assert_eq!(interpreter.typed_bindings().get(&name), Some(&Expr::prop()));
}

#[test]
fn malformed_duplicate_remapped_and_legacy_mixed_rows_refuse_atomically() {
    let env = Environment::default();
    let mut interpreter = RuntimeInterpreter::new(&env);
    let meta = interpreter.meta_ctx_mut().metas_mut().fresh(Expr::type_());
    interpreter
        .meta_ctx_mut()
        .metas_mut()
        .assign(meta, Expr::prop());
    let binding = row(Name::anon().str("x"), MetaState::to_fvar(meta));
    let invalid = [
        vec![marker(), marker(), binding.clone()],
        vec![marker(), binding.clone(), binding.clone()],
        vec![
            marker(),
            binding.clone(),
            row(Name::anon().str("y"), MetaState::to_fvar(meta)),
        ],
        vec![
            marker(),
            (binding.0.clone(), MDataValue::Name(Name::anon())),
        ],
        vec![
            marker(),
            (Name::anon().str("qq_binding_x"), binding.1.clone()),
        ],
        vec![
            marker(),
            (Name::anon().str("qq_runtime_check"), MDataValue::Bool(true)),
        ],
        vec![(marker().0, MDataValue::Bool(false)), binding.clone()],
        vec![marker(), row(Name::anon().str("x"), FVarId::new(0))],
    ];
    for metadata in invalid {
        interpreter
            .typed_bindings
            .insert(Name::anon().str("stale"), Expr::prop());
        let check = Expr::mdata(metadata, pair(Expr::prop(), Expr::prop()));
        assert!(
            matches!(interpreter.interpret(&check), RuntimeInterpretResult::NotInterpreted(value) if value == check)
        );
        assert!(interpreter.typed_bindings().is_empty());
    }
}

#[test]
fn missing_assignments_and_wrong_placeholder_payload_do_not_use_stale_or_legacy_values() {
    let env = Environment::default();
    let mut interpreter = RuntimeInterpreter::new(&env);
    let meta = interpreter.meta_ctx_mut().metas_mut().fresh(Expr::type_());
    let name = Name::anon().str("x");
    interpreter.bindings.insert("x".to_owned(), Expr::prop());
    let check = Expr::mdata(
        vec![marker(), row(name.clone(), MetaState::to_fvar(meta))],
        pair(Expr::prop(), Expr::prop()),
    );
    assert!(matches!(
        interpreter.interpret(&check),
        RuntimeInterpretResult::NotInterpreted(_)
    ));
    assert!(matches!(
        interpreter.interpret(&placeholder(name)),
        RuntimeInterpretResult::NotInterpreted(_)
    ));
    let wrong = Expr::mdata(
        vec![(
            Name::anon().str("qq_runtime_binding_v2"),
            MDataValue::String(Arc::from("x")),
        )],
        Expr::prop(),
    );
    assert!(
        matches!(interpreter.interpret(&wrong), RuntimeInterpretResult::NotInterpreted(value) if value == wrong)
    );
    assert_eq!(interpreter.bindings().get("x"), Some(&Expr::prop()));
}

#[test]
fn typed_metadata_population_and_name_budgets_refuse() {
    let env = Environment::default();
    let mut interpreter = RuntimeInterpreter::new(&env);
    let check = Expr::mdata(vec![marker(); 4098], pair(Expr::prop(), Expr::prop()));
    assert!(
        matches!(interpreter.interpret(&check), RuntimeInterpretResult::NotInterpreted(value) if value == check)
    );
    let mut deep = Name::anon().str("qq_binding_v2");
    for _ in 0..256 {
        deep = deep.str("a");
    }
    assert_eq!(RuntimeInterpreter::typed_binding_key(&deep), None);
    let long = Name::anon().str("qq_binding_v2").str("x".repeat(65537));
    assert_eq!(RuntimeInterpreter::typed_binding_key(&long), None);
}
