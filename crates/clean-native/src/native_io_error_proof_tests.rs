// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::env::{Declaration, KernelTheory};
use clean_kernel::{BinderInfo, Environment, Expr, LeanWorld, Level, Name, TypeChecker};
use clean_olean::{ConstantKind, RuntimeBody, RuntimeOleanInput};
use std::path::PathBuf;
use std::sync::Arc;

fn statement(function: &str) -> Expr {
    let code = Expr::bvar(0);
    let nat = Expr::app(Expr::const_str("UInt32.toNat"), code.clone());
    let word = Expr::app(Expr::const_str("UInt32.toUSize"), code);
    Expr::pi(
        BinderInfo::Default,
        Expr::const_str("UInt32"),
        Expr::apps(
            Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
            [
                Expr::const_str("String"),
                Expr::app(Expr::const_str(function), nat),
                Expr::app(Expr::const_str("USize.repr"), word),
            ],
        ),
    )
}

#[test]
#[ignore = "requires the official CLEAN_LEAN436_BIN and CLEAN_LEAN436_LIB"]
fn checked_uint32_error_decimal_equations_replay_in_both_kernels() {
    let lib = PathBuf::from(std::env::var_os("CLEAN_LEAN436_LIB").unwrap());
    let reference = std::env::var_os("CLEAN_LEAN436_BIN").unwrap();
    let directory = tempfile::tempdir().unwrap();
    let source = include_str!("../tests/fixtures/stable_io_error_uint32.lean");
    std::fs::write(directory.path().join("UInt32ErrorDecimal.lean"), source).unwrap();
    let checked = std::process::Command::new(reference)
        .current_dir(directory.path())
        .args(["-o", "UInt32ErrorDecimal.olean", "UInt32ErrorDecimal.lean"])
        .output()
        .unwrap();
    assert!(checked.status.success(), "{:?}", checked);
    let axioms = String::from_utf8(checked.stdout).unwrap();
    for name in ["errorCodeRepr", "errorCodeReprFast"] {
        assert!(axioms
            .lines()
            .any(|line| line == format!("'{name}' depends on axioms: [propext]")));
    }

    let mut env = Environment::for_lean_replay();
    env.set_kernel_theory(KernelTheory::Lean);
    clean_olean::declare_environment_world(&mut env, LeanWorld::Lean436.tag()).unwrap();
    let deps = [
        "Init",
        "Init.Data.Repr",
        "Init.Data.UInt.Lemmas",
        "Init.Data.Array.Lemmas",
        "Init.Data.List.Range",
    ]
    .map(str::to_owned);
    clean_olean::load_modules_with_deps(&mut env, &deps, &[lib]).unwrap();
    let bytes = std::fs::read(directory.path().join("UInt32ErrorDecimal.olean")).unwrap();
    let input = RuntimeOleanInput {
        label: "UInt32ErrorDecimal.olean".into(),
        bytes: Arc::from(bytes),
    };
    let parts = clean_olean::extract_olean_runtime_parts(input, None, None);
    assert_eq!(parts.len(), 1);
    assert!(parts[0].error.is_none());
    for (target, nat_repr) in [
        ("errorCodeReprFast", "Nat.reprFast"),
        ("errorCodeRepr", "Nat.repr"),
    ] {
        let target = Name::interned(target);
        assert!(env.get_const(&target).is_none());
        let row = parts[0]
            .rows
            .iter()
            .map(|r| r.declaration.as_ref().unwrap())
            .find(|r| r.name == target)
            .unwrap();
        assert_eq!(row.kind, ConstantKind::Theorem);
        assert!(row.represented_fields_complete);
        let RuntimeBody::Stored(Ok(proof)) = &row.body else {
            panic!("missing original proof")
        };
        let ty = row.type_.as_ref().unwrap();
        let mut used = std::collections::HashSet::new();
        for expr in [proof, ty] {
            expr.used_constants_dag(
                clean_kernel::expr::UsedConstants::WithProjectionStructures,
                &mut used,
            );
        }
        assert!(!used.contains(&target) && !used.contains(&Name::interned("sorryAx")));
        assert!(TypeChecker::new(&env).is_def_eq(ty, &statement(nat_repr)));
        let declaration = |value| Declaration::Theorem {
            name: target.clone(),
            level_params: row.level_params.clone(),
            type_: ty.clone(),
            value,
        };
        env.check_decl_readonly_strict(&declaration(proof.clone()))
            .unwrap();
        assert!(env
            .check_decl_readonly_strict(&declaration(Expr::nat_lit(0)))
            .is_err());
    }
}
