// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, FileContext,
};
use clean_kernel::{Environment, Name};

fn check(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file = FileContext::new();
    for decl in clean_parser::parse_file(source).map_err(|err| format!("{err:?}"))? {
        let decl = preprocess_decl_with_context(&decl, &mut file);
        elaborate_decl_and_register_with_context(&mut env, &decl, &mut file)
            .map_err(|err| err.to_string())?;
    }
    Ok(env)
}

#[test]
fn standalone_decision_agrees_with_the_field_values() {
    let source = "structure Boxed where\n  value : Nat\ndef sep := 0\n\
                  deriving instance DecidableEq for Boxed\n";
    let proposition = "theorem decision : decide (Boxed.mk 7 = Boxed.mk 8) = false := rfl";
    let env = check(&format!("{source}{proposition}")).expect("different fields decide false");
    assert!(env
        .get_const(&Name::from_string("instDecidableEqBoxed"))
        .is_some());
    assert!(check(&format!("{source}{}", proposition.replace("false", "true"))).is_err());
}

#[test]
fn standalone_deriving_requires_known_targets_and_handlers() {
    assert!(check("deriving instance DecidableEq for MissingType").is_err());
    assert!(check("deriving instance MissingClass for Nat").is_err());
}

#[test]
fn module_batch_uses_derived_instances_in_later_proofs() {
    use clean_elab::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};

    let source = "structure Wrapped where\n  data : Nat\ndef sep := 0\n\
                  deriving instance DecidableEq for Wrapped\n\
                  theorem yes : decide (Wrapped.mk 3 = Wrapped.mk 4) = false := rfl";
    let decls = clean_parser::parse_file(source).expect("command parses");
    let mut env = Environment::with_prelude();
    let result = elaborate_module(
        &mut env,
        &mut FileContext::new(),
        &[SourceUnit {
            id: UnitId(0),
            decls: &decls,
        }],
        BatchOptions::islands(),
    );
    assert!(result.is_clean(), "{:?}", result.all_rejections());
    assert!(env.get_const(&Name::from_string("yes")).is_some());
}

#[test]
fn derives_a_second_instance_under_the_current_namespace() {
    let env = check(
        "namespace Cases\nstructure Wrapper where\n  data : Nat\nend Cases\n\
         namespace Other\n\
         deriving instance DecidableEq for Cases.Wrapper\n\
         deriving instance DecidableEq for Cases.Wrapper\n\
         end Other",
    )
    .expect("instances get distinct names in the command namespace");
    for name in [
        "Other.instDecidableEqWrapper",
        "Other.instDecidableEqWrapper_1",
    ] {
        assert!(env.get_const(&Name::from_string(name)).is_some(), "{name}");
    }
}

#[test]
fn delta_deriving_reuses_the_unfolded_types_instance() {
    let source = "def DeriveAlias := Nat\n\
                  deriving instance DecidableEq for DeriveAlias\n\
                  theorem result : decide ((Nat.zero : DeriveAlias) = Nat.succ Nat.zero) = false := rfl";
    let env = check(source).expect("definition uses the instance of its unfolded type");
    assert!(env
        .get_const(&Name::from_string("instDecidableEqDeriveAlias"))
        .is_some());
    assert!(check(&source.replace("= false", "= true")).is_err());
}

#[test]
fn delta_deriving_preserves_the_definitions_parameters_and_local_instance() {
    let env = check(
        "def ConstantRange (_ : Type u) := Nat\nderiving instance DecidableEq for ConstantRange\n\
         theorem agrees (α : Type u) : decide ((Nat.zero : ConstantRange α) = Nat.zero) = true := rfl\n\
         def Like (α : Type u) [DecidableEq α] := α\nderiving instance DecidableEq for Like"
    ).expect("definition parameters and their instances remain available");
    assert!(env
        .get_const(&Name::from_string("instDecidableEqLike"))
        .is_some());
    assert!(check("def Like (α : Type u) := α\nderiving instance DecidableEq for Like").is_err());
}
