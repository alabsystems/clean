// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Equality through the real width-generic BitVec and Fin carriers.
use clean_elab::{
    elaborate_decl_and_register, prepare_session_environment, preprocess_decl_with_context,
    ElabResult, FileContext,
};
use clean_kernel::{reference::ReferenceKernel, Declaration, Environment, Expr, Name};
use clean_parser::parse_file;

const POSITIVE: &str = r"
theorem bitvec_values_determine_equality (w : Nat) (x y : BitVec w) (h : x.toNat = y.toNat) : x = y := BitVec.eq_of_toNat_eq h
theorem bitvec_reflexive (w : Nat) (x : BitVec w) : x = x := BitVec.eq_of_toNat_eq (by rfl)
theorem width_zero_equality (x y : BitVec 0) (h : x.toNat = y.toNat) : x = y := BitVec.eq_of_toNat_eq h
theorem width_one_equality (x y : BitVec 1) (h : x.toNat = y.toNat) : x = y := BitVec.eq_of_toNat_eq h
theorem width_65_equality (x y : BitVec 65) (h : x.toNat = y.toNat) : x = y := BitVec.eq_of_toNat_eq h
theorem width_128_equality (x y : BitVec 128) (h : x.toNat = y.toNat) : x = y := BitVec.eq_of_toNat_eq h
theorem zero_width_constants : BitVec.ofNat 0 0 = BitVec.ofNat 0 7 := BitVec.eq_of_toNat_eq (by decide)
theorem byte_wrap_constants : BitVec.ofNat 8 255 = BitVec.ofNat 8 511 := BitVec.eq_of_toNat_eq (by decide)
";

fn failed(result: &ElabResult) -> bool {
    match result {
        ElabResult::Failed { .. } => true,
        ElabResult::Multiple(xs) => xs.iter().any(failed),
        _ => false,
    }
}
fn register(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut context = FileContext::new();
    for declaration in parse_file(source).map_err(|error| format!("{error:?}"))? {
        let declaration = preprocess_decl_with_context(&declaration, &mut context);
        let result =
            elaborate_decl_and_register(env, &declaration).map_err(|error| error.to_string())?;
        if failed(&result) {
            return Err(format!("{result:?}"));
        }
    }
    Ok(())
}
fn environment() -> Environment {
    let mut env = Environment::with_prelude();
    prepare_session_environment(&mut env);
    env
}

#[test]
fn actual_bitvec_extensionality_source_replays_without_axioms() {
    let mut env = environment();
    register(&mut env, POSITIVE).expect("actual generic BitVec source");
    let mut reference = ReferenceKernel::new(env).expect("source provenance");
    for name in [
        "bitvec_values_determine_equality",
        "bitvec_reflexive",
        "width_zero_equality",
        "width_one_equality",
        "width_65_equality",
        "width_128_equality",
        "zero_width_constants",
        "byte_wrap_constants",
    ] {
        let original = Name::from_string(name);
        let info = reference
            .environment()
            .get_const(&original)
            .expect("actual source theorem");
        assert!(info.level_params.is_empty());
        let type_ = info.type_.clone();
        let alias = Name::from_string(&format!("source_reference_{name}"));
        reference
            .add_checked(Declaration::Theorem {
                name: alias.clone(),
                level_params: vec![],
                type_,
                value: Expr::const_(original, vec![]),
            })
            .expect("replay actual source proof closure");
        assert!(reference
            .environment()
            .axiom_deps(&alias)
            .expect("closure")
            .is_empty());
    }
}

#[test]
fn source_refuses_original_extensionality_proof_for_extra_unit() {
    let mut env = environment();
    let before = (env.num_constants(), env.num_instances());
    let source = "theorem bad_bitvec_ext (w : Nat) (x y : BitVec w) (h : x.toNat = y.toNat) : x = y + 1 := BitVec.eq_of_toNat_eq h";
    assert!(register(&mut env, source).is_err());
    assert!(env
        .get_const(&Name::from_string("bad_bitvec_ext"))
        .is_none());
    assert_eq!((env.num_constants(), env.num_instances()), before);
}

#[test]
fn source_refuses_false_values_and_mixed_width_equality() {
    for source in [
        "theorem bad_bitvec_ext : BitVec.ofNat 8 0 = BitVec.ofNat 8 1 := BitVec.eq_of_toNat_eq (by decide)",
        "theorem bad_bitvec_ext (x : BitVec 8) (y : BitVec 16) (h : x.toNat = y.toNat) : x = y := BitVec.eq_of_toNat_eq h",
    ] {
        let mut env = environment();
        let before = (env.num_constants(), env.num_instances());
        assert!(
            register(&mut env, source).is_err(),
            "false source: {source}"
        );
        assert!(
            env.get_const(&Name::from_string("bad_bitvec_ext"))
                .is_none()
        );
        assert_eq!((env.num_constants(), env.num_instances()), before);
    }
}
