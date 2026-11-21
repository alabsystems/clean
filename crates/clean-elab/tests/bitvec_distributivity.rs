// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Distributivity for the actual generic and wrapped BitVec operations.
use clean_elab::{
    elaborate_decl_and_register, prepare_session_environment, preprocess_decl_with_context,
    ElabResult, FileContext,
};
use clean_kernel::{reference::ReferenceKernel, Declaration, Environment, Expr, Name};
use clean_parser::parse_file;

const POSITIVE: &str = r"
theorem right_distributivity (w : Nat) (x y z : BitVec w) : (x + y) * z = x * z + y * z := BitVec.add_mul
theorem left_distributivity (w : Nat) (x y z : BitVec w) : x * (y + z) = x * y + x * z := BitVec.mul_add
theorem edge_update {w : Nat} (iv step stride : BitVec w) : iv * stride + step * stride = (iv + step) * stride := by exact BitVec.add_mul.symm
theorem zero_width_distributivity (x y z : BitVec 0) : (x + y) * z = x * z + y * z := BitVec.add_mul
theorem one_width_distributivity (x y z : BitVec 1) : x * (y + z) = x * y + x * z := BitVec.mul_add
theorem width_65_distributivity (x y z : BitVec 65) : (x + y) * z = x * z + y * z := BitVec.add_mul
theorem width_128_distributivity (x y z : BitVec 128) : x * (y + z) = x * y + x * z := BitVec.mul_add
theorem byte_wrap_distributivity : (BitVec.ofNat 8 255 + BitVec.ofNat 8 1) * BitVec.ofNat 8 3 = BitVec.ofNat 8 255 * BitVec.ofNat 8 3 + BitVec.ofNat 8 1 * BitVec.ofNat 8 3 := BitVec.add_mul
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
fn actual_bitvec_distributivity_source_replays_without_axioms() {
    let mut env = environment();
    register(&mut env, POSITIVE).expect("actual generic and wrapped source");
    let mut reference = ReferenceKernel::new(env).expect("source provenance");
    for name in [
        "right_distributivity",
        "left_distributivity",
        "edge_update",
        "zero_width_distributivity",
        "one_width_distributivity",
        "width_65_distributivity",
        "width_128_distributivity",
        "byte_wrap_distributivity",
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
fn source_refuses_original_distributivity_proofs_for_extra_units() {
    for source in [
        "theorem bad_bitvec_distrib (w : Nat) (x y z : BitVec w) : (x + y) * z = x * z + y * z + 1 := BitVec.add_mul",
        "theorem bad_bitvec_distrib (w : Nat) (x y z : BitVec w) : x * (y + z) = x * y + x * z + 1 := BitVec.mul_add",
    ] {
        let mut env = environment();
        let before = (env.num_constants(), env.num_instances());
        assert!(
            register(&mut env, source).is_err(),
            "false source: {source}"
        );
        assert!(
            env.get_const(&Name::from_string("bad_bitvec_distrib"))
                .is_none()
        );
        assert_eq!((env.num_constants(), env.num_instances()), before);
    }
}
#[test]
fn source_cannot_drop_a_summand_or_mix_widths() {
    for source in [
        "theorem bad_bitvec_distrib (w : Nat) (x y z : BitVec w) : (x + y) * z = x * z := BitVec.add_mul",
        "theorem bad_bitvec_distrib (x z : BitVec 8) (y : BitVec 16) : (x + y) * z = x * z + y * z := BitVec.add_mul",
    ] {
        let mut env = environment();
        let before = (env.num_constants(), env.num_instances());
        assert!(
            register(&mut env, source).is_err(),
            "false source: {source}"
        );
        assert!(
            env.get_const(&Name::from_string("bad_bitvec_distrib"))
                .is_none()
        );
        assert_eq!((env.num_constants(), env.num_instances()), before);
    }
}
