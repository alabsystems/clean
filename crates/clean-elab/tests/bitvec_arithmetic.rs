// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Actual source applications of Lean's width-generic BitVec arithmetic API.

use clean_elab::{
    elaborate_decl_and_register, prepare_session_environment, preprocess_decl_with_context,
    ElabResult, FileContext,
};
use clean_kernel::{reference::ReferenceKernel, Declaration, Environment, Expr, Name};
use clean_parser::parse_file;

const POSITIVE: &str = r"
def add8 (x y : BitVec 8) : BitVec 8 := x + y
def mul3 (x y : BitVec 3) : BitVec 3 := x * y
theorem add8_wrap : add8 255 1 = 0 := by decide
theorem mul3_wrap : mul3 3 3 = 1 := by decide
theorem zero_width : (7 : BitVec 0) + 11 = 0 := by decide
theorem add_branch_wrap : (if True then (255 : BitVec 8) + 1 else 0) = 0 := by decide
theorem mul_branch_wrap : (if True then (16 : BitVec 8) * 16 else 0) = 0 := by decide
theorem uint_control : (255 : UInt8) + 1 = 0 := by decide
theorem fin_control : (3 : Fin 4) + 1 = 0 := by decide
theorem symbolic_add {w : Nat} (x y : BitVec w) :
    (x + y).toNat = (x.toNat + y.toNat) % (2 ^ w) := by rfl
theorem symbolic_mul {w : Nat} (x y : BitVec w) :
    (x * y).toNat = (x.toNat * y.toNat) % (2 ^ w) := by rfl
theorem symbolic_mul_comm {w : Nat} (x y : BitVec w) :
    x * y = y * x := BitVec.mul_comm x y
";

fn failed(result: &ElabResult) -> bool {
    match result {
        ElabResult::Failed { .. } => true,
        ElabResult::Multiple(results) => results.iter().any(failed),
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

#[test]
fn source_bitvec_arithmetic_wraps_and_preserves_other_carriers() {
    let mut env = Environment::with_prelude();
    prepare_session_environment(&mut env);
    register(&mut env, POSITIVE).expect("canonical source semantics");
    let names = [
        "add8_wrap",
        "mul3_wrap",
        "zero_width",
        "add_branch_wrap",
        "mul_branch_wrap",
        "uint_control",
        "fin_control",
        "symbolic_add",
        "symbolic_mul",
        "symbolic_mul_comm",
    ];
    for name in names {
        assert!(env
            .axiom_deps(&Name::from_string(name))
            .expect("closure")
            .is_empty());
    }
    let mut reference = ReferenceKernel::new(env).expect("source environment provenance");
    for name in names {
        let original = Name::from_string(name);
        let info = reference
            .environment()
            .get_const(&original)
            .expect("source theorem");
        assert!(info.level_params.is_empty());
        let type_ = info.type_.clone();
        let alias = Name::from_string(&format!("reference_{name}"));
        reference
            .add_checked(Declaration::Theorem {
                name: alias.clone(),
                level_params: vec![],
                type_,
                value: Expr::const_(original, vec![]),
            })
            .expect("replay the actual source theorem and its inherited closure");
        assert!(reference
            .environment()
            .axiom_deps(&alias)
            .expect("reference closure")
            .is_empty());
    }
}

#[test]
fn source_bitvec_arithmetic_refuses_unchanged_proof_for_wrong_residues() {
    for source in [
        "theorem bad_result : (255 : BitVec 8) + 1 = 1 := by decide",
        "theorem bad_result : (3 : BitVec 3) * 3 = 2 := by decide",
        "theorem bad_result : (if True then (255 : BitVec 8) + 1 else 0) ≠ 0 := by decide",
        "theorem bad_result : (if True then (16 : BitVec 8) * 16 else 0) ≠ 0 := by decide",
        "theorem bad_result {w : Nat} (x y : BitVec w) : x * y = y * x + 1 := BitVec.mul_comm x y",
    ] {
        let mut env = Environment::with_prelude();
        prepare_session_environment(&mut env);
        let before = (env.num_constants(), env.num_instances());
        assert!(
            register(&mut env, source).is_err(),
            "false source: {source}"
        );
        assert!(env.get_const(&Name::from_string("bad_result")).is_none());
        assert_eq!((env.num_constants(), env.num_instances()), before);
    }
}

#[test]
fn source_bitvec_arithmetic_refuses_a_mixed_width_application() {
    let mut env = Environment::with_prelude();
    prepare_session_environment(&mut env);
    let before = (env.num_constants(), env.num_instances());
    let source = "def bad_width (x : BitVec 8) (y : BitVec 16) : BitVec 8 := x + y";
    assert!(register(&mut env, source).is_err());
    assert!(env.get_const(&Name::from_string("bad_width")).is_none());
    assert_eq!((env.num_constants(), env.num_instances()), before);
}
