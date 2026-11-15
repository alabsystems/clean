// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Real file-pipeline regressions for Nat and independently sized BitVec amounts.
use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, FileContext,
};
use clean_kernel::{env::Environment, Name};
use clean_parser::parse_file;

fn elaborate(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    for decl in parse_file(source).map_err(|e| format!("parse: {e:?}"))? {
        let decl = preprocess_decl_with_context(&decl, &mut context);
        elaborate_decl_and_register_with_context(&mut env, &decl, &mut context)
            .map_err(|e| e.to_string())?;
    }
    Ok(env)
}

#[test]
fn bitvec_shift_equations_apply_at_symbolic_widths() {
    let left = "theorem witness {w n : Nat} {x : BitVec w} : (x <<< n).toNat = (x.toNat <<< n) % 2^w := @BitVec.toNat_shiftLeft w n x";
    let right = "theorem witness {w : Nat} (x : BitVec w) (n : Nat) : (x >>> n).toNat = x.toNat >>> n := BitVec.toNat_ushiftRight x n";
    for (source, wrong) in [
        (left, left.replace("(x.toNat <<< n)", "(x.toNat >>> n)")),
        (right, right.replace("= x.toNat >>> n", "= x.toNat <<< n")),
    ] {
        let env = elaborate(source).unwrap_or_else(|e| panic!("symbolic equation: {e}\n{source}"));
        assert!(env
            .axiom_deps(&Name::from_string("witness"))
            .expect("proof closure")
            .is_empty());
        assert!(
            elaborate(&wrong).is_err(),
            "wrong universal equation must be refused"
        );
    }
}

#[test]
fn bitvec_shift_amounts_preserve_lean_semantics() {
    for (expression, expected, wrong) in [
        ("((1 : BitVec 3) <<< 8).toNat", 0, 1),
        ("((1 : BitVec 3) <<< (8 : Nat)).toNat", 0, 1),
        ("((1 : BitVec 3) <<< (8 : BitVec 3)).toNat", 1, 0),
        ("((1 : BitVec 3) <<< (8 : BitVec 4)).toNat", 0, 1),
        ("((7 : BitVec 3) >>> 8).toNat", 0, 7),
        ("((7 : BitVec 3) >>> (8 : Nat)).toNat", 0, 7),
        ("((7 : BitVec 3) >>> (8 : BitVec 3)).toNat", 7, 0),
        ("((7 : BitVec 3) >>> (8 : BitVec 4)).toNat", 0, 7),
        ("((0 : BitVec 0) >>> (100 : Nat)).toNat", 0, 1),
        ("((1 : BitVec 8) <<< (8 : Nat)).toNat", 0, 1),
    ] {
        let source = |value| {
            format!(
                "def probe : Nat := {expression}\ntheorem witness : probe = {value} := by rfl\n"
            )
        };
        let env = elaborate(&source(expected))
            .unwrap_or_else(|e| panic!("positive must elaborate: {expression}: {e}"));
        assert!(env
            .axiom_deps(&Name::from_string("witness"))
            .expect("proof closure")
            .is_empty());
        match elaborate(&source(wrong)) {
            Ok(_) => panic!("false equation admitted: {expression} = {wrong}"),
            Err(error) => assert!(
                error.contains("rfl")
                    || error.to_lowercase().contains("mismatch")
                    || error.contains("definitionally equal"),
                "unexpected refusal: {error}"
            ),
        }
    }
}
