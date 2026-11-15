// Added in Clean: independent fresh-parser semantics for array_const_select_v1.
use carcara::{checker, parser};

fn check(problem: &str, proof: &str, clean: bool) -> Result<bool, String> {
    let pc = if clean {
        parser::Config::clean_dialect()
    } else {
        parser::Config::new()
    };
    let (problem, proof, rules, mut pool) =
        parser::parse_instance(problem, proof, None, pc).map_err(|e| format!("parse: {e}"))?;
    let cfg = if clean {
        checker::Config::clean_dialect()
    } else {
        checker::Config::default()
    };
    checker::ProofChecker::new(&mut pool, &rules, cfg)
        .check(&problem, &proof)
        .map(|holey| !holey)
        .map_err(|e| format!("check: {e}"))
}
fn packet(index: &str, fill: &str, value: &str, reverse: bool) -> (String, String) {
    let read = format!("(select ((as const (Array {index} Bool)) {fill}) k)");
    let claim = if reverse {
        format!("(= {value} {read})")
    } else {
        format!("(= {read} {value})")
    };
    let problem=format!("(set-logic ALL)(declare-const k {index})(declare-const f Bool)(declare-const g Bool)(assert (not {claim}))(check-sat)");
    let proof=format!("(assume h (not {claim}))\n(step e (cl {claim}) :rule array_const_select_v1)\n(step done (cl) :rule resolution :premises (h e))");
    (problem, proof)
}

#[test]
fn array_const_select_clean_dialect_accepts_exact_units_and_standard_default_refuses() {
    for index in [
        "Bool",
        "Int",
        "(_ BitVec 1)",
        "(_ BitVec 32)",
        "(_ BitVec 128)",
    ] {
        for fill in ["true", "false", "f"] {
            for reverse in [false, true] {
                let (problem, proof) = packet(index, fill, fill, reverse);
                assert_eq!(check(&problem, &proof, true), Ok(true), "{problem}");
                let old = check(&problem, &proof, false).unwrap_err();
                assert!(old.contains("unknown rule"), "{old}");
            }
        }
    }
}

#[test]
fn array_const_select_different_fill_cannot_prove_a_sat_source() {
    for (fill, wrong) in [("true", "false"), ("false", "true"), ("f", "g")] {
        for reverse in [false, true] {
            let (problem, proof) = packet("(_ BitVec 32)", fill, wrong, reverse);
            assert!(check(&problem, &proof, true).is_err(), "{problem}");
        }
    }
}

#[test]
fn array_const_select_arity_arguments_premises_and_compound_atoms_refuse() {
    let (problem, proof) = packet("(_ BitVec 32)", "f", "f", false);
    for mutated in [
        proof.replace("(cl (= (select", "(cl true (= (select"),
        proof.replace(
            ":rule array_const_select_v1",
            ":rule array_const_select_v1 :args (f)",
        ),
        proof.replace(
            ":rule array_const_select_v1",
            ":rule array_const_select_v1 :premises (h)",
        ),
        proof.replace(
            "(Array (_ BitVec 32) Bool)) f)",
            "(Array (_ BitVec 32) Bool)) f g)",
        ),
        proof.replace(
            "(Array (_ BitVec 32) Bool)) f) k)",
            "(Array (_ BitVec 32) Bool)) f))",
        ),
        proof.replace(
            "(Array (_ BitVec 32) Bool)) f) k)",
            "(Array (_ BitVec 32) Bool)) f) f)",
        ),
        proof.replace(
            "(Array (_ BitVec 32) Bool)) f)",
            "(Array (_ BitVec 32) Int)) f)",
        ),
    ] {
        assert!(check(&problem, &mutated, true).is_err(), "{mutated}");
    }
    for (index, fill, key) in [
        ("Real", "f", "k"),
        ("(_ BitVec 129)", "f", "k"),
        ("(_ BitVec 32)", "(not f)", "k"),
        ("(_ BitVec 32)", "f", "(bvadd k (_ bv0 32))"),
    ] {
        let (problem, proof) = packet(index, fill, fill, false);
        let (problem, proof) = (
            problem.replace(")) f) k)", &format!(")) f) {key})")),
            proof.replace(")) f) k)", &format!(")) f) {key})")),
        );
        assert!(check(&problem, &proof, true).is_err(), "{problem}");
    }
}

#[test]
fn array_const_select_ordinary_function_lookalikes_do_not_gain_native_meaning() {
    for (declaration, claim) in [
        (
            "(declare-fun |select| ((Array (_ BitVec 32) Bool) (_ BitVec 32)) Bool)",
            "(= (|select| ((as const (Array (_ BitVec 32) Bool)) f) k) f)",
        ),
        (
            "(declare-fun const (Bool) (Array (_ BitVec 32) Bool))",
            "(= (select (const f) k) f)",
        ),
        (
            "(declare-fun fake_eq (Bool Bool) Bool)",
            "(fake_eq (select ((as const (Array (_ BitVec 32) Bool)) f) k) f)",
        ),
    ] {
        let problem=format!("(set-logic ALL)(declare-const k (_ BitVec 32))(declare-const f Bool){declaration}(assert (not {claim}))(check-sat)");
        let proof=format!("(assume h (not {claim}))(step e (cl {claim}) :rule array_const_select_v1)(step done (cl) :rule resolution :premises (h e))");
        assert!(check(&problem, &proof, true).is_err(), "{problem}");
    }
}

#[test]
fn array_const_select_foreign_assumption_and_changed_original_source_refuse() {
    let (problem, proof) = packet("(_ BitVec 32)", "f", "f", false);
    let changed = problem.replace(
        "(Array (_ BitVec 32) Bool)) f)",
        "(Array (_ BitVec 32) Bool)) g)",
    );
    assert!(check(&changed, &proof, true).is_err());
    let changed = problem
        .replace("(assert (not", "(assert (or true (not")
        .replace("))(check-sat)", ")))(check-sat)");
    assert!(check(&changed, &proof, true).is_err());
}

#[test]
fn array_const_select_original_row2_export_is_a_hermetic_fresh_source_regression() {
    let source = include_str!("fixtures/array_const_select_v1/original-p10-row2.smt2");
    let proof = include_str!("fixtures/array_const_select_v1/original-p10-row2.alethe");
    assert_eq!(check(source, proof, true), Ok(true));
    assert!(check(source, proof, false)
        .unwrap_err()
        .contains("unknown rule"));
    let sat_source = source.replace(
        "(Array (_ BitVec 32) Bool)) true)",
        "(Array (_ BitVec 32) Bool)) false)",
    );
    assert_ne!(sat_source, source);
    assert!(check(&sat_source, proof, true)
        .unwrap_err()
        .contains("original problem premises"));
}
