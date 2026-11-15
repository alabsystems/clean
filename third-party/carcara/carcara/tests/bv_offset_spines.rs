// Added in Clean: independently exercise the versioned scalar spine contract.
use carcara::{checker, parser};

const RULE: &str = "eq_simplify_bv_offset_spines";

#[derive(Clone, Copy)]
enum Dialect {
    Default,
    OldClean,
    SpinesV1,
}
fn config(dialect: Dialect) -> checker::Config {
    match dialect {
        Dialect::Default => checker::Config::new(),
        Dialect::OldClean => checker::Config::clean_dialect(),
        Dialect::SpinesV1 => checker::Config::clean_dialect().with_bv_offset_spines_v1(),
    }
}
fn certificate(defs: &str, theorem: &str, rule: &str) -> (String, String) {
    (format!("{defs}(assert (not {theorem}))(check-sat)"),
     format!("(assume h (not {theorem}))\n(step e (cl {theorem}) :rule {rule})\n(step done (cl) :rule resolution :premises (h e))"))
}
fn check(defs: &str, theorem: &str, rule: &str, dialect: Dialect) -> Result<bool, String> {
    let (problem, proof) = certificate(defs, theorem, rule);
    let (problem, proof, rules, mut pool) = parser::parse_instance(
        problem.as_str(),
        proof.as_str(),
        None,
        parser::Config::clean_dialect(),
    )
    .map_err(|e| format!("parse: {e}"))?;
    checker::ProofChecker::new(&mut pool, &rules, config(dialect))
        .check(&problem, &proof)
        .map(|holey| !holey)
        .map_err(|e| format!("check: {e}"))
}
fn literal(value: u128, width: usize) -> String {
    format!("#b{value:0width$b}")
}
fn frame(base: &str, k: &str, op: usize) -> String {
    match op {
        0 => format!("(bvadd {base} {k})"),
        1 => format!("(bvadd {k} {base})"),
        2 => format!("(bvsub {base} {k})"),
        _ => unreachable!(),
    }
}
fn arithmetic(value: i128, k: i128, op: usize, modulus: i128) -> i128 {
    if op == 2 {
        (value - k).rem_euclid(modulus)
    } else {
        (value + k).rem_euclid(modulus)
    }
}

#[test]
fn spine_v1_exhaustive_small_words_match_independent_modular_evaluation() {
    let mut reference = String::from("(set-logic QF_BV)\n");
    let mut expected = String::new();
    for width in 1..=4 {
        let modulus = 1i128 << width;
        let defs = format!("(declare-const x (_ BitVec {width}))");
        for a in 0..modulus {
            for b in 0..modulus {
                for first in 0..3 {
                    for second in 0..3 {
                        let left = frame(
                            &frame("x", &literal(a as u128, width), first),
                            &literal(b as u128, width),
                            second,
                        );
                        let offset =
                            arithmetic(arithmetic(0, a, first, modulus), b, second, modulus);
                        for x in 0..modulus {
                            assert_eq!(
                                arithmetic(arithmetic(x, a, first, modulus), b, second, modulus),
                                (x + offset).rem_euclid(modulus)
                            );
                        }
                        for delta in [0, 1] {
                            let right = if offset == 0 && delta == 0 {
                                "x".to_owned()
                            } else {
                                frame(
                                    "x",
                                    &literal(((offset + delta) % modulus) as u128, width),
                                    0,
                                )
                            };
                            let truth = delta == 0;
                            let inner = format!("(= {left} {right})");
                            let theorem = format!("(= {inner} {truth})");
                            assert_eq!(
                                check(&defs, &theorem, RULE, Dialect::SpinesV1),
                                Ok(true),
                                "{theorem}"
                            );
                            let reverse = format!("(= {truth} {inner})");
                            assert_eq!(
                                check(&defs, &reverse, RULE, Dialect::SpinesV1),
                                Ok(true),
                                "{reverse}"
                            );
                            let wrong = format!("(= {inner} {})", !truth);
                            let error = check(&defs, &wrong, RULE, Dialect::SpinesV1)
                                .expect_err("wrong truth");
                            assert!(error.contains("step 'e'"), "{error}");
                            for (claim, verdict) in [(&theorem, "unsat"), (&wrong, "sat")] {
                                reference.push_str(&format!("(push 1)\n{defs}\n(assert (not {claim}))\n(check-sat)\n(pop 1)\n"));
                                expected.push_str(verdict);
                                expected.push('\n');
                            }
                        }
                    }
                }
            }
        }
    }
    if let Ok(dir) = std::env::var("CLEAN_BV_OFFSET_SPINES_REFERENCE_DIR") {
        let dir = std::path::Path::new(&dir);
        std::fs::create_dir_all(dir).unwrap();
        std::fs::write(dir.join("small-spines.smt2"), reference).unwrap();
        std::fs::write(dir.join("small-spines.expected"), expected).unwrap();
    }
}

#[test]
fn spine_v1_bounds_wrap_and_bare_bases_are_exact() {
    for width in [1, 8, 64, 128] {
        let max = u128::MAX >> (128 - width);
        let defs = format!("(declare-const x (_ BitVec {width}))");
        let max = literal(max, width);
        let one = literal(1, width);
        let zero = literal(0, width);
        let wrap = frame(&frame("x", &max, 0), &one, 1);
        for theorem in [
            format!("(= (= {wrap} x) true)"),
            format!("(= true (= x {wrap}))"),
            format!("(= (= {} x) true)", frame(&frame("x", &one, 2), &one, 0)),
        ] {
            assert_eq!(
                check(&defs, &theorem, RULE, Dialect::SpinesV1),
                Ok(true),
                "{theorem}"
            );
        }
        for (a, b, accepted) in [
            (0, 0, true),
            (16, 0, true),
            (0, 16, true),
            (16, 16, true),
            (17, 16, false),
            (16, 17, false),
            (17, 17, false),
        ] {
            let mut left = "x".to_owned();
            let mut right = "x".to_owned();
            for i in 0..a {
                left = frame(&left, &zero, i % 3);
            }
            for i in 0..b {
                right = frame(&right, &zero, (i + 1) % 3);
            }
            let theorem = format!("(= (= {left} {right}) true)");
            assert_eq!(
                check(&defs, &theorem, RULE, Dialect::SpinesV1).is_ok(),
                accepted,
                "w={width} a={a} b={b}"
            );
        }
    }
}

#[test]
fn spine_v1_requires_its_separate_versioned_capability() {
    let defs = "(declare-const x (_ BitVec 8))";
    let deep = "(= (= (bvadd (bvadd x #xff) #x02) (bvadd x #x01)) true)";
    for old in [Dialect::Default, Dialect::OldClean] {
        let error = check(defs, deep, RULE, old).expect_err("new name must be unknown");
        assert!(error.to_lowercase().contains("unknown rule"), "{error}");
    }
    assert_eq!(check(defs, deep, RULE, Dialect::SpinesV1), Ok(true));
    assert!(check(defs, deep, "eq_simplify", Dialect::OldClean).is_err());
    assert!(check(defs, deep, "eq_simplify", Dialect::SpinesV1).is_err());
    let immediate = "(= (= (bvadd x #x00) (bvadd x #x01)) false)";
    assert_eq!(
        check(defs, immediate, "eq_simplify", Dialect::OldClean),
        Ok(true)
    );
    assert_eq!(
        check(defs, immediate, "eq_simplify", Dialect::SpinesV1),
        Ok(true)
    );
}

#[test]
fn spine_v1_opaque_bases_do_not_authorize_aliases_or_other_arithmetic() {
    let defs="(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))(declare-fun private_add ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))";
    for theorem in [
        "(= (= (bvadd (bvadd x #x01) #x02) (bvadd y #x03)) true)",
        "(= (= (bvadd (bvadd x #x01) #x02) (bvadd y #x04)) false)",
        "(= (= (bvsub #x01 x) (bvsub x #x01)) true)",
        "(= (= (bvmul x #x02) (bvadd x x)) true)",
        "(= (= (bvshl x #x01) (bvadd x x)) true)",
        "(= (= (bvneg x) (bvsub #x00 x)) true)",
        "(= (= (private_add x #x01) (bvadd x #x01)) true)",
        "(= (= (bvadd #x01 #x02) #x03) true)",
        "(= (= (bvsub #x02 #x01) #x01) true)",
        "(= (= (bvadd x y) x) true)",
    ] {
        let error = check(defs, theorem, RULE, Dialect::SpinesV1).expect_err(theorem);
        assert!(error.starts_with("check:"), "control must parse: {error}");
    }
    // An unsupported, well-typed whole term may be an identical opaque base.
    for base in [
        "(bvadd x y)",
        "(bvsub #x01 x)",
        "(bvmul x y)",
        "(private_add x y)",
        "((_ extract 7 0) x)",
    ] {
        let theorem = format!("(= (= (bvsub (bvadd {base} #x01) #x01) {base}) true)");
        assert_eq!(
            check(defs, &theorem, RULE, Dialect::SpinesV1),
            Ok(true),
            "{theorem}"
        );
    }
}

#[test]
fn spine_v1_alias_premises_arguments_and_wrong_truth_are_causal_refusals() {
    let defs = "(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))";
    let theorem = "(= (= (bvadd (bvadd x #x01) #x02) (bvadd x #x03)) true)";
    let (problem, proof) = certificate(defs, theorem, RULE);
    let wrong_theorem = theorem.replacen("true", "false", 1);
    let wrong = proof.replacen(
        &format!("(step e (cl {theorem})"),
        &format!("(step e (cl {wrong_theorem})"),
        1,
    );
    let (problem, proof, rules, mut pool) = parser::parse_instance(
        problem.as_str(),
        wrong.as_str(),
        None,
        parser::Config::clean_dialect(),
    )
    .unwrap();
    let error = checker::ProofChecker::new(&mut pool, &rules, config(Dialect::SpinesV1))
        .check(&problem, &proof)
        .unwrap_err();
    assert!(format!("{error}").contains("step 'e'"), "{error}");
    for suffix in [":premises (a)", ":args (#x01)"] {
        let problem = format!("{defs}(assert (= x y))");
        let proof=format!("(assume a (= x y))(step e (cl {theorem}) :rule {RULE} {suffix})(step end (cl) :rule hole)");
        let (problem, proof, rules, mut pool) = parser::parse_instance(
            problem.as_str(),
            proof.as_str(),
            None,
            parser::Config::clean_dialect(),
        )
        .unwrap();
        let error = checker::ProofChecker::new(&mut pool, &rules, config(Dialect::SpinesV1))
            .check(&problem, &proof)
            .unwrap_err();
        assert!(format!("{error}").contains("step 'e'"), "{error}");
    }
}
