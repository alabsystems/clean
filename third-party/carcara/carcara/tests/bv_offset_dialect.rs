// Added in Clean: checked scalar cancellation belongs only to the Clean rule dialect.
use carcara::{checker, parser};

fn check(definitions: &str, theorem: &str, clean: bool) -> Result<bool, String> {
    let problem = format!("{definitions}(assert (not {theorem}))(check-sat)");
    let proof = format!(
        "(assume h (not {theorem}))\n(step e (cl {theorem}) :rule eq_simplify)\n\
         (step done (cl) :rule resolution :premises (h e))"
    );
    let (problem, proof, rules, mut pool) = parser::parse_instance(
        problem.as_str(),
        proof.as_str(),
        None,
        parser::Config::clean_dialect(),
    )
    .map_err(|e| format!("parse: {e}"))?;
    let config = if clean {
        checker::Config::clean_dialect()
    } else {
        checker::Config::new()
    };
    checker::ProofChecker::new(&mut pool, &rules, config)
        .check(&problem, &proof)
        .map(|holey| !holey)
        .map_err(|e| format!("check: {e}"))
}

fn add(base: &str, value: u128, width: usize, constant_first: bool) -> String {
    let constant = literal(value, width);
    if constant_first {
        format!("(bvadd {constant} {base})")
    } else {
        format!("(bvadd {base} {constant})")
    }
}

fn literal(value: u128, width: usize) -> String {
    // Binary spelling exercises all 128 value bits; the legacy decimal
    // `_ bvN` argument reader has a narrower numeric range.
    format!("#b{value:0width$b}")
}

#[test]
fn clean_bv_offsets_exhaustive_small_words_match_all_valuations() {
    for width in 1..=3 {
        let modulus = 1u128 << width;
        let defs = format!("(declare-const x (_ BitVec {width}))");
        for a in 0..modulus {
            for b in 0..modulus {
                let equal = a == b;
                // Independent evaluation of every possible common base checks
                // the bijection, including every wraparound in these widths.
                for x in 0..modulus {
                    assert_eq!((x + a) % modulus == (x + b) % modulus, equal);
                }
                for a_first in [false, true] {
                    for b_first in [false, true] {
                        let left = add("x", a, width, a_first);
                        let right = add("x", b, width, b_first);
                        let source = format!("(= {left} {right})");
                        let target = equal.to_string();
                        for theorem in [
                            format!("(= {source} {target})"),
                            format!("(= {target} {source})"),
                        ] {
                            assert_eq!(check(&defs, &theorem, true), Ok(true), "{theorem}");
                        }
                        let wrong = format!("(= {source} {})", !equal);
                        assert!(check(&defs, &wrong, true).is_err(), "{wrong}");
                        let cancellation =
                            format!("(= {source} (= (_ bv{a} {width}) (_ bv{b} {width})))");
                        assert_eq!(
                            check(&defs, &cancellation, true),
                            Ok(true),
                            "{cancellation}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn clean_bv_offsets_word_boundaries_wrap_and_literal_equality() {
    for width in [1, 8, 64, 128] {
        let max = u128::MAX >> (128 - width);
        let defs = format!("(declare-const x (_ BitVec {width}))");
        for (a, b) in [(0, 0), (0, 1), (max, 0), (max, max), (max, 1)] {
            let left = add("x", a, width, false);
            let right = add("x", b, width, true);
            let theorem = format!("(= (= {left} {right}) {})", a == b);
            assert_eq!(check(&defs, &theorem, true), Ok(true), "{theorem}");
            let literal = format!(
                "(= (= {} {}) {})",
                literal(a, width),
                literal(b, width),
                a == b
            );
            assert_eq!(check(&defs, &literal, true), Ok(true), "{literal}");
        }
    }
    // Source literals are canonically reduced by the parser, so wrap-equivalent
    // spellings cannot be mistaken for distinct offsets.
    let wrap = "(= (= (bvadd x (_ bv256 8)) (bvadd x (_ bv0 8))) true)";
    assert_eq!(
        check("(declare-const x (_ BitVec 8))", wrap, true),
        Ok(true)
    );
    assert!(check(
        "(declare-const x (_ BitVec 8))",
        &wrap.replace("true", "false"),
        true
    )
    .is_err());
}

#[test]
fn clean_bv_offsets_does_not_extend_the_default_checker() {
    let defs = "(declare-const x (_ BitVec 8))";
    for theorem in [
        "(= (= (bvadd x #x00) (bvadd x #x01)) false)",
        "(= (= #x00 #x01) false)",
        "(= (= (bvadd x #x00) (bvadd #x01 x)) (= #x00 #x01))",
    ] {
        assert_eq!(check(defs, theorem, true), Ok(true));
        assert!(
            check(defs, theorem, false).is_err(),
            "default acquired {theorem}"
        );
    }
    assert_eq!(check(defs, "(= (= x x) true)", false), Ok(true));
    assert_eq!(check(defs, "(= (= 0 1) false)", true), Ok(true));
}

#[test]
fn clean_bv_offsets_uses_the_same_dialect_gate_in_parallel() {
    use std::sync::Arc;
    let theorem = "(= (= (bvadd x #x00) (bvadd x #x01)) false)";
    let problem = format!("(declare-const x (_ BitVec 8))(assert (not {theorem}))");
    let proof = format!("(assume h (not {theorem}))\n(step e (cl {theorem}) :rule eq_simplify)\n(step done (cl) :rule resolution :premises (h e))");
    for clean in [false, true] {
        for threads in [1, 4] {
            let (problem, proof, rules, pool) = parser::parse_instance(
                problem.as_str(),
                proof.as_str(),
                None,
                parser::Config::clean_dialect(),
            )
            .unwrap();
            let (scheduler, usage) = checker::Scheduler::new(threads, &proof);
            let config = if clean {
                checker::Config::clean_dialect()
            } else {
                checker::Config::new()
            };
            let got = checker::ParallelProofChecker::new(
                Arc::new(pool),
                config,
                &problem.prelude,
                &usage,
                8 * 1024 * 1024,
                rules,
            )
            .check(&problem, &proof, &scheduler);
            if clean {
                assert!(!got.unwrap());
            } else {
                assert!(got.is_err());
            }
        }
    }
}

#[test]
fn clean_bv_offsets_refuses_aliases_private_heads_and_wrong_claims() {
    let defs = "(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))\
                (declare-fun private_add ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))";
    for theorem in [
        "(= (= (bvadd x #x00) (bvadd y #x01)) false)",
        "(= (= (bvmul x #x00) (bvmul x #x01)) false)",
        "(= (= (private_add x #x00) (private_add x #x01)) false)",
        "(= (= (bvadd x #x00) (bvadd x #x01)) true)",
        "(= (= (bvadd x #x00) (bvadd x #x01)) (= #x00 #x02))",
        "(= (= (bvadd x (bvadd #x00 #x00)) (bvadd x #x01)) false)",
    ] {
        let error = check(defs, theorem, true).expect_err(theorem);
        assert!(
            error.starts_with("check:"),
            "control must parse: {theorem}: {error}"
        );
    }
    // An alias premise is not a cancellation authority; it needs a separately
    // checked congruence before this intrinsic rule can be used.
    let problem = format!("{defs}(assert (= x y))(assert false)");
    let proof = "(assume h (= x y))\n(step e (cl (= (= (bvadd x #x00) (bvadd y #x01)) false)) :rule eq_simplify :premises (h))\n(step done (cl) :rule hole)";
    let (problem, proof, rules, mut pool) = parser::parse_instance(
        problem.as_str(),
        proof,
        None,
        parser::Config::clean_dialect(),
    )
    .unwrap();
    let error = checker::ProofChecker::new(&mut pool, &rules, checker::Config::clean_dialect())
        .check(&problem, &proof)
        .unwrap_err();
    assert!(format!("{error}").contains("premises"), "{error}");

    let theorem = "(= (= (bvadd x #x00) (bvadd x #x01)) false)";
    let proof = format!(
        "(step e (cl {theorem}) :rule eq_simplify :args (#x00))\n(step done (cl) :rule hole)"
    );
    let (problem, proof, rules, mut pool) =
        parser::parse_instance(defs, proof.as_str(), None, parser::Config::clean_dialect())
            .unwrap();
    let error = checker::ProofChecker::new(&mut pool, &rules, checker::Config::clean_dialect())
        .check(&problem, &proof)
        .unwrap_err();
    assert!(format!("{error}").contains("arguments"), "{error}");
}
