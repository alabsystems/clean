// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::bridge::ay_backend::carcara_verify::verify_alethe_proof;

fn identity(left: &str, right: &str) -> (String, String) {
    let equality = format!("(= {left} {right})");
    let problem = format!("(set-logic QF_BV)(assert (not {equality}))(check-sat)");
    let proof = format!(
        "(assume a (not {equality}))(step e (cl {equality}) :rule refl)(step done (cl) :rule resolution :premises (a e))"
    );
    (problem, proof)
}

#[test]
fn original_decimal_and_binary_spellings_verify_across_machine_width() {
    for width in [1, 9, 63, 64, 65, 127, 128, 129, 256] {
        let limit = BigUint::from(1u8) << width;
        for value in [BigUint::from(0u8), BigUint::from(1u8), &limit - 1u8] {
            let binary = format!("#b{:0>width$}", value.to_str_radix(2));
            let decimal = format!("(_ bv{value} {width})");
            let (problem, proof) = identity(&decimal, &binary);
            assert!(
                matches!(verify_alethe_proof(&problem, &proof), Ok(true)),
                "{width}, {value}"
            );
            // A binary proof must still bind to the original decimal premise.
            let binary_proof = proof.replace(&decimal, &binary);
            assert!(matches!(
                verify_alethe_proof(&problem, &binary_proof),
                Ok(true)
            ));
            let different = (&value + 1u8) % &limit;
            let changed = problem.replace(&decimal, &format!("(_ bv{different} {width})"));
            assert!(!matches!(
                verify_alethe_proof(&changed, &binary_proof),
                Ok(true)
            ));
            for rule in ["hole", "trust"] {
                assert!(!matches!(
                    verify_alethe_proof(
                        &problem,
                        &proof.replace(":rule refl", &format!(":rule {rule}"))
                    ),
                    Ok(true)
                ));
            }
        }
    }
}

#[test]
fn decimal_reduction_uses_all_bits_before_modulo_the_declared_width() {
    for width in [1, 9, 64, 128, 256] {
        let limit = BigUint::from(1u8) << width;
        for low in [BigUint::from(0u8), BigUint::from(1u8), &limit - 1u8] {
            let value = (&limit << 257usize) + &low;
            let decimal = format!("(_ bv{value} {width})");
            let binary = format!("#b{:0>width$}", low.to_str_radix(2));
            let (problem, proof) = identity(&decimal, &binary);
            assert!(matches!(verify_alethe_proof(&problem, &proof), Ok(true)));
            let wrong = format!("#b{:0>width$}", ((&low + 1u8) % &limit).to_str_radix(2));
            let (_, wrong_proof) = identity(&decimal, &wrong);
            assert!(!matches!(
                verify_alethe_proof(&problem, &wrong_proof),
                Ok(true)
            ));
        }
    }
}

#[test]
fn lexical_context_preserves_comments_strings_symbols_and_unicode() {
    let opaque = "; (_ bv99 8)\n|(_ bv99 8)| \"quoted \"\" (_ bv99 8)\" |λ (_ bv99 8)|";
    assert_eq!(normalize(opaque).unwrap(), opaque);
    let input = format!("{opaque}\n(= (_ ; ignored (_ bv9 2)\n bv257 ; more\n 8) #b00000001)");
    assert_eq!(
        normalize(&input).unwrap(),
        format!("{opaque}\n(= #b00000001 #b00000001)")
    );
    for input in [
        "(_ |bv99| 8)",
        "(|_| bv99 8)",
        "(symbol_bv99 8)",
        "((_ extract 7 0) x)",
    ] {
        assert_eq!(normalize(input).unwrap(), input);
    }
    let name = "|λ (_ bv340282366920938463463374607431768211455 128)|";
    let problem = format!("(declare-const {name} Bool)(assert {name})(assert (not {name}))");
    let proof = format!(
        "(assume a {name})(assume b (not {name}))(step done (cl) :rule resolution :premises (a b))"
    );
    assert!(matches!(verify_alethe_proof(&problem, &proof), Ok(true)));
}

#[test]
fn malformed_and_over_budget_literals_are_errors() {
    for term in [
        "(_ bv 8)",
        "(_ bv-1 8)",
        "(_ bv+1 8)",
        "(_ bvNaN 8)",
        "(_ bv1 0)",
        "(_ bv1 -1)",
        "(_ bv1 01)",
        "(_ bv1 1.0)",
        "(_ bv1 8 extra)",
        "(_ bv1)",
        "(_ bv1 8",
        "(_ bv1 18446744073709551616)",
        "(_ bv1 16385)",
    ] {
        assert!(normalize(term).is_err(), "{term}");
        let (problem, proof) = identity(term, "#b1");
        assert!(!matches!(verify_alethe_proof(&problem, &proof), Ok(true)));
    }
    assert!(normalize(&format!("(_ bv{} 8)", "9".repeat(MAX_DIGITS + 1))).is_err());
    let many = "(_ bv0 16384) ".repeat(MAX_EXPANDED_BITS / MAX_WIDTH + 1);
    assert!(normalize(&many).is_err());
}

#[test]
fn definitions_and_local_assumptions_keep_the_original_constant() {
    let value = "(_ bv340282366920938463463374607431768211455 128)";
    let binary = format!("#b{}", "1".repeat(128));
    let (problem, proof) = identity(value, &binary);
    let defined = format!(
        "(define-fun wide () (_ BitVec 128) {value}){}",
        proof.replace(value, "wide")
    );
    assert!(matches!(verify_alethe_proof(&problem, &defined), Ok(true)));
    let wrong = defined.replace(value, "(_ bv0 128)");
    assert!(!matches!(verify_alethe_proof(&problem, &wrong), Ok(true)));
    let nested = format!(
        "(assume a (not (= {value} {binary})))(anchor :step local)(assume h true)(step e (cl (= {value} {binary})) :rule refl)(step local (cl (not true) (= {value} {binary})) :rule subproof :discharge (h))(step yes (cl true) :rule true)(step eq (cl (= {value} {binary})) :rule resolution :premises (local yes))(step done (cl) :rule resolution :premises (a eq))"
    );
    assert!(matches!(verify_alethe_proof(&problem, &nested), Ok(true)));
}

#[test]
fn a_comment_ended_by_cr_does_not_hide_a_string_from_the_rewrite() {
    // `; c<CR>` ends the comment for Carcara; text after the CR is code, and
    // the string literal that follows must stay byte-for-byte. Before the
    // pre-pass shared the lexer's comment rule, it rewrote `(_ bv1 1)` inside
    // the string to `#b1`, so a refutation of this satisfiable script passed.
    let problem =
        "(set-logic ALL)\n; c\r(assert (not (= \"\n(_ bv1 1)\" \"\n#b1\")))\n(check-sat)\n";
    let normalized = normalize(problem).expect("normalize");
    assert!(normalized.contains("\"\n(_ bv1 1)\""), "{normalized}");
    let proof = "(assume a (not (= \"\n(_ bv1 1)\" \"\n#b1\")))(step e (cl (= \"\n(_ bv1 1)\" \"\n#b1\")) :rule refl)(step done (cl) :rule resolution :premises (a e))";
    assert!(!matches!(verify_alethe_proof(problem, proof), Ok(true)));
}
