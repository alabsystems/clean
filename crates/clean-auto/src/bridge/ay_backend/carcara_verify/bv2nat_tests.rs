// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{pb_widths, verify_alethe_proof};
use carcara::{
    ast::{pool::PrimitivePool, Operator, ProofCommand, Rc, Term},
    parser::{Config, Parser},
    CarcaraResult,
};

fn term(definitions: &str, input: &str, config: Config) -> CarcaraResult<Rc<Term>> {
    Ok(terms(definitions, &[input], config)?.remove(0))
}

fn terms(definitions: &str, inputs: &[&str], config: Config) -> CarcaraResult<Vec<Rc<Term>>> {
    let mut pool = PrimitivePool::new();
    let mut parser = Parser::new(&mut pool, config, definitions)?;
    parser.parse_problem()?;
    inputs
        .iter()
        .map(|input| {
            parser.reset(input)?;
            parser.parse_term()
        })
        .collect()
}

fn configs() -> [Config; 2] {
    [
        Config::new().allow_legacy_bv2nat(true),
        Config::new()
            .allow_legacy_bv2nat(true)
            .apply_function_defs(true),
    ]
}

#[test]
fn legacy_bv2nat_is_opt_in_and_has_the_standard_typed_operator() {
    assert!(term("", "(bv2nat #b01)", Config::new()).is_err());
    for config in configs() {
        // Carcara terms use interned pointer identity: compare in one pool.
        let pair = terms("", &["(bv2nat #b01)", "(ubv_to_int #b01)"], config).unwrap();
        let legacy = &pair[0];
        assert_eq!(legacy, &pair[1]);
        assert!(matches!(legacy.as_ref(), Term::Op(Operator::UBvToInt, args) if args.len() == 1));
        for invalid in [
            "(bv2nat)",
            "(bv2nat #b01 #b10)",
            "(bv2nat 1)",
            "(bv2nat true)",
        ] {
            assert!(term("", invalid, config).is_err(), "{invalid}");
        }
    }
}

#[test]
fn legacy_bv2nat_preserves_declared_and_quoted_function_names() {
    for config in configs() {
        for declaration in ["bv2nat", "|bv2nat|"] {
            let definitions = format!("(declare-fun {declaration} ((_ BitVec 2)) Int)");
            for call in ["(bv2nat #b01)", "(|bv2nat| #b01)"] {
                assert!(matches!(
                    term(&definitions, call, config).unwrap().as_ref(),
                    Term::App(..)
                ));
            }
        }
    }
}

#[test]
fn legacy_bv2nat_preserves_function_definitions_in_both_parser_modes() {
    let definition = "(define-fun bv2nat ((x (_ BitVec 2))) Int 7)";
    for (config, expanded) in configs().into_iter().zip([false, true]) {
        let pair = terms(definition, &["(bv2nat #b01)", "7"], config).unwrap();
        let value = &pair[0];
        if expanded {
            assert_eq!(value, &pair[1]);
        } else {
            assert!(matches!(value.as_ref(), Term::App(..)));
        }
    }
}

#[test]
fn legacy_bv2nat_respects_let_quantifier_and_function_parameter_scopes() {
    for config in configs() {
        let definitions = "(declare-fun f ((_ BitVec 2)) Int)";
        let local = term(definitions, "(let ((bv2nat f)) (bv2nat #b01))", config).unwrap();
        assert!(
            matches!(local.as_ref(), Term::Let(_, body) if matches!(body.as_ref(), Term::App(..)))
        );
        let quantified = term(
            "",
            "(forall ((bv2nat (-> (_ BitVec 2) Int))) (= (bv2nat #b01) 7))",
            config,
        )
        .unwrap();
        let Term::Binder(_, _, body) = quantified.as_ref() else {
            panic!("binder")
        };
        let Term::Op(Operator::Equals, args) = body.as_ref() else {
            panic!("equality")
        };
        assert!(matches!(args[0].as_ref(), Term::App(..)));
        for invalid in [
            "(let ((bv2nat 7)) (bv2nat #b01))",
            "(forall ((bv2nat Int)) (= (bv2nat #b01) 7))",
        ] {
            assert!(term("", invalid, config).is_err(), "{invalid}");
        }
        let parameter = "(define-fun scoped ((bv2nat Int)) Int (bv2nat #b01))";
        assert!(term(parameter, "0", config).is_err());
    }
}

#[test]
fn legacy_bv2nat_anchor_scope_is_restored_after_the_subproof() {
    let proof = "(anchor :step end :args ((bv2nat (-> (_ BitVec 2) Int))))
        (step inner (cl (= (bv2nat #b01) 7)) :rule hole)
        (step end (cl) :rule hole)
        (step outer (cl (= (bv2nat #b01) 1)) :rule hole)";
    for config in configs() {
        let (_, proof, _, _) = carcara::parser::parse_instance("", proof, None, config).unwrap();
        let mut observed = Vec::new();
        for command in proof.iter() {
            let ProofCommand::Step(step) = command else {
                continue;
            };
            if !["inner", "outer"].contains(&step.id.as_str()) {
                continue;
            }
            let Term::Op(Operator::Equals, args) = step.clause[0].as_ref() else {
                panic!("equality")
            };
            observed.push((
                step.id.as_str(),
                matches!(args[0].as_ref(), Term::Op(Operator::UBvToInt, _)),
            ));
        }
        assert_eq!(observed, [("inner", false), ("outer", true)]);
    }
}

const CONTRADICTION: &str = "(assume a (= (ubv_to_int b) 1))
    (assume n (not (= (ubv_to_int b) 1)))
    (step done (cl) :rule resolution :premises (a n))";

fn problem(declaration: &str) -> String {
    format!(
        "(set-logic ALL)(declare-const b (_ BitVec 2)){declaration}
        (assert (= (bv2nat b) 1))(assert (not (= (ubv_to_int b) 1)))(check-sat)"
    )
}

#[test]
fn legacy_bv2nat_certificate_replays_without_rewriting_the_problem() {
    let original = problem("");
    assert!(matches!(
        verify_alethe_proof(&original, CONTRADICTION),
        Ok(true)
    ));
    for mutated in [
        original.replace("(assert (= (bv2nat b) 1))", ""),
        original.replace("(bv2nat b) 1)", "(bv2nat b) 2)"),
    ] {
        assert!(!matches!(
            verify_alethe_proof(&mutated, CONTRADICTION),
            Ok(true)
        ));
    }
    for rule in ["hole", "trust"] {
        assert!(!matches!(
            verify_alethe_proof(&original, &CONTRADICTION.replace("resolution", rule)),
            Ok(true)
        ));
    }
}

#[test]
fn legacy_bv2nat_cannot_turn_declared_or_defined_functions_into_builtins() {
    for declaration in [
        "(declare-fun bv2nat ((_ BitVec 2)) Int)",
        "(declare-fun |bv2nat| ((_ BitVec 2)) Int)",
        "(define-fun bv2nat ((x (_ BitVec 2))) Int 1)",
    ] {
        let original = problem(declaration);
        assert!(!matches!(
            verify_alethe_proof(&original, CONTRADICTION),
            Ok(true)
        ));
    }
}

#[test]
fn legacy_bv2nat_is_available_when_problem_definitions_are_expanded() {
    let original = "(set-logic ALL)(declare-const b (_ BitVec 2))
        (define-fun value () Int (bv2nat b))
        (assert (= value 1))(assert (not (= (ubv_to_int b) 1)))(check-sat)";
    assert!(matches!(
        verify_alethe_proof(original, CONTRADICTION),
        Ok(true)
    ));
    assert!(!matches!(
        pb_widths::check(
            original,
            &CONTRADICTION.replace(":rule resolution", ":rule hole")
        ),
        Ok(true)
    ));
}
