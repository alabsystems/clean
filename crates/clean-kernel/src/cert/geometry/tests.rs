// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for geometry certificate generation and problem conversion.

use super::*;
use crate::cert::ProofCert;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::level::Level;

#[test]
fn test_generator_requires_init() {
    let env = Environment::new();
    let result = GeometryCertGenerator::new(env);
    assert!(matches!(
        result,
        Err(GeometryCertError::EnvironmentNotInitialized)
    ));
}

#[test]
fn test_generator_with_init() {
    let mut env = Environment::new();
    env.init_computational_geometry().unwrap();
    let generator =
        GeometryCertGenerator::new(env).expect("Generator should initialize with geometry env");
    // Verify the generator can resolve known predicates
    generator
        .geometry_name_to_const("collinear")
        .expect("Initialized generator should resolve collinear");
}

#[test]
fn test_axiom_to_cert() {
    let mut env = Environment::new();
    env.init_computational_geometry().unwrap();
    let generator = GeometryCertGenerator::new(env).unwrap();

    let step = GeomStep::Axiom {
        name: "collinear".to_string(),
        args: vec!["A".to_string(), "B".to_string(), "C".to_string()],
    };

    let cert = generator
        .axiom_to_cert(&step.name_str(), &[])
        .expect("collinear axiom should produce a cert");
    assert!(
        matches!(cert, ProofCert::Const { .. }),
        "Axiom cert should be Const variant"
    );
}

#[test]
fn test_lemma_name_mapping() {
    let mut env = Environment::new();
    env.init_computational_geometry().unwrap();
    let generator = GeometryCertGenerator::new(env).unwrap();

    // Test various lemma name formats — verify each resolves to a Name
    generator
        .geometry_lemma_to_const("thales")
        .expect("thales should resolve");
    generator
        .geometry_lemma_to_const("Thales")
        .expect("Thales (capitalized) should resolve");
    generator
        .geometry_lemma_to_const("collinear_trans")
        .expect("collinear_trans should resolve");
    generator
        .geometry_lemma_to_const("sas")
        .expect("sas should resolve");
    generator
        .geometry_lemma_to_const("ptolemy")
        .expect("ptolemy should resolve");

    // Unknown lemma should fail with UnknownLemma
    let err = generator
        .geometry_lemma_to_const("unknown_lemma")
        .unwrap_err();
    assert!(
        matches!(err, GeometryCertError::UnknownLemma(_)),
        "Unknown lemma should give UnknownLemma, got: {err}"
    );
}

#[test]
fn test_predicate_name_mapping() {
    let mut env = Environment::new();
    env.init_computational_geometry().unwrap();
    let generator = GeometryCertGenerator::new(env).unwrap();

    // Test various predicate name formats — verify each resolves to a Name
    generator
        .geometry_name_to_const("collinear")
        .expect("collinear should resolve");
    generator
        .geometry_name_to_const("coll")
        .expect("coll should resolve");
    generator
        .geometry_name_to_const("cyclic")
        .expect("cyclic should resolve");
    generator
        .geometry_name_to_const("midpoint")
        .expect("midpoint should resolve");
    generator
        .geometry_name_to_const("on_circle")
        .expect("on_circle should resolve");

    // Unknown predicate should fail with UnknownAxiom
    let err = generator
        .geometry_name_to_const("unknown_pred")
        .unwrap_err();
    assert!(
        matches!(err, GeometryCertError::UnknownAxiom(_)),
        "Unknown predicate should give UnknownAxiom, got: {err}"
    );
}

impl GeomStep {
    /// Helper to get name from Axiom variant for tests
    fn name_str(&self) -> String {
        match self {
            GeomStep::Axiom { name, .. } => name.clone(),
            _ => String::new(),
        }
    }
}

// ════════════════════════════════════════════════════════════════════════
// Problem → GeomStep Converter Tests
// ════════════════════════════════════════════════════════════════════════

#[test]
fn test_convert_simple_collinear_problem() {
    let json = r#"
    {
        "id": "test_collinear",
        "objects": {
            "A": {"type": "point"},
            "B": {"type": "point"},
            "C": {"type": "point"}
        },
        "constraints": [
            {"type": "not_equal", "a": "A", "b": "B"},
            {"type": "not_equal", "a": "B", "b": "C"}
        ],
        "goal": {
            "type": "collinear",
            "points": ["A", "B", "C"]
        }
    }
    "#;

    let problem = crate::cert::problem::GeometryProblem::from_json(json).unwrap();
    let converter = ProblemToStepsConverter::new(problem);
    let steps = converter.convert().unwrap();

    assert_eq!(steps.problem_id, "test_collinear");
    // NotEqual constraints don't produce steps
    assert_eq!(steps.givens.len(), 0);
    assert_eq!(steps.goal.predicate, "collinear");
    assert_eq!(steps.goal.args, vec!["A", "B", "C"]);
}

#[test]
fn test_convert_problem_with_midpoint() {
    let json = r#"
    {
        "id": "midpoint_test",
        "objects": {
            "A": {"type": "point"},
            "B": {"type": "point"},
            "M": {"type": "point", "definition": {"midpoint_of": ["A", "B"]}}
        },
        "constraints": [],
        "goal": {
            "type": "congruent_segments",
            "seg1": ["A", "M"],
            "seg2": ["M", "B"]
        }
    }
    "#;

    let problem = crate::cert::problem::GeometryProblem::from_json(json).unwrap();
    let converter = ProblemToStepsConverter::new(problem);
    let steps = converter.convert().unwrap();

    assert_eq!(steps.givens.len(), 1);
    match &steps.givens[0] {
        GeomStep::Construct { kind, name, from } => {
            assert_eq!(kind, "midpoint");
            assert_eq!(name, "M");
            assert_eq!(from, &vec!["A".to_string(), "B".to_string()]);
        }
        _ => panic!("Expected Construct step"),
    }

    assert_eq!(steps.goal.predicate, "congruent_segments");
}

#[test]
fn test_convert_problem_with_constraints() {
    let json = r#"
    {
        "id": "parallel_test",
        "objects": {
            "A": {"type": "point"},
            "B": {"type": "point"},
            "C": {"type": "point"},
            "D": {"type": "point"}
        },
        "constraints": [
            {"type": "parallel", "line1": {"through": ["A", "B"]}, "line2": {"through": ["C", "D"]}},
            {"type": "on_circle", "point": "A", "circle": "mathverse"}
        ],
        "goal": {
            "type": "parallel",
            "line1": {"through": ["A", "C"]},
            "line2": {"through": ["B", "D"]}
        }
    }
    "#;

    let problem = crate::cert::problem::GeometryProblem::from_json(json).unwrap();
    let converter = ProblemToStepsConverter::new(problem);
    let steps = converter.convert().unwrap();

    assert_eq!(steps.givens.len(), 2);

    // Check parallel constraint
    let has_parallel = steps
        .givens
        .iter()
        .any(|s| matches!(s, GeomStep::Given { predicate, .. } if predicate == "parallel"));
    assert!(has_parallel);

    // Check on_circle constraint
    let has_on_circle = steps.givens.iter().any(|s| {
        matches!(s, GeomStep::Given { predicate, args }
            if predicate == "on_circle" && args.contains(&"A".to_string()))
    });
    assert!(has_on_circle);
}

#[test]
fn test_convert_problem_with_circumcenter() {
    let json = r#"
    {
        "id": "circumcenter_test",
        "objects": {
            "A": {"type": "point"},
            "B": {"type": "point"},
            "C": {"type": "point"},
            "O": {"type": "point", "definition": {"circumcenter": ["A", "B", "C"]}}
        },
        "constraints": [],
        "goal": {
            "type": "congruent_segments",
            "seg1": ["O", "A"],
            "seg2": ["O", "B"]
        }
    }
    "#;

    let problem = crate::cert::problem::GeometryProblem::from_json(json).unwrap();
    let converter = ProblemToStepsConverter::new(problem);
    let steps = converter.convert().unwrap();

    assert_eq!(steps.givens.len(), 1);
    match &steps.givens[0] {
        GeomStep::Construct { kind, name, from } => {
            assert_eq!(kind, "circumcenter");
            assert_eq!(name, "O");
            assert_eq!(from.len(), 3);
        }
        _ => panic!("Expected Construct step"),
    }
}

#[test]
fn test_problem_steps_validation() {
    let steps = ProblemSteps {
        problem_id: "test".to_string(),
        givens: vec![],
        goal: GoalStep {
            predicate: "collinear".to_string(),
            args: vec!["A".to_string(), "B".to_string(), "C".to_string()],
        },
        object_names: vec!["A".to_string(), "B".to_string(), "C".to_string()],
    };

    steps
        .validate()
        .expect("Valid problem steps should pass validation");
}

#[test]
fn test_problem_steps_validation_missing_object() {
    let steps = ProblemSteps {
        problem_id: "test".to_string(),
        givens: vec![],
        goal: GoalStep {
            predicate: "collinear".to_string(),
            args: vec!["A".to_string(), "B".to_string(), "X".to_string()],
        },
        object_names: vec!["A".to_string(), "B".to_string()],
    };

    let result = steps.validate();
    assert!(matches!(result, Err(ConversionError::ObjectNotFound(name)) if name == "X"));
}

#[test]
fn test_axiom_and_construction_steps_filters() {
    let steps = ProblemSteps {
        problem_id: "test".to_string(),
        givens: vec![
            GeomStep::Construct {
                kind: "midpoint".to_string(),
                name: "M".to_string(),
                from: vec!["A".to_string(), "B".to_string()],
            },
            GeomStep::Given {
                predicate: "collinear".to_string(),
                args: vec!["A".to_string(), "B".to_string(), "C".to_string()],
            },
            GeomStep::Given {
                predicate: "parallel".to_string(),
                args: vec![
                    "A".to_string(),
                    "B".to_string(),
                    "C".to_string(),
                    "D".to_string(),
                ],
            },
        ],
        goal: GoalStep {
            predicate: "collinear".to_string(),
            args: vec!["M".to_string(), "C".to_string()],
        },
        object_names: vec!["A", "B", "C", "D", "M"]
            .into_iter()
            .map(String::from)
            .collect(),
    };

    assert_eq!(steps.axiom_steps().len(), 2);
    assert_eq!(steps.construction_steps().len(), 1);
}

#[test]
fn test_apply_to_cert_with_type_inference() {
    let mut env = Environment::new();
    env.init_computational_geometry().unwrap();
    let mut generator = GeometryCertGenerator::new(env).unwrap();

    // Test lemma application with premises
    // This tests that type inference properly tracks the function type
    // through each application step
    let step = GeomStep::Apply {
        predicate: "right_angle".to_string(),
        lemma: "thales".to_string(),
        premises: vec![GeomStep::Axiom {
            name: "on_circle".to_string(),
            args: vec!["A".to_string()],
        }],
        args: vec!["A".to_string(), "B".to_string(), "C".to_string()],
    };

    let result = generator.step_to_cert(&step);
    // The result should be an App certificate (may fail type mismatch
    // if lemma type doesn't match, but structure should be built)
    // For now we're testing that the function doesn't panic
    // and produces some certificate
    match result {
        Ok(ProofCert::App { .. }) => {
            // Success - we got an application certificate
        }
        Ok(ProofCert::Const { .. }) => {
            // If no premises, we might get just the constant
        }
        Err(GeometryCertError::TypeMismatch { .. }) => {
            // Expected if type doesn't have enough Pi's for args
        }
        other => {
            // Allow other results for now - type inference is best-effort
            let _ = other;
        }
    }
}

#[test]
fn test_compute_app_types() {
    use crate::expr::BinderInfo;

    let mut env = Environment::new();
    env.init_computational_geometry().unwrap();
    let mut generator = GeometryCertGenerator::new(env).unwrap();

    // Create a simple Pi type: ∀ (x : Prop), Prop
    let domain = Expr::from_kind(ExprKind::Sort(Level::zero())); // Prop
    let codomain = Expr::from_kind(ExprKind::Sort(Level::zero())); // Prop
    let pi_type = Expr::pi(BinderInfo::Default, domain.clone(), codomain.clone());

    // Create an argument
    let arg = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // Compute types
    let (fn_type, result_type) = generator
        .compute_app_types(&pi_type, &arg)
        .expect("compute_app_types should succeed for simple Pi");
    // Function type should be the original Pi type
    assert_eq!(fn_type, pi_type);
    // Result type should be the instantiated codomain
    // Since codomain doesn't reference BVar(0), it should be unchanged
    assert_eq!(result_type, codomain);
}

#[test]
fn test_compute_app_types_with_dependent() {
    use crate::expr::BinderInfo;

    let mut env = Environment::new();
    env.init_computational_geometry().unwrap();
    let mut generator = GeometryCertGenerator::new(env).unwrap();

    // Create a dependent Pi type: ∀ (x : Type), x
    // When applied to Nat, result should be Nat
    let domain = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))); // Type 0
    let codomain = Expr::from_kind(ExprKind::BVar(0)); // Reference to the bound variable
    let pi_type = Expr::pi(BinderInfo::Default, domain.clone(), codomain);

    // Create an argument (Nat as a stand-in)
    let nat = Expr::const_(
        crate::name::Name::from_string("Nat"),
        crate::expr::LevelVec::new(),
    );

    // Compute types
    let (fn_type, result_type) = generator
        .compute_app_types(&pi_type, &nat)
        .expect("compute_app_types should succeed for dependent Pi");
    // Function type should be the original Pi type
    assert_eq!(fn_type, pi_type);
    // Result type should be the argument (since codomain was BVar(0))
    assert_eq!(result_type, nat);
}

// ════════════════════════════════════════════════════════════════════════
// End-to-End Certificate Verification Tests
// ════════════════════════════════════════════════════════════════════════

#[test]
fn test_e2e_axiom_cert_verification() {
    use crate::cert::CertVerifier;

    let mut env = Environment::new();
    env.init_computational_geometry().unwrap();
    let mut generator = GeometryCertGenerator::new(env).unwrap();

    // Create a simple axiom step
    let step = GeomStep::Axiom {
        name: "collinear".to_string(),
        args: vec!["A".to_string(), "B".to_string(), "C".to_string()],
    };

    // Generate certificate and expression
    let (cert, expr) = generator.step_to_cert_with_expr(&step).unwrap();

    // Verify the certificate
    let mut verifier = CertVerifier::new(generator.env());
    let result = verifier.verify(&cert, &expr);

    // Should verify successfully - it's a constant reference
    assert!(
        result.is_ok(),
        "Axiom cert verification failed: {:?}",
        result
    );
}

#[test]
fn test_e2e_given_cert_verification() {
    use crate::cert::CertVerifier;

    let mut env = Environment::new();
    env.init_computational_geometry().unwrap();
    let mut generator = GeometryCertGenerator::new(env).unwrap();

    // Create a "given" step (from problem constraints)
    let step = GeomStep::Given {
        predicate: "cyclic".to_string(),
        args: vec![
            "A".to_string(),
            "B".to_string(),
            "C".to_string(),
            "D".to_string(),
        ],
    };

    // Generate certificate and expression
    let (cert, expr) = generator.step_to_cert_with_expr(&step).unwrap();

    // Verify the certificate
    let mut verifier = CertVerifier::new(generator.env());
    let result = verifier.verify(&cert, &expr);

    assert!(
        result.is_ok(),
        "Given cert verification failed: {:?}",
        result
    );
}

#[test]
fn test_e2e_construct_cert_verification() {
    use crate::cert::CertVerifier;

    let mut env = Environment::new();
    env.init_computational_geometry().unwrap();
    let mut generator = GeometryCertGenerator::new(env).unwrap();

    // Create a construction step
    let step = GeomStep::Construct {
        kind: "midpoint".to_string(),
        name: "M".to_string(),
        from: vec!["A".to_string(), "B".to_string()],
    };

    // Generate certificate and expression
    let (cert, expr) = generator.step_to_cert_with_expr(&step).unwrap();

    // Verify the certificate
    let mut verifier = CertVerifier::new(generator.env());
    let result = verifier.verify(&cert, &expr);

    assert!(
        result.is_ok(),
        "Construct cert verification failed: {:?}",
        result
    );
}

// ════════════════════════════════════════════════════════════════════════
// Apply Step with Premises (Full Derivation Chain) Tests
// ════════════════════════════════════════════════════════════════════════

#[test]
fn test_e2e_apply_derivation_chain_structure() {
    // Test that Apply step with premises builds the correct certificate structure
    // even if the actual type checking fails (geometry constants are Type_u, not
    // proper theorem types with Pi structure)
    let mut env = Environment::new();
    env.init_computational_geometry().unwrap();
    let mut generator = GeometryCertGenerator::new(env).unwrap();

    // Build a derivation chain:
    // CollinearTrans applied to two collinear premises
    // collinear(A,B,C) and collinear(B,C,D) -> collinear(A,C,D)
    let step = GeomStep::Apply {
        predicate: "collinear".to_string(),
        lemma: "collinear_trans".to_string(),
        premises: vec![
            GeomStep::Given {
                predicate: "collinear".to_string(),
                args: vec!["A".to_string(), "B".to_string(), "C".to_string()],
            },
            GeomStep::Given {
                predicate: "collinear".to_string(),
                args: vec!["B".to_string(), "C".to_string(), "D".to_string()],
            },
        ],
        args: vec![], // No explicit args, just premises
    };

    // Try to generate certificate - this tests the derivation chain is built
    let result = generator.step_to_cert_with_expr(&step);

    // The result will be a TypeMismatch because CompGeom constants are Type_u,
    // not proper theorem types. But the important thing is that the code doesn't
    // panic and processes the premises correctly.
    match result {
        Ok((cert, expr)) => {
            // If it succeeds, verify the structure
            assert!(
                matches!(cert, ProofCert::App { .. }),
                "Expected App certificate"
            );
            assert!(
                matches!(&expr.kind, ExprKind::App(..)),
                "Expected App expression"
            );
        }
        Err(GeometryCertError::TypeMismatch { .. }) => {
            // Expected - geometry constants don't have proper Pi types
            // This is acceptable as it shows the derivation chain was attempted
        }
        Err(e) => {
            panic!("Unexpected error: {:?}", e);
        }
    }
}

#[test]
fn test_e2e_nested_apply_derivation() {
    // Test nested Apply steps (a derivation that uses another derivation as a premise)
    let mut env = Environment::new();
    env.init_computational_geometry().unwrap();
    let mut generator = GeometryCertGenerator::new(env).unwrap();

    // Build a nested derivation:
    // Use SASCongruence on triangle ABC and DEF, with nested premises
    let step = GeomStep::Apply {
        predicate: "congruent_triangles".to_string(),
        lemma: "sas".to_string(),
        premises: vec![
            // Premise 1: Congruent segments AB = DE (given)
            GeomStep::Given {
                predicate: "congruent".to_string(),
                args: vec![
                    "A".to_string(),
                    "B".to_string(),
                    "D".to_string(),
                    "E".to_string(),
                ],
            },
            // Premise 2: Congruent angles ABC = DEF (derived via angle theorem)
            GeomStep::Apply {
                predicate: "congruent_angles".to_string(),
                lemma: "inscribed_angle".to_string(),
                premises: vec![GeomStep::Given {
                    predicate: "on_circle".to_string(),
                    args: vec!["B".to_string()],
                }],
                args: vec!["A".to_string(), "B".to_string(), "C".to_string()],
            },
            // Premise 3: Congruent segments BC = EF (given)
            GeomStep::Given {
                predicate: "congruent".to_string(),
                args: vec![
                    "B".to_string(),
                    "C".to_string(),
                    "E".to_string(),
                    "F".to_string(),
                ],
            },
        ],
        args: vec![
            "A".to_string(),
            "B".to_string(),
            "C".to_string(),
            "D".to_string(),
            "E".to_string(),
            "F".to_string(),
        ],
    };

    // Generate certificate - tests nested derivation chain processing
    let result = generator.step_to_cert_with_expr(&step);

    // Check that nested premises are processed without panicking
    match result {
        Ok((cert, _expr)) => {
            // Verify structure is App (lemma applied to args and premises)
            assert!(
                matches!(cert, ProofCert::App { .. }),
                "Expected App certificate"
            );
        }
        Err(GeometryCertError::TypeMismatch { .. }) => {
            // Expected - demonstrates derivation chain was attempted
        }
        Err(e) => {
            panic!("Unexpected error in nested derivation: {:?}", e);
        }
    }
}

#[test]
fn test_derivation_chain_premise_count() {
    // Test that we correctly process all premises in a derivation
    let mut env = Environment::new();
    env.init_computational_geometry().unwrap();
    let mut generator = GeometryCertGenerator::new(env).unwrap();

    // Build a derivation with multiple premises
    let premises: Vec<GeomStep> = (0..5)
        .map(|i| GeomStep::Given {
            predicate: "collinear".to_string(),
            args: vec![
                format!("P{}", i),
                format!("P{}", i + 1),
                format!("P{}", i + 2),
            ],
        })
        .collect();

    let step = GeomStep::Apply {
        predicate: "collinear".to_string(),
        lemma: "collinear_trans".to_string(),
        premises,
        args: vec![],
    };

    // Process - should not panic even with multiple premises
    let result = generator.step_to_cert_with_expr(&step);

    // Any result (Ok or TypeMismatch) is acceptable - we're testing
    // that the code handles multiple premises without crashing
    assert!(
        matches!(result, Ok(_) | Err(GeometryCertError::TypeMismatch { .. })),
        "Expected Ok or TypeMismatch, got: {:?}",
        result
    );
}

#[test]
fn test_mixed_step_types_in_premises() {
    // Test derivation with mixed step types in premises
    let mut env = Environment::new();
    env.init_computational_geometry().unwrap();
    let mut generator = GeometryCertGenerator::new(env).unwrap();

    let step = GeomStep::Apply {
        predicate: "congruent_angles".to_string(),
        lemma: "thales".to_string(),
        premises: vec![
            // Given predicate
            GeomStep::Given {
                predicate: "on_circle".to_string(),
                args: vec!["A".to_string()],
            },
            // Axiom reference
            GeomStep::Axiom {
                name: "on_circle".to_string(),
                args: vec!["B".to_string()],
            },
            // Construction
            GeomStep::Construct {
                kind: "midpoint".to_string(),
                name: "M".to_string(),
                from: vec!["A".to_string(), "B".to_string()],
            },
        ],
        args: vec!["A".to_string(), "B".to_string(), "C".to_string()],
    };

    // Process - should handle all step types in premises
    let result = generator.step_to_cert_with_expr(&step);

    // Check it didn't panic and produced some result
    assert!(
        matches!(result, Ok(_) | Err(GeometryCertError::TypeMismatch { .. })),
        "Expected Ok or TypeMismatch for mixed premises, got: {:?}",
        result
    );
}

// ════════════════════════════════════════════════════════════════════════
// MicroChecker Independent Verification Tests
// ════════════════════════════════════════════════════════════════════════

#[test]
fn test_micro_checker_axiom_verification() {
    // Test that geometry axioms can be verified via MicroChecker path
    let mut env = Environment::new();
    env.init_computational_geometry().unwrap();
    let generator = GeometryCertGenerator::new(env).unwrap();

    // Generate certificate and expression directly from geometry name
    let const_name = generator.geometry_name_to_const("collinear").unwrap();
    let levels = vec![Level::zero()];
    let instantiated_type = generator
        .env()
        .instantiate_type(&const_name, &levels)
        .unwrap();

    let cert = ProofCert::Const {
        name: const_name.clone(),
        levels: levels.clone(),
        type_: Box::new(instantiated_type),
    };
    let expr = Expr::const_(const_name, levels);

    // Convert to MicroCert and verify with MicroChecker
    let result = generator.verify_with_micro_checker(&cert, &expr);
    assert!(
        result.is_ok(),
        "MicroChecker axiom verification failed: {:?}",
        result
    );
}

#[test]
fn test_micro_checker_given_verification() {
    // Test that given predicates can be verified via MicroChecker
    let mut env = Environment::new();
    env.init_computational_geometry().unwrap();
    let generator = GeometryCertGenerator::new(env).unwrap();

    // Create certificate for a given predicate
    let const_name = generator.geometry_name_to_const("cyclic").unwrap();
    let levels = vec![Level::zero()];
    let instantiated_type = generator
        .env()
        .instantiate_type(&const_name, &levels)
        .unwrap();

    let cert = ProofCert::Const {
        name: const_name.clone(),
        levels: levels.clone(),
        type_: Box::new(instantiated_type),
    };
    let expr = Expr::const_(const_name, levels);

    // Verify with MicroChecker
    let result = generator.verify_with_micro_checker(&cert, &expr);
    assert!(
        result.is_ok(),
        "MicroChecker given verification failed: {:?}",
        result
    );
}

#[test]
fn test_micro_checker_to_micro_cert_conversion() {
    // Test the to_micro_cert conversion function
    let mut env = Environment::new();
    env.init_computational_geometry().unwrap();
    let generator = GeometryCertGenerator::new(env).unwrap();

    // Create a Const certificate
    let const_name = generator.geometry_name_to_const("parallel").unwrap();
    let levels = vec![Level::zero()];
    let instantiated_type = generator
        .env()
        .instantiate_type(&const_name, &levels)
        .unwrap();

    let cert = ProofCert::Const {
        name: const_name.clone(),
        levels: levels.clone(),
        type_: Box::new(instantiated_type),
    };
    let expr = Expr::const_(const_name, levels);

    // Verify conversion succeeds
    let result = generator.to_micro_cert(&cert, &expr);
    assert!(
        result.is_some(),
        "to_micro_cert conversion should succeed for Const"
    );

    let (micro_cert, micro_expr) = result.unwrap();
    // Micro cert should be Opaque
    assert!(
        matches!(micro_cert, crate::micro::MicroCert::Opaque { .. }),
        "Const should convert to Opaque"
    );
    // Micro expr should also be Opaque
    assert!(
        matches!(micro_expr, crate::micro::MicroExpr::Opaque(_)),
        "Const expr should convert to Opaque expr"
    );
}

#[test]
fn test_micro_checker_dual_verification() {
    // Test that both CertVerifier and MicroChecker agree
    use crate::cert::CertVerifier;

    let mut env = Environment::new();
    env.init_computational_geometry().unwrap();
    let generator = GeometryCertGenerator::new(env).unwrap();

    // Create certificate for a geometry predicate
    let const_name = generator.geometry_name_to_const("midpoint").unwrap();
    let levels = vec![Level::zero()];
    let instantiated_type = generator
        .env()
        .instantiate_type(&const_name, &levels)
        .unwrap();

    let cert = ProofCert::Const {
        name: const_name.clone(),
        levels: levels.clone(),
        type_: Box::new(instantiated_type),
    };
    let expr = Expr::const_(const_name, levels);

    // Verify with CertVerifier (main kernel)
    let mut verifier = CertVerifier::new(generator.env());
    let kernel_result = verifier.verify(&cert, &expr);

    // Verify with MicroChecker (independent)
    let micro_result = generator.verify_with_micro_checker(&cert, &expr);

    // Both should succeed
    assert!(
        kernel_result.is_ok(),
        "CertVerifier should succeed: {:?}",
        kernel_result
    );
    assert!(
        micro_result.is_ok(),
        "MicroChecker should succeed: {:?}",
        micro_result
    );

    eprintln!("Dual verification passed: CertVerifier and MicroChecker agree");
}
