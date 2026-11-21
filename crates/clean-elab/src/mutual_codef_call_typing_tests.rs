// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{Environment, Name};

fn checked(
    env: &mut Environment,
    declaration: &clean_parser::SurfaceDecl,
) -> Result<(), crate::ElabError> {
    let result = crate::elaborate_decl_and_register(env, declaration)?;
    let mut leaves = Vec::new();
    result.leaf_decls(&mut leaves);
    for leaf in leaves {
        if let crate::ElabResult::Failed { error, .. } = leaf {
            return Err((**error).clone());
        }
    }
    Ok(())
}

#[test]
fn mutual_codef_bad_calls_refuse_before_any_member_registers() {
    for (label, source) in [
        (
            "wrong member",
            include_str!(
                "../../../tests/fixtures/mutual_codef_call_typing/wrong_callee_heads.lean"
            ),
        ),
        (
            "wrong parameters",
            include_str!(
                "../../../tests/fixtures/mutual_codef_call_typing/wrong_result_parameters.lean"
            ),
        ),
        (
            "observation call",
            include_str!(
                "../../../tests/fixtures/mutual_codef_call_typing/wrong_observation_call.lean"
            ),
        ),
        (
            "wrong state",
            include_str!("../../../tests/fixtures/mutual_codef_call_typing/wrong_state_type.lean"),
        ),
        (
            "shadowed callee",
            include_str!("../../../tests/fixtures/mutual_codef_call_typing/shadowed_callee.lean"),
        ),
        (
            "nonplain call",
            include_str!("../../../tests/fixtures/mutual_codef_call_typing/nonplain_call.lean"),
        ),
    ] {
        let declarations = clean_parser::parse_file(source).expect("control parses");
        assert_eq!(declarations.len(), 2, "{label}");
        let mut env = Environment::with_prelude();
        checked(&mut env, &declarations[0]).expect("both real codata members register");
        for owner in ["ReviewLeft", "ReviewRight"] {
            assert!(
                env.get_const(&Name::from_string(owner)).is_some(),
                "{label}: {owner}"
            );
        }
        let before = env.constants().count();
        let origins = env.codata_origin_count();
        let error = match checked(&mut env, &declarations[1]) {
            Err(error) => error,
            Ok(()) => panic!("{label}: bad authored call must refuse"),
        };
        assert!(
            error.to_string().contains(match label {
                "wrong state" => "generated corecursor application",
                "nonplain call" => "is not a plain call",
                _ => "authored recursive call failed type checking",
            }),
            "{label}: {error}"
        );
        assert_eq!(env.constants().count(), before, "{label}");
        assert_eq!(env.codata_origin_count(), origins, "{label}");
        for owner in ["reviewLeft", "reviewRight"] {
            assert!(
                env.get_const(&Name::from_string(owner)).is_none(),
                "{label}: {owner}"
            );
        }
    }
}

#[test]
fn mutual_codef_valid_generic_zero_and_typed_names_keep_checked_computation() {
    for (label, source, members) in [
        (
            "ordinary",
            include_str!("../../../tests/fixtures/mutual_codef_call_typing/valid.lean"),
            ["reviewLeft", "reviewRight"],
        ),
        (
            "zero state",
            include_str!("../../../tests/fixtures/mutual_codef_call_typing/zero_state.lean"),
            ["reviewLeft", "reviewRight"],
        ),
        (
            "definitionally equal parameters",
            include_str!("../../../tests/fixtures/mutual_codef_call_typing/defeq_parameters.lean"),
            ["reviewLeft", "reviewRight"],
        ),
        (
            "generic distinct states",
            include_str!(
                "../../../tests/fixtures/mutual_codef_call_typing/generic_distinct_states.lean"
            ),
            ["genericLeft", "genericRight"],
        ),
        (
            "quoted names",
            include_str!("../../../tests/fixtures/mutual_codef_call_typing/quoted_names.lean"),
            ["left.fn", "right.fn"],
        ),
        (
            "qualified calls",
            include_str!("../../../tests/fixtures/mutual_codef_call_typing/qualified_calls.lean"),
            ["ReviewCalls.left", "ReviewCalls.right"],
        ),
    ] {
        let mut env = Environment::with_prelude();
        for declaration in clean_parser::parse_file(source).expect("source control parses") {
            checked(&mut env, &declaration).unwrap_or_else(|error| panic!("{label}: {error}"));
        }
        for owner in members {
            let name = if label == "quoted names" {
                Name::anon().str(owner)
            } else {
                Name::from_string(owner)
            };
            assert!(env.get_const(&name).is_some(), "{label}: {name}");
            assert!(
                env.axiom_deps(&name)
                    .expect("checked dependency closure")
                    .is_empty(),
                "{label}: {name}"
            );
            assert!(
                env.trust_marker_deps(&name)
                    .expect("checked trust closure")
                    .is_empty(),
                "{label}: {name}"
            );
        }
    }
}

/// A codef parameter written `(s : _)` is refused. Main's declaration
/// inference (8c866b7fe8) requires header holes to be resolved before the body
/// is processed, so the generated corecursor application refuses. The pin
/// fails loudly the day that changes, and the fixture then belongs back
/// among the positives above.
#[test]
fn mutual_codef_inferred_state_header_hole_is_refused_before_registration() {
    let source =
        include_str!("../../../tests/fixtures/mutual_codef_call_typing/inferred_state.lean");
    let declarations = clean_parser::parse_file(source).expect("inferred-state control parses");
    assert_eq!(declarations.len(), 2);
    let mut env = Environment::with_prelude();
    checked(&mut env, &declarations[0]).expect("both real codata members register");
    let before = env.constants().count();
    let error = checked(&mut env, &declarations[1]).expect_err("header hole refuses");
    let text = error.to_string();
    assert!(
        text.contains("generated corecursor application")
            && text.contains("header holes must be resolved before the body is processed"),
        "{text}"
    );
    assert_eq!(env.constants().count(), before);
    for member in ["reviewLeft", "reviewRight"] {
        assert!(
            env.get_const(&Name::from_string(member)).is_none(),
            "{member}"
        );
    }
}

#[test]
fn mutual_codef_ordinary_typed_call_still_refuses_wrong_member() {
    let source = include_str!(
        "../../../tests/fixtures/mutual_codef_call_typing/explicit_wrong_callee_refusal.lean"
    );
    let declarations = clean_parser::parse_file(source).expect("ordinary twin parses");
    assert_eq!(declarations.len(), 3);
    let mut env = Environment::with_prelude();
    for declaration in &declarations[..2] {
        checked(&mut env, declaration).expect("valid mutual setup registers");
    }
    for member in ["reviewLeft", "reviewRight"] {
        assert!(env.get_const(&Name::from_string(member)).is_some());
    }
    let before = env.constants().count();
    let error = checked(&mut env, &declarations[2]).expect_err("wrong ordinary call refuses");
    assert!(
        error.to_string().contains("expected ReviewRight Nat"),
        "{error}"
    );
    assert!(error.to_string().contains("ReviewLeft Nat"), "{error}");
    assert_eq!(env.constants().count(), before);
    assert!(env.get_const(&Name::from_string("reviewBad")).is_none());
}
