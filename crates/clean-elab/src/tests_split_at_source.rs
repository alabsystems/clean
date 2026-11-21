//! Source-level location and proof-extraction controls for `split at h`.

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::Environment;

pub(crate) fn elaborate(source: &str) -> Result<Environment, String> {
    let report =
        clean_parser::parse_file_with_diagnostics(source).map_err(|error| format!("{error:?}"))?;
    if !report.diagnostics.is_empty() {
        return Err(format!("parser recovery: {:?}", report.diagnostics));
    }
    let mut environment = Environment::with_prelude();
    for declaration in &report.decls {
        elaborate_decl_and_register_with_warning(&mut environment, declaration)
            .map_err(|error| format!("{error:?}"))?;
    }
    Ok(environment)
}

pub(crate) const POSITIVE: [(&str, &str); 2] = [
    (
        "split_hyp",
        include_str!("../tests/fixtures/split_at/hyp.lean"),
    ),
    (
        "split_dependent",
        include_str!("../tests/fixtures/split_at/dependent.lean"),
    ),
];

pub(crate) const NEGATIVE: [&str; 2] = [
    include_str!("../tests/fixtures/split_at/wrong_result.lean"),
    include_str!("../tests/fixtures/split_at/wrong_location.lean"),
];

pub(crate) const MATCH_POSITIVE: [(&str, &str); 2] = [
    (
        "split_match",
        include_str!("../tests/fixtures/split_at/match.lean"),
    ),
    (
        "split_match_dependent",
        include_str!("../tests/fixtures/split_at/match_dependent.lean"),
    ),
];

pub(crate) const MATCH_NEGATIVE: [&str; 2] = [
    include_str!("../tests/fixtures/split_at/match_wrong_result.lean"),
    include_str!("../tests/fixtures/split_at/match_wrong_location.lean"),
];

#[test]
fn split_at_source_preserves_hypothesis_name_and_proof() {
    elaborate(POSITIVE[0].1)
        .expect("the named hypothesis must be restored in both checked branches");
}

#[test]
fn split_at_source_preserves_dependent_hypotheses() {
    elaborate(POSITIVE[1].1).expect("dependent locals must remain well typed after splitting");
}

#[test]
fn split_at_source_refuses_wrong_result() {
    assert!(elaborate(NEGATIVE[0]).is_err());
}

#[test]
fn split_at_source_does_not_use_an_if_in_another_location() {
    assert!(elaborate(NEGATIVE[1]).is_err());
}

#[test]
fn split_at_source_handles_match_discriminants() {
    elaborate(MATCH_POSITIVE[0].1)
        .expect("the match discriminant must refine the named hypothesis");
}

#[test]
fn split_at_source_match_preserves_dependent_hypotheses() {
    elaborate(MATCH_POSITIVE[1].1)
        .expect("dependent locals must remain checked in every match branch");
}

#[test]
fn split_at_source_match_refuses_wrong_result() {
    assert!(elaborate(MATCH_NEGATIVE[0]).is_err());
}

#[test]
fn split_at_source_does_not_use_a_match_in_another_location() {
    assert!(elaborate(MATCH_NEGATIVE[1]).is_err());
}

#[test]
fn split_at_source_match_abstracts_a_projection_in_hypothesis_and_goal() {
    elaborate(include_str!(
        "../tests/fixtures/split_at/match_projection.lean"
    ))
    .expect("the projection must be abstracted through the complete reverted goal");
}

#[test]
fn split_at_source_match_restores_locals_in_every_constructor_branch() {
    elaborate(include_str!("../tests/fixtures/split_at/match_three.lean"))
        .expect("the named hypothesis must be restored in all three branches");
}

#[test]
fn split_at_source_match_refuses_a_discriminant_bound_inside_the_hypothesis() {
    assert!(elaborate(include_str!("../tests/fixtures/split_at/match_bound.lean")).is_err());
}

#[test]
fn split_at_source_match_does_not_let_a_constructor_field_steal_the_hypothesis_name() {
    elaborate(include_str!(
        "../tests/fixtures/split_at/match_named_field.lean"
    ))
    .expect("exact must resolve the restored source hypothesis, not the generated Bool field");
}

#[test]
fn split_at_source_match_named_field_cannot_justify_an_opposite_result() {
    assert!(elaborate(include_str!(
        "../tests/fixtures/split_at/match_named_field_wrong.lean"
    ))
    .is_err());
}

#[test]
fn split_at_record_match_refines_its_projected_discriminant() {
    elaborate(include_str!(
        "../tests/fixtures/split_at/match_record_projection.lean"
    ))
    .expect("the stored record field must agree with the accepted branch");
    assert!(elaborate(include_str!(
        "../tests/fixtures/split_at/match_record_projection_wrong.lean"
    ))
    .is_err());
}

#[test]
fn split_at_checks_nested_field_patterns_and_preserves_operand_order() {
    let env = elaborate(include_str!(
        "../tests/fixtures/split_at/nested_record.lean"
    ))
    .expect("all constructor tests of the record and singleton-list pattern must be refined");
    assert!(env
        .get_const(&clean_kernel::Name::from_string("readAndNode_sound"))
        .is_some());
    assert!(elaborate(include_str!(
        "../tests/fixtures/split_at/nested_record_swapped.lean"
    ))
    .is_err());
}
