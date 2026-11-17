//! Pinned Lean's minor premise abstracts inside a lambda-valued index.
use super::*;
const INPUT: &str = include_str!("../../tests/fixtures/lambda-index.ndjson");
#[test]
fn lambda_index_recursor_matches_pinned_lean() {
    let report = replay(INPUT.as_bytes(), Dialect::Lean4Export31).unwrap();
    assert_eq!(report.counts(), (3, BTreeMap::new()));
}
#[test]
fn lambda_index_forged_recursor_conclusion_is_refused() {
    // Preserve all telescope domains and the admitted family. Only change the
    // recursor's final conclusion from `motive index major` to `Prop`.
    let mut changed = false;
    let forged = INPUT
        .lines()
        .map(|line| {
            let mut value: Value = serde_json::from_str(line).unwrap();
            if value.get("ie").and_then(Value::as_u64) == Some(37) {
                assert_eq!(value["forallE"]["body"], 36);
                value["forallE"]["body"] = Value::from(4);
                changed = true;
            }
            serde_json::to_string(&value).unwrap() + "\n"
        })
        .collect::<String>();
    assert!(changed);
    let report = replay(forged.as_bytes(), Dialect::Lean4Export31).unwrap();
    assert_eq!(report.rows.len(), 3);
    for row in report.rows {
        let error = row.verdict.unwrap_err();
        assert_eq!(error.reason(), "malformed");
        assert!(
            error.to_string().contains("recursor type mismatch"),
            "{error}"
        );
    }
}

#[test]
fn open_addition_through_a_projection_stays_lazy() {
    let input = include_str!("../../tests/fixtures/projection-addition.ndjson");
    let report = replay(input.as_bytes(), Dialect::Lean4Export31).unwrap();
    assert_eq!(report.counts(), (33, BTreeMap::new()));
}

#[test]
fn projection_retry_precedes_expensive_false_argument_congruence() {
    let input = include_str!("../../tests/fixtures/lazy-successor.ndjson");
    let report = replay(input.as_bytes(), Dialect::Lean4Export31).unwrap();
    assert_eq!(report.counts(), (55, BTreeMap::new()));
}
