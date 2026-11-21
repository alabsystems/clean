// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests of the section-4 board, `status` and multi-figure `check`.

use super::*;

fn survey(root: &Path) -> Value {
    serde_json::to_value(status::survey(root).unwrap()).unwrap()
}

fn row<'rows>(rows: &'rows Value, id: &str) -> &'rows Value {
    rows.as_array()
        .unwrap()
        .iter()
        .find(|row| row["id"] == id)
        .unwrap_or_else(|| panic!("no row {id}"))
}

#[test]
fn test_survey_historical_rows_keep_consistency_distinct_from_freshness() {
    let root = tempfile::tempdir().unwrap();
    let (clean, clean_board) = clean_example();
    let (trust, mut board) = example();
    board["headline"]["planted_false_mints_clean"] =
        clean_board["headline"]["planted_false_mints_clean"].clone();
    write_fixture(root.path(), CLEAN_PINS, &clean);
    write_fixture(root.path(), TRUST_PINS, &trust);
    write_fixture(root.path(), SCOREBOARD, &board);

    let rows = survey(root.path());
    for id in [CLEAN_FIGURE, TRUST_FIGURE] {
        let row = row(&rows, id);
        assert_eq!(row["board_row"], 2);
        assert_eq!(row["state"], "measured");
        assert_eq!(row["freshness"]["state"], "unknown");
    }
    assert_eq!(row(&rows, CLEAN_FIGURE)["commit"], clean["measured_commit"]);
    assert_eq!(row(&rows, CLEAN_FIGURE)["denominator"]["count"], 3);
    assert_eq!(row(&rows, TRUST_FIGURE)["value"]["minted_under_mutant"], 2);
    assert_eq!(
        row(&rows, TRUST_FIGURE)["value"]["clean_pin_in_trust"],
        trust["clean_pin_in_trust"]
    );

    // Independently decode the relevant W0 row when a sibling is invalid.
    board["headline"]["planted_false_mints_clean"] = json!("invalid");
    write_fixture(root.path(), SCOREBOARD, &board);
    let rows = survey(root.path());
    assert_eq!(row(&rows, CLEAN_FIGURE)["state"], "inconsistent");
    assert!(row(&rows, CLEAN_FIGURE).get("value").is_none());
    assert!(row(&rows, CLEAN_FIGURE)["reason"]
        .as_str()
        .unwrap()
        .contains(SCOREBOARD));
    assert_eq!(row(&rows, TRUST_FIGURE)["state"], "measured");

    fs::remove_file(root.path().join(TRUST_PINS)).unwrap();
    let rows = survey(root.path());
    assert_eq!(row(&rows, TRUST_FIGURE)["state"], "unavailable");
    assert!(row(&rows, TRUST_FIGURE).get("value").is_none());
    assert!(row(&rows, TRUST_FIGURE)["reason"]
        .as_str()
        .unwrap()
        .contains(TRUST_PINS));
}

#[test]
fn test_survey_board_order_then_other_figures_with_absent_reasons() {
    let root = tempfile::tempdir().unwrap();
    let all = survey(root.path());
    let rows = all.as_array().unwrap();
    let positions: Vec<Option<u64>> = rows.iter().map(|row| row["board_row"].as_u64()).collect();
    let board_end = positions.iter().position(Option::is_none).unwrap();
    assert!(positions[..board_end]
        .windows(2)
        .all(|pair| pair[0] <= pair[1]));
    assert!(positions[board_end..].iter().all(Option::is_none));
    assert_eq!(positions[0], Some(1));
    assert_eq!(positions[board_end - 1], Some(17));
    let python = row(&all, "tooling.python_minters");
    assert_eq!(python["board_row"], 16);
    assert_eq!(python["state"], "unavailable");
    assert_eq!(python["registered"], true);
    assert!(python["reason"]
        .as_str()
        .unwrap()
        .contains("python_minters_evidence.json"));
    assert_eq!(rows.len(), FIGURES.len());
    let rust_model: Vec<&str> = rows
        .iter()
        .filter(|row| row["board_row"] == 12)
        .map(|row| row["id"].as_str().unwrap())
        .collect();
    assert_eq!(
        rust_model,
        [
            "model.rust.instg_in_semr",
            "model.rust.minitests_in_core",
            "model.rust.divergence_rows_with_lemma",
            "model.rust.prod_equiv_bodies",
            "model.rust.rm_accept",
        ]
    );
    let stale = row(&all, evaluate::STALE_FIGURE);
    assert_eq!(stale["denominator"]["count"], rows.len() - 1);
    assert_eq!(
        stale["value"]["absent"],
        rows.iter().filter(|row| row["state"] == "absent").count()
    );
}

#[test]
fn test_status_markdown_renders_every_row_with_absent_reasons() {
    let root = tempfile::tempdir().unwrap();
    let rows = status::survey(root.path()).unwrap();
    let mut rendered = Vec::new();
    status::write_markdown(&rows, &mut rendered).unwrap();
    let rendered = String::from_utf8(rendered).unwrap();
    let table_rows = rendered
        .lines()
        .filter(|line| line.starts_with("| ") && !line.starts_with("| #"))
        .count();
    assert_eq!(table_rows, rows.len());
    assert!(rendered.contains("| 16 | `tooling.python_minters` | unavailable: "));
    assert!(rendered.contains("| 17 | `evidence.stale_figures` |"));
    assert!(rendered.contains("|  3 | `alignment.functions` | absent: "));
}

#[test]
fn test_catalog_absences_report_the_same_reason_without_a_checkout() {
    let root = tempfile::tempdir().unwrap();
    let missing = root.path().join("missing");
    let rows = survey(&missing);
    let absent: Vec<_> = FIGURES
        .iter()
        .filter_map(|figure| figure.absent_reason().map(|reason| (figure, reason)))
        .collect();
    assert_eq!(absent.len(), 15);
    for (figure, reason) in absent {
        let shown = row(&rows, figure.id);
        assert_eq!(shown["registered"], true);
        assert_eq!(shown["state"], "absent");
        assert_eq!(shown["reason"], reason);
        for field in ["value", "denominator", "freshness"] {
            assert!(shown.get(field).is_none(), "{} has {field}", figure.id);
        }
        assert_eq!(
            verdict(figure, figure.read(&missing)).unwrap(),
            format!("{} — absent: {reason}", figure.id)
        );
        let mut explanation = Vec::new();
        provenance::write_explanation(figure, &missing, &mut explanation).unwrap();
        let text = String::from_utf8(explanation).unwrap();
        assert!(text.contains(reason), "{text}");
        assert!(text.contains(figure.plan_unit), "{text}");
        assert!(!text.contains("manual inventory"), "{text}");
    }
}

#[test]
fn test_check_all_missing_inputs_is_not_knowable_here() {
    let root = tempfile::tempdir().unwrap();
    let error = run(&[], true, Some(root.path())).unwrap_err();
    assert_eq!(crate::forwarded_exit_code(&error), Some(3));
    assert!(error.to_string().contains("not knowable here"));
}

#[test]
fn test_check_several_figures_red_outranks_unavailable() {
    let (report, mut scoreboard) = example();
    scoreboard["headline"]["planted_false_mints_trust"]["sites"] = json!(4);
    let root = tempfile::tempdir().unwrap();
    write_fixture(root.path(), TRUST_PINS, &report);
    write_fixture(root.path(), SCOREBOARD, &scoreboard);
    let figures = [TRUST_FIGURE.to_owned(), CLEAN_FIGURE.to_owned()];
    let error = run(&figures, false, Some(root.path())).unwrap_err();
    assert_eq!(crate::forwarded_exit_code(&error), Some(1));
    assert!(error.to_string().contains(TRUST_FIGURE));
}

#[test]
fn test_check_no_figure_and_no_all_is_usage() {
    let error = run(&[], false, None).unwrap_err();
    assert_eq!(crate::forwarded_exit_code(&error), Some(2));
}

#[test]
fn test_status_text_escapes_control_characters_and_keeps_quotes() {
    let rows = [status::StatusRow {
        board_row: None,
        id: "example",
        registered: true,
        state: status::RowState::Inconsistent {
            reason: "line one\nsaid \"two\"".to_owned(),
        },
    }];
    let mut output = Vec::new();
    status::write_text(&rows, &mut output).unwrap();
    let output = String::from_utf8(output).unwrap();
    assert_eq!(
        output,
        "-- example — inconsistent: line one\\nsaid \"two\"\n"
    );
}
