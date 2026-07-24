// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::test_support::create_test_suite;
use super::*;
use tempfile::TempDir;

#[test]
fn test_run_single_requires_final_step_to_match_goal() {
    let temp = TempDir::new().unwrap();
    let suite_dir = temp.path().join("goal_mismatch_suite");
    std::fs::create_dir_all(&suite_dir).unwrap();

    let problem_dir = suite_dir.join("goal_mismatch");
    std::fs::create_dir_all(&problem_dir).unwrap();
    std::fs::write(
        problem_dir.join("problem.json"),
        r#"{
            "id": "goal_mismatch",
            "objects": {
                "A": {"type": "point"},
                "B": {"type": "point"},
                "C": {"type": "point"},
                "D": {"type": "point"}
            },
            "constraints": [],
            "goal": {"type": "collinear", "points": ["A", "B", "C"]}
        }"#,
    )
    .unwrap();
    std::fs::write(
        problem_dir.join("derivation.txt"),
        "DERIVE parallel(A, B, C, D) FROM midpoint_theorem\n",
    )
    .unwrap();

    let mut runner = BenchmarkRunner::new(&suite_dir)
        .unwrap()
        .with_config(BenchmarkConfig {
            verify_certs: false,
            continue_on_error: true,
            ..Default::default()
        });

    let results = runner.run_all().unwrap();
    assert_eq!(results.total, 1);
    assert_eq!(results.solved, 0);
    assert_eq!(results.unsolved, 1);
    assert!(results.results[0]
        .error
        .as_deref()
        .is_some_and(|msg| msg.contains("Goal mismatch")));
}

#[test]
fn test_run_single_accepts_matching_final_apply_goal() {
    let temp = TempDir::new().unwrap();
    let suite_dir = temp.path().join("goal_match_suite");
    std::fs::create_dir_all(&suite_dir).unwrap();

    let problem_dir = suite_dir.join("goal_match");
    std::fs::create_dir_all(&problem_dir).unwrap();
    std::fs::write(
        problem_dir.join("problem.json"),
        r#"{
            "id": "goal_match",
            "objects": {
                "A": {"type": "point"},
                "B": {"type": "point"},
                "C": {"type": "point"}
            },
            "constraints": [],
            "goal": {"type": "collinear", "points": ["A", "B", "C"]}
        }"#,
    )
    .unwrap();
    std::fs::write(
        problem_dir.join("derivation.txt"),
        "DERIVE collinear(A, B, C) FROM midpoint_theorem\n",
    )
    .unwrap();

    let mut runner = BenchmarkRunner::new(&suite_dir)
        .unwrap()
        .with_config(BenchmarkConfig {
            verify_certs: false,
            continue_on_error: true,
            ..Default::default()
        });

    let results = runner.run_all().unwrap();
    assert_eq!(results.total, 1);
    assert_eq!(results.solved, 1);
    assert_eq!(results.unsolved, 0);
    assert_eq!(results.results[0].error, None);
}

#[test]
fn test_run_single_accepts_alpha_geometry_alias_goal_match() {
    let temp = TempDir::new().unwrap();
    let suite_dir = temp.path().join("alpha_goal_match_suite");
    std::fs::create_dir_all(&suite_dir).unwrap();

    let problem_dir = suite_dir.join("alpha_goal_match");
    std::fs::create_dir_all(&problem_dir).unwrap();
    std::fs::write(
        problem_dir.join("problem.json"),
        r#"{
            "id": "alpha_goal_match",
            "objects": {
                "A": {"type": "point"},
                "B": {"type": "point"},
                "C": {"type": "point"}
            },
            "constraints": [],
            "goal": {"type": "collinear", "points": ["A", "B", "C"]}
        }"#,
    )
    .unwrap();
    // Use full alpha geometry derivation format with explicit premise for reliable parsing
    std::fs::write(
        problem_dir.join("derivation.txt"),
        "A B C coll <- A B C coll\n",
    )
    .unwrap();

    let mut runner = BenchmarkRunner::new(&suite_dir)
        .unwrap()
        .with_config(BenchmarkConfig {
            verify_certs: false,
            continue_on_error: true,
            ..Default::default()
        });

    let results = runner.run_all().unwrap();
    assert_eq!(results.total, 1);
    assert_eq!(
        results.results[0].error, None,
        "unexpected error in alpha geometry alias test: {:?}",
        results.results[0]
    );
    assert_eq!(results.solved, 1);
    assert_eq!(results.unsolved, 0);
}

#[test]
fn test_create_test_suite_still_produces_matching_goal() {
    let (_temp, suite_dir) = create_test_suite();
    let mut runner = BenchmarkRunner::new(&suite_dir)
        .unwrap()
        .with_config(BenchmarkConfig {
            verify_certs: false,
            ..Default::default()
        });
    let problems = runner.discover_problems().unwrap();
    let result = runner.run_single(&problems[0]).unwrap();
    assert!(result.error.is_none());
}
