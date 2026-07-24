// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;
use tempfile::TempDir;

pub(super) fn create_test_suite() -> (TempDir, PathBuf) {
    let temp = TempDir::new().expect("test suite tempdir should be creatable");
    let suite_dir = temp.path().join("test_suite");
    std::fs::create_dir_all(&suite_dir).expect("test suite directory should be creatable");

    // Create a test problem
    let problem_dir = suite_dir.join("test_problem_1");
    std::fs::create_dir_all(&problem_dir).expect("test problem directory should be creatable");

    let problem_json = r#"
    {
        "id": "test_problem_1",
        "objects": {
            "A": {"type": "point"},
            "B": {"type": "point"},
            "C": {"type": "point"}
        },
        "constraints": [
            {"type": "not_equal", "a": "A", "b": "B"}
        ],
        "goal": {"type": "collinear", "points": ["A", "B", "C"]}
    }
    "#;
    std::fs::write(problem_dir.join("problem.json"), problem_json)
        .expect("test problem.json should be writable");

    let derivation = r#"
    GIVEN not_equal(A, B)
    AXIOM collinear(A, B, C)
    "#;
    std::fs::write(problem_dir.join("derivation.txt"), derivation)
        .expect("test derivation should be writable");

    (temp, suite_dir)
}
