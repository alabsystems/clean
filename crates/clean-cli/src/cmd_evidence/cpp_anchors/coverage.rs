// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Coverage checked against the measured C++ inventory.

use std::collections::{BTreeMap, BTreeSet};

use super::{FunctionMeasured, Inventory, Report, Row};

type FunctionKey<'a> = (&'a str, &'a str);
type Claim<'a> = ([usize; 2], &'a Row);

/// Anchors whose declared ranges are contained in a measured function.
pub(super) type Claims<'a> = BTreeMap<(&'a str, &'a str), Vec<([usize; 2], &'a Row)>>;

pub(super) fn verify<'a>(
    inventory: &'a Inventory,
    claims: &Claims<'a>,
    complete: bool,
    report: &mut Report<'_>,
) {
    let functions: BTreeMap<_, _> = report
        .functions
        .iter()
        .flat_map(|(&file, functions)| {
            functions
                .iter()
                .map(move |function| ((file, function.name.as_str()), function))
        })
        .collect();
    for (&(file, name), &function) in &functions {
        let spans = claims.get(&(file, name)).map_or(&[][..], Vec::as_slice);
        verify_function(file, function, spans, complete, &mut report.findings);
    }

    // Constants may resolve through any pinned source file. Missing input
    // prevents conclusions in either direction about their resolved names.
    if complete {
        verify_declared_constants(inventory, &functions, &mut report.findings);
    }
}

fn verify_function(
    file: &str,
    function: &FunctionMeasured,
    spans: &[Claim<'_>],
    complete: bool,
    findings: &mut Vec<String>,
) {
    let location = format!("{file}:{}", function.name);
    let [start, end] = function.lines;
    if spans.is_empty() {
        findings.push(format!(
            "(a) UNMAPPED: function {location} (lines {start}-{end}) is claimed by no row"
        ));
        return;
    }
    if !spans.iter().any(|(lines, _)| *lines == function.lines) {
        verify_split_lines(&location, function, spans, findings);
    }
    if complete {
        for occurrence in &function.hardcoded_constants {
            if !spans.iter().any(|(lines, row)| {
                contains(*lines, occurrence.line)
                    && row
                        .constants
                        .as_ref()
                        .is_some_and(|names| names.contains(&occurrence.constant))
            }) {
                findings.push(format!(
                    "(a) UNMAPPED: hardcoded constant {} at {location} line {} is named by no row anchored there",
                    occurrence.constant, occurrence.line
                ));
            }
        }
    }
}

fn verify_split_lines(
    location: &str,
    function: &FunctionMeasured,
    spans: &[Claim<'_>],
    findings: &mut Vec<String>,
) {
    let claimed = |line| spans.iter().any(|(lines, _)| contains(*lines, line));
    for arm in &function.case_arms {
        if !claimed(arm.line) {
            findings.push(format!(
                "(a) UNMAPPED: case arm {location}/{} (line {}) is claimed by no row",
                arm.name, arm.line
            ));
        }
    }
    let arm_lines: BTreeSet<_> = function.case_arms.iter().map(|arm| arm.line).collect();
    let loose = function
        .code_lines
        .iter()
        .copied()
        .filter(|line| !claimed(*line) && !arm_lines.contains(line));
    let ranges = ranges(loose);
    if !ranges.is_empty() {
        findings.push(format!(
            "(a) UNMAPPED: {location} is split by line range and lines {ranges} are claimed by no row"
        ));
    }
}

fn verify_declared_constants(
    inventory: &Inventory,
    functions: &BTreeMap<FunctionKey<'_>, &FunctionMeasured>,
    findings: &mut Vec<String>,
) {
    for row in &inventory.rows {
        let Some(constants) = row.constants.as_deref().filter(|names| !names.is_empty()) else {
            continue;
        };
        // The incumbent uses the declared bounds for this reverse check,
        // including known-function anchors whose containment check failed.
        let used: BTreeSet<&str> = row
            .anchors
            .iter()
            .filter_map(|anchor| {
                let key = (anchor.file.as_str(), anchor.function.as_str());
                functions
                    .get(&key)
                    .map(|function| (anchor.lines, *function))
            })
            .flat_map(|(lines, function)| {
                function
                    .hardcoded_constants
                    .iter()
                    .filter(move |occurrence| contains(lines, occurrence.line))
                    .map(|occurrence| occurrence.constant.as_str())
            })
            .collect();
        for constant in constants {
            if !used.contains(constant.as_str()) {
                findings.push(format!(
                    "(b) ANCHOR: {} names hardcoded constant {constant}, which its anchors do not use",
                    row.id
                ));
            }
        }
    }
}

fn contains([lo, hi]: [usize; 2], line: usize) -> bool {
    (lo..=hi).contains(&line)
}

fn ranges(mut lines: impl Iterator<Item = usize>) -> String {
    let Some(mut start) = lines.next() else {
        return String::new();
    };
    let mut end = start;
    let mut runs = Vec::new();
    for line in lines {
        if end.checked_add(1) != Some(line) {
            runs.push([start, end]);
            start = line;
        }
        end = line;
    }
    runs.push([start, end]);
    runs.into_iter()
        .map(|[start, end]| {
            if start == end {
                start.to_string()
            } else {
                format!("{start}-{end}")
            }
        })
        .collect::<Vec<_>>()
        .join(", ")
}

#[cfg(test)]
mod tests {
    use clean_evidence::source_scan::cpp::{CppCaseArm, CppConstantUse};
    use serde_json::json;

    use super::super::decode_inventory;
    use super::{verify, BTreeMap, Claims, FunctionMeasured, Report};

    fn function(
        name: &str,
        [start, end]: [usize; 2],
        arms: &[(&str, usize)],
        constants: &[(usize, &str)],
    ) -> FunctionMeasured {
        FunctionMeasured {
            name: name.to_owned(),
            lines: [start, end],
            raw_sha256: String::new(),
            case_arms: arms
                .iter()
                .map(|&(name, line)| CppCaseArm {
                    name: name.to_owned(),
                    line,
                })
                .collect(),
            code_lines: (start..=end).collect(),
            hardcoded_constants: constants
                .iter()
                .map(|&(line, constant)| CppConstantUse {
                    line,
                    constant: constant.to_owned(),
                })
                .collect(),
        }
    }

    const FILE: &str = "k/checker.cpp";
    const UNCOVERED_ARMS: [&str; 2] = [
        "(a) UNMAPPED: case arm k/checker.cpp:alpha/switch1/B (line 5) is claimed by no row",
        "(a) UNMAPPED: case arm k/checker.cpp:alpha/switch2/A (line 2) is claimed by no row",
    ];
    const LOOSE_LINES: &str =
        "(a) UNMAPPED: k/checker.cpp:alpha is split by line range and lines 1, 4, 6-7 are claimed by no row";
    const UNCLAIMED: &str =
        "(a) UNMAPPED: function k/checker.cpp:zeta (lines 20-22) is claimed by no row";

    fn fixture_findings(complete: bool) -> Vec<String> {
        let inventory = json!({
            "upstream": {
                "repository": "", "tag": "", "commit": "",
                "root": "k", "toolchain_file": "lean-toolchain", "files": {}
            },
            "rows": [
                {
                    "id": "partial", "kind": "rule", "anchors": [
                        {"file": FILE, "function": "alpha", "lines": [3, 3], "sha256": ""},
                        {"file": FILE, "function": "alpha", "lines": [0, 6], "sha256": ""}
                    ], "constants": ["Visible", "Ghost"]
                },
                {
                    "id": "whole", "kind": "strategy", "anchors": [
                        {"file": FILE, "function": "beta", "lines": [10, 12], "sha256": ""}
                    ]
                }
            ]
        })
        .to_string();
        let inventory =
            decode_inventory(inventory.as_bytes(), true).expect("coverage fixture inventory");
        let claims = Claims::from([
            ((FILE, "alpha"), vec![([3, 3], &inventory.rows[0])]),
            ((FILE, "beta"), vec![([10, 12], &inventory.rows[1])]),
        ]);
        let mut report = Report {
            upstream: &inventory.upstream.identity,
            files: BTreeMap::new(),
            functions: BTreeMap::from([(
                FILE,
                vec![
                    function(
                        "beta",
                        [10, 12],
                        &[("switch1/Outer", 13)],
                        &[(11, "Required")],
                    ),
                    function(
                        "alpha",
                        [1, 7],
                        &[("switch1/B", 5), ("switch2/A", 2)],
                        &[(5, "Visible"), (5, "Visible")],
                    ),
                    function("zeta", [20, 22], &[], &[(21, "Unused")]),
                ],
            )]),
            anchors: Vec::new(),
            unreadable: BTreeMap::new(),
            findings: Vec::new(),
        };
        verify(&inventory, &claims, complete, &mut report);
        report.findings
    }

    #[test]
    fn reports_split_lines_and_constants_at_their_occurrences() {
        let repeated =
            "(a) UNMAPPED: hardcoded constant Visible at k/checker.cpp:alpha line 5 is named by no row anchored there";
        assert_eq!(
            fixture_findings(true),
            [
                UNCOVERED_ARMS[0],
                UNCOVERED_ARMS[1],
                LOOSE_LINES,
                repeated,
                repeated,
                "(a) UNMAPPED: hardcoded constant Required at k/checker.cpp:beta line 11 is named by no row anchored there",
                UNCLAIMED,
                "(b) ANCHOR: partial names hardcoded constant Ghost, which its anchors do not use",
            ]
        );
    }

    #[test]
    fn reports_known_structure_while_constant_resolution_is_incomplete() {
        assert_eq!(
            fixture_findings(false),
            [UNCOVERED_ARMS[0], UNCOVERED_ARMS[1], LOOSE_LINES, UNCLAIMED]
        );
    }
}
