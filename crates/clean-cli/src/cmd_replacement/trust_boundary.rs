// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TrustBoundary TSV audit report and parsing.

use super::*;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct TrustBoundaryAuditReport {
    pub(crate) schema_version: &'static str,
    pub(crate) generated_by: &'static str,
    pub(crate) issue: IssueRef,
    pub(crate) input_files: Vec<String>,
    pub(crate) expected_patterns_path: String,
    pub(crate) total_raw_hits: usize,
    pub(crate) expected_boundary_only_hits: usize,
    pub(crate) unexpected_hits: usize,
    pub(crate) by_crate: BTreeMap<String, usize>,
    pub(crate) groups: Vec<TrustBoundaryGroupedHit>,
    pub(crate) expected_groups: Vec<TrustBoundaryGroupedHit>,
    pub(crate) unexpected_groups: Vec<TrustBoundaryGroupedHit>,
    pub(crate) gate2_effectively_met: bool,
    pub(crate) recommendation: String,
    pub(crate) rerun_commands: Vec<String>,
}

impl TrustBoundaryAuditReport {
    pub(crate) fn from_args(args: &TrustBoundaryAuditArgs) -> Result<Self, ReplacementError> {
        let repo_root = discover_repo_root()?;
        let input_paths = args
            .inputs
            .iter()
            .map(|path| trust_boundary_repo_relative_path(&repo_root, path))
            .collect::<Vec<_>>();
        let expected_path = trust_boundary_repo_relative_path(&repo_root, &args.expected);

        for path in &input_paths {
            require_regular_file("input", path)?;
        }
        require_regular_file("expected", &expected_path)?;

        let mut records = Vec::new();
        for path in &input_paths {
            records.extend(parse_trust_boundary_tsv(path)?);
        }
        let expected_patterns = load_trust_boundary_expected_patterns(&expected_path)?;
        Ok(Self::from_records(
            records,
            &expected_patterns,
            &input_paths,
            &expected_path,
        ))
    }

    pub(crate) fn from_records(
        records: Vec<TrustBoundaryAuditRecord>,
        expected_patterns: &[String],
        input_paths: &[PathBuf],
        expected_path: &Path,
    ) -> Self {
        let groups = group_trust_boundary_records(&records);
        let mut by_crate = BTreeMap::new();
        for group in &groups {
            *by_crate.entry(group.crate_name.clone()).or_insert(0) += group.count;
        }

        let mut expected_groups = Vec::new();
        let mut unexpected_groups = Vec::new();
        for group in &groups {
            if expected_patterns
                .iter()
                .any(|pattern| group.test_name.contains(pattern))
            {
                expected_groups.push(group.clone());
            } else {
                unexpected_groups.push(group.clone());
            }
        }

        let total_raw_hits = groups.iter().map(|group| group.count).sum();
        let expected_boundary_only_hits = expected_groups.iter().map(|group| group.count).sum();
        let unexpected_hits = unexpected_groups.iter().map(|group| group.count).sum();
        let gate2_effectively_met = unexpected_hits == 0;
        let recommendation = if total_raw_hits == 0 {
            "No trust-boundary hits detected. Gate 2 criterion 5 is effectively met.".to_owned()
        } else if gate2_effectively_met {
            format!(
                "All {total_raw_hits} hits are from expected boundary-only tests. Gate 2 criterion 5 is effectively met."
            )
        } else {
            format!("{unexpected_hits} unexpected hit(s) found. Gate 2 criterion 5 is NOT yet met.")
        };

        Self {
            schema_version: TRUST_BOUNDARY_AUDIT_SCHEMA_VERSION,
            generated_by: "clean replacement trust-boundary-audit",
            issue: IssueRef::new(2875, "Gate 2 TrustBoundary audit"),
            input_files: input_paths
                .iter()
                .map(|path| path.to_string_lossy().into_owned())
                .collect(),
            expected_patterns_path: expected_path.to_string_lossy().into_owned(),
            total_raw_hits,
            expected_boundary_only_hits,
            unexpected_hits,
            by_crate,
            groups,
            expected_groups,
            unexpected_groups,
            gate2_effectively_met,
            recommendation,
            rerun_commands: trust_boundary_rerun_commands(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TrustBoundaryAuditRecord {
    pub(crate) lane: String,
    pub(crate) crate_name: String,
    pub(crate) test_name: String,
    pub(crate) tactic: String,
    pub(crate) proof_kind: String,
    pub(crate) subsystem: String,
    pub(crate) description: String,
    pub(crate) step_index: String,
    pub(crate) arithmetic_boundary_steps: usize,
    pub(crate) local_gap_steps: usize,
    pub(crate) trust_subterm_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct TrustBoundaryGroupedHit {
    pub(crate) crate_name: String,
    pub(crate) test_name: String,
    pub(crate) lane: String,
    pub(crate) tactic: String,
    pub(crate) proof_kind: String,
    pub(crate) subsystem: String,
    pub(crate) count: usize,
    pub(crate) total_arith: usize,
    pub(crate) total_local_gap: usize,
    pub(crate) total_trust: usize,
}

pub(crate) fn discover_repo_root() -> Result<PathBuf, ReplacementError> {
    let mut dir = std::env::current_dir()?;
    loop {
        if dir.join("Cargo.toml").is_file() && dir.join("crates/clean-cli").is_dir() {
            return Ok(dir);
        }
        if !dir.pop() {
            return std::env::current_dir().map_err(Into::into);
        }
    }
}

pub(crate) fn trust_boundary_repo_relative_path(repo_root: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        repo_root.join(path)
    }
}

pub(crate) fn require_regular_file(label: &str, path: &Path) -> Result<(), ReplacementError> {
    if !path.exists() {
        return Err(ReplacementError::TrustBoundaryAuditInput {
            message: format!("{label} path does not exist: {}", path.display()),
        });
    }
    if !path.is_file() {
        return Err(ReplacementError::TrustBoundaryAuditInput {
            message: format!("{label} path is not a file: {}", path.display()),
        });
    }
    Ok(())
}

pub(crate) fn parse_trust_boundary_tsv(
    path: &Path,
) -> Result<Vec<TrustBoundaryAuditRecord>, ReplacementError> {
    let text = fs::read_to_string(path).map_err(|source| ReplacementError::ReadArtifact {
        path: "trust-boundary audit input",
        source,
    })?;
    let mut records = Vec::new();
    for (line_index, line) in text.lines().enumerate() {
        if line.is_empty() {
            continue;
        }
        let cols = line.split('\t').collect::<Vec<_>>();
        if cols.len() != 11 {
            return Err(ReplacementError::TrustBoundaryAuditInput {
                message: format!(
                    "{}:{}: expected 11 tab-separated columns, got {}",
                    path.display(),
                    line_index + 1,
                    cols.len()
                ),
            });
        }
        records.push(TrustBoundaryAuditRecord {
            lane: cols[0].to_owned(),
            crate_name: cols[1].to_owned(),
            test_name: cols[2].to_owned(),
            tactic: cols[3].to_owned(),
            proof_kind: cols[4].to_owned(),
            subsystem: cols[5].to_owned(),
            description: cols[6].to_owned(),
            step_index: cols[7].to_owned(),
            arithmetic_boundary_steps: parse_trust_boundary_count(path, line_index, cols[8])?,
            local_gap_steps: parse_trust_boundary_count(path, line_index, cols[9])?,
            trust_subterm_count: parse_trust_boundary_count(path, line_index, cols[10])?,
        });
    }
    Ok(records)
}

pub(crate) fn parse_trust_boundary_count(
    path: &Path,
    line_index: usize,
    value: &str,
) -> Result<usize, ReplacementError> {
    value
        .parse()
        .map_err(|_| ReplacementError::TrustBoundaryAuditInput {
            message: format!(
                "{}:{}: columns 9-11 must be non-negative integers",
                path.display(),
                line_index + 1
            ),
        })
}

pub(crate) fn load_trust_boundary_expected_patterns(
    path: &Path,
) -> Result<Vec<String>, ReplacementError> {
    let text = fs::read_to_string(path).map_err(|source| ReplacementError::ReadArtifact {
        path: TRUST_BOUNDARY_EXPECTED_TESTS_PATH,
        source,
    })?;
    Ok(text
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(ToOwned::to_owned)
        .collect())
}

pub(crate) fn group_trust_boundary_records(
    records: &[TrustBoundaryAuditRecord],
) -> Vec<TrustBoundaryGroupedHit> {
    let mut groups = BTreeMap::new();
    for record in records {
        let key = (
            record.crate_name.clone(),
            record.test_name.clone(),
            record.lane.clone(),
            record.tactic.clone(),
            record.proof_kind.clone(),
            record.subsystem.clone(),
        );
        let group = groups
            .entry(key)
            .or_insert_with(|| TrustBoundaryGroupedHit {
                crate_name: record.crate_name.clone(),
                test_name: record.test_name.clone(),
                lane: record.lane.clone(),
                tactic: record.tactic.clone(),
                proof_kind: record.proof_kind.clone(),
                subsystem: record.subsystem.clone(),
                count: 0,
                total_arith: 0,
                total_local_gap: 0,
                total_trust: 0,
            });
        group.count += 1;
        group.total_arith += record.arithmetic_boundary_steps;
        group.total_local_gap += record.local_gap_steps;
        group.total_trust += record.trust_subterm_count;
    }
    groups.into_values().collect()
}

pub(crate) fn trust_boundary_rerun_commands() -> Vec<String> {
    vec![
        "CLEAN_TRUST_BOUNDARY_AUDIT_PATH=/tmp/clean-2875-auto.tsv cargo test --locked --message-format=short -j 1 -p clean-auto --lib".to_owned(),
        "CLEAN_TRUST_BOUNDARY_AUDIT_PATH=/tmp/clean-2875-elab.tsv cargo test --locked --message-format=short -j 1 -p clean-elab --lib --features ay-smt".to_owned(),
        format!(
            "clean replacement trust-boundary-audit --input /tmp/clean-2875-auto.tsv --input /tmp/clean-2875-elab.tsv --expected {TRUST_BOUNDARY_EXPECTED_TESTS_PATH} --output reports/research/issue-2875-trustboundary-audit-current.md"
        ),
    ]
}
