// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated-count manifest parsing and corpus discovery helpers.

use super::*;

pub(crate) fn parse_tactic_generated_count_manifests(
    registry: &str,
) -> Result<Vec<TacticParityGeneratedCountManifest>, Vec<String>> {
    let mut in_block = false;
    let mut current: BTreeMap<String, String> = BTreeMap::new();
    let mut raw_entries = Vec::new();

    for line in registry.lines() {
        if !in_block {
            if line.trim() == "generated_count_manifests:" {
                in_block = true;
            }
            continue;
        }
        if line.starts_with("  ") && !line.starts_with("    ") {
            break;
        }
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        if let Some(rest) = trimmed.strip_prefix("- ") {
            if !current.is_empty() {
                raw_entries.push(std::mem::take(&mut current));
            }
            if let Some((key, value)) = split_simple_yaml_field(rest) {
                current.insert(key.to_owned(), value.to_owned());
            }
            continue;
        }
        if let Some((key, value)) = split_simple_yaml_field(trimmed) {
            current.insert(key.to_owned(), value.to_owned());
        }
    }
    if !current.is_empty() {
        raw_entries.push(current);
    }

    let mut errors = Vec::new();
    let mut manifests = Vec::new();
    for (index, entry) in raw_entries.iter().enumerate() {
        let context = format!("generated_count_manifests[{index}]");
        let manifest = (|| -> Result<TacticParityGeneratedCountManifest, String> {
            Ok(TacticParityGeneratedCountManifest {
                tactic_lane: required_yaml_string(entry, "tactic_lane", &context)?,
                bucket: required_yaml_string(entry, "bucket", &context)?,
                generated: required_yaml_bool(entry, "generated", &context)?,
                source_corpus_path: required_yaml_string(entry, "source_corpus_path", &context)?,
                runner_path: required_yaml_string(entry, "runner_path", &context)?,
                runner_command: required_yaml_string(entry, "runner_command", &context)?,
                runner_artifact_contract: required_yaml_string(
                    entry,
                    "runner_artifact_contract",
                    &context,
                )?,
                expected_lean4_runner_artifact_path: required_yaml_string(
                    entry,
                    "expected_lean4_runner_artifact_path",
                    &context,
                )?,
                missing_runner_status: required_yaml_string(
                    entry,
                    "missing_runner_status",
                    &context,
                )?,
                parity_status: required_yaml_string(entry, "parity_status", &context)?,
                readiness_effect: required_yaml_string(entry, "readiness_effect", &context)?,
            })
        })();
        match manifest {
            Ok(manifest) => manifests.push(manifest),
            Err(error) => errors.push(error),
        }
    }

    if raw_entries.is_empty() {
        errors.push("registry generated_count_manifests block is empty".to_owned());
    }
    if errors.is_empty() {
        Ok(manifests)
    } else {
        Err(errors)
    }
}

pub(crate) fn discover_tactic_source_corpus(
    manifest: &TacticParityGeneratedCountManifest,
) -> TacticParitySourceCorpusDiscovery {
    let path = repo_artifact_path_dynamic(&manifest.source_corpus_path);
    let raw = fs::read_to_string(path);
    let present = raw.is_ok();
    let mut blockers = Vec::new();
    let mut case_ids = Vec::new();
    let mut valid = false;
    let mut sha256 = None;

    match raw {
        Ok(raw) => {
            sha256 = Some(sha256_hex(raw.as_bytes()));
            let fields = parse_top_level_yaml_fields(&raw);
            if fields.get("schema_version").map(String::as_str)
                != Some(TACTIC_GENERATED_COUNT_SOURCE_CORPUS_SCHEMA_VERSION)
            {
                blockers.push(format!(
                    "{} schema_version must be {}",
                    manifest.source_corpus_path,
                    TACTIC_GENERATED_COUNT_SOURCE_CORPUS_SCHEMA_VERSION
                ));
            }
            if fields.get("tactic_lane") != Some(&manifest.tactic_lane) {
                blockers.push(format!(
                    "{} tactic_lane must match {}",
                    manifest.source_corpus_path, manifest.tactic_lane
                ));
            }
            if fields.get("generated").map(String::as_str) != Some("false") {
                blockers.push(format!(
                    "{} must keep generated: false until real Lean4-vs-clean counts exist",
                    manifest.source_corpus_path
                ));
            }

            let mut seen = BTreeSet::new();
            for line in raw.lines() {
                let trimmed = line.trim();
                if let Some(rest) = trimmed.strip_prefix("- id:") {
                    let id = trim_yaml_scalar(rest);
                    if id.is_empty() {
                        blockers.push(format!(
                            "{} contains an empty case id",
                            manifest.source_corpus_path
                        ));
                    } else if !seen.insert(id.to_owned()) {
                        blockers.push(format!(
                            "{} contains duplicate case id {id}",
                            manifest.source_corpus_path
                        ));
                    } else {
                        case_ids.push(id.to_owned());
                    }
                }
            }
            if case_ids.is_empty() {
                blockers.push(format!(
                    "{} must contain at least one generated-count case",
                    manifest.source_corpus_path
                ));
            }
            valid = blockers.is_empty();
        }
        Err(error) => blockers.push(format!(
            "failed to read {}: {}",
            manifest.source_corpus_path, error
        )),
    }

    TacticParitySourceCorpusDiscovery {
        present,
        valid,
        sha256,
        case_ids,
        blockers,
    }
}

pub(crate) fn discover_tactic_generated_count_artifacts(template: &str) -> Vec<String> {
    let Some((prefix, suffix)) = template.split_once("{run_id}") else {
        let path = repo_artifact_path_dynamic(template);
        return if path.is_file() {
            vec![template.to_owned()]
        } else {
            Vec::new()
        };
    };
    let root = repo_artifact_path_dynamic(prefix.trim_end_matches('/'));
    if !root.is_dir() {
        return Vec::new();
    }

    let mut matches: Vec<String> = WalkDir::new(root)
        .into_iter()
        .filter_map(Result::ok)
        .filter(|entry| entry.file_type().is_file())
        .filter_map(|entry| {
            let path = entry.path();
            let repo_path = path
                .strip_prefix(repo_root_path())
                .unwrap_or(path)
                .to_string_lossy()
                .replace('\\', "/");
            if repo_path.starts_with(prefix) && repo_path.ends_with(suffix) {
                Some(repo_path)
            } else {
                None
            }
        })
        .collect();
    matches.sort();
    matches
}

pub(crate) fn parse_top_level_yaml_fields(raw: &str) -> BTreeMap<String, String> {
    raw.lines()
        .filter(|line| !line.starts_with(' ') && !line.starts_with('-'))
        .filter_map(|line| split_simple_yaml_field(line.trim()))
        .map(|(key, value)| (key.to_owned(), value.to_owned()))
        .collect()
}

pub(crate) fn split_simple_yaml_field(line: &str) -> Option<(&str, &str)> {
    let (key, value) = line.split_once(':')?;
    Some((key.trim(), trim_yaml_scalar(value)))
}

pub(crate) fn trim_yaml_scalar(value: &str) -> &str {
    value.trim().trim_matches('"').trim_matches('\'').trim()
}

pub(crate) fn required_yaml_string(
    entry: &BTreeMap<String, String>,
    field: &str,
    context: &str,
) -> Result<String, String> {
    entry
        .get(field)
        .filter(|value| !value.is_empty())
        .cloned()
        .ok_or_else(|| format!("{context} must define non-empty string field {field}"))
}

pub(crate) fn required_yaml_bool(
    entry: &BTreeMap<String, String>,
    field: &str,
    context: &str,
) -> Result<bool, String> {
    match entry.get(field).map(String::as_str) {
        Some("true") => Ok(true),
        Some("false") => Ok(false),
        _ => Err(format!("{context} must define boolean field {field}")),
    }
}

pub(crate) fn sha256_hex(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hasher
        .finalize()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>()
}

pub(crate) fn repo_root_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

pub(crate) fn repo_artifact_path_dynamic(path: &str) -> PathBuf {
    let cwd_path = Path::new(path);
    if cwd_path.exists() {
        return cwd_path.to_path_buf();
    }
    repo_root_path().join(path)
}
