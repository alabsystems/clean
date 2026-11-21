// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Exact byte-cohort loading followed by the unchanged full reference replay.
//!
//! This generic transport yields only an unbound reference base. Its caller
//! must authenticate any fixed source/model cohort separately; manifest labels,
//! source hashes and the returned data digest confer no canonical authority.
use crate::recheck_closed::ClosedRecheckOptions;
use crate::{
    load_modules_with_deps_checked, reference_base_closed, CapturedModuleBytes, ImportError,
    ReferenceBase,
};
use clean_kernel::{Environment, Name};
use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

mod custody;
#[cfg(test)]
mod entry_tests;
mod source_context;
pub use source_context::{open_source_context, CheckedSourceContext};

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Parts {
    base: String,
    server: Option<String>,
    private: Option<String>,
    ir: Option<String>,
}
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    schema: String,
    // These fields are transport metadata, never model authority.
    #[serde(rename = "ir_commit")]
    _ir_commit: String,
    lean_version: String,
    #[serde(rename = "lean_githash")]
    _lean_githash: String,
    #[serde(rename = "source_sha256")]
    _source_sha256: BTreeMap<String, String>,
    modules: BTreeMap<String, Parts>,
}
fn hash(data: &[u8]) -> String {
    Sha256::digest(data)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}
fn parts(bytes: CapturedModuleBytes<'_>) -> Parts {
    Parts {
        base: hash(bytes.base),
        server: bytes.server.map(hash),
        private: bytes.private.map(hash),
        ir: bytes.ir.map(hash),
    }
}
fn refusal(name: &Name, why: &str) -> ImportError {
    ImportError::UnsupportedModule {
        module: name.to_string(),
        reason: why.into(),
    }
}

/// Load only the exact manifest population/parts at canonical module paths,
/// then FULL-replay the requested roots using the original closed policy.
/// Callers needing canonical source authority must supply an authenticated,
/// fixed manifest and fixed roots through their own private constructor.
pub fn open_replay(
    directory: &Path,
    manifest: &str,
    schema: &str,
    root_modules: &[&str],
    theorems: &[&str],
) -> Result<(ReferenceBase, String), String> {
    let expected: Manifest = serde_json::from_str(manifest).map_err(|e| e.to_string())?;
    let roots = theorems
        .iter()
        .map(|name| Name::from_string(name))
        .collect::<BTreeSet<_>>();
    if expected.schema != schema
        || expected.lean_version != "4.30.0-rc2"
        || expected.modules.is_empty()
        || root_modules.is_empty()
        || roots.is_empty()
        || roots.len() != theorems.len()
    {
        return Err("invalid compiled frame theorem cohort".into());
    }
    custody::validate_artifact_census(directory, &expected)?;
    let env = load_expected(directory, &expected, root_modules)?;
    let options = ClosedRecheckOptions {
        max_closure: Some(100_000),
        ..ClosedRecheckOptions::default()
    };
    let replay = reference_base_closed(&env, &roots, &options).map_err(|e| e.to_string())?;
    if !replay.entry_refusals.is_empty()
        || !replay.report.passed()
        || !replay.report.extension_bindings_pinned
        || !roots.is_subset(&replay.admitted)
    {
        return Err(format!(
            "frame theorem dependency replay refused: {} {:?}",
            replay.report.verdict_sentence(),
            replay.entry_refusals
        ));
    }
    Ok((replay, hash(manifest.as_bytes())))
}

fn load_expected(
    directory: &Path,
    expected: &Manifest,
    root_modules: &[&str],
) -> Result<Environment, String> {
    let root = directory.canonicalize().map_err(|e| e.to_string())?;
    let mut env = Environment::for_lean_replay();
    let mut seen = BTreeSet::new();
    let mut before = |name: &Name, path: &Path, index: usize| {
        let name_s = name.to_string();
        if index != 0
            || !expected.modules.contains_key(&name_s)
            || name_s
                .split('.')
                .any(|p| p.is_empty() || !p.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_'))
        {
            return Err(refusal(name, "module is outside compiled frame cohort"));
        }
        let exact = root.join(name_s.replace('.', "/") + ".olean");
        if path != exact || path.canonicalize().ok().as_ref() != Some(&exact) {
            return Err(refusal(name, "frame cohort path or symlink differs"));
        }
        Ok(())
    };
    let mut captured = |name: &Name, _path: &Path, bytes: CapturedModuleBytes<'_>| {
        let key = name.to_string();
        let actual = parts(bytes);
        let wanted = expected
            .modules
            .get(&key)
            .ok_or_else(|| refusal(name, "unmanifested module"))?;
        if actual.base != wanted.base
            || actual.server != wanted.server
            || actual.private != wanted.private
            || actual.ir != wanted.ir
            || bytes.ir_signature.is_some()
        {
            return Err(refusal(name, "captured frame module bytes differ"));
        }
        if !seen.insert(key) {
            return Err(refusal(name, "duplicate module capture"));
        }
        Ok(())
    };
    load_modules_with_deps_checked(
        &mut env,
        &root_modules
            .iter()
            .map(|name| (*name).into())
            .collect::<Vec<_>>(),
        std::slice::from_ref(&root),
        &mut before,
        &mut captured,
    )
    .map_err(|e| e.to_string())?;
    if seen != expected.modules.keys().cloned().collect() {
        return Err("compiled frame cohort has missing or extra module rows".into());
    }
    Ok(env)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_or_duplicate_claim_populations_are_refused_before_loading() {
        let manifest = serde_json::json!({
            "schema": "test-cohort",
            "ir_commit": "untrusted-data",
            "lean_version": "4.30.0-rc2",
            "lean_githash": "untrusted-data",
            "source_sha256": {},
            "modules": {"Subject": {"base": "untrusted-data", "server": null,
                "private": null, "ir": null}}
        })
        .to_string();
        for (modules, roots) in [
            (vec![], vec!["Subject.goal"]),
            (vec!["Subject"], vec![]),
            (vec!["Subject"], vec!["Subject.goal", "Subject.goal"]),
        ] {
            let refused = open_replay(
                Path::new("/missing-cohort-data"),
                &manifest,
                "test-cohort",
                &modules,
                &roots,
            )
            .unwrap_err();
            assert_eq!(refused, "invalid compiled frame theorem cohort");
        }
    }
}
