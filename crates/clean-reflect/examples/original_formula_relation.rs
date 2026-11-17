// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![deny(
    clippy::wildcard_enum_match_arm,
    clippy::match_wildcard_for_single_variants,
    clippy::wildcard_in_or_patterns
)]

//! Actual FMREL import/replay diagnostic; never an object or function grade.
//!
//! original_formula_relation <exact-cohort-dir> <cohort-manifest.json> <subject.json>...
//! Subjects must be the exact compact serde bytes consumed by TrustIR's parser.
//! No Rust Formula schema, interpretation or normalization is used here.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use clean_kernel::{BigNat, Declaration, Environment, Expr, Level, Name, TypeChecker};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::{
    load_modules_with_deps_checked, reference_base_closed, CapturedModuleBytes, ImportError,
};
use clean_reflect::source_equation::check_source_goal_relation_with_proof;
use serde::Deserialize;
use sha2::{Digest, Sha256};

const SOURCE: &str = "TrustIr.Formula.V2.ConjHoldsB";
const GOAL: &str = "TrustIr.Formula.V2.GoalB";
const RELATION: &str = "TrustIr.Formula.V2.original_bytes_iff_goal";

#[derive(Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Parts {
    base: String,
    server: Option<String>,
    private: Option<String>,
    ir: Option<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    schema: String,
    ir_commit: String,
    lean_version: String,
    lean_githash: String,
    source_sha256: BTreeMap<String, String>,
    modules: BTreeMap<String, Parts>,
}

fn hash(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn refused(name: &Name, reason: &str) -> ImportError {
    ImportError::UnsupportedModule {
        module: name.to_string(),
        reason: reason.into(),
    }
}

fn original_bytes(bytes: &[u8]) -> [Expr; 2] {
    let limbs = bytes
        .chunks(8)
        .map(|chunk| {
            let mut word = [0; 8];
            word[..chunk.len()].copy_from_slice(chunk);
            u64::from_le_bytes(word)
        })
        .collect();
    [
        Expr::nat_lit(bytes.len() as u64),
        Expr::bignat_lit(BigNat::from_limbs(limbs)),
    ]
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args_os().skip(1);
    let directory = PathBuf::from(args.next().ok_or("missing exact-cohort-dir")?).canonicalize()?;
    let manifest_bytes = std::fs::read(args.next().ok_or("missing cohort-manifest.json")?)?;
    let manifest: Manifest = serde_json::from_slice(&manifest_bytes)?;
    if manifest.schema != "trust.formula-relation-cohort.v2"
        || manifest.lean_version != "4.30.0-rc2"
        || manifest.ir_commit.len() != 40
        || manifest.lean_githash.len() != 40
        || manifest.modules.is_empty()
        || manifest.source_sha256.is_empty()
    {
        return Err("invalid Formula relation cohort metadata".into());
    }
    let subjects: Vec<_> = args.map(PathBuf::from).collect();
    if subjects.is_empty() {
        return Err("missing original subject bytes".into());
    }
    let mut imported = Environment::for_lean_replay();
    let mut seen = BTreeSet::new();
    let mut before = |name: &Name, path: &Path, index: usize| {
        let text = name.to_string();
        if index != 0
            || !manifest.modules.contains_key(&text)
            || text.split('.').any(|part| {
                part.is_empty() || !part.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
            })
        {
            return Err(refused(name, "module outside exact Formula cohort"));
        }
        let expected = directory.join(text.replace('.', "/") + ".olean");
        if path != expected || path.canonicalize().ok().as_ref() != Some(&expected) {
            return Err(refused(name, "Formula cohort path or symlink differs"));
        }
        Ok(())
    };
    let mut captured = |name: &Name, _: &Path, bytes: CapturedModuleBytes<'_>| {
        let text = name.to_string();
        let actual = Parts {
            base: hash(bytes.base),
            server: bytes.server.map(hash),
            private: bytes.private.map(hash),
            ir: bytes.ir.map(hash),
        };
        if manifest.modules.get(&text) != Some(&actual) || !seen.insert(text) {
            return Err(refused(
                name,
                "captured Formula module bytes differ or repeat",
            ));
        }
        Ok(())
    };
    let modules = load_modules_with_deps_checked(
        &mut imported,
        &[
            "TrustIr.Formula.V2.ReflectSound".into(),
            "TrustIr.Formula.V1.CleanCompat".into(),
        ],
        std::slice::from_ref(&directory),
        &mut before,
        &mut captured,
    )?;
    if seen != manifest.modules.keys().cloned().collect() {
        return Err("missing or extra Formula cohort modules".into());
    }
    println!(
        "imported {} exact modules in {} artifact parts, cohort={}",
        seen.len(),
        modules.len(),
        hash(&manifest_bytes)
    );
    let targets = [
        SOURCE,
        GOAL,
        RELATION,
        "TrustIr.Formula.V1.Compat.Nat.div_add_mod",
        "TrustIr.Formula.V1.Compat.Nat.mul_succ",
        "TrustIr.Formula.V1.Compat.Nat.succ_mul",
    ]
    .into_iter()
    .map(Name::from_string)
    .collect::<BTreeSet<_>>();
    let run = reference_base_closed(&imported, &targets, &ClosedRecheckOptions::default())?;
    println!(
        "{}; cone={} elapsed_ms={} axioms={:?}",
        run.report.verdict_sentence(),
        run.report.cone_constants,
        run.report.elapsed_ms,
        run.report.axioms_admitted
    );
    if !run.report.passed()
        || !run.report.extension_bindings_pinned
        || !run.entry_refusals.is_empty()
        || !targets.is_subset(&run.admitted)
    {
        for refusal in &run.report.refusals {
            eprintln!("{refusal:?}");
        }
        for refusal in &run.entry_refusals {
            eprintln!("{refusal:?}");
        }
        return Err("original Formula source/relation dependency replay refused".into());
    }
    let kernel = run
        .into_kernel()
        .map_err(|report| std::io::Error::other(report.verdict_sentence()))?;
    let environment = kernel.environment();
    if let Some(path) = std::env::var_os("CLEAN_FORMULA_DIAGNOSTIC_ENV_OUT") {
        // Data only: deserializing this snapshot confers no origin, checked
        // token, source admission or proof authority. It is for profiling.
        let bytes = environment.to_dag_bincode()?;
        std::fs::write(path, &bytes)?;
        println!("diagnostic environment DATA only, sha256={}", hash(&bytes));
    }
    for (index, subject) in subjects.into_iter().enumerate() {
        let bytes = std::fs::read(&subject)?;
        if bytes.is_empty() || bytes.len() > 1024 * 1024 {
            return Err("original subject byte budget".into());
        }
        let arguments = original_bytes(&bytes);
        let goal = Expr::apps(Expr::const_str(GOAL), arguments.clone());
        let ready = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [Expr::const_str("Bool"), Expr::const_str("Bool.true")],
        );
        let proof = Expr::apps(
            Expr::const_str(RELATION),
            [arguments[0].clone(), arguments[1].clone(), ready],
        );
        if std::env::var_os("CLEAN_FORMULA_PROFILE_ROOT").is_some() {
            // Match the certification root's strict checker and its unchanged
            // default budget over the SAME full original statement and proof.
            let statement = Expr::apps(
                Expr::const_str("Iff"),
                [
                    Expr::apps(Expr::const_str(SOURCE), arguments.clone()),
                    goal.clone(),
                ],
            );
            let mut checker = TypeChecker::new(environment);
            checker.set_allow_unsafe(false);
            checker.set_allow_partial(false);
            checker.enable_heartbeat_profiler();
            let sort = checker.infer_sort(&statement)?;
            if !sort.is_zero() {
                return Err("original relation is not a proposition".into());
            }
            let result = checker.check_type(&proof, &statement);
            eprintln!(
                "SAME WHOLE ORIGINAL ROOT: {:?}",
                checker.heartbeat_profile()
            );
            result?;
        }
        let checked = check_source_goal_relation_with_proof(
            environment,
            &Name::from_string(SOURCE),
            &[],
            &arguments,
            &goal,
            Name::from_string(&format!("OriginalFormulaRelation{index}")),
            proof,
        )?;
        let Declaration::Theorem { value, .. } = checked.declaration() else {
            return Err("relation did not retain its fully checked theorem".into());
        };
        check_source_goal_relation_with_proof(
            environment,
            &Name::from_string(SOURCE),
            &[],
            &arguments,
            &goal,
            Name::from_string(&format!("ReplayedOriginalFormulaRelation{index}")),
            value.clone(),
        )?;
        // A relation certificate must not be silently rebound to different
        // original bytes, even when a replacement subject is also well formed.
        let mut changed = bytes.clone();
        if let Some(position) = bytes.windows(b"BvSDiv".len()).position(|w| w == b"BvSDiv") {
            changed[position + 2] = b'U';
        } else {
            changed[0] ^= 1;
        }
        if check_source_goal_relation_with_proof(
            environment,
            &Name::from_string(SOURCE),
            &[],
            &original_bytes(&changed),
            &goal,
            Name::from_string(&format!("ChangedOriginalFormulaRelation{index}")),
            value.clone(),
        )
        .is_ok()
        {
            return Err("retained relation replay accepted different original bytes".into());
        }
        println!(
            "checked+replayed original relation: {} bytes={}",
            subject.display(),
            bytes.len()
        );
    }
    Ok(())
}
