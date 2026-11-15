// Copyright 2026 Andrew Yates. Apache-2.0.
//! F4: whole pinned Init coverage/cost through the production fenced entry.
//! Exit zero means complete accounting, including refusals; never full acceptance.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::time::Instant;

use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::{load_module_with_deps, reference_base_closed};
use serde_json::json;

// LoadSummary labels companion parts as M._server and M._private. They
// belong to artifact M; they are not modules at M/_server.olean.
fn artifact_module<'a>(lib: &Path, label: &'a str) -> &'a str {
    if lib
        .join(label.replace('.', "/"))
        .with_extension("olean")
        .is_file()
    {
        label
    } else {
        label
            .strip_suffix("._server")
            .or_else(|| label.strip_suffix("._private"))
            .unwrap_or(label)
    }
}

fn unit(env: &Environment, name: &Name) -> String {
    let ind = env.get_inductive(name).or_else(|| {
        env.get_constructor(name)
            .and_then(|c| env.get_inductive(&c.inductive_name))
            .or_else(|| {
                env.get_recursor(name)
                    .and_then(|r| env.get_inductive(&r.inductive_name))
            })
    });
    ind.map_or_else(
        || name.to_string(),
        |i| {
            let head = i
                .all_names
                .iter()
                .filter(|n| env.get_inductive(n).is_some())
                .min()
                .unwrap_or(&i.name);
            format!("inductive {head}")
        },
    )
}

fn main() -> Result<(), Box<dyn Error>> {
    let out = PathBuf::from(std::env::args().nth(1).ok_or("output directory required")?);
    std::fs::create_dir_all(&out)?;
    let lib = clean_olean::require_pinned_lean_lib_path()?;
    let pin = include_str!("../../../lean-toolchain").trim();
    let started = Instant::now();
    let mut env = Environment::for_lean_replay();
    let summaries = load_module_with_deps(&mut env, "Init", std::slice::from_ref(&lib))?;
    let mut loader_refusals: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for summary in &summaries {
        for skipped in &summary.skipped_constants {
            loader_refusals
                .entry(skipped.name.clone())
                .or_default()
                .push(skipped.reason.clone());
        }
        for (name, reason) in summary
            .refused_completions
            .iter()
            .chain(&summary.shadowed_declarations)
        {
            loader_refusals
                .entry(name.to_string())
                .or_default()
                .push(reason.clone());
        }
    }
    let load_ms = started.elapsed().as_millis();
    let mut targets: BTreeSet<Name> = env
        .constants()
        .map(|c| c.name.clone())
        .chain(env.inductives().map(|i| i.name.clone()))
        .chain(env.constructors().map(|c| c.name.clone()))
        .chain(env.recursors().map(|r| r.name.clone()))
        .collect();
    let resident_names = targets.len();
    let inventory_started = Instant::now();
    let mut declared_names = BTreeSet::new();
    let mut module_inventory = BTreeMap::new();
    for summary in &summaries {
        let label = summary.module_name.as_deref().ok_or("unnamed import")?;
        let module = artifact_module(&lib, label);
        if module_inventory.contains_key(module) {
            continue;
        }
        let path = lib.join(module.replace('.', "/")).with_extension("olean");
        clean_olean::toolchain_identity::pinned_toolchain_module(module, &path)?;
        let artifact =
            clean_olean::read_artifact(module, &path, clean_olean::ArtifactDepth::Names)?;
        module_inventory.insert(module.to_owned(), artifact.names.len());
        declared_names.extend(artifact.names);
    }
    // Raw authoritative names prevent conversion losses from shrinking the
    // denominator. Missing residents reach the replay as named refusals.
    targets.extend(declared_names.iter().cloned());
    let inventory_ms = inventory_started.elapsed().as_millis();
    eprintln!(
        "Init loaded: {} resident names, {} summaries, {load_ms} ms; {} targets after raw inventory",
        resident_names,
        summaries.len(),
        targets.len(),
    );
    let options = ClosedRecheckOptions::default();
    let built = reference_base_closed(&env, &targets, &options)?;
    let name_units: BTreeMap<String, String> = targets
        .iter()
        .map(|name| (name.to_string(), unit(&env, name)))
        .collect();
    let mut refusals_by_subject: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for (index, refusal) in built.report.refusals.iter().enumerate() {
        let subject = refusal.subject();
        let label = name_units.get(subject).map_or(subject, String::as_str);
        refusals_by_subject
            .entry(label.to_owned())
            .or_default()
            .push(index);
        if let clean_olean::ClosedRecheckRefusal::DependencyCycle { names } = refusal {
            for name in names {
                refusals_by_subject
                    .entry(name.clone())
                    .or_default()
                    .push(index);
            }
        }
    }
    let mut rows = BufWriter::new(File::create(out.join("declarations.jsonl"))?);
    let mut admitted = 0;
    let mut refused = 0;
    for name in &targets {
        let unit = unit(&env, name);
        let reasons = refusals_by_subject
            .get(&unit)
            .or_else(|| refusals_by_subject.get(&name.to_string()));
        // A family's members may be regenerated before a later comparison
        // fails. Any refusal of that replay unit dominates partial admission.
        // Quotient primitives are kernel-built and compared, not in admitted.
        let load_errors = loader_refusals
            .remove(&name.to_string())
            .unwrap_or_default();
        let accepted = reasons.is_none()
            && load_errors.is_empty()
            && (built.admitted.contains(name)
                || built.kernel().environment().get_quot(name).is_some());
        if accepted {
            admitted += 1;
        } else {
            refused += 1;
            if reasons.is_none() && load_errors.is_empty() {
                return Err(format!("unaccounted declaration: {name}, unit {unit}").into());
            }
        }
        serde_json::to_writer(
            &mut rows,
            &json!({
                "name": name.to_string(), "name_debug": format!("{name:?}"),
                "declared_in_artifact": declared_names.contains(name),
                "unit": unit, "verdict": if accepted { "admitted" } else { "refused" },
                "refusal_indices": reasons.cloned().unwrap_or_default(),
                "loader_refusals": load_errors
            }),
        )?;
        writeln!(rows)?;
    }
    let loader_only_names = loader_refusals.len();
    for (name, reasons) in loader_refusals {
        serde_json::to_writer(
            &mut rows,
            &json!({
                "name": name, "verdict": "refused-at-load", "loader_refusals": reasons
            }),
        )?;
        writeln!(rows)?;
    }
    rows.flush()?;
    let mut imports = Vec::new();
    let mut parts = BTreeMap::new();
    for summary in &summaries {
        let label = summary.module_name.as_deref().ok_or("unnamed import")?;
        let module = artifact_module(&lib, label);
        clean_olean::toolchain_identity::pinned_toolchain_module(
            module,
            &lib.join(module.replace('.', "/")).with_extension("olean"),
        )?;
        for suffix in ["olean", "olean.server", "olean.private"] {
            let relative = format!("{}.{}", module.replace('.', "/"), suffix);
            let path = lib.join(&relative);
            if path.is_file() {
                parts.insert(
                    relative,
                    blake3::hash(&std::fs::read(path)?).to_hex().to_string(),
                );
            }
        }
        imports.push(json!({
            "module": module, "part_label": label, "added": summary.added_constants,
            "skipped": summary.skipped_constants.iter().map(|c| json!({"name": c.name, "reason": c.reason})).collect::<Vec<_>>(),
            "refused_completions": summary.refused_completions.iter().map(|(n,r)| (n.to_string(),r)).collect::<Vec<_>>(),
            "shadowed": summary.shadowed_declarations.iter().map(|(n,r)| (n.to_string(),r)).collect::<Vec<_>>()
        }));
    }
    let passed = built.report.passed();
    let report = json!({
        "schema": 1, "unit": "F4", "toolchain": pin, "lean_lib": lib,
        "meaning": "complete accounting, not whole-Init acceptance; no semantic soundness claim",
        "target_names": targets.len(), "admitted_names": admitted, "refused_names": refused,
        "resident_names": resident_names, "declared_names": declared_names.len(),
        "module_inventory": module_inventory, "inventory_ms": inventory_ms,
        "loader_only_refused_names": loader_only_names,
        "load_ms": load_ms, "total_ms": started.elapsed().as_millis(),
        "max_heartbeats": options.max_heartbeats, "max_closure": options.max_closure,
        "imports": imports, "olean_parts_blake3": parts,
        "closed_replay": built.report,
        "whole_init_accepted": passed && refused == 0 && loader_only_names == 0
    });
    // The production API must withhold authority on a partial replay.
    assert_eq!(built.into_kernel().is_ok(), passed);
    serde_json::to_writer_pretty(File::create(out.join("report.json"))?, &report)?;
    eprintln!("accounted: admitted={admitted} refused={refused} whole_init_accepted={passed}");
    Ok(())
}
