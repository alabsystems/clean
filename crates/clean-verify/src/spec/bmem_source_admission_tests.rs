// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Complete source/admission regression custody for the original F1/S1a tables.
use super::{core_spec, decl_budget, source_admission_trace as trace, Specification};
use clean_elab::ElabError;
use clean_kernel::{
    ConstantKind, DeclarationVerification, Expr, ExprKind, Level, Name, TypeChecker,
};
use clean_parser::{parse_decl_exact, SurfaceDecl};
use serde::Deserialize;
use std::{collections::BTreeSet, time::Instant};

#[path = "bmem_source_table_identity.rs"]
mod identity;

macro_rules! require {
    ($condition:expr, $($message:tt)*) => {
        if !$condition { return Err(format!($($message)*)); }
    };
}

#[derive(Clone, Debug, Deserialize, serde::Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Row {
    name: String,
    kind: String,
    source: String,
}

fn declaration(source: &str) -> Result<(String, &'static str), String> {
    match parse_decl_exact(source).map_err(|e| e.to_string())? {
        SurfaceDecl::Def { name, .. } => Ok((name.name().to_string(), "def")),
        SurfaceDecl::Inductive { name, .. } => Ok((name.name().to_string(), "inductive")),
        _ => Err("only original def/inductive rows are allowed".into()),
    }
}

fn rows(raw: &[u8], expected: &[(&str, &str)]) -> Result<Vec<Row>, String> {
    let result: Vec<Row> = serde_json::from_slice(raw).map_err(|e| e.to_string())?;
    require!(
        result.len() == expected.len(),
        "wrong full-table denominator"
    );
    let mut ids = BTreeSet::new();
    let mut names = BTreeSet::new();
    for (row, (id, kind)) in result.iter().zip(expected) {
        require!(
            row.name == *id && row.kind == *kind,
            "wrong ID/kind/order: {}",
            row.name
        );
        require!(ids.insert(&row.name), "duplicate metadata ID");
        let (declared, actual_kind) = declaration(&row.source)?;
        let expected_name = row.name.strip_suffix("_RED").unwrap_or(&row.name);
        require!(
            declared == expected_name && actual_kind == row.kind,
            "source AST/name/kind mismatch"
        );
        require!(names.insert(declared), "duplicate declared source name");
    }
    Ok(result)
}

fn authenticate(
    raw: &[u8],
    expected: &[(&str, &str)],
    canonical: &[Row],
) -> Result<Vec<Row>, String> {
    let result = rows(raw, expected)?;
    require!(
        result == canonical,
        "source bytes differ from the complete current CLI table"
    );
    Ok(result)
}

// Kept private after the corrected inline owner exceeded 500 lines.
#[path = "bmem_source_admission_tests_input.rs"]
mod producer_input;
use producer_input::input;

use super::SpecDefinition;

#[path = "bmem_source_admission_tests_checks.rs"]
mod checks;
use checks::{cost_coverage, joined, original_red, replay_budget};

#[path = "bmem_source_state_snapshot.rs"]
mod state;
use state::snapshot;

#[test]
fn original_f1_s1a_complete_source_admission_join() {
    crate::test_utils::run_with_stack(|| {
        assert_eq!(
            clean_kernel::tc::declaration_budget_limit(),
            0,
            "no enclosing admission budget override"
        );
        assert_eq!(
            decl_budget::configured_budget().expect("ordinary default declaration budget"),
            decl_budget::DEFAULT_SPEC_DECL_BUDGET,
            "qualification cannot change or disable the normal budget"
        );
        let (f1_bytes, f1) = input("f1", identity::F1).expect("complete current F1 CLI input");
        let (s1a_bytes, s1a) = input("s1a", identity::S1A).expect("complete current S1a CLI input");
        let capture = trace::Capture::start();
        let cold = Instant::now();
        let built = Specification::new();
        let cold_seconds = cold.elapsed().as_secs_f64();
        eprintln!(
            "bmem-source-cold-full seconds={cold_seconds} accepted={} actual_error={:?}",
            built.is_ok(),
            built.as_ref().err()
        );
        let full = built.expect("ordinary complete fresh Full must build");
        // The complete Full bundle must reach its ordinary Classical mode.
        assert_eq!(
            full.env().mode(),
            clean_kernel::mode::CleanMode::Classical,
            "ordinary Full uses the existing classical prelude mode"
        );
        eprintln!(
            "bmem-source-profile mode={:?} kernel_theory={:?} declaration_budget={}",
            full.env().mode(),
            full.env().kernel_theory(),
            decl_budget::DEFAULT_SPEC_DECL_BUDGET
        );
        let full_events = capture.events();
        let owned = core_spec::test_bmem_source_rows();
        assert_eq!(
            owned.len(),
            174,
            "exact current production trie21 + core153"
        );
        let f1_owned: BTreeSet<_> = f1
            .iter()
            .filter(|row| owned.iter().any(|r| r.0 == row.name))
            .map(|r| r.name.as_str())
            .collect();
        let s1a_owned: BTreeSet<_> = s1a
            .iter()
            .filter(|row| owned.iter().any(|r| r.0 == row.name))
            .map(|r| r.name.as_str())
            .collect();
        assert_eq!(
            f1_owned.intersection(&s1a_owned).count(),
            13,
            "explicit source-owned overlap"
        );
        let observed: Vec<_> = full_events
            .iter()
            .filter(|e| owned.iter().any(|r| r.0 == e.header))
            .collect();
        assert_eq!(
            observed.len(),
            owned.len(),
            "every ordinary production row observed once"
        );
        for ((name, kind, source), event) in owned.iter().zip(&observed) {
            assert_eq!(
                (event.header.as_str(), event.kind, event.source.as_str()),
                (*name, *kind, *source),
                "normal production order/source"
            );
            assert!(
                event.absent_before
                    && event.accepted
                    && !event.exhausted
                    && event.limit == decl_budget::DEFAULT_SPEC_DECL_BUDGET,
                "normal first admission: {event:?}"
            );
        }
        let mut failures = Vec::new();
        let mut costs = Vec::new();
        for (table, candidates, denominator, expected_resident) in
            [("F1", &f1, 54, 36), ("S1a", &s1a, 29, 21)]
        {
            let mut current = full.clone();
            let mut resident_count = 0;
            for (index, row) in candidates.iter().enumerate() {
                let started = Instant::now();
                let name = row.name.strip_suffix("_RED").unwrap_or(&row.name);
                let resident = owned.iter().position(|r| r.0 == name);
                let (result, route, actual_error, ticks, limit, admission_seconds) = if let Some(
                    owner_index,
                ) = resident
                {
                    resident_count += 1;
                    let event = observed[owner_index];
                    (
                        replay_budget(|| joined(&full, row, event)),
                        "normal-first-admission-join",
                        event.outcome.clone(),
                        event.ticks,
                        event.limit,
                        event.seconds,
                    )
                } else {
                    eprintln!(
                        "bmem-source-stage table={table} index={index} id={} stage=snapshot-before",
                        row.name
                    );
                    let before = snapshot(&current);
                    eprintln!(
                        "bmem-source-stage table={table} index={index} id={} stage=snapshot-after",
                        row.name
                    );
                    eprintln!(
                            "bmem-source-stage table={table} index={index} id={} stage=admission-before",
                            row.name
                        );
                    let outcome =
                        decl_budget::with_spec_declaration_budget(|| match row.kind.as_str() {
                            "inductive" => current.add_inductive(&row.source, &row.name),
                            "def" => current.add_recursive_def(&row.source, &row.name),
                            _ => panic!("validated original kind required"),
                        });
                    eprintln!(
                        "bmem-source-stage table={table} index={index} id={} stage=admission-after",
                        row.name
                    );
                    let event = capture
                        .last_event()
                        .expect("actual checked API observation");
                    let result = if row.name.ends_with("_RED") {
                        if snapshot(&current) != before {
                            Err("RED changed captured declaration/checker state".into())
                        } else {
                            replay_budget(|| original_red(&current, row, &event))
                        }
                    } else {
                        outcome
                            .map_err(|e| format!("{e:?}"))
                            .and_then(|()| replay_budget(|| joined(&current, row, &event)))
                    };
                    (
                        result,
                        "ordinary-existing-checked-API",
                        event.outcome.clone(),
                        event.ticks,
                        event.limit,
                        event.seconds,
                    )
                };
                let cost = serde_json::json!({"table":table,"index":index,"id":row.name,"kind":row.kind,
                    "source_blake3":blake3::hash(row.source.as_bytes()).to_hex().to_string(),"route":route,
                    "case_seconds":started.elapsed().as_secs_f64(),"actual_first_admission_ticks":ticks,
                    "actual_first_admission_seconds":admission_seconds,"production_owner_index":resident,
                    "ambient_limit":limit,"ticks_metered":limit!=0,"actual_registration_outcome":actual_error,"check":format!("{result:?}")});
                eprintln!("bmem-source-case {cost}");
                costs.push((table, index, row.name.clone()));
                if let Err(error) = result {
                    failures.push(format!("{table}[{index}] {}: {error}", row.name));
                }
            }
            assert_eq!(candidates.len(), denominator);
            assert_eq!(resident_count, expected_resident);
        }
        cost_coverage(&costs).expect("complete costs in original order");
        for omitted in 0..costs.len() {
            let mut broken = costs.clone();
            broken.remove(omitted);
            assert!(
                cost_coverage(&broken).is_err(),
                "omitted cost row must refuse"
            );
        }
        // Controls for previously omitted state; all changes stay on clones.
        let mut record_name = full.clone();
        let baseline = snapshot(&record_name);
        record_name
            .definitions_mut()
            .values_mut()
            .next()
            .expect("actual record")
            .name
            .push('_');
        assert_ne!(
            snapshot(&record_name),
            baseline,
            "record name is observable state"
        );
        let mut optional_deps = full.clone();
        let key = optional_deps
            .definitions()
            .keys()
            .next()
            .expect("actual record")
            .clone();
        optional_deps
            .definitions_mut()
            .get_mut(&key)
            .expect("record")
            .dependencies = None;
        let absent = snapshot(&optional_deps);
        optional_deps
            .definitions_mut()
            .get_mut(&key)
            .expect("record")
            .dependencies = Some(Default::default());
        assert_ne!(
            snapshot(&optional_deps),
            absent,
            "None differs from Some(empty)"
        );
        let mut sticky = full.clone();
        let baseline = snapshot(&sticky);
        assert!(
            !baseline.checker_settings.cumulative_ever,
            "ordinary default Full sticky history"
        );
        sticky.env_mut().set_cumulative(true);
        sticky
            .env_mut()
            .set_cumulative(baseline.checker_settings.cumulative);
        let changed = snapshot(&sticky);
        assert_eq!(
            changed.generation, baseline.generation,
            "setter does not bump generation"
        );
        assert_eq!(
            changed.serialized, baseline.serialized,
            "serde omits sticky history"
        );
        assert_ne!(
            changed, baseline,
            "typed checker settings retain cumulative_ever"
        );
        // Explicit live guards are additional controls, not original RED verdicts.
        // Run after recording all 83 outcomes so a diagnostic mismatch cannot
        // prevent the remaining original cases from being attempted.
        let mut unique = BTreeSet::new();
        for row in f1.iter().chain(&s1a) {
            if !owned.iter().any(|r| r.0 == row.name) || !unique.insert(row.name.clone()) {
                continue;
            }
            let event = observed[owned.iter().position(|r| r.0 == row.name).expect("owner")];
            let mut wrong = row.clone();
            wrong.source.push(' ');
            assert!(
                joined(&full, &wrong, event).is_err(),
                "right cached Expr with wrong source must refuse"
            );
            let mut forged = full.clone();
            if row.kind == "def" {
                forged
                    .definitions_mut()
                    .get_mut(&row.name)
                    .expect("actual metadata")
                    .type_src
                    .push(' ');
                assert!(
                    joined(&forged, row, event).is_err(),
                    "public metadata cannot seal source authority"
                );
            }
            let name = row.name.as_str();
            for source in [
                row.source.clone(),
                if row.kind == "inductive" {
                    format!("inductive {name} : Type\n| collision_control : {name}")
                } else {
                    format!("def {name} : Nat := 0")
                },
            ] {
                let mut duplicate = full.clone();
                let before = snapshot(&duplicate);
                let refused = decl_budget::with_spec_declaration_budget(|| {
                    if row.kind == "inductive" {
                        duplicate.add_inductive(&source, "explicit duplicate-name control")
                    } else {
                        duplicate.add_recursive_def(&source, "explicit duplicate-name control")
                    }
                });
                let actual = capture.last_event().expect("actual duplicate call");
                let cause = if row.kind == "inductive" {
                    matches!(actual.elaborator_error.as_ref(),
                        Some(ElabError::KernelRegistrationFailed { operation, detail })
                            if operation == "source family name preflight"
                                && detail == &format!("environment already contains '{}'",
                                    Name::from_string(name).to_unambiguous_string()))
                } else {
                    matches!(actual.elaborator_error.as_ref(),
                        Some(ElabError::KernelRegistrationFailed {detail,..}) if detail==&format!("Duplicate declaration: {name}"))
                };
                if refused.is_ok() || !cause || snapshot(&duplicate) != before {
                    failures.push(format!(
                        "{name}: UNQUALIFIED duplicate guard: {refused:?}; {actual:?}"
                    ));
                }
            }
            if row.kind == "inductive" {
                for ctor in &full
                    .env()
                    .get_inductive(&Name::from_string(name))
                    .expect("actual family")
                    .constructor_names
                {
                    let mut duplicate = full.clone();
                    let before = snapshot(&duplicate);
                    let source = format!("def {ctor} : Nat := 0");
                    let refused = decl_budget::with_spec_declaration_budget(|| {
                        duplicate.add_recursive_def(&source, "existing constructor collision")
                    });
                    let actual = capture.last_event().expect("actual constructor collision");
                    let cause = matches!(actual.elaborator_error.as_ref(),
                        Some(ElabError::KernelRegistrationFailed {detail,..}) if detail==&format!("Duplicate declaration: {ctor}"));
                    if refused.is_ok() || !cause || snapshot(&duplicate) != before {
                        failures.push(format!("{ctor}: UNQUALIFIED constructor duplicate guard: {refused:?}; {actual:?}"));
                    }
                }
            }
        }
        eprintln!(
            "bmem-source-full cold_seconds={cold_seconds} F1_raw_blake3={} S1a_raw_blake3={}",
            blake3::hash(&f1_bytes),
            blake3::hash(&s1a_bytes)
        );
        assert!(
            failures.is_empty(),
            "original obligations remain unqualified:\n{}",
            failures.join("\n")
        );
    });
}

#[test]
fn whole_table_custody_rejects_missing_empty_malformed_duplicate_reorder_and_source_drift() {
    for (table, ids) in [("f1", identity::F1), ("s1a", identity::S1A)] {
        let (raw, canonical) = input(table, ids).expect("actual CLI fixture required");
        for bad in [b"".as_slice(), b"[]".as_slice(), b"[".as_slice()] {
            assert!(authenticate(bad, ids, &canonical).is_err());
        }
        for index in 0..canonical.len() {
            let mut omitted = canonical.clone();
            omitted.remove(index);
            assert!(authenticate(
                &serde_json::to_vec(&omitted).expect("JSON"),
                ids,
                &canonical
            )
            .is_err());
            let mut changed = canonical.clone();
            changed[index].source.push(' ');
            assert!(authenticate(
                &serde_json::to_vec(&changed).expect("JSON"),
                ids,
                &canonical
            )
            .is_err());
        }
        let mut duplicate = canonical.clone();
        duplicate[1] = duplicate[0].clone();
        assert!(authenticate(
            &serde_json::to_vec(&duplicate).expect("JSON"),
            ids,
            &canonical
        )
        .is_err());
        let mut reordered = canonical.clone();
        reordered.swap(0, 1);
        assert!(authenticate(
            &serde_json::to_vec(&reordered).expect("JSON"),
            ids,
            &canonical
        )
        .is_err());
        let mut malformed = canonical.clone();
        malformed[0].source = "inductive".into();
        assert!(authenticate(
            &serde_json::to_vec(&malformed).expect("JSON"),
            ids,
            &canonical
        )
        .is_err());
        let mut bad_kind = canonical.clone();
        bad_kind[0].kind = "cachedExpr".into();
        assert!(authenticate(
            &serde_json::to_vec(&bad_kind).expect("JSON"),
            ids,
            &canonical
        )
        .is_err());
        let mut supplied_expr = serde_json::to_value(&canonical).expect("JSON");
        supplied_expr[0]["kernel_expr"] =
            serde_json::Value::String("a cached expression cannot authenticate source".into());
        assert!(authenticate(
            &serde_json::to_vec(&supplied_expr).expect("JSON"),
            ids,
            &canonical
        )
        .is_err());
        assert_eq!(
            authenticate(&raw, ids, &canonical).expect("authentic full input"),
            canonical
        );
    }
}
