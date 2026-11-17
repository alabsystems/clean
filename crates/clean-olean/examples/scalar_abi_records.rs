// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Read-only SDK/canonical record diagnostic. No scalar admission or native call.

use std::collections::{BTreeSet, HashSet};
use std::path::PathBuf;

use clean_kernel::expr::UsedConstants;
use clean_kernel::{BinderInfo, Environment, Expr, LeanWorld, Level, Name, TypeChecker, TypeError};
use clean_olean::ImportedConeGate;
use serde_json::json;

fn dependencies(env: &Environment) -> Result<BTreeSet<Name>, Box<dyn std::error::Error>> {
    let mut pending = vec![Name::from_string("UInt32"), Name::from_string("UInt64")];
    let mut seen = BTreeSet::new();
    while let Some(name) = pending.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        let info = env.get_const(&name).ok_or("absent canonical dependency")?;
        let mut refs = HashSet::new();
        info.type_
            .used_constants_dag(UsedConstants::WithProjectionStructures, &mut refs);
        if let Some(value) = &info.value {
            value.used_constants_dag(UsedConstants::WithProjectionStructures, &mut refs);
        }
        if let Some(inductive) = env.get_inductive(&name) {
            refs.extend(inductive.constructor_names.iter().cloned());
            let recursor = name.clone().str("rec");
            if env.get_recursor(&recursor).is_some() {
                refs.insert(recursor);
            }
        }
        if let Some(fields) = env.get_structure_field_names(&name) {
            for field in fields {
                let projection = Name::append(&name, &field.to_string());
                if env.get_const(&projection).is_some() {
                    refs.insert(projection);
                }
            }
        }
        pending.extend(refs);
    }
    Ok(seen)
}

fn record(env: &Environment, name: &Name) -> serde_json::Value {
    json!({
        "constant": env.get_const(name),
        "inductive": env.get_inductive(name),
        "constructor": env.get_constructor(name),
        "recursor": env.get_recursor(name),
        "fields": env.get_structure_field_names(name),
        "parents": env.get_structure_parents(name),
        "verification": format!("{:?}", env.declaration_verification(name)),
        "extern": format!("{:?}", env.get_extern(name)),
        "implemented_by": format!("{:?}", env.get_implemented_by(name)),
        "unsafe": env.is_unsafe(name),
        "partial": env.is_partial(name),
        "staged": env.is_staged_header(name),
        "needs_recheck": env.constant_needs_recheck(name),
        "kernel_theory": format!("{:?}", env.kernel_theory()),
        "native_fold_verdict": format!("{:?}", env.native_fold_verdict(name)),
        "native_fold_definition_verdict": format!("{:?}", env.native_fold_definition_verdict(name)),
    })
}

fn finish(tc: &TypeChecker<'_>) -> Result<(), String> {
    drop(
        tc.infer_type_full(&Expr::sort(Level::zero()))
            .map_err(|e| e.to_string())?,
    );
    // The final operation's scope drop may settle more work after its last tick.
    if tc.heartbeat_spent() {
        Err("heartbeat budget spent at final operation settlement".to_owned())
    } else {
        Ok(())
    }
}

fn validation_controls(env: &Environment) -> (Vec<serde_json::Value>, bool) {
    let nat = Expr::const_str("Nat");
    let candidates = [
        (
            "ill_typed_app_expected_type",
            Expr::app(
                Expr::lam(BinderInfo::Default, nat.clone(), nat.clone()),
                Expr::sort(Level::zero()),
            ),
        ),
        (
            "ill_typed_lambda_expected_type",
            Expr::lam(BinderInfo::Default, Expr::nat_lit(0), nat),
        ),
    ];
    let mut rows = Vec::new();
    for (name, candidate) in candidates {
        // Keep the permissive observation on a separate checker so it cannot
        // populate the full validation checker's caches or consume its budget.
        let mut infer_only = TypeChecker::new(env);
        infer_only.set_heartbeat_limit(1_000_000);
        let inferred = infer_only.infer_type(&candidate).map_err(|e| e.to_string());
        let mut full = TypeChecker::new(env);
        full.set_heartbeat_limit(1_000_000);
        let validated = full.infer_type_full(&candidate).map_err(|e| e.to_string());
        let sort = full.infer_sort(&candidate).map_err(|e| e.to_string());
        let finished = finish(&full);
        let matched = inferred.is_ok() && validated.is_err() && sort.is_err() && finished.is_ok();
        rows.push(
            json!({"name": name, "candidate": candidate, "infer_only": inferred,
            "infer_type_full": validated, "infer_sort": sort, "finish": finished,
            "control_matched": matched}),
        );
    }
    let mut limited = TypeChecker::new(env);
    limited.set_heartbeat_limit(1);
    let input = Expr::apps(
        Expr::const_str("Nat.pow"),
        [Expr::nat_lit(2), Expr::nat_lit(64)],
    );
    let reduced = limited.whnf(&input);
    let spent_before = limited.heartbeat_spent();
    let first = limited.infer_type_full(&Expr::sort(Level::zero()));
    let first_is_heartbeat = matches!(&first, Err(TypeError::HeartbeatExceeded { limit: 1, .. }));
    let second = limited.infer_type_full(&Expr::sort(Level::zero()));
    let second_is_heartbeat = matches!(&second, Err(TypeError::HeartbeatExceeded { limit: 1, .. }));
    let helper = finish(&limited);
    let mut healthy = TypeChecker::new(env);
    healthy.set_heartbeat_limit(1_000_000);
    let healthy_finish = finish(&healthy);
    let matched = spent_before
        && first_is_heartbeat
        && second_is_heartbeat
        && helper.is_err()
        && limited.heartbeat_spent()
        && healthy_finish.is_ok();
    rows.push(
        json!({"name": "nonresult_budget_error_remains_latched", "input": input,
        "unqualified_whnf_result": reduced, "spent_before": spent_before,
        "first_full_observation": first.map(|_| ()).map_err(|e| e.to_string()),
        "second_full_observation": second.map(|_| ()).map_err(|e| e.to_string()),
        "helper_observation": helper, "spent_after": limited.heartbeat_spent(),
        "healthy_checker_finish": healthy_finish, "control_matched": matched,
        "scope": "same limited checker; no budget or theory reset between observations"}),
    );
    let matched = rows.iter().all(|row| row["control_matched"] == true);
    (rows, matched)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if args.len() != 3 {
        return Err(
            "usage: scalar_abi_records <v4.30.0-rc2|v4.35.0> <official-lib/lean> <output.json>"
                .into(),
        );
    }
    let world = match args[0].as_str() {
        "v4.30.0-rc2" => LeanWorld::ORACLE,
        "v4.35.0" => LeanWorld::Lean435,
        _ => return Err("only the two requested official worlds are diagnostic inputs".into()),
    };
    let mut source = Environment::for_lean_replay();
    clean_olean::declare_environment_world(&mut source, world.tag())?;
    let base = source.clone();
    let modules = clean_olean::load_module_with_deps(
        &mut source,
        "Init.Prelude",
        &[PathBuf::from(&args[1])],
    )?;
    let canonical = Environment::try_with_prelude()?;
    let roots = dependencies(&canonical)?;
    let mut gate = ImportedConeGate::new(&base);
    let verdict = gate.check(&source, &roots);
    let passed = verdict.passed(false);
    let checked = gate.environment();
    let mut rows = Vec::new();
    for name in &roots {
        let mut comparison = json!({"executed": false});
        if passed {
            if let (Some(expected), Some(actual)) =
                (canonical.get_const(name), source.get_const(name))
            {
                let expected_levels = vec![Level::zero(); expected.level_params.len()];
                let actual_levels = vec![Level::zero(); actual.level_params.len()];
                let expected_type = expected
                    .type_
                    .instantiate_level_params_direct(&expected.level_params, &expected_levels);
                let actual_type = actual
                    .type_
                    .instantiate_level_params_direct(&actual.level_params, &actual_levels);
                let mut tc = TypeChecker::new(checked);
                tc.set_heartbeat_limit(1_000_000);
                let expected_type_check = tc
                    .infer_sort(&expected_type)
                    .map(|_| ())
                    .map_err(|e| e.to_string());
                let actual_type_check = tc
                    .infer_sort(&actual_type)
                    .map(|_| ())
                    .map_err(|e| e.to_string());
                let type_defeq = tc.is_def_eq(&expected_type, &actual_type);
                let body = match (&expected.value, &actual.value) {
                    (Some(e), Some(a)) => {
                        let e = e.instantiate_level_params_direct(
                            &expected.level_params,
                            &expected_levels,
                        );
                        let a =
                            a.instantiate_level_params_direct(&actual.level_params, &actual_levels);
                        let e_check = tc.check_type(&e, &expected_type).map_err(|e| e.to_string());
                        let a_check = tc.check_type(&a, &actual_type).map_err(|e| e.to_string());
                        let equal = tc.is_def_eq(&e, &a);
                        json!({"expected_check": e_check, "actual_check": a_check, "defeq": equal})
                    }
                    _ => serde_json::Value::Null,
                };
                let finished = finish(&tc);
                comparison = json!({"executed": true, "expected_type_check": expected_type_check,
                    "actual_type_check": actual_type_check, "type_defeq": type_defeq,
                    "body": body, "finish": finished, "heartbeats": 1_000_000,
                    "canonical_levels": expected_levels, "source_levels": actual_levels,
                    "scope": "closed all-zero universe instance only; no universal equivalence claim"});
            }
        }
        rows.push(
            json!({"name": name.to_string(), "source": record(&source, name),
            "canonical": record(&canonical, name), "checked": record(checked, name),
            "comparison_in_replayed_context": comparison}),
        );
    }
    let mut bounds = Vec::new();
    if passed {
        for width in [32_u32, 64] {
            let mut tc = TypeChecker::new(checked);
            tc.set_heartbeat_limit(1_000_000);
            let term = Expr::apps(
                Expr::const_str("Nat.pow"),
                [Expr::nat_lit(2), Expr::nat_lit(u64::from(width))],
            );
            let expected = Expr::nat_lit_u128(1_u128 << width);
            let wrong = Expr::nat_lit_u128((1_u128 << width) + 1);
            let term_check = tc
                .check_type(&term, &Expr::const_str("Nat"))
                .map_err(|e| e.to_string());
            let expected_check = tc
                .check_type(&expected, &Expr::const_str("Nat"))
                .map_err(|e| e.to_string());
            let wrong_check = tc
                .check_type(&wrong, &Expr::const_str("Nat"))
                .map_err(|e| e.to_string());
            let positive = tc.is_def_eq(&term, &expected);
            let negative = tc.is_def_eq(&term, &wrong);
            let finished = finish(&tc);
            bounds.push(json!({"width": width, "term": term, "expected": expected,
                "wrong": wrong, "term_check": term_check, "expected_check": expected_check,
                "wrong_check": wrong_check, "positive_defeq": positive, "wrong_defeq": negative,
                "finish": finished, "heartbeats": 1_000_000,
                "scope": "ordinary production kernel; existing reducer policy unchanged"}));
        }
    }
    let (controls, controls_matched) = if passed {
        validation_controls(checked)
    } else {
        (Vec::new(), false)
    };
    std::fs::write(
        &args[2],
        serde_json::to_vec_pretty(&json!({
            "claim": "record/comparison diagnostic only; no scalar admission, source ownership or native execution",
            "world": args[0], "modules_loaded": modules.len(), "abi_roots": roots.len(),
            "replay_passed": passed, "replay_verdict": verdict, "rows": rows, "closed_width_bounds": bounds,
            "type_validation": "infer_sort: full checking plus sort validation",
            "finish_validation": "infer_type_full(Sort0) followed by heartbeat_spent; no reset",
            "validation_controls": controls, "validation_controls_matched": controls_matched,
        }))?,
    )?;
    eprintln!(
        "world={} abi_roots={} replay_passed={} output={}",
        args[0],
        roots.len(),
        passed,
        args[2]
    );
    if !controls_matched {
        return Err(
            "diagnostic validation controls did not match; retained output is not qualified".into(),
        );
    }
    Ok(())
}
