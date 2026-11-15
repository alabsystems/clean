// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_export_writer_cic_l_round_trips_and_is_the_same_in_another_process() {
    let _heavy = HEAVY.lock().unwrap_or_else(PoisonError::into_inner);
    let minted = minted();
    let first = minted.bytes.split(|b| *b == b'\n').next().expect("a line");
    let header: Value = serde_json::from_slice(first).expect("the meta line");
    assert_eq!(header["meta"]["exporter"]["name"], EXPORTER_NAME);
    assert_eq!(header["meta"]["format"]["version"], "3.1.0");
    assert_eq!(header["meta"]["lean"]["version"], minted.meta.lean_version);
    assert_eq!(minted.summary.bytes, minted.bytes.len() as u64);
    assert!(
        minted.summary.declarations > 1000,
        "the closure of CIC_L is not a handful of constants: {}",
        minted.summary.declarations
    );
    for axiom in &minted.summary.axioms {
        assert!(
            FOUNDATIONAL_AXIOMS.contains(&axiom.as_str()),
            "the closure declares the axiom {axiom}"
        );
    }

    // Read back by Clean's reader and written again: the same bytes.
    check_export_round_trip(minted.bytes.as_slice(), &minted.summary).expect("the round trip");

    // Negative control: one byte of a binder's information changed is not
    // what was written.
    let needle = br#""binderInfo":"default""#;
    let at = minted
        .bytes
        .windows(needle.len())
        .position(|w| w == needle)
        .expect("a default binder");
    let mut tampered = minted.bytes.clone();
    tampered.splice(
        at..at + needle.len(),
        br#""binderInfo":"implicit""#.iter().copied(),
    );
    match check_export_round_trip(tampered.as_slice(), &minted.summary) {
        Err(ExportWriteError::RoundTrip { .. }) => {}
        other => panic!("a changed binder must fail the round trip, got {other:?}"),
    }

    // Written again by this process from its own load of the same modules.
    let (modules, lean_paths, meta) = (
        minted.modules.clone(),
        minted.lean_paths.clone(),
        minted.meta.clone(),
    );
    let (again, summary, narrow, narrow_summary) = on_big_stack(move || {
        let mut env = Environment::for_lean_replay();
        let mut visited = hashbrown::HashSet::new();
        for module in &modules {
            load_module_with_deps_shared(&mut env, module, &lean_paths, &mut visited)
                .unwrap_or_else(|e| panic!("cannot load {module}: {e}"));
        }
        let targets: BTreeSet<Name> = env
            .constants()
            .filter(|c| c.name.to_string().contains("CICL."))
            .map(|c| c.name.clone())
            .collect();
        let mut out = Vec::new();
        let summary = write_export(&env, &targets, &meta, &mut out).expect("write the cone");
        let one: BTreeSet<Name> = [Name::from_string(LEVEL_SUBJECT)].into();
        let mut narrow = Vec::new();
        let narrow_summary = write_export(&env, &one, &meta, &mut narrow).expect("write one cone");
        (out, summary, narrow, narrow_summary)
    });
    assert_eq!(summary, minted.summary);
    assert!(again == minted.bytes, "two processes wrote different bytes");

    // A KNOWN GAP, pinned so that it fails the day it closes. The front door
    // (`check_export_reader`) builds a level through the kernel's simplifying
    // constructors (R125). Lean wrote `LEVEL_SUBJECT`'s sort over
    // `max u_1 (imax (u+1) u_1)`, which those constructors build as
    // `imax (u+1) u_1`; the writer writes Lean's level, and the front door's
    // replay then REFUSES the honest declaration (exit 1, a type mismatch
    // between two sorts), whoever exported it. A false refusal, never a
    // wrong accept. The round trip and the fenced entry read levels node for
    // node, as the `.olean` loader does (R150), and the entry admits it.
    check_export_round_trip(narrow.as_slice(), &narrow_summary).expect("the narrow round trip");
    let front_door = {
        let bytes = narrow.clone();
        on_big_stack(move || check_export_reader(bytes.as_slice(), ExportCheckOptions::default()))
    };
    assert_eq!(
        front_door.exit_code, 1,
        "{:?} {:?} {:?}",
        front_door.decline_reason, front_door.first_refusal, front_door.reader_error
    );
    let first = front_door
        .first_refusal
        .as_ref()
        .expect("the front door's first refusal");
    assert_eq!(first.name, LEVEL_SUBJECT);
    assert!(
        first.reason.contains("TypeMismatch") && first.reason.contains("Sort("),
        "{}",
        first.reason
    );
    assert_eq!(front_door.refused, 1);
    let entry = reference(narrow);
    assert!(
        entry.accepted,
        "refusals {:?}, unpermitted {:?}",
        entry.refusals, entry.unpermitted_axioms
    );
    assert_eq!(entry.declarations, narrow_summary.declarations);
}

#[test]
fn test_export_writer_cic_l_is_accepted_by_the_fenced_kernel() {
    let _heavy = HEAVY.lock().unwrap_or_else(PoisonError::into_inner);
    let minted = minted();
    let report = reference(minted.bytes.clone());
    assert!(
        report.accepted,
        "refusals {:?}, unpermitted {:?}, reader {:?}",
        report.refusals, report.unpermitted_axioms, report.reader_error
    );
    assert_eq!(report.declarations, minted.summary.declarations);
    assert_eq!(report.admitted, report.declarations);
    let mut declared = minted.summary.axioms.clone();
    declared.sort();
    assert_eq!(report.axioms, declared);
    eprintln!(
        "Q1 fenced entry: {} declarations admitted, axioms {:?}",
        report.admitted, report.axioms
    );

    // Negative control for the caller's own axiom policy: the same bytes
    // under a policy that leaves `Quot.sound` out are not accepted, for that
    // axiom alone.
    assert!(report.axioms.contains(&"Quot.sound".to_owned()));
    let bytes = minted.bytes.clone();
    let narrow = reference_permitted(bytes, &["propext"]);
    assert!(!narrow.accepted);
    assert_eq!(narrow.unpermitted_axioms, vec!["Quot.sound".to_owned()]);
    assert!(narrow.refusals.is_empty(), "{:?}", narrow.refusals);
    assert_eq!(narrow.admitted, narrow.declarations);
}

#[test]
fn test_export_writer_cic_l_planted_axiom_is_refused_by_name() {
    let _heavy = HEAVY.lock().unwrap_or_else(PoisonError::into_inner);
    let minted = minted();
    let planted = with_planted_axiom(minted);
    let report = reference(planted.clone());
    assert!(!report.accepted);
    assert!(report.reader_error.is_none(), "{:?}", report.reader_error);
    // The entry itself admits no axiom outside Ax0: the planted one is
    // refused by name, and the theorem proved by it with it. Nothing else is.
    assert!(
        report.refusals.iter().any(|refusal| {
            refusal.starts_with("planted_axiom: ")
                && refusal.contains("reaches the axiom `planted_axiom`, which is outside Ax0")
        }),
        "{:?}",
        report.refusals
    );
    assert!(
        report.refusals.iter().any(|refusal| {
            refusal.starts_with("planted_theorem: ")
                && refusal.contains("DependencyRefused")
                && refusal.contains("blocked_by: \"planted_axiom\"")
        }),
        "{:?}",
        report.refusals
    );
    for refusal in &report.refusals {
        assert!(
            refusal.starts_with("planted_axiom: ") || refusal.starts_with("planted_theorem: "),
            "a refusal about something else: {refusal}"
        );
    }
    assert!(!report.axioms.contains(&"planted_axiom".to_owned()));
    assert_eq!(report.declarations, minted.summary.declarations + 2);
    assert_eq!(report.admitted, minted.summary.declarations);

    let path = write_beside(minted, "planted_axiom.ndjson", &planted);
    for (reader, out) in [
        ("Replay.lean", lean_replay(&path)),
        ("lean4export", lean_replay_upstream(&path)),
    ] {
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert_eq!(out.status.code(), Some(1), "{reader}: {stderr}");
        assert!(
            stderr.contains("axioms outside the permitted set") && stderr.contains("planted_axiom"),
            "{reader}: {stderr}"
        );
    }
}

#[test]
fn test_export_writer_cic_l_ill_typed_body_is_refused_by_name() {
    let _heavy = HEAVY.lock().unwrap_or_else(PoisonError::into_inner);
    let minted = minted();
    let ill_typed = with_ill_typed_body(minted);
    let report = reference(ill_typed.clone());
    assert!(!report.accepted);
    assert!(
        report.unpermitted_axioms.is_empty(),
        "{:?}",
        report.unpermitted_axioms
    );
    let about_subject: Vec<&String> = report
        .refusals
        .iter()
        .filter(|refusal| refusal.starts_with(&format!("{SUBJECT}: ")))
        .collect();
    assert!(
        !about_subject.is_empty(),
        "no refusal names {SUBJECT}: {:?}",
        report.refusals
    );
    assert!(
        about_subject
            .iter()
            .any(|refusal| refusal.contains("Type mismatch") && refusal.contains("got Prop")),
        "{about_subject:?}"
    );
    for refusal in &report.refusals {
        assert!(
            refusal.starts_with(&format!("{SUBJECT}: ")),
            "a refusal about something else: {refusal}"
        );
    }
    assert_eq!(report.admitted, report.declarations - 1);

    let path = write_beside(minted, "ill_typed.ndjson", &ill_typed);
    for (reader, out) in [
        ("Replay.lean", lean_replay(&path)),
        ("lean4export", lean_replay_upstream(&path)),
    ] {
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert_eq!(out.status.code(), Some(1), "{reader}: {stderr}");
        assert!(
            stderr.contains("REJECTED (kernel)")
                && stderr.contains(&format!("declaration type mismatch, '{SUBJECT}' has type")),
            "{reader}: {stderr}"
        );
    }
}

#[test]
fn test_export_writer_cic_l_is_accepted_by_pinned_leans_kernel() {
    let _heavy = HEAVY.lock().unwrap_or_else(PoisonError::into_inner);
    let minted = minted();
    let out = lean_replay(&minted.path);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(0), "{stderr}");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let last = stdout.lines().last().expect("a verdict line");
    let verdict: Value = serde_json::from_str(last).expect("a JSON verdict");
    assert_eq!(verdict["verdict"], "accepted");
    assert_eq!(verdict["kernel"], "Lean.Environment.replay");
    assert_eq!(verdict["lean_version"], minted.meta.lean_version);
    assert_eq!(verdict["lean_githash"], minted.meta.lean_githash);
    assert_eq!(
        verdict["declarations"].as_u64(),
        Some(minted.summary.declarations as u64)
    );
    assert_eq!(verdict["lines"].as_u64(), Some(minted.summary.lines));
    let declared: Vec<Value> = minted
        .summary
        .axioms
        .iter()
        .map(|a| Value::from(a.as_str()))
        .collect();
    let mut sorted = declared.clone();
    sorted.sort_by_key(|v| v.as_str().map(str::to_owned));
    assert_eq!(verdict["axioms"], Value::Array(sorted));
    eprintln!("Q1 Lean kernel: {last}");
}

#[test]
fn test_export_writer_cic_l_is_accepted_by_lean_through_lean4exports_own_parser() {
    let _heavy = HEAVY.lock().unwrap_or_else(PoisonError::into_inner);
    let minted = minted();
    let out = lean_replay_upstream(&minted.path);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(0), "{stderr}");
    assert!(
        stderr.contains("reader lean4export@"),
        "the reader's commit is not stated: {stderr}"
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    let last = stdout.lines().last().expect("a verdict line");
    let verdict: Value = serde_json::from_str(last).expect("a JSON verdict");
    assert_eq!(verdict["verdict"], "accepted");
    assert_eq!(verdict["kernel"], "Lean.Environment.replay");
    assert_eq!(verdict["reader"], "lean4export Export.parseStream");
    assert_eq!(verdict["lean_version"], minted.meta.lean_version);
    assert_eq!(verdict["lean_githash"], minted.meta.lean_githash);
    let declarations = Some(minted.summary.declarations as u64);
    assert_eq!(verdict["declarations"].as_u64(), declarations);
    assert_eq!(verdict["order"].as_u64(), declarations);
    let mut declared: Vec<Value> = minted
        .summary
        .axioms
        .iter()
        .map(|a| Value::from(a.as_str()))
        .collect();
    declared.sort_by_key(|v| v.as_str().map(str::to_owned));
    assert_eq!(verdict["axioms"], Value::Array(declared));
    eprintln!("Q1 Lean kernel, lean4export's parser: {last}");
}

#[test]
fn test_export_writer_full_export_matches_pinned_leans_environment_except_outparam_hint() {
    let _heavy = HEAVY.lock().unwrap_or_else(PoisonError::into_inner);
    let minted = minted();
    let mut command = Command::new(repo_root().join("scripts/lean_export_replay.sh"));
    command.args(["--reader", "upstream"]).arg(&minted.path);
    for module in &minted.modules {
        command.args(["--against", module]);
    }
    for path in &minted.lean_paths {
        command.arg("--lean-path").arg(path);
    }
    let out = command.output().expect("compare the FULL export with Lean");
    assert_eq!(
        out.status.code(),
        Some(1),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8(out.stdout).expect("comparison stdout");
    let last = stdout.lines().last().expect("the comparison verdict");
    let verdict: Value = serde_json::from_str(last).expect("comparison JSON");
    assert_eq!(
        verdict["compared"].as_u64(),
        Some(minted.summary.declarations as u64)
    );
    assert_eq!(
        verdict["equal"].as_u64(),
        Some(minted.summary.declarations as u64 - 1)
    );
    assert_eq!(verdict["absent"], serde_json::json!([]));
    assert_eq!(verdict["differing_count"], 1);
    assert_eq!(
        verdict["differing_by_field"],
        serde_json::json!({"hints": 1})
    );
    assert_eq!(
        verdict["differing"],
        serde_json::json!([
            {"name": "outParam", "fields": ["hints regular 1 vs abbrev"]}
        ])
    );
    eprintln!("Q1 FULL against Lean: {last}");
}

#[test]
fn test_reference_command_refuses_front_door_options_and_missing_files() {
    for args in [
        vec!["--reference", "--max-heartbeats", "1", "missing.ndjson"],
        vec!["--reference", "--permit"],
        vec!["--reference", "missing.ndjson"],
    ] {
        let out = Command::new(env!("CARGO_BIN_EXE_clean_export_check"))
            .args(&args)
            .output()
            .expect("run reference CLI usage control");
        assert_eq!(out.status.code(), Some(2));
        assert!(out.stdout.is_empty());
    }
}
