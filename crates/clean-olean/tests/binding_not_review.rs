// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Bounded compiled-byte qualification of BindingNotReview, not a new quorum
//! vote or production pin acceptance. All missing data/tools and unsupported
//! cones fail closed. The parent supplies frozen generated data; no pin minting
//! or compiler/kernel bypass is available in this test.

#[path = "binding_not_review/artifact.rs"]
mod artifact;
#[path = "binding_not_review/checks.rs"]
mod checks;
#[path = "binding_not_review/controls.rs"]
mod controls;
#[path = "binding_not_review/data.rs"]
mod data;
#[path = "binding_not_review/guards.rs"]
mod guards;
#[path = "binding_not_review/identity.rs"]
mod identity;
#[path = "binding_not_review/stock.rs"]
mod stock;

use checks::{checked_copy, closure, kind, metadata, mismatch, source_modules};
use clean_kernel::env::{ConstantKind, Declaration, Environment};
use clean_kernel::{Expr, Name};
use clean_olean::ndjson::{check_export_round_trip, write_export, ExportWriteSummary};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{
    load_module_with_deps, read_artifact, reference_base_closed, require_pinned_lean_lib_path,
    ArtifactDepth,
};
use serde_json::json;
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::process::Command;

const ROOT: &str = "BindingNotReview";
const PIN: &str = "leanprover/lean4:v4.30.0-rc2";
const AX0: [&str; 3] = ["propext", "Quot.sound", "Classical.choice"];

#[test]
fn binding_not_review_compiled_three_kernels_and_negative_controls() {
    std::thread::Builder::new()
        .name("binding-not-review".into())
        .stack_size(1024 * 1024 * 1024)
        .spawn(qualify)
        .expect("large-stack qualification worker")
        .join()
        .expect("compiled qualification failed");
}

fn qualify() {
    for flag in [
        "CLEAN_NATIVE_FOLD_REPIN",
        "CLEAN_NATIVE_FOLD_BOOTSTRAP_LOAD",
    ] {
        assert!(std::env::var_os(flag).is_none(), "{flag} must be absent");
    }
    let repo = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("repo root");
    let package = repo.join("theories/binding_not_review");
    let driver = repo.join(
        "reports/2026-11-14-extension-binding-not-review/generated/BindingNotReviewCensus.lean",
    );
    let manifest_path = package.join("manifest.json");
    let census_path = package.join("lean_census.json");
    let closure_path = package.join("axiom_closures.json");
    let pin_path = package.join("statement_pins.json");
    let manifest = data::read(&manifest_path);
    let census = data::read(&census_path);
    let closures = data::read(&closure_path);
    guards::headers(&manifest, &census, &closures).expect("exact receipt metadata");
    for path in [repo.join("lean-toolchain"), package.join("lean-toolchain")] {
        assert_eq!(
            std::fs::read_to_string(&path)
                .expect("required Lean pin")
                .trim(),
            PIN
        );
    }
    let lean_source_sha = data::file_sha(&package.join("BindingNotReview.lean"));
    let census_source_sha = data::file_sha(&driver);
    controls::receipts(
        &manifest,
        &census,
        &closures,
        &lean_source_sha,
        &census_source_sha,
    );
    let mut book = BTreeMap::new();
    for path in [
        &manifest_path,
        &census_path,
        &closure_path,
        &driver,
        &package.join("BindingNotReview.lean"),
        &package.join("ORDER"),
        &package.join("lean-toolchain"),
    ] {
        book.insert(path.to_owned(), data::file_sha(path));
    }
    let order = std::fs::read_to_string(package.join("ORDER")).expect("theory ORDER");
    let modules: Vec<_> = order
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(|l| l.replace('/', "."))
        .collect();
    assert_eq!(modules, vec![ROOT.to_owned()]);
    let mut sources = BTreeSet::new();
    source_modules(&package, &package, &mut sources);
    assert_eq!(
        sources,
        modules.iter().cloned().collect(),
        "every own logical source is in ORDER"
    );
    let expected = guards::inventory(&manifest).expect("exact own manifest inventory");
    let stock = stock::Stock::existing(&repo);
    let lib = require_pinned_lean_lib_path().expect("repository-pinned Lean SDK required");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean binary");
    let bin = lean.parent().expect("Lean bin");
    let checker = bin.join("leanchecker");
    book.insert(lean.clone(), data::file_sha(&lean));
    book.insert(checker.clone(), data::file_sha(&checker));
    let original_compiled = compiled_fixture_dir("binding_not_review");
    let derived = artifact::derive(&repo, &lean, &lib, &original_compiled, &manifest, &mut book);
    let compiled = derived.compiled.clone();
    let olean = compiled.join("BindingNotReview.olean");
    let lean_path = std::env::join_paths([&compiled, &lib]).expect("Lean search path");
    let mut paths = vec![bin.to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));
    let bin_path = std::env::join_paths(paths).expect("pinned Lean PATH");
    let out = Command::new(&checker)
        .args(["--fresh", ROOT])
        .current_dir(&compiled)
        .env("LEAN_PATH", &lean_path)
        .env("PATH", &bin_path)
        .output()
        .expect("fresh independent leanchecker");
    data::command_ok("binding-not leanchecker --fresh", &out);
    let out = Command::new(&lean)
        .arg(&driver)
        .current_dir(&compiled)
        .env("LEAN_PATH", &lean_path)
        .env("PATH", &bin_path)
        .output()
        .expect("fresh compiled-module Lean census");
    let lean_rows = data::fresh_census(&out, &manifest, &census);
    assert_eq!(
        lean_rows.keys().collect::<BTreeSet<_>>(),
        expected.keys().collect(),
        "exact Lean own declaration set"
    );

    let mut loaded = Environment::for_lean_replay();
    let summaries = load_module_with_deps(&mut loaded, ROOT, &[compiled.clone(), lib.clone()])
        .expect("actual compiled module closure");
    let own: Vec<_> = summaries
        .iter()
        .filter(|s| s.module_name.as_deref() == Some(ROOT))
        .collect();
    assert_eq!(
        own.len(),
        1,
        "one logical module, no skipped private module"
    );
    let mut added = BTreeSet::new();
    for s in own {
        assert!(
            s.skipped_constants.is_empty(),
            "own conversion skips: {:?}",
            s.skipped_constants
        );
        assert!(
            s.skipped_not_replayable.is_empty(),
            "own unsafe/partial skips"
        );
        assert!(
            s.shadowed_declarations.is_empty()
                && s.restated_declarations.is_empty()
                && s.refused_completions.is_empty(),
            "own declaration shadow/restatement/refusal"
        );
        for n in &s.added_names {
            assert!(added.insert(n.clone()), "duplicate own addition");
        }
    }
    let targets: BTreeSet<_> = loaded
        .constants()
        .filter(|c| {
            loaded
                .get_constant_origin(&c.name)
                .and_then(|o| o.module_name())
                == Some(ROOT)
        })
        .map(|c| c.name.clone())
        .collect();
    assert_eq!(targets, added, "origin census equals own loader additions");
    let artifact = read_artifact(ROOT, &olean, ArtifactDepth::Names)
        .expect("authoritative compiled own names");
    let artifact_names: BTreeSet<_> = artifact.names.iter().cloned().collect();
    assert_eq!(
        artifact_names.len(),
        artifact.names.len(),
        "no duplicate artifact names"
    );
    assert_eq!(
        targets, artifact_names,
        "no omitted compiler/private declaration"
    );
    assert_eq!(
        targets
            .iter()
            .map(ToString::to_string)
            .collect::<BTreeSet<_>>(),
        expected.keys().cloned().collect()
    );
    let actual_inventory:BTreeMap<_,_>=targets.iter().map(|n|{
        let c=loaded.get_const(n).expect("actual constant");
        (n.to_string(),json!({"kind":kind(c),"module":loaded.get_constant_origin(n).and_then(|o|o.module_name()),"is_unsafe":loaded.is_unsafe(n),"is_partial":loaded.is_partial(n),"has_value":c.value.is_some()}))
    }).collect();
    controls::loaded(&expected, &actual_inventory);
    let mut observed = BTreeMap::new();
    for subject in &targets {
        let c = loaded.get_const(subject).expect("actual declaration");
        let label = subject.to_string();
        assert_eq!(kind(c), expected[&label]);
        assert!(!loaded.is_unsafe(subject) && !loaded.is_partial(subject));
        assert!(
            c.value.is_some(),
            "own declaration has its actual stored value"
        );
        let row = &lean_rows[&label];
        assert_eq!(row["module"], ROOT);
        assert_eq!(row["kind"], kind(c));
        let (lean_type, lean_params) = identity::decode(&row["full_statement_identity"]);
        let actual_pin = identity::Identity::default().statement(&c.type_, &c.level_params);
        let lean_pin = identity::Identity::default().statement(&lean_type, &lean_params);
        assert_eq!(
            actual_pin, lean_pin,
            "actual compiled statement equals independent Lean identity for {label}"
        );
        assert_eq!(
            c.level_params, lean_params,
            "exact universe parameter names/order"
        );
        let params: Vec<_> = c.level_params.iter().map(identity::name_json).collect();
        let value = json!({"kind":kind(c),"statement_sha256":actual_pin,"level_params":params});
        eprintln!(
            "binding-not-observed-pin {label} {}",
            identity::canonical(&value)
        );
        observed.insert(label, value);
    }
    // Observations above are untrusted pin-mint diagnostics. A missing pin file
    // still refuses; it never authorizes an acceptance or creates a pin.
    let pins = data::read(&pin_path);
    book.insert(pin_path.clone(), data::file_sha(&pin_path));
    data::check_pins(&observed, &pins).expect("every actual compiled statement/universe pin");
    controls::pin_metadata(&observed, &pins);
    let first = observed
        .keys()
        .next()
        .expect("nonempty observed statements");
    let mut wrong = pins.clone();
    let pin = data::string(&wrong["declarations"][first], "statement_sha256").to_owned();
    wrong["declarations"][first]["statement_sha256"] = json!(format!(
        "{}{}",
        if pin.starts_with('0') { '1' } else { '0' },
        &pin[1..]
    ));
    assert_eq!(
        data::check_pins(&observed, &wrong),
        Err(format!("{first}: statement_sha256 pin mismatch")),
        "actual-data wrong-pin refusal"
    );
    let mut missing = pins.clone();
    missing["declarations"]
        .as_object_mut()
        .expect("pins")
        .remove(first);
    assert_eq!(
        data::check_pins(&observed, &missing),
        Err("statement pin declaration set mismatch".into())
    );

    let mut replay_targets = targets.clone();
    assert!(
        replay_targets.insert(Name::from_string("False")),
        "False is an external negative-control root"
    );
    let checked = reference_base_closed(&loaded, &replay_targets, &ClosedRecheckOptions::default())
        .expect("complete compiled-byte dependency cones");
    assert!(
        checked.report.passed() && checked.entry_refusals.is_empty(),
        "{} {:?}",
        checked.report.verdict_sentence(),
        checked.entry_refusals
    );
    eprintln!("binding-not fenced {}", checked.report.verdict_sentence());
    let mut kernel = checked.into_kernel().expect("complete fenced admissions");
    let allowed: BTreeSet<_> = AX0.map(str::to_owned).into();
    let mut actual_closures = BTreeMap::new();
    for (i, subject) in targets.iter().enumerate() {
        let c = loaded.get_const(subject).expect("compiled constant");
        let actual = closure(subject, kernel.environment());
        assert!(
            actual.is_subset(&allowed),
            "non-Ax0 closure {subject}: {actual:?}"
        );
        assert_eq!(
            actual,
            data::strings(&lean_rows[&subject.to_string()]["axiom_closure"]),
            "fenced/Lean exact axiom census"
        );
        actual_closures.insert(subject.to_string(), json!(actual));
        kernel
            .add_checked(checked_copy(
                c,
                Name::from_string(&format!("BindingNotReviewQualification.positive_{i}")),
            ))
            .unwrap_or_else(|e| panic!("actual value at actual stored type {subject}: {e:?}"));
        let bad = kernel.add_checked(Declaration::Theorem {
            name: Name::from_string(&format!("BindingNotReviewQualification.false_{i}")),
            level_params: c.level_params.clone(),
            type_: Expr::const_(Name::from_string("False"), vec![]),
            value: c.value.clone().expect("actual proof/value"),
        });
        assert!(
            mismatch(&bad),
            "actual {subject} cannot prove False; require precise TypeMismatch: {bad:?}"
        );
    }
    guards::closures(&actual_closures, &closures).expect("all actual own closures exactly pinned");

    let meta = metadata(&lean);
    std::fs::create_dir_all(env!("CARGO_TARGET_TMPDIR")).expect("qualification output parent");
    let out_dir = tempfile::Builder::new()
        .prefix("binding-not-review-")
        .tempdir_in(env!("CARGO_TARGET_TMPDIR"))
        .expect("unique qualification directory")
        .keep();
    eprintln!("binding-not retained-artifacts {}", out_dir.display());
    let export = out_dir.join("BindingNotReview.ndjson");
    let mut command = Command::new(env!("CARGO_BIN_EXE_clean_export_write"));
    command
        .args(["--module", ROOT])
        .arg("--lean-path")
        .arg(&compiled)
        .arg("--lean-path")
        .arg(&lib)
        .args([
            "--lean-version",
            &meta.lean_version,
            "--lean-githash",
            &meta.lean_githash,
        ]);
    for target in &replay_targets {
        command.arg("--target").arg(target.to_string());
    }
    let out = command
        .arg("--out")
        .arg(&export)
        .output()
        .expect("production clean_export_write");
    data::command_ok("binding-not production NDJSON writer", &out);
    let written = data::parse(
        std::str::from_utf8(&out.stdout)
            .expect("writer JSON")
            .trim(),
    );
    assert_eq!(
        written["targets"].as_u64(),
        Some(replay_targets.len() as u64)
    );
    let summary: ExportWriteSummary =
        serde_json::from_value(written["written"].clone()).expect("writer summary");
    let bytes = std::fs::read(&export).expect("actual production export");
    assert!(!export.with_extension("ndjson.partial").exists());
    assert_eq!(summary.sha256, identity::sha(&bytes));
    check_export_round_trip(bytes.as_slice(), &summary)
        .expect("actual production export round trip");
    let mut library_bytes = Vec::new();
    let library_summary = write_export(&loaded, &replay_targets, &meta, &mut library_bytes)
        .expect("same public writer/library cone");
    assert_eq!(library_summary, summary);
    assert_eq!(
        library_bytes, bytes,
        "production caller writes exact in-process compiled targets"
    );
    stock.replay(&export, &summary, &targets);
    let theorems: Vec<_> = targets
        .iter()
        .filter(|n| loaded.get_const(n).expect("target").kind == ConstantKind::Theorem)
        .collect();
    assert!(
        !theorems.is_empty(),
        "at least one actual equality/stored proof"
    );
    for subject in &theorems {
        let name = subject.to_string();
        let pin = data::string(&pins["declarations"][&name], "ck0_statement_sha256");
        stock.target(
            &export,
            &summary,
            &targets,
            subject,
            pin,
            &data::strings(&lean_rows[&name]["axiom_closure"]),
        );
    }
    let first = theorems[0];
    stock.wrong_pin(
        &export,
        first,
        data::string(
            &pins["declarations"][first.to_string()],
            "ck0_statement_sha256",
        ),
    );
    stock.false_statement(&export, &bytes, first);
    stock.unchanged(&repo);
    derived.unchanged();
    for (p, h) in book {
        assert_eq!(
            data::file_sha(&p),
            h,
            "qualification input changed: {}",
            p.display()
        );
    }
    eprintln!("binding-not-qualified own={} theorems={} exact-pins={} actual-value-positive={} actual-False-TypeMismatch={} stock-targets={} stock-wrong-pin=1 stock-False-type-check=1",targets.len(),theorems.len(),observed.len(),targets.len(),targets.len(),theorems.len());
}
