// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Check a complete exact axiom roster against a pinned Lean executable.

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::path::Path;
use std::process::Command;

fn parse(
    output: &str,
    subjects: &BTreeSet<&str>,
) -> Result<BTreeMap<String, BTreeSet<String>>, String> {
    let mut records = Vec::new();
    let mut pending = String::new();
    for line in output.lines().filter(|line| !line.trim().is_empty()) {
        if pending.is_empty() {
            if !line.starts_with('\'') {
                return Err(format!("unrecognized Lean axiom census line: {line}"));
            }
        } else {
            if !line.starts_with(char::is_whitespace) {
                return Err(format!("unfinished Lean axiom census row: {pending}"));
            }
            pending.push(' ');
        }
        pending.push_str(line.trim());
        if pending.ends_with(']') || pending.ends_with("does not depend on any axioms") {
            records.push(std::mem::take(&mut pending));
        } else if !pending.contains("depends on axioms: [") || pending.contains(']') {
            return Err(format!("unrecognized Lean axiom census row: {pending}"));
        }
    }
    if !pending.is_empty() {
        return Err(format!("unfinished Lean axiom census row: {pending}"));
    }
    let mut rows = BTreeMap::new();
    for line in &records {
        let (name, tail) = line
            .strip_prefix('\'')
            .and_then(|line| line.split_once("' "))
            .ok_or_else(|| format!("unrecognized Lean axiom census line: {line}"))?;
        if !subjects.contains(name) {
            return Err(format!("unexpected Lean axiom census subject: {name}"));
        }
        let mut axioms = BTreeSet::new();
        if tail != "does not depend on any axioms" {
            let list = tail
                .strip_prefix("depends on axioms: [")
                .and_then(|tail| tail.strip_suffix(']'))
                .ok_or_else(|| format!("unrecognized Lean axiom census line: {line}"))?;
            for axiom in list.split(',').map(str::trim) {
                if axiom.is_empty() || !axioms.insert(axiom.to_owned()) {
                    return Err(format!("empty or duplicate axiom for {name}: {line}"));
                }
            }
        }
        if rows.insert(name.to_owned(), axioms).is_some() {
            return Err(format!("duplicate Lean axiom census subject: {name}"));
        }
    }
    let missing: Vec<_> = subjects
        .iter()
        .filter(|subject| !rows.contains_key(**subject))
        .copied()
        .collect();
    if !missing.is_empty() {
        return Err(format!("missing Lean axiom census subjects: {missing:?}"));
    }
    Ok(rows)
}

/// Fail before an expensive replay if any exact oracle expectation is stale.
pub(super) fn check(lean: &Path, dir: &Path, root: &str, expected: &[(&str, &[&str])]) {
    let subjects: BTreeSet<_> = expected.iter().map(|(name, _)| *name).collect();
    assert!(!subjects.is_empty(), "empty expected axiom roster");
    assert_eq!(
        subjects.len(),
        expected.len(),
        "duplicate expected axiom subject"
    );
    let mut source = format!("import {root}\n");
    for subject in &subjects {
        source.push_str(&format!("#print axioms {subject}\n"));
    }
    let scratch = Path::new(env!("CARGO_TARGET_TMPDIR"));
    std::fs::create_dir_all(scratch).expect("create Lean census scratch");
    let mut query = tempfile::Builder::new()
        .prefix("lean-axiom-census-")
        .suffix(".lean")
        .tempfile_in(scratch)
        .expect("create Lean census source");
    query
        .write_all(source.as_bytes())
        .expect("write Lean axiom census");
    query.flush().expect("flush Lean axiom census source");
    let output = Command::new(lean)
        .arg(query.path())
        .current_dir(dir)
        .env("LEAN_PATH", dir)
        .output()
        .expect("run and reap pinned Lean axiom census");
    assert!(
        output.status.success(),
        "pinned Lean axiom census failed: {}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = std::str::from_utf8(&output.stdout).expect("Lean census UTF-8");
    let rows = parse(stdout, &subjects).expect("complete Lean axiom census");
    let mut mismatches = Vec::new();
    for (name, axioms) in expected {
        let want: BTreeSet<String> = axioms.iter().map(|axiom| (*axiom).to_owned()).collect();
        if rows[*name] != want {
            mismatches.push(format!("{name}: Lean {:?}, table {want:?}", rows[*name]));
        }
    }
    assert!(
        mismatches.is_empty(),
        "{} stale pinned-Lean axiom expectation(s):\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
    eprintln!(
        "pinned Lean axiom census: {} exact subjects matched",
        expected.len()
    );
}

#[test]
fn parser_refuses_incomplete_or_ambiguous_output() {
    let subjects = BTreeSet::from(["one", "two"]);
    let complete = "'one' depends on axioms: [propext]\n\
                    'two' does not depend on any axioms\n";
    let rows = parse(complete, &subjects).expect("complete census");
    assert_eq!(rows["one"], BTreeSet::from(["propext".to_owned()]));
    assert!(rows["two"].is_empty());
    let wrapped = complete.replace("[propext]", "[propext,\n  Classical.choice, Quot.sound]");
    assert_eq!(
        parse(&wrapped, &subjects).expect("wrapped census")["one"],
        BTreeSet::from([
            "propext".to_owned(),
            "Classical.choice".to_owned(),
            "Quot.sound".to_owned()
        ])
    );
    assert!(parse("", &subjects).is_err());
    assert!(parse("'one' depends on axioms: [propext]\n", &subjects).is_err());
    assert!(parse(&format!("{complete}{complete}"), &subjects).is_err());
    assert!(parse(&complete.replace("'two'", "'other'"), &subjects).is_err());
    assert!(parse(&complete.replace("[propext]", "[]"), &subjects).is_err());
    assert!(parse(
        &complete.replace("[propext]", "[propext, propext]"),
        &subjects
    )
    .is_err());
    assert!(parse(&format!("warning: incomplete\n{complete}"), &subjects).is_err());
    assert!(parse("'one' depends on axioms: [propext,\n", &subjects).is_err());
    assert!(parse(
        "'one' depends on axioms: [propext,\n'other' does not depend on any axioms",
        &subjects
    )
    .is_err());
}
