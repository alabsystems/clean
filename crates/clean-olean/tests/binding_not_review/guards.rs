// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! The positive-path receipt guards, also exercised on real-data mutations.
use super::{AX0, PIN, ROOT};
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};
type Guard<T = ()> = Result<T, &'static str>;

pub(super) fn headers(manifest: &Value, census: &Value, closures: &Value) -> Guard {
    if manifest["schema"] != "mixed-world-not-lean-witnesses/v2" {
        return Err("manifest schema");
    }
    if manifest["lean_toolchain"] != PIN || census["lean_toolchain"] != PIN {
        return Err("Lean toolchain pin");
    }
    if manifest["logical_module"] != ROOT || manifest["own_origin_modules"] != json!([ROOT]) {
        return Err("manifest module identity");
    }
    if manifest["control"]["mode"] != "none" || manifest["control"]["expected_compile"] != "pass" {
        return Err("manifest is a negative producer");
    }
    if census["schema"] != "binding-not-review-census/v1" || census["modules"] != json!([ROOT]) {
        return Err("census identity");
    }
    if closures["schema"] != "binding-not-review-closures/v1" {
        return Err("closure schema");
    }
    Ok(())
}
pub(super) fn sources(manifest: &Value, lean: &str, census: &str) -> Guard {
    if manifest["lean_source_sha256"] != lean {
        return Err("logical source binding");
    }
    if manifest["census_source_sha256"] != census {
        return Err("census source binding");
    }
    Ok(())
}
pub(super) fn inventory(manifest: &Value) -> Guard<BTreeMap<String, String>> {
    let rows = manifest["declarations"]
        .as_array()
        .ok_or("manifest declarations")?;
    let mut result = BTreeMap::new();
    for row in rows {
        let name = row["name"].as_str().ok_or("manifest declaration name")?;
        let kind = row["kind"].as_str().ok_or("manifest declaration kind")?;
        if !["theorem", "definition", "opaque"].contains(&kind) {
            return Err("own axiom/unsupported kind");
        }
        if result.insert(name.to_owned(), kind.to_owned()).is_some() {
            return Err("duplicate manifest declaration");
        }
    }
    if result.is_empty() || manifest["expected_E7_COUNT"].as_u64() != Some(result.len() as u64) {
        return Err("manifest count");
    }
    Ok(result)
}
pub(super) fn loaded(
    expected: &BTreeMap<String, String>,
    actual: &BTreeMap<String, Value>,
) -> Guard {
    if expected.keys().collect::<BTreeSet<_>>() != actual.keys().collect() {
        return Err("compiled declaration set");
    }
    for (name, kind) in expected {
        let row = &actual[name];
        if row["module"] != ROOT {
            return Err("compiled module origin");
        }
        if row["kind"] != *kind {
            return Err("compiled declaration kind");
        }
        if row["is_unsafe"] != false || row["is_partial"] != false {
            return Err("unsafe/partial compiled declaration");
        }
        if row["has_value"] != true {
            return Err("missing actual stored value");
        }
    }
    Ok(())
}
pub(super) fn fresh(
    manifest: &Value,
    committed: &Value,
    actual: &Value,
    counts: &[u64],
    bindings: &[Value],
) -> Guard {
    if bindings.len() != 1 || bindings[0] != manifest["census_input_binding"] {
        return Err("fresh census input binding");
    }
    if counts.len() != 1 || Some(counts[0]) != manifest["expected_E7_COUNT"].as_u64() {
        return Err("fresh census count");
    }
    if committed["decl_count"] != json!(counts[0]) {
        return Err("committed census count");
    }
    let to_map = |rows: &Value| -> Guard<BTreeMap<String, Value>> {
        let mut out = BTreeMap::new();
        for row in rows.as_array().ok_or("census rows")? {
            let name = row["declaration"]
                .as_str()
                .ok_or("census declaration")?
                .to_owned();
            if out.insert(name, row.clone()).is_some() {
                return Err("duplicate census declaration");
            }
        }
        Ok(out)
    };
    let actual = to_map(actual)?;
    if actual.len() as u64 != counts[0] {
        return Err("fresh census count");
    }
    if actual != to_map(&committed["declarations"])? {
        return Err("fresh/committed census mismatch");
    }
    let expected = inventory(manifest)?;
    if actual.keys().collect::<BTreeSet<_>>() != expected.keys().collect() {
        return Err("census declaration set");
    }
    for (name, kind) in expected {
        if actual[&name]["module"] != ROOT || actual[&name]["kind"] != kind {
            return Err("census declaration identity");
        }
    }
    Ok(())
}
pub(super) fn closures(actual: &BTreeMap<String, Value>, pins: &Value) -> Guard {
    let expected = pins["declarations"]
        .as_object()
        .ok_or("closure declaration table")?;
    if actual.keys().collect::<BTreeSet<_>>() != expected.keys().collect() {
        return Err("closure declaration set");
    }
    for (name, observed) in actual {
        let rows = expected[name].as_array().ok_or("closure array")?;
        let mut names = BTreeSet::new();
        for row in rows {
            let name = row.as_str().ok_or("closure name")?;
            if !names.insert(name) {
                return Err("duplicate closure axiom");
            }
            if !AX0.contains(&name) {
                return Err("closure outside Ax0");
            }
        }
        let got: BTreeSet<_> = observed
            .as_array()
            .ok_or("actual closure array")?
            .iter()
            .map(|s| s.as_str().ok_or("actual closure name"))
            .collect::<Result<_, _>>()?;
        if names != got {
            return Err("exact closure mismatch");
        }
    }
    Ok(())
}
