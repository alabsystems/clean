// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Mutate actual current receipts, then call the original positive-path guards.
use super::{data, guards};
use serde_json::{json, Value};
use std::collections::BTreeMap;

pub(super) fn receipts(
    manifest: &Value,
    census: &Value,
    closures: &Value,
    lean_sha: &str,
    census_sha: &str,
) {
    guards::headers(manifest, census, closures).expect("receipt headers");
    guards::sources(manifest, lean_sha, census_sha).expect("actual producer source bindings");
    let expected = guards::inventory(manifest).expect("actual inventory");
    let first = expected.keys().next().expect("own rows");
    let mut m = manifest.clone();
    m["schema"] = json!("forged-schema");
    assert_eq!(
        guards::headers(&m, census, closures),
        Err("manifest schema")
    );
    let mut m = manifest.clone();
    m["control"]["mode"] = json!("false-theorem");
    assert_eq!(
        guards::headers(&m, census, closures),
        Err("manifest is a negative producer")
    );
    let mut c = census.clone();
    c["schema"] = json!("forged-schema");
    assert_eq!(
        guards::headers(manifest, &c, closures),
        Err("census identity")
    );
    let mut c = census.clone();
    c["modules"] = json!([]);
    assert_eq!(
        guards::headers(manifest, &c, closures),
        Err("census identity")
    );
    let mut p = closures.clone();
    p["schema"] = json!("forged-schema");
    assert_eq!(guards::headers(manifest, census, &p), Err("closure schema"));
    let mut m = manifest.clone();
    m["lean_toolchain"] = json!("leanprover/lean4:wrong");
    assert_eq!(
        guards::headers(&m, census, closures),
        Err("Lean toolchain pin")
    );
    let mut m = manifest.clone();
    m["own_origin_modules"] = json!([]);
    assert_eq!(
        guards::headers(&m, census, closures),
        Err("manifest module identity")
    );
    let mut m = manifest.clone();
    m["declarations"]
        .as_array_mut()
        .expect("manifest rows")
        .push(manifest["declarations"][0].clone());
    assert_eq!(guards::inventory(&m), Err("duplicate manifest declaration"));
    let mut m = manifest.clone();
    m["declarations"][0]["kind"] = json!("axiom");
    assert_eq!(guards::inventory(&m), Err("own axiom/unsupported kind"));
    let mut m = manifest.clone();
    m["declarations"].as_array_mut().expect("rows").pop();
    assert_eq!(guards::inventory(&m), Err("manifest count"));
    let mut m = manifest.clone();
    m["lean_source_sha256"] = json!("0");
    assert_eq!(
        guards::sources(&m, lean_sha, census_sha),
        Err("logical source binding")
    );
    let mut m = manifest.clone();
    m["census_source_sha256"] = json!("0");
    assert_eq!(
        guards::sources(&m, lean_sha, census_sha),
        Err("census source binding")
    );
    let rows = &census["declarations"];
    let count = manifest["expected_E7_COUNT"].as_u64().expect("count");
    let binding = vec![manifest["census_input_binding"].clone()];
    guards::fresh(manifest, census, rows, &[count], &binding).expect("current census guard");
    assert_eq!(
        guards::fresh(manifest, census, rows, &[count], &[]),
        Err("fresh census input binding")
    );
    assert_eq!(
        guards::fresh(manifest, census, rows, &[], &binding),
        Err("fresh census count")
    );
    let mut c = census.clone();
    c["decl_count"] = json!(count + 1);
    assert_eq!(
        guards::fresh(manifest, &c, rows, &[count], &binding),
        Err("committed census count")
    );
    let mut c = census.clone();
    c["declarations"]
        .as_array_mut()
        .expect("rows")
        .push(rows[0].clone());
    assert_eq!(
        guards::fresh(manifest, &c, &c["declarations"], &[count], &binding),
        Err("duplicate census declaration")
    );
    let mut c = census.clone();
    c["declarations"].as_array_mut().expect("rows").pop();
    assert_eq!(
        guards::fresh(manifest, census, &c["declarations"], &[count], &binding),
        Err("fresh census count")
    );
    let mut c = census.clone();
    c["declarations"][0]["full_statement_identity"] = json!({"forged":true});
    assert_eq!(
        guards::fresh(manifest, &c, rows, &[count], &binding),
        Err("fresh/committed census mismatch")
    );
    let mut p = closures.clone();
    p["declarations"]
        .as_object_mut()
        .expect("closures")
        .remove(first);
    let actual: BTreeMap<_, _> = data::object(&closures["declarations"])
        .iter()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    guards::closures(&actual, closures).expect("frozen closure guard");
    assert_eq!(
        guards::closures(&actual, &p),
        Err("closure declaration set")
    );
    let mut p = closures.clone();
    p["declarations"][first] = json!(["propext", "propext"]);
    assert_eq!(
        guards::closures(&actual, &p),
        Err("duplicate closure axiom")
    );
    let mut p = closures.clone();
    p["declarations"][first] = json!(["BindingNotReviewForgedAxiom"]);
    assert_eq!(guards::closures(&actual, &p), Err("closure outside Ax0"));
    let mut p = closures.clone();
    let mut axioms = data::strings(&p["declarations"][first]);
    if !axioms.remove("propext") {
        axioms.insert("propext".into());
    }
    p["declarations"][first] = json!(axioms);
    assert_eq!(guards::closures(&actual, &p), Err("exact closure mismatch"));
}

pub(super) fn loaded(expected: &BTreeMap<String, String>, actual: &BTreeMap<String, Value>) {
    guards::loaded(expected, actual).expect("exact compiled origins/kinds/safety");
    let first = actual.keys().next().expect("actual compiled rows");
    let mut bad = actual.clone();
    bad.remove(first);
    assert_eq!(
        guards::loaded(expected, &bad),
        Err("compiled declaration set")
    );
    for (field, value, reason) in [
        ("module", json!("ForeignModule"), "compiled module origin"),
        ("kind", json!("axiom"), "compiled declaration kind"),
        (
            "is_unsafe",
            json!(true),
            "unsafe/partial compiled declaration",
        ),
        (
            "is_partial",
            json!(true),
            "unsafe/partial compiled declaration",
        ),
        ("has_value", json!(false), "missing actual stored value"),
    ] {
        let mut bad = actual.clone();
        bad.get_mut(first).expect("actual row")[field] = value;
        assert_eq!(guards::loaded(expected, &bad), Err(reason));
    }
}

pub(super) fn pin_metadata(actual: &BTreeMap<String, Value>, pins: &Value) {
    data::check_pins(actual, pins).expect("actual pin rows and metadata");
    let first = actual.keys().next().expect("pins");
    let mut p = pins.clone();
    p["schema"] = json!("forged-schema");
    assert_eq!(
        data::check_pins(actual, &p),
        Err("statement pin schema".into())
    );
    let mut p = pins.clone();
    p["lean_toolchain"] = json!("forged-toolchain");
    assert_eq!(
        data::check_pins(actual, &p),
        Err("statement pin Lean toolchain".into())
    );
    let mut p = pins.clone();
    p["declarations"][first]
        .as_object_mut()
        .expect("pin")
        .remove("kind");
    assert_eq!(
        data::check_pins(actual, &p),
        Err(format!("{first}: pin row fields"))
    );
    let mut p = pins.clone();
    p["declarations"][first]["level_params"] = Value::Null;
    assert_eq!(
        data::check_pins(actual, &p),
        Err(format!("{first}: level_params pin mismatch"))
    );
    let theorem = actual
        .iter()
        .find(|(_, v)| v["kind"] == "theorem")
        .expect("actual theorem pin")
        .0;
    let mut p = pins.clone();
    p["declarations"][theorem]["ck0_statement_sha256"] = Value::Null;
    assert_eq!(
        data::check_pins(actual, &p),
        Err(format!("{theorem}: missing ck0 theorem pin"))
    );
    let raw = serde_json::to_string(pins).expect("actual pin JSON");
    let duplicate = format!("{{\"schema\":{},{}", pins["schema"], &raw[1..]);
    assert!(data::try_parse(&duplicate)
        .expect_err("actual duplicate schema key")
        .contains("duplicate JSON key"));
}
