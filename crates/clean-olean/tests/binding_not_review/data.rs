// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Strict runtime receipts: absent files and duplicate JSON keys are refusals.
use serde::de::{self, Deserialize, Deserializer, MapAccess, SeqAccess, Visitor};
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::Path;
use std::process::Output;

use super::identity::sha;

struct Unique(Value);
impl<'de> Deserialize<'de> for Unique {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        struct V;
        impl<'de> Visitor<'de> for V {
            type Value = Unique;
            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("JSON without duplicate object keys")
            }
            fn visit_bool<E: de::Error>(self, v: bool) -> Result<Unique, E> {
                Ok(Unique(json!(v)))
            }
            fn visit_i64<E: de::Error>(self, v: i64) -> Result<Unique, E> {
                Ok(Unique(json!(v)))
            }
            fn visit_u64<E: de::Error>(self, v: u64) -> Result<Unique, E> {
                Ok(Unique(json!(v)))
            }
            fn visit_f64<E: de::Error>(self, _: f64) -> Result<Unique, E> {
                Err(E::custom("floating point is not a receipt field"))
            }
            fn visit_str<E: de::Error>(self, v: &str) -> Result<Unique, E> {
                Ok(Unique(json!(v)))
            }
            fn visit_string<E: de::Error>(self, v: String) -> Result<Unique, E> {
                Ok(Unique(json!(v)))
            }
            fn visit_unit<E: de::Error>(self) -> Result<Unique, E> {
                Ok(Unique(Value::Null))
            }
            fn visit_none<E: de::Error>(self) -> Result<Unique, E> {
                Ok(Unique(Value::Null))
            }
            fn visit_seq<A: SeqAccess<'de>>(self, mut a: A) -> Result<Unique, A::Error> {
                let mut out = Vec::new();
                while let Some(Unique(v)) = a.next_element()? {
                    out.push(v)
                }
                Ok(Unique(json!(out)))
            }
            fn visit_map<A: MapAccess<'de>>(self, mut a: A) -> Result<Unique, A::Error> {
                let mut out = serde_json::Map::new();
                while let Some((k, Unique(v))) = a.next_entry::<String, Unique>()? {
                    if out.insert(k, v).is_some() {
                        return Err(de::Error::custom("duplicate JSON key"));
                    }
                }
                Ok(Unique(Value::Object(out)))
            }
        }
        d.deserialize_any(V)
    }
}

pub(super) fn try_parse(raw: &str) -> Result<Value, String> {
    serde_json::from_str::<Unique>(raw)
        .map(|v| v.0)
        .map_err(|e| e.to_string())
}
pub(super) fn parse(raw: &str) -> Value {
    try_parse(raw).expect("strict receipt JSON")
}
pub(super) fn read(path: &Path) -> Value {
    parse(
        &std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("required receipt {}: {e}", path.display())),
    )
}
pub(super) fn file_sha(path: &Path) -> String {
    sha(&std::fs::read(path).unwrap_or_else(|e| panic!("required input {}: {e}", path.display())))
}
pub(super) fn object(v: &Value) -> &serde_json::Map<String, Value> {
    v.as_object().expect("receipt object")
}
pub(super) fn string<'a>(v: &'a Value, key: &str) -> &'a str {
    v[key]
        .as_str()
        .unwrap_or_else(|| panic!("missing string {key}"))
}
pub(super) fn strings(v: &Value) -> BTreeSet<String> {
    let rows = v.as_array().expect("string array");
    let out: BTreeSet<_> = rows
        .iter()
        .map(|s| s.as_str().expect("string").to_owned())
        .collect();
    assert_eq!(out.len(), rows.len(), "duplicate string array member");
    out
}
pub(super) fn hex(v: &Value) -> bool {
    v.as_str().is_some_and(|s| {
        s.len() == 64
            && s.bytes()
                .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
    })
}

pub(super) fn rows(v: &Value) -> BTreeMap<String, Value> {
    let mut out = BTreeMap::new();
    for row in v.as_array().expect("declaration rows") {
        let name = string(row, "declaration").to_owned();
        assert!(
            out.insert(name, row.clone()).is_none(),
            "duplicate census declaration"
        );
    }
    out
}

pub(super) fn command_ok(label: &str, out: &Output) {
    eprintln!(
        "{label} status={} stdout-sha256={} stderr-sha256={}\n{}\n{}",
        out.status,
        sha(&out.stdout),
        sha(&out.stderr),
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(out.status.success(), "{label} failed");
}

pub(super) fn fresh_census(
    out: &Output,
    manifest: &Value,
    committed: &Value,
) -> BTreeMap<String, Value> {
    command_ok("binding-not fresh Lean census", out);
    let text = String::from_utf8(out.stdout.clone()).expect("census UTF8");
    let mut actual = Vec::new();
    let mut counts = Vec::new();
    let mut bindings = Vec::new();
    for line in text.lines() {
        if let Some((_, s)) = line.split_once("E7_ROW ") {
            actual.push(parse(s));
        }
        if let Some((_, s)) = line.split_once("E7_COUNT ") {
            counts.push(s.trim().parse::<u64>().expect("census count"));
        }
        if let Some((_, s)) = line.split_once("WITNESS_INPUTS ") {
            bindings.push(parse(s));
        }
    }
    super::guards::fresh(manifest, committed, &json!(actual), &counts, &bindings)
        .expect("fresh Lean full statements/kinds/axioms and exact receipt binding");
    rows(&json!(actual))
}

pub(super) fn check_pins(observed: &BTreeMap<String, Value>, pins: &Value) -> Result<(), String> {
    if pins["schema"] != "binding-not-review-pins/v1" {
        return Err("statement pin schema".into());
    }
    if pins["lean_toolchain"] != super::PIN {
        return Err("statement pin Lean toolchain".into());
    }
    let expected = object(&pins["declarations"]);
    if observed.keys().collect::<BTreeSet<_>>() != expected.keys().collect::<BTreeSet<_>>() {
        return Err("statement pin declaration set mismatch".into());
    }
    for (name, got) in observed {
        let pin = &expected[name];
        let keys: BTreeSet<_> = object(pin).keys().map(String::as_str).collect();
        if keys
            != [
                "kind",
                "statement_sha256",
                "level_params",
                "ck0_statement_sha256",
            ]
            .into_iter()
            .collect()
        {
            return Err(format!("{name}: pin row fields"));
        }
        if !hex(&pin["statement_sha256"]) {
            return Err(format!("{name}: malformed statement pin"));
        }
        for key in ["kind", "statement_sha256", "level_params"] {
            if got[key] != pin[key] {
                return Err(format!("{name}: {key} pin mismatch"));
            }
        }
        if got["kind"] == "theorem" {
            if !hex(&pin["ck0_statement_sha256"]) {
                return Err(format!("{name}: missing ck0 theorem pin"));
            }
        } else if !pin["ck0_statement_sha256"].is_null() {
            return Err(format!("{name}: non-theorem ck0 pin"));
        }
    }
    Ok(())
}
