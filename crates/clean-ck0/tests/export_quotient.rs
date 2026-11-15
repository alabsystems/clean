//! Canonical primitive signatures and deliberately forged contexts, through bytes.
use clean_ck0::export::{replay, Dialect, Report};
use serde_json::Value;
const SOURCE: &str = include_str!("fixtures/q2-part2/quotient.ndjson");
fn run(s: &str) -> Report {
    replay(s.as_bytes(), Dialect::Lean4Export31).expect("wire syntax")
}
fn rows() -> Vec<Value> {
    SOURCE
        .lines()
        .map(|l| serde_json::from_str(l).unwrap())
        .collect()
}
fn serialize(rows: &[Value]) -> String {
    rows.iter().map(|v| format!("{v}\n")).collect()
}
fn refused(r: &Report, name: &str, detail: &str) {
    let e = r
        .rows
        .iter()
        .find(|r| r.name.to_string() == name)
        .unwrap()
        .verdict
        .as_ref()
        .unwrap_err();
    assert_eq!(e.reason(), "primitive-admission");
    assert!(e.to_string().contains(detail), "{name}: {e}");
}
#[test]
fn pinned_quotient_primitives_and_lift_iota_accept() {
    let r = run(SOURCE);
    assert_eq!(r.counts().0, 29, "{r:?}");
    assert!(r.counts().1.is_empty());
}
#[test]
fn every_primitive_signature_is_compared() {
    for (kind, name) in [
        ("type", "Quot"),
        ("ctor", "Quot.mk"),
        ("lift", "Quot.lift"),
        ("ind", "Quot.ind"),
    ] {
        let mut rs = rows();
        let prop = rs
            .iter()
            .find(|r| r.get("sort") == Some(&Value::from(0)))
            .unwrap()["ie"]
            .clone();
        let row = rs
            .iter_mut()
            .find_map(|r| r.get_mut("quot").filter(|q| q["kind"] == kind))
            .unwrap();
        row["type"] = prop;
        refused(&run(&serialize(&rs)), name, "quotient type");
    }
}
#[test]
fn primitive_names_and_universe_headers_grant_no_authority() {
    let mut rs = rows();
    let name = rs
        .iter()
        .filter_map(|r| r.get("in")?.as_u64())
        .max()
        .unwrap()
        + 1;
    let pos = rs.iter().position(|r| r.get("quot").is_some()).unwrap();
    rs[pos]["quot"]["name"] = Value::from(name);
    rs.insert(
        pos,
        serde_json::json!({"in":name,"str":{"pre":0,"str":"FakeQuot"}}),
    );
    refused(&run(&serialize(&rs)), "FakeQuot", "quotient identity");
    let mut rs = rows();
    let q = rs
        .iter_mut()
        .find_map(|r| r.get_mut("quot").filter(|q| q["kind"] == "lift"))
        .unwrap();
    q["levelParams"] = serde_json::json!([]);
    refused(
        &run(&serialize(&rs)),
        "Quot.lift",
        "quotient universe signature",
    );
}
#[test]
fn well_typed_noncanonical_eq_cannot_license_quotient_lift() {
    // All table references remain in producer order; only declaration order
    // changes, putting an independently checked alternative Eq first. Its
    // complete header and RHS are consistent, not an incidental duplicate.
    let mut rs = rows();
    let fake = rs
        .iter()
        .find(|r| {
            r.get("str")
                .is_some_and(|s| s["pre"] == 0 && s["str"] == "Q2FakeEq")
        })
        .unwrap()["in"]
        .clone();
    let real = rs
        .iter()
        .find(|r| {
            r.get("str")
                .is_some_and(|s| s["pre"] == 0 && s["str"] == "Eq")
        })
        .unwrap()["in"]
        .clone();
    let fake_block = rs
        .iter()
        .find(|r| {
            r.get("inductive")
                .is_some_and(|b| b["types"][0]["name"] == fake)
        })
        .unwrap()
        .clone();
    for r in &mut rs {
        if r.get("in") == Some(&fake) {
            r["str"]["str"] = Value::from("Eq");
        }
    }
    let mut forged: Vec<Value> = rs
        .iter()
        .filter(|r| {
            r.get("meta").is_some()
                || r.get("in").is_some()
                || r.get("il").is_some()
                || r.get("ie").is_some()
        })
        .cloned()
        .collect();
    forged.push(fake_block);
    forged.extend(rs.into_iter().filter(|r| {
        if r.get("meta").is_some()
            || r.get("in").is_some()
            || r.get("il").is_some()
            || r.get("ie").is_some()
        {
            return false;
        }
        !r.get("inductive")
            .is_some_and(|b| b["types"][0]["name"] == fake || b["types"][0]["name"] == real)
    }));
    let r = run(&serialize(&forged));
    for name in ["Eq", "Eq.refl", "Eq.rec"] {
        assert!(
            r.rows
                .iter()
                .find(|r| r.name.to_string() == name)
                .unwrap()
                .verdict
                .is_ok(),
            "{r:?}"
        );
    }
    refused(&r, "Quot.lift", "requires canonical Eq");
}
