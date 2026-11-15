//! Pinned mutual-original, indexed-container and private nested export controls.
use clean_ck0::export::{replay, Dialect, Report};
use serde_json::Value;
const SOURCE: &str = include_str!("fixtures/q2-part2/mutual-nested.ndjson");
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
fn mutual_nested(rows: &mut [Value]) -> &mut Value {
    rows.iter_mut()
        .find_map(|r| {
            r.get_mut("inductive").filter(|b| {
                b["types"].as_array().unwrap().len() == 2 && b["types"][0]["numNested"] == 1
            })
        })
        .unwrap()
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
    assert!(e.to_string().contains(detail), "{name}: {e}");
}
#[test]
fn pinned_general_nested_exports_and_computation_proofs_accept() {
    let r = run(SOURCE);
    assert!(r.counts().1.is_empty(), "{r:?}");
    for name in [
        "q2MutualNestedIota",
        "q2IndexedNestedIota",
        "q2PrivateNestedIota",
        "Q2UsesContainerB.rec",
    ] {
        assert!(r
            .rows
            .iter()
            .find(|r| r.name.to_string() == name)
            .unwrap()
            .verdict
            .is_ok());
    }
}
#[test]
fn zero_nested_counts_cannot_hide_occurrences_in_any_mutual_member() {
    let mut rs = rows();
    let block = mutual_nested(&mut rs);
    for ty in block["types"].as_array_mut().unwrap() {
        ty["numNested"] = Value::from(0);
    }
    let r = run(&serialize(&rs));
    for name in ["Q2MutualTree", "Q2MutualForest", "Q2MutualTree.rec_1"] {
        refused(&r, name, "nested metadata");
    }
}
#[test]
fn mutual_nested_counts_and_auxiliary_rules_are_checked() {
    let mut rs = rows();
    mutual_nested(&mut rs)["types"][1]["numNested"] = Value::from(2);
    refused(&run(&serialize(&rs)), "Q2MutualTree", "mutual nested count");
    let mut rs = rows();
    let block = mutual_nested(&mut rs);
    block["recs"][2]["rules"][0]["rhs"] = block["recs"][0]["rules"][0]["rhs"].clone();
    refused(
        &run(&serialize(&rs)),
        "Q2MutualTree.rec_1",
        "recursor rule RHS mismatch",
    );
}
#[test]
fn indexed_auxiliary_recursor_indices_are_not_producer_authority() {
    let mut rs = rows();
    let block = rs
        .iter_mut()
        .find_map(|r| {
            r.get_mut("inductive").filter(|b| {
                b["types"].as_array().unwrap().len() == 1
                    && b["types"][0]["numNested"] == 1
                    && b["recs"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .any(|r| r["numIndices"] == 1)
            })
        })
        .unwrap();
    let rec = block["recs"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|r| r["numIndices"] == 1)
        .unwrap();
    rec["numIndices"] = Value::from(0);
    refused(
        &run(&serialize(&rs)),
        "Q2IndexedTree",
        "recursor numIndices",
    );
}
