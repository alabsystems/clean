//! Pinned original nested exports, computation proofs, and corrupted advice.
use clean_ck0::export::{replay, Dialect, Report};
use serde_json::Value;
const SOURCE: &str = include_str!("fixtures/q2-part2/nested.ndjson");
fn run(s: &str) -> Report {
    replay(s.as_bytes(), Dialect::Lean4Export31).expect("wire syntax")
}
fn rows() -> Vec<Value> {
    SOURCE
        .lines()
        .map(|l| serde_json::from_str(l).unwrap())
        .collect()
}
fn serialize(rows: Vec<Value>) -> String {
    rows.iter().map(|v| format!("{v}\n")).collect()
}
fn first_nested(rows: &mut [Value]) -> &mut Value {
    rows.iter_mut()
        .find_map(|r| {
            r.get_mut("inductive")
                .filter(|b| b["types"][0]["numNested"] == 1)
        })
        .unwrap()
}
fn refused(r: &Report, n: &str, why: &str) {
    let e = r
        .rows
        .iter()
        .find(|r| r.name.to_string() == n)
        .unwrap()
        .verdict
        .as_ref()
        .unwrap_err();
    assert!(e.to_string().contains(why), "{n}: {e}");
}
#[test]
fn pinned_nested_families_and_real_iota_proofs_accept() {
    let r = run(SOURCE);
    assert_eq!(r.counts().0, 50, "{r:?}");
    assert!(r.counts().1.is_empty());
    for n in [
        "q2ListNestedIota",
        "q2ArrayNestedIota",
        "q2FunctionNestedIota",
    ] {
        assert!(r
            .rows
            .iter()
            .find(|r| r.name.to_string() == n)
            .unwrap()
            .verdict
            .is_ok());
    }
}
#[test]
fn producer_cannot_hide_or_invent_nested_auxiliaries() {
    for (count, why) in [(0, "nested metadata"), (2, "nested auxiliary count")] {
        let mut rs = rows();
        first_nested(&mut rs)["types"][0]["numNested"] = Value::from(count);
        refused(&run(&serialize(rs)), "Q2Rose", why);
    }
}
#[test]
fn nested_auxiliary_rules_and_motives_are_compared() {
    let mut rs = rows();
    first_nested(&mut rs)["recs"][0]["numMotives"] = Value::from(1);
    refused(&run(&serialize(rs)), "Q2Rose", "recursor numMotives");
    let mut rs = rows();
    let b = first_nested(&mut rs);
    let rhs = b["recs"][0]["rules"][0]["rhs"].clone();
    b["recs"][1]["rules"][0]["rhs"] = rhs;
    refused(&run(&serialize(rs)), "Q2Rose", "recursor rule RHS mismatch");
}
#[test]
fn negative_nesting_reaches_the_positivity_refusal() {
    let mut rs = rows();
    let pos = rs
        .iter()
        .position(|r| {
            r.get("inductive")
                .is_some_and(|b| b["types"][0]["numNested"] == 1)
        })
        .unwrap();
    let ty = rs[pos]["inductive"]["ctors"][0]["type"].as_u64().unwrap();
    let expr = |i: u64| {
        rs.iter()
            .find(|r| r.get("ie") == Some(&Value::from(i)))
            .unwrap()
            .clone()
    };
    let mut top = expr(ty);
    let mut value = expr(top["forallE"]["body"].as_u64().unwrap());
    let mut children = expr(value["forallE"]["body"].as_u64().unwrap());
    let list = expr(children["forallE"]["type"].as_u64().unwrap());
    let element = list["app"]["arg"].clone();
    let id = rs
        .iter()
        .filter_map(|r| r.get("ie")?.as_u64())
        .max()
        .unwrap()
        + 1;
    let prop = serde_json::json!({"ie":id,"sort":0});
    let negative = serde_json::json!({"ie":id+1,"forallE":{"name":0,"binderInfo":"default","type":element,"body":id}});
    let mut field = list;
    field["ie"] = Value::from(id + 2);
    field["app"]["arg"] = Value::from(id + 1);
    children["ie"] = Value::from(id + 3);
    children["forallE"]["type"] = Value::from(id + 2);
    value["ie"] = Value::from(id + 4);
    value["forallE"]["body"] = Value::from(id + 3);
    top["ie"] = Value::from(id + 5);
    top["forallE"]["body"] = Value::from(id + 4);
    rs[pos]["inductive"]["ctors"][0]["type"] = Value::from(id + 5);
    rs.splice(pos..pos, [prop, negative, field, children, value, top]);
    refused(
        &run(&serialize(rs)),
        "Q2Rose",
        "non-strictly-positive nesting",
    );
}
#[test]
fn original_inductives_named_below_are_not_primitive_recursors() {
    let r = run(include_str!("fixtures/q2-part2/auxiliary-names.ndjson"));
    assert!(r.counts().1.is_empty(), "{r:?}");
    assert!(r
        .rows
        .iter()
        .find(|r| r.name.to_string() == "Nat.le.below")
        .unwrap()
        .verdict
        .is_ok());
}

#[test]
fn private_lowering_types_cannot_be_referenced_by_wire_names() {
    let mut rs = rows();
    let block = rs
        .iter()
        .find_map(|r| {
            r.get("inductive")
                .filter(|b| b["types"][0]["numNested"] == 1)
        })
        .unwrap();
    let parent = block["types"][0]["name"].clone();
    let params = block["types"][0]["levelParams"].clone();
    let ty = block["types"][0]["type"].clone();
    let param = params[0].clone();
    let level = rs.iter().find(|r| r.get("param") == Some(&param)).unwrap()["il"].clone();
    let name = rs
        .iter()
        .filter_map(|r| r.get("in")?.as_u64())
        .max()
        .unwrap()
        + 1;
    let expr = rs
        .iter()
        .filter_map(|r| r.get("ie")?.as_u64())
        .max()
        .unwrap()
        + 1;
    rs.extend([
        serde_json::json!({"in":name,"str":{"pre":parent,"str":"_List"}}),
        serde_json::json!({"in":name+1,"str":{"pre":0,"str":"q2_private_leak"}}),
        serde_json::json!({"ie":expr,"const":{"name":name,"us":[level]}}),
        serde_json::json!({"def":{"name":name+1,"levelParams":params,"type":ty,"value":expr,"hints":"abbrev","safety":"safe","all":[]}}),
    ]);
    refused(
        &run(&serialize(rs)),
        "q2_private_leak",
        "private lowering name in export",
    );
}

#[test]
fn native_folds_cannot_bootstrap_from_constructor_syntax() {
    let r = run(include_str!(
        "fixtures/q2-part2/native-constructor-spoof.ndjson"
    ));
    refused(&r, "q2_spoofed_native", "type-check");
}
