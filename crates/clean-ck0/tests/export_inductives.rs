//! Pinned Lean bytes and semantic mutations of those bytes, through replay.
use clean_ck0::export::{replay, Dialect, Report};
use serde_json::Value;
const SEED: &str = include_str!("../../../reports/self-proof-q2-2026-11-12/seed.ndjson");
fn run(s: &str) -> Report {
    replay(s.as_bytes(), Dialect::Lean4Export31).expect("wire syntax")
}
fn mutate(f: impl FnOnce(&mut Value)) -> String {
    let mut rows: Vec<Value> = SEED
        .lines()
        .map(|l| serde_json::from_str(l).unwrap())
        .collect();
    f(rows
        .iter_mut()
        .find(|r| r.get("inductive").is_some())
        .unwrap()
        .get_mut("inductive")
        .unwrap());
    rows.iter().map(|v| format!("{v}\n")).collect()
}
fn refused(report: &Report, name: &str, detail: &str) {
    let row = report
        .rows
        .iter()
        .find(|r| r.name.to_string() == name)
        .expect("named row");
    let error = row.verdict.as_ref().expect_err("negative must refuse");
    assert!(
        error.to_string().contains(detail),
        "{name}: {error}; wanted {detail}"
    );
}
#[test]
fn pinned_seed_accepts_all_22_including_k_eta_iota_and_polymorphism() {
    let r = run(SEED);
    assert_eq!(r.rows.len(), 22);
    assert_eq!(r.counts().0, 22, "{r:?}");
    assert!(r.axioms.is_empty());
}
#[test]
fn every_recursor_header_and_rule_is_compared_before_block_commit() {
    for key in ["numParams", "numIndices", "numMotives", "numMinors"] {
        let s = mutate(|b| b["recs"][0][key] = Value::from(99));
        let r = run(&s);
        for n in ["Nat", "Nat.zero", "Nat.succ", "Nat.rec"] {
            refused(&r, n, &format!("recursor {key}"));
        }
        refused(&r, "q2Eq", "unknown-constant: Nat");
    }
    for (key, value, reason) in [
        ("k", Value::Bool(true), "recursor K flag"),
        ("type", Value::from(0), "recursor type mismatch"),
    ] {
        let r = run(&mutate(|b| b["recs"][0][key] = value));
        refused(&r, "Nat.rec", reason);
    }
    let r = run(&mutate(|b| {
        b["recs"][0]["rules"][0]["rhs"] = b["recs"][0]["rules"][1]["rhs"].clone();
    }));
    refused(&r, "Nat.rec", "recursor rule RHS mismatch");
    let r = run(&mutate(|b| {
        b["recs"][0]["rules"][0]["nfields"] = Value::from(1)
    }));
    refused(&r, "Nat.rec", "recursor rule constructor/fields");
}
#[test]
fn constructor_metadata_and_universe_arity_are_checked() {
    for (key, value, reason) in [
        ("numFields", Value::from(3), "constructor numFields"),
        (
            "numParams",
            Value::from(1),
            "constructor identity/parameters/order",
        ),
        (
            "cidx",
            Value::from(2),
            "constructor identity/parameters/order",
        ),
        (
            "levelParams",
            serde_json::json!([6]),
            "constructor identity/parameters/order",
        ),
    ] {
        let r = run(&mutate(|b| b["ctors"][0][key] = value));
        refused(&r, "Nat", reason);
    }
    let r = run(&mutate(|b| {
        b["recs"][0]["levelParams"] = serde_json::json!([])
    }));
    refused(&r, "Nat.rec", "recursor universe parameters");
}
#[test]
fn repository_forged_recursor_and_ill_typed_body_fail_semantically() {
    // Copied unchanged from Q3's mint of the repository's GenReplayForged
    // families, pinned Lean 4.30.0-rc2; producer sidecars are beside the bytes.
    let r = run(include_str!("fixtures/q2-part2/forged-recursor.ndjson"));
    refused(&r, "FRT.rec", "recursor numMinors");
    assert!(r
        .rows
        .iter()
        .find(|r| r.name.to_string() == "False")
        .unwrap()
        .verdict
        .is_ok());
    let r = run(include_str!("fixtures/q2-part2/ill-typed-body.ndjson"));
    refused(&r, "forged_bad", "type-check");
}
#[test]
fn planted_axiom_is_refused_after_seed_dependencies_accept() {
    let r = run(include_str!("fixtures/q2-part2/extra-axiom.ndjson"));
    refused(&r, "q3_extra_axiom", "axiom-policy");
    assert_eq!(r.counts().0, 22);
    assert!(r.axioms.is_empty());
}
#[test]
fn literal_constructor_expansion_remains_bounded() {
    let s = SEED.replace("\"natVal\":\"2\"", "\"natVal\":\"1000000000000\"");
    assert_ne!(s, SEED);
    // Literal admission no longer expands the number. This altered rfl body
    // demands a trillion recursive steps; the unchanged work bound refuses it.
    refused(&run(&s), "q2Nat", "out of budget");
}

const GENERAL: &str = include_str!("fixtures/q2-part2/general.ndjson");
#[test]
fn pinned_general_single_families_accept_with_parameters_and_prop_elimination() {
    let r = run(GENERAL);
    assert!(r.counts().1.is_empty(), "{r:?}");
    for n in [
        "List.rec",
        "And.rec",
        "Or.rec",
        "Subtype.rec",
        "Decidable.rec",
        "Bool.rec",
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

fn list_field(negative: bool) -> String {
    use std::collections::HashMap;
    let mut rows: Vec<Value> = GENERAL
        .lines()
        .map(|l| serde_json::from_str(l).unwrap())
        .collect();
    let list_name = rows
        .iter()
        .find(|r| {
            r.get("str")
                .is_some_and(|s| s["str"] == "List" && s["pre"] == 0)
        })
        .unwrap()["in"]
        .as_u64()
        .unwrap();
    let pos = rows
        .iter()
        .position(|r| {
            r.get("inductive")
                .is_some_and(|b| b["types"][0]["name"] == list_name)
        })
        .unwrap();
    let exprs: HashMap<u64, Value> = rows
        .iter()
        .filter_map(|r| Some((r.get("ie")?.as_u64()?, r.clone())))
        .collect();
    let mut id = exprs.keys().max().copied().unwrap() + 1;
    let mut added = Vec::new();
    let mut add = |mut v: Value| {
        let i = id;
        id += 1;
        v["ie"] = Value::from(i);
        added.push(v);
        i
    };
    let top_id = rows[pos]["inductive"]["ctors"][1]["type"].as_u64().unwrap();
    let mut top = exprs[&top_id].clone();
    let head_id = top["forallE"]["body"].as_u64().unwrap();
    let mut head = exprs[&head_id].clone();
    if negative {
        rows[pos]["inductive"]["types"][0]["isReflexive"] = Value::Bool(true);
        let tail = &exprs[&head["forallE"]["body"].as_u64().unwrap()];
        let list_app = &exprs[&tail["forallE"]["type"].as_u64().unwrap()];
        let bv0 = add(serde_json::json!({"bvar":0}));
        let prop = add(serde_json::json!({"sort":0}));
        let app = add(serde_json::json!({"app":{"fn":list_app["app"]["fn"],"arg":bv0}}));
        let dom = add(
            serde_json::json!({"forallE":{"name":0,"binderInfo":"default","type":app,"body":prop}}),
        );
        head["forallE"]["type"] = Value::from(dom);
    } else {
        // A field : Type u has a sort above List's Type u result universe.
        head["forallE"]["type"] = top["forallE"]["type"].clone();
    }
    top["forallE"]["body"] = Value::from(add(head));
    rows[pos]["inductive"]["ctors"][1]["type"] = Value::from(add(top));
    rows.splice(pos..pos, added);
    rows.iter().map(|v| format!("{v}\n")).collect()
}
#[test]
fn negative_occurrence_is_refused_by_strict_positivity() {
    refused(&run(&list_field(true)), "List", "non-strictly-positive");
}
#[test]
fn too_large_field_is_refused_by_universe_constraint() {
    refused(&run(&list_field(false)), "List", "field sort exceeds");
}

#[test]
fn pinned_type_annotations_are_consumed_by_checked_unfolding() {
    let r = run(include_str!("fixtures/q2-part2/annotations.ndjson"));
    assert_eq!(r.counts().0, 11, "{r:?}");
    assert!(r.counts().1.is_empty());
}

#[test]
fn annotation_definition_must_check_before_it_can_be_consumed() {
    let source = include_str!("fixtures/q2-part2/annotations.ndjson");
    let mut rows: Vec<Value> = source
        .lines()
        .map(|l| serde_json::from_str(l).unwrap())
        .collect();
    let def = rows
        .iter_mut()
        .find_map(|v| v.get_mut("def"))
        .expect("outParam definition");
    def["value"] = def["type"].clone();
    let forged: String = rows.iter().map(|v| format!("{v}\n")).collect();
    let r = run(&forged);
    refused(&r, "outParam", "type-check");
    refused(&r, "HPow", "unknown-constant: outParam");
}

#[test]
fn constructor_result_is_not_unfolded_before_admission() {
    let r = run(include_str!("fixtures/q2-part2/arena-056.ndjson"));
    let e = r
        .rows
        .iter()
        .find(|r| r.name.to_string() == "reduceCtorType")
        .unwrap()
        .verdict
        .as_ref()
        .unwrap_err();
    assert_eq!(e.reason(), "admission");
    assert!(
        e.to_string()
            .contains("generated recursor type failed kernel check"),
        "{e}"
    );
}

#[test]
fn eq_k_flag_cannot_be_disabled_by_the_export() {
    let mut rs: Vec<Value> = SEED
        .lines()
        .map(|l| serde_json::from_str(l).unwrap())
        .collect();
    let block = rs
        .iter_mut()
        .find_map(|r| r.get_mut("inductive").filter(|b| b["recs"][0]["k"] == true))
        .unwrap();
    block["recs"][0]["k"] = Value::Bool(false);
    let s: String = rs.iter().map(|v| format!("{v}\n")).collect();
    refused(&run(&s), "Eq.rec", "recursor K flag");
}

#[test]
fn header_consistent_forged_recursor_rule_is_refused() {
    let r = run(include_str!("fixtures/q2-part2/forged-rule.ndjson"));
    refused(&r, "FRR.rec", "recursor rule RHS mismatch");
    assert!(r
        .rows
        .iter()
        .find(|r| r.name.to_string() == "forged_rule_eq")
        .unwrap()
        .verdict
        .is_err());
}
