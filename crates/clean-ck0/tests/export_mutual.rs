//! Original pinned mutual exports and semantic mutations of those same bytes.
use clean_ck0::export::{replay, Dialect, Report};
use serde_json::Value;
const SOURCE: &str = include_str!("fixtures/q2-part2/mutual.ndjson");
fn run(s: &str) -> Report {
    replay(s.as_bytes(), Dialect::Lean4Export31).expect("wire syntax")
}
fn mutate(f: impl FnOnce(&mut Value)) -> String {
    let mut rows: Vec<Value> = SOURCE
        .lines()
        .map(|l| serde_json::from_str(l).unwrap())
        .collect();
    f(rows
        .iter_mut()
        .find_map(|r| {
            r.get_mut("inductive")
                .filter(|b| b["types"].as_array().unwrap().len() == 2)
        })
        .unwrap());
    rows.iter().map(|v| format!("{v}\n")).collect()
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
fn pinned_mutual_parameters_indices_and_prop_restriction_accept() {
    let r = run(SOURCE);
    assert_eq!(r.counts().0, 27, "{r:?}");
    assert!(r.counts().1.is_empty());
}
#[test]
fn forged_motive_count_refuses_the_complete_block() {
    let s = mutate(|b| b["recs"][0]["numMotives"] = Value::from(1));
    let r = run(&s);
    for name in [
        "Q2Tree",
        "Q2Forest",
        "Q2Tree.node",
        "Q2Forest.nil",
        "Q2Forest.cons",
        "Q2Tree.rec",
        "Q2Forest.rec",
    ] {
        refused(&r, name, "recursor numMotives");
    }
}
#[test]
fn forged_cross_member_rhs_is_refused() {
    let s = mutate(|b| {
        b["recs"][1]["rules"][0]["rhs"] = b["recs"][0]["rules"][0]["rhs"].clone();
    });
    refused(&run(&s), "Q2Forest.rec", "recursor rule RHS mismatch");
}
#[test]
fn mutually_inductive_types_must_share_the_result_universe() {
    let mut rows: Vec<Value> = SOURCE
        .lines()
        .map(|l| serde_json::from_str(l).unwrap())
        .collect();
    let pos = rows
        .iter()
        .position(|r| {
            r.get("inductive")
                .is_some_and(|b| b["types"].as_array().unwrap().len() == 2)
        })
        .unwrap();
    let ty = rows[pos]["inductive"]["types"][1]["type"].as_u64().unwrap();
    let mut top = rows
        .iter()
        .find(|r| r.get("ie") == Some(&Value::from(ty)))
        .unwrap()
        .clone();
    let tail = top["forallE"]["body"].as_u64().unwrap();
    let level = rows
        .iter()
        .find(|r| r.get("ie") == Some(&Value::from(tail)))
        .unwrap()["sort"]
        .clone();
    let il = rows
        .iter()
        .filter_map(|r| r.get("il")?.as_u64())
        .max()
        .unwrap()
        + 1;
    let ie = rows
        .iter()
        .filter_map(|r| r.get("ie")?.as_u64())
        .max()
        .unwrap()
        + 1;
    top["ie"] = Value::from(ie + 1);
    top["forallE"]["body"] = Value::from(ie);
    rows[pos]["inductive"]["types"][1]["type"] = Value::from(ie + 1);
    rows.splice(
        pos..pos,
        [
            serde_json::json!({"il":il,"succ":level}),
            serde_json::json!({"ie":ie,"sort":il}),
            top,
        ],
    );
    let s: String = rows.iter().map(|v| format!("{v}\n")).collect();
    refused(&run(&s), "Q2Forest", "mutual result universe");
}
