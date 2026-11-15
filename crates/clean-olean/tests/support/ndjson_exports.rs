// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! In-memory NDJSON exports for `tests/ndjson_front_door.rs`: the honest
//! control, archived tests and their forgeries, and the adversarial shapes of
//! the 2026-10-22 review. Data only; every assertion is in the test file.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::Duration;

use clean_olean::ndjson::{DeclarationVerdict, ExportReport};

use super::kernel_arena;

pub const META: &str = r#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"f72c35b3f637c8c6571d353742168ab66cc22c00","version":"4.29.1"}}}"#;

/// `axiom a : Type`, as lean4#15542's test spells it: the honest control every
/// rule arm perturbs.
pub const HONEST: [&str; 4] = [
    r#"{"in":1,"str":{"pre":0,"str":"a"}}"#,
    r#"{"il":1,"succ":0}"#,
    r#"{"ie":0,"sort":1}"#,
    r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"#,
];

/// `False` and its recursor, as the arena's `other/proj-of-prop` writes them.
pub const FALSE_BLOCK: [&str; 16] = [
    r#"{"in":1,"str":{"pre":0,"str":"False"}}"#,
    r#"{"ie":0,"sort":0}"#,
    r#"{"in":2,"str":{"pre":1,"str":"rec"}}"#,
    r#"{"in":3,"str":{"pre":0,"str":"u"}}"#,
    r#"{"il":1,"param":3}"#,
    r#"{"in":4,"str":{"pre":0,"str":"motive"}}"#,
    r#"{"in":5,"str":{"pre":0,"str":"t"}}"#,
    r#"{"const":{"name":1,"us":[]},"ie":1}"#,
    r#"{"ie":2,"sort":1}"#,
    r#"{"forallE":{"binderInfo":"default","body":2,"name":5,"type":1},"ie":3}"#,
    r#"{"bvar":1,"ie":4}"#,
    r#"{"bvar":0,"ie":5}"#,
    r#"{"app":{"arg":5,"fn":4},"ie":6}"#,
    r#"{"forallE":{"binderInfo":"default","body":6,"name":5,"type":1},"ie":7}"#,
    r#"{"forallE":{"binderInfo":"default","body":7,"name":4,"type":3},"ie":8}"#,
    r#"{"inductive":{"ctors":[],"recs":[{"all":[1],"isUnsafe":false,"k":false,"levelParams":[3],"name":2,"numIndices":0,"numMinors":0,"numMotives":1,"numParams":0,"rules":[],"type":8}],"types":[{"all":[1],"ctors":[],"isRec":false,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":1,"numIndices":0,"numNested":0,"numParams":0,"type":0}]}}"#,
];

/// After [`FALSE_BLOCK`]: `B : Prop` with `B.mk : (B → False) → B`, a
/// negative occurrence no kernel admits, in a block whose `all` is `ALL` and
/// whose flags are `REC` and `REFL`, then `bad : False` built from it. Lean's
/// replay builds the block from `all`; the reviewer's repro of 2026-10-22
/// (`all` = `[Z]`, a name no record declares) was accepted by 9b4a30b6a.
pub fn negative_block_export(all: &str, rec: bool, refl: bool) -> String {
    let block = format!(
        r#"{{"inductive":{{"ctors":[{{"cidx":0,"induct":6,"isUnsafe":false,"levelParams":[],"name":7,"numFields":1,"numParams":0,"type":11}}],"recs":[],"types":[{{"all":{all},"ctors":[7],"isRec":{rec},"isReflexive":{refl},"isUnsafe":false,"levelParams":[],"name":6,"numIndices":0,"numNested":0,"numParams":0,"type":0}}]}}}}"#
    );
    let tail = [
        r#"{"in":6,"str":{"pre":0,"str":"B"}}"#,
        r#"{"in":7,"str":{"pre":6,"str":"mk"}}"#,
        r#"{"in":8,"str":{"pre":0,"str":"Z"}}"#,
        r#"{"in":9,"str":{"pre":0,"str":"x"}}"#,
        r#"{"in":10,"str":{"pre":0,"str":"f"}}"#,
        r#"{"in":11,"str":{"pre":0,"str":"bad"}}"#,
        r#"{"const":{"name":6,"us":[]},"ie":9}"#,
        r#"{"forallE":{"binderInfo":"default","body":1,"name":9,"type":9},"ie":10}"#,
        r#"{"forallE":{"binderInfo":"default","body":9,"name":10,"type":10},"ie":11}"#,
        block.as_str(),
        r#"{"ie":12,"proj":{"idx":0,"struct":5,"typeName":6}}"#,
        r#"{"app":{"arg":5,"fn":12},"ie":13}"#,
        r#"{"ie":14,"lam":{"binderInfo":"default","body":13,"name":9,"type":9}}"#,
        r#"{"const":{"name":7,"us":[]},"ie":15}"#,
        r#"{"app":{"arg":14,"fn":15},"ie":16}"#,
        r#"{"app":{"arg":16,"fn":14},"ie":17}"#,
        r#"{"thm":{"all":[11],"levelParams":[],"name":11,"type":1,"value":17}}"#,
    ];
    let mut text = String::from(META);
    for line in FALSE_BLOCK.iter().copied().chain(tail) {
        text.push('\n');
        text.push_str(line);
    }
    text.push('\n');
    text
}

/// The text of an archived test.
pub fn archived(path: &str) -> String {
    let files = kernel_arena::archive();
    String::from_utf8(files[path].clone()).expect("UTF-8 export")
}

/// `text` with `from` replaced by `to`, exactly once.
pub fn replaced_once(text: &str, from: &str, to: &str) -> String {
    assert_eq!(text.matches(from).count(), 1, "{from:?} must occur once");
    text.replacen(from, to, 1)
}

/// `inductive S : Type | mk : S → S` (recursive and structure-like) with its
/// recursor, `isRec` = `IS_REC`, and `t : ∀ x : S, S.mk x.0 = x := fun x =>
/// rfl`, appended to the arena's honest `Eq` export. Lean's kernel recomputes
/// `isRec` (true), so structure eta never fires on `S` and `t` is refused.
pub fn structure_eta_export(is_rec: bool) -> String {
    let eq = archived("good/tutorial/043_eqType.ndjson");
    let block = format!(
        r#"{{"inductive":{{"types":[{{"name":1000,"levelParams":[],"type":1000,"numParams":0,"numIndices":0,"all":[1000],"ctors":[1001],"numNested":0,"isRec":{is_rec},"isUnsafe":false,"isReflexive":false}}],"ctors":[{{"name":1001,"levelParams":[],"type":1003,"induct":1000,"cidx":0,"numParams":0,"numFields":1,"isUnsafe":false}}],"recs":[{{"name":1002,"levelParams":[1003],"type":1022,"all":[1000],"numParams":0,"numIndices":0,"numMotives":1,"numMinors":1,"rules":[{{"ctor":1001,"nfields":1,"rhs":1031}}],"k":false,"isUnsafe":false}}]}}}}"#
    );
    let lines = [
        r#"{"in":1000,"str":{"pre":0,"str":"S"}}"#,
        r#"{"in":1001,"str":{"pre":1000,"str":"mk"}}"#,
        r#"{"in":1002,"str":{"pre":1000,"str":"rec"}}"#,
        r#"{"in":1003,"str":{"pre":0,"str":"u"}}"#,
        r#"{"in":1004,"str":{"pre":0,"str":"x"}}"#,
        r#"{"in":1005,"str":{"pre":0,"str":"t"}}"#,
        r#"{"il":1001,"succ":0}"#,
        r#"{"il":1002,"param":1003}"#,
        r#"{"ie":1000,"sort":1001}"#,
        r#"{"ie":1001,"const":{"name":1000,"us":[]}}"#,
        r#"{"ie":1003,"forallE":{"name":1004,"type":1001,"body":1001,"binderInfo":"default"}}"#,
        r#"{"ie":1004,"sort":1002}"#,
        r#"{"ie":1005,"forallE":{"name":1005,"type":1001,"body":1004,"binderInfo":"default"}}"#,
        r#"{"ie":1010,"bvar":0}"#,
        r#"{"ie":1011,"bvar":1}"#,
        r#"{"ie":1012,"bvar":2}"#,
        r#"{"ie":1013,"app":{"fn":1011,"arg":1010}}"#,
        r#"{"ie":1014,"const":{"name":1001,"us":[]}}"#,
        r#"{"ie":1015,"app":{"fn":1014,"arg":1011}}"#,
        r#"{"ie":1016,"app":{"fn":1012,"arg":1015}}"#,
        r#"{"ie":1017,"forallE":{"name":1004,"type":1013,"body":1016,"binderInfo":"default"}}"#,
        r#"{"ie":1018,"forallE":{"name":1004,"type":1001,"body":1017,"binderInfo":"default"}}"#,
        r#"{"ie":1019,"app":{"fn":1012,"arg":1010}}"#,
        r#"{"ie":1020,"forallE":{"name":1005,"type":1001,"body":1019,"binderInfo":"default"}}"#,
        r#"{"ie":1021,"forallE":{"name":1001,"type":1018,"body":1020,"binderInfo":"default"}}"#,
        r#"{"ie":1022,"forallE":{"name":1003,"type":1005,"body":1021,"binderInfo":"implicit"}}"#,
        r#"{"ie":1023,"const":{"name":1002,"us":[1002]}}"#,
        r#"{"ie":1024,"app":{"fn":1023,"arg":1012}}"#,
        r#"{"ie":1025,"app":{"fn":1024,"arg":1011}}"#,
        r#"{"ie":1026,"app":{"fn":1025,"arg":1010}}"#,
        r#"{"ie":1027,"app":{"fn":1011,"arg":1010}}"#,
        r#"{"ie":1028,"app":{"fn":1027,"arg":1026}}"#,
        r#"{"ie":1029,"lam":{"name":1004,"type":1001,"body":1028,"binderInfo":"default"}}"#,
        r#"{"ie":1030,"lam":{"name":1001,"type":1018,"body":1029,"binderInfo":"default"}}"#,
        r#"{"ie":1031,"lam":{"name":1003,"type":1005,"body":1030,"binderInfo":"implicit"}}"#,
        block.as_str(),
        r#"{"ie":1040,"const":{"name":1,"us":[1001]}}"#,
        r#"{"ie":1041,"app":{"fn":1040,"arg":1001}}"#,
        r#"{"ie":1042,"proj":{"typeName":1000,"idx":0,"struct":1010}}"#,
        r#"{"ie":1043,"app":{"fn":1014,"arg":1042}}"#,
        r#"{"ie":1044,"app":{"fn":1041,"arg":1043}}"#,
        r#"{"ie":1045,"app":{"fn":1044,"arg":1010}}"#,
        r#"{"ie":1046,"forallE":{"name":1004,"type":1001,"body":1045,"binderInfo":"default"}}"#,
        r#"{"ie":1047,"const":{"name":9,"us":[1001]}}"#,
        r#"{"ie":1048,"app":{"fn":1047,"arg":1001}}"#,
        r#"{"ie":1049,"app":{"fn":1048,"arg":1010}}"#,
        r#"{"ie":1050,"lam":{"name":1004,"type":1001,"body":1049,"binderInfo":"default"}}"#,
        r#"{"thm":{"name":1005,"levelParams":[],"type":1046,"value":1050,"all":[1005]}}"#,
    ];
    let mut text = eq.trim_end().to_owned();
    for line in lines {
        text.push('\n');
        text.push_str(line);
    }
    text.push('\n');
    text
}

/// A level ladder `l_k = imax l_{k-1} (imax l_{k-1} u)`, `k` rungs: a few bytes
/// per rung, a level tree of about `2^(k+1)` nodes; then `Sort l_k`.
pub fn level_ladder(rungs: u64) -> String {
    let mut text = String::from(META);
    text.push_str("\n{\"in\":1,\"str\":{\"pre\":0,\"str\":\"u\"}}");
    text.push_str("\n{\"in\":2,\"str\":{\"pre\":0,\"str\":\"v\"}}");
    text.push_str("\n{\"il\":1,\"param\":2}");
    text.push_str("\n{\"il\":2,\"param\":1}");
    let mut prev = 1;
    for k in 1..=rungs {
        let h = 2 * k + 1;
        let l = 2 * k + 2;
        text.push_str(&format!("\n{{\"il\":{h},\"imax\":[{prev},2]}}"));
        text.push_str(&format!("\n{{\"il\":{l},\"imax\":[{prev},{h}]}}"));
        prev = l;
    }
    text.push_str(&format!("\n{{\"ie\":0,\"sort\":{prev}}}\n"));
    text
}

/// `Quot.{u} : {α : Sort u} → (α → α → Prop) → Sort u`, the type `quotDecl`
/// gives `Quot`, and its `quot` record: an export with the quotient's first
/// record and nothing else.
pub const QUOT_ONLY: [&str; 13] = [
    r#"{"in":1,"str":{"pre":0,"str":"Quot"}}"#,
    r#"{"in":2,"str":{"pre":0,"str":"u"}}"#,
    r#"{"in":3,"str":{"pre":0,"str":"α"}}"#,
    r#"{"in":4,"str":{"pre":0,"str":"r"}}"#,
    r#"{"il":1,"param":2}"#,
    r#"{"ie":0,"sort":1}"#,
    r#"{"ie":1,"sort":0}"#,
    r#"{"ie":2,"bvar":0}"#,
    r#"{"ie":3,"bvar":1}"#,
    r#"{"ie":4,"forallE":{"name":0,"type":3,"body":1,"binderInfo":"default"}}"#,
    r#"{"ie":5,"forallE":{"name":0,"type":2,"body":4,"binderInfo":"default"}}"#,
    r#"{"ie":6,"forallE":{"name":4,"type":5,"body":0,"binderInfo":"default"}}"#,
    r#"{"ie":7,"forallE":{"name":3,"type":0,"body":6,"binderInfo":"implicit"}}"#,
];

/// `mutual A | a : A; B | b : A → B` with no recursors, the types' `isRec`
/// stored as `rec_a` and `rec_b`: Lean's flag is per BLOCK, so both are `true`.
pub fn mutual_export(rec_a: bool, rec_b: bool) -> String {
    let block = format!(
        r#"{{"inductive":{{"types":[{{"name":1,"levelParams":[],"type":0,"numParams":0,"numIndices":0,"all":[1,2],"ctors":[3],"numNested":0,"isRec":{rec_a},"isUnsafe":false,"isReflexive":false}},{{"name":2,"levelParams":[],"type":0,"numParams":0,"numIndices":0,"all":[1,2],"ctors":[4],"numNested":0,"isRec":{rec_b},"isUnsafe":false,"isReflexive":false}}],"ctors":[{{"name":3,"levelParams":[],"type":1,"induct":1,"cidx":0,"numParams":0,"numFields":0,"isUnsafe":false}},{{"name":4,"levelParams":[],"type":3,"induct":2,"cidx":0,"numParams":0,"numFields":1,"isUnsafe":false}}],"recs":[]}}}}"#
    );
    let lines = [
        r#"{"in":1,"str":{"pre":0,"str":"A"}}"#,
        r#"{"in":2,"str":{"pre":0,"str":"B"}}"#,
        r#"{"in":3,"str":{"pre":1,"str":"a"}}"#,
        r#"{"in":4,"str":{"pre":2,"str":"b"}}"#,
        r#"{"in":5,"str":{"pre":0,"str":"x"}}"#,
        r#"{"il":1,"succ":0}"#,
        r#"{"ie":0,"sort":1}"#,
        r#"{"ie":1,"const":{"name":1,"us":[]}}"#,
        r#"{"ie":2,"const":{"name":2,"us":[]}}"#,
        r#"{"ie":3,"forallE":{"name":5,"type":1,"body":2,"binderInfo":"default"}}"#,
        block.as_str(),
    ];
    let mut text = String::from(META);
    for line in lines {
        text.push('\n');
        text.push_str(line);
    }
    text.push('\n');
    text
}

/// [`HONEST`] and `def p : Type := a` with the given `safety`.
pub fn partial_def_export(safety: &str) -> String {
    let mut text = String::from(META);
    for line in HONEST.iter().copied().chain([
        r#"{"in":2,"str":{"pre":0,"str":"p"}}"#,
        r#"{"ie":1,"const":{"name":1,"us":[]}}"#,
    ]) {
        text.push('\n');
        text.push_str(line);
    }
    text.push_str(&format!(
        "\n{{\"def\":{{\"name\":2,\"levelParams\":[],\"type\":0,\"value\":1,\"hints\":\"opaque\",\"safety\":\"{safety}\",\"all\":[2]}}}}\n"
    ));
    text
}

/// `honest` (the arena's `129_quotSoundType`) with its `axiom Quot.sound`
/// given `Quot.ind`'s stored type.
pub fn forged_quot_sound(honest: &str) -> String {
    let names: BTreeMap<u64, String> = honest
        .lines()
        .filter_map(|l| serde_json::from_str::<serde_json::Value>(l).ok())
        .filter_map(|v| {
            let index = v.get("in")?.as_u64()?;
            let (pre, component) = if let Some(s) = v.get("str") {
                (s["pre"].as_u64()?, s["str"].as_str()?.to_owned())
            } else {
                let n = v.get("num")?;
                (n["pre"].as_u64()?, n["i"].as_u64()?.to_string())
            };
            Some((index, pre, component))
        })
        .fold(BTreeMap::new(), |mut names, (index, pre, component)| {
            let prefix: String = names.get(&pre).cloned().unwrap_or_default();
            let full = if prefix.is_empty() {
                component
            } else {
                format!("{prefix}.{component}")
            };
            names.insert(index, full);
            names
        });
    let sound = names
        .iter()
        .find(|(_, n)| n.as_str() == "Quot.sound")
        .map(|(i, _)| *i)
        .expect("the export declares Quot.sound");
    let quot_ind_type = honest
        .lines()
        .find(|l| l.starts_with("{\"quot\"") && l.contains("\"kind\":\"ind\""))
        .and_then(|l| serde_json::from_str::<serde_json::Value>(l).ok())
        .and_then(|v| v["quot"]["type"].as_u64())
        .expect("the export has Quot.ind's quot record");
    honest
        .lines()
        .map(|l| {
            let is_sound = serde_json::from_str::<serde_json::Value>(l)
                .ok()
                .is_some_and(|v| v["axiom"]["name"].as_u64() == Some(sound));
            if is_sound {
                let v: serde_json::Value = serde_json::from_str(l).expect("JSON");
                let old = format!("\"type\":{}", v["axiom"]["type"]);
                replaced_once(l, &old, &format!("\"type\":{quot_ind_type}"))
            } else {
                l.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// `n` lets that differ only in their names (one `Name.num` each), over one
/// sort: every one shares the kernel's 32-bit metadata hash.
pub fn colliding_lets_export(n: u64) -> String {
    let mut text = String::from(META);
    text.push_str("\n{\"ie\":0,\"sort\":0}");
    for k in 1..=n {
        text.push_str(&format!("\n{{\"in\":{k},\"num\":{{\"pre\":0,\"i\":{k}}}}}"));
    }
    for k in 1..=n {
        text.push_str(&format!(
            "\n{{\"ie\":{k},\"letE\":{{\"name\":{k},\"type\":0,\"value\":0,\"body\":0,\"nondep\":false}}}}"
        ));
    }
    text.push('\n');
    text
}

/// Two application spines of `n` nodes over lambdas that differ only in
/// binder information: equal metadata at every level.
pub fn binder_info_spines_export(n: u64) -> String {
    let mut text = String::from(META);
    text.push_str("\n{\"ie\":0,\"sort\":0}\n{\"ie\":1,\"bvar\":0}");
    // Two spines over lambdas that differ only in binder information.
    for (base, info) in [(10, "default"), (10 + n + 1, "implicit")] {
        text.push_str(&format!(
            "\n{{\"ie\":{base},\"lam\":{{\"name\":0,\"type\":0,\"body\":1,\"binderInfo\":\"{info}\"}}}}"
        ));
        for k in 1..=n {
            text.push_str(&format!(
                "\n{{\"ie\":{},\"app\":{{\"fn\":{},\"arg\":0}}}}",
                base + k,
                base + k - 1
            ));
        }
    }
    text.push('\n');
    text
}

/// [`HONEST`] with an `mdata` record whose payload nests `depth` arrays.
pub fn nested_mdata_lines(depth: usize) -> Vec<String> {
    let mut lines: Vec<String> = HONEST.iter().map(|s| (*s).to_owned()).collect();
    lines.insert(
        3,
        format!(
            "{{\"ie\":1,\"mdata\":{{\"expr\":0,\"data\":{{\"k\":{}{}}}}}}}",
            "[".repeat(depth),
            "]".repeat(depth)
        ),
    );
    lines
}

/// Arm (d)'s two inputs: where a v4.30.0-rc2 lean4export export of
/// `Init.Prelude` is vendored once minted, and the export-minting lane that
/// mints it (plan item `checkers-export-minting-lane`).
pub fn arm_d_inputs() -> (PathBuf, PathBuf) {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    (
        root.join("tests/fixtures/lean/v4.30.0-rc2/ndjson/Init.Prelude.ndjson"),
        root.join("../../scripts/lean_export_mint.sh"),
    )
}

/// `lines` with line `at` replaced by `with`.
pub fn perturbed(at: usize, with: &str) -> Vec<String> {
    let mut lines: Vec<String> = HONEST.iter().map(|s| (*s).to_owned()).collect();
    lines[at] = with.to_owned();
    lines
}

/// Run `check` on another thread and fail the test if it has not finished
/// within `bound`: a reader that does not terminate must fail, not hang the
/// suite.
pub fn within<T: Send + 'static>(bound: Duration, check: impl FnOnce() -> T + Send + 'static) -> T {
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            let _ = tx.send(check());
        })
        .expect("spawn the check");
    rx.recv_timeout(bound)
        .unwrap_or_else(|e| panic!("the check did not finish within {bound:?}: {e}"))
}

/// What became of declaration `name`.
pub fn verdict_of(report: &ExportReport, name: &str) -> Option<DeclarationVerdict> {
    report
        .records
        .iter()
        .find(|r| r.name == name)
        .map(|r| r.verdict)
}
