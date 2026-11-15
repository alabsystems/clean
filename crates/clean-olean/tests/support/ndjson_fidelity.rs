// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exports for `tests/ndjson_front_door_fidelity.rs`: the 2026-10-22
//! re-review's repros (N1-N10), the honest exports minted from the pinned
//! toolchain (`tests/fixtures/lean/v4.30.0-rc2/ndjson_minted/`), and the
//! adversarial level shapes. Data only; every assertion is in the test file.

use std::io::Read;
use std::path::PathBuf;
use std::time::Duration;

use clean_olean::ndjson::{DeclarationVerdict, ExportReport};

use super::kernel_arena;

/// The arena's header: Lean 4.29.1.
pub const META_429: &str = r#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"f72c35b3f637c8c6571d353742168ab66cc22c00","version":"4.29.1"}}}"#;

fn fixtures() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

/// A review repro under `tests/fixtures/ndjson_fidelity/forged/`.
pub fn forged(name: &str) -> String {
    let path = fixtures().join("ndjson_fidelity/forged").join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

/// A minted export under `tests/fixtures/lean/v4.30.0-rc2/ndjson_minted/`
/// (`MintExports.lean` there); a `.gz` one is decompressed in memory.
pub fn minted(name: &str) -> String {
    let path = fixtures().join("lean/v4.30.0-rc2/ndjson_minted").join(name);
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    if name.ends_with(".gz") {
        let mut text = String::new();
        flate2::read::GzDecoder::new(&bytes[..])
            .read_to_string(&mut text)
            .unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        text
    } else {
        String::from_utf8(bytes).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
    }
}

/// An archived arena test, as text.
pub fn archived(path: &str) -> String {
    let files = kernel_arena::archive();
    String::from_utf8(files[path].clone()).expect("the archive's exports are UTF-8")
}

/// `text` with the one occurrence of `from` replaced by `to` (panics unless
/// there is exactly one, so a forgery cannot silently miss its target).
pub fn replaced_once(text: &str, from: &str, to: &str) -> String {
    assert_eq!(text.matches(from).count(), 1, "`{from}` must occur once");
    text.replacen(from, to, 1)
}

/// `text` with `line` inserted before the one line that starts with `before`.
pub fn inserted_before(text: &str, before: &str, line: &str) -> String {
    let at = text.find(&format!("\n{before}")).expect("anchor line") + 1;
    assert!(
        !text[at + 1..].contains(&format!("\n{before}")),
        "`{before}` must start one line"
    );
    format!("{}{line}\n{}", &text[..at], &text[at..])
}

/// The verdict of `name` in a report.
pub fn verdict_of(report: &ExportReport, name: &str) -> Option<DeclarationVerdict> {
    report
        .records
        .iter()
        .find(|r| r.name == name)
        .map(|r| r.verdict)
}

/// Run `check` on another thread and fail the test if it has not finished
/// within `bound`.
pub fn within<T: Send + 'static>(bound: Duration, check: impl FnOnce() -> T + Send + 'static) -> T {
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(check());
    });
    rx.recv_timeout(bound)
        .unwrap_or_else(|_| panic!("the check did not finish within {bound:?}"))
}

/// Review finding N1's repro: `bad/other/nat-lit-add-bad`'s `Eq` and `Nat`
/// (its first 101 lines), then `Nat.<head> := fun a _ => a` and
/// `forgedAdd : Nat.<head> 2 3 = 2 := Eq.refl 2`. Lean's kernel folds a
/// constant named `Nat.add` on literals by name (`reduce_nat`), so with
/// `head = "add"` it computes `5` and refuses the theorem; under any other
/// name it unfolds the definition, as Clean does, and admits it.
pub fn forged_fold_head(head: &str) -> String {
    let text = archived("bad/other/nat-lit-add-bad.ndjson");
    let prefix: Vec<&str> = text.lines().take(101).collect();
    format!("{}\n{}\n", prefix.join("\n"), fold_head_tail(head))
}

fn fold_head_tail(head: &str) -> String {
    [
        &format!(r#"{{"in":900,"str":{{"pre":15,"str":"{head}"}}}}"#),
        r#"{"in":901,"str":{"pre":0,"str":"forgedAdd"}}"#,
        r#"{"forallE":{"binderInfo":"default","body":44,"name":18,"type":43},"ie":900}"#,
        r#"{"ie":901,"lam":{"binderInfo":"default","body":2,"name":18,"type":43}}"#,
        r#"{"ie":902,"lam":{"binderInfo":"default","body":901,"name":18,"type":43}}"#,
        r#"{"def":{"all":[900],"hints":{"regular":1},"levelParams":[],"name":900,"safety":"safe","type":900,"value":902}}"#,
        r#"{"const":{"name":1,"us":[3]},"ie":903}"#,
        r#"{"app":{"arg":43,"fn":903},"ie":904}"#,
        r#"{"ie":905,"natVal":"2"}"#,
        r#"{"ie":906,"natVal":"3"}"#,
        r#"{"const":{"name":900,"us":[]},"ie":907}"#,
        r#"{"app":{"arg":905,"fn":907},"ie":908}"#,
        r#"{"app":{"arg":906,"fn":908},"ie":909}"#,
        r#"{"app":{"arg":909,"fn":904},"ie":910}"#,
        r#"{"app":{"arg":905,"fn":910},"ie":911}"#,
        r#"{"const":{"name":9,"us":[3]},"ie":912}"#,
        r#"{"app":{"arg":43,"fn":912},"ie":913}"#,
        r#"{"app":{"arg":905,"fn":913},"ie":914}"#,
        r#"{"thm":{"all":[901],"levelParams":[],"name":901,"type":911,"value":914}}"#,
    ]
    .join("\n")
}

/// Review round 3's variant of N1: the same `Eq`/`Nat` prefix, then
/// `Lean.<head> := fun n => n` (a `def`, or an `opaque` when `opaque`),
/// `def c : Nat := 5` and `forgedReduceNat : Lean.<head> c = 5 := Eq.refl 5`.
/// Lean's kernel evaluates `Lean.reduceNat c` BY NAME with compiled code
/// (`reduce_native`), which a replayed export does not have, so pinned Lean
/// refuses the theorem ("(kernel) (interpreter) unknown declaration 'c'");
/// under any other name it unfolds the identity and admits it.
pub fn forged_reduce_nat(head: &str, opaque: bool) -> String {
    let text = archived("bad/other/nat-lit-add-bad.ndjson");
    let prefix: Vec<&str> = text.lines().take(101).collect();
    let declaration = if opaque {
        r#"{"opaque":{"all":[901],"isUnsafe":false,"levelParams":[],"name":901,"type":44,"value":900}}"#
    } else {
        r#"{"def":{"all":[901],"hints":{"regular":1},"levelParams":[],"name":901,"safety":"safe","type":44,"value":900}}"#
    };
    let tail = [
        r#"{"in":900,"str":{"pre":0,"str":"Lean"}}"#,
        &format!(r#"{{"in":901,"str":{{"pre":900,"str":"{head}"}}}}"#),
        r#"{"in":902,"str":{"pre":0,"str":"c"}}"#,
        r#"{"in":903,"str":{"pre":0,"str":"forgedReduceNat"}}"#,
        r#"{"ie":900,"lam":{"binderInfo":"default","body":1,"name":18,"type":43}}"#,
        declaration,
        r#"{"ie":901,"natVal":"5"}"#,
        r#"{"def":{"all":[902],"hints":{"regular":1},"levelParams":[],"name":902,"safety":"safe","type":43,"value":901}}"#,
        r#"{"const":{"name":1,"us":[3]},"ie":902}"#,
        r#"{"app":{"arg":43,"fn":902},"ie":903}"#,
        r#"{"const":{"name":901,"us":[]},"ie":904}"#,
        r#"{"const":{"name":902,"us":[]},"ie":905}"#,
        r#"{"app":{"arg":905,"fn":904},"ie":906}"#,
        r#"{"app":{"arg":906,"fn":903},"ie":907}"#,
        r#"{"app":{"arg":901,"fn":907},"ie":908}"#,
        r#"{"const":{"name":9,"us":[3]},"ie":909}"#,
        r#"{"app":{"arg":43,"fn":909},"ie":910}"#,
        r#"{"app":{"arg":901,"fn":910},"ie":911}"#,
        r#"{"thm":{"all":[903],"levelParams":[],"name":903,"type":908,"value":911}}"#,
    ]
    .join("\n");
    format!("{}\n{tail}\n", prefix.join("\n"))
}

/// An export of level records only, built record by record: names and
/// levels get fresh indices in order.
struct LevelExport {
    text: String,
    names: u64,
    levels: u64,
}

impl LevelExport {
    fn new() -> Self {
        Self {
            text: String::from(META_429),
            names: 0,
            levels: 0,
        }
    }

    fn level(&mut self, kind: &str, value: &str) -> u64 {
        self.levels += 1;
        self.text
            .push_str(&format!("\n{{\"il\":{},\"{kind}\":{value}}}", self.levels));
        self.levels
    }

    fn param(&mut self, name: &str) -> u64 {
        self.names += 1;
        self.text.push_str(&format!(
            "\n{{\"in\":{},\"str\":{{\"pre\":0,\"str\":\"{name}\"}}}}",
            self.names
        ));
        let index = self.names;
        self.level("param", &index.to_string())
    }

    fn pair(&mut self, kind: &str, a: u64, b: u64) -> u64 {
        self.level(kind, &format!("[{a},{b}]"))
    }

    /// `max(xs[0], max(xs[1], ...))`, one record per `max`.
    fn spine(&mut self, xs: &[u64]) -> u64 {
        let (last, rest) = xs.split_last().expect("a non-empty spine");
        rest.iter()
            .rev()
            .fold(*last, |m, &a| self.pair("max", a, m))
    }

    fn finish(mut self) -> String {
        self.text.push('\n');
        self.text
    }
}

/// Review round 3's N5 variant 1 (`mk_succ_groups.py`): eight `succ`-wrapped
/// spines of `imax(p, q)` (61 in all) under one `max`, each record within the
/// 256-node and 8-argument caps, then `extra` records `max(top, r)`, each of
/// which normalizes all 61.
pub fn level_succ_groups(extra: u64) -> String {
    let mut e = LevelExport::new();
    let mut succs = Vec::new();
    for (j, n) in [8, 8, 8, 8, 8, 8, 8, 5].into_iter().enumerate() {
        let mut imaxes = Vec::new();
        for i in 0..n {
            let p = e.param(&format!("p{j}_{i}"));
            let q = e.param(&format!("q{j}_{i}"));
            imaxes.push(e.pair("imax", p, q));
        }
        let m = e.spine(&imaxes);
        succs.push(e.level("succ", &m.to_string()));
    }
    let top = e.spine(&succs);
    let r = e.param("r");
    for _ in 0..extra {
        e.pair("max", top, r);
    }
    e.finish()
}

/// Review round 3's N5 variant 2 (`mk_rounds.py`): 50 `succ (succ (imax a
/// b))` under one counted argument, seven `imax z y_i` that the join of the
/// other side subsumes one per round, every record within the caps, then
/// `extra` records `max(top, r)`.
pub fn level_drop_rounds(extra: u64) -> String {
    let mut e = LevelExport::new();
    let mut groups = Vec::new();
    for (j, n) in [8, 8, 8, 8, 8, 5, 5].into_iter().enumerate() {
        let mut imaxes = Vec::new();
        for i in 0..n {
            let a = e.param(&format!("a{j}_{i}"));
            let b = e.param(&format!("b{j}_{i}"));
            imaxes.push(e.pair("imax", a, b));
        }
        let m = e.spine(&imaxes);
        groups.push(e.level("succ", &m.to_string()));
    }
    let g = e.spine(&groups);
    let big = e.level("succ", &g.to_string());
    let z = e.param("z");
    let ys: Vec<u64> = (0..7).map(|i| e.param(&format!("y{i}"))).collect();
    let mut a_side: Vec<u64> = ys.iter().map(|&y| e.pair("imax", z, y)).collect();
    a_side.push(big);
    let a = e.spine(&a_side);
    let mut b_side = vec![z];
    b_side.extend(&ys);
    let b = e.spine(&b_side);
    let top = e.pair("max", a, b);
    let r = e.param("r");
    for _ in 0..extra {
        e.pair("max", top, r);
    }
    e.finish()
}

/// `axiom <name> : Type` under the 4.29.1 header, `name` dotted into
/// string components.
pub fn axiom_named(name: &str) -> String {
    let mut lines = vec![META_429.to_owned()];
    for (i, component) in name.split('.').enumerate() {
        lines.push(format!(
            r#"{{"in":{},"str":{{"pre":{i},"str":"{component}"}}}}"#,
            i + 1
        ));
    }
    let last = name.split('.').count();
    lines.push(r#"{"il":1,"succ":0}"#.to_owned());
    lines.push(r#"{"ie":0,"sort":1}"#.to_owned());
    lines.push(format!(
        r#"{{"axiom":{{"isUnsafe":false,"levelParams":[],"name":{last},"type":0}}}}"#
    ));
    lines.join("\n")
}

/// `def imaxSuccForged.{v,w} : Sort (max (v+2) (w+3)) := Sort (succ L)` with
/// `L = imax v (w+1)`, or with `L = max v (w+1)` for the control. Lean's kernel
/// (pinned v4.30.0-rc2, measured) refuses the `imax` one: its normalization
/// does not push the outer `succ` through the `imax` it rewrites to a `max`,
/// so `succ (succ (imax v (w+1)))` and `max (v+2) (w+3)` are not equivalent
/// to it. It admits the `max` one.
pub fn imax_succ_def(imax: bool) -> String {
    let kind = if imax { "imax" } else { "max" };
    [
        META_429,
        r#"{"in":1,"str":{"pre":0,"str":"v"}}"#,
        r#"{"in":2,"str":{"pre":0,"str":"w"}}"#,
        r#"{"in":3,"str":{"pre":0,"str":"imaxSuccForged"}}"#,
        r#"{"il":1,"param":1}"#,
        r#"{"il":2,"param":2}"#,
        r#"{"il":3,"succ":2}"#,
        &format!(r#"{{"il":4,"{kind}":[1,3]}}"#),
        r#"{"il":5,"succ":4}"#,
        r#"{"il":6,"succ":1}"#,
        r#"{"il":7,"succ":6}"#,
        r#"{"il":8,"succ":3}"#,
        r#"{"il":9,"succ":8}"#,
        r#"{"il":10,"max":[7,9]}"#,
        r#"{"ie":0,"sort":10}"#,
        r#"{"ie":1,"sort":5}"#,
        r#"{"def":{"all":[3],"hints":"abbrev","levelParams":[1,2],"name":3,"safety":"safe","type":0,"value":1}}"#,
    ]
    .join("\n")
}

/// A level spine `max(imax(p0,q0), max(imax(p1,q1), ...))` of `composites`
/// arguments that no constructor simplifies, then `extra` records
/// `max(spine, r)`, each binding a new index (review finding N5's shape:
/// with 1023 composites and 1000 extra lines it is the 225 KB
/// `level_normalize_bomb`).
pub fn level_spine(composites: u64, extra: u64) -> String {
    let mut text = String::from(META_429);
    for i in 0..composites {
        text.push_str(&format!(
            "\n{{\"in\":{},\"str\":{{\"pre\":0,\"str\":\"p{i}\"}}}}\n{{\"in\":{},\"str\":{{\"pre\":0,\"str\":\"q{i}\"}}}}",
            2 * i + 1,
            2 * i + 2
        ));
    }
    let r_name = 2 * composites + 1;
    text.push_str(&format!(
        "\n{{\"in\":{r_name},\"str\":{{\"pre\":0,\"str\":\"r\"}}}}"
    ));
    // Levels: 3i+1 = p_i, 3i+2 = q_i, 3i+3 = imax(p_i, q_i).
    for i in 0..composites {
        text.push_str(&format!(
            "\n{{\"il\":{},\"param\":{}}}\n{{\"il\":{},\"param\":{}}}\n{{\"il\":{},\"imax\":[{},{}]}}",
            3 * i + 1,
            2 * i + 1,
            3 * i + 2,
            2 * i + 2,
            3 * i + 3,
            3 * i + 1,
            3 * i + 2
        ));
    }
    let mut next = 3 * composites + 1;
    let r = next;
    text.push_str(&format!("\n{{\"il\":{r},\"param\":{r_name}}}"));
    next += 1;
    // The right spine, innermost first.
    let mut spine = 3 * composites;
    for i in (0..composites.saturating_sub(1)).rev() {
        text.push_str(&format!(
            "\n{{\"il\":{next},\"max\":[{},{spine}]}}",
            3 * i + 3
        ));
        spine = next;
        next += 1;
    }
    for _ in 0..extra {
        text.push_str(&format!("\n{{\"il\":{next},\"max\":[{spine},{r}]}}"));
        next += 1;
    }
    text.push('\n');
    text
}

/// `axiom Std.«a.b» : Type` and `axiom Std.a<U+2024>b : Type`: two names
/// that differ, but whose components the reader spells alike once it has
/// escaped the first one's `.`.
pub fn escaped_name_collision() -> String {
    [
        META_429,
        r#"{"in":1,"str":{"pre":0,"str":"Std"}}"#,
        r#"{"in":2,"str":{"pre":1,"str":"a.b"}}"#,
        "{\"in\":3,\"str\":{\"pre\":1,\"str\":\"\u{2024}a\u{2024}b\"}}",
        r#"{"il":1,"succ":0}"#,
        r#"{"ie":0,"sort":1}"#,
        r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":2,"type":0}}"#,
        r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":3,"type":0}}"#,
    ]
    .join("\n")
}

/// Allow `within` a generous bound in an unoptimized build.
pub fn debug_scaled(release: Duration) -> Duration {
    if cfg!(debug_assertions) {
        release * 10
    } else {
        release
    }
}
