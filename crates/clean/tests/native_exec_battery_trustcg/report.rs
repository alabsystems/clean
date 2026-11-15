// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The LX0 report: identities, rows, and the JSON / Markdown renderings, plus
//! the few JSON reads the runner needs (this test crate has no JSON parser,
//! so receipts and pins are read field by field, escapes honoured).

use std::collections::BTreeMap;
use std::path::Path;
use std::process::Command;

/// Every trust-cg outcome class, in report order.
pub const OUTCOMES: [&str; 9] = [
    "BYTE_EQUAL",
    "WRONG_OUTPUT",
    "REFUSED_RUNTIME",
    "RUN_CRASH",
    "LINK_FAILED",
    "TRUSTCG_REFUSED",
    "EMIT_TRUSTIR_REFUSED",
    "TIMEOUT",
    "NO_RECEIPT",
];

pub const CLAIM: &str = "measurement only; no binary claim; lane = clean-compiler-unvalidated";
const SCHEMA: &str = "clean-lx0-trustcg-native-battery-v1";
pub const DRIVER: &str = "clean run --backend trust-cg --receipt <file> (crates/clean/tests/native_exec_battery_trustcg.rs)";
pub const GENERATED_BY: &str = "CLEAN_LX0_UPDATE=1 CLEAN_TRUST_CG_BIN=<trust-cg> targo --unverified test --locked -p clean --features trust-ir-backend --test native_exec_battery_trustcg";

/// One program's trust-cg lane result.
#[derive(Debug, Default)]
pub struct TrustCgRun {
    pub outcome: &'static str,
    pub step: String,
    pub cause: String,
    pub rc: Option<i32>,
    pub exit_zero: Option<bool>,
    pub module_digest: String,
    pub kernel_tv_certified: usize,
    pub bodies_unvalidated: usize,
    pub driver_entry: String,
}

/// One program's row.
#[derive(Debug)]
pub struct Row {
    pub name: String,
    pub in_scope: bool,
    pub c_lane: &'static str,
    pub c_lane_pinned: String,
    pub lean_rc: i32,
    pub trustcg: TrustCgRun,
}

/// What the `trust-cg` a bare `PATH` lookup finds (when it is not the
/// selected consumer) did with one program. Recorded when minting, never
/// compared against the pins: it is a property of the measuring box.
#[derive(Debug)]
pub struct ConsumerProbe {
    pub path: String,
    pub version: String,
    pub program: String,
    pub run: TrustCgRun,
}

/// What was measured with what.
#[derive(Debug)]
pub struct Identity {
    pub clean_sha: String,
    pub clean_tree_dirty: bool,
    pub trust_cg_path: String,
    pub trust_cg_version: String,
    pub trust_cg_blake3: String,
    pub trust_cg_source: String,
    pub host: String,
    pub cc: String,
    pub lean: String,
}

fn first_line(cmd: &mut Command) -> String {
    cmd.output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| {
            String::from_utf8_lossy(&o.stdout)
                .lines()
                .next()
                .unwrap_or("")
                .trim()
                .to_owned()
        })
        .unwrap_or_else(|| "<unavailable>".to_owned())
}

/// The first line of `<tool> --version`, or `<unavailable>`.
pub fn tool_version(tool: &Path) -> String {
    first_line(Command::new(tool).arg("--version"))
}

impl Identity {
    pub fn measure(trust_cg: &Path, repo: &Path) -> Self {
        assert!(
            trust_cg.is_file(),
            "CLEAN_TRUST_CG_BIN={} does not name a file",
            trust_cg.display()
        );
        let path = std::fs::canonicalize(trust_cg).expect("canonicalize trust-cg");
        let bytes = std::fs::read(&path).expect("read the trust-cg binary");
        let version = tool_version(&path);
        assert_ne!(
            version,
            "<unavailable>",
            "`{} --version` failed",
            path.display()
        );
        let dirty = Command::new("git")
            .arg("-C")
            .arg(repo)
            .args(["status", "--porcelain", "--untracked-files=no"])
            .output()
            .map(|o| !o.stdout.is_empty())
            .unwrap_or(true);
        let lean = std::fs::read_to_string(
            repo.join("tests/fixtures/native_exec_battery/expected/LEAN_VERSION"),
        )
        .expect("expected/LEAN_VERSION");
        Self {
            clean_sha: first_line(
                Command::new("git")
                    .arg("-C")
                    .arg(repo)
                    .args(["rev-parse", "HEAD"]),
            ),
            clean_tree_dirty: dirty,
            trust_cg_path: path.display().to_string(),
            trust_cg_version: version,
            trust_cg_blake3: blake3::hash(&bytes).to_hex().to_string(),
            trust_cg_source: std::env::var("CLEAN_LX0_TRUSTCG_SOURCE")
                .unwrap_or_else(|_| "unrecorded".to_owned()),
            host: format!(
                "{}-{} ({})",
                std::env::consts::ARCH,
                std::env::consts::OS,
                first_line(Command::new("uname").arg("-rs"))
            ),
            cc: first_line(
                Command::new(std::env::var("CC").unwrap_or_else(|_| "cc".to_owned()))
                    .arg("--version"),
            ),
            lean: lean.trim().to_owned(),
        }
    }
}

/// The first `Error:` line of a stderr, else its last non-empty line.
pub fn stderr_line(stderr: &[u8]) -> String {
    let text = String::from_utf8_lossy(stderr);
    let line = text
        .lines()
        .map(str::trim)
        .find(|l| l.starts_with("Error:"))
        .or_else(|| text.lines().map(str::trim).rfind(|l| !l.is_empty()))
        .unwrap_or("<empty stderr>");
    line.chars().take(400).collect()
}

/// Read the JSON string value of `"key": "..."` in `text`, escapes decoded.
pub fn json_string_field(text: &str, key: &str) -> Option<String> {
    let start = text.find(&format!("\"{key}\": \""))? + key.len() + 5;
    let mut out = String::new();
    let mut chars = text[start..].chars();
    while let Some(c) = chars.next() {
        match c {
            '"' => return Some(out),
            '\\' => match chars.next()? {
                'n' => out.push('\n'),
                't' => out.push('\t'),
                'r' => out.push('\r'),
                'b' => out.push('\u{8}'),
                'f' => out.push('\u{c}'),
                'u' => {
                    let hex: String = chars.by_ref().take(4).collect();
                    out.push(char::from_u32(u32::from_str_radix(&hex, 16).ok()?)?);
                }
                other => out.push(other),
            },
            c => out.push(c),
        }
    }
    None
}

/// Read the JSON number value of `"key": N` in `text` (0 when absent).
pub fn json_usize_field(text: &str, key: &str) -> usize {
    text.find(&format!("\"{key}\": "))
        .map(|at| &text[at + key.len() + 4..])
        .map(|rest| {
            rest.chars()
                .take_while(char::is_ascii_digit)
                .collect::<String>()
        })
        .and_then(|digits| digits.parse().ok())
        .unwrap_or(0)
}

/// `name -> <field>` from a report written one program per line.
pub fn read_pins(report: &str, field: &str) -> BTreeMap<String, String> {
    report
        .lines()
        .filter_map(|line| {
            Some((
                json_string_field(line, "name")?,
                json_string_field(line, field)?,
            ))
        })
        .collect()
}

pub fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

pub fn counts<'a>(rows: impl Iterator<Item = &'a Row>) -> BTreeMap<&'static str, usize> {
    let mut map: BTreeMap<&'static str, usize> = OUTCOMES.iter().map(|o| (*o, 0)).collect();
    for row in rows {
        *map.entry(row.trustcg.outcome).or_default() += 1;
    }
    map
}

fn counts_json(map: &BTreeMap<&'static str, usize>) -> String {
    OUTCOMES
        .iter()
        .map(|o| format!("\"{o}\": {}", map.get(o).copied().unwrap_or(0)))
        .collect::<Vec<_>>()
        .join(", ")
}

/// A cause with its program-specific spellings (backticked names, digits)
/// folded, so programs blocked by one cause group together.
fn cause_key(row: &Row) -> String {
    let mut key = String::new();
    let mut in_tick = false;
    for c in row.trustcg.cause.chars() {
        match c {
            '`' => {
                in_tick = !in_tick;
                key.push_str(if in_tick { "`_" } else { "`" });
            }
            _ if in_tick => {}
            c if c.is_ascii_digit() => {
                if !key.ends_with('#') {
                    key.push('#');
                }
            }
            c => key.push(c),
        }
    }
    format!("{} @ {}: {key}", row.trustcg.outcome, row.trustcg.step)
}

/// In-scope blocking causes, most programs first.
pub fn top_causes(rows: &[Row]) -> Vec<(String, Vec<String>)> {
    let mut groups: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for row in rows
        .iter()
        .filter(|r| r.in_scope && r.trustcg.outcome != "BYTE_EQUAL")
    {
        groups
            .entry(cause_key(row))
            .or_default()
            .push(row.name.clone());
    }
    let mut ranked: Vec<(String, Vec<String>)> = groups.into_iter().collect();
    ranked.sort_by(|a, b| b.1.len().cmp(&a.1.len()).then(a.0.cmp(&b.0)));
    ranked
}

/// The probe as one JSON object, or `null` when no other consumer is on PATH.
fn probe_json(probe: Option<&ConsumerProbe>) -> String {
    let q = |v: &str| format!("\"{}\"", json_escape(v));
    probe.map_or_else(
        || "null".to_owned(),
        |p| {
            format!(
                "{{\"path\": {}, \"version\": {}, \"program\": {}, \"outcome\": {}, \"step\": {}, \
                 \"cause\": {}, \"note\": {}}}",
                q(&p.path),
                q(&p.version),
                q(&p.program),
                q(p.run.outcome),
                q(&p.run.step),
                q(&p.run.cause),
                q(
                    "recorded when minting; a property of the measuring box, never compared \
                   against the pins"
                )
            )
        },
    )
}

pub fn render_json(rows: &[Row], id: &Identity, probe: Option<&ConsumerProbe>) -> String {
    let scoped = counts(rows.iter().filter(|r| r.in_scope));
    let other = counts(rows.iter().filter(|r| !r.in_scope));
    let wrong_exit0 = rows
        .iter()
        .filter(|r| r.in_scope && r.trustcg.exit_zero == Some(true))
        .count();
    let mut s = String::from("{\n");
    let mut field = |k: &str, v: String| s.push_str(&format!(" \"{k}\": {v},\n"));
    let q = |v: &str| format!("\"{}\"", json_escape(v));
    field("schema_version", q(SCHEMA));
    field("driver", q(DRIVER));
    field(
        "c_driver",
        q("clean run (the C lane, measured live by the same run)"),
    );
    field("generated_by", q(GENERATED_BY));
    field("claim", q(CLAIM));
    field("lowered", q("clean-compiler-unvalidated"));
    field("runtime", q("C via cc"));
    field("clean_sha", q(&id.clean_sha));
    field("clean_tree_dirty", id.clean_tree_dirty.to_string());
    field(
        "trust_cg",
        format!(
            "{{\"path\": {}, \"version\": {}, \"blake3\": {}, \"source\": {}}}",
            q(&id.trust_cg_path),
            q(&id.trust_cg_version),
            q(&id.trust_cg_blake3),
            q(&id.trust_cg_source)
        ),
    );
    field("host", q(&id.host));
    field("cc", q(&id.cc));
    field("lean", q(&id.lean));
    field("path_consumer_probe", probe_json(probe));
    field(
        "scope",
        q("p01_hello and every program reports/native-exec-battery.json pins BYTE_EQUAL (the C lane)"),
    );
    field(
        "in_scope_programs",
        rows.iter().filter(|r| r.in_scope).count().to_string(),
    );
    field("summary", format!("{{{}}}", counts_json(&scoped)));
    field("wrong_output_exit0", wrong_exit0.to_string());
    field(
        "summary_out_of_scope",
        format!("{{{}}}", counts_json(&other)),
    );
    let causes: Vec<String> = top_causes(rows)
        .iter()
        .map(|(cause, names)| {
            format!(
                "  {{\"programs\": {}, \"cause\": {}, \"names\": [{}]}}",
                names.len(),
                q(cause),
                names.iter().map(|n| q(n)).collect::<Vec<_>>().join(", ")
            )
        })
        .collect();
    field("top_causes", format!("[\n{}\n ]", causes.join(",\n")));
    s.push_str(" \"programs\": [\n");
    for (i, r) in rows.iter().enumerate() {
        let t = &r.trustcg;
        s.push_str(&format!(
            "  {{\"name\": {}, \"in_scope\": {}, \"outcome\": {}, \"step\": {}, \"cause\": {}, \
             \"exit_zero\": {}, \"rc\": {}, \"lean_rc\": {}, \"c_lane\": {}, \"c_lane_pinned\": {}, \
             \"kernel_tv_certified\": {}, \"bodies_unvalidated\": {}, \"driver_entry\": {}, \
             \"module_digest\": {}}}{}\n",
            q(&r.name),
            r.in_scope,
            q(t.outcome),
            q(&t.step),
            q(&t.cause),
            t.exit_zero.map_or("null".to_owned(), |b| b.to_string()),
            t.rc.map_or("null".to_owned(), |c| c.to_string()),
            r.lean_rc,
            q(r.c_lane),
            q(&r.c_lane_pinned),
            t.kernel_tv_certified,
            t.bodies_unvalidated,
            q(&t.driver_entry),
            q(&t.module_digest),
            if i + 1 == rows.len() { "" } else { "," }
        ));
    }
    s.push_str(" ]\n}\n");
    s
}
