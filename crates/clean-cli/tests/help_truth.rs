// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The help-truth gate: the properties of `--help` that a machine can check.
//!
//! # Why this exists
//!
//! Between 2026-08-27 and 2026-09-01, nine help strings were found contradicting
//! their own code across three alab repos. Two were soundness-adjacent:
//! `clean cert verify --minimal-env` claimed "only `sorry` axiom" while the
//! environment registers three axioms each of which inhabits every type, and
//! `aterm pkg doctor --fix` was named as THE cure for a broken toolchain by a
//! `doctor` that parses no arguments at all.
//!
//! Every one shipped because **nothing reads help text**. Doc claims are gated
//! (`scripts/check_doc_claims.py`); help was the ungated channel.
//!
//! # What is checkable, and what is not
//!
//! "Help matches behaviour" is undecidable, and a gate that pretends otherwise
//! is worse than none. Four properties are checkable, three of them by reading
//! the text alone:
//!
//! * **C1** — every command says something.
//! * **C2** — help is not a restatement of the name.
//! * **C3** — every repo path a help string names, exists.
//! * **C4** — every help string that makes a CAPABILITY CLAIM is backed by a
//!   dated verification in `data/cli_help_claims.json`, citing the file:line
//!   that makes it true.
//!
//! C3 is the strongest of the text checks and would have caught two of the
//! defects fixed this week: the `clean help "kernel verify"` worked example
//! naming a descriptor path that does not exist, printed in two places; and
//! `generate-lean4-baseline` pointing at
//! `crates/clean-kernel/tests/differential/` for a file that lives at
//! `tests/differential/`.
//!
//! # C4, and the hole it closes
//!
//! C1-C3 all pass on a sentence that is well-formed, non-tautological, names
//! only real paths — and is FALSE. `"Get cached .olean files"` on a verb that
//! fetches nothing had all three properties; so did `"Disable GPU acceleration"`
//! where there is no GPU path. **Falsity is not a text property**, so no text
//! check will ever find it. The only thing that finds it is a person reading
//! the handler.
//!
//! C4 does not read the handler. It does the one thing a machine can do about a
//! semantic claim: refuse to let it stand un-cited and un-dated. A lexicon
//! (`CLAIM_PATTERNS` + `TRUST_NOUNS`) picks out the help strings that assert
//! something about the code — "not implemented", "no-op", "no axioms", "only
//! ... trusted", "disables" — and each one must carry an entry binding the
//! sha256 of its exact text to a `file:line` and a date. Edit the sentence and
//! the sha moves, which re-opens the verification; move the code past the cited
//! line and the citation stops resolving; let six months pass and it expires.
//!
//! On the first run over the real surface the lexicon matched 20 of 1075 help
//! strings (1.9%), and verifying those 20 against source found `clean lake
//! upload`'s description asserting "`--dry-run` does not print an upload plan"
//! when the handler prints exactly that — a sentence that had been green under
//! C1, C2 and C3, and which contradicted the SAME command's clap help two
//! screens away.
//!
//! What C4 still cannot catch: a false claim whose wording misses the lexicon,
//! and a verification entry somebody filled in without doing the reading. The
//! first is a calibration question — `c4_lexicon_still_reaches_the_surface`
//! pins the reach so it cannot silently decay to zero. The second is why the
//! entry demands a line number: a citation that does not resolve is caught, and
//! one that resolves to the wrong thing is at least a specific claim someone
//! can check.

use std::collections::BTreeSet;
use std::path::Path;

use clean_cli::__test_support::{all_features, collect_clap_commands};

fn all_commands() -> Vec<(String, clap::Command)> {
    collect_clap_commands()
}

/// The help a user actually reads: `long_about` if present, else `about`.
fn command_help(cmd: &clap::Command) -> Option<String> {
    cmd.get_long_about()
        .or_else(|| cmd.get_about())
        .map(ToString::to_string)
}

// ---------------------------------------------------------------------------
// C1 — every command says something
// ---------------------------------------------------------------------------

/// Commands allowed to carry no help of their own. Empty by intent: adding a
/// silent command should be a decision somebody writes down here.
const C1_EXEMPT: &[&str] = &[];

#[test]
fn c1_every_command_has_help() {
    let mut silent: Vec<String> = Vec::new();
    for (path, cmd) in all_commands() {
        if C1_EXEMPT.contains(&path.as_str()) {
            continue;
        }
        if command_help(&cmd).unwrap_or_default().trim().is_empty() {
            silent.push(path);
        }
    }
    assert!(
        silent.is_empty(),
        "help-truth C1: {} command(s) print no description at all:\n  {}",
        silent.len(),
        silent.join("\n  ")
    );
}

// ---------------------------------------------------------------------------
// C2 — help is not a restatement of the name
// ---------------------------------------------------------------------------

/// Words carrying nothing when they are all the help adds to the name.
const FILLER: &[&str] = &[
    "show",
    "shows",
    "print",
    "prints",
    "display",
    "displays",
    "output",
    "outputs",
    "the",
    "a",
    "an",
    "of",
    "for",
    "to",
    "in",
    "on",
    "with",
    "this",
    "its",
    "and",
    "or",
    "run",
    "runs",
    "do",
    "does",
    "get",
    "gets",
    "set",
    "sets",
    "use",
    "uses",
    "command",
    "subcommand",
    "mode",
    "option",
    "flag",
    "as",
    "it",
    "that",
    "be",
    "is",
    "are",
    "will",
    "can",
];

/// Is `help` merely `name` with filler around it?
///
/// No stemming: `("quiet", "Run quietly")` does NOT fire, because `quietly`
/// and `quiet` are different tokens. Recorded rather than papered over — a
/// stemmer would add false positives worth more than the cases it catches.
fn is_tautological(name: &str, help: &str) -> bool {
    let norm = |s: &str| -> BTreeSet<String> {
        s.split(|c: char| !c.is_alphanumeric())
            .filter(|w| !w.is_empty())
            .map(str::to_lowercase)
            .filter(|w| !FILLER.contains(&w.as_str()))
            .collect()
    };
    let name_words = norm(&name.replace(['-', '_'], " "));
    let help_words = norm(help);
    help_words.is_empty() || help_words.is_subset(&name_words)
}

/// Tautological command descriptions. **Shrink-only, never raise.**
///
/// Compared with `==` rather than `<=` because it is zero: clippy correctly
/// points out that `len() <= 0` can only be `== 0`, and an equality also makes
/// the intent exact — this number is a fact about the tree, not a budget.
const C2_TAUTOLOGY_RATCHET: usize = 0;

#[test]
fn c2_tautology_ratchet() {
    let mut hits: Vec<String> = Vec::new();
    for (path, cmd) in all_commands() {
        let Some(help) = command_help(&cmd) else {
            continue;
        };
        let leaf = path.rsplit(' ').next().unwrap_or(&path);
        if is_tautological(leaf, &help) {
            hits.push(format!("{path}: {:?}", help.lines().next().unwrap_or("")));
        }
    }
    assert!(
        hits.len() == C2_TAUTOLOGY_RATCHET,
        "help-truth C2: {} help string(s) restate the command name and add \
         nothing, ratchet allows {}. Say what it DOES:\n  {}",
        hits.len(),
        C2_TAUTOLOGY_RATCHET,
        hits.join("\n  ")
    );
}

// ---------------------------------------------------------------------------
// C3 — every repo path named in help exists
// ---------------------------------------------------------------------------

/// Top-level directories of this repo. A token starting with one is a path
/// claim even without an extension (`data/graduation/invention-wave`).
const REPO_ROOTS: &[&str] = &[
    "crates/",
    "scripts/",
    "data/",
    "docs/",
    "tests/",
    "designs/",
    "reports/",
    "benchmarks/",
    "specs/",
    "proofs/",
    "demos/",
    "fuzz/",
    "publication/",
];

/// Extensions that mark a token as a file rather than a prose fragment.
///
/// No longer used by [`looks_like_repo_path`] — see the note there. Kept
/// because the tautology and placeholder checks read it, and deleting it would
/// lose the measured list.
#[allow(dead_code)]
const PATH_EXTS: &[&str] = &[
    ".rs", ".py", ".sh", ".json", ".toml", ".md", ".txt", ".lean", ".olean", ".jsonl", ".yml",
    ".yaml", ".tla", ".cfg",
];

/// Placeholder shapes that name nothing in particular.
const C3_PLACEHOLDER_SUBSTRINGS: &[&str] = &["path/to", "my/project", "your/", "example/"];

/// Words that make a NAMED-BUT-ABSENT path honest.
///
/// Two kinds of help legitimately name a file not in the tree: **historical**
/// ("Subsumes the retired `scripts/check_kv_ratchet.py`") and **output**
/// ("writes an untracked `.cargo/vendor.toml`" — the command creates it).
///
/// Keying the exemption on these WORDS rather than on a list of paths is what
/// keeps this a gate. A path allowlist silently covers a typo introduced later
/// at the same path; a sentence that has to say "retired" or "writes" cannot be
/// satisfied by accident, and a real typo — which claims neither — still fails.
const C3_HONEST_ABSENCE_MARKERS: &[&str] = &[
    "retired",
    "replaces",
    "replaced",
    "formerly",
    "port of",
    "superseded",
    "writes",
    "write",
    "creates",
    "create",
    "extracts",
    "emits",
    "generated",
    "produces",
    "remove",
    "removes",
];

/// A token that looks like a repo-relative path we can check.
///
/// The first draft asked only for a `/`, and 31 of its 34 hits were prose:
/// `accept/reject`, `init/build/test`, `PASS/FAIL`, `Poly/ML` — slash-separated
/// ALTERNATIVES. A gate whose output is 91% noise gets skimmed and then
/// ignored, so the discriminator has to be sharp rather than eager.
fn looks_like_repo_path(tok: &str) -> bool {
    if !tok.contains('/')
        || tok.starts_with('/')
        || tok.starts_with("http")
        || tok.starts_with('~')
        || tok.contains("://")
        || tok.contains('*')
        || tok.contains('<')
        || tok.contains('$')
        || tok.len() <= 4
    {
        return false;
    }
    // ONLY tokens rooted at a top-level directory of THIS repo.
    //
    // The extension rule (`*.py`, `*.json`, …) was dropped after measuring: it
    // pulled in 43 paths that belong to the USER, not to this tree —
    // `.lake/build/lib/lean/Mathlib/Logic/Basic.olean` in someone's Mathlib
    // checkout, `Init/SimpLemmas.olean`, `downloads/artifact-manifest.json`.
    // Those are correct help and their absence here means nothing. Requiring a
    // repo root makes every hit a claim about a file this repo either has or
    // does not, which is the only claim this check can actually adjudicate.
    //
    // The cost is stated rather than hidden: a bare `crown-proofs.cake.json`
    // (a real defect, fixed 2026-09-01) has no repo root and would NOT be
    // caught. Precision was chosen over recall because a gate whose output
    // needs triage gets skimmed, and PATH_EXTS is retained below for the
    // `docs/cli` generator check where the root is known.
    REPO_ROOTS.iter().any(|r| tok.starts_with(r))
}

/// Does the sentence containing `tok` explain why the path is absent?
fn absence_is_explained(help: &str, tok: &str) -> bool {
    let Some(at) = help.find(tok) else {
        return false;
    };
    // Sentence bounds, NOT bare '.': a file extension is a period too, so
    // splitting on '.' cut `data/kv_elision_opaque.json data/kv_elision_oat`
    // out of its own sentence and hid the "…the paired stamp runs write" that
    // explains it. Measured — it left six false hits standing.
    let start = help[..at]
        .rfind(". ")
        .map(|i| i + 2)
        .max(help[..at].rfind('\n').map(|i| i + 1))
        .unwrap_or(0);
    let rest = &help[at + tok.len()..];
    let end = at
        + tok.len()
        + rest
            .find(". ")
            .into_iter()
            .chain(rest.find('\n'))
            .min()
            .unwrap_or(rest.len());
    let clause = help[start..end].to_lowercase();
    C3_HONEST_ABSENCE_MARKERS.iter().any(|m| clause.contains(m))
}

/// Every user-facing help string in the tree, as `(where it is, the text)`.
///
/// TWO surfaces, and the distinction matters: the clap tree is what
/// `clean <cmd> --help` prints, and the `FeatureDescriptor` registry is what
/// `clean help <path>` renders AND what `docs/cli/` is generated from. An
/// earlier draft of this gate walked only clap and passed a planted
/// reinstatement of a real defect, because that defect lived in a descriptor.
/// Checking one surface and reporting on "help" would have been the same class
/// of false assurance this gate exists to prevent.
fn all_help_strings() -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = all_commands()
        .into_iter()
        .filter_map(|(path, cmd)| command_help(&cmd).map(|h| (format!("clap {path}"), h)))
        .collect();
    for d in all_features() {
        let where_ = format!("descriptor {}", d.path.join(" "));
        out.push((format!("{where_} (summary)"), d.summary.to_string()));
        out.push((format!("{where_} (description)"), d.description.to_string()));
        for (i, ex) in d.examples.iter().enumerate() {
            // An example is ONE unit: the command and the sentence explaining
            // it. Split apart, a `what` saying "the file `x` a previous run
            // emitted" could not exempt the `x` appearing in `cmd`, and C3
            // would demand that every example argument already exist in the
            // repo — which is false for every command that consumes its own
            // output.
            out.push((
                format!("{where_} (example {i})"),
                format!("{} — {}", ex.cmd, ex.what),
            ));
        }
    }
    out
}

/// Repo-rooted paths named in help that are not in the tree. **ZERO.**
///
/// It was 14 when this gate landed and is 0 now, drained the same day. Not one
/// was a typo, and the drain was not a deletion: each was a file the command
/// CREATES or CONSUMES from a prior run, and the fix was to make the sentence
/// say which — "the summary a real corpus stamp run writes", "the full record
/// and shard a graduation run writes", "the retired
/// `scripts/check_kv_ratchet.py`". Every one of those edits tells a reader
/// something they did not know: where the input comes from. That is the point
/// of keying the exemption on the sentence — satisfying the gate and improving
/// the help are the same act.
///
/// Two calibration bugs surfaced during the drain, both measured:
/// splitting the example's `cmd` from its `what` meant an explanation could
/// never cover the path it explained (14 -> 12 when joined), and splitting
/// clauses on a bare `.` cut `data/kv_elision_opaque.json` out of its own
/// sentence, because a file extension is a period too (12 -> 6 when fixed).
///
/// **Never raise this.** A help string naming a repo path that does not exist
/// is either a typo or a file the command makes; the first is a defect and the
/// second takes one word to say.
const C3_ABSENT_PATH_RATCHET: usize = 0;

#[test]
fn c3_paths_named_in_help_exist() {
    let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("crates/clean-cli has a workspace root two levels up");

    let mut missing: Vec<String> = Vec::new();
    for (path, help) in all_help_strings() {
        for raw in help.split(|c: char| c.is_whitespace() || c == '`' || c == '"') {
            let tok = raw.trim_matches(|c: char| {
                !c.is_alphanumeric() && c != '/' && c != '.' && c != '-' && c != '_'
            });
            if !looks_like_repo_path(tok)
                || C3_PLACEHOLDER_SUBSTRINGS.iter().any(|e| tok.contains(e))
                || repo_root.join(tok).exists()
                || absence_is_explained(&help, tok)
            {
                continue;
            }
            missing.push(format!("{path}: `{tok}`"));
        }
    }
    assert!(
        missing.len() == C3_ABSENT_PATH_RATCHET,
        "help-truth C3: {} repo-rooted path(s) named in help do not exist, \
         ratchet allows {}. A reader who follows one gets nothing, and cannot \
         tell whether they typed it wrong or the tool is lying. If the file is \
         one this command CREATES, say so in the same sentence (\"writes\", \
         \"emits\") and this check will stand down:\n  {}",
        missing.len(),
        C3_ABSENT_PATH_RATCHET,
        missing.join("\n  ")
    );
}

// ---------------------------------------------------------------------------
// The gate's own arms — a check that cannot fail is not a check
// ---------------------------------------------------------------------------

#[test]
fn tautology_detector_recognises_the_real_examples() {
    assert!(is_tautological("verbose", "Show verbose output."));
    assert!(is_tautological("json", "JSON output"));
    assert!(is_tautological("status", "Show the status"));
    // ...and stays quiet on help that says something.
    assert!(!is_tautological(
        "verbose",
        "Also print the parsed surface AST, the elaborated kernel term, and timing."
    ));
    assert!(!is_tautological(
        "minimal-env",
        "Verify against the smallest environment, NOT an axiom-free one."
    ));
}

#[test]
fn path_shape_detector_is_neither_blind_nor_greedy() {
    assert!(looks_like_repo_path("tests/differential/expressions.txt"));
    assert!(looks_like_repo_path("data/graduation/invention-wave"));
    assert!(looks_like_repo_path("scripts/check_kv_ratchet.py"));
    // Not repo paths.
    assert!(!looks_like_repo_path("https://example.invalid/x"));
    assert!(!looks_like_repo_path("/absolute/path"));
    assert!(!looks_like_repo_path("~/.config/thing"));
    assert!(!looks_like_repo_path("a/b"));
    assert!(!looks_like_repo_path("glob/*.rs"));
    // Prose alternatives, which the first draft counted as paths.
    assert!(!looks_like_repo_path("accept/reject"));
    assert!(!looks_like_repo_path("init/build/test"));
    assert!(!looks_like_repo_path("Poly/ML"));
}

#[test]
fn absence_exemption_reads_the_sentence_not_a_path_list() {
    assert!(absence_is_explained(
        "Subsumes the retired `scripts/check_kv_ratchet.py`.",
        "scripts/check_kv_ratchet.py"
    ));
    assert!(absence_is_explained(
        "writes an untracked `.cargo/vendor.toml` source-replacement config",
        ".cargo/vendor.toml"
    ));
    // A bare mention of an absent path is NOT exempt — the shape of every real
    // defect this check exists to catch.
    assert!(!absence_is_explained(
        "Reads the corpus at crates/clean-kernel/tests/differential/expressions.txt",
        "crates/clean-kernel/tests/differential/expressions.txt"
    ));
    // A marker in a DIFFERENT sentence must not cover this one.
    assert!(!absence_is_explained(
        "The old flow is retired. Reads scripts/nope.py for input",
        "scripts/nope.py"
    ));
}

// ---------------------------------------------------------------------------
// C4 — capability claims must be verified, dated, and bound to their text
// ---------------------------------------------------------------------------

/// Patterns that mark a help string as making a CAPABILITY CLAIM about the
/// code — the class that produced every false help string found this week.
///
/// Sized against the real surface, not proposed: a first draft using bare
/// `only` / `no X` / `never` / `without` flagged 68 / 35 / 32 / 38 strings, because
/// `only` in this tree almost always scopes the flag's own selection ("Only
/// load modules, skip type-checking") — honest, and not a capability claim.
/// Requiring a TRUST NOUN in the same clause takes that to a handful while
/// keeping the one hit that mattered: `--minimal-env`'s "only `sorry` axiom",
/// which was false in a proof-certificate verifier.
const CLAIM_PATTERNS: &[(&str, &[&str])] = &[
    (
        "A/not-implemented",
        &["not implemented", "not yet implemented"],
    ),
    (
        "B/stub",
        &["unimplemented", "no-op", "is a stub", "stubbed"],
    ),
    (
        "D/does-nothing",
        &[
            "does nothing",
            "fetches nothing",
            "no side-effect",
            "no network",
        ],
    ),
    (
        "E/inert",
        &[
            "advisory",
            "silently ignored",
            "is ignored",
            "has no effect",
            "not wired",
        ],
    ),
    (
        "H/minimal",
        &["minimal environment", "minimal env", "minimal prelude"],
    ),
    ("I/no-trust", &["no axioms", "no assumptions", "no trust"]),
    ("J/disable", &["disable", "disabling", "turns off"]),
];

/// Trust nouns: `only`/`without` becomes a capability claim when one is near.
const TRUST_NOUNS: &[&str] = &[
    "axiom",
    "sorry",
    "trusted",
    "assumption",
    "unsafe",
    "bypass",
    "tcb",
];

/// The claim's identity is its exact text: any edit re-opens verification.
fn help_sha256(help: &str) -> String {
    use sha2::Digest as _;
    sha2::Sha256::digest(help.as_bytes())
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// Which patterns a help string trips, if any.
fn claim_triggers(help: &str) -> Vec<&'static str> {
    let lower = help.to_lowercase();
    let mut fired: Vec<&'static str> = CLAIM_PATTERNS
        .iter()
        .filter(|(_, needles)| needles.iter().any(|n| lower.contains(n)))
        .map(|(id, _)| *id)
        .collect();
    // F/G: an exclusivity word within 60 bytes of a trust noun.
    //
    // Positions are COMPARED, never sliced: an earlier draft cut a window with
    // `lower[lo..hi]` and panicked on `start byte index 329 is not a char
    // boundary; it is inside '→'`. Help text in this tree is full of arrows and
    // typographic dashes.
    let positions = |needle: &str| -> Vec<usize> {
        let mut out = Vec::new();
        let mut from = 0;
        while let Some(at) = lower[from..].find(needle) {
            out.push(from + at);
            from += at + needle.len();
        }
        out
    };
    let noun_at: Vec<usize> = TRUST_NOUNS.iter().flat_map(|n| positions(n)).collect();
    'outer: for kw in ["only", "without"] {
        for i in positions(kw) {
            if noun_at.iter().any(|j| i.abs_diff(*j) <= 60) {
                fired.push("F/exclusive-trust");
                break 'outer;
            }
        }
    }
    fired.sort_unstable();
    fired.dedup();
    fired
}

/// Where the verified claims live.
const CLAIMS_FILE: &str = "data/cli_help_claims.json";

/// A claim goes stale on its own. Six months is long enough that verifying is
/// not a treadmill, short enough that a claim cannot outlive the code by a
/// release cycle.
const MAX_AGE_DAYS: i64 = 180;

/// `CLEAN_C4_DUMP=<path>` writes today's flagged set as a skeleton claims file.
/// It is a **starting point for verification, never a verdict** — every entry
/// it emits has an empty `evidence` and `statement`, which C4 refuses. The
/// work is filling those in by reading the handler.
#[test]
fn c4_dump_skeleton() {
    let Ok(out) = std::env::var("CLEAN_C4_DUMP") else {
        return;
    };
    let rows: Vec<_> = flagged_claims()
        .into_iter()
        .map(|(id, sha, triggers, _)| {
            serde_json::json!({
                "id": id, "help_sha256": sha, "triggers": triggers,
                "statement": "", "evidence": "", "anchor": "", "verified": "",
            })
        })
        .collect();
    std::fs::write(out, serde_json::to_string_pretty(&rows).expect("json")).expect("write");
}

/// Every help string that trips the lexicon, with its content hash.
fn flagged_claims() -> Vec<(String, String, Vec<&'static str>, String)> {
    all_help_strings()
        .into_iter()
        .filter_map(|(id, help)| {
            let t = claim_triggers(&help);
            (!t.is_empty()).then(|| (id, help_sha256(&help), t, help))
        })
        .collect()
}

/// Days since 1970-01-01 for a `YYYY-MM-DD` string (Hinnant's `days_from_civil`).
fn civil_days(date: &str) -> Option<i64> {
    let mut it = date.split('-');
    let y: i64 = it.next()?.parse().ok()?;
    let m: i64 = it.next()?.parse().ok()?;
    let d: i64 = it.next()?.parse().ok()?;
    if it.next().is_some() || !(1..=12).contains(&m) || !(1..=31).contains(&d) {
        return None;
    }
    let y = if m <= 2 { y - 1 } else { y };
    let era = if y >= 0 { y } else { y - 399 } / 400;
    let yoe = y - era * 400;
    let doy = (153 * (if m > 2 { m - 3 } else { m + 9 }) + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    Some(era * 146_097 + doe - 719_468)
}

fn today_days() -> i64 {
    let secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    (secs / 86_400) as i64
}

fn repo_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("crates/clean-cli has a workspace root two levels up")
}

fn load_claims(root: &Path) -> serde_json::Value {
    let raw = std::fs::read_to_string(root.join(CLAIMS_FILE))
        .unwrap_or_else(|e| panic!("help-truth C4: cannot read {CLAIMS_FILE}: {e}"));
    serde_json::from_str(&raw).unwrap_or_else(|e| panic!("{CLAIMS_FILE} is not JSON: {e}"))
}

/// The five refusals, as data, so the arms below can name them.
fn c4_violations(
    root: &Path,
    claims: &serde_json::Value,
    flagged: &[(String, String, Vec<&'static str>, String)],
) -> Vec<String> {
    let mut bad: Vec<String> = Vec::new();
    let rows = claims.as_array().cloned().unwrap_or_default();
    let by_id: std::collections::HashMap<&str, &serde_json::Value> = rows
        .iter()
        .filter_map(|r| r.get("id")?.as_str().map(|i| (i, r)))
        .collect();

    for (id, sha, triggers, _) in flagged {
        // R1 — a capability claim nobody has verified.
        let Some(row) = by_id.get(id.as_str()) else {
            bad.push(format!(
                "R1 UNVERIFIED: `{id}` makes a capability claim {triggers:?} with no \
                 entry in {CLAIMS_FILE}. Read the handler, then add one."
            ));
            continue;
        };
        // R2 — the text moved, so the verification no longer covers it.
        let recorded = row
            .get("help_sha256")
            .and_then(|v| v.as_str())
            .unwrap_or("");
        if recorded != sha {
            bad.push(format!(
                "R2 TEXT CHANGED: `{id}` was verified at help_sha256 {} but reads {} \
                 today. Re-read the handler, then update the sha and `verified`.",
                &recorded[..recorded.len().min(12)],
                &sha[..12]
            ));
            continue;
        }
        // R3a — the statement must say something.
        let stmt = row.get("statement").and_then(|v| v.as_str()).unwrap_or("");
        if stmt.trim().is_empty() {
            bad.push(format!("R3 NO STATEMENT: `{id}` has an empty `statement`."));
        }
        // R4 — the citation must land on a line that exists AND still say what
        // it said. A bare line number is nearly worthless as evidence: any edit
        // above it shifts the target silently, so the citation would keep
        // "resolving" while pointing somewhere else entirely. `anchor` is a
        // substring that must appear on the cited line, which turns drift into
        // a failure instead of a lie.
        let ev = row.get("evidence").and_then(|v| v.as_str()).unwrap_or("");
        let anchor = row.get("anchor").and_then(|v| v.as_str()).unwrap_or("");
        match ev.rsplit_once(':') {
            None => bad.push(format!(
                "R4 NO EVIDENCE: `{id}` cites `{ev}`, which is not `path:line`."
            )),
            Some((f, n)) => {
                let line: usize = n.parse().unwrap_or(0);
                let text = std::fs::read_to_string(root.join(f)).unwrap_or_default();
                let at = line.checked_sub(1).and_then(|i| text.lines().nth(i));
                match at {
                    None => bad.push(format!(
                        "R4 EVIDENCE DOES NOT RESOLVE: `{id}` cites `{ev}`; that file \
                         has {} line(s). The code moved — re-verify.",
                        text.lines().count()
                    )),
                    Some(_) if anchor.trim().is_empty() => bad.push(format!(
                        "R4 NO ANCHOR: `{id}` cites `{ev}` with no `anchor`. A line \
                         number alone drifts on any edit above it."
                    )),
                    Some(l) if !l.contains(anchor) => bad.push(format!(
                        "R4 ANCHOR MOVED: `{id}` cites `{ev}` for anchor {anchor:?}, \
                         but that line now reads {:?}. Find where the code went and \
                         re-verify — do not just bump the number.",
                        l.trim()
                    )),
                    Some(_) => {}
                }
            }
        }
        // R5 — a verification has a shelf life.
        let when = row.get("verified").and_then(|v| v.as_str()).unwrap_or("");
        match civil_days(when) {
            None => bad.push(format!(
                "R5 NO DATE: `{id}` has `verified: {when:?}`, not a YYYY-MM-DD date."
            )),
            Some(d) => {
                let age = today_days() - d;
                if age > MAX_AGE_DAYS {
                    bad.push(format!(
                        "R5 STALE: `{id}` was last verified {when} ({age} days ago, \
                         limit {MAX_AGE_DAYS}). Re-read the handler and re-date it."
                    ));
                }
            }
        }
    }

    // R3b — an entry for a claim that is no longer made is not evidence of
    // anything, and left in place it makes the file look more complete than it
    // is. The lexicon is the authority on what needs verifying.
    let live: std::collections::HashSet<&str> =
        flagged.iter().map(|(i, _, _, _)| i.as_str()).collect();
    for row in &rows {
        let id = row.get("id").and_then(|v| v.as_str()).unwrap_or("");
        if !live.contains(id) {
            bad.push(format!(
                "R3 ORPHAN: {CLAIMS_FILE} verifies `{id}`, which no longer makes a \
                 capability claim (renamed, reworded, or deleted). Drop the entry."
            ));
        }
    }
    bad
}

/// C4 — a help string that CLAIMS A CAPABILITY must have been checked against
/// the code, by a named line, on a date.
///
/// C1/C2/C3 all pass on a sentence that is well-formed, non-tautological, names
/// only real paths — and is false. `"Get cached .olean files"` on a verb that
/// fetches nothing had all three properties. Falsity is not a text property, so
/// no text check finds it; the only thing that does is a person reading the
/// handler. C4 does not read the handler — it refuses to let the claim stand
/// without a citation that someone did, and expires that citation.
#[test]
fn c4_capability_claims_are_verified() {
    let root = repo_root();
    let bad = c4_violations(root, &load_claims(root), &flagged_claims());
    assert!(
        bad.is_empty(),
        "help-truth C4: {} capability claim(s) in `clean --help` are not backed by a \
         current verification in {CLAIMS_FILE}:\n  {}",
        bad.len(),
        bad.join("\n  ")
    );
}

/// The lexicon is the gate's reach: if it silently stopped matching, C4 would
/// pass by having nothing to check.
#[test]
fn c4_lexicon_still_reaches_the_surface() {
    let flagged = flagged_claims();
    assert!(
        flagged.len() >= 15,
        "help-truth C4: the claim lexicon matches only {} help string(s). It matched \
         20 when this gate landed. A lexicon that stops matching turns C4 into a \
         no-op that reports success — check CLAIM_PATTERNS/TRUST_NOUNS before \
         lowering this floor.",
        flagged.len()
    );
}

/// Each refusal, demonstrated. A gate nobody has seen fail is `exit 0`
/// (docs/GATE_REGISTRY.md).
#[test]
fn c4_each_refusal_fires() {
    let root = repo_root();
    let flagged = flagged_claims();
    let real = load_claims(root);
    assert!(
        c4_violations(root, &real, &flagged).is_empty(),
        "the committed claims file must be clean before the arms mean anything"
    );

    let (id, sha, _, _) = flagged
        .first()
        .expect("the lexicon matches something")
        .clone();
    let row = |ev: &str, when: &str, stmt: &str, sha: &str| {
        serde_json::json!([{
            "id": id, "help_sha256": sha, "statement": stmt,
            "evidence": ev, "verified": when, "anchor": "Copyright",
        }])
    };
    let today = "2026-09-01";
    let good = "crates/clean-cli/tests/help_truth.rs:1";
    let fires = |v: serde_json::Value, tag: &str| {
        let out = c4_violations(root, &v, &flagged);
        assert!(
            out.iter().any(|m| m.starts_with(tag)),
            "expected {tag} to fire, got {out:?}"
        );
    };

    fires(serde_json::json!([]), "R1");
    fires(row(good, today, "s", &"0".repeat(64)), "R2");
    fires(row(good, today, "   ", &sha), "R3 NO STATEMENT");
    fires(
        row(
            "crates/clean-cli/tests/help_truth.rs:999999",
            today,
            "s",
            &sha,
        ),
        "R4",
    );
    fires(row("does/not/exist.rs:1", today, "s", &sha), "R4");
    fires(row("no-colon-here", today, "s", &sha), "R4 NO EVIDENCE");
    fires(row(good, "not-a-date", "s", &sha), "R5 NO DATE");
    fires(row(good, "2000-01-01", "s", &sha), "R5 STALE");

    // R4 anchor: present line, wrong content — the drift case a bare line
    // number cannot see. Line 2 of this file is the Author line, not Copyright.
    fires(
        row("crates/clean-cli/tests/help_truth.rs:2", today, "s", &sha),
        "R4 ANCHOR MOVED",
    );
    fires(
        serde_json::json!([{
            "id": id, "help_sha256": sha, "statement": "s",
            "evidence": good, "verified": today, "anchor": "",
        }]),
        "R4 NO ANCHOR",
    );

    let mut orphan = real.clone();
    if let Some(arr) = orphan.as_array_mut() {
        arr.push(serde_json::json!({
            "id": "descriptor no such command (summary)", "help_sha256": sha,
            "statement": "s", "evidence": good, "verified": today,
        }));
    }
    fires(orphan, "R3 ORPHAN");
}

/// The date arithmetic, against hand-computed reference points.
#[test]
fn civil_days_matches_known_dates() {
    assert_eq!(civil_days("1970-01-01"), Some(0));
    assert_eq!(civil_days("1969-12-31"), Some(-1));
    assert_eq!(civil_days("2000-03-01"), Some(11017));
    assert_eq!(civil_days("2026-09-01"), Some(20697));
    // A leap day must not be silently off by one against the day after it.
    assert_eq!(
        civil_days("2024-03-01").unwrap() - civil_days("2024-02-29").unwrap(),
        1
    );
    assert_eq!(civil_days("2026-13-01"), None, "month out of range");
    assert_eq!(civil_days("2026-09"), None, "not a full date");
    assert_eq!(civil_days("yesterday"), None);
}

// ---------------------------------------------------------------------------
// Re-check level wording on the `olean` surface
// ---------------------------------------------------------------------------

/// Phrases that name a STRONGER re-check than the local assumed-environment
/// check (`typecheck_constants_full`) that `clean olean verify-batch
/// --full-validation` and `import-reverify-metric` actually run.
///
/// The recheck-closure verification (round 23) found four of these still
/// printed by `--help` after the descriptors had been corrected: the clap doc
/// comments are a separate surface. Assembled at run time so this file does
/// not match its own needles.
fn overclaiming_recheck_phrases() -> Vec<String> {
    vec![
        ["re-verified", " fraction"].concat(),
        ["dep-closure", " re-verified"].concat(),
        ["full re-", "verify"].concat(),
        ["full-Init", " re-check"].concat(),
        ["re-verification", " ratchet"].concat(),
        ["successful full", " re-"].concat(),
    ]
}

/// Every `clean olean …` command's full rendered `--help` — about, long
/// about and every argument's help — says nothing stronger than the level it
/// runs.
#[test]
fn olean_help_does_not_describe_the_local_check_as_a_closure_recheck() {
    let mut hits = Vec::new();
    let mut seen = 0usize;
    for (path, cmd) in all_commands() {
        if !(path == "olean" || path.starts_with("olean ")) {
            continue;
        }
        seen += 1;
        let rendered = cmd.clone().render_long_help().to_string();
        for needle in overclaiming_recheck_phrases() {
            if rendered.contains(&needle) {
                hits.push(format!("clean {path} --help: {needle:?}"));
            }
        }
    }
    assert!(
        seen >= 3,
        "the olean surface must be walked (saw {seen} commands)"
    );
    assert!(
        hits.is_empty(),
        "olean help overclaims its re-check level: {hits:#?}"
    );
}
