// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Silent-tactic census + ratchet.**
//!
//! ## The defect class this makes countable
//!
//! A tactic Clean does not support is supposed to fail LOUDLY —
//! `TacticFailed(UnknownTactic("foo"))`. Measured on `origin/main` at
//! 2026-08-07, **27 of 374 probes failed with no diagnostic at all**: the
//! declaration degraded to a synthetic sorry and the only thing the user ever
//! saw was `declaration uses synthetic sorry`, with *nothing anywhere naming
//! the construct that did nothing*.
//!
//! The mechanism was a two-stage swallow. Whenever a tactic's ARGUMENT grammar
//! failed (`set x := e`, `conv_rhs => …`, `conv in p => …`, `simp [*]`,
//! `simp (config := …)`, `cases … with | _ =>`, `rcases … with -`, `module`,
//! `on_goal`, `let'`, `letI`, `guard_target`, `specialize h`, `∎`, or a bare
//! `rw`/`unfold`/`revert`/`clear`/`subst`/`rename_i`), `by_body` recovered the
//! whole block to `SurfaceExpr::SyntheticSorry` and *deferred* a recovery
//! diagnostic — and then `clean check` called `parse_file_with_tactics`, whose
//! return type has no room for recovery diagnostics, so the diagnostic was
//! dropped on the floor.
//!
//! The consequence, recorded as RC-Q in
//! `docs/plans/TACTICS_TO_100_2026-07-29.md`: **any coverage script keyed on
//! `UnknownTactic`/`TacticFailed` under-reports the real gap**, and nobody knew
//! by how much, because the class was unmeasurable by construction.
//!
//! This census measures it. `data/silent_tactic_probes.json` is the
//! denominator — one minimal `by <tactic>` declaration per (token, invocation
//! shape) — and `scripts/check_silent_tactic_ratchet.py` gates the counts
//! fail-closed against `data/silent_tactic_ratchet.json`.
//!
//! ## Verdicts
//!
//! | verdict | meaning |
//! |---|---|
//! | `pass` | every declaration elaborated and registered with no sorry |
//! | `loud` | failed, and some diagnostic NAMES the tactic under test |
//! | `unnamed` | failed with a diagnostic, but none names the tactic |
//! | `silent` | failed with **no diagnostic at all** — the class being ratcheted |
//!
//! `silent` is the only verdict a user cannot act on, and the ratchet baseline
//! for it is **0**: a probe that reaches `silent` fails the gate outright.
//! Probes marked `intentional_sorry` (`sorry`, `admit`) are excluded from the
//! count — writing `sorry` and being told the declaration uses a sorry IS the
//! diagnostic.
//!
//! ## Regenerating
//!
//! ```sh
//! CLEAN_SILENT_CENSUS_UPDATE=1 \
//!   cargo test --offline -p clean-elab --test silent_tactic_census
//! ```
//!
//! Everything runs on the builtin prelude and in-process, so the census needs
//! no `.olean` corpus and no release binary. That is sound for this class:
//! the silence is a PARSER-recovery property, and §8 trap 3 of the plan
//! forbids builtin-prelude numbers only for *parity* claims, which this is not.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use clean_elab::{
    elaborate_decl_and_register_with_warning, preprocess_decl_with_context, FileContext,
    RegistrationWarningKind,
};
use clean_kernel::env::Environment;

const PROBES_REL: &str = "data/silent_tactic_probes.json";
const CENSUS_REL: &str = "data/silent_tactic_census.json";
const RATCHET_REL: &str = "data/silent_tactic_ratchet.json";
const UPDATE_ENV_VAR: &str = "CLEAN_SILENT_CENSUS_UPDATE";

fn repo_root() -> PathBuf {
    // crates/clean-elab -> repo root
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("crate manifest dir has a grandparent")
        .to_path_buf()
}

fn read_json(path: &Path) -> serde_json::Value {
    let text = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("cannot parse {} as JSON: {e}", path.display()))
}

/// Does `haystack` name `token` as a standalone word?
///
/// Deliberately strict about boundaries: `simp` must not be credited by a
/// message that merely contains `simp_all`, and `rw` must not be credited by
/// `rewrite`. Tactic spellings carry `?`, `!` and `'`, so those count as part
/// of the word.
fn names_token(haystack: &str, token: &str) -> bool {
    fn word_char(c: char) -> bool {
        c.is_alphanumeric() || c == '_' || c == '?' || c == '!' || c == '\''
    }
    if token.is_empty() {
        return false;
    }
    let mut from = 0usize;
    while let Some(rel) = haystack[from..].find(token) {
        let start = from + rel;
        let end = start + token.len();
        let before_ok = haystack[..start]
            .chars()
            .next_back()
            .is_none_or(|c| !word_char(c));
        let after_ok = haystack[end..].chars().next().is_none_or(|c| !word_char(c));
        if before_ok && after_ok {
            return true;
        }
        from = end.max(start + 1);
        if from >= haystack.len() {
            break;
        }
    }
    false
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Pass,
    Loud,
    Unnamed,
    Silent,
}

impl Verdict {
    fn as_str(self) -> &'static str {
        match self {
            Verdict::Pass => "pass",
            Verdict::Loud => "loud",
            Verdict::Unnamed => "unnamed",
            Verdict::Silent => "silent",
        }
    }
}

struct ProbeOutcome {
    verdict: Verdict,
    /// First diagnostic observed, truncated — recorded so the artifact shows
    /// WHY a row is where it is, not just that it is there.
    detail: String,
}

/// Drive the same pipeline `clean check` drives, on the builtin prelude.
fn run_probe(source: &str, token: &str) -> ProbeOutcome {
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let mut messages: Vec<String> = Vec::new();

    let report = match clean_parser::parse_file_with_tactics_diagnostics(source, &patterns) {
        Ok(report) => report,
        Err(err) => {
            // A hard parse failure is loud by construction; classify by whether
            // the message names the tactic.
            let msg = format!("parse error: {err}");
            let verdict = if names_token(&msg, token) {
                Verdict::Loud
            } else {
                Verdict::Unnamed
            };
            return ProbeOutcome {
                verdict,
                detail: truncate(&msg),
            };
        }
    };
    for diag in &report.diagnostics {
        messages.push(match &diag.tactic {
            Some(tac) => format!("parser recovery [tactic `{tac}`]: {}", diag.message),
            None => format!("parser recovery [{}]: {}", diag.construct, diag.message),
        });
    }

    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let mut sorried = false;
    for decl in &report.decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        match elaborate_decl_and_register_with_warning(&mut env, &processed) {
            Ok(registered) => {
                if matches!(
                    registered.warning.as_ref().map(|w| &w.kind),
                    Some(RegistrationWarningKind::SyntheticSorry)
                        | Some(RegistrationWarningKind::ExplicitSorry)
                ) {
                    sorried = true;
                }
            }
            // `{err:?}`, not `{err}`: this is byte-for-byte the diagnostic
            // `clean check` puts in its JSON report (`cmd_core.rs`:
            // `format!("elaboration error: {e:?}")`). The Display form drops
            // the payload, so `TacticFailed(UnknownTactic("bv_omega"))` would
            // be scored as not naming its tactic when the user in fact sees the
            // name. The census must grade the string the user sees.
            Err(err) => messages.push(format!("elaboration error: {err:?}")),
        }
    }

    if messages.is_empty() && !sorried {
        return ProbeOutcome {
            verdict: Verdict::Pass,
            detail: String::new(),
        };
    }
    let joined = messages.join(" || ");
    let verdict = if messages.is_empty() {
        Verdict::Silent
    } else if names_token(&joined, token) {
        Verdict::Loud
    } else {
        Verdict::Unnamed
    };
    ProbeOutcome {
        verdict,
        detail: truncate(if joined.is_empty() {
            "(no diagnostic; declaration degraded to a sorry)"
        } else {
            &joined
        }),
    }
}

fn truncate(s: &str) -> String {
    let s = s.replace('\n', " ");
    if s.chars().count() > 240 {
        s.chars().take(240).collect::<String>() + "…"
    } else {
        s
    }
}

/// Run the whole corpus and build the census artifact value.
fn census() -> serde_json::Value {
    let root = repo_root();
    let probes = read_json(&root.join(PROBES_REL));
    let probes = probes["probes"]
        .as_array()
        .expect("probes corpus has a `probes` array");

    let mut rows = Vec::new();
    let (mut n_pass, mut n_loud, mut n_unnamed, mut n_silent, mut n_intentional) = (0, 0, 0, 0, 0);

    for probe in probes {
        let token = probe["token"].as_str().expect("probe.token");
        let source = probe["source_text"].as_str().expect("probe.source_text");
        let intentional = probe["intentional_sorry"].as_bool().unwrap_or(false);
        let outcome = run_probe(source, token);
        match outcome.verdict {
            Verdict::Pass => n_pass += 1,
            Verdict::Loud => n_loud += 1,
            Verdict::Unnamed => n_unnamed += 1,
            Verdict::Silent => {
                if intentional {
                    n_intentional += 1;
                } else {
                    n_silent += 1;
                }
            }
        }
        rows.push(serde_json::json!({
            "token": token,
            "label": probe["label"],
            "kind": probe["kind"],
            "tactic": probe["tactic_text"],
            "verdict": outcome.verdict.as_str(),
            "intentional_sorry": intentional,
            "detail": outcome.detail,
        }));
    }

    let silent_tokens: BTreeSet<String> = rows
        .iter()
        .filter(|r| r["verdict"] == "silent" && r["intentional_sorry"] == false)
        .map(|r| r["token"].as_str().unwrap_or_default().to_owned())
        .collect();
    let unnamed_tokens: BTreeSet<String> = rows
        .iter()
        .filter(|r| r["verdict"] == "unnamed")
        .map(|r| r["token"].as_str().unwrap_or_default().to_owned())
        .collect();

    serde_json::json!({
        "schema_version": "clean-silent-tactic-census-v1",
        "generated_by": "cargo test --offline -p clean-elab --test silent_tactic_census (CLEAN_SILENT_CENSUS_UPDATE=1)",
        "prelude": "builtin",
        "totals": {
            "probes": rows.len(),
            "pass": n_pass,
            "loud": n_loud,
            "unnamed": n_unnamed,
            "silent": n_silent,
            "intentional_sorry": n_intentional,
        },
        "silent_tokens": silent_tokens.iter().collect::<Vec<_>>(),
        "unnamed_tokens": unnamed_tokens.iter().collect::<Vec<_>>(),
        "rows": rows,
    })
}

/// The census artifact is regenerated and compared; with the update env var set
/// it is rewritten instead.
#[test]
fn silent_tactic_census_is_current_and_ratcheted() {
    let root = repo_root();
    let value = census();
    let rendered = serde_json::to_string_pretty(&value).expect("serialize census") + "\n";

    if std::env::var(UPDATE_ENV_VAR).is_ok() {
        std::fs::write(root.join(CENSUS_REL), &rendered).expect("write census");
        eprintln!("UPDATED {CENSUS_REL}: {}", value["totals"]);
        return;
    }

    let recorded = read_json(&root.join(CENSUS_REL));
    // The DENOMINATOR is asserted exactly: the artifact must still measure every
    // probe in the corpus, so the class cannot be "fixed" by dropping probes.
    assert_eq!(
        recorded["totals"]["probes"], value["totals"]["probes"],
        "silent-tactic census covers {} probes but the corpus declares {}. \
         Regenerate with {UPDATE_ENV_VAR}=1 cargo test --offline --release \
         -p clean-elab --test silent_tactic_census.",
        recorded["totals"]["probes"], value["totals"]["probes"]
    );
    // `pass`/`loud` are deliberately NOT asserted exactly. They move whenever any
    // tactic gets better, and an unrelated improvement must not break an
    // unrelated agent's build. Only the two ratcheted dimensions are enforced,
    // and only in the fail-closed direction.
    let ratchet = read_json(&root.join(RATCHET_REL));
    let base_silent = ratchet["baseline_silent"]
        .as_u64()
        .expect("baseline_silent");
    let base_unnamed = ratchet["baseline_unnamed"]
        .as_u64()
        .expect("baseline_unnamed");
    let live_silent = value["totals"]["silent"].as_u64().expect("totals.silent");
    let live_unnamed = value["totals"]["unnamed"].as_u64().expect("totals.unnamed");
    assert!(
        live_silent <= base_silent,
        "SILENT tactic failures rose {base_silent} -> {live_silent}. A tactic that \
         dispatches nothing must emit a diagnostic NAMING itself; a silent synthetic \
         sorry is a gate failure, not a skip. Silent tokens: {}",
        value["silent_tokens"]
    );
    assert!(
        live_unnamed <= base_unnamed,
        "tactic failures with no diagnostic naming the tactic rose \
         {base_unnamed} -> {live_unnamed}. Unnamed tokens: {}",
        value["unnamed_tokens"]
    );
    if live_silent < base_silent || live_unnamed < base_unnamed {
        eprintln!(
            "PROGRESS: silent {base_silent} -> {live_silent}, unnamed \
             {base_unnamed} -> {live_unnamed}. Regenerate the census \
             ({UPDATE_ENV_VAR}=1) and run \
             `scripts/check_silent_tactic_ratchet.py --update` to lock it in."
        );
    }
}

/// The two constructs whose parser/elaborator disagreement this census found
/// and closed. Both were SILENT before the fix: `expect_ident` rejected the
/// `_`, the whole `by` block recovered to a synthetic sorry, and the
/// elaborator's `alts.iter().find(|a| a.name == "_")` branch was dead code.
#[test]
fn wildcard_case_alternative_parses_and_closes() {
    for source in [
        "theorem w (b : Bool) : b = b := by\n  cases b with\n  | _ => rfl\n",
        "theorem w (n : Nat) : n = n := by\n  induction n with\n  | _ => rfl\n",
        "theorem w (b : Bool) : b = b := by\n  cases b with\n  | true => rfl\n  | _ => rfl\n",
        "theorem w (n : Nat) : n + 0 = n := by\n  induction n with\n  | zero => rfl\n  | succ k _ => rfl\n",
    ] {
        let outcome = run_probe(source, "cases");
        assert_eq!(
            outcome.verdict,
            Verdict::Pass,
            "wildcard/anonymous-binder case alternative must elaborate, got {:?}: {}",
            outcome.verdict,
            outcome.detail
        );
    }
}

/// Every construct in the historically-silent set now names itself.
///
/// This is the direct anti-regression for the T0 fix: reverting the
/// `tactic_chain` plumbing or the `parse_file_with_tactics_diagnostics` switch
/// puts these back to a bare synthetic sorry with an empty diagnostic list.
#[test]
fn historically_silent_constructs_name_themselves() {
    // (source, the token the diagnostic must name)
    let cases: &[(&str, &str)] = &[
        ("theorem p (a : Nat) : a = a := by\n  set x := a\n", "set"),
        (
            "theorem p (a : Nat) : a = a := by\n  conv_rhs => rfl\n",
            "conv_rhs",
        ),
        (
            "theorem p (a : Nat) : a = a := by\n  conv_lhs => rfl\n",
            "conv_lhs",
        ),
        (
            "theorem p (a : Nat) : a = a := by\n  conv in a => rfl\n",
            "conv",
        ),
        (
            "theorem p (a b : Nat) : a + b = b + a := by\n  module\n",
            "module",
        ),
        ("theorem p (a : Nat) : a = a := by\n  simp [*]\n", "simp"),
        (
            "theorem p (a : Nat) : a = a := by\n  simp (config := { decide := true })\n",
            "simp",
        ),
        (
            "theorem p (a b : Nat) (h : a = b) : a = b := by\n  rcases h with -\n",
            "rcases",
        ),
        (
            "theorem p (a b : Nat) (h : a = b) : a = b := by\n  on_goal 1 => exact h\n",
            "on_goal",
        ),
        ("theorem p (a : Nat) : a = a := by\n  let' x := a\n", "let'"),
        (
            "theorem p (a b : Nat) (h : a = b) : a = b := by\n  specialize h\n",
            "specialize",
        ),
        (
            "theorem p (a b : Nat) (h : a = b) : a = b := by\n  rw\n",
            "rw",
        ),
        (
            "theorem p (a b : Nat) (h : a = b) : a = b := by\n  revert\n",
            "revert",
        ),
        (
            "theorem p (a b : Nat) (h : a = b) : a = b := by\n  unfold\n",
            "unfold",
        ),
    ];
    for (source, token) in cases {
        let outcome = run_probe(source, token);
        assert_ne!(
            outcome.verdict,
            Verdict::Silent,
            "`{token}` degraded to a SILENT synthetic sorry — nothing named it.\n{source}"
        );
        assert_eq!(
            outcome.verdict,
            Verdict::Loud,
            "`{token}` failed without a diagnostic naming it (got {:?}): {}",
            outcome.verdict,
            outcome.detail
        );
    }
}
