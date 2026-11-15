// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Replay a loaded export and decide it: accept (0), reject (1) or decline
//! (2).
//!
//! The replay is `clean olean replay --fresh`'s engine
//! (`verify_batch_full::typecheck_constants_full_ordered`): every declaration
//! the export declares is a target, checked in Lean's replay order in
//! `KernelTheory::Lean`, every inductive block rebuilt by the kernel and its
//! stored constructors and recursors compared with the rebuilt ones. A
//! declaration refused before the replay (structural tier, quotient,
//! unknown constant) and every `unsafe`/`partial` declaration is handed to it
//! as not admitted, so every declaration that uses one is refused, as Lean's
//! replay refuses it with `unknown constant`.
//!
//! The verdict:
//!
//! - any refusal on a finding: REJECT (exit 1);
//! - otherwise any refusal that is only the heartbeat budget running out:
//!   DECLINE (exit 2);
//! - otherwise any `partial` definition left out (Lean's replay never checks
//!   one, and neither does this): DECLINE (exit 2, decision R117 in
//!   `docs/DECISIONS.md`);
//! - otherwise, when the export declares a name Lean's kernel keys a literal
//!   rule on (a `reduce_nat` head, `String.ofList`, `Char.ofNat`, `Nat`) and
//!   Clean does not admit that rule for the declaration (its native-fold
//!   authority, or the canonical `Nat`), or declares `Lean.reduceBool` or
//!   `Lean.reduceNat` at all: DECLINE (exit 2, R128). Lean folds by the name
//!   (or evaluates it with compiled code a replayed export lacks); Clean
//!   unfolds the declaration, so the two kernels compute different things for
//!   a forged one;
//! - otherwise, when a declaration's stored data mentions a level the
//!   kernel's constructors build otherwise than Lean reads it (built as
//!   `zero`, rewritten through an `imax`), or an inductive block mentions a
//!   rewritten level at all: DECLINE (exit 2, R125). Clean judged the
//!   declarations over the built level, which Lean does not read;
//! - otherwise ACCEPT (exit 0). An `unsafe` declaration is left out as Lean's
//!   replay leaves it out, and declines nothing.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::time::Instant;

use clean_kernel::name::Name;
use serde::Serialize;

use super::error::{ExitClass, NdjsonError};
use super::load::{load_export, LoadedExport};
use super::source::ExportSource;
use super::world::ExportMeta;
use crate::verify_batch_full::{typecheck_constants_full_ordered, ReplayScope};

/// How to run the front door.
#[derive(Debug, Clone, Copy, Default)]
pub struct ExportCheckOptions {
    /// Kernel heartbeat budget of each declaration check; `0` is unlimited, as
    /// Lean's replay runs.
    pub max_heartbeats: u32,
    /// Compute each declaration's structural axiom closure (`--json`).
    pub axiom_closures: bool,
}

/// What became of one declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum DeclarationVerdict {
    /// Checked and admitted.
    Admitted,
    /// Refused on a finding.
    Refused,
    /// Not decided: the heartbeat budget ran out (or ran out for every
    /// dependency that refused it). Not admitted.
    BudgetExhausted,
    /// `unsafe` or `partial`: left out, as Lean's replay leaves it out.
    NotReplayable,
}

/// One declaration of the export (`--json`).
#[derive(Debug, Clone, Serialize)]
pub struct DeclarationRecord {
    /// The name as the export wrote it, rendered unambiguously
    /// (`Name::to_unambiguous_string`).
    pub name: String,
    /// The record kind (`axiom`, `def`, `thm`, `opaque`, `quot`, `inductive`,
    /// `constructor`, `recursor`).
    pub kind: &'static str,
    /// The line that declares it.
    pub line: u64,
    /// What became of it.
    pub verdict: DeclarationVerdict,
    /// Why, unless admitted.
    pub reason: Option<String>,
    /// The declared axioms its stored data reaches through the export's
    /// declarations, by structure (names, not strings), rendered
    /// unambiguously; present when asked for.
    pub axioms: Option<Vec<String>>,
}

/// The first refusal, as `leanchecker` reports it.
#[derive(Debug, Clone, Serialize)]
pub struct FirstRefusal {
    /// The declaration.
    pub name: String,
    /// Why.
    pub reason: String,
}

/// The reader's refusal of a malformed (or unsupported) export.
#[derive(Debug, Clone, Serialize)]
pub struct ReaderRefusal {
    /// The rule (`NdjsonError::rule`).
    pub rule: &'static str,
    /// The message.
    pub message: String,
}

/// The verdict on one export.
#[derive(Debug, Clone, Serialize)]
pub struct ExportReport {
    /// Accept, reject or decline.
    pub exit: ExitClass,
    /// The exit code: 0, 1 or 2.
    pub exit_code: u8,
    /// The export's header, once read.
    pub meta: Option<ExportMeta>,
    /// Set when the reader refused or declined the export.
    pub reader_error: Option<ReaderRefusal>,
    /// Why the run declined, when it did after reading the export.
    pub decline_reason: Option<String>,
    /// Declarations the export declares.
    pub declarations: usize,
    /// Of them, admitted.
    pub admitted: usize,
    /// Refused on a finding.
    pub refused: usize,
    /// Not decided within the heartbeat budget.
    pub budget_exhausted: usize,
    /// `unsafe`/`partial`, left out.
    pub not_replayable: usize,
    /// The first refusal on a finding, in the export's order.
    pub first_refusal: Option<FirstRefusal>,
    /// Milliseconds spent reading and loading.
    pub load_ms: u64,
    /// Milliseconds spent replaying.
    pub replay_ms: u64,
    /// Targets the replay engine counted admitted.
    pub replay_pass: usize,
    /// Targets the replay engine counted refused.
    pub replay_fail: usize,
    /// Every declaration, in the export's order.
    pub records: Vec<DeclarationRecord>,
}

fn millis(since: Instant) -> u64 {
    u64::try_from(since.elapsed().as_millis()).unwrap_or(u64::MAX)
}

impl ExportReport {
    /// The report on an export the reader refused or declined.
    #[must_use]
    pub(crate) fn reader_failure(
        meta: Option<ExportMeta>,
        error: &NdjsonError,
        load_ms: u64,
    ) -> Self {
        let exit = error.exit_class();
        Self {
            exit,
            exit_code: exit.code(),
            meta,
            reader_error: Some(ReaderRefusal {
                rule: error.rule(),
                message: error.to_string(),
            }),
            decline_reason: None,
            declarations: 0,
            admitted: 0,
            refused: 0,
            budget_exhausted: 0,
            not_replayable: 0,
            first_refusal: None,
            load_ms,
            replay_ms: 0,
            replay_pass: 0,
            replay_fail: 0,
            records: Vec::new(),
        }
    }
}

/// Load `source`, replay it and decide.
pub(crate) fn check_export<S: ExportSource>(
    source: S,
    options: ExportCheckOptions,
) -> ExportReport {
    let start = Instant::now();
    let meta = source.meta().clone();
    let loaded = match load_export(source) {
        Ok(loaded) => loaded,
        Err(error) => return ExportReport::reader_failure(Some(meta), &error, millis(start)),
    };
    let load_ms = millis(start);
    let replay_start = Instant::now();
    let (mut verdicts, counted) = replay(&loaded, options.max_heartbeats);
    propagate(&loaded, &mut verdicts);
    let replay_ms = millis(replay_start);
    let closures = options
        .axiom_closures
        .then(|| super::closure::axiom_closures(&loaded.refs, &loaded.axioms));
    let mut report = decide(&loaded, &verdicts, closures.as_ref(), load_ms, replay_ms);
    report.replay_pass = counted.pass;
    report.replay_fail = counted.fail;
    if counted.fail > counted.failed_targets && report.exit == ExitClass::Accept {
        // Fail-closed: a failure the replay counted never reads as a pass
        // because no target carried its reason.
        report.exit = ExitClass::Reject;
        report.exit_code = report.exit.code();
        report.first_refusal = Some(FirstRefusal {
            name: String::new(),
            reason: format!(
                "the replay counted {} failure(s) and gave a reason for {}",
                counted.fail, counted.failed_targets
            ),
        });
    }
    report
}

/// What the replay itself counted, beside the per-target verdicts.
struct Counted {
    pass: usize,
    fail: usize,
    /// Targets this module recorded as not admitted.
    failed_targets: usize,
}

type Verdicts = BTreeMap<Name, (DeclarationVerdict, Option<String>)>;

fn replay(loaded: &LoadedExport, max_heartbeats: u32) -> (Verdicts, Counted) {
    let mut verdicts: Verdicts = BTreeMap::new();
    let mut targets: BTreeSet<String> = BTreeSet::new();
    let mut not_admitted: BTreeSet<String> = BTreeSet::new();
    for entry in &loaded.declared {
        let name = &entry.name;
        if let Some(reason) = loaded.refused.get(name) {
            verdicts.insert(
                name.clone(),
                (DeclarationVerdict::Refused, Some(reason.clone())),
            );
            not_admitted.insert(name.to_string());
        } else if let Some(safety) = loaded.not_replayable.get(name) {
            verdicts.insert(
                name.clone(),
                (
                    DeclarationVerdict::NotReplayable,
                    Some(format!(
                        "{safety}: left out, as Lean's replay leaves it out"
                    )),
                ),
            );
            not_admitted.insert(name.to_string());
        } else {
            targets.insert(name.to_string());
        }
    }
    let none = BTreeSet::new();
    let no_declarations = BTreeMap::new();
    let scope = ReplayScope {
        prerequisites: &none,
        not_admitted: &not_admitted,
        already_declared: &no_declarations,
    };
    let run = typecheck_constants_full_ordered(&loaded.env, &targets, &scope, max_heartbeats);
    let mut by_label: BTreeMap<String, (DeclarationVerdict, Option<String>)> = BTreeMap::new();
    for (name, verdict) in &run.verdicts {
        let row = match verdict {
            Ok(()) => (DeclarationVerdict::Admitted, None),
            Err(refusal) if refusal.undecided() => (
                DeclarationVerdict::BudgetExhausted,
                Some(refusal.to_string()),
            ),
            Err(refusal) => (DeclarationVerdict::Refused, Some(refusal.to_string())),
        };
        by_label.insert(name.to_string(), row);
    }
    let mut failed_targets = 0usize;
    for entry in &loaded.declared {
        let label = entry.name.to_string();
        if !targets.contains(&label) {
            continue;
        }
        let row = match (by_label.remove(&label), run.errors.get(&label)) {
            (Some((DeclarationVerdict::Admitted, _)), Some(problem)) | (None, Some(problem)) => {
                (DeclarationVerdict::Refused, Some(problem.clone()))
            }
            (Some(row), _) => row,
            // Fail-closed: a target the replay gave no verdict is not admitted.
            (None, None) => (
                DeclarationVerdict::Refused,
                Some("the replay recorded no verdict for it".to_owned()),
            ),
        };
        failed_targets += usize::from(row.0 != DeclarationVerdict::Admitted);
        verdicts.insert(entry.name.clone(), row);
    }
    let counted = Counted {
        pass: run.pass,
        fail: run.fail,
        failed_targets,
    };
    (verdicts, counted)
}

/// Refuse every admitted declaration that mentions one not admitted, to a
/// fixed point. The replay's own schedule does this already; this pass is the
/// export's own account of it, and adds the one edge the schedule cannot see:
/// Lean's replay installs the quotient only after `Eq` (`replayConstant`), so
/// every `quot` record depends on `Eq`.
fn propagate(loaded: &LoadedExport, verdicts: &mut Verdicts) {
    let eq = Name::from_string("Eq");
    let deps = |name: &Name| -> Vec<Name> {
        let mut out: Vec<Name> = loaded
            .refs
            .get(name)
            .map(|r| r.iter().filter(|d| *d != name).cloned().collect())
            .unwrap_or_default();
        if loaded.quot_records.contains(name) {
            out.push(eq.clone());
        }
        out
    };
    let mut users: BTreeMap<Name, Vec<Name>> = BTreeMap::new();
    for name in verdicts.keys() {
        for dep in deps(name) {
            users.entry(dep).or_default().push(name.clone());
        }
    }
    let mut queue: VecDeque<Name> = verdicts
        .iter()
        .filter(|(_, (v, _))| *v != DeclarationVerdict::Admitted)
        .map(|(n, _)| n.clone())
        .collect();
    while let Some(blocked) = queue.pop_front() {
        let Some(status) = verdicts.get(&blocked).map(|(v, _)| *v) else {
            continue;
        };
        for user in users.get(&blocked).into_iter().flatten() {
            if verdicts.get(user).map(|(v, _)| *v) != Some(DeclarationVerdict::Admitted) {
                continue;
            }
            let verdict = if status == DeclarationVerdict::BudgetExhausted {
                DeclarationVerdict::BudgetExhausted
            } else {
                DeclarationVerdict::Refused
            };
            verdicts.insert(
                user.clone(),
                (
                    verdict,
                    Some(format!(
                        "depends on `{}`, which was not admitted",
                        loaded.shown(&blocked)
                    )),
                ),
            );
            queue.push_back(user.clone());
        }
    }
}

/// The names Lean's kernel computes by NAME on literals (v4.30.0-rc2):
/// `type_checker::reduce_nat`'s fourteen binary heads, and the string-literal
/// expansion's `String.ofList` and `Char.ofNat` (`inductive.cpp`
/// `string_lit_to_constructor`), with what Lean does with each.
const NAME_KEYED_LITERAL_RULES: [(&str, &str); 16] = [
    ("Nat.add", "folds on literals (`reduce_nat`)"),
    ("Nat.sub", "folds on literals (`reduce_nat`)"),
    ("Nat.mul", "folds on literals (`reduce_nat`)"),
    ("Nat.div", "folds on literals (`reduce_nat`)"),
    ("Nat.mod", "folds on literals (`reduce_nat`)"),
    ("Nat.gcd", "folds on literals (`reduce_nat`)"),
    ("Nat.beq", "folds on literals (`reduce_nat`)"),
    ("Nat.ble", "folds on literals (`reduce_nat`)"),
    ("Nat.land", "folds on literals (`reduce_nat`)"),
    ("Nat.lor", "folds on literals (`reduce_nat`)"),
    ("Nat.xor", "folds on literals (`reduce_nat`)"),
    ("Nat.shiftLeft", "folds on literals (`reduce_nat`)"),
    ("Nat.shiftRight", "folds on literals (`reduce_nat`)"),
    ("Nat.pow", "folds on literals (`reduce_nat`)"),
    (
        "String.ofList",
        "expands string literals through (`string_lit_to_constructor`)",
    ),
    (
        "Char.ofNat",
        "expands string literals through (`string_lit_to_constructor`)",
    ),
];

/// The names Lean's kernel evaluates BY NAME with the compiler's interpreter
/// (v4.30.0-rc2 `type_checker::reduce_native`): an application's argument is
/// run as compiled code. A replayed export carries no compiled code, so Lean
/// refuses every such evaluation ("(kernel) (interpreter) unknown
/// declaration"), whatever the declaration says; Clean computes it from the
/// declaration (its authority admits an identity-valued one). An export that
/// declares either is never accepted, whatever Clean's authority (R128).
const NATIVE_EVALUATION_HEADS: [&str; 2] = ["Lean.reduceBool", "Lean.reduceNat"];

/// Why the export cannot be accepted for a name-keyed literal rule
/// (R128), if it cannot: it declares one of [`NAME_KEYED_LITERAL_RULES`]'s
/// names as a declaration Clean's native-fold authority does not admit, or a
/// `Nat` other than the canonical inductive. Lean applies the rule by the
/// name whatever the declaration says; Clean applies it only to an admitted
/// declaration and otherwise unfolds (or keeps stuck) what Lean computes, so
/// for a forged declaration the two kernels decide differently, in either
/// direction.
fn name_keyed_rule_unadmitted(loaded: &LoadedExport) -> Option<String> {
    let nat = Name::from_string("Nat");
    let heads: Vec<(Name, &str)> = NAME_KEYED_LITERAL_RULES
        .iter()
        .map(|(head, what)| (Name::from_string(head), *what))
        .collect();
    let native: Vec<Name> = NATIVE_EVALUATION_HEADS
        .iter()
        .map(|head| Name::from_string(head))
        .collect();
    for entry in &loaded.declared {
        if native.contains(&entry.name) {
            return Some(format!(
                "the export declares `{}`, a name Lean's kernel evaluates by name with compiled \
                 code (`reduce_native`), which a replayed export does not carry, so Lean refuses \
                 every such evaluation while Clean computes it from the declaration (decision \
                 R128)",
                loaded.shown(&entry.name)
            ));
        }
        if entry.name == nat && !loaded.env.nat_literal_extension_canonical() {
            return Some(format!(
                "the export declares `{}`, the name Lean's kernel types every literal by and \
                 expands literals with, and it is not the canonical `Nat : Type` with \
                 constructors `Nat.zero` and `Nat.succ`; Clean does not apply Lean's literal \
                 rules to it (decision R128)",
                loaded.shown(&entry.name)
            ));
        }
        if let Some((_, what)) = heads.iter().find(|(head, _)| entry.name == *head) {
            if !loaded.env.native_fold_authorized(&entry.name) {
                return Some(format!(
                    "the export declares `{}`, a name Lean's kernel {what} by name, and Clean's \
                     native-fold authority does not admit this declaration of it: Clean unfolds \
                     it where Lean computes by the name (decision R128)",
                    loaded.shown(&entry.name)
                ));
            }
        }
    }
    None
}

fn decide(
    loaded: &LoadedExport,
    verdicts: &Verdicts,
    closures: Option<&BTreeMap<Name, BTreeSet<Name>>>,
    load_ms: u64,
    replay_ms: u64,
) -> ExportReport {
    let mut report = ExportReport {
        exit: ExitClass::Accept,
        exit_code: 0,
        meta: Some(loaded.meta.clone()),
        reader_error: None,
        decline_reason: None,
        declarations: loaded.declared.len(),
        admitted: 0,
        refused: 0,
        budget_exhausted: 0,
        not_replayable: 0,
        first_refusal: None,
        load_ms,
        replay_ms,
        replay_pass: 0,
        replay_fail: 0,
        records: Vec::with_capacity(loaded.declared.len()),
    };
    let mut partial_left_out = false;
    for entry in &loaded.declared {
        let (verdict, reason) = verdicts.get(&entry.name).cloned().unwrap_or((
            DeclarationVerdict::Refused,
            Some("no verdict was recorded for it".to_owned()),
        ));
        match verdict {
            DeclarationVerdict::Admitted => report.admitted += 1,
            DeclarationVerdict::Refused => {
                report.refused += 1;
                if report.first_refusal.is_none() {
                    report.first_refusal = Some(FirstRefusal {
                        name: loaded.shown(&entry.name),
                        reason: reason.clone().unwrap_or_default(),
                    });
                }
            }
            DeclarationVerdict::BudgetExhausted => report.budget_exhausted += 1,
            DeclarationVerdict::NotReplayable => {
                report.not_replayable += 1;
                partial_left_out |= loaded.not_replayable.get(&entry.name) == Some(&"partial");
            }
        }
        report.records.push(DeclarationRecord {
            name: loaded.shown(&entry.name),
            kind: entry.kind,
            line: entry.line,
            verdict,
            reason,
            axioms: closures.map(|c| {
                c.get(&entry.name)
                    .map(|set| set.iter().map(|n| loaded.shown(n)).collect())
                    .unwrap_or_default()
            }),
        });
    }
    report.exit = if report.refused > 0 {
        ExitClass::Reject
    } else if report.budget_exhausted > 0 {
        report.decline_reason = Some(format!(
            "{} declaration(s) were not decided within the --max-heartbeats budget",
            report.budget_exhausted
        ));
        ExitClass::Decline
    } else if partial_left_out {
        report.decline_reason = Some(
            "a `partial` definition was left out unchecked, as Lean's replay leaves it out \
             (decision R117)"
                .to_owned(),
        );
        ExitClass::Decline
    } else if let Some(reason) = name_keyed_rule_unadmitted(loaded) {
        report.decline_reason = Some(reason);
        ExitClass::Decline
    } else if let (Some(taint), count) = &loaded.level_taint {
        report.decline_reason = Some(format!(
            "{taint}; {count} declaration record(s) are over such a level, and an export over \
             one is never accepted (decision R125)"
        ));
        ExitClass::Decline
    } else {
        ExitClass::Accept
    };
    report.exit_code = report.exit.code();
    report
}
