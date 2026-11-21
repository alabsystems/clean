// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `#guard_msgs`: compare the messages a command produces with the doc
//! comment written before it, exactly as Lean 4.8.0 does
//! (`Lean/Elab/GuardMsgs.lean`, `elabGuardMsgs`).
//!
//! The comparison is Lean's, step for step: the expectation is the doc text
//! trimmed, with the `⏎` trailing-whitespace marker removed; each captured
//! message is rendered `severity: text` without a position
//! (`messageToStringWithoutPos`); the renderings are joined with `---\n` and
//! trimmed; and the two sides are equal after the configured whitespace
//! normalization (newlines read as spaces by default).
//!
//! What a command "produces" is the one place Clean must translate: Lean logs
//! messages while elaborating, Clean returns a result or an error. The
//! translation ([`messages_of`]) is an information message per command output
//! (`#print axioms`, `#check`, `#eval`, `#print`), Lean's `declaration uses
//! 'sorry'` warning for an explicit `sorry`, and an error message per failure.
//! Where Clean's TEXT differs from Lean's (a `#check` rendering, an
//! elaboration error) the comparison fails — a mismatch is reported, never
//! excused.

use clean_parser::{GuardMsgsOrdering, GuardMsgsSeverity, GuardMsgsSpecElt, GuardMsgsWhitespace};

use crate::infer::{CommandOutput, ElabResult};
use crate::registration_warning::{RegistrationWarning, RegistrationWarningKind};
use crate::ElabError;

/// Severity of a message a command produced (`Lean.MessageSeverity`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum MessageSeverity {
    /// An information message (`logInfo`).
    Information,
    /// A warning.
    Warning,
    /// An error.
    Error,
}

/// One message a command produced.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CommandMessage {
    /// Its severity.
    pub severity: MessageSeverity,
    /// Its text (`msg.data.toString`).
    pub text: String,
}

impl CommandMessage {
    /// An information message.
    #[must_use]
    pub(crate) fn info(text: impl Into<String>) -> Self {
        Self {
            severity: MessageSeverity::Information,
            text: text.into(),
        }
    }

    /// `messageToStringWithoutPos` (a Clean message has no caption).
    #[must_use]
    fn render(&self) -> String {
        let mut text = self.text.clone();
        if !text.starts_with('\n') {
            text.insert(0, ' ');
        }
        let prefix = match self.severity {
            MessageSeverity::Information => "info:",
            MessageSeverity::Warning => "warning:",
            MessageSeverity::Error => "error:",
        };
        text.insert_str(0, prefix);
        if !text.ends_with('\n') {
            text.push('\n');
        }
        text
    }
}

/// A `#guard_msgs` whose expectation matched.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GuardMsgsResult {
    /// The messages the configuration let through unchecked (Lean puts them
    /// back on the message log).
    pub passthrough: Vec<CommandMessage>,
}

/// What the configuration does with one message (`SpecResult`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SpecResult {
    Check,
    Drop,
    Passthrough,
}

/// The interpreted configuration (`parseGuardMsgsSpec`).
struct GuardMsgsConfig {
    whitespace: GuardMsgsWhitespace,
    ordering: GuardMsgsOrdering,
    /// The filter clauses, leftmost first; empty means "check everything".
    filters: Vec<(bool, GuardMsgsSeverity)>,
}

impl GuardMsgsConfig {
    fn new(spec: &[GuardMsgsSpecElt]) -> Self {
        let mut config = Self {
            whitespace: GuardMsgsWhitespace::Normalized,
            ordering: GuardMsgsOrdering::Exact,
            filters: Vec::new(),
        };
        // Lean folds `elts.reverse`, so the LAST whitespace/ordering clause
        // written is applied first and the FIRST one written wins.
        for elt in spec.iter().rev() {
            match *elt {
                GuardMsgsSpecElt::Filter { drop, severity } => {
                    config.filters.push((drop, severity))
                }
                GuardMsgsSpecElt::Whitespace(mode) => config.whitespace = mode,
                GuardMsgsSpecElt::Ordering(mode) => config.ordering = mode,
            }
        }
        config.filters.reverse();
        config
    }

    /// The fold of `pushP` over the filters: the leftmost clause that names
    /// the message's severity (or `all`) decides; an unnamed severity passes
    /// through; with no filter clause at all every message is checked.
    fn classify(&self, severity: MessageSeverity) -> SpecResult {
        if self.filters.is_empty() {
            return SpecResult::Check;
        }
        for &(drop, named) in &self.filters {
            let hit = match named {
                GuardMsgsSeverity::All => true,
                GuardMsgsSeverity::Info => severity == MessageSeverity::Information,
                GuardMsgsSeverity::Warning => severity == MessageSeverity::Warning,
                GuardMsgsSeverity::Error => severity == MessageSeverity::Error,
            };
            if hit {
                return if drop {
                    SpecResult::Drop
                } else {
                    SpecResult::Check
                };
            }
        }
        SpecResult::Passthrough
    }
}

/// `Char.isWhitespace`: Lean's whitespace is these four characters only.
fn is_lean_whitespace(c: char) -> bool {
    matches!(c, ' ' | '\t' | '\r' | '\n')
}

/// `String.trim`.
fn lean_trim(s: &str) -> &str {
    s.trim_matches(is_lean_whitespace)
}

/// `WhitespaceMode.apply`.
fn apply_whitespace(mode: GuardMsgsWhitespace, s: &str) -> String {
    match mode {
        GuardMsgsWhitespace::Exact => s.to_owned(),
        GuardMsgsWhitespace::Normalized => s.replace('\n', " "),
        GuardMsgsWhitespace::Lax => s
            .split(is_lean_whitespace)
            .filter(|part| !part.is_empty())
            .collect::<Vec<_>>()
            .join(" "),
    }
}

/// The messages a finished command produced, in the order Lean would log
/// them.
#[must_use]
pub(crate) fn messages_of(
    outcome: &Result<ElabResult, ElabError>,
    warning: Option<&RegistrationWarning>,
) -> Vec<CommandMessage> {
    let mut out = Vec::new();
    match outcome {
        Ok(result) => push_result_messages(result, &mut out),
        Err(error) => out.push(CommandMessage {
            severity: MessageSeverity::Error,
            text: error.to_string(),
        }),
    }
    if warning.is_some_and(|w| matches!(w.kind, RegistrationWarningKind::ExplicitSorry)) {
        // Lean's `warnIfUsesSorry` text. A synthetic sorry stands for an
        // error already reported, and Lean logs nothing more for it.
        out.push(CommandMessage {
            severity: MessageSeverity::Warning,
            text: "declaration uses 'sorry'".to_owned(),
        });
    }
    out
}

/// The messages a command that ELABORATED produced, in the order Lean logs
/// them: an information message per command output (`#check`, `#eval`,
/// `#print`, `#print axioms`, a matched `#guard_msgs`'s passthrough) and an
/// error per failed member. The same translation `#guard_msgs` compares, so
/// `clean lean` (the `lean`-compatible front door) prints exactly what a
/// surrounding `#guard_msgs` would have seen. Trust-debt warnings are not
/// here: they belong to a checked leaf (see [`messages_of`]).
#[must_use]
pub fn result_messages(result: &ElabResult) -> Vec<CommandMessage> {
    let mut out = Vec::new();
    push_result_messages(result, &mut out);
    out
}

fn push_result_messages(result: &ElabResult, out: &mut Vec<CommandMessage>) {
    match result {
        ElabResult::Command(output) => match output {
            CommandOutput::PrintAxioms(r) => {
                out.extend(r.messages.iter().map(CommandMessage::info));
            }
            CommandOutput::PrintEquations(messages) => {
                out.extend(messages.iter().map(CommandMessage::info));
            }
            CommandOutput::GuardMsgs(r) => out.extend(r.passthrough.iter().cloned()),
            CommandOutput::Check(r) => out.push(CommandMessage::info(r.to_string())),
            CommandOutput::Eval(r) => out.push(CommandMessage::info(r.to_string())),
            CommandOutput::Reduce(r) => out.push(CommandMessage::info(r.to_string())),
            CommandOutput::Print(r) => out.push(CommandMessage::info(r.to_string())),
        },
        ElabResult::Multiple(results) => {
            for inner in results {
                push_result_messages(inner, out);
            }
        }
        ElabResult::Diagnosed {
            result,
            diagnostics,
        } => {
            push_result_messages(result, out);
            out.extend(diagnostics.iter().map(|diagnostic| CommandMessage {
                severity: MessageSeverity::Error,
                text: diagnostic.error.to_string(),
            }));
        }
        ElabResult::Failed { error, .. } => out.push(CommandMessage {
            severity: MessageSeverity::Error,
            text: error.to_string(),
        }),
        _ => {}
    }
}

/// The verdict of a `#guard_msgs`.
pub(crate) enum GuardMsgsVerdict {
    /// The expectation matched; the passthrough messages go back on the log.
    Matched(Vec<CommandMessage>),
    /// It did not; this is Lean's error message.
    Mismatch(String),
}

/// `elabGuardMsgs`'s comparison of `doc` (the raw doc-comment text, `None`
/// when there is none) against `messages`.
#[must_use]
pub(crate) fn judge(
    doc: Option<&str>,
    spec: &[GuardMsgsSpecElt],
    messages: &[CommandMessage],
) -> GuardMsgsVerdict {
    let config = GuardMsgsConfig::new(spec);
    let expected = lean_trim(doc.unwrap_or("")).replace("⏎\n", "\n");
    let mut checked = Vec::new();
    let mut passthrough = Vec::new();
    for message in messages {
        match config.classify(message.severity) {
            SpecResult::Check => checked.push(message.render()),
            SpecResult::Drop => {}
            SpecResult::Passthrough => passthrough.push(message.clone()),
        }
    }
    if config.ordering == GuardMsgsOrdering::Sorted {
        checked.sort();
    }
    let joined = checked.join("---\n");
    let produced = lean_trim(&joined);
    if apply_whitespace(config.whitespace, &expected)
        == apply_whitespace(config.whitespace, produced)
    {
        GuardMsgsVerdict::Matched(passthrough)
    } else {
        GuardMsgsVerdict::Mismatch(format!(
            "❌ Docstring on `#guard_msgs` does not match generated message:\n\n{produced}"
        ))
    }
}

/// Conclude a `#guard_msgs` whose command finished with `outcome`.
///
/// On a match the command's own result stands — a declaration it elaborated
/// is registered and counted like any other — except that an error the
/// expectation named is consumed, as Lean consumes it, leaving nothing
/// registered. A command result that is not a declaration becomes
/// [`CommandOutput::GuardMsgs`]. On a mismatch the `#guard_msgs` fails with
/// Lean's message, which quotes what the command produced.
///
/// # Errors
///
/// [`ElabError::CommandFailed`] on a mismatch.
pub(crate) fn conclude(
    doc: Option<&str>,
    spec: &[GuardMsgsSpecElt],
    outcome: Result<ElabResult, ElabError>,
    warning: Option<&RegistrationWarning>,
) -> Result<ElabResult, ElabError> {
    // A `#reduce` is never judged: its refusal is Clean's, not a message of
    // Lean's a doc comment could name, and its output is Clean's rendering,
    // not Lean's (`crate::reduce_command`). Either way the `#guard_msgs` is
    // refused, so no expectation, `drop` spec included, can launder it.
    if let Some(refusal) = reduce_refusal(&outcome) {
        return Err(refusal);
    }
    let messages = messages_of(&outcome, warning);
    match judge(doc, spec, &messages) {
        GuardMsgsVerdict::Mismatch(message) => {
            let error = ElabError::CommandFailed { message };
            match outcome {
                // The assertion failed after its body declared real values.
                // Keep those values and their original diagnostics; report
                // the failed assertion as a separate checked command.
                Ok(result) if has_checked_leaves(&result) => Ok(ElabResult::Multiple(vec![
                    result,
                    ElabResult::Diagnosed {
                        result: Box::new(ElabResult::Command(CommandOutput::GuardMsgs(
                            GuardMsgsResult {
                                passthrough: Vec::new(),
                            },
                        ))),
                        diagnostics: vec![crate::source_diagnostics::SourceDiagnostic {
                            error,
                            span: None,
                        }],
                    },
                ])),
                _ => Err(error),
            }
        }
        GuardMsgsVerdict::Matched(passthrough) => match outcome {
            Ok(result) if has_checked_leaves(&result) => Ok(result.without_source_diagnostics()),
            Ok(_) | Err(_) => Ok(ElabResult::Command(CommandOutput::GuardMsgs(
                GuardMsgsResult { passthrough },
            ))),
        },
    }
}

/// The refusal a `#guard_msgs` over `outcome` must surface unjudged: a
/// [`ElabError::ReduceUnmodeled`] anywhere in it, or a `#reduce` output.
fn reduce_refusal(outcome: &Result<ElabResult, ElabError>) -> Option<ElabError> {
    fn in_result(result: &ElabResult) -> Option<ElabError> {
        match result {
            ElabResult::Command(CommandOutput::Reduce(_)) => Some(ElabError::ReduceUnmodeled {
                reason: "a `#guard_msgs` compares its output, and Clean's rendering of a \
                         term is not Lean's"
                    .to_owned(),
            }),
            ElabResult::Failed { error, .. } => in_error(error),
            ElabResult::Diagnosed {
                result,
                diagnostics,
            } => diagnostics
                .iter()
                .find_map(|diagnostic| in_error(&diagnostic.error))
                .or_else(|| in_result(result)),
            ElabResult::Multiple(results) => results.iter().find_map(in_result),
            _ => None,
        }
    }
    fn in_error(error: &ElabError) -> Option<ElabError> {
        matches!(error, ElabError::ReduceUnmodeled { .. }).then(|| error.clone())
    }
    match outcome {
        Ok(result) => in_result(result),
        Err(error) => in_error(error),
    }
}

/// Whether `result` holds a declaration the checkers count (a definition, a
/// theorem, an `example`, a `#guard`, a failed member, …), as opposed to a
/// bare command output.
fn has_checked_leaves(result: &ElabResult) -> bool {
    let mut leaves = Vec::new();
    result.leaf_decls(&mut leaves);
    !leaves.is_empty()
}

#[cfg(test)]
#[path = "guard_msgs_tests.rs"]
mod tests;
