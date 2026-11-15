// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The module driver observed as Lean's message log (decision R77).
//!
//! `clean check` turns each declaration's outcome into a verification row;
//! `clean lean` turns the SAME outcome into the messages `lean` logs for it:
//!
//! - a command's output (`#eval`, `#check`, `#print`, `#print axioms`, a matched
//!   `#guard_msgs`'s passthrough) is an information message
//!   ([`clean_elab::result_messages`], the translation `#guard_msgs` compares);
//! - a declaration whose OWN terms contain an explicit `sorry` gets Lean's
//!   `declaration uses 'sorry'` warning on its name, and the run still exits 0
//!   (Lean's semantics, not `clean check`'s policy);
//! - a declaration, or a block member, that failed is an error.
//!
//! Fail-closed where Clean's outcome has no Lean counterpart, so `clean lean`
//! never exits 0 on something Lean was not shown to accept:
//!
//! - a synthetic `sorry` with no error logged for its declaration (Clean
//!   recovered from something it could not elaborate without saying so) is an
//!   error;
//! - a declaration resting on `trustedArith` / `trustedAy` (a decision
//!   procedure's verdict, where Lean checks a proof term) is an error;
//! - a kernel failure, a failed read-only re-validation and an exhausted
//!   per-declaration budget are errors.
//!
//! Messages of one top-level declaration are buffered, ordered by the source
//! position of the command that logged them (a `namespace` block's members log
//! in source order, as Lean's commands do), and printed when it is done.

use super::dialect::LeanDialect;
use super::locate::{aux_name_start, command_keyword_range, decl_ref_range, LineIndex};
use super::members::{flatten_members, member_at, Member, MemberKind};
use super::message::{LeanMessage, RenderOptions, Severity, KIND_ANONYMOUS, KIND_HAS_SORRY};
use clean_elab::module_driver::{surface_decl_span, BudgetReading, LeafOutcome, ModuleObserver};
use clean_elab::{
    CommandOutput, ElabError, ElabResult, FileContext, MessageSeverity, RegisteredElabResult,
};
use clean_kernel::env::DeclarationTrustSummary;
use clean_kernel::Environment;
use clean_parser::SurfaceDecl;
use std::io::Write;

/// A message waiting for its declaration to finish: the byte offset of the
/// command that logged it, and the message.
type Pending = (usize, LeanMessage);

/// `clean lean`'s observer.
pub(crate) struct LeanObserver<'a> {
    source: &'a str,
    lines: LineIndex<'a>,
    render: &'a RenderOptions,
    out: &'a mut dyn Write,
    /// Parser recovery notes not yet logged: byte offset and text, ascending.
    recovery: std::collections::VecDeque<(usize, String)>,
    pending: Vec<Pending>,
    /// Byte offsets of the errors logged for the declaration in flight.
    error_anchors: Vec<usize>,
    members: Vec<Member>,
    leaf_cursor: usize,
    command_cursor: usize,
    /// Whether any message of the run was logged as an error (Lean's exit
    /// status; `-E` does not change it).
    pub(crate) error_logged: bool,
    /// The first write to `out` that failed, if any.
    pub(crate) write_error: Option<std::io::Error>,
    /// The start of every top-level declaration, ascending: a declaration's
    /// `where` clause can lie past its own span, but never past the next one.
    decl_starts: Vec<usize>,
}

impl<'a> LeanObserver<'a> {
    pub(crate) fn new(
        source: &'a str,
        render: &'a RenderOptions,
        out: &'a mut dyn Write,
        recovery: Vec<(usize, String)>,
        decl_starts: Vec<usize>,
    ) -> Self {
        Self {
            decl_starts,
            source,
            lines: LineIndex::new(source),
            render,
            out,
            recovery: recovery.into(),
            pending: Vec::new(),
            error_anchors: Vec::new(),
            members: Vec::new(),
            leaf_cursor: 0,
            command_cursor: 0,
            error_logged: false,
            write_error: None,
        }
    }

    fn dialect(&self) -> LeanDialect {
        self.render.dialect
    }

    /// Queue a message logged by the command at `anchor`, spanning
    /// `start..end`.
    fn log(
        &mut self,
        anchor: usize,
        range: (usize, usize),
        severity: Severity,
        kind: &'static str,
        text: String,
    ) {
        if severity == Severity::Error {
            self.error_anchors.push(anchor);
        }
        let message = LeanMessage {
            severity,
            pos: self.lines.pos(range.0),
            end_pos: Some(self.lines.pos(range.1)),
            kind,
            text,
        };
        self.pending.push((anchor, message));
    }

    fn log_error(&mut self, anchor: usize, range: (usize, usize), text: String) {
        self.log(anchor, range, Severity::Error, KIND_ANONYMOUS, text);
    }

    /// Whether an error was logged inside `member`.
    fn member_has_error(&self, member: &Member) -> bool {
        self.error_anchors
            .iter()
            .any(|&at| at >= member.start && at < member.end.max(member.start + 1))
    }

    /// Print everything queued, in source order of the logging commands.
    pub(crate) fn flush(&mut self) {
        let mut pending = std::mem::take(&mut self.pending);
        pending.sort_by_key(|(anchor, _)| *anchor);
        for (_, message) in pending {
            if message.severity == Severity::Error {
                self.error_logged = true;
            }
            if self.write_error.is_none() {
                if let Err(error) = self.out.write_all(message.render(self.render).as_bytes()) {
                    self.write_error = Some(error);
                }
            }
        }
        if let Err(error) = self.out.flush() {
            self.write_error.get_or_insert(error);
        }
    }

    /// Log the recovery notes that lie before `end` (a declaration's end, or
    /// the end of the file). A note is a parse error, which Lean logs before
    /// anything the command's elaboration logs: it is anchored at the start
    /// of the member it lies in, ahead of that member's own messages.
    pub(crate) fn log_recovery_before(&mut self, end: usize) {
        while self.recovery.front().is_some_and(|(at, _)| *at < end) {
            let Some((at, text)) = self.recovery.pop_front() else {
                break;
            };
            let anchor = member_at(&self.members, at).map_or(at, |member| member.start);
            let token_end = decl_ref_range(self.source, at).1.max(at);
            self.log_error(anchor, (at, token_end), text);
        }
    }

    /// An elaboration error of the declaration (or member) at `span_start`.
    fn log_elab_error(&mut self, decl: &SurfaceDecl, span_start: usize, error: &ElabError) {
        if matches!(decl, SurfaceDecl::RawDecl { .. })
            && self.error_anchors.iter().any(|&at| at >= span_start)
        {
            // The parser's recovery note already reported this region.
            return;
        }
        let (range, text) = match error {
            ElabError::InTactic {
                span_start: tactic_start,
                span_end,
                source,
                ..
            } => ((*tactic_start, *span_end), source.to_string()),
            ElabError::CommandFailed { message } if is_guard_msgs(decl) => (
                command_keyword_range(self.source, span_start),
                message.clone(),
            ),
            other => (decl_ref_range(self.source, span_start), other.to_string()),
        };
        self.log_error(span_start, range, text);
    }

    /// The member a checked leaf named `name` belongs to.
    fn leaf_member(&mut self, name: &str, leaf: &ElabResult) -> Option<Member> {
        let found = self.members[self.leaf_cursor..]
            .iter()
            .position(|member| member.matches_leaf(name, leaf))?;
        let index = self.leaf_cursor + found;
        self.leaf_cursor = index + 1;
        Some(self.members[index].clone())
    }

    /// A `where` / `let rec` auxiliary declaration named `name` of the
    /// declaration starting at `start`, as a member starting at its name. The
    /// clause is looked for up to the next top-level declaration: the surface
    /// span of a `def … where …` can end before its clause.
    fn aux_member(&self, name: &str, start: usize, end: usize) -> Option<Member> {
        let short = name.rsplit('.').next().filter(|short| !short.is_empty())?;
        let window = self
            .decl_starts
            .iter()
            .copied()
            .find(|&next| next > start)
            .unwrap_or(self.source.len())
            .max(end);
        let at = aux_name_start(self.source, start, window, short)?;
        Some(Member {
            start: at,
            end: window,
            kind: MemberKind::Decl,
            name: Some(short.to_owned()),
            guarded: false,
        })
    }

    /// The command member the next command output belongs to.
    fn next_command_member(&mut self) -> Option<Member> {
        let found = self.members[self.command_cursor..]
            .iter()
            .position(|member| matches!(member.kind, MemberKind::Command))?;
        let index = self.command_cursor + found;
        self.command_cursor = index + 1;
        Some(self.members[index].clone())
    }

    /// Queue the messages of every command output in `result`, in order: the
    /// information message of `#eval` / `#check` / `#print` / `#print
    /// axioms`, and what a matched `#guard_msgs` passes through, with the
    /// severity it was logged with.
    fn log_outputs(&mut self, fallback: &Member, result: &ElabResult) {
        match result {
            ElabResult::Multiple(results) => {
                for inner in results {
                    self.log_outputs(fallback, inner);
                }
            }
            ElabResult::Command(output) => {
                let member = self
                    .next_command_member()
                    .unwrap_or_else(|| fallback.clone());
                let is_eval = matches!(output, CommandOutput::Eval(_));
                for message in clean_elab::result_messages(result) {
                    let severity = match message.severity {
                        MessageSeverity::Warning => Severity::Warning,
                        MessageSeverity::Error => Severity::Error,
                        _ => Severity::Information,
                    };
                    let mut text = message.text;
                    if is_eval && self.dialect() == LeanDialect::V4_8_0 && !text.ends_with('\n') {
                        // 4.8.0's `#eval` message data ends in a newline.
                        text.push('\n');
                    }
                    let range = command_keyword_range(self.source, member.start);
                    self.log(member.start, range, severity, KIND_ANONYMOUS, text);
                }
            }
            _ => {}
        }
    }

    /// The messages a checked leaf's own trust debt earns.
    fn log_trust(&mut self, env: &Environment, member: &Member, leaf: &ElabResult) {
        let own = clean_elab::register::own_trust_summary(env, leaf);
        let range = decl_ref_range(self.source, member.start);
        let has_error = self.member_has_error(member);
        for (severity, kind, text) in
            trust_messages(self.dialect(), &own, member.guarded, has_error)
        {
            self.log(member.start, range, severity, kind, text.to_owned());
        }
    }
}

/// The messages a checked declaration's OWN trust debt earns (decision R77):
/// Lean's `sorry` warning for an explicit `sorry` (unless a matched
/// `#guard_msgs` checked it, or Lean suppresses it for a declaration with a
/// synthetic `sorry` and an error), and an error, never silence, for what Lean
/// has no counterpart of: a `trustedArith` / `trustedAy` verdict, and a
/// synthetic `sorry` with no error logged for its declaration.
fn trust_messages(
    dialect: LeanDialect,
    own: &DeclarationTrustSummary,
    guarded: bool,
    has_error: bool,
) -> Vec<(Severity, &'static str, &'static str)> {
    let mut out = Vec::new();
    if own.trusted_axiom_count() > 0 {
        out.push((
            Severity::Error,
            KIND_ANONYMOUS,
            "Clean accepted this declaration only on an unverified decision-procedure verdict \
             (`trustedArith` / `trustedAy`) where Lean checks a proof term; `clean lean` does not \
             report that as accepted",
        ));
    }
    if own.has_explicit_sorry && !guarded && !(own.has_synthetic_sorry && has_error) {
        let text = match dialect {
            LeanDialect::V4_8_0 => "declaration uses 'sorry'",
            LeanDialect::V4_30_0Rc2 => "declaration uses `sorry`",
        };
        out.push((Severity::Warning, KIND_HAS_SORRY, text));
    }
    if own.has_synthetic_sorry && !has_error {
        out.push((
            Severity::Error,
            KIND_ANONYMOUS,
            "Clean could not elaborate part of this declaration and stood a synthetic `sorry` in \
             for it without reporting why; `clean lean` does not report that as accepted",
        ));
    }
    out
}

fn is_guard_msgs(decl: &SurfaceDecl) -> bool {
    matches!(decl, SurfaceDecl::GuardMsgs { .. })
}

/// The byte span of a declaration, or an empty span at 0.
fn span_of(decl: &SurfaceDecl) -> (usize, usize) {
    surface_decl_span(decl).map_or((0, 0), |span| (span.start, span.end))
}

impl ModuleObserver for LeanObserver<'_> {
    fn before_decl(&mut self, _env: &Environment, _index: usize, decl: &SurfaceDecl) {
        let (_, end) = span_of(decl);
        self.members = flatten_members(decl);
        self.leaf_cursor = 0;
        self.command_cursor = 0;
        self.error_anchors.clear();
        self.log_recovery_before(end);
    }

    fn decl_registered(&mut self, decl: &SurfaceDecl, registered: &RegisteredElabResult) {
        let (start, end) = span_of(decl);
        let fallback = Member::whole(decl, start, end);
        self.log_outputs(&fallback, &registered.result);
    }

    fn decl_failed(&mut self, _env: &Environment, decl: &SurfaceDecl, error: &ElabError) {
        let (start, _) = span_of(decl);
        self.log_elab_error(decl, start, error);
    }

    fn leaf_checked(&mut self, env: &Environment, decl: &SurfaceDecl, outcome: &LeafOutcome<'_>) {
        let (start, end) = span_of(decl);
        match outcome {
            LeafOutcome::Failed {
                decl: inner, error, ..
            } => {
                let (inner_start, _) = span_of(inner);
                self.log_elab_error(inner, inner_start, error);
            }
            LeafOutcome::ValidationFailed { name, message } => {
                let member = self
                    .members
                    .iter()
                    .find(|member| member.matches_name(name))
                    .cloned()
                    .unwrap_or_else(|| Member::whole(decl, start, end));
                let range = decl_ref_range(self.source, member.start);
                self.log_error(member.start, range, format!("(kernel) {message}"));
            }
            LeafOutcome::Checked {
                name,
                leaf,
                kernel_failures_delta,
                source_diagnostics,
                ..
            } => {
                let member = self
                    .leaf_member(name, leaf)
                    .or_else(|| self.aux_member(name, start, end))
                    .unwrap_or_else(|| Member::whole(decl, start, end));
                for diagnostic in *source_diagnostics {
                    let anchor = diagnostic.span.map_or(member.start, |span| span.start);
                    let range = decl_ref_range(self.source, anchor);
                    self.log_error(anchor, range, diagnostic.error.to_string());
                }
                if *kernel_failures_delta > 0 {
                    let range = decl_ref_range(self.source, member.start);
                    self.log_error(
                        member.start,
                        range,
                        format!(
                            "(kernel) Clean's kernel rejected {kernel_failures_delta} check(s) \
                             while elaborating this declaration"
                        ),
                    );
                }
                self.log_trust(env, &member, leaf);
            }
            other => {
                let range = decl_ref_range(self.source, start);
                self.log_error(
                    start,
                    range,
                    format!("internal: unclassified outcome {other:?}"),
                );
            }
        }
    }

    fn after_decl(&mut self, _file_ctx: &FileContext, decl: &SurfaceDecl, budget: &BudgetReading) {
        if budget.exhausted {
            // No verdict: whatever the declaration logged may rest on an
            // under-reduced term, so it is replaced by one error.
            let (start, _) = span_of(decl);
            self.pending.retain(|(anchor, _)| *anchor < start);
            let range = decl_ref_range(self.source, start);
            self.log_error(
                start,
                range,
                format!(
                    "(deterministic) timeout: Clean spent its whole per-declaration budget of {} \
                     kernel operations on this declaration",
                    budget.limit
                ),
            );
        }
        self.flush();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn summary(explicit: bool, synthetic: bool, trusted: usize) -> DeclarationTrustSummary {
        DeclarationTrustSummary {
            has_explicit_sorry: explicit,
            has_synthetic_sorry: synthetic,
            trusted_arith_count: trusted,
            trusted_ay_count: 0,
        }
    }

    fn severities(own: &DeclarationTrustSummary, guarded: bool, error: bool) -> Vec<Severity> {
        trust_messages(LeanDialect::V4_8_0, own, guarded, error)
            .into_iter()
            .map(|(severity, _, _)| severity)
            .collect()
    }

    #[test]
    fn test_explicit_sorry_is_leans_warning_per_release() {
        let own = summary(true, false, 0);
        assert_eq!(
            trust_messages(LeanDialect::V4_8_0, &own, false, false),
            vec![(
                Severity::Warning,
                KIND_HAS_SORRY,
                "declaration uses 'sorry'"
            )]
        );
        assert_eq!(
            trust_messages(LeanDialect::V4_30_0Rc2, &own, false, false)[0].2,
            "declaration uses `sorry`"
        );
        // Checked by a matched `#guard_msgs`, it is not logged again.
        assert!(severities(&own, true, false).is_empty());
    }

    #[test]
    fn test_unreported_synthetic_sorry_and_trusted_verdicts_fail_closed() {
        // A synthetic sorry nobody reported is an error, never an acceptance.
        assert_eq!(
            severities(&summary(false, true, 0), false, false),
            vec![Severity::Error]
        );
        // With its error already logged, Lean (and `clean lean`) adds nothing.
        assert!(severities(&summary(false, true, 0), false, true).is_empty());
        assert!(severities(&summary(true, true, 0), false, true).is_empty());
        // A decision procedure's verdict is an error even under `#guard_msgs`.
        assert_eq!(
            severities(&summary(false, false, 1), true, false),
            vec![Severity::Error]
        );
        assert!(severities(&summary(false, false, 0), false, false).is_empty());
    }
}
