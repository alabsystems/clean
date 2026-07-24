// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended tactic interpreter with replay, backtracking, tracing, and registry hooks.

use super::core::{ProofState, TacticError, TacticResult};
use super::script_runner::{comment_strip, execute_simple_tactic};
use std::collections::{HashMap, VecDeque};
use std::time::{Duration, Instant};
use thiserror::Error;

pub(crate) type TacticHandler = Box<dyn Fn(&mut ProofState) -> TacticResult + Send + Sync>;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct TacticTrace {
    pub(crate) name: String,
    pub(crate) duration: Duration,
    pub(crate) success: bool,
    pub(crate) children: Vec<TacticTrace>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct InterpConfig {
    pub(crate) fuel: usize,
    pub(crate) enable_tracing: bool,
    pub(crate) timeout: Option<Duration>,
}

impl Default for InterpConfig {
    /// Build the default interpreter configuration.
    fn default() -> Self {
        Self {
            fuel: 1_024,
            enable_tracing: false,
            timeout: None,
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct StateSnapshot {
    state: ProofState,
}

impl StateSnapshot {
    /// Capture the current proof state.
    pub(crate) fn capture(state: &ProofState) -> Self {
        Self {
            state: state.clone(),
        }
    }

    /// Restore the saved proof state.
    pub(crate) fn restore(&self, state: &mut ProofState) {
        *state = self.state.clone();
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub(crate) struct TacticStackFrame {
    pub(crate) tactic: String,
    pub(crate) depth: usize,
}

#[derive(Debug, Clone, Error)]
#[error("{source}")]
pub(crate) struct StructuredTacticError {
    pub(crate) source: TacticError,
    pub(crate) stack: Vec<TacticStackFrame>,
}

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub(crate) enum ScriptParseError {
    #[error("unbalanced delimiter")]
    UnbalancedDelimiter,
    #[error("{combinator}: missing body")]
    MissingBody { combinator: String },
    #[error("repeat: invalid max_iters '{value}'")]
    InvalidRepeatLimit { value: String },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TacticScript {
    Atom(String, Vec<String>),
    Seq(Vec<TacticScript>),
    First(Vec<TacticScript>),
    Repeat {
        body: Box<TacticScript>,
        max_iters: Option<usize>,
    },
    Try(Box<TacticScript>),
    AllGoals(Box<TacticScript>),
    AnyGoals(Box<TacticScript>),
    Focus(Box<TacticScript>),
}

#[derive(Debug, Clone)]
struct ActiveTrace {
    name: String,
    started_at: Instant,
    children: Vec<TacticTrace>,
}

pub(crate) struct ExtTacticInterpreter {
    config: InterpConfig,
    registry: HashMap<String, TacticHandler>,
    traces: Vec<TacticTrace>,
    trace_stack: Vec<ActiveTrace>,
    stack: Vec<TacticStackFrame>,
    last_error: Option<StructuredTacticError>,
    remaining_fuel: usize,
    run_started_at: Option<Instant>,
    run_depth: usize,
}

impl ExtTacticInterpreter {
    /// Create a new interpreter.
    pub(crate) fn new(config: InterpConfig) -> Self {
        Self {
            config,
            registry: HashMap::new(),
            traces: Vec::new(),
            trace_stack: Vec::new(),
            stack: Vec::new(),
            last_error: None,
            remaining_fuel: config.fuel,
            run_started_at: None,
            run_depth: 0,
        }
    }

    /// Return a copy with a different fuel budget.
    pub(crate) fn with_fuel(mut self, fuel: usize) -> Self {
        self.config.fuel = fuel;
        self
    }

    /// Register a custom tactic by name.
    pub(crate) fn register_tactic(&mut self, name: impl Into<String>, handler: TacticHandler) {
        self.registry.insert(name.into(), handler);
    }

    /// Look up a custom tactic by name.
    pub(crate) fn lookup_tactic(&self, name: &str) -> Option<&TacticHandler> {
        self.registry.get(name)
    }

    /// Return the trace forest from the last run.
    pub(crate) fn trace(&self) -> &[TacticTrace] {
        &self.traces
    }

    /// Return the last structured error, if any.
    pub(crate) fn last_error(&self) -> Option<&StructuredTacticError> {
        self.last_error.as_ref()
    }

    /// Parse a replay script into an AST.
    pub(crate) fn parse_script(script: &str) -> Result<TacticScript, TacticError> {
        parse_tactic_script(script).map_err(|err| TacticError::ParseFailed {
            tactic: "script".to_string(),
            detail: err.to_string(),
        })
    }

    /// Execute a closure and restore the saved state on failure.
    pub(crate) fn execute_with_backtrack<F>(
        &mut self,
        state: &mut ProofState,
        tactic_fn: F,
    ) -> TacticResult
    where
        F: FnOnce(&mut ProofState) -> TacticResult,
    {
        let snapshot = StateSnapshot::capture(state);
        match tactic_fn(state) {
            Ok(()) => {
                state.prune_solved_goals();
                Ok(())
            }
            Err(err) => {
                snapshot.restore(state);
                Err(err)
            }
        }
    }

    /// Execute `first`, trying tactics in order with rollback.
    pub(crate) fn execute_first(
        &mut self,
        state: &mut ProofState,
        tactics: &[TacticScript],
    ) -> TacticResult {
        self.run_named("first".to_string(), state, |this, state| {
            for tactic in tactics {
                match this.execute_branch(state, tactic) {
                    Ok(()) => return Ok(()),
                    Err(err) if is_fatal_error(&err) => return Err(err),
                    Err(_) => {}
                }
            }
            Err(TacticError::AllTacticsFailed {
                combinator: "first".to_string(),
            })
        })
    }

    /// Execute `repeat`, stopping at the first non-fatal failure.
    pub(crate) fn execute_repeat(
        &mut self,
        state: &mut ProofState,
        tactic: &TacticScript,
        max_iters: Option<usize>,
    ) -> TacticResult {
        let name = max_iters
            .map(|n| format!("repeat[{n}]"))
            .unwrap_or_else(|| "repeat".to_string());
        self.run_named(name, state, |this, state| {
            let mut iterations = 0usize;
            while max_iters.is_none_or(|limit| iterations < limit) {
                match this.execute_branch(state, tactic) {
                    Ok(()) => {
                        iterations += 1;
                        if state.is_complete() {
                            break;
                        }
                    }
                    Err(err) if is_fatal_error(&err) => return Err(err),
                    Err(_) => break,
                }
            }
            Ok(())
        })
    }

    /// Execute `try`, swallowing non-fatal failures.
    pub(crate) fn execute_try(
        &mut self,
        state: &mut ProofState,
        tactic: &TacticScript,
    ) -> TacticResult {
        self.run_named("try".to_string(), state, |this, state| {
            match this.execute_branch(state, tactic) {
                Ok(()) | Err(TacticError::NoGoals) => Ok(()),
                Err(err) if is_fatal_error(&err) => Err(err),
                Err(_) => Ok(()),
            }
        })
    }

    /// Execute `all_goals` on the original goals.
    pub(crate) fn execute_all_goals(
        &mut self,
        state: &mut ProofState,
        tactic: &TacticScript,
    ) -> TacticResult {
        self.run_named("all_goals".to_string(), state, |this, state| {
            let snapshot = StateSnapshot::capture(state);
            let original = state.goals.clone().into_iter().collect::<Vec<_>>();
            let mut next_goals = VecDeque::new();
            // PARALLEL sibling goals must allocate binder FVars from a shared base
            // so the id↔nesting-depth correspondence `close_fvars` relies on holds.
            // See `compound_seq_focus` (builtins_compound.rs) for the rationale.
            let branch_fvar_base = state.next_fvar;
            let mut branch_fvar_max = branch_fvar_base;
            for goal in original {
                state.next_fvar = branch_fvar_base;
                let mut focused = state.clone_with_goal(goal);
                if let Err(err) = this.execute_script(&mut focused, tactic) {
                    snapshot.restore(state);
                    return Err(err);
                }
                branch_fvar_max = branch_fvar_max.max(focused.next_fvar);
                state.merge_meta_state(&focused);
                next_goals.extend(focused.goals);
            }
            state.next_fvar = branch_fvar_max;
            state.goals = next_goals;
            state.prune_solved_goals();
            Ok(())
        })
    }

    /// Execute `any_goals`, keeping successful changes and untouched failures.
    pub(crate) fn execute_any_goals(
        &mut self,
        state: &mut ProofState,
        tactic: &TacticScript,
    ) -> TacticResult {
        self.run_named("any_goals".to_string(), state, |this, state| {
            let snapshot = StateSnapshot::capture(state);
            let original = state.goals.clone().into_iter().collect::<Vec<_>>();
            let mut next_goals = VecDeque::new();
            let mut any_succeeded = false;
            // Per-branch `next_fvar` reset for PARALLEL sibling goals — keeps the
            // FVar id↔binder-depth correspondence `close_fvars` assumes. See
            // `compound_seq_focus` (builtins_compound.rs) for the rationale.
            let branch_fvar_base = state.next_fvar;
            let mut branch_fvar_max = branch_fvar_base;
            for goal in original {
                state.next_fvar = branch_fvar_base;
                let mut focused = state.clone_with_goal(goal.clone());
                match this.execute_script(&mut focused, tactic) {
                    Ok(()) => {
                        any_succeeded = true;
                        branch_fvar_max = branch_fvar_max.max(focused.next_fvar);
                        state.merge_meta_state(&focused);
                        next_goals.extend(focused.goals);
                    }
                    Err(err) if is_fatal_error(&err) => {
                        snapshot.restore(state);
                        return Err(err);
                    }
                    Err(_) => next_goals.push_back(goal),
                }
            }
            state.next_fvar = branch_fvar_max;
            if !any_succeeded {
                snapshot.restore(state);
                return Err(TacticError::AllTacticsFailed {
                    combinator: "any_goals".to_string(),
                });
            }
            state.goals = next_goals;
            state.prune_solved_goals();
            Ok(())
        })
    }

    /// Execute `focus` on the first goal only.
    pub(crate) fn execute_focus(
        &mut self,
        state: &mut ProofState,
        tactic: &TacticScript,
    ) -> TacticResult {
        self.run_named("focus".to_string(), state, |this, state| {
            let goal = state.current_goal().cloned().ok_or(TacticError::NoGoals)?;
            let rest = state.goals.iter().skip(1).cloned().collect::<VecDeque<_>>();
            let snapshot = StateSnapshot::capture(state);
            let mut focused = state.clone_with_goal(goal);
            match this.execute_script(&mut focused, tactic) {
                Ok(()) => {
                    state.merge_meta_state(&focused);
                    state.goals = focused.goals;
                    state.goals.extend(rest);
                    state.prune_solved_goals();
                    Ok(())
                }
                Err(err) => {
                    snapshot.restore(state);
                    Err(err)
                }
            }
        })
    }

    /// Parse and execute a replay script.
    pub(crate) fn run_script(&mut self, state: &mut ProofState, script: &str) -> TacticResult {
        let parsed = Self::parse_script(script).inspect_err(|err| {
            self.last_error = Some(StructuredTacticError {
                source: err.clone(),
                stack: Vec::new(),
            });
        })?;
        self.execute_script(state, &parsed)
    }

    /// Execute a parsed script node.
    fn execute_script(&mut self, state: &mut ProofState, script: &TacticScript) -> TacticResult {
        self.run_named(script_name(script), state, |this, state| match script {
            TacticScript::Atom(name, args) => this.execute_atom(state, name, args),
            TacticScript::Seq(items) => {
                for item in items {
                    this.execute_script(state, item)?;
                }
                Ok(())
            }
            TacticScript::First(items) => this.execute_first(state, items),
            TacticScript::Repeat { body, max_iters } => {
                this.execute_repeat(state, body, *max_iters)
            }
            TacticScript::Try(body) => this.execute_try(state, body),
            TacticScript::AllGoals(body) => this.execute_all_goals(state, body),
            TacticScript::AnyGoals(body) => this.execute_any_goals(state, body),
            TacticScript::Focus(body) => this.execute_focus(state, body),
        })
    }

    /// Execute a script branch with rollback on failure.
    fn execute_branch(&mut self, state: &mut ProofState, script: &TacticScript) -> TacticResult {
        let snapshot = StateSnapshot::capture(state);
        match self.execute_script(state, script) {
            Ok(()) => Ok(()),
            Err(err) => {
                snapshot.restore(state);
                Err(err)
            }
        }
    }

    /// Execute one atomic tactic.
    fn execute_atom(
        &mut self,
        state: &mut ProofState,
        name: &str,
        args: &[String],
    ) -> TacticResult {
        if let Some(handler) = self.lookup_tactic(name) {
            if !args.is_empty() {
                return Err(TacticError::ParseFailed {
                    tactic: name.to_string(),
                    detail: "custom tactics do not accept script arguments".to_string(),
                });
            }
            handler(state)?;
            state.prune_solved_goals();
            return Ok(());
        }
        let env = state.env().clone();
        execute_simple_tactic(state, &render_atom(name, args), &env).map_err(|err| match err {
            TacticError::UnknownIdent(_) => TacticError::UnknownTactic(name.to_string()),
            other => other,
        })
    }

    /// Run one named node under tracing and budget control.
    fn run_named<F>(&mut self, name: String, state: &mut ProofState, f: F) -> TacticResult
    where
        F: FnOnce(&mut Self, &mut ProofState) -> TacticResult,
    {
        let outermost = self.run_depth == 0;
        if outermost {
            self.traces.clear();
            self.trace_stack.clear();
            self.stack.clear();
            self.last_error = None;
            self.remaining_fuel = self.config.fuel;
            self.run_started_at = Some(Instant::now());
        }
        self.run_depth += 1;
        self.stack.push(TacticStackFrame {
            tactic: name.clone(),
            depth: self.stack.len(),
        });
        if self.config.enable_tracing {
            self.trace_stack.push(ActiveTrace {
                name,
                started_at: Instant::now(),
                children: Vec::new(),
            });
        }
        let result = self.consume_step().and_then(|()| f(self, state));
        let error_stack = result.as_ref().err().map(|_| self.stack.clone());
        if let Some(frame) = self.trace_stack.pop() {
            let trace = TacticTrace {
                name: frame.name,
                duration: frame.started_at.elapsed(),
                success: result.is_ok(),
                children: frame.children,
            };
            if let Some(parent) = self.trace_stack.last_mut() {
                parent.children.push(trace);
            } else {
                self.traces.push(trace);
            }
        }
        let _ = self.stack.pop();
        self.run_depth = self.run_depth.saturating_sub(1);
        if let (Err(err), Some(stack)) = (&result, error_stack) {
            self.last_error = Some(StructuredTacticError {
                source: err.clone(),
                stack,
            });
        } else if outermost {
            self.last_error = None;
        }
        if outermost {
            self.run_started_at = None;
            self.trace_stack.clear();
            self.stack.clear();
        }
        result
    }

    /// Consume one execution step and enforce fuel and timeout limits.
    fn consume_step(&mut self) -> TacticResult {
        if self.remaining_fuel == 0 {
            return Err(TacticError::Timeout {
                detail: format!("fuel exhausted after {} steps", self.config.fuel),
            });
        }
        self.remaining_fuel -= 1;
        if let (Some(started_at), Some(timeout)) = (self.run_started_at, self.config.timeout) {
            if started_at.elapsed() > timeout {
                return Err(TacticError::Timeout {
                    detail: format!("timeout exceeded after {:?}", timeout),
                });
            }
        }
        Ok(())
    }
}

/// Return whether an error should abort combinator backtracking.
fn is_fatal_error(err: &TacticError) -> bool {
    matches!(err, TacticError::Timeout { .. })
}

/// Render an atomic tactic back into script form.
fn render_atom(name: &str, args: &[String]) -> String {
    if args.is_empty() {
        name.to_string()
    } else {
        format!("{name} {}", args.join(" "))
    }
}

/// Render a stable name for a script node.
fn script_name(script: &TacticScript) -> String {
    match script {
        TacticScript::Atom(name, args) => render_atom(name, args),
        TacticScript::Seq(_) => "seq".to_string(),
        TacticScript::First(_) => "first".to_string(),
        TacticScript::Repeat { max_iters, .. } => max_iters
            .map(|n| format!("repeat[{n}]"))
            .unwrap_or_else(|| "repeat".to_string()),
        TacticScript::Try(_) => "try".to_string(),
        TacticScript::AllGoals(_) => "all_goals".to_string(),
        TacticScript::AnyGoals(_) => "any_goals".to_string(),
        TacticScript::Focus(_) => "focus".to_string(),
    }
}

/// Parse a tactic script string.
fn parse_tactic_script(script: &str) -> Result<TacticScript, ScriptParseError> {
    let stripped = comment_strip::strip_block_comments(script);
    let cleaned = stripped
        .lines()
        .map(strip_line_comment)
        .collect::<Vec<_>>()
        .join("\n");
    parse_expr(&cleaned)
}

/// Strip a `--` line comment.
fn strip_line_comment(line: &str) -> &str {
    match line.find("--") {
        Some(idx) => &line[..idx],
        None => line,
    }
}

/// Parse one script expression.
fn parse_expr(input: &str) -> Result<TacticScript, ScriptParseError> {
    let input = strip_group(input.trim())?;
    let parts = split_top_level(input, ';')?;
    if parts.len() > 1 {
        return Ok(TacticScript::Seq(
            parts
                .into_iter()
                .map(|part| parse_expr(&part))
                .collect::<Result<Vec<_>, _>>()?,
        ));
    }
    parse_term(input)
}

/// Parse one non-sequence term.
fn parse_term(input: &str) -> Result<TacticScript, ScriptParseError> {
    if let Some(rest) = strip_keyword(input, "first") {
        let rest = strip_group(rest.trim_start_matches('|').trim())?;
        if rest.is_empty() {
            return Err(ScriptParseError::MissingBody {
                combinator: "first".to_string(),
            });
        }
        return Ok(TacticScript::First(
            split_top_level(rest, '|')?
                .into_iter()
                .map(|part| parse_expr(&part))
                .collect::<Result<Vec<_>, _>>()?,
        ));
    }
    if let Some(rest) = strip_keyword(input, "repeat") {
        let (max_iters, body) = parse_repeat(rest)?;
        return Ok(TacticScript::Repeat {
            body: Box::new(parse_expr(body)?),
            max_iters,
        });
    }
    if let Some(rest) = strip_keyword(input, "try") {
        return Ok(TacticScript::Try(Box::new(parse_body("try", rest)?)));
    }
    if let Some(rest) = strip_keyword(input, "all_goals") {
        return Ok(TacticScript::AllGoals(Box::new(parse_body(
            "all_goals",
            rest,
        )?)));
    }
    if let Some(rest) = strip_keyword(input, "any_goals") {
        return Ok(TacticScript::AnyGoals(Box::new(parse_body(
            "any_goals",
            rest,
        )?)));
    }
    if let Some(rest) = strip_keyword(input, "focus") {
        return Ok(TacticScript::Focus(Box::new(parse_body("focus", rest)?)));
    }
    let tokens = split_tokens(input);
    Ok(match tokens.split_first() {
        Some((name, args)) => TacticScript::Atom(name.clone(), args.to_vec()),
        None => TacticScript::Seq(Vec::new()),
    })
}

/// Parse the body of a unary combinator.
fn parse_body(combinator: &str, rest: &str) -> Result<TacticScript, ScriptParseError> {
    let body = strip_group(rest.trim())?;
    if body.is_empty() {
        return Err(ScriptParseError::MissingBody {
            combinator: combinator.to_string(),
        });
    }
    parse_expr(body)
}

/// Parse the optional `repeat[n]` header.
fn parse_repeat(rest: &str) -> Result<(Option<usize>, &str), ScriptParseError> {
    let rest = rest.trim();
    if !rest.starts_with('[') {
        if rest.is_empty() {
            return Err(ScriptParseError::MissingBody {
                combinator: "repeat".to_string(),
            });
        }
        return Ok((None, rest));
    }
    let close = find_matching(rest, 0, '[', ']')?;
    let raw = rest[1..close].trim();
    let max_iters = raw
        .parse::<usize>()
        .map_err(|_| ScriptParseError::InvalidRepeatLimit {
            value: raw.to_string(),
        })?;
    let body = rest[close + 1..].trim();
    if body.is_empty() {
        return Err(ScriptParseError::MissingBody {
            combinator: "repeat".to_string(),
        });
    }
    Ok((Some(max_iters), body))
}

/// Strip one wrapping delimiter pair when it covers the full input.
fn strip_group(input: &str) -> Result<&str, ScriptParseError> {
    if input.len() < 2 {
        return Ok(input);
    }
    for (open, close) in [('(', ')'), ('[', ']'), ('{', '}')] {
        if input.starts_with(open) && find_matching(input, 0, open, close)? + 1 == input.len() {
            return Ok(input[1..input.len() - 1].trim());
        }
    }
    Ok(input)
}

/// Split on a delimiter that appears at depth zero.
fn split_top_level(input: &str, delimiter: char) -> Result<Vec<String>, ScriptParseError> {
    let (mut parts, mut start, mut paren, mut bracket, mut brace, mut in_quote) =
        (Vec::new(), 0usize, 0usize, 0usize, 0usize, false);
    for (idx, ch) in input.char_indices() {
        match ch {
            '"' => in_quote = !in_quote,
            '(' if !in_quote => paren += 1,
            '[' if !in_quote => bracket += 1,
            '{' if !in_quote => brace += 1,
            ')' if !in_quote => {
                paren = paren
                    .checked_sub(1)
                    .ok_or(ScriptParseError::UnbalancedDelimiter)?
            }
            ']' if !in_quote => {
                bracket = bracket
                    .checked_sub(1)
                    .ok_or(ScriptParseError::UnbalancedDelimiter)?
            }
            '}' if !in_quote => {
                brace = brace
                    .checked_sub(1)
                    .ok_or(ScriptParseError::UnbalancedDelimiter)?
            }
            _ => {}
        }
        if ch == delimiter && !in_quote && paren == 0 && bracket == 0 && brace == 0 {
            parts.push(input[start..idx].trim().to_string());
            start = idx + ch.len_utf8();
        }
    }
    if in_quote || paren != 0 || bracket != 0 || brace != 0 {
        return Err(ScriptParseError::UnbalancedDelimiter);
    }
    parts.push(input[start..].trim().to_string());
    Ok(parts.into_iter().filter(|part| !part.is_empty()).collect())
}

/// Split one atomic tactic into tokens, preserving quoted strings.
fn split_tokens(input: &str) -> Vec<String> {
    let (mut tokens, mut current, mut in_quote) = (Vec::new(), String::new(), false);
    for ch in input.chars() {
        match ch {
            '"' => in_quote = !in_quote,
            c if c.is_whitespace() && !in_quote => {
                if !current.is_empty() {
                    tokens.push(std::mem::take(&mut current));
                }
            }
            _ => current.push(ch),
        }
    }
    if !current.is_empty() {
        tokens.push(current);
    }
    tokens
}

/// Match a combinator keyword at the start of the input.
fn strip_keyword<'a>(input: &'a str, keyword: &str) -> Option<&'a str> {
    let rest = input.strip_prefix(keyword)?;
    match rest.chars().next() {
        None => Some(rest),
        Some(ch) if ch.is_whitespace() || matches!(ch, '(' | '[' | '{' | '|') => Some(rest),
        Some(_) => None,
    }
}

/// Find the matching closing delimiter for a leading opener.
fn find_matching(
    input: &str,
    start: usize,
    open: char,
    close: char,
) -> Result<usize, ScriptParseError> {
    let (mut depth, mut in_quote) = (0usize, false);
    for (idx, ch) in input.char_indices().skip_while(|(idx, _)| *idx < start) {
        match ch {
            '"' => in_quote = !in_quote,
            c if c == open && !in_quote => depth += 1,
            c if c == close && !in_quote => {
                depth = depth
                    .checked_sub(1)
                    .ok_or(ScriptParseError::UnbalancedDelimiter)?;
                if depth == 0 {
                    return Ok(idx);
                }
            }
            _ => {}
        }
    }
    Err(ScriptParseError::UnbalancedDelimiter)
}
