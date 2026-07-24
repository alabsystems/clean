// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lightweight SMT-LIB2 builder for the Ay backend.
//!
//! The current `AyBackend` uses ay's native Rust API directly, but proof and
//! interoperability paths still need portable SMT-LIB emission. This module
//! keeps the surface deliberately small: declarations, assertions, basic
//! incremental commands, and response parsing for solver status/model output.

use super::{AyError, AyResult, AySolveResult};
use ay_core::quote_symbol;

/// SMT-LIB dialect selection for downstream solver adapters.
///
/// The command set in this module is portable across all three variants; the
/// enum is retained so callers can choose an explicit target dialect and grow
/// dialect-specific behavior later without changing call sites.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[must_use]
pub enum SmtLibDialect {
    #[default]
    Standard,
    Z3Extension,
    CVC5Extension,
}

/// Solver commands supported by the backend-local SMT-LIB builder.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
pub enum Command {
    DeclareSort {
        name: String,
        arity: u32,
    },
    DeclareFun {
        name: String,
        args: Vec<String>,
        result: String,
    },
    Assert(String),
    CheckSat,
    GetModel,
    Push(u32),
    Pop(u32),
}

impl Command {
    /// Render a command as SMT-LIB2 text.
    #[must_use]
    pub fn to_smtlib2(&self) -> String {
        match self {
            Self::DeclareSort { name, arity } => {
                format!("(declare-sort {} {arity})", quote_symbol(name))
            }
            Self::DeclareFun { name, args, result } => {
                let args = args
                    .iter()
                    .map(|arg| render_sort(arg))
                    .collect::<Vec<_>>()
                    .join(" ");
                format!(
                    "(declare-fun {} ({args}) {})",
                    quote_symbol(name),
                    render_sort(result)
                )
            }
            Self::Assert(formula) => format!("(assert {})", formula.trim()),
            Self::CheckSat => "(check-sat)".to_string(),
            Self::GetModel => "(get-model)".to_string(),
            Self::Push(levels) => format!("(push {levels})"),
            Self::Pop(levels) => format!("(pop {levels})"),
        }
    }
}

/// Portable solver response surface for SMT-LIB execution.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
pub enum SolverResponse {
    Sat { model: Option<String> },
    Unsat,
    Unknown { detail: Option<String> },
    Error(String),
}

impl SolverResponse {
    /// Return the tri-state solve result when the response is not an error.
    #[must_use]
    pub fn solve_result(&self) -> Option<AySolveResult> {
        match self {
            Self::Sat { .. } => Some(AySolveResult::Sat),
            Self::Unsat => Some(AySolveResult::Unsat),
            Self::Unknown { .. } => Some(AySolveResult::Unknown),
            Self::Error(_) => None,
        }
    }
}

/// Builder for backend-local SMT-LIB command sequences.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
pub struct SmtLibBuilder {
    dialect: SmtLibDialect,
    logic: Option<String>,
    commands: Vec<Command>,
}

impl Default for SmtLibBuilder {
    fn default() -> Self {
        Self::new(SmtLibDialect::Standard)
    }
}

impl SmtLibBuilder {
    /// Create an empty builder for the selected dialect.
    pub fn new(dialect: SmtLibDialect) -> Self {
        Self {
            dialect,
            logic: None,
            commands: Vec::new(),
        }
    }

    /// Return the configured dialect.
    pub fn dialect(&self) -> SmtLibDialect {
        self.dialect
    }

    /// Set `(set-logic ...)` for emitted queries.
    pub fn set_logic(&mut self, logic: impl Into<String>) -> &mut Self {
        self.logic = Some(logic.into());
        self
    }

    /// Append a raw command.
    pub fn add_command(&mut self, command: Command) -> &mut Self {
        self.commands.push(command);
        self
    }

    /// Access the currently accumulated commands.
    pub fn commands(&self) -> &[Command] {
        &self.commands
    }

    /// Append `(declare-sort ...)`.
    pub fn declare_sort(&mut self, name: impl Into<String>, arity: u32) -> &mut Self {
        self.add_command(Command::DeclareSort {
            name: name.into(),
            arity,
        })
    }

    /// Append `(declare-fun ...)`.
    pub fn declare_fun(
        &mut self,
        name: impl Into<String>,
        args: Vec<String>,
        result: impl Into<String>,
    ) -> &mut Self {
        self.add_command(Command::DeclareFun {
            name: name.into(),
            args,
            result: result.into(),
        })
    }

    /// Append `(assert ...)`.
    pub fn assert(&mut self, formula: impl Into<String>) -> &mut Self {
        self.add_command(Command::Assert(formula.into()))
    }

    /// Append `(check-sat)`.
    pub fn check_sat(&mut self) -> &mut Self {
        self.add_command(Command::CheckSat)
    }

    /// Append `(get-model)`.
    pub fn get_model(&mut self) -> &mut Self {
        self.add_command(Command::GetModel)
    }

    /// Append `(push N)`.
    pub fn push(&mut self, levels: u32) -> &mut Self {
        self.add_command(Command::Push(levels))
    }

    /// Append `(pop N)`.
    pub fn pop(&mut self, levels: u32) -> &mut Self {
        self.add_command(Command::Pop(levels))
    }

    /// Render the accumulated command sequence as SMT-LIB2 text.
    #[must_use]
    pub fn to_smtlib2(&self) -> String {
        render_lines(self.logic.as_deref(), &self.commands)
    }

    /// Build a standard query from declarations/control commands plus a set of
    /// assertions.
    ///
    /// Any trailing `check-sat`/`get-model` commands already present on the
    /// builder are emitted after the supplied assertions. If no trailing
    /// `check-sat` is present, one is appended automatically.
    #[must_use]
    pub fn build_query<I, S>(&self, assertions: I) -> String
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let split = self
            .commands
            .iter()
            .rposition(|command| !matches!(command, Command::CheckSat | Command::GetModel))
            .map_or(0, |index| index + 1);
        let (prefix, suffix) = self.commands.split_at(split);

        let mut commands = prefix.to_vec();
        commands.extend(
            assertions
                .into_iter()
                .map(|assertion| Command::Assert(assertion.as_ref().trim().to_string())),
        );
        if !suffix
            .iter()
            .any(|command| matches!(command, Command::CheckSat))
        {
            commands.push(Command::CheckSat);
        }
        commands.extend_from_slice(suffix);

        render_lines(self.logic.as_deref(), &commands)
    }
}

/// Parse a solver response from SMT-LIB execution.
///
/// Empty lines, comments, and `success` acknowledgements are ignored. When the
/// status is `sat`, any remaining payload is returned as the model text.
pub fn parse_response(text: &str) -> AyResult<SolverResponse> {
    let mut status = None;
    let mut payload = Vec::new();

    for raw_line in text.lines() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with(';') || line == "success" {
            continue;
        }

        if status.is_none() {
            match line {
                "sat" => status = Some("sat"),
                "unsat" => status = Some("unsat"),
                "unknown" => status = Some("unknown"),
                "unsupported" => {
                    return Ok(SolverResponse::Error("unsupported".to_string()));
                }
                other if other.starts_with("(error") => {
                    return Ok(SolverResponse::Error(parse_error_message(other)));
                }
                other => {
                    return Err(AyError::ScriptError(format!(
                        "unexpected solver response: {other}"
                    )));
                }
            }
        } else {
            payload.push(line.to_string());
        }
    }

    match status {
        Some("sat") => Ok(SolverResponse::Sat {
            model: (!payload.is_empty()).then(|| payload.join("\n")),
        }),
        Some("unsat") => Ok(SolverResponse::Unsat),
        Some("unknown") => Ok(SolverResponse::Unknown {
            detail: (!payload.is_empty()).then(|| payload.join("\n")),
        }),
        _ => Err(AyError::ScriptError(
            "missing SMT-LIB solver status".to_string(),
        )),
    }
}

fn render_lines(logic: Option<&str>, commands: &[Command]) -> String {
    let mut lines = Vec::new();
    if let Some(logic) = logic {
        lines.push(format!("(set-logic {})", logic.trim()));
    }
    lines.extend(commands.iter().map(Command::to_smtlib2));

    if lines.is_empty() {
        String::new()
    } else {
        let mut text = lines.join("\n");
        text.push('\n');
        text
    }
}

fn render_sort(sort: &str) -> String {
    let sort = sort.trim();
    if sort.starts_with('(') {
        sort.to_string()
    } else {
        quote_symbol(sort)
    }
}

fn parse_error_message(line: &str) -> String {
    let trimmed = line.trim();
    if !trimmed.starts_with("(error") {
        return trimmed.to_string();
    }

    trimmed
        .trim_start_matches("(error")
        .trim_end_matches(')')
        .trim()
        .trim_matches('"')
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::{parse_response, Command, SmtLibBuilder, SmtLibDialect, SolverResponse};
    use crate::bridge::ay_backend::{AyError, AySolveResult};

    #[test]
    fn command_rendering_quotes_symbols_and_keeps_sexpr_sorts() {
        assert_eq!(
            Command::DeclareSort {
                name: "bad sort".to_string(),
                arity: 0,
            }
            .to_smtlib2(),
            "(declare-sort |bad sort| 0)"
        );
        assert_eq!(
            Command::DeclareFun {
                name: "bad fun".to_string(),
                args: vec!["(_ BitVec 8)".to_string(), "(Array Int Bool)".to_string()],
                result: "bad result".to_string(),
            }
            .to_smtlib2(),
            "(declare-fun |bad fun| ((_ BitVec 8) (Array Int Bool)) |bad result|)"
        );
    }

    #[test]
    fn builder_build_query_places_assertions_before_terminal_commands() {
        let mut builder = SmtLibBuilder::new(SmtLibDialect::Z3Extension);
        builder
            .set_logic("QF_UF")
            .declare_sort("U", 0)
            .declare_fun("f", vec!["U".to_string()], "U")
            .declare_fun("x", vec![], "U")
            .get_model();

        let query = builder.build_query(["(= (f x) x)", "(not (= x (f x)))"]);

        assert_eq!(
            query,
            "(set-logic QF_UF)\n\
             (declare-sort U 0)\n\
             (declare-fun f (U) U)\n\
             (declare-fun x () U)\n\
             (assert (= (f x) x))\n\
             (assert (not (= x (f x))))\n\
             (check-sat)\n\
             (get-model)\n"
        );
    }

    #[test]
    fn builder_build_query_trims_nested_assertions_without_duplicate_check_sat() {
        let mut builder = SmtLibBuilder::default();
        builder.set_logic("ALL").check_sat().get_model();

        let query =
            builder.build_query(["  (let ((tmp (ite p (f a) (g b)))) (= tmp (h (k a b))))  "]);

        assert_eq!(
            query,
            "(set-logic ALL)\n\
             (assert (let ((tmp (ite p (f a) (g b)))) (= tmp (h (k a b)))))\n\
             (check-sat)\n\
             (get-model)\n"
        );
        assert_eq!(query.matches("(check-sat)\n").count(), 1);
    }

    #[test]
    fn builder_to_smtlib2_preserves_explicit_assertions_and_stack_commands() {
        let mut builder = SmtLibBuilder::new(SmtLibDialect::CVC5Extension);
        builder.push(1).assert("(> x 0)").pop(1).check_sat();

        assert_eq!(builder.commands().len(), 4);
        assert_eq!(
            builder.to_smtlib2(),
            "(push 1)\n(assert (> x 0))\n(pop 1)\n(check-sat)\n"
        );
        assert_eq!(builder.dialect(), SmtLibDialect::CVC5Extension);
    }

    #[test]
    fn parse_sat_response_with_model_and_success_lines() {
        let response =
            parse_response("success\n; satisfiable\nsat\n(model\n  (define-fun x () Int 1)\n)\n")
                .expect("sat response should parse");

        assert_eq!(
            response,
            SolverResponse::Sat {
                model: Some("(model\n(define-fun x () Int 1)\n)".to_string()),
            }
        );
        assert_eq!(response.solve_result(), Some(AySolveResult::Sat));
    }

    #[test]
    fn parse_unsat_and_unknown_responses() {
        assert_eq!(
            parse_response("unsat\n").expect("unsat response should parse"),
            SolverResponse::Unsat
        );
        assert_eq!(
            parse_response("unknown\n(reason-unknown timeout)\n")
                .expect("unknown response should parse"),
            SolverResponse::Unknown {
                detail: Some("(reason-unknown timeout)".to_string()),
            }
        );
    }

    #[test]
    fn parse_sat_response_preserves_nested_model_payload() {
        let response = parse_response(
            "sat\n(model\n  (define-fun f ((x Int)) Int\n    (ite (> x 0)\n      (+ x 1)\n      (let ((y (- x))) y)))\n)\n",
        )
        .expect("nested sat model should parse");

        assert_eq!(
            response,
            SolverResponse::Sat {
                model: Some(
                    "(model\n(define-fun f ((x Int)) Int\n(ite (> x 0)\n(+ x 1)\n(let ((y (- x))) y)))\n)"
                        .to_string()
                ),
            }
        );
    }

    #[test]
    fn parse_solver_errors_and_malformed_output() {
        assert_eq!(
            parse_response("(error \"unknown constant x\")\n")
                .expect("solver error should be interpreted"),
            SolverResponse::Error("unknown constant x".to_string())
        );
        assert_eq!(
            parse_response("unsupported\n").expect("unsupported should be interpreted"),
            SolverResponse::Error("unsupported".to_string())
        );
        assert!(matches!(
            parse_response("(model)\n").expect_err("model without status should fail"),
            AyError::ScriptError(message) if message == "unexpected solver response: (model)"
        ));
        assert!(matches!(
            parse_response("check-sat\n").expect_err("unknown command should fail"),
            AyError::ScriptError(message) if message == "unexpected solver response: check-sat"
        ));
        assert!(matches!(
            parse_response("success\n; still no status\n").expect_err("missing status should fail"),
            AyError::ScriptError(message) if message == "missing SMT-LIB solver status"
        ));
    }
}
