// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Typed SMT-LIB 2 builder for portable text emission.
//!
//! This module provides a small typed AST for SMT-LIB sorts, expressions, and
//! commands together with a builder that renders command sequences to
//! SMT-LIB2-compatible text.

use thiserror::Error;

/// A sequence builder for SMT-LIB2 commands.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SmtLibBuilder {
    commands: Vec<SmtLibCommand>,
}

impl SmtLibBuilder {
    /// Create an empty SMT-LIB builder.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Access the accumulated command sequence.
    #[must_use]
    pub fn commands(&self) -> &[SmtLibCommand] {
        &self.commands
    }

    /// Append a command to the SMT-LIB script.
    pub fn add_command(&mut self, command: SmtLibCommand) -> &mut Self {
        self.commands.push(command);
        self
    }

    /// Append `(set-logic ...)`.
    pub fn set_logic(&mut self, logic: impl Into<String>) -> &mut Self {
        self.add_command(SmtLibCommand::SetLogic(logic.into()))
    }

    /// Append `(declare-sort ...)`.
    pub fn declare_sort(&mut self, name: impl Into<String>, arity: u32) -> &mut Self {
        self.add_command(SmtLibCommand::DeclareSort {
            name: name.into(),
            arity,
        })
    }

    /// Append `(declare-fun ...)`.
    pub fn declare_fun(
        &mut self,
        name: impl Into<String>,
        args: Vec<SmtLibSort>,
        result: SmtLibSort,
    ) -> &mut Self {
        self.add_command(SmtLibCommand::DeclareFun {
            name: name.into(),
            args,
            result,
        })
    }

    /// Append `(define-fun ...)`.
    pub fn define_fun(
        &mut self,
        name: impl Into<String>,
        params: Vec<(String, SmtLibSort)>,
        result: SmtLibSort,
        body: SmtLibExpr,
    ) -> &mut Self {
        self.add_command(SmtLibCommand::DefineFun {
            name: name.into(),
            params,
            result,
            body,
        })
    }

    /// Append `(assert ...)`.
    pub fn assert_expr(&mut self, expr: SmtLibExpr) -> &mut Self {
        self.add_command(SmtLibCommand::Assert(expr))
    }

    /// Append `(check-sat)`.
    pub fn check_sat(&mut self) -> &mut Self {
        self.add_command(SmtLibCommand::CheckSat)
    }

    /// Append `(get-model)`.
    pub fn get_model(&mut self) -> &mut Self {
        self.add_command(SmtLibCommand::GetModel)
    }

    /// Append `(push N)`.
    pub fn push_scope(&mut self, levels: u32) -> &mut Self {
        self.add_command(SmtLibCommand::Push(levels))
    }

    /// Append `(pop N)`.
    pub fn pop_scope(&mut self, levels: u32) -> &mut Self {
        self.add_command(SmtLibCommand::Pop(levels))
    }

    /// Render the accumulated command sequence as SMT-LIB2 text.
    #[must_use]
    pub fn to_smtlib2(&self) -> String {
        if self.commands.is_empty() {
            String::new()
        } else {
            let mut text = self
                .commands
                .iter()
                .map(SmtLibCommand::to_smtlib2)
                .collect::<Vec<_>>()
                .join("\n");
            text.push('\n');
            text
        }
    }
}

/// SMT-LIB sort surface forms supported by the text builder.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SmtLibSort {
    Bool,
    Int,
    Real,
    BitVec(u32),
    Array(Box<SmtLibSort>, Box<SmtLibSort>),
    Uninterpreted(String),
}

impl SmtLibSort {
    /// Render the sort as SMT-LIB2 text.
    #[must_use]
    pub fn to_smtlib2(&self) -> String {
        match self {
            Self::Bool => "Bool".to_string(),
            Self::Int => "Int".to_string(),
            Self::Real => "Real".to_string(),
            Self::BitVec(width) => format!("(_ BitVec {width})"),
            Self::Array(domain, range) => {
                format!("(Array {} {})", domain.to_smtlib2(), range.to_smtlib2())
            }
            Self::Uninterpreted(name) => quote_symbol(name),
        }
    }
}

/// SMT-LIB constant surface forms supported by the text builder.
///
/// Numeric values are stored as strings to preserve exact textual spelling
/// (for example large integers, rationals, or solver-specific decimal forms).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SmtLibConst {
    Bool(bool),
    Int(String),
    Real(String),
    BitVec { value: String, width: u32 },
    String(String),
}

impl SmtLibConst {
    /// Render the constant as SMT-LIB2 text.
    #[must_use]
    pub fn to_smtlib2(&self) -> String {
        match self {
            Self::Bool(true) => "true".to_string(),
            Self::Bool(false) => "false".to_string(),
            Self::Int(value) | Self::Real(value) => value.clone(),
            Self::BitVec { value, width } => format!("(_ bv{value} {width})"),
            Self::String(value) => string_literal(value),
        }
    }
}

/// SMT-LIB expression surface forms supported by the text builder.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SmtLibExpr {
    Var(String),
    Const(SmtLibConst),
    Apply(String, Vec<SmtLibExpr>),
    Let(Vec<(String, SmtLibExpr)>, Box<SmtLibExpr>),
    Forall(Vec<(String, SmtLibSort)>, Box<SmtLibExpr>),
    Exists(Vec<(String, SmtLibSort)>, Box<SmtLibExpr>),
}

impl SmtLibExpr {
    /// Render the expression as SMT-LIB2 text.
    #[must_use]
    pub fn to_smtlib2(&self) -> String {
        match self {
            Self::Var(name) => quote_symbol(name),
            Self::Const(constant) => constant.to_smtlib2(),
            Self::Apply(name, args) => {
                if args.is_empty() {
                    quote_symbol(name)
                } else {
                    let args = args
                        .iter()
                        .map(SmtLibExpr::to_smtlib2)
                        .collect::<Vec<_>>()
                        .join(" ");
                    format!("({} {args})", quote_symbol(name))
                }
            }
            Self::Let(bindings, body) => {
                let bindings = bindings
                    .iter()
                    .map(|(name, expr)| format!("({} {})", quote_symbol(name), expr.to_smtlib2()))
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("(let ({bindings}) {})", body.to_smtlib2())
            }
            Self::Forall(vars, body) => {
                format!(
                    "(forall ({}) {})",
                    render_sorted_vars(vars),
                    body.to_smtlib2()
                )
            }
            Self::Exists(vars, body) => {
                format!(
                    "(exists ({}) {})",
                    render_sorted_vars(vars),
                    body.to_smtlib2()
                )
            }
        }
    }
}

/// SMT-LIB command surface forms supported by the text builder.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SmtLibCommand {
    SetLogic(String),
    DeclareSort {
        name: String,
        arity: u32,
    },
    DeclareFun {
        name: String,
        args: Vec<SmtLibSort>,
        result: SmtLibSort,
    },
    DefineFun {
        name: String,
        params: Vec<(String, SmtLibSort)>,
        result: SmtLibSort,
        body: SmtLibExpr,
    },
    Assert(SmtLibExpr),
    CheckSat,
    GetModel,
    Push(u32),
    Pop(u32),
}

impl SmtLibCommand {
    /// Render the command as SMT-LIB2 text.
    #[must_use]
    pub fn to_smtlib2(&self) -> String {
        match self {
            Self::SetLogic(logic) => format!("(set-logic {})", quote_symbol(logic)),
            Self::DeclareSort { name, arity } => {
                format!("(declare-sort {} {arity})", quote_symbol(name))
            }
            Self::DeclareFun { name, args, result } => {
                let args = args
                    .iter()
                    .map(SmtLibSort::to_smtlib2)
                    .collect::<Vec<_>>()
                    .join(" ");
                format!(
                    "(declare-fun {} ({args}) {})",
                    quote_symbol(name),
                    result.to_smtlib2()
                )
            }
            Self::DefineFun {
                name,
                params,
                result,
                body,
            } => format!(
                "(define-fun {} ({}) {} {})",
                quote_symbol(name),
                render_sorted_vars(params),
                result.to_smtlib2(),
                body.to_smtlib2()
            ),
            Self::Assert(expr) => format!("(assert {})", expr.to_smtlib2()),
            Self::CheckSat => "(check-sat)".to_string(),
            Self::GetModel => "(get-model)".to_string(),
            Self::Push(levels) => format!("(push {levels})"),
            Self::Pop(levels) => format!("(pop {levels})"),
        }
    }
}

/// Result of parsing an SMT-LIB2 `check-sat` response.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SmtLibCheckSatResult {
    Sat,
    Unsat,
    Unknown,
}

/// Errors returned when parsing solver result text.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum ParseSmtLib2ResultError {
    #[error("SMT-LIB2 result did not contain sat/unsat/unknown")]
    MissingStatus,

    #[error("unexpected SMT-LIB2 result line: {0}")]
    UnexpectedLine(String),
}

/// Parse the `sat` / `unsat` / `unknown` status from SMT-LIB2 solver output.
///
/// Leading empty lines, comments, and `success` acknowledgements are ignored.
/// If the solver emits additional payload after the status (for example a
/// model), the first status line is returned.
pub fn parse_smtlib2_result(text: &str) -> Result<SmtLibCheckSatResult, ParseSmtLib2ResultError> {
    for raw_line in text.lines() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with(';') || line == "success" {
            continue;
        }

        return match line {
            "sat" => Ok(SmtLibCheckSatResult::Sat),
            "unsat" => Ok(SmtLibCheckSatResult::Unsat),
            "unknown" => Ok(SmtLibCheckSatResult::Unknown),
            other => Err(ParseSmtLib2ResultError::UnexpectedLine(other.to_string())),
        };
    }

    Err(ParseSmtLib2ResultError::MissingStatus)
}

fn render_sorted_vars(vars: &[(String, SmtLibSort)]) -> String {
    vars.iter()
        .map(|(name, sort)| format!("({} {})", quote_symbol(name), sort.to_smtlib2()))
        .collect::<Vec<_>>()
        .join(" ")
}

fn quote_symbol(name: &str) -> String {
    const RESERVED: &[&str] = &[
        "true",
        "false",
        "let",
        "forall",
        "exists",
        "match",
        "par",
        "_",
        "!",
        "as",
        "BINARY",
        "DECIMAL",
        "HEXADECIMAL",
        "NUMERAL",
        "STRING",
        "assert",
        "check-sat",
        "check-sat-assuming",
        "declare-const",
        "declare-datatype",
        "declare-datatypes",
        "declare-fun",
        "declare-sort",
        "define-fun",
        "define-fun-rec",
        "define-funs-rec",
        "define-sort",
        "echo",
        "exit",
        "get-assertions",
        "get-assignment",
        "get-info",
        "get-model",
        "get-option",
        "get-proof",
        "get-unsat-assumptions",
        "get-unsat-core",
        "get-value",
        "pop",
        "push",
        "reset",
        "reset-assertions",
        "set-info",
        "set-logic",
        "set-option",
    ];

    let needs_quoting = name.is_empty()
        || name.starts_with(|c: char| c.is_ascii_digit())
        || RESERVED.contains(&name)
        || name.contains(|c: char| !is_symbol_char(c));

    if needs_quoting {
        let sanitized = name
            .chars()
            .map(|c| if c == '|' || c == '\\' { '_' } else { c })
            .collect::<String>();
        format!("|{sanitized}|")
    } else {
        name.to_string()
    }
}

fn is_symbol_char(c: char) -> bool {
    c.is_ascii_alphanumeric()
        || matches!(
            c,
            '+' | '-'
                | '/'
                | '*'
                | '='
                | '%'
                | '?'
                | '!'
                | '.'
                | '$'
                | '_'
                | '~'
                | '&'
                | '^'
                | '<'
                | '>'
                | '@'
        )
}

fn string_literal(value: &str) -> String {
    let escaped = value.replace('"', "\"\"");
    format!("\"{escaped}\"")
}

#[cfg(test)]
mod tests {
    use super::{
        parse_smtlib2_result, ParseSmtLib2ResultError, SmtLibBuilder, SmtLibCheckSatResult,
        SmtLibCommand, SmtLibConst, SmtLibExpr, SmtLibSort,
    };

    #[test]
    fn render_sort_variants() {
        assert_eq!(SmtLibSort::Bool.to_smtlib2(), "Bool");
        assert_eq!(SmtLibSort::Int.to_smtlib2(), "Int");
        assert_eq!(SmtLibSort::Real.to_smtlib2(), "Real");
        assert_eq!(SmtLibSort::BitVec(8).to_smtlib2(), "(_ BitVec 8)");
        assert_eq!(
            SmtLibSort::Array(Box::new(SmtLibSort::Int), Box::new(SmtLibSort::Bool)).to_smtlib2(),
            "(Array Int Bool)"
        );
        assert_eq!(
            SmtLibSort::Uninterpreted("bad name".to_string()).to_smtlib2(),
            "|bad name|"
        );
    }

    #[test]
    fn render_var_expr() {
        assert_eq!(
            SmtLibExpr::Var("123abc".to_string()).to_smtlib2(),
            "|123abc|"
        );
    }

    #[test]
    fn render_const_expr() {
        assert_eq!(
            SmtLibExpr::Const(SmtLibConst::Bool(true)).to_smtlib2(),
            "true"
        );
        assert_eq!(
            SmtLibExpr::Const(SmtLibConst::Int("42".to_string())).to_smtlib2(),
            "42"
        );
        assert_eq!(
            SmtLibExpr::Const(SmtLibConst::Real("3.5".to_string())).to_smtlib2(),
            "3.5"
        );
        assert_eq!(
            SmtLibExpr::Const(SmtLibConst::BitVec {
                value: "5".to_string(),
                width: 8,
            })
            .to_smtlib2(),
            "(_ bv5 8)"
        );
        assert_eq!(
            SmtLibExpr::Const(SmtLibConst::String("say \"hi\"".to_string())).to_smtlib2(),
            "\"say \"\"hi\"\"\""
        );
    }

    #[test]
    fn render_apply_expr() {
        let expr = SmtLibExpr::Apply(
            "+".to_string(),
            vec![
                SmtLibExpr::Var("x".to_string()),
                SmtLibExpr::Const(SmtLibConst::Int("1".to_string())),
            ],
        );

        assert_eq!(expr.to_smtlib2(), "(+ x 1)");
    }

    #[test]
    fn render_let_expr() {
        let expr = SmtLibExpr::Let(
            vec![
                (
                    "tmp".to_string(),
                    SmtLibExpr::Apply(
                        "+".to_string(),
                        vec![
                            SmtLibExpr::Var("x".to_string()),
                            SmtLibExpr::Const(SmtLibConst::Int("1".to_string())),
                        ],
                    ),
                ),
                (
                    "flag".to_string(),
                    SmtLibExpr::Const(SmtLibConst::Bool(true)),
                ),
            ],
            Box::new(SmtLibExpr::Apply(
                "and".to_string(),
                vec![
                    SmtLibExpr::Var("flag".to_string()),
                    SmtLibExpr::Apply(
                        ">".to_string(),
                        vec![
                            SmtLibExpr::Var("tmp".to_string()),
                            SmtLibExpr::Const(SmtLibConst::Int("0".to_string())),
                        ],
                    ),
                ],
            )),
        );

        assert_eq!(
            expr.to_smtlib2(),
            "(let ((tmp (+ x 1)) (flag true)) (and flag (> tmp 0)))"
        );
    }

    #[test]
    fn render_forall_expr() {
        let expr = SmtLibExpr::Forall(
            vec![
                ("x".to_string(), SmtLibSort::Int),
                ("bad name".to_string(), SmtLibSort::Bool),
            ],
            Box::new(SmtLibExpr::Apply(
                "=>".to_string(),
                vec![
                    SmtLibExpr::Var("bad name".to_string()),
                    SmtLibExpr::Apply(
                        ">".to_string(),
                        vec![
                            SmtLibExpr::Var("x".to_string()),
                            SmtLibExpr::Const(SmtLibConst::Int("0".to_string())),
                        ],
                    ),
                ],
            )),
        );

        assert_eq!(
            expr.to_smtlib2(),
            "(forall ((x Int) (|bad name| Bool)) (=> |bad name| (> x 0)))"
        );
    }

    #[test]
    fn render_exists_expr() {
        let expr = SmtLibExpr::Exists(
            vec![(
                "arr".to_string(),
                SmtLibSort::Array(Box::new(SmtLibSort::Int), Box::new(SmtLibSort::Bool)),
            )],
            Box::new(SmtLibExpr::Apply(
                "select".to_string(),
                vec![
                    SmtLibExpr::Var("arr".to_string()),
                    SmtLibExpr::Const(SmtLibConst::Int("0".to_string())),
                ],
            )),
        );

        assert_eq!(
            expr.to_smtlib2(),
            "(exists ((arr (Array Int Bool))) (select arr 0))"
        );
    }

    #[test]
    fn render_set_logic_command() {
        assert_eq!(
            SmtLibCommand::SetLogic("QF_UFLIA".to_string()).to_smtlib2(),
            "(set-logic QF_UFLIA)"
        );
    }

    #[test]
    fn render_declare_sort_command() {
        assert_eq!(
            SmtLibCommand::DeclareSort {
                name: "My Sort".to_string(),
                arity: 2,
            }
            .to_smtlib2(),
            "(declare-sort |My Sort| 2)"
        );
    }

    #[test]
    fn render_declare_fun_command() {
        assert_eq!(
            SmtLibCommand::DeclareFun {
                name: "f".to_string(),
                args: vec![SmtLibSort::Int, SmtLibSort::Bool],
                result: SmtLibSort::Real,
            }
            .to_smtlib2(),
            "(declare-fun f (Int Bool) Real)"
        );
    }

    #[test]
    fn render_define_fun_command() {
        let command = SmtLibCommand::DefineFun {
            name: "inc".to_string(),
            params: vec![("x".to_string(), SmtLibSort::Int)],
            result: SmtLibSort::Int,
            body: SmtLibExpr::Apply(
                "+".to_string(),
                vec![
                    SmtLibExpr::Var("x".to_string()),
                    SmtLibExpr::Const(SmtLibConst::Int("1".to_string())),
                ],
            ),
        };

        assert_eq!(
            command.to_smtlib2(),
            "(define-fun inc ((x Int)) Int (+ x 1))"
        );
    }

    #[test]
    fn render_assert_command() {
        let command = SmtLibCommand::Assert(SmtLibExpr::Apply(
            "=".to_string(),
            vec![
                SmtLibExpr::Var("x".to_string()),
                SmtLibExpr::Const(SmtLibConst::Int("1".to_string())),
            ],
        ));

        assert_eq!(command.to_smtlib2(), "(assert (= x 1))");
    }

    #[test]
    fn render_check_sat_command() {
        assert_eq!(SmtLibCommand::CheckSat.to_smtlib2(), "(check-sat)");
    }

    #[test]
    fn render_get_model_command() {
        assert_eq!(SmtLibCommand::GetModel.to_smtlib2(), "(get-model)");
    }

    #[test]
    fn render_push_command() {
        assert_eq!(SmtLibCommand::Push(2).to_smtlib2(), "(push 2)");
    }

    #[test]
    fn render_pop_command() {
        assert_eq!(SmtLibCommand::Pop(2).to_smtlib2(), "(pop 2)");
    }

    #[test]
    fn builder_renders_full_command_sequence() {
        let mut builder = SmtLibBuilder::new();
        builder
            .set_logic("QF_LIA")
            .declare_fun("x", vec![], SmtLibSort::Int)
            .assert_expr(SmtLibExpr::Apply(
                ">".to_string(),
                vec![
                    SmtLibExpr::Var("x".to_string()),
                    SmtLibExpr::Const(SmtLibConst::Int("0".to_string())),
                ],
            ))
            .check_sat()
            .get_model();

        assert_eq!(
            builder.to_smtlib2(),
            "(set-logic QF_LIA)\n(declare-fun x () Int)\n(assert (> x 0))\n(check-sat)\n(get-model)\n"
        );
    }

    #[test]
    fn parse_sat_result() {
        assert_eq!(parse_smtlib2_result("sat"), Ok(SmtLibCheckSatResult::Sat));
    }

    #[test]
    fn parse_unsat_result() {
        assert_eq!(
            parse_smtlib2_result("unsat"),
            Ok(SmtLibCheckSatResult::Unsat)
        );
    }

    #[test]
    fn parse_unknown_result() {
        assert_eq!(
            parse_smtlib2_result("unknown"),
            Ok(SmtLibCheckSatResult::Unknown)
        );
    }

    #[test]
    fn parse_result_ignores_comments_and_success_lines() {
        let output = "success\n; model follows later\nunknown\n";
        assert_eq!(
            parse_smtlib2_result(output),
            Ok(SmtLibCheckSatResult::Unknown)
        );
    }

    #[test]
    fn parse_result_rejects_unexpected_output() {
        assert_eq!(
            parse_smtlib2_result("(model ...)"),
            Err(ParseSmtLib2ResultError::UnexpectedLine(
                "(model ...)".to_string()
            ))
        );
        assert_eq!(
            parse_smtlib2_result(""),
            Err(ParseSmtLib2ResultError::MissingStatus)
        );
    }
}
