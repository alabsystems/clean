// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! OpenTheory `.art` parser.

use super::article::OtCommand;
use super::name::OtName;
use super::vm::{OtContext, OtVmState};
use super::{OpenTheoryError, OpenTheoryResult, OtArticle};
use std::fs;
use std::path::Path;

/// Parse an OpenTheory article from text.
pub fn parse_article(input: &str) -> OpenTheoryResult<OtArticle> {
    parse_article_inner(input, OtVmState::default())
}

/// Parse an OpenTheory article from text, resolving axioms against previously
/// proved theorems provided in `context`.
pub fn parse_article_with_context(input: &str, context: OtContext) -> OpenTheoryResult<OtArticle> {
    parse_article_inner(input, OtVmState::with_context(context))
}

/// Parse an OpenTheory article from disk.
pub fn parse_article_file(path: impl AsRef<Path>) -> OpenTheoryResult<OtArticle> {
    let input = fs::read_to_string(path)?;
    parse_article(&input)
}

/// Parse an OpenTheory article from disk, resolving axioms against `context`.
pub fn parse_article_file_with_context(
    path: impl AsRef<Path>,
    context: OtContext,
) -> OpenTheoryResult<OtArticle> {
    let input = fs::read_to_string(path)?;
    parse_article_with_context(&input, context)
}

fn parse_article_inner(input: &str, mut vm: OtVmState) -> OpenTheoryResult<OtArticle> {
    let mut commands = Vec::new();

    for (index, raw_line) in input.lines().enumerate() {
        let line_no = index + 1;
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let command = parse_command(line_no, line)?;
        vm.execute(&command, line_no)?;
        commands.push(command);
        vm.note_command_executed();
    }

    Ok(vm.into_article(commands))
}

fn parse_command(line_no: usize, line: &str) -> OpenTheoryResult<OtCommand> {
    if is_integer_literal(line) {
        return line.parse::<i64>().map(OtCommand::Number).map_err(|_| {
            OpenTheoryError::InvalidInteger {
                line: line_no,
                value: line.to_string(),
            }
        });
    }
    if line.starts_with('"') {
        return Ok(OtCommand::Name(parse_quoted_name(line)?));
    }
    match line {
        "absTerm" => Ok(OtCommand::AbsTerm),
        "absThm" => Ok(OtCommand::AbsThm),
        "appTerm" => Ok(OtCommand::AppTerm),
        "appThm" => Ok(OtCommand::AppThm),
        "assume" => Ok(OtCommand::Assume),
        "axiom" => Ok(OtCommand::Axiom),
        "betaConv" => Ok(OtCommand::BetaConv),
        "cons" => Ok(OtCommand::Cons),
        "const" => Ok(OtCommand::Const),
        "constTerm" => Ok(OtCommand::ConstTerm),
        "deductAntisym" => Ok(OtCommand::DeductAntisym),
        "def" => Ok(OtCommand::Def),
        "defineConst" => Ok(OtCommand::DefineConst),
        "defineConstList" => Ok(OtCommand::DefineConstList),
        "defineTypeOp" => Ok(OtCommand::DefineTypeOp),
        "eqMp" => Ok(OtCommand::EqMp),
        "hdTl" => Ok(OtCommand::HdTl),
        "nil" => Ok(OtCommand::Nil),
        "opType" => Ok(OtCommand::OpType),
        "pop" => Ok(OtCommand::Pop),
        "pragma" => Ok(OtCommand::Pragma),
        "proveHyp" => Ok(OtCommand::ProveHyp),
        "ref" => Ok(OtCommand::Ref),
        "refl" => Ok(OtCommand::Refl),
        "remove" => Ok(OtCommand::Remove),
        "subst" => Ok(OtCommand::Subst),
        "sym" => Ok(OtCommand::Sym),
        "thm" => Ok(OtCommand::Thm),
        "trans" => Ok(OtCommand::Trans),
        "typeOp" => Ok(OtCommand::TypeOp),
        "var" => Ok(OtCommand::Var),
        "varTerm" => Ok(OtCommand::VarTerm),
        "varType" => Ok(OtCommand::VarType),
        "version" => Ok(OtCommand::Version),
        _ => Err(OpenTheoryError::InvalidCommand {
            line: line_no,
            command: line.to_string(),
        }),
    }
}

fn is_integer_literal(input: &str) -> bool {
    if input == "0" {
        return true;
    }
    let digits = input.strip_prefix('-').unwrap_or(input);
    if digits.is_empty() || !digits.chars().all(|ch| ch.is_ascii_digit()) {
        return false;
    }
    if digits.starts_with('0') {
        return false;
    }
    true
}

fn parse_quoted_name(input: &str) -> OpenTheoryResult<OtName> {
    if !input.starts_with('"') || !input.ends_with('"') || input.len() < 2 {
        return Err(OpenTheoryError::InvalidQuotedName {
            value: input.to_string(),
        });
    }

    let mut components = Vec::new();
    let mut current = String::new();
    let mut escaped = false;
    for ch in input[1..input.len() - 1].chars() {
        if escaped {
            current.push(ch);
            escaped = false;
            continue;
        }
        match ch {
            '\\' => escaped = true,
            '.' => {
                components.push(current);
                current = String::new();
            }
            _ => current.push(ch),
        }
    }
    if escaped {
        return Err(OpenTheoryError::InvalidQuotedName {
            value: input.to_string(),
        });
    }
    components.push(current);
    let component = components
        .pop()
        .ok_or_else(|| OpenTheoryError::InvalidQuotedName {
            value: input.to_string(),
        })?;
    Ok(OtName::new(components, component))
}
