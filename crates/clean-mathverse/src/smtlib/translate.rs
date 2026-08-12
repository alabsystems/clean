// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SMT-LIB2 to clean kernel translation.
//!
//! Translates SMT-LIB2 sorts, terms, and commands into clean kernel `Expr`
//! via a shallow embedding:
//!
//! - **Bool** -> `Prop`
//! - **Int** -> `SMT.Int` (axiomatized constant)
//! - **Real** -> `SMT.Real` (axiomatized constant)
//! - **BitVec N** -> `SMT.BitVec N` (parameterized)
//! - **Named sorts** -> `SMT.<name>` constants
//! - **Functions** -> `Expr::const_` with arrow types
//! - **Assertions** -> propositions (terms of type `Prop`)
//! - **ForAll** -> `Expr::pi` (dependent product)
//! - **Exists** -> `Exists` constant applied to a lambda
//! - **And/Or/Not/Implies** -> logical connective constants
//! - **Eq** -> `Eq` constant
//! - **Variables** -> `Expr::bvar` (de Bruijn indices)

use super::types::{SmtCommand, SmtScript, SmtSort, SmtTerm};
use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};
#[cfg(test)]
use clean_kernel::ExprKind;
use clean_kernel::{BinderInfo, Expr, LevelVec, Name};
use thiserror::Error;

// ════════════════════════════════════════════════════════════════════════════
// Error type
// ════════════════════════════════════════════════════════════════════════════

/// Errors raised during SMT-LIB2 to clean translation.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum SmtTranslateError {
    /// Unbound variable encountered during translation.
    #[error("unbound variable `{name}` at depth {depth}")]
    UnboundVariable { name: String, depth: usize },
    /// Unsupported SMT-LIB2 construct.
    #[error("unsupported SMT-LIB2 construct: {desc}")]
    Unsupported { desc: String },
}

pub(crate) type SmtTranslateResult<T> = Result<T, SmtTranslateError>;

// ════════════════════════════════════════════════════════════════════════════
// Translation context
// ════════════════════════════════════════════════════════════════════════════

/// Translation environment for SMT-LIB2 terms -> clean kernel Expr.
pub struct SmtTranslationContext {
    /// Stack of bound variable names (innermost = last).
    locals: Vec<(String, SmtSort)>,
}

impl Default for SmtTranslationContext {
    fn default() -> Self {
        Self::new()
    }
}

impl SmtTranslationContext {
    /// Create an empty translation context.
    #[must_use]
    pub fn new() -> Self {
        Self { locals: Vec::new() }
    }

    fn push_local(&mut self, name: &str, sort: &SmtSort) {
        self.locals.push((name.to_owned(), sort.clone()));
    }

    fn pop_local(&mut self) {
        self.locals.pop();
    }

    fn lookup_var(&self, name: &str) -> Option<(u32, &SmtSort)> {
        for (i, (n, s)) in self.locals.iter().rev().enumerate() {
            if n == name {
                return Some((i as u32, s));
            }
        }
        None
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Helpers
// ════════════════════════════════════════════════════════════════════════════

/// Create a constant with no universe levels.
fn mk_const(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), LevelVec::new())
}

// ════════════════════════════════════════════════════════════════════════════
// Sort translation
// ════════════════════════════════════════════════════════════════════════════

/// Translate an SMT sort to a clean type expression.
pub fn translate_sort(sort: &SmtSort) -> Expr {
    match sort {
        SmtSort::Bool => mk_const("Prop"),
        SmtSort::Int => mk_const("SMT.Int"),
        SmtSort::Real => mk_const("SMT.Real"),
        SmtSort::BitVec(n) => Expr::app(mk_const("SMT.BitVec"), mk_const(&format!("SMT.nat.{n}"))),
        SmtSort::Array(idx, elem) => Expr::apps(
            mk_const("SMT.Array"),
            [translate_sort(idx), translate_sort(elem)],
        ),
        SmtSort::Named(name) => mk_const(&format!("SMT.{name}")),
        SmtSort::App(name, params) => {
            let base = mk_const(&format!("SMT.{name}"));
            let args: Vec<Expr> = params.iter().map(translate_sort).collect();
            Expr::apps(base, args)
        }
    }
}

/// Build an arrow type from parameter sorts to return sort.
fn build_function_type(params: &[SmtSort], ret: &SmtSort) -> Expr {
    let mut result = translate_sort(ret);
    for param in params.iter().rev() {
        result = Expr::arrow(translate_sort(param), result);
    }
    result
}

// ════════════════════════════════════════════════════════════════════════════
// Term translation
// ════════════════════════════════════════════════════════════════════════════

/// Translate an SMT-LIB2 term to a clean kernel expression.
pub fn translate_term(ctx: &mut SmtTranslationContext, term: &SmtTerm) -> SmtTranslateResult<Expr> {
    match term {
        SmtTerm::BoolLit(true) => Ok(mk_const("True")),
        SmtTerm::BoolLit(false) => Ok(mk_const("False")),
        SmtTerm::IntLit(n) => Ok(mk_const(&format!("SMT.int.{n}"))),
        SmtTerm::RealLit(s) => Ok(mk_const(&format!("SMT.real.{s}"))),
        SmtTerm::BvLit(s) => Ok(mk_const(&format!("SMT.bv.{s}"))),
        SmtTerm::StringLit(s) => Ok(mk_const(&format!("SMT.str.{s}"))),

        SmtTerm::Symbol(name) => {
            if let Some((idx, _sort)) = ctx.lookup_var(name) {
                Ok(Expr::bvar(idx))
            } else {
                Ok(mk_const(&format!("SMT.{name}")))
            }
        }

        SmtTerm::App(op, args) => {
            let translated_args = args
                .iter()
                .map(|a| translate_term(ctx, a))
                .collect::<SmtTranslateResult<Vec<_>>>()?;

            match op.as_str() {
                // Logical connectives.
                "and" if translated_args.len() == 2 => {
                    Ok(Expr::apps(mk_const("And"), translated_args))
                }
                "or" if translated_args.len() == 2 => {
                    Ok(Expr::apps(mk_const("Or"), translated_args))
                }
                "not" if translated_args.len() == 1 => Ok(Expr::arrow(
                    translated_args.into_iter().next().expect("checked len"),
                    mk_const("False"),
                )),
                "=>" if translated_args.len() == 2 => {
                    let mut it = translated_args.into_iter();
                    let lhs = it.next().expect("checked");
                    let rhs = it.next().expect("checked");
                    Ok(Expr::arrow(lhs, rhs))
                }
                "=" if translated_args.len() == 2 => {
                    let mut it = translated_args.into_iter();
                    let lhs = it.next().expect("checked");
                    let rhs = it.next().expect("checked");
                    Ok(Expr::apps(mk_const("Eq"), [mk_const("SMT.Sort"), lhs, rhs]))
                }
                "distinct" if translated_args.len() == 2 => {
                    let mut it = translated_args.into_iter();
                    let lhs = it.next().expect("checked");
                    let rhs = it.next().expect("checked");
                    let eq = Expr::apps(mk_const("Eq"), [mk_const("SMT.Sort"), lhs, rhs]);
                    Ok(Expr::arrow(eq, mk_const("False")))
                }
                "ite" if translated_args.len() == 3 => {
                    let func = mk_const("SMT.ite");
                    Ok(Expr::apps(func, translated_args))
                }
                // N-ary and/or.
                "and" => {
                    let mut it = translated_args.into_iter();
                    let first = it.next().unwrap_or_else(|| mk_const("True"));
                    Ok(it.fold(first, |acc, x| Expr::apps(mk_const("And"), [acc, x])))
                }
                "or" => {
                    let mut it = translated_args.into_iter();
                    let first = it.next().unwrap_or_else(|| mk_const("False"));
                    Ok(it.fold(first, |acc, x| Expr::apps(mk_const("Or"), [acc, x])))
                }
                // General function application.
                _ => {
                    let func = mk_const(&format!("SMT.{op}"));
                    Ok(Expr::apps(func, translated_args))
                }
            }
        }

        SmtTerm::Forall(vars, body) => {
            for (name, sort) in vars {
                ctx.push_local(name, sort);
            }
            let body_expr = translate_term(ctx, body)?;
            for _ in vars {
                ctx.pop_local();
            }
            let mut result = body_expr;
            for (_, sort) in vars.iter().rev() {
                result = Expr::pi(BinderInfo::Default, translate_sort(sort), result);
            }
            Ok(result)
        }

        SmtTerm::Exists(vars, body) => {
            for (name, sort) in vars {
                ctx.push_local(name, sort);
            }
            let body_expr = translate_term(ctx, body)?;
            for _ in vars {
                ctx.pop_local();
            }
            let mut result = body_expr;
            for (_, sort) in vars.iter().rev() {
                let lam = Expr::lam(BinderInfo::Default, translate_sort(sort), result);
                result = Expr::app(mk_const("Exists"), lam);
            }
            Ok(result)
        }

        SmtTerm::Let(bindings, body) => {
            // Translate let bindings as nested function application for simplicity.
            // In a full implementation, this would use Expr::let_.
            for (name, _val) in bindings {
                ctx.push_local(name, &SmtSort::Bool); // Sort approximation.
            }
            let body_expr = translate_term(ctx, body)?;
            for _ in bindings {
                ctx.pop_local();
            }
            Ok(body_expr)
        }

        SmtTerm::Annotated(inner, _attrs) => translate_term(ctx, inner),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Imported constant
// ════════════════════════════════════════════════════════════════════════════

/// Kind of an imported SMT-LIB constant.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum SmtConstantKind {
    /// A declared function or constant.
    Declaration,
    /// A defined function.
    Definition,
    /// An assertion.
    Assertion,
    /// A declared sort.
    Sort,
}

/// A single constant produced by importing an SMT-LIB2 command.
#[derive(Clone, Debug)]
pub struct SmtImportedConstant {
    /// clean-facing name.
    pub name: String,
    /// String representation of the translated type expression.
    pub type_expr: String,
    /// What kind of SMT-LIB item this came from.
    pub kind: SmtConstantKind,
    /// Axiom profile.
    pub axiom_profile: AxiomProfile,
    /// Trust level.
    pub trust_level: TrustLevel,
    /// Provenance record.
    pub provenance: Provenance,
}

/// Translate an SMT-LIB2 script into imported constants.
///
/// Each declaration, definition, and assertion produces one constant.
pub fn translate_script(
    ctx: &mut SmtTranslationContext,
    script: &SmtScript,
    problem_name: &str,
    source_file: Option<&str>,
) -> SmtTranslateResult<Vec<SmtImportedConstant>> {
    let mut constants = Vec::new();
    let mut assert_idx = 0usize;

    for cmd in &script.commands {
        match cmd {
            SmtCommand::DeclareFun(name, params, ret) => {
                let type_expr = build_function_type(params, ret);
                let cname = format!("SMT.{problem_name}.{name}");
                constants.push(SmtImportedConstant {
                    name: cname.clone(),
                    type_expr: format!("{type_expr:?}"),
                    kind: SmtConstantKind::Declaration,
                    axiom_profile: AxiomProfile::SMT_ORACLE,
                    trust_level: TrustLevel::TrustedOracle,
                    provenance: Provenance {
                        source: SourceSystem::SmtSolver,
                        original_name: cname,
                        source_file: source_file.map(String::from),
                        axiom_profile: AxiomProfile::SMT_ORACLE,
                    },
                });
            }

            SmtCommand::DeclareConst(name, sort) => {
                let type_expr = translate_sort(sort);
                let cname = format!("SMT.{problem_name}.{name}");
                constants.push(SmtImportedConstant {
                    name: cname.clone(),
                    type_expr: format!("{type_expr:?}"),
                    kind: SmtConstantKind::Declaration,
                    axiom_profile: AxiomProfile::SMT_ORACLE,
                    trust_level: TrustLevel::TrustedOracle,
                    provenance: Provenance {
                        source: SourceSystem::SmtSolver,
                        original_name: cname,
                        source_file: source_file.map(String::from),
                        axiom_profile: AxiomProfile::SMT_ORACLE,
                    },
                });
            }

            SmtCommand::DeclareSort(name, _arity) => {
                let cname = format!("SMT.{problem_name}.sort.{name}");
                constants.push(SmtImportedConstant {
                    name: cname.clone(),
                    type_expr: "Sort".to_owned(),
                    kind: SmtConstantKind::Sort,
                    axiom_profile: AxiomProfile::SMT_ORACLE,
                    trust_level: TrustLevel::TrustedOracle,
                    provenance: Provenance {
                        source: SourceSystem::SmtSolver,
                        original_name: cname,
                        source_file: source_file.map(String::from),
                        axiom_profile: AxiomProfile::SMT_ORACLE,
                    },
                });
            }

            SmtCommand::DefineFun(name, _params, _ret, _body) => {
                let cname = format!("SMT.{problem_name}.{name}");
                constants.push(SmtImportedConstant {
                    name: cname.clone(),
                    type_expr: "definition".to_owned(),
                    kind: SmtConstantKind::Definition,
                    axiom_profile: AxiomProfile::SMT_ORACLE,
                    trust_level: TrustLevel::TrustedOracle,
                    provenance: Provenance {
                        source: SourceSystem::SmtSolver,
                        original_name: cname,
                        source_file: source_file.map(String::from),
                        axiom_profile: AxiomProfile::SMT_ORACLE,
                    },
                });
            }

            SmtCommand::Assert(term) => {
                let _expr = translate_term(ctx, term)?;
                let cname = format!("SMT.{problem_name}.assert_{assert_idx}");
                assert_idx += 1;
                constants.push(SmtImportedConstant {
                    name: cname.clone(),
                    type_expr: format!("{_expr:?}"),
                    kind: SmtConstantKind::Assertion,
                    axiom_profile: AxiomProfile::SMT_ORACLE,
                    trust_level: TrustLevel::TrustedOracle,
                    provenance: Provenance {
                        source: SourceSystem::SmtSolver,
                        original_name: cname,
                        source_file: source_file.map(String::from),
                        axiom_profile: AxiomProfile::SMT_ORACLE,
                    },
                });
            }

            // Other commands don't produce constants.
            _ => {}
        }
    }

    Ok(constants)
}

// ════════════════════════════════════════════════════════════════════════════
// Tests
// ════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_translate_sort_bool() {
        let expr = translate_sort(&SmtSort::Bool);
        match expr.kind() {
            ExprKind::Const(name, _) => assert_eq!(*name, Name::from_string("Prop")),
            other => panic!("expected Const(Prop), got {other:?}"),
        }
    }

    #[test]
    fn test_translate_sort_int() {
        let expr = translate_sort(&SmtSort::Int);
        match expr.kind() {
            ExprKind::Const(name, _) => assert_eq!(*name, Name::from_string("SMT.Int")),
            other => panic!("expected Const(SMT.Int), got {other:?}"),
        }
    }

    #[test]
    fn test_translate_bool_literal() {
        let mut ctx = SmtTranslationContext::new();
        let expr = translate_term(&mut ctx, &SmtTerm::BoolLit(true)).expect("should translate");
        match expr.kind() {
            ExprKind::Const(name, _) => assert_eq!(*name, Name::from_string("True")),
            other => panic!("expected Const(True), got {other:?}"),
        }
    }

    #[test]
    fn test_translate_symbol_free() {
        let mut ctx = SmtTranslationContext::new();
        let expr =
            translate_term(&mut ctx, &SmtTerm::Symbol("x".to_owned())).expect("should translate");
        match expr.kind() {
            ExprKind::Const(name, _) => assert_eq!(*name, Name::from_string("SMT.x")),
            other => panic!("expected Const(SMT.x), got {other:?}"),
        }
    }

    #[test]
    fn test_translate_forall() {
        let mut ctx = SmtTranslationContext::new();
        let term = SmtTerm::Forall(
            vec![("x".to_owned(), SmtSort::Int)],
            Box::new(SmtTerm::App(
                ">".to_owned(),
                vec![SmtTerm::Symbol("x".to_owned()), SmtTerm::IntLit(0)],
            )),
        );
        let expr = translate_term(&mut ctx, &term).expect("should translate");
        assert!(matches!(expr.kind(), ExprKind::Pi(_, _, _)));
    }

    #[test]
    fn test_translate_exists() {
        let mut ctx = SmtTranslationContext::new();
        let term = SmtTerm::Exists(
            vec![("x".to_owned(), SmtSort::Int)],
            Box::new(SmtTerm::App(
                "=".to_owned(),
                vec![SmtTerm::Symbol("x".to_owned()), SmtTerm::IntLit(42)],
            )),
        );
        let expr = translate_term(&mut ctx, &term).expect("should translate");
        match expr.kind() {
            ExprKind::App(func, _) => {
                assert!(matches!(
                    func.kind(),
                    ExprKind::Const(name, _) if *name == Name::from_string("Exists")
                ));
            }
            other => panic!("expected App(Exists, ...), got {other:?}"),
        }
    }

    #[test]
    fn test_translate_and() {
        let mut ctx = SmtTranslationContext::new();
        let term = SmtTerm::App(
            "and".to_owned(),
            vec![SmtTerm::BoolLit(true), SmtTerm::BoolLit(false)],
        );
        let expr = translate_term(&mut ctx, &term).expect("should translate");
        assert!(matches!(expr.kind(), ExprKind::App(_, _)));
    }

    #[test]
    fn test_translate_not() {
        let mut ctx = SmtTranslationContext::new();
        let term = SmtTerm::App("not".to_owned(), vec![SmtTerm::BoolLit(true)]);
        let expr = translate_term(&mut ctx, &term).expect("should translate");
        // not P = P -> False
        assert!(matches!(expr.kind(), ExprKind::Pi(_, _, _)));
    }

    #[test]
    fn test_translate_script() {
        let script = SmtScript {
            logic: Some("QF_LIA".to_owned()),
            commands: vec![
                SmtCommand::DeclareFun("x".to_owned(), vec![], SmtSort::Int),
                SmtCommand::Assert(SmtTerm::App(
                    ">".to_owned(),
                    vec![SmtTerm::Symbol("x".to_owned()), SmtTerm::IntLit(0)],
                )),
                SmtCommand::CheckSat,
            ],
        };
        let mut ctx = SmtTranslationContext::new();
        let constants =
            translate_script(&mut ctx, &script, "test", None).expect("should translate");
        assert_eq!(constants.len(), 2); // declaration + assertion
        assert_eq!(constants[0].kind, SmtConstantKind::Declaration);
        assert_eq!(constants[1].kind, SmtConstantKind::Assertion);
    }
}
