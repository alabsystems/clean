// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TLA+ to clean kernel translation.
//!
//! Translates TLA+ declarations and expressions into clean kernel `Expr`
//! via a shallow embedding:
//!
//! - **Constants** -> `TLA.<module>.<name> : TLA.Value`
//! - **Variables** -> `TLA.<module>.<name> : TLA.Var`
//! - **Operators** -> `TLA.<module>.<name> : TLA.Value -> ... -> TLA.Value`
//! - **Theorems** -> `TLA.<module>.<name> : Prop`
//! - **ForAll/Exists** -> Pi/Exists in the kernel
//! - **Logical operators** -> And, Or, implies, Not
//! - **Arithmetic** -> axiomatized TLA.add, TLA.sub, etc.

#[cfg(test)]
use super::types::TlaDecl;
use super::types::{QuantifierKind, TlaDeclKind, TlaExpr, TlaModule};
use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};
#[cfg(test)]
use clean_kernel::ExprKind;
use clean_kernel::{BinderInfo, Expr, LevelVec, Name};
use thiserror::Error;

// ════════════════════════════════════════════════════════════════════════════
// Error type
// ════════════════════════════════════════════════════════════════════════════

/// Errors raised during TLA+ to clean translation.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum TlaTranslateError {
    /// Unsupported TLA+ construct.
    #[error("unsupported TLA+ construct: {desc}")]
    Unsupported { desc: String },
}

pub(crate) type TlaTranslateResult<T> = Result<T, TlaTranslateError>;

// ════════════════════════════════════════════════════════════════════════════
// Translation context
// ════════════════════════════════════════════════════════════════════════════

/// Translation environment for TLA+ -> clean kernel.
pub struct TlaTranslationContext {
    /// Stack of bound variable names.
    locals: Vec<String>,
}

impl Default for TlaTranslationContext {
    fn default() -> Self {
        Self::new()
    }
}

impl TlaTranslationContext {
    /// Create an empty translation context.
    #[must_use]
    pub fn new() -> Self {
        Self { locals: Vec::new() }
    }

    fn push_local(&mut self, name: &str) {
        self.locals.push(name.to_owned());
    }

    fn pop_local(&mut self) {
        self.locals.pop();
    }

    fn lookup_var(&self, name: &str) -> Option<u32> {
        for (i, n) in self.locals.iter().rev().enumerate() {
            if n == name {
                return Some(i as u32);
            }
        }
        None
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Helpers
// ════════════════════════════════════════════════════════════════════════════

fn mk_const(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), LevelVec::new())
}

/// The type of TLA+ values (untyped domain).
fn tla_value_type() -> Expr {
    mk_const("TLA.Value")
}

// ════════════════════════════════════════════════════════════════════════════
// Expression translation
// ════════════════════════════════════════════════════════════════════════════

/// Translate a TLA+ expression to a clean kernel expression.
pub fn translate_tla_expr(
    ctx: &mut TlaTranslationContext,
    expr: &TlaExpr,
) -> TlaTranslateResult<Expr> {
    match expr {
        TlaExpr::Ident(name) => {
            if let Some(idx) = ctx.lookup_var(name) {
                Ok(Expr::bvar(idx))
            } else {
                Ok(mk_const(&format!("TLA.{name}")))
            }
        }

        TlaExpr::IntLit(n) => Ok(mk_const(&format!("TLA.int.{n}"))),
        TlaExpr::StringLit(s) => Ok(mk_const(&format!("TLA.str.{s}"))),
        TlaExpr::BoolLit(true) => Ok(mk_const("True")),
        TlaExpr::BoolLit(false) => Ok(mk_const("False")),

        TlaExpr::App(name, args) => {
            let func = mk_const(&format!("TLA.{name}"));
            let translated_args = args
                .iter()
                .map(|a| translate_tla_expr(ctx, a))
                .collect::<TlaTranslateResult<Vec<_>>>()?;
            Ok(Expr::apps(func, translated_args))
        }

        TlaExpr::BinOp(op, lhs, rhs) => {
            let lhs_expr = translate_tla_expr(ctx, lhs)?;
            let rhs_expr = translate_tla_expr(ctx, rhs)?;
            match op.as_str() {
                "/\\" => Ok(Expr::apps(mk_const("And"), [lhs_expr, rhs_expr])),
                "\\/" => Ok(Expr::apps(mk_const("Or"), [lhs_expr, rhs_expr])),
                "=>" => Ok(Expr::arrow(lhs_expr, rhs_expr)),
                "=" => Ok(Expr::apps(
                    mk_const("Eq"),
                    [tla_value_type(), lhs_expr, rhs_expr],
                )),
                "#" | "/=" => {
                    let eq = Expr::apps(mk_const("Eq"), [tla_value_type(), lhs_expr, rhs_expr]);
                    Ok(Expr::arrow(eq, mk_const("False")))
                }
                "\\in" => Ok(Expr::apps(mk_const("TLA.mem"), [lhs_expr, rhs_expr])),
                "\\subseteq" => Ok(Expr::apps(mk_const("TLA.subseteq"), [lhs_expr, rhs_expr])),
                "\\cup" => Ok(Expr::apps(mk_const("TLA.union"), [lhs_expr, rhs_expr])),
                "\\cap" => Ok(Expr::apps(mk_const("TLA.inter"), [lhs_expr, rhs_expr])),
                ">=" => Ok(Expr::apps(mk_const("TLA.ge"), [lhs_expr, rhs_expr])),
                "<=" => Ok(Expr::apps(mk_const("TLA.le"), [lhs_expr, rhs_expr])),
                ">" => Ok(Expr::apps(mk_const("TLA.gt"), [lhs_expr, rhs_expr])),
                "<" => Ok(Expr::apps(mk_const("TLA.lt"), [lhs_expr, rhs_expr])),
                "+" => Ok(Expr::apps(mk_const("TLA.add"), [lhs_expr, rhs_expr])),
                "-" => Ok(Expr::apps(mk_const("TLA.sub"), [lhs_expr, rhs_expr])),
                "*" => Ok(Expr::apps(mk_const("TLA.mul"), [lhs_expr, rhs_expr])),
                _ => {
                    let op_const = mk_const(&format!("TLA.op.{op}"));
                    Ok(Expr::apps(op_const, [lhs_expr, rhs_expr]))
                }
            }
        }

        TlaExpr::UnaryOp(op, inner) => {
            let inner_expr = translate_tla_expr(ctx, inner)?;
            match op.as_str() {
                "~" | "\\neg" | "\\lnot" => Ok(Expr::arrow(inner_expr, mk_const("False"))),
                "ENABLED" => Ok(Expr::app(mk_const("TLA.enabled"), inner_expr)),
                "UNCHANGED" => Ok(Expr::app(mk_const("TLA.unchanged"), inner_expr)),
                _ => Ok(Expr::app(mk_const(&format!("TLA.op.{op}")), inner_expr)),
            }
        }

        TlaExpr::Prime(inner) => {
            let inner_expr = translate_tla_expr(ctx, inner)?;
            Ok(Expr::app(mk_const("TLA.prime"), inner_expr))
        }

        TlaExpr::Quantifier(kind, vars, body) => {
            for (name, _) in vars {
                ctx.push_local(name);
            }
            let body_expr = translate_tla_expr(ctx, body)?;
            for _ in vars {
                ctx.pop_local();
            }

            match kind {
                QuantifierKind::ForAll => {
                    let mut result = body_expr;
                    for _ in vars.iter().rev() {
                        result = Expr::pi(BinderInfo::Default, tla_value_type(), result);
                    }
                    Ok(result)
                }
                QuantifierKind::Exists => {
                    let mut result = body_expr;
                    for _ in vars.iter().rev() {
                        let lam = Expr::lam(BinderInfo::Default, tla_value_type(), result);
                        result = Expr::app(mk_const("Exists"), lam);
                    }
                    Ok(result)
                }
            }
        }

        TlaExpr::IfThenElse(cond, then_e, else_e) => {
            let cond_expr = translate_tla_expr(ctx, cond)?;
            let then_expr = translate_tla_expr(ctx, then_e)?;
            let else_expr = translate_tla_expr(ctx, else_e)?;
            Ok(Expr::apps(
                mk_const("TLA.ite"),
                [cond_expr, then_expr, else_expr],
            ))
        }

        TlaExpr::SetEnum(elems) => {
            let translated = elems
                .iter()
                .map(|e| translate_tla_expr(ctx, e))
                .collect::<TlaTranslateResult<Vec<_>>>()?;
            Ok(Expr::apps(mk_const("TLA.set_enum"), translated))
        }

        TlaExpr::Tuple(elems) => {
            let translated = elems
                .iter()
                .map(|e| translate_tla_expr(ctx, e))
                .collect::<TlaTranslateResult<Vec<_>>>()?;
            Ok(Expr::apps(mk_const("TLA.tuple"), translated))
        }

        TlaExpr::Record(fields) => {
            let mut args = Vec::new();
            for (key, val) in fields {
                args.push(mk_const(&format!("TLA.field.{key}")));
                args.push(translate_tla_expr(ctx, val)?);
            }
            Ok(Expr::apps(mk_const("TLA.record"), args))
        }

        TlaExpr::FieldAccess(rec, field) => {
            let rec_expr = translate_tla_expr(ctx, rec)?;
            Ok(Expr::apps(
                mk_const("TLA.field_access"),
                [rec_expr, mk_const(&format!("TLA.field.{field}"))],
            ))
        }

        TlaExpr::Unchanged(vars) => {
            let translated = vars
                .iter()
                .map(|v| translate_tla_expr(ctx, v))
                .collect::<TlaTranslateResult<Vec<_>>>()?;
            Ok(Expr::apps(mk_const("TLA.unchanged"), translated))
        }

        TlaExpr::Temporal(op, inner) => {
            let inner_expr = translate_tla_expr(ctx, inner)?;
            Ok(Expr::app(
                mk_const(&format!("TLA.temporal.{op}")),
                inner_expr,
            ))
        }

        TlaExpr::Choose(var, domain, body) => {
            ctx.push_local(var);
            let body_expr = translate_tla_expr(ctx, body)?;
            ctx.pop_local();
            let lam = Expr::lam(BinderInfo::Default, tla_value_type(), body_expr);
            match domain {
                Some(d) => {
                    let domain_expr = translate_tla_expr(ctx, d)?;
                    Ok(Expr::apps(mk_const("TLA.choose"), [domain_expr, lam]))
                }
                None => Ok(Expr::app(mk_const("TLA.choose_unbounded"), lam)),
            }
        }

        TlaExpr::SetFilter(var, set, pred) => {
            let set_expr = translate_tla_expr(ctx, set)?;
            ctx.push_local(var);
            let pred_expr = translate_tla_expr(ctx, pred)?;
            ctx.pop_local();
            let lam = Expr::lam(BinderInfo::Default, tla_value_type(), pred_expr);
            Ok(Expr::apps(mk_const("TLA.set_filter"), [set_expr, lam]))
        }

        TlaExpr::SetMap(body, var, set) => {
            let set_expr = translate_tla_expr(ctx, set)?;
            ctx.push_local(var);
            let body_expr = translate_tla_expr(ctx, body)?;
            ctx.pop_local();
            let lam = Expr::lam(BinderInfo::Default, tla_value_type(), body_expr);
            Ok(Expr::apps(mk_const("TLA.set_map"), [set_expr, lam]))
        }

        TlaExpr::LetIn(bindings, body) => {
            // Approximate: push all bindings as locals.
            for (name, _) in bindings {
                ctx.push_local(name);
            }
            let body_expr = translate_tla_expr(ctx, body)?;
            for _ in bindings {
                ctx.pop_local();
            }
            Ok(body_expr)
        }

        TlaExpr::Case(branches, default) => {
            // Represent as nested if-then-else.
            let mut result = match default {
                Some(d) => translate_tla_expr(ctx, d)?,
                None => mk_const("TLA.undefined"),
            };
            for (guard, body) in branches.iter().rev() {
                let guard_expr = translate_tla_expr(ctx, guard)?;
                let body_expr = translate_tla_expr(ctx, body)?;
                result = Expr::apps(mk_const("TLA.ite"), [guard_expr, body_expr, result]);
            }
            Ok(result)
        }

        TlaExpr::Raw(text) => {
            // Raw unparsed text — represent as a named constant.
            Ok(mk_const(&format!("TLA.raw.{}", text.replace(' ', "_"))))
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Declaration translation
// ════════════════════════════════════════════════════════════════════════════

/// Kind of an imported TLA+ constant.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum TlaConstantKind {
    /// A TLA+ constant.
    Constant,
    /// A TLA+ state variable.
    Variable,
    /// An operator definition.
    Operator,
    /// A theorem/lemma/proposition/corollary.
    Theorem,
    /// An axiom or assumption.
    Axiom,
    /// An INSTANCE declaration.
    Instance,
}

impl From<TlaDeclKind> for TlaConstantKind {
    fn from(kind: TlaDeclKind) -> Self {
        match kind {
            TlaDeclKind::Constant => Self::Constant,
            TlaDeclKind::Variable => Self::Variable,
            TlaDeclKind::Operator => Self::Operator,
            TlaDeclKind::Theorem
            | TlaDeclKind::Lemma
            | TlaDeclKind::Proposition
            | TlaDeclKind::Corollary => Self::Theorem,
            TlaDeclKind::Axiom | TlaDeclKind::Assumption => Self::Axiom,
            TlaDeclKind::Instance => Self::Instance,
        }
    }
}

/// A single constant produced by importing a TLA+ declaration.
#[derive(Clone, Debug)]
pub struct TlaImportedConstant {
    /// clean-facing name.
    pub name: String,
    /// String representation of the translated type expression.
    pub type_expr: String,
    /// What kind of TLA+ item this came from.
    pub kind: TlaConstantKind,
    /// Axiom profile.
    pub axiom_profile: AxiomProfile,
    /// Trust level.
    pub trust_level: TrustLevel,
    /// Provenance record.
    pub provenance: Provenance,
}

/// Translate a TLA+ module into imported constants.
pub fn translate_module(
    ctx: &mut TlaTranslationContext,
    module: &TlaModule,
    source_file: Option<&str>,
) -> TlaTranslateResult<Vec<TlaImportedConstant>> {
    let mut constants = Vec::new();

    for decl in &module.declarations {
        let kind = TlaConstantKind::from(decl.kind);
        let cname = format!("TLA.{}.{}", module.name, decl.name);

        let type_expr = match &decl.body {
            Some(body) => match translate_tla_expr(ctx, body) {
                Ok(expr) => format!("{expr:?}"),
                Err(_) => "TLA.Value".to_owned(),
            },
            None => match decl.kind {
                TlaDeclKind::Variable => "TLA.Var".to_owned(),
                TlaDeclKind::Constant => "TLA.Value".to_owned(),
                _ => "Prop".to_owned(),
            },
        };

        let trust_level = match kind {
            TlaConstantKind::Theorem => TrustLevel::TrustedOracle,
            TlaConstantKind::Axiom => TrustLevel::PartiallyAxiomatized,
            _ => TrustLevel::PartiallyAxiomatized,
        };

        constants.push(TlaImportedConstant {
            name: cname.clone(),
            type_expr,
            kind,
            axiom_profile: AxiomProfile::SMT_ORACLE, // TLC model checker is oracle-level
            trust_level,
            provenance: Provenance {
                source: SourceSystem::Tlc,
                original_name: cname,
                source_file: source_file.map(String::from),
                axiom_profile: AxiomProfile::SMT_ORACLE,
            },
        });
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
    fn test_translate_ident() {
        let mut ctx = TlaTranslationContext::new();
        let expr = translate_tla_expr(&mut ctx, &TlaExpr::Ident("foo".to_owned()))
            .expect("should translate");
        match expr.kind() {
            ExprKind::Const(name, _) => assert_eq!(*name, Name::from_string("TLA.foo")),
            other => panic!("expected Const, got {other:?}"),
        }
    }

    #[test]
    fn test_translate_bool() {
        let mut ctx = TlaTranslationContext::new();
        let expr = translate_tla_expr(&mut ctx, &TlaExpr::BoolLit(true)).expect("should translate");
        match expr.kind() {
            ExprKind::Const(name, _) => assert_eq!(*name, Name::from_string("True")),
            other => panic!("expected Const(True), got {other:?}"),
        }
    }

    #[test]
    fn test_translate_and() {
        let mut ctx = TlaTranslationContext::new();
        let term = TlaExpr::BinOp(
            "/\\".to_owned(),
            Box::new(TlaExpr::BoolLit(true)),
            Box::new(TlaExpr::BoolLit(false)),
        );
        let expr = translate_tla_expr(&mut ctx, &term).expect("should translate");
        assert!(matches!(expr.kind(), ExprKind::App(_, _)));
    }

    #[test]
    fn test_translate_implies() {
        let mut ctx = TlaTranslationContext::new();
        let term = TlaExpr::BinOp(
            "=>".to_owned(),
            Box::new(TlaExpr::Ident("P".to_owned())),
            Box::new(TlaExpr::Ident("Q".to_owned())),
        );
        let expr = translate_tla_expr(&mut ctx, &term).expect("should translate");
        assert!(matches!(expr.kind(), ExprKind::Pi(_, _, _)));
    }

    #[test]
    fn test_translate_forall() {
        let mut ctx = TlaTranslationContext::new();
        let term = TlaExpr::Quantifier(
            QuantifierKind::ForAll,
            vec![("x".to_owned(), None)],
            Box::new(TlaExpr::BinOp(
                ">=".to_owned(),
                Box::new(TlaExpr::Ident("x".to_owned())),
                Box::new(TlaExpr::IntLit(0)),
            )),
        );
        let expr = translate_tla_expr(&mut ctx, &term).expect("should translate");
        assert!(matches!(expr.kind(), ExprKind::Pi(_, _, _)));
    }

    #[test]
    fn test_translate_exists() {
        let mut ctx = TlaTranslationContext::new();
        let term = TlaExpr::Quantifier(
            QuantifierKind::Exists,
            vec![("x".to_owned(), None)],
            Box::new(TlaExpr::BinOp(
                "=".to_owned(),
                Box::new(TlaExpr::Ident("x".to_owned())),
                Box::new(TlaExpr::IntLit(42)),
            )),
        );
        let expr = translate_tla_expr(&mut ctx, &term).expect("should translate");
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
    fn test_translate_prime() {
        let mut ctx = TlaTranslationContext::new();
        let term = TlaExpr::Prime(Box::new(TlaExpr::Ident("x".to_owned())));
        let expr = translate_tla_expr(&mut ctx, &term).expect("should translate");
        assert!(matches!(expr.kind(), ExprKind::App(_, _)));
    }

    #[test]
    fn test_translate_module() {
        let module = TlaModule {
            name: "Test".to_owned(),
            extends: vec!["Naturals".to_owned()],
            declarations: vec![
                TlaDecl {
                    name: "N".to_owned(),
                    kind: TlaDeclKind::Constant,
                    params: Vec::new(),
                    body: None,
                },
                TlaDecl {
                    name: "x".to_owned(),
                    kind: TlaDeclKind::Variable,
                    params: Vec::new(),
                    body: None,
                },
                TlaDecl {
                    name: "Init".to_owned(),
                    kind: TlaDeclKind::Operator,
                    params: Vec::new(),
                    body: Some(TlaExpr::BinOp(
                        "=".to_owned(),
                        Box::new(TlaExpr::Ident("x".to_owned())),
                        Box::new(TlaExpr::IntLit(0)),
                    )),
                },
            ],
        };
        let mut ctx = TlaTranslationContext::new();
        let constants = translate_module(&mut ctx, &module, None).expect("should translate");
        assert_eq!(constants.len(), 3);
        assert_eq!(constants[0].kind, TlaConstantKind::Constant);
        assert_eq!(constants[1].kind, TlaConstantKind::Variable);
        assert_eq!(constants[2].kind, TlaConstantKind::Operator);
    }
}
