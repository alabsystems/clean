// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TPTP-to-clean kernel translation.
//!
//! Translates TPTP FOF/TFF formulas into clean kernel `Expr` via a shallow
//! embedding:
//!
//! - **Domain:** `TPTP.individual : Sort 0` (the universe of individuals)
//! - **Predicates:** functions into `Prop`
//! - **Functions:** functions on `TPTP.individual`
//! - **ForAll** -> `Expr::pi` (dependent product)
//! - **Exists** -> `Exists` constant applied to a lambda
//! - **Implies** -> `Expr::arrow` (non-dependent pi)
//! - **And/Or** -> logical connective constants
//! - **Not** -> arrow to `False`
//! - **Eq** -> `Eq` constant applied to `TPTP.individual`
//! - **Variables** -> `Expr::bvar` (de Bruijn indices)
//! - **Constants/functions** -> `Expr::const_`

use super::types::{TptpFormula, TptpRole, TptpTerm};
use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};
#[cfg(test)]
use clean_kernel::ExprKind;
use clean_kernel::{BinderInfo, Expr, LevelVec, Name};
use thiserror::Error;

// ════════════════════════════════════════════════════════════════════════════
// Error type
// ════════════════════════════════════════════════════════════════════════════

/// Errors raised during TPTP-to-clean translation.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum TptpTranslateError {
    /// Unbound variable encountered during translation.
    #[error("unbound variable `{name}` at depth {depth}")]
    UnboundVariable { name: String, depth: usize },
    /// Unsupported TPTP construct.
    #[error("unsupported TPTP construct: {desc}")]
    Unsupported { desc: String },
}

pub(crate) type TptpTranslateResult<T> = Result<T, TptpTranslateError>;

// ════════════════════════════════════════════════════════════════════════════
// Translation context
// ════════════════════════════════════════════════════════════════════════════

/// Translation environment for TPTP terms -> clean kernel Expr.
///
/// Tracks bound variable names and maps them to de Bruijn indices.
pub struct TptpTranslationContext {
    /// Stack of bound variable names (innermost = last).
    locals: Vec<String>,
}

impl Default for TptpTranslationContext {
    fn default() -> Self {
        Self::new()
    }
}

impl TptpTranslationContext {
    /// Create an empty translation context.
    #[must_use]
    pub fn new() -> Self {
        Self { locals: Vec::new() }
    }

    /// Push a local variable binding.
    fn push_local(&mut self, name: &str) {
        self.locals.push(name.to_owned());
    }

    /// Pop a local variable binding.
    fn pop_local(&mut self) {
        self.locals.pop();
    }

    /// Look up a variable by name, returning its de Bruijn index.
    fn lookup_var(&self, name: &str) -> Option<u32> {
        for (i, local) in self.locals.iter().rev().enumerate() {
            if local == name {
                return Some(i as u32);
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

/// The type of individuals in the TPTP domain.
fn individual_type() -> Expr {
    mk_const("TPTP.individual")
}

// ════════════════════════════════════════════════════════════════════════════
// Formula translation
// ════════════════════════════════════════════════════════════════════════════

/// Translate a TPTP term/formula to a clean kernel expression.
///
/// The result is an `Expr` in `Prop` (for formulas) or `TPTP.individual`
/// (for terms used as arguments).
pub fn translate_tptp_term(
    ctx: &mut TptpTranslationContext,
    term: &TptpTerm,
) -> TptpTranslateResult<Expr> {
    match term {
        TptpTerm::Var(name) => {
            if let Some(idx) = ctx.lookup_var(name) {
                Ok(Expr::bvar(idx))
            } else {
                // Free variable — treat as a constant.
                Ok(mk_const(&format!("TPTP.fvar.{name}")))
            }
        }

        TptpTerm::Atom(name) => Ok(mk_const(&format!("TPTP.{name}"))),

        TptpTerm::Func(name, args) => {
            let func_const = mk_const(&format!("TPTP.{name}"));
            let translated_args = args
                .iter()
                .map(|a| translate_tptp_term(ctx, a))
                .collect::<TptpTranslateResult<Vec<_>>>()?;
            Ok(Expr::apps(func_const, translated_args))
        }

        TptpTerm::Not(inner) => {
            let inner_expr = translate_tptp_term(ctx, inner)?;
            // ~P = P -> False
            Ok(Expr::arrow(inner_expr, mk_const("False")))
        }

        TptpTerm::And(lhs, rhs) => {
            let lhs_expr = translate_tptp_term(ctx, lhs)?;
            let rhs_expr = translate_tptp_term(ctx, rhs)?;
            Ok(Expr::apps(mk_const("And"), [lhs_expr, rhs_expr]))
        }

        TptpTerm::Or(lhs, rhs) => {
            let lhs_expr = translate_tptp_term(ctx, lhs)?;
            let rhs_expr = translate_tptp_term(ctx, rhs)?;
            Ok(Expr::apps(mk_const("Or"), [lhs_expr, rhs_expr]))
        }

        TptpTerm::Implies(lhs, rhs) => {
            let lhs_expr = translate_tptp_term(ctx, lhs)?;
            let rhs_expr = translate_tptp_term(ctx, rhs)?;
            // P => Q is non-dependent Pi: P -> Q
            Ok(Expr::arrow(lhs_expr, rhs_expr))
        }

        TptpTerm::Iff(lhs, rhs) => {
            let lhs_expr = translate_tptp_term(ctx, lhs)?;
            let rhs_expr = translate_tptp_term(ctx, rhs)?;
            Ok(Expr::apps(mk_const("Iff"), [lhs_expr, rhs_expr]))
        }

        TptpTerm::ForAll(vars, body) => {
            // Build nested Pi: (x1 : individual) -> (x2 : individual) -> ... -> body
            // Push all variables, translate body, then pop and wrap.
            for var in vars {
                ctx.push_local(var);
            }
            let body_expr = translate_tptp_term(ctx, body)?;
            for _ in vars {
                ctx.pop_local();
            }

            // Wrap in Pi from innermost to outermost.
            let mut result = body_expr;
            for _ in vars.iter().rev() {
                result = Expr::pi(BinderInfo::Default, individual_type(), result);
            }
            Ok(result)
        }

        TptpTerm::Exists(vars, body) => {
            // Exists: for a single variable, Exists (fun (x : individual) => body)
            // For multiple variables, nest: Exists (fun x1 => Exists (fun x2 => ... body))
            for var in vars {
                ctx.push_local(var);
            }
            let body_expr = translate_tptp_term(ctx, body)?;
            for _ in vars {
                ctx.pop_local();
            }

            // Build from innermost to outermost.
            let mut result = body_expr;
            for _ in vars.iter().rev() {
                let lam = Expr::lam(BinderInfo::Default, individual_type(), result);
                result = Expr::app(mk_const("Exists"), lam);
            }
            Ok(result)
        }

        TptpTerm::Eq(lhs, rhs) => {
            let lhs_expr = translate_tptp_term(ctx, lhs)?;
            let rhs_expr = translate_tptp_term(ctx, rhs)?;
            // Eq.{u} (alpha : Sort u) : alpha -> alpha -> Prop
            // We use Eq on TPTP.individual.
            Ok(Expr::apps(
                mk_const("Eq"),
                [individual_type(), lhs_expr, rhs_expr],
            ))
        }

        TptpTerm::Neq(lhs, rhs) => {
            let lhs_expr = translate_tptp_term(ctx, lhs)?;
            let rhs_expr = translate_tptp_term(ctx, rhs)?;
            // X != Y = (X = Y) -> False
            let eq_expr = Expr::apps(mk_const("Eq"), [individual_type(), lhs_expr, rhs_expr]);
            Ok(Expr::arrow(eq_expr, mk_const("False")))
        }

        TptpTerm::True => Ok(mk_const("True")),
        TptpTerm::False => Ok(mk_const("False")),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Annotated formula translation
// ════════════════════════════════════════════════════════════════════════════

/// Kind of an imported TPTP constant.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum TptpConstantKind {
    /// A TPTP axiom or hypothesis.
    Axiom,
    /// A TPTP conjecture (goal to prove).
    Conjecture,
    /// A TPTP theorem or lemma.
    Theorem,
    /// A TPTP definition.
    Definition,
    /// A type declaration (TFF).
    TypeDecl,
    /// Other (plain, etc.).
    Other,
}

impl From<TptpRole> for TptpConstantKind {
    fn from(role: TptpRole) -> Self {
        match role {
            TptpRole::Axiom | TptpRole::Hypothesis => Self::Axiom,
            TptpRole::Conjecture | TptpRole::NegatedConjecture => Self::Conjecture,
            TptpRole::Theorem | TptpRole::Lemma => Self::Theorem,
            TptpRole::Definition => Self::Definition,
            TptpRole::Type => Self::TypeDecl,
            TptpRole::Plain => Self::Other,
        }
    }
}

/// A single constant produced by importing a TPTP formula.
#[derive(Clone, Debug)]
pub struct TptpImportedConstant {
    /// clean-facing name (e.g., `TPTP.SET006.ax1`).
    pub name: String,
    /// String representation of the translated type expression.
    pub type_expr: String,
    /// What kind of TPTP item this came from.
    pub kind: TptpConstantKind,
    /// Axiom profile for this constant.
    pub axiom_profile: AxiomProfile,
    /// Trust level assigned to this constant.
    pub trust_level: TrustLevel,
    /// Full provenance record.
    pub provenance: Provenance,
}

/// Translate a single annotated TPTP formula into an imported constant.
///
/// Returns `Ok(Some(constant))` for successfully translated formulas,
/// `Ok(None)` for type declarations (which don't produce constants),
/// and `Err` for translation failures.
pub fn translate_tptp_formula(
    ctx: &mut TptpTranslationContext,
    formula: &TptpFormula,
    problem_name: &str,
    source_file: Option<&str>,
) -> TptpTranslateResult<Option<TptpImportedConstant>> {
    // Type declarations don't produce proof-level constants.
    if formula.role == TptpRole::Type {
        return Ok(None);
    }

    let type_expr = translate_tptp_term(ctx, &formula.formula)?;
    let kind = TptpConstantKind::from(formula.role);

    // Axiom profile: all TPTP imports depend on the ATP axiom embedding.
    let axiom_profile = AxiomProfile::ATP_CERT;

    // Trust level: TPTP axioms are axiomatized; theorems trusted from the source.
    let trust_level = match kind {
        TptpConstantKind::Axiom => TrustLevel::PartiallyAxiomatized,
        TptpConstantKind::Conjecture => TrustLevel::PartiallyAxiomatized,
        TptpConstantKind::Theorem => TrustLevel::TrustedOracle,
        _ => TrustLevel::PartiallyAxiomatized,
    };

    let name = format!("TPTP.{problem_name}.{}", formula.name);

    Ok(Some(TptpImportedConstant {
        name: name.clone(),
        type_expr: format!("{type_expr:?}"),
        kind,
        axiom_profile,
        trust_level,
        provenance: Provenance {
            source: SourceSystem::Atp,
            original_name: name,
            source_file: source_file.map(String::from),
            axiom_profile,
        },
    }))
}

/// Convenience: translate a TPTP term from a fresh context.
pub fn translate_tptp_term_fresh(term: &TptpTerm) -> Result<Expr, TptpTranslateError> {
    let mut ctx = TptpTranslationContext::new();
    translate_tptp_term(&mut ctx, term)
}

// ════════════════════════════════════════════════════════════════════════════
// Tests
// ════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_translate_atom() {
        let term = TptpTerm::Atom("p".to_owned());
        let expr = translate_tptp_term_fresh(&term).expect("should translate");
        match expr.kind() {
            ExprKind::Const(name, _) => {
                assert_eq!(*name, Name::from_string("TPTP.p"));
            }
            other => panic!("expected Const, got {other:?}"),
        }
    }

    #[test]
    fn test_translate_var_bound() {
        let term = TptpTerm::ForAll(
            vec!["X".to_owned()],
            Box::new(TptpTerm::Var("X".to_owned())),
        );
        let expr = translate_tptp_term_fresh(&term).expect("should translate");
        // Should be Pi(individual, BVar(0))
        match expr.kind() {
            ExprKind::Pi(_, _, body) => {
                assert!(matches!(body.kind(), ExprKind::BVar(0)));
            }
            other => panic!("expected Pi, got {other:?}"),
        }
    }

    #[test]
    fn test_translate_var_free() {
        let term = TptpTerm::Var("X".to_owned());
        let expr = translate_tptp_term_fresh(&term).expect("should translate");
        match expr.kind() {
            ExprKind::Const(name, _) => {
                assert_eq!(*name, Name::from_string("TPTP.fvar.X"));
            }
            other => panic!("expected Const for free var, got {other:?}"),
        }
    }

    #[test]
    fn test_translate_not() {
        let term = TptpTerm::Not(Box::new(TptpTerm::Atom("p".to_owned())));
        let expr = translate_tptp_term_fresh(&term).expect("should translate");
        // ~P = P -> False, which is Pi(P, False)
        match expr.kind() {
            ExprKind::Pi(_, _, _) => { /* arrow to False */ }
            other => panic!("expected Pi (arrow), got {other:?}"),
        }
    }

    #[test]
    fn test_translate_and() {
        let term = TptpTerm::And(
            Box::new(TptpTerm::Atom("p".to_owned())),
            Box::new(TptpTerm::Atom("q".to_owned())),
        );
        let expr = translate_tptp_term_fresh(&term).expect("should translate");
        match expr.kind() {
            ExprKind::App(_, _) => { /* And applied to p and q */ }
            other => panic!("expected App (And), got {other:?}"),
        }
    }

    #[test]
    fn test_translate_implies() {
        let term = TptpTerm::Implies(
            Box::new(TptpTerm::Atom("p".to_owned())),
            Box::new(TptpTerm::Atom("q".to_owned())),
        );
        let expr = translate_tptp_term_fresh(&term).expect("should translate");
        match expr.kind() {
            ExprKind::Pi(_, _, _) => { /* arrow: p -> q */ }
            other => panic!("expected Pi (arrow), got {other:?}"),
        }
    }

    #[test]
    fn test_translate_eq() {
        let term = TptpTerm::Eq(
            Box::new(TptpTerm::Var("X".to_owned())),
            Box::new(TptpTerm::Var("Y".to_owned())),
        );
        let expr = translate_tptp_term_fresh(&term).expect("should translate");
        // Eq applied to individual, X, Y
        match expr.kind() {
            ExprKind::App(_, _) => { /* Eq application */ }
            other => panic!("expected App (Eq), got {other:?}"),
        }
    }

    #[test]
    fn test_translate_exists() {
        let term = TptpTerm::Exists(
            vec!["X".to_owned()],
            Box::new(TptpTerm::Func(
                "p".to_owned(),
                vec![TptpTerm::Var("X".to_owned())],
            )),
        );
        let expr = translate_tptp_term_fresh(&term).expect("should translate");
        // Exists (fun X : individual => p(X))
        match expr.kind() {
            ExprKind::App(func, _) => match func.kind() {
                ExprKind::Const(name, _) => {
                    assert_eq!(*name, Name::from_string("Exists"));
                }
                other => panic!("expected Const(Exists), got {other:?}"),
            },
            other => panic!("expected App, got {other:?}"),
        }
    }

    #[test]
    fn test_translate_true_false() {
        let t = translate_tptp_term_fresh(&TptpTerm::True).expect("should translate");
        match t.kind() {
            ExprKind::Const(name, _) => assert_eq!(*name, Name::from_string("True")),
            other => panic!("expected Const(True), got {other:?}"),
        }
        let f = translate_tptp_term_fresh(&TptpTerm::False).expect("should translate");
        match f.kind() {
            ExprKind::Const(name, _) => assert_eq!(*name, Name::from_string("False")),
            other => panic!("expected Const(False), got {other:?}"),
        }
    }

    #[test]
    fn test_translate_formula_axiom() {
        let formula = TptpFormula {
            name: "ax1".to_owned(),
            language: super::super::types::TptpLanguage::Fof,
            role: TptpRole::Axiom,
            formula: TptpTerm::Atom("p".to_owned()),
        };
        let mut ctx = TptpTranslationContext::new();
        let result =
            translate_tptp_formula(&mut ctx, &formula, "TEST", None).expect("should translate");
        let c = result.expect("should produce constant");
        assert_eq!(c.kind, TptpConstantKind::Axiom);
        assert_eq!(c.name, "TPTP.TEST.ax1");
        assert_eq!(c.trust_level, TrustLevel::PartiallyAxiomatized);
        assert_eq!(c.provenance.source, SourceSystem::Atp);
    }

    #[test]
    fn test_translate_formula_conjecture() {
        let formula = TptpFormula {
            name: "goal".to_owned(),
            language: super::super::types::TptpLanguage::Fof,
            role: TptpRole::Conjecture,
            formula: TptpTerm::Atom("q".to_owned()),
        };
        let mut ctx = TptpTranslationContext::new();
        let result = translate_tptp_formula(&mut ctx, &formula, "PROB", Some("prob.p"))
            .expect("should translate");
        let c = result.expect("should produce constant");
        assert_eq!(c.kind, TptpConstantKind::Conjecture);
        assert_eq!(c.provenance.source_file, Some("prob.p".to_owned()));
    }

    #[test]
    fn test_translate_formula_type_decl_skipped() {
        let formula = TptpFormula {
            name: "color_decl".to_owned(),
            language: super::super::types::TptpLanguage::Tff,
            role: TptpRole::Type,
            formula: TptpTerm::Atom("color".to_owned()),
        };
        let mut ctx = TptpTranslationContext::new();
        let result =
            translate_tptp_formula(&mut ctx, &formula, "TEST", None).expect("should succeed");
        assert!(result.is_none(), "type decl should not produce constant");
    }

    #[test]
    fn test_translate_neq() {
        let term = TptpTerm::Neq(
            Box::new(TptpTerm::Atom("a".to_owned())),
            Box::new(TptpTerm::Atom("b".to_owned())),
        );
        let expr = translate_tptp_term_fresh(&term).expect("should translate");
        // a != b = (Eq individual a b) -> False
        match expr.kind() {
            ExprKind::Pi(_, domain, codomain) => {
                // domain should be Eq application
                assert!(matches!(domain.kind(), ExprKind::App(_, _)));
                // codomain should be False
                assert!(
                    matches!(codomain.kind(), ExprKind::Const(name, _) if *name == Name::from_string("False"))
                );
            }
            other => panic!("expected Pi (arrow to False), got {other:?}"),
        }
    }

    #[test]
    fn test_translate_multi_var_forall() {
        let term = TptpTerm::ForAll(
            vec!["X".to_owned(), "Y".to_owned()],
            Box::new(TptpTerm::Eq(
                Box::new(TptpTerm::Var("X".to_owned())),
                Box::new(TptpTerm::Var("Y".to_owned())),
            )),
        );
        let expr = translate_tptp_term_fresh(&term).expect("should translate");
        // Should be Pi(individual, Pi(individual, Eq ...))
        match expr.kind() {
            ExprKind::Pi(_, _, body) => {
                assert!(matches!(body.kind(), ExprKind::Pi(_, _, _)));
            }
            other => panic!("expected nested Pi, got {other:?}"),
        }
    }
}
