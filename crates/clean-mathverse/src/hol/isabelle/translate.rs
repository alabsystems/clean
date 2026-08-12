// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Isabelle-to-clean type/term translator.
//!
//! Maps Isabelle/Pure's simply-typed higher-order logic into clean's
//! dependent type theory:
//!
//! - `IsaType::TFree/TVar` → universe-polymorphic type variable (Sort/Const)
//! - `IsaType::Type("fun", [a, b])` → Pi type (arrow)
//! - `IsaType::Type("bool", [])` → Prop
//! - `IsaType::Type("prop", [])` → Prop
//! - `IsaType::Type(name, args)` → Const applied to args
//! - `IsaTerm::Bound(i)` → BVar(i)
//! - `IsaTerm::Free(name, ty)` → Const (free vars become named constants)
//! - `IsaTerm::Const(name, ty)` → Const
//! - `IsaTerm::Abs(name, ty, body)` → Lam
//! - `IsaTerm::App(f, x)` → App

use super::types::{IsaTerm, IsaTheorem, IsaTheoryExport, IsaType, ProofStatus};
use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};
use clean_kernel::{BinderInfo, Expr, Name};
use thiserror::Error;

/// Errors raised during Isabelle-to-clean translation.
#[derive(Debug, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum TranslateError {
    #[error("unsupported Isabelle type constructor: {name} (arity {arity})")]
    UnsupportedType { name: String, arity: usize },
    #[error("unsupported Isabelle term: {description}")]
    UnsupportedTerm { description: String },
    #[error("empty theorem proposition list for {name}")]
    EmptyProps { name: String },
}

/// A translated Isabelle theorem ready for Mathverse import.
#[derive(Clone, Debug)]
pub struct TranslatedTheorem {
    pub name: String,
    pub type_expr: Expr,
    pub proof_status: ProofStatus,
    pub axiom_profile: AxiomProfile,
    pub trust_level: TrustLevel,
    pub provenance: Provenance,
}

/// Isabelle base axiom profile: classical logic + extensionality + LCF-erased proofs.
const ISA_BASE_PROFILE: AxiomProfile = AxiomProfile(
    AxiomProfile::CLASSICAL.0
        | AxiomProfile::EXTENSIONALITY.0
        | AxiomProfile::ISABELLE_LCF_ERASED.0,
);

/// Isabelle-to-clean translator.
///
/// Translates Isabelle types, terms, and theorems into clean kernel expressions.
/// The translator is stateless — each translation is independent.
pub struct IsabelleTranslator {
    theory_name: String,
}

impl IsabelleTranslator {
    /// Create a new translator for the given Isabelle theory.
    #[must_use]
    pub fn new(theory_name: &str) -> Self {
        Self {
            theory_name: theory_name.to_owned(),
        }
    }

    /// Translate an Isabelle type to a clean expression.
    ///
    /// # Errors
    ///
    /// Returns `TranslateError::UnsupportedType` for unknown type constructors
    /// that cannot be mapped to clean.
    pub fn translate_type(&self, isa_type: &IsaType) -> Result<Expr, TranslateError> {
        match isa_type {
            IsaType::TFree { name, .. } | IsaType::TVar { name, .. } => {
                // Type variables become named constants at Type level.
                Ok(Expr::const_str(name))
            }
            IsaType::Type { name, args } => self.translate_type_constructor(name, args),
        }
    }

    fn translate_type_constructor(
        &self,
        name: &str,
        args: &[IsaType],
    ) -> Result<Expr, TranslateError> {
        match (name, args.len()) {
            // fun(a, b) → arrow type
            ("fun", 2) => {
                let domain = self.translate_type(&args[0])?;
                let codomain = self.translate_type(&args[1])?;
                Ok(Expr::arrow(domain, codomain))
            }
            // bool/prop → Prop
            ("HOL.bool" | "bool" | "prop", 0) => Ok(Expr::prop()),
            // nat → Const "Nat"
            ("Nat.nat" | "nat", 0) => Ok(Expr::const_str("Nat")),
            // int → Const "Int"
            ("Int.int" | "int", 0) => Ok(Expr::const_str("Int")),
            // list(a) → Const "List" applied to translated arg
            ("List.list" | "list", 1) => {
                let elem = self.translate_type(&args[0])?;
                Ok(Expr::app(Expr::const_str("List"), elem))
            }
            // set(a) → Const "Set" applied to translated arg
            ("Set.set" | "set", 1) => {
                let elem = self.translate_type(&args[0])?;
                Ok(Expr::app(Expr::const_str("Set"), elem))
            }
            // prod(a, b) → Const "Prod" applied to args
            ("Product_Type.prod" | "prod", 2) => {
                let a = self.translate_type(&args[0])?;
                let b = self.translate_type(&args[1])?;
                Ok(Expr::app(Expr::app(Expr::const_str("Prod"), a), b))
            }
            // Nullary type constructor → named constant
            (_, 0) => Ok(Expr::const_str(name)),
            // N-ary type constructor → applied constant
            _ => {
                let mut result = Expr::const_str(name);
                for arg in args {
                    let translated = self.translate_type(arg)?;
                    result = Expr::app(result, translated);
                }
                Ok(result)
            }
        }
    }

    /// Translate an Isabelle term to a clean expression.
    ///
    /// # Errors
    ///
    /// Returns `TranslateError::UnsupportedTerm` for term forms that cannot
    /// be represented in clean.
    pub fn translate_term(&self, term: &IsaTerm) -> Result<Expr, TranslateError> {
        match term {
            IsaTerm::Bound(idx) => Ok(Expr::bvar(*idx)),
            IsaTerm::Free { name, .. } => Ok(Expr::const_str(name)),
            IsaTerm::Var { name, index, .. } => {
                // Schematic variables: encode as "?name.index"
                let full_name = if *index == 0 {
                    format!("?{name}")
                } else {
                    format!("?{name}.{index}")
                };
                Ok(Expr::const_(Name::from_string(&full_name), vec![]))
            }
            IsaTerm::Const { name, .. } => Ok(Expr::const_str(name)),
            IsaTerm::Abs { name: _, ty, body } => {
                let lean_ty = self.translate_type(ty)?;
                let lean_body = self.translate_term(body)?;
                Ok(Expr::lam(BinderInfo::Default, lean_ty, lean_body))
            }
            IsaTerm::App { fun, arg } => {
                let lean_fun = self.translate_term(fun)?;
                let lean_arg = self.translate_term(arg)?;
                Ok(Expr::app(lean_fun, lean_arg))
            }
        }
    }

    /// Translate an Isabelle theorem to an Mathverse-importable form.
    ///
    /// The theorem's propositions are combined: hypotheses become Pi binders,
    /// with the conclusion as the final type. Single-proposition theorems
    /// translate directly.
    ///
    /// # Errors
    ///
    /// Returns `TranslateError::EmptyProps` if the theorem has no propositions.
    pub fn translate_theorem(&self, thm: &IsaTheorem) -> Result<TranslatedTheorem, TranslateError> {
        if thm.props.is_empty() {
            return Err(TranslateError::EmptyProps {
                name: thm.name.clone(),
            });
        }

        // Translate the conclusion (last prop) and hypotheses (all but last).
        let type_expr = if thm.props.len() == 1 {
            self.translate_term(&thm.props[0])?
        } else {
            // [H1, H2, ..., C] → H1 → H2 → ... → C
            let mut parts: Vec<Expr> = thm
                .props
                .iter()
                .map(|p| self.translate_term(p))
                .collect::<Result<_, _>>()?;
            // INVARIANT: this branch only runs when `thm.props.len() >= 2`
            // (the `len() == 1` case returned above), so `parts.len() >= 2`
            // and `pop()` is always Some.
            let conclusion = parts
                .pop()
                .expect("invariant: parts non-empty when props.len() >= 2");
            parts
                .into_iter()
                .rev()
                .fold(conclusion, |body, hyp| Expr::arrow(hyp, body))
        };

        let trust_level = match thm.proof_status {
            ProofStatus::Proved => TrustLevel::CertificateReplayed,
            ProofStatus::Axiomatized => TrustLevel::PartiallyAxiomatized,
        };

        let mut axiom_profile = ISA_BASE_PROFILE;
        if thm.proof_status == ProofStatus::Axiomatized {
            axiom_profile |= AxiomProfile::ISABELLE_LCF_ERASED;
        }

        Ok(TranslatedTheorem {
            name: thm.name.clone(),
            type_expr,
            proof_status: thm.proof_status,
            axiom_profile,
            trust_level,
            provenance: Provenance {
                source: SourceSystem::Isabelle,
                original_name: thm.name.clone(),
                source_file: Some(format!("{}.thy", self.theory_name)),
                axiom_profile,
            },
        })
    }

    /// Translate all theorems in a theory export.
    ///
    /// Returns successfully translated theorems and a count of failures.
    #[must_use]
    pub fn translate_theory(&self, export: &IsaTheoryExport) -> (Vec<TranslatedTheorem>, usize) {
        let mut results = Vec::with_capacity(export.theorems.len());
        let mut failures = 0;
        for thm in &export.theorems {
            match self.translate_theorem(thm) {
                Ok(translated) => results.push(translated),
                Err(_) => failures += 1,
            }
        }
        (results, failures)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn translator() -> IsabelleTranslator {
        IsabelleTranslator::new("Test.Theory")
    }

    // ── Type translation tests ──

    #[test]
    fn test_translate_type_tfree() {
        let t = translator();
        let isa_ty = IsaType::tfree("'a");
        let result = t.translate_type(&isa_ty).unwrap();
        assert!(format!("{result:?}").contains("'a"));
    }

    #[test]
    fn test_translate_type_bool_to_prop() {
        let t = translator();
        let isa_ty = IsaType::nullary("HOL.bool");
        let result = t.translate_type(&isa_ty).unwrap();
        // Should be Prop (Sort 0)
        assert!(format!("{result:?}").contains("Sort"));
    }

    #[test]
    fn test_translate_type_fun_to_arrow() {
        let t = translator();
        let isa_ty = IsaType::fun(IsaType::nullary("nat"), IsaType::nullary("HOL.bool"));
        let result = t.translate_type(&isa_ty).unwrap();
        // Should be Pi type
        assert!(format!("{result:?}").contains("Pi"));
    }

    #[test]
    fn test_translate_type_list() {
        let t = translator();
        let isa_ty = IsaType::Type {
            name: "List.list".to_owned(),
            args: vec![IsaType::nullary("nat")],
        };
        let result = t.translate_type(&isa_ty).unwrap();
        assert!(format!("{result:?}").contains("List"));
    }

    #[test]
    fn test_translate_type_prod() {
        let t = translator();
        let isa_ty = IsaType::Type {
            name: "Product_Type.prod".to_owned(),
            args: vec![IsaType::nullary("nat"), IsaType::nullary("HOL.bool")],
        };
        let result = t.translate_type(&isa_ty).unwrap();
        assert!(format!("{result:?}").contains("Prod"));
    }

    #[test]
    fn test_translate_type_nullary_custom() {
        let t = translator();
        let isa_ty = IsaType::nullary("MyTheory.mytype");
        let result = t.translate_type(&isa_ty).unwrap();
        let dbg = format!("{result:?}");
        assert!(dbg.contains("MyTheory") || dbg.contains("mytype"));
    }

    // ── Term translation tests ──

    #[test]
    fn test_translate_term_bound() {
        let t = translator();
        let term = IsaTerm::Bound(0);
        let result = t.translate_term(&term).unwrap();
        assert!(format!("{result:?}").contains("BVar(0)"));
    }

    #[test]
    fn test_translate_term_free() {
        let t = translator();
        let term = IsaTerm::Free {
            name: "x".to_owned(),
            ty: IsaType::nullary("nat"),
        };
        let result = t.translate_term(&term).unwrap();
        assert!(format!("{result:?}").contains("x"));
    }

    #[test]
    fn test_translate_term_const() {
        let t = translator();
        let term = IsaTerm::const_of("HOL.True", IsaType::nullary("HOL.bool"));
        let result = t.translate_term(&term).unwrap();
        let dbg = format!("{result:?}");
        assert!(dbg.contains("True"), "should reference True: {dbg}");
    }

    #[test]
    fn test_translate_term_abs() {
        let t = translator();
        let term = IsaTerm::abs("x", IsaType::nullary("nat"), IsaTerm::Bound(0));
        let result = t.translate_term(&term).unwrap();
        assert!(format!("{result:?}").contains("Lam"));
    }

    #[test]
    fn test_translate_term_app() {
        let t = translator();
        let term = IsaTerm::app(
            IsaTerm::const_of(
                "Suc",
                IsaType::fun(IsaType::nullary("nat"), IsaType::nullary("nat")),
            ),
            IsaTerm::const_of("zero", IsaType::nullary("nat")),
        );
        let result = t.translate_term(&term).unwrap();
        assert!(format!("{result:?}").contains("App"));
    }

    #[test]
    fn test_translate_term_schematic_var() {
        let t = translator();
        let term = IsaTerm::Var {
            name: "x".to_owned(),
            index: 0,
            ty: IsaType::nullary("nat"),
        };
        let result = t.translate_term(&term).unwrap();
        assert!(format!("{result:?}").contains("?x"));
    }

    // ── Theorem translation tests ──

    #[test]
    fn test_translate_simple_theorem() {
        let t = translator();
        let thm = IsaTheorem {
            name: "HOL.TrueI".to_owned(),
            props: vec![IsaTerm::const_of("HOL.True", IsaType::nullary("HOL.bool"))],
            proof_status: ProofStatus::Proved,
        };
        let result = t.translate_theorem(&thm).unwrap();
        assert_eq!(result.name, "HOL.TrueI");
        assert_eq!(result.trust_level, TrustLevel::CertificateReplayed);
        assert!(result.axiom_profile.contains(AxiomProfile::CLASSICAL));
    }

    #[test]
    fn test_translate_axiomatized_theorem() {
        let t = translator();
        let thm = IsaTheorem {
            name: "HOL.ext".to_owned(),
            props: vec![IsaTerm::const_of("HOL.ext", IsaType::nullary("HOL.bool"))],
            proof_status: ProofStatus::Axiomatized,
        };
        let result = t.translate_theorem(&thm).unwrap();
        assert_eq!(result.trust_level, TrustLevel::PartiallyAxiomatized);
        assert!(result
            .axiom_profile
            .contains(AxiomProfile::ISABELLE_LCF_ERASED));
    }

    #[test]
    fn test_translate_implication_theorem() {
        let t = translator();
        // [| P |] ==> Q  has props [P, Q]
        let thm = IsaTheorem {
            name: "mp".to_owned(),
            props: vec![
                IsaTerm::const_of("P", IsaType::nullary("HOL.bool")),
                IsaTerm::const_of("Q", IsaType::nullary("HOL.bool")),
            ],
            proof_status: ProofStatus::Proved,
        };
        let result = t.translate_theorem(&thm).unwrap();
        // Type should be P → Q (arrow)
        assert!(format!("{:?}", result.type_expr).contains("Pi"));
    }

    #[test]
    fn test_translate_empty_props_error() {
        let t = translator();
        let thm = IsaTheorem {
            name: "bad".to_owned(),
            props: vec![],
            proof_status: ProofStatus::Proved,
        };
        assert!(t.translate_theorem(&thm).is_err());
    }

    #[test]
    fn test_translate_theory() {
        let t = translator();
        let mut export = IsaTheoryExport::new("Test");
        export.theorems.push(IsaTheorem {
            name: "thm1".to_owned(),
            props: vec![IsaTerm::const_of("True", IsaType::nullary("HOL.bool"))],
            proof_status: ProofStatus::Proved,
        });
        export.theorems.push(IsaTheorem {
            name: "thm2".to_owned(),
            props: vec![],
            proof_status: ProofStatus::Proved,
        });
        let (results, failures) = t.translate_theory(&export);
        assert_eq!(results.len(), 1);
        assert_eq!(failures, 1);
    }

    #[test]
    fn test_provenance() {
        let t = translator();
        let thm = IsaTheorem {
            name: "Nat.add_comm".to_owned(),
            props: vec![IsaTerm::const_of("comm", IsaType::nullary("HOL.bool"))],
            proof_status: ProofStatus::Proved,
        };
        let result = t.translate_theorem(&thm).unwrap();
        assert_eq!(result.provenance.source, SourceSystem::Isabelle);
        assert_eq!(result.provenance.original_name, "Nat.add_comm");
        assert_eq!(
            result.provenance.source_file,
            Some("Test.Theory.thy".to_owned())
        );
    }
}
