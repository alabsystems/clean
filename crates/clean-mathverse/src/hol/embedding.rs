// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared HOL shallow embedding into clean kernel expressions.
//!
//! This module captures the simple type and term fragment shared by HOL Light,
//! HOL4, and Isabelle/HOL. The translation is intentionally shallow:
//! HOL function space becomes Lean arrows, HOL constants are namespaced under
//! `HOL.*`, and HOL booleans are mapped directly to `Prop`.
//!
//! The kernel expression API here uses de Bruijn indices for bound variables
//! and numeric `FVarId`s for open variables. Accordingly, lambda-bound HOL
//! variables become `Expr::bvar`, while free HOL variables are lowered to a
//! stable name-derived identifier.

use clean_kernel::{BinderInfo, Expr, Name as LeanName};
use serde::{Deserialize, Serialize};

use crate::types::AxiomProfile;

/// Base axiom profile required by the shared HOL shallow embedding.
pub(crate) const HOL_AXIOMS: AxiomProfile = AxiomProfile(
    AxiomProfile::CLASSICAL.0 | AxiomProfile::EXTENSIONALITY.0 | AxiomProfile::HOL_EMBEDDING.0,
);

/// Shared HOL simple types.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum HolType {
    /// HOL propositions / booleans.
    Bool,
    /// HOL individuals / infinity witness type.
    Ind,
    /// Non-dependent function type.
    Fun(Box<HolType>, Box<HolType>),
    /// Type variable.
    TyVar(String),
    /// Named type operator application.
    TyApp(String, Vec<HolType>),
}

/// Shared HOL terms.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum HolTerm {
    /// Term variable with its simple type.
    Var { name: String, ty: HolType },
    /// Named constant with its instantiated simple type.
    Const { name: String, ty: HolType },
    /// Application.
    App {
        func: Box<HolTerm>,
        arg: Box<HolTerm>,
    },
    /// Lambda abstraction.
    Abs {
        var_name: String,
        var_ty: HolType,
        body: Box<HolTerm>,
    },
}

/// HOL primitive inference rules shared across OpenTheory-style kernels.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum HolAxiom {
    Refl,
    Trans,
    MkComb,
    Abs,
    Beta,
    Assume,
    EqMp,
    DeductAntisym,
    InstType,
    InstTerm,
}

impl HolAxiom {
    /// Canonical OpenTheory-style rule name.
    #[must_use]
    pub const fn hol_axiom_name(&self) -> &'static str {
        match self {
            Self::Refl => "refl",
            Self::Trans => "trans",
            Self::MkComb => "mkComb",
            Self::Abs => "abs",
            Self::Beta => "beta",
            Self::Assume => "assume",
            Self::EqMp => "eqMp",
            Self::DeductAntisym => "deductAntisym",
            Self::InstType => "instType",
            Self::InstTerm => "instTerm",
        }
    }
}

/// Translate a shared HOL type into a clean kernel expression.
pub(crate) fn hol_type_to_clean(ty: &HolType) -> Expr {
    match ty {
        HolType::Bool => Expr::prop(),
        HolType::Ind => Expr::const_(hol_name("Ind"), vec![]),
        HolType::Fun(domain, codomain) => {
            Expr::arrow(hol_type_to_clean(domain), hol_type_to_clean(codomain))
        }
        HolType::TyVar(name) => Expr::const_(hol_name(&format!("TyVar.{name}")), vec![]),
        HolType::TyApp(name, args) => Expr::apps(
            Expr::const_(hol_name(name), vec![]),
            args.iter().map(hol_type_to_clean),
        ),
    }
}

/// Translate a shared HOL term into a clean kernel expression.
pub(crate) fn hol_term_to_clean(tm: &HolTerm) -> Expr {
    let mut binders = Vec::new();
    hol_term_to_clean_with_binders(tm, &mut binders)
}

fn hol_term_to_clean_with_binders<'a>(tm: &'a HolTerm, binders: &mut Vec<&'a str>) -> Expr {
    match tm {
        HolTerm::Var { name, .. } => bound_var_index(name, binders)
            .map(Expr::bvar)
            .unwrap_or_else(|| Expr::fvar(clean_kernel::FVarId::new(hol_fvar_id(name)))),
        HolTerm::Const { name, .. } => Expr::const_(hol_name(name), vec![]),
        HolTerm::App { func, arg } => Expr::app(
            hol_term_to_clean_with_binders(func, binders),
            hol_term_to_clean_with_binders(arg, binders),
        ),
        HolTerm::Abs {
            var_name,
            var_ty,
            body,
        } => {
            binders.push(var_name.as_str());
            let body_expr = hol_term_to_clean_with_binders(body, binders);
            binders.pop();
            Expr::lam(BinderInfo::Default, hol_type_to_clean(var_ty), body_expr)
        }
    }
}

fn hol_name(name: &str) -> LeanName {
    LeanName::from_string(&format!("HOL.{name}"))
}

fn hol_fvar_id(name: &str) -> u64 {
    const FNV_OFFSET: u64 = 0xcbf29ce484222325;
    const FNV_PRIME: u64 = 0x100000001b3;

    let mut hash = FNV_OFFSET;
    for byte in LeanName::from_string(name).to_string().bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}

fn bound_var_index(name: &str, binders: &[&str]) -> Option<u32> {
    binders
        .iter()
        .rev()
        .position(|binder| *binder == name)
        .map(|idx| idx as u32)
}

#[cfg(test)]
mod tests {
    use clean_kernel::{BinderInfo, Expr, ExprKind};

    use super::{hol_term_to_clean, hol_type_to_clean, HolAxiom, HolTerm, HolType, HOL_AXIOMS};
    use crate::types::AxiomProfile;

    #[test]
    fn translates_bool_and_ind_types() {
        assert_eq!(hol_type_to_clean(&HolType::Bool), Expr::prop());

        let ind = hol_type_to_clean(&HolType::Ind);
        assert!(matches!(
            ind.kind(),
            ExprKind::Const(name, levels)
                if *name == clean_kernel::Name::from_string("HOL.Ind") && levels.is_empty()
        ));
    }

    #[test]
    fn translates_function_and_type_application() {
        let ty = HolType::Fun(
            Box::new(HolType::TyApp(
                "list".to_owned(),
                vec![HolType::TyVar("a".to_owned())],
            )),
            Box::new(HolType::Bool),
        );
        let expr = hol_type_to_clean(&ty);
        let ExprKind::Pi(_, domain, body) = expr.kind() else {
            panic!("expected arrow translation");
        };
        assert!(matches!(
            domain.kind(),
            ExprKind::App(head, arg)
                if matches!(
                    head.kind(),
                    ExprKind::Const(name, _) if *name == clean_kernel::Name::from_string("HOL.list")
                ) && matches!(
                    arg.kind(),
                    ExprKind::Const(name, _) if *name == clean_kernel::Name::from_string("HOL.TyVar.a")
                )
        ));
        assert_eq!(body.as_ref(), &Expr::prop());
    }

    #[test]
    fn translates_free_variables_to_stable_fvars() {
        let tm = HolTerm::Var {
            name: "x".to_owned(),
            ty: HolType::Bool,
        };
        let expr = hol_term_to_clean(&tm);
        assert!(matches!(
            expr.kind(),
            ExprKind::FVar(id) if id.as_u64() == super::hol_fvar_id("x")
        ));
    }

    #[test]
    fn translates_constants_and_applications() {
        let tm = HolTerm::App {
            func: Box::new(HolTerm::Const {
                name: "AND".to_owned(),
                ty: HolType::Fun(Box::new(HolType::Bool), Box::new(HolType::Bool)),
            }),
            arg: Box::new(HolTerm::Var {
                name: "p".to_owned(),
                ty: HolType::Bool,
            }),
        };
        let expr = hol_term_to_clean(&tm);
        assert!(matches!(
            expr.kind(),
            ExprKind::App(func, arg)
                if matches!(
                    func.kind(),
                    ExprKind::Const(name, _) if *name == clean_kernel::Name::from_string("HOL.AND")
                ) && matches!(
                    arg.kind(),
                    ExprKind::FVar(id) if id.as_u64() == super::hol_fvar_id("p")
                )
        ));
    }

    #[test]
    fn translates_abstractions_with_de_bruijn_indices() {
        let tm = HolTerm::Abs {
            var_name: "x".to_owned(),
            var_ty: HolType::Bool,
            body: Box::new(HolTerm::App {
                func: Box::new(HolTerm::Var {
                    name: "x".to_owned(),
                    ty: HolType::Fun(Box::new(HolType::Bool), Box::new(HolType::Bool)),
                }),
                arg: Box::new(HolTerm::Var {
                    name: "x".to_owned(),
                    ty: HolType::Bool,
                }),
            }),
        };
        let expr = hol_term_to_clean(&tm);
        let ExprKind::Lam(info, ty, body) = expr.kind() else {
            panic!("expected lambda translation");
        };
        assert_eq!(info.info, BinderInfo::Default);
        assert_eq!(ty.as_ref(), &Expr::prop());
        assert!(matches!(
            body.kind(),
            ExprKind::App(func, arg)
                if matches!(func.kind(), ExprKind::BVar(0))
                    && matches!(arg.kind(), ExprKind::BVar(0))
        ));
    }

    #[test]
    fn hol_axiom_names_and_profile_match_expected_base() {
        assert_eq!(HolAxiom::DeductAntisym.hol_axiom_name(), "deductAntisym");
        assert!(HOL_AXIOMS.contains(AxiomProfile::CLASSICAL));
        assert!(HOL_AXIOMS.contains(AxiomProfile::EXTENSIONALITY));
        assert!(HOL_AXIOMS.contains(AxiomProfile::HOL_EMBEDDING));
    }
}
