// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Classifier-driven lowering for the proof-producing SMT translator.
//!
//! Owns `translate_classified(...)` which lowers `SmtLogicalForm` variants into
//! SMT-LIB2 strings. This replaces the local boolean/comparison/arithmetic/Exists
//! recognition tables that previously lived in `const_app.rs`.
//!
//! Part of #2810.

use clean_auto::bridge::proof_translation_contract::SmtLogicalForm;
use clean_kernel::{Expr, ExprKind, FVarId};

use super::{
    try_extract_concrete_int, try_extract_concrete_nat, ExistsSkolemization, RegisteredFVarDecl,
    RegisteredFVarKind, SmtLibTranslator, SmtSort, TranslateError, TranslatedTerm,
};

impl SmtLibTranslator {
    /// Translate a classifier-recognized semantic form to SMT-LIB2.
    ///
    /// Called from `translate_expr` for `App` and `Pi` expressions that the
    /// shared classifier recognized as logical connectives, comparisons,
    /// arithmetic operations, or quantifiers. `SmtLogicalForm::Atom` should
    /// NOT reach this method — it flows to the atom boundary instead.
    pub(super) fn translate_classified(
        &mut self,
        form: SmtLogicalForm,
    ) -> Result<TranslatedTerm, TranslateError> {
        match form {
            // --- Propositional ---
            SmtLogicalForm::And(a, b) => {
                let a = self.translate_expr_typed(&a)?;
                let b = self.translate_expr_typed(&b)?;
                Ok(TranslatedTerm {
                    smt: format!("(and {} {})", a.smt, b.smt),
                    sort: SmtSort::Bool,
                })
            }
            SmtLogicalForm::Or(a, b) => {
                let a = self.translate_expr_typed(&a)?;
                let b = self.translate_expr_typed(&b)?;
                Ok(TranslatedTerm {
                    smt: format!("(or {} {})", a.smt, b.smt),
                    sort: SmtSort::Bool,
                })
            }
            SmtLogicalForm::Not(a) => {
                let a = self.translate_expr_typed(&a)?;
                Ok(TranslatedTerm {
                    smt: format!("(not {})", a.smt),
                    sort: SmtSort::Bool,
                })
            }
            SmtLogicalForm::Implies(a, b) => {
                let a = self.translate_expr_typed(&a)?;
                let b = self.translate_expr_typed(&b)?;
                Ok(TranslatedTerm {
                    smt: format!("(=> {} {})", a.smt, b.smt),
                    sort: SmtSort::Bool,
                })
            }
            SmtLogicalForm::Iff(a, b) => {
                let a = self.translate_expr_typed(&a)?;
                let b = self.translate_expr_typed(&b)?;
                let a_smt = a.smt;
                let b_smt = b.smt;
                Ok(TranslatedTerm {
                    smt: format!("(and (=> {} {}) (=> {} {}))", a_smt, b_smt, b_smt, a_smt),
                    sort: SmtSort::Bool,
                })
            }
            SmtLogicalForm::True => Ok(TranslatedTerm {
                smt: String::from("true"),
                sort: SmtSort::Bool,
            }),
            SmtLogicalForm::False => Ok(TranslatedTerm {
                smt: String::from("false"),
                sort: SmtSort::Bool,
            }),

            // --- Equality ---
            SmtLogicalForm::Eq { lhs, rhs, .. } => {
                let lhs = self.translate_expr_typed(&lhs)?;
                let rhs = self.translate_expr_typed(&rhs)?;
                Ok(TranslatedTerm {
                    smt: format!("(= {} {})", lhs.smt, rhs.smt),
                    sort: SmtSort::Bool,
                })
            }
            SmtLogicalForm::Neq { lhs, rhs, .. } => {
                let lhs = self.translate_expr_typed(&lhs)?;
                let rhs = self.translate_expr_typed(&rhs)?;
                Ok(TranslatedTerm {
                    smt: format!("(not (= {} {}))", lhs.smt, rhs.smt),
                    sort: SmtSort::Bool,
                })
            }

            // --- Comparisons ---
            SmtLogicalForm::Lt { lhs, rhs, .. } => {
                let lhs = self.translate_expr_typed(&lhs)?;
                let rhs = self.translate_expr_typed(&rhs)?;
                Ok(TranslatedTerm {
                    smt: format!("(< {} {})", lhs.smt, rhs.smt),
                    sort: SmtSort::Bool,
                })
            }
            SmtLogicalForm::Le { lhs, rhs, .. } => {
                let lhs = self.translate_expr_typed(&lhs)?;
                let rhs = self.translate_expr_typed(&rhs)?;
                Ok(TranslatedTerm {
                    smt: format!("(<= {} {})", lhs.smt, rhs.smt),
                    sort: SmtSort::Bool,
                })
            }
            SmtLogicalForm::Gt { lhs, rhs, .. } => {
                let lhs = self.translate_expr_typed(&lhs)?;
                let rhs = self.translate_expr_typed(&rhs)?;
                Ok(TranslatedTerm {
                    smt: format!("(> {} {})", lhs.smt, rhs.smt),
                    sort: SmtSort::Bool,
                })
            }
            SmtLogicalForm::Ge { lhs, rhs, .. } => {
                let lhs = self.translate_expr_typed(&lhs)?;
                let rhs = self.translate_expr_typed(&rhs)?;
                Ok(TranslatedTerm {
                    smt: format!("(>= {} {})", lhs.smt, rhs.smt),
                    sort: SmtSort::Bool,
                })
            }

            // --- Arithmetic ---
            SmtLogicalForm::Add { lhs, rhs, .. } => {
                let lhs = self.translate_expr_typed(&lhs)?;
                let rhs = self.translate_expr_typed(&rhs)?;
                Ok(TranslatedTerm {
                    smt: format!("(+ {} {})", lhs.smt, rhs.smt),
                    sort: lhs.sort,
                })
            }
            SmtLogicalForm::Sub { ty, lhs, rhs } => {
                let lhs_s = self.translate_expr_typed(&lhs)?;
                let rhs_s = self.translate_expr_typed(&rhs)?;
                let sort = infer_smt_sort_from_type(&ty).ok_or_else(|| {
                    TranslateError::UnsupportedExpr(format!(
                        "unsupported subtraction type for SMT translation: {}",
                        ty
                    ))
                })?;
                if is_nat_type(&ty) {
                    // Nat.sub has monus semantics: max(a - b, 0)
                    let lhs_smt = lhs_s.smt;
                    let rhs_smt = rhs_s.smt;
                    Ok(TranslatedTerm {
                        smt: format!(
                            "(ite (>= {} {}) (- {} {}) 0)",
                            lhs_smt, rhs_smt, lhs_smt, rhs_smt
                        ),
                        sort,
                    })
                } else {
                    Ok(TranslatedTerm {
                        smt: format!("(- {} {})", lhs_s.smt, rhs_s.smt),
                        sort,
                    })
                }
            }
            SmtLogicalForm::Mul { lhs, rhs, .. } => {
                let lhs = self.translate_expr_typed(&lhs)?;
                let rhs = self.translate_expr_typed(&rhs)?;
                Ok(TranslatedTerm {
                    smt: format!("(* {} {})", lhs.smt, rhs.smt),
                    sort: lhs.sort,
                })
            }
            SmtLogicalForm::Div { ty, lhs, rhs } => {
                // Check concrete divisor BEFORE translating expressions so
                // symbolic Real denominators fail with the right error instead
                // of failing on unregistered FVar translation.
                if is_real_type(&ty) && !is_concrete_real_divisor(&rhs) {
                    return Err(TranslateError::UnsupportedExpr(
                        "Real division with symbolic denominator".to_string(),
                    ));
                }
                let lhs_s = self.translate_expr_typed(&lhs)?;
                let rhs_s = self.translate_expr_typed(&rhs)?;
                let sort = infer_smt_sort_from_type(&ty).ok_or_else(|| {
                    TranslateError::UnsupportedExpr(format!(
                        "unsupported division type for SMT translation: {}",
                        ty
                    ))
                })?;
                if is_nat_type(&ty) {
                    // Nat.div is total: Nat.div a 0 = 0
                    let lhs_smt = lhs_s.smt;
                    let rhs_smt = rhs_s.smt;
                    Ok(TranslatedTerm {
                        smt: format!("(ite (> {} 0) (div {} {}) 0)", rhs_smt, lhs_smt, rhs_smt),
                        sort,
                    })
                } else if is_real_type(&ty) {
                    Ok(TranslatedTerm {
                        smt: format!("(/ {} {})", lhs_s.smt, rhs_s.smt),
                        sort,
                    })
                } else {
                    Ok(TranslatedTerm {
                        smt: format!("(div {} {})", lhs_s.smt, rhs_s.smt),
                        sort,
                    })
                }
            }
            SmtLogicalForm::Mod { ty, lhs, rhs } => {
                let lhs_s = self.translate_expr_typed(&lhs)?;
                let rhs_s = self.translate_expr_typed(&rhs)?;
                let sort = infer_smt_sort_from_type(&ty).ok_or_else(|| {
                    TranslateError::UnsupportedExpr(format!(
                        "unsupported modulus type for SMT translation: {}",
                        ty
                    ))
                })?;
                if is_nat_type(&ty) {
                    // Nat.mod is total: Nat.mod a 0 = a
                    let lhs_smt = lhs_s.smt;
                    let rhs_smt = rhs_s.smt;
                    Ok(TranslatedTerm {
                        smt: format!(
                            "(ite (> {} 0) (mod {} {}) {})",
                            rhs_smt, lhs_smt, rhs_smt, lhs_smt
                        ),
                        sort,
                    })
                } else {
                    Ok(TranslatedTerm {
                        smt: format!("(mod {} {})", lhs_s.smt, rhs_s.smt),
                        sort,
                    })
                }
            }
            SmtLogicalForm::Neg { inner, .. } => {
                let a = self.translate_expr_typed(&inner)?;
                Ok(TranslatedTerm {
                    smt: format!("(- {})", a.smt),
                    sort: a.sort,
                })
            }

            // --- Quantifiers ---
            SmtLogicalForm::Forall { .. } => Err(TranslateError::UnsupportedExpr(
                "dependent Pi / forall not yet supported".to_string(),
            )),
            SmtLogicalForm::Exists {
                binder_type,
                body,
                predicate,
            } => self.translate_classified_exists(&binder_type, &body, &predicate),

            // Atom should not reach this path — it goes to the atom boundary.
            SmtLogicalForm::Atom(_) => Err(TranslateError::UnsupportedExpr(
                "Atom should not reach translate_classified".to_string(),
            )),

            // Future variants added to SmtLogicalForm (#[non_exhaustive]).
            _ => Err(TranslateError::UnsupportedExpr(
                "unrecognized SmtLogicalForm variant".to_string(),
            )),
        }
    }

    /// Translate existential quantifier via Skolemization: ∃x. P(x) → P(sk).
    ///
    /// REQUIRES: `body` has `BVar(0)` for the bound variable (extracted by
    /// the shared classifier). `predicate` is the raw second argument of the
    /// `Exists` application (for proof reconstruction metadata).
    /// ENSURES: Creates a fresh Skolem constant, instantiates the body, and
    /// records `ExistsSkolemization` for downstream proof reconstruction.
    fn translate_classified_exists(
        &mut self,
        binder_type: &Expr,
        body: &Expr,
        predicate: &Expr,
    ) -> Result<TranslatedTerm, TranslateError> {
        // Fail closed on non-lambda predicates to preserve the existing boundary.
        // The shared classifier eta-expands non-lambda predicates, but the
        // proof-producing lane does not support them yet. (#2787)
        let stripped_pred = predicate.strip_mdata();
        if !matches!(stripped_pred.kind(), ExprKind::Lam(..)) {
            return Err(TranslateError::UnsupportedExpr(
                "unsupported Exists predicate for SMT-LIB: expected lambda".to_string(),
            ));
        }

        let sort = infer_smt_sort_from_type(binder_type).ok_or_else(|| {
            TranslateError::UnsupportedExpr(format!(
                "unsupported Exists binder type for SMT translation: {}",
                binder_type
            ))
        })?;
        let skolem_idx = self.fresh_counter;
        let skolem_name = format!("sk_exists_{}", skolem_idx);
        self.fresh_counter += 1;
        self.emit_const_decl(&skolem_name, sort, None);
        // Allocate a translator-private FVar placeholder instead of a raw Const
        // to prevent collision with real Lean constants named `sk_exists_<n>`.
        // Part of #2848.
        let placeholder_id = FVarId::new(self.next_internal_fvar);
        self.next_internal_fvar += 1;
        assert!(
            !placeholder_id.is_sentinel(),
            "internal skolem FVar must not collide with sentinel range"
        );
        self.registered_fvars.insert(
            placeholder_id,
            RegisteredFVarDecl {
                name: skolem_name.clone(),
                kind: RegisteredFVarKind::Scalar(sort),
                lean_expr: None,
                lean_ty: None,
            },
        );
        self.exists_skolemizations.push(ExistsSkolemization {
            skolem_smt_name: skolem_name.clone(),
            binder_type: binder_type.clone(),
            predicate: predicate.clone(),
            translator_placeholder_fvar: placeholder_id,
        });
        let skolem_expr = Expr::fvar(placeholder_id);
        let instantiated = body.instantiate(&skolem_expr);
        self.translate_expr_typed(&instantiated)
    }
}

/// Infer SMT sort from a Lean type expression.
fn infer_smt_sort_from_type(lean_type: &Expr) -> Option<SmtSort> {
    let lean_type = lean_type.strip_mdata();
    if lean_type.is_prop() {
        return Some(SmtSort::Bool);
    }
    if lean_type.is_sort() {
        return None;
    }

    match lean_type.kind() {
        ExprKind::Const(name, _) => match name.to_string().as_str() {
            "Bool" => Some(SmtSort::Bool),
            "Nat" | "Int" => Some(SmtSort::Int),
            "Real" | "Rat" => Some(SmtSort::Real),
            _ => None,
        },
        _ => None,
    }
}

/// Check if a type expression is `Nat`.
fn is_nat_type(ty: &Expr) -> bool {
    matches!(
        ty.strip_mdata().kind(),
        ExprKind::Const(name, _) if name.to_string() == "Nat"
    )
}

/// Check if a type expression is `Real` or `Rat`.
///
/// Rat maps to SMT `Real` sort (dense ordered field) and uses the same
/// SMT-LIB division operator `/` (not integer `div`).
fn is_real_type(ty: &Expr) -> bool {
    matches!(
        ty.strip_mdata().kind(),
        ExprKind::Const(name, _) if matches!(name.to_string().as_str(), "Real" | "Rat")
    )
}

/// Check if an expression is a concrete Real divisor suitable for strict QF_LRA.
///
/// Accepts only exact constant forms that preserve the linear arithmetic
/// contract. Part of #2795.
fn is_concrete_real_divisor(expr: &Expr) -> bool {
    // Direct Nat literal (e.g. `2` in `x / 2`)
    if try_extract_concrete_nat(expr).is_some() {
        return true;
    }
    // Constructor-form Real: Real.ofNat n or Real.ofInt i
    if let ExprKind::App(f, a) = expr.kind() {
        if let ExprKind::Const(name, _) = f.kind() {
            match name.to_string().as_str() {
                "Real.ofNat" => return try_extract_concrete_nat(a).is_some(),
                "Real.ofInt" => return try_extract_concrete_int(a).is_some(),
                _ => {}
            }
        }
    }
    false
}
