// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_auto::bridge::proof_translation_contract::{
    classify_for_proof_translation, SmtLogicalForm,
};
use clean_kernel::expr::Literal;
use clean_kernel::{Expr, ExprKind, FVarId};

use super::{
    RegisteredFVarDecl, RegisteredFVarKind, SmtFuncDecl, SmtLibTranslator, SmtSort, SmtVarDecl,
    TranslateError, TranslatedTerm,
};

impl SmtLibTranslator {
    /// Emit a `(declare-const <name> <sort>)` declaration and push a
    /// corresponding `SmtVarDecl`.
    ///
    /// This is the single owner of constant-declaration emission. All call
    /// sites that need a new SMT constant should go through this helper.
    /// Part of #2818.
    pub(super) fn emit_const_decl(&mut self, name: &str, sort: SmtSort, lean_expr: Option<Expr>) {
        self.declarations
            .push(format!("(declare-const {name} {})", sort.smtlib_name()));
        self.var_decls.push(SmtVarDecl {
            name: name.to_owned(),
            sort,
            lean_expr,
        });
    }

    /// Emit a `(declare-fun <name> (<domains>) <result>)` declaration and push
    /// a corresponding `SmtFuncDecl`, caching in `fvar_func_decls`.
    ///
    /// This is the single owner of function-declaration emission. Part of #2818.
    fn emit_func_decl(
        &mut self,
        id: FVarId,
        name: &str,
        domain_sorts: &[SmtSort],
        result_sort: SmtSort,
        lean_expr: Expr,
        lean_ty: Expr,
    ) {
        self.declarations.push(format!(
            "(declare-fun {} ({}) {})",
            name,
            domain_sorts
                .iter()
                .map(|sort| sort.smtlib_name())
                .collect::<Vec<_>>()
                .join(" "),
            result_sort.smtlib_name()
        ));
        let decl = SmtFuncDecl {
            name: name.to_owned(),
            domain_sorts: domain_sorts.to_vec(),
            result_sort,
            lean_expr,
            lean_ty,
        };
        self.func_decls.push(decl.clone());
        self.fvar_func_decls.insert(id, decl);
    }

    /// Register a free variable with an explicit SMT sort.
    ///
    /// Reuses the canonical SMT name and emits at most one declaration for a
    /// given `FVarId`.
    pub fn register_fvar(&mut self, id: FVarId, sort: SmtSort, original_expr: Expr) -> String {
        if let Some(existing) = self.registered_fvars.get(&id) {
            debug_assert_eq!(
                existing.kind,
                RegisteredFVarKind::Scalar(sort),
                "FVar {id:?} re-registered with conflicting SMT kinds"
            );
            return existing.name.clone();
        }

        let name = Self::canonical_fvar_name(id);
        self.emit_const_decl(&name, sort, Some(original_expr.clone()));
        self.registered_fvars.insert(
            id,
            RegisteredFVarDecl {
                name: name.clone(),
                kind: RegisteredFVarKind::Scalar(sort),
                lean_expr: Some(original_expr),
                lean_ty: None,
            },
        );
        name
    }

    /// Register a callable free variable that may appear in application head
    /// position.
    ///
    /// This preserves the canonical SMT symbol and Lean function type but
    /// intentionally delays `(declare-fun ...)` emission until first use so the
    /// domain sorts come from the translated arguments.
    pub fn register_callable_fvar(
        &mut self,
        id: FVarId,
        result_sort: SmtSort,
        original_expr: Expr,
        lean_ty: Expr,
    ) -> String {
        if let Some(existing) = self.registered_fvars.get(&id) {
            debug_assert_eq!(
                existing.kind,
                RegisteredFVarKind::Callable { result_sort },
                "FVar {id:?} re-registered with conflicting callable SMT kinds"
            );
            debug_assert_eq!(
                existing.lean_ty.as_ref(),
                Some(&lean_ty),
                "FVar {id:?} re-registered with conflicting Lean function types"
            );
            return existing.name.clone();
        }

        let name = Self::canonical_fvar_name(id);
        self.registered_fvars.insert(
            id,
            RegisteredFVarDecl {
                name: name.clone(),
                kind: RegisteredFVarKind::Callable { result_sort },
                lean_expr: Some(original_expr),
                lean_ty: Some(lean_ty),
            },
        );
        name
    }

    /// Translate a kernel Expr to an SMT-LIB2 string.
    ///
    /// REQUIRES: `expr` is a well-formed kernel expression.
    /// ENSURES: Returns Ok(s) where s is a valid SMT-LIB2 term string, or
    ///   Err for genuinely unsupported expression kinds.
    ///   Side-effects: may add declarations to `self.declarations` and `self.var_decls`.
    pub fn translate_expr(&mut self, expr: &Expr) -> Result<String, TranslateError> {
        self.translate_expr_typed(expr).map(|term| term.smt)
    }

    pub(super) fn translate_expr_typed(
        &mut self,
        expr: &Expr,
    ) -> Result<TranslatedTerm, TranslateError> {
        match expr.kind() {
            ExprKind::FVar(id) => self.translate_fvar(*id),
            ExprKind::Lit(lit) => Ok(self.translate_literal(lit, expr)),
            ExprKind::Const(name, _) => self.translate_const(&name.to_string()),
            ExprKind::MData(_, inner) => self.translate_expr_typed(inner),
            // Pi and App expressions route through the shared classifier (#2810).
            // Recognized semantic forms (connectives, comparisons, arithmetic,
            // quantifiers) go to `translate_classified` in `classified.rs`.
            // Atoms (unrecognized by classifier) fall to the atom boundary.
            ExprKind::Pi(..) | ExprKind::App(..) => self.translate_via_classifier(expr),
            _ => Err(TranslateError::UnsupportedExpr(
                "unsupported expression kind for SMT-LIB".to_string(),
            )),
        }
    }

    /// Route App and Pi expressions through the shared `LogicalForm` classifier.
    ///
    /// Recognized forms go to `translate_classified()` (classified.rs).
    /// `SmtLogicalForm::Atom` (not recognized by the classifier) falls through
    /// to the atom boundary in `const_app.rs`.
    fn translate_via_classifier(&mut self, expr: &Expr) -> Result<TranslatedTerm, TranslateError> {
        let form = classify_for_proof_translation(expr);
        match form {
            SmtLogicalForm::Atom(atom) => {
                // Not recognized by classifier — delegate to atom boundary.
                let head = atom.get_app_fn().strip_mdata();
                let args = atom.get_app_args();
                match head.kind() {
                    ExprKind::Const(name, _) => {
                        self.translate_atom_const_app(&name.to_string(), &args)
                    }
                    ExprKind::FVar(id) => self.translate_fvar_app(*id, &args),
                    _ => Err(TranslateError::UnsupportedExpr(
                        "unsupported application head for SMT-LIB".to_string(),
                    )),
                }
            }
            classified => self.translate_classified(classified),
        }
    }

    /// Translate a previously registered free variable.
    ///
    /// REQUIRES: `register_fvar` ran for `id` when the verifiable SMT lane is
    /// expected to translate this expression.
    /// ENSURES: Returns the previously registered SMT-LIB variable name.
    fn translate_fvar(&mut self, id: FVarId) -> Result<TranslatedTerm, TranslateError> {
        self.registered_fvars
            .get(&id)
            .ok_or_else(|| {
                TranslateError::UnsupportedExpr(format!(
                    "unregistered FVar {id:?}; call register_fvar before translation"
                ))
            })
            .and_then(|decl| match decl.kind {
                RegisteredFVarKind::Scalar(sort) => Ok(TranslatedTerm {
                    smt: decl.name.clone(),
                    sort,
                }),
                RegisteredFVarKind::Callable { .. } => Err(TranslateError::UnsupportedExpr(
                    format!("callable FVar {id:?} must appear in application head position"),
                )),
            })
    }

    fn translate_fvar_app(
        &mut self,
        id: FVarId,
        args: &[&Expr],
    ) -> Result<TranslatedTerm, TranslateError> {
        let registered = self.registered_fvars.get(&id).cloned().ok_or_else(|| {
            TranslateError::UnsupportedExpr(format!(
                "unregistered FVar {id:?}; call register_fvar before translation"
            ))
        })?;

        let RegisteredFVarKind::Callable { result_sort } = registered.kind else {
            return Err(TranslateError::UnsupportedExpr(format!(
                "scalar FVar {id:?} cannot appear in application head position"
            )));
        };

        let mut translated_args = Vec::with_capacity(args.len());
        let mut domain_sorts = Vec::with_capacity(args.len());
        for arg in args {
            let translated = self.translate_expr_typed(arg)?;
            domain_sorts.push(translated.sort);
            translated_args.push(translated.smt);
        }

        if let Some(existing) = self.fvar_func_decls.get(&id) {
            if existing.domain_sorts.len() != domain_sorts.len() {
                return Err(TranslateError::UnsupportedExpr(format!(
                    "FVar {id:?} applied with {} args, but previously declared with arity {}",
                    domain_sorts.len(),
                    existing.domain_sorts.len()
                )));
            }
            if existing.domain_sorts != domain_sorts {
                return Err(TranslateError::UnsupportedExpr(format!(
                    "FVar {id:?} applied with incompatible domain sorts {:?}; expected {:?}",
                    domain_sorts, existing.domain_sorts
                )));
            }
        } else {
            let lean_expr = registered.lean_expr.clone().ok_or_else(|| {
                TranslateError::UnsupportedExpr(format!(
                    "callable FVar {id:?} missing Lean expression metadata"
                ))
            })?;
            let lean_ty = registered.lean_ty.clone().ok_or_else(|| {
                TranslateError::UnsupportedExpr(format!(
                    "callable FVar {id:?} missing Lean type metadata"
                ))
            })?;
            self.emit_func_decl(
                id,
                &registered.name,
                &domain_sorts,
                result_sort,
                lean_expr,
                lean_ty,
            );
        }

        Ok(TranslatedTerm {
            smt: format!("({} {})", registered.name, translated_args.join(" ")),
            sort: result_sort,
        })
    }

    /// Translate a literal value.
    ///
    /// ENSURES: Nat literals produce their decimal string; string literals
    ///   produce stable opaque Int constants deduplicated by literal value.
    fn translate_literal(&mut self, lit: &Literal, original_expr: &Expr) -> TranslatedTerm {
        match lit {
            Literal::Nat(n) => TranslatedTerm {
                smt: n.to_string(),
                sort: SmtSort::Int,
            },
            Literal::String(value) => {
                if let Some(cached) = self.string_constants.get(value.as_ref()) {
                    return TranslatedTerm {
                        smt: cached.clone(),
                        sort: SmtSort::Int,
                    };
                }

                let name = format!("str_{}", self.fresh_counter);
                self.fresh_counter += 1;
                self.emit_const_decl(&name, SmtSort::Int, Some(original_expr.clone()));
                self.string_constants
                    .insert(value.as_ref().to_owned(), name.clone());
                TranslatedTerm {
                    smt: name,
                    sort: SmtSort::Int,
                }
            }
        }
    }

    /// Translate a constant reference.
    ///
    /// REQUIRES: `name` is a Lean constant name string.
    /// ENSURES: True/False map to SMT-LIB "true"/"false". Explicitly registered
    ///   exact-name symbols round-trip through `const_names`. Other constants fail closed.
    fn translate_const(&mut self, name: &str) -> Result<TranslatedTerm, TranslateError> {
        if let Some(cached) = self.const_names.get(name) {
            return Ok(TranslatedTerm {
                smt: cached.name.clone(),
                sort: cached.sort,
            });
        }

        match name {
            "True" | "true" | "Bool.true" => Ok(TranslatedTerm {
                smt: String::from("true"),
                sort: SmtSort::Bool,
            }),
            "False" | "false" | "Bool.false" => Ok(TranslatedTerm {
                smt: String::from("false"),
                sort: SmtSort::Bool,
            }),
            _ => Err(TranslateError::UnsupportedExpr(format!(
                "unknown constant: {name}"
            ))),
        }
    }

    /// Build a complete SMT-LIB2 problem string with all declarations and assertion.
    ///
    /// REQUIRES: `assertion` is a valid SMT-LIB2 term string. `logic` is a valid
    ///   SMT-LIB2 logic name (e.g., "QF_LIA", "QF_BV", "QF_UF").
    /// ENSURES: Returns a complete SMT-LIB2 problem with set-logic, produce-proofs,
    ///   all collected declarations, assertion, check-sat, and get-proof commands.
    #[cfg(test)]
    pub(super) fn build_problem(&self, assertion: &str, logic: &str) -> String {
        let mut s = format!("(set-logic {logic})\n");
        s.push_str("(set-option :produce-proofs true)\n");
        for decl in &self.declarations {
            s.push_str(decl);
            s.push('\n');
        }
        s.push_str(&format!("(assert {assertion})\n"));
        s.push_str("(check-sat)\n(get-proof)\n");
        s
    }

    /// Return collected declarations.
    pub fn declarations(&self) -> &[String] {
        &self.declarations
    }

    /// Return structured variable declarations (name + sort).
    ///
    /// Use this to declare variables in AyProofBackend via `fresh_int`/`fresh_bool`
    /// before asserting the translated formula.
    pub fn var_declarations(&self) -> &[SmtVarDecl] {
        &self.var_decls
    }

    /// Return structured function declarations (name + signature + Lean metadata).
    pub fn func_declarations(&self) -> &[SmtFuncDecl] {
        &self.func_decls
    }

    /// Return existential Skolemization metadata recorded so far.
    pub fn exists_skolemizations(&self) -> &[super::ExistsSkolemization] {
        &self.exists_skolemizations
    }
}
