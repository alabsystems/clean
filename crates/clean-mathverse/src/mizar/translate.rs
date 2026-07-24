// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! FOL-to-DTT translation: Mizar terms -> clean kernel Expr.
//!
//! Mizar uses classical first-order logic with a soft typing system, which
//! differs fundamentally from clean's dependent type theory. The translation
//! maps:
//!
//! - `ForAll` -> Pi type in Prop
//! - `Exists` -> Sigma/exists in Prop
//! - `Not/And/Or/Implies` -> logical connectives
//! - `Pred` -> constant application
//! - `Var` -> bound variable (de Bruijn)
//! - `Functor` -> constant application
//! - `Mode` -> type constant
//! - `Set` -> Sort 0 (Type)
//!
//! The translation context tracks Mizar variable bindings and maps them
//! to de Bruijn indices in the kernel expression language.

use super::importer::{MizConstantKind, MizImportedConstant, MizarImportConfig};
use super::types::{MizDefinition, MizFormula, MizItem, MizRegistration, MizTerm, MizType};
use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};
use clean_kernel::{BinderInfo, Expr, ExprKind, LevelVec, Literal, Name};
use hashbrown::HashMap;
use thiserror::Error;

/// Errors raised during Mizar-to-clean translation.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum MizTranslateError {
    #[error("unbound variable `{name}` at depth {depth}")]
    UnboundVariable { name: String, depth: usize },
    #[error("unknown predicate `{name}`")]
    UnknownPredicate { name: String },
    #[error("unknown functor `{name}`")]
    UnknownFunctor { name: String },
    #[error("unknown mode `{name}`")]
    UnknownMode { name: String },
    #[error("unsupported Mizar construct: {desc}")]
    Unsupported { desc: String },
}

pub(crate) type MizTranslateResult<T> = Result<T, MizTranslateError>;

// ════════════════════════════════════════════════════════════════════════════
// Translation context
// ════════════════════════════════════════════════════════════════════════════

/// Translation environment for Mizar terms -> clean kernel Expr.
///
/// Tracks:
/// - Local variable bindings (Mizar name -> de Bruijn depth)
/// - Global name mappings (Mizar identifiers -> clean constant names)
/// - Predicate, functor, and mode declarations
pub struct MizTranslationContext {
    /// Stack of bound variable names (innermost = last).
    locals: Vec<String>,
    /// Mizar predicate names -> clean constant names.
    predicates: HashMap<String, Name>,
    /// Mizar functor names -> clean constant names.
    functors: HashMap<String, Name>,
    /// Mizar mode names -> clean constant names.
    modes: HashMap<String, Name>,
}

impl Default for MizTranslationContext {
    fn default() -> Self {
        Self::new()
    }
}

impl MizTranslationContext {
    /// Create an empty translation context.
    #[must_use]
    pub fn new() -> Self {
        Self {
            locals: Vec::new(),
            predicates: HashMap::new(),
            functors: HashMap::new(),
            modes: HashMap::new(),
        }
    }

    /// Register a predicate mapping.
    pub fn add_predicate(&mut self, mizar_name: &str, lean_name: Name) {
        self.predicates.insert(mizar_name.to_owned(), lean_name);
    }

    /// Register a functor mapping.
    pub fn add_functor(&mut self, mizar_name: &str, lean_name: Name) {
        self.functors.insert(mizar_name.to_owned(), lean_name);
    }

    /// Register a mode mapping.
    pub fn add_mode(&mut self, mizar_name: &str, lean_name: Name) {
        self.modes.insert(mizar_name.to_owned(), lean_name);
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
        // Search from innermost (last) to outermost (first).
        for (i, local) in self.locals.iter().rev().enumerate() {
            if local == name {
                return Some(i as u32);
            }
        }
        None
    }

    /// Resolve a predicate name to a clean Name, generating one if not registered.
    fn resolve_predicate(&self, name: &str) -> Name {
        self.predicates
            .get(name)
            .cloned()
            .unwrap_or_else(|| Name::from_string(&format!("Mizar.Pred.{name}")))
    }

    /// Resolve a functor name to a clean Name.
    fn resolve_functor(&self, name: &str) -> Name {
        self.functors
            .get(name)
            .cloned()
            .unwrap_or_else(|| Name::from_string(&format!("Mizar.Func.{name}")))
    }

    /// Resolve a mode name to a clean Name.
    fn resolve_mode(&self, name: &str) -> Name {
        self.modes
            .get(name)
            .cloned()
            .unwrap_or_else(|| Name::from_string(&format!("Mizar.Mode.{name}")))
    }
}

/// Helper: create a constant with no universe levels.
fn mk_const(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), LevelVec::new())
}

/// Helper: create a named constant with no universe levels.
fn mk_named_const(name: Name) -> Expr {
    Expr::const_(name, LevelVec::new())
}

// ════════════════════════════════════════════════════════════════════════════
// Formula translation
// ════════════════════════════════════════════════════════════════════════════

/// Translate a Mizar formula to a clean kernel expression in Prop.
///
/// The result is an `Expr` of type `Prop` (Sort 0).
pub fn translate_formula(
    ctx: &mut MizTranslationContext,
    f: &MizFormula,
) -> MizTranslateResult<Expr> {
    match f {
        MizFormula::Pred { name, args } => {
            let pred_const = mk_named_const(ctx.resolve_predicate(name));
            let translated_args = args
                .iter()
                .map(|a| translate_term(ctx, a))
                .collect::<MizTranslateResult<Vec<_>>>()?;
            Ok(Expr::apps(pred_const, translated_args))
        }

        MizFormula::Not(inner) => {
            let inner_expr = translate_formula(ctx, inner)?;
            // Not P = P -> False
            Ok(Expr::arrow(inner_expr, mk_const("False")))
        }

        MizFormula::And(conjuncts) => {
            if conjuncts.is_empty() {
                // Empty conjunction = True
                return Ok(mk_const("True"));
            }
            let mut result = translate_formula(ctx, &conjuncts[0])?;
            for conjunct in &conjuncts[1..] {
                let rhs = translate_formula(ctx, conjunct)?;
                result = Expr::apps(mk_const("And"), [result, rhs]);
            }
            Ok(result)
        }

        MizFormula::Or(disjuncts) => {
            if disjuncts.is_empty() {
                // Empty disjunction = False
                return Ok(mk_const("False"));
            }
            let mut result = translate_formula(ctx, &disjuncts[0])?;
            for disjunct in &disjuncts[1..] {
                let rhs = translate_formula(ctx, disjunct)?;
                result = Expr::apps(mk_const("Or"), [result, rhs]);
            }
            Ok(result)
        }

        MizFormula::Implies(lhs, rhs) => {
            let lhs_expr = translate_formula(ctx, lhs)?;
            let rhs_expr = translate_formula(ctx, rhs)?;
            // P implies Q = P -> Q (non-dependent Pi)
            Ok(Expr::arrow(lhs_expr, rhs_expr))
        }

        MizFormula::Iff(lhs, rhs) => {
            let lhs_expr = translate_formula(ctx, lhs)?;
            let rhs_expr = translate_formula(ctx, rhs)?;
            Ok(Expr::apps(mk_const("Iff"), [lhs_expr, rhs_expr]))
        }

        MizFormula::ForAll { var, ty, body } => {
            let ty_expr = translate_type(ctx, ty)?;
            ctx.push_local(var);
            let body_expr = translate_formula(ctx, body)?;
            ctx.pop_local();
            // for x being T holds P(x) = (x : T) -> P(x)
            Ok(Expr::pi(BinderInfo::Default, ty_expr, body_expr))
        }

        MizFormula::Exists { var, ty, body } => {
            let ty_expr = translate_type(ctx, ty)?;
            ctx.push_local(var);
            let body_expr = translate_formula(ctx, body)?;
            ctx.pop_local();
            // ex x being T st P(x) = Exists (fun (x : T) => P(x))
            let lam = Expr::lam(BinderInfo::Default, ty_expr, body_expr);
            Ok(Expr::app(mk_const("Exists"), lam))
        }

        MizFormula::Is { term, ty } => {
            // Enhanced Is translation: handles clustered types with adjective checking.
            // For `t is adj1 adj2 ... M`, we decompose into:
            //   And(Mizar.Is t M, adj1 t, adj2 t, ...)
            // For plain `t is M`, we emit `Mizar.Is t M` as before.
            let term_expr = translate_term(ctx, term)?;
            match ty {
                MizType::Clustered { adjectives, base } if !adjectives.is_empty() => {
                    let base_expr = translate_type(ctx, base)?;
                    // Start with `Mizar.Is term base`
                    let mut conjuncts = vec![Expr::apps(
                        mk_const("Mizar.Is"),
                        [term_expr.clone(), base_expr],
                    )];
                    // Add each adjective as a predicate applied to the term
                    for adj in adjectives {
                        let mut adj_expr = mk_const(&format!("Mizar.Adj.{}", adj.name));
                        // Apply adjective arguments
                        let args = adj
                            .args
                            .iter()
                            .map(|a| translate_term(ctx, a))
                            .collect::<MizTranslateResult<Vec<_>>>()?;
                        adj_expr = Expr::apps(adj_expr, args);
                        // Apply to the subject term
                        adj_expr = Expr::app(adj_expr, term_expr.clone());
                        if adj.negated {
                            adj_expr = Expr::arrow(adj_expr, mk_const("False"));
                        }
                        conjuncts.push(adj_expr);
                    }
                    // Conjoin all: Mizar.Is t M /\ adj1(t) /\ adj2(t) /\ ...
                    let mut result = conjuncts.remove(0);
                    for conjunct in conjuncts {
                        result = Expr::apps(mk_const("And"), [result, conjunct]);
                    }
                    Ok(result)
                }
                _ => {
                    // Plain type judgment: Mizar.Is t T
                    let ty_expr = translate_type(ctx, ty)?;
                    Ok(Expr::apps(mk_const("Mizar.Is"), [term_expr, ty_expr]))
                }
            }
        }

        MizFormula::Contradiction => Ok(mk_const("False")),

        MizFormula::Thesis => {
            // Thesis is a proof-level construct; translate as a placeholder.
            Ok(mk_const("Mizar.Thesis"))
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Term translation
// ════════════════════════════════════════════════════════════════════════════

/// Translate a Mizar term to a clean kernel expression.
pub fn translate_term(ctx: &mut MizTranslationContext, t: &MizTerm) -> MizTranslateResult<Expr> {
    match t {
        MizTerm::Var(name) => {
            if let Some(idx) = ctx.lookup_var(name) {
                Ok(Expr::bvar(idx))
            } else {
                // Treat as a free constant reference (Mizar global variable).
                Ok(mk_const(name))
            }
        }

        MizTerm::Numeral(n) => {
            // Translate numeral as a clean literal.
            let nat_val: u64 = (*n).try_into().unwrap_or(0);
            Ok(Expr::from_kind(ExprKind::Lit(Literal::nat(nat_val))))
        }

        MizTerm::Functor { name, args } => {
            let func_const = mk_named_const(ctx.resolve_functor(name));
            let translated_args = args
                .iter()
                .map(|a| translate_term(ctx, a))
                .collect::<MizTranslateResult<Vec<_>>>()?;
            Ok(Expr::apps(func_const, translated_args))
        }

        MizTerm::Aggregate {
            struct_name,
            fields,
        } => {
            let ctor_const = mk_const(&format!("Mizar.Struct.{struct_name}.mk"));
            let translated_fields = fields
                .iter()
                .map(|f| translate_term(ctx, f))
                .collect::<MizTranslateResult<Vec<_>>>()?;
            Ok(Expr::apps(ctor_const, translated_fields))
        }

        MizTerm::Selector { field, arg } => {
            let proj_const = mk_const(&format!("Mizar.Selector.{field}"));
            let arg_expr = translate_term(ctx, arg)?;
            Ok(Expr::app(proj_const, arg_expr))
        }

        MizTerm::The { ty } => {
            // Definite description: the T -> Mizar.the T
            let ty_expr = translate_type(ctx, ty)?;
            Ok(Expr::app(mk_const("Mizar.the"), ty_expr))
        }

        MizTerm::Fraenkel {
            term,
            vars,
            formula,
        } => {
            // Enhanced Fraenkel set-builder: { t where x1 is T1, ... : phi }
            //
            // Translation strategy:
            // - Single variable:
            //   Mizar.fraenkel (fun x1 : T1 => fraenkelPair(t, phi))
            // - Multiple variables (set comprehension with dependent binding):
            //   Mizar.fraenkelN N (fun x1 : T1 => fun x2 : T2 => ... => fraenkelPair(t, phi))
            //   where N is the number of binding variables.
            //
            // This preserves the full binding structure so downstream
            // consumers can reconstruct the comprehension domain.

            // Build the body with all variables in scope.
            let mut body = {
                for (name, _) in vars {
                    ctx.push_local(name);
                }
                let term_expr = translate_term(ctx, term)?;
                let formula_expr = translate_formula(ctx, formula)?;
                // Pair the term and formula.
                let paired = Expr::apps(mk_const("Mizar.fraenkelPair"), [term_expr, formula_expr]);
                for _ in vars {
                    ctx.pop_local();
                }
                paired
            };

            // Wrap in lambdas from innermost to outermost.
            for (_name, ty) in vars.iter().rev() {
                let ty_expr = translate_type(ctx, ty)?;
                body = Expr::lam(BinderInfo::Default, ty_expr, body);
            }

            // Choose the appropriate Fraenkel constructor based on arity.
            let fraenkel_expr = if vars.len() <= 1 {
                let fraenkel_const = mk_const("Mizar.fraenkel");
                Expr::app(fraenkel_const, body)
            } else {
                // Multi-variable: encode arity as a numeral argument.
                let arity = Expr::from_kind(ExprKind::Lit(Literal::nat(vars.len() as u64)));
                let fraenkel_n = mk_const("Mizar.fraenkelN");
                Expr::apps(fraenkel_n, [arity, body])
            };

            Ok(fraenkel_expr)
        }

        MizTerm::It => {
            // `it` in definitions: translate as a special constant.
            Ok(mk_const("Mizar.it"))
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Type translation
// ════════════════════════════════════════════════════════════════════════════

/// Translate a Mizar type to a clean kernel expression.
///
/// Mizar modes become type constants, structures become structure types,
/// and `set` becomes `Sort 0` (Type).
pub fn translate_type(ctx: &mut MizTranslationContext, ty: &MizType) -> MizTranslateResult<Expr> {
    match ty {
        MizType::Mode { name, args } => {
            let mode_const = mk_named_const(ctx.resolve_mode(name));
            let translated_args = args
                .iter()
                .map(|a| translate_term(ctx, a))
                .collect::<MizTranslateResult<Vec<_>>>()?;
            Ok(Expr::apps(mode_const, translated_args))
        }

        MizType::Struct { name, args } => {
            let struct_const = mk_const(&format!("Mizar.Struct.{name}"));
            let translated_args = args
                .iter()
                .map(|a| translate_term(ctx, a))
                .collect::<MizTranslateResult<Vec<_>>>()?;
            Ok(Expr::apps(struct_const, translated_args))
        }

        MizType::Set => {
            // Mizar `set` is the universal type; map to Type (Sort 1).
            Ok(Expr::type_())
        }

        MizType::Clustered { adjectives, base } => {
            // Clustered type: translate the base type and add adjective constraints.
            // Translate as `Mizar.Subtype base (fun x => adj1 x /\ adj2 x /\ ...)`
            let base_expr = translate_type(ctx, base)?;

            if adjectives.is_empty() {
                return Ok(base_expr);
            }

            // Build the adjective predicate (applied to BVar 0 inside a lambda).
            let adj_exprs: Vec<Expr> = adjectives
                .iter()
                .map(|adj| {
                    let mut result = mk_const(&format!("Mizar.Adj.{}", adj.name));

                    // Apply adjective arguments.
                    let args = adj
                        .args
                        .iter()
                        .map(|a| translate_term(ctx, a))
                        .collect::<MizTranslateResult<Vec<_>>>()?;
                    result = Expr::apps(result, args);

                    // Apply to bound variable (BVar 0 inside the lambda).
                    result = Expr::app(result, Expr::bvar(0));

                    if adj.negated {
                        // Negate: Not adj = adj -> False
                        result = Expr::arrow(result, mk_const("False"));
                    }

                    Ok(result)
                })
                .collect::<MizTranslateResult<Vec<_>>>()?;

            // Conjoin all adjective predicates.
            let mut pred = adj_exprs[0].clone();
            for adj in &adj_exprs[1..] {
                pred = Expr::apps(mk_const("And"), [pred, adj.clone()]);
            }

            // Wrap in lambda: fun x : base => pred
            let pred_lam = Expr::lam(BinderInfo::Default, base_expr.clone(), pred);

            Ok(Expr::apps(mk_const("Mizar.Subtype"), [base_expr, pred_lam]))
        }
    }
}

/// Convenience: translate a formula from a fresh context.
pub fn translate_formula_fresh(f: &MizFormula) -> MizTranslateResult<Expr> {
    let mut ctx = MizTranslationContext::new();
    translate_formula(&mut ctx, f)
}

/// Convenience: translate a term from a fresh context.
pub fn translate_term_fresh(t: &MizTerm) -> MizTranslateResult<Expr> {
    let mut ctx = MizTranslationContext::new();
    translate_term(&mut ctx, t)
}

/// Convenience: translate a type from a fresh context.
pub fn translate_type_fresh(ty: &MizType) -> MizTranslateResult<Expr> {
    let mut ctx = MizTranslationContext::new();
    translate_type(&mut ctx, ty)
}

// ════════════════════════════════════════════════════════════════════════════
// Article item translation
// ════════════════════════════════════════════════════════════════════════════

/// Translate a single Mizar article item into an imported constant.
///
/// Returns `Ok(None)` for items that are not translated (e.g., notations),
/// `Ok(Some(constant))` for translated items, and `Err` for translation failures.
pub fn translate_article_item(
    ctx: &mut MizTranslationContext,
    item: &MizItem,
    article_name: &str,
    config: &MizarImportConfig,
) -> MizTranslateResult<Option<MizImportedConstant>> {
    match item {
        MizItem::Theorem(thm) => {
            let type_expr = translate_formula(ctx, &thm.proposition)?;
            let has_proof = thm.proof.is_some();
            let (axiom_profile, trust_level) = if has_proof && config.translate_proofs {
                // Proved theorem with proof translation: MIZAR_SOFT_TYPE only
                // (still axiomatically depends on Mizar's type system embedding).
                (AxiomProfile::MIZAR_SOFT_TYPE, TrustLevel::AxiomDependent)
            } else if has_proof {
                // Proved but proof not translated: trust the Mizar checker.
                (
                    AxiomProfile::MIZAR_SOFT_TYPE,
                    TrustLevel::CertificateReplayed,
                )
            } else if config.axiomatize_unproved {
                // No proof, axiomatize.
                (
                    AxiomProfile::MIZAR_SOFT_TYPE,
                    TrustLevel::PartiallyAxiomatized,
                )
            } else {
                return Ok(None);
            };

            let name = format!("Mizar.{article_name}.T{}", thm.label);
            Ok(Some(MizImportedConstant {
                name: name.clone(),
                type_expr: format!("{:?}", type_expr),
                kernel_type_expr: Some(type_expr),
                kind: MizConstantKind::Theorem,
                axiom_profile,
                trust_level,
                provenance: Provenance {
                    source: SourceSystem::Mizar,
                    original_name: name,
                    source_file: Some(format!("{article_name}.miz")),
                    axiom_profile,
                },
            }))
        }

        MizItem::Definition(def) => {
            let (def_name, type_expr) = translate_definition_type(ctx, def)?;
            let name = format!("Mizar.{article_name}.{def_name}");
            let axiom_profile = AxiomProfile::MIZAR_SOFT_TYPE;
            Ok(Some(MizImportedConstant {
                name: name.clone(),
                type_expr: format!("{:?}", type_expr),
                kernel_type_expr: Some(type_expr),
                kind: MizConstantKind::Definition,
                axiom_profile,
                trust_level: TrustLevel::AxiomDependent,
                provenance: Provenance {
                    source: SourceSystem::Mizar,
                    original_name: name,
                    source_file: Some(format!("{article_name}.miz")),
                    axiom_profile,
                },
            }))
        }

        MizItem::Scheme(scheme) => {
            // Translate the conclusion as the type expression.
            let type_expr = translate_formula(ctx, &scheme.conclusion)?;
            let name = format!("Mizar.{article_name}.Sch.{}", scheme.name);
            let axiom_profile = AxiomProfile::MIZAR_SOFT_TYPE;
            Ok(Some(MizImportedConstant {
                name: name.clone(),
                type_expr: format!("{:?}", type_expr),
                kernel_type_expr: Some(type_expr),
                kind: MizConstantKind::Scheme,
                axiom_profile,
                trust_level: TrustLevel::AxiomDependent,
                provenance: Provenance {
                    source: SourceSystem::Mizar,
                    original_name: name,
                    source_file: Some(format!("{article_name}.miz")),
                    axiom_profile,
                },
            }))
        }

        MizItem::Registration(reg) => {
            let type_expr = translate_registration_type(ctx, reg)?;
            let reg_name = registration_name(reg);
            let name = format!("Mizar.{article_name}.Reg.{reg_name}");
            let axiom_profile = AxiomProfile::MIZAR_SOFT_TYPE;
            Ok(Some(MizImportedConstant {
                name: name.clone(),
                type_expr: format!("{:?}", type_expr),
                kernel_type_expr: Some(type_expr),
                kind: MizConstantKind::Registration,
                axiom_profile,
                trust_level: TrustLevel::AxiomDependent,
                provenance: Provenance {
                    source: SourceSystem::Mizar,
                    original_name: name,
                    source_file: Some(format!("{article_name}.miz")),
                    axiom_profile,
                },
            }))
        }

        MizItem::Notation(_) => {
            // Notations (synonyms, antonyms) do not produce constants.
            Ok(None)
        }
    }
}

/// Translate the type of a Mizar definition into a clean expression.
///
/// Returns `(definition_name, type_expr)`.
fn translate_definition_type(
    ctx: &mut MizTranslationContext,
    def: &MizDefinition,
) -> MizTranslateResult<(String, Expr)> {
    match def {
        MizDefinition::ModeDef {
            name,
            params,
            expansion,
        } => {
            let base = if let Some(exp) = expansion {
                translate_type(ctx, exp)?
            } else {
                Expr::type_()
            };
            // Build Pi over parameters.
            let result = wrap_params_as_pi(ctx, params, base)?;
            Ok((format!("Mode.{name}"), result))
        }

        MizDefinition::FunctorDef {
            name,
            params,
            result_ty,
            ..
        } => {
            let result_expr = translate_type(ctx, result_ty)?;
            let result = wrap_params_as_pi(ctx, params, result_expr)?;
            Ok((format!("Func.{name}"), result))
        }

        MizDefinition::PredicateDef { name, params, .. } => {
            let prop = mk_const("Prop");
            let result = wrap_params_as_pi(ctx, params, prop)?;
            Ok((format!("Pred.{name}"), result))
        }

        MizDefinition::AttributeDef { name, params, .. } => {
            // Attributes take a subject + params and return Prop.
            let prop = mk_const("Prop");
            let result = wrap_params_as_pi(ctx, params, prop)?;
            Ok((format!("Attr.{name}"), result))
        }

        MizDefinition::StructDef { name, fields, .. } => {
            // Structure type: fields produce a product type.
            let mut body = Expr::type_();
            for (_fname, fty) in fields.iter().rev() {
                let field_expr = translate_type(ctx, fty)?;
                body = Expr::pi(BinderInfo::Default, field_expr, body);
            }
            Ok((format!("Struct.{name}"), body))
        }
    }
}

/// Wrap a result expression in Pi types for each parameter.
fn wrap_params_as_pi(
    ctx: &mut MizTranslationContext,
    params: &[(String, MizType)],
    mut body: Expr,
) -> MizTranslateResult<Expr> {
    // Process in reverse to build correctly nested Pi.
    for (_name, ty) in params.iter().rev() {
        let param_ty = translate_type(ctx, ty)?;
        body = Expr::pi(BinderInfo::Default, param_ty, body);
    }
    Ok(body)
}

/// Translate the type of a registration into a clean expression.
fn translate_registration_type(
    ctx: &mut MizTranslationContext,
    reg: &MizRegistration,
) -> MizTranslateResult<Expr> {
    match reg {
        MizRegistration::Existential { ty, .. } => translate_type(ctx, ty),
        MizRegistration::Conditional { ty, .. } => translate_type(ctx, ty),
        MizRegistration::Functorial { term, .. } => translate_term(ctx, term),
    }
}

/// Generate a name for a registration.
fn registration_name(reg: &MizRegistration) -> String {
    match reg {
        MizRegistration::Existential { .. } => "exist".to_owned(),
        MizRegistration::Conditional { .. } => "cond".to_owned(),
        MizRegistration::Functorial { .. } => "func".to_owned(),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Additional translation tests
// ════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::super::types::MizAdjective;
    use super::*;

    #[test]
    fn test_translate_is_with_adjectives() {
        // t is non-empty set => And(Mizar.Is t set, Not(Mizar.Adj.non-empty t))
        // where Not is encoded as arrow to False
        let formula = MizFormula::Is {
            term: MizTerm::Var("X".to_owned()),
            ty: MizType::Clustered {
                adjectives: vec![MizAdjective {
                    name: "empty".to_owned(),
                    negated: true,
                    args: vec![],
                }],
                base: Box::new(MizType::Set),
            },
        };
        let expr = translate_formula_fresh(&formula).expect("should translate Is with adj");
        // Should be App(App(And, Mizar.Is ...), adj_negated ...)
        match expr.kind() {
            ExprKind::App(_, _) => { /* expected: And application */ }
            other => panic!("expected And application for Is+adj, got {other:?}"),
        }
    }

    #[test]
    fn test_translate_is_with_multiple_adjectives() {
        let formula = MizFormula::Is {
            term: MizTerm::Var("S".to_owned()),
            ty: MizType::Clustered {
                adjectives: vec![
                    MizAdjective {
                        name: "non-empty".to_owned(),
                        negated: false,
                        args: vec![],
                    },
                    MizAdjective {
                        name: "finite".to_owned(),
                        negated: false,
                        args: vec![],
                    },
                ],
                base: Box::new(MizType::Mode {
                    name: "set".to_owned(),
                    args: vec![],
                }),
            },
        };
        let expr = translate_formula_fresh(&formula).expect("should translate multiple adjs");
        // Outermost should be And(And(Is ..., adj1 ...), adj2 ...)
        match expr.kind() {
            ExprKind::App(_, _) => { /* nested And */ }
            other => panic!("expected App for multiple adj Is, got {other:?}"),
        }
    }

    #[test]
    fn test_translate_is_plain() {
        let formula = MizFormula::Is {
            term: MizTerm::Var("x".to_owned()),
            ty: MizType::Mode {
                name: "Nat".to_owned(),
                args: vec![],
            },
        };
        let expr = translate_formula_fresh(&formula).expect("should translate plain Is");
        // Should be App(App(Mizar.Is, x), Mizar.Mode.Nat)
        match expr.kind() {
            ExprKind::App(_, _) => { /* expected */ }
            other => panic!("expected App for plain Is, got {other:?}"),
        }
    }

    #[test]
    fn test_translate_fraenkel_single_var() {
        let term = MizTerm::Fraenkel {
            term: Box::new(MizTerm::Var("x".to_owned())),
            vars: vec![("x".to_owned(), MizType::Set)],
            formula: Box::new(MizFormula::Pred {
                name: "P".to_owned(),
                args: vec![MizTerm::Var("x".to_owned())],
            }),
        };
        let expr = translate_term_fresh(&term).expect("should translate single-var Fraenkel");
        // Should be App(Mizar.fraenkel, lam ...)
        match expr.kind() {
            ExprKind::App(func, _) => {
                assert!(matches!(func.kind(), ExprKind::Const(name, _)
                        if *name == Name::from_string("Mizar.fraenkel")));
            }
            other => panic!("expected App(Mizar.fraenkel, ...), got {other:?}"),
        }
    }

    #[test]
    fn test_translate_fraenkel_multi_var() {
        let term = MizTerm::Fraenkel {
            term: Box::new(MizTerm::Functor {
                name: "pair".to_owned(),
                args: vec![MizTerm::Var("x".to_owned()), MizTerm::Var("y".to_owned())],
            }),
            vars: vec![
                ("x".to_owned(), MizType::Set),
                ("y".to_owned(), MizType::Set),
            ],
            formula: Box::new(MizFormula::Pred {
                name: "R".to_owned(),
                args: vec![MizTerm::Var("x".to_owned()), MizTerm::Var("y".to_owned())],
            }),
        };
        let expr = translate_term_fresh(&term).expect("should translate multi-var Fraenkel");
        // Should be App(App(Mizar.fraenkelN, Lit(2)), lam ...)
        match expr.kind() {
            ExprKind::App(func_app, _body) => match func_app.kind() {
                ExprKind::App(fraenkel_n, arity) => {
                    assert!(matches!(fraenkel_n.kind(), ExprKind::Const(name, _)
                                if *name == Name::from_string("Mizar.fraenkelN")));
                    assert!(matches!(arity.kind(), ExprKind::Lit(_)));
                }
                other => panic!("expected App(Mizar.fraenkelN, arity), got {other:?}"),
            },
            other => panic!("expected App for multi-var Fraenkel, got {other:?}"),
        }
    }

    #[test]
    fn test_translate_article_item_theorem() {
        use super::super::types::MizTheorem;
        let mut ctx = MizTranslationContext::new();
        let config = MizarImportConfig::default();
        let item = MizItem::Theorem(MizTheorem {
            label: "42".to_owned(),
            proposition: MizFormula::Contradiction,
            proof: None,
        });
        let result = translate_article_item(&mut ctx, &item, "XBOOLE_0", &config)
            .expect("should translate theorem");
        let c = result.expect("should produce a constant");
        assert_eq!(c.kind, MizConstantKind::Theorem);
        assert_eq!(c.name, "Mizar.XBOOLE_0.T42");
        assert_eq!(c.trust_level, TrustLevel::PartiallyAxiomatized);
    }

    #[test]
    fn test_translate_article_item_notation_skipped() {
        use super::super::types::MizNotation;
        let mut ctx = MizTranslationContext::new();
        let config = MizarImportConfig::default();
        let item = MizItem::Notation(MizNotation::Synonym {
            new_name: "new".to_owned(),
            original: "old".to_owned(),
        });
        let result =
            translate_article_item(&mut ctx, &item, "TEST", &config).expect("should succeed");
        assert!(result.is_none(), "notation should not produce a constant");
    }

    #[test]
    fn test_translate_article_item_definition() {
        let mut ctx = MizTranslationContext::new();
        let config = MizarImportConfig::default();
        let item = MizItem::Definition(MizDefinition::PredicateDef {
            name: "eq".to_owned(),
            params: vec![
                ("x".to_owned(), MizType::Set),
                ("y".to_owned(), MizType::Set),
            ],
            meaning: None,
        });
        let result = translate_article_item(&mut ctx, &item, "HIDDEN", &config)
            .expect("should translate definition");
        let c = result.expect("should produce a constant");
        assert_eq!(c.kind, MizConstantKind::Definition);
        assert!(c.name.contains("Pred.eq"));
        assert_eq!(c.trust_level, TrustLevel::AxiomDependent);
    }

    #[test]
    fn test_translate_article_item_scheme() {
        use super::super::types::MizScheme;
        let mut ctx = MizTranslationContext::new();
        let config = MizarImportConfig::default();
        let item = MizItem::Scheme(MizScheme {
            name: "Induction".to_owned(),
            premises: vec![],
            conclusion: MizFormula::Pred {
                name: "P".to_owned(),
                args: vec![],
            },
        });
        let result = translate_article_item(&mut ctx, &item, "NAT_1", &config)
            .expect("should translate scheme");
        let c = result.expect("should produce a constant");
        assert_eq!(c.kind, MizConstantKind::Scheme);
        assert!(c.name.contains("Sch.Induction"));
    }
}
