// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Translation scope management and symbol collection.

use super::super::{HolLightImportError, HolProof, HolProofObject, HolTerm, HolType, HolVar};
use crate::{Expr, Name};
use hashbrown::HashSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ScopeBinderKind {
    TypeVar,
    TermVar,
}

#[derive(Clone, Debug)]
pub(super) struct ScopeBinder {
    pub kind: ScopeBinderKind,
    pub name: String,
    pub hol_ty: Option<HolType>,
    pub lean_ty: Expr,
}

#[derive(Clone, Debug, Default)]
pub(super) struct Scope {
    binders: Vec<ScopeBinder>,
}

impl Scope {
    pub(super) fn with_type_vars(vars: &[String]) -> Self {
        let binders = vars
            .iter()
            .map(|name| ScopeBinder {
                kind: ScopeBinderKind::TypeVar,
                name: name.clone(),
                hol_ty: None,
                lean_ty: Expr::type_(),
            })
            .collect();
        Self { binders }
    }

    pub(super) fn extend_term(&self, binder: &HolVar, lean_ty: Expr) -> Self {
        let mut binders = self.binders.clone();
        binders.push(ScopeBinder {
            kind: ScopeBinderKind::TermVar,
            name: binder.name.clone(),
            hol_ty: Some(binder.ty.clone()),
            lean_ty,
        });
        Self { binders }
    }

    pub(super) fn len(&self) -> usize {
        self.binders.len()
    }

    pub(super) fn binders(&self) -> &[ScopeBinder] {
        &self.binders
    }

    pub(super) fn lookup_type(&self, name: &str) -> Option<usize> {
        self.binders
            .iter()
            .rposition(|binder| binder.kind == ScopeBinderKind::TypeVar && binder.name == name)
    }

    pub(super) fn lookup_term(&self, var: &HolVar) -> Option<usize> {
        self.binders.iter().rposition(|binder| {
            binder.kind == ScopeBinderKind::TermVar
                && binder.name == var.name
                && binder.hol_ty.as_ref() == Some(&var.ty)
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct ConstSymbol {
    pub name: String,
    pub ty: HolType,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct TypeOpSymbol {
    pub name: String,
    pub arity: usize,
}

#[derive(Clone, Debug, Default)]
pub(super) struct SymbolCollector {
    type_ops_seen: HashSet<TypeOpSymbol>,
    consts_seen: HashSet<ConstSymbol>,
    type_ops: Vec<TypeOpSymbol>,
    consts: Vec<ConstSymbol>,
}

impl SymbolCollector {
    pub(super) fn note_type_op(&mut self, name: &str, arity: usize) {
        let symbol = TypeOpSymbol {
            name: name.to_string(),
            arity,
        };
        if self.type_ops_seen.insert(symbol.clone()) {
            self.type_ops.push(symbol);
        }
    }

    pub(super) fn note_const(&mut self, name: &str, ty: &HolType) {
        let symbol = ConstSymbol {
            name: name.to_string(),
            ty: ty.clone(),
        };
        if self.consts_seen.insert(symbol.clone()) {
            self.consts.push(symbol);
        }
    }

    pub(super) fn type_ops(&self) -> &[TypeOpSymbol] {
        &self.type_ops
    }

    pub(super) fn consts(&self) -> &[ConstSymbol] {
        &self.consts
    }
}

pub(super) fn root_scope(object: &HolProofObject) -> Result<Scope, HolLightImportError> {
    let mut type_vars = Vec::new();
    let mut term_vars = Vec::new();
    collect_free_from_proof(
        &object.proof,
        &mut Vec::new(),
        &mut type_vars,
        &mut term_vars,
    )?;
    let mut scope = Scope::with_type_vars(&type_vars);
    for term_var in term_vars {
        let lean_ty = translate_hol_type_for_scope(&scope, &term_var.ty)?;
        scope = scope.extend_term(&term_var, lean_ty);
    }
    Ok(scope)
}

fn collect_free_from_proof(
    proof: &HolProof,
    bound_terms: &mut Vec<HolVar>,
    type_vars: &mut Vec<String>,
    term_vars: &mut Vec<HolVar>,
) -> Result<(), HolLightImportError> {
    match proof {
        HolProof::Refl { term } | HolProof::Assume { proposition: term } => {
            collect_free_from_term(term, bound_terms, type_vars, term_vars)
        }
        HolProof::Trans { left, right }
        | HolProof::EqMp {
            equality: left,
            proof: right,
        }
        | HolProof::DeductAntisym { left, right } => {
            collect_free_from_proof(left, bound_terms, type_vars, term_vars)?;
            collect_free_from_proof(right, bound_terms, type_vars, term_vars)
        }
        HolProof::MkComb { function, argument } => {
            collect_free_from_proof(function, bound_terms, type_vars, term_vars)?;
            collect_free_from_proof(argument, bound_terms, type_vars, term_vars)
        }
        HolProof::Abs { binder, proof } => {
            collect_free_from_type(&binder.ty, type_vars);
            bound_terms.push(binder.clone());
            let result = collect_free_from_proof(proof, bound_terms, type_vars, term_vars);
            bound_terms.pop();
            result
        }
        HolProof::Beta {
            binder,
            body,
            argument,
        } => {
            collect_free_from_type(&binder.ty, type_vars);
            bound_terms.push(binder.clone());
            collect_free_from_term(body, bound_terms, type_vars, term_vars)?;
            bound_terms.pop();
            collect_free_from_term(argument, bound_terms, type_vars, term_vars)
        }
        HolProof::Inst {
            proof,
            substitutions,
        } => {
            collect_free_from_proof(proof, bound_terms, type_vars, term_vars)?;
            for substitution in substitutions {
                collect_free_from_type(&substitution.variable.ty, type_vars);
                collect_free_from_term(
                    &substitution.replacement,
                    bound_terms,
                    type_vars,
                    term_vars,
                )?;
            }
            Ok(())
        }
        HolProof::InstType {
            proof,
            substitutions,
        } => {
            collect_free_from_proof(proof, bound_terms, type_vars, term_vars)?;
            for substitution in substitutions {
                collect_free_from_type(&substitution.replacement, type_vars);
            }
            Ok(())
        }
    }
}

fn collect_free_from_term(
    term: &HolTerm,
    bound_terms: &[HolVar],
    type_vars: &mut Vec<String>,
    term_vars: &mut Vec<HolVar>,
) -> Result<(), HolLightImportError> {
    match term {
        HolTerm::Var { name, ty } => {
            let var = HolVar::new(name.clone(), ty.clone());
            collect_free_from_type(ty, type_vars);
            if !bound_terms.contains(&var) {
                push_free_term_var(term_vars, &var)?;
            }
            Ok(())
        }
        HolTerm::Const { ty, .. } => {
            collect_free_from_type(ty, type_vars);
            Ok(())
        }
        HolTerm::App { func, arg } => {
            collect_free_from_term(func, bound_terms, type_vars, term_vars)?;
            collect_free_from_term(arg, bound_terms, type_vars, term_vars)
        }
        HolTerm::Abs { binder, body } => {
            collect_free_from_type(&binder.ty, type_vars);
            let mut extended = bound_terms.to_vec();
            extended.push(binder.clone());
            collect_free_from_term(body, &extended, type_vars, term_vars)
        }
    }
}

fn push_free_term_var(vars: &mut Vec<HolVar>, var: &HolVar) -> Result<(), HolLightImportError> {
    match vars.iter().find(|existing| existing.name == var.name) {
        Some(existing) if existing != var => Err(HolLightImportError::InconsistentFreeVariable {
            name: var.name.clone(),
        }),
        Some(_) => Ok(()),
        None => {
            vars.push(var.clone());
            Ok(())
        }
    }
}

fn collect_free_from_type(ty: &HolType, vars: &mut Vec<String>) {
    match ty {
        HolType::Var { name } => push_unique(vars, name),
        HolType::Bool => {}
        HolType::Fun { domain, codomain } => {
            collect_free_from_type(domain, vars);
            collect_free_from_type(codomain, vars);
        }
        HolType::TyOp { args, .. } => {
            for arg in args {
                collect_free_from_type(arg, vars);
            }
        }
    }
}

fn push_unique<T: PartialEq + Clone>(values: &mut Vec<T>, value: &T) {
    if !values.contains(value) {
        values.push(value.clone());
    }
}

pub(super) fn scope_args_in_context(
    scope: &Scope,
    assumptions_len: usize,
    trailing_locals: usize,
) -> Vec<Expr> {
    let total = scope.len() + assumptions_len + trailing_locals;
    (0..scope.len())
        .map(|position| Expr::bvar((total - 1 - position) as u32))
        .collect()
}

pub(super) fn assumption_args_in_context(
    scope: &Scope,
    assumptions_len: usize,
    trailing_locals: usize,
) -> Vec<Expr> {
    let total = scope.len() + assumptions_len + trailing_locals;
    (0..assumptions_len)
        .map(|position| Expr::bvar((total - 1 - (scope.len() + position)) as u32))
        .collect()
}

pub(super) fn theorem_name(source_name: &str) -> Name {
    Name::from_string(&format!("HOLLight.Theorem.{}", encode_name(source_name)))
}

pub(super) fn type_op_name(symbol: &TypeOpSymbol) -> Name {
    Name::from_string(&format!(
        "HOLLight.TypeOp.{}.{}",
        encode_name(&symbol.name),
        symbol.arity
    ))
}

pub(super) fn const_name(symbol: &ConstSymbol) -> Name {
    let digest = stable_hash(&format!("{:?}", symbol.ty));
    Name::from_string(&format!(
        "HOLLight.Const.{}.{}",
        encode_name(&symbol.name),
        digest
    ))
}

fn encode_name(name: &str) -> String {
    let mut out = String::with_capacity(name.len() * 2);
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch);
        } else {
            out.push('_');
            out.push_str(&format!("{:x}", ch as u32));
        }
    }
    if out.is_empty() {
        "anon".to_string()
    } else {
        out
    }
}

fn stable_hash(input: &str) -> String {
    let mut hash = 0xcbf29ce484222325_u64;
    for byte in input.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    format!("{hash:016x}")
}

fn translate_hol_type_for_scope(scope: &Scope, ty: &HolType) -> Result<Expr, HolLightImportError> {
    match ty {
        HolType::Var { name } => {
            let position = scope
                .lookup_type(name)
                .ok_or_else(|| HolLightImportError::UnboundTypeVariable { name: name.clone() })?;
            Ok(Expr::bvar((scope.len() - 1 - position) as u32))
        }
        HolType::Bool => Ok(Expr::prop()),
        HolType::Fun { domain, codomain } => {
            // `A → B` = `Pi(_, A, B)`: the codomain lives under the arrow's
            // binder, so its de Bruijn indices must be lifted by one (see the
            // matching fix in `TermTranslator::translate_type`).
            let dom = translate_hol_type_for_scope(scope, domain)?;
            let cod = translate_hol_type_for_scope(scope, codomain)?.lift(1);
            Ok(Expr::arrow(dom, cod))
        }
        HolType::TyOp { name, args } => {
            let symbol = TypeOpSymbol {
                name: name.clone(),
                arity: args.len(),
            };
            let translated_args = args
                .iter()
                .map(|arg| translate_hol_type_for_scope(scope, arg))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Expr::apps(
                Expr::const_(type_op_name(&symbol), Vec::new()),
                translated_args,
            ))
        }
    }
}
