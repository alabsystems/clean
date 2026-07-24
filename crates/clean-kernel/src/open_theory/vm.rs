// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! OpenTheory stack-machine execution.

use super::article::{OtArticle, OtCommand};
use super::object::OtObject;
use super::term::{OtConstant, OtTerm, OtTheorem, OtVariable};
use super::ty::{OtType, OtTypeOperator};
use super::vm_support::{ensure_global_name, extract_substitution};
use super::{OpenTheoryError, OpenTheoryResult};
use hashbrown::HashMap;

/// Theorems proved by dependency articles, keyed by `(hypotheses, conclusion)`.
///
/// When processing a sequence of OpenTheory articles that form a dependency DAG,
/// earlier articles export theorems that later articles reference via `axiom`.
/// Providing these as context allows the VM to resolve axioms against proved
/// theorems instead of creating unresolved assumptions.
pub type OtContext = HashMap<(Vec<OtTerm>, OtTerm), OtTheorem>;

pub(crate) struct OtVmState {
    pub(super) stack: Vec<OtObject>,
    pub(super) dictionary: HashMap<i64, OtObject>,
    pub(super) assumptions: Vec<OtTheorem>,
    pub(super) theorems: Vec<OtTheorem>,
    pub(super) context: OtContext,
    pub(super) version: u32,
    pub(super) next_symbol_id: u64,
    pub(super) executed_commands: usize,
}

impl Default for OtVmState {
    fn default() -> Self {
        Self {
            stack: Vec::new(),
            dictionary: HashMap::new(),
            assumptions: Vec::new(),
            theorems: Vec::new(),
            context: OtContext::default(),
            version: 5,
            next_symbol_id: 0,
            executed_commands: 0,
        }
    }
}

impl OtVmState {
    /// Create a VM state initialized with theorems from dependency articles.
    pub(crate) fn with_context(context: OtContext) -> Self {
        Self {
            context,
            ..Self::default()
        }
    }
}

impl OtVmState {
    pub(crate) fn into_article(self, commands: Vec<OtCommand>) -> OtArticle {
        OtArticle {
            version: self.version,
            commands,
            assumptions: self.assumptions,
            theorems: self.theorems,
        }
    }

    pub(crate) fn execute(&mut self, command: &OtCommand, line: usize) -> OpenTheoryResult<()> {
        match command {
            OtCommand::Number(value) => self.stack.push(OtObject::Num(*value)),
            OtCommand::Name(name) => self.stack.push(OtObject::Name(name.clone())),
            OtCommand::AbsTerm => {
                let body = self.pop_term("absTerm")?;
                let binder = self.pop_var("absTerm")?;
                self.stack.push(OtObject::Term(OtTerm::abs(binder, body)));
            }
            OtCommand::AbsThm => self.handle_abs_thm()?,
            OtCommand::AppTerm => {
                let arg = self.pop_term("appTerm")?;
                let func = self.pop_term("appTerm")?;
                self.stack.push(OtObject::Term(OtTerm::app(func, arg)?));
            }
            OtCommand::AppThm => self.handle_app_thm()?,
            OtCommand::Assume => {
                let proposition = self.pop_term("assume")?;
                super::vm_support::ensure_bool_term("assume", &proposition)?;
                self.stack.push(OtObject::Thm(OtTheorem::new(
                    vec![proposition.clone()],
                    proposition,
                )));
            }
            OtCommand::Axiom => self.handle_axiom()?,
            OtCommand::BetaConv => self.handle_beta_conv()?,
            OtCommand::Cons => {
                let mut tail = self.pop_list("cons")?;
                let head = self.pop_obj("cons")?;
                tail.insert(0, head);
                self.stack.push(OtObject::List(tail));
            }
            OtCommand::Const => {
                let name = self.pop_name("const")?;
                self.stack
                    .push(OtObject::Const(OtConstant::from_name(name)));
            }
            OtCommand::ConstTerm => {
                let ty = self.pop_type("constTerm")?;
                let constant = self.pop_const("constTerm")?;
                self.stack
                    .push(OtObject::Term(OtTerm::const_(constant, ty)));
            }
            OtCommand::DeductAntisym => self.handle_deduct_antisym()?,
            OtCommand::Def => {
                let key = self.pop_num("def")?;
                let value = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or(OpenTheoryError::StackUnderflow { command: "def" })?;
                self.dictionary.insert(key, value);
            }
            OtCommand::DefineConst => self.handle_define_const()?,
            OtCommand::DefineConstList => self.handle_define_const_list()?,
            OtCommand::DefineTypeOp => self.handle_define_type_op()?,
            OtCommand::EqMp => self.handle_eq_mp()?,
            OtCommand::HdTl => {
                let list = self.pop_list("hdTl")?;
                let Some((head, tail)) = list.split_first() else {
                    return Err(OpenTheoryError::MalformedObject {
                        command: "hdTl",
                        detail: "expected a non-empty list".to_string(),
                    });
                };
                self.stack.push(head.clone());
                self.stack.push(OtObject::List(tail.to_vec()));
            }
            OtCommand::Nil => self.stack.push(OtObject::List(Vec::new())),
            OtCommand::OpType => {
                let args = self.pop_type_list("opType")?;
                let op = self.pop_type_op("opType")?;
                self.stack.push(OtObject::Type(OtType::apply(op, args)));
            }
            OtCommand::Pop => {
                let _ = self.pop_obj("pop")?;
            }
            OtCommand::Pragma => {
                let _ = self.pop_obj("pragma")?;
            }
            OtCommand::ProveHyp => {
                let delta = self.pop_thm("proveHyp")?;
                let gamma = self.pop_thm("proveHyp")?;
                self.stack.push(OtObject::Thm(OtTheorem::new(
                    OtTheorem::union_hypotheses(
                        &gamma.hypotheses,
                        &OtTheorem::without_hypothesis(&delta.hypotheses, &gamma.conclusion),
                    ),
                    delta.conclusion,
                )));
            }
            OtCommand::Ref => {
                let key = self.pop_num("ref")?;
                let value = self
                    .dictionary
                    .get(&key)
                    .cloned()
                    .ok_or(OpenTheoryError::UnknownDictionaryKey { key })?;
                self.stack.push(value);
            }
            OtCommand::Refl => {
                let term = self.pop_term("refl")?;
                self.stack.push(OtObject::Thm(OtTheorem::new(
                    Vec::new(),
                    OtTerm::eq(term.clone(), term)?,
                )));
            }
            OtCommand::Remove => {
                let key = self.pop_num("remove")?;
                let value = self
                    .dictionary
                    .remove(&key)
                    .ok_or(OpenTheoryError::UnknownDictionaryKey { key })?;
                self.stack.push(value);
            }
            OtCommand::Subst => {
                let theorem = self.pop_thm("subst")?;
                let substitution = self.pop_list("subst")?;
                let (type_subs, term_subs) = extract_substitution(&substitution)?;
                self.stack.push(OtObject::Thm(
                    theorem
                        .substitute_types(&type_subs)
                        .substitute_terms(&term_subs),
                ));
            }
            OtCommand::Sym => {
                let theorem = self.pop_thm("sym")?;
                let hypotheses = theorem.hypotheses.clone();
                let (lhs, rhs) = theorem
                    .as_equality()
                    .ok_or(OpenTheoryError::EqualityConclusionExpected { command: "sym" })?;
                self.stack.push(OtObject::Thm(OtTheorem::new(
                    hypotheses,
                    OtTerm::eq(rhs.clone(), lhs.clone())?,
                )));
            }
            OtCommand::Thm => self.handle_thm()?,
            OtCommand::Trans => self.handle_trans()?,
            OtCommand::TypeOp => {
                let name = self.pop_name("typeOp")?;
                self.stack
                    .push(OtObject::TypeOp(OtTypeOperator::from_name(name)));
            }
            OtCommand::Var => {
                let ty = self.pop_type("var")?;
                let name = self.pop_name("var")?;
                ensure_global_name("var", &name)?;
                self.stack.push(OtObject::Var(OtVariable::new(name, ty)));
            }
            OtCommand::VarTerm => {
                let variable = self.pop_var("varTerm")?;
                self.stack.push(OtObject::Term(OtTerm::var(variable)));
            }
            OtCommand::VarType => {
                let name = self.pop_name("varType")?;
                ensure_global_name("varType", &name)?;
                self.stack.push(OtObject::Type(OtType::Var(name)));
            }
            OtCommand::Version => {
                if self.executed_commands > 1 {
                    return Err(OpenTheoryError::InvalidVersionPosition { line });
                }
                let version = self.pop_num("version")?;
                if version < 0 {
                    return Err(OpenTheoryError::MalformedObject {
                        command: "version",
                        detail: "version must be non-negative".to_string(),
                    });
                }
                self.version = version as u32;
            }
        }
        Ok(())
    }

    pub(crate) fn note_command_executed(&mut self) {
        // Saturating: the counter's only consumer is the `> 1` Version-position
        // check, so saturation is semantics-preserving while removing the
        // panicking add on this untrusted-input-driven path (Trust ledger
        // 2026-06-10, assertion: arithmetic overflow (Add) @ open_theory/vm.rs:245).
        self.executed_commands = self.executed_commands.saturating_add(1);
    }
}
