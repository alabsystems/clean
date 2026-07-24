// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Large OpenTheory VM command handlers split out to keep files small.

use super::name::OtName;
use super::object::OtObject;
use super::term::{OtConstant, OtTerm, OtTheorem, OtVariable};
use super::ty::{OtType, OtTypeOperator};
use super::vm::OtVmState;
use super::vm_support::{ensure_bool_term, extract_name_var_pair, extract_variable_definition};
use super::{OpenTheoryError, OpenTheoryResult};

impl OtVmState {
    pub(super) fn handle_abs_thm(&mut self) -> OpenTheoryResult<()> {
        let theorem = self.pop_thm("absThm")?;
        let binder = self.pop_var("absThm")?;
        if theorem
            .hypotheses
            .iter()
            .any(|hypothesis| hypothesis.free_vars().contains(&binder))
        {
            return Err(OpenTheoryError::MalformedObject {
                command: "absThm",
                detail: "binder escapes an assumption".to_string(),
            });
        }
        let hypotheses = theorem.hypotheses.clone();
        let (lhs, rhs) = theorem
            .as_equality()
            .ok_or(OpenTheoryError::EqualityConclusionExpected { command: "absThm" })?;
        self.stack.push(OtObject::Thm(OtTheorem::new(
            hypotheses,
            OtTerm::eq(
                OtTerm::abs(binder.clone(), lhs.clone()),
                OtTerm::abs(binder, rhs.clone()),
            )?,
        )));
        Ok(())
    }

    pub(super) fn handle_app_thm(&mut self) -> OpenTheoryResult<()> {
        let arg_eq = self.pop_thm("appThm")?;
        let func_eq = self.pop_thm("appThm")?;
        let (x, y) = arg_eq
            .as_equality()
            .ok_or(OpenTheoryError::EqualityConclusionExpected { command: "appThm" })?;
        let (f, g) = func_eq
            .as_equality()
            .ok_or(OpenTheoryError::EqualityConclusionExpected { command: "appThm" })?;
        self.stack.push(OtObject::Thm(OtTheorem::new(
            OtTheorem::union_hypotheses(&func_eq.hypotheses, &arg_eq.hypotheses),
            OtTerm::eq(
                OtTerm::app(f.clone(), x.clone())?,
                OtTerm::app(g.clone(), y.clone())?,
            )?,
        )));
        Ok(())
    }

    pub(super) fn handle_axiom(&mut self) -> OpenTheoryResult<()> {
        let conclusion = self.pop_term("axiom")?;
        ensure_bool_term("axiom", &conclusion)?;
        let hypotheses = self.pop_term_list("axiom")?;
        for hypothesis in &hypotheses {
            ensure_bool_term("axiom", hypothesis)?;
        }

        // Check if a dependency article already proved this theorem.
        // The context key is (hypotheses, conclusion) — if we find a match,
        // use the proved theorem (which has no/fewer hypotheses) instead of
        // creating an unresolved assumption.
        let key = (hypotheses.clone(), conclusion.clone());
        if let Some(proved) = self.context.get(&key) {
            self.stack.push(OtObject::Thm(proved.clone()));
            return Ok(());
        }

        let theorem = OtTheorem::new(hypotheses, conclusion);
        self.push_assumption(theorem.clone());
        self.stack.push(OtObject::Thm(theorem));
        Ok(())
    }

    pub(super) fn handle_beta_conv(&mut self) -> OpenTheoryResult<()> {
        let application = self.pop_term("betaConv")?;
        let OtTerm::App { func, arg } = &application else {
            return Err(OpenTheoryError::MalformedObject {
                command: "betaConv",
                detail: "expected an application".to_string(),
            });
        };
        let OtTerm::Abs { binder, body } = func.as_ref() else {
            return Err(OpenTheoryError::MalformedObject {
                command: "betaConv",
                detail: "expected a lambda on the left of the application".to_string(),
            });
        };
        let reduced = body.substitute_terms(&[(binder.clone(), arg.as_ref().clone())]);
        self.stack.push(OtObject::Thm(OtTheorem::new(
            Vec::new(),
            OtTerm::eq(application, reduced)?,
        )));
        Ok(())
    }

    pub(super) fn handle_deduct_antisym(&mut self) -> OpenTheoryResult<()> {
        let delta = self.pop_thm("deductAntisym")?;
        let gamma = self.pop_thm("deductAntisym")?;
        let phi = gamma.conclusion.clone();
        let psi = delta.conclusion.clone();
        self.stack.push(OtObject::Thm(OtTheorem::new(
            OtTheorem::union_hypotheses(
                &OtTheorem::without_hypothesis(&gamma.hypotheses, &psi),
                &OtTheorem::without_hypothesis(&delta.hypotheses, &phi),
            ),
            OtTerm::eq(phi, psi)?,
        )));
        Ok(())
    }

    pub(super) fn handle_define_const(&mut self) -> OpenTheoryResult<()> {
        let term = self.pop_term("defineConst")?;
        let name = self.pop_name("defineConst")?;
        let principal_type = term.ty()?;
        let constant = OtConstant::defined(name, principal_type.clone(), self.fresh_symbol_id());
        let theorem = OtTheorem::new(
            Vec::new(),
            OtTerm::eq(OtTerm::const_(constant.clone(), principal_type), term)?,
        );
        self.stack.push(OtObject::Const(constant));
        self.stack.push(OtObject::Thm(theorem));
        Ok(())
    }

    pub(super) fn handle_define_const_list(&mut self) -> OpenTheoryResult<()> {
        let theorem = self.pop_thm("defineConstList")?;
        let pairs = self.pop_list("defineConstList")?;
        let pairings = pairs
            .iter()
            .map(extract_name_var_pair)
            .collect::<OpenTheoryResult<Vec<_>>>()?;
        let definitions = theorem
            .hypotheses
            .iter()
            .map(extract_variable_definition)
            .collect::<OpenTheoryResult<Vec<_>>>()?;

        let mut substitutions = Vec::new();
        let mut constants = Vec::new();
        for (name, variable) in pairings {
            let (_, rhs) = definitions
                .iter()
                .find(|(lhs, _)| lhs == &variable)
                .ok_or_else(|| OpenTheoryError::MalformedObject {
                    command: "defineConstList",
                    detail: format!("missing defining hypothesis for `{}`", variable.name),
                })?;
            let principal_type = rhs.ty()?;
            let constant =
                OtConstant::defined(name, principal_type.clone(), self.fresh_symbol_id());
            let const_term = OtTerm::const_(constant.clone(), principal_type);
            substitutions.push((variable.clone(), const_term));
            constants.push(OtObject::Const(constant));
        }

        self.stack.push(OtObject::List(constants));
        self.stack.push(OtObject::Thm(OtTheorem::new(
            Vec::new(),
            theorem.conclusion.substitute_terms(&substitutions),
        )));
        Ok(())
    }

    pub(super) fn handle_define_type_op(&mut self) -> OpenTheoryResult<()> {
        let witness_theorem = self.pop_thm("defineTypeOp")?;
        let type_var_names = self.pop_name_list("defineTypeOp")?;
        let rep_name = self.pop_name("defineTypeOp")?;
        let abs_name = self.pop_name("defineTypeOp")?;
        let op_name = self.pop_name("defineTypeOp")?;

        let OtTerm::App {
            func: predicate,
            arg: witness,
        } = &witness_theorem.conclusion
        else {
            return Err(OpenTheoryError::MalformedObject {
                command: "defineTypeOp",
                detail: "expected a predicate application `phi t`".to_string(),
            });
        };
        let arity = type_var_names.len();
        let op = OtTypeOperator::defined(op_name, arity, self.fresh_symbol_id());
        let params = type_var_names
            .iter()
            .cloned()
            .map(OtType::Var)
            .collect::<Vec<_>>();
        let abstract_ty = OtType::apply(op.clone(), params);
        let rep_ty = witness.ty()?;
        let abs_const_ty = OtType::function(rep_ty.clone(), abstract_ty.clone());
        let rep_const_ty = OtType::function(abstract_ty.clone(), rep_ty.clone());
        let abs_const = OtConstant::defined(abs_name, abs_const_ty.clone(), self.fresh_symbol_id());
        let rep_const = OtConstant::defined(rep_name, rep_const_ty.clone(), self.fresh_symbol_id());

        let abs_const_term = OtTerm::const_(abs_const.clone(), abs_const_ty);
        let rep_const_term = OtTerm::const_(rep_const.clone(), rep_const_ty);

        // Build shared subterms: abs(rep(a)) and rep(abs(r)).
        let a_var = OtVariable::new(OtName::global("a"), abstract_ty.clone());
        let a_term = OtTerm::var(a_var.clone());
        let rep_of_a = OtTerm::app(rep_const_term.clone(), a_term.clone())?;
        let abs_of_rep_a = OtTerm::app(abs_const_term.clone(), rep_of_a)?;

        let r_var = OtVariable::new(OtName::global("r"), rep_ty.clone());
        let r_term = OtTerm::var(r_var.clone());
        let abs_of_r = OtTerm::app(abs_const_term, r_term.clone())?;
        let rep_abs_r = OtTerm::app(rep_const_term, abs_of_r)?;

        let (abs_theorem, rep_theorem) = if self.version >= 6 {
            // Version 6:
            //   abs_thm: |- (λa. abs(rep a)) = (λa. a)
            //   rep_thm: |- (λr. rep(abs r) = r) = (λr. φ r)
            let left_abs = OtTerm::abs(a_var.clone(), abs_of_rep_a);
            let right_abs = OtTerm::abs(a_var, a_term);
            let abs_thm = OtTheorem::new(Vec::new(), OtTerm::eq(left_abs, right_abs)?);

            let left_rep = OtTerm::abs(r_var.clone(), OtTerm::eq(rep_abs_r, r_term.clone())?);
            let right_rep = OtTerm::abs(r_var, OtTerm::app(predicate.as_ref().clone(), r_term)?);
            let rep_thm = OtTheorem::new(Vec::new(), OtTerm::eq(left_rep, right_rep)?);
            (abs_thm, rep_thm)
        } else {
            // Version 5 (and earlier):
            //   abs_thm: |- abs(rep a) = a
            //   rep_thm: |- φ r = (rep(abs r) = r)
            let abs_thm = OtTheorem::new(Vec::new(), OtTerm::eq(abs_of_rep_a, a_term)?);

            let phi_r = OtTerm::app(predicate.as_ref().clone(), r_term.clone())?;
            let rep_eq = OtTerm::eq(rep_abs_r, r_term)?;
            let rep_thm = OtTheorem::new(Vec::new(), OtTerm::eq(phi_r, rep_eq)?);
            (abs_thm, rep_thm)
        };

        self.stack.push(OtObject::TypeOp(op));
        self.stack.push(OtObject::Const(abs_const));
        self.stack.push(OtObject::Const(rep_const));
        self.stack.push(OtObject::Thm(abs_theorem));
        self.stack.push(OtObject::Thm(rep_theorem));
        Ok(())
    }

    pub(super) fn handle_eq_mp(&mut self) -> OpenTheoryResult<()> {
        let proof = self.pop_thm("eqMp")?;
        let equality = self.pop_thm("eqMp")?;
        let (lhs, rhs) = equality
            .as_equality()
            .ok_or(OpenTheoryError::EqualityConclusionExpected { command: "eqMp" })?;
        if !lhs.alpha_eq(&proof.conclusion) {
            return Err(OpenTheoryError::MalformedObject {
                command: "eqMp",
                detail: "the proof conclusion does not match the equality lhs".to_string(),
            });
        }
        self.stack.push(OtObject::Thm(OtTheorem::new(
            OtTheorem::union_hypotheses(&proof.hypotheses, &equality.hypotheses),
            rhs.clone(),
        )));
        Ok(())
    }

    pub(super) fn handle_thm(&mut self) -> OpenTheoryResult<()> {
        let conclusion = self.pop_term("thm")?;
        let hypotheses = self.pop_term_list("thm")?;
        let theorem = self.pop_thm("thm")?;
        if !theorem.conclusion.alpha_eq(&conclusion) {
            return Err(OpenTheoryError::MalformedObject {
                command: "thm",
                detail: "conclusion does not match the proof theorem".to_string(),
            });
        }
        if theorem
            .hypotheses
            .iter()
            .any(|hypothesis| !hypothesis.alpha_mem(&hypotheses))
        {
            return Err(OpenTheoryError::MalformedObject {
                command: "thm",
                detail: "proof hypotheses are not covered by the exported hypothesis list"
                    .to_string(),
            });
        }
        self.push_theorem(OtTheorem::new(hypotheses, conclusion));
        Ok(())
    }

    pub(super) fn handle_trans(&mut self) -> OpenTheoryResult<()> {
        let delta = self.pop_thm("trans")?;
        let gamma = self.pop_thm("trans")?;
        let (t2_prime, t3) = delta
            .as_equality()
            .ok_or(OpenTheoryError::EqualityConclusionExpected { command: "trans" })?;
        let (t1, t2) = gamma
            .as_equality()
            .ok_or(OpenTheoryError::EqualityConclusionExpected { command: "trans" })?;
        if !t2.alpha_eq(t2_prime) {
            return Err(OpenTheoryError::MalformedObject {
                command: "trans",
                detail: "middle terms are not equal".to_string(),
            });
        }
        self.stack.push(OtObject::Thm(OtTheorem::new(
            OtTheorem::union_hypotheses(&gamma.hypotheses, &delta.hypotheses),
            OtTerm::eq(t1.clone(), t3.clone())?,
        )));
        Ok(())
    }
}
