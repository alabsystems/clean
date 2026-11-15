// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'a> State<'a> {
    pub(super) fn variable_sort<O: ExecutionObserver>(
        &mut self,
        spec: &'a SpecModule,
        variable: &'a SpecVar,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Option<&ClauseSort>>())?;
        let Some(declared) = &variable.sort else {
            return Ok(());
        };
        let Some(parsed) = sorts::parse(&variable.ty, work)? else {
            return Ok(());
        };
        if !self.equal_sort(sorts::Sort::Fixed(parsed), declared, work)? {
            self.begin_detail(work)?;
            work.text("type tag ", &mut self.detail)?;
            work.quoted(&variable.ty, &mut self.detail)?;
            work.text(" reads as sort ", &mut self.detail)?;
            self.sort_text(sorts::Sort::Fixed(parsed), work)?;
            work.text(", but the declared sort is ", &mut self.detail)?;
            self.sort_text(sorts::Sort::Borrowed(declared), work)?;
            emit!(
                self,
                work,
                V::SpecVariableSortMismatch {
                    machine: &spec.name,
                    variable: &variable.name,
                    detail: &self.detail
                }
            )?;
            self.clear_detail(work)?;
        }
        Ok(())
    }
    fn typed_issue<O: ExecutionObserver>(
        &mut self,
        spec: &SpecModule,
        subject: &'static str,
        name: &str,
        bound: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        emit!(
            self,
            work,
            V::SpecTypedBindingInvalid {
                machine: &spec.name,
                subject,
                name,
                binding: bound,
                detail: &self.detail
            }
        )?;
        self.clear_detail(work)
    }
    pub(super) fn typed<O: ExecutionObserver>(
        &mut self,
        spec: &'a SpecModule,
        subject: &'static str,
        name: &str,
        formula: &'a ProofFormula,
        action: bool,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some((bound, binding)) = work.at(&formula.bindings, at)? {
            work.admit(11, size_of::<ClausePlace>())?;
            let index = match binding.place {
                ClausePlace::SpecVar { index } => index,
                ClausePlace::SpecVarNext { index } => {
                    work.admit(1, 0)?;
                    if !action {
                        self.begin_detail(work)?;
                        work.text("SpecVarNext ", &mut self.detail)?;
                        work.number(u128::from(index), &mut self.detail)?;
                        work.text(
                            " names the SUCCESSOR state, which only an action relation has; this ",
                            &mut self.detail,
                        )?;
                        work.text(subject, &mut self.detail)?;
                        work.text(" is a single-state predicate", &mut self.detail)?;
                        self.typed_issue(spec, subject, name, bound, work)?;
                        work.next(&mut at)?;
                        continue;
                    }
                    index
                }
                place => {
                    self.begin_detail(work)?;
                    work.text("place ", &mut self.detail)?;
                    format::place(place, &mut self.detail, work)?;
                    work.text(" belongs to a function signature, not to a spec machine's state; a spec carrier may bind only SpecVar / SpecVarNext",&mut self.detail)?;
                    self.typed_issue(spec, subject, name, bound, work)?;
                    work.next(&mut at)?;
                    continue;
                }
            };
            work.admit(1, size_of::<usize>())?;
            let Some(variable) = work.at(&spec.vars, index as usize)? else {
                self.begin_detail(work)?;
                work.text("state variable ", &mut self.detail)?;
                work.number(u128::from(index), &mut self.detail)?;
                work.text(" is out of range: this machine declares ", &mut self.detail)?;
                work.number(spec.vars.len() as u128, &mut self.detail)?;
                work.text(" variable(s)", &mut self.detail)?;
                self.typed_issue(spec, subject, name, bound, work)?;
                work.next(&mut at)?;
                continue;
            };
            if let Some(declared) = sorts::effective(variable, work)?
                && !self.equal_sort(declared, &binding.sort, work)?
            {
                self.begin_detail(work)?;
                work.text("binds state variable ", &mut self.detail)?;
                work.number(u128::from(index), &mut self.detail)?;
                work.text(" (", &mut self.detail)?;
                work.quoted(&variable.name, &mut self.detail)?;
                work.text(") at sort ", &mut self.detail)?;
                self.sort_text(sorts::Sort::Borrowed(&binding.sort), work)?;
                work.text(", but the variable declares sort ", &mut self.detail)?;
                self.sort_text(declared, work)?;
                self.typed_issue(spec, subject, name, bound, work)?;
            }
            let mut spelled = 0;
            while let Some(other) = work.at(&spec.vars, spelled)? {
                if work.equal(&other.name, bound)? {
                    work.admit(1, size_of::<usize>())?;
                    if spelled != index as usize {
                        self.begin_detail(work)?;
                        work.text("is the name of state variable ", &mut self.detail)?;
                        work.number(spelled as u128, &mut self.detail)?;
                        work.text(" (", &mut self.detail)?;
                        work.quoted(&other.name, &mut self.detail)?;
                        work.text(
                            "), but this binding indexes state variable ",
                            &mut self.detail,
                        )?;
                        work.number(u128::from(index), &mut self.detail)?;
                        work.text(" (", &mut self.detail)?;
                        work.quoted(&variable.name, &mut self.detail)?;
                        work.text(
                            "); one name cannot denote two of this machine's variables",
                            &mut self.detail,
                        )?;
                        self.typed_issue(spec, subject, name, bound, work)?;
                    }
                    break;
                }
                work.next(&mut spelled)?;
            }
            work.next(&mut at)?;
        }
        Ok(())
    }
    pub(super) fn temporals<O: ExecutionObserver>(
        &mut self,
        spec: &'a SpecModule,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(property) = work.at(&spec.temporal, at)? {
            self.blank(spec, "temporal", "name", &property.name, work)?;
            work.admit(
                5,
                size_of::<Option<&str>>() + size_of::<[Option<(&ProofFormula, bool)>; 2]>(),
            )?;
            let (action, formulas) = match &property.form {
                TemporalForm::Always(p) | TemporalForm::Eventually(p) => {
                    (None, [Some((p, false)), None])
                }
                TemporalForm::LeadsTo(p, q) => (None, [Some((p, false)), Some((q, false))]),
                TemporalForm::WeakFair { action, relation }
                | TemporalForm::StrongFair { action, relation } => (
                    Some(action.as_str()),
                    [relation.as_ref().map(|p| (p, true)), None],
                ),
            };
            if let Some(action) = action {
                self.blank(spec, "temporal", "action", action, work)?;
                if !work.blank(action)?
                    && !work.blank(&spec.name)?
                    && !has_action(spec, action, work)?
                {
                    self.begin_detail(work)?;
                    work.text("fairness property ", &mut self.detail)?;
                    work.quoted(&property.name, &mut self.detail)?;
                    work.text(
                        " names an action this machine does not declare",
                        &mut self.detail,
                    )?;
                    emit!(
                        self,
                        work,
                        V::ActionMissing {
                            machine: &spec.name,
                            action,
                            from: "temporal",
                            detail: &self.detail
                        }
                    )?;
                    self.clear_detail(work)?;
                }
            }
            let mut f = 0;
            while let Some(formula) = work.at(&formulas, f)? {
                work.admit(1, size_of::<Option<(&ProofFormula, bool)>>())?;
                if let Some((formula, action)) = *formula {
                    self.typed(spec, "temporal", &property.name, formula, action, work)?;
                }
                work.next(&mut f)?;
            }
            work.next(&mut at)?;
        }
        Ok(())
    }
}
pub(super) fn has_action<O: ExecutionObserver>(
    spec: &SpecModule,
    action: &str,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    let mut index = 0;
    while let Some(row) = work.at(&spec.actions, index)? {
        if work.equal(row, action)? {
            return Ok(true);
        }
        work.next(&mut index)?;
    }
    Ok(false)
}
