// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0usize;
        while let Some(row) = work.at(&module.proof_obligations, index)? {
            work.admit(1, size_of::<Option<&ProofFormula>>())?;
            if let Some(formula) = &row.formula {
                work.admit(1, size_of::<FormulaSiteRef<'_>>())?;
                self.formula(FormulaSiteRef::Obligation(row.id), formula, module, work)?
            }
            work.next(&mut index)?;
        }
        let mut index = 0usize;
        while let Some(function) = work.at(&module.functions, index)? {
            work.admit(1, size_of::<Option<&crate::FunctionSummary>>())?;
            if let Some(summary) = &function.summary {
                self.clauses(function.id, "requires", &summary.requires, module, work)?;
                self.clauses(function.id, "ensures", &summary.ensures, module, work)?;
                self.clauses(function.id, "decreases", &summary.decreases, module, work)?;
            }
            work.next(&mut index)?;
        }
        let mut index = 0usize;
        while let Some(spec) = work.at(&module.spec_modules, index)? {
            let mut at = 0usize;
            while let Some(invariant) = work.at(&spec.invariants, at)? {
                work.admit(1, size_of::<Option<&ProofFormula>>())?;
                if let Some(formula) = &invariant.typed {
                    work.admit(1, size_of::<FormulaSiteRef<'_>>())?;
                    self.formula(
                        FormulaSiteRef::SpecInvariant {
                            machine: &spec.name,
                            invariant: &invariant.name,
                        },
                        formula,
                        module,
                        work,
                    )?;
                }
                work.next(&mut at)?;
            }
            let mut at = 0usize;
            while let Some(property) = work.at(&spec.temporal, at)? {
                self.temporal(&spec.name, &property.name, &property.form, module, work)?;
                work.next(&mut at)?;
            }
            work.next(&mut index)?;
        }
        Ok(())
    }
    fn clauses<O: ExecutionObserver>(
        &mut self,
        function: FuncId,
        clause: &'static str,
        formulas: &[ProofFormula],
        module: &Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0usize;
        while let Some(formula) = work.at(formulas, index)? {
            work.admit(1, size_of::<FormulaSiteRef<'_>>())?;
            self.formula(
                FormulaSiteRef::SummaryClause {
                    function,
                    clause,
                    index,
                },
                formula,
                module,
                work,
            )?;
            work.next(&mut index)?;
        }
        Ok(())
    }
    fn temporal<O: ExecutionObserver>(
        &mut self,
        machine: &str,
        property: &str,
        form: &TemporalForm,
        module: &Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(
            5,
            size_of::<FormulaSiteRef<'_>>() + size_of::<Option<&ProofFormula>>(),
        )?;
        let source = FormulaSiteRef::SpecTemporal { machine, property };
        match form {
            TemporalForm::Always(formula) | TemporalForm::Eventually(formula) => {
                self.formula(source, formula, module, work)
            }
            TemporalForm::LeadsTo(first, second) => {
                self.formula(source, first, module, work)?;
                self.formula(source, second, module, work)
            }
            TemporalForm::WeakFair { relation, .. } | TemporalForm::StrongFair { relation, .. } => {
                if let Some(formula) = relation {
                    self.formula(source, formula, module, work)?
                }
                Ok(())
            }
        }
    }
}
