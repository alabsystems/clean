// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Exact core bundle formula inventory and complete owning disagreement sites.
use super::{
    NativeVerificationBundle, NativeVerificationBundleError as E,
    retire_native_bundle_errors_observed,
};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::proof::{FormulaSite, FormulaSiteRef, ProofFormula};
use crate::spec::TemporalForm;
use crate::{FuncId, Module};
use core::mem::{size_of, take};
mod inventory;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    machine: String,
    label: String,
    pending: Option<E>,
    errors: Vec<E>,
}
impl NativeVerificationBundle {
    /// Exact whole original bundle formula disagreement group: actual physical
    /// obligations, functions' requires/ensures/decreases, then each spec's
    /// typed invariants and temporal leaves, with both LeadsTo leaves kept.
    /// Every traversal/actual formula child/raw label/growth/transport uses the
    /// same original session/site. No formula truth, replay or proof authority
    /// is inferred from this DATA diagnostic leaf.
    pub fn formula_text_errors_observed<O: ExecutionObserver>(
        &self,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        let mut w = Work { session: s, site };
        w.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
        let mut st = State::default();
        let result = st.run(&self.module, &mut w);
        st.finish(result, &mut w)
    }
}
impl State {
    fn formula<O: ExecutionObserver>(
        &mut self,
        source: FormulaSiteRef<'_>,
        formula: &ProofFormula,
        module: &Module,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(
            1,
            size_of::<FormulaSiteRef<'_>>() + size_of::<crate::pred::PredTable<'_>>(),
        )?;
        let predicates = module.pred_table();
        if !formula.states_two_texts_observed(&predicates, w.session, w.site)? {
            return Ok(());
        }
        w.admit(4, size_of::<FormulaSiteRef<'_>>())?;
        match source {
            FormulaSiteRef::Obligation(id) => {
                self.fixed(|| FormulaSite::Obligation(id), w)?;
            }
            FormulaSiteRef::SummaryClause {
                function,
                clause,
                index,
            } => {
                self.fixed(
                    || FormulaSite::SummaryClause {
                        function,
                        clause,
                        index,
                    },
                    w,
                )?;
            }
            FormulaSiteRef::SpecInvariant { machine, invariant } => {
                w.text(machine, &mut self.machine)?;
                w.text(invariant, &mut self.label)?;
                w.admit(
                    1,
                    size_of::<E>()
                        + size_of::<Option<E>>()
                        + size_of::<FormulaSite>()
                        + 2 * size_of::<String>(),
                )?;
                self.pending = Some(E::FormulaTextsDisagree {
                    site: FormulaSite::SpecInvariant {
                        machine: take(&mut self.machine),
                        invariant: take(&mut self.label),
                    },
                });
                self.emit(w)?;
            }
            FormulaSiteRef::SpecTemporal { machine, property } => {
                w.text(machine, &mut self.machine)?;
                w.text(property, &mut self.label)?;
                w.admit(
                    1,
                    size_of::<E>()
                        + size_of::<Option<E>>()
                        + size_of::<FormulaSite>()
                        + 2 * size_of::<String>(),
                )?;
                self.pending = Some(E::FormulaTextsDisagree {
                    site: FormulaSite::SpecTemporal {
                        machine: take(&mut self.machine),
                        property: take(&mut self.label),
                    },
                });
                self.emit(w)?;
            }
        }
        Ok(())
    }
    fn fixed<O: ExecutionObserver>(
        &mut self,
        make: impl FnOnce() -> FormulaSite,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(
            1,
            size_of::<E>() + size_of::<Option<E>>() + size_of::<FormulaSite>(),
        )?;
        self.pending = Some(E::FormulaTextsDisagree { site: make() });
        self.emit(w)
    }
    fn emit<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) -> R {
        w.reserve(&mut self.errors)?;
        w.admit(1, size_of::<E>() + size_of::<Option<E>>())?;
        self.errors.push(
            self.pending
                .take()
                .ok_or(ObservedValueError::InvalidRange)?,
        );
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.record(1, 2 * size_of::<String>());
        w.text_drop(take(&mut self.machine));
        w.text_drop(take(&mut self.label));
        w.record(1, size_of::<Option<E>>());
        if let Some(e) = self.pending.take() {
            let _ = e.retire_observed(w.session, w.site);
        }
        w.poll();
    }
    fn finish<O: ExecutionObserver>(&mut self, result: R, w: &mut Work<'_, '_, O>) -> R<Vec<E>> {
        self.retire_scratch(w);
        match result.and_then(|()| w.publication(size_of::<Vec<E>>())) {
            Ok(()) => Ok(take(&mut self.errors)),
            Err(error) => {
                w.record(1, size_of::<Vec<E>>());
                let _ =
                    retire_native_bundle_errors_observed(take(&mut self.errors), w.session, w.site);
                Err(error)
            }
        }
    }
}
