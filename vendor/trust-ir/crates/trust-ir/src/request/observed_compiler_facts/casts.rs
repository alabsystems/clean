// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl NativeCastFact {
    /// Complete ordinary cast-fact diagnostics. All layout-sensitive predicates
    /// run through the original-session observed layout constituent; no legacy
    /// predicate, ordinary memo or source/proof authority is credited here.
    pub fn validation_errors_observed<O: ExecutionObserver>(
        &self,
        layouts: &LayoutTable<'_>,
        functions: &BTreeSet<FuncId>,
        obligations: &BTreeSet<ProofId>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        let mut work = Work::new(session, site)?;
        let result = work.cast(layouts, self, functions, obligations, session, site);
        work.finish(result, session, site)
    }

    /// The ordinary cast result-node correspondence checks only, preserving
    /// the optional-result and actual-function absence guards.
    pub fn result_errors_observed<O: ExecutionObserver>(
        &self,
        module: &Module,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        let mut work = Work::new(session, site)?;
        let result = work.cast_result(module, self, session, site);
        work.finish(result, session, site)
    }
}

impl Work {
    pub(super) fn cast<O: ExecutionObserver>(
        &mut self,
        layouts: &LayoutTable<'_>,
        fact: &NativeCastFact,
        functions: &BTreeSet<FuncId>,
        obligations: &BTreeSet<ProofId>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let reference = NativeCompilerFactRef::Cast(fact.id);
        if !member(functions, &fact.function, session, site)? {
            self.unknown_function(reference, fact.function, session, site)?;
        }
        self.cast_result(layouts.module(), fact, session, site)?;
        self.obligations(reference, &fact.obligations, obligations, session, site)?;
        admit(session, site, 16, 0)?;
        if !fact.op.is_layout_sensitive() && fact.evidence != CastLayoutEvidence::NotLayoutSensitive
        {
            self.invalid(reference, "evidence", session, site)?;
        }
        match layouts.layout_sensitive_cast_evidence_observed(
            fact.op,
            &fact.source_ty,
            &fact.target_ty,
            session,
            site,
        )? {
            Ok(evidence) => self.cast_evidence = Some(evidence),
            Err(error) => self.layout_error = Some(error),
        }
        if let Some(expected) = &self.cast_evidence {
            admit(session, site, 32, 0)?;
            if *expected != fact.evidence {
                self.invalid(reference, "evidence", session, site)?;
            }
        } else {
            admit(session, site, 1, 0)?;
            if !matches!(
                &self.layout_error,
                Some(LayoutError::EnumLayoutUnavailable(_) | LayoutError::UnsupportedTyShape(_))
            ) {
                self.invalid(reference, "evidence", session, site)?;
            }
        }
        Ok(())
    }

    pub(super) fn cast_result<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        fact: &NativeCastFact,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        admit(session, site, 1, 0)?;
        let Some(result) = fact.result else {
            return Ok(());
        };
        let Some(function) = values::function(module, fact.function, session, site)? else {
            return Ok(());
        };
        if !matching(function, result, fact, session, site)? {
            self.invalid(
                NativeCompilerFactRef::Cast(fact.id),
                "result",
                session,
                site,
            )?;
        }
        Ok(())
    }
}

fn matching<O: ExecutionObserver>(
    function: &Function,
    result: ValueId,
    fact: &NativeCastFact,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    let Some(node) = values::result_node(function, result, session, site)? else {
        return Ok(false);
    };
    admit(session, site, 1, 0)?;
    let Inst::Cast {
        op, src_ty, dst_ty, ..
    } = &node.inst
    else {
        return Ok(false);
    };
    if *op != fact.op || !src_ty.structural_eq_observed(&fact.source_ty, session, site)? {
        return Ok(false);
    }
    dst_ty.structural_eq_observed(&fact.target_ty, session, site)
}
