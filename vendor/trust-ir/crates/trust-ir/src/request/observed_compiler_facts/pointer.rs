// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl NativePointerOffsetFact {
    /// Exact pointer-offset helper diagnostics, including value/result checks,
    /// under the caller's original session. Supplied known-ID sets are checked,
    /// not authenticated. This does not validate other facts or a full bundle.
    pub fn validation_errors_observed<O: ExecutionObserver>(
        &self,
        layouts: &LayoutTable<'_>,
        known_functions: &BTreeSet<FuncId>,
        known_obligations: &BTreeSet<ProofId>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        let mut work = Work::new(session, site)?;
        let result = work.pointer(
            layouts,
            self,
            known_functions,
            known_obligations,
            session,
            site,
        );
        work.finish(result, session, site)
    }

    /// Only the ordinary pointer-offset value/result constituent. All returned
    /// diagnostics and their successful disposal remain caller-owned.
    pub fn value_errors_observed<O: ExecutionObserver>(
        &self,
        module: &Module,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        let mut work = Work::new(session, site)?;
        let result = work.pointer_values(module, self, session, site);
        work.finish(result, session, site)
    }
}

impl Work {
    pub(super) fn pointer<O: ExecutionObserver>(
        &mut self,
        layouts: &LayoutTable<'_>,
        fact: &NativePointerOffsetFact,
        functions: &BTreeSet<FuncId>,
        obligations: &BTreeSet<ProofId>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let reference = NativeCompilerFactRef::PointerOffset(fact.id);
        if !member(functions, &fact.function, session, site)? {
            self.unknown_function(reference, fact.function, session, site)?;
        }
        admit(session, site, 16, 0)?;
        if !fact.base_ty.is_pointer_like() {
            self.invalid(reference, "base_ty", session, site)?;
        }
        admit(session, site, 8, 0)?;
        if !fact.offset_ty.is_signed() {
            self.invalid(reference, "offset_ty", session, site)?;
        }
        match layouts.ty_layout_observed(&fact.pointee_ty, session, site)? {
            Ok(layout) => self.layout = Some(layout),
            Err(error) => self.layout_error = Some(error),
        }
        if let Some(expected) = &self.layout {
            if !layout_equal(expected, &fact.element_layout, session, site)? {
                self.invalid(reference, "element_layout", session, site)?;
            }
            admit(session, site, 2, 0)?;
            if self
                .layout
                .as_ref()
                .is_some_and(|expected| expected.size_bits != fact.stride_bits)
                || !fact.stride_bits.is_multiple_of(8)
            {
                self.invalid(reference, "stride_bits", session, site)?;
            }
        } else {
            admit(session, site, 1, 0)?;
            if !matches!(
                &self.layout_error,
                Some(LayoutError::EnumLayoutUnavailable(_) | LayoutError::UnsupportedTyShape(_))
            ) {
                self.invalid(reference, "element_layout", session, site)?;
            }
        }
        admit(session, site, 1, 0)?;
        if let NativePointerOffsetProvenance::Unsupported(unsupported) = &fact.provenance {
            if blank(&unsupported.detail, session, site)? {
                self.invalid(reference, "provenance.unsupported.detail", session, site)?;
            }
            admit(session, site, 1, 0)?;
            if !fact.obligations.is_empty() {
                self.invalid(reference, "provenance", session, site)?;
            }
        }
        self.pointer_values(layouts.module(), fact, session, site)?;
        self.obligations(reference, &fact.obligations, obligations, session, site)
    }

    pub(super) fn pointer_values<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        fact: &NativePointerOffsetFact,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let Some(function) = values::function(module, fact.function, session, site)? else {
            return Ok(());
        };
        let reference = NativeCompilerFactRef::PointerOffset(fact.id);
        if !self.value_matches(function, fact.base, &fact.base_ty, session, site)? {
            self.invalid(reference, "base", session, site)?;
        }
        if !self.value_matches(function, fact.offset, &fact.offset_ty, session, site)? {
            self.invalid(reference, "offset", session, site)?;
        }
        admit(session, site, 1, 0)?;
        if let Some(result) = fact.result
            && !pointer_result(function, result, fact, session, site)?
        {
            self.invalid(reference, "result", session, site)?;
        }
        Ok(())
    }
}

fn pointer_result<O: ExecutionObserver>(
    function: &Function,
    result: ValueId,
    fact: &NativePointerOffsetFact,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    let Some(node) = values::result_node(function, result, session, site)? else {
        return Ok(false);
    };
    admit(session, site, 1, 0)?;
    let Inst::GEP {
        pointee_ty,
        base,
        indices,
        ..
    } = &node.inst
    else {
        return Ok(false);
    };
    if !pointee_ty.structural_eq_observed(&fact.pointee_ty, session, site)? {
        return Ok(false);
    }
    admit(session, site, 3, 0)?;
    Ok(*base == fact.base && indices.len() == 1 && indices[0] == fact.offset)
}
