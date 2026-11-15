// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State<'_> {
    pub(super) fn obligations<O: ExecutionObserver>(
        &mut self,
        b: &NativeVerificationBundle,
        r: &NativeVerificationRequest,
        id: NativeRequestId,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(obligation) = w.at(&self.ids, at)? {
            w.admit(1, size_of::<ProofId>() + size_of::<R<bool>>())?;
            let obligation = *obligation;
            let present = self
                .lineage
                .as_ref()
                .ok_or(ObservedValueError::InvalidRange)?
                .source_bound_obligation_contains_observed(obligation, w.session, w.site)?;
            if !present {
                self.fixed(
                    || E::RequestObligationNotInLineage {
                        request: id,
                        obligation,
                    },
                    w,
                )?;
            }
            if let Some(source) = Self::source(b, obligation, w)? {
                w.admit(1, size_of::<bool>())?;
                if source.span.is_none() {
                    self.fixed(
                        || E::MissingObligationSourceSpan {
                            request: id,
                            obligation,
                        },
                        w,
                    )?;
                }
            }
            if let Some(source) = Self::source(b, obligation, w)? {
                w.admit(1, size_of::<bool>())?;
                if source.assertion_id.is_none() {
                    self.fixed(
                        || E::MissingObligationSourceAssertion {
                            request: id,
                            obligation,
                        },
                        w,
                    )?;
                }
            }
            w.next(&mut at)?;
        }
        w.admit(1, size_of::<Option<FuncId>>())?;
        if let Some(function) = r.function()
            && !Self::function_exists(b, function, w)?
        {
            self.fixed(
                || E::MissingFunction {
                    request: id,
                    function,
                },
                w,
            )?;
        }
        w.admit(1, size_of::<Option<FuncId>>())?;
        if let Some(function) = r.function() {
            let mut at = 0;
            while let Some(obligation) = w.at(&self.ids, at)? {
                w.admit(1, size_of::<ProofId>())?;
                let obligation = *obligation;
                if let Some(source) = Self::source(b, obligation, w)? {
                    w.admit(2, size_of::<Option<FuncId>>() + size_of::<bool>())?;
                    if source.function != Some(function) {
                        self.fixed(
                            || E::RequestObligationFunctionMismatch {
                                request: id,
                                obligation,
                                expected: function,
                                actual: source.function,
                            },
                            w,
                        )?;
                    }
                }
                w.next(&mut at)?;
            }
        }
        Ok(())
    }
    fn source<'a, O: ExecutionObserver>(
        b: &'a NativeVerificationBundle,
        id: ProofId,
        w: &mut Work<'_, '_, O>,
    ) -> R<Option<&'a NativeObligationSource>> {
        let mut at = 0;
        while let Some(row) = w.at(&b.compiler_facts.obligation_sources, at)? {
            w.admit(1, 2 * size_of::<ProofId>() + size_of::<bool>())?;
            if row.obligation == id {
                return Ok(Some(row));
            }
            w.next(&mut at)?;
        }
        Ok(None)
    }
    fn function_exists<O: ExecutionObserver>(
        b: &NativeVerificationBundle,
        id: FuncId,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        w.admit(1, size_of::<usize>())?;
        let index = id.as_usize();
        if let Some(f) = w.at(&b.module.functions, index)? {
            w.admit(1, 2 * size_of::<FuncId>() + size_of::<bool>())?;
            if f.id == id {
                return Ok(true);
            }
        }
        let mut at = 0;
        while let Some(f) = w.at(&b.module.functions, at)? {
            w.admit(1, 2 * size_of::<FuncId>() + size_of::<bool>())?;
            if f.id == id {
                return Ok(true);
            }
            w.next(&mut at)?;
        }
        Ok(false)
    }
}
