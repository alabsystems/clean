// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State {
    pub(super) fn bind<O: ExecutionObserver>(
        &mut self,
        id: NativeRequestId,
        a: &NativeReplayAtom,
        obligations: &[ProofId],
        facts: &NativeCompilerFacts,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(
            4,
            size_of::<NativeReplayAtomKind>()
                + size_of::<Option<ProofId>>()
                + size_of::<Option<super::super::NativeAssertionId>>()
                + size_of::<bool>(),
        )?;
        if a.kind == NativeReplayAtomKind::Assertion
            && a.obligation.is_none()
            && a.assertion_id.is_none()
        {
            self.invalid(id, a, "assertion_binding", w)?;
        }
        w.admit(3, size_of::<bool>())?;
        if a.assertion_id.is_some() && a.obligation.is_none() {
            self.invalid(id, a, "assertion_id.obligation", w)?;
        }
        w.admit(3, size_of::<bool>())?;
        if a.span.is_some() && a.obligation.is_none() {
            self.invalid(id, a, "span.obligation", w)?;
        }
        w.admit(1, size_of::<Option<ProofId>>())?;
        let Some(obligation) = a.obligation else {
            return Ok(());
        };
        if !self.requested(obligations, obligation, w)? {
            self.fixed(
                || E::ReplayAtomObligationNotRequested {
                    request: id,
                    atom: a.id,
                    obligation,
                },
                w,
            )?;
        }
        let Some(source) = self.source(facts, obligation, w)? else {
            return Ok(());
        };
        w.admit(
            3,
            2 * size_of::<Option<super::super::NativeAssertionId>>() + size_of::<bool>(),
        )?;
        if let Some(actual) = a.assertion_id
            && source.assertion_id != Some(actual)
        {
            self.fixed(
                || E::ReplayAtomAssertionMismatch {
                    request: id,
                    atom: a.id,
                    obligation,
                    expected: source.assertion_id,
                    actual,
                },
                w,
            )?;
        }
        w.admit(
            6,
            2 * size_of::<Option<crate::SourceSpan>>() + size_of::<bool>(),
        )?;
        if let (Some(expected), Some(actual)) = (source.span, a.span)
            && expected != actual
        {
            self.fixed(
                || E::ReplayAtomSourceSpanMismatch {
                    request: id,
                    atom: a.id,
                    obligation,
                    expected,
                    actual,
                },
                w,
            )?;
        }
        Ok(())
    }
    fn requested<O: ExecutionObserver>(
        &self,
        rows: &[ProofId],
        id: ProofId,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut at = 0;
        while let Some(prior) = w.at(rows, at)? {
            w.admit(1, 2 * size_of::<ProofId>() + size_of::<bool>())?;
            if *prior == id {
                return Ok(true);
            }
            w.next(&mut at)?;
        }
        Ok(false)
    }
    fn source<'a, O: ExecutionObserver>(
        &self,
        facts: &'a NativeCompilerFacts,
        id: ProofId,
        w: &mut Work<'_, '_, O>,
    ) -> R<Option<&'a NativeObligationSource>> {
        let mut at = 0;
        while let Some(source) = w.at(&facts.obligation_sources, at)? {
            w.admit(1, 2 * size_of::<ProofId>() + size_of::<bool>())?;
            if source.obligation == id {
                return Ok(Some(source));
            }
            w.next(&mut at)?;
        }
        Ok(None)
    }
}
