// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl<'a> Scratch<'a> {
    pub(super) fn monomorph<O: ExecutionObserver>(
        &mut self,
        bundle: &NativeVerificationBundle,
        fact: &'a NativeMonomorphizationFact,
        work: &mut Work,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let reference = NativeCompilerFactRef::Monomorphization(fact.id);
        if !set_insert(&mut self.mono_ids, fact.id, session, site)? {
            work.fixed_error(|| E::DuplicateMonomorphizationId(fact.id), session, site)?;
        }
        insert(&mut self.monos, fact.id, fact, session, site)?;
        if insert(
            &mut self.digests,
            fact.stable_digest,
            fact.id,
            session,
            site,
        )?
        .is_some()
        {
            work.invalid(reference, "stable_digest.duplicate", session, site)?;
        }
        if text_insert(&mut self.symbols, &fact.symbol, fact.id, session, site)?.is_some() {
            work.invalid(reference, "symbol.duplicate", session, site)?;
        }
        if !text::identity(&fact.source_item, false, session, site)? {
            work.invalid(reference, "source_item", session, site)?;
        }
        if !text::identity(&fact.symbol, false, session, site)? {
            work.invalid(reference, "symbol", session, site)?;
        }
        admit(session, site, 32, 0)?;
        if fact.stable_digest.is_zero() {
            work.invalid(reference, "stable_digest", session, site)?;
        }
        admit(session, site, 1, 0)?;
        if fact.stable_digest.algorithm != ProofDigestAlgorithm::Sha256 {
            work.invalid(reference, "stable_digest.algorithm", session, site)?;
        }
        admit(session, site, 1, 0)?;
        if let Some(function) = fact.function
            && !member(&self.functions, &function, session, site)?
        {
            work.unknown_function(reference, function, session, site)?;
        }
        for argument in &fact.generic_args {
            admit(session, site, 1, 0)?;
            let ty = match argument {
                NativeGenericArg::Ty(ty) | NativeGenericArg::Const { ty, .. } => Some(ty),
                _ => None,
            };
            if let Some(ty) = ty
                && types::contains_error(ty, session, site)?
            {
                work.invalid(reference, "generic_args[].ty", session, site)?;
            }
            if let NativeGenericArg::Const { ty, value } = argument
                && !types::constant_matches(value, ty, bundle.module.pointer_bits(), session, site)?
            {
                work.invalid(reference, "generic_args[].const", session, site)?;
            }
        }
        Ok(())
    }
}
