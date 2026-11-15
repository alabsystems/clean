// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[cfg(test)]
mod tests;

fn flat<T, O: ExecutionObserver>(
    value: T,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    session.retirement_step(site, 1);
    drop(value);
    session.retirement_step(site, 1);
}

fn error<O: ExecutionObserver>(
    value: E,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    session.retirement_step(site, 1);
    match value {
        E::DuplicatePublicObligationSource {
            public_obligation_id,
            ..
        } => flat(public_obligation_id, session, site),
        E::EmbeddedPublicObligationIdMismatch {
            expected, actual, ..
        } => {
            flat(expected, session, site);
            flat(actual, session, site);
        }
        fixed => flat(fixed, session, site),
    }
    session.retirement_step(site, 1);
}

fn fields<O: ExecutionObserver>(
    mut values: Vec<FieldOffsetShape>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    while !values.is_empty() {
        session.retirement_step(site, 1);
        if let Some(value) = values.pop() {
            flat(value.name, session, site);
        }
    }
    flat(values, session, site);
}

fn layout<O: ExecutionObserver>(
    value: Arc<TyLayoutShape>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    session.retirement_step(site, 1);
    // into_inner atomically relinquishes a shared reference without a
    // try_unwrap-failure/drop race becoming the final recursive owner.
    if let Some(value) = Arc::into_inner(value) {
        match value.kind {
            TyLayoutKind::Struct { fields: values, .. }
            | TyLayoutKind::Tuple { fields: values }
            | TyLayoutKind::Closure {
                captures: values, ..
            } => fields(values, session, site),
            fixed => flat(fixed, session, site),
        }
    }
    session.retirement_step(site, 1);
}

fn tree<K: Copy + Ord, O: ExecutionObserver>(
    values: &mut BTreeSet<K>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    while !values.is_empty() {
        session.retirement_step(site, values.len().saturating_add(1));
        flat(values.pop_first(), session, site);
    }
    flat(take(values), session, site);
}

impl Work {
    pub(super) fn retire_owned_ty<O: ExecutionObserver>(
        &mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        session.retirement_step(site, 1);
        if let Some(ty) = self.owned_ty.take() {
            crate::ty::retire_ty_observed(ty, session, site);
        }
        session.retirement_step(site, 1);
    }

    fn retire_scratch<O: ExecutionObserver>(
        &mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        session.retirement_step(site, 1);
        if let Some(value) = self.pending.take() {
            error(value, session, site);
        }
        flat(take(&mut self.first_text), session, site);
        flat(take(&mut self.second_text), session, site);
        self.retire_owned_ty(session, site);
        if let Some(value) = self.cast_evidence.take() {
            flat(value, session, site);
        }
        if let Some(value) = self.layout.take() {
            layout(value, session, site);
        }
        if let Some(error) = self.layout_error.take() {
            match error {
                LayoutError::TargetScalarLayoutUnavailable { triple } => {
                    flat(triple, session, site)
                }
                fixed => flat(fixed, session, site),
            }
        }
        tree(&mut self.seen_variants, session, site);
        tree(&mut self.discriminants, session, site);
    }

    fn retire_errors<O: ExecutionObserver>(
        &mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        // Only the two explicit public-ID variants carry owned strings. All
        // other variants this builder emits contain fixed IDs/static labels.
        while !self.errors.is_empty() {
            session.retirement_step(site, 1);
            if let Some(value) = self.errors.pop() {
                error(value, session, site);
            }
        }
        flat(take(&mut self.errors), session, site);
    }

    pub(super) fn finish_component<O: ExecutionObserver>(
        &mut self,
        result: R,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        self.retire_scratch(session, site);
        result?;
        // A refusal during retirement must stop before the next fact.
        admit(session, site, 1, 0)
    }

    pub(super) fn finish<O: ExecutionObserver>(
        mut self,
        result: R,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        self.retire_scratch(session, site);
        let result = result.and_then(|()| {
            session
                .admit(ExecutionProgress {
                    phase: ExecutionPhase::Publication,
                    site,
                    work: 0,
                    copy_bytes: 0,
                })
                .map_err(Into::into)
        });
        match result {
            Ok(()) => Ok(take(&mut self.errors)),
            Err(error) => {
                self.retire_errors(session, site);
                Err(if session.first_refusal().is_some() {
                    ObservedValueError::AdmissionRefused
                } else {
                    error
                })
            }
        }
    }
}
