// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn blank<O: ExecutionObserver>(
    value: &str,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    let mut chars = value.chars();
    loop {
        // Prepay the WHOLE bounded UTF-8 decode (at most four bytes) plus
        // char::is_whitespace's ASCII dispatch and fixed Unicode White_Space
        // lookup. The retained scalar profile fits within64 logical steps;
        // no per-byte Unicode table traversal or physical-time bound claimed.
        admit(session, site, 64, 0)?;
        let Some(character) = chars.next() else {
            return Ok(true);
        };
        if !character.is_whitespace() {
            return Ok(false);
        }
    }
}

pub(super) fn reverse<T, O: ExecutionObserver>(
    values: &mut [T],
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R {
    let mut index = 0;
    while index < values.len() / 2 {
        // Prepay a temporary plus both destination writes for the swap.
        let bytes = size_of::<T>()
            .checked_mul(3)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        admit(session, site, 3, bytes)?;
        values.swap(index, values.len() - 1 - index);
        index += 1;
    }
    Ok(())
}

impl Checking {
    pub(super) fn begin<O: ExecutionObserver>(
        &mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        admit(session, site, 1, size_of::<E>())
    }

    pub(super) fn error<O: ExecutionObserver>(
        &mut self,
        fixed: impl FnOnce() -> E,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        // Every caller of this helper captures only fixed Copy fields or a
        // reference. No owned variable payload can drop if begin refuses.
        self.begin(session, site)?;
        self.pending = Some(fixed());
        self.commit(session, site)
    }

    pub(super) fn commit<O: ExecutionObserver>(
        &mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        reserve(&mut self.errors, session, site)?;
        admit(session, site, 1, size_of::<E>())?;
        if let Some(error) = self.pending.take() {
            self.errors.push(error);
        }
        Ok(())
    }

    pub(super) fn language_set<O: ExecutionObserver>(
        &mut self,
        source: &BTreeSet<NativeSourceLanguage>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        admit(
            session,
            site,
            observed_btree::population_work(source.len())?,
            0,
        )?;
        let target = match self.pending.as_mut() {
            Some(E::BundlePrimaryLanguageUncovered {
                source_languages, ..
            })
            | Some(E::BundleLanguageUncovered {
                source_languages, ..
            })
            | Some(E::BundleImportLanguageUncovered {
                source_languages, ..
            }) => source_languages,
            _ => return Err(ObservedValueError::UnsupportedValue),
        };
        for language in source {
            let cost = observed_btree::insertion_cost::<NativeSourceLanguage, ()>(target.len())?;
            admit(session, site, cost.work, cost.copy_bytes)?;
            admit(session, site, 1, size_of::<NativeSourceLanguage>())?;
            target.insert(*language);
        }
        Ok(())
    }

    fn retire_scratch<O: ExecutionObserver>(
        &mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        session.retirement_poll(site);
        if let Some(error) = self.pending.take() {
            retire_error(error, session, site);
        }
        while !self.functions.is_empty() {
            session.retirement_poll(site);
            if let Some((producer, mut ids)) = self.functions.pop() {
                retire_producer(producer, session, site);
                retire_ids(&mut ids, session, site);
            }
        }
        retire_value(take(&mut self.functions), session, site);
        while !self.imports.is_empty() {
            session.retirement_poll(site);
            if let Some((_, name, producer)) = self.imports.pop() {
                retire_value(name, session, site);
                retire_producer(producer, session, site);
            }
        }
        retire_value(take(&mut self.imports), session, site);
    }

    fn retire_errors<O: ExecutionObserver>(
        &mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        while !self.errors.is_empty() {
            session.retirement_poll(site);
            if let Some(error) = self.errors.pop() {
                retire_error(error, session, site);
            }
        }
        retire_value(take(&mut self.errors), session, site);
    }

    pub(super) fn finish<O: ExecutionObserver>(
        mut self,
        result: R,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        self.retire_scratch(session, site);
        if let Err(error) = result {
            self.retire_errors(session, site);
            return Err(terminal(error, session));
        }
        if let Err(error) = publication(session, site) {
            self.retire_errors(session, site);
            return Err(terminal(error, session));
        }
        Ok(take(&mut self.errors))
    }
}

fn retire_languages<O: ExecutionObserver>(
    languages: &mut BTreeSet<NativeSourceLanguage>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    while !languages.is_empty() {
        session.retirement_poll(site);
        retire_value(languages.pop_first(), session, site);
    }
    retire_value(take(languages), session, site);
}

fn retire_error<O: ExecutionObserver>(
    error: E,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    session.retirement_poll(site);
    match error {
        E::BundlePrimaryLanguageUncovered {
            mut source_languages,
            ..
        } => {
            retire_languages(&mut source_languages, session, site);
        }
        E::BundleLanguageUncovered {
            producer,
            mut functions,
            mut source_languages,
        } => {
            retire_producer(producer, session, site);
            retire_ids(&mut functions, session, site);
            retire_languages(&mut source_languages, session, site);
        }
        E::BundleImportLanguageUncovered {
            name,
            producer,
            mut source_languages,
            ..
        } => {
            retire_value(name, session, site);
            retire_producer(producer, session, site);
            retire_languages(&mut source_languages, session, site);
        }
        // The only other variants constructed in this private module contain
        // fixed digest/scalar fields and &'static str labels, never owned text.
        fixed => retire_value(fixed, session, site),
    }
    session.retirement_poll(site);
}

#[cfg(test)]
mod original_tail_tests;
