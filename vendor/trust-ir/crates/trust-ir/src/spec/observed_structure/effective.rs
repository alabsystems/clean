// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original effective-sort selection without cloning a recursive sort.
use super::*;
#[cfg(test)]
mod tests;
impl SpecVar {
    /// Return the exact original Debug text of this variable's effective sort
    /// only when that sort contradicts `binding`. An unreadable legacy `ty`
    /// tag still has no effective sort, as in [`Self::effective_sort`]. This is
    /// diagnostic data, not evidence of a valid variable or formula binding.
    ///
    /// Selection, actual legacy parsing, recursive equality, formatting,
    /// requested storage, failed-output disposal and final publication use
    /// only the supplied original session/site. A declared sort takes priority
    /// without reading the legacy tag. No recursive owned sort is cloned.
    pub fn effective_sort_mismatch_observed<'a, O: ExecutionObserver>(
        &'a self,
        binding: &'a ClauseSort,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Option<String>> {
        let mut work = Work { session, site };
        work.admit(
            1,
            size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>() + size_of::<Option<String>>(),
        )?;
        let mut state = State::default();
        let mut pending = None;
        let result = (|| {
            let Some(sort) = sorts::effective(self, &mut work)? else {
                return Ok(());
            };
            if state.equal_sort(sort, binding, &mut work)? {
                return Ok(());
            }
            state.begin_detail(&mut work)?;
            state.sort_text(sort, &mut work)?;
            // Keep the complete returned text in custody before any later
            // scratch retirement or publication can observe cancellation.
            work.admit(1, size_of::<String>() + size_of::<Option<String>>())?;
            pending = Some(take(&mut state.detail));
            Ok(())
        })();
        state.retire_scratch(&mut work);
        retirement::consume_vec(take(&mut state.errors), &mut work);
        match result.and_then(|()| work.publication(1, size_of::<Option<String>>())) {
            Ok(()) => Ok(pending),
            Err(error) => {
                work.step(size_of::<Option<String>>().saturating_add(1));
                if let Some(mut text) = pending.take() {
                    work.retire_text(&mut text);
                }
                work.poll();
                Err(work.terminal(error))
            }
        }
    }
}
// Successful caller-owned text/input disposal and physical std/allocator/
// deallocator/OOM/panic/unwind/RSS/machine-work/hardtime remain OPEN. No owner,
// grant, deadline, TLS or fuel is created or renewed here.
