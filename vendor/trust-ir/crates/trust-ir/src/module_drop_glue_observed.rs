// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Borrowed actual drop-glue table lookup; no Ty clones or unobserved hashing.
use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
type R<T> = Result<T, ObservedValueError>;
#[cfg(test)]
mod tests;

/// A lookup over one exact immutable module. This deliberately uses a linear
/// observed scan instead of cloning recursive Ty keys into a standard HashMap.
/// It establishes no type/layout validity or source/proof authority.
#[derive(Debug)]
pub struct ObservedDropGlueIndex<'m> {
    module: &'m Module,
}
impl Module {
    pub fn drop_glue_index_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<ObservedDropGlueIndex<'_>> {
        admit(
            session,
            site,
            1,
            core::mem::size_of::<ObservedDropGlueIndex<'_>>(),
        )?;
        let index = ObservedDropGlueIndex { module: self };
        publication(session, site)?;
        Ok(index)
    }
}
impl<'m> ObservedDropGlueIndex<'m> {
    /// Exact source identity; no alternate entry slice can be substituted.
    pub fn source_module(&self) -> &'m Module {
        self.module
    }
    /// Same unresolved/unique/ambiguous answer as the ordinary drop-glue index.
    /// Each actual candidate and structural equality observes the same caller
    /// operation. Successful scratch disposal occurs before an answer escapes.
    pub fn resolve<O: ExecutionObserver>(
        &self,
        ty: &Ty,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<DropResolution> {
        let mut result = DropResolution::Unresolved;
        for entry in &self.module.drop_glue {
            admit(session, site, 1, 0)?;
            if entry.ty.structural_eq_observed(ty, session, site)? {
                result = match result {
                    DropResolution::Unresolved => DropResolution::Resolved(entry.glue),
                    DropResolution::Resolved(_) | DropResolution::Ambiguous => {
                        DropResolution::Ambiguous
                    }
                };
            }
        }
        publication(session, site)?;
        Ok(result)
    }
    pub fn is_glue<O: ExecutionObserver>(
        &self,
        function: FuncId,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        for entry in &self.module.drop_glue {
            admit(session, site, 1, 0)?;
            if entry.glue == function {
                publication(session, site)?;
                return Ok(true);
            }
        }
        publication(session, site)?;
        Ok(false)
    }
    pub fn is_empty<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        admit(session, site, 1, 0)?;
        let empty = self.module.drop_glue.is_empty();
        publication(session, site)?;
        Ok(empty)
    }
}
fn admit<O: ExecutionObserver>(
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    work: usize,
    copy_bytes: usize,
) -> Result<(), ObservedValueError> {
    session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::DropGlueIndex,
            site,
            work,
            copy_bytes,
        })
        .map_err(Into::into)
}
fn publication<O: ExecutionObserver>(
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Result<(), ObservedValueError> {
    session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site,
            work: 0,
            copy_bytes: 0,
        })
        .map_err(Into::into)
}
