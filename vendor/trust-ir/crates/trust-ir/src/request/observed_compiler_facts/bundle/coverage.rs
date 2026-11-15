// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl Scratch<'_> {
    pub(super) fn matching_metadata<O: ExecutionObserver>(
        &self,
        source: &NativeObligationSource,
        fat: &NativeFatPointerFact,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        for reference in &source.facts {
            admit(session, site, 1, 0)?;
            let NativeCompilerFactRef::TraitObjectMetadata(id) = reference else {
                continue;
            };
            if let Some(metadata) = get(&self.metadata, id, session, site)?
                && metadata_matches(metadata, fat, session, site)?
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub(super) fn source_coverage<O: ExecutionObserver>(
        &self,
        source: &NativeObligationSource,
        work: &mut Work,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        for reference in &source.facts {
            admit(session, site, 1, 0)?;
            let NativeCompilerFactRef::TraitObjectMetadata(id) = reference else {
                continue;
            };
            let Some(metadata) = get(&self.metadata, id, session, site)? else {
                continue;
            };
            let mut found = false;
            for candidate in &source.facts {
                admit(session, site, 1, 0)?;
                let NativeCompilerFactRef::FatPointer(id) = candidate else {
                    continue;
                };
                if let Some(fat) = get(&self.fats, id, session, site)?
                    && metadata_matches(metadata, fat, session, site)?
                {
                    found = true;
                    break;
                }
            }
            if !found {
                work.fixed_error(
                    || E::ObligationSourceFactObligationMismatch {
                        obligation: source.obligation,
                        fact: *reference,
                    },
                    session,
                    site,
                )?;
            }
        }
        Ok(())
    }

    pub(super) fn bound_cast<O: ExecutionObserver>(
        &self,
        source: &NativeObligationSource,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        for reference in &source.facts {
            admit(session, site, 1, 0)?;
            let NativeCompilerFactRef::Cast(id) = reference else {
                continue;
            };
            let Some(cast) = get(&self.casts, id, session, site)? else {
                continue;
            };
            admit(session, site, 1, 0)?;
            if source.function == Some(cast.function)
                && contains(&cast.obligations, source.obligation, session, site)?
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub(super) fn bound_pointer<O: ExecutionObserver>(
        &self,
        source: &NativeObligationSource,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        for reference in &source.facts {
            admit(session, site, 1, 0)?;
            let NativeCompilerFactRef::PointerOffset(id) = reference else {
                continue;
            };
            let Some(pointer) = get(&self.pointers, id, session, site)? else {
                continue;
            };
            admit(session, site, 2, 0)?;
            if source.function == Some(pointer.function)
                && contains(&pointer.obligations, source.obligation, session, site)?
                && matches!(
                    &pointer.provenance,
                    NativePointerOffsetProvenance::SameAsBase
                )
            {
                return Ok(true);
            }
        }
        Ok(false)
    }
}

fn metadata_matches<O: ExecutionObserver>(
    metadata: &NativeTraitObjectMetadataFact,
    fat: &NativeFatPointerFact,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    if !metadata.ty.structural_eq_observed(&fat.ty, session, site)? {
        return Ok(false);
    }
    admit(session, site, 4, 0)?;
    Ok(fat.layout.metadata
        == Some(crate::PointerMetadataShape::VTable {
            trait_id: metadata.trait_id,
        }))
}
