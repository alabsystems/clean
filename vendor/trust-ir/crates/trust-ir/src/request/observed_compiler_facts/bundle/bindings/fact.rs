// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl Scratch<'_> {
    pub(super) fn fact_binding<O: ExecutionObserver>(
        &self,
        source: &NativeObligationSource,
        reference: NativeCompilerFactRef,
        work: &mut Work,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        admit(session, site, 1, 0)?;
        match reference {
            NativeCompilerFactRef::FatPointer(id) => {
                if let Some(fat) = get(&self.fats, &id, session, site)? {
                    admit(session, site, 2, 0)?;
                    if matches!(
                        (&fat.ty, fat.layout.metadata),
                        (
                            Ty::FatPtr(crate::FatPtrKind::TraitObject { .. }),
                            Some(crate::PointerMetadataShape::VTable { .. })
                        )
                    ) && !self.matching_metadata(source, fat, session, site)?
                    {
                        work.fixed_error(
                            || E::MissingObligationSourceTraitObjectMetadataFact {
                                obligation: source.obligation,
                                fat_pointer: id,
                            },
                            session,
                            site,
                        )?;
                    }
                }
            }
            NativeCompilerFactRef::TraitObjectMetadata(id) => {
                if let Some(metadata) = get(&self.metadata, &id, session, site)? {
                    admit(session, site, 1, 0)?;
                    if let Some(function) = metadata.function {
                        work.fact_function(source, reference, Some(function), session, site)?;
                    }
                    obligation_binding(
                        work,
                        source,
                        reference,
                        &metadata.obligations,
                        session,
                        site,
                    )?;
                }
            }
            NativeCompilerFactRef::PointerOffset(id) => {
                if let Some(pointer) = get(&self.pointers, &id, session, site)? {
                    work.fact_function(source, reference, Some(pointer.function), session, site)?;
                    obligation_binding(
                        work,
                        source,
                        reference,
                        &pointer.obligations,
                        session,
                        site,
                    )?;
                    admit(session, site, 1, 0)?;
                    if matches!(
                        &pointer.provenance,
                        NativePointerOffsetProvenance::Unsupported(_)
                    ) {
                        work.invalid(reference, "provenance", session, site)?;
                    }
                }
            }
            NativeCompilerFactRef::Cast(id) => {
                if let Some(cast) = get(&self.casts, &id, session, site)? {
                    work.fact_function(source, reference, Some(cast.function), session, site)?;
                    obligation_binding(work, source, reference, &cast.obligations, session, site)?;
                }
            }
            NativeCompilerFactRef::Monomorphization(id) if source.monomorphization != Some(id) => {
                if let Some(mono) = get(&self.monos, &id, session, site)? {
                    work.fact_function(source, reference, mono.function, session, site)?;
                }
            }
            NativeCompilerFactRef::AdtLayout(_) | NativeCompilerFactRef::Monomorphization(_) => {}
        }
        Ok(())
    }
}

fn obligation_binding<O: ExecutionObserver>(
    work: &mut Work,
    source: &NativeObligationSource,
    reference: NativeCompilerFactRef,
    obligations: &[ProofId],
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R {
    if !contains(obligations, source.obligation, session, site)? {
        work.fixed_error(
            || E::ObligationSourceFactObligationMismatch {
                obligation: source.obligation,
                fact: reference,
            },
            session,
            site,
        )?;
    }
    Ok(())
}
