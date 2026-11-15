// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact compiler-fact diagnostics under the caller's original custody.
//! This constituent does not validate a whole bundle or confer authority.

use super::{
    NativeAdtLayoutFact, NativeCastFact, NativeCompilerFactId, NativeCompilerFactRef,
    NativeEnumLayoutFact, NativeEnumTagEncoding, NativeFatPointerFact, NativeGenericArg,
    NativeMonomorphizationFact, NativeMonomorphizationId, NativeObligationCause,
    NativeObligationSource, NativePointerOffsetFact, NativePointerOffsetProvenance,
    NativeRequestId, NativeTraitObjectMetadataFact, NativeVerificationBundle,
    NativeVerificationBundleError as E,
};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError, observed_btree,
};
use crate::{
    CastLayoutEvidence, Constant, EnumDef, FieldOffsetShape, FuncId, Function, Inst, InstrNode,
    LayoutError, LayoutTable, Module, ProofDigest, ProofDigestAlgorithm, ProofId, SourceSpan, Ty,
    TyLayoutKind, TyLayoutShape, ValueId,
};
use core::mem::{size_of, take};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

mod bundle;
mod casts;
mod native_enum;
mod pointer;
mod retirement;
mod storage;
#[cfg(test)]
mod tests;
mod trait_object;
mod values;
use storage::*;

type R<T = ()> = Result<T, ObservedValueError>;

#[derive(Default)]
struct Work {
    errors: Vec<E>,
    pending: Option<E>,
    layout: Option<Arc<TyLayoutShape>>,
    layout_error: Option<LayoutError>,
    owned_ty: Option<Ty>,
    cast_evidence: Option<CastLayoutEvidence>,
    first_text: String,
    second_text: String,
    seen_variants: BTreeSet<u32>,
    discriminants: BTreeSet<i128>,
}

impl NativeAdtLayoutFact {
    /// The ordinary ADT helper's complete ordered diagnostics, using the
    /// supplied table's exact borrowed module and original session/site.
    /// Struct layout queries are observed. Enum facts retain the ordinary
    /// supplied-evidence shape checks, without an extra derived enum query.
    /// Other fact families, ID uniqueness, bundle validity and successful
    /// caller-owned diagnostic disposal remain outside this constituent.
    pub fn validation_errors_observed<O: ExecutionObserver>(
        &self,
        layouts: &LayoutTable<'_>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        let mut work = Work::new(session, site)?;
        let result = work.adt(layouts, self, session, site);
        work.finish(result, session, site)
    }
}

impl NativeEnumLayoutFact {
    /// The ordinary supplied enum-layout helper only, against this exact
    /// `enum_def` and enclosing `fact`. Preserves its tag-strategy early
    /// returns and diagnostics; this does not authenticate either input.
    pub fn validation_errors_observed<O: ExecutionObserver>(
        &self,
        fact: &NativeAdtLayoutFact,
        enum_def: &EnumDef,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        let mut work = Work::new(session, site)?;
        let result = work.native_enum(fact, self, enum_def, session, site);
        work.finish(result, session, site)
    }
}

impl NativeFatPointerFact {
    /// The ordinary fat-pointer helper's diagnostics only. The reviewed
    /// pointer-shape operation inspects fixed discriminants/IDs and target
    /// width; it never traverses or clones an inline pointee type.
    pub fn validation_errors_observed<O: ExecutionObserver>(
        &self,
        module: &Module,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        let mut work = Work::new(session, site)?;
        let result = work.fat_pointer(module, self, session, site);
        work.finish(result, session, site)
    }
}

impl Work {
    fn fat_pointer<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        fact: &NativeFatPointerFact,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        admit(
            session,
            site,
            32,
            size_of::<Option<crate::PointerLayoutShape>>(),
        )?;
        match fact.ty.pointer_layout_shape(module.pointer_bits()) {
            Some(expected) if expected == fact.layout && expected.is_fat() => Ok(()),
            Some(_) => self.invalid(
                NativeCompilerFactRef::FatPointer(fact.id),
                "layout",
                session,
                site,
            ),
            None => self.invalid(
                NativeCompilerFactRef::FatPointer(fact.id),
                "ty",
                session,
                site,
            ),
        }
    }

    fn new<O: ExecutionObserver>(
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Self> {
        admit(session, site, 1, size_of::<Self>())?;
        Ok(Self::default())
    }

    fn invalid<O: ExecutionObserver>(
        &mut self,
        fact: NativeCompilerFactRef,
        field: &'static str,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        self.fixed_error(|| E::InvalidCompilerFact { fact, field }, session, site)
    }

    fn fixed_error<O: ExecutionObserver>(
        &mut self,
        build: impl FnOnce() -> E,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        admit(session, site, 1, size_of::<E>())?;
        // All call sites capture fixed IDs/labels, never owned variable data.
        self.pending = Some(build());
        self.push_pending(session, site)
    }

    fn push_pending<O: ExecutionObserver>(
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

    fn adt<O: ExecutionObserver>(
        &mut self,
        layouts: &LayoutTable<'_>,
        fact: &NativeAdtLayoutFact,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        admit(session, site, 4, 0)?;
        let module = layouts.module();
        let reference = NativeCompilerFactRef::AdtLayout(fact.id);
        match (&fact.ty, &fact.layout.kind) {
            (Ty::Struct(id), TyLayoutKind::Struct { id: layout_id, .. }) if id == layout_id => {
                let mut exists = false;
                let mut index = 0;
                while index < module.structs.len() {
                    admit(session, site, 1, 0)?;
                    if module.structs[index].id == *id {
                        exists = true;
                        break;
                    }
                    index += 1;
                }
                if !exists {
                    self.invalid(reference, "ty.struct_id", session, site)?;
                }
                match layouts.ty_layout_observed(&fact.ty, session, site)? {
                    Ok(layout) => self.layout = Some(layout),
                    Err(error) => self.layout_error = Some(error),
                }
                if let Some(layout) = &self.layout {
                    if !struct_layout_equal(layout, &fact.layout, session, site)? {
                        self.invalid(reference, "layout", session, site)?;
                    }
                } else {
                    admit(session, site, 1, 0)?;
                    if !matches!(&self.layout_error, Some(LayoutError::MissingStruct(_))) {
                        self.invalid(reference, "layout", session, site)?;
                    }
                }
                admit(session, site, 1, 0)?;
                if fact.enum_layout.is_some() {
                    self.invalid(reference, "enum_layout", session, site)?;
                }
            }
            (
                Ty::Enum(id),
                TyLayoutKind::Enum {
                    id: layout_id,
                    variants,
                },
            ) if id == layout_id => {
                let mut definition = None;
                let mut index = 0;
                while index < module.enums.len() {
                    admit(session, site, 1, 0)?;
                    if module.enums[index].id == *id {
                        definition = Some(&module.enums[index]);
                        break;
                    }
                    index += 1;
                }
                let Some(definition) = definition else {
                    return self.invalid(reference, "ty.enum_id", session, site);
                };
                admit(session, site, 1, 0)?;
                if *variants != definition.variants.len() {
                    self.invalid(reference, "layout.kind.variants", session, site)?;
                }
                admit(session, site, 1, 0)?;
                let Some(layout) = &fact.enum_layout else {
                    return self.invalid(reference, "enum_layout", session, site);
                };
                admit(session, site, 1, 0)?;
                if layout.enum_id != *id {
                    self.invalid(reference, "enum_layout.enum_id", session, site)?;
                }
                admit(session, site, 1, 0)?;
                if layout.variants.len() != definition.variants.len() {
                    self.invalid(reference, "enum_layout.variants", session, site)?;
                }
                self.native_enum(fact, layout, definition, session, site)?;
            }
            (Ty::Struct(_), _) | (Ty::Enum(_), _) => {
                self.invalid(reference, "layout.kind", session, site)?
            }
            _ => self.invalid(reference, "ty", session, site)?,
        }
        Ok(())
    }
}
