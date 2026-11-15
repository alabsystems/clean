// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Actual observed layout work over the table's exact borrowed module.
//! Each call owns only its scratch/data memo; it borrows the original session.
//! The ordinary Mutex memo and its statistics are not read or credited here.
//! Successful nominal layouts are shared within one query/validation call.
//! Enum layout and its least-fixpoint inhabitedness checks use actual loops.
//! Cast evidence follows the actual module-aware handle/closure/bool guards.
//! Requested storage/copy charges do not bound allocator latency or RSS.
//! Disposal of a successfully returned layout remains the caller's operation.

use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError, observed_btree,
};
use core::mem::{align_of, size_of};
use std::collections::{BTreeMap, BTreeSet};

mod aggregate;
mod cast;
mod enums;
mod equality;
mod inhabit;
mod storage;
#[cfg(test)]
mod tests;
mod walk;

use aggregate::Aggregate;

enum Error {
    Resource(ObservedValueError),
    Layout(LayoutError),
}
impl From<ObservedValueError> for Error {
    fn from(error: ObservedValueError) -> Self {
        Self::Resource(error)
    }
}
impl From<LayoutError> for Error {
    fn from(error: LayoutError) -> Self {
        Self::Layout(error)
    }
}
type R<T = ()> = Result<T, Error>;
type Key = (u8, usize);

struct Work<'s, 'o, O: ExecutionObserver> {
    session: &'s mut ObservedSession<'o, O>,
    site: ExecutionSite,
    cache: BTreeMap<Key, Arc<TyLayoutShape>>,
    enums: BTreeMap<usize, Arc<EnumLayoutShape>>,
    inhabitedness: BTreeMap<inhabit::Node, bool>,
    open: BTreeSet<Key>,
    definitions: BTreeMap<(u8, u32), usize>,
    scanned: [usize; 2],
    spans: BTreeSet<(u64, u64)>,
    value: Option<Arc<TyLayoutShape>>,
}

impl<'m> LayoutTable<'m> {
    /// Construct the actual borrowed table, observing its target-prefix scan.
    /// This grants no layout result or ABI/source/proof authority.
    pub fn new_observed<O: ExecutionObserver>(
        module: &'m Module,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<Self, ObservedValueError> {
        storage::admit(session, site, 1, size_of::<Self>())?;
        let canonical_scalars = canonical_target(module, session, site)?;
        let table = Self {
            module,
            pointer_bits: module.pointer_bits(),
            canonical_scalars,
            // No RandomState::new, HashMap::new or cold entropy/TLS setup.
            // All observed queries below own independent BTree scratch Work.
            memo: Mutex::new(None),
        };
        if let Err(stop) = storage::publication(session, site) {
            session.retirement_poll(site);
            drop(table);
            session.retirement_poll(site);
            return Err(stop);
        }
        Ok(table)
    }

    /// The original layout or its original semantic error. An outer error is
    /// a separate resource stop/unsupported constituent, never a smaller table.
    /// Queries do not populate the ordinary memo; repeated calls perform and
    /// charge their work again in the same session.
    pub fn ty_layout_observed<O: ExecutionObserver>(
        &self,
        ty: &Ty,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<Result<Arc<TyLayoutShape>, LayoutError>, ObservedValueError> {
        let mut work = Work::new(session, site)?;
        let result = work.walk(self, ty);
        work.finish(result)
    }

    /// The original full enum shape, including its normative descriptor.
    pub fn enum_layout_observed<O: ExecutionObserver>(
        &self,
        id: EnumId,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<Result<Arc<EnumLayoutShape>, LayoutError>, ObservedValueError> {
        let mut work = Work::new(session, site)?;
        let result = (|| {
            let layout = work.walk(self, &Ty::Enum(id))?;
            work.retire_layout(layout);
            work.poll()?;
            let index = work
                .definition(self, 1, id.index())?
                .ok_or(LayoutError::EnumLayoutUnavailable(id))?;
            work.lookup(work.enums.len())?;
            work.admit(1, size_of::<Arc<EnumLayoutShape>>())?;
            work.enums
                .get(&index)
                .map(Arc::clone)
                .ok_or(Error::Layout(LayoutError::EnumLayoutUnavailable(id)))
        })();
        work.finish_enum_result(result)
    }

    /// The original least-fixpoint uninhabitedness predicate, including every
    /// duplicate definition and conservative missing/cyclic references.
    pub fn ty_is_uninhabited_observed<O: ExecutionObserver>(
        &self,
        ty: &Ty,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<bool, ObservedValueError> {
        let mut work = Work::new(session, site)?;
        let result = inhabit::some(self.module, core::iter::once(ty), &mut work);
        work.finish_predicate(result)
    }

    /// Whether any field of the variant is uninhabited, under
    /// the same all-definition least solution as the original table.
    pub fn variant_is_uninhabited_observed<O: ExecutionObserver>(
        &self,
        variant: &EnumVariant,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<bool, ObservedValueError> {
        let mut work = Work::new(session, site)?;
        let result = inhabit::some(self.module, variant.fields.iter(), &mut work);
        work.finish_predicate(result)
    }

    /// Validate every tuple declaration using actual observed layout loops.
    pub fn validate_tuple_layouts_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<Result<(), LayoutError>, ObservedValueError> {
        let mut work = Work::new(session, site)?;
        let result = (|| {
            for desc in &self.module.tuple_layouts {
                work.poll()?;
                let ty = self
                    .module
                    .types
                    .get(desc.tuple_type.as_usize())
                    .ok_or(LayoutError::MissingType(desc.tuple_type))?;
                if !matches!(ty, Ty::Tuple(_)) {
                    return Err(LayoutError::TupleLayoutIncoherent(desc.tuple_type).into());
                }
                let value = work.walk(self, ty)?;
                work.retire_layout(value);
                work.poll()?;
            }
            Ok(())
        })();
        work.finish_unit(result)
    }

    /// Validate every closure declaration, including unused and duplicate rows.
    pub fn validate_closure_layouts_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<Result<(), LayoutError>, ObservedValueError> {
        let mut work = Work::new(session, site)?;
        let result = (|| {
            for desc in &self.module.closure_layouts {
                work.poll()?;
                if self
                    .module
                    .closure_types
                    .get(desc.closure.as_usize())
                    .is_none()
                {
                    return Err(LayoutError::ClosureLayoutIncoherent(desc.closure).into());
                }
                let value = work.walk(self, &Ty::Closure(desc.closure))?;
                work.retire_layout(value);
                work.poll()?;
            }
            Ok(())
        })();
        work.finish_unit(result)
    }
}

fn canonical_target<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Result<bool, ObservedValueError> {
    let Some(target) = &module.target_info else {
        return Ok(true);
    };
    let mut end = 0;
    for byte in target.triple.bytes() {
        storage::admit(session, site, 1, 0)?;
        if byte == b'-' {
            break;
        }
        end += 1;
    }
    // All following comparisons are against fixed, at most seven-byte names.
    storage::admit(session, site, 64, 0)?;
    let arch = &target.triple[..end];
    Ok(match arch {
        "x86_64" | "x64" | "aarch64" | "arm64" | "wasm64" => target.pointer_size == 8,
        "wasm32" => target.pointer_size == 4,
        arch if arch.starts_with("riscv64") => target.pointer_size == 8,
        _ => false,
    })
}

impl<'s, 'o, O: ExecutionObserver> Work<'s, 'o, O> {
    fn new(
        session: &'s mut ObservedSession<'o, O>,
        site: ExecutionSite,
    ) -> Result<Self, ObservedValueError> {
        storage::admit(session, site, 1, size_of::<Self>())?;
        Ok(Self {
            session,
            site,
            cache: BTreeMap::new(),
            enums: BTreeMap::new(),
            inhabitedness: BTreeMap::new(),
            open: BTreeSet::new(),
            definitions: BTreeMap::new(),
            scanned: [0; 2],
            spans: BTreeSet::new(),
            value: None,
        })
    }

    fn finish(
        &mut self,
        result: R<Arc<TyLayoutShape>>,
    ) -> Result<Result<Arc<TyLayoutShape>, LayoutError>, ObservedValueError> {
        self.retire_scratch();
        if storage::publication(self.session, self.site).is_err() {
            match result {
                Ok(layout) => self.retire_layout(layout),
                Err(error) => self.retire_error(error),
            }
            return Err(ObservedValueError::AdmissionRefused);
        }
        match result {
            Ok(layout) => Ok(Ok(layout)),
            Err(Error::Layout(error)) => Ok(Err(error)),
            Err(Error::Resource(error)) => Err(error),
        }
    }

    fn finish_unit(&mut self, result: R) -> Result<Result<(), LayoutError>, ObservedValueError> {
        self.retire_scratch();
        if storage::publication(self.session, self.site).is_err() {
            if let Err(error) = result {
                self.retire_error(error);
            }
            return Err(ObservedValueError::AdmissionRefused);
        }
        match result {
            Ok(()) => Ok(Ok(())),
            Err(Error::Layout(error)) => Ok(Err(error)),
            Err(Error::Resource(error)) => Err(error),
        }
    }

    fn finish_enum_result(
        &mut self,
        result: R<Arc<EnumLayoutShape>>,
    ) -> Result<Result<Arc<EnumLayoutShape>, LayoutError>, ObservedValueError> {
        self.retire_scratch();
        if storage::publication(self.session, self.site).is_err() {
            match result {
                Ok(shape) => self.retire_enum(shape),
                Err(error) => self.retire_error(error),
            }
            return Err(ObservedValueError::AdmissionRefused);
        }
        match result {
            Ok(shape) => Ok(Ok(shape)),
            Err(Error::Layout(error)) => Ok(Err(error)),
            Err(Error::Resource(error)) => Err(error),
        }
    }

    fn finish_predicate(&mut self, result: R<bool>) -> Result<bool, ObservedValueError> {
        self.retire_scratch();
        if storage::publication(self.session, self.site).is_err() {
            if let Err(error) = result {
                self.retire_error(error);
            }
            return Err(ObservedValueError::AdmissionRefused);
        }
        match result {
            Ok(answer) => Ok(answer),
            Err(Error::Resource(error)) => Err(error),
            // The inhabitedness algorithm produces no semantic LayoutError.
            // Keep a future internal contract violation nonsemantic.
            Err(error @ Error::Layout(_)) => {
                self.retire_error(error);
                self.poll()
                    .map_err(|_| ObservedValueError::AdmissionRefused)?;
                Err(ObservedValueError::UnsupportedValue)
            }
        }
    }
}
