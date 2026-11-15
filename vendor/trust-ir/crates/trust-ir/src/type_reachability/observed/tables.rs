// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[derive(Clone, Copy, Default)]
pub(super) struct Bounds {
    pub(super) start: usize,
    pub(super) len: usize,
}
#[derive(Default)]
pub(super) struct Tables {
    pub(super) types: Bounds,
    pub(super) func_types: Bounds,
    pub(super) closure_types: Bounds,
    pub(super) structs: Vec<(u32, usize)>,
    pub(super) enums: Vec<(u32, usize)>,
    pub(super) records: Vec<(u32, usize)>,
}
impl Tables {
    pub(super) fn named<O: ExecutionObserver>(
        rows: &[(u32, usize)],
        id: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<usize>> {
        let mut at = 0usize;
        while let Some(row) = work.at(rows, at)? {
            work.admit(1, size_of::<(u32, usize)>())?;
            if row.0 == id {
                return Ok(Some(row.1));
            }
            work.next(&mut at)?;
        }
        Ok(None)
    }
    pub(super) fn bounded<O: ExecutionObserver>(
        bounds: Bounds,
        index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<usize>> {
        work.admit(2, size_of::<Option<usize>>())?;
        if index < bounds.len {
            Ok(Some(work.add(bounds.start, index)?))
        } else {
            Ok(None)
        }
    }
    pub(super) fn referenced<O: ExecutionObserver>(
        &self,
        ty: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<usize>> {
        // table_referent is the actual exhaustive, fixed-size Ty-tag/ID
        // projection; it does not traverse any Ty payload or source table.
        work.admit(
            42,
            size_of::<Option<TableReferent>>() + 2 * size_of::<Bounds>(),
        )?;
        match table_referent(ty) {
            None => Ok(None),
            Some(TableReferent::Ty(i)) => Self::bounded(self.types, i, work),
            Some(TableReferent::FuncTy(i)) => Self::bounded(self.func_types, i, work),
            Some(TableReferent::ClosureTy(i)) => Self::bounded(self.closure_types, i, work),
            Some(TableReferent::Struct(id)) => Self::named(&self.structs, id, work),
            Some(TableReferent::Enum(id)) => Self::named(&self.enums, id, work),
            Some(TableReferent::Record(id)) => Self::named(&self.records, id, work),
        }
    }
}
