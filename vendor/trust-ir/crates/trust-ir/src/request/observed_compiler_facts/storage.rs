// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn admit<O: ExecutionObserver>(
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    work: usize,
    copy_bytes: usize,
) -> R {
    session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work,
            copy_bytes,
        })
        .map_err(Into::into)
}

pub(super) fn reserve<T, O: ExecutionObserver>(
    values: &mut Vec<T>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R {
    admit(session, site, 1, 0)?;
    if values.len() == values.capacity() {
        let requested = values
            .len()
            .checked_mul(2)
            .and_then(|n| n.checked_add(1))
            .ok_or(ObservedValueError::CapacityOverflow)?;
        let work = requested
            .checked_add(values.len())
            .ok_or(ObservedValueError::CapacityOverflow)?;
        let bytes = work
            .checked_mul(size_of::<T>())
            .ok_or(ObservedValueError::CapacityOverflow)?;
        admit(session, site, work, bytes)?;
        values
            .try_reserve_exact(requested - values.len())
            .map_err(|_| ObservedValueError::AllocationFailed)?;
    }
    Ok(())
}

pub(super) fn set_insert<K: Copy + Ord, O: ExecutionObserver>(
    set: &mut BTreeSet<K>,
    key: K,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    admit(
        session,
        site,
        observed_btree::population_work(set.len())?,
        0,
    )?;
    if set.contains(&key) {
        return Ok(false);
    }
    let cost = observed_btree::insertion_cost::<K, ()>(set.len())?;
    admit(session, site, cost.work, cost.copy_bytes)?;
    admit(session, site, 1, size_of::<K>())?;
    Ok(set.insert(key))
}

pub(super) fn text_equal<O: ExecutionObserver>(
    a: &str,
    b: &str,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    admit(session, site, 1, 0)?;
    if a.len() != b.len() {
        return Ok(false);
    }
    for (a, b) in a.as_bytes().chunks(1024).zip(b.as_bytes().chunks(1024)) {
        admit(
            session,
            site,
            a.len()
                .checked_add(b.len())
                .ok_or(ObservedValueError::CapacityOverflow)?,
            0,
        )?;
        if a != b {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(super) fn struct_layout_equal<O: ExecutionObserver>(
    a: &TyLayoutShape,
    b: &TyLayoutShape,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    layout_equal(a, b, session, site)
}

pub(super) fn layout_equal<O: ExecutionObserver>(
    a: &TyLayoutShape,
    b: &TyLayoutShape,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    admit(session, site, 4, 0)?;
    if a.size_bits != b.size_bits || a.align_bits != b.align_bits {
        return Ok(false);
    }
    match (&a.kind, &b.kind) {
        (
            TyLayoutKind::Struct {
                id: a_id,
                fields: a,
            },
            TyLayoutKind::Struct {
                id: b_id,
                fields: b,
            },
        ) => {
            if a_id != b_id || a.len() != b.len() {
                return Ok(false);
            }
            fields_equal(a, b, session, site)
        }
        (TyLayoutKind::Tuple { fields: a }, TyLayoutKind::Tuple { fields: b }) => {
            fields_equal(a, b, session, site)
        }
        (
            TyLayoutKind::Closure {
                id: a_id,
                captures: a,
            },
            TyLayoutKind::Closure {
                id: b_id,
                captures: b,
            },
        ) => {
            if a_id != b_id {
                return Ok(false);
            }
            fields_equal(a, b, session, site)
        }
        (TyLayoutKind::Scalar(a), TyLayoutKind::Scalar(b)) => Ok(a == b),
        (TyLayoutKind::ThinPointer, TyLayoutKind::ThinPointer)
        | (TyLayoutKind::Unit, TyLayoutKind::Unit)
        | (TyLayoutKind::Never, TyLayoutKind::Never) => Ok(true),
        (TyLayoutKind::FatPointer(a), TyLayoutKind::FatPointer(b)) => Ok(a == b),
        (TyLayoutKind::Enum { id: a, variants: n }, TyLayoutKind::Enum { id: b, variants: m }) => {
            Ok(a == b && n == m)
        }
        (
            TyLayoutKind::Array {
                elem: a,
                len: n,
                stride_bits: x,
            },
            TyLayoutKind::Array {
                elem: b,
                len: m,
                stride_bits: y,
            },
        ) => Ok(a == b && n == m && x == y),
        (
            TyLayoutKind::Vector {
                elem_shape: a,
                lanes: n,
                lane_bits: x,
            },
            TyLayoutKind::Vector {
                elem_shape: b,
                lanes: m,
                lane_bits: y,
            },
        ) => Ok(a == b && n == m && x == y),
        _ => Ok(false),
    }
}

fn fields_equal<O: ExecutionObserver>(
    a: &[FieldOffsetShape],
    b: &[FieldOffsetShape],
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    admit(session, site, 1, 0)?;
    if a.len() != b.len() {
        return Ok(false);
    }
    let mut index = 0;
    while index < a.len() {
        admit(session, site, 2, 0)?;
        let (a, b) = (&a[index], &b[index]);
        if a.field != b.field || !text_equal(&a.name, &b.name, session, site)? {
            return Ok(false);
        }
        admit(session, site, 2, 0)?;
        if a.ty_shape != b.ty_shape || a.offset_bits != b.offset_bits {
            return Ok(false);
        }
        index += 1;
    }
    Ok(true)
}

pub(super) fn member<K: Ord, O: ExecutionObserver>(
    values: &BTreeSet<K>,
    key: &K,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    // Every call site uses a fixed Copy FuncId or ProofId key.
    admit(
        session,
        site,
        observed_btree::population_work(values.len())?,
        0,
    )?;
    Ok(values.contains(key))
}

pub(super) fn blank<O: ExecutionObserver>(
    value: &str,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    let mut chars = value.chars();
    loop {
        admit(session, site, 8, 0)?;
        let Some(character) = chars.next() else {
            return Ok(true);
        };
        if !character.is_whitespace() {
            return Ok(false);
        }
    }
}

impl Work {
    pub(super) fn unknown_function<O: ExecutionObserver>(
        &mut self,
        fact: NativeCompilerFactRef,
        function: FuncId,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        self.fixed_error(
            || E::UnknownCompilerFactFunction { fact, function },
            session,
            site,
        )
    }

    pub(super) fn obligations<O: ExecutionObserver>(
        &mut self,
        fact: NativeCompilerFactRef,
        obligations: &[ProofId],
        known: &BTreeSet<ProofId>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut index = 0;
        while index < obligations.len() {
            admit(session, site, 1, 0)?;
            let obligation = obligations[index];
            if !member(known, &obligation, session, site)? {
                self.fixed_error(
                    || E::UnknownCompilerFactObligation { fact, obligation },
                    session,
                    site,
                )?;
            }
            index += 1;
        }
        Ok(())
    }
}
