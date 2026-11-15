// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use crate::ty::{RecordDef, StructDef};
macro_rules! lookup {
    ($name:ident, $ty:ty) => {
        pub(super) fn $name<'a, O: ExecutionObserver>(
            rows: &'a [$ty],
            id: u32,
            w: &mut Work<'_, '_, O>,
        ) -> R<Option<&'a $ty>> {
            w.admit(1 + 2 * size_of::<u32>(), size_of::<Option<&$ty>>())?;
            if let Some(row) = rows.get(id as usize)
                && row.id.index() == id
            {
                return Ok(Some(row));
            }
            let mut remaining = rows;
            loop {
                w.admit(
                    1 + 2 * size_of::<u32>(),
                    size_of::<Option<(&$ty, &[$ty])>>(),
                )?;
                let Some((row, rest)) = remaining.split_first() else {
                    return Ok(None);
                };
                if row.id.index() == id {
                    return Ok(Some(row));
                }
                remaining = rest;
            }
        }
    };
}
lookup!(strukt, StructDef);
lookup!(enm, EnumDef);
lookup!(record, RecordDef);
