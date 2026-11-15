// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl Render {
    /// Preserve actual Module::function_by_id: indexed slot PLUS ID first,
    /// then FIRST matching physical fallback, including sparse/malformed IDs.
    pub(super) fn lookup<'m, O: ExecutionObserver>(
        m: &'m Module,
        id: FuncId,
        w: &mut Work<'_, '_, O>,
    ) -> R<Option<&'m Function>> {
        w.admit(1, size_of::<usize>() + size_of::<FuncId>())?;
        if let Some(f) = w.at(&m.functions, id.index() as usize)? {
            w.admit(1, 2 * size_of::<FuncId>() + size_of::<bool>())?;
            if f.id == id {
                return Ok(Some(f));
            }
        }
        let mut at = 0;
        while let Some(f) = w.at(&m.functions, at)? {
            w.admit(1, 2 * size_of::<FuncId>() + size_of::<bool>())?;
            if f.id == id {
                return Ok(Some(f));
            }
            w.next(&mut at)?;
        }
        Ok(None)
    }
}
