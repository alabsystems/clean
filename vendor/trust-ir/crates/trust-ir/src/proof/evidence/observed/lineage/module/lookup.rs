// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State {
    pub(super) fn module_symbol<O: ExecutionObserver>(
        &mut self,
        id: crate::FuncId,
        module: &Module,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        w.admit(1, size_of::<usize>())?;
        if let Some(function) = w.at(&module.functions, id.as_usize())? {
            w.admit(1, 2 * size_of::<crate::FuncId>() + size_of::<bool>())?;
            if function.id == id {
                self.blob(function.name.as_bytes(), w)?;
                return Ok(true);
            }
        }
        let mut at = 0;
        while let Some(function) = w.at(&module.functions, at)? {
            w.admit(1, 2 * size_of::<crate::FuncId>() + size_of::<bool>())?;
            if function.id == id {
                self.blob(function.name.as_bytes(), w)?;
                return Ok(true);
            }
            w.next(&mut at)?;
        }
        Ok(false)
    }
}
