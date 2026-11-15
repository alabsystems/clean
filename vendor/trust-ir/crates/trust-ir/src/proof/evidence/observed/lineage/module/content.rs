// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State {
    pub(super) fn module_content<O: ExecutionObserver>(
        &mut self,
        row: &ProofObligation,
        module: &Module,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        // Same complete ordinary v8 recipe; every variable field encoder is
        // the existing actual shared implementation, not a mirrored codec.
        self.kind(&row.kind, w)?;
        self.blob(row.description.as_bytes(), w)?;
        self.formula(row.formula.as_ref(), FormulaBindings::Included, w)?;
        self.u8(u8::from(row.function.is_some()), w)?;
        if let Some(function) = row.function
            && !self.module_symbol(function, module, w)?
        {
            return Ok(false);
        }
        self.source(row.source.as_ref(), w)?;
        self.u8(u8::from(row.site.is_some()), w)?;
        if let Some(site) = row.site {
            if !self.module_symbol(site.function, module, w)? {
                return Ok(false);
            }
            self.u32(site.block.index(), w)?;
            self.u32(site.inst_index, w)?;
        }
        self.u8(u8::from(row.spec.is_some()), w)?;
        if let Some(spec) = &row.spec {
            self.blob(spec.machine.as_bytes(), w)?;
            self.blob(spec.temporal.as_bytes(), w)?;
        }
        Ok(true)
    }
}
