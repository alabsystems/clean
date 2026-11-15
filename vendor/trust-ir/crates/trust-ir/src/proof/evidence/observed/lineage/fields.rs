// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use crate::proof::{
    ClauseBinding, ClausePlace, ObligationKind, ProofFormula, ProofObligationSourceIdentity,
};
#[derive(Clone, Copy)]
pub(super) enum FormulaBindings {
    Included,
    Tail,
}
impl State {
    pub(super) fn kind<O: ExecutionObserver>(
        &mut self,
        value: &ObligationKind,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        // Closed tag projection only; Custom's entire variable content follows.
        w.admit(32, size_of::<u8>())?;
        self.u8(super::super::super::obligation_kind_tag(value), w)?;
        if let ObligationKind::Custom { namespace, name } = value {
            self.blob(namespace.as_bytes(), w)?;
            self.blob(name.as_bytes(), w)?;
        }
        Ok(())
    }
    pub(super) fn formula<O: ExecutionObserver>(
        &mut self,
        value: Option<&ProofFormula>,
        bindings: FormulaBindings,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.u8(u8::from(value.is_some()), w)?;
        if let Some(f) = value {
            self.blob(f.schema.as_bytes(), w)?;
            self.blob(f.payload.as_bytes(), w)?;
            for text in [f.smtlib.as_deref(), f.sort.as_deref()] {
                self.u8(u8::from(text.is_some()), w)?;
                if let Some(text) = text {
                    self.blob(text.as_bytes(), w)?;
                }
            }
            if matches!(bindings, FormulaBindings::Included) {
                self.clauses(&f.bindings, w)?;
            }
        }
        Ok(())
    }
    pub(super) fn source<O: ExecutionObserver>(
        &mut self,
        value: Option<&ProofObligationSourceIdentity>,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.u8(u8::from(value.is_some()), w)?;
        if let Some(source) = value {
            self.blob(source.source_id.as_bytes(), w)?;
            self.blob(source.assertion_id.as_bytes(), w)?;
            self.u8(u8::from(source.range.is_some()), w)?;
            if let Some(r) = source.range {
                for n in [r.file, r.start_line, r.start_col, r.end_line, r.end_col] {
                    self.u32(n, w)?;
                }
            }
            self.u8(u8::from(source.public.is_some()), w)?;
            if let Some(public) = &source.public {
                self.blob(public.obligation_id.as_bytes(), w)?;
                self.digest_bytes(&public.semantic_digest, w)?;
            }
        }
        Ok(())
    }
    pub(super) fn clauses<O: ExecutionObserver>(
        &mut self,
        rows: &[(String, ClauseBinding)],
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.length(rows.len(), w)?;
        let mut at = 0;
        while let Some((name, binding)) = w.at(rows, at)? {
            self.blob(name.as_bytes(), w)?;
            self.sort(&binding.sort, w)?;
            self.place(&binding.place, w)?;
            w.next(&mut at)?;
        }
        Ok(())
    }
    fn place<O: ExecutionObserver>(&mut self, value: &ClausePlace, w: &mut Work<'_, '_, O>) -> R {
        w.admit(32, size_of::<Option<u32>>())?;
        let (tag, index) = match value {
            ClausePlace::Param { index } => (0, Some(*index)),
            ClausePlace::ResultSlot { index } => (1, Some(*index)),
            ClausePlace::MutParamExit { index } => (2, Some(*index)),
            ClausePlace::World => (3, None),
            ClausePlace::Unwind => (4, None),
            ClausePlace::Value(v) => (5, Some(v.index())),
            ClausePlace::SpecVar { index } => (6, Some(*index)),
            ClausePlace::SpecVarNext { index } => (7, Some(*index)),
            ClausePlace::WorldPre => (8, None),
            ClausePlace::WorldPost => (9, None),
            ClausePlace::ParamPointeeEntry { index } => (10, Some(*index)),
        };
        self.u8(tag, w)?;
        if let Some(index) = index {
            self.u32(index, w)?;
        }
        Ok(())
    }
}
