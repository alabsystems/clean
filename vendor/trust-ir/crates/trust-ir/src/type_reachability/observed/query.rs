// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
struct Query<'a> {
    inline: Inline<'a>,
    roots: Vec<&'a Ty>,
    found: bool,
}
impl ObservedNominalTypeReachability<'_> {
    /// Exact ordinary inline query, including actual named-table bit reads.
    pub fn contains_dialect_observed<O: ExecutionObserver>(
        &self,
        ty: &Ty,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        self.contains(NominalAxis::Dialect, ty, session, site)
    }
    /// Exact ordinary handle query. A stop cannot become false or true.
    pub fn contains_handle_observed<O: ExecutionObserver>(
        &self,
        ty: &Ty,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        self.contains(NominalAxis::Handle, ty, session, site)
    }
    /// Exact ordinary callable-axis query; unrelated pointer payloads unread.
    pub fn contains_callable_observed<O: ExecutionObserver>(
        &self,
        ty: &Ty,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        self.contains(NominalAxis::Callable, ty, session, site)
    }
    /// Exact original instruction roots followed by type-valued dialect attrs.
    pub fn contains_dialect_instruction_types_observed<O: ExecutionObserver>(
        &self,
        inst: &Inst,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        self.instruction(NominalAxis::Dialect, inst, session, site)
    }
    /// Exact original instruction handle query, without SSA operand lookups.
    pub fn contains_handle_instruction_types_observed<O: ExecutionObserver>(
        &self,
        inst: &Inst,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        self.instruction(NominalAxis::Handle, inst, session, site)
    }
    fn contains<O: ExecutionObserver>(
        &self,
        axis: NominalAxis,
        ty: &Ty,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<Query<'_>>() + size_of::<Work<'_, '_, O>>())?;
        let mut query = Query {
            inline: Inline::default(),
            roots: Vec::new(),
            found: false,
        };
        let result = query.ty(self, axis, ty, &mut work);
        query.finish(result, &mut work)
    }
    fn instruction<O: ExecutionObserver>(
        &self,
        axis: NominalAxis,
        inst: &Inst,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<Query<'_>>() + size_of::<Work<'_, '_, O>>())?;
        let mut query = Query {
            inline: Inline::default(),
            roots: Vec::new(),
            found: false,
        };
        let result = query.instruction(self, axis, inst, &mut work);
        query.finish(result, &mut work)
    }
}
impl<'a> Query<'a> {
    fn ty<O: ExecutionObserver>(
        &mut self,
        summary: &ObservedNominalTypeReachability<'_>,
        axis: NominalAxis,
        ty: &'a Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.inline.start(ty, work)?;
        while let Some(child) = self.inline.next(work)? {
            work.admit(6, 2 * size_of::<bool>())?;
            let mut yes = seeds(axis, child);
            if !yes && let Some(vertex) = summary.tables.referenced(child, work)? {
                work.admit(1, size_of::<bool>())?;
                yes = *work
                    .at(&summary.reachable[axis as usize], vertex)?
                    .ok_or(ObservedValueError::InvalidRange)?;
            }
            // Original contains uses bitwise OR, so later actual occurrences
            // are still visited even after the result is known to be true.
            work.admit(1, size_of::<bool>())?;
            self.found |= yes;
        }
        Ok(())
    }
    fn instruction<O: ExecutionObserver>(
        &mut self,
        summary: &ObservedNominalTypeReachability<'_>,
        axis: NominalAxis,
        inst: &'a Inst,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Vec<&Ty>>())?;
        self.roots = inst.inline_types_observed(work.session, work.site)?;
        let mut at = 0usize;
        while let Some(root) = work.at(&self.roots, at)? {
            work.admit(1, size_of::<&Ty>())?;
            let ty = *root;
            self.ty(summary, axis, ty, work)?;
            work.next(&mut at)?;
        }
        work.admit(67, size_of::<Option<&crate::dialect::DialectInst>>())?;
        if let Inst::DialectOp(op) = inst {
            let mut at = 0usize;
            while let Some(attr) = work.at(&op.attrs, at)? {
                work.admit(7, size_of::<Option<&Ty>>())?;
                if let crate::dialect::AttrValue::Ty(ty) = &attr.value {
                    self.ty(summary, axis, ty, work)?;
                }
                work.next(&mut at)?;
            }
        }
        Ok(())
    }
    fn finish<O: ExecutionObserver>(&mut self, result: R, work: &mut Work<'_, '_, O>) -> R<bool> {
        self.inline.retire(work);
        work.retire_copy(&mut self.roots);
        result
            .and_then(|()| work.publication(size_of::<bool>()))
            .map(|()| self.found)
            .map_err(|e| work.terminal(e))
    }
}
