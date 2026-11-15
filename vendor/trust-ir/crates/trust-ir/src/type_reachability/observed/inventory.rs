// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'m> State<'m> {
    pub(super) fn construct<O: ExecutionObserver>(
        &mut self,
        module: &'m Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.prepare(module, work)?;
        self.inventory(module, work)?;
        self.solve(work)
    }
    pub(super) fn record_type<O: ExecutionObserver>(
        &mut self,
        owner: usize,
        ty: &'m Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.inline.start(ty, work)?;
        while let Some(child) = self.inline.next(work)? {
            for axis in AXES {
                work.admit(6, size_of::<NominalAxis>() + size_of::<bool>())?;
                if seeds(axis, child) {
                    self.mark(axis, owner, work)?;
                }
            }
            if let Some(target) = self.summary.tables.referenced(child, work)? {
                self.dependency(owner, target, work)?;
            }
        }
        Ok(())
    }
    fn types<O: ExecutionObserver>(
        &mut self,
        owner: usize,
        types: &'m [Ty],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0usize;
        while let Some(ty) = work.at(types, at)? {
            self.record_type(owner, ty, work)?;
            work.next(&mut at)?;
        }
        Ok(())
    }
    fn fields<O: ExecutionObserver>(
        &mut self,
        owner: usize,
        fields: &'m [crate::FieldDef],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0usize;
        while let Some(field) = work.at(fields, at)? {
            work.admit(1, size_of::<&Ty>())?;
            self.record_type(owner, &field.ty, work)?;
            work.next(&mut at)?;
        }
        Ok(())
    }
    pub(super) fn inventory<O: ExecutionObserver>(
        &mut self,
        module: &'m Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0usize;
        while let Some(ty) = work.at(&module.types, at)? {
            let owner = work.add(self.summary.tables.types.start, at)?;
            self.record_type(owner, ty, work)?;
            work.next(&mut at)?;
        }
        at = 0;
        while let Some(signature) = work.at(&module.func_types, at)? {
            let owner = work.add(self.summary.tables.func_types.start, at)?;
            work.admit(2, 2 * size_of::<&[Ty]>())?;
            self.types(owner, &signature.params, work)?;
            self.types(owner, &signature.returns, work)?;
            work.next(&mut at)?;
        }
        at = 0;
        while let Some(definition) = work.at(&module.structs, at)? {
            work.admit(1, size_of::<u32>() + size_of::<&[crate::FieldDef]>())?;
            let owner = Tables::named(&self.summary.tables.structs, definition.id.index(), work)?
                .ok_or(ObservedValueError::InvalidRange)?;
            self.fields(owner, &definition.fields, work)?;
            work.next(&mut at)?;
        }
        at = 0;
        while let Some(definition) = work.at(&module.enums, at)? {
            work.admit(1, size_of::<u32>() + size_of::<&[crate::EnumVariant]>())?;
            let owner = Tables::named(&self.summary.tables.enums, definition.id.index(), work)?
                .ok_or(ObservedValueError::InvalidRange)?;
            let mut index = 0usize;
            while let Some(variant) = work.at(&definition.variants, index)? {
                work.admit(1, size_of::<&[Ty]>())?;
                self.types(owner, &variant.fields, work)?;
                work.next(&mut index)?;
            }
            work.next(&mut at)?;
        }
        at = 0;
        while let Some(definition) = work.at(&module.records, at)? {
            work.admit(1, size_of::<u32>() + size_of::<&[crate::FieldDef]>())?;
            let owner = Tables::named(&self.summary.tables.records, definition.id.index(), work)?
                .ok_or(ObservedValueError::InvalidRange)?;
            self.fields(owner, &definition.fields, work)?;
            work.next(&mut at)?;
        }
        at = 0;
        while let Some(closure) = work.at(&module.closure_types, at)? {
            let owner = work.add(self.summary.tables.closure_types.start, at)?;
            work.admit(1, size_of::<usize>() + size_of::<&[Ty]>())?;
            if let Some(target) = Tables::bounded(
                self.summary.tables.func_types,
                closure.func.as_usize(),
                work,
            )? {
                self.dependency(owner, target, work)?;
            }
            self.types(owner, &closure.captures, work)?;
            work.next(&mut at)?;
        }
        Ok(())
    }
}
