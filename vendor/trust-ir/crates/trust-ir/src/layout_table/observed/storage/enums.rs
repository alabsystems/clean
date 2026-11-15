// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(in super::super) fn arc_enum(&mut self, shape: EnumLayoutShape) -> R<Arc<EnumLayoutShape>> {
        let bytes = size_of::<EnumLayoutShape>()
            .checked_add(2 * size_of::<usize>())
            .and_then(|n| n.checked_add(2 * align_of::<EnumLayoutShape>()))
            .ok_or(ObservedValueError::CapacityOverflow);
        let result = bytes
            .map_err(Error::from)
            .and_then(|bytes| self.admit(1, bytes));
        if let Err(error) = result {
            self.retire_enum_shape(shape);
            self.poll()?;
            return Err(error);
        }
        Ok(Arc::new(shape))
    }

    pub(in super::super) fn cache_enum(&mut self, index: usize, shape: Arc<EnumLayoutShape>) -> R {
        let result = self.lookup(self.enums.len()).and_then(|()| {
            if self.enums.contains_key(&index) {
                return Err(ObservedValueError::UnsupportedValue.into());
            }
            self.tree::<usize, Arc<EnumLayoutShape>>(self.enums.len())
        });
        if let Err(error) = result {
            self.retire_enum(shape);
            self.poll()?;
            return Err(error);
        }
        self.enums.insert(index, shape);
        Ok(())
    }

    pub(in super::super) fn retire_enum(&mut self, shape: Arc<EnumLayoutShape>) {
        let _ = shape.retire_arc_observed(self.session, self.site);
    }

    fn retire_enum_shape(&mut self, shape: EnumLayoutShape) {
        let _ = shape.retire_observed(self.session, self.site);
    }
}
