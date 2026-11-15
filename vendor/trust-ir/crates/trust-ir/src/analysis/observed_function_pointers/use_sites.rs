// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'f> State<'f> {
    pub(super) fn build_uses<O: ExecutionObserver>(
        &mut self,
        function: &'f Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(block) = work.at(&function.blocks, at)? {
            work.admit(1, size_of::<UseBlockState<'_>>())?;
            self.pending_use = Some(UseBlockState::Unique {
                block,
                parameters: BTreeSet::new(),
            });
            let Some(UseBlockState::Unique { parameters, .. }) = &mut self.pending_use else {
                return Err(ObservedValueError::InvalidRange);
            };
            let mut p = 0;
            while let Some((parameter, _)) = work.at(&block.params, p)? {
                work.mark(parameters, parameter.index())?;
                work.next(&mut p)?;
            }
            // Freshly built and displaced parameter sets remain State-owned
            // across all admission/retirement callbacks, even on duplicate IDs.
            work.lookup(self.uses.len())?;
            let duplicate = self.uses.contains_key(&block.id.index());
            work.tree::<UseBlockState<'_>>(self.uses.len())?;
            work.admit(1, 2 * size_of::<Option<UseBlockState<'_>>>())?;
            let value = if duplicate {
                UseBlockState::Ambiguous
            } else {
                self.pending_use
                    .take()
                    .ok_or(ObservedValueError::InvalidRange)?
            };
            self.old_use = self.uses.insert(block.id.index(), value);
            work.use_state(self.old_use.take());
            work.use_state(self.pending_use.take());
            work.next(&mut at)?;
        }
        work.admit(1, size_of::<bool>())?;
        self.use_built = true;
        Ok(())
    }
    pub(super) fn use_block<O: ExecutionObserver>(
        &self,
        block: BlockId,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<&'f Block>> {
        work.lookup(self.uses.len())?;
        work.admit(1, size_of::<Option<&Block>>())?;
        let Some(UseBlockState::Unique { block, parameters }) = self.uses.get(&block.index())
        else {
            return Ok(None);
        };
        // Membership is intentionally NOT queried here: the exact operand
        // short-circuit must execute before the block-parameter dynamic check.
        let _ = parameters;
        Ok(Some(*block))
    }
    pub(super) fn is_parameter<O: ExecutionObserver>(
        &self,
        block: BlockId,
        value: ValueId,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.lookup(self.uses.len())?;
        let Some(UseBlockState::Unique { parameters, .. }) = self.uses.get(&block.index()) else {
            return Err(ObservedValueError::InvalidRange);
        };
        work.contains(parameters, value.index())
    }
}
