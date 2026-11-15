// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'f> State<'f> {
    pub(super) fn build_definitions<O: ExecutionObserver>(
        &mut self,
        function: &'f Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut b = 0;
        while let Some(block) = work.at(&function.blocks, b)? {
            let mut p = 0;
            while let Some((value, _)) = work.at(&block.params, p)? {
                self.record(
                    *value,
                    DefinitionState::Unique {
                        instruction: None,
                        block: block.id,
                        instruction_index: None,
                    },
                    work,
                )?;
                work.next(&mut p)?;
            }
            let mut n = 0;
            while let Some(node) = work.at(&block.body, n)? {
                work.admit(1, size_of::<bool>())?;
                if let [value] = node.results.as_slice() {
                    self.record(
                        *value,
                        DefinitionState::Unique {
                            instruction: Some(&node.inst),
                            block: block.id,
                            instruction_index: Some(n),
                        },
                        work,
                    )?;
                } else {
                    let mut v = 0;
                    while let Some(value) = work.at(&node.results, v)? {
                        self.record(*value, DefinitionState::Ambiguous, work)?;
                        work.next(&mut v)?;
                    }
                }
                work.next(&mut n)?;
            }
            work.next(&mut b)?;
        }
        work.admit(1, size_of::<bool>())?;
        self.definitions_built = true;
        Ok(())
    }
    fn record<O: ExecutionObserver>(
        &mut self,
        value: ValueId,
        definition: DefinitionState<'f>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let duplicate = work.read(&self.definitions, value.index())?.is_some();
        work.insert(
            &mut self.definitions,
            value.index(),
            if duplicate {
                DefinitionState::Ambiguous
            } else {
                definition
            },
        )
    }
}
