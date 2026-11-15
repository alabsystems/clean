// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn dynamic<O: ExecutionObserver>(
    block: &Block,
    value: ValueId,
    index: usize,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(16, 4 * size_of::<usize>() + size_of::<Option<usize>>())?;
    let window = local_prefilter_instruction_window(block.body.len(), index);
    let mut at = window.start;
    let mut definition = None;
    while at < window.end {
        let node = work
            .at(&block.body, at)?
            .ok_or(ObservedValueError::InvalidRange)?;
        work.admit(8, size_of::<Option<usize>>() + size_of::<ValueId>())?;
        if let [result] = node.results.as_slice()
            && *result == value
            && (!matches!(
                &node.inst,
                Inst::Const {
                    value: Constant::FnDef(_),
                    ..
                } | Inst::Copy { .. }
                    | Inst::Cast {
                        op: CastOp::ReifyFnPointer,
                        ..
                    }
            ) || definition.replace(at).is_some())
        {
            return Ok(true);
        }
        work.next(&mut at)?;
    }
    work.admit(1, size_of::<bool>())?;
    Ok(definition.is_some_and(|definition| definition >= index))
}
