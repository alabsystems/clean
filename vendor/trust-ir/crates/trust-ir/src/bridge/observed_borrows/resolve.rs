// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
impl State {
    pub(super) fn resolve<O: ExecutionObserver>(
        &mut self,
        known: &[(u32, Ty)],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<usize>())?;
        let mut index = 0usize;
        loop {
            work.admit(1, size_of::<(u32, u32)>())?;
            let Some(&(result, _)) = self.operands.get(index) else {
                return Ok(());
            };
            let root = chain_root(&self.operands, result, work)?;
            let operand_ty = match root {
                Some(root) => known_type(known, root, work)?,
                None => None,
            };
            work.make_type(operand_ty, &mut self.pending)?;
            work.push_row(&mut self.resolved, result, &mut self.pending)?;
            work.admit(1, size_of::<usize>())?;
            index = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
    }
}
pub(super) fn chain_root<O: ExecutionObserver>(
    rows: &[(u32, u32)],
    result: u32,
    work: &mut Work<'_, '_, O>,
) -> R<Option<u32>> {
    work.admit(1, size_of::<u32>() + size_of::<usize>())?;
    let (mut cursor, mut steps) = (result, 0usize);
    loop {
        work.admit(1, 0)?;
        match work.operand(rows, cursor)? {
            Some(operand) => {
                work.admit(1, size_of::<usize>() + size_of::<u32>())?;
                steps = steps
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                if steps > rows.len() {
                    return Ok(None);
                }
                cursor = operand;
            }
            None => return Ok(Some(cursor)),
        }
    }
}
fn known_type<'a, O: ExecutionObserver>(
    rows: &'a [(u32, Ty)],
    key: u32,
    work: &mut Work<'_, '_, O>,
) -> R<Option<&'a Ty>> {
    work.admit(1, size_of::<usize>())?;
    let mut index = rows.len();
    loop {
        work.admit(1, size_of::<usize>())?;
        if index == 0 {
            return Ok(None);
        }
        index -= 1;
        work.admit(1, size_of::<u32>() + 2 * size_of::<&Ty>())?;
        let (candidate, ty) = rows.get(index).ok_or(ObservedValueError::InvalidRange)?;
        if *candidate == key {
            return Ok(Some(ty));
        }
    }
}
