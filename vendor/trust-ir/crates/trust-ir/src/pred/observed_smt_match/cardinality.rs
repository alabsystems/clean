// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn cardinality<O: ExecutionObserver>(
    universe: &Universe,
    work: &mut Work<'_, '_, O>,
) -> R<Option<u128>> {
    work.admit(2, size_of::<Option<u128>>())?;
    match universe {
        Universe::IntRange { lo, hi } => {
            work.admit(8, 2 * size_of::<i128>() + size_of::<u128>())?;
            if lo > hi {
                return Ok(None);
            }
            Ok((hi.wrapping_sub(*lo) as u128).checked_add(1))
        }
        Universe::Members(items) => {
            work.admit(4, 2 * size_of::<usize>() + size_of::<Option<(u8, i128)>>())?;
            if items.is_empty() || items.len() > MAX_ENUMERATED_MEMBERS {
                return Ok(None);
            }
            let mut previous = None;
            let mut at = 0usize;
            while let Some(value) = work.at(items, at)? {
                // constant_key reads only fixed tags and Int/Bool scalars.
                work.admit(32, size_of::<Option<(u8, i128)>>())?;
                let Some(key) = constant_key(value) else {
                    return Ok(None);
                };
                work.admit(3, 2 * size_of::<(u8, i128)>())?;
                if previous.is_some_and(|prior| key <= prior) {
                    return Ok(None);
                }
                previous = Some(key);
                work.next(&mut at)?;
            }
            work.admit(1, size_of::<u128>())?;
            Ok(Some(items.len() as u128))
        }
    }
}
