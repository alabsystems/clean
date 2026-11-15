// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Original least solution of the uninhabitedness equations. The all-definition
//! relation is read by observed borrowed scans rather than an opaque index.

use super::*;
use crate::value::RecordId;

mod solve;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Node {
    Entry(usize),
    Struct(StructId),
    Record(RecordId),
    Enum(EnumId),
}

pub(super) fn unencoded<O: ExecutionObserver>(
    module: &Module,
    def: &EnumDef,
    untagged: u32,
    start: u32,
    end: u32,
    work: &mut Work<'_, '_, O>,
) -> R<Option<usize>> {
    for (index, variant) in def.variants.iter().enumerate() {
        work.poll()?;
        let encoded = u32::try_from(index)
            .is_ok_and(|index| index == untagged || (start..=end).contains(&index));
        if !encoded && !some(module, variant.fields.iter(), work)? {
            return Ok(Some(index));
        }
    }
    Ok(None)
}

pub(super) fn some<'t, O: ExecutionObserver>(
    module: &Module,
    tys: impl Iterator<Item = &'t Ty>,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    let mut roots = Vec::new();
    let mut undecided = Vec::new();
    let result = (|| {
        if literals(module, tys, &mut roots, work)? {
            return Ok(true);
        }
        for &node in &roots {
            work.lookup(work.inhabitedness.len())?;
            match work.inhabitedness.get(&node).copied() {
                Some(true) => return Ok(true),
                Some(false) => {}
                None => work.push(&mut undecided, node)?,
            }
        }
        if undecided.is_empty() {
            return Ok(false);
        }
        solve::run(module, &undecided, work)?;
        for &node in &undecided {
            work.lookup(work.inhabitedness.len())?;
            if work.inhabitedness.get(&node) == Some(&true) {
                return Ok(true);
            }
        }
        Ok(false)
    })();
    work.retire_copy_vec(roots);
    work.retire_copy_vec(undecided);
    work.poll()?;
    result
}

fn literals<'t, O: ExecutionObserver>(
    module: &Module,
    tys: impl Iterator<Item = &'t Ty>,
    out: &mut Vec<Node>,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    let mut pending = Vec::new();
    let result = (|| {
        for ty in tys {
            work.push(&mut pending, ty)?;
        }
        while !pending.is_empty() {
            work.poll()?;
            let Some(ty) = pending.pop() else { break };
            match ty {
                Ty::Never => return Ok(true),
                Ty::Tuple(elems) => {
                    for ty in elems {
                        work.push(&mut pending, ty)?;
                    }
                }
                Ty::Array(elem, len) if *len > 0 && module.types.get(elem.as_usize()).is_some() => {
                    work.push(out, Node::Entry(elem.as_usize()))?
                }
                Ty::Refine(base, _) if module.types.get(base.as_usize()).is_some() => {
                    work.push(out, Node::Entry(base.as_usize()))?
                }
                Ty::Struct(id) => work.push(out, Node::Struct(*id))?,
                Ty::Record(id) => work.push(out, Node::Record(*id))?,
                Ty::Enum(id) => work.push(out, Node::Enum(*id))?,
                _ => {}
            }
        }
        Ok(false)
    })();
    work.retire_copy_vec(pending);
    work.poll()?;
    result
}
