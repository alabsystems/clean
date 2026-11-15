// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
mod extend;
pub(super) use extend::dominates;
pub(super) fn build<'f, O: ExecutionObserver>(
    definitions: &BTreeMap<u32, DefinitionState<'f>>,
    tree: &DominatorTree,
    entries: &mut BTreeMap<u32, ProvenanceState<'f>>,
    active: &mut BTreeSet<u32>,
    path: &mut Vec<(u32, ProvenanceStep<'f>)>,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.cursor::<DefinitionState<'_>>(definitions.len())?;
    let mut rows = definitions.iter();
    loop {
        work.cursor_next::<DefinitionState<'_>>(definitions.len())?;
        let Some((&start, definition)) = rows.next() else {
            break;
        };
        work.admit(16, size_of::<bool>())?;
        if !is_static_provenance_candidate(definition) {
            continue;
        }
        if work.read(entries, start)?.is_some() {
            continue;
        }
        work.admit(
            1,
            size_of::<Vec<(u32, ProvenanceStep<'_>)>>() + 2 * size_of::<u32>(),
        )?;
        let mut current = start;
        let mut cycle = false;
        loop {
            if work.read(entries, current)?.is_some() {
                break;
            }
            if work.contains(active, current)? {
                cycle = true;
                break;
            }
            let Some(definition) = work.read(definitions, current)? else {
                break;
            };
            work.admit(16, size_of::<bool>())?;
            if !is_static_provenance_candidate(&definition) {
                break;
            }
            work.admit(
                16,
                size_of::<ProvenanceState<'_>>() + size_of::<ProvenanceStep<'_>>(),
            )?;
            match definition {
                DefinitionState::Unique {
                    instruction:
                        Some(Inst::Const {
                            ty: result_type @ Ty::Func(signature),
                            value: Constant::FnDef(function),
                        }),
                    block,
                    instruction_index: Some(index),
                } => {
                    work.insert(
                        entries,
                        current,
                        ProvenanceState::Resolved(StaticProvenanceSummary {
                            function: *function,
                            declared_signature: *signature,
                            carrier: StaticFunctionPointerCarrier::Function(*signature),
                            result_type,
                            definition_block: block,
                            definition_instruction: index,
                            origin_value: ValueId::new(current),
                            origin_block: block,
                            origin_instruction: index,
                            chain_definitions: 1,
                        }),
                    )?;
                    break;
                }
                DefinitionState::Unique {
                    instruction: Some(Inst::Copy { ty, operand }),
                    block,
                    instruction_index: Some(index),
                } => {
                    work.mark(active, current)?;
                    work.push(
                        path,
                        (
                            current,
                            ProvenanceStep::Copy {
                                result_type: ty,
                                operand: *operand,
                                definition_block: block,
                                definition_instruction: index,
                            },
                        ),
                    )?;
                    current = operand.index();
                }
                DefinitionState::Unique {
                    instruction:
                        Some(Inst::Cast {
                            op: CastOp::ReifyFnPointer,
                            src_ty,
                            dst_ty,
                            operand,
                        }),
                    block,
                    instruction_index: Some(index),
                } => {
                    work.mark(active, current)?;
                    work.push(
                        path,
                        (
                            current,
                            ProvenanceStep::Reify {
                                source_type: src_ty,
                                result_type: dst_ty,
                                operand: *operand,
                                definition_block: block,
                                definition_instruction: index,
                            },
                        ),
                    )?;
                    current = operand.index();
                }
                DefinitionState::Unique { .. } | DefinitionState::Ambiguous => break,
            }
        }
        if cycle {
            let mut at = 0;
            while let Some(&(value, _)) = work.at(path, at)? {
                work.unmark(active, value)?;
                work.insert(entries, value, ProvenanceState::Rejected)?;
                work.next(&mut at)?;
            }
        } else {
            loop {
                work.admit(1, size_of::<Option<(u32, ProvenanceStep<'_>)>>())?;
                let Some((value, step)) = path.pop() else {
                    break;
                };
                work.unmark(active, value)?;
                let operand = match step {
                    ProvenanceStep::Copy { operand, .. }
                    | ProvenanceStep::Reify { operand, .. } => operand,
                };
                let child = work
                    .read(entries, operand.index())?
                    .unwrap_or(ProvenanceState::Rejected);
                let state = extend::step(child, step, tree, work)?;
                work.insert(entries, value, state)?;
            }
        }
        work.rows(take(path));
        // Retirement cancellation must be observed before another normal row.
        work.admit(1, 0)?;
    }
    Ok(())
}
