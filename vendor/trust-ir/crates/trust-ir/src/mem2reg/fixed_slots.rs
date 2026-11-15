// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The fixed-count, homogeneous integer-array part of no-phi promotion.
//! Source loads are never moved or replaced by a later load: only accesses to
//! the fresh private destination are forwarded. A lane therefore retains the
//! value observed at its original store, even when external memory changes.

use super::{apply_promotions, rewrite_inst_with};
use crate::{CastOp, Constant, Function, Inst, Ty, ValueId};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy)]
struct Alias {
    root: ValueId,
    slot: u64,
}

struct Definition {
    ty: Ty,
    nonnegative_constant: Option<u64>,
}

struct Candidate {
    block: usize,
    ty: Ty,
    width: u64,
    count: u64,
    align: u64,
    valid: bool,
    current: HashMap<u64, ValueId>,
    forwards: Vec<(ValueId, ValueId)>,
    deletions: Vec<usize>,
}

fn integer_width(ty: &Ty) -> Option<u64> {
    Some(match ty {
        Ty::I8 | Ty::U8 => 1,
        Ty::I16 | Ty::U16 => 2,
        Ty::I32 | Ty::U32 => 4,
        Ty::I64 | Ty::U64 => 8,
        Ty::I128 | Ty::U128 => 16,
        // Only explicit integer widths, not pointer or aggregate type inference.
        _ => return None,
    })
}

fn literal(ty: &Ty, value: &Constant) -> Option<u64> {
    let width = integer_width(ty)?;
    let Constant::Int(value) = value else {
        return None;
    };
    let value = u64::try_from(*value).ok()?;
    let signed = matches!(ty, Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128);
    let value_bits = width * 8 - u64::from(signed);
    if value_bits < 64 && value >= (1u64 << value_bits) {
        return None;
    }
    Some(value)
}

// Only self-contained, explicitly typed result forms are needed here. Unknown
// producers (notably calls whose result requires module tables) are refused as
// stored values rather than assigned a guessed type by this function-only API.
fn result_type(inst: &Inst, result: usize, arity: usize) -> Option<&Ty> {
    if arity == 1 {
        match inst {
            Inst::Const { ty, .. }
            | Inst::Load { ty, .. }
            | Inst::BinOp { ty, .. }
            | Inst::UnOp { ty, .. }
            | Inst::Copy { ty, .. }
            | Inst::Select { ty, .. }
            | Inst::LoadSlot { ty, .. } => return integer_width(ty).map(|_| ty),
            Inst::Cast { dst_ty, .. } => return integer_width(dst_ty).map(|_| dst_ty),
            _ => {}
        }
    }
    if arity == 2
        && result == 0
        && let Inst::Overflow { ty, .. } = inst
    {
        return integer_width(ty).map(|_| ty);
    }
    None
}

fn aligned(candidate: &Candidate, slot: u64, align: Option<u64>) -> bool {
    let align = align.unwrap_or(candidate.width);
    align.is_power_of_two()
        && candidate.align >= align
        && slot
            .checked_mul(candidate.width)
            .is_some_and(|bytes| bytes.is_multiple_of(align))
}

/// Called only with canonical 64-bit layout authority, after the common proof
/// guard and scalar-register promotion.
/// Both walks are over actual nodes/operands; neither the declared allocation
/// count nor an offset determines collection sizes or loop bounds.
pub(super) fn promote(func: &mut Function) -> usize {
    let mut definitions = HashMap::new();
    let mut defined = HashSet::new();
    let mut duplicate_definition = false;
    let mut uses: HashMap<ValueId, usize> = HashMap::new();
    for block in &mut func.blocks {
        for (value, ty) in &block.params {
            duplicate_definition |= !defined.insert(*value);
            if integer_width(ty).is_some() {
                definitions.insert(
                    *value,
                    Definition {
                        ty: ty.clone(),
                        nonnegative_constant: None,
                    },
                );
            }
        }
        for node in &mut block.body {
            for (result, value) in node.results.iter().enumerate() {
                duplicate_definition |= !defined.insert(*value);
                if let Some(ty) = result_type(&node.inst, result, node.results.len()) {
                    let nonnegative_constant = match &node.inst {
                        Inst::Const { value, .. } => literal(ty, value),
                        _ => None,
                    };
                    definitions.insert(
                        *value,
                        Definition {
                            ty: ty.clone(),
                            nonnegative_constant,
                        },
                    );
                }
            }
            rewrite_inst_with(&mut node.inst, &mut |value| {
                *uses.entry(*value).or_default() += 1;
                *value
            });
        }
    }
    if duplicate_definition {
        return 0;
    }

    let mut aliases: HashMap<ValueId, Alias> = HashMap::new();
    let mut seen_uses: HashMap<ValueId, usize> = HashMap::new();
    let mut candidates: HashMap<ValueId, Candidate> = HashMap::new();
    for (block_index, block) in func.blocks.iter_mut().enumerate() {
        for (instruction, node) in block.body.iter_mut().enumerate() {
            let only_result = (node.results.len() == 1).then(|| node.results[0]);
            let mut allowed_operand = None;
            match &node.inst {
                Inst::Alloca {
                    ty,
                    count: Some(count),
                    align,
                } => {
                    let shape = integer_width(ty).and_then(|width| {
                        let count = definitions.get(count)?.nonnegative_constant?;
                        let align = align.unwrap_or(width);
                        (count > 0
                            && count.checked_mul(width).is_some()
                            && align.is_power_of_two()
                            && align >= width)
                            .then_some((width, count, align))
                    });
                    if let (Some(root), Some((width, count, align))) = (only_result, shape) {
                        aliases.insert(root, Alias { root, slot: 0 });
                        candidates.insert(
                            root,
                            Candidate {
                                block: block_index,
                                ty: ty.clone(),
                                width,
                                count,
                                align,
                                valid: true,
                                current: HashMap::new(),
                                forwards: Vec::new(),
                                deletions: vec![instruction],
                            },
                        );
                    }
                }
                Inst::GEP {
                    pointee_ty,
                    base,
                    indices,
                    ..
                } => {
                    if let Some(alias) = aliases.get(base).copied() {
                        let candidate = candidates.get_mut(&alias.root).unwrap();
                        let slot = indices.iter().try_fold(alias.slot, |slot, index| {
                            slot.checked_add(definitions.get(index)?.nonnegative_constant?)
                        });
                        if candidate.valid
                            && candidate.block == block_index
                            && *pointee_ty == candidate.ty
                            && let Some(result) = only_result
                            && let Some(slot) = slot.filter(|slot| *slot < candidate.count)
                        {
                            // TrustIR sums equally scaled indices. Requiring
                            // every intermediate alias in-range also protects
                            // any carried `inbounds` claim on a chained GEP.
                            aliases.insert(
                                result,
                                Alias {
                                    root: alias.root,
                                    slot,
                                },
                            );
                            candidate.deletions.push(instruction);
                            allowed_operand = Some(*base);
                        } else {
                            candidate.valid = false;
                        }
                    }
                }
                Inst::Copy {
                    ty: Ty::Ptr,
                    operand,
                } => {
                    if let Some(alias) = aliases.get(operand).copied() {
                        let candidate = candidates.get_mut(&alias.root).unwrap();
                        if candidate.valid
                            && candidate.block == block_index
                            && let Some(result) = only_result
                        {
                            aliases.insert(result, alias);
                            candidate.deletions.push(instruction);
                            allowed_operand = Some(*operand);
                        } else {
                            candidate.valid = false;
                        }
                    }
                }
                Inst::Load {
                    ty,
                    ptr,
                    volatile,
                    align,
                } => {
                    if let Some(alias) = aliases.get(ptr).copied() {
                        let candidate = candidates.get_mut(&alias.root).unwrap();
                        let value = candidate.current.get(&alias.slot).copied();
                        if candidate.valid
                            && candidate.block == block_index
                            && *ty == candidate.ty
                            && !volatile
                            && aligned(candidate, alias.slot, *align)
                            && let Some(result) = only_result
                            && let Some(value) = value
                        {
                            candidate.forwards.push((result, value));
                            candidate.deletions.push(instruction);
                            allowed_operand = Some(*ptr);
                        } else {
                            candidate.valid = false;
                        }
                    }
                }
                Inst::Store {
                    ty,
                    ptr,
                    value,
                    volatile,
                    align,
                } => {
                    if let Some(alias) = aliases.get(ptr).copied() {
                        let candidate = candidates.get_mut(&alias.root).unwrap();
                        if candidate.valid
                            && candidate.block == block_index
                            && *ty == candidate.ty
                            && !volatile
                            && node.results.is_empty()
                            && aligned(candidate, alias.slot, *align)
                            && !aliases.contains_key(value)
                            && definitions.get(value).is_some_and(|value| value.ty == *ty)
                        {
                            candidate.current.insert(alias.slot, *value);
                            candidate.deletions.push(instruction);
                            allowed_operand = Some(*ptr);
                        } else {
                            candidate.valid = false;
                        }
                    }
                }
                Inst::Cast {
                    op: CastOp::PtrToInt,
                    src_ty: Ty::Ptr,
                    dst_ty: Ty::I64 | Ty::U64,
                    operand,
                } => {
                    if let Some(alias) = aliases.get(operand).copied() {
                        let candidate = candidates.get_mut(&alias.root).unwrap();
                        if candidate.valid
                            && candidate.block == block_index
                            && only_result.is_some_and(|result| !uses.contains_key(&result))
                        {
                            // The common guard excludes ALL summary/proof
                            // bindings before this ordinary-SSA liveness test.
                            // No live integer address, even a roundtrip, aliases.
                            candidate.deletions.push(instruction);
                            allowed_operand = Some(*operand);
                        } else {
                            candidate.valid = false;
                        }
                    }
                }
                _ => {}
            }
            // One exhaustive operand census, not a candidate-by-node search.
            // Pointer-as-value Store and GEP-index uses remain escapes even if
            // the same node has a different, admitted address operand.
            rewrite_inst_with(&mut node.inst, &mut |value| {
                if let Some(alias) = aliases.get(value) {
                    *seen_uses.entry(*value).or_default() += 1;
                    if allowed_operand != Some(*value) {
                        candidates.get_mut(&alias.root).unwrap().valid = false;
                    }
                }
                *value
            });
        }
    }
    // In malformed backward/self-referential SSA an operand may precede alias
    // discovery. Never promote an object unless EVERY actual use was visited.
    for (value, alias) in &aliases {
        if uses.get(value).copied().unwrap_or(0) != seen_uses.get(value).copied().unwrap_or(0) {
            candidates.get_mut(&alias.root).unwrap().valid = false;
        }
    }
    let mut forwards = HashMap::new();
    let mut deletions = HashMap::<usize, Vec<usize>>::new();
    let mut promoted = 0;
    for candidate in candidates.into_values().filter(|candidate| candidate.valid) {
        forwards.extend(candidate.forwards);
        deletions
            .entry(candidate.block)
            .or_default()
            .extend(candidate.deletions);
        promoted += 1;
    }
    if promoted != 0 {
        apply_promotions(func, forwards, deletions);
    }
    promoted
}
