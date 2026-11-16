// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bounded, nominal Byte SSA metadata diagnostic, NOT a verified translator.
//!
//! The input module and its IDs are untouched. We independently census raw
//! definitions before the bridge's zip/map operations, then compare its typed
//! rows exactly. Types are mapped separately from the legacy `Projector`:
//! nominal aggregate IDs and all five fat-pointer kinds remain distinguishable.
//! No alignments, calling conventions, contexts, instructions, or authenticated
//! `IRByteSiteV1.mkt` terms are manufactured. Borrow metadata is unsupported:
//! the locked bridge can fall back to provisional `Ptr` without a known root.
//!
//! Success means only the stated definition/row/use checks succeeded. In
//! particular, `result_tys` returns an empty list for unresolved callees; an
//! unresolved ZERO-result call can pass arity equality. We do not establish
//! call resolution, dominance, instruction typing, or module validation, and
//! neither producer/source metadata nor this JSON grants proof authority.

mod metadata_eq;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use sha2::{Digest, Sha256};
use trust_ir::bridge::{borrow_result_types, TypedValueMetadata, ValueMetadataOrigin};
use trust_ir::{FatPtrKind, FuncId, Module, Ty};

use super::{hex, json_string, R};

const AUTHORITY: &str = concat!(
    "\"source_authority\":false,\"native_authority\":false,",
    "\"refinement_authority\":false,\"module_validation_authority\":false,",
    "\"authenticated_catalog\":false,\"full_byte_translation\":false,",
    "\"call_resolution_established\":false,\"dominance_established\":false,",
    "\"instruction_typing_established\":false,\"target_compatibility_established\":false,",
    "\"module_producer_cohort_established\":false,\"input_source_identity_established\":false,",
    "\"proof_annotations_authenticated\":false"
);

pub(super) fn run(args: &[String]) -> R<String> {
    if args.len() != 3 || args[0] != "--byte-sites" {
        return Err("usage: a2project --byte-sites <fca-module.bin> <function-id>".into());
    }
    if args[2].is_empty() || !args[2].bytes().all(|byte| byte.is_ascii_digit()) {
        return Err("function-id must be an unsigned decimal u32".into());
    }
    let id = args[2]
        .parse::<u32>()
        .map_err(|error| format!("function-id is not a u32: {error}"))?;
    let bytes = std::fs::read(&args[1]).map_err(|error| format!("read {}: {error}", args[1]))?;
    let module = trust_ir::binary::deserialize_module(&bytes)
        .map_err(|error| format!("deserialize {}: {error}", args[1]))?;
    let reflected = reflect(&module, FuncId::new(id))?;
    let digest = hex(&Sha256::digest(&bytes));
    reflected.json(&args[1], &digest)
}

#[derive(Debug)]
struct Row {
    raw: TypedValueMetadata,
    byte_ty: String,
}

#[derive(Debug)]
struct Node {
    block: u32,
    pc: usize,
    results: Vec<u32>,
    raw_result_tys: Vec<Ty>,
    byte_result_tys: Vec<String>,
    // Occurrences retain multiplicity and producer visitor order. Metadata
    // deduplicates IDs in first-occurrence order; repeated SSA uses are legal.
    occurrences: Vec<u32>,
    operands: Vec<u32>,
}

#[derive(Debug)]
struct Reflection {
    function: u32,
    name: String,
    entry: u32,
    blocks: Vec<u32>,
    rows: Vec<Row>,
    nodes: Vec<Node>,
}

/// This census intentionally precedes any ID-keyed lookup or bridge call.
/// Function/aggregate lookup otherwise uses a first-match table scan.
fn unique_module_ids(module: &Module) -> R<()> {
    let mut functions = BTreeSet::new();
    for function in &module.functions {
        if !functions.insert(function.id) {
            return Err(format!("duplicate module function ID {}", function.id));
        }
    }
    let mut structs = BTreeSet::new();
    for def in &module.structs {
        if !structs.insert(def.id) {
            return Err(format!("duplicate module struct ID {}", def.id));
        }
    }
    let mut enums = BTreeSet::new();
    for def in &module.enums {
        if !enums.insert(def.id) {
            return Err(format!("duplicate module enum ID {}", def.id));
        }
    }
    Ok(())
}

fn origin_key(origin: ValueMetadataOrigin) -> (u8, u32, usize, usize) {
    match origin {
        ValueMetadataOrigin::BlockParam { block, param_index } => (0, block.0, param_index, 0),
        ValueMetadataOrigin::InstrResult {
            block,
            instruction_index,
            result_index,
        } => (1, block.0, instruction_index, result_index),
    }
}

fn origins_match(actual: ValueMetadataOrigin, expected: ValueMetadataOrigin) -> bool {
    match (actual, expected) {
        (
            ValueMetadataOrigin::BlockParam {
                block: a,
                param_index: ai,
            },
            ValueMetadataOrigin::BlockParam {
                block: b,
                param_index: bi,
            },
        ) => a == b && ai == bi,
        (
            ValueMetadataOrigin::InstrResult {
                block: a,
                instruction_index: ap,
                result_index: ar,
            },
            ValueMetadataOrigin::InstrResult {
                block: b,
                instruction_index: bp,
                result_index: br,
            },
        ) => a == b && ap == bp && ar == br,
        (
            ValueMetadataOrigin::BlockParam {
                block: _,
                param_index: _,
            },
            ValueMetadataOrigin::InstrResult {
                block: _,
                instruction_index: _,
                result_index: _,
            },
        ) => false,
        (
            ValueMetadataOrigin::InstrResult {
                block: _,
                instruction_index: _,
                result_index: _,
            },
            ValueMetadataOrigin::BlockParam {
                block: _,
                param_index: _,
            },
        ) => false,
    }
}

/// Compare every row field in order. Origins, types, and annotations use
/// exhaustive structural pair matches; new producer variants force an
/// explicit reader change rather than falling through a value comparison.
fn rows_match(actual: &[TypedValueMetadata], expected: &[TypedValueMetadata]) -> bool {
    actual.len() == expected.len()
        && actual.iter().zip(expected).all(|(a, b)| {
            a.value == b.value
                && metadata_eq::ty_matches(&a.ty, &b.ty)
                && origins_match(a.origin, b.origin)
                && metadata_eq::proofs_match(&a.proofs, &b.proofs)
                && a.span == b.span
        })
}

fn reflect(module: &Module, id: FuncId) -> R<Reflection> {
    unique_module_ids(module)?;
    let function = module
        .function_by_id(id)
        .ok_or_else(|| format!("selected function ID {id} is absent"))?;
    if function.blocks.is_empty() {
        return Err(format!("selected function {id} has no body"));
    }
    let mut blocks = BTreeSet::new();
    let mut definitions = BTreeSet::new();
    let mut origins = BTreeSet::new();
    let mut expected = Vec::new();
    let mut nodes = Vec::new();
    for block in &function.blocks {
        if !blocks.insert(block.id) {
            return Err(format!("duplicate block ID {} in function {id}", block.id));
        }
        for (param_index, (value, ty)) in block.params.iter().enumerate() {
            if !definitions.insert(*value) {
                return Err(format!("duplicate SSA definition {value} in function {id}"));
            }
            let origin = ValueMetadataOrigin::BlockParam {
                block: block.id,
                param_index,
            };
            if !origins.insert(origin_key(origin)) {
                return Err("duplicate block parameter origin".into());
            }
            expected.push(TypedValueMetadata {
                value: *value,
                ty: ty.clone(),
                origin,
                proofs: Vec::new(),
                span: None,
            });
        }
        for (pc, node) in block.body.iter().enumerate() {
            let result_tys = node.result_tys(module);
            // Do not let the bridge's zip hide omitted, excess, unresolved,
            // or duplicate result carriers (including malformed borrows).
            if node.results.len() != result_tys.len() {
                return Err(format!(
                    "result arity mismatch at function {id} block {} pc {pc}: {} IDs versus {} types",
                    block.id, node.results.len(), result_tys.len()
                ));
            }
            for (result_index, (value, ty)) in node.results.iter().zip(&result_tys).enumerate() {
                if !definitions.insert(*value) {
                    return Err(format!("duplicate SSA definition {value} in function {id}"));
                }
                let origin = ValueMetadataOrigin::InstrResult {
                    block: block.id,
                    instruction_index: pc,
                    result_index,
                };
                if !origins.insert(origin_key(origin)) {
                    return Err("duplicate instruction result origin".into());
                }
                expected.push(TypedValueMetadata {
                    value: *value,
                    ty: ty.clone(),
                    origin,
                    proofs: node.proofs.clone(),
                    span: node.span,
                });
            }
            let mut occurrences = Vec::new();
            node.inst
                .visit_value_operands(|value| occurrences.push(value.0));
            let mut seen = BTreeSet::new();
            let operands = occurrences
                .iter()
                .copied()
                .filter(|value| seen.insert(*value))
                .collect();
            nodes.push(Node {
                block: block.id.0,
                pc,
                results: node.results.iter().map(|value| value.0).collect(),
                raw_result_tys: result_tys,
                byte_result_tys: Vec::new(),
                occurrences,
                operands,
            });
        }
    }
    if !blocks.contains(&function.entry) {
        return Err(format!("entry block {} is absent", function.entry));
    }
    // Every syntactic Borrow/BorrowMut has exactly one result after the arity
    // check above, so this canonical helper necessarily enumerates it. Reject
    // ALL such rows, including valid roots and cycles, rather than accepting
    // its provisional Ptr. Zero-result borrows failed the earlier arity check.
    if !borrow_result_types(function, &|_| None).is_empty() {
        return Err("unsupported Borrow/BorrowMut metadata: no successful-root witness; provisional Ptr is not accepted".into());
    }
    let actual = function.typed_values(module);
    if !rows_match(&actual, &expected) {
        return Err(
            "typed_values differs from complete ordered raw definition/type/origin census".into(),
        );
    }
    let rows = expected
        .into_iter()
        .map(|raw| {
            Ok(Row {
                byte_ty: byte_ty(module, &raw.ty)?,
                raw,
            })
        })
        .collect::<R<Vec<_>>>()?;
    let row_by_id: BTreeMap<_, _> = rows.iter().map(|row| (row.raw.value.0, row)).collect();
    for node in &mut nodes {
        for value in &node.occurrences {
            if !row_by_id.contains_key(value) {
                return Err(format!(
                    "undefined SSA use {value} at function {id} block {} pc {}",
                    node.block, node.pc
                ));
            }
        }
        node.byte_result_tys = node
            .raw_result_tys
            .iter()
            .map(|ty| byte_ty(module, ty))
            .collect::<R<Vec<_>>>()?;
    }
    Ok(Reflection {
        function: id.0,
        name: function.name.clone(),
        entry: function.entry.0,
        blocks: function.blocks.iter().map(|block| block.id.0).collect(),
        rows,
        nodes,
    })
}

fn byte_ty(module: &Module, ty: &Ty) -> R<String> {
    byte_ty_inner(module, ty, &mut BTreeSet::new())
}

fn byte_ty_inner(module: &Module, ty: &Ty, resolving: &mut BTreeSet<u32>) -> R<String> {
    // Cycles fail below; an unusually deep acyclic table is also outside this
    // bounded diagnostic, rather than becoming an unbounded host recursion.
    if resolving.len() >= 64 {
        return Err("slice element resolution exceeds the 64-row diagnostic depth limit".into());
    }
    Ok(match ty {
        Ty::Ext(e) => e.unreachable(),
        Ty::Bool => "IRTy.bool_".into(),
        Ty::I8 => "(IRTy.int_ 8)".into(),
        Ty::I16 => "(IRTy.int_ 16)".into(),
        Ty::I32 => "(IRTy.int_ 32)".into(),
        Ty::I64 => "(IRTy.int_ 64)".into(),
        Ty::I128 => "(IRTy.int_ 128)".into(),
        Ty::U8 => "(IRTy.uint_ 8)".into(),
        Ty::U16 => "(IRTy.uint_ 16)".into(),
        Ty::U32 => "(IRTy.uint_ 32)".into(),
        Ty::U64 => "(IRTy.uint_ 64)".into(),
        Ty::U128 => "(IRTy.uint_ 128)".into(),
        Ty::F32 => "(IRTy.float_ 32)".into(),
        Ty::F64 => "(IRTy.float_ 64)".into(),
        Ty::Ptr => "IRTy.ptr_".into(),
        Ty::Unit => "IRTy.unit_".into(),
        Ty::Never => "IRTy.never_".into(),
        Ty::Struct(id) => {
            if module.struct_def(*id).is_none() {
                return Err(format!("missing nominal struct ID {id}"));
            }
            format!("(IRTy.struct_ {})", id.0)
        }
        Ty::Enum(id) => {
            if module.enum_def(*id).is_none() {
                return Err(format!("missing nominal enum ID {id}"));
            }
            format!("(IRTy.enum_ {})", id.0)
        }
        Ty::Func(id) => {
            if module.func_type(*id).is_none() {
                return Err(format!("missing nominal function signature ID {id}"));
            }
            format!("(IRTy.func_ {})", id.0)
        }
        Ty::FatPtr(kind) => match kind {
            FatPtrKind::Str => "IRTy.fatstr_".into(),
            FatPtrKind::Slice(id) => {
                if !resolving.insert(id.0) {
                    return Err(format!("cyclic slice element type ID {id}"));
                }
                let element = module
                    .ty(*id)
                    .ok_or_else(|| format!("missing slice element type ID {id}"))?;
                let image = byte_ty_inner(module, element, resolving)?;
                resolving.remove(&id.0);
                format!("(IRTy.fatslice_ {image})")
            }
            FatPtrKind::TraitObject { trait_id } => format!("(IRTy.fatdyn_ {trait_id})"),
            FatPtrKind::ContainerLen => "IRTy.containerlen_".into(),
            FatPtrKind::ContainerVtable => "IRTy.containervtable_".into(),
        },
        unsupported @ (Ty::FnItem(_)
        | Ty::Isize
        | Ty::Usize
        | Ty::Char
        | Ty::Error
        | Ty::F16
        | Ty::Vector(..)
        | Ty::Array(..)
        | Ty::Tuple(..)
        | Ty::Ref(..)
        | Ty::RefMut(..)
        | Ty::PtrConst(..)
        | Ty::PtrMut(..)
        | Ty::Rc(..)
        | Ty::Set(..)
        | Ty::Sequence(..)
        | Ty::Record(..)
        | Ty::Closure(..)
        | Ty::Refine(..)
        | Ty::Dialect(..)
        | Ty::Tensor(..)
        | Ty::Storage(..)
        | Ty::Handle(..)) => {
            return Err(format!(
                "unsupported nominal Byte type {unsupported:?}; no erasure permitted"
            ))
        }
    })
}

fn numbers(values: &[u32]) -> String {
    values
        .iter()
        .map(u32::to_string)
        .collect::<Vec<_>>()
        .join(",")
}

fn strings(values: impl IntoIterator<Item = String>) -> String {
    values
        .into_iter()
        .map(|value| json_string(&value))
        .collect::<Vec<_>>()
        .join(",")
}

fn origin_json(origin: ValueMetadataOrigin) -> String {
    match origin {
        ValueMetadataOrigin::BlockParam { block, param_index } => format!(
            "{{\"kind\":\"block_param\",\"block\":{},\"param_index\":{param_index}}}", block.0
        ),
        ValueMetadataOrigin::InstrResult { block, instruction_index, result_index } => format!(
            "{{\"kind\":\"instruction_result\",\"block\":{},\"pc\":{instruction_index},\"result_index\":{result_index}}}", block.0
        ),
    }
}

impl Reflection {
    fn json(&self, input: &str, digest: &str) -> R<String> {
        let mut out = format!(
            "{{\"schema_version\":\"clean.byte_ssa_diagnostic.v1\",\"status\":\"diagnostic_only\",{AUTHORITY},\"input_path\":{},\"input_sha256\":{},\"raw_ids_preserved\":true,\"function_id\":{},\"function_name_diagnostic\":{},\"entry_block\":{},\"block_ids\":[{}],\"checks\":{{\"unique_module_function_struct_enum_ids\":true,\"unique_selected_blocks_definitions_origins\":true,\"exact_node_result_arities\":true,\"exact_ordered_typed_values_rows\":true,\"all_operand_occurrences_defined\":true,\"borrow_rows_supported\":false}},\"definition_count\":{},\"node_count\":{},\"operand_occurrence_count\":{},\"deduplicated_operand_row_count\":{},\"rows\":[",
            json_string(input), json_string(digest), self.function,
            json_string(&self.name), self.entry, numbers(&self.blocks),
            self.rows.len(), self.nodes.len(),
            self.nodes.iter().map(|node| node.occurrences.len()).sum::<usize>(),
            self.nodes.iter().map(|node| node.operands.len()).sum::<usize>()
        );
        for (index, row) in self.rows.iter().enumerate() {
            if index != 0 {
                out.push(',');
            }
            let _ = write!(
                out,
                "{{\"value_id\":{},\"raw_ty\":{},\"byte_ty\":{},\"origin\":{}}}",
                row.raw.value.0,
                json_string(&format!("{:?}", row.raw.ty)),
                json_string(&row.byte_ty),
                origin_json(row.raw.origin)
            );
        }
        out.push_str("],\"nodes\":[");
        for (index, node) in self.nodes.iter().enumerate() {
            if index != 0 {
                out.push(',');
            }
            let _ = write!(out,
                "{{\"block\":{},\"pc\":{},\"result_ids\":[{}],\"raw_result_tys\":[{}],\"byte_result_tys\":[{}],\"operand_occurrences\":[{}],\"operands\":[",
                node.block, node.pc, numbers(&node.results),
                strings(node.raw_result_tys.iter().map(|ty| format!("{ty:?}"))),
                strings(node.byte_result_tys.iter().cloned()), numbers(&node.occurrences)
            );
            for (operand_index, value) in node.operands.iter().enumerate() {
                if operand_index != 0 {
                    out.push(',');
                }
                // The complete use census checked this exact raw ID above.
                // No default type or first-match nominal inference is used.
                let row = self
                    .rows
                    .iter()
                    .find(|row| row.raw.value.0 == *value)
                    .ok_or_else(|| format!("internal diagnostic census lost operand ID {value}"))?;
                let _ = write!(
                    out,
                    "{{\"value_id\":{value},\"raw_ty\":{},\"byte_ty\":{}}}",
                    json_string(&format!("{:?}", row.raw.ty)),
                    json_string(&row.byte_ty)
                );
            }
            out.push_str("]}");
        }
        out.push_str("]}");
        Ok(out)
    }
}

#[cfg(test)]
mod tests;
