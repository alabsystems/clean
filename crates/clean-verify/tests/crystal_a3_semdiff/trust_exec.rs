// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **E2 — running the committed emitted body under trust-ir's own interpreter.**
//!
//! The subject function is the fixture text VERBATIM. Only two things are added
//! around it, and both are declared rather than assumed:
//!
//! * an **enum declaration** for the argument type, because the crate-level dump
//!   references `enum.13` without carrying the enum table (the mini-module the
//!   flip actually compiles has its own local tables; the dumped artifact does
//!   not). Its faithfulness is recorded per chain as an
//!   [`EnumModel`](clean_verify::ir_semdiff::EnumModel) and, for payload-bearing
//!   types, mechanically guarded by `payload_is_unread`.
//! * an **execution harness** `fn(u8 tag) -> R` that allocas the enum, stores
//!   the tag at offset 0 (trust-ir's canonical tagged-union layout puts the tag
//!   there), and calls the subject. It exists because `execute_function` builds
//!   a fresh state and there is no other way to hand the body a live pointer.
//!
//! The harness's own 4 instructions are subtracted, so the reported step count
//! is the SUBJECT body's alone.
//!
//! ## A defect found while building this
//!
//! `trust_ir::parser::parse_module` cannot read `trust_ir`'s own printed output
//! for a Rust def-path name: `fn @mode::CleanMode::has_cubical_layer` fails at
//! the first `:` with `expected '('`. The round trip
//! print → parse is therefore NOT total over the names the producer emits.
//! Reported in the run output; worked around here by renaming the subject,
//! which the interpreter never reads.

use clean_verify::ir_semdiff::{ArgShape, RunResult};
use trust_ir::inst::Inst;
use trust_ir::interpret::{InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, Function, Module};

/// Instructions the harness itself executes, per argument shape. Subtracted so
/// the reported count is the SUBJECT body's alone.
///
/// `PointerCell`: alloca, store, call, ret.
/// `ValueAggregate`: alloca, store, load, call, extractfield, ret — the extra
/// `load` materializes a well-formed aggregate to pass by value, and the extra
/// `extractfield` reduces the returned aggregate to its tag so both sides
/// compare the same observation.
pub const fn harness_steps(shape: ArgShape) -> u64 {
    match shape {
        ArgShape::PointerCell => 4,
        ArgShape::ValueAggregate => 6,
    }
}

/// The name the subject is renamed to so trust-ir's parser can read it.
const SUBJECT: &str = "g2_subject";

/// A `FuncId` far above anything a single-body fixture uses, so the harness can
/// never collide with the subject.
const HARNESS_FUNC_ID: u32 = 0x000f_ffff;

/// Build the interpretable module: header + enum declaration + the verbatim
/// fixture body with only its NAME rewritten.
///
/// Returns the module and the subject's own text (for the payload guard).
pub fn build_module(
    fixture_text: &str,
    original_name: &str,
    enum_decls: &str,
    ret_ty: Ty,
    shape: ArgShape,
    arg_enum: u32,
) -> Result<(Module, String), String> {
    let renamed = fixture_text.replace(original_name, &format!("@{SUBJECT}"));
    let text =
        format!("; TrustIr text format v1\nmodule \"crystal_a3\"\n\n{enum_decls}\n\n{renamed}");
    let mut module = trust_ir::parser::parse_module(&text)
        .map_err(|e| format!("trust-ir parser rejected the composed module: {e}"))?;
    if module.functions.len() != 1 {
        return Err(format!(
            "expected exactly one function in the fixture, got {}",
            module.functions.len()
        ));
    }
    // The crate-level dump names the subject's signature by its ASSEMBLED index
    // (`functy.0` for one body, `functy.470` for another) but carries no functy
    // table, so the table has to be reconstituted here. Size it to the index the
    // subject actually declares and place the signature there; the harness takes
    // the next slot. Getting this wrong is a `signature_mismatch` fault, which is
    // reported as an absent trust leg rather than silently skipped.
    let subject_ty = module
        .functions
        .first()
        .map(|f| f.ty.index() as usize)
        .ok_or_else(|| "no subject function".to_owned())?;
    let harness_slot = subject_ty + 1;
    let placeholder = FuncTy {
        params: Vec::new(),
        returns: Vec::new(),
        is_vararg: false,
    };
    module.func_types = vec![placeholder; harness_slot + 1];
    let enum_ty = Ty::Enum(arg_enum_id(&module, arg_enum)?);
    module.func_types[subject_ty] = FuncTy {
        params: vec![match shape {
            ArgShape::PointerCell => Ty::Ptr,
            ArgShape::ValueAggregate => enum_ty,
        }],
        returns: vec![ret_ty],
        is_vararg: false,
    };
    // The harness takes a `u8` tag. It returns whatever the SUBJECT returns,
    // except that an enum return is projected to its `u8` tag first — so every
    // chain reports one observation shape without ever declaring a signature the
    // body does not have. (Declaring `u8` unconditionally is a
    // `signature_mismatch`, which this gate caught rather than passed.)
    let harness_ret = match &module.func_types[subject_ty].returns[..] {
        [Ty::Enum(_)] => Ty::U8,
        [other] => other.clone(),
        _ => return Err("subject must return exactly one value".to_owned()),
    };
    module.func_types[harness_slot] = FuncTy {
        params: vec![Ty::U8],
        returns: vec![harness_ret],
        is_vararg: false,
    };
    Ok((module, renamed))
}

/// The `EnumId` of the argument enum, chosen by DECLARED id rather than by
/// position.
///
/// `from_source_system` needs two enum declarations — `enum.178` for its
/// parameter and `enum.13` for its result — so "the first one" is not a
/// well-defined answer, and picking wrong is a `type_error` rather than a
/// silent mis-measurement.
fn arg_enum_id(module: &Module, declared: u32) -> Result<trust_ir::value::EnumId, String> {
    module
        .enums
        .iter()
        .find(|e| e.id.index() == declared)
        .map(|e| e.id)
        .ok_or_else(|| format!("no enum with declared id {declared} in the composed module"))
}

/// Append the `fn(u8) -> R` execution harness and return it.
pub fn attach_harness(
    module: &mut Module,
    shape: ArgShape,
    arg_enum: u32,
) -> Result<Function, String> {
    let subject = module
        .functions
        .first()
        .ok_or_else(|| "no subject function".to_owned())?
        .clone();
    let harness_slot = u32::try_from(module.func_types.len().saturating_sub(1))
        .map_err(|_| "functy table too large".to_owned())?;
    let enum_ty = Ty::Enum(arg_enum_id(module, arg_enum)?);
    let ret_ty = module
        .func_types
        .get(subject.ty.index() as usize)
        .and_then(|ft| ft.returns.first())
        .cloned()
        .ok_or_else(|| "subject has no return type".to_owned())?;

    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), Ty::U8));
    entry.body.push(
        InstrNode::new(Inst::Alloca {
            ty: enum_ty.clone(),
            count: None,
            align: None,
        })
        .with_result(ValueId::new(1)),
    );
    // The tag occupies offset 0 of trust-ir's canonical tagged-union layout.
    entry.body.push(InstrNode::new(Inst::Store {
        ty: Ty::U8,
        ptr: ValueId::new(1),
        value: ValueId::new(0),
        volatile: false,
        align: None,
    }));

    // Argument: the pointer itself, or a well-formed aggregate loaded from it.
    let arg = match shape {
        ArgShape::PointerCell => ValueId::new(1),
        ArgShape::ValueAggregate => {
            entry.body.push(
                InstrNode::new(Inst::Load {
                    ty: enum_ty,
                    ptr: ValueId::new(1),
                    volatile: false,
                    align: None,
                })
                .with_result(ValueId::new(3)),
            );
            ValueId::new(3)
        }
    };
    entry.body.push(
        InstrNode::new(Inst::Call {
            callee: subject.id,
            args: vec![arg],
        })
        .with_result(ValueId::new(2)),
    );

    // Reduce an enum return to its tag so every chain reports one shape.
    let returned = if matches!(ret_ty, Ty::Enum(_)) {
        entry.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: Ty::U8,
                aggregate: ValueId::new(2),
                field: 0,
            })
            .with_result(ValueId::new(4)),
        );
        ValueId::new(4)
    } else {
        ValueId::new(2)
    };
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![returned],
    }));

    let harness = Function {
        id: FuncId::new(HARNESS_FUNC_ID),
        name: "g2_harness".to_owned(),
        ty: FuncTyId::new(harness_slot),
        entry: BlockId::new(0),
        blocks: vec![entry],
        ..subject
    };
    module.functions.push(harness.clone());
    Ok(harness)
}

/// Run the subject on one input tag.
///
/// Returns the value and the SUBJECT's step count (harness overhead removed).
/// A fault is a first-class answer — `Fault(code)` — never a skipped row.
///
/// `overhead_bias` perturbs the subtracted harness overhead. It is `0` on every
/// real run; the cost-mutation battery passes a nonzero value to falsify the
/// COST gate against the quantity the gate actually measures, rather than
/// against a hardcoded probe. Taking it as a parameter is what makes that
/// mutation possible without a second copy of this function.
pub fn run(
    module: &Module,
    harness: &Function,
    shape: ArgShape,
    tag: u32,
    overhead_bias: i64,
) -> (RunResult, Option<u32>) {
    let interp = Interpreter::with_module(module);
    let arg = match InterpretValue::int(Ty::U8, i128::from(tag)) {
        Ok(v) => v,
        Err(e) => return (RunResult::Fault(format!("arg:{}", e.code.as_str())), None),
    };
    match interp.execute_function(harness, vec![arg]) {
        Ok(outcome) => {
            let subtract = harness_steps(shape).saturating_add_signed(overhead_bias);
            let steps = u32::try_from(outcome.steps.saturating_sub(subtract)).ok();
            let value = match outcome.returns.first() {
                Some(v) => match &v.kind {
                    InterpretValueKind::Bool(b) => RunResult::Bool(*b),
                    InterpretValueKind::Int(i) => match u32::try_from(i.as_unsigned()) {
                        Ok(n) => RunResult::Int(n),
                        Err(_) => RunResult::Fault("int_too_wide".to_owned()),
                    },
                    other => RunResult::Fault(format!("unmapped_value:{other:?}")),
                },
                None => RunResult::Fault("no_return_value".to_owned()),
            };
            (value, steps)
        }
        Err(e) => (RunResult::Fault(e.code.as_str().to_owned()), None),
    }
}
