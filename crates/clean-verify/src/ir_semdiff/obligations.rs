// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Clean-side obligation generation for the GAP-2 differential.
//!
//! Every function here emits Clean source whose proof term is `Eq.refl`. That
//! is the whole point: the Clean **kernel** discharges it by *reducing*
//! `ir_eval` over the registered module, so acceptance is an execution of
//! Clean's semantics and not an assertion about it. Nothing in this file may
//! decide agreement — it only phrases the question.

use super::DiffError;

/// Largest `ir_d<N>` numeral the EvalIR spec defines
/// (`eval_ir_crystal.rs::add_eval_ir_numerals` registers 0..=16).
pub const MAX_IR_NUMERAL: u32 = 16;

/// The value a body returned, in the vocabulary both sides share.
///
/// Deliberately small: these are the result shapes the chained bodies actually
/// return. Anything else is a [`DiffError::UnmappedResult`] — a refusal, never
/// an approximation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RunResult {
    /// A `bool` return; Clean-side `IRScalar.bool_`.
    Bool(bool),
    /// An unsigned integer return; Clean-side `IRScalar.int_`.
    Int(u32),
    /// A fieldless-enum return, reduced to its variant tag; Clean-side
    /// `ir_var <tag> ir_sp0` — an aggregate scalar with an empty payload spine.
    EnumTag(u32),
    /// The run did not return. The string is the executor's own stable code.
    Fault(String),
}

impl core::fmt::Display for RunResult {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            RunResult::Bool(b) => write!(f, "bool {b}"),
            RunResult::Int(n) => write!(f, "int {n}"),
            RunResult::EnumTag(n) => write!(f, "enum tag {n}"),
            RunResult::Fault(c) => write!(f, "fault {c}"),
        }
    }
}

impl RunResult {
    /// The Clean `IRScalar` term for this result.
    ///
    /// `None` for a fault: a faulting run has no `ret` outcome, so there is no
    /// value obligation to phrase and the row must be handled as a refusal.
    #[must_use]
    pub(crate) fn clean_scalar(&self) -> Option<String> {
        match self {
            RunResult::Bool(true) => Some("(IRScalar.bool_ Bool.true)".to_owned()),
            RunResult::Bool(false) => Some("(IRScalar.bool_ Bool.false)".to_owned()),
            RunResult::Int(n) => Some(format!("(IRScalar.int_ {})", ir_numeral(*n).ok()?)),
            RunResult::EnumTag(n) => Some(format!("(ir_var {} ir_sp0)", ir_numeral(*n).ok()?)),
            RunResult::Fault(_) => None,
        }
    }
}

/// The `ir_d<N>` numeral name for `n`.
///
/// # Errors
/// [`DiffError::NumeralOutOfRange`] when `n > MAX_IR_NUMERAL`. Generating a
/// name the spec does not define would fail to elaborate for a reason that has
/// nothing to do with semantics, and would be misread as a disagreement.
pub(crate) fn ir_numeral(n: u32) -> Result<String, DiffError> {
    if n > MAX_IR_NUMERAL {
        return Err(DiffError::NumeralOutOfRange(n));
    }
    Ok(format!("ir_d{n}"))
}

/// A body reached by loading a one-cell heap through a pointer argument — the
/// shape shared by `has_cubical_layer`, `level_kind_ord` and
/// `expr_path_step_clone`.
///
/// The state is a single live cell at address 0 whose payload spine is `ir_sp0`
/// and whose variant tag is the input. That is exactly the heap
/// `EncodesCleanMode` / `EncodesLevelKindCell` describe, so the differential
/// runs the machine on the same states the chain's own theorems quantify over
/// rather than on a state invented for the test.
#[must_use]
pub(crate) fn ptr_cell_call(module: &str, fuel: &str, tag: &str) -> String {
    format!(
        "ir_eval {fuel} {module} ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) \
         (ir_cell ir_d0 (ir_var {tag} ir_sp0) ir_mem0) ir_d1"
    )
}

/// A body reached by passing the argument BY VALUE, with no heap at all — the
/// shape of `CleanMode::from_source_system`, whose parameter is `enum.175`
/// rather than a pointer.
///
/// Worth having as a separate shape rather than a special case: it exercises
/// `ir_bind_params` on an aggregate and reaches the switch with no `load` in
/// front of it, so a `load`-side misunderstanding cannot mask a switch-side one.
#[must_use]
pub(crate) fn value_arg_call(module: &str, fuel: &str, tag: &str) -> String {
    format!("ir_eval {fuel} {module} ir_d0 (ir_vl1 (ir_var {tag} ir_sp0)) ir_mem0 ir_d0")
}

/// How the body under test receives its argument.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArgShape {
    /// A pointer into a one-cell heap, which the body `load`s.
    PointerCell,
    /// The aggregate itself, passed directly as a parameter.
    ValueAggregate,
}

impl ArgShape {
    /// The `ir_eval` application for this shape.
    #[must_use]
    pub(crate) fn call(self, module: &str, fuel: &str, tag: &str) -> String {
        match self {
            ArgShape::PointerCell => ptr_cell_call(module, fuel, tag),
            ArgShape::ValueAggregate => value_arg_call(module, fuel, tag),
        }
    }
}

/// The obligation that pins the returned VALUE at a given fuel.
///
/// # Errors
/// Propagates [`ir_numeral`]; [`DiffError::UnmappedResult`] for a result shape
/// with no Clean encoding.
pub fn value_obligation(
    def_name: &str,
    module: &str,
    shape: ArgShape,
    fuel: u32,
    tag: u32,
    result: &RunResult,
) -> Result<String, DiffError> {
    let scalar = result
        .clean_scalar()
        .ok_or_else(|| DiffError::UnmappedResult(result.to_string()))?;
    let call = shape.call(module, &ir_numeral(fuel)?, &ir_numeral(tag)?);
    let rhs = format!("(IROutcome.ret (ir_vl1 {scalar}))");
    Ok(format!(
        "def {def_name} : Eq IROutcome ({call}) {rhs} := Eq.refl IROutcome {rhs}"
    ))
}

/// The obligation that the machine has NOT yet finished at a given fuel.
///
/// Used to find the exact threshold from below. `IROutcome.fuel_out` is its own
/// outcome — distinct from `ret` and from every fault, and refutable — which is
/// what lets a cost be *pinned* rather than merely bounded above.
///
/// # Errors
/// Propagates [`ir_numeral`].
pub fn fuel_out_obligation(
    def_name: &str,
    module: &str,
    shape: ArgShape,
    fuel: u32,
    tag: u32,
) -> Result<String, DiffError> {
    let call = shape.call(module, &ir_numeral(fuel)?, &ir_numeral(tag)?);
    Ok(format!(
        "def {def_name} : Eq IROutcome ({call}) IROutcome.fuel_out \
         := Eq.refl IROutcome IROutcome.fuel_out"
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ir_numeral_in_range_is_named() {
        assert_eq!(ir_numeral(0).expect("0 is in range"), "ir_d0");
        assert_eq!(ir_numeral(16).expect("16 is in range"), "ir_d16");
    }

    #[test]
    fn test_ir_numeral_out_of_range_refuses() {
        assert!(matches!(
            ir_numeral(17),
            Err(DiffError::NumeralOutOfRange(17))
        ));
    }

    #[test]
    fn test_value_obligation_is_an_eq_refl_over_the_measured_value() {
        let src = value_obligation(
            "probe",
            "ir_h2_module",
            ArgShape::PointerCell,
            6,
            2,
            &RunResult::Bool(true),
        )
        .expect("bool at fuel 6 tag 2 is encodable");
        assert!(src.contains("ir_eval ir_d6 ir_h2_module"), "{src}");
        assert!(src.contains("ir_var ir_d2 ir_sp0"), "{src}");
        assert!(
            src.contains("Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))"),
            "{src}"
        );
    }

    #[test]
    fn test_value_obligation_encodes_an_int_return() {
        let src = value_obligation(
            "probe",
            "ir_ko_module",
            ArgShape::PointerCell,
            6,
            3,
            &RunResult::Int(3),
        )
        .expect("int at fuel 6 tag 3 is encodable");
        assert!(src.contains("(IRScalar.int_ ir_d3)"), "{src}");
    }

    #[test]
    fn test_fault_has_no_ret_encoding_and_refuses() {
        let err = value_obligation(
            "probe",
            "m",
            ArgShape::PointerCell,
            6,
            0,
            &RunResult::Fault("type_error".to_owned()),
        )
        .expect_err("a fault has no `ret` outcome");
        assert!(matches!(err, DiffError::UnmappedResult(_)));
    }

    #[test]
    fn test_by_value_shape_has_no_heap_cell() {
        let src = value_obligation(
            "probe",
            "ir_fs_module",
            ArgShape::ValueAggregate,
            5,
            11,
            &RunResult::EnumTag(4),
        )
        .expect("enum tag at fuel 5 tag 11 is encodable");
        assert!(
            src.contains("(ir_vl1 (ir_var ir_d11 ir_sp0)) ir_mem0"),
            "{src}"
        );
        assert!(
            !src.contains("ir_cell"),
            "the by-value shape uses no heap: {src}"
        );
        assert!(src.contains("(ir_var ir_d4 ir_sp0)"), "{src}");
    }

    #[test]
    fn test_fuel_out_obligation_targets_the_exhaustion_outcome() {
        let src = fuel_out_obligation("probe", "ir_h2_module", ArgShape::PointerCell, 5, 2)
            .expect("fuel 5 tag 2 is encodable");
        assert!(src.contains("IROutcome.fuel_out"), "{src}");
        assert!(src.contains("ir_eval ir_d5"), "{src}");
    }
}
