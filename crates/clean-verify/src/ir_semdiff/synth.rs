// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Clean-side obligation generation for the W2a **synthetic-module** lane of
//! the GAP-2 differential (`docs/analysis/evalir-completion-plan-2026-08-24.md`
//! §5 W2a), plus the minimal outcome-vocabulary map that lane needs.
//!
//! The W1 wide builders ([`super::wide`]) phrase only `IROutcome.ret` rows,
//! because every W1 fixture returns a value on every measured input. The W2a
//! constructors do not: `unreachable`'s entire semantics is a UB halt, the
//! `extractelement` out-of-bounds edge is a fault, and the `undef` chain's
//! honest Clean answer is `ret [undef_]` — a value [`super::RunResult`] has no
//! encoding for. So this module adds ONE typed outcome vocabulary and ONE
//! obligation builder over it; nothing here decides agreement.
//!
//! ## The outcome map, and its measured limit
//!
//! Plan §4(b) calls for "an outcome-vocabulary map so UB/stuck rows compare":
//! Clean's `IROutcome` families against `trust_ir::interpret`'s
//! `InterpretErrorCode`. This is the W2a-sized subset — two classes, measured
//! against the pinned trust-ir rev (`a4e81b6`) rather than assumed:
//!
//! * Clean `IROutcome.ub _` ↔ interpreter `undefined_behavior` — agree on
//!   `unreachable` ("executed unreachable", `interpret.rs:996-1000`).
//! * Clean `IROutcome.type_error _` ↔ interpreter `type_error`.
//!
//! **The map is NOT total and the residue is a finding, not a rounding.**
//! Measured on the same rev: the interpreter reports an out-of-bounds
//! `extractelement` as `undefined_behavior` (`eval_extract_element`,
//! `interpret.rs:4507-4516`) where Clean's `ir_ef_at` fails closed with
//! `type_error bad_field` — a genuine class divergence between the two
//! executors, which the battery records as a DECLARED delta row rather than
//! smoothing into either class. And the interpreter refuses to EXECUTE
//! `Inst::Undef` at all ("executing undef would read an undefined value",
//! `interpret.rs:619-623`, code `undefined_behavior`) where Clean's dispatch
//! arm binds `IRScalar.undef_` and continues — so the `undef` constructor has
//! no measurable E2 leg on this rev, recorded per row, never folded into
//! agreement.

use super::obligations::RunResult;
use super::wide::{wide_ret_values, WideEncoding};
use super::DiffError;

/// The Clean `IRFault` constructors the synthetic lane's obligations may name.
///
/// A closed enum rather than a free string, so a typo'd fault name is a compile
/// error here instead of an elaboration failure misread as a disagreement on
/// the big box.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IrFaultName {
    /// `IRFault.unreachable` — executing `IRInst.unreachable`.
    Unreachable,
    /// `IRFault.bad_field` — an aggregate read past the spine's end.
    BadField,
    /// `IRFault.not_bool` — a non-boolean where a condition was required.
    NotBool,
    /// `IRFault.not_int` — a non-integer where an integer was required.
    NotInt,
    /// `IRFault.not_agg` — a scalar where an aggregate was required.
    NotAgg,
    /// `IRFault.uninit` — reading a cell that was never written (the W2b
    /// `alloca` chain's fresh-cell edge). NOTE the measured fault-SITE split
    /// this name sits on: Clean faults at the LOAD of the undef_ cell, while
    /// the reference interpreter's plain load yields inert PartialBytes poison
    /// and faults `undefined_behavior` only where the value is INSPECTED
    /// (`reject_partial`, trust-ir `a4e81b6` `interpret.rs:5402-5403`) — same
    /// class, different trace step, recorded in the chain rather than
    /// smoothed.
    Uninit,
    /// `IRFault.not_ptr` — a non-pointer where a pointer was required.
    NotPtr,
    /// `IRFault.null_deref` — dereferencing (or calling through) the null
    /// pointer: the W2c `callindirect` null-callee edge. NOTE the measured
    /// CODE split this name sits on: Clean pins `ub null_deref` where the
    /// reference interpreter reports its own `invalid_function_pointer` code,
    /// not `undefined_behavior` (trust-ir `a4e81b6`,
    /// `interpret.rs:1415-1421`) — outside the two-class map, so the battery
    /// carries that row as a DECLARED delta, never class agreement.
    NullDeref,
}

impl IrFaultName {
    /// The registered `IRFault` constructor's name.
    #[must_use]
    pub fn term(self) -> &'static str {
        match self {
            IrFaultName::Unreachable => "IRFault.unreachable",
            IrFaultName::BadField => "IRFault.bad_field",
            IrFaultName::NotBool => "IRFault.not_bool",
            IrFaultName::NotInt => "IRFault.not_int",
            IrFaultName::NotAgg => "IRFault.not_agg",
            IrFaultName::Uninit => "IRFault.uninit",
            IrFaultName::NotPtr => "IRFault.not_ptr",
            IrFaultName::NullDeref => "IRFault.null_deref",
        }
    }
}

/// The full `IROutcome` a synthetic-lane row pins on the Clean side.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SynthOutcome {
    /// `IROutcome.ret` of a value [`super::RunResult`] can encode.
    Ret(RunResult),
    /// `IROutcome.ret (ir_vl1 IRScalar.undef_)` — the `undef` chain's honest
    /// answer: the machine binds an undef value and RETURNS it, which is what
    /// distinguishes Clean's arm from the interpreter's refusal to execute it.
    RetUndef,
    /// `IROutcome.ub <fault>`.
    Ub(IrFaultName),
    /// `IROutcome.type_error <fault>`.
    TypeError(IrFaultName),
}

impl SynthOutcome {
    /// The Clean `IROutcome` term, or a refusal for an unencodable `Ret`.
    ///
    /// # Errors
    /// [`DiffError::UnmappedResult`] when a `Ret` payload has no Clean
    /// encoding under `encoding` (a fault is not a `ret` and must be phrased
    /// as `Ub`/`TypeError` instead).
    pub fn clean_term(&self, encoding: WideEncoding) -> Result<String, DiffError> {
        match self {
            SynthOutcome::Ret(r) => wide_ret_values(r, encoding)
                .map(|values| format!("(IROutcome.ret {values})"))
                .ok_or_else(|| DiffError::UnmappedResult(r.to_string())),
            SynthOutcome::RetUndef => Ok("(IROutcome.ret (ir_vl1 IRScalar.undef_))".to_owned()),
            SynthOutcome::Ub(f) => Ok(format!("(IROutcome.ub {})", f.term())),
            SynthOutcome::TypeError(f) => Ok(format!("(IROutcome.type_error {})", f.term())),
        }
    }

    /// The class tag the differential rows compare at (the exact term is
    /// pinned by the kernel obligation and carried in the row's notes).
    #[must_use]
    pub fn class(&self) -> OutcomeClass {
        match self {
            SynthOutcome::Ret(_) | SynthOutcome::RetUndef => OutcomeClass::Ret,
            SynthOutcome::Ub(_) => OutcomeClass::Ub,
            SynthOutcome::TypeError(_) => OutcomeClass::TypeError,
        }
    }
}

/// The shared outcome classes non-`ret` rows compare at.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OutcomeClass {
    /// The run returned.
    Ret,
    /// Undefined behavior.
    Ub,
    /// A type error.
    TypeError,
}

impl OutcomeClass {
    /// The tag used in the differential rows' shared vocabulary.
    #[must_use]
    pub fn tag(self) -> &'static str {
        match self {
            OutcomeClass::Ret => "ret",
            OutcomeClass::Ub => "ub",
            OutcomeClass::TypeError => "type_error",
        }
    }
}

/// Map a trust-ir `InterpretErrorCode` string to the shared outcome class.
///
/// `None` for every code outside the measured two-class map — including the
/// whole `unsupported_*` family (an interpreter capability bound, not an
/// outcome) — so an unmapped code can only be handled as an explicit,
/// per-chain declared condition, never silently classed.
#[must_use]
pub fn e2_fault_class(code: &str) -> Option<OutcomeClass> {
    match code {
        "undefined_behavior" => Some(OutcomeClass::Ub),
        "type_error" => Some(OutcomeClass::TypeError),
        _ => None,
    }
}

/// The obligation pinning a synthetic chain's FULL outcome at a given fuel —
/// the fault-capable generalization of
/// [`super::wide::wide_value_obligation`], sharing its tail convention.
///
/// # Errors
/// [`DiffError::NumeralOutOfRange`] when `fuel` exceeds the named-numeral
/// pool; [`DiffError::UnmappedResult`] for an unencodable `Ret` payload.
pub fn synth_outcome_obligation(
    def_name: &str,
    module: &str,
    fid: &str,
    fuel: u32,
    tail: &str,
    outcome: &SynthOutcome,
    encoding: WideEncoding,
) -> Result<String, DiffError> {
    let rhs = outcome.clean_term(encoding)?;
    let fuel = super::obligations::ir_numeral(fuel)?;
    Ok(format!(
        "def {def_name} : @Eq IROutcome (ir_eval {fuel} {module} {fid} {tail}) {rhs} \
         := @Eq.refl IROutcome {rhs}"
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ub_outcome_names_the_fault_constructor() {
        let term = SynthOutcome::Ub(IrFaultName::Unreachable)
            .clean_term(WideEncoding::Scalar)
            .expect("ub is always encodable");
        assert_eq!(term, "(IROutcome.ub IRFault.unreachable)");
    }

    #[test]
    fn test_type_error_outcome_names_the_fault_constructor() {
        let term = SynthOutcome::TypeError(IrFaultName::BadField)
            .clean_term(WideEncoding::Scalar)
            .expect("type_error is always encodable");
        assert_eq!(term, "(IROutcome.type_error IRFault.bad_field)");
    }

    #[test]
    fn test_ret_undef_is_a_ret_of_the_undef_scalar() {
        let term = SynthOutcome::RetUndef
            .clean_term(WideEncoding::Scalar)
            .expect("ret undef is always encodable");
        assert_eq!(term, "(IROutcome.ret (ir_vl1 IRScalar.undef_))");
    }

    #[test]
    fn test_a_fault_run_result_refuses_as_a_ret() {
        let err = SynthOutcome::Ret(RunResult::Fault("x".to_owned()))
            .clean_term(WideEncoding::Scalar)
            .expect_err("a fault is not a ret; it must be phrased as Ub/TypeError");
        assert!(matches!(err, DiffError::UnmappedResult(_)));
    }

    #[test]
    fn test_the_outcome_obligation_is_an_eq_refl_over_the_supplied_tail() {
        let src = synth_outcome_obligation(
            "probe",
            "ir_w2a_ur_module",
            "ir_d0",
            2,
            "(ir_vl1 (IRScalar.bool_ Bool.false)) ir_mem0 ir_d0",
            &SynthOutcome::Ub(IrFaultName::Unreachable),
            WideEncoding::Scalar,
        )
        .expect("ub at fuel 2 is encodable");
        assert!(
            src.contains(
                "ir_eval ir_d2 ir_w2a_ur_module ir_d0 \
                 (ir_vl1 (IRScalar.bool_ Bool.false)) ir_mem0 ir_d0"
            ),
            "{src}"
        );
        assert!(
            src.contains(":= @Eq.refl IROutcome (IROutcome.ub IRFault.unreachable)"),
            "{src}"
        );
    }

    #[test]
    fn test_w2b_fault_names_term_to_their_constructors() {
        assert_eq!(IrFaultName::Uninit.term(), "IRFault.uninit");
        assert_eq!(IrFaultName::NotPtr.term(), "IRFault.not_ptr");
    }

    #[test]
    fn test_w2c_fault_name_terms_to_its_constructor() {
        assert_eq!(IrFaultName::NullDeref.term(), "IRFault.null_deref");
        let term = SynthOutcome::Ub(IrFaultName::NullDeref)
            .clean_term(WideEncoding::Scalar)
            .expect("ub is always encodable");
        assert_eq!(term, "(IROutcome.ub IRFault.null_deref)");
    }

    #[test]
    fn test_the_e2_class_map_is_partial_on_purpose() {
        assert_eq!(e2_fault_class("undefined_behavior"), Some(OutcomeClass::Ub));
        assert_eq!(e2_fault_class("type_error"), Some(OutcomeClass::TypeError));
        assert_eq!(e2_fault_class("unsupported_instruction"), None);
        assert_eq!(e2_fault_class("panic"), None);
        assert_eq!(e2_fault_class("out_of_fuel"), None);
    }

    #[test]
    fn test_classes_partition_the_synth_outcomes() {
        assert_eq!(
            SynthOutcome::Ret(RunResult::Int(3)).class(),
            OutcomeClass::Ret
        );
        assert_eq!(SynthOutcome::RetUndef.class(), OutcomeClass::Ret);
        assert_eq!(
            SynthOutcome::Ub(IrFaultName::Unreachable).class(),
            OutcomeClass::Ub
        );
        assert_eq!(
            SynthOutcome::TypeError(IrFaultName::NotInt).class(),
            OutcomeClass::TypeError
        );
    }
}
