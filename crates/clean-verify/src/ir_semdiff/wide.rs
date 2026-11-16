// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Clean-side obligation generation for the W1 **fixture-widening** lane of the
//! GAP-2 differential (`docs/analysis/evalir-completion-plan-2026-08-24.md` §5
//! W1).
//!
//! The original obligations ([`super::obligations`]) phrase exactly two call
//! shapes — a one-cell pointer heap and a single by-value enum — because the
//! first three chains had exactly those shapes. The nine W1 constructors live
//! in bodies with three `u32` parameters, by-value one-field structs, a
//! two-function module reached at two different function ids, a mutating body
//! against a prepared heap, and a nullary constant body. Rather than grow a
//! closed `ArgShape` enum by seven variants, the wide obligation takes the
//! **argument/heap/next-address tail of the `ir_eval` application as text**,
//! written per input by the chain table from the SAME encodings the committed
//! concrete witnesses use (`ir_br_correct_witness`, `ir_sm_on_true`,
//! `ir_pv_on_custom_seven`, …). Nothing here decides agreement; every function
//! emits an `Eq.refl` the Clean kernel discharges by reducing `ir_eval`, or a
//! refusal.
//!
//! **The numeral bound binds NAMES, not values.** `ir_d<N>` stops at 16, so
//! probed FUEL stays within [`super::MAX_IR_NUMERAL`] (every W1 chain's
//! measured threshold is ≤ 13). Argument and result VALUES are raw decimal
//! literals when large — the encoding the committed witnesses already use
//! (`4294967295`, `17592186044416`) and the reason a `u32::MAX` sentinel row
//! is phrasable at all.

use super::obligations::{ir_nat_term, ir_numeral, RunResult};
use super::DiffError;

/// How a returned value is wrapped on the Clean side of a wide chain.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WideEncoding {
    /// The scalar itself: `IRScalar.bool_` / `IRScalar.int_`.
    Scalar,
    /// A one-field aggregate carrying an integer — the runtime value of a
    /// one-field struct like `FlatFlags` (`ir_fc_val` in the registered
    /// stages): `IRScalar.aggv (IRScalar.vcons (IRScalar.int_ n)
    /// IRScalar.vnil)`. Declared per chain, never inferred: `int 3` and
    /// `struct { 3 }` are different Clean terms and comparing the wrong one
    /// would be a spurious disagreement.
    AggInt,
}

/// The `IROutcome.ret` payload term for a measured result.
///
/// `None` for a fault (no `ret` outcome exists to phrase) — the caller must
/// treat that as a refusal, never as a comparison.
#[must_use]
pub fn wide_ret_values(result: &RunResult, encoding: WideEncoding) -> Option<String> {
    match (result, encoding) {
        (RunResult::Unit, _) => Some("(@IRList.nil IRScalar)".to_owned()),
        (RunResult::Bool(b), WideEncoding::Scalar) => Some(format!(
            "(ir_vl1 (IRScalar.bool_ Bool.{}))",
            if *b { "true" } else { "false" }
        )),
        (RunResult::Int(n), WideEncoding::Scalar) => {
            Some(format!("(ir_vl1 (IRScalar.int_ {}))", ir_nat_term(*n)))
        }
        (RunResult::Float(n), WideEncoding::Scalar) => {
            Some(format!("(ir_vl1 (IRScalar.float_ {}))", ir_nat_term(*n)))
        }
        (RunResult::Int(n) | RunResult::EnumTag(n), WideEncoding::AggInt) => Some(format!(
            "(ir_vl1 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ {}) IRScalar.vnil)))",
            ir_nat_term(*n)
        )),
        (RunResult::EnumTag(n), WideEncoding::Scalar) => {
            Some(format!("(ir_vl1 (ir_var {} ir_sp0))", ir_nat_term(*n)))
        }
        // A multi-value return: the ret payload is the cons spine of the
        // elements' scalar terms, in order — the W3 overflow lane's six-value
        // `ret`. Any element without a scalar encoding (a nested Many, a
        // Unit, a Fault) refuses the whole list; and the AggInt wrapper is a
        // ONE-field-struct convention, so a Many under it refuses rather
        // than guessing which element the struct was.
        (RunResult::Many(vs), WideEncoding::Scalar) => {
            let mut out = "(@IRList.nil IRScalar)".to_owned();
            for v in vs.iter().rev() {
                out = format!("(@IRList.cons IRScalar {} {out})", v.clean_scalar()?);
            }
            Some(out)
        }
        (RunResult::Bool(_) | RunResult::Many(_) | RunResult::Float(_), WideEncoding::AggInt)
        | (RunResult::Fault(_), _) => None,
    }
}

/// The obligation that pins the returned VALUE of a wide chain at a given fuel.
///
/// `tail` is the `<args> <heap> <next-addr>` portion of the `ir_eval`
/// application, verbatim; `fid` is the function id term (`ir_d0`, or `ir_d1`
/// for the callee row of a two-function module).
///
/// # Errors
/// [`DiffError::NumeralOutOfRange`] when `fuel` exceeds the named-numeral pool;
/// [`DiffError::UnmappedResult`] for a result with no Clean `ret` encoding.
pub fn wide_value_obligation(
    def_name: &str,
    module: &str,
    fid: &str,
    fuel: u32,
    tail: &str,
    result: &RunResult,
    encoding: WideEncoding,
) -> Result<String, DiffError> {
    let values = wide_ret_values(result, encoding)
        .ok_or_else(|| DiffError::UnmappedResult(result.to_string()))?;
    let fuel = ir_numeral(fuel)?;
    let rhs = format!("(IROutcome.ret {values})");
    Ok(format!(
        "def {def_name} : @Eq IROutcome (ir_eval {fuel} {module} {fid} {tail}) {rhs} \
         := @Eq.refl IROutcome {rhs}"
    ))
}

/// The obligation that the machine has NOT yet finished at a given fuel —
/// the wide form of [`super::fuel_out_obligation`], used to show a measured
/// threshold is needed and not merely sufficient.
///
/// # Errors
/// [`DiffError::NumeralOutOfRange`] when `fuel` exceeds the named-numeral pool.
pub fn wide_fuel_out_obligation(
    def_name: &str,
    module: &str,
    fid: &str,
    fuel: u32,
    tail: &str,
) -> Result<String, DiffError> {
    let fuel = ir_numeral(fuel)?;
    Ok(format!(
        "def {def_name} : @Eq IROutcome (ir_eval {fuel} {module} {fid} {tail}) IROutcome.fuel_out \
         := @Eq.refl IROutcome IROutcome.fuel_out"
    ))
}

/// The Clean argument-list term for a sequence of scalar terms — an inlined
/// `IRList.cons` spine, so wide chains depend on no stage-registered list
/// helper beyond what the minimal `EvalIr` bundle carries.
#[must_use]
pub fn wide_args(scalars: &[String]) -> String {
    let mut out = "(@IRList.nil IRScalar)".to_owned();
    for s in scalars.iter().rev() {
        out = format!("(@IRList.cons IRScalar {s} {out})");
    }
    out
}

/// `IRScalar.int_ n`, with the literal/name split of [`ir_nat_term`].
#[must_use]
pub fn wide_int(n: u64) -> String {
    format!("(IRScalar.int_ {})", ir_nat_term(n))
}

/// `IRScalar.bool_ b` — the W2a synthetic lane's `select`/`condbr` condition
/// arguments arrive as first-class booleans rather than through an enum cell.
#[must_use]
pub fn wide_bool(b: bool) -> String {
    format!("(IRScalar.bool_ Bool.{})", if b { "true" } else { "false" })
}

/// `IRScalar.float_ bits` — the W4 fcmp lane's binary64 arguments. A bit
/// pattern exceeds the named-numeral pool by ~17 orders of magnitude, so it
/// rides the raw-literal half of [`ir_nat_term`] — the committed encoding
/// (`ir_f64_sign_bit` is spelled as its literal for the same reason: the
/// kernel folds literals natively on `BigNat`, and the comparisons that
/// consume them are the folded `ir_nat_ltb`/`ir_nat_eqb`, never a walk).
#[must_use]
pub fn wide_float(bits: u64) -> String {
    format!("(IRScalar.float_ {})", ir_nat_term(bits))
}

/// `IRScalar.unit_` — the W2b `ptrfromparts` chain passes the thin rebuild's
/// unit metadata as a first-class argument (trust-ir spells the type `()`).
#[must_use]
pub fn wide_unit() -> String {
    "IRScalar.unit_".to_owned()
}

/// `IRScalar.fnptr_ f` — the W2c `callindirect` chain passes its callee as a
/// first-class function-pointer argument, so one caller body dispatches to
/// either companion callee purely through the VALUE (the property under
/// measure).
#[must_use]
pub fn wide_fnptr(f: u64) -> String {
    format!("(IRScalar.fnptr_ {})", ir_nat_term(f))
}

/// `IRScalar.nullptr_` — the W2c null-callee edge's argument.
#[must_use]
pub fn wide_nullptr() -> String {
    "IRScalar.nullptr_".to_owned()
}

/// An n-field integer aggregate — the inline `vcons` spine EvalIR uses for
/// every aggregate value (`eval_ir_syntax.rs`: "aggregates are inline spine
/// values, no second store"). The W2a `extractelement` chain passes its
/// element container this way; [`wide_agg1`] is the one-field special case the
/// W1 struct chains already use.
#[must_use]
pub fn wide_agg(fields: &[u64]) -> String {
    let mut spine = "IRScalar.vnil".to_owned();
    for f in fields.iter().rev() {
        spine = format!(
            "(IRScalar.vcons (IRScalar.int_ {}) {spine})",
            ir_nat_term(*f)
        );
    }
    format!("(IRScalar.aggv {spine})")
}

/// A one-field integer aggregate — the runtime value of a one-field struct
/// (`FlatFlags` / `ExprMeta` / `NodeId`), inlined.
#[must_use]
pub fn wide_agg1(n: u64) -> String {
    format!(
        "(IRScalar.aggv (IRScalar.vcons (IRScalar.int_ {}) IRScalar.vnil))",
        ir_nat_term(n)
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wide_args_inlines_the_cons_spine_in_order() {
        let args = wide_args(&[wide_int(3), wide_int(1), wide_int(5)]);
        assert_eq!(
            args,
            "(@IRList.cons IRScalar (IRScalar.int_ ir_d3) \
             (@IRList.cons IRScalar (IRScalar.int_ ir_d1) \
             (@IRList.cons IRScalar (IRScalar.int_ ir_d5) (@IRList.nil IRScalar))))"
        );
    }

    #[test]
    fn test_large_values_are_literals_not_names() {
        assert_eq!(wide_int(4_294_967_295), "(IRScalar.int_ 4294967295)");
        assert_eq!(wide_int(7), "(IRScalar.int_ ir_d7)");
    }

    #[test]
    fn test_bool_scalars_use_the_bool_constructors() {
        assert_eq!(wide_bool(true), "(IRScalar.bool_ Bool.true)");
        assert_eq!(wide_bool(false), "(IRScalar.bool_ Bool.false)");
    }

    #[test]
    fn test_agg_inlines_the_vcons_spine_in_field_order() {
        assert_eq!(
            wide_agg(&[5, 11, 2]),
            "(IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d5) \
             (IRScalar.vcons (IRScalar.int_ ir_d11) \
             (IRScalar.vcons (IRScalar.int_ ir_d2) IRScalar.vnil))))"
        );
        assert_eq!(wide_agg(&[]), "(IRScalar.aggv IRScalar.vnil)");
    }

    #[test]
    fn test_float_scalars_ride_the_literal_or_name_split() {
        assert_eq!(
            wide_float(4_607_182_418_800_017_408),
            "(IRScalar.float_ 4607182418800017408)"
        );
        assert_eq!(wide_float(0), "(IRScalar.float_ ir_d0)");
    }

    /// A float RETURN encodes as the `IRScalar.float_` pattern — singly and
    /// inside a `Many` spine (the float-residue lane's two- and three-value
    /// rets) — and refuses under the one-field-struct wrapper.
    #[test]
    fn test_float_returns_encode_as_patterns() {
        let single = wide_ret_values(
            &RunResult::Float(4_607_182_418_800_017_408),
            WideEncoding::Scalar,
        )
        .expect("a float return has a ret encoding");
        assert_eq!(single, "(ir_vl1 (IRScalar.float_ 4607182418800017408))");
        let many = wide_ret_values(
            &RunResult::Many(vec![
                RunResult::Float(0),
                RunResult::Float(9_223_372_036_854_775_808),
            ]),
            WideEncoding::Scalar,
        )
        .expect("a float pair has a ret encoding");
        assert_eq!(
            many,
            "(@IRList.cons IRScalar (IRScalar.float_ ir_d0) \
             (@IRList.cons IRScalar (IRScalar.float_ 9223372036854775808) (@IRList.nil IRScalar)))"
        );
        assert!(wide_ret_values(&RunResult::Float(3), WideEncoding::AggInt).is_none());
    }

    #[test]
    fn test_fnptr_and_nullptr_scalars_use_the_pointer_constructors() {
        assert_eq!(wide_fnptr(2), "(IRScalar.fnptr_ ir_d2)");
        assert_eq!(wide_nullptr(), "IRScalar.nullptr_");
    }

    #[test]
    fn test_unit_result_encodes_the_empty_ret() {
        let values = wide_ret_values(&RunResult::Unit, WideEncoding::Scalar)
            .expect("unit has a ret encoding");
        assert_eq!(values, "(@IRList.nil IRScalar)");
    }

    #[test]
    fn test_agg_encoding_wraps_the_int_in_a_one_field_spine() {
        let values = wide_ret_values(&RunResult::Int(14), WideEncoding::AggInt)
            .expect("agg int has a ret encoding");
        assert!(values.contains("IRScalar.aggv"), "{values}");
        assert!(values.contains("(IRScalar.int_ ir_d14)"), "{values}");
    }

    #[test]
    fn test_a_fault_refuses_rather_than_encodes() {
        assert!(wide_ret_values(&RunResult::Fault("x".to_owned()), WideEncoding::Scalar).is_none());
    }

    #[test]
    fn test_many_encodes_the_ret_payload_spine_in_order() {
        let values = wide_ret_values(
            &RunResult::Many(vec![RunResult::Int(5), RunResult::Bool(false)]),
            WideEncoding::Scalar,
        )
        .expect("a scalar pair has a ret encoding");
        assert_eq!(
            values,
            "(@IRList.cons IRScalar (IRScalar.int_ ir_d5) \
             (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.nil IRScalar)))"
        );
    }

    #[test]
    fn test_many_with_an_unencodable_element_refuses() {
        assert!(wide_ret_values(
            &RunResult::Many(vec![RunResult::Int(5), RunResult::Unit]),
            WideEncoding::Scalar,
        )
        .is_none());
        assert!(wide_ret_values(
            &RunResult::Many(vec![RunResult::Int(5), RunResult::Bool(true)]),
            WideEncoding::AggInt,
        )
        .is_none());
    }

    #[test]
    fn test_value_obligation_is_an_eq_refl_over_the_supplied_tail() {
        let src = wide_value_obligation(
            "probe",
            "ir_br_module",
            "ir_d0",
            9,
            "(ir_vl1 (IRScalar.int_ ir_d3)) ir_mem0 ir_d0",
            &RunResult::Bool(true),
            WideEncoding::Scalar,
        )
        .expect("bool at fuel 9 is encodable");
        assert!(
            src.contains(
                "ir_eval ir_d9 ir_br_module ir_d0 (ir_vl1 (IRScalar.int_ ir_d3)) ir_mem0 ir_d0"
            ),
            "{src}"
        );
        assert!(src.contains("Eq.refl IROutcome"), "{src}");
    }

    #[test]
    fn test_fuel_beyond_the_name_pool_refuses() {
        let err = wide_fuel_out_obligation("probe", "m", "ir_d0", 17, "x")
            .expect_err("17 has no ir_d name");
        assert!(matches!(err, DiffError::NumeralOutOfRange(17)));
    }
}
