// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! SMT-LIB transport for the shared integer division semantics.

use clean_auto::bridge::proof_translation_contract::{
    integer_quotient, integer_remainder, IntDivisionRounding, IntegerDivisionOps,
};

struct SmtIntegerOps;

impl IntegerDivisionOps for SmtIntegerOps {
    type Term = String;
    fn zero(&mut self) -> String {
        "0".to_string()
    }
    fn eq(&mut self, lhs: String, rhs: String) -> String {
        format!("(= {lhs} {rhs})")
    }
    fn lt(&mut self, lhs: String, rhs: String) -> String {
        format!("(< {lhs} {rhs})")
    }
    fn neg(&mut self, value: String) -> String {
        format!("(- {value})")
    }
    fn mul(&mut self, lhs: String, rhs: String) -> String {
        format!("(* {lhs} {rhs})")
    }
    fn sub(&mut self, lhs: String, rhs: String) -> String {
        format!("(- {lhs} {rhs})")
    }
    fn div(&mut self, lhs: String, rhs: String) -> String {
        format!("(div {lhs} {rhs})")
    }
    fn modulo(&mut self, lhs: String, rhs: String) -> String {
        format!("(mod {lhs} {rhs})")
    }
    fn ite(&mut self, condition: String, yes: String, no: String) -> String {
        format!("(ite {condition} {yes} {no})")
    }
}

pub(super) fn quotient(lhs: String, rhs: String, rounding: IntDivisionRounding) -> String {
    integer_quotient(&mut SmtIntegerOps, lhs, rhs, rounding)
}

pub(super) fn remainder(lhs: String, rhs: String, rounding: IntDivisionRounding) -> String {
    integer_remainder(&mut SmtIntegerOps, lhs, rhs, rounding)
}
