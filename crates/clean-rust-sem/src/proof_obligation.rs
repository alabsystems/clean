// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused VIR-to-Lean proof obligations for assertion-like sites.

use crate::ownership::Place;
use crate::translate::translate_place;
use crate::vir::{
    AggregateConst, AssertMessage, BasicBlockId, BinOp, Body, ConstAggregateKind, Constant,
    Operand, RetagKind, Rvalue, ScalarValue, Stmt, Term,
};
use clean_kernel::Expr;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObligationSource {
    FunctionContract,
    Precondition,
    Postcondition,
    LoopInvariant,
    AssertionCheck,
    UnsafeBlock,
    Overflow,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofObligation {
    pub function: String,
    pub location: String,
    pub source: ObligationSource,
    pub preconditions: Vec<Expr>,
    pub postconditions: Vec<Expr>,
    pub invariants: Vec<Expr>,
}

impl ProofObligation {
    pub fn goal(&self) -> Expr {
        let mut conclusions = self.invariants.clone();
        conclusions.extend(self.postconditions.clone());
        self.preconditions
            .iter()
            .rev()
            .fold(conjoin(&conclusions), |goal, premise| {
                Expr::arrow(premise.clone(), goal)
            })
    }
}

#[derive(Debug, Clone, Default)]
pub struct VirToLean;

impl VirToLean {
    #[must_use]
    pub fn new() -> Self {
        Self
    }

    #[must_use]
    pub fn translate_term(&self, term: &Term) -> Option<Expr> {
        match term {
            Term::Assert {
                cond,
                expected,
                msg,
                ..
            } => Some(self.translate_assertion(cond, *expected, msg)),
            _ => None,
        }
    }

    pub fn translate_assertion(&self, cond: &Operand, expected: bool, msg: &AssertMessage) -> Expr {
        Expr::apps(
            Expr::const_str("RustVIR.assertion"),
            [
                self.translate_assert_message(msg),
                self.translate_operand(cond),
                bool_expr(expected),
            ],
        )
    }

    pub fn translate_unsafe_site(&self, place: &Place) -> Expr {
        Expr::app(
            Expr::const_str("RustVIR.unsafeSite"),
            translate_place(place),
        )
    }

    #[must_use]
    pub fn translate_assert_invariants(&self, msg: &AssertMessage) -> Vec<Expr> {
        match msg {
            AssertMessage::BoundsCheck { len, index } => vec![Expr::apps(
                Expr::const_str("RustVIR.inBounds"),
                [self.translate_operand(index), self.translate_operand(len)],
            )],
            AssertMessage::Overflow(op, lhs, rhs) => vec![Expr::apps(
                Expr::const_str("RustVIR.noOverflow"),
                [
                    Expr::str_lit(format!("{op:?}")),
                    self.translate_operand(lhs),
                    self.translate_operand(rhs),
                ],
            )],
            AssertMessage::OverflowNeg(operand) => vec![Expr::app(
                Expr::const_str("RustVIR.noNegOverflow"),
                self.translate_operand(operand),
            )],
            AssertMessage::DivisionByZero(operand) | AssertMessage::RemainderByZero(operand) => {
                vec![Expr::app(
                    Expr::const_str("RustVIR.nonZero"),
                    self.translate_operand(operand),
                )]
            }
            AssertMessage::MisalignedPointerDereference { required, found } => vec![Expr::apps(
                Expr::const_str("RustVIR.aligned"),
                [
                    self.translate_operand(found),
                    self.translate_operand(required),
                ],
            )],
            AssertMessage::Custom(message) => vec![Expr::app(
                Expr::const_str("RustVIR.userAssert"),
                Expr::str_lit(message),
            )],
        }
    }

    fn translate_assert_message(&self, msg: &AssertMessage) -> Expr {
        match msg {
            AssertMessage::BoundsCheck { len, index } => Expr::apps(
                Expr::const_str("RustVIR.boundsCheck"),
                [self.translate_operand(index), self.translate_operand(len)],
            ),
            AssertMessage::Overflow(op, lhs, rhs) => Expr::apps(
                Expr::const_str("RustVIR.overflow"),
                [
                    binop_expr(*op),
                    self.translate_operand(lhs),
                    self.translate_operand(rhs),
                ],
            ),
            AssertMessage::OverflowNeg(operand) => Expr::app(
                Expr::const_str("RustVIR.overflowNeg"),
                self.translate_operand(operand),
            ),
            AssertMessage::DivisionByZero(operand) => Expr::app(
                Expr::const_str("RustVIR.divisionByZero"),
                self.translate_operand(operand),
            ),
            AssertMessage::RemainderByZero(operand) => Expr::app(
                Expr::const_str("RustVIR.remainderByZero"),
                self.translate_operand(operand),
            ),
            AssertMessage::MisalignedPointerDereference { required, found } => Expr::apps(
                Expr::const_str("RustVIR.misalignedDeref"),
                [
                    self.translate_operand(found),
                    self.translate_operand(required),
                ],
            ),
            AssertMessage::Custom(message) => Expr::app(
                Expr::const_str("RustVIR.customAssert"),
                Expr::str_lit(message),
            ),
        }
    }

    fn translate_operand(&self, operand: &Operand) -> Expr {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => translate_place(place),
            Operand::Constant(constant) => translate_constant(constant),
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ObligationBatch {
    pub obligations: Vec<ProofObligation>,
}

impl ObligationBatch {
    #[must_use]
    pub fn from_body(function: &str, body: &Body) -> Self {
        Self {
            obligations: extract_obligations(function, body),
        }
    }

    #[must_use]
    pub fn goals(&self) -> Vec<Expr> {
        self.obligations.iter().map(ProofObligation::goal).collect()
    }

    pub fn submit<T>(&self, mut verifier: impl FnMut(&ProofObligation, Expr) -> T) -> Vec<T> {
        self.obligations
            .iter()
            .map(|obligation| verifier(obligation, obligation.goal()))
            .collect()
    }
}

#[must_use]
pub fn extract_obligations(function: &str, body: &Body) -> Vec<ProofObligation> {
    let translator = VirToLean::new();
    let mut obligations = Vec::new();

    for (block_idx, block) in body.blocks.iter().enumerate() {
        let block_id = block_idx as BasicBlockId;
        for (stmt_idx, stmt) in block.statements.iter().enumerate() {
            if let Some(obligation) =
                extract_statement_obligation(function, block_id, stmt_idx, stmt, &translator)
            {
                obligations.push(obligation);
            }
        }
        if let Some(obligation) =
            extract_terminator_obligation(function, block_id, &block.terminator, &translator)
        {
            obligations.push(obligation);
        }
    }

    obligations
}

fn extract_statement_obligation(
    function: &str,
    block: BasicBlockId,
    stmt_idx: usize,
    stmt: &Stmt,
    translator: &VirToLean,
) -> Option<ProofObligation> {
    let location = format!("{function}:bb{block}:stmt{stmt_idx}");
    match stmt {
        Stmt::Assign {
            rvalue: Rvalue::AddressOf { place, .. },
            ..
        }
        | Stmt::Retag {
            kind: RetagKind::Raw(_),
            place,
        } => Some(ProofObligation {
            function: function.to_string(),
            location,
            source: ObligationSource::UnsafeBlock,
            preconditions: Vec::new(),
            postconditions: vec![translator.translate_unsafe_site(place)],
            invariants: Vec::new(),
        }),
        _ => None,
    }
}

fn extract_terminator_obligation(
    function: &str,
    block: BasicBlockId,
    term: &Term,
    translator: &VirToLean,
) -> Option<ProofObligation> {
    let Term::Assert {
        cond,
        expected,
        msg,
        ..
    } = term
    else {
        return None;
    };

    Some(ProofObligation {
        function: function.to_string(),
        location: format!("{function}:bb{block}:term"),
        source: assert_source(msg),
        preconditions: Vec::new(),
        postconditions: vec![translator.translate_assertion(cond, *expected, msg)],
        invariants: translator.translate_assert_invariants(msg),
    })
}

fn assert_source(msg: &AssertMessage) -> ObligationSource {
    match msg {
        AssertMessage::BoundsCheck { .. }
        | AssertMessage::DivisionByZero(..)
        | AssertMessage::RemainderByZero(..)
        | AssertMessage::MisalignedPointerDereference { .. } => ObligationSource::Precondition,
        AssertMessage::Overflow(..) | AssertMessage::OverflowNeg(..) => ObligationSource::Overflow,
        AssertMessage::Custom(..) => ObligationSource::AssertionCheck,
    }
}

fn translate_constant(constant: &Constant) -> Expr {
    match constant {
        Constant::Scalar(scalar) => translate_scalar(scalar),
        Constant::ZeroSized => Expr::const_str("Unit.unit"),
        Constant::Static(name) | Constant::Str(name) => Expr::str_lit(name),
        Constant::ByteStr(bytes) => Expr::str_lit(String::from_utf8_lossy(bytes)),
        Constant::FnDef { name, .. } => Expr::str_lit(name),
        Constant::Aggregate(aggregate) => translate_aggregate_constant(aggregate),
    }
}

/// Translate a composite constant (tuple/array/struct/enum literal) into a Lean
/// term: the appropriate head applied to the translated element constants. This
/// preserves the full structure so consumers see the materialized value rather
/// than a temporary.
fn translate_aggregate_constant(aggregate: &AggregateConst) -> Expr {
    let elements = aggregate.elements.iter().map(translate_constant);
    let head = match &aggregate.kind {
        ConstAggregateKind::Tuple => Expr::const_str("Tuple"),
        ConstAggregateKind::Array(_) => Expr::const_str("Array"),
        ConstAggregateKind::Struct { name, .. } => Expr::const_str(name),
        ConstAggregateKind::Enum { name, variant, .. } => {
            Expr::const_str(&format!("{name}.{variant}"))
        }
    };
    Expr::apps(head, elements)
}

fn translate_scalar(scalar: &ScalarValue) -> Expr {
    match scalar {
        ScalarValue::Bool(value) => bool_expr(*value),
        ScalarValue::Char(value) => Expr::str_lit(value.to_string()),
        ScalarValue::Int(value) => Expr::str_lit(value.to_string()),
        ScalarValue::Uint(value) => {
            u64::try_from(*value).map_or_else(|_| Expr::str_lit(value.to_string()), Expr::nat_lit)
        }
        ScalarValue::Float32(value) => Expr::str_lit(value.to_string()),
        ScalarValue::Float64(value) => Expr::str_lit(value.to_string()),
    }
}

fn bool_expr(value: bool) -> Expr {
    if value {
        Expr::const_str("Bool.true")
    } else {
        Expr::const_str("Bool.false")
    }
}

fn binop_expr(op: BinOp) -> Expr {
    Expr::str_lit(format!("{op:?}"))
}

fn conjoin(terms: &[Expr]) -> Expr {
    match terms {
        [] => Expr::const_str("True"),
        [term] => term.clone(),
        [first, rest @ ..] => rest.iter().fold(first.clone(), |acc, term| {
            Expr::apps(Expr::const_str("And"), [acc, term.clone()])
        }),
    }
}

#[cfg(test)]
mod tests;
