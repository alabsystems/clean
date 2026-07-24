// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! VIR-to-Lean proof-obligation scaffolding.
//!
//! This module walks lowered VIR and extracts verification obligations at
//! explicit ownership, lifetime, panic, and invariant boundaries. Each
//! obligation keeps enough VIR context to let downstream verification layers
//! relate the generated Lean expression back to the originating Rust program.

use crate::ownership::Place;
use crate::translate::{translate_place, translate_type, TranslationContext};
use crate::types::{Lifetime, RustType};
use crate::vir::{
    AggregateConst, AggregateKind, AssertMessage, BasicBlockId, Body, BorrowKind,
    ConstAggregateKind, Constant, LocalId, Operand, Rvalue, ScalarValue, Stmt, Term,
};
use crate::vir_lowering::LoweredProgram;
use clean_kernel::Expr as LeanExpr;

/// High-level proof-obligation categories emitted from VIR.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ObligationKind {
    OwnershipTransfer,
    BorrowValid,
    LifetimeOutlives,
    PanicFreedom,
    MemorySafety,
    TypeInvariant,
}

/// Precise VIR site for an obligation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VirSite {
    Statement(usize),
    Terminator,
}

/// Snapshot of a local visible at an obligation site.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VirLocalContext {
    pub local: LocalId,
    pub name: Option<String>,
    pub ty: RustType,
}

/// Surrounding VIR context for an emitted obligation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VirContext {
    pub function: String,
    pub block: BasicBlockId,
    pub site: VirSite,
    pub locals: Vec<VirLocalContext>,
    pub related_places: Vec<Place>,
}

/// A proof obligation extracted from lowered VIR.
#[derive(Debug, Clone, PartialEq)]
pub struct ProofObligation {
    pub source_location: Option<String>,
    pub kind: ObligationKind,
    pub preconditions: Vec<LeanExpr>,
    pub postcondition: LeanExpr,
    pub vir_context: VirContext,
}

impl ProofObligation {
    #[must_use]
    pub fn new(
        source_location: Option<String>,
        kind: ObligationKind,
        preconditions: Vec<LeanExpr>,
        postcondition: LeanExpr,
        vir_context: VirContext,
    ) -> Self {
        Self {
            source_location,
            kind,
            preconditions,
            postcondition,
            vir_context,
        }
    }

    /// Translate this obligation into a Lean verification goal.
    ///
    /// Preconditions are folded into a right-associated implication chain:
    /// `p1 -> p2 -> ... -> postcondition`.
    pub fn to_lean_expr(&self) -> LeanExpr {
        self.preconditions
            .iter()
            .rev()
            .fold(self.postcondition.clone(), |goal, precondition| {
                LeanExpr::arrow(precondition.clone(), goal)
            })
    }
}

/// Collect proof obligations by walking VIR bodies.
#[derive(Debug, Default)]
pub struct ObligationCollector {
    obligations: Vec<ProofObligation>,
}

impl ObligationCollector {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub fn collect_program(lowered: &LoweredProgram) -> Vec<ProofObligation> {
        let mut collector = Self::new();
        for (function, body) in &lowered.functions {
            collector.collect_body(function, body);
        }
        collector.obligations
    }

    pub fn collect_body(&mut self, function: &str, body: &Body) {
        for (block_idx, block) in body.blocks.iter().enumerate() {
            let block_id = block_idx as BasicBlockId;
            for (stmt_idx, stmt) in block.statements.iter().enumerate() {
                self.scan_stmt(function, body, block_id, stmt_idx, stmt);
            }
            self.scan_term(function, body, block_id, &block.terminator);
        }
    }

    #[must_use]
    pub fn obligations(&self) -> &[ProofObligation] {
        &self.obligations
    }

    fn scan_stmt(
        &mut self,
        function: &str,
        body: &Body,
        block: BasicBlockId,
        stmt_idx: usize,
        stmt: &Stmt,
    ) {
        let site = VirSite::Statement(stmt_idx);
        match stmt {
            Stmt::Assign { place, rvalue } => {
                self.scan_assign(function, body, block, &site, place, rvalue);
            }
            Stmt::SetDiscriminant {
                place,
                variant_index,
            } => {
                self.emit(
                    function,
                    body,
                    block,
                    site,
                    vec![place.clone()],
                    ObligationKind::TypeInvariant,
                    vec![place_predicate("RustOwnership.placeInitialized", place)],
                    LeanExpr::apps(
                        const_expr("RustTypeInvariant.discriminantSet"),
                        [
                            translate_place(place),
                            LeanExpr::nat_lit(u64::from(*variant_index)),
                        ],
                    ),
                );
            }
            Stmt::Retag { place, .. } => {
                self.emit(
                    function,
                    body,
                    block,
                    site,
                    vec![place.clone()],
                    ObligationKind::MemorySafety,
                    vec![place_predicate("RustOwnership.borrowValid", place)],
                    place_predicate("RustMemory.retagSafe", place),
                );
            }
            Stmt::StorageLive(..) | Stmt::StorageDead(..) | Stmt::Nop => {}
        }
    }

    fn scan_assign(
        &mut self,
        function: &str,
        body: &Body,
        block: BasicBlockId,
        site: &VirSite,
        destination: &Place,
        rvalue: &Rvalue,
    ) {
        match rvalue {
            Rvalue::Ref { borrow_kind, place } => {
                let mut preconditions =
                    vec![place_predicate("RustOwnership.placeInitialized", place)];
                if matches!(borrow_kind, BorrowKind::Mut { .. }) {
                    preconditions.push(place_predicate("RustOwnership.exclusiveAccess", place));
                }
                self.emit(
                    function,
                    body,
                    block,
                    site.clone(),
                    vec![destination.clone(), place.clone()],
                    ObligationKind::BorrowValid,
                    preconditions,
                    place_predicate("RustOwnership.borrowValid", place),
                );

                if let Some(lifetime) = reference_lifetime_for_place(body, destination) {
                    self.emit(
                        function,
                        body,
                        block,
                        site.clone(),
                        vec![destination.clone(), place.clone()],
                        ObligationKind::LifetimeOutlives,
                        vec![place_predicate("RustOwnership.borrowValid", place)],
                        LeanExpr::apps(
                            const_expr("RustLifetime.outlives"),
                            [translate_lifetime(lifetime), translate_place(place)],
                        ),
                    );
                }
            }
            Rvalue::AddressOf { place, .. } => {
                self.emit(
                    function,
                    body,
                    block,
                    site.clone(),
                    vec![destination.clone(), place.clone()],
                    ObligationKind::MemorySafety,
                    vec![
                        place_predicate("RustMemory.allocated", place),
                        place_predicate("RustMemory.aligned", place),
                    ],
                    place_predicate("RustMemory.addressOfSafe", place),
                );
            }
            Rvalue::CopyForDeref(place) => {
                self.emit(
                    function,
                    body,
                    block,
                    site.clone(),
                    vec![destination.clone(), place.clone()],
                    ObligationKind::MemorySafety,
                    vec![place_predicate("RustMemory.derefable", place)],
                    place_predicate("RustMemory.copyForDerefSafe", place),
                );
            }
            Rvalue::Aggregate { kind, .. } => {
                self.emit(
                    function,
                    body,
                    block,
                    site.clone(),
                    vec![destination.clone()],
                    ObligationKind::TypeInvariant,
                    place_type(body, destination)
                        .map(|ty| vec![type_predicate("RustTypeInvariant.wellFormed", ty)])
                        .unwrap_or_default(),
                    LeanExpr::apps(
                        const_expr("RustTypeInvariant.assignmentPreserves"),
                        [
                            translate_place(destination),
                            aggregate_kind_expr(kind),
                            place_type_expr(body, destination),
                        ],
                    ),
                );
            }
            _ => {}
        }

        self.scan_rvalue(function, body, block, site, rvalue);
    }

    fn scan_term(&mut self, function: &str, body: &Body, block: BasicBlockId, term: &Term) {
        let site = VirSite::Terminator;
        match term {
            Term::Return | Term::Unreachable | Term::UnwindResume | Term::UnwindTerminate => {}
            Term::Goto { args, .. } => {
                for operand in args {
                    self.scan_operand(function, body, block, &site, operand);
                }
            }
            Term::SwitchInt {
                discriminant,
                targets,
            } => {
                self.scan_operand(function, body, block, &site, discriminant);
                for (_, target) in targets.iter_targets() {
                    for operand in &target.args {
                        self.scan_operand(function, body, block, &site, operand);
                    }
                }
            }
            Term::Call {
                func,
                args,
                target_args,
                ..
            } => {
                self.scan_operand(function, body, block, &site, func);
                for operand in args {
                    self.scan_operand(function, body, block, &site, operand);
                }
                for operand in target_args {
                    self.scan_operand(function, body, block, &site, operand);
                }
            }
            Term::Assert {
                cond,
                expected,
                msg,
                target_args,
                ..
            } => {
                self.emit(
                    function,
                    body,
                    block,
                    site.clone(),
                    Vec::new(),
                    ObligationKind::PanicFreedom,
                    vec![LeanExpr::apps(
                        const_expr("RustSem.conditionMatchesExpectation"),
                        [operand_expr(cond), bool_expr(*expected)],
                    )],
                    LeanExpr::apps(
                        const_expr("RustSem.panicFree"),
                        [assert_message_expr(msg), operand_expr(cond)],
                    ),
                );
                self.scan_operand(function, body, block, &site, cond);
                for operand in target_args {
                    self.scan_operand(function, body, block, &site, operand);
                }
            }
            Term::Drop {
                place, target_args, ..
            } => {
                self.emit(
                    function,
                    body,
                    block,
                    site.clone(),
                    vec![place.clone()],
                    ObligationKind::MemorySafety,
                    vec![place_predicate("RustOwnership.placeInitialized", place)],
                    LeanExpr::apps(
                        const_expr("RustMemory.dropSafe"),
                        [translate_place(place), place_type_expr(body, place)],
                    ),
                );
                for operand in target_args {
                    self.scan_operand(function, body, block, &site, operand);
                }
            }
            Term::Yield {
                value, resume_args, ..
            } => {
                self.scan_operand(function, body, block, &site, value);
                for operand in resume_args {
                    self.scan_operand(function, body, block, &site, operand);
                }
            }
        }
    }

    fn scan_rvalue(
        &mut self,
        function: &str,
        body: &Body,
        block: BasicBlockId,
        site: &VirSite,
        rvalue: &Rvalue,
    ) {
        match rvalue {
            Rvalue::Use(operand)
            | Rvalue::ShallowInitBox { operand, .. }
            | Rvalue::UnaryOp { operand, .. } => {
                self.scan_operand(function, body, block, site, operand)
            }
            Rvalue::Repeat { operand, .. } => {
                self.scan_operand(function, body, block, site, operand)
            }
            Rvalue::Cast { operand, .. } => self.scan_operand(function, body, block, site, operand),
            Rvalue::BinaryOp { lhs, rhs, .. } | Rvalue::CheckedBinaryOp { lhs, rhs, .. } => {
                self.scan_operand(function, body, block, site, lhs);
                self.scan_operand(function, body, block, site, rhs);
            }
            Rvalue::Aggregate { operands, .. } => {
                for operand in operands {
                    self.scan_operand(function, body, block, site, operand);
                }
            }
            Rvalue::Ref { .. }
            | Rvalue::ThreadLocalRef(_)
            | Rvalue::AddressOf { .. }
            | Rvalue::Len(_)
            | Rvalue::NullaryOp { .. }
            | Rvalue::Discriminant(_)
            | Rvalue::Opaque { .. }
            | Rvalue::CopyForDeref(_) => {}
        }
    }

    fn scan_operand(
        &mut self,
        function: &str,
        body: &Body,
        block: BasicBlockId,
        site: &VirSite,
        operand: &Operand,
    ) {
        if let Operand::Move(place) = operand {
            self.emit(
                function,
                body,
                block,
                site.clone(),
                vec![place.clone()],
                ObligationKind::OwnershipTransfer,
                vec![
                    place_predicate("RustOwnership.noActiveBorrows", place),
                    place_predicate("RustOwnership.placeInitialized", place),
                ],
                place_predicate("RustOwnership.transferAllowed", place),
            );
        }
    }

    fn emit(
        &mut self,
        function: &str,
        body: &Body,
        block: BasicBlockId,
        site: VirSite,
        related_places: Vec<Place>,
        kind: ObligationKind,
        preconditions: Vec<LeanExpr>,
        postcondition: LeanExpr,
    ) {
        let context = make_context(function, body, block, site, related_places);
        let source_location = Some(location_string(function, context.block, &context.site));
        self.obligations.push(ProofObligation::new(
            source_location,
            kind,
            preconditions,
            postcondition,
            context,
        ));
    }
}

fn make_context(
    function: &str,
    body: &Body,
    block: BasicBlockId,
    site: VirSite,
    related_places: Vec<Place>,
) -> VirContext {
    let locals = body
        .locals
        .iter()
        .enumerate()
        .map(|(idx, decl)| VirLocalContext {
            local: idx as LocalId,
            name: decl.name.clone(),
            ty: decl.ty.clone(),
        })
        .collect();

    VirContext {
        function: function.to_string(),
        block,
        site,
        locals,
        related_places,
    }
}

fn location_string(function: &str, block: BasicBlockId, site: &VirSite) -> String {
    match site {
        VirSite::Statement(stmt_idx) => format!("{function}:bb{block}:stmt{stmt_idx}"),
        VirSite::Terminator => format!("{function}:bb{block}:term"),
    }
}

fn place_type<'a>(body: &'a Body, place: &Place) -> Option<&'a RustType> {
    match place.base() {
        Place::Local(local) => body.local(*local).map(|decl| &decl.ty),
        Place::Static(_) => None,
        Place::Field { .. } | Place::Index { .. } | Place::Deref(_) | Place::Downcast { .. } => {
            None
        }
    }
}

fn reference_lifetime_for_place<'a>(body: &'a Body, place: &Place) -> Option<&'a Lifetime> {
    match place_type(body, place) {
        Some(RustType::Reference { lifetime, .. }) => Some(lifetime),
        _ => None,
    }
}

fn place_type_expr(body: &Body, place: &Place) -> LeanExpr {
    place_type(body, place)
        .map(translate_rust_type)
        .unwrap_or_else(|| LeanExpr::const_str("Unit"))
}

fn translate_rust_type(ty: &RustType) -> LeanExpr {
    let ctx = TranslationContext::new();
    translate_type(ty, &ctx)
}

fn type_predicate(predicate: &str, ty: &RustType) -> LeanExpr {
    LeanExpr::app(const_expr(predicate), translate_rust_type(ty))
}

fn place_predicate(predicate: &str, place: &Place) -> LeanExpr {
    LeanExpr::app(const_expr(predicate), translate_place(place))
}

fn aggregate_kind_expr(kind: &AggregateKind) -> LeanExpr {
    match kind {
        AggregateKind::Array(ty) => LeanExpr::apps(
            const_expr("RustAggregateKind.array"),
            [translate_rust_type(ty)],
        ),
        AggregateKind::Tuple => const_expr("RustAggregateKind.tuple"),
        AggregateKind::Adt {
            name,
            variant_index,
        } => LeanExpr::apps(
            const_expr("RustAggregateKind.adt"),
            [
                LeanExpr::str_lit(name),
                LeanExpr::nat_lit(u64::from(*variant_index)),
            ],
        ),
        AggregateKind::Closure { def_id } => LeanExpr::app(
            const_expr("RustAggregateKind.closure"),
            LeanExpr::str_lit(def_id),
        ),
        AggregateKind::Generator { def_id } => LeanExpr::app(
            const_expr("RustAggregateKind.generator"),
            LeanExpr::str_lit(def_id),
        ),
    }
}

fn assert_message_expr(message: &AssertMessage) -> LeanExpr {
    match message {
        AssertMessage::BoundsCheck { .. } => LeanExpr::str_lit("bounds_check"),
        AssertMessage::Overflow(..) => LeanExpr::str_lit("overflow"),
        AssertMessage::OverflowNeg(..) => LeanExpr::str_lit("overflow_neg"),
        AssertMessage::DivisionByZero(..) => LeanExpr::str_lit("division_by_zero"),
        AssertMessage::RemainderByZero(..) => LeanExpr::str_lit("remainder_by_zero"),
        AssertMessage::MisalignedPointerDereference { .. } => {
            LeanExpr::str_lit("misaligned_pointer_dereference")
        }
        AssertMessage::Custom(message) => LeanExpr::str_lit(message),
    }
}

fn operand_expr(operand: &Operand) -> LeanExpr {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => translate_place(place),
        Operand::Constant(constant) => constant_expr(constant),
    }
}

fn constant_expr(constant: &Constant) -> LeanExpr {
    match constant {
        Constant::Scalar(scalar) => scalar_expr(scalar),
        Constant::ZeroSized => LeanExpr::const_str("Unit.unit"),
        Constant::Static(name) | Constant::Str(name) => LeanExpr::str_lit(name),
        Constant::ByteStr(bytes) => LeanExpr::str_lit(String::from_utf8_lossy(bytes)),
        Constant::FnDef { name, .. } => LeanExpr::str_lit(name),
        Constant::Aggregate(aggregate) => aggregate_constant_expr(aggregate),
    }
}

/// Translate a composite constant (tuple/array/struct/enum literal) into a Lean
/// term: the appropriate head applied to the translated element constants,
/// preserving the materialized structure.
fn aggregate_constant_expr(aggregate: &AggregateConst) -> LeanExpr {
    let elements = aggregate.elements.iter().map(constant_expr);
    let head = match &aggregate.kind {
        ConstAggregateKind::Tuple => LeanExpr::const_str("Tuple"),
        ConstAggregateKind::Array(_) => LeanExpr::const_str("Array"),
        ConstAggregateKind::Struct { name, .. } => LeanExpr::const_str(name),
        ConstAggregateKind::Enum { name, variant, .. } => {
            LeanExpr::const_str(&format!("{name}.{variant}"))
        }
    };
    LeanExpr::apps(head, elements)
}

fn scalar_expr(scalar: &ScalarValue) -> LeanExpr {
    match scalar {
        ScalarValue::Bool(value) => bool_expr(*value),
        ScalarValue::Char(value) => LeanExpr::str_lit(value.to_string()),
        ScalarValue::Int(value) => LeanExpr::str_lit(value.to_string()),
        ScalarValue::Uint(value) => match u64::try_from(*value) {
            Ok(value) => LeanExpr::nat_lit(value),
            Err(_) => LeanExpr::str_lit(value.to_string()),
        },
        ScalarValue::Float32(value) => LeanExpr::str_lit(value.to_string()),
        ScalarValue::Float64(value) => LeanExpr::str_lit(value.to_string()),
    }
}

fn bool_expr(value: bool) -> LeanExpr {
    if value {
        LeanExpr::const_str("Bool.true")
    } else {
        LeanExpr::const_str("Bool.false")
    }
}

fn translate_lifetime(lifetime: &Lifetime) -> LeanExpr {
    match lifetime {
        Lifetime::Static => const_expr("RustLifetime.static"),
        Lifetime::Named(name) => {
            LeanExpr::app(const_expr("RustLifetime.named"), LeanExpr::str_lit(name))
        }
        Lifetime::Anonymous(id) => LeanExpr::app(
            const_expr("RustLifetime.anonymous"),
            LeanExpr::nat_lit(u64::from(*id)),
        ),
        Lifetime::Existential(id) => LeanExpr::app(
            const_expr("RustLifetime.existential"),
            LeanExpr::nat_lit(u64::from(*id)),
        ),
    }
}

fn const_expr(name: &str) -> LeanExpr {
    LeanExpr::const_str(name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{Mutability, UintType};
    use crate::vir::{BasicBlock, BorrowKind, LocalDecl, MutBorrowKind};

    #[test]
    fn test_proof_obligation_to_lean_expr_builds_implication_chain() {
        let obligation = ProofObligation::new(
            Some("main:bb0:stmt0".to_string()),
            ObligationKind::BorrowValid,
            vec![
                LeanExpr::const_str("RustHyp.p"),
                LeanExpr::const_str("RustHyp.q"),
            ],
            LeanExpr::const_str("RustGoal.r"),
            VirContext {
                function: "main".to_string(),
                block: 0,
                site: VirSite::Statement(0),
                locals: Vec::new(),
                related_places: vec![Place::Local(1)],
            },
        );

        let expected = LeanExpr::arrow(
            LeanExpr::const_str("RustHyp.p"),
            LeanExpr::arrow(
                LeanExpr::const_str("RustHyp.q"),
                LeanExpr::const_str("RustGoal.r"),
            ),
        );

        assert_eq!(obligation.to_lean_expr(), expected);
    }

    #[test]
    fn test_obligation_collector_emits_borrow_lifetime_and_transfer_scaffolding() {
        let mut body = Body::new();
        body.add_local(LocalDecl::new(RustType::Unit, Mutability::Mutable).with_name("_0"));
        let value_local = body.add_local(
            LocalDecl::new(RustType::Uint(UintType::U32), Mutability::Mutable).with_name("value"),
        );
        let slot_local = body.add_local(
            LocalDecl::new(
                RustType::Reference {
                    lifetime: Lifetime::Named("a".to_string()),
                    mutability: Mutability::Mutable,
                    inner: Box::new(RustType::Uint(UintType::U32)),
                },
                Mutability::Mutable,
            )
            .with_name("slot"),
        );

        let mut block = BasicBlock::new(Term::Return);
        block.add_statement(Stmt::Assign {
            place: Place::Local(slot_local),
            rvalue: Rvalue::Ref {
                borrow_kind: BorrowKind::Mut {
                    kind: MutBorrowKind::Default,
                },
                place: Place::Local(value_local),
            },
        });
        block.add_statement(Stmt::Assign {
            place: Place::Local(0),
            rvalue: Rvalue::Use(Operand::Move(Place::Local(value_local))),
        });
        body.add_block(block);

        let mut lowered = LoweredProgram::default();
        lowered.functions.insert("main".to_string(), body);

        let obligations = ObligationCollector::collect_program(&lowered);
        let kinds = obligations
            .iter()
            .map(|obligation| obligation.kind)
            .collect::<Vec<_>>();

        assert!(
            kinds.contains(&ObligationKind::BorrowValid),
            "collector should emit borrow-valid obligations: {kinds:?}"
        );
        assert!(
            kinds.contains(&ObligationKind::LifetimeOutlives),
            "collector should emit lifetime-outlives obligations: {kinds:?}"
        );
        assert!(
            kinds.contains(&ObligationKind::OwnershipTransfer),
            "collector should emit ownership-transfer obligations: {kinds:?}"
        );
        assert_eq!(
            obligations[0].source_location.as_deref(),
            Some("main:bb0:stmt0")
        );
        assert_eq!(obligations[0].vir_context.function, "main");
        assert_eq!(obligations[0].vir_context.related_places.len(), 2);
    }
}
