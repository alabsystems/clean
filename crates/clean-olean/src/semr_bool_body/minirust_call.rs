// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const CALL_ROOTS: &[&str] = &[
    "MiniRustBoolConjunction.SourceCall",
    "MiniRustBoolConjunction.SourceCallBlob",
    "MiniRustBoolConjunction.checked_source_call",
    "MiniRustBoolConjunction.with_checked_root",
    "MR_IntBinOp.BitAnd",
    "MR_IntBinOp.BitOr",
    "MR_IntBinOp.BitXor",
];

/// The four numbers are raw owner-local HIR IDs in declaration and occurrence
/// order. The independently constructed goal retains all four, including swaps.
#[derive(Clone, Copy, Debug)]
pub struct MiniRustCallSubject {
    pub operation: BoolSourceOp,
    pub declarations: [u32; 2],
    pub occurrences: [u32; 2],
}

impl BoolSourceOp {
    pub(super) fn minirust_name(self) -> &'static str {
        match self {
            BoolSourceOp::BitAnd => "MR_IntBinOp.BitAnd",
            BoolSourceOp::BitOr => "MR_IntBinOp.BitOr",
            BoolSourceOp::BitXor => "MR_IntBinOp.BitXor",
        }
    }
}

impl MiniRustCallSubject {
    fn arguments(self) -> [Expr; 5] {
        let op = self.operation.minirust_name();
        let [first, second] = self.declarations.map(|n| Expr::nat_lit(n.into()));
        let [left, right] = self.occurrences.map(|n| Expr::nat_lit(n.into()));
        [c(op), first, second, left, right]
    }
}

impl PreparedBoolMathematicsContext {
    /// Compare the FULL-replayed declarations for the original MiniRust call
    /// and its SemR connection with the accepted original source environment.
    pub fn check_minirust_call_source(
        &self,
        original: &Environment,
    ) -> Result<(), BoolBodyRefusal> {
        self.check_model_source(original)?;
        self.model
            .check_source_roots(original, CALL_ROOTS, &self.call_source_reference)?;
        Ok(())
    }

    fn require_minirust_call_source(&self) -> Result<(), BoolBodyRefusal> {
        if self.call_source_reference.get().is_none() {
            return Err(BoolBodyRefusal::ModelSourceClosure(
                "the original MiniRust call source closure has not been checked".into(),
            ));
        }
        Ok(())
    }

    /// Check the proposed source-only call under the authenticated original
    /// model. No IR subject is created by this operation.
    pub fn check_minirust_call(
        &self,
        source: MiniRustCallSubject,
        source_proof: &Expr,
    ) -> Result<(), BoolBodyRefusal> {
        self.require_minirust_call_source()?;
        let goal = Expr::apps(c("MiniRustBoolConjunction.SourceCall"), source.arguments());
        self.model
            .kernel()
            .check_closed_term(&goal, source_proof)
            .map_err(BoolBodyRefusal::Proof)?;
        Ok(())
    }

    pub(super) fn prepared_root_arguments(
        &self,
        expected: &BoolSubject,
        checked: &CheckedUnboundBoolMathematics,
    ) -> Result<[Expr; 2], BoolBodyRefusal> {
        if checked.origin != CheckedBoolOrigin::PreparedRoot
            || checked.context != self.digest()
            || checked.subject.function != expected.function
            || checked.subject.module.bytes != expected.module.bytes
        {
            return Err(BoolBodyRefusal::SubjectMismatch);
        }
        let quote = self.quote(&expected.module)?;
        let bytes = quote.concrete.clone();
        let fid = Expr::nat_lit(expected.function.into());
        Ok([bytes, fid])
    }

    /// Check a single proposition over the original MiniRust machine and the
    /// concrete, already byte-bound root. Only the retained prepared proof for
    /// this module, function and kernel context may supply the IR equation.
    pub fn check_minirust_call_blob(
        &self,
        expected: &BoolSubject,
        checked: &CheckedUnboundBoolMathematics,
        source: MiniRustCallSubject,
        source_proof: &Expr,
    ) -> Result<(), BoolBodyRefusal> {
        self.require_minirust_call_source()?;
        let [bytes, fid] = self.prepared_root_arguments(expected, checked)?;
        let goal = Expr::apps(
            Expr::apps(
                c("MiniRustBoolConjunction.SourceCallBlob"),
                [bytes.clone(), fid.clone()],
            ),
            source.arguments(),
        );
        let [first, second] = source.declarations.map(|n| Expr::nat_lit(n.into()));
        let proof = Expr::apps(
            c("MiniRustBoolConjunction.with_checked_root"),
            [
                bytes,
                fid,
                first,
                second,
                source_proof.clone(),
                checked.proof.clone(),
            ],
        );
        self.model
            .kernel()
            .check_closed_term(&goal, &proof)
            .map_err(BoolBodyRefusal::Proof)?;
        Ok(())
    }
}
