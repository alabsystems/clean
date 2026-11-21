// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// These original declarations and their dependencies must agree with the separately
/// accepted model source before original-item requests can be checked.
pub const ORIGINAL_BOOL_ITEM_ROOTS: &[&str] = &[
    "MiniRustBoolConjunction.Item.Local",
    "MiniRustBoolConjunction.Item.Local.mk",
    "MiniRustBoolConjunction.Item.read",
    "MiniRustBoolConjunction.Item.quotedRhs",
    "MiniRustBoolConjunction.Item.checkAt",
    "MiniRustBoolConjunction.Item.BoundAt",
    "MiniRustBoolConjunction.Item.BoundBlobAt",
    "MiniRustBoolConjunction.Item.ofCheckAt",
    "MiniRustBoolConjunction.Item.withRoot",
];

/// A compiler owner-local binding or occurrence, with half-open byte offsets within its item.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OriginalBoolItemLocal {
    pub id: u32,
    pub lo: u32,
    pub hi: u32,
}

impl OriginalBoolItemLocal {
    fn term(self) -> Expr {
        Expr::apps(
            c("MiniRustBoolConjunction.Item.Local.mk"),
            [self.id, self.lo, self.hi].map(|n| Expr::nat_lit(n.into())),
        )
    }
}

/// Independently held original file bytes, expected item name and compiler input.
/// Item bounds are file-relative, while every binding and occurrence range is item-relative.
#[derive(Clone, Copy, Debug)]
pub struct OriginalBoolItemSubject<'a> {
    pub file: &'a [u8],
    pub item_start: u32,
    pub item_end: u32,
    pub symbol: &'a [u8],
    pub operation: BoolSourceOp,
    pub declarations: [OriginalBoolItemLocal; 2],
    pub occurrences: [OriginalBoolItemLocal; 2],
}

/// Keep the term depth bounded even when the selected item is in a large source file.
/// The original Lean checker receives every byte and performs the selection itself.
fn source_bytes(bytes: &[u8]) -> Expr {
    if bytes.len() <= 128 {
        return crate::semr_model::bytes(bytes);
    }
    let (left, right) = bytes.split_at(bytes.len() / 2);
    byte_quote::append(source_bytes(left), source_bytes(right))
}

impl OriginalBoolItemSubject<'_> {
    fn arguments(&self) -> [Expr; 9] {
        let [a, b] = self.declarations.map(OriginalBoolItemLocal::term);
        let [l, r] = self.occurrences.map(OriginalBoolItemLocal::term);
        [
            source_bytes(self.file),
            Expr::nat_lit(self.item_start.into()),
            Expr::nat_lit(self.item_end.into()),
            source_bytes(self.symbol),
            c(self.operation.minirust_name()),
            a,
            b,
            l,
            r,
        ]
    }
}

fn true_refl() -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [c("Bool"), c("Bool.true")],
    )
}

impl PreparedBoolMathematicsContext {
    pub fn check_original_bool_item_source(
        &self,
        original: &Environment,
    ) -> Result<(), BoolBodyRefusal> {
        self.check_minirust_call_source(original)?;
        self.model.check_source_roots(
            original,
            ORIGINAL_BOOL_ITEM_ROOTS,
            &self.item_source_reference,
        )?;
        Ok(())
    }

    fn require_original_bool_item_source(&self) -> Result<(), BoolBodyRefusal> {
        if self.item_source_reference.get().is_none() {
            return Err(BoolBodyRefusal::ModelSourceClosure(
                "the original Rust item model source closure has not been checked".into(),
            ));
        }
        Ok(())
    }

    /// The complete expected proposition contains the source file, item span, owner name,
    /// operation, and all four binding records. Success requires the source decision's proof
    /// to type-check in the original model and the original MiniRust call to follow.
    pub fn check_original_bool_item(
        &self,
        source: &OriginalBoolItemSubject<'_>,
    ) -> Result<(), BoolBodyRefusal> {
        self.require_original_bool_item_source()?;
        let args = source.arguments();
        let goal = Expr::apps(c("MiniRustBoolConjunction.Item.BoundAt"), args.clone());
        let proof = Expr::app(
            Expr::apps(c("MiniRustBoolConjunction.Item.ofCheckAt"), args),
            true_refl(),
        );
        self.model
            .kernel()
            .check_closed_term(&goal, &proof)
            .map_err(BoolBodyRefusal::Proof)?;
        Ok(())
    }

    /// Combine the original source decision with the already checked canonical module and
    /// function's universal equation. A source-only or different physical root cannot supply it.
    pub fn check_original_bool_item_blob(
        &self,
        expected: &BoolSubject,
        checked: &CheckedUnboundBoolMathematics,
        source: &OriginalBoolItemSubject<'_>,
    ) -> Result<(), BoolBodyRefusal> {
        self.require_original_bool_item_source()?;
        let root = self.prepared_root_arguments(expected, checked)?;
        let args = source.arguments();
        let goal = Expr::apps(
            Expr::apps(c("MiniRustBoolConjunction.Item.BoundBlobAt"), args.clone()),
            root.clone(),
        );
        let proof = Expr::apps(
            Expr::apps(
                Expr::apps(c("MiniRustBoolConjunction.Item.withRoot"), args),
                root,
            ),
            [true_refl(), checked.proof.clone()],
        );
        self.model
            .kernel()
            .check_closed_term(&goal, &proof)
            .map_err(BoolBodyRefusal::Proof)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ClosedRecheckOptions, load_modules_with_deps, reference_base_closed};
    use clean_kernel::{KernelEnvError, KernelTypeError};

    #[test]
    fn original_file_quotation_preserves_bytes_on_both_sides_of_a_chunk_boundary() {
        let lib = crate::installed_lean_lib_path("leanprover/lean4:v4.30.0-rc2")
            .expect("the Boolean model's pinned Lean library is required");
        let mut env = Environment::for_lean_replay();
        load_modules_with_deps(&mut env, &["Init.Data.List.Basic".into()], &[lib]).unwrap();
        let names = [
            "List.append",
            "List.cons",
            "List.nil",
            "Nat",
            "Eq",
            "Eq.refl",
        ]
        .map(Name::from_string)
        .into_iter()
        .collect();
        let base = reference_base_closed(&env, &names, &ClosedRecheckOptions::default()).unwrap();
        assert!(base.report.passed() && base.entry_refusals.is_empty());
        let kernel = base.into_kernel().unwrap();
        let source: Vec<u8> = (0..=255).chain([13, 10]).collect();
        let flat = crate::semr_model::bytes(&source);
        let ty = Expr::app(
            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            c("Nat"),
        );
        let level = Level::succ(Level::zero());
        let proposition = |raw: &[u8]| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![level.clone()]),
                [ty.clone(), source_bytes(raw), flat.clone()],
            )
        };
        let proof = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![level.clone()]),
            [ty.clone(), flat.clone()],
        );
        kernel
            .check_closed_term(&proposition(&source), &proof)
            .unwrap();
        for offset in [0, 128, 129, 257] {
            let mut altered = source.clone();
            altered[offset] ^= 1;
            assert!(matches!(
                kernel.check_closed_term(&proposition(&altered), &proof),
                Err(ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
                    source: KernelTypeError::TypeMismatch { .. },
                    ..
                }))
            ));
        }
    }
}
