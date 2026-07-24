// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # clean Rust Semantics (clean-rust-sem)
//!
//! This crate provides a formal model of Rust semantics that can be used
//! to verify Rust programs in clean. The ultimate goal is self-verification:
//! clean verifying its own Rust implementation.
//!
//! ## Architecture
//!
//! The formalization follows the Rust memory model and type system:
//!
//! 1. **Types** (`types.rs`): Rust type system including ownership types
//! 2. **Memory** (`memory/`): Memory model with regions and lifetimes
//! 3. **Ownership** (`ownership.rs`): Ownership and borrowing model
//! 4. **Values** (`values.rs`): Value representation and operations
//! 5. **Expressions** (`expr.rs`): Rust expression semantics
//! 6. **Statements** (`stmt.rs`): Statement semantics and control flow
//! 7. **Translation** (`translate.rs`): Rust → clean kernel translation
//! 8. **Eval** (`eval/`): Operational semantics interpreter
//! 9. **VIR** (`vir.rs`): MIR-derived CFG intermediate representation
//! 10. **Examples** (`examples.rs`): Worked ownership verification programs
//!
//! ## Verification Approach
//!
//! We formalize Rust semantics using clean's kernel terms:
//!
//! - Rust types map to clean types with ownership predicates
//! - Memory operations map to state-passing functions
//! - Ownership rules emit Lean-facing proof obligations via `proof_bundle.rs`
//!
//! This allows clean to verify properties of Rust programs,
//! including the clean kernel itself.

#[cfg(feature = "cli")]
pub mod cli;
pub mod coercion;
pub mod concrete_liveness;
pub mod error;
pub mod eval;
pub mod examples;
pub mod expr;
mod format_intrinsics;
pub mod if_let_chain;
pub mod item;
pub mod iterator;
pub mod memory;
pub mod nll;
pub mod ownership;
pub mod pattern_match;
pub mod proof_bundle;
pub mod proof_bundle_builder;
pub mod proof_obligation;
pub mod proof_obligations;
pub mod shared_memory_model;
pub mod source;
pub mod stack;
pub mod stacked_borrows;
pub mod stmt;
pub mod trait_defaults;
pub mod translate;
pub mod tree_borrows;
pub mod try_block;
pub mod types;
pub mod value_at_address;
pub mod value_at_address_kernel;
pub mod value_view;
pub mod values;
pub mod vir;
pub mod vir_lowering;
pub mod while_let;

// Explicit re-exports (avoid glob exports for semver safety)
pub use coercion::{coerce_value, is_coercible, try_coerce, CoercionKind};
pub use error::RustSemError;
pub use memory::{Address, AllocId, Allocation, Memory, MemoryError};
pub use nll::{
    check_body as nll_check_body, LivenessResult, NllBorrow, NllError, NllResult, ProgramPoint,
    Region,
};
pub use ownership::{
    Borrow, BorrowChecker, BorrowError, DropElaborator, MoveAnalysis, OwnershipState, Place,
    PlaceState,
};
pub use proof_bundle::{AliasingObservation, RustProofBundle, TranslatedFunctionTypes};
pub use proof_bundle_builder::{
    give_back_refinement_obligation, BundleStats, OwnershipObligation, OwnershipObligationKind,
    ProofBundleBuilder,
};
pub use proof_obligation::{
    extract_obligations, ObligationBatch, ObligationSource,
    ProofObligation as VirAssertionObligation, VirToLean,
};
pub use proof_obligations::{
    ObligationCollector, ObligationKind, ProofObligation, VirContext, VirLocalContext, VirSite,
};
pub use shared_memory_model::{RustMemoryModel, RustMemoryModelError};
pub use source::{SourceError, SourceProgram};
pub use stack::{Stack, StackFrame};
pub use stacked_borrows::{
    AccessKind, AliasingDiscipline, BorrowPermission, BorrowStackEntry, BorrowTag, ProtectorId,
    StackedBorrows, StackedBorrowsError,
};
pub use stmt::{AssociatedTypeDef, TraitDef, TraitImplInfo};
pub use tree_borrows::{
    Permission, TreeBorrowNode, TreeBorrowState, TreeBorrows, TreeBorrowsError, TreeBorrowsState,
};
pub use types::{
    dependent_const_eval, resolve_gat, validate_const_generic_bounds, validate_gat_bounds,
    ConstGenericArg, ConstGenericBound, ConstGenericEval, ConstGenericUnifier, ConstGenericValue,
    ConstParamDef, EnumDef, EnumVariant, FloatType, GatDef, GatProjection, GatSubstitution,
    IntType, Lifetime, Mutability, RustType, StructDef, StructField, TypeContext, TypeParamDef,
    TypeVar, UintType, Visibility,
};
pub use value_at_address::{
    step as value_at_address_step, Config, MemOp, Observation, StepOutcome, StuckReason,
};
pub use values::{
    cast_value, eval_binop, eval_unop, BinOp, EnumPayload, FatPointer, FatPtrMetadata, UnOp, Value,
    ValueView, VtablePtr,
};
pub use vir::{
    BasicBlock, BasicBlockId, BlockParam, BlockParamIdx, Body, LocalDecl, LocalId, Operand,
    RetagKind, Rvalue, Stmt, SwitchTarget, SwitchTargets, Term,
};
pub use vir_lowering::{LoweredProgram, VirLoweringError};

/// Domain-prefixed alias for collision-free imports.
///
/// Use `RustSemMemory` when importing from multiple crates with `Memory` types.
pub use memory::Memory as RustSemMemory;

/// Domain-prefixed alias for collision-free imports.
///
/// Use `RustSemStructField` when importing from multiple crates with `StructField` types.
pub use types::StructField as RustSemStructField;

/// Domain-prefixed alias for collision-free imports.
///
/// Use `RustSemStackFrame` when importing from multiple crates with `StackFrame` types.
pub use stack::StackFrame as RustSemStackFrame;

/// Domain-prefixed alias for collision-free imports.
///
/// Use `RustSemLocalDecl` when importing from multiple crates with `LocalDecl` types.
pub use vir::LocalDecl as RustSemLocalDecl;

#[cfg(test)]
mod proof_bundle_tests;

#[cfg(test)]
mod falsification_tests;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_type_construction() {
        let unit_ty = RustType::Unit;
        let bool_ty = RustType::Bool;
        let u32_ty = RustType::Uint(UintType::U32);
        let i64_ty = RustType::Int(IntType::I64);

        assert_eq!(unit_ty.size(), Some(0));
        assert_eq!(bool_ty.size(), Some(1));
        assert_eq!(u32_ty.size(), Some(4));
        assert_eq!(i64_ty.size(), Some(8));
    }

    #[test]
    fn test_reference_types() {
        let lifetime = Lifetime::Named("a".to_string());
        let inner = RustType::Bool;

        let shared_ref = RustType::Reference {
            lifetime: lifetime.clone(),
            mutability: Mutability::Shared,
            inner: Box::new(inner.clone()),
        };

        let mutable_ref = RustType::Reference {
            lifetime,
            mutability: Mutability::Mutable,
            inner: Box::new(inner),
        };

        // References have pointer size (8 bytes on 64-bit)
        assert_eq!(shared_ref.size(), Some(8));
        assert_eq!(mutable_ref.size(), Some(8));
    }

    #[test]
    fn test_ownership_state() {
        let place = Place::local(0);

        let mut state = OwnershipState::new();
        state.mark_owned(place.clone());

        assert!(state.is_owned(&place));
        assert!(!state.is_borrowed(&place));
        assert!(!state.is_moved(&place));

        state.mark_moved(place.clone());
        assert!(!state.is_owned(&place));
        assert!(state.is_moved(&place));
    }

    #[test]
    fn test_memory_model() {
        let mut mem = Memory::new();

        // Allocate a value
        let ptr = mem.allocate_aligned(4, 4).expect("allocation failed");
        assert!(mem.is_valid(ptr));

        // Write and read
        mem.write_u32(ptr, 42).expect("write failed");
        let val = mem.read_u32(ptr).expect("read failed");
        assert_eq!(val, 42);

        // Deallocate
        mem.deallocate(ptr).expect("deallocation failed");
        assert!(!mem.is_valid(ptr));
    }

    #[test]
    fn test_borrow_checker_rules() {
        let checker = BorrowChecker::new();
        let place = Place::local(0);
        let lifetime = Lifetime::Named("a".to_string());

        // Start with owned value
        let mut state = OwnershipState::new();
        state.mark_owned(place.clone());

        // Can create shared borrow
        checker
            .check_borrow(&state, &place, Mutability::Shared, &lifetime)
            .expect("shared borrow of owned place should succeed");

        // Can create multiple shared borrows (would be checked in full impl)
    }

    #[test]
    fn test_worked_examples_module_is_registered() {
        let examples = examples::all_examples();
        assert_eq!(examples.len(), 7);
        assert_eq!(examples[0].name, "inventory_restock");
        assert_eq!(examples[6].name, "raw_write_invalidates_reader");
    }

    #[test]
    fn test_type_compatibility() {
        let u32_ty = RustType::Uint(UintType::U32);
        let i32_ty = RustType::Int(IntType::I32);
        let bool_ty = RustType::Bool;

        // Same types are compatible
        assert!(u32_ty.is_compatible(&u32_ty));
        assert!(bool_ty.is_compatible(&bool_ty));

        // Different numeric types are not compatible
        assert!(!u32_ty.is_compatible(&i32_ty));
        assert!(!u32_ty.is_compatible(&bool_ty));
    }
}
