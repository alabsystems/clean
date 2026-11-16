// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exact structural equality for the raw metadata census.
//!
//! This is comparison, not type admission or proof authentication. All current
//! variants are named in both coordinates of each pair match. Diagonal arms
//! compare every payload; the remaining explicitly named crossproduct rejects
//! different variants. A new producer variant makes the match nonexhaustive.
//! Raw IDs are compared unchanged, never resolved or canonicalized. The current
//! standalone dependency does not enable the feature-gated Goal annotation;
//! enabling that producer feature must force an explicit reader change.

use trust_ir::inst::Ordering;
use trust_ir::proof::Divergence;
use trust_ir::ty::{DialectTy, FatPtrKind, HandleTy, SetRepr, Ty};
use trust_ir::ProofAnnotation;

pub(super) fn ty_matches(a: &Ty, b: &Ty) -> bool {
    match (a, b) {
        (Ty::I8, Ty::I8)
        | (Ty::I16, Ty::I16)
        | (Ty::I32, Ty::I32)
        | (Ty::I64, Ty::I64)
        | (Ty::I128, Ty::I128)
        | (Ty::U8, Ty::U8)
        | (Ty::U16, Ty::U16)
        | (Ty::U32, Ty::U32)
        | (Ty::U64, Ty::U64)
        | (Ty::U128, Ty::U128)
        | (Ty::Isize, Ty::Isize)
        | (Ty::Usize, Ty::Usize)
        | (Ty::Char, Ty::Char)
        | (Ty::Error, Ty::Error)
        | (Ty::F16, Ty::F16)
        | (Ty::F32, Ty::F32)
        | (Ty::F64, Ty::F64)
        | (Ty::Bool, Ty::Bool)
        | (Ty::Ptr, Ty::Ptr)
        | (Ty::Unit, Ty::Unit)
        | (Ty::Never, Ty::Never) => true,
        (Ty::Vector(a, an), Ty::Vector(b, bn)) => an == bn && ty_matches(a, b),
        (Ty::Tensor(a, an), Ty::Tensor(b, bn)) => an == bn && ty_matches(a, b),
        (Ty::FatPtr(a), Ty::FatPtr(b)) => fat_matches(a, b),
        (Ty::Storage(a), Ty::Storage(b)) => a == b,
        (Ty::Struct(a), Ty::Struct(b)) => a == b,
        (Ty::Array(a, an), Ty::Array(b, bn)) => a == b && an == bn,
        (Ty::Tuple(a), Ty::Tuple(b)) => tys_match(a, b),
        (Ty::Enum(a), Ty::Enum(b)) => a == b,
        (Ty::Func(a), Ty::Func(b)) => a == b,
        (Ty::FnItem(a), Ty::FnItem(b)) => a == b,
        (Ty::Ref(a), Ty::Ref(b)) => ty_matches(a, b),
        (Ty::RefMut(a), Ty::RefMut(b)) => ty_matches(a, b),
        (Ty::PtrConst(a), Ty::PtrConst(b)) => ty_matches(a, b),
        (Ty::PtrMut(a), Ty::PtrMut(b)) => ty_matches(a, b),
        (Ty::Rc(a), Ty::Rc(b)) => ty_matches(a, b),
        (Ty::Set(a, ar), Ty::Set(b, br)) => a == b && set_matches(ar, br),
        (Ty::Sequence(a), Ty::Sequence(b)) => a == b,
        (Ty::Record(a), Ty::Record(b)) => a == b,
        (Ty::Closure(a), Ty::Closure(b)) => a == b,
        (Ty::Refine(a, ap), Ty::Refine(b, bp)) => a == b && ap == bp,
        (Ty::Dialect(a), Ty::Dialect(b)) => {
            let DialectTy {
                namespace: an,
                name: at,
                version: av,
            } = a.as_ref();
            let DialectTy {
                namespace: bn,
                name: bt,
                version: bv,
            } = b.as_ref();
            an == bn && at == bt && av == bv
        }
        (Ty::Handle(a), Ty::Handle(b)) => {
            let HandleTy {
                name: an,
                runtime: ar,
            } = a.as_ref();
            let HandleTy {
                name: bn,
                runtime: br,
            } = b.as_ref();
            an == bn && ar == br
        }
        (
            Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::Char
            | Ty::Error
            | Ty::F16
            | Ty::F32
            | Ty::F64
            | Ty::Bool
            | Ty::Ptr
            | Ty::Unit
            | Ty::Never
            | Ty::Vector(_, _)
            | Ty::FatPtr(_)
            | Ty::Struct(_)
            | Ty::Array(_, _)
            | Ty::Tuple(_)
            | Ty::Enum(_)
            | Ty::Func(_)
            | Ty::FnItem(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Rc(_)
            | Ty::Set(_, _)
            | Ty::Sequence(_)
            | Ty::Record(_)
            | Ty::Closure(_)
            | Ty::Refine(_, _)
            | Ty::Dialect(_)
            | Ty::Storage(_)
            | Ty::Tensor(_, _)
            | Ty::Handle(_)
            // trust-ir amendment S: uninhabited at level R, named so the arm stays exhaustive.
            | Ty::Ext(_),
            Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::Char
            | Ty::Error
            | Ty::F16
            | Ty::F32
            | Ty::F64
            | Ty::Bool
            | Ty::Ptr
            | Ty::Unit
            | Ty::Never
            | Ty::Vector(_, _)
            | Ty::FatPtr(_)
            | Ty::Struct(_)
            | Ty::Array(_, _)
            | Ty::Tuple(_)
            | Ty::Enum(_)
            | Ty::Func(_)
            | Ty::FnItem(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Rc(_)
            | Ty::Set(_, _)
            | Ty::Sequence(_)
            | Ty::Record(_)
            | Ty::Closure(_)
            | Ty::Refine(_, _)
            | Ty::Dialect(_)
            | Ty::Storage(_)
            | Ty::Tensor(_, _)
            | Ty::Handle(_)
            // trust-ir amendment S: uninhabited at level R, named so the arm stays exhaustive.
            | Ty::Ext(_),
        ) => false,
    }
}

fn tys_match(a: &[Ty], b: &[Ty]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(a, b)| ty_matches(a, b))
}

pub(super) fn fat_matches(a: &FatPtrKind, b: &FatPtrKind) -> bool {
    match (a, b) {
        (FatPtrKind::Str, FatPtrKind::Str)
        | (FatPtrKind::ContainerLen, FatPtrKind::ContainerLen)
        | (FatPtrKind::ContainerVtable, FatPtrKind::ContainerVtable) => true,
        (FatPtrKind::Slice(a), FatPtrKind::Slice(b)) => a == b,
        (FatPtrKind::TraitObject { trait_id: a }, FatPtrKind::TraitObject { trait_id: b }) => {
            a == b
        }
        (
            FatPtrKind::Str
            | FatPtrKind::ContainerLen
            | FatPtrKind::ContainerVtable
            | FatPtrKind::Slice(_)
            | FatPtrKind::TraitObject { trait_id: _ },
            FatPtrKind::Str
            | FatPtrKind::ContainerLen
            | FatPtrKind::ContainerVtable
            | FatPtrKind::Slice(_)
            | FatPtrKind::TraitObject { trait_id: _ },
        ) => false,
    }
}

pub(super) fn set_matches(a: &SetRepr, b: &SetRepr) -> bool {
    match (a, b) {
        (SetRepr::Bitset, SetRepr::Bitset) | (SetRepr::Boxed, SetRepr::Boxed) => true,
        (SetRepr::Bitset | SetRepr::Boxed, SetRepr::Bitset | SetRepr::Boxed) => false,
    }
}

pub(super) fn ordering_matches(a: &Ordering, b: &Ordering) -> bool {
    match (a, b) {
        (Ordering::Relaxed, Ordering::Relaxed)
        | (Ordering::Acquire, Ordering::Acquire)
        | (Ordering::Release, Ordering::Release)
        | (Ordering::AcqRel, Ordering::AcqRel)
        | (Ordering::SeqCst, Ordering::SeqCst) => true,
        (
            Ordering::Relaxed
            | Ordering::Acquire
            | Ordering::Release
            | Ordering::AcqRel
            | Ordering::SeqCst,
            Ordering::Relaxed
            | Ordering::Acquire
            | Ordering::Release
            | Ordering::AcqRel
            | Ordering::SeqCst,
        ) => false,
    }
}

pub(super) fn divergence_matches(a: &Divergence, b: &Divergence) -> bool {
    match (a, b) {
        (Divergence::Uniform, Divergence::Uniform)
        | (Divergence::Low, Divergence::Low)
        | (Divergence::High, Divergence::High) => true,
        (
            Divergence::Uniform | Divergence::Low | Divergence::High,
            Divergence::Uniform | Divergence::Low | Divergence::High,
        ) => false,
    }
}

/// Retain ordinary f64 PartialEq for BoundedOutput: NaN is unequal, while
/// positive and negative zero compare equal. No byte/tag equality is used.
pub(super) fn proof_matches(a: &ProofAnnotation, b: &ProofAnnotation) -> bool {
    match (a, b) {
        (ProofAnnotation::InBounds, ProofAnnotation::InBounds)
        | (ProofAnnotation::NotNull, ProofAnnotation::NotNull)
        | (ProofAnnotation::ValidBorrow, ProofAnnotation::ValidBorrow)
        | (ProofAnnotation::UniqueBorrow, ProofAnnotation::UniqueBorrow)
        | (ProofAnnotation::SharedBorrow, ProofAnnotation::SharedBorrow)
        | (ProofAnnotation::ValidDealloc, ProofAnnotation::ValidDealloc)
        | (ProofAnnotation::NoOverflow, ProofAnnotation::NoOverflow)
        | (ProofAnnotation::NoWrap, ProofAnnotation::NoWrap)
        | (ProofAnnotation::DivNonZero, ProofAnnotation::DivNonZero)
        | (ProofAnnotation::ShiftInRange, ProofAnnotation::ShiftInRange)
        | (ProofAnnotation::Wrapping, ProofAnnotation::Wrapping)
        | (ProofAnnotation::Pure, ProofAnnotation::Pure)
        | (ProofAnnotation::Terminates, ProofAnnotation::Terminates)
        | (ProofAnnotation::Deterministic, ProofAnnotation::Deterministic)
        | (ProofAnnotation::Associative, ProofAnnotation::Associative)
        | (ProofAnnotation::Commutative, ProofAnnotation::Commutative)
        | (ProofAnnotation::DataRaceFree, ProofAnnotation::DataRaceFree)
        | (ProofAnnotation::Monotonic, ProofAnnotation::Monotonic)
        | (ProofAnnotation::NoAlias, ProofAnnotation::NoAlias)
        | (ProofAnnotation::NoPanic, ProofAnnotation::NoPanic)
        | (ProofAnnotation::NoUndef, ProofAnnotation::NoUndef)
        | (ProofAnnotation::Tainted, ProofAnnotation::Tainted)
        | (ProofAnnotation::TrustedSink, ProofAnnotation::TrustedSink)
        | (ProofAnnotation::ReadonlyTable, ProofAnnotation::ReadonlyTable)
        | (ProofAnnotation::AppendOnlyBuffer, ProofAnnotation::AppendOnlyBuffer)
        | (ProofAnnotation::AtomicSetInsert, ProofAnnotation::AtomicSetInsert)
        | (ProofAnnotation::ParallelMap, ProofAnnotation::ParallelMap)
        | (ProofAnnotation::FreshSymbolicHavoc, ProofAnnotation::FreshSymbolicHavoc)
        | (ProofAnnotation::RegionHavocStore, ProofAnnotation::RegionHavocStore) => true,
        (ProofAnnotation::AtomicOrdering(a), ProofAnnotation::AtomicOrdering(b)) => {
            ordering_matches(a, b)
        }
        (
            ProofAnnotation::BoundedOutput { lo: al, hi: ah },
            ProofAnnotation::BoundedOutput { lo: bl, hi: bh },
        ) => al == bl && ah == bh,
        (ProofAnnotation::Aligned(a), ProofAnnotation::Aligned(b)) => a == b,
        (ProofAnnotation::BoundedLoop(a), ProofAnnotation::BoundedLoop(b)) => a == b,
        (ProofAnnotation::DivergenceClass(a), ProofAnnotation::DivergenceClass(b)) => {
            divergence_matches(a, b)
        }
        (ProofAnnotation::Custom(a), ProofAnnotation::Custom(b)) => a == b,
        (ProofAnnotation::ProofRef(a), ProofAnnotation::ProofRef(b)) => a == b,
        (
            ProofAnnotation::ValueRange { lo: al, hi: ah },
            ProofAnnotation::ValueRange { lo: bl, hi: bh },
        ) => al == bl && ah == bh,
        (
            ProofAnnotation::KnownBits {
                zeros: az,
                ones: ao,
            },
            ProofAnnotation::KnownBits {
                zeros: bz,
                ones: bo,
            },
        ) => az == bz && ao == bo,
        (ProofAnnotation::BranchWeights(a), ProofAnnotation::BranchWeights(b)) => a == b,
        (
            ProofAnnotation::InBounds
            | ProofAnnotation::NotNull
            | ProofAnnotation::ValidBorrow
            | ProofAnnotation::UniqueBorrow
            | ProofAnnotation::SharedBorrow
            | ProofAnnotation::ValidDealloc
            | ProofAnnotation::NoOverflow
            | ProofAnnotation::NoWrap
            | ProofAnnotation::DivNonZero
            | ProofAnnotation::ShiftInRange
            | ProofAnnotation::Wrapping
            | ProofAnnotation::Pure
            | ProofAnnotation::Terminates
            | ProofAnnotation::Deterministic
            | ProofAnnotation::Associative
            | ProofAnnotation::Commutative
            | ProofAnnotation::DataRaceFree
            | ProofAnnotation::Monotonic
            | ProofAnnotation::NoAlias
            | ProofAnnotation::NoPanic
            | ProofAnnotation::NoUndef
            | ProofAnnotation::Tainted
            | ProofAnnotation::TrustedSink
            | ProofAnnotation::ReadonlyTable
            | ProofAnnotation::AppendOnlyBuffer
            | ProofAnnotation::AtomicSetInsert
            | ProofAnnotation::ParallelMap
            | ProofAnnotation::FreshSymbolicHavoc
            | ProofAnnotation::RegionHavocStore
            | ProofAnnotation::AtomicOrdering(_)
            | ProofAnnotation::BoundedOutput { lo: _, hi: _ }
            | ProofAnnotation::Aligned(_)
            | ProofAnnotation::BoundedLoop(_)
            | ProofAnnotation::DivergenceClass(_)
            | ProofAnnotation::Custom(_)
            | ProofAnnotation::ProofRef(_)
            | ProofAnnotation::ValueRange { lo: _, hi: _ }
            | ProofAnnotation::KnownBits { zeros: _, ones: _ }
            | ProofAnnotation::BranchWeights(_),
            ProofAnnotation::InBounds
            | ProofAnnotation::NotNull
            | ProofAnnotation::ValidBorrow
            | ProofAnnotation::UniqueBorrow
            | ProofAnnotation::SharedBorrow
            | ProofAnnotation::ValidDealloc
            | ProofAnnotation::NoOverflow
            | ProofAnnotation::NoWrap
            | ProofAnnotation::DivNonZero
            | ProofAnnotation::ShiftInRange
            | ProofAnnotation::Wrapping
            | ProofAnnotation::Pure
            | ProofAnnotation::Terminates
            | ProofAnnotation::Deterministic
            | ProofAnnotation::Associative
            | ProofAnnotation::Commutative
            | ProofAnnotation::DataRaceFree
            | ProofAnnotation::Monotonic
            | ProofAnnotation::NoAlias
            | ProofAnnotation::NoPanic
            | ProofAnnotation::NoUndef
            | ProofAnnotation::Tainted
            | ProofAnnotation::TrustedSink
            | ProofAnnotation::ReadonlyTable
            | ProofAnnotation::AppendOnlyBuffer
            | ProofAnnotation::AtomicSetInsert
            | ProofAnnotation::ParallelMap
            | ProofAnnotation::FreshSymbolicHavoc
            | ProofAnnotation::RegionHavocStore
            | ProofAnnotation::AtomicOrdering(_)
            | ProofAnnotation::BoundedOutput { lo: _, hi: _ }
            | ProofAnnotation::Aligned(_)
            | ProofAnnotation::BoundedLoop(_)
            | ProofAnnotation::DivergenceClass(_)
            | ProofAnnotation::Custom(_)
            | ProofAnnotation::ProofRef(_)
            | ProofAnnotation::ValueRange { lo: _, hi: _ }
            | ProofAnnotation::KnownBits { zeros: _, ones: _ }
            | ProofAnnotation::BranchWeights(_),
        ) => false,
    }
}

pub(super) fn proofs_match(a: &[ProofAnnotation], b: &[ProofAnnotation]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(a, b)| proof_matches(a, b))
}
