// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared inventory of type occurrences. ID references are not followed:
//! module tables are visited once, independently of their reference graph.

use crate::{Inst, InstG, Module, Ty, TyG};

impl<X> TyG<X> {
    /// Visit this type and every recursively embedded inline child in preorder.
    /// References into module tables are not followed.
    pub fn visit_types<'a>(&'a self, mut visit: impl FnMut(&'a TyG<X>)) {
        self.visit_types_with(&mut visit);
    }

    fn visit_types_with<'a>(&'a self, visit: &mut impl FnMut(&'a TyG<X>)) {
        let mut pending: Vec<std::slice::Iter<'a, TyG<X>>> = Vec::new();
        let mut current = self;
        loop {
            visit(current);
            match current {
                TyG::Storage(_) => {}
                TyG::Vector(inner, _)
                | TyG::Tensor(inner, _)
                | TyG::Ref(inner)
                | TyG::RefMut(inner)
                | TyG::PtrConst(inner)
                | TyG::PtrMut(inner)
                | TyG::Rc(inner) => {
                    current = inner;
                    continue;
                }
                TyG::Tuple(types) => {
                    if let Some((first, rest)) = types.split_first() {
                        if !rest.is_empty() {
                            pending.push(rest.iter());
                        }
                        current = first;
                        continue;
                    }
                }
                TyG::I8
                | TyG::I16
                | TyG::I32
                | TyG::I64
                | TyG::I128
                | TyG::U8
                | TyG::U16
                | TyG::U32
                | TyG::U64
                | TyG::U128
                | TyG::Isize
                | TyG::Usize
                | TyG::Char
                | TyG::Error
                | TyG::F16
                | TyG::F32
                | TyG::F64
                | TyG::Bool
                | TyG::Ptr
                | TyG::FatPtr(_)
                | TyG::Unit
                | TyG::Never
                | TyG::Struct(_)
                | TyG::Array(_, _)
                | TyG::Enum(_)
                | TyG::Func(_)
                | TyG::Set(_, _)
                | TyG::Sequence(_)
                | TyG::Record(_)
                | TyG::Closure(_)
                | TyG::Refine(_, _)
                | TyG::Dialect(_)
                | TyG::Handle(_) => {}
                TyG::Ext(_) => {}
            }
            loop {
                let Some(siblings) = pending.last_mut() else {
                    return;
                };
                if let Some(next) = siblings.next() {
                    current = next;
                    break;
                }
                pending.pop();
            }
        }
    }
}

impl Ty {
    /// Whether this inline type tree includes an unlegalized dialect type.
    /// Named type definitions must be inspected separately in their module.
    pub fn contains_dialect(&self) -> bool {
        let mut found = false;
        self.visit_types(|ty| found |= matches!(ty, Ty::Dialect(_)));
        found
    }

    /// Whether this inline type tree includes a nominal opaque runtime handle
    /// (v43). Named type definitions must be inspected separately in their
    /// module (`Module::nominal_type_reachability`).
    pub fn contains_handle(&self) -> bool {
        let mut found = false;
        self.visit_types(|ty| found |= matches!(ty, Ty::Handle(_)));
        found
    }
}

impl<X> InstG<X> {
    /// Visit every type spelled by this instruction, including inline children
    /// and type-valued dialect attributes, telling the level's own types
    /// ([`TypeOccurrence::Spelled`]) from the level-R types a binding frame or
    /// dialect op carries at every level ([`TypeOccurrence::Ground`]). Table
    /// references are not followed.
    pub fn visit_type_occurrences<'a>(&'a self, mut visit: impl FnMut(TypeOccurrence<'a, X>)) {
        self.visit_type_root_occurrences(|root| match root {
            TypeOccurrence::Spelled(ty) => {
                ty.visit_types_with(&mut |t| visit(TypeOccurrence::Spelled(t)))
            }
            TypeOccurrence::Ground(ty) => {
                ty.visit_types_with(&mut |t| visit(TypeOccurrence::Ground(t)))
            }
        });
    }

    /// Borrow each actual type root without interpreting pointer pointees as
    /// separately transported values. The original full visitor expands these
    /// same roots; there is only one exhaustive instruction-field projection.
    pub fn visit_type_root_occurrences<'a>(&'a self, mut visit: impl FnMut(TypeOccurrence<'a, X>)) {
        let mut roots: Vec<&'a TyG<X>> = Vec::new();
        let mut ground: Vec<&'a Ty> = Vec::new();
        let mut root = |ty: &'a TyG<X>| roots.push(ty);
        match self {
            // Trust (wave-DS): the dropped type is spelled here and must be walked, or a
            // splice would not remap a struct/enum id occurring only in a drop.
            InstG::Drop { ty, .. } | InstG::DropInvoke { ty, .. } => root(ty),
            InstG::BinOp { ty, .. }
            | InstG::SeqMapAddK { ty, .. }
            | InstG::SeqMapNot { ty, .. }
            | InstG::SeqMap { ty, .. }
            | InstG::UnOp { ty, .. }
            | InstG::Overflow { ty, .. }
            | InstG::ICmp { ty, .. }
            | InstG::FCmp { ty, .. }
            | InstG::Load { ty, .. }
            | InstG::Store { ty, .. }
            | InstG::Alloca { ty, .. }
            | InstG::HeapAlloc { ty, .. }
            | InstG::AtomicLoad { ty, .. }
            | InstG::AtomicStore { ty, .. }
            | InstG::AtomicRMW { ty, .. }
            | InstG::CmpXchg { ty, .. }
            | InstG::MakeAggregate { ty, .. }
            | InstG::ArraySplat { ty, .. }
            | InstG::TensorContract { ty, .. }
            | InstG::TensorReduce { ty, .. }
            | InstG::TensorView { ty, .. }
            | InstG::TensorGather { ty, .. }
            | InstG::TensorScatter { ty, .. }
            | InstG::ExtractField { ty, .. }
            | InstG::InsertField { ty, .. }
            | InstG::ExtractElement { ty, .. }
            | InstG::InsertElement { ty, .. }
            | InstG::Const { ty, .. }
            | InstG::Undef { ty }
            | InstG::Copy { ty, .. }
            | InstG::Select { ty, .. }
            | InstG::LoadSlot { ty, .. } => root(ty),
            InstG::Cast { src_ty, dst_ty, .. } => {
                root(src_ty);
                root(dst_ty);
            }
            // PKG-U13c: the result type, then each body node's types in
            // node order (a cast node spells two).
            InstG::TensorMap { ty, body, .. } => {
                root(ty);
                for node in body {
                    for node_ty in node.types() {
                        root(node_ty);
                    }
                }
            }
            InstG::GEP { pointee_ty, .. } => root(pointee_ty),
            InstG::PtrData { ptr_ty, .. } => root(ptr_ty),
            InstG::PtrMetadata {
                ptr_ty,
                metadata_ty,
                ..
            }
            | InstG::PtrFromParts {
                ptr_ty,
                metadata_ty,
                ..
            } => {
                root(ptr_ty);
                root(metadata_ty);
            }
            InstG::OpenFrame { def } => {
                for slot in &def.slots {
                    ground.push(&slot.ty);
                }
            }
            InstG::DialectOp(op) => {
                for ty in &op.result_tys {
                    ground.push(ty);
                }
                for attr in &op.attrs {
                    if let crate::dialect::AttrValue::Ty(ty) = &attr.value {
                        ground.push(ty);
                    }
                }
            }
            InstG::Fence { .. }
            | InstG::Br { .. }
            | InstG::CondBr { .. }
            | InstG::Switch { .. }
            | InstG::Call { .. }
            | InstG::CallIndirect { .. }
            | InstG::MakeClosure { .. }
            | InstG::CallCannotUnwind { .. }
            | InstG::CallIndirectCannotUnwind { .. }
            | InstG::InvokeIndirect { .. }
            | InstG::Return { .. }
            | InstG::NullPtr
            | InstG::GlobalAddr { .. }
            | InstG::Assume { .. }
            | InstG::Assert { .. }
            | InstG::Unreachable
            | InstG::Borrow { .. }
            | InstG::BorrowMut { .. }
            | InstG::EndBorrow { .. }
            | InstG::Retain { .. }
            | InstG::Release { .. }
            | InstG::IsUnique { .. }
            | InstG::Dealloc { .. }
            // WS3.20: the bulk ops are byte-granular and spell no type.
            | InstG::MemCopy { .. }
            | InstG::MemSet { .. }
            | InstG::BindSlot { .. }
            | InstG::CloseFrame { .. }
            | InstG::CoroSuspend { .. }
            | InstG::Invoke { .. }
            | InstG::LandingPad { .. }
            | InstG::Resume { .. }
            | InstG::AssertInvoke { .. } => {}
        }
        for ty in roots {
            visit(TypeOccurrence::Spelled(ty));
        }
        for ty in ground {
            visit(TypeOccurrence::Ground(ty));
        }
    }
}

/// A type an instruction spells: one of the level's own types, or a level-R
/// type a binding frame or a dialect op carries at every level.
pub enum TypeOccurrence<'a, X> {
    Spelled(&'a TyG<X>),
    Ground(&'a Ty),
}

impl Inst {
    /// Each spelled type root, without descending through pointer pointees.
    pub fn visit_type_roots<'a>(&'a self, mut visit: impl FnMut(&'a Ty)) {
        self.visit_type_root_occurrences(|occurrence| match occurrence {
            TypeOccurrence::Spelled(ty) | TypeOccurrence::Ground(ty) => visit(ty),
        });
    }

    /// Visit every type spelled by this instruction, including inline children
    /// and type-valued dialect attributes. Table references are not followed.
    pub fn visit_types<'a>(&'a self, mut visit: impl FnMut(&'a Ty)) {
        self.visit_type_occurrences(|occurrence| match occurrence {
            TypeOccurrence::Spelled(ty) | TypeOccurrence::Ground(ty) => visit(ty),
        });
    }
}

impl Module {
    /// Visit every stored type occurrence, including unused table entries,
    /// signatures, aggregate fields, closure captures, block parameters, and
    /// instruction types. Inline children are visited recursively; table IDs
    /// are not followed, so cyclic type-table references do not repeat work.
    pub fn visit_types<'a>(&'a self, mut visit: impl FnMut(&'a Ty)) {
        for ty in &self.types {
            ty.visit_types_with(&mut visit);
        }
        for signature in &self.func_types {
            for ty in signature.params.iter().chain(&signature.returns) {
                ty.visit_types_with(&mut visit);
            }
        }
        for definition in &self.structs {
            for field in &definition.fields {
                field.ty.visit_types_with(&mut visit);
            }
        }
        for definition in &self.records {
            for field in &definition.fields {
                field.ty.visit_types_with(&mut visit);
            }
        }
        for definition in &self.enums {
            for variant in &definition.variants {
                for ty in &variant.fields {
                    ty.visit_types_with(&mut visit);
                }
            }
        }
        for closure in &self.closure_types {
            for ty in &closure.captures {
                ty.visit_types_with(&mut visit);
            }
        }
        for global in &self.globals {
            global.ty.visit_types_with(&mut visit);
        }
        // Amendment D: a drop-glue row's key is an inline type.
        for entry in &self.drop_glue {
            entry.ty.visit_types_with(&mut visit);
        }
        for function in &self.functions {
            for block in &function.blocks {
                for (_, ty) in &block.params {
                    ty.visit_types_with(&mut visit);
                }
                for node in &block.body {
                    node.inst.visit_types(&mut visit);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn visitor_is_preorder_and_allows_retaining_a_borrow() {
        let ty = Ty::Tuple(vec![
            Ty::Ref(Box::new(Ty::I64)),
            Ty::Dialect(Box::new(crate::DialectTy::new("example", "value", 1))),
        ]);
        let mut seen = Vec::new();
        let mut identity = None;
        ty.visit_types(|child| {
            seen.push(child.shape());
            if let Ty::Dialect(nominal) = child {
                identity = Some(nominal.as_ref());
            }
        });
        assert_eq!(
            seen,
            vec![
                crate::shape::TyShape::Tuple,
                crate::shape::TyShape::Ref,
                crate::shape::TyShape::Int {
                    signed: true,
                    bits: 64
                },
                crate::shape::TyShape::Dialect
            ]
        );
        assert_eq!(identity.unwrap().name, "value");
    }

    #[test]
    fn deeply_nested_inline_types_use_no_rust_call_stack() {
        let mut ty = Ty::Dialect(Box::new(crate::DialectTy::new("example", "value", 1)));
        for _ in 0..100_000 {
            ty = Ty::Ref(Box::new(ty));
        }
        let mut count = 0;
        ty.visit_types(|_| count += 1);
        assert_eq!(count, 100_001);
        assert!(ty.contains_dialect());
        assert!(!ty.contains_handle());
        // The derived destructor is unrelated to the visitor under test;
        // dismantle the adversarial input iteratively too.
        while let Ty::Ref(inner) = ty {
            ty = *inner;
        }
    }

    #[test]
    fn handle_census_sees_inline_occurrences_only() {
        let handle = Ty::handle("Nat", "trust_bignum::Nat");
        assert!(handle.contains_handle());
        assert!(!handle.contains_dialect());
        assert!(Ty::Tuple(vec![Ty::I8, Ty::Ref(Box::new(handle))]).contains_handle());
        // A table reference is not followed: the module walk decides that.
        assert!(!Ty::Array(crate::TyId::new(0), 1).contains_handle());
    }

    #[test]
    fn a_tensor_element_is_an_inline_child_and_a_contraction_spells_its_type() {
        use crate::shape::TyShape;
        let handle = Ty::handle("Nat", "trust_bignum::Nat");
        let tensor = Ty::Tensor(Box::new(handle), 2);
        let mut seen = Vec::new();
        tensor.visit_types(|child| seen.push(child.shape()));
        assert_eq!(seen, [TyShape::Tensor, TyShape::Handle]);
        assert!(tensor.contains_handle());
        let contract = Inst::TensorContract {
            ty: Ty::Tensor(Box::new(Ty::I32), 2),
            lhs: crate::ValueId::new(0),
            rhs: crate::ValueId::new(1),
            batch: vec![],
            contract: vec![(1, 0)],
        };
        let mut roots = Vec::new();
        contract.visit_type_roots(|ty| roots.push(ty.clone()));
        assert_eq!(roots, vec![Ty::Tensor(Box::new(Ty::I32), 2)]);
        let mut all = Vec::new();
        contract.visit_types(|ty| all.push(ty.clone()));
        assert_eq!(all, vec![Ty::Tensor(Box::new(Ty::I32), 2), Ty::I32]);
    }

    #[test]
    fn tuple_iterator_scratch_tracks_depth_not_width_and_does_not_follow_ids() {
        let ty = Ty::Tuple(vec![Ty::Tuple(vec![Ty::I8, Ty::I16]), Ty::I32]);
        let mut count = 0;
        ty.visit_types(|_| count += 1);
        assert_eq!(count, 5);
        let mut module = Module::new("cycle");
        module.types.push(Ty::Array(crate::TyId::new(0), 1));
        let mut count = 0;
        module.visit_types(|_| count += 1);
        assert_eq!(count, 1);
    }
}
