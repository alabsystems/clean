// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'a> State<'a> {
    pub(super) fn ty_text<O: ExecutionObserver>(
        &mut self,
        ty: &'a Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        match ty {
            Ty::Storage(layout) => {
                work.text("Storage(StorageLayout { size_bytes: ", &mut self.detail)?;
                work.number(u128::from(layout.size_bytes), &mut self.detail)?;
                work.text(", align_bytes: ", &mut self.detail)?;
                work.number(u128::from(layout.align_bytes), &mut self.detail)?;
                work.text(" })", &mut self.detail)
            }
            Ty::I8 => work.text("I8", &mut self.detail),
            Ty::I16 => work.text("I16", &mut self.detail),
            Ty::I32 => work.text("I32", &mut self.detail),
            Ty::I64 => work.text("I64", &mut self.detail),
            Ty::I128 => work.text("I128", &mut self.detail),
            Ty::U8 => work.text("U8", &mut self.detail),
            Ty::U16 => work.text("U16", &mut self.detail),
            Ty::U32 => work.text("U32", &mut self.detail),
            Ty::U64 => work.text("U64", &mut self.detail),
            Ty::U128 => work.text("U128", &mut self.detail),
            Ty::Isize => work.text("Isize", &mut self.detail),
            Ty::Usize => work.text("Usize", &mut self.detail),
            Ty::Char => work.text("Char", &mut self.detail),
            Ty::Error => work.text("Error", &mut self.detail),
            Ty::F16 => work.text("F16", &mut self.detail),
            Ty::F32 => work.text("F32", &mut self.detail),
            Ty::F64 => work.text("F64", &mut self.detail),
            Ty::Bool => work.text("Bool", &mut self.detail),
            Ty::Ptr => work.text("Ptr", &mut self.detail),
            Ty::Unit => work.text("Unit", &mut self.detail),
            Ty::Never => work.text("Never", &mut self.detail),
            Ty::Vector(inner, lanes) => {
                work.text("Vector(", &mut self.detail)?;
                self.task(Task::Text(")"), work)?;
                self.task(Task::Number(*lanes as u128), work)?;
                self.task(Task::Text(", "), work)?;
                self.task(Task::Type(inner), work)
            }
            Ty::Tensor(inner, rank) => {
                work.text("Tensor(", &mut self.detail)?;
                self.task(Task::Text(")"), work)?;
                self.task(Task::Number(*rank as u128), work)?;
                self.task(Task::Text(", "), work)?;
                self.task(Task::Type(inner), work)
            }
            Ty::Ref(inner) => self.wrapped("Ref", inner, work),
            Ty::RefMut(inner) => self.wrapped("RefMut", inner, work),
            Ty::PtrConst(inner) => self.wrapped("PtrConst", inner, work),
            Ty::PtrMut(inner) => self.wrapped("PtrMut", inner, work),
            Ty::Rc(inner) => self.wrapped("Rc", inner, work),
            Ty::Tuple(rows) => {
                work.text("Tuple(", &mut self.detail)?;
                self.task(Task::Text(")"), work)?;
                self.task(Task::Types(rows, 0), work)
            }
            Ty::Struct(id) => {
                self.id("Struct(StructId(", id.index(), work)?;
                work.text("))", &mut self.detail)
            }
            Ty::Enum(id) => {
                self.id("Enum(EnumId(", id.index(), work)?;
                work.text("))", &mut self.detail)
            }
            Ty::Func(id) => {
                self.id("Func(FuncTyId(", id.index(), work)?;
                work.text("))", &mut self.detail)
            }
            Ty::Record(id) => {
                self.id("Record(RecordId(", id.index(), work)?;
                work.text("))", &mut self.detail)
            }
            Ty::Closure(id) => {
                self.id("Closure(ClosureTyId(", id.index(), work)?;
                work.text("))", &mut self.detail)
            }
            Ty::Sequence(id) => {
                self.id("Sequence(TyId(", id.index(), work)?;
                work.text("))", &mut self.detail)
            }
            Ty::Array(id, len) => {
                self.id("Array(TyId(", id.index(), work)?;
                work.text("), ", &mut self.detail)?;
                work.number(*len as u128, &mut self.detail)?;
                work.text(")", &mut self.detail)
            }
            Ty::Refine(id, pred) => {
                self.id("Refine(TyId(", id.index(), work)?;
                self.id("), PredId(", pred.index(), work)?;
                work.text("))", &mut self.detail)
            }
            Ty::Set(id, repr) => {
                self.id("Set(TyId(", id.index(), work)?;
                work.text("), ", &mut self.detail)?;
                work.admit(2, size_of::<SetRepr>())?;
                work.text(
                    match repr {
                        SetRepr::Bitset => "Bitset",
                        SetRepr::Boxed => "Boxed",
                    },
                    &mut self.detail,
                )?;
                work.text(")", &mut self.detail)
            }
            Ty::FatPtr(kind) => {
                work.text("FatPtr(", &mut self.detail)?;
                work.admit(5, size_of::<FatPtrKind>())?;
                match kind {
                    FatPtrKind::Slice(id) => {
                        self.id("Slice(TyId(", id.index(), work)?;
                        work.text("))", &mut self.detail)?;
                    }
                    FatPtrKind::Str => work.text("Str", &mut self.detail)?,
                    FatPtrKind::TraitObject { trait_id } => {
                        work.text("TraitObject { trait_id: ", &mut self.detail)?;
                        work.number(*trait_id as u128, &mut self.detail)?;
                        work.text(" }", &mut self.detail)?;
                    }
                    FatPtrKind::ContainerLen => work.text("ContainerLen", &mut self.detail)?,
                    FatPtrKind::ContainerVtable => {
                        work.text("ContainerVtable", &mut self.detail)?
                    }
                }
                work.text(")", &mut self.detail)
            }
            Ty::Dialect(ty) => {
                let DialectTy {
                    namespace,
                    name,
                    version,
                } = ty.as_ref();
                work.text("Dialect(DialectTy { namespace: ", &mut self.detail)?;
                work.quoted(namespace, &mut self.detail)?;
                work.text(", name: ", &mut self.detail)?;
                work.quoted(name, &mut self.detail)?;
                work.text(", version: ", &mut self.detail)?;
                work.number(*version as u128, &mut self.detail)?;
                work.text(" })", &mut self.detail)
            }
            Ty::Handle(ty) => {
                let HandleTy { name, runtime } = ty.as_ref();
                work.text("Handle(HandleTy { name: ", &mut self.detail)?;
                work.quoted(name, &mut self.detail)?;
                work.text(", runtime: ", &mut self.detail)?;
                work.quoted(runtime, &mut self.detail)?;
                work.text(" })", &mut self.detail)
            }
            Ty::Ext(extension) => extension.unreachable(),
        }
    }
}
