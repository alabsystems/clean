// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'a> State<'a> {
    pub(super) fn ty<O: ExecutionObserver>(&mut self, ty: &'a Ty, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, size_of::<Ty>())?;
        match ty {
            Ty::Storage(layout) => scheduled!(self, work; [
            Task::Text("Storage(StorageLayout { size_bytes: "),
            Task::Num(u128::from(layout.size_bytes)),
            Task::Text(", align_bytes: "),
            Task::Num(u128::from(layout.align_bytes)),
            Task::Text(" })"),
            ]),
            Ty::I8 => work.text("I8", &mut self.output),
            Ty::I16 => work.text("I16", &mut self.output),
            Ty::I32 => work.text("I32", &mut self.output),
            Ty::I64 => work.text("I64", &mut self.output),
            Ty::I128 => work.text("I128", &mut self.output),
            Ty::U8 => work.text("U8", &mut self.output),
            Ty::U16 => work.text("U16", &mut self.output),
            Ty::U32 => work.text("U32", &mut self.output),
            Ty::U64 => work.text("U64", &mut self.output),
            Ty::U128 => work.text("U128", &mut self.output),
            Ty::Isize => work.text("Isize", &mut self.output),
            Ty::Usize => work.text("Usize", &mut self.output),
            Ty::Char => work.text("Char", &mut self.output),
            Ty::Error => work.text("Error", &mut self.output),
            Ty::F16 => work.text("F16", &mut self.output),
            Ty::F32 => work.text("F32", &mut self.output),
            Ty::F64 => work.text("F64", &mut self.output),
            Ty::Bool => work.text("Bool", &mut self.output),
            Ty::Ptr => work.text("Ptr", &mut self.output),
            Ty::Unit => work.text("Unit", &mut self.output),
            Ty::Never => work.text("Never", &mut self.output),
            Ty::Struct(..)
            | Ty::Enum(..)
            | Ty::Func(..)
            | Ty::Sequence(..)
            | Ty::Record(..)
            | Ty::Closure(..) => self.ids(ty, work),
            Ty::Vector(..)
            | Ty::Tensor(..)
            | Ty::Tuple(..)
            | Ty::Ref(..)
            | Ty::RefMut(..)
            | Ty::PtrConst(..)
            | Ty::PtrMut(..)
            | Ty::Rc(..) => self.inline(ty, work),
            Ty::Array(..) | Ty::Refine(..) | Ty::Set(..) => self.indirect(ty, work),
            Ty::Dialect(..) | Ty::Handle(..) => self.nominal_text(ty, work),
            Ty::FatPtr(..) => self.fat(ty, work),
            Ty::Ext(e) => e.unreachable(),
        }
    }
    fn ids<O: ExecutionObserver>(&mut self, ty: &'a Ty, work: &mut Work<'_, '_, O>) -> R {
        match ty {
            Ty::Struct(id) => scheduled!(self, work; [
                Task::Text("Struct(StructId("),
                Task::Num(u128::from(id.index())),
                Task::Text("))"),
            ]),
            Ty::Enum(id) => scheduled!(self, work; [
                Task::Text("Enum(EnumId("),
                Task::Num(u128::from(id.index())),
                Task::Text("))"),
            ]),
            Ty::Func(id) => scheduled!(self, work; [
                Task::Text("Func(FuncTyId("),
                Task::Num(u128::from(id.index())),
                Task::Text("))"),
            ]),
            Ty::Sequence(id) => scheduled!(self, work; [
                Task::Text("Sequence(TyId("),
                Task::Num(u128::from(id.index())),
                Task::Text("))"),
            ]),
            Ty::Record(id) => scheduled!(self, work; [
                Task::Text("Record(RecordId("),
                Task::Num(u128::from(id.index())),
                Task::Text("))"),
            ]),
            Ty::Closure(id) => scheduled!(self, work; [
                Task::Text("Closure(ClosureTyId("),
                Task::Num(u128::from(id.index())),
                Task::Text("))"),
            ]),
            _ => Err(ObservedValueError::UnsupportedValue),
        }
    }
    fn inline<O: ExecutionObserver>(&mut self, ty: &'a Ty, work: &mut Work<'_, '_, O>) -> R {
        match ty {
            Ty::Vector(t, n) => scheduled!(self, work; [
                Task::Text("Vector("),
                Task::Ty(t),
                Task::Text(", "),
                Task::Num(u128::from(*n)),
                Task::Text(")"),
            ]),
            Ty::Tensor(t, rank) => scheduled!(self, work; [
                Task::Text("Tensor("),
                Task::Ty(t),
                Task::Text(", "),
                Task::Num(u128::from(*rank)),
                Task::Text(")"),
            ]),
            Ty::Tuple(t) => scheduled!(self, work; [
                Task::Text("Tuple(["),
                Task::List(List::Types(t), true),
                Task::Text("])"),
            ]),
            Ty::Ref(t) => {
                scheduled!(self, work; [Task::Text("Ref("), Task::Ty(t), Task::Text(")")])
            }
            Ty::RefMut(t) => {
                scheduled!(self, work; [Task::Text("RefMut("), Task::Ty(t), Task::Text(")")])
            }
            Ty::PtrConst(t) => {
                scheduled!(self, work; [Task::Text("PtrConst("), Task::Ty(t), Task::Text(")")])
            }
            Ty::PtrMut(t) => {
                scheduled!(self, work; [Task::Text("PtrMut("), Task::Ty(t), Task::Text(")")])
            }
            Ty::Rc(t) => scheduled!(self, work; [Task::Text("Rc("), Task::Ty(t), Task::Text(")")]),
            _ => Err(ObservedValueError::UnsupportedValue),
        }
    }
    fn indirect<O: ExecutionObserver>(&mut self, ty: &'a Ty, work: &mut Work<'_, '_, O>) -> R {
        match ty {
            Ty::Array(id, n) => scheduled!(self, work; [
                Task::Text("Array(TyId("),
                Task::Num(u128::from(id.index())),
                Task::Text("), "),
                Task::Num(u128::from(*n)),
                Task::Text(")"),
            ]),
            Ty::Refine(id, p) => scheduled!(self, work; [
                Task::Text("Refine(TyId("),
                Task::Num(u128::from(id.index())),
                Task::Text("), PredId("),
                Task::Num(u128::from(p.index())),
                Task::Text("))"),
            ]),
            Ty::Set(id, r) => scheduled!(self, work; [
                Task::Text("Set(TyId("),
                Task::Num(u128::from(id.index())),
                Task::Text("), "),
                Task::Text(match r {
                    SetRepr::Bitset => "Bitset",
                    SetRepr::Boxed => "Boxed",
                }),
                Task::Text(")"),
            ]),
            _ => Err(ObservedValueError::UnsupportedValue),
        }
    }
    fn nominal_text<O: ExecutionObserver>(&mut self, ty: &'a Ty, work: &mut Work<'_, '_, O>) -> R {
        match ty {
            Ty::Dialect(d) => {
                let DialectTy {
                    namespace,
                    name,
                    version,
                } = d.as_ref();
                scheduled!(self, work; [
                    Task::Text("Dialect(DialectTy { namespace: "),
                    Task::Quoted(namespace),
                    Task::Text(", name: "),
                    Task::Quoted(name),
                    Task::Text(", version: "),
                    Task::Num(u128::from(*version)),
                    Task::Text(" })"),
                ])
            }
            Ty::Handle(h) => {
                let HandleTy { name, runtime } = h.as_ref();
                scheduled!(self, work; [
                    Task::Text("Handle(HandleTy { name: "),
                    Task::Quoted(name),
                    Task::Text(", runtime: "),
                    Task::Quoted(runtime),
                    Task::Text(" })"),
                ])
            }
            _ => Err(ObservedValueError::UnsupportedValue),
        }
    }
    fn fat<O: ExecutionObserver>(&mut self, ty: &'a Ty, work: &mut Work<'_, '_, O>) -> R {
        match ty {
            Ty::FatPtr(k) => {
                work.text("FatPtr(", &mut self.output)?;
                match k {
                    FatPtrKind::Slice(id) => {
                        work.text("Slice(TyId(", &mut self.output)?;
                        work.number(u128::from(id.index()), &mut self.output)?;
                        work.text("))", &mut self.output)?;
                    }
                    FatPtrKind::TraitObject { trait_id } => {
                        work.text("TraitObject { trait_id: ", &mut self.output)?;
                        work.number(u128::from(*trait_id), &mut self.output)?;
                        work.text(" }", &mut self.output)?;
                    }
                    FatPtrKind::Str => work.text("Str", &mut self.output)?,
                    FatPtrKind::ContainerLen => work.text("ContainerLen", &mut self.output)?,
                    FatPtrKind::ContainerVtable => {
                        work.text("ContainerVtable", &mut self.output)?
                    }
                };
                work.text(")", &mut self.output)
            }
            _ => Err(ObservedValueError::UnsupportedValue),
        }
    }
}
