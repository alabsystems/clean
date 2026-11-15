// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

impl<'a> State<'a> {
    pub(super) fn ty<O: ExecutionObserver>(&mut self, ty: &'a Ty, work: &mut Work<'_, '_, O>) -> R {
        match ty {
            Ty::Storage(layout) => {
                work.text("storage<", &mut self.output)?;
                work.number(u128::from(layout.size_bytes), &mut self.output)?;
                work.text(", ", &mut self.output)?;
                work.number(u128::from(layout.align_bytes), &mut self.output)?;
                work.text(">", &mut self.output)
            }
            Ty::I8 => work.text("i8", &mut self.output),
            Ty::I16 => work.text("i16", &mut self.output),
            Ty::I32 => work.text("i32", &mut self.output),
            Ty::I64 => work.text("i64", &mut self.output),
            Ty::I128 => work.text("i128", &mut self.output),
            Ty::U8 => work.text("u8", &mut self.output),
            Ty::U16 => work.text("u16", &mut self.output),
            Ty::U32 => work.text("u32", &mut self.output),
            Ty::U64 => work.text("u64", &mut self.output),
            Ty::U128 => work.text("u128", &mut self.output),
            Ty::Isize => work.text("isize", &mut self.output),
            Ty::Usize => work.text("usize", &mut self.output),
            Ty::Char => work.text("char", &mut self.output),
            Ty::Error => work.text("{error}", &mut self.output),
            Ty::F16 => work.text("f16", &mut self.output),
            Ty::F32 => work.text("f32", &mut self.output),
            Ty::F64 => work.text("f64", &mut self.output),
            Ty::Bool => work.text("bool", &mut self.output),
            Ty::Ptr => work.text("ptr", &mut self.output),
            Ty::Unit => work.text("()", &mut self.output),
            Ty::Never => work.text("!", &mut self.output),
            Ty::Vector(element, lanes) => {
                work.text("<", &mut self.output)?;
                work.number(u128::from(*lanes), &mut self.output)?;
                work.text(" x ", &mut self.output)?;
                self.push(Task::Text(">"), work)?;
                self.push(Task::Type(element), work)
            }
            // `tensor<{elem}, {rank}>`: the rank follows the element, so it
            // waits on the task stack behind it.
            Ty::Tensor(element, rank) => {
                work.text("tensor<", &mut self.output)?;
                self.push(Task::Text(">"), work)?;
                self.push(Task::Number(*rank), work)?;
                self.push(Task::Text(", "), work)?;
                self.push(Task::Type(element), work)
            }
            Ty::Ref(inner) => self.wrapped("&", "", inner, work),
            Ty::RefMut(inner) => self.wrapped("&mut ", "", inner, work),
            Ty::PtrConst(inner) => self.wrapped("*const ", "", inner, work),
            Ty::PtrMut(inner) => self.wrapped("*mut ", "", inner, work),
            Ty::Rc(inner) => self.wrapped("Rc<", ">", inner, work),
            Ty::Tuple(types) => {
                if types.is_empty() {
                    return work.text("(,)", &mut self.output);
                }
                work.text("(", &mut self.output)?;
                self.push(Task::Text(")"), work)?;
                self.push(Task::Types(types, true), work)
            }
            Ty::Struct(id) => self.id("struct.", id.index(), work),
            Ty::Enum(id) => self.id("enum.", id.index(), work),
            Ty::Func(id) => self.id("functy.", id.index(), work),
            Ty::Record(id) => self.id("record.", id.index(), work),
            Ty::Closure(id) => self.id("closure.", id.index(), work),
            Ty::Sequence(id) => {
                self.id("seq<ty.", id.index(), work)?;
                work.text(">", &mut self.output)
            }
            Ty::Array(id, len) => {
                self.id("[ty.", id.index(), work)?;
                work.text(" x ", &mut self.output)?;
                work.number(u128::from(*len), &mut self.output)?;
                work.text("]", &mut self.output)
            }
            Ty::Refine(id, predicate) => {
                self.id("refine<ty.", id.index(), work)?;
                self.id(", pred.", predicate.index(), work)?;
                work.text(">", &mut self.output)
            }
            Ty::Set(id, repr) => {
                self.id("set<ty.", id.index(), work)?;
                work.text(", ", &mut self.output)?;
                work.admit(2, 0)?;
                work.text(
                    match repr {
                        SetRepr::Bitset => "bitset",
                        SetRepr::Boxed => "boxed",
                    },
                    &mut self.output,
                )?;
                work.text(">", &mut self.output)
            }
            Ty::FatPtr(kind) => self.fat(*kind, work),
            Ty::Dialect(ty) => {
                work.text("dialect<", &mut self.output)?;
                work.text(&ty.namespace, &mut self.output)?;
                work.text(", ", &mut self.output)?;
                work.text(&ty.name, &mut self.output)?;
                work.text(", ", &mut self.output)?;
                work.number(u128::from(ty.version), &mut self.output)?;
                work.text(">", &mut self.output)
            }
            Ty::Handle(ty) => {
                work.text("handle<", &mut self.output)?;
                work.quoted(&ty.name, &mut self.output)?;
                work.text(", ", &mut self.output)?;
                work.quoted(&ty.runtime, &mut self.output)?;
                work.text(">", &mut self.output)
            }
            Ty::Ext(extension) => extension.unreachable(),
        }
    }

    fn fat<O: ExecutionObserver>(&mut self, kind: FatPtrKind, work: &mut Work<'_, '_, O>) -> R {
        work.admit(5, 0)?;
        work.text("fatptr<", &mut self.output)?;
        match kind {
            FatPtrKind::Slice(id) => self.id("slice ty.", id.index(), work)?,
            FatPtrKind::Str => work.text("str", &mut self.output)?,
            FatPtrKind::TraitObject { trait_id } => self.id("dyn.", trait_id, work)?,
            FatPtrKind::ContainerLen => work.text("container_len", &mut self.output)?,
            FatPtrKind::ContainerVtable => work.text("container_vtable", &mut self.output)?,
        }
        work.text(">", &mut self.output)
    }
}
