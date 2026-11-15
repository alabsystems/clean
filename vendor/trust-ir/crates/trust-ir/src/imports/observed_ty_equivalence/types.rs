// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use crate::ty::FatPtrKind;
pub(super) fn pair<'a, O: ExecutionObserver>(
    s: &mut State<'a>,
    a: &'a Ty,
    b: &'a Ty,
    w: &mut Work<'_, '_, O>,
) -> R {
    w.admit(1 + 2 * size_of::<Ty>(), 2 * size_of::<Ty>())?;
    if core::mem::discriminant(a) != core::mem::discriminant(b) {
        s.last = false;
        return Ok(());
    }
    match (a, b) {
        (Ty::Storage(a), Ty::Storage(b)) => s.last = a == b,
        (Ty::Vector(a, n), Ty::Vector(b, m)) | (Ty::Tensor(a, n), Ty::Tensor(b, m)) => {
            s.last = n == m;
            if s.last {
                s.push(Task::Ty(a, b), w)?;
            }
        }
        (Ty::Ref(a), Ty::Ref(b))
        | (Ty::RefMut(a), Ty::RefMut(b))
        | (Ty::PtrConst(a), Ty::PtrConst(b))
        | (Ty::PtrMut(a), Ty::PtrMut(b))
        | (Ty::Rc(a), Ty::Rc(b)) => s.push(Task::Ty(a, b), w)?,
        (Ty::Array(a, n), Ty::Array(b, m)) => {
            s.last = n == m;
            if s.last {
                s.push(Task::Id(*a, *b), w)?;
            }
        }
        (Ty::Set(a, n), Ty::Set(b, m)) => {
            s.last = n == m;
            if s.last {
                s.push(Task::Id(*a, *b), w)?;
            }
        }
        (Ty::Sequence(a), Ty::Sequence(b)) => s.push(Task::Id(*a, *b), w)?,
        (Ty::Tuple(a), Ty::Tuple(b)) => s.push(Task::Types(a, b), w)?,
        (Ty::Struct(a), Ty::Struct(b)) => {
            s.push(Task::Nominal(Kind::Struct, a.index(), b.index()), w)?
        }
        (Ty::Enum(a), Ty::Enum(b)) => s.push(Task::Nominal(Kind::Enum, a.index(), b.index()), w)?,
        (Ty::Record(a), Ty::Record(b)) => {
            s.push(Task::Nominal(Kind::Record, a.index(), b.index()), w)?
        }
        (Ty::Closure(a), Ty::Closure(b)) => {
            s.push(Task::Nominal(Kind::Closure, a.index(), b.index()), w)?
        }
        (Ty::Func(a), Ty::Func(b)) => s.push(Task::Nominal(Kind::Func, a.index(), b.index()), w)?,
        (Ty::Refine(a, pa), Ty::Refine(b, pb)) => {
            s.push(Task::Pred(*pa, *pb), w)?;
            s.push(Task::Id(*a, *b), w)?;
        }
        (Ty::Dialect(a), Ty::Dialect(b)) => {
            s.last = w.text(a.namespace.as_bytes(), b.namespace.as_bytes())?
                && w.text(a.name.as_bytes(), b.name.as_bytes())?
                && a.version == b.version;
        }
        (Ty::Handle(a), Ty::Handle(b)) => {
            s.last = w.text(a.name.as_bytes(), b.name.as_bytes())?
                && w.text(a.runtime.as_bytes(), b.runtime.as_bytes())?;
        }
        (Ty::FatPtr(a), Ty::FatPtr(b)) => match (a, b) {
            (FatPtrKind::Slice(a), FatPtrKind::Slice(b)) => s.push(Task::Id(*a, *b), w)?,
            (FatPtrKind::Str, FatPtrKind::Str)
            | (FatPtrKind::ContainerLen, FatPtrKind::ContainerLen)
            | (FatPtrKind::ContainerVtable, FatPtrKind::ContainerVtable) => (),
            (FatPtrKind::TraitObject { trait_id: a }, FatPtrKind::TraitObject { trait_id: b }) => {
                s.last = a == b
            }
            _ => s.last = false,
        },
        _ => s.last = scalar(a),
    }
    Ok(())
}
fn scalar(ty: &Ty) -> bool {
    match ty {
        Ty::Storage(_) => false,
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
        | Ty::F16
        | Ty::F32
        | Ty::F64
        | Ty::Bool
        | Ty::Ptr
        | Ty::Unit
        | Ty::Never => true,
        Ty::Error => false,
        Ty::Ext(extension) => extension.unreachable(),
        Ty::Vector(..)
        | Ty::Tensor(..)
        | Ty::Ref(..)
        | Ty::RefMut(..)
        | Ty::PtrConst(..)
        | Ty::PtrMut(..)
        | Ty::Rc(..)
        | Ty::Array(..)
        | Ty::Set(..)
        | Ty::Sequence(..)
        | Ty::Tuple(..)
        | Ty::Struct(..)
        | Ty::Enum(..)
        | Ty::Record(..)
        | Ty::Closure(..)
        | Ty::Func(..)
        | Ty::Refine(..)
        | Ty::Dialect(..)
        | Ty::Handle(..)
        | Ty::FatPtr(..) => false,
    }
}
pub(super) fn tail<'a, O: ExecutionObserver>(
    s: &mut State<'a>,
    a: &'a [Ty],
    b: &'a [Ty],
    w: &mut Work<'_, '_, O>,
) -> R {
    w.admit(1, 2 * size_of::<Option<(&Ty, &[Ty])>>())?;
    if a.len() != b.len() {
        s.last = false;
        return Ok(());
    }
    if let (Some((a, rest_a)), Some((b, rest_b))) = (a.split_first(), b.split_first()) {
        s.push(Task::Types(rest_a, rest_b), w)?;
        s.push(Task::Ty(a, b), w)?;
    }
    Ok(())
}
