// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The LEVEL of a carrier (amendment S, `docs/SPEC_RATIFICATIONS.md` §1).
//!
//! The type-bearing carriers — [`crate::TyG`], [`crate::ConstantG`],
//! [`crate::InstG`], [`crate::InstrNodeG`], [`crate::BlockG`],
//! [`crate::FunctionG`], [`crate::FuncTyG`], [`crate::GlobalG`] and
//! [`crate::ModuleG`] — are generic over an EXTENSION type `X`, carried by
//! exactly one variant, `TyG::Ext(X)` / `ConstantG::Ext(X)`.
//!
//! * Level R (a module) is `X = `[`NoExt`]. `NoExt` has no value, so the
//!   extension variant is uninhabited and a parameterized level-R type is
//!   unrepresentable at compile time. `Ty`, `Constant`, `Inst`, `InstrNode`,
//!   `Block`, `Function`, `FuncTy`, `Global` and `Module` are aliases at
//!   `NoExt`, so every level-R API is unchanged and takes level R only.
//! * Level S (a template) instantiates the same carriers at its own
//!   extension; a template is never a module (amendment S, §22).

use crate::constant::{Constant, ConstantG};
use crate::inst::InstG;
use crate::node::InstrNodeG;
use crate::ty::{EnumDefG, EnumVariantG, FieldDefG, FuncTyG, StructDefG, Ty, TyG};
use crate::value::{FuncTyId, HoleId, ParamId, TyId};
use crate::{BlockG, FunctionG, GlobalG, ModuleG};

/// The extension a level-R carrier has: none. Uninhabited.
///
/// ```
/// fn absurd(x: &trust_ir::level::NoExt) -> ! {
///     x.unreachable()
/// }
/// assert_eq!(core::mem::size_of::<trust_ir::level::NoExt>(), 0);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NoExt {}

impl NoExt {
    /// A level-R value never reaches the extension arm: this is that arm.
    pub fn unreachable(&self) -> ! {
        match *self {}
    }
}

/// The extension a level-S (template) position carries: a reference into the
/// template's own parameter or hole table (amendment S, §1.2). Spelled `$n`
/// (a parameter) or `?n` (a hole) in text.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TemplateRef {
    /// A type or const parameter, `TemplateHeader::params[p]`.
    Param(ParamId),
    /// A hole the host answers at instantiation, `TemplateHeader::holes[h]`.
    Hole(HoleId),
}

impl core::fmt::Display for TemplateRef {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TemplateRef::Param(p) => write!(f, "${}", p.index()),
            TemplateRef::Hole(h) => write!(f, "?{}", h.index()),
        }
    }
}

mod sealed {
    pub trait Sealed {}
    impl Sealed for super::NoExt {}
    impl Sealed for super::TemplateRef {}
}

/// The extension types a carrier may be instantiated at: exactly [`NoExt`]
/// (level R) and [`TemplateRef`] (level S). Sealed: a new level is a format
/// amendment, never a downstream impl.
pub trait Extension:
    sealed::Sealed + Clone + core::fmt::Debug + PartialEq + Eq + core::hash::Hash
{
    /// The text spelling of an extension value (`$n` / `?n`).
    fn fmt_ext(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result;
}

impl Extension for NoExt {
    fn fmt_ext(&self, _: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.unreachable()
    }
}

impl Extension for TemplateRef {
    fn fmt_ext(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Display::fmt(self, f)
    }
}

/// The type half of a level map ([`InstG::try_map_level`] and the carriers
/// above it): one type at level `X` to level `Y`, or the caller's refusal.
pub type TyMap<'f, X, Y, E> = dyn FnMut(&TyG<X>) -> Result<TyG<Y>, E> + 'f;

/// The constant half of a level map: one ROOT constant at level `X`, with
/// the type it is spelled at, to level `Y`, or the caller's refusal.
pub type ConstMap<'f, X, Y, E> = dyn FnMut(&ConstantG<X>, &TyG<X>) -> Result<ConstantG<Y>, E> + 'f;

// ---------------------------------------------------------------------------
// Level maps: rebuild a carrier at another extension. Substitution (amendment
// S, `instantiate`) is these maps at `TemplateRef -> NoExt`; a level-R value
// embeds into level S through them at `NoExt -> TemplateRef`. Each is
// exhaustive over its carrier, so a new variant or field is a compile error
// here rather than a silently unmapped type.
// ---------------------------------------------------------------------------

impl<X> TyG<X> {
    /// Rebuild this type at another level: every `Ext(x)` becomes `ext(x)`,
    /// everything else is kept (a `TyId` / `FuncTyId` / table id is an index
    /// the caller's tables give meaning to, and is copied unchanged).
    pub fn try_map_ext<Y, E>(
        &self,
        ext: &mut dyn FnMut(&X) -> Result<TyG<Y>, E>,
    ) -> Result<TyG<Y>, E> {
        Ok(match self {
            TyG::Storage(layout) => TyG::Storage(*layout),
            TyG::I8 => TyG::I8,
            TyG::I16 => TyG::I16,
            TyG::I32 => TyG::I32,
            TyG::I64 => TyG::I64,
            TyG::I128 => TyG::I128,
            TyG::U8 => TyG::U8,
            TyG::U16 => TyG::U16,
            TyG::U32 => TyG::U32,
            TyG::U64 => TyG::U64,
            TyG::U128 => TyG::U128,
            TyG::Isize => TyG::Isize,
            TyG::Usize => TyG::Usize,
            TyG::Char => TyG::Char,
            TyG::Error => TyG::Error,
            TyG::F16 => TyG::F16,
            TyG::F32 => TyG::F32,
            TyG::F64 => TyG::F64,
            TyG::Bool => TyG::Bool,
            TyG::Vector(elem, lanes) => TyG::Vector(Box::new(elem.try_map_ext(ext)?), *lanes),
            TyG::Ptr => TyG::Ptr,
            TyG::FatPtr(kind) => TyG::FatPtr(*kind),
            TyG::Unit => TyG::Unit,
            TyG::Never => TyG::Never,
            TyG::Struct(id) => TyG::Struct(*id),
            TyG::Array(elem, len) => TyG::Array(*elem, *len),
            TyG::Tuple(elems) => TyG::Tuple(
                elems
                    .iter()
                    .map(|elem| elem.try_map_ext(ext))
                    .collect::<Result<_, _>>()?,
            ),
            TyG::Enum(id) => TyG::Enum(*id),
            TyG::Func(id) => TyG::Func(*id),
            TyG::Ref(inner) => TyG::Ref(Box::new(inner.try_map_ext(ext)?)),
            TyG::RefMut(inner) => TyG::RefMut(Box::new(inner.try_map_ext(ext)?)),
            TyG::PtrConst(inner) => TyG::PtrConst(Box::new(inner.try_map_ext(ext)?)),
            TyG::PtrMut(inner) => TyG::PtrMut(Box::new(inner.try_map_ext(ext)?)),
            TyG::Rc(inner) => TyG::Rc(Box::new(inner.try_map_ext(ext)?)),
            TyG::Set(elem, repr) => TyG::Set(*elem, *repr),
            TyG::Sequence(elem) => TyG::Sequence(*elem),
            TyG::Record(id) => TyG::Record(*id),
            TyG::Closure(id) => TyG::Closure(*id),
            TyG::Refine(base, pred) => TyG::Refine(*base, *pred),
            TyG::Dialect(ty) => TyG::Dialect(ty.clone()),
            TyG::Handle(ty) => TyG::Handle(ty.clone()),
            TyG::Ext(x) => ext(x)?,
            TyG::Tensor(elem, rank) => TyG::Tensor(Box::new(elem.try_map_ext(ext)?), *rank),
        })
    }

    /// The extension values this type spells DIRECTLY (not through a `TyId`
    /// or `FuncTyId` row), in preorder.
    pub fn for_each_ext(&self, f: &mut dyn FnMut(&X)) {
        match self {
            TyG::Storage(_) => {}
            TyG::Vector(inner, _)
            | TyG::Tensor(inner, _)
            | TyG::Ref(inner)
            | TyG::RefMut(inner)
            | TyG::PtrConst(inner)
            | TyG::PtrMut(inner)
            | TyG::Rc(inner) => inner.for_each_ext(f),
            TyG::Tuple(elems) => elems.iter().for_each(|elem| elem.for_each_ext(f)),
            TyG::Ext(x) => f(x),
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
        }
    }

    /// The table rows this type names DIRECTLY: `TyId`s (`Array`, `Set`,
    /// `Sequence`, `Refine`) and `FuncTyId`s (`Func`), in preorder.
    pub fn for_each_row(
        &self,
        ty_row: &mut dyn FnMut(TyId),
        func_ty_row: &mut dyn FnMut(FuncTyId),
    ) {
        match self {
            TyG::Storage(_) => {}
            TyG::Vector(inner, _)
            | TyG::Tensor(inner, _)
            | TyG::Ref(inner)
            | TyG::RefMut(inner)
            | TyG::PtrConst(inner)
            | TyG::PtrMut(inner)
            | TyG::Rc(inner) => inner.for_each_row(ty_row, func_ty_row),
            TyG::Tuple(elems) => elems
                .iter()
                .for_each(|elem| elem.for_each_row(ty_row, func_ty_row)),
            TyG::Array(elem, _)
            | TyG::Set(elem, _)
            | TyG::Sequence(elem)
            | TyG::Refine(elem, _) => {
                ty_row(*elem);
            }
            TyG::Func(id) => func_ty_row(*id),
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
            | TyG::Enum(_)
            | TyG::Record(_)
            | TyG::Closure(_)
            | TyG::Dialect(_)
            | TyG::Handle(_)
            | TyG::Ext(_) => {}
        }
    }

    /// The extension value at the HEAD of this type, if it is one.
    pub fn head_ext(&self) -> Option<&X> {
        match self {
            TyG::Ext(x) => Some(x),
            _ => None,
        }
    }
}

impl Ty {
    /// This level-R type at any level (it spells no extension).
    pub fn embed<Y>(&self) -> TyG<Y> {
        match self.try_map_ext::<Y, core::convert::Infallible>(&mut |e| e.unreachable()) {
            Ok(ty) => ty,
            Err(never) => match never {},
        }
    }
}

impl<X> ConstantG<X> {
    /// Rebuild this constant at another level. Only the ROOT can be an
    /// extension (every child is a level-R [`Constant`]), so the children are
    /// copied unchanged.
    pub fn try_map_ext<Y, E>(
        &self,
        ext: &mut dyn FnMut(&X) -> Result<ConstantG<Y>, E>,
    ) -> Result<ConstantG<Y>, E> {
        Ok(match self {
            ConstantG::Int(v) => ConstantG::Int(*v),
            ConstantG::U128(v) => ConstantG::U128(*v),
            ConstantG::Bytes { data, utf8 } => ConstantG::Bytes {
                data: data.clone(),
                utf8: *utf8,
            },
            ConstantG::Float(v) => ConstantG::Float(*v),
            ConstantG::Bool(v) => ConstantG::Bool(*v),
            ConstantG::Aggregate(v) => ConstantG::Aggregate(v.clone()),
            ConstantG::Array(v) => ConstantG::Array(v.clone()),
            ConstantG::Splat { elem, len } => ConstantG::Splat {
                elem: elem.clone(),
                len: *len,
            },
            ConstantG::Vector(v) => ConstantG::Vector(v.clone()),
            ConstantG::Sequence(v) => ConstantG::Sequence(v.clone()),
            ConstantG::Set(v) => ConstantG::Set(v.clone()),
            ConstantG::Record(v) => ConstantG::Record(v.clone()),
            ConstantG::Closure { func, captures } => ConstantG::Closure {
                func: *func,
                captures: captures.clone(),
            },
            ConstantG::FnDef(func) => ConstantG::FnDef(*func),
            ConstantG::SymbolAddr { symbol, addend } => ConstantG::SymbolAddr {
                symbol: symbol.clone(),
                addend: *addend,
            },
            ConstantG::PhantomData => ConstantG::PhantomData,
            ConstantG::Uninit => ConstantG::Uninit,
            ConstantG::TensorBlob { digest, dims } => ConstantG::TensorBlob {
                digest: *digest,
                dims: dims.clone(),
            },
            ConstantG::Ext(x) => ext(x)?,
        })
    }
}

impl Constant {
    /// This level-R constant at any level (it spells no extension).
    pub fn embed<Y>(&self) -> ConstantG<Y> {
        match self.try_map_ext::<Y, core::convert::Infallible>(&mut |e| e.unreachable()) {
            Ok(c) => c,
            Err(never) => match never {},
        }
    }
}

impl<X> FuncTyG<X> {
    /// Rebuild this signature at another level.
    pub fn try_map_level<Y, E>(&self, ty: &mut TyMap<'_, X, Y, E>) -> Result<FuncTyG<Y>, E> {
        Ok(FuncTyG {
            params: self.params.iter().map(&mut *ty).collect::<Result<_, _>>()?,
            returns: self
                .returns
                .iter()
                .map(&mut *ty)
                .collect::<Result<_, _>>()?,
            is_vararg: self.is_vararg,
            abi: self.abi.clone(),
        })
    }
}

impl<X> FieldDefG<X> {
    /// Rebuild a nominal field through the same total type map as instructions.
    pub fn try_map_level<Y, E>(&self, ty: &mut TyMap<'_, X, Y, E>) -> Result<FieldDefG<Y>, E> {
        let Self {
            name,
            ty: field_ty,
            offset,
        } = self;
        Ok(FieldDefG {
            name: name.clone(),
            ty: ty(field_ty)?,
            offset: *offset,
        })
    }
}

impl<X> StructDefG<X> {
    /// Map every field, preserving identity and the exact retained layout facts.
    /// This is data conversion, never a layout or source-refinement judgement.
    pub fn try_map_level<Y, E>(&self, ty: &mut TyMap<'_, X, Y, E>) -> Result<StructDefG<Y>, E> {
        let Self {
            id,
            name,
            fields,
            size,
            align,
            repr,
            origin,
        } = self;
        Ok(StructDefG {
            id: *id,
            name: name.clone(),
            fields: fields
                .iter()
                .map(|field| field.try_map_level(ty))
                .collect::<Result<_, _>>()?,
            size: *size,
            align: *align,
            repr: *repr,
            origin: origin.clone(),
        })
    }
}

impl<X> EnumVariantG<X> {
    /// Map every variant payload field and retain source field names verbatim.
    pub fn try_map_level<Y, E>(&self, ty: &mut TyMap<'_, X, Y, E>) -> Result<EnumVariantG<Y>, E> {
        let Self {
            name,
            fields,
            field_names,
        } = self;
        Ok(EnumVariantG {
            name: name.clone(),
            fields: fields.iter().map(&mut *ty).collect::<Result<_, _>>()?,
            field_names: field_names.clone(),
        })
    }
}

impl<X> EnumDefG<X> {
    /// Map every variant through the shared level map. No tag width, layout or
    /// nominal origin is synthesized, discarded or reinterpreted.
    pub fn try_map_level<Y, E>(&self, ty: &mut TyMap<'_, X, Y, E>) -> Result<EnumDefG<Y>, E> {
        let Self {
            id,
            name,
            variants,
            discriminants,
            repr,
            layout,
            origin,
        } = self;
        Ok(EnumDefG {
            id: *id,
            name: name.clone(),
            variants: variants
                .iter()
                .map(|variant| variant.try_map_level(ty))
                .collect::<Result<_, _>>()?,
            discriminants: discriminants.clone(),
            repr: *repr,
            layout: layout.clone(),
            origin: origin.clone(),
        })
    }
}

impl<X> crate::inst::TensorMapNode<X> {
    /// Rebuild this map-body node at another level, mapping each type it
    /// spells with `map_ty` (PKG-U13c). Exhaustive, as
    /// [`InstG::try_map_level`] is.
    pub fn try_map_level<Y, E>(
        &self,
        map_ty: &mut TyMap<'_, X, Y, E>,
    ) -> Result<crate::inst::TensorMapNode<Y>, E> {
        use crate::inst::TensorMapNode as N;
        Ok(match self {
            N::BinOp { op, ty, lhs, rhs } => N::BinOp {
                op: *op,
                ty: map_ty(ty)?,
                lhs: *lhs,
                rhs: *rhs,
            },
            N::UnOp { op, ty, operand } => N::UnOp {
                op: *op,
                ty: map_ty(ty)?,
                operand: *operand,
            },
            N::ICmp { op, ty, lhs, rhs } => N::ICmp {
                op: *op,
                ty: map_ty(ty)?,
                lhs: *lhs,
                rhs: *rhs,
            },
            N::Select {
                ty,
                cond,
                then_lane,
                else_lane,
            } => N::Select {
                ty: map_ty(ty)?,
                cond: *cond,
                then_lane: *then_lane,
                else_lane: *else_lane,
            },
            N::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => N::Cast {
                op: *op,
                src_ty: map_ty(src_ty)?,
                dst_ty: map_ty(dst_ty)?,
                operand: *operand,
            },
        })
    }
}

impl<X> InstG<X> {
    /// Rebuild this instruction at another level, mapping every type field
    /// with `map_ty` and the root constant of a `Const` with `map_const`
    /// (amendment S: substitution is this map). Exhaustive: a new variant
    /// is a compile error here, never a silently unmapped type.
    #[allow(clippy::clone_on_copy)]
    pub fn try_map_level<Y, E>(
        &self,
        map_ty: &mut TyMap<'_, X, Y, E>,
        map_const: &mut ConstMap<'_, X, Y, E>,
    ) -> Result<InstG<Y>, E> {
        Ok(match self {
            InstG::BinOp { op, ty, lhs, rhs } => InstG::BinOp {
                op: op.clone(),
                ty: map_ty(ty)?,
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            },
            InstG::UnOp { op, ty, operand } => InstG::UnOp {
                op: op.clone(),
                ty: map_ty(ty)?,
                operand: operand.clone(),
            },
            InstG::Overflow { op, ty, lhs, rhs } => InstG::Overflow {
                op: op.clone(),
                ty: map_ty(ty)?,
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            },
            InstG::ICmp { op, ty, lhs, rhs } => InstG::ICmp {
                op: op.clone(),
                ty: map_ty(ty)?,
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            },
            InstG::FCmp { op, ty, lhs, rhs } => InstG::FCmp {
                op: op.clone(),
                ty: map_ty(ty)?,
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            },
            InstG::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => InstG::Cast {
                op: op.clone(),
                src_ty: map_ty(src_ty)?,
                dst_ty: map_ty(dst_ty)?,
                operand: operand.clone(),
            },
            InstG::Load {
                ty,
                ptr,
                volatile,
                align,
            } => InstG::Load {
                ty: map_ty(ty)?,
                ptr: ptr.clone(),
                volatile: volatile.clone(),
                align: align.clone(),
            },
            InstG::Store {
                ty,
                ptr,
                value,
                volatile,
                align,
            } => InstG::Store {
                ty: map_ty(ty)?,
                ptr: ptr.clone(),
                value: value.clone(),
                volatile: volatile.clone(),
                align: align.clone(),
            },
            InstG::Alloca { ty, count, align } => InstG::Alloca {
                ty: map_ty(ty)?,
                count: count.clone(),
                align: align.clone(),
            },
            InstG::Drop { ty, ptr } => InstG::Drop {
                ty: map_ty(ty)?,
                ptr: ptr.clone(),
            },
            InstG::HeapAlloc {
                ty,
                count,
                align,
                origin,
            } => InstG::HeapAlloc {
                ty: map_ty(ty)?,
                count: count.clone(),
                align: align.clone(),
                origin: origin.clone(),
            },
            InstG::GEP {
                pointee_ty,
                base,
                indices,
                inbounds,
            } => InstG::GEP {
                pointee_ty: map_ty(pointee_ty)?,
                base: base.clone(),
                indices: indices.clone(),
                inbounds: inbounds.clone(),
            },
            InstG::PtrData { ptr_ty, ptr } => InstG::PtrData {
                ptr_ty: map_ty(ptr_ty)?,
                ptr: ptr.clone(),
            },
            InstG::PtrMetadata {
                ptr_ty,
                metadata_ty,
                ptr,
            } => InstG::PtrMetadata {
                ptr_ty: map_ty(ptr_ty)?,
                metadata_ty: map_ty(metadata_ty)?,
                ptr: ptr.clone(),
            },
            InstG::PtrFromParts {
                ptr_ty,
                metadata_ty,
                data,
                metadata,
            } => InstG::PtrFromParts {
                ptr_ty: map_ty(ptr_ty)?,
                metadata_ty: map_ty(metadata_ty)?,
                data: data.clone(),
                metadata: metadata.clone(),
            },
            InstG::AtomicLoad { ty, ptr, ordering } => InstG::AtomicLoad {
                ty: map_ty(ty)?,
                ptr: ptr.clone(),
                ordering: ordering.clone(),
            },
            InstG::AtomicStore {
                ty,
                ptr,
                value,
                ordering,
            } => InstG::AtomicStore {
                ty: map_ty(ty)?,
                ptr: ptr.clone(),
                value: value.clone(),
                ordering: ordering.clone(),
            },
            InstG::AtomicRMW {
                op,
                ty,
                ptr,
                value,
                ordering,
            } => InstG::AtomicRMW {
                op: op.clone(),
                ty: map_ty(ty)?,
                ptr: ptr.clone(),
                value: value.clone(),
                ordering: ordering.clone(),
            },
            InstG::CmpXchg {
                ty,
                ptr,
                expected,
                desired,
                success,
                failure,
                weak,
            } => InstG::CmpXchg {
                ty: map_ty(ty)?,
                ptr: ptr.clone(),
                expected: expected.clone(),
                desired: desired.clone(),
                success: success.clone(),
                failure: failure.clone(),
                weak: weak.clone(),
            },
            InstG::Fence { ordering } => InstG::Fence {
                ordering: ordering.clone(),
            },
            InstG::Br { target, args } => InstG::Br {
                target: target.clone(),
                args: args.clone(),
            },
            InstG::CondBr {
                cond,
                then_target,
                then_args,
                else_target,
                else_args,
            } => InstG::CondBr {
                cond: cond.clone(),
                then_target: then_target.clone(),
                then_args: then_args.clone(),
                else_target: else_target.clone(),
                else_args: else_args.clone(),
            },
            InstG::Switch {
                value,
                default,
                default_args,
                cases,
                exhaustive_enum_unreachable,
            } => InstG::Switch {
                value: value.clone(),
                default: default.clone(),
                default_args: default_args.clone(),
                cases: cases.clone(),
                exhaustive_enum_unreachable: exhaustive_enum_unreachable.clone(),
            },
            InstG::Call { callee, args } => InstG::Call {
                callee: callee.clone(),
                args: args.clone(),
            },
            InstG::CallIndirect {
                callee,
                sig,
                args,
                calling_conv,
            } => InstG::CallIndirect {
                callee: callee.clone(),
                sig: sig.clone(),
                args: args.clone(),
                calling_conv: calling_conv.clone(),
            },
            InstG::Return { values } => InstG::Return {
                values: values.clone(),
            },
            InstG::ExtractField {
                ty,
                aggregate,
                field,
            } => InstG::ExtractField {
                ty: map_ty(ty)?,
                aggregate: aggregate.clone(),
                field: field.clone(),
            },
            InstG::InsertField {
                ty,
                aggregate,
                field,
                value,
            } => InstG::InsertField {
                ty: map_ty(ty)?,
                aggregate: aggregate.clone(),
                field: field.clone(),
                value: value.clone(),
            },
            InstG::ExtractElement { ty, array, index } => InstG::ExtractElement {
                ty: map_ty(ty)?,
                array: array.clone(),
                index: index.clone(),
            },
            InstG::InsertElement {
                ty,
                array,
                index,
                value,
            } => InstG::InsertElement {
                ty: map_ty(ty)?,
                array: array.clone(),
                index: index.clone(),
                value: value.clone(),
            },
            InstG::Const { ty: t, value } => InstG::Const {
                value: map_const(value, t)?,
                ty: map_ty(t)?,
            },
            InstG::NullPtr => InstG::NullPtr,
            InstG::GlobalAddr { global } => InstG::GlobalAddr {
                global: global.clone(),
            },
            InstG::Undef { ty } => InstG::Undef { ty: map_ty(ty)? },
            InstG::Assume { cond } => InstG::Assume { cond: cond.clone() },
            InstG::Assert { cond, kind, site } => InstG::Assert {
                cond: cond.clone(),
                kind: kind.clone(),
                site: site.clone(),
            },
            InstG::Unreachable => InstG::Unreachable,
            InstG::Copy { ty, operand } => InstG::Copy {
                ty: map_ty(ty)?,
                operand: operand.clone(),
            },
            InstG::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => InstG::Select {
                ty: map_ty(ty)?,
                cond: cond.clone(),
                then_val: then_val.clone(),
                else_val: else_val.clone(),
            },
            InstG::SeqMapAddK { ty, seq, k } => InstG::SeqMapAddK {
                ty: map_ty(ty)?,
                seq: seq.clone(),
                k: k.clone(),
            },
            InstG::SeqMapNot { ty, seq } => InstG::SeqMapNot {
                ty: map_ty(ty)?,
                seq: seq.clone(),
            },
            InstG::SeqMap { ty, seq, fwd } => InstG::SeqMap {
                ty: map_ty(ty)?,
                seq: seq.clone(),
                fwd: fwd.clone(),
            },
            InstG::Borrow { ptr } => InstG::Borrow { ptr: ptr.clone() },
            InstG::BorrowMut { ptr } => InstG::BorrowMut { ptr: ptr.clone() },
            InstG::EndBorrow { borrow_ptr } => InstG::EndBorrow {
                borrow_ptr: borrow_ptr.clone(),
            },
            InstG::Retain { ptr } => InstG::Retain { ptr: ptr.clone() },
            InstG::Release { ptr } => InstG::Release { ptr: ptr.clone() },
            InstG::IsUnique { ptr } => InstG::IsUnique { ptr: ptr.clone() },
            InstG::Dealloc { ptr } => InstG::Dealloc { ptr: ptr.clone() },
            InstG::MemCopy {
                dst,
                src,
                bytes,
                overlap,
            } => InstG::MemCopy {
                dst: dst.clone(),
                src: src.clone(),
                bytes: bytes.clone(),
                overlap: overlap.clone(),
            },
            InstG::MemSet { dst, byte, bytes } => InstG::MemSet {
                dst: dst.clone(),
                byte: byte.clone(),
                bytes: bytes.clone(),
            },
            InstG::OpenFrame { def } => InstG::OpenFrame { def: def.clone() },
            InstG::BindSlot { frame, slot, value } => InstG::BindSlot {
                frame: frame.clone(),
                slot: slot.clone(),
                value: value.clone(),
            },
            InstG::LoadSlot { frame, slot, ty } => InstG::LoadSlot {
                frame: frame.clone(),
                slot: slot.clone(),
                ty: map_ty(ty)?,
            },
            InstG::CloseFrame { frame } => InstG::CloseFrame {
                frame: frame.clone(),
            },
            InstG::CoroSuspend {
                frame,
                state_slot,
                next_state,
                value,
            } => InstG::CoroSuspend {
                frame: frame.clone(),
                state_slot: state_slot.clone(),
                next_state: next_state.clone(),
                value: value.clone(),
            },
            InstG::Invoke {
                callee,
                args,
                normal_dest,
                normal_args,
                unwind_dest,
            } => InstG::Invoke {
                callee: callee.clone(),
                args: args.clone(),
                normal_dest: normal_dest.clone(),
                normal_args: normal_args.clone(),
                unwind_dest: unwind_dest.clone(),
            },
            InstG::LandingPad {
                is_cleanup,
                catch_type_indices,
            } => InstG::LandingPad {
                is_cleanup: is_cleanup.clone(),
                catch_type_indices: catch_type_indices.clone(),
            },
            InstG::Resume { exn } => InstG::Resume { exn: exn.clone() },
            InstG::AssertInvoke {
                cond,
                kind,
                site,
                normal_dest,
                normal_args,
                unwind_dest,
            } => InstG::AssertInvoke {
                cond: cond.clone(),
                kind: kind.clone(),
                site: site.clone(),
                normal_dest: normal_dest.clone(),
                normal_args: normal_args.clone(),
                unwind_dest: unwind_dest.clone(),
            },
            InstG::DialectOp(payload) => InstG::DialectOp(payload.clone()),
            InstG::MakeAggregate {
                ty,
                variant,
                fields,
            } => InstG::MakeAggregate {
                ty: map_ty(ty)?,
                variant: variant.clone(),
                fields: fields.clone(),
            },
            InstG::MakeClosure { ty, func, captures } => InstG::MakeClosure {
                ty: *ty,
                func: *func,
                captures: captures.clone(),
            },
            InstG::ArraySplat { ty, value } => InstG::ArraySplat {
                ty: map_ty(ty)?,
                value: value.clone(),
            },
            InstG::TensorContract {
                ty,
                lhs,
                rhs,
                batch,
                contract,
            } => InstG::TensorContract {
                ty: map_ty(ty)?,
                lhs: lhs.clone(),
                rhs: rhs.clone(),
                batch: batch.clone(),
                contract: contract.clone(),
            },
            InstG::TensorMap { ty, args, body } => InstG::TensorMap {
                ty: map_ty(ty)?,
                args: args.clone(),
                body: body
                    .iter()
                    .map(|node| node.try_map_level(map_ty))
                    .collect::<Result<_, _>>()?,
            },
            InstG::TensorReduce {
                ty,
                src,
                op,
                axes,
                order,
            } => InstG::TensorReduce {
                ty: map_ty(ty)?,
                src: src.clone(),
                op: *op,
                axes: axes.clone(),
                order: *order,
            },
            InstG::TensorView {
                ty,
                src,
                params,
                exprs,
                shape,
                index,
                fill,
            } => InstG::TensorView {
                ty: map_ty(ty)?,
                src: src.clone(),
                params: params.clone(),
                exprs: exprs.clone(),
                shape: shape.clone(),
                index: index.clone(),
                fill: fill.clone(),
            },
            InstG::TensorGather { ty, data, coords } => InstG::TensorGather {
                ty: map_ty(ty)?,
                data: data.clone(),
                coords: coords.clone(),
            },
            InstG::TensorScatter {
                ty,
                init,
                src,
                coords,
            } => InstG::TensorScatter {
                ty: map_ty(ty)?,
                init: init.clone(),
                src: src.clone(),
                coords: coords.clone(),
            },
            InstG::CallCannotUnwind { callee, args } => InstG::CallCannotUnwind {
                callee: callee.clone(),
                args: args.clone(),
            },
            InstG::CallIndirectCannotUnwind {
                callee,
                sig,
                args,
                calling_conv,
            } => InstG::CallIndirectCannotUnwind {
                callee: callee.clone(),
                sig: sig.clone(),
                args: args.clone(),
                calling_conv: calling_conv.clone(),
            },
            InstG::DropInvoke {
                ty,
                ptr,
                normal_dest,
                normal_args,
                unwind_dest,
            } => InstG::DropInvoke {
                ty: map_ty(ty)?,
                ptr: ptr.clone(),
                normal_dest: normal_dest.clone(),
                normal_args: normal_args.clone(),
                unwind_dest: unwind_dest.clone(),
            },
            InstG::InvokeIndirect {
                callee,
                sig,
                args,
                calling_conv,
                normal_dest,
                normal_args,
                unwind_dest,
            } => InstG::InvokeIndirect {
                callee: callee.clone(),
                sig: sig.clone(),
                args: args.clone(),
                calling_conv: calling_conv.clone(),
                normal_dest: normal_dest.clone(),
                normal_args: normal_args.clone(),
                unwind_dest: unwind_dest.clone(),
            },
        })
    }

    /// Visit every type field of this instruction, in field order.
    /// Exhaustive, like [`InstG::try_map_level`].
    pub fn for_each_ty<'a>(&'a self, mut f: impl FnMut(&'a TyG<X>)) {
        match self {
            InstG::BinOp { ty, .. } => {
                f(ty);
            }
            InstG::UnOp { ty, .. } => {
                f(ty);
            }
            InstG::Overflow { ty, .. } => {
                f(ty);
            }
            InstG::ICmp { ty, .. } => {
                f(ty);
            }
            InstG::FCmp { ty, .. } => {
                f(ty);
            }
            InstG::Cast { src_ty, dst_ty, .. } => {
                f(src_ty);
                f(dst_ty);
            }
            InstG::Load { ty, .. } => {
                f(ty);
            }
            InstG::Store { ty, .. } => {
                f(ty);
            }
            InstG::Alloca { ty, .. } => {
                f(ty);
            }
            InstG::Drop { ty, .. } => {
                f(ty);
            }
            InstG::HeapAlloc { ty, .. } => {
                f(ty);
            }
            InstG::GEP { pointee_ty, .. } => {
                f(pointee_ty);
            }
            InstG::PtrData { ptr_ty, .. } => {
                f(ptr_ty);
            }
            InstG::PtrMetadata {
                ptr_ty,
                metadata_ty,
                ..
            } => {
                f(ptr_ty);
                f(metadata_ty);
            }
            InstG::PtrFromParts {
                ptr_ty,
                metadata_ty,
                ..
            } => {
                f(ptr_ty);
                f(metadata_ty);
            }
            InstG::AtomicLoad { ty, .. } => {
                f(ty);
            }
            InstG::AtomicStore { ty, .. } => {
                f(ty);
            }
            InstG::AtomicRMW { ty, .. } => {
                f(ty);
            }
            InstG::CmpXchg { ty, .. } => {
                f(ty);
            }
            InstG::Fence { .. } => {}
            InstG::Br { .. } => {}
            InstG::CondBr { .. } => {}
            InstG::Switch { .. } => {}
            InstG::Call { .. } => {}
            InstG::CallIndirect { .. } => {}
            InstG::Return { .. } => {}
            InstG::ExtractField { ty, .. } => {
                f(ty);
            }
            InstG::InsertField { ty, .. } => {
                f(ty);
            }
            InstG::ExtractElement { ty, .. } => {
                f(ty);
            }
            InstG::InsertElement { ty, .. } => {
                f(ty);
            }
            InstG::Const { ty, .. } => {
                f(ty);
            }
            InstG::NullPtr => {}
            InstG::GlobalAddr { .. } => {}
            InstG::Undef { ty, .. } => {
                f(ty);
            }
            InstG::Assume { .. } => {}
            InstG::Assert { .. } => {}
            InstG::Unreachable => {}
            InstG::Copy { ty, .. } => {
                f(ty);
            }
            InstG::Select { ty, .. } => {
                f(ty);
            }
            InstG::SeqMapAddK { ty, .. } => {
                f(ty);
            }
            InstG::SeqMapNot { ty, .. } => {
                f(ty);
            }
            InstG::SeqMap { ty, .. } => {
                f(ty);
            }
            InstG::Borrow { .. } => {}
            InstG::BorrowMut { .. } => {}
            InstG::EndBorrow { .. } => {}
            InstG::Retain { .. } => {}
            InstG::Release { .. } => {}
            InstG::IsUnique { .. } => {}
            InstG::Dealloc { .. } => {}
            InstG::MemCopy { .. } => {}
            InstG::MemSet { .. } => {}
            InstG::OpenFrame { .. } => {}
            InstG::BindSlot { .. } => {}
            InstG::LoadSlot { ty, .. } => {
                f(ty);
            }
            InstG::CloseFrame { .. } => {}
            InstG::CoroSuspend { .. } => {}
            InstG::Invoke { .. } => {}
            InstG::LandingPad { .. } => {}
            InstG::Resume { .. } => {}
            InstG::AssertInvoke { .. } => {}
            InstG::DialectOp(_) => {}
            InstG::MakeAggregate { ty, .. } => {
                f(ty);
            }
            InstG::ArraySplat { ty, .. } => {
                f(ty);
            }
            InstG::MakeClosure { .. } => {}
            InstG::CallCannotUnwind { .. } => {}
            InstG::CallIndirectCannotUnwind { .. } => {}
            InstG::DropInvoke { ty, .. } => {
                f(ty);
            }
            InstG::InvokeIndirect { .. } => {}
            InstG::TensorContract { ty, .. }
            | InstG::TensorReduce { ty, .. }
            | InstG::TensorView { ty, .. }
            | InstG::TensorGather { ty, .. }
            | InstG::TensorScatter { ty, .. } => {
                f(ty);
            }
            InstG::TensorMap { ty, body, .. } => {
                f(ty);
                for node in body {
                    for node_ty in node.types() {
                        f(node_ty);
                    }
                }
            }
        }
    }
}

impl<X> InstrNodeG<X> {
    /// Rebuild this node at another level (its instruction mapped; results,
    /// proofs, span, proof context and scope copied).
    pub fn try_map_level<Y, E>(
        &self,
        ty: &mut TyMap<'_, X, Y, E>,
        constant: &mut ConstMap<'_, X, Y, E>,
    ) -> Result<InstrNodeG<Y>, E> {
        Ok(InstrNodeG {
            inst: self.inst.try_map_level(ty, constant)?,
            results: self.results.clone(),
            proofs: self.proofs.clone(),
            span: self.span,
            proof_context: self.proof_context.clone(),
            scope: self.scope,
        })
    }
}

impl<X> BlockG<X> {
    /// Rebuild this block at another level.
    pub fn try_map_level<Y, E>(
        &self,
        ty: &mut TyMap<'_, X, Y, E>,
        constant: &mut ConstMap<'_, X, Y, E>,
    ) -> Result<BlockG<Y>, E> {
        Ok(BlockG {
            id: self.id,
            params: self
                .params
                .iter()
                .map(|(value, param_ty)| Ok((*value, ty(param_ty)?)))
                .collect::<Result<_, E>>()?,
            body: self
                .body
                .iter()
                .map(|node| node.try_map_level(ty, constant))
                .collect::<Result<_, E>>()?,
        })
    }
}

impl<X> FunctionG<X> {
    /// Rebuild this function at another level (its blocks mapped; every other
    /// field copied).
    pub fn try_map_level<Y, E>(
        &self,
        ty: &mut TyMap<'_, X, Y, E>,
        constant: &mut ConstMap<'_, X, Y, E>,
    ) -> Result<FunctionG<Y>, E> {
        Ok(FunctionG {
            id: self.id,
            name: self.name.clone(),
            ty: self.ty,
            entry: self.entry,
            blocks: self
                .blocks
                .iter()
                .map(|block| block.try_map_level(ty, constant))
                .collect::<Result<_, E>>()?,
            proofs: self.proofs.clone(),
            calling_conv: self.calling_conv,
            linkage: self.linkage,
            attrs: self.attrs.clone(),
            summary: self.summary.clone(),
            producer: self.producer.clone(),
            value_names: self.value_names.clone(),
            scopes: self.scopes.clone(),
            source_provenance: self.source_provenance.clone(),
            body_gate: self.body_gate.clone(),
            display_path: self.display_path.clone(),
            section: self.section.clone(),
            visibility: self.visibility,
            retained: self.retained,
        })
    }
}

impl<X> GlobalG<X> {
    /// Rebuild this global at another level (its type mapped; its initializer
    /// is level R at every level).
    pub fn try_map_level<Y, E>(&self, ty: &mut TyMap<'_, X, Y, E>) -> Result<GlobalG<Y>, E> {
        Ok(GlobalG {
            name: self.name.clone(),
            ty: ty(&self.ty)?,
            mutable: self.mutable,
            initializer: self.initializer.clone(),
            linkage: self.linkage,
            tls: self.tls,
            align: self.align,
            section: self.section.clone(),
            visibility: self.visibility,
            retained: self.retained,
        })
    }
}

impl<X> ModuleG<X> {
    /// Rebuild this module at another level: its functions, globals,
    /// function types, type rows and nominal fields mapped. The other tables
    /// remain level R at every level and are copied.
    pub fn try_map_level<Y, E>(
        &self,
        ty: &mut TyMap<'_, X, Y, E>,
        constant: &mut ConstMap<'_, X, Y, E>,
    ) -> Result<ModuleG<Y>, E> {
        Ok(ModuleG {
            name: self.name.clone(),
            functions: self
                .functions
                .iter()
                .map(|function| function.try_map_level(ty, constant))
                .collect::<Result<_, E>>()?,
            structs: self
                .structs
                .iter()
                .map(|row| row.try_map_level(ty))
                .collect::<Result<_, E>>()?,
            enums: self
                .enums
                .iter()
                .map(|row| row.try_map_level(ty))
                .collect::<Result<_, E>>()?,
            records: self.records.clone(),
            closure_types: self.closure_types.clone(),
            globals: self
                .globals
                .iter()
                .map(|global| global.try_map_level(ty))
                .collect::<Result<_, E>>()?,
            func_types: self
                .func_types
                .iter()
                .map(|signature| signature.try_map_level(ty))
                .collect::<Result<_, E>>()?,
            types: self.types.iter().map(&mut *ty).collect::<Result<_, E>>()?,
            proof_obligations: self.proof_obligations.clone(),
            proof_certificates: self.proof_certificates.clone(),
            target_info: self.target_info.clone(),
            files: self.files.clone(),
            obligation_diagnostics: self.obligation_diagnostics.clone(),
            spec_modules: self.spec_modules.clone(),
            universes: self.universes.clone(),
            predicates: self.predicates.clone(),
            global_asm: self.global_asm.clone(),
            imports: self.imports.clone(),
            tuple_layouts: self.tuple_layouts.clone(),
            completeness: self.completeness.clone(),
            drop_glue: self.drop_glue.clone(),
            closure_layouts: self.closure_layouts.clone(),
            blobs: self.blobs.clone(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Commit A of amendment S: the level-R extension has no value, so it
    /// occupies nothing and no constructor exists (an empty `match` on it
    /// type-checks only because it is uninhabited).
    #[test]
    fn noext_is_uninhabited() {
        fn absurd(x: NoExt) -> ! {
            match x {}
        }
        let _: fn(NoExt) -> ! = absurd;
        assert_eq!(core::mem::size_of::<NoExt>(), 0);
        assert_eq!(
            core::mem::size_of::<crate::Ty>(),
            core::mem::size_of::<crate::Ty>()
        );
        // The declaration, spelled in two pieces so this test's own text is
        // not a second match.
        let source = include_str!("level.rs");
        let decl = ["pub enum NoExt", " {}"].concat();
        assert_eq!(
            source.matches(&decl).count(),
            1,
            "NoExt is declared with no variant"
        );
    }

    /// Nominal fields use the same map as every other typed carrier. Retained
    /// identity/layout metadata is data and survives unchanged, including ZST
    /// offsets and explicit enum discriminants.
    #[test]
    fn nominal_fields_share_the_total_level_map() {
        use crate::{
            EnumDefG, EnumId, EnumTagRepr, EnumVariantG, FieldDefG, StructDefG, StructId,
            StructRepr,
        };
        let mut source = ModuleG::<TemplateRef>::new("nominal-level-map");
        source.structs.push(StructDefG {
            id: StructId::new(0),
            name: "Packet".into(),
            fields: vec![FieldDefG {
                name: "value".into(),
                ty: TyG::Tuple(vec![
                    TyG::Ext(TemplateRef::Param(ParamId::new(0))),
                    TyG::Unit,
                ]),
                offset: Some(0),
            }],
            size: Some(8),
            align: Some(8),
            repr: StructRepr::C,
            origin: None,
        });
        source.enums.push(EnumDefG {
            id: EnumId::new(0),
            name: "Choice".into(),
            variants: vec![EnumVariantG {
                name: "Some".into(),
                fields: vec![TyG::Ext(TemplateRef::Hole(HoleId::new(1)))],
                field_names: vec!["value".into()],
            }],
            discriminants: vec![Some(7)],
            repr: Some(EnumTagRepr::U8),
            layout: None,
            origin: None,
        });
        let before = source.clone();
        let mapped = source
            .try_map_level(
                &mut |ty| {
                    ty.try_map_ext(&mut |r| match r {
                        TemplateRef::Param(p) if p.index() == 0 => Ok::<Ty, &str>(Ty::U64),
                        TemplateRef::Hole(h) if h.index() == 1 => Ok(Ty::U16),
                        _ => Err("unexpected extension"),
                    })
                },
                &mut |_, _| Err("no constant expected"),
            )
            .unwrap();
        assert_eq!(
            mapped.structs[0].fields[0].ty,
            Ty::Tuple(vec![Ty::U64, Ty::Unit])
        );
        assert_eq!(mapped.structs[0].fields[0].offset, Some(0));
        assert_eq!(
            (
                mapped.structs[0].size,
                mapped.structs[0].align,
                mapped.structs[0].repr
            ),
            (Some(8), Some(8), StructRepr::C)
        );
        assert_eq!(mapped.enums[0].variants[0].fields, vec![Ty::U16]);
        assert_eq!(mapped.enums[0].variants[0].field_names, vec!["value"]);
        assert_eq!(mapped.enums[0].discriminants, vec![Some(7)]);
        assert_eq!(mapped.enums[0].repr, Some(EnumTagRepr::U8));
        assert_eq!(source, before);
        let refused = source.try_map_level(
            &mut |ty| ty.try_map_ext(&mut |_| Err::<Ty, _>("refused nominal field")),
            &mut |_, _| Err("no constant expected"),
        );
        assert_eq!(refused.unwrap_err(), "refused nominal field");
        assert_eq!(source, before, "a failed map never edits source data");
    }

    /// A generic carrier supplies no permission to put generic fields in a
    /// ground table. Both direct extensions and extensions through type rows
    /// retain T5's refusal, including at the binary boundary.
    #[test]
    fn generic_nominal_fields_still_refuse_ground_table_admission() {
        use crate::template::{Template, TemplateError, TemplateHeader, TemplateParam};
        use crate::{EnumDefG, EnumId, EnumVariantG, FieldDefG, StructDefG, StructId, StructRepr};
        for is_enum in [false, true] {
            for through_row in [false, true] {
                let mut module = ModuleG::<TemplateRef>::new("generic-ground-refusal");
                let ext = TyG::Ext(TemplateRef::Param(ParamId::new(0)));
                let ty = if through_row {
                    module.types.push(ext.clone());
                    TyG::Array(TyId::new(0), 3)
                } else {
                    ext
                };
                if is_enum {
                    module.enums.push(EnumDefG::new(
                        EnumId::new(0),
                        "Choice",
                        vec![EnumVariantG {
                            name: "Some".into(),
                            fields: vec![ty],
                            field_names: vec![],
                        }],
                    ));
                } else {
                    module.structs.push(StructDefG {
                        id: StructId::new(0),
                        name: "Packet".into(),
                        fields: vec![FieldDefG {
                            name: "value".into(),
                            ty,
                            offset: None,
                        }],
                        size: None,
                        align: None,
                        repr: StructRepr::Rust,
                        origin: None,
                    });
                }
                let param = TyG::Ext(TemplateRef::Param(ParamId::new(0)));
                let signature = module
                    .add_func_type(crate::FuncTyG {
                        params: vec![param.clone()],
                        returns: vec![param.clone()],
                        is_vararg: false,
                        abi: None,
                    })
                    .unwrap();
                let mut body = crate::FunctionG::new(
                    crate::FuncId::new(0),
                    crate::template::TEMPLATE_BODY_NAME,
                    signature,
                    crate::BlockId::new(0),
                );
                let mut block = crate::BlockG::new(crate::BlockId::new(0))
                    .with_param(crate::ValueId::new(0), param);
                block
                    .body
                    .push(crate::InstrNodeG::new(crate::InstG::Return {
                        values: vec![crate::ValueId::new(0)],
                    }));
                body.blocks.push(block);
                module.functions.push(body);
                let template = Template {
                    header: TemplateHeader {
                        identity: "generic-ground-refusal".into(),
                        params: vec![TemplateParam::Type],
                        holes: vec![],
                    },
                    module,
                };
                let expected = if is_enum { "enum" } else { "struct" };
                assert!(
                    matches!(template.check_structure(), Err(TemplateError::ExtInGroundTable { table, index: 0 }) if table == expected)
                );
                assert!(
                    matches!(crate::binary::serialize_template(&template), Err(TemplateError::ExtInGroundTable { table, index: 0 }) if table == expected)
                );
            }
        }
    }
}
