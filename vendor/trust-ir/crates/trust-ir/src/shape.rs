// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Stable proof-grade shape classification for Rust bootstrap MIR imports.
//!
//! These enums deliberately classify IR by semantic shape rather than by
//! formatted strings. Downstream proof tooling can branch on them without
//! scraping `Display` output or depending on arena ids.

use crate::Module;
use crate::constant::Constant;
use crate::inst::CastOp;
use crate::ty::{EnumTagRepr, FatPtrKind, Ty};
use crate::value::{EnumId, StructId, TyId};

pub const DEFAULT_POINTER_BITS: u32 = 64;

/// Unsigned integer type used for a target pointer-sized metadata lane.
pub fn pointer_sized_unsigned_ty(pointer_bits: u32) -> Option<Ty> {
    match pointer_bits {
        8 => Some(Ty::U8),
        16 => Some(Ty::U16),
        32 => Some(Ty::U32),
        64 => Some(Ty::U64),
        128 => Some(Ty::U128),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TyShape {
    Int {
        signed: bool,
        bits: u32,
    },
    /// v25: pointer-width integer (Rust isize/usize) — width is the target's
    /// thin-pointer width, so a target-free shape cannot spell a bit count.
    PointerInt {
        signed: bool,
    },
    /// v25: the producer-internal error/bottom type (never wire-legal).
    Error,
    Float {
        bits: u32,
    },
    Bool,
    ThinPointer,
    FatPointer,
    Unit,
    Never,
    Struct,
    Array,
    Vector,
    Tuple,
    Enum,
    Function,
    Ref,
    RefMut,
    PtrConst,
    PtrMut,
    Rc,
    Set,
    Sequence,
    Record,
    Closure,
    /// A refinement type. **Representation-preserving**: the value's real
    /// shape is the base type's, but `Ty::shape()` has no module in hand to
    /// resolve the `TyId`, so it reports the refinement layer honestly rather
    /// than guessing. Resolve it with `Module::ty_layout_shape`, which does
    /// delegate to the base.
    Refine,
}

impl core::fmt::Display for TyShape {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TyShape::Int { signed, bits } => {
                if *signed {
                    write!(f, "i{bits}")
                } else {
                    write!(f, "u{bits}")
                }
            }
            TyShape::PointerInt { signed } => f.write_str(if *signed { "isize" } else { "usize" }),
            TyShape::Error => f.write_str("error"),
            TyShape::Float { bits } => write!(f, "f{bits}"),
            TyShape::Bool => f.write_str("bool"),
            TyShape::ThinPointer => f.write_str("thin_pointer"),
            TyShape::FatPointer => f.write_str("fat_pointer"),
            TyShape::Unit => f.write_str("unit"),
            TyShape::Never => f.write_str("never"),
            TyShape::Struct => f.write_str("struct"),
            TyShape::Array => f.write_str("array"),
            TyShape::Vector => f.write_str("vector"),
            TyShape::Tuple => f.write_str("tuple"),
            TyShape::Enum => f.write_str("enum"),
            TyShape::Function => f.write_str("function"),
            TyShape::Ref => f.write_str("ref"),
            TyShape::RefMut => f.write_str("ref_mut"),
            TyShape::PtrConst => f.write_str("ptr_const"),
            TyShape::PtrMut => f.write_str("ptr_mut"),
            TyShape::Rc => f.write_str("rc"),
            TyShape::Set => f.write_str("set"),
            TyShape::Sequence => f.write_str("sequence"),
            TyShape::Record => f.write_str("record"),
            TyShape::Closure => f.write_str("closure"),
            TyShape::Refine => f.write_str("refine"),
        }
    }
}

impl Ty {
    pub fn shape(&self) -> TyShape {
        match self {
            Ty::I8 => TyShape::Int {
                signed: true,
                bits: 8,
            },
            Ty::I16 => TyShape::Int {
                signed: true,
                bits: 16,
            },
            Ty::I32 => TyShape::Int {
                signed: true,
                bits: 32,
            },
            Ty::I64 => TyShape::Int {
                signed: true,
                bits: 64,
            },
            Ty::I128 => TyShape::Int {
                signed: true,
                bits: 128,
            },
            Ty::U8 => TyShape::Int {
                signed: false,
                bits: 8,
            },
            Ty::U16 => TyShape::Int {
                signed: false,
                bits: 16,
            },
            Ty::U32 => TyShape::Int {
                signed: false,
                bits: 32,
            },
            Ty::U64 => TyShape::Int {
                signed: false,
                bits: 64,
            },
            Ty::U128 => TyShape::Int {
                signed: false,
                bits: 128,
            },
            // v25 B1 scalars.
            Ty::Isize => TyShape::PointerInt { signed: true },
            Ty::Usize => TyShape::PointerInt { signed: false },
            Ty::Char => TyShape::Int {
                signed: false,
                bits: 32,
            },
            Ty::Error => TyShape::Error,
            Ty::F16 => TyShape::Float { bits: 16 },
            Ty::F32 => TyShape::Float { bits: 32 },
            Ty::F64 => TyShape::Float { bits: 64 },
            Ty::Bool => TyShape::Bool,
            Ty::Ptr => TyShape::ThinPointer,
            Ty::FatPtr(_) => TyShape::FatPointer,
            Ty::Unit => TyShape::Unit,
            Ty::Never => TyShape::Never,
            Ty::Struct(_) => TyShape::Struct,
            Ty::Array(_, _) => TyShape::Array,
            Ty::Vector(_, _) => TyShape::Vector,
            Ty::Tuple(_) => TyShape::Tuple,
            Ty::Enum(_) => TyShape::Enum,
            Ty::Func(_) => TyShape::Function,
            Ty::Ref(_) => TyShape::Ref,
            Ty::RefMut(_) => TyShape::RefMut,
            Ty::PtrConst(_) => TyShape::PtrConst,
            Ty::PtrMut(_) => TyShape::PtrMut,
            Ty::Rc(_) => TyShape::Rc,
            Ty::Set(_, _) => TyShape::Set,
            Ty::Sequence(_) => TyShape::Sequence,
            Ty::Record(_) => TyShape::Record,
            Ty::Closure(_) => TyShape::Closure,
            Ty::Refine(_, _) => TyShape::Refine,
        }
    }

    pub fn is_adt(&self) -> bool {
        matches!(self, Ty::Struct(_) | Ty::Enum(_))
    }

    pub fn is_fat_pointer(&self) -> bool {
        matches!(self, Ty::FatPtr(_))
    }

    pub fn is_thin_pointer_like(&self) -> bool {
        matches!(
            self,
            Ty::Ptr
                | Ty::Ref(_)
                | Ty::RefMut(_)
                | Ty::PtrConst(_)
                | Ty::PtrMut(_)
                | Ty::Rc(_)
                | Ty::Func(_)
        )
    }

    pub fn is_pointer_like(&self) -> bool {
        matches!(
            self,
            Ty::Ptr
                | Ty::Ref(_)
                | Ty::RefMut(_)
                | Ty::PtrConst(_)
                | Ty::PtrMut(_)
                | Ty::Rc(_)
                | Ty::Func(_)
                | Ty::FatPtr(_)
        )
    }

    pub fn pointer_layout_shape(&self, pointer_bits: u32) -> Option<PointerLayoutShape> {
        match self {
            Ty::Ptr
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Rc(_)
            | Ty::Func(_) => Some(PointerLayoutShape::thin(pointer_bits)),
            Ty::FatPtr(kind) => Some(PointerLayoutShape::fat(pointer_bits, kind.metadata_shape())),
            _ => None,
        }
    }

    pub fn pointer_metadata_ty(&self, pointer_bits: u32) -> Option<Ty> {
        match self {
            Ty::FatPtr(kind) => kind.metadata_ty(pointer_bits),
            ty if ty.is_thin_pointer_like() => Some(Ty::Unit),
            _ => None,
        }
    }

    pub fn default_pointer_layout_shape(&self) -> Option<PointerLayoutShape> {
        self.pointer_layout_shape(DEFAULT_POINTER_BITS)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PointerMetadataShape {
    SliceLen { elem: TyId },
    StrLen,
    VTable { trait_id: u32 },
}

impl core::fmt::Display for PointerMetadataShape {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            PointerMetadataShape::SliceLen { elem } => write!(f, "slice_len<ty.{}>", elem.0),
            PointerMetadataShape::StrLen => f.write_str("str_len"),
            PointerMetadataShape::VTable { trait_id } => write!(f, "vtable<dyn.{trait_id}>"),
        }
    }
}

impl FatPtrKind {
    pub fn metadata_shape(&self) -> PointerMetadataShape {
        match *self {
            FatPtrKind::Slice(elem) => PointerMetadataShape::SliceLen { elem },
            FatPtrKind::Str => PointerMetadataShape::StrLen,
            FatPtrKind::TraitObject { trait_id } => PointerMetadataShape::VTable { trait_id },
        }
    }

    pub fn metadata_ty(&self, pointer_bits: u32) -> Option<Ty> {
        self.metadata_shape().metadata_ty(pointer_bits)
    }
}

impl PointerMetadataShape {
    pub fn metadata_ty(self, pointer_bits: u32) -> Option<Ty> {
        match self {
            PointerMetadataShape::SliceLen { .. } | PointerMetadataShape::StrLen => {
                pointer_sized_unsigned_ty(pointer_bits)
            }
            PointerMetadataShape::VTable { .. } => Some(Ty::Ptr),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PointerLayoutShape {
    pub data_bits: u32,
    pub metadata_bits: Option<u32>,
    pub metadata: Option<PointerMetadataShape>,
}

impl PointerLayoutShape {
    pub fn thin(data_bits: u32) -> Self {
        Self {
            data_bits,
            metadata_bits: None,
            metadata: None,
        }
    }

    pub fn fat(pointer_bits: u32, metadata: PointerMetadataShape) -> Self {
        Self {
            data_bits: pointer_bits,
            metadata_bits: Some(pointer_bits),
            metadata: Some(metadata),
        }
    }

    pub fn lane_count(self) -> u8 {
        if self.metadata.is_some() { 2 } else { 1 }
    }

    pub fn is_fat(self) -> bool {
        self.metadata.is_some()
    }

    pub fn total_bits(self) -> Option<u32> {
        match self.metadata_bits {
            Some(metadata_bits) => self.data_bits.checked_add(metadata_bits),
            None => Some(self.data_bits),
        }
    }
}

impl core::fmt::Display for PointerLayoutShape {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match (self.metadata, self.metadata_bits) {
            (Some(metadata), Some(metadata_bits)) => {
                write!(
                    f,
                    "fat(data={}b, metadata={metadata}:{}b)",
                    self.data_bits, metadata_bits
                )
            }
            _ => write!(f, "thin(data={}b)", self.data_bits),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CastShape {
    IntegerResize,
    FloatResize,
    FloatInteger,
    PointerInteger,
    Pointer,
    Bitcast,
    Transmute,
    ReifyFnPointer,
}

impl core::fmt::Display for CastShape {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            CastShape::IntegerResize => "integer_resize",
            CastShape::FloatResize => "float_resize",
            CastShape::FloatInteger => "float_integer",
            CastShape::PointerInteger => "pointer_integer",
            CastShape::Pointer => "pointer",
            CastShape::Bitcast => "bitcast",
            CastShape::Transmute => "transmute",
            CastShape::ReifyFnPointer => "reify_fn_pointer",
        })
    }
}

impl CastOp {
    pub fn shape(self) -> CastShape {
        match self {
            CastOp::Trunc | CastOp::ZExt | CastOp::SExt => CastShape::IntegerResize,
            CastOp::FPTrunc | CastOp::FPExt => CastShape::FloatResize,
            CastOp::FPToUI
            | CastOp::FPToSI
            | CastOp::FPToUISat
            | CastOp::FPToSISat
            | CastOp::UIToFP
            | CastOp::SIToFP => CastShape::FloatInteger,
            CastOp::PtrToInt | CastOp::IntToPtr => CastShape::PointerInteger,
            CastOp::PtrToPtr => CastShape::Pointer,
            CastOp::Bitcast => CastShape::Bitcast,
            CastOp::Transmute => CastShape::Transmute,
            CastOp::ReifyFnPointer => CastShape::ReifyFnPointer,
        }
    }

    pub fn is_layout_sensitive(self) -> bool {
        matches!(
            self,
            CastOp::PtrToPtr | CastOp::Bitcast | CastOp::Transmute | CastOp::ReifyFnPointer
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FieldOffsetShape {
    pub field: u32,
    pub name: String,
    pub ty_shape: TyShape,
    pub offset_bits: Option<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TyLayoutKind {
    Scalar(TyShape),
    ThinPointer,
    FatPointer(PointerMetadataShape),
    Struct {
        id: StructId,
        fields: Vec<FieldOffsetShape>,
    },
    Enum {
        id: EnumId,
        variants: usize,
    },
    Array {
        elem: TyId,
        len: u64,
        stride_bits: u64,
    },
    Vector {
        elem_shape: TyShape,
        lanes: u32,
        lane_bits: u64,
    },
    Unit,
    Never,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TyLayoutShape {
    pub size_bits: u64,
    pub align_bits: Option<u64>,
    pub kind: TyLayoutKind,
}

/// trust-ir's **canonical tagged-union layout** of a `Ty::Enum`, computed by
/// [`Module::enum_layout_shape`].
///
/// # Canonical layout rules (all sizes/alignments in bits, byte-multiples)
///
/// * The **tag** — an integer of type [`EnumLayoutShape::tag`]
///   ([`crate::ty::EnumDef::canonical_tag_repr`]: the explicit `repr` hint, or
///   the smallest integer fitting every effective discriminant) — sits at
///   offset 0 with its natural (size = alignment) requirements.
/// * Each variant's **payload** lays its fields out C-style (each field at
///   the next offset aligned to the field's natural alignment; variant
///   alignment = max field alignment, min 1 byte; variant size rounded up to
///   the variant alignment).
/// * The shared **payload region** starts at
///   [`EnumLayoutShape::payload_offset_bits`] = the tag size aligned up to
///   the payload alignment (max variant alignment), and spans
///   [`EnumLayoutShape::payload_size_bits`] = the largest variant size.
/// * The enum's alignment is `max(tag alignment, payload alignment)`; its
///   size is `payload_offset + payload_size` rounded up to that alignment.
///
/// # This is trust-ir's layout, NOT rustc's
///
/// rustc's `repr(Rust)` enums perform niche optimization (`Option<&T>` is
/// pointer-sized), variant reordering, and other layout optimizations that
/// this canonical shape deliberately does not model. A producer can instead
/// supply an [`crate::ty::EnumLayoutDescriptor`]; when present it is
/// normative, and its size, alignment, offsets, and tag encoding replace the
/// synthesized byte layout.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct EnumLayoutShape {
    /// The enum this layout describes.
    pub id: EnumId,
    /// Resolved logical tag integer type. Its byte position is offset 0 only
    /// for the canonical layout; a descriptor supplies its own encoding.
    pub tag: EnumTagRepr,
    /// Logical tag size in bits (= its natural alignment).
    pub tag_size_bits: u64,
    /// Canonical shared-payload offset in bits. This is a legacy projection
    /// when `descriptor.is_some()`; descriptor field offsets are normative.
    pub payload_offset_bits: u64,
    /// Canonical shared-payload size in bits. This is a legacy projection when
    /// `descriptor.is_some()`.
    pub payload_size_bits: u64,
    /// Total size in bits. A descriptor overrides the canonical tagged-union
    /// calculation.
    pub size_bits: u64,
    /// Alignment in bits. Without a descriptor this is `max(tag alignment,
    /// payload alignment)`; otherwise it is the descriptor alignment.
    pub align_bits: u64,
    /// Effective discriminant of each variant, in variant order
    /// ([`crate::ty::EnumDef::effective_discriminants`]).
    pub discriminants: Vec<i128>,
    /// Normative concrete layout when one was supplied by the producer.
    #[cfg_attr(feature = "serde", serde(default))]
    pub descriptor: Option<crate::ty::EnumLayoutDescriptor>,
}

impl TyLayoutShape {
    pub fn size_bytes(&self) -> Option<u64> {
        self.size_bits
            .checked_div(8)
            .filter(|_| self.size_bits.is_multiple_of(8))
    }
}

impl core::fmt::Display for TyLayoutKind {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TyLayoutKind::Scalar(shape) => write!(f, "scalar<{shape}>"),
            TyLayoutKind::ThinPointer => f.write_str("thin_pointer"),
            TyLayoutKind::FatPointer(metadata) => write!(f, "fat_pointer<{metadata}>"),
            TyLayoutKind::Struct { id, fields } => {
                write!(f, "struct.{}[{} fields]", id.0, fields.len())
            }
            TyLayoutKind::Enum { id, variants } => {
                write!(f, "enum.{}[{} variants]", id.0, variants)
            }
            TyLayoutKind::Array {
                elem,
                len,
                stride_bits,
            } => {
                write!(f, "array<ty.{}, len={len}, stride={stride_bits}b>", elem.0)
            }
            TyLayoutKind::Vector {
                elem_shape,
                lanes,
                lane_bits,
            } => write!(f, "vector<{lanes} x {elem_shape}, lane={lane_bits}b>"),
            TyLayoutKind::Unit => f.write_str("unit"),
            TyLayoutKind::Never => f.write_str("never"),
        }
    }
}

impl core::fmt::Display for TyLayoutShape {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self.align_bits {
            Some(align_bits) => write!(
                f,
                "{} size={}b align={}b",
                self.kind, self.size_bits, align_bits
            ),
            None => write!(f, "{} size={}b align=?", self.kind, self.size_bits),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum LayoutError {
    MissingType(TyId),
    MissingStruct(StructId),
    MissingStructSize(StructId),
    MissingFieldOffset {
        struct_id: StructId,
        field: u32,
    },
    EnumLayoutUnavailable(EnumId),
    UnsupportedTyShape(TyShape),
    SizeOverflow,
    NotPointer(TyShape),
    PointerLaneMismatch {
        src_lanes: u8,
        dst_lanes: u8,
    },
    PointerMetadataMismatch {
        src: Option<PointerMetadataShape>,
        dst: Option<PointerMetadataShape>,
    },
    NotFunctionPointerSource(TyShape),
    CastSizeMismatch {
        src_bits: u64,
        dst_bits: u64,
    },
}

impl core::fmt::Display for LayoutError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            LayoutError::MissingType(id) => write!(f, "type table entry ty.{} is missing", id.0),
            LayoutError::MissingStruct(id) => {
                write!(f, "struct layout entry struct.{} is missing", id.0)
            }
            LayoutError::MissingStructSize(id) => {
                write!(f, "struct.{} has no size layout metadata", id.0)
            }
            LayoutError::MissingFieldOffset { struct_id, field } => write!(
                f,
                "struct.{} field {} has no offset layout metadata",
                struct_id.0, field
            ),
            LayoutError::EnumLayoutUnavailable(id) => {
                write!(f, "enum.{} has no concrete enum layout metadata", id.0)
            }
            LayoutError::UnsupportedTyShape(shape) => {
                write!(f, "{shape} has no concrete memory layout evidence")
            }
            LayoutError::SizeOverflow => f.write_str("layout size overflow"),
            LayoutError::NotPointer(shape) => write!(f, "{shape} is not pointer-like"),
            LayoutError::PointerLaneMismatch {
                src_lanes,
                dst_lanes,
            } => write!(
                f,
                "pointer cast changes lane count from {src_lanes} to {dst_lanes}"
            ),
            LayoutError::PointerMetadataMismatch { src, dst } => write!(
                f,
                "pointer cast changes metadata from {:?} to {:?}",
                src, dst
            ),
            LayoutError::NotFunctionPointerSource(shape) => {
                write!(
                    f,
                    "reify_fn_pointer source must be a function item, got {shape}"
                )
            }
            LayoutError::CastSizeMismatch { src_bits, dst_bits } => {
                write!(f, "cast layout sizes differ: {src_bits}b -> {dst_bits}b")
            }
        }
    }
}

impl std::error::Error for LayoutError {}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CastLayoutEvidence {
    NotLayoutSensitive,
    PointerCast {
        src: PointerLayoutShape,
        dst: PointerLayoutShape,
    },
    SameSize {
        size_bits: u64,
        src_align_bits: Option<u64>,
        dst_align_bits: Option<u64>,
    },
    ReifyFnPointer {
        pointer_bits: u32,
    },
}

impl core::fmt::Display for CastLayoutEvidence {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            CastLayoutEvidence::NotLayoutSensitive => f.write_str("not_layout_sensitive"),
            CastLayoutEvidence::PointerCast { src, dst } => {
                write!(f, "pointer_cast({src} -> {dst})")
            }
            CastLayoutEvidence::SameSize {
                size_bits,
                src_align_bits,
                dst_align_bits,
            } => write!(
                f,
                "same_size({size_bits}b, src_align={:?}, dst_align={:?})",
                src_align_bits, dst_align_bits
            ),
            CastLayoutEvidence::ReifyFnPointer { pointer_bits } => {
                write!(f, "reify_fn_pointer({pointer_bits}b)")
            }
        }
    }
}

impl Module {
    pub fn pointer_bits(&self) -> u32 {
        self.target_info
            .as_ref()
            .and_then(|target| target.pointer_size.checked_mul(8))
            .unwrap_or(DEFAULT_POINTER_BITS)
    }

    pub fn ty_layout_shape(&self, ty: &Ty) -> Result<TyLayoutShape, LayoutError> {
        self.ty_layout_shape_inner(ty, &mut Vec::new())
    }

    /// [`Module::ty_layout_shape`] with the enum cycle guard threaded through:
    /// `enum_visiting` tracks the enum ids currently being laid out, so a
    /// self-referential enum (an inline `Ty::Enum` cycle not broken by a
    /// pointer) fails closed with [`LayoutError::EnumLayoutUnavailable`]
    /// instead of recursing without bound.
    fn ty_layout_shape_inner(
        &self,
        ty: &Ty,
        enum_visiting: &mut Vec<EnumId>,
    ) -> Result<TyLayoutShape, LayoutError> {
        let pointer_bits = self.pointer_bits();
        match ty {
            Ty::Bool => Ok(scalar_layout(TyShape::Bool, 8, Some(8))),
            Ty::I8 => Ok(scalar_layout(
                TyShape::Int {
                    signed: true,
                    bits: 8,
                },
                8,
                Some(8),
            )),
            Ty::I16 => Ok(scalar_layout(
                TyShape::Int {
                    signed: true,
                    bits: 16,
                },
                16,
                Some(16),
            )),
            Ty::I32 => Ok(scalar_layout(
                TyShape::Int {
                    signed: true,
                    bits: 32,
                },
                32,
                Some(32),
            )),
            Ty::I64 => Ok(scalar_layout(
                TyShape::Int {
                    signed: true,
                    bits: 64,
                },
                64,
                Some(64),
            )),
            Ty::I128 => Ok(scalar_layout(
                TyShape::Int {
                    signed: true,
                    bits: 128,
                },
                128,
                Some(128),
            )),
            Ty::U8 => Ok(scalar_layout(
                TyShape::Int {
                    signed: false,
                    bits: 8,
                },
                8,
                Some(8),
            )),
            Ty::U16 => Ok(scalar_layout(
                TyShape::Int {
                    signed: false,
                    bits: 16,
                },
                16,
                Some(16),
            )),
            Ty::U32 => Ok(scalar_layout(
                TyShape::Int {
                    signed: false,
                    bits: 32,
                },
                32,
                Some(32),
            )),
            Ty::U64 => Ok(scalar_layout(
                TyShape::Int {
                    signed: false,
                    bits: 64,
                },
                64,
                Some(64),
            )),
            Ty::U128 => Ok(scalar_layout(
                TyShape::Int {
                    signed: false,
                    bits: 128,
                },
                128,
                Some(128),
            )),
            // v25 B1 scalars: pointer-width ints take the target's pointer
            // width; char is a 32-bit scalar; Error has NO layout (typing
            // hole - fail closed).
            Ty::Isize => Ok(scalar_layout(
                TyShape::PointerInt { signed: true },
                u64::from(pointer_bits),
                Some(u64::from(pointer_bits)),
            )),
            Ty::Usize => Ok(scalar_layout(
                TyShape::PointerInt { signed: false },
                u64::from(pointer_bits),
                Some(u64::from(pointer_bits)),
            )),
            Ty::Char => Ok(scalar_layout(
                TyShape::Int {
                    signed: false,
                    bits: 32,
                },
                32,
                Some(32),
            )),
            Ty::Error => Err(LayoutError::UnsupportedTyShape(TyShape::Error)),
            Ty::F16 => Ok(scalar_layout(TyShape::Float { bits: 16 }, 16, Some(16))),
            Ty::F32 => Ok(scalar_layout(TyShape::Float { bits: 32 }, 32, Some(32))),
            Ty::F64 => Ok(scalar_layout(TyShape::Float { bits: 64 }, 64, Some(64))),
            Ty::Ptr
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Rc(_)
            | Ty::Func(_) => Ok(TyLayoutShape {
                size_bits: u64::from(pointer_bits),
                align_bits: Some(u64::from(pointer_bits)),
                kind: TyLayoutKind::ThinPointer,
            }),
            Ty::FatPtr(kind) => {
                let ptr = PointerLayoutShape::fat(pointer_bits, kind.metadata_shape());
                let size_bits = u64::from(ptr.total_bits().ok_or(LayoutError::SizeOverflow)?);
                Ok(TyLayoutShape {
                    size_bits,
                    align_bits: Some(u64::from(pointer_bits)),
                    kind: TyLayoutKind::FatPointer(kind.metadata_shape()),
                })
            }
            Ty::Unit => Ok(TyLayoutShape {
                size_bits: 0,
                align_bits: Some(8),
                kind: TyLayoutKind::Unit,
            }),
            Ty::Never => Ok(TyLayoutShape {
                size_bits: 0,
                align_bits: None,
                kind: TyLayoutKind::Never,
            }),
            Ty::Struct(id) => {
                let sd = self
                    .structs
                    .iter()
                    .find(|sd| sd.id == *id)
                    .ok_or(LayoutError::MissingStruct(*id))?;
                let size = sd.size.ok_or(LayoutError::MissingStructSize(*id))?;
                let fields = sd
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(field, def)| FieldOffsetShape {
                        field: field as u32,
                        name: def.name.clone(),
                        ty_shape: def.ty.shape(),
                        offset_bits: def.offset.and_then(|offset| offset.checked_mul(8)),
                    })
                    .collect();
                Ok(TyLayoutShape {
                    size_bits: size.checked_mul(8).ok_or(LayoutError::SizeOverflow)?,
                    align_bits: sd.align.and_then(|align| align.checked_mul(8)),
                    kind: TyLayoutKind::Struct { id: *id, fields },
                })
            }
            Ty::Array(elem, len) => {
                let elem_ty = self
                    .types
                    .get(elem.as_usize())
                    .ok_or(LayoutError::MissingType(*elem))?;
                let elem_layout = self.ty_layout_shape_inner(elem_ty, enum_visiting)?;
                Ok(TyLayoutShape {
                    size_bits: elem_layout
                        .size_bits
                        .checked_mul(*len)
                        .ok_or(LayoutError::SizeOverflow)?,
                    align_bits: elem_layout.align_bits,
                    kind: TyLayoutKind::Array {
                        elem: *elem,
                        len: *len,
                        stride_bits: elem_layout.size_bits,
                    },
                })
            }
            Ty::Vector(elem, lanes) => {
                let elem_layout = self.ty_layout_shape_inner(elem, enum_visiting)?;
                Ok(TyLayoutShape {
                    size_bits: elem_layout
                        .size_bits
                        .checked_mul(u64::from(*lanes))
                        .ok_or(LayoutError::SizeOverflow)?,
                    align_bits: elem_layout.align_bits,
                    kind: TyLayoutKind::Vector {
                        elem_shape: elem.shape(),
                        lanes: *lanes,
                        lane_bits: elem_layout.size_bits,
                    },
                })
            }
            // trust-ir's CANONICAL tagged-union layout (see
            // `Module::enum_layout_shape`). Deliberately NOT a claim of rustc
            // layout parity: no niche optimization, no variant reordering.
            Ty::Enum(id) => {
                let layout = self.enum_layout_shape_inner(*id, enum_visiting)?;
                Ok(TyLayoutShape {
                    size_bits: layout.size_bits,
                    align_bits: Some(layout.align_bits),
                    kind: TyLayoutKind::Enum {
                        id: *id,
                        variants: layout.discriminants.len(),
                    },
                })
            }
            Ty::Tuple(elems) if elems.is_empty() => Ok(TyLayoutShape {
                size_bits: 0,
                align_bits: Some(8),
                kind: TyLayoutKind::Unit,
            }),
            // REPRESENTATION PRESERVATION, enforced here: a `Refine(b, p)`
            // lays out EXACTLY as `b` does. This delegation is what makes the
            // whole typed-value-model change unable to move a byte of any
            // downstream artifact.
            Ty::Refine(base, _) => match self.types.get(base.as_usize()) {
                Some(base_ty) => self.ty_layout_shape_inner(base_ty, enum_visiting),
                None => Err(LayoutError::UnsupportedTyShape(TyShape::Refine)),
            },
            Ty::Tuple(_) | Ty::Closure(_) | Ty::Set(_, _) | Ty::Sequence(_) | Ty::Record(_) => {
                Err(LayoutError::UnsupportedTyShape(ty.shape()))
            }
        }
    }

    /// Compute trust-ir's **canonical tagged-union layout** for `enum.id`.
    ///
    /// See [`EnumLayoutShape`] for the layout rules and the explicit
    /// non-parity disclaimer (this is trust-ir's canonical layout, not
    /// rustc's). Fail-closed: a missing def, an unresolvable discriminant
    /// assignment (duplicates / overflow / a `repr` hint too narrow /
    /// \>64-bit values), zero variants (uninhabited), or an inline
    /// self-referential enum cycle all yield
    /// [`LayoutError::EnumLayoutUnavailable`]; a variant field whose own
    /// layout is unavailable propagates its error — never a partial or wrong
    /// layout.
    pub fn enum_layout_shape(&self, id: EnumId) -> Result<EnumLayoutShape, LayoutError> {
        self.enum_layout_shape_inner(id, &mut Vec::new())
    }

    /// [`Module::enum_layout_shape`] with the shared enum cycle guard.
    fn enum_layout_shape_inner(
        &self,
        id: EnumId,
        enum_visiting: &mut Vec<EnumId>,
    ) -> Result<EnumLayoutShape, LayoutError> {
        if enum_visiting.contains(&id) {
            // Inline self-reference (not broken by a pointer): no finite
            // canonical layout exists.
            return Err(LayoutError::EnumLayoutUnavailable(id));
        }
        let ed = self
            .enums
            .iter()
            .find(|ed| ed.id == id)
            .ok_or(LayoutError::EnumLayoutUnavailable(id))?;
        let discriminants = ed
            .effective_discriminants()
            .ok_or(LayoutError::EnumLayoutUnavailable(id))?;
        let tag = ed
            .canonical_tag_repr()
            .ok_or(LayoutError::EnumLayoutUnavailable(id))?;
        let tag_size_bits = u64::from(
            tag.ty()
                .bit_width()
                .expect("enum tag repr is a sized integer"),
        );

        enum_visiting.push(id);
        let result = (|| {
            // Payload region: each variant laid out C-style; the region takes
            // the max variant size and max variant alignment (min 1 byte).
            let mut payload_size_bits: u64 = 0;
            let mut payload_align_bits: u64 = 8;
            let mut variant_field_sizes = Vec::with_capacity(ed.variants.len());
            let mut variant_field_aligns = Vec::with_capacity(ed.variants.len());
            for variant in &ed.variants {
                let mut offset_bits: u64 = 0;
                let mut variant_align_bits: u64 = 8;
                let mut field_sizes = Vec::with_capacity(variant.fields.len());
                let mut field_aligns = Vec::with_capacity(variant.fields.len());
                for field_ty in &variant.fields {
                    let field_layout = self.ty_layout_shape_inner(field_ty, enum_visiting)?;
                    let field_size = field_layout
                        .size_bytes()
                        .ok_or(LayoutError::EnumLayoutUnavailable(id))?;
                    let field_align_bits = field_layout
                        .align_bits
                        .ok_or(LayoutError::EnumLayoutUnavailable(id))?
                        .max(8);
                    offset_bits = align_up_bits(offset_bits, field_align_bits)?;
                    offset_bits = offset_bits
                        .checked_add(field_layout.size_bits)
                        .ok_or(LayoutError::SizeOverflow)?;
                    variant_align_bits = variant_align_bits.max(field_align_bits);
                    field_sizes.push(field_size);
                    field_aligns.push(field_align_bits / 8);
                }
                let variant_size_bits = align_up_bits(offset_bits, variant_align_bits)?;
                payload_size_bits = payload_size_bits.max(variant_size_bits);
                payload_align_bits = payload_align_bits.max(variant_align_bits);
                variant_field_sizes.push(field_sizes);
                variant_field_aligns.push(field_aligns);
            }

            let payload_offset_bits = align_up_bits(tag_size_bits, payload_align_bits)?;
            let mut align_bits = tag_size_bits.max(payload_align_bits);
            let mut size_bits = align_up_bits(
                payload_offset_bits
                    .checked_add(payload_size_bits)
                    .ok_or(LayoutError::SizeOverflow)?,
                align_bits,
            )?;
            if let Some(desc) = &ed.layout {
                if desc.align == 0
                    || !desc.align.is_power_of_two()
                    || !desc.size.is_multiple_of(desc.align)
                    || desc.variant_field_offsets.len() != ed.variants.len()
                {
                    return Err(LayoutError::EnumLayoutUnavailable(id));
                }
                for ((offsets, sizes), aligns) in desc
                    .variant_field_offsets
                    .iter()
                    .zip(&variant_field_sizes)
                    .zip(&variant_field_aligns)
                {
                    if offsets.len() != sizes.len() || offsets.len() != aligns.len() {
                        return Err(LayoutError::EnumLayoutUnavailable(id));
                    }
                    for ((offset, field_size), field_align) in offsets.iter().zip(sizes).zip(aligns)
                    {
                        if !offset.is_multiple_of(*field_align)
                            || *field_align > desc.align
                            || offset
                                .checked_add(*field_size)
                                .is_none_or(|end| end > desc.size)
                        {
                            return Err(LayoutError::EnumLayoutUnavailable(id));
                        }
                    }
                    for left in 0..offsets.len() {
                        for right in left + 1..offsets.len() {
                            if byte_ranges_overlap(
                                offsets[left],
                                sizes[left],
                                offsets[right],
                                sizes[right],
                            ) {
                                return Err(LayoutError::EnumLayoutUnavailable(id));
                            }
                        }
                    }
                }
                match &desc.encoding {
                    // v37: no tag lane exists, so every tag-PLACEMENT check is
                    // vacuous — there is no offset to align, nothing to fit
                    // inside `desc.size`, and nothing that could overlap a
                    // payload field. The per-field bound above still ran and is
                    // what makes this encoding safe: the fields must lie inside
                    // the declared size exactly as for the tagged encodings.
                    //
                    // The one check with content is that a variant is
                    // RECOVERABLE without reading anything, which holds exactly
                    // when there is one. This mirrors the interpreter and the
                    // validator: all three must agree, or a shape query would
                    // report a size for an enum the interpreter refuses to load.
                    crate::ty::EnumTagEncoding::Untagged => {
                        if ed.variants.len() != 1 {
                            return Err(LayoutError::EnumLayoutUnavailable(id));
                        }
                    }
                    crate::ty::EnumTagEncoding::Direct { tag_offset } => {
                        let tag_size = tag_size_bits / 8;
                        if tag_size > desc.align
                            || !tag_offset.is_multiple_of(tag_size)
                            || tag_offset
                                .checked_add(tag_size)
                                .is_none_or(|end| end > desc.size)
                        {
                            return Err(LayoutError::EnumLayoutUnavailable(id));
                        }
                        for (offsets, sizes) in
                            desc.variant_field_offsets.iter().zip(&variant_field_sizes)
                        {
                            if offsets.iter().zip(sizes).any(|(offset, field_size)| {
                                byte_ranges_overlap(*tag_offset, tag_size, *offset, *field_size)
                            }) {
                                return Err(LayoutError::EnumLayoutUnavailable(id));
                            }
                        }
                    }
                    crate::ty::EnumTagEncoding::Niche {
                        untagged_variant,
                        niche_variants_start,
                        niche_variants_end,
                        niche_start,
                        niche_offset,
                        niche_ty,
                    } => {
                        let variant_count = u32::try_from(ed.variants.len())
                            .map_err(|_| LayoutError::EnumLayoutUnavailable(id))?;
                        let niche_size = enum_tag_repr_bytes(*niche_ty);
                        let niche_bits = u32::try_from(niche_size * 8)
                            .map_err(|_| LayoutError::EnumLayoutUnavailable(id))?;
                        let niche_mask = match niche_bits {
                            0 => return Err(LayoutError::EnumLayoutUnavailable(id)),
                            128 => u128::MAX,
                            bits if bits < 128 => (1u128 << bits) - 1,
                            _ => return Err(LayoutError::EnumLayoutUnavailable(id)),
                        };
                        let niche_span = niche_variants_end
                            .checked_sub(*niche_variants_start)
                            .map(u128::from)
                            .ok_or(LayoutError::EnumLayoutUnavailable(id))?;
                        let extra_untagged = if (*niche_variants_start..=*niche_variants_end)
                            .contains(untagged_variant)
                        {
                            0
                        } else {
                            1
                        };
                        if *untagged_variant >= variant_count
                            || *niche_variants_end >= variant_count
                            || niche_span
                                .checked_add(1)
                                .and_then(|covered| covered.checked_add(extra_untagged))
                                != Some(u128::from(variant_count))
                            || niche_span > niche_mask
                            || *niche_start > niche_mask
                            || niche_size > desc.align
                            || !niche_offset.is_multiple_of(niche_size)
                            || niche_offset
                                .checked_add(niche_size)
                                .is_none_or(|end| end > desc.size)
                        {
                            return Err(LayoutError::EnumLayoutUnavailable(id));
                        }
                        let untagged = *untagged_variant as usize;
                        let lane_end = niche_offset
                            .checked_add(niche_size)
                            .ok_or(LayoutError::EnumLayoutUnavailable(id))?;
                        let lane_is_covered = desc.variant_field_offsets[untagged]
                            .iter()
                            .zip(&variant_field_sizes[untagged])
                            .any(|(field_offset, field_size)| {
                                *field_size > 0
                                    && *field_offset <= *niche_offset
                                    && field_offset
                                        .checked_add(*field_size)
                                        .is_some_and(|field_end| field_end >= lane_end)
                            });
                        if !lane_is_covered {
                            return Err(LayoutError::EnumLayoutUnavailable(id));
                        }
                        for variant in *niche_variants_start..=*niche_variants_end {
                            if variant == *untagged_variant {
                                continue;
                            }
                            let variant = variant as usize;
                            if desc.variant_field_offsets[variant]
                                .iter()
                                .zip(&variant_field_sizes[variant])
                                .any(|(field_offset, field_size)| {
                                    byte_ranges_overlap(
                                        *niche_offset,
                                        niche_size,
                                        *field_offset,
                                        *field_size,
                                    )
                                })
                            {
                                return Err(LayoutError::EnumLayoutUnavailable(id));
                            }
                        }
                    }
                }
                size_bits = desc.size.checked_mul(8).ok_or(LayoutError::SizeOverflow)?;
                align_bits = desc.align.checked_mul(8).ok_or(LayoutError::SizeOverflow)?;
            }
            Ok(EnumLayoutShape {
                id,
                tag,
                tag_size_bits,
                payload_offset_bits,
                payload_size_bits,
                size_bits,
                align_bits,
                discriminants,
                descriptor: ed.layout.clone(),
            })
        })();
        enum_visiting.pop();
        result
    }

    pub fn struct_field_offset_bits(
        &self,
        struct_id: StructId,
        field: u32,
    ) -> Result<u64, LayoutError> {
        let sd = self
            .structs
            .iter()
            .find(|sd| sd.id == struct_id)
            .ok_or(LayoutError::MissingStruct(struct_id))?;
        let field_def = sd
            .fields
            .get(field as usize)
            .ok_or(LayoutError::MissingFieldOffset { struct_id, field })?;
        field_def
            .offset
            .and_then(|offset| offset.checked_mul(8))
            .ok_or(LayoutError::MissingFieldOffset { struct_id, field })
    }

    pub fn layout_sensitive_cast_evidence(
        &self,
        op: CastOp,
        src: &Ty,
        dst: &Ty,
    ) -> Result<CastLayoutEvidence, LayoutError> {
        if !op.is_layout_sensitive() {
            return Ok(CastLayoutEvidence::NotLayoutSensitive);
        }

        match op {
            CastOp::PtrToPtr => {
                let pointer_bits = self.pointer_bits();
                let src_layout = src
                    .pointer_layout_shape(pointer_bits)
                    .ok_or_else(|| LayoutError::NotPointer(src.shape()))?;
                let dst_layout = dst
                    .pointer_layout_shape(pointer_bits)
                    .ok_or_else(|| LayoutError::NotPointer(dst.shape()))?;
                if src_layout.lane_count() != dst_layout.lane_count() {
                    return Err(LayoutError::PointerLaneMismatch {
                        src_lanes: src_layout.lane_count(),
                        dst_lanes: dst_layout.lane_count(),
                    });
                }
                if src_layout.metadata != dst_layout.metadata {
                    return Err(LayoutError::PointerMetadataMismatch {
                        src: src_layout.metadata,
                        dst: dst_layout.metadata,
                    });
                }
                Ok(CastLayoutEvidence::PointerCast {
                    src: src_layout,
                    dst: dst_layout,
                })
            }
            CastOp::Bitcast | CastOp::Transmute => {
                let src_layout = self.ty_layout_shape(src)?;
                let dst_layout = self.ty_layout_shape(dst)?;
                if src_layout.size_bits != dst_layout.size_bits {
                    return Err(LayoutError::CastSizeMismatch {
                        src_bits: src_layout.size_bits,
                        dst_bits: dst_layout.size_bits,
                    });
                }
                Ok(CastLayoutEvidence::SameSize {
                    size_bits: src_layout.size_bits,
                    src_align_bits: src_layout.align_bits,
                    dst_align_bits: dst_layout.align_bits,
                })
            }
            CastOp::ReifyFnPointer => {
                if !matches!(src, Ty::Func(_)) {
                    return Err(LayoutError::NotFunctionPointerSource(src.shape()));
                }
                let pointer_bits = self.pointer_bits();
                let dst_layout = dst
                    .pointer_layout_shape(pointer_bits)
                    .ok_or_else(|| LayoutError::NotPointer(dst.shape()))?;
                if dst_layout.is_fat() {
                    return Err(LayoutError::PointerLaneMismatch {
                        src_lanes: 1,
                        dst_lanes: dst_layout.lane_count(),
                    });
                }
                Ok(CastLayoutEvidence::ReifyFnPointer { pointer_bits })
            }
            _ => Ok(CastLayoutEvidence::NotLayoutSensitive),
        }
    }
}

fn scalar_layout(shape: TyShape, size_bits: u64, align_bits: Option<u64>) -> TyLayoutShape {
    TyLayoutShape {
        size_bits,
        align_bits,
        kind: TyLayoutKind::Scalar(shape),
    }
}

/// Round `offset_bits` up to the next multiple of `align_bits` (nonzero),
/// failing closed on arithmetic overflow.
fn align_up_bits(offset_bits: u64, align_bits: u64) -> Result<u64, LayoutError> {
    debug_assert!(align_bits > 0, "alignment must be nonzero");
    let rem = offset_bits % align_bits;
    if rem == 0 {
        return Ok(offset_bits);
    }
    offset_bits
        .checked_add(align_bits - rem)
        .ok_or(LayoutError::SizeOverflow)
}

fn byte_ranges_overlap(a_offset: u64, a_size: u64, b_offset: u64, b_size: u64) -> bool {
    if a_size == 0 || b_size == 0 {
        return false;
    }
    let Some(a_end) = a_offset.checked_add(a_size) else {
        return true;
    };
    let Some(b_end) = b_offset.checked_add(b_size) else {
        return true;
    };
    a_offset < b_end && b_offset < a_end
}

fn enum_tag_repr_bytes(repr: EnumTagRepr) -> u64 {
    u64::from(
        repr.ty()
            .bit_width()
            .expect("enum tag repr is a sized integer"),
    ) / 8
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ConstantShape {
    Int,
    /// v25 raw byte-array constant (`Constant::Bytes`).
    Bytes {
        len: usize,
    },
    Float,
    Bool,
    Aggregate {
        len: usize,
    },
    Array {
        len: usize,
    },
    Vector {
        len: usize,
    },
    Sequence {
        len: usize,
    },
    Set {
        len: usize,
    },
    Record {
        fields: usize,
    },
    Closure {
        captures: usize,
    },
    FnDef,
    SymbolAddr,
    PhantomData,
}

impl core::fmt::Display for ConstantShape {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ConstantShape::Int => f.write_str("int"),
            ConstantShape::Bytes { len } => write!(f, "bytes[{len}]"),
            ConstantShape::Float => f.write_str("float"),
            ConstantShape::Bool => f.write_str("bool"),
            ConstantShape::Aggregate { len } => write!(f, "aggregate[{len}]"),
            ConstantShape::Array { len } => write!(f, "array[{len}]"),
            ConstantShape::Vector { len } => write!(f, "vector[{len}]"),
            ConstantShape::Sequence { len } => write!(f, "sequence[{len}]"),
            ConstantShape::Set { len } => write!(f, "set[{len}]"),
            ConstantShape::Record { fields } => write!(f, "record[{fields}]"),
            ConstantShape::Closure { captures } => write!(f, "closure[{captures}]"),
            ConstantShape::FnDef => f.write_str("fndef"),
            ConstantShape::SymbolAddr => f.write_str("symaddr"),
            ConstantShape::PhantomData => f.write_str("phantomdata"),
        }
    }
}

impl Constant {
    pub fn shape(&self) -> ConstantShape {
        match self {
            Constant::Int(_) => ConstantShape::Int,
            // v24: an unsigned 128-bit constant IS an integer shape — shape is
            // the coarse value classification, not the carrier spelling.
            Constant::U128(_) => ConstantShape::Int,
            Constant::Bytes { data, .. } => ConstantShape::Bytes { len: data.len() },
            Constant::Float(_) => ConstantShape::Float,
            Constant::Bool(_) => ConstantShape::Bool,
            Constant::Aggregate(v) => ConstantShape::Aggregate { len: v.len() },
            Constant::Array(v) => ConstantShape::Array { len: v.len() },
            Constant::Vector(v) => ConstantShape::Vector { len: v.len() },
            Constant::Sequence(v) => ConstantShape::Sequence { len: v.len() },
            Constant::Set(v) => ConstantShape::Set { len: v.len() },
            Constant::Record(v) => ConstantShape::Record { fields: v.len() },
            Constant::Closure { captures, .. } => ConstantShape::Closure {
                captures: captures.len(),
            },
            Constant::FnDef(_) => ConstantShape::FnDef,
            Constant::SymbolAddr { .. } => ConstantShape::SymbolAddr,
            Constant::PhantomData => ConstantShape::PhantomData,
        }
    }

    pub fn shape_label(&self) -> String {
        match self {
            Constant::Closure { func, captures } => {
                format!("closure<func.{}>[{}]", func.index(), captures.len())
            }
            Constant::FnDef(func) => format!("fndef<func.{}>", func.index()),
            Constant::SymbolAddr { symbol, addend } => {
                format!("symaddr<{symbol} + {addend}>")
            }
            _ => self.shape().to_string(),
        }
    }

    pub fn shape_matches_ty(&self, ty: &Ty) -> bool {
        match (self, ty) {
            (Constant::Int(_), t) if t.is_integer() => true,
            (Constant::Int(_), Ty::Ptr) => true,
            // v25: a char constant is an Int leaf under Ty::Char (char is NOT
            // an integer type - no arithmetic - but its constants are integer
            // scalars; the Unicode range is checked by int_value_fits_ty and
            // the validator).
            (Constant::Int(_), Ty::Char) => true,
            // v24: a canonical U128 (value > i128::MAX) only fits the U128
            // type - never a narrower integer, never a pointer (fail closed).
            (Constant::U128(_), Ty::U128) => true,
            // v25 Bytes: a byte-array payload — fits a same-length Array
            // (element-type U8-ness needs the module table and is checked by
            // validate_constant_against_ty, same split as Array constants).
            (Constant::Bytes { data, .. }, Ty::Array(_, n)) => *n == data.len() as u64,
            (Constant::Float(_), t) if t.is_float() => true,
            (Constant::Bool(_), Ty::Bool) => true,
            (Constant::Aggregate(_), Ty::Tuple(_))
            | (Constant::Aggregate(_), Ty::Array(_, _))
            | (Constant::Aggregate(_), Ty::Struct(_))
            | (Constant::Aggregate(_), Ty::Record(_)) => true,
            // Enum constants use the tag + payload Aggregate convention:
            // element 0 is the discriminant (`Constant::Int`), the rest are
            // the selected variant's fields. See the interpreter's
            // `constant_to_value` for the authoritative decoding.
            // Trust (B3-1): tightened from an unconditional `true` — the local
            // shape must at least carry the convention's head (a non-empty
            // aggregate whose element 0 is an integer discriminant). Variant
            // resolution/arity/field types need the module table and are
            // checked by `validate_constant_against_ty`'s enum arm (the same
            // split as Array element types).
            (Constant::Aggregate(elems), Ty::Enum(_)) => {
                matches!(elems.first(), Some(Constant::Int(_)))
            }
            (Constant::Array(_), Ty::Array(_, _)) => true,
            (Constant::Vector(_), Ty::Vector(_, _)) => true,
            (Constant::Sequence(_), Ty::Sequence(_)) => true,
            (Constant::Set(_), Ty::Set(_, _)) => true,
            (Constant::Record(_), Ty::Record(_)) => true,
            (Constant::Closure { .. }, Ty::Closure(_)) => true,
            (Constant::FnDef(_), Ty::Func(_)) => true,
            // A relocatable symbol address is a native pointer: it can stand
            // for a data-global pointer (`Ty::Ptr`) or a function pointer
            // (`Ty::Func`). It also appears as an element inside an aggregate
            // initializer, where the enclosing aggregate carries the type.
            (Constant::SymbolAddr { .. }, Ty::Ptr) => true,
            (Constant::SymbolAddr { .. }, Ty::Func(_)) => true,
            (Constant::PhantomData, Ty::Unit) => true,
            _ => false,
        }
    }

    /// Return true when this constant can be represented by the declared type.
    ///
    /// This is stricter than [`Constant::shape_matches_ty`]: integer constants
    /// are range-checked against the signedness and width of the target `Ty`,
    /// and vector lanes are checked recursively. `Constant::Int` is currently
    /// an `i128` payload, so `Ty::U128` accepts only the non-negative subset
    /// that the payload can represent.
    pub fn value_matches_ty(&self, ty: &Ty) -> bool {
        match (self, ty) {
            (Constant::Int(value), ty) if ty.is_integer() => int_value_fits_ty(*value, ty),
            // v25 Char: NOT an integer type (no arithmetic), but its constants
            // are Int leaves whose Unicode-scalar range must still be checked.
            (Constant::Int(value), Ty::Char) => int_value_fits_ty(*value, &Ty::Char),
            // v24: canonicality (value > i128::MAX) makes U128-vs-Ty::U128 the
            // only fitting pair; shape_matches_ty already enforces it, and the
            // value always fits (u128 IS the declared range).
            (Constant::U128(_), Ty::U128) => true,
            (Constant::Bytes { data, .. }, Ty::Array(_, n)) => *n == data.len() as u64,
            (Constant::Vector(elems), Ty::Vector(elem_ty, lanes)) => {
                elems.len() == *lanes as usize
                    && elems.iter().all(|elem| elem.value_matches_ty(elem_ty))
            }
            _ => self.shape_matches_ty(ty),
        }
    }
}

fn int_value_fits_ty(value: i128, ty: &Ty) -> bool {
    match ty {
        Ty::I8 => value >= i8::MIN as i128 && value <= i8::MAX as i128,
        Ty::I16 => value >= i16::MIN as i128 && value <= i16::MAX as i128,
        Ty::I32 => value >= i32::MIN as i128 && value <= i32::MAX as i128,
        Ty::I64 => value >= i64::MIN as i128 && value <= i64::MAX as i128,
        Ty::I128 => true,
        Ty::U8 => value >= 0 && value <= u8::MAX as i128,
        Ty::U16 => value >= 0 && value <= u16::MAX as i128,
        Ty::U32 => value >= 0 && value <= u32::MAX as i128,
        Ty::U64 => value >= 0 && value <= u64::MAX as i128,
        Ty::U128 => value >= 0,
        // v25 B1 scalars: pointer-width ints range-check at the 64-bit
        // reference width (the same fixed convention the interpreter and the
        // fat-pointer len word use); char range-checks as a Unicode scalar
        // (the validator enforces the same rule at the constant funnel).
        Ty::Isize => value >= i64::MIN as i128 && value <= i64::MAX as i128,
        Ty::Usize => value >= 0 && value <= u64::MAX as i128,
        Ty::Char => (0..=0x10FFFF).contains(&value) && !(0xD800..=0xDFFF).contains(&value),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ty::{FatPtrKind, FieldDef, StructDef};
    use crate::value::{ClosureTyId, EnumId, FuncId, FuncTyId, StructId, TyId};
    use crate::{Endianness, Module, TargetInfo};

    #[test]
    fn type_shape_classifies_bootstrap_mir_forms() {
        assert_eq!(Ty::Struct(StructId::new(0)).shape(), TyShape::Struct);
        assert_eq!(Ty::Enum(EnumId::new(0)).shape(), TyShape::Enum);
        assert_eq!(Ty::FatPtr(FatPtrKind::Str).shape(), TyShape::FatPointer);
        assert_eq!(Ty::Func(FuncTyId::new(0)).shape(), TyShape::Function);
        assert_eq!(Ty::Closure(ClosureTyId::new(0)).shape(), TyShape::Closure);
        assert_eq!(Ty::Vector(Box::new(Ty::I32), 4).shape(), TyShape::Vector);

        assert!(Ty::Struct(StructId::new(0)).is_adt());
        assert!(Ty::Enum(EnumId::new(0)).is_adt());
        assert!(Ty::Func(FuncTyId::new(0)).is_thin_pointer_like());
        assert!(Ty::FatPtr(FatPtrKind::Slice(TyId::new(0))).is_fat_pointer());
        assert!(Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 7 }).is_pointer_like());
    }

    #[test]
    fn pointer_layout_shapes_pin_fat_pointer_metadata_lanes() {
        // tRust #1081/#1082: downstream proof tools must see the exact
        // metadata lane instead of one opaque "fat pointer" bucket.
        let slice = Ty::FatPtr(FatPtrKind::Slice(TyId::new(9)))
            .pointer_layout_shape(64)
            .expect("slice fat pointer layout");
        assert_eq!(slice.data_bits, 64);
        assert_eq!(slice.metadata_bits, Some(64));
        assert_eq!(
            slice.metadata,
            Some(PointerMetadataShape::SliceLen { elem: TyId::new(9) })
        );
        assert_eq!(slice.lane_count(), 2);
        assert_eq!(slice.total_bits(), Some(128));
        assert_eq!(
            format!("{slice}"),
            "fat(data=64b, metadata=slice_len<ty.9>:64b)"
        );

        let str_ptr = Ty::FatPtr(FatPtrKind::Str)
            .default_pointer_layout_shape()
            .unwrap();
        assert_eq!(str_ptr.metadata, Some(PointerMetadataShape::StrLen));

        let dyn_ptr = Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 7 })
            .pointer_layout_shape(32)
            .unwrap();
        assert_eq!(
            dyn_ptr.metadata,
            Some(PointerMetadataShape::VTable { trait_id: 7 })
        );
        assert_eq!(dyn_ptr.total_bits(), Some(64));
        assert_eq!(
            format!("{dyn_ptr}"),
            "fat(data=32b, metadata=vtable<dyn.7>:32b)"
        );
    }

    #[test]
    fn pointer_layout_shapes_model_function_pointers_as_thin() {
        let func = Ty::Func(FuncTyId::new(3))
            .pointer_layout_shape(64)
            .expect("function pointer layout");
        assert_eq!(func, PointerLayoutShape::thin(64));
        assert_eq!(func.lane_count(), 1);
        assert!(!func.is_fat());
        assert_eq!(func.total_bits(), Some(64));
        assert_eq!(format!("{func}"), "thin(data=64b)");

        assert!(
            Ty::Closure(ClosureTyId::new(0))
                .pointer_layout_shape(64)
                .is_none()
        );
        assert!(Ty::I64.pointer_layout_shape(64).is_none());
    }

    #[test]
    fn pointer_metadata_type_is_target_pointer_sized() {
        let slice = Ty::FatPtr(FatPtrKind::Slice(TyId::new(9)));
        let str_ptr = Ty::FatPtr(FatPtrKind::Str);
        let dyn_ptr = Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 7 });

        assert_eq!(slice.pointer_metadata_ty(64), Some(Ty::U64));
        assert_eq!(str_ptr.pointer_metadata_ty(32), Some(Ty::U32));
        assert_eq!(dyn_ptr.pointer_metadata_ty(64), Some(Ty::Ptr));
        assert_eq!(Ty::Ptr.pointer_metadata_ty(64), Some(Ty::Unit));
        assert_eq!(Ty::I64.pointer_metadata_ty(64), None);
    }

    #[test]
    fn cast_shape_is_stable_and_explicit() {
        assert_eq!(CastOp::ZExt.shape(), CastShape::IntegerResize);
        assert_eq!(CastOp::FPExt.shape(), CastShape::FloatResize);
        assert_eq!(CastOp::FPToSI.shape(), CastShape::FloatInteger);
        assert_eq!(CastOp::PtrToInt.shape(), CastShape::PointerInteger);
        assert_eq!(CastOp::PtrToPtr.shape(), CastShape::Pointer);
        assert_eq!(CastOp::Transmute.shape(), CastShape::Transmute);
        assert!(CastOp::Transmute.is_layout_sensitive());
        assert!(CastOp::ReifyFnPointer.is_layout_sensitive());
    }

    #[test]
    fn module_layout_evidence_tracks_struct_offsets_and_array_stride() {
        let mut module = Module::new("layout");
        module.target_info = Some(TargetInfo {
            triple: "x86_64-unknown-linux-gnu".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        });
        let sid = StructId::new(0);
        module.add_struct(StructDef {
            id: sid,
            name: "Pair".into(),
            fields: vec![
                FieldDef {
                    name: "a".into(),
                    ty: Ty::U64,
                    offset: Some(0),
                },
                FieldDef {
                    name: "b".into(),
                    ty: Ty::U64,
                    offset: Some(8),
                },
            ],
            size: Some(16),
            align: Some(8),

            repr: Default::default(),
        });

        let layout = module.ty_layout_shape(&Ty::Struct(sid)).unwrap();
        assert_eq!(layout.size_bits, 128);
        assert_eq!(layout.align_bits, Some(64));
        match layout.kind {
            TyLayoutKind::Struct { id, fields } => {
                assert_eq!(id, sid);
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[1].name, "b");
                assert_eq!(fields[1].offset_bits, Some(64));
            }
            other => panic!("expected struct layout, got {other:?}"),
        }
        assert_eq!(module.struct_field_offset_bits(sid, 1).unwrap(), 64);

        let u8_id = module.add_type(Ty::U8);
        let array = module.ty_layout_shape(&Ty::Array(u8_id, 4)).unwrap();
        assert_eq!(array.size_bits, 32);
        assert_eq!(array.align_bits, Some(8));
        assert_eq!(
            array.kind,
            TyLayoutKind::Array {
                elem: u8_id,
                len: 4,
                stride_bits: 8
            }
        );

        let vector = module
            .ty_layout_shape(&Ty::Vector(Box::new(Ty::I32), 4))
            .unwrap();
        assert_eq!(vector.size_bits, 128);
        assert_eq!(vector.align_bits, Some(32));
        assert_eq!(
            vector.kind,
            TyLayoutKind::Vector {
                elem_shape: TyShape::Int {
                    signed: true,
                    bits: 32
                },
                lanes: 4,
                lane_bits: 32
            }
        );
    }

    #[test]
    fn layout_sensitive_cast_evidence_covers_transmute_and_fn_reify() {
        let mut module = Module::new("casts");
        let sid = StructId::new(0);
        module.add_struct(StructDef {
            id: sid,
            name: "Pair".into(),
            fields: vec![
                FieldDef {
                    name: "a".into(),
                    ty: Ty::U64,
                    offset: Some(0),
                },
                FieldDef {
                    name: "b".into(),
                    ty: Ty::U64,
                    offset: Some(8),
                },
            ],
            size: Some(16),
            align: Some(8),

            repr: Default::default(),
        });
        let u64_id = module.add_type(Ty::U64);

        let evidence = module
            .layout_sensitive_cast_evidence(
                CastOp::Transmute,
                &Ty::Struct(sid),
                &Ty::Array(u64_id, 2),
            )
            .unwrap();
        assert_eq!(
            evidence,
            CastLayoutEvidence::SameSize {
                size_bits: 128,
                src_align_bits: Some(64),
                dst_align_bits: Some(64),
            }
        );

        let reify = module
            .layout_sensitive_cast_evidence(
                CastOp::ReifyFnPointer,
                &Ty::Func(FuncTyId::new(0)),
                &Ty::Ptr,
            )
            .unwrap();
        assert_eq!(
            reify,
            CastLayoutEvidence::ReifyFnPointer { pointer_bits: 64 }
        );

        let mismatch = module
            .layout_sensitive_cast_evidence(
                CastOp::PtrToPtr,
                &Ty::FatPtr(FatPtrKind::Str),
                &Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 7 }),
            )
            .unwrap_err();
        assert!(matches!(
            mismatch,
            LayoutError::PointerMetadataMismatch { .. }
        ));
    }

    #[test]
    fn constant_shape_matches_declared_type_without_string_parsing() {
        assert_eq!(
            Constant::Array(vec![Constant::Int(1)]).shape(),
            ConstantShape::Array { len: 1 }
        );
        assert!(
            Constant::Array(vec![Constant::Int(1)]).shape_matches_ty(&Ty::Array(TyId::new(0), 1))
        );
        assert_eq!(
            Constant::Vector(vec![Constant::Int(1), Constant::Int(2)]).shape(),
            ConstantShape::Vector { len: 2 }
        );
        assert!(
            Constant::Vector(vec![Constant::Int(1), Constant::Int(2)])
                .shape_matches_ty(&Ty::Vector(Box::new(Ty::I32), 2))
        );
        assert!(
            !Constant::Array(vec![Constant::Int(1), Constant::Int(2)])
                .shape_matches_ty(&Ty::Vector(Box::new(Ty::I32), 2))
        );
        assert!(Constant::FnDef(FuncId::new(3)).shape_matches_ty(&Ty::Func(FuncTyId::new(0))));
        assert!(Constant::PhantomData.shape_matches_ty(&Ty::Unit));
        assert_eq!(
            Constant::Closure {
                func: FuncId::new(2),
                captures: vec![Constant::Bool(true)]
            }
            .shape_label(),
            "closure<func.2>[1]"
        );
    }

    #[test]
    fn constant_value_match_range_checks_integer_width_and_signedness() {
        assert!(Constant::Int(255).value_matches_ty(&Ty::U8));
        assert!(!Constant::Int(256).value_matches_ty(&Ty::U8));
        assert!(!Constant::Int(-1).value_matches_ty(&Ty::U8));
        assert!(Constant::Int(-128).value_matches_ty(&Ty::I8));
        assert!(!Constant::Int(-129).value_matches_ty(&Ty::I8));
        assert!(Constant::Int(i128::MAX).value_matches_ty(&Ty::U128));
        assert!(!Constant::Int(-1).value_matches_ty(&Ty::U128));

        assert!(
            Constant::Vector(vec![Constant::Int(0), Constant::Int(255)])
                .value_matches_ty(&Ty::Vector(Box::new(Ty::U8), 2))
        );
        assert!(
            !Constant::Vector(vec![Constant::Int(0), Constant::Int(256)])
                .value_matches_ty(&Ty::Vector(Box::new(Ty::U8), 2))
        );
    }

    // --- canonical enum layout (tag + max payload) ---

    use crate::ty::{EnumDef, EnumTagRepr, EnumVariant};

    fn module_with_enum(ed: EnumDef) -> Module {
        let mut module = Module::new("enum-layout");
        module.add_enum(ed);
        module
    }

    fn option_i32_def(id: u32) -> EnumDef {
        EnumDef::new(
            EnumId::new(id),
            "OptionI32",
            vec![
                EnumVariant {
                    name: "None".into(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "Some".into(),
                    fields: vec![Ty::I32],
                    field_names: Vec::new(),
                },
            ],
        )
    }

    #[test]
    fn enum_layout_is_tag_plus_max_payload() {
        // Option<i32>-like: tag u8 @0, i32 payload aligned to 4 → payload at
        // byte 4, total 8 bytes, align 4.
        let module = module_with_enum(option_i32_def(0));
        let layout = module.enum_layout_shape(EnumId::new(0)).expect("layout");
        assert_eq!(layout.tag, EnumTagRepr::U8);
        assert_eq!(layout.tag_size_bits, 8);
        assert_eq!(layout.payload_offset_bits, 32);
        assert_eq!(layout.payload_size_bits, 32);
        assert_eq!(layout.size_bits, 64);
        assert_eq!(layout.align_bits, 32);
        assert_eq!(layout.discriminants, vec![0, 1]);

        // The generic `ty_layout_shape` agrees and reports the enum kind.
        let ty_layout = module.ty_layout_shape(&Ty::Enum(EnumId::new(0))).unwrap();
        assert_eq!(ty_layout.size_bits, 64);
        assert_eq!(ty_layout.align_bits, Some(32));
        assert_eq!(
            ty_layout.kind,
            TyLayoutKind::Enum {
                id: EnumId::new(0),
                variants: 2
            }
        );

        // A padded multi-field variant: (u8, u64) → variant size 16B align 8B;
        // tag u8 → payload at byte 8; total 24 bytes.
        let padded = module_with_enum(EnumDef::new(
            EnumId::new(0),
            "Padded",
            vec![
                EnumVariant {
                    name: "A".into(),
                    fields: vec![Ty::U8, Ty::U64],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "B".into(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
            ],
        ));
        let layout = padded.enum_layout_shape(EnumId::new(0)).expect("layout");
        assert_eq!(layout.tag_size_bits, 8);
        assert_eq!(layout.payload_offset_bits, 64);
        assert_eq!(layout.payload_size_bits, 128);
        assert_eq!(layout.size_bits, 192);
        assert_eq!(layout.align_bits, 64);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn legacy_enum_layout_shape_defaults_descriptor() {
        let module = module_with_enum(option_i32_def(0));
        let layout = module.enum_layout_shape(EnumId::new(0)).expect("layout");
        let mut json = serde_json::to_value(&layout).expect("serialize shape");
        json.as_object_mut()
            .expect("shape serializes as an object")
            .remove("descriptor");
        let decoded: EnumLayoutShape =
            serde_json::from_value(json).expect("legacy shape without descriptor");
        assert_eq!(decoded.descriptor, None);
        assert_eq!(decoded.size_bits, layout.size_bits);
    }

    #[test]
    fn enum_layout_honors_discriminants_and_repr_hint() {
        // An explicit 1000 forces a u16 tag: fieldless enum = 2 bytes.
        let wide = module_with_enum(
            EnumDef::new(
                EnumId::new(0),
                "Wide",
                vec![
                    EnumVariant {
                        name: "A".into(),
                        fields: vec![],
                        field_names: Vec::new(),
                    },
                    EnumVariant {
                        name: "B".into(),
                        fields: vec![],
                        field_names: Vec::new(),
                    },
                ],
            )
            .with_discriminants(vec![Some(1000)]),
        );
        let layout = wide.enum_layout_shape(EnumId::new(0)).expect("layout");
        assert_eq!(layout.tag, EnumTagRepr::U16);
        assert_eq!(layout.size_bits, 16);
        assert_eq!(layout.discriminants, vec![1000, 1001]);

        // A repr hint pins the tag wider than the values require.
        let hinted = module_with_enum(option_i32_def(0).with_repr(EnumTagRepr::U32));
        let layout = hinted.enum_layout_shape(EnumId::new(0)).expect("layout");
        assert_eq!(layout.tag, EnumTagRepr::U32);
        assert_eq!(layout.tag_size_bits, 32);
        assert_eq!(layout.payload_offset_bits, 32);
        assert_eq!(layout.size_bits, 64);
    }

    #[test]
    fn enum_layout_fails_closed() {
        // Missing definition.
        let empty_module = Module::new("no-enums");
        assert_eq!(
            empty_module.enum_layout_shape(EnumId::new(7)),
            Err(LayoutError::EnumLayoutUnavailable(EnumId::new(7)))
        );

        // Duplicate discriminants: no canonical assignment.
        let dup = module_with_enum(option_i32_def(0).with_discriminants(vec![Some(1), Some(1)]));
        assert_eq!(
            dup.enum_layout_shape(EnumId::new(0)),
            Err(LayoutError::EnumLayoutUnavailable(EnumId::new(0)))
        );

        // Uninhabited (zero-variant) enums have no layout, matching Never's
        // "no concrete memory layout" stance.
        let uninhabited = module_with_enum(EnumDef::new(EnumId::new(0), "Never", vec![]));
        assert_eq!(
            uninhabited.enum_layout_shape(EnumId::new(0)),
            Err(LayoutError::EnumLayoutUnavailable(EnumId::new(0)))
        );

        // A repr hint too narrow for the values.
        let narrow = module_with_enum(
            option_i32_def(0)
                .with_discriminants(vec![Some(300)])
                .with_repr(EnumTagRepr::U8),
        );
        assert_eq!(
            narrow.enum_layout_shape(EnumId::new(0)),
            Err(LayoutError::EnumLayoutUnavailable(EnumId::new(0)))
        );
    }

    #[test]
    fn enum_layout_guards_inline_self_reference() {
        // enum.0 carrying itself INLINE (not via a pointer) has no finite
        // layout — the guard must error, not recurse without bound.
        let cyclic = module_with_enum(EnumDef::new(
            EnumId::new(0),
            "Cyclic",
            vec![EnumVariant {
                name: "SelfRef".into(),
                fields: vec![Ty::Enum(EnumId::new(0))],
                field_names: Vec::new(),
            }],
        ));
        assert_eq!(
            cyclic.enum_layout_shape(EnumId::new(0)),
            Err(LayoutError::EnumLayoutUnavailable(EnumId::new(0)))
        );

        // The same recursion broken by a pointer is finite (the M2
        // Box-recursion shape): payload = one thin pointer.
        let boxed = module_with_enum(EnumDef::new(
            EnumId::new(0),
            "Boxed",
            vec![
                EnumVariant {
                    name: "Nil".into(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "Cons".into(),
                    fields: vec![Ty::Ptr],
                    field_names: Vec::new(),
                },
            ],
        ));
        let layout = boxed.enum_layout_shape(EnumId::new(0)).expect("layout");
        assert_eq!(layout.payload_size_bits, 64);
        assert_eq!(layout.size_bits, 128);
    }

    #[test]
    fn enum_aggregate_constant_shape_matches_enum_ty() {
        // The tag + payload constant convention is shape-admissible.
        assert!(
            Constant::Aggregate(vec![Constant::Int(1), Constant::Int(42)])
                .shape_matches_ty(&Ty::Enum(EnumId::new(0)))
        );
        // Non-aggregate constants still do not match an enum type.
        assert!(!Constant::Int(1).shape_matches_ty(&Ty::Enum(EnumId::new(0))));
    }
}
