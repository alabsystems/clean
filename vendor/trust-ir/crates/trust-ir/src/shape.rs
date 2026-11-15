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
use crate::value::{ClosureTyId, EnumId, StructId, TyId};

mod observed_constant_values;
mod observed_layout_error;
mod observed_layout_retirement;

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
    /// Nominal semantic type without a machine representation.
    Dialect,
    /// Nominal opaque runtime handle (v43): one pointer word, not pointer-like.
    Handle,
    Storage,
    /// A tensor (`Ty::Tensor`): no memory layout, as `Sequence` has none.
    /// Appended last so earlier serde discriminants stay.
    Tensor,
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
            TyShape::Dialect => f.write_str("dialect"),
            TyShape::Storage => f.write_str("storage"),
            TyShape::Handle => f.write_str("handle"),
            TyShape::Tensor => f.write_str("tensor"),
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
            Ty::Dialect(_) => TyShape::Dialect,
            Ty::Handle(_) => TyShape::Handle,
            Ty::Storage(_) => TyShape::Storage,
            Ty::Tensor(_, _) => TyShape::Tensor,
            Ty::Ext(e) => e.unreachable(),
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
    SliceLen {
        elem: TyId,
    },
    StrLen,
    VTable {
        trait_id: u32,
    },
    /// `usize` length metadata whose data pointer addresses a CONTAINER whose
    /// tail is the DST, not the DST content. See [`FatPtrKind::ContainerLen`].
    ContainerLen,
    /// Opaque VTABLE-word metadata whose data pointer addresses a CONTAINER
    /// whose tail is the `dyn`, not the dispatched object. NEVER a length, and
    /// no trait id: nothing dispatches through it. See
    /// [`FatPtrKind::ContainerVtable`].
    ContainerVtable,
}

impl core::fmt::Display for PointerMetadataShape {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            PointerMetadataShape::SliceLen { elem } => write!(f, "slice_len<ty.{}>", elem.0),
            PointerMetadataShape::StrLen => f.write_str("str_len"),
            PointerMetadataShape::VTable { trait_id } => write!(f, "vtable<dyn.{trait_id}>"),
            PointerMetadataShape::ContainerLen => f.write_str("container_len"),
            PointerMetadataShape::ContainerVtable => f.write_str("container_vtable"),
        }
    }
}

impl FatPtrKind {
    pub fn metadata_shape(&self) -> PointerMetadataShape {
        match *self {
            FatPtrKind::Slice(elem) => PointerMetadataShape::SliceLen { elem },
            FatPtrKind::Str => PointerMetadataShape::StrLen,
            FatPtrKind::TraitObject { trait_id } => PointerMetadataShape::VTable { trait_id },
            FatPtrKind::ContainerLen => PointerMetadataShape::ContainerLen,
            FatPtrKind::ContainerVtable => PointerMetadataShape::ContainerVtable,
        }
    }

    pub fn metadata_ty(&self, pointer_bits: u32) -> Option<Ty> {
        self.metadata_shape().metadata_ty(pointer_bits)
    }
}

impl PointerMetadataShape {
    pub fn metadata_ty(self, pointer_bits: u32) -> Option<Ty> {
        match self {
            // ContainerLen carries the SAME `usize` metadata as a slice or
            // str length -- the distinction is what the DATA pointer
            // addresses, not the metadata's type -- so the layout is
            // deliberately identical here and differs only in identity.
            PointerMetadataShape::SliceLen { .. }
            | PointerMetadataShape::StrLen
            | PointerMetadataShape::ContainerLen => pointer_sized_unsigned_ty(pointer_bits),
            // ContainerVtable carries the SAME opaque vtable word as a trait
            // object -- again the distinction is what the DATA pointer
            // addresses -- so it is `Ty::Ptr` here and must NEVER fall into
            // the unsigned-length arm above: a vtable word read as a length
            // is a type confusion, not a layout.
            PointerMetadataShape::VTable { .. } | PointerMetadataShape::ContainerVtable => {
                Some(Ty::Ptr)
            }
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
    Tuple {
        fields: Vec<FieldOffsetShape>,
    },
    /// A first-class closure's DECLARED environment frame (wire v58). Fields
    /// are the captures in CAPTURE order; their offsets are the producer's
    /// declared image, which `repr(Rust)` may have reordered.
    Closure {
        id: ClosureTyId,
        captures: Vec<FieldOffsetShape>,
    },
    /// Geometry only; no initialized value encoding exists.
    Storage,
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
            TyLayoutKind::Tuple { fields } => write!(f, "tuple<{} fields>", fields.len()),
            TyLayoutKind::Closure { id, captures } => {
                write!(f, "closure<{}, {} captures>", id.index(), captures.len())
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
            TyLayoutKind::Storage => f.write_str("storage"),
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
    MissingStructAlign(StructId),
    /// A declared struct layout contradicted its own size/alignment/offset
    /// evidence, or contained an inline recursive cycle with no finite size.
    StructLayoutIncoherent(StructId),
    TupleLayoutIncoherent(TyId),
    TupleLayoutTargetMissing,
    /// A declared closure layout (wire v58) contradicted its own
    /// size/alignment/offset evidence, named a closure type that does not
    /// resolve, or was one of two rows for one closure type.
    ClosureLayoutIncoherent(ClosureTyId),
    /// A declared closure layout needs the target's scalar layout to size its
    /// captures, exactly as a declared tuple layout does.
    ClosureLayoutTargetMissing,
    /// The module names a target whose scalar ABI alignment is not represented
    /// by TrustIR's built-in layout table. Size-only guesses are not layout
    /// evidence; layout-sensitive consumers must decline this target.
    /// Must-refuse corpus row `refuse/enum_tag_lane_off_scalar_table` (the
    /// enum-lane sibling, `EnumTagTargetScalarLayoutUnavailable`, on i686).
    TargetScalarLayoutUnavailable {
        triple: String,
    },
    MissingFieldOffset {
        struct_id: StructId,
        field: u32,
    },
    EnumLayoutUnavailable(EnumId),
    /// A `TyId` in the module type table refers to itself, directly or through
    /// a chain, with no pointer or nominal definition breaking the cycle
    /// (`types[0] = Array(ty.0, 4)`). Such a type has no finite layout.
    ///
    /// This is a SEPARATE defect from [`LayoutError::UnsupportedTyShape`]
    /// (a shape with no layout RULE) and from [`LayoutError::MissingType`]
    /// (a dangling index): the entry resolves and its shape is supported, and
    /// only the cycle makes it unlayoutable. Before this variant existed the
    /// two `TyId`-resolving arms had no cycle guard at all — the enum and
    /// struct arms did — so the walk recursed without bound and ABORTED the
    /// process on a stack overflow rather than returning an error.
    TyLayoutCycle(TyId),
    UnsupportedTyShape(TyShape),
    SizeOverflow,
    NotPointer(TyShape),
    /// v43: a layout-sensitive cast names an opaque runtime handle on either
    /// side. A handle is one pointer word, so a pure size comparison would
    /// ADMIT `Bitcast Ptr -> Handle`; this variant is what keeps the layout
    /// evidence from ever saying so. Refused before any width is compared.
    OpaqueHandleCast {
        src: TyShape,
        dst: TyShape,
    },
    /// A reinterpret cast (`Bitcast` / `Transmute`) has `bool` or a
    /// `<N x bool>` — a bool lane — stored by value on either side. A bool
    /// lane is one BIT of value ([`Ty::bit_width`], what the structural
    /// validator and the reference interpreter compare) in one BYTE of
    /// storage ([`Module::ty_layout_shape`], what this evidence compares), so
    /// the two same-size tests disagree by exactly bits-per-byte and admit
    /// opposite casts (`bitcast <8 x bool> -> u8` structurally, `-> u64` by
    /// layout) while the reference interpreter (`eval_bitcast`) and the Lean
    /// model (`semCast .Bitcast`) execute neither. Refused before any width
    /// is compared, as [`LayoutError::OpaqueHandleCast`] is. A pointer TO a
    /// bool lane is not a bool lane (its image is an address), and the
    /// identity cast is not a reinterpretation.
    BoolLaneReinterpret {
        src: TyShape,
        dst: TyShape,
    },
    /// v58: a layout-sensitive cast names a first-class closure BY VALUE on
    /// either side (directly, or inside an aggregate no pointer breaks). A
    /// closure value's bits are its captured environment, never a code
    /// address, and a declared frame (`Module.closure_layouts`) gives it a
    /// SIZE — which is exactly when a pure width comparison would start to
    /// ADMIT `Bitcast closure -> Ptr`, laundering the environment into a
    /// callee the closure-application rule cannot see. Refused before any
    /// width is compared, declared frame or not: the by-value application
    /// ruling (`lowering-target-subset.md` G18-2) names this as the rule the
    /// layout table must keep.
    ClosureCast {
        src: TyShape,
        dst: TyShape,
    },
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
            LayoutError::MissingStructAlign(id) => {
                write!(f, "struct.{} has no alignment layout metadata", id.0)
            }
            LayoutError::StructLayoutIncoherent(id) => {
                write!(f, "struct.{} has incoherent declared layout metadata", id.0)
            }
            LayoutError::TupleLayoutIncoherent(id) => {
                write!(
                    f,
                    "tuple layout ty.{} has incoherent or ambiguous declared metadata",
                    id.0
                )
            }
            LayoutError::TupleLayoutTargetMissing => {
                f.write_str("declared tuple layout requires target information")
            }
            LayoutError::ClosureLayoutIncoherent(id) => write!(
                f,
                "closure layout closure.{} has incoherent or ambiguous declared metadata",
                id.index()
            ),
            LayoutError::ClosureLayoutTargetMissing => {
                f.write_str("declared closure layout requires target information")
            }
            LayoutError::TargetScalarLayoutUnavailable { triple } => write!(
                f,
                "target {triple:?} is outside TrustIR's canonical scalar-layout set"
            ),
            LayoutError::MissingFieldOffset { struct_id, field } => write!(
                f,
                "struct.{} field {} has no offset layout metadata",
                struct_id.0, field
            ),
            LayoutError::EnumLayoutUnavailable(id) => {
                write!(f, "enum.{} has no concrete enum layout metadata", id.0)
            }
            LayoutError::TyLayoutCycle(id) => write!(
                f,
                "type table entry ty.{} is cyclic; a self-referential type has no finite layout",
                id.0
            ),
            LayoutError::UnsupportedTyShape(shape) => {
                write!(f, "{shape} has no concrete memory layout evidence")
            }
            LayoutError::SizeOverflow => f.write_str("layout size overflow"),
            LayoutError::NotPointer(shape) => write!(f, "{shape} is not pointer-like"),
            LayoutError::OpaqueHandleCast { src, dst } => write!(
                f,
                "{src} -> {dst}: an opaque runtime handle has no cast in or out; its only \
                 origins are its runtime's pinned entry points"
            ),
            LayoutError::BoolLaneReinterpret { src, dst } => write!(
                f,
                "{src} -> {dst}: a bool lane is one bit of value in one byte of storage, so \
                 no bit-image reinterpretation is defined for it (the reference interpreter \
                 and the Lean model both refuse it); spell int<->bool as trunc/zext and \
                 obtain a logical <N x bool> mask by comparing"
            ),
            LayoutError::ClosureCast { src, dst } => write!(
                f,
                "{src} -> {dst}: a first-class closure's bits are its captured environment, \
                 never a code address, and no cast reinterprets them, declared frame or not; \
                 apply it through CallIndirect at its closure type"
            ),
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

    /// Whether the target's scalar ABI alignment is exactly the table encoded
    /// by [`Module::ty_layout_shape`].
    ///
    /// TrustIR currently carries a triple and pointer width, not an LLVM/Rust
    /// data-layout string. The fixed table is exact for the architectures that
    /// TrustCg implements (plus its Wasm backend), but it is *not* exact for
    /// targets such as i686 (`f64` alignment 4) or AVR (wide integers alignment
    /// 1). Treating those as though alignment equalled scalar size manufactures
    /// false ABI evidence, so layout-sensitive queries fail closed instead.
    pub fn target_has_canonical_scalar_layout(&self) -> bool {
        let Some(target) = &self.target_info else {
            // Target-free TrustIR uses the documented canonical reference layout.
            return true;
        };
        let arch = target.triple.split('-').next().unwrap_or_default();
        match arch {
            "x86_64" | "x64" | "aarch64" | "arm64" | "wasm64" => target.pointer_size == 8,
            "wasm32" => target.pointer_size == 4,
            arch if arch.starts_with("riscv64") => target.pointer_size == 8,
            _ => false,
        }
    }

    /// The ALIGNMENT, in bytes, of an enum's tag lane on this module's target.
    ///
    /// The tag's **size** is a property of the repr alone
    /// ([`crate::EnumTagRepr::size_bytes`]); its **alignment** is a property of
    /// the TARGET, and the two are not the same fact. Every repr spellable
    /// today is naturally aligned on every target this table covers (the
    /// canonical set gives the v45 128-bit lanes rustc's 16, WS3.14(b)), so
    /// this returns the same number as `size_bytes` for all of them — but it
    /// returns it because the layout authority was ASKED, not because the byte
    /// count was reused. On a target outside the canonical scalar set the
    /// authority has no answer and this fails closed with
    /// [`LayoutError::TargetScalarLayoutUnavailable`]: an unknown ABI is not
    /// evidence that a declared tag offset is aligned.
    ///
    /// (WS2.22 review: an ABI may align an integer below its width — the i386
    /// System V ABI aligns `i64` to 4 — and rustc aligns `i128` to 16 on
    /// x86_64/aarch64 while other data layouts use 8. The validator, `shape`
    /// and the interpreter must therefore agree on where the alignment comes
    /// from before a 128-bit tag repr can exist; the interpreter already asked
    /// (`byte_align_in`), and this is the same question for the other two.)
    pub fn enum_tag_repr_align(&self, repr: crate::EnumTagRepr) -> Result<u64, LayoutError> {
        let ty = repr.ty();
        let align_bits = self
            .ty_layout_shape(&ty)?
            .align_bits
            .filter(|bits| *bits != 0 && bits.is_multiple_of(8))
            .ok_or_else(|| LayoutError::UnsupportedTyShape(ty.shape()))?;
        Ok(align_bits / 8)
    }

    /// Resolve by structural tuple identity, refusing aliases that carry two
    /// descriptors. Never choose the first of conflicting layout declarations.
    pub fn tuple_layout_descriptor(
        &self,
        ty: &Ty,
    ) -> Result<Option<&crate::TupleLayoutDescriptor>, LayoutError> {
        let mut found = None;
        for desc in &self.tuple_layouts {
            let declared = self
                .types
                .get(desc.tuple_type.as_usize())
                .ok_or(LayoutError::MissingType(desc.tuple_type))?;
            if !matches!(declared, Ty::Tuple(_)) {
                return Err(LayoutError::TupleLayoutIncoherent(desc.tuple_type));
            }
            if declared == ty {
                if found.is_some() {
                    return Err(LayoutError::TupleLayoutIncoherent(desc.tuple_type));
                }
                found = Some(desc);
            }
        }
        Ok(found)
    }

    /// Resolve the declared layout of `closure`, refusing two rows for one
    /// closure type. Never choose the first of conflicting declarations.
    pub fn closure_layout_descriptor(
        &self,
        closure: ClosureTyId,
    ) -> Result<Option<&crate::ClosureLayoutDescriptor>, LayoutError> {
        let mut found = None;
        for desc in &self.closure_layouts {
            if self.closure_type(desc.closure).is_none() {
                return Err(LayoutError::ClosureLayoutIncoherent(desc.closure));
            }
            if desc.closure == closure {
                if found.is_some() {
                    return Err(LayoutError::ClosureLayoutIncoherent(desc.closure));
                }
                found = Some(desc);
            }
        }
        Ok(found)
    }

    /// Check every declared closure layout, including unused rows. One
    /// [`crate::LayoutTable`] answers every row, as for
    /// [`Module::validate_tuple_layouts`].
    pub fn validate_closure_layouts(&self) -> Result<(), LayoutError> {
        self.layout_table().validate_closure_layouts()?;
        // Origin is producer data, never source authentication. As for nominal
        // aggregate origins, equal claims must nevertheless agree structurally,
        // including unused frames. A conflicting spelling cannot hide behind a
        // second closure arena index.
        let mut origins = std::collections::BTreeMap::new();
        for frame in &self.closure_layouts {
            let Some(origin) = &frame.origin else {
                continue;
            };
            let closure = self
                .closure_type(frame.closure)
                .ok_or(LayoutError::ClosureLayoutIncoherent(frame.closure))?;
            let signature = self.func_type(closure.func);
            if let Some((previous, captures, previous_function, previous_signature)) =
                origins.insert(origin, (frame, &closure.captures, closure.func, signature))
                && (previous.size != frame.size
                    || previous.align != frame.align
                    || previous.capture_offsets != frame.capture_offsets
                    || captures != &closure.captures
                    || previous_signature != signature
                    || (signature.is_none() && previous_function != closure.func))
            {
                return Err(LayoutError::ClosureLayoutIncoherent(frame.closure));
            }
        }
        Ok(())
    }

    /// Check every declaration, including unused rows and recursive interiors.
    /// One [`crate::LayoutTable`] answers every row, so this is O(total
    /// fields), not a walk per row; a caller that holds a table asks
    /// [`crate::LayoutTable::validate_tuple_layouts`] instead.
    pub fn validate_tuple_layouts(&self) -> Result<(), LayoutError> {
        self.layout_table().validate_tuple_layouts()
    }

    /// The layout of `ty`: its size, alignment and (for a struct or a
    /// declared tuple) its field offsets, or why it has none.
    ///
    /// Each call lays out what `ty` reaches through a fresh
    /// [`crate::LayoutTable`], each nominal node once, so it costs O(that
    /// reach). A caller with many questions about one module asks one table
    /// ([`Module::layout_table`]) instead, and the whole module costs O(total
    /// fields). Either way the walk is iterative: no depth limit.
    pub fn ty_layout_shape(&self, ty: &Ty) -> Result<TyLayoutShape, LayoutError> {
        if let Some(layout) = self.ty_leaf_layout(ty) {
            return layout;
        }
        crate::LayoutTable::new(self).ty_layout_shape(ty)
    }

    /// [`Module::ty_layout_shape`] for a type that names no other type by
    /// value (see [`leaf_layout`]); `None` for the seven that do.
    fn ty_leaf_layout(&self, ty: &Ty) -> Option<Result<TyLayoutShape, LayoutError>> {
        if ty_uses_scalar_layout_table(ty) && !self.target_has_canonical_scalar_layout() {
            return Some(Err(LayoutError::TargetScalarLayoutUnavailable {
                triple: self
                    .target_info
                    .as_ref()
                    .map_or_else(String::new, |target| target.triple.clone()),
            }));
        }
        leaf_layout(ty, self.pointer_bits())
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
    ///
    /// Lays out what the enum reaches through a fresh [`crate::LayoutTable`];
    /// see [`Module::ty_layout_shape`] for the cost and for asking many
    /// questions of one module.
    pub fn enum_layout_shape(&self, id: EnumId) -> Result<EnumLayoutShape, LayoutError> {
        crate::LayoutTable::new(self).enum_layout_shape(id)
    }

    pub fn struct_field_offset_bits(
        &self,
        struct_id: StructId,
        field: u32,
    ) -> Result<u64, LayoutError> {
        crate::LayoutTable::new(self).struct_field_offset_bits(struct_id, field)
    }

    /// Whether `ty` holds a first-class closure (`Ty::Closure`) BY VALUE:
    /// directly, or inside a tuple / array / vector / refinement / struct /
    /// enum / record that no pointer, reference or `Rc` breaks. A `Ref`,
    /// `RefMut`, raw pointer or `Rc` to a closure is an address whose bits are
    /// an address, so it is not held by value; a `Ty::Func` mentioning a
    /// closure in its signature is a code address. Named table references are
    /// followed, every definition of a duplicate id included, so a
    /// self-holding definition terminates.
    ///
    /// This is the closure counterpart of
    /// [`Module::type_reaches_handle`](crate::Module::type_reaches_handle)
    /// for the layout-sensitive cast rule; unlike the handle walk it stops at
    /// pointers, because the hazard is reinterpreting the environment's BYTES,
    /// not naming the type.
    ///
    /// Reachability, decided on the heap over one pass of each definition
    /// table it meets, so it costs O(the type's by-value reach plus those
    /// tables); a caller with
    /// many questions asks one [`crate::LayoutTable`]
    /// ([`crate::LayoutTable::type_holds_closure_by_value`]), which decides
    /// each node once (see `reach`'s module docs).
    #[must_use]
    pub fn type_contains_storage_by_value(&self, ty: &Ty) -> bool {
        self.layout_table().type_contains_storage_by_value(ty)
    }

    pub fn type_holds_closure_by_value(&self, ty: &Ty) -> bool {
        crate::reach::ReachMemo::default().reaches(self, crate::reach::Reach::ClosureByValue, ty)
    }

    /// Whether this type carries a `Char` by value, following the canonical
    /// Char-origin reachability rules. See [`crate::LayoutTable::type_contains_char_by_value`].
    #[must_use]
    pub fn type_contains_char_by_value(&self, ty: &Ty) -> bool {
        self.layout_table().type_contains_char_by_value(ty)
    }

    /// The layout evidence for a layout-sensitive cast, or why there is none.
    ///
    /// Lays out what the two types reach through a fresh
    /// [`crate::LayoutTable`]; a caller judging many casts of one module asks
    /// [`crate::LayoutTable::layout_sensitive_cast_evidence`] on one table.
    pub fn layout_sensitive_cast_evidence(
        &self,
        op: CastOp,
        src: &Ty,
        dst: &Ty,
    ) -> Result<CastLayoutEvidence, LayoutError> {
        self.layout_table()
            .layout_sensitive_cast_evidence(op, src, dst)
    }
}

impl crate::LayoutTable<'_> {
    /// [`Module::layout_sensitive_cast_evidence`], with the layouts answered
    /// from (and into) this table.
    pub fn layout_sensitive_cast_evidence(
        &self,
        op: CastOp,
        src: &Ty,
        dst: &Ty,
    ) -> Result<CastLayoutEvidence, LayoutError> {
        let module = self.module();
        if !op.is_layout_sensitive() {
            return Ok(CastLayoutEvidence::NotLayoutSensitive);
        }
        // v43: a handle occupies exactly one pointer word, so the size test
        // below would accept `Bitcast Ptr -> Handle` — the forgery the type
        // exists to make impossible. Refuse any handle side outright, before
        // any layout is compared.
        //
        // The predicate must FOLLOW table references, because the layout walk
        // below does. `Ty::contains_handle` inspects the inline spelling only,
        // so it answers `false` for `Refine(ty.0, _)` and `Array(ty.0, _)`
        // while `ty_layout_shape` resolves both to `Scalar(TyShape::Handle)`
        // at pointer width — measured: with the inline predicate,
        // `Bitcast Ptr -> Refine(ty.0=handle, _)` returned
        // `Ok(SameSize { size_bits: 64, .. })`. The validator's transport rule
        // does refuse such a node independently, but this function's OTHER
        // caller — `request::digest::validate_cast_fact` — has no transport
        // rule in front of it, and a matching `NativeCastFact` validated
        // clean, authenticating `Ptr -> handle` as a compiler fact.
        // `type_reaches_handle` is the targeted form of the module-aware
        // predicate the transport rule uses. Both callers query it inside a
        // per-node loop, so it is asked of this table's reachability memo:
        // each node is decided once per table, not walked again per cast
        // (and not by a whole-module `nominal_type_reachability()` build per
        // call either).
        if self.type_reaches_handle(src) || self.type_reaches_handle(dst) {
            return Err(LayoutError::OpaqueHandleCast {
                src: src.shape(),
                dst: dst.shape(),
            });
        }
        // v58: a closure with a DECLARED frame has a size, so the same-size
        // rule below would admit `Bitcast closure -> Ptr` / `Transmute closure
        // -> U64` — the laundering of a captured environment into a callee
        // that the closure-application rule cannot see. Refuse it here, before
        // any width is compared, whether or not a frame is declared, and
        // through any aggregate that holds the closure by value.
        if self.type_contains_storage_by_value(src) || self.type_contains_storage_by_value(dst) {
            return Err(LayoutError::UnsupportedTyShape(TyShape::Storage));
        }
        if self.type_holds_closure_by_value(src) || self.type_holds_closure_by_value(dst) {
            return Err(LayoutError::ClosureCast {
                src: src.shape(),
                dst: dst.shape(),
            });
        }

        match op {
            CastOp::PtrToPtr => {
                let pointer_bits = module.pointer_bits();
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
                // A bool lane's storage size (one byte per lane, compared
                // here) is not its value width (one bit per lane, compared by
                // the structural validator and the interpreter), so a size
                // test alone would admit `bitcast <8 x bool> -> u64` here
                // while the referee refuses it. Refuse by name first, following
                // by-value table references exactly as `ty_layout_shape` does.
                if src != dst
                    && (self.type_stores_bool_lane(src) || self.type_stores_bool_lane(dst))
                {
                    return Err(LayoutError::BoolLaneReinterpret {
                        src: src.shape(),
                        dst: dst.shape(),
                    });
                }
                let src_layout = self.ty_layout(src)?;
                let dst_layout = self.ty_layout(dst)?;
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
                let pointer_bits = module.pointer_bits();
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

impl Module {
    /// Whether `ty` STORES a bool lane by value in this module: `bool`
    /// itself, a `<N x bool>` at any vector nesting, or an array, tuple,
    /// struct, enum or refinement whose by-value closure reaches one —
    /// FOLLOWING named table references, because the layout walk does.
    /// Pointer edges are not followed: a pointer's byte image is an address
    /// whatever it points at, so `*const <8 x bool>` stores no bool lane.
    ///
    /// This is the family for which [`Ty::bit_width`] (one bit per lane) is
    /// not [`Module::ty_layout_shape`] (one byte per lane), so a same-size
    /// test between the two is meaningless for it; the reinterpret lane
    /// refuses it before any width is compared
    /// ([`LayoutError::BoolLaneReinterpret`]). The inline-only form is
    /// [`Ty::has_bool_lanes`]. Duplicate named ids contribute every matching
    /// definition (a duplicate id is itself a validation error, so this only
    /// widens a refusal on a module that is already rejected).
    ///
    /// Reachability, decided on the heap over one pass of each definition
    /// table it meets, so it costs O(the type's by-value reach plus those
    /// tables); a caller with many questions asks one [`crate::LayoutTable`]
    /// ([`crate::LayoutTable::type_stores_bool_lane`]).
    pub fn type_stores_bool_lane(&self, ty: &Ty) -> bool {
        crate::reach::ReachMemo::default().reaches(self, crate::reach::Reach::BoolLane, ty)
    }
}

pub(crate) fn ty_uses_scalar_layout_table(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Bool
            | Ty::I8
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
            | Ty::Ptr
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Rc(_)
            | Ty::Func(_)
            | Ty::FatPtr(_)
    )
}

fn scalar_layout(shape: TyShape, size_bits: u64, align_bits: Option<u64>) -> TyLayoutShape {
    TyLayoutShape {
        size_bits,
        align_bits,
        kind: TyLayoutKind::Scalar(shape),
    }
}

/// The layout of a type that names no other type by value — every `Ty` but
/// `Struct`, `Enum`, `Array`, `Vector`, `Tuple`, `Closure` and `Refine`, for which this
/// is `None` and [`crate::LayoutTable`] walks the type graph. The canonical
/// scalar table is assumed: the caller refuses a type
/// [`ty_uses_scalar_layout_table`] names on a target outside it first.
pub(crate) fn leaf_layout(
    ty: &Ty,
    pointer_bits: u32,
) -> Option<Result<TyLayoutShape, LayoutError>> {
    let int = |signed: bool, bits: u32| {
        Ok(scalar_layout(
            TyShape::Int { signed, bits },
            u64::from(bits),
            Some(u64::from(bits)),
        ))
    };
    let pointer_width = pointer_bits;
    let pointer_bits = u64::from(pointer_bits);
    Some(match ty {
        Ty::Bool => Ok(scalar_layout(TyShape::Bool, 8, Some(8))),
        Ty::I8 => int(true, 8),
        Ty::I16 => int(true, 16),
        Ty::I32 => int(true, 32),
        Ty::I64 => int(true, 64),
        Ty::I128 => int(true, 128),
        Ty::U8 => int(false, 8),
        Ty::U16 => int(false, 16),
        Ty::U32 => int(false, 32),
        Ty::U64 => int(false, 64),
        Ty::U128 => int(false, 128),
        // v25 B1 scalars: pointer-width ints take the target's pointer
        // width; char is a 32-bit scalar; Error has NO layout (typing
        // hole - fail closed).
        Ty::Isize => Ok(scalar_layout(
            TyShape::PointerInt { signed: true },
            pointer_bits,
            Some(pointer_bits),
        )),
        Ty::Usize => Ok(scalar_layout(
            TyShape::PointerInt { signed: false },
            pointer_bits,
            Some(pointer_bits),
        )),
        Ty::Char => int(false, 32),
        Ty::Error => Err(LayoutError::UnsupportedTyShape(TyShape::Error)),
        Ty::Dialect(_) => Err(LayoutError::UnsupportedTyShape(TyShape::Dialect)),
        // v43: a handle is one pointer-sized SCALAR word. Deliberately not
        // `TyLayoutKind::ThinPointer` — the layout says how many bytes it
        // occupies, never that anything may address through it.
        Ty::Storage(layout) => {
            if !layout.is_well_formed(pointer_width) {
                Err(LayoutError::UnsupportedTyShape(TyShape::Storage))
            } else {
                Ok(TyLayoutShape {
                    size_bits: layout.size_bytes * 8,
                    align_bits: Some(layout.align_bytes * 8),
                    kind: TyLayoutKind::Storage,
                })
            }
        }
        Ty::Handle(_) => Ok(scalar_layout(
            TyShape::Handle,
            pointer_bits,
            Some(pointer_bits),
        )),
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
            size_bits: pointer_bits,
            align_bits: Some(pointer_bits),
            kind: TyLayoutKind::ThinPointer,
        }),
        Ty::FatPtr(kind) => {
            let ptr = PointerLayoutShape::fat(pointer_width, kind.metadata_shape());
            match ptr.total_bits() {
                Some(total) => Ok(TyLayoutShape {
                    size_bits: u64::from(total),
                    align_bits: Some(pointer_bits),
                    kind: TyLayoutKind::FatPointer(kind.metadata_shape()),
                }),
                None => Err(LayoutError::SizeOverflow),
            }
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
        // A tensor's extents are run-time values (shape is a value, not a
        // type), so it has no memory layout, exactly as a sequence has none.
        Ty::Set(_, _) | Ty::Sequence(_) | Ty::Record(_) | Ty::Tensor(_, _) => {
            Err(LayoutError::UnsupportedTyShape(ty.shape()))
        }
        // v58: a closure lays out through its DECLARED frame, which names its
        // captures' types by value.
        Ty::Struct(_)
        | Ty::Enum(_)
        | Ty::Array(_, _)
        | Ty::Vector(_, _)
        | Ty::Tuple(_)
        | Ty::Closure(_)
        | Ty::Refine(_, _) => return None,
        Ty::Ext(e) => e.unreachable(),
    })
}

/// Round `offset_bits` up to the next multiple of `align_bits` (nonzero),
/// failing closed on arithmetic overflow.
pub(crate) fn align_up_bits(offset_bits: u64, align_bits: u64) -> Result<u64, LayoutError> {
    debug_assert!(align_bits > 0, "alignment must be nonzero");
    let rem = offset_bits % align_bits;
    if rem == 0 {
        return Ok(offset_bits);
    }
    offset_bits
        .checked_add(align_bits - rem)
        .ok_or(LayoutError::SizeOverflow)
}

/// Whether two byte ranges `(offset, size)` overlap: never when either is
/// empty, always when a nonempty range's end overflows, else when they
/// intersect.
pub fn byte_ranges_overlap(a_offset: u64, a_size: u64, b_offset: u64, b_size: u64) -> bool {
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

/// Whether some two of `ranges` (`(offset, size)` in bytes) overlap by
/// [`byte_ranges_overlap`] — the same answer as testing every pair, in
/// O(n log n) rather than O(n^2): an empty range overlaps nothing, a nonempty
/// range whose end overflows overlaps every other nonempty range, and
/// otherwise a sweep in offset order finds a range that starts before the
/// furthest end seen so far exactly when some pair overlaps.
pub fn any_byte_ranges_overlap(ranges: &[(u64, u64)]) -> bool {
    let mut spans = Vec::with_capacity(ranges.len());
    let mut overflowing = 0usize;
    for &(offset, size) in ranges {
        if size == 0 {
            continue;
        }
        match offset.checked_add(size) {
            Some(end) => spans.push((offset, end)),
            None => overflowing += 1,
        }
    }
    if overflowing > 0 {
        return overflowing + spans.len() >= 2;
    }
    spans.sort_unstable();
    let mut spans = spans.into_iter();
    let Some((_, mut reach)) = spans.next() else {
        return false;
    };
    for (start, end) in spans {
        if start < reach {
            return true;
        }
        reach = reach.max(end);
    }
    false
}

/// Every pair `(i, j)`, `i < j`, of `ranges` (`(offset, size)` in bytes)
/// that overlap by [`byte_ranges_overlap`], in `(i, j)` order — the pairs a
/// nested loop over `i` and then `j > i` would report, in its order — in
/// O(n log n + k) for `k` pairs: a nonempty range whose end overflows pairs
/// with every other nonempty range; the rest are swept in offset order,
/// each range pairing with the ranges still open at its start; the pairs are
/// then put in order by two counting passes.
pub fn overlapping_byte_range_pairs(ranges: &[(u64, u64)]) -> Vec<(usize, usize)> {
    use std::cmp::Reverse;
    use std::collections::BinaryHeap;

    let mut spans: Vec<(u64, u64, usize)> = Vec::with_capacity(ranges.len());
    let mut nonempty: Vec<usize> = Vec::with_capacity(ranges.len());
    let mut overflowing: Vec<usize> = Vec::new();
    let mut overflows = vec![false; ranges.len()];
    for (index, &(offset, size)) in ranges.iter().enumerate() {
        if size == 0 {
            continue;
        }
        nonempty.push(index);
        match offset.checked_add(size) {
            Some(end) => spans.push((offset, end, index)),
            None => {
                overflowing.push(index);
                overflows[index] = true;
            }
        }
    }
    let mut pairs: Vec<(usize, usize)> = Vec::new();
    let order = |a: usize, b: usize| if a < b { (a, b) } else { (b, a) };
    // An overflowing range overlaps every other nonempty range; a pair of two
    // overflowing ranges is reported once, from its lower index.
    for &wide in &overflowing {
        for &other in &nonempty {
            if other != wide && (other > wide || !overflows[other]) {
                pairs.push(order(wide, other));
            }
        }
    }
    spans.sort_unstable();
    // The ranges open at the sweep point, by end: every one still open when
    // a range starts overlaps it.
    let mut open: BinaryHeap<Reverse<(u64, usize)>> = BinaryHeap::new();
    for (start, end, index) in spans {
        while let Some(Reverse((open_end, _))) = open.peek() {
            if *open_end > start {
                break;
            }
            open.pop();
        }
        for Reverse((_, other)) in open.iter() {
            pairs.push(order(*other, index));
        }
        open.push(Reverse((end, index)));
    }
    // Two stable counting passes, by `j` and then by `i`: `(i, j)` order in
    // O(n + k).
    let counting_pass = |pairs: Vec<(usize, usize)>, key: fn(&(usize, usize)) -> usize| {
        let mut starts = vec![0usize; ranges.len() + 1];
        for pair in &pairs {
            starts[key(pair) + 1] += 1;
        }
        for index in 1..starts.len() {
            starts[index] += starts[index - 1];
        }
        let mut sorted = vec![(0, 0); pairs.len()];
        for pair in pairs {
            let slot = &mut starts[key(&pair)];
            sorted[*slot] = pair;
            *slot += 1;
        }
        sorted
    };
    let pairs = counting_pass(pairs, |pair| pair.1);
    counting_pass(pairs, |pair| pair.0)
}

impl Module {
    /// Is `ty` **uninhabited** — provably without any value?
    ///
    /// WS3.14 (F-056). The predicate is deliberately SOUND rather than
    /// complete: `true` is a claim that grants an exemption (an uninhabited
    /// enum variant needs no niche encoding), so it answers `true` only when
    /// the structural rules below derive it in finitely many steps (the
    /// least solution of the rules read as equations over the nominal nodes,
    /// see the `inhabit` module):
    ///
    /// * `Ty::Never`;
    /// * an enum every one of whose variants is uninhabited (a zero-variant
    ///   enum included);
    /// * a struct, record or tuple with at least one uninhabited field;
    /// * a NON-EMPTY array of an uninhabited element (`[!; 0]` has a value);
    /// * a refinement of an uninhabited base.
    ///
    /// Everything else — pointers and references to `!` included, which rustc
    /// also treats as inhabited for layout — answers `false`. A nominal id that
    /// does not resolve answers `false`, and so does a by-value cycle that
    /// derives nothing (`struct S { s: S }`): an unresolvable question is
    /// treated as "inhabited", which keeps every check that the exemption
    /// would skip. A nominal id with several same-id definitions (a module the
    /// validator refuses, but the interpreter may be handed unvalidated) is
    /// uninhabited only when EVERY definition says so.
    ///
    /// The answer is order-independent and costs O(what `ty` reaches), on a
    /// heap stack. A caller with many questions asks one
    /// [`crate::LayoutTable`] ([`crate::LayoutTable::ty_is_uninhabited`]),
    /// which decides each node once.
    pub fn ty_is_uninhabited(&self, ty: &Ty) -> bool {
        crate::inhabit::InhabitMemo::default().ty_is_uninhabited(self, ty)
    }

    /// Is this enum `variant` **uninhabited** — does some field of it have no
    /// value (see [`Module::ty_is_uninhabited`])?
    ///
    /// rustc gives such a variant no encoding in a niche layout
    /// (`enum E { A(char), B(!), C }` reserves one niche value, for `C` only),
    /// so the niche-coverage rule counts INHABITED variants only. A value of an
    /// uninhabited variant can never exist: constructing one is refused by the
    /// validator, and decoding a byte image that names one is refused by the
    /// interpreter.
    pub fn variant_is_uninhabited(&self, variant: &crate::ty::EnumVariant) -> bool {
        crate::inhabit::InhabitMemo::default().variant_is_uninhabited(self, variant)
    }

    /// The niche-coverage rule, shared by the validator, `shape` and the
    /// interpreter: the index of the first INHABITED variant of `def` that a
    /// niche encoding leaves without an encoding — neither the untagged
    /// variant nor inside `niche_variants_start..=niche_variants_end` — or
    /// `None` when every inhabited variant is encoded.
    ///
    /// An uninhabited variant may be the untagged variant, lie in the niche
    /// interval, or lie in neither: it never has a value to encode. The caller
    /// still checks, separately, that both indices and the interval are in
    /// range and ordered. One inhabitedness memo serves every variant, so the
    /// rule costs O(what the variants reach), each node decided once.
    pub fn niche_unencoded_inhabited_variant(
        &self,
        def: &crate::ty::EnumDef,
        untagged_variant: u32,
        niche_variants_start: u32,
        niche_variants_end: u32,
    ) -> Option<usize> {
        crate::inhabit::InhabitMemo::default().niche_unencoded_inhabited_variant(
            self,
            def,
            untagged_variant,
            niche_variants_start,
            niche_variants_end,
        )
    }
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
    /// v50: `len` copies of one element (`Constant::Splat`). The length is
    /// the declared `u64`, never a materialized count.
    Splat {
        len: u64,
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
    /// Crystal lane (E3b, v49): an unwritten struct/tuple lane (`Constant::Uninit`).
    Uninit,
    /// v70: a content-addressed tensor (`Constant::TensorBlob`) of `rank`
    /// extents.
    TensorBlob {
        rank: usize,
    },
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
            ConstantShape::Splat { len } => write!(f, "splat[{len}]"),
            ConstantShape::Vector { len } => write!(f, "vector[{len}]"),
            ConstantShape::Sequence { len } => write!(f, "sequence[{len}]"),
            ConstantShape::Set { len } => write!(f, "set[{len}]"),
            ConstantShape::Record { fields } => write!(f, "record[{fields}]"),
            ConstantShape::Closure { captures } => write!(f, "closure[{captures}]"),
            ConstantShape::FnDef => f.write_str("fndef"),
            ConstantShape::SymbolAddr => f.write_str("symaddr"),
            ConstantShape::PhantomData => f.write_str("phantomdata"),
            ConstantShape::Uninit => f.write_str("uninit"),
            ConstantShape::TensorBlob { rank } => write!(f, "tensor_blob[{rank}]"),
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
            Constant::Splat { len, .. } => ConstantShape::Splat { len: *len },
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
            Constant::Uninit => ConstantShape::Uninit,
            Constant::TensorBlob { dims, .. } => ConstantShape::TensorBlob { rank: dims.len() },
            Constant::Ext(e) => e.unreachable(),
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
            // scalars; the Unicode range is checked by int_value_fits_ty, i.e.
            // by `value_matches_ty`).
            (Constant::Int(_), Ty::Char) => true,
            // v24: a canonical U128 (value > i128::MAX) only fits the U128
            // type - never a narrower integer, never a pointer (fail closed).
            (Constant::U128(_), Ty::U128) => true,
            // v25 Bytes: a byte-array payload — fits a same-length Array
            // (element-type U8-ness needs the module table and is checked by
            // validate_constant_against_ty, same split as Array constants).
            (Constant::Bytes { data, .. }, Ty::Array(_, n)) => *n == data.len() as u64,
            // Trust (wave-FS): a NULL FAT POINTER — `(data, metadata)` both zero — is the
            // only `Ty::FatPtr` constant admitted, and it is admitted ZERO-ONLY. A `&str` /
            // `&[T]` / `&dyn Tr` leaf inside an aggregate seed has no other representable
            // originator: `Inst::Const` is the sole way to originate an aggregate, and before
            // this arm the intersection of the two authorities was EMPTY (no `Ty::FatPtr` arm
            // here, none in `constant_to_value`, and the interpreter's `(_, PhantomData)`
            // wildcard is not an escape because THIS function's `PhantomData` arm is
            // `Ty::Unit`-only). A NONZERO data word would fabricate an address with no
            // provenance and must stay a type error, exactly as the landed
            // `(Ty::Ptr, Constant::Int(0)) -> NullPtr` precedent is zero-only.
            //
            // WS3.8 (F-049): the NON-NULL `&str` / `&[T]` spelling
            // `[SymbolAddr { G, addend: k }, Int(n)]` is admitted, but NOT here: it is
            // a window of one immutable module array global, and only the
            // module-table-aware walk (`trust-ir-build` `validate_constant_against_ty`)
            // can check `G`. This table-free authority keeps refusing it.
            (Constant::Aggregate(elems), Ty::FatPtr(_)) => {
                matches!(elems.as_slice(), [Constant::Int(0), Constant::Int(0)])
            }
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
            // v50: a splat fits an array of EXACTLY its length; its element's
            // typing needs the module table and is checked by
            // `validate_constant_against_ty` (the same split as `Array`).
            (Constant::Splat { len, .. }, Ty::Array(_, n)) => len == n,
            // v70: a content-addressed tensor fits an integer tensor of its
            // rank. Whether its row exists and holds `∏ dims × width/8` bytes
            // needs the module's blob table, and where it may stand (only the
            // whole value of an `Inst::Const`) is `trust-ir-build`'s
            // `InvalidTensorBlob` rule.
            (Constant::TensorBlob { dims, .. }, Ty::Tensor(elem, rank)) => {
                elem.is_integer() && u64::try_from(dims.len()).is_ok_and(|n| n == u64::from(*rank))
            }
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
            // WS3.8 (F-049): `SymbolAddr { symbol, addend: 0 }` at `Ref(T)` /
            // `PtrConst(T)` / `PtrMut(T)` is admitted by the module-table-aware walk
            // (it must name one module-defined global of type `T`), never here.
            (Constant::SymbolAddr { .. }, Ty::Ptr) => true,
            (Constant::SymbolAddr { .. }, Ty::Func(_)) => true,
            (Constant::PhantomData, Ty::Unit) => true,
            // Crystal lane (E3b): `Constant::Uninit` matches NO type on its own. It stands only as a
            // direct lane of a struct/tuple aggregate constant, where the arms above accept the
            // aggregate without inspecting its lanes, and trust-ir-build's placement rule is
            // what admits it there. A bare `uninit` at any type falls through to `false`.
            _ => false,
        }
    }

    /// Return true when this constant is a value of the declared type on a
    /// target whose thin pointers are `pointer_bits` wide.
    ///
    /// This is stricter than [`Constant::shape_matches_ty`]: an integer
    /// constant is range-checked against the signedness and the width of its
    /// type, and nested vector lanes are checked with a stack-safe borrowed
    /// walk. Scalar and unary-vector paths allocate no traversal scratch;
    /// branching retains O(vector depth) sibling iterators, not O(vector
    /// width) lanes. `Constant::Int` is an `i128` payload, so `Ty::U128`
    /// accepts only the non-negative subset that the payload can represent.
    ///
    /// THE WIDTH IS A PARAMETER, never a default: `isize` / `usize` are
    /// `pointer_bits` wide, so on wasm32 (`pointer_bits = 32`) `2^32` is no
    /// `usize` — it is the 64-bit spelling of `0`, which the reference
    /// interpreter, executing `usize` at 32 bits there, would wrap to `0`. A
    /// module-aware caller passes [`Module::pointer_bits`] (the target's
    /// width, and the documented 64-bit default for a target-free module); the
    /// validator's constant funnel and a verification bundle's const generic
    /// arguments do (`docs/SPEC_RATIFICATIONS.md` §3.3). A consumer MUST refuse
    /// a pointer-width constant outside its target's range
    /// (`refuse/const_usize_beyond_target_width`).
    pub fn value_matches_ty(&self, ty: &Ty, pointer_bits: u32) -> bool {
        let mut pending: Vec<(core::slice::Iter<'_, Constant>, &Ty)> = Vec::new();
        let (mut value, mut ty) = (self, ty);
        loop {
            let matches = match (value, ty) {
                (Constant::Int(integer), ty) if ty.is_integer() => {
                    int_value_fits_ty(*integer, ty, pointer_bits)
                }
                // Char is not an integer type; its integer constants still
                // require Unicode-scalar range validation.
                (Constant::Int(integer), Ty::Char) => {
                    int_value_fits_ty(*integer, &Ty::Char, pointer_bits)
                }
                // Canonical integer spelling is a separate check, preserving
                // the existing local-shape behavior for hand-built U128s.
                (Constant::U128(_), Ty::U128) => true,
                (Constant::Bytes { data, .. }, Ty::Array(_, n)) => *n == data.len() as u64,
                (Constant::Vector(elements), Ty::Vector(element_ty, lanes)) => {
                    if elements.len() != *lanes as usize {
                        return false;
                    }
                    let mut children = elements.iter();
                    if let Some(first) = children.next() {
                        if children.len() != 0 {
                            pending.push((children, element_ty));
                        }
                        value = first;
                        ty = element_ty;
                        continue;
                    }
                    true
                }
                _ => value.shape_matches_ty(ty),
            };
            if !matches {
                return false;
            }
            let Some((siblings, element_ty)) = pending.last_mut() else {
                return true;
            };
            value = siblings.next().expect("only nonempty lanes are suspended");
            ty = *element_ty;
            if siblings.len() == 0 {
                pending.pop();
            }
        }
    }
}

/// Whether `value` is a value of the integer (or `char`) type `ty` when
/// pointer-width integers are `pointer_bits` wide. ONE rule for every integer
/// width: the width is [`Ty::bit_width_with`]'s — the width the layout tables
/// and the reference interpreter (`int_shape_at`) execute the type at — and
/// the range is that width's signed or unsigned range. `char` is a Unicode
/// scalar value (`0..=0x10FFFF` minus the surrogates).
fn int_value_fits_ty(value: i128, ty: &Ty, pointer_bits: u32) -> bool {
    if matches!(ty, Ty::Char) {
        return (0..=0x10FFFF).contains(&value) && !(0xD800..=0xDFFF).contains(&value);
    }
    if !ty.is_integer() {
        return false;
    }
    ty.bit_width_with(pointer_bits)
        .is_some_and(|bits| int_value_fits_bits(value, bits, ty.is_signed()))
}

/// Whether `value` lies in the `bits`-wide signed (`-2^(bits-1) ..
/// 2^(bits-1)`) or unsigned (`0 .. 2^bits`) range. A width of 0 or above 128
/// holds nothing (fail closed); 128 bits holds every non-negative `i128` as
/// an unsigned value and every `i128` as a signed one.
fn int_value_fits_bits(value: i128, bits: u32, signed: bool) -> bool {
    match (bits, signed) {
        (1..=127, true) => {
            let half = 1i128 << (bits - 1);
            (-half..half).contains(&value)
        }
        (1..=127, false) => value >= 0 && value >> bits == 0,
        (128, true) => true,
        (128, false) => value >= 0,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ty::{EnumDef, EnumVariant, FatPtrKind, FieldDef, SetRepr, StructDef, StructRepr};
    use crate::value::{ClosureTyId, EnumId, FuncId, FuncTyId, PredId, StructId, TyId};
    use crate::{Endianness, Module, TargetInfo};

    #[test]
    fn null_fat_pointer_constant_is_admitted_zero_only() {
        // Trust (wave-FS): the ONLY `Ty::FatPtr` constant is the null fat pointer, and it is
        // admitted zero-only — the same discipline as the landed
        // `(Constant::Int(0), Ty::Ptr)` arm, and for the same reason: a nonzero data word
        // would fabricate an address with no provenance.
        let zero = || Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0)]);
        for kind in [
            FatPtrKind::Str,
            FatPtrKind::Slice(TyId::new(0)),
            FatPtrKind::TraitObject { trait_id: 7 },
            FatPtrKind::ContainerLen,
            FatPtrKind::ContainerVtable,
        ] {
            assert!(
                zero().shape_matches_ty(&Ty::FatPtr(kind)),
                "the null fat pointer must fit every fat-pointer kind",
            );
        }

        // NONZERO in either word is a type error, not a fabricated pointer.
        for bad in [
            Constant::Aggregate(vec![Constant::Int(1), Constant::Int(0)]),
            Constant::Aggregate(vec![Constant::Int(0), Constant::Int(1)]),
            Constant::Aggregate(vec![Constant::Int(1), Constant::Int(1)]),
        ] {
            assert!(
                !bad.shape_matches_ty(&Ty::FatPtr(FatPtrKind::Str)),
                "a nonzero fat-pointer word must stay a type error",
            );
        }

        // WRONG ARITY is a type error too: a fat pointer is exactly (data, metadata).
        for bad in [
            Constant::Aggregate(vec![]),
            Constant::Aggregate(vec![Constant::Int(0)]),
            Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0), Constant::Int(0)]),
        ] {
            assert!(
                !bad.shape_matches_ty(&Ty::FatPtr(FatPtrKind::Str)),
                "a fat pointer is exactly two words",
            );
        }

        // And the arm must not leak into the THIN pointer type, whose own constant is
        // `Constant::Int(0)` and never an aggregate.
        assert!(!zero().shape_matches_ty(&Ty::Ptr));
    }

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
    fn a_tensor_has_its_own_shape_and_no_memory_layout() {
        assert_eq!(TyShape::Tensor.to_string(), "tensor");
        let module = Module::new("tensor-layout");
        for tensor in [
            Ty::Tensor(Box::new(Ty::I32), 2),
            Ty::Tensor(Box::new(Ty::U8), 0),
        ] {
            assert_eq!(tensor.shape(), TyShape::Tensor);
            assert_eq!(
                module.ty_layout_shape(&tensor),
                Err(LayoutError::UnsupportedTyShape(TyShape::Tensor))
            );
        }
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

    /// v43: no layout-sensitive cast admits a handle on either side, even
    /// though a handle and a thin pointer lay out identically.
    #[test]
    fn layout_sensitive_casts_refuse_opaque_handles_before_comparing_widths() {
        let module = Module::new("handle-cast");
        let handle = Ty::handle("Nat", "trust_bignum::Nat");
        // Same size and alignment as Ptr — the hazard.
        let handle_layout = module.ty_layout_shape(&handle).unwrap();
        let ptr_layout = module.ty_layout_shape(&Ty::Ptr).unwrap();
        assert_eq!(handle_layout.size_bits, ptr_layout.size_bits);
        assert_eq!(handle_layout.align_bits, ptr_layout.align_bits);
        assert!(matches!(
            handle_layout.kind,
            TyLayoutKind::Scalar(TyShape::Handle)
        ));
        for op in [CastOp::Bitcast, CastOp::Transmute, CastOp::PtrToPtr] {
            for (src, dst) in [(&Ty::Ptr, &handle), (&handle, &Ty::Ptr), (&handle, &handle)] {
                assert!(
                    matches!(
                        module.layout_sensitive_cast_evidence(op, src, dst),
                        Err(LayoutError::OpaqueHandleCast { .. })
                    ),
                    "{op:?} {src} -> {dst}"
                );
            }
            // Wrapped occurrences are refused too.
            let boxed = Ty::Tuple(vec![handle.clone()]);
            assert!(matches!(
                module.layout_sensitive_cast_evidence(op, &boxed, &boxed),
                Err(LayoutError::OpaqueHandleCast { .. })
            ));
        }
        // The control: Ptr -> Ptr is still fine.
        assert!(
            module
                .layout_sensitive_cast_evidence(CastOp::Bitcast, &Ty::Ptr, &Ty::Ptr)
                .is_ok()
        );
    }

    /// The guard must follow TABLE references, because the layout walk it
    /// guards does. Regression: it tested `Ty::contains_handle`, which is
    /// documented as inline-only, so every spelling that reaches the handle
    /// through `Module.types` escaped it and the width test then admitted the
    /// forgery — `Bitcast Ptr -> Refine(ty.0 = handle, _)` returned
    /// `Ok(SameSize { size_bits: 64, .. })`, a pointer bit-reinterpreted as
    /// an opaque runtime handle. Inside `validate_module` the transport rule
    /// refuses such a node independently; `request::digest::validate_cast_fact`
    /// has nothing in front of it (see the bundle test
    /// `native_bundle_rejects_a_cast_fact_forging_a_table_backed_handle`).
    #[test]
    fn layout_sensitive_casts_refuse_handles_reached_through_the_type_table() {
        let mut module = Module::new("table-backed-handle-cast");
        module.types.push(Ty::handle("Nat", "trust_bignum::Nat"));
        module.types.push(Ty::I64);

        // The hazard is that each of these lays out as ONE POINTER WORD, the
        // same width as `Ty::Ptr`, so a width comparison cannot tell them
        // apart. Each reaches the handle only through `ty.0`.
        let table_backed = [
            Ty::Refine(TyId::new(0), PredId::new(0)),
            Ty::Array(TyId::new(0), 1),
            Ty::Sequence(TyId::new(0)),
            Ty::Set(TyId::new(0), SetRepr::Boxed),
            Ty::FatPtr(FatPtrKind::Slice(TyId::new(0))),
            Ty::Ref(Box::new(Ty::Array(TyId::new(0), 1))),
        ];
        for ty in &table_backed {
            assert!(
                !ty.contains_handle(),
                "{ty} must be a TABLE-backed spelling for this test to bite"
            );
            assert!(
                module.type_reaches_handle(ty),
                "the module-aware predicate must see through the table: {ty}"
            );
            for op in [CastOp::Bitcast, CastOp::Transmute, CastOp::PtrToPtr] {
                for (src, dst) in [(&Ty::Ptr, ty), (ty, &Ty::Ptr)] {
                    assert!(
                        matches!(
                            module.layout_sensitive_cast_evidence(op, src, dst),
                            Err(LayoutError::OpaqueHandleCast { .. })
                        ),
                        "{op:?} {src} -> {dst} escaped the handle guard"
                    );
                }
            }
        }

        // Through a named STRUCT field, and through an ENUM variant field.
        module.structs.push(StructDef {
            id: StructId::new(0),
            name: "Wrapper".into(),
            fields: vec![FieldDef {
                name: "inner".into(),
                ty: Ty::handle("Nat", "trust_bignum::Nat"),
                offset: Some(0),
            }],
            size: Some(8),
            align: Some(8),
            repr: StructRepr::Rust,
            origin: None,
        });
        module.enums.push(EnumDef::new(
            EnumId::new(0),
            "Either",
            vec![EnumVariant {
                name: "Some".into(),
                fields: vec![Ty::Struct(StructId::new(0))],
                field_names: Vec::new(),
            }],
        ));
        for ty in [Ty::Struct(StructId::new(0)), Ty::Enum(EnumId::new(0))] {
            assert!(!ty.contains_handle());
            assert!(module.type_reaches_handle(&ty), "{ty}");
            assert!(matches!(
                module.layout_sensitive_cast_evidence(CastOp::Bitcast, &Ty::Ptr, &ty),
                Err(LayoutError::OpaqueHandleCast { .. })
            ));
        }

        // A table reference that does NOT reach a handle is still admitted, so
        // the guard has not degenerated into refusing every table-backed type.
        let handle_free = Ty::Array(TyId::new(1), 1);
        assert!(!module.type_reaches_handle(&handle_free));
        assert!(
            module
                .layout_sensitive_cast_evidence(CastOp::Bitcast, &handle_free, &handle_free)
                .is_ok()
        );
        // And a table CYCLE terminates instead of recursing forever.
        module.types.push(Ty::Array(TyId::new(2), 1));
        assert!(!module.type_reaches_handle(&Ty::Array(TyId::new(2), 1)));
    }

    #[test]
    fn scalar_layout_evidence_declines_targets_outside_the_canonical_table() {
        let mut i686 = Module::new("i686-layout");
        i686.target_info = Some(TargetInfo {
            triple: "i686-unknown-linux-gnu".into(),
            pointer_size: 4,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        });
        assert!(matches!(
            i686.ty_layout_shape(&Ty::F64),
            Err(LayoutError::TargetScalarLayoutUnavailable { triple })
                if triple == "i686-unknown-linux-gnu"
        ));

        // Empty aggregate evidence does not consult a scalar table and remains
        // available even on an otherwise unsupported target.
        i686.add_struct(StructDef {
            id: StructId::new(0),
            name: "Empty".into(),
            fields: vec![],
            size: Some(0),
            align: Some(1),
            repr: crate::ty::StructRepr::C,
            origin: None,
        });
        assert!(i686.ty_layout_shape(&Ty::Struct(StructId::new(0))).is_ok());

        let mut wasm = Module::new("wasm-layout");
        wasm.target_info = Some(TargetInfo {
            triple: "wasm32-unknown-unknown".into(),
            pointer_size: 4,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        });
        assert_eq!(wasm.ty_layout_shape(&Ty::F64).unwrap().align_bits, Some(64));
        assert_eq!(wasm.ty_layout_shape(&Ty::Ptr).unwrap().align_bits, Some(32));

        let mut forged_x86_64 = Module::new("forged-x86-64-layout");
        forged_x86_64.target_info = Some(TargetInfo {
            triple: "x86_64-unknown-linux-gnu".into(),
            pointer_size: 4,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        });
        assert!(matches!(
            forged_x86_64.ty_layout_shape(&Ty::Ptr),
            Err(LayoutError::TargetScalarLayoutUnavailable { triple })
                if triple == "x86_64-unknown-linux-gnu"
        ));
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
            origin: None,
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

        let u8_id = module
            .add_type(Ty::U8)
            .expect("Module::add_type: test fixture");
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

    fn module_with_declared_struct(
        fields: Vec<FieldDef>,
        size: u64,
        align: u64,
        repr: crate::ty::StructRepr,
    ) -> Module {
        let mut module = Module::new("declared-struct-shape");
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "S".into(),
            fields,
            size: Some(size),
            align: Some(align),
            repr,
            origin: None,
        });
        module
    }

    #[test]
    fn struct_shape_revalidates_declared_layout_before_exporting_it() {
        let field = |name: &str, ty: Ty, offset: Option<u64>| FieldDef {
            name: name.into(),
            ty,
            offset,
        };
        let incoherent = |module: &Module| {
            matches!(
                module.ty_layout_shape(&Ty::Struct(StructId::new(0))),
                Err(LayoutError::StructLayoutIncoherent(id)) if id == StructId::new(0)
            )
        };

        let misaligned = module_with_declared_struct(
            vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(3))],
            16,
            8,
            crate::ty::StructRepr::C,
        );
        assert!(incoherent(&misaligned));
        assert!(matches!(
            misaligned.struct_field_offset_bits(StructId::new(0), 1),
            Err(LayoutError::StructLayoutIncoherent(_))
        ));

        let overlap = module_with_declared_struct(
            vec![field("a", Ty::U64, Some(0)), field("b", Ty::U32, Some(4))],
            16,
            8,
            crate::ty::StructRepr::C,
        );
        assert!(incoherent(&overlap));

        let packed_bad_clamp = module_with_declared_struct(
            vec![field("value", Ty::U64, Some(0))],
            8,
            1,
            crate::ty::StructRepr::Packed(3),
        );
        assert!(incoherent(&packed_bad_clamp));

        let packed_overaligned = module_with_declared_struct(
            vec![field("value", Ty::U64, Some(0))],
            8,
            8,
            crate::ty::StructRepr::Packed(1),
        );
        assert!(incoherent(&packed_overaligned));

        let packed_control = module_with_declared_struct(
            vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(3))],
            11,
            1,
            crate::ty::StructRepr::Packed(1),
        );
        let layout = packed_control
            .ty_layout_shape(&Ty::Struct(StructId::new(0)))
            .expect("packed(1) makes byte 3 coherent");
        assert_eq!(layout.size_bits, 88);
        assert_eq!(
            packed_control.struct_field_offset_bits(StructId::new(0), 1),
            Ok(24)
        );

        let missing_sized = module_with_declared_struct(
            vec![field("value", Ty::U64, None)],
            8,
            8,
            crate::ty::StructRepr::C,
        );
        assert!(matches!(
            missing_sized.ty_layout_shape(&Ty::Struct(StructId::new(0))),
            Err(LayoutError::MissingFieldOffset {
                struct_id,
                field: 0
            }) if struct_id == StructId::new(0)
        ));

        let missing_zst = module_with_declared_struct(
            vec![field("zst", Ty::Unit, None)],
            0,
            1,
            crate::ty::StructRepr::C,
        );
        assert_eq!(
            missing_zst.struct_field_offset_bits(StructId::new(0), 0),
            Ok(0)
        );
    }

    #[test]
    fn struct_shape_enforces_the_exact_transparent_carrier_layout() {
        let field = |name: &str, ty: Ty, offset: Option<u64>| FieldDef {
            name: name.into(),
            ty,
            offset,
        };
        let incoherent = |module: &Module, id: u32| {
            matches!(
                module.ty_layout_shape(&Ty::Struct(StructId::new(id))),
                Err(LayoutError::StructLayoutIncoherent(found)) if found == StructId::new(id)
            )
        };

        let shifted_carrier = module_with_declared_struct(
            vec![field("value", Ty::U64, Some(8))],
            16,
            8,
            crate::ty::StructRepr::Transparent,
        );
        assert!(incoherent(&shifted_carrier, 0));

        let two_carriers = module_with_declared_struct(
            vec![
                field("left", Ty::U32, Some(0)),
                field("right", Ty::U32, Some(4)),
            ],
            8,
            4,
            crate::ty::StructRepr::Transparent,
        );
        assert!(incoherent(&two_carriers, 0));

        let ordinary = module_with_declared_struct(
            vec![
                field("value", Ty::U64, Some(0)),
                field("marker", Ty::Unit, None),
            ],
            8,
            8,
            crate::ty::StructRepr::Transparent,
        );
        assert_eq!(
            ordinary
                .ty_layout_shape(&Ty::Struct(StructId::new(0)))
                .expect("one carrier plus a 1-ZST is transparent")
                .size_bits,
            64
        );

        // A zero-sized field with alignment greater than one is the carrier;
        // size-only counting would wrongly call both fields trivial.
        let mut overaligned = Module::new("transparent-overaligned-zst");
        overaligned.add_struct(StructDef {
            id: StructId::new(0),
            name: "Marker".into(),
            fields: vec![],
            size: Some(0),
            align: Some(8),
            repr: crate::ty::StructRepr::Rust,
            origin: None,
        });
        overaligned.add_struct(StructDef {
            id: StructId::new(1),
            name: "Wrapper".into(),
            fields: vec![
                field("marker", Ty::Struct(StructId::new(0)), Some(0)),
                field("unit", Ty::Unit, None),
            ],
            size: Some(0),
            align: Some(8),
            repr: crate::ty::StructRepr::Transparent,
            origin: None,
        });
        let layout = overaligned
            .ty_layout_shape(&Ty::Struct(StructId::new(1)))
            .expect("an over-aligned ZST can be the sole transparent carrier");
        assert_eq!(layout.size_bits, 0);
        assert_eq!(layout.align_bits, Some(64));
    }

    /// The overlap sweep answers what testing every pair answered, including
    /// empty ranges (overlap nothing) and a range whose end overflows (overlaps
    /// every other nonempty range).
    #[test]
    fn the_overlap_sweep_is_the_pairwise_test() {
        let pairwise = |ranges: &[(u64, u64)]| {
            (0..ranges.len()).any(|left| {
                (left + 1..ranges.len()).any(|right| {
                    byte_ranges_overlap(
                        ranges[left].0,
                        ranges[left].1,
                        ranges[right].0,
                        ranges[right].1,
                    )
                })
            })
        };
        let mut state = 0x0bad_5eed_u64;
        let mut next = |n: u64| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state % n
        };
        let (mut overlapping, mut disjoint) = (0, 0);
        for _ in 0..50_000 {
            let len = next(7) as usize;
            let ranges: Vec<(u64, u64)> = (0..len)
                .map(|_| match next(12) {
                    0 => (u64::MAX - next(4), next(6)),
                    1 => (next(40), 0),
                    _ => (next(40), next(9)),
                })
                .collect();
            let expected = pairwise(&ranges);
            assert_eq!(any_byte_ranges_overlap(&ranges), expected, "{ranges:?}");
            if expected {
                overlapping += 1;
            } else {
                disjoint += 1;
            }
        }
        assert!(overlapping > 1_000 && disjoint > 1_000);
    }

    #[test]
    fn the_overlapping_pairs_are_the_nested_loops_pairs_in_its_order() {
        let nested = |ranges: &[(u64, u64)]| {
            let mut pairs = Vec::new();
            for left in 0..ranges.len() {
                for right in left + 1..ranges.len() {
                    if byte_ranges_overlap(
                        ranges[left].0,
                        ranges[left].1,
                        ranges[right].0,
                        ranges[right].1,
                    ) {
                        pairs.push((left, right));
                    }
                }
            }
            pairs
        };
        let mut state = 0x5ca1_ab1e_u64;
        let mut next = |n: u64| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state % n
        };
        let (mut pairs_seen, mut with_overflow, mut none) = (0usize, 0usize, 0usize);
        for _ in 0..50_000 {
            let len = next(11) as usize;
            let ranges: Vec<(u64, u64)> = (0..len)
                .map(|_| match next(14) {
                    0 => (u64::MAX - next(4), next(6)),
                    1 => (next(40), 0),
                    2 => (7, 3),
                    _ => (next(40), next(9)),
                })
                .collect();
            let expected = nested(&ranges);
            assert_eq!(
                overlapping_byte_range_pairs(&ranges),
                expected,
                "{ranges:?}"
            );
            assert_eq!(any_byte_ranges_overlap(&ranges), !expected.is_empty());
            pairs_seen += expected.len();
            if ranges
                .iter()
                .any(|(offset, size)| *size > 0 && offset.checked_add(*size).is_none())
            {
                with_overflow += 1;
            }
            none += usize::from(expected.is_empty());
        }
        assert!(pairs_seen > 50_000 && with_overflow > 1_000 && none > 1_000);
        // Wide: n ranges with k = n - 1 overlaps (a chain), and n disjoint.
        let n = 100_000u64;
        let chain: Vec<(u64, u64)> = (0..n).map(|i| (i, 2)).collect();
        let pairs = overlapping_byte_range_pairs(&chain);
        assert_eq!(pairs.len() as u64, n - 1);
        assert!(pairs.iter().all(|(left, right)| right - left == 1));
        let disjoint: Vec<(u64, u64)> = (0..n).rev().map(|i| (i, 1)).collect();
        assert!(overlapping_byte_range_pairs(&disjoint).is_empty());
    }

    #[test]
    fn struct_shape_refuses_an_inline_recursive_cycle() {
        let recursive = module_with_declared_struct(
            vec![FieldDef {
                name: "self".into(),
                ty: Ty::Struct(StructId::new(0)),
                offset: Some(0),
            }],
            8,
            8,
            crate::ty::StructRepr::Rust,
        );
        assert!(matches!(
            recursive.ty_layout_shape(&Ty::Struct(StructId::new(0))),
            Err(LayoutError::StructLayoutIncoherent(id)) if id == StructId::new(0)
        ));
    }

    /// The struct and enum arms had a cycle guard; the two arms that resolve a
    /// `TyId` through the module type table did NOT, so a self-referential
    /// entry recursed without bound and ABORTED the process on a stack
    /// overflow. Measured 2026-08-31: 60 corpus files SIGSEGV'd under the
    /// producer's validate_module tripwire (192 bodies lost, `modules_invalid`
    /// left unmeasurable) — a walk that crashes cannot be promoted to a gate.
    ///
    /// Written as a CONTRAST: a cyclic array must be refused as a CYCLE, while
    /// the same shape over a real element must still lay out. Refusing both
    /// would "fix" the crash by making the arm useless.
    #[test]
    fn array_shape_refuses_a_ty_table_cycle_but_still_lays_out_a_real_element() {
        let mut cyclic = Module::new("cyclic-array");
        cyclic.types.push(Ty::Array(TyId::new(0), 4));
        let seed = cyclic.types[0].clone();
        assert!(matches!(
            cyclic.ty_layout_shape(&seed),
            Err(LayoutError::TyLayoutCycle(id)) if id == TyId::new(0)
        ));

        let mut sound = Module::new("sound-array");
        let elem = sound
            .add_type(Ty::U32)
            .expect("Module::add_type: test fixture");
        assert_eq!(
            sound
                .ty_layout_shape(&Ty::Array(elem, 4))
                .expect("an array of u32 has a layout")
                .size_bits,
            128
        );
    }

    /// The cycle need not be direct: `ty.0 -> ty.1 -> ty.0` is the same defect,
    /// and a guard that only compared against the immediately-enclosing id
    /// would miss it. The reported id is the one whose re-entry closed the
    /// cycle, so the message names a real table entry either way.
    #[test]
    fn array_shape_refuses_an_indirect_ty_table_cycle() {
        let mut module = Module::new("indirect-cycle");
        module.types.push(Ty::Array(TyId::new(1), 2));
        module.types.push(Ty::Array(TyId::new(0), 2));
        let seed = module.types[0].clone();
        assert!(matches!(
            module.ty_layout_shape(&seed),
            Err(LayoutError::TyLayoutCycle(_))
        ));
    }

    /// `Refine` delegates to its base for layout (representation preservation),
    /// which is exactly what makes a self-referential base unbounded. It is
    /// refused as a CYCLE, distinct from the `UnsupportedTyShape(Refine)` a
    /// DANGLING base id already produced — two different defects with two
    /// different owners.
    #[test]
    fn refine_shape_refuses_a_self_referential_base() {
        let mut module = Module::new("cyclic-refine");
        module
            .types
            .push(Ty::Refine(TyId::new(0), crate::value::PredId::new(0)));
        let seed = module.types[0].clone();
        assert!(matches!(
            module.ty_layout_shape(&seed),
            Err(LayoutError::TyLayoutCycle(id)) if id == TyId::new(0)
        ));
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
            origin: None,
        });
        let u64_id = module
            .add_type(Ty::U64)
            .expect("Module::add_type: test fixture");

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
        let at = |c: Constant, ty: Ty| c.value_matches_ty(&ty, DEFAULT_POINTER_BITS);
        assert!(at(Constant::Int(255), Ty::U8));
        assert!(!at(Constant::Int(256), Ty::U8));
        assert!(!at(Constant::Int(-1), Ty::U8));
        assert!(at(Constant::Int(-128), Ty::I8));
        assert!(!at(Constant::Int(-129), Ty::I8));
        assert!(at(Constant::Int(i128::MAX), Ty::U128));
        assert!(!at(Constant::Int(-1), Ty::U128));
        assert!(at(Constant::Int(i128::MIN), Ty::I128));

        assert!(at(
            Constant::Vector(vec![Constant::Int(0), Constant::Int(255)]),
            Ty::Vector(Box::new(Ty::U8), 2)
        ));
        assert!(!at(
            Constant::Vector(vec![Constant::Int(0), Constant::Int(256)]),
            Ty::Vector(Box::new(Ty::U8), 2)
        ));
    }

    /// The fixed-width table the range rule replaced, kept as the oracle:
    /// every fixed-width integer type's range is the same at every pointer
    /// width, and equals its Rust type's `MIN..=MAX`.
    #[test]
    fn fixed_width_integer_ranges_are_their_rust_types_at_every_pointer_width() {
        let cells: [(Ty, i128, i128); 10] = [
            (Ty::I8, i8::MIN.into(), i8::MAX.into()),
            (Ty::I16, i16::MIN.into(), i16::MAX.into()),
            (Ty::I32, i32::MIN.into(), i32::MAX.into()),
            (Ty::I64, i64::MIN.into(), i64::MAX.into()),
            (Ty::I128, i128::MIN, i128::MAX),
            (Ty::U8, 0, u8::MAX.into()),
            (Ty::U16, 0, u16::MAX.into()),
            (Ty::U32, 0, u32::MAX.into()),
            (Ty::U64, 0, u64::MAX.into()),
            (Ty::U128, 0, i128::MAX),
        ];
        for pointer_bits in [8, 16, 32, 64] {
            for (ty, lo, hi) in &cells {
                for (value, fits) in [
                    (*lo, true),
                    (*hi, true),
                    (lo.saturating_sub(1), *lo == i128::MIN),
                    (hi.saturating_add(1), *hi == i128::MAX),
                ] {
                    assert_eq!(
                        Constant::Int(value).value_matches_ty(ty, pointer_bits),
                        fits,
                        "{ty} {value} at {pointer_bits}-bit pointers"
                    );
                }
            }
        }
    }

    /// `isize` / `usize` have the pointer's width: each end of the range at
    /// 8, 16, 32 and 64 bits fits, one past either end does not, and a width
    /// no target has (0, or above 128) holds nothing.
    #[test]
    fn pointer_width_integer_ranges_follow_the_pointer_width() {
        for bits in [8u32, 16, 32, 64] {
            let half = 1i128 << (bits - 1);
            let full = 1i128 << bits;
            for (ty, value, fits) in [
                (Ty::Usize, 0, true),
                (Ty::Usize, full - 1, true),
                (Ty::Usize, full, false),
                (Ty::Usize, -1, false),
                (Ty::Isize, -half, true),
                (Ty::Isize, half - 1, true),
                (Ty::Isize, half, false),
                (Ty::Isize, -half - 1, false),
            ] {
                assert_eq!(
                    Constant::Int(value).value_matches_ty(&ty, bits),
                    fits,
                    "{ty} {value} at {bits}-bit pointers"
                );
            }
        }
        // The documented default is the 64-bit reference width.
        assert!(Constant::Int((1 << 32) - 1).value_matches_ty(&Ty::Usize, DEFAULT_POINTER_BITS));
        assert!(Constant::Int(1 << 32).value_matches_ty(&Ty::Usize, DEFAULT_POINTER_BITS));
        assert!(!Constant::Int(1 << 32).value_matches_ty(&Ty::Usize, 32));
        // A vector lane is checked at the same width (the validator refuses
        // a pointer-width vector type; the range rule still answers).
        let lanes = Ty::Vector(Box::new(Ty::Usize), 2);
        let pair = Constant::Vector(vec![Constant::Int(0), Constant::Int(1 << 32)]);
        assert!(pair.value_matches_ty(&lanes, 64));
        assert!(!pair.value_matches_ty(&lanes, 32));
        for bits in [0, 129, u32::MAX] {
            assert!(
                !Constant::Int(0).value_matches_ty(&Ty::Usize, bits),
                "{bits}"
            );
            assert!(
                !Constant::Int(0).value_matches_ty(&Ty::Isize, bits),
                "{bits}"
            );
        }
        // `char` is a Unicode scalar value at every pointer width.
        for bits in [16, 32, 64] {
            assert!(Constant::Int(0x10FFFF).value_matches_ty(&Ty::Char, bits));
            assert!(!Constant::Int(0xD800).value_matches_ty(&Ty::Char, bits));
        }
    }

    #[test]
    fn nested_vector_value_matching_is_stack_safe_and_range_faithful() {
        let mut valid = Constant::Int(255);
        let mut invalid = Constant::Int(256);
        let mut ty = Ty::U8;
        for _ in 0..100_000 {
            valid = Constant::Vector(vec![valid]);
            invalid = Constant::Vector(vec![invalid]);
            ty = Ty::Vector(Box::new(ty), 1);
        }
        // Constant/Ty Drop are not made iterative by this local shape change.
        let valid = Box::leak(Box::new(valid));
        let invalid = Box::leak(Box::new(invalid));
        let ty = Box::leak(Box::new(ty));
        assert!(valid.value_matches_ty(ty, DEFAULT_POINTER_BITS));
        assert!(!invalid.value_matches_ty(ty, DEFAULT_POINTER_BITS));
    }

    #[test]
    fn nested_vector_value_matching_checks_all_lanes_and_preserves_shallow_fallbacks() {
        let ty = Ty::Vector(Box::new(Ty::Vector(Box::new(Ty::U8), 2)), 2);
        let valid = Constant::Vector(vec![
            Constant::Vector(vec![Constant::Int(0), Constant::Int(255)]),
            Constant::Vector(vec![Constant::Int(10), Constant::Int(20)]),
        ]);
        assert!(valid.value_matches_ty(&ty, DEFAULT_POINTER_BITS));
        let last_invalid = Constant::Vector(vec![
            Constant::Vector(vec![Constant::Int(0), Constant::Int(255)]),
            Constant::Vector(vec![Constant::Int(10), Constant::Int(256)]),
        ]);
        assert!(!last_invalid.value_matches_ty(&ty, DEFAULT_POINTER_BITS));
        assert!(
            !Constant::Vector(vec![Constant::Vector(vec![Constant::Int(0)])])
                .value_matches_ty(&ty, DEFAULT_POINTER_BITS)
        );
        assert!(
            Constant::Vector(vec![])
                .value_matches_ty(&Ty::Vector(Box::new(Ty::Bool), 0), DEFAULT_POINTER_BITS)
        );

        // These checks remain local: table-backed aggregate element validation
        // and canonical integer spelling are separate existing responsibilities.
        assert!(
            Constant::Vector(vec![Constant::Array(vec![Constant::Bool(true)])]).value_matches_ty(
                &Ty::Vector(Box::new(Ty::Array(TyId(0), 99)), 1),
                DEFAULT_POINTER_BITS
            )
        );
        assert!(
            Constant::Vector(vec![Constant::U128(0)])
                .value_matches_ty(&Ty::Vector(Box::new(Ty::U128), 1), DEFAULT_POINTER_BITS)
        );
    }

    #[test]
    fn wide_nested_vector_value_matching_streams_siblings_and_checks_last_lane() {
        let mut lanes: Vec<_> = (0..100_000)
            .map(|_| Constant::Vector(vec![Constant::Int(255)]))
            .collect();
        let ty = Ty::Vector(
            Box::new(Ty::Vector(Box::new(Ty::U8), 1)),
            lanes.len() as u32,
        );
        assert!(Constant::Vector(lanes.clone()).value_matches_ty(&ty, DEFAULT_POINTER_BITS));
        *lanes.last_mut().expect("last lane") = Constant::Vector(vec![Constant::Int(256)]);
        assert!(!Constant::Vector(lanes).value_matches_ty(&ty, DEFAULT_POINTER_BITS));
    }

    // --- canonical enum layout (tag + max payload) ---

    use crate::ty::EnumTagRepr;

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

#[cfg(test)]
mod container_len_layout_tests {
    use super::*;
    use crate::FatPtrKind;

    /// The defect this variant exists to close: a fat pointer signed as an
    /// anonymous `(ptr, i64)` tuple has NO layout, because `ty_layout_shape`
    /// covers the empty tuple only. Everything transitively containing one
    /// became unresolvable, and the enum-layout validator failed closed.
    ///
    /// Asserted as a CONTRAST so the test states the whole point: the tuple
    /// spelling does not resolve, the first-class kind does.
    #[test]
    fn container_len_resolves_where_the_tuple_spelling_does_not() {
        let m = Module::new("container_len_layout");

        let tuple = Ty::Tuple(vec![Ty::Ptr, Ty::I64]);
        assert!(
            m.ty_layout_shape(&tuple).is_err(),
            "the tuple spelling is expected to have NO layout — if this starts \
             resolving, the motivation for FatPtrKind::ContainerLen changed and \
             this test should be the thing that says so"
        );

        let fat = Ty::FatPtr(FatPtrKind::ContainerLen);
        let shape = m
            .ty_layout_shape(&fat)
            .expect("ContainerLen must resolve — that is the entire point");

        // Same bytes as a str-length fat pointer: two pointer-sized words. The
        // kinds differ in what the DATA pointer addresses, never in layout.
        let str_shape = m
            .ty_layout_shape(&Ty::FatPtr(FatPtrKind::Str))
            .expect("Str fat pointer resolves");
        assert_eq!(
            shape.size_bytes(),
            str_shape.size_bytes(),
            "ContainerLen must lay out exactly like Str"
        );
        assert_eq!(shape.align_bits, str_shape.align_bits);
    }

    /// The identity half. Layout equality above must NOT become identity
    /// equality: a container-tail pointer is not a string pointer, and the
    /// metadata shapes are what downstream consumers switch on.
    #[test]
    fn container_len_is_not_str() {
        assert_ne!(
            FatPtrKind::ContainerLen.metadata_shape(),
            FatPtrKind::Str.metadata_shape(),
            "sharing a metadata shape with Str would re-encode the very claim \
             the variant exists to avoid making"
        );
    }

    /// v41, the vtable twin. Same CONTRAST shape as the two tests above: the
    /// layout must match a plain trait-object fat pointer exactly, and the
    /// identity must NOT.
    #[test]
    fn container_vtable_lays_out_like_a_trait_object_but_is_not_one() {
        let m = Module::new("container_vtable_layout");

        let container = m
            .ty_layout_shape(&Ty::FatPtr(FatPtrKind::ContainerVtable))
            .expect("ContainerVtable must resolve — that is the entire point");
        let dyn_shape = m
            .ty_layout_shape(&Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 7 }))
            .expect("trait-object fat pointer resolves");

        assert_eq!(
            container.size_bytes(),
            dyn_shape.size_bytes(),
            "ContainerVtable must lay out exactly like a trait object"
        );
        assert_eq!(container.align_bits, dyn_shape.align_bits);

        assert_ne!(
            FatPtrKind::ContainerVtable.metadata_shape(),
            FatPtrKind::TraitObject { trait_id: 7 }.metadata_shape(),
            "sharing a metadata shape with TraitObject would assert the data \
             pointer addresses the trait object, which is the false claim this \
             variant exists to avoid making"
        );
    }

    /// The OTHER near-miss spelling, and the one v38 alone would have invited:
    /// `ContainerLen` gets the container claim right but carries pointer-sized
    /// LENGTH metadata. A consumer switching on the metadata shape would read
    /// a `usize` where a vtable pointer lives.
    #[test]
    fn container_vtable_metadata_is_a_pointer_not_a_length() {
        assert_eq!(
            FatPtrKind::ContainerVtable.metadata_ty(64),
            Some(Ty::Ptr),
            "vtable metadata is a pointer"
        );
        assert_eq!(
            FatPtrKind::ContainerLen.metadata_ty(64),
            Some(Ty::U64),
            "length metadata is a pointer-sized unsigned"
        );
        assert_ne!(
            FatPtrKind::ContainerVtable.metadata_shape(),
            FatPtrKind::ContainerLen.metadata_shape(),
        );
    }
}

#[cfg(test)]
mod container_vtable_layout_tests {
    use super::*;
    use crate::FatPtrKind;

    /// The defect this variant exists to close, as a CONTRAST: the producer's
    /// fail-closed spelling for a pointer-to-`dyn`-tailed-container was
    /// `Ty::Unit`, which is not a pointer at all -- no metadata, no lanes, so
    /// nothing declared over it had a coherent size. The first-class kind is
    /// a two-lane fat pointer that lays out EXACTLY like a trait object.
    #[test]
    fn container_vtable_lays_out_exactly_like_trait_object() {
        let m = Module::new("container_vtable_layout");
        let bits = m.pointer_bits();

        let fail_closed = Ty::Unit;
        assert_eq!(
            fail_closed.pointer_metadata_ty(bits),
            None,
            "the fail-closed spelling is not pointer-like -- if this changes, \
             the motivation for FatPtrKind::ContainerVtable changed and this \
             test should be the thing that says so"
        );

        let fat = Ty::FatPtr(FatPtrKind::ContainerVtable);
        let dyn_ptr = Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 7 });

        let shape = m
            .ty_layout_shape(&fat)
            .expect("ContainerVtable must resolve -- that is the entire point");
        let dyn_shape = m
            .ty_layout_shape(&dyn_ptr)
            .expect("TraitObject fat pointer resolves");
        assert_eq!(
            shape.size_bytes(),
            dyn_shape.size_bytes(),
            "ContainerVtable must lay out exactly like TraitObject"
        );
        assert_eq!(shape.align_bits, dyn_shape.align_bits);
        // Two pointer words: 16 bytes / align 8 on the 64-bit default target.
        assert_eq!(bits, 64);
        assert_eq!(shape.size_bytes(), Some(16));
        assert_eq!(shape.align_bits, Some(64));

        let lanes = fat
            .pointer_layout_shape(bits)
            .expect("ContainerVtable is a fat pointer");
        let dyn_lanes = dyn_ptr.pointer_layout_shape(bits).unwrap();
        assert_eq!(lanes.lane_count(), 2);
        assert_eq!(lanes.data_bits, dyn_lanes.data_bits);
        assert_eq!(lanes.metadata_bits, dyn_lanes.metadata_bits);
        assert_eq!(lanes.total_bits(), dyn_lanes.total_bits());
        assert_eq!(
            format!("{lanes}"),
            "fat(data=64b, metadata=container_vtable:64b)"
        );
    }

    /// The metadata half. It is the OPAQUE VTABLE WORD -- the same `Ty::Ptr`
    /// a trait object carries -- and NEVER the unsigned length the slice-side
    /// kinds carry. Reading it as a length would be a type confusion.
    #[test]
    fn container_vtable_metadata_is_the_vtable_word_never_a_length() {
        for bits in [32u32, 64] {
            let vtable_word = FatPtrKind::TraitObject { trait_id: 7 }.metadata_ty(bits);
            assert_eq!(vtable_word, Some(Ty::Ptr));
            assert_eq!(
                FatPtrKind::ContainerVtable.metadata_ty(bits),
                vtable_word,
                "ContainerVtable metadata must be the vtable word at {bits} bits"
            );
            assert_ne!(
                FatPtrKind::ContainerVtable.metadata_ty(bits),
                FatPtrKind::ContainerLen.metadata_ty(bits),
                "ContainerVtable must not carry the length word ContainerLen does"
            );
        }
        assert_eq!(
            FatPtrKind::ContainerVtable.metadata_shape(),
            PointerMetadataShape::ContainerVtable
        );
    }

    /// The identity half. Layout equality must NOT become identity equality:
    /// a container-tail pointer is not a trait-object pointer (it addresses
    /// the container header and dispatches nothing), and it is not the
    /// slice-side container kind either. The metadata shapes are what
    /// downstream consumers switch on.
    #[test]
    fn container_vtable_is_neither_trait_object_nor_container_len() {
        for trait_id in [0u32, 7, u32::MAX] {
            assert_ne!(
                FatPtrKind::ContainerVtable.metadata_shape(),
                FatPtrKind::TraitObject { trait_id }.metadata_shape(),
                "sharing a metadata shape with TraitObject would re-encode the \
                 dispatch claim the variant exists to avoid making"
            );
        }
        assert_ne!(
            FatPtrKind::ContainerVtable.metadata_shape(),
            FatPtrKind::ContainerLen.metadata_shape()
        );
        assert_eq!(
            format!("{}", Ty::FatPtr(FatPtrKind::ContainerVtable)),
            "fatptr<container_vtable>"
        );
    }
}
