// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::value::{ClosureTyId, EnumId, FuncTyId, PredId, RecordId, StructId, TyId};

/// Representation hint for `Ty::Set`.
///
/// Small-scalar sets (e.g. `Set(U8)`) can be lowered as bitsets when the
/// universe is bounded; unbounded or recursive element types fall through to
/// a boxed runtime representation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum SetRepr {
    /// Flat bitset lowering (small bounded scalar elements).
    Bitset,
    /// Boxed runtime container (hash set / sorted vec). Default conservative
    /// choice; frontends may refine to `Bitset` when they can prove the
    /// universe is small and dense.
    #[default]
    Boxed,
}

impl core::fmt::Display for SetRepr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            SetRepr::Bitset => "bitset",
            SetRepr::Boxed => "boxed",
        })
    }
}

/// Runtime shape of a Rust wide/fat pointer.
///
/// A fat pointer is represented as `(data_ptr, metadata)` where metadata is
/// length for slices/`str` and a vtable-like descriptor for trait objects.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum FatPtrKind {
    Slice(TyId),
    Str,
    TraitObject { trait_id: u32 },
}

impl core::fmt::Display for FatPtrKind {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            FatPtrKind::Slice(elem) => write!(f, "slice ty.{}", elem.0),
            FatPtrKind::Str => f.write_str("str"),
            FatPtrKind::TraitObject { trait_id } => write!(f, "dyn.{trait_id}"),
        }
    }
}

/// The canonical `FatPtrKind::TraitObject { trait_id }` mint (B2-3).
///
/// `trait_id` is a CONTENT-derived identity, never a positional/interned one:
/// every frontend derives it as `stable_trait_object_id` of the principal
/// trait's def-path string, so two modules — or two producers of the *same*
/// module, like a frontend/oracle differential pair — that name the same
/// trait always sign the same id, and body-level splicing may clone the kind
/// verbatim without a remap table. Principal-less trait objects (`dyn Send`)
/// have no def path to hash and must fail closed at the frontend rather than
/// share a sentinel id.
///
/// The hash is 32-bit FNV-1a over the UTF-8 bytes, fixed here as part of the
/// convention (platform/version-stable; deliberately NOT `std::hash`).
/// Collisions across *distinct* def paths are the frontend's hazard to
/// tripwire (keep a def-path → id map per module and fail closed on any
/// collision).
pub fn stable_trait_object_id(principal_def_path: &str) -> u32 {
    const FNV_OFFSET: u32 = 0x811c_9dc5;
    const FNV_PRIME: u32 = 0x0100_0193;
    let mut hash = FNV_OFFSET;
    for byte in principal_def_path.as_bytes() {
        hash ^= u32::from(*byte);
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}

/// The canonical VTABLE-GLOBAL name mint (vtable slice 3) — the module-global
/// identity of "the vtable attached by the coercion `Source as dyn Principal`".
///
/// Like [`stable_trait_object_id`], this is a CONTENT-derived shared convention:
/// two producers of the same module (a frontend/oracle differential pair) that
/// model the same trait-object unsize must reference the SAME initializer-less
/// external `Global`, so that "two coercions of one `(principal, source)` pair
/// yield `Load`-equal metadata" — TRUE of every real execution — is stated
/// structurally on both sides, and never coincidentally.
///
/// Unlike the 32-bit `trait_id` (a fixed-width format FIELD), a global NAME is
/// an unbounded string, so this mint embeds both components VERBATIM instead of
/// hashing them: name equality then IS key equality, and the collision tripwire
/// a hashed mint would force on every frontend (per-module map, fail-closed on
/// two pairs sharing one hash) is unnecessary by construction. Injectivity is
/// enforced HERE, fail-closed: the separator `$` must not occur in
/// `source_type_key` (splitting the payload at its LAST `$` then recovers the
/// pair uniquely, whatever bytes the principal path contains), and empty
/// components are refused — a mint that cannot state its key mints nothing,
/// never a sentinel. Callers must pass the principal's UNTRIMMED def path (the
/// `stable_trait_object_id` spelling discipline) and a CLOSED-grammar canonical
/// source-type key; a source type outside the caller's canonical grammar must
/// fail closed at the caller rather than improvise a spelling.
pub fn stable_vtable_global_name(
    principal_def_path: &str,
    source_type_key: &str,
) -> Option<String> {
    if principal_def_path.is_empty() || source_type_key.is_empty() || source_type_key.contains('$')
    {
        return None;
    }
    Some(format!(
        "__trust_vtable__{principal_def_path}${source_type_key}__"
    ))
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Ty {
    // Signed integers
    I8,
    I16,
    I32,
    I64,
    I128,
    // Unsigned integers
    U8,
    U16,
    U32,
    U64,
    U128,
    /// v25 (RFC TRUST_IR_V2 B1): pointer-width signed integer — Rust `isize`
    /// carried FAITHFULLY instead of the historical fixed-width I64 respell
    /// (which could not distinguish isize from i64 and made 32-bit targets
    /// unrepresentable). Width comes from the target: `bit_width()` is `None`
    /// (target-dependent, exactly like `Ptr`); use `bit_width_with`.
    Isize,
    /// v25: pointer-width unsigned integer — Rust `usize`, the faithful twin
    /// of [`Ty::Isize`] (see its doc).
    Usize,
    /// v25: Unicode scalar value — Rust `char`. A 32-bit unsigned carrier
    /// whose VALID RANGE (`0..=0x10FFFF` minus the surrogate gap
    /// `0xD800..=0xDFFF`) is a checked claim: the validator rejects an
    /// out-of-range `char` constant. Arithmetic/switch flow through the
    /// 32-bit unsigned integer paths (casts to/from `u32` are `Bitcast`-free
    /// same-width transmutes at the value level).
    Char,
    /// v25: the ERROR/bottom type — a producer-internal fail-closed
    /// placeholder that stops the historical overloading of `Ty::Unit` for
    /// "could not type this" (the Unit ambiguity independently caused the
    /// wave-UV/A4/UF class of bugs). NEVER wire-legal: the binary writer
    /// REJECTS it (`Unencodable`), and `validate_module` rejects any module
    /// carrying it. It exists so in-memory lowering can mark a typing hole
    /// precisely and fail closed at the emission boundary instead of leaking
    /// a lie.
    Error,
    // Floating point
    F16,
    F32,
    F64,
    // Special types
    Bool,
    /// Fixed-width SIMD vector.
    ///
    /// The element type is inline so vector signatures and instructions can
    /// round-trip through the text format without relying on the module
    /// `types` table. Frontends should use a nonzero lane count. Integer and
    /// bool vectors are the core lowering surface for x86 batch Bool/Int
    /// evaluation; existing typed `BinOp`, `ICmp`, `Select`, `Load`, and
    /// `Store` instructions carry this type directly.
    ///
    /// Vector comparisons produce logical masks of type `<N x bool>`. A
    /// `select` whose result/arm type is `<N x T>` also requires a `<N x bool>`
    /// condition. Backends that use physical all-ones integer masks such as
    /// `<N x i32>` must first compare that mask to zero, then feed the compare
    /// result to `select`.
    Vector(Box<Ty>, u32),
    Ptr,
    FatPtr(FatPtrKind),
    Unit,
    Never,
    // Composite types
    Struct(StructId),
    Array(TyId, u64),
    Tuple(Vec<Ty>),
    Enum(EnumId),
    Func(FuncTyId),
    // Reference types (Rust borrowing)
    Ref(Box<Ty>),
    RefMut(Box<Ty>),
    // Raw pointer types (C semantics)
    PtrConst(Box<Ty>),
    PtrMut(Box<Ty>),
    // Reference counted (Swift ARC)
    Rc(Box<Ty>),
    // Aggregate types (issue #30, item 1).
    /// Unordered set of elements of type `T`. Representation hint is carried
    /// alongside the element type so TrustIr can pick bitset vs. boxed lowering
    /// without re-inferring. Element type is referenced via `TyId` to allow
    /// bounded forward references and to keep the enum Copy/Hash cheap.
    Set(TyId, SetRepr),
    /// Ordered variable-length sequence of elements of type `T`. Lowered to a
    /// packed buffer (length-prefixed) when the element type has known size.
    Sequence(TyId),
    /// Named-field record (ty semantics). Distinct from `Struct`: records
    /// have no fixed layout, no offsets, and equality is by field-set. Use
    /// `Struct` when C-style layout/offsets matter; use `Record` for logical
    /// labeled tuples. Defined by `RecordDef` in the module's record table.
    Record(RecordId),
    /// First-class closure: a bare function signature bundled with a typed
    /// captured-environment frame. Defined by `ClosureTy` in the module's
    /// closure-type table. The captured environment is part of the type
    /// identity (captures are explicit values, not an implicit env pointer);
    /// this is what lets self-referential `FuncDef`s route through the state
    /// partition correctly — see ty#4145 for the soundness lesson where
    /// cached closure bodies diverged from current state.
    Closure(ClosureTyId),
    /// **Refinement type**: a value of base type `TyId` that additionally
    /// satisfies predicate `PredId` (see [`crate::pred::Pred`]).
    ///
    /// # Representation-preserving, by construction
    ///
    /// `Refine(b, p)` has EXACTLY the representation of `b` — same
    /// [`Ty::bit_width`], same layout, same shape, same encoding, same
    /// codegen. No downstream artifact moves when a producer adds a
    /// refinement. The predicate is *proof surface only*; it uses the same
    /// `TyId` indirection as `Set(TyId, SetRepr)` / `Sequence(TyId)` /
    /// `Array(TyId, u64)`, so the spelling stays canonical and the enum stays
    /// cheap.
    ///
    /// # What it is FOR
    ///
    /// It puts an encoding CONVENTION in the type. When a consumer
    /// hand-encodes sums, products, functions and sets into anonymous integer
    /// lanes, the fact "this lane is an INDEX into universe U, not a MEMBER of
    /// U" lives in a producer-side map, and **dropping that fact changes
    /// meaning rather than precision** — the value silently reverts to the raw
    /// convention. Carried as a `Refine`, a dropped fact becomes
    /// [`crate::pred::Pred::Top`], `Top` entails nothing non-trivial, and the
    /// loss surfaces as a *named implication failure* at the consumption site
    /// (`validate_module`) instead of a miscompile.
    ///
    /// # Rules the validator enforces
    ///
    /// * `TyId` and `PredId` both in range.
    /// * The base may not itself be a `Refine` — one refinement layer per
    ///   spelling; nest predicates with [`crate::pred::Pred::Conj`] instead,
    ///   so there is one canonical way to say any given thing.
    /// * The predicate must be *stateable* about the base type (an interval
    ///   over an integer, `NonNull` over a pointer, and so on).
    /// * **The consumption rule**: a `Refine`-typed value flowing into a site
    ///   that declares a required predicate must satisfy
    ///   `implies(actual, required)`, where a non-`Refine` actual counts as
    ///   `Top`. Failure is a hard error naming BOTH predicates — never a
    ///   silent widen.
    Refine(TyId, PredId),
}

/// The default thin-pointer width, in bits, for the 64-bit targets TrustIr
/// currently supports.
///
/// The pointer-size-agnostic [`Ty::bit_width`] deliberately returns `None` for
/// pointer-like types rather than baking in a width — a context-free 64-bit
/// answer would be a latent miscompile on 32-bit targets such as wasm32. Code
/// that needs a concrete pointer width should call [`Ty::bit_width_with`] with
/// the target's pointer size; this constant is the right value to pass on a
/// 64-bit target.
pub const DEFAULT_POINTER_BITS: u32 = 64;

impl Ty {
    /// Bit width of a type whose size is **target-independent**.
    ///
    /// Returns `None` for every pointer-like type (`Ptr`, `*const`/`*mut`,
    /// `&`/`&mut`, `Rc`, fat pointers): their width is the target's pointer
    /// size, which is only known with a target. Resolve them with
    /// [`Ty::bit_width_with`] (e.g. 32 on wasm32, 64 on aarch64/x86-64).
    // Trust: pointers must not report a context-free 64-bit width — that is a
    // latent miscompile/missproof on 32-bit targets such as wasm32.
    pub fn bit_width(&self) -> Option<u32> {
        match self {
            Ty::Bool => Some(1),
            Ty::I8 | Ty::U8 => Some(8),
            Ty::I16 | Ty::U16 => Some(16),
            Ty::I32 | Ty::U32 => Some(32),
            Ty::I64 | Ty::U64 => Some(64),
            Ty::I128 | Ty::U128 => Some(128),
            Ty::F16 => Some(16),
            Ty::F32 => Some(32),
            Ty::F64 => Some(64),
            Ty::Vector(elem, lanes) => elem.bit_width().and_then(|bits| bits.checked_mul(*lanes)),
            Ty::Char => Some(32),
            // Pointer-width integers are target-dependent — see `bit_width_with`.
            Ty::Isize | Ty::Usize => None,
            // Pointer-like types are target-dependent — see `bit_width_with`.
            Ty::Ptr
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::Rc(_)
            | Ty::FatPtr(_) => None,
            _ => None,
        }
    }

    /// Bit width of a type given the target's thin-pointer width in bits
    /// (`pointer_bits` — e.g. 32 on wasm32, 64 on aarch64/x86-64).
    ///
    /// Resolves the pointer-like types that [`Ty::bit_width`] leaves as `None`:
    /// thin pointers/refs/`Rc` are `pointer_bits`; a fat pointer is two
    /// pointer-sized lanes (`2 * pointer_bits`, matching the fat
    /// `PointerLayoutShape` in `shape`). Every other type delegates to
    /// [`Ty::bit_width`], so its answer is unchanged.
    pub fn bit_width_with(&self, pointer_bits: u32) -> Option<u32> {
        match self {
            Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_) | Ty::Rc(_) => {
                Some(pointer_bits)
            }
            // v25 pointer-width integers.
            Ty::Isize | Ty::Usize => Some(pointer_bits),
            Ty::FatPtr(_) => pointer_bits.checked_mul(2),
            Ty::Vector(elem, lanes) => elem
                .bit_width_with(pointer_bits)
                .and_then(|bits| bits.checked_mul(*lanes)),
            _ => self.bit_width(),
        }
    }

    /// Returns true for all integer types (signed and unsigned).
    pub fn is_integer(&self) -> bool {
        self.is_signed() || self.is_unsigned()
    }

    /// Returns true for signed integer types (i8..i128).
    pub fn is_signed(&self) -> bool {
        matches!(
            self,
            Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128 | Ty::Isize
        )
    }

    /// Returns true for unsigned integer types (u8..u128).
    pub fn is_unsigned(&self) -> bool {
        matches!(
            self,
            Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128 | Ty::Usize
        )
    }

    pub fn is_float(&self) -> bool {
        matches!(self, Ty::F16 | Ty::F32 | Ty::F64)
    }

    pub fn is_numeric(&self) -> bool {
        self.is_integer() || self.is_float()
    }

    /// Whether this inline type surface contains the producer-internal
    /// [`Ty::Error`] placeholder. Named aggregate members live in module
    /// tables and must be checked at their definitions; this method recurses
    /// through every `Ty` variant that embeds another `Ty` directly.
    pub fn contains_error(&self) -> bool {
        match self {
            Ty::Error => true,
            Ty::Vector(element, _)
            | Ty::Ref(element)
            | Ty::RefMut(element)
            | Ty::PtrConst(element)
            | Ty::PtrMut(element)
            | Ty::Rc(element) => element.contains_error(),
            Ty::Tuple(elements) => elements.iter().any(Ty::contains_error),
            _ => false,
        }
    }

    /// Returns true for any fixed-width SIMD vector type.
    pub fn is_vector(&self) -> bool {
        matches!(self, Ty::Vector(_, _))
    }

    /// Returns the vector element type and lane count, if this is a vector.
    pub fn vector_shape(&self) -> Option<(&Ty, u32)> {
        match self {
            Ty::Vector(elem, lanes) => Some((elem.as_ref(), *lanes)),
            _ => None,
        }
    }

    /// Lane count for any type that supports element-update operations.
    /// Returns `None` for types that do not have a static element count.
    pub fn element_op_lane_count(&self) -> Option<u32> {
        match self {
            Ty::Vector(_, lanes) => Some(*lanes),
            Ty::Array(_, len) => u32::try_from(*len).ok(),
            _ => None,
        }
    }

    /// Returns true if this type supports element-level update operations
    /// (`extract_element`, `insert_element`). Both fixed-width SIMD vectors
    /// and fixed-size arrays qualify.
    pub fn supports_element_ops(&self) -> bool {
        matches!(self, Ty::Vector(_, _) | Ty::Array(_, _))
    }

    /// Canonical CHC x86 lane-packed integer vector type, `<4 x i32>`.
    pub fn v4_i32() -> Self {
        Ty::Vector(Box::new(Ty::I32), 4)
    }

    /// Canonical CHC x86 lane-packed integer vector type, `<2 x i64>`.
    pub fn v2_i64() -> Self {
        Ty::Vector(Box::new(Ty::I64), 2)
    }

    /// Canonical logical mask type for `<4 x i32>` vector selects.
    pub fn v4_bool() -> Self {
        Ty::Vector(Box::new(Ty::Bool), 4)
    }

    /// Canonical logical mask type for 8-lane vector compare masks.
    pub fn v8_bool() -> Self {
        Ty::Vector(Box::new(Ty::Bool), 8)
    }

    /// Canonical logical mask type for 16-lane vector compare masks.
    pub fn v16_bool() -> Self {
        Ty::Vector(Box::new(Ty::Bool), 16)
    }

    /// Canonical logical mask type for `<2 x i64>` vector selects.
    pub fn v2_bool() -> Self {
        Ty::Vector(Box::new(Ty::Bool), 2)
    }

    /// Canonical single-precision float lane vector, `<4 x f32>`.
    pub fn v4_f32() -> Self {
        Ty::Vector(Box::new(Ty::F32), 4)
    }

    /// Canonical double-precision float lane vector, `<2 x f64>`.
    pub fn v2_f64() -> Self {
        Ty::Vector(Box::new(Ty::F64), 2)
    }

    /// Returns true for nonzero-lane vectors whose element type is integer.
    pub fn is_integer_vector(&self) -> bool {
        matches!(self, Ty::Vector(elem, lanes) if *lanes > 0 && elem.is_integer())
    }

    /// Returns true for nonzero-lane vectors whose element type is `bool`.
    pub fn is_bool_vector(&self) -> bool {
        matches!(self, Ty::Vector(elem, lanes) if *lanes > 0 && **elem == Ty::Bool)
    }

    /// Returns true for nonzero-lane vectors whose element type is float.
    pub fn is_float_vector(&self) -> bool {
        matches!(self, Ty::Vector(elem, lanes) if *lanes > 0 && elem.is_float())
    }

    /// Result type for an elementwise comparison over this operand type.
    pub fn comparison_result_ty(&self) -> Ty {
        match self {
            Ty::Vector(_, lanes) => Ty::Vector(Box::new(Ty::Bool), *lanes),
            _ => Ty::Bool,
        }
    }

    /// Required condition type for a `select` producing this value type.
    ///
    /// Scalar selects use a scalar `bool` condition. Vector selects use a
    /// logical lane mask, `<N x bool>`, regardless of the selected element type.
    pub fn select_condition_ty(&self) -> Ty {
        match self {
            Ty::Vector(_, lanes) => Ty::Vector(Box::new(Ty::Bool), *lanes),
            _ => Ty::Bool,
        }
    }

    /// Returns true when this is an integer vector with the same lane count as
    /// a vector select result. Such values are physical masks, not legal TrustIr
    /// select conditions; compare them to zero to obtain `<N x bool>`.
    pub fn is_integer_vector_mask_for_select_ty(&self, select_ty: &Ty) -> bool {
        match (self.vector_shape(), select_ty.vector_shape()) {
            (Some((cond_elem, cond_lanes)), Some((_select_elem, select_lanes))) => {
                cond_lanes == select_lanes && cond_elem.is_integer()
            }
            _ => false,
        }
    }

    /// Returns true for reference types (&T, &mut T, *const T, *mut T, Rc<T>).
    pub fn is_reference(&self) -> bool {
        matches!(
            self,
            Ty::Ref(_)
                | Ty::RefMut(_)
                | Ty::PtrConst(_)
                | Ty::PtrMut(_)
                | Ty::Rc(_)
                | Ty::FatPtr(_)
        )
    }

    /// Returns true for aggregate / collection types: Set, Sequence, Record,
    /// Tuple, Array, Struct, Enum.
    ///
    /// Aggregates have no fixed bit width (`bit_width()` returns None) and
    /// typically require auxiliary definitions (`StructDef`, `EnumDef`,
    /// `RecordDef`) or element-type lookups.
    pub fn is_aggregate(&self) -> bool {
        matches!(
            self,
            Ty::Set(_, _)
                | Ty::Sequence(_)
                | Ty::Record(_)
                | Ty::Tuple(_)
                | Ty::Array(_, _)
                | Ty::Struct(_)
                | Ty::Enum(_)
        )
    }

    /// Returns true for closure types (function with captured environment).
    pub fn is_closure(&self) -> bool {
        matches!(self, Ty::Closure(_))
    }

    /// Returns true for refinement types.
    pub fn is_refine(&self) -> bool {
        matches!(self, Ty::Refine(_, _))
    }

    /// The `(base, predicate)` pair of a refinement type.
    pub fn refinement(&self) -> Option<(TyId, PredId)> {
        match self {
            Ty::Refine(base, pred) => Some((*base, *pred)),
            _ => None,
        }
    }

    /// The predicate a refinement carries, or `None` for every other type.
    ///
    /// A `None` here means [`crate::pred::Pred::Top`] at a consumption site —
    /// "no information" — NOT "no constraint to check". That mapping is the
    /// whole safety argument: an unrefined value cannot satisfy a site that
    /// demands a convention.
    pub fn predicate(&self) -> Option<PredId> {
        match self {
            Ty::Refine(_, pred) => Some(*pred),
            _ => None,
        }
    }
}

impl core::fmt::Display for Ty {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Ty::I8 => f.write_str("i8"),
            Ty::I16 => f.write_str("i16"),
            Ty::I32 => f.write_str("i32"),
            Ty::I64 => f.write_str("i64"),
            Ty::I128 => f.write_str("i128"),
            Ty::U8 => f.write_str("u8"),
            Ty::U16 => f.write_str("u16"),
            Ty::U32 => f.write_str("u32"),
            Ty::U64 => f.write_str("u64"),
            Ty::U128 => f.write_str("u128"),
            Ty::Isize => f.write_str("isize"),
            Ty::Usize => f.write_str("usize"),
            Ty::Char => f.write_str("char"),
            // Diagnostics-only spelling the parser REJECTS: a leaked Error
            // can never round-trip through the text format.
            Ty::Error => f.write_str("{error}"),
            Ty::F16 => f.write_str("f16"),
            Ty::F32 => f.write_str("f32"),
            Ty::F64 => f.write_str("f64"),
            Ty::Bool => f.write_str("bool"),
            Ty::Vector(elem, lanes) => write!(f, "<{lanes} x {elem}>"),
            Ty::Ptr => f.write_str("ptr"),
            Ty::FatPtr(kind) => write!(f, "fatptr<{kind}>"),
            Ty::Unit => f.write_str("()"),
            Ty::Never => f.write_str("!"),
            Ty::Struct(id) => write!(f, "struct.{}", id.0),
            Ty::Array(elem, len) => write!(f, "[ty.{} x {}]", elem.0, len),
            Ty::Tuple(elems) => {
                // The zero-element tuple is spelled `(,)` so it is textually
                // distinct from the unit type `()` (which Display emits above).
                // Without this they would both render `()` and a text round
                // trip would collapse `Ty::Unit` into `Ty::Tuple(vec![])`.
                if elems.is_empty() {
                    return f.write_str("(,)");
                }
                write!(f, "(")?;
                for (i, ty) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", ty)?;
                }
                write!(f, ")")
            }
            Ty::Enum(id) => write!(f, "enum.{}", id.0),
            Ty::Func(id) => write!(f, "functy.{}", id.0),
            Ty::Ref(inner) => write!(f, "&{}", inner),
            Ty::RefMut(inner) => write!(f, "&mut {}", inner),
            Ty::PtrConst(inner) => write!(f, "*const {}", inner),
            Ty::PtrMut(inner) => write!(f, "*mut {}", inner),
            Ty::Rc(inner) => write!(f, "Rc<{}>", inner),
            Ty::Set(elem, repr) => write!(f, "set<ty.{}, {}>", elem.0, repr),
            Ty::Sequence(elem) => write!(f, "seq<ty.{}>", elem.0),
            Ty::Record(id) => write!(f, "record.{}", id.0),
            Ty::Closure(id) => write!(f, "closure.{}", id.0),
            Ty::Refine(base, pred) => write!(f, "refine<ty.{}, pred.{}>", base.0, pred.0),
        }
    }
}

/// Definition of a named-field record (ty-style).
///
/// Records are structurally typed labeled tuples with no layout metadata.
/// Field order in the `fields` vector is canonical (typically sorted by
/// `name`) so that records with the same field-set compare equal by value.
/// Frontends that need C-style struct layout (offsets, size, alignment)
/// should use `StructDef` instead.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct RecordDef {
    pub id: RecordId,
    pub name: String,
    /// Named fields. Reuses `FieldDef` but `offset` is always `None` for
    /// records (records have no fixed layout).
    pub fields: Vec<FieldDef>,
}

/// First-class closure type: a bare function signature (`FuncTyId`) bundled
/// with an explicit captured-environment frame.
///
/// The captures list records the types of values captured from the enclosing
/// scope at closure-creation time. Captures are part of the type identity
/// because TrustIr closures route captured state through the state partition
/// explicitly — cached closure bodies that reference stale captured state
/// are the soundness bug pattern ty#4145 hit for `SA[bb \in Ballot]`
/// recursive defs.
///
/// Bare function pointers (no captures) use `Ty::Func(FuncTyId)` directly;
/// `Ty::Closure(ClosureTyId)` is for any function value with captured env.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ClosureTy {
    /// Reference to the bare function signature in the module's
    /// `func_types` table (params + returns + vararg flag).
    pub func: FuncTyId,
    /// Types of captured environment slots, in declaration order.
    /// Empty captures still produces a distinct closure type — callers that
    /// want a plain function pointer should use `Ty::Func(FuncTyId)`.
    pub captures: Vec<Ty>,
}

impl ClosureTy {
    /// Convenience: closure with no captures (equivalent in semantics to a
    /// bare function pointer but with closure-typed value identity).
    pub fn bare(func: FuncTyId) -> Self {
        Self {
            func,
            captures: Vec::new(),
        }
    }

    /// Number of captured-env slots.
    pub fn capture_count(&self) -> usize {
        self.captures.len()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FuncTy {
    pub params: Vec<Ty>,
    pub returns: Vec<Ty>,
    pub is_vararg: bool,
}

/// ABI / layout classification of a struct, mirroring Rust's `#[repr(..)]`:
/// - `Rust` — unspecified, layout-optimised representation (the default); field
///   order/padding is the backend's choice.
/// - `C` — C-compatible layout (`#[repr(C)]`): fields in declaration order.
/// - `Transparent` — `#[repr(transparent)]`: a wrapper whose ABI is exactly its
///   single non-zero-size field.
/// - `Packed(align)` — `#[repr(packed(N))]`: field alignment clamped to `N`
///   (a power of two; `Packed(1)` is fully packed).
///
/// TrustCg needs this to lay out struct memory deterministically; it is part of
/// the ABI contract, not a hint.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum StructRepr {
    /// Unspecified, layout-optimised Rust representation. Default.
    #[default]
    Rust,
    /// C-compatible layout (`#[repr(C)]`).
    C,
    /// Single-field transparent wrapper (`#[repr(transparent)]`).
    Transparent,
    /// Packed layout with the given power-of-two alignment clamp.
    Packed(u32),
}

impl core::fmt::Display for StructRepr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            StructRepr::Rust => f.write_str("rust"),
            StructRepr::C => f.write_str("c"),
            StructRepr::Transparent => f.write_str("transparent"),
            StructRepr::Packed(align) => write!(f, "packed({align})"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct StructDef {
    pub id: StructId,
    pub name: String,
    pub fields: Vec<FieldDef>,
    pub size: Option<u64>,
    pub align: Option<u64>,
    /// ABI / layout classification (defaults to [`StructRepr::Rust`]). Additive:
    /// modules serialized before this field existed deserialize as `Rust`.
    #[cfg_attr(feature = "serde", serde(default))]
    pub repr: StructRepr,
}

impl StructDef {
    /// Builder-style setter for [`StructDef::repr`], chainable onto a literal.
    pub fn with_repr(mut self, repr: StructRepr) -> Self {
        self.repr = repr;
        self
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FieldDef {
    pub name: String,
    pub ty: Ty,
    pub offset: Option<u64>,
}

/// Explicit tag-integer representation hint for an enum, mirroring Rust's
/// `#[repr(u8)] / #[repr(i32)] / …` on a fieldful or fieldless enum.
///
/// This names the integer type of the **discriminant tag lane** in trust-ir's
/// canonical tagged-union layout (see [`EnumDef`]). When absent, the canonical
/// layout picks the smallest tag that fits every effective discriminant
/// ([`EnumDef::canonical_tag_repr`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum EnumTagRepr {
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
}

impl EnumTagRepr {
    /// The integer [`Ty`] of the tag lane.
    pub fn ty(self) -> Ty {
        match self {
            EnumTagRepr::U8 => Ty::U8,
            EnumTagRepr::U16 => Ty::U16,
            EnumTagRepr::U32 => Ty::U32,
            EnumTagRepr::U64 => Ty::U64,
            EnumTagRepr::I8 => Ty::I8,
            EnumTagRepr::I16 => Ty::I16,
            EnumTagRepr::I32 => Ty::I32,
            EnumTagRepr::I64 => Ty::I64,
        }
    }

    /// True when `value` is representable in this tag type.
    pub fn fits(self, value: i128) -> bool {
        match self {
            EnumTagRepr::U8 => (0..=u8::MAX as i128).contains(&value),
            EnumTagRepr::U16 => (0..=u16::MAX as i128).contains(&value),
            EnumTagRepr::U32 => (0..=u32::MAX as i128).contains(&value),
            EnumTagRepr::U64 => (0..=u64::MAX as i128).contains(&value),
            EnumTagRepr::I8 => (i8::MIN as i128..=i8::MAX as i128).contains(&value),
            EnumTagRepr::I16 => (i16::MIN as i128..=i16::MAX as i128).contains(&value),
            EnumTagRepr::I32 => (i32::MIN as i128..=i32::MAX as i128).contains(&value),
            EnumTagRepr::I64 => (i64::MIN as i128..=i64::MAX as i128).contains(&value),
        }
    }

    /// The smallest tag repr whose range covers `[min, max]` under trust-ir's
    /// canonical rule: all-non-negative discriminants take the smallest
    /// unsigned width; any negative discriminant takes the smallest signed
    /// width. `None` when the span exceeds 64 bits (the canonical tag cap —
    /// i128-wide discriminants are unsupported, fail-closed).
    pub fn smallest_for(min: i128, max: i128) -> Option<Self> {
        let candidates: &[EnumTagRepr] = if min >= 0 {
            &[
                EnumTagRepr::U8,
                EnumTagRepr::U16,
                EnumTagRepr::U32,
                EnumTagRepr::U64,
            ]
        } else {
            &[
                EnumTagRepr::I8,
                EnumTagRepr::I16,
                EnumTagRepr::I32,
                EnumTagRepr::I64,
            ]
        };
        candidates
            .iter()
            .copied()
            .find(|repr| repr.fits(min) && repr.fits(max))
    }
}

impl core::fmt::Display for EnumTagRepr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            EnumTagRepr::U8 => "u8",
            EnumTagRepr::U16 => "u16",
            EnumTagRepr::U32 => "u32",
            EnumTagRepr::U64 => "u64",
            EnumTagRepr::I8 => "i8",
            EnumTagRepr::I16 => "i16",
            EnumTagRepr::I32 => "i32",
            EnumTagRepr::I64 => "i64",
        })
    }
}

/// How a multi-variant enum's discriminant is encoded in memory.
///
/// `Direct` stores the effective discriminant in a tag word. `Niche` stores
/// niched variants in otherwise-invalid values of a payload lane; the
/// `untagged_variant` retains its ordinary payload value. Niche arithmetic
/// wraps at `niche_ty`'s width. The interval may contain the untagged variant;
/// its corresponding reserved value is then a dead/invalid byte image.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum EnumTagEncoding {
    Direct {
        /// Byte offset of the tag word within the enum's memory image.
        tag_offset: u64,
    },
    Niche {
        untagged_variant: u32,
        niche_variants_start: u32,
        niche_variants_end: u32,
        #[cfg_attr(feature = "serde", serde(with = "crate::wide_int_serde::wide_u128"))]
        niche_start: u128,
        /// Byte offset of the niche field within the enum's memory image.
        niche_offset: u64,
        /// In-memory width and signedness of the niche scalar.
        niche_ty: EnumTagRepr,
    },
    /// No runtime tag: the variant is statically known, so the memory image is
    /// the payload alone.
    ///
    /// This is the shape rustc gives a single-INHABITED-variant `repr(Rust)`
    /// enum — `enum UnOp { Not(Vec<()>) }` is exactly its 24-byte payload, with
    /// no discriminant stored anywhere. Before this encoding existed the
    /// producer had to DECLINE a descriptor for such a def (the grammar could
    /// only say `Direct` or `Niche`, and neither is true), and a descriptor-less
    /// enum falls back to the canonical tagged-union layout — which budgets a
    /// tag. The gap was not cosmetic: it made `Option<UnOp>` unvalidatable,
    /// because Option's own (correct, rustc-derived) descriptor says 24 while
    /// the canonical recomputation of its `UnOp` field says 8 + 24 = 32.
    ///
    /// NOT the same predicate as "one variant". rustc drops the tag only when
    /// `present_second.is_none() && !repr.inhibit_enum_layout_opt()`, and
    /// `inhibit` is `repr.c() || repr.int.is_some()` — so `#[repr(C)] enum H
    /// { X(u8) }` (size 8, field at 4) and `#[repr(u8)] enum C2 { X(u8) }`
    /// (size 2, field at 1) BOTH keep a real discriminant and must keep using
    /// `Direct`. The producer therefore reads rustc's own `Variants::Single`
    /// verdict rather than counting variants.
    ///
    /// The canonical layout is deliberately left alone. It is not a rustc model
    /// (see the note on `EnumDef` — rustc also REORDERS fields, which canonical
    /// does not), so making it tag-free would not buy parity; it would only
    /// trade a loud, checkable error for a silent, wider disagreement. Every
    /// other rustc layout fact rides the descriptor, and so does this one.
    ///
    /// This affects the memory IMAGE, not the value model. `EnumDef` still has
    /// a `canonical_tag_repr()` and the interpreter's enum value is still
    /// `Aggregate([tag, fields..])`; the tag simply is not stored, and is
    /// recovered on `Load` from the sole variant. (The verifier-facing
    /// `request::facts::NativeEnumTagEncoding::Untagged`, which has described
    /// rustc's strategy since before this variant existed, is the same fact one
    /// layer out — it additionally forbids a discriminant, because it describes
    /// rustc's enum rather than trust-ir's byte image.)
    Untagged,
}

/// Concrete enum memory layout supplied by the producer.
///
/// The descriptor is normative when present: consumers must use this byte
/// layout instead of synthesizing trust-ir's canonical tagged-union layout.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct EnumLayoutDescriptor {
    pub encoding: EnumTagEncoding,
    /// Total size in bytes.
    pub size: u64,
    /// ABI alignment in bytes.
    pub align: u64,
    /// Per-variant, per-field byte offsets in source-declaration order.
    pub variant_field_offsets: Vec<Vec<u64>>,
}

/// Definition of an enum (sum) type with named variants.
///
/// # Canonical layout (trust-ir's, NOT a claim of rustc layout parity)
///
/// `Ty::Enum` has a **canonical tagged-union layout** defined by trust-ir
/// itself: a discriminant tag lane at offset 0 followed by a max-sized payload
/// region shared by all variants (rules documented on
/// `Module::enum_layout_shape` in `shape` and mirrored by the reference
/// interpreter's memory model). This is deliberately *not* rustc's layout:
/// rustc's `repr(Rust)` enums perform niche optimization, variant reordering,
/// and other layout optimizations that trust-ir does not model. Mapping a
/// rustc-laid-out enum onto this canonical shape (or asserting equivalence) is
/// a producer-side concern, exactly like `StructRepr::Rust` structs whose
/// declared offsets come from the producer.
///
/// # Discriminants
///
/// `discriminants` optionally assigns explicit values per variant, parallel to
/// `variants` (missing / `None` entries follow Rust's assignment rule: one
/// more than the previous variant's value, with the first defaulting to 0 —
/// see [`EnumDef::effective_discriminants`]). `repr` optionally pins the tag
/// integer type. Both fields are additive and serde-defaulted: modules
/// serialized before they existed deserialize with no explicit discriminants
/// and no repr hint, preserving the historical index-tag interpretation
/// (variant *i* tags as *i*). `layout` is a concrete producer-provided layout
/// descriptor and is normative when present.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct EnumDef {
    pub id: EnumId,
    pub name: String,
    pub variants: Vec<EnumVariant>,
    /// Explicit per-variant discriminant values, parallel to `variants`.
    /// Entries may be `None` (implicit: previous + 1, first defaults to 0) and
    /// the vector may be shorter than `variants` (missing entries are
    /// implicit). Canonical/diff-stable form trims trailing `None`s; the
    /// all-implicit case is the empty vector.
    // Positional-MessagePack safety: this is not the last field, so it must
    // ALWAYS be emitted (no skip_serializing_if) — only the trailing `repr`
    // could ever skip.
    #[cfg_attr(feature = "serde", serde(default))]
    pub discriminants: Vec<Option<i128>>,
    /// Optional explicit tag-representation hint (`#[repr(u8)]`-style). When
    /// present, every effective discriminant must fit it or the enum has no
    /// canonical layout (fail-closed).
    #[cfg_attr(feature = "serde", serde(default))]
    pub repr: Option<EnumTagRepr>,
    /// Concrete producer-provided layout, or `None` when layout is unknown.
    ///
    /// This is a trailing serde-defaulted field for positional MessagePack
    /// compatibility with modules written before wire version 31.
    #[cfg_attr(feature = "serde", serde(default))]
    pub layout: Option<EnumLayoutDescriptor>,
}

impl EnumDef {
    /// Convenience constructor for the common all-implicit case: no explicit
    /// discriminants (variant *i* takes value *i*), no repr hint.
    pub fn new(id: EnumId, name: impl Into<String>, variants: Vec<EnumVariant>) -> Self {
        Self {
            id,
            name: name.into(),
            variants,
            discriminants: Vec::new(),
            repr: None,
            layout: None,
        }
    }

    /// Builder-style setter for [`EnumDef::discriminants`].
    pub fn with_discriminants(mut self, discriminants: Vec<Option<i128>>) -> Self {
        self.discriminants = discriminants;
        self
    }

    /// Builder-style setter for [`EnumDef::repr`].
    pub fn with_repr(mut self, repr: EnumTagRepr) -> Self {
        self.repr = Some(repr);
        self
    }

    /// Resolve every variant's **effective discriminant** under the canonical
    /// assignment rule (mirroring Rust): an explicit entry takes its value; an
    /// implicit one takes the previous variant's value plus one, with the
    /// first variant defaulting to 0.
    ///
    /// Fail-closed `None` when the assignment is ill-formed: an implicit
    /// increment overflows `i128`, or two variants resolve to the same value
    /// (duplicate discriminants make the tag ambiguous).
    pub fn effective_discriminants(&self) -> Option<Vec<i128>> {
        let mut out: Vec<i128> = Vec::with_capacity(self.variants.len());
        let mut next: Option<i128> = Some(0);
        for i in 0..self.variants.len() {
            let value = match self.discriminants.get(i).copied().flatten() {
                Some(explicit) => explicit,
                None => next?,
            };
            if out.contains(&value) {
                return None;
            }
            out.push(value);
            next = value.checked_add(1);
        }
        Some(out)
    }

    /// The canonical tag representation for this enum's layout: the explicit
    /// [`EnumDef::repr`] hint when present (every effective discriminant must
    /// fit it), otherwise the smallest width per
    /// [`EnumTagRepr::smallest_for`].
    ///
    /// Fail-closed `None` when the enum has no canonical tag: zero variants
    /// (uninhabited — no values, no layout), unresolvable discriminants
    /// ([`EnumDef::effective_discriminants`]), a hint too narrow for the
    /// values, or values beyond the 64-bit tag cap.
    pub fn canonical_tag_repr(&self) -> Option<EnumTagRepr> {
        if self.variants.is_empty() {
            return None;
        }
        let discs = self.effective_discriminants()?;
        if let Some(hint) = self.repr {
            return discs.iter().all(|d| hint.fits(*d)).then_some(hint);
        }
        let min = *discs.iter().min()?;
        let max = *discs.iter().max()?;
        EnumTagRepr::smallest_for(min, max)
    }
}

/// A single variant of an enum type.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct EnumVariant {
    pub name: String,
    pub fields: Vec<Ty>,
    /// Per-field source names, parallel to `fields`. Empty means positional.
    /// These names are fidelity metadata and are ignored by cross-module type
    /// comparison.
    #[cfg_attr(feature = "serde", serde(default))]
    pub field_names: Vec<String>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::{ClosureTyId, EnumId, FuncTyId, PredId, RecordId, StructId, TyId};

    #[test]
    fn bit_width_integers() {
        assert_eq!(Ty::I8.bit_width(), Some(8));
        assert_eq!(Ty::I16.bit_width(), Some(16));
        assert_eq!(Ty::I32.bit_width(), Some(32));
        assert_eq!(Ty::I64.bit_width(), Some(64));
        assert_eq!(Ty::I128.bit_width(), Some(128));
    }

    #[test]
    fn bit_width_floats() {
        assert_eq!(Ty::F16.bit_width(), Some(16));
        assert_eq!(Ty::F32.bit_width(), Some(32));
        assert_eq!(Ty::F64.bit_width(), Some(64));
    }

    #[test]
    fn bit_width_special() {
        assert_eq!(Ty::Bool.bit_width(), Some(1));
        // Pointer width is target-dependent: `bit_width` is honest and returns
        // None; the resolved width comes from `bit_width_with`.
        assert_eq!(Ty::Ptr.bit_width(), None);
        assert_eq!(Ty::Unit.bit_width(), None);
    }

    #[test]
    fn bit_width_with_resolves_pointers_by_target() {
        // Thin pointer-like types take the target's pointer width.
        assert_eq!(Ty::Ptr.bit_width_with(32), Some(32));
        assert_eq!(Ty::Ptr.bit_width_with(64), Some(64));
        assert_eq!(Ty::PtrConst(Box::new(Ty::I32)).bit_width_with(32), Some(32));
        assert_eq!(Ty::PtrMut(Box::new(Ty::I32)).bit_width_with(64), Some(64));
        assert_eq!(Ty::Ref(Box::new(Ty::I32)).bit_width_with(32), Some(32));
        assert_eq!(Ty::RefMut(Box::new(Ty::I32)).bit_width_with(64), Some(64));
        assert_eq!(Ty::Rc(Box::new(Ty::I32)).bit_width_with(32), Some(32));
        // A fat pointer is two pointer-sized lanes.
        assert_eq!(Ty::FatPtr(FatPtrKind::Str).bit_width_with(32), Some(64));
        assert_eq!(Ty::FatPtr(FatPtrKind::Str).bit_width_with(64), Some(128));
        // Non-pointer types ignore `pointer_bits` and match `bit_width`.
        assert_eq!(Ty::I32.bit_width_with(32), Some(32));
        assert_eq!(Ty::I64.bit_width_with(32), Ty::I64.bit_width());
        assert_eq!(Ty::Unit.bit_width_with(32), None);
    }

    #[test]
    fn bit_width_compound_types_return_none() {
        assert_eq!(Ty::Struct(StructId::new(0)).bit_width(), None);
        assert_eq!(Ty::Array(TyId::new(0), 10).bit_width(), None);
        assert_eq!(Ty::Func(FuncTyId::new(0)).bit_width(), None);
    }

    #[test]
    fn bit_width_with_default_pointer_bits_resolves_to_64() {
        // For non-pointer types, the pointer-agnostic `bit_width` and the
        // target-aware `bit_width_with` agree regardless of the pointer size.
        for ty in [
            Ty::Bool,
            Ty::I32,
            Ty::F64,
            Ty::v4_i32(),
            Ty::Struct(StructId::new(0)),
        ] {
            assert_eq!(
                ty.bit_width(),
                ty.bit_width_with(super::DEFAULT_POINTER_BITS),
                "non-pointer bit_width must be pointer-size-independent for {ty:?}"
            );
        }
        // Pointer-like types are honestly `None` pointer-agnostically, but
        // resolve to the 64-bit default when handed DEFAULT_POINTER_BITS.
        for ty in [
            Ty::Ptr,
            Ty::PtrConst(Box::new(Ty::I8)),
            Ty::Ref(Box::new(Ty::I64)),
            Ty::Rc(Box::new(Ty::I32)),
        ] {
            assert_eq!(ty.bit_width(), None, "{ty:?} must be target-dependent");
            assert_eq!(
                ty.bit_width_with(super::DEFAULT_POINTER_BITS),
                Some(64),
                "{ty:?} resolves to 64 bits on a 64-bit target"
            );
        }

        // Vectors of pointers are also target-dependent, scaling lane count by
        // the resolved per-lane pointer width.
        let v2_ptr = Ty::Vector(Box::new(Ty::Ptr), 2);
        assert_eq!(v2_ptr.bit_width(), None);
        assert_eq!(v2_ptr.bit_width_with(32), Some(64));
        assert_eq!(v2_ptr.bit_width_with(64), Some(128));
    }

    #[test]
    fn is_integer_classification() {
        assert!(Ty::I8.is_integer());
        assert!(Ty::I16.is_integer());
        assert!(Ty::I32.is_integer());
        assert!(Ty::I64.is_integer());
        assert!(Ty::I128.is_integer());
        assert!(!Ty::F16.is_integer());
        assert!(!Ty::F32.is_integer());
        assert!(!Ty::F64.is_integer());
        assert!(!Ty::Bool.is_integer());
        assert!(!Ty::Ptr.is_integer());
        assert!(!Ty::Unit.is_integer());
    }

    #[test]
    fn is_float_classification() {
        assert!(Ty::F16.is_float());
        assert!(Ty::F32.is_float());
        assert!(Ty::F64.is_float());
        assert!(!Ty::I32.is_float());
        assert!(!Ty::Bool.is_float());
        assert!(!Ty::Ptr.is_float());
    }

    #[test]
    fn is_numeric_classification() {
        assert!(Ty::I32.is_numeric());
        assert!(Ty::F16.is_numeric());
        assert!(Ty::F64.is_numeric());
        assert!(!Ty::Bool.is_numeric());
        assert!(!Ty::Ptr.is_numeric());
        assert!(!Ty::Unit.is_numeric());
    }

    #[test]
    fn display_primitive_types() {
        assert_eq!(format!("{}", Ty::I8), "i8");
        assert_eq!(format!("{}", Ty::I16), "i16");
        assert_eq!(format!("{}", Ty::I32), "i32");
        assert_eq!(format!("{}", Ty::I64), "i64");
        assert_eq!(format!("{}", Ty::I128), "i128");
        assert_eq!(format!("{}", Ty::F16), "f16");
        assert_eq!(format!("{}", Ty::F32), "f32");
        assert_eq!(format!("{}", Ty::F64), "f64");
        assert_eq!(format!("{}", Ty::Bool), "bool");
        assert_eq!(format!("{}", Ty::Ptr), "ptr");
        assert_eq!(format!("{}", Ty::Unit), "()");
    }

    #[test]
    fn display_compound_types() {
        assert_eq!(format!("{}", Ty::Struct(StructId::new(3))), "struct.3");
        assert_eq!(format!("{}", Ty::Array(TyId::new(1), 8)), "[ty.1 x 8]");
        assert_eq!(format!("{}", Ty::Func(FuncTyId::new(2))), "functy.2");
    }

    // --- NEW TYPE TESTS ---

    #[test]
    fn is_numeric_compound_types_false() {
        assert!(!Ty::Struct(StructId::new(0)).is_numeric());
        assert!(!Ty::Array(TyId::new(0), 10).is_numeric());
        assert!(!Ty::Func(FuncTyId::new(0)).is_numeric());
    }

    #[test]
    fn is_integer_compound_types_false() {
        assert!(!Ty::Struct(StructId::new(0)).is_integer());
        assert!(!Ty::Array(TyId::new(0), 5).is_integer());
        assert!(!Ty::Func(FuncTyId::new(0)).is_integer());
    }

    #[test]
    fn is_float_compound_types_false() {
        assert!(!Ty::Struct(StructId::new(0)).is_float());
        assert!(!Ty::Array(TyId::new(0), 5).is_float());
        assert!(!Ty::Func(FuncTyId::new(0)).is_float());
    }

    #[test]
    fn struct_def_with_no_size_align() {
        let sd = StructDef {
            id: StructId::new(0),
            name: "Opaque".to_string(),
            fields: vec![],
            size: None,
            align: None,

            repr: Default::default(),
        };
        assert_eq!(sd.name, "Opaque");
        assert!(sd.fields.is_empty());
        assert!(sd.size.is_none());
        assert!(sd.align.is_none());
    }

    #[test]
    fn func_ty_vararg() {
        let ft = FuncTy {
            params: vec![Ty::I32],
            returns: vec![],
            is_vararg: true,
        };
        assert!(ft.is_vararg);
        assert_eq!(ft.params.len(), 1);
    }

    #[test]
    fn func_ty_no_params_no_returns() {
        let ft = FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        };
        assert!(ft.params.is_empty());
        assert!(ft.returns.is_empty());
        assert!(!ft.is_vararg);
    }

    #[test]
    fn func_ty_multiple_returns() {
        let ft = FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32, Ty::Bool],
            is_vararg: false,
        };
        assert_eq!(ft.returns.len(), 2);
        assert_eq!(ft.returns[0], Ty::I32);
        assert_eq!(ft.returns[1], Ty::Bool);
    }

    #[test]
    fn field_def_without_offset() {
        let fd = FieldDef {
            name: "field".to_string(),
            ty: Ty::I32,
            offset: None,
        };
        assert!(fd.offset.is_none());
    }

    #[test]
    fn ty_equality() {
        assert_eq!(Ty::I32, Ty::I32);
        assert_ne!(Ty::I32, Ty::I64);
        assert_ne!(Ty::F32, Ty::F64);
        assert_ne!(Ty::Bool, Ty::I8);
        assert_eq!(Ty::Struct(StructId::new(0)), Ty::Struct(StructId::new(0)));
        assert_ne!(Ty::Struct(StructId::new(0)), Ty::Struct(StructId::new(1)));
    }

    // --- Unsigned integer tests ---

    #[test]
    fn bit_width_unsigned_integers() {
        assert_eq!(Ty::U8.bit_width(), Some(8));
        assert_eq!(Ty::U16.bit_width(), Some(16));
        assert_eq!(Ty::U32.bit_width(), Some(32));
        assert_eq!(Ty::U64.bit_width(), Some(64));
        assert_eq!(Ty::U128.bit_width(), Some(128));
    }

    #[test]
    fn is_unsigned_classification() {
        assert!(Ty::U8.is_unsigned());
        assert!(Ty::U16.is_unsigned());
        assert!(Ty::U32.is_unsigned());
        assert!(Ty::U64.is_unsigned());
        assert!(Ty::U128.is_unsigned());
        assert!(!Ty::I8.is_unsigned());
        assert!(!Ty::I32.is_unsigned());
        assert!(!Ty::F16.is_unsigned());
        assert!(!Ty::F32.is_unsigned());
        assert!(!Ty::Bool.is_unsigned());
    }

    #[test]
    fn is_signed_classification() {
        assert!(Ty::I8.is_signed());
        assert!(Ty::I16.is_signed());
        assert!(Ty::I32.is_signed());
        assert!(Ty::I64.is_signed());
        assert!(Ty::I128.is_signed());
        assert!(!Ty::U8.is_signed());
        assert!(!Ty::U32.is_signed());
        assert!(!Ty::F16.is_signed());
        assert!(!Ty::F64.is_signed());
        assert!(!Ty::Bool.is_signed());
    }

    #[test]
    fn unsigned_is_integer() {
        assert!(Ty::U8.is_integer());
        assert!(Ty::U16.is_integer());
        assert!(Ty::U32.is_integer());
        assert!(Ty::U64.is_integer());
        assert!(Ty::U128.is_integer());
    }

    #[test]
    fn unsigned_is_numeric() {
        assert!(Ty::U8.is_numeric());
        assert!(Ty::U32.is_numeric());
        assert!(Ty::U128.is_numeric());
    }

    #[test]
    fn display_unsigned_types() {
        assert_eq!(format!("{}", Ty::U8), "u8");
        assert_eq!(format!("{}", Ty::U16), "u16");
        assert_eq!(format!("{}", Ty::U32), "u32");
        assert_eq!(format!("{}", Ty::U64), "u64");
        assert_eq!(format!("{}", Ty::U128), "u128");
    }

    #[test]
    fn unsigned_signed_not_equal() {
        assert_ne!(Ty::I8, Ty::U8);
        assert_ne!(Ty::I16, Ty::U16);
        assert_ne!(Ty::I32, Ty::U32);
        assert_ne!(Ty::I64, Ty::U64);
        assert_ne!(Ty::I128, Ty::U128);
    }

    // --- Unit and Never type tests ---

    #[test]
    fn unit_type_properties() {
        assert_eq!(Ty::Unit.bit_width(), None);
        assert!(!Ty::Unit.is_integer());
        assert!(!Ty::Unit.is_float());
        assert!(!Ty::Unit.is_numeric());
        assert!(!Ty::Unit.is_reference());
        assert!(!Ty::Unit.is_signed());
        assert!(!Ty::Unit.is_unsigned());
    }

    #[test]
    fn never_type_properties() {
        assert_eq!(Ty::Never.bit_width(), None);
        assert!(!Ty::Never.is_integer());
        assert!(!Ty::Never.is_float());
        assert!(!Ty::Never.is_numeric());
        assert!(!Ty::Never.is_reference());
    }

    #[test]
    fn display_unit_and_never() {
        assert_eq!(format!("{}", Ty::Unit), "()");
        assert_eq!(format!("{}", Ty::Never), "!");
    }

    #[test]
    fn unit_never_not_equal() {
        assert_ne!(Ty::Unit, Ty::Never);
    }

    // --- Tuple type tests ---

    #[test]
    fn tuple_type_properties() {
        let t = Ty::Tuple(vec![Ty::I32, Ty::Bool]);
        assert_eq!(t.bit_width(), None);
        assert!(!t.is_integer());
        assert!(!t.is_float());
        assert!(!t.is_numeric());
        assert!(!t.is_reference());
    }

    #[test]
    fn display_tuple_types() {
        // The empty tuple is `(,)`, distinct from the unit type `()`.
        assert_eq!(format!("{}", Ty::Tuple(vec![])), "(,)");
        assert_eq!(format!("{}", Ty::Unit), "()");
        assert_ne!(format!("{}", Ty::Tuple(vec![])), format!("{}", Ty::Unit));
        assert_eq!(format!("{}", Ty::Tuple(vec![Ty::I32])), "(i32)");
        assert_eq!(
            format!("{}", Ty::Tuple(vec![Ty::I32, Ty::Bool])),
            "(i32, bool)"
        );
        assert_eq!(
            format!("{}", Ty::Tuple(vec![Ty::I32, Ty::F64, Ty::U8])),
            "(i32, f64, u8)"
        );
    }

    #[test]
    fn tuple_equality() {
        assert_eq!(
            Ty::Tuple(vec![Ty::I32, Ty::Bool]),
            Ty::Tuple(vec![Ty::I32, Ty::Bool])
        );
        assert_ne!(
            Ty::Tuple(vec![Ty::I32, Ty::Bool]),
            Ty::Tuple(vec![Ty::Bool, Ty::I32])
        );
        assert_ne!(Ty::Tuple(vec![Ty::I32]), Ty::Tuple(vec![Ty::I32, Ty::Bool]));
    }

    // --- Enum type tests ---

    #[test]
    fn enum_type_properties() {
        let e = Ty::Enum(EnumId::new(0));
        assert_eq!(e.bit_width(), None);
        assert!(!e.is_integer());
        assert!(!e.is_float());
        assert!(!e.is_numeric());
        assert!(!e.is_reference());
    }

    #[test]
    fn display_enum_type() {
        assert_eq!(format!("{}", Ty::Enum(EnumId::new(0))), "enum.0");
        assert_eq!(format!("{}", Ty::Enum(EnumId::new(42))), "enum.42");
    }

    #[test]
    fn enum_def_construction() {
        let ed = EnumDef {
            id: EnumId::new(0),
            name: "Option".to_string(),
            variants: vec![
                EnumVariant {
                    name: "None".to_string(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "Some".to_string(),
                    fields: vec![Ty::I32],
                    field_names: Vec::new(),
                },
            ],
            discriminants: Vec::new(),
            repr: None,
            layout: None,
        };
        assert_eq!(ed.name, "Option");
        assert_eq!(ed.variants.len(), 2);
        assert_eq!(ed.variants[0].name, "None");
        assert!(ed.variants[0].fields.is_empty());
        assert_eq!(ed.variants[1].name, "Some");
        assert_eq!(ed.variants[1].fields.len(), 1);
    }

    #[test]
    fn enum_equality() {
        assert_eq!(Ty::Enum(EnumId::new(0)), Ty::Enum(EnumId::new(0)));
        assert_ne!(Ty::Enum(EnumId::new(0)), Ty::Enum(EnumId::new(1)));
    }

    // --- canonical enum discriminants + tag repr ---

    fn variants(n: usize) -> Vec<EnumVariant> {
        (0..n)
            .map(|i| EnumVariant {
                name: format!("V{i}"),
                fields: vec![],
                field_names: Vec::new(),
            })
            .collect()
    }

    #[test]
    fn effective_discriminants_follow_the_assignment_rule() {
        // All implicit: 0, 1, 2.
        let implicit = EnumDef::new(EnumId::new(0), "E", variants(3));
        assert_eq!(implicit.effective_discriminants(), Some(vec![0, 1, 2]));

        // Explicit restart mid-way: 0, 10, 11 (implicit = previous + 1).
        let mixed =
            EnumDef::new(EnumId::new(0), "E", variants(3)).with_discriminants(vec![None, Some(10)]);
        assert_eq!(mixed.effective_discriminants(), Some(vec![0, 10, 11]));

        // Negative explicit values are allowed.
        let negative =
            EnumDef::new(EnumId::new(0), "E", variants(2)).with_discriminants(vec![Some(-2)]);
        assert_eq!(negative.effective_discriminants(), Some(vec![-2, -1]));

        // Zero variants: trivially resolvable (empty), but see
        // `canonical_tag_repr` — uninhabited enums have no tag.
        let empty = EnumDef::new(EnumId::new(0), "E", vec![]);
        assert_eq!(empty.effective_discriminants(), Some(vec![]));
    }

    #[test]
    fn effective_discriminants_fail_closed_on_ill_formed_assignments() {
        // Duplicate via explicit collision with an implicit successor:
        // V0=1, V1=2 (implicit), V2=2 (explicit) — ambiguous tag.
        let dup = EnumDef::new(EnumId::new(0), "E", variants(3)).with_discriminants(vec![
            Some(1),
            None,
            Some(2),
        ]);
        assert_eq!(dup.effective_discriminants(), None);

        // Implicit increment overflowing i128.
        let overflow = EnumDef::new(EnumId::new(0), "E", variants(2))
            .with_discriminants(vec![Some(i128::MAX)]);
        assert_eq!(overflow.effective_discriminants(), None);
    }

    #[test]
    fn canonical_tag_repr_picks_the_smallest_fitting_width() {
        // 0..=2 fits u8.
        let small = EnumDef::new(EnumId::new(0), "E", variants(3));
        assert_eq!(small.canonical_tag_repr(), Some(EnumTagRepr::U8));

        // An explicit 1000 forces u16.
        let wide =
            EnumDef::new(EnumId::new(0), "E", variants(2)).with_discriminants(vec![Some(1000)]);
        assert_eq!(wide.canonical_tag_repr(), Some(EnumTagRepr::U16));

        // A negative discriminant switches to the signed ladder.
        let signed =
            EnumDef::new(EnumId::new(0), "E", variants(2)).with_discriminants(vec![Some(-1)]);
        assert_eq!(signed.canonical_tag_repr(), Some(EnumTagRepr::I8));

        // The explicit repr hint wins when it fits...
        let hinted = EnumDef::new(EnumId::new(0), "E", variants(2)).with_repr(EnumTagRepr::U32);
        assert_eq!(hinted.canonical_tag_repr(), Some(EnumTagRepr::U32));

        // ...and fails closed when too narrow for the values.
        let narrow = EnumDef::new(EnumId::new(0), "E", variants(2))
            .with_discriminants(vec![Some(300)])
            .with_repr(EnumTagRepr::U8);
        assert_eq!(narrow.canonical_tag_repr(), None);

        // Uninhabited enums have no canonical tag.
        let empty = EnumDef::new(EnumId::new(0), "E", vec![]);
        assert_eq!(empty.canonical_tag_repr(), None);

        // Beyond the 64-bit cap: no width fits.
        let huge = EnumDef::new(EnumId::new(0), "E", variants(1))
            .with_discriminants(vec![Some(u64::MAX as i128 + 1)]);
        assert_eq!(huge.canonical_tag_repr(), None);
    }

    #[test]
    fn enum_tag_repr_ty_and_fits() {
        assert_eq!(EnumTagRepr::U8.ty(), Ty::U8);
        assert_eq!(EnumTagRepr::I64.ty(), Ty::I64);
        assert!(EnumTagRepr::U8.fits(255));
        assert!(!EnumTagRepr::U8.fits(256));
        assert!(!EnumTagRepr::U8.fits(-1));
        assert!(EnumTagRepr::I8.fits(-128));
        assert!(!EnumTagRepr::I8.fits(-129));
        assert_eq!(EnumTagRepr::smallest_for(0, 255), Some(EnumTagRepr::U8));
        assert_eq!(EnumTagRepr::smallest_for(0, 256), Some(EnumTagRepr::U16));
        assert_eq!(EnumTagRepr::smallest_for(-1, 127), Some(EnumTagRepr::I8));
        assert_eq!(EnumTagRepr::smallest_for(0, u64::MAX as i128 + 1), None);
    }

    // --- Reference type tests ---

    #[test]
    fn ref_type_properties() {
        let r = Ty::Ref(Box::new(Ty::I32));
        // Target-dependent width: None without a target, resolved by target.
        assert_eq!(r.bit_width(), None);
        assert_eq!(r.bit_width_with(64), Some(64));
        assert_eq!(r.bit_width_with(32), Some(32));
        assert!(!r.is_integer());
        assert!(!r.is_float());
        assert!(!r.is_numeric());
        assert!(r.is_reference());
    }

    #[test]
    fn ref_mut_type_properties() {
        let r = Ty::RefMut(Box::new(Ty::I32));
        assert_eq!(r.bit_width(), None);
        assert_eq!(r.bit_width_with(64), Some(64));
        assert!(r.is_reference());
    }

    #[test]
    fn ptr_const_type_properties() {
        let p = Ty::PtrConst(Box::new(Ty::I32));
        assert_eq!(p.bit_width(), None);
        assert_eq!(p.bit_width_with(64), Some(64));
        assert!(p.is_reference());
    }

    #[test]
    fn ptr_mut_type_properties() {
        let p = Ty::PtrMut(Box::new(Ty::I32));
        assert_eq!(p.bit_width(), None);
        assert_eq!(p.bit_width_with(64), Some(64));
        assert!(p.is_reference());
    }

    #[test]
    fn rc_type_properties() {
        let r = Ty::Rc(Box::new(Ty::I32));
        assert_eq!(r.bit_width(), None);
        assert_eq!(r.bit_width_with(64), Some(64));
        assert!(r.is_reference());
    }

    #[test]
    fn display_reference_types() {
        assert_eq!(format!("{}", Ty::Ref(Box::new(Ty::I32))), "&i32");
        assert_eq!(format!("{}", Ty::RefMut(Box::new(Ty::I32))), "&mut i32");
        assert_eq!(format!("{}", Ty::PtrConst(Box::new(Ty::I32))), "*const i32");
        assert_eq!(format!("{}", Ty::PtrMut(Box::new(Ty::I32))), "*mut i32");
        assert_eq!(format!("{}", Ty::Rc(Box::new(Ty::I32))), "Rc<i32>");
    }

    #[test]
    fn display_nested_reference_types() {
        assert_eq!(
            format!("{}", Ty::Ref(Box::new(Ty::RefMut(Box::new(Ty::I32))))),
            "&&mut i32"
        );
        assert_eq!(
            format!("{}", Ty::Rc(Box::new(Ty::Ref(Box::new(Ty::U64))))),
            "Rc<&u64>"
        );
    }

    #[test]
    fn reference_types_not_numeric() {
        assert!(!Ty::Ref(Box::new(Ty::I32)).is_integer());
        assert!(!Ty::RefMut(Box::new(Ty::I32)).is_float());
        assert!(!Ty::PtrConst(Box::new(Ty::I32)).is_numeric());
        assert!(!Ty::PtrMut(Box::new(Ty::I32)).is_signed());
        assert!(!Ty::Rc(Box::new(Ty::I32)).is_unsigned());
    }

    #[test]
    fn reference_equality() {
        assert_eq!(Ty::Ref(Box::new(Ty::I32)), Ty::Ref(Box::new(Ty::I32)));
        assert_ne!(Ty::Ref(Box::new(Ty::I32)), Ty::Ref(Box::new(Ty::I64)));
        assert_ne!(Ty::Ref(Box::new(Ty::I32)), Ty::RefMut(Box::new(Ty::I32)));
    }

    // --- is_reference for non-reference types ---

    #[test]
    fn non_reference_types() {
        assert!(!Ty::I32.is_reference());
        assert!(!Ty::U64.is_reference());
        assert!(!Ty::F32.is_reference());
        assert!(!Ty::Bool.is_reference());
        assert!(!Ty::Ptr.is_reference());
        assert!(!Ty::Unit.is_reference());
        assert!(!Ty::Never.is_reference());
        assert!(!Ty::Struct(StructId::new(0)).is_reference());
        assert!(!Ty::Tuple(vec![Ty::I32]).is_reference());
        assert!(!Ty::Enum(EnumId::new(0)).is_reference());
    }

    // --- Clone tests for heap-allocated types ---

    #[test]
    fn clone_tuple_type() {
        let t = Ty::Tuple(vec![Ty::I32, Ty::F64, Ty::Bool]);
        let cloned = t.clone();
        assert_eq!(t, cloned);
    }

    #[test]
    fn clone_reference_type() {
        let r = Ty::Ref(Box::new(Ty::Tuple(vec![Ty::I32, Ty::U64])));
        let cloned = r.clone();
        assert_eq!(r, cloned);
    }

    #[test]
    fn clone_enum_variant() {
        let ev = EnumVariant {
            name: "Some".to_string(),
            fields: vec![Ty::Ref(Box::new(Ty::I32))],
            field_names: Vec::new(),
        };
        let cloned = ev.clone();
        assert_eq!(ev, cloned);
    }

    // --- Aggregate types (Set / Sequence / Record) and closures (issue #30) ---

    #[test]
    fn set_repr_default_is_boxed() {
        assert_eq!(SetRepr::default(), SetRepr::Boxed);
    }

    #[test]
    fn set_repr_display() {
        assert_eq!(format!("{}", SetRepr::Bitset), "bitset");
        assert_eq!(format!("{}", SetRepr::Boxed), "boxed");
    }

    #[test]
    fn set_type_has_no_bit_width() {
        let s = Ty::Set(TyId::new(3), SetRepr::Boxed);
        assert_eq!(s.bit_width(), None);
        assert!(!s.is_numeric());
        assert!(!s.is_reference());
    }

    #[test]
    fn set_type_equality_includes_repr() {
        // Same element type, different repr hint: distinct types so that
        // lowering decisions are stable and not silently aliased.
        let a = Ty::Set(TyId::new(7), SetRepr::Bitset);
        let b = Ty::Set(TyId::new(7), SetRepr::Boxed);
        let c = Ty::Set(TyId::new(7), SetRepr::Bitset);
        assert_ne!(a, b);
        assert_eq!(a, c);
    }

    #[test]
    fn set_type_display() {
        let s = Ty::Set(TyId::new(4), SetRepr::Bitset);
        assert_eq!(format!("{}", s), "set<ty.4, bitset>");
        let s2 = Ty::Set(TyId::new(0), SetRepr::Boxed);
        assert_eq!(format!("{}", s2), "set<ty.0, boxed>");
    }

    #[test]
    fn sequence_type_basic_properties() {
        let s = Ty::Sequence(TyId::new(9));
        assert_eq!(s.bit_width(), None);
        assert!(!s.is_numeric());
        assert!(!s.is_reference());
        assert_eq!(format!("{}", s), "seq<ty.9>");
    }

    #[test]
    fn sequence_equality() {
        assert_eq!(Ty::Sequence(TyId::new(1)), Ty::Sequence(TyId::new(1)));
        assert_ne!(Ty::Sequence(TyId::new(1)), Ty::Sequence(TyId::new(2)));
    }

    #[test]
    fn record_type_basic_properties() {
        let r = Ty::Record(RecordId::new(2));
        assert_eq!(r.bit_width(), None);
        assert!(!r.is_numeric());
        assert!(!r.is_reference());
        assert_eq!(format!("{}", r), "record.2");
    }

    #[test]
    fn record_def_holds_named_fields() {
        let rd = RecordDef {
            id: RecordId::new(0),
            name: "Point".to_string(),
            fields: vec![
                FieldDef {
                    name: "x".to_string(),
                    ty: Ty::I32,
                    offset: None,
                },
                FieldDef {
                    name: "y".to_string(),
                    ty: Ty::I32,
                    offset: None,
                },
            ],
        };
        assert_eq!(rd.name, "Point");
        assert_eq!(rd.fields.len(), 2);
        // Records have no layout, so offset must be None.
        for f in &rd.fields {
            assert!(f.offset.is_none());
        }
    }

    #[test]
    fn record_is_distinct_from_struct() {
        // Record and Struct sharing the same numeric id are different Ty
        // variants — distinct in the type system and in Display.
        let r = Ty::Record(RecordId::new(5));
        let s = Ty::Struct(StructId::new(5));
        assert_ne!(r, s);
        assert_ne!(format!("{}", r), format!("{}", s));
    }

    #[test]
    fn closure_type_basic_properties() {
        let c = Ty::Closure(ClosureTyId::new(1));
        assert_eq!(c.bit_width(), None);
        assert!(!c.is_numeric());
        assert!(!c.is_reference());
        assert_eq!(format!("{}", c), "closure.1");
    }

    #[test]
    fn closure_ty_bare_has_no_captures() {
        let c = ClosureTy::bare(FuncTyId::new(3));
        assert_eq!(c.func, FuncTyId::new(3));
        assert_eq!(c.capture_count(), 0);
        assert!(c.captures.is_empty());
    }

    #[test]
    fn closure_ty_with_captures() {
        let c = ClosureTy {
            func: FuncTyId::new(2),
            captures: vec![Ty::I32, Ty::Ref(Box::new(Ty::U64))],
        };
        assert_eq!(c.capture_count(), 2);
        assert_eq!(c.captures[0], Ty::I32);
    }

    #[test]
    fn closure_ty_captures_are_part_of_identity() {
        // This is the ty#4145 soundness lesson in type form: two closures
        // over the same function signature but with different captured
        // environments are NOT the same type. Self-referential FuncDef routes
        // its captured state partition through the closure type identity, so
        // changes to captured values yield a new type rather than a stale
        // cached body.
        let base = FuncTyId::new(7);
        let c_no_cap = ClosureTy::bare(base);
        let c_one_cap = ClosureTy {
            func: base,
            captures: vec![Ty::I32],
        };
        let c_one_cap_different = ClosureTy {
            func: base,
            captures: vec![Ty::I64],
        };

        assert_ne!(c_no_cap, c_one_cap);
        assert_ne!(c_one_cap, c_one_cap_different);

        // Same func + same captures = same type.
        let c_one_cap_dup = ClosureTy {
            func: base,
            captures: vec![Ty::I32],
        };
        assert_eq!(c_one_cap, c_one_cap_dup);
    }

    #[test]
    fn is_aggregate_classification() {
        // Aggregates: Set, Sequence, Record, Tuple, Array, Struct, Enum.
        assert!(Ty::Set(TyId::new(0), SetRepr::Boxed).is_aggregate());
        assert!(Ty::Sequence(TyId::new(0)).is_aggregate());
        assert!(Ty::Record(RecordId::new(0)).is_aggregate());
        assert!(Ty::Tuple(vec![Ty::I32, Ty::Bool]).is_aggregate());
        assert!(Ty::Array(TyId::new(0), 4).is_aggregate());
        assert!(Ty::Struct(StructId::new(0)).is_aggregate());
        assert!(Ty::Enum(EnumId::new(0)).is_aggregate());

        // Non-aggregates.
        assert!(!Ty::I32.is_aggregate());
        assert!(!Ty::Bool.is_aggregate());
        assert!(!Ty::Ptr.is_aggregate());
        assert!(!Ty::Ref(Box::new(Ty::I32)).is_aggregate());
        assert!(!Ty::Closure(ClosureTyId::new(0)).is_aggregate());
        assert!(!Ty::Func(FuncTyId::new(0)).is_aggregate());
        assert!(!Ty::Vector(Box::new(Ty::I32), 4).is_aggregate());
    }

    #[test]
    fn refine_classification_and_spelling() {
        let refined = Ty::Refine(TyId::new(3), PredId::new(7));
        assert!(refined.is_refine());
        assert_eq!(refined.refinement(), Some((TyId::new(3), PredId::new(7))));
        assert_eq!(refined.predicate(), Some(PredId::new(7)));
        assert_eq!(format!("{refined}"), "refine<ty.3, pred.7>");

        // An UNREFINED type carries no predicate. At a consumption site that
        // `None` means `Pred::Top` — no information — never "no constraint".
        assert_eq!(Ty::I64.predicate(), None);
        assert!(!Ty::I64.is_refine());

        // Representation-preserving: a refinement is not an aggregate, not a
        // reference, and reports no context-free width of its own (the base
        // type in the module table answers all three).
        assert!(!refined.is_aggregate());
        assert!(!refined.is_reference());
        assert!(!refined.is_numeric());
        assert_eq!(refined.bit_width(), None);
        assert_eq!(refined.bit_width_with(64), None);
        // And it can never hide a producer-internal Error in its inline
        // surface — there is no inline surface.
        assert!(!refined.contains_error());
    }

    #[test]
    fn is_closure_classification() {
        assert!(Ty::Closure(ClosureTyId::new(0)).is_closure());
        // Func is not a closure (no captured environment).
        assert!(!Ty::Func(FuncTyId::new(0)).is_closure());
        assert!(!Ty::I32.is_closure());
        assert!(!Ty::Ref(Box::new(Ty::I32)).is_closure());
    }

    #[test]
    fn new_types_do_not_report_reference_or_numeric() {
        let samples = [
            Ty::Set(TyId::new(0), SetRepr::Boxed),
            Ty::Set(TyId::new(0), SetRepr::Bitset),
            Ty::Sequence(TyId::new(0)),
            Ty::Record(RecordId::new(0)),
            Ty::Closure(ClosureTyId::new(0)),
        ];
        for t in &samples {
            assert!(!t.is_reference(), "{:?} must not be a reference", t);
            assert!(!t.is_numeric(), "{:?} must not be numeric", t);
            assert!(!t.is_integer(), "{:?} must not be integer", t);
            assert!(!t.is_float(), "{:?} must not be float", t);
        }
    }

    #[test]
    fn vector_type_classification_and_display() {
        let v4i32 = Ty::v4_i32();
        let v4bool = Ty::v4_bool();
        let v8bool = Ty::Vector(Box::new(Ty::Bool), 8);
        let v2f64 = Ty::Vector(Box::new(Ty::F64), 2);

        assert!(v4i32.is_vector());
        assert_eq!(v4i32.vector_shape(), Some((&Ty::I32, 4)));
        assert_eq!(v4i32.bit_width(), Some(128));
        assert!(v4i32.is_integer_vector());
        assert!(!v4i32.is_integer());
        assert!(!v4i32.is_numeric());
        assert_eq!(format!("{v4i32}"), "<4 x i32>");

        assert!(v4bool.is_bool_vector());
        assert_eq!(v4bool.vector_shape(), Some((&Ty::Bool, 4)));
        assert_eq!(format!("{v4bool}"), "<4 x bool>");

        assert!(v8bool.is_bool_vector());
        assert_eq!(v8bool.bit_width(), Some(8));
        assert_eq!(v4i32.comparison_result_ty(), Ty::v4_bool());
        assert_eq!(v4i32.select_condition_ty(), Ty::v4_bool());
        assert_eq!(Ty::I32.select_condition_ty(), Ty::Bool);
        assert!(v4i32.is_integer_vector_mask_for_select_ty(&v4i32));
        assert!(!v8bool.is_integer_vector_mask_for_select_ty(&v4i32));
        assert!(!Ty::Vector(Box::new(Ty::I32), 8).is_integer_vector_mask_for_select_ty(&v4i32));

        assert!(v2f64.is_float_vector());
        assert_eq!(format!("{v2f64}"), "<2 x f64>");
    }

    #[test]
    fn clone_new_types() {
        let set = Ty::Set(TyId::new(1), SetRepr::Bitset);
        assert_eq!(set.clone(), set);
        let seq = Ty::Sequence(TyId::new(2));
        assert_eq!(seq.clone(), seq);
        let rec = Ty::Record(RecordId::new(3));
        assert_eq!(rec.clone(), rec);
        let clos = Ty::Closure(ClosureTyId::new(4));
        assert_eq!(clos.clone(), clos);
        let vec_ty = Ty::Vector(Box::new(Ty::U64), 2);
        assert_eq!(vec_ty.clone(), vec_ty);

        let cty = ClosureTy {
            func: FuncTyId::new(0),
            captures: vec![Ty::I32, Ty::Bool],
        };
        assert_eq!(cty.clone(), cty);

        let rd = RecordDef {
            id: RecordId::new(0),
            name: "R".to_string(),
            fields: vec![FieldDef {
                name: "x".to_string(),
                ty: Ty::I32,
                offset: None,
            }],
        };
        assert_eq!(rd.clone(), rd);
    }

    /// B2-3: the trait-object id mint is a pinned convention, not an
    /// implementation detail — frontends on both sides of a differential
    /// derive it independently and the ids must collide iff the def paths do.
    /// These constants are FROZEN; a change here is a format-level break.
    #[test]
    fn stable_trait_object_id_is_pinned() {
        assert_eq!(stable_trait_object_id(""), 0x811c_9dc5); // FNV-1a offset basis
        assert_eq!(stable_trait_object_id("core::fmt::Debug"), 0x01bd_d3c8);
        assert_eq!(stable_trait_object_id("core::fmt::Display"), 0xdefd_84c5);
        // distinct def paths -> distinct ids (the everyday non-collision case)
        assert_ne!(
            stable_trait_object_id("core::fmt::Debug"),
            stable_trait_object_id("core::fmt::Display"),
        );
    }

    /// vtable slice 3: the vtable-global name mint is a pinned convention —
    /// both sides of a differential derive it independently and the names must
    /// be equal iff the `(principal, source)` pairs are. The literal shape is
    /// FROZEN; a change here re-keys every minted vtable identity.
    #[test]
    fn stable_vtable_global_name_is_pinned_and_injective() {
        assert_eq!(
            stable_vtable_global_name("core::fmt::Debug", "i32").as_deref(),
            Some("__trust_vtable__core::fmt::Debug$i32__"),
        );
        // Same pair -> same name; either component differing -> different name.
        assert_eq!(
            stable_vtable_global_name("core::fmt::Debug", "i32"),
            stable_vtable_global_name("core::fmt::Debug", "i32"),
        );
        assert_ne!(
            stable_vtable_global_name("core::fmt::Debug", "i32"),
            stable_vtable_global_name("core::fmt::Debug", "u32"),
        );
        assert_ne!(
            stable_vtable_global_name("core::fmt::Debug", "i32"),
            stable_vtable_global_name("core::fmt::Display", "i32"),
        );
        // Injectivity across the component boundary: a principal that ends in
        // what a source key starts with must not merge with the re-split pair.
        // (`$` never occurs in a canonical source key, so the LAST `$` in the
        // payload is the one this mint wrote.)
        assert_ne!(
            stable_vtable_global_name("a::b", "c(d)"),
            stable_vtable_global_name("a", "b$c(d)"), // refused outright below
        );
        // Fail-closed refusals: empty components, and a `$` in the source key
        // (which would make the payload ambiguous to re-split).
        assert_eq!(stable_vtable_global_name("", "i32"), None);
        assert_eq!(stable_vtable_global_name("core::fmt::Debug", ""), None);
        assert_eq!(stable_vtable_global_name("core::fmt::Debug", "a$b"), None);
        // A `$` in the PRINCIPAL is tolerated: the source key carries none, so
        // splitting at the last `$` still recovers the pair uniquely.
        assert_eq!(
            stable_vtable_global_name("weird$path", "i32").as_deref(),
            Some("__trust_vtable__weird$path$i32__"),
        );
    }
}
