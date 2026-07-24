// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core flat format data types: `FlatTag`, `FlatFlags`, `FlatExpr`, `FlatLevel`.

use super::error::FlatError;

/// Expression tag values for flat format.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FlatTag {
    /// Bound variable (de Bruijn index): data = u32 index
    BVar = 0,
    /// Sort (Type u): data = u32 level_idx
    Sort = 1,
    /// Constant: data = u32 name_idx, u32 levels_list_idx (into level_lists table)
    Const = 2,
    /// Application: data = u32 fn_idx, u32 arg_idx
    App = 3,
    /// Lambda: data = u8 binder_info, u32 ty_idx, u32 body_idx
    Lam = 4,
    /// Pi/Forall: data = u8 binder_info, u32 ty_idx, u32 body_idx
    Pi = 5,
    /// Let: data = u32 ty_idx, u32 val_idx, u32 body_idx
    Let = 6,
    /// Natural literal: data = u64 value (first 8 bytes)
    LitNat = 7,
    /// String literal: data = u32 string_idx
    LitStr = 8,
    /// Projection: data = u32 name_idx, u16 field, u32 expr_idx
    Proj = 9,
    /// Free variable: data = u64 fvar_id
    FVar = 10,
}

impl TryFrom<u8> for FlatTag {
    type Error = FlatError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Self::BVar),
            1 => Ok(Self::Sort),
            2 => Ok(Self::Const),
            3 => Ok(Self::App),
            4 => Ok(Self::Lam),
            5 => Ok(Self::Pi),
            6 => Ok(Self::Let),
            7 => Ok(Self::LitNat),
            8 => Ok(Self::LitStr),
            9 => Ok(Self::Proj),
            10 => Ok(Self::FVar),
            _ => Err(FlatError::InvalidTag(value)),
        }
    }
}

/// Flat expression flags.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FlatFlags(pub(crate) u8);

impl FlatFlags {
    /// Expression is verified (type-checked).
    pub const VERIFIED: FlatFlags = FlatFlags(0x01);
    /// Expression has free variables.
    pub const HAS_FVAR: FlatFlags = FlatFlags(0x02);
    /// Expression has loose bound variables.
    pub const HAS_LOOSE_BVAR: FlatFlags = FlatFlags(0x04);
    /// Expression contains metavariables (for partial proofs).
    pub const HAS_MVAR: FlatFlags = FlatFlags(0x08);
    /// Expression was downgraded from unsupported variant (e.g., cubical, ZFC).
    /// Verification should treat these as opaque/unverifiable.
    pub const UNSUPPORTED: FlatFlags = FlatFlags(0x10);
    /// LitNat whose value exceeds u64::MAX: `data[0..4]` is a STRING-table index
    /// to the comma-separated decimal little-endian u64 limbs of the BigNat (the
    /// inline u64 in `data[0..8]` is unused). Lets the otherwise u64-only Nat
    /// literal carry arbitrary-precision Nats (e.g. `USize.size = 2^64`) so the
    /// shard round-trips them faithfully instead of dropping the constant.
    pub const NAT_BIG: FlatFlags = FlatFlags(0x20);

    /// Create empty flags.
    #[inline]
    pub const fn empty() -> Self {
        FlatFlags(0)
    }

    /// Check if flag is set.
    #[inline]
    pub const fn contains(self, other: FlatFlags) -> bool {
        (self.0 & other.0) == other.0
    }

    /// Set flag.
    #[inline]
    pub const fn with(self, other: FlatFlags) -> Self {
        FlatFlags(self.0 | other.0)
    }

    /// Raw flag bits (for writers in other crates that build a `FlatExpr`'s
    /// `flags` byte directly, e.g. marking a node UNSUPPORTED).
    #[inline]
    pub const fn bits(self) -> u8 {
        self.0
    }
}

/// 16-byte aligned flat expression (cache-line friendly).
///
/// All expressions are exactly 16 bytes, enabling:
/// - Direct memory mapping with no deserialization
/// - Linear array access with predictable cache behavior
/// - Lock-free parallel reads
#[repr(C, align(16))]
#[derive(Clone, Copy, Debug)]
pub struct FlatExpr {
    /// Expression variant tag.
    pub tag: u8,
    /// Metadata flags.
    pub flags: u8,
    /// Alignment padding.
    pub(crate) _pad: [u8; 2],
    /// Variant-specific data (12 bytes).
    pub data: [u8; 12],
}

impl FlatExpr {
    /// Size of a FlatExpr in bytes.
    pub const SIZE: usize = 16;

    /// Create a BVar expression.
    ///
    /// # Contract
    ///
    /// REQUIRES: `idx` is a valid de Bruijn index within the expression's context
    /// ENSURES: `result.tag() == Ok(FlatTag::BVar)`
    /// ENSURES: `result.flags().contains(FlatFlags::HAS_LOOSE_BVAR)`
    #[inline]
    pub fn bvar(idx: u32) -> Self {
        let mut data = [0u8; 12];
        data[0..4].copy_from_slice(&idx.to_le_bytes());
        Self {
            tag: FlatTag::BVar as u8,
            flags: FlatFlags::HAS_LOOSE_BVAR.0,
            _pad: [0, 0],
            data,
        }
    }

    /// Create a Sort expression.
    ///
    /// # Contract
    ///
    /// REQUIRES: `level_idx < builder.level_count()` when used with a FlatBuilder
    /// ENSURES: `result.tag() == Ok(FlatTag::Sort)`
    #[inline]
    pub fn sort(level_idx: u32) -> Self {
        let mut data = [0u8; 12];
        data[0..4].copy_from_slice(&level_idx.to_le_bytes());
        Self {
            tag: FlatTag::Sort as u8,
            flags: 0,
            _pad: [0, 0],
            data,
        }
    }

    /// Create a Const expression.
    ///
    /// # Contract
    ///
    /// REQUIRES: `name_idx < builder.name_count()` when used with a FlatBuilder
    /// REQUIRES: `levels_list_idx` is valid offset in level_lists table, or `u32::MAX` (no levels)
    /// ENSURES: `result.tag() == Ok(FlatTag::Const)`
    ///
    /// Note: `levels_list_idx` points to the level_lists table (not level table), supporting
    /// multi-level universe polymorphism (#1162). The format at that offset is:
    /// [count: u32, level_idx_0: u32, ..., level_idx_N: u32]
    #[inline]
    pub fn const_ref(name_idx: u32, levels_list_idx: u32) -> Self {
        let mut data = [0u8; 12];
        data[0..4].copy_from_slice(&name_idx.to_le_bytes());
        data[4..8].copy_from_slice(&levels_list_idx.to_le_bytes());
        Self {
            tag: FlatTag::Const as u8,
            flags: 0,
            _pad: [0, 0],
            data,
        }
    }

    /// Create an App expression.
    ///
    /// # Contract
    ///
    /// REQUIRES: `fn_idx < builder.expr_count()` when used with a FlatBuilder
    /// REQUIRES: `arg_idx < builder.expr_count()` when used with a FlatBuilder
    /// ENSURES: `result.tag() == Ok(FlatTag::App)`
    #[inline]
    pub fn app(fn_idx: u32, arg_idx: u32) -> Self {
        let mut data = [0u8; 12];
        data[0..4].copy_from_slice(&fn_idx.to_le_bytes());
        data[4..8].copy_from_slice(&arg_idx.to_le_bytes());
        Self {
            tag: FlatTag::App as u8,
            flags: 0,
            _pad: [0, 0],
            data,
        }
    }

    /// Create a Lam expression.
    ///
    /// # Contract
    ///
    /// REQUIRES: `binder_info <= 3` (0=Default, 1=Implicit, 2=StrictImplicit, 3=InstImplicit)
    /// REQUIRES: `ty_idx < builder.expr_count()` when used with a FlatBuilder
    /// REQUIRES: `body_idx < builder.expr_count()` when used with a FlatBuilder
    /// ENSURES: `result.tag() == Ok(FlatTag::Lam)`
    #[inline]
    pub fn lam(binder_info: u8, ty_idx: u32, body_idx: u32) -> Self {
        let mut data = [0u8; 12];
        data[0] = binder_info;
        data[1..5].copy_from_slice(&ty_idx.to_le_bytes());
        data[5..9].copy_from_slice(&body_idx.to_le_bytes());
        Self {
            tag: FlatTag::Lam as u8,
            flags: 0,
            _pad: [0, 0],
            data,
        }
    }

    /// Create a Pi expression.
    ///
    /// # Contract
    ///
    /// REQUIRES: `binder_info <= 3` (0=Default, 1=Implicit, 2=StrictImplicit, 3=InstImplicit)
    /// REQUIRES: `ty_idx < builder.expr_count()` when used with a FlatBuilder
    /// REQUIRES: `body_idx < builder.expr_count()` when used with a FlatBuilder
    /// ENSURES: `result.tag() == Ok(FlatTag::Pi)`
    #[inline]
    pub fn pi(binder_info: u8, ty_idx: u32, body_idx: u32) -> Self {
        let mut data = [0u8; 12];
        data[0] = binder_info;
        data[1..5].copy_from_slice(&ty_idx.to_le_bytes());
        data[5..9].copy_from_slice(&body_idx.to_le_bytes());
        Self {
            tag: FlatTag::Pi as u8,
            flags: 0,
            _pad: [0, 0],
            data,
        }
    }

    /// Create a Let expression.
    ///
    /// # Contract
    ///
    /// REQUIRES: `ty_idx < builder.expr_count()` when used with a FlatBuilder
    /// REQUIRES: `val_idx < builder.expr_count()` when used with a FlatBuilder
    /// REQUIRES: `body_idx < builder.expr_count()` when used with a FlatBuilder
    /// ENSURES: `result.tag() == Ok(FlatTag::Let)`
    #[inline]
    pub fn let_expr(ty_idx: u32, val_idx: u32, body_idx: u32) -> Self {
        let mut data = [0u8; 12];
        data[0..4].copy_from_slice(&ty_idx.to_le_bytes());
        data[4..8].copy_from_slice(&val_idx.to_le_bytes());
        data[8..12].copy_from_slice(&body_idx.to_le_bytes());
        Self {
            tag: FlatTag::Let as u8,
            flags: 0,
            _pad: [0, 0],
            data,
        }
    }

    /// Create a Nat literal expression.
    ///
    /// # Contract
    ///
    /// ENSURES: `result.tag() == Ok(FlatTag::LitNat)`
    /// ENSURES: `result.read_u64(0) == Ok(value)`
    #[inline]
    pub fn lit_nat(value: u64) -> Self {
        let mut data = [0u8; 12];
        data[0..8].copy_from_slice(&value.to_le_bytes());
        Self {
            tag: FlatTag::LitNat as u8,
            flags: 0,
            _pad: [0, 0],
            data,
        }
    }

    /// Create a String literal expression.
    ///
    /// # Contract
    ///
    /// REQUIRES: `string_idx < builder.string_count()` when used with a FlatBuilder
    /// ENSURES: `result.tag() == Ok(FlatTag::LitStr)`
    #[inline]
    pub fn lit_str(string_idx: u32) -> Self {
        let mut data = [0u8; 12];
        data[0..4].copy_from_slice(&string_idx.to_le_bytes());
        Self {
            tag: FlatTag::LitStr as u8,
            flags: 0,
            _pad: [0, 0],
            data,
        }
    }

    /// Create a Proj expression.
    ///
    /// # Contract
    ///
    /// REQUIRES: `name_idx < builder.name_count()` when used with a FlatBuilder
    /// REQUIRES: `expr_idx < builder.expr_count()` when used with a FlatBuilder
    /// ENSURES: `result.tag() == Ok(FlatTag::Proj)`
    #[inline]
    pub fn proj(name_idx: u32, field: u16, expr_idx: u32) -> Self {
        let mut data = [0u8; 12];
        data[0..4].copy_from_slice(&name_idx.to_le_bytes());
        data[4..6].copy_from_slice(&field.to_le_bytes());
        data[6..10].copy_from_slice(&expr_idx.to_le_bytes());
        Self {
            tag: FlatTag::Proj as u8,
            flags: 0,
            _pad: [0, 0],
            data,
        }
    }

    /// Create a FVar expression.
    ///
    /// # Contract
    ///
    /// ENSURES: `result.tag() == Ok(FlatTag::FVar)`
    /// ENSURES: `result.flags().contains(FlatFlags::HAS_FVAR)`
    #[inline]
    pub fn fvar(id: u64) -> Self {
        let mut data = [0u8; 12];
        data[0..8].copy_from_slice(&id.to_le_bytes());
        Self {
            tag: FlatTag::FVar as u8,
            flags: FlatFlags::HAS_FVAR.0,
            _pad: [0, 0],
            data,
        }
    }

    /// Get the tag as an enum.
    #[inline]
    pub fn tag(&self) -> Result<FlatTag, FlatError> {
        FlatTag::try_from(self.tag)
    }

    /// Get flags as struct.
    #[inline]
    pub fn flags(&self) -> FlatFlags {
        FlatFlags(self.flags)
    }

    /// Set the verified flag.
    #[inline]
    pub fn set_verified(&mut self) {
        self.flags |= FlatFlags::VERIFIED.0;
    }

    /// Check if expression is verified.
    #[inline]
    pub fn is_verified(&self) -> bool {
        (self.flags & FlatFlags::VERIFIED.0) != 0
    }

    /// Read u32 from data at offset.
    #[inline]
    pub fn read_u32(&self, offset: usize) -> Result<u32, FlatError> {
        Ok(u32::from_le_bytes(self.read_fixed::<4>(offset)?))
    }

    /// Read u64 from data at offset.
    #[inline]
    pub fn read_u64(&self, offset: usize) -> Result<u64, FlatError> {
        Ok(u64::from_le_bytes(self.read_fixed::<8>(offset)?))
    }

    /// Read u16 from data at offset.
    #[inline]
    pub fn read_u16(&self, offset: usize) -> Result<u16, FlatError> {
        Ok(u16::from_le_bytes(self.read_fixed::<2>(offset)?))
    }

    #[inline]
    fn read_fixed<const N: usize>(&self, offset: usize) -> Result<[u8; N], FlatError> {
        let end = offset.checked_add(N).ok_or(FlatError::TruncatedData)?;
        let slice = self.data.get(offset..end).ok_or(FlatError::TruncatedData)?;
        let mut out = [0u8; N];
        out.copy_from_slice(slice);
        Ok(out)
    }
}

/// Flat universe level representation.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct FlatLevel {
    /// Level tag.
    pub tag: u8,
    /// Padding.
    pub(crate) _pad: [u8; 3],
    /// Level data (depends on tag).
    pub data: [u8; 8],
}

impl FlatLevel {
    /// Size of a FlatLevel in bytes.
    pub const SIZE: usize = 12;

    /// Level zero.
    pub const TAG_ZERO: u8 = 0;
    /// Level successor.
    pub const TAG_SUCC: u8 = 1;
    /// Level max.
    pub const TAG_MAX: u8 = 2;
    /// Level imax.
    pub const TAG_IMAX: u8 = 3;
    /// Level parameter.
    pub const TAG_PARAM: u8 = 4;
    // Note: TAG_MVAR (5) was removed - kernel Level enum doesn't have MVar variant.
    // The flat format is for serialized, fully-elaborated expressions only.

    /// Create a zero level.
    ///
    /// # Contract
    ///
    /// ENSURES: `result.tag == Self::TAG_ZERO`
    pub fn zero() -> Self {
        Self {
            tag: Self::TAG_ZERO,
            _pad: [0; 3],
            data: [0; 8],
        }
    }

    /// Create a successor level.
    ///
    /// # Contract
    ///
    /// REQUIRES: `inner_idx < builder.level_count()` when used with a FlatBuilder
    /// ENSURES: `result.tag == Self::TAG_SUCC`
    pub fn succ(inner_idx: u32) -> Self {
        let mut data = [0u8; 8];
        data[0..4].copy_from_slice(&inner_idx.to_le_bytes());
        Self {
            tag: Self::TAG_SUCC,
            _pad: [0; 3],
            data,
        }
    }

    /// Create a max level.
    ///
    /// # Contract
    ///
    /// REQUIRES: `left_idx < builder.level_count()` when used with a FlatBuilder
    /// REQUIRES: `right_idx < builder.level_count()` when used with a FlatBuilder
    /// ENSURES: `result.tag == Self::TAG_MAX`
    pub fn max(left_idx: u32, right_idx: u32) -> Self {
        let mut data = [0u8; 8];
        data[0..4].copy_from_slice(&left_idx.to_le_bytes());
        data[4..8].copy_from_slice(&right_idx.to_le_bytes());
        Self {
            tag: Self::TAG_MAX,
            _pad: [0; 3],
            data,
        }
    }

    /// Create a param level.
    ///
    /// # Contract
    ///
    /// REQUIRES: `name_idx < builder.name_count()` when used with a FlatBuilder
    /// ENSURES: `result.tag == Self::TAG_PARAM`
    pub fn param(name_idx: u32) -> Self {
        let mut data = [0u8; 8];
        data[0..4].copy_from_slice(&name_idx.to_le_bytes());
        Self {
            tag: Self::TAG_PARAM,
            _pad: [0; 3],
            data,
        }
    }
}
