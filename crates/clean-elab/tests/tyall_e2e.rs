// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! ALL TRUST TYPES ARE *ONE* CLEAN TYPE — the entire trust-ir `Ty` enum
//! (first-party/trust-ir/crates/trust-ir/src/ty.rs) modeled as a SINGLE Clean
//! inductive `TyAll` (33 constructors, the exact enum), with all 11 classifiers
//! (`bit_width`/`bit_width_with`/`is_signed`/`is_unsigned`/`is_integer`/
//! `is_float`/`is_numeric`/`is_vector`/`is_reference`/`is_aggregate`/`is_closure`)
//! faithful to the Rust method bodies, PLUS cross-cutting STRUCTURAL metatheorems
//! that the four separate slices in `tyfull_e2e.rs` cannot express:
//!
//!   * partition/disjointness — signed/unsigned disjoint, integer/float disjoint,
//!     vector not numeric, aggregate/closure disjoint, reference/numeric disjoint;
//!   * width-coherence — `is_reference`/`is_aggregate`/`is_closure` ⇒ no fixed
//!     `bit_width`; `bit_width_with` agrees with `bit_width` off the pointer path;
//!     fat pointer = two thin pointers;
//!   * exhaustiveness/structure — the classifiers COVER every constructor
//!     (`coverAll t = true` for all t), `comparison_result_ty = select_condition_ty`,
//!     `vector_shape` coheres with `is_vector`, and the has-width set is exact.
//!
//! Every theorem passes the SAME `axiom_deps(name).is_empty()` bedrock gate that
//! `axiom_bedrock_check.rs` proves is real and discriminating — so the whole
//! `Ty` enum, as one Clean inductive with proven structure, rests only on the 3
//! foundational axioms.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

const TYALL_SOURCE: &str = r#"
namespace TyAll

inductive FatKindA where
  | fpslice : Nat -> FatKindA
  | fpstr : FatKindA
  | fptraitobj : Nat -> FatKindA

inductive SetReprA where
  | bitset : SetReprA
  | boxed : SetReprA

inductive TyAll where
  | i8 : TyAll
  | i16 : TyAll
  | i32 : TyAll
  | i64 : TyAll
  | i128 : TyAll
  | u8 : TyAll
  | u16 : TyAll
  | u32 : TyAll
  | u64 : TyAll
  | u128 : TyAll
  | f16 : TyAll
  | f32 : TyAll
  | f64 : TyAll
  | tbool : TyAll
  | vector : TyAll -> Nat -> TyAll
  | ptr : TyAll
  | fatptr : FatKindA -> TyAll
  | tunit : TyAll
  | never : TyAll
  | tstruct : Nat -> TyAll
  | tarray : Nat -> Nat -> TyAll
  | ttuple : TyAll -> TyAll -> TyAll
  | tenum : Nat -> TyAll
  | tfunc : Nat -> TyAll
  | tref : TyAll -> TyAll
  | trefmut : TyAll -> TyAll
  | tptrconst : TyAll -> TyAll
  | tptrmut : TyAll -> TyAll
  | trc : TyAll -> TyAll
  | tset : Nat -> SetReprA -> TyAll
  | tseq : Nat -> TyAll
  | trecord : Nat -> TyAll
  | tclosure : Nat -> TyAll

-- `Ty::bit_width` (ty.rs:142, target-free). Vector recurses on its element width
-- (=> @TyAll.rec). Scalars give fixed widths; pointers/aggregates/etc -> none.
def bitWidth : TyAll -> Option Nat := fun t =>
  @TyAll.rec (fun _ => Option Nat)
    (Option.some 8)              -- i8
    (Option.some 16)             -- i16
    (Option.some 32)             -- i32
    (Option.some 64)             -- i64
    (Option.some 128)            -- i128
    (Option.some 8)              -- u8
    (Option.some 16)             -- u16
    (Option.some 32)             -- u32
    (Option.some 64)             -- u64
    (Option.some 128)            -- u128
    (Option.some 16)             -- f16
    (Option.some 32)             -- f32
    (Option.some 64)             -- f64
    (Option.some 1)              -- tbool
    (fun _e n ihE =>             -- vector(e,n): elem width * lanes (checked)
      @Option.casesOn Nat (fun _ => Option Nat) ihE
        Option.none
        (fun w => Option.some (Nat.mul w n)))
    Option.none                  -- ptr
    (fun _k => Option.none)      -- fatptr
    Option.none                  -- tunit
    Option.none                  -- never
    (fun _id => Option.none)     -- tstruct
    (fun _el _len => Option.none) -- tarray
    (fun _a _b _iha _ihb => Option.none) -- ttuple
    (fun _id => Option.none)     -- tenum
    (fun _id => Option.none)     -- tfunc
    (fun _a _iha => Option.none) -- tref
    (fun _a _iha => Option.none) -- trefmut
    (fun _a _iha => Option.none) -- tptrconst
    (fun _a _iha => Option.none) -- tptrmut
    (fun _a _iha => Option.none) -- trc
    (fun _el _r => Option.none)  -- tset
    (fun _el => Option.none)     -- tseq
    (fun _id => Option.none)     -- trecord
    (fun _id => Option.none)     -- tclosure
    t

-- `Ty::is_signed` (ty.rs:196): i8..i128 only.
def isSigned : TyAll -> Bool := fun t =>
  @TyAll.casesOn (fun _ => Bool) t
    true true true true true     -- i8 i16 i32 i64 i128
    false false false false false -- u8 u16 u32 u64 u128
    false false false            -- f16 f32 f64
    false                        -- tbool
    (fun _e _n => false)         -- vector
    false                        -- ptr
    (fun _k => false)            -- fatptr
    false                        -- tunit
    false                        -- never
    (fun _id => false)           -- tstruct
    (fun _el _len => false)      -- tarray
    (fun _a _b => false)         -- ttuple
    (fun _id => false)           -- tenum
    (fun _id => false)           -- tfunc
    (fun _a => false)            -- tref
    (fun _a => false)            -- trefmut
    (fun _a => false)            -- tptrconst
    (fun _a => false)            -- tptrmut
    (fun _a => false)            -- trc
    (fun _el _r => false)        -- tset
    (fun _el => false)           -- tseq
    (fun _id => false)           -- trecord
    (fun _id => false)           -- tclosure

-- `Ty::is_unsigned` (ty.rs:201): u8..u128 only.
def isUnsigned : TyAll -> Bool := fun t =>
  @TyAll.casesOn (fun _ => Bool) t
    false false false false false -- i8 i16 i32 i64 i128
    true true true true true     -- u8 u16 u32 u64 u128
    false false false            -- f16 f32 f64
    false                        -- tbool
    (fun _e _n => false)         -- vector
    false                        -- ptr
    (fun _k => false)            -- fatptr
    false                        -- tunit
    false                        -- never
    (fun _id => false)           -- tstruct
    (fun _el _len => false)      -- tarray
    (fun _a _b => false)         -- ttuple
    (fun _id => false)           -- tenum
    (fun _id => false)           -- tfunc
    (fun _a => false)            -- tref
    (fun _a => false)            -- trefmut
    (fun _a => false)            -- tptrconst
    (fun _a => false)            -- tptrmut
    (fun _a => false)            -- trc
    (fun _el _r => false)        -- tset
    (fun _el => false)           -- tseq
    (fun _id => false)           -- trecord
    (fun _id => false)           -- tclosure

-- `Ty::is_integer` (ty.rs:191) = is_signed || is_unsigned.
def isInteger : TyAll -> Bool := fun t => Bool.or (isSigned t) (isUnsigned t)

-- `Ty::is_float` (ty.rs:205): f16/f32/f64 only.
def isFloat : TyAll -> Bool := fun t =>
  @TyAll.casesOn (fun _ => Bool) t
    false false false false false -- i8 i16 i32 i64 i128
    false false false false false -- u8 u16 u32 u64 u128
    true true true               -- f16 f32 f64
    false                        -- tbool
    (fun _e _n => false)         -- vector
    false                        -- ptr
    (fun _k => false)            -- fatptr
    false                        -- tunit
    false                        -- never
    (fun _id => false)           -- tstruct
    (fun _el _len => false)      -- tarray
    (fun _a _b => false)         -- ttuple
    (fun _id => false)           -- tenum
    (fun _id => false)           -- tfunc
    (fun _a => false)            -- tref
    (fun _a => false)            -- trefmut
    (fun _a => false)            -- tptrconst
    (fun _a => false)            -- tptrmut
    (fun _a => false)            -- trc
    (fun _el _r => false)        -- tset
    (fun _el => false)           -- tseq
    (fun _id => false)           -- trecord
    (fun _id => false)           -- tclosure

-- `Ty::is_numeric` (ty.rs:209) = is_integer || is_float.
def isNumeric : TyAll -> Bool := fun t => Bool.or (isInteger t) (isFloat t)

-- `Ty::is_vector` (ty.rs:214): vector only.
def isVector : TyAll -> Bool := fun t =>
  @TyAll.casesOn (fun _ => Bool) t
    false false false false false -- i8 i16 i32 i64 i128
    false false false false false -- u8 u16 u32 u64 u128
    false false false            -- f16 f32 f64
    false                        -- tbool
    (fun _e _n => true)          -- vector
    false                        -- ptr
    (fun _k => false)            -- fatptr
    false                        -- tunit
    false                        -- never
    (fun _id => false)           -- tstruct
    (fun _el _len => false)      -- tarray
    (fun _a _b => false)         -- ttuple
    (fun _id => false)           -- tenum
    (fun _id => false)           -- tfunc
    (fun _a => false)            -- tref
    (fun _a => false)            -- trefmut
    (fun _a => false)            -- tptrconst
    (fun _a => false)            -- tptrmut
    (fun _a => false)            -- trc
    (fun _el _r => false)        -- tset
    (fun _el => false)           -- tseq
    (fun _id => false)           -- trecord
    (fun _id => false)           -- tclosure

-- `Ty::is_reference` (ty.rs:320): fatptr/tref/trefmut/tptrconst/tptrmut/trc.
-- Bare ptr is NOT a reference.
def isReference : TyAll -> Bool := fun t =>
  @TyAll.casesOn (fun _ => Bool) t
    false false false false false -- i8 i16 i32 i64 i128
    false false false false false -- u8 u16 u32 u64 u128
    false false false            -- f16 f32 f64
    false                        -- tbool
    (fun _e _n => false)         -- vector
    false                        -- ptr  (NOT a reference)
    (fun _k => true)             -- fatptr
    false                        -- tunit
    false                        -- never
    (fun _id => false)           -- tstruct
    (fun _el _len => false)      -- tarray
    (fun _a _b => false)         -- ttuple
    (fun _id => false)           -- tenum
    (fun _id => false)           -- tfunc
    (fun _a => true)             -- tref
    (fun _a => true)             -- trefmut
    (fun _a => true)             -- tptrconst
    (fun _a => true)             -- tptrmut
    (fun _a => true)             -- trc
    (fun _el _r => false)        -- tset
    (fun _el => false)           -- tseq
    (fun _id => false)           -- trecord
    (fun _id => false)           -- tclosure

-- `Ty::is_aggregate` (ty.rs:338): tstruct/tarray/ttuple/tenum/tset/tseq/trecord.
def isAggregate : TyAll -> Bool := fun t =>
  @TyAll.casesOn (fun _ => Bool) t
    false false false false false -- i8 i16 i32 i64 i128
    false false false false false -- u8 u16 u32 u64 u128
    false false false            -- f16 f32 f64
    false                        -- tbool
    (fun _e _n => false)         -- vector
    false                        -- ptr
    (fun _k => false)            -- fatptr
    false                        -- tunit
    false                        -- never
    (fun _id => true)            -- tstruct
    (fun _el _len => true)       -- tarray
    (fun _a _b => true)          -- ttuple
    (fun _id => true)            -- tenum
    (fun _id => false)           -- tfunc
    (fun _a => false)            -- tref
    (fun _a => false)            -- trefmut
    (fun _a => false)            -- tptrconst
    (fun _a => false)            -- tptrmut
    (fun _a => false)            -- trc
    (fun _el _r => true)         -- tset
    (fun _el => true)            -- tseq
    (fun _id => true)            -- trecord
    (fun _id => false)           -- tclosure

-- `Ty::is_closure` (ty.rs:352): tclosure only.
def isClosure : TyAll -> Bool := fun t =>
  @TyAll.casesOn (fun _ => Bool) t
    false false false false false -- i8 i16 i32 i64 i128
    false false false false false -- u8 u16 u32 u64 u128
    false false false            -- f16 f32 f64
    false                        -- tbool
    (fun _e _n => false)         -- vector
    false                        -- ptr
    (fun _k => false)            -- fatptr
    false                        -- tunit
    false                        -- never
    (fun _id => false)           -- tstruct
    (fun _el _len => false)      -- tarray
    (fun _a _b => false)         -- ttuple
    (fun _id => false)           -- tenum
    (fun _id => false)           -- tfunc
    (fun _a => false)            -- tref
    (fun _a => false)            -- trefmut
    (fun _a => false)            -- tptrconst
    (fun _a => false)            -- tptrmut
    (fun _a => false)            -- trc
    (fun _el _r => false)        -- tset
    (fun _el => false)           -- tseq
    (fun _id => false)           -- trecord
    (fun _id => true)            -- tclosure

-- `Ty::bit_width_with` (ty.rs:174): given thin-pointer width pb, the pointer-like
-- thin types -> some pb; fatptr -> some (pb+pb); vector recurses; every other
-- type delegates to bit_width. Vector recurses (=> @TyAll.rec); the per-element
-- IH is the element's own bit_width_with pb.
def bitWidthWith : Nat -> TyAll -> Option Nat := fun pb t =>
  @TyAll.rec (fun _ => Option Nat)
    (Option.some 8)              -- i8
    (Option.some 16)             -- i16
    (Option.some 32)             -- i32
    (Option.some 64)             -- i64
    (Option.some 128)            -- i128
    (Option.some 8)              -- u8
    (Option.some 16)             -- u16
    (Option.some 32)             -- u32
    (Option.some 64)             -- u64
    (Option.some 128)            -- u128
    (Option.some 16)             -- f16
    (Option.some 32)             -- f32
    (Option.some 64)             -- f64
    (Option.some 1)              -- tbool
    (fun _e n ihE =>             -- vector(e,n): elem bitWidthWith * lanes
      @Option.casesOn Nat (fun _ => Option Nat) ihE
        Option.none
        (fun w => Option.some (Nat.mul w n)))
    (Option.some pb)             -- ptr  -> some pb
    (fun _k => Option.some (Nat.add pb pb)) -- fatptr -> some (pb+pb)
    Option.none                  -- tunit
    Option.none                  -- never
    (fun _id => Option.none)     -- tstruct
    (fun _el _len => Option.none) -- tarray
    (fun _a _b _iha _ihb => Option.none) -- ttuple
    (fun _id => Option.none)     -- tenum
    (fun _id => Option.none)     -- tfunc
    (fun _a _iha => Option.some pb) -- tref      -> some pb
    (fun _a _iha => Option.some pb) -- trefmut   -> some pb
    (fun _a _iha => Option.some pb) -- tptrconst -> some pb
    (fun _a _iha => Option.some pb) -- tptrmut   -> some pb
    (fun _a _iha => Option.some pb) -- trc       -> some pb
    (fun _el _r => Option.none)  -- tset
    (fun _el => Option.none)     -- tseq
    (fun _id => Option.none)     -- trecord
    (fun _id => Option.none)     -- tclosure
    t

-- ===========================================================================
-- FAITHFULNESS: bitWidth (ty.rs:142). Representative sample across ctor-shapes.
-- ===========================================================================
theorem tya_bitWidth_i32 : bitWidth TyAll.i32 = Option.some 32 := rfl
theorem tya_bitWidth_i128 : bitWidth TyAll.i128 = Option.some 128 := rfl
theorem tya_bitWidth_u32 : bitWidth TyAll.u32 = Option.some 32 := rfl
theorem tya_bitWidth_f32 : bitWidth TyAll.f32 = Option.some 32 := rfl
theorem tya_bitWidth_tbool : bitWidth TyAll.tbool = Option.some 1 := rfl
theorem tya_bitWidth_v4i32 : bitWidth (TyAll.vector TyAll.i32 4) = Option.some 128 := rfl
theorem tya_bitWidth_v8bool : bitWidth (TyAll.vector TyAll.tbool 8) = Option.some 8 := rfl
theorem tya_bitWidth_ptr : bitWidth TyAll.ptr = Option.none := rfl
theorem tya_bitWidth_fatptr : bitWidth (TyAll.fatptr FatKindA.fpstr) = Option.none := rfl
theorem tya_bitWidth_tunit : bitWidth TyAll.tunit = Option.none := rfl
theorem tya_bitWidth_never : bitWidth TyAll.never = Option.none := rfl
theorem tya_bitWidth_tstruct : bitWidth (TyAll.tstruct 0) = Option.none := rfl
theorem tya_bitWidth_tarray : bitWidth (TyAll.tarray 0 0) = Option.none := rfl
theorem tya_bitWidth_ttuple : bitWidth (TyAll.ttuple TyAll.i32 TyAll.i32) = Option.none := rfl
theorem tya_bitWidth_tenum : bitWidth (TyAll.tenum 0) = Option.none := rfl
theorem tya_bitWidth_tfunc : bitWidth (TyAll.tfunc 0) = Option.none := rfl
theorem tya_bitWidth_tref : bitWidth (TyAll.tref TyAll.i32) = Option.none := rfl
theorem tya_bitWidth_trc : bitWidth (TyAll.trc TyAll.i32) = Option.none := rfl
theorem tya_bitWidth_tset : bitWidth (TyAll.tset 0 SetReprA.boxed) = Option.none := rfl
theorem tya_bitWidth_tseq : bitWidth (TyAll.tseq 0) = Option.none := rfl
theorem tya_bitWidth_trecord : bitWidth (TyAll.trecord 0) = Option.none := rfl
theorem tya_bitWidth_tclosure : bitWidth (TyAll.tclosure 0) = Option.none := rfl

-- ===========================================================================
-- FAITHFULNESS: isSigned (ty.rs:196). Only i8..i128 true.
-- ===========================================================================
theorem tya_isSigned_i32 : isSigned TyAll.i32 = true := rfl
theorem tya_isSigned_u32 : isSigned TyAll.u32 = false := rfl
theorem tya_isSigned_f32 : isSigned TyAll.f32 = false := rfl
theorem tya_isSigned_tbool : isSigned TyAll.tbool = false := rfl
theorem tya_isSigned_vector : isSigned (TyAll.vector TyAll.i32 4) = false := rfl
theorem tya_isSigned_ptr : isSigned TyAll.ptr = false := rfl
theorem tya_isSigned_fatptr : isSigned (TyAll.fatptr FatKindA.fpstr) = false := rfl
theorem tya_isSigned_tunit : isSigned TyAll.tunit = false := rfl
theorem tya_isSigned_never : isSigned TyAll.never = false := rfl
theorem tya_isSigned_tstruct : isSigned (TyAll.tstruct 0) = false := rfl
theorem tya_isSigned_tarray : isSigned (TyAll.tarray 0 0) = false := rfl
theorem tya_isSigned_ttuple : isSigned (TyAll.ttuple TyAll.i32 TyAll.i32) = false := rfl
theorem tya_isSigned_tenum : isSigned (TyAll.tenum 0) = false := rfl
theorem tya_isSigned_tfunc : isSigned (TyAll.tfunc 0) = false := rfl
theorem tya_isSigned_tref : isSigned (TyAll.tref TyAll.i32) = false := rfl
theorem tya_isSigned_trc : isSigned (TyAll.trc TyAll.i32) = false := rfl
theorem tya_isSigned_tset : isSigned (TyAll.tset 0 SetReprA.boxed) = false := rfl
theorem tya_isSigned_tseq : isSigned (TyAll.tseq 0) = false := rfl
theorem tya_isSigned_trecord : isSigned (TyAll.trecord 0) = false := rfl
theorem tya_isSigned_tclosure : isSigned (TyAll.tclosure 0) = false := rfl

-- ===========================================================================
-- FAITHFULNESS: isUnsigned (ty.rs:201). Only u8..u128 true.
-- ===========================================================================
theorem tya_isUnsigned_i32 : isUnsigned TyAll.i32 = false := rfl
theorem tya_isUnsigned_u32 : isUnsigned TyAll.u32 = true := rfl
theorem tya_isUnsigned_f32 : isUnsigned TyAll.f32 = false := rfl
theorem tya_isUnsigned_tbool : isUnsigned TyAll.tbool = false := rfl
theorem tya_isUnsigned_vector : isUnsigned (TyAll.vector TyAll.i32 4) = false := rfl
theorem tya_isUnsigned_ptr : isUnsigned TyAll.ptr = false := rfl
theorem tya_isUnsigned_fatptr : isUnsigned (TyAll.fatptr FatKindA.fpstr) = false := rfl
theorem tya_isUnsigned_tunit : isUnsigned TyAll.tunit = false := rfl
theorem tya_isUnsigned_never : isUnsigned TyAll.never = false := rfl
theorem tya_isUnsigned_tstruct : isUnsigned (TyAll.tstruct 0) = false := rfl
theorem tya_isUnsigned_tarray : isUnsigned (TyAll.tarray 0 0) = false := rfl
theorem tya_isUnsigned_ttuple : isUnsigned (TyAll.ttuple TyAll.i32 TyAll.i32) = false := rfl
theorem tya_isUnsigned_tenum : isUnsigned (TyAll.tenum 0) = false := rfl
theorem tya_isUnsigned_tfunc : isUnsigned (TyAll.tfunc 0) = false := rfl
theorem tya_isUnsigned_tref : isUnsigned (TyAll.tref TyAll.i32) = false := rfl
theorem tya_isUnsigned_trc : isUnsigned (TyAll.trc TyAll.i32) = false := rfl
theorem tya_isUnsigned_tset : isUnsigned (TyAll.tset 0 SetReprA.boxed) = false := rfl
theorem tya_isUnsigned_tseq : isUnsigned (TyAll.tseq 0) = false := rfl
theorem tya_isUnsigned_trecord : isUnsigned (TyAll.trecord 0) = false := rfl
theorem tya_isUnsigned_tclosure : isUnsigned (TyAll.tclosure 0) = false := rfl

-- ===========================================================================
-- FAITHFULNESS: isInteger (ty.rs:191). i8..i128 and u8..u128 true.
-- ===========================================================================
theorem tya_isInteger_i32 : isInteger TyAll.i32 = true := rfl
theorem tya_isInteger_u32 : isInteger TyAll.u32 = true := rfl
theorem tya_isInteger_f32 : isInteger TyAll.f32 = false := rfl
theorem tya_isInteger_tbool : isInteger TyAll.tbool = false := rfl
theorem tya_isInteger_vector : isInteger (TyAll.vector TyAll.i32 4) = false := rfl
theorem tya_isInteger_ptr : isInteger TyAll.ptr = false := rfl
theorem tya_isInteger_fatptr : isInteger (TyAll.fatptr FatKindA.fpstr) = false := rfl
theorem tya_isInteger_tunit : isInteger TyAll.tunit = false := rfl
theorem tya_isInteger_never : isInteger TyAll.never = false := rfl
theorem tya_isInteger_tstruct : isInteger (TyAll.tstruct 0) = false := rfl
theorem tya_isInteger_tarray : isInteger (TyAll.tarray 0 0) = false := rfl
theorem tya_isInteger_ttuple : isInteger (TyAll.ttuple TyAll.i32 TyAll.i32) = false := rfl
theorem tya_isInteger_tenum : isInteger (TyAll.tenum 0) = false := rfl
theorem tya_isInteger_tfunc : isInteger (TyAll.tfunc 0) = false := rfl
theorem tya_isInteger_tref : isInteger (TyAll.tref TyAll.i32) = false := rfl
theorem tya_isInteger_trc : isInteger (TyAll.trc TyAll.i32) = false := rfl
theorem tya_isInteger_tset : isInteger (TyAll.tset 0 SetReprA.boxed) = false := rfl
theorem tya_isInteger_tseq : isInteger (TyAll.tseq 0) = false := rfl
theorem tya_isInteger_trecord : isInteger (TyAll.trecord 0) = false := rfl
theorem tya_isInteger_tclosure : isInteger (TyAll.tclosure 0) = false := rfl

-- ===========================================================================
-- FAITHFULNESS: isFloat (ty.rs:205). Only f16/f32/f64 true.
-- ===========================================================================
theorem tya_isFloat_i32 : isFloat TyAll.i32 = false := rfl
theorem tya_isFloat_u32 : isFloat TyAll.u32 = false := rfl
theorem tya_isFloat_f32 : isFloat TyAll.f32 = true := rfl
theorem tya_isFloat_tbool : isFloat TyAll.tbool = false := rfl
theorem tya_isFloat_vector : isFloat (TyAll.vector TyAll.i32 4) = false := rfl
theorem tya_isFloat_ptr : isFloat TyAll.ptr = false := rfl
theorem tya_isFloat_fatptr : isFloat (TyAll.fatptr FatKindA.fpstr) = false := rfl
theorem tya_isFloat_tunit : isFloat TyAll.tunit = false := rfl
theorem tya_isFloat_never : isFloat TyAll.never = false := rfl
theorem tya_isFloat_tstruct : isFloat (TyAll.tstruct 0) = false := rfl
theorem tya_isFloat_tarray : isFloat (TyAll.tarray 0 0) = false := rfl
theorem tya_isFloat_ttuple : isFloat (TyAll.ttuple TyAll.i32 TyAll.i32) = false := rfl
theorem tya_isFloat_tenum : isFloat (TyAll.tenum 0) = false := rfl
theorem tya_isFloat_tfunc : isFloat (TyAll.tfunc 0) = false := rfl
theorem tya_isFloat_tref : isFloat (TyAll.tref TyAll.i32) = false := rfl
theorem tya_isFloat_trc : isFloat (TyAll.trc TyAll.i32) = false := rfl
theorem tya_isFloat_tset : isFloat (TyAll.tset 0 SetReprA.boxed) = false := rfl
theorem tya_isFloat_tseq : isFloat (TyAll.tseq 0) = false := rfl
theorem tya_isFloat_trecord : isFloat (TyAll.trecord 0) = false := rfl
theorem tya_isFloat_tclosure : isFloat (TyAll.tclosure 0) = false := rfl

-- ===========================================================================
-- FAITHFULNESS: isNumeric (ty.rs:209). Integers and floats true.
-- ===========================================================================
theorem tya_isNumeric_i32 : isNumeric TyAll.i32 = true := rfl
theorem tya_isNumeric_u32 : isNumeric TyAll.u32 = true := rfl
theorem tya_isNumeric_f32 : isNumeric TyAll.f32 = true := rfl
theorem tya_isNumeric_tbool : isNumeric TyAll.tbool = false := rfl
theorem tya_isNumeric_vector : isNumeric (TyAll.vector TyAll.i32 4) = false := rfl
theorem tya_isNumeric_ptr : isNumeric TyAll.ptr = false := rfl
theorem tya_isNumeric_fatptr : isNumeric (TyAll.fatptr FatKindA.fpstr) = false := rfl
theorem tya_isNumeric_tunit : isNumeric TyAll.tunit = false := rfl
theorem tya_isNumeric_never : isNumeric TyAll.never = false := rfl
theorem tya_isNumeric_tstruct : isNumeric (TyAll.tstruct 0) = false := rfl
theorem tya_isNumeric_tarray : isNumeric (TyAll.tarray 0 0) = false := rfl
theorem tya_isNumeric_ttuple : isNumeric (TyAll.ttuple TyAll.i32 TyAll.i32) = false := rfl
theorem tya_isNumeric_tenum : isNumeric (TyAll.tenum 0) = false := rfl
theorem tya_isNumeric_tfunc : isNumeric (TyAll.tfunc 0) = false := rfl
theorem tya_isNumeric_tref : isNumeric (TyAll.tref TyAll.i32) = false := rfl
theorem tya_isNumeric_trc : isNumeric (TyAll.trc TyAll.i32) = false := rfl
theorem tya_isNumeric_tset : isNumeric (TyAll.tset 0 SetReprA.boxed) = false := rfl
theorem tya_isNumeric_tseq : isNumeric (TyAll.tseq 0) = false := rfl
theorem tya_isNumeric_trecord : isNumeric (TyAll.trecord 0) = false := rfl
theorem tya_isNumeric_tclosure : isNumeric (TyAll.tclosure 0) = false := rfl

-- ===========================================================================
-- FAITHFULNESS: isVector (ty.rs:214). Only vector true.
-- ===========================================================================
theorem tya_isVector_i32 : isVector TyAll.i32 = false := rfl
theorem tya_isVector_u32 : isVector TyAll.u32 = false := rfl
theorem tya_isVector_f32 : isVector TyAll.f32 = false := rfl
theorem tya_isVector_tbool : isVector TyAll.tbool = false := rfl
theorem tya_isVector_vector : isVector (TyAll.vector TyAll.i32 4) = true := rfl
theorem tya_isVector_ptr : isVector TyAll.ptr = false := rfl
theorem tya_isVector_fatptr : isVector (TyAll.fatptr FatKindA.fpstr) = false := rfl
theorem tya_isVector_tunit : isVector TyAll.tunit = false := rfl
theorem tya_isVector_never : isVector TyAll.never = false := rfl
theorem tya_isVector_tstruct : isVector (TyAll.tstruct 0) = false := rfl
theorem tya_isVector_tarray : isVector (TyAll.tarray 0 0) = false := rfl
theorem tya_isVector_ttuple : isVector (TyAll.ttuple TyAll.i32 TyAll.i32) = false := rfl
theorem tya_isVector_tenum : isVector (TyAll.tenum 0) = false := rfl
theorem tya_isVector_tfunc : isVector (TyAll.tfunc 0) = false := rfl
theorem tya_isVector_tref : isVector (TyAll.tref TyAll.i32) = false := rfl
theorem tya_isVector_trc : isVector (TyAll.trc TyAll.i32) = false := rfl
theorem tya_isVector_tset : isVector (TyAll.tset 0 SetReprA.boxed) = false := rfl
theorem tya_isVector_tseq : isVector (TyAll.tseq 0) = false := rfl
theorem tya_isVector_trecord : isVector (TyAll.trecord 0) = false := rfl
theorem tya_isVector_tclosure : isVector (TyAll.tclosure 0) = false := rfl

-- ===========================================================================
-- FAITHFULNESS: isReference (ty.rs:320). fatptr/tref/trefmut/tptrconst/
-- tptrmut/trc true; bare ptr FALSE.
-- ===========================================================================
theorem tya_isReference_i32 : isReference TyAll.i32 = false := rfl
theorem tya_isReference_u32 : isReference TyAll.u32 = false := rfl
theorem tya_isReference_f32 : isReference TyAll.f32 = false := rfl
theorem tya_isReference_tbool : isReference TyAll.tbool = false := rfl
theorem tya_isReference_vector : isReference (TyAll.vector TyAll.i32 4) = false := rfl
theorem tya_isReference_ptr : isReference TyAll.ptr = false := rfl
theorem tya_isReference_fatptr : isReference (TyAll.fatptr FatKindA.fpstr) = true := rfl
theorem tya_isReference_tunit : isReference TyAll.tunit = false := rfl
theorem tya_isReference_never : isReference TyAll.never = false := rfl
theorem tya_isReference_tstruct : isReference (TyAll.tstruct 0) = false := rfl
theorem tya_isReference_tarray : isReference (TyAll.tarray 0 0) = false := rfl
theorem tya_isReference_ttuple : isReference (TyAll.ttuple TyAll.i32 TyAll.i32) = false := rfl
theorem tya_isReference_tenum : isReference (TyAll.tenum 0) = false := rfl
theorem tya_isReference_tfunc : isReference (TyAll.tfunc 0) = false := rfl
theorem tya_isReference_tref : isReference (TyAll.tref TyAll.i32) = true := rfl
theorem tya_isReference_trefmut : isReference (TyAll.trefmut TyAll.i32) = true := rfl
theorem tya_isReference_tptrconst : isReference (TyAll.tptrconst TyAll.i32) = true := rfl
theorem tya_isReference_tptrmut : isReference (TyAll.tptrmut TyAll.i32) = true := rfl
theorem tya_isReference_trc : isReference (TyAll.trc TyAll.i32) = true := rfl
theorem tya_isReference_tset : isReference (TyAll.tset 0 SetReprA.boxed) = false := rfl
theorem tya_isReference_tseq : isReference (TyAll.tseq 0) = false := rfl
theorem tya_isReference_trecord : isReference (TyAll.trecord 0) = false := rfl
theorem tya_isReference_tclosure : isReference (TyAll.tclosure 0) = false := rfl

-- ===========================================================================
-- FAITHFULNESS: isAggregate (ty.rs:338). tstruct/tarray/ttuple/tenum/tset/
-- tseq/trecord true; tfunc/tclosure/vector/scalars/refs false.
-- ===========================================================================
theorem tya_isAggregate_i32 : isAggregate TyAll.i32 = false := rfl
theorem tya_isAggregate_u32 : isAggregate TyAll.u32 = false := rfl
theorem tya_isAggregate_f32 : isAggregate TyAll.f32 = false := rfl
theorem tya_isAggregate_tbool : isAggregate TyAll.tbool = false := rfl
theorem tya_isAggregate_vector : isAggregate (TyAll.vector TyAll.i32 4) = false := rfl
theorem tya_isAggregate_ptr : isAggregate TyAll.ptr = false := rfl
theorem tya_isAggregate_fatptr : isAggregate (TyAll.fatptr FatKindA.fpstr) = false := rfl
theorem tya_isAggregate_tunit : isAggregate TyAll.tunit = false := rfl
theorem tya_isAggregate_never : isAggregate TyAll.never = false := rfl
theorem tya_isAggregate_tstruct : isAggregate (TyAll.tstruct 0) = true := rfl
theorem tya_isAggregate_tarray : isAggregate (TyAll.tarray 0 0) = true := rfl
theorem tya_isAggregate_ttuple : isAggregate (TyAll.ttuple TyAll.i32 TyAll.i32) = true := rfl
theorem tya_isAggregate_tenum : isAggregate (TyAll.tenum 0) = true := rfl
theorem tya_isAggregate_tfunc : isAggregate (TyAll.tfunc 0) = false := rfl
theorem tya_isAggregate_tref : isAggregate (TyAll.tref TyAll.i32) = false := rfl
theorem tya_isAggregate_trc : isAggregate (TyAll.trc TyAll.i32) = false := rfl
theorem tya_isAggregate_tset : isAggregate (TyAll.tset 0 SetReprA.boxed) = true := rfl
theorem tya_isAggregate_tseq : isAggregate (TyAll.tseq 0) = true := rfl
theorem tya_isAggregate_trecord : isAggregate (TyAll.trecord 0) = true := rfl
theorem tya_isAggregate_tclosure : isAggregate (TyAll.tclosure 0) = false := rfl

-- ===========================================================================
-- FAITHFULNESS: isClosure (ty.rs:352). Only tclosure true.
-- ===========================================================================
theorem tya_isClosure_i32 : isClosure TyAll.i32 = false := rfl
theorem tya_isClosure_u32 : isClosure TyAll.u32 = false := rfl
theorem tya_isClosure_f32 : isClosure TyAll.f32 = false := rfl
theorem tya_isClosure_tbool : isClosure TyAll.tbool = false := rfl
theorem tya_isClosure_vector : isClosure (TyAll.vector TyAll.i32 4) = false := rfl
theorem tya_isClosure_ptr : isClosure TyAll.ptr = false := rfl
theorem tya_isClosure_fatptr : isClosure (TyAll.fatptr FatKindA.fpstr) = false := rfl
theorem tya_isClosure_tunit : isClosure TyAll.tunit = false := rfl
theorem tya_isClosure_never : isClosure TyAll.never = false := rfl
theorem tya_isClosure_tstruct : isClosure (TyAll.tstruct 0) = false := rfl
theorem tya_isClosure_tarray : isClosure (TyAll.tarray 0 0) = false := rfl
theorem tya_isClosure_ttuple : isClosure (TyAll.ttuple TyAll.i32 TyAll.i32) = false := rfl
theorem tya_isClosure_tenum : isClosure (TyAll.tenum 0) = false := rfl
theorem tya_isClosure_tfunc : isClosure (TyAll.tfunc 0) = false := rfl
theorem tya_isClosure_tref : isClosure (TyAll.tref TyAll.i32) = false := rfl
theorem tya_isClosure_trc : isClosure (TyAll.trc TyAll.i32) = false := rfl
theorem tya_isClosure_tset : isClosure (TyAll.tset 0 SetReprA.boxed) = false := rfl
theorem tya_isClosure_tseq : isClosure (TyAll.tseq 0) = false := rfl
theorem tya_isClosure_trecord : isClosure (TyAll.trecord 0) = false := rfl
theorem tya_isClosure_tclosure : isClosure (TyAll.tclosure 0) = true := rfl

-- ===========================================================================
-- FAITHFULNESS: bitWidthWith (ty.rs:174). Thin pointer-like -> some pb;
-- fatptr -> some (pb+pb); everything else delegates to bitWidth.
-- Proven symbolically (any pb) and concretely at pb=64.
-- ===========================================================================
theorem tya_bitWidthWith_ptr (pb : Nat) : bitWidthWith pb TyAll.ptr = Option.some pb := rfl
theorem tya_bitWidthWith_tref (pb : Nat) : bitWidthWith pb (TyAll.tref TyAll.i32) = Option.some pb := rfl
theorem tya_bitWidthWith_trefmut (pb : Nat) : bitWidthWith pb (TyAll.trefmut TyAll.i32) = Option.some pb := rfl
theorem tya_bitWidthWith_tptrconst (pb : Nat) : bitWidthWith pb (TyAll.tptrconst TyAll.i32) = Option.some pb := rfl
theorem tya_bitWidthWith_tptrmut (pb : Nat) : bitWidthWith pb (TyAll.tptrmut TyAll.i32) = Option.some pb := rfl
theorem tya_bitWidthWith_trc (pb : Nat) : bitWidthWith pb (TyAll.trc TyAll.i32) = Option.some pb := rfl
theorem tya_bitWidthWith_fatptr (pb : Nat) :
    bitWidthWith pb (TyAll.fatptr FatKindA.fpstr) = Option.some (Nat.add pb pb) := rfl
theorem tya_bitWidthWith_i32 (pb : Nat) : bitWidthWith pb TyAll.i32 = Option.some 32 := rfl
-- Concrete thin = 64, fat = 128.
theorem tya_bitWidthWith64_ptr : bitWidthWith 64 TyAll.ptr = Option.some 64 := rfl
theorem tya_bitWidthWith64_tref : bitWidthWith 64 (TyAll.tref TyAll.i32) = Option.some 64 := rfl
theorem tya_bitWidthWith64_fatptr : bitWidthWith 64 (TyAll.fatptr FatKindA.fpstr) = Option.some 128 := rfl
theorem tya_bitWidthWith64_i32 : bitWidthWith 64 TyAll.i32 = Option.some 32 := rfl

-- =========================================================================
-- METATHEOREMS: partition/disjointness
-- =========================================================================
-- ===========================================================================
-- METATHEOREMS: universally-quantified PARTITION / DISJOINTNESS / IMPLICATION
-- laws over ALL 33 ctors. Each proof is a single 33-minor @TyAll.casesOn whose
-- every minor reduces by iota to rfl. (Bool.not x || y encodes implication x=>y;
-- Bool.and x y = false encodes disjointness of x,y.)
-- ===========================================================================

-- signed/unsigned DISJOINT: no type is both signed and unsigned.
theorem mpart_signed_unsigned_disjoint (t : TyAll) :
    Bool.and (isSigned t) (isUnsigned t) = false :=
  @TyAll.casesOn (fun k => Bool.and (isSigned k) (isUnsigned k) = false) t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _e _n => rfl) rfl (fun _k => rfl) rfl rfl
    (fun _id => rfl) (fun _el _len => rfl) (fun _a _b => rfl)
    (fun _id => rfl) (fun _id => rfl) (fun _a => rfl) (fun _a => rfl)
    (fun _a => rfl) (fun _a => rfl) (fun _a => rfl) (fun _el _r => rfl)
    (fun _el => rfl) (fun _id => rfl) (fun _id => rfl)

-- signed => integer.
theorem mpart_signed_implies_integer (t : TyAll) :
    Bool.or (Bool.not (isSigned t)) (isInteger t) = true :=
  @TyAll.casesOn (fun k => Bool.or (Bool.not (isSigned k)) (isInteger k) = true) t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _e _n => rfl) rfl (fun _k => rfl) rfl rfl
    (fun _id => rfl) (fun _el _len => rfl) (fun _a _b => rfl)
    (fun _id => rfl) (fun _id => rfl) (fun _a => rfl) (fun _a => rfl)
    (fun _a => rfl) (fun _a => rfl) (fun _a => rfl) (fun _el _r => rfl)
    (fun _el => rfl) (fun _id => rfl) (fun _id => rfl)

-- unsigned => integer.
theorem mpart_unsigned_implies_integer (t : TyAll) :
    Bool.or (Bool.not (isUnsigned t)) (isInteger t) = true :=
  @TyAll.casesOn (fun k => Bool.or (Bool.not (isUnsigned k)) (isInteger k) = true) t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _e _n => rfl) rfl (fun _k => rfl) rfl rfl
    (fun _id => rfl) (fun _el _len => rfl) (fun _a _b => rfl)
    (fun _id => rfl) (fun _id => rfl) (fun _a => rfl) (fun _a => rfl)
    (fun _a => rfl) (fun _a => rfl) (fun _a => rfl) (fun _el _r => rfl)
    (fun _el => rfl) (fun _id => rfl) (fun _id => rfl)

-- integer/float DISJOINT.
theorem mpart_integer_float_disjoint (t : TyAll) :
    Bool.and (isInteger t) (isFloat t) = false :=
  @TyAll.casesOn (fun k => Bool.and (isInteger k) (isFloat k) = false) t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _e _n => rfl) rfl (fun _k => rfl) rfl rfl
    (fun _id => rfl) (fun _el _len => rfl) (fun _a _b => rfl)
    (fun _id => rfl) (fun _id => rfl) (fun _a => rfl) (fun _a => rfl)
    (fun _a => rfl) (fun _a => rfl) (fun _a => rfl) (fun _el _r => rfl)
    (fun _el => rfl) (fun _id => rfl) (fun _id => rfl)

-- integer => numeric.
theorem mpart_integer_implies_numeric (t : TyAll) :
    Bool.or (Bool.not (isInteger t)) (isNumeric t) = true :=
  @TyAll.casesOn (fun k => Bool.or (Bool.not (isInteger k)) (isNumeric k) = true) t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _e _n => rfl) rfl (fun _k => rfl) rfl rfl
    (fun _id => rfl) (fun _el _len => rfl) (fun _a _b => rfl)
    (fun _id => rfl) (fun _id => rfl) (fun _a => rfl) (fun _a => rfl)
    (fun _a => rfl) (fun _a => rfl) (fun _a => rfl) (fun _el _r => rfl)
    (fun _el => rfl) (fun _id => rfl) (fun _id => rfl)

-- float => numeric.
theorem mpart_float_implies_numeric (t : TyAll) :
    Bool.or (Bool.not (isFloat t)) (isNumeric t) = true :=
  @TyAll.casesOn (fun k => Bool.or (Bool.not (isFloat k)) (isNumeric k) = true) t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _e _n => rfl) rfl (fun _k => rfl) rfl rfl
    (fun _id => rfl) (fun _el _len => rfl) (fun _a _b => rfl)
    (fun _id => rfl) (fun _id => rfl) (fun _a => rfl) (fun _a => rfl)
    (fun _a => rfl) (fun _a => rfl) (fun _a => rfl) (fun _el _r => rfl)
    (fun _el => rfl) (fun _id => rfl) (fun _id => rfl)

-- vector NOT numeric.
theorem mpart_vector_not_numeric (t : TyAll) :
    Bool.and (isVector t) (isNumeric t) = false :=
  @TyAll.casesOn (fun k => Bool.and (isVector k) (isNumeric k) = false) t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _e _n => rfl) rfl (fun _k => rfl) rfl rfl
    (fun _id => rfl) (fun _el _len => rfl) (fun _a _b => rfl)
    (fun _id => rfl) (fun _id => rfl) (fun _a => rfl) (fun _a => rfl)
    (fun _a => rfl) (fun _a => rfl) (fun _a => rfl) (fun _el _r => rfl)
    (fun _el => rfl) (fun _id => rfl) (fun _id => rfl)

-- vector NOT integer.
theorem mpart_vector_not_integer (t : TyAll) :
    Bool.and (isVector t) (isInteger t) = false :=
  @TyAll.casesOn (fun k => Bool.and (isVector k) (isInteger k) = false) t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _e _n => rfl) rfl (fun _k => rfl) rfl rfl
    (fun _id => rfl) (fun _el _len => rfl) (fun _a _b => rfl)
    (fun _id => rfl) (fun _id => rfl) (fun _a => rfl) (fun _a => rfl)
    (fun _a => rfl) (fun _a => rfl) (fun _a => rfl) (fun _el _r => rfl)
    (fun _el => rfl) (fun _id => rfl) (fun _id => rfl)

-- vector NOT float.
theorem mpart_vector_not_float (t : TyAll) :
    Bool.and (isVector t) (isFloat t) = false :=
  @TyAll.casesOn (fun k => Bool.and (isVector k) (isFloat k) = false) t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _e _n => rfl) rfl (fun _k => rfl) rfl rfl
    (fun _id => rfl) (fun _el _len => rfl) (fun _a _b => rfl)
    (fun _id => rfl) (fun _id => rfl) (fun _a => rfl) (fun _a => rfl)
    (fun _a => rfl) (fun _a => rfl) (fun _a => rfl) (fun _el _r => rfl)
    (fun _el => rfl) (fun _id => rfl) (fun _id => rfl)

-- aggregate/closure DISJOINT.
theorem mpart_aggregate_closure_disjoint (t : TyAll) :
    Bool.and (isAggregate t) (isClosure t) = false :=
  @TyAll.casesOn (fun k => Bool.and (isAggregate k) (isClosure k) = false) t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _e _n => rfl) rfl (fun _k => rfl) rfl rfl
    (fun _id => rfl) (fun _el _len => rfl) (fun _a _b => rfl)
    (fun _id => rfl) (fun _id => rfl) (fun _a => rfl) (fun _a => rfl)
    (fun _a => rfl) (fun _a => rfl) (fun _a => rfl) (fun _el _r => rfl)
    (fun _el => rfl) (fun _id => rfl) (fun _id => rfl)

-- reference/numeric DISJOINT.
theorem mpart_reference_numeric_disjoint (t : TyAll) :
    Bool.and (isReference t) (isNumeric t) = false :=
  @TyAll.casesOn (fun k => Bool.and (isReference k) (isNumeric k) = false) t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _e _n => rfl) rfl (fun _k => rfl) rfl rfl
    (fun _id => rfl) (fun _el _len => rfl) (fun _a _b => rfl)
    (fun _id => rfl) (fun _id => rfl) (fun _a => rfl) (fun _a => rfl)
    (fun _a => rfl) (fun _a => rfl) (fun _a => rfl) (fun _el _r => rfl)
    (fun _el => rfl) (fun _id => rfl) (fun _id => rfl)

-- reference/aggregate DISJOINT.
theorem mpart_reference_aggregate_disjoint (t : TyAll) :
    Bool.and (isReference t) (isAggregate t) = false :=
  @TyAll.casesOn (fun k => Bool.and (isReference k) (isAggregate k) = false) t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _e _n => rfl) rfl (fun _k => rfl) rfl rfl
    (fun _id => rfl) (fun _el _len => rfl) (fun _a _b => rfl)
    (fun _id => rfl) (fun _id => rfl) (fun _a => rfl) (fun _a => rfl)
    (fun _a => rfl) (fun _a => rfl) (fun _a => rfl) (fun _el _r => rfl)
    (fun _el => rfl) (fun _id => rfl) (fun _id => rfl)

-- reference/vector DISJOINT.
theorem mpart_reference_vector_disjoint (t : TyAll) :
    Bool.and (isReference t) (isVector t) = false :=
  @TyAll.casesOn (fun k => Bool.and (isReference k) (isVector k) = false) t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _e _n => rfl) rfl (fun _k => rfl) rfl rfl
    (fun _id => rfl) (fun _el _len => rfl) (fun _a _b => rfl)
    (fun _id => rfl) (fun _id => rfl) (fun _a => rfl) (fun _a => rfl)
    (fun _a => rfl) (fun _a => rfl) (fun _a => rfl) (fun _el _r => rfl)
    (fun _el => rfl) (fun _id => rfl) (fun _id => rfl)

-- reference/closure DISJOINT.
theorem mpart_reference_closure_disjoint (t : TyAll) :
    Bool.and (isReference t) (isClosure t) = false :=
  @TyAll.casesOn (fun k => Bool.and (isReference k) (isClosure k) = false) t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _e _n => rfl) rfl (fun _k => rfl) rfl rfl
    (fun _id => rfl) (fun _el _len => rfl) (fun _a _b => rfl)
    (fun _id => rfl) (fun _id => rfl) (fun _a => rfl) (fun _a => rfl)
    (fun _a => rfl) (fun _a => rfl) (fun _a => rfl) (fun _el _r => rfl)
    (fun _el => rfl) (fun _id => rfl) (fun _id => rfl)

-- aggregate/numeric DISJOINT.
theorem mpart_aggregate_numeric_disjoint (t : TyAll) :
    Bool.and (isAggregate t) (isNumeric t) = false :=
  @TyAll.casesOn (fun k => Bool.and (isAggregate k) (isNumeric k) = false) t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _e _n => rfl) rfl (fun _k => rfl) rfl rfl
    (fun _id => rfl) (fun _el _len => rfl) (fun _a _b => rfl)
    (fun _id => rfl) (fun _id => rfl) (fun _a => rfl) (fun _a => rfl)
    (fun _a => rfl) (fun _a => rfl) (fun _a => rfl) (fun _el _r => rfl)
    (fun _el => rfl) (fun _id => rfl) (fun _id => rfl)

-- closure NOT numeric.
theorem mpart_closure_not_numeric (t : TyAll) :
    Bool.and (isClosure t) (isNumeric t) = false :=
  @TyAll.casesOn (fun k => Bool.and (isClosure k) (isNumeric k) = false) t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _e _n => rfl) rfl (fun _k => rfl) rfl rfl
    (fun _id => rfl) (fun _el _len => rfl) (fun _a _b => rfl)
    (fun _id => rfl) (fun _id => rfl) (fun _a => rfl) (fun _a => rfl)
    (fun _a => rfl) (fun _a => rfl) (fun _a => rfl) (fun _el _r => rfl)
    (fun _el => rfl) (fun _id => rfl) (fun _id => rfl)

-- numeric => NOT vector (contrapositive direction stated independently).
theorem mpart_numeric_not_vector (t : TyAll) :
    Bool.or (Bool.not (isNumeric t)) (Bool.not (isVector t)) = true :=
  @TyAll.casesOn (fun k => Bool.or (Bool.not (isNumeric k)) (Bool.not (isVector k)) = true) t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _e _n => rfl) rfl (fun _k => rfl) rfl rfl
    (fun _id => rfl) (fun _el _len => rfl) (fun _a _b => rfl)
    (fun _id => rfl) (fun _id => rfl) (fun _a => rfl) (fun _a => rfl)
    (fun _a => rfl) (fun _a => rfl) (fun _a => rfl) (fun _el _r => rfl)
    (fun _el => rfl) (fun _id => rfl) (fun _id => rfl)

-- =========================================================================
-- METATHEOREMS: width-coherence
-- =========================================================================
-- ===========================================================================
-- WIDTH-COHERENCE METATHEOREMS (NEW). `optIsNone` observes width-lessness;
-- the three "X => no fixed width" facts are universal over all 33 ctors, by
-- @TyAll.casesOn (the coherence property depends on the OUTER constructor only,
-- so each minor closes by rfl). The agreement and fat=2*thin facts follow.
-- ===========================================================================

-- optIsNone : none -> true, some _ -> false (via @Option.casesOn).
def optIsNone : Option Nat -> Bool := fun o =>
  @Option.casesOn Nat (fun _ => Bool) o
    true
    (fun _w => false)

-- A reference type never has a fixed (target-free) bit_width.
-- forall t, (Bool.not (isReference t)) OR (optIsNone (bitWidth t)).
theorem mwid_reference_no_fixed_width (t : TyAll) :
    Bool.or (Bool.not (isReference t)) (optIsNone (bitWidth t)) = true :=
  @TyAll.casesOn (fun k => Bool.or (Bool.not (isReference k)) (optIsNone (bitWidth k)) = true) t
    rfl rfl rfl rfl rfl           -- i8 i16 i32 i64 i128
    rfl rfl rfl rfl rfl           -- u8 u16 u32 u64 u128
    rfl rfl rfl                   -- f16 f32 f64
    rfl                           -- tbool
    (fun _e _n => rfl)            -- vector
    rfl                           -- ptr
    (fun _k => rfl)               -- fatptr
    rfl                           -- tunit
    rfl                           -- never
    (fun _id => rfl)              -- tstruct
    (fun _el _len => rfl)         -- tarray
    (fun _a _b => rfl)            -- ttuple
    (fun _id => rfl)              -- tenum
    (fun _id => rfl)              -- tfunc
    (fun _a => rfl)               -- tref
    (fun _a => rfl)               -- trefmut
    (fun _a => rfl)               -- tptrconst
    (fun _a => rfl)               -- tptrmut
    (fun _a => rfl)               -- trc
    (fun _el _r => rfl)           -- tset
    (fun _el => rfl)              -- tseq
    (fun _id => rfl)              -- trecord
    (fun _id => rfl)              -- tclosure

-- An aggregate type never has a fixed (target-free) bit_width.
theorem mwid_aggregate_no_fixed_width (t : TyAll) :
    Bool.or (Bool.not (isAggregate t)) (optIsNone (bitWidth t)) = true :=
  @TyAll.casesOn (fun k => Bool.or (Bool.not (isAggregate k)) (optIsNone (bitWidth k)) = true) t
    rfl rfl rfl rfl rfl           -- i8 i16 i32 i64 i128
    rfl rfl rfl rfl rfl           -- u8 u16 u32 u64 u128
    rfl rfl rfl                   -- f16 f32 f64
    rfl                           -- tbool
    (fun _e _n => rfl)            -- vector
    rfl                           -- ptr
    (fun _k => rfl)               -- fatptr
    rfl                           -- tunit
    rfl                           -- never
    (fun _id => rfl)              -- tstruct
    (fun _el _len => rfl)         -- tarray
    (fun _a _b => rfl)            -- ttuple
    (fun _id => rfl)              -- tenum
    (fun _id => rfl)              -- tfunc
    (fun _a => rfl)               -- tref
    (fun _a => rfl)               -- trefmut
    (fun _a => rfl)               -- tptrconst
    (fun _a => rfl)               -- tptrmut
    (fun _a => rfl)               -- trc
    (fun _el _r => rfl)           -- tset
    (fun _el => rfl)              -- tseq
    (fun _id => rfl)              -- trecord
    (fun _id => rfl)              -- tclosure

-- A closure type never has a fixed (target-free) bit_width.
theorem mwid_closure_no_fixed_width (t : TyAll) :
    Bool.or (Bool.not (isClosure t)) (optIsNone (bitWidth t)) = true :=
  @TyAll.casesOn (fun k => Bool.or (Bool.not (isClosure k)) (optIsNone (bitWidth k)) = true) t
    rfl rfl rfl rfl rfl           -- i8 i16 i32 i64 i128
    rfl rfl rfl rfl rfl           -- u8 u16 u32 u64 u128
    rfl rfl rfl                   -- f16 f32 f64
    rfl                           -- tbool
    (fun _e _n => rfl)            -- vector
    rfl                           -- ptr
    (fun _k => rfl)               -- fatptr
    rfl                           -- tunit
    rfl                           -- never
    (fun _id => rfl)              -- tstruct
    (fun _el _len => rfl)         -- tarray
    (fun _a _b => rfl)            -- ttuple
    (fun _id => rfl)              -- tenum
    (fun _id => rfl)              -- tfunc
    (fun _a => rfl)               -- tref
    (fun _a => rfl)               -- trefmut
    (fun _a => rfl)               -- tptrconst
    (fun _a => rfl)               -- tptrmut
    (fun _a => rfl)               -- trc
    (fun _el _r => rfl)           -- tset
    (fun _el => rfl)              -- tseq
    (fun _id => rfl)              -- trecord
    (fun _id => rfl)              -- tclosure

-- AGREEMENT: bit_width_with pb c = bit_width c on every NON-pointer, NON-vector
-- ctor. The non-pointer scalars/aggregates do not consult pb, so both defs reduce
-- to the SAME constant (rfl, symbolic in pb).
theorem mwid_agree_i8 (pb : Nat) : bitWidthWith pb TyAll.i8 = bitWidth TyAll.i8 := rfl
theorem mwid_agree_i16 (pb : Nat) : bitWidthWith pb TyAll.i16 = bitWidth TyAll.i16 := rfl
theorem mwid_agree_i32 (pb : Nat) : bitWidthWith pb TyAll.i32 = bitWidth TyAll.i32 := rfl
theorem mwid_agree_i64 (pb : Nat) : bitWidthWith pb TyAll.i64 = bitWidth TyAll.i64 := rfl
theorem mwid_agree_i128 (pb : Nat) : bitWidthWith pb TyAll.i128 = bitWidth TyAll.i128 := rfl
theorem mwid_agree_u8 (pb : Nat) : bitWidthWith pb TyAll.u8 = bitWidth TyAll.u8 := rfl
theorem mwid_agree_f16 (pb : Nat) : bitWidthWith pb TyAll.f16 = bitWidth TyAll.f16 := rfl
theorem mwid_agree_f32 (pb : Nat) : bitWidthWith pb TyAll.f32 = bitWidth TyAll.f32 := rfl
theorem mwid_agree_f64 (pb : Nat) : bitWidthWith pb TyAll.f64 = bitWidth TyAll.f64 := rfl
theorem mwid_agree_tbool (pb : Nat) : bitWidthWith pb TyAll.tbool = bitWidth TyAll.tbool := rfl
theorem mwid_agree_tunit (pb : Nat) : bitWidthWith pb TyAll.tunit = bitWidth TyAll.tunit := rfl
theorem mwid_agree_never (pb : Nat) : bitWidthWith pb TyAll.never = bitWidth TyAll.never := rfl
theorem mwid_agree_tstruct (pb : Nat) : bitWidthWith pb (TyAll.tstruct 0) = bitWidth (TyAll.tstruct 0) := rfl
theorem mwid_agree_ttuple (pb : Nat) :
    bitWidthWith pb (TyAll.ttuple TyAll.i32 TyAll.i32) = bitWidth (TyAll.ttuple TyAll.i32 TyAll.i32) := rfl
theorem mwid_agree_tset (pb : Nat) :
    bitWidthWith pb (TyAll.tset 0 SetReprA.boxed) = bitWidth (TyAll.tset 0 SetReprA.boxed) := rfl
theorem mwid_agree_tclosure (pb : Nat) :
    bitWidthWith pb (TyAll.tclosure 0) = bitWidth (TyAll.tclosure 0) := rfl

-- FAT POINTER is two thin pointers; THIN pointer (bare ptr) is one. (forall pb.)
theorem mwid_fatptr_is_two_thin (pb : Nat) :
    bitWidthWith pb (TyAll.fatptr FatKindA.fpstr) = Option.some (Nat.add pb pb) := rfl
theorem mwid_ptr_is_one_thin (pb : Nat) :
    bitWidthWith pb TyAll.ptr = Option.some pb := rfl
-- And the bitWidthWith of a thin pointer is the single thin width pb, matching the
-- fat pointer being pb+pb (two of those). Stated as the fat/thin relationship at a
-- representative concrete pb = 64 (so 128 = 64 + 64).
theorem mwid_fat_double_thin_64 :
    bitWidthWith 64 (TyAll.fatptr FatKindA.fpstr)
      = Option.some (Nat.add 64 64) := rfl

-- optIsNone sanity (it really observes width-lessness): a pointer is width-less
-- under bit_width, a scalar is not.
theorem mwid_optIsNone_ptr : optIsNone (bitWidth TyAll.ptr) = true := rfl
theorem mwid_optIsNone_i32 : optIsNone (bitWidth TyAll.i32) = false := rfl

-- =========================================================================
-- METATHEOREMS: exhaustiveness/structure
-- =========================================================================
-- ---------------------------------------------------------------------------
-- METATHEOREMS (prefix mexh_): EXHAUSTIVENESS + STRUCTURE over the classifier
-- family.
-- ---------------------------------------------------------------------------

-- (1) comparison_result_ty / select_condition_ty AGREE (ty.rs:289 vs 300).
def compResult : TyAll -> TyAll := fun t =>
  @TyAll.casesOn (fun _ => TyAll) t
    TyAll.tbool TyAll.tbool TyAll.tbool TyAll.tbool TyAll.tbool -- i8..i128
    TyAll.tbool TyAll.tbool TyAll.tbool TyAll.tbool TyAll.tbool -- u8..u128
    TyAll.tbool TyAll.tbool TyAll.tbool                        -- f16 f32 f64
    TyAll.tbool                                                -- tbool
    (fun _e n => TyAll.vector TyAll.tbool n)                   -- vector
    TyAll.tbool                                                -- ptr
    (fun _k => TyAll.tbool)                                    -- fatptr
    TyAll.tbool                                                -- tunit
    TyAll.tbool                                                -- never
    (fun _id => TyAll.tbool)                                   -- tstruct
    (fun _el _len => TyAll.tbool)                              -- tarray
    (fun _a _b => TyAll.tbool)                                 -- ttuple
    (fun _id => TyAll.tbool)                                   -- tenum
    (fun _id => TyAll.tbool)                                   -- tfunc
    (fun _a => TyAll.tbool)                                    -- tref
    (fun _a => TyAll.tbool)                                    -- trefmut
    (fun _a => TyAll.tbool)                                    -- tptrconst
    (fun _a => TyAll.tbool)                                    -- tptrmut
    (fun _a => TyAll.tbool)                                    -- trc
    (fun _el _r => TyAll.tbool)                                -- tset
    (fun _el => TyAll.tbool)                                   -- tseq
    (fun _id => TyAll.tbool)                                   -- trecord
    (fun _id => TyAll.tbool)                                   -- tclosure

def selectCond : TyAll -> TyAll := fun t =>
  @TyAll.casesOn (fun _ => TyAll) t
    TyAll.tbool TyAll.tbool TyAll.tbool TyAll.tbool TyAll.tbool -- i8..i128
    TyAll.tbool TyAll.tbool TyAll.tbool TyAll.tbool TyAll.tbool -- u8..u128
    TyAll.tbool TyAll.tbool TyAll.tbool                        -- f16 f32 f64
    TyAll.tbool                                                -- tbool
    (fun _e n => TyAll.vector TyAll.tbool n)                   -- vector
    TyAll.tbool                                                -- ptr
    (fun _k => TyAll.tbool)                                    -- fatptr
    TyAll.tbool                                                -- tunit
    TyAll.tbool                                                -- never
    (fun _id => TyAll.tbool)                                   -- tstruct
    (fun _el _len => TyAll.tbool)                              -- tarray
    (fun _a _b => TyAll.tbool)                                 -- ttuple
    (fun _id => TyAll.tbool)                                   -- tenum
    (fun _id => TyAll.tbool)                                   -- tfunc
    (fun _a => TyAll.tbool)                                    -- tref
    (fun _a => TyAll.tbool)                                    -- trefmut
    (fun _a => TyAll.tbool)                                    -- tptrconst
    (fun _a => TyAll.tbool)                                    -- tptrmut
    (fun _a => TyAll.tbool)                                    -- trc
    (fun _el _r => TyAll.tbool)                                -- tset
    (fun _el => TyAll.tbool)                                   -- tseq
    (fun _id => TyAll.tbool)                                   -- trecord
    (fun _id => TyAll.tbool)                                   -- tclosure

theorem mexh_comp_eq_select (t : TyAll) : compResult t = selectCond t :=
  @TyAll.casesOn (fun k => compResult k = selectCond k) t
    rfl rfl rfl rfl rfl          -- i8..i128
    rfl rfl rfl rfl rfl          -- u8..u128
    rfl rfl rfl                  -- f16 f32 f64
    rfl                          -- tbool
    (fun _e _n => rfl)           -- vector
    rfl                          -- ptr
    (fun _k => rfl)              -- fatptr
    rfl                          -- tunit
    rfl                          -- never
    (fun _id => rfl)             -- tstruct
    (fun _el _len => rfl)        -- tarray
    (fun _a _b => rfl)           -- ttuple
    (fun _id => rfl)             -- tenum
    (fun _id => rfl)             -- tfunc
    (fun _a => rfl)              -- tref
    (fun _a => rfl)              -- trefmut
    (fun _a => rfl)              -- tptrconst
    (fun _a => rfl)              -- tptrmut
    (fun _a => rfl)              -- trc
    (fun _el _r => rfl)          -- tset
    (fun _el => rfl)             -- tseq
    (fun _id => rfl)             -- trecord
    (fun _id => rfl)             -- tclosure

theorem mexh_compResult_v4i32 :
    compResult (TyAll.vector TyAll.i32 4) = TyAll.vector TyAll.tbool 4 := rfl
theorem mexh_selectCond_v4i32 :
    selectCond (TyAll.vector TyAll.i32 4) = TyAll.vector TyAll.tbool 4 := rfl
theorem mexh_compResult_i32 : compResult TyAll.i32 = TyAll.tbool := rfl
theorem mexh_selectCond_ptr : selectCond TyAll.ptr = TyAll.tbool := rfl
theorem mexh_comp_eq_select_vector (e : TyAll) (n : Nat) :
    compResult (TyAll.vector e n) = selectCond (TyAll.vector e n) := rfl
theorem mexh_comp_eq_select_i32 : compResult TyAll.i32 = selectCond TyAll.i32 := rfl

-- (2) vector_shape coherence (ty.rs:219). Some(elem,lanes) iff vector.
def vectorShape : TyAll -> Option (Prod TyAll Nat) := fun t =>
  @TyAll.casesOn (fun _ => Option (Prod TyAll Nat)) t
    Option.none Option.none Option.none Option.none Option.none -- i8..i128
    Option.none Option.none Option.none Option.none Option.none -- u8..u128
    Option.none Option.none Option.none                        -- f16 f32 f64
    Option.none                                                -- tbool
    (fun e n => Option.some (Prod.mk e n))                     -- vector
    Option.none                                                -- ptr
    (fun _k => Option.none)                                    -- fatptr
    Option.none                                                -- tunit
    Option.none                                                -- never
    (fun _id => Option.none)                                   -- tstruct
    (fun _el _len => Option.none)                              -- tarray
    (fun _a _b => Option.none)                                 -- ttuple
    (fun _id => Option.none)                                   -- tenum
    (fun _id => Option.none)                                   -- tfunc
    (fun _a => Option.none)                                    -- tref
    (fun _a => Option.none)                                    -- trefmut
    (fun _a => Option.none)                                    -- tptrconst
    (fun _a => Option.none)                                    -- tptrmut
    (fun _a => Option.none)                                    -- trc
    (fun _el _r => Option.none)                                -- tset
    (fun _el => Option.none)                                   -- tseq
    (fun _id => Option.none)                                   -- trecord
    (fun _id => Option.none)                                   -- tclosure

theorem mexh_vector_isVector (e : TyAll) (n : Nat) :
    isVector (TyAll.vector e n) = true := rfl
theorem mexh_vector_shape (e : TyAll) (n : Nat) :
    vectorShape (TyAll.vector e n) = Option.some (Prod.mk e n) := rfl
theorem mexh_vector_shape_v4i32 :
    vectorShape (TyAll.vector TyAll.i32 4) = Option.some (Prod.mk TyAll.i32 4) := rfl

theorem mexh_nonvector_i32_isVector : isVector TyAll.i32 = false := rfl
theorem mexh_nonvector_i32_shape : vectorShape TyAll.i32 = Option.none := rfl
theorem mexh_nonvector_tbool_isVector : isVector TyAll.tbool = false := rfl
theorem mexh_nonvector_tbool_shape : vectorShape TyAll.tbool = Option.none := rfl
theorem mexh_nonvector_ptr_isVector : isVector TyAll.ptr = false := rfl
theorem mexh_nonvector_ptr_shape : vectorShape TyAll.ptr = Option.none := rfl
theorem mexh_nonvector_tstruct_isVector : isVector (TyAll.tstruct 0) = false := rfl
theorem mexh_nonvector_tstruct_shape : vectorShape (TyAll.tstruct 0) = Option.none := rfl
theorem mexh_nonvector_ttuple_isVector :
    isVector (TyAll.ttuple TyAll.i32 TyAll.i32) = false := rfl
theorem mexh_nonvector_ttuple_shape :
    vectorShape (TyAll.ttuple TyAll.i32 TyAll.i32) = Option.none := rfl

def optShapeIsSome : Option (Prod TyAll Nat) -> Bool := fun o =>
  @Option.casesOn (Prod TyAll Nat) (fun _ => Bool) o false (fun _p => true)

theorem mexh_isVector_iff_shape_vector (e : TyAll) (n : Nat) :
    isVector (TyAll.vector e n) = optShapeIsSome (vectorShape (TyAll.vector e n)) := rfl
theorem mexh_isVector_iff_shape_i32 :
    isVector TyAll.i32 = optShapeIsSome (vectorShape TyAll.i32) := rfl
theorem mexh_isVector_iff_shape_ptr :
    isVector TyAll.ptr = optShapeIsSome (vectorShape TyAll.ptr) := rfl

-- (3) TOTAL COVERAGE / EXHAUSTIVENESS.
def rem : TyAll -> Bool := fun t =>
  @TyAll.casesOn (fun _ => Bool) t
    false false false false false -- i8..i128  (numeric)
    false false false false false -- u8..u128  (numeric)
    false false false            -- f16 f32 f64 (numeric)
    true                         -- tbool   (leftover)
    (fun _e _n => false)         -- vector  (isVector)
    true                         -- ptr     (leftover)
    (fun _k => false)            -- fatptr  (reference)
    true                         -- tunit   (leftover)
    true                         -- never   (leftover)
    (fun _id => false)           -- tstruct (aggregate)
    (fun _el _len => false)      -- tarray  (aggregate)
    (fun _a _b => false)         -- ttuple  (aggregate)
    (fun _id => false)           -- tenum   (aggregate)
    (fun _id => true)            -- tfunc   (leftover)
    (fun _a => false)            -- tref      (reference)
    (fun _a => false)            -- trefmut   (reference)
    (fun _a => false)            -- tptrconst (reference)
    (fun _a => false)            -- tptrmut   (reference)
    (fun _a => false)            -- trc       (reference)
    (fun _el _r => false)        -- tset    (aggregate)
    (fun _el => false)           -- tseq    (aggregate)
    (fun _id => false)           -- trecord (aggregate)
    (fun _id => false)           -- tclosure (closure)

def coverAll : TyAll -> Bool := fun t =>
  Bool.or (Bool.or (isNumeric t) (isReference t))
    (Bool.or (isAggregate t)
      (Bool.or (isClosure t)
        (Bool.or (isVector t) (rem t))))

theorem mexh_cover_total (t : TyAll) : coverAll t = true :=
  @TyAll.casesOn (fun k => coverAll k = true) t
    rfl rfl rfl rfl rfl          -- i8..i128
    rfl rfl rfl rfl rfl          -- u8..u128
    rfl rfl rfl                  -- f16 f32 f64
    rfl                          -- tbool
    (fun _e _n => rfl)           -- vector
    rfl                          -- ptr
    (fun _k => rfl)              -- fatptr
    rfl                          -- tunit
    rfl                          -- never
    (fun _id => rfl)             -- tstruct
    (fun _el _len => rfl)        -- tarray
    (fun _a _b => rfl)           -- ttuple
    (fun _id => rfl)             -- tenum
    (fun _id => rfl)             -- tfunc
    (fun _a => rfl)              -- tref
    (fun _a => rfl)              -- trefmut
    (fun _a => rfl)              -- tptrconst
    (fun _a => rfl)              -- tptrmut
    (fun _a => rfl)              -- trc
    (fun _el _r => rfl)          -- tset
    (fun _el => rfl)             -- tseq
    (fun _id => rfl)             -- trecord
    (fun _id => rfl)             -- tclosure

theorem mexh_cover_i32 : coverAll TyAll.i32 = true := rfl
theorem mexh_cover_fatptr : coverAll (TyAll.fatptr FatKindA.fpstr) = true := rfl
theorem mexh_cover_tstruct : coverAll (TyAll.tstruct 0) = true := rfl
theorem mexh_cover_tclosure : coverAll (TyAll.tclosure 0) = true := rfl
theorem mexh_cover_vector : coverAll (TyAll.vector TyAll.i32 4) = true := rfl
theorem mexh_cover_ptr : coverAll TyAll.ptr = true := rfl
theorem mexh_cover_tfunc : coverAll (TyAll.tfunc 0) = true := rfl

theorem mexh_rem_ptr : rem TyAll.ptr = true := rfl
theorem mexh_rem_tbool : rem TyAll.tbool = true := rfl
theorem mexh_rem_tunit : rem TyAll.tunit = true := rfl
theorem mexh_rem_never : rem TyAll.never = true := rfl
theorem mexh_rem_tfunc : rem (TyAll.tfunc 0) = true := rfl
theorem mexh_rem_i32 : rem TyAll.i32 = false := rfl
theorem mexh_rem_fatptr : rem (TyAll.fatptr FatKindA.fpstr) = false := rfl
theorem mexh_rem_tstruct : rem (TyAll.tstruct 0) = false := rfl
theorem mexh_rem_tclosure : rem (TyAll.tclosure 0) = false := rfl
theorem mexh_rem_vector : rem (TyAll.vector TyAll.i32 4) = false := rfl

-- (4) bitWidth has-width SET.
def optIsSome : Option Nat -> Bool := fun o =>
  @Option.casesOn Nat (fun _ => Bool) o false (fun _w => true)

theorem mexh_hasWidth_i32 : optIsSome (bitWidth TyAll.i32) = true := rfl
theorem mexh_hasWidth_i128 : optIsSome (bitWidth TyAll.i128) = true := rfl
theorem mexh_hasWidth_u32 : optIsSome (bitWidth TyAll.u32) = true := rfl
theorem mexh_hasWidth_f64 : optIsSome (bitWidth TyAll.f64) = true := rfl
theorem mexh_hasWidth_tbool : optIsSome (bitWidth TyAll.tbool) = true := rfl
theorem mexh_hasWidth_v4i32 :
    optIsSome (bitWidth (TyAll.vector TyAll.i32 4)) = true := rfl
theorem mexh_hasWidth_v8bool :
    optIsSome (bitWidth (TyAll.vector TyAll.tbool 8)) = true := rfl

theorem mexh_noWidth_ptr : optIsSome (bitWidth TyAll.ptr) = false := rfl
theorem mexh_noWidth_fatptr :
    optIsSome (bitWidth (TyAll.fatptr FatKindA.fpstr)) = false := rfl
theorem mexh_noWidth_tunit : optIsSome (bitWidth TyAll.tunit) = false := rfl
theorem mexh_noWidth_never : optIsSome (bitWidth TyAll.never) = false := rfl
theorem mexh_noWidth_tstruct :
    optIsSome (bitWidth (TyAll.tstruct 0)) = false := rfl
theorem mexh_noWidth_tarray :
    optIsSome (bitWidth (TyAll.tarray 0 0)) = false := rfl
theorem mexh_noWidth_ttuple :
    optIsSome (bitWidth (TyAll.ttuple TyAll.i32 TyAll.i32)) = false := rfl
theorem mexh_noWidth_tref :
    optIsSome (bitWidth (TyAll.tref TyAll.i32)) = false := rfl
theorem mexh_noWidth_trc :
    optIsSome (bitWidth (TyAll.trc TyAll.i32)) = false := rfl
theorem mexh_noWidth_tset :
    optIsSome (bitWidth (TyAll.tset 0 SetReprA.boxed)) = false := rfl
theorem mexh_noWidth_tseq : optIsSome (bitWidth (TyAll.tseq 0)) = false := rfl
theorem mexh_noWidth_trecord :
    optIsSome (bitWidth (TyAll.trecord 0)) = false := rfl
theorem mexh_noWidth_tclosure :
    optIsSome (bitWidth (TyAll.tclosure 0)) = false := rfl
theorem mexh_noWidth_tfunc : optIsSome (bitWidth (TyAll.tfunc 0)) = false := rfl
theorem mexh_noWidth_tenum : optIsSome (bitWidth (TyAll.tenum 0)) = false := rfl

theorem mexh_hasWidth_tvec_i32 (n : Nat) :
    optIsSome (bitWidth (TyAll.vector TyAll.i32 n)) = true := rfl

theorem mexh_numeric_hasWidth_i32 :
    Bool.and (isNumeric TyAll.i32) (optIsSome (bitWidth TyAll.i32)) = true := rfl
theorem mexh_numeric_hasWidth_f32 :
    Bool.and (isNumeric TyAll.f32) (optIsSome (bitWidth TyAll.f32)) = true := rfl
theorem mexh_aggregate_noWidth_tstruct :
    Bool.and (isAggregate (TyAll.tstruct 0))
      (optIsSome (bitWidth (TyAll.tstruct 0))) = false := rfl

end TyAll
"#;

fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed)
            .map_err(|e| format!("elaborate/kernel-check error: {e}"))?;
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        if !failures.is_empty() {
            return Err(format!(
                "inner declaration(s) failed to elaborate:\n{}",
                failures.join("\n")
            ));
        }
    }
    Ok(env)
}

fn collect_failures(result: &ElabResult, out: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => {
            for r in results {
                collect_failures(r, out);
            }
        }
        ElabResult::Failed { name, error, .. } => out.push(format!("{name}: {error}")),
        _ => {}
    }
}

fn resolve_name(env: &Environment, short: &str) -> Name {
    env.constants()
        .map(|c| &c.name)
        .find(|n| n.last_component().as_deref() == Some(short))
        .cloned()
        .unwrap_or_else(|| panic!("no registered constant with short name `{short}`"))
}

fn assert_proven_to_foundations(env: &Environment, short: &str) {
    let name = resolve_name(env, short);
    let deps = env
        .axiom_deps(&name)
        .unwrap_or_else(|| panic!("{name}: not registered (axiom_deps returned None)"));
    assert!(
        deps.is_empty(),
        "{name} must be proven down to the foundational axioms, but rests on: {deps:?}"
    );
}

/// Every theorem over the unified `TyAll` inductive (the whole trust-ir Ty enum
/// as one Clean type): 325 per-variant faithfulness + cross-cutting metatheorems.
const TYALL_THEOREMS: &[&str] = &[
    "tya_bitWidth_i32",
    "tya_bitWidth_i128",
    "tya_bitWidth_u32",
    "tya_bitWidth_f32",
    "tya_bitWidth_tbool",
    "tya_bitWidth_v4i32",
    "tya_bitWidth_v8bool",
    "tya_bitWidth_ptr",
    "tya_bitWidth_fatptr",
    "tya_bitWidth_tunit",
    "tya_bitWidth_never",
    "tya_bitWidth_tstruct",
    "tya_bitWidth_tarray",
    "tya_bitWidth_ttuple",
    "tya_bitWidth_tenum",
    "tya_bitWidth_tfunc",
    "tya_bitWidth_tref",
    "tya_bitWidth_trc",
    "tya_bitWidth_tset",
    "tya_bitWidth_tseq",
    "tya_bitWidth_trecord",
    "tya_bitWidth_tclosure",
    "tya_isSigned_i32",
    "tya_isSigned_u32",
    "tya_isSigned_f32",
    "tya_isSigned_tbool",
    "tya_isSigned_vector",
    "tya_isSigned_ptr",
    "tya_isSigned_fatptr",
    "tya_isSigned_tunit",
    "tya_isSigned_never",
    "tya_isSigned_tstruct",
    "tya_isSigned_tarray",
    "tya_isSigned_ttuple",
    "tya_isSigned_tenum",
    "tya_isSigned_tfunc",
    "tya_isSigned_tref",
    "tya_isSigned_trc",
    "tya_isSigned_tset",
    "tya_isSigned_tseq",
    "tya_isSigned_trecord",
    "tya_isSigned_tclosure",
    "tya_isUnsigned_i32",
    "tya_isUnsigned_u32",
    "tya_isUnsigned_f32",
    "tya_isUnsigned_tbool",
    "tya_isUnsigned_vector",
    "tya_isUnsigned_ptr",
    "tya_isUnsigned_fatptr",
    "tya_isUnsigned_tunit",
    "tya_isUnsigned_never",
    "tya_isUnsigned_tstruct",
    "tya_isUnsigned_tarray",
    "tya_isUnsigned_ttuple",
    "tya_isUnsigned_tenum",
    "tya_isUnsigned_tfunc",
    "tya_isUnsigned_tref",
    "tya_isUnsigned_trc",
    "tya_isUnsigned_tset",
    "tya_isUnsigned_tseq",
    "tya_isUnsigned_trecord",
    "tya_isUnsigned_tclosure",
    "tya_isInteger_i32",
    "tya_isInteger_u32",
    "tya_isInteger_f32",
    "tya_isInteger_tbool",
    "tya_isInteger_vector",
    "tya_isInteger_ptr",
    "tya_isInteger_fatptr",
    "tya_isInteger_tunit",
    "tya_isInteger_never",
    "tya_isInteger_tstruct",
    "tya_isInteger_tarray",
    "tya_isInteger_ttuple",
    "tya_isInteger_tenum",
    "tya_isInteger_tfunc",
    "tya_isInteger_tref",
    "tya_isInteger_trc",
    "tya_isInteger_tset",
    "tya_isInteger_tseq",
    "tya_isInteger_trecord",
    "tya_isInteger_tclosure",
    "tya_isFloat_i32",
    "tya_isFloat_u32",
    "tya_isFloat_f32",
    "tya_isFloat_tbool",
    "tya_isFloat_vector",
    "tya_isFloat_ptr",
    "tya_isFloat_fatptr",
    "tya_isFloat_tunit",
    "tya_isFloat_never",
    "tya_isFloat_tstruct",
    "tya_isFloat_tarray",
    "tya_isFloat_ttuple",
    "tya_isFloat_tenum",
    "tya_isFloat_tfunc",
    "tya_isFloat_tref",
    "tya_isFloat_trc",
    "tya_isFloat_tset",
    "tya_isFloat_tseq",
    "tya_isFloat_trecord",
    "tya_isFloat_tclosure",
    "tya_isNumeric_i32",
    "tya_isNumeric_u32",
    "tya_isNumeric_f32",
    "tya_isNumeric_tbool",
    "tya_isNumeric_vector",
    "tya_isNumeric_ptr",
    "tya_isNumeric_fatptr",
    "tya_isNumeric_tunit",
    "tya_isNumeric_never",
    "tya_isNumeric_tstruct",
    "tya_isNumeric_tarray",
    "tya_isNumeric_ttuple",
    "tya_isNumeric_tenum",
    "tya_isNumeric_tfunc",
    "tya_isNumeric_tref",
    "tya_isNumeric_trc",
    "tya_isNumeric_tset",
    "tya_isNumeric_tseq",
    "tya_isNumeric_trecord",
    "tya_isNumeric_tclosure",
    "tya_isVector_i32",
    "tya_isVector_u32",
    "tya_isVector_f32",
    "tya_isVector_tbool",
    "tya_isVector_vector",
    "tya_isVector_ptr",
    "tya_isVector_fatptr",
    "tya_isVector_tunit",
    "tya_isVector_never",
    "tya_isVector_tstruct",
    "tya_isVector_tarray",
    "tya_isVector_ttuple",
    "tya_isVector_tenum",
    "tya_isVector_tfunc",
    "tya_isVector_tref",
    "tya_isVector_trc",
    "tya_isVector_tset",
    "tya_isVector_tseq",
    "tya_isVector_trecord",
    "tya_isVector_tclosure",
    "tya_isReference_i32",
    "tya_isReference_u32",
    "tya_isReference_f32",
    "tya_isReference_tbool",
    "tya_isReference_vector",
    "tya_isReference_ptr",
    "tya_isReference_fatptr",
    "tya_isReference_tunit",
    "tya_isReference_never",
    "tya_isReference_tstruct",
    "tya_isReference_tarray",
    "tya_isReference_ttuple",
    "tya_isReference_tenum",
    "tya_isReference_tfunc",
    "tya_isReference_tref",
    "tya_isReference_trefmut",
    "tya_isReference_tptrconst",
    "tya_isReference_tptrmut",
    "tya_isReference_trc",
    "tya_isReference_tset",
    "tya_isReference_tseq",
    "tya_isReference_trecord",
    "tya_isReference_tclosure",
    "tya_isAggregate_i32",
    "tya_isAggregate_u32",
    "tya_isAggregate_f32",
    "tya_isAggregate_tbool",
    "tya_isAggregate_vector",
    "tya_isAggregate_ptr",
    "tya_isAggregate_fatptr",
    "tya_isAggregate_tunit",
    "tya_isAggregate_never",
    "tya_isAggregate_tstruct",
    "tya_isAggregate_tarray",
    "tya_isAggregate_ttuple",
    "tya_isAggregate_tenum",
    "tya_isAggregate_tfunc",
    "tya_isAggregate_tref",
    "tya_isAggregate_trc",
    "tya_isAggregate_tset",
    "tya_isAggregate_tseq",
    "tya_isAggregate_trecord",
    "tya_isAggregate_tclosure",
    "tya_isClosure_i32",
    "tya_isClosure_u32",
    "tya_isClosure_f32",
    "tya_isClosure_tbool",
    "tya_isClosure_vector",
    "tya_isClosure_ptr",
    "tya_isClosure_fatptr",
    "tya_isClosure_tunit",
    "tya_isClosure_never",
    "tya_isClosure_tstruct",
    "tya_isClosure_tarray",
    "tya_isClosure_ttuple",
    "tya_isClosure_tenum",
    "tya_isClosure_tfunc",
    "tya_isClosure_tref",
    "tya_isClosure_trc",
    "tya_isClosure_tset",
    "tya_isClosure_tseq",
    "tya_isClosure_trecord",
    "tya_isClosure_tclosure",
    "tya_bitWidthWith_ptr",
    "tya_bitWidthWith_tref",
    "tya_bitWidthWith_trefmut",
    "tya_bitWidthWith_tptrconst",
    "tya_bitWidthWith_tptrmut",
    "tya_bitWidthWith_trc",
    "tya_bitWidthWith_fatptr",
    "tya_bitWidthWith_i32",
    "tya_bitWidthWith64_ptr",
    "tya_bitWidthWith64_tref",
    "tya_bitWidthWith64_fatptr",
    "tya_bitWidthWith64_i32",
    "mpart_signed_unsigned_disjoint",
    "mpart_signed_implies_integer",
    "mpart_unsigned_implies_integer",
    "mpart_integer_float_disjoint",
    "mpart_integer_implies_numeric",
    "mpart_float_implies_numeric",
    "mpart_vector_not_numeric",
    "mpart_vector_not_integer",
    "mpart_vector_not_float",
    "mpart_aggregate_closure_disjoint",
    "mpart_reference_numeric_disjoint",
    "mpart_reference_aggregate_disjoint",
    "mpart_reference_vector_disjoint",
    "mpart_reference_closure_disjoint",
    "mpart_aggregate_numeric_disjoint",
    "mpart_closure_not_numeric",
    "mpart_numeric_not_vector",
    "mwid_reference_no_fixed_width",
    "mwid_aggregate_no_fixed_width",
    "mwid_closure_no_fixed_width",
    "mwid_agree_i8",
    "mwid_agree_i16",
    "mwid_agree_i32",
    "mwid_agree_i64",
    "mwid_agree_i128",
    "mwid_agree_u8",
    "mwid_agree_f16",
    "mwid_agree_f32",
    "mwid_agree_f64",
    "mwid_agree_tbool",
    "mwid_agree_tunit",
    "mwid_agree_never",
    "mwid_agree_tstruct",
    "mwid_agree_ttuple",
    "mwid_agree_tset",
    "mwid_agree_tclosure",
    "mwid_fatptr_is_two_thin",
    "mwid_ptr_is_one_thin",
    "mwid_fat_double_thin_64",
    "mwid_optIsNone_ptr",
    "mwid_optIsNone_i32",
    "mexh_comp_eq_select",
    "mexh_compResult_v4i32",
    "mexh_selectCond_v4i32",
    "mexh_compResult_i32",
    "mexh_selectCond_ptr",
    "mexh_comp_eq_select_vector",
    "mexh_comp_eq_select_i32",
    "mexh_vector_isVector",
    "mexh_vector_shape",
    "mexh_vector_shape_v4i32",
    "mexh_nonvector_i32_isVector",
    "mexh_nonvector_i32_shape",
    "mexh_nonvector_tbool_isVector",
    "mexh_nonvector_tbool_shape",
    "mexh_nonvector_ptr_isVector",
    "mexh_nonvector_ptr_shape",
    "mexh_nonvector_tstruct_isVector",
    "mexh_nonvector_tstruct_shape",
    "mexh_nonvector_ttuple_isVector",
    "mexh_nonvector_ttuple_shape",
    "mexh_isVector_iff_shape_vector",
    "mexh_isVector_iff_shape_i32",
    "mexh_isVector_iff_shape_ptr",
    "mexh_cover_total",
    "mexh_cover_i32",
    "mexh_cover_fatptr",
    "mexh_cover_tstruct",
    "mexh_cover_tclosure",
    "mexh_cover_vector",
    "mexh_cover_ptr",
    "mexh_cover_tfunc",
    "mexh_rem_ptr",
    "mexh_rem_tbool",
    "mexh_rem_tunit",
    "mexh_rem_never",
    "mexh_rem_tfunc",
    "mexh_rem_i32",
    "mexh_rem_fatptr",
    "mexh_rem_tstruct",
    "mexh_rem_tclosure",
    "mexh_rem_vector",
    "mexh_hasWidth_i32",
    "mexh_hasWidth_i128",
    "mexh_hasWidth_u32",
    "mexh_hasWidth_f64",
    "mexh_hasWidth_tbool",
    "mexh_hasWidth_v4i32",
    "mexh_hasWidth_v8bool",
    "mexh_noWidth_ptr",
    "mexh_noWidth_fatptr",
    "mexh_noWidth_tunit",
    "mexh_noWidth_never",
    "mexh_noWidth_tstruct",
    "mexh_noWidth_tarray",
    "mexh_noWidth_ttuple",
    "mexh_noWidth_tref",
    "mexh_noWidth_trc",
    "mexh_noWidth_tset",
    "mexh_noWidth_tseq",
    "mexh_noWidth_trecord",
    "mexh_noWidth_tclosure",
    "mexh_noWidth_tfunc",
    "mexh_noWidth_tenum",
    "mexh_hasWidth_tvec_i32",
    "mexh_numeric_hasWidth_i32",
    "mexh_numeric_hasWidth_f32",
    "mexh_aggregate_noWidth_tstruct",
];

#[test]
fn tyall_unified_trust_type_elaborates_and_kernel_checks() {
    elaborate_module(TYALL_SOURCE).expect(
        "the entire trust-ir Ty enum as ONE Clean inductive (TyAll, 33 ctors) with all 11 \
         classifiers + structural metatheorems must elaborate and kernel-check",
    );
}

#[test]
fn tyall_theorems_are_proven_down_to_the_foundational_axioms() {
    let env = elaborate_module(TYALL_SOURCE)
        .expect("the unified TyAll module must elaborate before auditing its theorems");
    for thm in TYALL_THEOREMS {
        assert_proven_to_foundations(&env, thm);
    }
    println!(
        "ALL TRUST TYPES ARE ONE CLEAN TYPE: {} theorems over the unified TyAll inductive (the \
         complete trust-ir Ty enum), every one proven to the 3 foundational axioms (bedrock).",
        TYALL_THEOREMS.len()
    );
}
