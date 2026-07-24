// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! ALL TRUST TYPES ARE CLEAN TYPES — the COMPLETE trust-ir `Ty` enum
//! (first-party/trust-ir/crates/trust-ir/src/ty.rs), modeled faithfully in Clean
//! and proven down to the 3 foundational axioms.
//!
//! `trustir_typesystem_e2e.rs` already models the scalar CORE (i8..u128, bool,
//! unit, tuple) with the MIR<->trust-ir<->trust-cg correspondence. THIS file
//! closes every remaining `Ty` variant — the frontiers that were deferred there
//! — across four Clean namespaces that together image the WHOLE enum:
//!
//!   * `TyFloatScalar` — F16/F32/F64 floats, `Never`, bare `Ptr`
//!       (`bit_width`/`is_float`/`is_signed`/`is_unsigned`/`is_integer`/
//!        `is_numeric`/`is_reference`)
//!   * `TyRefPtr`      — `Ref`/`RefMut`/`PtrConst`/`PtrMut`/`Rc`/`FatPtr`
//!       (`is_reference` + target-dependent `bit_width_with`; fat = 2*ptr)
//!   * `TyVector`      — `Vector(elem, lanes)`
//!       (`is_vector`/`vector_shape`/`bit_width`/`is_integer_vector`/
//!        `is_bool_vector`/`is_float_vector`/`comparison_result_ty`/
//!        `select_condition_ty`)
//!   * `TyAggregate`   — `Struct`/`Array`/`Tuple`/`Enum`/`Func`/`Set`/`Sequence`/
//!        `Record`/`Closure` (`is_aggregate`/`is_closure`/`bit_width` + `SetRepr`
//!        identity + recursive `Den`)
//!
//! Every classifier matches the exact Rust method body in ty.rs, and every
//! theorem here passes the SAME `axiom_deps(name).is_empty()` bedrock gate that
//! `axiom_bedrock_check.rs` proves is real and discriminating. The four slices
//! are elaborated together in ONE environment, so this also proves they coexist.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

const TYFULL_SOURCE: &str = r#"
namespace TyFloatScalar

-- The FLOATS + Never + bare Ptr scalar frontier of trust-ir's `Ty`, plus two
-- contrast anchors (tbool, ti32). Constructor order is fixed (the casesOn
-- minors below follow it): f16, f32, f64, never, ptr, tbool, ti32.
inductive TyFS where
  | f16 : TyFS
  | f32 : TyFS
  | f64 : TyFS
  | never : TyFS
  | ptr : TyFS
  | tbool : TyFS
  | ti32 : TyFS

-- `Ty::bit_width` (ty.rs:142): F16->some 16, F32->some 32, F64->some 64,
-- Bool->some 1, I32->some 32; Never and bare Ptr are width-less -> none.
def bitWidth : TyFS -> Option Nat := fun t =>
  @TyFS.casesOn (fun _ => Option Nat) t
    (Option.some 16)
    (Option.some 32)
    (Option.some 64)
    Option.none
    Option.none
    (Option.some 1)
    (Option.some 32)

-- `Ty::is_float` (ty.rs:205): exactly F16/F32/F64.
def isFloat : TyFS -> Bool := fun t =>
  @TyFS.casesOn (fun _ => Bool) t
    true true true
    false false false false

-- `Ty::is_signed` (ty.rs:196): I8..I128; in this slice only ti32.
def isSigned : TyFS -> Bool := fun t =>
  @TyFS.casesOn (fun _ => Bool) t
    false false false false false false
    true

-- `Ty::is_unsigned` (ty.rs:201): U8..U128; none present in this slice.
def isUnsigned : TyFS -> Bool := fun t =>
  @TyFS.casesOn (fun _ => Bool) t
    false false false false false false false

-- `Ty::is_integer` (ty.rs:191): is_signed OR is_unsigned.
def isInteger : TyFS -> Bool := fun t => Bool.or (isSigned t) (isUnsigned t)

-- `Ty::is_numeric` (ty.rs:209): is_integer OR is_float.
def isNumeric : TyFS -> Bool := fun t => Bool.or (isInteger t) (isFloat t)

-- `Ty::is_reference` (ty.rs:320): true only for Ref/RefMut/PtrConst/PtrMut/Rc/
-- FatPtr (a DIFFERENT slice). Bare Ptr, Never, and the floats are all NOT
-- references in this slice.
def isReference : TyFS -> Bool := fun t =>
  @TyFS.casesOn (fun _ => Bool) t
    false false false false false false false

-- ===========================================================================
-- FAITHFULNESS to `Ty::bit_width` (ty.rs:142). Each variant by casesOn iota.
-- ===========================================================================
theorem flt_bitWidth_f16 : bitWidth TyFS.f16 = Option.some 16 := rfl
theorem flt_bitWidth_f32 : bitWidth TyFS.f32 = Option.some 32 := rfl
theorem flt_bitWidth_f64 : bitWidth TyFS.f64 = Option.some 64 := rfl
theorem flt_bitWidth_never : bitWidth TyFS.never = Option.none := rfl
theorem flt_bitWidth_ptr : bitWidth TyFS.ptr = Option.none := rfl
theorem flt_bitWidth_tbool : bitWidth TyFS.tbool = Option.some 1 := rfl
theorem flt_bitWidth_ti32 : bitWidth TyFS.ti32 = Option.some 32 := rfl

-- FAITHFULNESS to `Ty::is_float` (ty.rs:205).
theorem flt_isFloat_f16 : isFloat TyFS.f16 = true := rfl
theorem flt_isFloat_f32 : isFloat TyFS.f32 = true := rfl
theorem flt_isFloat_f64 : isFloat TyFS.f64 = true := rfl
theorem flt_isFloat_never : isFloat TyFS.never = false := rfl
theorem flt_isFloat_ptr : isFloat TyFS.ptr = false := rfl
theorem flt_isFloat_tbool : isFloat TyFS.tbool = false := rfl
theorem flt_isFloat_ti32 : isFloat TyFS.ti32 = false := rfl

-- FAITHFULNESS to `Ty::is_signed` (ty.rs:196).
theorem flt_isSigned_f16 : isSigned TyFS.f16 = false := rfl
theorem flt_isSigned_f32 : isSigned TyFS.f32 = false := rfl
theorem flt_isSigned_f64 : isSigned TyFS.f64 = false := rfl
theorem flt_isSigned_never : isSigned TyFS.never = false := rfl
theorem flt_isSigned_ptr : isSigned TyFS.ptr = false := rfl
theorem flt_isSigned_tbool : isSigned TyFS.tbool = false := rfl
theorem flt_isSigned_ti32 : isSigned TyFS.ti32 = true := rfl

-- FAITHFULNESS to `Ty::is_unsigned` (ty.rs:201): all false in this slice.
theorem flt_isUnsigned_f16 : isUnsigned TyFS.f16 = false := rfl
theorem flt_isUnsigned_f32 : isUnsigned TyFS.f32 = false := rfl
theorem flt_isUnsigned_f64 : isUnsigned TyFS.f64 = false := rfl
theorem flt_isUnsigned_never : isUnsigned TyFS.never = false := rfl
theorem flt_isUnsigned_ptr : isUnsigned TyFS.ptr = false := rfl
theorem flt_isUnsigned_tbool : isUnsigned TyFS.tbool = false := rfl
theorem flt_isUnsigned_ti32 : isUnsigned TyFS.ti32 = false := rfl

-- FAITHFULNESS to `Ty::is_integer` (ty.rs:191): only ti32 here.
theorem flt_isInteger_f16 : isInteger TyFS.f16 = false := rfl
theorem flt_isInteger_f32 : isInteger TyFS.f32 = false := rfl
theorem flt_isInteger_f64 : isInteger TyFS.f64 = false := rfl
theorem flt_isInteger_never : isInteger TyFS.never = false := rfl
theorem flt_isInteger_ptr : isInteger TyFS.ptr = false := rfl
theorem flt_isInteger_tbool : isInteger TyFS.tbool = false := rfl
theorem flt_isInteger_ti32 : isInteger TyFS.ti32 = true := rfl

-- FAITHFULNESS to `Ty::is_numeric` (ty.rs:209): floats and ti32 are numeric;
-- Bool, Never, Ptr are not.
theorem flt_isNumeric_f16 : isNumeric TyFS.f16 = true := rfl
theorem flt_isNumeric_f32 : isNumeric TyFS.f32 = true := rfl
theorem flt_isNumeric_f64 : isNumeric TyFS.f64 = true := rfl
theorem flt_isNumeric_never : isNumeric TyFS.never = false := rfl
theorem flt_isNumeric_ptr : isNumeric TyFS.ptr = false := rfl
theorem flt_isNumeric_tbool : isNumeric TyFS.tbool = false := rfl
theorem flt_isNumeric_ti32 : isNumeric TyFS.ti32 = true := rfl

-- FAITHFULNESS to `Ty::is_reference` (ty.rs:320): bare Ptr is NOT a reference,
-- Never is not, the floats are not. (Only &/&mut/*const/*mut/Rc/FatPtr are
-- references -- a different slice.)
theorem flt_isReference_f16 : isReference TyFS.f16 = false := rfl
theorem flt_isReference_f32 : isReference TyFS.f32 = false := rfl
theorem flt_isReference_f64 : isReference TyFS.f64 = false := rfl
theorem flt_isReference_never : isReference TyFS.never = false := rfl
theorem flt_isReference_ptr : isReference TyFS.ptr = false := rfl
theorem flt_isReference_tbool : isReference TyFS.tbool = false := rfl
theorem flt_isReference_ti32 : isReference TyFS.ti32 = false := rfl

end TyFloatScalar

namespace TyRefPtr

-- A faithful image of `FatPtrKind` (ty.rs:39): Slice(TyId) | Str |
-- TraitObject{trait_id}. The `TyId`/`trait_id` payloads are `Nat` here (they do
-- not affect any classifier in this slice — is_reference/bit_width ignore them).
inductive FatKind where
  | fpslice : Nat -> FatKind
  | fpstr : FatKind
  | fptraitobj : Nat -> FatKind

-- The reference/pointer frontier of trust-ir `Ty`. The five box-carrying
-- variants (Ref/RefMut/PtrConst/PtrMut/Rc) are RECURSIVE (carry an inner `Ty`),
-- modeled by a self-referential field. `fatptr` carries a `FatKind`. `ptr` is
-- the bare opaque pointer (NOT a reference). `ti32` is the nested non-pointer
-- scalar (Ty::I32) used to nest inside the reference constructors.
-- Constructor order is fixed (the casesOn/rec minors below follow it):
--   tref, trefmut, tptrconst, tptrmut, trc, fatptr, ptr, ti32.
inductive TyRP where
  | tref : TyRP -> TyRP
  | trefmut : TyRP -> TyRP
  | tptrconst : TyRP -> TyRP
  | tptrmut : TyRP -> TyRP
  | trc : TyRP -> TyRP
  | fatptr : FatKind -> TyRP
  | ptr : TyRP
  | ti32 : TyRP

-- trust-ir `Ty::is_reference` (ty.rs:320), faithfully: Ref/RefMut/PtrConst/
-- PtrMut/Rc/FatPtr -> true; bare Ptr -> false; the nested scalar (I32) -> false.
-- The five recursive minors bind their sub-value (unused — is_reference does not
-- recurse, it matches on the OUTER constructor only).
def isReference : TyRP -> Bool := fun t =>
  @TyRP.casesOn (fun _ => Bool) t
    (fun _a => true)
    (fun _a => true)
    (fun _a => true)
    (fun _a => true)
    (fun _a => true)
    (fun _k => true)
    false
    false

-- trust-ir `Ty::bit_width` (ty.rs:142, target-FREE): EVERY pointer-like type
-- (Ref/RefMut/PtrConst/PtrMut/Rc/FatPtr/Ptr) -> none. The nested scalar (I32)
-- -> some 32 (ty.rs:147). `Option Nat` mirrors the Rust `Option<u32>`.
def bitWidth : TyRP -> Option Nat := fun t =>
  @TyRP.casesOn (fun _ => Option Nat) t
    (fun _a => Option.none)
    (fun _a => Option.none)
    (fun _a => Option.none)
    (fun _a => Option.none)
    (fun _a => Option.none)
    (fun _k => Option.none)
    Option.none
    (Option.some 32)

-- trust-ir `Ty::bit_width_with` (ty.rs:174): given the target thin-pointer width
-- `pb` (in bits), Ref/RefMut/PtrConst/PtrMut/Rc/Ptr -> some pb; FatPtr(_) ->
-- some (pb + pb) [== 2*pb, modeled as Nat.add for rfl-reducibility]; every other
-- type delegates to bit_width, so the nested scalar (I32) -> some 32.
def bitWidthWith : Nat -> TyRP -> Option Nat := fun pb t =>
  @TyRP.casesOn (fun _ => Option Nat) t
    (fun _a => Option.some pb)
    (fun _a => Option.some pb)
    (fun _a => Option.some pb)
    (fun _a => Option.some pb)
    (fun _a => Option.some pb)
    (fun _k => Option.some (Nat.add pb pb))
    (Option.some pb)
    (Option.some 32)

-- ===========================================================================
-- FAITHFULNESS to `Ty::is_reference` (ty.rs:320). The five box-carrying refs are
-- references; FatPtr is a reference; bare Ptr is NOT; the nested scalar is NOT.
-- All by `casesOn` iota (`rfl`). We use `ti32` (a non-pointer) as the inner type
-- nested inside the recursive constructors.
-- ===========================================================================
theorem ref_isRef_tref : isReference (TyRP.tref TyRP.ti32) = true := rfl
theorem ref_isRef_trefmut : isReference (TyRP.trefmut TyRP.ti32) = true := rfl
theorem ref_isRef_tptrconst : isReference (TyRP.tptrconst TyRP.ti32) = true := rfl
theorem ref_isRef_tptrmut : isReference (TyRP.tptrmut TyRP.ti32) = true := rfl
theorem ref_isRef_trc : isReference (TyRP.trc TyRP.ti32) = true := rfl
theorem ref_isRef_fatptr_slice : isReference (TyRP.fatptr (FatKind.fpslice 7)) = true := rfl
theorem ref_isRef_fatptr_str : isReference (TyRP.fatptr FatKind.fpstr) = true := rfl
theorem ref_isRef_fatptr_traitobj : isReference (TyRP.fatptr (FatKind.fptraitobj 3)) = true := rfl
theorem ref_isRef_ptr : isReference TyRP.ptr = false := rfl
theorem ref_isRef_ti32 : isReference TyRP.ti32 = false := rfl

-- is_reference matches on the OUTER constructor only — it is invariant under the
-- choice of inner type (here a reference nested inside a reference).
theorem ref_isRef_tref_holds_any (t : TyRP) : isReference (TyRP.tref t) = true := rfl
-- A nesting example: &(&mut i32) is still a reference (the prompt's named case).
theorem ref_isRef_nested : isReference (TyRP.tref (TyRP.trefmut TyRP.ti32)) = true := rfl

-- ===========================================================================
-- FAITHFULNESS to `Ty::bit_width` (ty.rs:142, target-FREE): every pointer-like
-- type has NO fixed width; the nested scalar I32 has width 32.
-- ===========================================================================
theorem ref_bw_tref : bitWidth (TyRP.tref TyRP.ti32) = Option.none := rfl
theorem ref_bw_trefmut : bitWidth (TyRP.trefmut TyRP.ti32) = Option.none := rfl
theorem ref_bw_tptrconst : bitWidth (TyRP.tptrconst TyRP.ti32) = Option.none := rfl
theorem ref_bw_tptrmut : bitWidth (TyRP.tptrmut TyRP.ti32) = Option.none := rfl
theorem ref_bw_trc : bitWidth (TyRP.trc TyRP.ti32) = Option.none := rfl
theorem ref_bw_fatptr : bitWidth (TyRP.fatptr FatKind.fpstr) = Option.none := rfl
theorem ref_bw_ptr : bitWidth TyRP.ptr = Option.none := rfl
theorem ref_bw_ti32 : bitWidth TyRP.ti32 = Option.some 32 := rfl

-- ===========================================================================
-- FAITHFULNESS to `Ty::bit_width_with` (ty.rs:174). Thin pointer-like ->
-- some pb; FatPtr -> some (pb+pb); the nested scalar I32 delegates to bit_width
-- -> some 32. Proven both at a CONCRETE pb (64) and SYMBOLICALLY (any pb).
-- ===========================================================================
-- Symbolic (any pb : Nat):
theorem ref_bww_tref (pb : Nat) : bitWidthWith pb (TyRP.tref TyRP.ti32) = Option.some pb := rfl
theorem ref_bww_trefmut (pb : Nat) : bitWidthWith pb (TyRP.trefmut TyRP.ti32) = Option.some pb := rfl
theorem ref_bww_tptrconst (pb : Nat) : bitWidthWith pb (TyRP.tptrconst TyRP.ti32) = Option.some pb := rfl
theorem ref_bww_tptrmut (pb : Nat) : bitWidthWith pb (TyRP.tptrmut TyRP.ti32) = Option.some pb := rfl
theorem ref_bww_trc (pb : Nat) : bitWidthWith pb (TyRP.trc TyRP.ti32) = Option.some pb := rfl
theorem ref_bww_ptr (pb : Nat) : bitWidthWith pb TyRP.ptr = Option.some pb := rfl
theorem ref_bww_fatptr (pb : Nat) : bitWidthWith pb (TyRP.fatptr FatKind.fpstr) = Option.some (Nat.add pb pb) := rfl
theorem ref_bww_ti32 (pb : Nat) : bitWidthWith pb TyRP.ti32 = Option.some 32 := rfl

-- The fat-pointer width is pb+pb (two pointer-sized lanes), matching ty.rs:182
-- `pointer_bits.checked_mul(2)` (modeled as Nat.add pb pb, the rfl-reducible form
-- of 2*pb).
theorem ref_bww_fatptr_is_double (pb : Nat) :
    bitWidthWith pb (TyRP.fatptr (FatKind.fptraitobj 9)) = Option.some (Nat.add pb pb) := rfl

-- Concrete pb = 64 (aarch64 / x86-64 thin-pointer width): thin -> some 64,
-- fat -> some 128 (= 64 + 64).
theorem ref_bww64_tref : bitWidthWith 64 (TyRP.tref TyRP.ti32) = Option.some 64 := rfl
theorem ref_bww64_trc : bitWidthWith 64 (TyRP.trc TyRP.ti32) = Option.some 64 := rfl
theorem ref_bww64_ptr : bitWidthWith 64 TyRP.ptr = Option.some 64 := rfl
theorem ref_bww64_fatptr : bitWidthWith 64 (TyRP.fatptr FatKind.fpstr) = Option.some 128 := rfl
theorem ref_bww64_ti32 : bitWidthWith 64 TyRP.ti32 = Option.some 32 := rfl

-- Concrete pb = 32 (wasm32 thin-pointer width): thin -> some 32, fat -> some 64.
theorem ref_bww32_tptrconst : bitWidthWith 32 (TyRP.tptrconst TyRP.ti32) = Option.some 32 := rfl
theorem ref_bww32_fatptr : bitWidthWith 32 (TyRP.fatptr (FatKind.fpslice 1)) = Option.some 64 := rfl

-- ===========================================================================
-- CROSS-CLASSIFIER coherence: a type that is_reference() either has no fixed
-- bit_width (every pointer-like ref) — and bit_width_with resolves it to some
-- pointer-sized value. Stated per-constructor (rfl), partitioning the slice.
-- ===========================================================================
-- The bare Ptr is the lone NON-reference pointer-like type (is_reference=false)
-- yet still has no fixed bit_width and resolves under bit_width_with.
theorem ref_ptr_not_ref_but_pointer_sized :
    bitWidthWith 64 TyRP.ptr = Option.some 64 := rfl
-- The nested scalar is neither a reference nor pointer-sized: it keeps width 32
-- under both bit_width and bit_width_with (the delegation case, ty.rs:186).
theorem ref_scalar_keeps_width (pb : Nat) :
    bitWidthWith pb TyRP.ti32 = bitWidth TyRP.ti32 := rfl

end TyRefPtr

namespace TyVector

-- A faithful Clean image of the SIMD Vector frontier of trust-ir's `Ty`.
-- Scalar element types (the realistic vector element types) plus the recursive
-- vector constructor `tvec : TyV -> Nat -> TyV` (element type inline + lane count,
-- mirroring `Vector(Box<Ty>, u32)`). Constructor order is fixed; the casesOn/rec
-- minors below follow it: ti32, tu32, tf32, tbool, tvec.
inductive TyV where
  | ti32 : TyV
  | tu32 : TyV
  | tf32 : TyV
  | tbool : TyV
  | tvec : TyV -> Nat -> TyV

-- ===========================================================================
-- is_vector (ty.rs:214): Vector -> true; every scalar -> false.
-- The tvec minor binds the element sub-value, its IH, and the lane Nat.
-- ===========================================================================
def isVector : TyV -> Bool := fun t =>
  @TyV.casesOn (fun _ => Bool) t
    false false false false
    (fun _e _n => true)

theorem vec_isVector_ti32 : isVector TyV.ti32 = false := rfl
theorem vec_isVector_tu32 : isVector TyV.tu32 = false := rfl
theorem vec_isVector_tf32 : isVector TyV.tf32 = false := rfl
theorem vec_isVector_tbool : isVector TyV.tbool = false := rfl
theorem vec_isVector_tvec (e : TyV) (n : Nat) : isVector (TyV.tvec e n) = true := rfl

-- ===========================================================================
-- Scalar element classifiers (ty.rs:191,205): is_integer / is_float on the
-- scalar element types. Used to define the vector classifiers faithfully.
-- ===========================================================================
def isInteger : TyV -> Bool := fun t =>
  @TyV.casesOn (fun _ => Bool) t
    true false false false
    (fun _e _n => false)

def isFloat : TyV -> Bool := fun t =>
  @TyV.casesOn (fun _ => Bool) t
    false false true false
    (fun _e _n => false)

-- is_numeric (ty.rs:209) = is_integer || is_float. On vectors this is false
-- (a Vector is neither a scalar integer nor a scalar float).
def isNumeric : TyV -> Bool := fun t => Bool.or (isInteger t) (isFloat t)

-- The scalar classifiers are FALSE on vectors (a vector is not a scalar int/float).
theorem vec_isInteger_tvec (e : TyV) (n : Nat) : isInteger (TyV.tvec e n) = false := rfl
theorem vec_isFloat_tvec (e : TyV) (n : Nat) : isFloat (TyV.tvec e n) = false := rfl
theorem vec_isNumeric_tvec (e : TyV) (n : Nat) : isNumeric (TyV.tvec e n) = false := rfl
theorem vec_isInteger_ti32 : isInteger TyV.ti32 = true := rfl
theorem vec_isFloat_tf32 : isFloat TyV.tf32 = true := rfl

-- ===========================================================================
-- vector_shape (ty.rs:219): Vector(elem,lanes) -> Some (elem,lanes); else None.
-- Modeled as Option (Prod TyV Nat).
-- ===========================================================================
def vectorShape : TyV -> Option (Prod TyV Nat) := fun t =>
  @TyV.casesOn (fun _ => Option (Prod TyV Nat)) t
    Option.none Option.none Option.none Option.none
    (fun e n => Option.some (Prod.mk e n))

theorem vec_vectorShape_ti32 : vectorShape TyV.ti32 = Option.none := rfl
theorem vec_vectorShape_tbool : vectorShape TyV.tbool = Option.none := rfl
theorem vec_vectorShape_tvec (e : TyV) (n : Nat) :
    vectorShape (TyV.tvec e n) = Option.some (Prod.mk e n) := rfl
-- Concrete <4 x i32>: shape is exactly (i32, 4).
theorem vec_vectorShape_v4i32 :
    vectorShape (TyV.tvec TyV.ti32 4) = Option.some (Prod.mk TyV.ti32 4) := rfl

-- ===========================================================================
-- bit_width (ty.rs:142,153): scalar widths, and Vector(elem,lanes) ->
-- elem.bit_width *checked* lanes. The Clean model returns the un-truncated
-- product Some (w*n) (honest scope: Rust returns None on u32 overflow).
-- ===========================================================================
def bitWidth : TyV -> Option Nat := fun t =>
  @TyV.rec (fun _ => Option Nat)
    (Option.some 32) (Option.some 32) (Option.some 32) (Option.some 1)
    (fun _e n ihE =>
      @Option.casesOn Nat (fun _ => Option Nat) ihE
        Option.none
        (fun w => Option.some (Nat.mul w n)))
    t

-- Scalar widths (ty.rs:144-149): i32/u32/f32 -> 32, bool -> 1.
theorem vec_bitWidth_ti32 : bitWidth TyV.ti32 = Option.some 32 := rfl
theorem vec_bitWidth_tu32 : bitWidth TyV.tu32 = Option.some 32 := rfl
theorem vec_bitWidth_tf32 : bitWidth TyV.tf32 = Option.some 32 := rfl
theorem vec_bitWidth_tbool : bitWidth TyV.tbool = Option.some 1 := rfl

-- Concrete vector widths (match Rust checked_mul exactly, no overflow):
--   <4 x i32>  => Some 128  (32*4)
--   <8 x bool> => Some 8    (1*8)
--   <2 x i32>  => Some 64   (32*2)
theorem vec_bitWidth_v4i32 : bitWidth (TyV.tvec TyV.ti32 4) = Option.some 128 := rfl
theorem vec_bitWidth_v8bool : bitWidth (TyV.tvec TyV.tbool 8) = Option.some 8 := rfl
theorem vec_bitWidth_v2i32 : bitWidth (TyV.tvec TyV.ti32 2) = Option.some 64 := rfl

-- General symbolic lemma for an i32-element vector: bitWidth (tvec ti32 n) =
-- Some (32 * n). The element bitWidth reduces (ti32 -> some 32), so the
-- Option.casesOn picks the some-branch and the result is Some (Nat.mul 32 n).
theorem vec_bitWidth_tvec_i32 (n : Nat) :
    bitWidth (TyV.tvec TyV.ti32 n) = Option.some (Nat.mul 32 n) := rfl

-- ===========================================================================
-- is_integer_vector / is_bool_vector / is_float_vector (ty.rs:274-285):
-- lanes>0 && (elem classifier). The lanes>0 test is a Nat.casesOn on the lane
-- count (zero -> false, succ _ -> the element test).
-- ===========================================================================
def isIntegerVector : TyV -> Bool := fun t =>
  @TyV.casesOn (fun _ => Bool) t
    false false false false
    (fun e n => @Nat.casesOn (fun _ => Bool) n false (fun _k => isInteger e))

def isBoolVector : TyV -> Bool := fun t =>
  @TyV.casesOn (fun _ => Bool) t
    false false false false
    (fun e n =>
      @Nat.casesOn (fun _ => Bool) n false
        (fun _k => @TyV.casesOn (fun _ => Bool) e false false false true (fun _a _b => false)))

def isFloatVector : TyV -> Bool := fun t =>
  @TyV.casesOn (fun _ => Bool) t
    false false false false
    (fun e n => @Nat.casesOn (fun _ => Bool) n false (fun _k => isFloat e))

-- nonzero lanes => the element test governs.
theorem vec_isIntegerVector_succ (k : Nat) :
    isIntegerVector (TyV.tvec TyV.ti32 (Nat.succ k)) = true := rfl
theorem vec_isIntegerVector_zero :
    isIntegerVector (TyV.tvec TyV.ti32 0) = false := rfl
theorem vec_isBoolVector_succ (k : Nat) :
    isBoolVector (TyV.tvec TyV.tbool (Nat.succ k)) = true := rfl
theorem vec_isBoolVector_zero :
    isBoolVector (TyV.tvec TyV.tbool 0) = false := rfl
theorem vec_isFloatVector_succ (k : Nat) :
    isFloatVector (TyV.tvec TyV.tf32 (Nat.succ k)) = true := rfl
theorem vec_isFloatVector_zero :
    isFloatVector (TyV.tvec TyV.tf32 0) = false := rfl
-- A float-element vector is NOT an integer vector (element test discriminates).
theorem vec_isIntegerVector_tf32_succ (k : Nat) :
    isIntegerVector (TyV.tvec TyV.tf32 (Nat.succ k)) = false := rfl
-- An integer-element vector is NOT a bool vector.
theorem vec_isBoolVector_ti32_succ (k : Nat) :
    isBoolVector (TyV.tvec TyV.ti32 (Nat.succ k)) = false := rfl
-- Concrete <4 x i32> is an integer vector.
theorem vec_isIntegerVector_v4i32 : isIntegerVector (TyV.tvec TyV.ti32 4) = true := rfl

-- ===========================================================================
-- comparison_result_ty / select_condition_ty (ty.rs:289,300):
-- Vector(_,lanes) -> Vector(Bool,lanes); scalar -> Bool. Both same shape.
-- Modeled returning TyV (scalar -> tbool, vector -> tvec tbool lanes).
-- ===========================================================================
def compResult : TyV -> TyV := fun t =>
  @TyV.casesOn (fun _ => TyV) t
    TyV.tbool TyV.tbool TyV.tbool TyV.tbool
    (fun _e n => TyV.tvec TyV.tbool n)

def selectCond : TyV -> TyV := fun t =>
  @TyV.casesOn (fun _ => TyV) t
    TyV.tbool TyV.tbool TyV.tbool TyV.tbool
    (fun _e n => TyV.tvec TyV.tbool n)

-- Vector comparison/select condition: <N x bool>, preserving the lane count,
-- independent of element type.
theorem vec_compResult_tvec (e : TyV) (n : Nat) :
    compResult (TyV.tvec e n) = TyV.tvec TyV.tbool n := rfl
theorem vec_selectCond_tvec (e : TyV) (n : Nat) :
    selectCond (TyV.tvec e n) = TyV.tvec TyV.tbool n := rfl
theorem vec_compResult_v4i32 :
    compResult (TyV.tvec TyV.ti32 4) = TyV.tvec TyV.tbool 4 := rfl
theorem vec_selectCond_v4i32 :
    selectCond (TyV.tvec TyV.ti32 4) = TyV.tvec TyV.tbool 4 := rfl
-- Scalars use a scalar bool condition/result.
theorem vec_compResult_ti32 : compResult TyV.ti32 = TyV.tbool := rfl
theorem vec_selectCond_ti32 : selectCond TyV.ti32 = TyV.tbool := rfl
theorem vec_selectCond_tf32 : selectCond TyV.tf32 = TyV.tbool := rfl

-- comparison_result and select_condition agree on every type (ty.rs:289 vs 300
-- are the same shape), by casesOn.
theorem vec_comp_eq_select (t : TyV) : compResult t = selectCond t :=
  @TyV.casesOn (fun k => compResult k = selectCond k) t
    rfl rfl rfl rfl
    (fun _e _n => rfl)

end TyVector

namespace TyAggregate

-- Set representation hint, faithful to trust-ir `SetRepr` (ty.rs:14): Bitset | Boxed.
-- Part of `Ty::Set` identity (Set(7,Bitset) != Set(7,Boxed)). Two constructors
-- (so it is a real sum type, not compiled to a structure).
inductive SetReprA where
  | bitset : SetReprA
  | boxed : SetReprA

-- Aggregate + closure frontier of trust-ir `Ty`. Constructor order is fixed; the
-- casesOn/rec minors below follow it:
--   ti32, tstruct, tarray, ttuple, tenum, tfunc, tset, tseq, trecord, tclosure.
-- `ttuple` is a BINARY tuple (TyA -> TyA -> TyA), recursive (like trust-ir's
-- Tuple(Vec<Ty>)) so the denotation can be a genuine recursive product, while
-- avoiding the nested-inductive (List TyA) elaboration hazard.
inductive TyA where
  | ti32 : TyA
  | tstruct : Nat -> TyA
  | tarray : Nat -> Nat -> TyA
  | ttuple : TyA -> TyA -> TyA
  | tenum : Nat -> TyA
  | tfunc : Nat -> TyA
  | tset : Nat -> SetReprA -> TyA
  | tseq : Nat -> TyA
  | trecord : Nat -> TyA
  | tclosure : Nat -> TyA

-- trust-ir `Ty::is_aggregate` (ty.rs:338): Set, Sequence, Record, Tuple, Array,
-- Struct, Enum -> true; Closure, Func, scalar -> false.
def isAggregate : TyA -> Bool := fun t =>
  @TyA.casesOn (fun _ => Bool) t
    false                       -- ti32
    (fun _id => true)           -- tstruct
    (fun _el _len => true)      -- tarray
    (fun _a _b => true)         -- ttuple
    (fun _id => true)           -- tenum
    (fun _id => false)          -- tfunc
    (fun _el _r => true)        -- tset
    (fun _el => true)           -- tseq
    (fun _id => true)           -- trecord
    (fun _id => false)          -- tclosure

-- trust-ir `Ty::is_closure` (ty.rs:352): Closure -> true; everything else false.
def isClosure : TyA -> Bool := fun t =>
  @TyA.casesOn (fun _ => Bool) t
    false                       -- ti32
    (fun _id => false)          -- tstruct
    (fun _el _len => false)     -- tarray
    (fun _a _b => false)        -- ttuple
    (fun _id => false)          -- tenum
    (fun _id => false)          -- tfunc
    (fun _el _r => false)       -- tset
    (fun _el => false)          -- tseq
    (fun _id => false)          -- trecord
    (fun _id => true)           -- tclosure

-- trust-ir `Ty::bit_width` (ty.rs:142): every aggregate / closure / func has no
-- target-independent width -> Option.none. The scalar anchor i32 -> some 32.
def bitWidth : TyA -> Option Nat := fun t =>
  @TyA.casesOn (fun _ => Option Nat) t
    (Option.some 32)            -- ti32
    (fun _id => Option.none)    -- tstruct
    (fun _el _len => Option.none) -- tarray
    (fun _a _b => Option.none)  -- ttuple
    (fun _id => Option.none)    -- tenum
    (fun _id => Option.none)    -- tfunc
    (fun _el _r => Option.none) -- tset
    (fun _el => Option.none)    -- tseq
    (fun _id => Option.none)    -- trecord
    (fun _id => Option.none)    -- tclosure

-- Discriminator that observes a `tset`'s `SetReprA` (showing repr is part of the
-- type and is recoverable): defaults to bitset for non-set ctors (irrelevant —
-- only the tset case is exercised by the faithfulness theorems below).
def setRepr : TyA -> SetReprA := fun t =>
  @TyA.casesOn (fun _ => SetReprA) t
    SetReprA.bitset             -- ti32
    (fun _id => SetReprA.bitset)    -- tstruct
    (fun _el _len => SetReprA.bitset) -- tarray
    (fun _a _b => SetReprA.bitset)  -- ttuple
    (fun _id => SetReprA.bitset)    -- tenum
    (fun _id => SetReprA.bitset)    -- tfunc
    (fun _el r => r)            -- tset  (returns the carried repr)
    (fun _el => SetReprA.bitset)    -- tseq
    (fun _id => SetReprA.bitset)    -- trecord
    (fun _id => SetReprA.bitset)    -- tclosure

-- Faithful recursive carrier denotation (via @TyA.rec so it is total + recursive
-- on the tuple). `ttuple a b` -> `Prod (Den a) (Den b)`; the id-carrying
-- aggregates/closure/func and scalar pick reasonable opaque carriers (the point
-- is Den is total and recurses through the tuple). Each recursive ctor minor
-- (only ttuple here) binds BOTH sub-values AND their IHs.
def Den : TyA -> Type := fun t =>
  @TyA.rec (fun _ => Type)
    Nat                                   -- ti32
    (fun _id => Unit)                     -- tstruct
    (fun _el _len => Unit)                -- tarray
    (fun _a _b Da Db => Prod Da Db)       -- ttuple (recursive product)
    (fun _id => Unit)                     -- tenum
    (fun _id => Unit)                     -- tfunc
    (fun _el _r => Unit)                  -- tset
    (fun _el => Unit)                     -- tseq
    (fun _id => Unit)                     -- trecord
    (fun _id => Unit)                     -- tclosure
    t

-- ===========================================================================
-- FAITHFULNESS: is_aggregate (ty.rs:338). One rfl per variant in the slice.
-- ===========================================================================
theorem agg_isAggregate_tset_bitset (n : Nat) : isAggregate (TyA.tset n SetReprA.bitset) = true := rfl
theorem agg_isAggregate_tset_boxed (n : Nat) : isAggregate (TyA.tset n SetReprA.boxed) = true := rfl
theorem agg_isAggregate_tseq (n : Nat) : isAggregate (TyA.tseq n) = true := rfl
theorem agg_isAggregate_trecord (n : Nat) : isAggregate (TyA.trecord n) = true := rfl
theorem agg_isAggregate_ttuple (a b : TyA) : isAggregate (TyA.ttuple a b) = true := rfl
theorem agg_isAggregate_tarray (e n : Nat) : isAggregate (TyA.tarray e n) = true := rfl
theorem agg_isAggregate_tstruct (n : Nat) : isAggregate (TyA.tstruct n) = true := rfl
theorem agg_isAggregate_tenum (n : Nat) : isAggregate (TyA.tenum n) = true := rfl
-- Non-aggregates:
theorem agg_isAggregate_tclosure (n : Nat) : isAggregate (TyA.tclosure n) = false := rfl
theorem agg_isAggregate_tfunc (n : Nat) : isAggregate (TyA.tfunc n) = false := rfl
theorem agg_isAggregate_ti32 : isAggregate TyA.ti32 = false := rfl

-- ===========================================================================
-- FAITHFULNESS: is_closure (ty.rs:352). Only Closure is true.
-- ===========================================================================
theorem agg_isClosure_tclosure (n : Nat) : isClosure (TyA.tclosure n) = true := rfl
theorem agg_isClosure_tfunc (n : Nat) : isClosure (TyA.tfunc n) = false := rfl
theorem agg_isClosure_tset (n : Nat) : isClosure (TyA.tset n SetReprA.boxed) = false := rfl
theorem agg_isClosure_tseq (n : Nat) : isClosure (TyA.tseq n) = false := rfl
theorem agg_isClosure_trecord (n : Nat) : isClosure (TyA.trecord n) = false := rfl
theorem agg_isClosure_ttuple (a b : TyA) : isClosure (TyA.ttuple a b) = false := rfl
theorem agg_isClosure_tarray (e n : Nat) : isClosure (TyA.tarray e n) = false := rfl
theorem agg_isClosure_tstruct (n : Nat) : isClosure (TyA.tstruct n) = false := rfl
theorem agg_isClosure_tenum (n : Nat) : isClosure (TyA.tenum n) = false := rfl
theorem agg_isClosure_ti32 : isClosure TyA.ti32 = false := rfl

-- ===========================================================================
-- FAITHFULNESS: bit_width (ty.rs:142). All aggregates/closure/func -> none.
-- ===========================================================================
theorem agg_bitWidth_tstruct (n : Nat) : bitWidth (TyA.tstruct n) = Option.none := rfl
theorem agg_bitWidth_tarray (e n : Nat) : bitWidth (TyA.tarray e n) = Option.none := rfl
theorem agg_bitWidth_ttuple (a b : TyA) : bitWidth (TyA.ttuple a b) = Option.none := rfl
theorem agg_bitWidth_tenum (n : Nat) : bitWidth (TyA.tenum n) = Option.none := rfl
theorem agg_bitWidth_tfunc (n : Nat) : bitWidth (TyA.tfunc n) = Option.none := rfl
theorem agg_bitWidth_tset (n : Nat) : bitWidth (TyA.tset n SetReprA.bitset) = Option.none := rfl
theorem agg_bitWidth_tseq (n : Nat) : bitWidth (TyA.tseq n) = Option.none := rfl
theorem agg_bitWidth_trecord (n : Nat) : bitWidth (TyA.trecord n) = Option.none := rfl
theorem agg_bitWidth_tclosure (n : Nat) : bitWidth (TyA.tclosure n) = Option.none := rfl
-- Scalar anchor still has a width (sanity that the classifier discriminates).
theorem agg_bitWidth_ti32 : bitWidth TyA.ti32 = Option.some 32 := rfl

-- ===========================================================================
-- SetRepr DISCRIMINATOR: the repr hint is observable (Set(n,Bitset) vs
-- Set(n,Boxed) differ in `setRepr`), so it is genuinely part of type identity.
-- ===========================================================================
theorem agg_setRepr_bitset (n : Nat) : setRepr (TyA.tset n SetReprA.bitset) = SetReprA.bitset := rfl
theorem agg_setRepr_boxed (n : Nat) : setRepr (TyA.tset n SetReprA.boxed) = SetReprA.boxed := rfl

-- ===========================================================================
-- DENOTATION: total recursive carrier; the tuple denotes a genuine product.
-- ===========================================================================
theorem agg_Den_ttuple (a b : TyA) : Den (TyA.ttuple a b) = Prod (Den a) (Den b) := rfl
theorem agg_Den_ti32 : Den TyA.ti32 = Nat := rfl
theorem agg_Den_tstruct (n : Nat) : Den (TyA.tstruct n) = Unit := rfl
theorem agg_Den_tclosure (n : Nat) : Den (TyA.tclosure n) = Unit := rfl
theorem agg_Den_tset (n : Nat) : Den (TyA.tset n SetReprA.boxed) = Unit := rfl

end TyAggregate
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

/// Every theorem across the four full-`Ty` slices, in declaration order. Each
/// must pass the `axiom_deps(name).is_empty()` bedrock gate.
const TYFULL_THEOREMS: &[&str] = &[
    // --- TyFloatScalar: F16/F32/F64 + Never + bare Ptr (49) ---
    "flt_bitWidth_f16",
    "flt_bitWidth_f32",
    "flt_bitWidth_f64",
    "flt_bitWidth_never",
    "flt_bitWidth_ptr",
    "flt_bitWidth_tbool",
    "flt_bitWidth_ti32",
    "flt_isFloat_f16",
    "flt_isFloat_f32",
    "flt_isFloat_f64",
    "flt_isFloat_never",
    "flt_isFloat_ptr",
    "flt_isFloat_tbool",
    "flt_isFloat_ti32",
    "flt_isSigned_f16",
    "flt_isSigned_f32",
    "flt_isSigned_f64",
    "flt_isSigned_never",
    "flt_isSigned_ptr",
    "flt_isSigned_tbool",
    "flt_isSigned_ti32",
    "flt_isUnsigned_f16",
    "flt_isUnsigned_f32",
    "flt_isUnsigned_f64",
    "flt_isUnsigned_never",
    "flt_isUnsigned_ptr",
    "flt_isUnsigned_tbool",
    "flt_isUnsigned_ti32",
    "flt_isInteger_f16",
    "flt_isInteger_f32",
    "flt_isInteger_f64",
    "flt_isInteger_never",
    "flt_isInteger_ptr",
    "flt_isInteger_tbool",
    "flt_isInteger_ti32",
    "flt_isNumeric_f16",
    "flt_isNumeric_f32",
    "flt_isNumeric_f64",
    "flt_isNumeric_never",
    "flt_isNumeric_ptr",
    "flt_isNumeric_tbool",
    "flt_isNumeric_ti32",
    "flt_isReference_f16",
    "flt_isReference_f32",
    "flt_isReference_f64",
    "flt_isReference_never",
    "flt_isReference_ptr",
    "flt_isReference_tbool",
    "flt_isReference_ti32",
    // --- TyRefPtr: Ref/RefMut/PtrConst/PtrMut/Rc/FatPtr (38) ---
    "ref_isRef_tref",
    "ref_isRef_trefmut",
    "ref_isRef_tptrconst",
    "ref_isRef_tptrmut",
    "ref_isRef_trc",
    "ref_isRef_fatptr_slice",
    "ref_isRef_fatptr_str",
    "ref_isRef_fatptr_traitobj",
    "ref_isRef_ptr",
    "ref_isRef_ti32",
    "ref_isRef_tref_holds_any",
    "ref_isRef_nested",
    "ref_bw_tref",
    "ref_bw_trefmut",
    "ref_bw_tptrconst",
    "ref_bw_tptrmut",
    "ref_bw_trc",
    "ref_bw_fatptr",
    "ref_bw_ptr",
    "ref_bw_ti32",
    "ref_bww_tref",
    "ref_bww_trefmut",
    "ref_bww_tptrconst",
    "ref_bww_tptrmut",
    "ref_bww_trc",
    "ref_bww_ptr",
    "ref_bww_fatptr",
    "ref_bww_ti32",
    "ref_bww_fatptr_is_double",
    "ref_bww64_tref",
    "ref_bww64_trc",
    "ref_bww64_ptr",
    "ref_bww64_fatptr",
    "ref_bww64_ti32",
    "ref_bww32_tptrconst",
    "ref_bww32_fatptr",
    "ref_ptr_not_ref_but_pointer_sized",
    "ref_scalar_keeps_width",
    // --- TyVector: Vector(elem, lanes) (39) ---
    "vec_isVector_ti32",
    "vec_isVector_tu32",
    "vec_isVector_tf32",
    "vec_isVector_tbool",
    "vec_isVector_tvec",
    "vec_isInteger_tvec",
    "vec_isFloat_tvec",
    "vec_isNumeric_tvec",
    "vec_isInteger_ti32",
    "vec_isFloat_tf32",
    "vec_vectorShape_ti32",
    "vec_vectorShape_tbool",
    "vec_vectorShape_tvec",
    "vec_vectorShape_v4i32",
    "vec_bitWidth_ti32",
    "vec_bitWidth_tu32",
    "vec_bitWidth_tf32",
    "vec_bitWidth_tbool",
    "vec_bitWidth_v4i32",
    "vec_bitWidth_v8bool",
    "vec_bitWidth_v2i32",
    "vec_bitWidth_tvec_i32",
    "vec_isIntegerVector_succ",
    "vec_isIntegerVector_zero",
    "vec_isBoolVector_succ",
    "vec_isBoolVector_zero",
    "vec_isFloatVector_succ",
    "vec_isFloatVector_zero",
    "vec_isIntegerVector_tf32_succ",
    "vec_isBoolVector_ti32_succ",
    "vec_isIntegerVector_v4i32",
    "vec_compResult_tvec",
    "vec_selectCond_tvec",
    "vec_compResult_v4i32",
    "vec_selectCond_v4i32",
    "vec_compResult_ti32",
    "vec_selectCond_ti32",
    "vec_selectCond_tf32",
    "vec_comp_eq_select",
    // --- TyAggregate: Struct/Array/Tuple/Enum/Func/Set/Sequence/Record/Closure (38) ---
    "agg_isAggregate_tset_bitset",
    "agg_isAggregate_tset_boxed",
    "agg_isAggregate_tseq",
    "agg_isAggregate_trecord",
    "agg_isAggregate_ttuple",
    "agg_isAggregate_tarray",
    "agg_isAggregate_tstruct",
    "agg_isAggregate_tenum",
    "agg_isAggregate_tclosure",
    "agg_isAggregate_tfunc",
    "agg_isAggregate_ti32",
    "agg_isClosure_tclosure",
    "agg_isClosure_tfunc",
    "agg_isClosure_tset",
    "agg_isClosure_tseq",
    "agg_isClosure_trecord",
    "agg_isClosure_ttuple",
    "agg_isClosure_tarray",
    "agg_isClosure_tstruct",
    "agg_isClosure_tenum",
    "agg_isClosure_ti32",
    "agg_bitWidth_tstruct",
    "agg_bitWidth_tarray",
    "agg_bitWidth_ttuple",
    "agg_bitWidth_tenum",
    "agg_bitWidth_tfunc",
    "agg_bitWidth_tset",
    "agg_bitWidth_tseq",
    "agg_bitWidth_trecord",
    "agg_bitWidth_tclosure",
    "agg_bitWidth_ti32",
    "agg_setRepr_bitset",
    "agg_setRepr_boxed",
    "agg_Den_ttuple",
    "agg_Den_ti32",
    "agg_Den_tstruct",
    "agg_Den_tclosure",
    "agg_Den_tset",
];

#[test]
fn tyfull_all_trust_types_elaborate_and_kernel_check() {
    elaborate_module(TYFULL_SOURCE).expect(
        "the COMPLETE trust-ir Ty enum (floats/Never/Ptr, refs/rawptr/Rc/FatPtr, Vector, \
         aggregates/closure), faithful to ty.rs, must elaborate and kernel-check together",
    );
}

#[test]
fn tyfull_faithfulness_theorems_are_proven_down_to_the_foundational_axioms() {
    let env = elaborate_module(TYFULL_SOURCE)
        .expect("the full-Ty module must elaborate before auditing its theorems");
    for thm in TYFULL_THEOREMS {
        assert_proven_to_foundations(&env, thm);
    }
    println!(
        "ALL TRUST TYPES ARE CLEAN TYPES: {} faithfulness theorems over the COMPLETE trust-ir \
         Ty enum, every one proven to the 3 foundational axioms (bedrock).",
        TYFULL_THEOREMS.len()
    );
}
