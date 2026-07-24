// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TrustIr: a faithful Clean image of canonical trust-ir, its direct trust-cg
//! backend, and the retained MIR compatibility correspondence, proven down to
//! the three foundational axioms.
//!
//! ## Why this exists (vs. the generic `TrustCore`)
//!
//! Trust lowers both Rust/THIR and Clean directly to **trust-ir**, the canonical
//! universal proof-carrying IR (`first-party/trust-ir`), and **trust-cg** is its
//! direct code-generation backend. The MIR round trip in this test is retained
//! compatibility and differential evidence; it is not the frontend or target
//! architecture. `TrustCore` (sibling test) proved out the *technique* —
//! intrinsically-typed syntax, a total dependent evaluator, recursive
//! denotations — on a generic calculus. This module re-targets that technique
//! onto trust-ir's actual types/instructions/semantics and proves the direct
//! backend plus compatibility mappings semantics-preserving, so the Clean model
//! is a faithful image of what Trust really produces, not a parallel toy.
//!
//! ## What is proven (every theorem below has transitive axiom closure = {} ⊆
//! {propext, Quot.sound, Classical.choice}; the audit test enforces it)
//!
//! TYPES: `TyIr` (i8..i128 / u8..u128 / bool / unit / tuple) faithful to
//!   `Ty::bit_width`/`is_signed`/`is_unsigned`/`is_integer` (ty.rs:142-203) and
//!   `Den` (each type denotes its carrier); MIR<->trust-ir type ISOMORPHISM
//!   (`raise∘lower = id`, both ways) + denotation preservation.
//! INSTRUCTIONS (value-preserving lowerings, MIR<->trust-ir and trust-ir->
//!   trust-cg, both directions where applicable): arithmetic/bitwise BinOps
//!   (add/sub/mul/and/or/xor — wrapping/bitwise carrier semantics faithful to
//!   interpret.rs); width Casts (zext/trunc); left shift; UNSIGNED div/rem;
//!   overflow (wrapped result + Nat-valued carry-out); comparison at Prop level
//!   (irEq/irUlt); a TYPED layer threading `TyIr` + `tyWidth` (== `bitWidth`)
//!   through the binop.
//! BASIC BLOCKS: a register-file model + left-folded instruction lists;
//!   lowering a whole MIR basic block to trust-ir (and on to trust-cg) preserves
//!   the final register file, both directions.
//! CONTROL FLOW / WHOLE PROGRAMS: terminators + a fuel-bounded CFG interpreter
//!   `runProg`; lowering a whole MIR control-flow graph preserves the
//!   whole-program result on any fuel/entry/start env, both directions, and
//!   through the retained MIR -> trust-ir compatibility path and direct
//!   trust-ir -> trust-cg backend.
//!
//! ## Deferred (documented blockers, being addressed by reformulation)
//!
//! Signed div/rem, SExt/LShr/AShr, and the Bool-PACKAGED overflow flag /
//! comparison were initially deferred because they reached for `Nat.shiftRight`
//! (a non-foundational prelude AXIOM) or `decide` (which does not reduce here).
//! They are expressible WITHOUT those (logical shift = `Nat.div`, sign bit =
//! `a / 2^(w-1)`, Bool comparison = `Nat.blt`/`Nat.ble`/`Nat.beq` — axiom-free
//! deciders), and are being re-landed by that reformulation.
//!
//! See `designs/2026-06-19-mir-trustir-trustcg-correspondence.md` for the full
//! inventory and the reusable Clean-elaboration techniques.

use clean_kernel::env::Environment;
use clean_kernel::Name;

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_parser::parse_file;

/// A faithful Clean image of (a core slice of) trust-ir's `Ty`, plus the
/// `bit_width`/`is_signed`/`is_unsigned`/`is_integer` classifiers and the `Den`
/// denotation, all in Clean surface (Lean 4) syntax.
const TRUSTIR_SOURCE: &str = r#"
namespace TrustIr

-- Core slice of trust-ir's `Ty` (ty.rs): scalar integers + bool + unit + the
-- binary tuple. Constructor order is fixed (the recursor/casesOn minors below
-- follow it): i8,i16,i32,i64,i128, u8,u16,u32,u64,u128, tbool, tunit, ttuple.
inductive TyIr where
  | i8 : TyIr
  | i16 : TyIr
  | i32 : TyIr
  | i64 : TyIr
  | i128 : TyIr
  | u8 : TyIr
  | u16 : TyIr
  | u32 : TyIr
  | u64 : TyIr
  | u128 : TyIr
  | tbool : TyIr
  | tunit : TyIr
  | ttuple : TyIr -> TyIr -> TyIr

-- trust-ir `Ty::bit_width` (ty.rs:142), faithfully: Bool->some 1; iN/uN->some N;
-- unit and tuple (compound) -> none. `Option Nat` mirrors the Rust `Option<u32>`.
def bitWidth : TyIr -> Option Nat := fun t =>
  @TyIr.casesOn (fun _ => Option Nat) t
    (Option.some 8) (Option.some 16) (Option.some 32) (Option.some 64) (Option.some 128)
    (Option.some 8) (Option.some 16) (Option.some 32) (Option.some 64) (Option.some 128)
    (Option.some 1)
    Option.none
    (fun _a _b => Option.none)

-- trust-ir `Ty::is_signed` (ty.rs:196): exactly I8..I128.
def isSigned : TyIr -> Bool := fun t =>
  @TyIr.casesOn (fun _ => Bool) t
    true true true true true
    false false false false false
    false false (fun _a _b => false)

-- trust-ir `Ty::is_unsigned` (ty.rs:201): exactly U8..U128.
def isUnsigned : TyIr -> Bool := fun t =>
  @TyIr.casesOn (fun _ => Bool) t
    false false false false false
    true true true true true
    false false (fun _a _b => false)

-- trust-ir `Ty::is_integer` (ty.rs:191): signed OR unsigned.
def isInteger : TyIr -> Bool := fun t => Bool.or (isSigned t) (isUnsigned t)

-- Denotation of a TrustIr type as a Clean type. Each N-bit integer denotes the
-- `Nat` value carrier (its bit-width is recovered by `bitWidth`); `tbool`->Bool,
-- `tunit`->Unit, `ttuple a b`->`Prod (Den a)(Den b)` (so `Den` is RECURSIVE, via
-- @TyIr.rec, exactly like TrustCore's product denotation).
def Den : TyIr -> Type := fun t =>
  @TyIr.rec (fun _ => Type)
    Nat Nat Nat Nat Nat
    Nat Nat Nat Nat Nat
    Bool
    Unit
    (fun _a _b Da Db => Prod Da Db)
    t

-- ===========================================================================
-- FAITHFULNESS to trust-ir's `Ty::bit_width` (ty.rs:142): every scalar width
-- matches, and compound types have no width. All by `casesOn` iota (`rfl`).
-- ===========================================================================
theorem bitWidth_i8 : bitWidth TyIr.i8 = Option.some 8 := rfl
theorem bitWidth_i16 : bitWidth TyIr.i16 = Option.some 16 := rfl
theorem bitWidth_i32 : bitWidth TyIr.i32 = Option.some 32 := rfl
theorem bitWidth_i64 : bitWidth TyIr.i64 = Option.some 64 := rfl
theorem bitWidth_i128 : bitWidth TyIr.i128 = Option.some 128 := rfl
theorem bitWidth_u8 : bitWidth TyIr.u8 = Option.some 8 := rfl
theorem bitWidth_u32 : bitWidth TyIr.u32 = Option.some 32 := rfl
theorem bitWidth_u128 : bitWidth TyIr.u128 = Option.some 128 := rfl
theorem bitWidth_tbool : bitWidth TyIr.tbool = Option.some 1 := rfl
theorem bitWidth_tunit : bitWidth TyIr.tunit = Option.none := rfl
theorem bitWidth_ttuple (a b : TyIr) : bitWidth (TyIr.ttuple a b) = Option.none := rfl

-- FAITHFULNESS to `Ty::is_signed` / `Ty::is_unsigned` / `Ty::is_integer`.
theorem isSigned_i8 : isSigned TyIr.i8 = true := rfl
theorem isSigned_i128 : isSigned TyIr.i128 = true := rfl
theorem isSigned_u8 : isSigned TyIr.u8 = false := rfl
theorem isSigned_tbool : isSigned TyIr.tbool = false := rfl
theorem isUnsigned_u8 : isUnsigned TyIr.u8 = true := rfl
theorem isUnsigned_i8 : isUnsigned TyIr.i8 = false := rfl
theorem isInteger_i32 : isInteger TyIr.i32 = true := rfl
theorem isInteger_u64 : isInteger TyIr.u64 = true := rfl
theorem isInteger_tbool : isInteger TyIr.tbool = false := rfl
theorem isInteger_ttuple (a b : TyIr) : isInteger (TyIr.ttuple a b) = false := rfl

-- A signed integer is never classified unsigned (the two predicates partition
-- the integers) — proven from the definitions by `casesOn` reduction at each
-- integer constructor. (Stated per-constructor since a universally-quantified
-- form would need case analysis the prelude `decide` cannot supply.)
theorem signed_not_unsigned_i32 : isUnsigned TyIr.i32 = false := rfl
theorem unsigned_not_signed_u32 : isSigned TyIr.u32 = false := rfl

-- DENOTATION reductions: each type denotes its carrier (mirrors trust-ir's
-- value representation; `ttuple` is the recursive product denotation).
theorem Den_i8 : Den TyIr.i8 = Nat := rfl
theorem Den_u64 : Den TyIr.u64 = Nat := rfl
theorem Den_tbool : Den TyIr.tbool = Bool := rfl
theorem Den_tunit : Den TyIr.tunit = Unit := rfl
theorem Den_ttuple (a b : TyIr) : Den (TyIr.ttuple a b) = Prod (Den a) (Den b) := rfl

-- ===========================================================================
-- MIR <-> trust-ir TYPE CORRESPONDENCE (both directions).
--
-- `MirTy` is the MIR-side core type fragment (the scalar + tuple types that
-- `trust-mir-extract` maps to/from trust-ir `Ty`). `lower` is the MIR -> trust-ir
-- lowering, `raise` the reverse. We prove they form an ISOMORPHISM
-- (`raise (lower t) = t` and `lower (raise t) = t`) AND that lowering PRESERVES
-- the denotation (`Den (lower t) = MirDen t`) -- i.e. MIR and trust-ir are
-- semantically the same type system, in both directions, down to the 3 axioms.
-- ===========================================================================
inductive MirTy where
  | mi8 : MirTy
  | mi16 : MirTy
  | mi32 : MirTy
  | mi64 : MirTy
  | mi128 : MirTy
  | mu8 : MirTy
  | mu16 : MirTy
  | mu32 : MirTy
  | mu64 : MirTy
  | mu128 : MirTy
  | mbool : MirTy
  | munit : MirTy
  | mtuple : MirTy -> MirTy -> MirTy

-- lower : MIR -> trust-ir (the trust-mir-extract lowering direction).
def lower : MirTy -> TyIr := fun t =>
  @MirTy.rec (fun _ => TyIr)
    TyIr.i8 TyIr.i16 TyIr.i32 TyIr.i64 TyIr.i128
    TyIr.u8 TyIr.u16 TyIr.u32 TyIr.u64 TyIr.u128
    TyIr.tbool TyIr.tunit
    (fun _a _b la lb => TyIr.ttuple la lb)
    t

-- raise : trust-ir -> MIR (the reverse direction).
def raise : TyIr -> MirTy := fun t =>
  @TyIr.rec (fun _ => MirTy)
    MirTy.mi8 MirTy.mi16 MirTy.mi32 MirTy.mi64 MirTy.mi128
    MirTy.mu8 MirTy.mu16 MirTy.mu32 MirTy.mu64 MirTy.mu128
    MirTy.mbool MirTy.munit
    (fun _a _b ra rb => MirTy.mtuple ra rb)
    t

-- ROUND-TRIP 1: MIR -> trust-ir -> MIR is the identity (by induction; the tuple
-- case rebuilds via the IHs).
theorem raise_lower (t : MirTy) : raise (lower t) = t :=
  @MirTy.rec (fun k => raise (lower k) = k)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun a b iha ihb =>
      Eq.trans (congrArg (fun z => MirTy.mtuple z (raise (lower b))) iha)
        (congrArg (fun z => MirTy.mtuple a z) ihb))
    t

-- ROUND-TRIP 2: trust-ir -> MIR -> trust-ir is the identity.
theorem lower_raise (t : TyIr) : lower (raise t) = t :=
  @TyIr.rec (fun k => lower (raise k) = k)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun a b iha ihb =>
      Eq.trans (congrArg (fun z => TyIr.ttuple z (lower (raise b))) iha)
        (congrArg (fun z => TyIr.ttuple a z) ihb))
    t

-- The MIR-side denotation (same carriers as trust-ir's `Den`).
def MirDen : MirTy -> Type := fun t =>
  @MirTy.rec (fun _ => Type)
    Nat Nat Nat Nat Nat
    Nat Nat Nat Nat Nat
    Bool Unit
    (fun _a _b Da Db => Prod Da Db)
    t

-- SEMANTIC EQUIVALENCE at the type level: lowering a MIR type to trust-ir
-- PRESERVES its denotation -- `lower t` denotes exactly what `t` denotes. With
-- the two round-trips above, MIR and trust-ir are the same semantics type-by-type.
theorem lower_preserves_Den (t : MirTy) : Den (lower t) = MirDen t :=
  @MirTy.rec (fun k => Den (lower k) = MirDen k)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun a b iha ihb =>
      Eq.trans (congrArg (fun z => Prod z (Den (lower b))) iha)
        (congrArg (fun z => Prod (MirDen a) z) ihb))
    t

-- ===========================================================================
-- INSTRUCTION-level MIR <-> trust-ir correspondence (BinOp value semantics).
--
-- trust-ir's `interpret.rs` (lines 3130-3132) evaluates `BinOp::Add/Sub/Mul` as
-- the width-`w` WRAPPING arithmetic `wrapping_{add,sub,mul}` (i.e. `(a op b) %
-- 2^w`) over the raw carrier, and `And/Or/Xor` bitwise. MIR's `Rvalue::BinaryOp`
-- has the SAME Rust wrapping semantics. So lowering a MIR arithmetic op to a
-- trust-ir op preserves the COMPUTED VALUE at every width -- the value-level
-- half of the MIR <-> trust-ir correspondence (the type-level half is above).
-- ===========================================================================
inductive IrOp where
  | iadd : IrOp
  | isub : IrOp
  | imul : IrOp
  | iand : IrOp
  | ior : IrOp
  | ixor : IrOp

-- trust-ir BinOp value semantics at width `w`, faithful to interpret.rs:3130
-- (Add=wrapping_add=`(a+b)%2^w`, Sub=wrapping_sub, Mul=wrapping_mul, And/Or/Xor
-- bitwise). Matches the audited bvadd/bvsub/bvmul/bvand/bvor/bvxor shapes.
def irBinOp : IrOp -> Nat -> Nat -> Nat -> Nat := fun op w a b =>
  @IrOp.casesOn (fun _ => Nat) op
    ((a + b) % (2 ^ w))
    ((a + (2 ^ w - b % (2 ^ w))) % (2 ^ w))
    ((a * b) % (2 ^ w))
    (Nat.land a b)
    (Nat.lor a b)
    (Nat.xor a b)

inductive MirOp where
  | madd : MirOp
  | msub : MirOp
  | mmul : MirOp
  | mand : MirOp
  | mor : MirOp
  | mxor : MirOp

-- MIR BinaryOp value semantics at width `w` -- the SAME Rust wrapping/bitwise
-- semantics (this is exactly why the lowering is value-preserving).
def mirBinOp : MirOp -> Nat -> Nat -> Nat -> Nat := fun op w a b =>
  @MirOp.casesOn (fun _ => Nat) op
    ((a + b) % (2 ^ w))
    ((a + (2 ^ w - b % (2 ^ w))) % (2 ^ w))
    ((a * b) % (2 ^ w))
    (Nat.land a b)
    (Nat.lor a b)
    (Nat.xor a b)

-- op lowering MIR -> trust-ir, and the reverse.
def lowerOp : MirOp -> IrOp := fun op =>
  @MirOp.casesOn (fun _ => IrOp) op
    IrOp.iadd IrOp.isub IrOp.imul IrOp.iand IrOp.ior IrOp.ixor

def raiseOp : IrOp -> MirOp := fun op =>
  @IrOp.casesOn (fun _ => MirOp) op
    MirOp.madd MirOp.msub MirOp.mmul MirOp.mand MirOp.mor MirOp.mxor

-- Faithfulness of irBinOp to interpret.rs (each opcode computes the documented
-- wrapping/bitwise value).
theorem irBinOp_add (w a b : Nat) : irBinOp IrOp.iadd w a b = (a + b) % (2 ^ w) := rfl
theorem irBinOp_mul (w a b : Nat) : irBinOp IrOp.imul w a b = (a * b) % (2 ^ w) := rfl
theorem irBinOp_and (w a b : Nat) : irBinOp IrOp.iand w a b = Nat.land a b := rfl

-- The op lowering is an ISOMORPHISM (both round-trips identity), by casesOn.
theorem raiseOp_lowerOp (op : MirOp) : raiseOp (lowerOp op) = op :=
  @MirOp.casesOn (fun o => raiseOp (lowerOp o) = o) op rfl rfl rfl rfl rfl rfl

theorem lowerOp_raiseOp (op : IrOp) : lowerOp (raiseOp op) = op :=
  @IrOp.casesOn (fun o => lowerOp (raiseOp o) = o) op rfl rfl rfl rfl rfl rfl

-- THE INSTRUCTION-LEVEL CORRESPONDENCE: lowering a MIR BinOp to trust-ir
-- PRESERVES the computed value at every width and on all operands. Proven by
-- case analysis on the opcode (each case reduces to the same wrapping/bitwise
-- expression on both sides). No domain axioms.
theorem lowerOp_preserves_binop (op : MirOp) (w a b : Nat) :
    irBinOp (lowerOp op) w a b = mirBinOp op w a b :=
  @MirOp.casesOn (fun o => irBinOp (lowerOp o) w a b = mirBinOp o w a b) op
    rfl rfl rfl rfl rfl rfl

-- ...and the reverse direction: raising a trust-ir BinOp to MIR preserves the
-- value, completing the BOTH-DIRECTIONS Inst-level correspondence.
theorem raiseOp_preserves_binop (op : IrOp) (w a b : Nat) :
    mirBinOp (raiseOp op) w a b = irBinOp op w a b :=
  @IrOp.casesOn (fun o => mirBinOp (raiseOp o) w a b = irBinOp o w a b) op
    rfl rfl rfl rfl rfl rfl


-- ===========================================================================
-- INSTRUCTION-level MIR <-> trust-ir correspondence (Cast value semantics).
--
-- trust-ir's `interpret.rs` `eval_cast` (lines 1986-2007) evaluates the two
-- value-preserving width casts on the raw integer carrier via
-- `InterpretInt::from_raw(dst_bits, dst_signed, int.raw)`, where `from_raw`
-- (interpret.rs:223-229) sets `raw = int.raw & int_mask(dst_bits)` and
-- `int_mask(w) = 2^w - 1` (interpret.rs:3574-3580):
--
--   * ZEXT (CastOp::ZExt, the small->large case): the source value `int.raw`
--     is already < 2^src_bits <= 2^dst_bits, so masking by the LARGER mask
--     `2^dst_bits - 1` leaves it UNCHANGED. The carrier value is `int.raw` --
--     zero-extension is the IDENTITY on the Nat carrier. We model it as
--     `irZext a = a`.
--   * TRUNC (CastOp::Trunc, the large->small case): `raw = int.raw & (2^w' - 1)`
--     which AS A VALUE equals `int.raw % 2^w'`. We model truncation to width w'
--     as `irTrunc w' a = a % 2^w'` (the same shape as the wrapping BinOps).
--
-- MIR's `Rvalue::Cast(CastKind::IntToInt, ..)` has the SAME Rust truncate/
-- zero-extend value semantics, so lowering a MIR width-cast to trust-ir
-- PRESERVES the computed value -- the value-level Cast half of the MIR <->
-- trust-ir correspondence, mirroring `lowerOp_preserves_binop` for BinOps.
--
-- SExt (CastOp::SExt, interpret.rs:2008-2017) is OMITTED: it uses
-- `InterpretInt::from_i128(dst_bits, dst_signed, int.as_signed())`, and
-- `as_signed` (interpret.rs:235-248) extracts the sign bit and forms the
-- magnitude `((!raw & mask) + 1) & mask` -- a Nat bit-complement that has no
-- clean carrier formula reducible without `Nat.shiftRight` / `Nat.div` (both
-- of which break the empty-axiom gate). Sign-extension is deferred until a
-- complement-free carrier model exists.
-- ===========================================================================

-- The trust-ir width-cast opcodes we model (the two value-preserving casts).
inductive CastOpIr where
  | czext : CastOpIr
  | ctrunc : CastOpIr

-- The MIR-side counterparts (same two value-preserving width casts).
inductive CastOpMir where
  | mczext : CastOpMir
  | mctrunc : CastOpMir

-- trust-ir ZEXT on the carrier: zero-extension is the identity on the raw
-- value (interpret.rs:1997-2007 masks `int.raw` by the larger dst mask, a no-op).
def irZext : Nat -> Nat := fun a => a

-- MIR ZEXT on the carrier: the same identity (Rust `as` widening of an
-- unsigned value is value-preserving).
def mirZext : Nat -> Nat := fun a => a

-- trust-ir TRUNC to width w': `int.raw & (2^w' - 1) = int.raw % 2^w'`
-- (interpret.rs:1997-2007 via int_mask interpret.rs:3574-3580).
def irTrunc : Nat -> Nat -> Nat := fun w a => a % (2 ^ w)

-- MIR TRUNC to width w': the same wrapping truncation.
def mirTrunc : Nat -> Nat -> Nat := fun w a => a % (2 ^ w)

-- VALUE-PRESERVATION of each cast across MIR <-> trust-ir, directly (rfl):
-- both sides are the same carrier formula.
theorem zext_preserves (a : Nat) : irZext a = mirZext a := rfl
theorem trunc_preserves (w a : Nat) : irTrunc w a = mirTrunc w a := rfl

-- ZEXT is the identity on the carrier (the value-preservation fact the prompt
-- asks for; mod_lt-style in-range reasoning is intentionally not needed here).
theorem zext_identity (a : Nat) : irZext a = a := rfl

-- trust-ir cast value semantics at width `w` on operand `a`, dispatched on the
-- cast opcode (czext ignores width; ctrunc truncates to width `w`).
def irCast : CastOpIr -> Nat -> Nat -> Nat := fun op w a =>
  @CastOpIr.casesOn (fun _ => Nat) op
    (irZext a)
    (irTrunc w a)

-- MIR cast value semantics at width `w` -- the SAME truncate/zero-extend
-- semantics (this is exactly why the lowering is value-preserving).
def mirCast : CastOpMir -> Nat -> Nat -> Nat := fun op w a =>
  @CastOpMir.casesOn (fun _ => Nat) op
    (mirZext a)
    (mirTrunc w a)

-- cast-opcode lowering MIR -> trust-ir, and the reverse.
def lowerCast : CastOpMir -> CastOpIr := fun op =>
  @CastOpMir.casesOn (fun _ => CastOpIr) op
    CastOpIr.czext CastOpIr.ctrunc

def raiseCast : CastOpIr -> CastOpMir := fun op =>
  @CastOpIr.casesOn (fun _ => CastOpMir) op
    CastOpMir.mczext CastOpMir.mctrunc

-- Faithfulness of irCast to interpret.rs (each opcode computes the documented
-- value): zext = identity, trunc = `a % 2^w`.
theorem irCast_zext (w a : Nat) : irCast CastOpIr.czext w a = a := rfl
theorem irCast_trunc (w a : Nat) : irCast CastOpIr.ctrunc w a = a % (2 ^ w) := rfl

-- The cast-opcode lowering is an ISOMORPHISM (both round-trips identity), by casesOn.
theorem raiseCast_lowerCast (op : CastOpMir) : raiseCast (lowerCast op) = op :=
  @CastOpMir.casesOn (fun o => raiseCast (lowerCast o) = o) op rfl rfl

theorem lowerCast_raiseCast (op : CastOpIr) : lowerCast (raiseCast op) = op :=
  @CastOpIr.casesOn (fun o => lowerCast (raiseCast o) = o) op rfl rfl

-- THE INSTRUCTION-LEVEL CAST CORRESPONDENCE: lowering a MIR width-cast to
-- trust-ir PRESERVES the computed value at every width and operand. Proven by
-- case analysis on the opcode (czext -> both `a`; ctrunc -> both `a % 2^w`).
theorem lowerCast_preserves (op : CastOpMir) (w a : Nat) :
    irCast (lowerCast op) w a = mirCast op w a :=
  @CastOpMir.casesOn (fun o => irCast (lowerCast o) w a = mirCast o w a) op
    rfl rfl

-- ...and the reverse direction: raising a trust-ir width-cast to MIR preserves
-- the value, completing the BOTH-DIRECTIONS Inst-level cast correspondence.
theorem raiseCast_preserves (op : CastOpIr) (w a : Nat) :
    mirCast (raiseCast op) w a = irCast op w a :=
  @CastOpIr.casesOn (fun o => mirCast (raiseCast o) w a = irCast o w a) op
    rfl rfl

-- ===========================================================================
-- SHIFT instruction correspondence (MIR <-> trust-ir): LEFT SHIFT.
--
-- trust-ir `interpret.rs` evaluates `BinOp::Shl` (eval_int_binop, inst.rs:37) as
-- `lhs.raw << amount` (interpret.rs:3170-3172), and the WHOLE eval_int_binop
-- result is masked `& mask` where `mask = int_mask(bits) = (1<<w) - 1`
-- (interpret.rs:3192, int_mask @3573). Rust `<<` on the raw carrier is
-- multiply-by-`2^amount`, and masking to the low `w` bits is `% 2^w`. So the
-- stored value of a width-`w` left shift by `k` is exactly `(a * 2^k) % 2^w`
-- (the `bvshl` carrier the Trust verifier reasons over). MIR's
-- `Rvalue::BinaryOp(Shl)` has the SAME Rust shift+wrap semantics, so lowering a
-- MIR `Shl` to a trust-ir `Shl` preserves the computed value at every width --
-- the shift slice of the value-level MIR <-> trust-ir correspondence.
--
-- RIGHT shift (`LShr`/`AShr`, interpret.rs:3174-3181) is `lhs.raw >> amount` /
-- `(lhs.as_signed() >> amount)`, i.e. `a / 2^k` -- modelled in Clean only via
-- `Nat.shiftRight`, which is a PRELUDE AXIOM (and `Nat.div` is opaque, with no
-- `Nat.mod_lt`/`Nat.div` reductions available), so a right-shift model cannot
-- clear the empty-axiom-closure gate. It is DELIBERATELY omitted here. Only the
-- kernel's `Nat.shiftLeft` is an axiom-free Definition (shift-by-0 = identity,
-- shift-by-(succ n) = double), so left shift alone is provable to foundations.
-- ===========================================================================

-- Self-proven Nat multiplication helpers (the prelude registers NO mul lemmas).
-- `Nat.mul` recurses on its 2nd arg (`mul x 0 = 0`, `mul x (succ y) =
-- Nat.add (mul x y) x`) and `Nat.add` on its 2nd arg (`add x 0 = x`,
-- `add x (succ y) = succ (add x y)`); `Nat.add_assoc`/`Nat.add_comm` are
-- confirmed-constructive prelude lemmas. Each lemma is local to TrustIr.

-- `mul 0 n = 0`, by @Nat.rec on `n` (base rfl; step is the IH unchanged since
-- `mul 0 (succ k) = add (mul 0 k) 0 = mul 0 k`).
theorem nmul_zero_left_ir (n : Nat) : Nat.mul 0 n = 0 :=
  @Nat.rec (fun k => Nat.mul 0 k = 0) rfl (fun _ ih => ih) n

-- `(a + b) + c = (a + c) + b`, a pure add_assoc/add_comm/congrArg chain.
theorem nadd_right_comm_ir (a b c : Nat) :
    Nat.add (Nat.add a b) c = Nat.add (Nat.add a c) b :=
  Eq.trans (Nat.add_assoc a b c)
    (Eq.trans (congrArg (fun z => Nat.add a z) (Nat.add_comm b c))
      (Eq.symm (Nat.add_assoc a c b)))

-- `mul (succ a) n = (mul a n) + n`, by @Nat.rec on `n` (base rfl; step rewrites
-- the IH then reassociates via `nadd_right_comm_ir` under `Nat.succ`).
theorem nmul_succ_left_ir (a n : Nat) :
    Nat.mul (Nat.succ a) n = Nat.add (Nat.mul a n) n :=
  @Nat.rec
    (fun k => Nat.mul (Nat.succ a) k = Nat.add (Nat.mul a k) k)
    rfl
    (fun k ih =>
      Eq.trans
        (congrArg (fun z => Nat.add z (Nat.succ a)) ih)
        (congrArg (fun z => Nat.succ z) (nadd_right_comm_ir (Nat.mul a k) k a)))
    n

-- Commutativity of `Nat.mul`, by @Nat.rec on `b` (base `Eq.symm nmul_zero_left_ir`;
-- step rewrites the IH then closes with `Eq.symm (nmul_succ_left_ir k a)`).
theorem nmul_comm_ir (a b : Nat) : Nat.mul a b = Nat.mul b a :=
  @Nat.rec
    (fun k => Nat.mul a k = Nat.mul k a)
    (Eq.symm (nmul_zero_left_ir a))
    (fun k ih =>
      Eq.trans
        (congrArg (fun z => Nat.add z a) ih)
        (Eq.symm (nmul_succ_left_ir k a)))
    b

-- `1 * n = n`, by @Nat.rec on `n` (literal `1` = `Nat.succ Nat.zero`, so
-- `mul 1 (succ k) = succ (mul 1 k)` definitionally; step is `congrArg Nat.succ ih`).
theorem nmul_one_left_ir (n : Nat) : Nat.mul 1 n = n :=
  @Nat.rec
    (fun k => Nat.mul 1 k = k)
    rfl
    (fun k ih => congrArg (fun z => Nat.succ z) ih)
    n

-- `n * 1 = n`, by commutativity then left-identity (the induction lives in those).
theorem nmul_one_right_ir (n : Nat) : Nat.mul n 1 = n :=
  Eq.trans (nmul_comm_ir n 1) (nmul_one_left_ir n)

-- trust-ir left-shift value semantics at width `w`: shift `a` left by `k`,
-- reduced to width `w`. Faithful to interpret.rs:3170-3172 (`lhs.raw << amount`
-- = multiply by `2^k`) composed with interpret.rs:3192 (`& mask`, mask =
-- `(1<<w)-1`, int_mask @3573) = `% 2^w`. This is the audited `bvshl` carrier.
def irShl : Nat -> Nat -> Nat -> Nat := fun w a k => (a * (2 ^ k)) % (2 ^ w)

-- MIR left-shift value semantics at width `w` -- the SAME Rust shift+wrap
-- semantics as `Rvalue::BinaryOp(Shl)` (this is why the lowering preserves value).
def mirShl : Nat -> Nat -> Nat -> Nat := fun w a k => (a * (2 ^ k)) % (2 ^ w)

-- THE SHIFT-INSTRUCTION CORRESPONDENCE: lowering a MIR `Shl` to trust-ir `Shl`
-- preserves the computed value at every width and on all operands. There is a
-- single shift opcode, so no opcode case split is needed -- both sides reduce to
-- the identical `(a * 2^k) % 2^w`, closed by `rfl`. No domain axioms.
theorem lowerShl_preserves (w a k : Nat) : irShl w a k = mirShl w a k := rfl

-- ...and the reverse direction (trust-ir `Shl` -> MIR `Shl`), completing the
-- BOTH-DIRECTIONS shift correspondence. Also `rfl`.
theorem raiseShl_preserves (w a k : Nat) : mirShl w a k = irShl w a k := rfl

-- FAITHFULNESS: `irShl` computes the documented `(a * 2^k) % 2^w` shape (the
-- masked left-shift of interpret.rs:3170-3172 + 3192).
theorem irShl_def (w a k : Nat) : irShl w a k = (a * (2 ^ k)) % (2 ^ w) := rfl

-- Shift-by-zero coherence (trust-ir side): a left shift by `0` is just the width
-- mask. `irShl w a 0` unfolds to `(a * 2^0) % 2^w`; `2^0` iota-reduces to `1`, so
-- the multiplicand is `Nat.mul a 1`, rewritten to `a` by `nmul_one_right_ir`
-- under the `(. % 2^w)` congruence. Faithful to `(a << 0) & mask = a & mask`.
theorem shl_zero (w a : Nat) : irShl w a 0 = a % (2 ^ w) :=
  congrArg (fun z => z % (2 ^ w)) (nmul_one_right_ir a)

-- Shift-by-zero coherence (MIR side): identical, so both models agree at `k = 0`.
theorem mirShl_zero (w a : Nat) : mirShl w a 0 = a % (2 ^ w) :=
  congrArg (fun z => z % (2 ^ w)) (nmul_one_right_ir a)

-- The kernel's REAL `Nat.shiftLeft` is an axiom-FREE Definition: shift-by-0 is
-- the identity (Nat.rec base = `m`), holding by iota/delta.
theorem shl_kernel_zero (a : Nat) : Nat.shiftLeft a 0 = a := rfl

-- ...and shift-by-(succ n) doubles shift-by-n (Nat.rec succ minor = `Nat.mul ih 2`),
-- i.e. `Nat.shiftLeft a n = a * 2^n`. Pure iota/delta, no axioms.
theorem shl_kernel_succ (a n : Nat) :
    Nat.shiftLeft a (Nat.succ n) = Nat.mul (Nat.shiftLeft a n) 2 := rfl

-- COHERENCE with the kernel primitive: `irShl w a 0` agrees with the masked
-- output of the kernel's own `Nat.shiftLeft a 0`. LHS reduces to `(Nat.mul a 1)
-- % 2^w` (pow iota), RHS to `a % 2^w` (`Nat.shiftLeft a 0` iota), and the same
-- `nmul_one_right_ir` congruence closes the gap -- the operation model and the
-- kernel shift primitive are the same computation at shift amount `0`.
theorem irShl_shiftLeft_zero (w a : Nat) :
    irShl w a 0 = (Nat.shiftLeft a 0) % (2 ^ w) :=
  congrArg (fun z => z % (2 ^ w)) (nmul_one_right_ir a)

-- ===========================================================================
-- OVERFLOW-instruction MIR <-> trust-ir correspondence (the WRAPPED-RESULT half).
--
-- trust-ir's `Inst::Overflow { op: OverflowOp, .. }` (inst.rs:434-439, op enum
-- OverflowOp::{AddOverflow,SubOverflow,MulOverflow}, inst.rs:67-71) computes a
-- PAIR `(wrapped_result, overflow_flag)`. `interpret.rs`'s `eval_int_overflow`
-- (interpret.rs:3254-3283) produces the wrapped result by DELEGATING to
-- `eval_int_binop` under the opcode mapping (interpret.rs:3266-3275):
--     AddOverflow -> BinOp::Add ,  SubOverflow -> BinOp::Sub ,  MulOverflow -> BinOp::Mul
-- i.e. the overflowing op's RESULT is EXACTLY the plain wrapping `BinOp` result
-- (interpret.rs:3130-3132: Add=wrapping_add, Sub=wrapping_sub, Mul=wrapping_mul,
-- each masked to width `w` at interpret.rs:3190 -> `(a op b) % 2^w`). So this
-- module pins, down to the 3 axioms, the SAFE (result) half of the Overflow
-- correspondence: lowering a MIR overflowing op to trust-ir preserves the
-- wrapped value at every width, and that value coincides with the already-proven
-- plain-BinOp value.
--
-- The overflow FLAG is DELIBERATELY OMITTED here: per interpret.rs:3506-3531
-- (`unsigned_overflow` tests `sum > mask` / `lhs.raw < rhs.raw`; `signed_overflow`
-- tests signed `checked_*` bounds) its characterization needs `Nat.mod_lt` /
-- modular-comparison facts and a Bool-valued `decide`, BOTH of which are blocked
-- under the empty-axiom gate. It is left for a later cut that re-derives the
-- needed mod lemmas constructively.
-- ===========================================================================

-- trust-ir OverflowOp opcodes (inst.rs:67-71), order fixed for the casesOn minors.
inductive IrOvOp where
  | ovadd : IrOvOp
  | ovsub : IrOvOp
  | ovmul : IrOvOp

-- The WRAPPED result of a trust-ir overflowing op at width `w`, faithful to
-- eval_int_overflow's delegation (interpret.rs:3266-3275) into eval_int_binop
-- (interpret.rs:3130-3132 + mask at 3190): Add/Sub/Mul wrapping arithmetic.
-- The Sub shape matches the audited `irBinOp IrOp.isub` modular form.
def irOvResult : IrOvOp -> Nat -> Nat -> Nat -> Nat := fun op w a b =>
  @IrOvOp.casesOn (fun _ => Nat) op
    ((a + b) % (2 ^ w))
    ((a + (2 ^ w - b % (2 ^ w))) % (2 ^ w))
    ((a * b) % (2 ^ w))

-- MIR-side overflowing op (Rust's checked_{add,sub,mul} result lane is the same
-- wrapping value as the plain op -- exactly why the lowering is value-preserving).
inductive MirOvOp where
  | movadd : MirOvOp
  | movsub : MirOvOp
  | movmul : MirOvOp

-- MIR overflowing-op wrapped result at width `w` -- same Rust wrapping semantics.
def mirOvResult : MirOvOp -> Nat -> Nat -> Nat -> Nat := fun op w a b =>
  @MirOvOp.casesOn (fun _ => Nat) op
    ((a + b) % (2 ^ w))
    ((a + (2 ^ w - b % (2 ^ w))) % (2 ^ w))
    ((a * b) % (2 ^ w))

-- Overflow-opcode lowering MIR -> trust-ir, and the reverse.
def lowerOvOp : MirOvOp -> IrOvOp := fun op =>
  @MirOvOp.casesOn (fun _ => IrOvOp) op
    IrOvOp.ovadd IrOvOp.ovsub IrOvOp.ovmul

def raiseOvOp : IrOvOp -> MirOvOp := fun op =>
  @IrOvOp.casesOn (fun _ => MirOvOp) op
    MirOvOp.movadd MirOvOp.movsub MirOvOp.movmul

-- FAITHFULNESS of irOvResult to interpret.rs:3266-3275 (each overflow opcode's
-- result is the documented wrapping value at width `w`). By casesOn iota (rfl).
theorem irOvResult_add (w a b : Nat) : irOvResult IrOvOp.ovadd w a b = (a + b) % (2 ^ w) := rfl
theorem irOvResult_sub (w a b : Nat) :
    irOvResult IrOvOp.ovsub w a b = (a + (2 ^ w - b % (2 ^ w))) % (2 ^ w) := rfl
theorem irOvResult_mul (w a b : Nat) : irOvResult IrOvOp.ovmul w a b = (a * b) % (2 ^ w) := rfl

-- BRIDGE: the wrapped result of a trust-ir overflowing op EQUALS the plain
-- trust-ir BinOp result (the already-proven `irBinOp` value). This is the
-- formal content of interpret.rs:3266-3275 mapping OverflowOp -> BinOp.
theorem irOvResult_eq_binop_add (w a b : Nat) :
    irOvResult IrOvOp.ovadd w a b = irBinOp IrOp.iadd w a b := rfl
theorem irOvResult_eq_binop_sub (w a b : Nat) :
    irOvResult IrOvOp.ovsub w a b = irBinOp IrOp.isub w a b := rfl
theorem irOvResult_eq_binop_mul (w a b : Nat) :
    irOvResult IrOvOp.ovmul w a b = irBinOp IrOp.imul w a b := rfl

-- The overflow-opcode lowering is an ISOMORPHISM (both round-trips identity).
theorem raiseOvOp_lowerOvOp (op : MirOvOp) : raiseOvOp (lowerOvOp op) = op :=
  @MirOvOp.casesOn (fun o => raiseOvOp (lowerOvOp o) = o) op rfl rfl rfl

theorem lowerOvOp_raiseOvOp (op : IrOvOp) : lowerOvOp (raiseOvOp op) = op :=
  @IrOvOp.casesOn (fun o => lowerOvOp (raiseOvOp o) = o) op rfl rfl rfl

-- THE OVERFLOW INSTRUCTION-LEVEL CORRESPONDENCE (result half): lowering a MIR
-- overflowing op to trust-ir PRESERVES the wrapped result at every width and on
-- all operands. By case analysis on the opcode (each reduces to the same
-- wrapping expression on both sides). No domain axioms.
theorem lowerOvOp_preserves_result (op : MirOvOp) (w a b : Nat) :
    irOvResult (lowerOvOp op) w a b = mirOvResult op w a b :=
  @MirOvOp.casesOn (fun o => irOvResult (lowerOvOp o) w a b = mirOvResult o w a b) op
    rfl rfl rfl

-- ...and the reverse direction, completing the both-directions correspondence.
theorem raiseOvOp_preserves_result (op : IrOvOp) (w a b : Nat) :
    mirOvResult (raiseOvOp op) w a b = irOvResult op w a b :=
  @IrOvOp.casesOn (fun o => mirOvResult (raiseOvOp o) w a b = irOvResult o w a b) op
    rfl rfl rfl

-- ===========================================================================
-- INSTRUCTION-level MIR <-> trust-ir correspondence (ICmp value semantics).
--
-- trust-ir's `interpret.rs` lowers `Inst::ICmp` (interpret.rs:519) through
-- `eval_icmp` (interpret.rs:1892) to `eval_int_icmp` (interpret.rs:3285-3298),
-- which compares the fixed-width payload's `raw` field. Crucially `raw` is
-- "always masked to `bits`" (interpret.rs:205-206), i.e. `raw = value % 2^w`
-- is the in-range carrier representative. The two scalar cases we model:
--
--   ICmpOp::Eq  => lhs.raw == rhs.raw   (interpret.rs:3287)
--   ICmpOp::Ult => lhs.raw <  rhs.raw   (interpret.rs:3289)
--
-- `eval_int_icmp` RETURNS A BOOL via Rust `==` / `<`. Clean's `decide` does NOT
-- reduce, so a Bool-valued comparison equality is not kernel-provable. We model
-- the comparisons at the PROPOSITION level instead (mirroring TrustCore's
-- `Bvult : ... -> Prop`): a Prop IS provable, and it captures exactly the
-- mathematical content of the masked-`raw` comparison. `irEq` compares the raw
-- carriers directly (`raw == raw`); `irUlt` compares the width-`w` masked
-- carriers (`(a % 2^w) < (b % 2^w)`), matching `raw`'s masking discipline.
-- ===========================================================================

-- trust-ir ICmp Eq as a Prop: equality of the raw carriers (interpret.rs:3287,
-- `lhs.raw == rhs.raw`; `raw` is the masked in-range value, interpret.rs:205).
def irEq : Nat -> Nat -> Prop := fun a b => a = b

-- trust-ir ICmp Ult as a Prop: width-`w` unsigned less-than on the masked
-- carriers (interpret.rs:3289, `lhs.raw < rhs.raw`; the `% 2^w` mirrors `raw`'s
-- "always masked to `bits`" invariant, interpret.rs:205-206). Mirrors the
-- TrustCore sibling's `Bvult` shape.
def irUlt : Nat -> Nat -> Nat -> Prop := fun w a b => Nat.lt (a % (2 ^ w)) (b % (2 ^ w))

-- MIR-side ICmp Eq / Ult as Props -- the SAME Rust `==` / unsigned `<` carrier
-- semantics (this identity is exactly why the lowering preserves the Prop).
def mirEq : Nat -> Nat -> Prop := fun a b => a = b

def mirUlt : Nat -> Nat -> Nat -> Prop := fun w a b => Nat.lt (a % (2 ^ w)) (b % (2 ^ w))

-- Faithfulness of the modeled Props to interpret.rs:3287/3289 (each unfolds to
-- the documented carrier comparison). By `def` iota (`rfl`).
theorem irEq_def (a b : Nat) : irEq a b = (a = b) := rfl
theorem irUlt_def (w a b : Nat) : irUlt w a b = Nat.lt (a % (2 ^ w)) (b % (2 ^ w)) := rfl

-- ===========================================================================
-- THE ICmp CORRESPONDENCE (Prop level, BOTH directions): lowering a MIR ICmp to
-- trust-ir -- and raising back -- preserves the PROPOSITION. The two sides are
-- the LITERALLY SAME Prop (same masked-carrier comparison), so each is `rfl`.
-- This is the comparison analogue of `lowerOp_preserves_binop`.
-- ===========================================================================
theorem lowerEq_preserves (a b : Nat) : irEq a b = mirEq a b := rfl
theorem lowerUlt_preserves (w a b : Nat) : irUlt w a b = mirUlt w a b := rfl
theorem raiseEq_preserves (a b : Nat) : mirEq a b = irEq a b := rfl
theorem raiseUlt_preserves (w a b : Nat) : mirUlt w a b = irUlt w a b := rfl

-- ORDER FACTS about `irEq` (it is the carrier equality, so it inherits the
-- equality structure -- foundational `Eq` built-ins only).
theorem irEq_refl (a : Nat) : irEq a a := rfl
theorem irEq_symm (a b : Nat) : irEq a b -> irEq b a := fun h => Eq.symm h

-- ORDER FACTS about `irUlt`, reusing the constructive (axiom-free) prelude
-- theorems `Nat.lt_irrefl : forall a, Nat.lt a a -> False` and
-- `Nat.lt_asymm : forall a b, Nat.lt a b -> Nat.lt b a -> False`. After
-- unfolding `irUlt`, the goals are `Nat.lt (a%2^w)(a%2^w) -> False` and the
-- asymmetry pair, discharged by direct application at the masked carriers.
theorem irUlt_irrefl (w a : Nat) : irUlt w a a -> False :=
  Nat.lt_irrefl (a % (2 ^ w))

theorem irUlt_asymm (w a b : Nat) : irUlt w a b -> irUlt w b a -> False :=
  fun h1 h2 => Nat.lt_asymm (a % (2 ^ w)) (b % (2 ^ w)) h1 h2

-- ===========================================================================
-- THE ICmp OPCODE CLASS: opcode-enum + isomorphism + preservation, mirroring
-- the BinOp class (`IrOp`/`MirOp`, `lowerOp_preserves_binop`). The bare
-- `irEq`/`irUlt` Props above only covered Eq/Ult; the rest of trust-ir's
-- UNSIGNED `ICmpOp` family (interpret.rs:3285-3298 `eval_int_icmp`) is:
--
--   ICmpOp::Eq  => lhs.raw == rhs.raw          (ceq)
--   ICmpOp::Ne  => lhs.raw != rhs.raw          (cne)
--   ICmpOp::Ult => lhs.raw <  rhs.raw          (cult)
--   ICmpOp::Ule => lhs.raw <= rhs.raw          (cule)
--   ICmpOp::Uge => lhs.raw >= rhs.raw          (cuge, i.e. rhs.raw <= lhs.raw)
--   ICmpOp::Ugt => lhs.raw >  rhs.raw          (cugt, i.e. rhs.raw <  lhs.raw)
--
-- `raw` is "always masked to `bits`" (interpret.rs:205-206), so each opcode is
-- modeled at width `w` on the masked carriers `a % 2^w` / `b % 2^w` -- the same
-- masked-carrier discipline as `irUlt`. As with `eval_int_icmp`'s Bool result,
-- `decide` does NOT reduce, so the comparisons are modeled at the PROPOSITION
-- level (a Prop IS provable). MIR's `Rvalue::BinaryOp(BinOp::Eq/Ne/Lt/Le/..)`
-- has the SAME unsigned-carrier `==`/`!=`/`<`/`<=` semantics, so the two
-- dispatchers are BYTE-IDENTICAL and the preservation is `rfl` per opcode.
-- ===========================================================================
inductive IrCmpOp where
  | ceq : IrCmpOp
  | cne : IrCmpOp
  | cult : IrCmpOp
  | cule : IrCmpOp
  | cuge : IrCmpOp
  | cugt : IrCmpOp

inductive MirCmpOp where
  | mceq : MirCmpOp
  | mcne : MirCmpOp
  | mcult : MirCmpOp
  | mcule : MirCmpOp
  | mcuge : MirCmpOp
  | mcugt : MirCmpOp

-- trust-ir ICmp value semantics (Prop) at width `w`, on the masked carriers --
-- faithful to eval_int_icmp (interpret.rs:3285-3298). cuge/cugt are the swapped
-- forms of cule/cult (lhs >= rhs <=> rhs <= lhs), matching the Rust comparison.
def irCmp : IrCmpOp -> Nat -> Nat -> Nat -> Prop := fun op w a b =>
  @IrCmpOp.casesOn (fun _ => Prop) op
    (a % (2 ^ w) = b % (2 ^ w))
    (Not (a % (2 ^ w) = b % (2 ^ w)))
    (Nat.lt (a % (2 ^ w)) (b % (2 ^ w)))
    (Nat.le (a % (2 ^ w)) (b % (2 ^ w)))
    (Nat.le (b % (2 ^ w)) (a % (2 ^ w)))
    (Nat.lt (b % (2 ^ w)) (a % (2 ^ w)))

-- MIR-side ICmp value semantics (Prop) -- the SAME unsigned-carrier comparison
-- semantics (this byte-identical RHS is exactly why the lowering preserves the
-- Prop). BYTE-IDENTICAL to `irCmp`'s case bodies.
def mirCmp : MirCmpOp -> Nat -> Nat -> Nat -> Prop := fun op w a b =>
  @MirCmpOp.casesOn (fun _ => Prop) op
    (a % (2 ^ w) = b % (2 ^ w))
    (Not (a % (2 ^ w) = b % (2 ^ w)))
    (Nat.lt (a % (2 ^ w)) (b % (2 ^ w)))
    (Nat.le (a % (2 ^ w)) (b % (2 ^ w)))
    (Nat.le (b % (2 ^ w)) (a % (2 ^ w)))
    (Nat.lt (b % (2 ^ w)) (a % (2 ^ w)))

-- ICmp opcode lowering MIR -> trust-ir, and the reverse.
def lowerCmpOp : MirCmpOp -> IrCmpOp := fun op =>
  @MirCmpOp.casesOn (fun _ => IrCmpOp) op
    IrCmpOp.ceq IrCmpOp.cne IrCmpOp.cult IrCmpOp.cule IrCmpOp.cuge IrCmpOp.cugt

def raiseCmpOp : IrCmpOp -> MirCmpOp := fun op =>
  @IrCmpOp.casesOn (fun _ => MirCmpOp) op
    MirCmpOp.mceq MirCmpOp.mcne MirCmpOp.mcult MirCmpOp.mcule MirCmpOp.mcuge MirCmpOp.mcugt

-- The ICmp opcode lowering is an ISOMORPHISM (both round-trips identity), by
-- case analysis on the opcode. No domain axioms.
theorem raiseCmpOp_lowerCmpOp (op : MirCmpOp) : raiseCmpOp (lowerCmpOp op) = op :=
  @MirCmpOp.casesOn (fun o => raiseCmpOp (lowerCmpOp o) = o) op rfl rfl rfl rfl rfl rfl

theorem lowerCmpOp_raiseCmpOp (op : IrCmpOp) : lowerCmpOp (raiseCmpOp op) = op :=
  @IrCmpOp.casesOn (fun o => lowerCmpOp (raiseCmpOp o) = o) op rfl rfl rfl rfl rfl rfl

-- THE ICmp INSTRUCTION-LEVEL CORRESPONDENCE: lowering a MIR ICmp opcode to
-- trust-ir PRESERVES the comparison PROPOSITION at every width and on all
-- operands. By case analysis on the opcode -- each case reduces to the same
-- masked-carrier comparison Prop on both sides (the dispatchers are
-- byte-identical), so every case is `rfl`. The comparison analogue of
-- `lowerOp_preserves_binop`. No domain axioms.
theorem lowerCmpOp_preserves (op : MirCmpOp) (w a b : Nat) :
    irCmp (lowerCmpOp op) w a b = mirCmp op w a b :=
  @MirCmpOp.casesOn (fun o => irCmp (lowerCmpOp o) w a b = mirCmp o w a b) op
    rfl rfl rfl rfl rfl rfl

-- ...and the reverse direction: raising a trust-ir ICmp opcode to MIR preserves
-- the comparison Prop, completing the BOTH-DIRECTIONS opcode correspondence.
theorem raiseCmpOp_preserves (op : IrCmpOp) (w a b : Nat) :
    mirCmp (raiseCmpOp op) w a b = irCmp op w a b :=
  @IrCmpOp.casesOn (fun o => mirCmp (raiseCmpOp o) w a b = irCmp o w a b) op
    rfl rfl rfl rfl rfl rfl

-- ===========================================================================
-- trust-ir <-> trust-cg (the verified-codegen backend) BinOp correspondence.
--
-- trust-cg's LIR `Opcode` (trust-cg-lower/src/instructions.rs:49-187) has
-- Iadd/Isub/Imul/Band/Bor/Bxor; its interpreter (trust-cg-codegen/src/
-- interpreter.rs:671-801) evaluates them with the SAME width-w WRAPPING /
-- bitwise semantics as trust-ir (Iadd=wrapping_add=(a+b)%2^w, Isub=wrapping_sub,
-- Imul=wrapping_mul, Band/Bor/Bxor bitwise); and trust-cg-verify
-- (trust_ir_semantics.rs:55-82) proves the lowering correct by encoding
-- Iadd->bvadd etc. So lowering a trust-ir BinOp to a trust-cg LIR op PRESERVES
-- the computed value -- the trust-cg half of the verified-codegen picture.
-- ===========================================================================
inductive CgOp where
  | cadd : CgOp
  | csub : CgOp
  | cmul : CgOp
  | cand : CgOp
  | cor : CgOp
  | cxor : CgOp

-- trust-cg LIR value semantics at width `w`, faithful to interpreter.rs:671-801.
def cgBinOp : CgOp -> Nat -> Nat -> Nat -> Nat := fun op w a b =>
  @CgOp.casesOn (fun _ => Nat) op
    ((a + b) % (2 ^ w))
    ((a + (2 ^ w - b % (2 ^ w))) % (2 ^ w))
    ((a * b) % (2 ^ w))
    (Nat.land a b)
    (Nat.lor a b)
    (Nat.xor a b)

-- trust-ir -> trust-cg op lowering (BinOp::Add -> Opcode::Iadd, ...), and reverse.
def lowerIrToCg : IrOp -> CgOp := fun op =>
  @IrOp.casesOn (fun _ => CgOp) op
    CgOp.cadd CgOp.csub CgOp.cmul CgOp.cand CgOp.cor CgOp.cxor

def raiseCgToIr : CgOp -> IrOp := fun op =>
  @CgOp.casesOn (fun _ => IrOp) op
    IrOp.iadd IrOp.isub IrOp.imul IrOp.iand IrOp.ior IrOp.ixor

theorem cgBinOp_add (w a b : Nat) : cgBinOp CgOp.cadd w a b = (a + b) % (2 ^ w) := rfl

-- The trust-ir <-> trust-cg op lowering is an ISOMORPHISM.
theorem raiseCgToIr_lowerIrToCg (op : IrOp) : raiseCgToIr (lowerIrToCg op) = op :=
  @IrOp.casesOn (fun o => raiseCgToIr (lowerIrToCg o) = o) op rfl rfl rfl rfl rfl rfl

theorem lowerIrToCg_raiseCgToIr (op : CgOp) : lowerIrToCg (raiseCgToIr op) = op :=
  @CgOp.casesOn (fun o => lowerIrToCg (raiseCgToIr o) = o) op rfl rfl rfl rfl rfl rfl

-- trust-ir -> trust-cg lowering PRESERVES the computed value (both directions).
theorem lowerIrToCg_preserves (op : IrOp) (w a b : Nat) :
    cgBinOp (lowerIrToCg op) w a b = irBinOp op w a b :=
  @IrOp.casesOn (fun o => cgBinOp (lowerIrToCg o) w a b = irBinOp o w a b) op
    rfl rfl rfl rfl rfl rfl

theorem raiseCgToIr_preserves (op : CgOp) (w a b : Nat) :
    irBinOp (raiseCgToIr op) w a b = cgBinOp op w a b :=
  @CgOp.casesOn (fun o => irBinOp (raiseCgToIr o) w a b = cgBinOp o w a b) op
    rfl rfl rfl rfl rfl rfl

-- THE FULL PIPELINE: lowering a MIR BinOp all the way through trust-ir to
-- trust-cg PRESERVES the computed value -- composing lowerOp (MIR->trust-ir)
-- with lowerIrToCg (trust-ir->trust-cg). This closes MIR -> trust-ir -> trust-cg
-- at the value level for the arithmetic/bitwise instructions.
theorem lowerMirToCg_preserves (op : MirOp) (w a b : Nat) :
    cgBinOp (lowerIrToCg (lowerOp op)) w a b = mirBinOp op w a b :=
  @MirOp.casesOn (fun o => cgBinOp (lowerIrToCg (lowerOp o)) w a b = mirBinOp o w a b) op
    rfl rfl rfl rfl rfl rfl


-- ===========================================================================
-- PROGRAM-LEVEL correspondence (straight-line basic blocks).
--
-- trust-ir's `interpret.rs` evaluates a basic block as a sequence of SSA
-- instructions threaded through a register environment (a map from value-id to
-- the computed integer); MIR's interpreter and trust-cg's `interpreter.rs` do
-- the same over their own instruction lists. We model the register file as a
-- total function `Env := Nat -> Nat` (value-id -> carrier value), an
-- instruction as a destination + two source ids + width + opcode, and a basic
-- block as a list of instructions evaluated LEFT-to-RIGHT (accumulator-passing
-- recursor, so the env threads forward exactly as the real interpreters do).
--
-- The headline theorem `lowerBlock_preserves` lifts the per-instruction value
-- correspondence `lowerOp_preserves_binop` over a whole block: lowering an
-- entire MIR basic block to trust-ir produces a block that, run on any starting
-- register file, yields the SAME final register file. This is the program-level
-- (basic-block) half of the MIR <-> trust-ir correspondence, built on top of
-- the instruction-level half above. No domain axioms (the only non-rfl steps
-- use congrArg + the proven per-op lemma + structural induction on the block).
-- ===========================================================================

-- Register environment: value-id -> carrier value (a total map, matching the
-- interpreters' SSA value tables).

-- Register write: overwrite value-id `d` with `v`, leaving every other id
-- untouched (faithful single-assignment store). `Nat.beq` is the prelude's
-- boolean equality on Nat.
def writeReg (e : (Nat -> Nat)) (d v : Nat) : (Nat -> Nat) :=
  fun r => match Nat.beq r d with | true => v | false => e r

-- A trust-ir SSA instruction: dst <- binop(width, env[src1], env[src2]), plus a
-- no-op (`irNop`, a real IR instruction form: it leaves the register file
-- unchanged). The two constructors keep `IrInst` a genuine inductive -- a
-- single-constructor inductive would be promoted to a STRUCTURE with
-- definitional projections, and reducing through those projections breaks
-- def-eq in the block-induction proof (`MirInst.0` vs `IrInst.0` mismatch).
inductive IrInst where
  | mkIr (dst : Nat) (src1 : Nat) (src2 : Nat) (width : Nat) (op : IrOp)
  | irNop

-- The MIR-side counterpart (same shape, MIR opcode, plus the no-op).
inductive MirInst where
  | mkMir (dst : Nat) (src1 : Nat) (src2 : Nat) (width : Nat) (op : MirOp)
  | mirNop

-- Execute one trust-ir instruction against the register file (interpret.rs:
-- compute the binop on the two source values, write the result into dst; the
-- no-op leaves the register file untouched).
def stepIr (e : (Nat -> Nat)) (i : IrInst) : (Nat -> Nat) :=
  @IrInst.casesOn.{1} (fun _ => (Nat -> Nat)) i
    (fun dst src1 src2 width op => writeReg e dst (irBinOp op width (e src1) (e src2)))
    e

-- Execute one MIR instruction -- the SAME register-file update with MIR's
-- (identical) wrapping/bitwise binop semantics.
def stepMir (e : (Nat -> Nat)) (i : MirInst) : (Nat -> Nat) :=
  @MirInst.casesOn.{1} (fun _ => (Nat -> Nat)) i
    (fun dst src1 src2 width op => writeReg e dst (mirBinOp op width (e src1) (e src2)))
    e

-- Instruction lowering MIR -> trust-ir (keep dst/src/width, lower the opcode;
-- no-op maps to no-op), and the reverse.
def lowerInst (i : MirInst) : IrInst :=
  @MirInst.casesOn (fun _ => IrInst) i
    (fun dst src1 src2 width op => IrInst.mkIr dst src1 src2 width (lowerOp op))
    IrInst.irNop

def raiseInst (i : IrInst) : MirInst :=
  @IrInst.casesOn (fun _ => MirInst) i
    (fun dst src1 src2 width op => MirInst.mkMir dst src1 src2 width (raiseOp op))
    MirInst.mirNop

-- PER-INSTRUCTION step correspondence: stepping the lowered instruction over any
-- register file produces the SAME register file as stepping the MIR original --
-- the writes agree because the destination/sources/width are preserved and the
-- written value agrees by `lowerOp_preserves_binop`. No funext needed (the two
-- writes are equal by congrArg on the written value).
--
-- NOTE on `@Eq.{1} (Nat -> Nat) ...`: a bare `a = b` between two register files
-- (`Nat -> Nat`, a function type / `Sort 1`) leaves the elaborator unable to
-- DEFAULT the `Eq` universe and it spuriously generalizes the theorem to a free
-- universe param. Pinning `@Eq.{1} (Nat -> Nat)` fixes the universe to `1`
-- (probed: the `.{1}` form kernel-checks; bare `=` and `.{0}` do not). The
-- per-instruction value lemmas above stay at `Nat` so they need no annotation.
theorem stepInst_preserves (e : (Nat -> Nat)) (i : MirInst) :
    @Eq.{1} (Nat -> Nat) (stepIr e (lowerInst i)) (stepMir e i) :=
  @MirInst.casesOn (fun ii => @Eq.{1} (Nat -> Nat) (stepIr e (lowerInst ii)) (stepMir e ii)) i
    (fun dst src1 src2 width op =>
      congrArg (writeReg e dst) (lowerOp_preserves_binop op width (e src1) (e src2)))
    rfl

-- ...and the reverse direction (raising a trust-ir instruction to MIR preserves
-- the register-file update), completing the BOTH-DIRECTIONS step correspondence.
theorem stepInst_raise_preserves (e : (Nat -> Nat)) (i : IrInst) :
    @Eq.{1} (Nat -> Nat) (stepMir e (raiseInst i)) (stepIr e i) :=
  @IrInst.casesOn (fun ii => @Eq.{1} (Nat -> Nat) (stepMir e (raiseInst ii)) (stepIr e ii)) i
    (fun dst src1 src2 width op =>
      congrArg (writeReg e dst) (raiseOp_preserves_binop op width (e src1) (e src2)))
    rfl

-- A basic block is a list of instructions (evaluated left to right).
inductive IrBlock where
  | bnil
  | bcons (i : IrInst) (rest : IrBlock)

inductive MirBlock where
  | mnil
  | mcons (i : MirInst) (rest : MirBlock)

-- Evaluate a trust-ir basic block: thread the register file forward through the
-- instructions (accumulator-passing recursor -> genuine left fold, so i1 runs
-- before i2 before ...).
def evalIrBlock (b : IrBlock) : (Nat -> Nat) -> (Nat -> Nat) :=
  @IrBlock.rec.{1} (fun _ => (Nat -> Nat) -> (Nat -> Nat))
    (fun e => e)
    (fun i rest ih => fun e => ih (stepIr e i))
    b

def evalMirBlock (b : MirBlock) : (Nat -> Nat) -> (Nat -> Nat) :=
  @MirBlock.rec.{1} (fun _ => (Nat -> Nat) -> (Nat -> Nat))
    (fun e => e)
    (fun i rest ih => fun e => ih (stepMir e i))
    b

-- Lower an entire MIR basic block to trust-ir (lower each instruction), and the
-- reverse.
def lowerBlock (b : MirBlock) : IrBlock :=
  @MirBlock.rec (fun _ => IrBlock)
    IrBlock.bnil
    (fun i rest ih => IrBlock.bcons (lowerInst i) ih)
    b

def raiseBlock (b : IrBlock) : MirBlock :=
  @IrBlock.rec (fun _ => MirBlock)
    MirBlock.mnil
    (fun i rest ih => MirBlock.mcons (raiseInst i) ih)
    b

-- Block-evaluation reduction lemmas (ι-reduction of the recursor on each
-- constructor; all rfl). These pin the operational semantics of a block.
theorem evalIrBlock_nil (e : (Nat -> Nat)) :
    @Eq.{1} (Nat -> Nat) (evalIrBlock IrBlock.bnil e) e := rfl
theorem evalIrBlock_cons (i : IrInst) (rest : IrBlock) (e : (Nat -> Nat)) :
    @Eq.{1} (Nat -> Nat) (evalIrBlock (IrBlock.bcons i rest) e) (evalIrBlock rest (stepIr e i)) := rfl
theorem evalMirBlock_nil (e : (Nat -> Nat)) :
    @Eq.{1} (Nat -> Nat) (evalMirBlock MirBlock.mnil e) e := rfl
theorem evalMirBlock_cons (i : MirInst) (rest : MirBlock) (e : (Nat -> Nat)) :
    @Eq.{1} (Nat -> Nat) (evalMirBlock (MirBlock.mcons i rest) e) (evalMirBlock rest (stepMir e i)) := rfl

-- Lowering reduction lemmas (rfl): lowering distributes over the block spine.
theorem lowerBlock_nil : lowerBlock MirBlock.mnil = IrBlock.bnil := rfl
theorem lowerBlock_cons (i : MirInst) (rest : MirBlock) :
    lowerBlock (MirBlock.mcons i rest) = IrBlock.bcons (lowerInst i) (lowerBlock rest) := rfl

-- THE PROGRAM-LEVEL (BASIC-BLOCK) CORRESPONDENCE: lowering a MIR basic block to
-- trust-ir preserves the WHOLE-BLOCK semantics -- run on ANY starting register
-- file, the lowered trust-ir block produces the same final register file as the
-- MIR original. Proven by structural induction on the block: the head step
-- agrees by `stepInst_preserves`, and the tail agrees by the induction
-- hypothesis (instantiated at the post-head register file).
theorem lowerBlock_preserves (b : MirBlock) :
    forall (e : (Nat -> Nat)), @Eq.{1} (Nat -> Nat) (evalIrBlock (lowerBlock b) e) (evalMirBlock b e) :=
  @MirBlock.rec
    (fun b => forall (e : (Nat -> Nat)), @Eq.{1} (Nat -> Nat) (evalIrBlock (lowerBlock b) e) (evalMirBlock b e))
    (fun e => rfl)
    (fun i rest ih => fun e =>
      Eq.trans
        (congrArg (evalIrBlock (lowerBlock rest)) (stepInst_preserves e i))
        (ih (stepMir e i)))
    b

-- ...and the reverse direction: raising a trust-ir basic block to MIR preserves
-- the whole-block semantics, completing the BOTH-DIRECTIONS program-level
-- correspondence.
theorem raiseBlock_preserves (b : IrBlock) :
    forall (e : (Nat -> Nat)), @Eq.{1} (Nat -> Nat) (evalMirBlock (raiseBlock b) e) (evalIrBlock b e) :=
  @IrBlock.rec
    (fun b => forall (e : (Nat -> Nat)), @Eq.{1} (Nat -> Nat) (evalMirBlock (raiseBlock b) e) (evalIrBlock b e))
    (fun e => rfl)
    (fun i rest ih => fun e =>
      Eq.trans
        (congrArg (evalMirBlock (raiseBlock rest)) (stepInst_raise_preserves e i))
        (ih (stepIr e i)))
    b


-- ===========================================================================
-- CONTROL FLOW: terminators + a fuel-bounded CFG interpreter, and the
-- whole-PROGRAM MIR <-> trust-ir correspondence.
--
-- A function in trust-ir / MIR is a control-flow graph: a finite set of basic
-- blocks, each ending in a terminator that picks the next block (or halts). We
-- model the block table as a map `Nat -> Block` (block-id -> block), the
-- terminator table as `Nat -> Term`, and interpret the CFG with a FUEL bound
-- (so the total function terminates even on loops). The crucial fact is that
-- the terminators and the CFG SHAPE are IDENTICAL across MIR and trust-ir --
-- only the per-block instruction lists lower -- so running the lowered CFG
-- yields the same final register file as the MIR CFG, on ANY entry / fuel /
-- start env. `runProg_congr` is the parametric core (running two CFGs that
-- agree block-by-block agree as whole programs); `cfgLower_preserves` /
-- `cfgRaise_preserves` instantiate it with `lowerBlock_preserves` /
-- `raiseBlock_preserves`. All down to the foundational axioms.
-- ===========================================================================

-- A basic-block terminator: return (halt), unconditional branch, or a
-- conditional branch on a register (taken when the register is nonzero).
inductive Term where
  | tret
  | tbr (target : Nat)
  | tcondBr (cond : Nat) (thn : Nat) (els : Nat)

-- The successor block selected by a terminator under a register file: `tret`
-- halts (none); `tbr` jumps unconditionally; `tcondBr` takes `thn` when the
-- condition register is nonzero, else `els`.
def nextBlock (t : Term) (e : (Nat -> Nat)) : Option Nat :=
  @Term.casesOn (fun _ => Option Nat) t
    Option.none
    (fun target => Option.some target)
    (fun cond thn els => match Nat.beq (e cond) 0 with | true => Option.some els | false => Option.some thn)

theorem nextBlock_ret (e : (Nat -> Nat)) : nextBlock Term.tret e = Option.none := rfl
theorem nextBlock_br (target : Nat) (e : (Nat -> Nat)) :
    nextBlock (Term.tbr target) e = Option.some target := rfl

-- Terminator successor selection agrees whenever the two register files agree
-- pointwise -- control flow depends only on the condition register's value, so
-- preserving the register file preserves the chosen successor.
theorem nextBlock_agrees (t : Term) (eA : (Nat -> Nat)) (eB : (Nat -> Nat))
    (H : forall (r : Nat), eA r = eB r) : nextBlock t eA = nextBlock t eB :=
  @Term.casesOn (fun tm => nextBlock tm eA = nextBlock tm eB) t
    rfl
    (fun target => rfl)
    (fun cond thn els =>
      congrArg (fun b => match Nat.beq b 0 with | true => Option.some els | false => Option.some thn) (H cond))

-- Fuel-bounded CFG interpreter, generic over the per-block evaluator
-- `step : Nat -> env -> env` (run block `bid` on `e`). Each step runs the
-- current block then follows its terminator (ret halts with the post-block env;
-- br jumps; condBr branches on the condition register). `@..casesOn.{1}` pins
-- the motive universe (the motive returns a function type, `Sort 1`).
def runProg (fuel : Nat) :
    (Nat -> (Nat -> Nat) -> (Nat -> Nat)) -> (Nat -> Term) -> Nat -> (Nat -> Nat) -> (Nat -> Nat) :=
  @Nat.rec.{1}
    (fun _ => (Nat -> (Nat -> Nat) -> (Nat -> Nat)) -> (Nat -> Term) -> Nat -> (Nat -> Nat) -> (Nat -> Nat))
    (fun step terms bid e => e)
    (fun f ihrun step terms bid e =>
      @Term.casesOn.{1} (fun _ => (Nat -> Nat)) (terms bid)
        (step bid e)
        (fun target => ihrun step terms target (step bid e))
        (fun cond thn els =>
          @Bool.casesOn.{1} (fun _ => (Nat -> Nat)) (Nat.beq ((step bid e) cond) 0)
            (ihrun step terms thn (step bid e))
            (ihrun step terms els (step bid e))))
    fuel

-- Operational-semantics reduction: out of fuel returns the current register file.
theorem runProg_zero (step : Nat -> (Nat -> Nat) -> (Nat -> Nat)) (terms : Nat -> Term)
    (bid : Nat) (e : (Nat -> Nat)) : @Eq.{1} (Nat -> Nat) (runProg 0 step terms bid e) e := rfl

-- THE PARAMETRIC CFG CORRESPONDENCE: two CFGs with the SAME terminators that
-- agree block-by-block (their per-block evaluators produce the same register
-- file) produce the same final register file as WHOLE PROGRAMS, on any fuel /
-- entry / start env. Proven by induction on fuel: the head block agrees by the
-- hypothesis (rewritten in via congrArg), and each successor sub-run agrees by
-- the induction hypothesis (case-split on the terminator, and on the condition
-- register for `tcondBr`).
theorem runProg_congr (fuel : Nat) (stepA : Nat -> (Nat -> Nat) -> (Nat -> Nat))
    (stepB : Nat -> (Nat -> Nat) -> (Nat -> Nat)) (terms : Nat -> Term)
    (Hstep : forall (b : Nat) (ee : (Nat -> Nat)), @Eq.{1} (Nat -> Nat) (stepA b ee) (stepB b ee)) :
    forall (bid : Nat) (e : (Nat -> Nat)),
      @Eq.{1} (Nat -> Nat) (runProg fuel stepA terms bid e) (runProg fuel stepB terms bid e) :=
  @Nat.rec
    (fun fuel =>
      forall (bid : Nat) (e : (Nat -> Nat)),
        @Eq.{1} (Nat -> Nat) (runProg fuel stepA terms bid e) (runProg fuel stepB terms bid e))
    (fun bid e => rfl)
    (fun f IH bid e =>
      Eq.trans
        (congrArg
          (fun v =>
            @Term.casesOn.{1} (fun _ => (Nat -> Nat)) (terms bid)
              v
              (fun target => runProg f stepA terms target v)
              (fun cond thn els =>
                @Bool.casesOn.{1} (fun _ => (Nat -> Nat)) (Nat.beq (v cond) 0)
                  (runProg f stepA terms thn v)
                  (runProg f stepA terms els v)))
          (Hstep bid e))
        (@Term.casesOn
          (fun tm =>
            @Eq.{1} (Nat -> Nat)
              (@Term.casesOn.{1} (fun _ => (Nat -> Nat)) tm
                (stepB bid e)
                (fun target => runProg f stepA terms target (stepB bid e))
                (fun cond thn els =>
                  @Bool.casesOn.{1} (fun _ => (Nat -> Nat)) (Nat.beq ((stepB bid e) cond) 0)
                    (runProg f stepA terms thn (stepB bid e))
                    (runProg f stepA terms els (stepB bid e))))
              (@Term.casesOn.{1} (fun _ => (Nat -> Nat)) tm
                (stepB bid e)
                (fun target => runProg f stepB terms target (stepB bid e))
                (fun cond thn els =>
                  @Bool.casesOn.{1} (fun _ => (Nat -> Nat)) (Nat.beq ((stepB bid e) cond) 0)
                    (runProg f stepB terms thn (stepB bid e))
                    (runProg f stepB terms els (stepB bid e)))))
          (terms bid)
          rfl
          (fun target => IH target (stepB bid e))
          (fun cond thn els =>
            @Bool.casesOn
              (fun bb =>
                @Eq.{1} (Nat -> Nat)
                  (@Bool.casesOn.{1} (fun _ => (Nat -> Nat)) bb
                    (runProg f stepA terms thn (stepB bid e)) (runProg f stepA terms els (stepB bid e)))
                  (@Bool.casesOn.{1} (fun _ => (Nat -> Nat)) bb
                    (runProg f stepB terms thn (stepB bid e)) (runProg f stepB terms els (stepB bid e))))
              (Nat.beq ((stepB bid e) cond) 0)
              (IH thn (stepB bid e))
              (IH els (stepB bid e)))))
    fuel

-- THE WHOLE-PROGRAM CORRESPONDENCE: lowering EVERY basic block of a MIR control-
-- flow graph to trust-ir preserves the final register file of running the whole
-- CFG (any fuel, any entry block, any starting register file). Instantiates the
-- parametric core with the per-block correspondence `lowerBlock_preserves`.
theorem cfgLower_preserves (fuel : Nat) (mblocks : Nat -> MirBlock) (terms : Nat -> Term)
    (bid : Nat) (e : (Nat -> Nat)) :
    @Eq.{1} (Nat -> Nat)
      (runProg fuel (fun b ee => evalIrBlock (lowerBlock (mblocks b)) ee) terms bid e)
      (runProg fuel (fun b ee => evalMirBlock (mblocks b) ee) terms bid e) :=
  runProg_congr fuel
    (fun b ee => evalIrBlock (lowerBlock (mblocks b)) ee)
    (fun b ee => evalMirBlock (mblocks b) ee)
    terms
    (fun b ee => lowerBlock_preserves (mblocks b) ee)
    bid e

-- ...and the reverse direction (raising every trust-ir block to MIR preserves
-- the whole-CFG result), completing the BOTH-DIRECTIONS whole-program
-- correspondence.
theorem cfgRaise_preserves (fuel : Nat) (iblocks : Nat -> IrBlock) (terms : Nat -> Term)
    (bid : Nat) (e : (Nat -> Nat)) :
    @Eq.{1} (Nat -> Nat)
      (runProg fuel (fun b ee => evalMirBlock (raiseBlock (iblocks b)) ee) terms bid e)
      (runProg fuel (fun b ee => evalIrBlock (iblocks b) ee) terms bid e) :=
  runProg_congr fuel
    (fun b ee => evalMirBlock (raiseBlock (iblocks b)) ee)
    (fun b ee => evalIrBlock (iblocks b) ee)
    terms
    (fun b ee => raiseBlock_preserves (iblocks b) ee)
    bid e

-- Per-transition control-flow correspondence: after running block `mblock`, the
-- successor selected by terminator `t` is the SAME whether we ran the lowered
-- trust-ir block or the MIR block (the post-block register files agree by
-- `lowerBlock_preserves`, so `nextBlock` picks the same successor).
theorem lowerCfgSucc_preserves (mblock : MirBlock) (t : Term) (e : (Nat -> Nat)) :
    nextBlock t (evalIrBlock (lowerBlock mblock) e) = nextBlock t (evalMirBlock mblock e) :=
  congrArg (nextBlock t) (lowerBlock_preserves mblock e)


-- ===========================================================================
-- THE FULL PIPELINE at the PROGRAM level: trust-ir -> trust-cg, then composing
-- MIR -> trust-ir -> trust-cg, at the BASIC-BLOCK and WHOLE-CFG levels.
--
-- The value-level pipeline (`lowerMirToCg_preserves`) already closed
-- MIR -> trust-ir -> trust-cg for single instructions. Here we lift it to whole
-- basic blocks and whole control-flow graphs, reusing the trust-cg LIR opcode
-- semantics `cgBinOp` and the per-op lowering `lowerIrToCg` (with
-- `lowerIrToCg_preserves`). A MIR function, lowered all the way to trust-cg LIR,
-- computes the same final register file as the MIR original -- on any fuel,
-- entry block, and start env, down to the foundational axioms.
-- ===========================================================================

-- A trust-cg LIR instruction (same shape as the trust-ir one, CG opcode) plus a
-- no-op (second constructor keeps it a genuine inductive, not a structure).
inductive CgInst where
  | mkCg (dst : Nat) (src1 : Nat) (src2 : Nat) (width : Nat) (op : CgOp)
  | cgNop

-- Execute one trust-cg instruction against the register file (`cgBinOp` is the
-- audited trust-cg LIR value semantics; the no-op leaves the file untouched).
def stepCg (e : (Nat -> Nat)) (i : CgInst) : (Nat -> Nat) :=
  @CgInst.casesOn.{1} (fun _ => (Nat -> Nat)) i
    (fun dst src1 src2 width op => writeReg e dst (cgBinOp op width (e src1) (e src2)))
    e

-- Lower a trust-ir instruction to a trust-cg instruction (lower the opcode via
-- `lowerIrToCg`; no-op maps to no-op).
def lowerInstIrToCg (i : IrInst) : CgInst :=
  @IrInst.casesOn (fun _ => CgInst) i
    (fun dst src1 src2 width op => CgInst.mkCg dst src1 src2 width (lowerIrToCg op))
    CgInst.cgNop

-- PER-INSTRUCTION step correspondence (trust-ir -> trust-cg): stepping the
-- lowered CG instruction agrees with stepping the trust-ir one (the writes agree
-- because the value agrees by `lowerIrToCg_preserves`).
theorem stepInstIrToCg_preserves (e : (Nat -> Nat)) (i : IrInst) :
    @Eq.{1} (Nat -> Nat) (stepCg e (lowerInstIrToCg i)) (stepIr e i) :=
  @IrInst.casesOn (fun ii => @Eq.{1} (Nat -> Nat) (stepCg e (lowerInstIrToCg ii)) (stepIr e ii)) i
    (fun dst src1 src2 width op =>
      congrArg (writeReg e dst) (lowerIrToCg_preserves op width (e src1) (e src2)))
    rfl

-- A trust-cg basic block.
inductive CgBlock where
  | cbnil
  | cbcons (i : CgInst) (rest : CgBlock)

def evalCgBlock (b : CgBlock) : (Nat -> Nat) -> (Nat -> Nat) :=
  @CgBlock.rec.{1} (fun _ => (Nat -> Nat) -> (Nat -> Nat))
    (fun e => e)
    (fun i rest ih => fun e => ih (stepCg e i))
    b

def lowerBlockIrToCg (b : IrBlock) : CgBlock :=
  @IrBlock.rec (fun _ => CgBlock)
    CgBlock.cbnil
    (fun i rest ih => CgBlock.cbcons (lowerInstIrToCg i) ih)
    b

theorem evalCgBlock_nil (e : (Nat -> Nat)) :
    @Eq.{1} (Nat -> Nat) (evalCgBlock CgBlock.cbnil e) e := rfl
theorem evalCgBlock_cons (i : CgInst) (rest : CgBlock) (e : (Nat -> Nat)) :
    @Eq.{1} (Nat -> Nat) (evalCgBlock (CgBlock.cbcons i rest) e) (evalCgBlock rest (stepCg e i)) := rfl

-- BLOCK-level trust-ir -> trust-cg correspondence: lowering a whole trust-ir
-- basic block to trust-cg preserves the final register file (structural
-- induction; head via `stepInstIrToCg_preserves`, tail via the IH).
theorem lowerBlockIrToCg_preserves (b : IrBlock) :
    forall (e : (Nat -> Nat)),
      @Eq.{1} (Nat -> Nat) (evalCgBlock (lowerBlockIrToCg b) e) (evalIrBlock b e) :=
  @IrBlock.rec
    (fun b => forall (e : (Nat -> Nat)),
      @Eq.{1} (Nat -> Nat) (evalCgBlock (lowerBlockIrToCg b) e) (evalIrBlock b e))
    (fun e => rfl)
    (fun i rest ih => fun e =>
      Eq.trans
        (congrArg (evalCgBlock (lowerBlockIrToCg rest)) (stepInstIrToCg_preserves e i))
        (ih (stepIr e i)))
    b

-- THE FULL PIPELINE at the BLOCK level: lowering a MIR basic block all the way
-- through trust-ir to trust-cg preserves the whole-block register file
-- (composes `lowerBlockIrToCg_preserves` with `lowerBlock_preserves`).
theorem lowerBlockMirToCg_preserves (b : MirBlock) :
    forall (e : (Nat -> Nat)),
      @Eq.{1} (Nat -> Nat) (evalCgBlock (lowerBlockIrToCg (lowerBlock b)) e) (evalMirBlock b e) :=
  fun e =>
    Eq.trans
      (lowerBlockIrToCg_preserves (lowerBlock b) e)
      (lowerBlock_preserves b e)

-- THE FULL PIPELINE at the WHOLE-PROGRAM level: running a MIR control-flow graph
-- lowered all the way to trust-cg agrees with running the MIR CFG, on any fuel /
-- entry block / start env. Instantiates `runProg_congr` with the block-level
-- full-pipeline correspondence.
theorem cfgLowerMirToCg_preserves (fuel : Nat) (mblocks : Nat -> MirBlock) (terms : Nat -> Term)
    (bid : Nat) (e : (Nat -> Nat)) :
    @Eq.{1} (Nat -> Nat)
      (runProg fuel (fun b ee => evalCgBlock (lowerBlockIrToCg (lowerBlock (mblocks b))) ee) terms bid e)
      (runProg fuel (fun b ee => evalMirBlock (mblocks b) ee) terms bid e) :=
  runProg_congr fuel
    (fun b ee => evalCgBlock (lowerBlockIrToCg (lowerBlock (mblocks b))) ee)
    (fun b ee => evalMirBlock (mblocks b) ee)
    terms
    (fun b ee => lowerBlockMirToCg_preserves (mblocks b) ee)
    bid e


-- ===========================================================================
-- UNSIGNED DIV/REM instruction correspondence (Udiv / Urem).
--
-- trust-ir `BinOp::UDiv` / `BinOp::URem` (inst.rs:11) and MIR's unsigned
-- div/rem compute Nat division / remainder on the carrier; trust-cg's Udiv/Urem
-- (instructions.rs) do the same. Division/remainder of an in-range value stays
-- in range, so no width-wrap is needed -- the computed value is IDENTICAL across
-- all three IRs, so lowering preserves it in both directions and through the
-- full MIR -> trust-ir -> trust-cg pipeline.
--
-- SIGNED Sdiv/Srem are DEFERRED: they need the signed carrier interpretation
-- (the same complement-based reasoning that blocks SExt / signed shift), with
-- no clean axiom-free Nat formula.
-- ===========================================================================
inductive IrDivOp where
  | iudiv
  | iurem
inductive MirDivOp where
  | mudiv
  | murem
inductive CgDivOp where
  | cudiv
  | curem

-- Value semantics: unsigned division `a / b` and remainder `a % b` on the Nat
-- carrier (same shape on all three IRs).
def irDivOp : IrDivOp -> Nat -> Nat -> Nat := fun op a b =>
  @IrDivOp.casesOn (fun _ => Nat) op (a / b) (a % b)
def mirDivOp : MirDivOp -> Nat -> Nat -> Nat := fun op a b =>
  @MirDivOp.casesOn (fun _ => Nat) op (a / b) (a % b)
def cgDivOp : CgDivOp -> Nat -> Nat -> Nat := fun op a b =>
  @CgDivOp.casesOn (fun _ => Nat) op (a / b) (a % b)

def lowerDivOp : MirDivOp -> IrDivOp := fun op =>
  @MirDivOp.casesOn (fun _ => IrDivOp) op IrDivOp.iudiv IrDivOp.iurem
def raiseDivOp : IrDivOp -> MirDivOp := fun op =>
  @IrDivOp.casesOn (fun _ => MirDivOp) op MirDivOp.mudiv MirDivOp.murem
def lowerDivIrToCg : IrDivOp -> CgDivOp := fun op =>
  @IrDivOp.casesOn (fun _ => CgDivOp) op CgDivOp.cudiv CgDivOp.curem

theorem irDivOp_udiv (a b : Nat) : irDivOp IrDivOp.iudiv a b = a / b := rfl
theorem irDivOp_urem (a b : Nat) : irDivOp IrDivOp.iurem a b = a % b := rfl

theorem raiseDivOp_lowerDivOp (op : MirDivOp) : raiseDivOp (lowerDivOp op) = op :=
  @MirDivOp.casesOn (fun o => raiseDivOp (lowerDivOp o) = o) op rfl rfl
theorem lowerDivOp_raiseDivOp (op : IrDivOp) : lowerDivOp (raiseDivOp op) = op :=
  @IrDivOp.casesOn (fun o => lowerDivOp (raiseDivOp o) = o) op rfl rfl

-- DIV/REM value preservation: both directions, and the full pipeline.
theorem lowerDivOp_preserves (op : MirDivOp) (a b : Nat) :
    irDivOp (lowerDivOp op) a b = mirDivOp op a b :=
  @MirDivOp.casesOn (fun o => irDivOp (lowerDivOp o) a b = mirDivOp o a b) op rfl rfl
theorem raiseDivOp_preserves (op : IrDivOp) (a b : Nat) :
    mirDivOp (raiseDivOp op) a b = irDivOp op a b :=
  @IrDivOp.casesOn (fun o => mirDivOp (raiseDivOp o) a b = irDivOp o a b) op rfl rfl
theorem lowerDivIrToCg_preserves (op : IrDivOp) (a b : Nat) :
    cgDivOp (lowerDivIrToCg op) a b = irDivOp op a b :=
  @IrDivOp.casesOn (fun o => cgDivOp (lowerDivIrToCg o) a b = irDivOp o a b) op rfl rfl
theorem lowerDivMirToCg_preserves (op : MirDivOp) (a b : Nat) :
    cgDivOp (lowerDivIrToCg (lowerDivOp op)) a b = mirDivOp op a b :=
  @MirDivOp.casesOn (fun o => cgDivOp (lowerDivIrToCg (lowerDivOp o)) a b = mirDivOp o a b) op rfl rfl


-- ===========================================================================
-- TYPED-INSTRUCTION layer: thread the trust-ir TYPE (`TyIr`) and its declared
-- bit-width through the binop, connecting the TYPE faithfulness (`bitWidth`) to
-- the INSTRUCTION value semantics. `tyWidth` is the raw integer width a type
-- carries (matching `bitWidth`); a TYPED binop runs at the type's width, so
-- lowering a typed op preserves the value at THAT width -- the width is now
-- derived from the TYPE, not an arbitrary Nat parameter.
-- ===========================================================================
def tyWidth : TyIr -> Nat := fun t =>
  @TyIr.casesOn (fun _ => Nat) t
    8 16 32 64 128
    8 16 32 64 128
    1
    0
    (fun _a _b => 0)

-- `tyWidth` agrees with the faithful `bitWidth` on the integer/bool types.
theorem tyWidth_bitWidth_i8 : Option.some (tyWidth TyIr.i8) = bitWidth TyIr.i8 := rfl
theorem tyWidth_bitWidth_i32 : Option.some (tyWidth TyIr.i32) = bitWidth TyIr.i32 := rfl
theorem tyWidth_bitWidth_u64 : Option.some (tyWidth TyIr.u64) = bitWidth TyIr.u64 := rfl
theorem tyWidth_bitWidth_u128 : Option.some (tyWidth TyIr.u128) = bitWidth TyIr.u128 := rfl
theorem tyWidth_bitWidth_tbool : Option.some (tyWidth TyIr.tbool) = bitWidth TyIr.tbool := rfl

-- A TYPED binop runs the opcode at the width declared by the type.
def tyBinOpIr : TyIr -> IrOp -> Nat -> Nat -> Nat := fun t op a b => irBinOp op (tyWidth t) a b
def tyBinOpMir : TyIr -> MirOp -> Nat -> Nat -> Nat := fun t op a b => mirBinOp op (tyWidth t) a b
def tyBinOpCg : TyIr -> CgOp -> Nat -> Nat -> Nat := fun t op a b => cgBinOp op (tyWidth t) a b

-- TYPED value preservation: lowering a typed MIR binop to trust-ir, and all the
-- way to trust-cg, preserves the value -- AT THE TYPE'S WIDTH (instantiating the
-- width-generic per-op lemmas at `tyWidth t`).
theorem tyLower_preserves (t : TyIr) (op : MirOp) (a b : Nat) :
    tyBinOpIr t (lowerOp op) a b = tyBinOpMir t op a b :=
  lowerOp_preserves_binop op (tyWidth t) a b
theorem tyLowerMirToCg_preserves (t : TyIr) (op : MirOp) (a b : Nat) :
    tyBinOpCg t (lowerIrToCg (lowerOp op)) a b = tyBinOpMir t op a b :=
  lowerMirToCg_preserves op (tyWidth t) a b


-- ===========================================================================
-- OVERFLOW FLAG as the Nat-valued CARRY-OUT (completing the trust-ir Overflow op
-- alongside the wrapped result from the earlier slice).
--
-- trust-ir's checked-arithmetic `BinOp::Add/Sub/Mul` with overflow produce a
-- (wrapped value, overflow flag) pair. The wrapped value is already proven
-- preserved (`irOvResult` / `lowerOvOp_preserves_result`). Here we add the FLAG.
-- The Bool-valued flag (`a + b >= 2^w`) is blocked: surface `decide` does not
-- reduce, so there is no axiom-free Bool comparison. BUT the flag's VALUE is the
-- carry-out, which for in-range operands is exactly `(a + b) / 2^w` in {0,1} (and
-- `(a*b) / 2^w` for the multiply high part / `(a + (2^w - b%2^w)) / 2^w` for the
-- subtract carry) -- a Nat, computed with `Nat.div`, needing no comparison. The
-- carry is the SAME formula on all three IRs, so lowering preserves it. This is
-- the axiom-free part of the overflow correspondence; the Bool packaging remains
-- deferred behind the `decide` blocker.
-- ===========================================================================
def irOvCarry : IrOvOp -> Nat -> Nat -> Nat -> Nat := fun op w a b =>
  @IrOvOp.casesOn (fun _ => Nat) op
    ((a + b) / (2 ^ w))
    ((a + (2 ^ w - b % (2 ^ w))) / (2 ^ w))
    ((a * b) / (2 ^ w))
def mirOvCarry : MirOvOp -> Nat -> Nat -> Nat -> Nat := fun op w a b =>
  @MirOvOp.casesOn (fun _ => Nat) op
    ((a + b) / (2 ^ w))
    ((a + (2 ^ w - b % (2 ^ w))) / (2 ^ w))
    ((a * b) / (2 ^ w))

theorem irOvCarry_add (w a b : Nat) : irOvCarry IrOvOp.ovadd w a b = (a + b) / (2 ^ w) := rfl
theorem irOvCarry_mul (w a b : Nat) : irOvCarry IrOvOp.ovmul w a b = (a * b) / (2 ^ w) := rfl

-- The overflow carry-out is preserved by lowering in BOTH directions (same
-- carry formula on MIR and trust-ir), completing the overflow correspondence
-- (wrapped value + carry flag) at the value level.
theorem lowerOvCarry_preserves (op : MirOvOp) (w a b : Nat) :
    irOvCarry (lowerOvOp op) w a b = mirOvCarry op w a b :=
  @MirOvOp.casesOn (fun o => irOvCarry (lowerOvOp o) w a b = mirOvCarry o w a b) op rfl rfl rfl
theorem raiseOvCarry_preserves (op : IrOvOp) (w a b : Nat) :
    mirOvCarry (raiseOvOp op) w a b = irOvCarry op w a b :=
  @IrOvOp.casesOn (fun o => mirOvCarry (raiseOvOp o) w a b = irOvCarry o w a b) op rfl rfl rfl


-- ===========================================================================
-- UNBLOCKING the deferred shift / sign-extension / Bool-compare ops by
-- REFORMULATION with axiom-free computable primitives.
--
-- The earlier deferrals were NOT about expressiveness -- they were caused by
-- reaching for two specific things: `Nat.shiftRight` (a non-foundational prelude
-- AXIOM -- using it pollutes the axiom closure) and `decide` (which does not
-- reduce in surface proofs here). Both are avoidable:
--   * a LOGICAL right shift `a >> k` on the carrier is `a / 2^k`  (Nat.div),
--   * the SIGN BIT of a w-bit value is `a / 2^(w-1)` in {0,1}      (Nat.div),
--   * a Bool comparison is `Nat.blt` / `Nat.ble` / `Nat.beq`       (axiom-free
--     boolean deciders that DO reduce).
-- With these, the lowering correspondences hold by `rfl` per opcode (a lowering
-- correspondence is a syntactic equality of two identical formulas after
-- `casesOn` iota -- it never needs the arithmetic to reduce to a literal), and
-- every theorem's axiom closure stays empty.
-- ===========================================================================

-- LOGICAL SHIFT RIGHT (trust-ir BinOp::LShr / MIR unsigned `>>` / trust-cg Ushr):
-- `a >> k = a / 2^k` on the carrier (re-truncated to width w; a/2^k <= a so the
-- mask is a no-op, kept for width-uniformity). NO `Nat.shiftRight`.
def irLShr : Nat -> Nat -> Nat -> Nat := fun w a k => (a / (2 ^ k)) % (2 ^ w)
def mirLShr : Nat -> Nat -> Nat -> Nat := fun w a k => (a / (2 ^ k)) % (2 ^ w)
def cgLShr : Nat -> Nat -> Nat -> Nat := fun w a k => (a / (2 ^ k)) % (2 ^ w)
theorem irLShr_def (w a k : Nat) : irLShr w a k = (a / (2 ^ k)) % (2 ^ w) := rfl
theorem lowerLShr_preserves (w a k : Nat) : irLShr w a k = mirLShr w a k := rfl
theorem raiseLShr_preserves (w a k : Nat) : mirLShr w a k = irLShr w a k := rfl
theorem lowerLShrIrToCg_preserves (w a k : Nat) : cgLShr w a k = irLShr w a k := rfl
theorem lowerLShrMirToCg_preserves (w a k : Nat) : cgLShr w a k = mirLShr w a k := rfl

-- SIGN BIT of a w-bit value: the top bit `a / 2^(w-1)` (in {0,1} for a < 2^w),
-- computed with Nat.div -- no comparison, no `decide`.
def signBit : Nat -> Nat -> Nat := fun w a => a / (2 ^ (w - 1))
theorem signBit_def (w a : Nat) : signBit w a = a / (2 ^ (w - 1)) := rfl

-- SIGN EXTENSION (trust-ir CastOp::SExt) from width w to w': keep the low w
-- bits, fill bits w..w'-1 with the sign bit -> carrier value
-- `a + signBit * (2^w' - 2^w)`. NO complement, NO `Nat.shiftRight`.
def irSExt : Nat -> Nat -> Nat -> Nat := fun w wp a => a + (signBit w a) * ((2 ^ wp) - (2 ^ w))
def mirSExt : Nat -> Nat -> Nat -> Nat := fun w wp a => a + (signBit w a) * ((2 ^ wp) - (2 ^ w))
theorem lowerSExt_preserves (w wp a : Nat) : irSExt w wp a = mirSExt w wp a := rfl
theorem raiseSExt_preserves (w wp a : Nat) : mirSExt w wp a = irSExt w wp a := rfl

-- ARITHMETIC SHIFT RIGHT (trust-ir BinOp::AShr): logical `a / 2^k` with the top
-- k bits filled by the sign bit -> `(a / 2^k) + signBit * (2^w - 2^(w-k))`.
def irAShr : Nat -> Nat -> Nat -> Nat := fun w a k =>
  (a / (2 ^ k)) + (signBit w a) * ((2 ^ w) - (2 ^ (w - k)))
def mirAShr : Nat -> Nat -> Nat -> Nat := fun w a k =>
  (a / (2 ^ k)) + (signBit w a) * ((2 ^ w) - (2 ^ (w - k)))
theorem lowerAShr_preserves (w a k : Nat) : irAShr w a k = mirAShr w a k := rfl
theorem raiseAShr_preserves (w a k : Nat) : mirAShr w a k = irAShr w a k := rfl

-- BOOL-VALUED COMPARISON via `Nat.blt` / `Nat.beq` (boolean deciders that reduce
-- and rest on no axioms) -- the axiom-free replacement for `decide`. This is the
-- Bool-PACKAGED form of the Prop-level irUlt/irEq from the earlier slice.
def irUltB : Nat -> Nat -> Nat -> Bool := fun w a b => Nat.blt (a % (2 ^ w)) (b % (2 ^ w))
def mirUltB : Nat -> Nat -> Nat -> Bool := fun w a b => Nat.blt (a % (2 ^ w)) (b % (2 ^ w))
def irEqB : Nat -> Nat -> Bool := fun a b => Nat.beq a b
def mirEqB : Nat -> Nat -> Bool := fun a b => Nat.beq a b
theorem lowerUltB_preserves (w a b : Nat) : irUltB w a b = mirUltB w a b := rfl
theorem raiseUltB_preserves (w a b : Nat) : mirUltB w a b = irUltB w a b := rfl
theorem lowerEqB_preserves (a b : Nat) : irEqB a b = mirEqB a b := rfl

-- BOOL-VALUED OVERFLOW FLAG for unsigned add: true iff `a + b >= 2^w`, i.e.
-- `Nat.ble (2^w) (a+b)` -- the axiom-free Bool packaging of the carry-out
-- (whose Nat value was proven preserved above).
def irOvFlagAdd : Nat -> Nat -> Nat -> Bool := fun w a b => Nat.ble (2 ^ w) (a + b)
def mirOvFlagAdd : Nat -> Nat -> Nat -> Bool := fun w a b => Nat.ble (2 ^ w) (a + b)
theorem lowerOvFlagAdd_preserves (w a b : Nat) : irOvFlagAdd w a b = mirOvFlagAdd w a b := rfl
theorem raiseOvFlagAdd_preserves (w a b : Nat) : mirOvFlagAdd w a b = irOvFlagAdd w a b := rfl


-- ===========================================================================
-- SIGNED DIV/REM (Sdiv / Srem) by a two's-complement magnitude model -- the last
-- instruction-correspondence blocker, now axiom-free.
--
-- On the w-bit two's-complement carrier a value `a in [0, 2^w)` denotes the
-- signed integer `a` (if the sign bit is 0) or `a - 2^w` (if 1). Signed division
-- rounds toward zero, so it is computed on MAGNITUDES with the result's sign =
-- (sign a) xor (sign b); the remainder takes the dividend's sign. All of this is
-- Nat arithmetic on the carrier (Nat.div / Nat.mod / Nat.mul / Nat.sub, sign bit
-- via Nat.div) -- no `Nat.shiftRight`, no `decide`, no complement intrinsic. The
-- formula is identical on MIR / trust-ir / trust-cg, so lowering preserves it by
-- `rfl`. (We prove the LOWERING correspondence; full faithfulness of the
-- rounding to Rust's signed `/`/`%` is a separate value-level claim.)
-- ===========================================================================

-- Magnitude of a w-bit signed value: `a` if non-negative, else `2^w - a`.
def sMag : Nat -> Nat -> Nat := fun w a =>
  (1 - signBit w a) * a + (signBit w a) * ((2 ^ w) - a)
-- Re-encode a magnitude `m` with sign `neg in {0,1}` into the w-bit carrier.
def encSigned : Nat -> Nat -> Nat -> Nat := fun w neg m =>
  (1 - neg) * m + neg * ((2 ^ w) - m)
-- Result sign of a signed multiply/divide: (sign a) xor (sign b), in {0,1}.
def sXor : Nat -> Nat -> Nat -> Nat := fun w a b => (signBit w a + signBit w b) % 2

-- Signed division: divide magnitudes, re-encode with the xor sign.
def irSDiv : Nat -> Nat -> Nat -> Nat := fun w a b =>
  encSigned w (sXor w a b) ((sMag w a) / (sMag w b))
def mirSDiv : Nat -> Nat -> Nat -> Nat := fun w a b =>
  encSigned w (sXor w a b) ((sMag w a) / (sMag w b))
def cgSDiv : Nat -> Nat -> Nat -> Nat := fun w a b =>
  encSigned w (sXor w a b) ((sMag w a) / (sMag w b))

-- Signed remainder: remainder of magnitudes, re-encode with the DIVIDEND's sign.
def irSRem : Nat -> Nat -> Nat -> Nat := fun w a b =>
  encSigned w (signBit w a) ((sMag w a) % (sMag w b))
def mirSRem : Nat -> Nat -> Nat -> Nat := fun w a b =>
  encSigned w (signBit w a) ((sMag w a) % (sMag w b))

theorem lowerSDiv_preserves (w a b : Nat) : irSDiv w a b = mirSDiv w a b := rfl
theorem raiseSDiv_preserves (w a b : Nat) : mirSDiv w a b = irSDiv w a b := rfl
theorem lowerSDivMirToCg_preserves (w a b : Nat) : cgSDiv w a b = mirSDiv w a b := rfl
theorem lowerSRem_preserves (w a b : Nat) : irSRem w a b = mirSRem w a b := rfl
theorem raiseSRem_preserves (w a b : Nat) : mirSRem w a b = irSRem w a b := rfl


-- ===========================================================================
-- MEMORY OPERATIONS (Load / Store): the STATEFUL dimension of the
-- correspondence (everything above is register/value level).
--
-- trust-ir's `interpret.rs` Load/Store read/write a byte-addressed memory; we
-- model the memory as a total map address -> value (`Nat -> Nat`), exactly like
-- the register file. A Store reads its address and value out of the register
-- file and writes memory; a Load reads memory at an address. Lowering a MIR
-- memory op to trust-ir (and a whole straight-line sequence of them) preserves
-- the memory effect -- proven by the SAME register-file/block technique as the
-- arithmetic instructions, both directions, all to the foundational axioms.
-- ===========================================================================

-- Memory write: store value `v` at address `d` (single-address store).
def writeMem (m : (Nat -> Nat)) (d : Nat) (v : Nat) : (Nat -> Nat) :=
  fun r => match Nat.beq r d with | true => v | false => m r

-- LOAD value semantics: read memory at an address. Identical on MIR/trust-ir.
def loadIr : (Nat -> Nat) -> Nat -> Nat := fun m addr => m addr
def loadMir : (Nat -> Nat) -> Nat -> Nat := fun m addr => m addr
theorem load_preserves (m : (Nat -> Nat)) (addr : Nat) : loadIr m addr = loadMir m addr := rfl

-- A memory STORE instruction: store register `valReg` at the address held in
-- register `addrReg`; plus a no-op (second constructor keeps it a genuine
-- inductive, not a structure -- avoids the projection-mismatch def-eq trap).
inductive IrMemInst where
  | mstoreIr (addrReg : Nat) (valReg : Nat)
  | mnopIr
inductive MirMemInst where
  | mstoreMir (addrReg : Nat) (valReg : Nat)
  | mnopMir

-- Execute a memory instruction against memory `m`, given register file `regs`.
def stepMemIr (regs : (Nat -> Nat)) (m : (Nat -> Nat)) (i : IrMemInst) : (Nat -> Nat) :=
  @IrMemInst.casesOn.{1} (fun _ => (Nat -> Nat)) i
    (fun addrReg valReg => writeMem m (regs addrReg) (regs valReg))
    m
def stepMemMir (regs : (Nat -> Nat)) (m : (Nat -> Nat)) (i : MirMemInst) : (Nat -> Nat) :=
  @MirMemInst.casesOn.{1} (fun _ => (Nat -> Nat)) i
    (fun addrReg valReg => writeMem m (regs addrReg) (regs valReg))
    m

def lowerMemInst (i : MirMemInst) : IrMemInst :=
  @MirMemInst.casesOn (fun _ => IrMemInst) i
    (fun addrReg valReg => IrMemInst.mstoreIr addrReg valReg)
    IrMemInst.mnopIr
def raiseMemInst (i : IrMemInst) : MirMemInst :=
  @IrMemInst.casesOn (fun _ => MirMemInst) i
    (fun addrReg valReg => MirMemInst.mstoreMir addrReg valReg)
    MirMemInst.mnopMir

-- PER-INSTRUCTION memory-effect correspondence (both directions): the store
-- writes the same address/value, so the resulting memory agrees.
theorem stepMem_preserves (regs : (Nat -> Nat)) (m : (Nat -> Nat)) (i : MirMemInst) :
    @Eq.{1} (Nat -> Nat) (stepMemIr regs m (lowerMemInst i)) (stepMemMir regs m i) :=
  @MirMemInst.casesOn
    (fun ii => @Eq.{1} (Nat -> Nat) (stepMemIr regs m (lowerMemInst ii)) (stepMemMir regs m ii)) i
    (fun addrReg valReg => rfl)
    rfl
theorem stepMem_raise_preserves (regs : (Nat -> Nat)) (m : (Nat -> Nat)) (i : IrMemInst) :
    @Eq.{1} (Nat -> Nat) (stepMemMir regs m (raiseMemInst i)) (stepMemIr regs m i) :=
  @IrMemInst.casesOn
    (fun ii => @Eq.{1} (Nat -> Nat) (stepMemMir regs m (raiseMemInst ii)) (stepMemIr regs m ii)) i
    (fun addrReg valReg => rfl)
    rfl

-- A straight-line memory block (sequence of memory instructions).
inductive IrMemBlock where
  | mbnil
  | mbcons (i : IrMemInst) (rest : IrMemBlock)
inductive MirMemBlock where
  | mmbnil
  | mmbcons (i : MirMemInst) (rest : MirMemBlock)

-- Evaluate a memory block: thread the memory forward through the stores, with a
-- fixed register file (accumulator-passing recursor -> left fold).
def evalMemIr (regs : (Nat -> Nat)) (b : IrMemBlock) : (Nat -> Nat) -> (Nat -> Nat) :=
  @IrMemBlock.rec.{1} (fun _ => (Nat -> Nat) -> (Nat -> Nat))
    (fun m => m)
    (fun i rest ih => fun m => ih (stepMemIr regs m i))
    b
def evalMemMir (regs : (Nat -> Nat)) (b : MirMemBlock) : (Nat -> Nat) -> (Nat -> Nat) :=
  @MirMemBlock.rec.{1} (fun _ => (Nat -> Nat) -> (Nat -> Nat))
    (fun m => m)
    (fun i rest ih => fun m => ih (stepMemMir regs m i))
    b
def lowerMemBlock (b : MirMemBlock) : IrMemBlock :=
  @MirMemBlock.rec (fun _ => IrMemBlock)
    IrMemBlock.mbnil
    (fun i rest ih => IrMemBlock.mbcons (lowerMemInst i) ih)
    b
def raiseMemBlock (b : IrMemBlock) : MirMemBlock :=
  @IrMemBlock.rec (fun _ => MirMemBlock)
    MirMemBlock.mmbnil
    (fun i rest ih => MirMemBlock.mmbcons (raiseMemInst i) ih)
    b

theorem evalMemIr_nil (regs : (Nat -> Nat)) (m : (Nat -> Nat)) :
    @Eq.{1} (Nat -> Nat) (evalMemIr regs IrMemBlock.mbnil m) m := rfl
theorem evalMemIr_cons (regs : (Nat -> Nat)) (i : IrMemInst) (rest : IrMemBlock) (m : (Nat -> Nat)) :
    @Eq.{1} (Nat -> Nat) (evalMemIr regs (IrMemBlock.mbcons i rest) m)
      (evalMemIr regs rest (stepMemIr regs m i)) := rfl

-- WHOLE-BLOCK memory correspondence: lowering a MIR straight-line memory block
-- to trust-ir preserves the final memory, on any starting memory and register
-- file, BOTH directions (structural induction; head via `stepMem_preserves`,
-- tail via the IH).
theorem lowerMemBlock_preserves (regs : (Nat -> Nat)) (b : MirMemBlock) :
    forall (m : (Nat -> Nat)),
      @Eq.{1} (Nat -> Nat) (evalMemIr regs (lowerMemBlock b) m) (evalMemMir regs b m) :=
  @MirMemBlock.rec
    (fun b => forall (m : (Nat -> Nat)),
      @Eq.{1} (Nat -> Nat) (evalMemIr regs (lowerMemBlock b) m) (evalMemMir regs b m))
    (fun m => rfl)
    (fun i rest ih => fun m =>
      Eq.trans
        (congrArg (evalMemIr regs (lowerMemBlock rest)) (stepMem_preserves regs m i))
        (ih (stepMemMir regs m i)))
    b
theorem raiseMemBlock_preserves (regs : (Nat -> Nat)) (b : IrMemBlock) :
    forall (m : (Nat -> Nat)),
      @Eq.{1} (Nat -> Nat) (evalMemMir regs (raiseMemBlock b) m) (evalMemIr regs b m) :=
  @IrMemBlock.rec
    (fun b => forall (m : (Nat -> Nat)),
      @Eq.{1} (Nat -> Nat) (evalMemMir regs (raiseMemBlock b) m) (evalMemIr regs b m))
    (fun m => rfl)
    (fun i rest ih => fun m =>
      Eq.trans
        (congrArg (evalMemMir regs (raiseMemBlock rest)) (stepMem_raise_preserves regs m i))
        (ih (stepMemIr regs m i)))
    b

-- ============================================================================
-- CARRIER SOUNDNESS: every wrapping op lands back in `[0, 2^w)`.
-- ============================================================================
-- Each wrapping op (irBinOp add/sub/mul, irTrunc, irLShr, irOvResult add) is
-- DEFINITIONALLY `SOMETHING % (2^w)`, so its result is `< 2^w` by `mod_lt`
-- applied with the strict positivity of the width modulus (`two_pow_pos`).
-- This is newly axiom-free because `Nat.mod` is now a real structural
-- definition (`Nat.modCore`, fuel-recursive); the Nat sub/order lemmas absent
-- from `with_prelude` are self-proved below by `@Nat.rec` induction.
-- These helpers are copied verbatim from `nat_mod_lt_e2e.rs` (which proves
-- exactly these facts down to the foundational axioms).

-- `a <= 0 -> a = 0`.  Case on `a` via @Nat.rec.  The equation in the motive is
-- parenthesized so `->` and `=` do not mis-associate.
theorem le_zero (a : Nat) (h : Nat.le a 0) : a = Nat.zero :=
  @Nat.rec
    (fun k => Nat.le k 0 -> (k = Nat.zero))
    (fun _h0 => rfl)
    (fun a' _ih hs =>
      @False.elim (Nat.succ a' = Nat.zero) (Nat.not_succ_le_zero a' hs))
    a
    h

-- `succ x - succ m = x - m`, by induction on `m`.
theorem succ_sub_succ (x m : Nat) : Nat.sub (Nat.succ x) (Nat.succ m) = Nat.sub x m :=
  @Nat.rec
    (fun k => Nat.sub (Nat.succ x) (Nat.succ k) = Nat.sub x k)
    rfl
    (fun j ih => congrArg Nat.pred ih)
    m

-- `0 - m = 0`, by induction on `m`.
theorem zero_sub (m : Nat) : Nat.sub 0 m = 0 :=
  @Nat.rec
    (fun k => Nat.sub 0 k = 0)
    rfl
    (fun j ih => congrArg Nat.pred ih)
    m

-- `0 < n - a  ->  a < n`, in the stronger generalized-over-`n` form.
theorem sub_pos_lt (a n : Nat) (h : Nat.lt 0 (Nat.sub n a)) : Nat.lt a n :=
  @Nat.rec
    (fun k => forall (m : Nat), Nat.lt 0 (Nat.sub m k) -> Nat.lt k m)
    (fun m hm => hm)
    (fun a' ih =>
      fun m =>
        @Nat.rec
          (fun mm => Nat.lt 0 (Nat.sub mm (Nat.succ a')) -> Nat.lt (Nat.succ a') mm)
          (fun h0 =>
            @False.elim (Nat.lt (Nat.succ a') Nat.zero)
              (Nat.not_succ_le_zero Nat.zero
                (@Eq.subst Nat (fun z => Nat.lt 0 z) (Nat.sub Nat.zero (Nat.succ a')) Nat.zero
                  (zero_sub (Nat.succ a')) h0)))
          (fun n' _ihn hn =>
            @Nat.succ_le_succ (Nat.succ a') n'
              (ih n'
                (@Eq.subst Nat (fun z => Nat.lt 0 z)
                  (Nat.sub (Nat.succ n') (Nat.succ a')) (Nat.sub n' a')
                  (succ_sub_succ n' a') hn)))
          m)
    a
    n
    h

-- The decrease bound for the recursive call: `a <= succ f -> 0 < n -> a - n <= f`.
theorem key (a n f : Nat) (ha : Nat.le a (Nat.succ f)) (hn : Nat.lt 0 n) :
    Nat.le (Nat.sub a n) f :=
  @Nat.rec
    (fun nn => Nat.lt 0 nn -> Nat.le (Nat.sub a nn) f)
    (fun h0 =>
      @False.elim (Nat.le (Nat.sub a Nat.zero) f) (Nat.not_succ_le_zero Nat.zero h0))
    (fun m _ihn _hsm =>
      @Nat.rec
        (fun aa => Nat.le aa (Nat.succ f) -> Nat.le (Nat.sub aa (Nat.succ m)) f)
        (fun _haa =>
          @Eq.subst Nat (fun z => Nat.le z f) Nat.zero (Nat.sub Nat.zero (Nat.succ m))
            (Eq.symm (zero_sub (Nat.succ m))) (Nat.zero_le f))
        (fun a' _iha haa =>
          @Eq.subst Nat (fun z => Nat.le z f)
            (Nat.sub a' m) (Nat.sub (Nat.succ a') (Nat.succ m))
            (Eq.symm (succ_sub_succ a' m))
            (@Nat.le_trans (Nat.sub a' m) a' f
              (Nat.sub_le a' m)
              (Nat.le_of_succ_le_succ a' f haa)))
        a
        ha)
    n
    hn

-- The fuel-induction core: `modCore` is bounded by the modulus.
-- The threaded equation is written `@Eq Nat ...` / `@Eq.refl Nat ...` so the
-- recursor motive carries no unsolved level metavariables.
theorem modCore_lt (fuel : Nat) :
    forall (a n : Nat), Nat.le a fuel -> Nat.lt 0 n -> Nat.lt (Nat.modCore fuel a n) n :=
  @Nat.rec
    (fun f => forall (a n : Nat), Nat.le a f -> Nat.lt 0 n -> Nat.lt (Nat.modCore f a n) n)
    (fun a n ha hn =>
      @Eq.subst Nat (fun z => Nat.lt z n) Nat.zero a (Eq.symm (le_zero a ha)) hn)
    (fun f ih =>
      fun a n ha hn =>
        @Nat.rec
          (fun s =>
            (@Eq Nat (Nat.sub n a) s) ->
              Nat.lt
                (@Nat.rec (fun _ => Nat) (Nat.modCore f (Nat.sub a n) n) (fun _ _ => a) s)
                n)
          (fun _heq => ih (Nat.sub a n) n (key a n f ha hn) hn)
          (fun k _ihk heq =>
            sub_pos_lt a n
              (@Eq.subst Nat (fun z => Nat.lt 0 z) (Nat.succ k) (Nat.sub n a)
                (Eq.symm heq) (Nat.zero_lt_succ k)))
          (Nat.sub n a)
          (@Eq.refl Nat (Nat.sub n a)))
    fuel

-- `Nat.mod a n < n` whenever `0 < n`.
theorem mod_lt (a n : Nat) (h : Nat.lt 0 n) : Nat.lt (Nat.mod a n) n :=
  modCore_lt a a n (Nat.le_refl a) h

-- `0 < a -> 0 < b -> 0 < a * b`, by @Nat.rec on `b`.
theorem nmul_pos (a b : Nat) : Nat.lt 0 a -> Nat.lt 0 b -> Nat.lt 0 (Nat.mul a b) :=
  fun ha hb =>
    @Nat.rec
      (fun k => Nat.lt 0 k -> Nat.lt 0 (Nat.mul a k))
      (fun h0 => @False.elim (Nat.lt 0 (Nat.mul a 0)) (Nat.lt_irrefl 0 h0))
      (fun j _ih _hsj =>
        @Nat.le_trans 1 (Nat.succ (Nat.mul a j)) (Nat.add (Nat.mul a j) a)
          (@Nat.succ_le_succ 0 (Nat.mul a j) (Nat.zero_le (Nat.mul a j)))
          (Nat.add_le_add_left 1 a ha (Nat.mul a j)))
      b hb

-- `0 < 2 ^ w` at every width, by @Nat.rec on `w`.
theorem two_pow_pos (w : Nat) : Nat.lt 0 (Nat.pow 2 w) :=
  @Nat.rec
    (fun k => Nat.lt 0 (Nat.pow 2 k))
    (Nat.le_refl 1)
    (fun k ih => nmul_pos (Nat.pow 2 k) 2 ih (@Nat.succ_le_succ 0 1 (Nat.zero_le 1)))
    w

-- The six carrier-soundness theorems.  Each goal `Nat.lt (op ...) (Nat.pow 2 w)`
-- is defeq to `Nat.lt (UNDERLYING % (2^w)) (2^w)`, an instance of `mod_lt`.
theorem irBinOp_add_in_range (w a b : Nat) :
    Nat.lt (irBinOp IrOp.iadd w a b) (Nat.pow 2 w) :=
  mod_lt (Nat.add a b) (Nat.pow 2 w) (two_pow_pos w)

theorem irBinOp_sub_in_range (w a b : Nat) :
    Nat.lt (irBinOp IrOp.isub w a b) (Nat.pow 2 w) :=
  mod_lt (Nat.add a (Nat.sub (Nat.pow 2 w) (Nat.mod b (Nat.pow 2 w)))) (Nat.pow 2 w) (two_pow_pos w)

theorem irBinOp_mul_in_range (w a b : Nat) :
    Nat.lt (irBinOp IrOp.imul w a b) (Nat.pow 2 w) :=
  mod_lt (Nat.mul a b) (Nat.pow 2 w) (two_pow_pos w)

theorem irTrunc_in_range (w a : Nat) :
    Nat.lt (irTrunc w a) (Nat.pow 2 w) :=
  mod_lt a (Nat.pow 2 w) (two_pow_pos w)

theorem irLShr_in_range (w a k : Nat) :
    Nat.lt (irLShr w a k) (Nat.pow 2 w) :=
  mod_lt (Nat.div a (Nat.pow 2 k)) (Nat.pow 2 w) (two_pow_pos w)

theorem irOvResult_add_in_range (w a b : Nat) :
    Nat.lt (irOvResult IrOvOp.ovadd w a b) (Nat.pow 2 w) :=
  mod_lt (Nat.add a b) (Nat.pow 2 w) (two_pow_pos w)


-- ===========================================================================
-- THE UNIFIED MACHINE: one addressable store `S : Nat -> Nat` on which a mixed
-- instruction stream (arithmetic + indirect load/store) runs -- the von-Neumann
-- view where registers and memory cells share one address space. This UNIFIES
-- the register and memory dimensions into a single machine-state correspondence:
-- lowering a whole MIR machine program to trust-ir preserves the ENTIRE store
-- through execution, on any starting store, both directions, to the 3 axioms.
--   uArith dst s1 s2 w op : S[dst]      <- binop(w, S[s1], S[s2])
--   uLoad  dst addrReg    : S[dst]      <- S[S[addrReg]]      (indirect load)
--   uStore addrReg valReg : S[S[addrReg]] <- S[valReg]        (indirect store)
--   uNop                  : S unchanged
-- ===========================================================================
inductive IrMachInst where
  | uArithIr (dst : Nat) (src1 : Nat) (src2 : Nat) (width : Nat) (op : IrOp)
  | uLoadIr (dst : Nat) (addrReg : Nat)
  | uStoreIr (addrReg : Nat) (valReg : Nat)
  | uNopIr
inductive MirMachInst where
  | uArithMir (dst : Nat) (src1 : Nat) (src2 : Nat) (width : Nat) (op : MirOp)
  | uLoadMir (dst : Nat) (addrReg : Nat)
  | uStoreMir (addrReg : Nat) (valReg : Nat)
  | uNopMir

-- Execute one instruction against the store (writeReg is the addressable store
-- update -- a write at `addr` leaving every other cell untouched).
def stepMachIr (s : (Nat -> Nat)) (i : IrMachInst) : (Nat -> Nat) :=
  @IrMachInst.casesOn.{1} (fun _ => (Nat -> Nat)) i
    (fun dst src1 src2 width op => writeReg s dst (irBinOp op width (s src1) (s src2)))
    (fun dst addrReg => writeReg s dst (s (s addrReg)))
    (fun addrReg valReg => writeReg s (s addrReg) (s valReg))
    s
def stepMachMir (s : (Nat -> Nat)) (i : MirMachInst) : (Nat -> Nat) :=
  @MirMachInst.casesOn.{1} (fun _ => (Nat -> Nat)) i
    (fun dst src1 src2 width op => writeReg s dst (mirBinOp op width (s src1) (s src2)))
    (fun dst addrReg => writeReg s dst (s (s addrReg)))
    (fun addrReg valReg => writeReg s (s addrReg) (s valReg))
    s

def lowerMachInst (i : MirMachInst) : IrMachInst :=
  @MirMachInst.casesOn (fun _ => IrMachInst) i
    (fun dst src1 src2 width op => IrMachInst.uArithIr dst src1 src2 width (lowerOp op))
    (fun dst addrReg => IrMachInst.uLoadIr dst addrReg)
    (fun addrReg valReg => IrMachInst.uStoreIr addrReg valReg)
    IrMachInst.uNopIr
def raiseMachInst (i : IrMachInst) : MirMachInst :=
  @IrMachInst.casesOn (fun _ => MirMachInst) i
    (fun dst src1 src2 width op => MirMachInst.uArithMir dst src1 src2 width (raiseOp op))
    (fun dst addrReg => MirMachInst.uLoadMir dst addrReg)
    (fun addrReg valReg => MirMachInst.uStoreMir addrReg valReg)
    MirMachInst.uNopMir

-- PER-INSTRUCTION machine-state correspondence (both directions): the arithmetic
-- case agrees by `lowerOp_preserves_binop` (the write value), and the load/store/
-- nop cases are structurally identical after lowering.
theorem stepMach_preserves (s : (Nat -> Nat)) (i : MirMachInst) :
    @Eq.{1} (Nat -> Nat) (stepMachIr s (lowerMachInst i)) (stepMachMir s i) :=
  @MirMachInst.casesOn
    (fun ii => @Eq.{1} (Nat -> Nat) (stepMachIr s (lowerMachInst ii)) (stepMachMir s ii)) i
    (fun dst src1 src2 width op =>
      congrArg (writeReg s dst) (lowerOp_preserves_binop op width (s src1) (s src2)))
    (fun dst addrReg => rfl)
    (fun addrReg valReg => rfl)
    rfl
theorem stepMach_raise_preserves (s : (Nat -> Nat)) (i : IrMachInst) :
    @Eq.{1} (Nat -> Nat) (stepMachMir s (raiseMachInst i)) (stepMachIr s i) :=
  @IrMachInst.casesOn
    (fun ii => @Eq.{1} (Nat -> Nat) (stepMachMir s (raiseMachInst ii)) (stepMachIr s ii)) i
    (fun dst src1 src2 width op =>
      congrArg (writeReg s dst) (raiseOp_preserves_binop op width (s src1) (s src2)))
    (fun dst addrReg => rfl)
    (fun addrReg valReg => rfl)
    rfl

-- A machine PROGRAM is a straight-line instruction list.
inductive IrMachBlock where
  | umbnil
  | umbcons (i : IrMachInst) (rest : IrMachBlock)
inductive MirMachBlock where
  | ummbnil
  | ummbcons (i : MirMachInst) (rest : MirMachBlock)

def evalMachIr (b : IrMachBlock) : (Nat -> Nat) -> (Nat -> Nat) :=
  @IrMachBlock.rec.{1} (fun _ => (Nat -> Nat) -> (Nat -> Nat))
    (fun s => s)
    (fun i rest ih => fun s => ih (stepMachIr s i))
    b
def evalMachMir (b : MirMachBlock) : (Nat -> Nat) -> (Nat -> Nat) :=
  @MirMachBlock.rec.{1} (fun _ => (Nat -> Nat) -> (Nat -> Nat))
    (fun s => s)
    (fun i rest ih => fun s => ih (stepMachMir s i))
    b
def lowerMachBlock (b : MirMachBlock) : IrMachBlock :=
  @MirMachBlock.rec (fun _ => IrMachBlock)
    IrMachBlock.umbnil
    (fun i rest ih => IrMachBlock.umbcons (lowerMachInst i) ih)
    b
def raiseMachBlock (b : IrMachBlock) : MirMachBlock :=
  @IrMachBlock.rec (fun _ => MirMachBlock)
    MirMachBlock.ummbnil
    (fun i rest ih => MirMachBlock.ummbcons (raiseMachInst i) ih)
    b

theorem evalMachIr_nil (s : (Nat -> Nat)) :
    @Eq.{1} (Nat -> Nat) (evalMachIr IrMachBlock.umbnil s) s := rfl
theorem evalMachIr_cons (i : IrMachInst) (rest : IrMachBlock) (s : (Nat -> Nat)) :
    @Eq.{1} (Nat -> Nat) (evalMachIr (IrMachBlock.umbcons i rest) s)
      (evalMachIr rest (stepMachIr s i)) := rfl

-- THE WHOLE-PROGRAM MACHINE CORRESPONDENCE: lowering a whole MIR machine program
-- to trust-ir preserves the final store on ANY starting store, BOTH directions
-- (structural induction; head via `stepMach_preserves`, tail via the IH). This
-- is the unified register+memory+arithmetic execution, preserved by lowering.
theorem lowerMachBlock_preserves (b : MirMachBlock) :
    forall (s : (Nat -> Nat)),
      @Eq.{1} (Nat -> Nat) (evalMachIr (lowerMachBlock b) s) (evalMachMir b s) :=
  @MirMachBlock.rec
    (fun b => forall (s : (Nat -> Nat)),
      @Eq.{1} (Nat -> Nat) (evalMachIr (lowerMachBlock b) s) (evalMachMir b s))
    (fun s => rfl)
    (fun i rest ih => fun s =>
      Eq.trans
        (congrArg (evalMachIr (lowerMachBlock rest)) (stepMach_preserves s i))
        (ih (stepMachMir s i)))
    b
theorem raiseMachBlock_preserves (b : IrMachBlock) :
    forall (s : (Nat -> Nat)),
      @Eq.{1} (Nat -> Nat) (evalMachMir (raiseMachBlock b) s) (evalMachIr b s) :=
  @IrMachBlock.rec
    (fun b => forall (s : (Nat -> Nat)),
      @Eq.{1} (Nat -> Nat) (evalMachMir (raiseMachBlock b) s) (evalMachIr b s))
    (fun s => rfl)
    (fun i rest ih => fun s =>
      Eq.trans
        (congrArg (evalMachMir (raiseMachBlock rest)) (stepMach_raise_preserves s i))
        (ih (stepMachIr s i)))
    b

-- ===========================================================================
-- TYPE SOUNDNESS OF THE WRAPPING-ARITHMETIC MACHINE
--
-- The trust-ir / MIR carrier discipline is: every register holds a value that
-- fits its declared width, i.e. `< 2^w`. The wrapping arithmetic ops (`iadd`,
-- `isub`, `imul`) are total functions `Nat -> Nat -> Nat` whose result is always
-- `< 2^w` (they end in `% 2^w`).  This section proves the PROGRESS/PRESERVATION
-- metatheorem: executing a whole block of wrapping-arithmetic instructions
-- preserves the store invariant "every register is in range".  This is the
-- value-level type-soundness statement for the wrapping machine -- a well-typed
-- store stays well-typed under execution, on ANY starting store, all the way
-- down to the foundational axioms.
--
--   storeInRange w s   :=   forall r, s r < 2^w     (the typing invariant)
--   writeReg_inRange   :   writing an in-range value preserves the invariant
--   stepWrap_inRange   :   one instruction preserves the invariant (step soundness)
--   evalWrap_inRange   :   a whole block preserves the invariant (THE metatheorem)
-- ===========================================================================

-- The store-typing invariant: every register currently holds a width-`w` value.
def storeInRange : Nat -> (Nat -> Nat) -> Prop :=
  fun w s => forall (r : Nat), Nat.lt (s r) (Nat.pow 2 w)

-- KEY LEMMA.  Overwriting register `d` with an in-range value `v` keeps the
-- whole store in range: every register `r` is either `d` (now holds `v`, in
-- range by `hv`) or untouched (holds `s r`, in range by `hs r`).  The case split
-- is the dependent-motive `Bool.casesOn` on `Nat.beq r d`; `writeReg s d v r`
-- is def-eq to `@Bool.casesOn (fun _ => Nat) (Nat.beq r d) (s r) v` (false-case
-- `s r`, true-case `v`, confirmed by the reduction of `writeReg`'s match).
theorem writeReg_inRange (w : Nat) (s : (Nat -> Nat)) (d v : Nat)
    (hs : storeInRange w s) (hv : Nat.lt v (Nat.pow 2 w)) :
    storeInRange w (writeReg s d v) :=
  fun r =>
    @Bool.casesOn
      (fun b => Nat.lt (@Bool.casesOn (fun _ => Nat) b (s r) v) (Nat.pow 2 w))
      (Nat.beq r d)
      (hs r)
      hv

-- A 3-constructor wrapping-op tag (add/sub/mul); the bitwise ops are excluded
-- because their in-range characterization needs separate lemmas -- here we want
-- the cleanest possible "every op result is `< 2^w` by `mod_lt`" story.
inductive WrapOp where
  | wadd : WrapOp
  | wsub : WrapOp
  | wmul : WrapOp

-- The value of a wrapping op at width `w`, matching irBinOp's wrapping cases
-- (Add = `(a+b)%2^w`, Sub = `(a + (2^w - b%2^w))%2^w`, Mul = `(a*b)%2^w`).
def wrapBinOp : WrapOp -> Nat -> Nat -> Nat -> Nat := fun op w a b =>
  @WrapOp.casesOn (fun _ => Nat) op
    ((a + b) % (2 ^ w))
    ((a + (2 ^ w - b % (2 ^ w))) % (2 ^ w))
    ((a * b) % (2 ^ w))

-- The wrapping cases of wrapBinOp coincide with irBinOp (faithfulness: this is
-- the same machine arithmetic the audited correspondence section reasons about).
theorem wrapBinOp_add_eq (w a b : Nat) : @Eq Nat (wrapBinOp WrapOp.wadd w a b) (irBinOp IrOp.iadd w a b) := rfl
theorem wrapBinOp_sub_eq (w a b : Nat) : @Eq Nat (wrapBinOp WrapOp.wsub w a b) (irBinOp IrOp.isub w a b) := rfl
theorem wrapBinOp_mul_eq (w a b : Nat) : @Eq Nat (wrapBinOp WrapOp.wmul w a b) (irBinOp IrOp.imul w a b) := rfl

-- Every wrapping op result is in range: each case ends in `% 2^w`, so it is an
-- instance of `mod_lt` with the strictly-positive modulus `two_pow_pos`.
theorem wrapBinOp_in_range (op : WrapOp) (w a b : Nat) :
    Nat.lt (wrapBinOp op w a b) (Nat.pow 2 w) :=
  @WrapOp.casesOn
    (fun o => Nat.lt (wrapBinOp o w a b) (Nat.pow 2 w))
    op
    (mod_lt (Nat.add a b) (Nat.pow 2 w) (two_pow_pos w))
    (mod_lt (Nat.add a (Nat.sub (Nat.pow 2 w) (Nat.mod b (Nat.pow 2 w)))) (Nat.pow 2 w) (two_pow_pos w))
    (mod_lt (Nat.mul a b) (Nat.pow 2 w) (two_pow_pos w))

-- A wrapping-arithmetic instruction: `dst <- wrapBinOp op w (s src1) (s src2)`,
-- plus a no-op.  Two constructors keep WrapInst a genuine inductive (not a
-- single-constructor structure with definitional projections).
inductive WrapInst where
  | wmk (dst : Nat) (src1 : Nat) (src2 : Nat) (op : WrapOp)
  | wnop

-- Execute one wrapping instruction at width `w` against the store.
def stepWrap (w : Nat) (s : (Nat -> Nat)) (i : WrapInst) : (Nat -> Nat) :=
  @WrapInst.casesOn.{1} (fun _ => (Nat -> Nat)) i
    (fun dst src1 src2 op => writeReg s dst (wrapBinOp op w (s src1) (s src2)))
    s

-- STEP SOUNDNESS: one wrapping instruction preserves the store invariant.  The
-- arithmetic case writes an in-range value (`wrapBinOp_in_range`) so the store
-- stays in range (`writeReg_inRange`); the no-op leaves the store unchanged.
theorem stepWrap_inRange (w : Nat) (s : (Nat -> Nat)) (i : WrapInst)
    (hs : storeInRange w s) :
    storeInRange w (stepWrap w s i) :=
  @WrapInst.casesOn
    (fun i => storeInRange w (stepWrap w s i))
    i
    (fun dst src1 src2 op =>
      writeReg_inRange w s dst (wrapBinOp op w (s src1) (s src2)) hs
        (wrapBinOp_in_range op w (s src1) (s src2)))
    hs

-- A basic block of wrapping instructions (cons-list).
inductive WrapBlock where
  | wbnil
  | wbcons (i : WrapInst) (rest : WrapBlock)

-- Evaluate a wrapping block: thread the store forward through the instructions
-- (accumulator-passing recursor -> genuine left fold, i1 before i2 before ...).
def evalWrap (w : Nat) (b : WrapBlock) : (Nat -> Nat) -> (Nat -> Nat) :=
  @WrapBlock.rec.{1} (fun _ => (Nat -> Nat) -> (Nat -> Nat))
    (fun s => s)
    (fun i rest ih => fun s => ih (stepWrap w s i))
    b

-- Block-evaluation reduction lemmas (iota-reduction of the recursor; rfl).
theorem evalWrap_nil (w : Nat) (s : (Nat -> Nat)) :
    @Eq.{1} (Nat -> Nat) (evalWrap w WrapBlock.wbnil s) s := rfl
theorem evalWrap_cons (w : Nat) (i : WrapInst) (rest : WrapBlock) (s : (Nat -> Nat)) :
    @Eq.{1} (Nat -> Nat) (evalWrap w (WrapBlock.wbcons i rest) s) (evalWrap w rest (stepWrap w s i)) := rfl

-- THE TYPE-SOUNDNESS METATHEOREM.  Running a WHOLE wrapping-arithmetic block on
-- any in-range store yields an in-range store: the typing invariant
-- `storeInRange w` is preserved by execution of an arbitrary wrapping program.
-- Proven by structural induction on the block: nil leaves the store untouched
-- (the hypothesis carries through); cons runs the head step (in range by
-- `stepWrap_inRange`) then the tail by the induction hypothesis.
theorem evalWrap_inRange (w : Nat) (b : WrapBlock) :
    forall (s : (Nat -> Nat)), storeInRange w s -> storeInRange w (evalWrap w b s) :=
  @WrapBlock.rec
    (fun b => forall (s : (Nat -> Nat)), storeInRange w s -> storeInRange w (evalWrap w b s))
    (fun s hs => hs)
    (fun i rest ih => fun s hs => ih (stepWrap w s i) (stepWrap_inRange w s i hs))
    b

-- ===========================================================================
-- PROOF-CARRYING / OBLIGATION-DISCHARGE SLICE.
--
-- The heart of proof-carrying code: when a trust-ir SAFETY OBLIGATION holds,
-- the WRAPPING op equals REAL arithmetic. The `noOverflow` obligation for
-- `iadd`/`imul` at width `w` is `a + b < 2^w` (resp. `a * b < 2^w`). We prove
-- that under that obligation the wrapping result `(a+b) % 2^w` (which is
-- DEFINITIONALLY what `irBinOp IrOp.iadd w a b` computes) equals the exact
-- `a + b` -- i.e. the modulus never fires, so there is no wraparound and no
-- information loss. The obligation discharges to exact semantics.
--
-- The substance is `mod_eq_of_lt : a < n -> a % n = a`, proven through the
-- real fuel-recursive `Nat.modCore` definition (no `Nat.mod_*` prelude lemmas
-- are assumed). We reuse the self-proved Nat sub/order lemmas above
-- (`succ_sub_succ`, `zero_sub`) and the threaded case-split pattern from
-- `modCore_lt`.
-- ===========================================================================

-- Forward direction of the sub/order correspondence: `a < n -> 0 < n - a`.
-- (The converse `sub_pos_lt` is proved above; this is the direction the
-- obligation-discharge proof needs.)  Double @Nat.rec: outer on `a`
-- (generalized over the modulus-side `m`), inner on `m`.
theorem lt_sub_pos (a n : Nat) (h : Nat.lt a n) : Nat.lt 0 (Nat.sub n a) :=
  @Nat.rec
    (fun k => forall (m : Nat), Nat.lt k m -> Nat.lt 0 (Nat.sub m k))
    (fun m hm => hm)
    (fun a' ih =>
      fun m =>
        @Nat.rec
          (fun mm => Nat.lt (Nat.succ a') mm -> Nat.lt 0 (Nat.sub mm (Nat.succ a')))
          (fun h0 =>
            @False.elim (Nat.lt 0 (Nat.sub Nat.zero (Nat.succ a')))
              (Nat.not_succ_le_zero (Nat.succ a') h0))
          (fun n' _ihn hn =>
            @Eq.subst Nat (fun z => Nat.lt 0 z) (Nat.sub n' a')
              (Nat.sub (Nat.succ n') (Nat.succ a'))
              (Eq.symm (succ_sub_succ n' a'))
              (ih n' (Nat.le_of_succ_le_succ (Nat.succ a') n' hn)))
          m)
    a
    n
    h

-- The fuel-induction core for obligation discharge: when `a < n`, the modulus
-- never fires, so `modCore fuel a n = a` at ANY fuel.  The threaded equation
-- `@Eq Nat (Nat.sub n a) s` lets the inner `Nat.rec` (which switches on
-- `n - a`) reduce: `a < n` forces `n - a = succ k` (by `lt_sub_pos`), so the
-- inner rec takes the SUCC branch (`fun _ _ => a`) and the whole expression is
-- `a`.  Reflexivity on the threading variable closes it.
theorem modCore_eq_of_lt (fuel : Nat) :
    forall (a n : Nat), Nat.lt a n -> @Eq Nat (Nat.modCore fuel a n) a :=
  @Nat.rec
    (fun f => forall (a n : Nat), Nat.lt a n -> @Eq Nat (Nat.modCore f a n) a)
    (fun a n _h => @Eq.refl Nat a)
    (fun f _ih =>
      fun a n h =>
        @Nat.rec
          (fun s =>
            (@Eq Nat (Nat.sub n a) s) ->
              @Eq Nat
                (@Nat.rec (fun _ => Nat) (Nat.modCore f (Nat.sub a n) n) (fun _ _ => a) s)
                a)
          (fun heq =>
            @False.elim
              (@Eq Nat
                (@Nat.rec (fun _ => Nat) (Nat.modCore f (Nat.sub a n) n) (fun _ _ => a) Nat.zero)
                a)
              (Nat.not_succ_le_zero Nat.zero
                (@Eq.subst Nat (fun z => Nat.lt 0 z) (Nat.sub n a) Nat.zero heq
                  (lt_sub_pos a n h))))
          (fun k _ihk _heq => @Eq.refl Nat a)
          (Nat.sub n a)
          (@Eq.refl Nat (Nat.sub n a)))
    fuel

-- `a % n = a` when `a < n` -- the modulus does not fire.  `Nat.mod a n` is
-- DEFINITIONALLY `Nat.modCore a a n`, so this is `modCore_eq_of_lt` at fuel `a`.
theorem mod_eq_of_lt (a n : Nat) (h : Nat.lt a n) : @Eq Nat (Nat.mod a n) a :=
  modCore_eq_of_lt a a n h

-- ===========================================================================
-- HEADLINE OBLIGATION-DISCHARGE THEOREMS (proof-carrying code).
--
-- `irBinOp IrOp.iadd w a b` is DEFINITIONALLY `Nat.mod (Nat.add a b) (Nat.pow 2 w)`
-- (and similarly `imul` for `Nat.mul`).  So if the `noOverflow` obligation
-- `a + b < 2^w` (resp. `a * b < 2^w`) holds, the wrapping op equals exact
-- arithmetic: the safety obligation discharges to exact integer semantics.
-- ===========================================================================
theorem noOverflow_add (w a b : Nat) (h : Nat.lt (Nat.add a b) (Nat.pow 2 w)) :
    @Eq Nat (irBinOp IrOp.iadd w a b) (Nat.add a b) :=
  mod_eq_of_lt (Nat.add a b) (Nat.pow 2 w) h

theorem noOverflow_mul (w a b : Nat) (h : Nat.lt (Nat.mul a b) (Nat.pow 2 w)) :
    @Eq Nat (irBinOp IrOp.imul w a b) (Nat.mul a b) :=
  mod_eq_of_lt (Nat.mul a b) (Nat.pow 2 w) h


-- ===========================================================================
-- THE FULL VON-NEUMANN MACHINE IS TYPE-SOUND.  Extends the wrapping-arithmetic
-- soundness above to the complete machine: wrapping arithmetic PLUS indirect
-- load/store on one addressable store.  The memory ops just MOVE in-range values
-- -- a load copies `s[s[addr]]` (some existing cell, in range by the invariant)
-- into `dst`; a store copies `s[val]` (in range) into `s[addr]` -- so they
-- preserve `storeInRange` exactly like the wrapping arithmetic does.  Hence a
-- WHOLE machine program (arith + memory) keeps every register in `[0, 2^w)`.
-- ===========================================================================
inductive SafeInst where
  | smArith (dst : Nat) (src1 : Nat) (src2 : Nat) (op : WrapOp)
  | smLoad (dst : Nat) (addrReg : Nat)
  | smStore (addrReg : Nat) (valReg : Nat)
  | smNop

def stepSafe (w : Nat) (s : (Nat -> Nat)) (i : SafeInst) : (Nat -> Nat) :=
  @SafeInst.casesOn.{1} (fun _ => (Nat -> Nat)) i
    (fun dst src1 src2 op => writeReg s dst (wrapBinOp op w (s src1) (s src2)))
    (fun dst addrReg => writeReg s dst (s (s addrReg)))
    (fun addrReg valReg => writeReg s (s addrReg) (s valReg))
    s

-- STEP SOUNDNESS for the full machine: every instruction writes an in-range
-- value -- arithmetic by `wrapBinOp_in_range`, load by `hs (s addrReg)` (the
-- loaded cell is in range), store by `hs valReg` (the stored value is in range).
theorem stepSafe_inRange (w : Nat) (s : (Nat -> Nat)) (i : SafeInst)
    (hs : storeInRange w s) :
    storeInRange w (stepSafe w s i) :=
  @SafeInst.casesOn
    (fun i => storeInRange w (stepSafe w s i))
    i
    (fun dst src1 src2 op =>
      writeReg_inRange w s dst (wrapBinOp op w (s src1) (s src2)) hs
        (wrapBinOp_in_range op w (s src1) (s src2)))
    (fun dst addrReg => writeReg_inRange w s dst (s (s addrReg)) hs (hs (s addrReg)))
    (fun addrReg valReg => writeReg_inRange w s (s addrReg) (s valReg) hs (hs valReg))
    hs

inductive SafeBlock where
  | sbnil
  | sbcons (i : SafeInst) (rest : SafeBlock)

def evalSafe (w : Nat) (b : SafeBlock) : (Nat -> Nat) -> (Nat -> Nat) :=
  @SafeBlock.rec.{1} (fun _ => (Nat -> Nat) -> (Nat -> Nat))
    (fun s => s)
    (fun i rest ih => fun s => ih (stepSafe w s i))
    b

-- THE FULL-MACHINE TYPE-SOUNDNESS METATHEOREM: running a WHOLE program of
-- arithmetic + memory instructions on any in-range store yields an in-range
-- store -- the von-Neumann machine (registers AND memory sharing one address
-- space) maintains its store-typing invariant through arbitrary execution.
theorem evalSafe_inRange (w : Nat) (b : SafeBlock) :
    forall (s : (Nat -> Nat)), storeInRange w s -> storeInRange w (evalSafe w b s) :=
  @SafeBlock.rec
    (fun b => forall (s : (Nat -> Nat)), storeInRange w s -> storeInRange w (evalSafe w b s))
    (fun s hs => hs)
    (fun i rest ih => fun s hs => ih (stepSafe w s i) (stepSafe_inRange w s i hs))
    b

-- ===========================================================================
-- THE PROGRAM-LEVEL PROOF-CARRYING CONTRACT: verified compilation under
-- obligations.  Everything above proves that a wrapping program STAYS in range.
-- This final section proves the stronger, end-to-end guarantee a proof-carrying
-- compiler actually wants: if EVERY overflow obligation of a wrapping program
-- holds along its execution, then the wrapping program computes the EXACT
-- UNBOUNDED-INTEGER result -- byte-for-byte the same store an idealized
-- arbitrary-precision machine would produce.  The modular carrier never loses
-- information when its obligations discharge.
--
-- We use a clean add/mul calculus (`POp`): both ops have a `result < 2^w`
-- obligation that, when met, makes `x % 2^w = x` fire to the exact value via
-- the already-proven `mod_eq_of_lt`.  (Subtraction is excluded: its obligation
-- is no-UNDERFLOW, a different shape; add/mul give the cleanest contract.)
-- ===========================================================================

-- A two-op pure-arithmetic tag: addition and multiplication.
inductive POp where
  | padd
  | pmul

-- EXACT (unbounded-integer) semantics: no wrapping, no modulus.  This is what an
-- arbitrary-precision machine computes.
def exactBinOp : POp -> Nat -> Nat -> Nat :=
  fun op a b => @POp.casesOn (fun _ => Nat) op (Nat.add a b) (Nat.mul a b)

-- WRAPPING (machine) semantics at width `w`: the result modulo `2^w`, exactly
-- the carrier arithmetic `irBinOp` performs.
def wrapPBinOp : POp -> Nat -> Nat -> Nat -> Nat :=
  fun op w a b =>
    @POp.casesOn (fun _ => Nat) op
      ((a + b) % (2 ^ w))
      ((a * b) % (2 ^ w))

-- The bridge between the two carriers: the wrapping op is the exact op reduced
-- mod 2^w.  Both cases are `rfl` after `casesOn` (padd: `(a+b)%2^w` vs
-- `(a+b)%2^w`; pmul: `(a*b)%2^w` vs `(a*b)%2^w`).
theorem wrapPBinOp_eq_mod (op : POp) (w a b : Nat) :
    @Eq Nat (wrapPBinOp op w a b) (Nat.mod (exactBinOp op a b) (Nat.pow 2 w)) :=
  @POp.casesOn
    (fun o => @Eq Nat (wrapPBinOp o w a b) (Nat.mod (exactBinOp o a b) (Nat.pow 2 w)))
    op
    (@Eq.refl Nat (Nat.mod (Nat.add a b) (Nat.pow 2 w)))
    (@Eq.refl Nat (Nat.mod (Nat.mul a b) (Nat.pow 2 w)))

-- A pure-arithmetic instruction: `dst <- op(env[src1], env[src2])`, plus a
-- no-op.  Two constructors keep PInst a genuine inductive (not a structure).
inductive PInst where
  | pmk (dst : Nat) (src1 : Nat) (src2 : Nat) (op : POp)
  | pnop

-- Execute one instruction under EXACT semantics.
def stepExact (s : (Nat -> Nat)) (i : PInst) : (Nat -> Nat) :=
  @PInst.casesOn.{1} (fun _ => (Nat -> Nat)) i
    (fun dst src1 src2 op => writeReg s dst (exactBinOp op (s src1) (s src2)))
    s

-- Execute one instruction under WRAPPING semantics at width `w`.
def stepWrapP (w : Nat) (s : (Nat -> Nat)) (i : PInst) : (Nat -> Nat) :=
  @PInst.casesOn.{1} (fun _ => (Nat -> Nat)) i
    (fun dst src1 src2 op => writeReg s dst (wrapPBinOp op w (s src1) (s src2)))
    s

-- The OVERFLOW OBLIGATION for one instruction at width `w` in store `s`: the
-- EXACT result fits in `w` bits.  (For the no-op there is nothing to discharge,
-- so the obligation is `True`.)
def instOK (w : Nat) (s : (Nat -> Nat)) (i : PInst) : Prop :=
  @PInst.casesOn (fun _ => Prop) i
    (fun dst src1 src2 op => Nat.lt (exactBinOp op (s src1) (s src2)) (Nat.pow 2 w))
    True

-- PER-STEP EXACTNESS (obligation discharge, one instruction): when the
-- instruction's overflow obligation holds, the wrapping step and the exact step
-- produce the SAME store.  Arithmetic case: `wrapPBinOp op w x y` is (by
-- `wrapPBinOp_eq_mod`) `exactBinOp op x y % 2^w`, which equals `exactBinOp op x y`
-- by `mod_eq_of_lt` under the obligation `h`; `congrArg (writeReg s dst)` lifts
-- the value-level equality to the store.  No-op case: both sides are `s` (rfl).
theorem stepOK_exact (w : Nat) (s : (Nat -> Nat)) (i : PInst)
    (h : instOK w s i) :
    @Eq.{1} (Nat -> Nat) (stepWrapP w s i) (stepExact s i) :=
  @PInst.casesOn
    (fun i => instOK w s i -> @Eq.{1} (Nat -> Nat) (stepWrapP w s i) (stepExact s i))
    i
    (fun dst src1 src2 op =>
      fun h =>
        congrArg (writeReg s dst)
          (Eq.trans
            (wrapPBinOp_eq_mod op w (s src1) (s src2))
            (mod_eq_of_lt (exactBinOp op (s src1) (s src2)) (Nat.pow 2 w) h)))
    (fun _h => @Eq.refl (Nat -> Nat) s)
    h

-- A basic block of pure-arithmetic instructions (cons-list).
inductive PBlock where
  | pbnil
  | pbcons (i : PInst) (rest : PBlock)

-- Evaluate a block under EXACT semantics (left fold threading the store).
def evalExact (b : PBlock) : (Nat -> Nat) -> (Nat -> Nat) :=
  @PBlock.rec.{1} (fun _ => (Nat -> Nat) -> (Nat -> Nat))
    (fun s => s)
    (fun i rest ih => fun s => ih (stepExact s i))
    b

-- Evaluate a block under WRAPPING semantics at width `w`.
def evalWrapP (w : Nat) (b : PBlock) : (Nat -> Nat) -> (Nat -> Nat) :=
  @PBlock.rec.{1} (fun _ => (Nat -> Nat) -> (Nat -> Nat))
    (fun s => s)
    (fun i rest ih => fun s => ih (stepWrapP w s i))
    b

-- THE WHOLE-PROGRAM OBLIGATION: every instruction's overflow obligation holds
-- along the WRAPPING execution.  The cons case demands the head obligation in
-- the CURRENT store AND (recursively) every tail obligation in the store AFTER
-- the head wrapping step -- exactly the obligations a proof-carrying compiler
-- discharges in program order.  Motive lands in `Prop` but is function-typed
-- (`(Nat->Nat) -> Prop : Sort 1`), so the recursor takes the `.{1}` motive.
def blockOK (w : Nat) (b : PBlock) : (Nat -> Nat) -> Prop :=
  @PBlock.rec.{1} (fun _ => (Nat -> Nat) -> Prop)
    (fun s => True)
    (fun i rest ih => fun s => And (instOK w s i) (ih (stepWrapP w s i)))
    b

-- THE PROGRAM-LEVEL PROOF-CARRYING THEOREM.  If every overflow obligation of a
-- wrapping program holds along its execution (`blockOK w b s`), then the
-- wrapping program computes the EXACT unbounded-integer result (`evalWrapP w b s
-- = evalExact b s`).  Structural induction on the block:
--   * pbnil: both sides are `s` (rfl); the (`True`) obligation is unused.
--   * pbcons i rest, ih: destructure `hb : And (instOK w s i) (blockOK w rest
--     (stepWrapP w s i))` into the head obligation `h1` (`And.left`) and the
--     tail obligations `h2` (`And.right`).  `stepOK_exact w s i h1` makes the
--     head wrapping step equal the exact step; `ih (stepWrapP w s i) h2` makes
--     the tail wrapping run equal the exact run from that store; `congrArg
--     (evalExact rest)` rewrites the tail's start store to the exact step.
--     Chain with `Eq.trans`:
--       evalWrapP w rest (stepWrapP w s i)
--         =[ih ...]            evalExact rest (stepWrapP w s i)
--         =[congrArg ...]      evalExact rest (stepExact s i).
theorem prog_exact_under_obligations (w : Nat) (b : PBlock) :
    forall (s : (Nat -> Nat)), blockOK w b s ->
      @Eq.{1} (Nat -> Nat) (evalWrapP w b s) (evalExact b s) :=
  @PBlock.rec
    (fun b => forall (s : (Nat -> Nat)), blockOK w b s ->
      @Eq.{1} (Nat -> Nat) (evalWrapP w b s) (evalExact b s))
    (fun s _hb => @Eq.refl (Nat -> Nat) s)
    (fun i rest ih =>
      fun s hb =>
        @Eq.trans (Nat -> Nat)
          (evalWrapP w rest (stepWrapP w s i))
          (evalExact rest (stepWrapP w s i))
          (evalExact rest (stepExact s i))
          (ih (stepWrapP w s i)
            (@And.right (instOK w s i) (blockOK w rest (stepWrapP w s i)) hb))
          (congrArg (evalExact rest)
            (stepOK_exact w s i
              (@And.left (instOK w s i) (blockOK w rest (stepWrapP w s i)) hb))))
    b


-- ===========================================================================
-- trust-cg BACKEND CARRIER SOUNDNESS + PROOF-CARRYING, plus the COMPOSED
-- FULL-PIPELINE results.  Mirrors the trust-ir carrier-soundness
-- (`irBinOp_*_in_range`) and proof-carrying (`noOverflow_*`) theorems onto the
-- trust-cg LIR ops (`cgBinOp`), then composes them through the MIR -> trust-ir
-- -> trust-cg lowering so that a MIR op lowered ALL THE WAY to trust-cg LIR is
-- still in range, and exact under its no-overflow obligation.  All axiom-free:
-- every goal is defeq to an instance of `mod_lt` / `mod_eq_of_lt` already
-- proven above.
-- ===========================================================================

-- (1) trust-cg CARRIER SOUNDNESS.  Each `cgBinOp` result lands in `[0, 2^w)`:
-- the goal is defeq to `Nat.lt (UNDERLYING % 2^w) (2^w)`, an instance of
-- `mod_lt` with the strictly-positive width modulus `two_pow_pos`.  csub's
-- underlying expression mirrors `irBinOp_sub_in_range` exactly.
theorem cgBinOp_add_in_range (w a b : Nat) :
    Nat.lt (cgBinOp CgOp.cadd w a b) (Nat.pow 2 w) :=
  mod_lt (Nat.add a b) (Nat.pow 2 w) (two_pow_pos w)

theorem cgBinOp_sub_in_range (w a b : Nat) :
    Nat.lt (cgBinOp CgOp.csub w a b) (Nat.pow 2 w) :=
  mod_lt (Nat.add a (Nat.sub (Nat.pow 2 w) (Nat.mod b (Nat.pow 2 w)))) (Nat.pow 2 w) (two_pow_pos w)

theorem cgBinOp_mul_in_range (w a b : Nat) :
    Nat.lt (cgBinOp CgOp.cmul w a b) (Nat.pow 2 w) :=
  mod_lt (Nat.mul a b) (Nat.pow 2 w) (two_pow_pos w)

-- (2) trust-cg PROOF-CARRYING.  Under the no-overflow obligation, the wrapping
-- trust-cg op computes the EXACT integer result -- the safety obligation
-- discharges to exact integer semantics.  Defeq to `mod_eq_of_lt`.
theorem cgNoOverflow_add (w a b : Nat) (h : Nat.lt (Nat.add a b) (Nat.pow 2 w)) :
    @Eq Nat (cgBinOp CgOp.cadd w a b) (Nat.add a b) :=
  mod_eq_of_lt (Nat.add a b) (Nat.pow 2 w) h

theorem cgNoOverflow_mul (w a b : Nat) (h : Nat.lt (Nat.mul a b) (Nat.pow 2 w)) :
    @Eq Nat (cgBinOp CgOp.cmul w a b) (Nat.mul a b) :=
  mod_eq_of_lt (Nat.mul a b) (Nat.pow 2 w) h

-- (3) FULL-PIPELINE composed results.  A MIR op lowered ALL THE WAY to trust-cg
-- LIR (`cgBinOp (lowerIrToCg (lowerOp MirOp.m..)) w a b`) is defeq to the bare
-- wrapping expression: `lowerOp` maps `madd -> iadd`, `lowerIrToCg` maps
-- `iadd -> cadd`, and `cadd`'s body is `(a+b) % 2^w` (all defeq via casesOn on
-- constructors).  So in-range is an instance of `mod_lt` and exactness an
-- instance of `mod_eq_of_lt`, directly -- no transport needed.

theorem pipelineAdd_in_range (w a b : Nat) :
    Nat.lt (cgBinOp (lowerIrToCg (lowerOp MirOp.madd)) w a b) (Nat.pow 2 w) :=
  mod_lt (Nat.add a b) (Nat.pow 2 w) (two_pow_pos w)

theorem pipelineMul_in_range (w a b : Nat) :
    Nat.lt (cgBinOp (lowerIrToCg (lowerOp MirOp.mmul)) w a b) (Nat.pow 2 w) :=
  mod_lt (Nat.mul a b) (Nat.pow 2 w) (two_pow_pos w)

theorem pipelineAdd_noOverflow (w a b : Nat) (h : Nat.lt (Nat.add a b) (Nat.pow 2 w)) :
    @Eq Nat (cgBinOp (lowerIrToCg (lowerOp MirOp.madd)) w a b) (Nat.add a b) :=
  mod_eq_of_lt (Nat.add a b) (Nat.pow 2 w) h

theorem pipelineMul_noOverflow (w a b : Nat) (h : Nat.lt (Nat.mul a b) (Nat.pow 2 w)) :
    @Eq Nat (cgBinOp (lowerIrToCg (lowerOp MirOp.mmul)) w a b) (Nat.mul a b) :=
  mod_eq_of_lt (Nat.mul a b) (Nat.pow 2 w) h

-- ===========================================================================
-- A SOUND HOARE LOGIC OVER THE WRAPPING-PROGRAM SEMANTICS.
--
-- This is the reflection of program verification into CIC.  A trust-ir
-- program's specification is a CIC proposition (a predicate on stores); a
-- Hoare triple {P} b {Q} states that running `b` from any `P`-store lands in a
-- `Q`-store.  We define the triple directly over the already-audited wrapping
-- semantics (`evalWrapP`), prove the three STANDARD HOARE RULES sound (skip,
-- sequencing/cons, consequence), and then VERIFY A CONCRETE PROGRAM against a
-- spec.  A kernel-checked proof of the triple IS a certificate that the
-- program meets its spec -- the reflection R : (trust-ir program correctness)
-- => (CIC theorem).  Everything is axiom-free: the rules are pure lambda terms
-- threading `evalWrapP`'s definitional unfolding, and the concrete program
-- discharges through `wrapPBinOp_eq_mod` + `mod_eq_of_lt` + the writeReg
-- read-back.
-- ===========================================================================

-- READ-BACK of a register write: reading `d` right after writing `v` to `d`
-- yields `v`.  `writeReg s d v d` is def-eq to
-- `@Bool.casesOn (fun _ => Nat) (Nat.beq d d) (s d) v` (the `match` in writeReg
-- on `Nat.beq d d`).  Rewriting `Nat.beq d d` to `true` (via the prelude's
-- `Nat.beq_refl d : Nat.beq d d = true`) makes the casesOn pick the true-branch
-- `v`.  We lift the bit-level equality through the casesOn motive `P` with
-- `congrArg`: `P (Nat.beq d d)` def-eq `writeReg s d v d`, `P Bool.true` def-eq
-- `v`, so `congrArg P (Nat.beq_refl d)` has type `writeReg s d v d = v`.
theorem writeReg_same (s : (Nat -> Nat)) (d v : Nat) :
    @Eq Nat (writeReg s d v d) v :=
  congrArg
    (fun (b : Bool) => @Bool.casesOn (fun _ => Nat) b (s d) v)
    (Nat.beq_refl d)

-- A STORE PREDICATE (= a program specification): a proposition about a store.
-- Naming this abbreviation lets the higher-order predicate appear as a plain
-- constant in binder/domain position (the elaborator chokes on a nested
-- `((Nat -> Nat) -> Prop)` arrow used as a binder domain, but not on a named
-- constant).  Its sort is `Type` (`Sort 1`); its inhabitants are the store
-- predicates themselves.
def StorePred : Type := (Nat -> Nat) -> Prop

-- THE HOARE TRIPLE.  `Hoare w P b Q` := running block `b` at width `w` from any
-- store satisfying the precondition `P` produces a store satisfying the
-- postcondition `Q`.  Predicates are `StorePred`; the carrier is the audited
-- wrapping interpreter `evalWrapP`.
--
-- We thread the result store through a NAMED equality witness `s' = evalWrapP w
-- b s` and apply `Q` to the *bound* store `s'` (rather than writing the
-- postcondition as `Q (evalWrapP w b s)` directly).  This is logically
-- identical -- the equality pins `s'` to the computed store -- but keeps every
-- predicate application a `Q`/`P` against a bound variable, which the
-- elaborator handles uniformly.  (The whole body is spelled with explicit
-- `forall (_h : ..)` binders rather than `->` for the same robustness.)
def Hoare (w : Nat) (P : StorePred) (b : PBlock) (Q : StorePred) : Prop :=
  forall (s : (Nat -> Nat)), forall (s' : (Nat -> Nat)),
    forall (_h1 : P s), forall (_h2 : @Eq (Nat -> Nat) s' (evalWrapP w b s)), Q s'

-- SOUND RULE (SKIP).  The empty block satisfies {P} pbnil {P}: `evalWrapP w
-- pbnil s = s` by rfl, so the result store `s'` is (by the threaded equality
-- `h2 : s' = evalWrapP w pbnil s`, def-eq `s' = s`) the unchanged store, and
-- the precondition witness `h1 : P s` transports along `Eq.symm h2 : s = s'`
-- to `P s'` via `Eq.subst` with motive `P`.
theorem hoare_skip (w : Nat) (P : StorePred) :
    Hoare w P PBlock.pbnil P :=
  fun s s' h1 h2 => @Eq.subst (Nat -> Nat) P s s' (Eq.symm h2) h1

-- SOUND RULE (SEQUENCING / CONS).  If the head instruction `i` carries the
-- precondition `P` to an intermediate assertion `R` (one wrapping step), and
-- the tail `rest` is a Hoare triple {R} rest {Q}, then the whole block
-- {P} (pbcons i rest) {Q} holds.  Proof: `evalWrapP w (pbcons i rest) s =
-- evalWrapP w rest (stepWrapP w s i)` by rfl, so the threaded equality
-- `h2 : s' = evalWrapP w (pbcons i rest) s` is def-eq to
-- `s' = evalWrapP w rest (stepWrapP w s i)`.  Run the tail triple `hrest` from
-- the post-step store `stepWrapP w s i` to the same final store `s'`: its
-- precondition `R (stepWrapP w s i)` is supplied by `hstep s h1`, its
-- equality witness by `h2`.
theorem hoare_cons (w : Nat) (P R Q : StorePred)
    (i : PInst) (rest : PBlock)
    (hstep : forall (s : (Nat -> Nat)), forall (_hp : P s), R (stepWrapP w s i))
    (hrest : Hoare w R rest Q) :
    Hoare w P (PBlock.pbcons i rest) Q :=
  fun s s' h1 h2 => hrest (stepWrapP w s i) s' (hstep s h1) h2

-- SOUND RULE (CONSEQUENCE).  Strengthen the precondition and weaken the
-- postcondition: from {P'} b {Q'}, `P => P'`, and `Q' => Q`, derive {P} b {Q}.
-- Proof: run `htrip` from `s` to the same final store `s'` with strengthened
-- precondition `hpre s h1` and the SAME equality witness `h2`, obtaining
-- `Q' s'`; then weaken it to `Q s'` with `hpost s'`.
theorem hoare_conseq (w : Nat) (P P' Q Q' : StorePred) (b : PBlock)
    (hpre : forall (s : (Nat -> Nat)), forall (_hp : P s), P' s)
    (htrip : Hoare w P' b Q')
    (hpost : forall (s : (Nat -> Nat)), forall (_hq : Q' s), Q s) :
    Hoare w P b Q :=
  fun s s' h1 h2 => hpost s' (htrip s s' (hpre s h1) h2)

-- THE REFLECTION IN ACTION: a CONCRETE VERIFIED PROGRAM.
-- `double` is the one-instruction block `r1 := r0 + r0` (wrapping at width `w`):
--   PBlock.pbcons (PInst.pmk 1 0 0 POp.padd) PBlock.pbnil
-- Spec: {  r0 + r0 fits in w bits  } double {  r1 = r0 + r0 exactly  }.
-- We discharge it through `hoare_cons` with the intermediate assertion
-- R = Q = (fun s => s 1 = s 0 + s 0):
--   * head step:  stepWrapP w s (pmk 1 0 0 padd)
--                   = writeReg s 1 (wrapPBinOp padd w (s 0) (s 0)).
--     Reading r1 back gives the written value (`writeReg_same`); under the
--     precondition `hp : s 0 + s 0 < 2^w` that value equals `s 0 + s 0`
--     exactly (`wrapPBinOp_eq_mod` to push to mod, then `mod_eq_of_lt` to
--     collapse the modulus).  Reading r0 back of the new store is def-eq to
--     `s 0` (Nat.beq 0 1 reduces to false), so the RHS `s' 0 + s' 0` is def-eq
--     to `s 0 + s 0` -- the assertion `R (stepWrapP ...)` is exactly this
--     value equality.
--   * tail:  hoare_skip carries R = Q across the empty block unchanged.
theorem double_verified (w : Nat) :
    Hoare w
      (fun s => Nat.lt (Nat.add (s 0) (s 0)) (Nat.pow 2 w))
      (PBlock.pbcons (PInst.pmk 1 0 0 POp.padd) PBlock.pbnil)
      (fun s => @Eq Nat (s 1) (Nat.add (s 0) (s 0))) :=
  hoare_cons w
    (fun s => Nat.lt (Nat.add (s 0) (s 0)) (Nat.pow 2 w))
    (fun s => @Eq Nat (s 1) (Nat.add (s 0) (s 0)))
    (fun s => @Eq Nat (s 1) (Nat.add (s 0) (s 0)))
    (PInst.pmk 1 0 0 POp.padd)
    PBlock.pbnil
    (fun s hp =>
      Eq.trans
        (writeReg_same s 1 (wrapPBinOp POp.padd w (s 0) (s 0)))
        (Eq.trans
          (wrapPBinOp_eq_mod POp.padd w (s 0) (s 0))
          (mod_eq_of_lt (Nat.add (s 0) (s 0)) (Nat.pow 2 w) hp)))
    (hoare_skip w (fun s => @Eq Nat (s 1) (Nat.add (s 0) (s 0))))

-- ===========================================================================
-- COMPOSITIONAL HOARE: program append + the SEQUENCING (COMPOSITION) RULE.
--
-- The Hoare rules above verify a block by structural cons.  Real compositional
-- verification needs to glue two ALREADY-VERIFIED programs end to end:
-- {P} b1 {R}  and  {R} b2 {Q}  =>  {P} (b1 ++ b2) {Q}.  This is the heart of
-- modular program proof -- each piece is verified once against an interface
-- (R), and the composition rule assembles the whole-program triple from the
-- pieces WITHOUT re-running the proof over the combined block.
--
-- We define program append `appendP` and prove the carrier distributes over it
-- (`evalWrapP_append`: running an appended program = running b2 from the store
-- b1 produced), then derive the sequencing rule, then USE it to verify a
-- two-instruction program by COMPOSING two single-instruction triples.
-- Everything stays axiom-free: append is a plain recursor term, the
-- distribution lemma is `PBlock.rec` with `ih` at the post-step store, and the
-- rule threads `evalWrapP_append` through the Hoare equality witness with
-- `Eq.subst`.
-- ===========================================================================

-- PROGRAM APPEND.  `appendP b1 b2` concatenates the instruction lists by
-- recursion on `b1`: nil yields `b2`; cons `i rest` yields `pbcons i` of the
-- recursively-appended tail.  Both reductions are `rfl`:
--   appendP pbnil          b2 = b2
--   appendP (pbcons i rest) b2 = pbcons i (appendP rest b2).
def appendP (b1 b2 : PBlock) : PBlock :=
  @PBlock.rec (fun _ => PBlock)
    b2
    (fun i rest ih => PBlock.pbcons i ih)
    b1

-- KEY LEMMA: the wrapping interpreter DISTRIBUTES over append.  Running the
-- appended program `appendP b1 b2` from `s` equals running `b2` from the store
-- `evalWrapP w b1 s` that `b1` produced -- i.e. eval is a homomorphism from
-- (append, programs) to (composition, store transformers).  `PBlock.rec` on b1:
--   * pbnil: `appendP pbnil b2 = b2` and `evalWrapP w pbnil s = s`, so both
--     sides are `evalWrapP w b2 s` (rfl) -> `Eq.refl`.
--   * pbcons i rest, ih: every `appendP`/`pbcons`/`evalWrapP` step below is rfl,
--     reducing the goal to `evalWrapP w (appendP rest b2) (stepWrapP w s i)
--     = evalWrapP w b2 (evalWrapP w rest (stepWrapP w s i))`, which is exactly
--     `ih` instantiated at the post-step store `stepWrapP w s i`.
theorem evalWrapP_append (w : Nat) (b1 b2 : PBlock) :
    forall (s : (Nat -> Nat)),
      @Eq.{1} (Nat -> Nat)
        (evalWrapP w (appendP b1 b2) s)
        (evalWrapP w b2 (evalWrapP w b1 s)) :=
  @PBlock.rec
    (fun b1 => forall (s : (Nat -> Nat)),
      @Eq.{1} (Nat -> Nat)
        (evalWrapP w (appendP b1 b2) s)
        (evalWrapP w b2 (evalWrapP w b1 s)))
    (fun s => @Eq.refl (Nat -> Nat) (evalWrapP w b2 s))
    (fun i rest ih => fun s => ih (stepWrapP w s i))
    b1

-- SOUND RULE (SEQUENCING / COMPOSITION).  Compose two verified triples sharing
-- the interface assertion `R`: from {P} b1 {R} and {R} b2 {Q} derive
-- {P} (appendP b1 b2) {Q}.  This is the COMPOSITIONAL rule -- it assembles the
-- whole-program triple from independently-verified pieces.
--
-- Proof (in the Hoare named-witness idiom): given `s`, the final store `s'`,
-- `h1 : P s`, and `h2 : s' = evalWrapP w (appendP b1 b2) s`.  Transport `h2`
-- along the distribution lemma `evalWrapP_append w b1 b2 s` to obtain
-- `h2' : s' = evalWrapP w b2 (evalWrapP w b1 s)` (rewrite the RHS of `h2` with
-- `Eq.subst` under the motive `fun t => @Eq (Nat->Nat) s' t`).  Let
-- `m := evalWrapP w b1 s` be the intermediate store.  Run `h1trip` from `s` to
-- `m` (its equality witness is `Eq.refl m : m = evalWrapP w b1 s`) to get
-- `R m`; then run `h2trip` from `m` to `s'` with that `R m` and the
-- transported witness `h2'` to get `Q s'`.
theorem hoare_seq (w : Nat) (P R Q : StorePred) (b1 b2 : PBlock)
    (h1trip : Hoare w P b1 R)
    (h2trip : Hoare w R b2 Q) :
    Hoare w P (appendP b1 b2) Q :=
  fun s s' h1 h2 =>
    h2trip
      (evalWrapP w b1 s)
      s'
      (h1trip s (evalWrapP w b1 s) h1 (@Eq.refl (Nat -> Nat) (evalWrapP w b1 s)))
      (@Eq.subst (Nat -> Nat)
        (fun t => @Eq (Nat -> Nat) s' t)
        (evalWrapP w (appendP b1 b2) s)
        (evalWrapP w b2 (evalWrapP w b1 s))
        (evalWrapP_append w b1 b2 s)
        h2)

-- THE COMPOSITIONAL REFLECTION IN ACTION: a TWO-INSTRUCTION program verified by
-- COMPOSING two single-instruction triples through `hoare_seq`.
--   progA = { r1 := r0 + r0 }   (PInst.pmk 1 0 0 padd)
--   progB = { r2 := r1 + r1 }   (PInst.pmk 2 1 1 padd)
-- The composed program `appendP progA progB` is verified against the spec
--   {  r0+r0 < 2^w  AND  (r0+r0)+(r0+r0) < 2^w  }
--     appendP progA progB
--   {  r2 = (r0+r0) + (r0+r0)  }
-- WITHOUT ever proving anything about the combined block directly: we give
-- progA the triple {P} progA {R} and progB the triple {R} progB {Q} (each a
-- one-step `hoare_cons`/`hoare_skip` proof in the `double_verified` shape),
-- then `hoare_seq` assembles them.  The shared interface is
--   R = (fun s => s 1 = r0+r0  AND  (s 1)+(s 1) < 2^w)
-- carrying both the value progA established (r1 = r0+r0) and the obligation
-- progB needs (its add fits).  progB's step reads r1 (untouched by its own
-- write to r2; `Nat.beq 1 2` is def-eq false so the read is rfl `s 1`) and,
-- under R's two facts, writes r2 = (s 1)+(s 1) = (r0+r0)+(r0+r0) exactly.
def progA : PBlock := PBlock.pbcons (PInst.pmk 1 0 0 POp.padd) PBlock.pbnil
def progB : PBlock := PBlock.pbcons (PInst.pmk 2 1 1 POp.padd) PBlock.pbnil

theorem seq_example_verified (w : Nat) :
    Hoare w
      (fun s => And
        (Nat.lt (Nat.add (s 0) (s 0)) (Nat.pow 2 w))
        (Nat.lt (Nat.add (Nat.add (s 0) (s 0)) (Nat.add (s 0) (s 0))) (Nat.pow 2 w)))
      (appendP progA progB)
      (fun s => @Eq Nat (s 2) (Nat.add (Nat.add (s 0) (s 0)) (Nat.add (s 0) (s 0)))) :=
  hoare_seq w
    -- P
    (fun s => And
      (Nat.lt (Nat.add (s 0) (s 0)) (Nat.pow 2 w))
      (Nat.lt (Nat.add (Nat.add (s 0) (s 0)) (Nat.add (s 0) (s 0))) (Nat.pow 2 w)))
    -- R (the shared interface): r1 = r0+r0  AND  (r1)+(r1) fits in w bits
    (fun s => And
      (@Eq Nat (s 1) (Nat.add (s 0) (s 0)))
      (Nat.lt (Nat.add (s 1) (s 1)) (Nat.pow 2 w)))
    -- Q
    (fun s => @Eq Nat (s 2) (Nat.add (Nat.add (s 0) (s 0)) (Nat.add (s 0) (s 0))))
    progA
    progB
    -- {P} progA {R}: head step writes r1 = wrapPBinOp padd w (s0) (s0); under P
    -- this equals r0+r0 (read-back + mod collapse).  R's second conjunct
    -- ((s1)+(s1) < 2^w) is def-eq, after the read-backs collapse r1 to r0+r0,
    -- to P's second conjunct -- supplied directly by `And.right`.
    (hoare_cons w
      (fun s => And
        (Nat.lt (Nat.add (s 0) (s 0)) (Nat.pow 2 w))
        (Nat.lt (Nat.add (Nat.add (s 0) (s 0)) (Nat.add (s 0) (s 0))) (Nat.pow 2 w)))
      (fun s => And
        (@Eq Nat (s 1) (Nat.add (s 0) (s 0)))
        (Nat.lt (Nat.add (s 1) (s 1)) (Nat.pow 2 w)))
      (fun s => And
        (@Eq Nat (s 1) (Nat.add (s 0) (s 0)))
        (Nat.lt (Nat.add (s 1) (s 1)) (Nat.pow 2 w)))
      (PInst.pmk 1 0 0 POp.padd)
      PBlock.pbnil
      (fun s hp =>
        @And.intro
          (@Eq Nat
            (writeReg s 1 (wrapPBinOp POp.padd w (s 0) (s 0)) 1)
            (Nat.add (s 0) (s 0)))
          (Nat.lt
            (Nat.add
              (writeReg s 1 (wrapPBinOp POp.padd w (s 0) (s 0)) 1)
              (writeReg s 1 (wrapPBinOp POp.padd w (s 0) (s 0)) 1))
            (Nat.pow 2 w))
          (Eq.trans
            (writeReg_same s 1 (wrapPBinOp POp.padd w (s 0) (s 0)))
            (Eq.trans
              (wrapPBinOp_eq_mod POp.padd w (s 0) (s 0))
              (mod_eq_of_lt (Nat.add (s 0) (s 0)) (Nat.pow 2 w)
                (@And.left
                  (Nat.lt (Nat.add (s 0) (s 0)) (Nat.pow 2 w))
                  (Nat.lt (Nat.add (Nat.add (s 0) (s 0)) (Nat.add (s 0) (s 0))) (Nat.pow 2 w))
                  hp))))
          (@Eq.subst Nat
            (fun (v : Nat) =>
              Nat.lt (Nat.add v v) (Nat.pow 2 w))
            (Nat.add (s 0) (s 0))
            (writeReg s 1 (wrapPBinOp POp.padd w (s 0) (s 0)) 1)
            (Eq.symm
              (Eq.trans
                (writeReg_same s 1 (wrapPBinOp POp.padd w (s 0) (s 0)))
                (Eq.trans
                  (wrapPBinOp_eq_mod POp.padd w (s 0) (s 0))
                  (mod_eq_of_lt (Nat.add (s 0) (s 0)) (Nat.pow 2 w)
                    (@And.left
                      (Nat.lt (Nat.add (s 0) (s 0)) (Nat.pow 2 w))
                      (Nat.lt (Nat.add (Nat.add (s 0) (s 0)) (Nat.add (s 0) (s 0))) (Nat.pow 2 w))
                      hp)))))
            (@And.right
              (Nat.lt (Nat.add (s 0) (s 0)) (Nat.pow 2 w))
              (Nat.lt (Nat.add (Nat.add (s 0) (s 0)) (Nat.add (s 0) (s 0))) (Nat.pow 2 w))
              hp)))
      (hoare_skip w
        (fun s => And
          (@Eq Nat (s 1) (Nat.add (s 0) (s 0)))
          (Nat.lt (Nat.add (s 1) (s 1)) (Nat.pow 2 w)))))
    -- {R} progB {Q}: head step writes r2 = wrapPBinOp padd w (s1) (s1).  Under R
    -- the obligation `(s1)+(s1) < 2^w` collapses the wrap (read-back of r2 +
    -- mod), giving r2 = (s1)+(s1); R's first fact `s1 = r0+r0` rewrites it to
    -- (r0+r0)+(r0+r0).  (Reading r1 of the new store is rfl `s 1`: Nat.beq 1 2
    -- is def-eq false.)
    (hoare_cons w
      (fun s => And
        (@Eq Nat (s 1) (Nat.add (s 0) (s 0)))
        (Nat.lt (Nat.add (s 1) (s 1)) (Nat.pow 2 w)))
      (fun s => @Eq Nat (s 2) (Nat.add (Nat.add (s 0) (s 0)) (Nat.add (s 0) (s 0))))
      (fun s => @Eq Nat (s 2) (Nat.add (Nat.add (s 0) (s 0)) (Nat.add (s 0) (s 0))))
      (PInst.pmk 2 1 1 POp.padd)
      PBlock.pbnil
      (fun s hr =>
        Eq.trans
          (writeReg_same s 2 (wrapPBinOp POp.padd w (s 1) (s 1)))
          (Eq.trans
            (wrapPBinOp_eq_mod POp.padd w (s 1) (s 1))
            (Eq.trans
              (mod_eq_of_lt (Nat.add (s 1) (s 1)) (Nat.pow 2 w)
                (@And.right
                  (@Eq Nat (s 1) (Nat.add (s 0) (s 0)))
                  (Nat.lt (Nat.add (s 1) (s 1)) (Nat.pow 2 w))
                  hr))
              (@Eq.subst Nat
                (fun (v : Nat) =>
                  @Eq Nat (Nat.add (s 1) (s 1)) (Nat.add v v))
                (s 1)
                (Nat.add (s 0) (s 0))
                (@And.left
                  (@Eq Nat (s 1) (Nat.add (s 0) (s 0)))
                  (Nat.lt (Nat.add (s 1) (s 1)) (Nat.pow 2 w))
                  hr)
                (@Eq.refl Nat (Nat.add (s 1) (s 1)))))))
      (hoare_skip w
        (fun s => @Eq Nat (s 2) (Nat.add (Nat.add (s 0) (s 0)) (Nat.add (s 0) (s 0))))))

-- ===========================================================================
-- HOARE LOGIC OVER THE FULL MACHINE (arithmetic + indirect load/store).
--
-- Everything above verifies pure-arithmetic blocks (`PBlock` / `evalWrapP`).
-- This section lifts the SAME sound Hoare calculus onto the FULL von-Neumann
-- machine `evalSafe` -- the interpreter that already covers `smArith`,
-- `smLoad` (indirect load `dst <- s[s[addr]]`), and `smStore` (indirect store
-- `s[s[addr]] <- s[val]`) over one shared address space.  We reuse the exact
-- named-equality-witness idiom of `Hoare`, prove the three standard rules
-- sound over `evalSafe`/`SafeBlock`, and then VERIFY A CONCRETE MEMORY PROGRAM:
-- a store-then-load that recovers a value through memory.  Everything stays
-- axiom-free: the rules are lambda terms threading `evalSafe`'s definitional
-- unfolding; the memory program discharges through the `writeReg` read-back
-- lemmas (`writeReg_same` for the matching cell, `writeReg_other` for the
-- non-aliasing cell).
-- ===========================================================================

-- READ-BACK of a DIFFERENT cell: reading `e` after writing `d` (with `e ≠ d` as
-- `Nat.beq e d = false`) leaves the cell unchanged.  `writeReg s d v e` is
-- def-eq to `@Bool.casesOn (fun _ => Nat) (Nat.beq e d) (s e) v` (the `match` in
-- writeReg on `Nat.beq e d`).  Transporting the hypothesis `Nat.beq e d = false`
-- through the casesOn motive `P` with `congrArg` selects the false-branch `s e`:
-- `P (Nat.beq e d)` def-eq `writeReg s d v e`, `P Bool.false` def-eq `s e`, so
-- `congrArg P h` has type `writeReg s d v e = s e`.
theorem writeReg_other (s : (Nat -> Nat)) (d v e : Nat)
    (h : @Eq Bool (Nat.beq e d) Bool.false) :
    @Eq Nat (writeReg s d v e) (s e) :=
  congrArg
    (fun (b : Bool) => @Bool.casesOn (fun _ => Nat) b (s e) v)
    h

-- THE FULL-MACHINE HOARE TRIPLE.  `HoareSafe w P b Q` := running the full
-- machine block `b` at width `w` from any `P`-store yields a `Q`-store.  Same
-- named-witness idiom as `Hoare`: the result store is threaded through a NAMED
-- equality `s' = evalSafe w b s`, and predicates are applied only to the bound
-- store `s'`.  The carrier is the audited full-machine interpreter `evalSafe`.
def HoareSafe (w : Nat) (P : StorePred) (b : SafeBlock) (Q : StorePred) : Prop :=
  forall (s : (Nat -> Nat)), forall (s' : (Nat -> Nat)),
    forall (_h1 : P s), forall (_h2 : @Eq (Nat -> Nat) s' (evalSafe w b s)), Q s'

-- SOUND RULE (SKIP).  `evalSafe w sbnil s = s` by rfl, so the threaded equality
-- `h2 : s' = evalSafe w sbnil s` is def-eq to `s' = s`; transport `h1 : P s`
-- along `Eq.symm h2` to `P s'` via `Eq.subst` with motive `P`.
theorem hoareSafe_skip (w : Nat) (P : StorePred) :
    HoareSafe w P SafeBlock.sbnil P :=
  fun s s' h1 h2 => @Eq.subst (Nat -> Nat) P s s' (Eq.symm h2) h1

-- SOUND RULE (SEQUENCING / CONS).  If the head instruction `i` carries `P` to an
-- intermediate assertion `R` (one full-machine step), and `{R} rest {Q}` holds,
-- then `{P} (sbcons i rest) {Q}` holds.  `evalSafe w (sbcons i rest) s =
-- evalSafe w rest (stepSafe w s i)` by rfl, so the threaded equality is def-eq
-- to `s' = evalSafe w rest (stepSafe w s i)`.  Run `hrest` from the post-step
-- store `stepSafe w s i` to the same `s'`, supplying its precondition with
-- `hstep s h1` and its equality witness with `h2`.
theorem hoareSafe_cons (w : Nat) (P R Q : StorePred)
    (i : SafeInst) (rest : SafeBlock)
    (hstep : forall (s : (Nat -> Nat)), forall (_hp : P s), R (stepSafe w s i))
    (hrest : HoareSafe w R rest Q) :
    HoareSafe w P (SafeBlock.sbcons i rest) Q :=
  fun s s' h1 h2 => hrest (stepSafe w s i) s' (hstep s h1) h2

-- SOUND RULE (CONSEQUENCE).  Strengthen the precondition, weaken the
-- postcondition: from `{P'} b {Q'}`, `P => P'`, `Q' => Q`, derive `{P} b {Q}`.
-- Run `htrip` from `s` to the same `s'` with the strengthened precondition
-- `hpre s h1` and the SAME equality witness `h2`, obtaining `Q' s'`; weaken to
-- `Q s'` with `hpost s'`.
theorem hoareSafe_conseq (w : Nat) (P P' Q Q' : StorePred) (b : SafeBlock)
    (hpre : forall (s : (Nat -> Nat)), forall (_hp : P s), P' s)
    (htrip : HoareSafe w P' b Q')
    (hpost : forall (s : (Nat -> Nat)), forall (_hq : Q' s), Q s) :
    HoareSafe w P b Q :=
  fun s s' h1 h2 => hpost s' (htrip s s' (hpre s h1) h2)

-- THE HEADLINE: a CONCRETE VERIFIED MEMORY PROGRAM (store-then-load).
-- `memRoundtrip` is the two-instruction full-machine block
--   smStore 0 1 ; smLoad 2 0
-- read in machine terms:
--   * `smStore 0 1`: store register-1's value at the address held in register 0
--       -- i.e. `mem[s 0] <- s 1`, producing `W = writeReg s (s 0) (s 1)`.
--   * `smLoad 2 0`:  load FROM the address held in register 0 INTO register 2
--       -- i.e. `L = writeReg W 2 (W (W 0))`.
-- The value `s 1` makes a genuine ROUND TRIP through memory: stored at address
-- `s 0`, then read back out of `mem[s 0]` and landed in register 2.
--
-- NON-ALIASING PRECONDITION.  In this von-Neumann machine registers and memory
-- share ONE address space, so the data address `s 0` could in principle collide
-- with the register cells 0, 1, 2 that the program reads.  The honest spec
-- carries the three disjointness facts that rule the collisions out:
--   beq 0 (s 0) = false   (store doesn't clobber the address register 0),
--   beq 1 (s 0) = false   (store doesn't clobber the value register 1),
--   beq 2 (s 0) = false   (store doesn't clobber the destination register 2).
-- Under them, EVERY re-read of cells 0/1/2 through the mutated store reduces
-- back to its original value (`writeReg_other`), while the written cell reads
-- back the stored value (`writeReg_same`).
-- Spec:  { s0 ∉ {0,1,2} }  memRoundtrip  { s 2 = s 1 }.
--
-- The Hoare triple is named-witness: every predicate is applied to the CURRENT
-- (post-step) store, so the interface assertion `R` must restate the
-- non-aliasing facts on the post-store store and pin `mem[addr]` to the value
-- via the store's OWN index (`s (s 0)` read through the post-store store).
def memRoundtrip : SafeBlock :=
  SafeBlock.sbcons (SafeInst.smStore 0 1)
    (SafeBlock.sbcons (SafeInst.smLoad 2 0) SafeBlock.sbnil)

theorem memRoundtrip_verified (w : Nat) :
    HoareSafe w
      (fun s => And
        (@Eq Bool (Nat.beq 0 (s 0)) Bool.false)
        (And
          (@Eq Bool (Nat.beq 1 (s 0)) Bool.false)
          (@Eq Bool (Nat.beq 2 (s 0)) Bool.false)))
      memRoundtrip
      (fun s => @Eq Nat (s 2) (s 1)) :=
  hoareSafe_cons w
    -- P : the data address s 0 is none of the register cells 0, 1, 2.
    (fun s => And
      (@Eq Bool (Nat.beq 0 (s 0)) Bool.false)
      (And
        (@Eq Bool (Nat.beq 1 (s 0)) Bool.false)
        (@Eq Bool (Nat.beq 2 (s 0)) Bool.false)))
    -- R (post-store interface), stated on the CURRENT store `t`:
    --   (1) the cell at t's own address `t (t 0)` holds `t 1` (the value survived);
    --   (2,3,4) the address `t 0` still avoids register cells 0, 1, 2.
    (fun t => And
      (@Eq Nat (t (t 0)) (t 1))
      (And
        (@Eq Bool (Nat.beq 0 (t 0)) Bool.false)
        (And
          (@Eq Bool (Nat.beq 1 (t 0)) Bool.false)
          (@Eq Bool (Nat.beq 2 (t 0)) Bool.false))))
    -- Q : register 2 holds the recovered value (= original register 1).
    (fun s => @Eq Nat (s 2) (s 1))
    (SafeInst.smStore 0 1)
    (SafeBlock.sbcons (SafeInst.smLoad 2 0) SafeBlock.sbnil)
    -- {P} smStore 0 1 {R}.  Post-store store `W = writeReg s (s 0) (s 1)`.
    -- Under P (= h0/h1/h2), every cell read of W reduces:
    --   W 0 = s 0, W 1 = s 1, W 2 = s 2   (writeReg_other; addresses 0/1/2 ≠ s 0)
    --   W (s 0) = s 1                      (writeReg_same; the written cell)
    -- R(W) conjuncts:
    --   (1) W (W 0) = W 1 : rewrite index `W 0 = s 0`, then `W (s 0) = s 1`
    --       (writeReg_same) and `W 1 = s 1` (writeReg_other) glue to the equality.
    --   (2,3,4) beq k (W 0) = false : rewrite `W 0 = s 0`, supply h_k.
    (fun s hp =>
      @And.intro
        (@Eq Nat
          (writeReg s (s 0) (s 1) (writeReg s (s 0) (s 1) 0))
          (writeReg s (s 0) (s 1) 1))
        (And
          (@Eq Bool (Nat.beq 0 (writeReg s (s 0) (s 1) 0)) Bool.false)
          (And
            (@Eq Bool (Nat.beq 1 (writeReg s (s 0) (s 1) 0)) Bool.false)
            (@Eq Bool (Nat.beq 2 (writeReg s (s 0) (s 1) 0)) Bool.false)))
        -- (1) W (W 0) = W 1.
        (Eq.trans
          -- W (W 0) = s 1 : transport index `W 0 -> s 0`, then writeReg_same.
          (@Eq.subst Nat
            (fun (a : Nat) =>
              @Eq Nat (writeReg s (s 0) (s 1) a) (s 1))
            (s 0)
            (writeReg s (s 0) (s 1) 0)
            (Eq.symm
              (writeReg_other s (s 0) (s 1) 0
                (@And.left
                  (@Eq Bool (Nat.beq 0 (s 0)) Bool.false)
                  (And
                    (@Eq Bool (Nat.beq 1 (s 0)) Bool.false)
                    (@Eq Bool (Nat.beq 2 (s 0)) Bool.false))
                  hp)))
            (writeReg_same s (s 0) (s 1)))
          -- s 1 = W 1 : symm of writeReg_other (cell 1 ≠ s 0).
          (Eq.symm
            (writeReg_other s (s 0) (s 1) 1
              (@And.left
                (@Eq Bool (Nat.beq 1 (s 0)) Bool.false)
                (@Eq Bool (Nat.beq 2 (s 0)) Bool.false)
                (@And.right
                  (@Eq Bool (Nat.beq 0 (s 0)) Bool.false)
                  (And
                    (@Eq Bool (Nat.beq 1 (s 0)) Bool.false)
                    (@Eq Bool (Nat.beq 2 (s 0)) Bool.false))
                  hp)))))
        (@And.intro
          (@Eq Bool (Nat.beq 0 (writeReg s (s 0) (s 1) 0)) Bool.false)
          (And
            (@Eq Bool (Nat.beq 1 (writeReg s (s 0) (s 1) 0)) Bool.false)
            (@Eq Bool (Nat.beq 2 (writeReg s (s 0) (s 1) 0)) Bool.false))
          -- (2) beq 0 (W 0) = false : transport index, supply h0.
          (@Eq.subst Nat
            (fun (a : Nat) => @Eq Bool (Nat.beq 0 a) Bool.false)
            (s 0)
            (writeReg s (s 0) (s 1) 0)
            (Eq.symm
              (writeReg_other s (s 0) (s 1) 0
                (@And.left
                  (@Eq Bool (Nat.beq 0 (s 0)) Bool.false)
                  (And
                    (@Eq Bool (Nat.beq 1 (s 0)) Bool.false)
                    (@Eq Bool (Nat.beq 2 (s 0)) Bool.false))
                  hp)))
            (@And.left
              (@Eq Bool (Nat.beq 0 (s 0)) Bool.false)
              (And
                (@Eq Bool (Nat.beq 1 (s 0)) Bool.false)
                (@Eq Bool (Nat.beq 2 (s 0)) Bool.false))
              hp))
          (@And.intro
            (@Eq Bool (Nat.beq 1 (writeReg s (s 0) (s 1) 0)) Bool.false)
            (@Eq Bool (Nat.beq 2 (writeReg s (s 0) (s 1) 0)) Bool.false)
            -- (3) beq 1 (W 0) = false : transport index, supply h1.
            (@Eq.subst Nat
              (fun (a : Nat) => @Eq Bool (Nat.beq 1 a) Bool.false)
              (s 0)
              (writeReg s (s 0) (s 1) 0)
              (Eq.symm
                (writeReg_other s (s 0) (s 1) 0
                  (@And.left
                    (@Eq Bool (Nat.beq 0 (s 0)) Bool.false)
                    (And
                      (@Eq Bool (Nat.beq 1 (s 0)) Bool.false)
                      (@Eq Bool (Nat.beq 2 (s 0)) Bool.false))
                    hp)))
              (@And.left
                (@Eq Bool (Nat.beq 1 (s 0)) Bool.false)
                (@Eq Bool (Nat.beq 2 (s 0)) Bool.false)
                (@And.right
                  (@Eq Bool (Nat.beq 0 (s 0)) Bool.false)
                  (And
                    (@Eq Bool (Nat.beq 1 (s 0)) Bool.false)
                    (@Eq Bool (Nat.beq 2 (s 0)) Bool.false))
                  hp)))
            -- (4) beq 2 (W 0) = false : transport index, supply h2.
            (@Eq.subst Nat
              (fun (a : Nat) => @Eq Bool (Nat.beq 2 a) Bool.false)
              (s 0)
              (writeReg s (s 0) (s 1) 0)
              (Eq.symm
                (writeReg_other s (s 0) (s 1) 0
                  (@And.left
                    (@Eq Bool (Nat.beq 0 (s 0)) Bool.false)
                    (And
                      (@Eq Bool (Nat.beq 1 (s 0)) Bool.false)
                      (@Eq Bool (Nat.beq 2 (s 0)) Bool.false))
                    hp)))
              (@And.right
                (@Eq Bool (Nat.beq 1 (s 0)) Bool.false)
                (@Eq Bool (Nat.beq 2 (s 0)) Bool.false)
                (@And.right
                  (@Eq Bool (Nat.beq 0 (s 0)) Bool.false)
                  (And
                    (@Eq Bool (Nat.beq 1 (s 0)) Bool.false)
                    (@Eq Bool (Nat.beq 2 (s 0)) Bool.false))
                  hp))))))
    -- {R} smLoad 2 0 {Q}.  Post-load store `L = writeReg t 2 (t (t 0))`.
    --   L 2 = t (t 0)  (writeReg_same), and R.1 says `t (t 0) = t 1`.
    --   L 1 = t 1      (def-eq: beq 1 2 reduces to false), so Q(L) `L 2 = L 1`
    --   is exactly `t (t 0) = t 1`, supplied by R.1.
    (hoareSafe_cons w
      (fun t => And
        (@Eq Nat (t (t 0)) (t 1))
        (And
          (@Eq Bool (Nat.beq 0 (t 0)) Bool.false)
          (And
            (@Eq Bool (Nat.beq 1 (t 0)) Bool.false)
            (@Eq Bool (Nat.beq 2 (t 0)) Bool.false))))
      (fun s => @Eq Nat (s 2) (s 1))
      (fun s => @Eq Nat (s 2) (s 1))
      (SafeInst.smLoad 2 0)
      SafeBlock.sbnil
      (fun s hr =>
        Eq.trans
          (writeReg_same s 2 (s (s 0)))
          (@And.left
            (@Eq Nat (s (s 0)) (s 1))
            (And
              (@Eq Bool (Nat.beq 0 (s 0)) Bool.false)
              (And
                (@Eq Bool (Nat.beq 1 (s 0)) Bool.false)
                (@Eq Bool (Nat.beq 2 (s 0)) Bool.false)))
            hr))
      (hoareSafe_skip w
        (fun s => @Eq Nat (s 2) (s 1))))

-- ===========================================================================
-- THE LOOP-INVARIANT RULE: verifying BOUNDED ITERATIVE programs.
--
-- Everything above verifies STRAIGHT-LINE blocks (cons / append).  A real
-- program logic must also verify LOOPS.  We define `repeatN n body` -- the
-- program that runs `body` exactly `n` times -- and prove the bounded-loop
-- invariant rule: if `body` PRESERVES an invariant `Inv` (one iteration is a
-- triple {Inv} body {Inv}), then repeating it ANY number of times preserves
-- `Inv` ({Inv} (repeatN n body) {Inv}).  This is THE rule that discharges the
-- verification condition of an iterative program: prove the body preserves the
-- invariant once, conclude the whole loop preserves it for every trip count.
--
-- The proof is `@Nat.rec` on the iteration count, with `hoare_skip` at 0 and
-- `hoare_seq` (the already-proven COMPOSITION rule) gluing one more body
-- iteration onto the inductive hypothesis at `succ`.  Both `repeatN` reductions
-- are `rfl`, so each case is a one-liner.  Everything stays axiom-free: the
-- only ingredients are the recursor, `hoare_skip`, and `hoare_seq`.
-- ===========================================================================

-- N-FOLD REPETITION.  `repeatN n body` is `body` appended to itself `n` times,
-- by `@Nat.rec` on `n`: zero yields the empty program `pbnil`; `succ k` prepends
-- one more `body` onto the `k`-fold repetition.  Both reductions are `rfl`:
--   repeatN 0        body = pbnil
--   repeatN (succ k) body = appendP body (repeatN k body).
def repeatN : Nat -> PBlock -> PBlock :=
  fun n body =>
    @Nat.rec (fun _ => PBlock)
      PBlock.pbnil
      (fun _ ih => appendP body ih)
      n

-- THE LOOP-INVARIANT RULE (the headline).  If one iteration of `body` preserves
-- the invariant `Inv` (`h : Hoare w Inv body Inv`), then `repeatN n body`
-- preserves `Inv` for EVERY iteration count `n`.  `@Nat.rec` on `n` with motive
-- `fun n => Hoare w Inv (repeatN n body) Inv`:
--   * n = 0: `repeatN 0 body = pbnil` (rfl), so the goal `Hoare w Inv pbnil Inv`
--     is exactly `hoare_skip w Inv`.
--   * n = succ k, ih : `Hoare w Inv (repeatN k body) Inv`:
--     `repeatN (succ k) body = appendP body (repeatN k body)` (rfl), so the goal
--     `Hoare w Inv (appendP body (repeatN k body)) Inv` is exactly
--     `hoare_seq w Inv Inv Inv body (repeatN k body) h ih` -- compose the head
--     iteration's triple `h` with the loop tail's triple `ih` over the shared
--     interface `Inv`.
theorem hoare_repeat (w : Nat) (Inv : StorePred) (body : PBlock)
    (h : Hoare w Inv body Inv) :
    forall (n : Nat), Hoare w Inv (repeatN n body) Inv :=
  @Nat.rec
    (fun n => Hoare w Inv (repeatN n body) Inv)
    (hoare_skip w Inv)
    (fun k ih => hoare_seq w Inv Inv Inv body (repeatN k body) h ih)

-- ===========================================================================
-- A CONCRETE VERIFIED LOOP (reflection-in-action): a real iterative program
-- preserving the store-typing invariant `storeInRange w` for ANY trip count.
--
-- We lift the `storeInRange` substrate (already proven for the WrapInst machine)
-- onto the PBlock machine, then feed a single-instruction body through the
-- loop-invariant rule.  The body is `r1 := r0 + r0` (`pmk 1 0 0 padd`); each
-- iteration's result is `(s 0 + s 0) % 2^w`, which is `< 2^w` by `mod_lt`, so
-- the body preserves `storeInRange w`.  `hoare_repeat` then certifies that
-- running that body any number of times keeps every register width-`w`.
-- ===========================================================================

-- Every PBlock wrapping-op result is in range: each `wrapPBinOp` case ends in
-- `% 2^w`, an instance of `mod_lt` with the strictly-positive modulus.
-- `@POp.casesOn` (padd: `(a+b)%2^w`; pmul: `(a*b)%2^w`).
theorem wrapPBinOp_in_range (op : POp) (w a b : Nat) :
    Nat.lt (wrapPBinOp op w a b) (Nat.pow 2 w) :=
  @POp.casesOn
    (fun o => Nat.lt (wrapPBinOp o w a b) (Nat.pow 2 w))
    op
    (mod_lt (Nat.add a b) (Nat.pow 2 w) (two_pow_pos w))
    (mod_lt (Nat.mul a b) (Nat.pow 2 w) (two_pow_pos w))

-- STEP SOUNDNESS (PBlock machine): one PBlock instruction preserves the store
-- invariant.  Arithmetic case writes an in-range value (`wrapPBinOp_in_range`),
-- so `writeReg_inRange` keeps the store in range; the no-op leaves it unchanged.
theorem stepWrapP_inRange (w : Nat) (s : (Nat -> Nat)) (i : PInst)
    (hs : storeInRange w s) :
    storeInRange w (stepWrapP w s i) :=
  @PInst.casesOn
    (fun i => storeInRange w (stepWrapP w s i))
    i
    (fun dst src1 src2 op =>
      writeReg_inRange w s dst (wrapPBinOp op w (s src1) (s src2)) hs
        (wrapPBinOp_in_range op w (s src1) (s src2)))
    hs

-- THE LOOP BODY: a single PBlock instruction `r1 := r0 + r0`.
def inRangeBody : PBlock := PBlock.pbcons (PInst.pmk 1 0 0 POp.padd) PBlock.pbnil

-- {storeInRange w} inRangeBody {storeInRange w}: one iteration preserves the
-- typing invariant.  `hoare_cons` with the head step discharged by
-- `stepWrapP_inRange` (the step writes an in-range value), the tail by
-- `hoare_skip`.
theorem body_inRange (w : Nat) :
    Hoare w (storeInRange w) inRangeBody (storeInRange w) :=
  hoare_cons w
    (storeInRange w)
    (storeInRange w)
    (storeInRange w)
    (PInst.pmk 1 0 0 POp.padd)
    PBlock.pbnil
    (fun s hp => stepWrapP_inRange w s (PInst.pmk 1 0 0 POp.padd) hp)
    (hoare_skip w (storeInRange w))

-- THE VERIFIED LOOP (the headline result).  Running `inRangeBody` ANY number of
-- iterations `n` preserves the store-typing invariant `storeInRange w` -- a real
-- bounded loop, verified for every trip count by `hoare_repeat` from the single
-- body triple `body_inRange`.
theorem loop_preserves_inRange (w : Nat) :
    forall (n : Nat), Hoare w (storeInRange w) (repeatN n inRangeBody) (storeInRange w) :=
  hoare_repeat w (storeInRange w) inRangeBody (body_inRange w)

-- ===========================================================================
-- THE COUNTED (INDEXED) LOOP-INVARIANT RULE: verifying the FUNCTIONAL RESULT
-- of an iterative program.
--
-- `hoare_repeat` proves a loop PRESERVES a single fixed invariant -- enough for
-- TYPE-soundness (the store stays in range) but blind to what the loop COMPUTES.
-- To verify functional correctness we need a counter-INDEXED invariant
-- `Inv : Nat -> StorePred` that ADVANCES with the iteration count: if every step
-- carries `Inv k` to `Inv (succ k)`, then `n` steps carry `Inv 0` to `Inv n`.
-- The post-state `Inv n` then PINS the computed value as a function of the trip
-- count -- that is functional correctness.
--
-- We define `repeatR n body` with the body composed LAST
-- (`repeatR (succ k) body = appendP (repeatR k body) body`, rfl) so that the
-- induction lines up with `hoare_seq` directly: the loop tail `repeatR k body`
-- runs first (taking `Inv 0` to `Inv k` by the IH), then ONE more body runs
-- (taking `Inv k` to `Inv (succ k)` by the per-step hypothesis at `k`).
-- Everything is axiom-free: `@Nat.rec`, `hoare_skip`, and `hoare_seq`.
-- ===========================================================================

-- N-FOLD REPETITION, BODY LAST.  `repeatR n body` runs `body` `n` times, with the
-- recursion APPENDING one more body on the right at each `succ`:
--   repeatR 0        body = pbnil
--   repeatR (succ k) body = appendP (repeatR k body) body.
-- Both reductions are `rfl`.  (Contrast `repeatN`, which prepends on the left;
-- appending on the right is what makes the counted-invariant induction compose
-- with `hoare_seq` -- the already-verified prefix `repeatR k body` is the FIRST
-- operand, the single fresh `body` the second.)
def repeatR : Nat -> PBlock -> PBlock :=
  fun n body =>
    @Nat.rec (fun _ => PBlock)
      PBlock.pbnil
      (fun _ ih => appendP ih body)
      n

-- THE COUNTED LOOP-INVARIANT RULE (the headline).  Given a counter-indexed
-- invariant `Inv : Nat -> StorePred` and a body that ADVANCES the index by one
-- (`h : forall k, Hoare w (Inv k) body (Inv (succ k))`), running the body `n`
-- times advances the index from `0` to `n`:
--   forall n, Hoare w (Inv 0) (repeatR n body) (Inv n).
-- `@Nat.rec` on `n` with motive `fun n => Hoare w (Inv 0) (repeatR n body) (Inv n)`:
--   * n = 0: `repeatR 0 body = pbnil` (rfl); goal `Hoare w (Inv 0) pbnil (Inv 0)`
--     is exactly `hoare_skip w (Inv 0)`.
--   * n = succ k, ih : `Hoare w (Inv 0) (repeatR k body) (Inv k)`:
--     `repeatR (succ k) body = appendP (repeatR k body) body` (rfl); goal
--     `Hoare w (Inv 0) (appendP (repeatR k body) body) (Inv (succ k))` is exactly
--     `hoare_seq w (Inv 0) (Inv k) (Inv (succ k)) (repeatR k body) body ih (h k)`
--     -- compose the verified loop tail (`Inv 0` -> `Inv k`, the IH) with one more
--     body iteration (`Inv k` -> `Inv (succ k)`, the per-step hypothesis at `k`).
theorem hoare_repeat_indexed (w : Nat) (Inv : Nat -> StorePred) (body : PBlock)
    (h : forall (k : Nat), Hoare w (Inv k) body (Inv (Nat.succ k))) :
    forall (n : Nat), Hoare w (Inv 0) (repeatR n body) (Inv n) :=
  @Nat.rec
    (fun n => Hoare w (Inv 0) (repeatR n body) (Inv n))
    (hoare_skip w (Inv 0))
    (fun k ih =>
      hoare_seq w (Inv 0) (Inv k) (Inv (Nat.succ k)) (repeatR k body) body ih (h k))

-- ===========================================================================
-- A VERIFIED ITERATIVE ALGORITHM: MULTIPLY BY REPEATED ADDITION.
--
-- The headline application of the counted loop rule.  The loop body is the
-- single instruction `r0 := r0 + r1` (`pmk 0 0 1 padd`).  Starting from r0 = 0
-- and r1 = C, running the body `n` times accumulates `C` into r0 `n` times --
-- computing the product `C * n`.  We verify this for EVERY trip count `n`.
--
-- An accumulating loop's exact value `C*k` grows without bound, so no machine
-- store-predicate can carry the no-overflow `C*k < 2^w` as a SELF-PRESERVING
-- invariant (each step would need a strictly larger bound than the last).  The
-- honest, unconditional functional spec is therefore the MACHINE recurrence
-- itself: `iterAdd w C k` is the k-fold wrapping accumulation
-- `(· + C) % 2^w` from 0, which matches the body step DEFINITIONALLY
-- (`iterAdd w C (succ k) = (iterAdd w C k + C) % 2^w`, rfl).  The counted-loop
-- triple then closes with NO precondition at all -- the loop computes
-- `iterAdd w C n` for every `n`.
--
-- We then prove, as a separate PURE-ARITHMETIC lemma, that this machine
-- recurrence COINCIDES with true multiplication whenever the product fits:
-- `C*k < 2^w  ->  iterAdd w C k = C*k`.  The induction works because the bound
-- is DOWNWARD-CLOSED -- `C*k <= C*(succ k)` (monotonicity of `Nat.mul`), so the
-- bound at `succ k` hands the IH its bound at `k`.  `hoare_conseq` finally
-- weakens the machine-recurrence postcondition to the exact product `C*N` under
-- the global precondition `C*N < 2^w`, giving the verified multiply.
-- ===========================================================================

-- THE MACHINE RECURRENCE.  `iterAdd w C k` = accumulate `C` into 0, wrapping at
-- width `w`, exactly `k` times:
--   iterAdd w C 0        = 0
--   iterAdd w C (succ k) = (iterAdd w C k + C) % 2^w.
-- Both reductions are `rfl`; the `succ` reduction is EXACTLY the body step.
def iterAdd : Nat -> Nat -> Nat -> Nat :=
  fun w C k =>
    @Nat.rec (fun _ => Nat)
      0
      (fun _ ih => (ih + C) % (2 ^ w))
      k

-- THE LOOP BODY: `r0 := r0 + r1` (add register 1 into register 0).
def mulBody : PBlock := PBlock.pbcons (PInst.pmk 0 0 1 POp.padd) PBlock.pbnil

-- THE COUNTER-INDEXED INVARIANT.  After `k` iterations: r1 still holds the
-- multiplicand `C`, and r0 holds the k-fold machine accumulation `iterAdd w C k`.
def mulInv (w C : Nat) : Nat -> StorePred :=
  fun k => fun s =>
    And (@Eq Nat (s 1) C) (@Eq Nat (s 0) (iterAdd w C k))

-- PER-STEP PRESERVATION: one body iteration advances the indexed invariant from
-- `k` to `succ k`.  The body writes r0 := `wrapPBinOp padd w (s 0) (s 1)` =
-- `(s 0 + s 1) % 2^w` and leaves r1 untouched (`writeReg_other`, `Nat.beq 1 0`
-- def-eq false).  Under `mulInv ... k` (`s 1 = C`, `s 0 = iterAdd w C k`):
--   * r1 read-back: `writeReg_other` gives `s' 1 = s 1`, then `= C` by the
--     invariant's first conjunct.
--   * r0 read-back: `writeReg_same` gives `s' 0 = (s 0 + s 1) % 2^w`; rewriting
--     `s 1` to `C` (second `Eq.subst`) and `s 0` to `iterAdd w C k` (third)
--     turns it into `(iterAdd w C k + C) % 2^w`, which is `iterAdd w C (succ k)`
--     DEFINITIONALLY (the `succ` reduction of `iterAdd`).  No no-overflow
--     reasoning is needed -- the spec IS the wrapping recurrence.
theorem mulBody_step (w C : Nat) :
    forall (k : Nat), Hoare w (mulInv w C k) mulBody (mulInv w C (Nat.succ k)) :=
  fun k =>
    hoare_cons w
      (mulInv w C k)
      (mulInv w C (Nat.succ k))
      (mulInv w C (Nat.succ k))
      (PInst.pmk 0 0 1 POp.padd)
      PBlock.pbnil
      (fun s hp =>
        @And.intro
          (@Eq Nat
            (writeReg s 0 (wrapPBinOp POp.padd w (s 0) (s 1)) 1)
            C)
          (@Eq Nat
            (writeReg s 0 (wrapPBinOp POp.padd w (s 0) (s 1)) 0)
            (iterAdd w C (Nat.succ k)))
          -- r1 unchanged, = C
          (Eq.trans
            (writeReg_other s 0 (wrapPBinOp POp.padd w (s 0) (s 1)) 1
              (@Eq.refl Bool Bool.false))
            (@And.left
              (@Eq Nat (s 1) C)
              (@Eq Nat (s 0) (iterAdd w C k))
              hp))
          -- r0 = wrapPBinOp padd w (s0) (s1).  Rewrite s1 -> C (second subst) and
          -- s0 -> iterAdd w C k (third subst); the result
          -- `wrapPBinOp padd w (iterAdd w C k) C` is DEFINITIONALLY
          -- `(iterAdd w C k + C) % 2^w` = `iterAdd w C (succ k)` (final Eq.refl).
          (Eq.trans
            (writeReg_same s 0 (wrapPBinOp POp.padd w (s 0) (s 1)))
            (@Eq.subst Nat
              (fun (v : Nat) =>
                @Eq Nat (wrapPBinOp POp.padd w (s 0) v) (iterAdd w C (Nat.succ k)))
              C
              (s 1)
              (Eq.symm
                (@And.left
                  (@Eq Nat (s 1) C)
                  (@Eq Nat (s 0) (iterAdd w C k))
                  hp))
              (@Eq.subst Nat
                (fun (u : Nat) =>
                  @Eq Nat (wrapPBinOp POp.padd w u C) (iterAdd w C (Nat.succ k)))
                (iterAdd w C k)
                (s 0)
                (Eq.symm
                  (@And.right
                    (@Eq Nat (s 1) C)
                    (@Eq Nat (s 0) (iterAdd w C k))
                    hp))
                (@Eq.refl Nat (iterAdd w C (Nat.succ k)))))))
      (hoare_skip w (mulInv w C (Nat.succ k)))

-- THE COUNTED LOOP, UNCONDITIONAL.  Running `mulBody` `n` times advances the
-- invariant from `mulInv w C 0` to `mulInv w C n` -- i.e. from `r0 = 0` to
-- `r0 = iterAdd w C n` -- for EVERY trip count `n`, with NO precondition.  This
-- is `hoare_repeat_indexed` fed the per-step triple `mulBody_step`.
theorem mul_loop_machine (w C : Nat) :
    forall (n : Nat),
      Hoare w (mulInv w C 0) (repeatR n mulBody) (mulInv w C n) :=
  hoare_repeat_indexed w (mulInv w C) mulBody (mulBody_step w C)

-- PURE-ARITHMETIC BRIDGE: the machine recurrence COINCIDES with multiplication
-- when the product fits.  `C*k < 2^w  ->  iterAdd w C k = C*k`, by `@Nat.rec` on
-- `k`.  Base: `iterAdd w C 0 = 0 = C*0` (rfl).  Step (given `hb : C*(succ k) < 2^w`):
--   * The bound is DOWNWARD-CLOSED: `C*k <= C*(succ k)` (`Nat.mul C k <= Nat.mul
--     C k + C = Nat.mul C (succ k)` by `Nat.le_add_right`), so `C*k < 2^w` by
--     `Nat.le_trans`; feed that to the IH to get `iterAdd w C k = C*k`.
--   * Then `iterAdd w C (succ k) = (iterAdd w C k + C) % 2^w = (C*k + C) % 2^w`
--     (rewrite by IH) `= C*k + C` (`mod_eq_of_lt` under `hb`, since `C*k + C =
--     C*(succ k)`) `= C*(succ k)` (rfl).
theorem iterAdd_eq_mul (w C : Nat) :
    forall (k : Nat),
      (Nat.lt (Nat.mul C k) (Nat.pow 2 w) -> (@Eq Nat (iterAdd w C k) (Nat.mul C k))) :=
  fun k =>
   @Nat.rec
    (fun k => (Nat.lt (Nat.mul C k) (Nat.pow 2 w) -> (@Eq Nat (iterAdd w C k) (Nat.mul C k))))
    (fun _hb => @Eq.refl Nat 0)
    (fun k ih =>
      fun hb =>
        -- C*k < 2^w  (downward-closed from C*(succ k) < 2^w via C*k <= C*(succ k))
        Eq.trans
          (@Eq.subst Nat
            (fun (v : Nat) =>
              @Eq Nat (iterAdd w C (Nat.succ k)) (Nat.mod (Nat.add v C) (Nat.pow 2 w)))
            (iterAdd w C k)
            (Nat.mul C k)
            (ih
              (@Nat.le_trans
                (Nat.succ (Nat.mul C k))
                (Nat.succ (Nat.mul C (Nat.succ k)))
                (Nat.pow 2 w)
                (@Nat.succ_le_succ (Nat.mul C k) (Nat.mul C (Nat.succ k))
                  (Nat.le_add_right (Nat.mul C k) C))
                hb))
            (@Eq.refl Nat (iterAdd w C (Nat.succ k))))
          (mod_eq_of_lt (Nat.add (Nat.mul C k) C) (Nat.pow 2 w) hb))
    k

-- THE VERIFIED MULTIPLY (the headline result).  Under the no-overflow side
-- condition `hb : C*N < 2^w`, the program `repeatR N mulBody` (the body
-- `r0 := r0 + r1` run `N` times) computes the product EXACTLY:
--   {  r0 = 0  AND  r1 = C  }  repeatR N mulBody  {  r0 = C*N  }.
--
-- Built by `hoare_conseq` over `mul_loop_machine`:
--   * precondition: from `r0 = 0 AND r1 = C` we get `mulInv w C 0`
--     (`= r1 = C AND r0 = iterAdd w C 0`, and `iterAdd w C 0 = 0` is `rfl`).
--   * the machine triple `mul_loop_machine w C N` carries `mulInv w C 0` to
--     `mulInv w C N` (`r1 = C AND r0 = iterAdd w C N`).
--   * postcondition: `iterAdd w C N = C*N` by `iterAdd_eq_mul` under `hb`, so
--     `r0 = iterAdd w C N` rewrites to `r0 = C*N`.
theorem mul_by_addition_verified (w C N : Nat)
    (hb : Nat.lt (Nat.mul C N) (Nat.pow 2 w)) :
    Hoare w
      (fun s => And (@Eq Nat (s 0) 0) (@Eq Nat (s 1) C))
      (repeatR N mulBody)
      (fun s => @Eq Nat (s 0) (Nat.mul C N)) :=
  hoare_conseq w
    -- P
    (fun s => And (@Eq Nat (s 0) 0) (@Eq Nat (s 1) C))
    -- P' = mulInv w C 0
    (mulInv w C 0)
    -- Q
    (fun s => @Eq Nat (s 0) (Nat.mul C N))
    -- Q' = mulInv w C N
    (mulInv w C N)
    (repeatR N mulBody)
    -- P => mulInv w C 0  :  (s1 = C) AND (s0 = iterAdd w C 0 = 0)
    (fun s hp =>
      @And.intro
        (@Eq Nat (s 1) C)
        (@Eq Nat (s 0) (iterAdd w C 0))
        (@And.right
          (@Eq Nat (s 0) 0)
          (@Eq Nat (s 1) C)
          hp)
        (@And.left
          (@Eq Nat (s 0) 0)
          (@Eq Nat (s 1) C)
          hp))
    -- the machine loop triple
    (mul_loop_machine w C N)
    -- mulInv w C N => Q  :  s0 = iterAdd w C N = C*N
    (fun s hq =>
      Eq.trans
        (@And.right
          (@Eq Nat (s 1) C)
          (@Eq Nat (s 0) (iterAdd w C N))
          hq)
        (iterAdd_eq_mul w C N hb))

-- ===========================================================================
-- THE STRUCTURAL HOARE RULES (conjunction / disjunction / false).
--
-- The rules above (skip, cons, conseq, seq) build and compose triples along
-- the program structure.  The STRUCTURAL rules instead combine triples for the
-- SAME block under logical operations on the assertions -- the standard
-- conjunction, disjunction, and ex-falso rules of Hoare logic.  Each is a plain
-- lambda term in the exact named-equality-witness idiom of `Hoare`: given the
-- start store `s`, the threaded final store `s'`, the precondition witness, and
-- the equality `s' = evalWrapP w b s`, run the supplied sub-triples at the SAME
-- `(s, s')` with the SAME equality witness `h2` and combine their `Q`-witnesses.
-- All predicate applications stay against the BOUND stores `s`/`s'`.
-- Axiom-free: only `And.intro`/`And.left`/`And.right`, `Or.casesOn`, and
-- `False.elim` -- the prelude logic connectives -- plus the sub-triples.
-- ===========================================================================

-- STRUCTURAL RULE (CONJUNCTION).  If {P1} b {Q1} and {P2} b {Q2}, then running
-- `b` from a store satisfying BOTH preconditions yields a store satisfying BOTH
-- postconditions: {P1 AND P2} b {Q1 AND Q2}.  Proof: the precondition witness
-- `hp : And (P1 s) (P2 s)` splits via `And.left`/`And.right`; feed each half to
-- the matching sub-triple at the same `(s, s', h2)` to get `Q1 s'` and `Q2 s'`,
-- then `And.intro` them.
theorem hoare_conj (w : Nat) (P1 P2 Q1 Q2 : StorePred) (b : PBlock)
    (h1 : Hoare w P1 b Q1)
    (h2 : Hoare w P2 b Q2) :
    Hoare w (fun s => And (P1 s) (P2 s)) b (fun s => And (Q1 s) (Q2 s)) :=
  fun s s' hp heq =>
    @And.intro (Q1 s') (Q2 s')
      (h1 s s' (@And.left (P1 s) (P2 s) hp) heq)
      (h2 s s' (@And.right (P1 s) (P2 s) hp) heq)

-- STRUCTURAL RULE (DISJUNCTION).  If {P1} b {Q} and {P2} b {Q} (the SAME
-- postcondition), then running `b` from a store satisfying EITHER precondition
-- yields a `Q`-store: {P1 OR P2} b {Q}.  Proof: case-split the precondition
-- witness `hp : Or (P1 s) (P2 s)` with `@Or.casesOn` under the motive
-- `fun _ => Q s'`; the `inl` branch (`P1 s`) closes by `h1`, the `inr` branch
-- (`P2 s`) by `h2`, each at the same `(s, s', h2)`.
theorem hoare_disj (w : Nat) (P1 P2 Q : StorePred) (b : PBlock)
    (h1 : Hoare w P1 b Q)
    (h2 : Hoare w P2 b Q) :
    Hoare w (fun s => Or (P1 s) (P2 s)) b Q :=
  fun s s' hp heq =>
    @Or.casesOn (P1 s) (P2 s)
      (fun _ => Q s')
      hp
      (fun hp1 => h1 s s' hp1 heq)
      (fun hp2 => h2 s s' hp2 heq)

-- STRUCTURAL RULE (EX-FALSO).  From a contradictory precondition anything
-- follows: {False} b {Q} for every postcondition `Q`.  Proof: the precondition
-- witness `hp : False` discharges the goal `Q s'` directly via `@False.elim`.
theorem hoare_false (w : Nat) (Q : StorePred) (b : PBlock) :
    Hoare w (fun _ => False) b Q :=
  fun s s' hp heq => @False.elim (Q s') hp

-- ===========================================================================
-- THE SEPARATION-LOGIC FRAME RULE -- modular reasoning over a write-footprint.
--
-- The rules above combine triples for the SAME block under logical or program
-- structure.  The FRAME RULE is the cornerstone of modular verification: it
-- lets a triple `{P} c {Q}` be lifted to `{P AND R} c {Q AND R}` for ANY
-- predicate `R` that reads only cells the program `c` does NOT write.  The
-- predicate `R` ("the frame") is carried across the program untouched -- so a
-- piece of program can be verified against its OWN footprint, then composed
-- into a larger context whose extra state `R` it provably leaves alone.
--
-- We model a program's write-footprint as a Bool-predicate on addresses (an
-- `AddrSet`): `W r = true` means "c may write cell r", `W r = false` means
-- "c provably leaves cell r unchanged".  Two side conditions tie `R` and `c`
-- to the same footprint `W`:
--   * `writesOnly w c W` -- c touches no cell outside W (every `W r = false`
--     cell is unchanged by `evalWrapP w c`);
--   * `framedOff R W`    -- R is supported outside W (R transfers between any
--     two stores that agree on all `W r = false` cells).
-- Both are spelled with explicit `forall (_ : ..)` binders and apply the store
-- predicates only to BOUND store variables, in the same robustness idiom as
-- `Hoare`.  `AddrSet` aliases `(Nat -> Bool)` so the higher-order footprint
-- appears as a plain named constant in binder/domain position (the elaborator
-- handles a named constant where it chokes on a nested arrow), exactly as
-- `StorePred` aliases `(Nat -> Nat) -> Prop`.
-- ===========================================================================

-- A WRITE-FOOTPRINT: a Bool-predicate on addresses.  `W r = true` flags a cell
-- the program may write; `W r = false` flags a cell it provably leaves alone.
def AddrSet : Type := Nat -> Bool

-- FOOTPRINT SOUNDNESS for a program: `c` writes only within `W`, i.e. every
-- cell `r` with `W r = false` reads back UNCHANGED after running `c` from any
-- store `s`.  (`evalWrapP w c s r = s r` whenever `W r = false`.)
def writesOnly (w : Nat) (c : PBlock) (W : AddrSet) : Prop :=
  forall (s : (Nat -> Nat)), forall (r : Nat),
    forall (_hr : @Eq Bool (W r) Bool.false),
      @Eq Nat (evalWrapP w c s r) (s r)

-- FRAME SOUNDNESS for a predicate: `R` is supported OUTSIDE `W` -- if two stores
-- `s` and `s2` agree on every cell `r` with `W r = false`, then `R` transfers
-- from `s` to `s2`.  (R reads only `W r = false` cells, so cells inside W are
-- irrelevant to it.)
def framedOff (R : StorePred) (W : AddrSet) : Prop :=
  forall (s : (Nat -> Nat)), forall (s2 : (Nat -> Nat)),
    forall (_hag : forall (r : Nat),
      forall (_hr : @Eq Bool (W r) Bool.false), @Eq Nat (s r) (s2 r)),
    forall (_hR : R s), R s2

-- THE FRAME RULE.  From `{P} c {Q}`, a footprint `W` that bounds c's writes
-- (`writesOnly`), and a frame `R` supported off that footprint (`framedOff`),
-- derive `{P AND R} c {Q AND R}`: running `c` from a store satisfying both `P`
-- and the frame `R` yields a store satisfying both `Q` and the SAME `R`.
--
-- Proof (the `hoare_conj` named-witness idiom).  Given the start store `s`, the
-- threaded final store `s'`, the precondition `hp : And (P s) (R s)`, and the
-- equality `heq : s' = evalWrapP w c s`:
--   * split `hp` -> `hP = And.left : P s`, `hR = And.right : R s`;
--   * `Q s'` is `h s s' hP heq` (the original triple at the same `(s, s')`);
--   * `R s'`: first prove `R (evalWrapP w c s)` by `hr` applied to `s` and the
--     post store `evalWrapP w c s`, with the agreement obligation
--       `fun r hrW => Eq.symm (hw s r hrW) : s r = evalWrapP w c s r`
--     (the two stores agree on every `W r = false` cell, since `hw` says `c`
--     leaves exactly those cells alone), fed `hR`.  Then transport along
--     `Eq.symm heq : evalWrapP w c s = s'` via `@Eq.subst` with motive `R` to
--     land `R s'`.
--   * `And.intro (Q s') (R s')`.
-- Predicates `P`/`Q`/`R` are applied only to the bound stores `s`/`s'` (and the
-- bound post store inside the frame transport), keeping every application a
-- predicate-against-a-bound-variable as the elaborator requires.
theorem hoare_frame (w : Nat) (P Q R : StorePred) (c : PBlock) (W : AddrSet)
    (h : Hoare w P c Q)
    (hw : writesOnly w c W)
    (hr : framedOff R W) :
    Hoare w (fun s => And (P s) (R s)) c (fun s => And (Q s) (R s)) :=
  fun s s' hp heq =>
    @And.intro (Q s') (R s')
      (h s s' (@And.left (P s) (R s) hp) heq)
      (@Eq.subst (Nat -> Nat) R (evalWrapP w c s) s'
        (Eq.symm heq)
        (hr s (evalWrapP w c s)
          (fun r hrW => Eq.symm (hw s r hrW))
          (@And.right (P s) (R s) hp)))

-- ===========================================================================
-- THE FRAME RULE IN ACTION -- a concrete framed triple (modular verification).
--
-- `frameBody` is the one-instruction program `r1 := r0 + r0` (`pmk 1 0 0 padd`)
-- -- it writes ONLY cell 1.  We discharge both side conditions concretely for
-- the footprint `W = (fun r => Nat.beq r 1)` (the singleton {1}), then frame a
-- predicate about cell 2 across it: cell 2 is provably untouched, so a fact
-- `s 2 = c` survives the program unchanged.  This is the modular-verification
-- workflow: verify `frameBody` against its own footprint once, then carry an
-- arbitrary disjoint fact (here `s 2 = c`) through it for free.
-- ===========================================================================

-- The framed program: `r1 := r0 + r0`.  Writes only register 1.
def frameBody : PBlock := PBlock.pbcons (PInst.pmk 1 0 0 POp.padd) PBlock.pbnil

-- FOOTPRINT SOUNDNESS for `frameBody`: it writes only within {1}.  For any cell
-- `r` with `Nat.beq r 1 = false`, `evalWrapP w frameBody s r` def-reduces to
-- `writeReg s 1 (wrapPBinOp padd w (s 0) (s 0)) r` (run the single instruction,
-- then the empty tail), and `writeReg_other` (cell `r` differs from the written
-- cell 1, witnessed by `hr : Nat.beq r 1 = false`) reads it back as `s r`.
theorem frameBody_writesOnly (w : Nat) :
    writesOnly w frameBody (fun r => Nat.beq r 1) :=
  fun s r hr =>
    writeReg_other s 1 (wrapPBinOp POp.padd w (s 0) (s 0)) r hr

-- FRAME SOUNDNESS for a cell-2 predicate.  `R = (fun s => s 2 = c)` reads only
-- cell 2, which is outside the footprint {1}: `Nat.beq 2 1` reduces to
-- `Bool.false` by `rfl`, so the agreement hypothesis instantiated at `r = 2`
-- gives `s 2 = s2 2`.  Then `s 2 = c` (the witness `hR`) rewrites along that
-- agreement (`@Eq.subst` with motive `fun n => n = c`) to `s2 2 = c`.
theorem frameR_framedOff (c : Nat) :
    framedOff (fun s => @Eq Nat (s 2) c) (fun r => Nat.beq r 1) :=
  fun s s2 hag hR =>
    @Eq.subst Nat (fun n => @Eq Nat n c) (s 2) (s2 2)
      (hag 2 (@Eq.refl Bool Bool.false))
      hR

-- THE HEADLINE: a concrete FRAMED triple, assembled from an existing triple by
-- the frame rule.  `double_verified w` proves `{ r0+r0 fits } frameBody { r1 =
-- r0+r0 }`.  Framing the disjoint fact `s 2 = c` across it (the footprint {1}
-- bounds frameBody's writes by `frameBody_writesOnly`, and `s 2 = c` is framed
-- off {1} by `frameR_framedOff`) yields, with ZERO re-proof of the program:
--   { (r0+r0 fits) AND (r2 = c) } frameBody { (r1 = r0+r0) AND (r2 = c) }.
-- The cell-2 fact is carried through the program for free -- modular
-- verification in action.
theorem frame_example (w : Nat) (c : Nat) :
    Hoare w
      (fun s => And (Nat.lt (Nat.add (s 0) (s 0)) (Nat.pow 2 w)) (@Eq Nat (s 2) c))
      frameBody
      (fun s => And (@Eq Nat (s 1) (Nat.add (s 0) (s 0))) (@Eq Nat (s 2) c)) :=
  hoare_frame w
    (fun s => Nat.lt (Nat.add (s 0) (s 0)) (Nat.pow 2 w))
    (fun s => @Eq Nat (s 1) (Nat.add (s 0) (s 0)))
    (fun s => @Eq Nat (s 2) c)
    frameBody
    (fun r => Nat.beq r 1)
    (double_verified w)
    (frameBody_writesOnly w)
    (frameR_framedOff c)

-- ===========================================================================
-- A VERIFIED EXPONENTIAL ALGORITHM: COMPUTE 2^N BY REPEATED DOUBLING.
--
-- The headline EXPONENTIAL application of the counted loop rule.  The loop body
-- is the single instruction `r0 := r0 + r0` (`pmk 0 0 0 padd`).  Starting from
-- r0 = 1, running the body `N` times DOUBLES r0 each iteration -- computing
-- `2^N`.  We verify this for EVERY trip count `N` (under no-overflow).
--
-- This reuses the ENTIRE method of `mul_by_addition_verified` (the counted-loop
-- rule `hoare_repeat_indexed`, the machine-recurrence-indexed invariant, the
-- final `hoare_conseq` collapse to the closed form under a DOWNWARD-CLOSED
-- no-overflow bound).  Doubling instead of `+C`; `2^k` instead of `C*k`.
--
-- As with the accumulator, the exact value `2^k` grows without bound, so the
-- only self-preserving invariant is the MACHINE recurrence itself:
-- `iterDbl w k` is the k-fold wrapping doubling `(· + ·) % 2^w` from 1, which
-- matches the body step DEFINITIONALLY at register 0
-- (`iterDbl w (succ k) = (iterDbl w k + iterDbl w k) % 2^w`, rfl).  The
-- counted-loop triple closes with NO precondition; the loop computes
-- `iterDbl w N` for every `N`.  We then prove, as a PURE-ARITHMETIC lemma, that
-- this machine recurrence COINCIDES with `2^k` whenever it fits:
-- `2^k < 2^w  ->  iterDbl w k = 2^k`.  `hoare_conseq` finally weakens the
-- machine-recurrence postcondition to the exact power `2^N` under `2^N < 2^w`.
-- ===========================================================================

-- THE MACHINE RECURRENCE.  `iterDbl w k` = double 1 (wrapping at width `w`)
-- exactly `k` times:
--   iterDbl w 0        = 1
--   iterDbl w (succ k) = (iterDbl w k + iterDbl w k) % 2^w.
-- Both reductions are `rfl`; the `succ` reduction is EXACTLY the body step.
def iterDbl : Nat -> Nat -> Nat :=
  fun w k =>
    @Nat.rec (fun _ => Nat)
      1
      (fun _ ih => (Nat.add ih ih) % (2 ^ w))
      k

-- THE LOOP BODY: `r0 := r0 + r0` (add register 0 into itself -- a doubling).
def dblBody : PBlock := PBlock.pbcons (PInst.pmk 0 0 0 POp.padd) PBlock.pbnil

-- THE COUNTER-INDEXED INVARIANT.  After `k` iterations r0 holds the k-fold
-- machine doubling `iterDbl w k`.
def dblInv (w : Nat) : Nat -> StorePred :=
  fun k => fun s => @Eq Nat (s 0) (iterDbl w k)

-- PER-STEP PRESERVATION: one body iteration advances the indexed invariant from
-- `k` to `succ k`.  The body writes r0 := `wrapPBinOp padd w (s 0) (s 0)` =
-- `(s 0 + s 0) % 2^w`.  Under `dblInv ... k` (`s 0 = iterDbl w k`):
--   * r0 read-back: `writeReg_same` gives `s' 0 = (s 0 + s 0) % 2^w`; rewriting
--     `s 0` to `iterDbl w k` (one `Eq.subst`) turns it into
--     `(iterDbl w k + iterDbl w k) % 2^w`, which is `iterDbl w (succ k)`
--     DEFINITIONALLY (the `succ` reduction of `iterDbl`).  No no-overflow
--     reasoning is needed -- the spec IS the wrapping recurrence.
theorem dblBody_step (w : Nat) :
    forall (k : Nat), Hoare w (dblInv w k) dblBody (dblInv w (Nat.succ k)) :=
  fun k =>
    hoare_cons w
      (dblInv w k)
      (dblInv w (Nat.succ k))
      (dblInv w (Nat.succ k))
      (PInst.pmk 0 0 0 POp.padd)
      PBlock.pbnil
      (fun s hp =>
        -- r0 = wrapPBinOp padd w (s0) (s0).  Rewrite s0 -> iterDbl w k; the
        -- result `wrapPBinOp padd w (iterDbl w k) (iterDbl w k)` is DEFINITIONALLY
        -- `(iterDbl w k + iterDbl w k) % 2^w` = `iterDbl w (succ k)` (final Eq.refl).
        (Eq.trans
          (writeReg_same s 0 (wrapPBinOp POp.padd w (s 0) (s 0)))
          (@Eq.subst Nat
            (fun (u : Nat) =>
              @Eq Nat (wrapPBinOp POp.padd w u u) (iterDbl w (Nat.succ k)))
            (iterDbl w k)
            (s 0)
            (Eq.symm hp)
            (@Eq.refl Nat (iterDbl w (Nat.succ k))))))
      (hoare_skip w (dblInv w (Nat.succ k)))

-- THE COUNTED LOOP, UNCONDITIONAL.  Running `dblBody` `n` times advances the
-- invariant from `dblInv w 0` to `dblInv w n` -- i.e. from `r0 = 1` to
-- `r0 = iterDbl w n` -- for EVERY trip count `n`, with NO precondition.  This
-- is `hoare_repeat_indexed` fed the per-step triple `dblBody_step`.
theorem dbl_loop_machine (w : Nat) :
    forall (n : Nat),
      Hoare w (dblInv w 0) (repeatR n dblBody) (dblInv w n) :=
  hoare_repeat_indexed w (dblInv w) dblBody (dblBody_step w)

-- PURE-ARITHMETIC HELPER: `2^(succ j) = 2^j + 2^j`.  The kernel reduces
-- `Nat.pow 2 (succ j)` to `Nat.mul (Nat.pow 2 j) 2` (rfl), and `Nat.mul x 2`
-- to `Nat.add (Nat.add 0 x) x` (rfl, since `Nat.mul` recurses on its second
-- argument).  The remaining `Nat.add 0 (2^j)` is collapsed to `2^j` by
-- `Nat.zero_add` (one `Eq.subst`), giving `2^j + 2^j`.
theorem two_pow_succ (j : Nat) :
    @Eq Nat (Nat.pow 2 (Nat.succ j)) (Nat.add (Nat.pow 2 j) (Nat.pow 2 j)) :=
  @Eq.subst Nat
    (fun (z : Nat) =>
      @Eq Nat (Nat.pow 2 (Nat.succ j)) (Nat.add z (Nat.pow 2 j)))
    (Nat.add 0 (Nat.pow 2 j))
    (Nat.pow 2 j)
    (Nat.zero_add (Nat.pow 2 j))
    (@Eq.refl Nat (Nat.pow 2 (Nat.succ j)))

-- PURE-ARITHMETIC BRIDGE: the machine recurrence COINCIDES with `2^k` when the
-- power fits.  `2^k < 2^w  ->  iterDbl w k = 2^k`, by `@Nat.rec` on `k`.
-- Base: `iterDbl w 0 = 1 = 2^0` (rfl).  Step (given `hb : 2^(succ k) < 2^w`):
--   * The bound is DOWNWARD-CLOSED: `2^k <= 2^(succ k)`.  By `two_pow_succ`,
--     `2^(succ k) = 2^k + 2^k`, and `2^k <= 2^k + 2^k` by `Nat.le_add_right`;
--     transporting along `two_pow_succ` (Eq.subst) gives `2^k <= 2^(succ k)`,
--     so `2^k < 2^w` by `Nat.le_trans` with `hb`; feed that to the IH to get
--     `iterDbl w k = 2^k`.
--   * Then `iterDbl w (succ k) = (iterDbl w k + iterDbl w k) % 2^w
--     = (2^k + 2^k) % 2^w` (rewrite by IH) `= 2^k + 2^k` (`mod_eq_of_lt`, since
--     `2^k + 2^k = 2^(succ k) < 2^w` by `two_pow_succ` + `hb`) `= 2^(succ k)`
--     (Eq.symm two_pow_succ).
theorem iterDbl_eq_pow (w : Nat) :
    forall (k : Nat),
      (Nat.lt (Nat.pow 2 k) (Nat.pow 2 w) -> (@Eq Nat (iterDbl w k) (Nat.pow 2 k))) :=
  fun k =>
   @Nat.rec
    (fun k => (Nat.lt (Nat.pow 2 k) (Nat.pow 2 w) -> (@Eq Nat (iterDbl w k) (Nat.pow 2 k))))
    (fun _hb => @Eq.refl Nat 1)
    (fun k ih =>
      fun hb =>
        -- 2^k < 2^w  (downward-closed: 2^k <= 2^(succ k) = 2^k + 2^k, then < 2^w)
        Eq.trans
          (Eq.trans
            (@Eq.subst Nat
              (fun (v : Nat) =>
                @Eq Nat (iterDbl w (Nat.succ k)) (Nat.mod (Nat.add v v) (Nat.pow 2 w)))
              (iterDbl w k)
              (Nat.pow 2 k)
              (ih
                (@Nat.le_trans
                  (Nat.succ (Nat.pow 2 k))
                  (Nat.succ (Nat.pow 2 (Nat.succ k)))
                  (Nat.pow 2 w)
                  (@Nat.succ_le_succ (Nat.pow 2 k) (Nat.pow 2 (Nat.succ k))
                    (@Eq.subst Nat
                      (fun (z : Nat) => Nat.le (Nat.pow 2 k) z)
                      (Nat.add (Nat.pow 2 k) (Nat.pow 2 k))
                      (Nat.pow 2 (Nat.succ k))
                      (Eq.symm (two_pow_succ k))
                      (Nat.le_add_right (Nat.pow 2 k) (Nat.pow 2 k))))
                  hb))
              (@Eq.refl Nat (iterDbl w (Nat.succ k))))
            (mod_eq_of_lt (Nat.add (Nat.pow 2 k) (Nat.pow 2 k)) (Nat.pow 2 w)
              (@Eq.subst Nat
                (fun (z : Nat) => Nat.lt z (Nat.pow 2 w))
                (Nat.pow 2 (Nat.succ k))
                (Nat.add (Nat.pow 2 k) (Nat.pow 2 k))
                (two_pow_succ k)
                hb)))
          (Eq.symm (two_pow_succ k)))
    k

-- THE VERIFIED EXPONENTIAL (the headline result).  Under the no-overflow side
-- condition `hb : 2^N < 2^w`, the program `repeatR N dblBody` (the body
-- `r0 := r0 + r0` run `N` times) computes the power EXACTLY:
--   {  r0 = 1  }  repeatR N dblBody  {  r0 = 2^N  }.
--
-- Built by `hoare_conseq` over `dbl_loop_machine`:
--   * precondition: `r0 = 1` is `dblInv w 0` (`= r0 = iterDbl w 0`, and
--     `iterDbl w 0 = 1` is `rfl`).
--   * the machine triple `dbl_loop_machine w N` carries `dblInv w 0` to
--     `dblInv w N` (`r0 = iterDbl w N`).
--   * postcondition: `iterDbl w N = 2^N` by `iterDbl_eq_pow` under `hb`, so
--     `r0 = iterDbl w N` rewrites to `r0 = 2^N`.
theorem pow2_by_doubling_verified (w N : Nat)
    (hb : Nat.lt (Nat.pow 2 N) (Nat.pow 2 w)) :
    Hoare w
      (fun s => @Eq Nat (s 0) 1)
      (repeatR N dblBody)
      (fun s => @Eq Nat (s 0) (Nat.pow 2 N)) :=
  hoare_conseq w
    -- P = (s0 = 1)
    (fun s => @Eq Nat (s 0) 1)
    -- P' = dblInv w 0  (= s0 = iterDbl w 0 = 1)
    (dblInv w 0)
    -- Q = (s0 = 2^N)
    (fun s => @Eq Nat (s 0) (Nat.pow 2 N))
    -- Q' = dblInv w N  (= s0 = iterDbl w N)
    (dblInv w N)
    (repeatR N dblBody)
    -- P => dblInv w 0  :  s0 = 1 = iterDbl w 0 (rfl)
    (fun s hp => hp)
    -- the machine loop triple
    (dbl_loop_machine w N)
    -- dblInv w N => Q  :  s0 = iterDbl w N = 2^N
    (fun s hq =>
      Eq.trans hq (iterDbl_eq_pow w N hb))

-- ===========================================================================
-- A CONDITIONAL (if-then-else) CONSTRUCT + ITS SOUND HOARE RULE -- verifying
-- BRANCHING programs.
--
-- Everything above verifies straight-line / counted-loop programs.  Real
-- programs BRANCH: run one of two sub-blocks depending on a runtime test.  We
-- add `evalIte` -- run `thenB` when a guard register is NONZERO, else `elseB` --
-- built directly on the audited wrapping interpreter `evalWrapP` via
-- `Bool.casesOn` on the prelude decider `Nat.beq (s cond) 0`.  Then we prove the
-- SOUND CONDITIONAL RULE `hoare_ite`: to verify the whole conditional against a
-- postcondition `Q`, verify each branch under the precondition REFINED by the
-- guard it took (`thenB` under `0 < s cond`, `elseB` under `s cond = 0`).  A
-- kernel-checked proof of the resulting triple certifies a BRANCHING program
-- meets its spec.  Axiom-free: the rule is `Bool.casesOn` case analysis over the
-- guard plus two self-proved `Nat.beq`-vs-`Eq`/`lt` bridges (the prelude lacks
-- `Nat.eq_of_beq_eq_true`, so we build the zero-specialised bridges by
-- `Nat.rec` + `Bool.noConfusion`, mirroring the kernel's own construction).
-- ===========================================================================

-- BRIDGE (true side): `Nat.beq a 0 = true` means `a = 0`.  `Nat.rec` on `a`:
--   * a = 0: goal `0 = 0` is `Eq.refl 0` (the hypothesis is unused).
--   * a = succ k: `Nat.beq (succ k) 0` reduces to `Bool.false`, so the
--     hypothesis `hk : Bool.false = Bool.true` is absurd -- `Bool.noConfusion`
--     produces the goal from the false-vs-true equality.
theorem nat_eq_zero_of_beq_zero (a : Nat)
    (h : @Eq Bool (Nat.beq a 0) Bool.true) : @Eq Nat a 0 :=
  @Nat.rec
    (fun a => @Eq Bool (Nat.beq a 0) Bool.true -> @Eq Nat a 0)
    (fun _h => @Eq.refl Nat 0)
    (fun k _ih => fun hk =>
      @Bool.noConfusion (@Eq Nat (Nat.succ k) 0) Bool.false Bool.true hk)
    a
    h

-- BRIDGE (false side): `Nat.beq a 0 = false` means `a` is NONZERO, i.e.
-- `0 < a`.  `Nat.rec` on `a`:
--   * a = 0: `Nat.beq 0 0` reduces to `Bool.true`, so the hypothesis
--     `h0 : Bool.true = Bool.false` is absurd -- `Bool.noConfusion`.
--   * a = succ k: goal `0 < succ k` is `Nat.zero_lt_succ k` (hypothesis unused).
theorem nat_lt_of_beq_zero_false (a : Nat)
    (h : @Eq Bool (Nat.beq a 0) Bool.false) : Nat.lt 0 a :=
  @Nat.rec
    (fun a => @Eq Bool (Nat.beq a 0) Bool.false -> Nat.lt 0 a)
    (fun h0 => @Bool.noConfusion (Nat.lt 0 0) Bool.true Bool.false h0)
    (fun k _ih => fun _hk => Nat.zero_lt_succ k)
    a
    h

-- THE CONDITIONAL CARRIER.  `evalIte w cond thenB elseB s` runs `thenB` from `s`
-- when the guard register `cond` is NONZERO (`Nat.beq (s cond) 0 = false`, the
-- Bool.casesOn FALSE branch), and `elseB` when it is ZERO (`= true`, the TRUE
-- branch).  Built on the audited wrapping interpreter `evalWrapP`; the motive is
-- the constant `(Nat -> Nat)` so the recursor takes the `.{1}` motive.
def evalIte (w : Nat) (cond : Nat) (thenB elseB : PBlock) (s : (Nat -> Nat)) : (Nat -> Nat) :=
  @Bool.casesOn.{1} (fun _ => (Nat -> Nat)) (Nat.beq (s cond) 0)
    (evalWrapP w thenB s)
    (evalWrapP w elseB s)

-- THE CONDITIONAL HOARE TRIPLE.  `HoareIte w cond thenB elseB P Q` := running the
-- conditional at width `w` from any `P`-store lands in a `Q`-store.  Same
-- named-equality-witness idiom as `Hoare` (the result store is pinned to a bound
-- `s'` so the postcondition `Q` only ever applies to a bound variable).
def HoareIte (w : Nat) (cond : Nat) (thenB elseB : PBlock) (P Q : StorePred) : Prop :=
  forall (s : (Nat -> Nat)), forall (s' : (Nat -> Nat)),
    forall (_h1 : P s),
    forall (_h2 : @Eq (Nat -> Nat) s' (evalIte w cond thenB elseB s)), Q s'

-- THE SOUND CONDITIONAL RULE (the headline).  To verify `{P} (if cond then thenB
-- else elseB) {Q}`, verify each branch under the precondition REFINED by the
-- guard value that selects it:
--   * `hthen`: from `P s` AND `0 < s cond` (guard nonzero), `thenB` reaches `Q`;
--   * `helse`: from `P s` AND `s cond = 0` (guard zero), `elseB` reaches `Q`.
-- Both branch hypotheses are stated in the named-witness style (postcondition
-- applied to the bound result store `t`/`u`), exactly as `Hoare` is.
--
-- Proof: given the start store `s`, the threaded final store `s'`, `h1 : P s`,
-- and `h2 : s' = evalIte w cond thenB elseB s`, CASE-SPLIT the guard
-- `Nat.beq (s cond) 0` with `@Bool.casesOn` under the motive
--   fun b => forall s', s' = @Bool.casesOn .. b (evalWrapP w thenB s)
--                                               (evalWrapP w elseB s) -> Q s'
-- (so the motive at `Nat.beq (s cond) 0` is def-eq to the obligation
-- `s' = evalIte .. -> Q s'`, the motive at `Bool.false` is the thenB obligation,
-- at `Bool.true` the elseB obligation):
--   * FALSE branch (`Nat.beq (s cond) 0 = false`, guard nonzero): the equality
--     witness reads `s' = evalWrapP w thenB s`; `nat_lt_of_beq_zero_false`
--     converts the branch's defining `Nat.beq (s cond) 0 = false` to
--     `0 < s cond`, then `hthen s s' h1 (that) heq` lands `Q s'`.
--   * TRUE branch (`Nat.beq (s cond) 0 = true`, guard zero): the witness reads
--     `s' = evalWrapP w elseB s`; `nat_eq_zero_of_beq_zero` converts to
--     `s cond = 0`, then `helse s s' h1 (that) heq` lands `Q s'`.
-- Inside each branch the deciding equality (`Nat.beq (s cond) 0 = false`/`true`)
-- is `Eq.refl` -- the branch FIXES that Bool literal, so the bridge premise is
-- discharged definitionally.
theorem hoare_ite (w : Nat) (cond : Nat) (thenB elseB : PBlock) (P Q : StorePred)
    (hthen : forall (s : (Nat -> Nat)), forall (t : (Nat -> Nat)),
      forall (_hp : P s), forall (_hg : Nat.lt 0 (s cond)),
      forall (_ht : @Eq (Nat -> Nat) t (evalWrapP w thenB s)), Q t)
    (helse : forall (s : (Nat -> Nat)), forall (u : (Nat -> Nat)),
      forall (_hp : P s), forall (_hg : @Eq Nat (s cond) 0),
      forall (_hu : @Eq (Nat -> Nat) u (evalWrapP w elseB s)), Q u) :
    HoareIte w cond thenB elseB P Q :=
  fun s s' h1 h2 =>
    @Bool.casesOn
      -- Motive threads BOTH the result-store equation (parametric in `b`) AND a
      -- proof that the guard `Nat.beq (s cond) 0` equals the case constructor
      -- `b`.  At the scrutinee `Nat.beq (s cond) 0` the guard premise is
      -- `Eq.refl`; inside the FALSE/TRUE branch it specialises to
      -- `Nat.beq (s cond) 0 = Bool.false`/`= Bool.true`, which the bridges need.
      (fun b =>
        forall (_he : @Eq (Nat -> Nat) s'
          (@Bool.casesOn.{1} (fun _ => (Nat -> Nat)) b
            (evalWrapP w thenB s) (evalWrapP w elseB s))),
        forall (_hb : @Eq Bool (Nat.beq (s cond) 0) b), Q s')
      (Nat.beq (s cond) 0)
      -- FALSE branch: guard nonzero -> thenB.  `hb : Nat.beq (s cond) 0 = false`
      -- feeds `nat_lt_of_beq_zero_false` to get `0 < s cond`.
      (fun heq hb =>
        hthen s s' h1
          (nat_lt_of_beq_zero_false (s cond) hb)
          heq)
      -- TRUE branch: guard zero -> elseB.  `hb : Nat.beq (s cond) 0 = true`
      -- feeds `nat_eq_zero_of_beq_zero` to get `s cond = 0`.
      (fun heq hb =>
        helse s s' h1
          (nat_eq_zero_of_beq_zero (s cond) hb)
          heq)
      h2
      (@Eq.refl Bool (Nat.beq (s cond) 0))

-- THE BRANCHING REFLECTION IN ACTION: a CONCRETE VERIFIED CONDITIONAL.
-- The conditional chooses, on guard register `r0`, between
--   thenB = `r1 := r0 + r0`  (the one-instruction doubling block)  and
--   elseB = `pbnil`          (do nothing).
-- Spec, at every width: keeping r1 in range is preserved across BOTH branches.
--   P = (s1 < 2^w)   -- r1 starts in range
--   Q = (s1 < 2^w)   -- r1 stays in range
-- thenB writes r1 := (r0+r0) % 2^w, which is in range by `writeReg_inRange` /
-- `wrapPBinOp_in_range` (`mod_lt`); elseB leaves r1 untouched so the
-- precondition carries over unchanged.  A genuinely branch-dependent triple:
-- the postcondition is re-established by DIFFERENT reasoning in each arm, yet
-- `hoare_ite` assembles the whole-conditional certificate.
theorem ite_example_verified (w : Nat) :
    HoareIte w 0
      (PBlock.pbcons (PInst.pmk 1 0 0 POp.padd) PBlock.pbnil)
      PBlock.pbnil
      (fun s => Nat.lt (s 1) (Nat.pow 2 w))
      (fun s => Nat.lt (s 1) (Nat.pow 2 w)) :=
  hoare_ite w 0
    (PBlock.pbcons (PInst.pmk 1 0 0 POp.padd) PBlock.pbnil)
    PBlock.pbnil
    (fun s => Nat.lt (s 1) (Nat.pow 2 w))
    (fun s => Nat.lt (s 1) (Nat.pow 2 w))
    -- THEN branch (guard r0 nonzero): run `r1 := r0+r0`.  The result store is
    -- `t = evalWrapP w thenB s = writeReg s 1 ((s0+s0)%2^w)`; reading r1 back is
    -- that mod value, in range by `mod_lt`.  Transport `Q t` (= `t 1 < 2^w`)
    -- along the threaded equality `ht : t = evalWrapP w thenB s`.
    (fun s t hp _hg ht =>
      @Eq.subst (Nat -> Nat)
        (fun (z : (Nat -> Nat)) => Nat.lt (z 1) (Nat.pow 2 w))
        (evalWrapP w (PBlock.pbcons (PInst.pmk 1 0 0 POp.padd) PBlock.pbnil) s)
        t
        (Eq.symm ht)
        (@Eq.subst Nat
          (fun (v : Nat) => Nat.lt v (Nat.pow 2 w))
          (wrapPBinOp POp.padd w (s 0) (s 0))
          ((evalWrapP w (PBlock.pbcons (PInst.pmk 1 0 0 POp.padd) PBlock.pbnil) s) 1)
          (Eq.symm (writeReg_same s 1 (wrapPBinOp POp.padd w (s 0) (s 0))))
          (@Eq.subst Nat
            (fun (m : Nat) => Nat.lt m (Nat.pow 2 w))
            (Nat.mod (Nat.add (s 0) (s 0)) (Nat.pow 2 w))
            (wrapPBinOp POp.padd w (s 0) (s 0))
            (Eq.symm (wrapPBinOp_eq_mod POp.padd w (s 0) (s 0)))
            (mod_lt (Nat.add (s 0) (s 0)) (Nat.pow 2 w) (two_pow_pos w)))))
    -- ELSE branch (guard r0 zero): do nothing.  `u = evalWrapP w pbnil s = s`,
    -- so `Q u` (= `u 1 < 2^w`) is the precondition `hp : s 1 < 2^w` transported
    -- along `hu : u = s`.
    (fun s u hp _hg hu =>
      @Eq.subst (Nat -> Nat)
        (fun (z : (Nat -> Nat)) => Nat.lt (z 1) (Nat.pow 2 w))
        s
        u
        (Eq.symm hu)
        hp)

-- ===========================================================================
-- CFG-INVARIANT METATHEOREM: an invariant preserved by every block's step is
-- preserved throughout the WHOLE control-flow graph execution (any fuel, any
-- entry block, any terminator wiring -> any branching and looping).  This lifts
-- the per-block "step soundness" property to a whole-program guarantee over the
-- REAL fuel-bounded CFG interpreter `runProg`, with NO assumption on the shape
-- of the CFG: the terminator function `terms` is arbitrary, so the proof covers
-- every possible branch/loop structure.
--
-- Proven by induction on `fuel` (motive a Prop), exactly mirroring the
-- structural case-split of `runProg_congr` (Term/Bool `casesOn`) but with the
-- equality goal swapped for `Inv (...)`:
--   * fuel = 0:    `runProg 0 ... bid e = e` (rfl), so goal is `Inv e -> Inv e`.
--   * fuel = succ: `runProg (succ f) ...` reduces (rfl) to the Term.casesOn of
--       the terminator.  `Inv (step bid e)` holds by `h bid e hi`.  Case-split
--       `terms bid`: `tret` returns `step bid e` (closed by `h`); `tbr target`
--       recurses to `target` (closed by `ih target ...`); `tcondBr` branches on
--       the condition register via Bool.casesOn, each side closed by `ih`.
-- ===========================================================================
-- Operational-semantics reduction (succ): one fuel-step unfolds `runProg` into
-- the terminator case-split (rfl, the iota-reduction of `@Nat.rec` on `succ`).
theorem runProg_succ (f : Nat) (step : Nat -> (Nat -> Nat) -> (Nat -> Nat))
    (terms : Nat -> Term) (bid : Nat) (e : (Nat -> Nat)) :
    @Eq.{1} (Nat -> Nat) (runProg (Nat.succ f) step terms bid e)
      (@Term.casesOn.{1} (fun _ => (Nat -> Nat)) (terms bid)
        (step bid e)
        (fun target => runProg f step terms target (step bid e))
        (fun cond thn els =>
          @Bool.casesOn.{1} (fun _ => (Nat -> Nat)) (Nat.beq ((step bid e) cond) 0)
            (runProg f step terms thn (step bid e))
            (runProg f step terms els (step bid e)))) := rfl

theorem runProg_invariant (Inv : (Nat -> Nat) -> Prop)
    (step : Nat -> (Nat -> Nat) -> (Nat -> Nat)) (terms : Nat -> Term)
    (h : forall (bid : Nat) (e : (Nat -> Nat)), Inv e -> Inv (step bid e)) :
    forall (fuel : Nat) (bid : Nat) (e : (Nat -> Nat)),
      Inv e -> Inv (runProg fuel step terms bid e) :=
  @Nat.rec
    (fun fuel =>
      forall (bid : Nat) (e : (Nat -> Nat)),
        Inv e -> Inv (runProg fuel step terms bid e))
    (fun bid e hi => hi)
    (fun f IH bid e hi =>
      -- Transport `Inv (<terminator case-split>)` back along `runProg_succ`
      -- (symm) to the goal `Inv (runProg (succ f) step terms bid e)`.
      @Eq.subst (Nat -> Nat)
        (fun (z : (Nat -> Nat)) => Inv z)
        (@Term.casesOn.{1} (fun _ => (Nat -> Nat)) (terms bid)
          (step bid e)
          (fun target => runProg f step terms target (step bid e))
          (fun cond thn els =>
            @Bool.casesOn.{1} (fun _ => (Nat -> Nat)) (Nat.beq ((step bid e) cond) 0)
              (runProg f step terms thn (step bid e))
              (runProg f step terms els (step bid e))))
        (runProg (Nat.succ f) step terms bid e)
        (Eq.symm (runProg_succ f step terms bid e))
        (@Term.casesOn
          (fun tm =>
            Inv
              (@Term.casesOn.{1} (fun _ => (Nat -> Nat)) tm
                (step bid e)
                (fun target => runProg f step terms target (step bid e))
                (fun cond thn els =>
                  @Bool.casesOn.{1} (fun _ => (Nat -> Nat)) (Nat.beq ((step bid e) cond) 0)
                    (runProg f step terms thn (step bid e))
                    (runProg f step terms els (step bid e)))))
          (terms bid)
          (h bid e hi)
          (fun target => IH target (step bid e) (h bid e hi))
          (fun cond thn els =>
            @Bool.casesOn
              (fun bb =>
                Inv
                  (@Bool.casesOn.{1} (fun _ => (Nat -> Nat)) bb
                    (runProg f step terms thn (step bid e))
                    (runProg f step terms els (step bid e))))
              (Nat.beq ((step bid e) cond) 0)
              (IH thn (step bid e) (h bid e hi))
              (IH els (step bid e) (h bid e hi)))))

-- ===========================================================================
-- A CONCRETE CFG INVARIANT INSTANCE: a control-flow graph whose every block
-- performs a wrapping write keeps the store IN RANGE.  We adapt the PBlock step
-- machinery to `runProg`'s block-id-indexed step signature: every "block" runs
-- `r1 := r0 + r0` (wrapping at width `w`), which writes an in-range value.
-- ===========================================================================

-- The per-block step for the CFG: every block performs the wrapping write
-- `r1 := r0 + r0`.  Signature `Nat -> (Nat -> Nat) -> (Nat -> Nat)` matches
-- `runProg`'s `step` (block-id -> store -> store).
def cfgStep (w : Nat) : Nat -> (Nat -> Nat) -> (Nat -> Nat) :=
  fun bid s => stepWrapP w s (PInst.pmk 1 0 0 POp.padd)

-- STEP SOUNDNESS for the CFG step: every block preserves `storeInRange w`.  The
-- wrapping write stores an in-range value, so `stepWrapP_inRange` applies
-- (block id is irrelevant -- every block runs the same in-range-preserving step).
theorem cfgStep_inRange (w : Nat) (bid : Nat) (s : (Nat -> Nat))
    (hs : storeInRange w s) :
    storeInRange w (cfgStep w bid s) :=
  stepWrapP_inRange w s (PInst.pmk 1 0 0 POp.padd) hs

-- THE HEADLINE INSTANCE: a REAL invariant (`storeInRange w`) preserved through an
-- ARBITRARY control-flow graph.  For any terminator wiring `terms` (hence any
-- branching/looping structure), any fuel, any entry block, and any in-range
-- starting store, running the whole CFG yields an in-range store.  This is
-- value-level type soundness lifted from a single step to the whole CFG via the
-- axiom-free `runProg_invariant`.
theorem cfg_preserves_inRange (w : Nat) (terms : Nat -> Term) (fuel : Nat)
    (bid : Nat) (s : (Nat -> Nat)) (hs : storeInRange w s) :
    storeInRange w (runProg fuel (cfgStep w) terms bid s) :=
  runProg_invariant (storeInRange w) (cfgStep w) terms
    (fun bid e hi => cfgStep_inRange w bid e hi)
    fuel bid s hs


-- ===========================================================================
-- REFLECTION R: Trust's ACTUAL verification obligations, refuted in Clean.
--
-- Trust's `trust_certify::certify_vc` (crates/trust-certify/src/lib.rs:121)
-- takes a `VerificationCondition` whose `formula` is the VIOLATION, proves it
-- UNSAT under the program's path constraints, reconstructs a kernel-checked
-- `term : False`, and emits a `ProofEvidence::CleanCic` (trust-ir proof.rs:662).
-- We model the EXACT violation formulas Trust's `trust-vcgen` emits and prove
-- their refutation under the discharging precondition -- i.e. the SAME
-- proposition Trust's proof-carrying path certifies, here a kernel-checked Clean
-- theorem with empty non-foundational axiom closure. This is the reflection R
-- connecting this framework to Trust's real CleanCic certificates.
-- ===========================================================================

-- (A) UNSIGNED ADD OVERFLOW.  trust-vcgen/generate.rs:6980 emits, for `a + b : uN`,
-- the violation `BvULt(BvAdd(a, b, N), a, N)` -- "the wrapped sum (a+b) mod 2^N
-- is < a" (a carry-out / wrap-around occurred). On the Nat carrier the wrapped
-- sum is `(a + b) % 2^w`.
def addOverflowVC : Nat -> Nat -> Nat -> Prop :=
  fun w a b => Nat.lt (Nat.mod (Nat.add a b) (Nat.pow 2 w)) a

-- REFUTED under the no-overflow precondition (a + b < 2^w): then the wrapped sum
-- equals `a + b >= a`, so the violation `wrapped < a` is impossible. This is
-- exactly the `term : False` `certify_vc` reconstructs for the discharged VC.
theorem addOverflow_refuted (w a b : Nat) (hfit : Nat.lt (Nat.add a b) (Nat.pow 2 w))
    (hv : addOverflowVC w a b) : False :=
  Nat.lt_irrefl a
    (Nat.lt_of_le_of_lt a (Nat.add a b) a
      (Nat.le_add_right a b)
      (@Eq.subst Nat (fun z => Nat.lt z a)
        (Nat.mod (Nat.add a b) (Nat.pow 2 w)) (Nat.add a b)
        (mod_eq_of_lt (Nat.add a b) (Nat.pow 2 w) hfit) hv))

-- (B) DIVISION BY ZERO.  trust-vcgen emits the violation `Eq(b, 0)` (the divisor
-- is zero) for `a / b` / `a % b`.
def divZeroVC : Nat -> Prop := fun b => @Eq Nat b 0

-- REFUTED under the precondition `0 < b` (the divisor is provably nonzero).
theorem divZero_refuted (b : Nat) (hpos : Nat.lt 0 b) (hv : divZeroVC b) : False :=
  Nat.lt_irrefl 0 (@Eq.subst Nat (fun z => Nat.lt 0 z) b 0 hv hpos)

-- (C) INDEX OUT OF BOUNDS.  For `arr[i]`, the safe condition is `i < len`; the
-- violation Trust refutes is `Le(len, i)` (i.e. `len <= i`, since on the Nat
-- carrier `i >= 0` always holds, so the lower-bound conjunct is trivial).
def indexOobVC : Nat -> Nat -> Prop := fun i len => Nat.le len i

-- REFUTED under the in-bounds precondition `i < len`.
theorem indexOob_refuted (i len : Nat) (hlt : Nat.lt i len) (hv : indexOobVC i len) : False :=
  Nat.lt_irrefl len (Nat.lt_of_le_of_lt len i len hv hlt)

-- (D) The reflection, stated positively: under its precondition each obligation's
-- SAFE property holds. For add: the no-overflow obligation `a + b < 2^w` implies
-- the wrapped result did NOT wrap (`a <= (a+b) % 2^w`) -- the safety fact a Trust
-- consumer reads off the discharged VC.
theorem addOverflow_safe (w a b : Nat) (hfit : Nat.lt (Nat.add a b) (Nat.pow 2 w)) :
    Nat.le a (Nat.mod (Nat.add a b) (Nat.pow 2 w)) :=
  @Eq.subst Nat (fun z => Nat.le a z) (Nat.add a b) (Nat.mod (Nat.add a b) (Nat.pow 2 w))
    (Eq.symm (mod_eq_of_lt (Nat.add a b) (Nat.pow 2 w) hfit))
    (Nat.le_add_right a b)

-- (E) UNSIGNED SUB UNDERFLOW.  For `a - b : uN`, trust-vcgen's violation is
-- `BvULt(a, b, N)` -- "a < b" (the subtraction would borrow / underflow).
def subUnderflowVC : Nat -> Nat -> Prop := fun a b => Nat.lt a b

-- REFUTED under the no-underflow precondition `b <= a`.
theorem subUnderflow_refuted (a b : Nat) (hge : Nat.le b a) (hv : subUnderflowVC a b) : False :=
  Nat.lt_irrefl b (Nat.lt_of_le_of_lt b a b hge hv)

-- (F) SHIFT-AMOUNT BOUNDS.  For `a << k` / `a >> k` at width w, a shift amount
-- `k >= w` is UB; trust-vcgen's violation is `Le(w, k)` (i.e. `w <= k`).
def shiftOobVC : Nat -> Nat -> Prop := fun w k => Nat.le w k

-- REFUTED under the in-range shift-amount precondition `k < w`.
theorem shiftOob_refuted (w k : Nat) (hlt : Nat.lt k w) (hv : shiftOobVC w k) : False :=
  Nat.lt_irrefl w (Nat.lt_of_le_of_lt w k w hv hlt)

-- ===========================================================================
-- THE HOARE LOGIC DISCHARGES A VC.  This is the bridge that closes the loop:
-- the Hoare triples above prove programs CORRECT; the obligation-refutation
-- theorems above refute Trust's VCs; here a Hoare-VERIFIED program AUTOMATICALLY
-- DISCHARGES its own add-overflow VC on the RESULT store.  No extra arithmetic
-- is needed at the discharge site -- the postcondition the Hoare proof already
-- established IS the no-overflow obligation, and `addOverflow_refuted` consumes
-- it to refute the violation `(a+b) % 2^w < a` on the two registers' values in
-- the store the program produced.
--
-- We extract the postcondition at the result store via the SAME named-equality
-- witness the Hoare definition threads (`hoare_skip`/`hoare_cons` use it): run
-- `h` from `s` to the EXPLICIT post store `s' := evalWrapP w c s`, feeding the
-- trivial precondition `True.intro` for `P = (fun _ => True)` and the reflexive
-- witness `@Eq.refl (Nat -> Nat) (evalWrapP w c s)` for the equality
-- `_h2 : s' = evalWrapP w c s`.  `Q s'` then beta-reduces to
-- `Nat.lt (Nat.add ((evalWrapP w c s) ra) ((evalWrapP w c s) rb)) (Nat.pow 2 w)`
-- -- exactly the `hfit` hypothesis `addOverflow_refuted` requires on those two
-- register values.
theorem hoare_discharges_addOverflow (w : Nat) (c : PBlock) (ra rb : Nat)
    (h : Hoare w (fun s => True) c
      (fun s => Nat.lt (Nat.add (s ra) (s rb)) (Nat.pow 2 w)))
    (s : (Nat -> Nat)) :
    addOverflowVC w ((evalWrapP w c s) ra) ((evalWrapP w c s) rb) -> False :=
  addOverflow_refuted w ((evalWrapP w c s) ra) ((evalWrapP w c s) rb)
    (h s (evalWrapP w c s) True.intro (@Eq.refl (Nat -> Nat) (evalWrapP w c s)))

-- TRIVIAL-PROGRAM COROLLARY.  The empty program `pbnil` leaves the store
-- unchanged (`evalWrapP w pbnil s = s` by rfl), so verifying the no-overflow
-- postcondition over `pbnil` discharges the add-overflow VC directly on the
-- INPUT store's register values.  Built by instantiating the general bridge at
-- `c := pbnil` (the discharge specialises to `s ra`, `s rb` since the result
-- store is def-eq to `s`).
theorem hoare_discharges_addOverflow_skip (w : Nat) (ra rb : Nat)
    (h : Hoare w (fun s => True) PBlock.pbnil
      (fun s => Nat.lt (Nat.add (s ra) (s rb)) (Nat.pow 2 w)))
    (s : (Nat -> Nat)) :
    addOverflowVC w (s ra) (s rb) -> False :=
  addOverflow_refuted w (s ra) (s rb)
    (h s s True.intro (@Eq.refl (Nat -> Nat) s))

-- POSITIVE FORM.  The verified-program ⇒ safety-fact direction: a program whose
-- Hoare postcondition establishes no-overflow on `ra`/`rb` GUARANTEES the
-- wrapped sum in the result store did NOT wrap (`ra-value <= (sum) % 2^w`) --
-- the safety property a Trust consumer reads off the discharged VC, here lifted
-- through the Hoare proof to the program's actual output store.
theorem hoare_ensures_addOverflow_safe (w : Nat) (c : PBlock) (ra rb : Nat)
    (h : Hoare w (fun s => True) c
      (fun s => Nat.lt (Nat.add (s ra) (s rb)) (Nat.pow 2 w)))
    (s : (Nat -> Nat)) :
    Nat.le ((evalWrapP w c s) ra)
      (Nat.mod (Nat.add ((evalWrapP w c s) ra) ((evalWrapP w c s) rb)) (Nat.pow 2 w)) :=
  addOverflow_safe w ((evalWrapP w c s) ra) ((evalWrapP w c s) rb)
    (h s (evalWrapP w c s) True.intro (@Eq.refl (Nat -> Nat) (evalWrapP w c s)))

-- ===========================================================================
-- PART 2: TRUST'S UNSIGNED MUL-OVERFLOW VC, REFUTED.
--
-- trust-vcgen emits, for `a * b : uN`, the violation
--   And(Not(a = 0), Not(Eq(BvUDiv(BvMul(a,b,w), a, w), b)))
-- -- "a is nonzero AND the quotient-recovery test (a*b)/a = b FAILS".  On the
-- Nat carrier under no-overflow (`a*b < 2^w`): `BvMul(a,b,w) = (a*b) % 2^w = a*b`
-- (mod_eq_of_lt), so the test reduces to `(a*b)/a ≠ b`; for `0 < a` this is
-- FALSE because `(a*b)/a = b` (mul_div_cancel).  We MODEL the violation exactly
-- and REFUTE it, the same `term : False` `certify_vc` reconstructs.
--
-- The crux is `mul_div_cancel : 0 < a -> (a*b)/a = b`, GENUINE number theory.
-- `Nat.div`/`Nat.divCore` are registered as fuel-recursive structural defs in
-- this kernel (exactly like `Nat.mod`/`Nat.modCore`), so the divCore recurrence
-- reduces and the cancellation is provable from the recursor.  We build it
-- bottom-up from the same idioms `modCore_lt`/`modCore_eq_of_lt` use.
-- ===========================================================================

-- `a <= m + a`, the left-summand lower bound.  `a <= a + m` (`Nat.le_add_right`)
-- transported along commutativity `a + m = m + a` (`Nat.add_comm`).  (The
-- prelude has `Nat.le_add_right` but no `Nat.le_add_left`, so we derive it.)
theorem le_add_left_n (a m : Nat) : Nat.le a (Nat.add m a) :=
  @Eq.subst Nat (fun z => Nat.le a z) (Nat.add a m) (Nat.add m a)
    (Nat.add_comm a m) (Nat.le_add_right a m)

-- `(m + a) - a = m`, by induction on `a` (base rfl; step `succ_sub_succ` + ih).
-- `m + succ a = succ (m + a)` definitionally, so `(m + succ a) - succ a` is
-- def-eq to `(succ (m + a)) - succ a`, which `succ_sub_succ` collapses to
-- `(m + a) - a`, then ih.
theorem add_sub_cancel_r (m a : Nat) : @Eq Nat (Nat.sub (Nat.add m a) a) m :=
  @Nat.rec
    (fun k => @Eq Nat (Nat.sub (Nat.add m k) k) m)
    (@Eq.refl Nat m)
    (fun k ih => Eq.trans (succ_sub_succ (Nat.add m k) k) ih)
    a

-- `x <= y  ->  x - y = 0`, by induction on `x` generalizing `y` (the
-- `sub_pos_lt`/`key` double-rec idiom).  base `x=0`: `0 - y = 0` (zero_sub).
-- step `x = succ x'`: `y` cannot be `0` (`not_succ_le_zero`), so `y = succ y'`;
-- `succ x' - succ y' = x' - y'` (`succ_sub_succ`) `= 0` by ih on `x' <= y'`.
theorem sub_eq_zero_of_le (x y : Nat) (h : Nat.le x y) : @Eq Nat (Nat.sub x y) 0 :=
  @Nat.rec
    (fun k => forall (m : Nat), Nat.le k m -> @Eq Nat (Nat.sub k m) 0)
    (fun m _hm => zero_sub m)
    (fun x' ih =>
      fun m =>
        @Nat.rec
          (fun mm => Nat.le (Nat.succ x') mm -> @Eq Nat (Nat.sub (Nat.succ x') mm) 0)
          (fun h0 =>
            @False.elim (@Eq Nat (Nat.sub (Nat.succ x') Nat.zero) 0)
              (Nat.not_succ_le_zero x' h0))
          (fun m' _ihm hm =>
            Eq.trans (succ_sub_succ x' m')
              (ih m' (Nat.le_of_succ_le_succ x' m' hm)))
          m)
    x
    y
    h

-- `succ a' * b = 0  ->  b = 0`.  `succ a' * b` recurses on `b`; at `b = succ k`
-- it is `succ a' * k + succ a' = succ (...)`, never `0`.  Reduce via casing on
-- `b` and `Nat.noConfusion` on the succ-form numerator.
theorem mul_succ_eq_zero (a' b : Nat) (h : @Eq Nat (Nat.mul (Nat.succ a') b) 0) :
    @Eq Nat b 0 :=
  @Nat.rec
    (fun k => @Eq Nat (Nat.mul (Nat.succ a') k) 0 -> @Eq Nat k 0)
    (fun _h => @Eq.refl Nat 0)
    (fun k _ih hk =>
      -- mul (succ a') (succ k) = mul (succ a') k + succ a' = succ (mul (succ a') k + a')
      @False.elim (@Eq Nat (Nat.succ k) 0)
        (@Nat.noConfusion False (Nat.add (Nat.mul (Nat.succ a') k) (Nat.succ a')) Nat.zero hk))
    b
    h

-- `x + succ a' <= succ f  ->  x <= f`.  `x + succ a' = succ (x + a') >= succ x`
-- (`Nat.le_add_right`), so `succ x <= x + succ a' <= succ f`, hence `x <= f`
-- (`Nat.le_of_succ_le_succ`).  Chains `le_trans` then strips the `succ`.
theorem le_of_add_succ_le_succ (x a' f : Nat)
    (h : Nat.le (Nat.add x (Nat.succ a')) (Nat.succ f)) : Nat.le x f :=
  Nat.le_of_succ_le_succ x f
    (@Nat.le_trans (Nat.succ x) (Nat.add x (Nat.succ a')) (Nat.succ f)
      -- succ x <= succ (x + a') = (x + succ a')  (def-eq: add recurses on 2nd arg)
      (@Nat.succ_le_succ x (Nat.add x a') (Nat.le_add_right x a'))
      h)

-- THE DIVISION-CANCELLATION CORE.  For ANY fuel `F` bounding the numerator
-- `(succ a') * b`, `divCore F ((succ a') * b) (succ a') = b`.  Proven by
-- induction on `F`, casing the inner `Nat.rec` over `(succ a') - numerator`
-- via the threaded-equality idiom (mirrors `modCore_eq_of_lt`).
--   * F = 0: `divCore 0 _ _ = 0`; the bound `(succ a')*b <= 0` forces `b = 0`.
--   * F = succ f, b = 0: numerator is `0`; `(succ a') - 0 = succ a'` (a succ),
--     inner rec takes the `0` branch -> `0 = b`.
--   * F = succ f, b = succ k: numerator is `(succ a')*k + succ a'`; since
--     `succ a' <= numerator`, `(succ a') - numerator = 0` (sub_eq_zero_of_le),
--     inner rec takes the succ branch -> `succ (divCore f (numerator - succ a')
--     (succ a'))`; `numerator - succ a' = (succ a')*k` (add_sub_cancel_r), and
--     the IH (fuel f, value k; bound discharged by le_of_add_succ_le_succ)
--     gives `divCore f ((succ a')*k) (succ a') = k`, so the whole is `succ k`.
theorem divCore_mul_cancel (F : Nat) :
    forall (a' b : Nat), Nat.le (Nat.mul (Nat.succ a') b) F ->
      @Eq Nat (Nat.divCore F (Nat.mul (Nat.succ a') b) (Nat.succ a')) b :=
  @Nat.rec
    (fun f => forall (a' b : Nat), Nat.le (Nat.mul (Nat.succ a') b) f ->
      @Eq Nat (Nat.divCore f (Nat.mul (Nat.succ a') b) (Nat.succ a')) b)
    (fun a' b hb =>
      -- F = 0: divCore 0 X (succ a') = 0; bound forces b = 0.
      Eq.symm (mul_succ_eq_zero a' b (le_zero (Nat.mul (Nat.succ a') b) hb)))
    (fun f ih =>
      fun a' b =>
        @Nat.rec
          (fun bb => Nat.le (Nat.mul (Nat.succ a') bb) (Nat.succ f) ->
            @Eq Nat (Nat.divCore (Nat.succ f) (Nat.mul (Nat.succ a') bb) (Nat.succ a')) bb)
          (fun _hb0 =>
            -- b = 0: numerator = mul (succ a') 0 = 0.  divCore (succ f) 0 (succ a'):
            -- inner rec over (succ a') - 0 = succ a' (a succ) -> the `0` branch.
            @Eq.refl Nat 0)
          (fun k _ihk hbk =>
            -- b = succ k.  numerator = mul (succ a') (succ k)
            --   = add (mul (succ a') k) (succ a')  (def-eq, mul recurses on 2nd arg).
            -- Case the inner Nat.rec over (succ a') - numerator via threaded eq:
            -- since succ a' <= numerator, that sub is 0 -> succ branch.
            @Eq.subst Nat
              (fun z =>
                @Eq Nat
                  (@Nat.rec (fun _ => Nat)
                    (Nat.succ (Nat.divCore f
                      (Nat.sub (Nat.add (Nat.mul (Nat.succ a') k) (Nat.succ a')) (Nat.succ a'))
                      (Nat.succ a')))
                    (fun _ _ => 0)
                    z)
                  (Nat.succ k))
              Nat.zero
              (Nat.sub (Nat.succ a') (Nat.add (Nat.mul (Nat.succ a') k) (Nat.succ a')))
              (Eq.symm
                (sub_eq_zero_of_le (Nat.succ a')
                  (Nat.add (Nat.mul (Nat.succ a') k) (Nat.succ a'))
                  (le_add_left_n (Nat.succ a') (Nat.mul (Nat.succ a') k))))
              -- After subst the inner rec is at 0 -> base branch:
              --   succ (divCore f (numerator - succ a') (succ a'))
              -- numerator - succ a' = mul (succ a') k (add_sub_cancel_r), then ih.
              (congrArg (fun z => Nat.succ z)
                (@Eq.subst Nat
                  (fun z => @Eq Nat (Nat.divCore f z (Nat.succ a')) k)
                  (Nat.mul (Nat.succ a') k)
                  (Nat.sub (Nat.add (Nat.mul (Nat.succ a') k) (Nat.succ a')) (Nat.succ a'))
                  (Eq.symm (add_sub_cancel_r (Nat.mul (Nat.succ a') k) (Nat.succ a')))
                  (ih a' k
                    (le_of_add_succ_le_succ (Nat.mul (Nat.succ a') k) a' f hbk)))))
          b)
    F

-- `mul_div_cancel : 0 < a  ->  (a * b) / a = b`.  Since `0 < a`, case `a` as
-- `succ a'` (via the strictly-positive hypothesis), then `div X (succ a') =
-- divCore X X (succ a')` (def-eq; fuel = numerator), and `divCore_mul_cancel`
-- at fuel = numerator (`Nat.le_refl`) closes it.
theorem mul_div_cancel (a b : Nat) (ha : Nat.lt 0 a) :
    @Eq Nat (Nat.div (Nat.mul a b) a) b :=
  @Nat.rec
    (fun aa => Nat.lt 0 aa -> @Eq Nat (Nat.div (Nat.mul aa b) aa) b)
    (fun h0 => @False.elim (@Eq Nat (Nat.div (Nat.mul 0 b) 0) b) (Nat.lt_irrefl 0 h0))
    (fun a' _iha _hsa =>
      -- div (mul (succ a') b) (succ a') = divCore (mul (succ a') b) (mul (succ a') b) (succ a')
      divCore_mul_cancel (Nat.mul (Nat.succ a') b) a' b
        (Nat.le_refl (Nat.mul (Nat.succ a') b)))
    a
    ha

-- TRUST'S UNSIGNED MUL-OVERFLOW VIOLATION, modeled on the Nat carrier:
--   And(Not(a = 0), Not((a*b mod 2^w)/a = b))
def mulOverflowVC : Nat -> Nat -> Nat -> Prop :=
  fun w a b => And (Not (@Eq Nat a 0))
    (Not (@Eq Nat (Nat.div (Nat.mod (Nat.mul a b) (Nat.pow 2 w)) a) b))

-- REFUTED under `0 < a` (so a ≠ 0, killing the first conjunct's role) and the
-- no-overflow precondition `a*b < 2^w`: then `(a*b) % 2^w = a*b` (mod_eq_of_lt),
-- so the divisor test is `(a*b)/a = b`, TRUE by `mul_div_cancel` (`0 < a`).  The
-- violation asserts this equality is FALSE -- contradiction.  This is exactly
-- the `term : False` `certify_vc` reconstructs for a discharged mul-overflow VC.
theorem mulOverflow_refuted (w a b : Nat) (ha : Nat.lt 0 a)
    (hfit : Nat.lt (Nat.mul a b) (Nat.pow 2 w)) (hv : mulOverflowVC w a b) : False :=
  @And.right (Not (@Eq Nat a 0))
    (Not (@Eq Nat (Nat.div (Nat.mod (Nat.mul a b) (Nat.pow 2 w)) a) b)) hv
    (@Eq.subst Nat
      (fun z => @Eq Nat (Nat.div z a) b)
      (Nat.mul a b)
      (Nat.mod (Nat.mul a b) (Nat.pow 2 w))
      (Eq.symm (mod_eq_of_lt (Nat.mul a b) (Nat.pow 2 w) hfit))
      (mul_div_cancel a b ha))

end TrustIr
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

#[test]
fn trustir_typesystem_elaborates_and_kernel_checks() {
    elaborate_module(TRUSTIR_SOURCE).expect(
        "the TrustIr type system (faithful to trust-ir Ty) must elaborate and kernel-check",
    );
}

#[test]
fn trustir_faithfulness_theorems_are_proven_down_to_the_foundational_axioms() {
    let env = elaborate_module(TRUSTIR_SOURCE)
        .expect("the TrustIr module must elaborate before auditing its theorems");
    for thm in [
        "bitWidth_i8",
        "bitWidth_i16",
        "bitWidth_i32",
        "bitWidth_i64",
        "bitWidth_i128",
        "bitWidth_u8",
        "bitWidth_u32",
        "bitWidth_u128",
        "bitWidth_tbool",
        "bitWidth_tunit",
        "bitWidth_ttuple",
        "isSigned_i8",
        "isSigned_i128",
        "isSigned_u8",
        "isSigned_tbool",
        "isUnsigned_u8",
        "isUnsigned_i8",
        "isInteger_i32",
        "isInteger_u64",
        "isInteger_tbool",
        "isInteger_ttuple",
        "signed_not_unsigned_i32",
        "unsigned_not_signed_u32",
        "Den_i8",
        "Den_u64",
        "Den_tbool",
        "Den_tunit",
        "Den_ttuple",
        "raise_lower",
        "lower_raise",
        "lower_preserves_Den",
        "irBinOp_add",
        "irBinOp_mul",
        "irBinOp_and",
        "raiseOp_lowerOp",
        "lowerOp_raiseOp",
        "lowerOp_preserves_binop",
        "raiseOp_preserves_binop",
        "cgBinOp_add",
        "raiseCgToIr_lowerIrToCg",
        "lowerIrToCg_raiseCgToIr",
        "lowerIrToCg_preserves",
        "raiseCgToIr_preserves",
        "lowerMirToCg_preserves",
        "zext_preserves",
        "trunc_preserves",
        "zext_identity",
        "irCast_zext",
        "irCast_trunc",
        "raiseCast_lowerCast",
        "lowerCast_raiseCast",
        "lowerCast_preserves",
        "raiseCast_preserves",
        "nmul_zero_left_ir",
        "nadd_right_comm_ir",
        "nmul_succ_left_ir",
        "nmul_comm_ir",
        "nmul_one_left_ir",
        "nmul_one_right_ir",
        "lowerShl_preserves",
        "raiseShl_preserves",
        "irShl_def",
        "shl_zero",
        "mirShl_zero",
        "shl_kernel_zero",
        "shl_kernel_succ",
        "irShl_shiftLeft_zero",
        "irOvResult_add",
        "irOvResult_sub",
        "irOvResult_mul",
        "irOvResult_eq_binop_add",
        "irOvResult_eq_binop_sub",
        "irOvResult_eq_binop_mul",
        "raiseOvOp_lowerOvOp",
        "lowerOvOp_raiseOvOp",
        "lowerOvOp_preserves_result",
        "raiseOvOp_preserves_result",
        "irEq_def",
        "irUlt_def",
        "lowerEq_preserves",
        "lowerUlt_preserves",
        "raiseEq_preserves",
        "raiseUlt_preserves",
        "irEq_refl",
        "irEq_symm",
        "irUlt_irrefl",
        "irUlt_asymm",
        "raiseCmpOp_lowerCmpOp",
        "lowerCmpOp_raiseCmpOp",
        "lowerCmpOp_preserves",
        "raiseCmpOp_preserves",
        "stepInst_preserves",
        "stepInst_raise_preserves",
        "evalIrBlock_nil",
        "evalIrBlock_cons",
        "evalMirBlock_nil",
        "evalMirBlock_cons",
        "lowerBlock_nil",
        "lowerBlock_cons",
        "lowerBlock_preserves",
        "raiseBlock_preserves",
        "nextBlock_ret",
        "nextBlock_br",
        "nextBlock_agrees",
        "runProg_zero",
        "runProg_congr",
        "cfgLower_preserves",
        "cfgRaise_preserves",
        "lowerCfgSucc_preserves",
        "stepInstIrToCg_preserves",
        "evalCgBlock_nil",
        "evalCgBlock_cons",
        "lowerBlockIrToCg_preserves",
        "lowerBlockMirToCg_preserves",
        "cfgLowerMirToCg_preserves",
        "irDivOp_udiv",
        "irDivOp_urem",
        "raiseDivOp_lowerDivOp",
        "lowerDivOp_raiseDivOp",
        "lowerDivOp_preserves",
        "raiseDivOp_preserves",
        "lowerDivIrToCg_preserves",
        "lowerDivMirToCg_preserves",
        "tyWidth_bitWidth_i8",
        "tyWidth_bitWidth_i32",
        "tyWidth_bitWidth_u64",
        "tyWidth_bitWidth_u128",
        "tyWidth_bitWidth_tbool",
        "tyLower_preserves",
        "tyLowerMirToCg_preserves",
        "irOvCarry_add",
        "irOvCarry_mul",
        "lowerOvCarry_preserves",
        "raiseOvCarry_preserves",
        "irLShr_def",
        "lowerLShr_preserves",
        "raiseLShr_preserves",
        "lowerLShrIrToCg_preserves",
        "lowerLShrMirToCg_preserves",
        "signBit_def",
        "lowerSExt_preserves",
        "raiseSExt_preserves",
        "lowerAShr_preserves",
        "raiseAShr_preserves",
        "lowerUltB_preserves",
        "raiseUltB_preserves",
        "lowerEqB_preserves",
        "lowerOvFlagAdd_preserves",
        "raiseOvFlagAdd_preserves",
        "lowerSDiv_preserves",
        "raiseSDiv_preserves",
        "lowerSDivMirToCg_preserves",
        "lowerSRem_preserves",
        "raiseSRem_preserves",
        "load_preserves",
        "stepMem_preserves",
        "stepMem_raise_preserves",
        "evalMemIr_nil",
        "evalMemIr_cons",
        "lowerMemBlock_preserves",
        "raiseMemBlock_preserves",
        "irBinOp_add_in_range",
        "irBinOp_sub_in_range",
        "irBinOp_mul_in_range",
        "irTrunc_in_range",
        "irLShr_in_range",
        "irOvResult_add_in_range",
        "stepMach_preserves",
        "stepMach_raise_preserves",
        "evalMachIr_nil",
        "evalMachIr_cons",
        "lowerMachBlock_preserves",
        "raiseMachBlock_preserves",
        "writeReg_inRange",
        "wrapBinOp_add_eq",
        "wrapBinOp_sub_eq",
        "wrapBinOp_mul_eq",
        "wrapBinOp_in_range",
        "stepWrap_inRange",
        "evalWrap_nil",
        "evalWrap_cons",
        "evalWrap_inRange",
        "lt_sub_pos",
        "modCore_eq_of_lt",
        "mod_eq_of_lt",
        "noOverflow_add",
        "noOverflow_mul",
        "stepSafe_inRange",
        "evalSafe_inRange",
        "wrapPBinOp_eq_mod",
        "stepOK_exact",
        "prog_exact_under_obligations",
        "cgBinOp_add_in_range",
        "cgBinOp_sub_in_range",
        "cgBinOp_mul_in_range",
        "cgNoOverflow_add",
        "cgNoOverflow_mul",
        "pipelineAdd_in_range",
        "pipelineMul_in_range",
        "pipelineAdd_noOverflow",
        "pipelineMul_noOverflow",
        "writeReg_same",
        "hoare_skip",
        "hoare_cons",
        "hoare_conseq",
        "double_verified",
        "evalWrapP_append",
        "hoare_seq",
        "seq_example_verified",
        "writeReg_other",
        "hoareSafe_skip",
        "hoareSafe_cons",
        "hoareSafe_conseq",
        "memRoundtrip_verified",
        "hoare_repeat",
        "wrapPBinOp_in_range",
        "stepWrapP_inRange",
        "body_inRange",
        "loop_preserves_inRange",
        "hoare_repeat_indexed",
        "mulBody_step",
        "mul_loop_machine",
        "iterAdd_eq_mul",
        "mul_by_addition_verified",
        "hoare_conj",
        "hoare_disj",
        "hoare_false",
        "hoare_frame",
        "frameBody_writesOnly",
        "frameR_framedOff",
        "frame_example",
        "dblBody_step",
        "dbl_loop_machine",
        "two_pow_succ",
        "iterDbl_eq_pow",
        "pow2_by_doubling_verified",
        "nat_eq_zero_of_beq_zero",
        "nat_lt_of_beq_zero_false",
        "hoare_ite",
        "ite_example_verified",
        "runProg_succ",
        "runProg_invariant",
        "cfgStep_inRange",
        "cfg_preserves_inRange",
        "addOverflow_refuted",
        "divZero_refuted",
        "indexOob_refuted",
        "addOverflow_safe",
        "subUnderflow_refuted",
        "shiftOob_refuted",
        "hoare_discharges_addOverflow",
        "hoare_discharges_addOverflow_skip",
        "hoare_ensures_addOverflow_safe",
        "add_sub_cancel_r",
        "sub_eq_zero_of_le",
        "le_add_left_n",
        "le_of_add_succ_le_succ",
        "mul_succ_eq_zero",
        "divCore_mul_cancel",
        "mul_div_cancel",
        "mulOverflow_refuted",
    ] {
        assert_proven_to_foundations(&env, thm);
    }
}
