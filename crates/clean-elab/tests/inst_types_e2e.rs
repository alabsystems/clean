// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! ALL TRUST INSTRUCTION-OPERATION TYPES ARE CLEAN TYPES — trust-ir's instruction
//! enums (first-party/trust-ir/crates/trust-ir/src/inst.rs) modeled faithfully in
//! Clean and proven down to the 3 foundational axioms.
//!
//! This is the instruction-layer companion to `tyfull_e2e.rs`/`tyall_e2e.rs` (which
//! cover the `Ty` type enum). Four namespaces image the full operation-type surface:
//!
//!   * `InstKind`    — the 50-variant `Inst` enum, with the LITERAL Rust methods
//!       `Inst::is_terminator` (inst.rs:804) and `Inst::has_side_effects`
//!       (inst.rs:826) reproduced exactly, + the real invariant that every
//!       terminator is side-effecting, + purity = non-side-effecting.
//!   * `InstBinOp`   — `BinOp` (20) + `UnOp` (9), op-family classifiers
//!       (float/int-arith/div-rem/bitwise/shift/signed) + disjointness.
//!   * `InstCmpCast` — `ICmpOp` (10) + `FCmpOp` (12) + `CastOp` (15):
//!       signed/unsigned compares, ordered/unordered IEEE float compares (the O/U
//!       prefix is the documented semantics), cast families + coverage.
//!   * `InstAtomic`  — `Ordering` (5) as the memory-ordering strength lattice
//!       (Relaxed bottom, SeqCst top; reflexive) + `AtomicRMWOp` (10) families.
//!
//! Classifiers tied to a literal Rust method match the method body; op-family
//! classifiers match the documented taxonomy (enum doc-comments + Display strings +
//! the trust-ir instruction table). Every theorem passes the same
//! `axiom_deps(name).is_empty()` bedrock gate proven discriminating in
//! `axiom_bedrock_check.rs`. All four slices elaborate together in one environment.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

const INST_SOURCE: &str = r#"

-- ###########################################################################
-- Inst enum kind (50 variants) — LITERAL Rust methods is_terminator (inst.rs:804) + has_side_effects (inst.rs:826)
-- ###########################################################################
namespace InstKind

-- The flagship trust-ir `Inst` enum (inst.rs:422), 50 variants in DECLARATION
-- ORDER, each modeled as a NULLARY tag (the ValueId/Ty/BlockId payloads do not
-- affect is_terminator/has_side_effects — both match only on the outer ctor).
-- The casesOn minors below follow this exact order.
inductive InstK where
  | ibinop : InstK
  | iunop : InstK
  | ioverflow : InstK
  | iicmp : InstK
  | ifcmp : InstK
  | icast : InstK
  | iload : InstK
  | istore : InstK
  | ialloca : InstK
  | iheapalloc : InstK
  | igep : InstK
  | iptrdata : InstK
  | iptrmetadata : InstK
  | iptrfromparts : InstK
  | iatomicload : InstK
  | iatomicstore : InstK
  | iatomicrmw : InstK
  | icmpxchg : InstK
  | ifence : InstK
  | ibr : InstK
  | icondbr : InstK
  | iswitch : InstK
  | icall : InstK
  | icallindirect : InstK
  | ireturn : InstK
  | iextractfield : InstK
  | iinsertfield : InstK
  | iextractelement : InstK
  | iinsertelement : InstK
  | iconst : InstK
  | inullptr : InstK
  | iglobaladdr : InstK
  | iundef : InstK
  | iassume : InstK
  | iassert : InstK
  | iunreachable : InstK
  | icopy : InstK
  | iselect : InstK
  | iborrow : InstK
  | iborrowmut : InstK
  | iendborrow : InstK
  | iretain : InstK
  | irelease : InstK
  | isunique : InstK
  | idealloc : InstK
  | iopenframe : InstK
  | ibindslot : InstK
  | iloadslot : InstK
  | icloseframe : InstK
  | idialectop : InstK

-- LITERAL Rust method `Inst::is_terminator` (inst.rs:804):
--   matches!(self, Br | CondBr | Switch | Return | Unreachable)
-- true for ibr, icondbr, iswitch, ireturn, iunreachable; false for all others.
-- Minors are in declaration order (positions: ibr=20, icondbr=21, iswitch=22,
-- ireturn=25, iunreachable=36).
def isTerminator : InstK -> Bool := fun t =>
  @InstK.casesOn (fun _ => Bool) t
    false   -- ibinop
    false   -- iunop
    false   -- ioverflow
    false   -- iicmp
    false   -- ifcmp
    false   -- icast
    false   -- iload
    false   -- istore
    false   -- ialloca
    false   -- iheapalloc
    false   -- igep
    false   -- iptrdata
    false   -- iptrmetadata
    false   -- iptrfromparts
    false   -- iatomicload
    false   -- iatomicstore
    false   -- iatomicrmw
    false   -- icmpxchg
    false   -- ifence
    true    -- ibr           (terminator)
    true    -- icondbr       (terminator)
    true    -- iswitch       (terminator)
    false   -- icall
    false   -- icallindirect
    true    -- ireturn       (terminator)
    false   -- iextractfield
    false   -- iinsertfield
    false   -- iextractelement
    false   -- iinsertelement
    false   -- iconst
    false   -- inullptr
    false   -- iglobaladdr
    false   -- iundef
    false   -- iassume
    false   -- iassert
    true    -- iunreachable  (terminator)
    false   -- icopy
    false   -- iselect
    false   -- iborrow
    false   -- iborrowmut
    false   -- iendborrow
    false   -- iretain
    false   -- irelease
    false   -- isunique
    false   -- idealloc
    false   -- iopenframe
    false   -- ibindslot
    false   -- iloadslot
    false   -- icloseframe
    false   -- idialectop

-- LITERAL Rust method `Inst::has_side_effects` (inst.rs:826). The explicit
-- side-effecting arms { Store, AtomicStore, AtomicRMW, CmpXchg, Fence, Dealloc,
-- Call, CallIndirect, Assert, Borrow, BorrowMut, EndBorrow, Retain, Release,
-- CloseFrame, DialectOp } plus the `_ if self.is_terminator()` fallthrough arm
-- (inst.rs:865) covering Br/CondBr/Switch/Return/Unreachable; everything else
-- (the final `_ => false`) is pure. Encoded directly as the per-variant Bool
-- (the terminator fallthrough is inlined into the five terminator positions).
def hasSideEffects : InstK -> Bool := fun t =>
  @InstK.casesOn (fun _ => Bool) t
    false   -- ibinop
    false   -- iunop
    false   -- ioverflow
    false   -- iicmp
    false   -- ifcmp
    false   -- icast
    false   -- iload
    true    -- istore        (memory write)
    false   -- ialloca
    false   -- iheapalloc
    false   -- igep
    false   -- iptrdata
    false   -- iptrmetadata
    false   -- iptrfromparts
    false   -- iatomicload
    true    -- iatomicstore   (memory write)
    true    -- iatomicrmw     (memory write)
    true    -- icmpxchg       (memory write)
    true    -- ifence         (memory fence)
    true    -- ibr            (terminator)
    true    -- icondbr        (terminator)
    true    -- iswitch        (terminator)
    true    -- icall          (call)
    true    -- icallindirect  (call)
    true    -- ireturn        (terminator)
    false   -- iextractfield
    false   -- iinsertfield
    false   -- iextractelement
    false   -- iinsertelement
    false   -- iconst
    false   -- inullptr
    false   -- iglobaladdr
    false   -- iundef
    false   -- iassume
    true    -- iassert        (may trap)
    true    -- iunreachable   (terminator)
    false   -- icopy
    false   -- iselect
    true    -- iborrow        (permission map)
    true    -- iborrowmut     (permission map)
    true    -- iendborrow     (permission map)
    true    -- iretain        (refcount)
    true    -- irelease       (refcount)
    false   -- isunique
    true    -- idealloc       (deallocation)
    false   -- iopenframe
    false   -- ibindslot
    false   -- iloadslot
    true    -- icloseframe    (discipline marker)
    true    -- idialectop     (opaque)

-- Purity helper: an instruction is pure exactly when it has no side effects.
def isPure : InstK -> Bool := fun t => Bool.not (hasSideEffects t)

-- ===========================================================================
-- FAITHFULNESS to `Inst::is_terminator` (inst.rs:804) — all 50 variants by iota.
-- ===========================================================================
theorem inst_isTerminator_ibinop : isTerminator InstK.ibinop = false := rfl
theorem inst_isTerminator_iunop : isTerminator InstK.iunop = false := rfl
theorem inst_isTerminator_ioverflow : isTerminator InstK.ioverflow = false := rfl
theorem inst_isTerminator_iicmp : isTerminator InstK.iicmp = false := rfl
theorem inst_isTerminator_ifcmp : isTerminator InstK.ifcmp = false := rfl
theorem inst_isTerminator_icast : isTerminator InstK.icast = false := rfl
theorem inst_isTerminator_iload : isTerminator InstK.iload = false := rfl
theorem inst_isTerminator_istore : isTerminator InstK.istore = false := rfl
theorem inst_isTerminator_ialloca : isTerminator InstK.ialloca = false := rfl
theorem inst_isTerminator_iheapalloc : isTerminator InstK.iheapalloc = false := rfl
theorem inst_isTerminator_igep : isTerminator InstK.igep = false := rfl
theorem inst_isTerminator_iptrdata : isTerminator InstK.iptrdata = false := rfl
theorem inst_isTerminator_iptrmetadata : isTerminator InstK.iptrmetadata = false := rfl
theorem inst_isTerminator_iptrfromparts : isTerminator InstK.iptrfromparts = false := rfl
theorem inst_isTerminator_iatomicload : isTerminator InstK.iatomicload = false := rfl
theorem inst_isTerminator_iatomicstore : isTerminator InstK.iatomicstore = false := rfl
theorem inst_isTerminator_iatomicrmw : isTerminator InstK.iatomicrmw = false := rfl
theorem inst_isTerminator_icmpxchg : isTerminator InstK.icmpxchg = false := rfl
theorem inst_isTerminator_ifence : isTerminator InstK.ifence = false := rfl
theorem inst_isTerminator_ibr : isTerminator InstK.ibr = true := rfl
theorem inst_isTerminator_icondbr : isTerminator InstK.icondbr = true := rfl
theorem inst_isTerminator_iswitch : isTerminator InstK.iswitch = true := rfl
theorem inst_isTerminator_icall : isTerminator InstK.icall = false := rfl
theorem inst_isTerminator_icallindirect : isTerminator InstK.icallindirect = false := rfl
theorem inst_isTerminator_ireturn : isTerminator InstK.ireturn = true := rfl
theorem inst_isTerminator_iextractfield : isTerminator InstK.iextractfield = false := rfl
theorem inst_isTerminator_iinsertfield : isTerminator InstK.iinsertfield = false := rfl
theorem inst_isTerminator_iextractelement : isTerminator InstK.iextractelement = false := rfl
theorem inst_isTerminator_iinsertelement : isTerminator InstK.iinsertelement = false := rfl
theorem inst_isTerminator_iconst : isTerminator InstK.iconst = false := rfl
theorem inst_isTerminator_inullptr : isTerminator InstK.inullptr = false := rfl
theorem inst_isTerminator_iglobaladdr : isTerminator InstK.iglobaladdr = false := rfl
theorem inst_isTerminator_iundef : isTerminator InstK.iundef = false := rfl
theorem inst_isTerminator_iassume : isTerminator InstK.iassume = false := rfl
theorem inst_isTerminator_iassert : isTerminator InstK.iassert = false := rfl
theorem inst_isTerminator_iunreachable : isTerminator InstK.iunreachable = true := rfl
theorem inst_isTerminator_icopy : isTerminator InstK.icopy = false := rfl
theorem inst_isTerminator_iselect : isTerminator InstK.iselect = false := rfl
theorem inst_isTerminator_iborrow : isTerminator InstK.iborrow = false := rfl
theorem inst_isTerminator_iborrowmut : isTerminator InstK.iborrowmut = false := rfl
theorem inst_isTerminator_iendborrow : isTerminator InstK.iendborrow = false := rfl
theorem inst_isTerminator_iretain : isTerminator InstK.iretain = false := rfl
theorem inst_isTerminator_irelease : isTerminator InstK.irelease = false := rfl
theorem inst_isTerminator_isunique : isTerminator InstK.isunique = false := rfl
theorem inst_isTerminator_idealloc : isTerminator InstK.idealloc = false := rfl
theorem inst_isTerminator_iopenframe : isTerminator InstK.iopenframe = false := rfl
theorem inst_isTerminator_ibindslot : isTerminator InstK.ibindslot = false := rfl
theorem inst_isTerminator_iloadslot : isTerminator InstK.iloadslot = false := rfl
theorem inst_isTerminator_icloseframe : isTerminator InstK.icloseframe = false := rfl
theorem inst_isTerminator_idialectop : isTerminator InstK.idialectop = false := rfl

-- ===========================================================================
-- FAITHFULNESS to `Inst::has_side_effects` (inst.rs:826) — all 50 by iota.
-- ===========================================================================
theorem inst_hasSideEffects_ibinop : hasSideEffects InstK.ibinop = false := rfl
theorem inst_hasSideEffects_iunop : hasSideEffects InstK.iunop = false := rfl
theorem inst_hasSideEffects_ioverflow : hasSideEffects InstK.ioverflow = false := rfl
theorem inst_hasSideEffects_iicmp : hasSideEffects InstK.iicmp = false := rfl
theorem inst_hasSideEffects_ifcmp : hasSideEffects InstK.ifcmp = false := rfl
theorem inst_hasSideEffects_icast : hasSideEffects InstK.icast = false := rfl
theorem inst_hasSideEffects_iload : hasSideEffects InstK.iload = false := rfl
theorem inst_hasSideEffects_istore : hasSideEffects InstK.istore = true := rfl
theorem inst_hasSideEffects_ialloca : hasSideEffects InstK.ialloca = false := rfl
theorem inst_hasSideEffects_iheapalloc : hasSideEffects InstK.iheapalloc = false := rfl
theorem inst_hasSideEffects_igep : hasSideEffects InstK.igep = false := rfl
theorem inst_hasSideEffects_iptrdata : hasSideEffects InstK.iptrdata = false := rfl
theorem inst_hasSideEffects_iptrmetadata : hasSideEffects InstK.iptrmetadata = false := rfl
theorem inst_hasSideEffects_iptrfromparts : hasSideEffects InstK.iptrfromparts = false := rfl
theorem inst_hasSideEffects_iatomicload : hasSideEffects InstK.iatomicload = false := rfl
theorem inst_hasSideEffects_iatomicstore : hasSideEffects InstK.iatomicstore = true := rfl
theorem inst_hasSideEffects_iatomicrmw : hasSideEffects InstK.iatomicrmw = true := rfl
theorem inst_hasSideEffects_icmpxchg : hasSideEffects InstK.icmpxchg = true := rfl
theorem inst_hasSideEffects_ifence : hasSideEffects InstK.ifence = true := rfl
theorem inst_hasSideEffects_ibr : hasSideEffects InstK.ibr = true := rfl
theorem inst_hasSideEffects_icondbr : hasSideEffects InstK.icondbr = true := rfl
theorem inst_hasSideEffects_iswitch : hasSideEffects InstK.iswitch = true := rfl
theorem inst_hasSideEffects_icall : hasSideEffects InstK.icall = true := rfl
theorem inst_hasSideEffects_icallindirect : hasSideEffects InstK.icallindirect = true := rfl
theorem inst_hasSideEffects_ireturn : hasSideEffects InstK.ireturn = true := rfl
theorem inst_hasSideEffects_iextractfield : hasSideEffects InstK.iextractfield = false := rfl
theorem inst_hasSideEffects_iinsertfield : hasSideEffects InstK.iinsertfield = false := rfl
theorem inst_hasSideEffects_iextractelement : hasSideEffects InstK.iextractelement = false := rfl
theorem inst_hasSideEffects_iinsertelement : hasSideEffects InstK.iinsertelement = false := rfl
theorem inst_hasSideEffects_iconst : hasSideEffects InstK.iconst = false := rfl
theorem inst_hasSideEffects_inullptr : hasSideEffects InstK.inullptr = false := rfl
theorem inst_hasSideEffects_iglobaladdr : hasSideEffects InstK.iglobaladdr = false := rfl
theorem inst_hasSideEffects_iundef : hasSideEffects InstK.iundef = false := rfl
theorem inst_hasSideEffects_iassume : hasSideEffects InstK.iassume = false := rfl
theorem inst_hasSideEffects_iassert : hasSideEffects InstK.iassert = true := rfl
theorem inst_hasSideEffects_iunreachable : hasSideEffects InstK.iunreachable = true := rfl
theorem inst_hasSideEffects_icopy : hasSideEffects InstK.icopy = false := rfl
theorem inst_hasSideEffects_iselect : hasSideEffects InstK.iselect = false := rfl
theorem inst_hasSideEffects_iborrow : hasSideEffects InstK.iborrow = true := rfl
theorem inst_hasSideEffects_iborrowmut : hasSideEffects InstK.iborrowmut = true := rfl
theorem inst_hasSideEffects_iendborrow : hasSideEffects InstK.iendborrow = true := rfl
theorem inst_hasSideEffects_iretain : hasSideEffects InstK.iretain = true := rfl
theorem inst_hasSideEffects_irelease : hasSideEffects InstK.irelease = true := rfl
theorem inst_hasSideEffects_isunique : hasSideEffects InstK.isunique = false := rfl
theorem inst_hasSideEffects_idealloc : hasSideEffects InstK.idealloc = true := rfl
theorem inst_hasSideEffects_iopenframe : hasSideEffects InstK.iopenframe = false := rfl
theorem inst_hasSideEffects_ibindslot : hasSideEffects InstK.ibindslot = false := rfl
theorem inst_hasSideEffects_iloadslot : hasSideEffects InstK.iloadslot = false := rfl
theorem inst_hasSideEffects_icloseframe : hasSideEffects InstK.icloseframe = true := rfl
theorem inst_hasSideEffects_idialectop : hasSideEffects InstK.idialectop = true := rfl

-- ===========================================================================
-- METATHEOREM (the real invariant at inst.rs:865, the `_ if self.is_terminator()`
-- arm): EVERY terminator is side-effecting. Stated as the Bool implication
-- `isTerminator i -> hasSideEffects i`, encoded `or (not p) q = true`, proven by
-- a 50-constructor casesOn (each minor `rfl`, all ctors nullary).
-- ===========================================================================
theorem inst_terminator_implies_side_effects (i : InstK) :
    Bool.or (Bool.not (isTerminator i)) (hasSideEffects i) = true :=
  @InstK.casesOn (fun k => Bool.or (Bool.not (isTerminator k)) (hasSideEffects k) = true) i
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- ===========================================================================
-- PURITY is exactly NON-side-effecting: `and (isPure i) (hasSideEffects i)` is
-- always false (a value cannot be both pure and side-effecting). 50-ctor casesOn.
-- ===========================================================================
theorem inst_pure_excludes_side_effects (i : InstK) :
    Bool.and (isPure i) (hasSideEffects i) = false :=
  @InstK.casesOn (fun k => Bool.and (isPure k) (hasSideEffects k) = false) i
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

end InstKind

-- ###########################################################################
-- BinOp (20) + UnOp (9) — op-family classifiers (float/int-arith/div-rem/bitwise/shift/signed)
-- ###########################################################################
namespace InstBinOp

-- A faithful Clean image of trust-ir `BinOp` (inst.rs:11). 20 nullary ctors in
-- DECLARATION ORDER. The three keyword-clashing names (And/Or/Xor) are renamed
-- to band/bor/bxor (the Display mnemonics are still "and"/"or"/"xor"; only the
-- Clean identifier is changed to dodge the parser keyword clash).
inductive BinOp where
  | add : BinOp
  | sub : BinOp
  | mul : BinOp
  | udiv : BinOp
  | sdiv : BinOp
  | urem : BinOp
  | srem : BinOp
  | fadd : BinOp
  | fsub : BinOp
  | fmul : BinOp
  | fdiv : BinOp
  | frem : BinOp
  | fmin : BinOp
  | fmax : BinOp
  | band : BinOp
  | bor : BinOp
  | bxor : BinOp
  | shl : BinOp
  | lshr : BinOp
  | ashr : BinOp

-- A faithful Clean image of trust-ir `UnOp` (inst.rs:44). 9 nullary ctors in
-- DECLARATION ORDER (bnot renamed from `Not` to dodge the keyword clash; its
-- Display mnemonic is still "not").
inductive UnOp where
  | neg : UnOp
  | fneg : UnOp
  | fabs : UnOp
  | fsqrt : UnOp
  | ffloor : UnOp
  | fceil : UnOp
  | ftrunc : UnOp
  | bnot : UnOp
  | ctpop : UnOp

-- ===========================================================================
-- BinOp op-FAMILY classifiers. Each is a 20-minor @BinOp.casesOn whose minors
-- are bare Bool literals (all ctors nullary), in declaration order:
--   add sub mul udiv sdiv urem srem fadd fsub fmul fdiv frem fmin fmax
--   band bor bxor shl lshr ashr
-- ===========================================================================

-- isFloatOp: the F-prefixed binary ops (fadd..fmax). [Display: fadd/fsub/fmul/
-- fdiv/frem/fmin/fmax; the whole "float" family of the instruction table.]
def isFloatOp : BinOp -> Bool := fun o =>
  @BinOp.casesOn (fun _ => Bool) o
    false false false false false false false   -- add sub mul udiv sdiv urem srem
    true true true true true true true          -- fadd fsub fmul fdiv frem fmin fmax
    false false false false false false         -- band bor bxor shl lshr ashr

-- isIntArith: the three wrap-around integer arithmetic ops (add/sub/mul).
def isIntArith : BinOp -> Bool := fun o =>
  @BinOp.casesOn (fun _ => Bool) o
    true true true false false false false      -- add sub mul udiv sdiv urem srem
    false false false false false false false   -- fadd fsub fmul fdiv frem fmin fmax
    false false false false false false         -- band bor bxor shl lshr ashr

-- isDivRem: the integer division / remainder family (udiv/sdiv/urem/srem).
def isDivRem : BinOp -> Bool := fun o =>
  @BinOp.casesOn (fun _ => Bool) o
    false false false true true true true       -- add sub mul udiv sdiv urem srem
    false false false false false false false   -- fadd fsub fmul fdiv frem fmin fmax
    false false false false false false         -- band bor bxor shl lshr ashr

-- isBitwise: the bitwise logical ops (band/bor/bxor == and/or/xor).
def isBitwise : BinOp -> Bool := fun o =>
  @BinOp.casesOn (fun _ => Bool) o
    false false false false false false false   -- add sub mul udiv sdiv urem srem
    false false false false false false false   -- fadd fsub fmul fdiv frem fmin fmax
    true true true false false false            -- band bor bxor shl lshr ashr

-- isShift: the three shift ops (shl/lshr/ashr).
def isShift : BinOp -> Bool := fun o =>
  @BinOp.casesOn (fun _ => Bool) o
    false false false false false false false   -- add sub mul udiv sdiv urem srem
    false false false false false false false   -- fadd fsub fmul fdiv frem fmin fmax
    false false false true true true            -- band bor bxor shl lshr ashr

-- isSignedOp: the signedness-bearing integer ops — sdiv, srem (the S-prefixed
-- div/rem) and ashr (the arithmetic, i.e. sign-extending, shift). The U-prefixed
-- udiv/urem and the logical lshr are the unsigned mirrors and are NOT here.
def isSignedOp : BinOp -> Bool := fun o =>
  @BinOp.casesOn (fun _ => Bool) o
    false false false false true false true     -- add sub mul udiv SDIV urem SREM
    false false false false false false false   -- fadd fsub fmul fdiv frem fmin fmax
    false false false false false true          -- band bor bxor shl lshr ASHR

-- ===========================================================================
-- UnOp op-FAMILY classifiers (9-minor @UnOp.casesOn, declaration order:
--   neg fneg fabs fsqrt ffloor fceil ftrunc bnot ctpop).
-- ===========================================================================

-- isFloatUn: the F-prefixed unary ops (fneg/fabs/fsqrt/ffloor/fceil/ftrunc).
def isFloatUn : UnOp -> Bool := fun u =>
  @UnOp.casesOn (fun _ => Bool) u
    false                                       -- neg
    true true true true true true               -- fneg fabs fsqrt ffloor fceil ftrunc
    false false                                 -- bnot ctpop

-- isIntUn: the integer/bit unary ops — neg (integer negate), bnot (bitwise NOT),
-- ctpop (population count). [Display: neg/not/ctpop.]
def isIntUn : UnOp -> Bool := fun u =>
  @UnOp.casesOn (fun _ => Bool) u
    true                                        -- neg
    false false false false false false         -- fneg fabs fsqrt ffloor fceil ftrunc
    true true                                   -- bnot ctpop

-- ===========================================================================
-- FAITHFULNESS: isFloatOp — exactly the F-prefixed binary ops, by casesOn iota.
-- ===========================================================================
theorem bop_isFloatOp_add : isFloatOp BinOp.add = false := rfl
theorem bop_isFloatOp_sub : isFloatOp BinOp.sub = false := rfl
theorem bop_isFloatOp_mul : isFloatOp BinOp.mul = false := rfl
theorem bop_isFloatOp_udiv : isFloatOp BinOp.udiv = false := rfl
theorem bop_isFloatOp_sdiv : isFloatOp BinOp.sdiv = false := rfl
theorem bop_isFloatOp_urem : isFloatOp BinOp.urem = false := rfl
theorem bop_isFloatOp_srem : isFloatOp BinOp.srem = false := rfl
theorem bop_isFloatOp_fadd : isFloatOp BinOp.fadd = true := rfl
theorem bop_isFloatOp_fsub : isFloatOp BinOp.fsub = true := rfl
theorem bop_isFloatOp_fmul : isFloatOp BinOp.fmul = true := rfl
theorem bop_isFloatOp_fdiv : isFloatOp BinOp.fdiv = true := rfl
theorem bop_isFloatOp_frem : isFloatOp BinOp.frem = true := rfl
theorem bop_isFloatOp_fmin : isFloatOp BinOp.fmin = true := rfl
theorem bop_isFloatOp_fmax : isFloatOp BinOp.fmax = true := rfl
theorem bop_isFloatOp_band : isFloatOp BinOp.band = false := rfl
theorem bop_isFloatOp_bor : isFloatOp BinOp.bor = false := rfl
theorem bop_isFloatOp_bxor : isFloatOp BinOp.bxor = false := rfl
theorem bop_isFloatOp_shl : isFloatOp BinOp.shl = false := rfl
theorem bop_isFloatOp_lshr : isFloatOp BinOp.lshr = false := rfl
theorem bop_isFloatOp_ashr : isFloatOp BinOp.ashr = false := rfl

-- FAITHFULNESS: isIntArith — exactly add/sub/mul.
theorem bop_isIntArith_add : isIntArith BinOp.add = true := rfl
theorem bop_isIntArith_sub : isIntArith BinOp.sub = true := rfl
theorem bop_isIntArith_mul : isIntArith BinOp.mul = true := rfl
theorem bop_isIntArith_udiv : isIntArith BinOp.udiv = false := rfl
theorem bop_isIntArith_fadd : isIntArith BinOp.fadd = false := rfl
theorem bop_isIntArith_band : isIntArith BinOp.band = false := rfl
theorem bop_isIntArith_shl : isIntArith BinOp.shl = false := rfl

-- FAITHFULNESS: isDivRem — exactly udiv/sdiv/urem/srem.
theorem bop_isDivRem_udiv : isDivRem BinOp.udiv = true := rfl
theorem bop_isDivRem_sdiv : isDivRem BinOp.sdiv = true := rfl
theorem bop_isDivRem_urem : isDivRem BinOp.urem = true := rfl
theorem bop_isDivRem_srem : isDivRem BinOp.srem = true := rfl
theorem bop_isDivRem_add : isDivRem BinOp.add = false := rfl
theorem bop_isDivRem_fdiv : isDivRem BinOp.fdiv = false := rfl
theorem bop_isDivRem_shl : isDivRem BinOp.shl = false := rfl

-- FAITHFULNESS: isBitwise — exactly band/bor/bxor.
theorem bop_isBitwise_band : isBitwise BinOp.band = true := rfl
theorem bop_isBitwise_bor : isBitwise BinOp.bor = true := rfl
theorem bop_isBitwise_bxor : isBitwise BinOp.bxor = true := rfl
theorem bop_isBitwise_add : isBitwise BinOp.add = false := rfl
theorem bop_isBitwise_shl : isBitwise BinOp.shl = false := rfl
theorem bop_isBitwise_ashr : isBitwise BinOp.ashr = false := rfl
theorem bop_isBitwise_fadd : isBitwise BinOp.fadd = false := rfl

-- FAITHFULNESS: isShift — exactly shl/lshr/ashr.
theorem bop_isShift_shl : isShift BinOp.shl = true := rfl
theorem bop_isShift_lshr : isShift BinOp.lshr = true := rfl
theorem bop_isShift_ashr : isShift BinOp.ashr = true := rfl
theorem bop_isShift_band : isShift BinOp.band = false := rfl
theorem bop_isShift_add : isShift BinOp.add = false := rfl
theorem bop_isShift_fmul : isShift BinOp.fmul = false := rfl

-- FAITHFULNESS: isSignedOp — exactly sdiv/srem/ashr.
theorem bop_isSignedOp_sdiv : isSignedOp BinOp.sdiv = true := rfl
theorem bop_isSignedOp_srem : isSignedOp BinOp.srem = true := rfl
theorem bop_isSignedOp_ashr : isSignedOp BinOp.ashr = true := rfl
theorem bop_isSignedOp_udiv : isSignedOp BinOp.udiv = false := rfl
theorem bop_isSignedOp_urem : isSignedOp BinOp.urem = false := rfl
theorem bop_isSignedOp_lshr : isSignedOp BinOp.lshr = false := rfl
theorem bop_isSignedOp_add : isSignedOp BinOp.add = false := rfl
theorem bop_isSignedOp_fadd : isSignedOp BinOp.fadd = false := rfl

-- ===========================================================================
-- FAITHFULNESS: UnOp isFloatUn — exactly fneg/fabs/fsqrt/ffloor/fceil/ftrunc.
-- ===========================================================================
theorem bop_isFloatUn_neg : isFloatUn UnOp.neg = false := rfl
theorem bop_isFloatUn_fneg : isFloatUn UnOp.fneg = true := rfl
theorem bop_isFloatUn_fabs : isFloatUn UnOp.fabs = true := rfl
theorem bop_isFloatUn_fsqrt : isFloatUn UnOp.fsqrt = true := rfl
theorem bop_isFloatUn_ffloor : isFloatUn UnOp.ffloor = true := rfl
theorem bop_isFloatUn_fceil : isFloatUn UnOp.fceil = true := rfl
theorem bop_isFloatUn_ftrunc : isFloatUn UnOp.ftrunc = true := rfl
theorem bop_isFloatUn_bnot : isFloatUn UnOp.bnot = false := rfl
theorem bop_isFloatUn_ctpop : isFloatUn UnOp.ctpop = false := rfl

-- FAITHFULNESS: UnOp isIntUn — exactly neg/bnot/ctpop.
theorem bop_isIntUn_neg : isIntUn UnOp.neg = true := rfl
theorem bop_isIntUn_fneg : isIntUn UnOp.fneg = false := rfl
theorem bop_isIntUn_fabs : isIntUn UnOp.fabs = false := rfl
theorem bop_isIntUn_fsqrt : isIntUn UnOp.fsqrt = false := rfl
theorem bop_isIntUn_ffloor : isIntUn UnOp.ffloor = false := rfl
theorem bop_isIntUn_fceil : isIntUn UnOp.fceil = false := rfl
theorem bop_isIntUn_ftrunc : isIntUn UnOp.ftrunc = false := rfl
theorem bop_isIntUn_bnot : isIntUn UnOp.bnot = true := rfl
theorem bop_isIntUn_ctpop : isIntUn UnOp.ctpop = true := rfl

-- ===========================================================================
-- PARTITION METATHEOREMS — proven over ALL 20 (resp. 9) ctors by one all-ctor
-- @casesOn (each minor is `rfl`, since every ctor is nullary). These say the
-- op-families are pairwise-coherent for EVERY BinOp/UnOp, not just the witnessed
-- ones — the structural content the per-variant rfls cannot express.
-- ===========================================================================

-- Float ops and integer-arith ops are disjoint over all of BinOp.
theorem bop_part_float_intarith_disjoint (o : BinOp) :
    Bool.and (isFloatOp o) (isIntArith o) = false :=
  @BinOp.casesOn (fun k => Bool.and (isFloatOp k) (isIntArith k) = false) o
    rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl

-- Float ops and bitwise ops are disjoint over all of BinOp.
theorem bop_part_float_bitwise_disjoint (o : BinOp) :
    Bool.and (isFloatOp o) (isBitwise o) = false :=
  @BinOp.casesOn (fun k => Bool.and (isFloatOp k) (isBitwise k) = false) o
    rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl

-- Bitwise ops and shift ops are disjoint over all of BinOp.
theorem bop_part_bitwise_shift_disjoint (o : BinOp) :
    Bool.and (isBitwise o) (isShift o) = false :=
  @BinOp.casesOn (fun k => Bool.and (isBitwise k) (isShift k) = false) o
    rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl

-- Float ops and the div/rem family are disjoint over all of BinOp.
theorem bop_part_float_divrem_disjoint (o : BinOp) :
    Bool.and (isFloatOp o) (isDivRem o) = false :=
  @BinOp.casesOn (fun k => Bool.and (isFloatOp k) (isDivRem k) = false) o
    rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl

-- Integer-arith ops and the div/rem family are disjoint over all of BinOp.
theorem bop_part_intarith_divrem_disjoint (o : BinOp) :
    Bool.and (isIntArith o) (isDivRem o) = false :=
  @BinOp.casesOn (fun k => Bool.and (isIntArith k) (isDivRem k) = false) o
    rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl

-- Integer-arith ops and shift ops are disjoint over all of BinOp.
theorem bop_part_intarith_shift_disjoint (o : BinOp) :
    Bool.and (isIntArith o) (isShift o) = false :=
  @BinOp.casesOn (fun k => Bool.and (isIntArith k) (isShift k) = false) o
    rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl

-- Bitwise ops and the div/rem family are disjoint over all of BinOp.
theorem bop_part_bitwise_divrem_disjoint (o : BinOp) :
    Bool.and (isBitwise o) (isDivRem o) = false :=
  @BinOp.casesOn (fun k => Bool.and (isBitwise k) (isDivRem k) = false) o
    rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl

-- Any signed integer op is NOT a float op (signedness is an INTEGER concept):
-- encoded over Bool as  (not isSignedOp) || (not isFloatOp) = true.
theorem bop_part_signed_not_float (o : BinOp) :
    Bool.or (Bool.not (isSignedOp o)) (Bool.not (isFloatOp o)) = true :=
  @BinOp.casesOn (fun k => Bool.or (Bool.not (isSignedOp k)) (Bool.not (isFloatOp k)) = true) o
    rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl

-- Any signed integer op is NOT an integer-arith op (add/sub/mul carry no
-- signedness): (not isSignedOp) || (not isIntArith) = true over all of BinOp.
theorem bop_part_signed_not_intarith (o : BinOp) :
    Bool.or (Bool.not (isSignedOp o)) (Bool.not (isIntArith o)) = true :=
  @BinOp.casesOn (fun k => Bool.or (Bool.not (isSignedOp k)) (Bool.not (isIntArith k)) = true) o
    rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl

-- Every signed op IS either a div/rem op or a shift op (sdiv/srem in div/rem,
-- ashr in shift): (not isSignedOp) || (isDivRem || isShift) = true over BinOp.
theorem bop_part_signed_implies_divrem_or_shift (o : BinOp) :
    Bool.or (Bool.not (isSignedOp o)) (Bool.or (isDivRem o) (isShift o)) = true :=
  @BinOp.casesOn
    (fun k => Bool.or (Bool.not (isSignedOp k)) (Bool.or (isDivRem k) (isShift k)) = true) o
    rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl

-- UnOp: float-unary and integer-unary are disjoint over all 9 ctors.
theorem bop_part_unop_float_int_disjoint (u : UnOp) :
    Bool.and (isFloatUn u) (isIntUn u) = false :=
  @UnOp.casesOn (fun k => Bool.and (isFloatUn k) (isIntUn k) = false) u
    rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- UnOp: the two families are EXHAUSTIVE — every UnOp is float-unary or
-- integer-unary: (isFloatUn || isIntUn) = true over all 9 ctors.
theorem bop_part_unop_float_int_total (u : UnOp) :
    Bool.or (isFloatUn u) (isIntUn u) = true :=
  @UnOp.casesOn (fun k => Bool.or (isFloatUn k) (isIntUn k) = true) u
    rfl rfl rfl rfl rfl rfl rfl rfl rfl

end InstBinOp

-- ###########################################################################
-- ICmpOp (10) + FCmpOp (12) + CastOp (15) — signed/unsigned, ordered/unordered, cast families
-- ###########################################################################
namespace InstCmpCast

-- ===========================================================================
-- ICmpOp (inst.rs:75). 10 nullary ctors, in DECLARATION ORDER:
--   Eq Ne Ult Ule Ugt Uge Slt Sle Sgt Sge
-- ===========================================================================
inductive ICmpOp where
  | ieq : ICmpOp
  | ine : ICmpOp
  | iult : ICmpOp
  | iule : ICmpOp
  | iugt : ICmpOp
  | iuge : ICmpOp
  | islt : ICmpOp
  | isle : ICmpOp
  | isgt : ICmpOp
  | isge : ICmpOp

-- isEquality: the sign-agnostic equality predicates (ieq, ine). (Grounded in the
-- LLVM icmp predicate taxonomy: eq/ne are the only sign-independent predicates.)
def isEquality : ICmpOp -> Bool := fun c =>
  @ICmpOp.casesOn (fun _ => Bool) c
    true true false false false false false false false false

-- isSignedCmp: the S-prefixed ordering predicates (islt, isle, isgt, isge).
-- (Grounded: CLAUDE.md "signed and unsigned"; S = signed in these mnemonics.)
def isSignedCmp : ICmpOp -> Bool := fun c =>
  @ICmpOp.casesOn (fun _ => Bool) c
    false false false false false false true true true true

-- isUnsignedCmp: the U-prefixed ordering predicates (iult, iule, iugt, iuge).
def isUnsignedCmp : ICmpOp -> Bool := fun c =>
  @ICmpOp.casesOn (fun _ => Bool) c
    false false true true true true false false false false

-- --- FAITHFULNESS: isEquality, per variant (casesOn iota = rfl) ---
theorem cc_icmp_isEquality_ieq : isEquality ICmpOp.ieq = true := rfl
theorem cc_icmp_isEquality_ine : isEquality ICmpOp.ine = true := rfl
theorem cc_icmp_isEquality_iult : isEquality ICmpOp.iult = false := rfl
theorem cc_icmp_isEquality_iule : isEquality ICmpOp.iule = false := rfl
theorem cc_icmp_isEquality_iugt : isEquality ICmpOp.iugt = false := rfl
theorem cc_icmp_isEquality_iuge : isEquality ICmpOp.iuge = false := rfl
theorem cc_icmp_isEquality_islt : isEquality ICmpOp.islt = false := rfl
theorem cc_icmp_isEquality_isle : isEquality ICmpOp.isle = false := rfl
theorem cc_icmp_isEquality_isgt : isEquality ICmpOp.isgt = false := rfl
theorem cc_icmp_isEquality_isge : isEquality ICmpOp.isge = false := rfl

-- --- FAITHFULNESS: isSignedCmp, per variant ---
theorem cc_icmp_isSigned_ieq : isSignedCmp ICmpOp.ieq = false := rfl
theorem cc_icmp_isSigned_ine : isSignedCmp ICmpOp.ine = false := rfl
theorem cc_icmp_isSigned_iult : isSignedCmp ICmpOp.iult = false := rfl
theorem cc_icmp_isSigned_iule : isSignedCmp ICmpOp.iule = false := rfl
theorem cc_icmp_isSigned_iugt : isSignedCmp ICmpOp.iugt = false := rfl
theorem cc_icmp_isSigned_iuge : isSignedCmp ICmpOp.iuge = false := rfl
theorem cc_icmp_isSigned_islt : isSignedCmp ICmpOp.islt = true := rfl
theorem cc_icmp_isSigned_isle : isSignedCmp ICmpOp.isle = true := rfl
theorem cc_icmp_isSigned_isgt : isSignedCmp ICmpOp.isgt = true := rfl
theorem cc_icmp_isSigned_isge : isSignedCmp ICmpOp.isge = true := rfl

-- --- FAITHFULNESS: isUnsignedCmp, per variant ---
theorem cc_icmp_isUnsigned_ieq : isUnsignedCmp ICmpOp.ieq = false := rfl
theorem cc_icmp_isUnsigned_ine : isUnsignedCmp ICmpOp.ine = false := rfl
theorem cc_icmp_isUnsigned_iult : isUnsignedCmp ICmpOp.iult = true := rfl
theorem cc_icmp_isUnsigned_iule : isUnsignedCmp ICmpOp.iule = true := rfl
theorem cc_icmp_isUnsigned_iugt : isUnsignedCmp ICmpOp.iugt = true := rfl
theorem cc_icmp_isUnsigned_iuge : isUnsignedCmp ICmpOp.iuge = true := rfl
theorem cc_icmp_isUnsigned_islt : isUnsignedCmp ICmpOp.islt = false := rfl
theorem cc_icmp_isUnsigned_isle : isUnsignedCmp ICmpOp.isle = false := rfl
theorem cc_icmp_isUnsigned_isgt : isUnsignedCmp ICmpOp.isgt = false := rfl
theorem cc_icmp_isUnsigned_isge : isUnsignedCmp ICmpOp.isge = false := rfl

-- --- METATHEOREM: signed and unsigned comparison families are DISJOINT.
-- No integer comparison predicate is both signed and unsigned. (All-ctor casesOn;
-- 10 nullary minors -> rfl.)
theorem cc_icmp_signed_unsigned_disjoint (c : ICmpOp) :
    Bool.and (isSignedCmp c) (isUnsignedCmp c) = false :=
  @ICmpOp.casesOn (fun k => Bool.and (isSignedCmp k) (isUnsignedCmp k) = false) c
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- --- METATHEOREM: the three families COVER every ICmpOp constructor.
-- Every integer comparison is equality OR signed OR unsigned.
theorem cc_icmp_cover_all (c : ICmpOp) :
    Bool.or (Bool.or (isEquality c) (isSignedCmp c)) (isUnsignedCmp c) = true :=
  @ICmpOp.casesOn
    (fun k => Bool.or (Bool.or (isEquality k) (isSignedCmp k)) (isUnsignedCmp k) = true) c
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- --- METATHEOREM: equality is DISJOINT from signed (additional partition edge).
theorem cc_icmp_equality_signed_disjoint (c : ICmpOp) :
    Bool.and (isEquality c) (isSignedCmp c) = false :=
  @ICmpOp.casesOn (fun k => Bool.and (isEquality k) (isSignedCmp k) = false) c
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- --- METATHEOREM: equality is DISJOINT from unsigned.
theorem cc_icmp_equality_unsigned_disjoint (c : ICmpOp) :
    Bool.and (isEquality c) (isUnsignedCmp c) = false :=
  @ICmpOp.casesOn (fun k => Bool.and (isEquality k) (isUnsignedCmp k) = false) c
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- ===========================================================================
-- FCmpOp (inst.rs:90). 12 nullary ctors, in DECLARATION ORDER:
--   OEq ONe OLt OLe OGt OGe UEq UNe ULt ULe UGt UGe
-- ===========================================================================
inductive FCmpOp where
  | oeq : FCmpOp
  | one : FCmpOp
  | olt : FCmpOp
  | ole : FCmpOp
  | ogt : FCmpOp
  | oge : FCmpOp
  | ueq : FCmpOp
  | une : FCmpOp
  | ult : FCmpOp
  | ule : FCmpOp
  | ugt : FCmpOp
  | uge : FCmpOp

-- isOrdered: the O-prefixed predicates (oeq one olt ole ogt oge). (Grounded in
-- IEEE 754 / LLVM fcmp: "ordered" = yields false if EITHER operand is NaN.)
def isOrdered : FCmpOp -> Bool := fun c =>
  @FCmpOp.casesOn (fun _ => Bool) c
    true true true true true true
    false false false false false false

-- isUnordered: the U-prefixed predicates (ueq une ult ule ugt uge). (Grounded:
-- "unordered" = yields true if EITHER operand is NaN.)
def isUnordered : FCmpOp -> Bool := fun c =>
  @FCmpOp.casesOn (fun _ => Bool) c
    false false false false false false
    true true true true true true

-- --- FAITHFULNESS: isOrdered, per variant ---
theorem cc_fcmp_isOrdered_oeq : isOrdered FCmpOp.oeq = true := rfl
theorem cc_fcmp_isOrdered_one : isOrdered FCmpOp.one = true := rfl
theorem cc_fcmp_isOrdered_olt : isOrdered FCmpOp.olt = true := rfl
theorem cc_fcmp_isOrdered_ole : isOrdered FCmpOp.ole = true := rfl
theorem cc_fcmp_isOrdered_ogt : isOrdered FCmpOp.ogt = true := rfl
theorem cc_fcmp_isOrdered_oge : isOrdered FCmpOp.oge = true := rfl
theorem cc_fcmp_isOrdered_ueq : isOrdered FCmpOp.ueq = false := rfl
theorem cc_fcmp_isOrdered_une : isOrdered FCmpOp.une = false := rfl
theorem cc_fcmp_isOrdered_ult : isOrdered FCmpOp.ult = false := rfl
theorem cc_fcmp_isOrdered_ule : isOrdered FCmpOp.ule = false := rfl
theorem cc_fcmp_isOrdered_ugt : isOrdered FCmpOp.ugt = false := rfl
theorem cc_fcmp_isOrdered_uge : isOrdered FCmpOp.uge = false := rfl

-- --- FAITHFULNESS: isUnordered, per variant ---
theorem cc_fcmp_isUnordered_oeq : isUnordered FCmpOp.oeq = false := rfl
theorem cc_fcmp_isUnordered_one : isUnordered FCmpOp.one = false := rfl
theorem cc_fcmp_isUnordered_olt : isUnordered FCmpOp.olt = false := rfl
theorem cc_fcmp_isUnordered_ole : isUnordered FCmpOp.ole = false := rfl
theorem cc_fcmp_isUnordered_ogt : isUnordered FCmpOp.ogt = false := rfl
theorem cc_fcmp_isUnordered_oge : isUnordered FCmpOp.oge = false := rfl
theorem cc_fcmp_isUnordered_ueq : isUnordered FCmpOp.ueq = true := rfl
theorem cc_fcmp_isUnordered_une : isUnordered FCmpOp.une = true := rfl
theorem cc_fcmp_isUnordered_ult : isUnordered FCmpOp.ult = true := rfl
theorem cc_fcmp_isUnordered_ule : isUnordered FCmpOp.ule = true := rfl
theorem cc_fcmp_isUnordered_ugt : isUnordered FCmpOp.ugt = true := rfl
theorem cc_fcmp_isUnordered_uge : isUnordered FCmpOp.uge = true := rfl

-- --- METATHEOREM: ordered and unordered float-compare families are DISJOINT.
theorem cc_fcmp_ordered_unordered_disjoint (c : FCmpOp) :
    Bool.and (isOrdered c) (isUnordered c) = false :=
  @FCmpOp.casesOn (fun k => Bool.and (isOrdered k) (isUnordered k) = false) c
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- --- METATHEOREM: every float comparison is ordered OR unordered (COVERS all).
-- Equivalently: every float-compare is ordered XOR unordered (disjoint + cover).
theorem cc_fcmp_cover_all (c : FCmpOp) :
    Bool.or (isOrdered c) (isUnordered c) = true :=
  @FCmpOp.casesOn (fun k => Bool.or (isOrdered k) (isUnordered k) = true) c
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- ===========================================================================
-- CastOp (inst.rs:107). 15 nullary ctors, in DECLARATION ORDER:
--   Trunc ZExt SExt FPTrunc FPExt FPToUI FPToSI UIToFP SIToFP PtrToInt
--   IntToPtr PtrToPtr Bitcast Transmute ReifyFnPointer
-- ===========================================================================
inductive CastOp where
  | trunc : CastOp
  | zext : CastOp
  | sext : CastOp
  | fptrunc : CastOp
  | fpext : CastOp
  | fptoui : CastOp
  | fptosi : CastOp
  | uitofp : CastOp
  | sitofp : CastOp
  | ptrtoint : CastOp
  | inttoptr : CastOp
  | ptrtoptr : CastOp
  | bitcast : CastOp
  | transmute : CastOp
  | reifyfnptr : CastOp

-- Conversion-taxonomy families (grounded in CLAUDE.md "Type conversions" + the
-- inst.rs Display strings). Order of the 15 minors follows declaration order.

-- isIntResize: integer-width changes (trunc, zext, sext).
def isIntResize : CastOp -> Bool := fun c =>
  @CastOp.casesOn (fun _ => Bool) c
    true true true
    false false false false false false false false false false false false

-- isFpResize: float-width changes (fptrunc, fpext).
def isFpResize : CastOp -> Bool := fun c =>
  @CastOp.casesOn (fun _ => Bool) c
    false false false
    true true
    false false false false false false false false false false

-- isFpToInt: float -> integer (fptoui, fptosi).
def isFpToInt : CastOp -> Bool := fun c =>
  @CastOp.casesOn (fun _ => Bool) c
    false false false false false
    true true
    false false false false false false false false

-- isIntToFp: integer -> float (uitofp, sitofp).
def isIntToFp : CastOp -> Bool := fun c =>
  @CastOp.casesOn (fun _ => Bool) c
    false false false false false false false
    true true
    false false false false false false

-- isPtrCast: pointer conversions (ptrtoint, inttoptr, ptrtoptr).
def isPtrCast : CastOp -> Bool := fun c =>
  @CastOp.casesOn (fun _ => Bool) c
    false false false false false false false false false
    true true true
    false false false

-- isReinterpret: bit-reinterpretations (bitcast, transmute, reify_fn_pointer).
def isReinterpret : CastOp -> Bool := fun c =>
  @CastOp.casesOn (fun _ => Bool) c
    false false false false false false false false false false false false
    true true true

-- isSignedCast: the SIGN-dependent casts (sext, fptosi, sitofp) — the casts
-- whose semantics interpret/produce a SIGNED value (sign-extend, float->signed,
-- signed->float). (Grounded: these are the only CastOp mnemonics whose behavior
-- depends on signedness; zext/fptoui/uitofp are the unsigned counterparts.)
def isSignedCast : CastOp -> Bool := fun c =>
  @CastOp.casesOn (fun _ => Bool) c
    false false true            -- trunc zext SEXT
    false false                 -- fptrunc fpext
    false true                  -- fptoui FPTOSI
    false true                  -- uitofp SITOFP
    false false false           -- ptrtoint inttoptr ptrtoptr
    false false false           -- bitcast transmute reifyfnptr

-- --- FAITHFULNESS: isIntResize, per variant ---
theorem cc_cast_isIntResize_trunc : isIntResize CastOp.trunc = true := rfl
theorem cc_cast_isIntResize_zext : isIntResize CastOp.zext = true := rfl
theorem cc_cast_isIntResize_sext : isIntResize CastOp.sext = true := rfl
theorem cc_cast_isIntResize_fptrunc : isIntResize CastOp.fptrunc = false := rfl
theorem cc_cast_isIntResize_fpext : isIntResize CastOp.fpext = false := rfl
theorem cc_cast_isIntResize_fptoui : isIntResize CastOp.fptoui = false := rfl
theorem cc_cast_isIntResize_fptosi : isIntResize CastOp.fptosi = false := rfl
theorem cc_cast_isIntResize_uitofp : isIntResize CastOp.uitofp = false := rfl
theorem cc_cast_isIntResize_sitofp : isIntResize CastOp.sitofp = false := rfl
theorem cc_cast_isIntResize_ptrtoint : isIntResize CastOp.ptrtoint = false := rfl
theorem cc_cast_isIntResize_inttoptr : isIntResize CastOp.inttoptr = false := rfl
theorem cc_cast_isIntResize_ptrtoptr : isIntResize CastOp.ptrtoptr = false := rfl
theorem cc_cast_isIntResize_bitcast : isIntResize CastOp.bitcast = false := rfl
theorem cc_cast_isIntResize_transmute : isIntResize CastOp.transmute = false := rfl
theorem cc_cast_isIntResize_reifyfnptr : isIntResize CastOp.reifyfnptr = false := rfl

-- --- FAITHFULNESS: isFpResize, the two true cases + representative falses ---
theorem cc_cast_isFpResize_fptrunc : isFpResize CastOp.fptrunc = true := rfl
theorem cc_cast_isFpResize_fpext : isFpResize CastOp.fpext = true := rfl
theorem cc_cast_isFpResize_trunc : isFpResize CastOp.trunc = false := rfl
theorem cc_cast_isFpResize_fptoui : isFpResize CastOp.fptoui = false := rfl
theorem cc_cast_isFpResize_bitcast : isFpResize CastOp.bitcast = false := rfl

-- --- FAITHFULNESS: isFpToInt ---
theorem cc_cast_isFpToInt_fptoui : isFpToInt CastOp.fptoui = true := rfl
theorem cc_cast_isFpToInt_fptosi : isFpToInt CastOp.fptosi = true := rfl
theorem cc_cast_isFpToInt_uitofp : isFpToInt CastOp.uitofp = false := rfl
theorem cc_cast_isFpToInt_fpext : isFpToInt CastOp.fpext = false := rfl

-- --- FAITHFULNESS: isIntToFp ---
theorem cc_cast_isIntToFp_uitofp : isIntToFp CastOp.uitofp = true := rfl
theorem cc_cast_isIntToFp_sitofp : isIntToFp CastOp.sitofp = true := rfl
theorem cc_cast_isIntToFp_fptosi : isIntToFp CastOp.fptosi = false := rfl
theorem cc_cast_isIntToFp_sext : isIntToFp CastOp.sext = false := rfl

-- --- FAITHFULNESS: isPtrCast ---
theorem cc_cast_isPtrCast_ptrtoint : isPtrCast CastOp.ptrtoint = true := rfl
theorem cc_cast_isPtrCast_inttoptr : isPtrCast CastOp.inttoptr = true := rfl
theorem cc_cast_isPtrCast_ptrtoptr : isPtrCast CastOp.ptrtoptr = true := rfl
theorem cc_cast_isPtrCast_bitcast : isPtrCast CastOp.bitcast = false := rfl
theorem cc_cast_isPtrCast_trunc : isPtrCast CastOp.trunc = false := rfl

-- --- FAITHFULNESS: isReinterpret ---
theorem cc_cast_isReinterpret_bitcast : isReinterpret CastOp.bitcast = true := rfl
theorem cc_cast_isReinterpret_transmute : isReinterpret CastOp.transmute = true := rfl
theorem cc_cast_isReinterpret_reifyfnptr : isReinterpret CastOp.reifyfnptr = true := rfl
theorem cc_cast_isReinterpret_ptrtoptr : isReinterpret CastOp.ptrtoptr = false := rfl
theorem cc_cast_isReinterpret_sext : isReinterpret CastOp.sext = false := rfl

-- --- FAITHFULNESS: isSignedCast (sext, fptosi, sitofp = true) ---
theorem cc_cast_isSignedCast_sext : isSignedCast CastOp.sext = true := rfl
theorem cc_cast_isSignedCast_fptosi : isSignedCast CastOp.fptosi = true := rfl
theorem cc_cast_isSignedCast_sitofp : isSignedCast CastOp.sitofp = true := rfl
theorem cc_cast_isSignedCast_zext : isSignedCast CastOp.zext = false := rfl
theorem cc_cast_isSignedCast_fptoui : isSignedCast CastOp.fptoui = false := rfl
theorem cc_cast_isSignedCast_uitofp : isSignedCast CastOp.uitofp = false := rfl
theorem cc_cast_isSignedCast_trunc : isSignedCast CastOp.trunc = false := rfl
theorem cc_cast_isSignedCast_bitcast : isSignedCast CastOp.bitcast = false := rfl

-- ===========================================================================
-- METATHEOREMS over CastOp (>=6 elaborating partition/coverage facts overall).
-- ===========================================================================

-- Sample disjointness: int-resize and pointer-cast families are DISJOINT.
theorem cc_cast_intresize_ptrcast_disjoint (c : CastOp) :
    Bool.and (isIntResize c) (isPtrCast c) = false :=
  @CastOp.casesOn (fun k => Bool.and (isIntResize k) (isPtrCast k) = false) c
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- More disjointness edges among the 6 conversion families:
theorem cc_cast_fpresize_fptoint_disjoint (c : CastOp) :
    Bool.and (isFpResize c) (isFpToInt c) = false :=
  @CastOp.casesOn (fun k => Bool.and (isFpResize k) (isFpToInt k) = false) c
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem cc_cast_fptoint_inttofp_disjoint (c : CastOp) :
    Bool.and (isFpToInt c) (isIntToFp c) = false :=
  @CastOp.casesOn (fun k => Bool.and (isFpToInt k) (isIntToFp k) = false) c
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem cc_cast_intresize_reinterpret_disjoint (c : CastOp) :
    Bool.and (isIntResize c) (isReinterpret c) = false :=
  @CastOp.casesOn (fun k => Bool.and (isIntResize k) (isReinterpret k) = false) c
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem cc_cast_ptrcast_reinterpret_disjoint (c : CastOp) :
    Bool.and (isPtrCast c) (isReinterpret c) = false :=
  @CastOp.casesOn (fun k => Bool.and (isPtrCast k) (isReinterpret k) = false) c
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- COVERAGE over the 6 conversion families: every CastOp belongs to exactly one
-- of {intResize, fpResize, fpToInt, intToFp, ptrCast, reinterpret} — here the
-- COVER direction: every CastOp is in at least one family.
theorem cc_cast_cover_all (c : CastOp) :
    Bool.or (Bool.or (Bool.or (isIntResize c) (isFpResize c))
             (Bool.or (isFpToInt c) (isIntToFp c)))
            (Bool.or (isPtrCast c) (isReinterpret c)) = true :=
  @CastOp.casesOn
    (fun k => Bool.or (Bool.or (Bool.or (isIntResize k) (isFpResize k))
              (Bool.or (isFpToInt k) (isIntToFp k)))
              (Bool.or (isPtrCast k) (isReinterpret k)) = true) c
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- isSignedCast is a SUB-family: every signed cast is one of the conversion
-- families (it never escapes the taxonomy). signedCast => covered.
theorem cc_cast_signed_implies_covered (c : CastOp) :
    Bool.or (Bool.not (isSignedCast c))
            (Bool.or (Bool.or (Bool.or (isIntResize c) (isFpResize c))
                     (Bool.or (isFpToInt c) (isIntToFp c)))
                    (Bool.or (isPtrCast c) (isReinterpret c))) = true :=
  @CastOp.casesOn
    (fun k => Bool.or (Bool.not (isSignedCast k))
              (Bool.or (Bool.or (Bool.or (isIntResize k) (isFpResize k))
                       (Bool.or (isFpToInt k) (isIntToFp k)))
                      (Bool.or (isPtrCast k) (isReinterpret k))) = true) c
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- isSignedCast is DISJOINT from the reinterpret family (signedness-free bitcasts).
theorem cc_cast_signed_reinterpret_disjoint (c : CastOp) :
    Bool.and (isSignedCast c) (isReinterpret c) = false :=
  @CastOp.casesOn (fun k => Bool.and (isSignedCast k) (isReinterpret k) = false) c
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

end InstCmpCast

-- ###########################################################################
-- Ordering (5) memory-strength lattice + AtomicRMWOp (10) op families
-- ###########################################################################
namespace InstAtomic

-- ===========================================================================
-- `Ordering` (inst.rs:127). Constructor order is fixed (the casesOn minors
-- below follow it): relaxed, acquire, release, acqrel, seqcst.
-- ===========================================================================
inductive MemOrd where
  | relaxed : MemOrd
  | acquire : MemOrd
  | release : MemOrd
  | acqrel : MemOrd
  | seqcst : MemOrd

-- Memory-ordering STRENGTH rank. NOT a literal Rust method: this encodes the
-- documented C++/Rust ordering hierarchy. Relaxed (no sync) = 0; Acquire and
-- Release are the two single-direction half-barriers (same strength tier) = 1;
-- AcqRel is the full acquire+release barrier = 2; SeqCst (total order) = 3.
def rank : MemOrd -> Nat := fun o =>
  @MemOrd.casesOn (fun _ => Nat) o
    (0)    -- relaxed
    (1)    -- acquire
    (1)    -- release
    (2)    -- acqrel
    (3)    -- seqcst

-- o is no stronger than p iff rank o <= rank p (Nat.ble on the ranks).
def strengthLE : MemOrd -> MemOrd -> Bool := fun o p =>
  Nat.ble (rank o) (rank p)

-- ===========================================================================
-- FAITHFULNESS to the rank assignment (per-variant, by casesOn iota).
-- ===========================================================================
theorem atom_rank_relaxed : rank MemOrd.relaxed = 0 := rfl
theorem atom_rank_acquire : rank MemOrd.acquire = 1 := rfl
theorem atom_rank_release : rank MemOrd.release = 1 := rfl
theorem atom_rank_acqrel : rank MemOrd.acqrel = 2 := rfl
theorem atom_rank_seqcst : rank MemOrd.seqcst = 3 := rfl

-- Acquire and Release sit at the SAME strength tier (peers, rank 1).
theorem atom_rank_acquire_eq_release : rank MemOrd.acquire = rank MemOrd.release := rfl

-- ===========================================================================
-- LATTICE LAWS for the strength order.
-- ===========================================================================

-- Reflexive: every ordering is no stronger than itself (rank o <= rank o).
-- Proven uniformly over all 5 constructors by casesOn (each minor is rfl,
-- since strengthLE o o reduces to Nat.ble k k = true at a concrete rank k).
theorem atom_strengthLE_refl (o : MemOrd) : strengthLE o o = true :=
  @MemOrd.casesOn (fun k => strengthLE k k = true) o
    rfl rfl rfl rfl rfl

-- SeqCst is the TOP element: every ordering is no stronger than SeqCst.
-- rank o <= 3 for every o, proven per-constructor by casesOn.
theorem atom_strengthLE_top (o : MemOrd) : strengthLE o MemOrd.seqcst = true :=
  @MemOrd.casesOn (fun k => strengthLE k MemOrd.seqcst = true) o
    rfl rfl rfl rfl rfl

-- Relaxed is the BOTTOM element: Relaxed is no stronger than any ordering.
-- 0 <= rank o for every o, proven per-constructor by casesOn.
theorem atom_strengthLE_bot (o : MemOrd) : strengthLE MemOrd.relaxed o = true :=
  @MemOrd.casesOn (fun k => strengthLE MemOrd.relaxed k = true) o
    rfl rfl rfl rfl rfl

-- ===========================================================================
-- PER-PAIR FAITHFULNESS of the strength order (concrete ordering comparisons).
-- ===========================================================================
-- Relaxed (0) is below SeqCst (3).
theorem atom_strengthLE_relaxed_seqcst : strengthLE MemOrd.relaxed MemOrd.seqcst = true := rfl
-- SeqCst (3) is NOT below Relaxed (0) — the order is genuinely a partial order,
-- not the trivial all-true relation.
theorem atom_strengthLE_seqcst_relaxed : strengthLE MemOrd.seqcst MemOrd.relaxed = false := rfl
-- Acquire (1) is below AcqRel (2).
theorem atom_strengthLE_acquire_acqrel : strengthLE MemOrd.acquire MemOrd.acqrel = true := rfl
-- AcqRel (2) is NOT below Acquire (1).
theorem atom_strengthLE_acqrel_acquire : strengthLE MemOrd.acqrel MemOrd.acquire = false := rfl
-- Release (1) is below AcqRel (2) (Release is one half of the full barrier).
theorem atom_strengthLE_release_acqrel : strengthLE MemOrd.release MemOrd.acqrel = true := rfl
-- Relaxed (0) is below Acquire (1).
theorem atom_strengthLE_relaxed_acquire : strengthLE MemOrd.relaxed MemOrd.acquire = true := rfl
-- AcqRel (2) is below SeqCst (3) — SeqCst is strictly above the full barrier.
theorem atom_strengthLE_acqrel_seqcst : strengthLE MemOrd.acqrel MemOrd.seqcst = true := rfl
-- Acquire (1) and Release (1) are mutually <= (same tier): each is no stronger
-- than the other.
theorem atom_strengthLE_acquire_release : strengthLE MemOrd.acquire MemOrd.release = true := rfl
theorem atom_strengthLE_release_acquire : strengthLE MemOrd.release MemOrd.acquire = true := rfl
-- SeqCst is not below AcqRel (top is strictly above the full barrier).
theorem atom_strengthLE_seqcst_acqrel : strengthLE MemOrd.seqcst MemOrd.acqrel = false := rfl

-- ===========================================================================
-- `AtomicRMWOp` (inst.rs:137). Constructor order is fixed (the casesOn minors
-- below follow it): axchg, aadd, asub, aand, aor, axor, amax, amin, aumax,
-- aumin.
-- ===========================================================================
inductive AtomicRMWOp where
  | axchg : AtomicRMWOp
  | aadd : AtomicRMWOp
  | asub : AtomicRMWOp
  | aand : AtomicRMWOp
  | aor : AtomicRMWOp
  | axor : AtomicRMWOp
  | amax : AtomicRMWOp
  | amin : AtomicRMWOp
  | aumax : AtomicRMWOp
  | aumin : AtomicRMWOp

-- Op-FAMILY classifiers. No single Rust method partitions AtomicRMWOp; this
-- matches the documented taxonomy (inst.rs Display strings + CLAUDE.md atomics
-- table): arithmetic {add,sub}, bitwise {and,or,xor}, signed min/max {max,min},
-- unsigned min/max {umax,umin}, and the exchange {xchg}.

-- isArith: aadd, asub.
def isArith : AtomicRMWOp -> Bool := fun r =>
  @AtomicRMWOp.casesOn (fun _ => Bool) r
    false   -- axchg
    true    -- aadd
    true    -- asub
    false   -- aand
    false   -- aor
    false   -- axor
    false   -- amax
    false   -- amin
    false   -- aumax
    false   -- aumin

-- isBitwise: aand, aor, axor.
def isBitwise : AtomicRMWOp -> Bool := fun r =>
  @AtomicRMWOp.casesOn (fun _ => Bool) r
    false   -- axchg
    false   -- aadd
    false   -- asub
    true    -- aand
    true    -- aor
    true    -- axor
    false   -- amax
    false   -- amin
    false   -- aumax
    false   -- aumin

-- isSignedMinMax: amax, amin.
def isSignedMinMax : AtomicRMWOp -> Bool := fun r =>
  @AtomicRMWOp.casesOn (fun _ => Bool) r
    false   -- axchg
    false   -- aadd
    false   -- asub
    false   -- aand
    false   -- aor
    false   -- axor
    true    -- amax
    true    -- amin
    false   -- aumax
    false   -- aumin

-- isUnsignedMinMax: aumax, aumin.
def isUnsignedMinMax : AtomicRMWOp -> Bool := fun r =>
  @AtomicRMWOp.casesOn (fun _ => Bool) r
    false   -- axchg
    false   -- aadd
    false   -- asub
    false   -- aand
    false   -- aor
    false   -- axor
    false   -- amax
    false   -- amin
    true    -- aumax
    true    -- aumin

-- isXchg: axchg.
def isXchg : AtomicRMWOp -> Bool := fun r =>
  @AtomicRMWOp.casesOn (fun _ => Bool) r
    true    -- axchg
    false   -- aadd
    false   -- asub
    false   -- aand
    false   -- aor
    false   -- axor
    false   -- amax
    false   -- amin
    false   -- aumax
    false   -- aumin

-- The five families OR'd together — used for the coverage metatheorem.
def inSomeFamily : AtomicRMWOp -> Bool := fun r =>
  Bool.or (isArith r)
    (Bool.or (isBitwise r)
      (Bool.or (isSignedMinMax r)
        (Bool.or (isUnsignedMinMax r) (isXchg r))))

-- ===========================================================================
-- PER-VARIANT FAITHFULNESS of every family classifier (10 ctors x 5 families).
-- Each is a casesOn iota-equality (rfl).
-- ===========================================================================
-- isArith
theorem atom_isArith_axchg : isArith AtomicRMWOp.axchg = false := rfl
theorem atom_isArith_aadd : isArith AtomicRMWOp.aadd = true := rfl
theorem atom_isArith_asub : isArith AtomicRMWOp.asub = true := rfl
theorem atom_isArith_aand : isArith AtomicRMWOp.aand = false := rfl
theorem atom_isArith_aor : isArith AtomicRMWOp.aor = false := rfl
theorem atom_isArith_axor : isArith AtomicRMWOp.axor = false := rfl
theorem atom_isArith_amax : isArith AtomicRMWOp.amax = false := rfl
theorem atom_isArith_amin : isArith AtomicRMWOp.amin = false := rfl
theorem atom_isArith_aumax : isArith AtomicRMWOp.aumax = false := rfl
theorem atom_isArith_aumin : isArith AtomicRMWOp.aumin = false := rfl

-- isBitwise
theorem atom_isBitwise_axchg : isBitwise AtomicRMWOp.axchg = false := rfl
theorem atom_isBitwise_aadd : isBitwise AtomicRMWOp.aadd = false := rfl
theorem atom_isBitwise_asub : isBitwise AtomicRMWOp.asub = false := rfl
theorem atom_isBitwise_aand : isBitwise AtomicRMWOp.aand = true := rfl
theorem atom_isBitwise_aor : isBitwise AtomicRMWOp.aor = true := rfl
theorem atom_isBitwise_axor : isBitwise AtomicRMWOp.axor = true := rfl
theorem atom_isBitwise_amax : isBitwise AtomicRMWOp.amax = false := rfl
theorem atom_isBitwise_amin : isBitwise AtomicRMWOp.amin = false := rfl
theorem atom_isBitwise_aumax : isBitwise AtomicRMWOp.aumax = false := rfl
theorem atom_isBitwise_aumin : isBitwise AtomicRMWOp.aumin = false := rfl

-- isSignedMinMax
theorem atom_isSignedMinMax_axchg : isSignedMinMax AtomicRMWOp.axchg = false := rfl
theorem atom_isSignedMinMax_aadd : isSignedMinMax AtomicRMWOp.aadd = false := rfl
theorem atom_isSignedMinMax_asub : isSignedMinMax AtomicRMWOp.asub = false := rfl
theorem atom_isSignedMinMax_aand : isSignedMinMax AtomicRMWOp.aand = false := rfl
theorem atom_isSignedMinMax_aor : isSignedMinMax AtomicRMWOp.aor = false := rfl
theorem atom_isSignedMinMax_axor : isSignedMinMax AtomicRMWOp.axor = false := rfl
theorem atom_isSignedMinMax_amax : isSignedMinMax AtomicRMWOp.amax = true := rfl
theorem atom_isSignedMinMax_amin : isSignedMinMax AtomicRMWOp.amin = true := rfl
theorem atom_isSignedMinMax_aumax : isSignedMinMax AtomicRMWOp.aumax = false := rfl
theorem atom_isSignedMinMax_aumin : isSignedMinMax AtomicRMWOp.aumin = false := rfl

-- isUnsignedMinMax
theorem atom_isUnsignedMinMax_axchg : isUnsignedMinMax AtomicRMWOp.axchg = false := rfl
theorem atom_isUnsignedMinMax_aadd : isUnsignedMinMax AtomicRMWOp.aadd = false := rfl
theorem atom_isUnsignedMinMax_asub : isUnsignedMinMax AtomicRMWOp.asub = false := rfl
theorem atom_isUnsignedMinMax_aand : isUnsignedMinMax AtomicRMWOp.aand = false := rfl
theorem atom_isUnsignedMinMax_aor : isUnsignedMinMax AtomicRMWOp.aor = false := rfl
theorem atom_isUnsignedMinMax_axor : isUnsignedMinMax AtomicRMWOp.axor = false := rfl
theorem atom_isUnsignedMinMax_amax : isUnsignedMinMax AtomicRMWOp.amax = false := rfl
theorem atom_isUnsignedMinMax_amin : isUnsignedMinMax AtomicRMWOp.amin = false := rfl
theorem atom_isUnsignedMinMax_aumax : isUnsignedMinMax AtomicRMWOp.aumax = true := rfl
theorem atom_isUnsignedMinMax_aumin : isUnsignedMinMax AtomicRMWOp.aumin = true := rfl

-- isXchg
theorem atom_isXchg_axchg : isXchg AtomicRMWOp.axchg = true := rfl
theorem atom_isXchg_aadd : isXchg AtomicRMWOp.aadd = false := rfl
theorem atom_isXchg_asub : isXchg AtomicRMWOp.asub = false := rfl
theorem atom_isXchg_aand : isXchg AtomicRMWOp.aand = false := rfl
theorem atom_isXchg_aor : isXchg AtomicRMWOp.aor = false := rfl
theorem atom_isXchg_axor : isXchg AtomicRMWOp.axor = false := rfl
theorem atom_isXchg_amax : isXchg AtomicRMWOp.amax = false := rfl
theorem atom_isXchg_amin : isXchg AtomicRMWOp.amin = false := rfl
theorem atom_isXchg_aumax : isXchg AtomicRMWOp.aumax = false := rfl
theorem atom_isXchg_aumin : isXchg AtomicRMWOp.aumin = false := rfl

-- ===========================================================================
-- PARTITION METATHEOREMS (universally quantified over all 10 ctors). Each is a
-- casesOn over AtomicRMWOp with one rfl minor per constructor (all nullary).
-- ===========================================================================

-- Signed min/max and unsigned min/max are disjoint families.
theorem atom_signed_unsigned_disjoint (r : AtomicRMWOp) :
    Bool.and (isSignedMinMax r) (isUnsignedMinMax r) = false :=
  @AtomicRMWOp.casesOn (fun k => Bool.and (isSignedMinMax k) (isUnsignedMinMax k) = false) r
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- Arithmetic and bitwise are disjoint families.
theorem atom_arith_bitwise_disjoint (r : AtomicRMWOp) :
    Bool.and (isArith r) (isBitwise r) = false :=
  @AtomicRMWOp.casesOn (fun k => Bool.and (isArith k) (isBitwise k) = false) r
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- Arithmetic and signed-min/max are disjoint.
theorem atom_arith_signed_disjoint (r : AtomicRMWOp) :
    Bool.and (isArith r) (isSignedMinMax r) = false :=
  @AtomicRMWOp.casesOn (fun k => Bool.and (isArith k) (isSignedMinMax k) = false) r
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- Xchg is disjoint from arithmetic (xchg is its own family).
theorem atom_xchg_arith_disjoint (r : AtomicRMWOp) :
    Bool.and (isXchg r) (isArith r) = false :=
  @AtomicRMWOp.casesOn (fun k => Bool.and (isXchg k) (isArith k) = false) r
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- Bitwise is disjoint from unsigned-min/max.
theorem atom_bitwise_unsigned_disjoint (r : AtomicRMWOp) :
    Bool.and (isBitwise r) (isUnsignedMinMax r) = false :=
  @AtomicRMWOp.casesOn (fun k => Bool.and (isBitwise k) (isUnsignedMinMax k) = false) r
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- COVERAGE: every AtomicRMWOp belongs to exactly one of the five families
-- (the union of the five classifiers covers all 10 constructors).
theorem atom_family_coverage (r : AtomicRMWOp) : inSomeFamily r = true :=
  @AtomicRMWOp.casesOn (fun k => inSomeFamily k = true) r
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

end InstAtomic
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

/// Every theorem across the four instruction-operation-type slices, in order.
const INST_THEOREMS: &[&str] = &[
    // --- InstKind (102) ---
    "inst_isTerminator_ibinop",
    "inst_isTerminator_iunop",
    "inst_isTerminator_ioverflow",
    "inst_isTerminator_iicmp",
    "inst_isTerminator_ifcmp",
    "inst_isTerminator_icast",
    "inst_isTerminator_iload",
    "inst_isTerminator_istore",
    "inst_isTerminator_ialloca",
    "inst_isTerminator_iheapalloc",
    "inst_isTerminator_igep",
    "inst_isTerminator_iptrdata",
    "inst_isTerminator_iptrmetadata",
    "inst_isTerminator_iptrfromparts",
    "inst_isTerminator_iatomicload",
    "inst_isTerminator_iatomicstore",
    "inst_isTerminator_iatomicrmw",
    "inst_isTerminator_icmpxchg",
    "inst_isTerminator_ifence",
    "inst_isTerminator_ibr",
    "inst_isTerminator_icondbr",
    "inst_isTerminator_iswitch",
    "inst_isTerminator_icall",
    "inst_isTerminator_icallindirect",
    "inst_isTerminator_ireturn",
    "inst_isTerminator_iextractfield",
    "inst_isTerminator_iinsertfield",
    "inst_isTerminator_iextractelement",
    "inst_isTerminator_iinsertelement",
    "inst_isTerminator_iconst",
    "inst_isTerminator_inullptr",
    "inst_isTerminator_iglobaladdr",
    "inst_isTerminator_iundef",
    "inst_isTerminator_iassume",
    "inst_isTerminator_iassert",
    "inst_isTerminator_iunreachable",
    "inst_isTerminator_icopy",
    "inst_isTerminator_iselect",
    "inst_isTerminator_iborrow",
    "inst_isTerminator_iborrowmut",
    "inst_isTerminator_iendborrow",
    "inst_isTerminator_iretain",
    "inst_isTerminator_irelease",
    "inst_isTerminator_isunique",
    "inst_isTerminator_idealloc",
    "inst_isTerminator_iopenframe",
    "inst_isTerminator_ibindslot",
    "inst_isTerminator_iloadslot",
    "inst_isTerminator_icloseframe",
    "inst_isTerminator_idialectop",
    "inst_hasSideEffects_ibinop",
    "inst_hasSideEffects_iunop",
    "inst_hasSideEffects_ioverflow",
    "inst_hasSideEffects_iicmp",
    "inst_hasSideEffects_ifcmp",
    "inst_hasSideEffects_icast",
    "inst_hasSideEffects_iload",
    "inst_hasSideEffects_istore",
    "inst_hasSideEffects_ialloca",
    "inst_hasSideEffects_iheapalloc",
    "inst_hasSideEffects_igep",
    "inst_hasSideEffects_iptrdata",
    "inst_hasSideEffects_iptrmetadata",
    "inst_hasSideEffects_iptrfromparts",
    "inst_hasSideEffects_iatomicload",
    "inst_hasSideEffects_iatomicstore",
    "inst_hasSideEffects_iatomicrmw",
    "inst_hasSideEffects_icmpxchg",
    "inst_hasSideEffects_ifence",
    "inst_hasSideEffects_ibr",
    "inst_hasSideEffects_icondbr",
    "inst_hasSideEffects_iswitch",
    "inst_hasSideEffects_icall",
    "inst_hasSideEffects_icallindirect",
    "inst_hasSideEffects_ireturn",
    "inst_hasSideEffects_iextractfield",
    "inst_hasSideEffects_iinsertfield",
    "inst_hasSideEffects_iextractelement",
    "inst_hasSideEffects_iinsertelement",
    "inst_hasSideEffects_iconst",
    "inst_hasSideEffects_inullptr",
    "inst_hasSideEffects_iglobaladdr",
    "inst_hasSideEffects_iundef",
    "inst_hasSideEffects_iassume",
    "inst_hasSideEffects_iassert",
    "inst_hasSideEffects_iunreachable",
    "inst_hasSideEffects_icopy",
    "inst_hasSideEffects_iselect",
    "inst_hasSideEffects_iborrow",
    "inst_hasSideEffects_iborrowmut",
    "inst_hasSideEffects_iendborrow",
    "inst_hasSideEffects_iretain",
    "inst_hasSideEffects_irelease",
    "inst_hasSideEffects_isunique",
    "inst_hasSideEffects_idealloc",
    "inst_hasSideEffects_iopenframe",
    "inst_hasSideEffects_ibindslot",
    "inst_hasSideEffects_iloadslot",
    "inst_hasSideEffects_icloseframe",
    "inst_hasSideEffects_idialectop",
    "inst_terminator_implies_side_effects",
    "inst_pure_excludes_side_effects",
    // --- InstBinOp (85) ---
    "bop_isFloatOp_add",
    "bop_isFloatOp_sub",
    "bop_isFloatOp_mul",
    "bop_isFloatOp_udiv",
    "bop_isFloatOp_sdiv",
    "bop_isFloatOp_urem",
    "bop_isFloatOp_srem",
    "bop_isFloatOp_fadd",
    "bop_isFloatOp_fsub",
    "bop_isFloatOp_fmul",
    "bop_isFloatOp_fdiv",
    "bop_isFloatOp_frem",
    "bop_isFloatOp_fmin",
    "bop_isFloatOp_fmax",
    "bop_isFloatOp_band",
    "bop_isFloatOp_bor",
    "bop_isFloatOp_bxor",
    "bop_isFloatOp_shl",
    "bop_isFloatOp_lshr",
    "bop_isFloatOp_ashr",
    "bop_isIntArith_add",
    "bop_isIntArith_sub",
    "bop_isIntArith_mul",
    "bop_isIntArith_udiv",
    "bop_isIntArith_fadd",
    "bop_isIntArith_band",
    "bop_isIntArith_shl",
    "bop_isDivRem_udiv",
    "bop_isDivRem_sdiv",
    "bop_isDivRem_urem",
    "bop_isDivRem_srem",
    "bop_isDivRem_add",
    "bop_isDivRem_fdiv",
    "bop_isDivRem_shl",
    "bop_isBitwise_band",
    "bop_isBitwise_bor",
    "bop_isBitwise_bxor",
    "bop_isBitwise_add",
    "bop_isBitwise_shl",
    "bop_isBitwise_ashr",
    "bop_isBitwise_fadd",
    "bop_isShift_shl",
    "bop_isShift_lshr",
    "bop_isShift_ashr",
    "bop_isShift_band",
    "bop_isShift_add",
    "bop_isShift_fmul",
    "bop_isSignedOp_sdiv",
    "bop_isSignedOp_srem",
    "bop_isSignedOp_ashr",
    "bop_isSignedOp_udiv",
    "bop_isSignedOp_urem",
    "bop_isSignedOp_lshr",
    "bop_isSignedOp_add",
    "bop_isSignedOp_fadd",
    "bop_isFloatUn_neg",
    "bop_isFloatUn_fneg",
    "bop_isFloatUn_fabs",
    "bop_isFloatUn_fsqrt",
    "bop_isFloatUn_ffloor",
    "bop_isFloatUn_fceil",
    "bop_isFloatUn_ftrunc",
    "bop_isFloatUn_bnot",
    "bop_isFloatUn_ctpop",
    "bop_isIntUn_neg",
    "bop_isIntUn_fneg",
    "bop_isIntUn_fabs",
    "bop_isIntUn_fsqrt",
    "bop_isIntUn_ffloor",
    "bop_isIntUn_fceil",
    "bop_isIntUn_ftrunc",
    "bop_isIntUn_bnot",
    "bop_isIntUn_ctpop",
    "bop_part_float_intarith_disjoint",
    "bop_part_float_bitwise_disjoint",
    "bop_part_bitwise_shift_disjoint",
    "bop_part_float_divrem_disjoint",
    "bop_part_intarith_divrem_disjoint",
    "bop_part_intarith_shift_disjoint",
    "bop_part_bitwise_divrem_disjoint",
    "bop_part_signed_not_float",
    "bop_part_signed_not_intarith",
    "bop_part_signed_implies_divrem_or_shift",
    "bop_part_unop_float_int_disjoint",
    "bop_part_unop_float_int_total",
    // --- InstCmpCast (114) ---
    "cc_icmp_isEquality_ieq",
    "cc_icmp_isEquality_ine",
    "cc_icmp_isEquality_iult",
    "cc_icmp_isEquality_iule",
    "cc_icmp_isEquality_iugt",
    "cc_icmp_isEquality_iuge",
    "cc_icmp_isEquality_islt",
    "cc_icmp_isEquality_isle",
    "cc_icmp_isEquality_isgt",
    "cc_icmp_isEquality_isge",
    "cc_icmp_isSigned_ieq",
    "cc_icmp_isSigned_ine",
    "cc_icmp_isSigned_iult",
    "cc_icmp_isSigned_iule",
    "cc_icmp_isSigned_iugt",
    "cc_icmp_isSigned_iuge",
    "cc_icmp_isSigned_islt",
    "cc_icmp_isSigned_isle",
    "cc_icmp_isSigned_isgt",
    "cc_icmp_isSigned_isge",
    "cc_icmp_isUnsigned_ieq",
    "cc_icmp_isUnsigned_ine",
    "cc_icmp_isUnsigned_iult",
    "cc_icmp_isUnsigned_iule",
    "cc_icmp_isUnsigned_iugt",
    "cc_icmp_isUnsigned_iuge",
    "cc_icmp_isUnsigned_islt",
    "cc_icmp_isUnsigned_isle",
    "cc_icmp_isUnsigned_isgt",
    "cc_icmp_isUnsigned_isge",
    "cc_icmp_signed_unsigned_disjoint",
    "cc_icmp_cover_all",
    "cc_icmp_equality_signed_disjoint",
    "cc_icmp_equality_unsigned_disjoint",
    "cc_fcmp_isOrdered_oeq",
    "cc_fcmp_isOrdered_one",
    "cc_fcmp_isOrdered_olt",
    "cc_fcmp_isOrdered_ole",
    "cc_fcmp_isOrdered_ogt",
    "cc_fcmp_isOrdered_oge",
    "cc_fcmp_isOrdered_ueq",
    "cc_fcmp_isOrdered_une",
    "cc_fcmp_isOrdered_ult",
    "cc_fcmp_isOrdered_ule",
    "cc_fcmp_isOrdered_ugt",
    "cc_fcmp_isOrdered_uge",
    "cc_fcmp_isUnordered_oeq",
    "cc_fcmp_isUnordered_one",
    "cc_fcmp_isUnordered_olt",
    "cc_fcmp_isUnordered_ole",
    "cc_fcmp_isUnordered_ogt",
    "cc_fcmp_isUnordered_oge",
    "cc_fcmp_isUnordered_ueq",
    "cc_fcmp_isUnordered_une",
    "cc_fcmp_isUnordered_ult",
    "cc_fcmp_isUnordered_ule",
    "cc_fcmp_isUnordered_ugt",
    "cc_fcmp_isUnordered_uge",
    "cc_fcmp_ordered_unordered_disjoint",
    "cc_fcmp_cover_all",
    "cc_cast_isIntResize_trunc",
    "cc_cast_isIntResize_zext",
    "cc_cast_isIntResize_sext",
    "cc_cast_isIntResize_fptrunc",
    "cc_cast_isIntResize_fpext",
    "cc_cast_isIntResize_fptoui",
    "cc_cast_isIntResize_fptosi",
    "cc_cast_isIntResize_uitofp",
    "cc_cast_isIntResize_sitofp",
    "cc_cast_isIntResize_ptrtoint",
    "cc_cast_isIntResize_inttoptr",
    "cc_cast_isIntResize_ptrtoptr",
    "cc_cast_isIntResize_bitcast",
    "cc_cast_isIntResize_transmute",
    "cc_cast_isIntResize_reifyfnptr",
    "cc_cast_isFpResize_fptrunc",
    "cc_cast_isFpResize_fpext",
    "cc_cast_isFpResize_trunc",
    "cc_cast_isFpResize_fptoui",
    "cc_cast_isFpResize_bitcast",
    "cc_cast_isFpToInt_fptoui",
    "cc_cast_isFpToInt_fptosi",
    "cc_cast_isFpToInt_uitofp",
    "cc_cast_isFpToInt_fpext",
    "cc_cast_isIntToFp_uitofp",
    "cc_cast_isIntToFp_sitofp",
    "cc_cast_isIntToFp_fptosi",
    "cc_cast_isIntToFp_sext",
    "cc_cast_isPtrCast_ptrtoint",
    "cc_cast_isPtrCast_inttoptr",
    "cc_cast_isPtrCast_ptrtoptr",
    "cc_cast_isPtrCast_bitcast",
    "cc_cast_isPtrCast_trunc",
    "cc_cast_isReinterpret_bitcast",
    "cc_cast_isReinterpret_transmute",
    "cc_cast_isReinterpret_reifyfnptr",
    "cc_cast_isReinterpret_ptrtoptr",
    "cc_cast_isReinterpret_sext",
    "cc_cast_isSignedCast_sext",
    "cc_cast_isSignedCast_fptosi",
    "cc_cast_isSignedCast_sitofp",
    "cc_cast_isSignedCast_zext",
    "cc_cast_isSignedCast_fptoui",
    "cc_cast_isSignedCast_uitofp",
    "cc_cast_isSignedCast_trunc",
    "cc_cast_isSignedCast_bitcast",
    "cc_cast_intresize_ptrcast_disjoint",
    "cc_cast_fpresize_fptoint_disjoint",
    "cc_cast_fptoint_inttofp_disjoint",
    "cc_cast_intresize_reinterpret_disjoint",
    "cc_cast_ptrcast_reinterpret_disjoint",
    "cc_cast_cover_all",
    "cc_cast_signed_implies_covered",
    "cc_cast_signed_reinterpret_disjoint",
    // --- InstAtomic (75) ---
    "atom_rank_relaxed",
    "atom_rank_acquire",
    "atom_rank_release",
    "atom_rank_acqrel",
    "atom_rank_seqcst",
    "atom_rank_acquire_eq_release",
    "atom_strengthLE_refl",
    "atom_strengthLE_top",
    "atom_strengthLE_bot",
    "atom_strengthLE_relaxed_seqcst",
    "atom_strengthLE_seqcst_relaxed",
    "atom_strengthLE_acquire_acqrel",
    "atom_strengthLE_acqrel_acquire",
    "atom_strengthLE_release_acqrel",
    "atom_strengthLE_relaxed_acquire",
    "atom_strengthLE_acqrel_seqcst",
    "atom_strengthLE_acquire_release",
    "atom_strengthLE_release_acquire",
    "atom_strengthLE_seqcst_acqrel",
    "atom_isArith_axchg",
    "atom_isArith_aadd",
    "atom_isArith_asub",
    "atom_isArith_aand",
    "atom_isArith_aor",
    "atom_isArith_axor",
    "atom_isArith_amax",
    "atom_isArith_amin",
    "atom_isArith_aumax",
    "atom_isArith_aumin",
    "atom_isBitwise_axchg",
    "atom_isBitwise_aadd",
    "atom_isBitwise_asub",
    "atom_isBitwise_aand",
    "atom_isBitwise_aor",
    "atom_isBitwise_axor",
    "atom_isBitwise_amax",
    "atom_isBitwise_amin",
    "atom_isBitwise_aumax",
    "atom_isBitwise_aumin",
    "atom_isSignedMinMax_axchg",
    "atom_isSignedMinMax_aadd",
    "atom_isSignedMinMax_asub",
    "atom_isSignedMinMax_aand",
    "atom_isSignedMinMax_aor",
    "atom_isSignedMinMax_axor",
    "atom_isSignedMinMax_amax",
    "atom_isSignedMinMax_amin",
    "atom_isSignedMinMax_aumax",
    "atom_isSignedMinMax_aumin",
    "atom_isUnsignedMinMax_axchg",
    "atom_isUnsignedMinMax_aadd",
    "atom_isUnsignedMinMax_asub",
    "atom_isUnsignedMinMax_aand",
    "atom_isUnsignedMinMax_aor",
    "atom_isUnsignedMinMax_axor",
    "atom_isUnsignedMinMax_amax",
    "atom_isUnsignedMinMax_amin",
    "atom_isUnsignedMinMax_aumax",
    "atom_isUnsignedMinMax_aumin",
    "atom_isXchg_axchg",
    "atom_isXchg_aadd",
    "atom_isXchg_asub",
    "atom_isXchg_aand",
    "atom_isXchg_aor",
    "atom_isXchg_axor",
    "atom_isXchg_amax",
    "atom_isXchg_amin",
    "atom_isXchg_aumax",
    "atom_isXchg_aumin",
    "atom_signed_unsigned_disjoint",
    "atom_arith_bitwise_disjoint",
    "atom_arith_signed_disjoint",
    "atom_xchg_arith_disjoint",
    "atom_bitwise_unsigned_disjoint",
    "atom_family_coverage",
];

#[test]
fn inst_types_elaborate_and_kernel_check() {
    elaborate_module(INST_SOURCE).expect(
        "the trust-ir instruction-operation types (Inst kind + BinOp/UnOp/ICmp/FCmp/Cast/Ordering/\
         AtomicRMW), faithful to inst.rs, must elaborate and kernel-check together",
    );
}

#[test]
fn inst_types_faithfulness_theorems_are_proven_down_to_the_foundational_axioms() {
    let env = elaborate_module(INST_SOURCE)
        .expect("the instruction-types module must elaborate before auditing its theorems");
    for thm in INST_THEOREMS {
        assert_proven_to_foundations(&env, thm);
    }
    println!(
        "ALL TRUST INSTRUCTION-OPERATION TYPES ARE CLEAN TYPES: {} faithfulness + structural \
         theorems over trust-ir's instruction enums, every one proven to the 3 foundational axioms.",
        INST_THEOREMS.len()
    );
}
