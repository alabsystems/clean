// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! TRUST INSTRUCTIONS ARE WELL-TYPED — trust-ir's instruction RESULT-TYPING rules
//! (inst.rs + ty.rs), proven as Clean theorems down to the 3 foundational axioms.
//!
//! The capstone tying the `Ty` model (tyfull_e2e.rs/tyall_e2e.rs) to the `Inst`
//! model (inst_types_e2e.rs): not just each type/instruction in isolation, but the
//! TYPING DISCIPLINE that relates them. Four namespaces, each a trust-ir rule:
//!
//!   * `TypArith`   — `Inst::BinOp`/`Inst::UnOp` result type = the operand type
//!       (arithmetic/bitwise/shift preserve type), and preserve numeric/integer/float.
//!   * `TypCompare` — `Inst::ICmp`/`Inst::FCmp` result = `Ty::comparison_result_ty`
//!       (ty.rs:289): always boolish, lane count preserved, predicate-independent.
//!   * `TypCast`    — `Inst::Cast` result = the TARGET type, and the result kind
//!       (int/float/ptr) is exactly the target kind.
//!   * `TypOvfSel`  — `Inst::Overflow` result = `(value, overflow-flag)` pair
//!       (checked arithmetic), `Inst::Select` preserves value type with condition
//!       = `Ty::select_condition_ty` (ty.rs:300).
//!
//! Every theorem passes the `axiom_deps(name).is_empty()` bedrock gate. The four
//! slices elaborate together in one environment.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

const TYPEDINST_SOURCE: &str = r#"

-- ###########################################################################
-- BinOp/UnOp result-type PRESERVATION (result = operand type) + numeric/integer preservation
-- ###########################################################################
namespace TypArith

-- A compact image of the trust-ir `Ty` scalars relevant to BinOp/UnOp typing:
-- ti32 (Ty::I32), tu32 (Ty::U32), tf32 (Ty::F32), tbool (Ty::Bool). Four nullary
-- ctors (>=2, a genuine sum type). Constructor order is fixed; the casesOn minors
-- below follow it: ti32, tu32, tf32, tbool.
inductive Ty where
  | ti32 : Ty
  | tu32 : Ty
  | tf32 : Ty
  | tbool : Ty

-- The BinOp family of trust-ir `BinOp` (inst.rs:11), the integer/bitwise/shift
-- subset whose result type is the operand type: Add/Sub/Mul, UDiv/SDiv, URem/SRem,
-- And/Or/Xor (bitwise, prefixed `b` to avoid colliding with Bool), Shl/LShr/AShr.
-- 13 nullary ctors in declaration order.
inductive Bop where
  | add : Bop
  | sub : Bop
  | mul : Bop
  | udiv : Bop
  | sdiv : Bop
  | urem : Bop
  | srem : Bop
  | band : Bop
  | bor : Bop
  | bxor : Bop
  | shl : Bop
  | lshr : Bop
  | ashr : Bop

-- The UnOp family of trust-ir `UnOp` (inst.rs:44) whose result type is the operand
-- type: Neg, Not (bitwise complement, prefixed `b`), CtPop (population count). 3
-- nullary ctors in declaration order.
inductive Uop where
  | neg : Uop
  | bnot : Uop
  | ctpop : Uop

-- ===========================================================================
-- ty.rs SCALAR CLASSIFIERS on the compact Ty.
--   is_integer (ty.rs:191): ti32 (I32) and tu32 (U32) -> true; tf32/tbool false.
--   is_float   (ty.rs:205): tf32 (F32) -> true; the rest false.
--   is_numeric (ty.rs:209) = is_integer || is_float.
-- ===========================================================================
def isInteger : Ty -> Bool := fun t =>
  @Ty.casesOn (fun _ => Bool) t
    true true false false

def isFloat : Ty -> Bool := fun t =>
  @Ty.casesOn (fun _ => Bool) t
    false false true false

def isNumeric : Ty -> Bool := fun t => Bool.or (isInteger t) (isFloat t)

-- ===========================================================================
-- THE TYPING RULE. trust-ir `Inst::BinOp { op, ty, lhs, rhs }` (inst.rs:423) and
-- `Inst::UnOp { op, ty, operand }` (inst.rs:429) each CARRY the result type `ty`
-- as a struct field, and that field IS the operand type — arithmetic, bitwise, and
-- shift binops (and the unary ops) all RETURN the operand type. So the result-type
-- function is the second projection: identity on the operand type, ignoring `op`.
-- ===========================================================================
def binResultTy : Bop -> Ty -> Ty := fun _op t => t
def unResultTy : Uop -> Ty -> Ty := fun _op t => t

-- ===========================================================================
-- HEADLINE TYPE-PRESERVATION THEOREM (BinOp): for EVERY op and EVERY operand type,
-- the result type equals the operand type. This is trust-ir's BinOp result-typing
-- rule, stated over all ops and all types. By rfl (binResultTy is identity in t).
-- ===========================================================================
theorem tyar_binResultTy_preserves (op : Bop) (t : Ty) : binResultTy op t = t := rfl

-- HEADLINE TYPE-PRESERVATION THEOREM (UnOp): same rule for unary ops.
theorem tyar_unResultTy_preserves (op : Uop) (t : Ty) : unResultTy op t = t := rfl

-- ===========================================================================
-- PER-OP REPRESENTATIVES (BinOp): one per op family — arithmetic (add/sub/mul),
-- division (udiv/sdiv), remainder (urem/srem), bitwise (band/bor/bxor), shift
-- (shl/lshr/ashr). Each is binResultTy <op> t = t for an arbitrary t, by rfl.
-- ===========================================================================
theorem tyar_binResultTy_add (t : Ty) : binResultTy Bop.add t = t := rfl
theorem tyar_binResultTy_sub (t : Ty) : binResultTy Bop.sub t = t := rfl
theorem tyar_binResultTy_mul (t : Ty) : binResultTy Bop.mul t = t := rfl
theorem tyar_binResultTy_udiv (t : Ty) : binResultTy Bop.udiv t = t := rfl
theorem tyar_binResultTy_sdiv (t : Ty) : binResultTy Bop.sdiv t = t := rfl
theorem tyar_binResultTy_urem (t : Ty) : binResultTy Bop.urem t = t := rfl
theorem tyar_binResultTy_srem (t : Ty) : binResultTy Bop.srem t = t := rfl
theorem tyar_binResultTy_band (t : Ty) : binResultTy Bop.band t = t := rfl
theorem tyar_binResultTy_bor (t : Ty) : binResultTy Bop.bor t = t := rfl
theorem tyar_binResultTy_bxor (t : Ty) : binResultTy Bop.bxor t = t := rfl
theorem tyar_binResultTy_shl (t : Ty) : binResultTy Bop.shl t = t := rfl
theorem tyar_binResultTy_lshr (t : Ty) : binResultTy Bop.lshr t = t := rfl
theorem tyar_binResultTy_ashr (t : Ty) : binResultTy Bop.ashr t = t := rfl

-- Per-op representatives (UnOp): neg, bnot, ctpop.
theorem tyar_unResultTy_neg (t : Ty) : unResultTy Uop.neg t = t := rfl
theorem tyar_unResultTy_bnot (t : Ty) : unResultTy Uop.bnot t = t := rfl
theorem tyar_unResultTy_ctpop (t : Ty) : unResultTy Uop.ctpop t = t := rfl

-- Concrete-type witnesses (an i32 add yields i32; a u32 shl yields u32; an f32 mul
-- yields f32) — the typing rule on named, fully-applied instructions.
theorem tyar_binResultTy_add_i32 : binResultTy Bop.add Ty.ti32 = Ty.ti32 := rfl
theorem tyar_binResultTy_shl_u32 : binResultTy Bop.shl Ty.tu32 = Ty.tu32 := rfl
theorem tyar_binResultTy_mul_f32 : binResultTy Bop.mul Ty.tf32 = Ty.tf32 := rfl
theorem tyar_unResultTy_neg_i32 : unResultTy Uop.neg Ty.ti32 = Ty.ti32 := rfl

-- ===========================================================================
-- RESULT STAYS NUMERIC (BinOp). For all op and t: a numeric operand type yields a
-- numeric result type. Encoded over Bool as the implication
--   (not isNumeric t) || isNumeric (binResultTy op t) = true.
-- Since binResultTy op t = t, this is (not isNumeric t) || isNumeric t = true, a
-- Bool tautology. Proven over ALL 4 ctors of Ty by a casesOn (each minor rfl); the
-- op argument is irrelevant (binResultTy ignores it), so it stays universally bound.
-- ===========================================================================
theorem tyar_binResultTy_numeric_preserved (op : Bop) (t : Ty) :
    Bool.or (Bool.not (isNumeric t)) (isNumeric (binResultTy op t)) = true :=
  @Ty.casesOn (fun k => Bool.or (Bool.not (isNumeric k)) (isNumeric (binResultTy op k)) = true) t
    rfl rfl rfl rfl

-- RESULT STAYS NUMERIC (UnOp): same, for the unary result-typing rule.
theorem tyar_unResultTy_numeric_preserved (op : Uop) (t : Ty) :
    Bool.or (Bool.not (isNumeric t)) (isNumeric (unResultTy op t)) = true :=
  @Ty.casesOn (fun k => Bool.or (Bool.not (isNumeric k)) (isNumeric (unResultTy op k)) = true) t
    rfl rfl rfl rfl

-- ===========================================================================
-- INTEGER OPS PRESERVE INTEGERNESS (BinOp). For all op and t: an integer operand
-- type yields an integer result type. Encoded
--   (not isInteger t) || isInteger (binResultTy op t) = true.
-- Same casesOn-over-Ty structure.
-- ===========================================================================
theorem tyar_binResultTy_integer_preserved (op : Bop) (t : Ty) :
    Bool.or (Bool.not (isInteger t)) (isInteger (binResultTy op t)) = true :=
  @Ty.casesOn (fun k => Bool.or (Bool.not (isInteger k)) (isInteger (binResultTy op k)) = true) t
    rfl rfl rfl rfl

-- INTEGER PRESERVATION (UnOp): same for unary ops.
theorem tyar_unResultTy_integer_preserved (op : Uop) (t : Ty) :
    Bool.or (Bool.not (isInteger t)) (isInteger (unResultTy op t)) = true :=
  @Ty.casesOn (fun k => Bool.or (Bool.not (isInteger k)) (isInteger (unResultTy op k)) = true) t
    rfl rfl rfl rfl

-- ===========================================================================
-- FLOAT-NESS PRESERVED LIKEWISE (sharper structural fact): a float operand type
-- yields a float result type, over all op and all t.
-- ===========================================================================
theorem tyar_binResultTy_float_preserved (op : Bop) (t : Ty) :
    Bool.or (Bool.not (isFloat t)) (isFloat (binResultTy op t)) = true :=
  @Ty.casesOn (fun k => Bool.or (Bool.not (isFloat k)) (isFloat (binResultTy op k)) = true) t
    rfl rfl rfl rfl

-- ===========================================================================
-- CLASSIFIER COHERENCE under the typing rule: the result type's classifier is the
-- SAME Bool as the operand type's classifier, since the result type IS the operand
-- type. isNumeric (binResultTy op t) = isNumeric t, proven over all op and t by rfl
-- (binResultTy op t reduces to t definitionally, so both sides are identical).
-- ===========================================================================
theorem tyar_binResultTy_isNumeric_eq (op : Bop) (t : Ty) :
    isNumeric (binResultTy op t) = isNumeric t := rfl
theorem tyar_unResultTy_isInteger_eq (op : Uop) (t : Ty) :
    isInteger (unResultTy op t) = isInteger t := rfl

-- ===========================================================================
-- BinOp and UnOp result-typing AGREE: on a shared operand type, both rules return
-- the same type (both are the identity on the operand type). For all bop, uop, t:
-- binResultTy bop t = unResultTy uop t. By rfl (both reduce to t).
-- ===========================================================================
theorem tyar_bin_un_resultTy_agree (bop : Bop) (uop : Uop) (t : Ty) :
    binResultTy bop t = unResultTy uop t := rfl

end TypArith

-- ###########################################################################
-- ICmp/FCmp result = comparison_result_ty (always boolish, lanes preserved, predicate-independent)
-- ###########################################################################
namespace TypCompare

-- A compact Clean image of the trust-ir `Ty` slice the comparison-typing rule
-- needs: the realistic scalar operand types (ti32, tu32, tf32, tbool) plus the
-- recursive SIMD vector constructor `tvec : Ty -> Nat -> Ty` (element type inline
-- + lane count, mirroring `Vector(Box<Ty>, u32)`). Five ctors (>=2, a genuine sum
-- type). Constructor order is fixed; the casesOn minors below follow it:
--   ti32, tu32, tf32, tbool, tvec.
inductive Ty where
  | ti32 : Ty
  | tu32 : Ty
  | tf32 : Ty
  | tbool : Ty
  | tvec : Ty -> Nat -> Ty

-- The ICmp predicate inventory, faithful to trust-ir `ICmpOp` (inst.rs:75): the
-- 10 integer-comparison predicates (Eq, Ne, Ult, Ule, Ugt, Uge, Slt, Sle, Sgt,
-- Sge), in DECLARATION ORDER. These are NULLARY tags: the comparison RESULT TYPE
-- does not depend on the predicate (comparison_result_ty inspects only the operand
-- type), so the predicate carries no payload here.
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

-- The FCmp predicate inventory, faithful to trust-ir `FCmpOp` (inst.rs:90): the
-- 12 IEEE-754 ordered/unordered float-comparison predicates (OEq, ONe, OLt, OLe,
-- OGt, OGe, UEq, UNe, ULt, ULe, UGt, UGe), in DECLARATION ORDER. Also nullary
-- tags — the FCmp result type likewise depends only on the operand type.
inductive FCmpOp where
  | foeq : FCmpOp
  | fone : FCmpOp
  | folt : FCmpOp
  | fole : FCmpOp
  | fogt : FCmpOp
  | foge : FCmpOp
  | fueq : FCmpOp
  | fune : FCmpOp
  | fult : FCmpOp
  | fule : FCmpOp
  | fugt : FCmpOp
  | fuge : FCmpOp

-- ===========================================================================
-- comparison_result_ty (ty.rs:289): the result type of an elementwise comparison
-- over operand type T.
--   Vector(_, lanes) => Vector(Bool, lanes)   -- a bool vector, lane count preserved
--   _                => Bool                   -- a scalar bool
-- The four scalar minors map to tbool; the tvec minor (binding element + lanes)
-- produces tvec tbool n — preserving the lane count `n` and DISCARDING the element
-- type (the `_` in `Vector(_, lanes)`).
-- ===========================================================================
def compResultTy : Ty -> Ty := fun t =>
  @Ty.casesOn (fun _ => Ty) t
    Ty.tbool                       -- ti32  -> Bool
    Ty.tbool                       -- tu32  -> Bool
    Ty.tbool                       -- tf32  -> Bool
    Ty.tbool                       -- tbool -> Bool
    (fun _e n => Ty.tvec Ty.tbool n)  -- tvec e n -> <n x bool>

-- The ICmp instruction-typing function: the result type of an `ICmp op a b` over
-- operand type T. By the trust-ir rule the result is `comparison_result_ty(T)`,
-- INDEPENDENT of the predicate `op`. So icmpResultTy op t = compResultTy t.
def icmpResultTy : ICmpOp -> Ty -> Ty := fun _op t => compResultTy t

-- The FCmp instruction-typing function: identical shape — FCmp likewise yields
-- comparison_result_ty(T), independent of the float predicate.
def fcmpResultTy : FCmpOp -> Ty -> Ty := fun _op t => compResultTy t

-- ===========================================================================
-- The boolishness classifier. A type is "boolish" iff it is the scalar Bool OR a
-- bool-element vector (<N x bool>). isBoolVector is a tvec whose element is tbool
-- (a nested casesOn on the element); isBoolish = (t is tbool) || isBoolVector t.
-- This is the well-typedness predicate for comparison RESULT types.
-- ===========================================================================
def isScalarBool : Ty -> Bool := fun t =>
  @Ty.casesOn (fun _ => Bool) t
    false false false true
    (fun _e _n => false)

def isBoolVector : Ty -> Bool := fun t =>
  @Ty.casesOn (fun _ => Bool) t
    false false false false
    (fun e _n => @Ty.casesOn (fun _ => Bool) e false false false true (fun _a _b => false))

def isBoolish : Ty -> Bool := fun t => Bool.or (isScalarBool t) (isBoolVector t)

-- A lane-count extractor: for a vector returns Some lanes, for a scalar None.
-- Used to state the lane-preservation invariant as an equality of lane counts.
def laneCount : Ty -> Option Nat := fun t =>
  @Ty.casesOn (fun _ => Option Nat) t
    Option.none Option.none Option.none Option.none
    (fun _e n => Option.some n)

-- ===========================================================================
-- THEOREM 1 — the ICmp result type is INDEPENDENT OF THE PREDICATE: for every
-- predicate op and operand t, icmpResultTy op t = compResultTy t. (This is the
-- definitional shape of the rule; stated over all ICmpOp by an all-ctor casesOn,
-- each minor `rfl`.) Together with THEOREM 1f it shows the comparison result type
-- is a function of the operand type ALONE.
-- ===========================================================================
theorem tycmp_icmp_pred_independent (op : ICmpOp) (t : Ty) :
    icmpResultTy op t = compResultTy t :=
  @ICmpOp.casesOn (fun k => icmpResultTy k t = compResultTy t) op
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- THEOREM 1f — the FCmp result type is likewise independent of the float
-- predicate: for every FCmpOp op and operand t, fcmpResultTy op t = compResultTy t.
-- All-ctor casesOn over the 12 FCmpOp ctors (each minor `rfl`).
theorem tycmp_fcmp_pred_independent (op : FCmpOp) (t : Ty) :
    fcmpResultTy op t = compResultTy t :=
  @FCmpOp.casesOn (fun k => fcmpResultTy k t = compResultTy t) op
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- THEOREM 1ic — ICmp and FCmp agree on the result type for any shared operand:
-- icmpResultTy iop t = fcmpResultTy fop t. Both reduce to compResultTy t.
theorem tycmp_icmp_fcmp_agree (iop : ICmpOp) (fop : FCmpOp) (t : Ty) :
    icmpResultTy iop t = fcmpResultTy fop t := rfl

-- ===========================================================================
-- THEOREM 2 — SCALAR comparisons yield Bool: compResultTy is tbool on every scalar
-- operand type. One `rfl` per scalar (casesOn iota).
-- ===========================================================================
theorem tycmp_scalar_i32_is_bool : compResultTy Ty.ti32 = Ty.tbool := rfl
theorem tycmp_scalar_u32_is_bool : compResultTy Ty.tu32 = Ty.tbool := rfl
theorem tycmp_scalar_f32_is_bool : compResultTy Ty.tf32 = Ty.tbool := rfl
theorem tycmp_scalar_bool_is_bool : compResultTy Ty.tbool = Ty.tbool := rfl

-- The same, threaded through the instruction-typing functions (an actual ICmp/FCmp
-- over a scalar operand has a scalar Bool result type).
theorem tycmp_icmp_scalar_i32_is_bool (op : ICmpOp) :
    icmpResultTy op Ty.ti32 = Ty.tbool := rfl
theorem tycmp_fcmp_scalar_f32_is_bool (op : FCmpOp) :
    fcmpResultTy op Ty.tf32 = Ty.tbool := rfl

-- ===========================================================================
-- THEOREM 3 — VECTOR comparisons yield bool-vectors preserving lanes: for every
-- element type e and lane count n, compResultTy (tvec e n) = tvec tbool n. The
-- ELEMENT type is discarded (the `_` in `Vector(_, lanes)`); the LANE COUNT is
-- preserved. Stated symbolically (any e, any n) — one casesOn-iota `rfl`.
-- ===========================================================================
theorem tycmp_vector_result_is_bool_vector (e : Ty) (n : Nat) :
    compResultTy (Ty.tvec e n) = Ty.tvec Ty.tbool n := rfl

-- Element-independence of the vector result: two vectors with DIFFERENT element
-- types but the same lane count have the SAME comparison result type.
theorem tycmp_vector_result_element_independent (e1 e2 : Ty) (n : Nat) :
    compResultTy (Ty.tvec e1 n) = compResultTy (Ty.tvec e2 n) := rfl

-- Concrete <4 x i32>: an integer comparison over a 4-lane i32 vector yields
-- <4 x bool>, for any predicate (threaded through icmpResultTy).
theorem tycmp_icmp_v4i32_is_v4bool (op : ICmpOp) :
    icmpResultTy op (Ty.tvec Ty.ti32 4) = Ty.tvec Ty.tbool 4 := rfl

-- ===========================================================================
-- THEOREM 4 — the comparison result is ALWAYS BOOLISH: for every operand type t,
-- isBoolish (compResultTy t) = true. This is the WELL-TYPEDNESS invariant of the
-- comparison-typing rule (a comparison always produces a Bool or a bool-vector).
-- Proven by an all-ctor @Ty.casesOn: the four scalar minors give isBoolish tbool;
-- the tvec minor (binding element + lanes) gives isBoolish (tvec tbool n) — both
-- reduce to `true`, so every minor is `rfl`.
-- ===========================================================================
theorem tycmp_result_always_boolish (t : Ty) :
    isBoolish (compResultTy t) = true :=
  @Ty.casesOn (fun k => isBoolish (compResultTy k) = true) t
    rfl rfl rfl rfl
    (fun _e _n => rfl)

-- The instruction-typed forms of the well-typedness invariant: an ICmp/FCmp result
-- is always boolish, for any predicate and any operand. All-ctor casesOn over Ty,
-- with the predicate fixed-but-arbitrary (the result ignores it).
theorem tycmp_icmp_result_always_boolish (op : ICmpOp) (t : Ty) :
    isBoolish (icmpResultTy op t) = true :=
  @Ty.casesOn (fun k => isBoolish (icmpResultTy op k) = true) t
    rfl rfl rfl rfl
    (fun _e _n => rfl)

theorem tycmp_fcmp_result_always_boolish (op : FCmpOp) (t : Ty) :
    isBoolish (fcmpResultTy op t) = true :=
  @Ty.casesOn (fun k => isBoolish (fcmpResultTy op k) = true) t
    rfl rfl rfl rfl
    (fun _e _n => rfl)

-- ===========================================================================
-- THEOREM 5 — LANE COUNT IS PRESERVED: for every element type e and lane count n,
-- the comparison result vector has the SAME lane count `n` as the operand vector.
-- Stated as an equality of the extracted lane counts:
--   laneCount (compResultTy (tvec e n)) = laneCount (tvec e n)  (= Some n).
-- compResultTy (tvec e n) reduces to tvec tbool n, whose laneCount is Some n,
-- which equals the operand's laneCount Some n. One casesOn-iota `rfl`.
-- ===========================================================================
theorem tycmp_lane_count_preserved (e : Ty) (n : Nat) :
    laneCount (compResultTy (Ty.tvec e n)) = laneCount (Ty.tvec e n) := rfl

-- The explicit lane-count values (operand and result both Some n).
theorem tycmp_lane_count_result_is_some (e : Ty) (n : Nat) :
    laneCount (compResultTy (Ty.tvec e n)) = Option.some n := rfl

-- Scalars have no lane count, and neither does their (scalar Bool) result.
theorem tycmp_scalar_no_lane_count :
    laneCount (compResultTy Ty.ti32) = Option.none := rfl

-- ===========================================================================
-- THEOREM 6 — boolishness DISCRIMINATES: a non-boolean scalar operand type is NOT
-- itself boolish (so the comparison genuinely CHANGES the type from e.g. i32 to
-- bool). These anchor that isBoolish is not trivially true.
-- ===========================================================================
theorem tycmp_i32_not_boolish : isBoolish Ty.ti32 = false := rfl
theorem tycmp_f32_not_boolish : isBoolish Ty.tf32 = false := rfl
theorem tycmp_i32vec_not_boolish (n : Nat) : isBoolish (Ty.tvec Ty.ti32 n) = false := rfl
-- ...and tbool / bool-vectors ARE boolish (the result shapes).
theorem tycmp_bool_is_boolish : isBoolish Ty.tbool = true := rfl
theorem tycmp_boolvec_is_boolish (n : Nat) : isBoolish (Ty.tvec Ty.tbool n) = true := rfl

end TypCompare

-- ###########################################################################
-- Cast result = TARGET type; result kind = target kind across cast families
-- ###########################################################################
namespace TypCast

-- A compact Clean image of the trust-ir `Ty` constructors that participate in
-- casts (ty.rs scalar/pointer frontier). Six nullary tags (>=2, a real sum type,
-- not a structure). Constructor order is fixed; the casesOn minors below follow
-- it: ti32, tu32, tf32, tf64, tptr, tbool.
--   ti32  = Ty::I32   (signed integer)
--   tu32  = Ty::U32   (unsigned integer)
--   tf32  = Ty::F32   (float)
--   tf64  = Ty::F64   (float)
--   tptr  = Ty::Ptr   (opaque pointer)
--   tbool = Ty::Bool
inductive Ty where
  | ti32 : Ty
  | tu32 : Ty
  | tf32 : Ty
  | tf64 : Ty
  | tptr : Ty
  | tbool : Ty

-- The 15 trust-ir `CastOp`s (inst.rs CastOp enum), as NULLARY tags in DECLARATION
-- ORDER. They name HOW a value is reinterpreted/converted, but per trust-ir's
-- result-typing rule they do NOT affect the result type (= the target `to_ty`):
--   trunc      : integer truncation        (iN -> iM, M < N)
--   zext       : zero-extend               (unsigned widen)
--   sext       : sign-extend               (signed widen)
--   fptrunc    : float truncation          (f64 -> f32)
--   fpext      : float extension           (f32 -> f64)
--   fptoui     : float -> unsigned int
--   fptosi     : float -> signed int
--   uitofp     : unsigned int -> float
--   sitofp     : signed int -> float
--   ptrtoint   : pointer -> integer
--   inttoptr   : integer -> pointer
--   ptrtoptr   : pointer -> pointer
--   bitcast    : bit-preserving reinterpret (same width)
--   transmute  : raw reinterpret
--   reifyfnptr : function item -> fn pointer
inductive Cop where
  | trunc : Cop
  | zext : Cop
  | sext : Cop
  | fptrunc : Cop
  | fpext : Cop
  | fptoui : Cop
  | fptosi : Cop
  | uitofp : Cop
  | sitofp : Cop
  | ptrtoint : Cop
  | inttoptr : Cop
  | ptrtoptr : Cop
  | bitcast : Cop
  | transmute : Cop
  | reifyfnptr : Cop

-- ===========================================================================
-- THE HEADLINE RULE. trust-ir `Inst::Cast { op, from_ty, to_ty, operand }`
-- produces a result of type `to_ty`: castResultTy op from to = to. The op and the
-- source type are consumed (the legality of the conversion depends on them) but
-- the RESULT type is always the target. All 15 CastOps share this rule.
-- ===========================================================================
def castResultTy : Cop -> Ty -> Ty -> Ty := fun _op _src to => to

-- ===========================================================================
-- FAMILY CLASSIFIERS on `Ty` (ty.rs is_integer / is_float / pointer frontier).
-- isIntTy: the integer scalars I32/U32. isFloatTy: the floats F32/F64.
-- isPtrTy: the opaque pointer. (tbool is none of these here.) Each is a 6-minor
-- @Ty.casesOn over bare Bool literals, DECLARATION ORDER:
--   ti32 tu32 tf32 tf64 tptr tbool
-- ===========================================================================
def isIntTy : Ty -> Bool := fun t =>
  @Ty.casesOn (fun _ => Bool) t
    true true false false false false

def isFloatTy : Ty -> Bool := fun t =>
  @Ty.casesOn (fun _ => Bool) t
    false false true true false false

def isPtrTy : Ty -> Bool := fun t =>
  @Ty.casesOn (fun _ => Bool) t
    false false false false true false

-- ===========================================================================
-- HEADLINE RULE, the universal form: forall op from to, castResultTy op from to =
-- to. The RESULT of a Cast is its TARGET type, for every op / source / target.
-- castResultTy is definitionally `fun _op _from to => to`, so the body reduces by
-- beta to `to` for ANY arguments — proven by `rfl` under the binders.
-- ===========================================================================
theorem tycast_result_is_target (op : Cop) (src : Ty) (to : Ty) :
    castResultTy op src to = to := rfl

-- ===========================================================================
-- REPRESENTATIVE WITNESSES (the prompt's named cases): each cast op, on a
-- concrete (from, to), yields exactly the target. By beta + casesOn iota = rfl.
-- ===========================================================================
-- integer-producing widen (zext: unsigned widen, here ti32 -> tu32 as the target)
theorem tycast_zext_i32_to_u32 : castResultTy Cop.zext Ty.ti32 Ty.tu32 = Ty.tu32 := rfl
-- signed-int -> float (sitofp): result is the float target
theorem tycast_sitofp_i32_to_f32 : castResultTy Cop.sitofp Ty.ti32 Ty.tf32 = Ty.tf32 := rfl
-- unsigned-int -> float (uitofp): result is the float target
theorem tycast_uitofp_u32_to_f64 : castResultTy Cop.uitofp Ty.tu32 Ty.tf64 = Ty.tf64 := rfl
-- int -> pointer (inttoptr): result is the pointer target
theorem tycast_inttoptr_i32_to_ptr : castResultTy Cop.inttoptr Ty.ti32 Ty.tptr = Ty.tptr := rfl
-- bit-preserving reinterpret f32 -> i32 (bitcast): result is the integer target
theorem tycast_bitcast_f32_to_i32 : castResultTy Cop.bitcast Ty.tf32 Ty.ti32 = Ty.ti32 := rfl
-- float -> signed int (fptosi): result is the integer target
theorem tycast_fptosi_f32_to_i32 : castResultTy Cop.fptosi Ty.tf32 Ty.ti32 = Ty.ti32 := rfl
-- pointer -> integer (ptrtoint): result is the integer target
theorem tycast_ptrtoint_ptr_to_i32 : castResultTy Cop.ptrtoint Ty.tptr Ty.ti32 = Ty.ti32 := rfl
-- pointer -> pointer (ptrtoptr): result is the pointer target
theorem tycast_ptrtoptr_ptr_to_ptr : castResultTy Cop.ptrtoptr Ty.tptr Ty.tptr = Ty.tptr := rfl
-- float truncation (fptrunc): f64 -> f32, result is the float target
theorem tycast_fptrunc_f64_to_f32 : castResultTy Cop.fptrunc Ty.tf64 Ty.tf32 = Ty.tf32 := rfl
-- float extension (fpext): f32 -> f64, result is the float target
theorem tycast_fpext_f32_to_f64 : castResultTy Cop.fpext Ty.tf32 Ty.tf64 = Ty.tf64 := rfl
-- integer truncation (trunc): result is the (narrower) integer target
theorem tycast_trunc_i32_to_u32 : castResultTy Cop.trunc Ty.ti32 Ty.tu32 = Ty.tu32 := rfl
-- sign-extend (sext): result is the integer target
theorem tycast_sext_i32_to_i32 : castResultTy Cop.sext Ty.ti32 Ty.ti32 = Ty.ti32 := rfl
-- raw reinterpret (transmute): result is the declared target (here ptr)
theorem tycast_transmute_i32_to_ptr : castResultTy Cop.transmute Ty.ti32 Ty.tptr = Ty.tptr := rfl
-- function-item -> fn pointer (reifyfnptr): result is the pointer target
theorem tycast_reifyfnptr_i32_to_ptr : castResultTy Cop.reifyfnptr Ty.ti32 Ty.tptr = Ty.tptr := rfl
-- float -> unsigned int (fptoui): result is the integer target
theorem tycast_fptoui_f32_to_u32 : castResultTy Cop.fptoui Ty.tf32 Ty.tu32 = Ty.tu32 := rfl

-- ===========================================================================
-- RESULT-KIND = TARGET-KIND metatheorems. The classifier of the RESULT type
-- equals the classifier of the TARGET type — because the result IS the target.
-- Stated UNIVERSALLY (forall op from to) so it covers every cast, every source,
-- every target. castResultTy reduces to `to` by beta, so each is `rfl`.
-- ===========================================================================
-- The result is a float iff the target is a float.
theorem tycast_resultkind_float (op : Cop) (src : Ty) (to : Ty) :
    isFloatTy (castResultTy op src to) = isFloatTy to := rfl
-- The result is an integer iff the target is an integer.
theorem tycast_resultkind_int (op : Cop) (src : Ty) (to : Ty) :
    isIntTy (castResultTy op src to) = isIntTy to := rfl
-- The result is a pointer iff the target is a pointer.
theorem tycast_resultkind_ptr (op : Cop) (src : Ty) (to : Ty) :
    isPtrTy (castResultTy op src to) = isPtrTy to := rfl

-- ===========================================================================
-- PER-FAMILY WITNESSES that the result CARRIES the documented target kind.
-- These instantiate the universal kind theorems on representative casts: an
-- fp-producing cast yields a FLOAT result; an int-producing cast yields an INTEGER
-- result; a ptr-producing cast yields a POINTER result. By beta + casesOn iota.
-- ===========================================================================
-- fp-producing (sitofp -> f32): the result is a float.
theorem tycast_sitofp_result_is_float :
    isFloatTy (castResultTy Cop.sitofp Ty.ti32 Ty.tf32) = true := rfl
-- fp-producing (uitofp -> f64): the result is a float.
theorem tycast_uitofp_result_is_float :
    isFloatTy (castResultTy Cop.uitofp Ty.tu32 Ty.tf64) = true := rfl
-- int-producing (fptosi -> i32): the result is an integer.
theorem tycast_fptosi_result_is_int :
    isIntTy (castResultTy Cop.fptosi Ty.tf32 Ty.ti32) = true := rfl
-- ptr-producing (inttoptr -> ptr): the result is a pointer.
theorem tycast_inttoptr_result_is_ptr :
    isPtrTy (castResultTy Cop.inttoptr Ty.ti32 Ty.tptr) = true := rfl
-- bitcast f32 -> i32: the result is an integer (NOT a float — kind follows target).
theorem tycast_bitcast_result_is_int :
    isIntTy (castResultTy Cop.bitcast Ty.tf32 Ty.ti32) = true := rfl
-- ...and the bitcast result is NOT a float (it took the integer target's kind).
theorem tycast_bitcast_result_not_float :
    isFloatTy (castResultTy Cop.bitcast Ty.tf32 Ty.ti32) = false := rfl

-- ===========================================================================
-- COHERENCE: the result type is INDEPENDENT of the cast op and the source type.
-- For all ops o1 o2 and sources f1 f2, casting to the same target gives the same
-- result type. This is the structural content "result = to_ty only" — proven by
-- beta-reduction (both sides reduce to `to`), `rfl`.
-- ===========================================================================
theorem tycast_result_indep_of_op_and_source
    (o1 : Cop) (o2 : Cop) (f1 : Ty) (f2 : Ty) (to : Ty) :
    castResultTy o1 f1 to = castResultTy o2 f2 to := rfl

-- The family classifiers are pairwise-disjoint on the target (so "result kind =
-- target kind" is a genuine partition, not vacuous): no Ty is both int and float.
theorem tycast_int_float_disjoint (t : Ty) :
    Bool.and (isIntTy t) (isFloatTy t) = false :=
  @Ty.casesOn (fun k => Bool.and (isIntTy k) (isFloatTy k) = false) t
    rfl rfl rfl rfl rfl rfl

-- No Ty is both a pointer and a float (target-kind families are disjoint).
theorem tycast_ptr_float_disjoint (t : Ty) :
    Bool.and (isPtrTy t) (isFloatTy t) = false :=
  @Ty.casesOn (fun k => Bool.and (isPtrTy k) (isFloatTy k) = false) t
    rfl rfl rfl rfl rfl rfl

end TypCast

-- ###########################################################################
-- Overflow result = (value, flag) pair; Select preserves value type, condition = select_condition_ty
-- ###########################################################################
namespace TypOvfSel

-- A COMPACT Clean image of trust-ir's `Ty` carrying just the constructors this
-- typing-discipline slice needs: the scalar anchors (ti32, tu32, tbool), the
-- recursive SIMD vector `tvec : Ty -> Nat -> Ty` (element type inline + lane
-- count, mirroring `Vector(Box<Ty>, u32)`), and the binary tuple `ttuple : Ty ->
-- Ty -> Ty` (recursive, mirroring `Tuple(Vec<Ty>)` for the 2-element checked-
-- arithmetic result pair). Constructor order is fixed; the casesOn minors below
-- follow it: ti32, tu32, tbool, tvec, ttuple. (>=2 ctors, so a genuine inductive.)
inductive Ty where
  | ti32 : Ty
  | tu32 : Ty
  | tbool : Ty
  | tvec : Ty -> Nat -> Ty
  | ttuple : Ty -> Ty -> Ty

-- The three checked-arithmetic overflow ops, faithful to trust-ir `OverflowOp`
-- (inst.rs:67): AddOverflow / SubOverflow / MulOverflow. Modeled as nullary tags
-- (the result-typing rule does not inspect WHICH op — all three produce the same
-- (value, flag) pair shape). >=2 ctors.
inductive OvOp where
  | oadd : OvOp
  | osub : OvOp
  | omul : OvOp

-- ===========================================================================
-- `Inst::Overflow { op, ty, .. }` RESULT TYPE (inst.rs:434 + CLAUDE.md
-- "Checked arithmetic returning (result, overflowed)"): a 2-tuple whose first
-- component is the OPERAND type `ty` and whose second component is `Bool` (the
-- overflow flag). The op is IGNORED — every overflow op yields the same shape.
-- ===========================================================================
def ovResultTy : OvOp -> Ty -> Ty := fun _op t => Ty.ttuple t Ty.tbool

-- ===========================================================================
-- `Inst::Select { cond, ty, .. }` RESULT TYPE (inst.rs:655): a select PRESERVES
-- the selected value type `ty`. The result type is exactly `ty`.
-- ===========================================================================
def selResultTy : Ty -> Ty := fun t => t

-- ===========================================================================
-- `Ty::select_condition_ty` (ty.rs:300): the REQUIRED condition type for a select
-- producing value type `t` — a scalar `bool` for a scalar `t`, and a logical lane
-- mask `<N x bool>` (= tvec tbool lanes) for a vector `t`, regardless of the
-- selected element type, lane count preserved. The recursive tvec minor binds the
-- element sub-value (unused — the mask element is always tbool) and the lane Nat;
-- the ttuple minor binds both sub-values (a tuple is a scalar-shaped select value).
-- ===========================================================================
def selCondTy : Ty -> Ty := fun t =>
  @Ty.casesOn (fun _ => Ty) t
    Ty.tbool                                  -- ti32   -> bool
    Ty.tbool                                  -- tu32   -> bool
    Ty.tbool                                  -- tbool  -> bool
    (fun _e n => Ty.tvec Ty.tbool n)          -- tvec e n -> <n x bool>
    (fun _a _b => Ty.tbool)                   -- ttuple a b -> bool

-- ===========================================================================
-- OVERFLOW RESULT IS THE (value, flag) PAIR — for EVERY op and EVERY operand type
-- the result is `ttuple t tbool` (the checked-arithmetic pair). Proven uniformly
-- over all 3 ops AND all 5 ty ctors by a nested all-ctor @casesOn (each minor rfl,
-- since ovResultTy ignores the op and is definitionally `ttuple t tbool`).
-- ===========================================================================
theorem tyovf_ovResultTy_is_pair (op : OvOp) (t : Ty) :
    ovResultTy op t = Ty.ttuple t Ty.tbool :=
  @OvOp.casesOn (fun o => ovResultTy o t = Ty.ttuple t Ty.tbool) op
    rfl rfl rfl

-- ===========================================================================
-- The FIRST component of the Overflow result is the OPERAND type, the SECOND is
-- Bool — read off per representative (op, ty). Each is a casesOn iota = rfl.
-- ===========================================================================
theorem tyovf_ovResultTy_oadd_ti32 : ovResultTy OvOp.oadd Ty.ti32 = Ty.ttuple Ty.ti32 Ty.tbool := rfl
theorem tyovf_ovResultTy_osub_ti32 : ovResultTy OvOp.osub Ty.ti32 = Ty.ttuple Ty.ti32 Ty.tbool := rfl
theorem tyovf_ovResultTy_omul_ti32 : ovResultTy OvOp.omul Ty.ti32 = Ty.ttuple Ty.ti32 Ty.tbool := rfl
theorem tyovf_ovResultTy_oadd_tu32 : ovResultTy OvOp.oadd Ty.tu32 = Ty.ttuple Ty.tu32 Ty.tbool := rfl
theorem tyovf_ovResultTy_omul_tu32 : ovResultTy OvOp.omul Ty.tu32 = Ty.ttuple Ty.tu32 Ty.tbool := rfl
-- The op is IRRELEVANT to the result shape: all three ops agree at a fixed operand.
theorem tyovf_ovResultTy_op_irrelevant_add_eq_mul (t : Ty) :
    ovResultTy OvOp.oadd t = ovResultTy OvOp.omul t := rfl
theorem tyovf_ovResultTy_op_irrelevant_add_eq_sub (t : Ty) :
    ovResultTy OvOp.oadd t = ovResultTy OvOp.osub t := rfl

-- ===========================================================================
-- SELECT PRESERVES the value type: for all t, selResultTy t = t. Proven uniformly
-- over all 5 ctors (each minor rfl; selResultTy is the identity by definition).
-- ===========================================================================
theorem tyovf_selResultTy_id (t : Ty) : selResultTy t = t :=
  @Ty.casesOn (fun k => selResultTy k = k) t
    rfl rfl rfl
    (fun _e _n => rfl)
    (fun _a _b => rfl)

-- Per-representative selResultTy = identity (casesOn iota = rfl).
theorem tyovf_selResultTy_ti32 : selResultTy Ty.ti32 = Ty.ti32 := rfl
theorem tyovf_selResultTy_tu32 : selResultTy Ty.tu32 = Ty.tu32 := rfl
theorem tyovf_selResultTy_tvec (e : Ty) (n : Nat) :
    selResultTy (Ty.tvec e n) = Ty.tvec e n := rfl

-- ===========================================================================
-- SELECT CONDITION IS BOOLISH (ty.rs:300): scalar `ty` -> scalar `tbool`; vector
-- `ty` -> `<N x bool>` (tvec tbool lanes), lane count PRESERVED, independent of the
-- element type. Per representative (casesOn iota = rfl) + a symbolic vector lemma.
-- ===========================================================================
theorem tyovf_selCondTy_ti32 : selCondTy Ty.ti32 = Ty.tbool := rfl
theorem tyovf_selCondTy_tu32 : selCondTy Ty.tu32 = Ty.tbool := rfl
theorem tyovf_selCondTy_tbool : selCondTy Ty.tbool = Ty.tbool := rfl
-- Vector select condition is the lane mask <n x bool>, ANY element type, ANY lanes.
theorem tyovf_selCondTy_tvec (e : Ty) (n : Nat) :
    selCondTy (Ty.tvec e n) = Ty.tvec Ty.tbool n := rfl
-- Concrete <4 x i32> select condition is <4 x bool> (the lane count is preserved).
theorem tyovf_selCondTy_v4i32 :
    selCondTy (Ty.tvec Ty.ti32 4) = Ty.tvec Ty.tbool 4 := rfl
-- The element type does NOT affect the mask: <n x i32> and <n x u32> get the same
-- condition type for every lane count n (the mask element is always tbool).
theorem tyovf_selCondTy_elem_irrelevant (n : Nat) :
    selCondTy (Ty.tvec Ty.ti32 n) = selCondTy (Ty.tvec Ty.tu32 n) := rfl

-- ===========================================================================
-- COHERENCE: the Overflow FLAG component is exactly `tbool`. We state the result
-- as the (value, flag) pair and read off the second component via a tuple
-- projector `sndTy` (defined on ttuple), confirming the overflow flag is Bool for
-- EVERY op and operand type.
-- ===========================================================================

-- Second-component projector for a tuple type (defaults to ti32 on non-tuples —
-- irrelevant, only the ttuple case is exercised by the coherence theorems).
def sndTy : Ty -> Ty := fun t =>
  @Ty.casesOn (fun _ => Ty) t
    Ty.ti32                                   -- ti32
    Ty.ti32                                   -- tu32
    Ty.ti32                                   -- tbool
    (fun _e _n => Ty.ti32)                    -- tvec
    (fun _a b => b)                           -- ttuple a b -> b (the flag slot)

-- First-component projector (the value slot of the checked-arith pair).
def fstTy : Ty -> Ty := fun t =>
  @Ty.casesOn (fun _ => Ty) t
    Ty.ti32                                   -- ti32
    Ty.ti32                                   -- tu32
    Ty.ti32                                   -- tbool
    (fun _e _n => Ty.ti32)                    -- tvec
    (fun a _b => a)                           -- ttuple a b -> a (the value slot)

-- The flag component of an Overflow result is tbool, for every op and operand
-- type (uniform over all 3 ops and all 5 ty ctors).
theorem tyovf_ovResult_flag_is_bool (op : OvOp) (t : Ty) :
    sndTy (ovResultTy op t) = Ty.tbool :=
  @OvOp.casesOn (fun o => sndTy (ovResultTy o t) = Ty.tbool) op
    rfl rfl rfl

-- The value component of an Overflow result is exactly the operand type, for
-- every op and operand type.
theorem tyovf_ovResult_value_is_operand (op : OvOp) (t : Ty) :
    fstTy (ovResultTy op t) = t :=
  @OvOp.casesOn (fun o => fstTy (ovResultTy o t) = t) op
    rfl rfl rfl

-- Read-off at a representative: add-overflow on i32 has flag tbool and value ti32.
theorem tyovf_ovResult_flag_is_bool_oadd_ti32 :
    sndTy (ovResultTy OvOp.oadd Ty.ti32) = Ty.tbool := rfl
theorem tyovf_ovResult_value_is_operand_oadd_ti32 :
    fstTy (ovResultTy OvOp.oadd Ty.ti32) = Ty.ti32 := rfl

-- ===========================================================================
-- CROSS-INSTRUCTION coherence: a select's RESULT type and its required CONDITION
-- type agree exactly when the value type is already a scalar bool — and for a
-- vector value they are both `<n x bool>`-shaped only in the bool-element case.
-- General fact: for a vector value type, selResultTy keeps the element type while
-- selCondTy forces the element to tbool — they coincide iff the element is bool.
-- We state the bool-vector coincidence (selResultTy = selCondTy on <n x bool>).
-- ===========================================================================
theorem tyovf_select_result_cond_coincide_boolvec (n : Nat) :
    selResultTy (Ty.tvec Ty.tbool n) = selCondTy (Ty.tvec Ty.tbool n) := rfl
-- ...and the scalar-bool coincidence (a bool select's result and condition are both bool).
theorem tyovf_select_result_cond_coincide_bool :
    selResultTy Ty.tbool = selCondTy Ty.tbool := rfl

end TypOvfSel
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

/// Every trust-ir instruction-typing theorem across the four slices, in order.
const TYPEDINST_THEOREMS: &[&str] = &[
    // --- TypArith (30) ---
    "tyar_binResultTy_preserves",
    "tyar_unResultTy_preserves",
    "tyar_binResultTy_add",
    "tyar_binResultTy_sub",
    "tyar_binResultTy_mul",
    "tyar_binResultTy_udiv",
    "tyar_binResultTy_sdiv",
    "tyar_binResultTy_urem",
    "tyar_binResultTy_srem",
    "tyar_binResultTy_band",
    "tyar_binResultTy_bor",
    "tyar_binResultTy_bxor",
    "tyar_binResultTy_shl",
    "tyar_binResultTy_lshr",
    "tyar_binResultTy_ashr",
    "tyar_unResultTy_neg",
    "tyar_unResultTy_bnot",
    "tyar_unResultTy_ctpop",
    "tyar_binResultTy_add_i32",
    "tyar_binResultTy_shl_u32",
    "tyar_binResultTy_mul_f32",
    "tyar_unResultTy_neg_i32",
    "tyar_binResultTy_numeric_preserved",
    "tyar_unResultTy_numeric_preserved",
    "tyar_binResultTy_integer_preserved",
    "tyar_unResultTy_integer_preserved",
    "tyar_binResultTy_float_preserved",
    "tyar_binResultTy_isNumeric_eq",
    "tyar_unResultTy_isInteger_eq",
    "tyar_bin_un_resultTy_agree",
    // --- TypCompare (23) ---
    "tycmp_icmp_pred_independent",
    "tycmp_fcmp_pred_independent",
    "tycmp_icmp_fcmp_agree",
    "tycmp_scalar_i32_is_bool",
    "tycmp_scalar_u32_is_bool",
    "tycmp_scalar_f32_is_bool",
    "tycmp_scalar_bool_is_bool",
    "tycmp_icmp_scalar_i32_is_bool",
    "tycmp_fcmp_scalar_f32_is_bool",
    "tycmp_vector_result_is_bool_vector",
    "tycmp_vector_result_element_independent",
    "tycmp_icmp_v4i32_is_v4bool",
    "tycmp_result_always_boolish",
    "tycmp_icmp_result_always_boolish",
    "tycmp_fcmp_result_always_boolish",
    "tycmp_lane_count_preserved",
    "tycmp_lane_count_result_is_some",
    "tycmp_scalar_no_lane_count",
    "tycmp_i32_not_boolish",
    "tycmp_f32_not_boolish",
    "tycmp_i32vec_not_boolish",
    "tycmp_bool_is_boolish",
    "tycmp_boolvec_is_boolish",
    // --- TypCast (28) ---
    "tycast_result_is_target",
    "tycast_zext_i32_to_u32",
    "tycast_sitofp_i32_to_f32",
    "tycast_uitofp_u32_to_f64",
    "tycast_inttoptr_i32_to_ptr",
    "tycast_bitcast_f32_to_i32",
    "tycast_fptosi_f32_to_i32",
    "tycast_ptrtoint_ptr_to_i32",
    "tycast_ptrtoptr_ptr_to_ptr",
    "tycast_fptrunc_f64_to_f32",
    "tycast_fpext_f32_to_f64",
    "tycast_trunc_i32_to_u32",
    "tycast_sext_i32_to_i32",
    "tycast_transmute_i32_to_ptr",
    "tycast_reifyfnptr_i32_to_ptr",
    "tycast_fptoui_f32_to_u32",
    "tycast_resultkind_float",
    "tycast_resultkind_int",
    "tycast_resultkind_ptr",
    "tycast_sitofp_result_is_float",
    "tycast_uitofp_result_is_float",
    "tycast_fptosi_result_is_int",
    "tycast_inttoptr_result_is_ptr",
    "tycast_bitcast_result_is_int",
    "tycast_bitcast_result_not_float",
    "tycast_result_indep_of_op_and_source",
    "tycast_int_float_disjoint",
    "tycast_ptr_float_disjoint",
    // --- TypOvfSel (24) ---
    "tyovf_ovResultTy_is_pair",
    "tyovf_ovResultTy_oadd_ti32",
    "tyovf_ovResultTy_osub_ti32",
    "tyovf_ovResultTy_omul_ti32",
    "tyovf_ovResultTy_oadd_tu32",
    "tyovf_ovResultTy_omul_tu32",
    "tyovf_ovResultTy_op_irrelevant_add_eq_mul",
    "tyovf_ovResultTy_op_irrelevant_add_eq_sub",
    "tyovf_selResultTy_id",
    "tyovf_selResultTy_ti32",
    "tyovf_selResultTy_tu32",
    "tyovf_selResultTy_tvec",
    "tyovf_selCondTy_ti32",
    "tyovf_selCondTy_tu32",
    "tyovf_selCondTy_tbool",
    "tyovf_selCondTy_tvec",
    "tyovf_selCondTy_v4i32",
    "tyovf_selCondTy_elem_irrelevant",
    "tyovf_ovResult_flag_is_bool",
    "tyovf_ovResult_value_is_operand",
    "tyovf_ovResult_flag_is_bool_oadd_ti32",
    "tyovf_ovResult_value_is_operand_oadd_ti32",
    "tyovf_select_result_cond_coincide_boolvec",
    "tyovf_select_result_cond_coincide_bool",
];

#[test]
fn typed_instructions_elaborate_and_kernel_check() {
    elaborate_module(TYPEDINST_SOURCE).expect(
        "trust-ir's instruction result-typing rules (BinOp/UnOp preserve type, ICmp/FCmp -> \
         comparison_result_ty, Cast -> target, Overflow -> pair, Select) must elaborate and kernel-check",
    );
}

#[test]
fn typed_instruction_rules_are_proven_down_to_the_foundational_axioms() {
    let env = elaborate_module(TYPEDINST_SOURCE)
        .expect("the typed-instruction module must elaborate before auditing its theorems");
    for thm in TYPEDINST_THEOREMS {
        assert_proven_to_foundations(&env, thm);
    }
    println!(
        "TRUST INSTRUCTIONS ARE WELL-TYPED: {} instruction result-typing theorems (Ty <-> Inst \
         coherence) proven to the 3 foundational axioms.",
        TYPEDINST_THEOREMS.len()
    );
}
