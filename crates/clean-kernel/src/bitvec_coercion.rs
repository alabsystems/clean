// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Option-B step 1 (B1): a Formula-MIRRORING kernel datatype for the gate's
//! add-leaf op shape, with a `List Bool` evaluator and the PARAMETRIC
//! COERCION-IDENTITY lemmas — as raw kernel `Expr`s, reachable from `clean-auto`
//! (clean-kernel only; no parser/elab/.lean).
//!
//! # Why (the gate's REAL obligation, per ledger #35)
//!
//! The gate's `add@N` obligation is `machine_out == auto` where
//! `auto = BvAdd(W0,W1,N)` and
//! `machine_out = Extract[N-1:0]( ZeroExt_N( BvAdd(W0,W1,N) ) )` (plus
//! `BvOr(Const 0, ·)` identity wrappers). BOTH sides contain the SAME `BvAdd`
//! subterm; the residual is purely that the WIDTH-COERCION WRAPPERS are identity.
//! So the gate obligation is discharged WITHOUT any theorem about addition — by
//! the coercion identities instantiated at `z := the shared BvAdd`:
//!
//! ```text
//!   extractLow (len z) (zeroExt z k) = z          -- Extract∘ZeroExt = id
//!   zipOr (allFalseLike z) z         = z          -- Or(Const 0, ·) = id
//! ```
//!
//! These hold for ANY `z : List Bool` and pad `k`, proved by `List.rec` induction
//! on `z` (the #34 `bitvec_inductive` skeleton). This module:
//!   (1) defines the `List Bool` coercion ops (append / takeLen / zipOr /
//!       allFalseLike) as real reducible recursive Definitions;
//!   (2) proves the two parametric identities (`extract_zeroext_id`, `or_zero_id`);
//!   (3) defines a Formula-mirroring datatype `BvF`
//!       (Leaf/Const/Add/ZeroExt/ExtractLow/Or) with an evaluator `bvfEval` into
//!       `List Bool` (the embedding B2 will tie to the gate's `Formula`); and
//!       (4) lifts the identities to `bvfEval` (`bvf_extract_zeroext_id`,
//!       `bvf_or_zero_id`).
//!
//! # Non-vacuity guard (NOT softened)
//!
//! ZeroExt/Extract/Or/Const are REAL `List Bool` operations (zeroext APPENDS `k`
//! falses; takeLen takes the low bits; zipOr is pointwise; allFalse is all-false),
//! separately defined to match the Formula semantics — NOT stubs. The identities
//! hold by the ops' computation. The tests assert: empty domain-axiom closure; a
//! positive instantiation at a SYMBOLIC `z`; and MUTANT coercions that BREAK the
//! identity at a discriminating witness (zeroext padding TRUE; extract at offset
//! 1; extract width+1; or with a nonzero const) are kernel-REJECTED.
//!
//! Names live under `Clean.BVC.` (BVC = bit-vector coercion).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::name::Name;
use crate::{
    BinderInfo, Constructor, Declaration, EnvError, Environment, Expr, InductiveDecl,
    InductiveType, Level,
};

/// Declaration names for the coercion-identity layer.
pub mod names {
    /// `bvAppend : List Bool → List Bool → List Bool` (xs ++ ys).
    pub const APPEND: &str = "Clean.BVC.bvAppend";
    /// `bvReplF : Nat → List Bool` (k copies of false).
    pub const REPL_F: &str = "Clean.BVC.bvReplF";
    /// `bvZeroExt : List Bool → Nat → List Bool` (append k falses = LSB-first zext).
    pub const ZEXT: &str = "Clean.BVC.bvZeroExt";
    /// `bvTakeLen : List Bool → List Bool → List Bool` (take (length xs) ys).
    pub const TAKE_LEN: &str = "Clean.BVC.bvTakeLen";
    /// `bvAllFalse : List Bool → List Bool` (a same-length all-false mask).
    pub const ALL_FALSE: &str = "Clean.BVC.bvAllFalse";
    /// `bvMul : List Bool → List Bool → List Bool` — a TOTAL shift-add multiplier
    /// (LSB-first, recurses on the first operand; each set bit adds a left-shifted
    /// copy of the second). Faithful (differential-validated vs the trust-side
    /// multiply), but its multiplication-correctness is NOT load-bearing for the
    /// mul coercion-identity discharge — both gate sides reflect to the SAME
    /// `BvF.Mul` over key-matched operands, so `bvf_mul_cong` cancels it by
    /// congruence (exactly as `bvUlt`'s value is not load-bearing for ult).
    pub const BV_MUL: &str = "Clean.BVC.bvMul";
    /// `bvToNat : List Bool → Nat` — LSB-first place value (`x0 + 2·bvToNat xs`).
    pub const BV_TO_NAT: &str = "Clean.BVC.bvToNat";
    /// `natToBvAux : Nat(width) → Nat(value) → List Bool` — the `width` low bits of
    /// `value`, LSB-first (`Nat.rec` on width; per-bit `Nat.mod _ 2` / `Nat.div _ 2`).
    pub const NAT_TO_BV_AUX: &str = "Clean.BVC.natToBvAux";
    /// `bvDiv : List Bool → List Bool → List Bool` — TOTAL, FAITHFUL unsigned division
    /// `natToBvAux (len a) (Nat.div (bvToNat a) (bvToNat b))`. Delegates to the kernel-
    /// native `Nat.div` (Lean semantics `n/0 = 0`, matching AArch64 `UDIV` by-zero = 0),
    /// so it computes REAL truncating division (differential-validated on literals), NOT
    /// a non-semantic stub (the bvUlt lesson). Reflected from the IR `BvUDiv` as `BvF.Div`
    /// over key-matched operands, so `bvf_div_cong` cancels it by congruence (the value is
    /// not load-bearing for the coercion-identity discharge, but is faithful so the
    /// substrate carries no footgun); composes with `divGuardBridge` for the b≠0 guard.
    ///
    /// SCOPE (honesty — UNSIGNED DIV ONLY; REM and signed SDIV are DEFERRED):
    /// - Signed `SDIV` rounds toward zero, which differs from `Nat.div`'s floor for
    ///   negative operands, so a consumer MUST reflect only `BvUDiv` to `BvF.Div`,
    ///   NEVER `BvSDiv` (a distinct signed node is future work).
    /// - There is no `BvF.Rem` ctor. AArch64 `a % b` lowers to `a - (a/b)*b`, which is
    ///   dischargeable by `bvf_sub_cong` + `bvf_mul_cong` + `bvf_div_cong` JOINTLY over
    ///   the composite — NOT by `bvf_div_cong` alone.
    /// WIDTH-SOUNDNESS (why `natToBvAux (len a)` never truncates): the quotient
    /// `q = a/b ≤ a < 2^(len a)` for `b≠0`, and `q = 0` for `b=0`, so the low `len a`
    /// bits always hold the exact quotient.
    pub const BV_DIV: &str = "Clean.BVC.bvDiv";
    /// `bvNeg : List Bool → List Bool` — two's-complement negate (`addRecM (bvNot x) allFalse true`
    /// = `~x + 1`).
    pub const BV_NEG: &str = "Clean.BVC.bvNeg";
    /// `bvAbs : List Bool → List Bool` — signed absolute value (`bvIteVal (bvLastBit x) (bvNeg x) x`).
    pub const BV_ABS: &str = "Clean.BVC.bvAbs";
    /// `bvSDiv : List Bool → List Bool → List Bool` — TOTAL, FAITHFUL SIGNED division by
    /// sign-magnitude: `bvIteVal (xor (msb a) (msb b)) (bvNeg q) q` with `q = bvDiv (bvAbs a)(bvAbs b)`.
    /// Magnitude division truncates (Nat.div) and the sign is applied AFTER, so this rounds TOWARD
    /// ZERO — matching AArch64 `SDIV` (and SDIV-by-0 = 0, since `bvDiv _ 0 = 0` and `bvNeg 0 = 0`;
    /// INT_MIN/-1 wraps to INT_MIN, also matching). Reflected from the IR `BvSDiv` as `BvF.SDiv`.
    pub const BV_SDIV: &str = "Clean.BVC.bvSDiv";
    /// `bvShl : List Bool → List Bool → List Bool` — logical LEFT shift by the (already mask-
    /// reduced) amount `n`: `natToBvAux (bvLen a) (Nat.shiftLeft (bvToNat a) (bvToNat n))`
    /// (truncated to width, so high bits shift out — matches AArch64 `LSL`).
    pub const BV_SHL: &str = "Clean.BVC.bvShl";
    /// `bvLShr : List Bool → List Bool → List Bool` — LOGICAL right shift (zero-fill):
    /// `natToBvAux (bvLen a) (Nat.shiftRight (bvToNat a) (bvToNat n))` (AArch64 `LSR`).
    pub const BV_LSHR: &str = "Clean.BVC.bvLShr";
    /// `bvAShr : List Bool → List Bool → List Bool` — ARITHMETIC right shift (sign-fill):
    /// `bvIteVal (bvLastBit a) (bvNot (bvLShr (bvNot a) n)) (bvLShr a n)` — for a negative `a`
    /// the complement trick fills 1s from the top (AArch64 `ASR`); for non-negative it is `bvLShr`.
    pub const BV_ASHR: &str = "Clean.BVC.bvAShr";
    /// `bvTwoPow : Nat → Nat` — `2^k` (`Nat.rec` + `Nat.mul`); used to express shifts as
    /// `Nat.mul`/`Nat.div` by a power of two, which are DECLARED (axiom-free), unlike the
    /// native-only `Nat.shiftLeft`/`Nat.shiftRight`.
    pub const BV_TWO_POW: &str = "Clean.BVC.bvTwoPow";
    /// `bvZipOr : List Bool → List Bool → List Bool` (pointwise or; length of 1st).
    pub const ZIP_OR: &str = "Clean.BVC.bvZipOr";
    /// `extract_zeroext_id : ∀ z k, bvTakeLen z (bvZeroExt z k) = z`.
    pub const EXTRACT_ZEXT_ID: &str = "Clean.BVC.extract_zeroext_id";
    /// `bvTakeLenAppend : ∀ (s w : List Bool), bvTakeLen s (bvAppend s w) = s`
    /// — take `len(s)` bits from `s ++ w` = `s`, for ANY suffix `w` (not just the
    /// `bvReplF k` zeros of `extract_zeroext_id`, which is the `w := bvReplF k` case).
    /// THE general prefix-take identity: the load-bearing lemma for sub-register-width
    /// (u8/u16) readout normalization, where an `ExtractLow` slices a value NARROWER
    /// than the zero-ext inner it sits over (`extract width ≠ zero-ext inner length`) —
    /// the exact spine the memory store-load [PROVED] promotion needs. Proven by
    /// induction on `s` (nil: `bvTakeLen nil _ ≡ nil`; cons: `bvTakeLen (h::t)(h::t++w)
    /// ≡ h :: bvTakeLen t (t++w)`, closed by `congrArg (h :: ·) ih`). Empty
    /// domain-axiom closure. NON-VACUITY: dropping the prefix structure (`bvTakeLen s
    /// (a ++ w) = s` for `a ≠ s`) is FALSE and kernel-REJECTED.
    pub const BV_TAKE_LEN_APPEND: &str = "Clean.BVC.bvTakeLenAppend";
    /// `or_zero_id : ∀ z, bvZipOr (bvAllFalse z) z = z`.
    pub const OR_ZERO_ID: &str = "Clean.BVC.or_zero_id";
    /// `add_zero_id : ∀ y, addRecM (bvAllFalse y) y false = y` — the ripple-adder
    /// LEFT-identity (adding all-false with carry-in false returns y). Strips the
    /// AArch64 `madd Wd,Wn,Wm,WZR` (= `BvAdd(0, mul)`) wrapper the IR `BvMul` lacks.
    pub const ADD_ZERO_ID: &str = "Clean.BVC.add_zero_id";
    /// `bvf_add_zero_id : ∀ (e : BvF), bvfEval (Add (Const (bvAllFalse (bvfEval e))) e) = bvfEval e`
    /// — the bvfEval lift of `add_zero_id` (mirrors `bvf_or_zero_id`).
    pub const BVF_ADD_ZERO_ID: &str = "Clean.BVC.bvf_add_zero_id";
    /// The Formula-mirroring datatype `Clean.BVC.BvF`.
    pub const BVF: &str = "Clean.BVC.BvF";
    /// `bvfEval : BvF → List Bool`.
    pub const BVF_EVAL: &str = "Clean.BVC.bvfEval";
    /// `bvf_extract_zeroext_id : ∀ (e : BvF) k,
    ///     bvfEval (ExtractLow (ZeroExt e k) (lenTag e)) = bvfEval e`  (see note).
    pub const BVF_EXTRACT_ZEXT_ID: &str = "Clean.BVC.bvf_extract_zeroext_id";
    /// `bvf_or_zero_id : ∀ (e : BvF), bvfEval (Or (ConstAllFalse e) e) = bvfEval e`.
    pub const BVF_OR_ZERO_ID: &str = "Clean.BVC.bvf_or_zero_id";
    /// THE COMPOSED GATE-SHAPE DISCHARGE (B2a): the gate's move-via-ORR + W-register
    /// round-trip wrapper `W(e) = ExtractLow(ZeroExt(Or(Const 0, e), k), e)` is
    /// IDENTITY on `bvfEval`, parametric over the inner shared subterm `e`:
    /// `bvf_wrapper_id : ∀ (e : BvF) (k : Nat), bvfEval (W e k) = bvfEval e`.
    /// Composes `or_zero_id` (inner Or) then `extract_zeroext_id` (outer slice).
    pub const BVF_WRAPPER_ID: &str = "Clean.BVC.bvf_wrapper_id";
    /// `bvfEval`-headed Add-congruence (B2b-positive composition keystone):
    /// `bvf_add_cong : ∀ (a a' b b' : BvF), bvfEval a = bvfEval a' →
    ///     bvfEval b = bvfEval b' → bvfEval (Add a b) = bvfEval (Add a' b')`.
    pub const BVF_ADD_CONG: &str = "Clean.BVC.bvf_add_cong";
    /// `bvf_or_cong2 : ∀ (c x x' : BvF), bvfEval x = bvfEval x' →
    ///     bvfEval (Or c x) = bvfEval (Or c x')` (congruence in Or's 2nd arg).
    pub const BVF_OR_CONG2: &str = "Clean.BVC.bvf_or_cong2";
    /// `bvf_zext_cong : ∀ (x x' : BvF) (k : Nat), bvfEval x = bvfEval x' →
    ///     bvfEval (ZeroExt x k) = bvfEval (ZeroExt x' k)` (congruence in the operand).
    pub const BVF_ZEXT_CONG: &str = "Clean.BVC.bvf_zext_cong";
    /// `bvf_extract_cong1 : ∀ (x x' tag : BvF), bvfEval x = bvfEval x' →
    ///     bvfEval (ExtractLow x tag) = bvfEval (ExtractLow x' tag)` (congruence in the inner).
    pub const BVF_EXTRACT_CONG1: &str = "Clean.BVC.bvf_extract_cong1";
    /// `bvNot : List Bool → List Bool` (per-bit complement; for the Sub model).
    pub const BV_NOT: &str = "Clean.BVC.bvNot";
    /// `bvf_sub_cong : ∀ (a a' b b' : BvF), bvfEval a = bvfEval a' →
    ///     bvfEval b = bvfEval b' → bvfEval (Sub a b) = bvfEval (Sub a' b')`
    /// (the SUB analogue of `bvf_add_cong`; B4 SUB-op wiring).
    pub const BVF_SUB_CONG: &str = "Clean.BVC.bvf_sub_cong";
    /// `bvZipAnd : List Bool → List Bool → List Bool` (pointwise and; length of 1st).
    pub const ZIP_AND: &str = "Clean.BVC.bvZipAnd";
    /// `bvZipXor : List Bool → List Bool → List Bool` (pointwise xor; length of 1st).
    pub const ZIP_XOR: &str = "Clean.BVC.bvZipXor";
    /// `bvf_and_cong` / `bvf_xor_cong` — bitwise op congruences (B4 AND/XOR wiring).
    pub const BVF_AND_CONG: &str = "Clean.BVC.bvf_and_cong";
    pub const BVF_XOR_CONG: &str = "Clean.BVC.bvf_xor_cong";
    /// `bvf_or_cong : ∀ (a a' b b' : BvF), bvfEval a = bvfEval a' →
    ///     bvfEval b = bvfEval b' → bvfEval (Or a b) = bvfEval (Or a' b')`
    ///
    /// The GENERAL two-sided OR congruence, and the sibling of `bvf_and_cong` /
    /// `bvf_xor_cong` — `bvfEval (Or x y)` reduces to `bvZipOr (eval x)(eval y)`,
    /// the identical shape.
    ///
    /// # Why this was missing, and what its absence cost
    ///
    /// [`BVF_OR_CONG2`] is one-sided: it only relates `Or c x` to `Or c x'` for a
    /// FIXED left operand, which is all the `Orr Wd, WZR, Ws` register-move
    /// wrapper needs. Every other binary op — and, xor, mul, div, sdiv, shl,
    /// lshr, ashr — had the general two-sided form, so a machine `Orr` with two
    /// real operands (a user-level `|`) was the ONE binary shape with no O(1)
    /// coercion-identity route through `reflect_formula`.
    ///
    /// It therefore fell out of that path and back onto bit-blast + SAT + kernel
    /// re-check. (c) MEASURED before this theorem existed, compiling one function
    /// through `trust-cg` with `--emit=link`: `(x ^ y) ^ (x & y)` cost 2.76 s and
    /// **0.99 GB**, while `(x ^ y) | (x & y)` — identical shape, one instruction
    /// different (`eor` vs `orr`) — cost 20.94 s and **27.41 GB**. At five ops the
    /// OR form reached **54.78 GB**, past physical memory.
    pub const BVF_OR_CONG: &str = "Clean.BVC.bvf_or_cong";
    /// `bvf_mul_cong : ∀ (a a' b b' : BvF), bvfEval a = bvfEval a' →
    ///     bvfEval b = bvfEval b' → bvfEval (Mul a b) = bvfEval (Mul a' b')`
    /// (the MUL analogue of `bvf_add_cong`; B4 MUL-op wiring — cancels the shared
    /// `BvF.Mul` by congruence, so the eval's mul-correctness is not load-bearing).
    pub const BVF_MUL_CONG: &str = "Clean.BVC.bvf_mul_cong";
    /// `bvf_div_cong : ∀ (a a' b b' : BvF), bvfEval a = bvfEval a' →
    ///     bvfEval b = bvfEval b' → bvfEval (Div a b) = bvfEval (Div a' b')`
    /// (`bvfEval (Div x y)` reduces to `bvDiv (eval x)(eval y)`; same `Eq.subst` shape
    /// as mul — the gate cancels the shared `BvF.Div` node by congruence under the
    /// `divGuardBridge` divisor-nonzero precondition; the eval's div-value is not
    /// load-bearing for this discharge).
    pub const BVF_DIV_CONG: &str = "Clean.BVC.bvf_div_cong";
    /// `bvf_sdiv_cong` — the `bvfEval`-headed congruence for `BvF.SDiv` (same table-driven
    /// Eq.subst shape as div; `bvfEval (SDiv x y)` reduces to `bvSDiv (eval x)(eval y)`).
    pub const BVF_SDIV_CONG: &str = "Clean.BVC.bvf_sdiv_cong";
    /// `bvf_shl_cong` / `bvf_lshr_cong` / `bvf_ashr_cong` — the `bvfEval`-headed congruences for
    /// `BvF.Shl` / `BvF.LShr` / `BvF.AShr` (table-driven Eq.subst, same shape as div).
    pub const BVF_SHL_CONG: &str = "Clean.BVC.bvf_shl_cong";
    pub const BVF_LSHR_CONG: &str = "Clean.BVC.bvf_lshr_cong";
    pub const BVF_ASHR_CONG: &str = "Clean.BVC.bvf_ashr_cong";

    // ── EQ predicate layer (compares RUNG 1) ──────────────────────────────────
    /// `bvBeq : List Bool → List Bool → Bool` — genuine per-bit list equality
    /// (the IR-side `Eq(a,b)` predicate, separate from the Z/sub form).
    pub const BV_BEQ: &str = "Clean.BVC.bvBeq";
    /// `bvIsZero : List Bool → Bool` — true iff every bit is false (the SUBS Z
    /// flag; the machine-side `Not(a-b != 0)` reduces to `bvIsZero (a-b)`).
    pub const BV_IS_ZERO: &str = "Clean.BVC.bvIsZero";
    /// `bvIteVal : Bool → List Bool → List Bool → List Bool` — the compare
    /// register value `Ite(p, v_then, v_else)` via `@Bool.rec (fun _ => List Bool)`.
    pub const BV_ITE_VAL: &str = "Clean.BVC.bvIteVal";
    /// `iteVal_not : ∀ p u v, bvIteVal (Bool.not p) u v = bvIteVal p v u`
    /// (the inverted-CSET branch-swap identity).
    pub const ITE_VAL_NOT: &str = "Clean.BVC.iteVal_not";
    /// `divGuardBridge : ∀ (b z dv : List Bool), bvIsZero b = false →
    ///     bvIteVal (bvIsZero b) z dv = dv`
    /// — THE CONDITIONAL-DISCHARGE KEYSTONE. Models the AArch64 div-by-zero guard
    /// `Ite(Eq(divisor,0), 0, div)`: under the precondition `divisor ≠ 0`
    /// (`bvIsZero b = false`), the guarded value collapses to the else branch `dv`
    /// (the unguarded divide). Proven by `Eq.subst` rewriting the guard predicate to
    /// `false` via the hypothesis, so the lemma GENUINELY USES the precondition —
    /// dropping it leaves `bvIteVal (bvIsZero b) z dv` STUCK, unprovable by refl.
    /// Reusable infra for ANY preconditioned obligation (div/rem + the construct
    /// dimension). Empty domain-axiom closure.
    pub const DIV_GUARD_BRIDGE: &str = "Clean.BVC.divGuardBridge";
    /// `bvBeq_refl : ∀ (a : List Bool), bvBeq a a = true` — per-bit equality is
    /// reflexive (the address self-match for the store-load roundtrip). Induction on
    /// `a` with a `Bool.rec` head-dispatch (`xor h h = false` ⇒ `not false = true` ⇒
    /// `and true ih = ih`). Empty domain-axiom closure.
    pub const BV_BEQ_REFL: &str = "Clean.BVC.bvBeq_refl";
    /// `bvSelect : (List Bool → List Bool) → List Bool → List Bool` — array read at
    /// an address. Model: an array is a function `addr → value`; `bvSelect m a := m a`.
    pub const BV_SELECT: &str = "Clean.BVC.bvSelect";
    /// `bvStore : (List Bool → List Bool) → List Bool → List Bool → (List Bool → List Bool)`
    /// — array write. `bvStore m a v := fun a' => bvIteVal (bvBeq a a') v (m a')`
    /// (point-update: address `a` reads back `v`; every other address is unchanged).
    pub const BV_STORE: &str = "Clean.BVC.bvStore";
    /// `selectStoreSame : ∀ m a v, bvSelect (bvStore m a v) a = v` — THE single-address
    /// READ-OVER-WRITE keystone (the array analogue of the scalar coercion-identity).
    /// For the SAME address the stored value reads back. Proven via `bvBeq_refl`
    /// collapsing the store guard (`bvIteVal (bvBeq a a) v (m a) = bvIteVal true v (m a)
    /// = v`). NON-VACUOUS (a wrong-address read or the no-store variant fails at a
    /// discriminating witness). Empty domain-axiom closure. The construct dimension's
    /// first rung (memory store-load).
    pub const SELECT_STORE_SAME: &str = "Clean.BVC.selectStoreSame";
    /// `selectStoreDiff : ∀ m a a' v, bvBeq a a' = false → bvSelect (bvStore m a v) a' = bvSelect m a'`
    /// — THE non-aliasing read-over-write: a load at a DIFFERENT address than the store sees THROUGH
    /// the store to the underlying memory. The conditional (false-branch) partner of selectStoreSame;
    /// the memory keystone for multi-cell / multi-byte store-load (each byte load skips the later
    /// byte stores via selectStoreDiff and hits its own via selectStoreSame).
    pub const SELECT_STORE_DIFF: &str = "Clean.BVC.selectStoreDiff";
    /// `selectAddrCong : ∀ (m : List Bool → List Bool) (a a' : List Bool),
    ///     a = a' → bvSelect m a = bvSelect m a'`
    ///
    /// THE CALLER-PROVIDED-MEMORY keystone: a congruence over `bvSelect`'s ADDRESS
    /// argument, at a FIXED array `m`. Two reads of the SAME untouched memory at
    /// PROVABLY-EQUAL addresses return the same value.
    ///
    /// # Why this one is different from `selectStoreSame` / `selectStoreDiff`
    ///
    /// Both of those relate a read to a WRITE the term itself performs — they are
    /// read-over-write laws, and the underlying `m` is never inspected (which is
    /// why the store-load path can abstract it as a closed dummy array). Neither
    /// says anything about a read from an OPAQUE PRE-STATE: memory the function
    /// never wrote, i.e. exactly what a load through a `&T` PARAMETER is. There
    /// was no lemma for that shape at all, so a bare `bvSelect M a` was stuck and
    /// the whole obligation fell outside the fragment.
    ///
    /// This is the missing law, and it is the WEAKEST one that suffices: it does
    /// NOT interpret `m`, does not require `m` closed, and asserts nothing about
    /// aliasing. It only transports an address equality under the read. That is
    /// enough because the two sides of a machine-vs-IR obligation read the SAME
    /// pre-state — sound precisely when nothing has written to it (a read-only
    /// body); the caller enforces that side condition, this lemma does not.
    ///
    /// # Shape and non-vacuity
    ///
    /// Proven by the same `Eq.subst` shape as the rest of the layer (motive
    /// `l := bvSelect m a = bvSelect m l`, base `Eq.refl (bvSelect m a)`), so it
    /// carries an empty domain-axiom closure. The hypothesis is LOAD-BEARING:
    /// dropping it leaves the FALSE `∀ m a a', bvSelect m a = bvSelect m a'`
    /// (`bvSelect` genuinely depends on its address — at `m := fun w => w` the two
    /// sides are `a` and `a'`), which is kernel-REJECTED.
    ///
    /// The address argument is second, so this does NOT fit the generated
    /// `bvf_*_cong` table: those rows are two-hypothesis congruences over a
    /// `BvF` binary constructor whose `bvfEval` reduces to a `List Bool → List
    /// Bool → List Bool` op. `bvSelect`'s first argument is an ARRAY
    /// (`List Bool → List Bool`) and there is no `BvF.Select` constructor, so it
    /// lives here with the other two memory lemmas instead.
    pub const SELECT_ADDR_CONG: &str = "Clean.BVC.selectAddrCong";
    /// `bvBeqConsFalse : ∀ (h1 h2 : Bool) (t1 t2 : List Bool), Bool.xor h1 h2 = true →
    ///     bvBeq (h1 :: t1) (h2 :: t2) = false`
    /// — THE address-distinctness REDUCTION STEP feeding `selectStoreDiff`. `bvBeq` is the
    /// per-bit `and (not (xor · ·))` fold; a single differing head bit (`xor h1 h2 = true`)
    /// makes the head factor `and (not true) _ = and false _ = false`, so the whole conjunction
    /// is false REGARDLESS of the tails. Proven by the `divGuardBridge` `Eq.subst` shape
    /// (rewrite `xor h1 h2 → true`, base `and (not true) (bvBeq t1 t2) = false` is refl). This
    /// is how the byte-adjacency non-aliasing `bvBeq (X_p+k) (X_p+j) = false` (k≠j) discharges:
    /// the low bits of `X_p+k` and `X_p+j` are `x0 ⊕ k0` and `x0 ⊕ j0`, which differ iff
    /// `k0 ≠ j0` — the symbolic base `x0` cancels — so a `Bool.rec` split on `x0` supplies the
    /// `xor = true` hypothesis. Empty domain-axiom closure. NON-VACUITY: dropping the hypothesis
    /// (an unconditional `bvBeq (h1::t1) (h2::t2) = false`) is FALSE (take h1=h2, t1=t2) and is
    /// kernel-REJECTED.
    pub const BV_BEQ_CONS_FALSE: &str = "Clean.BVC.bvBeqConsFalse";
    /// `bvLen : List Bool → Nat` — list length (the equal-width bridge guard).
    pub const BV_LEN: &str = "Clean.BVC.bvLen";
    /// `beq_eq_isZero_sub : ∀ a b, bvLen a = bvLen b →
    ///     bvBeq a b = bvIsZero (addRecM a (bvNot b) true)`
    /// (the subtract-zero predicate bridge: at equal width, `a == b ⟺ a - b == 0`).
    pub const BEQ_EQ_ISZERO_SUB: &str = "Clean.BVC.beq_eq_isZero_sub";
    /// `eq_value_bridge : ∀ a b vt ve, bvLen a = bvLen b →
    ///     bvIteVal (Bool.not (bvIsZero (addRecM a (bvNot b) true))) ve vt
    ///       = bvIteVal (bvBeq a b) vt ve`
    /// — the composed EQ register-value equality (machine inverted-CSET form ==
    /// IR `Ite(a==b, vt, ve)`): branch-inversion (iteVal_not) + the subtract-zero
    /// bridge. The trust eq reflect arm instantiates this at the operand cores.
    pub const EQ_VALUE_BRIDGE: &str = "Clean.BVC.eq_value_bridge";
    /// `carryOut : List Bool → List Bool → Bool → Bool` — final carry-out of the
    /// ripple adder (maj-threaded; the SUBS C-flag source).
    pub const CARRY_OUT: &str = "Clean.BVC.carryOut";
    /// `bvUlt : List Bool → List Bool → Bool` — GENUINELY computes unsigned
    /// less-than, in the BORROW form `Bool.not (carryOut a (bvNot b) true)`:
    /// `a <u b` iff the borrow-out of `a - b = a + ¬b + 1` is set (carry-out 0).
    /// Kernel-verified-computing (`test_bvult_computes_real_unsigned_lt`:
    /// `bvUlt 2 1 ⟶ false`, `bvUlt 1 2 ⟶ true`). ult/ule soundness rests on
    /// branch-inversion (semantics-agnostic), but the faithful signed predicate
    /// `bvSLtReal a b := bvUlt (bvFlipMsb a) (bvFlipMsb b)` CORRECTLY DEPENDS ON
    /// bvUlt computing real unsigned-LT (signed-LT = unsigned-LT after flipping
    /// the sign bit — the classic identity).
    pub const BV_ULT: &str = "Clean.BVC.bvUlt";
    /// `bvFlipMsb : List Bool → List Bool` — flip the MSB (last element).
    pub const BV_FLIP_MSB: &str = "Clean.BVC.bvFlipMsb";
    /// `bvSLtReal : List Bool → List Bool → Bool` — FAITHFUL signed-LT, defined as
    /// `bvUlt (bvFlipMsb a) (bvFlipMsb b)` (the classic identity: signed compare =
    /// unsigned compare after flipping the sign bit). Self-evidently signed-LT.
    pub const BV_SLT_REAL: &str = "Clean.BVC.bvSLtReal";
    /// `bvLastBit : List Bool → Bool` — the MSB (last element; false if empty).
    pub const BV_LAST_BIT: &str = "Clean.BVC.bvLastBit";
    /// `bvIsCons : List Bool → Bool` — true iff the list is a cons (non-empty).
    pub const BV_IS_CONS: &str = "Clean.BVC.bvIsCons";
    /// `slt_flag_bridge : ∀ a b, bvIsCons a = true → bvLen a = bvLen b →
    ///     bvSLtReal a b = Bool.xor N V` (the N⊕V signed-overflow theorem).
    /// N = bvLastBit(addRecM a (bvNot b) true); V = And(bxor(msb a, msb b),
    /// bxor(N, msb a)). The `bvIsCons` guard makes the width-0 case (where the
    /// statement degenerates) absurd; the gate's width-32 operands discharge it
    /// by refl. The genuine signed bridge (carry-invariant induction, singleton
    /// base valid for all c).
    pub const SLT_FLAG_BRIDGE: &str = "Clean.BVC.slt_flag_bridge";
    /// `idP : ∀ (P : Prop), P → P` — the GENERAL def-eq-carrying coercion combinator
    /// (the #46 motive-redex fix, abstracted ONCE). `@idP Q proof` ascribes the
    /// UN-reduced type Q the recursor minor expects, with `proof : Q` checked by
    /// full def_eq (reducing). Usable at ANY recursor layer / any motive shape.
    pub const IDP: &str = "Clean.BVC.idP";
    /// `ult_value_bridge : ∀ a b vt ve,
    ///     bvIteVal (Bool.not (bvUlt a b)) ve vt = bvIteVal (bvUlt a b) vt ve`
    /// — the ULT register-value equality (machine inverted-CSET `Ite(¬(a<b),0,1)`
    /// == IR `Ite(a<b,1,0)`); PURE branch-inversion (iteVal_not), no length guard.
    pub const ULT_VALUE_BRIDGE: &str = "Clean.BVC.ult_value_bridge";
    /// `bvULe : List Bool → List Bool → Bool` := `Or(bvUlt, bvBeq)`. As with
    /// bvUlt, this is the predicate the IR's `BvULe` reflects to; ule soundness
    /// rests on the De Morgan + subtract-zero + branch-inversion composition (the
    /// machine `And(Not(BvULt),Not(Eq(BvSub,0)))` reflects to the matching form),
    /// NOT on bvULe computing unsigned-≤.
    pub const BV_ULE: &str = "Clean.BVC.bvULe";
    /// `demorgan_and_not : ∀ p q, Bool.and (Bool.not p) (Bool.not q) = Bool.not (Bool.or p q)`.
    pub const DEMORGAN_AND_NOT: &str = "Clean.BVC.demorgan_and_not";
    /// `ule_value_bridge : ∀ a b vt ve, bvLen a = bvLen b →
    ///     bvIteVal (Bool.and (Bool.not (bvUlt a b)) (Bool.not (bvIsZero (addRecM a (bvNot b) true)))) ve vt
    ///       = bvIteVal (bvULe a b) vt ve`
    /// — the ULE register-value equality (machine inverted Hi-condition == IR
    /// `Ite(a<=b,1,0)`): De Morgan + subtract-zero bridge + branch-inversion.
    pub const ULE_VALUE_BRIDGE: &str = "Clean.BVC.ule_value_bridge";
    /// `slt_value_bridge : ∀ a b vt ve, bvIsCons a = true → bvLen a = bvLen b →
    ///     bvIteVal (Bool.not (Bool.xor N V)) ve vt = bvIteVal (bvSLtReal a b) vt ve`
    /// — the SLT register-value equality (machine inverted AArch64 `LT` flag `N⊕V`
    /// == IR `Ite(a <s b, 1, 0)`): composes `slt_flag_bridge` (xor N V = bvSLtReal)
    /// with branch-inversion (`iteVal_not`). N = bvLastBit(addRecM a (bvNot b) true),
    /// V = And(bxor(msb a, msb b), bxor(N, msb a)). Mirrors `ule_value_bridge`.
    pub const SLT_VALUE_BRIDGE: &str = "Clean.BVC.slt_value_bridge";
    /// `bvSLeReal : List Bool → List Bool → Bool` := `Or(bvSLtReal, bvBeq)`
    /// (signed `<=` = signed `<` or `=`). The IR predicate the gate's `BvSLe`
    /// reflects to; faithfulness rests on `bvSLtReal` (signed-LT) + `bvBeq` (eq).
    pub const BV_SLE_REAL: &str = "Clean.BVC.bvSLeReal";
    /// `sle_value_bridge : ∀ a b vt ve, bvIsCons a = true → bvLen a = bvLen b →
    ///     bvIteVal (And(Not(bvIsZero(sub)), Not(Bool.xor N V))) ve vt
    ///       = bvIteVal (bvSLeReal a b) vt ve`
    /// — the SLE register-value equality (machine inverted `a > b` flag
    /// `And(a≠b, a>=s b)` == IR `Ite(a <=s b, 1, 0)`): composes the subtract-zero
    /// bridge (bvIsZero(sub) = bvBeq), the slt flag bridge (xor N V = bvSLtReal),
    /// De Morgan, and branch-inversion. Mirrors `ule_value_bridge`.
    pub const SLE_VALUE_BRIDGE: &str = "Clean.BVC.sle_value_bridge";
}

// ── Bool / List Bool / Nat term helpers ───────────────────────────────────────
fn bool_ty() -> Expr {
    Expr::const_str("Bool")
}
fn bfalse() -> Expr {
    Expr::const_str("Bool.false")
}
fn nat_ty() -> Expr {
    Expr::const_str("Nat")
}
fn bor(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Bool.or"), [x, y])
}
fn band(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Bool.and"), [x, y])
}
fn bxor(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Bool.xor"), [x, y])
}
fn list_bool() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        bool_ty(),
    )
}
fn nil_b() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        bool_ty(),
    )
}
fn cons_b(h: Expr, t: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
        [bool_ty(), h, t],
    )
}
fn app2(xs: Expr, ys: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::APPEND), [xs, ys])
}
fn zext(e: Expr, k: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::ZEXT), [e, k])
}
fn take_len(xs: Expr, ys: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::TAKE_LEN), [xs, ys])
}
fn all_false(z: Expr) -> Expr {
    Expr::app(Expr::const_str(names::ALL_FALSE), z)
}
fn zip_or(xs: Expr, ys: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::ZIP_OR), [xs, ys])
}
#[cfg(test)]
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
fn zip_and(xs: Expr, ys: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::ZIP_AND), [xs, ys])
}
#[cfg(test)]
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
fn zip_xor(xs: Expr, ys: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::ZIP_XOR), [xs, ys])
}
fn btrue() -> Expr {
    Expr::const_str("Bool.true")
}
fn bnot(x: Expr) -> Expr {
    Expr::app(Expr::const_str("Bool.not"), x)
}
fn bv_not(x: Expr) -> Expr {
    Expr::app(Expr::const_str(names::BV_NOT), x)
}
/// `addRecM a b cin` — the #34 machine ripple adder (reused for the Sub model).
fn bv_ult_op(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::BV_ULT), [a, b])
}
fn carry_out(a: Expr, b: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::CARRY_OUT), [a, b, c])
}
fn flip_msb(x: Expr) -> Expr {
    Expr::app(Expr::const_str(names::BV_FLIP_MSB), x)
}
fn last_bit(x: Expr) -> Expr {
    Expr::app(Expr::const_str(names::BV_LAST_BIT), x)
}
fn bv_slt_real(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::BV_SLT_REAL), [a, b])
}
fn bv_is_cons(x: Expr) -> Expr {
    Expr::app(Expr::const_str(names::BV_IS_CONS), x)
}
/// `@idP Q proof : Q` — ascribe the (un-reduced) Prop type Q via the general
/// def-eq-carrying combinator; `proof` is checked at Q by full def_eq.
#[cfg(test)]
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
fn idp(q: Expr, proof: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::IDP), [q, proof])
}
fn bv_ule_op(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::BV_ULE), [a, b])
}
fn add_rec_m(a: Expr, b: Expr, cin: Expr) -> Expr {
    Expr::apps(
        Expr::const_str(crate::bitvec_inductive::names::ADD_REC_M),
        [a, b, cin],
    )
}
fn bv_beq(xs: Expr, ys: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::BV_BEQ), [xs, ys])
}
fn bv_is_zero(xs: Expr) -> Expr {
    Expr::app(Expr::const_str(names::BV_IS_ZERO), xs)
}
#[cfg(test)]
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
fn lb_bool_arrow() -> Expr {
    Expr::arrow(list_bool(), bool_ty())
}
fn bv_ite_val(p: Expr, vt: Expr, ve: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::BV_ITE_VAL), [p, vt, ve])
}
/// `@Eq Bool x y` — Bool-level equality.
fn eq_bool(x: Expr, y: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [bool_ty(), x, y],
    )
}
fn bv_beq_l(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::BV_BEQ), [x, y])
}
fn bv_is_zero_l(x: Expr) -> Expr {
    Expr::app(Expr::const_str(names::BV_IS_ZERO), x)
}
fn bv_not_l(x: Expr) -> Expr {
    Expr::app(Expr::const_str(names::BV_NOT), x)
}
fn add_rec_m_l(a: Expr, b: Expr, c: Expr) -> Expr {
    Expr::apps(
        Expr::const_str(crate::bitvec_inductive::names::ADD_REC_M),
        [a, b, c],
    )
}
fn eq_refl_bool(v: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [bool_ty(), v],
    )
}

// ── Eq / proof-term helpers over List Bool ────────────────────────────────────
fn eq_list(x: Expr, y: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [list_bool(), x, y],
    )
}
fn eq_refl_list(v: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [list_bool(), v],
    )
}
/// `@congrArg.{1,1} (List Bool) (List Bool) a1 a2 f h : Eq (f a1) (f a2)`.
fn congr_arg_ll(a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
    let l1 = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        [list_bool(), list_bool(), a1, a2, f, h],
    )
}

impl Environment {
    /// Register the coercion-identity layer (B1). Idempotent.
    ///
    /// # Errors
    /// Propagates kernel-checking failures (a broken identity proof fails here).
    pub fn init_bv_coercion(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::OR_ZERO_ID))
            .is_some()
        {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;
        self.init_nat()?;
        self.init_list()?;
        self.register_bvc_ops()?;
        self.register_bvc_identities()?;
        self.register_bvf_datatype()?;
        // eq-predicate layer (bvIteVal, bvLastBit, bvIsZero, the value bridges, …) is
        // bvfEval-INDEPENDENT and is registered BEFORE register_bvf_eval so the signed-div
        // value `bvSDiv` (which uses bvIteVal/bvLastBit) is well-formed inside bvfEval's sdiv_case.
        self.register_bvf_eq_predicate()?;
        self.register_bvf_eval()?;
        self.register_bvf_identities()?;
        Ok(())
    }

    /// The `List Bool` coercion operations, as reducible recursive `Definition`s.
    fn register_bvc_ops(&mut self) -> Result<(), EnvError> {
        let llb = Expr::arrow(list_bool(), Expr::arrow(list_bool(), list_bool()));
        let lb = Expr::arrow(list_bool(), list_bool());

        // idP : ∀ (P : Prop), P → P := fun P p => p — the GENERAL def-eq-carrying
        // coercion (the #46 motive-redex fix, abstracted once). `@idP Q proof`
        // ascribes the UN-reduced type Q the recursor minor expects; `proof : Q` is
        // checked by full def_eq (which reduces). Reusable at any recursor layer.
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (pp_id, pp) = b.fresh_local(Expr::sort(Level::zero()));
                let inner = Expr::arrow(pp.clone(), pp.clone());
                b.finish(b.mk_pi(pp_id, BinderInfo::Default, Expr::sort(Level::zero()), inner))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (pp_id, pp) = b.fresh_local(Expr::sort(Level::zero()));
                let body = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (x_id, x) = c.fresh_local(pp.clone());
                    c.finish_child(c.mk_lam(x_id, BinderInfo::Default, pp.clone(), x))
                };
                b.finish(b.mk_lam(pp_id, BinderInfo::Default, Expr::sort(Level::zero()), body))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::IDP),
                level_params: vec![],
                type_: ty,
                value: val,
                is_reducible: true,
            })?;
        }

        // bvAppend xs ys := List.rec (fun _ => List Bool) ys (fun h _ ih => cons h ih) xs
        let append_val = {
            let mut b = EnvDeclBuilder::new();
            let (xs_id, xs) = b.fresh_local(list_bool());
            let (ys_id, ys) = b.fresh_local(list_bool());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(list_bool());
                c.finish_child(c.mk_lam(w_id, BinderInfo::Default, list_bool(), list_bool()))
            };
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(bool_ty());
                let (t_id, _t) = c.fresh_local(list_bool());
                let (ih_id, ih) = c.fresh_local(list_bool());
                let body = cons_b(h, ih);
                let r = c.mk_lam(ih_id, BinderInfo::Default, list_bool(), body);
                let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, bool_ty(), r))
            };
            let rec = list_rec_type1(motive, ys.clone(), cons_case, xs.clone());
            let r = b.mk_lam(ys_id, BinderInfo::Default, list_bool(), rec);
            b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_bool(), r))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::APPEND),
            level_params: vec![],
            type_: llb.clone(),
            value: append_val,
            is_reducible: true,
        })?;

        // bvReplF k := Nat.rec (fun _ => List Bool) nil (fun _ ih => cons false ih) k
        let replf_val = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(nat_ty());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(nat_ty());
                c.finish_child(c.mk_lam(w_id, BinderInfo::Default, nat_ty(), list_bool()))
            };
            let succ_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (n_id, _n) = c.fresh_local(nat_ty());
                let (ih_id, ih) = c.fresh_local(list_bool());
                let body = cons_b(bfalse(), ih);
                let r = c.mk_lam(ih_id, BinderInfo::Default, list_bool(), body);
                c.finish_child(c.mk_lam(n_id, BinderInfo::Default, nat_ty(), r))
            };
            let rec = nat_rec_type1(motive, nil_b(), succ_case, k.clone());
            b.finish(b.mk_lam(k_id, BinderInfo::Default, nat_ty(), rec))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::REPL_F),
            level_params: vec![],
            type_: Expr::arrow(nat_ty(), list_bool()),
            value: replf_val,
            is_reducible: true,
        })?;

        // bvZeroExt e k := bvAppend e (bvReplF k)
        let zext_val = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(list_bool());
            let (k_id, k) = b.fresh_local(nat_ty());
            let body = app2(e, Expr::app(Expr::const_str(names::REPL_F), k));
            let r = b.mk_lam(k_id, BinderInfo::Default, nat_ty(), body);
            b.finish(b.mk_lam(e_id, BinderInfo::Default, list_bool(), r))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::ZEXT),
            level_params: vec![],
            type_: Expr::arrow(list_bool(), Expr::arrow(nat_ty(), list_bool())),
            value: zext_val,
            is_reducible: true,
        })?;

        // bvTakeLen xs ys := List.rec (fun _ => List Bool → List Bool)
        //                      (fun _ => nil)
        //                      (fun _ _ ih => fun ws => cons (bhead ws) (ih (btail ws)))
        //                      xs ys
        // i.e. take (length xs) ys — recursion over xs, consuming ys via head/tail.
        // We inline head/tail to avoid an extra dependency: use List.rec on ys per step.
        let take_len_val = {
            let mut b = EnvDeclBuilder::new();
            let (xs_id, xs) = b.fresh_local(list_bool());
            let (ys_id, ys) = b.fresh_local(list_bool());
            // motive over xs : List Bool → (List Bool → List Bool)
            let consumer = Expr::arrow(list_bool(), list_bool());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(list_bool());
                c.finish_child(c.mk_lam(w_id, BinderInfo::Default, list_bool(), consumer.clone()))
            };
            // nil_case : List Bool → List Bool = fun _ => nil
            let nil_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ws_id, _ws) = c.fresh_local(list_bool());
                c.finish_child(c.mk_lam(ws_id, BinderInfo::Default, list_bool(), nil_b()))
            };
            // cons_case : (h:Bool)(t:List Bool)(ih:consumer) → consumer
            //   = fun h t ih => fun ws => listRec ws nil (fun wh wt _ => cons wh (ih wt))
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, _h) = c.fresh_local(bool_ty());
                let (t_id, _t) = c.fresh_local(list_bool());
                let (ih_id, ih) = c.fresh_local(consumer.clone());
                let inner = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (ws_id, ws) = d.fresh_local(list_bool());
                    // listRec over ws : motive (fun _ => List Bool)
                    let wmot = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (z_id, _z) = e.fresh_local(list_bool());
                        e.finish_child(e.mk_lam(
                            z_id,
                            BinderInfo::Default,
                            list_bool(),
                            list_bool(),
                        ))
                    };
                    let wcons = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (wh_id, wh) = e.fresh_local(bool_ty());
                        let (wt_id, wt) = e.fresh_local(list_bool());
                        let (wih_id, _wih) = e.fresh_local(list_bool());
                        let body = cons_b(wh, Expr::app(ih.clone(), wt));
                        let r = e.mk_lam(wih_id, BinderInfo::Default, list_bool(), body);
                        let r = e.mk_lam(wt_id, BinderInfo::Default, list_bool(), r);
                        e.finish_child(e.mk_lam(wh_id, BinderInfo::Default, bool_ty(), r))
                    };
                    let body = list_rec_type1(wmot, nil_b(), wcons, ws.clone());
                    d.finish_child(d.mk_lam(ws_id, BinderInfo::Default, list_bool(), body))
                };
                let r = c.mk_lam(ih_id, BinderInfo::Default, consumer.clone(), inner);
                let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, bool_ty(), r))
            };
            let rec = list_rec_type1(motive, nil_case, cons_case, xs.clone());
            let applied = Expr::app(rec, ys.clone());
            let r = b.mk_lam(ys_id, BinderInfo::Default, list_bool(), applied);
            b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_bool(), r))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::TAKE_LEN),
            level_params: vec![],
            type_: llb.clone(),
            value: take_len_val,
            is_reducible: true,
        })?;

        // bvAllFalse z := List.rec (fun _ => List Bool) nil (fun _ _ ih => cons false ih) z
        let all_false_val = {
            let mut b = EnvDeclBuilder::new();
            let (z_id, z) = b.fresh_local(list_bool());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(list_bool());
                c.finish_child(c.mk_lam(w_id, BinderInfo::Default, list_bool(), list_bool()))
            };
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, _h) = c.fresh_local(bool_ty());
                let (t_id, _t) = c.fresh_local(list_bool());
                let (ih_id, ih) = c.fresh_local(list_bool());
                let body = cons_b(bfalse(), ih);
                let r = c.mk_lam(ih_id, BinderInfo::Default, list_bool(), body);
                let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, bool_ty(), r))
            };
            let rec = list_rec_type1(motive, nil_b(), cons_case, z.clone());
            b.finish(b.mk_lam(z_id, BinderInfo::Default, list_bool(), rec))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::ALL_FALSE),
            level_params: vec![],
            type_: lb,
            value: all_false_val,
            is_reducible: true,
        })?;

        // bvNot z := List.rec (fun _ => List Bool) nil (fun h _ ih => cons (Bool.not h) ih) z
        // (per-bit complement; the Sub model uses it: sub a b = addRecM a (bvNot b) true.)
        let bnot1 = |x: Expr| Expr::app(Expr::const_str("Bool.not"), x);
        let bvnot_val = {
            let mut b = EnvDeclBuilder::new();
            let (z_id, z) = b.fresh_local(list_bool());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(list_bool());
                c.finish_child(c.mk_lam(w_id, BinderInfo::Default, list_bool(), list_bool()))
            };
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(bool_ty());
                let (t_id, _t) = c.fresh_local(list_bool());
                let (ih_id, ih) = c.fresh_local(list_bool());
                let body = cons_b(bnot1(h), ih);
                let r = c.mk_lam(ih_id, BinderInfo::Default, list_bool(), body);
                let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, bool_ty(), r))
            };
            let rec = list_rec_type1(motive, nil_b(), cons_case, z.clone());
            b.finish(b.mk_lam(z_id, BinderInfo::Default, list_bool(), rec))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::BV_NOT),
            level_params: vec![],
            type_: Expr::arrow(list_bool(), list_bool()),
            value: bvnot_val,
            is_reducible: true,
        })?;

        // bvZipOr xs ys := List.rec (fun _ => List Bool → List Bool)
        //   (fun _ => nil) (fun xh _ ih => fun ws => cons (or xh (bhead ws)) (ih (btail ws))) xs ys
        let zip_or_val = {
            let mut b = EnvDeclBuilder::new();
            let (xs_id, xs) = b.fresh_local(list_bool());
            let (ys_id, ys) = b.fresh_local(list_bool());
            let consumer = Expr::arrow(list_bool(), list_bool());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(list_bool());
                c.finish_child(c.mk_lam(w_id, BinderInfo::Default, list_bool(), consumer.clone()))
            };
            let nil_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ws_id, _ws) = c.fresh_local(list_bool());
                c.finish_child(c.mk_lam(ws_id, BinderInfo::Default, list_bool(), nil_b()))
            };
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (xh_id, xh) = c.fresh_local(bool_ty());
                let (xt_id, _xt) = c.fresh_local(list_bool());
                let (ih_id, ih) = c.fresh_local(consumer.clone());
                let inner = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (ws_id, ws) = d.fresh_local(list_bool());
                    let wmot = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (z_id, _z) = e.fresh_local(list_bool());
                        e.finish_child(e.mk_lam(
                            z_id,
                            BinderInfo::Default,
                            list_bool(),
                            list_bool(),
                        ))
                    };
                    let wcons = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (wh_id, wh) = e.fresh_local(bool_ty());
                        let (wt_id, wt) = e.fresh_local(list_bool());
                        let (wih_id, _wih) = e.fresh_local(list_bool());
                        let body = cons_b(bor(xh.clone(), wh), Expr::app(ih.clone(), wt));
                        let r = e.mk_lam(wih_id, BinderInfo::Default, list_bool(), body);
                        let r = e.mk_lam(wt_id, BinderInfo::Default, list_bool(), r);
                        e.finish_child(e.mk_lam(wh_id, BinderInfo::Default, bool_ty(), r))
                    };
                    let body = list_rec_type1(wmot, nil_b(), wcons, ws.clone());
                    d.finish_child(d.mk_lam(ws_id, BinderInfo::Default, list_bool(), body))
                };
                let r = c.mk_lam(ih_id, BinderInfo::Default, consumer.clone(), inner);
                let r = c.mk_lam(xt_id, BinderInfo::Default, list_bool(), r);
                c.finish_child(c.mk_lam(xh_id, BinderInfo::Default, bool_ty(), r))
            };
            let rec = list_rec_type1(motive, nil_case, cons_case, xs.clone());
            let applied = Expr::app(rec, ys.clone());
            let r = b.mk_lam(ys_id, BinderInfo::Default, list_bool(), applied);
            b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_bool(), r))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::ZIP_OR),
            level_params: vec![],
            type_: llb.clone(),
            value: zip_or_val,
            is_reducible: true,
        })?;

        // bvZipAnd / bvZipXor — same per-bit zip shape as bvZipOr, with Bool.and /
        // Bool.xor as the gate. Built via a closure over the per-bit op.
        for (zname, gate) in [
            (names::ZIP_AND, &band as &dyn Fn(Expr, Expr) -> Expr),
            (names::ZIP_XOR, &bxor as &dyn Fn(Expr, Expr) -> Expr),
        ] {
            let zip_val = {
                let mut b = EnvDeclBuilder::new();
                let (xs_id, xs) = b.fresh_local(list_bool());
                let (ys_id, ys) = b.fresh_local(list_bool());
                let consumer = Expr::arrow(list_bool(), list_bool());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(list_bool());
                    c.finish_child(c.mk_lam(
                        w_id,
                        BinderInfo::Default,
                        list_bool(),
                        consumer.clone(),
                    ))
                };
                let nil_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (ws_id, _ws) = c.fresh_local(list_bool());
                    c.finish_child(c.mk_lam(ws_id, BinderInfo::Default, list_bool(), nil_b()))
                };
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (xh_id, xh) = c.fresh_local(bool_ty());
                    let (xt_id, _xt) = c.fresh_local(list_bool());
                    let (ih_id, ih) = c.fresh_local(consumer.clone());
                    let inner = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (ws_id, ws) = d.fresh_local(list_bool());
                        let wmot = {
                            let mut e = EnvDeclBuilder::child_of(&d);
                            let (z_id, _z) = e.fresh_local(list_bool());
                            e.finish_child(e.mk_lam(
                                z_id,
                                BinderInfo::Default,
                                list_bool(),
                                list_bool(),
                            ))
                        };
                        let wcons = {
                            let mut e = EnvDeclBuilder::child_of(&d);
                            let (wh_id, wh) = e.fresh_local(bool_ty());
                            let (wt_id, wt) = e.fresh_local(list_bool());
                            let (wih_id, _wih) = e.fresh_local(list_bool());
                            let body = cons_b(gate(xh.clone(), wh), Expr::app(ih.clone(), wt));
                            let r = e.mk_lam(wih_id, BinderInfo::Default, list_bool(), body);
                            let r = e.mk_lam(wt_id, BinderInfo::Default, list_bool(), r);
                            e.finish_child(e.mk_lam(wh_id, BinderInfo::Default, bool_ty(), r))
                        };
                        let body = list_rec_type1(wmot, nil_b(), wcons, ws.clone());
                        d.finish_child(d.mk_lam(ws_id, BinderInfo::Default, list_bool(), body))
                    };
                    let r = c.mk_lam(ih_id, BinderInfo::Default, consumer.clone(), inner);
                    let r = c.mk_lam(xt_id, BinderInfo::Default, list_bool(), r);
                    c.finish_child(c.mk_lam(xh_id, BinderInfo::Default, bool_ty(), r))
                };
                let rec = list_rec_type1(motive, nil_case, cons_case, xs.clone());
                let applied = Expr::app(rec, ys.clone());
                let r = b.mk_lam(ys_id, BinderInfo::Default, list_bool(), applied);
                b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_bool(), r))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(zname),
                level_params: vec![],
                type_: llb.clone(),
                value: zip_val,
                is_reducible: true,
            })?;
        }
        Ok(())
    }

    /// The two parametric coercion identities, proved by `List.rec` on `z`:
    ///   extract_zeroext_id : ∀ z k, bvTakeLen z (bvZeroExt z k) = z
    ///   or_zero_id         : ∀ z,   bvZipOr (bvAllFalse z) z   = z
    fn register_bvc_identities(&mut self) -> Result<(), EnvError> {
        // ---- extract_zeroext_id : ∀ (z : List Bool) (k : Nat),
        //          bvTakeLen z (bvZeroExt z k) = z
        // Induction on z. nil: bvTakeLen nil (zext nil k) = nil = nil (rfl).
        // cons h t: bvTakeLen (h::t) (zext (h::t) k)
        //   = bvTakeLen (h::t) (h :: (t ++ replF k))      [zext cons-unfold]
        //   = h :: bvTakeLen t (t ++ replF k)             [takeLen cons-unfold]
        //   = h :: bvTakeLen t (zext t k)                 [defeq: zext t k = t ++ replF k]
        //   = h :: t                                       [congrArg (cons h) (ih k)]
        {
            let goal_of = |z: Expr, k: Expr| eq_list(take_len(z.clone(), zext(z.clone(), k)), z);
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (z_id, z) = b.fresh_local(list_bool());
                let (k_id, k) = b.fresh_local(nat_ty());
                let goal = goal_of(z.clone(), k.clone());
                let t = b.mk_pi(k_id, BinderInfo::Default, nat_ty(), goal);
                b.finish(b.mk_pi(z_id, BinderInfo::Default, list_bool(), t))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (z_id, z) = b.fresh_local(list_bool());
                // motive (w) = ∀ k, bvTakeLen w (bvZeroExt w k) = w
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, w) = c.fresh_local(list_bool());
                    let inner = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (k_id, k) = d.fresh_local(nat_ty());
                        d.finish_child(d.mk_pi(
                            k_id,
                            BinderInfo::Default,
                            nat_ty(),
                            goal_of(w.clone(), k),
                        ))
                    };
                    c.finish_child(c.mk_lam(w_id, BinderInfo::Default, list_bool(), inner))
                };
                // nil_case : ∀ k, bvTakeLen nil (zext nil k) = nil  = fun k => rfl nil
                let nil_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (k_id, _k) = c.fresh_local(nat_ty());
                    c.finish_child(c.mk_lam(
                        k_id,
                        BinderInfo::Default,
                        nat_ty(),
                        eq_refl_list(nil_b()),
                    ))
                };
                // cons_case : (h)(t)(ih : ∀k, takeLen t (zext t k) = t) → ∀ k, … = h::t
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (h_id, h) = c.fresh_local(bool_ty());
                    let (t_id, t) = c.fresh_local(list_bool());
                    let ih_ty = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (k_id, k) = d.fresh_local(nat_ty());
                        d.finish_child(d.mk_pi(
                            k_id,
                            BinderInfo::Default,
                            nat_ty(),
                            goal_of(t.clone(), k),
                        ))
                    };
                    let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                    let body = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (k_id, k) = d.fresh_local(nat_ty());
                        // LHS = bvTakeLen (h::t) (zext (h::t) k)
                        // reduces (defeq) to: h :: bvTakeLen t (zext t k)
                        // ih k : bvTakeLen t (zext t k) = t
                        // congrArg (cons h ·) (ih k) : h :: bvTakeLen t (zext t k) = h :: t
                        let cons_h_fn = {
                            let mut e = EnvDeclBuilder::child_of(&d);
                            let (w_id, w) = e.fresh_local(list_bool());
                            e.finish_child(e.mk_lam(
                                w_id,
                                BinderInfo::Default,
                                list_bool(),
                                cons_b(h.clone(), w),
                            ))
                        };
                        let lhs_tail = take_len(t.clone(), zext(t.clone(), k.clone()));
                        let proof = congr_arg_ll(
                            lhs_tail,
                            t.clone(),
                            cons_h_fn,
                            Expr::app(ih.clone(), k.clone()),
                        );
                        d.finish_child(d.mk_lam(k_id, BinderInfo::Default, nat_ty(), proof))
                    };
                    let r = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                    let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, bool_ty(), r))
                };
                let rec = list_rec_prop(motive, nil_case, cons_case, z.clone());
                b.finish(b.mk_lam(z_id, BinderInfo::Default, list_bool(), rec))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::EXTRACT_ZEXT_ID),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }

        // ---- bvTakeLenAppend : ∀ (s w : List Bool), bvTakeLen s (bvAppend s w) = s
        // Induction on s. nil: bvTakeLen nil (append nil w) ≡ bvTakeLen nil w ≡ nil (rfl).
        // cons h t: bvTakeLen (h::t) (append (h::t) w)
        //   ≡ bvTakeLen (h::t) (h :: append t w)   [append cons-unfold]
        //   ≡ h :: bvTakeLen t (append t w)         [takeLen cons-unfold]
        //   = h :: t                                 [congrArg (cons h ·) (ih w)]
        // Same shape as extract_zeroext_id with the suffix `w` (a free List Bool)
        // replacing `bvReplF k`; the motive quantifies over `w`.
        {
            let goal_of = |s: Expr, w: Expr| eq_list(take_len(s.clone(), app2(s.clone(), w)), s);
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (s_id, s) = b.fresh_local(list_bool());
                let (w_id, w) = b.fresh_local(list_bool());
                let goal = goal_of(s.clone(), w.clone());
                let t = b.mk_pi(w_id, BinderInfo::Default, list_bool(), goal);
                b.finish(b.mk_pi(s_id, BinderInfo::Default, list_bool(), t))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (s_id, s) = b.fresh_local(list_bool());
                // motive (u) = ∀ w, bvTakeLen u (bvAppend u w) = u
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (u_id, u) = c.fresh_local(list_bool());
                    let inner = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (w_id, w) = d.fresh_local(list_bool());
                        d.finish_child(d.mk_pi(
                            w_id,
                            BinderInfo::Default,
                            list_bool(),
                            goal_of(u.clone(), w),
                        ))
                    };
                    c.finish_child(c.mk_lam(u_id, BinderInfo::Default, list_bool(), inner))
                };
                // nil_case : ∀ w, bvTakeLen nil (append nil w) = nil  = fun w => rfl nil
                let nil_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(list_bool());
                    c.finish_child(c.mk_lam(
                        w_id,
                        BinderInfo::Default,
                        list_bool(),
                        eq_refl_list(nil_b()),
                    ))
                };
                // cons_case : (h)(t)(ih : ∀w, takeLen t (append t w) = t) → ∀ w, … = h::t
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (h_id, h) = c.fresh_local(bool_ty());
                    let (t_id, t) = c.fresh_local(list_bool());
                    let ih_ty = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (w_id, w) = d.fresh_local(list_bool());
                        d.finish_child(d.mk_pi(
                            w_id,
                            BinderInfo::Default,
                            list_bool(),
                            goal_of(t.clone(), w),
                        ))
                    };
                    let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                    let body = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (w_id, w) = d.fresh_local(list_bool());
                        let cons_h_fn = {
                            let mut e = EnvDeclBuilder::child_of(&d);
                            let (u_id, u) = e.fresh_local(list_bool());
                            e.finish_child(e.mk_lam(
                                u_id,
                                BinderInfo::Default,
                                list_bool(),
                                cons_b(h.clone(), u),
                            ))
                        };
                        let lhs_tail = take_len(t.clone(), app2(t.clone(), w.clone()));
                        let proof = congr_arg_ll(
                            lhs_tail,
                            t.clone(),
                            cons_h_fn,
                            Expr::app(ih.clone(), w.clone()),
                        );
                        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, list_bool(), proof))
                    };
                    let r = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                    let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, bool_ty(), r))
                };
                let rec = list_rec_prop(motive, nil_case, cons_case, s.clone());
                b.finish(b.mk_lam(s_id, BinderInfo::Default, list_bool(), rec))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::BV_TAKE_LEN_APPEND),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }

        // ---- or_zero_id : ∀ (z : List Bool), bvZipOr (bvAllFalse z) z = z
        // Induction on z. nil: rfl. cons h t:
        //   bvZipOr (allFalse (h::t)) (h::t) = bvZipOr (false :: allFalse t) (h::t)
        //     = (or false h) :: bvZipOr (allFalse t) t   [zipOr/allFalse cons-unfold]
        //     = h :: bvZipOr (allFalse t) t               [or false h defeq h]
        //     = h :: t                                     [congrArg (cons h) ih]
        {
            let goal_of = |z: Expr| eq_list(zip_or(all_false(z.clone()), z.clone()), z);
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (z_id, z) = b.fresh_local(list_bool());
                b.finish(b.mk_pi(z_id, BinderInfo::Default, list_bool(), goal_of(z.clone())))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (z_id, z) = b.fresh_local(list_bool());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, w) = c.fresh_local(list_bool());
                    c.finish_child(c.mk_lam(
                        w_id,
                        BinderInfo::Default,
                        list_bool(),
                        goal_of(w.clone()),
                    ))
                };
                let nil_case = eq_refl_list(nil_b());
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (h_id, h) = c.fresh_local(bool_ty());
                    let (t_id, t) = c.fresh_local(list_bool());
                    let ih_ty = goal_of(t.clone());
                    let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                    // congrArg (cons h ·) ih : h :: zipOr(allFalse t) t = h :: t
                    // and LHS reduces (defeq) to h :: zipOr(allFalse t) t.
                    let cons_h_fn = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (w_id, w) = d.fresh_local(list_bool());
                        d.finish_child(d.mk_lam(
                            w_id,
                            BinderInfo::Default,
                            list_bool(),
                            cons_b(h.clone(), w),
                        ))
                    };
                    let lhs_tail = zip_or(all_false(t.clone()), t.clone());
                    let body = congr_arg_ll(lhs_tail, t.clone(), cons_h_fn, ih);
                    let r = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                    let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, bool_ty(), r))
                };
                let rec = list_rec_prop(motive, nil_case, cons_case, z.clone());
                b.finish(b.mk_lam(z_id, BinderInfo::Default, list_bool(), rec))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::OR_ZERO_ID),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }

        // ---- add_zero_id : ∀ (y : List Bool), addRecM (bvAllFalse y) y false = y
        // (needs the #34 ripple adder addRecM — ensure it is registered first.)
        self.init_bv_inductive()?;
        // Induction on y. nil: addRecM nil nil false = nil (rfl). cons y0 ys:
        //   addRecM (allFalse (y0::ys)) (y0::ys) false
        //     = addRecM (false :: allFalse ys) (y0::ys) false        [allFalse cons-unfold]
        //     = (xor3 false y0 false) :: addRecM (allFalse ys) ys (maj false y0 false)  [addRecM cons]
        //     = y0 :: addRecM (allFalse ys) ys false                 [xor3/maj defeq]
        //     = y0 :: ys                                              [congrArg (cons y0) ih]
        {
            let add_rec_m = |x: Expr, y: Expr| {
                Expr::apps(
                    Expr::const_str(crate::bitvec_inductive::names::ADD_REC_M),
                    [x, y, bfalse()],
                )
            };
            let goal_of = |y: Expr| eq_list(add_rec_m(all_false(y.clone()), y.clone()), y);
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (y_id, y) = b.fresh_local(list_bool());
                b.finish(b.mk_pi(y_id, BinderInfo::Default, list_bool(), goal_of(y.clone())))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (y_id, y) = b.fresh_local(list_bool());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, w) = c.fresh_local(list_bool());
                    c.finish_child(c.mk_lam(
                        w_id,
                        BinderInfo::Default,
                        list_bool(),
                        goal_of(w.clone()),
                    ))
                };
                let nil_case = eq_refl_list(nil_b());
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (h_id, h) = c.fresh_local(bool_ty());
                    let (t_id, t) = c.fresh_local(list_bool());
                    let ih_ty = goal_of(t.clone());
                    let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                    // The cons-step bit-ops `xor3 false h false` / `maj false h false` are STUCK
                    // on a symbolic head h (Bool.xor recurses on its first arg). DISPATCH h via
                    // Bool.rec: at each LITERAL head the LHS reduces concretely to
                    //   cons h0 (addRecM (allFalse t) t false), proved by congrArg (cons h0 ·) ih.
                    let lhs_tail = add_rec_m(all_false(t.clone()), t.clone());
                    let mk_leaf = |h0: Expr, parent: &EnvDeclBuilder| -> Expr {
                        let cons_h_fn = {
                            let mut d = EnvDeclBuilder::child_of(parent);
                            let (w_id, w) = d.fresh_local(list_bool());
                            d.finish_child(d.mk_lam(
                                w_id,
                                BinderInfo::Default,
                                list_bool(),
                                cons_b(h0.clone(), w),
                            ))
                        };
                        congr_arg_ll(lhs_tail.clone(), t.clone(), cons_h_fn, ih.clone())
                    };
                    // motive_h h0 := addRecM (allFalse (cons h0 t)) (cons h0 t) false = cons h0 t
                    let hmot = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (h0_id, h0) = d.fresh_local(bool_ty());
                        let g = eq_list(
                            add_rec_m(
                                all_false(cons_b(h0.clone(), t.clone())),
                                cons_b(h0.clone(), t.clone()),
                            ),
                            cons_b(h0.clone(), t.clone()),
                        );
                        d.finish_child(d.mk_lam(h0_id, BinderInfo::Default, bool_ty(), g))
                    };
                    // motive eliminates into Prop (Eq is Sort 0) -> Bool.rec.{0}.
                    let body = Expr::apps(
                        Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
                        [hmot, mk_leaf(bfalse(), &c), mk_leaf(btrue(), &c), h.clone()],
                    );
                    let r = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                    let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, bool_ty(), r))
                };
                let rec = list_rec_prop(motive, nil_case, cons_case, y.clone());
                b.finish(b.mk_lam(y_id, BinderInfo::Default, list_bool(), rec))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::ADD_ZERO_ID),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }

        Ok(())
    }

    /// The Formula-mirroring datatype `Clean.BVC.BvF`:
    ///   Leaf      : List Bool → BvF
    ///   Const     : List Bool → BvF
    ///   Add       : BvF → BvF → BvF
    ///   ZeroExt   : BvF → Nat → BvF
    ///   ExtractLow: BvF → BvF → BvF      (2nd arg = the "length tag" list; eval
    ///                                     takes `bvTakeLen (eval tag) (eval e)`)
    ///   Or        : BvF → BvF → BvF
    /// The ExtractLow length is carried as a `BvF` whose eval supplies the take
    /// length (mirroring the gate's `Extract[len(z)-1:0]`, where the width is the
    /// inner operand's width) — this keeps the eval purely list-structural.
    fn register_bvf_datatype(&mut self) -> Result<(), EnvError> {
        if self.get_inductive(&Name::from_string(names::BVF)).is_some() {
            return Ok(());
        }
        let bvf = Expr::const_str(names::BVF);
        let arrow_to = |args: &[Expr]| {
            let mut r = bvf.clone();
            for a in args.iter().rev() {
                r = Expr::arrow(a.clone(), r);
            }
            r
        };
        let ctor = |name: &str, args: &[Expr]| Constructor {
            name: Name::from_string(name),
            type_: arrow_to(args),
        };
        let decl = InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string(names::BVF),
                type_: Expr::type_(),
                constructors: vec![
                    ctor("Clean.BVC.BvF.Leaf", &[list_bool()]),
                    ctor("Clean.BVC.BvF.Const", &[list_bool()]),
                    ctor("Clean.BVC.BvF.Add", &[bvf.clone(), bvf.clone()]),
                    ctor("Clean.BVC.BvF.Sub", &[bvf.clone(), bvf.clone()]),
                    ctor("Clean.BVC.BvF.And", &[bvf.clone(), bvf.clone()]),
                    ctor("Clean.BVC.BvF.Xor", &[bvf.clone(), bvf.clone()]),
                    ctor("Clean.BVC.BvF.ZeroExt", &[bvf.clone(), nat_ty()]),
                    ctor("Clean.BVC.BvF.ExtractLow", &[bvf.clone(), bvf.clone()]),
                    ctor("Clean.BVC.BvF.Or", &[bvf.clone(), bvf.clone()]),
                    ctor("Clean.BVC.BvF.Mul", &[bvf.clone(), bvf.clone()]),
                    ctor("Clean.BVC.BvF.Div", &[bvf.clone(), bvf.clone()]),
                    ctor("Clean.BVC.BvF.SDiv", &[bvf.clone(), bvf.clone()]),
                    ctor("Clean.BVC.BvF.Shl", &[bvf.clone(), bvf.clone()]),
                    ctor("Clean.BVC.BvF.LShr", &[bvf.clone(), bvf.clone()]),
                    ctor("Clean.BVC.BvF.AShr", &[bvf.clone(), bvf.clone()]),
                ],
            }],
        };
        self.add_inductive(decl)?;
        Ok(())
    }

    /// `bvfEval : BvF → List Bool`, recursing structurally. Add uses the #34
    /// machine adder `Clean.BVI.addRecM … false` (carry-in false); the coercion
    /// ops use this module's `bvZeroExt`/`bvTakeLen`/`bvZipOr`. (The coercion
    /// identities below do NOT depend on the Add semantics — that is the point.)
    fn register_bvf_eval(&mut self) -> Result<(), EnvError> {
        // Ensure the #34 adder is present (for the Add arm).
        self.init_bv_inductive()?;
        // bvMul : List Bool → List Bool → List Bool — TOTAL shift-add multiplier.
        //   bvMul a b := List.rec (fun _ => List Bool) nil
        //                  (fun a0 _ ih => addRecM (Bool.rec (bvAllFalse b) b a0)
        //                                          (cons false ih) false) a
        // Each set bit a0 of `a` (LSB-first) adds `b` to the left-shifted partial
        // product (`cons false ih`); a clear bit adds all-false. Totality is all the
        // mul coercion-identity discharge needs (the value is not load-bearing).
        {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(list_bool());
                let (bb_id, bb) = b.fresh_local(list_bool());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(list_bool());
                    c.finish_child(c.mk_lam(w_id, BinderInfo::Default, list_bool(), list_bool()))
                };
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (a0_id, a0) = c.fresh_local(bool_ty());
                    let (t_id, _t) = c.fresh_local(list_bool());
                    let (ih_id, ih) = c.fresh_local(list_bool());
                    // sel = Bool.rec.{1} (fun _ => List Bool) (bvAllFalse b) b a0  (a0 ? b : allFalse b)
                    let sel = Expr::apps(
                        Expr::const_(
                            Name::from_string("Bool.rec"),
                            vec![Level::succ(Level::zero())],
                        ),
                        [
                            {
                                let mut d = EnvDeclBuilder::child_of(&c);
                                let (w_id, _w) = d.fresh_local(bool_ty());
                                d.finish_child(d.mk_lam(
                                    w_id,
                                    BinderInfo::Default,
                                    bool_ty(),
                                    list_bool(),
                                ))
                            },
                            all_false(bb.clone()),
                            bb.clone(),
                            a0.clone(),
                        ],
                    );
                    let shifted = cons_b(bfalse(), ih);
                    let body = Expr::apps(
                        Expr::const_str(crate::bitvec_inductive::names::ADD_REC_M),
                        [sel, shifted, bfalse()],
                    );
                    let r = c.mk_lam(ih_id, BinderInfo::Default, list_bool(), body);
                    let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                    c.finish_child(c.mk_lam(a0_id, BinderInfo::Default, bool_ty(), r))
                };
                let rec = list_rec_type1(motive, nil_b(), cons_case, a.clone());
                let r = b.mk_lam(bb_id, BinderInfo::Default, list_bool(), rec);
                b.finish(b.mk_lam(a_id, BinderInfo::Default, list_bool(), r))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::BV_MUL),
                level_params: vec![],
                type_: Expr::arrow(list_bool(), Expr::arrow(list_bool(), list_bool())),
                value: val,
                is_reducible: true,
            })?;
        }
        // ── bvToNat / natToBvAux / bvDiv : FAITHFUL unsigned division ──────────
        // bvDiv delegates to kernel-native Nat.div (Lean n/0=0 = AArch64 UDIV-by-0=0),
        // so it computes REAL truncating division (no non-semantic stub). Its value is
        // not load-bearing for the gate's coercion-identity discharge (bvf_div_cong
        // cancels the shared BvF.Div node), but faithfulness keeps the substrate honest.
        {
            // bvToNat xs := List.rec (fun _ => Nat) Nat.zero
            //                 (fun x _ ih => Nat.add (x?1:0) (Nat.mul 2 ih)) xs   (LSB-first)
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (xs_id, xs) = b.fresh_local(list_bool());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(list_bool());
                    c.finish_child(c.mk_lam(w_id, BinderInfo::Default, list_bool(), nat_ty()))
                };
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (x_id, x) = c.fresh_local(bool_ty());
                    let (t_id, _t) = c.fresh_local(list_bool());
                    let (ih_id, ih) = c.fresh_local(nat_ty());
                    // boolToNat x = Bool.rec.{1} (fun _ => Nat) 0 1 x  (literals, so the
                    // native Nat.add/Nat.mul stay literal-reducible on concrete inputs).
                    let bool_to_nat = Expr::apps(
                        Expr::const_(
                            Name::from_string("Bool.rec"),
                            vec![Level::succ(Level::zero())],
                        ),
                        [
                            {
                                let mut d = EnvDeclBuilder::child_of(&c);
                                let (w_id, _w) = d.fresh_local(bool_ty());
                                d.finish_child(d.mk_lam(
                                    w_id,
                                    BinderInfo::Default,
                                    bool_ty(),
                                    nat_ty(),
                                ))
                            },
                            Expr::nat_lit(0),
                            Expr::nat_lit(1),
                            x,
                        ],
                    );
                    let body = Expr::apps(
                        Expr::const_str("Nat.add"),
                        [
                            bool_to_nat,
                            Expr::apps(Expr::const_str("Nat.mul"), [Expr::nat_lit(2), ih]),
                        ],
                    );
                    let r = c.mk_lam(ih_id, BinderInfo::Default, nat_ty(), body);
                    let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                    c.finish_child(c.mk_lam(x_id, BinderInfo::Default, bool_ty(), r))
                };
                let rec = list_rec_type1(motive, Expr::nat_lit(0), cons_case, xs.clone());
                b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_bool(), rec))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::BV_TO_NAT),
                level_params: vec![],
                type_: Expr::arrow(list_bool(), nat_ty()),
                value: val,
                is_reducible: true,
            })?;

            // natToBvAux width := Nat.rec (fun _ => Nat → List Bool)
            //                       (fun _v => nil)
            //                       (fun _n ih => fun v => cons (Nat.ble 1 (Nat.mod v 2))
            //                                                   (ih (Nat.div v 2)))
            //                       width
            let nat_to_lb = Expr::arrow(nat_ty(), list_bool());
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (w_id, w) = b.fresh_local(nat_ty());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (m_id, _m) = c.fresh_local(nat_ty());
                    c.finish_child(c.mk_lam(m_id, BinderInfo::Default, nat_ty(), nat_to_lb.clone()))
                };
                let zero_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (v_id, _v) = c.fresh_local(nat_ty());
                    c.finish_child(c.mk_lam(v_id, BinderInfo::Default, nat_ty(), nil_b()))
                };
                let succ_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (n_id, _n) = c.fresh_local(nat_ty());
                    let (ih_id, ih) = c.fresh_local(nat_to_lb.clone());
                    let inner = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (v_id, v) = d.fresh_local(nat_ty());
                        let bit = Expr::apps(
                            Expr::const_str("Nat.ble"),
                            [
                                Expr::nat_lit(1),
                                Expr::apps(
                                    Expr::const_str("Nat.mod"),
                                    [v.clone(), Expr::nat_lit(2)],
                                ),
                            ],
                        );
                        let half =
                            Expr::apps(Expr::const_str("Nat.div"), [v.clone(), Expr::nat_lit(2)]);
                        let body = cons_b(bit, Expr::app(ih.clone(), half));
                        d.finish_child(d.mk_lam(v_id, BinderInfo::Default, nat_ty(), body))
                    };
                    let r = c.mk_lam(ih_id, BinderInfo::Default, nat_to_lb.clone(), inner);
                    c.finish_child(c.mk_lam(n_id, BinderInfo::Default, nat_ty(), r))
                };
                let rec = nat_rec_type1(motive, zero_case, succ_case, w.clone());
                b.finish(b.mk_lam(w_id, BinderInfo::Default, nat_ty(), rec))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::NAT_TO_BV_AUX),
                level_params: vec![],
                type_: Expr::arrow(nat_ty(), nat_to_lb.clone()),
                value: val,
                is_reducible: true,
            })?;

            // bvDiv a b := natToBvAux (len a) (Nat.div (bvToNat a) (bvToNat b))
            //   len a inlined as List.rec (fun _ => Nat) Nat.zero (fun _ _ ih => Nat.succ ih) a
            //   (avoids depending on bvLen, which registers after register_bvf_eval).
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(list_bool());
                let (bb_id, bb) = b.fresh_local(list_bool());
                let len_a = {
                    let motive = {
                        let mut c = EnvDeclBuilder::child_of(&b);
                        let (w_id, _w) = c.fresh_local(list_bool());
                        c.finish_child(c.mk_lam(w_id, BinderInfo::Default, list_bool(), nat_ty()))
                    };
                    let cons_case = {
                        let mut c = EnvDeclBuilder::child_of(&b);
                        let (x_id, _x) = c.fresh_local(bool_ty());
                        let (t_id, _t) = c.fresh_local(list_bool());
                        let (ih_id, ih) = c.fresh_local(nat_ty());
                        let body = Expr::app(Expr::const_str("Nat.succ"), ih);
                        let r = c.mk_lam(ih_id, BinderInfo::Default, nat_ty(), body);
                        let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                        c.finish_child(c.mk_lam(x_id, BinderInfo::Default, bool_ty(), r))
                    };
                    list_rec_type1(motive, Expr::const_str("Nat.zero"), cons_case, a.clone())
                };
                let to_nat = |x: Expr| Expr::app(Expr::const_str(names::BV_TO_NAT), x);
                let q = Expr::apps(
                    Expr::const_str("Nat.div"),
                    [to_nat(a.clone()), to_nat(bb.clone())],
                );
                let body = Expr::apps(Expr::const_str(names::NAT_TO_BV_AUX), [len_a, q]);
                let r = b.mk_lam(bb_id, BinderInfo::Default, list_bool(), body);
                b.finish(b.mk_lam(a_id, BinderInfo::Default, list_bool(), r))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::BV_DIV),
                level_params: vec![],
                type_: Expr::arrow(list_bool(), Expr::arrow(list_bool(), list_bool())),
                value: val,
                is_reducible: true,
            })?;

            // ── bvNeg / bvAbs / bvSDiv : FAITHFUL signed division (sign-magnitude) ─────
            // bvNeg x := addRecM (bvNot x) (bvAllFalse (bvNot x)) true   (= ~x + 1).
            {
                let val = {
                    let mut b = EnvDeclBuilder::new();
                    let (x_id, x) = b.fresh_local(list_bool());
                    let notx = Expr::app(Expr::const_str(names::BV_NOT), x);
                    let af = Expr::app(Expr::const_str(names::ALL_FALSE), notx.clone());
                    let body = Expr::apps(
                        Expr::const_str(crate::bitvec_inductive::names::ADD_REC_M),
                        [notx, af, Expr::const_str("Bool.true")],
                    );
                    b.finish(b.mk_lam(x_id, BinderInfo::Default, list_bool(), body))
                };
                self.add_decl_if_absent(Declaration::Definition {
                    name: Name::from_string(names::BV_NEG),
                    level_params: vec![],
                    type_: Expr::arrow(list_bool(), list_bool()),
                    value: val,
                    is_reducible: true,
                })?;
            }
            // bvAbs x := bvIteVal (bvLastBit x) (bvNeg x) x   (MSB set -> negate; else x).
            {
                let val = {
                    let mut b = EnvDeclBuilder::new();
                    let (x_id, x) = b.fresh_local(list_bool());
                    let msb = Expr::app(Expr::const_str(names::BV_LAST_BIT), x.clone());
                    let negx = Expr::app(Expr::const_str(names::BV_NEG), x.clone());
                    let body = Expr::apps(Expr::const_str(names::BV_ITE_VAL), [msb, negx, x]);
                    b.finish(b.mk_lam(x_id, BinderInfo::Default, list_bool(), body))
                };
                self.add_decl_if_absent(Declaration::Definition {
                    name: Name::from_string(names::BV_ABS),
                    level_params: vec![],
                    type_: Expr::arrow(list_bool(), list_bool()),
                    value: val,
                    is_reducible: true,
                })?;
            }
            // bvSDiv a b := bvIteVal (xor (bvLastBit a)(bvLastBit b)) (bvNeg q) q,
            //   q = bvDiv (bvAbs a)(bvAbs b)   (sign-magnitude truncating div = AArch64 SDIV).
            {
                let val = {
                    let mut b = EnvDeclBuilder::new();
                    let (a_id, a) = b.fresh_local(list_bool());
                    let (bb_id, bb) = b.fresh_local(list_bool());
                    let abs = |e: Expr| Expr::app(Expr::const_str(names::BV_ABS), e);
                    let lastbit = |e: Expr| Expr::app(Expr::const_str(names::BV_LAST_BIT), e);
                    let q = Expr::apps(
                        Expr::const_str(names::BV_DIV),
                        [abs(a.clone()), abs(bb.clone())],
                    );
                    let sign = Expr::apps(
                        Expr::const_str("Bool.xor"),
                        [lastbit(a.clone()), lastbit(bb.clone())],
                    );
                    let negq = Expr::app(Expr::const_str(names::BV_NEG), q.clone());
                    let body = Expr::apps(Expr::const_str(names::BV_ITE_VAL), [sign, negq, q]);
                    let r = b.mk_lam(bb_id, BinderInfo::Default, list_bool(), body);
                    b.finish(b.mk_lam(a_id, BinderInfo::Default, list_bool(), r))
                };
                self.add_decl_if_absent(Declaration::Definition {
                    name: Name::from_string(names::BV_SDIV),
                    level_params: vec![],
                    type_: Expr::arrow(list_bool(), Expr::arrow(list_bool(), list_bool())),
                    value: val,
                    is_reducible: true,
                })?;
            }

            // ── bvShl / bvLShr / bvAShr : FAITHFUL shifts (AXIOM-FREE: Nat.mul/div + 2^n) ──
            // Nat.shiftLeft/Right are NATIVE-only (undeclared -> they appear as AXIOMS in the
            // bvfEval closure), so shift by 2^n via DECLARED Nat.mul / Nat.div instead.
            // bvTwoPow k := Nat.rec (fun _ => Nat) 1 (fun _ ih => Nat.mul 2 ih) k   (= 2^k)
            {
                let val = {
                    let mut b = EnvDeclBuilder::new();
                    let (k_id, k) = b.fresh_local(nat_ty());
                    let motive = {
                        let mut c = EnvDeclBuilder::child_of(&b);
                        let (w_id, _w) = c.fresh_local(nat_ty());
                        c.finish_child(c.mk_lam(w_id, BinderInfo::Default, nat_ty(), nat_ty()))
                    };
                    let succ_case = {
                        let mut c = EnvDeclBuilder::child_of(&b);
                        let (n_id, _n) = c.fresh_local(nat_ty());
                        let (ih_id, ih) = c.fresh_local(nat_ty());
                        let body = Expr::apps(Expr::const_str("Nat.mul"), [Expr::nat_lit(2), ih]);
                        let r = c.mk_lam(ih_id, BinderInfo::Default, nat_ty(), body);
                        c.finish_child(c.mk_lam(n_id, BinderInfo::Default, nat_ty(), r))
                    };
                    let rec = nat_rec_type1(motive, Expr::nat_lit(1), succ_case, k.clone());
                    b.finish(b.mk_lam(k_id, BinderInfo::Default, nat_ty(), rec))
                };
                self.add_decl_if_absent(Declaration::Definition {
                    name: Name::from_string(names::BV_TWO_POW),
                    level_params: vec![],
                    type_: Expr::arrow(nat_ty(), nat_ty()),
                    value: val,
                    is_reducible: true,
                })?;
            }
            // bvShl a n  := natToBvAux (bvLen a) (Nat.mul (bvToNat a) (bvTwoPow (bvToNat n)))
            // bvLShr a n := natToBvAux (bvLen a) (Nat.div (bvToNat a) (bvTwoPow (bvToNat n)))
            for (nm, is_left) in [(names::BV_SHL, true), (names::BV_LSHR, false)] {
                let val = {
                    let mut b = EnvDeclBuilder::new();
                    let (a_id, a) = b.fresh_local(list_bool());
                    let (n_id, n) = b.fresh_local(list_bool());
                    let to_nat = |x: Expr| Expr::app(Expr::const_str(names::BV_TO_NAT), x);
                    let len_a = Expr::app(Expr::const_str(names::BV_LEN), a.clone());
                    let two_pow_n =
                        Expr::app(Expr::const_str(names::BV_TWO_POW), to_nat(n.clone()));
                    let natop = if is_left { "Nat.mul" } else { "Nat.div" };
                    let shifted =
                        Expr::apps(Expr::const_str(natop), [to_nat(a.clone()), two_pow_n]);
                    let body = Expr::apps(Expr::const_str(names::NAT_TO_BV_AUX), [len_a, shifted]);
                    let r = b.mk_lam(n_id, BinderInfo::Default, list_bool(), body);
                    b.finish(b.mk_lam(a_id, BinderInfo::Default, list_bool(), r))
                };
                self.add_decl_if_absent(Declaration::Definition {
                    name: Name::from_string(nm),
                    level_params: vec![],
                    type_: Expr::arrow(list_bool(), Expr::arrow(list_bool(), list_bool())),
                    value: val,
                    is_reducible: true,
                })?;
            }
            // bvAShr a n := bvIteVal (bvLastBit a) (bvNot (bvLShr (bvNot a) n)) (bvLShr a n)
            //   (negative a -> complement, lshr, complement = sign-fill; non-negative -> lshr).
            {
                let val = {
                    let mut b = EnvDeclBuilder::new();
                    let (a_id, a) = b.fresh_local(list_bool());
                    let (n_id, n) = b.fresh_local(list_bool());
                    let not = |e: Expr| Expr::app(Expr::const_str(names::BV_NOT), e);
                    let lshr =
                        |x: Expr, y: Expr| Expr::apps(Expr::const_str(names::BV_LSHR), [x, y]);
                    let msb = Expr::app(Expr::const_str(names::BV_LAST_BIT), a.clone());
                    let neg_branch = not(lshr(not(a.clone()), n.clone()));
                    let pos_branch = lshr(a.clone(), n.clone());
                    let body = Expr::apps(
                        Expr::const_str(names::BV_ITE_VAL),
                        [msb, neg_branch, pos_branch],
                    );
                    let r = b.mk_lam(n_id, BinderInfo::Default, list_bool(), body);
                    b.finish(b.mk_lam(a_id, BinderInfo::Default, list_bool(), r))
                };
                self.add_decl_if_absent(Declaration::Definition {
                    name: Name::from_string(names::BV_ASHR),
                    level_params: vec![],
                    type_: Expr::arrow(list_bool(), Expr::arrow(list_bool(), list_bool())),
                    value: val,
                    is_reducible: true,
                })?;
            }
        }
        let bvf = Expr::const_str(names::BVF);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(bvf.clone());
            // motive : BvF → Sort 1 = fun _ => List Bool
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(bvf.clone());
                c.finish_child(c.mk_lam(w_id, BinderInfo::Default, bvf.clone(), list_bool()))
            };
            // Leaf l ↦ l ; Const l ↦ l
            let leaf_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (l_id, l) = c.fresh_local(list_bool());
                c.finish_child(c.mk_lam(l_id, BinderInfo::Default, list_bool(), l))
            };
            let const_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (l_id, l) = c.fresh_local(list_bool());
                c.finish_child(c.mk_lam(l_id, BinderInfo::Default, list_bool(), l))
            };
            // Add a b (with IH ea eb : List Bool) ↦ addRecM ea eb false
            let add_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, _a) = c.fresh_local(bvf.clone());
                let (b2_id, _b2) = c.fresh_local(bvf.clone());
                let (ea_id, ea) = c.fresh_local(list_bool());
                let (eb_id, eb) = c.fresh_local(list_bool());
                let body = Expr::apps(
                    Expr::const_str(crate::bitvec_inductive::names::ADD_REC_M),
                    [ea, eb, bfalse()],
                );
                let r = c.mk_lam(eb_id, BinderInfo::Default, list_bool(), body);
                let r = c.mk_lam(ea_id, BinderInfo::Default, list_bool(), r);
                let r = c.mk_lam(b2_id, BinderInfo::Default, bvf.clone(), r);
                c.finish_child(c.mk_lam(a_id, BinderInfo::Default, bvf.clone(), r))
            };
            // Sub a b (IH ea eb : List Bool) ↦ addRecM ea (bvNot eb) true
            //   (two's-complement subtract a + ¬b + 1; the #34 machine adder + bvNot).
            let sub_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, _a) = c.fresh_local(bvf.clone());
                let (b2_id, _b2) = c.fresh_local(bvf.clone());
                let (ea_id, ea) = c.fresh_local(list_bool());
                let (eb_id, eb) = c.fresh_local(list_bool());
                let body = Expr::apps(
                    Expr::const_str(crate::bitvec_inductive::names::ADD_REC_M),
                    [
                        ea,
                        Expr::app(Expr::const_str(names::BV_NOT), eb),
                        Expr::const_str("Bool.true"),
                    ],
                );
                let r = c.mk_lam(eb_id, BinderInfo::Default, list_bool(), body);
                let r = c.mk_lam(ea_id, BinderInfo::Default, list_bool(), r);
                let r = c.mk_lam(b2_id, BinderInfo::Default, bvf.clone(), r);
                c.finish_child(c.mk_lam(a_id, BinderInfo::Default, bvf.clone(), r))
            };
            // And/Xor a b (IH ea eb) ↦ bvZipAnd/bvZipXor ea eb (bare per-bit zip).
            let zip_case = |zname: &str| {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, _a) = c.fresh_local(bvf.clone());
                let (b2_id, _b2) = c.fresh_local(bvf.clone());
                let (ea_id, ea) = c.fresh_local(list_bool());
                let (eb_id, eb) = c.fresh_local(list_bool());
                let body = Expr::apps(Expr::const_str(zname), [ea, eb]);
                let r = c.mk_lam(eb_id, BinderInfo::Default, list_bool(), body);
                let r = c.mk_lam(ea_id, BinderInfo::Default, list_bool(), r);
                let r = c.mk_lam(b2_id, BinderInfo::Default, bvf.clone(), r);
                c.finish_child(c.mk_lam(a_id, BinderInfo::Default, bvf.clone(), r))
            };
            let and_case = zip_case(names::ZIP_AND);
            let xor_case = zip_case(names::ZIP_XOR);
            // ZeroExt e k (IH ee : List Bool) ↦ bvZeroExt ee k
            let zext_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (e2_id, _e2) = c.fresh_local(bvf.clone());
                let (k_id, k) = c.fresh_local(nat_ty());
                let (ee_id, ee) = c.fresh_local(list_bool());
                let body = zext(ee, k.clone());
                let r = c.mk_lam(ee_id, BinderInfo::Default, list_bool(), body);
                let r = c.mk_lam(k_id, BinderInfo::Default, nat_ty(), r);
                c.finish_child(c.mk_lam(e2_id, BinderInfo::Default, bvf.clone(), r))
            };
            // ExtractLow e tag (IH ee etag : List Bool) ↦ bvTakeLen etag ee
            let extract_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (e2_id, _e2) = c.fresh_local(bvf.clone());
                let (tag_id, _tag) = c.fresh_local(bvf.clone());
                let (ee_id, ee) = c.fresh_local(list_bool());
                let (etag_id, etag) = c.fresh_local(list_bool());
                let body = take_len(etag, ee);
                let r = c.mk_lam(etag_id, BinderInfo::Default, list_bool(), body);
                let r = c.mk_lam(ee_id, BinderInfo::Default, list_bool(), r);
                let r = c.mk_lam(tag_id, BinderInfo::Default, bvf.clone(), r);
                c.finish_child(c.mk_lam(e2_id, BinderInfo::Default, bvf.clone(), r))
            };
            // Or a b (IH ea eb) ↦ bvZipOr ea eb
            let or_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, _a) = c.fresh_local(bvf.clone());
                let (b2_id, _b2) = c.fresh_local(bvf.clone());
                let (ea_id, ea) = c.fresh_local(list_bool());
                let (eb_id, eb) = c.fresh_local(list_bool());
                let body = zip_or(ea, eb);
                let r = c.mk_lam(eb_id, BinderInfo::Default, list_bool(), body);
                let r = c.mk_lam(ea_id, BinderInfo::Default, list_bool(), r);
                let r = c.mk_lam(b2_id, BinderInfo::Default, bvf.clone(), r);
                c.finish_child(c.mk_lam(a_id, BinderInfo::Default, bvf.clone(), r))
            };
            // Mul a b (IH ea eb : List Bool) ↦ bvMul ea eb (TOTAL shift-add multiplier).
            let mul_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, _a) = c.fresh_local(bvf.clone());
                let (b2_id, _b2) = c.fresh_local(bvf.clone());
                let (ea_id, ea) = c.fresh_local(list_bool());
                let (eb_id, eb) = c.fresh_local(list_bool());
                let body = Expr::apps(Expr::const_str(names::BV_MUL), [ea, eb]);
                let r = c.mk_lam(eb_id, BinderInfo::Default, list_bool(), body);
                let r = c.mk_lam(ea_id, BinderInfo::Default, list_bool(), r);
                let r = c.mk_lam(b2_id, BinderInfo::Default, bvf.clone(), r);
                c.finish_child(c.mk_lam(a_id, BinderInfo::Default, bvf.clone(), r))
            };
            // Div a b (IH ea eb : List Bool) ↦ bvDiv ea eb (TOTAL faithful unsigned division).
            let div_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, _a) = c.fresh_local(bvf.clone());
                let (b2_id, _b2) = c.fresh_local(bvf.clone());
                let (ea_id, ea) = c.fresh_local(list_bool());
                let (eb_id, eb) = c.fresh_local(list_bool());
                let body = Expr::apps(Expr::const_str(names::BV_DIV), [ea, eb]);
                let r = c.mk_lam(eb_id, BinderInfo::Default, list_bool(), body);
                let r = c.mk_lam(ea_id, BinderInfo::Default, list_bool(), r);
                let r = c.mk_lam(b2_id, BinderInfo::Default, bvf.clone(), r);
                c.finish_child(c.mk_lam(a_id, BinderInfo::Default, bvf.clone(), r))
            };
            // SDiv a b (IH ea eb : List Bool) ↦ bvSDiv ea eb (TOTAL faithful signed division).
            let sdiv_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, _a) = c.fresh_local(bvf.clone());
                let (b2_id, _b2) = c.fresh_local(bvf.clone());
                let (ea_id, ea) = c.fresh_local(list_bool());
                let (eb_id, eb) = c.fresh_local(list_bool());
                let body = Expr::apps(Expr::const_str(names::BV_SDIV), [ea, eb]);
                let r = c.mk_lam(eb_id, BinderInfo::Default, list_bool(), body);
                let r = c.mk_lam(ea_id, BinderInfo::Default, list_bool(), r);
                let r = c.mk_lam(b2_id, BinderInfo::Default, bvf.clone(), r);
                c.finish_child(c.mk_lam(a_id, BinderInfo::Default, bvf.clone(), r))
            };
            // Shl/LShr/AShr a b (IH ea eb) ↦ bvShl/bvLShr/bvAShr ea eb (binary, like sdiv).
            let bin_shift_case = |opname: &str| {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, _a) = c.fresh_local(bvf.clone());
                let (b2_id, _b2) = c.fresh_local(bvf.clone());
                let (ea_id, ea) = c.fresh_local(list_bool());
                let (eb_id, eb) = c.fresh_local(list_bool());
                let body = Expr::apps(Expr::const_str(opname), [ea, eb]);
                let r = c.mk_lam(eb_id, BinderInfo::Default, list_bool(), body);
                let r = c.mk_lam(ea_id, BinderInfo::Default, list_bool(), r);
                let r = c.mk_lam(b2_id, BinderInfo::Default, bvf.clone(), r);
                c.finish_child(c.mk_lam(a_id, BinderInfo::Default, bvf.clone(), r))
            };
            let shl_case = bin_shift_case(names::BV_SHL);
            let lshr_case = bin_shift_case(names::BV_LSHR);
            let ashr_case = bin_shift_case(names::BV_ASHR);
            // @BvF.rec.{1} (motive := fun _ => List Bool) leaf const add sub and xor zext extract or mul div sdiv shl lshr ashr e
            let rec = Expr::apps(
                Expr::const_(
                    Name::from_string(&format!("{}.rec", names::BVF)),
                    vec![Level::succ(Level::zero())],
                ),
                [
                    motive,
                    leaf_case,
                    const_case,
                    add_case,
                    sub_case,
                    and_case,
                    xor_case,
                    zext_case,
                    extract_case,
                    or_case,
                    mul_case,
                    div_case,
                    sdiv_case,
                    shl_case,
                    lshr_case,
                    ashr_case,
                    e.clone(),
                ],
            );
            b.finish(b.mk_lam(e_id, BinderInfo::Default, bvf.clone(), rec))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::BVF_EVAL),
            level_params: vec![],
            type_: Expr::arrow(bvf, list_bool()),
            value,
            is_reducible: true,
        })?;
        Ok(())
    }

    /// Lift the coercion identities to the `bvfEval` embedding:
    ///   bvf_extract_zeroext_id : ∀ (e : BvF) (k : Nat),
    ///       bvfEval (ExtractLow (ZeroExt e k) e) = bvfEval e
    ///     (the ExtractLow length tag is `e` itself — `bvTakeLen (eval e) (eval (ZeroExt e k))`
    ///      = bvTakeLen (eval e) (bvZeroExt (eval e) k) = eval e, by extract_zeroext_id.)
    ///   bvf_or_zero_id : ∀ (e : BvF),
    ///       bvfEval (Or (Const (bvAllFalse (bvfEval e))) e) = bvfEval e
    fn register_bvf_identities(&mut self) -> Result<(), EnvError> {
        let bvf = Expr::const_str(names::BVF);
        let eval = |e: Expr| Expr::app(Expr::const_str(names::BVF_EVAL), e);
        let mk = |ctor: &str, args: Vec<Expr>| Expr::apps(Expr::const_str(ctor), args);

        // bvf_extract_zeroext_id
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (e_id, e) = b.fresh_local(bvf.clone());
                let (k_id, k) = b.fresh_local(nat_ty());
                let lhs_f = mk(
                    "Clean.BVC.BvF.ExtractLow",
                    vec![
                        mk("Clean.BVC.BvF.ZeroExt", vec![e.clone(), k.clone()]),
                        e.clone(),
                    ],
                );
                let goal = eq_list(eval(lhs_f), eval(e.clone()));
                let t = b.mk_pi(k_id, BinderInfo::Default, nat_ty(), goal);
                b.finish(b.mk_pi(e_id, BinderInfo::Default, bvf.clone(), t))
            };
            // value: fun e k => extract_zeroext_id (bvfEval e) k
            //   extract_zeroext_id (eval e) k : bvTakeLen (eval e) (bvZeroExt (eval e) k) = eval e
            //   and the LHS bvfEval(ExtractLow (ZeroExt e k) e) reduces (defeq) to exactly that.
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (e_id, e) = b.fresh_local(bvf.clone());
                let (k_id, k) = b.fresh_local(nat_ty());
                let proof = Expr::apps(
                    Expr::const_str(names::EXTRACT_ZEXT_ID),
                    [eval(e.clone()), k.clone()],
                );
                let r = b.mk_lam(k_id, BinderInfo::Default, nat_ty(), proof);
                b.finish(b.mk_lam(e_id, BinderInfo::Default, bvf.clone(), r))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::BVF_EXTRACT_ZEXT_ID),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }

        // bvf_or_zero_id
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (e_id, e) = b.fresh_local(bvf.clone());
                let lhs_f = mk(
                    "Clean.BVC.BvF.Or",
                    vec![
                        mk("Clean.BVC.BvF.Const", vec![all_false(eval(e.clone()))]),
                        e.clone(),
                    ],
                );
                let goal = eq_list(eval(lhs_f), eval(e.clone()));
                b.finish(b.mk_pi(e_id, BinderInfo::Default, bvf.clone(), goal))
            };
            // value: fun e => or_zero_id (bvfEval e)
            //   or_zero_id (eval e) : bvZipOr (bvAllFalse (eval e)) (eval e) = eval e
            //   and bvfEval(Or (Const (allFalse (eval e))) e) reduces (defeq) to exactly that.
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (e_id, e) = b.fresh_local(bvf.clone());
                let proof = Expr::app(Expr::const_str(names::OR_ZERO_ID), eval(e.clone()));
                b.finish(b.mk_lam(e_id, BinderInfo::Default, bvf.clone(), proof))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::BVF_OR_ZERO_ID),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }

        // bvf_add_zero_id — the bvfEval lift of add_zero_id (mirrors bvf_or_zero_id).
        //   ∀ e, bvfEval (Add (Const (allFalse (eval e))) e) = bvfEval e
        // bvfEval(Add (Const z) e) reduces (defeq) to addRecM z (eval e) false; with
        // z = allFalse(eval e) that is exactly `add_zero_id (eval e)`. Strips the
        // AArch64 `madd Wd,Wn,Wm,WZR` (= BvAdd(0,mul)) wrapper the IR BvMul lacks.
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (e_id, e) = b.fresh_local(bvf.clone());
                let lhs_f = mk(
                    "Clean.BVC.BvF.Add",
                    vec![
                        mk("Clean.BVC.BvF.Const", vec![all_false(eval(e.clone()))]),
                        e.clone(),
                    ],
                );
                let goal = eq_list(eval(lhs_f), eval(e.clone()));
                b.finish(b.mk_pi(e_id, BinderInfo::Default, bvf.clone(), goal))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (e_id, e) = b.fresh_local(bvf.clone());
                let proof = Expr::app(Expr::const_str(names::ADD_ZERO_ID), eval(e.clone()));
                b.finish(b.mk_lam(e_id, BinderInfo::Default, bvf.clone(), proof))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::BVF_ADD_ZERO_ID),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }

        // bvf_wrapper_id — THE COMPOSED GATE-SHAPE DISCHARGE.
        //   W(e,k) := ExtractLow( ZeroExt( Or(Const (allFalse (eval e)), e), k ), e )
        //   goal:  ∀ e k, bvfEval (W e k) = bvfEval e
        // bvfEval(W e k) reduces (defeq) to
        //   bvTakeLen (eval e) (bvZeroExt (bvZipOr (allFalse (eval e)) (eval e)) k)
        // Chain:
        //   (1) or_zero_id (eval e) : bvZipOr (allFalse (eval e)) (eval e) = eval e
        //   (2) congrArg (fun w => bvTakeLen (eval e) (bvZeroExt w k)) (1)
        //         : bvTakeLen (eval e) (bvZeroExt OR k) = bvTakeLen (eval e) (bvZeroExt (eval e) k)
        //   (3) extract_zeroext_id (eval e) k
        //         : bvTakeLen (eval e) (bvZeroExt (eval e) k) = eval e
        //   Eq.trans (2) (3) : goal.
        {
            let wrapper = |e: Expr, k: Expr| {
                mk(
                    "Clean.BVC.BvF.ExtractLow",
                    vec![
                        mk(
                            "Clean.BVC.BvF.ZeroExt",
                            vec![
                                mk(
                                    "Clean.BVC.BvF.Or",
                                    vec![
                                        mk("Clean.BVC.BvF.Const", vec![all_false(eval(e.clone()))]),
                                        e.clone(),
                                    ],
                                ),
                                k,
                            ],
                        ),
                        e,
                    ],
                )
            };
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (e_id, e) = b.fresh_local(bvf.clone());
                let (k_id, k) = b.fresh_local(nat_ty());
                let goal = eq_list(eval(wrapper(e.clone(), k.clone())), eval(e.clone()));
                let t = b.mk_pi(k_id, BinderInfo::Default, nat_ty(), goal);
                b.finish(b.mk_pi(e_id, BinderInfo::Default, bvf.clone(), t))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (e_id, e) = b.fresh_local(bvf.clone());
                let (k_id, k) = b.fresh_local(nat_ty());
                let ev = eval(e.clone());
                let or_term = zip_or(all_false(ev.clone()), ev.clone());
                // (1)
                let or_eq = Expr::app(Expr::const_str(names::OR_ZERO_ID), ev.clone());
                // (2) congrArg (fun w => bvTakeLen ev (bvZeroExt w k)) or_eq
                let cong_fn = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, w) = c.fresh_local(list_bool());
                    let body = take_len(ev.clone(), zext(w, k.clone()));
                    c.finish_child(c.mk_lam(w_id, BinderInfo::Default, list_bool(), body))
                };
                let step2 = congr_arg_ll(or_term.clone(), ev.clone(), cong_fn, or_eq);
                // (3) extract_zeroext_id ev k
                let step3 = Expr::apps(
                    Expr::const_str(names::EXTRACT_ZEXT_ID),
                    [ev.clone(), k.clone()],
                );
                // chain: bvTakeLen ev (bvZeroExt OR k) = bvTakeLen ev (bvZeroExt ev k) = ev
                let a = take_len(ev.clone(), zext(or_term, k.clone()));
                let bmid = take_len(ev.clone(), zext(ev.clone(), k.clone()));
                let proof = eq_trans_list(a, bmid, ev, step2, step3);
                let r = b.mk_lam(k_id, BinderInfo::Default, nat_ty(), proof);
                b.finish(b.mk_lam(e_id, BinderInfo::Default, bvf.clone(), r))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::BVF_WRAPPER_ID),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }

        // bvf_add_cong — the bvfEval-headed Add-congruence (B2b-positive keystone).
        //   ∀ (a a' b b' : BvF), bvfEval a = bvfEval a' → bvfEval b = bvfEval b'
        //       → bvfEval (Add a b) = bvfEval (Add a' b')
        // bvfEval(Add x y) reduces (defeq) to addRecM (eval x) (eval y) false, so the
        // proof is two congrArgs over addRecM composed by Eq.trans; the kernel checks
        // it against the bvfEval-headed goal by defeq (BvF.rec ι + beta).
        {
            let add = |x: Expr, y: Expr| mk("Clean.BVC.BvF.Add", vec![x, y]);
            let add_rec_m = |x: Expr, y: Expr| {
                Expr::apps(
                    Expr::const_str(crate::bitvec_inductive::names::ADD_REC_M),
                    [x, y, bfalse()],
                )
            };
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(bvf.clone());
                let (ap_id, ap) = b.fresh_local(bvf.clone());
                let (bb_id, bb) = b.fresh_local(bvf.clone());
                let (bp_id, bp) = b.fresh_local(bvf.clone());
                let ha_ty = eq_list(eval(a.clone()), eval(ap.clone()));
                let hb_ty = eq_list(eval(bb.clone()), eval(bp.clone()));
                let (ha_id, _ha) = b.fresh_local(ha_ty.clone());
                let (hb_id, _hb) = b.fresh_local(hb_ty.clone());
                let concl = eq_list(
                    eval(add(a.clone(), bb.clone())),
                    eval(add(ap.clone(), bp.clone())),
                );
                let t = b.mk_pi(hb_id, BinderInfo::Default, hb_ty, concl);
                let t = b.mk_pi(ha_id, BinderInfo::Default, ha_ty, t);
                let t = b.mk_pi(bp_id, BinderInfo::Default, bvf.clone(), t);
                let t = b.mk_pi(bb_id, BinderInfo::Default, bvf.clone(), t);
                let t = b.mk_pi(ap_id, BinderInfo::Default, bvf.clone(), t);
                b.finish(b.mk_pi(a_id, BinderInfo::Default, bvf.clone(), t))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(bvf.clone());
                let (ap_id, ap) = b.fresh_local(bvf.clone());
                let (bb_id, bb) = b.fresh_local(bvf.clone());
                let (bp_id, bp) = b.fresh_local(bvf.clone());
                let ha_ty = eq_list(eval(a.clone()), eval(ap.clone()));
                let hb_ty = eq_list(eval(bb.clone()), eval(bp.clone()));
                let (ha_id, ha) = b.fresh_local(ha_ty.clone());
                let (hb_id, hb) = b.fresh_local(hb_ty.clone());
                let ea = eval(a.clone());
                let ea_p = eval(ap.clone());
                let eb = eval(bb.clone());
                let eb_p = eval(bp.clone());
                // Proof by two `Eq.subst`s over the REDUCED `addRecM` form (NO
                // congrArg lambda-redex — each subst motive body is `addRecM l _ false`
                // directly, so the inferred type is goal-shaped and the kernel def-eqs
                // it to the bvfEval-headed goal by BvF.rec ι, no stuck beta-redex).
                //   base : addRecM ea eb false = addRecM ea eb false      (Eq.refl)
                //   sB   : addRecM ea eb false = addRecM ea eb_p false     (subst b via hb)
                //   sA   : addRecM ea eb false = addRecM ea_p eb_p false   (subst a via ha)
                let eq_subst = |motive: Expr, a: Expr, bb2: Expr, h: Expr, m: Expr| {
                    Expr::apps(
                        Expr::const_(
                            Name::from_string("Eq.subst"),
                            vec![Level::succ(Level::zero())],
                        ),
                        [list_bool(), motive, a, bb2, h, m],
                    )
                };
                let base = Expr::apps(
                    Expr::const_(
                        Name::from_string("Eq.refl"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [list_bool(), add_rec_m(ea.clone(), eb.clone())],
                );
                // motive_b l := Eq (addRecM ea eb false) (addRecM ea l false)
                let motive_b = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (l_id, l) = c.fresh_local(list_bool());
                    let body = eq_list(add_rec_m(ea.clone(), eb.clone()), add_rec_m(ea.clone(), l));
                    c.finish_child(c.mk_lam(l_id, BinderInfo::Default, list_bool(), body))
                };
                let s_b = eq_subst(motive_b, eb.clone(), eb_p.clone(), hb, base);
                // motive_a l := Eq (addRecM ea eb false) (addRecM l eb_p false)
                let motive_a = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (l_id, l) = c.fresh_local(list_bool());
                    let body = eq_list(
                        add_rec_m(ea.clone(), eb.clone()),
                        add_rec_m(l, eb_p.clone()),
                    );
                    c.finish_child(c.mk_lam(l_id, BinderInfo::Default, list_bool(), body))
                };
                let proof = eq_subst(motive_a, ea.clone(), ea_p.clone(), ha, s_b);
                let r = b.mk_lam(hb_id, BinderInfo::Default, hb_ty, proof);
                let r = b.mk_lam(ha_id, BinderInfo::Default, ha_ty, r);
                let r = b.mk_lam(bp_id, BinderInfo::Default, bvf.clone(), r);
                let r = b.mk_lam(bb_id, BinderInfo::Default, bvf.clone(), r);
                let r = b.mk_lam(ap_id, BinderInfo::Default, bvf.clone(), r);
                b.finish(b.mk_lam(a_id, BinderInfo::Default, bvf.clone(), r))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::BVF_ADD_CONG),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }

        // bvf_sub_cong — the bvfEval-headed Sub-congruence (SUB-op, B4 wiring).
        //   ∀ (a a' b b' : BvF), bvfEval a = bvfEval a' → bvfEval b = bvfEval b'
        //       → bvfEval (Sub a b) = bvfEval (Sub a' b')
        // bvfEval(Sub x y) reduces (defeq) to addRecM (eval x) (bvNot (eval y)) true.
        // Same Eq.subst (goal-shaped motive, no congrArg redex) structure as add;
        // the 2nd-operand substitution goes INSIDE bvNot.
        {
            let sub = |x: Expr, y: Expr| mk("Clean.BVC.BvF.Sub", vec![x, y]);
            let sub_model = |x: Expr, y: Expr| {
                Expr::apps(
                    Expr::const_str(crate::bitvec_inductive::names::ADD_REC_M),
                    [
                        x,
                        Expr::app(Expr::const_str(names::BV_NOT), y),
                        Expr::const_str("Bool.true"),
                    ],
                )
            };
            let eq_subst = |motive: Expr, a: Expr, bb2: Expr, h: Expr, m: Expr| {
                Expr::apps(
                    Expr::const_(
                        Name::from_string("Eq.subst"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [list_bool(), motive, a, bb2, h, m],
                )
            };
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(bvf.clone());
                let (ap_id, ap) = b.fresh_local(bvf.clone());
                let (bb_id, bb) = b.fresh_local(bvf.clone());
                let (bp_id, bp) = b.fresh_local(bvf.clone());
                let ha_ty = eq_list(eval(a.clone()), eval(ap.clone()));
                let hb_ty = eq_list(eval(bb.clone()), eval(bp.clone()));
                let (ha_id, _ha) = b.fresh_local(ha_ty.clone());
                let (hb_id, _hb) = b.fresh_local(hb_ty.clone());
                let concl = eq_list(
                    eval(sub(a.clone(), bb.clone())),
                    eval(sub(ap.clone(), bp.clone())),
                );
                let t = b.mk_pi(hb_id, BinderInfo::Default, hb_ty, concl);
                let t = b.mk_pi(ha_id, BinderInfo::Default, ha_ty, t);
                let t = b.mk_pi(bp_id, BinderInfo::Default, bvf.clone(), t);
                let t = b.mk_pi(bb_id, BinderInfo::Default, bvf.clone(), t);
                let t = b.mk_pi(ap_id, BinderInfo::Default, bvf.clone(), t);
                b.finish(b.mk_pi(a_id, BinderInfo::Default, bvf.clone(), t))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(bvf.clone());
                let (ap_id, ap) = b.fresh_local(bvf.clone());
                let (bb_id, bb) = b.fresh_local(bvf.clone());
                let (bp_id, bp) = b.fresh_local(bvf.clone());
                let ha_ty = eq_list(eval(a.clone()), eval(ap.clone()));
                let hb_ty = eq_list(eval(bb.clone()), eval(bp.clone()));
                let (ha_id, ha) = b.fresh_local(ha_ty.clone());
                let (hb_id, hb) = b.fresh_local(hb_ty.clone());
                let ea = eval(a.clone());
                let ea_p = eval(ap.clone());
                let eb = eval(bb.clone());
                let eb_p = eval(bp.clone());
                let base = Expr::apps(
                    Expr::const_(
                        Name::from_string("Eq.refl"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [list_bool(), sub_model(ea.clone(), eb.clone())],
                );
                // motive_b l := Eq (subModel ea eb) (subModel ea l)  — l replaces eb (inside bvNot via subModel).
                let motive_b = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (l_id, l) = c.fresh_local(list_bool());
                    let body = eq_list(sub_model(ea.clone(), eb.clone()), sub_model(ea.clone(), l));
                    c.finish_child(c.mk_lam(l_id, BinderInfo::Default, list_bool(), body))
                };
                let s_b = eq_subst(motive_b, eb.clone(), eb_p.clone(), hb, base);
                // motive_a l := Eq (subModel ea eb) (subModel l eb_p)
                let motive_a = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (l_id, l) = c.fresh_local(list_bool());
                    let body = eq_list(
                        sub_model(ea.clone(), eb.clone()),
                        sub_model(l, eb_p.clone()),
                    );
                    c.finish_child(c.mk_lam(l_id, BinderInfo::Default, list_bool(), body))
                };
                let proof = eq_subst(motive_a, ea.clone(), ea_p.clone(), ha, s_b);
                let r = b.mk_lam(hb_id, BinderInfo::Default, hb_ty, proof);
                let r = b.mk_lam(ha_id, BinderInfo::Default, ha_ty, r);
                let r = b.mk_lam(bp_id, BinderInfo::Default, bvf.clone(), r);
                let r = b.mk_lam(bb_id, BinderInfo::Default, bvf.clone(), r);
                let r = b.mk_lam(ap_id, BinderInfo::Default, bvf.clone(), r);
                b.finish(b.mk_lam(a_id, BinderInfo::Default, bvf.clone(), r))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::BVF_SUB_CONG),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }

        // bvf_and_cong / bvf_xor_cong — bitwise op congruences (bvfEval-headed,
        // Eq.subst, no congrArg redex). bvfEval(And x y) reduces to bvZipAnd
        // (eval x)(eval y); bvfEval(Xor x y) to bvZipXor. Same shape as add_cong.
        for (thm_name, ctor_name, reduced) in [
            (names::BVF_AND_CONG, "Clean.BVC.BvF.And", names::ZIP_AND),
            (names::BVF_XOR_CONG, "Clean.BVC.BvF.Xor", names::ZIP_XOR),
            // OR — the general two-sided form. `bvfEval (Or x y)` reduces to
            // `bvZipOr (eval x)(eval y)` exactly as And/Xor reduce to their zips,
            // so it belongs in this table and needs no separate proof shape. Its
            // ABSENCE was load-bearing: `bvf_or_cong2` covers only a fixed left
            // operand (the `Orr Wd, WZR, Ws` move wrapper), so a machine `Orr`
            // with two real operands had no O(1) coercion-identity route and fell
            // back to bit-blasting. See [`names::BVF_OR_CONG`] for the measured
            // cost of that fallback.
            (names::BVF_OR_CONG, "Clean.BVC.BvF.Or", names::ZIP_OR),
            // MUL — bvfEval(Mul x y) reduces to bvMul (eval x)(eval y); same shape.
            (names::BVF_MUL_CONG, "Clean.BVC.BvF.Mul", names::BV_MUL),
            // DIV — bvfEval(Div x y) reduces to bvDiv (eval x)(eval y); same shape.
            (names::BVF_DIV_CONG, "Clean.BVC.BvF.Div", names::BV_DIV),
            // SDIV — bvfEval(SDiv x y) reduces to bvSDiv (eval x)(eval y); same shape.
            (names::BVF_SDIV_CONG, "Clean.BVC.BvF.SDiv", names::BV_SDIV),
            // SHIFTS — bvfEval(Shl/LShr/AShr x y) reduces to bvShl/bvLShr/bvAShr (eval x)(eval y).
            (names::BVF_SHL_CONG, "Clean.BVC.BvF.Shl", names::BV_SHL),
            (names::BVF_LSHR_CONG, "Clean.BVC.BvF.LShr", names::BV_LSHR),
            (names::BVF_ASHR_CONG, "Clean.BVC.BvF.AShr", names::BV_ASHR),
        ] {
            let op = |x: Expr, y: Expr| mk(ctor_name, vec![x, y]);
            let red = |x: Expr, y: Expr| Expr::apps(Expr::const_str(reduced), [x, y]);
            let eq_subst = |motive: Expr, a: Expr, bb2: Expr, h: Expr, m: Expr| {
                Expr::apps(
                    Expr::const_(
                        Name::from_string("Eq.subst"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [list_bool(), motive, a, bb2, h, m],
                )
            };
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(bvf.clone());
                let (ap_id, ap) = b.fresh_local(bvf.clone());
                let (bb_id, bb) = b.fresh_local(bvf.clone());
                let (bp_id, bp) = b.fresh_local(bvf.clone());
                let ha_ty = eq_list(eval(a.clone()), eval(ap.clone()));
                let hb_ty = eq_list(eval(bb.clone()), eval(bp.clone()));
                let (ha_id, _ha) = b.fresh_local(ha_ty.clone());
                let (hb_id, _hb) = b.fresh_local(hb_ty.clone());
                let concl = eq_list(
                    eval(op(a.clone(), bb.clone())),
                    eval(op(ap.clone(), bp.clone())),
                );
                let t = b.mk_pi(hb_id, BinderInfo::Default, hb_ty, concl);
                let t = b.mk_pi(ha_id, BinderInfo::Default, ha_ty, t);
                let t = b.mk_pi(bp_id, BinderInfo::Default, bvf.clone(), t);
                let t = b.mk_pi(bb_id, BinderInfo::Default, bvf.clone(), t);
                let t = b.mk_pi(ap_id, BinderInfo::Default, bvf.clone(), t);
                b.finish(b.mk_pi(a_id, BinderInfo::Default, bvf.clone(), t))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(bvf.clone());
                let (ap_id, ap) = b.fresh_local(bvf.clone());
                let (bb_id, bb) = b.fresh_local(bvf.clone());
                let (bp_id, bp) = b.fresh_local(bvf.clone());
                let ha_ty = eq_list(eval(a.clone()), eval(ap.clone()));
                let hb_ty = eq_list(eval(bb.clone()), eval(bp.clone()));
                let (ha_id, ha) = b.fresh_local(ha_ty.clone());
                let (hb_id, hb) = b.fresh_local(hb_ty.clone());
                let ea = eval(a.clone());
                let ea_p = eval(ap.clone());
                let eb = eval(bb.clone());
                let eb_p = eval(bp.clone());
                let base = Expr::apps(
                    Expr::const_(
                        Name::from_string("Eq.refl"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [list_bool(), red(ea.clone(), eb.clone())],
                );
                let motive_b = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (l_id, l) = c.fresh_local(list_bool());
                    let body = eq_list(red(ea.clone(), eb.clone()), red(ea.clone(), l));
                    c.finish_child(c.mk_lam(l_id, BinderInfo::Default, list_bool(), body))
                };
                let s_b = eq_subst(motive_b, eb.clone(), eb_p.clone(), hb, base);
                let motive_a = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (l_id, l) = c.fresh_local(list_bool());
                    let body = eq_list(red(ea.clone(), eb.clone()), red(l, eb_p.clone()));
                    c.finish_child(c.mk_lam(l_id, BinderInfo::Default, list_bool(), body))
                };
                let proof = eq_subst(motive_a, ea.clone(), ea_p.clone(), ha, s_b);
                let r = b.mk_lam(hb_id, BinderInfo::Default, hb_ty, proof);
                let r = b.mk_lam(ha_id, BinderInfo::Default, ha_ty, r);
                let r = b.mk_lam(bp_id, BinderInfo::Default, bvf.clone(), r);
                let r = b.mk_lam(bb_id, BinderInfo::Default, bvf.clone(), r);
                let r = b.mk_lam(ap_id, BinderInfo::Default, bvf.clone(), r);
                b.finish(b.mk_lam(a_id, BinderInfo::Default, bvf.clone(), r))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(thm_name),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }

        // Single-operand congruences (Or 2nd arg / ZeroExt operand / ExtractLow inner),
        // each `bvfEval`-headed and proved by ONE `Eq.subst` over the reduced form.
        let eq_subst1 = |motive: Expr, a: Expr, bb2: Expr, h: Expr, m: Expr| {
            Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.subst"),
                    vec![Level::succ(Level::zero())],
                ),
                [list_bool(), motive, a, bb2, h, m],
            )
        };
        let refl_at = |v: Expr| {
            Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.refl"),
                    vec![Level::succ(Level::zero())],
                ),
                [list_bool(), v],
            )
        };
        // reduced-op builders
        let zip_or = |xs: Expr, ys: Expr| Expr::apps(Expr::const_str(names::ZIP_OR), [xs, ys]);
        let zext_op = |e: Expr, k: Expr| Expr::apps(Expr::const_str(names::ZEXT), [e, k]);
        let take_len_op =
            |xs: Expr, ys: Expr| Expr::apps(Expr::const_str(names::TAKE_LEN), [xs, ys]);

        // bvf_or_cong2 : ∀ c x x', eval x = eval x' → eval(Or c x) = eval(Or c x')
        {
            let lhs_red = |c: Expr, xv: Expr| zip_or(eval(c), xv);
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (c_id, c) = b.fresh_local(bvf.clone());
                let (x_id, x) = b.fresh_local(bvf.clone());
                let (xp_id, xp) = b.fresh_local(bvf.clone());
                let h_ty = eq_list(eval(x.clone()), eval(xp.clone()));
                let (h_id, _h) = b.fresh_local(h_ty.clone());
                let concl = eq_list(
                    eval(mk("Clean.BVC.BvF.Or", vec![c.clone(), x.clone()])),
                    eval(mk("Clean.BVC.BvF.Or", vec![c.clone(), xp.clone()])),
                );
                let t = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
                let t = b.mk_pi(xp_id, BinderInfo::Default, bvf.clone(), t);
                let t = b.mk_pi(x_id, BinderInfo::Default, bvf.clone(), t);
                b.finish(b.mk_pi(c_id, BinderInfo::Default, bvf.clone(), t))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (c_id, c) = b.fresh_local(bvf.clone());
                let (x_id, x) = b.fresh_local(bvf.clone());
                let (xp_id, xp) = b.fresh_local(bvf.clone());
                let h_ty = eq_list(eval(x.clone()), eval(xp.clone()));
                let (h_id, h) = b.fresh_local(h_ty.clone());
                let motive = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (l_id, l) = d.fresh_local(list_bool());
                    let body = eq_list(
                        lhs_red(c.clone(), eval(x.clone())),
                        zip_or(eval(c.clone()), l),
                    );
                    d.finish_child(d.mk_lam(l_id, BinderInfo::Default, list_bool(), body))
                };
                let base = refl_at(lhs_red(c.clone(), eval(x.clone())));
                let proof = eq_subst1(motive, eval(x.clone()), eval(xp.clone()), h, base);
                let r = b.mk_lam(h_id, BinderInfo::Default, h_ty, proof);
                let r = b.mk_lam(xp_id, BinderInfo::Default, bvf.clone(), r);
                let r = b.mk_lam(x_id, BinderInfo::Default, bvf.clone(), r);
                b.finish(b.mk_lam(c_id, BinderInfo::Default, bvf.clone(), r))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::BVF_OR_CONG2),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }

        // bvf_zext_cong : ∀ x x' k, eval x = eval x' → eval(ZeroExt x k) = eval(ZeroExt x' k)
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (x_id, x) = b.fresh_local(bvf.clone());
                let (xp_id, xp) = b.fresh_local(bvf.clone());
                let (k_id, k) = b.fresh_local(nat_ty());
                let h_ty = eq_list(eval(x.clone()), eval(xp.clone()));
                let (h_id, _h) = b.fresh_local(h_ty.clone());
                let concl = eq_list(
                    eval(mk("Clean.BVC.BvF.ZeroExt", vec![x.clone(), k.clone()])),
                    eval(mk("Clean.BVC.BvF.ZeroExt", vec![xp.clone(), k.clone()])),
                );
                let t = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
                let t = b.mk_pi(k_id, BinderInfo::Default, nat_ty(), t);
                let t = b.mk_pi(xp_id, BinderInfo::Default, bvf.clone(), t);
                b.finish(b.mk_pi(x_id, BinderInfo::Default, bvf.clone(), t))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (x_id, x) = b.fresh_local(bvf.clone());
                let (xp_id, xp) = b.fresh_local(bvf.clone());
                let (k_id, k) = b.fresh_local(nat_ty());
                let h_ty = eq_list(eval(x.clone()), eval(xp.clone()));
                let (h_id, h) = b.fresh_local(h_ty.clone());
                let motive = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (l_id, l) = d.fresh_local(list_bool());
                    let body = eq_list(zext_op(eval(x.clone()), k.clone()), zext_op(l, k.clone()));
                    d.finish_child(d.mk_lam(l_id, BinderInfo::Default, list_bool(), body))
                };
                let base = refl_at(zext_op(eval(x.clone()), k.clone()));
                let proof = eq_subst1(motive, eval(x.clone()), eval(xp.clone()), h, base);
                let r = b.mk_lam(h_id, BinderInfo::Default, h_ty, proof);
                let r = b.mk_lam(k_id, BinderInfo::Default, nat_ty(), r);
                let r = b.mk_lam(xp_id, BinderInfo::Default, bvf.clone(), r);
                b.finish(b.mk_lam(x_id, BinderInfo::Default, bvf.clone(), r))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::BVF_ZEXT_CONG),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }

        // bvf_extract_cong1 : ∀ x x' tag, eval x = eval x' → eval(ExtractLow x tag) = eval(ExtractLow x' tag)
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (x_id, x) = b.fresh_local(bvf.clone());
                let (xp_id, xp) = b.fresh_local(bvf.clone());
                let (tag_id, tag) = b.fresh_local(bvf.clone());
                let h_ty = eq_list(eval(x.clone()), eval(xp.clone()));
                let (h_id, _h) = b.fresh_local(h_ty.clone());
                let concl = eq_list(
                    eval(mk("Clean.BVC.BvF.ExtractLow", vec![x.clone(), tag.clone()])),
                    eval(mk(
                        "Clean.BVC.BvF.ExtractLow",
                        vec![xp.clone(), tag.clone()],
                    )),
                );
                let t = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
                let t = b.mk_pi(tag_id, BinderInfo::Default, bvf.clone(), t);
                let t = b.mk_pi(xp_id, BinderInfo::Default, bvf.clone(), t);
                b.finish(b.mk_pi(x_id, BinderInfo::Default, bvf.clone(), t))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (x_id, x) = b.fresh_local(bvf.clone());
                let (xp_id, xp) = b.fresh_local(bvf.clone());
                let (tag_id, tag) = b.fresh_local(bvf.clone());
                let h_ty = eq_list(eval(x.clone()), eval(xp.clone()));
                let (h_id, h) = b.fresh_local(h_ty.clone());
                let motive = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (l_id, l) = d.fresh_local(list_bool());
                    let body = eq_list(
                        take_len_op(eval(tag.clone()), eval(x.clone())),
                        take_len_op(eval(tag.clone()), l),
                    );
                    d.finish_child(d.mk_lam(l_id, BinderInfo::Default, list_bool(), body))
                };
                let base = refl_at(take_len_op(eval(tag.clone()), eval(x.clone())));
                let proof = eq_subst1(motive, eval(x.clone()), eval(xp.clone()), h, base);
                let r = b.mk_lam(h_id, BinderInfo::Default, h_ty, proof);
                let r = b.mk_lam(tag_id, BinderInfo::Default, bvf.clone(), r);
                let r = b.mk_lam(xp_id, BinderInfo::Default, bvf.clone(), r);
                b.finish(b.mk_lam(x_id, BinderInfo::Default, bvf.clone(), r))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::BVF_EXTRACT_CONG1),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }
        Ok(())
    }

    /// The EQ predicate layer (compares RUNG 1): the genuine Bool predicates
    /// `bvBeq` (per-bit list equality, the IR side) and `bvIsZero` (the SUBS Z
    /// flag, the machine side), the compare register value `bvIteVal` (via
    /// `Bool.rec`), the branch-inversion identity `iteVal_not`, and the
    /// subtract-zero bridge `beq_eq_isZero_sub` (`a == b ⟺ a - b == 0`).
    ///
    /// NON-VACUITY: `bvBeq` and `bvIsZero` are SEPARATELY-DEFINED real Bool
    /// functions; the bridge is PROVEN by induction (not definitional collapse);
    /// `bvIteVal (Bool.not p) u v = bvIteVal p v u` is proven by `Bool.rec`
    /// case-split (a non-inverted form would NOT typecheck against this goal).
    fn register_bvf_eq_predicate(&mut self) -> Result<(), EnvError> {
        let lbb = Expr::arrow(list_bool(), Expr::arrow(list_bool(), bool_ty()));
        let lb_bool = Expr::arrow(list_bool(), bool_ty());

        // ── bvIsZero : List Bool → Bool ───────────────────────────────────────
        // bvIsZero xs := List.rec (fun _ => Bool) true
        //                  (fun h _ ih => Bool.and (Bool.not h) ih) xs
        // (true iff every bit is false — the SUBS Z flag of the result word.)
        {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (xs_id, xs) = b.fresh_local(list_bool());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(list_bool());
                    c.finish_child(c.mk_lam(w_id, BinderInfo::Default, list_bool(), bool_ty()))
                };
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (h_id, h) = c.fresh_local(bool_ty());
                    let (t_id, _t) = c.fresh_local(list_bool());
                    let (ih_id, ih) = c.fresh_local(bool_ty());
                    let body = band(bnot(h), ih);
                    let r = c.mk_lam(ih_id, BinderInfo::Default, bool_ty(), body);
                    let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, bool_ty(), r))
                };
                // @List.rec.{1,0} Bool (fun _ => Bool) true cons_case xs
                let rec = Expr::apps(
                    Expr::const_(
                        Name::from_string("List.rec"),
                        vec![Level::succ(Level::zero()), Level::zero()],
                    ),
                    [bool_ty(), motive, btrue(), cons_case, xs.clone()],
                );
                b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_bool(), rec))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::BV_IS_ZERO),
                level_params: vec![],
                type_: lb_bool.clone(),
                value: val,
                is_reducible: true,
            })?;
        }

        // ── bvBeq : List Bool → List Bool → Bool ──────────────────────────────
        // Recurse over xs (consuming ys), folding Bool.and of per-bit equality
        // (Bool.beq of head bits via `Bool.not (Bool.xor h wh)`). nil-case: ws ↦
        // true (a length-mismatch tail is ignored — both operands are width-w in
        // the gate, so xs/ys have equal length and this never bites). Same
        // two-arg recursion shape as bvTakeLen.
        {
            let consumer = lb_bool.clone(); // List Bool → Bool
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (xs_id, xs) = b.fresh_local(list_bool());
                let (ys_id, ys) = b.fresh_local(list_bool());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(list_bool());
                    c.finish_child(c.mk_lam(
                        w_id,
                        BinderInfo::Default,
                        list_bool(),
                        consumer.clone(),
                    ))
                };
                // nil_case : List Bool → Bool = fun _ => true
                let nil_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (ws_id, _ws) = c.fresh_local(list_bool());
                    c.finish_child(c.mk_lam(ws_id, BinderInfo::Default, list_bool(), btrue()))
                };
                // cons_case h t ih = fun ws => listRec ws true
                //   (fun wh wt _ => Bool.and (Bool.not (Bool.xor h wh)) (ih wt))
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (h_id, h) = c.fresh_local(bool_ty());
                    let (t_id, _t) = c.fresh_local(list_bool());
                    let (ih_id, ih) = c.fresh_local(consumer.clone());
                    let inner = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (ws_id, ws) = d.fresh_local(list_bool());
                        let wmot = {
                            let mut e = EnvDeclBuilder::child_of(&d);
                            let (z_id, _z) = e.fresh_local(list_bool());
                            e.finish_child(e.mk_lam(
                                z_id,
                                BinderInfo::Default,
                                list_bool(),
                                bool_ty(),
                            ))
                        };
                        let wcons = {
                            let mut e = EnvDeclBuilder::child_of(&d);
                            let (wh_id, wh) = e.fresh_local(bool_ty());
                            let (wt_id, wt) = e.fresh_local(list_bool());
                            let (wih_id, _wih) = e.fresh_local(bool_ty());
                            // Bool.and (Bool.not (Bool.xor h wh)) (ih wt)
                            let body = band(bnot(bxor(h.clone(), wh)), Expr::app(ih.clone(), wt));
                            let r = e.mk_lam(wih_id, BinderInfo::Default, bool_ty(), body);
                            let r = e.mk_lam(wt_id, BinderInfo::Default, list_bool(), r);
                            e.finish_child(e.mk_lam(wh_id, BinderInfo::Default, bool_ty(), r))
                        };
                        let wrec = Expr::apps(
                            Expr::const_(
                                Name::from_string("List.rec"),
                                vec![Level::succ(Level::zero()), Level::zero()],
                            ),
                            [bool_ty(), wmot, btrue(), wcons, ws.clone()],
                        );
                        d.finish_child(d.mk_lam(ws_id, BinderInfo::Default, list_bool(), wrec))
                    };
                    let r = c.mk_lam(ih_id, BinderInfo::Default, consumer.clone(), inner);
                    let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, bool_ty(), r))
                };
                let rec = Expr::apps(
                    Expr::const_(
                        Name::from_string("List.rec"),
                        vec![Level::succ(Level::zero()), Level::zero()],
                    ),
                    [bool_ty(), motive, nil_case, cons_case, xs.clone()],
                );
                let applied = Expr::app(rec, ys.clone());
                let r = b.mk_lam(ys_id, BinderInfo::Default, list_bool(), applied);
                b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_bool(), r))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::BV_BEQ),
                level_params: vec![],
                type_: lbb.clone(),
                value: val,
                is_reducible: true,
            })?;
        }

        // ── bvIteVal : Bool → List Bool → List Bool → List Bool ───────────────
        // bvIteVal p vt ve := @Bool.rec (fun _ => List Bool) ve vt p
        // (minors in ctor order: false-case = ve, true-case = vt).
        {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(bool_ty());
                let (vt_id, vt) = b.fresh_local(list_bool());
                let (ve_id, ve) = b.fresh_local(list_bool());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(bool_ty());
                    c.finish_child(c.mk_lam(w_id, BinderInfo::Default, bool_ty(), list_bool()))
                };
                let rec = Expr::apps(
                    Expr::const_(
                        Name::from_string("Bool.rec"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [motive, ve.clone(), vt.clone(), p.clone()],
                );
                let r = b.mk_lam(ve_id, BinderInfo::Default, list_bool(), rec);
                let r = b.mk_lam(vt_id, BinderInfo::Default, list_bool(), r);
                b.finish(b.mk_lam(p_id, BinderInfo::Default, bool_ty(), r))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::BV_ITE_VAL),
                level_params: vec![],
                type_: Expr::arrow(
                    bool_ty(),
                    Expr::arrow(list_bool(), Expr::arrow(list_bool(), list_bool())),
                ),
                value: val,
                is_reducible: true,
            })?;
        }

        // ── iteVal_not : ∀ p u v, bvIteVal (Bool.not p) u v = bvIteVal p v u ───
        // Proven by `Bool.rec` case-split on p (a DEPENDENT motive over the
        // discriminant): false ⟹ both sides reduce to v (refl); true ⟹ both
        // reduce to u (refl). A non-inverted RHS (`bvIteVal p u v`) would leave
        // the false case as `v = u`, NOT closeable by refl — so this is the real
        // branch-swap, not a vacuous restatement.
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(bool_ty());
                let (u_id, u) = b.fresh_local(list_bool());
                let (v_id, v) = b.fresh_local(list_bool());
                let goal = eq_list(
                    bv_ite_val(bnot(p.clone()), u.clone(), v.clone()),
                    bv_ite_val(p.clone(), v.clone(), u.clone()),
                );
                let t = b.mk_pi(v_id, BinderInfo::Default, list_bool(), goal);
                let t = b.mk_pi(u_id, BinderInfo::Default, list_bool(), t);
                b.finish(b.mk_pi(p_id, BinderInfo::Default, bool_ty(), t))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(bool_ty());
                let (u_id, u) = b.fresh_local(list_bool());
                let (v_id, v) = b.fresh_local(list_bool());
                // motive x := bvIteVal (Bool.not x) u v = bvIteVal x v u
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (x_id, x) = c.fresh_local(bool_ty());
                    let body = eq_list(
                        bv_ite_val(bnot(x.clone()), u.clone(), v.clone()),
                        bv_ite_val(x.clone(), v.clone(), u.clone()),
                    );
                    c.finish_child(c.mk_lam(x_id, BinderInfo::Default, bool_ty(), body))
                };
                // false minor: bvIteVal (not false=true) u v = bvIteVal false v u
                //   LHS ≡ u (true picks vt=u); RHS ≡ u (false picks ve=u) → refl u.
                let minor_false = eq_refl_list(u.clone());
                // true minor: bvIteVal (not true=false) u v = bvIteVal true v u
                //   LHS ≡ v ; RHS ≡ v → refl v.
                let minor_true = eq_refl_list(v.clone());
                let rec = Expr::apps(
                    Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
                    [motive, minor_false, minor_true, p.clone()],
                );
                let r = b.mk_lam(v_id, BinderInfo::Default, list_bool(), rec);
                let r = b.mk_lam(u_id, BinderInfo::Default, list_bool(), r);
                b.finish(b.mk_lam(p_id, BinderInfo::Default, bool_ty(), r))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::ITE_VAL_NOT),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }

        // ── divGuardBridge : ∀ (b z dv : List Bool), bvIsZero b = false →
        //      bvIteVal (bvIsZero b) z dv = dv   (THE CONDITIONAL-DISCHARGE KEYSTONE)
        // The machine div-by-zero guard `Ite(Eq(b,0), 0, div) = bvIteVal (bvIsZero b) z dv`
        // collapses to the else branch `dv` under the precondition `bvIsZero b = false`.
        // Proof: Eq.subst rewrites the guard predicate `bvIsZero b → false` via the
        // hypothesis (Eq.symm h : false = bvIsZero b), lifting the base `bvIteVal false z dv = dv`
        // (refl — false picks the else branch) to `bvIteVal (bvIsZero b) z dv = dv`. The
        // hypothesis is LOAD-BEARING: without it the guard predicate stays symbolic and
        // `bvIteVal (bvIsZero b) z dv` is STUCK (not refl-closeable).
        {
            let l1 = Level::succ(Level::zero());
            let iz = |b: Expr| bv_is_zero(b);
            let goal_of =
                |b: Expr, z: Expr, dv: Expr| eq_list(bv_ite_val(iz(b), z, dv.clone()), dv);
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (bb_id, bb) = b.fresh_local(list_bool());
                let (z_id, z) = b.fresh_local(list_bool());
                let (dv_id, dv) = b.fresh_local(list_bool());
                let hty = eq_bool(iz(bb.clone()), bfalse());
                let (h_id, _h) = b.fresh_local(hty.clone());
                let t = b.mk_pi(
                    h_id,
                    BinderInfo::Default,
                    hty,
                    goal_of(bb.clone(), z.clone(), dv.clone()),
                );
                let t = b.mk_pi(dv_id, BinderInfo::Default, list_bool(), t);
                let t = b.mk_pi(z_id, BinderInfo::Default, list_bool(), t);
                b.finish(b.mk_pi(bb_id, BinderInfo::Default, list_bool(), t))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (bb_id, bb) = b.fresh_local(list_bool());
                let (z_id, z) = b.fresh_local(list_bool());
                let (dv_id, dv) = b.fresh_local(list_bool());
                let hty = eq_bool(iz(bb.clone()), bfalse());
                let (h_id, h) = b.fresh_local(hty.clone());
                // motive p := bvIteVal p z dv = dv
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (p_id, p) = c.fresh_local(bool_ty());
                    let body = eq_list(bv_ite_val(p, z.clone(), dv.clone()), dv.clone());
                    c.finish_child(c.mk_lam(p_id, BinderInfo::Default, bool_ty(), body))
                };
                // base : motive false = (bvIteVal false z dv = dv) — refl (false picks ve=dv).
                let base = eq_refl_list(dv.clone());
                // symm h : false = bvIsZero b
                let symm = Expr::apps(
                    Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
                    [bool_ty(), iz(bb.clone()), bfalse(), h],
                );
                // Eq.subst {Bool} motive false (bvIsZero b) (symm h) base : motive (bvIsZero b)
                let proof = Expr::apps(
                    Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
                    [bool_ty(), motive, bfalse(), iz(bb.clone()), symm, base],
                );
                let r = b.mk_lam(h_id, BinderInfo::Default, hty, proof);
                let r = b.mk_lam(dv_id, BinderInfo::Default, list_bool(), r);
                let r = b.mk_lam(z_id, BinderInfo::Default, list_bool(), r);
                b.finish(b.mk_lam(bb_id, BinderInfo::Default, list_bool(), r))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::DIV_GUARD_BRIDGE),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }

        // ════════════════════════════════════════════════════════════════════════
        // MEMORY (construct-dimension rung 1): the store-then-load roundtrip.
        // An array is modelled as a function `addr → value` (List Bool → List Bool):
        //   bvSelect m a := m a
        //   bvStore m a v := fun a' => bvIteVal (bvBeq a a') v (m a')
        // A pure-Definition function model (NO inductive extension → NO recursor
        // re-derivation, NO ripple risk by construction). The keystone is the
        // single-address read-over-write identity, the array analogue of the scalar
        // coercion-identity.
        // ════════════════════════════════════════════════════════════════════════
        let arr_ty = Expr::arrow(list_bool(), list_bool()); // addr → value

        // ── bvBeq_refl : ∀ (a : List Bool), bvBeq a a = true ──────────────────
        // Induction on a. nil: bvBeq nil nil ≡ true (rfl). cons h t:
        //   bvBeq (h::t) (h::t) = and (not (xor h h)) (bvBeq t t). `xor h h` is STUCK
        //   on a symbolic head, so DISPATCH h via Bool.rec: at each literal,
        //   xor h0 h0 = false ⇒ not false = true ⇒ and true (bvBeq t t) = bvBeq t t,
        //   proved by the IH `bvBeq t t = true` (so and true true = true).
        {
            let goal_of = |a: Expr| eq_bool(bv_beq(a.clone(), a), btrue());
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(list_bool());
                b.finish(b.mk_pi(a_id, BinderInfo::Default, list_bool(), goal_of(a.clone())))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(list_bool());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, w) = c.fresh_local(list_bool());
                    c.finish_child(c.mk_lam(
                        w_id,
                        BinderInfo::Default,
                        list_bool(),
                        goal_of(w.clone()),
                    ))
                };
                let nil_case = eq_refl_bool(btrue());
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (h_id, h) = c.fresh_local(bool_ty());
                    let (t_id, t) = c.fresh_local(list_bool());
                    let ih_ty = goal_of(t.clone());
                    let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                    // motive_h h0 := bvBeq (h0::t) (h0::t) = true
                    let hmot = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (h0_id, h0) = d.fresh_local(bool_ty());
                        let g = eq_bool(
                            bv_beq(cons_b(h0.clone(), t.clone()), cons_b(h0.clone(), t.clone())),
                            btrue(),
                        );
                        d.finish_child(d.mk_lam(h0_id, BinderInfo::Default, bool_ty(), g))
                    };
                    // At a literal head, bvBeq (h0::t)(h0::t) ≡ and (not (xor h0 h0)) (bvBeq t t)
                    //   ≡ and true (bvBeq t t) ≡ bvBeq t t ; the goal is `bvBeq t t = true` = ih.
                    let mk_leaf = |_h0: Expr| ih.clone();
                    let body = Expr::apps(
                        Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
                        [hmot, mk_leaf(bfalse()), mk_leaf(btrue()), h.clone()],
                    );
                    let r = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                    let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, bool_ty(), r))
                };
                let rec = list_rec_prop(motive, nil_case, cons_case, a.clone());
                b.finish(b.mk_lam(a_id, BinderInfo::Default, list_bool(), rec))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::BV_BEQ_REFL),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }

        // ── bvBeqConsFalse : ∀ (h1 h2 : Bool) (t1 t2 : List Bool),
        //      Bool.xor h1 h2 = true → bvBeq (h1::t1) (h2::t2) = false ──────────
        // bvBeq (h1::t1)(h2::t2) ≡ and (not (xor h1 h2)) (bvBeq t1 t2). Under the
        // hypothesis xor h1 h2 = true this is and (not true) _ ≡ and false _ ≡ false.
        // Same Eq.subst shape as divGuardBridge/selectStoreDiff: motive p := and (not p)
        // (bvBeq t1 t2) = false ; base motive true ≡ (false = false) refl ; lift along
        // (symm h : true = xor h1 h2) to motive (xor h1 h2) ≡ the goal.
        {
            let l1 = Level::succ(Level::zero());
            let goal_of = |h1: Expr, h2: Expr, t1: Expr, t2: Expr| {
                eq_bool(bv_beq(cons_b(h1, t1), cons_b(h2, t2)), bfalse())
            };
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (h1_id, h1) = b.fresh_local(bool_ty());
                let (h2_id, h2) = b.fresh_local(bool_ty());
                let (t1_id, t1) = b.fresh_local(list_bool());
                let (t2_id, t2) = b.fresh_local(list_bool());
                let hty = eq_bool(bxor(h1.clone(), h2.clone()), btrue());
                let (h_id, _h) = b.fresh_local(hty.clone());
                let goal = goal_of(h1.clone(), h2.clone(), t1.clone(), t2.clone());
                let t = b.mk_pi(h_id, BinderInfo::Default, hty, goal);
                let t = b.mk_pi(t2_id, BinderInfo::Default, list_bool(), t);
                let t = b.mk_pi(t1_id, BinderInfo::Default, list_bool(), t);
                let t = b.mk_pi(h2_id, BinderInfo::Default, bool_ty(), t);
                b.finish(b.mk_pi(h1_id, BinderInfo::Default, bool_ty(), t))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (h1_id, h1) = b.fresh_local(bool_ty());
                let (h2_id, h2) = b.fresh_local(bool_ty());
                let (t1_id, t1) = b.fresh_local(list_bool());
                let (t2_id, t2) = b.fresh_local(list_bool());
                let hty = eq_bool(bxor(h1.clone(), h2.clone()), btrue());
                let (h_id, h) = b.fresh_local(hty.clone());
                // motive p := Bool.and (Bool.not p) (bvBeq t1 t2) = false
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (p_id, p) = c.fresh_local(bool_ty());
                    let body = eq_bool(band(bnot(p), bv_beq(t1.clone(), t2.clone())), bfalse());
                    c.finish_child(c.mk_lam(p_id, BinderInfo::Default, bool_ty(), body))
                };
                // base : motive true ≡ (and (not true) (bvBeq t1 t2) = false) ≡ (false = false)
                let base = eq_refl_bool(bfalse());
                // symm h : true = xor h1 h2
                let symm = Expr::apps(
                    Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
                    [bool_ty(), bxor(h1.clone(), h2.clone()), btrue(), h],
                );
                // Eq.subst motive true (xor h1 h2) (symm) base : motive (xor h1 h2)
                //   ≡ (and (not (xor h1 h2)) (bvBeq t1 t2) = false) ≡ goal.
                let proof = Expr::apps(
                    Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
                    [
                        bool_ty(),
                        motive,
                        btrue(),
                        bxor(h1.clone(), h2.clone()),
                        symm,
                        base,
                    ],
                );
                let r = b.mk_lam(h_id, BinderInfo::Default, hty, proof);
                let r = b.mk_lam(t2_id, BinderInfo::Default, list_bool(), r);
                let r = b.mk_lam(t1_id, BinderInfo::Default, list_bool(), r);
                let r = b.mk_lam(h2_id, BinderInfo::Default, bool_ty(), r);
                b.finish(b.mk_lam(h1_id, BinderInfo::Default, bool_ty(), r))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::BV_BEQ_CONS_FALSE),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }

        // ── bvSelect m a := m a ───────────────────────────────────────────────
        {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (m_id, m) = b.fresh_local(arr_ty.clone());
                let (a_id, a) = b.fresh_local(list_bool());
                let body = Expr::app(m, a);
                let r = b.mk_lam(a_id, BinderInfo::Default, list_bool(), body);
                b.finish(b.mk_lam(m_id, BinderInfo::Default, arr_ty.clone(), r))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::BV_SELECT),
                level_params: vec![],
                type_: Expr::arrow(arr_ty.clone(), Expr::arrow(list_bool(), list_bool())),
                value: val,
                is_reducible: true,
            })?;
        }

        // ── bvStore m a v := fun a' => bvIteVal (bvBeq a a') v (m a') ──────────
        {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (m_id, m) = b.fresh_local(arr_ty.clone());
                let (a_id, a) = b.fresh_local(list_bool());
                let (v_id, v) = b.fresh_local(list_bool());
                let body = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (ap_id, ap) = c.fresh_local(list_bool());
                    let upd = bv_ite_val(
                        bv_beq(a.clone(), ap.clone()),
                        v.clone(),
                        Expr::app(m.clone(), ap.clone()),
                    );
                    c.finish_child(c.mk_lam(ap_id, BinderInfo::Default, list_bool(), upd))
                };
                let r = b.mk_lam(v_id, BinderInfo::Default, list_bool(), body);
                let r = b.mk_lam(a_id, BinderInfo::Default, list_bool(), r);
                b.finish(b.mk_lam(m_id, BinderInfo::Default, arr_ty.clone(), r))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::BV_STORE),
                level_params: vec![],
                type_: Expr::arrow(
                    arr_ty.clone(),
                    Expr::arrow(list_bool(), Expr::arrow(list_bool(), arr_ty.clone())),
                ),
                value: val,
                is_reducible: true,
            })?;
        }

        // ── selectStoreSame : ∀ m a v, bvSelect (bvStore m a v) a = v ─────────
        // bvSelect (bvStore m a v) a ≡ (bvStore m a v) a ≡ bvIteVal (bvBeq a a) v (m a).
        // bvBeq_refl a : bvBeq a a = true ; Eq.subst rewrites the guard to true, so
        // bvIteVal true v (m a) ≡ v. Proof: Eq.subst (motive p := bvIteVal p v (m a) = v)
        //   false-shape... here the base is `bvIteVal true v (m a) = v` (refl) lifted
        //   along (symm of bvBeq_refl): false direction is true → bvBeq a a.
        {
            let sel = |m: Expr, a: Expr| Expr::apps(Expr::const_str(names::BV_SELECT), [m, a]);
            let sto =
                |m: Expr, a: Expr, v: Expr| Expr::apps(Expr::const_str(names::BV_STORE), [m, a, v]);
            let l1 = Level::succ(Level::zero());
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (m_id, m) = b.fresh_local(arr_ty.clone());
                let (a_id, a) = b.fresh_local(list_bool());
                let (v_id, v) = b.fresh_local(list_bool());
                let goal = eq_list(
                    sel(sto(m.clone(), a.clone(), v.clone()), a.clone()),
                    v.clone(),
                );
                let t = b.mk_pi(v_id, BinderInfo::Default, list_bool(), goal);
                let t = b.mk_pi(a_id, BinderInfo::Default, list_bool(), t);
                b.finish(b.mk_pi(m_id, BinderInfo::Default, arr_ty.clone(), t))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (m_id, m) = b.fresh_local(arr_ty.clone());
                let (a_id, a) = b.fresh_local(list_bool());
                let (v_id, v) = b.fresh_local(list_bool());
                // motive p := bvIteVal p v (m a) = v
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (p_id, p) = c.fresh_local(bool_ty());
                    let body = eq_list(
                        bv_ite_val(p, v.clone(), Expr::app(m.clone(), a.clone())),
                        v.clone(),
                    );
                    c.finish_child(c.mk_lam(p_id, BinderInfo::Default, bool_ty(), body))
                };
                // base : motive true = (bvIteVal true v (m a) = v) — refl (true picks vt=v).
                let base = eq_refl_list(v.clone());
                // bvBeq_refl a : bvBeq a a = true ; symm : true = bvBeq a a
                let beq_refl = Expr::app(Expr::const_str(names::BV_BEQ_REFL), a.clone());
                let symm = Expr::apps(
                    Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
                    [bool_ty(), bv_beq(a.clone(), a.clone()), btrue(), beq_refl],
                );
                // Eq.subst {Bool} motive true (bvBeq a a) symm base : motive (bvBeq a a)
                //   ≡ (bvIteVal (bvBeq a a) v (m a) = v) ≡ (bvSelect (bvStore m a v) a = v).
                let proof = Expr::apps(
                    Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
                    [
                        bool_ty(),
                        motive,
                        btrue(),
                        bv_beq(a.clone(), a.clone()),
                        symm,
                        base,
                    ],
                );
                let r = b.mk_lam(v_id, BinderInfo::Default, list_bool(), proof);
                let r = b.mk_lam(a_id, BinderInfo::Default, list_bool(), r);
                b.finish(b.mk_lam(m_id, BinderInfo::Default, arr_ty.clone(), r))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::SELECT_STORE_SAME),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;

            // ── selectStoreDiff : ∀ m a a' v, bvBeq a a' = false →
            //      bvSelect (bvStore m a v) a' = bvSelect m a'  (the non-aliasing read-over-write) ──
            // bvSelect (bvStore m a v) a' reduces to bvIteVal (bvBeq a a') v (m a'); under
            // bvBeq a a' = false the guard picks the ELSE branch m a' = bvSelect m a' (divGuardBridge
            // shape). Eq.subst rewrites false -> bvBeq a a' via (Eq.symm h), lifting the base
            // (bvIteVal false v (m a') = m a', refl) to the goal.
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (m_id, m) = b.fresh_local(arr_ty.clone());
                let (a_id, a) = b.fresh_local(list_bool());
                let (ap_id, ap) = b.fresh_local(list_bool());
                let (v_id, v) = b.fresh_local(list_bool());
                let hty = eq_bool(bv_beq(a.clone(), ap.clone()), bfalse());
                let (h_id, _h) = b.fresh_local(hty.clone());
                let goal = eq_list(
                    sel(sto(m.clone(), a.clone(), v.clone()), ap.clone()),
                    sel(m.clone(), ap.clone()),
                );
                let t = b.mk_pi(h_id, BinderInfo::Default, hty, goal);
                let t = b.mk_pi(v_id, BinderInfo::Default, list_bool(), t);
                let t = b.mk_pi(ap_id, BinderInfo::Default, list_bool(), t);
                let t = b.mk_pi(a_id, BinderInfo::Default, list_bool(), t);
                b.finish(b.mk_pi(m_id, BinderInfo::Default, arr_ty.clone(), t))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (m_id, m) = b.fresh_local(arr_ty.clone());
                let (a_id, a) = b.fresh_local(list_bool());
                let (ap_id, ap) = b.fresh_local(list_bool());
                let (v_id, v) = b.fresh_local(list_bool());
                let hty = eq_bool(bv_beq(a.clone(), ap.clone()), bfalse());
                let (h_id, h) = b.fresh_local(hty.clone());
                let m_ap = Expr::app(m.clone(), ap.clone());
                // motive p := bvIteVal p v (m a') = m a'
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (p_id, p) = c.fresh_local(bool_ty());
                    let body = eq_list(bv_ite_val(p, v.clone(), m_ap.clone()), m_ap.clone());
                    c.finish_child(c.mk_lam(p_id, BinderInfo::Default, bool_ty(), body))
                };
                // base : motive false = (bvIteVal false v (m a') = m a') — refl (false picks the else branch).
                let base = eq_refl_list(m_ap.clone());
                // symm h : false = bvBeq a a'
                let symm = Expr::apps(
                    Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
                    [bool_ty(), bv_beq(a.clone(), ap.clone()), bfalse(), h],
                );
                let proof = Expr::apps(
                    Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
                    [
                        bool_ty(),
                        motive,
                        bfalse(),
                        bv_beq(a.clone(), ap.clone()),
                        symm,
                        base,
                    ],
                );
                let r = b.mk_lam(h_id, BinderInfo::Default, hty, proof);
                let r = b.mk_lam(v_id, BinderInfo::Default, list_bool(), r);
                let r = b.mk_lam(ap_id, BinderInfo::Default, list_bool(), r);
                let r = b.mk_lam(a_id, BinderInfo::Default, list_bool(), r);
                b.finish(b.mk_lam(m_id, BinderInfo::Default, arr_ty.clone(), r))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::SELECT_STORE_DIFF),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;

            // ── selectAddrCong : ∀ m a a', a = a' → bvSelect m a = bvSelect m a' ──
            //
            // THE CALLER-PROVIDED-MEMORY law (see `names::SELECT_ADDR_CONG`). The two
            // read-over-write lemmas above both relate a read to a write the term
            // itself performs; NEITHER covers a read from an OPAQUE PRE-STATE — memory
            // the function never wrote, which is exactly a load through a `&T`
            // parameter. This transports an address equality under `bvSelect` at a
            // FIXED array, which is the weakest law that discharges that shape: `m` is
            // never interpreted, so it holds for an axiom-opaque memory (the caller's),
            // not just for the closed dummy array the store-load path abstracts to.
            //
            // Proof: Eq.subst with motive `l := bvSelect m a = bvSelect m l`, base
            // `Eq.refl (bvSelect m a)` — the same shape as every other cong in this
            // layer, so the domain-axiom closure stays empty. NO congrArg redex.
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (m_id, m) = b.fresh_local(arr_ty.clone());
                let (a_id, a) = b.fresh_local(list_bool());
                let (ap_id, ap) = b.fresh_local(list_bool());
                let hty = eq_list(a.clone(), ap.clone());
                let (h_id, _h) = b.fresh_local(hty.clone());
                let goal = eq_list(sel(m.clone(), a.clone()), sel(m.clone(), ap.clone()));
                let t = b.mk_pi(h_id, BinderInfo::Default, hty, goal);
                let t = b.mk_pi(ap_id, BinderInfo::Default, list_bool(), t);
                let t = b.mk_pi(a_id, BinderInfo::Default, list_bool(), t);
                b.finish(b.mk_pi(m_id, BinderInfo::Default, arr_ty.clone(), t))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (m_id, m) = b.fresh_local(arr_ty.clone());
                let (a_id, a) = b.fresh_local(list_bool());
                let (ap_id, ap) = b.fresh_local(list_bool());
                let hty = eq_list(a.clone(), ap.clone());
                let (h_id, h) = b.fresh_local(hty.clone());
                // motive l := bvSelect m a = bvSelect m l
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (l_id, l) = c.fresh_local(list_bool());
                    let body = eq_list(sel(m.clone(), a.clone()), sel(m.clone(), l));
                    c.finish_child(c.mk_lam(l_id, BinderInfo::Default, list_bool(), body))
                };
                // base : motive a ≡ (bvSelect m a = bvSelect m a) — refl.
                let base = eq_refl_list(sel(m.clone(), a.clone()));
                // Eq.subst {List Bool} motive a a' h base : motive a'.
                let proof = Expr::apps(
                    Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
                    [list_bool(), motive, a.clone(), ap.clone(), h, base],
                );
                let r = b.mk_lam(h_id, BinderInfo::Default, hty, proof);
                let r = b.mk_lam(ap_id, BinderInfo::Default, list_bool(), r);
                let r = b.mk_lam(a_id, BinderInfo::Default, list_bool(), r);
                b.finish(b.mk_lam(m_id, BinderInfo::Default, arr_ty.clone(), r))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::SELECT_ADDR_CONG),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }

        // ── bvLen : List Bool -> Nat ──────────────────────────────────────────
        {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (xs_id, xs) = b.fresh_local(list_bool());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(list_bool());
                    c.finish_child(c.mk_lam(w_id, BinderInfo::Default, list_bool(), nat_ty()))
                };
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (h_id, _h) = c.fresh_local(bool_ty());
                    let (t_id, _t) = c.fresh_local(list_bool());
                    let (ih_id, ih) = c.fresh_local(nat_ty());
                    let body = Expr::app(Expr::const_str("Nat.succ"), ih);
                    let r = c.mk_lam(ih_id, BinderInfo::Default, nat_ty(), body);
                    let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, bool_ty(), r))
                };
                let rec = Expr::apps(
                    Expr::const_(
                        Name::from_string("List.rec"),
                        vec![Level::succ(Level::zero()), Level::zero()],
                    ),
                    [
                        bool_ty(),
                        motive,
                        Expr::const_str("Nat.zero"),
                        cons_case,
                        xs.clone(),
                    ],
                );
                b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_bool(), rec))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::BV_LEN),
                level_params: vec![],
                type_: Expr::arrow(list_bool(), nat_ty()),
                value: val,
                is_reducible: true,
            })?;
        }

        self.register_beq_is_zero_bridge()?;
        self.register_ult_predicate()?;
        self.register_ule_predicate()?;
        self.register_slt_predicate()?;
        Ok(())
    }

    /// The subtract-zero predicate bridge (EQ meaning bridge):
    ///   beq_eq_isZero_sub : forall a b, bvLen a = bvLen b ->
    ///       bvBeq a b = bvIsZero (addRecM a (bvNot b) true)
    /// (`a == b  <=>  a - b == 0` at equal width). Induction over `a`, destruct
    /// `b`; cons/cons arm by a 2x2 Bool.rec on the head bits (carry-in true is the
    /// clean invariant). Mismatch arms: absurd via a Nat zero/succ discriminator.
    /// g16 is the STRATEGY TEMPLATE (its eq_equiv is adder-vs-adder fidelity, a
    /// different equation) re-proved on the live substrate, NOT a dependency.
    #[allow(clippy::too_many_lines)]
    fn register_beq_is_zero_bridge(&mut self) -> Result<(), EnvError> {
        let nat = nat_ty();
        let nzero = Expr::const_str("Nat.zero");
        let succ = |n: Expr| Expr::app(Expr::const_str("Nat.succ"), n);
        let bvlen = |xs: Expr| Expr::app(Expr::const_str(names::BV_LEN), xs);
        let eq_nat = |x: Expr, y: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [nat.clone(), x, y],
            )
        };
        // goal(a,b) := bvBeq a b = bvIsZero (addRecM a (bvNot b) true)
        let goal = |a: Expr, b: Expr| {
            eq_bool(
                bv_beq_l(a.clone(), b.clone()),
                bv_is_zero_l(add_rec_m_l(a, bv_not_l(b), btrue())),
            )
        };

        // Identity-coercion helpers (the #39 keystone for nested recursors): carry
        // the def-eq `goal (cons LIT as)(cons LIT bs) == goal as bs` in the TYPE
        // SIGNATURE (checked by full def_eq at registration), so the equal-case
        // recursor leaf can present the UN-reduced motive-application type the
        // Bool.rec minor expects, instead of the reduced `goal as bs`. Proven by
        // `fun g => g` (the two are definitionally equal at a CONCRETE head bit).
        for (suffix, lit) in [("True", btrue()), ("False", bfalse())] {
            let name = format!("Clean.BVC.goalConsCong{suffix}");
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (as_id, as_) = b.fresh_local(list_bool());
                let (bs_id, bs) = b.fresh_local(list_bool());
                let g_ty = goal(as_.clone(), bs.clone());
                let (g_id, _g) = b.fresh_local(g_ty.clone());
                let concl = goal(
                    cons_b(lit.clone(), as_.clone()),
                    cons_b(lit.clone(), bs.clone()),
                );
                let t = b.mk_pi(g_id, BinderInfo::Default, g_ty, concl);
                let t = b.mk_pi(bs_id, BinderInfo::Default, list_bool(), t);
                b.finish(b.mk_pi(as_id, BinderInfo::Default, list_bool(), t))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (as_id, as_) = b.fresh_local(list_bool());
                let (bs_id, bs) = b.fresh_local(list_bool());
                let g_ty = goal(as_.clone(), bs.clone());
                let (g_id, g) = b.fresh_local(g_ty.clone());
                let r = b.mk_lam(g_id, BinderInfo::Default, g_ty, g);
                let r = b.mk_lam(bs_id, BinderInfo::Default, list_bool(), r);
                b.finish(b.mk_lam(as_id, BinderInfo::Default, list_bool(), r))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(&name),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }

        // Nat zero/succ discriminator: disc n := Nat.rec.{1} (fun _ => Prop) True (fun _ _ => False) n
        let nat_disc = {
            let mut c = EnvDeclBuilder::new();
            let (n_id, n) = c.fresh_local(nat.clone());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&c);
                let (w_id, _w) = d.fresh_local(nat.clone());
                d.finish_child(d.mk_lam(
                    w_id,
                    BinderInfo::Default,
                    nat.clone(),
                    Expr::sort(Level::zero()),
                ))
            };
            let succ_case = {
                let mut d = EnvDeclBuilder::child_of(&c);
                let (m_id, _m) = d.fresh_local(nat.clone());
                let (ih_id, _ih) = d.fresh_local(Expr::sort(Level::zero()));
                let r = d.mk_lam(
                    ih_id,
                    BinderInfo::Default,
                    Expr::sort(Level::zero()),
                    Expr::const_str("False"),
                );
                d.finish_child(d.mk_lam(m_id, BinderInfo::Default, nat.clone(), r))
            };
            let rec = Expr::apps(
                Expr::const_(
                    Name::from_string("Nat.rec"),
                    vec![Level::succ(Level::zero())],
                ),
                [motive, Expr::const_str("True"), succ_case, n.clone()],
            );
            c.finish(c.mk_lam(n_id, BinderInfo::Default, nat.clone(), rec))
        };
        // From h : zero = succ k  ->  False  (Eq.subst nat_disc + True.intro), and
        // False.elim into a Prop conclusion.
        let false_from_zero_eq_succ = |k: Expr, h: Expr| -> Expr {
            Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.subst"),
                    vec![Level::succ(Level::zero())],
                ),
                [
                    nat.clone(),
                    nat_disc.clone(),
                    nzero.clone(),
                    succ(k),
                    h,
                    Expr::const_str("True.intro"),
                ],
            )
        };
        let false_elim_prop = |contra: Expr, concl: Expr| -> Expr {
            Expr::apps(
                Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
                [concl, contra],
            )
        };
        // natPred z := Nat.rec.{1} (fun _ => Nat) zero (fun p _ => p) z ; succ_inj via congrArg.
        let nat_pred = {
            let mut c = EnvDeclBuilder::new();
            let (z_id, z) = c.fresh_local(nat.clone());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&c);
                let (w_id, _w) = d.fresh_local(nat.clone());
                d.finish_child(d.mk_lam(w_id, BinderInfo::Default, nat.clone(), nat.clone()))
            };
            let succ_case = {
                let mut d = EnvDeclBuilder::child_of(&c);
                let (pp_id, pp) = d.fresh_local(nat.clone());
                let (ih_id, _ih) = d.fresh_local(nat.clone());
                let r = d.mk_lam(ih_id, BinderInfo::Default, nat.clone(), pp);
                d.finish_child(d.mk_lam(pp_id, BinderInfo::Default, nat.clone(), r))
            };
            let rec = Expr::apps(
                Expr::const_(
                    Name::from_string("Nat.rec"),
                    vec![Level::succ(Level::zero())],
                ),
                [motive, nzero.clone(), succ_case, z.clone()],
            );
            c.finish(c.mk_lam(z_id, BinderInfo::Default, nat.clone(), rec))
        };
        let succ_inj = |m: Expr, n: Expr, h: Expr| -> Expr {
            let l1 = Level::succ(Level::zero());
            Expr::apps(
                Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
                [
                    nat.clone(),
                    nat.clone(),
                    succ(m),
                    succ(n),
                    nat_pred.clone(),
                    h,
                ],
            )
        };

        // motive_a(a) := forall b, bvLen a = bvLen b -> goal a b
        let mk_motive_a = || {
            let mut c = EnvDeclBuilder::new();
            let (a_id, a) = c.fresh_local(list_bool());
            let body = {
                let mut d = EnvDeclBuilder::child_of(&c);
                let (b_id, bb) = d.fresh_local(list_bool());
                let lenh = eq_nat(bvlen(a.clone()), bvlen(bb.clone()));
                let (h_id, _h) = d.fresh_local(lenh.clone());
                let g = goal(a.clone(), bb.clone());
                let inner = d.mk_pi(h_id, BinderInfo::Default, lenh, g);
                d.finish_child(d.mk_pi(b_id, BinderInfo::Default, list_bool(), inner))
            };
            c.finish(c.mk_lam(a_id, BinderInfo::Default, list_bool(), body))
        };

        // nil-a minor : motive_a nil
        let nil_a_minor = {
            let mut c = EnvDeclBuilder::new();
            let (b_id, bb) = c.fresh_local(list_bool());
            let lenh_ty = eq_nat(bvlen(nil_b()), bvlen(bb.clone()));
            let (h_id, h) = c.fresh_local(lenh_ty.clone());
            let inner_motive = {
                let mut d = EnvDeclBuilder::child_of(&c);
                let (x_id, x) = d.fresh_local(list_bool());
                let hx = eq_nat(bvlen(nil_b()), bvlen(x.clone()));
                let body = Expr::arrow(hx, goal(nil_b(), x.clone()));
                d.finish_child(d.mk_lam(x_id, BinderInfo::Default, list_bool(), body))
            };
            // b=nil minor : (bvLen nil = bvLen nil) -> goal nil nil ; goal nil nil reduces to (true=true)
            let bnil_case = {
                let mut d = EnvDeclBuilder::child_of(&c);
                let hh = eq_nat(bvlen(nil_b()), bvlen(nil_b()));
                let (i_id, _i) = d.fresh_local(hh.clone());
                d.finish_child(d.mk_lam(i_id, BinderInfo::Default, hh, eq_refl_bool(btrue())))
            };
            // b=cons b0 bs minor : (b0)(bs)(ih)(hbad : zero = succ(bvLen bs)) -> goal nil (cons b0 bs)
            let bcons_case = {
                let mut d = EnvDeclBuilder::child_of(&c);
                let (b0_id, b0) = d.fresh_local(bool_ty());
                let (bs_id, bs) = d.fresh_local(list_bool());
                let ih_ty = Expr::arrow(
                    eq_nat(bvlen(nil_b()), bvlen(bs.clone())),
                    goal(nil_b(), bs.clone()),
                );
                let (ih_id, _ih) = d.fresh_local(ih_ty.clone());
                let hbad_ty = eq_nat(bvlen(nil_b()), bvlen(cons_b(b0.clone(), bs.clone())));
                let (hbad_id, hbad) = d.fresh_local(hbad_ty.clone());
                let contra = false_from_zero_eq_succ(bvlen(bs.clone()), hbad);
                let concl = goal(nil_b(), cons_b(b0.clone(), bs.clone()));
                let body = false_elim_prop(contra, concl);
                let r = d.mk_lam(hbad_id, BinderInfo::Default, hbad_ty, body);
                let r = d.mk_lam(ih_id, BinderInfo::Default, ih_ty, r);
                let r = d.mk_lam(bs_id, BinderInfo::Default, list_bool(), r);
                d.finish_child(d.mk_lam(b0_id, BinderInfo::Default, bool_ty(), r))
            };
            let rec = list_rec_prop(inner_motive, bnil_case, bcons_case, bb.clone());
            let applied = Expr::app(rec, h);
            let r = c.mk_lam(h_id, BinderInfo::Default, lenh_ty, applied);
            c.finish(c.mk_lam(b_id, BinderInfo::Default, list_bool(), r))
        };

        // cons-a minor : (a0)(as)(ih_a : motive_a as) -> motive_a (cons a0 as)
        let cons_a_minor = {
            let mut c = EnvDeclBuilder::new();
            let (a0_id, a0) = c.fresh_local(bool_ty());
            let (as_id, as_) = c.fresh_local(list_bool());
            let ih_a_ty = {
                let mut d = EnvDeclBuilder::child_of(&c);
                let (b_id, bb) = d.fresh_local(list_bool());
                let hx = eq_nat(bvlen(as_.clone()), bvlen(bb.clone()));
                let (h_id, _h) = d.fresh_local(hx.clone());
                let inner = d.mk_pi(h_id, BinderInfo::Default, hx, goal(as_.clone(), bb.clone()));
                d.finish_child(d.mk_pi(b_id, BinderInfo::Default, list_bool(), inner))
            };
            let (ih_a_id, ih_a) = c.fresh_local(ih_a_ty.clone());
            let aa = cons_b(a0.clone(), as_.clone());
            let body = {
                let mut d = EnvDeclBuilder::child_of(&c);
                let (b_id, bb) = d.fresh_local(list_bool());
                let lenh_ty = eq_nat(bvlen(aa.clone()), bvlen(bb.clone()));
                let (h_id, h) = d.fresh_local(lenh_ty.clone());
                let inner_motive = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (x_id, x) = e.fresh_local(list_bool());
                    let hx = eq_nat(bvlen(aa.clone()), bvlen(x.clone()));
                    let bdy = Expr::arrow(hx, goal(aa.clone(), x.clone()));
                    e.finish_child(e.mk_lam(x_id, BinderInfo::Default, list_bool(), bdy))
                };
                // b=nil minor : (i : succ(bvLen as) = zero) -> goal aa nil  (absurd via symm)
                let bnil_case = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let hh_ty = eq_nat(bvlen(aa.clone()), bvlen(nil_b()));
                    let (i_id, i) = e.fresh_local(hh_ty.clone());
                    let symm = Expr::apps(
                        Expr::const_(
                            Name::from_string("Eq.symm"),
                            vec![Level::succ(Level::zero())],
                        ),
                        [nat.clone(), bvlen(aa.clone()), bvlen(nil_b()), i],
                    );
                    let contra = false_from_zero_eq_succ(bvlen(as_.clone()), symm);
                    let concl = goal(aa.clone(), nil_b());
                    let bdy = false_elim_prop(contra, concl);
                    e.finish_child(e.mk_lam(i_id, BinderInfo::Default, hh_ty, bdy))
                };
                // b=cons b0 bs minor : (b0)(bs)(ih_b)(i : succ(bvLen as)=succ(bvLen bs)) -> goal aa (cons b0 bs)
                let bcons_case = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (b0_id, b0) = e.fresh_local(bool_ty());
                    let (bs_id, bs) = e.fresh_local(list_bool());
                    let ihb_ty = Expr::arrow(
                        eq_nat(bvlen(aa.clone()), bvlen(bs.clone())),
                        goal(aa.clone(), bs.clone()),
                    );
                    let (ihb_id, _ihb) = e.fresh_local(ihb_ty.clone());
                    let bbcons = cons_b(b0.clone(), bs.clone());
                    let hh_ty = eq_nat(bvlen(aa.clone()), bvlen(bbcons.clone()));
                    let (i_id, i) = e.fresh_local(hh_ty.clone());
                    let htail = succ_inj(bvlen(as_.clone()), bvlen(bs.clone()), i);
                    // 2x2 nested Bool.rec on a0 then b0 with SIMPLE (non-dependent-
                    // equation) goal-shaped motives — the structure validated in
                    // isolation by `PROBE_boolrec_helper_minor`. Equal-head leaves use
                    // the coercion helper (carrying the def-eq goal(cons LIT)=goal in
                    // its signature); unequal-head leaves are `Eq.refl false`.
                    // inner Bool.rec over b0 for fixed a0 literal `av`.
                    let inner_b0 = |av: Expr, av_t: bool| -> Expr {
                        let mot = {
                            let mut g = EnvDeclBuilder::child_of(&e);
                            let (y_id, y) = g.fresh_local(bool_ty());
                            g.finish_child(g.mk_lam(
                                y_id,
                                BinderInfo::Default,
                                bool_ty(),
                                goal(
                                    cons_b(av.clone(), as_.clone()),
                                    cons_b(y.clone(), bs.clone()),
                                ),
                            ))
                        };
                        let leaf = |bv_t: bool| -> Expr {
                            if av_t == bv_t {
                                let helper = if bv_t {
                                    "Clean.BVC.goalConsCongTrue"
                                } else {
                                    "Clean.BVC.goalConsCongFalse"
                                };
                                Expr::apps(
                                    Expr::const_str(helper),
                                    [
                                        as_.clone(),
                                        bs.clone(),
                                        Expr::apps(ih_a.clone(), [bs.clone(), htail.clone()]),
                                    ],
                                )
                            } else {
                                eq_refl_bool(bfalse())
                            }
                        };
                        Expr::apps(
                            Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
                            [mot, leaf(false), leaf(true), b0.clone()],
                        )
                    };
                    // outer Bool.rec over a0 : motive x := goal (cons x as)(cons b0 bs)
                    let outer_mot = {
                        let mut f = EnvDeclBuilder::child_of(&e);
                        let (x_id, x) = f.fresh_local(bool_ty());
                        f.finish_child(f.mk_lam(
                            x_id,
                            BinderInfo::Default,
                            bool_ty(),
                            goal(cons_b(x.clone(), as_.clone()), bbcons.clone()),
                        ))
                    };
                    let rec = Expr::apps(
                        Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
                        [
                            outer_mot,
                            inner_b0(bfalse(), false),
                            inner_b0(btrue(), true),
                            a0.clone(),
                        ],
                    );
                    let r = e.mk_lam(i_id, BinderInfo::Default, hh_ty, rec);
                    let r = e.mk_lam(ihb_id, BinderInfo::Default, ihb_ty, r);
                    let r = e.mk_lam(bs_id, BinderInfo::Default, list_bool(), r);
                    e.finish_child(e.mk_lam(b0_id, BinderInfo::Default, bool_ty(), r))
                };
                let rec = list_rec_prop(inner_motive, bnil_case, bcons_case, bb.clone());
                let applied = Expr::app(rec, h);
                let r = d.mk_lam(h_id, BinderInfo::Default, lenh_ty, applied);
                d.finish_child(d.mk_lam(b_id, BinderInfo::Default, list_bool(), r))
            };
            let r = c.mk_lam(ih_a_id, BinderInfo::Default, ih_a_ty, body);
            let r = c.mk_lam(as_id, BinderInfo::Default, list_bool(), r);
            c.finish(c.mk_lam(a0_id, BinderInfo::Default, bool_ty(), r))
        };

        let motive_a = mk_motive_a();
        let ty = {
            let mut c = EnvDeclBuilder::new();
            let (a_id, a) = c.fresh_local(list_bool());
            let (b_id, bb) = c.fresh_local(list_bool());
            let lenh = eq_nat(bvlen(a.clone()), bvlen(bb.clone()));
            let (h_id, _h) = c.fresh_local(lenh.clone());
            let g = goal(a.clone(), bb.clone());
            let t = c.mk_pi(h_id, BinderInfo::Default, lenh, g);
            let t = c.mk_pi(b_id, BinderInfo::Default, list_bool(), t);
            c.finish(c.mk_pi(a_id, BinderInfo::Default, list_bool(), t))
        };
        let val = {
            let mut c = EnvDeclBuilder::new();
            let (a_id, a) = c.fresh_local(list_bool());
            let (b_id, bb) = c.fresh_local(list_bool());
            let lenh = eq_nat(bvlen(a.clone()), bvlen(bb.clone()));
            let (h_id, h) = c.fresh_local(lenh.clone());
            let rec = list_rec_prop(
                motive_a.clone(),
                nil_a_minor.clone(),
                cons_a_minor.clone(),
                a.clone(),
            );
            let applied = Expr::apps(rec, [bb.clone(), h]);
            let r = c.mk_lam(h_id, BinderInfo::Default, lenh, applied);
            let r = c.mk_lam(b_id, BinderInfo::Default, list_bool(), r);
            c.finish(c.mk_lam(a_id, BinderInfo::Default, list_bool(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::BEQ_EQ_ISZERO_SUB),
            level_params: vec![],
            type_: ty,
            value: val,
        })?;

        self.register_eq_value_bridge()?;
        Ok(())
    }

    /// `eq_value_bridge` — the composed EQ register-value equality. Proof:
    ///   sub := addRecM a (bvNot b) true ;  Z := bvIsZero sub
    ///   (1) iteVal_not Z ve vt : bvIteVal (not Z) ve vt = bvIteVal Z vt ve
    ///   (2) Eq.symm (beq_eq_isZero_sub a b h) : Z = bvBeq a b      [as `bvIsZero sub = bvBeq a b`]
    ///   (3) congrArg (fun p => bvIteVal p vt ve) (2)
    ///         : bvIteVal Z vt ve = bvIteVal (bvBeq a b) vt ve
    ///   Eq.trans (1) (3).
    fn register_eq_value_bridge(&mut self) -> Result<(), EnvError> {
        let nat = nat_ty();
        let eq_nat = |x: Expr, y: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [nat.clone(), x, y],
            )
        };
        let bvlen = |xs: Expr| Expr::app(Expr::const_str(names::BV_LEN), xs);
        let z_of = |a: Expr, b: Expr| bv_is_zero(add_rec_m(a, bv_not(b), btrue()));
        let lhs = |a: Expr, b: Expr, vt: Expr, ve: Expr| {
            bv_ite_val(bnot(z_of(a.clone(), b.clone())), ve, vt)
        };
        let rhs = |a: Expr, b: Expr, vt: Expr, ve: Expr| bv_ite_val(bv_beq(a, b), vt, ve);

        let ty = {
            let mut c = EnvDeclBuilder::new();
            let (a_id, a) = c.fresh_local(list_bool());
            let (b_id, bb) = c.fresh_local(list_bool());
            let (vt_id, vt) = c.fresh_local(list_bool());
            let (ve_id, ve) = c.fresh_local(list_bool());
            let lenh = eq_nat(bvlen(a.clone()), bvlen(bb.clone()));
            let (h_id, _h) = c.fresh_local(lenh.clone());
            let concl = eq_list(
                lhs(a.clone(), bb.clone(), vt.clone(), ve.clone()),
                rhs(a.clone(), bb.clone(), vt.clone(), ve.clone()),
            );
            let t = c.mk_pi(h_id, BinderInfo::Default, lenh, concl);
            let t = c.mk_pi(ve_id, BinderInfo::Default, list_bool(), t);
            let t = c.mk_pi(vt_id, BinderInfo::Default, list_bool(), t);
            let t = c.mk_pi(b_id, BinderInfo::Default, list_bool(), t);
            c.finish(c.mk_pi(a_id, BinderInfo::Default, list_bool(), t))
        };
        let val = {
            let mut c = EnvDeclBuilder::new();
            let (a_id, a) = c.fresh_local(list_bool());
            let (b_id, bb) = c.fresh_local(list_bool());
            let (vt_id, vt) = c.fresh_local(list_bool());
            let (ve_id, ve) = c.fresh_local(list_bool());
            let lenh = eq_nat(bvlen(a.clone()), bvlen(bb.clone()));
            let (h_id, h) = c.fresh_local(lenh.clone());
            let z = z_of(a.clone(), bb.clone());
            // (1) iteVal_not z ve vt : bvIteVal (not z) ve vt = bvIteVal z vt ve
            let step1 = Expr::apps(
                Expr::const_str(names::ITE_VAL_NOT),
                [z.clone(), ve.clone(), vt.clone()],
            );
            // (2) symm (beq_eq_isZero_sub a b h) : z = bvBeq a b
            let bridge = Expr::apps(
                Expr::const_str(names::BEQ_EQ_ISZERO_SUB),
                [a.clone(), bb.clone(), h],
            );
            let beq = bv_beq(a.clone(), bb.clone());
            let symm = Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.symm"),
                    vec![Level::succ(Level::zero())],
                ),
                [bool_ty(), beq.clone(), z.clone(), bridge],
            );
            // (3) congrArg (fun p:Bool => bvIteVal p vt ve) symm : bvIteVal z vt ve = bvIteVal beq vt ve
            let cong_fn = {
                let mut d = EnvDeclBuilder::child_of(&c);
                let (p_id, p) = d.fresh_local(bool_ty());
                d.finish_child(d.mk_lam(
                    p_id,
                    BinderInfo::Default,
                    bool_ty(),
                    bv_ite_val(p, vt.clone(), ve.clone()),
                ))
            };
            // @congrArg.{1,1} Bool (List Bool) z beq cong_fn symm
            let l1 = Level::succ(Level::zero());
            let step3 = Expr::apps(
                Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
                [
                    bool_ty(),
                    list_bool(),
                    z.clone(),
                    beq.clone(),
                    cong_fn,
                    symm,
                ],
            );
            // Eq.trans step1 step3
            let mid = bv_ite_val(z.clone(), vt.clone(), ve.clone());
            let proof = eq_trans_list(
                bv_ite_val(bnot(z), ve.clone(), vt.clone()),
                mid,
                bv_ite_val(beq, vt.clone(), ve.clone()),
                step1,
                step3,
            );
            let r = c.mk_lam(h_id, BinderInfo::Default, lenh, proof);
            let r = c.mk_lam(ve_id, BinderInfo::Default, list_bool(), r);
            let r = c.mk_lam(vt_id, BinderInfo::Default, list_bool(), r);
            let r = c.mk_lam(b_id, BinderInfo::Default, list_bool(), r);
            c.finish(c.mk_lam(a_id, BinderInfo::Default, list_bool(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::EQ_VALUE_BRIDGE),
            level_params: vec![],
            type_: ty,
            value: val,
        })?;
        Ok(())
    }

    /// The ULT predicate + register-value bridge. `bvUlt` is a real unsigned-LT
    /// (LSB-first fold); `ult_value_bridge` is PURE branch-inversion (iteVal_not),
    /// since BOTH the machine (Ite(¬(a<b),0,1)) and IR (Ite(a<b,1,0)) sides use the
    /// SAME `BvULt` predicate — no carry/borrow bridge is needed (traced #ult). No
    /// length guard (branch-inversion holds for all operands/lengths).
    fn register_ult_predicate(&mut self) -> Result<(), EnvError> {
        let lbb = Expr::arrow(list_bool(), Expr::arrow(list_bool(), bool_ty()));
        // ── carryOut : List Bool → List Bool → Bool → Bool ───────────────────
        // Final carry-out of the ripple adder, threaded by `maj` (the SUBS C flag
        // source). Same recursion shape as addRecM but returns the carry, not the
        // sum list. nil ↦ fun ys c => c ; cons a as ih ↦ fun ys c => ih (btail ys)
        // (maj a (bhead ys) c).
        {
            let consumer = Expr::arrow(list_bool(), Expr::arrow(bool_ty(), bool_ty()));
            let maj = |x: Expr, y: Expr, z: Expr| {
                Expr::apps(
                    Expr::const_str(crate::bitvec_inductive::names::MAJ),
                    [x, y, z],
                )
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (xs_id, xs) = b.fresh_local(list_bool());
                let (ys_id, ys) = b.fresh_local(list_bool());
                let (c_id, cc0) = b.fresh_local(bool_ty());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(list_bool());
                    c.finish_child(c.mk_lam(
                        w_id,
                        BinderInfo::Default,
                        list_bool(),
                        consumer.clone(),
                    ))
                };
                // nil_case : fun ys c => c
                let nil_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (ys2_id, _ys2) = c.fresh_local(list_bool());
                    let (cc_id, cc) = c.fresh_local(bool_ty());
                    let r = c.mk_lam(cc_id, BinderInfo::Default, bool_ty(), cc);
                    c.finish_child(c.mk_lam(ys2_id, BinderInfo::Default, list_bool(), r))
                };
                // cons_case a as ih = fun ys c => ih (btail ys) (maj a (bhead ys) c)
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (a_id, a) = c.fresh_local(bool_ty());
                    let (as_id, _as) = c.fresh_local(list_bool());
                    let (ih_id, ih) = c.fresh_local(consumer.clone());
                    let inner = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (ys2_id, ys2) = d.fresh_local(list_bool());
                        let (cc_id, cc) = d.fresh_local(bool_ty());
                        let bvi_bhead = |v: Expr| {
                            Expr::app(Expr::const_str(crate::bitvec_inductive::names::BHEAD), v)
                        };
                        let bvi_btail = |v: Expr| {
                            Expr::app(Expr::const_str(crate::bitvec_inductive::names::BTAIL), v)
                        };
                        let nextc = maj(a.clone(), bvi_bhead(ys2.clone()), cc.clone());
                        let body = Expr::apps(ih.clone(), [bvi_btail(ys2.clone()), nextc]);
                        let r = d.mk_lam(cc_id, BinderInfo::Default, bool_ty(), body);
                        d.finish_child(d.mk_lam(ys2_id, BinderInfo::Default, list_bool(), r))
                    };
                    let r = c.mk_lam(ih_id, BinderInfo::Default, consumer.clone(), inner);
                    let r = c.mk_lam(as_id, BinderInfo::Default, list_bool(), r);
                    c.finish_child(c.mk_lam(a_id, BinderInfo::Default, bool_ty(), r))
                };
                let rec = Expr::apps(
                    Expr::const_(
                        Name::from_string("List.rec"),
                        vec![Level::succ(Level::zero()), Level::zero()],
                    ),
                    [bool_ty(), motive, nil_case, cons_case, xs.clone()],
                );
                let applied = Expr::apps(rec, [ys.clone(), cc0.clone()]);
                let r = b.mk_lam(c_id, BinderInfo::Default, bool_ty(), applied);
                let r = b.mk_lam(ys_id, BinderInfo::Default, list_bool(), r);
                b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_bool(), r))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::CARRY_OUT),
                level_params: vec![],
                type_: Expr::arrow(
                    list_bool(),
                    Expr::arrow(list_bool(), Expr::arrow(bool_ty(), bool_ty())),
                ),
                value: val,
                is_reducible: true,
            })?;
        }

        // ── bvUlt a b := Bool.not (carryOut a (bvNot b) true) ─────────────────
        // The borrow form: a <u b ⟺ borrow-out of (a - b) = a + ¬b + 1, i.e. the
        // carry-out is 0. This is a GENUINE unsigned-less-than (verified). (ult/ule
        // soundness rests on branch-inversion regardless, but this upgrades bvUlt
        // from opaque to genuinely-computing — and is REQUIRED for the faithful
        // signed bvSLt_real := bvUlt(flipMsb a)(flipMsb b).)
        {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(list_bool());
                let (bb_id, bb) = b.fresh_local(list_bool());
                let co = Expr::apps(
                    Expr::const_str(names::CARRY_OUT),
                    [a.clone(), bv_not(bb.clone()), btrue()],
                );
                let body = bnot(co);
                let r = b.mk_lam(bb_id, BinderInfo::Default, list_bool(), body);
                b.finish(b.mk_lam(a_id, BinderInfo::Default, list_bool(), r))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::BV_ULT),
                level_params: vec![],
                type_: lbb,
                value: val,
                is_reducible: true,
            })?;
        }

        // ── ult_value_bridge : ∀ a b vt ve,
        //      bvIteVal (Bool.not (bvUlt a b)) ve vt = bvIteVal (bvUlt a b) vt ve
        // = iteVal_not (bvUlt a b) ve vt   (pure branch-inversion).
        {
            let ult = |a: Expr, b: Expr| Expr::apps(Expr::const_str(names::BV_ULT), [a, b]);
            let ty = {
                let mut c = EnvDeclBuilder::new();
                let (a_id, a) = c.fresh_local(list_bool());
                let (b_id, bb) = c.fresh_local(list_bool());
                let (vt_id, vt) = c.fresh_local(list_bool());
                let (ve_id, ve) = c.fresh_local(list_bool());
                let p = ult(a.clone(), bb.clone());
                let concl = eq_list(
                    bv_ite_val(bnot(p.clone()), ve.clone(), vt.clone()),
                    bv_ite_val(p, vt.clone(), ve.clone()),
                );
                let t = c.mk_pi(ve_id, BinderInfo::Default, list_bool(), concl);
                let t = c.mk_pi(vt_id, BinderInfo::Default, list_bool(), t);
                let t = c.mk_pi(b_id, BinderInfo::Default, list_bool(), t);
                c.finish(c.mk_pi(a_id, BinderInfo::Default, list_bool(), t))
            };
            let val = {
                let mut c = EnvDeclBuilder::new();
                let (a_id, a) = c.fresh_local(list_bool());
                let (b_id, bb) = c.fresh_local(list_bool());
                let (vt_id, vt) = c.fresh_local(list_bool());
                let (ve_id, ve) = c.fresh_local(list_bool());
                let p = ult(a.clone(), bb.clone());
                // iteVal_not p ve vt : bvIteVal (not p) ve vt = bvIteVal p vt ve
                let proof = Expr::apps(
                    Expr::const_str(names::ITE_VAL_NOT),
                    [p, ve.clone(), vt.clone()],
                );
                let r = c.mk_lam(ve_id, BinderInfo::Default, list_bool(), proof);
                let r = c.mk_lam(vt_id, BinderInfo::Default, list_bool(), r);
                let r = c.mk_lam(b_id, BinderInfo::Default, list_bool(), r);
                c.finish(c.mk_lam(a_id, BinderInfo::Default, list_bool(), r))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::ULT_VALUE_BRIDGE),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }
        Ok(())
    }

    /// The ULE predicate + register-value bridge. `bvULe := Or(bvUlt, bvBeq)`
    /// (unsigned <= = < or =). `ule_value_bridge` composes the subtract-zero bridge
    /// (bvIsZero(sub) = bvBeq) + De Morgan (And(¬p,¬q) = ¬(Or p q)) + branch-
    /// inversion (iteVal_not): the machine inverted Hi-condition
    /// `Ite(And(¬(a<b), ¬(a-b==0)), 0, 1)` == IR `Ite(a<=b, 1, 0)`. Length-guarded
    /// (the subtract-zero bridge needs equal width).
    fn register_ule_predicate(&mut self) -> Result<(), EnvError> {
        // ── bvULe a b := Bool.or (bvUlt a b) (bvBeq a b) ──────────────────────
        {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(list_bool());
                let (bb_id, bb) = b.fresh_local(list_bool());
                let body = bor(
                    bv_ult_op(a.clone(), bb.clone()),
                    bv_beq(a.clone(), bb.clone()),
                );
                let r = b.mk_lam(bb_id, BinderInfo::Default, list_bool(), body);
                b.finish(b.mk_lam(a_id, BinderInfo::Default, list_bool(), r))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::BV_ULE),
                level_params: vec![],
                type_: Expr::arrow(list_bool(), Expr::arrow(list_bool(), bool_ty())),
                value: val,
                is_reducible: true,
            })?;
        }

        // ── demorgan_and_not : ∀ p q, and (not p) (not q) = not (or p q) ──────
        // 2×2 Bool.rec, ground per leaf (refl).
        {
            let goal =
                |p: Expr, q: Expr| eq_bool(band(bnot(p.clone()), bnot(q.clone())), bnot(bor(p, q)));
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(bool_ty());
                let (q_id, q) = b.fresh_local(bool_ty());
                let g = goal(p.clone(), q.clone());
                let t = b.mk_pi(q_id, BinderInfo::Default, bool_ty(), g);
                b.finish(b.mk_pi(p_id, BinderInfo::Default, bool_ty(), t))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(bool_ty());
                let (q_id, q) = b.fresh_local(bool_ty());
                // outer motive over p': fun p' => goal p' q
                let outer_mot = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (x_id, x) = c.fresh_local(bool_ty());
                    c.finish_child(c.mk_lam(
                        x_id,
                        BinderInfo::Default,
                        bool_ty(),
                        goal(x, q.clone()),
                    ))
                };
                let inner_for = |pv: Expr| {
                    let c = EnvDeclBuilder::child_of(&b);
                    let mot = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (y_id, y) = d.fresh_local(bool_ty());
                        d.finish_child(d.mk_lam(
                            y_id,
                            BinderInfo::Default,
                            bool_ty(),
                            goal(pv.clone(), y),
                        ))
                    };
                    // each leaf: ground Bool eq -> refl of the LHS value.
                    let leaf = |qv: Expr| eq_refl_bool(band(bnot(pv.clone()), bnot(qv)));
                    let rec = Expr::apps(
                        Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
                        [mot, leaf(bfalse()), leaf(btrue()), q.clone()],
                    );
                    c.finish_child(rec)
                };
                let rec = Expr::apps(
                    Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
                    [
                        outer_mot,
                        inner_for(bfalse()),
                        inner_for(btrue()),
                        p.clone(),
                    ],
                );
                let r = b.mk_lam(q_id, BinderInfo::Default, bool_ty(), rec);
                b.finish(b.mk_lam(p_id, BinderInfo::Default, bool_ty(), r))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::DEMORGAN_AND_NOT),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }

        // ── ule_value_bridge ──────────────────────────────────────────────────
        {
            let nat = nat_ty();
            let eq_nat = |x: Expr, y: Expr| {
                Expr::apps(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    [nat.clone(), x, y],
                )
            };
            let bvlen = |xs: Expr| Expr::app(Expr::const_str(names::BV_LEN), xs);
            let sub_of = |a: Expr, b: Expr| add_rec_m(a, bv_not(b), btrue());
            let iz = |a: Expr, b: Expr| bv_is_zero(sub_of(a, b));
            // machine predicate M(a,b) = and (not (ult a b)) (not (isZero (sub a b)))
            let m_pred =
                |a: Expr, b: Expr| band(bnot(bv_ult_op(a.clone(), b.clone())), bnot(iz(a, b)));
            let ty = {
                let mut c = EnvDeclBuilder::new();
                let (a_id, a) = c.fresh_local(list_bool());
                let (b_id, bb) = c.fresh_local(list_bool());
                let (vt_id, vt) = c.fresh_local(list_bool());
                let (ve_id, ve) = c.fresh_local(list_bool());
                let lenh = eq_nat(bvlen(a.clone()), bvlen(bb.clone()));
                let (h_id, _h) = c.fresh_local(lenh.clone());
                let concl = eq_list(
                    bv_ite_val(m_pred(a.clone(), bb.clone()), ve.clone(), vt.clone()),
                    bv_ite_val(bv_ule_op(a.clone(), bb.clone()), vt.clone(), ve.clone()),
                );
                let t = c.mk_pi(h_id, BinderInfo::Default, lenh, concl);
                let t = c.mk_pi(ve_id, BinderInfo::Default, list_bool(), t);
                let t = c.mk_pi(vt_id, BinderInfo::Default, list_bool(), t);
                let t = c.mk_pi(b_id, BinderInfo::Default, list_bool(), t);
                c.finish(c.mk_pi(a_id, BinderInfo::Default, list_bool(), t))
            };
            let val = {
                let mut c = EnvDeclBuilder::new();
                let (a_id, a) = c.fresh_local(list_bool());
                let (b_id, bb) = c.fresh_local(list_bool());
                let (vt_id, vt) = c.fresh_local(list_bool());
                let (ve_id, ve) = c.fresh_local(list_bool());
                let lenh = eq_nat(bvlen(a.clone()), bvlen(bb.clone()));
                let (h_id, h) = c.fresh_local(lenh.clone());
                let ult = bv_ult_op(a.clone(), bb.clone());
                let beq = bv_beq(a.clone(), bb.clone());
                let m = m_pred(a.clone(), bb.clone()); // and(¬ult, ¬(isZero sub))
                let m_beq = band(bnot(ult.clone()), bnot(beq.clone())); // and(¬ult, ¬beq)
                let not_ule = bnot(bor(ult.clone(), beq.clone())); // ¬(or ult beq) = ¬(bvULe)  (defeq)
                let ule = bv_ule_op(a.clone(), bb.clone());
                // step1: m = m_beq, via congrArg (fun z => and(¬ult, ¬z)) (beq_eq_isZero_sub a b h : beq = isZero sub).
                //   bridge h : bvBeq a b = bvIsZero(sub) ; symm -> isZero = beq ; we rewrite isZero -> beq.
                let bridge = Expr::apps(
                    Expr::const_str(names::BEQ_EQ_ISZERO_SUB),
                    [a.clone(), bb.clone(), h],
                );
                // bridge : beq = isZero(sub). congrArg (fun z => and(¬ult,¬z)) bridge : and(¬ult,¬beq) = and(¬ult,¬isZero)
                let cong_fn1 = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (z_id, z) = d.fresh_local(bool_ty());
                    d.finish_child(d.mk_lam(
                        z_id,
                        BinderInfo::Default,
                        bool_ty(),
                        band(bnot(ult.clone()), bnot(z)),
                    ))
                };
                let l1 = Level::succ(Level::zero());
                let cg_bool = |a1: Expr, a2: Expr, f: Expr, hh: Expr| {
                    Expr::apps(
                        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
                        [bool_ty(), bool_ty(), a1, a2, f, hh],
                    )
                };
                // congrArg cong_fn1 bridge : and(¬ult, ¬beq) = and(¬ult, ¬isZero) = m
                let step1 = cg_bool(beq.clone(), iz(a.clone(), bb.clone()), cong_fn1, bridge);
                // step2: m_beq = not_ule, via demorgan_and_not ult beq : and(¬ult,¬beq) = ¬(or ult beq)
                let step2 = Expr::apps(
                    Expr::const_str(names::DEMORGAN_AND_NOT),
                    [ult.clone(), beq.clone()],
                );
                // We want a proof: m = not_ule.  Eq.trans (Eq.symm step1) step2.
                //   symm step1 : m = m_beq ; step2 : m_beq = not_ule.
                let symm_step1 = Expr::apps(
                    Expr::const_(
                        Name::from_string("Eq.symm"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [bool_ty(), m_beq.clone(), m.clone(), step1],
                );
                let eq_trans_bool = |x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr| {
                    Expr::apps(
                        Expr::const_(
                            Name::from_string("Eq.trans"),
                            vec![Level::succ(Level::zero())],
                        ),
                        [bool_ty(), x, y, z, h1, h2],
                    )
                };
                let m_eq_notule =
                    eq_trans_bool(m.clone(), m_beq.clone(), not_ule.clone(), symm_step1, step2);
                // step3: congrArg (fun p => bvIteVal p ve vt) (m_eq_notule) :
                //   bvIteVal m ve vt = bvIteVal not_ule ve vt
                let cong_fn3 = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (p_id, p) = d.fresh_local(bool_ty());
                    d.finish_child(d.mk_lam(
                        p_id,
                        BinderInfo::Default,
                        bool_ty(),
                        bv_ite_val(p, ve.clone(), vt.clone()),
                    ))
                };
                let cg_ite = |a1: Expr, a2: Expr, f: Expr, hh: Expr| {
                    Expr::apps(
                        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
                        [bool_ty(), list_bool(), a1, a2, f, hh],
                    )
                };
                let step3 = cg_ite(m.clone(), not_ule.clone(), cong_fn3, m_eq_notule);
                // step4: iteVal_not bvULe ve vt : bvIteVal (¬bvULe) ve vt = bvIteVal bvULe vt ve
                //   (¬bvULe ≡ not_ule defeq, since bvULe := or ult beq).
                let step4 = Expr::apps(
                    Expr::const_str(names::ITE_VAL_NOT),
                    [ule.clone(), ve.clone(), vt.clone()],
                );
                // chain: bvIteVal m ve vt = bvIteVal not_ule ve vt = bvIteVal bvULe vt ve.
                let proof = eq_trans_list(
                    bv_ite_val(m, ve.clone(), vt.clone()),
                    bv_ite_val(not_ule, ve.clone(), vt.clone()),
                    bv_ite_val(ule, vt.clone(), ve.clone()),
                    step3,
                    step4,
                );
                let r = c.mk_lam(h_id, BinderInfo::Default, lenh, proof);
                let r = c.mk_lam(ve_id, BinderInfo::Default, list_bool(), r);
                let r = c.mk_lam(vt_id, BinderInfo::Default, list_bool(), r);
                let r = c.mk_lam(b_id, BinderInfo::Default, list_bool(), r);
                c.finish(c.mk_lam(a_id, BinderInfo::Default, list_bool(), r))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::ULE_VALUE_BRIDGE),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }
        Ok(())
    }

    /// The faithful signed-LT predicate: `bvFlipMsb` (flip the MSB = last element)
    /// + `bvSLtReal a b := bvUlt (bvFlipMsb a) (bvFlipMsb b)` (signed compare =
    /// unsigned compare after flipping the sign bit — self-evidently signed-LT,
    /// verified numerically + in-kernel). The N⊕V flag bridge + the slt value
    /// discharge are built separately (the genuine new rung).
    fn register_slt_predicate(&mut self) -> Result<(), EnvError> {
        // ── bvFlipMsb : List Bool → List Bool ─────────────────────────────────
        // Flip the last element. cons x xs ih = listRec xs (cons (¬x) nil)
        //   (fun _ _ _ => cons x ih) — i.e. if xs is nil, [¬x]; else x :: ih.
        {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (xs_id, xs) = b.fresh_local(list_bool());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(list_bool());
                    c.finish_child(c.mk_lam(w_id, BinderInfo::Default, list_bool(), list_bool()))
                };
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (x_id, x) = c.fresh_local(bool_ty());
                    let (t_id, t) = c.fresh_local(list_bool());
                    let (ih_id, ih) = c.fresh_local(list_bool());
                    // listRec t (cons (¬x) nil) (fun _ _ _ => cons x ih)  -- decide nil vs cons of the TAIL
                    let inner_mot = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (z_id, _z) = d.fresh_local(list_bool());
                        d.finish_child(d.mk_lam(
                            z_id,
                            BinderInfo::Default,
                            list_bool(),
                            list_bool(),
                        ))
                    };
                    let inner_nil = cons_b(bnot(x.clone()), nil_b());
                    let inner_cons = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (th_id, _th) = d.fresh_local(bool_ty());
                        let (tt_id, _tt) = d.fresh_local(list_bool());
                        let (tih_id, _tih) = d.fresh_local(list_bool());
                        let body = cons_b(x.clone(), ih.clone());
                        let r = d.mk_lam(tih_id, BinderInfo::Default, list_bool(), body);
                        let r = d.mk_lam(tt_id, BinderInfo::Default, list_bool(), r);
                        d.finish_child(d.mk_lam(th_id, BinderInfo::Default, bool_ty(), r))
                    };
                    let wrec = Expr::apps(
                        Expr::const_(
                            Name::from_string("List.rec"),
                            vec![Level::succ(Level::zero()), Level::zero()],
                        ),
                        [bool_ty(), inner_mot, inner_nil, inner_cons, t.clone()],
                    );
                    let r = c.mk_lam(ih_id, BinderInfo::Default, list_bool(), wrec);
                    let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                    c.finish_child(c.mk_lam(x_id, BinderInfo::Default, bool_ty(), r))
                };
                let rec = Expr::apps(
                    Expr::const_(
                        Name::from_string("List.rec"),
                        vec![Level::succ(Level::zero()), Level::zero()],
                    ),
                    [bool_ty(), motive, nil_b(), cons_case, xs.clone()],
                );
                b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_bool(), rec))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::BV_FLIP_MSB),
                level_params: vec![],
                type_: Expr::arrow(list_bool(), list_bool()),
                value: val,
                is_reducible: true,
            })?;
        }
        // ── bvSLtReal a b := bvUlt (bvFlipMsb a) (bvFlipMsb b) ────────────────
        {
            let flip = |x: Expr| Expr::app(Expr::const_str(names::BV_FLIP_MSB), x);
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(list_bool());
                let (bb_id, bb) = b.fresh_local(list_bool());
                let body = bv_ult_op(flip(a.clone()), flip(bb.clone()));
                let r = b.mk_lam(bb_id, BinderInfo::Default, list_bool(), body);
                b.finish(b.mk_lam(a_id, BinderInfo::Default, list_bool(), r))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::BV_SLT_REAL),
                level_params: vec![],
                type_: Expr::arrow(list_bool(), Expr::arrow(list_bool(), bool_ty())),
                value: val,
                is_reducible: true,
            })?;
        }
        // ── bvLastBit : List Bool → Bool (MSB; false if empty) ────────────────
        // cons x xs ih = listRec xs x (fun _ _ _ => ih) — if xs nil, x; else ih.
        {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (xs_id, xs) = b.fresh_local(list_bool());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(list_bool());
                    c.finish_child(c.mk_lam(w_id, BinderInfo::Default, list_bool(), bool_ty()))
                };
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (x_id, x) = c.fresh_local(bool_ty());
                    let (t_id, t) = c.fresh_local(list_bool());
                    let (ih_id, ih) = c.fresh_local(bool_ty());
                    let inner_mot = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (z_id, _z) = d.fresh_local(list_bool());
                        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, list_bool(), bool_ty()))
                    };
                    let inner_cons = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (th_id, _th) = d.fresh_local(bool_ty());
                        let (tt_id, _tt) = d.fresh_local(list_bool());
                        let (tih_id, _tih) = d.fresh_local(bool_ty());
                        let r = d.mk_lam(tih_id, BinderInfo::Default, bool_ty(), ih.clone());
                        let r = d.mk_lam(tt_id, BinderInfo::Default, list_bool(), r);
                        d.finish_child(d.mk_lam(th_id, BinderInfo::Default, bool_ty(), r))
                    };
                    let wrec = Expr::apps(
                        Expr::const_(
                            Name::from_string("List.rec"),
                            vec![Level::succ(Level::zero()), Level::zero()],
                        ),
                        [bool_ty(), inner_mot, x.clone(), inner_cons, t.clone()],
                    );
                    let r = c.mk_lam(ih_id, BinderInfo::Default, bool_ty(), wrec);
                    let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                    c.finish_child(c.mk_lam(x_id, BinderInfo::Default, bool_ty(), r))
                };
                let rec = Expr::apps(
                    Expr::const_(
                        Name::from_string("List.rec"),
                        vec![Level::succ(Level::zero()), Level::zero()],
                    ),
                    [bool_ty(), motive, bfalse(), cons_case, xs.clone()],
                );
                b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_bool(), rec))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::BV_LAST_BIT),
                level_params: vec![],
                type_: Expr::arrow(list_bool(), bool_ty()),
                value: val,
                is_reducible: true,
            })?;
        }
        // ── bvIsCons : List Bool → Bool (true iff non-empty) ──────────────────
        {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (xs_id, xs) = b.fresh_local(list_bool());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(list_bool());
                    c.finish_child(c.mk_lam(w_id, BinderInfo::Default, list_bool(), bool_ty()))
                };
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (x_id, _x) = c.fresh_local(bool_ty());
                    let (t_id, _t) = c.fresh_local(list_bool());
                    let (ih_id, _ih) = c.fresh_local(bool_ty());
                    let r = c.mk_lam(ih_id, BinderInfo::Default, bool_ty(), btrue());
                    let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                    c.finish_child(c.mk_lam(x_id, BinderInfo::Default, bool_ty(), r))
                };
                let rec = Expr::apps(
                    Expr::const_(
                        Name::from_string("List.rec"),
                        vec![Level::succ(Level::zero()), Level::zero()],
                    ),
                    [bool_ty(), motive, bfalse(), cons_case, xs.clone()],
                );
                b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_bool(), rec))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::BV_IS_CONS),
                level_params: vec![],
                type_: Expr::arrow(list_bool(), bool_ty()),
                value: val,
                is_reducible: true,
            })?;
        }
        self.register_slt_flag_bridge()?;
        Ok(())
    }

    /// `slt_flag_bridge : ∀ a b c, bvIsCons a = true → bvLen a = bvLen b →
    ///     bvSLtReal a b = Bool.xor N V`   (N⊕V signed-overflow, carry-in c generalized)
    /// where N = bvLastBit (addRecM a (bvNot b) c), V = And(bxor(msb a, msb b),
    /// bxor(N, msb a)). PROVED by induction on `a`; the `bvIsCons` guard makes the
    /// nil base ABSURD (the statement degenerates at width 0), so the genuine base
    /// is the SINGLETON (valid for all c — verified). cons-step threads
    /// `maj a0 (¬b0) c` to the tail. Mirrors `beq_eq_isZero_sub`; the inner
    /// tail-nil-check uses goalConsCong-style def-eq-carrying helpers.
    #[allow(clippy::too_many_lines)]
    fn register_slt_flag_bridge(&mut self) -> Result<(), EnvError> {
        let nat = nat_ty();
        let nzero = Expr::const_str("Nat.zero");
        let succ = |n: Expr| Expr::app(Expr::const_str("Nat.succ"), n);
        let bvlen = |xs: Expr| Expr::app(Expr::const_str(names::BV_LEN), xs);
        let eq_nat = |x: Expr, y: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [nat.clone(), x, y],
            )
        };
        let maj = |x: Expr, y: Expr, z: Expr| {
            Expr::apps(
                Expr::const_str(crate::bitvec_inductive::names::MAJ),
                [x, y, z],
            )
        };
        // N,V,goal over (a,b,c).
        let nflag = |a: Expr, b: Expr, c: Expr| last_bit(add_rec_m(a, bv_not(b), c));
        let vflag = |a: Expr, b: Expr, c: Expr| {
            let n = nflag(a.clone(), b.clone(), c);
            band(
                bxor(last_bit(a.clone()), last_bit(b.clone())),
                bxor(n, last_bit(a)),
            )
        };
        let rhs = |a: Expr, b: Expr, c: Expr| {
            bxor(nflag(a.clone(), b.clone(), c.clone()), vflag(a, b, c))
        };
        // LHS GENERALIZED over carry-in c (bvSLtReal hardcodes c=true via bvUlt;
        // the cons-step threads `maj a0 (¬b0) c`, so the lemma must expose c).
        let lhs = |a: Expr, b: Expr, c: Expr| bnot(carry_out(flip_msb(a), bv_not(flip_msb(b)), c));
        let goal =
            |a: Expr, b: Expr, c: Expr| eq_bool(lhs(a.clone(), b.clone(), c.clone()), rhs(a, b, c));
        let istrue = |x: Expr| eq_bool(x, btrue());

        // tf_to_false-style: from h : false = true derive False (for bvIsCons nil = false).
        // disc x := Bool.rec.{1} (fun _=>Prop) True False x  (disc false=False? no: ctor order
        //   false-minor then true-minor: Bool.rec mFalse mTrue x; we want disc false = False,
        //   disc true = True so that h: false=true rewrites False-witness... use: discT x =
        //   Bool.rec (fun _=>Prop) False True x : discT false=False, discT true=True. Then
        //   Eq.subst discT false true (h:false=true) (?:discT false=False) -- need witness of
        //   discT false=False which IS `id`? discT false REDUCES to False, so a proof of
        //   discT false is a proof of False — but we have h:false=true and want False.
        //   Better: discF x := Bool.rec True False x : discF false=True, discF true=False.
        //   Eq.subst discF false true h (True.intro : discF false) : discF true = False. )
        let disc_f = {
            let mut c = EnvDeclBuilder::new();
            let (x_id, x) = c.fresh_local(bool_ty());
            let mot = {
                let mut d = EnvDeclBuilder::child_of(&c);
                let (w_id, _w) = d.fresh_local(bool_ty());
                d.finish_child(d.mk_lam(
                    w_id,
                    BinderInfo::Default,
                    bool_ty(),
                    Expr::sort(Level::zero()),
                ))
            };
            let rec = Expr::apps(
                Expr::const_(
                    Name::from_string("Bool.rec"),
                    vec![Level::succ(Level::zero())],
                ),
                [
                    mot,
                    Expr::const_str("True"),
                    Expr::const_str("False"),
                    x.clone(),
                ],
            );
            c.finish(c.mk_lam(x_id, BinderInfo::Default, bool_ty(), rec))
        };
        // false_of_false_eq_true (h : false = true) : False
        let false_of_ft = |h: Expr| -> Expr {
            Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.subst"),
                    vec![Level::succ(Level::zero())],
                ),
                [
                    bool_ty(),
                    disc_f.clone(),
                    bfalse(),
                    btrue(),
                    h,
                    Expr::const_str("True.intro"),
                ],
            )
        };
        // Nat zero/succ discriminator (mismatch arms).
        let nat_disc = {
            let mut c = EnvDeclBuilder::new();
            let (n_id, n) = c.fresh_local(nat.clone());
            let mot = {
                let mut d = EnvDeclBuilder::child_of(&c);
                let (w_id, _w) = d.fresh_local(nat.clone());
                d.finish_child(d.mk_lam(
                    w_id,
                    BinderInfo::Default,
                    nat.clone(),
                    Expr::sort(Level::zero()),
                ))
            };
            let sc = {
                let mut d = EnvDeclBuilder::child_of(&c);
                let (m_id, _m) = d.fresh_local(nat.clone());
                let (ih_id, _ih) = d.fresh_local(Expr::sort(Level::zero()));
                let r = d.mk_lam(
                    ih_id,
                    BinderInfo::Default,
                    Expr::sort(Level::zero()),
                    Expr::const_str("False"),
                );
                d.finish_child(d.mk_lam(m_id, BinderInfo::Default, nat.clone(), r))
            };
            let rec = Expr::apps(
                Expr::const_(
                    Name::from_string("Nat.rec"),
                    vec![Level::succ(Level::zero())],
                ),
                [mot, Expr::const_str("True"), sc, n.clone()],
            );
            c.finish(c.mk_lam(n_id, BinderInfo::Default, nat.clone(), rec))
        };
        let false_zero_succ = |k: Expr, h: Expr| {
            Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.subst"),
                    vec![Level::succ(Level::zero())],
                ),
                [
                    nat.clone(),
                    nat_disc.clone(),
                    nzero.clone(),
                    succ(k),
                    h,
                    Expr::const_str("True.intro"),
                ],
            )
        };
        let false_elim_b = |contra: Expr, concl: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
                [concl, contra],
            )
        };
        let nat_pred = {
            let mut c = EnvDeclBuilder::new();
            let (z_id, z) = c.fresh_local(nat.clone());
            let mot = {
                let mut d = EnvDeclBuilder::child_of(&c);
                let (w_id, _w) = d.fresh_local(nat.clone());
                d.finish_child(d.mk_lam(w_id, BinderInfo::Default, nat.clone(), nat.clone()))
            };
            let sc = {
                let mut d = EnvDeclBuilder::child_of(&c);
                let (p_id, pp) = d.fresh_local(nat.clone());
                let (ih_id, _ih) = d.fresh_local(nat.clone());
                let r = d.mk_lam(ih_id, BinderInfo::Default, nat.clone(), pp);
                d.finish_child(d.mk_lam(p_id, BinderInfo::Default, nat.clone(), r))
            };
            let rec = Expr::apps(
                Expr::const_(
                    Name::from_string("Nat.rec"),
                    vec![Level::succ(Level::zero())],
                ),
                [mot, nzero.clone(), sc, z.clone()],
            );
            c.finish(c.mk_lam(z_id, BinderInfo::Default, nat.clone(), rec))
        };
        let succ_inj = |m: Expr, n: Expr, h: Expr| {
            let l1 = Level::succ(Level::zero());
            Expr::apps(
                Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
                [
                    nat.clone(),
                    nat.clone(),
                    succ(m),
                    succ(n),
                    nat_pred.clone(),
                    h,
                ],
            )
        };
        // ── TELESCOPE-COLLAPSE helpers (#56): the slt induction is now a SINGLE List.rec
        // on `a`; the cons-a minor converts `b`/`as` shapes via STANDALONE inversion
        // lemmas used as Eq.subst rewrites (NO nested b/as/bs recursor), so the #53
        // Pi-hypothesis recursor-minor motive-redex STRUCTURALLY cannot arise. The key
        // enabler (verified): bvFlipMsb / bvLastBit are HEAD-TRANSPARENT on a 2+-cons
        // (`flipMsb (cons h (cons h2 t)) = cons h (flipMsb (cons h2 t))` by refl), so
        // the cons-step def-eq holds even when the tail is in (bhead/btail) cons form.
        let l1 = Level::succ(Level::zero());
        let bhead = |x: Expr| Expr::app(Expr::const_str(crate::bitvec_inductive::names::BHEAD), x);
        let btail = |x: Expr| Expr::app(Expr::const_str(crate::bitvec_inductive::names::BTAIL), x);
        let eq_list = |x: Expr, y: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
                [list_bool(), x, y],
            )
        };
        let eq_symm_l = |x: Expr, y: Expr, h: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
                [list_bool(), x, y, h],
            )
        };
        // Eq.subst over List Bool: motive is `fun y => body(y)` built from a child builder.
        // consOfIsCons : ∀ xs, bvIsCons xs = true → xs = cons (bhead xs)(btail xs).
        //   List.rec.{0} on xs; nil ⇒ bvIsCons nil = false, so h:false=true absurd; cons ⇒ refl.
        {
            let nm = "Clean.BVC.consOfIsCons";
            let mk_body = |x: Expr| {
                Expr::arrow(
                    istrue(bv_is_cons(x.clone())),
                    eq_list(x.clone(), cons_b(bhead(x.clone()), btail(x.clone()))),
                )
            };
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (xs_id, xs) = b.fresh_local(list_bool());
                b.finish(b.mk_pi(xs_id, BinderInfo::Default, list_bool(), mk_body(xs)))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (xs_id, xs) = b.fresh_local(list_bool());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (y_id, y) = c.fresh_local(list_bool());
                    c.finish_child(c.mk_lam(y_id, BinderInfo::Default, list_bool(), mk_body(y)))
                };
                let nil_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let hty = istrue(bv_is_cons(nil_b()));
                    let (h_id, h) = c.fresh_local(hty.clone());
                    let contra = false_of_ft(h);
                    let concl = eq_list(nil_b(), cons_b(bhead(nil_b()), btail(nil_b())));
                    let body = false_elim_b(contra, concl);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, hty, body))
                };
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (h0_id, h0) = c.fresh_local(bool_ty());
                    let (t_id, t) = c.fresh_local(list_bool());
                    let ih_ty = Expr::arrow(
                        istrue(bv_is_cons(t.clone())),
                        eq_list(t.clone(), cons_b(bhead(t.clone()), btail(t.clone()))),
                    );
                    let (ih_id, _ih) = c.fresh_local(ih_ty.clone());
                    let cl = cons_b(h0.clone(), t.clone());
                    let hty = istrue(bv_is_cons(cl.clone()));
                    let (hh_id, _hh) = c.fresh_local(hty.clone());
                    // bhead(cons h0 t)=h0, btail(cons h0 t)=t by refl ⇒ goal = (cl = cl) ⇒ Eq.refl.
                    let refl = Expr::apps(
                        Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
                        [list_bool(), cl.clone()],
                    );
                    let r = c.mk_lam(hh_id, BinderInfo::Default, hty, refl);
                    let r = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, r);
                    let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                    c.finish_child(c.mk_lam(h0_id, BinderInfo::Default, bool_ty(), r))
                };
                let rec = Expr::apps(
                    Expr::const_(
                        Name::from_string("List.rec"),
                        vec![Level::zero(), Level::zero()],
                    ),
                    [bool_ty(), motive, nil_case, cons_case, xs.clone()],
                );
                b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_bool(), rec))
            };
            self.add_decl_if_absent(Declaration::Theorem {
                name: Name::from_string(nm),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }
        // isConsOfLenSucc : ∀ xs n, bvLen xs = Nat.succ n → bvIsCons xs = true.
        //   List.rec.{0} on xs; nil ⇒ bvLen nil = 0, so h:0=succ n absurd; cons ⇒ refl true.
        {
            let nm = "Clean.BVC.isConsOfLenSucc";
            // mk_body builds `∀ n, bvLen x = succ n → bvIsCons x = true` against the
            // SUPPLIED parent builder `p` (so `x`'s FVar is owned by `p`, no leak).
            let mk_body = |p: &EnvDeclBuilder, x: Expr| -> Expr {
                let mut c = EnvDeclBuilder::child_of(p);
                let (n_id, n) = c.fresh_local(nat.clone());
                let inner = Expr::arrow(
                    eq_nat(bvlen(x.clone()), succ(n.clone())),
                    istrue(bv_is_cons(x.clone())),
                );
                c.finish_child(c.mk_pi(n_id, BinderInfo::Default, nat.clone(), inner))
            };
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (xs_id, xs) = b.fresh_local(list_bool());
                let body = mk_body(&b, xs.clone());
                b.finish(b.mk_pi(xs_id, BinderInfo::Default, list_bool(), body))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (xs_id, xs) = b.fresh_local(list_bool());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (y_id, y) = c.fresh_local(list_bool());
                    let body = mk_body(&c, y.clone());
                    c.finish_child(c.mk_lam(y_id, BinderInfo::Default, list_bool(), body))
                };
                let nil_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (n_id, n) = c.fresh_local(nat.clone());
                    let hty = eq_nat(bvlen(nil_b()), succ(n.clone()));
                    let (h_id, h) = c.fresh_local(hty.clone());
                    // bvLen nil ≡ 0, so h : 0 = succ n ; false_zero_succ n h : False.
                    let contra = false_zero_succ(n.clone(), h);
                    let body = false_elim_b(contra, istrue(bv_is_cons(nil_b())));
                    let r = c.mk_lam(h_id, BinderInfo::Default, hty, body);
                    c.finish_child(c.mk_lam(n_id, BinderInfo::Default, nat.clone(), r))
                };
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (h0_id, h0) = c.fresh_local(bool_ty());
                    let (t_id, t) = c.fresh_local(list_bool());
                    let ih_ty = mk_body(&c, t.clone());
                    let (ih_id, _ih) = c.fresh_local(ih_ty.clone());
                    let cl = cons_b(h0.clone(), t.clone());
                    let (n_id, n) = c.fresh_local(nat.clone());
                    let hty = eq_nat(bvlen(cl.clone()), succ(n.clone()));
                    let (h_id, _h) = c.fresh_local(hty.clone());
                    // bvIsCons(cons ..) ≡ true ⇒ goal is (true = true) ⇒ Eq.refl true.
                    let refl = eq_refl_bool(btrue());
                    let r = c.mk_lam(h_id, BinderInfo::Default, hty, refl);
                    let r = c.mk_lam(n_id, BinderInfo::Default, nat.clone(), r);
                    let r = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, r);
                    let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                    c.finish_child(c.mk_lam(h0_id, BinderInfo::Default, bool_ty(), r))
                };
                let rec = Expr::apps(
                    Expr::const_(
                        Name::from_string("List.rec"),
                        vec![Level::zero(), Level::zero()],
                    ),
                    [bool_ty(), motive, nil_case, cons_case, xs.clone()],
                );
                b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_bool(), rec))
            };
            self.add_decl_if_absent(Declaration::Theorem {
                name: Name::from_string(nm),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }
        // nilOfNotIsCons : ∀ xs, bvIsCons xs = false → xs = nil.
        //   List.rec.{0} on xs; nil ⇒ refl nil; cons ⇒ bvIsCons(cons..)=true, so h:true=false absurd.
        {
            let nm = "Clean.BVC.nilOfNotIsCons";
            let isfalse = |x: Expr| {
                Expr::apps(
                    Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
                    [bool_ty(), bv_is_cons(x), bfalse()],
                )
            };
            let mk_body = |x: Expr| Expr::arrow(isfalse(x.clone()), eq_list(x.clone(), nil_b()));
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (xs_id, xs) = b.fresh_local(list_bool());
                b.finish(b.mk_pi(xs_id, BinderInfo::Default, list_bool(), mk_body(xs)))
            };
            // disc_t x := Bool.rec True False x  (disc_t true=True, disc_t false=False) for true=false absurd.
            let disc_t = {
                let mut c = EnvDeclBuilder::new();
                let (x_id, x) = c.fresh_local(bool_ty());
                let mot = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (w_id, _w) = d.fresh_local(bool_ty());
                    d.finish_child(d.mk_lam(
                        w_id,
                        BinderInfo::Default,
                        bool_ty(),
                        Expr::sort(Level::zero()),
                    ))
                };
                // Bool.rec mFalse mTrue x : we want disc_t false=False, disc_t true=True → mFalse=False, mTrue=True.
                let rec = Expr::apps(
                    Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]),
                    [
                        mot,
                        Expr::const_str("False"),
                        Expr::const_str("True"),
                        x.clone(),
                    ],
                );
                c.finish(c.mk_lam(x_id, BinderInfo::Default, bool_ty(), rec))
            };
            // false_of_true_eq_false (h : true = false) : False = Eq.subst disc_t true false h (True.intro : disc_t true).
            let false_of_tf = |h: Expr| {
                Expr::apps(
                    Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
                    [
                        bool_ty(),
                        disc_t.clone(),
                        btrue(),
                        bfalse(),
                        h,
                        Expr::const_str("True.intro"),
                    ],
                )
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (xs_id, xs) = b.fresh_local(list_bool());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (y_id, y) = c.fresh_local(list_bool());
                    c.finish_child(c.mk_lam(y_id, BinderInfo::Default, list_bool(), mk_body(y)))
                };
                let nil_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let hty = isfalse(nil_b());
                    let (h_id, _h) = c.fresh_local(hty.clone());
                    let refl = Expr::apps(
                        Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
                        [list_bool(), nil_b()],
                    );
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, hty, refl))
                };
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (h0_id, h0) = c.fresh_local(bool_ty());
                    let (t_id, t) = c.fresh_local(list_bool());
                    let ih_ty = Expr::arrow(isfalse(t.clone()), eq_list(t.clone(), nil_b()));
                    let (ih_id, _ih) = c.fresh_local(ih_ty.clone());
                    let cl = cons_b(h0.clone(), t.clone());
                    let hty = isfalse(cl.clone());
                    let (h_id, h) = c.fresh_local(hty.clone());
                    // bvIsCons(cons..) ≡ true, so h : true = false ; absurd.
                    let contra = false_of_tf(h);
                    let body = false_elim_b(contra, eq_list(cl.clone(), nil_b()));
                    let r = c.mk_lam(h_id, BinderInfo::Default, hty, body);
                    let r = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, r);
                    let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                    c.finish_child(c.mk_lam(h0_id, BinderInfo::Default, bool_ty(), r))
                };
                let rec = Expr::apps(
                    Expr::const_(
                        Name::from_string("List.rec"),
                        vec![Level::zero(), Level::zero()],
                    ),
                    [bool_ty(), motive, nil_case, cons_case, xs.clone()],
                );
                b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_bool(), rec))
            };
            self.add_decl_if_absent(Declaration::Theorem {
                name: Name::from_string(nm),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }
        // nilOfLenZero : ∀ xs, bvLen xs = Nat.zero → xs = nil.
        //   List.rec.{0} on xs; nil ⇒ refl nil; cons ⇒ bvLen(cons..)=succ.., so h:succ=0 absurd.
        {
            let nm = "Clean.BVC.nilOfLenZero";
            let lenz = |x: Expr| eq_nat(bvlen(x), nzero.clone());
            let mk_body = |x: Expr| Expr::arrow(lenz(x.clone()), eq_list(x.clone(), nil_b()));
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (xs_id, xs) = b.fresh_local(list_bool());
                b.finish(b.mk_pi(xs_id, BinderInfo::Default, list_bool(), mk_body(xs)))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (xs_id, xs) = b.fresh_local(list_bool());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (y_id, y) = c.fresh_local(list_bool());
                    c.finish_child(c.mk_lam(y_id, BinderInfo::Default, list_bool(), mk_body(y)))
                };
                let nil_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let hty = lenz(nil_b());
                    let (h_id, _h) = c.fresh_local(hty.clone());
                    let refl = Expr::apps(
                        Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
                        [list_bool(), nil_b()],
                    );
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, hty, refl))
                };
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (h0_id, h0) = c.fresh_local(bool_ty());
                    let (t_id, t) = c.fresh_local(list_bool());
                    let ih_ty = Expr::arrow(lenz(t.clone()), eq_list(t.clone(), nil_b()));
                    let (ih_id, _ih) = c.fresh_local(ih_ty.clone());
                    let cl = cons_b(h0.clone(), t.clone());
                    let hty = lenz(cl.clone());
                    let (h_id, h) = c.fresh_local(hty.clone());
                    // bvLen(cons..) ≡ succ(bvLen t), so h : succ.. = 0 ; symm → 0 = succ.. ; absurd.
                    let symm = Expr::apps(
                        Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
                        [nat.clone(), bvlen(cl.clone()), nzero.clone(), h],
                    );
                    let contra = false_zero_succ(bvlen(t.clone()), symm);
                    let body = false_elim_b(contra, eq_list(cl.clone(), nil_b()));
                    let r = c.mk_lam(h_id, BinderInfo::Default, hty, body);
                    let r = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, r);
                    let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                    c.finish_child(c.mk_lam(h0_id, BinderInfo::Default, bool_ty(), r))
                };
                let rec = Expr::apps(
                    Expr::const_(
                        Name::from_string("List.rec"),
                        vec![Level::zero(), Level::zero()],
                    ),
                    [bool_ty(), motive, nil_case, cons_case, xs.clone()],
                );
                b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_bool(), rec))
            };
            self.add_decl_if_absent(Declaration::Theorem {
                name: Name::from_string(nm),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }

        // ── goalConsCong helper (the #46 keystone): carry the cons-step def-eq
        // `goal (cons a0 as)(cons b0 bs) c == goal as bs (maj a0 (¬b0) c)` (valid
        // when as,bs are CONS — flipMsb/lastBit/carryOut pass the head through) in
        // the TYPE SIGNATURE, so the inner-cons recursor leaf presents the
        // un-reduced motive type. Proven `fun g => g` at CONCRETE head bits.
        // Parameterized over a0,b0 literals (4 combos) — only the head LITERALS
        // matter for the def-eq (the tail bits stay symbolic).
        // We register these as local theorems sltConsCong_{a0}{b0}.
        // ONE parametric sltConsCong (over SYMBOLIC a0,b0): the cons-step def-eq holds
        // symbolically (verified) — no literal dispatch / a0,b0 Bool.rec needed (avoids the
        // #46 motive-redex). `fun g => g`: goal (cons a1 asp)(cons b1 bsp)(maj a0 ¬b0 c)
        //   = goal (cons a0 (cons a1 asp))(cons b0 (cons b1 bsp)) c   (def-eq, AS/BS cons).
        {
            let nm = "Clean.BVC.sltConsCong";
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (a0_id, a0) = b.fresh_local(bool_ty());
                let (b0_id, b0) = b.fresh_local(bool_ty());
                let (a1_id, a1) = b.fresh_local(bool_ty());
                let (asx_id, asx) = b.fresh_local(list_bool());
                let (b1_id, b1) = b.fresh_local(bool_ty());
                let (bsx_id, bsx) = b.fresh_local(list_bool());
                let (c_id, cc) = b.fresh_local(bool_ty());
                let asl = cons_b(a1.clone(), asx.clone());
                let bsl = cons_b(b1.clone(), bsx.clone());
                let cstep = maj(a0.clone(), bnot(b0.clone()), cc.clone());
                let g_ty = goal(asl.clone(), bsl.clone(), cstep);
                let (g_id, _g) = b.fresh_local(g_ty.clone());
                let concl = goal(
                    cons_b(a0.clone(), asl.clone()),
                    cons_b(b0.clone(), bsl.clone()),
                    cc.clone(),
                );
                let t = b.mk_pi(g_id, BinderInfo::Default, g_ty, concl);
                let t = b.mk_pi(c_id, BinderInfo::Default, bool_ty(), t);
                let t = b.mk_pi(bsx_id, BinderInfo::Default, list_bool(), t);
                let t = b.mk_pi(b1_id, BinderInfo::Default, bool_ty(), t);
                let t = b.mk_pi(asx_id, BinderInfo::Default, list_bool(), t);
                let t = b.mk_pi(a1_id, BinderInfo::Default, bool_ty(), t);
                let t = b.mk_pi(b0_id, BinderInfo::Default, bool_ty(), t);
                b.finish(b.mk_pi(a0_id, BinderInfo::Default, bool_ty(), t))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (a0_id, _a0) = b.fresh_local(bool_ty());
                let (b0_id, _b0) = b.fresh_local(bool_ty());
                let (a1_id, a1) = b.fresh_local(bool_ty());
                let (asx_id, asx) = b.fresh_local(list_bool());
                let (b1_id, b1) = b.fresh_local(bool_ty());
                let (bsx_id, bsx) = b.fresh_local(list_bool());
                let (c_id, cc) = b.fresh_local(bool_ty());
                let asl = cons_b(a1.clone(), asx.clone());
                let bsl = cons_b(b1.clone(), bsx.clone());
                let cstep = maj(_a0.clone(), bnot(_b0.clone()), cc.clone());
                let g_ty = goal(asl.clone(), bsl.clone(), cstep);
                let (g_id, g) = b.fresh_local(g_ty.clone());
                let r = b.mk_lam(g_id, BinderInfo::Default, g_ty, g);
                let r = b.mk_lam(c_id, BinderInfo::Default, bool_ty(), r);
                let r = b.mk_lam(bsx_id, BinderInfo::Default, list_bool(), r);
                let r = b.mk_lam(b1_id, BinderInfo::Default, bool_ty(), r);
                let r = b.mk_lam(asx_id, BinderInfo::Default, list_bool(), r);
                let r = b.mk_lam(a1_id, BinderInfo::Default, bool_ty(), r);
                let r = b.mk_lam(b0_id, BinderInfo::Default, bool_ty(), r);
                b.finish(b.mk_lam(a0_id, BinderInfo::Default, bool_ty(), r))
            };
            self.add_decl_if_absent(Declaration::Theorem {
                name: Name::from_string(nm),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }
        // ── the induction. motive_a a := ∀ b c, bvIsCons a = true → bvLen a = bvLen b → goal a b c
        let mk_motive_a = || {
            let mut c0 = EnvDeclBuilder::new();
            let (a_id, a) = c0.fresh_local(list_bool());
            let body = {
                let mut d = EnvDeclBuilder::child_of(&c0);
                let (b_id, bb) = d.fresh_local(list_bool());
                let inner = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (c_id, cc) = e.fresh_local(bool_ty());
                    let consh = istrue(bv_is_cons(a.clone()));
                    let (ch_id, _ch) = e.fresh_local(consh.clone());
                    let lenh = eq_nat(bvlen(a.clone()), bvlen(bb.clone()));
                    let (lh_id, _lh) = e.fresh_local(lenh.clone());
                    let g = goal(a.clone(), bb.clone(), cc.clone());
                    let t = e.mk_pi(lh_id, BinderInfo::Default, lenh, g);
                    let t = e.mk_pi(ch_id, BinderInfo::Default, consh, t);
                    e.finish_child(e.mk_pi(c_id, BinderInfo::Default, bool_ty(), t))
                };
                d.finish_child(d.mk_pi(b_id, BinderInfo::Default, list_bool(), inner))
            };
            c0.finish(c0.mk_lam(a_id, BinderInfo::Default, list_bool(), body))
        };
        let motive_a = mk_motive_a();

        // nil-a minor: motive_a nil. bvIsCons nil = false, so the consh : false = true is absurd.
        let nil_a = {
            let mut c0 = EnvDeclBuilder::new();
            let (b_id, _bb) = c0.fresh_local(list_bool());
            let (c_id, _cc) = c0.fresh_local(bool_ty());
            let consh = istrue(bv_is_cons(nil_b()));
            let (ch_id, ch) = c0.fresh_local(consh.clone());
            let lenh = eq_nat(bvlen(nil_b()), bvlen(_bb.clone()));
            let (lh_id, _lh) = c0.fresh_local(lenh.clone());
            // bvIsCons nil ≡ false, so ch : false = true. false_of_ft ch : False. False.elim.
            let contra = false_of_ft(ch);
            let concl = goal(nil_b(), _bb.clone(), _cc.clone());
            let body = false_elim_b(contra, concl);
            let r = c0.mk_lam(lh_id, BinderInfo::Default, lenh, body);
            let r = c0.mk_lam(ch_id, BinderInfo::Default, consh, r);
            let r = c0.mk_lam(c_id, BinderInfo::Default, bool_ty(), r);
            c0.finish(c0.mk_lam(b_id, BinderInfo::Default, list_bool(), r))
        };

        // ── cons-a minor (#56 TELESCOPE-COLLAPSE): (a0, as, ih_a : motive_a as) →
        //    ∀ b c, bvIsCons(cons a0 as)=true → bvLen(cons a0 as)=bvLen b → goal (cons a0 as) b c.
        // NO nested List.rec on b/as/bs. ONE cheap Bool.rec on `bvIsCons as`:
        //   false-branch ⇒ as ≡ nil ⇒ SINGLETON; b is a 1-cons (from len = succ 0); 8-case Bool.rec.
        //   true-branch  ⇒ as = cons(bhead as)(btail as) [consOfIsCons]; b = cons b0 (cons b1 ..)
        //     [isConsOfLenSucc ×2 + consOfIsCons ×2]; g_tail = subst-rewrites of (ih_a (btail b) ..);
        //     sltConsCong threads the head; subst back to goal (cons a0 as) b c.
        // bvLastBit / bvFlipMsb head-transparency on a 2+-cons (verified #56) makes every
        // flipMsb/lastBit/carryOut reduce by refl in cons-form, so no recursor-minor redex arises.
        let cons_a = {
            let mut c0 = EnvDeclBuilder::new();
            let (a0_id, a0) = c0.fresh_local(bool_ty());
            let (as_id, as_) = c0.fresh_local(list_bool());
            let ih_ty = {
                let mut d = EnvDeclBuilder::child_of(&c0);
                let (b_id, bb) = d.fresh_local(list_bool());
                let inner = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (c_id, cc) = e.fresh_local(bool_ty());
                    let consh = istrue(bv_is_cons(as_.clone()));
                    let (ch_id, _ch) = e.fresh_local(consh.clone());
                    let lenh = eq_nat(bvlen(as_.clone()), bvlen(bb.clone()));
                    let (lh_id, _lh) = e.fresh_local(lenh.clone());
                    let g = goal(as_.clone(), bb.clone(), cc.clone());
                    let t = e.mk_pi(lh_id, BinderInfo::Default, lenh, g);
                    let t = e.mk_pi(ch_id, BinderInfo::Default, consh, t);
                    e.finish_child(e.mk_pi(c_id, BinderInfo::Default, bool_ty(), t))
                };
                d.finish_child(d.mk_pi(b_id, BinderInfo::Default, list_bool(), inner))
            };
            let (ih_id, ih) = c0.fresh_local(ih_ty.clone());
            let aa = cons_b(a0.clone(), as_.clone());
            // body : ∀ b c, bvIsCons aa = true → bvLen aa = bvLen b → goal aa b c.
            // SINGLE cheap Bool.rec on `bvIsCons as_` (no telescope); cons-form rewrites via the
            // standalone inversion lemmas; sltConsCong threads the head in the recursive branch.
            let body = {
                let mut d = EnvDeclBuilder::child_of(&c0);
                let (b_id, bb) = d.fresh_local(list_bool());
                let (c_id, cc) = d.fresh_local(bool_ty());
                let consh = istrue(bv_is_cons(aa.clone()));
                let (ch_id, _ch) = d.fresh_local(consh.clone());
                let lenh = eq_nat(bvlen(aa.clone()), bvlen(bb.clone()));
                let (lh_id, lh) = d.fresh_local(lenh.clone());
                // lh : bvLen(cons a0 as) = bvLen b  ≡  succ(bvLen as) = bvLen b   (bvLen cons reduces).
                // Branch on `bvIsCons as_` via Bool.rec with the dependent
                //   motive_w w := (bvIsCons as_ = w) → goal aa b c
                // applied to (bvIsCons as_) with witness Eq.refl, so each minor receives the
                // discriminating equality.
                let dec_eq = |x: Expr, v: Expr| {
                    Expr::apps(
                        Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
                        [bool_ty(), x, v],
                    )
                };
                let goal_aa_b = goal(aa.clone(), bb.clone(), cc.clone());
                let wmot = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (w_id, w) = e.fresh_local(bool_ty());
                    e.finish_child(e.mk_lam(
                        w_id,
                        BinderInfo::Default,
                        bool_ty(),
                        Expr::arrow(dec_eq(bv_is_cons(as_.clone()), w), goal_aa_b.clone()),
                    ))
                };
                // helper consts
                let cons_of_is_cons = |x: Expr, h: Expr| {
                    Expr::apps(Expr::const_str("Clean.BVC.consOfIsCons"), [x, h])
                };
                let is_cons_of_len_succ = |x: Expr, n: Expr, h: Expr| {
                    Expr::apps(Expr::const_str("Clean.BVC.isConsOfLenSucc"), [x, n, h])
                };
                let nil_of_not_is_cons = |x: Expr, h: Expr| {
                    Expr::apps(Expr::const_str("Clean.BVC.nilOfNotIsCons"), [x, h])
                };
                let nil_of_len_zero = |x: Expr, h: Expr| {
                    Expr::apps(Expr::const_str("Clean.BVC.nilOfLenZero"), [x, h])
                };
                let eq_symm_n = |x: Expr, y: Expr, h: Expr| {
                    Expr::apps(
                        Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
                        [nat.clone(), x, y, h],
                    )
                };
                let _eq_refl_l = |x: Expr| {
                    Expr::apps(
                        Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
                        [list_bool(), x],
                    )
                };
                // Eq.subst over List Bool with a child-built motive `fun y => body_at(y)`.
                let subst_list = |parent: &EnvDeclBuilder,
                                  from: Expr,
                                  to: Expr,
                                  h: Expr,
                                  base: Expr,
                                  body_at: &dyn Fn(Expr) -> Expr|
                 -> Expr {
                    let mut g = EnvDeclBuilder::child_of(parent);
                    let (y_id, y) = g.fresh_local(list_bool());
                    let mot = g.finish_child(g.mk_lam(
                        y_id,
                        BinderInfo::Default,
                        list_bool(),
                        body_at(y),
                    ));
                    Expr::apps(
                        Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
                        [list_bool(), mot, from, to, h, base],
                    )
                };

                // ── TRUE branch: h_cons : bvIsCons as_ = true.  Recursive case.
                let true_minor = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let hc_ty = dec_eq(bv_is_cons(as_.clone()), btrue());
                    let (hc_id, hc) = e.fresh_local(hc_ty.clone());
                    // e_as : as = cons (bhead as)(btail as)
                    let e_as = cons_of_is_cons(as_.clone(), hc.clone());
                    let a1 = bhead(as_.clone());
                    let asp = btail(as_.clone());
                    // bvIsCons b = true : from lh. lh : succ(bvLen as) = bvLen b ; symm → bvLen b = succ(bvLen as).
                    let lh_symm = eq_symm_n(bvlen(aa.clone()), bvlen(bb.clone()), lh.clone());
                    // bvLen aa ≡ succ(bvLen as_), so lh_symm : bvLen b = succ(bvLen as_).
                    let cons_b_hyp =
                        is_cons_of_len_succ(bb.clone(), bvlen(as_.clone()), lh_symm.clone());
                    let e_b = cons_of_is_cons(bb.clone(), cons_b_hyp);
                    let b0 = bhead(bb.clone());
                    let btb = btail(bb.clone());
                    // hz : bvLen as_ = bvLen (btail b).
                    //   lh_symm : bvLen b = succ(bvLen as_). e_b : b = cons b0 (btail b), so
                    //   bvLen b ≡ succ(bvLen (btail b)). Hence succ(bvLen (btail b)) = succ(bvLen as_) after
                    //   subst e_b into lh_symm. Then succ_inj. We get bvLen(btail b)=bvLen as_; symm → hz.
                    // Build: subst e_b into lh_symm to rewrite the b on the LHS to (cons b0 btb):
                    //   target type: bvLen (cons b0 btb) = succ(bvLen as_)  ≡  succ(bvLen btb) = succ(bvLen as_).
                    let lhs_after = {
                        // motive y := bvLen y = succ(bvLen as_)
                        let asx = as_.clone();
                        let body_at = move |y: Expr| eq_nat(bvlen(y), succ(bvlen(asx.clone())));
                        subst_list(
                            &e,
                            bb.clone(),
                            cons_b(b0.clone(), btb.clone()),
                            e_b.clone(),
                            lh_symm.clone(),
                            &body_at,
                        )
                    };
                    // lhs_after : bvLen(cons b0 btb)=succ(bvLen as_) ≡ succ(bvLen btb)=succ(bvLen as_). succ_inj.
                    let len_eq = succ_inj(bvlen(btb.clone()), bvlen(as_.clone()), lhs_after);
                    // len_eq : bvLen btb = bvLen as_ ; hz : bvLen as_ = bvLen btb.
                    let hz = eq_symm_n(bvlen(btb.clone()), bvlen(as_.clone()), len_eq.clone());
                    // bvIsCons (btail b) = true : isConsOfLenSucc btb (bvLen (btail as_)) (proof bvLen btb = succ(bvLen(btail as_))).
                    //   bvLen btb = bvLen as_ (len_eq) ; bvLen as_ ≡ succ(bvLen(btail as_)) once as_ is in cons form,
                    //   but as_ is symbolic — use e_as: subst e_as into len_eq's RHS as_ → cons a1 asp gives
                    //   bvLen btb = bvLen(cons a1 asp) ≡ succ(bvLen asp).
                    let len_eq_cons = {
                        let btbx = btb.clone();
                        let body_at = move |y: Expr| eq_nat(bvlen(btbx.clone()), bvlen(y));
                        subst_list(
                            &e,
                            as_.clone(),
                            cons_b(a1.clone(), asp.clone()),
                            e_as.clone(),
                            len_eq.clone(),
                            &body_at,
                        )
                    };
                    // len_eq_cons : bvLen btb = bvLen(cons a1 asp) ≡ succ(bvLen asp).
                    let cons_btb_hyp =
                        is_cons_of_len_succ(btb.clone(), bvlen(asp.clone()), len_eq_cons);
                    let e_bt = cons_of_is_cons(btb.clone(), cons_btb_hyp);
                    let b1 = bhead(btb.clone());
                    let bsp = btail(btb.clone());
                    let cstep = maj(a0.clone(), bnot(b0.clone()), cc.clone());
                    // ih_a (btail b) cstep h_cons hz : goal as_ (btail b) cstep
                    let ih_app = Expr::apps(
                        ih.clone(),
                        [btb.clone(), cstep.clone(), hc.clone(), hz.clone()],
                    );
                    // rewrite as_ → cons a1 asp (e_as) inside goal _ (btail b) cstep
                    let g1 = {
                        let btbx = btb.clone();
                        let cstepx = cstep.clone();
                        let goalf = goal;
                        let body_at = move |y: Expr| goalf(y, btbx.clone(), cstepx.clone());
                        subst_list(
                            &e,
                            as_.clone(),
                            cons_b(a1.clone(), asp.clone()),
                            e_as.clone(),
                            ih_app,
                            &body_at,
                        )
                    };
                    // g1 : goal (cons a1 asp)(btail b) cstep ; rewrite (btail b) → cons b1 bsp (e_bt)
                    let g_tail = {
                        let a1x = a1.clone();
                        let aspx = asp.clone();
                        let cstepx = cstep.clone();
                        let goalf = goal;
                        let body_at = move |y: Expr| {
                            goalf(cons_b(a1x.clone(), aspx.clone()), y, cstepx.clone())
                        };
                        subst_list(
                            &e,
                            btb.clone(),
                            cons_b(b1.clone(), bsp.clone()),
                            e_bt.clone(),
                            g1,
                            &body_at,
                        )
                    };
                    // g_tail : goal (cons a1 asp)(cons b1 bsp) cstep.
                    // sltConsCong a0 b0 a1 asp b1 bsp c g_tail : goal (cons a0 (cons a1 asp))(cons b0 (cons b1 bsp)) c.
                    let consstep = Expr::apps(
                        Expr::const_str("Clean.BVC.sltConsCong"),
                        [
                            a0.clone(),
                            b0.clone(),
                            a1.clone(),
                            asp.clone(),
                            b1.clone(),
                            bsp.clone(),
                            cc.clone(),
                            g_tail,
                        ],
                    );
                    // subst BACK to goal aa b c. Three rewrites:
                    //   (cons a1 asp) → as_           [e_as.symm]   : goal (cons a0 as_)(cons b0 (cons b1 bsp)) c
                    //   (cons b1 bsp) → btail b       [e_bt.symm]   : goal (cons a0 as_)(cons b0 (btail b)) c
                    //   (cons b0 (btail b)) → b       [e_b.symm]    : goal (cons a0 as_) b c   ≡ goal aa b c
                    let back1 = {
                        let a0x = a0.clone();
                        let consb = cons_b(b0.clone(), cons_b(b1.clone(), bsp.clone()));
                        let ccx = cc.clone();
                        let goalf = goal;
                        let body_at = move |y: Expr| {
                            goalf(cons_b(a0x.clone(), y), consb.clone(), ccx.clone())
                        };
                        subst_list(
                            &e,
                            cons_b(a1.clone(), asp.clone()),
                            as_.clone(),
                            eq_symm_l(as_.clone(), cons_b(a1.clone(), asp.clone()), e_as.clone()),
                            consstep,
                            &body_at,
                        )
                    };
                    let back2 = {
                        let consa = cons_b(a0.clone(), as_.clone());
                        let b0x = b0.clone();
                        let ccx = cc.clone();
                        let goalf = goal;
                        let body_at = move |y: Expr| {
                            goalf(consa.clone(), cons_b(b0x.clone(), y), ccx.clone())
                        };
                        subst_list(
                            &e,
                            cons_b(b1.clone(), bsp.clone()),
                            btb.clone(),
                            eq_symm_l(btb.clone(), cons_b(b1.clone(), bsp.clone()), e_bt.clone()),
                            back1,
                            &body_at,
                        )
                    };
                    let back3 = {
                        let consa = cons_b(a0.clone(), as_.clone());
                        let ccx = cc.clone();
                        let goalf = goal;
                        let body_at = move |y: Expr| goalf(consa.clone(), y, ccx.clone());
                        subst_list(
                            &e,
                            cons_b(b0.clone(), btb.clone()),
                            bb.clone(),
                            eq_symm_l(bb.clone(), cons_b(b0.clone(), btb.clone()), e_b.clone()),
                            back2,
                            &body_at,
                        )
                    };
                    // back3 : goal (cons a0 as_) b c ≡ goal aa b c.
                    e.finish_child(e.mk_lam(hc_id, BinderInfo::Default, hc_ty, back3))
                };

                // ── FALSE branch: h_ncons : bvIsCons as_ = false.  Singleton case.
                let false_minor = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let hn_ty = dec_eq(bv_is_cons(as_.clone()), bfalse());
                    let (hn_id, hn) = e.fresh_local(hn_ty.clone());
                    // e_as : as_ = nil   [nilOfNotIsCons]
                    let e_as_nil = nil_of_not_is_cons(as_.clone(), hn.clone());
                    // bvLen b = succ(bvLen as_)  [lh.symm] ; rewrite as_→nil → bvLen b = succ 0 = 1.
                    let lh_symm = eq_symm_n(bvlen(aa.clone()), bvlen(bb.clone()), lh.clone());
                    // bvIsCons b = true (len = succ _) ; e_b : b = cons (bhead b)(btail b).
                    let cons_b_hyp =
                        is_cons_of_len_succ(bb.clone(), bvlen(as_.clone()), lh_symm.clone());
                    let e_b = cons_of_is_cons(bb.clone(), cons_b_hyp);
                    let b0 = bhead(bb.clone());
                    let btb = btail(bb.clone());
                    // btail b = nil : bvLen(btail b) = 0. From lh_symm rewritten by e_b: succ(bvLen btb)=succ(bvLen as_),
                    //   succ_inj → bvLen btb = bvLen as_ ; rewrite as_→nil (e_as_nil) → bvLen btb = bvLen nil = 0.
                    let lhs_after = {
                        let asx = as_.clone();
                        let body_at = move |y: Expr| eq_nat(bvlen(y), succ(bvlen(asx.clone())));
                        subst_list(
                            &e,
                            bb.clone(),
                            cons_b(b0.clone(), btb.clone()),
                            e_b.clone(),
                            lh_symm.clone(),
                            &body_at,
                        )
                    };
                    let len_eq = succ_inj(bvlen(btb.clone()), bvlen(as_.clone()), lhs_after);
                    // len_eq : bvLen btb = bvLen as_ ; rewrite as_→nil → bvLen btb = bvLen nil ≡ 0.
                    let len_btb_zero = {
                        let btbx = btb.clone();
                        let body_at = move |y: Expr| eq_nat(bvlen(btbx.clone()), bvlen(y));
                        subst_list(
                            &e,
                            as_.clone(),
                            nil_b(),
                            e_as_nil.clone(),
                            len_eq.clone(),
                            &body_at,
                        )
                    };
                    // len_btb_zero : bvLen btb = bvLen nil ≡ Nat.zero. nilOfLenZero btb : btail b = nil.
                    let e_bt_nil = nil_of_len_zero(btb.clone(), len_btb_zero);
                    // SINGLETON proof: goal (cons a0 nil)(cons b0 nil) c via Bool.rec on a0,b0,c (ground refl).
                    // goal [a0][b0] c : LHS = Not(carryOut(flipMsb[a0], bvNot(flipMsb[b0]), c)) = Not(maj ¬a0 b0 c).
                    let sgoal = |av: Expr, bv: Expr, cv: Expr| {
                        goal(cons_b(av, nil_b()), cons_b(bv, nil_b()), cv)
                    };
                    let singleton = {
                        // nested Bool.rec a0 → b0 → c, leaf = eq_refl_bool(Not(maj ¬av bv cv)).
                        let mk_c = |av: Expr, bv: Expr, parent: &EnvDeclBuilder| -> Expr {
                            let h = EnvDeclBuilder::child_of(parent);
                            let cmot = {
                                let mut k = EnvDeclBuilder::child_of(&h);
                                let (cv_id, cv) = k.fresh_local(bool_ty());
                                k.finish_child(k.mk_lam(
                                    cv_id,
                                    BinderInfo::Default,
                                    bool_ty(),
                                    sgoal(av.clone(), bv.clone(), cv),
                                ))
                            };
                            let leaf = |cv: Expr| {
                                eq_refl_bool(bnot(maj(bnot(av.clone()), bv.clone(), cv)))
                            };
                            let rec = Expr::apps(
                                Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
                                [cmot, leaf(bfalse()), leaf(btrue()), cc.clone()],
                            );
                            h.finish_child(rec)
                        };
                        let mk_b = |av: Expr, parent: &EnvDeclBuilder| -> Expr {
                            let h = EnvDeclBuilder::child_of(parent);
                            // b-motive: `fun bv => sgoal av bv c` (outer c=cc fixed; inner c-rec dispatches c).
                            let bmot = {
                                let mut k = EnvDeclBuilder::child_of(&h);
                                let (bv_id, bv) = k.fresh_local(bool_ty());
                                k.finish_child(k.mk_lam(
                                    bv_id,
                                    BinderInfo::Default,
                                    bool_ty(),
                                    sgoal(av.clone(), bv, cc.clone()),
                                ))
                            };
                            let rec = Expr::apps(
                                Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
                                [
                                    bmot,
                                    mk_c(av.clone(), bfalse(), &h),
                                    mk_c(av.clone(), btrue(), &h),
                                    b0.clone(),
                                ],
                            );
                            h.finish_child(rec)
                        };
                        let amot = {
                            let mut k = EnvDeclBuilder::child_of(&e);
                            let (av_id, av) = k.fresh_local(bool_ty());
                            k.finish_child(k.mk_lam(
                                av_id,
                                BinderInfo::Default,
                                bool_ty(),
                                sgoal(av, b0.clone(), cc.clone()),
                            ))
                        };
                        Expr::apps(
                            Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
                            [amot, mk_b(bfalse(), &e), mk_b(btrue(), &e), a0.clone()],
                        )
                    };
                    // singleton : goal (cons a0 nil)(cons b0 nil) c.
                    // subst BACK to goal aa b c: rewrite nil→as_ (e_as_nil.symm) for the a-operand, then
                    //   nil→btail b (e_bt_nil.symm), then (cons b0 (btail b))→b (e_b.symm).
                    let back1 = {
                        let a0x = a0.clone();
                        let consb = cons_b(b0.clone(), nil_b());
                        let ccx = cc.clone();
                        let goalf = goal;
                        let body_at = move |y: Expr| {
                            goalf(cons_b(a0x.clone(), y), consb.clone(), ccx.clone())
                        };
                        subst_list(
                            &e,
                            nil_b(),
                            as_.clone(),
                            eq_symm_l(as_.clone(), nil_b(), e_as_nil.clone()),
                            singleton,
                            &body_at,
                        )
                    };
                    // back1 : goal (cons a0 as_)(cons b0 nil) c.
                    let back2 = {
                        let consa = cons_b(a0.clone(), as_.clone());
                        let b0x = b0.clone();
                        let ccx = cc.clone();
                        let goalf = goal;
                        let body_at = move |y: Expr| {
                            goalf(consa.clone(), cons_b(b0x.clone(), y), ccx.clone())
                        };
                        subst_list(
                            &e,
                            nil_b(),
                            btb.clone(),
                            eq_symm_l(btb.clone(), nil_b(), e_bt_nil.clone()),
                            back1,
                            &body_at,
                        )
                    };
                    // back2 : goal (cons a0 as_)(cons b0 (btail b)) c.
                    let back3 = {
                        let consa = cons_b(a0.clone(), as_.clone());
                        let ccx = cc.clone();
                        let goalf = goal;
                        let body_at = move |y: Expr| goalf(consa.clone(), y, ccx.clone());
                        subst_list(
                            &e,
                            cons_b(b0.clone(), btb.clone()),
                            bb.clone(),
                            eq_symm_l(bb.clone(), cons_b(b0.clone(), btb.clone()), e_b.clone()),
                            back2,
                            &body_at,
                        )
                    };
                    e.finish_child(e.mk_lam(hn_id, BinderInfo::Default, hn_ty, back3))
                };

                // Bool.rec wmot false_minor true_minor (bvIsCons as_) : (bvIsCons as_ = bvIsCons as_) → goal aa b c
                // motive `fun w => (bvIsCons as = w) → goal aa b c` eliminates into Prop (Sort 0).
                let w_rec = Expr::apps(
                    Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
                    [wmot, false_minor, true_minor, bv_is_cons(as_.clone())],
                );
                // apply the reflexivity witness `Eq.refl (bvIsCons as_)`.
                let applied = Expr::app(w_rec, {
                    Expr::apps(
                        Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
                        [bool_ty(), bv_is_cons(as_.clone())],
                    )
                });
                let r = d.mk_lam(lh_id, BinderInfo::Default, lenh, applied);
                let r = d.mk_lam(ch_id, BinderInfo::Default, consh, r);
                let r = d.mk_lam(c_id, BinderInfo::Default, bool_ty(), r);
                d.finish_child(d.mk_lam(b_id, BinderInfo::Default, list_bool(), r))
            };
            let r = c0.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
            let r = c0.mk_lam(as_id, BinderInfo::Default, list_bool(), r);
            c0.finish(c0.mk_lam(a0_id, BinderInfo::Default, bool_ty(), r))
        };
        // ── assemble slt_flag_bridge : ∀ a b, bvIsCons a = true → bvLen a = bvLen b →
        //      bvSLtReal a b = bxor(N,V)   (specializes the c-generalized core at c=true).
        // bvSLtReal a b ≡ Not(carryOut(flipMsb a)(bvNot(flipMsb b)) true) = lhs a b true (defeq),
        // so the c=true instance of the core IS the bridge.
        let ty = {
            let mut c = EnvDeclBuilder::new();
            let (a_id, a) = c.fresh_local(list_bool());
            let (b_id, bb) = c.fresh_local(list_bool());
            let consh = istrue(bv_is_cons(a.clone()));
            let (ch_id, _ch) = c.fresh_local(consh.clone());
            let lenh = eq_nat(bvlen(a.clone()), bvlen(bb.clone()));
            let (lh_id, _lh) = c.fresh_local(lenh.clone());
            // conclusion uses bvSLtReal (the faithful predicate) on the LHS:
            let concl = eq_bool(
                bv_slt_real(a.clone(), bb.clone()),
                rhs(a.clone(), bb.clone(), btrue()),
            );
            let t = c.mk_pi(lh_id, BinderInfo::Default, lenh, concl);
            let t = c.mk_pi(ch_id, BinderInfo::Default, consh, t);
            let t = c.mk_pi(b_id, BinderInfo::Default, list_bool(), t);
            c.finish(c.mk_pi(a_id, BinderInfo::Default, list_bool(), t))
        };
        let val = {
            let mut c = EnvDeclBuilder::new();
            let (a_id, a) = c.fresh_local(list_bool());
            let (b_id, bb) = c.fresh_local(list_bool());
            let consh = istrue(bv_is_cons(a.clone()));
            let (ch_id, ch) = c.fresh_local(consh.clone());
            let lenh = eq_nat(bvlen(a.clone()), bvlen(bb.clone()));
            let (lh_id, lh) = c.fresh_local(lenh.clone());
            // (List.rec motive_a nil_a cons_a a) bb true ch lh : goal a bb true
            //   = eq_bool(lhs a bb true, rhs a bb true) ; lhs a bb true ≡ bvSLtReal a bb (defeq).
            let rec = list_rec_prop(motive_a.clone(), nil_a.clone(), cons_a.clone(), a.clone());
            let applied = Expr::apps(rec, [bb.clone(), btrue(), ch, lh]);
            let r = c.mk_lam(lh_id, BinderInfo::Default, lenh, applied);
            let r = c.mk_lam(ch_id, BinderInfo::Default, consh, r);
            let r = c.mk_lam(b_id, BinderInfo::Default, list_bool(), r);
            c.finish(c.mk_lam(a_id, BinderInfo::Default, list_bool(), r))
        };
        // PROVED (#56, telescope-collapse): the slt bridge is a SINGLE List.rec on `a`
        // with the b/as/bs shapes converted via standalone inversion lemmas
        // (consOfIsCons / isConsOfLenSucc / nilOfNotIsCons / nilOfLenZero) used as
        // Eq.subst rewrites — NO nested recursor, so the #53 telescope motive-redex
        // cannot arise. bvFlipMsb/bvLastBit head-transparency on a 2+-cons (verified)
        // makes the cons-step def-eq hold in cons-form. Registered unconditionally
        // (kernel-checked at registration).
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::SLT_FLAG_BRIDGE),
            level_params: vec![],
            type_: ty,
            value: val,
        })?;

        // ── slt_value_bridge : ∀ a b vt ve, bvIsCons a = true → bvLen a = bvLen b →
        //     bvIteVal (Bool.not (Bool.xor N V)) ve vt = bvIteVal (bvSLtReal a b) vt ve
        // where N = bvLastBit(addRecM a (bvNot b) true), V = And(bxor(msb a,msb b),bxor(N,msb a)).
        // The machine emits the inverted NZCV signed-LT flag `N⊕V` (the AArch64 `LT` cond);
        // the IR reflects to `bvSLtReal`. Composes `slt_flag_bridge` (bvSLtReal = xor N V) with
        // branch-inversion (`iteVal_not`), mirroring `ule_value_bridge`. N,V reuse the
        // flag-bridge `rhs` (= xor N V at carry-in true).
        {
            let m_cond = |a: Expr, b: Expr| rhs(a, b, btrue()); // = Bool.xor N V at c=true
            let ty = {
                let mut c = EnvDeclBuilder::new();
                let (a_id, a) = c.fresh_local(list_bool());
                let (b_id, bb) = c.fresh_local(list_bool());
                let (vt_id, vt) = c.fresh_local(list_bool());
                let (ve_id, ve) = c.fresh_local(list_bool());
                let consh = istrue(bv_is_cons(a.clone()));
                let (ch_id, _ch) = c.fresh_local(consh.clone());
                let lenh = eq_nat(bvlen(a.clone()), bvlen(bb.clone()));
                let (lh_id, _lh) = c.fresh_local(lenh.clone());
                let concl = eq_list(
                    bv_ite_val(bnot(m_cond(a.clone(), bb.clone())), ve.clone(), vt.clone()),
                    bv_ite_val(bv_slt_real(a.clone(), bb.clone()), vt.clone(), ve.clone()),
                );
                let t = c.mk_pi(lh_id, BinderInfo::Default, lenh, concl);
                let t = c.mk_pi(ch_id, BinderInfo::Default, consh, t);
                let t = c.mk_pi(ve_id, BinderInfo::Default, list_bool(), t);
                let t = c.mk_pi(vt_id, BinderInfo::Default, list_bool(), t);
                let t = c.mk_pi(b_id, BinderInfo::Default, list_bool(), t);
                c.finish(c.mk_pi(a_id, BinderInfo::Default, list_bool(), t))
            };
            let val = {
                let mut c = EnvDeclBuilder::new();
                let (a_id, a) = c.fresh_local(list_bool());
                let (b_id, bb) = c.fresh_local(list_bool());
                let (vt_id, vt) = c.fresh_local(list_bool());
                let (ve_id, ve) = c.fresh_local(list_bool());
                let consh = istrue(bv_is_cons(a.clone()));
                let (ch_id, ch) = c.fresh_local(consh.clone());
                let lenh = eq_nat(bvlen(a.clone()), bvlen(bb.clone()));
                let (lh_id, lh) = c.fresh_local(lenh.clone());
                let cond = m_cond(a.clone(), bb.clone()); // xor N V
                let slt = bv_slt_real(a.clone(), bb.clone());
                // flag : bvSLtReal a b = xor N V ; symm : xor N V = bvSLtReal a b
                let flag = Expr::apps(
                    Expr::const_str(names::SLT_FLAG_BRIDGE),
                    [a.clone(), bb.clone(), ch, lh],
                );
                let flag_symm = Expr::apps(
                    Expr::const_(
                        Name::from_string("Eq.symm"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [bool_ty(), slt.clone(), cond.clone(), flag],
                );
                let l1 = Level::succ(Level::zero());
                // step_not : Bool.not (xor N V) = Bool.not (bvSLtReal a b)
                let cong_not = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (z_id, z) = d.fresh_local(bool_ty());
                    d.finish_child(d.mk_lam(z_id, BinderInfo::Default, bool_ty(), bnot(z)))
                };
                let cg_bool = |a1: Expr, a2: Expr, f: Expr, hh: Expr| {
                    Expr::apps(
                        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
                        [bool_ty(), bool_ty(), a1, a2, f, hh],
                    )
                };
                let step_not = cg_bool(cond.clone(), slt.clone(), cong_not, flag_symm);
                // step_ite : bvIteVal (not (xor N V)) ve vt = bvIteVal (not (bvSLtReal a b)) ve vt
                let cong_ite = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (p_id, p) = d.fresh_local(bool_ty());
                    d.finish_child(d.mk_lam(
                        p_id,
                        BinderInfo::Default,
                        bool_ty(),
                        bv_ite_val(p, ve.clone(), vt.clone()),
                    ))
                };
                let cg_ite = |a1: Expr, a2: Expr, f: Expr, hh: Expr| {
                    Expr::apps(
                        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
                        [bool_ty(), list_bool(), a1, a2, f, hh],
                    )
                };
                let step_ite = cg_ite(bnot(cond.clone()), bnot(slt.clone()), cong_ite, step_not);
                // step_inv : bvIteVal (not (bvSLtReal a b)) ve vt = bvIteVal (bvSLtReal a b) vt ve
                let step_inv = Expr::apps(
                    Expr::const_str(names::ITE_VAL_NOT),
                    [slt.clone(), ve.clone(), vt.clone()],
                );
                let proof = eq_trans_list(
                    bv_ite_val(bnot(cond.clone()), ve.clone(), vt.clone()),
                    bv_ite_val(bnot(slt.clone()), ve.clone(), vt.clone()),
                    bv_ite_val(slt.clone(), vt.clone(), ve.clone()),
                    step_ite,
                    step_inv,
                );
                let r = c.mk_lam(lh_id, BinderInfo::Default, lenh, proof);
                let r = c.mk_lam(ch_id, BinderInfo::Default, consh, r);
                let r = c.mk_lam(ve_id, BinderInfo::Default, list_bool(), r);
                let r = c.mk_lam(vt_id, BinderInfo::Default, list_bool(), r);
                let r = c.mk_lam(b_id, BinderInfo::Default, list_bool(), r);
                c.finish(c.mk_lam(a_id, BinderInfo::Default, list_bool(), r))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::SLT_VALUE_BRIDGE),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }

        // ── bvSLeReal a b := Bool.or (bvSLtReal a b) (bvBeq a b) ──────────────
        {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(list_bool());
                let (bb_id, bb) = b.fresh_local(list_bool());
                let body = bor(
                    bv_slt_real(a.clone(), bb.clone()),
                    bv_beq(a.clone(), bb.clone()),
                );
                let r = b.mk_lam(bb_id, BinderInfo::Default, list_bool(), body);
                b.finish(b.mk_lam(a_id, BinderInfo::Default, list_bool(), r))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::BV_SLE_REAL),
                level_params: vec![],
                type_: Expr::arrow(list_bool(), Expr::arrow(list_bool(), bool_ty())),
                value: val,
                is_reducible: true,
            })?;
        }

        // ── sle_value_bridge : ∀ a b vt ve, bvIsCons a = true → bvLen a = bvLen b →
        //     bvIteVal (And(Not(bvIsZero(sub)), Not(xor N V))) ve vt = bvIteVal (bvSLeReal a b) vt ve.
        // Machine emits the inverted `a > b` flag `And(a≠b, a>=s b)`; IR reflects to bvSLeReal.
        // Compose: (1) beq_eq_isZero_sub: bvBeq = bvIsZero(sub) ⇒ rewrite the isZero conjunct to bvBeq;
        //   (2) slt_flag_bridge: bvSLtReal = xor N V ⇒ rewrite the (xor N V) conjunct to bvSLtReal;
        //   (3) demorgan_and_not: And(¬p,¬q) = ¬(Or p q) with p=bvSLtReal, q=bvBeq ⇒ ¬(bvSLeReal);
        //   (4) iteVal_not: bvIteVal (¬bvSLeReal) ve vt = bvIteVal bvSLeReal vt ve.
        {
            let sub_of = |a: Expr, b: Expr| add_rec_m(a, bv_not(b), btrue());
            let iz = |a: Expr, b: Expr| bv_is_zero(sub_of(a, b));
            let nv = |a: Expr, b: Expr| rhs(a, b, btrue()); // xor N V
                                                            // machine predicate M(a,b) = and(not(isZero sub), not(xor N V))
            let m_pred = |a: Expr, b: Expr| band(bnot(iz(a.clone(), b.clone())), bnot(nv(a, b)));
            let ty = {
                let mut c = EnvDeclBuilder::new();
                let (a_id, a) = c.fresh_local(list_bool());
                let (b_id, bb) = c.fresh_local(list_bool());
                let (vt_id, vt) = c.fresh_local(list_bool());
                let (ve_id, ve) = c.fresh_local(list_bool());
                let consh = istrue(bv_is_cons(a.clone()));
                let (ch_id, _ch) = c.fresh_local(consh.clone());
                let lenh = eq_nat(bvlen(a.clone()), bvlen(bb.clone()));
                let (lh_id, _lh) = c.fresh_local(lenh.clone());
                let sle = Expr::apps(Expr::const_str(names::BV_SLE_REAL), [a.clone(), bb.clone()]);
                let concl = eq_list(
                    bv_ite_val(m_pred(a.clone(), bb.clone()), ve.clone(), vt.clone()),
                    bv_ite_val(sle, vt.clone(), ve.clone()),
                );
                let t = c.mk_pi(lh_id, BinderInfo::Default, lenh, concl);
                let t = c.mk_pi(ch_id, BinderInfo::Default, consh, t);
                let t = c.mk_pi(ve_id, BinderInfo::Default, list_bool(), t);
                let t = c.mk_pi(vt_id, BinderInfo::Default, list_bool(), t);
                let t = c.mk_pi(b_id, BinderInfo::Default, list_bool(), t);
                c.finish(c.mk_pi(a_id, BinderInfo::Default, list_bool(), t))
            };
            let val = {
                let mut c = EnvDeclBuilder::new();
                let (a_id, a) = c.fresh_local(list_bool());
                let (b_id, bb) = c.fresh_local(list_bool());
                let (vt_id, vt) = c.fresh_local(list_bool());
                let (ve_id, ve) = c.fresh_local(list_bool());
                let consh = istrue(bv_is_cons(a.clone()));
                let (ch_id, ch) = c.fresh_local(consh.clone());
                let lenh = eq_nat(bvlen(a.clone()), bvlen(bb.clone()));
                let (lh_id, lh) = c.fresh_local(lenh.clone());
                let l1 = Level::succ(Level::zero());
                let slt = bv_slt_real(a.clone(), bb.clone());
                let beq = bv_beq(a.clone(), bb.clone());
                let nvc = nv(a.clone(), bb.clone()); // xor N V
                let isz = iz(a.clone(), bb.clone()); // bvIsZero(sub)
                let m = m_pred(a.clone(), bb.clone()); // and(¬isz, ¬nv)
                let not_sle = bnot(bor(slt.clone(), beq.clone())); // ¬(or slt beq) = ¬bvSLeReal (defeq)
                let sle = Expr::apps(Expr::const_str(names::BV_SLE_REAL), [a.clone(), bb.clone()]);
                let cg_bool = |a1: Expr, a2: Expr, f: Expr, hh: Expr| {
                    Expr::apps(
                        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
                        [bool_ty(), bool_ty(), a1, a2, f, hh],
                    )
                };
                let eq_trans_bool = |x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr| {
                    Expr::apps(
                        Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
                        [bool_ty(), x, y, z, h1, h2],
                    )
                };
                let eq_symm_bool = |x: Expr, y: Expr, h: Expr| {
                    Expr::apps(
                        Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
                        [bool_ty(), x, y, h],
                    )
                };
                // bridge_beq : bvBeq = bvIsZero(sub)   [beq_eq_isZero_sub a b lh]
                let bridge_beq = Expr::apps(
                    Expr::const_str(names::BEQ_EQ_ISZERO_SUB),
                    [a.clone(), bb.clone(), lh.clone()],
                );
                // flag : bvSLtReal = xor N V           [slt_flag_bridge a b ch lh] — but lh moved; rebuild lh.
                // (lh consumed above; the bridge needs its own — re-fetch is impossible, so reorder:)
                let _ = &bridge_beq;
                // Build m = and(¬slt? no): we want m = and(¬isz, ¬nv) -> and(¬beq, ¬slt) -> ¬(or slt beq).
                //   step_iz : and(¬isz, ¬nv) = and(¬beq, ¬nv)   via congrArg(fun z=>and(¬z,¬nv))(symm bridge_beq)
                //   step_nv : and(¬beq, ¬nv) = and(¬beq, ¬slt)  via congrArg(fun z=>and(¬beq,¬z))(symm flag)
                //   step_dm : and(¬beq, ¬slt)... we want and(¬slt,¬beq) for demorgan(slt,beq). reorder:
                // Simpler: target ¬(or slt beq). demorgan_and_not slt beq : and(¬slt,¬beq) = ¬(or slt beq).
                //   So massage m = and(¬isz,¬nv) into and(¬slt,¬beq):
                //     a) and(¬isz,¬nv) = and(¬nv,¬isz)? and is not comm by defeq. Instead rewrite each slot:
                //        and(¬isz,¬nv) --(isz->beq)--> and(¬beq,¬nv) --(nv->slt)--> and(¬beq,¬slt).
                //     demorgan wants and(¬slt,¬beq). We have and(¬beq,¬slt). Use demorgan_and_not beq slt :
                //        and(¬beq,¬slt) = ¬(or beq slt). Then ¬(or beq slt) vs ¬bvSLeReal=¬(or slt beq):
                //        or beq slt = or slt beq? not defeq. So instead order m as and(¬slt,¬beq) from the start
                //        by rewriting nv->slt FIRST then isz->beq: and(¬isz,¬nv)--(nv->slt)-->and(¬isz,¬slt)
                //        --(isz->beq)-->and(¬beq,¬slt). still beq,slt order. The machine m has isz as FIRST
                //        conjunct, slt-side (nv) as SECOND. bvSLeReal := or(slt, beq) (slt first). demorgan
                //        slt beq gives and(¬slt,¬beq). To match, rewrite m's FIRST(¬isz)->¬? we need ¬slt first.
                //   Cleanest: prove m = ¬(or slt beq) directly by rewriting into and(¬slt,¬beq) via TWO congrArgs
                //   that ALSO swap: not worth it. Instead: bvSLeReal flips to or(slt,beq); but De Morgan target
                //   is and(¬slt,¬beq). Rewrite m (=and(¬isz,¬nv)) to and(¬slt,¬beq):
                //     m --(¬isz -> ¬slt? NO, isz=beq not slt).
                // Correct mapping: ¬isz <-> ¬beq (subtract-zero), ¬nv <-> ¬slt (flag). So m = and(¬beq,¬slt)
                //   after rewrites. bvSLeReal = or(slt,beq). demorgan_and_not slt beq : and(¬slt,¬beq)=¬(or slt beq).
                //   and(¬beq,¬slt) ≠ and(¬slt,¬beq) syntactically but Bool.and is NOT defeq-comm. So define the
                //   bridge's m_pred with the conjunct order MATCHING demorgan: but the MACHINE fixes isz-first.
                // Resolution: use demorgan_and_not beq slt : and(¬beq,¬slt) = ¬(or beq slt) and define bvSLeReal
                //   as or(slt,beq); then ¬(or beq slt) vs ¬(or slt beq) need or-comm. Bool.or also not defeq-comm.
                // FINAL: define bvSLeReal := or(slt,beq); prove m = ¬bvSLeReal via the chain to and(¬slt,¬beq)
                //   by rewriting m's slots in the order that yields slt FIRST. m=and(¬isz,¬nv): rewrite the
                //   SECOND slot ¬nv->¬slt (congrArg fun z=>and(¬isz,¬z)) giving and(¬isz,¬slt), then FIRST slot
                //   ¬isz->¬beq giving and(¬beq,¬slt). Still beq-first. The genuine fix is one extra and-comm
                //   lemma OR define bvSLeReal := or(beq,slt). Per the directive 'bvSLeReal := Or(bvSLtReal,bvBeq)'
                //   we keep slt-first and add and_comm via a 2x2 Bool.rec lemma inline.
                let flag = Expr::apps(
                    Expr::const_str(names::SLT_FLAG_BRIDGE),
                    [a.clone(), bb.clone(), ch, lh],
                );
                // step_iz: and(¬isz,¬nv) = and(¬beq,¬nv)  [congrArg (fun z=>and(¬z,¬nv)) (symm bridge_beq)]
                let cong_iz = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (z_id, z) = d.fresh_local(bool_ty());
                    d.finish_child(d.mk_lam(
                        z_id,
                        BinderInfo::Default,
                        bool_ty(),
                        band(bnot(z), bnot(nvc.clone())),
                    ))
                };
                let symm_beq = eq_symm_bool(beq.clone(), isz.clone(), bridge_beq);
                let step_iz = cg_bool(isz.clone(), beq.clone(), cong_iz, symm_beq);
                // step_nv: and(¬beq,¬nv) = and(¬beq,¬slt)  [congrArg (fun z=>and(¬beq,¬z)) (symm flag)]
                let cong_nv = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (z_id, z) = d.fresh_local(bool_ty());
                    d.finish_child(d.mk_lam(
                        z_id,
                        BinderInfo::Default,
                        bool_ty(),
                        band(bnot(beq.clone()), bnot(z)),
                    ))
                };
                let symm_flag = eq_symm_bool(slt.clone(), nvc.clone(), flag);
                let step_nv = cg_bool(nvc.clone(), slt.clone(), cong_nv, symm_flag);
                // m = and(¬isz,¬nv) -> and(¬beq,¬nv) -> and(¬beq,¬slt)
                let m_eq_bs = eq_trans_bool(
                    m.clone(),
                    band(bnot(beq.clone()), bnot(nvc.clone())),
                    band(bnot(beq.clone()), bnot(slt.clone())),
                    step_iz,
                    step_nv,
                );
                // and_comm_not : and(¬beq,¬slt) = and(¬slt,¬beq)  [2x2 Bool.rec, ground refl]
                let and_comm = and_comm_not_local(&c, bnot(beq.clone()), bnot(slt.clone()));
                let m_eq_sb = eq_trans_bool(
                    m.clone(),
                    band(bnot(beq.clone()), bnot(slt.clone())),
                    band(bnot(slt.clone()), bnot(beq.clone())),
                    m_eq_bs,
                    and_comm,
                );
                // demorgan_and_not slt beq : and(¬slt,¬beq) = ¬(or slt beq) = not_sle
                let dm = Expr::apps(
                    Expr::const_str(names::DEMORGAN_AND_NOT),
                    [slt.clone(), beq.clone()],
                );
                let m_eq_notsle = eq_trans_bool(
                    m.clone(),
                    band(bnot(slt.clone()), bnot(beq.clone())),
                    not_sle.clone(),
                    m_eq_sb,
                    dm,
                );
                // step_ite: bvIteVal m ve vt = bvIteVal not_sle ve vt
                let cong_ite = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (p_id, p) = d.fresh_local(bool_ty());
                    d.finish_child(d.mk_lam(
                        p_id,
                        BinderInfo::Default,
                        bool_ty(),
                        bv_ite_val(p, ve.clone(), vt.clone()),
                    ))
                };
                let cg_ite = |a1: Expr, a2: Expr, f: Expr, hh: Expr| {
                    Expr::apps(
                        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
                        [bool_ty(), list_bool(), a1, a2, f, hh],
                    )
                };
                let step_ite = cg_ite(m.clone(), not_sle.clone(), cong_ite, m_eq_notsle);
                // step_inv: iteVal_not bvSLeReal ve vt : bvIteVal (¬bvSLeReal) ve vt = bvIteVal bvSLeReal vt ve
                //   (¬bvSLeReal ≡ not_sle defeq, since bvSLeReal := or slt beq).
                let step_inv = Expr::apps(
                    Expr::const_str(names::ITE_VAL_NOT),
                    [sle.clone(), ve.clone(), vt.clone()],
                );
                let proof = eq_trans_list(
                    bv_ite_val(m, ve.clone(), vt.clone()),
                    bv_ite_val(not_sle, ve.clone(), vt.clone()),
                    bv_ite_val(sle, vt.clone(), ve.clone()),
                    step_ite,
                    step_inv,
                );
                let r = c.mk_lam(lh_id, BinderInfo::Default, lenh, proof);
                let r = c.mk_lam(ch_id, BinderInfo::Default, consh, r);
                let r = c.mk_lam(ve_id, BinderInfo::Default, list_bool(), r);
                let r = c.mk_lam(vt_id, BinderInfo::Default, list_bool(), r);
                let r = c.mk_lam(b_id, BinderInfo::Default, list_bool(), r);
                c.finish(c.mk_lam(a_id, BinderInfo::Default, list_bool(), r))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(names::SLE_VALUE_BRIDGE),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }
        Ok(())
    }
}

/// `Eq.refl.{1} Nat v` built without consuming an outer hypothesis (local to a builder ctx).
#[cfg(test)]
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
fn eq_refl_nat_local(_c: &EnvDeclBuilder, v: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat_ty(), v],
    )
}

/// `and_comm_not : and x y = and y x` at the SPECIFIC x,y (proved by a 2×2 Bool.rec,
/// ground refl per leaf). Used to reorder the SLE De Morgan conjuncts.
fn and_comm_not_local(parent: &EnvDeclBuilder, x: Expr, y: Expr) -> Expr {
    // Bool.rec on x then y, each leaf refl of `and xv yv` (= and yv xv at ground bits).
    // We instead build a direct proof: the goal `and x y = and y x` is NOT refl for
    // symbolic x,y, so case both via Bool.rec with the dependent motive.
    let l1 = Level::succ(Level::zero());
    let band = |p: Expr, q: Expr| Expr::apps(Expr::const_str("Bool.and"), [p, q]);
    let eqb = |p: Expr, q: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            [Expr::const_str("Bool"), p, q],
        )
    };
    let reflb = |v: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            [Expr::const_str("Bool"), v],
        )
    };
    let btrue = Expr::const_str("Bool.true");
    let bfalse = Expr::const_str("Bool.false");
    // motive_x xv := and xv y = and y xv
    let xmot = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (xv_id, xv) = d.fresh_local(Expr::const_str("Bool"));
        d.finish_child(d.mk_lam(
            xv_id,
            BinderInfo::Default,
            Expr::const_str("Bool"),
            eqb(band(xv.clone(), y.clone()), band(y.clone(), xv)),
        ))
    };
    // For a fixed xv, case y: leaf = refl of (and xv yv).
    let mk_y = |xv: Expr| -> Expr {
        let d = EnvDeclBuilder::child_of(parent);
        let ymot = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (yv_id, yv) = e.fresh_local(Expr::const_str("Bool"));
            e.finish_child(e.mk_lam(
                yv_id,
                BinderInfo::Default,
                Expr::const_str("Bool"),
                eqb(band(xv.clone(), yv.clone()), band(yv.clone(), xv.clone())),
            ))
        };
        let leaf = |yv: Expr| reflb(band(xv.clone(), yv));
        // motive eliminates into Prop (Eq is Sort 0) -> Bool.rec.{0}.
        let rec = Expr::apps(
            Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            [ymot, leaf(bfalse.clone()), leaf(btrue.clone()), y.clone()],
        );
        d.finish_child(rec)
    };
    let xf = mk_y(bfalse.clone());
    let xt = mk_y(btrue.clone());
    Expr::apps(
        Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
        [xmot, xf, xt, x],
    )
}

/// `@Eq.trans.{1} (List Bool) a b c h1 h2`.
fn eq_trans_list(a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [list_bool(), a, b, c, h1, h2],
    )
}

/// `@List.rec.{1,0} Bool (motive : List Bool → Sort 1) nil_case cons_case major`
/// — eliminate a `List Bool` into a `Type` (Sort 1) result.
fn list_rec_type1(motive: Expr, nil_case: Expr, cons_case: Expr, major: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("List.rec"),
            vec![Level::succ(Level::zero()), Level::zero()],
        ),
        [bool_ty(), motive, nil_case, cons_case, major],
    )
}

/// `@List.rec.{0,0} Bool (motive : List Bool → Prop) nil_case cons_case major`.
fn list_rec_prop(motive: Expr, nil_case: Expr, cons_case: Expr, major: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("List.rec"),
            vec![Level::zero(), Level::zero()],
        ),
        [bool_ty(), motive, nil_case, cons_case, major],
    )
}

/// `@Nat.rec.{1} (motive : Nat → Sort 1) zero_case succ_case major`.
fn nat_rec_type1(motive: Expr, zero_case: Expr, succ_case: Expr, major: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [motive, zero_case, succ_case, major],
    )
}

#[cfg(test)]
#[path = "bitvec_coercion_tests.rs"]
mod tests;
