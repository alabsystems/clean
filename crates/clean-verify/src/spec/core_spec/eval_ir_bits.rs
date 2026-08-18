// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `EvalIR` — **the O(bit-length) `Nat` substrate**: a strict doubling, a left
//! shift, a bit-length scan, and one restoring driver that is division,
//! remainder and multiplication depending on the increment it is given.
//!
//! Everything here is built from `Nat.add`, `Nat.sub`, `Nat.succ`, `Nat.rec`
//! and `Bool.rec` — the same primitives [`super::eval_ir_state`]'s
//! `ir_nat_pow2` and `ir_nat_rem` have always relied on. **No accelerated
//! constant is added and no new trust is bought**: `Nat.div`, `Nat.mod`,
//! `Nat.mul`, `Nat.pow`, `Nat.beq`, `Nat.ble`, `Nat.shiftLeft` and
//! `Nat.shiftRight` are all natively reduced by the kernel and none of them
//! appears here, for exactly the reason [`super::eval_ir_state`] refuses them
//! for `ir_nat_rem`: their declared bodies are never consulted.
//!
//! ## Why this module exists
//!
//! `ir_nat_div` fuels `ir_div_go` by repeated subtraction and is **linear in
//! the quotient**. That is affordable at the quotients the integer lane needs
//! (a width-`w` residue has quotient 0, an exponent field extract has quotient
//! ≤ 2047) and unaffordable at the quotients binary64 rounding needs. Measured
//! in the `EvalIr` bundle at this commit, one declaration each:
//!
//! ```text
//! ir_nat_div                       quotient  2047      0.428 s
//! ir_nat_div                       quotient  4096      0.864 s   (x2.02 — linear)
//! ir_nat_div                       quotient  2^52-1    ~39,700 yr (extrapolated; never run)
//! ir_dm_quot (ir_nat_divpow2 …)    quotient  2047      0.011 s
//! ir_dm_quot (ir_nat_divpow2 …)    quotient  4096      0.008 s
//! ir_dm_quot (ir_nat_divpow2 …)    quotient  2^52-1    0.040 s
//! ```
//!
//! The right-hand column does not grow with the quotient. It grows with the
//! **bit length**, and 53 bits is 53 bits.
//!
//! ## The strict doubling, and the measurement that forced it
//!
//! `ir_nat_dbl n` is `2n`, written as a `Nat.rec` that **peels its argument
//! first** and then doubles the predecessor:
//!
//! ```text
//! ir_nat_dbl n = Nat.rec … Nat.zero (fun p _ => Nat.succ (Nat.add p (Nat.succ p))) n
//! ```
//!
//! `Nat.add n n` would be shorter and it is **wrong here for a measured
//! reason**. `Nat.add x x` names `x` twice, so a `k`-deep doubling ladder over
//! an argument that is still a REDEX is a term with `2^k` leaves; whether that
//! costs `k` or `2^k` depends on whether the kernel happens to share the
//! evaluation, and it does not always. The bomb, isolated:
//!
//! ```text
//! ir_dm_rem (ir_nat_divpow2 Nat.zero Nat.zero)                       0.003 s
//! ir_dm_rem (ir_nat_divpow2 (ir_nat_shl Nat.zero 53) Nat.zero)       KILLED at > 250 s
//!                                        ^^^^^^^^^^ a redex, not a literal
//! ```
//!
//! With the strict doubling the second one is **0.014 s**. `ir_nat_dbl` forces
//! its argument to a constructor before duplicating anything, and the kernel's
//! native `BigNat` peel makes the predecessor a literal, so every rung of the
//! ladder is a literal and the ladder is linear.
//!
//! **This explains the open cost anomaly** that
//! `designs/2026-08-16-float-finite-fragment-scope.md` §3.5/§6 recorded and
//! could not account for (`f2_magout3 0 1022` killed at > 2 min 30 s, and
//! `1.0 + (-1.0)` with it). It was never about the zero significand: it was
//! about a renormalising left shift applied to an unreduced term. With
//! `ir_nat_dbl` the same computation is **0.037 s**, and the guard the scope
//! document proposed — dispatch `ir_f64_opposite` first so the pipeline never
//! sees `m = 0` — is kept because the rule is exact, not because the cost
//! cliff is still there.
//!
//! `ir_nat_dbl_eq` proves `ir_nat_dbl n = Nat.add n n` for every `n`, so the
//! restructuring is a kernel-checked fact and not a reading of two
//! definitions. That is the `ir_nat_ltb_sub_eq` discipline applied here.
//!
//! ## One driver, three operations
//!
//! `ir_dm_go inc hi fuel p st` ascends `p` by doubling while `p <= hi`, then
//! applies `ir_dm_step inc p` on the way OUT — so the powers are visited in
//! DESCENDING order without a halving primitive, which is the circularity that
//! makes the naive route look impossible. Each step is one comparison, one
//! `Nat.sub` and one strict doubling:
//!
//! ```text
//! ir_dm_step2 inc w r q = if r < w then (r, 2q) else (r - w, 2q + inc)
//! ```
//!
//! * `inc = 1`  — restoring division: `ir_nat_divmod m dv` starts at `p = dv`
//!   and yields `(m mod dv, m / dv)`.
//! * `inc = a`  — shift-and-add multiplication: `ir_nat_mulb a b` starts at
//!   `p = 1` with `r = b`, so the bits of `b` are consumed most-significant
//!   first and the accumulator collects `2q + a` on each set bit, i.e. `a * b`.
//!
//! **`ir_nat_divmod` requires `dv >= 1`**, exactly as `ir_nat_div` does. At
//! `dv = 0` the ascent never terminates on its guard and the fuel runs out; no
//! caller here reaches it (`ir_nat_pow2 s >= 1` always, and the float callers
//! pass a significand of a `fin_`-classified operand, which is non-zero).
//!
//! ## What this does NOT claim
//!
//! `ir_nat_divmod` is **not proved equal to** `ir_nat_div` / `ir_nat_rem`, and
//! `ir_nat_mulb` is **not proved equal to** `ir_nat_mul`. Those agreement
//! theorems are two different algorithms agreeing, which in this substrate —
//! no automation, explicit recursor terms — goes through a loop invariant plus
//! uniqueness of quotient, and they are NOT attempted here. What is here
//! instead is a **kernel-EXECUTED differential ladder**
//! (`add_eval_ir_bits_witnesses`): every new operation is run against the
//! reference definition at every argument where the reference is affordable,
//! by the kernel, as `Eq.refl`. That is the same evidential bar
//! [`super::eval_ir_float`] already sets for its tables, and it is not a proof.
//! The missing theorems are named in this module's doc so the gap is visible
//! rather than assumed away.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Register the O(bit-length) `Nat` substrate.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_bits(&mut self) -> Result<(), SpecError> {
        self.add_eval_ir_bits_defs()?;
        self.add_eval_ir_bits_witnesses()
    }

    fn add_eval_ir_bits_defs(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            concat!(
                "def ir_nat_dbl (n : Nat) : Nat := ",
                "Nat.rec (fun (_ : Nat) => Nat) Nat.zero ",
                "(fun (p : Nat) (_ : Nat) => Nat.succ (Nat.add p (Nat.succ p))) n",
            ),
            "*** THE STRICT DOUBLING. *** 2n, written so the argument is PEELED before anything \
             is duplicated. `Nat.add n n` computes the same number and is a cost bomb: it names n \
             twice, so a k-deep doubling ladder over an unreduced argument is a term with 2^k \
             leaves. Measured: `ir_dm_rem (ir_nat_divpow2 (ir_nat_shl Nat.zero 53) Nat.zero)` was \
             KILLED at over 250 s through `Nat.add x x` and is 0.014 s through this. The peel \
             makes the predecessor a native BigNat literal, so every rung of the ladder is a \
             literal. ir_nat_dbl_eq proves this IS `Nat.add n n`. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_nat_succ_add (a : Nat) (b : Nat) : ",
                "Eq Nat (Nat.add (Nat.succ a) b) (Nat.succ (Nat.add a b)) := ",
                "Nat.rec (fun (k : Nat) => ",
                "Eq Nat (Nat.add (Nat.succ a) k) (Nat.succ (Nat.add a k))) ",
                "(Eq.refl Nat (Nat.succ a)) ",
                "(fun (k : Nat) (ih : Eq Nat (Nat.add (Nat.succ a) k) ",
                "(Nat.succ (Nat.add a k))) => ",
                "ir_eq_cong Nat Nat Nat.succ (Nat.add (Nat.succ a) k) ",
                "(Nat.succ (Nat.add a k)) ih) b",
            ),
            "(succ a) + b = succ (a + b). Nat.add recurses on its SECOND argument, so this is the \
             direction that does not hold by iota and it needs an induction on b. The foundation \
             stage proves `0 + n = n` (nat_add_zero) and this is its successor twin; it lives \
             here rather than there for the same reason ir_nat_sub_zero_left does — the \
             dependency-scoped EvalIr bundle does not carry add_foundation_arith_lemmas. \
             DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_nat_dbl_eq (n : Nat) : Eq Nat (ir_nat_dbl n) (Nat.add n n) := ",
                "Nat.rec (fun (k : Nat) => Eq Nat (ir_nat_dbl k) (Nat.add k k)) ",
                "(Eq.refl Nat Nat.zero) ",
                "(fun (p : Nat) (_ : Eq Nat (ir_nat_dbl p) (Nat.add p p)) => ",
                "Eq.symm Nat (Nat.add (Nat.succ p) (Nat.succ p)) ",
                "(ir_nat_dbl (Nat.succ p)) ",
                "(ir_eq_cong Nat Nat Nat.succ (Nat.add (Nat.succ p) p) ",
                "(Nat.succ (Nat.add p p)) (ir_nat_succ_add p p))) n",
            ),
            "*** THE DOUBLING AGREEMENT THEOREM. *** The strict doubling the substrate runs and \
             the ordinary `Nat.add n n` are the SAME FUNCTION, at every argument. Same shape as \
             ir_nat_ltb_sub_eq: a definitional restructuring made for cost, plus a kernel-checked \
             equation so the swap is proved rather than read off two definitions. \
             \n\nThe successor case needs no induction hypothesis — `ir_nat_dbl (succ p)` is \
             `succ (p + succ p)` by iota and `succ p + succ p` is `succ (succ p + p)` by iota, so \
             one ir_nat_succ_add under an ir_eq_cong closes it. The hypothesis is bound and unused, \
             and that is deliberate: it says the doubling is not really a recursion, it is a \
             single peel. DerivedProved, zero axiom_deps.",
        )?;

        self.add_inductive(
            "inductive IRDivMod : Type\n| mk : Nat -> Nat -> IRDivMod",
            "A remainder and a quotient, in that field order. A two-field non-recursive \
             inductive, not a pair of separate walks: the restoring loop produces both at once \
             and computing them separately would run the loop twice. `IR`-prefixed so the \
             vacuity firewall's prefix discovery reaches it — it is a data type with no premise \
             and nothing to be vacuous about, and a name the firewall cannot see is exactly the \
             silent-no-op mode that gate exists to rule out. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_dm_rem (x : IRDivMod) : Nat := ",
                "IRDivMod.rec (fun (_ : IRDivMod) => Nat) ",
                "(fun (r : Nat) (_ : Nat) => r) x",
            ),
            "The remainder field. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_dm_quot (x : IRDivMod) : Nat := ",
                "IRDivMod.rec (fun (_ : IRDivMod) => Nat) ",
                "(fun (_ : Nat) (q : Nat) => q) x",
            ),
            "The quotient field. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_nat_shl (m : Nat) (k : Nat) : Nat := ",
                "Nat.rec (fun (_ : Nat) => Nat -> Nat) (fun (x : Nat) => x) ",
                "(fun (_ : Nat) (ih : Nat -> Nat) => fun (x : Nat) => ih (ir_nat_dbl x)) k m",
            ),
            "m * 2^k, as k STRICT doublings of an accumulator. Linear in k where \
             `ir_nat_mul m (ir_nat_pow2 k)` is linear in 2^k: the 2045-place alignment binary64 \
             addition needs is 2045 native BigNat additions here and 2^2045 of them there. \
             \n\nThe accumulator doubles on the way IN, which is why the doubling has to be the \
             strict one — through `Nat.add x x` this definition is the cost bomb ir_nat_dbl's \
             comment measures. ir_nat_shl_mul_w runs it against the reference spelling at a shift \
             small enough for the reference to exist. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_nat_bitlen_go (m : Nat) (fuel : Nat) (p : Nat) (c : Nat) : Nat := ",
                "Nat.rec (fun (_ : Nat) => Nat -> Nat -> Nat) ",
                "(fun (_ : Nat) (c0 : Nat) => c0) ",
                "(fun (_ : Nat) (ih : Nat -> Nat -> Nat) => fun (p0 : Nat) (c0 : Nat) => ",
                "Bool.rec (fun (_ : Bool) => Nat) ",
                "(ih (ir_nat_dbl p0) (Nat.succ c0)) c0 ",
                "(ir_nat_ltb m p0)) ",
                "fuel p c",
            ),
            "Bit-length by an ASCENDING doubling scan: count how many doublings of 1 it takes to \
             pass m. Bool.rec's minor order is (false, true), so the FIRST minor is the \
             `p0 <= m` step and the second is the `m < p0` stop. Fuel-driven because the \
             recursion is not structural in m. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_nat_bitlen (m : Nat) : Nat := ir_nat_bitlen_go m 4200 (Nat.succ Nat.zero) Nat.zero",
            "The number of bits in m; zero for zero. Fuel 4200 covers every intermediate binary64 \
             arithmetic can build: the widest is an exact sum at the maximum alignment distance, \
             2098 bits, and the widest a finite product reaches is 106. EvalIR substrate for the \
             rounding tail. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_dm_step2 (inc : Nat) (w : Nat) (r : Nat) (q : Nat) : IRDivMod := ",
                "Bool.rec (fun (_ : Bool) => IRDivMod) ",
                "(IRDivMod.mk (Nat.sub r w) (Nat.add (ir_nat_dbl q) inc)) ",
                "(IRDivMod.mk r (ir_nat_dbl q)) ",
                "(ir_nat_ltb r w)",
            ),
            "ONE RESTORING STEP at width w. Bool.rec minor order is (false, true), so the FIRST \
             minor is the `r >= w` case — subtract and set the bit — and the second is the \
             `r < w` case, which only shifts. `inc` is what the set bit contributes: 1 makes this \
             division, and the multiplicand makes it multiplication. DerivedProved, zero \
             axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_dm_step (inc : Nat) (w : Nat) (st : IRDivMod) : IRDivMod := ",
                "IRDivMod.rec (fun (_ : IRDivMod) => IRDivMod) ",
                "(fun (r : Nat) (q : Nat) => ir_dm_step2 inc w r q) st",
            ),
            "The step, applied to a state. Split from ir_dm_step2 because this surface syntax has \
             single-scrutinee match only. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_dm_go (inc : Nat) (hi : Nat) (fuel : Nat) (p : Nat) ",
                "(st : IRDivMod) : IRDivMod := ",
                "Nat.rec (fun (_ : Nat) => Nat -> IRDivMod -> IRDivMod) ",
                "(fun (_ : Nat) (s0 : IRDivMod) => s0) ",
                "(fun (_ : Nat) (ih : Nat -> IRDivMod -> IRDivMod) => ",
                "fun (p0 : Nat) (s0 : IRDivMod) => ",
                "Bool.rec (fun (_ : Bool) => IRDivMod) ",
                "(ir_dm_step inc p0 (ih (ir_nat_dbl p0) s0)) s0 ",
                "(ir_nat_ltb hi p0)) ",
                "fuel p st",
            ),
            "*** THE DRIVER, AND THE ONE IDEA THAT MAKES THIS SUBSTRATE AFFORDABLE. *** It \
             ASCENDS on the way in — doubling p while p <= hi — and applies the step on the way \
             OUT, so the widths fire in DESCENDING order with no halving primitive anywhere. That \
             circularity (a restoring division needs descending powers; descending needs \
             halving; halving is a division) is what makes the naive route look impossible, and \
             the recursion's own return path resolves it. \n\nCost is O(bit length of hi / p), \
             not O(quotient): the same computation `ir_nat_div` needs 2^52 loop iterations for \
             costs 53 steps here. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_nat_divmod (m : Nat) (dv : Nat) : IRDivMod := ",
                "ir_dm_go (Nat.succ Nat.zero) m 4200 dv (IRDivMod.mk m Nat.zero)",
            ),
            "Restoring division: `(m mod dv, m / dv)`, both from ONE pass. PRECONDITION dv >= 1, \
             the same precondition ir_nat_div carries (its callers reject a zero divisor first). \
             At dv = 0 the ascent's guard never fires and the fuel is consumed; no caller reaches \
             it, because every divisor here is either a power of two or the significand of a \
             `fin_`-classified binary64 operand. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_nat_divpow2 (m : Nat) (s : Nat) : IRDivMod := ir_nat_divmod m (ir_nat_pow2 s)",
            "Division by a power of two. The rounding tail's workhorse: `m / 2^s` with its \
             remainder, which together are the truncated significand and everything that decides \
             the rounding. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_nat_mulb (a : Nat) (b : Nat) : Nat := ",
                "ir_dm_quot (ir_dm_go a b 4200 (Nat.succ Nat.zero) ",
                "(IRDivMod.mk b Nat.zero))",
            ),
            "Shift-and-add multiplication: THE SAME DRIVER with the multiplicand as the \
             increment. The state's remainder field carries b, consumed most-significant bit \
             first, and the quotient field accumulates `2q + a` on each set bit — which is a*b. \
             O(bit length of b) where ir_nat_mul is O(b): the 53x53-bit product a binary64 \
             multiply needs costs 0.042 s here and 2^53 additions there. DerivedProved, zero \
             axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_nat_min (x : Nat) (y : Nat) : Nat := Bool.rec (fun (_ : Bool) => Nat) y x (ir_nat_ltb x y)",
            "The smaller of two Nats (Bool.rec minor order is false, true). DerivedProved, zero \
             axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_nat_max (x : Nat) (y : Nat) : Nat := Bool.rec (fun (_ : Bool) => Nat) x y (ir_nat_ltb x y)",
            "The larger of two Nats. DerivedProved, zero axiom_deps.",
        )?;

        Ok(())
    }

    /// The kernel-EXECUTED differential ladder: the new operations against the
    /// reference definitions, at every argument where the reference is
    /// affordable.
    fn add_eval_ir_bits_witnesses(&mut self) -> Result<(), SpecError> {
        for (name, src, note) in super::eval_ir_bits_witnesses::BITS_WITNESSES {
            self.add_recursive_def(src, note)?;
            let _ = name;
        }
        Ok(())
    }
}
