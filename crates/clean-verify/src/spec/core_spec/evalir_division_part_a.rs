// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Restoring division agrees with repeated subtraction — part one: the
//! arithmetic, the comparison layer, and the per-step invariant.**
//!
//! Split out of `candmodel_dep_pi_probe.rs` because that file crossed 1,000
//! lines and `data/paragon_ratchet.json`'s `files_over_1000` is shrink-only.
//! The rows are unchanged; only their address moved. Part two is
//! [`super::evalir_division_part_b`], and the two are ONE vector at the call
//! site — `candmodel_ir_wrap_fix_sources` there prepends these.
//!
//! The governing fact, which priced every lemma here before it was written:
//! **`Nat.add`, `Nat.sub` and `ir_nat_mul` all recurse on their SECOND
//! argument.** Anything stated along the recursive argument is free; every use
//! of the left argument costs a rewrite. Read
//! [`designs/2026-09-20-restoring-division-agrees-with-repeated-subtraction.md`]
//! for what each part cost against what the plan guessed.

use crate::spec::Specification;

impl Specification {
    /// Part one's rows. See the module doc; `candmodel_ir_wrap_fix_sources`
    /// in part two prepends these to its own.
    #[cfg(test)]
    pub(super) fn evalir_division_rows_part_a() -> Vec<(String, String)> {
        vec![
            (
                // THE CORRECT FIX, and it is already in the tree.
                //
                // My first proposal — redefine through the kernel-native
                // `Nat.mod` — is REFUTED on soundness grounds by this spec's
                // own mechanised policy. `eval_ir_bits_witnesses.rs`'s
                // `test_no_accelerated_constant_is_added` BANS `Nat.div`,
                // `Nat.mod`, `Nat.mul`, `Nat.pow`, `Nat.beq`, `Nat.ble` and
                // `Nat.blt`, because a native reducer means "the kernel never
                // consults the declared body — speed bought with trust". That
                // is exactly what `ir_wrap` must not become, and it is why
                // `Nat.mod` does not resolve in this spec at all: the refusal
                // is deliberate and mechanised, not an oversight.
                //
                // The right machinery sits beside that policy:
                // `ir_nat_divmod m dv := ir_dm_go 1 m 4200 dv ..` is RESTORING
                // division with BIT-bounded fuel (4200), so it is O(bits) where
                // `ir_div_go` is O(value); `ir_nat_divpow2 m s` is exactly a
                // residue by a power of two; and `ir_nat_shl_divpow2_w` already
                // round-trips a 2098-BIT value through it, kernel-executed,
                // with zero accelerated constants.
                //
                // So the fix is `ir_wrap w n := ir_dm_rem (ir_nat_divpow2 n w)`,
                // and THIS ROW TESTS THAT EQUATION AT THE VALUE THAT DEFEATS
                // THE CURRENT PATH. If it folds, the fix is demonstrated
                // without touching the substrate, without a native constant,
                // and without violating the policy that refused my first idea.
                "divpow2_residue_folds_at_u64_max".to_string(),
                "def divpow2_residue_folds_at_u64_max : \
                 Eq Nat (ir_dm_rem (ir_nat_divpow2 18446744073709551615 32)) 4294967295 := \
                 Eq.refl Nat 4294967295"
                    .to_string(),
            ),
            (
                // THE CONTROL, and it is deliberately SMALL.
                //
                // The obvious control — `ir_wrap 32 18446744073709551615` — would
                // not FAIL, it would run ~4.29e9 reduction steps and take the test
                // with it. A probe that hangs measures nothing and costs a slot, so
                // the control runs `ir_wrap` at a value it can actually reach:
                // `ir_wrap 8 300` needs 300/256 = 1 iteration.
                //
                // Together the two rows say the thing that matters: `ir_wrap` is
                // CORRECT and cheap at small values, and `Nat.mod` is cheap at
                // 1.8e19 where `ir_wrap` cannot go. The difference is SCALE, not
                // correctness — which is why the fix is a change of computing side
                // and not a change of meaning.
                "ir_wrap_folds_at_a_small_value".to_string(),
                "def ir_wrap_folds_at_a_small_value : Eq Nat (ir_wrap 8 300) 44 := \
             Eq.refl Nat 44"
                    .to_string(),
            ),
            (
                // PART (1) OF THE OWED PROOF, first piece: the two BRANCH
                // EQUATIONS for `ir_dm_step2`.
                //
                // Any step invariant for restoring division starts here — you
                // cannot reason about what a step preserves until you can say
                // what it computes under each guard. `ir_dm_step2` is a
                // `Bool.rec` on `ir_nat_ltb r w` whose minor order is
                // (false, true), so the FIRST minor is the SUBTRACTING branch
                // and the second is the pass-through. Getting that order
                // backwards would invert the whole algorithm, which is why
                // these are stated separately rather than assumed.
                //
                // Same idiom `ir_div_go`'s own unfolding equation uses: one
                // congruence over the guard, so the branch selection is
                // AUDITABLE rather than trusted.
                "ir_dm_step2_when_lt".to_string(),
                "def ir_dm_step2_when_lt (inc : Nat) (w : Nat) (r : Nat) (q : Nat) \
                 (h : Eq Bool (ir_nat_ltb r w) Bool.true) : \
                 Eq IRDivMod (ir_dm_step2 inc w r q) (IRDivMod.mk r (ir_nat_dbl q)) := \
                 Eq.cong Bool IRDivMod (fun (g : Bool) => Bool.rec (fun (_qb : Bool) => IRDivMod) (IRDivMod.mk (Nat.sub r w) (Nat.add (ir_nat_dbl q) inc)) (IRDivMod.mk r (ir_nat_dbl q)) g) (ir_nat_ltb r w) Bool.true h"
                    .to_string(),
            ),
            (
                // The other branch: the guard is FALSE, so `w` fits and the
                // step SUBTRACTS and sets q := 2q + inc. This is the arm that
                // does the work, and the pair of them is what a restoring
                // invariant is stated over.
                "ir_dm_step2_when_ge".to_string(),
                "def ir_dm_step2_when_ge (inc : Nat) (w : Nat) (r : Nat) (q : Nat) \
                 (h : Eq Bool (ir_nat_ltb r w) Bool.false) : \
                 Eq IRDivMod (ir_dm_step2 inc w r q) (IRDivMod.mk (Nat.sub r w) (Nat.add (ir_nat_dbl q) inc)) := \
                 Eq.cong Bool IRDivMod (fun (g : Bool) => Bool.rec (fun (_qb : Bool) => IRDivMod) (IRDivMod.mk (Nat.sub r w) (Nat.add (ir_nat_dbl q) inc)) (IRDivMod.mk r (ir_nat_dbl q)) g) (ir_nat_ltb r w) Bool.false h"
                    .to_string(),
            ),
            (
                // PART (1), arithmetic rung: `ir_nat_mul`'s DEFINING equations.
                //
                // `ir_nat_mul a b := Nat.rec .. Nat.zero (fun _ ih => Nat.add a ih) b`
                // recurses on its SECOND argument, so these two are
                // definitional — `Eq.refl` — and they are worth stating anyway
                // because everything in the step invariant is rewriting with
                // them, and because which argument the recursion is on decides
                // which side needs an induction. Left-successor
                // (`ir_nat_mul (succ a) b`) is NOT definitional and needs a
                // `Nat.rec` on `b`; right-successor is free. Getting that
                // backwards would misplan the whole invariant.
                "ir_nat_mul_zero_right".to_string(),
                "def ir_nat_mul_zero_right (a : Nat) : \
                 Eq Nat (ir_nat_mul a Nat.zero) Nat.zero := \
                 Eq.refl Nat Nat.zero"
                    .to_string(),
            ),
            (
                // The successor equation on the RECURSIVE argument, free for
                // the same reason.
                "ir_nat_mul_succ_right".to_string(),
                "def ir_nat_mul_succ_right (a : Nat) (b : Nat) : \
                 Eq Nat (ir_nat_mul a (Nat.succ b)) (Nat.add a (ir_nat_mul a b)) := \
                 Eq.refl Nat (Nat.add a (ir_nat_mul a b))"
                    .to_string(),
            ),
            (
                // PINNED REFUSAL — the arithmetic is NOT reachable here, and
                // that is the finding.
                //
                // MEASURED 2026-09-20: this row FAILS with
                // `Unknown identifier: add_assoc`. `Nat.add_assoc` is a KERNEL
                // constant and the spec uses it freely elsewhere (4 sites,
                // alongside `Nat.add_comm` x5 and `Nat.mul_comm` x3) — but
                // those live in `eval_ir_byte_*_laws.rs`, registered through
                // `eval_ir_byte.rs`, which `new_eval_ir_spec` does not include.
                // So the EvalIR TEST spec carries no Nat algebra.
                //
                // Consequence for the planned proof: part (1)'s step invariant
                // cannot borrow `Nat.add_assoc` / `add_comm` in this spec. It
                // must either be built where the byte laws are built, or prove
                // its handful of `Nat.add` facts locally from `Nat.rec`.
                //
                // Pinned rather than deleted because it is exactly the kind of
                // fact that should fail LOUDLY if the bundle composition
                // changes — a later session finding this green has learned
                // something, not lost a test.
                // `ir_nat_mul` and `ir_nat_dbl` are both built on `Nat.add`,
                // so the kernel's `Nat.add_assoc` / `Nat.add_comm` /
                // `Nat.add_succ` algebra applies to them directly — the step
                // invariant does NOT need a parallel algebra for the EvalIR
                // multiplication.
                //
                // Checked here rather than assumed, because `Nat.mul` itself is
                // on `test_no_accelerated_constant_is_added`'s BANNED list and
                // it would be easy to conclude the kernel's whole Nat algebra
                // is off-limits. It is not: the ban is on ACCELERATED
                // COMPUTATION, not on lemmas about `Nat.add`.
                "nat_add_algebra_is_reachable".to_string(),
                "def nat_add_algebra_is_reachable (a : Nat) (b : Nat) (c : Nat) : \
                 Eq Nat (Nat.add (Nat.add a b) c) (Nat.add a (Nat.add b c)) := \
                 Nat.add_assoc a b c"
                    .to_string(),
            ),
            (
                // Which ARGUMENT does `Nat.add` recurse on? If the SECOND, `add a 0` is
                // definitional and `add 0 a` is not; if the FIRST, the reverse. The
                // planned invariant rewrites in both directions, so knowing which
                // side is free decides how much local algebra part (1) must build.
                // Measured rather than read out of the kernel.
                "nat_add_zero_right_is_refl".to_string(),
                "def nat_add_zero_right_is_refl (a : Nat) : \
                 Eq Nat (Nat.add a Nat.zero) a := \
                 Eq.refl Nat a"
                    .to_string(),
            ),
            (
                // The mirror. Exactly one of these two should be free.
                "nat_add_zero_left_is_refl".to_string(),
                "def nat_add_zero_left_is_refl (a : Nat) : \
                 Eq Nat (Nat.add Nat.zero a) a := \
                 Eq.refl Nat a"
                    .to_string(),
            ),
            (
                // The successor equation on the SECOND argument.
                "nat_add_succ_right_is_refl".to_string(),
                "def nat_add_succ_right_is_refl (a : Nat) (b : Nat) : \
                 Eq Nat (Nat.add a (Nat.succ b)) (Nat.succ (Nat.add a b)) := \
                 Eq.refl Nat (Nat.succ (Nat.add a b))"
                    .to_string(),
            ),
            (
                // And on the FIRST. The invariant's subtracting branch needs THIS one, so if
                // it is not free it is the first thing part (1) must prove.
                "nat_add_succ_left_is_refl".to_string(),
                "def nat_add_succ_left_is_refl (a : Nat) (b : Nat) : \
                 Eq Nat (Nat.add (Nat.succ a) b) (Nat.succ (Nat.add a b)) := \
                 Eq.refl Nat (Nat.succ (Nat.add a b))"
                    .to_string(),
            ),
            (
                // PART (1), BOOTSTRAP LEMMA 1: `Nat.add Nat.zero a = a`.
                //
                // Not definitional — `Nat.add` recurses on its SECOND argument,
                // measured by the pinned `nat_add_zero_left_is_refl` above. So
                // it wants a `Nat.rec` on `a`, and each case is then free:
                //   a = 0      : `add 0 0` IS `0` (right-zero is definitional);
                //   a = succ k : `add 0 (succ k)` IS `succ (add 0 k)`
                //                (right-succ is definitional), so the goal is
                //                `succ (add 0 k) = succ k` and the IH lifts
                //                under `succ` by one congruence.
                "nat_add_zero_left".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("nat_add_zero_left")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // PART (1), BOOTSTRAP LEMMA 2: the LEFT-successor equation.
                //
                // `Nat.add (Nat.succ a) b = Nat.succ (Nat.add a b)`, by
                // `Nat.rec` on `b` — the argument the recursion is on, so both
                // cases reduce:
                //   b = 0      : both sides ARE `succ a`;
                //   b = succ k : LHS is `succ (add (succ a) k)` and RHS is
                //                `succ (succ (add a k))`, so the IH lifts under
                //                `succ`.
                //
                // THIS is the lemma the invariant's subtracting branch needs —
                // `(2q + inc) * w = 2q * w + w` is a left-successor shape — and
                // it is why the recursion direction had to be measured before
                // planning.
                "nat_add_succ_left".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("nat_add_succ_left")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // PART (1), STEP 3a: ASSOCIATIVITY of `Nat.add`.
                //
                // `Nat.rec` on `c` — the argument the recursion is on, so both
                // cases reduce without needing the bootstrap lemmas at all:
                //   c = 0      : both sides ARE `Nat.add a b`;
                //   c = succ k : LHS is `succ (add (add a b) k)` and RHS is
                //                `succ (add a (add b k))`, since `add x (succ y)`
                //                is definitionally `succ (add x y)` on BOTH
                //                sides. So the IH lifts under one congruence.
                //
                // Worth noting it needed neither `nat_add_zero_left` nor
                // `nat_add_succ_left`: associativity is free on the recursive
                // argument, and only COMMUTATIVITY pays for the left side.
                "nat_add_assoc_local".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("nat_add_assoc_local")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // PART (1), STEP 3b: COMMUTATIVITY, and this is where both
                // bootstrap lemmas are spent.
                //
                // `Nat.rec` on `b`:
                //   b = 0      : `add a 0` IS `a` (free), and `add 0 a = a` is
                //                `nat_add_zero_left` — so the base case is that
                //                lemma, symmetrised;
                //   b = succ k : LHS is `succ (add a k)` (free), which the IH
                //                sends to `succ (add k a)`; RHS is
                //                `add (succ k) a`, which `nat_add_succ_left`
                //                sends to `succ (add k a)`. The two meet, so
                //                the step is a `trans` of the lifted IH against
                //                that lemma's symm.
                //
                // This is the shape the measurement predicted: the left side is
                // never free, and every use of it costs one of the two lemmas.
                "nat_add_comm_local".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("nat_add_comm_local")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // PART (1), STEP 4 — the last arithmetic rung, and the one the
                // invariant actually calls for.
                //
                // `ir_nat_mul (Nat.succ a) b = Nat.add b (ir_nat_mul a b)`.
                // LEFT-successor, so it is not definitional: `ir_nat_mul`
                // recurses on its SECOND argument, which is why this needs a
                // `Nat.rec` on `b` and why the three lemmas above exist.
                //
                // The step case is where they are all spent. After the IH turns
                // `ir_nat_mul (succ a) k` into `add k X` (X = ir_nat_mul a k),
                // both sides reduce to a re-association:
                //
                //   add (succ a) (add k X)  ==  add (succ k) (add a X)
                //
                // and the route is succ_left, then
                // (symm assoc; cong comm; assoc) under one `succ`, then
                // succ_left backwards. Associativity moves the brackets,
                // commutativity swaps `a` and `k` inside them, and the two
                // succ_left uses take the `succ` out of the left argument at
                // each end — which is exactly the side the measurement showed
                // is never free.
                "ir_nat_mul_succ_left".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_mul_succ_left")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // PART (2), and it is a lemma I should have named the FIRST
                // time: the swap of the outer two summands.
                //
                //   add a (add b c) = add b (add a c)
                //
                // This exact chain — symm assoc, cong comm, assoc — was inlined
                // inside `ir_nat_mul_succ_left`, and distributivity needs it
                // again. Naming it once makes both proofs one step instead of
                // five, and makes the shape visible: it is the only way to move
                // a term past another when `Nat.add` is only free on its right.
                "nat_add_swap_first_two".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("nat_add_swap_first_two")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // PART (2): RIGHT-distributivity of `ir_nat_mul` over `Nat.add`.
                //
                // `Nat.rec` on `c`, the argument BOTH operations recurse on, so
                // every reduction is free and the only real step is the swap
                // above. The invariant needs this to turn `q * (2w)` into
                // `q*w + q*w` on the way to `(2q) * w`.
                "ir_nat_mul_add_right".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_mul_add_right")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // PART (2): `ir_nat_dbl n = Nat.add n n` — the bridge from the
                // doubling primitive to the algebra just built.
                //
                // `ir_nat_dbl` is NOT recursive: its succ arm is
                // `fun p _ih => Nat.succ (Nat.add p (Nat.succ p))`, discarding
                // the induction hypothesis. So this is a CASE ANALYSIS wearing
                // a `Nat.rec`, and the `_ih` below is genuinely unused rather
                // than accidentally so.
                //
                // Each case then nearly reduces:
                //   n = 0      : `dbl 0` IS `0` and `add 0 0` IS `0`;
                //   n = succ p : `dbl (succ p)` IS `succ (succ (add p p))`
                //                (the inner `add p (succ p)` is free on its
                //                right), while `add (succ p) (succ p)` is only
                //                `succ (add (succ p) p)` — the outer step is
                //                free, the INNER one is a left-successor and
                //                costs `nat_add_succ_left`.
                //
                // One lemma, in the one place the left argument appears. That
                // is the recursion-direction result showing up for the fifth
                // time in this file.
                "ir_nat_dbl_is_add".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_dbl_is_add")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // PART (2): the FOUR-TERM REARRANGEMENT that left-distributivity
                // needs. `(a+b) + (x+y) = (a+x) + (b+y)`.
                //
                // Five steps, and they are the only five available: assoc to
                // open the left bracket, symm-assoc to re-bracket the inside,
                // comm to swap `b` past `x`, assoc to re-close, symm-assoc to
                // rebuild the right shape. There is no shortcut because
                // `Nat.add` is free only on its right, so every term that has
                // to move leftward costs a rewrite.
                "nat_add_exchange".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("nat_add_exchange")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // PART (2): LEFT-distributivity, and its step case is
                // `nat_add_exchange` with nothing left over.
                //
                // After the IH, the goal is literally
                // `(a+b) + (X+Y)  ==  (a+X) + (b+Y)` with X = mul a k and
                // Y = mul b k. Naming the exchange separately turned this proof
                // into two steps; inlined, it would have been six.
                "ir_nat_mul_add_left".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_mul_add_left")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // PART (2): `q * (2w) = (2q) * w` — THE EQUATION THE STEP
                // INVARIANT TURNS ON.
                //
                // Both sides go to `q*w + q*w` and meet there: the left via
                // `dbl_is_add` then RIGHT-distributivity, the right via
                // `dbl_is_add` then LEFT-distributivity. That is why both
                // distributivities were needed — the doubling sits on a
                // different side of the product in each half of the invariant.
                //
                // With this, the pass-through branch closes: `q' = dbl q` and
                // `q' * w = q * (2w)`, so `m = q*(2w) + r` becomes
                // `m = q'*w + r'` with `r' = r`.
                "ir_nat_mul_dbl_shift".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_mul_dbl_shift")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // PART (2), THE COMPARISON LAYER. Four lemmas that turn the
                // step's two branch guards into arithmetic. All four are stated
                // over `ir_nat_ltb_walk` -- the PAIRED UNARY WALK -- and not over
                // `ir_nat_ltb`, which is what the machine runs: the walk is the
                // shape an induction can peel, and `ir_nat_ltb_walk_eq` (already
                // in the substrate) carries any result back. Reasoning directly
                // on `ir_nat_ltb` would have to fight its two-operand peel and
                // the `ir_nat_sub_ltb` core underneath it.
                //
                // `x < 0` is FALSE for every x. Both cases are `Eq.refl`: the
                // walk's zero arm is `ir_nat_pos y` and its successor arm cases
                // on y, and at y = 0 both compute to `Bool.false`.
                "ir_nat_ltb_walk_zero_right".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_ltb_walk_zero_right")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // A COMMON RIGHT ADDEND CANCELS IN A COMPARISON, as an
                // EQUATION rather than an implication -- which is what makes the
                // bound half cheap, and is the cost model paying off once more.
                // `k` is the argument BOTH `Nat.add`s recurse on, so the base is
                // `add d 0 = d` by iota and the successor case is the walk's own
                // succ/succ arm: `ltb_walk (succ X) (succ Y)` IS `ltb_walk X Y`.
                // Both cases free; the induction hypothesis is returned unchanged.
                //
                // I first tried the bound half as a direct paired induction on w
                // against `r < 2w`, and it does NOT close: at `w = succ wp` the
                // hypothesis one gets is `rp <= 2wp` where the induction
                // hypothesis wants `rp < 2wp`, and the conclusion needed is
                // `rp - wp <= wp` where it gives `< wp`. Off by one on both ends.
                // Decomposing `r` as `d + w` first and cancelling is what works.
                "ir_nat_ltb_walk_add_cancel_right".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_ltb_walk_add_cancel_right")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // THE DECOMPOSITION: `r >= w` gives back `(r - w) + w = r`.
                // This is what makes the subtracting branch a statement about
                // ADDITION, so the arithmetic above applies to it at all.
                //
                // Stated in the `(r - w) + w` orientation and NOT `w + (r - w)`,
                // and the cost model says why: `Nat.add` and `Nat.sub` both
                // recurse on their second argument, so with `w` on the right the
                // base case is `Eq.refl` and the successor case's outer
                // `Nat.add X (succ wp)` peels for free. The commuted spelling
                // costs `nat_add_zero_left` in the base and one extra rewrite in
                // the step -- three real steps instead of two.
                //
                // `Nat.rec` on w generalizing r, then an inner `Nat.rec` on r.
                // The r = 0 arm is the absurd one: `ltb_walk 0 (succ wp)` IS
                // `Bool.true`, so the hypothesis is contradictory and
                // `ir_bool_false_ne_true` takes it to the goal. One `Eq.symm`
                // stands in the way because that eliminator is stated
                // false = true and the walk hands this arm true = false.
                "ir_nat_sub_add_cancel_walk".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_sub_add_cancel_walk")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // THE BOUND HALF OF THE STEP INVARIANT: `r < 2w` and `r >= w`
                // give `r - w < w`. Three rewrites and no induction of its own --
                // decompose `r` as `(r - w) + w`, then cancel the common `w`
                // against the `w + w` on the right. `ir_nat_dbl_is_add` is what
                // connects this to the step's actual guard, which is stated at
                // `ir_nat_dbl w`.
                "ir_nat_sub_bound_walk".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_sub_bound_walk")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // PART (2), THE STEP INVARIANT. The step's case analysis is a
                // `Bool.rec` on `ir_nat_ltb r w`, and that scrutinee sits STUCK
                // inside the goal -- so to case on it at all, the motive has to
                // vary in it. This is `ir_dm_step2`'s own body with the boolean
                // lifted to a PARAMETER; the bridge below is `Eq.refl`, and the
                // two theorems after it are stated about the REAL `ir_dm_step2`,
                // reaching the generalization through delta.
                "ir_dm_step2_gen".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_dm_step2_gen")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // The bridge, and it is refl: `ir_dm_step2 inc w r q` IS
                // `ir_dm_step2_gen inc w r q (ir_nat_ltb r w)` after one delta
                // step. Registered rather than assumed, because a generalization
                // that is NOT the original body is the way this technique goes
                // wrong silently.
                "ir_dm_step2_is_gen".to_string(),
                "def ir_dm_step2_is_gen (inc : Nat) (w : Nat) (r : Nat) (q : Nat) : Eq IRDivMod (ir_dm_step2 inc w r q) (ir_dm_step2_gen inc w r q (ir_nat_ltb r w)) := Eq.refl IRDivMod (ir_dm_step2 inc w r q)"
                    .to_string(),
            ),
            (
                // *** THE STEP INVARIANT, EQUATION HALF ***
                //     q' * w + r'  ==  q * (2w) + r
                // for (r', q') = ir_dm_step2 1 w r q, in BOTH branches, with no
                // hypothesis about r at all beyond the branch's own guard.
                //
                // PASS-THROUGH (r < w): q' = 2q and r' = r, so the whole claim is
                // `(2q)*w = q*(2w)` -- ir_nat_mul_dbl_shift, backwards. One step,
                // and the guard is unused.
                //
                // SUBTRACTING (r >= w): q' = `Nat.add (2q) 1`, which REDUCES to
                // `Nat.succ (2q)` because `Nat.add` recurses on its second
                // argument -- so ir_nat_mul_succ_left applies with no rewrite in
                // front of it. Five steps: succ_left, assoc, swap, then
                // `w + (r - w) = r` from the guard, then dbl_shift. The fourth is
                // where the branch guard is actually consumed, and it is the only
                // place in either half that needs the comparison layer above.
                "ir_dm_step_eq".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_dm_step_eq")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // *** THE STEP INVARIANT, BOUND HALF ***  r' < w, given r < 2w.
                // Pass-through takes it from its own guard; subtracting takes it
                // from ir_nat_sub_bound_walk. Stated over `ir_nat_ltb_walk` in
                // BOTH the hypothesis and the conclusion, which is what lets the
                // loop induction compose this with itself: the descent hands each
                // step the previous step's bound, so the two must be the same
                // shape, and the walk is the shape the arithmetic is proved at.
                "ir_dm_step_bound".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_dm_step_bound")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
        ]
    }
}
