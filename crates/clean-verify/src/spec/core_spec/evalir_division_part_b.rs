// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Restoring division agrees with repeated subtraction — part two: the loop
//! invariant, the specification, uniqueness, and the agreement theorem.**
//!
//! Split out of `candmodel_dep_pi_probe.rs` for the `files_over_1000` ratchet;
//! the rows are unchanged. This module owns `candmodel_ir_wrap_fix_sources`,
//! which prepends [`super::evalir_division_part_a`]'s rows, so the pair is one
//! vector to every caller and the pinned-refusal bookkeeping in the test is
//! unaffected.
//!
//! The headline: `ir_div_agrees_unconditional` and `ir_rem_agrees_unconditional`
//! need NO premise — every `m`, every positive divisor — provided the loop runs
//! at fuel `m+1` rather than at the magic 4200. Two scope conditions travel
//! with any quotation of them, and both are recorded in the design note: the
//! fuel change is NOT safe to land at `ir_nat_divmod`, because at `dv = 0` it
//! trades a bounded wrong answer for a hang; and the sound landing is at
//! `ir_wrap`, whose divisor is a successor by construction.

use crate::spec::Specification;

impl Specification {
    /// The division agreement, DEMONSTRATED rather than made — and it needs
    /// EVAL_IR spec, not the substitution one.
    ///
    /// First attempt put these two in `candmodel_app_inversion_sources`, which
    /// runs on `build_substitution_spec_with_stack`. Both failed with
    /// `Unknown identifier: ir_wrap` / `Unknown identifier: mod` — a MISSING
    /// CONSTANT, not a failure to fold. `ir_wrap` and the `Nat.mod` uses live
    /// in the EvalIR substrate, which that bundle does not carry, so the run
    /// answered a question nobody asked.
    #[cfg(test)]
    pub(super) fn candmodel_ir_wrap_fix_sources() -> Vec<(String, String)> {
        let mut rows = Self::evalir_division_rows_part_a();
        rows.extend(Self::evalir_view_retraction_rows());
        rows.extend(vec![
            (
                // PART (3), THE LOOP. `ir_nat_mul` recurses on its SECOND
                // argument, so `a * 0 = 0` is free (ir_nat_mul_zero_right, above)
                // and `0 * b = 0` is an induction -- the same asymmetry the whole
                // of part (2)'s arithmetic turned on. The loop's base case needs
                // this one, because the initial quotient is the zero.
                "ir_nat_mul_zero_left".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_mul_zero_left")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // STRUCTURE ETA, and no precedent in this tree required it.
                // `ir_dm_step` destructures with `IRDivMod.rec`, and the state the
                // induction hypothesis hands back is `ir_dm_go ...` -- not a
                // literal `mk` -- so the step is STUCK on it. One `IRDivMod.rec`
                // with an `Eq.refl` minor unsticks it. Proved rather than assumed
                // definitional, because whether this kernel has structure eta is
                // not something to find out by relying on it.
                "ir_dm_eta".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_dm_eta")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // The step, re-expressed on an arbitrary state. `ir_dm_step` was
                // split from `ir_dm_step2` only because the surface syntax has
                // single-scrutinee match; this puts the two back together at a
                // state the loop actually produces.
                "ir_dm_step_on_state".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_dm_step_on_state")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // The loop's guard, lifted to a parameter -- the same move
                // `ir_dm_step2_gen` makes, for the same reason: `ir_nat_ltb hi p`
                // is stuck inside the goal and the motive has to vary in it. Note
                // this is the SUCCESSOR body only; the fuel-zero case has no
                // guard, and that asymmetry is the whole subtlety of part (3).
                "ir_dm_go_gen".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_dm_go_gen")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // Refl again, and worth the row: `ir_dm_go`'s successor case is
                // a `Bool.rec` nested INSIDE a `Nat.rec` minor, so this equation
                // is doing two unfoldings at once and is the one place a
                // mis-transcription of the driver would hide.
                "ir_dm_go_is_gen".to_string(),
                "def ir_dm_go_is_gen (inc : Nat) (hi : Nat) (kp : Nat) (p : Nat) (s0 : IRDivMod) : Eq IRDivMod (ir_dm_go inc hi (Nat.succ kp) p s0) (ir_dm_go_gen inc hi kp p s0 (ir_nat_ltb hi p)) := Eq.refl IRDivMod (ir_dm_go inc hi (Nat.succ kp) p s0)"
                    .to_string(),
            ),
            (
                // *** THE LOOP INVARIANT, EQUATION HALF -- AND IT NEEDS NO FUEL
                //     PREMISE AT ALL. ***  q * p + r == hi, at EVERY fuel.
                //
                // I had priced this as conditional and it is not. `ir_dm_step_eq`
                // takes no hypothesis, and the fuel-exhaustion case returns the
                // INITIAL state, where the claim is `hi = 0 * p + hi` -- true
                // unconditionally. So the product-sum identity holds of
                // `ir_dm_go` whether or not the loop ran to completion; only the
                // BOUND can fail when the fuel runs out. The two halves separate,
                // which is why they are two inductions and not one conjunction.
                //
                // Both non-recursive arms are the SAME term (`BASE_EQ`): fuel
                // exhaustion and the guard-stop return the same state, so they
                // discharge identically.
                //
                // The recursive arm is three steps: unstick the step with
                // `ir_dm_step_on_state`, apply `ir_dm_step_eq` at `w := p`, then
                // the induction hypothesis at `ir_nat_dbl p`. That the step is
                // applied on the way OUT is what makes this easy -- the hypothesis
                // hands over a state and the step invariant consumes it.
                "ir_dm_go_eq".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_dm_go_eq")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // *** THE LOOP INVARIANT, BOUND HALF -- and THIS is where the
                //     4200 lives. ***  r < p, GIVEN that the fuel sufficed.
                //
                // `ir_dm_go`'s `Nat.rec` base returns the state UNCHANGED at fuel
                // exhaustion, which is a different exit from the guard exit, so
                // the bound is simply FALSE there unless the fuel was enough. The
                // premise `hi < ir_nat_shl p k` says exactly that: after k
                // doublings we are past hi. It threads for free, because
                // `ir_nat_shl p (succ kp)` IS `ir_nat_shl (ir_nat_dbl p) kp`
                // definitionally -- `ir_nat_shl` doubles on the way IN.
                //
                // Consequence for part (4), and it is the theorem's SCOPE and not
                // a caveat about it: `ir_nat_divmod m dv` fixes k = 4200, so what
                // is provable is agreement exactly when `m < 2^4200 * dv`. Not for
                // all `Nat`.
                "ir_dm_go_bound".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_dm_go_bound")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // PART (4). *** THE FIRST CHARACTERIZATION OF THE RESTORING
                //     DIVISION THIS TREE HAS. ***  Nothing here states
                //     `q * dv + r == m` or `r < dv` for `ir_nat_divmod`,
                //     `ir_nat_div` or `ir_nat_rem` in any form -- searched by name
                //     AND by statement shape. The seven `_w` rows in
                //     eval_ir_bits_witnesses.rs are closed-literal `Eq.refl`
                //     witnesses at 17/5, 4096/256 and three power-of-two points,
                //     and that module's own header says they stand in for the
                //     unattempted agreement theorems and are not a proof.
                //
                // This one is a direct instantiation of ir_dm_go_eq, because
                // `ir_nat_divmod m dv` IS `ir_dm_go 1 m 4200 dv (mk m 0)` after
                // delta -- and it carries NO premise, for the reason part (3)
                // records: fuel exhaustion returns the initial state, where the
                // equation is `m = 0 * dv + m`.
                "ir_nat_divmod_spec_eq".to_string(),
                "def ir_nat_divmod_spec_eq (m : Nat) (dv : Nat) : Eq Nat (Nat.add (ir_nat_mul (ir_dm_quot (ir_nat_divmod m dv)) dv) (ir_dm_rem (ir_nat_divmod m dv))) m := ir_dm_go_eq m 4200 dv"
                    .to_string(),
            ),
            (
                // The bound, and it DOES carry the premise -- this is where the
                // 4200 becomes visible at the top level. `ir_nat_divmod` is not
                // correct for all `Nat`: it is correct exactly when
                // `m < 2^4200 * dv`, and this row is where that stops being a
                // remark about the implementation and becomes a hypothesis of a
                // theorem. Anyone quoting the agreement result must quote this
                // premise with it.
                "ir_nat_divmod_spec_bound".to_string(),
                "def ir_nat_divmod_spec_bound (m : Nat) (dv : Nat) (hfuel : Eq Bool (ir_nat_ltb m (ir_nat_shl dv 4200)) Bool.true) : Eq Bool (ir_nat_ltb_walk (ir_dm_rem (ir_nat_divmod m dv)) dv) Bool.true := ir_dm_go_bound m 4200 dv hfuel"
                    .to_string(),
            ),
            (
                // COMMUTATIVITY, needed for a reason that is invisible from the
                // names: `ir_nat_rem a b` is DEFINED as
                // `Nat.sub a (ir_nat_mul b (ir_nat_div a b))` -- the divisor on the
                // LEFT of the product -- while every invariant above is stated with
                // the quotient on the left. Two steps, once mul_zero_left and
                // mul_succ_left are in hand.
                "ir_nat_mul_comm".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_mul_comm")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // `x + d < d` is FALSE. This is the arm that kills the
                // mismatched cases of uniqueness: if one quotient is zero and the
                // other is a successor, the successor side contributes a whole
                // `dv` to the sum and the remainder bound is contradicted.
                //
                // No induction of its own -- it is the cancellation equation
                // against `ir_nat_ltb_walk_zero_right`, which is why both of those
                // were worth naming separately in part (2) rather than inlining.
                "ir_nat_ltb_walk_add_self_false".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_ltb_walk_add_self_false")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // Successor injectivity, as one `Eq.cong` through `Nat.pred`:
                // `Nat.pred (Nat.succ x)` is `x` by iota, so the congruence's own
                // type IS the goal.
                "nat_succ_inj".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("nat_succ_inj")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // RIGHT cancellation, and the side is forced by the cost model
                // one more time: `Nat.add x (succ d)` reduces to
                // `succ (Nat.add x d)` for free, so the induction on `d` is two
                // lines -- the base returns its hypothesis unchanged and the step
                // is one `nat_succ_inj`. Stated on the LEFT it would need
                // `nat_add_succ_left` on both sides of every equation.
                "nat_add_right_cancel".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("nat_add_right_cancel")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // LEFT cancellation, derived from the right one through two
                // commutations rather than proved again. The two sides are needed
                // for different reasons and that is not an accident: the quotient
                // sum is `q * dv + r`, so cancelling the PRODUCT to compare
                // remainders is a left cancellation, while cancelling a `dv` that
                // `ir_nat_mul_succ_left` put on the left is also one -- and the
                // only cheap induction is on the right.
                "nat_add_left_cancel".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("nat_add_left_cancel")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // THE ONE REWRITE UNIQUENESS RUNS ON: `(succ j) * dv + r` is
                // `dv + (j * dv + r)`. It peels exactly one divisor off the front
                // of a quotient-remainder sum, which is what both the descent
                // (cancel `dv`, recurse) and the contradiction (the sum is at
                // least `dv`, so it cannot be a remainder) need. Named because it
                // appears four times in ir_nat_qr_unique_q and would otherwise be
                // four copies of a two-step chain.
                "ir_nat_mul_succ_left_assoc".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_mul_succ_left_assoc")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // Its zero twin: `0 * dv + r` is `r`. Two steps, and both of
                // them are the left-side costs the cost model predicts --
                // `ir_nat_mul_zero_left` then `nat_add_zero_left`, neither free.
                "ir_nat_mul_zero_left_add".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_mul_zero_left_add")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // `d + y < d` is false -- the commuted form, which is the one
                // that actually arises, because ir_nat_mul_succ_left puts the
                // divisor on the LEFT.
                "ir_nat_ltb_walk_add_left_self_false".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_ltb_walk_add_left_self_false")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // The contradiction, packaged once. If `r` is a whole `d` plus
                // something, it cannot be a remainder mod `d`. Both mismatched
                // arms of uniqueness are this lemma with the roles swapped, so
                // packaging it turns two eight-line absurdity chains into two
                // applications.
                "ir_nat_lt_add_left_absurd".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_lt_add_left_absurd")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // *** QUOTIENT UNIQUENESS. ***  Two quotient-remainder
                // decompositions of the same number, both with remainders below
                // the divisor, have the same quotient.
                //
                // A DOUBLE induction: `Nat.rec` on q1 with an inner `Nat.rec` on
                // q2 inside each arm, because all four combinations behave
                // differently. (0,0) is `Eq.refl`. (0,succ) and (succ,0) are the
                // contradiction above with the roles swapped -- the successor side
                // contributes a whole `dv` to a sum that is supposed to be a
                // remainder. (succ,succ) peels one `dv` off each side with
                // ir_nat_mul_succ_left_assoc, cancels it, and recurses.
                //
                // Note the induction hypothesis is used at a DIFFERENT q2 than the
                // one bound outside it, which is why the motive quantifies over
                // q2, r1 and r2 rather than fixing them.
                "ir_nat_qr_unique_q".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_qr_unique_q")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // Remainder uniqueness, which is quotient uniqueness plus one
                // cancellation -- and the cancellation is on the LEFT, because the
                // remainder sits on the right of the sum. This is what
                // nat_add_left_cancel exists for.
                "ir_nat_qr_unique_r".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_qr_unique_r")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // *** THE CHARACTERIZATION. ***  `ir_nat_divmod` does not merely
                // SATISFY the quotient-remainder specification -- it is the ONLY
                // thing that does. For any q and r with `q * dv + r == m` and
                // `r < dv`, that q IS the quotient the restoring loop computes.
                //
                // This is what makes the specification worth having: a spec
                // something else could also satisfy pins nothing.
                "ir_nat_divmod_is_the_quotient".to_string(),
                "def ir_nat_divmod_is_the_quotient (m : Nat) (dv : Nat) (q : Nat) (r : Nat) (hfuel : Eq Bool (ir_nat_ltb m (ir_nat_shl dv 4200)) Bool.true) (heq : Eq Nat (Nat.add (ir_nat_mul q dv) r) m) (hr : Eq Bool (ir_nat_ltb_walk r dv) Bool.true) : Eq Nat q (ir_dm_quot (ir_nat_divmod m dv)) := ir_nat_qr_unique_q dv q (ir_dm_quot (ir_nat_divmod m dv)) r (ir_dm_rem (ir_nat_divmod m dv)) (Eq.trans Nat (Nat.add (ir_nat_mul q dv) r) m (Nat.add (ir_nat_mul (ir_dm_quot (ir_nat_divmod m dv)) dv) (ir_dm_rem (ir_nat_divmod m dv))) heq (Eq.symm Nat (Nat.add (ir_nat_mul (ir_dm_quot (ir_nat_divmod m dv)) dv) (ir_dm_rem (ir_nat_divmod m dv))) m (ir_nat_divmod_spec_eq m dv))) hr (ir_nat_divmod_spec_bound m dv hfuel)"
                    .to_string(),
            ),
            (
                // ... and the same for the remainder. Note both carry the fuel
                // premise, because both route through ir_nat_divmod_spec_bound --
                // uniqueness needs BOTH remainders below the divisor, and the
                // loop's own is only below it when the fuel sufficed.
                "ir_nat_divmod_is_the_remainder".to_string(),
                "def ir_nat_divmod_is_the_remainder (m : Nat) (dv : Nat) (q : Nat) (r : Nat) (hfuel : Eq Bool (ir_nat_ltb m (ir_nat_shl dv 4200)) Bool.true) (heq : Eq Nat (Nat.add (ir_nat_mul q dv) r) m) (hr : Eq Bool (ir_nat_ltb_walk r dv) Bool.true) : Eq Nat r (ir_dm_rem (ir_nat_divmod m dv)) := ir_nat_qr_unique_r dv q (ir_dm_quot (ir_nat_divmod m dv)) r (ir_dm_rem (ir_nat_divmod m dv)) (Eq.trans Nat (Nat.add (ir_nat_mul q dv) r) m (Nat.add (ir_nat_mul (ir_dm_quot (ir_nat_divmod m dv)) dv) (ir_dm_rem (ir_nat_divmod m dv))) heq (Eq.symm Nat (Nat.add (ir_nat_mul (ir_dm_quot (ir_nat_divmod m dv)) dv) (ir_dm_rem (ir_nat_divmod m dv))) m (ir_nat_divmod_spec_eq m dv))) hr (ir_nat_divmod_spec_bound m dv hfuel)"
                    .to_string(),
            ),
            (
                // `1 * b == b`. Needed because the repeated-subtraction loop's
                // fuel premise is stated at `(k+1) * b` and its base case is k = 0,
                // where that has to collapse to a bare `b`.
                "ir_nat_mul_one_left".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_mul_one_left")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // THE RESIDUE OF REPEATED SUBTRACTION, as its own recursion.
                // `ir_div_go` COUNTS the subtractions and throws the residue away;
                // `ir_nat_rem a b` recovers it as `a - b * (a / b)`, which is a
                // statement about the count rather than about the loop. This
                // mirrors `ir_div_go` step for step and returns what is left, so
                // the pair satisfies an equation with no subtraction in it at all
                // -- which is what lets the same uniqueness theorem apply to both
                // divisions. It is a PROBE-LOCAL definition, not a substrate
                // change: nothing in the semantics calls it.
                "ir_div_rem_go".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_div_rem_go")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // The counting loop's guard as a parameter, same move as
                // ir_dm_go_gen. Note the two `Bool.rec`s have to be generalized
                // SEPARATELY even though they dispatch on the same scrutinee,
                // because they live in different definitions.
                "ir_div_go_gen".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_div_go_gen")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // ... and the residue loop's. The motive of the pair invariant
                // mentions both, so both must vary in the same `bl`.
                "ir_div_rem_go_gen".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_div_rem_go_gen")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // Refl bridge for the counting loop.
                "ir_div_go_is_gen".to_string(),
                "def ir_div_go_is_gen (b : Nat) (kp : Nat) (x : Nat) : Eq Nat (ir_div_go (Nat.succ kp) x b) (ir_div_go_gen b kp x (ir_nat_ltb x b)) := Eq.refl Nat (ir_div_go (Nat.succ kp) x b)"
                    .to_string(),
            ),
            (
                // Refl bridge for the residue loop. Registered for the same
                // reason as its sibling: these are the two places where a
                // mis-transcription of the driver would hide behind a definitional
                // equality that happens to hold anyway.
                "ir_div_rem_go_is_gen".to_string(),
                "def ir_div_rem_go_is_gen (b : Nat) (kp : Nat) (x : Nat) : Eq Nat (ir_div_rem_go b (Nat.succ kp) x) (ir_div_rem_go_gen b kp x (ir_nat_ltb x b)) := Eq.refl Nat (ir_div_rem_go b (Nat.succ kp) x)"
                    .to_string(),
            ),
            (
                // *** REPEATED SUBTRACTION SATISFIES THE SAME EQUATION, and it
                //     too needs NO fuel premise. ***  q * b + r == x at every fuel.
                //
                // Same shape as ir_dm_go_eq and the same reason it is
                // unconditional: fuel exhaustion returns count 0 and residue x,
                // where the claim is `x = 0 * b + x`. The guard-stop arm returns
                // the SAME pair, so the two non-recursive arms are once more the
                // identical term.
                //
                // The recursive arm consumes the branch guard exactly once, at
                // `b + (x - b) == x` -- which is ir_nat_sub_add_cancel_walk from
                // part (2), commuted. That lemma is now used by both divisions.
                "ir_div_go_pair_eq".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_div_go_pair_eq")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // *** THE RESIDUE IS BELOW THE DIVISOR, given `x < (k+1) * b`.
                //     *** This is the repeated-subtraction loop's fuel premise,
                // and it is a DIFFERENT shape from the restoring loop's
                // (`hi < ir_nat_shl p k`) because the two loops consume fuel
                // differently: one subtracts b per unit of fuel, the other doubles.
                //
                // The step is the interesting part and it needs no new machinery:
                // from `x >= b` we get `x == (x - b) + b`, and the premise
                // `x < (k+2) * b` becomes `x < (k+1)*b + b` by mul_succ_left and a
                // commutation -- so both sides carry a trailing `+ b` and
                // ir_nat_ltb_walk_add_cancel_right strips it, leaving exactly the
                // induction hypothesis's premise. The cancellation equation from
                // part (2) pays for a third time here.
                "ir_div_rem_go_bound".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_div_rem_go_bound")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // PART (4), THE AGREEMENT. `(x + y) - x == y`. The mixed one:
                // `Nat.add x y` recurses on y and `Nat.sub _ x` recurses on x, so
                // neither side is free and the induction is on x with
                // nat_add_succ_left in front of ir_nat_sub_succ_succ. The tree has
                // this lemma in schema.rs, which is NOT in the EvalIR bundle --
                // the same reason ir_nat_eqb duplicates nat_eqb and
                // ir_nat_sub_zero_left duplicates nat_sub_zero_left.
                "nat_sub_add_left".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("nat_sub_add_left")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // `ir_nat_rem a b` IS the residue the subtraction loop leaves --
                // AND THIS NEEDS NO PREMISE AT ALL, not even that b is positive.
                // It follows from the pair equation alone, which is unconditional:
                // `a - (b * (a/b))` is `(Q*b + R) - (Q*b)`, and that is R.
                //
                // ir_nat_mul_comm is consumed here and only here, for the reason
                // the name does not show: ir_nat_rem puts the DIVISOR on the left
                // of the product where every invariant above puts the quotient.
                "ir_nat_rem_is_residue".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_rem_is_residue")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // `m < m + (z+1)`. The base case is `Eq.refl` because
                // `Nat.add 0 (succ z)` is a SUCCESSOR by iota and the walk's zero
                // arm is `ir_nat_pos` -- no rewrite needed even though
                // `Nat.add 0 y = y` is famously not free here.
                "ir_nat_ltb_walk_self_lt_add_succ".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_ltb_walk_self_lt_add_succ")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // *** THE DIVISOR-POSITIVITY PREMISE, DISCHARGED. ***  Writing
                // the divisor as `Nat.succ d` rather than carrying `dv >= 1` as a
                // hypothesis turns the subtraction loop's fuel premise into a
                // THEOREM: `m < (m+1) * (d+1)` always.
                //
                // And it is nearly free, because `ir_nat_mul` recurses on its
                // second argument: `(m+1) * (d+1)` IS `(m+1) + (m+1)*d` by iota,
                // which is `m + (1 + (m+1)*d)` by nat_add_succ_left -- exactly the
                // shape of the lemma above. One cong.
                //
                // So `ir_nat_div`'s own fuel is always enough. The ONLY premise
                // left in the agreement theorem is the restoring loop's bit bound.
                "ir_div_fuel_suffices_pos".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_div_fuel_suffices_pos")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // *** THE AGREEMENT THEOREM, QUOTIENT HALF. ***
                //     ir_nat_div m (d+1) == ir_dm_quot (ir_nat_divmod m (d+1))
                //
                // Restoring division and repeated subtraction compute the same
                // quotient, for every m and every POSITIVE divisor, subject to one
                // premise and one only: `m < (d+1) * 2^4200`.
                //
                // That premise is not decoration. `ir_nat_divmod` fixes its fuel at
                // 4200 and its loop returns the state UNCHANGED when the fuel runs
                // out, so beyond that bound the two really do disagree. Quote the
                // premise with the theorem.
                "ir_nat_div_agrees".to_string(),
                "def ir_nat_div_agrees (m : Nat) (d : Nat) (hbits : Eq Bool (ir_nat_ltb m (ir_nat_shl (Nat.succ d) 4200)) Bool.true) : Eq Nat (ir_nat_div m (Nat.succ d)) (ir_dm_quot (ir_nat_divmod m (Nat.succ d))) := ir_nat_divmod_is_the_quotient m (Nat.succ d) (ir_nat_div m (Nat.succ d)) (ir_div_rem_go (Nat.succ d) m m) hbits (ir_div_go_pair_eq (Nat.succ d) m m) (ir_div_rem_go_bound (Nat.succ d) m m (ir_div_fuel_suffices_pos m d))"
                    .to_string(),
            ),
            (
                // *** THE AGREEMENT THEOREM, REMAINDER HALF. ***  Two steps:
                // ir_nat_rem is the subtraction loop's residue (unconditional), and
                // that residue is the restoring loop's remainder (by uniqueness,
                // under the same bit bound).
                //
                // What this replaces: eval_ir_bits_witnesses.rs held
                // ir_nat_divmod_q_w and ir_nat_divmod_r_w -- `Eq.refl` at 17/5 --
                // and its header said they stood in for exactly this theorem.
                "ir_nat_rem_agrees".to_string(),
                "def ir_nat_rem_agrees (m : Nat) (d : Nat) (hbits : Eq Bool (ir_nat_ltb m (ir_nat_shl (Nat.succ d) 4200)) Bool.true) : Eq Nat (ir_nat_rem m (Nat.succ d)) (ir_dm_rem (ir_nat_divmod m (Nat.succ d))) := Eq.trans Nat (ir_nat_rem m (Nat.succ d)) (ir_div_rem_go (Nat.succ d) m m) (ir_dm_rem (ir_nat_divmod m (Nat.succ d))) (ir_nat_rem_is_residue m (Nat.succ d)) (ir_nat_divmod_is_the_remainder m (Nat.succ d) (ir_nat_div m (Nat.succ d)) (ir_div_rem_go (Nat.succ d) m m) hbits (ir_div_go_pair_eq (Nat.succ d) m m) (ir_div_rem_go_bound (Nat.succ d) m m (ir_div_fuel_suffices_pos m d)))"
                    .to_string(),
            ),
            (
                // THE VACUITY FIX, PART ONE: the characterization at a GENERAL
                // fuel. ir_dm_go_eq and ir_dm_go_bound were already general in k;
                // only ir_nat_divmod_is_the_quotient was pinned at 4200, and that
                // pinning is what made the agreement theorem unwitnessable --
                // `ir_nat_shl dv 4200` cannot be evaluated, because `ir_nat_dbl`
                // forces its argument, so no concrete instance discharges the
                // premise by `Eq.refl`.
                //
                // Nothing is weakened: the 4200 versions are this at k = 4200.
                "ir_dm_go_is_the_quotient".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_dm_go_is_the_quotient")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // ... and the remainder half, same generalization.
                "ir_dm_go_is_the_remainder".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_dm_go_is_the_remainder")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // THE AGREEMENT THEOREM AT A GENERAL FUEL. This is the primary
                // statement and `ir_nat_div_agrees` is its k = 4200 instance --
                // which is the honest ordering, because the 4200 is a property of
                // `ir_nat_divmod`'s definition and not of the mathematics.
                "ir_div_agrees_at_fuel".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_div_agrees_at_fuel")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // ... and the remainder half.
                "ir_rem_agrees_at_fuel".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_rem_agrees_at_fuel")
                    .expect("fixed historical division source")
                    .to_string(),
            ),
            (
                // *** THE NON-VACUITY WITNESS. ***  17 / 5 at fuel 8, where
                // `ir_nat_shl 5 8` is 1280 and the premise really does compute --
                // 1275 iota steps of doubling, then one native comparison. The
                // hypothesis is discharged by `Eq.refl`, so the theorem above is
                // not a statement about an empty premise.
                //
                // This is what the earlier commit could not do and said so. A
                // theorem whose hypothesis nothing satisfies proves nothing, and
                // this tree has a firewall for exactly that failure.
                "ir_div_agrees_witness".to_string(),
                "def ir_div_agrees_witness : Eq Nat (ir_nat_div 17 5) (ir_dm_quot (ir_dm_go (Nat.succ Nat.zero) 17 8 5 (IRDivMod.mk 17 Nat.zero))) := ir_div_agrees_at_fuel 17 4 8 (Eq.refl Bool Bool.true)"
                    .to_string(),
            ),
            (
                // ... and for the remainder.
                "ir_rem_agrees_witness".to_string(),
                "def ir_rem_agrees_witness : Eq Nat (ir_nat_rem 17 5) (ir_dm_rem (ir_dm_go (Nat.succ Nat.zero) 17 8 5 (IRDivMod.mk 17 Nat.zero))) := ir_rem_agrees_at_fuel 17 4 8 (Eq.refl Bool Bool.true)"
                    .to_string(),
            ),
            (
                // AND THE WITNESS IS NOT TWO STUCK TERMS. A theorem equating two
                // expressions neither of which reduces is satisfied by `Eq.refl`
                // and measures nothing, so the value is asserted separately:
                // 17 / 5 is 3, computed through the restoring loop.
                //
                // Same discipline as the standing rule that a green
                // "it compiled and ran" never checks what the program PRINTED.
                "ir_div_agrees_witness_is_not_stuck".to_string(),
                "def ir_div_agrees_witness_is_not_stuck : Eq Nat (ir_dm_quot (ir_dm_go (Nat.succ Nat.zero) 17 8 5 (IRDivMod.mk 17 Nat.zero))) 3 := Eq.refl Nat 3"
                    .to_string(),
            ),
            (
                // ... and the remainder is 2. Together these two rows say the
                // agreement is between two real computations, not between two
                // symbols.
                "ir_rem_agrees_witness_is_not_stuck".to_string(),
                "def ir_rem_agrees_witness_is_not_stuck : Eq Nat (ir_dm_rem (ir_dm_go (Nat.succ Nat.zero) 17 8 5 (IRDivMod.mk 17 Nat.zero))) 2 := Eq.refl Nat 2"
                    .to_string(),
            ),
            (
                // REMOVING THE BIT BOUND. `succ x < b` gives `x < b`. No
                // induction -- a `Nat.rec` CASE SPLIT on b: at 0 the hypothesis is
                // contradictory (ir_nat_ltb_walk_zero_right), and at `succ bp` the
                // hypothesis IS `ltb_walk x bp = true` by iota, so the substrate's
                // own `ir_nat_ltb_succ_walk` closes it.
                "ir_nat_ltb_walk_pred_left".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_ltb_walk_pred_left")
                    .expect("fixed historical unconditional division source")
                    .to_string(),
            ),
            (
                // `a + c < b` gives `a < b`. Induction on c through the lemma
                // above, free at every step because `Nat.add a (succ cp)` reduces
                // to `succ (Nat.add a cp)`.
                //
                // This is the piece the naive attempt was missing. `2^k > k` does
                // not prove by plain induction -- at `succ kp` the hypothesis gives
                // `kp <` where `succ kp <` is wanted -- so the statement has to be
                // STRENGTHENED to carry slack, and something must then throw the
                // slack away. This throws it away.
                "ir_nat_ltb_walk_drop_add_left".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_ltb_walk_drop_add_left")
                    .expect("fixed historical unconditional division source")
                    .to_string(),
            ),
            (
                // *** `k + p < 2^k * (p+1)` -- THE STRENGTHENED FORM, and the
                //     strengthening is the whole content. ***
                //
                // The statement one wants is `k < 2^k * (p+1)`, and it does NOT
                // prove: the doubling has to be USED, and a bare index on the left
                // gives the induction nothing to consume it with. Carrying `k + p`
                // instead works because `ir_nat_shl` doubles its ACCUMULATOR on the
                // way in -- `shl q (succ k)` IS `shl (dbl q) k` -- so the step
                // applies the induction hypothesis at `p' = p + (p+1)`, and the
                // extra `p` that appears on the left is exactly the slack
                // ir_nat_ltb_walk_drop_add_left then discards.
                //
                // The rearrangement is two steps, assoc then nat_add_succ_left, and
                // the target side is free because `Nat.add` recurses on its second
                // argument -- the cost model again.
                "ir_nat_shl_index_lt".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_nat_shl_index_lt")
                    .expect("fixed historical unconditional division source")
                    .to_string(),
            ),
            (
                // *** `m < 2^(m+1) * (d+1)`, FOR EVERY m AND d. ***  The
                // restoring loop's fuel premise, discharged outright at fuel
                // `Nat.succ m` -- no bound on m, no bound on the divisor beyond
                // positivity, which is already spelled into `Nat.succ d`.
                //
                // One transport: `m + (d+1)` and `(m+1) + d` are the same number,
                // and only one of the two spellings is free.
                "ir_dm_fuel_always_suffices".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_dm_fuel_always_suffices")
                    .expect("fixed historical unconditional division source")
                    .to_string(),
            ),
            (
                // *** THE AGREEMENT, WITH NO PREMISE AT ALL. ***
                //     ir_nat_div m (d+1) == ir_dm_quot (ir_dm_go 1 m (m+1) (d+1) ..)
                //
                // Restoring division and repeated subtraction agree for EVERY m and
                // every positive divisor, full stop -- provided the loop is run at
                // fuel `m+1` rather than at the magic 4200.
                //
                // And `m+1` costs nothing at run time: ir_dm_go stops at its GUARD,
                // not at its fuel -- its successor arm returns `s0` without
                // touching `ih` when `hi < p0` -- so the fuel is a recursion DEPTH
                // BOUND that the loop never reaches. This is the argument for
                // changing ir_nat_divmod's 4200 to `Nat.succ m`: it makes the
                // function total-correct rather than bit-bounded, and it makes the
                // ir_wrap swap meaning-preserving instead of a semantic change.
                "ir_div_agrees_unconditional".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_div_agrees_unconditional")
                    .expect("fixed historical unconditional division source")
                    .to_string(),
            ),
            (
                // ... and the remainder, likewise with no premise. Together these
                // two are what the 2026-09-20 note called the fix worth having, and
                // the lemma it said had not been attempted is ir_nat_shl_index_lt
                // above.
                "ir_rem_agrees_unconditional".to_string(),
                super::super::eval_ir_positive_division_v1::source_for_probe("ir_rem_agrees_unconditional")
                    .expect("fixed historical unconditional division source")
                    .to_string(),
            ),
            (
                // *** THE FREE-VARIABLE FAIL-OPEN, MEASURED RATHER THAN CITED. ***
                //
                // `ir_undeclared_probe_zzz` is declared NOWHERE in this tree. It
                // appears here only in the TYPE (a binder's domain) and never in
                // the value. If this row PASSES, an undeclared identifier in a
                // type position was silently auto-bound as a free variable, and
                // the declaration is true of an arbitrary thing rather than of
                // what it names.
                //
                // That is not hypothetical. `ir_lzd_max_running_at_9` and `_at_10`
                // shipped naming `ir_d64`, which the EvalIr bundle does not
                // declare, and both PASSED — so both were true of an arbitrary
                // counter rather than of 64, a weaker statement than the one
                // written, reached silently. They were switched to `ir_d63`;
                // docs/CRYSTAL_STATUS.md names the general hole and says it "is
                // not this chain's to close".
                //
                // THIS ROW IS EXPECTED TO PASS, and its passing is the DEFECT.
                // The day it starts failing, the fail-open has been closed and
                // CRYSTAL_STATUS should be updated — the test asserts that
                // explicitly rather than leaving it to be noticed.
                "free_var_fail_open_type_position".to_string(),
                "def free_var_fail_open_type_position (h : Eq Nat ir_undeclared_probe_zzz ir_undeclared_probe_zzz) : Eq Nat Nat.zero Nat.zero := Eq.refl Nat Nat.zero"
                    .to_string(),
            ),
            (
                // THE OTHER HALF OF THE ASYMMETRY, and the control that makes
                // the row above mean something. The SAME undeclared spelling, in
                // VALUE position, is a hard `Unknown identifier`.
                //
                // Without this control the row above is unreadable: a name that
                // resolves to nothing anywhere would make both rows fail and the
                // pair would measure that the name is absent, not that type
                // position treats it differently from value position. Together
                // they measure the asymmetry itself, which is the actual defect.
                //
                // PINNED REFUSAL: expected to fail.
                "free_var_hard_error_value_position".to_string(),
                "def free_var_hard_error_value_position (n : Nat) : Nat := ir_undeclared_probe_zzz n"
                    .to_string(),
            ),
            (
                // DISCRIMINATOR 1 — is it ONE variable or a FRESH one per
                // occurrence? The same undeclared spelling is required to be a
                // `Nat` in one binder and a `Bool` in the next. One bound
                // variable cannot be both, so:
                //   FAILS  => the name is bound ONCE, and the fail-open is a
                //             binder with an inferred type
                //   PASSES => each occurrence mints a FRESH unknown, which is
                //             strictly worse: two occurrences of one spelling in
                //             one statement need not denote the same thing
                // Classified after the run, not before.
                "free_var_same_name_two_types".to_string(),
                "def free_var_same_name_two_types (h : Eq Nat ir_undeclared_probe_zzz Nat.zero) (k : Eq Bool ir_undeclared_probe_zzz Bool.true) : Eq Nat Nat.zero Nat.zero := Eq.refl Nat Nat.zero"
                    .to_string(),
            ),
            (
                // DISCRIMINATOR 2 — is the binder's domain actually elaborated,
                // or merely skipped because nothing uses it? Here the binder IS
                // used in the value and the undeclared name appears in the
                // declaration's RESULT type as well, so neither can be ignored.
                // Classified after the run.
                "free_var_binder_used_in_value".to_string(),
                "def free_var_binder_used_in_value (h : Eq Nat ir_undeclared_probe_zzz ir_undeclared_probe_zzz) : Eq Nat ir_undeclared_probe_zzz ir_undeclared_probe_zzz := h"
                    .to_string(),
            ),
            (
                // THE CAPSTONE OF THE DIVISION THREAD, in three rows.
                //
                // `2^k - 1`, written as its OWN recursion rather than as
                // `Nat.pred (ir_nat_pow2 k)`. That spelling matters and is the
                // only reason the next row is two congruences instead of a
                // four-step transport: `ir_nat_pow2 (succ j)` is
                // `Nat.add (pow2 j) (pow2 j)`, whose `Nat.pred` is STUCK at a
                // symbolic `j`, so a `pred`-based statement has to rewrite under
                // a `pred` and then rewrite back. Recursing separately makes both
                // sides compute, and the successor case lands on the definition
                // by iota.
                "ir_pow2_pred".to_string(),
                "def ir_pow2_pred (k : Nat) : Nat := Nat.rec (fun (_ : Nat) => Nat) Nat.zero (fun (_ : Nat) (ih : Nat) => Nat.add (Nat.succ ih) ih) k"
                    .to_string(),
            ),
            (
                // *** `ir_nat_pow2 w` IS A SUCCESSOR, for every w. *** This is
                // the lemma the 2026-09-20 note named as unwritten and as the one
                // thing standing between the unconditional agreement and the
                // `ir_wrap` statement below.
                //
                // Two congruences on the SAME induction hypothesis, one at each
                // occurrence of `pow2 j` in `add (pow2 j) (pow2 j)`. The base is
                // `Eq.refl`: `ir_nat_pow2 Nat.zero` is literally `Nat.succ
                // Nat.zero` and `ir_pow2_pred Nat.zero` is `Nat.zero`.
                "ir_nat_pow2_is_succ".to_string(),
                "def ir_nat_pow2_is_succ (w : Nat) : Eq Nat (ir_nat_pow2 w) (Nat.succ (ir_pow2_pred w)) := Nat.rec (fun (k : Nat) => Eq Nat (ir_nat_pow2 k) (Nat.succ (ir_pow2_pred k))) (Eq.refl Nat (Nat.succ Nat.zero)) (fun (j : Nat) (ih : Eq Nat (ir_nat_pow2 j) (Nat.succ (ir_pow2_pred j))) => Eq.trans Nat (Nat.add (ir_nat_pow2 j) (ir_nat_pow2 j)) (Nat.add (ir_nat_pow2 j) (Nat.succ (ir_pow2_pred j))) (Nat.succ (Nat.add (Nat.succ (ir_pow2_pred j)) (ir_pow2_pred j))) (Eq.cong Nat Nat (fun (z : Nat) => Nat.add (ir_nat_pow2 j) z) (ir_nat_pow2 j) (Nat.succ (ir_pow2_pred j)) ih) (Eq.cong Nat Nat (fun (z : Nat) => Nat.succ (Nat.add z (ir_pow2_pred j))) (ir_nat_pow2 j) (Nat.succ (ir_pow2_pred j)) ih)) w"
                    .to_string(),
            ),
            (
                // *** `ir_wrap w n` IS THE RESTORING LOOP'S RESIDUE, WITH NO
                //     PREMISE AT ALL. ***
                //
                //   ir_wrap w n == ir_dm_rem (ir_dm_go 1 n (n+1) (2^w) (n, 0))
                //
                // Every w, every n. This is the theorem that justifies the
                // substrate change the whole division thread was for, and it needs
                // nothing about the size of n: positivity of the divisor comes
                // from `ir_nat_pow2 w` being a successor by construction, and the
                // fuel `n+1` is always enough by `ir_dm_fuel_always_suffices`.
                //
                // TWO THINGS IT DOES NOT LICENSE, both measured earlier and both
                // recorded in the design note. It is NOT an argument for changing
                // `ir_nat_divmod`'s own fuel from 4200 to `Nat.succ m`: at dv = 0
                // that trades a bounded wrong answer for a ~9e15-iteration hang,
                // and the fuel is the only thing bounding that precondition
                // violation. And landing it at `ir_wrap` still has a blast radius
                // OUTSIDE this bundle -- `ir_byte_wrap_canonical_v1` and
                // `ir_byte_wrap_once_v1` are theorems ABOUT `ir_wrap` in a stage
                // this probe never registers, so this test could not catch them
                // breaking. The mathematics is finished; the edit is a separate,
                // measured act against a stage that does not build here.
                "ir_wrap_is_the_restoring_residue".to_string(),
                "def ir_wrap_is_the_restoring_residue (w : Nat) (n : Nat) : Eq Nat (ir_wrap w n) (ir_dm_rem (ir_dm_go (Nat.succ Nat.zero) n (Nat.succ n) (ir_nat_pow2 w) (IRDivMod.mk n Nat.zero))) := Eq.trans Nat (ir_nat_rem n (ir_nat_pow2 w)) (ir_nat_rem n (Nat.succ (ir_pow2_pred w))) (ir_dm_rem (ir_dm_go (Nat.succ Nat.zero) n (Nat.succ n) (ir_nat_pow2 w) (IRDivMod.mk n Nat.zero))) (Eq.cong Nat Nat (fun (z : Nat) => ir_nat_rem n z) (ir_nat_pow2 w) (Nat.succ (ir_pow2_pred w)) (ir_nat_pow2_is_succ w)) (Eq.trans Nat (ir_nat_rem n (Nat.succ (ir_pow2_pred w))) (ir_dm_rem (ir_dm_go (Nat.succ Nat.zero) n (Nat.succ n) (Nat.succ (ir_pow2_pred w)) (IRDivMod.mk n Nat.zero))) (ir_dm_rem (ir_dm_go (Nat.succ Nat.zero) n (Nat.succ n) (ir_nat_pow2 w) (IRDivMod.mk n Nat.zero))) (ir_rem_agrees_unconditional n (ir_pow2_pred w)) (Eq.cong Nat Nat (fun (z : Nat) => ir_dm_rem (ir_dm_go (Nat.succ Nat.zero) n (Nat.succ n) z (IRDivMod.mk n Nat.zero))) (Nat.succ (ir_pow2_pred w)) (ir_nat_pow2 w) (Eq.symm Nat (ir_nat_pow2 w) (Nat.succ (ir_pow2_pred w)) (ir_nat_pow2_is_succ w))))"
                    .to_string(),
            ),
        ]);
        rows
    }
}
