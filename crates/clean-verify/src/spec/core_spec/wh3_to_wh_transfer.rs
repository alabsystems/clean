// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Three-way to two-way TRANSFER — completeness at the deployed-faithful loop.
//!
//! Items 2 through 8 of
//! `designs/2026-09-18-completeness-at-the-deployed-faithful-loop.md`, built
//! arm by arm rather than as one nine-arm `KExpr.rec`. The route in one line:
//! the STEP transfers (items 2 and 3), so the LOOP transfers (4), so the
//! ALGORITHM transfers (5 and 6), so the WITNESS transfers (7) — and the
//! three-way completeness capstone becomes a two-way one (8), with its
//! budget unchanged.
//!
//! Derive the constant list from the table at the bottom of this file, never
//! from a count in prose.
//!
//! # Why arm by arm
//!
//! The assembled induction is a single term of a few hundred lines, and a
//! kernel rejection of it names a type mismatch somewhere inside, not the arm
//! that caused it. Each arm that does real work is therefore its own named
//! lemma, separately elaborable, so a failure says WHICH arm. The five trivial
//! arms (`sort`, `bvar`, `lam`, `pi`, `lit`) need no lemma — the three-way step
//! is `wstuck` there and the two-way step is `none`, so the obligation is
//! `Eq.refl`.
//!
//! # What the transfer says, and the one thing that makes it work
//!
//! `whnf_fuel_red_wh3` returns `some r` ONLY when its step reported genuine
//! stuckness; exhaustion returns `none` instead of a term. So the three-way
//! loop succeeds on a STRICT SUBSET of the two-way loop's cases and agrees
//! where both succeed — the refinement is entirely on the FAILURE side. Two
//! directions carry that:
//!
//! * `wstuck` at the three-way step ⟹ `none` at the two-way step;
//! * `wstep e2` at the three-way step ⟹ `some e2` at the two-way step.
//!
//! `wstarved` needs neither: it is the one case where the two loops genuinely
//! diverge (the two-way step announces the term as its own normal form), and it
//! is excluded because the three-way loop returns `none` there, falsifying the
//! antecedent of everything above.
//!
//! **WIRED**, from `add_defeq_fuel` after `add_wh3_norm_acc_witness`
//! (`defeq_fuel.rs`). Not after `add_slot_dispatch_at`, which is one stage
//! earlier and was the first attempt: that stage mints
//! `def_eq_fuel_complete_wh3_final`, but the WITNESS for it —
//! `def_eq_fuel_complete_wh3_final_witness`, which item 8's own non-vacuity
//! witness consumes — is minted by the stage after it, so the spec build
//! aborted with `Unknown identifier` on exactly that name.
//!
//! Every constant was scratch-elaborated BEFORE being wired, per the recipe and
//! per the cycle item 1 cost by ignoring it: once the stage is in the bundle,
//! one bad constant panics the cached spec build and every test in the crate
//! dies with no mention of which constant broke. To iterate here again, unwire
//! first — the scratch test's own wired-state guard will otherwise early-return
//! and tell you nothing.
//!
//! # A cost claim this module used to carry, RETRACTED 2026-09-17
//!
//! It said a nine-arm `KExpr.rec` leaving both the scrutinee and a convoy
//! operand variable was pathological, and cited "more than seven minutes in the
//! elaborator without finishing" for the `app` arm written that way.
//!
//! **That was not a measurement.** Two runs were killed at about seven minutes
//! believing they were stuck on that arm. They were not: in this test process a
//! full `Specification::new()` takes about **1100 seconds**, and neither run had
//! reached a single arm of this module when it was killed. The relative cost of
//! the two proof shapes is **UNMEASURED**.
//!
//! What IS measured, from the run that completed (2026-09-17, every one of the
//! seventeen constants registered AT THAT RUN reporting `ok` — the module has
//! grown since, so read the table, not that number): every constant here
//! elaborates in
//! **under a second**, ~5 s for the whole list against ~1098 s of spec build.
//! The per-constant timings print live under `--nocapture`, which is how this
//! was caught — and is why they print before the attempt rather than after.
//!
//! The literal-transport structure below is KEPT, because it is green and
//! proves exactly the statements the direct shape would. But it was adopted on
//! a misreading, and nothing here should be read as evidence against the direct
//! shape until the two are measured side by side.
//!
//! # Two lemmas the repair left without a consumer
//!
//! `wh3_ilift_stuck_gives_none` and `wh3_ilift_step_gives_some` are the general
//! ilift convoys — head result an arbitrary `WhStepR`. The `app` arm used to go
//! through them; after the repair it does not, because transporting the head
//! result to a literal FIRST is exactly what makes the convoy disappear.
//!
//! They are kept, and this paragraph is why rather than an oversight. Both are
//! true, both are `DerivedProved` with empty axiom closures, and both state the
//! general fact that the literal-indexed lemmas state only at three points. But
//! **nothing in this module consumes either of them today**, and that should be
//! said out loud rather than left for a reader to discover: an unconsumed lemma
//! is registered weight, and if a later increment does not pick them up they
//! should go rather than accumulate.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// Which shape the non-`lam` arms of one `app_head_some_at` case take.
///
/// The three cases differ ONLY here, which is the fact worth keeping: a head
/// that is stuck goes to the ι chain, a starved one is absurd outside `lam`,
/// and one that stepped takes the congruence.
#[derive(Clone, Copy)]
enum AppHeadSomeArm {
    Chain,
    Absurd,
    Congruence,
}

impl Specification {
    /// Every arm source this module currently carries, IN DEPENDENCY ORDER.
    ///
    /// The scratch test registers these sequentially against a built spec, so a lemma
    /// must precede its consumers or the run reports `Unknown identifier` rather than
    /// anything about the term. The ilift convoy consumes the chain lemma; listing it
    /// first cost a cycle.
    pub(super) fn wh3_to_wh_arm_sources() -> Vec<(String, String)> {
        vec![
            (
                Self::wh3_to_wh_chain_src(),
            "wh3_chain_stuck_gives_none: THE CONTENT OF THE app ARM -- if the three-way iota chain \
             is stuck, the two-way chain declines. One application of iota_reduct_whc3_stuck_inv \
             (the Prop variant, the goal being an Eq) whose six continuations map ONE-TO-ONE onto \
             decline lemmas: k1/k2/k3 onto the three that already existed, k5/k6/ktail onto the \
             three landed as item 1. \
             \
             THERE IS NO k4, and that absence is why the transfer works at all: level 4 is the \
             pre-pass, which cannot produce a wstuck -- a starved pre-pass yields wstarved, which \
             wh_stuck_ne_starved separates. Starvation cannot leak in. \
             \
             The continuation hypothesis is spent in exactly three places, transporting the \
             pre-pass result; every other fact the decline lemmas need mentions no pre-pass at \
             all, which is why the bottom three levels needed no new work. DerivedProved, zero \
             axiom_deps."
                .to_string(),
            ),
            (
                Self::wh3_to_wh_const_arm_src(),
            "wh3_const_stuck_gives_none: the const arm of the three-way-to-two-way step transfer. \
             The three-way step at a constant binds the stored value with wstuck as its failure \
             default; the two-way step IS that lookup. So wstuck forces the none branch, the some \
             branch reporting wstep v, and wh_stuck_ne_step_type refutes it. Smallest arm that \
             does real work, and the one that exercises the option convoy plus the WhStepR \
             no-confusion lemma every other non-trivial arm needs. DerivedProved, zero \
             axiom_deps."
                .to_string(),
            ),
            (
                Self::wh3_to_wh_proj_arm_src(),
            "wh3_proj_stuck_gives_none: the proj arm of the step transfer -- the one arm outside \
             the application spine where the three-way step does extra work, carrying STARVATION \
             UP from its subterm rather than losing it. Takes the induction hypothesis as a \
             hypothesis so the arm is checkable without the nine-arm recursor around it. Three-way \
             convoy on the subterm's result: wstuck uses the IH and opt_proj_lift reduces at none; \
             wstarved and wstep are refuted by WhStepR no-confusion. DerivedProved, zero \
             axiom_deps."
                .to_string(),
            ),
            (
                Self::wh3_to_wh_ilift_src(),
            "wh3_ilift_stuck_gives_none: the ilift convoy, one layer above the chain lemma and one \
             below the app arm. Head stuck reaches for iota on both sides and hands off to the \
             chain lemma; head STARVED is the arm where the naive 'the divergence is confined to \
             the chain' reading is wrong -- the two-way opt_app_ilift sees only none and DOES \
             attempt iota there -- and it is harmless only because wstarved is not wstuck, so the \
             branch is refuted rather than transferred; head reduced takes the congruence and is \
             refuted the same way. DerivedProved, zero axiom_deps."
                .to_string(),
            ),
            (
                Self::wh3_to_wh_head_stuck_src(),
                "wh3_app_head_stuck_gives_head_stuck: the head's own stuckness, and nothing else \
                 -- the transport that makes the app arm CHEAP. The tree's precedent says to do \
                 it this way: wh3_stuck_app_forces_iota_stuck's description in \
                 budget_induction_prereqs.rs is explicit that splitting the Eq.subst out of the \
                 nine-arm recursion keeps eight of those nine arms literally the identity. This \
                 is that split, stated parametrically in renv and the pre-pass rather than at a \
                 fixed budget. Its motive carries ONE small equation. DerivedProved, zero \
                 axiom_deps."
                    .to_string(),
            ),
            (
                Self::wh3_to_wh_app_head_lit_src(),
                "wh3_app_head_stuck_gives_none_at_lit: the app arm AT THE LITERALS, where eight \
                 arms collapse to one chain application each and the ilift convoy disappears \
                 entirely. With c3 known to be wstuck and c2 known to be none, both app-head \
                 reducers iota-reduce at every non-lam head to their respective iota chains, \
                 because opt_app_ilift3's wstuck arm and opt_app_ilift_wh's none arm ARE those \
                 chains. So each arm is one wh3_chain_stuck_gives_none with no WhStepR.rec \
                 between them. wh3_ilift_stuck_gives_none remains the GENERAL statement -- the \
                 success direction needs it, its head result not being transportable to a literal \
                 -- but this direction does not have to pay for it. DerivedProved, zero \
                 axiom_deps."
                    .to_string(),
            ),
            (
                Self::wh3_to_wh_app_head_via_lit_src(),
                "wh3_app_head_stuck_gives_none: the app arm as the assembly consumes it -- the \
                 two transports around the literal form. SAME STATEMENT as the direct nine-arm \
                 version it replaces, so the assembly does not change; only the cost does. \
                 wh3_app_head_stuck_gives_head_stuck gives c3 = wstuck, the induction hypothesis \
                 turns that into c2 = none, and two Eq.substTypes move the hypothesis and the \
                 goal to those literals where the cheap recursor applies. DerivedProved, zero \
                 axiom_deps."
                    .to_string(),
            ),
            (
                Self::wh3_to_wh_step_src(),
                "wh_step3_stuck_to_none: ITEM 2 ASSEMBLED -- one three-way step reporting GENUINE \
                 stuckness forces the two-way step to decline. Nine arms, of which FIVE are \
                 Eq.refl (sort, bvar, lam, pi, lit: both steps decline outright, and the \
                 hypothesis is never looked at), let_ is absurd and inlined (the three-way step \
                 contracts, so wh_stuck_ne_step refutes on the spot), and const/proj/app delegate \
                 to the three arm lemmas. \
                 \
                 That five of nine arms are free is the measure of how narrow the three-way \
                 refinement is: it is entirely on the FAILURE side, which is why SUCCESS \
                 transfers with the witnessed budget UNCHANGED and monotonicity is touched \
                 nowhere. Each delegating arm passes the recursor's motive-at-the-subterm \
                 straight through as the lemma's ih, which is the payoff of stating every arm \
                 with its induction hypothesis as a HYPOTHESIS rather than closing over the \
                 recursion -- each was checkable before this constant existed. DerivedProved, \
                 zero axiom_deps."
                    .to_string(),
            ),
            (
                Self::wh3_to_wh_chain_some_src(),
                "wh3_chain_step_gives_some: ITEM 3 BEGINS -- the SUCCESS direction of the iota \
                 chain. Markedly smaller than its stuck mirror: iota_reduct_whc3_some_inv has ONE \
                 continuation where the stuck inverter has six, because a fired iota has one \
                 shape and a declined one has six ways to decline. The continuation's six binders \
                 and seven facts land one-for-one on iota_reduct_whc_some_of_facts, with the \
                 pre-pass fact -- and only that one -- routed through hw. \
                 \
                 The guarded tail transfers UNTOUCHED: iota_contractum_at mentions no whnf \
                 continuation at all, so the fact the three-way inverter hands out is literally \
                 the fact the two-way reassembler wants. The two loops differ only where a \
                 pre-pass is consulted, and the tail never consults one. DerivedProved, zero \
                 axiom_deps."
                    .to_string(),
            ),
            (
                Self::wh3_to_wh_const_some_src(),
                "wh3_const_step_gives_some: the const arm of the SUCCESS direction. Mirror of the stuck \
                 arm with the branches swapped -- none is refuted and some carries the work. What \
                 it needs beyond its twin is wh_step_inj: the three-way step wraps the stored \
                 value in wstep, and recovering the payload is where a some-direction transfer \
                 always spends a no-confusion lemma its none-direction twin does not. \
                 DerivedProved, zero axiom_deps."
                    .to_string(),
            ),
            (
                Self::wh3_to_wh_proj_some_src(),
                "wh3_proj_step_gives_some: the proj arm of the SUCCESS direction, and it needs only ONE \
                 of the two induction hypotheses. A proj can only report a step when its subterm \
                 did, so wstuck and wstarved are both refuted outright and the stuck-direction \
                 hypothesis is never consulted -- unlike the ilift and app arms, where a stuck \
                 HEAD is exactly when the two-way iota is attempted. DerivedProved, zero \
                 axiom_deps."
                    .to_string(),
            ),
            (
                Self::wh3_to_wh_ilift_some_src(),
                "wh3_ilift_step_gives_some: the ilift convoy, SUCCESS direction -- and it needs BOTH \
                 hypotheses, which is where item 3 genuinely consumes item 2 rather than \
                 mirroring it. A head reporting wstuck is exactly the case in which both loops \
                 reach for iota, so computing the two-way ilift at all requires the two-way head \
                 result, and a wstuck three-way head says nothing about it except through the \
                 stuck-direction transfer. Head starved is refuted, so STARVATION IS EXCLUDED ON \
                 THIS SIDE TOO, for the same reason as in the stuck direction. DerivedProved, \
                 zero axiom_deps."
                    .to_string(),
            ),
            (
                Self::wh3_to_wh_app_head_some_at_stuck_src(),
                "wh3_app_head_step_gives_some_at_stuck: the SUCCESS direction's app arm at a \
                 wstuck head result. One of three cheap recursors replacing the shape the module \
                 doc measures as pathological. With the head result at the literal wstuck and the \
                 two-way one at none, both app-head reducers iota-reduce at every non-lam head to \
                 their iota chains, so eight arms are one wh3_chain_step_gives_some each; lam \
                 computes by beta on both sides. DerivedProved, zero axiom_deps."
                    .to_string(),
            ),
            (
                Self::wh3_to_wh_app_head_some_at_starved_src(),
                "wh3_app_head_step_gives_some_at_starved: the SUCCESS direction's app arm at a \
                 wstarved head result. Eight arms are REFUTED -- opt_app_ilift3 propagates \
                 wstarved, which is not a wstep -- and only lam survives, beta ignoring the head \
                 result entirely. That asymmetry is why this case needs no knowledge of the \
                 two-way head result at all: where the three-way side is not absurd, the two-way \
                 side does not consult c2 either. DerivedProved, zero axiom_deps."
                    .to_string(),
            ),
            (
                Self::wh3_to_wh_app_head_some_at_step_src(),
                "wh3_app_head_step_gives_some_at_step: the SUCCESS direction's app arm at a wstep \
                 head result. All nine arms compute and all nine are the same two lines -- the \
                 three-way side rebuilds the application (lam contracts instead), the two-way \
                 side does the matching thing, and wh_step_inj identifies the payload. No arm \
                 consults the iota chain, because a head that stepped never reaches iota on \
                 either side. DerivedProved, zero axiom_deps."
                    .to_string(),
            ),
            (
                Self::wh3_to_wh_app_head_some_via_cases_src(),
                "wh3_app_head_step_gives_some: the SUCCESS direction's app arm assembled -- \
                 convoy on the head result FIRST, then one of the three cheap recursors. SAME \
                 STATEMENT as the direct nine-arm version it replaces; only the cost changes. The \
                 convoy is what buys it: inside each of its arms the head result is a LITERAL, so \
                 the recursor that runs there has both app-head reducers iota-reducing all the \
                 way down. wstuck spends ihs (item 2's direction), wstep spends ihp, and wstarved \
                 spends NEITHER -- the same asymmetry the proj arm shows one level down. \
                 DerivedProved, zero axiom_deps."
                    .to_string(),
            ),
            (
                Self::wh3_to_wh_step_some_src(),
                "wh_step3_step_to_some: ITEM 3 ASSEMBLED -- a three-way step that actually \
                 reduces forces the two-way step to reduce to the SAME term. The nine-arm shape \
                 of item 2 with the arms' fortunes reversed: the five free shapes there (sort, \
                 bvar, lam, pi, lit) are refuted here because the three-way step reports wstuck \
                 at all of them, and let_, absurd there, is the computing arm here. \
                 \
                 The app arm is where item 3 CONSUMES item 2: it must supply the head's \
                 stuck-direction transfer as well as its own induction hypothesis, and the \
                 recursor cannot hand it both -- the motive carries one implication. It comes \
                 from wh_step3_stuck_to_none applied at the head, a closed lemma needing no \
                 induction, which is why the two items are sequenced rather than proved as one \
                 mutual induction. DerivedProved, zero axiom_deps."
                    .to_string(),
            ),
            (
                Self::wh3_to_wh_loop_src(),
                "whnf_fuel_red_wh3_to_wh: ITEM 4 -- the LOOP transfer. Nat.rec on the fuel, and \
                 the succ arm's induction hypothesis IS the hw that items 2 and 3 take as a \
                 parameter, the same type binder for binder. Nothing else in the development \
                 supplies it, which is why every arm lemma carries it rather than closing over a \
                 fixed pre-pass; both loops pass THEMSELVES at k as their pre-pass, so at succ k \
                 the hypothesis is available exactly where the step transfer needs it. \
                 \
                 The convoy carries its own EQUATION as well as the dispatch, because the two \
                 working arms need to know WHICH step result they are in and not just what the \
                 dispatch computed. The wstarved arm is where the loops genuinely differ and \
                 there is nothing to transfer: the three-way loop reports honest exhaustion, so \
                 the hypothesis is none = some and option_none_ne_some closes it. That is the \
                 arm the two-way loop cannot express, and it is why the transfer is \
                 one-directional. \
                 \
                 THE FUEL IS NEVER RAISED: the target at succ k has both legs at k and the \
                 induction hypothesis is used at k only, which is why this route touches \
                 monotonicity nowhere. DerivedProved, zero axiom_deps."
                    .to_string(),
            ),
            (
                Self::wh3_to_wh_of_struct_src(),
                "def_eq_fuel_wh_of_struct: ITEM 5 -- the introduction rule at the \
                 deployed-faithful algorithm, DERIVED from its three-way twin by \
                 whole-identifier substitution rather than by transcribing the proof. Both \
                 algorithms have the same shape one substitution apart, so the proof transports \
                 verbatim; the generator asserts every pattern is present and that no three-way \
                 identifier survives, which is what makes that a checked claim rather than a \
                 hope. DerivedProved, zero axiom_deps."
                    .to_string(),
            ),
            (
                Self::wh3_to_wh_defeq_src(),
                "def_eq_fuel_wh3_to_wh: ITEM 6 -- the ALGORITHM transfer, and EASIER than its \
                 three-way twin for the reason the design doc gives: the target lands at succ j \
                 with both legs at j, so nothing is raised and def_eq_fuel_succ_mono is never \
                 reached. Two option convoys and three appeals -- each whnf leg by item 4 at the \
                 SAME fuel, the structural layer by def_eq_struct_mono, which needs no port \
                 because def_eq_struct is parametric in its comparator and the induction \
                 hypothesis IS the pointwise implication it wants, and the fold back up by item \
                 5. The none arms are refuted rather than handled: a leg that fails to reduce \
                 makes the algorithm false, so the hypothesis is false = true. DerivedProved, \
                 zero axiom_deps."
                    .to_string(),
            ),
            (
                Self::wh3_to_wh_accepts_src(),
                "def_eq_accepts_wh3_to_wh: ITEM 7 -- the witness transfer, one arm. The two \
                 Accepts types are the same single-constructor witness idiom over the two \
                 algorithms, so unwrapping one and rewrapping the other around item 6 is the \
                 whole proof -- and THE BUDGET IS CARRIED ACROSS UNCHANGED, which is the property \
                 this whole route exists to preserve. DerivedProved, zero axiom_deps."
                    .to_string(),
            ),
            (
                Self::wh3_to_wh_complete_src(),
                "def_eq_fuel_complete_wh: ITEM 8 -- COMPLETENESS OF THE DEPLOYED-FAITHFUL \
                 CONVERSION ALGORITHM. With def_eq_fuel_wh_sound_final this gives loop (ii) BOTH \
                 directions; today that pair exists only for loop (iii), an analysis artifact no \
                 fidelity gate connects to the shipping is_def_eq. \
                 \
                 TWO CAVEATS TRAVEL WITH IT AND NEITHER IS OPTIONAL. (1) The premise is \
                 Wh3NormAcc, a normalisation-accessibility predicate about the ANALYSIS loop, \
                 carried onto a theorem about the DEPLOYED-FAITHFUL one; it is satisfiable and \
                 hereditary but it is not a statement about whnf_fuel_red_wh's own \
                 normalisation. (2) THE FUEL GUARANTEE IS CONDITIONAL ON HOW THE \
                 BUDGET WAS OBTAINED, which is narrower than 'the fuel is not monotone' and is \
                 the accurate form. whnf_fuel_red_wh_monotone_is_false stands at this loop, so a \
                 budget reached by an arbitrary route may fail at a larger one -- but the budget \
                 THIS theorem witnesses comes through the three-way capstone, and \
                 def_eq_fuel_wh_accepts_at_every_larger shows such a budget is UPWARD CLOSED: \
                 every m with Le k m works too. Two-way monotonicity itself remains OPEN and is \
                 not what that constant proves. DerivedProved, zero axiom_deps."
                    .to_string(),
            ),
            (
                Self::wh3_to_wh_complete_witness_src(),
                "def_eq_fuel_complete_wh_witness: *** THE COMPLETENESS THEOREM IS NOT VACUOUS. *** \
                 def_eq_fuel_complete_wh is a conditional on Wh3NormAcc, and the soundness \
                 certificate is explicit that a vacuous conditional passes every axiom-closure \
                 gate -- the hazard fired once already, on loop (i)'s def_eq_fuel_complete, whose \
                 hnf premise turned out false. The type alone cannot tell complete from empty, so \
                 the three-way capstone carries a witness and the two-way one must carry its \
                 counterpart. \
                 \
                 It is ONE application of item 7 to def_eq_fuel_complete_wh3_final_witness, which \
                 is the point: the transfer moves the WITNESS as readily as the theorem, so \
                 non-vacuity costs nothing extra and there is no excuse for omitting it. \
                 DerivedProved, zero axiom_deps."
                    .to_string(),
            ),
            (
                Self::wh3_to_wh_accepts_sound_src(),
                "def_eq_fuel_wh_accepts_sound: the SOUNDNESS direction at the witness level, \
                 factored out of the pair so the roundtrip witness can be expressed. The \
                 two-way counterpart of def_eq_fuel_wh3_accepts_sound: unwrap the witness, apply \
                 def_eq_fuel_wh_sound_final at the budget it carries. UNCONDITIONAL -- no \
                 Wh3NormAcc, no fuel side condition. DerivedProved, zero axiom_deps."
                    .to_string(),
            ),
            (
                Self::wh3_to_wh_pair_src(),
                "def_eq_wh_sound_and_complete: THE PAIR AT LOOP (ii), AS ONE OBJECT. \
                 def_eq_wh3_sound_and_complete does this for loop (iii); until now there was no \
                 counterpart at loop (ii) because there was no completeness half to pair. \
                 Registering the conjunction rather than leaving two theorems side by side is \
                 what makes 'loop (ii) has both directions' greppable instead of a sentence \
                 someone has to assemble. \
                 \
                 THE HALVES ARE NOT SYMMETRIC IN WHAT THEY COST. Completeness carries Wh3NormAcc \
                 on both terms -- a predicate about the ANALYSIS loop -- and its fuel guarantee \
                 is conditional on how the budget was obtained (see \
                 def_eq_fuel_wh_accepts_at_every_larger). Soundness is def_eq_fuel_wh_sound_final \
                 and carries NOTHING: \
                 unconditional, at any fuel. The accessibility premises on this statement are \
                 there for the completeness direction ALONE, and a reader who wants soundness \
                 should take it directly rather than through this pair. \
                 \
                 SCOPE, which must travel with any statement of it: loop (ii) is \
                 deployed-faithful by a CODE CITATION (the major-premise whnf pre-pass that \
                 try_iota_reduction performs) and by the empirical differential in \
                 fidelity_gate.rs over a six-constructor subset -- not by a theorem. This is a \
                 pair for a MODELLED algorithm, not a proof about the shipping is_def_eq. \
                 DerivedProved, zero axiom_deps."
                    .to_string(),
            ),
            (
                Self::wh3_to_wh_upward_closed_src(),
                "def_eq_fuel_wh_accepts_at_every_larger: THE NON-MONOTONICITY CAVEAT MADE \
                 PRECISE. From a THREE-way acceptance at k, the TWO-way algorithm accepts at \
                 EVERY m with Le k m -- two lines, def_eq_fuel_wh3_le to raise the budget on the \
                 monotone side then the algorithm transfer at the raised budget. \
                 \
                 It does NOT prove two-way monotonicity, which stays open, and the distinction is \
                 the whole point: acceptance at each m is derived FRESHLY at m through the \
                 transfer, never carried from m-1. So this and whnf_fuel_red_wh_monotone_is_false \
                 are compatible -- a budget the two-way algorithm reaches by some OTHER route may \
                 still fail at a larger one, which is exactly the refutation's witness. \
                 \
                 The budget def_eq_fuel_complete_wh witnesses comes through the three-way \
                 capstone, so it IS of this form. The caveat that must travel is therefore \
                 narrower than 'the fuel is not monotone': the guarantee attaches to budgets \
                 certified through the three-way route, not to the two-way algorithm in general. \
                 DerivedProved, zero axiom_deps."
                    .to_string(),
            ),
            (
                Self::wh3_to_wh_roundtrip_witness_src(),
                "def_eq_wh_roundtrip_witness: *** THE PAIR COMPOSES. *** Two theorems side by \
                 side is weaker than it looks -- each could be about a different object, or one \
                 could be vacuous. This runs the ROUND TRIP on completeness's own witness: take \
                 the DefEqFuelAcceptsWh that def_eq_fuel_complete_wh_witness produces, feed it to \
                 soundness, get a DefEq back. The two halves are therefore demonstrably about the \
                 same object, on an inhabitant rather than in the abstract. The two-way \
                 counterpart of def_eq_wh3_roundtrip_witness. DerivedProved, zero axiom_deps."
                    .to_string(),
            ),
        ]
    }

    /// The SUCCESS direction's `app` arm at a **`wstuck`** head result.
    ///
    /// One of the three cheap recursors that replace the pathological shape
    /// (see the module doc). With the head result transported to the literal
    /// `WhStepR.wstuck` and the two-way one to `none`, both app-head reducers
    /// ι-reduce at every non-`lam` head to their ι chains, so eight arms are one
    /// `wh3_chain_step_gives_some` each. The `lam` arm computes: beta on both
    /// sides, and `wh_step_inj` identifies the payload.
    pub(super) fn wh3_to_wh_app_head_some_at_stuck_src() -> String {
        Self::app_head_some_at(
            "wh3_app_head_step_gives_some_at_stuck",
            "WhStepR.wstuck",
            "(OptionType.none KExpr)",
            AppHeadSomeArm::Chain,
        )
    }

    /// The SUCCESS direction's `app` arm at a **`wstarved`** head result.
    ///
    /// Eight arms are REFUTED — `opt_app_ilift3` propagates `wstarved`, which is
    /// not a `wstep` — and only `lam` survives, because beta ignores the head
    /// result entirely. That asymmetry is why this case needs no knowledge of
    /// the two-way head result at all: where the three-way side is not absurd,
    /// the two-way side does not consult `c2` either.
    pub(super) fn wh3_to_wh_app_head_some_at_starved_src() -> String {
        Self::app_head_some_at(
            "wh3_app_head_step_gives_some_at_starved",
            "WhStepR.wstarved",
            "c2",
            AppHeadSomeArm::Absurd,
        )
    }

    /// The SUCCESS direction's `app` arm at a **`wstep f2`** head result.
    ///
    /// All nine arms compute and all nine are the same two lines: the three-way
    /// side rebuilds the application (`lam` contracts instead), the two-way side
    /// does the matching thing, and `wh_step_inj` identifies the payload with
    /// `r`. No arm consults the ι chain, because a head that stepped never
    /// reaches ι on either side.
    pub(super) fn wh3_to_wh_app_head_some_at_step_src() -> String {
        Self::app_head_some_at(
            "wh3_app_head_step_gives_some_at_step",
            "(WhStepR.wstep f2)",
            "(OptionType.some KExpr f2)",
            AppHeadSomeArm::Congruence,
        )
    }

    /// The three cases above share everything but their non-`lam` arm, so they
    /// are emitted from one place. Re-transcribing a nine-arm recursor three
    /// times is how the two spellings of a chain drift apart.
    fn app_head_some_at(name: &str, c3: &str, c2: &str, kind: AppHeadSomeArm) -> String {
        let o = "OptionType KExpr";
        let extra = if matches!(kind, AppHeadSomeArm::Congruence) {
            "(f2 : KExpr) "
        } else if matches!(kind, AppHeadSomeArm::Absurd) {
            "(c2 : OptionType KExpr) "
        } else {
            ""
        };
        let hyp = |z: &str| {
            format!("Eq WhStepR (reduce_app_head_red_wh3 renv wh3 a {z} {c3}) (WhStepR.wstep r)")
        };
        let goal = |z: &str| {
            format!(
                "Eq ({o}) (reduce_app_head_red_wh renv wh2 a {z} {c2}) (OptionType.some KExpr r)"
            )
        };
        let motive = format!("(fun (z : KExpr) => {} -> {})", hyp("z"), goal("z"));
        let at = |z: &str| format!("({} -> {})", hyp(z), goal(z));
        // The `lam` arm is the same in all three: beta on both sides, and the
        // two-way side never consults the head result there, which is why this
        // arm needs no case-specific `c2`.
        let lam_body = format!(
            "Eq.substType KExpr \
             (fun (X : KExpr) => Eq ({o}) (OptionType.some KExpr (instantiate b a)) \
             (OptionType.some KExpr X)) \
             (instantiate b a) r (wh_step_inj (instantiate b a) r hz) \
             (Eq.refl ({o}) (OptionType.some KExpr (instantiate b a)))"
        );
        let arm = |binders: &str, z: &str| {
            let body = match kind {
                AppHeadSomeArm::Chain => {
                    format!("wh3_chain_step_gives_some renv wh3 wh2 hw (KExpr.app {z} a) r hz")
                }
                AppHeadSomeArm::Absurd => format!("wh_starved_ne_step r ({}) hz", goal(z)),
                AppHeadSomeArm::Congruence => format!(
                    "Eq.substType KExpr \
                     (fun (X : KExpr) => Eq ({o}) (OptionType.some KExpr (KExpr.app f2 a)) \
                     (OptionType.some KExpr X)) \
                     (KExpr.app f2 a) r (wh_step_inj (KExpr.app f2 a) r hz) \
                     (Eq.refl ({o}) (OptionType.some KExpr (KExpr.app f2 a)))"
                ),
            };
            format!("(fun {binders} (hz : {}) => {body})", hyp(z))
        };
        format!(
            "def {name} (renv : RedEnv) (wh3 : KExpr -> {o}) (wh2 : KExpr -> {o}) \
             (hw : forall (x : KExpr) (y : KExpr), Eq ({o}) (wh3 x) (OptionType.some KExpr y) -> \
             Eq ({o}) (wh2 x) (OptionType.some KExpr y)) \
             (a : KExpr) {extra}(f : KExpr) (r : KExpr) (h : {hyp_f}) : {goal_f} := \
             KExpr.rec {motive} \
             {a_sort} {a_bvar} {a_app} {a_lam} {a_pi} {a_const} {a_let} {a_proj} {a_lit} \
             f h",
            hyp_f = hyp("f"),
            goal_f = goal("f"),
            a_sort = arm("(n : Level)", "(KExpr.sort n)"),
            a_bvar = arm("(i : Nat)", "(KExpr.bvar i)"),
            a_app = arm(
                &format!(
                    "(g : KExpr) (b : KExpr) (_cg : {}) (_cb : {})",
                    at("g"),
                    at("b")
                ),
                "(KExpr.app g b)",
            ),
            a_lam = format_args!(
                "(fun (ty : KExpr) (b : KExpr) (_cty : {mt}) (_cb : {mb}) \
                 (hz : Eq WhStepR (WhStepR.wstep (instantiate b a)) (WhStepR.wstep r)) => {body})",
                mt = at("ty"),
                mb = at("b"),
                body = lam_body,
            ),
            a_pi = arm(
                &format!(
                    "(ty : KExpr) (b : KExpr) (_cty : {}) (_cb : {})",
                    at("ty"),
                    at("b")
                ),
                "(KExpr.pi ty b)",
            ),
            a_const = arm("(n : Name) (us : ListType Level)", "(KExpr.const n us)"),
            a_let = arm(
                &format!(
                    "(ty : KExpr) (v : KExpr) (b : KExpr) (_c1 : {}) (_c2 : {}) (_c3 : {})",
                    at("ty"),
                    at("v"),
                    at("b")
                ),
                "(KExpr.let_ ty v b)",
            ),
            a_proj = arm(
                &format!("(s : Name) (i : Nat) (sub : KExpr) (_csub : {})", at("sub")),
                "(KExpr.proj s i sub)",
            ),
            a_lit = arm("(v : Nat)", "(KExpr.lit v)"),
        )
    }

    /// The SUCCESS direction's `app` arm, assembled: convoy on the head result
    /// FIRST, then one of the three cheap recursors.
    ///
    /// Same statement as the direct nine-arm version it replaces — only the
    /// cost changes. The convoy is what buys it: inside each of its three arms
    /// the head result is a LITERAL, so the recursor that runs there has both
    /// app-head reducers ι-reducing all the way down.
    ///
    /// Note which arms need which hypothesis. `wstuck` spends `ihs` (item 2's
    /// direction) to learn `c2 = none`; `wstep f2` spends `ihp` to learn
    /// `c2 = some f2`; **`wstarved` spends neither**, because outside `lam` it
    /// is absurd and inside `lam` the two-way side never consults `c2`. That is
    /// the same asymmetry the `proj` arm shows, one level down.
    pub(super) fn wh3_to_wh_app_head_some_via_cases_src() -> String {
        let o = "OptionType KExpr";
        let goal =
            format!("Eq ({o}) (reduce_app_head_red_wh renv wh2 a f c2) (OptionType.some KExpr r)");
        let hyp3 = |q: &str| {
            format!("Eq WhStepR (reduce_app_head_red_wh3 renv wh3 a f {q}) (WhStepR.wstep r)")
        };
        let ihs_ty = |q: &str| {
            format!("Eq WhStepR {q} WhStepR.wstuck -> Eq ({o}) c2 (OptionType.none KExpr)")
        };
        let ihp_ty = |q: &str| {
            format!(
                "forall (y : KExpr), Eq WhStepR {q} (WhStepR.wstep y) -> \
                 Eq ({o}) c2 (OptionType.some KExpr y)"
            )
        };
        // Both computing arms transport the GOAL's `c2` to the literal the
        // hypothesis names, then call the matching case lemma.
        let transport = |lit: &str, proof: &str, sub: &str| {
            format!(
                "Eq.substType ({o}) \
                 (fun (z : {o}) => \
                 Eq ({o}) (reduce_app_head_red_wh renv wh2 a f z) (OptionType.some KExpr r)) \
                 {lit} c2 (Eq.symm ({o}) c2 {lit} ({proof})) ({sub})"
            )
        };
        format!(
            "def wh3_app_head_step_gives_some (renv : RedEnv) (wh3 : KExpr -> {o}) \
             (wh2 : KExpr -> {o}) \
             (hw : forall (x : KExpr) (y : KExpr), Eq ({o}) (wh3 x) (OptionType.some KExpr y) -> \
             Eq ({o}) (wh2 x) (OptionType.some KExpr y)) \
             (a : KExpr) (c3 : WhStepR) (c2 : {o}) \
             (ihs : {ihs_c3}) (ihp : {ihp_c3}) (f : KExpr) (r : KExpr) (h : {hyp_c3}) : {goal} := \
             WhStepR.rec \
             (fun (q : WhStepR) => ({ihs_q}) -> ({ihp_q}) -> {hyp_q} -> {goal}) \
             (fun (ihs0 : {ihs_stuck}) (_ihp0 : {ihp_stuck}) (hq : {hyp_stuck}) => {arm_stuck}) \
             (fun (_ihs1 : {ihs_starved}) (_ihp1 : {ihp_starved}) (hq : {hyp_starved}) => \
             wh3_app_head_step_gives_some_at_starved renv wh3 wh2 hw a c2 f r hq) \
             (fun (f2 : KExpr) (_ihs2 : {ihs_step}) (ihp2 : {ihp_step}) (hq : {hyp_step}) => \
             {arm_step}) \
             c3 ihs ihp h",
            ihs_c3 = ihs_ty("c3"),
            ihp_c3 = ihp_ty("c3"),
            hyp_c3 = hyp3("c3"),
            ihs_q = ihs_ty("q"),
            ihp_q = ihp_ty("q"),
            hyp_q = hyp3("q"),
            ihs_stuck = ihs_ty("WhStepR.wstuck"),
            ihp_stuck = ihp_ty("WhStepR.wstuck"),
            hyp_stuck = hyp3("WhStepR.wstuck"),
            ihs_starved = ihs_ty("WhStepR.wstarved"),
            ihp_starved = ihp_ty("WhStepR.wstarved"),
            hyp_starved = hyp3("WhStepR.wstarved"),
            ihs_step = ihs_ty("(WhStepR.wstep f2)"),
            ihp_step = ihp_ty("(WhStepR.wstep f2)"),
            hyp_step = hyp3("(WhStepR.wstep f2)"),
            arm_stuck = transport(
                "(OptionType.none KExpr)",
                "ihs0 (Eq.refl WhStepR WhStepR.wstuck)",
                "wh3_app_head_step_gives_some_at_stuck renv wh3 wh2 hw a f r hq",
            ),
            arm_step = transport(
                "(OptionType.some KExpr f2)",
                "ihp2 f2 (Eq.refl WhStepR (WhStepR.wstep f2))",
                "wh3_app_head_step_gives_some_at_step renv wh3 wh2 hw a f2 f r hq",
            ),
        )
    }

    /// Registered from `add_defeq_fuel`, after `add_slot_dispatch_at`.
    ///
    /// Sequential and fail-fast, like every stage: a constant that fails takes
    /// the whole spec build down and reports only its NAME, which is why the
    /// scratch test beside this file exists and why the list below is in
    /// dependency order.
    pub(super) fn add_wh3_to_wh_transfer(&mut self) -> Result<(), SpecError> {
        for (src, desc) in Self::wh3_to_wh_arm_sources() {
            self.add_recursive_def(&src, &desc)?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "wh3_to_wh_transfer_tests.rs"]
mod tests;
