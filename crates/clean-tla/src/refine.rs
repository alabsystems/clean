// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! T·REFINE — kernel-checked TLA+ REFINEMENT theorems: the SAFETY slice **and
//! the fairness-preserving APEX (property-transfer form)** — liveness survives
//! the refinement map.
//!
//! This is a brick of the T·REFINE rung of the TY×Clean unified
//! certifying-verification program
//! (`designs/2026-06-20-ty-clean-unified-certifying-program.md`, §6 "T·REFINE
//! — the Refinement Tower: spec ⊑ trust-ir ⊑ binary", §6 "v1-apex"). It sits on
//! top of the already-landed T·SEM behavior semantics ([`crate::semantics`]):
//! `Behavior`, `Sat`, `Runs`, `SemBox`, `Lift`, the safety keystone
//! `InductiveInvariantSound`, and — for the apex — the liveness metatheorem
//! `LatticeRankSoundGeneral` (raw Lamport-WF1 VCs ⇒ `P ⇝ Q`).
//!
//! ## The fairness-preserving apex (property-transfer direction) — PROVED
//!
//! Two new theorems carry liveness across the map (both `Constructive`,
//! `axiom_deps == []`):
//!
//! * [`register_liveness_transfer`] (`TLAsem.LivenessTransfer`) — the LIVENESS
//!   analogue of [`register_property_transfer`]: an abstract `P ⇝ Q` proven for
//!   the abstract spec transfers by proof to the refinement-mapped concrete
//!   behavior, by applying the abstract-liveness hypothesis to the abstract run
//!   `RefMap ref b` (which [`register_mapped_behavior_runs`] supplies). A
//!   one-application corollary of `MappedBehaviorRuns` with `LeadsTo Pa Qa` in
//!   place of `SemBox (Lift InvA)`.
//! * [`register_refined_liveness_from_vcs`] (`TLAsem.RefinedLivenessFromVCs`) —
//!   the blow-away chain: compose `LatticeRankSoundGeneral` (deriving the
//!   abstract `Pa ⇝ Qa` from the raw WF1 verification conditions on the ABSTRACT
//!   system) with `LivenessTransfer` to conclude the CONCRETE implementation's
//!   (mapped) liveness `∀ b, Runs InitC NextC b → Sat (RefMap ref b)
//!   (LeadsTo (Lift Pa)(Lift Qa))` — derived from the abstract spec's
//!   verification conditions + the refinement map.
//!
//! ## HONEST SCOPE — the direction this brick does NOT close
//!
//! This is the **property-transfer direction**: *abstract* liveness ⇒
//! *concrete-mapped* liveness. The abstract-fairness premise `WF A` (resp. the
//! abstract VCs + `∀a, Runs InitA NextA a → Sat a (WF A)` in
//! `RefinedLivenessFromVCs`) is ASSUMED on the abstract system. The harder,
//! complementary **fairness-PRESERVATION** direction — proving the *concrete*
//! system's fairness (`Sat b (WF Ac)`) IMPLIES the abstract fairness on the
//! mapped run (`Sat (RefMap ref b)(WF A)`), so that abstract liveness applies
//! under genuine concrete fairness assumptions — is **NOT closed here**. It is
//! the remaining open Pi-hypothesis (a **soundness-leg** gap, **NOT** an axiom:
//! nothing in this module assumes it; the apex theorems simply take abstract
//! fairness as a hypothesis). Closing it requires two extra side conditions plus
//! `◇□`/`◇` modal reasoning across `drop`/`RefMap`:
//!   * **action projection** (covariant, tractable): `∀ c c', Ac c c' →
//!     A (ref c)(ref c')` — a concrete `⟨Ac⟩` fire maps to an abstract `⟨A⟩`
//!     fire on the mapped run;
//!   * **enabledness reflection** (contravariant, the genuine obstruction):
//!     abstract `Enabled A (ref c)` does NOT generally imply concrete
//!     `Enabled Ac c` (the map can hide a disabled concrete state), so `WF A` on
//!     the mapped run cannot be derived from `WF Ac` without an extra
//!     enabledness-reflection premise.
//! This is the classic Lamport fairness-preservation obstruction; it is named
//! here so it is designed against, and is the next apex brick.
//!
//! ## What it proves
//!
//! Given a concrete spec `(InitC, NextC)`, an abstract spec `(InitA, NextA)`,
//! and a **refinement map** `ref : StateC → StateA` (here both states are
//! `Nat`, per the M0 model), the refinement is witnessed by:
//!
//! * **init-correspondence** — `∀ c, InitC c → InitA (ref c)`;
//! * an **inductive reachable-invariant** `ReachInv` on the concrete side
//!   (`∀ c, InitC c → ReachInv c` and `∀ c c', ReachInv c → NextC c c' →
//!   ReachInv c'`); and
//! * **step-simulation-or-stutter** —
//!   `∀ c c', ReachInv c → NextC c c' → NextA (ref c)(ref c') ∨ ref c' = ref c`.
//!
//! The central lemma [`register_mapped_behavior_runs`]
//! (`TLAsem.MappedBehaviorRuns`) transports the run **pointwise**: it proves the
//! mapped behavior `RefMap ref b := λ i, ref (b i)` is *itself an abstract run*:
//!
//! ```text
//! MappedBehaviorRuns :
//!   ∀ (InitC ReachInv InitA : StatePred) (NextC NextA : Action) (ref : State → State),
//!     (∀ c, InitC c → InitA (ref c)) →
//!     (∀ c, InitC c → ReachInv c) →
//!     (∀ c c', ReachInv c → NextC c c' → ReachInv c') →
//!     (∀ c c', ReachInv c → NextC c c' → Or (NextA (ref c)(ref c')) (Eq (ref c')(ref c))) →
//!     ∀ b, Runs InitC NextC b → Runs InitA NextA (RefMap ref b)
//! ```
//!
//! Because `Runs` is defined **index-wise** (T·SEM: `Init (b 0) ∧ ∀ n, [N]`),
//! the per-step disjunction `NextA ∨ stutter` propagates *pointwise* — no
//! coinduction is needed for the safety slice (the §6 "KEY MOVE"). The stutter
//! is genuinely closed: a concrete stutter `b (succ n) = b n` is lifted by
//! congruence (`Eq.subst`) to an *abstract* stutter `ref (b (succ n)) = ref
//! (b n)`, so the mapped step relation holds with no new axiom.
//!
//! From this lemma, two consequences (both real kernel theorems):
//!
//! * [`register_refinement_mapping_sound`] (`TLAsem.RefinementMappingSound`):
//!   add that `InvA` is an inductive □-invariant of the abstract spec
//!   (`∀ s, InitA s → InvA s`, `∀ s s', InvA s → NextA s s' → InvA s'`) and
//!   conclude every concrete run satisfies the mapped box-invariant
//!   `∀ b, Runs InitC NextC b → Sat (RefMap ref b) (SemBox (Lift InvA))` — the
//!   abstract spec's □-invariant transfers to the mapped concrete behavior. The
//!   proof *composes* `MappedBehaviorRuns` with the keystone
//!   `InductiveInvariantSound` on the abstract side.
//! * [`register_property_transfer`] (`TLAsem.PropertyTransfer`): take the
//!   abstract □-property *as a proven fact* and transfer it by proof:
//!   `(∀ a, Runs InitA NextA a → Sat a (SemBox (Lift InvA))) → ∀ b,
//!   Runs InitC NextC b → Sat (RefMap ref b) (SemBox (Lift InvA))` — a
//!   one-application corollary of `MappedBehaviorRuns`.
//!
//! ## Honesty (per `AGENTS.md`)
//!
//! Every declaration is registered via `Environment::add_decl`, which runs the
//! kernel type-checker. The refinement hypotheses (init-correspondence,
//! `ReachInv`-induction, step-simulation-or-stutter) are all **Pi-bound
//! hypotheses, NOT axioms** — so each theorem's transitive axiom closure stays
//! `⊆ FOUNDATIONAL_AXIOMS` (it reaches only `Eq`/`And`/`Or`/`Nat` and, via
//! `InductiveInvariantSound`, the same). No `Declaration::Axiom` is added; the
//! axiom audit (foundational 3 / domain 4 / total 7) is unchanged. The test
//! module asserts `proof_quality(..) == ProofQuality::Constructive` for all
//! three theorems, a non-vacuity test, and an anti-masquerade test (the proof
//! term genuinely references `MappedBehaviorRuns` / `InductiveInvariantSound`,
//! `Nat.rec`, `Or.rec`, `Eq.subst` — not an axiom).
//!
//! ## Builder discipline
//!
//! Every hand-rolled term builder owns a DISJOINT FVar range (the [`B`]
//! allocator from [`crate::semantics`]). Value-lambda binder type-annotations
//! are rebuilt against the *value* builder's FVars, never the type builder's —
//! the real bug that bit the prior bricks (#1544).

use crate::semantics::reexport::{
    action_ty, app, behavior_ty, c, eq_state, eq_subst_state, formula_ty, hasub_ty, hen_wait_ty,
    hhelp_ty, hpstab_ty, hrank_ty, nat_succ, nat_zero, or, or_inr, or_rec, state, state_pred_ty, B,
};
use clean_kernel::env::{Declaration, EnvError, Environment};
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::level::Level;
use clean_kernel::name::Name;

/// `RefMap : (State → State) → Behavior → Behavior`
/// `RefMap ref b := λ i, ref (b i)` — the refinement-mapped behavior `refb`.
fn register_ref_map(env: &mut Environment) -> Result<(), EnvError> {
    let name = "TLAsem.RefMap";
    if env.get_const(&Name::from_string(name)).is_some() {
        return Ok(());
    }
    // (State → State) → Behavior → Behavior
    let ref_ty = Expr::arrow(state(), state());
    let type_ = Expr::arrow(ref_ty.clone(), Expr::arrow(behavior_ty(), behavior_ty()));
    let mut bld = B::new();
    let (r_id, r) = bld.fresh();
    let (b_id, b) = bld.fresh();
    let (i_id, i) = bld.fresh();
    let body = app(r.clone(), app(b.clone(), i));
    let v = bld.lam(i_id, BinderInfo::Default, state(), body);
    let v = bld.lam(b_id, BinderInfo::Default, behavior_ty(), v);
    let v = bld.lam(r_id, BinderInfo::Default, ref_ty, v);
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value: bld.finish(v),
        is_reducible: true,
    })
}

// ── shared hypothesis-type builders (parameterized by fvars) ────────────────

/// `∀ c, InitC c → InitA (ref c)`.
fn h_initcorr_ty(initc: &Expr, inita: &Expr, refm: &Expr) -> Expr {
    let mut hb = B::new();
    let (cc_id, cc) = hb.fresh();
    let imp = Expr::arrow(
        app(initc.clone(), cc.clone()),
        app(inita.clone(), app(refm.clone(), cc.clone())),
    );
    hb.pi(cc_id, BinderInfo::Default, state(), imp)
}

/// `∀ c, InitC c → ReachInv c`.
fn h_reach_init_ty(initc: &Expr, reach: &Expr) -> Expr {
    let mut hb = B::new();
    let (cc_id, cc) = hb.fresh();
    let imp = Expr::arrow(
        app(initc.clone(), cc.clone()),
        app(reach.clone(), cc.clone()),
    );
    hb.pi(cc_id, BinderInfo::Default, state(), imp)
}

/// `∀ c c', ReachInv c → NextC c c' → ReachInv c'`.
fn h_reach_step_ty(nextc: &Expr, reach: &Expr) -> Expr {
    let mut hb = B::new();
    let (c_id, cc) = hb.fresh();
    let (cp_id, cp) = hb.fresh();
    let nextc_cc = Expr::apps(nextc.clone(), [cc.clone(), cp.clone()]);
    let inner = Expr::arrow(
        app(reach.clone(), cc.clone()),
        Expr::arrow(nextc_cc, app(reach.clone(), cp.clone())),
    );
    let inner = hb.pi(cp_id, BinderInfo::Default, state(), inner);
    hb.pi(c_id, BinderInfo::Default, state(), inner)
}

/// `∀ c c', ReachInv c → NextC c c' → Or (NextA (ref c)(ref c')) (Eq (ref c')(ref c))`.
/// This is the step-simulation-OR-stutter hypothesis.
fn h_stepsim_ty(nextc: &Expr, nexta: &Expr, refm: &Expr, reach: &Expr) -> Expr {
    let mut hb = B::new();
    let (c_id, cc) = hb.fresh();
    let (cp_id, cp) = hb.fresh();
    let refc = app(refm.clone(), cc.clone());
    let refcp = app(refm.clone(), cp.clone());
    let nextc_cc = Expr::apps(nextc.clone(), [cc.clone(), cp.clone()]);
    let nexta_step = Expr::apps(nexta.clone(), [refc.clone(), refcp.clone()]);
    let abs_stutter = eq_state(refcp.clone(), refc.clone());
    let disj = or(nexta_step, abs_stutter);
    let inner = Expr::arrow(app(reach.clone(), cc.clone()), Expr::arrow(nextc_cc, disj));
    let inner = hb.pi(cp_id, BinderInfo::Default, state(), inner);
    hb.pi(c_id, BinderInfo::Default, state(), inner)
}

/// `Runs Init Next b` for given fvars.
fn runs_app(init: &Expr, next: &Expr, b: &Expr) -> Expr {
    Expr::apps(c("TLAsem.Runs"), [init.clone(), next.clone(), b.clone()])
}

/// `RefMap ref b`.
fn refmap_app(refm: &Expr, b: &Expr) -> Expr {
    Expr::apps(c("TLAsem.RefMap"), [refm.clone(), b.clone()])
}

/// `∀ n, Or (Next (b n)(b (succ n))) (Eq (b (succ n))(b n))` — the per-index
/// step disjunction inside `Runs Init Next b` (concrete or abstract).
fn step_forall_ty(next: &Expr, b: &Expr) -> Expr {
    let mut sb = B::new();
    let (n_id, n) = sb.fresh();
    let bn = app(b.clone(), n.clone());
    let bsn = app(b.clone(), nat_succ(n.clone()));
    let stepr = Expr::apps(next.clone(), [bn.clone(), bsn.clone()]);
    let stut = eq_state(bsn.clone(), bn.clone());
    sb.pi(n_id, BinderInfo::Default, state(), or(stepr, stut))
}

/// Register `TLAsem.MappedBehaviorRuns` — the central pointwise transport
/// lemma: the refinement-mapped behavior is itself an abstract run.
///
/// ```text
/// MappedBehaviorRuns :
///   ∀ (InitC ReachInv InitA : StatePred) (NextC NextA : Action) (ref : State → State),
///     (∀ c, InitC c → InitA (ref c)) →
///     (∀ c, InitC c → ReachInv c) →
///     (∀ c c', ReachInv c → NextC c c' → ReachInv c') →
///     (∀ c c', ReachInv c → NextC c c' → NextA (ref c)(ref c') ∨ ref c' = ref c) →
///     ∀ b, Runs InitC NextC b → Runs InitA NextA (RefMap ref b)
/// ```
///
/// PROOF (real `Nat.rec` induction; no axiom stand-ins). `Runs InitA NextA
/// (RefMap ref b)` reduces (Runs/RefMap reducible) to
/// `And (InitA (ref (b 0))) (∀ n, Or (NextA (ref (b n))(ref (b (succ n))))
/// (Eq (ref (b (succ n)))(ref (b n))))`. We build the conjunction:
///   * left — `hInitCorr (b 0) (And.left hRunsC)` (init-correspondence applied
///     to the concrete initial state, which holds by `And.left` of the
///     concrete run).
///   * right — for each `n`, we first establish `reach n : ReachInv (b n)` by
///     `Nat.rec` (base: `hReachInit (b 0) (And.left hRunsC)`; step: split the
///     concrete step `Or.rec` — a real `NextC` feeds `hReachStep`, a stutter
///     `b(succ n)=b n` is closed by `Eq.subst` exactly as the keystone). Then
///     the concrete step disjunction `disjC n` is `Or.rec`-split:
///       - left `hNc : NextC (b n)(b (succ n))` ⇒ `hStepSim (b n)(b(succ n))
///         (reach n) hNc : NextA (ref…)(ref…) ∨ ref(b(succ n)) = ref(b n)` —
///         exactly the abstract step disjunction we need.
///       - right `hEq : b(succ n) = b n` ⇒ congruence: the abstract stutter
///         `ref (b (succ n)) = ref (b n)` follows by `Eq.subst` with motive
///         `λ z, Eq (ref z)(ref (b n))` over `Eq.refl (ref (b n))`, then
///         `Or.inr`.
pub fn register_mapped_behavior_runs(env: &mut Environment) -> Result<(), EnvError> {
    register_prereqs(env)?;
    let name = Name::from_string("TLAsem.MappedBehaviorRuns");
    if env.get_const(&name).is_some() {
        return Ok(());
    }

    let nat = state();
    let ref_ty = Expr::arrow(state(), state());
    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let and_left = c("And.left");

    // ── statement type ────────────────────────────────────────────────────
    let mut tb = B::new();
    let (initc_id, initc) = tb.fresh();
    let (reach_id, reach) = tb.fresh();
    let (inita_id, inita) = tb.fresh();
    let (nextc_id, nextc) = tb.fresh();
    let (nexta_id, nexta) = tb.fresh();
    let (ref_id, refm) = tb.fresh();
    let (hic_id, _hic) = tb.fresh();
    let (hri_id, _hri) = tb.fresh();
    let (hrs_id, _hrs) = tb.fresh();
    let (hss_id, _hss) = tb.fresh();
    let (b_id, b) = tb.fresh();
    let (hruns_id, _hruns) = tb.fresh();

    let concl = runs_app(&inita, &nexta, &refmap_app(&refm, &b));
    let type_ = {
        let mut t = concl;
        t = tb.pi(
            hruns_id,
            BinderInfo::Default,
            runs_app(&initc, &nextc, &b),
            t,
        );
        t = tb.pi(b_id, BinderInfo::Default, behavior_ty(), t);
        t = tb.pi(
            hss_id,
            BinderInfo::Default,
            h_stepsim_ty(&nextc, &nexta, &refm, &reach),
            t,
        );
        t = tb.pi(
            hrs_id,
            BinderInfo::Default,
            h_reach_step_ty(&nextc, &reach),
            t,
        );
        t = tb.pi(
            hri_id,
            BinderInfo::Default,
            h_reach_init_ty(&initc, &reach),
            t,
        );
        t = tb.pi(
            hic_id,
            BinderInfo::Default,
            h_initcorr_ty(&initc, &inita, &refm),
            t,
        );
        t = tb.pi(ref_id, BinderInfo::Default, ref_ty.clone(), t);
        t = tb.pi(nexta_id, BinderInfo::Implicit, action_ty(), t);
        t = tb.pi(nextc_id, BinderInfo::Implicit, action_ty(), t);
        t = tb.pi(inita_id, BinderInfo::Implicit, state_pred_ty(), t);
        t = tb.pi(reach_id, BinderInfo::Implicit, state_pred_ty(), t);
        t = tb.pi(initc_id, BinderInfo::Implicit, state_pred_ty(), t);
        tb.finish(t)
    };

    // ── proof value ───────────────────────────────────────────────────────
    let mut vb = B::new();
    let (vinitc_id, vinitc) = vb.fresh();
    let (vreach_id, vreach) = vb.fresh();
    let (vinita_id, vinita) = vb.fresh();
    let (vnextc_id, vnextc) = vb.fresh();
    let (vnexta_id, vnexta) = vb.fresh();
    let (vref_id, vref) = vb.fresh();
    let (vhic_id, vhic) = vb.fresh();
    let (vhri_id, vhri) = vb.fresh();
    let (vhrs_id, vhrs) = vb.fresh();
    let (vhss_id, vhss) = vb.fresh();
    let (vb_id, vbv) = vb.fresh();
    let (vhruns_id, vhruns) = vb.fresh();

    let b0 = app(vbv.clone(), nat_zero());
    let initc_b0_ty = app(vinitc.clone(), b0.clone());
    let stepsc_ty = step_forall_ty(&vnextc, &vbv);

    // And.left hRunsC : InitC (b 0)
    let h_initc_b0 = Expr::apps(
        and_left.clone(),
        [initc_b0_ty.clone(), stepsc_ty.clone(), vhruns.clone()],
    );
    // And.right hRunsC : ∀ n, Or (NextC (b n)(b(succ n))) (Eq (b(succ n))(b n))
    let h_stepsc = Expr::apps(
        c("And.right"),
        [initc_b0_ty.clone(), stepsc_ty.clone(), vhruns.clone()],
    );

    // reach : ∀ n, ReachInv (b n)  — by Nat.rec.
    let reach_motive = {
        let mut mb = B::new();
        let (n_id, n) = mb.fresh();
        let body = app(vreach.clone(), app(vbv.clone(), n.clone()));
        mb.lam(n_id, BinderInfo::Default, nat.clone(), body)
    };
    // base : ReachInv (b 0) := hReachInit (b 0) (And.left hRunsC)
    let reach_base = Expr::apps(vhri.clone(), [b0.clone(), h_initc_b0.clone()]);
    // step : ∀ n, ReachInv (b n) → ReachInv (b (succ n))
    let reach_step = {
        let mut stb = B::new();
        let (n_id, n) = stb.fresh();
        let (ih_id, ih) = stb.fresh();
        let bn = app(vbv.clone(), n.clone());
        let bsn = app(vbv.clone(), nat_succ(n.clone()));
        let disjc_n = app(h_stepsc.clone(), n.clone());
        let step_rel = Expr::apps(vnextc.clone(), [bn.clone(), bsn.clone()]);
        let stut_eq = eq_state(bsn.clone(), bn.clone());
        let goal = app(vreach.clone(), bsn.clone());

        // fl : NextC (b n)(b(succ n)) → ReachInv (b(succ n))
        let fl = {
            let mut lb = B::new();
            let (hn_id, hn) = lb.fresh();
            let body = Expr::apps(
                vhrs.clone(),
                [bn.clone(), bsn.clone(), ih.clone(), hn.clone()],
            );
            lb.lam(hn_id, BinderInfo::Default, step_rel.clone(), body)
        };
        // fr : Eq (b(succ n))(b n) → ReachInv (b(succ n))
        //   via Eq.subst with motive ReachInv over Eq.symm.
        let fr = {
            let mut rb = B::new();
            let (heq_id, heq) = rb.fresh();
            // hsym : Eq (b n)(b(succ n))
            let hsym = Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.symm"),
                    vec![Level::succ(Level::zero())],
                ),
                [nat.clone(), bsn.clone(), bn.clone(), heq.clone()],
            );
            // @Eq.subst State ReachInv (b n)(b(succ n)) hsym ih : ReachInv (b(succ n))
            let body = eq_subst_state(vreach.clone(), bn.clone(), bsn.clone(), hsym, ih.clone());
            rb.lam(heq_id, BinderInfo::Default, stut_eq.clone(), body)
        };
        let or_motive = {
            let mut ob = B::new();
            let (o_id, _o) = ob.fresh();
            let disj_ty = or(step_rel.clone(), stut_eq.clone());
            ob.lam(o_id, BinderInfo::Default, disj_ty, goal.clone())
        };
        let or_app = or_rec(
            step_rel.clone(),
            stut_eq.clone(),
            or_motive,
            fl,
            fr,
            disjc_n,
        );
        let lam_ih = stb.lam(
            ih_id,
            BinderInfo::Default,
            app(vreach.clone(), bn.clone()),
            or_app,
        );
        stb.lam(n_id, BinderInfo::Default, nat.clone(), lam_ih)
    };
    let reach_fn = {
        let mut jb = B::new();
        let (n_id, n) = jb.fresh();
        let body = Expr::apps(
            nat_rec.clone(),
            [
                reach_motive.clone(),
                reach_base.clone(),
                reach_step.clone(),
                n,
            ],
        );
        jb.lam(n_id, BinderInfo::Default, nat.clone(), body)
    };

    // ── left of the abstract Runs conjunction: InitA (ref (b 0)) ──────────
    let left_proof = Expr::apps(vhic.clone(), [b0.clone(), h_initc_b0.clone()]);

    // ── right: ∀ n, Or (NextA (ref(b n))(ref(b(succ n)))) (Eq (ref(b(succ n)))(ref(b n)))
    let right_proof = {
        let mut pb = B::new();
        let (n_id, n) = pb.fresh();
        let bn = app(vbv.clone(), n.clone());
        let bsn = app(vbv.clone(), nat_succ(n.clone()));
        let refbn = app(vref.clone(), bn.clone());
        let refbsn = app(vref.clone(), bsn.clone());
        let disjc_n = app(h_stepsc.clone(), n.clone());
        let step_rel = Expr::apps(vnextc.clone(), [bn.clone(), bsn.clone()]);
        let stut_eq = eq_state(bsn.clone(), bn.clone());
        // the abstract goal disjunction
        let abs_step = Expr::apps(vnexta.clone(), [refbn.clone(), refbsn.clone()]);
        let abs_stut = eq_state(refbsn.clone(), refbn.clone());
        let goal = or(abs_step.clone(), abs_stut.clone());

        let reach_bn = app(reach_fn.clone(), n.clone());

        // fl : NextC (b n)(b(succ n)) → goal
        //   := hStepSim (b n)(b(succ n)) (reach n) hNc
        let fl = {
            let mut lb = B::new();
            let (hn_id, hn) = lb.fresh();
            let body = Expr::apps(
                vhss.clone(),
                [bn.clone(), bsn.clone(), reach_bn.clone(), hn.clone()],
            );
            lb.lam(hn_id, BinderInfo::Default, step_rel.clone(), body)
        };
        // fr : Eq (b(succ n))(b n) → goal
        //   congruence: ref (b(succ n)) = ref (b n) via Eq.subst with motive
        //   λ z, Eq (ref z)(ref (b n)) applied to Eq.refl (ref (b n)).
        let fr = {
            let mut rb = B::new();
            let (heq_id, heq) = rb.fresh();
            // motive_cong := λ (z : State), Eq (ref z) (ref (b n))
            let motive_cong = {
                let mut zb = B::new();
                let (z_id, z) = zb.fresh();
                let body = eq_state(app(vref.clone(), z.clone()), refbn.clone());
                zb.lam(z_id, BinderInfo::Default, nat.clone(), body)
            };
            // refl : Eq (ref (b n)) (ref (b n))   : motive_cong (b n)
            let refl = Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.refl"),
                    vec![Level::succ(Level::zero())],
                ),
                [nat.clone(), refbn.clone()],
            );
            // hsym : Eq (b n)(b(succ n))   := @Eq.symm State (b(succ n))(b n) heq
            //   (heq : Eq (b(succ n))(b n), the concrete stutter shape from `Runs`).
            let hsym = Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.symm"),
                    vec![Level::succ(Level::zero())],
                ),
                [nat.clone(), bsn.clone(), bn.clone(), heq.clone()],
            );
            // @Eq.subst State motive_cong (b n)(b(succ n)) hsym refl
            //   : motive_cong (b(succ n)) = Eq (ref (b(succ n))) (ref (b n)) = abs_stut
            let cong = eq_subst_state(motive_cong, bn.clone(), bsn.clone(), hsym, refl);
            // Or.inr abs_step abs_stut cong
            let body = or_inr(abs_step.clone(), abs_stut.clone(), cong);
            rb.lam(heq_id, BinderInfo::Default, stut_eq.clone(), body)
        };
        let or_motive = {
            let mut ob = B::new();
            let (o_id, _o) = ob.fresh();
            let disj_ty = or(step_rel.clone(), stut_eq.clone());
            ob.lam(o_id, BinderInfo::Default, disj_ty, goal.clone())
        };
        let or_app = or_rec(
            step_rel.clone(),
            stut_eq.clone(),
            or_motive,
            fl,
            fr,
            disjc_n,
        );
        pb.lam(n_id, BinderInfo::Default, nat.clone(), or_app)
    };

    // And.intro (InitA (ref (b 0)))-type (steps-A)-type left_proof right_proof
    let inita_refb0_ty = app(vinita.clone(), app(vref.clone(), b0.clone()));
    // the abstract step-forall type over the mapped behavior:
    // ∀ n, Or (NextA (ref(b n))(ref(b(succ n)))) (Eq (ref(b(succ n)))(ref(b n)))
    let stepsa_ty = {
        // step_forall over the mapped behavior `RefMap ref b`; but to keep the
        // And.intro type-arg syntactically aligned with the reduced `Runs`
        // conjunct, build it directly with `ref (b ·)`.
        let mut sb = B::new();
        let (n_id, n) = sb.fresh();
        let bn = app(vbv.clone(), n.clone());
        let bsn = app(vbv.clone(), nat_succ(n.clone()));
        let refbn = app(vref.clone(), bn.clone());
        let refbsn = app(vref.clone(), bsn.clone());
        let stepr = Expr::apps(vnexta.clone(), [refbn.clone(), refbsn.clone()]);
        let stut = eq_state(refbsn.clone(), refbn.clone());
        sb.pi(n_id, BinderInfo::Default, state(), or(stepr, stut))
    };
    let conj = Expr::apps(
        c("And.intro"),
        [inita_refb0_ty, stepsa_ty, left_proof, right_proof],
    );

    let value = {
        let mut v = conj;
        v = vb.lam(
            vhruns_id,
            BinderInfo::Default,
            runs_app(&vinitc, &vnextc, &vbv),
            v,
        );
        v = vb.lam(vb_id, BinderInfo::Default, behavior_ty(), v);
        v = vb.lam(
            vhss_id,
            BinderInfo::Default,
            h_stepsim_ty(&vnextc, &vnexta, &vref, &vreach),
            v,
        );
        v = vb.lam(
            vhrs_id,
            BinderInfo::Default,
            h_reach_step_ty(&vnextc, &vreach),
            v,
        );
        v = vb.lam(
            vhri_id,
            BinderInfo::Default,
            h_reach_init_ty(&vinitc, &vreach),
            v,
        );
        v = vb.lam(
            vhic_id,
            BinderInfo::Default,
            h_initcorr_ty(&vinitc, &vinita, &vref),
            v,
        );
        v = vb.lam(vref_id, BinderInfo::Default, ref_ty.clone(), v);
        v = vb.lam(vnexta_id, BinderInfo::Implicit, action_ty(), v);
        v = vb.lam(vnextc_id, BinderInfo::Implicit, action_ty(), v);
        v = vb.lam(vinita_id, BinderInfo::Implicit, state_pred_ty(), v);
        v = vb.lam(vreach_id, BinderInfo::Implicit, state_pred_ty(), v);
        v = vb.lam(vinitc_id, BinderInfo::Implicit, state_pred_ty(), v);
        vb.finish(v)
    };

    env.add_decl(Declaration::Theorem {
        name,
        level_params: vec![],
        type_,
        value,
    })
}

/// `Sat (RefMap ref b) (SemBox (Lift InvA))`.
fn sat_mapped_box_inv(refm: &Expr, b: &Expr, inva: &Expr) -> Expr {
    let lift = app(c("TLAsem.Lift"), inva.clone());
    let boxed = app(c("TLAsem.SemBox"), lift);
    Expr::apps(c("TLAsem.Sat"), [refmap_app(refm, b), boxed])
}

/// `∀ s, InitA s → InvA s` (abstract initiation).
fn h_abs_init_ty(inita: &Expr, inva: &Expr) -> Expr {
    let mut hb = B::new();
    let (s_id, s) = hb.fresh();
    let imp = Expr::arrow(app(inita.clone(), s.clone()), app(inva.clone(), s.clone()));
    hb.pi(s_id, BinderInfo::Default, state(), imp)
}

/// `∀ s s', InvA s → NextA s s' → InvA s'` (abstract consecution).
fn h_abs_cons_ty(nexta: &Expr, inva: &Expr) -> Expr {
    let mut hb = B::new();
    let (s_id, s) = hb.fresh();
    let (sp_id, sp) = hb.fresh();
    let next_ss = Expr::apps(nexta.clone(), [s.clone(), sp.clone()]);
    let inner = Expr::arrow(
        app(inva.clone(), s.clone()),
        Expr::arrow(next_ss, app(inva.clone(), sp.clone())),
    );
    let inner = hb.pi(sp_id, BinderInfo::Default, state(), inner);
    hb.pi(s_id, BinderInfo::Default, state(), inner)
}

/// Register `TLAsem.RefinementMappingSound` — every inductive □-invariant of
/// the abstract spec transfers to the mapped concrete behavior (SAFETY slice).
///
/// ```text
/// RefinementMappingSound :
///   ∀ (InitC ReachInv InitA InvA : StatePred) (NextC NextA : Action) (ref : State → State),
///     (∀ c, InitC c → InitA (ref c)) →                                   -- init-corr
///     (∀ c, InitC c → ReachInv c) →                                      -- reach init
///     (∀ c c', ReachInv c → NextC c c' → ReachInv c') →                  -- reach step
///     (∀ c c', ReachInv c → NextC c c' → NextA (ref c)(ref c') ∨ ref c' = ref c) → -- step-sim
///     (∀ s, InitA s → InvA s) →                                          -- abs initiation
///     (∀ s s', InvA s → NextA s s' → InvA s') →                          -- abs consecution
///     ∀ b, Runs InitC NextC b → Sat (RefMap ref b) (SemBox (Lift InvA))
/// ```
///
/// PROOF (composition; no axiom stand-ins). The mapped behavior `RefMap ref b`
/// is an abstract run by `MappedBehaviorRuns` (applied to the four refinement
/// hypotheses); the abstract invariant `InvA` is `□` along every abstract run
/// by `InductiveInvariantSound` (applied to the two abstract-invariant
/// hypotheses, taking `Safety := InvA` so the `J⇒Safety` premise is `λ s h, h`,
/// i.e. `id`). Composing: `InductiveInvariantSound InitA NextA InvA InvA
/// hAbsInit hAbsCons (λ s h, h) (RefMap ref b) (MappedBehaviorRuns … b hRunsC)`.
pub fn register_refinement_mapping_sound(env: &mut Environment) -> Result<(), EnvError> {
    register_mapped_behavior_runs(env)?;
    let name = Name::from_string("TLAsem.RefinementMappingSound");
    if env.get_const(&name).is_some() {
        return Ok(());
    }

    let ref_ty = Expr::arrow(state(), state());

    // ── statement type ────────────────────────────────────────────────────
    let mut tb = B::new();
    let (initc_id, initc) = tb.fresh();
    let (reach_id, reach) = tb.fresh();
    let (inita_id, inita) = tb.fresh();
    let (inva_id, inva) = tb.fresh();
    let (nextc_id, nextc) = tb.fresh();
    let (nexta_id, nexta) = tb.fresh();
    let (ref_id, refm) = tb.fresh();
    let (hic_id, _hic) = tb.fresh();
    let (hri_id, _hri) = tb.fresh();
    let (hrs_id, _hrs) = tb.fresh();
    let (hss_id, _hss) = tb.fresh();
    let (hai_id, _hai) = tb.fresh();
    let (hac_id, _hac) = tb.fresh();
    let (b_id, b) = tb.fresh();
    let (hruns_id, _hruns) = tb.fresh();

    let concl = sat_mapped_box_inv(&refm, &b, &inva);
    let type_ = {
        let mut t = concl;
        t = tb.pi(
            hruns_id,
            BinderInfo::Default,
            runs_app(&initc, &nextc, &b),
            t,
        );
        t = tb.pi(b_id, BinderInfo::Default, behavior_ty(), t);
        t = tb.pi(hac_id, BinderInfo::Default, h_abs_cons_ty(&nexta, &inva), t);
        t = tb.pi(hai_id, BinderInfo::Default, h_abs_init_ty(&inita, &inva), t);
        t = tb.pi(
            hss_id,
            BinderInfo::Default,
            h_stepsim_ty(&nextc, &nexta, &refm, &reach),
            t,
        );
        t = tb.pi(
            hrs_id,
            BinderInfo::Default,
            h_reach_step_ty(&nextc, &reach),
            t,
        );
        t = tb.pi(
            hri_id,
            BinderInfo::Default,
            h_reach_init_ty(&initc, &reach),
            t,
        );
        t = tb.pi(
            hic_id,
            BinderInfo::Default,
            h_initcorr_ty(&initc, &inita, &refm),
            t,
        );
        t = tb.pi(ref_id, BinderInfo::Default, ref_ty.clone(), t);
        t = tb.pi(nexta_id, BinderInfo::Implicit, action_ty(), t);
        t = tb.pi(nextc_id, BinderInfo::Implicit, action_ty(), t);
        t = tb.pi(inva_id, BinderInfo::Implicit, state_pred_ty(), t);
        t = tb.pi(inita_id, BinderInfo::Implicit, state_pred_ty(), t);
        t = tb.pi(reach_id, BinderInfo::Implicit, state_pred_ty(), t);
        t = tb.pi(initc_id, BinderInfo::Implicit, state_pred_ty(), t);
        tb.finish(t)
    };

    // ── proof value ───────────────────────────────────────────────────────
    let mut vb = B::new();
    let (vinitc_id, vinitc) = vb.fresh();
    let (vreach_id, vreach) = vb.fresh();
    let (vinita_id, vinita) = vb.fresh();
    let (vinva_id, vinva) = vb.fresh();
    let (vnextc_id, vnextc) = vb.fresh();
    let (vnexta_id, vnexta) = vb.fresh();
    let (vref_id, vref) = vb.fresh();
    let (vhic_id, vhic) = vb.fresh();
    let (vhri_id, vhri) = vb.fresh();
    let (vhrs_id, vhrs) = vb.fresh();
    let (vhss_id, vhss) = vb.fresh();
    let (vhai_id, vhai) = vb.fresh();
    let (vhac_id, vhac) = vb.fresh();
    let (vb_id, vbv) = vb.fresh();
    let (vhruns_id, vhruns) = vb.fresh();

    // mapped : Runs InitA NextA (RefMap ref b)
    //   := MappedBehaviorRuns InitC ReachInv InitA NextC NextA ref
    //        hic hri hrs hss b hRunsC
    // (implicit args InitC/ReachInv/InitA/NextC/NextA elaborate, but we pass
    //  them explicitly to keep the term closed and robust against unification.)
    let mapped = Expr::apps(
        c("TLAsem.MappedBehaviorRuns"),
        [
            vinitc.clone(),
            vreach.clone(),
            vinita.clone(),
            vnextc.clone(),
            vnexta.clone(),
            vref.clone(),
            vhic.clone(),
            vhri.clone(),
            vhrs.clone(),
            vhss.clone(),
            vbv.clone(),
            vhruns.clone(),
        ],
    );

    // id_safe : ∀ s, InvA s → InvA s   := λ s h, h
    let id_safe = {
        let mut idb = B::new();
        let (s_id, s) = idb.fresh();
        let (h_id, h) = idb.fresh();
        let r = idb.lam(h_id, BinderInfo::Default, app(vinva.clone(), s.clone()), h);
        idb.lam(s_id, BinderInfo::Default, state(), r)
    };

    // InductiveInvariantSound InitA NextA InvA InvA hAbsInit hAbsCons id_safe
    //   (RefMap ref b) mapped : Sat (RefMap ref b) (SemBox (Lift InvA))
    let body = Expr::apps(
        c("TLAsem.InductiveInvariantSound"),
        [
            vinita.clone(),
            vnexta.clone(),
            vinva.clone(),
            vinva.clone(),
            vhai.clone(),
            vhac.clone(),
            id_safe,
            refmap_app(&vref, &vbv),
            mapped,
        ],
    );

    let value = {
        let mut v = body;
        v = vb.lam(
            vhruns_id,
            BinderInfo::Default,
            runs_app(&vinitc, &vnextc, &vbv),
            v,
        );
        v = vb.lam(vb_id, BinderInfo::Default, behavior_ty(), v);
        v = vb.lam(
            vhac_id,
            BinderInfo::Default,
            h_abs_cons_ty(&vnexta, &vinva),
            v,
        );
        v = vb.lam(
            vhai_id,
            BinderInfo::Default,
            h_abs_init_ty(&vinita, &vinva),
            v,
        );
        v = vb.lam(
            vhss_id,
            BinderInfo::Default,
            h_stepsim_ty(&vnextc, &vnexta, &vref, &vreach),
            v,
        );
        v = vb.lam(
            vhrs_id,
            BinderInfo::Default,
            h_reach_step_ty(&vnextc, &vreach),
            v,
        );
        v = vb.lam(
            vhri_id,
            BinderInfo::Default,
            h_reach_init_ty(&vinitc, &vreach),
            v,
        );
        v = vb.lam(
            vhic_id,
            BinderInfo::Default,
            h_initcorr_ty(&vinitc, &vinita, &vref),
            v,
        );
        v = vb.lam(vref_id, BinderInfo::Default, ref_ty.clone(), v);
        v = vb.lam(vnexta_id, BinderInfo::Implicit, action_ty(), v);
        v = vb.lam(vnextc_id, BinderInfo::Implicit, action_ty(), v);
        v = vb.lam(vinva_id, BinderInfo::Implicit, state_pred_ty(), v);
        v = vb.lam(vinita_id, BinderInfo::Implicit, state_pred_ty(), v);
        v = vb.lam(vreach_id, BinderInfo::Implicit, state_pred_ty(), v);
        v = vb.lam(vinitc_id, BinderInfo::Implicit, state_pred_ty(), v);
        vb.finish(v)
    };

    env.add_decl(Declaration::Theorem {
        name,
        level_params: vec![],
        type_,
        value,
    })
}

/// Register `TLAsem.PropertyTransfer` — a □-property *proven* for the abstract
/// spec transfers by proof to the mapped concrete behavior.
///
/// ```text
/// PropertyTransfer :
///   ∀ (InitC ReachInv InitA InvA : StatePred) (NextC NextA : Action) (ref : State → State),
///     (∀ c, InitC c → InitA (ref c)) →
///     (∀ c, InitC c → ReachInv c) →
///     (∀ c c', ReachInv c → NextC c c' → ReachInv c') →
///     (∀ c c', ReachInv c → NextC c c' → NextA (ref c)(ref c') ∨ ref c' = ref c) →
///     (∀ a, Runs InitA NextA a → Sat a (SemBox (Lift InvA))) →
///     ∀ b, Runs InitC NextC b → Sat (RefMap ref b) (SemBox (Lift InvA))
/// ```
///
/// PROOF (one application; no axiom stand-ins). The abstract □-property holds
/// for the mapped behavior because the mapped behavior is an abstract run:
/// `hAbsProp (RefMap ref b) (MappedBehaviorRuns … b hRunsC)`.
pub fn register_property_transfer(env: &mut Environment) -> Result<(), EnvError> {
    register_mapped_behavior_runs(env)?;
    let name = Name::from_string("TLAsem.PropertyTransfer");
    if env.get_const(&name).is_some() {
        return Ok(());
    }

    let ref_ty = Expr::arrow(state(), state());

    // `∀ a, Runs InitA NextA a → Sat a (SemBox (Lift InvA))`.
    let h_abs_prop_ty = |inita: &Expr, nexta: &Expr, inva: &Expr| -> Expr {
        let mut hb = B::new();
        let (a_id, a) = hb.fresh();
        let lift = app(c("TLAsem.Lift"), inva.clone());
        let boxed = app(c("TLAsem.SemBox"), lift);
        let sat = Expr::apps(c("TLAsem.Sat"), [a.clone(), boxed]);
        let imp = Expr::arrow(runs_app(inita, nexta, &a), sat);
        hb.pi(a_id, BinderInfo::Default, behavior_ty(), imp)
    };

    // ── statement type ────────────────────────────────────────────────────
    let mut tb = B::new();
    let (initc_id, initc) = tb.fresh();
    let (reach_id, reach) = tb.fresh();
    let (inita_id, inita) = tb.fresh();
    let (inva_id, inva) = tb.fresh();
    let (nextc_id, nextc) = tb.fresh();
    let (nexta_id, nexta) = tb.fresh();
    let (ref_id, refm) = tb.fresh();
    let (hic_id, _hic) = tb.fresh();
    let (hri_id, _hri) = tb.fresh();
    let (hrs_id, _hrs) = tb.fresh();
    let (hss_id, _hss) = tb.fresh();
    let (hap_id, _hap) = tb.fresh();
    let (b_id, b) = tb.fresh();
    let (hruns_id, _hruns) = tb.fresh();

    let concl = sat_mapped_box_inv(&refm, &b, &inva);
    let type_ = {
        let mut t = concl;
        t = tb.pi(
            hruns_id,
            BinderInfo::Default,
            runs_app(&initc, &nextc, &b),
            t,
        );
        t = tb.pi(b_id, BinderInfo::Default, behavior_ty(), t);
        t = tb.pi(
            hap_id,
            BinderInfo::Default,
            h_abs_prop_ty(&inita, &nexta, &inva),
            t,
        );
        t = tb.pi(
            hss_id,
            BinderInfo::Default,
            h_stepsim_ty(&nextc, &nexta, &refm, &reach),
            t,
        );
        t = tb.pi(
            hrs_id,
            BinderInfo::Default,
            h_reach_step_ty(&nextc, &reach),
            t,
        );
        t = tb.pi(
            hri_id,
            BinderInfo::Default,
            h_reach_init_ty(&initc, &reach),
            t,
        );
        t = tb.pi(
            hic_id,
            BinderInfo::Default,
            h_initcorr_ty(&initc, &inita, &refm),
            t,
        );
        t = tb.pi(ref_id, BinderInfo::Default, ref_ty.clone(), t);
        t = tb.pi(nexta_id, BinderInfo::Implicit, action_ty(), t);
        t = tb.pi(nextc_id, BinderInfo::Implicit, action_ty(), t);
        t = tb.pi(inva_id, BinderInfo::Implicit, state_pred_ty(), t);
        t = tb.pi(inita_id, BinderInfo::Implicit, state_pred_ty(), t);
        t = tb.pi(reach_id, BinderInfo::Implicit, state_pred_ty(), t);
        t = tb.pi(initc_id, BinderInfo::Implicit, state_pred_ty(), t);
        tb.finish(t)
    };

    // ── proof value ───────────────────────────────────────────────────────
    let mut vb = B::new();
    let (vinitc_id, vinitc) = vb.fresh();
    let (vreach_id, vreach) = vb.fresh();
    let (vinita_id, vinita) = vb.fresh();
    let (vinva_id, vinva) = vb.fresh();
    let (vnextc_id, vnextc) = vb.fresh();
    let (vnexta_id, vnexta) = vb.fresh();
    let (vref_id, vref) = vb.fresh();
    let (vhic_id, vhic) = vb.fresh();
    let (vhri_id, vhri) = vb.fresh();
    let (vhrs_id, vhrs) = vb.fresh();
    let (vhss_id, vhss) = vb.fresh();
    let (vhap_id, vhap) = vb.fresh();
    let (vb_id, vbv) = vb.fresh();
    let (vhruns_id, vhruns) = vb.fresh();

    let mapped = Expr::apps(
        c("TLAsem.MappedBehaviorRuns"),
        [
            vinitc.clone(),
            vreach.clone(),
            vinita.clone(),
            vnextc.clone(),
            vnexta.clone(),
            vref.clone(),
            vhic.clone(),
            vhri.clone(),
            vhrs.clone(),
            vhss.clone(),
            vbv.clone(),
            vhruns.clone(),
        ],
    );
    // hAbsProp (RefMap ref b) mapped : Sat (RefMap ref b) (SemBox (Lift InvA))
    let body = Expr::apps(vhap.clone(), [refmap_app(&vref, &vbv), mapped]);

    let value = {
        let mut v = body;
        v = vb.lam(
            vhruns_id,
            BinderInfo::Default,
            runs_app(&vinitc, &vnextc, &vbv),
            v,
        );
        v = vb.lam(vb_id, BinderInfo::Default, behavior_ty(), v);
        v = vb.lam(
            vhap_id,
            BinderInfo::Default,
            h_abs_prop_ty(&vinita, &vnexta, &vinva),
            v,
        );
        v = vb.lam(
            vhss_id,
            BinderInfo::Default,
            h_stepsim_ty(&vnextc, &vnexta, &vref, &vreach),
            v,
        );
        v = vb.lam(
            vhrs_id,
            BinderInfo::Default,
            h_reach_step_ty(&vnextc, &vreach),
            v,
        );
        v = vb.lam(
            vhri_id,
            BinderInfo::Default,
            h_reach_init_ty(&vinitc, &vreach),
            v,
        );
        v = vb.lam(
            vhic_id,
            BinderInfo::Default,
            h_initcorr_ty(&vinitc, &vinita, &vref),
            v,
        );
        v = vb.lam(vref_id, BinderInfo::Default, ref_ty.clone(), v);
        v = vb.lam(vnexta_id, BinderInfo::Implicit, action_ty(), v);
        v = vb.lam(vnextc_id, BinderInfo::Implicit, action_ty(), v);
        v = vb.lam(vinva_id, BinderInfo::Implicit, state_pred_ty(), v);
        v = vb.lam(vinita_id, BinderInfo::Implicit, state_pred_ty(), v);
        v = vb.lam(vreach_id, BinderInfo::Implicit, state_pred_ty(), v);
        v = vb.lam(vinitc_id, BinderInfo::Implicit, state_pred_ty(), v);
        vb.finish(v)
    };

    env.add_decl(Declaration::Theorem {
        name,
        level_params: vec![],
        type_,
        value,
    })
}

// ════════════════════════════════════════════════════════════════════════════
//  THE FAIRNESS-PRESERVING REFINEMENT APEX (property-transfer form):
//  liveness survives the refinement map.
// ════════════════════════════════════════════════════════════════════════════

/// `Sat (RefMap ref b) (LeadsTo Pa Qa)`.
fn sat_mapped_leadsto(refm: &Expr, b: &Expr, pa: &Expr, qa: &Expr) -> Expr {
    let lt = Expr::apps(c("TLAsem.LeadsTo"), [pa.clone(), qa.clone()]);
    Expr::apps(c("TLAsem.Sat"), [refmap_app(refm, b), lt])
}

/// `Lift P`.
fn lift(p: &Expr) -> Expr {
    app(c("TLAsem.Lift"), p.clone())
}

/// `∀ a, Runs InitA NextA a → Sat a (WF A)` — the abstract-system fairness
/// premise: every abstract run is weakly fair to `A`.
fn h_abs_fair_ty(inita: &Expr, nexta: &Expr, a_act: &Expr) -> Expr {
    let mut hb = B::new();
    let (a_id, a) = hb.fresh();
    let wf = app(c("TLAsem.WF"), a_act.clone());
    let sat = Expr::apps(c("TLAsem.Sat"), [a.clone(), wf]);
    let imp = Expr::arrow(runs_app(inita, nexta, &a), sat);
    hb.pi(a_id, BinderInfo::Default, behavior_ty(), imp)
}

/// Register `TLAsem.LivenessTransfer` — the **liveness analogue of
/// `PropertyTransfer`**: an abstract `P ⇝ Q` proven for the *abstract* spec
/// transfers by proof to the refinement-mapped concrete behavior.
///
/// ```text
/// LivenessTransfer :
///   ∀ (InitC ReachInv InitA : StatePred) (NextC NextA : Action)
///     (ref : State → State) (Pa Qa : Formula),
///     (∀ c, InitC c → InitA (ref c)) →                                   -- init-corr
///     (∀ c, InitC c → ReachInv c) →                                      -- reach init
///     (∀ c c', ReachInv c → NextC c c' → ReachInv c') →                  -- reach step
///     (∀ c c', ReachInv c → NextC c c' → NextA (ref c)(ref c') ∨ ref c' = ref c) → -- step-sim
///     (∀ a, Runs InitA NextA a → Sat a (LeadsTo Pa Qa)) →                -- abstract liveness
///     ∀ b, Runs InitC NextC b → Sat (RefMap ref b) (LeadsTo Pa Qa)
/// ```
///
/// PROOF (one application; no axiom stand-ins). The refinement-mapped behavior
/// `RefMap ref b` IS an abstract run by [`register_mapped_behavior_runs`]
/// (`MappedBehaviorRuns` applied to the four refinement hypotheses); the abstract
/// liveness hypothesis, instantiated at that mapped run, gives the mapped
/// `P ⇝ Q` directly:
///   `hAbsLive (RefMap ref b) (MappedBehaviorRuns … b hRunsC)`.
///
/// This is a *structural near-clone* of [`register_property_transfer`] with
/// `LeadsTo Pa Qa` in place of `SemBox (Lift InvA)` — the safety→liveness swap
/// is purely in the transported formula; `MappedBehaviorRuns` does all the work
/// because `Runs` is index-wise (no coinduction). `Pa`/`Qa` are arbitrary
/// behavior `Formula`s, so this transports *any* leads-to (not only `Lift`ed
/// state predicates).
pub fn register_liveness_transfer(env: &mut Environment) -> Result<(), EnvError> {
    register_mapped_behavior_runs(env)?;
    let name = Name::from_string("TLAsem.LivenessTransfer");
    if env.get_const(&name).is_some() {
        return Ok(());
    }

    let ref_ty = Expr::arrow(state(), state());

    // `∀ a, Runs InitA NextA a → Sat a (LeadsTo Pa Qa)`.
    let h_abs_live_ty = |inita: &Expr, nexta: &Expr, pa: &Expr, qa: &Expr| -> Expr {
        let mut hb = B::new();
        let (a_id, a) = hb.fresh();
        let lt = Expr::apps(c("TLAsem.LeadsTo"), [pa.clone(), qa.clone()]);
        let sat = Expr::apps(c("TLAsem.Sat"), [a.clone(), lt]);
        let imp = Expr::arrow(runs_app(inita, nexta, &a), sat);
        hb.pi(a_id, BinderInfo::Default, behavior_ty(), imp)
    };

    // ── statement type ────────────────────────────────────────────────────
    let mut tb = B::new();
    let (initc_id, initc) = tb.fresh();
    let (reach_id, reach) = tb.fresh();
    let (inita_id, inita) = tb.fresh();
    let (nextc_id, nextc) = tb.fresh();
    let (nexta_id, nexta) = tb.fresh();
    let (ref_id, refm) = tb.fresh();
    let (pa_id, pa) = tb.fresh();
    let (qa_id, qa) = tb.fresh();
    let (hic_id, _hic) = tb.fresh();
    let (hri_id, _hri) = tb.fresh();
    let (hrs_id, _hrs) = tb.fresh();
    let (hss_id, _hss) = tb.fresh();
    let (hal_id, _hal) = tb.fresh();
    let (b_id, b) = tb.fresh();
    let (hruns_id, _hruns) = tb.fresh();

    let concl = sat_mapped_leadsto(&refm, &b, &pa, &qa);
    let type_ = {
        let mut t = concl;
        t = tb.pi(
            hruns_id,
            BinderInfo::Default,
            runs_app(&initc, &nextc, &b),
            t,
        );
        t = tb.pi(b_id, BinderInfo::Default, behavior_ty(), t);
        t = tb.pi(
            hal_id,
            BinderInfo::Default,
            h_abs_live_ty(&inita, &nexta, &pa, &qa),
            t,
        );
        t = tb.pi(
            hss_id,
            BinderInfo::Default,
            h_stepsim_ty(&nextc, &nexta, &refm, &reach),
            t,
        );
        t = tb.pi(
            hrs_id,
            BinderInfo::Default,
            h_reach_step_ty(&nextc, &reach),
            t,
        );
        t = tb.pi(
            hri_id,
            BinderInfo::Default,
            h_reach_init_ty(&initc, &reach),
            t,
        );
        t = tb.pi(
            hic_id,
            BinderInfo::Default,
            h_initcorr_ty(&initc, &inita, &refm),
            t,
        );
        t = tb.pi(qa_id, BinderInfo::Implicit, formula_ty(), t);
        t = tb.pi(pa_id, BinderInfo::Implicit, formula_ty(), t);
        t = tb.pi(ref_id, BinderInfo::Default, ref_ty.clone(), t);
        t = tb.pi(nexta_id, BinderInfo::Implicit, action_ty(), t);
        t = tb.pi(nextc_id, BinderInfo::Implicit, action_ty(), t);
        t = tb.pi(inita_id, BinderInfo::Implicit, state_pred_ty(), t);
        t = tb.pi(reach_id, BinderInfo::Implicit, state_pred_ty(), t);
        t = tb.pi(initc_id, BinderInfo::Implicit, state_pred_ty(), t);
        tb.finish(t)
    };

    // ── proof value ───────────────────────────────────────────────────────
    let mut vb = B::new();
    let (vinitc_id, vinitc) = vb.fresh();
    let (vreach_id, vreach) = vb.fresh();
    let (vinita_id, vinita) = vb.fresh();
    let (vnextc_id, vnextc) = vb.fresh();
    let (vnexta_id, vnexta) = vb.fresh();
    let (vref_id, vref) = vb.fresh();
    let (vpa_id, vpa) = vb.fresh();
    let (vqa_id, vqa) = vb.fresh();
    let (vhic_id, vhic) = vb.fresh();
    let (vhri_id, vhri) = vb.fresh();
    let (vhrs_id, vhrs) = vb.fresh();
    let (vhss_id, vhss) = vb.fresh();
    let (vhal_id, vhal) = vb.fresh();
    let (vb_id, vbv) = vb.fresh();
    let (vhruns_id, vhruns) = vb.fresh();

    // mapped : Runs InitA NextA (RefMap ref b)
    let mapped = Expr::apps(
        c("TLAsem.MappedBehaviorRuns"),
        [
            vinitc.clone(),
            vreach.clone(),
            vinita.clone(),
            vnextc.clone(),
            vnexta.clone(),
            vref.clone(),
            vhic.clone(),
            vhri.clone(),
            vhrs.clone(),
            vhss.clone(),
            vbv.clone(),
            vhruns.clone(),
        ],
    );
    // hAbsLive (RefMap ref b) mapped : Sat (RefMap ref b) (LeadsTo Pa Qa)
    let body = Expr::apps(vhal.clone(), [refmap_app(&vref, &vbv), mapped]);

    let value = {
        let mut v = body;
        v = vb.lam(
            vhruns_id,
            BinderInfo::Default,
            runs_app(&vinitc, &vnextc, &vbv),
            v,
        );
        v = vb.lam(vb_id, BinderInfo::Default, behavior_ty(), v);
        v = vb.lam(
            vhal_id,
            BinderInfo::Default,
            h_abs_live_ty(&vinita, &vnexta, &vpa, &vqa),
            v,
        );
        v = vb.lam(
            vhss_id,
            BinderInfo::Default,
            h_stepsim_ty(&vnextc, &vnexta, &vref, &vreach),
            v,
        );
        v = vb.lam(
            vhrs_id,
            BinderInfo::Default,
            h_reach_step_ty(&vnextc, &vreach),
            v,
        );
        v = vb.lam(
            vhri_id,
            BinderInfo::Default,
            h_reach_init_ty(&vinitc, &vreach),
            v,
        );
        v = vb.lam(
            vhic_id,
            BinderInfo::Default,
            h_initcorr_ty(&vinitc, &vinita, &vref),
            v,
        );
        v = vb.lam(vqa_id, BinderInfo::Implicit, formula_ty(), v);
        v = vb.lam(vpa_id, BinderInfo::Implicit, formula_ty(), v);
        v = vb.lam(vref_id, BinderInfo::Default, ref_ty.clone(), v);
        v = vb.lam(vnexta_id, BinderInfo::Implicit, action_ty(), v);
        v = vb.lam(vnextc_id, BinderInfo::Implicit, action_ty(), v);
        v = vb.lam(vinita_id, BinderInfo::Implicit, state_pred_ty(), v);
        v = vb.lam(vreach_id, BinderInfo::Implicit, state_pred_ty(), v);
        v = vb.lam(vinitc_id, BinderInfo::Implicit, state_pred_ty(), v);
        vb.finish(v)
    };

    env.add_decl(Declaration::Theorem {
        name,
        level_params: vec![],
        type_,
        value,
    })
}

// ── the blow-away chain: concrete-mapped liveness FROM the abstract WF1 VCs ──

/// Register `TLAsem.RefinedLivenessFromVCs` — **the apex chain**: the
/// CONCRETE implementation's (mapped) liveness, derived from the ABSTRACT
/// spec's raw Lamport WF1 verification conditions plus the refinement map.
///
/// ```text
/// RefinedLivenessFromVCs :
///   ∀ (InitC ReachInv InitA : StatePred) (NextC NextA A : Action)
///     (Pa Qa : StatePred) (rho : State → Nat) (ref : State → State),
///     -- refinement obligations (CONCRETE ⊑ ABSTRACT):
///     (∀ c, InitC c → InitA (ref c)) →
///     (∀ c, InitC c → ReachInv c) →
///     (∀ c c', ReachInv c → NextC c c' → ReachInv c') →
///     (∀ c c', ReachInv c → NextC c c' → NextA (ref c)(ref c') ∨ ref c' = ref c) →
///     -- abstract WF1 verification conditions (on the ABSTRACT system A ⊆ NextA):
///     (∀ s s', A s s' → NextA s s') →                          -- HAsub
///     (∀ s s', Pa s → ¬Qa s → NextA s s' → Qa s' ∨ Pa s') →    -- Hpstab
///     (∀ s s', Pa s → ¬Qa s → NextA s s' → Qa s' ∨ rho s' ≤ rho s) → -- Hrank
///     (∀ s s', Pa s → ¬Qa s → A s s' → Qa s' ∨ rho s' < rho s) → -- Hhelp
///     (∀ s, Pa s → ¬Qa s → Enabled A s) →                       -- Hen (enabled while waiting)
///     -- abstract fairness premise:
///     (∀ a, Runs InitA NextA a → Sat a (WF A)) →                -- Hfair
///     ∀ b, Runs InitC NextC b → Sat (RefMap ref b) (LeadsTo (Lift Pa)(Lift Qa))
/// ```
///
/// PROOF (the blow-away composition; no axiom stand-ins). Two moves:
///
///  1. **Abstract liveness from the VCs.** Build
///     `hAbsLive : ∀ a, Runs InitA NextA a → Sat a (LeadsTo (Lift Pa)(Lift Qa))`
///     by, for each abstract run `a`, invoking
///     [`LatticeRankSoundGeneral`](crate::semantics::register_lattice_rank_sound_general)
///     `A NextA Pa Qa rho a Hstep HAsub Hpstab Hrank Hhelp Hen (Hfair a hRunsA)`,
///     where `Hstep := And.right hRunsA` is the step-disjunction component of the
///     abstract run. The result `∀ n, Pa(a n) → ∃ m, Qa(a (n+m))` is
///     **definitionally** `Sat a (LeadsTo (Lift Pa)(Lift Qa))` (T·SEM
///     `LeadsTo`/`Sat`/`SemBox`/`SemDiam`/`drop`/`Lift` all reduce), so it
///     inhabits the abstract-liveness premise up to def-eq.
///  2. **Transfer across the map.** Apply
///     [`register_liveness_transfer`] (`LivenessTransfer`) with `Pa := Lift Pa`,
///     `Qa := Lift Qa` and `hAbsLive` to conclude the concrete-mapped `P ⇝ Q`.
///
/// Every hypothesis is Pi-bound (NONE is an axiom). Transitive axiom closure ⊆
/// FOUNDATIONAL (it reaches only what `LatticeRankSoundGeneral` /
/// `LivenessTransfer` / `MappedBehaviorRuns` reach). Needs
/// `Environment::with_prelude()` (for `LatticeRankSoundGeneral`'s `Acc.rec`).
pub fn register_refined_liveness_from_vcs(env: &mut Environment) -> Result<(), EnvError> {
    register_liveness_transfer(env)?;
    // `LatticeRankSoundGeneral` (and its substrate) is only registered when the
    // well-founded prelude machinery is available (see
    // `crate::semantics::register_tla_liveness`). On a bare env it is absent and
    // this apex theorem cannot be built — register the safety slice only.
    if env
        .get_const(&Name::from_string("TLAsem.LatticeRankSoundGeneral"))
        .is_none()
    {
        return Ok(());
    }
    let name = Name::from_string("TLAsem.RefinedLivenessFromVCs");
    if env.get_const(&name).is_some() {
        return Ok(());
    }

    let ref_ty = Expr::arrow(state(), state());
    let rho_ty = Expr::arrow(state(), state());

    // ── statement type ────────────────────────────────────────────────────
    let mut tb = B::new();
    let (initc_id, initc) = tb.fresh();
    let (reach_id, reach) = tb.fresh();
    let (inita_id, inita) = tb.fresh();
    let (nextc_id, nextc) = tb.fresh();
    let (nexta_id, nexta) = tb.fresh();
    let (a_id, a_act) = tb.fresh();
    let (pa_id, pa) = tb.fresh();
    let (qa_id, qa) = tb.fresh();
    let (rho_id, rho) = tb.fresh();
    let (ref_id, refm) = tb.fresh();
    let (hic_id, _hic) = tb.fresh();
    let (hri_id, _hri) = tb.fresh();
    let (hrs_id, _hrs) = tb.fresh();
    let (hss_id, _hss) = tb.fresh();
    let (hasub_id, _hasub) = tb.fresh();
    let (hpstab_id, _hpstab) = tb.fresh();
    let (hrank_id, _hrank) = tb.fresh();
    let (hhelp_id, _hhelp) = tb.fresh();
    let (hen_id, _hen) = tb.fresh();
    let (hfair_id, _hfair) = tb.fresh();
    let (b_id, b) = tb.fresh();
    let (hruns_id, _hruns) = tb.fresh();

    let concl = sat_mapped_leadsto(&refm, &b, &lift(&pa), &lift(&qa));
    let type_ = {
        let mut t = concl;
        t = tb.pi(
            hruns_id,
            BinderInfo::Default,
            runs_app(&initc, &nextc, &b),
            t,
        );
        t = tb.pi(b_id, BinderInfo::Default, behavior_ty(), t);
        t = tb.pi(
            hfair_id,
            BinderInfo::Default,
            h_abs_fair_ty(&inita, &nexta, &a_act),
            t,
        );
        t = tb.pi(
            hen_id,
            BinderInfo::Default,
            hen_wait_ty(&a_act, &pa, &qa),
            t,
        );
        t = tb.pi(
            hhelp_id,
            BinderInfo::Default,
            hhelp_ty(&a_act, &pa, &qa, &rho),
            t,
        );
        t = tb.pi(
            hrank_id,
            BinderInfo::Default,
            hrank_ty(&nexta, &pa, &qa, &rho),
            t,
        );
        t = tb.pi(
            hpstab_id,
            BinderInfo::Default,
            hpstab_ty(&nexta, &pa, &qa),
            t,
        );
        t = tb.pi(hasub_id, BinderInfo::Default, hasub_ty(&a_act, &nexta), t);
        t = tb.pi(
            hss_id,
            BinderInfo::Default,
            h_stepsim_ty(&nextc, &nexta, &refm, &reach),
            t,
        );
        t = tb.pi(
            hrs_id,
            BinderInfo::Default,
            h_reach_step_ty(&nextc, &reach),
            t,
        );
        t = tb.pi(
            hri_id,
            BinderInfo::Default,
            h_reach_init_ty(&initc, &reach),
            t,
        );
        t = tb.pi(
            hic_id,
            BinderInfo::Default,
            h_initcorr_ty(&initc, &inita, &refm),
            t,
        );
        t = tb.pi(ref_id, BinderInfo::Default, ref_ty.clone(), t);
        t = tb.pi(rho_id, BinderInfo::Default, rho_ty.clone(), t);
        t = tb.pi(qa_id, BinderInfo::Implicit, state_pred_ty(), t);
        t = tb.pi(pa_id, BinderInfo::Implicit, state_pred_ty(), t);
        t = tb.pi(a_id, BinderInfo::Implicit, action_ty(), t);
        t = tb.pi(nexta_id, BinderInfo::Implicit, action_ty(), t);
        t = tb.pi(nextc_id, BinderInfo::Implicit, action_ty(), t);
        t = tb.pi(inita_id, BinderInfo::Implicit, state_pred_ty(), t);
        t = tb.pi(reach_id, BinderInfo::Implicit, state_pred_ty(), t);
        t = tb.pi(initc_id, BinderInfo::Implicit, state_pred_ty(), t);
        tb.finish(t)
    };

    // ── proof value ───────────────────────────────────────────────────────
    let mut vb = B::new();
    let (vinitc_id, vinitc) = vb.fresh();
    let (vreach_id, vreach) = vb.fresh();
    let (vinita_id, vinita) = vb.fresh();
    let (vnextc_id, vnextc) = vb.fresh();
    let (vnexta_id, vnexta) = vb.fresh();
    let (va_id, va_act) = vb.fresh();
    let (vpa_id, vpa) = vb.fresh();
    let (vqa_id, vqa) = vb.fresh();
    let (vrho_id, vrho) = vb.fresh();
    let (vref_id, vref) = vb.fresh();
    let (vhic_id, vhic) = vb.fresh();
    let (vhri_id, vhri) = vb.fresh();
    let (vhrs_id, vhrs) = vb.fresh();
    let (vhss_id, vhss) = vb.fresh();
    let (vhasub_id, vhasub) = vb.fresh();
    let (vhpstab_id, vhpstab) = vb.fresh();
    let (vhrank_id, vhrank) = vb.fresh();
    let (vhhelp_id, vhhelp) = vb.fresh();
    let (vhen_id, vhen) = vb.fresh();
    let (vhfair_id, vhfair) = vb.fresh();
    let (vb_id, vbv) = vb.fresh();
    let (vhruns_id, vhruns) = vb.fresh();

    // hAbsLive : ∀ a, Runs InitA NextA a → Sat a (LeadsTo (Lift Pa)(Lift Qa))
    //   := λ (a)(hRunsA)(n)(hP) =>
    //        LatticeRankSoundGeneral A NextA Pa Qa rho a
    //          (And.right … hRunsA) HAsub Hpstab Hrank Hhelp Hen (Hfair a hRunsA) n hP
    // (body type ∃ m, Qa(a(n+m)) is def-eq to the LeadsTo conclusion).
    let h_abs_live = {
        let mut lb = B::new();
        let (la_id, la) = lb.fresh();
        let (lhruns_id, lhruns) = lb.fresh();
        let (ln_id, ln) = lb.fresh();
        let (lhp_id, lhp) = lb.fresh();

        let inita_a0_ty = app(vinita.clone(), app(la.clone(), nat_zero()));
        let stepsa_ty = step_forall_a_ty(&vnexta, &la);
        let hstep = Expr::apps(
            c("And.right"),
            [inita_a0_ty.clone(), stepsa_ty.clone(), lhruns.clone()],
        );
        let hwf = Expr::apps(vhfair.clone(), [la.clone(), lhruns.clone()]);

        let lrsg = Expr::apps(
            c("TLAsem.LatticeRankSoundGeneral"),
            [
                va_act.clone(),
                vnexta.clone(),
                vpa.clone(),
                vqa.clone(),
                vrho.clone(),
                la.clone(),
                hstep,
                vhasub.clone(),
                vhpstab.clone(),
                vhrank.clone(),
                vhhelp.clone(),
                vhen.clone(),
                hwf,
                ln.clone(),
                lhp.clone(),
            ],
        );
        let pa_an = app(vpa.clone(), app(la.clone(), ln.clone()));
        let inner = lb.lam(lhp_id, BinderInfo::Default, pa_an, lrsg);
        let inner = lb.lam(ln_id, BinderInfo::Default, state(), inner);
        let inner = lb.lam(
            lhruns_id,
            BinderInfo::Default,
            runs_app(&vinita, &vnexta, &la),
            inner,
        );
        lb.lam(la_id, BinderInfo::Default, behavior_ty(), inner)
    };

    // LivenessTransfer InitC ReachInv InitA NextC NextA ref (Lift Pa)(Lift Qa)
    //   hic hri hrs hss hAbsLive b hRunsC
    let body = Expr::apps(
        c("TLAsem.LivenessTransfer"),
        [
            vinitc.clone(),
            vreach.clone(),
            vinita.clone(),
            vnextc.clone(),
            vnexta.clone(),
            vref.clone(),
            lift(&vpa),
            lift(&vqa),
            vhic.clone(),
            vhri.clone(),
            vhrs.clone(),
            vhss.clone(),
            h_abs_live,
            vbv.clone(),
            vhruns.clone(),
        ],
    );

    let value = {
        let mut v = body;
        v = vb.lam(
            vhruns_id,
            BinderInfo::Default,
            runs_app(&vinitc, &vnextc, &vbv),
            v,
        );
        v = vb.lam(vb_id, BinderInfo::Default, behavior_ty(), v);
        v = vb.lam(
            vhfair_id,
            BinderInfo::Default,
            h_abs_fair_ty(&vinita, &vnexta, &va_act),
            v,
        );
        v = vb.lam(
            vhen_id,
            BinderInfo::Default,
            hen_wait_ty(&va_act, &vpa, &vqa),
            v,
        );
        v = vb.lam(
            vhhelp_id,
            BinderInfo::Default,
            hhelp_ty(&va_act, &vpa, &vqa, &vrho),
            v,
        );
        v = vb.lam(
            vhrank_id,
            BinderInfo::Default,
            hrank_ty(&vnexta, &vpa, &vqa, &vrho),
            v,
        );
        v = vb.lam(
            vhpstab_id,
            BinderInfo::Default,
            hpstab_ty(&vnexta, &vpa, &vqa),
            v,
        );
        v = vb.lam(
            vhasub_id,
            BinderInfo::Default,
            hasub_ty(&va_act, &vnexta),
            v,
        );
        v = vb.lam(
            vhss_id,
            BinderInfo::Default,
            h_stepsim_ty(&vnextc, &vnexta, &vref, &vreach),
            v,
        );
        v = vb.lam(
            vhrs_id,
            BinderInfo::Default,
            h_reach_step_ty(&vnextc, &vreach),
            v,
        );
        v = vb.lam(
            vhri_id,
            BinderInfo::Default,
            h_reach_init_ty(&vinitc, &vreach),
            v,
        );
        v = vb.lam(
            vhic_id,
            BinderInfo::Default,
            h_initcorr_ty(&vinitc, &vinita, &vref),
            v,
        );
        v = vb.lam(vref_id, BinderInfo::Default, ref_ty.clone(), v);
        v = vb.lam(vrho_id, BinderInfo::Default, rho_ty.clone(), v);
        v = vb.lam(vqa_id, BinderInfo::Implicit, state_pred_ty(), v);
        v = vb.lam(vpa_id, BinderInfo::Implicit, state_pred_ty(), v);
        v = vb.lam(va_id, BinderInfo::Implicit, action_ty(), v);
        v = vb.lam(vnexta_id, BinderInfo::Implicit, action_ty(), v);
        v = vb.lam(vnextc_id, BinderInfo::Implicit, action_ty(), v);
        v = vb.lam(vinita_id, BinderInfo::Implicit, state_pred_ty(), v);
        v = vb.lam(vreach_id, BinderInfo::Implicit, state_pred_ty(), v);
        v = vb.lam(vinitc_id, BinderInfo::Implicit, state_pred_ty(), v);
        vb.finish(v)
    };

    env.add_decl(Declaration::Theorem {
        name,
        level_params: vec![],
        type_,
        value,
    })
}

/// `∀ n, Or (NextA (a n)(a (succ n))) (Eq (a (succ n))(a n))` — the step
/// component of `Runs InitA NextA a` (used to build `And.right` over an
/// abstract run). Local to the apex chain to avoid touching `semantics.rs`'s
/// private `step_forall_ty`.
fn step_forall_a_ty(nexta: &Expr, a: &Expr) -> Expr {
    let mut sb = B::new();
    let (n_id, n) = sb.fresh();
    let an = app(a.clone(), n.clone());
    let asn = app(a.clone(), nat_succ(n.clone()));
    let stepr = Expr::apps(nexta.clone(), [an.clone(), asn.clone()]);
    let stut = eq_state(asn.clone(), an.clone());
    sb.pi(n_id, BinderInfo::Default, state(), or(stepr, stut))
}

/// Ensure the T·SEM definitions the refinement layer references are present
/// (`Runs`, `RefMap`, `Sat`, `SemBox`, `Lift`, `InductiveInvariantSound`).
fn register_prereqs(env: &mut Environment) -> Result<(), EnvError> {
    crate::semantics::register_tla_semantics(env)?;
    register_ref_map(env)?;
    Ok(())
}

/// Register the entire T·REFINE module (safety slice): `RefMap`, the central
/// transport lemma, and the two consequences. Idempotent.
///
/// REQUIRES: nothing (bootstraps T·SEM via [`crate::semantics::register_tla_semantics`]).
/// ENSURES: on success, `TLAsem.{MappedBehaviorRuns, RefinementMappingSound,
///          PropertyTransfer}` are kernel-checked `Declaration::Theorem`s with
///          `proof_quality == Constructive`.
pub fn register_tla_refinement(env: &mut Environment) -> Result<(), EnvError> {
    register_prereqs(env)?;
    register_mapped_behavior_runs(env)?;
    register_refinement_mapping_sound(env)?;
    register_property_transfer(env)?;
    register_liveness_transfer(env)?;
    register_refined_liveness_from_vcs(env)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::env::{ConstantKind, ProofQuality};
    use clean_kernel::tc::TypeChecker;

    // ── the three theorems are real, Constructive, axiom-free ──────────────

    #[test]
    fn test_refinement_theorems_register_constructive_and_axiom_free() {
        let mut env = Environment::with_prelude();
        register_tla_refinement(&mut env).expect("T·REFINE registers + kernel-checks");

        for name in [
            "TLAsem.MappedBehaviorRuns",
            "TLAsem.RefinementMappingSound",
            "TLAsem.PropertyTransfer",
        ] {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
            assert!(info.value.is_some(), "{name} must retain its proof term");

            // Re-run the kernel type-checker over the stored proof.
            let tc = TypeChecker::with_mode(&env, env.mode());
            tc.check_type(info.value.as_ref().unwrap(), &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));

            // Constructive ⇒ transitive axiom closure ⊆ FOUNDATIONAL.
            let q = env
                .proof_quality(&Name::from_string(name))
                .expect("proof quality computes");
            assert_eq!(
                q,
                ProofQuality::Constructive,
                "{name} must be Constructive (closure ⊆ FOUNDATIONAL), got {q:?}"
            );

            // Stronger: axiom_deps is *empty* (not even Classical.choice).
            let deps: Vec<String> = env
                .axiom_deps(&Name::from_string(name))
                .expect("axiom_deps computes")
                .iter()
                .map(|d| d.to_string())
                .collect();
            assert!(
                deps.is_empty(),
                "{name} must be axiom-free; axiom_deps = {deps:?}"
            );
        }
    }

    /// `RefMap` is a reducible definition; `RefMap ref b ≡ λ i, ref (b i)`,
    /// so `(RefMap ref b) n ≡ ref (b n)` (the pointwise lowering the transport
    /// relies on).
    #[test]
    fn test_refmap_reduces_pointwise() {
        let mut env = Environment::with_prelude();
        register_tla_refinement(&mut env).expect("register");
        let tc = TypeChecker::with_mode(&env, env.mode());

        // ref := Nat.succ ; b := λ i, i ; check (RefMap ref b) 3 ≡ ref (b 3) ≡ 4.
        let refm = c("Nat.succ");
        let id_beh = Expr::lam(BinderInfo::Default, state(), Expr::bvar(0));
        let three = nat_succ(nat_succ(nat_succ(nat_zero())));
        let four = nat_succ(three.clone());
        let mapped_at_3 = app(refmap_app(&refm, &id_beh), three);
        assert!(
            tc.is_def_eq(&mapped_at_3, &four),
            "(RefMap Nat.succ id) 3 must reduce to 4"
        );
    }

    // ── degenerate ref = id: validates the transport skeleton ──────────────

    /// With `ref := λ s, s` the refinement collapses to the identity, and
    /// `MappedBehaviorRuns` instantiates to a self-refinement: every concrete
    /// run is (its own) abstract run. We supply REAL proofs of all four
    /// refinement obligations (init-corr / reach-init / reach-step are `id`-ish;
    /// step-sim is `Or.inl` of the very `NextC` step), instantiate the theorem,
    /// and kernel-check the resulting closed term — the transport skeleton works
    /// end-to-end before we stress it with a non-trivial map.
    #[test]
    fn test_identity_refinement_instance_kernel_checks() {
        let mut env = Environment::with_prelude();
        register_tla_refinement(&mut env).expect("register");
        env.init_true_false().expect("True/False");
        let tc = TypeChecker::with_mode(&env, env.mode());

        // ref := λ s, s
        let ref_id = Expr::lam(BinderInfo::Default, state(), Expr::bvar(0));
        // InitC = InitA := λ s, Eq s 0
        let init_pred = {
            let mut b = B::new();
            let (s_id, s) = b.fresh();
            let body = eq_state(s.clone(), nat_zero());
            b.finish(b.lam(s_id, BinderInfo::Default, state(), body))
        };
        // NextC = NextA := λ s s', Eq s' (succ s)
        let next_act = {
            let mut b = B::new();
            let (s_id, s) = b.fresh();
            let (sp_id, sp) = b.fresh();
            let body = eq_state(sp.clone(), nat_succ(s.clone()));
            let inner = b.lam(sp_id, BinderInfo::Default, state(), body);
            b.finish(b.lam(s_id, BinderInfo::Default, state(), inner))
        };
        // ReachInv := λ _, True
        let reach_true = Expr::lam(BinderInfo::Default, state(), c("True"));

        // init-corr : ∀ c, InitC c → InitA (ref c)   (InitA (ref c) ≡ InitC c) := λ c h, h
        let h_ic = {
            let mut b = B::new();
            let (cc_id, cc) = b.fresh();
            let (h_id, h) = b.fresh();
            let ic_cc = app(init_pred.clone(), cc.clone());
            let r = b.lam(h_id, BinderInfo::Default, ic_cc, h);
            b.finish(b.lam(cc_id, BinderInfo::Default, state(), r))
        };
        // reach-init : ∀ c, InitC c → True := λ c _, True.intro
        let h_ri = {
            let mut b = B::new();
            let (cc_id, cc) = b.fresh();
            let (h_id, _h) = b.fresh();
            let ic_cc = app(init_pred.clone(), cc.clone());
            let r = b.lam(h_id, BinderInfo::Default, ic_cc, c("True.intro"));
            b.finish(b.lam(cc_id, BinderInfo::Default, state(), r))
        };
        // reach-step : ∀ c c', True → NextC c c' → True := λ c c' _ _, True.intro
        let h_rs = {
            let mut b = B::new();
            let (cc_id, cc) = b.fresh();
            let (cp_id, cp) = b.fresh();
            let (h1_id, _h1) = b.fresh();
            let (h2_id, _h2) = b.fresh();
            let nextc_cc = Expr::apps(next_act.clone(), [cc.clone(), cp.clone()]);
            let r = b.lam(h2_id, BinderInfo::Default, nextc_cc, c("True.intro"));
            let r = b.lam(h1_id, BinderInfo::Default, c("True"), r);
            let r = b.lam(cp_id, BinderInfo::Default, state(), r);
            b.finish(b.lam(cc_id, BinderInfo::Default, state(), r))
        };
        // step-sim : ∀ c c', True → NextC c c' → Or (NextA c c') (Eq c' c)
        //   := λ c c' _ hN, Or.inl (NextA c c')(Eq c' c) hN
        //   (NextA (ref c)(ref c') ≡ NextA c c' since ref = id).
        let h_ss = {
            let mut b = B::new();
            let (cc_id, cc) = b.fresh();
            let (cp_id, cp) = b.fresh();
            let (h1_id, _h1) = b.fresh();
            let (hn_id, hn) = b.fresh();
            let nexta = Expr::apps(next_act.clone(), [cc.clone(), cp.clone()]);
            let stut = eq_state(cp.clone(), cc.clone());
            let body = Expr::apps(c("Or.inl"), [nexta.clone(), stut.clone(), hn.clone()]);
            let r = b.lam(hn_id, BinderInfo::Default, nexta, body);
            let r = b.lam(h1_id, BinderInfo::Default, c("True"), r);
            let r = b.lam(cp_id, BinderInfo::Default, state(), r);
            b.finish(b.lam(cc_id, BinderInfo::Default, state(), r))
        };

        // MappedBehaviorRuns InitC ReachInv InitA NextC NextA ref h_ic h_ri h_rs h_ss
        //   : ∀ b, Runs InitC NextC b → Runs InitA NextA (RefMap ref b)
        let instance = Expr::apps(
            c("TLAsem.MappedBehaviorRuns"),
            [
                init_pred.clone(),
                reach_true.clone(),
                init_pred.clone(),
                next_act.clone(),
                next_act.clone(),
                ref_id.clone(),
                h_ic,
                h_ri,
                h_rs,
                h_ss,
            ],
        );
        let inst_ty = tc
            .infer_type(&instance)
            .expect("identity-refinement instance must kernel-check");
        // The specialized type must be a real ∀b, Runs … → Runs … (a Pi), not True.
        assert!(
            matches!(inst_ty.kind(), clean_kernel::expr::ExprKind::Pi(..)),
            "instantiated MappedBehaviorRuns must be a real ∀-statement, got {:?}",
            inst_ty.kind()
        );
        assert!(
            !tc.is_def_eq(&inst_ty, &c("True")),
            "identity-refinement instance type must not collapse to True"
        );
    }

    // ── real ref ≠ id: a 2-place buffered counter refining a 1-place one ───

    /// **The directive's headline instance.** A 2-place *buffered* counter
    /// refines a 1-place abstract counter under `ref := Nat.div2` (a genuine,
    /// provably non-identity projection): the concrete state `c` encodes
    /// `(value, phase)` as `c = 2·value + phase`, so `ref c = Nat.div2 c =
    /// value`. A concrete step either **flushes** the buffer — `div2 c' =
    /// succ (div2 c)`, a real abstract `NextA` increment — or **fills** it —
    /// `div2 c' = div2 c`, an abstract *stutter*. We discharge all four
    /// refinement obligations with REAL kernel-checked proof terms:
    ///   * `NextC c c' := (div2 c' = succ (div2 c)) ∨ (div2 c' = div2 c)` makes
    ///     step-simulation-or-stutter the **identity** on the disjunction
    ///     (`λ c c' _ hN, hN`) — yet it genuinely references `NextC`'s content,
    ///     so it is not vacuous;
    ///   * init-correspondence is `id` (`InitA (div2 c) ≡ InitC c`);
    ///   * `ReachInv := λ _, True` is trivially inductive.
    ///
    /// Instantiating `MappedBehaviorRuns` yields a closed, kernel-checked term
    /// `∀ b, Runs InitC NextC b → Runs InitA NextA (RefMap Nat.div2 b)` — a real
    /// `ref ≠ id` refinement with every obligation discharged in-kernel.
    #[test]
    fn test_buffered_counter_refinement_instance_kernel_checks() {
        let mut env = Environment::with_prelude();
        register_tla_refinement(&mut env).expect("register");
        env.init_true_false().expect("True/False");
        let tc = TypeChecker::with_mode(&env, env.mode());

        // ref := Nat.div2  (≠ id: div2 1 = 0 ≠ 1, see the dedicated test below)
        let div2 = c("Nat.div2");
        // NextA := λ a a', Eq a' (succ a)
        let nexta = {
            let mut b = B::new();
            let (a_id, a) = b.fresh();
            let (ap_id, ap) = b.fresh();
            let body = eq_state(ap.clone(), nat_succ(a.clone()));
            let inner = b.lam(ap_id, BinderInfo::Default, state(), body);
            b.finish(b.lam(a_id, BinderInfo::Default, state(), inner))
        };
        // NextC := λ c c', Or (Eq (div2 c')(succ (div2 c))) (Eq (div2 c')(div2 c))
        let nextc = {
            let mut b = B::new();
            let (c_id, cc) = b.fresh();
            let (cp_id, cp) = b.fresh();
            let dvc = app(div2.clone(), cc.clone());
            let dvcp = app(div2.clone(), cp.clone());
            let flush = eq_state(dvcp.clone(), nat_succ(dvc.clone()));
            let fill = eq_state(dvcp.clone(), dvc.clone());
            let body = or(flush, fill);
            let inner = b.lam(cp_id, BinderInfo::Default, state(), body);
            b.finish(b.lam(c_id, BinderInfo::Default, state(), inner))
        };
        // InitC := λ c, Eq (div2 c) 0 ; InitA := λ a, Eq a 0
        let initc = {
            let mut b = B::new();
            let (c_id, cc) = b.fresh();
            let body = eq_state(app(div2.clone(), cc.clone()), nat_zero());
            b.finish(b.lam(c_id, BinderInfo::Default, state(), body))
        };
        let inita = {
            let mut b = B::new();
            let (a_id, a) = b.fresh();
            let body = eq_state(a.clone(), nat_zero());
            b.finish(b.lam(a_id, BinderInfo::Default, state(), body))
        };
        let reach_true = Expr::lam(BinderInfo::Default, state(), c("True"));

        // init-corr : ∀ c, InitC c → InitA (div2 c)
        //   InitA (div2 c) ≡ Eq (div2 c) 0 ≡ InitC c, so := λ c h, h
        let h_ic = {
            let mut b = B::new();
            let (cc_id, cc) = b.fresh();
            let (h_id, h) = b.fresh();
            let ic_cc = app(initc.clone(), cc.clone());
            let r = b.lam(h_id, BinderInfo::Default, ic_cc, h);
            b.finish(b.lam(cc_id, BinderInfo::Default, state(), r))
        };
        // reach-init : ∀ c, InitC c → True := λ c _, True.intro
        let h_ri = {
            let mut b = B::new();
            let (cc_id, cc) = b.fresh();
            let (h_id, _h) = b.fresh();
            let ic_cc = app(initc.clone(), cc.clone());
            let r = b.lam(h_id, BinderInfo::Default, ic_cc, c("True.intro"));
            b.finish(b.lam(cc_id, BinderInfo::Default, state(), r))
        };
        // reach-step : ∀ c c', True → NextC c c' → True := λ c c' _ _, True.intro
        let h_rs = {
            let mut b = B::new();
            let (cc_id, cc) = b.fresh();
            let (cp_id, cp) = b.fresh();
            let (h1_id, _h1) = b.fresh();
            let (h2_id, _h2) = b.fresh();
            let nextc_cc = Expr::apps(nextc.clone(), [cc.clone(), cp.clone()]);
            let r = b.lam(h2_id, BinderInfo::Default, nextc_cc, c("True.intro"));
            let r = b.lam(h1_id, BinderInfo::Default, c("True"), r);
            let r = b.lam(cp_id, BinderInfo::Default, state(), r);
            b.finish(b.lam(cc_id, BinderInfo::Default, state(), r))
        };
        // step-sim : ∀ c c', True → NextC c c'
        //              → Or (NextA (div2 c)(div2 c')) (Eq (div2 c')(div2 c))
        //   NextA (div2 c)(div2 c') ≡ Eq (div2 c')(succ (div2 c)), and
        //   NextC c c' IS exactly Or (Eq (div2 c')(succ (div2 c)))(Eq (div2 c')(div2 c)),
        //   so the goal is def-eq to NextC c c' and step-sim is the identity on it:
        //     := λ c c' _ hN, hN
        let h_ss = {
            let mut b = B::new();
            let (cc_id, cc) = b.fresh();
            let (cp_id, cp) = b.fresh();
            let (h1_id, _h1) = b.fresh();
            let (hn_id, hn) = b.fresh();
            let nextc_cc = Expr::apps(nextc.clone(), [cc.clone(), cp.clone()]);
            let r = b.lam(hn_id, BinderInfo::Default, nextc_cc, hn);
            let r = b.lam(h1_id, BinderInfo::Default, c("True"), r);
            let r = b.lam(cp_id, BinderInfo::Default, state(), r);
            b.finish(b.lam(cc_id, BinderInfo::Default, state(), r))
        };

        let instance = Expr::apps(
            c("TLAsem.MappedBehaviorRuns"),
            [
                initc.clone(),
                reach_true.clone(),
                inita.clone(),
                nextc.clone(),
                nexta.clone(),
                div2.clone(),
                h_ic,
                h_ri,
                h_rs,
                h_ss,
            ],
        );
        let inst_ty = tc
            .infer_type(&instance)
            .expect("buffered-counter (ref = Nat.div2) refinement instance must kernel-check");
        assert!(
            matches!(inst_ty.kind(), clean_kernel::expr::ExprKind::Pi(..)),
            "instantiated statement must be ∀ b, Runs … → Runs …, got {:?}",
            inst_ty.kind()
        );
        assert!(
            !tc.is_def_eq(&inst_ty, &c("True")),
            "buffered-counter refinement instance type must not collapse to True"
        );
    }

    /// The refinement map `Nat.div2` used by the buffered counter is genuinely
    /// `≠ id`: `div2 1 ≡ 0 ≠ 1` — so the instance above is a real `ref ≠ id`
    /// refinement, not the degenerate identity case in disguise.
    #[test]
    fn test_buffered_counter_ref_is_not_identity() {
        let env = Environment::with_prelude();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let one = nat_succ(nat_zero());
        let div2_one = app(c("Nat.div2"), one.clone());
        // div2 1 ≡ 0
        assert!(
            tc.is_def_eq(&div2_one, &nat_zero()),
            "Nat.div2 1 must reduce to 0 (buffer-fill: value held)"
        );
        // div2 1 ≢ 1 (so ref ≠ id at input 1)
        assert!(
            !tc.is_def_eq(&div2_one, &one),
            "Nat.div2 1 must NOT equal 1 — the map is genuinely non-identity"
        );
        // div2 2 ≡ 1 (buffer-flush: value advanced)
        let two = nat_succ(one.clone());
        let div2_two = app(c("Nat.div2"), two);
        assert!(
            tc.is_def_eq(&div2_two, &one),
            "Nat.div2 2 must reduce to 1 (buffer-flush: value advances)"
        );
    }

    // ── non-vacuity of the transferred □-property ──────────────────────────

    /// Non-vacuity: the conclusion `Sat (RefMap ref b) (SemBox (Lift InvA))` of
    /// `RefinementMappingSound`/`PropertyTransfer` is NOT definitionally `True`.
    /// We instantiate the (implicit) `InvA` with the always-false predicate and
    /// confirm the mapped box-invariant reduces to a genuine `∀ n, False` over
    /// the trace — so a transferred invariant says something.
    #[test]
    fn test_transferred_box_invariant_is_not_vacuous() {
        let mut env = Environment::with_prelude();
        register_tla_refinement(&mut env).expect("register");
        env.init_true_false().expect("True/False");
        let tc = TypeChecker::with_mode(&env, env.mode());

        // ref := Nat.succ ; b := λ _, 0 ; InvA := λ _, False
        let refm = c("Nat.succ");
        let zero_beh = Expr::lam(BinderInfo::Default, state(), nat_zero());
        let false_pred = Expr::lam(BinderInfo::Default, state(), c("False"));

        // Sat (RefMap ref b) (SemBox (Lift InvA))
        let concl = sat_mapped_box_inv(&refm, &zero_beh, &false_pred);
        let ty = tc.infer_type(&concl).expect("concl is a Prop");
        assert_eq!(ty, Expr::prop());

        // reduces to ∀ n, False (RefMap/Sat/SemBox/Lift/drop all reducible;
        // InvA (ref ((RefMap ref b) (n+0))) ≡ False).
        let forall_false = Expr::pi(BinderInfo::Default, state(), c("False"));
        assert!(
            tc.is_def_eq(&concl, &forall_false),
            "Sat (RefMap ref (const-0)) (□ (Lift λ_,False)) must reduce to ∀ n, False"
        );
        assert!(
            !tc.is_def_eq(&concl, &c("True")),
            "transferred box-invariant must not collapse to True"
        );
    }

    // ── anti-masquerade: the proofs reference the REAL substrate ────────────

    /// `MappedBehaviorRuns`'s proof term genuinely runs the inductive machinery
    /// — `Nat.rec` (the `ReachInv` induction), `Or.rec` (the per-step
    /// case-split), `Eq.subst`/`Eq.symm` (the stutter-congruence) — and is NOT a
    /// degenerate term wrapping an axiom.
    #[test]
    fn test_mapped_behavior_runs_uses_real_induction() {
        let mut env = Environment::with_prelude();
        register_tla_refinement(&mut env).expect("register");
        let info = env
            .get_const(&Name::from_string("TLAsem.MappedBehaviorRuns"))
            .expect("registered");
        let value = info.value.as_ref().expect("has proof value");
        let names = const_names(value);
        for required in ["Nat.rec", "Or.rec", "Eq.subst", "Eq.symm", "And.intro"] {
            assert!(
                names.contains(required),
                "MappedBehaviorRuns proof must reference {required}; refs = {names:?}"
            );
        }
        // and it must NOT reference any Axiom-flavored stand-in.
        assert!(
            !names
                .iter()
                .any(|n| n.contains("sorry") || n.contains("axiom")),
            "proof must not reference a stand-in axiom; refs = {names:?}"
        );
    }

    /// `RefinementMappingSound`'s proof genuinely COMPOSES the transport lemma
    /// `MappedBehaviorRuns` with the safety keystone `InductiveInvariantSound`
    /// — not an axiom, not a re-proof.
    #[test]
    fn test_refinement_mapping_sound_composes_substrate() {
        let mut env = Environment::with_prelude();
        register_tla_refinement(&mut env).expect("register");
        let info = env
            .get_const(&Name::from_string("TLAsem.RefinementMappingSound"))
            .expect("registered");
        let names = const_names(info.value.as_ref().expect("value"));
        for required in [
            "TLAsem.MappedBehaviorRuns",
            "TLAsem.InductiveInvariantSound",
        ] {
            assert!(
                names.contains(required),
                "RefinementMappingSound must compose {required}; refs = {names:?}"
            );
        }
    }

    /// `PropertyTransfer`'s proof genuinely applies the transport lemma
    /// `MappedBehaviorRuns` to the supplied abstract □-property.
    #[test]
    fn test_property_transfer_uses_transport_lemma() {
        let mut env = Environment::with_prelude();
        register_tla_refinement(&mut env).expect("register");
        let info = env
            .get_const(&Name::from_string("TLAsem.PropertyTransfer"))
            .expect("registered");
        let names = const_names(info.value.as_ref().expect("value"));
        assert!(
            names.contains("TLAsem.MappedBehaviorRuns"),
            "PropertyTransfer must apply MappedBehaviorRuns; refs = {names:?}"
        );
    }

    /// Idempotent: re-registering does not error or duplicate.
    #[test]
    fn test_registration_is_idempotent() {
        let mut env = Environment::with_prelude();
        register_tla_refinement(&mut env).expect("first");
        register_tla_refinement(&mut env).expect("second (idempotent)");
        register_mapped_behavior_runs(&mut env).expect("idempotent single");
    }

    /// On a bare `Environment::new()` (no prelude) the safety-only refinement
    /// layer still registers and kernel-checks — `MappedBehaviorRuns` /
    /// `RefinementMappingSound` / `PropertyTransfer` use only `Nat.rec`/`Or`/
    /// `Eq`/`And`, never `Acc.rec`, so they do not need `with_prelude()`.
    #[test]
    fn test_refinement_registers_on_bare_env() {
        let mut env = Environment::new();
        register_tla_refinement(&mut env).expect("T·REFINE registers on a bare env");
        for n in [
            "TLAsem.MappedBehaviorRuns",
            "TLAsem.RefinementMappingSound",
            "TLAsem.PropertyTransfer",
        ] {
            assert!(
                env.get_const(&Name::from_string(n)).is_some(),
                "{n} must register on a bare (non-prelude) env"
            );
        }
    }

    // ════════════════════════════════════════════════════════════════════════
    //  THE FAIRNESS-PRESERVING REFINEMENT APEX (property-transfer form) — tests.
    // ════════════════════════════════════════════════════════════════════════

    /// Both apex theorems register, are real `Theorem`s, re-kernel-check, are
    /// `Constructive` (closure ⊆ FOUNDATIONAL), and have an **empty** axiom
    /// closure (`axiom_deps == []` — not even `Classical.choice`).
    #[test]
    fn test_apex_liveness_theorems_constructive_and_axiom_free() {
        let mut env = Environment::with_prelude();
        register_tla_refinement(&mut env).expect("T·REFINE (apex) registers + kernel-checks");

        for name in ["TLAsem.LivenessTransfer", "TLAsem.RefinedLivenessFromVCs"] {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
            assert!(info.value.is_some(), "{name} must retain its proof term");

            let tc = TypeChecker::with_mode(&env, env.mode());
            tc.check_type(info.value.as_ref().unwrap(), &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));

            let q = env
                .proof_quality(&Name::from_string(name))
                .expect("proof quality computes");
            assert_eq!(
                q,
                ProofQuality::Constructive,
                "{name} must be Constructive (closure ⊆ FOUNDATIONAL), got {q:?}"
            );

            let deps: Vec<String> = env
                .axiom_deps(&Name::from_string(name))
                .expect("axiom_deps computes")
                .iter()
                .map(|d| d.to_string())
                .collect();
            assert!(
                deps.is_empty(),
                "{name} must be axiom-free; axiom_deps = {deps:?}"
            );
        }
    }

    /// Anti-masquerade: `LivenessTransfer`'s proof genuinely applies the
    /// transport lemma `MappedBehaviorRuns` to the supplied abstract liveness
    /// property — the liveness analogue of `PropertyTransfer`, NOT an axiom.
    #[test]
    fn test_liveness_transfer_uses_transport_lemma() {
        let mut env = Environment::with_prelude();
        register_tla_refinement(&mut env).expect("register");
        let info = env
            .get_const(&Name::from_string("TLAsem.LivenessTransfer"))
            .expect("registered");
        let names = const_names(info.value.as_ref().expect("value"));
        assert!(
            names.contains("TLAsem.MappedBehaviorRuns"),
            "LivenessTransfer must apply MappedBehaviorRuns; refs = {names:?}"
        );
        assert!(
            !names
                .iter()
                .any(|n| n.contains("sorry") || n.contains("axiom")),
            "LivenessTransfer must not reference a stand-in axiom; refs = {names:?}"
        );
    }

    /// Anti-masquerade for the blow-away chain: `RefinedLivenessFromVCs`
    /// genuinely COMPOSES the abstract liveness metatheorem
    /// `LatticeRankSoundGeneral` (deriving `Pa ⇝ Qa` from the raw WF1 VCs) with
    /// the transfer theorem `LivenessTransfer` (carrying it across the map) —
    /// and uses NO `sorryAx`/`Classical.choice` stand-in.
    #[test]
    fn test_refined_liveness_from_vcs_composes_substrate() {
        let mut env = Environment::with_prelude();
        register_tla_refinement(&mut env).expect("register");
        let info = env
            .get_const(&Name::from_string("TLAsem.RefinedLivenessFromVCs"))
            .expect("registered");
        let names = const_names(info.value.as_ref().expect("value"));
        for required in ["TLAsem.LivenessTransfer", "TLAsem.LatticeRankSoundGeneral"] {
            assert!(
                names.contains(required),
                "RefinedLivenessFromVCs must compose {required}; refs = {names:?}"
            );
        }
        for forbidden in ["sorryAx", "Classical.choice"] {
            assert!(
                !names.iter().any(|n| n.contains(forbidden)),
                "RefinedLivenessFromVCs must not use {forbidden}; refs = {names:?}"
            );
        }
    }

    /// **Non-vacuity** (directive item 3): the transferred `LeadsTo` is NOT
    /// definitionally a trivial truth. `Sat (RefMap ref b)(LeadsTo (Lift Pa)
    /// (Lift Qa))` reduces to `∀ n, Pa(ref(b n)) → ∃ m, Qa(ref(b(n+m)))`.
    /// With `ref := Nat.div2`, `b := λ_,0`, `Pa := λ_,True`, `Qa := λ_,False`
    /// it is `∀ n, True → ∃ m, False` — a genuine Prop, **not** `True`.
    #[test]
    fn test_transferred_leadsto_is_not_vacuous() {
        let mut env = Environment::with_prelude();
        register_tla_refinement(&mut env).expect("register");
        env.init_true_false().expect("True/False");
        let tc = TypeChecker::with_mode(&env, env.mode());

        let div2 = c("Nat.div2");
        let zero_beh = Expr::lam(BinderInfo::Default, state(), nat_zero());
        let p_true = Expr::lam(BinderInfo::Default, state(), c("True"));
        let q_false = Expr::lam(BinderInfo::Default, state(), c("False"));

        let concl = sat_mapped_leadsto(&div2, &zero_beh, &lift(&p_true), &lift(&q_false));
        let ty = tc.infer_type(&concl).expect("conclusion is a Prop");
        assert_eq!(ty, Expr::prop());

        let unfolded = {
            let mut nb = B::new();
            let (n_id, _n) = nb.fresh();
            let ex_false = {
                let mut mb = B::new();
                let (m_id, _m) = mb.fresh();
                let pred = mb.lam(m_id, BinderInfo::Default, state(), c("False"));
                Expr::apps(
                    Expr::const_(
                        Name::from_string("Exists"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [state(), pred],
                )
            };
            let body = Expr::arrow(c("True"), ex_false);
            nb.pi(n_id, BinderInfo::Default, state(), nb.finish(body))
        };
        assert!(
            tc.is_def_eq(&concl, &unfolded),
            "transferred LeadsTo must reduce to ∀ n, Pa(…) → ∃ m, Qa(…) (here ∀n,True→∃m,False)"
        );
        assert!(
            !tc.is_def_eq(&concl, &c("True")),
            "transferred LeadsTo must NOT collapse to True"
        );
    }

    /// **Real `ref ≠ id` instance — `LivenessTransfer` (directive item 3).**
    /// Buffered 2-place ⊑ 1-place counter under `ref := Nat.div2`
    /// (`div2 1 = 0 ≠ 1`): REAL kernel-checked proofs of the four refinement
    /// obligations, partially applied at `Pa := Lift (λ_,True)`,
    /// `Qa := Lift (λ_,False)`. The residual is a genuine implication
    /// `(∀a, Runs InitA NextA a → Sat a (Pa⇝Qa)) → ∀b, Runs InitC NextC b →
    /// Sat (RefMap Nat.div2 b)(Pa⇝Qa)` — abstract liveness transferred to the
    /// mapped concrete behavior over a non-identity map.
    #[test]
    fn test_buffered_counter_liveness_transfer_instance_kernel_checks() {
        let mut env = Environment::with_prelude();
        register_tla_refinement(&mut env).expect("register");
        env.init_true_false().expect("True/False");
        let tc = TypeChecker::with_mode(&env, env.mode());

        let div2 = c("Nat.div2");
        let nexta = {
            let mut b = B::new();
            let (a_id, a) = b.fresh();
            let (ap_id, ap) = b.fresh();
            let body = eq_state(ap.clone(), nat_succ(a.clone()));
            let inner = b.lam(ap_id, BinderInfo::Default, state(), body);
            b.finish(b.lam(a_id, BinderInfo::Default, state(), inner))
        };
        let nextc = {
            let mut b = B::new();
            let (c_id, cc) = b.fresh();
            let (cp_id, cp) = b.fresh();
            let dvc = app(div2.clone(), cc.clone());
            let dvcp = app(div2.clone(), cp.clone());
            let flush = eq_state(dvcp.clone(), nat_succ(dvc.clone()));
            let fill = eq_state(dvcp.clone(), dvc.clone());
            let inner = b.lam(cp_id, BinderInfo::Default, state(), or(flush, fill));
            b.finish(b.lam(c_id, BinderInfo::Default, state(), inner))
        };
        let initc = {
            let mut b = B::new();
            let (c_id, cc) = b.fresh();
            let body = eq_state(app(div2.clone(), cc.clone()), nat_zero());
            b.finish(b.lam(c_id, BinderInfo::Default, state(), body))
        };
        let inita = {
            let mut b = B::new();
            let (a_id, a) = b.fresh();
            let body = eq_state(a.clone(), nat_zero());
            b.finish(b.lam(a_id, BinderInfo::Default, state(), body))
        };
        let reach_true = Expr::lam(BinderInfo::Default, state(), c("True"));

        let h_ic = {
            let mut b = B::new();
            let (cc_id, cc) = b.fresh();
            let (h_id, h) = b.fresh();
            let ic_cc = app(initc.clone(), cc.clone());
            let r = b.lam(h_id, BinderInfo::Default, ic_cc, h);
            b.finish(b.lam(cc_id, BinderInfo::Default, state(), r))
        };
        let h_ri = {
            let mut b = B::new();
            let (cc_id, cc) = b.fresh();
            let (h_id, _h) = b.fresh();
            let ic_cc = app(initc.clone(), cc.clone());
            let r = b.lam(h_id, BinderInfo::Default, ic_cc, c("True.intro"));
            b.finish(b.lam(cc_id, BinderInfo::Default, state(), r))
        };
        let h_rs = {
            let mut b = B::new();
            let (cc_id, cc) = b.fresh();
            let (cp_id, cp) = b.fresh();
            let (h1_id, _h1) = b.fresh();
            let (h2_id, _h2) = b.fresh();
            let nextc_cc = Expr::apps(nextc.clone(), [cc.clone(), cp.clone()]);
            let r = b.lam(h2_id, BinderInfo::Default, nextc_cc, c("True.intro"));
            let r = b.lam(h1_id, BinderInfo::Default, c("True"), r);
            let r = b.lam(cp_id, BinderInfo::Default, state(), r);
            b.finish(b.lam(cc_id, BinderInfo::Default, state(), r))
        };
        let h_ss = {
            let mut b = B::new();
            let (cc_id, cc) = b.fresh();
            let (cp_id, cp) = b.fresh();
            let (h1_id, _h1) = b.fresh();
            let (hn_id, hn) = b.fresh();
            let nextc_cc = Expr::apps(nextc.clone(), [cc.clone(), cp.clone()]);
            let r = b.lam(hn_id, BinderInfo::Default, nextc_cc, hn);
            let r = b.lam(h1_id, BinderInfo::Default, c("True"), r);
            let r = b.lam(cp_id, BinderInfo::Default, state(), r);
            b.finish(b.lam(cc_id, BinderInfo::Default, state(), r))
        };

        let pa = lift(&Expr::lam(BinderInfo::Default, state(), c("True")));
        let qa = lift(&Expr::lam(BinderInfo::Default, state(), c("False")));

        let instance = Expr::apps(
            c("TLAsem.LivenessTransfer"),
            [
                initc.clone(),
                reach_true.clone(),
                inita.clone(),
                nextc.clone(),
                nexta.clone(),
                div2.clone(),
                pa.clone(),
                qa.clone(),
                h_ic,
                h_ri,
                h_rs,
                h_ss,
            ],
        );
        let inst_ty = tc.infer_type(&instance).expect(
            "buffered-counter (ref = Nat.div2) LivenessTransfer instance must kernel-check",
        );
        assert!(
            matches!(inst_ty.kind(), clean_kernel::expr::ExprKind::Pi(..)),
            "instantiated LivenessTransfer must be a real ∀/→ statement, got {:?}",
            inst_ty.kind()
        );
        assert!(
            !tc.is_def_eq(&inst_ty, &c("True")),
            "buffered-counter LivenessTransfer instance type must not collapse to True"
        );
    }

    /// **Real `ref ≠ id` instance — `RefinedLivenessFromVCs` (the blow-away
    /// chain).** Partially apply the apex theorem at the buffered-counter
    /// refinement (`ref := Nat.div2`) with REAL refinement-obligation proofs;
    /// the residual still demands the five abstract WF1 VCs + the abstract
    /// fairness premise and concludes `Sat (RefMap Nat.div2 b)(Lift Pa ⇝ Lift Qa)`
    /// — a genuine non-`True` Pi deriving CONCRETE-mapped liveness from the
    /// ABSTRACT spec's verification conditions, over a non-identity map.
    #[test]
    fn test_buffered_counter_refined_liveness_from_vcs_instance_kernel_checks() {
        let mut env = Environment::with_prelude();
        register_tla_refinement(&mut env).expect("register");
        env.init_true_false().expect("True/False");
        let tc = TypeChecker::with_mode(&env, env.mode());

        let div2 = c("Nat.div2");
        let nexta = {
            let mut b = B::new();
            let (a_id, a) = b.fresh();
            let (ap_id, ap) = b.fresh();
            let body = eq_state(ap.clone(), nat_succ(a.clone()));
            let inner = b.lam(ap_id, BinderInfo::Default, state(), body);
            b.finish(b.lam(a_id, BinderInfo::Default, state(), inner))
        };
        let nextc = {
            let mut b = B::new();
            let (c_id, cc) = b.fresh();
            let (cp_id, cp) = b.fresh();
            let dvc = app(div2.clone(), cc.clone());
            let dvcp = app(div2.clone(), cp.clone());
            let flush = eq_state(dvcp.clone(), nat_succ(dvc.clone()));
            let fill = eq_state(dvcp.clone(), dvc.clone());
            let inner = b.lam(cp_id, BinderInfo::Default, state(), or(flush, fill));
            b.finish(b.lam(c_id, BinderInfo::Default, state(), inner))
        };
        let initc = {
            let mut b = B::new();
            let (c_id, cc) = b.fresh();
            let body = eq_state(app(div2.clone(), cc.clone()), nat_zero());
            b.finish(b.lam(c_id, BinderInfo::Default, state(), body))
        };
        let inita = {
            let mut b = B::new();
            let (a_id, a) = b.fresh();
            let body = eq_state(a.clone(), nat_zero());
            b.finish(b.lam(a_id, BinderInfo::Default, state(), body))
        };
        let reach_true = Expr::lam(BinderInfo::Default, state(), c("True"));
        let a_act = nexta.clone();

        let h_ic = {
            let mut b = B::new();
            let (cc_id, cc) = b.fresh();
            let (h_id, h) = b.fresh();
            let ic_cc = app(initc.clone(), cc.clone());
            let r = b.lam(h_id, BinderInfo::Default, ic_cc, h);
            b.finish(b.lam(cc_id, BinderInfo::Default, state(), r))
        };
        let h_ri = {
            let mut b = B::new();
            let (cc_id, cc) = b.fresh();
            let (h_id, _h) = b.fresh();
            let ic_cc = app(initc.clone(), cc.clone());
            let r = b.lam(h_id, BinderInfo::Default, ic_cc, c("True.intro"));
            b.finish(b.lam(cc_id, BinderInfo::Default, state(), r))
        };
        let h_rs = {
            let mut b = B::new();
            let (cc_id, cc) = b.fresh();
            let (cp_id, cp) = b.fresh();
            let (h1_id, _h1) = b.fresh();
            let (h2_id, _h2) = b.fresh();
            let nextc_cc = Expr::apps(nextc.clone(), [cc.clone(), cp.clone()]);
            let r = b.lam(h2_id, BinderInfo::Default, nextc_cc, c("True.intro"));
            let r = b.lam(h1_id, BinderInfo::Default, c("True"), r);
            let r = b.lam(cp_id, BinderInfo::Default, state(), r);
            b.finish(b.lam(cc_id, BinderInfo::Default, state(), r))
        };
        let h_ss = {
            let mut b = B::new();
            let (cc_id, cc) = b.fresh();
            let (cp_id, cp) = b.fresh();
            let (h1_id, _h1) = b.fresh();
            let (hn_id, hn) = b.fresh();
            let nextc_cc = Expr::apps(nextc.clone(), [cc.clone(), cp.clone()]);
            let r = b.lam(hn_id, BinderInfo::Default, nextc_cc, hn);
            let r = b.lam(h1_id, BinderInfo::Default, c("True"), r);
            let r = b.lam(cp_id, BinderInfo::Default, state(), r);
            b.finish(b.lam(cc_id, BinderInfo::Default, state(), r))
        };

        let pa = Expr::lam(BinderInfo::Default, state(), c("True"));
        let qa = Expr::lam(BinderInfo::Default, state(), c("False"));
        let rho = Expr::lam(BinderInfo::Default, state(), Expr::bvar(0));

        let instance = Expr::apps(
            c("TLAsem.RefinedLivenessFromVCs"),
            [
                initc.clone(),
                reach_true.clone(),
                inita.clone(),
                nextc.clone(),
                nexta.clone(),
                a_act.clone(),
                pa.clone(),
                qa.clone(),
                rho.clone(),
                div2.clone(),
                h_ic,
                h_ri,
                h_rs,
                h_ss,
            ],
        );
        let inst_ty = tc.infer_type(&instance).expect(
            "buffered-counter (ref = Nat.div2) RefinedLivenessFromVCs instance must kernel-check",
        );
        assert!(
            matches!(inst_ty.kind(), clean_kernel::expr::ExprKind::Pi(..)),
            "instantiated RefinedLivenessFromVCs must be a real ∀/→ statement, got {:?}",
            inst_ty.kind()
        );
        assert!(
            !tc.is_def_eq(&inst_ty, &c("True")),
            "buffered-counter RefinedLivenessFromVCs instance type must not collapse to True"
        );
    }

    /// `RefinedLivenessFromVCs` is correctly GATED on the liveness prelude: on a
    /// bare `Environment::new()` (no `Acc.rec`) `LatticeRankSoundGeneral` is
    /// absent, so the apex chain is skipped — but `LivenessTransfer` (needs only
    /// `MappedBehaviorRuns`) still registers. The safety slice is unaffected.
    #[test]
    fn test_apex_gating_on_bare_env() {
        let mut env = Environment::new();
        register_tla_refinement(&mut env).expect("registers on bare env");
        assert!(
            env.get_const(&Name::from_string("TLAsem.LivenessTransfer"))
                .is_some(),
            "LivenessTransfer registers on a bare env (needs only MappedBehaviorRuns)"
        );
        assert!(
            env.get_const(&Name::from_string("TLAsem.RefinedLivenessFromVCs"))
                .is_none(),
            "RefinedLivenessFromVCs is correctly skipped on a bare env (no LatticeRankSoundGeneral)"
        );
    }

    /// Collect every `Const` name appearing in a term.
    fn const_names(e: &Expr) -> std::collections::HashSet<String> {
        use clean_kernel::expr::ExprKind;
        fn go(e: &Expr, out: &mut std::collections::HashSet<String>) {
            match e.kind() {
                ExprKind::Const(n, _) => {
                    out.insert(n.to_string());
                }
                ExprKind::App(f, a) => {
                    go(f, out);
                    go(a, out);
                }
                ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                    go(t, out);
                    go(b, out);
                }
                _ => {}
            }
        }
        let mut s = std::collections::HashSet::new();
        go(e, &mut s);
        s
    }
}
