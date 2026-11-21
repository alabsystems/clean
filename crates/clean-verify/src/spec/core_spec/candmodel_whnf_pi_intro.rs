// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **`pi_intro` at `RedWStep` — the quantifier-order gap, made checkable.**
//!
//! Derivation and scope in
//! `designs/2026-09-18-is-candmodel-uninhabited.md` §3l. In short: the field's
//! premise gives the pointwise property only for `a` IN THE CANDIDATE, while the
//! conclusion's clause at index `n+1` demands it for every `x` with
//! `RedW n A x` — one index, a strictly WEAKER condition. So the premise cannot
//! be invoked where the conclusion needs it, and the gap is an order of
//! quantifiers rather than a missing fact.
//!
//! The witness, with both sides computing because `sort 0` is index-free:
//!
//! ```text
//! A := pi (sort 0) (sort 0)     B := sort 0     f := OMEGA_LAM
//! ```
//!
//! * premise — `whnf_acc (app OMEGA_LAM a)` for candidate `a`; HOLDS, because
//!   `app OMEGA_LAM a` beta-steps to `app a a` and `a`'s own candidate property
//!   delivers that;
//! * conclusion at index one — `forall x, whnf_acc x -> whnf_acc (app OMEGA_LAM x)`;
//!   FAILS at `x := OMEGA_LAM`, by `self_app_loop_not_whnf_acc`.
//!
//! **`omega_app_acc_of_candidate` is the whole cost**, and the beta case is why
//! it is a proof rather than a transfer: unlike
//! `redw_cr3_pointwise_at_a_nondependent_codomain`, there is no `Neutral`
//! premise to kill it with, because `OMEGA_LAM` IS a `lam`. `whnf_step_app_inv`
//! hands back a universally quantified `A0`/`body` with only
//! `Eq KExpr OMEGA_LAM (lam A0 body)`, and this tree has no `lam` injectivity —
//! so `lamBody`, a `KExpr.rec` projection, recovers the body by congruence
//! instead.
//!
//! **Carriers, named rather than hidden.** Three hypotheses are assumed, on the
//! same footing as `redabstraction_blind`'s: ι and δ cannot reduce a
//! `lam`-headed application, and `OMEGA_LAM` has no `beta_reduces` successor.
//! All three are true and none is discharged here, so a landing refutation is
//! CONDITIONAL — the same relationship `pi_elim_blind_refuted` has to
//! `pi_elim_blind_refuted_uncond`. Discharging them is the follow-up.
//!
//! Everything here is SCRATCH and unwired.

use crate::spec::Specification;

#[cfg(test)]
const OM: &str = "(KExpr.lam (KExpr.bvar Nat.zero) \
                  (KExpr.app (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)))";
#[cfg(test)]
const OM_BODY: &str = "(KExpr.app (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero))";

impl Specification {
    /// The `lamBody` projection, the SN obligation, and the refutation.
    #[cfg(test)]
    pub(super) fn candmodel_whnf_pi_intro_refutation_sources() -> Vec<(String, String)> {
        let s0 = "(KExpr.sort Level.zero)";
        let pia = format!("(KExpr.pi {s0} {s0})");
        // ι/δ on a `lam`-headed application, and `OMEGA_LAM`'s non-reduction.
        let carriers = format!(
            "(kio : forall (p : KExpr) (q : KExpr) (r : KExpr) (z : KExpr), \
             iota_reduces (KExpr.app (KExpr.lam p q) r) z -> whnf_acc z) \
             (kde : forall (p : KExpr) (q : KExpr) (r : KExpr) (z : KExpr), \
             delta_reduces (KExpr.app (KExpr.lam p q) r) z -> whnf_acc z) \
             (knored : forall (f2 : KExpr) (R : Type), beta_reduces {OM} f2 -> R)"
        );
        let dflt = s0.to_string();
        let arm = |vals: &str| format!("(fun ({vals}) => {dflt})");
        vec![
            (
                "lamBody".to_string(),
                format!(
                    "def lamBody (t : KExpr) : KExpr := \
                     @KExpr.rec (fun (_t : KExpr) => KExpr) \
                     {sort} {bvar} {app} \
                     (fun (lty : KExpr) (lb : KExpr) (i1 : KExpr) (i2 : KExpr) => lb) \
                     {pi} {konst} {let_} {proj} {mvar} t",
                    sort = arm("l : Level"),
                    bvar = arm("i : Nat"),
                    app = arm("ff : KExpr) (aa : KExpr) (i1 : KExpr) (i2 : KExpr"),
                    pi = arm("ty : KExpr) (bb : KExpr) (i1 : KExpr) (i2 : KExpr"),
                    konst = arm("nm : Name) (us : ListType Level"),
                    let_ = arm("zty : KExpr) (zv : KExpr) (zb : KExpr) (i1 : KExpr) \
                         (i2 : KExpr) (i3 : KExpr"),
                    proj = arm("ps : Name) (pidx : Nat) (sub : KExpr) (i1 : KExpr"),
                    mvar = arm("v : Nat"),
                ),
            ),
            (
                // A local copy of the `sort 0` transport, so this probe does not
                // have to register a third dependency vec — the gate is at its
                // ceiling and each registration costs real memory.
                "piintro_acc_to_sort".to_string(),
                format!(
                    "def piintro_acc_to_sort : forall (k : Nat) (y : KExpr), \
                     whnf_acc y -> RedW k {s0} y := \
                     @Nat.rec (fun (kk : Nat) => forall (y : KExpr), \
                     whnf_acc y -> RedW kk {s0} y) \
                     (fun (y : KExpr) (h0 : whnf_acc y) => h0) \
                     (fun (n : Nat) (_ih : forall (y : KExpr), \
                     whnf_acc y -> RedW n {s0} y) => \
                     fun (y : KExpr) (ha : whnf_acc y) => ha)"
                ),
            ),
            (
                // MEASURED 2026-09-19 (probe run 2): `instantiate` does NOT reduce on a
                // concrete body against a VARIABLE argument. Read the definitions rather
                // than guessing again — `instantiate b v = instantiate_at b v 0`, whose
                // `bvar` arm is `instantiate_bvar_at i 0 v`, which lands on
                // `instantiate_bvar_geq i 0 v = lift_at v Nat.zero Nat.zero`. And
                // `lift_at` MATCHES ON ITS EXPRESSION, so at a free variable it is stuck.
                // The missing fact is therefore LIFT-BY-ZERO IS THE IDENTITY, and the
                // tree has no such lemma (the only sibling, `r28_probe_lift_fixed_depth`,
                // lifts by ONE and carries an `InertTy` side condition).
                //
                // The `bvar` case needs its own induction because `Nat.sub c i` recurses
                // on its SECOND argument and so is stuck at a variable `i` — but BOTH
                // branches give `bvar i`, since `Nat.add i Nat.zero` computes to `i`
                // (`Nat.add` recurses on its second argument too).
                "lift_bvar_zero".to_string(),
                "def lift_bvar_zero (i : Nat) (c : Nat) : \
                 @Eq KExpr (lift_bvar_at i c Nat.zero) (KExpr.bvar i) := \
                 @Nat.rec (fun (k : Nat) => \
                 @Eq KExpr (@Nat.rec (fun (_j : Nat) => KExpr) \
                 (KExpr.bvar (Nat.add i Nat.zero)) \
                 (fun (_j : Nat) (_r : KExpr) => KExpr.bvar i) k) (KExpr.bvar i)) \
                 (@Eq.refl KExpr (KExpr.bvar i)) \
                 (fun (k : Nat) (_ih : @Eq KExpr (@Nat.rec (fun (_j : Nat) => KExpr) \
                 (KExpr.bvar (Nat.add i Nat.zero)) \
                 (fun (_j : Nat) (_r : KExpr) => KExpr.bvar i) k) (KExpr.bvar i)) => \
                 @Eq.refl KExpr (KExpr.bvar i)) \
                 (Nat.sub c i)"
                    .to_string(),
            ),
            (
                // The 9 arms are `sort, bvar, app, lam, pi, const, let_, proj, lit` —
                // read off `lift_at`'s own match, NOT guessed. (`RedWInner`'s ninth arm
                // is named `mvar` in this tree and is really `lit`; same arity, which is
                // why it elaborates.) The binder-crossing arms recur at `Nat.succ c`,
                // which is exactly why the statement quantifies the cutoff.
                "lift_zero_id".to_string(),
                {
                    let cong1 = |ctor: &str, sub: &str, rest: &str, ih: &str, v: &str| {
                        format!(
                            "(Eq.substType KExpr (fun (q : KExpr) => \
                             Eq KExpr {ctor} ({sub} q {rest})) \
                             (lift_at {v} c Nat.zero) {v} ({ih} c) "
                        )
                    };
                    let _ = cong1;
                    // Written out per arm; the pattern is: start from `Eq.refl` on the
                    // LIFTED spelling and rewrite each lifted subterm to its unlifted
                    // self with one `Eq.substType` per subterm.
                    "def lift_zero_id : forall (e : KExpr) (c : Nat), \
                     @Eq KExpr (lift_at e c Nat.zero) e := \
                     @KExpr.rec (fun (e : KExpr) => forall (c : Nat), \
                     @Eq KExpr (lift_at e c Nat.zero) e) \
                     (fun (l : Level) (c : Nat) => @Eq.refl KExpr (KExpr.sort l)) \
                     (fun (i : Nat) (c : Nat) => lift_bvar_zero i c) \
                     (fun (f : KExpr) (a : KExpr) \
                     (ihf : forall (c : Nat), @Eq KExpr (lift_at f c Nat.zero) f) \
                     (iha : forall (c : Nat), @Eq KExpr (lift_at a c Nat.zero) a) \
                     (c : Nat) => \
                     Eq.substType KExpr (fun (q : KExpr) => \
                     @Eq KExpr (KExpr.app (lift_at f c Nat.zero) (lift_at a c Nat.zero)) \
                     (KExpr.app f q)) (lift_at a c Nat.zero) a (iha c) \
                     (Eq.substType KExpr (fun (q : KExpr) => \
                     @Eq KExpr (KExpr.app (lift_at f c Nat.zero) (lift_at a c Nat.zero)) \
                     (KExpr.app q (lift_at a c Nat.zero))) \
                     (lift_at f c Nat.zero) f (ihf c) \
                     (@Eq.refl KExpr (KExpr.app (lift_at f c Nat.zero) \
                     (lift_at a c Nat.zero))))) \
                     (fun (ty : KExpr) (b : KExpr) \
                     (ihty : forall (c : Nat), @Eq KExpr (lift_at ty c Nat.zero) ty) \
                     (ihb : forall (c : Nat), @Eq KExpr (lift_at b c Nat.zero) b) \
                     (c : Nat) => \
                     Eq.substType KExpr (fun (q : KExpr) => \
                     @Eq KExpr (KExpr.lam (lift_at ty c Nat.zero) \
                     (lift_at b (Nat.succ c) Nat.zero)) (KExpr.lam ty q)) \
                     (lift_at b (Nat.succ c) Nat.zero) b (ihb (Nat.succ c)) \
                     (Eq.substType KExpr (fun (q : KExpr) => \
                     @Eq KExpr (KExpr.lam (lift_at ty c Nat.zero) \
                     (lift_at b (Nat.succ c) Nat.zero)) \
                     (KExpr.lam q (lift_at b (Nat.succ c) Nat.zero))) \
                     (lift_at ty c Nat.zero) ty (ihty c) \
                     (@Eq.refl KExpr (KExpr.lam (lift_at ty c Nat.zero) \
                     (lift_at b (Nat.succ c) Nat.zero))))) \
                     (fun (ty : KExpr) (b : KExpr) \
                     (ihty : forall (c : Nat), @Eq KExpr (lift_at ty c Nat.zero) ty) \
                     (ihb : forall (c : Nat), @Eq KExpr (lift_at b c Nat.zero) b) \
                     (c : Nat) => \
                     Eq.substType KExpr (fun (q : KExpr) => \
                     @Eq KExpr (KExpr.pi (lift_at ty c Nat.zero) \
                     (lift_at b (Nat.succ c) Nat.zero)) (KExpr.pi ty q)) \
                     (lift_at b (Nat.succ c) Nat.zero) b (ihb (Nat.succ c)) \
                     (Eq.substType KExpr (fun (q : KExpr) => \
                     @Eq KExpr (KExpr.pi (lift_at ty c Nat.zero) \
                     (lift_at b (Nat.succ c) Nat.zero)) \
                     (KExpr.pi q (lift_at b (Nat.succ c) Nat.zero))) \
                     (lift_at ty c Nat.zero) ty (ihty c) \
                     (@Eq.refl KExpr (KExpr.pi (lift_at ty c Nat.zero) \
                     (lift_at b (Nat.succ c) Nat.zero))))) \
                     (fun (nm : Name) (us : ListType Level) (c : Nat) => \
                     @Eq.refl KExpr (KExpr.const nm us)) \
                     (fun (ty : KExpr) (v : KExpr) (b : KExpr) \
                     (ihty : forall (c : Nat), @Eq KExpr (lift_at ty c Nat.zero) ty) \
                     (ihv : forall (c : Nat), @Eq KExpr (lift_at v c Nat.zero) v) \
                     (ihb : forall (c : Nat), @Eq KExpr (lift_at b c Nat.zero) b) \
                     (c : Nat) => \
                     Eq.substType KExpr (fun (q : KExpr) => \
                     @Eq KExpr (KExpr.let_ (lift_at ty c Nat.zero) \
                     (lift_at v c Nat.zero) (lift_at b (Nat.succ c) Nat.zero)) \
                     (KExpr.let_ ty v q)) \
                     (lift_at b (Nat.succ c) Nat.zero) b (ihb (Nat.succ c)) \
                     (Eq.substType KExpr (fun (q : KExpr) => \
                     @Eq KExpr (KExpr.let_ (lift_at ty c Nat.zero) \
                     (lift_at v c Nat.zero) (lift_at b (Nat.succ c) Nat.zero)) \
                     (KExpr.let_ ty q (lift_at b (Nat.succ c) Nat.zero))) \
                     (lift_at v c Nat.zero) v (ihv c) \
                     (Eq.substType KExpr (fun (q : KExpr) => \
                     @Eq KExpr (KExpr.let_ (lift_at ty c Nat.zero) \
                     (lift_at v c Nat.zero) (lift_at b (Nat.succ c) Nat.zero)) \
                     (KExpr.let_ q (lift_at v c Nat.zero) \
                     (lift_at b (Nat.succ c) Nat.zero))) \
                     (lift_at ty c Nat.zero) ty (ihty c) \
                     (@Eq.refl KExpr (KExpr.let_ (lift_at ty c Nat.zero) \
                     (lift_at v c Nat.zero) \
                     (lift_at b (Nat.succ c) Nat.zero)))))) \
                     (fun (sn : Name) (si : Nat) (sub : KExpr) \
                     (ihs : forall (c : Nat), @Eq KExpr (lift_at sub c Nat.zero) sub) \
                     (c : Nat) => \
                     Eq.substType KExpr (fun (q : KExpr) => \
                     @Eq KExpr (KExpr.proj sn si (lift_at sub c Nat.zero)) \
                     (KExpr.proj sn si q)) \
                     (lift_at sub c Nat.zero) sub (ihs c) \
                     (@Eq.refl KExpr (KExpr.proj sn si (lift_at sub c Nat.zero)))) \
                     (fun (ln : Nat) (c : Nat) => @Eq.refl KExpr (KExpr.lit ln))"
                        .to_string()
                },
            ),
            (
                // Now the equation the refutation needs, PROVED rather than assumed:
                // `instantiate OM_BODY y` is `app (lift_at y 0 0) (lift_at y 0 0)`, and
                // `lift_zero_id` collapses each side.
                "omega_instantiate_body".to_string(),
                format!(
                    "def omega_instantiate_body (y : KExpr) : \
                     @Eq KExpr (instantiate {OM_BODY} y) (KExpr.app y y) := \
                     Eq.substType KExpr (fun (q : KExpr) => \
                     @Eq KExpr (KExpr.app (lift_at y Nat.zero Nat.zero) \
                     (lift_at y Nat.zero Nat.zero)) (KExpr.app y q)) \
                     (lift_at y Nat.zero Nat.zero) y (lift_zero_id y Nat.zero) \
                     (Eq.substType KExpr (fun (q : KExpr) => \
                     @Eq KExpr (KExpr.app (lift_at y Nat.zero Nat.zero) \
                     (lift_at y Nat.zero Nat.zero)) \
                     (KExpr.app q (lift_at y Nat.zero Nat.zero))) \
                     (lift_at y Nat.zero Nat.zero) y (lift_zero_id y Nat.zero) \
                     (@Eq.refl KExpr (KExpr.app (lift_at y Nat.zero Nat.zero) \
                     (lift_at y Nat.zero Nat.zero))))"
                ),
            ),
            (
                "omega_app_acc_of_candidate".to_string(),
                format!(
                    "def omega_app_acc_of_candidate {carriers} \
                     (hinst : forall (y : KExpr), \
                     @Eq KExpr (instantiate {OM_BODY} y) (KExpr.app y y)) \
                     (a : KExpr) (ha : whnf_acc a) : \
                     (forall (y : KExpr), whnf_acc y -> whnf_acc (KExpr.app a y)) -> \
                     whnf_acc (KExpr.app {OM} a) := \
                     @whnf_acc.rec \
                     (fun (w : KExpr) (_hw : whnf_acc w) => \
                     (forall (y : KExpr), whnf_acc y -> whnf_acc (KExpr.app w y)) -> \
                     whnf_acc (KExpr.app {OM} w)) \
                     (fun (w : KExpr) \
                     (fw : forall (y : KExpr), whnf_step w y -> whnf_acc y) \
                     (ih : forall (y : KExpr) (_s : whnf_step w y), \
                     (forall (u : KExpr), whnf_acc u -> whnf_acc (KExpr.app y u)) -> \
                     whnf_acc (KExpr.app {OM} y)) \
                     (hc : forall (y : KExpr), whnf_acc y -> whnf_acc (KExpr.app w y)) => \
                     whnf_acc.intro (KExpr.app {OM} w) \
                     (fun (z : KExpr) (sz : whnf_step (KExpr.app {OM} w) z) => \
                     whnf_step_app_inv {OM} w z (whnf_acc z) sz \
                     (fun (A0 : KExpr) (body : KExpr) \
                     (heq : @Eq KExpr {OM} (KExpr.lam A0 body)) \
                     (hz : @Eq KExpr z (instantiate body w)) => \
                     Eq.substType KExpr (fun (q : KExpr) => whnf_acc q) \
                     (instantiate body w) z \
                     (@Eq.symm KExpr z (instantiate body w) hz) \
                     (Eq.substType KExpr \
                     (fun (q : KExpr) => whnf_acc (instantiate q w)) \
                     {OM_BODY} body \
                     (Eq.substType KExpr \
                     (fun (q : KExpr) => @Eq KExpr (lamBody {OM}) (lamBody q)) \
                     {OM} (KExpr.lam A0 body) heq \
                     (@Eq.refl KExpr (lamBody {OM}))) \
                     (Eq.substType KExpr (fun (q : KExpr) => whnf_acc q) \
                     (KExpr.app w w) (instantiate {OM_BODY} w) \
                     (@Eq.symm KExpr (instantiate {OM_BODY} w) (KExpr.app w w) \
                     (hinst w)) \
                     (hc w (whnf_acc.intro w fw))))) \
                     (fun (f2 : KExpr) (hf : beta_reduces {OM} f2) \
                     (_hz : @Eq KExpr z (KExpr.app f2 w)) => \
                     knored f2 (whnf_acc z) hf) \
                     (fun (a2 : KExpr) (hsa : beta_reduces w a2) \
                     (hz : @Eq KExpr z (KExpr.app {OM} a2)) => \
                     Eq.substType KExpr (fun (q : KExpr) => whnf_acc q) \
                     (KExpr.app {OM} a2) z \
                     (@Eq.symm KExpr z (KExpr.app {OM} a2) hz) \
                     (ih a2 (whnf_step.beta w a2 hsa) \
                     (fun (u : KExpr) (hu : whnf_acc u) => \
                     whnf_acc_step (KExpr.app w u) (KExpr.app a2 u) (hc u hu) \
                     (whnf_step.beta (KExpr.app w u) (KExpr.app a2 u) \
                     (beta_reduces.app_left w a2 u hsa))))) \
                     (fun (hi : iota_reduces (KExpr.app {OM} w) z) => \
                     kio (KExpr.bvar Nat.zero) {OM_BODY} w z hi) \
                     (fun (hd : delta_reduces (KExpr.app {OM} w) z) => \
                     kde (KExpr.bvar Nat.zero) {OM_BODY} w z hd))) \
                     a ha"
                ),
            ),
            (
                // Trust: the ι carrier, discharged. Same one-liner shape as
                // `no_iota_reduces_bvar_app` — ι needs a RECURSOR head and a
                // `lam`-headed application has none, so the step computes to `none`
                // and `option_none_ne_some_type` closes it.
                "no_iota_reduces_lam_app".to_string(),
                "def no_iota_reduces_lam_app (p : KExpr) (q : KExpr) (r : KExpr) \
                 (z : KExpr) (C : Type) \
                 (h : iota_reduces (KExpr.app (KExpr.lam p q) r) z) : C := \
                 option_none_ne_some_type KExpr z C \
                 (iota_reduces_to_step (KExpr.app (KExpr.lam p q) r) z h)"
                    .to_string(),
            ),
            (
                // The δ carrier, discharged. δ needs a CONST head; a `lam`-headed
                // application has none.
                "no_delta_reduces_lam_app".to_string(),
                "def no_delta_reduces_lam_app (p : KExpr) (q : KExpr) (r : KExpr) \
                 (z : KExpr) (C : Type) \
                 (h : delta_reduces (KExpr.app (KExpr.lam p q) r) z) : C := \
                 option_none_ne_some_type KExpr z C \
                 (delta_reduces_to_step (KExpr.app (KExpr.lam p q) r) z h)"
                    .to_string(),
            ),
            (
                // The β carrier, discharged. `OMEGA_LAM` has NO `beta_reduces`
                // successor at all, and this is the argument `whnf_acc_omega_lam`
                // already runs INSIDE itself — extracted here so it can be named.
                // A step must be in the domain (`bvar 0`, which does not step) or in
                // the body `app (bvar 0) (bvar 0)`, whose every inversion case is
                // closed: the beta case needs the head to be a `lam` and it is a
                // `bvar` (`lam_ne_bvar`), the fn/arg cases step a `bvar`, and ι/δ on a
                // `bvar`-headed application are already refuted in the tree.
                //
                // MEASURED: `beta_reduces_lam_inv` takes a FOURTH continuation,
                // `kiota : iota_reduces (lam A b) e2 -> C` — so `beta_reduces` on a
                // `lam` can also arise ι-wise and the inversion will not let you
                // forget it. A first attempt supplied only kty/kbody and failed with
                // `expected R, got (iota_reduces (lam ..) z -> R) -> R`, which is the
                // missing argument naming itself. Discharged by `no_iota_reduces_lam`.
                "no_beta_reduces_omega_lam".to_string(),
                format!(
                    "def no_beta_reduces_omega_lam (f2 : KExpr) (R : Type) \
                     (hb : beta_reduces {OM} f2) : R := \
                     beta_reduces_lam_inv (KExpr.bvar Nat.zero) {OM_BODY} f2 R hb \
                     (fun (A2 : KExpr) (hsA : beta_reduces (KExpr.bvar Nat.zero) A2) \
                     (_he : @Eq KExpr f2 (KExpr.lam A2 {OM_BODY})) => \
                     no_whnf_step_bvar Nat.zero A2 R \
                     (whnf_step.beta (KExpr.bvar Nat.zero) A2 hsA)) \
                     (fun (b2 : KExpr) (hsb : beta_reduces {OM_BODY} b2) \
                     (_he : @Eq KExpr f2 (KExpr.lam (KExpr.bvar Nat.zero) b2)) => \
                     whnf_step_app_inv (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero) b2 R \
                     (whnf_step.beta {OM_BODY} b2 hsb) \
                     (fun (A0 : KExpr) (body0 : KExpr) \
                     (hl : @Eq KExpr (KExpr.bvar Nat.zero) (KExpr.lam A0 body0)) \
                     (_hb2 : @Eq KExpr b2 (instantiate body0 (KExpr.bvar Nat.zero))) => \
                     lam_ne_bvar A0 body0 Nat.zero R \
                     (@Eq.symm KExpr (KExpr.bvar Nat.zero) (KExpr.lam A0 body0) hl)) \
                     (fun (g2 : KExpr) (hsf : beta_reduces (KExpr.bvar Nat.zero) g2) \
                     (_hb2 : @Eq KExpr b2 (KExpr.app g2 (KExpr.bvar Nat.zero))) => \
                     no_whnf_step_bvar Nat.zero g2 R \
                     (whnf_step.beta (KExpr.bvar Nat.zero) g2 hsf)) \
                     (fun (a2 : KExpr) (hsa : beta_reduces (KExpr.bvar Nat.zero) a2) \
                     (_hb2 : @Eq KExpr b2 (KExpr.app (KExpr.bvar Nat.zero) a2)) => \
                     no_whnf_step_bvar Nat.zero a2 R \
                     (whnf_step.beta (KExpr.bvar Nat.zero) a2 hsa)) \
                     (fun (hir : iota_reduces {OM_BODY} b2) => \
                     no_iota_reduces_bvar_app Nat.zero (KExpr.bvar Nat.zero) b2 R hir) \
                     (fun (hdr : delta_reduces {OM_BODY} b2) => \
                     no_delta_reduces_bvar_app Nat.zero (KExpr.bvar Nat.zero) b2 R hdr)) \
                     (fun (hir : iota_reduces {OM} f2) => \
                     no_iota_reduces_lam (KExpr.bvar Nat.zero) {OM_BODY} f2 R hir)"
                ),
            ),
            (
                "redw_pi_intro_refuted_at_redwstep".to_string(),
                format!(
                    "def redw_pi_intro_refuted_at_redwstep (C : Type) {carriers} \
                     (law : forall (A : KExpr) (B : KExpr) (f : KExpr), \
                     (forall (a : KExpr), RedWStep A a -> \
                     RedWStep (instantiate B a) (KExpr.app f a)) -> \
                     RedWStep (KExpr.pi A B) f) : C := \
                     self_app_loop_not_whnf_acc {OM} omega_self_step C \
                     (AndType.right (whnf_acc {OM}) {pw_om} \
                     (law {pia} {s0} {OM} \
                     (fun (a : KExpr) (h : RedWStep {pia} a) => \
                     fun (n : Nat) => piintro_acc_to_sort n (KExpr.app {OM} a) \
                     (omega_app_acc_of_candidate kio kde knored omega_instantiate_body \
                     a (h Nat.zero) \
                     (AndType.right (whnf_acc a) {pw_a} \
                     (h (Nat.succ Nat.zero))))) \
                     (Nat.succ Nat.zero)) \
                     {OM} whnf_acc_omega_lam_uncond)",
                    pw_om = format_args!(
                        "(forall (x : KExpr), RedW Nat.zero {s0} x -> \
                         RedW Nat.zero {s0} (KExpr.app {OM} x))"
                    ),
                    pw_a = format_args!(
                        "(forall (x : KExpr), RedW Nat.zero {s0} x -> \
                         RedW Nat.zero {s0} (KExpr.app a x))"
                    ),
                ),
            ),
            (
                // The refutation with EVERY carrier discharged — the `_uncond` form,
                // on the `pi_elim_blind_refuted` -> `pi_elim_blind_refuted_uncond`
                // pattern. If this elaborates, `pi_intro` is FALSE at `RedWStep`
                // outright, not false-modulo-three-hypotheses.
                "redw_pi_intro_refuted_at_redwstep_uncond".to_string(),
                format!(
                    "def redw_pi_intro_refuted_at_redwstep_uncond (C : Type) \
                     (law : forall (A : KExpr) (B : KExpr) (f : KExpr), \
                     (forall (a : KExpr), RedWStep A a -> \
                     RedWStep (instantiate B a) (KExpr.app f a)) -> \
                     RedWStep (KExpr.pi A B) f) : C := \
                     redw_pi_intro_refuted_at_redwstep C \
                     (fun (p : KExpr) (q : KExpr) (r : KExpr) (z : KExpr) \
                     (h : iota_reduces (KExpr.app (KExpr.lam p q) r) z) => \
                     no_iota_reduces_lam_app p q r z (whnf_acc z) h) \
                     (fun (p : KExpr) (q : KExpr) (r : KExpr) (z : KExpr) \
                     (h : delta_reduces (KExpr.app (KExpr.lam p q) r) z) => \
                     no_delta_reduces_lam_app p q r z (whnf_acc z) h) \
                     (fun (f2 : KExpr) (R : Type) (h : beta_reduces {OM} f2) => \
                     no_beta_reduces_omega_lam f2 R h) \
                     law"
                ),
            ),
        ]
    }
}

#[cfg(test)]
#[path = "candmodel_whnf_pi_intro_tests.rs"]
mod tests;
