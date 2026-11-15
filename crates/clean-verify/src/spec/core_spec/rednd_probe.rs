// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **PROBE — is `pi_elim`'s failure about PI, or about DEPENDENCE?**
//!
//! `designs/2026-09-18-is-candmodel-uninhabited.md` §3g localises the whole
//! content of the `CandModel` hypothesis to `pi_elim`: it is the only law that
//! must MANUFACTURE strong normalization rather than inherit it, which is why
//! the type-blind candidate fails it and only it. That says WHERE the
//! difficulty is. It does not say WHAT it is.
//!
//! This asks the next question. The type-blind family fails `pi_elim` because
//! it discards the type index. So give it one — define reducibility by
//! STRUCTURAL RECURSION on the type, the Girard/Tait shape:
//!
//! ```text
//! RedNd (pi A B) f := whnf_acc f  AND  (forall a, RedNd A a -> RedNd B (app f a))
//! RedNd T        e := whnf_acc e                                     (otherwise)
//! ```
//!
//! This is well-founded where the real construction is not: the `pi` arm's
//! recursive calls are at `A` and `B`, which are SUBTERMS of `pi A B`, so
//! `KExpr.rec` accepts it. The real definition needs `RedNd (instantiate B a)`,
//! and `instantiate B a` is not a subterm of anything.
//!
//! # What the probe is designed to show
//!
//! That the gap between the two is EXACTLY dependence. `rednd_pi_elim_nondep`
//! discharges `pi_elim` at this candidate under one side condition —
//! `instantiate B a = B`, i.e. the codomain does not mention its binder. If it
//! elaborates, then:
//!
//! * `pi_elim` is not hard because of `pi`, and not hard because of
//!   application — a type-aware family gets it by projection;
//! * the entire residual difficulty is the DEPENDENT case, where the recursion
//!   would have to descend into `instantiate B a`.
//!
//! That is a sharper statement than §3g's and it is the one that says what a
//! construction actually has to solve.
//!
//! # What the probe measures, law by law
//!
//! Four of the fourteen laws are registered here, and the interesting content is
//! in which fifth one is NOT.
//!
//! Read the STATUS column as what the scratch test last measured, not as what
//! the term is meant to show — `rednd_probe_tests.rs` is the artifact.
//!
//! | law | at `RedNd` | cost |
//! |---|---|---|
//! | `cr1` | elaborates | `AndType.left` at `pi`, identity elsewhere |
//! | `cr2` | elaborates | `whnf_acc_step`, plus `whnfStep_app_left` under `ihb` |
//! | `red_sort` | elaborates | identity — it is the `sort` arm by definition |
//! | `pi_elim` | elaborates NON-DEPENDENTLY | projection and a transport |
//! | `cr3` | **NOT WRITTEN — see below** | a nested accessibility induction |
//!
//! ## Why `cr3` is the expensive one, and what that says
//!
//! At the type-BLIND candidate `cr3` is free: it is literally `whnf_acc.intro`,
//! which holds at every term, neutral or not. That is why `cr3` sits among the
//! eight laws the blind family satisfies exactly.
//!
//! At `RedNd` it is not free, and the reason is precise. The `pi` arm has to
//! produce `RedNd b (KExpr.app g x)` from `cr3` at the codomain, which needs
//! every successor of `KExpr.app g x` handled. Inverting that step gives three
//! shapes:
//!
//! * a HEAD step `KExpr.app g2 x` — discharged by the hypothesis at `g2`;
//! * a BETA step — impossible, because `Neutral g` rules out `g` being a `lam`
//!   (`Neutral`'s `lam` arm is `Empty`);
//! * an ARGUMENT step `KExpr.app g x2` — and nothing in scope says anything
//!   about `x2`.
//!
//! The third obligation is dischargeable only by an induction on `whnf_acc x`,
//! which `rednd_cr1` supplies from `RedNd ty x`. That induction is exactly the
//! one Girard's CR3 proof performs, and it is the first point in this whole
//! probe where the type-aware candidate costs a real argument rather than a
//! projection.
//!
//! So the honest reading of the table is: giving the family a type index buys
//! `pi_elim` in the non-dependent case and costs `cr3` an induction. Neither the
//! purchase nor the cost was obvious before it was measured, and the cost is
//! NOT a defect — it is the shape of the construction the ladder is looking for.
//!
//! # What it is NOT
//!
//! `RedNd` is not a candidate model either, and no claim here says otherwise.
//! Its `pi` arm is the non-dependent reading, so it satisfies the DEPENDENT
//! `pi_elim` only under the side condition, exactly as the type-blind family
//! satisfies `redConst` and the `redRec*` family only under theirs. Scratch
//! only, and not to be wired as a fact about `CandModel`.

use crate::spec::Specification;

impl Specification {
    /// The type-aware candidate, by `KExpr.rec` on the TYPE.
    ///
    /// Nine minors — sort, bvar, app, lam, pi, const, let_, proj, lit — with
    /// arities read off `psubst`'s own recursor application rather than
    /// grepped, per this crate's standing note that grep gave the wrong answer
    /// twice. Eight of them ignore the type entirely and return `whnf_acc`;
    /// only `pi` looks at its components, and that is the whole content.
    ///
    /// The motive is `KExpr -> Type`, so this eliminates the `Type 0` inductive
    /// `KExpr` into `Type 1`.
    #[cfg(test)]
    pub(super) fn rednd_src() -> String {
        let blind = "fun (e : KExpr) => whnf_acc e";
        format!(
            "def RedNd (T : KExpr) : KExpr -> Type := \
             KExpr.rec (fun (_ : KExpr) => KExpr -> Type) \
             (fun (n : Level) => {blind}) \
             (fun (i : Nat) => {blind}) \
             (fun (f : KExpr) (a : KExpr) (ihf : KExpr -> Type) (iha : KExpr -> Type) => {blind}) \
             (fun (ty : KExpr) (b : KExpr) (ihty : KExpr -> Type) (ihb : KExpr -> Type) => {blind}) \
             (fun (ty : KExpr) (b : KExpr) (ihty : KExpr -> Type) (ihb : KExpr -> Type) => \
             fun (g : KExpr) => AndType (whnf_acc g) \
             (forall (x : KExpr), ihty x -> ihb (KExpr.app g x))) \
             (fun (n : Name) (us : ListType Level) => {blind}) \
             (fun (lty : KExpr) (lv : KExpr) (lb : KExpr) (ihty : KExpr -> Type) \
             (ihv : KExpr -> Type) (ihb : KExpr -> Type) => {blind}) \
             (fun (ps : Name) (pidx : Nat) (sub : KExpr) (ihsub : KExpr -> Type) => {blind}) \
             (fun (v : Nat) => {blind}) \
             T"
        )
    }

    /// NON-VACUITY: `RedNd` actually COMPUTES. `red_sort` is the identity here,
    /// which it can only be if the `sort` minor reduces. Without this the two
    /// results below could both hold of a family that never unfolds.
    #[cfg(test)]
    pub(super) fn rednd_red_sort_src() -> String {
        "def rednd_red_sort (n : Level) (e : KExpr) (h : whnf_acc e) : \
         RedNd (KExpr.sort n) e := h"
            .to_string()
    }

    /// `cr1` at this candidate: reducible implies strongly normalizing.
    ///
    /// Eight arms are the identity, because `RedNd` at those types IS
    /// `whnf_acc`. The `pi` arm is `AndType.left` — which is why the `whnf_acc`
    /// conjunct is in the `pi` arm at all: without it `cr1` would fail here,
    /// and `cr1` is the law §3g shows everything else hangs from.
    #[cfg(test)]
    pub(super) fn rednd_cr1_src() -> String {
        let id_arm = "fun (e : KExpr) (h : whnf_acc e) => h";
        format!(
            "def rednd_cr1 (T : KExpr) (e : KExpr) (h : RedNd T e) : whnf_acc e := \
             KExpr.rec (fun (T0 : KExpr) => forall (x : KExpr), RedNd T0 x -> whnf_acc x) \
             (fun (n : Level) => {id_arm}) \
             (fun (i : Nat) => {id_arm}) \
             (fun (ff : KExpr) (aa : KExpr) \
             (ihf : forall (x : KExpr), RedNd ff x -> whnf_acc x) \
             (iha : forall (x : KExpr), RedNd aa x -> whnf_acc x) => {id_arm}) \
             (fun (ty : KExpr) (b : KExpr) \
             (ihty : forall (x : KExpr), RedNd ty x -> whnf_acc x) \
             (ihb : forall (x : KExpr), RedNd b x -> whnf_acc x) => {id_arm}) \
             (fun (ty : KExpr) (b : KExpr) \
             (ihty : forall (x : KExpr), RedNd ty x -> whnf_acc x) \
             (ihb : forall (x : KExpr), RedNd b x -> whnf_acc x) => \
             fun (g : KExpr) (hg : RedNd (KExpr.pi ty b) g) => \
             AndType.left (whnf_acc g) \
             (forall (x : KExpr), RedNd ty x -> RedNd b (KExpr.app g x)) hg) \
             (fun (n : Name) (us : ListType Level) => {id_arm}) \
             (fun (lty : KExpr) (lv : KExpr) (lb : KExpr) \
             (ihty : forall (x : KExpr), RedNd lty x -> whnf_acc x) \
             (ihv : forall (x : KExpr), RedNd lv x -> whnf_acc x) \
             (ihb : forall (x : KExpr), RedNd lb x -> whnf_acc x) => {id_arm}) \
             (fun (ps : Name) (pidx : Nat) (sub : KExpr) \
             (ihsub : forall (x : KExpr), RedNd sub x -> whnf_acc x) => {id_arm}) \
             (fun (v : Nat) => {id_arm}) \
             T e h"
        )
    }

    /// **THE POINT.** `pi_elim` at this candidate, under exactly one side
    /// condition: the codomain does not mention its binder.
    ///
    /// The proof is a projection and a transport — `AndType.right` gives the
    /// pointwise function, applying it at `a` gives `RedNd B (app f a)`, and
    /// the side condition rewrites `B` to `instantiate B a`. No induction, no
    /// accessibility argument, nothing about reduction at all.
    ///
    /// That is the finding: at a type-AWARE candidate, non-dependent `pi_elim`
    /// is free. Everything that makes the real field hard is in the step from
    /// `B` to `instantiate B a`.
    #[cfg(test)]
    pub(super) fn rednd_pi_elim_nondep_src() -> String {
        "def rednd_pi_elim_nondep (A : KExpr) (B : KExpr) (f : KExpr) (a : KExpr) \
         (hf : RedNd (KExpr.pi A B) f) (ha : RedNd A a) \
         (hnd : Eq KExpr (instantiate B a) B) : \
         RedNd (instantiate B a) (KExpr.app f a) := \
         Eq.substType KExpr (fun (z : KExpr) => RedNd z (KExpr.app f a)) \
         B (instantiate B a) (Eq.symm KExpr (instantiate B a) B hnd) \
         (AndType.right (whnf_acc f) \
         (forall (x : KExpr), RedNd A x -> RedNd B (KExpr.app f x)) hf a ha)"
            .to_string()
    }

    /// `cr2` at this candidate: reducibility is preserved by a step.
    ///
    /// Eight arms are `whnf_acc_step` verbatim, because `RedNd` at those types
    /// IS `whnf_acc`. The `pi` arm rebuilds the pair: the left conjunct is
    /// `whnf_acc_step` again, and the right transports the pointwise function
    /// along the head congruence `whnfStep_app_left`, discharged by the
    /// codomain's induction hypothesis `ihb`.
    ///
    /// NOTE ON THE MINOR TYPES, which is where the first draft was wrong. The
    /// motive here is `fun T0 => forall x y, RedNd T0 x -> whnf_step x y ->
    /// RedNd T0 y`, so every induction hypothesis has THAT type at its subterm
    /// -- not the `KExpr -> Type` that `rednd_src`'s `fun _ => KExpr -> Type`
    /// motive gives. `rednd_cr1_src` gets this right and is the pattern to copy.
    ///
    /// Worth contrasting with `cr3`, which is NOT available this cheaply.
    #[cfg(test)]
    pub(super) fn rednd_cr2_src() -> String {
        // The motive at a subterm -- every IH binder has this type.
        let ih = |t: &str| {
            format!("forall (x : KExpr) (y : KExpr), RedNd {t} x -> whnf_step x y -> RedNd {t} y")
        };
        let body = "fun (x : KExpr) (y : KExpr) (hx : whnf_acc x) \
                    (sxy : whnf_step x y) => whnf_acc_step x y hx sxy";
        // One non-pi arm: value binders, then one IH binder per recursive slot.
        let arm = |vals: &str, subs: &[&str]| {
            let ihs: String = subs
                .iter()
                .enumerate()
                .map(|(k, t)| format!(" (ih{k} : {})", ih(t)))
                .collect();
            format!("(fun ({vals}){ihs} => {body})")
        };
        let pi_arm = format!(
            "(fun (ty : KExpr) (b : KExpr) (ihty : {ihty}) (ihb : {ihb}) => \
             fun (g : KExpr) (g2 : KExpr) (hg : RedNd (KExpr.pi ty b) g) \
             (sg : whnf_step g g2) => \
             AndType.intro (whnf_acc g2) \
             (forall (x : KExpr), RedNd ty x -> RedNd b (KExpr.app g2 x)) \
             (whnf_acc_step g g2 \
             (AndType.left (whnf_acc g) \
             (forall (x : KExpr), RedNd ty x -> RedNd b (KExpr.app g x)) hg) sg) \
             (fun (x : KExpr) (hx : RedNd ty x) => \
             ihb (KExpr.app g x) (KExpr.app g2 x) \
             (AndType.right (whnf_acc g) \
             (forall (x0 : KExpr), RedNd ty x0 -> RedNd b (KExpr.app g x0)) hg x hx) \
             (whnfStep_app_left g g2 x sg)))",
            ihty = ih("ty"),
            ihb = ih("b"),
        );
        format!(
            "def rednd_cr2 (T : KExpr) (e : KExpr) (e2 : KExpr) (h : RedNd T e) \
             (st : whnf_step e e2) : RedNd T e2 := \
             KExpr.rec (fun (T0 : KExpr) => \
             forall (x : KExpr) (y : KExpr), RedNd T0 x -> whnf_step x y -> RedNd T0 y) \
             {sort} {bvar} {app} {lam} {pi_arm} {konst} {let_} {proj} {mvar} \
             T e e2 h st",
            sort = arm("n : Level", &[]),
            bvar = arm("i : Nat", &[]),
            app = arm("ff : KExpr) (aa : KExpr", &["ff", "aa"]),
            lam = arm("lty : KExpr) (lb : KExpr", &["lty", "lb"]),
            konst = arm("n : Name) (us : ListType Level", &[]),
            let_ = arm(
                "zty : KExpr) (zv : KExpr) (zb : KExpr",
                &["zty", "zv", "zb"],
            ),
            proj = arm("ps : Name) (pidx : Nat) (sub : KExpr", &["sub"]),
            mvar = arm("v : Nat", &[]),
        )
    }

    #[cfg(test)]
    pub(super) fn rednd_probe_sources() -> Vec<(String, String)> {
        vec![
            ("RedNd".to_string(), Self::rednd_src()),
            ("rednd_red_sort".to_string(), Self::rednd_red_sort_src()),
            ("rednd_cr1".to_string(), Self::rednd_cr1_src()),
            ("rednd_cr2".to_string(), Self::rednd_cr2_src()),
            (
                "rednd_pi_elim_nondep".to_string(),
                Self::rednd_pi_elim_nondep_src(),
            ),
        ]
    }
}

#[cfg(test)]
#[path = "rednd_probe_tests.rs"]
mod tests;
