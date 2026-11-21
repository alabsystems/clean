// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **A DERIVATION-INDEXED pi-set — the first buildable step of the dependent
//! route, and its own objection stated beside it.**
//!
//! Measured context (`designs/2026-09-18-is-candmodel-uninhabited.md`): `xval`'s
//! `m_pi` interprets a pi NON-dependently, passing `junkD` where the argument's
//! interpretation belongs. That is forced, not lazy: `domSk Sk.ty = Sk.ty` and
//! `VD Sk.ty = KExpr -> Type`, so a TERM binder's valuation slot holds a
//! CANDIDATE and there is nothing term-shaped to store. `PiSet` can therefore
//! hand its codomain the term `a` but never a `WKC` derivation for it.
//!
//! The design constraint that follows: a spelling quantifying a free
//! `va : VD d` alongside `a` is TOO STRONG — it demands the codomain at every
//! value rather than at `a`'s. The value must be TIED to the term, and the only
//! tie available is a derivation. Hence:
//!
//! ```text
//! PiSetDep D d r CA CB := fun t =>
//!   forall (a : KExpr) (ha : WKC D a d), CA a -> CB (xval D a d ha r) (app t a)
//! ```
//!
//! **THE OBJECTION, stated because it may sink this spelling.** Quantifying over
//! `ha` restricts the condition to arguments that HAVE a derivation, which makes
//! membership WEAKER than `PiSet`'s `forall a, CA a -> ..`. Weaker membership is
//! easier to prove and HARDER TO USE — and cr1 (every member is `whnf_acc`) is a
//! USE. A Tait candidate normally quantifies every term of the candidate, not
//! only the typed ones. So this probe is a measurement of whether the spelling
//! is even well-formed, NOT a claim that it is the right candidate notion.
//!
//! A second, independent hazard, now SETTLED: two derivations of the same
//! `WKC D a d` could in principle give different `xval`, so the tie is only as
//! good as derivation irrelevance at that type. That is `r17_xval_irrel`,
//! proved at R17 via `r17_wkc_deriv_unique` — `WKC` is a subsingleton. The
//! hazard was real and is discharged; this note used to point at
//! `r14_wkCastT` / `r14_wkCastS` as "where that would be settled", which was
//! the right neighbourhood and the wrong constant.
//!
//! Everything here is SCRATCH and unwired.

use crate::spec::Specification;

impl Specification {
    /// The derivation-indexed pi-set, and the two facts worth measuring about it.
    #[cfg(test)]
    pub(super) fn candmodel_dep_pi_sources() -> Vec<(String, String)> {
        vec![
            (
                // Does it even elaborate? `VD d` lives in `Type 1` and the body
                // is a `Type`, so the universe of a `forall` over a derivation
                // is the first thing that can refuse this.
                "PiSetDep".to_string(),
                "def PiSetDep (D : Nat -> Sk) (d : Sk) (r : VEnvD D) \
                 (CA : KExpr -> Type) (CB : VD d -> KExpr -> Type) : KExpr -> Type := \
                 fun (t : KExpr) => forall (a : KExpr) (ha : WKC D a d), \
                 CA a -> CB (xval D a d ha r) (KExpr.app t a)"
                    .to_string(),
            ),
            (
                // THE DECISIVE OBLIGATION: cr1 at `PiSetDep`.
                //
                // Measured from `pi_intro_blind`'s own proof: it uses its
                // pointwise hypothesis at EXACTLY ONE argument, `KExpr.bvar
                // Nat.zero` --
                //   whnf_acc_app_fn hdapp (app ff (bvar 0))
                //     (hpt (bvar 0) (whnf_acc_bvar 0)) ff (bvar 0) (Eq.refl ..)
                // -- and `WKC.var : WKC D (bvar i) (D i)` types EVERY variable.
                // So the arguments `PiSetDep` drops relative to `PiSet` (the
                // non-variable untyped terms) are precisely the ones cr1 never
                // reaches for, and the weakening proved above costs nothing HERE.
                //
                // `hd` transports the variable's shape: `WKC.var` gives
                // `WKC D (bvar i) (D i)` and the pi-set wants it at `d`.
                "piSetDep_cr1".to_string(),
                "def piSetDep_cr1 \
                 (hdapp : forall (p : KExpr) (q : KExpr) (rr : KExpr), \
                 delta_reduces p q -> whnf_step (KExpr.app p rr) (KExpr.app q rr)) \
                 (D : Nat -> Sk) (d : Sk) (r : VEnvD D) (i : Nat) \
                 (hd : @Eq Sk (D i) d) \
                 (CA : KExpr -> Type) (CB : VD d -> KExpr -> Type) \
                 (hCAvar : CA (KExpr.bvar i)) \
                 (hCBsn : forall (v : VD d) (x : KExpr), CB v x -> whnf_acc x) \
                 (t : KExpr) (h : PiSetDep D d r CA CB t) : whnf_acc t := \
                 whnf_acc_app_fn hdapp (KExpr.app t (KExpr.bvar i)) \
                 (hCBsn (xval D (KExpr.bvar i) d \
                 (Eq.substType Sk (fun (z : Sk) => WKC D (KExpr.bvar i) z) \
                 (D i) d hd (WKC.var D i)) r) \
                 (KExpr.app t (KExpr.bvar i)) \
                 (h (KExpr.bvar i) \
                 (Eq.substType Sk (fun (z : Sk) => WKC D (KExpr.bvar i) z) \
                 (D i) d hd (WKC.var D i)) hCAvar)) \
                 t (KExpr.bvar i) \
                 (@Eq.refl KExpr (KExpr.app t (KExpr.bvar i)))"
                    .to_string(),
            ),
            (
                // cr2 at `PiSetDep`. Direct: the codomain index `xval D a d ha r`
                // does NOT move when the FUNCTION steps, so this is the codomain's
                // own cr2 under an app-congruence. Contrast cr3 below, where the
                // ARGUMENT steps and the index does move.
                "piSetDep_cr2".to_string(),
                "def piSetDep_cr2 (D : Nat -> Sk) (d : Sk) (r : VEnvD D) \
                 (CA : KExpr -> Type) (CB : VD d -> KExpr -> Type) \
                 (hcong : forall (x : KExpr) (y : KExpr) (aa : KExpr), \
                 whnf_step x y -> whnf_step (KExpr.app x aa) (KExpr.app y aa)) \
                 (hCBcr2 : forall (v : VD d) (x : KExpr) (y : KExpr), \
                 CB v x -> whnf_step x y -> CB v y) \
                 (t : KExpr) (t2 : KExpr) \
                 (h : PiSetDep D d r CA CB t) (st : whnf_step t t2) : \
                 PiSetDep D d r CA CB t2 := \
                 fun (a : KExpr) (ha : WKC D a d) (hca : CA a) => \
                 hCBcr2 (xval D a d ha r) (KExpr.app t a) (KExpr.app t2 a) \
                 (h a ha hca) (hcong t t2 a st)"
                    .to_string(),
            ),
            (
                // WHAT cr3 NEEDS — and the tree HAS it. The next two constants
                // discharge this one; the paragraph that used to stand here said
                // the opposite and was wrong when it was written.
                //
                // cr3's argument-steps case must move the codomain index: from
                // `xval D a d ha r` to `xval D a2 d (wkc_step D a d ha a2 st) r`.
                // `wkc_step` (subject reduction for WKC) EXISTS, and so does the
                // equation relating the two interpretations: `r21_xval_step`,
                // registered since R21. It is still stated here as its own named
                // constant, because a gap that turns out to be closed is worth
                // exactly as much as one that is open only if it is NAMED.
                //
                // (Declared `Prop`, not `Type`: the body is a `forall` ending in
                // an `Eq`, and a first draft annotated `Type` and was refused
                // with "expected Type, got Prop". Recorded because the same slip
                // costs a 19-minute spec build each time.)
                "xvalStepInvariant".to_string(),
                "def xvalStepInvariant (D : Nat -> Sk) (d : Sk) (r : VEnvD D) : Prop := \
                 forall (a : KExpr) (a2 : KExpr) (ha : WKC D a d) (st : whnf_step a a2), \
                 Eq (VD d) (xval D a2 d (wkc_step D a d ha a2 st) r) (xval D a d ha r)"
                    .to_string(),
            ),
            (
                // DISCHARGED 2026-09-19 — one application, no transport.
                //
                // Why the earlier scan missed it, recorded because the same scan
                // will miss the next one: in this tree a constant's NAME and its
                // TYPE live in DIFFERENT files. The name is a string literal in
                // `r21_items()`; the type is a `const TY_*` beside it. So
                // `grep "def r21_xval_step"` — and every grep shaped like it —
                // answers NOTHING for a constant that is registered and green.
                // Grep the `TY_*` bodies, not the `def` spellings.
                //
                // `r21_xval_step` is STRICTLY MORE GENERAL than what is needed
                // here: it takes an arbitrary `h2 : WKC D e2 s` rather than
                // `wkc_step`'s output, so this is one application. That
                // generality is `r17_xval_irrel`'s doing — derivation
                // irrelevance, proved at R17 via `r17_wkc_deriv_unique`.
                "xvalStepInvariant_holds".to_string(),
                "def xvalStepInvariant_holds (D : Nat -> Sk) (d : Sk) (r : VEnvD D) : \
                 xvalStepInvariant D d r := \
                 fun (a : KExpr) (a2 : KExpr) (ha : WKC D a d) (st : whnf_step a a2) => \
                 r21_xval_step D a d ha a2 st (wkc_step D a d ha a2 st) r"
                    .to_string(),
            ),
            (
                // The same statement with the type written OUT rather than via
                // `xvalStepInvariant`. Deliberate redundancy: the folded form
                // needs the elaborator to delta-unfold a `Prop`-valued `def` in
                // TYPE position, and this tree has refused a delta in a
                // neighbouring position before (`Eq.substType`, recorded at R14).
                // If the two disagree, the disagreement is about unfolding and
                // not about the mathematics — worth one arm to separate, since
                // the spec build that answers it costs ~19 minutes.
                "xval_step_invariant_unfolded".to_string(),
                "def xval_step_invariant_unfolded (D : Nat -> Sk) (d : Sk) (r : VEnvD D) \
                 (a : KExpr) (a2 : KExpr) (ha : WKC D a d) (st : whnf_step a a2) : \
                 Eq (VD d) (xval D a2 d (wkc_step D a d ha a2 st) r) (xval D a d ha r) := \
                 r21_xval_step D a d ha a2 st (wkc_step D a d ha a2 st) r"
                    .to_string(),
            ),
            (
                // The weakening, made explicit rather than argued: `PiSet`'s
                // membership IMPLIES `PiSetDep`'s at a codomain that ignores the
                // value. If this elaborates, the two are ordered and the ordering
                // is the wrong way round for a candidate — which is the objection
                // in the module doc, checkable instead of asserted.
                "piSetDep_is_weaker_than_piSet".to_string(),
                "def piSetDep_is_weaker_than_piSet (D : Nat -> Sk) (d : Sk) \
                 (r : VEnvD D) (CA : KExpr -> Type) (C0 : KExpr -> Type) (t : KExpr) \
                 (h : PiSet CA (fun (_a : KExpr) (x : KExpr) => C0 x) t) : \
                 PiSetDep D d r CA (fun (_v : VD d) (x : KExpr) => C0 x) t := \
                 fun (a : KExpr) (_ha : WKC D a d) (hca : CA a) => h a hca"
                    .to_string(),
            ),
            (
                // DIAGNOSTIC, and it must be read BEFORE `piSetDep_cr3` below.
                //
                // `beta_app_index_refutation_probe` measured that this
                // elaborator refutes an impossible constructor by index clash.
                // It did NOT measure whether a SURVIVING branch REFINES a
                // variable bound outside the match. cr3's `beta` case needs
                // exactly that: matching index `KExpr.app t x` against
                // `beta_reduces.beta`'s `KExpr.app (KExpr.lam A body) arg`
                // forces `t := KExpr.lam A body`, and only then does the
                // field's own `hn : Neutral t` become `Neutral (lam A body)`,
                // which computes to `Empty` (Neutral's `lam` arm).
                //
                // Refining a telescope variable requires the match to
                // generalise over it, which many implementations do not do. So
                // it is isolated here: if `piSetDep_cr3` fails and this passes,
                // the fault is elsewhere in cr3; if both fail, the inversion
                // needs the discriminator + `Eq.substType` route that
                // `beta_reduces_preserves_typing.rs` already uses.
                "match_refines_outer_var_probe".to_string(),
                "def match_refines_outer_var_probe (t : KExpr) (x : KExpr) (y : KExpr) \
                 (C : Type) (hn : Neutral t) (c : C) \
                 (h : beta_reduces (KExpr.app t x) y) : C := \
                 match h with \
                 | beta_reduces.beta A body arg => @Empty.rec (fun (_ : Empty) => C) hn \
                 | beta_reduces.app_left f f2 aa hf => c \
                 | beta_reduces.app_right f aa aa2 ha => c \
                 | beta_reduces.iota ee ee2 hi => c"
                    .to_string(),
            ),
            (
                // R30 ROUTE 2, ITEM 3 — THE ARITY-GENERAL SPINE STEP.
                //
                // `candExp_iota_genRec2` is stuck at TWO minors because
                // `candExp_iota_spine4` is stuck at FOUR arguments, resting on a
                // PER-ARITY reduct-inversion scaffold (`constSpine3_beta_inv`,
                // `constSpine4_beta_inv`, `constSpine4_whnf_inv`). Generalising
                // that scaffold is the expensive reading of the residual.
                //
                // `whnfAcc_inertSpine` (`mutual_schema.rs:493`) is the
                // arbitrary-length `ListType` induction one reaches for, and it
                // does NOT apply: its deadness is hypothesised of the head NAME
                // (`defval_for … n = none` AND `recmeta_for … n = none`), which is
                // false for a LIVE recursor. But the deadness `redRecGen` needs is
                // per-spine-LENGTH -- an under-applied recursor does not fire --
                // not a property of the constant.
                //
                // So abstract the head PREDICATE rather than the head name: any
                // `P` closed under application to a `whnf_acc` argument
                // propagates along a spine. `P := whnf_acc` with the inert step
                // recovers `whnfAcc_inertSpine`; `P := S` for a candidate set
                // gives the candidate-set propagation the arity-general engine
                // needs for its DEAD PREFIX, with the fire handled separately at
                // the final argument.
                //
                // Plain `WhnfAccAll.rec`: `apply_spine nil sh` IS `sh` and
                // `apply_spine (cons x rest) sh` IS `apply_spine rest (app sh x)`,
                // both by iota, so the nil arm returns its hypothesis and the cons
                // arm is one `hstep` under the induction hypothesis.
                "spinePropagate".to_string(),
                "def spinePropagate (P : KExpr -> Type) (hstep : forall (h : KExpr) (x : KExpr), P h -> whnf_acc x -> P (KExpr.app h x)) (xs : ListType KExpr) (hxs : WhnfAccAll xs) : forall (sh : KExpr), P sh -> P (apply_spine xs sh) := @WhnfAccAll.rec (fun (l : ListType KExpr) (_ : WhnfAccAll l) => forall (sh : KExpr), P sh -> P (apply_spine l sh)) (fun (sh : KExpr) (hp : P sh) => hp) (fun (x : KExpr) (rest : ListType KExpr) (_hx : whnf_acc x) (_hrest : WhnfAccAll rest) (ih : forall (sh : KExpr), P sh -> P (apply_spine rest sh)) => fun (sh : KExpr) (hp : P sh) => ih (KExpr.app sh x) (hstep sh x hp _hx)) xs hxs"
                    .to_string(),
            ),
            (
                // R30 ROUTE 2 — THE BRIDGE, AND IT IS A ONE-LINER.
                //
                // `inertApp_step_inv` kills its iota arm with
                // `iota_step_no_recmeta_absurd`, keyed on `recmeta_for env n =
                // none` — a property of the head NAME, and FALSE for a live
                // recursor. What an under-applied recursor spine has instead is
                // `iota_reduct env e = none`, which
                // `iota_reduct_whc_none_of_no_major` already proves from the
                // major premise being ABSENT.
                //
                // Those connect definitionally, which is why this is one line:
                // `iota_step env e e'` IS `Eq (iota_reduct env e) (some e')`
                // (`iota_step.rs:162`), so `none = some e'` is immediately absurd
                // by `option_none_ne_some_type` — the same eliminator this
                // inversion already uses for its head-name case.
                "iota_step_no_reduct_absurd".to_string(),
                "def iota_step_no_reduct_absurd (env : RecEnv) (e : KExpr) (t : KExpr) (C : Type) (hnone : @Eq (OptionType KExpr) (iota_reduct env e) (@OptionType.none KExpr)) (hstep : iota_step env e t) : C := option_none_ne_some_type KExpr t C (@Eq.trans (OptionType KExpr) (@OptionType.none KExpr) (iota_reduct env e) (@OptionType.some KExpr t) (@Eq.symm (OptionType KExpr) (iota_reduct env e) (@OptionType.none KExpr) hnone) hstep)"
                    .to_string(),
            ),
            (
                // ... AND THE INVERSION WITH THAT ARM RE-KEYED.
                //
                // A transcription of `inertApp_step_inv` (`mutual_schema.rs:483`)
                // with exactly two edits: the `hrec` binder becomes an
                // APPLICATION-level `hiota`, and the single `hrec` use — there is
                // only one in 10,744 characters — becomes the bridge above. The
                // beta-in-head and beta-in-argument continuations, `app_inj_fst`,
                // the delta arm via `hdef`, and both `whnf_acc.rec` layers are
                // untouched.
                //
                // One transport is needed that the original did not: the iota arm
                // fires at `e0` with `heq : e0 = app sh ar`, so `hiota` — stated
                // at `app sh ar` — is carried back along `heq` by `Eq.substType`.
                // The name-keyed original needed no transport because its
                // hypothesis was about `n`, which no equation moves.
                "deadApp_step_inv".to_string(),
                "def deadApp_step_inv (n : Name) (hdef : @Eq (OptionType KExpr) (defval_for (red_def the_red_env) n) (@OptionType.none KExpr)) (sh : KExpr) (ar : KExpr) (hiota : @Eq (OptionType KExpr) (iota_reduct (red_rec the_red_env) (KExpr.app sh ar)) (@OptionType.none KExpr)) (e2 : KExpr) (C : Type) (hhead : @Eq (OptionType Name) (kexpr_const_name (kapp_fn sh)) (@OptionType.some Name n)) (hs : whnf_step (KExpr.app sh ar) e2) (kL : forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr e2 (KExpr.app h2 ar) -> C) (kR : forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr e2 (KExpr.app sh a2) -> C) : C := @whnf_step.rec (KExpr.app sh ar) e2 (fun (_ : whnf_step (KExpr.app sh ar) e2) => C) (fun (hbr : beta_reduces (KExpr.app sh ar) e2) => @beta_reduces.rec (fun (s : KExpr) (t : KExpr) (_ : beta_reduces s t) => @Eq KExpr s (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr t (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr t (KExpr.app sh a2) -> C) -> C) (fun (A0 : KExpr) (body : KExpr) (arg : KExpr) (heq : @Eq KExpr (KExpr.app (KExpr.lam A0 body) arg) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr (instantiate body arg) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr (instantiate body arg) (KExpr.app sh a2) -> C) => option_none_ne_some_type Name n C (@Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam A0 body))) (kexpr_const_name (kapp_fn sh)) (@OptionType.some Name n) (Eq.cong KExpr (OptionType Name) (fun (w : KExpr) => kexpr_const_name (kapp_fn w)) (KExpr.lam A0 body) sh (app_inj_fst (KExpr.lam A0 body) arg sh ar heq)) hhead)) (fun (g : KExpr) (g2 : KExpr) (x0 : KExpr) (hstp : beta_reduces g g2) (_ih : @Eq KExpr g (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr g2 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr g2 (KExpr.app sh a2) -> C) -> C) (heq : @Eq KExpr (KExpr.app g x0) (KExpr.app sh ar)) (kkL : forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr (KExpr.app g2 x0) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr (KExpr.app g2 x0) (KExpr.app sh a2) -> C) => kkL g2 (Eq.substType KExpr (fun (w : KExpr) => beta_reduces w g2) g sh (app_inj_fst g x0 sh ar heq) hstp) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app g2 w) x0 ar (app_inj_snd g x0 sh ar heq))) (fun (g : KExpr) (x0 : KExpr) (x1 : KExpr) (hstp : beta_reduces x0 x1) (_ih : @Eq KExpr x0 (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr x1 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr x1 (KExpr.app sh a2) -> C) -> C) (heq : @Eq KExpr (KExpr.app g x0) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr (KExpr.app g x1) (KExpr.app h2 ar) -> C) (kkR : forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr (KExpr.app g x1) (KExpr.app sh a2) -> C) => kkR x1 (Eq.substType KExpr (fun (w : KExpr) => beta_reduces w x1) x0 ar (app_inj_snd g x0 sh ar heq) hstp) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app w x1) g sh (app_inj_fst g x0 sh ar heq))) (fun (ty : KExpr) (ty2 : KExpr) (body : KExpr) (hstp : beta_reduces ty ty2) (_ih : @Eq KExpr ty (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr ty2 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr ty2 (KExpr.app sh a2) -> C) -> C) (heq : @Eq KExpr (KExpr.lam ty body) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr (KExpr.lam ty2 body) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr (KExpr.lam ty2 body) (KExpr.app sh a2) -> C) => lam_ne_app ty body sh ar C heq) (fun (ty : KExpr) (body : KExpr) (body2 : KExpr) (hstp : beta_reduces body body2) (_ih : @Eq KExpr body (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr body2 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr body2 (KExpr.app sh a2) -> C) -> C) (heq : @Eq KExpr (KExpr.lam ty body) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr (KExpr.lam ty body2) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr (KExpr.lam ty body2) (KExpr.app sh a2) -> C) => lam_ne_app ty body sh ar C heq) (fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (hstp : beta_reduces dom dom2) (_ih : @Eq KExpr dom (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr dom2 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr dom2 (KExpr.app sh a2) -> C) -> C) (heq : @Eq KExpr (KExpr.pi dom body) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr (KExpr.pi dom2 body) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr (KExpr.pi dom2 body) (KExpr.app sh a2) -> C) => pi_ne_app dom body sh ar C heq) (fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (hstp : beta_reduces body body2) (_ih : @Eq KExpr body (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr body2 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr body2 (KExpr.app sh a2) -> C) -> C) (heq : @Eq KExpr (KExpr.pi dom body) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr (KExpr.pi dom body2) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr (KExpr.pi dom body2) (KExpr.app sh a2) -> C) => pi_ne_app dom body sh ar C heq) (fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (hstp : beta_reduces dom dom2) (_ih : @Eq KExpr dom (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr dom2 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr dom2 (KExpr.app sh a2) -> C) -> C) (heq : @Eq KExpr (KExpr.forall_ dom body) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr (KExpr.forall_ dom2 body) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr (KExpr.forall_ dom2 body) (KExpr.app sh a2) -> C) => pi_ne_app dom body sh ar C heq) (fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (hstp : beta_reduces body body2) (_ih : @Eq KExpr body (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr body2 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr body2 (KExpr.app sh a2) -> C) -> C) (heq : @Eq KExpr (KExpr.forall_ dom body) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr (KExpr.forall_ dom body2) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr (KExpr.forall_ dom body2) (KExpr.app sh a2) -> C) => pi_ne_app dom body sh ar C heq) (fun (ty : KExpr) (val : KExpr) (body : KExpr) (heq : @Eq KExpr (KExpr.let_ ty val body) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr (instantiate body val) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr (instantiate body val) (KExpr.app sh a2) -> C) => let_ne_app ty val body sh ar C heq) (fun (ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr) (hstp : beta_reduces ty ty2) (_ih : @Eq KExpr ty (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr ty2 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr ty2 (KExpr.app sh a2) -> C) -> C) (heq : @Eq KExpr (KExpr.let_ ty val body) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr (KExpr.let_ ty2 val body) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr (KExpr.let_ ty2 val body) (KExpr.app sh a2) -> C) => let_ne_app ty val body sh ar C heq) (fun (ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr) (hstp : beta_reduces val val2) (_ih : @Eq KExpr val (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr val2 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr val2 (KExpr.app sh a2) -> C) -> C) (heq : @Eq KExpr (KExpr.let_ ty val body) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr (KExpr.let_ ty val2 body) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr (KExpr.let_ ty val2 body) (KExpr.app sh a2) -> C) => let_ne_app ty val body sh ar C heq) (fun (ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr) (hstp : beta_reduces body body2) (_ih : @Eq KExpr body (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr body2 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr body2 (KExpr.app sh a2) -> C) -> C) (heq : @Eq KExpr (KExpr.let_ ty val body) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr (KExpr.let_ ty val body2) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr (KExpr.let_ ty val body2) (KExpr.app sh a2) -> C) => let_ne_app ty val body sh ar C heq) (fun (e0 : KExpr) (e02 : KExpr) (hio : iota_reduces e0 e02) (heq : @Eq KExpr e0 (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr e02 (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr e02 (KExpr.app sh a2) -> C) => iota_step_no_reduct_absurd (red_rec the_red_env) e0 e02 C (Eq.substType KExpr (fun (w : KExpr) => @Eq (OptionType KExpr) (iota_reduct (red_rec the_red_env) w) (@OptionType.none KExpr)) (KExpr.app sh ar) e0 (@Eq.symm KExpr e0 (KExpr.app sh ar) heq) hiota) (iota_reduces_to_step e0 e02 hio)) (fun (ps : Name) (pin : Nat) (sub : KExpr) (sub2 : KExpr) (hstp : beta_reduces sub sub2) (_ih : @Eq KExpr sub (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr sub2 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr sub2 (KExpr.app sh a2) -> C) -> C) (heq : @Eq KExpr (KExpr.proj ps pin sub) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> @Eq KExpr (KExpr.proj ps pin sub2) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> @Eq KExpr (KExpr.proj ps pin sub2) (KExpr.app sh a2) -> C) => proj_ne_app ps pin sub sh ar C heq) (KExpr.app sh ar) e2 hbr (@Eq.refl KExpr (KExpr.app sh ar)) kL kR) (fun (hdr : delta_reduces (KExpr.app sh ar) e2) => option_none_ne_some_type KExpr e2 C (@Eq.trans (OptionType KExpr) (@OptionType.none KExpr) (delta_reduct (red_def the_red_env) (KExpr.app sh ar)) (@OptionType.some KExpr e2) (@Eq.symm (OptionType KExpr) (delta_reduct (red_def the_red_env) (KExpr.app sh ar)) (@OptionType.none KExpr) (delta_reduct_eq_none_of_defval_none (red_def the_red_env) (KExpr.app sh ar) n hhead hdef)) (delta_reduces_to_step (KExpr.app sh ar) e2 hdr))) hs"
                    .to_string(),
            ),
            (
                // R30 ROUTE 2 — THE PLAIN-`iota_reduct` NO-MAJOR LEMMA.
                //
                // `iota_reduct_whc_none_of_no_major` concludes about
                // `iota_reduct_whc`, but `iota_step` is defined over PLAIN
                // `iota_reduct` (`iota_step.rs:162`), so the absurdity above
                // needs this form. `iota_reduct`'s body is a five-level
                // `opt_bind` chain whose THIRD bind is the major-premise lookup
                // (`iota_step.rs:150`), so an absent major short-circuits the
                // whole chain: three congruences on the three scrutinees, and
                // `opt_bind none _` computes to `none`.
                "iota_reduct_none_of_no_major".to_string(),
                "def iota_reduct_none_of_no_major (env : RecEnv) (e : KExpr) (nm : Name) (meta : RecMeta) (hh : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name nm)) (hrm : @Eq (OptionType RecMeta) (recmeta_for env nm) (@OptionType.some RecMeta meta)) (hno : @Eq (OptionType KExpr) (list_head (list_drop (iota_major_index meta) (kapp_args e))) (@OptionType.none KExpr)) : @Eq (OptionType KExpr) (iota_reduct env e) (@OptionType.none KExpr) := @Eq.trans (OptionType KExpr) (iota_reduct env e) (opt_bind RecMeta KExpr (recmeta_for env nm) (fun (mta : RecMeta) => (opt_bind KExpr KExpr (list_head (list_drop (iota_major_index mta) (kapp_args e))) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env nm cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major)))))))))) (@OptionType.none KExpr) (Eq.cong (OptionType Name) (OptionType KExpr) (fun (o : OptionType Name) => (opt_bind Name KExpr o (fun (recname : Name) => (opt_bind RecMeta KExpr (recmeta_for env recname) (fun (mta : RecMeta) => (opt_bind KExpr KExpr (list_head (list_drop (iota_major_index mta) (kapp_args e))) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))))))))))) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name nm) hh) (@Eq.trans (OptionType KExpr) (opt_bind RecMeta KExpr (recmeta_for env nm) (fun (mta : RecMeta) => (opt_bind KExpr KExpr (list_head (list_drop (iota_major_index mta) (kapp_args e))) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env nm cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major)))))))))) (opt_bind KExpr KExpr (list_head (list_drop (iota_major_index meta) (kapp_args e))) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env nm cname) (fun (rule : RecRule) => (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major)))))))) (@OptionType.none KExpr) (Eq.cong (OptionType RecMeta) (OptionType KExpr) (fun (o : OptionType RecMeta) => (opt_bind RecMeta KExpr o (fun (mta : RecMeta) => (opt_bind KExpr KExpr (list_head (list_drop (iota_major_index mta) (kapp_args e))) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env nm cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))))))))) (recmeta_for env nm) (@OptionType.some RecMeta meta) hrm) (Eq.cong (OptionType KExpr) (OptionType KExpr) (fun (o : (OptionType KExpr)) => (opt_bind KExpr KExpr o (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env nm cname) (fun (rule : RecRule) => (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))))))) (list_head (list_drop (iota_major_index meta) (kapp_args e))) (@OptionType.none KExpr) hno))"
                    .to_string(),
            ),
        ]
    }
}

impl Specification {
    /// R30 ROUTE 2 — THE DEAD-PREFIX CHAIN, against the FULL spec.
    ///
    /// Measured 2026-09-20 and the reason this vector exists separately: the
    /// three stages carrying the arity lemmas this chain needs are in NEITHER
    /// reduced bundle. `kapp_args_length_app` and `list_head_drop_none_of_le`
    /// come from `add_defeq_fuel`, `inertApp_step_inv`/`inertHead_beta_pres`
    /// from `add_mutual_schema`, `list_append_length` from `add_snschema` —
    /// and all three read `in_substitution: false, in_impl_soundness: false`
    /// in `bundles.rs`. So the substitution spec the sibling probe builds can
    /// host the head-name half of this chain (which is why `deadApp_step_inv`
    /// had to be a TRANSCRIPTION of `inertApp_step_inv` rather than a call)
    /// but cannot host the spine half at all.
    ///
    /// The four prerequisites are taken by NAME from the sibling vector rather
    /// than duplicated, so the two runs cannot drift: they are measured in the
    /// substitution spec there and re-measured in the full spec here.
    #[cfg(test)]
    pub(super) fn candmodel_dead_prefix_sources() -> Vec<(String, String)> {
        const PREREQ: [&str; 4] = [
            "spinePropagate",
            "iota_step_no_reduct_absurd",
            "deadApp_step_inv",
            "iota_reduct_none_of_no_major",
        ];
        let mut rows: Vec<(String, String)> = PREREQ
            .iter()
            .map(|want| {
                Self::candmodel_dep_pi_sources()
                    .into_iter()
                    .find(|(n, _)| n == want)
                    .unwrap_or_else(|| panic!("prerequisite {want} left the sibling vector"))
            })
            .collect();
        rows.push((
            // The strengthened-motive analogue of `inertHead_beta_pres`: a beta
            // step preserves the head NAME *and* the spine LENGTH. Twelve of the
            // fifteen arms are the same contradiction on `hh` — a `lam`/`pi`/
            // `let_`/`proj`/beta-redex has no constant head. `app_left` descends
            // the bound through `kapp_args_length_app` + `le_of_succ_le` and
            // rebuilds the length equality on the way out; `app_right` never
            // moves the head or the length. The `iota` arm is where the bound
            // pays: one argument short of the major index means the major slot
            // is empty, so `iota_reduct` short-circuits to `none` and the step
            // that claimed to fire is absurd.
            "deadHead_beta_pres".to_string(),
            "def deadHead_beta_pres (nm : Name) (meta : RecMeta) (hrm : @Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) nm) (@OptionType.some RecMeta meta)) (e : KExpr) (e2 : KExpr) (C : Type) (hb : beta_reduces e e2) (hhead : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name nm)) (hle : Le (list_length (kapp_args e)) (iota_major_index meta)) (k : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e2)) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args e2)) (list_length (kapp_args e)) -> C) : C := @beta_reduces.rec (fun (s : KExpr) (t : KExpr) (_ : beta_reduces s t) => @Eq (OptionType Name) (kexpr_const_name (kapp_fn s)) (@OptionType.some Name nm) -> Le (list_length (kapp_args s)) (iota_major_index meta) -> (@Eq (OptionType Name) (kexpr_const_name (kapp_fn t)) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args t)) (list_length (kapp_args s)) -> C) -> C) (fun (A0 : KExpr) (body : KExpr) (arg : KExpr) (hh : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app (KExpr.lam A0 body) arg))) (@OptionType.some Name nm)) (hlen : Le (list_length (kapp_args (KExpr.app (KExpr.lam A0 body) arg))) (iota_major_index meta)) (kk : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (instantiate body arg))) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args (instantiate body arg))) (list_length (kapp_args (KExpr.app (KExpr.lam A0 body) arg))) -> C) => option_none_ne_some_type Name nm C hh) (fun (g : KExpr) (g2 : KExpr) (x0 : KExpr) (_hs : beta_reduces g g2) (ih : @Eq (OptionType Name) (kexpr_const_name (kapp_fn g)) (@OptionType.some Name nm) -> Le (list_length (kapp_args g)) (iota_major_index meta) -> (@Eq (OptionType Name) (kexpr_const_name (kapp_fn g2)) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args g2)) (list_length (kapp_args g)) -> C) -> C) (hh : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app g x0))) (@OptionType.some Name nm)) (hlen : Le (list_length (kapp_args (KExpr.app g x0))) (iota_major_index meta)) (kk : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app g2 x0))) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args (KExpr.app g2 x0))) (list_length (kapp_args (KExpr.app g x0))) -> C) => ih hh (le_of_succ_le (list_length (kapp_args g)) (iota_major_index meta) (Eq.substType Nat (fun (z : Nat) => (Le z (iota_major_index meta))) (list_length (kapp_args (KExpr.app g x0))) (Nat.succ (list_length (kapp_args g))) (kapp_args_length_app g x0) hlen)) (fun (hd2 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn g2)) (@OptionType.some Name nm)) (hl2 : @Eq Nat (list_length (kapp_args g2)) (list_length (kapp_args g))) => kk hd2 (@Eq.trans Nat (list_length (kapp_args (KExpr.app g2 x0))) (Nat.succ (list_length (kapp_args g))) (list_length (kapp_args (KExpr.app g x0))) (@Eq.trans Nat (list_length (kapp_args (KExpr.app g2 x0))) (Nat.succ (list_length (kapp_args g2))) (Nat.succ (list_length (kapp_args g))) (kapp_args_length_app g2 x0) (Eq.cong Nat Nat (fun (z : Nat) => (Nat.succ z)) (list_length (kapp_args g2)) (list_length (kapp_args g)) hl2)) (@Eq.symm Nat (list_length (kapp_args (KExpr.app g x0))) (Nat.succ (list_length (kapp_args g))) (kapp_args_length_app g x0))))) (fun (g : KExpr) (x0 : KExpr) (x1 : KExpr) (_hs : beta_reduces x0 x1) (ih : @Eq (OptionType Name) (kexpr_const_name (kapp_fn x0)) (@OptionType.some Name nm) -> Le (list_length (kapp_args x0)) (iota_major_index meta) -> (@Eq (OptionType Name) (kexpr_const_name (kapp_fn x1)) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args x1)) (list_length (kapp_args x0)) -> C) -> C) (hh : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app g x0))) (@OptionType.some Name nm)) (hlen : Le (list_length (kapp_args (KExpr.app g x0))) (iota_major_index meta)) (kk : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app g x1))) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args (KExpr.app g x1))) (list_length (kapp_args (KExpr.app g x0))) -> C) => kk hh (@Eq.trans Nat (list_length (kapp_args (KExpr.app g x1))) (Nat.succ (list_length (kapp_args g))) (list_length (kapp_args (KExpr.app g x0))) (kapp_args_length_app g x1) (@Eq.symm Nat (list_length (kapp_args (KExpr.app g x0))) (Nat.succ (list_length (kapp_args g))) (kapp_args_length_app g x0)))) (fun (ty : KExpr) (ty2 : KExpr) (body : KExpr) (_hs : beta_reduces ty ty2) (ih : @Eq (OptionType Name) (kexpr_const_name (kapp_fn ty)) (@OptionType.some Name nm) -> Le (list_length (kapp_args ty)) (iota_major_index meta) -> (@Eq (OptionType Name) (kexpr_const_name (kapp_fn ty2)) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args ty2)) (list_length (kapp_args ty)) -> C) -> C) (hh : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam ty body))) (@OptionType.some Name nm)) (hlen : Le (list_length (kapp_args (KExpr.lam ty body))) (iota_major_index meta)) (kk : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam ty2 body))) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args (KExpr.lam ty2 body))) (list_length (kapp_args (KExpr.lam ty body))) -> C) => option_none_ne_some_type Name nm C hh) (fun (ty : KExpr) (body : KExpr) (body2 : KExpr) (_hs : beta_reduces body body2) (ih : @Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (@OptionType.some Name nm) -> Le (list_length (kapp_args body)) (iota_major_index meta) -> (@Eq (OptionType Name) (kexpr_const_name (kapp_fn body2)) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args body2)) (list_length (kapp_args body)) -> C) -> C) (hh : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam ty body))) (@OptionType.some Name nm)) (hlen : Le (list_length (kapp_args (KExpr.lam ty body))) (iota_major_index meta)) (kk : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam ty body2))) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args (KExpr.lam ty body2))) (list_length (kapp_args (KExpr.lam ty body))) -> C) => option_none_ne_some_type Name nm C hh) (fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hs : beta_reduces dom dom2) (ih : @Eq (OptionType Name) (kexpr_const_name (kapp_fn dom)) (@OptionType.some Name nm) -> Le (list_length (kapp_args dom)) (iota_major_index meta) -> (@Eq (OptionType Name) (kexpr_const_name (kapp_fn dom2)) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args dom2)) (list_length (kapp_args dom)) -> C) -> C) (hh : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.pi dom body))) (@OptionType.some Name nm)) (hlen : Le (list_length (kapp_args (KExpr.pi dom body))) (iota_major_index meta)) (kk : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.pi dom2 body))) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args (KExpr.pi dom2 body))) (list_length (kapp_args (KExpr.pi dom body))) -> C) => option_none_ne_some_type Name nm C hh) (fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hs : beta_reduces body body2) (ih : @Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (@OptionType.some Name nm) -> Le (list_length (kapp_args body)) (iota_major_index meta) -> (@Eq (OptionType Name) (kexpr_const_name (kapp_fn body2)) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args body2)) (list_length (kapp_args body)) -> C) -> C) (hh : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.pi dom body))) (@OptionType.some Name nm)) (hlen : Le (list_length (kapp_args (KExpr.pi dom body))) (iota_major_index meta)) (kk : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.pi dom body2))) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args (KExpr.pi dom body2))) (list_length (kapp_args (KExpr.pi dom body))) -> C) => option_none_ne_some_type Name nm C hh) (fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hs : beta_reduces dom dom2) (ih : @Eq (OptionType Name) (kexpr_const_name (kapp_fn dom)) (@OptionType.some Name nm) -> Le (list_length (kapp_args dom)) (iota_major_index meta) -> (@Eq (OptionType Name) (kexpr_const_name (kapp_fn dom2)) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args dom2)) (list_length (kapp_args dom)) -> C) -> C) (hh : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.forall_ dom body))) (@OptionType.some Name nm)) (hlen : Le (list_length (kapp_args (KExpr.forall_ dom body))) (iota_major_index meta)) (kk : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.forall_ dom2 body))) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args (KExpr.forall_ dom2 body))) (list_length (kapp_args (KExpr.forall_ dom body))) -> C) => option_none_ne_some_type Name nm C hh) (fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hs : beta_reduces body body2) (ih : @Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (@OptionType.some Name nm) -> Le (list_length (kapp_args body)) (iota_major_index meta) -> (@Eq (OptionType Name) (kexpr_const_name (kapp_fn body2)) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args body2)) (list_length (kapp_args body)) -> C) -> C) (hh : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.forall_ dom body))) (@OptionType.some Name nm)) (hlen : Le (list_length (kapp_args (KExpr.forall_ dom body))) (iota_major_index meta)) (kk : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.forall_ dom body2))) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args (KExpr.forall_ dom body2))) (list_length (kapp_args (KExpr.forall_ dom body))) -> C) => option_none_ne_some_type Name nm C hh) (fun (ty : KExpr) (val : KExpr) (body : KExpr) (hh : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (@OptionType.some Name nm)) (hlen : Le (list_length (kapp_args (KExpr.let_ ty val body))) (iota_major_index meta)) (kk : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (instantiate body val))) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args (instantiate body val))) (list_length (kapp_args (KExpr.let_ ty val body))) -> C) => option_none_ne_some_type Name nm C hh) (fun (ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr) (_hs : beta_reduces ty ty2) (ih : @Eq (OptionType Name) (kexpr_const_name (kapp_fn ty)) (@OptionType.some Name nm) -> Le (list_length (kapp_args ty)) (iota_major_index meta) -> (@Eq (OptionType Name) (kexpr_const_name (kapp_fn ty2)) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args ty2)) (list_length (kapp_args ty)) -> C) -> C) (hh : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (@OptionType.some Name nm)) (hlen : Le (list_length (kapp_args (KExpr.let_ ty val body))) (iota_major_index meta)) (kk : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty2 val body))) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args (KExpr.let_ ty2 val body))) (list_length (kapp_args (KExpr.let_ ty val body))) -> C) => option_none_ne_some_type Name nm C hh) (fun (ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr) (_hs : beta_reduces val val2) (ih : @Eq (OptionType Name) (kexpr_const_name (kapp_fn val)) (@OptionType.some Name nm) -> Le (list_length (kapp_args val)) (iota_major_index meta) -> (@Eq (OptionType Name) (kexpr_const_name (kapp_fn val2)) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args val2)) (list_length (kapp_args val)) -> C) -> C) (hh : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (@OptionType.some Name nm)) (hlen : Le (list_length (kapp_args (KExpr.let_ ty val body))) (iota_major_index meta)) (kk : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val2 body))) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args (KExpr.let_ ty val2 body))) (list_length (kapp_args (KExpr.let_ ty val body))) -> C) => option_none_ne_some_type Name nm C hh) (fun (ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr) (_hs : beta_reduces body body2) (ih : @Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (@OptionType.some Name nm) -> Le (list_length (kapp_args body)) (iota_major_index meta) -> (@Eq (OptionType Name) (kexpr_const_name (kapp_fn body2)) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args body2)) (list_length (kapp_args body)) -> C) -> C) (hh : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (@OptionType.some Name nm)) (hlen : Le (list_length (kapp_args (KExpr.let_ ty val body))) (iota_major_index meta)) (kk : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body2))) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args (KExpr.let_ ty val body2))) (list_length (kapp_args (KExpr.let_ ty val body))) -> C) => option_none_ne_some_type Name nm C hh) (fun (e0 : KExpr) (e02 : KExpr) (hio : iota_reduces e0 e02) (hh : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e0)) (@OptionType.some Name nm)) (hlen : Le (list_length (kapp_args e0)) (iota_major_index meta)) (kk : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e02)) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args e02)) (list_length (kapp_args e0)) -> C) => iota_step_no_reduct_absurd (red_rec the_red_env) e0 e02 C (iota_reduct_none_of_no_major (red_rec the_red_env) e0 nm meta hh hrm (list_head_drop_none_of_le (iota_major_index meta) (kapp_args e0) hlen)) (iota_reduces_to_step e0 e02 hio)) (fun (ps : Name) (pin : Nat) (sub : KExpr) (sub2 : KExpr) (_hs : beta_reduces sub sub2) (ih : @Eq (OptionType Name) (kexpr_const_name (kapp_fn sub)) (@OptionType.some Name nm) -> Le (list_length (kapp_args sub)) (iota_major_index meta) -> (@Eq (OptionType Name) (kexpr_const_name (kapp_fn sub2)) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args sub2)) (list_length (kapp_args sub)) -> C) -> C) (hh : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.proj ps pin sub))) (@OptionType.some Name nm)) (hlen : Le (list_length (kapp_args (KExpr.proj ps pin sub))) (iota_major_index meta)) (kk : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.proj ps pin sub2))) (@OptionType.some Name nm) -> @Eq Nat (list_length (kapp_args (KExpr.proj ps pin sub2))) (list_length (kapp_args (KExpr.proj ps pin sub))) -> C) => option_none_ne_some_type Name nm C hh) e e2 hb hhead hle k".to_string(),
        ));
        rows.push((
            // The capstone: an application whose head is a recursor with FEWER
            // arguments than its major index is `whnf_acc`. Mirrors
            // `whnfAcc_inertApp`'s double `whnf_acc.rec` exactly; what differs
            // is that `whnfAcc_inertApp` hypothesises the head has NO recmeta
            // (dead by name) while this hypothesises it has one and the spine
            // cannot reach it (dead by arity). That is the distinction the
            // under-applied recursor needs and the one no existing lemma made.
            "whnfAcc_deadApp".to_string(),
            "def whnfAcc_deadApp (nm : Name) (meta : RecMeta) (hdef : @Eq (OptionType KExpr) (defval_for (red_def the_red_env) nm) (@OptionType.none KExpr)) (hrm : @Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) nm) (@OptionType.some RecMeta meta)) (sh : KExpr) (hsh : whnf_acc sh) (ar : KExpr) (har : whnf_acc ar) (hhead : @Eq (OptionType Name) (kexpr_const_name (kapp_fn sh)) (@OptionType.some Name nm)) (hlen : Le (Nat.succ (list_length (kapp_args sh))) (iota_major_index meta)) : whnf_acc (KExpr.app sh ar) := @whnf_acc.rec (fun (sh0 : KExpr) (_ : whnf_acc sh0) => @Eq (OptionType Name) (kexpr_const_name (kapp_fn sh0)) (@OptionType.some Name nm) -> Le (Nat.succ (list_length (kapp_args sh0))) (iota_major_index meta) -> forall (a0 : KExpr), whnf_acc a0 -> whnf_acc (KExpr.app sh0 a0)) (fun (sh0 : KExpr) (hsacc : forall (h2 : KExpr), whnf_step sh0 h2 -> whnf_acc h2) (ihH : forall (h2 : KExpr), whnf_step sh0 h2 -> @Eq (OptionType Name) (kexpr_const_name (kapp_fn h2)) (@OptionType.some Name nm) -> Le (Nat.succ (list_length (kapp_args h2))) (iota_major_index meta) -> forall (a0 : KExpr), whnf_acc a0 -> whnf_acc (KExpr.app h2 a0)) => fun (hd0 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn sh0)) (@OptionType.some Name nm)) (hb0 : Le (Nat.succ (list_length (kapp_args sh0))) (iota_major_index meta)) (a0 : KExpr) (ha0 : whnf_acc a0) => @whnf_acc.rec (fun (a1 : KExpr) (_ : whnf_acc a1) => whnf_acc (KExpr.app sh0 a1)) (fun (a1 : KExpr) (haacc : forall (a2 : KExpr), whnf_step a1 a2 -> whnf_acc a2) (ihA : forall (a2 : KExpr), whnf_step a1 a2 -> whnf_acc (KExpr.app sh0 a2)) => whnf_acc.intro (KExpr.app sh0 a1) (fun (e3 : KExpr) (hstep : whnf_step (KExpr.app sh0 a1) e3) => deadApp_step_inv nm hdef sh0 a1 (iota_reduct_none_of_no_major (red_rec the_red_env) (KExpr.app sh0 a1) nm meta hd0 hrm (list_head_drop_none_of_le (iota_major_index meta) (kapp_args (KExpr.app sh0 a1)) (Eq.substType Nat (fun (z : Nat) => (Le z (iota_major_index meta))) (Nat.succ (list_length (kapp_args sh0))) (list_length (kapp_args (KExpr.app sh0 a1))) (@Eq.symm Nat (list_length (kapp_args (KExpr.app sh0 a1))) (Nat.succ (list_length (kapp_args sh0))) (kapp_args_length_app sh0 a1)) hb0))) e3 (whnf_acc e3) hd0 hstep (fun (h2 : KExpr) (hb : beta_reduces sh0 h2) (heq : @Eq KExpr e3 (KExpr.app h2 a1)) => deadHead_beta_pres nm meta hrm sh0 h2 (whnf_acc e3) hb hd0 (le_of_succ_le (list_length (kapp_args sh0)) (iota_major_index meta) hb0) (fun (hd2 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn h2)) (@OptionType.some Name nm)) (hl2 : @Eq Nat (list_length (kapp_args h2)) (list_length (kapp_args sh0))) => Eq.substType KExpr (fun (w : KExpr) => whnf_acc w) (KExpr.app h2 a1) e3 (@Eq.symm KExpr e3 (KExpr.app h2 a1) heq) (ihH h2 (whnf_step.beta sh0 h2 hb) hd2 (Eq.substType Nat (fun (z : Nat) => (Le (Nat.succ z) (iota_major_index meta))) (list_length (kapp_args sh0)) (list_length (kapp_args h2)) (@Eq.symm Nat (list_length (kapp_args h2)) (list_length (kapp_args sh0)) hl2) hb0) a1 (whnf_acc.intro a1 haacc)))) (fun (a2 : KExpr) (hb : beta_reduces a1 a2) (heq : @Eq KExpr e3 (KExpr.app sh0 a2)) => Eq.substType KExpr (fun (w : KExpr) => whnf_acc w) (KExpr.app sh0 a2) e3 (@Eq.symm KExpr e3 (KExpr.app sh0 a2) heq) (ihA a2 (whnf_step.beta a1 a2 hb))))) a0 ha0) sh hsh hhead hlen ar har".to_string(),
        ));
        rows.push((
            // Applying arguments never SHORTENS the spine. `ListType.rec`; nil is
            // `Le.refl`, cons is `le_trans` through `Le.step .. (Le.refl ..)`
            // transported along `kapp_args_length_app`. This is what lets the
            // spine form recover the one-step bound from a bound stated at the
            // RESULT.
            "apply_spine_length_ge".to_string(),
            "def apply_spine_length_ge (l : ListType KExpr) : forall (h : KExpr), Le (list_length (kapp_args h)) (list_length (kapp_args (apply_spine l h))) := @ListType.rec KExpr (fun (l0 : ListType KExpr) => forall (h : KExpr), Le (list_length (kapp_args h)) (list_length (kapp_args (apply_spine l0 h)))) (fun (h : KExpr) => Le.refl (list_length (kapp_args h))) (fun (x : KExpr) (rest : ListType KExpr) (ih : forall (h : KExpr), Le (list_length (kapp_args h)) (list_length (kapp_args (apply_spine rest h)))) => fun (h : KExpr) => le_trans (list_length (kapp_args h)) (list_length (kapp_args (KExpr.app h x))) (list_length (kapp_args (apply_spine rest (KExpr.app h x)))) (Eq.substType Nat (fun (z : Nat) => (Le (list_length (kapp_args h)) z)) (Nat.succ (list_length (kapp_args h))) (list_length (kapp_args (KExpr.app h x))) (@Eq.symm Nat (list_length (kapp_args (KExpr.app h x))) (Nat.succ (list_length (kapp_args h))) (kapp_args_length_app h x)) (Le.step (list_length (kapp_args h)) (list_length (kapp_args h)) (Le.refl (list_length (kapp_args h))))) (ih (KExpr.app h x))) l".to_string(),
        ));
        rows.push((
            // The spine form. `spinePropagate` CANNOT carry it -- its step hypothesis
            // has no access to an arity bound, and the bound STRENGTHENS as the
            // spine grows (it must: once the spine reaches the major index the
            // recursor should fire). Stating the bound at the RESULT is what makes
            // this two lemmas instead of four: the cons arm's hypothesis is already
            // exactly what the IH wants, so `hb` and the head-name pass through
            // untouched and arithmetic is needed only to feed `whnfAcc_deadApp`.
            "whnfAcc_deadSpine".to_string(),
            "def whnfAcc_deadSpine (nm : Name) (meta : RecMeta) (hdef : @Eq (OptionType KExpr) (defval_for (red_def the_red_env) nm) (@OptionType.none KExpr)) (hrm : @Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) nm) (@OptionType.some RecMeta meta)) (xs : ListType KExpr) (hxs : WhnfAccAll xs) : forall (sh : KExpr), whnf_acc sh -> @Eq (OptionType Name) (kexpr_const_name (kapp_fn sh)) (@OptionType.some Name nm) -> Le (list_length (kapp_args (apply_spine xs sh))) (iota_major_index meta) -> whnf_acc (apply_spine xs sh) := @WhnfAccAll.rec (fun (l : ListType KExpr) (_ : WhnfAccAll l) => forall (sh : KExpr), whnf_acc sh -> @Eq (OptionType Name) (kexpr_const_name (kapp_fn sh)) (@OptionType.some Name nm) -> Le (list_length (kapp_args (apply_spine l sh))) (iota_major_index meta) -> whnf_acc (apply_spine l sh)) (fun (sh : KExpr) (hsh : whnf_acc sh) (_hd : @Eq (OptionType Name) (kexpr_const_name (kapp_fn sh)) (@OptionType.some Name nm)) (_hb : Le (list_length (kapp_args (apply_spine (@ListType.nil KExpr) sh))) (iota_major_index meta)) => hsh) (fun (x : KExpr) (rest : ListType KExpr) (hx : whnf_acc x) (_hrest : WhnfAccAll rest) (ih : forall (sh : KExpr), whnf_acc sh -> @Eq (OptionType Name) (kexpr_const_name (kapp_fn sh)) (@OptionType.some Name nm) -> Le (list_length (kapp_args (apply_spine rest sh))) (iota_major_index meta) -> whnf_acc (apply_spine rest sh)) => fun (sh : KExpr) (hsh : whnf_acc sh) (hd : @Eq (OptionType Name) (kexpr_const_name (kapp_fn sh)) (@OptionType.some Name nm)) (hb : Le (list_length (kapp_args (apply_spine (@ListType.cons KExpr x rest) sh))) (iota_major_index meta)) => ih (KExpr.app sh x) (whnfAcc_deadApp nm meta hdef hrm sh hsh x hx hd (Eq.substType Nat (fun (z : Nat) => (Le z (iota_major_index meta))) (list_length (kapp_args (KExpr.app sh x))) (Nat.succ (list_length (kapp_args sh))) (kapp_args_length_app sh x) (le_trans (list_length (kapp_args (KExpr.app sh x))) (list_length (kapp_args (apply_spine rest (KExpr.app sh x)))) (iota_major_index meta) (apply_spine_length_ge rest (KExpr.app sh x)) hb))) hd hb) xs hxs".to_string(),
        ));
        rows.push((
            // Does this reflected recursor have a delta-definition? Asked of the
            // ELABORATOR because a regex could not answer it: the value is
            // `DefEnv.addDef <nested env expr> <name> <value>`, so a pattern
            // anchored on `addDef` walks into the nested parens instead of the
            // name slot -- mine returned 1 name out of 77 applications. If this
            // elaborates, the witness below drops its last hypothesis.
            "probe_kcre92_defval_is_none".to_string(),
            "def probe_kcre92_defval_is_none : @Eq (OptionType KExpr) (defval_for (red_def the_red_env) kcre_name_92) (@OptionType.none KExpr) := @Eq.refl (OptionType KExpr) (@OptionType.none KExpr)".to_string(),
        ));
        rows.push((
            // NON-VACUITY, by an APPLIED instance -- the landing rule aimed at a
            // lemma. `the_red_env` is `kernel_core_red_env`, whose value is a nest
            // of 21 `RecEnv.addRec` applications; `kcre_rec_meta_92` is
            // `RecMeta.mk 0 1 1 0 true _`, so `iota_major_index` is
            // ((0+1)+1)+0 = 2. The major is read AT that index
            // (`list_head (list_drop (iota_major_index mta) (kapp_args e))`,
            // iota_step.rs:150), so the shortest spine that HAS a major is THREE
            // long, and this ONE-argument application is TWO short of it -- its
            // `Le 1 2` bound carries a argument of slack. The TIGHT case is
            // `deadPrefix_spine_witness_is_applied` below, whose 2-long spine
            // closes the bound by `Le.refl`.
            "deadPrefix_witness_is_applied".to_string(),
            "def deadPrefix_witness_is_applied (us : ListType Level) : whnf_acc (KExpr.app (KExpr.const kcre_name_92 us) (KExpr.const kcre_name_92 us)) := whnfAcc_deadApp kcre_name_92 kcre_rec_meta_92 probe_kcre92_defval_is_none (@Eq.refl (OptionType RecMeta) (@OptionType.some RecMeta kcre_rec_meta_92)) (KExpr.const kcre_name_92 us) (whnfAcc_const kcre_name_92 us probe_kcre92_defval_is_none) (KExpr.const kcre_name_92 us) (whnfAcc_const kcre_name_92 us probe_kcre92_defval_is_none) (@Eq.refl (OptionType Name) (@OptionType.some Name kcre_name_92)) (Le.step (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Le.refl (Nat.succ Nat.zero)))".to_string(),
        ));
        rows.push((
            // THE LANDING RULE, for the SPINE form. `whnfAcc_deadApp` had an
            // applied witness; `whnfAcc_deadSpine` did not, and a lemma with no
            // caller is the thing this tree keeps catching.
            //
            // Deliberately the BOUNDARY case: `kcre_rec_meta_92` has
            // `iota_major_index` 2, and the spine here is exactly 2 long, so
            // `Le 2 2` closes by `Le.refl`. That is the last configuration
            // before iota could fire -- one more argument and the recursor
            // reaches its major premise, so if the bound were off by one in the
            // permissive direction this witness is where it would show.
            "deadPrefix_spine_witness_is_applied".to_string(),
            "def deadPrefix_spine_witness_is_applied (us : ListType Level) : whnf_acc (apply_spine (@ListType.cons KExpr (KExpr.const kcre_name_92 us) (@ListType.cons KExpr (KExpr.const kcre_name_92 us) (@ListType.nil KExpr))) (KExpr.const kcre_name_92 us)) := whnfAcc_deadSpine kcre_name_92 kcre_rec_meta_92 probe_kcre92_defval_is_none (@Eq.refl (OptionType RecMeta) (@OptionType.some RecMeta kcre_rec_meta_92)) (@ListType.cons KExpr (KExpr.const kcre_name_92 us) (@ListType.cons KExpr (KExpr.const kcre_name_92 us) (@ListType.nil KExpr))) (WhnfAccAll.cons (KExpr.const kcre_name_92 us) (@ListType.cons KExpr (KExpr.const kcre_name_92 us) (@ListType.nil KExpr)) (whnfAcc_const kcre_name_92 us probe_kcre92_defval_is_none) (WhnfAccAll.cons (KExpr.const kcre_name_92 us) (@ListType.nil KExpr) (whnfAcc_const kcre_name_92 us probe_kcre92_defval_is_none) WhnfAccAll.nil)) (KExpr.const kcre_name_92 us) (whnfAcc_const kcre_name_92 us probe_kcre92_defval_is_none) (@Eq.refl (OptionType Name) (@OptionType.some Name kcre_name_92)) (Le.refl (Nat.succ (Nat.succ Nat.zero)))".to_string(),
        ));
        rows
    }

    /// Does this elaborator refute an impossible constructor by INDEX CLASH?
    ///
    /// Deliberately a SEPARATE source vector with a disjoint dependency set,
    /// not two more arms on `candmodel_dep_pi_sources`. That probe already
    /// peaks at 3.62 GB of this box's 4 GB gate budget, and the driver of that
    /// cost is how many dependency vecs a single test registers, not how many
    /// arms it has. These two constants need `beta_reduces` and
    /// `ConstFreeUnit`; they need none of `xval` / `WKC` / `VD`.
    ///
    /// What turns on the answer: cr3 at `PiSetDep` must invert a step out of
    /// `KExpr.app t a`. `beta_reduces` has FIFTEEN constructors, of which only
    /// `app_left`, `app_right`, `beta` and `iota` can have an `app` on the
    /// left. If the elaborator discharges the other eleven itself, that
    /// inversion is four cases; if not, each of the eleven needs a hand-written
    /// head discriminator in the `r9_sort_discr` / `r11_pi_discr` idiom.
    ///
    /// NOTHING in this tree currently measures it. All three existing `match`es
    /// on a step relation (`natStep`, `roseStep`, `genStep`) scrutinise a
    /// two-constructor inductive at an UNCONSTRAINED index, where refutation
    /// never arises.
    #[cfg(test)]
    pub(super) fn candmodel_beta_match_sources() -> Vec<(String, String)> {
        vec![
            (
                // CONTROL. Same match, UNCONSTRAINED index, all fifteen arms
                // listed. Its only job is to fix the pattern syntax and arity,
                // so a failure in the measurement below cannot be misread as an
                // index-refutation failure when it is really a spelling error.
                // Same discipline CLAUDE.md requires of a `-Ztrust-policy`
                // probe: without a control it measures nothing.
                "beta_match_control".to_string(),
                "def beta_match_control (e : KExpr) (y : KExpr) \
                 (h : beta_reduces e y) : ConstFreeUnit := \
                 match h with \
                 | beta_reduces.beta A body arg => ConstFreeUnit.triv \
                 | beta_reduces.app_left f f2 aa hf => ConstFreeUnit.triv \
                 | beta_reduces.app_right f aa aa2 ha => ConstFreeUnit.triv \
                 | beta_reduces.lam_ty ty ty2 body hty => ConstFreeUnit.triv \
                 | beta_reduces.lam_body ty body body2 hb => ConstFreeUnit.triv \
                 | beta_reduces.pi_dom dom dom2 body hd => ConstFreeUnit.triv \
                 | beta_reduces.pi_cod dom body body2 hb => ConstFreeUnit.triv \
                 | beta_reduces.forall_congr_dom dom dom2 body hd => ConstFreeUnit.triv \
                 | beta_reduces.forall_congr_cod dom body body2 hb => ConstFreeUnit.triv \
                 | beta_reduces.zeta ty val body => ConstFreeUnit.triv \
                 | beta_reduces.let_ty ty ty2 val body hty => ConstFreeUnit.triv \
                 | beta_reduces.let_val ty val val2 body hv => ConstFreeUnit.triv \
                 | beta_reduces.let_body ty val body body2 hb => ConstFreeUnit.triv \
                 | beta_reduces.iota ee ee2 hi => ConstFreeUnit.triv \
                 | beta_reduces.proj sn i sub sub2 hs => ConstFreeUnit.triv"
                    .to_string(),
            ),
            (
                // THE MEASUREMENT. Index PINNED to `KExpr.app t a`, and only the
                // four arms whose left-hand side can be an `app` are listed. The
                // other eleven are omitted deliberately.
                "beta_app_index_refutation_probe".to_string(),
                "def beta_app_index_refutation_probe (t : KExpr) (a : KExpr) (y : KExpr) \
                 (h : beta_reduces (KExpr.app t a) y) : ConstFreeUnit := \
                 match h with \
                 | beta_reduces.beta A body arg => ConstFreeUnit.triv \
                 | beta_reduces.app_left f f2 aa hf => ConstFreeUnit.triv \
                 | beta_reduces.app_right f aa aa2 ha => ConstFreeUnit.triv \
                 | beta_reduces.iota ee ee2 hi => ConstFreeUnit.triv"
                    .to_string(),
            ),
        ]
    }
}

impl Specification {
    /// THE APP-INVERSION, adapted from a template this tree already had.
    ///
    /// Found rather than invented: `candmodel_construct_r2.rs` carries a
    /// complete fifteen-arm `beta_reduces.rec` inversion at an app target
    /// (`r2_witness_no_beta`), and `expr_model_discrimination.rs` carries the
    /// head-clash and injectivity lemmas it uses. This constant is that
    /// template with the target generalised from a fixture to the variables
    /// `gt`/`gx`, and with the three app arms handing control to
    /// continuations instead of refuting.
    ///
    /// Everything it leans on is pre-existing and proved: `lam_ne_app`,
    /// `pi_ne_app`, `let_ne_app`, `proj_ne_app`, `app_inj_fst`,
    /// `app_inj_snd`. I had written my own `kexpr_not_app`, `head_clash_app`,
    /// `appFnOf`/`appArgOf` and `app_inj_fn`/`app_inj_arg` before finding
    /// them; all six are deleted here.
    ///
    /// Two details taken from the template rather than guessed:
    /// * the `forall_congr_*` arms are discharged by `pi_ne_app`, so
    ///   `KExpr.forall_` unfolds to `KExpr.pi` — it is not a tenth `KExpr`
    ///   constructor, and `Neutral`s nine-arm `KExpr.rec` agrees;
    /// * the motive carries TWO equations, one per index. R2 needed only the
    ///   first because its conclusion never mentions the reduct; the
    ///   continuations here do, so the second is what lets an arm say
    ///   anything about `e2`.
    #[cfg(test)]
    pub(super) fn candmodel_app_inversion_sources() -> Vec<(String, String)> {
        // `PiSetDep` is pulled from the dep-pi vector rather than respelled, so
        // cr3 here is measured against the SAME candidate notion cr1 and cr2
        // were. A second copy of that definition could drift from it silently.
        let mut items: Vec<(String, String)> = Self::candmodel_dep_pi_sources()
            .into_iter()
            .filter(|(n, _)| n == "PiSetDep")
            .collect();
        items.push((
            "beta_app_inv".to_string(),
            "def beta_app_inv (gt : KExpr) (gx : KExpr) (e2 : KExpr) (C : Type) (kbeta : forall (A0 : KExpr) (bd : KExpr) (ag : KExpr), @Eq KExpr (KExpr.lam A0 bd) gt -> C) (kleft : forall (f2 : KExpr), beta_reduces gt f2 -> @Eq KExpr e2 (KExpr.app f2 gx) -> C) (kright : forall (a2 : KExpr), beta_reduces gx a2 -> @Eq KExpr e2 (KExpr.app gt a2) -> C) (kiota : iota_reduces (KExpr.app gt gx) e2 -> C) (hbr : beta_reduces (KExpr.app gt gx) e2) : C := @beta_reduces.rec (fun (s : KExpr) (t : KExpr) (_hb : beta_reduces s t) => @Eq KExpr s (KExpr.app gt gx) -> @Eq KExpr t e2 -> C) (fun (A0 : KExpr) (bd : KExpr) (ag : KExpr) (h1 : @Eq KExpr (KExpr.app (KExpr.lam A0 bd) ag) (KExpr.app gt gx)) (_h2 : @Eq KExpr (instantiate bd ag) e2) => kbeta A0 bd ag (app_inj_fst (KExpr.lam A0 bd) ag gt gx h1)) (fun (f : KExpr) (f2 : KExpr) (a : KExpr) (hst : beta_reduces f f2) (_ih : @Eq KExpr f (KExpr.app gt gx) -> @Eq KExpr f2 e2 -> C) (h1 : @Eq KExpr (KExpr.app f a) (KExpr.app gt gx)) (h2 : @Eq KExpr (KExpr.app f2 a) e2) => kleft f2 (@Eq.rec KExpr f (fun (x : KExpr) (_q : @Eq KExpr f x) => beta_reduces x f2) hst gt (app_inj_fst f a gt gx h1)) (@Eq.trans KExpr e2 (KExpr.app f2 a) (KExpr.app f2 gx) (@Eq.symm KExpr (KExpr.app f2 a) e2 h2) (Eq.cong KExpr KExpr (fun (z : KExpr) => KExpr.app f2 z) a gx (app_inj_snd f a gt gx h1)))) (fun (f : KExpr) (a : KExpr) (a2 : KExpr) (hst : beta_reduces a a2) (_ih : @Eq KExpr a (KExpr.app gt gx) -> @Eq KExpr a2 e2 -> C) (h1 : @Eq KExpr (KExpr.app f a) (KExpr.app gt gx)) (h2 : @Eq KExpr (KExpr.app f a2) e2) => kright a2 (@Eq.rec KExpr a (fun (x : KExpr) (_q : @Eq KExpr a x) => beta_reduces x a2) hst gx (app_inj_snd f a gt gx h1)) (@Eq.trans KExpr e2 (KExpr.app f a2) (KExpr.app gt a2) (@Eq.symm KExpr (KExpr.app f a2) e2 h2) (Eq.cong KExpr KExpr (fun (z : KExpr) => KExpr.app z a2) f gt (app_inj_fst f a gt gx h1)))) (fun (ty : KExpr) (ty2 : KExpr) (bd : KExpr) (_hst : beta_reduces ty ty2) (_ih : @Eq KExpr ty (KExpr.app gt gx) -> @Eq KExpr ty2 e2 -> C) (h1 : @Eq KExpr (KExpr.lam ty bd) (KExpr.app gt gx)) (_h2 : @Eq KExpr (KExpr.lam ty2 bd) e2) => lam_ne_app ty bd gt gx C h1) (fun (ty : KExpr) (bd : KExpr) (bd2 : KExpr) (_hst : beta_reduces bd bd2) (_ih : @Eq KExpr bd (KExpr.app gt gx) -> @Eq KExpr bd2 e2 -> C) (h1 : @Eq KExpr (KExpr.lam ty bd) (KExpr.app gt gx)) (_h2 : @Eq KExpr (KExpr.lam ty bd2) e2) => lam_ne_app ty bd gt gx C h1) (fun (dm : KExpr) (dm2 : KExpr) (bd : KExpr) (_hst : beta_reduces dm dm2) (_ih : @Eq KExpr dm (KExpr.app gt gx) -> @Eq KExpr dm2 e2 -> C) (h1 : @Eq KExpr (KExpr.pi dm bd) (KExpr.app gt gx)) (_h2 : @Eq KExpr (KExpr.pi dm2 bd) e2) => pi_ne_app dm bd gt gx C h1) (fun (dm : KExpr) (bd : KExpr) (bd2 : KExpr) (_hst : beta_reduces bd bd2) (_ih : @Eq KExpr bd (KExpr.app gt gx) -> @Eq KExpr bd2 e2 -> C) (h1 : @Eq KExpr (KExpr.pi dm bd) (KExpr.app gt gx)) (_h2 : @Eq KExpr (KExpr.pi dm bd2) e2) => pi_ne_app dm bd gt gx C h1) (fun (dm : KExpr) (dm2 : KExpr) (bd : KExpr) (_hst : beta_reduces dm dm2) (_ih : @Eq KExpr dm (KExpr.app gt gx) -> @Eq KExpr dm2 e2 -> C) (h1 : @Eq KExpr (KExpr.forall_ dm bd) (KExpr.app gt gx)) (_h2 : @Eq KExpr (KExpr.forall_ dm2 bd) e2) => pi_ne_app dm bd gt gx C h1) (fun (dm : KExpr) (bd : KExpr) (bd2 : KExpr) (_hst : beta_reduces bd bd2) (_ih : @Eq KExpr bd (KExpr.app gt gx) -> @Eq KExpr bd2 e2 -> C) (h1 : @Eq KExpr (KExpr.forall_ dm bd) (KExpr.app gt gx)) (_h2 : @Eq KExpr (KExpr.forall_ dm bd2) e2) => pi_ne_app dm bd gt gx C h1) (fun (ty : KExpr) (vl : KExpr) (bd : KExpr) (h1 : @Eq KExpr (KExpr.let_ ty vl bd) (KExpr.app gt gx)) (_h2 : @Eq KExpr (instantiate bd vl) e2) => let_ne_app ty vl bd gt gx C h1) (fun (ty : KExpr) (ty2 : KExpr) (vl : KExpr) (bd : KExpr) (_hst : beta_reduces ty ty2) (_ih : @Eq KExpr ty (KExpr.app gt gx) -> @Eq KExpr ty2 e2 -> C) (h1 : @Eq KExpr (KExpr.let_ ty vl bd) (KExpr.app gt gx)) (_h2 : @Eq KExpr (KExpr.let_ ty2 vl bd) e2) => let_ne_app ty vl bd gt gx C h1) (fun (ty : KExpr) (vl : KExpr) (vl2 : KExpr) (bd : KExpr) (_hst : beta_reduces vl vl2) (_ih : @Eq KExpr vl (KExpr.app gt gx) -> @Eq KExpr vl2 e2 -> C) (h1 : @Eq KExpr (KExpr.let_ ty vl bd) (KExpr.app gt gx)) (_h2 : @Eq KExpr (KExpr.let_ ty vl2 bd) e2) => let_ne_app ty vl bd gt gx C h1) (fun (ty : KExpr) (vl : KExpr) (bd : KExpr) (bd2 : KExpr) (_hst : beta_reduces bd bd2) (_ih : @Eq KExpr bd (KExpr.app gt gx) -> @Eq KExpr bd2 e2 -> C) (h1 : @Eq KExpr (KExpr.let_ ty vl bd) (KExpr.app gt gx)) (_h2 : @Eq KExpr (KExpr.let_ ty vl bd2) e2) => let_ne_app ty vl bd gt gx C h1) (fun (e0 : KExpr) (e02 : KExpr) (hio : iota_reduces e0 e02) (h1 : @Eq KExpr e0 (KExpr.app gt gx)) (h2 : @Eq KExpr e02 e2) => kiota (@Eq.rec KExpr e02 (fun (y : KExpr) (_q : @Eq KExpr e02 y) => iota_reduces (KExpr.app gt gx) y) (@Eq.rec KExpr e0 (fun (x : KExpr) (_q : @Eq KExpr e0 x) => iota_reduces x e02) hio (KExpr.app gt gx) h1) e2 h2)) (fun (ps : Name) (pin : Nat) (sb : KExpr) (sb2 : KExpr) (_hst : beta_reduces sb sb2) (_ih : @Eq KExpr sb (KExpr.app gt gx) -> @Eq KExpr sb2 e2 -> C) (h1 : @Eq KExpr (KExpr.proj ps pin sb) (KExpr.app gt gx)) (_h2 : @Eq KExpr (KExpr.proj ps pin sb2) e2) => proj_ne_app ps pin sb gt gx C h1) (KExpr.app gt gx) e2 hbr (@Eq.refl KExpr (KExpr.app gt gx)) (@Eq.refl KExpr e2)"
                .to_string(),
        ));
        items.push((
            // cr3 AT `PiSetDep`, on `beta_app_inv`. Induction is `whnf_acc.rec`
            // on the ARGUMENT, its accessibility supplied by CA's own cr1, so
            // the induction costs no new premise. Neutrality of `app t x` is
            // free — `Neutral`s `app` arm is unconditional — so CB's cr3 is
            // stated without one.
            //
            // The four cases: `beta` refuted by `hnlam`; `app_left` from the
            // law's own premise, transported along the reduct equation;
            // `app_right` from the IH, with `r21_xval_step` moving the CODOMAIN
            // INDEX back from `xval .. a2` to `xval .. x` — the transport this
            // whole dependent route turned on, and which was already proved;
            // `iota` and `whnf_step.delta` from `hni`/`hnd`.
            //
            // `hnlam` rather than `Neutral t`: the beta case needs "t is not a
            // lam" in USABLE form, and `Neutral` is a `KExpr.rec` definition
            // that may be registered Opaque — in which case it would not
            // compute to `Empty` and would fail exactly as `head_clash_app`
            // did. Stating the refutation principle directly sidesteps that and
            // is implied by neutrality. `hnd`/`hni` are the PREDICTED
            // delta/iota-freedom side condition: `Neutral`s `konst` arm is
            // unconditional, so a neutral `t` may be a constant WITH a
            // definition and `app t x` can then step at the head.
            "piSetDep_cr3".to_string(),
            "def piSetDep_cr3 (D : Nat -> Sk) (d : Sk) (r : VEnvD D) (CA : KExpr -> Type) (CB : VD d -> KExpr -> Type) (t : KExpr) (hCAsn : forall (x : KExpr), CA x -> whnf_acc x) (hCAcr2 : forall (x : KExpr) (y : KExpr), CA x -> whnf_step x y -> CA y) (hCBcr3 : forall (v : VD d) (x : KExpr), (forall (y : KExpr), whnf_step x y -> CB v y) -> CB v x) (hnlam : forall (A0 : KExpr) (bd : KExpr) (R : Type), @Eq KExpr (KExpr.lam A0 bd) t -> R) (hnd : forall (x : KExpr) (y : KExpr) (R : Type), delta_reduces (KExpr.app t x) y -> R) (hni : forall (x : KExpr) (y : KExpr) (R : Type), iota_reduces (KExpr.app t x) y -> R) (hstep : forall (t2 : KExpr), whnf_step t t2 -> PiSetDep D d r CA CB t2) : PiSetDep D d r CA CB t := fun (a : KExpr) (ha : WKC D a d) (hca : CA a) => @whnf_acc.rec (fun (x : KExpr) (_hx : whnf_acc x) => forall (hx : WKC D x d), CA x -> CB (xval D x d hx r) (KExpr.app t x)) (fun (x : KExpr) (_f : forall (y : KExpr), whnf_step x y -> whnf_acc y) (ih : forall (y : KExpr), whnf_step x y -> forall (hy : WKC D y d), CA y -> CB (xval D y d hy r) (KExpr.app t y)) (hx : WKC D x d) (hcx : CA x) => hCBcr3 (xval D x d hx r) (KExpr.app t x) (fun (y : KExpr) (st : whnf_step (KExpr.app t x) y) => match st with | whnf_step.delta hd => hnd x y (CB (xval D x d hx r) y) hd | whnf_step.beta hb => beta_app_inv t x y (CB (xval D x d hx r) y) (fun (A0 : KExpr) (bd : KExpr) (_ag : KExpr) (heq : @Eq KExpr (KExpr.lam A0 bd) t) => hnlam A0 bd (CB (xval D x d hx r) y) heq) (fun (f2 : KExpr) (hst : beta_reduces t f2) (heq : @Eq KExpr y (KExpr.app f2 x)) => Eq.substType KExpr (fun (z : KExpr) => CB (xval D x d hx r) z) (KExpr.app f2 x) y (@Eq.symm KExpr y (KExpr.app f2 x) heq) (hstep f2 (whnf_step.beta t f2 hst) x hx hcx)) (fun (a2 : KExpr) (hst : beta_reduces x a2) (heq : @Eq KExpr y (KExpr.app t a2)) => Eq.substType KExpr (fun (z : KExpr) => CB (xval D x d hx r) z) (KExpr.app t a2) y (@Eq.symm KExpr y (KExpr.app t a2) heq) (Eq.substType (VD d) (fun (v : VD d) => CB v (KExpr.app t a2)) (xval D a2 d (wkc_step D x d hx a2 (whnf_step.beta x a2 hst)) r) (xval D x d hx r) (r21_xval_step D x d hx a2 (whnf_step.beta x a2 hst) (wkc_step D x d hx a2 (whnf_step.beta x a2 hst)) r) (ih a2 (whnf_step.beta x a2 hst) (wkc_step D x d hx a2 (whnf_step.beta x a2 hst)) (hCAcr2 x a2 hcx (whnf_step.beta x a2 hst))))) (fun (hio : iota_reduces (KExpr.app t x) y) => hni x y (CB (xval D x d hx r) y) hio) hb)) a (hCAsn a hca) ha hca"
                .to_string(),
        ));
        items.push((
            // Does `Neutral` UNFOLD? cr3 took `hnlam` to route around the
            // possibility that it is registered Opaque like `kexpr_not_app`.
            // This asks the question directly instead: `Neutral (lam A b)`
            // should compute to `Empty` through `Neutral`s `KExpr.rec`.
            //
            // If it fails, `Neutral` is Opaque and `hnlam` was necessary rather
            // than merely cautious. If it passes, cr3 can take the FIELD's own
            // premise — which is what the constant after it does.
            "neutral_lam_is_empty".to_string(),
            "def neutral_lam_is_empty (A : KExpr) (b : KExpr) (C : Type) \
             (hn : Neutral (KExpr.lam A b)) : C := \
             @Empty.rec (fun (_e : Empty) => C) hn"
                .to_string(),
        ));
        items.push((
            // cr3 WITH THE TELESCOPE'S OWN PREMISE. `CandModel`'s cr3 field
            // gives `Neutral e`, not "e is not a lam", so a cr3 stated at
            // `Neutral t` is materially closer to the law than `piSetDep_cr3`
            // is. It transports `hn` along the inversion's equation and
            // eliminates the resulting `Neutral (lam A0 bd)` as `Empty`.
            //
            // Depends on the probe above: if `Neutral` does not unfold, this
            // cannot elaborate and `hnlam` stays the honest spelling.
            "piSetDep_cr3_neutral".to_string(),
            "def piSetDep_cr3_neutral (D : Nat -> Sk) (d : Sk) (r : VEnvD D) (CA : KExpr -> Type) (CB : VD d -> KExpr -> Type) (t : KExpr) (hCAsn : forall (x : KExpr), CA x -> whnf_acc x) (hCAcr2 : forall (x : KExpr) (y : KExpr), CA x -> whnf_step x y -> CA y) (hCBcr3 : forall (v : VD d) (x : KExpr), (forall (y : KExpr), whnf_step x y -> CB v y) -> CB v x) (hn : Neutral t) (hnd : forall (x : KExpr) (y : KExpr) (R : Type), delta_reduces (KExpr.app t x) y -> R) (hni : forall (x : KExpr) (y : KExpr) (R : Type), iota_reduces (KExpr.app t x) y -> R) (hstep : forall (t2 : KExpr), whnf_step t t2 -> PiSetDep D d r CA CB t2) : PiSetDep D d r CA CB t := fun (a : KExpr) (ha : WKC D a d) (hca : CA a) => @whnf_acc.rec (fun (x : KExpr) (_hx : whnf_acc x) => forall (hx : WKC D x d), CA x -> CB (xval D x d hx r) (KExpr.app t x)) (fun (x : KExpr) (_f : forall (y : KExpr), whnf_step x y -> whnf_acc y) (ih : forall (y : KExpr), whnf_step x y -> forall (hy : WKC D y d), CA y -> CB (xval D y d hy r) (KExpr.app t y)) (hx : WKC D x d) (hcx : CA x) => hCBcr3 (xval D x d hx r) (KExpr.app t x) (fun (y : KExpr) (st : whnf_step (KExpr.app t x) y) => match st with | whnf_step.delta hd => hnd x y (CB (xval D x d hx r) y) hd | whnf_step.beta hb => beta_app_inv t x y (CB (xval D x d hx r) y) (fun (A0 : KExpr) (bd : KExpr) (_ag : KExpr) (heq : @Eq KExpr (KExpr.lam A0 bd) t) => @Empty.rec (fun (_e : Empty) => (CB (xval D x d hx r) y)) (Eq.substType KExpr Neutral t (KExpr.lam A0 bd) (@Eq.symm KExpr (KExpr.lam A0 bd) t heq) hn)) (fun (f2 : KExpr) (hst : beta_reduces t f2) (heq : @Eq KExpr y (KExpr.app f2 x)) => Eq.substType KExpr (fun (z : KExpr) => CB (xval D x d hx r) z) (KExpr.app f2 x) y (@Eq.symm KExpr y (KExpr.app f2 x) heq) (hstep f2 (whnf_step.beta t f2 hst) x hx hcx)) (fun (a2 : KExpr) (hst : beta_reduces x a2) (heq : @Eq KExpr y (KExpr.app t a2)) => Eq.substType KExpr (fun (z : KExpr) => CB (xval D x d hx r) z) (KExpr.app t a2) y (@Eq.symm KExpr y (KExpr.app t a2) heq) (Eq.substType (VD d) (fun (v : VD d) => CB v (KExpr.app t a2)) (xval D a2 d (wkc_step D x d hx a2 (whnf_step.beta x a2 hst)) r) (xval D x d hx r) (r21_xval_step D x d hx a2 (whnf_step.beta x a2 hst) (wkc_step D x d hx a2 (whnf_step.beta x a2 hst)) r) (ih a2 (whnf_step.beta x a2 hst) (wkc_step D x d hx a2 (whnf_step.beta x a2 hst)) (hCAcr2 x a2 hcx (whnf_step.beta x a2 hst))))) (fun (hio : iota_reduces (KExpr.app t x) y) => hni x y (CB (xval D x d hx r) y) hio) hb)) a (hCAsn a hca) ha hca"
                .to_string(),
        ));
        items.push((
            // THE STEP-INDEXED `xval` — the decisive structural probe.
            //
            // `m_pi` cannot name `xval` because it is an arm of the `WKC.rec`
            // that DEFINES it, and the argument `qa` is an arbitrary term, not
            // a subterm of `pi A B`. That is the whole obstruction to a
            // dependent `m_pi`, and it is the same non-structurality §3h
            // identifies for `pi_elim`.
            //
            // The fix `RedN` used there: recur on a `Nat` and DROP the index on
            // the recursive call, so the pi arm never needs a subterm. Here the
            // outer recursion is `Nat.rec`; at `succ`, `m_pi` conses
            // `qih qD qa (domSk qsA) qha qr` — the index-`m` interpretation of
            // the ARGUMENT — exactly where stock `xval` conses
            // `junkD (domSk qsA)`.
            //
            // Every other arm is copied from `xval` verbatim, so a failure is
            // about the pi arm or about the `Nat.rec`/`WKC.rec` nesting and not
            // about the model. Note `m_lam` and `m_let` ALREADY cons real
            // values (`qx`, `qihv qr`); `m_pi` was the only arm passing junk,
            // which is why this is a one-arm change.
            //
            // `r20_xval_inst` certifies the semantics of that slot: the
            // interpretation of `instantiate b a` IS the interpretation of `b`
            // in an environment extended by `xval` of `a`. So if this
            // elaborates, the dependent arm is not merely well-typed, it is the
            // right value.
            //
            // NOT claimed by a green here: that `xvalN` agrees with `xval`, or
            // that its limit over `n` exists. This measures ONE thing — whether
            // step-indexing dissolves the self-reference.
            "xvalN".to_string(),
            "def xvalN (n : Nat) : forall (qD : Nat -> Sk) (qe : KExpr) (qs : Sk), WKC qD qe qs -> VEnvD qD -> VD qs := @Nat.rec (fun (qn : Nat) => forall (qD : Nat -> Sk) (qe : KExpr) (qs : Sk), WKC qD qe qs -> VEnvD qD -> VD qs) (fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WKC qD qe qs) (qr : VEnvD qD) => junkD qs) (fun (qm : Nat) (qih : forall (qD : Nat -> Sk) (qe : KExpr) (qs : Sk), WKC qD qe qs -> VEnvD qD -> VD qs) (zD : Nat -> Sk) (ze : KExpr) (zs : Sk) (zh : WKC zD ze zs) (zr : VEnvD zD) => @WKC.rec (fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WKC qD qe qs) => VEnvD qD -> VD qs) (fun (qD : Nat -> Sk) (qi : Nat) (qr : VEnvD qD) => qr qi) (fun (qD : Nat -> Sk) (qn : Level) (qr : VEnvD qD) (qe : KExpr) => whnf_acc qe) (fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WKC qD qA qsA) (qhB : WKC (skcons (domSk qsA) qD) qB qsB) (qihA : VEnvD qD -> VD qsA) (qihB : VEnvD (skcons (domSk qsA) qD) -> VD qsB) (qr : VEnvD qD) => mkTyD qsA qsB (fun (qt : KExpr) => forall (qa : KExpr) (qha : WKC qD qa (domSk qsA)), vcarD qsA (qihA qr) qa -> vcarD qsB (qihB (vconsD (domSk qsA) qD (qih qD qa (domSk qsA) qha qr) qr)) (KExpr.app qt qa))) (fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WKC qD qA qsA) (qhb : WKC (skcons (domSk qsA) qD) qb qc) (qihA : VEnvD qD -> VD qsA) (qihb : VEnvD (skcons (domSk qsA) qD) -> VD qc) (qr : VEnvD qD) (qx : VD (domSk qsA)) => qihb (vconsD (domSk qsA) qD qx qr)) (fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WKC qD qf (Sk.arr qd qcc)) (qha : WKC qD qa qd) (qihf : VEnvD qD -> VD (Sk.arr qd qcc)) (qiha : VEnvD qD -> VD qd) (qr : VEnvD qD) => qihf qr (qiha qr)) (fun (qD : Nat -> Sk) (qn : Name) (qus : ListType Level) (qhd : @Eq (OptionType KExpr) (defval_for (red_def the_red_env) qn) (@OptionType.none KExpr)) (qhr : @Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) qn) (@OptionType.none RecMeta)) (qr : VEnvD qD) (qe : KExpr) => whnf_acc qe) (fun (qD : Nat -> Sk) (qt : KExpr) (qv : KExpr) (qb : KExpr) (qst : Sk) (qsv : Sk) (qc : Sk) (qht : WKC qD qt qst) (qhv : WKC qD qv qsv) (qhb : WKC (skcons qsv qD) qb qc) (qiht : VEnvD qD -> VD qst) (qihv : VEnvD qD -> VD qsv) (qihb : VEnvD (skcons qsv qD) -> VD qc) (qr : VEnvD qD) => qihb (vconsD qsv qD (qihv qr) qr)) zD ze zs zh zr) n"
                .to_string(),
        ));
        items.push((
            // THE LIMIT of a step-indexed family, shape-directed.
            //
            // `xvalN` (if it elaborates) gives a family indexed by `n`; the
            // model needs ONE value. Intersecting is directed by `VD`'s own
            // `Sk.rec`, because `VD` is not uniform:
            //
            //   VD Sk.ty      = KExpr -> Type    -> intersect pointwise over n
            //   VD (Sk.kd s)  = KExpr -> Type    -> same
            //   VD (Sk.arr d c) = VD d -> VD c   -> recurse on the CODOMAIN
            //
            // Independent of `xvalN` — it is a statement about `VD` alone — so
            // it is measured in the same run whichever way `xvalN` goes. A
            // green means the limit is EXPRESSIBLE, nothing more: that
            // `interD s (fun n => xvalN n ..)` satisfies any model law is a
            // separate question, and the arrow case is where a naive
            // intersection would be expected to fail first, since it must
            // commute with application.
            "interD".to_string(),
            "def interD (s : Sk) (f : Nat -> VD s) : VD s := @Sk.rec (fun (qs : Sk) => (Nat -> VD qs) -> VD qs) (fun (qf : Nat -> VD Sk.ty) (qe : KExpr) => forall (qn : Nat), qf qn qe) (fun (qs1 : Sk) (qih : (Nat -> VD qs1) -> VD qs1) (qf : Nat -> VD (Sk.kd qs1)) (qe : KExpr) => forall (qn : Nat), qf qn qe) (fun (qd : Sk) (qc : Sk) (qihd : (Nat -> VD qd) -> VD qd) (qihc : (Nat -> VD qc) -> VD qc) (qf : Nat -> VD (Sk.arr qd qc)) (qx : VD qd) => qihc (fun (qn : Nat) => qf qn qx)) s f"
                .to_string(),
        ));
        items.push((
            // cr1 AT THE LIMIT, and it should be a PROJECTION, not a proof.
            //
            // The base case of `xvalN` is `junkD`, and `junkD Sk.ty` is
            // `fun qe => whnf_acc qe`. The limit intersects over ALL `n`
            // INCLUDING 0, so projecting the limit at index 0 lands directly in
            // `whnf_acc`. If this elaborates as the bare `hm Nat.zero`, cr1
            // holds at the limit at every shape by construction rather than by
            // argument — an accident of choosing `junkD` as the obvious default
            // for the base case, which turns out to be the right default for a
            // reducibility model.
            "xvalInf_cr1_ty".to_string(),
            "def xvalInf_cr1_ty (D : Nat -> Sk) (e0 : KExpr) (h : WKC D e0 Sk.ty) (r : VEnvD D) (t : KExpr) (hm : interD Sk.ty (fun (qn : Nat) => xvalN qn D e0 Sk.ty h r) t) : whnf_acc t := hm Nat.zero"
                .to_string(),
        ));
        items.push((
            // IS THE LIMIT INHABITED? This is the question that decides whether
            // the whole step-indexed construction is vacuous.
            //
            // Nothing in this tree has ever intersected a step-indexed family
            // at a NON-propositional type — `RedStep`/`RedWStep` intersect at a
            // small `Type` after full application — and `RedW` is on record as
            // monotone in the index in NEITHER direction, which is exactly the
            // property a limit wants. So an empty limit was a live possibility.
            //
            // Stated against the REAL constructor `WKC.sort D u`, whose shape
            // is `Sk.kd Sk.ty`, rather than against a hypothetical derivation —
            // a premise nothing inhabits would make this vacuously true and
            // measure nothing.
            //
            // At a sort the family is CONSTANT: index 0 gives
            // `junkD (Sk.kd Sk.ty) = fun qe => whnf_acc qe`, and every `succ`
            // gives `m_sort`, which is the same. So the witness is `ht` in both
            // arms of a `Nat.rec`, and a green means the limit is inhabited
            // exactly where `whnf_acc` is.
            //
            // It does NOT show the limit is inhabited at a PI — that is the
            // interesting case, where the family is not constant and where
            // index monotonicity would actually be needed.
            "xvalInf_sort_inhabited".to_string(),
            "def xvalInf_sort_inhabited (D : Nat -> Sk) (u : Level) (r : VEnvD D) (t : KExpr) (ht : whnf_acc t) : interD (Sk.kd Sk.ty) (fun (qn : Nat) => xvalN qn D (KExpr.sort u) (Sk.kd Sk.ty) (WKC.sort D u) r) t := fun (qn : Nat) => @Nat.rec (fun (qk : Nat) => xvalN qk D (KExpr.sort u) (Sk.kd Sk.ty) (WKC.sort D u) r t) ht (fun (qk : Nat) (qih : xvalN qk D (KExpr.sort u) (Sk.kd Sk.ty) (WKC.sort D u) r t) => ht) qn"
                .to_string(),
        ));
        items.push((
            // STEP-INVARIANCE OF `xvalN` AT INDEX 0 — the base case of the
            // obligation that gates the pi case.
            //
            // At index m+1 the pi clause is `PiSetDep`-shaped with
            // V := `xvalN m`, and cr3 for `PiSetDep` consumes `r21_xval_step`
            // (step-invariance of `xval`). The analogue for `xvalN` does not
            // exist, so cr3 does not transfer to the indexed family and
            // pi-inhabitation has no route without it.
            //
            // The base case should be FREE: `xvalN 0` is the `Nat.rec` zero
            // arm, which returns `junkD s` regardless of the term OR the
            // derivation. So both sides are literally `junkD s` and this is
            // `Eq.refl`. If that bare term does not elaborate, `xvalN 0` is not
            // reducing as intended and everything above it is suspect.
            "xvalN_step_zero".to_string(),
            "def xvalN_step_zero (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) (e2 : KExpr) (st : whnf_step e e2) (h2 : WKC D e2 s) (r : VEnvD D) : Eq (VD s) (xvalN Nat.zero D e2 s h2 r) (xvalN Nat.zero D e s h r) := @Eq.refl (VD s) (junkD s)"
                .to_string(),
        ));
        items.push((
            // IS THE LIMIT INHABITED AT A PI? A DEGENERATE case, labelled as
            // such, because the honest general case is blocked on the
            // step-invariance above.
            //
            // The construction: shape env constantly `Sk.ty`, valuation
            // constantly the EMPTY candidate, and the pi `(bvar 0) -> (bvar 0)`.
            // Then the domain `vcarD Sk.ty (qihA r) qa` computes to `Empty`, so
            // every `succ` arm is vacuously satisfied by `Empty.rec` and index
            // 0 is `junkD = whnf_acc`, discharged by `ht`.
            //
            // WHAT IT IS WORTH: it rules out "the limit is empty at EVERY pi",
            // and it exercises the dependent clause's actual reduction
            // behaviour — the `vconsD` of `xvalN qk` at the argument, which is
            // the one thing that distinguishes this model from stock `xval`.
            //
            // WHAT IT IS NOT: inhabitation at a pi with an INHABITED domain.
            // There the family genuinely varies with the index and the witness
            // cannot be vacuous, which is the case that needs step-invariance
            // and, plausibly, index monotonicity — the property `RedW` lacks in
            // both directions. Do not cite this row for that one.
            "xvalInf_pi_inhabited_empty_domain".to_string(),
            "def xvalInf_pi_inhabited_empty_domain (t : KExpr) (ht : whnf_acc t) : interD (piShape Sk.ty Sk.ty) (fun (qn : Nat) => xvalN qn (fun (qi : Nat) => Sk.ty) (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)) (piShape Sk.ty Sk.ty) (WKC.pi (fun (qi : Nat) => Sk.ty) (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero) Sk.ty Sk.ty (WKC.var (fun (qi : Nat) => Sk.ty) Nat.zero) (WKC.var (skcons (domSk Sk.ty) (fun (qi : Nat) => Sk.ty)) Nat.zero)) (fun (qi : Nat) => (fun (qe : KExpr) => Empty))) t := fun (qn : Nat) => @Nat.rec (fun (qk : Nat) => xvalN qk (fun (qi : Nat) => Sk.ty) (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)) (piShape Sk.ty Sk.ty) (WKC.pi (fun (qi : Nat) => Sk.ty) (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero) Sk.ty Sk.ty (WKC.var (fun (qi : Nat) => Sk.ty) Nat.zero) (WKC.var (skcons (domSk Sk.ty) (fun (qi : Nat) => Sk.ty)) Nat.zero)) (fun (qi : Nat) => (fun (qe : KExpr) => Empty)) t) ht (fun (qk : Nat) (qih : xvalN qk (fun (qi : Nat) => Sk.ty) (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)) (piShape Sk.ty Sk.ty) (WKC.pi (fun (qi : Nat) => Sk.ty) (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero) Sk.ty Sk.ty (WKC.var (fun (qi : Nat) => Sk.ty) Nat.zero) (WKC.var (skcons (domSk Sk.ty) (fun (qi : Nat) => Sk.ty)) Nat.zero)) (fun (qi : Nat) => (fun (qe : KExpr) => Empty)) t) => (fun (qa : KExpr) (qha : WKC (fun (qi : Nat) => Sk.ty) qa (domSk Sk.ty)) (hd : Empty) => @Empty.rec (fun (qz : Empty) => vcarD Sk.ty (xvalN (Nat.succ qk) (skcons (domSk Sk.ty) (fun (qi : Nat) => Sk.ty)) (KExpr.bvar Nat.zero) Sk.ty (WKC.var (skcons (domSk Sk.ty) (fun (qi : Nat) => Sk.ty)) Nat.zero) (vconsD (domSk Sk.ty) (fun (qi : Nat) => Sk.ty) (xvalN qk (fun (qi : Nat) => Sk.ty) qa (domSk Sk.ty) qha (fun (qi : Nat) => (fun (qe : KExpr) => Empty))) (fun (qi : Nat) => (fun (qe : KExpr) => Empty)))) (KExpr.app t qa)) hd)) qn"
                .to_string(),
        ));
        items
    }
}

#[cfg(test)]
#[path = "evalir_division_part_a.rs"]
mod evalir_division_part_a;
#[cfg(test)]
#[path = "evalir_division_part_b.rs"]
mod evalir_division_part_b;
#[cfg(test)]
#[path = "evalir_view_retraction.rs"]
mod evalir_view_retraction;

#[cfg(test)]
#[path = "candmodel_dep_pi_probe_tests.rs"]
mod tests;
