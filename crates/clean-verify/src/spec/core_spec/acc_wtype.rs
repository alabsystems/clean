// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Higher-order-fields rung (9th fragment increment): W-types / Acc — a family
//! whose constructor takes a FUNCTION into the family (`sup : (D -> W) -> W`),
//! so the recursor's recursive call lives UNDER a binder. This is the
//! generalization beyond first-order (Nat.rec) and mutual: the genuinely new
//! content is the `lift_at _ 0 1` arithmetic through the field-domain binder
//! (`wIhBody`/`wRecRhsBody`), the shape a first-order rung never produces.
//!
//! W is a CONCRETE single family (like Nat), so `natrec.rs` is the primary
//! template. Ported from the Aristotle-PROVEN guide
//! `scratch/aristotle-harvest/w5-acc-wtype/.../AccWType.lean` (all 3 targets
//! proven) via the big-push draft `scratch/acc-wtype-port-draft.md`. This
//! registers the OBJECT LAYER + the two rfl validations (w_iota_fires_gen,
//! wREnv_ok), the SN specialization `whnf_terminates_well_typed_w`, and
//! adequacy GROUP 1 (`wIhCod`/`inst_bvar0`/`wIhCod_inst`/`wIhBody_inst`,
//! transcribed from `AccWTypeSN.lean:863-921`). The `redRecW` CandModel field
//! and `redRecW_holds` already live in `dependent_sn_richmodel.rs`. Groups 2-4
//! then landed the const-irreducibility infra, the canonical-major SN gate
//! (`supApp_step_inv`/`whnfAcc_supApp`), the major class (`WMajor`/`MinorUseW`),
//! and the CANONICAL arm `w_adequacy_canon` (guide :1451).
//!
//! **THE RUNG IS COMPLETE.** `w_adequacy` (guide :1555) is registered and
//! kernel-checked: higher-order W-recursor adequacy, by cases over `WMajor` —
//! the canonical arm `w_adequacy_canon` (:1451) and the stuck arm
//! `w_adequacy_stuck` (:1478). Validated by `axiom_ratchet` 3/3; census 11
//! throughout, ratchet file untouched, zero new axioms.
//!
//! Getting there needed `redTypeStep` restored to the CandModel telescope
//! (candidates respect conversion), which also unblocked `minorUseW_motive_step`.
//!
//! TWO HONEST NOTES:
//!  * Everything here is CONDITIONAL on `CandModel`, the labeled Godel-floor
//!    reducibility-candidate hypothesis — as is every theorem in this layer.
//!    Restoring `redTypeStep` made that hypothesis STRICTLY STRONGER; the trust
//!    delta is recorded at the field in `dependent_sn_richmodel.rs`.
//!  * `w_adequacy_stuck`'s `hst : WStuckMajor u t` is DEAD in the body. The
//!    spec's `whnf_step`/`iota_reduces` are pinned to `the_red_env`, which keys
//!    no `wRec` recursor, so the spine cannot iota-fire regardless of the
//!    major's head — making the spec's statement strictly stronger than the
//!    guide's, which needs the gate only because its iota lives at `wREnv u`.
//!    The parameter survives so the capstone's `WMajor.rec` arm lines up.
//!    Consequently `iota_reduct_wRecApp_stuck` has no consumer; it is kept as
//!    the faithful analogue for any future env-parametric restatement.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// W-type OBJECT prefix: names/consts/types/rule-rhs/recursor-env/contractum
    /// + the two gates (`WFresh`, `WRecEnvOK`) + the rfl validations.
    ///
    /// Split out of `add_acc_wtype` and moved AHEAD of
    /// `add_dependent_sn_richmodel` so that a CandModel `redRecW` field can
    /// reference `wRecApp`/`WFresh`/`WRecEnvOK`/`WRecContract` — the
    /// stage-ordering prerequisite for the W-type adequacy layer that
    /// `add_acc_wtype`'s header calls deferred. Exactly the two-stage idiom
    /// already used by `add_natrec_objects` and `add_snschema_objects`.
    ///
    /// Consumes only early stages: `expr_model` (`lift_at`), `rec_env`
    /// (`opt_pick`/`name_eqb`/`recmeta_for`/`recrule_for`), `iota_step`, and
    /// `delta_step` (`defval_for`) — all registered far earlier than the target
    /// slot. Census-NEUTRAL pure reorder: no declaration is added or removed.
    pub(super) fn add_acc_wtype_objects(&mut self) -> Result<(), SpecError> {
        // Coded names: D (domain, = natName by value but a distinct def id),
        // W (family), sup (ctor), wRec (recursor).
        self.add_recursive_def(
            "def dName : Name := Name.str Name.anonymous Nat.zero",
            "dName: the W-type domain D's name (str anonymous 0). AccWType rung.",
        )?;
        self.add_recursive_def(
            "def wName : Name := Name.str Name.anonymous (Nat.succ Nat.zero)",
            "wName: the W family name (str anonymous 1). AccWType rung.",
        )?;
        self.add_recursive_def(
            "def supName : Name := Name.str wName Nat.zero",
            "supName: the sup constructor name (str W 0). AccWType rung.",
        )?;
        self.add_recursive_def(
            "def wRecName : Name := Name.str wName (Nat.succ Nat.zero)",
            "wRecName: the W recursor name (str W 1). AccWType rung.",
        )?;
        // Constant heads.
        self.add_recursive_def(
            "def dTypeC : KExpr := KExpr.const dName (ListType.nil Level)",
            "dTypeC: the domain D type constant. AccWType rung.",
        )?;
        self.add_recursive_def(
            "def wTypeC : KExpr := KExpr.const wName (ListType.nil Level)",
            "wTypeC: the W family type constant. AccWType rung.",
        )?;
        self.add_recursive_def(
            "def supC : KExpr := KExpr.const supName (ListType.nil Level)",
            "supC: the sup constructor constant. AccWType rung.",
        )?;
        self.add_recursive_def(
            "def wRecC (u : Level) : KExpr := KExpr.const wRecName (ListType.cons Level u (ListType.nil Level))",
            "wRecC u: the W recursor constant carrying its motive-universe level. AccWType rung.",
        )?;
        // Types + constructor spine.
        self.add_recursive_def(
            "def wMotiveTy (u : Level) : KExpr := KExpr.pi wTypeC (KExpr.sort u)",
            "wMotiveTy u: the W motive type W -> Sort u. AccWType rung.",
        )?;
        self.add_recursive_def(
            "def wFieldTy : KExpr := KExpr.pi dTypeC wTypeC",
            "wFieldTy: the sup field type D -> W (the higher-order recursive argument). AccWType rung.",
        )?;
        self.add_recursive_def(
            "def wMinorTy : KExpr := KExpr.pi wFieldTy (KExpr.pi (KExpr.pi dTypeC (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)))) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.app supC (KExpr.bvar (Nat.succ Nat.zero)))))",
            "wMinorTy: the sup minor type — takes the field function f : D -> W AND the pointwise IH (d:D) -> C (f d), concludes C (sup f). The higher-order IH-under-binder. AccWType rung.",
        )?;
        self.add_recursive_def(
            "def supApp (f : KExpr) : KExpr := KExpr.app supC f",
            "supApp f: the sup constructor applied to a field function. AccWType rung.",
        )?;
        self.add_recursive_def(
            "def wRecTy (u : Level) : KExpr := KExpr.pi (wMotiveTy u) (KExpr.pi wMinorTy (KExpr.pi wTypeC (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))))",
            "wRecTy u: THE W recursor type (motive, sup-minor, then major -> motive at major). AccWType rung.",
        )?;
        // Rule rhs (the under-binder recursive call is the new content), metadata,
        // rules, environment.
        self.add_recursive_def(
            "def wRecRhsBody (u : Level) : KExpr := KExpr.app (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.lam dTypeC (KExpr.app (KExpr.app (KExpr.app (wRecC u) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero))))",
            "wRecRhsBody u: the rule-rhs body = minor applied to the field f and the IH function (fun d => wRec m mn (f d)); the recursive wRec call is UNDER the lam dTypeC binder (bvar 3 reach). AccWType rung.",
        )?;
        self.add_recursive_def(
            "def wRecRhs (u : Level) : KExpr := KExpr.lam (wMotiveTy u) (KExpr.lam wMinorTy (KExpr.lam wFieldTy (wRecRhsBody u)))",
            "wRecRhs u: the full sup rule-rhs lambda (lam motive, minor, field; body = wRecRhsBody). AccWType rung.",
        )?;
        self.add_recursive_def(
            "def wRecMeta : RecMeta := RecMeta.mk Nat.zero (Nat.succ Nat.zero) (Nat.succ Nat.zero) Nat.zero Bool.true",
            "wRecMeta: W recursor metadata (0 params, 1 motive, 1 minor, 0 indices, major-after-minors). AccWType rung.",
        )?;
        self.add_recursive_def(
            "def wRecRules (u : Level) : RecRules := RecRules.cons (RecRule.mk supName (Nat.succ Nat.zero) (wRecRhs u)) RecRules.nil",
            "wRecRules u: the W recursor's single sup rule (name/1-field/wRecRhs). AccWType rung.",
        )?;
        self.add_recursive_def(
            "def wREnv (u : Level) : RecEnv := RecEnv.addRec RecEnv.empty wRecName wRecMeta (wRecRules u)",
            "wREnv u: the W recursor environment. AccWType rung.",
        )?;
        // Recursor spine + the IH-under-binder terms (the new de Bruijn content).
        self.add_recursive_def(
            "def wRecApp (u : Level) (m : KExpr) (mn : KExpr) (t : KExpr) : KExpr := KExpr.app (KExpr.app (KExpr.app (wRecC u) m) mn) t",
            "wRecApp u m mn t: a fully-applied W recursor spine (wRec m mn t). AccWType rung.",
        )?;
        self.add_recursive_def(
            "def wIhBody (u : Level) (m : KExpr) (mn : KExpr) (f : KExpr) : KExpr := KExpr.app (KExpr.app (KExpr.app (wRecC u) (lift_at m Nat.zero (Nat.succ Nat.zero))) (lift_at mn Nat.zero (Nat.succ Nat.zero))) (KExpr.app (lift_at f Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero))",
            "wIhBody u m mn f: the IH body under the d-binder — wRec (lift m)(lift mn)((lift f) d); THE lift_at _ 0 1 through-the-binder arithmetic, the rung's genuinely new de Bruijn content. AccWType rung.",
        )?;
        self.add_recursive_def(
            "def wIhFun (u : Level) (m : KExpr) (mn : KExpr) (f : KExpr) : KExpr := KExpr.lam dTypeC (wIhBody u m mn f)",
            "wIhFun u m mn f: the IH function fun (d:D) => wRec m mn (f d). AccWType rung.",
        )?;
        self.add_recursive_def(
            "def wContractum (u : Level) (m : KExpr) (mn : KExpr) (f : KExpr) : KExpr := KExpr.app (KExpr.app mn f) (wIhFun u m mn f)",
            "wContractum u m mn f: the W iota contractum = minor applied to the field f and the IH function. AccWType rung.",
        )?;
        // The contraction relation + the two gates.
        self.add_inductive(
            "inductive WRecContract (u : Level) : KExpr -> KExpr -> Type\n| sup : forall (m : KExpr) (mn : KExpr) (f : KExpr), WRecContract u (wRecApp u m mn (supApp f)) (wContractum u m mn f)",
            "WRecContract u lhs rhs: the W iota computation rule — wRec on (sup f) contracts to minor applied to f and the IH function. AccWType rung.",
        )?;
        self.add_inductive(
            "inductive WFresh : DefEnv -> Type\n| mk : forall (denv : DefEnv), Eq (OptionType KExpr) (defval_for denv dName) (OptionType.none KExpr) -> Eq (OptionType KExpr) (defval_for denv wName) (OptionType.none KExpr) -> Eq (OptionType KExpr) (defval_for denv supName) (OptionType.none KExpr) -> Eq (OptionType KExpr) (defval_for denv wRecName) (OptionType.none KExpr) -> WFresh denv",
            "WFresh denv: the D/W/sup/wRec names are all unbound in denv (delta won't fire). AccWType rung.",
        )?;
        self.add_inductive(
            "inductive WRecEnvOK : Level -> RecEnv -> Type\n| mk : forall (u : Level) (renv : RecEnv), Eq (OptionType RecMeta) (recmeta_for renv wRecName) (OptionType.some RecMeta wRecMeta) -> Eq (OptionType RecRule) (recrule_for renv wRecName supName) (OptionType.some RecRule (RecRule.mk supName (Nat.succ Nat.zero) (wRecRhs u))) -> WRecEnvOK u renv",
            "WRecEnvOK u renv: renv stores the W recursor metadata + the sup rule (the wREnv_ok conclusion shape). AccWType rung.",
        )?;
        // rfl validations (LOUD gates — a de Bruijn / metadata slip fails these).
        self.add_recursive_def(
            "def w_iota_fires_gen (u : Level) (m : KExpr) (mn : KExpr) (f : KExpr) : iota_step (wREnv u) (wRecApp u m mn (supApp f)) (KExpr.app (KExpr.app (KExpr.app (wRecRhs u) m) mn) f) := Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.app (KExpr.app (KExpr.app (wRecRhs u) m) mn) f))",
            "w_iota_fires_gen: the W iota FIRES by rfl — wRec m mn (sup f) iota-steps to wRecRhs applied to m,mn,f. THE loud validation gate for the whole object-layer wiring. AccWType rung.",
        )?;
        self.add_recursive_def(
            "def wREnv_ok (u : Level) : WRecEnvOK u (wREnv u) := WRecEnvOK.mk u (wREnv u) (Eq.refl (OptionType RecMeta) (OptionType.some RecMeta wRecMeta)) (Eq.refl (OptionType RecRule) (OptionType.some RecRule (RecRule.mk supName (Nat.succ Nat.zero) (wRecRhs u))))",
            "wREnv_ok u: WRecEnvOK holds for wREnv by rfl (metadata + rule lookups fire). AccWType rung.",
        )?;

        Ok(())
    }

    /// W-type CandModel-dependent tail: the const-typing env + the SN
    /// specialization. Stays late because it consumes `CandModel` and
    /// `whnf_terminates_well_typed_dependent` from `add_dependent_sn_richmodel`.
    pub(super) fn add_acc_wtype(&mut self) -> Result<(), SpecError> {
        // ── SN via the fundamental-theorem path (the same one-liner as
        // nat/gen/indexed/mut): wTEnv types D and W at Sort 1, the sup ctor at
        // (D->W)->W, the recursor at wRecTy; the SN theorem is
        // whnf_terminates_well_typed_dependent specialized at wTEnv, with the
        // CandModel M an assumed parameter (the labeled hypothesis). The redRecW
        // field the adequacy proof needs is NOT required here — SN is conditional
        // on M, and M is a parameter.
        self.add_recursive_def(
            "def wTEnv (u : Level) (n : Name) : OptionType KExpr := opt_pick KExpr (name_eqb n wName) (KExpr.sort (Level.succ Level.zero)) (opt_pick KExpr (name_eqb n dName) (KExpr.sort (Level.succ Level.zero)) (opt_pick KExpr (name_eqb n wRecName) (wRecTy u) (opt_pick KExpr (name_eqb n supName) (KExpr.pi wFieldTy wTypeC) (OptionType.none KExpr))))",
            "wTEnv u: the W-type const-typing env (D, W at Sort 1; sup at (D->W)->W; recursor at wRecTy). The higher-order analog of genTEnv/iTEnv/mutTEnv. AccWType rung SN.",
        )?;
        self.add_recursive_def(
            "def whnf_terminates_well_typed_w (u : Level) (M : CandModel (wTEnv u)) (e : KExpr) (T : KExpr) (h : TypingCtx (wTEnv u) (ListType.nil KExpr) e T) : whnf_acc e := whnf_terminates_well_typed_dependent (wTEnv u) M e T h",
            "whnf_terminates_well_typed_w: every closed well-typed term over the W-type typing env (D/W/sup/recursor as typed consts) is whnf_acc (SN), modulo M : CandModel (wTEnv u). One-line specialization of whnf_terminates_well_typed_dependent, mirroring gen/idx/mut/nat. THE higher-order (W-type/Acc) recursor SN theorem — 9th fragment-ladder rung SN payoff. AccWType rung SN.",
        )?;

        // ── OptionType no-confusion (BOTH CURRENTLY UNUSED — see below) ─────
        //
        // `Eq (OptionType A) none (some a) -> C`, in both orientations.
        //
        // CORRECTION 2026-07-26: the justification originally written here said
        // "the spec had NO lemma eliminating a none/some equation (searched by
        // name AND semantically)". **That was false.** The spec already had at
        // least two:
        //   * `option_none_ne_some_type` (`par_reduces_c.rs:1396`) — the exact
        //     Type-valued eliminator, and the one the `natrec.rs` template and
        //     the group-2 code below actually call;
        //   * `opt_none_ne_some_t` — used throughout `whnf_progress.rs` and
        //     `rigid_app_inv.rs`.
        // The claim was a NAME search reported as a semantic one, which is the
        // same mistake that mis-sized this rung twice (see
        // `scratch/port-adequacy-fields.md`). Search by statement SHAPE.
        //
        // Consequence: `opt_none_ne_some` and `opt_some_ne_none` have no
        // consumer anywhere in the crate. They are kept for now rather than
        // deleted mid-rung — removing spec declarations is a census-visible
        // change that wants its own validated commit — but they are dead, and
        // the two orientations they add over `option_none_ne_some_type` were
        // never needed. Retire them, or adopt them in place of the existing
        // eliminators; do not add a fourth.
        //
        // Shape, for whoever does that cleanup: same as `bool_true_ne_false`
        // (schema.rs) — pick a motive that is an inhabited type at the
        // constructor you HAVE and `C` at the one you are refuting, then
        // transport along the equation. `OptionType` is `| none | some`, so
        // `OptionType.rec` takes the none-case first.
        self.add_recursive_def(
            "def opt_none_ne_some (A : Type) (C : Type) (a : A) (h : Eq (OptionType A) (OptionType.none A) (OptionType.some A a)) : C := Eq.substType (OptionType A) (fun (o : OptionType A) => OptionType.rec A (fun (_ : OptionType A) => Type) Nat (fun (_ : A) => C) o) (OptionType.none A) (OptionType.some A a) h Nat.zero",
            "opt_none_ne_some: Eq (OptionType A) none (some a) -> C. OptionType no-confusion in eliminating form, the OptionType analogue of bool_true_ne_false. Motive is Nat (inhabited by zero) at none and C at some, transported along h. Needed by head-discrimination inversions over a reduction relation. CURRENTLY UNUSED: the spec already had option_none_ne_some_type (par_reduces_c.rs) and opt_none_ne_some_t, and those are what the live code calls -- the 'spec had none' claim in the original description was a name search reported as a semantic one. Retire or adopt; do not add a fourth.",
        )?;
        self.add_recursive_def(
            "def opt_some_ne_none (A : Type) (C : Type) (a : A) (h : Eq (OptionType A) (OptionType.some A a) (OptionType.none A)) : C := Eq.substType (OptionType A) (fun (o : OptionType A) => OptionType.rec A (fun (_ : OptionType A) => Type) C (fun (_ : A) => Nat) o) (OptionType.some A a) (OptionType.none A) h Nat.zero",
            "opt_some_ne_none: the mirrored orientation, Eq (OptionType A) (some a) none -> C. Motive is Nat at some and C at none. Both orientations are provided so an inversion never has to insert an Eq.symm just to match direction.",
        )?;

        // ── ADEQUACY GROUP 1: the IH-binder de Bruijn arithmetic ────────────
        //
        // Ported from the Aristotle-PROVEN guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:863-921
        // (`wIhCod`, `wIhCod_inst`, `wIhBody_inst`). These are the substitution
        // facts the adequacy proof needs in order to push `redAbstraction`
        // through the field-domain binder: they say that instantiating the
        // under-binder terms at a domain element `a` cancels the unit lifts.
        //
        // Registered HERE (stage 135, the late tail) and not in
        // `add_acc_wtype_objects` (stage 77) because `inst_lift1` is registered
        // by `add_natrec` (stage 79) — placing them early fails with
        // "Unknown identifier: inst_lift1". Every dependency's stage was checked
        // before writing: lift_zero_identity 31, inst_lift1 79, wIhBody/wRecC 77.
        //
        // No CandModel, no recursion, no SN — pure de Bruijn arithmetic, which is
        // why this is the tractable first group of the adequacy port.
        let lift1 = |e: &str| format!("(lift_at {e} Nat.zero (Nat.succ Nat.zero))");
        let inst = |e: String| format!("(instantiate {e} a)");

        self.add_recursive_def(
            &format!(
                "def wIhCod (m : KExpr) (f : KExpr) : KExpr := KExpr.app {lm} (KExpr.app {lf} (KExpr.bvar Nat.zero))",
                lm = lift1("m"),
                lf = lift1("f"),
            ),
            "wIhCod m f: the semantic IH-function codomain under the d-binder — m ((lift f) d), with m and f lifted by one. Guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:863. AccWType adequacy group 1.",
        )?;

        // instantiate (bvar 0) a = a. Holds because instantiate_bvar_at at
        // idx = depth = 0 computes to `lift_at a 0 0`, which lift_zero_identity
        // collapses. Broken out because all three rewrites below need it.
        self.add_recursive_def(
            "def inst_bvar0 (a : KExpr) : Eq KExpr (instantiate (KExpr.bvar Nat.zero) a) a := lift_zero_identity a",
            "inst_bvar0: instantiating the innermost bound variable yields the value itself (instantiate_bvar_at at idx=depth=0 computes to lift_at a 0 0; lift_zero_identity collapses it). AccWType adequacy group 1.",
        )?;

        // wIhCod_inst: (wIhCod m f)[a] = m (f a). Three rewrites, right to left,
        // chained with Eq.trans: the bvar, then f's lift, then m's lift.
        {
            let a0_inner = format!(
                "(KExpr.app {ilf} {ib})",
                ilf = inst(lift1("f")),
                ib = "(instantiate (KExpr.bvar Nat.zero) a)"
            );
            let a0 = format!("(KExpr.app {ilm} {a0_inner})", ilm = inst(lift1("m")));
            let a1 = format!("(KExpr.app m {a0_inner})");
            let a2 =
                "(KExpr.app m (KExpr.app f (instantiate (KExpr.bvar Nat.zero) a)))".to_string();
            let a3 = "(KExpr.app m (KExpr.app f a))".to_string();
            let s1 = format!(
                "(Eq.cong KExpr KExpr (fun (X : KExpr) => KExpr.app X {a0_inner}) {ilm} m (inst_lift1 m a))",
                ilm = inst(lift1("m")),
            );
            let s2 = format!(
                "(Eq.cong KExpr KExpr (fun (Y : KExpr) => KExpr.app m (KExpr.app Y (instantiate (KExpr.bvar Nat.zero) a))) {ilf} f (inst_lift1 f a))",
                ilf = inst(lift1("f")),
            );
            let s3 = "(Eq.cong KExpr KExpr (fun (Z : KExpr) => KExpr.app m (KExpr.app f Z)) (instantiate (KExpr.bvar Nat.zero) a) a (inst_bvar0 a))".to_string();
            self.add_recursive_def(
                &format!(
                    "def wIhCod_inst (m : KExpr) (f : KExpr) (a : KExpr) : Eq KExpr (instantiate (wIhCod m f) a) {a3} := Eq.trans KExpr {a0} {a2} {a3} (Eq.trans KExpr {a0} {a1} {a2} {s1} {s2}) {s3}"
                ),
                "wIhCod_inst: (wIhCod m f)[a] = m (f a) — the unit lifts cancel under instantiation. Guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:890. Proof: three Eq.cong rewrites (bvar, then f, then m) chained by Eq.trans. AccWType adequacy group 1.",
            )?;
        }

        // wIhBody_inst: beta-reducing the IH function at a domain element —
        // (wIhBody u m mn f)[a] = wRec m mn (f a). THE equation that lets
        // redAbstraction close the recursive call UNDER the binder in the
        // adequacy proof. Same shape, four rewrites (m, mn, f, bvar); the
        // recursor head `wRecC u` is a const and instantiates to itself.
        {
            let ilm = inst(lift1("m"));
            let ilmn = inst(lift1("mn"));
            let ilf = inst(lift1("f"));
            let ib = "(instantiate (KExpr.bvar Nat.zero) a)";
            let spine =
                |x: &str, y: &str| format!("(KExpr.app (KExpr.app (KExpr.app (wRecC u) {x}) {y})");
            let b0 = format!("{sp} (KExpr.app {ilf} {ib}))", sp = spine(&ilm, &ilmn));
            let b1 = format!("{sp} (KExpr.app {ilf} {ib}))", sp = spine("m", &ilmn));
            let b2 = format!("{sp} (KExpr.app {ilf} {ib}))", sp = spine("m", "mn"));
            let b3 = format!("{sp} (KExpr.app f {ib}))", sp = spine("m", "mn"));
            let b4 = "(wRecApp u m mn (KExpr.app f a))".to_string();
            let t1 = format!(
                "(Eq.cong KExpr KExpr (fun (X : KExpr) => {sp} (KExpr.app {ilf} {ib}))) {ilm} m (inst_lift1 m a))",
                sp = spine("X", &ilmn),
            );
            let t2 = format!(
                "(Eq.cong KExpr KExpr (fun (Y : KExpr) => {sp} (KExpr.app {ilf} {ib}))) {ilmn} mn (inst_lift1 mn a))",
                sp = spine("m", "Y"),
            );
            let t3 = format!(
                "(Eq.cong KExpr KExpr (fun (Z : KExpr) => {sp} (KExpr.app Z {ib}))) {ilf} f (inst_lift1 f a))",
                sp = spine("m", "mn"),
            );
            let t4 = format!(
                "(Eq.cong KExpr KExpr (fun (W : KExpr) => {sp} (KExpr.app f W))) {ib} a (inst_bvar0 a))",
                sp = spine("m", "mn"),
            );
            self.add_recursive_def(
                &format!(
                    "def wIhBody_inst (u : Level) (m : KExpr) (mn : KExpr) (f : KExpr) (a : KExpr) : Eq KExpr (instantiate (wIhBody u m mn f) a) {b4} := Eq.trans KExpr {b0} {b3} {b4} (Eq.trans KExpr {b0} {b2} {b3} (Eq.trans KExpr {b0} {b1} {b2} {t1} {t2}) {t3}) {t4}"
                ),
                "wIhBody_inst: (wIhBody u m mn f)[a] = wRec m mn (f a) — the through-the-binder lifts cancel. THE equation that makes redAbstraction close the recursive call under the field-domain binder in W-adequacy. Guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:911. Four Eq.cong rewrites chained by Eq.trans; the wRecC head is a const and instantiates to itself. AccWType adequacy group 1.",
            )?;
        }

        // ── ADEQUACY GROUP 2 (shared infra): const irreducibility ───────────
        //
        // The guide reaches `whnfAcc_dTypeC` (AccWTypeSN.lean:1192) through
        // `no_whnf_step_dTypeC` (:1180), which dispatches the two whnf_step
        // constructors onto `no_betaReduces_const` (:515) and
        // `delta_reduct_none_of_defval_none` (:301).
        //
        // SIZING CORRECTION (2026-07-26): both of those primitives ALREADY EXIST
        // in-spec under different names, so only the dispatch is new here:
        //   guide no_betaReduces_const          = `const_no_beta_reduces`
        //                                         (natrec.rs, stage 79) — and the
        //                                         spec's is STRONGER: it needs no
        //                                         recmeta gate, because
        //                                         `iota_reduct_const_none` holds
        //                                         unconditionally for a bare const.
        //   guide delta_reduct_none_of_defval_none
        //                                       = `delta_reduct_eq_none_of_defval_none`
        //                                         (par_reduces_iota_delta.rs, stage
        //                                         registered at bundles.rs:678).
        // Both are in scope by this stage (acc_wtype is the last stage, 135).
        //
        // Stated GENERALLY over any const whose δ-definition is absent, not just
        // the W lane's `dTypeC`: every rung's `whnfAcc_*` gate needs this same
        // fact, so it is built once. General utility — hoist to an earlier stage
        // if an earlier stage ever needs it (same note as `opt_none_ne_some`).
        // The spec's whnf_acc/whnf_step are env-FIXED to `the_red_env`, so the
        // guide's env-parametric statement collapses onto `red_def the_red_env`.
        {
            let cn = "(KExpr.const n us)";
            let denv = "(red_def the_red_env)";
            // delta arm: delta_reduces gives delta_reduct = some e2, but the
            // defval-none hypothesis forces delta_reduct = none. The head-name
            // side condition `kexpr_const_name (kapp_fn (const n us)) = some n`
            // is rfl: a bare const is its own spine head.
            let delta_arm = format!(
                "(fun (hdr : delta_reduces {cn} e2) => option_none_ne_some_type KExpr e2 C \
                 (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (delta_reduct {denv} {cn}) (OptionType.some KExpr e2) \
                 (Eq.symm (OptionType KExpr) (delta_reduct {denv} {cn}) (OptionType.none KExpr) \
                 (delta_reduct_eq_none_of_defval_none {denv} {cn} n \
                 (Eq.refl (OptionType Name) (OptionType.some Name n)) hdef)) \
                 (delta_reduces_to_step {cn} e2 hdr)))"
            );
            let beta_arm = format!(
                "(fun (hbr : beta_reduces {cn} e2) => const_no_beta_reduces n us e2 C hbr)"
            );
            self.add_recursive_def(
                &format!(
                    "def no_whnf_step_const (n : Name) (us : ListType Level) \
                     (hdef : Eq (OptionType KExpr) (defval_for {denv} n) (OptionType.none KExpr)) \
                     (e2 : KExpr) (C : Type) (hs : whnf_step {cn} e2) : C := \
                     whnf_step.rec {cn} e2 (fun (_ : whnf_step {cn} e2) => C) {beta_arm} {delta_arm} hs"
                ),
                "no_whnf_step_const: a constant with no δ-definition in the fixed def-env admits NO whnf_step, producing any C. whnf_step.rec dispatch — beta arm via const_no_beta_reduces (a bare const has no beta/iota step, iota_reduct_const_none being unconditional), delta arm via delta_reduct_eq_none_of_defval_none (defval none => delta_reduct none) against delta_reduces_to_step. Guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:1180 (no_whnf_step_dTypeC), stated generally over any δ-free const rather than the W lane's dTypeC. AccWType adequacy group 2, shared infra.",
            )?;

            self.add_recursive_def(
                &format!(
                    "def whnfAcc_const (n : Name) (us : ListType Level) \
                     (hdef : Eq (OptionType KExpr) (defval_for {denv} n) (OptionType.none KExpr)) : whnf_acc {cn} := \
                     whnf_acc.intro {cn} (fun (e2 : KExpr) (hs : whnf_step {cn} e2) => \
                     no_whnf_step_const n us hdef e2 (whnf_acc e2) hs)"
                ),
                "whnfAcc_const: a constant with no δ-definition is strongly normalizing — whnf_acc.intro over the vacuous step set, discharged by no_whnf_step_const at motive `whnf_acc e2`. Guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:1192 (whnfAcc_dTypeC), stated generally. AccWType adequacy group 2, shared infra.",
            )?;
        }

        // ── ADEQUACY GROUP 2 (W-specific): canonical-major SN ───────────────
        //
        // `supApp_step_inv` (guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:1252) then `whnfAcc_supApp`
        // (:1349) — the canonical-major arm of W adequacy, and the first place
        // the W-specific `sup f` spine actually appears.
        //
        // The guide returns an existential `∃ f', BetaReduces f f' ∧ e' = supApp f'`.
        // The spec has no `Exists`, so this is stated in ELIMINATOR (CPS) form:
        // the caller supplies a continuation `k` consuming the witness. That is
        // the same idiom `no_whnf_step_const` uses for absurdity (`... (C : Type)
        // ... : C`), just with a non-vacuous continuation.
        //
        // The env-FIXED spec makes this STRICTLY easier than the guide's
        // env-parametric statement: over `the_red_env` the head `supC` carries no
        // recursor metadata, so the iota arm dies by `rfl` (exactly as the
        // `numeral_no_beta` succ arm does for `app natSuccC n` in natrec.rs) and
        // only the δ gate needs a hypothesis. That hypothesis is the spec's
        // stand-in for the guide's `WFresh` conjunct `hf.2.2.1`.
        {
            let sf = "(supApp f)";
            let denv = "(red_def the_red_env)";
            let renv = "(red_rec the_red_env)";
            // motive carries BOTH the source-eq and the continuation, because the
            // productive arm (app_right) must relate the recursor's TARGET index to
            // `supApp f2`; a source-only motive loses that connection.
            let mot = format!(
                "(fun (s : KExpr) (t : KExpr) (_ : beta_reduces s t) => Eq KExpr s {sf} -> (forall (f2 : KExpr), beta_reduces f f2 -> Eq KExpr t (supApp f2) -> C) -> C)"
            );
            // NOTE: the continuation's Eq is at the arm's OWN target `t`, which
            // differs per constructor, so each arm spells its own out.
            let a_beta = format!("(fun (A0 : KExpr) (body : KExpr) (arg : KExpr) (heq : Eq KExpr (KExpr.app (KExpr.lam A0 body) arg) {sf}) (_kk : forall (f2 : KExpr), beta_reduces f f2 -> Eq KExpr (instantiate body arg) (supApp f2) -> C) => const_ne_lam supName (ListType.nil Level) A0 body C (Eq.symm KExpr (KExpr.lam A0 body) supC (app_inj_fst (KExpr.lam A0 body) arg supC f heq)))");
            let a_appl = format!("(fun (g : KExpr) (g2 : KExpr) (a : KExpr) (hstep : beta_reduces g g2) (_ih : Eq KExpr g {sf} -> (forall (f2 : KExpr), beta_reduces f f2 -> Eq KExpr g2 (supApp f2) -> C) -> C) (heq : Eq KExpr (KExpr.app g a) {sf}) (_kk : forall (f2 : KExpr), beta_reduces f f2 -> Eq KExpr (KExpr.app g2 a) (supApp f2) -> C) => const_no_beta_reduces supName (ListType.nil Level) g2 C (Eq.rec KExpr g (fun (x : KExpr) (_ : Eq KExpr g x) => beta_reduces x g2) hstep supC (app_inj_fst g a supC f heq)))");
            // THE productive arm: a step in the field argument.
            let a_appr = format!("(fun (g : KExpr) (a : KExpr) (a2 : KExpr) (hstep : beta_reduces a a2) (_ih : Eq KExpr a {sf} -> (forall (f2 : KExpr), beta_reduces f f2 -> Eq KExpr a2 (supApp f2) -> C) -> C) (heq : Eq KExpr (KExpr.app g a) {sf}) (kk : forall (f2 : KExpr), beta_reduces f f2 -> Eq KExpr (KExpr.app g a2) (supApp f2) -> C) => kk a2 (Eq.rec KExpr a (fun (x : KExpr) (_ : Eq KExpr a x) => beta_reduces x a2) hstep f (app_inj_snd g a supC f heq)) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x a2) g supC (app_inj_fst g a supC f heq)))");
            // Non-app sources: lam/pi/forall/let/proj all differ from `app supC f`.
            let mk_nonapp = |ctor_args: &str, src: &str, tgt: &str, helper: &str, hargs: &str| {
                format!("(fun {ctor_args} (heq : Eq KExpr {src} {sf}) (_kk : forall (f2 : KExpr), beta_reduces f f2 -> Eq KExpr {tgt} (supApp f2) -> C) => {helper} {hargs} supC f C heq)")
            };
            let ih = |src: &str, tgt: &str| {
                format!("(_ih : Eq KExpr {src} {sf} -> (forall (f2 : KExpr), beta_reduces f f2 -> Eq KExpr {tgt} (supApp f2) -> C) -> C)")
            };
            let a_lamty = mk_nonapp(
                &format!(
                    "(ty : KExpr) (ty2 : KExpr) (body : KExpr) (_hstep : beta_reduces ty ty2) {}",
                    ih("ty", "ty2")
                ),
                "(KExpr.lam ty body)",
                "(KExpr.lam ty2 body)",
                "lam_ne_app",
                "ty body",
            );
            let a_lambd = mk_nonapp(&format!("(ty : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) {}", ih("body", "body2")), "(KExpr.lam ty body)", "(KExpr.lam ty body2)", "lam_ne_app", "ty body");
            let a_pidom = mk_nonapp(&format!("(dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hstep : beta_reduces dom dom2) {}", ih("dom", "dom2")), "(KExpr.pi dom body)", "(KExpr.pi dom2 body)", "pi_ne_app", "dom body");
            let a_picod = mk_nonapp(&format!("(dom : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) {}", ih("body", "body2")), "(KExpr.pi dom body)", "(KExpr.pi dom body2)", "pi_ne_app", "dom body");
            let a_fadom = mk_nonapp(&format!("(dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hstep : beta_reduces dom dom2) {}", ih("dom", "dom2")), "(KExpr.forall_ dom body)", "(KExpr.forall_ dom2 body)", "pi_ne_app", "dom body");
            let a_facod = mk_nonapp(&format!("(dom : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) {}", ih("body", "body2")), "(KExpr.forall_ dom body)", "(KExpr.forall_ dom body2)", "pi_ne_app", "dom body");
            let a_zeta = mk_nonapp(
                "(ty : KExpr) (val : KExpr) (body : KExpr)",
                "(KExpr.let_ ty val body)",
                "(instantiate body val)",
                "let_ne_app",
                "ty val body",
            );
            let a_letty = mk_nonapp(&format!("(ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr) (_hstep : beta_reduces ty ty2) {}", ih("ty", "ty2")), "(KExpr.let_ ty val body)", "(KExpr.let_ ty2 val body)", "let_ne_app", "ty val body");
            let a_letval = mk_nonapp(&format!("(ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr) (_hstep : beta_reduces val val2) {}", ih("val", "val2")), "(KExpr.let_ ty val body)", "(KExpr.let_ ty val2 body)", "let_ne_app", "ty val body");
            let a_letbd = mk_nonapp(&format!("(ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) {}", ih("body", "body2")), "(KExpr.let_ ty val body)", "(KExpr.let_ ty val body2)", "let_ne_app", "ty val body");
            let a_proj = mk_nonapp(&format!("(ps : Name) (pin : Nat) (sub : KExpr) (sub2 : KExpr) (_hstep : beta_reduces sub sub2) {}", ih("sub", "sub2")), "(KExpr.proj ps pin sub)", "(KExpr.proj ps pin sub2)", "proj_ne_app", "ps pin sub");
            // iota: the head supC carries no recursor metadata in the fixed env, so
            // iota_reduct of the sup spine is `none` by rfl (natrec.rs precedent for
            // `app natSuccC n`), contradicting the step's `= some`.
            let a_iota = format!("(fun (e0 : KExpr) (e02 : KExpr) (hiota : iota_reduces e0 e02) (heq : Eq KExpr e0 {sf}) (_kk : forall (f2 : KExpr), beta_reduces f f2 -> Eq KExpr e02 (supApp f2) -> C) => option_none_ne_some_type KExpr e02 C (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct {renv} e0) (OptionType.some KExpr e02) (Eq.symm (OptionType KExpr) (iota_reduct {renv} e0) (OptionType.none KExpr) (Eq.trans (OptionType KExpr) (iota_reduct {renv} e0) (iota_reduct {renv} {sf}) (OptionType.none KExpr) (Eq.cong KExpr (OptionType KExpr) (fun (x : KExpr) => iota_reduct {renv} x) e0 {sf} heq) (Eq.refl (OptionType KExpr) (OptionType.none KExpr)))) (iota_reduces_to_step e0 e02 hiota)))");
            // delta: dies on the WFresh stand-in hypothesis, same shape as
            // no_whnf_step_const. The spine head of `app supC f` is supC, so the
            // head-name side condition is rfl.
            let delta_arm = format!("(fun (hdr : delta_reduces {sf} e2) => option_none_ne_some_type KExpr e2 C (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (delta_reduct {denv} {sf}) (OptionType.some KExpr e2) (Eq.symm (OptionType KExpr) (delta_reduct {denv} {sf}) (OptionType.none KExpr) (delta_reduct_eq_none_of_defval_none {denv} {sf} supName (Eq.refl (OptionType Name) (OptionType.some Name supName)) hdef)) (delta_reduces_to_step {sf} e2 hdr)))");
            let beta_arm = format!("(fun (hbr : beta_reduces {sf} e2) => beta_reduces.rec {mot} {a_beta} {a_appl} {a_appr} {a_lamty} {a_lambd} {a_pidom} {a_picod} {a_fadom} {a_facod} {a_zeta} {a_letty} {a_letval} {a_letbd} {a_iota} {a_proj} {sf} e2 hbr (Eq.refl KExpr {sf}) k)");
            self.add_recursive_def(
                &format!(
                    "def supApp_step_inv (f : KExpr) (e2 : KExpr) (C : Type) \
                     (hdef : Eq (OptionType KExpr) (defval_for {denv} supName) (OptionType.none KExpr)) \
                     (hs : whnf_step {sf} e2) \
                     (k : forall (f2 : KExpr), beta_reduces f f2 -> Eq KExpr e2 (supApp f2) -> C) : C := \
                     whnf_step.rec {sf} e2 (fun (_ : whnf_step {sf} e2) => C) {beta_arm} {delta_arm} hs"
                ),
                "supApp_step_inv: every whnf_step of the canonical spine `sup f` is a beta step in the FIELD f — eliminator (CPS) form, since the spec has no Exists to carry the guide's existential. whnf_step.rec: delta arm dies on the δ-freeness hypothesis (the spec's stand-in for the guide's WFresh conjunct); beta arm is a 15-case beta_reduces.rec whose motive carries both the source-eq and the continuation, so the productive app_right arm can relate the recursor's target index to `supApp f2`. app_left dies via const_no_beta_reduces, the beta redex via const_ne_lam after app_inj_fst, iota by rfl (supC has no recursor metadata in the fixed env), and every non-app source via lam/pi/let/proj_ne_app. Guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:1252. AccWType adequacy group 2.",
            )?;

            self.add_recursive_def(
                &format!(
                    "def whnfAcc_supApp (hdef : Eq (OptionType KExpr) (defval_for {denv} supName) (OptionType.none KExpr)) (f : KExpr) (hacc : whnf_acc f) : whnf_acc {sf} := \
                     whnf_acc.rec (fun (f0 : KExpr) (_h : whnf_acc f0) => whnf_acc (supApp f0)) \
                     (fun (f0 : KExpr) (_hsteps : forall (e' : KExpr), whnf_step f0 e' -> whnf_acc e') (ihf : forall (e' : KExpr), whnf_step f0 e' -> whnf_acc (supApp e')) => \
                     whnf_acc.intro (supApp f0) (fun (e2 : KExpr) (hstep : whnf_step (supApp f0) e2) => \
                     supApp_step_inv f0 e2 (whnf_acc e2) hdef hstep \
                     (fun (f2 : KExpr) (hb : beta_reduces f0 f2) (heq : Eq KExpr e2 (supApp f2)) => \
                     Eq.rec KExpr (supApp f2) (fun (x : KExpr) (_ : Eq KExpr (supApp f2) x) => whnf_acc x) (ihf f2 (whnf_step.beta f0 f2 hb)) e2 (Eq.symm KExpr e2 (supApp f2) heq)))) \
                     f hacc"
                ),
                "whnfAcc_supApp: the canonical W major `sup f` is strongly normalizing whenever its field f is — Acc induction (whnf_acc.rec) on f, then whnf_acc.intro at `supApp f0`, decomposing each step via supApp_step_inv into a field beta step, applying the Acc IH at the reduct and transporting back along the target equation. Guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:1349. This is the canonical-major SN gate that w_adequacy_canon consumes. AccWType adequacy group 2.",
            )?;
        }

        // ── ADEQUACY GROUP 3: the major class + the minor-use pack ──────────
        //
        // Guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:1203-1250 (WStuckMajor/WMajor) and :1417-1450
        // (MinorUseW and its transport lemmas). These are the two semantic
        // structures `w_adequacy` inducts over and applies.
        //
        // Env collapse, as everywhere in this rung: the guide's
        // `WhnfStep denv (wREnv u)` becomes the spec's env-FIXED `whnf_step`.
        // Prop becomes Type (spec convention).
        //
        // `minorUseW_motive_step` (guide :1431) was previously blocked because
        // this spec had dropped `CandModel.redTypeStep`. That field is restored,
        // so both minor transport lemmas are ported below. The same restoration
        // also removes the old interface blocker for `w_adequacy_stuck` (guide
        // :1478 uses redTypeStep twice); that later adequacy lemma and the
        // `w_adequacy` capstone remain separate ports rather than being
        // misclassified as blocked on a missing model field.
        {
            // The concrete W-freshness witness over the fixed env, mirroring
            // `natFresh_red` (natrec.rs) exactly: all four δ-lookups compute to
            // `none`, so each conjunct is `rfl`.
            self.add_recursive_def(
                "def wFresh_red : WFresh (red_def the_red_env) := WFresh.mk (red_def the_red_env) (Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (Eq.refl (OptionType KExpr) (OptionType.none KExpr))",
                "wFresh_red: the W-lane names (D/W/sup/wRec) are all δ-free in the fixed reduction env, so WFresh holds there by four rfl witnesses. Exact mirror of natFresh_red. This is what discharges the `hdef` hypothesis that supApp_step_inv/whnfAcc_supApp thread. AccWType adequacy group 3.",
            )?;

            // Projection out of the WFresh pack: the sup conjunct is the third
            // of four (dName, wName, supName, wRecName). Elimination convention
            // copied from the NatFresh.rec use in natrec.rs — denv stays ambient,
            // the motive takes only the proof, the arm only the four equations.
            self.add_recursive_def(
                "def wFresh_sup (denv : DefEnv) (h : WFresh denv) : Eq (OptionType KExpr) (defval_for denv supName) (OptionType.none KExpr) := WFresh.rec (fun (_ : WFresh denv) => Eq (OptionType KExpr) (defval_for denv supName) (OptionType.none KExpr)) (fun (_h0 : Eq (OptionType KExpr) (defval_for denv dName) (OptionType.none KExpr)) (_h1 : Eq (OptionType KExpr) (defval_for denv wName) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (defval_for denv supName) (OptionType.none KExpr)) (_h3 : Eq (OptionType KExpr) (defval_for denv wRecName) (OptionType.none KExpr)) => h2) h",
                "wFresh_sup: project the supName δ-freeness conjunct out of a WFresh pack (third of four). Lets a caller holding the guide's `hf : WFresh denv` feed supApp_step_inv/whnfAcc_supApp without rebuilding the equation. AccWType adequacy group 3.",
            )?;
            // Same projection for the DOMAIN name (first of four) — needed by
            // w_adequacy_canon's `whnfAcc_const dName ...` gate.
            self.add_recursive_def(
                "def wFresh_dom (denv : DefEnv) (h : WFresh denv) : Eq (OptionType KExpr) (defval_for denv dName) (OptionType.none KExpr) := WFresh.rec (fun (_ : WFresh denv) => Eq (OptionType KExpr) (defval_for denv dName) (OptionType.none KExpr)) (fun (h0 : Eq (OptionType KExpr) (defval_for denv dName) (OptionType.none KExpr)) (_h1 : Eq (OptionType KExpr) (defval_for denv wName) (OptionType.none KExpr)) (_h2 : Eq (OptionType KExpr) (defval_for denv supName) (OptionType.none KExpr)) (_h3 : Eq (OptionType KExpr) (defval_for denv wRecName) (OptionType.none KExpr)) => h0) h",
                "wFresh_dom: project the dName delta-freeness conjunct out of a WFresh pack (first of four). Feeds whnfAcc_const at dTypeC, the domain-constant SN gate that redAbstraction needs in w_adequacy_canon. AccWType adequacy group 3.",
            )?;

            // WStuckMajor: the major's head constant, if it has one, keys no
            // wRec rule — the gate under which the schematic iota cannot fire on
            // the full spine. Guide :1205.
            self.add_recursive_def(
                "def WStuckMajor (u : Level) (t : KExpr) : Prop := forall (cn : Name), Eq (OptionType Name) (kexpr_const_name (kapp_fn t)) (OptionType.some Name cn) -> Eq (OptionType RecRule) (recrule_for (wREnv u) wRecName cn) (OptionType.none RecRule)",
                "WStuckMajor u t: the head constant of t (if any) carries NO wRec recursor rule — the gate under which the schematic iota cannot fire on the recursor spine. Guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:1205. Stays Prop-valued because its body is a forall into Eq, and Eq is Prop-sorted; the first-order analogue GenStuckMajor is declared the same way. Annotating it Type is a spec-build error (expected Type, got Prop). AccWType adequacy group 3.",
            )?;

            // A bvar has no head constant, so the gate is vacuous. Guide :1209.
            self.add_recursive_def(
                "def wStuckMajor_bvar (u : Level) (i : Nat) : WStuckMajor u (KExpr.bvar i) := fun (cn : Name) (h : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.bvar i))) (OptionType.some Name cn)) => option_none_ne_some Name cn (Eq (OptionType RecRule) (recrule_for (wREnv u) wRecName cn) (OptionType.none RecRule)) h",
                "wStuckMajor_bvar: a bound variable is a stuck major — it has no head constant, so `kexpr_const_name (kapp_fn (bvar i))` computes to none and the gate's hypothesis is absurd. Guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:1209. AccWType adequacy group 3.",
            )?;

            // MinorUseW: the elimination-ready "the minor is reducible" pack.
            // The first-order rung's recursive-results LIST becomes this FUNCTION
            // pack — the higher-order shape this whole rung exists to exercise.
            // Guide :1417.
            self.add_recursive_def(
                "def MinorUseW (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (m : KExpr) (mn : KExpr) : Type := forall (f : KExpr) (ihf : KExpr), cm_Red tenv M wFieldTy f -> (forall (d : KExpr), cm_Red tenv M dTypeC d -> cm_Red tenv M (KExpr.app m (KExpr.app f d)) (KExpr.app ihf d)) -> cm_Red tenv M (KExpr.app m (supApp f)) (KExpr.app (KExpr.app mn f) ihf)",
                "MinorUseW tenv M m mn: applied to a reducible field function f and any term ihf behaving as a POINTWISE-reducible IH function, the minor lands in the candidate at the motive of the built value. The higher-order analogue of the first-order rung's MinorUse: its recursive-results list becomes this function pack. Guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:1417. AccWType adequacy group 3.",
            )?;

            // Transport along a reduction of the MINOR. Needs only cr2; its
            // motive-side sibling below uses the restored redTypeStep.
            // Guide :1440.
            self.add_recursive_def(
                "def minorUseW_minor_step (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (m : KExpr) (mn : KExpr) (mn2 : KExpr) (hb : beta_reduces mn mn2) (huse : MinorUseW tenv M m mn) : MinorUseW tenv M m mn2 := fun (f : KExpr) (ihf : KExpr) (hredf : cm_Red tenv M wFieldTy f) (hpoint : forall (d : KExpr), cm_Red tenv M dTypeC d -> cm_Red tenv M (KExpr.app m (KExpr.app f d)) (KExpr.app ihf d)) => CR2 tenv M (KExpr.app m (supApp f)) (KExpr.app (KExpr.app mn f) ihf) (KExpr.app (KExpr.app mn2 f) ihf) (huse f ihf hredf hpoint) (whnf_step.beta (KExpr.app (KExpr.app mn f) ihf) (KExpr.app (KExpr.app mn2 f) ihf) (beta_reduces.app_left (KExpr.app mn f) (KExpr.app mn2 f) ihf (beta_reduces.app_left mn mn2 f hb)))",
                "minorUseW_minor_step: a MinorUseW pack transports along a beta reduction of the MINOR, by CR2 at the doubly-app_left-congruent step. Its motive-side sibling follows below using the restored CandModel.redTypeStep field. Guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:1440. AccWType adequacy group 3.",
            )?;

            // Transport along a reduction of the MOTIVE. This is the sibling
            // that was blocked until `redTypeStep` was restored to CandModel:
            // it moves the candidate along a whnf step of the TYPE index, in
            // both directions (guide :1431 uses .mpr then .mp; here they are
            // AndType.right and AndType.left of the redTypeStep pack).
            {
                // .mpr at the pointwise premise: pull hpoint (stated at m2) back to m.
                let back = "(AndType.right (cm_Red tenv M (KExpr.app m (KExpr.app f d)) (KExpr.app ihf d) -> cm_Red tenv M (KExpr.app m2 (KExpr.app f d)) (KExpr.app ihf d)) (cm_Red tenv M (KExpr.app m2 (KExpr.app f d)) (KExpr.app ihf d) -> cm_Red tenv M (KExpr.app m (KExpr.app f d)) (KExpr.app ihf d)) (redTypeStep_holds tenv M (KExpr.app m (KExpr.app f d)) (KExpr.app m2 (KExpr.app f d)) (KExpr.app ihf d) (whnf_step.beta (KExpr.app m (KExpr.app f d)) (KExpr.app m2 (KExpr.app f d)) (beta_reduces.app_left m m2 (KExpr.app f d) hb))) (hpoint d hd))";
                // .mp at the conclusion: push huse's result from m forward to m2.
                let fwd = format!("(AndType.left (cm_Red tenv M (KExpr.app m (supApp f)) (KExpr.app (KExpr.app mn f) ihf) -> cm_Red tenv M (KExpr.app m2 (supApp f)) (KExpr.app (KExpr.app mn f) ihf)) (cm_Red tenv M (KExpr.app m2 (supApp f)) (KExpr.app (KExpr.app mn f) ihf) -> cm_Red tenv M (KExpr.app m (supApp f)) (KExpr.app (KExpr.app mn f) ihf)) (redTypeStep_holds tenv M (KExpr.app m (supApp f)) (KExpr.app m2 (supApp f)) (KExpr.app (KExpr.app mn f) ihf) (whnf_step.beta (KExpr.app m (supApp f)) (KExpr.app m2 (supApp f)) (beta_reduces.app_left m m2 (supApp f) hb))) (huse f ihf hredf (fun (d : KExpr) (hd : cm_Red tenv M dTypeC d) => {back})))");
                self.add_recursive_def(
                    &format!(
                        "def minorUseW_motive_step (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (m : KExpr) (m2 : KExpr) (mn : KExpr) (hb : beta_reduces m m2) (huse : MinorUseW tenv M m mn) : MinorUseW tenv M m2 mn := fun (f : KExpr) (ihf : KExpr) (hredf : cm_Red tenv M wFieldTy f) (hpoint : forall (d : KExpr), cm_Red tenv M dTypeC d -> cm_Red tenv M (KExpr.app m2 (KExpr.app f d)) (KExpr.app ihf d)) => {fwd}"
                    ),
                    "minorUseW_motive_step: a MinorUseW pack transports along a beta reduction of the MOTIVE. Needs the conversion-transport law in BOTH directions — AndType.right (guide .mpr) to pull the pointwise premise back from m2 to m, then AndType.left (guide .mp) to push the assembled result forward — which is why this one waited on redTypeStep being restored to CandModel while its minor-side sibling did not. Guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:1431. AccWType adequacy group 3.",
                )?;
            }

            // The constructor-generated major class. The `canon` arm is the new
            // shape: a canonical value is `sup f` for a field function that is
            // reducible AND pointwise major-producing — the first-order class's
            // member-field LIST becomes a FUNCTION premise. Guide :1217.
            self.add_inductive(
                "inductive WMajor (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (u : Level) : KExpr -> Type\n| canon : forall (f : KExpr), cm_Red tenv M wFieldTy f -> (forall (d : KExpr), cm_Red tenv M dTypeC d -> WMajor tenv M u (KExpr.app f d)) -> WMajor tenv M u (supApp f)\n| stuck : forall (t : KExpr), Neutral t -> WStuckMajor u t -> (forall (t2 : KExpr), whnf_step t t2 -> WMajor tenv M u t2) -> WMajor tenv M u t",
                "WMajor tenv M u t: the constructor-generated W major class. canon: `sup f` where f is reducible at the field type and POINTWISE major-producing (`f d` is again a major for every reducible domain element d) — an Acc.intro-shaped higher-order premise, the genuinely new content versus a first-order rung. stuck: a neutral, rule-free head all of whose whnf reducts are majors. Guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:1217. AccWType adequacy group 3.",
            )?;

            // Variables are stuck majors. Guide :1227.
            self.add_recursive_def(
                "def wMajor_bvar (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (u : Level) (i : Nat) : WMajor tenv M u (KExpr.bvar i) := WMajor.stuck tenv M u (KExpr.bvar i) ConstFreeUnit.triv (wStuckMajor_bvar u i) (fun (t2 : KExpr) (hstep : whnf_step (KExpr.bvar i) t2) => no_whnf_step_bvar i t2 (WMajor tenv M u t2) hstep)",
                "wMajor_bvar: every bound variable is a (stuck) W major — Neutral by the bvar arm of Neutral, stuck by wStuckMajor_bvar, and its reduct premise is vacuous by no_whnf_step_bvar. Guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:1227. AccWType adequacy group 3.",
            )?;
        }

        // ── ADEQUACY GROUP 4: the CANONICAL arm of W-recursor adequacy ──────
        //
        // `w_adequacy_canon`, guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:1451. THE payoff of the
        // rung: the recursor applied to a canonical major `sup f` is reducible
        // at the motive, given the pointwise IH at each `f d`.
        //
        // Reachable precisely because it does NOT touch the dropped
        // `redTypeStep` field — it needs only `cr1`, `redAbstraction_holds`,
        // `redRecW_holds` and the group-2 SN gate `whnfAcc_supApp`. Its sibling
        // `w_adequacy_stuck` DOES use redTypeStep (twice), which is why the
        // capstone `w_adequacy` (by cases over both arms) is still blocked.
        //
        // Env note: RedRecW quantifies denv/renv, but the spec's whnf_acc gates
        // are env-FIXED, so the concrete instance is denv = red_def the_red_env
        // (witness `wFresh_red`) and renv = wREnv u (witness `wREnv_ok u`).
        {
            let m_ty = "(KExpr.app m (supApp f))";
            let contract = "(wContractum u m mn f)";
            // The pointwise IH premise of redAbstraction, at domain element `a`:
            // hih gives reducibility at the APPLIED forms; the two group-1
            // instantiation equations move it under the binder. Both transports
            // run BACKWARD (Eq.symm), target index first, then the type index.
            let inner = {
                let hih_at = "(hih a ha m mn hm hmn huse)";
                let step1 = format!(
                    "(Eq.rec KExpr (wRecApp u m mn (KExpr.app f a)) (fun (x : KExpr) (_ : Eq KExpr (wRecApp u m mn (KExpr.app f a)) x) => cm_Red tenv M (KExpr.app m (KExpr.app f a)) x) {hih_at} (instantiate (wIhBody u m mn f) a) (Eq.symm KExpr (instantiate (wIhBody u m mn f) a) (wRecApp u m mn (KExpr.app f a)) (wIhBody_inst u m mn f a)))"
                );
                format!(
                    "(fun (a : KExpr) (ha : cm_Red tenv M dTypeC a) => Eq.rec KExpr (KExpr.app m (KExpr.app f a)) (fun (x : KExpr) (_ : Eq KExpr (KExpr.app m (KExpr.app f a)) x) => cm_Red tenv M x (instantiate (wIhBody u m mn f) a)) {step1} (instantiate (wIhCod m f) a) (Eq.symm KExpr (instantiate (wIhCod m f) a) (KExpr.app m (KExpr.app f a)) (wIhCod_inst m f a)))"
                )
            };
            // redAbstraction at A := dTypeC, b := wIhBody, B := wIhCod. Its
            // conclusion's `app (lam A b) d` is already `app (wIhFun u m mn f) d`
            // definitionally, so only the TYPE index needs moving — forward,
            // along wIhCod_inst.
            let hpoint = format!(
                "(fun (d : KExpr) (hd : cm_Red tenv M dTypeC d) => Eq.rec KExpr (instantiate (wIhCod m f) d) (fun (x : KExpr) (_ : Eq KExpr (instantiate (wIhCod m f) d) x) => cm_Red tenv M x (KExpr.app (wIhFun u m mn f) d)) (redAbstraction_holds tenv M dTypeC (wIhBody u m mn f) (wIhCod m f) (whnfAcc_const dName (ListType.nil Level) (wFresh_dom (red_def the_red_env) wFresh_red)) {inner} d hd) (KExpr.app m (KExpr.app f d)) (wIhCod_inst m f d))"
            );
            // wContractum u m mn f == app (app mn f) (wIhFun u m mn f), which is
            // exactly MinorUseW's conclusion shape.
            let hred = format!("(huse f (wIhFun u m mn f) hredf {hpoint})");
            self.add_recursive_def(
                &format!(
                    "def w_adequacy_canon (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (u : Level) \
                     (f : KExpr) (hredf : cm_Red tenv M wFieldTy f) \
                     (hih : forall (d : KExpr), cm_Red tenv M dTypeC d -> forall (m : KExpr) (mn : KExpr), cm_Red tenv M (wMotiveTy u) m -> whnf_acc mn -> MinorUseW tenv M m mn -> cm_Red tenv M (KExpr.app m (KExpr.app f d)) (wRecApp u m mn (KExpr.app f d))) \
                     (m : KExpr) (mn : KExpr) (hm : cm_Red tenv M (wMotiveTy u) m) (hmn : whnf_acc mn) (huse : MinorUseW tenv M m mn) \
                     : cm_Red tenv M {m_ty} (wRecApp u m mn (supApp f)) := \
                     redRecW_holds tenv M u (red_def the_red_env) (wREnv u) m mn (supApp f) {contract} {m_ty} \
                     wFresh_red (wREnv_ok u) (WRecContract.sup u m mn f) \
                     (CR1 tenv M (wMotiveTy u) m hm) hmn \
                     (whnfAcc_supApp (wFresh_sup (red_def the_red_env) wFresh_red) f (CR1 tenv M wFieldTy f hredf)) \
                     {hred}"
                ),
                "w_adequacy_canon: the CANONICAL-major arm of W-recursor adequacy — wRec m mn (sup f) is reducible at the motive, given the pointwise IH at each (f d). Guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:1451. Closes via redRecW_holds at the concrete env pair (red_def the_red_env, wREnv u), with the contractum's reducibility supplied by the MinorUseW pack applied to the IH function wIhFun; that function's pointwise reducibility is redAbstraction over the group-1 instantiation equations wIhCod_inst / wIhBody_inst, which cancel the unit lifts through the field-domain binder. Uses NO redTypeStep. (That was once the reason this arm was reachable while w_adequacy_stuck was not; redTypeStep has since been restored to CandModel and w_adequacy_stuck is landed in this same function, with the capstone w_adequacy dispatching to both.) AccWType adequacy group 4.",
            )?;
        }

        // ── ADEQUACY GROUP 5: the stuck-major spine inversions ─────────────
        //
        // The prerequisites of w_adequacy_stuck. Unlike the rest of this rung
        // these had NO first-order template in the spec (no natRecApp_step_inv /
        // genRecApp_step_inv exists), so they were DERIVED and then hand-checked
        // against the two validated templates const_no_beta_reduces (natrec.rs)
        // and supApp_step_inv above.
        //
        // Registration ORDER matters: wFresh_rec, then the iota gate, then the
        // 1-arg spine, the 2-arg spine, and finally the full inversion — each
        // consumes the previous.
        {
            self.add_recursive_def(
                "def wFresh_rec (denv : DefEnv) (h : WFresh denv) : Eq (OptionType KExpr) (defval_for denv wRecName) (OptionType.none KExpr) := WFresh.rec (fun (_ : WFresh denv) => Eq (OptionType KExpr) (defval_for denv wRecName) (OptionType.none KExpr)) (fun (_h0 : Eq (OptionType KExpr) (defval_for denv dName) (OptionType.none KExpr)) (_h1 : Eq (OptionType KExpr) (defval_for denv wName) (OptionType.none KExpr)) (_h2 : Eq (OptionType KExpr) (defval_for denv supName) (OptionType.none KExpr)) (h3 : Eq (OptionType KExpr) (defval_for denv wRecName) (OptionType.none KExpr)) => h3) h",
                "wFresh_rec: project the wRecName delta-freeness conjunct out of a WFresh pack (FOURTH of four). Feeds the delta arm of wRecApp_step_inv. AccWType adequacy group 5.",
            )?;

            self.add_recursive_def(
                "def iota_reduct_wRecApp_stuck (u : Level) (m : KExpr) (mn : KExpr) (t : KExpr) (hstuck : WStuckMajor u t) : Eq (OptionType KExpr) (iota_reduct (wREnv u) (wRecApp u m mn t)) (OptionType.none KExpr) := OptionType.rec Name (fun (o : OptionType Name) => Eq (OptionType Name) (kexpr_const_name (kapp_fn t)) o -> Eq (OptionType KExpr) (opt_bind Name KExpr o (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for (wREnv u) wRecName cname) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params wRecMeta) (recmeta_num_motives wRecMeta)) (recmeta_num_minors wRecMeta)) (recmeta_num_indices wRecMeta))) (kapp_args (wRecApp u m mn t))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args t)) (recrule_num_fields rule)) (kapp_args t)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params wRecMeta) (recmeta_num_motives wRecMeta)) (recmeta_num_minors wRecMeta)) (kapp_args (wRecApp u m mn t))) (recrule_rhs rule))))))) (OptionType.none KExpr)) (fun (_hnone : Eq (OptionType Name) (kexpr_const_name (kapp_fn t)) (OptionType.none Name)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (fun (cn : Name) (hc : Eq (OptionType Name) (kexpr_const_name (kapp_fn t)) (OptionType.some Name cn)) => Eq.trans (OptionType KExpr) (opt_bind RecRule KExpr (recrule_for (wREnv u) wRecName cn) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params wRecMeta) (recmeta_num_motives wRecMeta)) (recmeta_num_minors wRecMeta)) (recmeta_num_indices wRecMeta))) (kapp_args (wRecApp u m mn t))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args t)) (recrule_num_fields rule)) (kapp_args t)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params wRecMeta) (recmeta_num_motives wRecMeta)) (recmeta_num_minors wRecMeta)) (kapp_args (wRecApp u m mn t))) (recrule_rhs rule)))))) (opt_bind RecRule KExpr (OptionType.none RecRule) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params wRecMeta) (recmeta_num_motives wRecMeta)) (recmeta_num_minors wRecMeta)) (recmeta_num_indices wRecMeta))) (kapp_args (wRecApp u m mn t))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args t)) (recrule_num_fields rule)) (kapp_args t)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params wRecMeta) (recmeta_num_motives wRecMeta)) (recmeta_num_minors wRecMeta)) (kapp_args (wRecApp u m mn t))) (recrule_rhs rule)))))) (OptionType.none KExpr) (Eq.cong (OptionType RecRule) (OptionType KExpr) (fun (O : OptionType RecRule) => opt_bind RecRule KExpr O (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params wRecMeta) (recmeta_num_motives wRecMeta)) (recmeta_num_minors wRecMeta)) (recmeta_num_indices wRecMeta))) (kapp_args (wRecApp u m mn t))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args t)) (recrule_num_fields rule)) (kapp_args t)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params wRecMeta) (recmeta_num_motives wRecMeta)) (recmeta_num_minors wRecMeta)) (kapp_args (wRecApp u m mn t))) (recrule_rhs rule)))))) (recrule_for (wREnv u) wRecName cn) (OptionType.none RecRule) (hstuck cn hc)) (Eq.refl (OptionType KExpr) (OptionType.none KExpr))) (kexpr_const_name (kapp_fn t)) (Eq.refl (OptionType Name) (kexpr_const_name (kapp_fn t)))",
                "iota_reduct_wRecApp_stuck: the schematic iota CANNOT fire on a recursor spine whose major is stuck. iota_reduct nests five opt_binds; for wRecApp the first three (spine head -> wRecName, recmeta_for, major selection) all COMPUTE even with m/mn/t free, because kapp_fn recurses on the function side only and kapp_args/list_drop/list_head scrutinise just the spine shape. So the goal is definitionally an opt_bind on the MAJOR's head name. Dependent OptionType.rec retaining the scrutinee equation: none-arm by rfl, some-arm through the WStuckMajor gate. Guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:1236. DEAD AT PRESENT: zero consumers repo-wide, because wRecApp_step_inv turned out not to need it (see that lemma's CORRECTION note). Kept because it is the faithful analogue of the guide's gate and any future env-parametric restatement will want it. AccWType adequacy group 5.",
            )?;

            self.add_recursive_def(
                "def wRecSpine1_step_inv (u : Level) (m : KExpr) (g2 : KExpr) (C : Type) (hb : beta_reduces (KExpr.app (wRecC u) m) g2) (k : forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr g2 (KExpr.app (wRecC u) m2) -> C) : C := beta_reduces.rec (fun (s : KExpr) (r : KExpr) (_ : beta_reduces s r) => Eq KExpr s (KExpr.app (wRecC u) m) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr r (KExpr.app (wRecC u) m2) -> C) -> C) (fun (A0 : KExpr) (body : KExpr) (arg : KExpr) (heq : Eq KExpr (KExpr.app (KExpr.lam A0 body) arg) (KExpr.app (wRecC u) m)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (instantiate body arg) (KExpr.app (wRecC u) m2) -> C)) => const_ne_lam wRecName (ListType.cons Level u (ListType.nil Level)) A0 body C (Eq.symm KExpr (KExpr.lam A0 body) (wRecC u) (app_inj_fst (KExpr.lam A0 body) arg (wRecC u) m heq))) (fun (g : KExpr) (g3 : KExpr) (a : KExpr) (hstep : beta_reduces g g3) (_ih : Eq KExpr g (KExpr.app (wRecC u) m) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr g3 (KExpr.app (wRecC u) m2) -> C) -> C) (heq : Eq KExpr (KExpr.app g a) (KExpr.app (wRecC u) m)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.app g3 a) (KExpr.app (wRecC u) m2) -> C)) => const_no_beta_reduces wRecName (ListType.cons Level u (ListType.nil Level)) g3 C (Eq.rec KExpr g (fun (x : KExpr) (_ : Eq KExpr g x) => beta_reduces x g3) hstep (wRecC u) (app_inj_fst g a (wRecC u) m heq))) (fun (g : KExpr) (a : KExpr) (a2 : KExpr) (hstep : beta_reduces a a2) (_ih : Eq KExpr a (KExpr.app (wRecC u) m) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr a2 (KExpr.app (wRecC u) m2) -> C) -> C) (heq : Eq KExpr (KExpr.app g a) (KExpr.app (wRecC u) m)) (kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.app g a2) (KExpr.app (wRecC u) m2) -> C)) => kk0 a2 (Eq.rec KExpr a (fun (x : KExpr) (_ : Eq KExpr a x) => beta_reduces x a2) hstep m (app_inj_snd g a (wRecC u) m heq)) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x a2) g (wRecC u) (app_inj_fst g a (wRecC u) m heq))) (fun (ty : KExpr) (ty2 : KExpr) (body : KExpr) (_hstep : beta_reduces ty ty2) (_ih : Eq KExpr ty (KExpr.app (wRecC u) m) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr ty2 (KExpr.app (wRecC u) m2) -> C) -> C) (heq : Eq KExpr (KExpr.lam ty body) (KExpr.app (wRecC u) m)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.lam ty2 body) (KExpr.app (wRecC u) m2) -> C)) => lam_ne_app ty body (wRecC u) m C heq) (fun (ty : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body (KExpr.app (wRecC u) m) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr body2 (KExpr.app (wRecC u) m2) -> C) -> C) (heq : Eq KExpr (KExpr.lam ty body) (KExpr.app (wRecC u) m)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.lam ty body2) (KExpr.app (wRecC u) m2) -> C)) => lam_ne_app ty body (wRecC u) m C heq) (fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hstep : beta_reduces dom dom2) (_ih : Eq KExpr dom (KExpr.app (wRecC u) m) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr dom2 (KExpr.app (wRecC u) m2) -> C) -> C) (heq : Eq KExpr (KExpr.pi dom body) (KExpr.app (wRecC u) m)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.pi dom2 body) (KExpr.app (wRecC u) m2) -> C)) => pi_ne_app dom body (wRecC u) m C heq) (fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body (KExpr.app (wRecC u) m) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr body2 (KExpr.app (wRecC u) m2) -> C) -> C) (heq : Eq KExpr (KExpr.pi dom body) (KExpr.app (wRecC u) m)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.pi dom body2) (KExpr.app (wRecC u) m2) -> C)) => pi_ne_app dom body (wRecC u) m C heq) (fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hstep : beta_reduces dom dom2) (_ih : Eq KExpr dom (KExpr.app (wRecC u) m) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr dom2 (KExpr.app (wRecC u) m2) -> C) -> C) (heq : Eq KExpr (KExpr.forall_ dom body) (KExpr.app (wRecC u) m)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.forall_ dom2 body) (KExpr.app (wRecC u) m2) -> C)) => pi_ne_app dom body (wRecC u) m C heq) (fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body (KExpr.app (wRecC u) m) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr body2 (KExpr.app (wRecC u) m2) -> C) -> C) (heq : Eq KExpr (KExpr.forall_ dom body) (KExpr.app (wRecC u) m)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.forall_ dom body2) (KExpr.app (wRecC u) m2) -> C)) => pi_ne_app dom body (wRecC u) m C heq) (fun (ty : KExpr) (val : KExpr) (body : KExpr) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.app (wRecC u) m)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (instantiate body val) (KExpr.app (wRecC u) m2) -> C)) => let_ne_app ty val body (wRecC u) m C heq) (fun (ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr) (_hstep : beta_reduces ty ty2) (_ih : Eq KExpr ty (KExpr.app (wRecC u) m) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr ty2 (KExpr.app (wRecC u) m2) -> C) -> C) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.app (wRecC u) m)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.let_ ty2 val body) (KExpr.app (wRecC u) m2) -> C)) => let_ne_app ty val body (wRecC u) m C heq) (fun (ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr) (_hstep : beta_reduces val val2) (_ih : Eq KExpr val (KExpr.app (wRecC u) m) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr val2 (KExpr.app (wRecC u) m2) -> C) -> C) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.app (wRecC u) m)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.let_ ty val2 body) (KExpr.app (wRecC u) m2) -> C)) => let_ne_app ty val body (wRecC u) m C heq) (fun (ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body (KExpr.app (wRecC u) m) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr body2 (KExpr.app (wRecC u) m2) -> C) -> C) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.app (wRecC u) m)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.let_ ty val body2) (KExpr.app (wRecC u) m2) -> C)) => let_ne_app ty val body (wRecC u) m C heq) (fun (e0 : KExpr) (e02 : KExpr) (hiota : iota_reduces e0 e02) (heq : Eq KExpr e0 (KExpr.app (wRecC u) m)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr e02 (KExpr.app (wRecC u) m2) -> C)) => option_none_ne_some_type KExpr e02 C (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct (red_rec the_red_env) e0) (OptionType.some KExpr e02) (Eq.symm (OptionType KExpr) (iota_reduct (red_rec the_red_env) e0) (OptionType.none KExpr) (Eq.trans (OptionType KExpr) (iota_reduct (red_rec the_red_env) e0) (iota_reduct (red_rec the_red_env) (KExpr.app (wRecC u) m)) (OptionType.none KExpr) (Eq.cong KExpr (OptionType KExpr) (fun (x : KExpr) => iota_reduct (red_rec the_red_env) x) e0 (KExpr.app (wRecC u) m) heq) (Eq.refl (OptionType KExpr) (OptionType.none KExpr)))) (iota_reduces_to_step e0 e02 hiota))) (fun (ps : Name) (pin : Nat) (sub : KExpr) (sub2 : KExpr) (_hstep : beta_reduces sub sub2) (_ih : Eq KExpr sub (KExpr.app (wRecC u) m) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr sub2 (KExpr.app (wRecC u) m2) -> C) -> C) (heq : Eq KExpr (KExpr.proj ps pin sub) (KExpr.app (wRecC u) m)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.proj ps pin sub2) (KExpr.app (wRecC u) m2) -> C)) => proj_ne_app ps pin sub (wRecC u) m C heq) (KExpr.app (wRecC u) m) g2 hb (Eq.refl KExpr (KExpr.app (wRecC u) m)) k",
                "wRecSpine1_step_inv: invert a beta step of the ONE-argument recursor spine (app (wRecC u) m) into a step of m, in CPS form. 15-arm beta_reduces.rec; the wRecC head is a bare const so const_no_beta_reduces kills the app_left arm, and every non-app source dies by lam/pi/let/proj_ne_app. AccWType adequacy group 5.",
            )?;

            self.add_recursive_def(
                "def wRecSpine2_step_inv (u : Level) (m : KExpr) (mn : KExpr) (g2 : KExpr) (C : Type) (hb : beta_reduces (KExpr.app (KExpr.app (wRecC u) m) mn) g2) (kM : forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr g2 (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C) (kMN : forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr g2 (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C) : C := beta_reduces.rec (fun (s : KExpr) (r : KExpr) (_ : beta_reduces s r) => Eq KExpr s (KExpr.app (KExpr.app (wRecC u) m) mn) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr r (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr r (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C) -> C) (fun (A0 : KExpr) (body : KExpr) (arg : KExpr) (heq : Eq KExpr (KExpr.app (KExpr.lam A0 body) arg) (KExpr.app (KExpr.app (wRecC u) m) mn)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (instantiate body arg) (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (instantiate body arg) (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C)) => lam_ne_app A0 body (wRecC u) m C (app_inj_fst (KExpr.lam A0 body) arg (KExpr.app (wRecC u) m) mn heq)) (fun (g : KExpr) (g3 : KExpr) (a : KExpr) (hstep : beta_reduces g g3) (_ih : Eq KExpr g (KExpr.app (KExpr.app (wRecC u) m) mn) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr g3 (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr g3 (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C) -> C) (heq : Eq KExpr (KExpr.app g a) (KExpr.app (KExpr.app (wRecC u) m) mn)) (kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.app g3 a) (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C)) (kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.app g3 a) (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C)) => wRecSpine1_step_inv u m g3 C (Eq.rec KExpr g (fun (x : KExpr) (_ : Eq KExpr g x) => beta_reduces x g3) hstep (KExpr.app (wRecC u) m) (app_inj_fst g a (KExpr.app (wRecC u) m) mn heq)) (fun (m2 : KExpr) (hm2 : beta_reduces m m2) (heq2 : Eq KExpr g3 (KExpr.app (wRecC u) m2)) => kk0 m2 hm2 (Eq.trans KExpr (KExpr.app g3 a) (KExpr.app (KExpr.app (wRecC u) m2) a) (KExpr.app (KExpr.app (wRecC u) m2) mn) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x a) g3 (KExpr.app (wRecC u) m2) heq2) (Eq.cong KExpr KExpr (fun (y : KExpr) => KExpr.app (KExpr.app (wRecC u) m2) y) a mn (app_inj_snd g a (KExpr.app (wRecC u) m) mn heq))))) (fun (g : KExpr) (a : KExpr) (a2 : KExpr) (hstep : beta_reduces a a2) (_ih : Eq KExpr a (KExpr.app (KExpr.app (wRecC u) m) mn) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr a2 (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr a2 (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C) -> C) (heq : Eq KExpr (KExpr.app g a) (KExpr.app (KExpr.app (wRecC u) m) mn)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.app g a2) (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C)) (kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.app g a2) (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C)) => kk1 a2 (Eq.rec KExpr a (fun (x : KExpr) (_ : Eq KExpr a x) => beta_reduces x a2) hstep mn (app_inj_snd g a (KExpr.app (wRecC u) m) mn heq)) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x a2) g (KExpr.app (wRecC u) m) (app_inj_fst g a (KExpr.app (wRecC u) m) mn heq))) (fun (ty : KExpr) (ty2 : KExpr) (body : KExpr) (_hstep : beta_reduces ty ty2) (_ih : Eq KExpr ty (KExpr.app (KExpr.app (wRecC u) m) mn) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr ty2 (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr ty2 (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C) -> C) (heq : Eq KExpr (KExpr.lam ty body) (KExpr.app (KExpr.app (wRecC u) m) mn)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.lam ty2 body) (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.lam ty2 body) (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C)) => lam_ne_app ty body (KExpr.app (wRecC u) m) mn C heq) (fun (ty : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body (KExpr.app (KExpr.app (wRecC u) m) mn) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr body2 (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr body2 (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C) -> C) (heq : Eq KExpr (KExpr.lam ty body) (KExpr.app (KExpr.app (wRecC u) m) mn)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.lam ty body2) (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.lam ty body2) (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C)) => lam_ne_app ty body (KExpr.app (wRecC u) m) mn C heq) (fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hstep : beta_reduces dom dom2) (_ih : Eq KExpr dom (KExpr.app (KExpr.app (wRecC u) m) mn) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr dom2 (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr dom2 (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C) -> C) (heq : Eq KExpr (KExpr.pi dom body) (KExpr.app (KExpr.app (wRecC u) m) mn)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.pi dom2 body) (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.pi dom2 body) (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C)) => pi_ne_app dom body (KExpr.app (wRecC u) m) mn C heq) (fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body (KExpr.app (KExpr.app (wRecC u) m) mn) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr body2 (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr body2 (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C) -> C) (heq : Eq KExpr (KExpr.pi dom body) (KExpr.app (KExpr.app (wRecC u) m) mn)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.pi dom body2) (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.pi dom body2) (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C)) => pi_ne_app dom body (KExpr.app (wRecC u) m) mn C heq) (fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hstep : beta_reduces dom dom2) (_ih : Eq KExpr dom (KExpr.app (KExpr.app (wRecC u) m) mn) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr dom2 (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr dom2 (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C) -> C) (heq : Eq KExpr (KExpr.forall_ dom body) (KExpr.app (KExpr.app (wRecC u) m) mn)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.forall_ dom2 body) (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.forall_ dom2 body) (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C)) => pi_ne_app dom body (KExpr.app (wRecC u) m) mn C heq) (fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body (KExpr.app (KExpr.app (wRecC u) m) mn) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr body2 (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr body2 (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C) -> C) (heq : Eq KExpr (KExpr.forall_ dom body) (KExpr.app (KExpr.app (wRecC u) m) mn)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.forall_ dom body2) (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.forall_ dom body2) (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C)) => pi_ne_app dom body (KExpr.app (wRecC u) m) mn C heq) (fun (ty : KExpr) (val : KExpr) (body : KExpr) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.app (KExpr.app (wRecC u) m) mn)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (instantiate body val) (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (instantiate body val) (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C)) => let_ne_app ty val body (KExpr.app (wRecC u) m) mn C heq) (fun (ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr) (_hstep : beta_reduces ty ty2) (_ih : Eq KExpr ty (KExpr.app (KExpr.app (wRecC u) m) mn) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr ty2 (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr ty2 (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C) -> C) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.app (KExpr.app (wRecC u) m) mn)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.let_ ty2 val body) (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.let_ ty2 val body) (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C)) => let_ne_app ty val body (KExpr.app (wRecC u) m) mn C heq) (fun (ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr) (_hstep : beta_reduces val val2) (_ih : Eq KExpr val (KExpr.app (KExpr.app (wRecC u) m) mn) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr val2 (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr val2 (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C) -> C) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.app (KExpr.app (wRecC u) m) mn)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.let_ ty val2 body) (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.let_ ty val2 body) (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C)) => let_ne_app ty val body (KExpr.app (wRecC u) m) mn C heq) (fun (ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body (KExpr.app (KExpr.app (wRecC u) m) mn) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr body2 (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr body2 (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C) -> C) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.app (KExpr.app (wRecC u) m) mn)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.let_ ty val body2) (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.let_ ty val body2) (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C)) => let_ne_app ty val body (KExpr.app (wRecC u) m) mn C heq) (fun (e0 : KExpr) (e02 : KExpr) (hiota : iota_reduces e0 e02) (heq : Eq KExpr e0 (KExpr.app (KExpr.app (wRecC u) m) mn)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr e02 (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr e02 (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C)) => option_none_ne_some_type KExpr e02 C (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct (red_rec the_red_env) e0) (OptionType.some KExpr e02) (Eq.symm (OptionType KExpr) (iota_reduct (red_rec the_red_env) e0) (OptionType.none KExpr) (Eq.trans (OptionType KExpr) (iota_reduct (red_rec the_red_env) e0) (iota_reduct (red_rec the_red_env) (KExpr.app (KExpr.app (wRecC u) m) mn)) (OptionType.none KExpr) (Eq.cong KExpr (OptionType KExpr) (fun (x : KExpr) => iota_reduct (red_rec the_red_env) x) e0 (KExpr.app (KExpr.app (wRecC u) m) mn) heq) (Eq.refl (OptionType KExpr) (OptionType.none KExpr)))) (iota_reduces_to_step e0 e02 hiota))) (fun (ps : Name) (pin : Nat) (sub : KExpr) (sub2 : KExpr) (_hstep : beta_reduces sub sub2) (_ih : Eq KExpr sub (KExpr.app (KExpr.app (wRecC u) m) mn) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr sub2 (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr sub2 (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C) -> C) (heq : Eq KExpr (KExpr.proj ps pin sub) (KExpr.app (KExpr.app (wRecC u) m) mn)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.proj ps pin sub2) (KExpr.app (KExpr.app (wRecC u) m2) mn) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.proj ps pin sub2) (KExpr.app (KExpr.app (wRecC u) m) mn2) -> C)) => proj_ne_app ps pin sub (KExpr.app (wRecC u) m) mn C heq) (KExpr.app (KExpr.app (wRecC u) m) mn) g2 hb (Eq.refl KExpr (KExpr.app (KExpr.app (wRecC u) m) mn)) kM kMN",
                "wRecSpine2_step_inv: invert a beta step of the TWO-argument spine (app (app (wRecC u) m) mn) into a step of m or of mn, in CPS form with two continuations. Its app_left arm recurses into wRecSpine1_step_inv. AccWType adequacy group 5.",
            )?;

            self.add_recursive_def(
                "def wRecApp_step_inv (u : Level) (m : KExpr) (mn : KExpr) (t : KExpr) (e2 : KExpr) (C : Type) (hdef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) wRecName) (OptionType.none KExpr)) (hs : whnf_step (wRecApp u m mn t) e2) (kM : forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr e2 (wRecApp u m2 mn t) -> C) (kMN : forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr e2 (wRecApp u m mn2 t) -> C) (kT : forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr e2 (wRecApp u m mn t2) -> C) : C := whnf_step.rec (wRecApp u m mn t) e2 (fun (_ : whnf_step (wRecApp u m mn t) e2) => C) (fun (hbr : beta_reduces (wRecApp u m mn t) e2) => beta_reduces.rec (fun (s : KExpr) (r : KExpr) (_ : beta_reduces s r) => Eq KExpr s (wRecApp u m mn t) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr r (wRecApp u m2 mn t) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr r (wRecApp u m mn2 t) -> C) -> (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr r (wRecApp u m mn t2) -> C) -> C) (fun (A0 : KExpr) (body : KExpr) (arg : KExpr) (heq : Eq KExpr (KExpr.app (KExpr.lam A0 body) arg) (wRecApp u m mn t)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (instantiate body arg) (wRecApp u m2 mn t) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (instantiate body arg) (wRecApp u m mn2 t) -> C)) (_kk2 : (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr (instantiate body arg) (wRecApp u m mn t2) -> C)) => lam_ne_app A0 body (KExpr.app (wRecC u) m) mn C (app_inj_fst (KExpr.lam A0 body) arg (KExpr.app (KExpr.app (wRecC u) m) mn) t heq)) (fun (g : KExpr) (g3 : KExpr) (a : KExpr) (hstep : beta_reduces g g3) (_ih : Eq KExpr g (wRecApp u m mn t) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr g3 (wRecApp u m2 mn t) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr g3 (wRecApp u m mn2 t) -> C) -> (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr g3 (wRecApp u m mn t2) -> C) -> C) (heq : Eq KExpr (KExpr.app g a) (wRecApp u m mn t)) (kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.app g3 a) (wRecApp u m2 mn t) -> C)) (kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.app g3 a) (wRecApp u m mn2 t) -> C)) (_kk2 : (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr (KExpr.app g3 a) (wRecApp u m mn t2) -> C)) => wRecSpine2_step_inv u m mn g3 C (Eq.rec KExpr g (fun (x : KExpr) (_ : Eq KExpr g x) => beta_reduces x g3) hstep (KExpr.app (KExpr.app (wRecC u) m) mn) (app_inj_fst g a (KExpr.app (KExpr.app (wRecC u) m) mn) t heq)) (fun (m2 : KExpr) (hm2 : beta_reduces m m2) (heq2 : Eq KExpr g3 (KExpr.app (KExpr.app (wRecC u) m2) mn)) => kk0 m2 hm2 (Eq.trans KExpr (KExpr.app g3 a) (KExpr.app (KExpr.app (KExpr.app (wRecC u) m2) mn) a) (wRecApp u m2 mn t) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x a) g3 (KExpr.app (KExpr.app (wRecC u) m2) mn) heq2) (Eq.cong KExpr KExpr (fun (y : KExpr) => KExpr.app (KExpr.app (KExpr.app (wRecC u) m2) mn) y) a t (app_inj_snd g a (KExpr.app (KExpr.app (wRecC u) m) mn) t heq)))) (fun (mn2 : KExpr) (hmn2 : beta_reduces mn mn2) (heq2 : Eq KExpr g3 (KExpr.app (KExpr.app (wRecC u) m) mn2)) => kk1 mn2 hmn2 (Eq.trans KExpr (KExpr.app g3 a) (KExpr.app (KExpr.app (KExpr.app (wRecC u) m) mn2) a) (wRecApp u m mn2 t) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x a) g3 (KExpr.app (KExpr.app (wRecC u) m) mn2) heq2) (Eq.cong KExpr KExpr (fun (y : KExpr) => KExpr.app (KExpr.app (KExpr.app (wRecC u) m) mn2) y) a t (app_inj_snd g a (KExpr.app (KExpr.app (wRecC u) m) mn) t heq))))) (fun (g : KExpr) (a : KExpr) (a2 : KExpr) (hstep : beta_reduces a a2) (_ih : Eq KExpr a (wRecApp u m mn t) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr a2 (wRecApp u m2 mn t) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr a2 (wRecApp u m mn2 t) -> C) -> (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr a2 (wRecApp u m mn t2) -> C) -> C) (heq : Eq KExpr (KExpr.app g a) (wRecApp u m mn t)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.app g a2) (wRecApp u m2 mn t) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.app g a2) (wRecApp u m mn2 t) -> C)) (kk2 : (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr (KExpr.app g a2) (wRecApp u m mn t2) -> C)) => kk2 a2 (Eq.rec KExpr a (fun (x : KExpr) (_ : Eq KExpr a x) => beta_reduces x a2) hstep t (app_inj_snd g a (KExpr.app (KExpr.app (wRecC u) m) mn) t heq)) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x a2) g (KExpr.app (KExpr.app (wRecC u) m) mn) (app_inj_fst g a (KExpr.app (KExpr.app (wRecC u) m) mn) t heq))) (fun (ty : KExpr) (ty2 : KExpr) (body : KExpr) (_hstep : beta_reduces ty ty2) (_ih : Eq KExpr ty (wRecApp u m mn t) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr ty2 (wRecApp u m2 mn t) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr ty2 (wRecApp u m mn2 t) -> C) -> (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr ty2 (wRecApp u m mn t2) -> C) -> C) (heq : Eq KExpr (KExpr.lam ty body) (wRecApp u m mn t)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.lam ty2 body) (wRecApp u m2 mn t) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.lam ty2 body) (wRecApp u m mn2 t) -> C)) (_kk2 : (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr (KExpr.lam ty2 body) (wRecApp u m mn t2) -> C)) => lam_ne_app ty body (KExpr.app (KExpr.app (wRecC u) m) mn) t C heq) (fun (ty : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body (wRecApp u m mn t) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr body2 (wRecApp u m2 mn t) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr body2 (wRecApp u m mn2 t) -> C) -> (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr body2 (wRecApp u m mn t2) -> C) -> C) (heq : Eq KExpr (KExpr.lam ty body) (wRecApp u m mn t)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.lam ty body2) (wRecApp u m2 mn t) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.lam ty body2) (wRecApp u m mn2 t) -> C)) (_kk2 : (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr (KExpr.lam ty body2) (wRecApp u m mn t2) -> C)) => lam_ne_app ty body (KExpr.app (KExpr.app (wRecC u) m) mn) t C heq) (fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hstep : beta_reduces dom dom2) (_ih : Eq KExpr dom (wRecApp u m mn t) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr dom2 (wRecApp u m2 mn t) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr dom2 (wRecApp u m mn2 t) -> C) -> (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr dom2 (wRecApp u m mn t2) -> C) -> C) (heq : Eq KExpr (KExpr.pi dom body) (wRecApp u m mn t)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.pi dom2 body) (wRecApp u m2 mn t) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.pi dom2 body) (wRecApp u m mn2 t) -> C)) (_kk2 : (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr (KExpr.pi dom2 body) (wRecApp u m mn t2) -> C)) => pi_ne_app dom body (KExpr.app (KExpr.app (wRecC u) m) mn) t C heq) (fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body (wRecApp u m mn t) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr body2 (wRecApp u m2 mn t) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr body2 (wRecApp u m mn2 t) -> C) -> (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr body2 (wRecApp u m mn t2) -> C) -> C) (heq : Eq KExpr (KExpr.pi dom body) (wRecApp u m mn t)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.pi dom body2) (wRecApp u m2 mn t) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.pi dom body2) (wRecApp u m mn2 t) -> C)) (_kk2 : (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr (KExpr.pi dom body2) (wRecApp u m mn t2) -> C)) => pi_ne_app dom body (KExpr.app (KExpr.app (wRecC u) m) mn) t C heq) (fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hstep : beta_reduces dom dom2) (_ih : Eq KExpr dom (wRecApp u m mn t) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr dom2 (wRecApp u m2 mn t) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr dom2 (wRecApp u m mn2 t) -> C) -> (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr dom2 (wRecApp u m mn t2) -> C) -> C) (heq : Eq KExpr (KExpr.forall_ dom body) (wRecApp u m mn t)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.forall_ dom2 body) (wRecApp u m2 mn t) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.forall_ dom2 body) (wRecApp u m mn2 t) -> C)) (_kk2 : (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr (KExpr.forall_ dom2 body) (wRecApp u m mn t2) -> C)) => pi_ne_app dom body (KExpr.app (KExpr.app (wRecC u) m) mn) t C heq) (fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body (wRecApp u m mn t) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr body2 (wRecApp u m2 mn t) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr body2 (wRecApp u m mn2 t) -> C) -> (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr body2 (wRecApp u m mn t2) -> C) -> C) (heq : Eq KExpr (KExpr.forall_ dom body) (wRecApp u m mn t)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.forall_ dom body2) (wRecApp u m2 mn t) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.forall_ dom body2) (wRecApp u m mn2 t) -> C)) (_kk2 : (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr (KExpr.forall_ dom body2) (wRecApp u m mn t2) -> C)) => pi_ne_app dom body (KExpr.app (KExpr.app (wRecC u) m) mn) t C heq) (fun (ty : KExpr) (val : KExpr) (body : KExpr) (heq : Eq KExpr (KExpr.let_ ty val body) (wRecApp u m mn t)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (instantiate body val) (wRecApp u m2 mn t) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (instantiate body val) (wRecApp u m mn2 t) -> C)) (_kk2 : (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr (instantiate body val) (wRecApp u m mn t2) -> C)) => let_ne_app ty val body (KExpr.app (KExpr.app (wRecC u) m) mn) t C heq) (fun (ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr) (_hstep : beta_reduces ty ty2) (_ih : Eq KExpr ty (wRecApp u m mn t) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr ty2 (wRecApp u m2 mn t) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr ty2 (wRecApp u m mn2 t) -> C) -> (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr ty2 (wRecApp u m mn t2) -> C) -> C) (heq : Eq KExpr (KExpr.let_ ty val body) (wRecApp u m mn t)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.let_ ty2 val body) (wRecApp u m2 mn t) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.let_ ty2 val body) (wRecApp u m mn2 t) -> C)) (_kk2 : (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr (KExpr.let_ ty2 val body) (wRecApp u m mn t2) -> C)) => let_ne_app ty val body (KExpr.app (KExpr.app (wRecC u) m) mn) t C heq) (fun (ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr) (_hstep : beta_reduces val val2) (_ih : Eq KExpr val (wRecApp u m mn t) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr val2 (wRecApp u m2 mn t) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr val2 (wRecApp u m mn2 t) -> C) -> (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr val2 (wRecApp u m mn t2) -> C) -> C) (heq : Eq KExpr (KExpr.let_ ty val body) (wRecApp u m mn t)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.let_ ty val2 body) (wRecApp u m2 mn t) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.let_ ty val2 body) (wRecApp u m mn2 t) -> C)) (_kk2 : (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr (KExpr.let_ ty val2 body) (wRecApp u m mn t2) -> C)) => let_ne_app ty val body (KExpr.app (KExpr.app (wRecC u) m) mn) t C heq) (fun (ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body (wRecApp u m mn t) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr body2 (wRecApp u m2 mn t) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr body2 (wRecApp u m mn2 t) -> C) -> (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr body2 (wRecApp u m mn t2) -> C) -> C) (heq : Eq KExpr (KExpr.let_ ty val body) (wRecApp u m mn t)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.let_ ty val body2) (wRecApp u m2 mn t) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.let_ ty val body2) (wRecApp u m mn2 t) -> C)) (_kk2 : (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr (KExpr.let_ ty val body2) (wRecApp u m mn t2) -> C)) => let_ne_app ty val body (KExpr.app (KExpr.app (wRecC u) m) mn) t C heq) (fun (e0 : KExpr) (e02 : KExpr) (hiota : iota_reduces e0 e02) (heq : Eq KExpr e0 (wRecApp u m mn t)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr e02 (wRecApp u m2 mn t) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr e02 (wRecApp u m mn2 t) -> C)) (_kk2 : (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr e02 (wRecApp u m mn t2) -> C)) => option_none_ne_some_type KExpr e02 C (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct (red_rec the_red_env) e0) (OptionType.some KExpr e02) (Eq.symm (OptionType KExpr) (iota_reduct (red_rec the_red_env) e0) (OptionType.none KExpr) (Eq.trans (OptionType KExpr) (iota_reduct (red_rec the_red_env) e0) (iota_reduct (red_rec the_red_env) (wRecApp u m mn t)) (OptionType.none KExpr) (Eq.cong KExpr (OptionType KExpr) (fun (x : KExpr) => iota_reduct (red_rec the_red_env) x) e0 (wRecApp u m mn t) heq) (Eq.refl (OptionType KExpr) (OptionType.none KExpr)))) (iota_reduces_to_step e0 e02 hiota))) (fun (ps : Name) (pin : Nat) (sub : KExpr) (sub2 : KExpr) (_hstep : beta_reduces sub sub2) (_ih : Eq KExpr sub (wRecApp u m mn t) -> (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr sub2 (wRecApp u m2 mn t) -> C) -> (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr sub2 (wRecApp u m mn2 t) -> C) -> (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr sub2 (wRecApp u m mn t2) -> C) -> C) (heq : Eq KExpr (KExpr.proj ps pin sub) (wRecApp u m mn t)) (_kk0 : (forall (m2 : KExpr), beta_reduces m m2 -> Eq KExpr (KExpr.proj ps pin sub2) (wRecApp u m2 mn t) -> C)) (_kk1 : (forall (mn2 : KExpr), beta_reduces mn mn2 -> Eq KExpr (KExpr.proj ps pin sub2) (wRecApp u m mn2 t) -> C)) (_kk2 : (forall (t2 : KExpr), beta_reduces t t2 -> Eq KExpr (KExpr.proj ps pin sub2) (wRecApp u m mn t2) -> C)) => proj_ne_app ps pin sub (KExpr.app (KExpr.app (wRecC u) m) mn) t C heq) (wRecApp u m mn t) e2 hbr (Eq.refl KExpr (wRecApp u m mn t)) kM kMN kT) (fun (hdr : delta_reduces (wRecApp u m mn t) e2) => option_none_ne_some_type KExpr e2 C (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (delta_reduct (red_def the_red_env) (wRecApp u m mn t)) (OptionType.some KExpr e2) (Eq.symm (OptionType KExpr) (delta_reduct (red_def the_red_env) (wRecApp u m mn t)) (OptionType.none KExpr) (delta_reduct_eq_none_of_defval_none (red_def the_red_env) (wRecApp u m mn t) wRecName (Eq.refl (OptionType Name) (OptionType.some Name wRecName)) hdef)) (delta_reduces_to_step (wRecApp u m mn t) e2 hdr))) hs",
                "wRecApp_step_inv: every whnf step of the recursor spine wRecApp u m mn t is a congruence step in one of m, mn, t, delivered to whichever of three continuations applies. CORRECTION: an earlier description said 'over a STUCK major' and 'exactly one'. There is NO WStuckMajor hypothesis -- see the note below on why none is needed -- and CPS form hands the caller ONE continuation without asserting the others are unreachable. Stated in 3-continuation CPS form (kM/kMN/kT) rather than as a nested OrType, the same choice supApp_step_inv makes and far more robust than assembling a disjunction. The delta arm dies on the wRecName freshness hypothesis and the app_left arm recurses through wRecSpine2_step_inv. CORRECTION: the iota arm does NOT use iota_reduct_wRecApp_stuck -- it closes by Eq.refl, because whnf_step/iota_reduces are hardwired to the_red_env, which keys no wRec recursor at all, so the spine can never iota-fire REGARDLESS of the major's head. This proves something strictly STRONGER than the guide (which needs a stuckness gate because its iota lives at wREnv u), and it means this lemma needs no WStuckMajor hypothesis. Guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:1276. AccWType adequacy group 5.",
            )?;
        }

        // ── ADEQUACY GROUP 6: the stuck arm and THE CAPSTONE ───────────────
        //
        // Split into per-continuation case lemmas rather than one monolith, so
        // that a failure isolates to one small declaration instead of costing a
        // whole 30-minute validation cycle on a 3k-character term.
        //
        // The double Acc induction in w_adequacy_stuck follows the VALIDATED
        // whnfAcc_pi template (dependent_sn_richmodel.rs:2993): the outer motive
        // QUANTIFIES the inner subject so the inner induction can re-instantiate
        // it, and the outer IH is re-fired by rebuilding the inner accessibility
        // with whnf_acc.intro.
        {
            self.add_recursive_def(
                "def neutral_wRecApp (u : Level) (m : KExpr) (mn : KExpr) (t : KExpr) : Neutral (wRecApp u m mn t) := ConstFreeUnit.triv",
                "neutral_wRecApp: the recursor spine wRecApp u m mn t is Neutral, by ConstFreeUnit.triv. CORRECTION: an earlier description implied the wRec head was doing work and that this was the one step needing validation. It is not. Neutral (dependent_sn_richmodel.rs) is a KExpr.rec whose app arm is unconditional -- EVERY KExpr.app is Neutral, the head is irrelevant, and the fact is decided by one constructor arm. Kept as its own declaration for readability at the CR3 call site, not because it was uncertain. AccWType adequacy group 6.",
            )?;

            self.add_recursive_def(
                "def w_stuck_motive_case (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (u : Level) (t : KExpr) (m0 : KExpr) (m2 : KExpr) (mn1 : KExpr) (e2 : KExpr) (hm0 : cm_Red tenv M (wMotiveTy u) m0) (huse1 : MinorUseW tenv M m0 mn1) (hmnacc : forall (mn2 : KExpr), whnf_step mn1 mn2 -> whnf_acc mn2) (ihm : forall (m3 : KExpr), whnf_step m0 m3 -> cm_Red tenv M (wMotiveTy u) m3 -> forall (mnb : KExpr), whnf_acc mnb -> MinorUseW tenv M m3 mnb -> cm_Red tenv M (KExpr.app m3 t) (wRecApp u m3 mnb t)) (hb : beta_reduces m0 m2) (heq : Eq KExpr e2 (wRecApp u m2 mn1 t)) : cm_Red tenv M (KExpr.app m0 t) e2 := Eq.substType KExpr (fun (x : KExpr) => cm_Red tenv M (KExpr.app m0 t) x) (wRecApp u m2 mn1 t) e2 (Eq.symm KExpr e2 (wRecApp u m2 mn1 t) heq) (AndType.right (cm_Red tenv M (KExpr.app m0 t) (wRecApp u m2 mn1 t) -> cm_Red tenv M (KExpr.app m2 t) (wRecApp u m2 mn1 t)) (cm_Red tenv M (KExpr.app m2 t) (wRecApp u m2 mn1 t) -> cm_Red tenv M (KExpr.app m0 t) (wRecApp u m2 mn1 t)) (redTypeStep_holds tenv M (KExpr.app m0 t) (KExpr.app m2 t) (wRecApp u m2 mn1 t) (whnf_step.beta (KExpr.app m0 t) (KExpr.app m2 t) (beta_reduces.app_left m0 m2 t hb))) (ihm m2 (whnf_step.beta m0 m2 hb) (CR2 tenv M (wMotiveTy u) m0 m2 hm0 (whnf_step.beta m0 m2 hb)) mn1 (whnf_acc.intro mn1 hmnacc) (minorUseW_motive_step tenv M m0 m2 mn1 hb huse1)))",
                "w_stuck_motive_case: the kM continuation of wRecApp_step_inv — a step in the MOTIVE m. Transports the candidate along the type-index step via redTypeStep (AndType.right -- the BACKWARD implication, the guide's .mpr, pulling the result back from the reduced motive; an earlier description said AndType.left, which the term does not use) and re-fires the outer Acc induction hypothesis at the reduced motive, carrying the MinorUseW pack across by minorUseW_motive_step. AccWType adequacy group 6.",
            )?;

            self.add_recursive_def(
                "def w_stuck_minor_case (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (u : Level) (t : KExpr) (m0 : KExpr) (mn1 : KExpr) (mn2 : KExpr) (e2 : KExpr) (huse1 : MinorUseW tenv M m0 mn1) (ihmn : forall (mn3 : KExpr), whnf_step mn1 mn3 -> MinorUseW tenv M m0 mn3 -> cm_Red tenv M (KExpr.app m0 t) (wRecApp u m0 mn3 t)) (hb : beta_reduces mn1 mn2) (heq : Eq KExpr e2 (wRecApp u m0 mn2 t)) : cm_Red tenv M (KExpr.app m0 t) e2 := Eq.substType KExpr (fun (x : KExpr) => cm_Red tenv M (KExpr.app m0 t) x) (wRecApp u m0 mn2 t) e2 (Eq.symm KExpr e2 (wRecApp u m0 mn2 t) heq) (ihmn mn2 (whnf_step.beta mn1 mn2 hb) (minorUseW_minor_step tenv M m0 mn1 mn2 hb huse1))",
                "w_stuck_minor_case: the kMN continuation — a step in the MINOR mn. The type index is unchanged, so this needs only the inner Acc induction hypothesis plus minorUseW_minor_step. AccWType adequacy group 6.",
            )?;

            self.add_recursive_def(
                "def w_stuck_major_case (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (u : Level) (t : KExpr) (m0 : KExpr) (mn1 : KExpr) (t2 : KExpr) (e2 : KExpr) (hm0 : cm_Red tenv M (wMotiveTy u) m0) (huse1 : MinorUseW tenv M m0 mn1) (hmnacc : forall (mn2 : KExpr), whnf_step mn1 mn2 -> whnf_acc mn2) (hih : forall (t3 : KExpr), whnf_step t t3 -> forall (m3 : KExpr) (mn3 : KExpr), cm_Red tenv M (wMotiveTy u) m3 -> whnf_acc mn3 -> MinorUseW tenv M m3 mn3 -> cm_Red tenv M (KExpr.app m3 t3) (wRecApp u m3 mn3 t3)) (hb : beta_reduces t t2) (heq : Eq KExpr e2 (wRecApp u m0 mn1 t2)) : cm_Red tenv M (KExpr.app m0 t) e2 := Eq.substType KExpr (fun (x : KExpr) => cm_Red tenv M (KExpr.app m0 t) x) (wRecApp u m0 mn1 t2) e2 (Eq.symm KExpr e2 (wRecApp u m0 mn1 t2) heq) (AndType.right (cm_Red tenv M (KExpr.app m0 t) (wRecApp u m0 mn1 t2) -> cm_Red tenv M (KExpr.app m0 t2) (wRecApp u m0 mn1 t2)) (cm_Red tenv M (KExpr.app m0 t2) (wRecApp u m0 mn1 t2) -> cm_Red tenv M (KExpr.app m0 t) (wRecApp u m0 mn1 t2)) (redTypeStep_holds tenv M (KExpr.app m0 t) (KExpr.app m0 t2) (wRecApp u m0 mn1 t2) (whnf_step.beta (KExpr.app m0 t) (KExpr.app m0 t2) (beta_reduces.app_right m0 t t2 hb))) (hih t2 (whnf_step.beta t t2 hb) m0 mn1 hm0 (whnf_acc.intro mn1 hmnacc) huse1))",
                "w_stuck_major_case: the kT continuation — a step in the MAJOR t. Discharged by the caller-supplied hih at the reduct, transported along the type-index step by redTypeStep (AndType.right). AccWType adequacy group 6.",
            )?;

            self.add_recursive_def(
                "def w_stuck_node (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (u : Level) (t : KExpr) (hih : forall (t3 : KExpr), whnf_step t t3 -> forall (m3 : KExpr) (mn3 : KExpr), cm_Red tenv M (wMotiveTy u) m3 -> whnf_acc mn3 -> MinorUseW tenv M m3 mn3 -> cm_Red tenv M (KExpr.app m3 t3) (wRecApp u m3 mn3 t3)) (m0 : KExpr) (mn1 : KExpr) (hm0 : cm_Red tenv M (wMotiveTy u) m0) (hmnacc : forall (mn2 : KExpr), whnf_step mn1 mn2 -> whnf_acc mn2) (ihm : forall (m3 : KExpr), whnf_step m0 m3 -> cm_Red tenv M (wMotiveTy u) m3 -> forall (mnb : KExpr), whnf_acc mnb -> MinorUseW tenv M m3 mnb -> cm_Red tenv M (KExpr.app m3 t) (wRecApp u m3 mnb t)) (ihmn : forall (mn3 : KExpr), whnf_step mn1 mn3 -> MinorUseW tenv M m0 mn3 -> cm_Red tenv M (KExpr.app m0 t) (wRecApp u m0 mn3 t)) (huse1 : MinorUseW tenv M m0 mn1) : cm_Red tenv M (KExpr.app m0 t) (wRecApp u m0 mn1 t) := CR3 tenv M (KExpr.app m0 t) (wRecApp u m0 mn1 t) (neutral_wRecApp u m0 mn1 t) (fun (e2 : KExpr) (hstep : whnf_step (wRecApp u m0 mn1 t) e2) => wRecApp_step_inv u m0 mn1 t e2 (cm_Red tenv M (KExpr.app m0 t) e2) (wFresh_rec (red_def the_red_env) wFresh_red) hstep (fun (m2 : KExpr) (hbm : beta_reduces m0 m2) (heqm : Eq KExpr e2 (wRecApp u m2 mn1 t)) => w_stuck_motive_case tenv M u t m0 m2 mn1 e2 hm0 huse1 hmnacc ihm hbm heqm) (fun (mn2 : KExpr) (hbmn : beta_reduces mn1 mn2) (heqmn : Eq KExpr e2 (wRecApp u m0 mn2 t)) => w_stuck_minor_case tenv M u t m0 mn1 mn2 e2 huse1 ihmn hbmn heqmn) (fun (t2 : KExpr) (hbt : beta_reduces t t2) (heqt : Eq KExpr e2 (wRecApp u m0 mn1 t2)) => w_stuck_major_case tenv M u t m0 mn1 t2 e2 hm0 huse1 hmnacc hih hbt heqt))",
                "w_stuck_node: ONE node of the stuck-major induction. Applies CR3 at the neutral recursor spine (neutral_wRecApp) and dispatches each whnf reduct through wRecApp_step_inv's three continuations into the three case lemmas above. AccWType adequacy group 6.",
            )?;

            self.add_recursive_def(
                "def w_adequacy_stuck (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (u : Level) (t : KExpr) (hst : WStuckMajor u t) (hih : forall (t3 : KExpr), whnf_step t t3 -> forall (m3 : KExpr) (mn3 : KExpr), cm_Red tenv M (wMotiveTy u) m3 -> whnf_acc mn3 -> MinorUseW tenv M m3 mn3 -> cm_Red tenv M (KExpr.app m3 t3) (wRecApp u m3 mn3 t3)) (m : KExpr) (mn : KExpr) (hm : cm_Red tenv M (wMotiveTy u) m) (hmn : whnf_acc mn) (huse : MinorUseW tenv M m mn) : cm_Red tenv M (KExpr.app m t) (wRecApp u m mn t) := whnf_acc.rec (fun (m0 : KExpr) (_hacc : whnf_acc m0) => cm_Red tenv M (wMotiveTy u) m0 -> forall (mna : KExpr), whnf_acc mna -> MinorUseW tenv M m0 mna -> cm_Red tenv M (KExpr.app m0 t) (wRecApp u m0 mna t)) (fun (m0 : KExpr) (_hmsteps : forall (m2 : KExpr), whnf_step m0 m2 -> whnf_acc m2) (ihm : forall (m2 : KExpr), whnf_step m0 m2 -> cm_Red tenv M (wMotiveTy u) m2 -> forall (mnb : KExpr), whnf_acc mnb -> MinorUseW tenv M m2 mnb -> cm_Red tenv M (KExpr.app m2 t) (wRecApp u m2 mnb t)) => fun (hm0 : cm_Red tenv M (wMotiveTy u) m0) (mn0 : KExpr) (hmn0 : whnf_acc mn0) (huse0 : MinorUseW tenv M m0 mn0) => whnf_acc.rec (fun (mn1 : KExpr) (_hacc2 : whnf_acc mn1) => MinorUseW tenv M m0 mn1 -> cm_Red tenv M (KExpr.app m0 t) (wRecApp u m0 mn1 t)) (fun (mn1 : KExpr) (hmnacc : forall (mn2 : KExpr), whnf_step mn1 mn2 -> whnf_acc mn2) (ihmn : forall (mn2 : KExpr), whnf_step mn1 mn2 -> MinorUseW tenv M m0 mn2 -> cm_Red tenv M (KExpr.app m0 t) (wRecApp u m0 mn2 t)) => fun (huse1 : MinorUseW tenv M m0 mn1) => w_stuck_node tenv M u t hih m0 mn1 hm0 hmnacc ihm ihmn huse1) mn0 hmn0 huse0) m (CR1 tenv M (wMotiveTy u) m hm) hm mn hmn huse",
                "w_adequacy_stuck: the STUCK-major arm of W-recursor adequacy (guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:1478). Double accessibility induction — outer whnf_acc.rec on the motive m with the motive QUANTIFYING mn so the inner induction can re-instantiate it, inner whnf_acc.rec on mn — following the validated whnfAcc_pi template (dependent_sn_richmodel.rs:2993), then w_stuck_node at each node. NOTE: the hst : WStuckMajor u t parameter is DEAD in the body and kept only so the capstone's WMajor.rec stuck arm lines up without eta-expansion; the spec's whnf_step is pinned to the_red_env which keys no wRec recursor, so the spine cannot iota-fire regardless of the major's head and no stuckness gate is needed. That makes this strictly stronger than the guide's version. AccWType adequacy group 6.",
            )?;

            self.add_recursive_def(
                "def w_adequacy (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (u : Level) (t : KExpr) (ht : WMajor tenv M u t) : forall (m : KExpr) (mn : KExpr), cm_Red tenv M (wMotiveTy u) m -> whnf_acc mn -> MinorUseW tenv M m mn -> cm_Red tenv M (KExpr.app m t) (wRecApp u m mn t) := WMajor.rec tenv M u (fun (t0 : KExpr) (_hmaj : WMajor tenv M u t0) => forall (m : KExpr) (mn : KExpr), cm_Red tenv M (wMotiveTy u) m -> whnf_acc mn -> MinorUseW tenv M m mn -> cm_Red tenv M (KExpr.app m t0) (wRecApp u m mn t0)) (fun (f : KExpr) (hredf : cm_Red tenv M wFieldTy f) (_hpt : forall (d : KExpr), cm_Red tenv M dTypeC d -> WMajor tenv M u (KExpr.app f d)) (ihc : forall (d : KExpr), cm_Red tenv M dTypeC d -> forall (m : KExpr) (mn : KExpr), cm_Red tenv M (wMotiveTy u) m -> whnf_acc mn -> MinorUseW tenv M m mn -> cm_Red tenv M (KExpr.app m (KExpr.app f d)) (wRecApp u m mn (KExpr.app f d))) => w_adequacy_canon tenv M u f hredf ihc) (fun (t0 : KExpr) (_hn : Neutral t0) (hst0 : WStuckMajor u t0) (_hcl : forall (t2 : KExpr), whnf_step t0 t2 -> WMajor tenv M u t2) (ihs : forall (t2 : KExpr), whnf_step t0 t2 -> forall (m : KExpr) (mn : KExpr), cm_Red tenv M (wMotiveTy u) m -> whnf_acc mn -> MinorUseW tenv M m mn -> cm_Red tenv M (KExpr.app m t2) (wRecApp u m mn t2)) => w_adequacy_stuck tenv M u t0 hst0 ihs) t ht",
                "w_adequacy: HIGHER-ORDER W-RECURSOR ADEQUACY, the capstone of the W/Acc rung (guide U-aristotle-acc-wtype-sn/.../AccWTypeSN.lean:1555). Two-arm WMajor.rec dispatching the canonical major to w_adequacy_canon and the stuck major to w_adequacy_stuck. Conditional on CandModel, the labeled Godel-floor reducibility-candidate hypothesis, as every theorem in this layer is. AccWType adequacy group 6.",
            )?;
        }

        // whnfAcc_iMajor_nil — relocated here from add_snschema. It consumes
        // whnfAcc_const, which lives in THIS function (stage 135), not in
        // add_acc_wtype_objects; add_snschema is stage 132, so registering it
        // there failed with "Unknown identifier: whnfAcc_const". The trap:
        // acc_wtype.rs hosts TWO registration fns at very different stages, so a
        // file:line citation says nothing about scope.
        self.add_recursive_def(
            "def whnfAcc_iMajor_nil (fam : Name) (j : Nat) (hdef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) (ctorName fam j)) (OptionType.none KExpr)) : whnf_acc (ctorApp fam j (ListType.nil KExpr)) := whnfAcc_const (ctorName fam j) (ListType.nil Level) hdef",
            "whnfAcc_iMajor_nil: whnf_acc (ctorApp fam j nil). CORRECTION: an earlier description said 'an indexed major with an empty index vector'; ctorApp has NO index-vector parameter -- its third argument is the constructor's ARGUMENT spine (ctorApp fam j fields := apply_spine fields (ctorC fam j), schema.rs:183), and in idx_adequacy_canon_of_red the index vector is the separate ix. At fields = nil the subject is literally the bare const ctorC fam j, so this is the const-irreducibility gate applied at an empty spine, nothing more. Relocated to the late add_acc_wtype for whnfAcc_const scope. Indexed adequacy Phase 2.",
        )?;

        // ctorApp_whnfAcc — relocated from add_mutual_schema (stage 134). It is
        // the MUTUAL lane's canonical-spine SN lemma, but it consumes
        // whnfAcc_const, registered in THIS function at stage 135. Cross-lane
        // placement forced by scope, not by topic.
        self.add_recursive_def(
            "def ctorApp_whnfAcc (fam : Name) (j : Nat) (fields : ListType KExpr) (hdef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) (ctorName fam j)) (OptionType.none KExpr)) (hrec : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) (ctorName fam j)) (OptionType.none RecMeta)) (hfields : WhnfAccAll fields) : whnf_acc (ctorApp fam j fields) := whnfAcc_inertSpine (ctorName fam j) hdef hrec fields hfields (ctorC fam j) (Eq.refl (OptionType Name) (OptionType.some Name (ctorName fam j))) (whnfAcc_const (ctorName fam j) (ListType.nil Level) hdef)",
            "ctorApp_whnfAcc: a constructor spine is strongly normalizing when its fields are — the mutual lane's canonical-major SN gate, via the const-irreducibility lemma whnfAcc_const. Relocated here for that dependency's scope. MutSchema adequacy Phase 2.",
        )?;

        // ── MUT + IDX ADEQUACY: the canonical-major arms ───────────────────
        //
        // Cross-lane placement, forced by SCOPE not topic: both consume
        // ctorApp_whnfAcc, which lives in THIS function (stage 135), while their
        // own lanes sit at 132/134. Same reason ctorApp_whnfAcc itself was moved
        // here.
        //
        // SCOPE, stated plainly: these are CONDITIONAL CANONICAL-MAJOR
        // theorems. Each takes the contractum's reducibility `hred` as a
        // hypothesis and closes in one application of the projected CandModel
        // field. They are NOT the two-arm `WMajor.rec` dispatch that
        // `w_adequacy` is — there is no stuck arm and no major induction here.
        // The guides scope them the same way. So the W lane remains the only
        // one of the four with a full capstone; Mut and Idx have their
        // canonical arms only.
        self.add_recursive_def(
            "def mut_adequacy (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (msig : ListType FamSpec) (u : Level) (denv : DefEnv) (hf : MutFresh msig denv) (hd : FamNamesDistinct msig) (i : Nat) (j : Nat) (rs : ListType Nat) (mj : KExpr) (T : KExpr) (cs : ListType KExpr) (ms : ListType KExpr) (fields : ListType KExpr) (hspec : Eq (OptionType (ListType Nat)) (ctorSpecAt msig i j) (OptionType.some (ListType Nat) rs)) (hcs : Eq Nat (list_length cs) (famCount msig)) (hms : Eq Nat (list_length ms) (mutNumMinors msig)) (hmj : Eq (OptionType KExpr) (listGet ms (Nat.add (mutOffset msig i) j)) (OptionType.some KExpr mj)) (hfl : Eq Nat (list_length fields) (sigLength rs)) (hcsSN : WhnfAccAll cs) (hmsSN : WhnfAccAll ms) (hfieldsSN : WhnfAccAll fields) (hdefC : Eq (OptionType KExpr) (defval_for (red_def the_red_env) (ctorName (famNameAt msig i) j)) (OptionType.none KExpr)) (hrecC : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) (ctorName (famNameAt msig i) j)) (OptionType.none RecMeta)) (hred : cm_Red tenv M T (mutContractum msig u cs ms mj rs fields)) : cm_Red tenv M T (mutRecApp msig u i cs ms (ctorApp (famNameAt msig i) j fields)) := redRecMut_holds tenv M msig u i denv (mutREnv msig u) cs ms (ctorApp (famNameAt msig i) j fields) (mutContractum msig u cs ms mj rs fields) T hf (mutREnv_ok msig u hd) (MutRecContract.rule msig u i j rs mj cs ms fields hspec hcs hms hmj hfl) hcsSN hmsSN (ctorApp_whnfAcc (famNameAt msig i) j fields hdefC hrecC hfieldsSN) hred",
            "mut_adequacy: the CANONICAL-major arm of mutual-block recursor adequacy — wRec-style spine over a constructor-headed major is reducible at the motive, GIVEN the contractum's reducibility as an explicit hypothesis. Guide MutualAdequacy.lean:3175. SCOPE: this is a CONDITIONAL canonical case, not a two-arm major dispatch like w_adequacy — the guide itself scopes it that way. Registered at stage 135 because its SN gate ctorApp_whnfAcc lives here. MutSchema adequacy Phase 3.",
        )?;

        self.add_recursive_def(
            "def specGet_lt (sig : ListType (ListType Nat)) (rs : ListType Nat) (j : Nat) (h : Eq (OptionType (ListType Nat)) (specGet sig j) (OptionType.some (ListType Nat) rs)) : Lt j (ctorCount sig) := ListType.rec (ListType Nat) (fun (sg : ListType (ListType Nat)) => forall (j0 : Nat), Eq (OptionType (ListType Nat)) (specGet sg j0) (OptionType.some (ListType Nat) rs) -> Lt j0 (ctorCount sg)) (fun (j0 : Nat) (h0 : Eq (OptionType (ListType Nat)) (specGet (ListType.nil (ListType Nat)) j0) (OptionType.some (ListType Nat) rs)) => option_none_ne_some_type (ListType Nat) rs (Lt j0 (ctorCount (ListType.nil (ListType Nat)))) h0) (fun (rh : ListType Nat) (rt : ListType (ListType Nat)) (ih : forall (j0 : Nat), Eq (OptionType (ListType Nat)) (specGet rt j0) (OptionType.some (ListType Nat) rs) -> Lt j0 (ctorCount rt)) => fun (j0 : Nat) => Nat.rec (fun (jj : Nat) => Eq (OptionType (ListType Nat)) (specGet (ListType.cons (ListType Nat) rh rt) jj) (OptionType.some (ListType Nat) rs) -> Lt jj (ctorCount (ListType.cons (ListType Nat) rh rt))) (fun (_hz : Eq (OptionType (ListType Nat)) (specGet (ListType.cons (ListType Nat) rh rt) Nat.zero) (OptionType.some (ListType Nat) rs)) => Lt.zero_lt_succ (ctorCount rt)) (fun (j1 : Nat) (_ihj : Eq (OptionType (ListType Nat)) (specGet (ListType.cons (ListType Nat) rh rt) j1) (OptionType.some (ListType Nat) rs) -> Lt j1 (ctorCount (ListType.cons (ListType Nat) rh rt))) => fun (hs : Eq (OptionType (ListType Nat)) (specGet (ListType.cons (ListType Nat) rh rt) (Nat.succ j1)) (OptionType.some (ListType Nat) rs)) => Lt.succ_lt_succ j1 (ctorCount rt) (ih j1 hs)) j0) sig j h",
            "specGet_lt: index-bound helper for the mutual family-spec lookup. MutSchema adequacy Phase 3.",
        )?;

        self.add_recursive_def(
            "def isigGet_lt (isig : ListType ICtor) (d : ICtor) (j : Nat) (h : Eq (OptionType ICtor) (isigGet isig j) (OptionType.some ICtor d)) : Lt j (iSigLength isig) := ListType.rec ICtor (fun (l : ListType ICtor) => forall (j0 : Nat), Eq (OptionType ICtor) (isigGet l j0) (OptionType.some ICtor d) -> Lt j0 (iSigLength l)) (fun (j0 : Nat) (h0 : Eq (OptionType ICtor) (isigGet (ListType.nil ICtor) j0) (OptionType.some ICtor d)) => option_none_ne_some_type ICtor d (Lt j0 (iSigLength (ListType.nil ICtor))) h0) (fun (dh : ICtor) (rest : ListType ICtor) (ih : forall (j0 : Nat), Eq (OptionType ICtor) (isigGet rest j0) (OptionType.some ICtor d) -> Lt j0 (iSigLength rest)) => fun (j0 : Nat) => Nat.rec (fun (jj : Nat) => Eq (OptionType ICtor) (isigGet (ListType.cons ICtor dh rest) jj) (OptionType.some ICtor d) -> Lt jj (iSigLength (ListType.cons ICtor dh rest))) (fun (_hz : Eq (OptionType ICtor) (isigGet (ListType.cons ICtor dh rest) Nat.zero) (OptionType.some ICtor d)) => Lt.zero_lt_succ (iSigLength rest)) (fun (j1 : Nat) (_ihj : Eq (OptionType ICtor) (isigGet (ListType.cons ICtor dh rest) j1) (OptionType.some ICtor d) -> Lt j1 (iSigLength (ListType.cons ICtor dh rest))) => fun (hs : Eq (OptionType ICtor) (isigGet (ListType.cons ICtor dh rest) (Nat.succ j1)) (OptionType.some ICtor d)) => Lt.succ_lt_succ j1 (iSigLength rest) (ih j1 hs)) j0) isig j h",
            "isigGet_lt: index-bound helper for the indexed ctor-spec lookup. Indexed adequacy Phase 3.",
        )?;

        self.add_recursive_def(
            "def idx_adequacy_canon_of_red (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (iFam : Name) (fam : Name) (nIdx : Nat) (isig : ListType ICtor) (u : Level) (denv : DefEnv) (j : Nat) (d : ICtor) (m : KExpr) (mj : KExpr) (ms : ListType KExpr) (ix : ListType KExpr) (avec : ListType KExpr) (fields : ListType KExpr) (hfresh : IGenFresh fam isig denv) (hjd : Eq (OptionType ICtor) (isigGet isig j) (OptionType.some ICtor d)) (hms_len : Eq Nat (list_length ms) (iSigLength isig)) (hmj : Eq (OptionType KExpr) (listGet ms j) (OptionType.some KExpr mj)) (hix_len : Eq Nat (list_length ix) nIdx) (has_len : Eq Nat (list_length avec) (icP d)) (hf_len : Eq Nat (list_length fields) (recsLen (icRecs d))) (hdefC : Eq (OptionType KExpr) (defval_for (red_def the_red_env) (ctorName fam j)) (OptionType.none KExpr)) (hrecC : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) (ctorName fam j)) (OptionType.none RecMeta)) (hm : whnf_acc m) (hmsA : WhnfAccAll ms) (hixA : WhnfAccAll ix) (hasA : WhnfAccAll avec) (hfA : WhnfAccAll fields) (hred : cm_Red tenv M (motApp m ix (ctorApp fam j (list_append avec fields))) (iContractum fam isig u m mj ms avec fields d)) : cm_Red tenv M (motApp m ix (ctorApp fam j (list_append avec fields))) (iRecApp fam isig u m ms ix (ctorApp fam j (list_append avec fields))) := redRecIdx_holds tenv M iFam fam nIdx isig u denv (iREnv iFam fam nIdx isig u) m ms ix (ctorApp fam j (list_append avec fields)) (iContractum fam isig u m mj ms avec fields d) (motApp m ix (ctorApp fam j (list_append avec fields))) hfresh (iREnv_ok iFam fam nIdx isig u) (IGenRecContract.rule fam nIdx isig u j d m mj ms ix avec fields hjd hms_len hmj hix_len has_len hf_len) hm hmsA hixA (ctorApp_whnfAcc fam j (list_append avec fields) hdefC hrecC (whnfAccAll_append avec fields hasA hfA)) hred",
            "idx_adequacy_canon_of_red: the CANONICAL-major arm of indexed-family recursor adequacy, conditional on the contractum's reducibility. Guide IndexedAdequacy.lean:1310. NAMED for what it is: like mut_adequacy this is the conditional canonical case, NOT a full capstone with a stuck arm and major dispatch. Registered at stage 135 for ctorApp_whnfAcc scope. Indexed adequacy Phase 3.",
        )?;

        Ok(())
    }
}
