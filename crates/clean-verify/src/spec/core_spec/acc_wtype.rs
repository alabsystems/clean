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
//! wREnv_ok); the SN/adequacy theorems are deferred (they need the env-fixed
//! CandModel rework, analogous to redNatRec -> redRecGen). Census stays 11.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Higher-order-fields (W-type) rung object layer + rfl validations.
    /// Terminal lemma layer (reuses only foundation + rec_env + iota_step +
    /// expr_model), registered after the other schema rungs.
    pub(super) fn add_acc_wtype(&mut self) -> Result<(), SpecError> {
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

        Ok(())
    }
}
