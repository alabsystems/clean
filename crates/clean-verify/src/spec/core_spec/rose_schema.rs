// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nested-inductive rung (10th fragment increment): rose trees
//! `Rose := node (children : List Rose)` — the constructor NESTS the family
//! under a container (List Rose), the shape beyond mutual/higher-order. The
//! recursor uses a fused List.rec to map over the children, so the nested
//! container is modeled as its own object-level family (List Rose with
//! nil/cons/rec). Ported from the Aristotle-proven w5/wave-9 nested-rose guide
//! (`scratch/aristotle-harvest/U-aristotle-nested-rose/
//! aristotle-nested-rose_aristotle/NestedRoseSN.lean` — IN THE TREE as of the
//! 2026-07-26 second rescue; `whnf_terminates_well_typed_rose` proven via the
//! roseTEnv backbone, and exactly two of its theorems carry `sorryAx`:
//! `rose_recContract_steps` and `whnf_terminates_roseRec_open`, which are the
//! two deferred below. See scratch/aristotle-harvest/UNRESCUED_CENSUS_2026-07-26.md)
//! through the workflow port-draft
//! scratch/port-nested-rose.md. Object layer + rfl gates + the SN one-liner;
//! roseRecRhs_instIter is LANDED (2026-07-28) along with its beta-chain layer.
//!
//! CORRECTION to this header's earlier claim: it said all three remaining
//! theorems "need a whnf_step/RoseMajor reduction substrate not yet in-spec".
//! That was wrong twice over. `beta_reduces` (whnf_reduction.rs:117),
//! `whnf_step` (:138) and `whnf_acc` (:161) have been registered since stage
//! 29, and `natrec.rs` built a full env-parametric reduction substrate
//! (iotaCong / natStep / natSteps / natRecContract_steps) at stage 79. The real
//! constraint is that `whnf_step`'s iota is PINNED to `the_red_env`, which keys
//! no rose recursor -- the same structural fact the W lane records for
//! `wRecName`. And `roseRecRhs_instIter` needed none of it: it is a pure beta
//! chain with no env dependence.
//!
//! `rose_recContract_steps` is now DERIVED (2026-07-28) — the guide leaves it
//! `by sorry` at :3579, so there was no term to port; see the group comment at
//! its registration for why it needed its own `roseSteps` relation (the landed
//! `whnf_red_step_star` has no `app_right`, and rose's contractum reduces
//! entirely under one).
//!
//! `whnf_terminates_roseRec_open` (guide :3653, also `by sorry`) is NOT derived,
//! and the reason is structural rather than a matter of effort:
//!
//!  1. AS THE GUIDE STATES IT, IT IS NOT STATABLE HERE. Its conclusion is
//!     `WhnfAcc denv (roseREnv u) ...` — env-PARAMETRIC accessibility in which
//!     the rose iota fires. The spec's `whnf_acc` (whnf_reduction.rs:161) is
//!     accessibility over `whnf_step`, whose iota and delta legs are both pinned
//!     to `the_red_env`. No RecEnv-generic accessibility exists in core_spec.
//!  2. THE INERTNESS SHORTCUT IS A RENAME, NOT A PROOF. `roseRecName` keys
//!     nothing in `the_red_env` (rose_schema.rs, two rfl witnesses; and
//!     structurally, all 127 generated red-env names are FLAT
//!     `Name.str Name.anonymous k` while every rose name is nested). So
//!     `whnf_acc (roseRecApp u C m t)` from its parts is EXACTLY the already
//!     landed `roseRecApp_whnfAcc_inert`. Emitting that under the guide's name
//!     would be a masquerade, and was deliberately refused.
//!  3. THE FAITHFUL ROUTES NEED NEW INDUCTIVES: either a rose-parametric
//!     accessibility over the `roseSteps` substrate (a real reducibility
//!     argument, not an inertness one), or the W-lane shape — a `RoseMajor`
//!     canon/stuck inductive plus `rose_adequacy` in `cm_Red`.
//!  4. THE W-LANE ROUTE ALSO NEEDS a `redRose` CandModel law (the four existing
//!     `redRec*` fields do not instantiate at the 3-argument `roseRecApp`) and a
//!     ~15k-character `roseRecApp_step_inv` inversion. `rose_recContract_steps` additionally needs a
//! prerequisite this port dropped: the landed `roseREnv` carries ONLY the rose
//! rule, whereas the guide's is two-layer and also carries the fused List.rec
//! rules (roseListRecMeta / RhsNil / RhsCons / Rules, guide :3336-3363). The
//! guide's own R9 note claiming otherwise is stale against its own R3 code.
//! Census stays 11.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Nested-inductive (rose-tree) rung object layer + rfl gates + SN one-liner.
    /// Terminal lemma layer, registered after add_acc_wtype.
    pub(super) fn add_rose_schema(&mut self) -> Result<(), SpecError> {
        // Coded names: Rose family, node ctor, Rose.rec; the nested List Rose
        // container as its own family (List, nil/cons/rec).
        self.add_recursive_def(
            "def roseName : Name := Name.str Name.anonymous (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))",
            "roseName: the Rose family name (code 5). Rose rung.",
        )?;
        self.add_recursive_def(
            "def nodeName : Name := Name.str roseName Nat.zero",
            "nodeName: the node constructor name. Rose rung.",
        )?;
        self.add_recursive_def(
            "def roseRecName : Name := Name.str roseName (Nat.succ Nat.zero)",
            "roseRecName: the Rose recursor name. Rose rung.",
        )?;
        self.add_recursive_def(
            "def roseListName : Name := Name.str Name.anonymous (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))",
            "roseListName: the nested List Rose container family name (code 6). Rose rung.",
        )?;
        self.add_recursive_def(
            "def listNilName : Name := Name.str roseListName Nat.zero",
            "listNilName: List Rose nil constructor name. Rose rung.",
        )?;
        self.add_recursive_def(
            "def listConsName : Name := Name.str roseListName (Nat.succ Nat.zero)",
            "listConsName: List Rose cons constructor name. Rose rung.",
        )?;
        self.add_recursive_def(
            "def listRecName : Name := Name.str roseListName (Nat.succ (Nat.succ Nat.zero))",
            "listRecName: List Rose recursor name (the fused-map recursor). Rose rung.",
        )?;
        // Constant heads.
        self.add_recursive_def(
            "def nodeC : KExpr := KExpr.const nodeName (ListType.nil Level)",
            "nodeC: the node constructor constant. Rose rung.",
        )?;
        self.add_recursive_def(
            "def roseRecC (u : Level) : KExpr := KExpr.const roseRecName (ListType.cons Level u (ListType.nil Level))",
            "roseRecC u: the Rose recursor constant. Rose rung.",
        )?;
        self.add_recursive_def(
            "def listNilC : KExpr := KExpr.const listNilName (ListType.nil Level)",
            "listNilC: List Rose nil constant. Rose rung.",
        )?;
        self.add_recursive_def(
            "def listConsC : KExpr := KExpr.const listConsName (ListType.nil Level)",
            "listConsC: List Rose cons constant. Rose rung.",
        )?;
        self.add_recursive_def(
            "def listRecC (u : Level) : KExpr := KExpr.const listRecName (ListType.cons Level u (ListType.nil Level))",
            "listRecC u: List Rose recursor constant. Rose rung.",
        )?;
        // Type constants + the children-list object folder + node/recApp spines.
        self.add_recursive_def(
            "def roseTyC : KExpr := famTypeC roseName",
            "roseTyC: the Rose family type constant. Rose rung.",
        )?;
        self.add_recursive_def(
            "def roseListTyC : KExpr := famTypeC roseListName",
            "roseListTyC: the List Rose family type constant. Rose rung.",
        )?;
        self.add_recursive_def(
            "def roseList (l : ListType KExpr) : KExpr := ListType.rec KExpr (fun (_ : ListType KExpr) => KExpr) listNilC (fun (x : KExpr) (rest : ListType KExpr) (ih : KExpr) => KExpr.app (KExpr.app listConsC x) ih) l",
            "roseList l: fold a meta children list into an object-level List Rose spine (nil/cons consts). Rose rung.",
        )?;
        self.add_recursive_def(
            "def roseNode (cs : KExpr) : KExpr := KExpr.app nodeC cs",
            "roseNode cs: the node constructor applied to a children List Rose. Rose rung.",
        )?;
        self.add_recursive_def(
            "def roseRecApp (u : Level) (C : KExpr) (m : KExpr) (t : KExpr) : KExpr := KExpr.app (KExpr.app (KExpr.app (roseRecC u) C) m) t",
            "roseRecApp u C m t: a fully-applied Rose recursor spine. Rose rung.",
        )?;
        // Recursor type (nested motive) + the fused-List.rec rule rhs.
        self.add_recursive_def(
            "def roseNodeMinorTy (u : Level) : KExpr := KExpr.pi roseListTyC (KExpr.pi roseListTyC (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.app nodeC (KExpr.bvar (Nat.succ Nat.zero)))))",
            "roseNodeMinorTy u: the node minor type — takes the children list and the per-element IH list, concludes C (node cs). Rose rung.",
        )?;
        self.add_recursive_def(
            "def roseRecTy (u : Level) : KExpr := KExpr.pi (genMotiveTy roseName u) (KExpr.pi (roseNodeMinorTy u) (KExpr.pi roseTyC (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))))",
            "roseRecTy u: THE Rose dependent recursor type (motive, node-minor, major -> motive at major). Rose rung.",
        )?;
        self.add_recursive_def(
            "def roseConsCase (u : Level) : KExpr := KExpr.lam roseTyC (KExpr.lam roseListTyC (KExpr.lam roseListTyC (KExpr.app (KExpr.app listConsC (roseRecApp u (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar Nat.zero))))",
            "roseConsCase u: the cons case of the fused map — maps the recursor over the head, conses the tail's mapped result. Rose rung.",
        )?;
        self.add_recursive_def(
            "def roseMapMotive : KExpr := KExpr.lam roseListTyC roseListTyC",
            "roseMapMotive: the (constant) motive of the fused List.rec map. Rose rung.",
        )?;
        self.add_recursive_def(
            "def roseMapTerm (u : Level) : KExpr := KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) roseMapMotive) listNilC) (roseConsCase u)) (KExpr.bvar Nat.zero)",
            "roseMapTerm u: List.rec mapping the recursor over the children (the fused nested-to-mutual map). Rose rung.",
        )?;
        self.add_recursive_def(
            "def roseRecRhsBody (u : Level) : KExpr := KExpr.app (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (roseMapTerm u)",
            "roseRecRhsBody u: the node rule-rhs body = minor applied to children and the fused-mapped recursive results. Rose rung.",
        )?;
        self.add_recursive_def(
            "def roseRecRhs (u : Level) : KExpr := KExpr.lam (genMotiveTy roseName u) (KExpr.lam (roseNodeMinorTy u) (KExpr.lam roseListTyC (roseRecRhsBody u)))",
            "roseRecRhs u: the full node rule-rhs lambda (lam motive, minor, children; body = roseRecRhsBody). Rose rung.",
        )?;
        // Metadata, rules, env.
        self.add_recursive_def(
            "def roseRecMeta : RecMeta := RecMeta.mk Nat.zero (Nat.succ Nat.zero) (Nat.succ Nat.zero) Nat.zero Bool.true",
            "roseRecMeta: Rose recursor metadata (0 params, 1 motive, 1 minor, 0 indices, major-after-minors). Rose rung.",
        )?;
        self.add_recursive_def(
            "def roseRecRules (u : Level) : RecRules := RecRules.cons (RecRule.mk nodeName (Nat.succ Nat.zero) (roseRecRhs u)) RecRules.nil",
            "roseRecRules u: the Rose recursor's single node rule. Rose rung.",
        )?;

        // ── The FUSED auxiliary List.rec layer (2026-07-28) ────────────────
        //
        // The original port registered a SINGLE-LAYER roseREnv carrying only the
        // rose rule, silently dropping the four declarations below. The guide's
        // roseREnv (NestedRoseSN.lean:3367) is TWO-layer and also carries the
        // fused List.rec rules; without them the nested-to-mutual computation
        // rule cannot fire, because the rose rhs maps an auxiliary List.rec over
        // its children. The guide's own R9 note saying roseREnv carries only the
        // rose rule is stale against its own R3 code, and
        // scratch/port-nested-rose.md inherited that staleness.
        //
        // All four are pure data (RecMeta/KExpr/RecRules) with no proof
        // obligation, so this is a faithful transcription, not a derivation.
        self.add_recursive_def(
            "def roseListRecMeta : RecMeta := RecMeta.mk Nat.zero (Nat.succ Nat.zero) (Nat.succ (Nat.succ Nat.zero)) Nat.zero Bool.true",
            "roseListRecMeta: metadata for the FUSED auxiliary List.rec that the rose recursor's rhs maps over its children — 0 params, 1 motive, 2 minors, 0 indices. Guide NestedRoseSN.lean:3336.",
        )?;

        self.add_recursive_def(
            "def roseListRecRhsNil : KExpr := KExpr.lam (genMotiveTy roseListName Level.zero) (KExpr.lam roseListTyC (KExpr.lam roseListTyC (KExpr.bvar (Nat.succ Nat.zero))))",
            "roseListRecRhsNil: the fused list recursor's nil rule, `fun C z s => z`. Guide NestedRoseSN.lean:3339.",
        )?;

        self.add_recursive_def(
            "def roseListRecRhsCons (u : Level) : KExpr := KExpr.lam (genMotiveTy roseListName Level.zero) (KExpr.lam roseListTyC (KExpr.lam roseListTyC (KExpr.lam roseTyC (KExpr.lam roseListTyC (KExpr.app (KExpr.app (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))))))",
            "roseListRecRhsCons: the fused list recursor's cons rule, `fun C z s h t => s h t (List.rec C z s t)` — the nested-to-mutual step where the recursive call descends into the tail. Guide NestedRoseSN.lean:3346.",
        )?;

        self.add_recursive_def(
            "def roseListRecRules (u : Level) : RecRules := RecRules.cons (RecRule.mk listNilName Nat.zero roseListRecRhsNil) (RecRules.cons (RecRule.mk listConsName (Nat.succ (Nat.succ Nat.zero)) (roseListRecRhsCons u)) RecRules.nil)",
            "roseListRecRules: the two rules of the fused auxiliary list recursor (nil/0 fields, cons/2 fields). Guide NestedRoseSN.lean:3361.",
        )?;
        self.add_recursive_def(
            "def roseREnv (u : Level) : RecEnv := RecEnv.addRec (RecEnv.addRec RecEnv.empty listRecName roseListRecMeta (roseListRecRules u)) roseRecName roseRecMeta (roseRecRules u)",
            "roseREnv u: the Rose recursor environment. Rose rung.",
        )?;
        self.add_recursive_def(
            "def roseContractum (u : Level) (C : KExpr) (m : KExpr) (children : ListType KExpr) : KExpr := KExpr.app (KExpr.app m (roseList children)) (roseList (mapLT (fun (x : KExpr) => roseRecApp u C m x) children))",
            "roseContractum u C m children: the Rose iota contractum = minor applied to the children and the mapped recursive results. Rose rung.",
        )?;
        // The contraction relation + the two wellformedness gates.
        self.add_inductive(
            "inductive RoseRecContract (u : Level) : KExpr -> KExpr -> Type\n| node : forall (C : KExpr) (m : KExpr) (children : ListType KExpr), RoseRecContract u (roseRecApp u C m (roseNode (roseList children))) (roseContractum u C m children)",
            "RoseRecContract u lhs rhs: the Rose iota rule — rec on (node children) contracts to minor applied to children and the mapped recursive results. Rose rung.",
        )?;
        self.add_inductive(
            "inductive RoseFresh : DefEnv -> Type\n| mk : forall (denv : DefEnv), Eq (OptionType KExpr) (defval_for denv roseName) (OptionType.none KExpr) -> Eq (OptionType KExpr) (defval_for denv nodeName) (OptionType.none KExpr) -> Eq (OptionType KExpr) (defval_for denv roseRecName) (OptionType.none KExpr) -> Eq (OptionType KExpr) (defval_for denv roseListName) (OptionType.none KExpr) -> Eq (OptionType KExpr) (defval_for denv listNilName) (OptionType.none KExpr) -> Eq (OptionType KExpr) (defval_for denv listConsName) (OptionType.none KExpr) -> Eq (OptionType KExpr) (defval_for denv listRecName) (OptionType.none KExpr) -> RoseFresh denv",
            "RoseFresh denv: the Rose/List family/ctor/recursor names are all unbound in denv. Rose rung.",
        )?;
        self.add_inductive(
            "inductive RoseRecEnvOK : Level -> RecEnv -> Type\n| mk : forall (u : Level) (renv : RecEnv), Eq (OptionType RecMeta) (recmeta_for renv roseRecName) (OptionType.some RecMeta roseRecMeta) -> Eq (OptionType RecRule) (recrule_for renv roseRecName nodeName) (OptionType.some RecRule (RecRule.mk nodeName (Nat.succ Nat.zero) (roseRecRhs u))) -> RoseRecEnvOK u renv",
            "RoseRecEnvOK u renv: renv stores the Rose recursor metadata + the node rule. Rose rung.",
        )?;
        // rfl gates (LOUD validation of the whole nested wiring incl. the fused map).
        self.add_recursive_def(
            "def rose_iota_fires_gen (u : Level) (C : KExpr) (m : KExpr) (cs : KExpr) : iota_step (roseREnv u) (roseRecApp u C m (roseNode cs)) (KExpr.app (KExpr.app (KExpr.app (roseRecRhs u) C) m) cs) := Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.app (KExpr.app (KExpr.app (roseRecRhs u) C) m) cs))",
            "rose_iota_fires_gen: the Rose iota FIRES by rfl (rec C m (node cs) -> roseRecRhs C m cs). THE loud validation gate for the nested object-layer wiring. Rose rung.",
        )?;
        self.add_recursive_def(
            "def roseREnv_ok (u : Level) : RoseRecEnvOK u (roseREnv u) := RoseRecEnvOK.mk u (roseREnv u) (Eq.refl (OptionType RecMeta) (OptionType.some RecMeta roseRecMeta)) (Eq.refl (OptionType RecRule) (OptionType.some RecRule (RecRule.mk nodeName (Nat.succ Nat.zero) (roseRecRhs u))))",
            "roseREnv_ok u: RoseRecEnvOK holds for roseREnv by rfl. Rose rung.",
        )?;
        // SN via the fundamental-theorem one-liner (mirror mutTEnv/wTEnv).
        self.add_recursive_def(
            "def roseTEnv (u : Level) (n : Name) : OptionType KExpr := opt_pick KExpr (name_eqb n roseName) (KExpr.sort (Level.succ Level.zero)) (opt_pick KExpr (name_eqb n nodeName) (KExpr.pi roseListTyC roseTyC) (opt_pick KExpr (name_eqb n roseRecName) (roseRecTy u) (opt_pick KExpr (name_eqb n roseListName) (KExpr.sort (Level.succ Level.zero)) (opt_pick KExpr (name_eqb n listNilName) roseListTyC (opt_pick KExpr (name_eqb n listConsName) (KExpr.pi roseTyC (KExpr.pi roseListTyC roseListTyC)) (opt_pick KExpr (name_eqb n listRecName) (roseRecTy u) (OptionType.none KExpr)))))))",
            "roseTEnv u: the Rose+List const-typing env (families at Sort 1; node at List Rose->Rose; cons at Rose->List->List; recursors at their rec types). Rose rung SN.",
        )?;
        self.add_recursive_def(
            "def whnf_terminates_well_typed_rose (u : Level) (M : CandModel (roseTEnv u)) (e : KExpr) (T : KExpr) (h : TypingCtx (roseTEnv u) (ListType.nil KExpr) e T) : whnf_acc e := whnf_terminates_well_typed_dependent (roseTEnv u) M e T h",
            "whnf_terminates_well_typed_rose: every closed well-typed term over the Rose+List typing env is whnf_acc (SN), modulo M : CandModel (roseTEnv u). One-line specialization of whnf_terminates_well_typed_dependent, mirroring gen/idx/mut/w/nat. THE nested-inductive recursor SN theorem — 10th fragment-ladder rung SN payoff. Rose rung SN.",
        )?;
        // Non-vacuity: node [] : Rose is well-typed and SN through the env.
        self.add_recursive_def(
            "def roseLeaf_typed (u : Level) : TypingCtx (roseTEnv u) (ListType.nil KExpr) (roseNode (roseList (ListType.nil KExpr))) roseTyC := TypingCtx.app (roseTEnv u) (ListType.nil KExpr) nodeC listNilC roseListTyC roseTyC (TypingCtx.const (roseTEnv u) (ListType.nil KExpr) nodeName (ListType.nil Level) (KExpr.pi roseListTyC roseTyC) (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.pi roseListTyC roseTyC)))) (TypingCtx.const (roseTEnv u) (ListType.nil KExpr) listNilName (ListType.nil Level) roseListTyC (Eq.refl (OptionType KExpr) (OptionType.some KExpr roseListTyC)))",
            "roseLeaf_typed u: node [] : Rose typed through roseTEnv (non-vacuity witness). Rose rung.",
        )?;
        self.add_recursive_def(
            "def roseLeaf_sn (u : Level) (M : CandModel (roseTEnv u)) : whnf_acc (roseNode (roseList (ListType.nil KExpr))) := whnf_terminates_well_typed_rose u M (roseNode (roseList (ListType.nil KExpr))) roseTyC (roseLeaf_typed u)",
            "roseLeaf_sn: node [] is whnf_acc via the SN one-liner (non-vacuity of the rose SN theorem). Rose rung.",
        )?;

        // ── RUNG 10: the deferred beta-chain layer ─────────────────────────
        //
        // The module header deferred three theorems on the grounds that they
        // "need a whnf_step/RoseMajor reduction substrate not yet in-spec".
        // That justification was WRONG: beta_reduces (whnf_reduction.rs:117),
        // whnf_step (:138) and whnf_acc (:161) have been registered since stage
        // 29, and natrec.rs built an env-parametric reduction substrate
        // (iotaCong/natStep/natSteps/natRecContract_steps) at stage 79. The real
        // constraint is that whnf_step's iota is PINNED to the_red_env, which
        // keys no rose recursor -- the same fact the W lane records for wRecName.
        //
        // roseRecRhs_instIter needed none of that: it is a pure beta chain. The
        // guide proves it and this is the port.
        //
        // STILL DEFERRED, and NOT invented here: rose_recContract_steps and
        // whnf_terminates_roseRec_open are `by sorry` in the guide
        // (NestedRoseSN.lean:3579 and :3653). There is no proof term to port.
        // Beyond that, rose_recContract_steps has a real prerequisite the port
        // dropped: the landed roseREnv carries ONLY the rose rule, while the
        // guide's is two-layer and also carries the fused List.rec rules
        // (roseListRecMeta/RhsNil/RhsCons/Rules, guide :3336-3363). The guide's
        // own R9 note claiming otherwise is stale against its own R3 code.
        self.add_recursive_def(
            "def roseRhsBeta (u : Level) (C : KExpr) (m : KExpr) (cs : KExpr) : KExpr := instantiate_at (instantiate_at (instantiate_at (roseRecRhsBody u) C (Nat.succ (Nat.succ Nat.zero))) m (Nat.succ Nat.zero)) cs Nat.zero",
            "roseRhsBeta: the single beta contraction of the rose rule-rhs applied to its motive. Pure beta, no env dependence.",
        )?;

        self.add_recursive_def(
            "def roseRhsInst1 (u : Level) (C : KExpr) : KExpr := KExpr.lam (instantiate_at (roseNodeMinorTy u) C Nat.zero) (KExpr.lam (instantiate_at roseListTyC C (Nat.succ Nat.zero)) (instantiate_at (roseRecRhsBody u) C (Nat.succ (Nat.succ Nat.zero))))",
            "roseRhsInst1: first instantiation step of the rose rule-rhs telescope (motive binder).",
        )?;

        self.add_recursive_def(
            "def roseRhsInst2 (u : Level) (C : KExpr) (m : KExpr) : KExpr := KExpr.lam (instantiate_at (instantiate_at roseListTyC C (Nat.succ Nat.zero)) m Nat.zero) (instantiate_at (instantiate_at (roseRecRhsBody u) C (Nat.succ (Nat.succ Nat.zero))) m (Nat.succ Nat.zero))",
            "roseRhsInst2: second instantiation step (node-minor binder).",
        )?;

        self.add_recursive_def(
            "def roseRecRhs_betaStar (u : Level) (C : KExpr) (m : KExpr) (cs : KExpr) : beta_reduces_bd_star (KExpr.app (KExpr.app (KExpr.app (roseRecRhs u) C) m) cs) (roseRhsBeta u C m cs) := beta_reduces_bd_star.step (KExpr.app (KExpr.app (KExpr.app (roseRecRhs u) C) m) cs) (KExpr.app (KExpr.app (roseRhsInst1 u C) m) cs) (roseRhsBeta u C m cs) (beta_reduces_bd.app_left (KExpr.app (KExpr.app (roseRecRhs u) C) m) (KExpr.app (roseRhsInst1 u C) m) cs (beta_reduces_bd.app_left (KExpr.app (roseRecRhs u) C) (roseRhsInst1 u C) m (beta_reduces_bd.beta (genMotiveTy roseName u) (KExpr.lam (roseNodeMinorTy u) (KExpr.lam roseListTyC (roseRecRhsBody u))) C))) (beta_reduces_bd_star.step (KExpr.app (KExpr.app (roseRhsInst1 u C) m) cs) (KExpr.app (roseRhsInst2 u C m) cs) (roseRhsBeta u C m cs) (beta_reduces_bd.app_left (KExpr.app (roseRhsInst1 u C) m) (roseRhsInst2 u C m) cs (beta_reduces_bd.beta (instantiate_at (roseNodeMinorTy u) C Nat.zero) (KExpr.lam (instantiate_at roseListTyC C (Nat.succ Nat.zero)) (instantiate_at (roseRecRhsBody u) C (Nat.succ (Nat.succ Nat.zero)))) m)) (beta_reduces_bd_star.step (KExpr.app (roseRhsInst2 u C m) cs) (roseRhsBeta u C m cs) (roseRhsBeta u C m cs) (beta_reduces_bd.beta (instantiate_at (instantiate_at roseListTyC C (Nat.succ Nat.zero)) m Nat.zero) (instantiate_at (instantiate_at (roseRecRhsBody u) C (Nat.succ (Nat.succ Nat.zero))) m (Nat.succ Nat.zero)) cs) (beta_reduces_bd_star.refl (roseRhsBeta u C m cs))))",
            "roseRecRhs_betaStar: the full beta chain from the applied rose rule-rhs to its contractum, composing the three instantiation steps. The de Bruijn bookkeeping the guide's KEY-4.28 gotcha warns about.",
        )?;

        self.add_recursive_def(
            "def roseRecRhs_instIter (u : Level) (d : DefEnv) (C : KExpr) (m : KExpr) (cs : KExpr) : whnf_red_step_star (RedEnv.mk (roseREnv u) d) (KExpr.app (KExpr.app (KExpr.app (roseRecRhs u) C) m) cs) (roseRhsBeta u C m cs) := beta_bd_star_to_whnf_red_star (RedEnv.mk (roseREnv u) d) (KExpr.app (KExpr.app (KExpr.app (roseRecRhs u) C) m) cs) (roseRhsBeta u C m cs) (roseRecRhs_betaStar u C m cs)",
            "roseRecRhs_instIter: iterated instantiation of the rose rule-rhs yields the contractum. DEFERRAL RETIRED: the module header listed this as needing 'a whnf_step/RoseMajor reduction substrate not yet in-spec'. That was wrong on both counts -- beta_reduces/whnf_step/whnf_acc have been in-spec since stage 29, and this theorem is a pure beta-chain statement with no env dependence at all. The guide PROVES it (NestedRoseSN.lean:3531-3535, `repeat constructor`); this is the explicit-term port. Rung 10.",
        )?;

        self.add_recursive_def(
            "def rose_iota_beta_steps (u : Level) (d : DefEnv) (C : KExpr) (m : KExpr) (cs : KExpr) : whnf_red_step_star (RedEnv.mk (roseREnv u) d) (roseRecApp u C m (roseNode cs)) (roseRhsBeta u C m cs) := whnf_red_step_star.step (RedEnv.mk (roseREnv u) d) (roseRecApp u C m (roseNode cs)) (KExpr.app (KExpr.app (KExpr.app (roseRecRhs u) C) m) cs) (roseRhsBeta u C m cs) (whnf_red_step.iota (RedEnv.mk (roseREnv u) d) (roseRecApp u C m (roseNode cs)) (KExpr.app (KExpr.app (KExpr.app (roseRecRhs u) C) m) cs) (rose_iota_fires_gen u C m cs)) (roseRecRhs_instIter u d C m cs)",
            "rose_iota_beta_steps: the rose iota fire composed with the rhs beta chain, as a reduction-star. The (a)-half of the guide's computation-fidelity pair.",
        )?;

        self.add_recursive_def(
            "def roseRecApp_whnfAcc_inert (u : Level) (hdef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) roseRecName) (OptionType.none KExpr)) (hrec : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) roseRecName) (OptionType.none RecMeta)) (C : KExpr) (m : KExpr) (t : KExpr) (hC : whnf_acc C) (hm : whnf_acc m) (ht : whnf_acc t) : whnf_acc (roseRecApp u C m t) := whnfAcc_inertSpine roseRecName hdef hrec (ListType.cons KExpr C (ListType.cons KExpr m (ListType.cons KExpr t (ListType.nil KExpr)))) (WhnfAccAll.cons C (ListType.cons KExpr m (ListType.cons KExpr t (ListType.nil KExpr))) hC (WhnfAccAll.cons m (ListType.cons KExpr t (ListType.nil KExpr)) hm (WhnfAccAll.cons t (ListType.nil KExpr) ht WhnfAccAll.nil))) (roseRecC u) (Eq.refl (OptionType Name) (OptionType.some Name roseRecName)) (whnfAcc_const roseRecName (ListType.cons Level u (ListType.nil Level)) hdef)",
            "roseRecApp_whnfAcc_inert: the rose recursor spine is strongly normalizing when its parts are, via the const-irreducibility gate -- roseRecName keys nothing in the_red_env, so the spine is inert there.",
        )?;

        self.add_recursive_def(
            "def roseRec_red_nodef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) roseRecName) (OptionType.none KExpr) := Eq.refl (OptionType KExpr) (OptionType.none KExpr)",
            "roseRec_red_nodef: roseRecName has no delta-definition in the fixed reduction env (rfl).",
        )?;

        self.add_recursive_def(
            "def roseRec_red_norecmeta : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) roseRecName) (OptionType.none RecMeta) := Eq.refl (OptionType RecMeta) (OptionType.none RecMeta)",
            "roseRec_red_norecmeta: roseRecName has no recursor metadata in the fixed reduction env (rfl). Together with roseRec_red_nodef this is why the rose spine is inert under the spec's env-pinned whnf_step -- the same structural fact the W lane recorded for wRecName.",
        )?;

        // ── RUNG 10: rose_recContract_steps, DERIVED (not ported) ──────────
        //
        // The guide leaves this `by sorry` (NestedRoseSN.lean:3579). There was
        // no proof term to port, so this is an ORIGINAL derivation built on the
        // natrec.rs substrate (iotaCong/natStep/natSteps/natRecContract_steps,
        // stage 79) generalized to the rose environment.
        //
        // Why it needed its own relation: the landed rose beta-chain used
        // `whnf_red_step_star`, which has NO app_right constructor
        // (whnf_progress.rs:4219). roseContractum puts the mapped IH pack in the
        // ARGUMENT position of the outer app, so the fused List.rec reduction
        // happens entirely under app_right — the existing relation cannot even
        // STATE the theorem. Hence roseIotaCong / roseStep / roseSteps, with the
        // app_right congruence the proof requires. The genIotaCong family
        // (schema.rs:658) could not be reused: it is pinned to `genREnv fam sig
        // u`, not an arbitrary RecEnv.
        //
        // The nesting is the real content: where Nat has ONE fixed-arity
        // recursive call, rose maps a fused List.rec over a list-indexed family,
        // so the single NatRecContract.rec arm becomes an induction over the
        // children list (roseListRec_nil_steps / _cons_steps / roseMap_steps).
        self.add_inductive(
            "inductive roseIotaCong (u : Level) : KExpr -> KExpr -> Type\n| head : forall (e : KExpr) (e2 : KExpr), iota_step (roseREnv u) e e2 -> roseIotaCong u e e2\n| app_left : forall (f : KExpr) (f2 : KExpr) (a : KExpr), roseIotaCong u f f2 -> roseIotaCong u (KExpr.app f a) (KExpr.app f2 a)\n| app_right : forall (f : KExpr) (a : KExpr) (a2 : KExpr), roseIotaCong u a a2 -> roseIotaCong u (KExpr.app f a) (KExpr.app f a2)",
            "roseIotaCong u: the one-hole congruence closure of iota_step at the ROSE recursor env — head/app_left/app_right. The app_right arm is the whole reason this relation exists: roseContractum puts the mapped IH pack in the ARGUMENT position, and the landed whnf_red_step_star (whnf_progress.rs) has no app_right, so it cannot state rose_recContract_steps. Clone of natrec.rs iotaCong at roseREnv. Rung 10.",
        )?;

        self.add_inductive(
            "inductive roseStep (u : Level) : KExpr -> KExpr -> Type\n| iota : forall (e : KExpr) (e2 : KExpr), roseIotaCong u e e2 -> roseStep u e e2\n| beta : forall (e : KExpr) (e2 : KExpr), beta_reduces e e2 -> roseStep u e e2",
            "roseStep u: roseIotaCong union beta_reduces — the rose analogue of natStep. Rung 10.",
        )?;

        self.add_inductive(
            "inductive roseSteps (u : Level) : KExpr -> KExpr -> Type\n| refl : forall (e : KExpr), roseSteps u e e\n| step : forall (e : KExpr) (e2 : KExpr) (e3 : KExpr), roseStep u e e2 -> roseSteps u e2 e3 -> roseSteps u e e3",
            "roseSteps u: reflexive-transitive closure of roseStep — the spec's stand-in for the guide's WhnfStar at the rose env. Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseSteps_trans (u : Level) (a : KExpr) (b : KExpr) (c : KExpr) (h1 : roseSteps u a b) (h2 : roseSteps u b c) : roseSteps u a c := roseSteps.rec u (fun (a0 : KExpr) (b0 : KExpr) (_ : roseSteps u a0 b0) => roseSteps u b0 c -> roseSteps u a0 c) (fun (e : KExpr) => fun (hc : roseSteps u e c) => hc) (fun (e : KExpr) (e2 : KExpr) (e3 : KExpr) (st : roseStep u e e2) (_rest : roseSteps u e2 e3) (ih : roseSteps u e3 c -> roseSteps u e2 c) => fun (hc : roseSteps u e3 c) => roseSteps.step u e e2 c st (ih hc)) a b h1 h2",
            "roseSteps_trans: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseStep_app_right (u : Level) (f : KExpr) (e : KExpr) (e2 : KExpr) (h : roseStep u e e2) : roseStep u (KExpr.app f e) (KExpr.app f e2) := match h with | roseStep.iota ic => roseStep.iota u (KExpr.app f e) (KExpr.app f e2) (roseIotaCong.app_right u f e e2 ic) | roseStep.beta br => roseStep.beta u (KExpr.app f e) (KExpr.app f e2) (beta_reduces.app_right f e e2 br)",
            "roseStep_app_right: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseSteps_app_right (u : Level) (f : KExpr) (a : KExpr) (b : KExpr) (h : roseSteps u a b) : roseSteps u (KExpr.app f a) (KExpr.app f b) := roseSteps.rec u (fun (a0 : KExpr) (b0 : KExpr) (_ : roseSteps u a0 b0) => roseSteps u (KExpr.app f a0) (KExpr.app f b0)) (fun (e : KExpr) => roseSteps.refl u (KExpr.app f e)) (fun (e : KExpr) (e2 : KExpr) (e3 : KExpr) (st : roseStep u e e2) (_rest : roseSteps u e2 e3) (ih : roseSteps u (KExpr.app f e2) (KExpr.app f e3)) => roseSteps.step u (KExpr.app f e) (KExpr.app f e2) (KExpr.app f e3) (roseStep_app_right u f e e2 st) ih) a b h",
            "roseSteps_app_right: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseListNilLam2 : KExpr := KExpr.lam roseListTyC (KExpr.bvar (Nat.succ Nat.zero))",
            "roseListNilLam2: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseListNilLam1 : KExpr := KExpr.lam roseListTyC roseListNilLam2",
            "roseListNilLam1: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseListRecRhsNil_shape : Eq KExpr roseListRecRhsNil (KExpr.lam (genMotiveTy roseListName Level.zero) roseListNilLam1) := Eq.refl KExpr roseListRecRhsNil",
            "roseListRecRhsNil_shape: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseListConsBody (u : Level) : KExpr := KExpr.app (KExpr.app (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero))",
            "roseListConsBody: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseListConsLam4 (u : Level) : KExpr := KExpr.lam roseListTyC (roseListConsBody u)",
            "roseListConsLam4: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseListConsLam3 (u : Level) : KExpr := KExpr.lam roseTyC (roseListConsLam4 u)",
            "roseListConsLam3: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseListConsLam2 (u : Level) : KExpr := KExpr.lam roseListTyC (roseListConsLam3 u)",
            "roseListConsLam2: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseListConsLam1 (u : Level) : KExpr := KExpr.lam roseListTyC (roseListConsLam2 u)",
            "roseListConsLam1: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseListRecRhsCons_shape (u : Level) : Eq KExpr (roseListRecRhsCons u) (KExpr.lam (genMotiveTy roseListName Level.zero) (roseListConsLam1 u)) := Eq.refl KExpr (roseListRecRhsCons u)",
            "roseListRecRhsCons_shape: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseList_iota_nil (u : Level) (Mo : KExpr) (Ni : KExpr) (Cc : KExpr) : iota_step (roseREnv u) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) Ni) Cc) listNilC) (KExpr.app (KExpr.app (KExpr.app roseListRecRhsNil Mo) Ni) Cc) := Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.app (KExpr.app (KExpr.app roseListRecRhsNil Mo) Ni) Cc))",
            "roseList_iota_nil: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseList_iota_cons (u : Level) (Mo : KExpr) (Ni : KExpr) (Cc : KExpr) (x : KExpr) (tl : KExpr) : iota_step (roseREnv u) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) Ni) Cc) (KExpr.app (KExpr.app listConsC x) tl)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (roseListRecRhsCons u) Mo) Ni) Cc) x) tl) := Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (roseListRecRhsCons u) Mo) Ni) Cc) x) tl))",
            "roseList_iota_cons: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseListRec_nil_steps (u : Level) (Mo : KExpr) (Ni : KExpr) (Cc : KExpr) : roseSteps u (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) Ni) Cc) listNilC) Ni := roseSteps.step u (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) Ni) Cc) listNilC) (KExpr.app (KExpr.app (KExpr.app roseListRecRhsNil Mo) Ni) Cc) Ni (roseStep.iota u (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) Ni) Cc) listNilC) (KExpr.app (KExpr.app (KExpr.app roseListRecRhsNil Mo) Ni) Cc) (roseIotaCong.head u (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) Ni) Cc) listNilC) (KExpr.app (KExpr.app (KExpr.app roseListRecRhsNil Mo) Ni) Cc) (roseList_iota_nil u Mo Ni Cc))) (roseSteps.step u (KExpr.app (KExpr.app (KExpr.app roseListRecRhsNil Mo) Ni) Cc) (KExpr.app (KExpr.app (psubst (scons Mo idsubst) roseListNilLam1) Ni) Cc) Ni (roseStep.beta u (KExpr.app (KExpr.app (KExpr.app roseListRecRhsNil Mo) Ni) Cc) (KExpr.app (KExpr.app (psubst (scons Mo idsubst) roseListNilLam1) Ni) Cc) (beta_reduces.app_left (KExpr.app (KExpr.app roseListRecRhsNil Mo) Ni) (KExpr.app (psubst (scons Mo idsubst) roseListNilLam1) Ni) Cc (beta_reduces.app_left (KExpr.app roseListRecRhsNil Mo) (psubst (scons Mo idsubst) roseListNilLam1) Ni (betaReduces_psubst (genMotiveTy roseListName Level.zero) roseListNilLam1 Mo)))) (roseSteps.step u (KExpr.app (KExpr.app (psubst (scons Mo idsubst) roseListNilLam1) Ni) Cc) (KExpr.app (psubst (scons Ni (scons Mo idsubst)) roseListNilLam2) Cc) Ni (roseStep.beta u (KExpr.app (KExpr.app (psubst (scons Mo idsubst) roseListNilLam1) Ni) Cc) (KExpr.app (psubst (scons Ni (scons Mo idsubst)) roseListNilLam2) Cc) (beta_reduces.app_left (KExpr.app (psubst (scons Mo idsubst) roseListNilLam1) Ni) (psubst (scons Ni (scons Mo idsubst)) roseListNilLam2) Cc (Eq.substType KExpr (fun (w : KExpr) => beta_reduces (KExpr.app (psubst (scons Mo idsubst) roseListNilLam1) Ni) w) (psubst (scons Ni idsubst) (psubst (up (scons Mo idsubst)) roseListNilLam2)) (psubst (scons Ni (scons Mo idsubst)) roseListNilLam2) (psubst_scons_up Ni roseListNilLam2 (scons Mo idsubst)) (betaReduces_psubst (psubst (scons Mo idsubst) roseListTyC) (psubst (up (scons Mo idsubst)) roseListNilLam2) Ni)))) (roseSteps.step u (KExpr.app (psubst (scons Ni (scons Mo idsubst)) roseListNilLam2) Cc) (psubst (scons Cc (scons Ni (scons Mo idsubst))) (KExpr.bvar (Nat.succ Nat.zero))) Ni (roseStep.beta u (KExpr.app (psubst (scons Ni (scons Mo idsubst)) roseListNilLam2) Cc) (psubst (scons Cc (scons Ni (scons Mo idsubst))) (KExpr.bvar (Nat.succ Nat.zero))) (Eq.substType KExpr (fun (w : KExpr) => beta_reduces (KExpr.app (psubst (scons Ni (scons Mo idsubst)) roseListNilLam2) Cc) w) (psubst (scons Cc idsubst) (psubst (up (scons Ni (scons Mo idsubst))) (KExpr.bvar (Nat.succ Nat.zero)))) (psubst (scons Cc (scons Ni (scons Mo idsubst))) (KExpr.bvar (Nat.succ Nat.zero))) (psubst_scons_up Cc (KExpr.bvar (Nat.succ Nat.zero)) (scons Ni (scons Mo idsubst))) (betaReduces_psubst (psubst (scons Ni (scons Mo idsubst)) roseListTyC) (psubst (up (scons Ni (scons Mo idsubst))) (KExpr.bvar (Nat.succ Nat.zero))) Cc))) (roseSteps.refl u Ni))))",
            "roseListRec_nil_steps: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseListRec_cons_steps (u : Level) (Mo : KExpr) (Ni : KExpr) (Cc : KExpr) (x : KExpr) (tl : KExpr) : roseSteps u (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) Ni) Cc) (KExpr.app (KExpr.app listConsC x) tl)) (KExpr.app (KExpr.app (KExpr.app Cc x) tl) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) Ni) Cc) tl)) := roseSteps.step u (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) Ni) Cc) (KExpr.app (KExpr.app listConsC x) tl)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (roseListRecRhsCons u) Mo) Ni) Cc) x) tl) (KExpr.app (KExpr.app (KExpr.app Cc x) tl) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) Ni) Cc) tl)) (roseStep.iota u (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) Ni) Cc) (KExpr.app (KExpr.app listConsC x) tl)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (roseListRecRhsCons u) Mo) Ni) Cc) x) tl) (roseIotaCong.head u (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) Ni) Cc) (KExpr.app (KExpr.app listConsC x) tl)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (roseListRecRhsCons u) Mo) Ni) Cc) x) tl) (roseList_iota_cons u Mo Ni Cc x tl))) (roseSteps.step u (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (roseListRecRhsCons u) Mo) Ni) Cc) x) tl) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (psubst (scons Mo idsubst) (roseListConsLam1 u)) Ni) Cc) x) tl) (KExpr.app (KExpr.app (KExpr.app Cc x) tl) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) Ni) Cc) tl)) (roseStep.beta u (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (roseListRecRhsCons u) Mo) Ni) Cc) x) tl) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (psubst (scons Mo idsubst) (roseListConsLam1 u)) Ni) Cc) x) tl) (beta_reduces.app_left (KExpr.app (KExpr.app (KExpr.app (KExpr.app (roseListRecRhsCons u) Mo) Ni) Cc) x) (KExpr.app (KExpr.app (KExpr.app (psubst (scons Mo idsubst) (roseListConsLam1 u)) Ni) Cc) x) tl (beta_reduces.app_left (KExpr.app (KExpr.app (KExpr.app (roseListRecRhsCons u) Mo) Ni) Cc) (KExpr.app (KExpr.app (psubst (scons Mo idsubst) (roseListConsLam1 u)) Ni) Cc) x (beta_reduces.app_left (KExpr.app (KExpr.app (roseListRecRhsCons u) Mo) Ni) (KExpr.app (psubst (scons Mo idsubst) (roseListConsLam1 u)) Ni) Cc (beta_reduces.app_left (KExpr.app (roseListRecRhsCons u) Mo) (psubst (scons Mo idsubst) (roseListConsLam1 u)) Ni (betaReduces_psubst (genMotiveTy roseListName Level.zero) (roseListConsLam1 u) Mo)))))) (roseSteps.step u (KExpr.app (KExpr.app (KExpr.app (KExpr.app (psubst (scons Mo idsubst) (roseListConsLam1 u)) Ni) Cc) x) tl) (KExpr.app (KExpr.app (KExpr.app (psubst (scons Ni (scons Mo idsubst)) (roseListConsLam2 u)) Cc) x) tl) (KExpr.app (KExpr.app (KExpr.app Cc x) tl) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) Ni) Cc) tl)) (roseStep.beta u (KExpr.app (KExpr.app (KExpr.app (KExpr.app (psubst (scons Mo idsubst) (roseListConsLam1 u)) Ni) Cc) x) tl) (KExpr.app (KExpr.app (KExpr.app (psubst (scons Ni (scons Mo idsubst)) (roseListConsLam2 u)) Cc) x) tl) (beta_reduces.app_left (KExpr.app (KExpr.app (KExpr.app (psubst (scons Mo idsubst) (roseListConsLam1 u)) Ni) Cc) x) (KExpr.app (KExpr.app (psubst (scons Ni (scons Mo idsubst)) (roseListConsLam2 u)) Cc) x) tl (beta_reduces.app_left (KExpr.app (KExpr.app (psubst (scons Mo idsubst) (roseListConsLam1 u)) Ni) Cc) (KExpr.app (psubst (scons Ni (scons Mo idsubst)) (roseListConsLam2 u)) Cc) x (beta_reduces.app_left (KExpr.app (psubst (scons Mo idsubst) (roseListConsLam1 u)) Ni) (psubst (scons Ni (scons Mo idsubst)) (roseListConsLam2 u)) Cc (Eq.substType KExpr (fun (w : KExpr) => beta_reduces (KExpr.app (psubst (scons Mo idsubst) (roseListConsLam1 u)) Ni) w) (psubst (scons Ni idsubst) (psubst (up (scons Mo idsubst)) (roseListConsLam2 u))) (psubst (scons Ni (scons Mo idsubst)) (roseListConsLam2 u)) (psubst_scons_up Ni (roseListConsLam2 u) (scons Mo idsubst)) (betaReduces_psubst (psubst (scons Mo idsubst) roseListTyC) (psubst (up (scons Mo idsubst)) (roseListConsLam2 u)) Ni)))))) (roseSteps.step u (KExpr.app (KExpr.app (KExpr.app (psubst (scons Ni (scons Mo idsubst)) (roseListConsLam2 u)) Cc) x) tl) (KExpr.app (KExpr.app (psubst (scons Cc (scons Ni (scons Mo idsubst))) (roseListConsLam3 u)) x) tl) (KExpr.app (KExpr.app (KExpr.app Cc x) tl) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) Ni) Cc) tl)) (roseStep.beta u (KExpr.app (KExpr.app (KExpr.app (psubst (scons Ni (scons Mo idsubst)) (roseListConsLam2 u)) Cc) x) tl) (KExpr.app (KExpr.app (psubst (scons Cc (scons Ni (scons Mo idsubst))) (roseListConsLam3 u)) x) tl) (beta_reduces.app_left (KExpr.app (KExpr.app (psubst (scons Ni (scons Mo idsubst)) (roseListConsLam2 u)) Cc) x) (KExpr.app (psubst (scons Cc (scons Ni (scons Mo idsubst))) (roseListConsLam3 u)) x) tl (beta_reduces.app_left (KExpr.app (psubst (scons Ni (scons Mo idsubst)) (roseListConsLam2 u)) Cc) (psubst (scons Cc (scons Ni (scons Mo idsubst))) (roseListConsLam3 u)) x (Eq.substType KExpr (fun (w : KExpr) => beta_reduces (KExpr.app (psubst (scons Ni (scons Mo idsubst)) (roseListConsLam2 u)) Cc) w) (psubst (scons Cc idsubst) (psubst (up (scons Ni (scons Mo idsubst))) (roseListConsLam3 u))) (psubst (scons Cc (scons Ni (scons Mo idsubst))) (roseListConsLam3 u)) (psubst_scons_up Cc (roseListConsLam3 u) (scons Ni (scons Mo idsubst))) (betaReduces_psubst (psubst (scons Ni (scons Mo idsubst)) roseListTyC) (psubst (up (scons Ni (scons Mo idsubst))) (roseListConsLam3 u)) Cc))))) (roseSteps.step u (KExpr.app (KExpr.app (psubst (scons Cc (scons Ni (scons Mo idsubst))) (roseListConsLam3 u)) x) tl) (KExpr.app (psubst (scons x (scons Cc (scons Ni (scons Mo idsubst)))) (roseListConsLam4 u)) tl) (KExpr.app (KExpr.app (KExpr.app Cc x) tl) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) Ni) Cc) tl)) (roseStep.beta u (KExpr.app (KExpr.app (psubst (scons Cc (scons Ni (scons Mo idsubst))) (roseListConsLam3 u)) x) tl) (KExpr.app (psubst (scons x (scons Cc (scons Ni (scons Mo idsubst)))) (roseListConsLam4 u)) tl) (beta_reduces.app_left (KExpr.app (psubst (scons Cc (scons Ni (scons Mo idsubst))) (roseListConsLam3 u)) x) (psubst (scons x (scons Cc (scons Ni (scons Mo idsubst)))) (roseListConsLam4 u)) tl (Eq.substType KExpr (fun (w : KExpr) => beta_reduces (KExpr.app (psubst (scons Cc (scons Ni (scons Mo idsubst))) (roseListConsLam3 u)) x) w) (psubst (scons x idsubst) (psubst (up (scons Cc (scons Ni (scons Mo idsubst)))) (roseListConsLam4 u))) (psubst (scons x (scons Cc (scons Ni (scons Mo idsubst)))) (roseListConsLam4 u)) (psubst_scons_up x (roseListConsLam4 u) (scons Cc (scons Ni (scons Mo idsubst)))) (betaReduces_psubst (psubst (scons Cc (scons Ni (scons Mo idsubst))) roseTyC) (psubst (up (scons Cc (scons Ni (scons Mo idsubst)))) (roseListConsLam4 u)) x)))) (roseSteps.step u (KExpr.app (psubst (scons x (scons Cc (scons Ni (scons Mo idsubst)))) (roseListConsLam4 u)) tl) (psubst (scons tl (scons x (scons Cc (scons Ni (scons Mo idsubst))))) (roseListConsBody u)) (KExpr.app (KExpr.app (KExpr.app Cc x) tl) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) Ni) Cc) tl)) (roseStep.beta u (KExpr.app (psubst (scons x (scons Cc (scons Ni (scons Mo idsubst)))) (roseListConsLam4 u)) tl) (psubst (scons tl (scons x (scons Cc (scons Ni (scons Mo idsubst))))) (roseListConsBody u)) (Eq.substType KExpr (fun (w : KExpr) => beta_reduces (KExpr.app (psubst (scons x (scons Cc (scons Ni (scons Mo idsubst)))) (roseListConsLam4 u)) tl) w) (psubst (scons tl idsubst) (psubst (up (scons x (scons Cc (scons Ni (scons Mo idsubst))))) (roseListConsBody u))) (psubst (scons tl (scons x (scons Cc (scons Ni (scons Mo idsubst))))) (roseListConsBody u)) (psubst_scons_up tl (roseListConsBody u) (scons x (scons Cc (scons Ni (scons Mo idsubst))))) (betaReduces_psubst (psubst (scons x (scons Cc (scons Ni (scons Mo idsubst)))) roseListTyC) (psubst (up (scons x (scons Cc (scons Ni (scons Mo idsubst))))) (roseListConsBody u)) tl))) (roseSteps.refl u (KExpr.app (KExpr.app (KExpr.app Cc x) tl) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) Ni) Cc) tl))))))))",
            "roseListRec_cons_steps: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseMap_steps (u : Level) (Mo : KExpr) (Cc : KExpr) (f : KExpr -> KExpr) (hcons : forall (x : KExpr) (tl : KExpr) (ih : KExpr), roseSteps u (KExpr.app (KExpr.app (KExpr.app Cc x) tl) ih) (KExpr.app (KExpr.app listConsC (f x)) ih)) (children : ListType KExpr) : roseSteps u (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) listNilC) Cc) (roseList children)) (roseList (mapLT f children)) := ListType.rec KExpr (fun (l : ListType KExpr) => roseSteps u (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) listNilC) Cc) (roseList l)) (roseList (mapLT f l))) (roseListRec_nil_steps u Mo listNilC Cc) (fun (x : KExpr) (rest : ListType KExpr) (ih : roseSteps u (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) listNilC) Cc) (roseList rest)) (roseList (mapLT f rest))) => roseSteps_trans u (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) listNilC) Cc) (KExpr.app (KExpr.app listConsC x) (roseList rest))) (KExpr.app (KExpr.app (KExpr.app Cc x) (roseList rest)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) listNilC) Cc) (roseList rest))) (KExpr.app (KExpr.app listConsC (f x)) (roseList (mapLT f rest))) (roseListRec_cons_steps u Mo listNilC Cc x (roseList rest)) (roseSteps_trans u (KExpr.app (KExpr.app (KExpr.app Cc x) (roseList rest)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) listNilC) Cc) (roseList rest))) (KExpr.app (KExpr.app listConsC (f x)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) listNilC) Cc) (roseList rest))) (KExpr.app (KExpr.app listConsC (f x)) (roseList (mapLT f rest))) (hcons x (roseList rest) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) listNilC) Cc) (roseList rest))) (roseSteps_app_right u (KExpr.app listConsC (f x)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) Mo) listNilC) Cc) (roseList rest)) (roseList (mapLT f rest)) ih))) children",
            "roseMap_steps: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseRhsLam2 (u : Level) : KExpr := KExpr.lam roseListTyC (roseRecRhsBody u)",
            "roseRhsLam2: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseRhsLam1 (u : Level) : KExpr := KExpr.lam (roseNodeMinorTy u) (roseRhsLam2 u)",
            "roseRhsLam1: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseRecRhs_shape (u : Level) : Eq KExpr (roseRecRhs u) (KExpr.lam (genMotiveTy roseName u) (roseRhsLam1 u)) := Eq.refl KExpr (roseRecRhs u)",
            "roseRecRhs_shape: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseRecRhs_betaSteps (u : Level) (C : KExpr) (m : KExpr) (cs : KExpr) : roseSteps u (KExpr.app (KExpr.app (KExpr.app (roseRecRhs u) C) m) cs) (KExpr.app (KExpr.app m cs) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) roseMapMotive) listNilC) (psubst (scons cs (scons m (scons C idsubst))) (roseConsCase u))) cs)) := roseSteps.step u (KExpr.app (KExpr.app (KExpr.app (roseRecRhs u) C) m) cs) (KExpr.app (KExpr.app (psubst (scons C idsubst) (roseRhsLam1 u)) m) cs) (KExpr.app (KExpr.app m cs) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) roseMapMotive) listNilC) (psubst (scons cs (scons m (scons C idsubst))) (roseConsCase u))) cs)) (roseStep.beta u (KExpr.app (KExpr.app (KExpr.app (roseRecRhs u) C) m) cs) (KExpr.app (KExpr.app (psubst (scons C idsubst) (roseRhsLam1 u)) m) cs) (beta_reduces.app_left (KExpr.app (KExpr.app (roseRecRhs u) C) m) (KExpr.app (psubst (scons C idsubst) (roseRhsLam1 u)) m) cs (beta_reduces.app_left (KExpr.app (roseRecRhs u) C) (psubst (scons C idsubst) (roseRhsLam1 u)) m (betaReduces_psubst (genMotiveTy roseName u) (roseRhsLam1 u) C)))) (roseSteps.step u (KExpr.app (KExpr.app (psubst (scons C idsubst) (roseRhsLam1 u)) m) cs) (KExpr.app (psubst (scons m (scons C idsubst)) (roseRhsLam2 u)) cs) (KExpr.app (KExpr.app m cs) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) roseMapMotive) listNilC) (psubst (scons cs (scons m (scons C idsubst))) (roseConsCase u))) cs)) (roseStep.beta u (KExpr.app (KExpr.app (psubst (scons C idsubst) (roseRhsLam1 u)) m) cs) (KExpr.app (psubst (scons m (scons C idsubst)) (roseRhsLam2 u)) cs) (beta_reduces.app_left (KExpr.app (psubst (scons C idsubst) (roseRhsLam1 u)) m) (psubst (scons m (scons C idsubst)) (roseRhsLam2 u)) cs (Eq.substType KExpr (fun (w : KExpr) => beta_reduces (KExpr.app (psubst (scons C idsubst) (roseRhsLam1 u)) m) w) (psubst (scons m idsubst) (psubst (up (scons C idsubst)) (roseRhsLam2 u))) (psubst (scons m (scons C idsubst)) (roseRhsLam2 u)) (psubst_scons_up m (roseRhsLam2 u) (scons C idsubst)) (betaReduces_psubst (psubst (scons C idsubst) (roseNodeMinorTy u)) (psubst (up (scons C idsubst)) (roseRhsLam2 u)) m)))) (roseSteps.step u (KExpr.app (psubst (scons m (scons C idsubst)) (roseRhsLam2 u)) cs) (psubst (scons cs (scons m (scons C idsubst))) (roseRecRhsBody u)) (KExpr.app (KExpr.app m cs) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) roseMapMotive) listNilC) (psubst (scons cs (scons m (scons C idsubst))) (roseConsCase u))) cs)) (roseStep.beta u (KExpr.app (psubst (scons m (scons C idsubst)) (roseRhsLam2 u)) cs) (psubst (scons cs (scons m (scons C idsubst))) (roseRecRhsBody u)) (Eq.substType KExpr (fun (w : KExpr) => beta_reduces (KExpr.app (psubst (scons m (scons C idsubst)) (roseRhsLam2 u)) cs) w) (psubst (scons cs idsubst) (psubst (up (scons m (scons C idsubst))) (roseRecRhsBody u))) (psubst (scons cs (scons m (scons C idsubst))) (roseRecRhsBody u)) (psubst_scons_up cs (roseRecRhsBody u) (scons m (scons C idsubst))) (betaReduces_psubst (psubst (scons m (scons C idsubst)) roseListTyC) (psubst (up (scons m (scons C idsubst))) (roseRecRhsBody u)) cs))) (roseSteps.refl u (KExpr.app (KExpr.app m cs) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) roseMapMotive) listNilC) (psubst (scons cs (scons m (scons C idsubst))) (roseConsCase u))) cs)))))",
            "roseRecRhs_betaSteps: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseConsCaseBody (u : Level) : KExpr := KExpr.app (KExpr.app listConsC (roseRecApp u (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar Nat.zero)",
            "roseConsCaseBody: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseConsCaseLam2 (u : Level) : KExpr := KExpr.lam roseListTyC (roseConsCaseBody u)",
            "roseConsCaseLam2: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseConsCaseLam1 (u : Level) : KExpr := KExpr.lam roseListTyC (roseConsCaseLam2 u)",
            "roseConsCaseLam1: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseConsCase_shape (u : Level) : Eq KExpr (roseConsCase u) (KExpr.lam roseTyC (roseConsCaseLam1 u)) := Eq.refl KExpr (roseConsCase u)",
            "roseConsCase_shape: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseConsCase_betaSteps (u : Level) (C : KExpr) (m : KExpr) (cs : KExpr) (x : KExpr) (tl : KExpr) (ihv : KExpr) : roseSteps u (KExpr.app (KExpr.app (KExpr.app (psubst (scons cs (scons m (scons C idsubst))) (roseConsCase u)) x) tl) ihv) (KExpr.app (KExpr.app listConsC (roseRecApp u C m x)) ihv) := roseSteps.step u (KExpr.app (KExpr.app (KExpr.app (psubst (scons cs (scons m (scons C idsubst))) (roseConsCase u)) x) tl) ihv) (KExpr.app (KExpr.app (psubst (scons x (scons cs (scons m (scons C idsubst)))) (roseConsCaseLam1 u)) tl) ihv) (KExpr.app (KExpr.app listConsC (roseRecApp u C m x)) ihv) (roseStep.beta u (KExpr.app (KExpr.app (KExpr.app (psubst (scons cs (scons m (scons C idsubst))) (roseConsCase u)) x) tl) ihv) (KExpr.app (KExpr.app (psubst (scons x (scons cs (scons m (scons C idsubst)))) (roseConsCaseLam1 u)) tl) ihv) (beta_reduces.app_left (KExpr.app (KExpr.app (psubst (scons cs (scons m (scons C idsubst))) (roseConsCase u)) x) tl) (KExpr.app (psubst (scons x (scons cs (scons m (scons C idsubst)))) (roseConsCaseLam1 u)) tl) ihv (beta_reduces.app_left (KExpr.app (psubst (scons cs (scons m (scons C idsubst))) (roseConsCase u)) x) (psubst (scons x (scons cs (scons m (scons C idsubst)))) (roseConsCaseLam1 u)) tl (Eq.substType KExpr (fun (w : KExpr) => beta_reduces (KExpr.app (psubst (scons cs (scons m (scons C idsubst))) (roseConsCase u)) x) w) (psubst (scons x idsubst) (psubst (up (scons cs (scons m (scons C idsubst)))) (roseConsCaseLam1 u))) (psubst (scons x (scons cs (scons m (scons C idsubst)))) (roseConsCaseLam1 u)) (psubst_scons_up x (roseConsCaseLam1 u) (scons cs (scons m (scons C idsubst)))) (betaReduces_psubst (psubst (scons cs (scons m (scons C idsubst))) roseTyC) (psubst (up (scons cs (scons m (scons C idsubst)))) (roseConsCaseLam1 u)) x))))) (roseSteps.step u (KExpr.app (KExpr.app (psubst (scons x (scons cs (scons m (scons C idsubst)))) (roseConsCaseLam1 u)) tl) ihv) (KExpr.app (psubst (scons tl (scons x (scons cs (scons m (scons C idsubst))))) (roseConsCaseLam2 u)) ihv) (KExpr.app (KExpr.app listConsC (roseRecApp u C m x)) ihv) (roseStep.beta u (KExpr.app (KExpr.app (psubst (scons x (scons cs (scons m (scons C idsubst)))) (roseConsCaseLam1 u)) tl) ihv) (KExpr.app (psubst (scons tl (scons x (scons cs (scons m (scons C idsubst))))) (roseConsCaseLam2 u)) ihv) (beta_reduces.app_left (KExpr.app (psubst (scons x (scons cs (scons m (scons C idsubst)))) (roseConsCaseLam1 u)) tl) (psubst (scons tl (scons x (scons cs (scons m (scons C idsubst))))) (roseConsCaseLam2 u)) ihv (Eq.substType KExpr (fun (w : KExpr) => beta_reduces (KExpr.app (psubst (scons x (scons cs (scons m (scons C idsubst)))) (roseConsCaseLam1 u)) tl) w) (psubst (scons tl idsubst) (psubst (up (scons x (scons cs (scons m (scons C idsubst))))) (roseConsCaseLam2 u))) (psubst (scons tl (scons x (scons cs (scons m (scons C idsubst))))) (roseConsCaseLam2 u)) (psubst_scons_up tl (roseConsCaseLam2 u) (scons x (scons cs (scons m (scons C idsubst))))) (betaReduces_psubst (psubst (scons x (scons cs (scons m (scons C idsubst)))) roseListTyC) (psubst (up (scons x (scons cs (scons m (scons C idsubst))))) (roseConsCaseLam2 u)) tl)))) (roseSteps.step u (KExpr.app (psubst (scons tl (scons x (scons cs (scons m (scons C idsubst))))) (roseConsCaseLam2 u)) ihv) (psubst (scons ihv (scons tl (scons x (scons cs (scons m (scons C idsubst)))))) (roseConsCaseBody u)) (KExpr.app (KExpr.app listConsC (roseRecApp u C m x)) ihv) (roseStep.beta u (KExpr.app (psubst (scons tl (scons x (scons cs (scons m (scons C idsubst))))) (roseConsCaseLam2 u)) ihv) (psubst (scons ihv (scons tl (scons x (scons cs (scons m (scons C idsubst)))))) (roseConsCaseBody u)) (Eq.substType KExpr (fun (w : KExpr) => beta_reduces (KExpr.app (psubst (scons tl (scons x (scons cs (scons m (scons C idsubst))))) (roseConsCaseLam2 u)) ihv) w) (psubst (scons ihv idsubst) (psubst (up (scons tl (scons x (scons cs (scons m (scons C idsubst)))))) (roseConsCaseBody u))) (psubst (scons ihv (scons tl (scons x (scons cs (scons m (scons C idsubst)))))) (roseConsCaseBody u)) (psubst_scons_up ihv (roseConsCaseBody u) (scons tl (scons x (scons cs (scons m (scons C idsubst)))))) (betaReduces_psubst (psubst (scons tl (scons x (scons cs (scons m (scons C idsubst))))) roseListTyC) (psubst (up (scons tl (scons x (scons cs (scons m (scons C idsubst)))))) (roseConsCaseBody u)) ihv))) (roseSteps.refl u (KExpr.app (KExpr.app listConsC (roseRecApp u C m x)) ihv))))",
            "roseConsCase_betaSteps: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def rose_node_steps (u : Level) (C : KExpr) (m : KExpr) (children : ListType KExpr) : roseSteps u (roseRecApp u C m (roseNode (roseList children))) (roseContractum u C m children) := roseSteps.step u (roseRecApp u C m (roseNode (roseList children))) (KExpr.app (KExpr.app (KExpr.app (roseRecRhs u) C) m) (roseList children)) (roseContractum u C m children) (roseStep.iota u (roseRecApp u C m (roseNode (roseList children))) (KExpr.app (KExpr.app (KExpr.app (roseRecRhs u) C) m) (roseList children)) (roseIotaCong.head u (roseRecApp u C m (roseNode (roseList children))) (KExpr.app (KExpr.app (KExpr.app (roseRecRhs u) C) m) (roseList children)) (rose_iota_fires_gen u C m (roseList children)))) (roseSteps_trans u (KExpr.app (KExpr.app (KExpr.app (roseRecRhs u) C) m) (roseList children)) (KExpr.app (KExpr.app m (roseList children)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) roseMapMotive) listNilC) (psubst (scons (roseList children) (scons m (scons C idsubst))) (roseConsCase u))) (roseList children))) (roseContractum u C m children) (roseRecRhs_betaSteps u C m (roseList children)) (roseSteps_app_right u (KExpr.app m (roseList children)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (listRecC u) roseMapMotive) listNilC) (psubst (scons (roseList children) (scons m (scons C idsubst))) (roseConsCase u))) (roseList children)) (roseList (mapLT (fun (x : KExpr) => roseRecApp u C m x) children)) (roseMap_steps u roseMapMotive (psubst (scons (roseList children) (scons m (scons C idsubst))) (roseConsCase u)) (fun (x : KExpr) => roseRecApp u C m x) (fun (x : KExpr) (tl : KExpr) (ihv : KExpr) => roseConsCase_betaSteps u C m (roseList children) x tl ihv) children)))",
            "rose_node_steps: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def rose_recContract_steps (u : Level) (e : KExpr) (e2 : KExpr) (h : RoseRecContract u e e2) : roseSteps u e e2 := RoseRecContract.rec u (fun (e0 : KExpr) (e0b : KExpr) (_ : RoseRecContract u e0 e0b) => roseSteps u e0 e0b) (fun (C : KExpr) (m : KExpr) (children : ListType KExpr) => rose_node_steps u C m children) e e2 h",
            "rose_recContract_steps: rose_recContract_steps chain (DERIVED, guide leaves it sorry). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseNode_red_nodef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) nodeName) (OptionType.none KExpr) := Eq.refl (OptionType KExpr) (OptionType.none KExpr)",
            "roseNode_red_nodef: rose SN-open support (lane did NOT close; see header). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseNode_red_norecmeta : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) nodeName) (OptionType.none RecMeta) := Eq.refl (OptionType RecMeta) (OptionType.none RecMeta)",
            "roseNode_red_norecmeta: rose SN-open support (lane did NOT close; see header). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseListNil_red_nodef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) listNilName) (OptionType.none KExpr) := Eq.refl (OptionType KExpr) (OptionType.none KExpr)",
            "roseListNil_red_nodef: rose SN-open support (lane did NOT close; see header). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseListCons_red_nodef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) listConsName) (OptionType.none KExpr) := Eq.refl (OptionType KExpr) (OptionType.none KExpr)",
            "roseListCons_red_nodef: rose SN-open support (lane did NOT close; see header). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseListCons_red_norecmeta : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) listConsName) (OptionType.none RecMeta) := Eq.refl (OptionType RecMeta) (OptionType.none RecMeta)",
            "roseListCons_red_norecmeta: rose SN-open support (lane did NOT close; see header). Rung 10.",
        )?;

        self.add_recursive_def(
            "def whnfAcc_listNilC : whnf_acc listNilC := whnfAcc_const listNilName (ListType.nil Level) roseListNil_red_nodef",
            "whnfAcc_listNilC: rose SN-open support (lane did NOT close; see header). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseList_whnfAcc (children : ListType KExpr) (h : WhnfAccAll children) : whnf_acc (roseList children) := WhnfAccAll.rec (fun (l : ListType KExpr) (_hl : WhnfAccAll l) => whnf_acc (roseList l)) whnfAcc_listNilC (fun (x : KExpr) (rest : ListType KExpr) (hx : whnf_acc x) (_hrest : WhnfAccAll rest) (ih : whnf_acc (roseList rest)) => whnfAcc_inertSpine listConsName roseListCons_red_nodef roseListCons_red_norecmeta (ListType.cons KExpr x (ListType.cons KExpr (roseList rest) (ListType.nil KExpr))) (WhnfAccAll.cons x (ListType.cons KExpr (roseList rest) (ListType.nil KExpr)) hx (WhnfAccAll.cons (roseList rest) (ListType.nil KExpr) ih WhnfAccAll.nil)) listConsC (Eq.refl (OptionType Name) (OptionType.some Name listConsName)) (whnfAcc_const listConsName (ListType.nil Level) roseListCons_red_nodef)) children h",
            "roseList_whnfAcc: rose SN-open support (lane did NOT close; see header). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseNode_whnfAcc (cs : KExpr) (hcs : whnf_acc cs) : whnf_acc (roseNode cs) := whnfAcc_inertApp nodeName roseNode_red_nodef roseNode_red_norecmeta nodeC (whnfAcc_const nodeName (ListType.nil Level) roseNode_red_nodef) cs hcs (Eq.refl (OptionType Name) (OptionType.some Name nodeName))",
            "roseNode_whnfAcc: rose SN-open support (lane did NOT close; see header). Rung 10.",
        )?;

        self.add_recursive_def(
            "def whnfAccAll_of_memL (l : ListType KExpr) (h : forall (x : KExpr), MemL x l -> whnf_acc x) : WhnfAccAll l := ListType.rec KExpr (fun (l0 : ListType KExpr) => (forall (x : KExpr), MemL x l0 -> whnf_acc x) -> WhnfAccAll l0) (fun (_h0 : forall (x : KExpr), MemL x (ListType.nil KExpr) -> whnf_acc x) => WhnfAccAll.nil) (fun (y : KExpr) (rest : ListType KExpr) (ih : (forall (x : KExpr), MemL x rest -> whnf_acc x) -> WhnfAccAll rest) => fun (hall : forall (x : KExpr), MemL x (ListType.cons KExpr y rest) -> whnf_acc x) => WhnfAccAll.cons y rest (hall y (MemL.head y rest)) (ih (fun (x : KExpr) (hm : MemL x rest) => hall x (MemL.tail x y rest hm)))) l h",
            "whnfAccAll_of_memL: rose SN-open support (lane did NOT close; see header). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseCanonMajor_whnfAcc (children : ListType KExpr) (h : forall (x : KExpr), MemL x children -> whnf_acc x) : whnf_acc (roseNode (roseList children)) := roseNode_whnfAcc (roseList children) (roseList_whnfAcc children (whnfAccAll_of_memL children h))",
            "roseCanonMajor_whnfAcc: rose SN-open support (lane did NOT close; see header). Rung 10.",
        )?;

        self.add_recursive_def(
            "def whnf_terminates_roseRec_open_canon (u : Level) (C : KExpr) (m : KExpr) (children : ListType KExpr) (hC : whnf_acc C) (hm : whnf_acc m) (hch : forall (x : KExpr), MemL x children -> whnf_acc x) : whnf_acc (roseRecApp u C m (roseNode (roseList children))) := roseRecApp_whnfAcc_inert u roseRec_red_nodef roseRec_red_norecmeta C m (roseNode (roseList children)) hC hm (roseCanonMajor_whnfAcc children hch)",
            "whnf_terminates_roseRec_open_canon: rose SN-open support (lane did NOT close; see header). Rung 10.",
        )?;

        self.add_recursive_def(
            "def RoseStuckMajor (u : Level) (t : KExpr) : Prop := forall (cn : Name), Eq (OptionType Name) (kexpr_const_name (kapp_fn t)) (OptionType.some Name cn) -> Eq (OptionType RecRule) (recrule_for (roseREnv u) roseRecName cn) (OptionType.none RecRule)",
            "RoseStuckMajor: rose SN-open support (lane did NOT close; see header). Rung 10.",
        )?;

        self.add_recursive_def(
            "def roseStuckMajor_bvar (u : Level) (i : Nat) : RoseStuckMajor u (KExpr.bvar i) := fun (cn : Name) (h : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.bvar i))) (OptionType.some Name cn)) => option_none_ne_some Name cn (Eq (OptionType RecRule) (recrule_for (roseREnv u) roseRecName cn) (OptionType.none RecRule)) h",
            "roseStuckMajor_bvar: rose SN-open support (lane did NOT close; see header). Rung 10.",
        )?;

        self.add_recursive_def(
            "def neutral_roseRecApp (u : Level) (C : KExpr) (m : KExpr) (t : KExpr) : Neutral (roseRecApp u C m t) := ConstFreeUnit.triv",
            "neutral_roseRecApp: rose SN-open support (lane did NOT close; see header). Rung 10.",
        )?;

        Ok(())
    }
}
