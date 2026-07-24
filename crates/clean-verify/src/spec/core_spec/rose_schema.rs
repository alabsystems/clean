// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nested-inductive rung (10th fragment increment): rose trees
//! `Rose := node (children : List Rose)` — the constructor NESTS the family
//! under a container (List Rose), the shape beyond mutual/higher-order. The
//! recursor uses a fused List.rec to map over the children, so the nested
//! container is modeled as its own object-level family (List Rose with
//! nil/cons/rec). Ported from the Aristotle-proven w5/wave-9 nested-rose guide
//! (scratch/aristotle-nested-rose/NestedRoseSN.lean, whnf_terminates_well_typed_rose
//! proven via the roseTEnv backbone) through the workflow port-draft
//! scratch/port-nested-rose.md. Object layer + rfl gates + the SN one-liner;
//! the 3 hard computational theorems (roseRecRhs_instIter / rose_recContract_steps
//! / whnf_terminates_roseRec_open) are deferred (they need a whnf_step/RoseMajor
//! reduction substrate not yet in-spec). Census stays 11.

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
        self.add_recursive_def(
            "def roseREnv (u : Level) : RecEnv := RecEnv.addRec RecEnv.empty roseRecName roseRecMeta (roseRecRules u)",
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

        Ok(())
    }
}
