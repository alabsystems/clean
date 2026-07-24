// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! de Bruijn keystone: instantiate_at is the identity above the free-variable
//! ceiling (Stage-0 Brick 1).
//!
//! Clean port of the Aristotle-proven Lean lemma
//! `proofs/lean-aristotle/inst_above_ceiling_id.lean` (0 sorry). The Lean proof
//! is `induction e; simp_all +decide`; here the same induction is the explicit
//! `KExpr.rec` term, mirroring `expr_model_lift_cancel.rs::lift_cancel_gen`.
//!
//! `bvar_ceiling` is an ADD-based over-approximation of the free de Bruijn
//! ceiling: binders do NOT subtract (a looser-but-valid bound that avoids
//! needing `Nat.max`, which the spec does not provide). The keystone:
//!
//!   inst_above_ceiling_id : Le (bvar_ceiling e) d -> instantiate_at e val d = e
//!
//! Substitution at a depth no free variable reaches is the identity. This
//! unblocks env-generalizing the iota/delta defeq rules (specializes WF_SUBST
//! down to DefEq e e' by choosing d above both ceilings).
//!
//! Also hosts the LIFT analogue (Front #1 keystone, Aristotle strategy guide
//! `/tmp/ari-keystones/project_aristotle/Keystones.lean`, foundational-only
//! closure):
//!
//!   lift_ceiling_id : Le (bvar_ceiling e) cutoff -> lift_at e cutoff amount = e
//!
//! Lifting at a cutoff at-or-above the ceiling is the identity — it lets a
//! rule-RHS with `bvar_ceiling rhs = 0` (rfl-provable on concrete envs) yield
//! `lift_at rhs c a = rhs` for the i4/i6 (RecEnvLiftClosed / DefEnvLiftClosed)
//! interfaces. Same generalized-cutoff KExpr.rec shape as the inst keystone.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_expr_model_inst_ceiling(&mut self) -> Result<(), SpecError> {
        // bvar_ceiling: ADD-based strict over-approximation of the free de
        // Bruijn ceiling. sort/const are closed leaves (0); bvar i contributes
        // succ i; app/lam/pi sum the children (binders do NOT subtract — looser
        // but valid, and avoids Nat.max). Structural KExpr recursion → Nat, the
        // same shape as kapp_arg_count, so the constructor-unfolding lemmas below
        // hold by Eq.refl.
        self.add_recursive_def(
            r"def bvar_ceiling (e : KExpr) : Nat := match e with
| KExpr.sort n => Nat.zero
| KExpr.bvar i => Nat.succ i
| KExpr.app f a => Nat.add (bvar_ceiling f) (bvar_ceiling a)
| KExpr.lam ty b => Nat.add (bvar_ceiling ty) (bvar_ceiling b)
| KExpr.pi ty b => Nat.add (bvar_ceiling ty) (bvar_ceiling b)
| KExpr.const n us => Nat.zero
| KExpr.let_ ty v b => Nat.add (bvar_ceiling ty) (Nat.add (bvar_ceiling v) (bvar_ceiling b))
| KExpr.proj s i sub => bvar_ceiling sub
| KExpr.lit n => Nat.zero",
            "ADD-based strict over-approximation of the free de Bruijn ceiling \
             (binders do not subtract). Stage-0 Brick 1.",
        )?;

        // bvar_ceiling_bvar: unfolding — bvar_ceiling (bvar i) = succ i.
        self.add_definition(SpecDefinition {
            name: "bvar_ceiling_bvar".to_string(),
            type_src: "forall (i : Nat), Eq Nat (bvar_ceiling (KExpr.bvar i)) (Nat.succ i)"
                .to_string(),
            value_src: Some("fun (i : Nat) => Eq.refl Nat (Nat.succ i)".to_string()),
            is_axiom: false,
            description: "Unfolding: bvar_ceiling (bvar i) = succ i. DerivedProved via Eq.refl. \
                          Stage-0 Brick 1."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // bvar_ceiling_app: unfolding — bvar_ceiling (app f a) = add (ceil f) (ceil a).
        self.add_definition(SpecDefinition {
            name: "bvar_ceiling_app".to_string(),
            type_src: concat!(
                "forall (f : KExpr) (a : KExpr), ",
                "Eq Nat (bvar_ceiling (KExpr.app f a)) ",
                "(Nat.add (bvar_ceiling f) (bvar_ceiling a))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (f : KExpr) (a : KExpr) => ",
                    "Eq.refl Nat (Nat.add (bvar_ceiling f) (bvar_ceiling a))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Unfolding: bvar_ceiling (app f a) = add (ceil f) (ceil a). \
                          DerivedProved via Eq.refl. Stage-0 Brick 1."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // bvar_ceiling_lam: unfolding — bvar_ceiling (lam ty b) = add (ceil ty) (ceil b).
        self.add_definition(SpecDefinition {
            name: "bvar_ceiling_lam".to_string(),
            type_src: concat!(
                "forall (ty : KExpr) (b : KExpr), ",
                "Eq Nat (bvar_ceiling (KExpr.lam ty b)) ",
                "(Nat.add (bvar_ceiling ty) (bvar_ceiling b))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (ty : KExpr) (b : KExpr) => ",
                    "Eq.refl Nat (Nat.add (bvar_ceiling ty) (bvar_ceiling b))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Unfolding: bvar_ceiling (lam ty b) = add (ceil ty) (ceil b). \
                          DerivedProved via Eq.refl. Stage-0 Brick 1."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // bvar_ceiling_pi: unfolding — bvar_ceiling (pi ty b) = add (ceil ty) (ceil b).
        self.add_definition(SpecDefinition {
            name: "bvar_ceiling_pi".to_string(),
            type_src: concat!(
                "forall (ty : KExpr) (b : KExpr), ",
                "Eq Nat (bvar_ceiling (KExpr.pi ty b)) ",
                "(Nat.add (bvar_ceiling ty) (bvar_ceiling b))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (ty : KExpr) (b : KExpr) => ",
                    "Eq.refl Nat (Nat.add (bvar_ceiling ty) (bvar_ceiling b))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Unfolding: bvar_ceiling (pi ty b) = add (ceil ty) (ceil b). \
                          DerivedProved via Eq.refl. Stage-0 Brick 1."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // bvar_ceiling_let_: unfolding — bvar_ceiling (let_ ty v b)
        // = add (ceil ty) (add (ceil v) (ceil b)).
        self.add_definition(SpecDefinition {
            name: "bvar_ceiling_let_".to_string(),
            type_src: concat!(
                "forall (ty : KExpr) (v : KExpr) (b : KExpr), ",
                "Eq Nat (bvar_ceiling (KExpr.let_ ty v b)) ",
                "(Nat.add (bvar_ceiling ty) (Nat.add (bvar_ceiling v) (bvar_ceiling b)))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (ty : KExpr) (v : KExpr) (b : KExpr) => ",
                    "Eq.refl Nat (Nat.add (bvar_ceiling ty) ",
                    "(Nat.add (bvar_ceiling v) (bvar_ceiling b)))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Unfolding: bvar_ceiling (let_ ty v b) = add (ceil ty) (add (ceil v) \
                          (ceil b)). DerivedProved via Eq.refl. Part of the let-promotion \
                          surgery (task #28)."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // nat_sub_succ_self: Nat.sub (succ i) i = succ 0.
        //
        // Nat.rec on i.
        //   base i=0: Nat.sub (succ 0) 0 = succ 0 by iota on concrete zero (Eq.refl).
        //   step i=succ k: nat_sub_succ_succ (succ k) k reduces the minuend/subtrahend,
        //     then the IH closes.
        self.add_definition(SpecDefinition {
            name: "nat_sub_succ_self".to_string(),
            type_src: "forall (i : Nat), Eq Nat (Nat.sub (Nat.succ i) i) (Nat.succ Nat.zero)"
                .to_string(),
            value_src: Some(
                concat!(
                    "fun (i : Nat) => Nat.rec ",
                    "(fun (j : Nat) => Eq Nat (Nat.sub (Nat.succ j) j) (Nat.succ Nat.zero)) ",
                    "(Eq.refl Nat (Nat.succ Nat.zero)) ",
                    "(fun (k : Nat) (ih : Eq Nat (Nat.sub (Nat.succ k) k) (Nat.succ Nat.zero)) => ",
                    "Eq.trans Nat ",
                    "(Nat.sub (Nat.succ (Nat.succ k)) (Nat.succ k)) ",
                    "(Nat.sub (Nat.succ k) k) ",
                    "(Nat.succ Nat.zero) ",
                    "(nat_sub_succ_succ (Nat.succ k) k) ",
                    "ih) ",
                    "i",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Nat.sub (succ i) i = succ 0. DerivedProved via Nat.rec on i + \
                          nat_sub_succ_succ. Stage-0 Brick 1."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(),
                "Eq.refl".to_string(),
                "Eq.trans".to_string(),
                "nat_sub_succ_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_sub_succ_pos: Le (succ i) d -> Nat.sub d i is positive (witness shape).
        //
        // Le.rec on the proof (first index succ i promoted to parameter; motive over
        // the second index j is exactly the positivity-witness equation on Nat.sub j i):
        //   refl arm (j = succ i): nat_sub_succ_self i gives Nat.sub (succ i) i = succ 0;
        //     nat_pos_witness_from_succ_eq reshapes it to the witness form.
        //   step arm (j = succ m): nat_sub_pos_succ m i lifts the IH from m to succ m.
        self.add_definition(SpecDefinition {
            name: "nat_sub_succ_pos".to_string(),
            type_src: concat!(
                "forall (i : Nat) (d : Nat), ",
                "Le (Nat.succ i) d -> ",
                "Eq Nat (Nat.sub d i) ",
                "(Nat.succ (Nat.sub (Nat.sub d i) (Nat.succ Nat.zero)))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (i : Nat) (d : Nat) (h : Le (Nat.succ i) d) => ",
                    "Le.rec (Nat.succ i) ",
                    "(fun (j : Nat) (_ : Le (Nat.succ i) j) => ",
                    "Eq Nat (Nat.sub j i) ",
                    "(Nat.succ (Nat.sub (Nat.sub j i) (Nat.succ Nat.zero)))) ",
                    // refl arm: j = succ i
                    "(nat_pos_witness_from_succ_eq (Nat.sub (Nat.succ i) i) Nat.zero ",
                    "(nat_sub_succ_self i)) ",
                    // step arm: j = succ m
                    "(fun (m : Nat) (_hm : Le (Nat.succ i) m) ",
                    "(ihm : Eq Nat (Nat.sub m i) ",
                    "(Nat.succ (Nat.sub (Nat.sub m i) (Nat.succ Nat.zero)))) => ",
                    "nat_sub_pos_succ m i ihm) ",
                    "d h",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Le (succ i) d -> Nat.sub d i positive (witness shape). DerivedProved \
                          via Le.rec on the proof; refl arm uses nat_sub_succ_self + \
                          nat_pos_witness_from_succ_eq, step arm uses nat_sub_pos_succ. \
                          Stage-0 Brick 1."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Le".to_string(),
                "Le.rec".to_string(),
                "nat_sub_succ_self".to_string(),
                "nat_pos_witness_from_succ_eq".to_string(),
                "nat_sub_pos_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // inst_bvar_lt: if succ i <= d then instantiate_bvar_at i d v = bvar i.
        //
        // instantiate_bvar_at_below consumes the positivity witness; nat_sub_succ_pos
        // supplies it from the Le proof.
        self.add_definition(SpecDefinition {
            name: "inst_bvar_lt".to_string(),
            type_src: concat!(
                "forall (i : Nat) (d : Nat) (v : KExpr), ",
                "Le (Nat.succ i) d -> ",
                "Eq KExpr (instantiate_bvar_at i d v) (KExpr.bvar i)",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (i : Nat) (d : Nat) (v : KExpr) (h : Le (Nat.succ i) d) => ",
                    "instantiate_bvar_at_below i d v (nat_sub_succ_pos i d h)",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "If succ i <= d then instantiate_bvar_at i d v = bvar i. DerivedProved \
                          via instantiate_bvar_at_below + nat_sub_succ_pos. Stage-0 Brick 1."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Le".to_string(),
                "instantiate_bvar_at_below".to_string(),
                "nat_sub_succ_pos".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // le_add_self_right: Le b (add a b). Transport le_add_self_left b a along
        // nat_add_comm b a (add b a = add a b).
        self.add_definition(SpecDefinition {
            name: "le_add_self_right".to_string(),
            type_src: "forall (a : Nat) (b : Nat), Le b (Nat.add a b)".to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) => ",
                    "Eq.subst Nat (fun (z : Nat) => Le b z) ",
                    "(Nat.add b a) (Nat.add a b) ",
                    "(nat_add_comm b a) ",
                    "(le_add_self_left b a)",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Le b (add a b): b is below its left-sum. DerivedProved via Eq.subst \
                          transport of le_add_self_left along nat_add_comm. Stage-0 Brick 1."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Le".to_string(),
                "Eq.subst".to_string(),
                "nat_add_comm".to_string(),
                "le_add_self_left".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // inst_above_ceiling_id (KEYSTONE): if d is at-or-above the ceiling of e then
        // instantiate_at e val d = e.
        //
        // Explicit KExpr.rec on e with a (val, d)-universalized, hypothesis-carrying
        // motive (mirror of lift_cancel_gen):
        //   M x := forall (v : KExpr) (d : Nat),
        //            Le (bvar_ceiling x) d -> Eq KExpr (instantiate_at x v d) x.
        //   sort/const: instantiate_at_sort / instantiate_at_const (Le hyp unused).
        //   bvar i: transport the hyp through bvar_ceiling_bvar to Le (succ i) d, then
        //     instantiate_at_bvar ; inst_bvar_lt.
        //   app/lam/pi: transport through bvar_ceiling_{app,lam,pi}, split the add-bound
        //     with le_add_self_{left,right} + le_trans, recurse via the IHs (binders
        //     step the body bound to succ d via Le.step), rebuild with the
        //     instantiate_at_{app,lam,pi} unfoldings + Eq.cong/Eq.trans.
        self.add_definition(SpecDefinition {
            name: "inst_above_ceiling_id".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (val : KExpr) (d : Nat), ",
                "Le (bvar_ceiling e) d -> ",
                "Eq KExpr (instantiate_at e val d) e",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (val : KExpr) (d : Nat) (h : Le (bvar_ceiling e) d) => ",
                    "KExpr.rec ",
                    // motive
                    "(fun (x : KExpr) => forall (v : KExpr) (c : Nat), ",
                    "Le (bvar_ceiling x) c -> Eq KExpr (instantiate_at x v c) x) ",
                    // --- sort branch ---
                    "(fun (n : Level) (v : KExpr) (c : Nat) ",
                    "(_ : Le (bvar_ceiling (KExpr.sort n)) c) => ",
                    "instantiate_at_sort n v c) ",
                    // --- bvar branch ---
                    "(fun (i : Nat) (v : KExpr) (c : Nat) ",
                    "(hb : Le (bvar_ceiling (KExpr.bvar i)) c) => ",
                    "Eq.trans KExpr ",
                    "(instantiate_at (KExpr.bvar i) v c) ",
                    "(instantiate_bvar_at i c v) ",
                    "(KExpr.bvar i) ",
                    "(instantiate_at_bvar i v c) ",
                    "(inst_bvar_lt i c v ",
                    "(Eq.subst Nat (fun (z : Nat) => Le z c) ",
                    "(bvar_ceiling (KExpr.bvar i)) (Nat.succ i) ",
                    "(bvar_ceiling_bvar i) hb))) ",
                    // --- app branch ---
                    "(fun (f : KExpr) (a : KExpr) ",
                    "(ihf : forall (v : KExpr) (c : Nat), ",
                    "Le (bvar_ceiling f) c -> Eq KExpr (instantiate_at f v c) f) ",
                    "(iha : forall (v : KExpr) (c : Nat), ",
                    "Le (bvar_ceiling a) c -> Eq KExpr (instantiate_at a v c) a) ",
                    "(v : KExpr) (c : Nat) ",
                    "(hap : Le (bvar_ceiling (KExpr.app f a)) c) => ",
                    "Eq.trans KExpr ",
                    "(instantiate_at (KExpr.app f a) v c) ",
                    "(KExpr.app (instantiate_at f v c) (instantiate_at a v c)) ",
                    "(KExpr.app f a) ",
                    "(instantiate_at_app f a v c) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.app (instantiate_at f v c) (instantiate_at a v c)) ",
                    "(KExpr.app f (instantiate_at a v c)) ",
                    "(KExpr.app f a) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.app x (instantiate_at a v c)) ",
                    "(instantiate_at f v c) f ",
                    "(ihf v c ",
                    "(le_trans (bvar_ceiling f) ",
                    "(Nat.add (bvar_ceiling f) (bvar_ceiling a)) c ",
                    "(le_add_self_left (bvar_ceiling f) (bvar_ceiling a)) ",
                    "(Eq.subst Nat (fun (z : Nat) => Le z c) ",
                    "(bvar_ceiling (KExpr.app f a)) ",
                    "(Nat.add (bvar_ceiling f) (bvar_ceiling a)) ",
                    "(bvar_ceiling_app f a) hap)))) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.app f x) ",
                    "(instantiate_at a v c) a ",
                    "(iha v c ",
                    "(le_trans (bvar_ceiling a) ",
                    "(Nat.add (bvar_ceiling f) (bvar_ceiling a)) c ",
                    "(le_add_self_right (bvar_ceiling f) (bvar_ceiling a)) ",
                    "(Eq.subst Nat (fun (z : Nat) => Le z c) ",
                    "(bvar_ceiling (KExpr.app f a)) ",
                    "(Nat.add (bvar_ceiling f) (bvar_ceiling a)) ",
                    "(bvar_ceiling_app f a) hap)))))) ",
                    // --- lam branch ---
                    "(fun (ty : KExpr) (b : KExpr) ",
                    "(ihty : forall (v : KExpr) (c : Nat), ",
                    "Le (bvar_ceiling ty) c -> Eq KExpr (instantiate_at ty v c) ty) ",
                    "(ihb : forall (v : KExpr) (c : Nat), ",
                    "Le (bvar_ceiling b) c -> Eq KExpr (instantiate_at b v c) b) ",
                    "(v : KExpr) (c : Nat) ",
                    "(hlam : Le (bvar_ceiling (KExpr.lam ty b)) c) => ",
                    "Eq.trans KExpr ",
                    "(instantiate_at (KExpr.lam ty b) v c) ",
                    "(KExpr.lam (instantiate_at ty v c) (instantiate_at b v (Nat.succ c))) ",
                    "(KExpr.lam ty b) ",
                    "(instantiate_at_lam ty b v c) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.lam (instantiate_at ty v c) (instantiate_at b v (Nat.succ c))) ",
                    "(KExpr.lam ty (instantiate_at b v (Nat.succ c))) ",
                    "(KExpr.lam ty b) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.lam x (instantiate_at b v (Nat.succ c))) ",
                    "(instantiate_at ty v c) ty ",
                    "(ihty v c ",
                    "(le_trans (bvar_ceiling ty) ",
                    "(Nat.add (bvar_ceiling ty) (bvar_ceiling b)) c ",
                    "(le_add_self_left (bvar_ceiling ty) (bvar_ceiling b)) ",
                    "(Eq.subst Nat (fun (z : Nat) => Le z c) ",
                    "(bvar_ceiling (KExpr.lam ty b)) ",
                    "(Nat.add (bvar_ceiling ty) (bvar_ceiling b)) ",
                    "(bvar_ceiling_lam ty b) hlam)))) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.lam ty x) ",
                    "(instantiate_at b v (Nat.succ c)) b ",
                    "(ihb v (Nat.succ c) ",
                    "(Le.step (bvar_ceiling b) c ",
                    "(le_trans (bvar_ceiling b) ",
                    "(Nat.add (bvar_ceiling ty) (bvar_ceiling b)) c ",
                    "(le_add_self_right (bvar_ceiling ty) (bvar_ceiling b)) ",
                    "(Eq.subst Nat (fun (z : Nat) => Le z c) ",
                    "(bvar_ceiling (KExpr.lam ty b)) ",
                    "(Nat.add (bvar_ceiling ty) (bvar_ceiling b)) ",
                    "(bvar_ceiling_lam ty b) hlam))))))) ",
                    // --- pi branch ---
                    "(fun (ty : KExpr) (b : KExpr) ",
                    "(ihty : forall (v : KExpr) (c : Nat), ",
                    "Le (bvar_ceiling ty) c -> Eq KExpr (instantiate_at ty v c) ty) ",
                    "(ihb : forall (v : KExpr) (c : Nat), ",
                    "Le (bvar_ceiling b) c -> Eq KExpr (instantiate_at b v c) b) ",
                    "(v : KExpr) (c : Nat) ",
                    "(hpi : Le (bvar_ceiling (KExpr.pi ty b)) c) => ",
                    "Eq.trans KExpr ",
                    "(instantiate_at (KExpr.pi ty b) v c) ",
                    "(KExpr.pi (instantiate_at ty v c) (instantiate_at b v (Nat.succ c))) ",
                    "(KExpr.pi ty b) ",
                    "(instantiate_at_pi ty b v c) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.pi (instantiate_at ty v c) (instantiate_at b v (Nat.succ c))) ",
                    "(KExpr.pi ty (instantiate_at b v (Nat.succ c))) ",
                    "(KExpr.pi ty b) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.pi x (instantiate_at b v (Nat.succ c))) ",
                    "(instantiate_at ty v c) ty ",
                    "(ihty v c ",
                    "(le_trans (bvar_ceiling ty) ",
                    "(Nat.add (bvar_ceiling ty) (bvar_ceiling b)) c ",
                    "(le_add_self_left (bvar_ceiling ty) (bvar_ceiling b)) ",
                    "(Eq.subst Nat (fun (z : Nat) => Le z c) ",
                    "(bvar_ceiling (KExpr.pi ty b)) ",
                    "(Nat.add (bvar_ceiling ty) (bvar_ceiling b)) ",
                    "(bvar_ceiling_pi ty b) hpi)))) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.pi ty x) ",
                    "(instantiate_at b v (Nat.succ c)) b ",
                    "(ihb v (Nat.succ c) ",
                    "(Le.step (bvar_ceiling b) c ",
                    "(le_trans (bvar_ceiling b) ",
                    "(Nat.add (bvar_ceiling ty) (bvar_ceiling b)) c ",
                    "(le_add_self_right (bvar_ceiling ty) (bvar_ceiling b)) ",
                    "(Eq.subst Nat (fun (z : Nat) => Le z c) ",
                    "(bvar_ceiling (KExpr.pi ty b)) ",
                    "(Nat.add (bvar_ceiling ty) (bvar_ceiling b)) ",
                    "(bvar_ceiling_pi ty b) hpi))))))) ",
                    // --- const branch ---
                    "(fun (nm : Name) (us : ListType Level) (v : KExpr) (c : Nat) ",
                    "(_ : Le (bvar_ceiling (KExpr.const nm us)) c) => ",
                    "instantiate_at_const nm us v c) ",
                    // --- let_ branch ---
                    "(fun (ty : KExpr) (val : KExpr) (body : KExpr) ",
                    "(ihty : forall (v : KExpr) (c : Nat), ",
                    "Le (bvar_ceiling ty) c -> Eq KExpr (instantiate_at ty v c) ty) ",
                    "(ihval : forall (v : KExpr) (c : Nat), ",
                    "Le (bvar_ceiling val) c -> Eq KExpr (instantiate_at val v c) val) ",
                    "(ihbody : forall (v : KExpr) (c : Nat), ",
                    "Le (bvar_ceiling body) c -> Eq KExpr (instantiate_at body v c) body) ",
                    "(v : KExpr) (c : Nat) ",
                    "(hlet : Le (bvar_ceiling (KExpr.let_ ty val body)) c) => ",
                    "Eq.trans KExpr ",
                    "(instantiate_at (KExpr.let_ ty val body) v c) ",
                    "(KExpr.let_ (instantiate_at ty v c) (instantiate_at val v c) (instantiate_at body v (Nat.succ c))) ",
                    "(KExpr.let_ ty val body) ",
                    "(instantiate_at_let_ ty val body v c) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.let_ (instantiate_at ty v c) (instantiate_at val v c) (instantiate_at body v (Nat.succ c))) ",
                    "(KExpr.let_ ty (instantiate_at val v c) (instantiate_at body v (Nat.succ c))) ",
                    "(KExpr.let_ ty val body) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.let_ x (instantiate_at val v c) (instantiate_at body v (Nat.succ c))) ",
                    "(instantiate_at ty v c) ty ",
                    "(ihty v c ",
                    "(le_trans (bvar_ceiling ty) ",
                    "(Nat.add (bvar_ceiling ty) (Nat.add (bvar_ceiling val) (bvar_ceiling body))) c ",
                    "(le_add_self_left (bvar_ceiling ty) (Nat.add (bvar_ceiling val) (bvar_ceiling body))) ",
                    "(Eq.subst Nat (fun (z : Nat) => Le z c) ",
                    "(bvar_ceiling (KExpr.let_ ty val body)) ",
                    "(Nat.add (bvar_ceiling ty) (Nat.add (bvar_ceiling val) (bvar_ceiling body))) ",
                    "(bvar_ceiling_let_ ty val body) hlet)))) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.let_ ty (instantiate_at val v c) (instantiate_at body v (Nat.succ c))) ",
                    "(KExpr.let_ ty val (instantiate_at body v (Nat.succ c))) ",
                    "(KExpr.let_ ty val body) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.let_ ty x (instantiate_at body v (Nat.succ c))) ",
                    "(instantiate_at val v c) val ",
                    "(ihval v c ",
                    "(le_trans (bvar_ceiling val) ",
                    "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) c ",
                    "(le_add_self_left (bvar_ceiling val) (bvar_ceiling body)) ",
                    "(le_trans (Nat.add (bvar_ceiling val) (bvar_ceiling body)) ",
                    "(Nat.add (bvar_ceiling ty) (Nat.add (bvar_ceiling val) (bvar_ceiling body))) c ",
                    "(le_add_self_right (bvar_ceiling ty) (Nat.add (bvar_ceiling val) (bvar_ceiling body))) ",
                    "(Eq.subst Nat (fun (z : Nat) => Le z c) ",
                    "(bvar_ceiling (KExpr.let_ ty val body)) ",
                    "(Nat.add (bvar_ceiling ty) (Nat.add (bvar_ceiling val) (bvar_ceiling body))) ",
                    "(bvar_ceiling_let_ ty val body) hlet))))) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.let_ ty val x) ",
                    "(instantiate_at body v (Nat.succ c)) body ",
                    "(ihbody v (Nat.succ c) ",
                    "(Le.step (bvar_ceiling body) c ",
                    "(le_trans (bvar_ceiling body) ",
                    "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) c ",
                    "(le_add_self_right (bvar_ceiling val) (bvar_ceiling body)) ",
                    "(le_trans (Nat.add (bvar_ceiling val) (bvar_ceiling body)) ",
                    "(Nat.add (bvar_ceiling ty) (Nat.add (bvar_ceiling val) (bvar_ceiling body))) c ",
                    "(le_add_self_right (bvar_ceiling ty) (Nat.add (bvar_ceiling val) (bvar_ceiling body))) ",
                    "(Eq.subst Nat (fun (z : Nat) => Le z c) ",
                    "(bvar_ceiling (KExpr.let_ ty val body)) ",
                    "(Nat.add (bvar_ceiling ty) (Nat.add (bvar_ceiling val) (bvar_ceiling body))) ",
                    "(bvar_ceiling_let_ ty val body) hlet))))))))) ",
                    // proj: 1-child; bvar_ceiling + instantiate_at reduce through proj; ih_sub cong.
                    "(fun (s : Name) (i : Nat) (sub : KExpr) ",
                    "(ih_sub : forall (v : KExpr) (c : Nat), Le (bvar_ceiling sub) c -> Eq KExpr (instantiate_at sub v c) sub) ",
                    "(v : KExpr) (c : Nat) (h : Le (bvar_ceiling (KExpr.proj s i sub)) c) => ",
                    "Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.proj s i x) (instantiate_at sub v c) sub (ih_sub v c h)) ",
                    "(fun (litn : Nat) (v : KExpr) (c : Nat) (h : Le (bvar_ceiling (KExpr.lit litn)) c) => Eq.refl KExpr (KExpr.lit litn)) ",
                    // major premise + universalized args
                    "e val d h",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "KEYSTONE: Le (bvar_ceiling e) d -> instantiate_at e val d = e. \
                          Clean port of the Aristotle-proven Lean lemma \
                          (proofs/lean-aristotle/inst_above_ceiling_id.lean). DerivedProved \
                          via explicit KExpr.rec with a hypothesis-carrying motive. \
                          Stage-0 Brick 1."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(),
                "Le".to_string(),
                "Le.step".to_string(),
                "Eq.subst".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "bvar_ceiling".to_string(),
                "bvar_ceiling_bvar".to_string(),
                "bvar_ceiling_app".to_string(),
                "bvar_ceiling_lam".to_string(),
                "bvar_ceiling_pi".to_string(),
                "bvar_ceiling_let_".to_string(),
                "instantiate_at_sort".to_string(),
                "instantiate_at_const".to_string(),
                "instantiate_at_app".to_string(),
                "instantiate_at_lam".to_string(),
                "instantiate_at_pi".to_string(),
                "instantiate_at_let_".to_string(),
                "instantiate_at_bvar".to_string(),
                "inst_bvar_lt".to_string(),
                "le_trans".to_string(),
                "le_add_self_left".to_string(),
                "le_add_self_right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lift_bvar_lt: if succ i <= c then lift_at (bvar i) c amount = bvar i.
        //
        // The lift mirror of inst_bvar_lt: lift_at_bvar_below consumes the
        // positivity witness; nat_sub_succ_pos supplies it from the Le proof.
        self.add_definition(SpecDefinition {
            name: "lift_bvar_lt".to_string(),
            type_src: concat!(
                "forall (i : Nat) (c : Nat) (amount : Nat), ",
                "Le (Nat.succ i) c -> ",
                "Eq KExpr (lift_at (KExpr.bvar i) c amount) (KExpr.bvar i)",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (i : Nat) (c : Nat) (amount : Nat) (h : Le (Nat.succ i) c) => ",
                    "lift_at_bvar_below i c amount (nat_sub_succ_pos i c h)",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "If succ i <= c then lift_at (bvar i) c amount = bvar i. DerivedProved \
                          via lift_at_bvar_below + nat_sub_succ_pos — the lift mirror of \
                          inst_bvar_lt. Front #1 keystone support."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Le".to_string(),
                "lift_at_bvar_below".to_string(),
                "nat_sub_succ_pos".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lift_ceiling_id (KEYSTONE): if cutoff is at-or-above the ceiling of e
        // then lift_at e cutoff amount = e.
        //
        // The exact lift analogue of inst_above_ceiling_id (Aristotle strategy
        // guide Keystones.lean::lift_ceiling_id, [propext]-only closure there;
        // an explicit zero-axiom KExpr.rec term here). Explicit KExpr.rec on e
        // with an (amount, cutoff)-universalized, hypothesis-carrying motive:
        //   M x := forall (a : Nat) (c : Nat),
        //            Le (bvar_ceiling x) c -> Eq KExpr (lift_at x c a) x.
        //   sort/const: lift_at_sort / lift_at_const (Le hyp unused).
        //   bvar i: transport the hyp through bvar_ceiling_bvar to Le (succ i) c,
        //     then lift_bvar_lt.
        //   app/lam/pi: transport through bvar_ceiling_{app,lam,pi}, split the
        //     add-bound with le_add_self_{left,right} + le_trans, recurse via the
        //     IHs (binders step the body bound to succ c via Le.step), rebuild
        //     with the lift_at_{app,lam,pi} unfoldings + Eq.cong/Eq.trans.
        self.add_definition(SpecDefinition {
            name: "lift_ceiling_id".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (cutoff : Nat) (amount : Nat), ",
                "Le (bvar_ceiling e) cutoff -> ",
                "Eq KExpr (lift_at e cutoff amount) e",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (cutoff : Nat) (amount : Nat) ",
                    "(h : Le (bvar_ceiling e) cutoff) => ",
                    "KExpr.rec ",
                    // motive
                    "(fun (x : KExpr) => forall (a : Nat) (c : Nat), ",
                    "Le (bvar_ceiling x) c -> Eq KExpr (lift_at x c a) x) ",
                    // --- sort branch ---
                    "(fun (n : Level) (a : Nat) (c : Nat) ",
                    "(_ : Le (bvar_ceiling (KExpr.sort n)) c) => ",
                    "lift_at_sort n c a) ",
                    // --- bvar branch ---
                    "(fun (i : Nat) (a : Nat) (c : Nat) ",
                    "(hb : Le (bvar_ceiling (KExpr.bvar i)) c) => ",
                    "lift_bvar_lt i c a ",
                    "(Eq.subst Nat (fun (z : Nat) => Le z c) ",
                    "(bvar_ceiling (KExpr.bvar i)) (Nat.succ i) ",
                    "(bvar_ceiling_bvar i) hb)) ",
                    // --- app branch ---
                    "(fun (f : KExpr) (g : KExpr) ",
                    "(ihf : forall (a : Nat) (c : Nat), ",
                    "Le (bvar_ceiling f) c -> Eq KExpr (lift_at f c a) f) ",
                    "(ihg : forall (a : Nat) (c : Nat), ",
                    "Le (bvar_ceiling g) c -> Eq KExpr (lift_at g c a) g) ",
                    "(a : Nat) (c : Nat) ",
                    "(hap : Le (bvar_ceiling (KExpr.app f g)) c) => ",
                    "Eq.trans KExpr ",
                    "(lift_at (KExpr.app f g) c a) ",
                    "(KExpr.app (lift_at f c a) (lift_at g c a)) ",
                    "(KExpr.app f g) ",
                    "(lift_at_app f g c a) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.app (lift_at f c a) (lift_at g c a)) ",
                    "(KExpr.app f (lift_at g c a)) ",
                    "(KExpr.app f g) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.app x (lift_at g c a)) ",
                    "(lift_at f c a) f ",
                    "(ihf a c ",
                    "(le_trans (bvar_ceiling f) ",
                    "(Nat.add (bvar_ceiling f) (bvar_ceiling g)) c ",
                    "(le_add_self_left (bvar_ceiling f) (bvar_ceiling g)) ",
                    "(Eq.subst Nat (fun (z : Nat) => Le z c) ",
                    "(bvar_ceiling (KExpr.app f g)) ",
                    "(Nat.add (bvar_ceiling f) (bvar_ceiling g)) ",
                    "(bvar_ceiling_app f g) hap)))) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.app f x) ",
                    "(lift_at g c a) g ",
                    "(ihg a c ",
                    "(le_trans (bvar_ceiling g) ",
                    "(Nat.add (bvar_ceiling f) (bvar_ceiling g)) c ",
                    "(le_add_self_right (bvar_ceiling f) (bvar_ceiling g)) ",
                    "(Eq.subst Nat (fun (z : Nat) => Le z c) ",
                    "(bvar_ceiling (KExpr.app f g)) ",
                    "(Nat.add (bvar_ceiling f) (bvar_ceiling g)) ",
                    "(bvar_ceiling_app f g) hap)))))) ",
                    // --- lam branch ---
                    "(fun (ty : KExpr) (b : KExpr) ",
                    "(ihty : forall (a : Nat) (c : Nat), ",
                    "Le (bvar_ceiling ty) c -> Eq KExpr (lift_at ty c a) ty) ",
                    "(ihb : forall (a : Nat) (c : Nat), ",
                    "Le (bvar_ceiling b) c -> Eq KExpr (lift_at b c a) b) ",
                    "(a : Nat) (c : Nat) ",
                    "(hlam : Le (bvar_ceiling (KExpr.lam ty b)) c) => ",
                    "Eq.trans KExpr ",
                    "(lift_at (KExpr.lam ty b) c a) ",
                    "(KExpr.lam (lift_at ty c a) (lift_at b (Nat.succ c) a)) ",
                    "(KExpr.lam ty b) ",
                    "(lift_at_lam ty b c a) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.lam (lift_at ty c a) (lift_at b (Nat.succ c) a)) ",
                    "(KExpr.lam ty (lift_at b (Nat.succ c) a)) ",
                    "(KExpr.lam ty b) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.lam x (lift_at b (Nat.succ c) a)) ",
                    "(lift_at ty c a) ty ",
                    "(ihty a c ",
                    "(le_trans (bvar_ceiling ty) ",
                    "(Nat.add (bvar_ceiling ty) (bvar_ceiling b)) c ",
                    "(le_add_self_left (bvar_ceiling ty) (bvar_ceiling b)) ",
                    "(Eq.subst Nat (fun (z : Nat) => Le z c) ",
                    "(bvar_ceiling (KExpr.lam ty b)) ",
                    "(Nat.add (bvar_ceiling ty) (bvar_ceiling b)) ",
                    "(bvar_ceiling_lam ty b) hlam)))) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.lam ty x) ",
                    "(lift_at b (Nat.succ c) a) b ",
                    "(ihb a (Nat.succ c) ",
                    "(Le.step (bvar_ceiling b) c ",
                    "(le_trans (bvar_ceiling b) ",
                    "(Nat.add (bvar_ceiling ty) (bvar_ceiling b)) c ",
                    "(le_add_self_right (bvar_ceiling ty) (bvar_ceiling b)) ",
                    "(Eq.subst Nat (fun (z : Nat) => Le z c) ",
                    "(bvar_ceiling (KExpr.lam ty b)) ",
                    "(Nat.add (bvar_ceiling ty) (bvar_ceiling b)) ",
                    "(bvar_ceiling_lam ty b) hlam))))))) ",
                    // --- pi branch ---
                    "(fun (ty : KExpr) (b : KExpr) ",
                    "(ihty : forall (a : Nat) (c : Nat), ",
                    "Le (bvar_ceiling ty) c -> Eq KExpr (lift_at ty c a) ty) ",
                    "(ihb : forall (a : Nat) (c : Nat), ",
                    "Le (bvar_ceiling b) c -> Eq KExpr (lift_at b c a) b) ",
                    "(a : Nat) (c : Nat) ",
                    "(hpi : Le (bvar_ceiling (KExpr.pi ty b)) c) => ",
                    "Eq.trans KExpr ",
                    "(lift_at (KExpr.pi ty b) c a) ",
                    "(KExpr.pi (lift_at ty c a) (lift_at b (Nat.succ c) a)) ",
                    "(KExpr.pi ty b) ",
                    "(lift_at_pi ty b c a) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.pi (lift_at ty c a) (lift_at b (Nat.succ c) a)) ",
                    "(KExpr.pi ty (lift_at b (Nat.succ c) a)) ",
                    "(KExpr.pi ty b) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.pi x (lift_at b (Nat.succ c) a)) ",
                    "(lift_at ty c a) ty ",
                    "(ihty a c ",
                    "(le_trans (bvar_ceiling ty) ",
                    "(Nat.add (bvar_ceiling ty) (bvar_ceiling b)) c ",
                    "(le_add_self_left (bvar_ceiling ty) (bvar_ceiling b)) ",
                    "(Eq.subst Nat (fun (z : Nat) => Le z c) ",
                    "(bvar_ceiling (KExpr.pi ty b)) ",
                    "(Nat.add (bvar_ceiling ty) (bvar_ceiling b)) ",
                    "(bvar_ceiling_pi ty b) hpi)))) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.pi ty x) ",
                    "(lift_at b (Nat.succ c) a) b ",
                    "(ihb a (Nat.succ c) ",
                    "(Le.step (bvar_ceiling b) c ",
                    "(le_trans (bvar_ceiling b) ",
                    "(Nat.add (bvar_ceiling ty) (bvar_ceiling b)) c ",
                    "(le_add_self_right (bvar_ceiling ty) (bvar_ceiling b)) ",
                    "(Eq.subst Nat (fun (z : Nat) => Le z c) ",
                    "(bvar_ceiling (KExpr.pi ty b)) ",
                    "(Nat.add (bvar_ceiling ty) (bvar_ceiling b)) ",
                    "(bvar_ceiling_pi ty b) hpi))))))) ",
                    // --- const branch ---
                    "(fun (nm : Name) (us : ListType Level) (a : Nat) (c : Nat) ",
                    "(_ : Le (bvar_ceiling (KExpr.const nm us)) c) => ",
                    "lift_at_const nm us c a) ",
                    // --- let_ branch ---
                    "(fun (ty : KExpr) (val : KExpr) (body : KExpr) ",
                    "(ihty : forall (a : Nat) (c : Nat), ",
                    "Le (bvar_ceiling ty) c -> Eq KExpr (lift_at ty c a) ty) ",
                    "(ihval : forall (a : Nat) (c : Nat), ",
                    "Le (bvar_ceiling val) c -> Eq KExpr (lift_at val c a) val) ",
                    "(ihbody : forall (a : Nat) (c : Nat), ",
                    "Le (bvar_ceiling body) c -> Eq KExpr (lift_at body c a) body) ",
                    "(a : Nat) (c : Nat) ",
                    "(hlet : Le (bvar_ceiling (KExpr.let_ ty val body)) c) => ",
                    "Eq.trans KExpr ",
                    "(lift_at (KExpr.let_ ty val body) c a) ",
                    "(KExpr.let_ (lift_at ty c a) (lift_at val c a) (lift_at body (Nat.succ c) a)) ",
                    "(KExpr.let_ ty val body) ",
                    "(lift_at_let_ ty val body c a) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.let_ (lift_at ty c a) (lift_at val c a) (lift_at body (Nat.succ c) a)) ",
                    "(KExpr.let_ ty (lift_at val c a) (lift_at body (Nat.succ c) a)) ",
                    "(KExpr.let_ ty val body) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.let_ x (lift_at val c a) (lift_at body (Nat.succ c) a)) ",
                    "(lift_at ty c a) ty ",
                    "(ihty a c ",
                    "(le_trans (bvar_ceiling ty) ",
                    "(Nat.add (bvar_ceiling ty) (Nat.add (bvar_ceiling val) (bvar_ceiling body))) c ",
                    "(le_add_self_left (bvar_ceiling ty) (Nat.add (bvar_ceiling val) (bvar_ceiling body))) ",
                    "(Eq.subst Nat (fun (z : Nat) => Le z c) ",
                    "(bvar_ceiling (KExpr.let_ ty val body)) ",
                    "(Nat.add (bvar_ceiling ty) (Nat.add (bvar_ceiling val) (bvar_ceiling body))) ",
                    "(bvar_ceiling_let_ ty val body) hlet)))) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.let_ ty (lift_at val c a) (lift_at body (Nat.succ c) a)) ",
                    "(KExpr.let_ ty val (lift_at body (Nat.succ c) a)) ",
                    "(KExpr.let_ ty val body) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.let_ ty x (lift_at body (Nat.succ c) a)) ",
                    "(lift_at val c a) val ",
                    "(ihval a c ",
                    "(le_trans (bvar_ceiling val) ",
                    "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) c ",
                    "(le_add_self_left (bvar_ceiling val) (bvar_ceiling body)) ",
                    "(le_trans (Nat.add (bvar_ceiling val) (bvar_ceiling body)) ",
                    "(Nat.add (bvar_ceiling ty) (Nat.add (bvar_ceiling val) (bvar_ceiling body))) c ",
                    "(le_add_self_right (bvar_ceiling ty) (Nat.add (bvar_ceiling val) (bvar_ceiling body))) ",
                    "(Eq.subst Nat (fun (z : Nat) => Le z c) ",
                    "(bvar_ceiling (KExpr.let_ ty val body)) ",
                    "(Nat.add (bvar_ceiling ty) (Nat.add (bvar_ceiling val) (bvar_ceiling body))) ",
                    "(bvar_ceiling_let_ ty val body) hlet))))) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.let_ ty val x) ",
                    "(lift_at body (Nat.succ c) a) body ",
                    "(ihbody a (Nat.succ c) ",
                    "(Le.step (bvar_ceiling body) c ",
                    "(le_trans (bvar_ceiling body) ",
                    "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) c ",
                    "(le_add_self_right (bvar_ceiling val) (bvar_ceiling body)) ",
                    "(le_trans (Nat.add (bvar_ceiling val) (bvar_ceiling body)) ",
                    "(Nat.add (bvar_ceiling ty) (Nat.add (bvar_ceiling val) (bvar_ceiling body))) c ",
                    "(le_add_self_right (bvar_ceiling ty) (Nat.add (bvar_ceiling val) (bvar_ceiling body))) ",
                    "(Eq.subst Nat (fun (z : Nat) => Le z c) ",
                    "(bvar_ceiling (KExpr.let_ ty val body)) ",
                    "(Nat.add (bvar_ceiling ty) (Nat.add (bvar_ceiling val) (bvar_ceiling body))) ",
                    "(bvar_ceiling_let_ ty val body) hlet))))))))) ",
                    // proj: 1-child; bvar_ceiling + lift_at reduce through proj; ih_sub cong.
                    "(fun (s : Name) (i : Nat) (sub : KExpr) ",
                    "(ih_sub : forall (a : Nat) (c : Nat), Le (bvar_ceiling sub) c -> Eq KExpr (lift_at sub c a) sub) ",
                    "(a : Nat) (c : Nat) (h : Le (bvar_ceiling (KExpr.proj s i sub)) c) => ",
                    "Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.proj s i x) (lift_at sub c a) sub (ih_sub a c h)) ",
                    "(fun (litn : Nat) (a : Nat) (c : Nat) (h : Le (bvar_ceiling (KExpr.lit litn)) c) => Eq.refl KExpr (KExpr.lit litn)) ",
                    // major premise + universalized args
                    "e amount cutoff h",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "KEYSTONE: Le (bvar_ceiling e) cutoff -> lift_at e cutoff amount = e. \
                          The lift analogue of inst_above_ceiling_id — Clean port of the \
                          Aristotle-proven Lean lemma (Keystones.lean::lift_ceiling_id, Front #1). \
                          DerivedProved via explicit KExpr.rec with a hypothesis-carrying, \
                          cutoff-generalized motive. Zero axiom deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(),
                "Le".to_string(),
                "Le.step".to_string(),
                "Eq.subst".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "bvar_ceiling".to_string(),
                "bvar_ceiling_bvar".to_string(),
                "bvar_ceiling_app".to_string(),
                "bvar_ceiling_lam".to_string(),
                "bvar_ceiling_pi".to_string(),
                "bvar_ceiling_let_".to_string(),
                "lift_at_sort".to_string(),
                "lift_at_const".to_string(),
                "lift_at_app".to_string(),
                "lift_at_lam".to_string(),
                "lift_at_pi".to_string(),
                "lift_at_let_".to_string(),
                "lift_bvar_lt".to_string(),
                "le_trans".to_string(),
                "le_add_self_left".to_string(),
                "le_add_self_right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::spec::types::ProofStatus;
    use crate::test_utils::build_spec_with_stack;

    #[test]
    fn test_inst_above_ceiling_id_is_constructive() {
        let spec = build_spec_with_stack();

        // bvar_ceiling is a kernel-checked recursive `def` (DerivedPending, the
        // standard status for elaborated defs — like lift_at / instantiate_at).
        // It must still be non-axiomatic with no axiom blockers.
        let ceiling = spec
            .definitions()
            .get("bvar_ceiling")
            .expect("Missing bvar_ceiling");
        assert!(
            ceiling.value_src.is_some(),
            "bvar_ceiling should have a value"
        );
        assert!(!ceiling.is_axiom, "bvar_ceiling should not be an axiom");
        assert!(
            ceiling.axiom_deps.is_empty(),
            "bvar_ceiling should have no axiom blockers: {:?}",
            ceiling.axiom_deps
        );

        // The unfolding lemmas, arithmetic/Le helpers, and the keystone are all
        // DerivedProved, zero-axiom proof terms.
        for name in [
            "bvar_ceiling_bvar",
            "bvar_ceiling_app",
            "bvar_ceiling_lam",
            "bvar_ceiling_pi",
            "bvar_ceiling_let_",
            "nat_sub_succ_self",
            "nat_sub_succ_pos",
            "inst_bvar_lt",
            "le_add_self_right",
            "inst_above_ceiling_id",
            "lift_bvar_lt",
            "lift_ceiling_id",
        ] {
            let def = spec
                .definitions()
                .get(name)
                .unwrap_or_else(|| panic!("Missing {name}"));
            assert!(def.value_src.is_some(), "{name} should have a proof term");
            assert!(!def.is_axiom, "{name} should not be an axiom");
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "{name} should be DerivedProved"
            );
            assert!(
                def.axiom_deps.is_empty(),
                "{name} should have no remaining helper blockers: {:?}",
                def.axiom_deps
            );
        }

        // The Front #1 lift keystone pair re-typechecks against the live kernel
        // environment (the ported Aristotle lemma is a genuine explicit term).
        for name in ["lift_bvar_lt", "lift_ceiling_id"] {
            spec.verify_definition(name).unwrap_or_else(|e| {
                panic!("{name} should re-typecheck in the spec environment: {e:?}")
            });
        }
    }
}
