// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! General instantiate-after-lift cancellation (additive de Bruijn brick).
//!
//! Clean port of the Aristotle-proven Lean lemma
//! `proofs/lean-aristotle/instantiate_lift_cancel_general.lean` (0 sorry). The
//! Lean proof is `induction e; split_ifs; omega`; here the same induction is the
//! explicit `KExpr.rec` term (mirroring `expr_model_lift_cancel.rs::lift_cancel_gen`
//! and `expr_model_inst_ceiling.rs`), and the bvar case-split is a `Nat.rec`
//! convoy on `Nat.sub cutoff idx` (the pattern used by
//! `expr_model_subst_lift_exchange.rs`).
//!
//! TARGET (`instantiate_lift_cancel_general`): when the substitution depth `d`
//! falls inside the freshly-lifted gap `[c, c+a)`, the substitution reaches no
//! occupied variable and collapses one unit of the lift:
//!
//!   instantiate_at (lift_at e c a) val d  =  lift_at e c (a - 1)
//!
//! The depth is parameterised as `d = c + j` (the faithful, equivalent form of
//! the Aristotle guard `c <= d < c + a`): `j` ranges over `[0, a)` exactly as `d`
//! ranges over `[c, c+a)`, and the single guard `j < a` (positivity of
//! `Nat.sub a j`) captures both `c <= d` (automatic: `d = c+j >= c`) and
//! `d < c + a` (`j < a`). This parameterisation keeps every bvar witness inside
//! the existing zero-axiom Nat toolbox -- the below case is a single
//! `nat_sub_pos_add_right`, and the geq case is `gap_to_add` +
//! `nat_sub_zero_add_monotone` + `nat_sub_pos_witness` + arithmetic transports.
//!
//! This GENERALISES two live spec lemmas: `lift_cancel_gen`
//! (expr_model_lift_cancel.rs, the `a = 1, j = 0` case) and the bvar core of the
//! keystone `inst_above_ceiling_id` (expr_model_inst_ceiling.rs). Additive: no
//! census axiom is drained (the saved de Bruijn Aristotle proofs mirror
//! already-DerivedProved lemmas; the 3 PendingLeaf census axioms are par_*
//! confluence lemmas blocked on the iota wall, not de Bruijn). DerivedProved,
//! zero axiom_deps -- advances the de Bruijn substitution-commutation pillar.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_expr_model_instantiate_lift_cancel_general(
        &mut self,
    ) -> Result<(), SpecError> {
        // instantiate_lift_cancel_general_bvar: the bvar case.
        //
        // Nat.rec convoy on `Nat.sub c i`:
        //   g = 0        (i >= c): lift lands `bvar (i+a)`; since c <= i and
        //                j < a, i+a > c+j, so instantiate decrements to
        //                `bvar ((i+a)-1)`; the RHS lift gives `bvar (i+(a-1))`,
        //                and (i+a)-1 = i+(a-1) since a >= 1.
        //   g = succ kk  (i < c):  both sides reduce to `bvar i` (lift below +
        //                instantiate below, the latter via c+j > i).
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_lift_cancel_general_bvar".to_string(),
            type_src: concat!(
                "forall (i : Nat) (val : KExpr) (c : Nat) (a : Nat) (j : Nat), ",
                "Eq Nat (Nat.sub a j) ",
                "(Nat.succ (Nat.sub (Nat.sub a j) (Nat.succ Nat.zero))) -> ",
                "Eq KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar i) c a) val (Nat.add c j)) ",
                "(lift_at (KExpr.bvar i) c (Nat.sub a (Nat.succ Nat.zero)))"
            )
            .to_string(),
            value_src: Some(instantiate_lift_cancel_general_bvar_value()),
            is_axiom: false,
            description: concat!(
                "bvar case of the general instantiate-after-lift cancellation: ",
                "instantiate_at (lift_at (bvar i) c a) val (c+j) = lift_at (bvar i) c (a-1) ",
                "for j < a. DerivedProved via a Nat.rec convoy on Nat.sub c i; ",
                "below case = nat_sub_pos_add_right, geq case = gap_to_add + ",
                "nat_sub_zero_add_monotone + nat_sub_pos_witness. No new axiom. ",
                "Additive de Bruijn brick (Aristotle instantiate_lift_cancel_general)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(),
                "Eq.refl".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.cong".to_string(),
                "Eq.subst".to_string(),
                "lift_at_bvar_geq".to_string(),
                "lift_at_bvar_below".to_string(),
                "instantiate_at_bvar".to_string(),
                "instantiate_bvar_at_above".to_string(),
                "instantiate_bvar_at_below".to_string(),
                "nat_sub_zero_of_sub_pos".to_string(),
                "nat_sub_zero_succ_gap_to_add".to_string(),
                "nat_succ_add".to_string(),
                "nat_sub_zero_add_right".to_string(),
                "nat_sub_zero_add_same_right".to_string(),
                "nat_add_assoc".to_string(),
                "nat_sub_pos_witness".to_string(),
                "nat_add_succ_right".to_string(),
                "nat_sub_zero_add_monotone".to_string(),
                "nat_sub_succ_one".to_string(),
                "nat_pos_witness_from_succ_eq".to_string(),
                "nat_sub_pos_add_right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Per-constructor congruence step lemmas (app/lam/pi). Each takes the two
        // child IHs (the recursor's minor-premise hypotheses) and rebuilds the
        // cancellation over the constructor: unfold the outer lift/instantiate
        // shells, apply the IHs (lam/pi transport the body depth
        // succ(c+j) = (succ c)+j via nat_succ_add), fold the lift back. Splitting
        // them out keeps each proof term independently kernel-checked.
        for (name, ctor, lift_unfold, inst_unfold, is_binder) in [
            (
                "instantiate_lift_cancel_general_app_step",
                "KExpr.app",
                "lift_at_app",
                "instantiate_at_app",
                false,
            ),
            (
                "instantiate_lift_cancel_general_lam_step",
                "KExpr.lam",
                "lift_at_lam",
                "instantiate_at_lam",
                true,
            ),
            (
                "instantiate_lift_cancel_general_pi_step",
                "KExpr.pi",
                "lift_at_pi",
                "instantiate_at_pi",
                true,
            ),
        ] {
            self.add_definition_structural(SpecDefinition {
                name: name.to_string(),
                type_src: binder_step_type(ctor),
                value_src: Some(binder_two_arm(ctor, lift_unfold, inst_unfold, is_binder)),
                is_axiom: false,
                description: format!(
                    "Congruence step of instantiate_lift_cancel_general for {ctor}: rebuilds the \
                     cancellation over the constructor from the two child IHs. DerivedProved; no new axiom."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.subst".to_string(),
                    lift_unfold.to_string(),
                    inst_unfold.to_string(),
                    "nat_succ_add".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // let_ congruence step: three children (ty/val at cutoff, body at succ
        // cutoff). The let_ analogue of the app/lam/pi steps above; registered
        // separately because the let_ constructor carries three child IHs.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_lift_cancel_general_let_step".to_string(),
            type_src: binder_step_type_let(),
            value_src: Some(let_three_arm()),
            is_axiom: false,
            description:
                "Congruence step of instantiate_lift_cancel_general for KExpr.let_: rebuilds \
                 the cancellation over the three-child let_ constructor (ty/val at cutoff, \
                 body at succ cutoff) from the three child IHs. DerivedProved; no new axiom."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.cong".to_string(),
                "Eq.subst".to_string(),
                "lift_at_let_".to_string(),
                "instantiate_at_let_".to_string(),
                "nat_succ_add".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // instantiate_lift_cancel_general: full-expression cancellation via
        // KExpr.rec (a,j-universalised, guard-carrying motive). sort/const are
        // leaves; bvar delegates to the helper; app/lam/pi delegate to the
        // per-constructor step lemmas above.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_lift_cancel_general".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (val : KExpr) (c : Nat) (a : Nat) (j : Nat), ",
                "Eq Nat (Nat.sub a j) ",
                "(Nat.succ (Nat.sub (Nat.sub a j) (Nat.succ Nat.zero))) -> ",
                "Eq KExpr ",
                "(instantiate_at (lift_at e c a) val (Nat.add c j)) ",
                "(lift_at e c (Nat.sub a (Nat.succ Nat.zero)))"
            )
            .to_string(),
            value_src: Some(instantiate_lift_cancel_general_value()),
            is_axiom: false,
            description: concat!(
                "General instantiate-after-lift cancellation: for j < a, ",
                "instantiate_at (lift_at e c a) val (c+j) = lift_at e c (a-1). ",
                "Clean port of the Aristotle-proven Lean lemma ",
                "(proofs/lean-aristotle/instantiate_lift_cancel_general.lean). ",
                "DerivedProved via KExpr.rec with a guard-carrying motive, bvar ",
                "delegated to instantiate_lift_cancel_general_bvar. Generalises ",
                "lift_cancel_gen (a=1,j=0) and the bvar core of inst_above_ceiling_id. ",
                "Additive de Bruijn brick; no new axiom."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(),
                "Eq.refl".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.cong".to_string(),
                "lift_at_sort".to_string(),
                "instantiate_at_sort".to_string(),
                "instantiate_lift_cancel_general_bvar".to_string(),
                "instantiate_lift_cancel_general_app_step".to_string(),
                "instantiate_lift_cancel_general_lam_step".to_string(),
                "instantiate_lift_cancel_general_pi_step".to_string(),
                "instantiate_lift_cancel_general_let_step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

/// The guard `j < a` (positivity of `Nat.sub a j`).
fn guard() -> String {
    "Eq Nat (Nat.sub a j) (Nat.succ (Nat.sub (Nat.sub a j) (Nat.succ Nat.zero)))".to_string()
}

/// Build the bvar-case proof term (Nat.rec convoy on `Nat.sub c i`).
fn instantiate_lift_cancel_general_bvar_value() -> String {
    // Atoms (Lean-syntax fragments; no braces so inline format capture is safe).
    let cj = "(Nat.add c j)";
    let ia = "(Nat.add i a)";
    let a1 = "(Nat.sub a (Nat.succ Nat.zero))";
    let gaj = "(Nat.sub (Nat.sub a j) (Nat.succ Nat.zero))"; // (a - j) - 1
    let gpj = format!("(Nat.add {gaj} j)"); // (a-j-1) + j = a - 1
    let x = format!("(Nat.add i {gpj})"); // i + (a-1)
    let iam1 = "(Nat.sub (Nat.add i a) (Nat.succ Nat.zero))"; // (i+a) - 1
    let lhs = "(instantiate_at (lift_at (KExpr.bvar i) c a) val (Nat.add c j))";
    let rhs = "(lift_at (KExpr.bvar i) c (Nat.sub a (Nat.succ Nat.zero)))";
    let g = guard();

    // -- geq witnesses (i >= c: h_ci : sub c i = 0) --
    let h_ja0 = format!("(nat_sub_zero_of_sub_pos a j {gaj} hj)"); // sub j a = 0
    let h_a_eq = format!("(nat_sub_zero_succ_gap_to_add a j {gaj} {h_ja0} hj)"); // a = (succ gaj) + j
    let h_a_eq2 = format!(
        "(Eq.trans Nat a (Nat.add (Nat.succ {gaj}) j) (Nat.succ {gpj}) {h_a_eq} (nat_succ_add {gaj} j))"
    ); // a = succ (a-1)
    let h_c_ig = format!("(nat_sub_zero_add_right c i {gaj} h_ci)"); // sub c (i+gaj) = 0
    let h_cj_iggj0 = format!("(nat_sub_zero_add_same_right c (Nat.add i {gaj}) j {h_c_ig})"); // sub (c+j) ((i+gaj)+j) = 0
    let h_assoc = format!("(nat_add_assoc i {gaj} j)"); // (i+gaj)+j = i+(gaj+j) = X
    let h_cj_x0 = format!(
        "(Eq.subst Nat (fun (z : Nat) => Eq Nat (Nat.sub {cj} z) Nat.zero) (Nat.add (Nat.add i {gaj}) j) {x} {h_assoc} {h_cj_iggj0})"
    ); // sub (c+j) X = 0
    let h_succx_cj_pos = format!("(nat_sub_pos_witness {cj} {x} {h_cj_x0})"); // sub (succ X) (c+j) > 0
    let h_ia_succx = format!(
        "(Eq.trans Nat {ia} (Nat.add i (Nat.succ {gpj})) (Nat.succ {x}) \
         (Eq.cong Nat Nat (fun (z : Nat) => Nat.add i z) a (Nat.succ {gpj}) {h_a_eq2}) \
         (nat_add_succ_right i {gpj}))"
    ); // i+a = succ X
    let h2 = format!(
        "(Eq.subst Nat \
         (fun (z : Nat) => Eq Nat (Nat.sub z {cj}) (Nat.succ (Nat.sub (Nat.sub z {cj}) (Nat.succ Nat.zero)))) \
         (Nat.succ {x}) {ia} (Eq.symm Nat {ia} (Nat.succ {x}) {h_ia_succx}) {h_succx_cj_pos})"
    ); // sub (i+a) (c+j) > 0
    let h1 = format!("(nat_sub_zero_add_monotone c i j a h_ci {h_ja0})"); // sub (c+j) (i+a) = 0

    // index equality: i+(a-1) = (i+a)-1  (both equal X)
    let h_suba1 = format!(
        "(Eq.trans Nat {a1} (Nat.sub (Nat.succ {gpj}) (Nat.succ Nat.zero)) {gpj} \
         (Eq.cong Nat Nat (fun (z : Nat) => Nat.sub z (Nat.succ Nat.zero)) a (Nat.succ {gpj}) {h_a_eq2}) \
         (nat_sub_succ_one {gpj}))"
    ); // a-1 = gpj
    let part1 = format!("(Eq.cong Nat Nat (fun (z : Nat) => Nat.add i z) {a1} {gpj} {h_suba1})"); // i+(a-1) = X
    let p3 = format!(
        "(Eq.trans Nat {iam1} (Nat.sub (Nat.succ {x}) (Nat.succ Nat.zero)) {x} \
         (Eq.cong Nat Nat (fun (z : Nat) => Nat.sub z (Nat.succ Nat.zero)) {ia} (Nat.succ {x}) {h_ia_succx}) \
         (nat_sub_succ_one {x}))"
    ); // (i+a)-1 = X
    let index_eq =
        format!("(Eq.trans Nat (Nat.add i {a1}) {x} {iam1} {part1} (Eq.symm Nat {iam1} {x} {p3}))"); // i+(a-1) = (i+a)-1

    let geq_lhs_to_bvar = format!(
        "(Eq.trans KExpr {lhs} (instantiate_at (KExpr.bvar {ia}) val {cj}) (KExpr.bvar {iam1}) \
         (Eq.cong KExpr KExpr (fun (t : KExpr) => instantiate_at t val {cj}) \
         (lift_at (KExpr.bvar i) c a) (KExpr.bvar {ia}) (lift_at_bvar_geq i c a h_ci)) \
         (Eq.trans KExpr (instantiate_at (KExpr.bvar {ia}) val {cj}) \
         (instantiate_bvar_at {ia} {cj} val) (KExpr.bvar {iam1}) \
         (instantiate_at_bvar {ia} val {cj}) \
         (instantiate_bvar_at_above {ia} {cj} val {h1} {h2})))"
    );
    let geq_bvar_to_rhs = format!(
        "(Eq.symm KExpr {rhs} (KExpr.bvar {iam1}) \
         (Eq.trans KExpr {rhs} (KExpr.bvar (Nat.add i {a1})) (KExpr.bvar {iam1}) \
         (lift_at_bvar_geq i c {a1} h_ci) \
         (Eq.cong Nat KExpr KExpr.bvar (Nat.add i {a1}) {iam1} {index_eq})))"
    );
    let geq_arm = format!(
        "(Eq.trans KExpr {lhs} (KExpr.bvar {iam1}) {rhs} {geq_lhs_to_bvar} {geq_bvar_to_rhs})"
    );

    // -- below arm (i < c: h_sk : sub c i = succ kk) --
    let h_ci_pos = "(nat_pos_witness_from_succ_eq (Nat.sub c i) kk h_sk)"; // sub c i > 0
    let below_lhs_to_bvar = format!(
        "(Eq.trans KExpr {lhs} (instantiate_at (KExpr.bvar i) val {cj}) (KExpr.bvar i) \
         (Eq.cong KExpr KExpr (fun (t : KExpr) => instantiate_at t val {cj}) \
         (lift_at (KExpr.bvar i) c a) (KExpr.bvar i) (lift_at_bvar_below i c a {h_ci_pos})) \
         (Eq.trans KExpr (instantiate_at (KExpr.bvar i) val {cj}) \
         (instantiate_bvar_at i {cj} val) (KExpr.bvar i) \
         (instantiate_at_bvar i val {cj}) \
         (instantiate_bvar_at_below i {cj} val (nat_sub_pos_add_right c j i {h_ci_pos}))))"
    );
    let below_bvar_to_rhs =
        format!("(Eq.symm KExpr {rhs} (KExpr.bvar i) (lift_at_bvar_below i c {a1} {h_ci_pos}))");
    let below_arm = format!(
        "(Eq.trans KExpr {lhs} (KExpr.bvar i) {rhs} {below_lhs_to_bvar} {below_bvar_to_rhs})"
    );

    format!(
        "fun (i : Nat) (val : KExpr) (c : Nat) (a : Nat) (j : Nat) (hj : {g}) => \
         Nat.rec (fun (gg : Nat) => Eq Nat (Nat.sub c i) gg -> Eq KExpr {lhs} {rhs}) \
         (fun (h_ci : Eq Nat (Nat.sub c i) Nat.zero) => {geq_arm}) \
         (fun (kk : Nat) (ihk : Eq Nat (Nat.sub c i) kk -> Eq KExpr {lhs} {rhs}) \
         (h_sk : Eq Nat (Nat.sub c i) (Nat.succ kk)) => {below_arm}) \
         (Nat.sub c i) (Eq.refl Nat (Nat.sub c i))"
    )
}

/// Build the app/lam/pi branch of the main KExpr.rec proof. `ctor`
/// (`KExpr.app`/`KExpr.lam`/`KExpr.pi`), `lift_unfold`, `inst_unfold`, and
/// whether the second (body) argument recurses under a binder (`succ c`). For
/// app both args recurse at the same depth; for lam/pi the body arg recurses at
/// `succ c` with a depth transport succ(c+j) = (succ c)+j.
fn binder_two_arm(ctor: &str, lift_unfold: &str, inst_unfold: &str, is_binder: bool) -> String {
    let g = guard();
    // First recursive child is `ty0`, second is `bd0`. (Single-letter binder
    // names like `q` trip an elaborator name-resolution edge case here.)
    let x2_lifted = if is_binder {
        "(lift_at bd0 (Nat.succ c) a)".to_string()
    } else {
        "(lift_at bd0 c a)".to_string()
    };
    let x2_lifted_res = if is_binder {
        "(lift_at bd0 (Nat.succ c) (Nat.sub a (Nat.succ Nat.zero)))".to_string()
    } else {
        "(lift_at bd0 c (Nat.sub a (Nat.succ Nat.zero)))".to_string()
    };
    let x2_inst = if is_binder {
        format!("(instantiate_at {x2_lifted} w (Nat.succ (Nat.add c j)))")
    } else {
        format!("(instantiate_at {x2_lifted} w (Nat.add c j))")
    };
    // Proof that the second child instantiation equals its lifted result. For a
    // binder the body IH is at cutoff (succ c) with depth (succ c)+j, while the
    // instantiate_at unfolding produced depth succ(c+j); transport the IH along
    // nat_succ_add: (succ c)+j = succ(c+j).
    let x2_body_eq = if is_binder {
        format!(
            "(Eq.subst Nat \
             (fun (dd : Nat) => Eq KExpr (instantiate_at {x2_lifted} w dd) {x2_lifted_res}) \
             (Nat.add (Nat.succ c) j) (Nat.succ (Nat.add c j)) (nat_succ_add c j) \
             (ih_bd w (Nat.succ c) a j hj))"
        )
    } else {
        "(ih_bd w c a j hj)".to_string()
    };

    let lhs = format!("(instantiate_at (lift_at ({ctor} ty0 bd0) c a) w (Nat.add c j))");
    let rhs = format!("(lift_at ({ctor} ty0 bd0) c (Nat.sub a (Nat.succ Nat.zero)))");
    let unfolded_lift = format!("({ctor} (lift_at ty0 c a) {x2_lifted})");
    let mid = format!("({ctor} (instantiate_at (lift_at ty0 c a) w (Nat.add c j)) {x2_inst})");
    let res = format!("({ctor} (lift_at ty0 c (Nat.sub a (Nat.succ Nat.zero))) {x2_lifted_res})");

    // step LHS -> mid : unfold lift then instantiate on the constructor.
    let lhs_to_mid = format!(
        "(Eq.trans KExpr {lhs} (instantiate_at {unfolded_lift} w (Nat.add c j)) {mid} \
         (Eq.cong KExpr KExpr (fun (t : KExpr) => instantiate_at t w (Nat.add c j)) \
         (lift_at ({ctor} ty0 bd0) c a) {unfolded_lift} ({lift_unfold} ty0 bd0 c a)) \
         ({inst_unfold} (lift_at ty0 c a) {x2_lifted} w (Nat.add c j)))"
    );
    // step mid -> res : apply the two IHs (congruence on each slot).
    let mid_to_res = format!(
        "(Eq.trans KExpr {mid} \
         ({ctor} (lift_at ty0 c (Nat.sub a (Nat.succ Nat.zero))) {x2_inst}) {res} \
         (Eq.cong KExpr KExpr (fun (t : KExpr) => {ctor} t {x2_inst}) \
         (instantiate_at (lift_at ty0 c a) w (Nat.add c j)) \
         (lift_at ty0 c (Nat.sub a (Nat.succ Nat.zero))) (ih_ty w c a j hj)) \
         (Eq.cong KExpr KExpr \
         (fun (t : KExpr) => {ctor} (lift_at ty0 c (Nat.sub a (Nat.succ Nat.zero))) t) \
         {x2_inst} {x2_lifted_res} {x2_body_eq}))"
    );
    // step res -> RHS : fold the lift back over the constructor.
    let res_to_rhs = format!(
        "(Eq.symm KExpr {rhs} {res} ({lift_unfold} ty0 bd0 c (Nat.sub a (Nat.succ Nat.zero))))"
    );

    format!(
        "(fun (ty0 : KExpr) (bd0 : KExpr) {} \
         (w : KExpr) (c : Nat) (a : Nat) (j : Nat) (hj : {g}) => \
         Eq.trans KExpr {lhs} {mid} {rhs} {lhs_to_mid} \
         (Eq.trans KExpr {mid} {res} {rhs} {mid_to_res} {res_to_rhs}))",
        ih_hyps()
    )
}

/// The child-IH hypotheses shared by every constructor step lemma (bound as
/// `ih_ty` / `ih_bd` over children `ty0` / `bd0`).
fn ih_hyps() -> String {
    let g = guard();
    format!(
        "(ih_ty : forall (w : KExpr) (c : Nat) (a : Nat) (j : Nat), {g} -> \
         Eq KExpr (instantiate_at (lift_at ty0 c a) w (Nat.add c j)) \
         (lift_at ty0 c (Nat.sub a (Nat.succ Nat.zero)))) \
         (ih_bd : forall (w : KExpr) (c : Nat) (a : Nat) (j : Nat), {g} -> \
         Eq KExpr (instantiate_at (lift_at bd0 c a) w (Nat.add c j)) \
         (lift_at bd0 c (Nat.sub a (Nat.succ Nat.zero))))"
    )
}

/// Type of a per-constructor step lemma (matches the recursor minor premise).
fn binder_step_type(ctor: &str) -> String {
    let g = guard();
    let hyps = ih_hyps();
    format!(
        "forall (ty0 : KExpr) (bd0 : KExpr) {hyps} \
         (w : KExpr) (c : Nat) (a : Nat) (j : Nat), {g} -> \
         Eq KExpr (instantiate_at (lift_at ({ctor} ty0 bd0) c a) w (Nat.add c j)) \
         (lift_at ({ctor} ty0 bd0) c (Nat.sub a (Nat.succ Nat.zero)))"
    )
}

/// KExpr.rec branch that delegates to a per-constructor step lemma.
fn binder_step_call(step_name: &str) -> String {
    let g = guard();
    let hyps = ih_hyps();
    format!(
        "(fun (ty0 : KExpr) (bd0 : KExpr) {hyps} \
         (w : KExpr) (c : Nat) (a : Nat) (j : Nat) (hj : {g}) => \
         {step_name} ty0 bd0 ih_ty ih_bd w c a j hj)"
    )
}

/// The three child-IH hypotheses for the let_ step lemma (children `ty0` /
/// `val0` / `bd0`; the recursor motive is applied to each child). All three IHs
/// are at cutoff — the body `bd0` binder step is handled inside the arm.
fn ih_hyps_let() -> String {
    let g = guard();
    format!(
        "(ih_ty : forall (w : KExpr) (c : Nat) (a : Nat) (j : Nat), {g} -> \
         Eq KExpr (instantiate_at (lift_at ty0 c a) w (Nat.add c j)) \
         (lift_at ty0 c (Nat.sub a (Nat.succ Nat.zero)))) \
         (ih_val : forall (w : KExpr) (c : Nat) (a : Nat) (j : Nat), {g} -> \
         Eq KExpr (instantiate_at (lift_at val0 c a) w (Nat.add c j)) \
         (lift_at val0 c (Nat.sub a (Nat.succ Nat.zero)))) \
         (ih_bd : forall (w : KExpr) (c : Nat) (a : Nat) (j : Nat), {g} -> \
         Eq KExpr (instantiate_at (lift_at bd0 c a) w (Nat.add c j)) \
         (lift_at bd0 c (Nat.sub a (Nat.succ Nat.zero))))"
    )
}

/// Type of the let_ step lemma (matches the recursor's let_ minor premise:
/// three child IHs, then the universalised guard-carrying conclusion).
fn binder_step_type_let() -> String {
    let g = guard();
    let hyps = ih_hyps_let();
    format!(
        "forall (ty0 : KExpr) (val0 : KExpr) (bd0 : KExpr) {hyps} \
         (w : KExpr) (c : Nat) (a : Nat) (j : Nat), {g} -> \
         Eq KExpr (instantiate_at (lift_at (KExpr.let_ ty0 val0 bd0) c a) w (Nat.add c j)) \
         (lift_at (KExpr.let_ ty0 val0 bd0) c (Nat.sub a (Nat.succ Nat.zero)))"
    )
}

/// Build the KExpr.let_ branch proof (three children: `ty0`/`val0` at cutoff
/// `c`, the body `bd0` at succ `c`). Mirrors `binder_two_arm` with an extra
/// middle (val) congruence leg; the body child transports its IH depth
/// (succ c)+j = succ(c+j) via nat_succ_add exactly as the lam/pi body does.
fn let_three_arm() -> String {
    let g = guard();
    let l_ty = "(lift_at ty0 c a)";
    let l_val = "(lift_at val0 c a)";
    let l_bd = "(lift_at bd0 (Nat.succ c) a)";
    let l_ty_res = "(lift_at ty0 c (Nat.sub a (Nat.succ Nat.zero)))";
    let l_val_res = "(lift_at val0 c (Nat.sub a (Nat.succ Nat.zero)))";
    let l_bd_res = "(lift_at bd0 (Nat.succ c) (Nat.sub a (Nat.succ Nat.zero)))";
    let i_ty = "(instantiate_at (lift_at ty0 c a) w (Nat.add c j))";
    let i_val = "(instantiate_at (lift_at val0 c a) w (Nat.add c j))";
    let i_bd = "(instantiate_at (lift_at bd0 (Nat.succ c) a) w (Nat.succ (Nat.add c j)))";
    let lhs = "(instantiate_at (lift_at (KExpr.let_ ty0 val0 bd0) c a) w (Nat.add c j))";
    let rhs = "(lift_at (KExpr.let_ ty0 val0 bd0) c (Nat.sub a (Nat.succ Nat.zero)))";
    let unfolded_lift = format!("(KExpr.let_ {l_ty} {l_val} {l_bd})");
    let mid = format!("(KExpr.let_ {i_ty} {i_val} {i_bd})");
    let res = format!("(KExpr.let_ {l_ty_res} {l_val_res} {l_bd_res})");
    let m1 = format!("(KExpr.let_ {l_ty_res} {i_val} {i_bd})");
    let m2 = format!("(KExpr.let_ {l_ty_res} {l_val_res} {i_bd})");
    // body IH transported from (succ c)+j to succ(c+j) via nat_succ_add.
    let bd_body_eq = format!(
        "(Eq.subst Nat \
         (fun (dd : Nat) => Eq KExpr (instantiate_at {l_bd} w dd) {l_bd_res}) \
         (Nat.add (Nat.succ c) j) (Nat.succ (Nat.add c j)) (nat_succ_add c j) \
         (ih_bd w (Nat.succ c) a j hj))"
    );
    // LHS -> mid: unfold lift then instantiate over the constructor.
    let lhs_to_mid = format!(
        "(Eq.trans KExpr {lhs} (instantiate_at {unfolded_lift} w (Nat.add c j)) {mid} \
         (Eq.cong KExpr KExpr (fun (t : KExpr) => instantiate_at t w (Nat.add c j)) \
         (lift_at (KExpr.let_ ty0 val0 bd0) c a) {unfolded_lift} (lift_at_let_ ty0 val0 bd0 c a)) \
         (instantiate_at_let_ {l_ty} {l_val} {l_bd} w (Nat.add c j)))"
    );
    // mid -> res: three congruences (ty, val, then transported body).
    let cong_ty = format!(
        "(Eq.cong KExpr KExpr (fun (t : KExpr) => KExpr.let_ t {i_val} {i_bd}) \
         {i_ty} {l_ty_res} (ih_ty w c a j hj))"
    );
    let cong_val = format!(
        "(Eq.cong KExpr KExpr (fun (t : KExpr) => KExpr.let_ {l_ty_res} t {i_bd}) \
         {i_val} {l_val_res} (ih_val w c a j hj))"
    );
    let cong_bd = format!(
        "(Eq.cong KExpr KExpr (fun (t : KExpr) => KExpr.let_ {l_ty_res} {l_val_res} t) \
         {i_bd} {l_bd_res} {bd_body_eq})"
    );
    let mid_to_res = format!(
        "(Eq.trans KExpr {mid} {m1} {res} {cong_ty} \
         (Eq.trans KExpr {m1} {m2} {res} {cong_val} {cong_bd}))"
    );
    // res -> RHS: fold the lift back over the constructor.
    let res_to_rhs = format!(
        "(Eq.symm KExpr {rhs} {res} \
         (lift_at_let_ ty0 val0 bd0 c (Nat.sub a (Nat.succ Nat.zero))))"
    );
    format!(
        "(fun (ty0 : KExpr) (val0 : KExpr) (bd0 : KExpr) {} \
         (w : KExpr) (c : Nat) (a : Nat) (j : Nat) (hj : {g}) => \
         Eq.trans KExpr {lhs} {mid} {rhs} {lhs_to_mid} \
         (Eq.trans KExpr {mid} {res} {rhs} {mid_to_res} {res_to_rhs}))",
        ih_hyps_let()
    )
}

/// KExpr.let_ recursor branch that delegates to the three-child step lemma.
fn let_step_call(step_name: &str) -> String {
    let g = guard();
    let hyps = ih_hyps_let();
    format!(
        "(fun (ty0 : KExpr) (val0 : KExpr) (bd0 : KExpr) {hyps} \
         (w : KExpr) (c : Nat) (a : Nat) (j : Nat) (hj : {g}) => \
         {step_name} ty0 val0 bd0 ih_ty ih_val ih_bd w c a j hj)"
    )
}

/// Build the full-expression proof term (KExpr.rec).
fn instantiate_lift_cancel_general_value() -> String {
    let g = guard();
    let motive = format!(
        "(fun (xe : KExpr) => forall (w : KExpr) (c : Nat) (a : Nat) (j : Nat), {g} -> \
         Eq KExpr (instantiate_at (lift_at xe c a) w (Nat.add c j)) \
         (lift_at xe c (Nat.sub a (Nat.succ Nat.zero))))"
    );

    // sort branch: both sides reduce to (sort n) via lift_at_sort / instantiate_at_sort.
    let sort_branch = format!(
        "(fun (n : Level) (w : KExpr) (c : Nat) (a : Nat) (j : Nat) (hj : {g}) => \
         Eq.trans KExpr \
         (instantiate_at (lift_at (KExpr.sort n) c a) w (Nat.add c j)) \
         (KExpr.sort n) \
         (lift_at (KExpr.sort n) c (Nat.sub a (Nat.succ Nat.zero))) \
         (Eq.trans KExpr \
         (instantiate_at (lift_at (KExpr.sort n) c a) w (Nat.add c j)) \
         (instantiate_at (KExpr.sort n) w (Nat.add c j)) (KExpr.sort n) \
         (Eq.cong KExpr KExpr (fun (t : KExpr) => instantiate_at t w (Nat.add c j)) \
         (lift_at (KExpr.sort n) c a) (KExpr.sort n) (lift_at_sort n c a)) \
         (instantiate_at_sort n w (Nat.add c j))) \
         (Eq.symm KExpr (lift_at (KExpr.sort n) c (Nat.sub a (Nat.succ Nat.zero))) (KExpr.sort n) \
         (lift_at_sort n c (Nat.sub a (Nat.succ Nat.zero)))))"
    );

    let bvar_branch = format!(
        "(fun (i : Nat) (w : KExpr) (c : Nat) (a : Nat) (j : Nat) (hj : {g}) => \
         instantiate_lift_cancel_general_bvar i w c a j hj)"
    );

    let app_branch = binder_step_call("instantiate_lift_cancel_general_app_step");
    let lam_branch = binder_step_call("instantiate_lift_cancel_general_lam_step");
    let pi_branch = binder_step_call("instantiate_lift_cancel_general_pi_step");
    let let_branch = let_step_call("instantiate_lift_cancel_general_let_step");

    let const_branch = format!(
        "(fun (nm : Name) (us : ListType Level) (w : KExpr) (c : Nat) (a : Nat) (j : Nat) (hj : {g}) => \
         Eq.refl KExpr (KExpr.const nm us))"
    );

    // proj: 1-child node; instantiate_at + lift_at reduce through proj, ih_sub cong.
    let proj_branch = format!(
        "(fun (s : Name) (i : Nat) (sub : KExpr) \
         (ih_sub : forall (w : KExpr) (c : Nat) (a : Nat) (j : Nat), {g} -> \
         Eq KExpr (instantiate_at (lift_at sub c a) w (Nat.add c j)) (lift_at sub c (Nat.sub a (Nat.succ Nat.zero)))) \
         (w : KExpr) (c : Nat) (a : Nat) (j : Nat) (hj : {g}) => \
         Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.proj s i x) \
         (instantiate_at (lift_at sub c a) w (Nat.add c j)) \
         (lift_at sub c (Nat.sub a (Nat.succ Nat.zero))) (ih_sub w c a j hj))"
    );
    // lit: leaf; both sides reduce to (lit m).
    let lit_branch = format!(
        "(fun (m : Nat) (w : KExpr) (c : Nat) (a : Nat) (j : Nat) (hj : {g}) => \
         Eq.refl KExpr (KExpr.lit m))"
    );

    format!(
        "fun (e : KExpr) (val : KExpr) (c : Nat) (a : Nat) (j : Nat) (hj : {g}) => \
         KExpr.rec {motive} {sort_branch} {bvar_branch} {app_branch} {lam_branch} {pi_branch} \
         {const_branch} {let_branch} {proj_branch} {lit_branch} e val c a j hj"
    )
}

#[cfg(test)]
mod tests {
    use crate::spec::types::ProofStatus;
    use crate::test_utils::build_spec_with_stack;

    #[test]
    fn test_instantiate_lift_cancel_general_is_constructive() {
        let spec = build_spec_with_stack();

        for name in [
            "instantiate_lift_cancel_general_bvar",
            "instantiate_lift_cancel_general_app_step",
            "instantiate_lift_cancel_general_lam_step",
            "instantiate_lift_cancel_general_pi_step",
            "instantiate_lift_cancel_general_let_step",
            "instantiate_lift_cancel_general",
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
    }
}
