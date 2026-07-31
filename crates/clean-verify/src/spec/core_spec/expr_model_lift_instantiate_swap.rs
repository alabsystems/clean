// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Lift/substitution interchange (gap form): the load-bearing lemma for the
//! iota-free Tait/Martin-Löf confluence skeleton (Route B, #2859).
//!
//! Statement (Wave 128 gap form — verified true over compound terms):
//!   lift_at (instantiate_at body val d) (d+k) a
//!     = instantiate_at (lift_at body (succ(d+k)) a) (lift_at val k a) d
//!
//! Contains:
//!   - lift_instantiate_swap_bvar: the bvar case, a 4-leaf triple-Nat.rec convoy
//!     on sub(i,d) / sub(d,i) / sub(succ(d+k),i).
//!   - lift_instantiate_swap: the full KExpr.rec proof, delegating the bvar case
//!     to lift_instantiate_swap_bvar and mirroring subst_lift_interchange_gen's
//!     app/lam/pi arms (adapted to the gap-form conclusion).
//!
//! At d = 0 (via nat_zero_add) this specializes to exactly the shape par_lift_bd
//! needs in its beta/let_ contraction arms. No iota arm (KExpr has no recursor
//! node); empty axiom_deps.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_expr_model_lift_instantiate_swap(&mut self) -> Result<(), SpecError> {
        self.add_lift_instantiate_swap_bvar()?;
        self.add_lift_instantiate_swap()?;
        Ok(())
    }

    fn add_lift_instantiate_swap_bvar(&mut self) -> Result<(), SpecError> {
        self.add_definition_structural(SpecDefinition {
            name: "lift_instantiate_swap_bvar".to_string(),
            type_src: concat!(
                "forall (i : Nat) (val : KExpr) (d : Nat) (k : Nat) (a : Nat), ",
                "Eq KExpr ",
                "(lift_at (instantiate_at (KExpr.bvar i) val d) (Nat.add d k) a) ",
                "(instantiate_at (lift_at (KExpr.bvar i) (Nat.succ (Nat.add d k)) a) ",
                "(lift_at val k a) d)",
            )
            .to_string(),
            value_src: Some(bvar_proof()),
            is_axiom: false,
            description: concat!(
                "bvar case of lift_instantiate_swap (gap form). DerivedProved via a ",
                "4-leaf triple-Nat.rec convoy on sub(i,d) / sub(d,i) / sub(succ(d+k),i): ",
                "i<d and i>d-below leaves land bvar i / bvar(i-1) on both sides; the ",
                "i=d leaf bridges lift(lift val 0 d)(d+k)a = lift(lift val k a)0 d via ",
                "lift_at_lift_at_exchange (Wave 127); the i>=succ(d+k) leaf lands ",
                "bvar((i-1)+a) via nat_pred_add_at_pos. No new axiom. ",
                "Part of #2859 Wave 129 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.refl".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "Nat.rec".to_string(),
                "instantiate_at_bvar".to_string(),
                "instantiate_at_bvar_eq_from_zero_witnesses".to_string(),
                "instantiate_bvar_at_above".to_string(),
                "instantiate_bvar_at_below".to_string(),
                "lift_at_bvar_below".to_string(),
                "lift_at_bvar_geq".to_string(),
                "lift_at_lift_at_exchange".to_string(),
                "nat_pos_witness_from_succ_eq".to_string(),
                "nat_pred_add_at_pos".to_string(),
                "nat_sub_pos_add_right".to_string(),
                "nat_sub_pos_pred_of_succ_add_pos".to_string(),
                "nat_sub_pos_succ_add_witness".to_string(),
                "nat_sub_zero_of_sub_pos".to_string(),
                "nat_sub_zero_pred_of_succ_add_zero".to_string(),
                "nat_zero_add".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    fn add_lift_instantiate_swap(&mut self) -> Result<(), SpecError> {
        self.add_definition_structural(SpecDefinition {
            name: "lift_instantiate_swap".to_string(),
            type_src: concat!(
                "forall (body : KExpr) (val : KExpr) (d : Nat) (k : Nat) (a : Nat), ",
                "Eq KExpr ",
                "(lift_at (instantiate_at body val d) (Nat.add d k) a) ",
                "(instantiate_at (lift_at body (Nat.succ (Nat.add d k)) a) ",
                "(lift_at val k a) d)",
            )
            .to_string(),
            value_src: Some(full_proof()),
            is_axiom: false,
            description: concat!(
                "Lift/substitution interchange (gap form): lifting at cutoff (d+k) ",
                "commutes with a depth-d substitution, with the value lifted at the ",
                "GAP cutoff k. DerivedProved via KExpr.rec on body — sort/const by ",
                "Eq.refl, bvar by lift_instantiate_swap_bvar, app/lam/pi by the ",
                "subst_lift_interchange_gen template adapted to the gap-form ",
                "conclusion. At d=0 specializes to exactly what par_lift_bd needs. ",
                "No iota arm, no new axiom. Part of #2859 Wave 129 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.refl".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "KExpr.rec".to_string(),
                "instantiate_at_app".to_string(),
                "instantiate_at_lam".to_string(),
                "instantiate_at_pi".to_string(),
                "instantiate_at_let_".to_string(),
                "lift_at_app".to_string(),
                "lift_at_lam".to_string(),
                "lift_at_pi".to_string(),
                "lift_at_let_".to_string(),
                "lift_instantiate_swap_bvar".to_string(),
                "nat_succ_add".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }
}

// ===================================================================
// bvar case: 4-leaf triple-Nat.rec convoy.
// ===================================================================

/// LHS of the goal.
const LHS: &str = "(lift_at (instantiate_at (KExpr.bvar i) val d) (Nat.add d k) a)";
/// RHS of the goal.
const RHS: &str = concat!(
    "(instantiate_at (lift_at (KExpr.bvar i) (Nat.succ (Nat.add d k)) a) ",
    "(lift_at val k a) d)"
);

/// sub(d,i) positivity-witness, from `h_di : sub(d,i) = succ k2`.
const W_DI: &str = "(nat_pos_witness_from_succ_eq (Nat.sub d i) k2 h_di)";
/// sub(i,d) positivity-witness, from `h_id : sub(i,d) = succ k4`.
const W_ID: &str = "(nat_pos_witness_from_succ_eq (Nat.sub i d) k4 h_id)";

fn bvar_proof() -> String {
    format!(
        concat!(
            "fun (i : Nat) (val : KExpr) (d : Nat) (k : Nat) (a : Nat) => ",
            // ===== OUTER Nat.rec on sub(i, d) =====
            "Nat.rec ",
            "(fun (g : Nat) => Eq Nat (Nat.sub i d) g -> Eq KExpr {lhs} {rhs}) ",
            // ----- OUTER ZERO: sub(i,d) = 0 (i <= d) -----
            "(fun (h_id : Eq Nat (Nat.sub i d) Nat.zero) => ",
            // MIDDLE Nat.rec on sub(d, i)
            "Nat.rec ",
            "(fun (g2 : Nat) => Eq Nat (Nat.sub d i) g2 -> Eq KExpr {lhs} {rhs}) ",
            // --- MIDDLE ZERO: sub(d,i) = 0 (i = d) : LEAF 2 ---
            "(fun (h_di0 : Eq Nat (Nat.sub d i) Nat.zero) => {leaf2}) ",
            // --- MIDDLE SUCC: sub(d,i) = succ k2 (i < d) : LEAF 1 ---
            "(fun (k2 : Nat) ",
            "(_ : Eq Nat (Nat.sub d i) k2 -> Eq KExpr {lhs} {rhs}) ",
            "(h_di : Eq Nat (Nat.sub d i) (Nat.succ k2)) => {leaf1}) ",
            "(Nat.sub d i) (Eq.refl Nat (Nat.sub d i))) ",
            // ----- OUTER SUCC: sub(i,d) = succ k4 (i > d) -----
            "(fun (k4 : Nat) ",
            "(_ : Eq Nat (Nat.sub i d) k4 -> Eq KExpr {lhs} {rhs}) ",
            "(h_id : Eq Nat (Nat.sub i d) (Nat.succ k4)) => ",
            // INNER Nat.rec on sub(succ(d+k), i)
            "Nat.rec ",
            "(fun (g3 : Nat) => Eq Nat (Nat.sub (Nat.succ (Nat.add d k)) i) g3 -> ",
            "Eq KExpr {lhs} {rhs}) ",
            // --- INNER ZERO: sub(succ(d+k),i) = 0 (i >= succ(d+k)) : LEAF 3 ---
            "(fun (h_s0 : Eq Nat (Nat.sub (Nat.succ (Nat.add d k)) i) Nat.zero) => {leaf3}) ",
            // --- INNER SUCC: sub(succ(d+k),i) = succ k6 (i < succ(d+k)) : LEAF 4 ---
            "(fun (k6 : Nat) ",
            "(_ : Eq Nat (Nat.sub (Nat.succ (Nat.add d k)) i) k6 -> Eq KExpr {lhs} {rhs}) ",
            "(h_s : Eq Nat (Nat.sub (Nat.succ (Nat.add d k)) i) (Nat.succ k6)) => {leaf4}) ",
            "(Nat.sub (Nat.succ (Nat.add d k)) i) ",
            "(Eq.refl Nat (Nat.sub (Nat.succ (Nat.add d k)) i))) ",
            // apply outer to the discriminant + refl
            "(Nat.sub i d) (Eq.refl Nat (Nat.sub i d))",
        ),
        lhs = LHS,
        rhs = RHS,
        leaf1 = leaf1(),
        leaf2 = leaf2(),
        leaf3 = leaf3(),
        leaf4 = leaf4(),
    )
}

/// LEAF 1 (i < d): both sides reduce to `KExpr.bvar i`.
/// Witnesses available: h_di : sub(d,i)=succ k2 ; h_id : sub(i,d)=0.
fn leaf1() -> String {
    // W_dki : sub(d+k,i) positive (from W_DI via nat_sub_pos_add_right d k i).
    let w_dki = format!("(nat_sub_pos_add_right d k i {w_di})", w_di = W_DI);
    // W_sdki : sub(succ(d+k),i) positive (from h_id via nat_sub_pos_succ_add_witness).
    let w_sdki = "(nat_sub_pos_succ_add_witness i d k h_id)";
    // LHS = bvar i :
    //   lift_at (instantiate_at (bvar i) val d) (d+k) a
    //   = lift_at (bvar i) (d+k) a              [cong (inst (bvar i) val d = bvar i)]
    //   = bvar i                                [lift_at_bvar_below]
    let lhs_to_bvar = format!(
        concat!(
            "(Eq.trans KExpr {lhs} ",
            "(lift_at (KExpr.bvar i) (Nat.add d k) a) ",
            "(KExpr.bvar i) ",
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => lift_at x (Nat.add d k) a) ",
            "(instantiate_at (KExpr.bvar i) val d) (KExpr.bvar i) ",
            "(Eq.trans KExpr (instantiate_at (KExpr.bvar i) val d) ",
            "(instantiate_bvar_at i d val) (KExpr.bvar i) ",
            "(instantiate_at_bvar i val d) ",
            "(instantiate_bvar_at_below i d val {w_di}))) ",
            "(lift_at_bvar_below i (Nat.add d k) a {w_dki}))"
        ),
        lhs = LHS,
        w_di = W_DI,
        w_dki = w_dki,
    );
    // RHS = bvar i :
    //   instantiate_at (lift_at (bvar i) (succ(d+k)) a) (lift val k a) d
    //   = instantiate_at (bvar i) (lift val k a) d   [cong (lift (bvar i) .. = bvar i)]
    //   = bvar i                                     [inst_bvar / below]
    let rhs_to_bvar = format!(
        concat!(
            "(Eq.trans KExpr {rhs} ",
            "(instantiate_at (KExpr.bvar i) (lift_at val k a) d) ",
            "(KExpr.bvar i) ",
            "(Eq.cong KExpr KExpr ",
            "(fun (x : KExpr) => instantiate_at x (lift_at val k a) d) ",
            "(lift_at (KExpr.bvar i) (Nat.succ (Nat.add d k)) a) (KExpr.bvar i) ",
            "(lift_at_bvar_below i (Nat.succ (Nat.add d k)) a {w_sdki})) ",
            "(Eq.trans KExpr (instantiate_at (KExpr.bvar i) (lift_at val k a) d) ",
            "(instantiate_bvar_at i d (lift_at val k a)) (KExpr.bvar i) ",
            "(instantiate_at_bvar i (lift_at val k a) d) ",
            "(instantiate_bvar_at_below i d (lift_at val k a) {w_di})))"
        ),
        rhs = RHS,
        w_sdki = w_sdki,
        w_di = W_DI,
    );
    format!(
        "Eq.trans KExpr {lhs} (KExpr.bvar i) {rhs} {l} (Eq.symm KExpr {rhs} (KExpr.bvar i) {r})",
        lhs = LHS,
        rhs = RHS,
        l = lhs_to_bvar,
        r = rhs_to_bvar,
    )
}

/// LEAF 2 (i = d): bridge via lift_at_lift_at_exchange.
/// Witnesses: h_id : sub(i,d)=0 ; h_di0 : sub(d,i)=0.
fn leaf2() -> String {
    // W_sdki : sub(succ(d+k),i) positive (from h_id via helper #1).
    let w_sdki = "(nat_sub_pos_succ_add_witness i d k h_id)";
    // LHS = lift_at (lift_at val 0 d) (d+k) a :
    //   lift_at (instantiate_at (bvar i) val d) (d+k) a
    //   = lift_at (lift_at val 0 d) (d+k) a   [cong (inst eq from zero witnesses)]
    let lhs_form = concat!(
        "(Eq.cong KExpr KExpr (fun (x : KExpr) => lift_at x (Nat.add d k) a) ",
        "(instantiate_at (KExpr.bvar i) val d) ",
        "(lift_at val Nat.zero d) ",
        "(instantiate_at_bvar_eq_from_zero_witnesses i d val h_di0 h_id))"
    );
    // RHS = lift_at (lift_at val k a) 0 d :
    //   instantiate_at (lift_at (bvar i) (succ(d+k)) a) (lift val k a) d
    //   = instantiate_at (bvar i) (lift val k a) d     [cong (lift below = bvar i)]
    //   = lift_at (lift_at val k a) 0 d                [inst eq from zero witnesses]
    let rhs_form = format!(
        concat!(
            "(Eq.trans KExpr {rhs} ",
            "(instantiate_at (KExpr.bvar i) (lift_at val k a) d) ",
            "(lift_at (lift_at val k a) Nat.zero d) ",
            "(Eq.cong KExpr KExpr ",
            "(fun (x : KExpr) => instantiate_at x (lift_at val k a) d) ",
            "(lift_at (KExpr.bvar i) (Nat.succ (Nat.add d k)) a) (KExpr.bvar i) ",
            "(lift_at_bvar_below i (Nat.succ (Nat.add d k)) a {w_sdki})) ",
            "(instantiate_at_bvar_eq_from_zero_witnesses i d (lift_at val k a) h_di0 h_id))"
        ),
        rhs = RHS,
        w_sdki = w_sdki,
    );
    // BRIDGE: lift_at (lift_at val 0 d) (d+k) a = lift_at (lift_at val k a) 0 d.
    //
    // lift_at_lift_at_exchange val c k a d :
    //   lift(lift(val, c+k, a), c, d) = lift(lift(val, c, d), c+(d+k), a)
    // Instantiate c=0:
    //   lift(lift(val, 0+k, a), 0, d) = lift(lift(val, 0, d), 0+(d+k), a)
    // We need: lift(lift(val,0,d),(d+k),a) = lift(lift(val,k,a),0,d).
    // That is the Eq.symm of the exchange instance, after rewriting
    //   0+k -> k          (nat_zero_add k)        in the LHS of the exchange, and
    //   0+(d+k) -> (d+k)  (nat_zero_add (d+k))    in the RHS of the exchange.
    //
    // Build EX = exchange instance at c=0, then transport both occurrences, then symm.
    //
    // ex0 : lift(lift(val,(0+k),a),0,d) = lift(lift(val,0,d),(0+(d+k)),a)
    // step1: rewrite (0+k)->k on the exchange LHS, giving
    //        lift(lift(val,k,a),0,d) = lift(lift(val,0,d),(0+(d+k)),a)
    // step2: rewrite (0+(d+k))->(d+k) on the RHS, giving
    //        lift(lift(val,k,a),0,d) = lift(lift(val,0,d),(d+k),a)
    // then Eq.symm yields lift(lift(val,0,d),(d+k),a) = lift(lift(val,k,a),0,d).
    let bridge = concat!(
        // we construct  E : lift(lift(val,k,a),0,d) = lift(lift(val,0,d),(d+k),a)
        // and return Eq.symm E : lift(lift(val,0,d),(d+k),a) = lift(lift(val,k,a),0,d).
        // Eq.symm KExpr A B (E : Eq A B) : Eq B A, with A=MID2, B=MID1.
        "(Eq.symm KExpr ",
        "(lift_at (lift_at val k a) Nat.zero d) ",
        "(lift_at (lift_at val Nat.zero d) (Nat.add d k) a) ",
        // E:
        "(Eq.trans KExpr ",
        "(lift_at (lift_at val k a) Nat.zero d) ",
        "(lift_at (lift_at val Nat.zero d) (Nat.add Nat.zero (Nat.add d k)) a) ",
        "(lift_at (lift_at val Nat.zero d) (Nat.add d k) a) ",
        // E1 : lift(lift(val,k,a),0,d) = lift(lift(val,0,d),(0+(d+k)),a)
        "(Eq.trans KExpr ",
        "(lift_at (lift_at val k a) Nat.zero d) ",
        "(lift_at (lift_at val (Nat.add Nat.zero k) a) Nat.zero d) ",
        "(lift_at (lift_at val Nat.zero d) (Nat.add Nat.zero (Nat.add d k)) a) ",
        // rewrite k -> 0+k on the exchange LHS inner cutoff (symm nat_zero_add k)
        "(Eq.cong Nat KExpr ",
        "(fun (n : Nat) => lift_at (lift_at val n a) Nat.zero d) ",
        "k (Nat.add Nat.zero k) ",
        "(Eq.symm Nat (Nat.add Nat.zero k) k (nat_zero_add k))) ",
        // exchange instance at c=0
        "(lift_at_lift_at_exchange val Nat.zero k a d)) ",
        // E2 : rewrite (0+(d+k)) -> (d+k) on outer cutoff (nat_zero_add (d+k))
        "(Eq.cong Nat KExpr ",
        "(fun (n : Nat) => lift_at (lift_at val Nat.zero d) n a) ",
        "(Nat.add Nat.zero (Nat.add d k)) (Nat.add d k) ",
        "(nat_zero_add (Nat.add d k)))))"
    );
    // Assemble: LHS = lift(lift val 0 d)(d+k)a [lhs_form] ; bridge ; RHS [symm rhs_form].
    format!(
        concat!(
            "Eq.trans KExpr {lhs} ",
            "(lift_at (lift_at val Nat.zero d) (Nat.add d k) a) {rhs} ",
            "{lhs_form} ",
            "(Eq.trans KExpr ",
            "(lift_at (lift_at val Nat.zero d) (Nat.add d k) a) ",
            "(lift_at (lift_at val k a) Nat.zero d) {rhs} ",
            "{bridge} ",
            "(Eq.symm KExpr {rhs} (lift_at (lift_at val k a) Nat.zero d) {rhs_form}))"
        ),
        lhs = LHS,
        rhs = RHS,
        lhs_form = lhs_form,
        rhs_form = rhs_form,
        bridge = bridge,
    )
}

/// LEAF 3 (i > d, i >= succ(d+k)): both sides reduce to `KExpr.bvar ((i-1)+a)`.
/// Witnesses: h_id : sub(i,d)=succ k4 ; h_s0 : sub(succ(d+k),i)=0.
fn leaf3() -> String {
    // sub(d,i) = 0 (antisymmetry) for instantiate_bvar_at_above's first hyp.
    let w_di0 = "(nat_sub_zero_of_sub_pos i d k4 h_id)";
    // sub(d+k, i-1) = 0 (helper #2) for LHS lift geq.
    let w_dk_pred0 = "(nat_sub_zero_pred_of_succ_add_zero d k i h_s0)";
    // sub(d, i+a) = 0 for RHS instantiate above first hyp (from w_di0 via add_right on a).
    //   nat_sub_zero_add_right : sub(d,i)=0 -> sub(d, i+a) = 0 ? Need exact signature.
    //   We use the available nat_sub_zero_add_right d i a.
    let w_d_ia0 = format!("(nat_sub_zero_add_right d i a {w_di0})", w_di0 = w_di0);
    // sub(i+a, d) positive (RHS instantiate above second hyp), from h_id via add_right.
    let w_ia_d_pos = format!("(nat_sub_pos_add_right i a d {w_id})", w_id = W_ID,);
    // bridge (i-1)+a = (i+a)-1 : nat_pred_add_right i a d k4 h_id
    //   : sub(i+a, 1) = (sub(i,1)) + a, i.e. (i+a)-1 = (i-1)+a.
    // LHS chain: LHS = bvar((i-1)+a)
    //   lift_at (instantiate_at (bvar i) val d) (d+k) a
    //   = lift_at (bvar (i-1)) (d+k) a       [cong inst above]
    //   = bvar ((i-1)+a)                     [lift geq with w_dk_pred0]
    let lhs_chain = format!(
        concat!(
            "(Eq.trans KExpr {lhs} ",
            "(lift_at (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (Nat.add d k) a) ",
            "(KExpr.bvar (Nat.add (Nat.sub i (Nat.succ Nat.zero)) a)) ",
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => lift_at x (Nat.add d k) a) ",
            "(instantiate_at (KExpr.bvar i) val d) ",
            "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) ",
            "(Eq.trans KExpr (instantiate_at (KExpr.bvar i) val d) ",
            "(instantiate_bvar_at i d val) ",
            "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) ",
            "(instantiate_at_bvar i val d) ",
            "(instantiate_bvar_at_above i d val {w_di0} {w_id}))) ",
            "(lift_at_bvar_geq (Nat.sub i (Nat.succ Nat.zero)) (Nat.add d k) a {w_dk_pred0}))"
        ),
        lhs = LHS,
        w_di0 = w_di0,
        w_id = W_ID,
        w_dk_pred0 = w_dk_pred0,
    );
    // RHS chain: RHS = bvar((i+a)-1)
    //   instantiate_at (lift_at (bvar i) (succ(d+k)) a) (lift val k a) d
    //   = instantiate_at (bvar (i+a)) (lift val k a) d   [cong lift geq]
    //   = bvar ((i+a)-1)                                 [inst above]
    let rhs_chain = format!(
        concat!(
            "(Eq.trans KExpr {rhs} ",
            "(instantiate_at (KExpr.bvar (Nat.add i a)) (lift_at val k a) d) ",
            "(KExpr.bvar (Nat.sub (Nat.add i a) (Nat.succ Nat.zero))) ",
            "(Eq.cong KExpr KExpr ",
            "(fun (x : KExpr) => instantiate_at x (lift_at val k a) d) ",
            "(lift_at (KExpr.bvar i) (Nat.succ (Nat.add d k)) a) ",
            "(KExpr.bvar (Nat.add i a)) ",
            "(lift_at_bvar_geq i (Nat.succ (Nat.add d k)) a h_s0)) ",
            "(Eq.trans KExpr ",
            "(instantiate_at (KExpr.bvar (Nat.add i a)) (lift_at val k a) d) ",
            "(instantiate_bvar_at (Nat.add i a) d (lift_at val k a)) ",
            "(KExpr.bvar (Nat.sub (Nat.add i a) (Nat.succ Nat.zero))) ",
            "(instantiate_at_bvar (Nat.add i a) (lift_at val k a) d) ",
            "(instantiate_bvar_at_above (Nat.add i a) d (lift_at val k a) {w_d_ia0} {w_ia_d_pos})))"
        ),
        rhs = RHS,
        w_d_ia0 = w_d_ia0,
        w_ia_d_pos = w_ia_d_pos,
    );
    // BRIDGE bvar((i-1)+a) = bvar((i+a)-1) via Eq.symm of nat_pred_add_at_pos.
    //   nat_pred_add_at_pos i a d k4 h_id : sub(i+a,1) = (sub(i,1)) + a
    //   i.e. (i+a)-1 = (i-1)+a. We need (i-1)+a = (i+a)-1, so Eq.symm.
    let bridge = concat!(
        "(Eq.cong Nat KExpr KExpr.bvar ",
        "(Nat.add (Nat.sub i (Nat.succ Nat.zero)) a) ",
        "(Nat.sub (Nat.add i a) (Nat.succ Nat.zero)) ",
        "(Eq.symm Nat ",
        "(Nat.sub (Nat.add i a) (Nat.succ Nat.zero)) ",
        "(Nat.add (Nat.sub i (Nat.succ Nat.zero)) a) ",
        "(nat_pred_add_at_pos i a d k4 h_id)))"
    );
    // Assemble: LHS = bvar((i-1)+a) [lhs_chain] ; bridge to bvar((i+a)-1) ; symm rhs_chain.
    format!(
        concat!(
            "Eq.trans KExpr {lhs} ",
            "(KExpr.bvar (Nat.add (Nat.sub i (Nat.succ Nat.zero)) a)) {rhs} ",
            "{lhs_chain} ",
            "(Eq.trans KExpr ",
            "(KExpr.bvar (Nat.add (Nat.sub i (Nat.succ Nat.zero)) a)) ",
            "(KExpr.bvar (Nat.sub (Nat.add i a) (Nat.succ Nat.zero))) {rhs} ",
            "{bridge} ",
            "(Eq.symm KExpr {rhs} ",
            "(KExpr.bvar (Nat.sub (Nat.add i a) (Nat.succ Nat.zero))) {rhs_chain}))"
        ),
        lhs = LHS,
        rhs = RHS,
        lhs_chain = lhs_chain,
        rhs_chain = rhs_chain,
        bridge = bridge,
    )
}

/// LEAF 4 (i > d, i < succ(d+k)): both sides reduce to `KExpr.bvar (i-1)`.
/// Witnesses: h_id : sub(i,d)=succ k4 ; h_s : sub(succ(d+k),i)=succ k6.
fn leaf4() -> String {
    // sub(d,i)=0 (antisymmetry) for instantiate above first hyp.
    let w_di0 = "(nat_sub_zero_of_sub_pos i d k4 h_id)";
    // sub(succ(d+k),i) positive-witness, from h_s.
    let w_s_pos = "(nat_pos_witness_from_succ_eq (Nat.sub (Nat.succ (Nat.add d k)) i) k6 h_s)";
    // sub(d+k, i-1) positive (helper #3) for LHS lift below.
    let w_dk_pred_pos = format!(
        "(nat_sub_pos_pred_of_succ_add_pos d k i {w_s_pos} {w_id})",
        w_s_pos = w_s_pos,
        w_id = W_ID,
    );
    // LHS chain: LHS = bvar (i-1)
    //   lift_at (instantiate_at (bvar i) val d) (d+k) a
    //   = lift_at (bvar (i-1)) (d+k) a    [cong inst above]
    //   = bvar (i-1)                      [lift below with w_dk_pred_pos]
    let lhs_chain = format!(
        concat!(
            "(Eq.trans KExpr {lhs} ",
            "(lift_at (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (Nat.add d k) a) ",
            "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) ",
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => lift_at x (Nat.add d k) a) ",
            "(instantiate_at (KExpr.bvar i) val d) ",
            "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) ",
            "(Eq.trans KExpr (instantiate_at (KExpr.bvar i) val d) ",
            "(instantiate_bvar_at i d val) ",
            "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) ",
            "(instantiate_at_bvar i val d) ",
            "(instantiate_bvar_at_above i d val {w_di0} {w_id}))) ",
            "(lift_at_bvar_below (Nat.sub i (Nat.succ Nat.zero)) (Nat.add d k) a {w_dk_pred_pos}))"
        ),
        lhs = LHS,
        w_di0 = w_di0,
        w_id = W_ID,
        w_dk_pred_pos = w_dk_pred_pos,
    );
    // RHS chain: RHS = bvar (i-1)
    //   instantiate_at (lift_at (bvar i) (succ(d+k)) a) (lift val k a) d
    //   = instantiate_at (bvar i) (lift val k a) d   [cong lift below]
    //   = bvar (i-1)                                 [inst above]
    let rhs_chain = format!(
        concat!(
            "(Eq.trans KExpr {rhs} ",
            "(instantiate_at (KExpr.bvar i) (lift_at val k a) d) ",
            "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) ",
            "(Eq.cong KExpr KExpr ",
            "(fun (x : KExpr) => instantiate_at x (lift_at val k a) d) ",
            "(lift_at (KExpr.bvar i) (Nat.succ (Nat.add d k)) a) (KExpr.bvar i) ",
            "(lift_at_bvar_below i (Nat.succ (Nat.add d k)) a {w_s_pos})) ",
            "(Eq.trans KExpr ",
            "(instantiate_at (KExpr.bvar i) (lift_at val k a) d) ",
            "(instantiate_bvar_at i d (lift_at val k a)) ",
            "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) ",
            "(instantiate_at_bvar i (lift_at val k a) d) ",
            "(instantiate_bvar_at_above i d (lift_at val k a) {w_di0} {w_id})))"
        ),
        rhs = RHS,
        w_s_pos = w_s_pos,
        w_di0 = w_di0,
        w_id = W_ID,
    );
    format!(
        concat!(
            "Eq.trans KExpr {lhs} ",
            "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) {rhs} ",
            "{lhs_chain} ",
            "(Eq.symm KExpr {rhs} (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) {rhs_chain})"
        ),
        lhs = LHS,
        rhs = RHS,
        lhs_chain = lhs_chain,
        rhs_chain = rhs_chain,
    )
}

// ===================================================================
// full KExpr.rec proof (sort/const refl, bvar delegate, app/lam/pi).
// ===================================================================

fn full_proof() -> String {
    let motive = concat!(
        "(fun (expr : KExpr) => forall (val : KExpr) (d : Nat) (k : Nat) (a : Nat), ",
        "Eq KExpr ",
        "(lift_at (instantiate_at expr val d) (Nat.add d k) a) ",
        "(instantiate_at (lift_at expr (Nat.succ (Nat.add d k)) a) (lift_at val k a) d))"
    );
    let ih = concat!(
        "forall (val : KExpr) (d : Nat) (k : Nat) (a : Nat), ",
        "Eq KExpr ",
        "(lift_at (instantiate_at SUB val d) (Nat.add d k) a) ",
        "(instantiate_at (lift_at SUB (Nat.succ (Nat.add d k)) a) (lift_at val k a) d)"
    );
    let ih_f = ih.replace("SUB", "f");
    let ih_a = ih.replace("SUB", "a0");
    let ih_ty = ih.replace("SUB", "ty");
    let ih_lval = ih.replace("SUB", "lval");
    let ih_body = ih.replace("SUB", "body");
    format!(
        concat!(
            "fun (body : KExpr) (val : KExpr) (d : Nat) (k : Nat) (a : Nat) => ",
            "KExpr.rec {motive} ",
            // sort
            "(fun (sv : Level) (val : KExpr) (d : Nat) (k : Nat) (a : Nat) => ",
            "Eq.refl KExpr (KExpr.sort sv)) ",
            // bvar
            "(fun (i : Nat) (val : KExpr) (d : Nat) (k : Nat) (a : Nat) => ",
            "lift_instantiate_swap_bvar i val d k a) ",
            // app
            "(fun (f : KExpr) (a0 : KExpr) ",
            "(ih_f : {ih_f}) (ih_a : {ih_a}) ",
            "(val : KExpr) (d : Nat) (k : Nat) (a : Nat) => {app_arm}) ",
            // lam
            "(fun (ty : KExpr) (body : KExpr) ",
            "(ih_ty : {ih_ty}) (ih_body : {ih_body}) ",
            "(val : KExpr) (d : Nat) (k : Nat) (a : Nat) => {lam_arm}) ",
            // pi
            "(fun (ty : KExpr) (body : KExpr) ",
            "(ih_ty : {ih_ty}) (ih_body : {ih_body}) ",
            "(val : KExpr) (d : Nat) (k : Nat) (a : Nat) => {pi_arm}) ",
            // const
            "(fun (nm : Name) (us : ListType Level) ",
            "(val : KExpr) (d : Nat) (k : Nat) (a : Nat) => ",
            "Eq.refl KExpr (KExpr.const nm us)) ",
            // let_
            "(fun (ty : KExpr) (lval : KExpr) (body : KExpr) ",
            "(ih_ty : {ih_ty}) (ih_lval : {ih_lval}) (ih_body : {ih_body}) ",
            "(val : KExpr) (d : Nat) (k : Nat) (a : Nat) => {let_arm}) ",
            // proj: 1-child node; lift_at + instantiate_at reduce through proj, ih_sub cong.
            "(fun (s : Name) (i : Nat) (sub : KExpr) ",
            "(ih_sub : forall (val : KExpr) (d : Nat) (k : Nat) (a : Nat), Eq KExpr (lift_at (instantiate_at sub val d) (Nat.add d k) a) (instantiate_at (lift_at sub (Nat.succ (Nat.add d k)) a) (lift_at val k a) d)) ",
            "(val : KExpr) (d : Nat) (k : Nat) (a : Nat) => ",
            "Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.proj s i x) (lift_at (instantiate_at sub val d) (Nat.add d k) a) (instantiate_at (lift_at sub (Nat.succ (Nat.add d k)) a) (lift_at val k a) d) (ih_sub val d k a)) ",
            // lit: leaf.
            "(fun (litn : Nat) (val : KExpr) (d : Nat) (k : Nat) (a : Nat) => Eq.refl KExpr (KExpr.lit litn)) ",
            "body val d k a",
        ),
        motive = motive,
        ih_f = ih_f,
        ih_a = ih_a,
        ih_ty = ih_ty,
        ih_lval = ih_lval,
        ih_body = ih_body,
        app_arm = app_arm(),
        lam_arm = binder_arm("KExpr.lam", "lift_at_lam", "instantiate_at_lam"),
        pi_arm = binder_arm("KExpr.pi", "lift_at_pi", "instantiate_at_pi"),
        let_arm = let_arm(),
    )
}

/// app arm: unfold instantiate_at_app + lift_at on both sides, apply IHs.
///
/// LHS = lift_at (instantiate_at (app f a0) val d) (d+k) a
///     = lift_at (app (inst f val d) (inst a0 val d)) (d+k) a
///     = app (lift_at (inst f val d) (d+k) a) (lift_at (inst a0 val d) (d+k) a)
/// RHS = instantiate_at (lift_at (app f a0) (succ(d+k)) a) (lift val k a) d
///     = instantiate_at (app (lift f (succ(d+k)) a) (lift a0 (succ(d+k)) a)) (lift val k a) d
///     = app (instantiate_at (lift f (succ(d+k)) a) (lift val k a) d)
///           (instantiate_at (lift a0 (succ(d+k)) a) (lift val k a) d)
/// IHs equate the two components.
fn app_arm() -> String {
    // LHS' = app (lift (inst f val d) (d+k) a) (lift (inst a0 val d) (d+k) a)
    // RHS' = app (inst (lift f (succ(d+k)) a) (lift val k a) d)
    //            (inst (lift a0 (succ(d+k)) a) (lift val k a) d)
    let lhs = "(lift_at (instantiate_at (KExpr.app f a0) val d) (Nat.add d k) a)";
    let rhs = concat!(
        "(instantiate_at (lift_at (KExpr.app f a0) (Nat.succ (Nat.add d k)) a) ",
        "(lift_at val k a) d)"
    );
    let lhs_mid = concat!(
        "(KExpr.app (lift_at (instantiate_at f val d) (Nat.add d k) a) ",
        "(lift_at (instantiate_at a0 val d) (Nat.add d k) a))"
    );
    let rhs_mid = concat!(
        "(KExpr.app ",
        "(instantiate_at (lift_at f (Nat.succ (Nat.add d k)) a) (lift_at val k a) d) ",
        "(instantiate_at (lift_at a0 (Nat.succ (Nat.add d k)) a) (lift_at val k a) d))"
    );
    format!(
        concat!(
            // LHS = LHS_mid
            "Eq.trans KExpr {lhs} {lhs_mid} {rhs} ",
            "(Eq.trans KExpr {lhs} ",
            "(lift_at (KExpr.app (instantiate_at f val d) (instantiate_at a0 val d)) ",
            "(Nat.add d k) a) ",
            "{lhs_mid} ",
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => lift_at x (Nat.add d k) a) ",
            "(instantiate_at (KExpr.app f a0) val d) ",
            "(KExpr.app (instantiate_at f val d) (instantiate_at a0 val d)) ",
            "(instantiate_at_app f a0 val d)) ",
            "(lift_at_app (instantiate_at f val d) (instantiate_at a0 val d) (Nat.add d k) a)) ",
            // LHS_mid = RHS_mid via IHs, then RHS_mid = RHS
            "(Eq.trans KExpr {lhs_mid} {rhs_mid} {rhs} ",
            // IH on f then IH on a0
            "(Eq.trans KExpr {lhs_mid} ",
            "(KExpr.app ",
            "(instantiate_at (lift_at f (Nat.succ (Nat.add d k)) a) (lift_at val k a) d) ",
            "(lift_at (instantiate_at a0 val d) (Nat.add d k) a)) ",
            "{rhs_mid} ",
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x ",
            "(lift_at (instantiate_at a0 val d) (Nat.add d k) a)) ",
            "(lift_at (instantiate_at f val d) (Nat.add d k) a) ",
            "(instantiate_at (lift_at f (Nat.succ (Nat.add d k)) a) (lift_at val k a) d) ",
            "(ih_f val d k a)) ",
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app ",
            "(instantiate_at (lift_at f (Nat.succ (Nat.add d k)) a) (lift_at val k a) d) x) ",
            "(lift_at (instantiate_at a0 val d) (Nat.add d k) a) ",
            "(instantiate_at (lift_at a0 (Nat.succ (Nat.add d k)) a) (lift_at val k a) d) ",
            "(ih_a val d k a))) ",
            // RHS_mid = RHS : fold back via symm of (inst_app then lift_app cong)
            "(Eq.symm KExpr {rhs} {rhs_mid} ",
            "(Eq.trans KExpr {rhs} ",
            "(instantiate_at (KExpr.app (lift_at f (Nat.succ (Nat.add d k)) a) ",
            "(lift_at a0 (Nat.succ (Nat.add d k)) a)) (lift_at val k a) d) ",
            "{rhs_mid} ",
            "(Eq.cong KExpr KExpr ",
            "(fun (x : KExpr) => instantiate_at x (lift_at val k a) d) ",
            "(lift_at (KExpr.app f a0) (Nat.succ (Nat.add d k)) a) ",
            "(KExpr.app (lift_at f (Nat.succ (Nat.add d k)) a) ",
            "(lift_at a0 (Nat.succ (Nat.add d k)) a)) ",
            "(lift_at_app f a0 (Nat.succ (Nat.add d k)) a)) ",
            "(instantiate_at_app (lift_at f (Nat.succ (Nat.add d k)) a) ",
            "(lift_at a0 (Nat.succ (Nat.add d k)) a) (lift_at val k a) d))))"
        ),
        lhs = lhs,
        rhs = rhs,
        lhs_mid = lhs_mid,
        rhs_mid = rhs_mid,
    )
}

/// lam/pi arm, parametric in the constructor and its unfolders.
///
/// LHS = lift_at (instantiate_at (C ty body) val d) (d+k) a
///     = lift_at (C (inst ty val d) (inst body val (succ d))) (d+k) a
///     = C (lift (inst ty val d) (d+k) a) (lift (inst body val (succ d)) (succ(d+k)) a)
/// RHS = instantiate_at (lift_at (C ty body) (succ(d+k)) a) (lift val k a) d
///     = instantiate_at (C (lift ty (succ(d+k)) a) (lift body (succ(succ(d+k))) a))
///                      (lift val k a) d
///     = C (inst (lift ty (succ(d+k)) a) (lift val k a) d)
///         (inst (lift body (succ(succ(d+k))) a) (lift val k a) (succ d))
/// ty IH closes the first component directly. For the body component we need
/// the IH on body at (val, succ d, k, a):
///   lift (inst body val (succ d)) ((succ d)+k) a
///     = inst (lift body (succ((succ d)+k)) a) (lift val k a) (succ d)
/// and (succ d)+k = succ(d+k) by nat_succ_add, so succ((succ d)+k) = succ(succ(d+k))
/// and the LHS body cutoff succ(d+k) = (succ d)+k. Transport both occurrences.
fn binder_arm(ctor: &str, lift_unfold: &str, inst_unfold: &str) -> String {
    format!(
        concat!(
            // canonical shapes
            // LHS, RHS
            "Eq.trans KExpr ",
            "(lift_at (instantiate_at ({ctor} ty body) val d) (Nat.add d k) a) ",
            // LHS_mid = C (lift (inst ty val d) (d+k) a) (lift (inst body val (succ d)) (succ(d+k)) a)
            "({ctor} (lift_at (instantiate_at ty val d) (Nat.add d k) a) ",
            "(lift_at (instantiate_at body val (Nat.succ d)) (Nat.succ (Nat.add d k)) a)) ",
            "(instantiate_at (lift_at ({ctor} ty body) (Nat.succ (Nat.add d k)) a) ",
            "(lift_at val k a) d) ",
            // ---- LHS = LHS_mid ----
            "(Eq.trans KExpr ",
            "(lift_at (instantiate_at ({ctor} ty body) val d) (Nat.add d k) a) ",
            "(lift_at ({ctor} (instantiate_at ty val d) ",
            "(instantiate_at body val (Nat.succ d))) (Nat.add d k) a) ",
            "({ctor} (lift_at (instantiate_at ty val d) (Nat.add d k) a) ",
            "(lift_at (instantiate_at body val (Nat.succ d)) (Nat.succ (Nat.add d k)) a)) ",
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => lift_at x (Nat.add d k) a) ",
            "(instantiate_at ({ctor} ty body) val d) ",
            "({ctor} (instantiate_at ty val d) (instantiate_at body val (Nat.succ d))) ",
            "({inst_unfold} ty body val d)) ",
            "({lift_unfold} (instantiate_at ty val d) ",
            "(instantiate_at body val (Nat.succ d)) (Nat.add d k) a)) ",
            // ---- LHS_mid = RHS ----
            "(Eq.trans KExpr ",
            "({ctor} (lift_at (instantiate_at ty val d) (Nat.add d k) a) ",
            "(lift_at (instantiate_at body val (Nat.succ d)) (Nat.succ (Nat.add d k)) a)) ",
            // RHS_mid = C (inst (lift ty (succ(d+k)) a) (lift val k a) d)
            //             (inst (lift body (succ(succ(d+k))) a) (lift val k a) (succ d))
            "({ctor} ",
            "(instantiate_at (lift_at ty (Nat.succ (Nat.add d k)) a) (lift_at val k a) d) ",
            "(instantiate_at (lift_at body (Nat.succ (Nat.succ (Nat.add d k))) a) ",
            "(lift_at val k a) (Nat.succ d))) ",
            "(instantiate_at (lift_at ({ctor} ty body) (Nat.succ (Nat.add d k)) a) ",
            "(lift_at val k a) d) ",
            // ty IH and body IH (with transport)
            "(Eq.trans KExpr ",
            "({ctor} (lift_at (instantiate_at ty val d) (Nat.add d k) a) ",
            "(lift_at (instantiate_at body val (Nat.succ d)) (Nat.succ (Nat.add d k)) a)) ",
            "({ctor} ",
            "(instantiate_at (lift_at ty (Nat.succ (Nat.add d k)) a) (lift_at val k a) d) ",
            "(lift_at (instantiate_at body val (Nat.succ d)) (Nat.succ (Nat.add d k)) a)) ",
            "({ctor} ",
            "(instantiate_at (lift_at ty (Nat.succ (Nat.add d k)) a) (lift_at val k a) d) ",
            "(instantiate_at (lift_at body (Nat.succ (Nat.succ (Nat.add d k))) a) ",
            "(lift_at val k a) (Nat.succ d))) ",
            // cong ty IH on first slot
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => {ctor} x ",
            "(lift_at (instantiate_at body val (Nat.succ d)) (Nat.succ (Nat.add d k)) a)) ",
            "(lift_at (instantiate_at ty val d) (Nat.add d k) a) ",
            "(instantiate_at (lift_at ty (Nat.succ (Nat.add d k)) a) (lift_at val k a) d) ",
            "(ih_ty val d k a)) ",
            // cong body IH (transported) on second slot
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => {ctor} ",
            "(instantiate_at (lift_at ty (Nat.succ (Nat.add d k)) a) (lift_at val k a) d) x) ",
            "(lift_at (instantiate_at body val (Nat.succ d)) (Nat.succ (Nat.add d k)) a) ",
            "(instantiate_at (lift_at body (Nat.succ (Nat.succ (Nat.add d k))) a) ",
            "(lift_at val k a) (Nat.succ d)) ",
            // body chain: transport LHS cutoff succ(d+k) -> (succ d)+k, apply body IH,
            // transport result cutoff succ((succ d)+k) -> succ(succ(d+k)).
            "(Eq.trans KExpr ",
            "(lift_at (instantiate_at body val (Nat.succ d)) (Nat.succ (Nat.add d k)) a) ",
            "(lift_at (instantiate_at body val (Nat.succ d)) (Nat.add (Nat.succ d) k) a) ",
            "(instantiate_at (lift_at body (Nat.succ (Nat.succ (Nat.add d k))) a) ",
            "(lift_at val k a) (Nat.succ d)) ",
            // transport LHS body cutoff succ(d+k) -> (succ d)+k (symm nat_succ_add)
            "(Eq.cong Nat KExpr ",
            "(fun (n : Nat) => lift_at (instantiate_at body val (Nat.succ d)) n a) ",
            "(Nat.succ (Nat.add d k)) (Nat.add (Nat.succ d) k) ",
            "(Eq.symm Nat (Nat.add (Nat.succ d) k) (Nat.succ (Nat.add d k)) ",
            "(nat_succ_add d k))) ",
            // apply body IH at (val, succ d, k, a), then transport its result cutoff.
            "(Eq.trans KExpr ",
            "(lift_at (instantiate_at body val (Nat.succ d)) (Nat.add (Nat.succ d) k) a) ",
            "(instantiate_at (lift_at body (Nat.succ (Nat.add (Nat.succ d) k)) a) ",
            "(lift_at val k a) (Nat.succ d)) ",
            "(instantiate_at (lift_at body (Nat.succ (Nat.succ (Nat.add d k))) a) ",
            "(lift_at val k a) (Nat.succ d)) ",
            "(ih_body val (Nat.succ d) k a) ",
            // transport succ((succ d)+k) -> succ(succ(d+k)) via nat_succ_add inside succ
            "(Eq.cong Nat KExpr ",
            "(fun (n : Nat) => instantiate_at (lift_at body (Nat.succ n) a) ",
            "(lift_at val k a) (Nat.succ d)) ",
            "(Nat.add (Nat.succ d) k) (Nat.succ (Nat.add d k)) ",
            "(nat_succ_add d k)))))) ",
            // ---- RHS_mid = RHS : fold back ----
            "(Eq.symm KExpr ",
            "(instantiate_at (lift_at ({ctor} ty body) (Nat.succ (Nat.add d k)) a) ",
            "(lift_at val k a) d) ",
            "({ctor} ",
            "(instantiate_at (lift_at ty (Nat.succ (Nat.add d k)) a) (lift_at val k a) d) ",
            "(instantiate_at (lift_at body (Nat.succ (Nat.succ (Nat.add d k))) a) ",
            "(lift_at val k a) (Nat.succ d))) ",
            "(Eq.trans KExpr ",
            "(instantiate_at (lift_at ({ctor} ty body) (Nat.succ (Nat.add d k)) a) ",
            "(lift_at val k a) d) ",
            "(instantiate_at ({ctor} (lift_at ty (Nat.succ (Nat.add d k)) a) ",
            "(lift_at body (Nat.succ (Nat.succ (Nat.add d k))) a)) (lift_at val k a) d) ",
            "({ctor} ",
            "(instantiate_at (lift_at ty (Nat.succ (Nat.add d k)) a) (lift_at val k a) d) ",
            "(instantiate_at (lift_at body (Nat.succ (Nat.succ (Nat.add d k))) a) ",
            "(lift_at val k a) (Nat.succ d))) ",
            // unfold the outer lift on (C ty body) at cutoff succ(d+k): body cutoff becomes succ(succ(d+k))
            "(Eq.cong KExpr KExpr ",
            "(fun (x : KExpr) => instantiate_at x (lift_at val k a) d) ",
            "(lift_at ({ctor} ty body) (Nat.succ (Nat.add d k)) a) ",
            "({ctor} (lift_at ty (Nat.succ (Nat.add d k)) a) ",
            "(lift_at body (Nat.succ (Nat.succ (Nat.add d k))) a)) ",
            "({lift_unfold} ty body (Nat.succ (Nat.add d k)) a)) ",
            // unfold instantiate on C: body depth becomes succ d
            "({inst_unfold} (lift_at ty (Nat.succ (Nat.add d k)) a) ",
            "(lift_at body (Nat.succ (Nat.succ (Nat.add d k))) a) (lift_at val k a) d))))",
        ),
        ctor = ctor,
        lift_unfold = lift_unfold,
        inst_unfold = inst_unfold,
    )
}

/// let_ arm of the KExpr.rec proof (three children: ty/lval at cutoff d, the
/// body under one binder). A hybrid of `app_arm` (ty and lval share the same
/// cutoff/depth, closed directly by their IHs) and `binder_arm` (the body
/// child transports its IH depth (succ d)+k = succ(d+k) via nat_succ_add,
/// exactly as the lam/pi body does).
fn let_arm() -> String {
    // canonical shapes (child cutoffs/depths).
    let inst_ty_d = "(instantiate_at ty val d)";
    let inst_lval_d = "(instantiate_at lval val d)";
    let inst_body_sd = "(instantiate_at body val (Nat.succ d))";
    let lift_inst_ty = "(lift_at (instantiate_at ty val d) (Nat.add d k) a)";
    let lift_inst_lval = "(lift_at (instantiate_at lval val d) (Nat.add d k) a)";
    let lift_inst_body =
        "(lift_at (instantiate_at body val (Nat.succ d)) (Nat.succ (Nat.add d k)) a)";
    let lift_ty_s = "(lift_at ty (Nat.succ (Nat.add d k)) a)";
    let lift_lval_s = "(lift_at lval (Nat.succ (Nat.add d k)) a)";
    let lift_body_ss = "(lift_at body (Nat.succ (Nat.succ (Nat.add d k))) a)";
    let inst_lift_ty =
        "(instantiate_at (lift_at ty (Nat.succ (Nat.add d k)) a) (lift_at val k a) d)";
    let inst_lift_lval =
        "(instantiate_at (lift_at lval (Nat.succ (Nat.add d k)) a) (lift_at val k a) d)";
    let inst_lift_body = "(instantiate_at (lift_at body (Nat.succ (Nat.succ (Nat.add d k))) a) (lift_at val k a) (Nat.succ d))";

    let lhs = "(lift_at (instantiate_at (KExpr.let_ ty lval body) val d) (Nat.add d k) a)";
    let rhs = "(instantiate_at (lift_at (KExpr.let_ ty lval body) (Nat.succ (Nat.add d k)) a) (lift_at val k a) d)";
    let inst_unfolded = format!("(KExpr.let_ {inst_ty_d} {inst_lval_d} {inst_body_sd})");
    let lift_of_that = format!("(lift_at {inst_unfolded} (Nat.add d k) a)");
    let lhs_mid = format!("(KExpr.let_ {lift_inst_ty} {lift_inst_lval} {lift_inst_body})");
    let rhs_mid = format!("(KExpr.let_ {inst_lift_ty} {inst_lift_lval} {inst_lift_body})");
    let m1 = format!("(KExpr.let_ {inst_lift_ty} {lift_inst_lval} {lift_inst_body})");
    let m2 = format!("(KExpr.let_ {inst_lift_ty} {inst_lift_lval} {lift_inst_body})");
    let rhs_intermediate = format!(
        "(instantiate_at (KExpr.let_ {lift_ty_s} {lift_lval_s} {lift_body_ss}) (lift_at val k a) d)"
    );

    // ---- STEP1: LHS = LHS_mid (unfold instantiate then lift over let_) ----
    let step1 = format!(
        "(Eq.trans KExpr {lhs} {lift_of_that} {lhs_mid} \
         (Eq.cong KExpr KExpr (fun (x : KExpr) => lift_at x (Nat.add d k) a) \
         (instantiate_at (KExpr.let_ ty lval body) val d) {inst_unfolded} \
         (instantiate_at_let_ ty lval body val d)) \
         (lift_at_let_ {inst_ty_d} {inst_lval_d} {inst_body_sd} (Nat.add d k) a))"
    );

    // body-child chain: transport the LHS body cutoff succ(d+k) -> (succ d)+k,
    // apply the body IH at (val, succ d, k, a), transport its result cutoff back.
    let body_chain = format!(
        "(Eq.trans KExpr {lift_inst_body} \
         (lift_at (instantiate_at body val (Nat.succ d)) (Nat.add (Nat.succ d) k) a) \
         {inst_lift_body} \
         (Eq.cong Nat KExpr \
         (fun (n : Nat) => lift_at (instantiate_at body val (Nat.succ d)) n a) \
         (Nat.succ (Nat.add d k)) (Nat.add (Nat.succ d) k) \
         (Eq.symm Nat (Nat.add (Nat.succ d) k) (Nat.succ (Nat.add d k)) (nat_succ_add d k))) \
         (Eq.trans KExpr \
         (lift_at (instantiate_at body val (Nat.succ d)) (Nat.add (Nat.succ d) k) a) \
         (instantiate_at (lift_at body (Nat.succ (Nat.add (Nat.succ d) k)) a) (lift_at val k a) (Nat.succ d)) \
         {inst_lift_body} \
         (ih_body val (Nat.succ d) k a) \
         (Eq.cong Nat KExpr \
         (fun (n : Nat) => instantiate_at (lift_at body (Nat.succ n) a) (lift_at val k a) (Nat.succ d)) \
         (Nat.add (Nat.succ d) k) (Nat.succ (Nat.add d k)) \
         (nat_succ_add d k))))"
    );

    // ---- STEP2: LHS_mid = RHS_mid via the three child IHs ----
    let cong_ty = format!(
        "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.let_ x {lift_inst_lval} {lift_inst_body}) \
         {lift_inst_ty} {inst_lift_ty} (ih_ty val d k a))"
    );
    let cong_lval = format!(
        "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.let_ {inst_lift_ty} x {lift_inst_body}) \
         {lift_inst_lval} {inst_lift_lval} (ih_lval val d k a))"
    );
    let cong_body = format!(
        "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.let_ {inst_lift_ty} {inst_lift_lval} x) \
         {lift_inst_body} {inst_lift_body} {body_chain})"
    );
    let step2 = format!(
        "(Eq.trans KExpr {lhs_mid} {m1} {rhs_mid} {cong_ty} \
         (Eq.trans KExpr {m1} {m2} {rhs_mid} {cong_lval} {cong_body}))"
    );

    // ---- STEP3: RHS_mid = RHS (fold the lift/instantiate back over let_) ----
    let step3 = format!(
        "(Eq.symm KExpr {rhs} {rhs_mid} \
         (Eq.trans KExpr {rhs} {rhs_intermediate} {rhs_mid} \
         (Eq.cong KExpr KExpr (fun (x : KExpr) => instantiate_at x (lift_at val k a) d) \
         (lift_at (KExpr.let_ ty lval body) (Nat.succ (Nat.add d k)) a) \
         (KExpr.let_ {lift_ty_s} {lift_lval_s} {lift_body_ss}) \
         (lift_at_let_ ty lval body (Nat.succ (Nat.add d k)) a)) \
         (instantiate_at_let_ {lift_ty_s} {lift_lval_s} {lift_body_ss} (lift_at val k a) d)))"
    );

    format!(
        "Eq.trans KExpr {lhs} {lhs_mid} {rhs} {step1} \
         (Eq.trans KExpr {lhs_mid} {rhs_mid} {rhs} {step2} {step3})"
    )
}

#[cfg(test)]
mod tests {
    use crate::spec::types::ProofStatus;
    use crate::test_utils::run_with_stack;
    use crate::Specification;

    #[test]
    fn test_lift_instantiate_swap_is_derived_proved() {
        let spec = run_with_stack(|| {
            Specification::new_substitution_test_spec()
                .expect("substitution/WHNF test spec should build")
        });

        for name in ["lift_instantiate_swap_bvar", "lift_instantiate_swap"] {
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
                "{name} should have no axiom deps: {:?}",
                def.axiom_deps
            );
        }
    }
}
