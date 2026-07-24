// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Cross-cutoff lift EXCHANGE (non-collapsing) for substitution/lift proofs.
//!
//! Contains:
//!   - lift_at_lift_at_exchange_bvar: bvar case of the exchange.
//!   - lift_at_lift_at_exchange: full KExpr.rec exchange.
//!
//! Statement (no side condition):
//!   lift_at (lift_at e (Nat.add c k) a) c d
//!   = lift_at (lift_at e c d) (Nat.add c (Nat.add d k)) a
//!
//! Unlike `lift_at_cross_compose` (which COLLAPSES a nested lift whose outer
//! cutoff is at-or-above the inner cutoff into a single lift), this lemma
//! EXCHANGES two lifts whose cutoffs straddle: the `d`-lift sits at the lower
//! cutoff `c`, the `a`-lift at the higher cutoff `c+k`. Pushing the lower-cutoff
//! lift outermost shifts the higher cutoff by `d` (to `c + (d + k)`). This is
//! the genuine lift/lift commutation needed by the `i = depth` arm of
//! `lift_instantiate_swap` (Route B, #2859), where the substituted value picks
//! up the binder-depth lift (cutoff 0, amount d) on one side and the structural
//! lift (cutoff c+k → here k after the depth offset cancels) on the other.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_expr_model_subst_lift_exchange(&mut self) -> Result<(), SpecError> {
        // lift_at_lift_at_exchange_bvar: bvar case of the lift exchange.
        //
        // Statement:
        //   lift_at (lift_at (bvar j) (c+k) a) c d
        //   = lift_at (lift_at (bvar j) c d) (c+(d+k)) a
        //
        // Proof: triple Nat.rec convoy.
        //   Outer on sub(c+k, j):
        //     0  (j >= c+k)  : both sides reduce to bvar via two lift_at_bvar_geq
        //                      each; bridge (j+a)+d = (j+d)+a by add assoc/comm.
        //     succ (j < c+k) : inner Nat.rec on sub(c, j):
        //        0   (c <= j < c+k) : LHS inner lift below (bvar j), then geq → bvar(j+d);
        //                             RHS lift c d → bvar(j+d), then outer below → bvar(j+d).
        //        succ (j < c)       : every lift below → bvar j on both sides.
        // No side condition. Empty axiom_deps.
        self.add_definition_structural(SpecDefinition {
            name: "lift_at_lift_at_exchange_bvar".to_string(),
            type_src: concat!(
                "forall (j : Nat) (c : Nat) (k : Nat) (a : Nat) (d : Nat), ",
                "Eq KExpr ",
                "(lift_at (lift_at (KExpr.bvar j) (Nat.add c k) a) c d) ",
                "(lift_at (lift_at (KExpr.bvar j) c d) (Nat.add c (Nat.add d k)) a)"
            )
            .to_string(),
            value_src: Some(bvar_exchange_proof()),
            is_axiom: false,
            description: concat!(
                "bvar case of the cross-cutoff lift exchange: ",
                "lift(lift(bvar j, c+k, a), c, d) = lift(lift(bvar j, c, d), c+(d+k), a). ",
                "DerivedProved via a triple Nat.rec convoy on sub(c+k,j) then sub(c,j). ",
                "No side condition, no new axiom. Part of #2859 Wave 127 (Route B)."
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
                "lift_at_bvar_below".to_string(),
                "lift_at_bvar_geq".to_string(),
                "nat_add_assoc".to_string(),
                "nat_add_comm".to_string(),
                "nat_pos_witness_from_succ_eq".to_string(),
                "nat_sub_pos_add_right".to_string(),
                "nat_sub_pos_add_same_right".to_string(),
                "nat_sub_zero_add_right".to_string(),
                "nat_sub_zero_add_same_right".to_string(),
                "nat_sub_zero_trans".to_string(),
                "nat_sub_self".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lift_at_lift_at_exchange: full-expression lift exchange.
        //
        // KExpr.rec on e, motive universalizing c, k, a, d.
        //   sort/const : Eq.refl.
        //   bvar       : delegate to lift_at_lift_at_exchange_bvar.
        //   app        : unfold lift_at_app twice each side, IH on f and a.
        //   lam/pi     : unfold lift_at_lam/pi twice each side; ty IH at (c,k,a,d);
        //                body IH at (succ c, k, a, d) with the outer cutoff
        //                transport succ(c+(d+k)) = (succ c)+(d+k) via nat_succ_add.
        // No side condition. Empty axiom_deps.
        self.add_definition_structural(SpecDefinition {
            name: "lift_at_lift_at_exchange".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (c : Nat) (k : Nat) (a : Nat) (d : Nat), ",
                "Eq KExpr ",
                "(lift_at (lift_at e (Nat.add c k) a) c d) ",
                "(lift_at (lift_at e c d) (Nat.add c (Nat.add d k)) a)"
            )
            .to_string(),
            value_src: Some(exchange_proof()),
            is_axiom: false,
            description: concat!(
                "Cross-cutoff lift exchange (non-collapsing): ",
                "lift(lift(e, c+k, a), c, d) = lift(lift(e, c, d), c+(d+k), a). ",
                "DerivedProved via KExpr.rec, bvar delegated to ",
                "lift_at_lift_at_exchange_bvar. The genuine lift/lift commutation ",
                "for the i=depth arm of lift_instantiate_swap. No new axiom. ",
                "Part of #2859 Wave 127 (Route B)."
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
                "lift_at_app".to_string(),
                "lift_at_lam".to_string(),
                "lift_at_let_".to_string(),
                "lift_at_pi".to_string(),
                "lift_at_lift_at_exchange_bvar".to_string(),
                "nat_succ_add".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

/// Build the bvar exchange proof term (triple Nat.rec convoy).
fn bvar_exchange_proof() -> String {
    // Abbreviations for the two goal sides.
    let lhs = "(lift_at (lift_at (KExpr.bvar j) (Nat.add c k) a) c d)";
    let rhs = "(lift_at (lift_at (KExpr.bvar j) c d) (Nat.add c (Nat.add d k)) a)";
    format!(
        concat!(
            "fun (j : Nat) (c : Nat) (k : Nat) (a : Nat) (d : Nat) => ",
            "Nat.rec ",
            "(fun (g : Nat) => Eq Nat (Nat.sub (Nat.add c k) j) g -> Eq KExpr {lhs} {rhs}) ",
            // ===== CASE A: sub(c+k, j) = 0  (j >= c+k) =====
            "(fun (h_ckj : Eq Nat (Nat.sub (Nat.add c k) j) Nat.zero) => ",
            // LHS: lift(bvar j, c+k, a) = bvar(j+a); then lift(., c, d) = bvar((j+a)+d).
            "Eq.trans KExpr {lhs} ",
            "(KExpr.bvar (Nat.add (Nat.add j a) d)) {rhs} ",
            "(Eq.trans KExpr {lhs} ",
            "(lift_at (KExpr.bvar (Nat.add j a)) c d) ",
            "(KExpr.bvar (Nat.add (Nat.add j a) d)) ",
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => lift_at x c d) ",
            "(lift_at (KExpr.bvar j) (Nat.add c k) a) (KExpr.bvar (Nat.add j a)) ",
            "(lift_at_bvar_geq j (Nat.add c k) a h_ckj)) ",
            "(lift_at_bvar_geq (Nat.add j a) c d ",
            // witness: sub c (j+a) = 0, from sub c j = 0 (via trans through c+k) then add_right
            "(nat_sub_zero_add_right c j a ",
            "(nat_sub_zero_trans c (Nat.add c k) j ",
            "(nat_sub_zero_add_right c c k (nat_sub_self c)) h_ckj)))) ",
            // RHS: lift(bvar j, c, d) = bvar(j+d); then lift(., c+(d+k), a) = bvar((j+d)+a).
            "(Eq.symm KExpr {rhs} ",
            "(KExpr.bvar (Nat.add (Nat.add j a) d)) ",
            "(Eq.trans KExpr {rhs} ",
            "(lift_at (KExpr.bvar (Nat.add j d)) (Nat.add c (Nat.add d k)) a) ",
            "(KExpr.bvar (Nat.add (Nat.add j a) d)) ",
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => lift_at x (Nat.add c (Nat.add d k)) a) ",
            "(lift_at (KExpr.bvar j) c d) (KExpr.bvar (Nat.add j d)) ",
            "(lift_at_bvar_geq j c d ",
            "(nat_sub_zero_trans c (Nat.add c k) j ",
            "(nat_sub_zero_add_right c c k (nat_sub_self c)) h_ckj))) ",
            "(Eq.trans KExpr ",
            "(lift_at (KExpr.bvar (Nat.add j d)) (Nat.add c (Nat.add d k)) a) ",
            "(KExpr.bvar (Nat.add (Nat.add j d) a)) ",
            "(KExpr.bvar (Nat.add (Nat.add j a) d)) ",
            // lift(bvar(j+d), c+(d+k), a) = bvar((j+d)+a); witness sub (c+(d+k)) (j+d) = 0
            "(lift_at_bvar_geq (Nat.add j d) (Nat.add c (Nat.add d k)) a ",
            // sub (c+(d+k)) (j+d) = 0. Build from sub (c+k) j = 0 via same-offset d then reassoc.
            "(Eq.trans Nat (Nat.sub (Nat.add c (Nat.add d k)) (Nat.add j d)) ",
            "(Nat.sub (Nat.add (Nat.add c k) d) (Nat.add j d)) Nat.zero ",
            "(Eq.cong Nat Nat (fun (x : Nat) => Nat.sub x (Nat.add j d)) ",
            "(Nat.add c (Nat.add d k)) (Nat.add (Nat.add c k) d) ",
            // c+(d+k) = (c+k)+d
            "(Eq.trans Nat (Nat.add c (Nat.add d k)) (Nat.add c (Nat.add k d)) ",
            "(Nat.add (Nat.add c k) d) ",
            "(Eq.cong Nat Nat (fun (x : Nat) => Nat.add c x) (Nat.add d k) (Nat.add k d) ",
            "(nat_add_comm d k)) ",
            "(Eq.symm Nat (Nat.add (Nat.add c k) d) (Nat.add c (Nat.add k d)) ",
            "(nat_add_assoc c k d)))) ",
            "(nat_sub_zero_add_same_right (Nat.add c k) j d h_ckj))) ",
            // bridge bvar((j+d)+a) = bvar((j+a)+d)
            "(Eq.cong Nat KExpr KExpr.bvar (Nat.add (Nat.add j d) a) (Nat.add (Nat.add j a) d) ",
            // (j+d)+a = j+(d+a) = j+(a+d) = (j+a)+d
            "(Eq.trans Nat (Nat.add (Nat.add j d) a) (Nat.add j (Nat.add d a)) ",
            "(Nat.add (Nat.add j a) d) ",
            "(nat_add_assoc j d a) ",
            "(Eq.trans Nat (Nat.add j (Nat.add d a)) (Nat.add j (Nat.add a d)) ",
            "(Nat.add (Nat.add j a) d) ",
            "(Eq.cong Nat Nat (fun (x : Nat) => Nat.add j x) (Nat.add d a) (Nat.add a d) ",
            "(nat_add_comm d a)) ",
            "(Eq.symm Nat (Nat.add (Nat.add j a) d) (Nat.add j (Nat.add a d)) ",
            "(nat_add_assoc j a d))))))))) ",
            // ===== CASE B: sub(c+k, j) = succ kk  (j < c+k) =====
            "(fun (kk : Nat) ",
            "(_ : Eq Nat (Nat.sub (Nat.add c k) j) kk -> Eq KExpr {lhs} {rhs}) ",
            "(h_ckj_s : Eq Nat (Nat.sub (Nat.add c k) j) (Nat.succ kk)) => ",
            // inner Nat.rec on sub(c, j)
            "Nat.rec ",
            "(fun (g2 : Nat) => Eq Nat (Nat.sub c j) g2 -> Eq KExpr {lhs} {rhs}) ",
            // --- B2: sub(c, j) = 0  (c <= j < c+k) ---
            "(fun (h_cj : Eq Nat (Nat.sub c j) Nat.zero) => ",
            // LHS: lift(bvar j, c+k, a) below -> bvar j; then lift(bvar j, c, d) geq -> bvar(j+d).
            "Eq.trans KExpr {lhs} (KExpr.bvar (Nat.add j d)) {rhs} ",
            "(Eq.trans KExpr {lhs} (lift_at (KExpr.bvar j) c d) (KExpr.bvar (Nat.add j d)) ",
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => lift_at x c d) ",
            "(lift_at (KExpr.bvar j) (Nat.add c k) a) (KExpr.bvar j) ",
            "(lift_at_bvar_below j (Nat.add c k) a ",
            "(nat_pos_witness_from_succ_eq (Nat.sub (Nat.add c k) j) kk h_ckj_s))) ",
            "(lift_at_bvar_geq j c d h_cj)) ",
            // RHS: lift(bvar j, c, d) geq -> bvar(j+d); then lift(., c+(d+k), a) below -> bvar(j+d).
            "(Eq.symm KExpr {rhs} (KExpr.bvar (Nat.add j d)) ",
            "(Eq.trans KExpr {rhs} ",
            "(lift_at (KExpr.bvar (Nat.add j d)) (Nat.add c (Nat.add d k)) a) ",
            "(KExpr.bvar (Nat.add j d)) ",
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => lift_at x (Nat.add c (Nat.add d k)) a) ",
            "(lift_at (KExpr.bvar j) c d) (KExpr.bvar (Nat.add j d)) ",
            "(lift_at_bvar_geq j c d h_cj)) ",
            // lift(bvar(j+d), c+(d+k), a) below -> bvar(j+d): need sub (c+(d+k)) (j+d) positive.
            "(lift_at_bvar_below (Nat.add j d) (Nat.add c (Nat.add d k)) a ",
            // positivity: sub (c+(d+k)) (j+d) = succ (...). Build from sub (c+k) j = succ kk.
            // sub (c+(d+k)) (j+d) = sub ((c+k)+d) (j+d) [reassoc] = positive from sub(c+k,j) via same offset d.
            "(Eq.trans Nat (Nat.sub (Nat.add c (Nat.add d k)) (Nat.add j d)) ",
            "(Nat.sub (Nat.add (Nat.add c k) d) (Nat.add j d)) ",
            "(Nat.succ (Nat.sub (Nat.sub (Nat.add c (Nat.add d k)) (Nat.add j d)) (Nat.succ Nat.zero))) ",
            "(Eq.cong Nat Nat (fun (x : Nat) => Nat.sub x (Nat.add j d)) ",
            "(Nat.add c (Nat.add d k)) (Nat.add (Nat.add c k) d) ",
            "(Eq.trans Nat (Nat.add c (Nat.add d k)) (Nat.add c (Nat.add k d)) ",
            "(Nat.add (Nat.add c k) d) ",
            "(Eq.cong Nat Nat (fun (x : Nat) => Nat.add c x) (Nat.add d k) (Nat.add k d) ",
            "(nat_add_comm d k)) ",
            "(Eq.symm Nat (Nat.add (Nat.add c k) d) (Nat.add c (Nat.add k d)) ",
            "(nat_add_assoc c k d)))) ",
            // now sub ((c+k)+d) (j+d) = succ((...)-1), and we must transport the succ tail back.
            "(Eq.trans Nat (Nat.sub (Nat.add (Nat.add c k) d) (Nat.add j d)) ",
            "(Nat.succ (Nat.sub (Nat.sub (Nat.add (Nat.add c k) d) (Nat.add j d)) (Nat.succ Nat.zero))) ",
            "(Nat.succ (Nat.sub (Nat.sub (Nat.add c (Nat.add d k)) (Nat.add j d)) (Nat.succ Nat.zero))) ",
            "(nat_sub_pos_add_same_right (Nat.add c k) j d ",
            "(nat_pos_witness_from_succ_eq (Nat.sub (Nat.add c k) j) kk h_ckj_s)) ",
            "(Eq.cong Nat Nat (fun (z : Nat) => Nat.succ (Nat.sub z (Nat.succ Nat.zero))) ",
            "(Nat.sub (Nat.add (Nat.add c k) d) (Nat.add j d)) ",
            "(Nat.sub (Nat.add c (Nat.add d k)) (Nat.add j d)) ",
            "(Eq.cong Nat Nat (fun (x : Nat) => Nat.sub x (Nat.add j d)) ",
            "(Nat.add (Nat.add c k) d) (Nat.add c (Nat.add d k)) ",
            "(Eq.trans Nat (Nat.add (Nat.add c k) d) (Nat.add c (Nat.add k d)) ",
            "(Nat.add c (Nat.add d k)) ",
            "(nat_add_assoc c k d) ",
            "(Eq.cong Nat Nat (fun (x : Nat) => Nat.add c x) (Nat.add k d) (Nat.add d k) ",
            "(nat_add_comm k d))))))))))) ",
            // --- B1: sub(c, j) = succ mm  (j < c) ---
            "(fun (mm : Nat) ",
            "(_ : Eq Nat (Nat.sub c j) mm -> Eq KExpr {lhs} {rhs}) ",
            "(h_cj_s : Eq Nat (Nat.sub c j) (Nat.succ mm)) => ",
            // Both sides reduce to bvar j. LHS: below (c+k) then below c. RHS: below c then below c+(d+k).
            "Eq.trans KExpr {lhs} (KExpr.bvar j) {rhs} ",
            "(Eq.trans KExpr {lhs} (lift_at (KExpr.bvar j) c d) (KExpr.bvar j) ",
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => lift_at x c d) ",
            "(lift_at (KExpr.bvar j) (Nat.add c k) a) (KExpr.bvar j) ",
            "(lift_at_bvar_below j (Nat.add c k) a ",
            "(nat_pos_witness_from_succ_eq (Nat.sub (Nat.add c k) j) kk h_ckj_s))) ",
            "(lift_at_bvar_below j c d ",
            "(nat_pos_witness_from_succ_eq (Nat.sub c j) mm h_cj_s))) ",
            "(Eq.symm KExpr {rhs} (KExpr.bvar j) ",
            "(Eq.trans KExpr {rhs} (lift_at (KExpr.bvar j) (Nat.add c (Nat.add d k)) a) (KExpr.bvar j) ",
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => lift_at x (Nat.add c (Nat.add d k)) a) ",
            "(lift_at (KExpr.bvar j) c d) (KExpr.bvar j) ",
            "(lift_at_bvar_below j c d ",
            "(nat_pos_witness_from_succ_eq (Nat.sub c j) mm h_cj_s))) ",
            // lift(bvar j, c+(d+k), a) below -> bvar j: sub (c+(d+k)) j positive from sub c j positive.
            "(lift_at_bvar_below j (Nat.add c (Nat.add d k)) a ",
            "(nat_sub_pos_add_right c (Nat.add d k) j ",
            "(nat_pos_witness_from_succ_eq (Nat.sub c j) mm h_cj_s)))))) ",
            "(Nat.sub c j) (Eq.refl Nat (Nat.sub c j))) ",
            "(Nat.sub (Nat.add c k) j) (Eq.refl Nat (Nat.sub (Nat.add c k) j))",
        ),
        lhs = lhs,
        rhs = rhs,
    )
}

/// Build the full-expression exchange proof term (KExpr.rec).
fn exchange_proof() -> String {
    // motive m(expr) := forall c k a d, Eq KExpr (lift(lift(expr,c+k,a),c,d)) (lift(lift(expr,c,d),c+(d+k),a))
    let motive = concat!(
        "(fun (expr : KExpr) => forall (c : Nat) (k : Nat) (a : Nat) (d : Nat), ",
        "Eq KExpr ",
        "(lift_at (lift_at expr (Nat.add c k) a) c d) ",
        "(lift_at (lift_at expr c d) (Nat.add c (Nat.add d k)) a))"
    );
    let ih_ty = concat!(
        "(ih_ty : forall (c : Nat) (k : Nat) (a : Nat) (d : Nat), ",
        "Eq KExpr (lift_at (lift_at ty (Nat.add c k) a) c d) ",
        "(lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a)) "
    );
    let ih_val = concat!(
        "(ih_val : forall (c : Nat) (k : Nat) (a : Nat) (d : Nat), ",
        "Eq KExpr (lift_at (lift_at val (Nat.add c k) a) c d) ",
        "(lift_at (lift_at val c d) (Nat.add c (Nat.add d k)) a)) "
    );
    let ih_body = concat!(
        "(ih_body : forall (c : Nat) (k : Nat) (a : Nat) (d : Nat), ",
        "Eq KExpr (lift_at (lift_at body (Nat.add c k) a) c d) ",
        "(lift_at (lift_at body c d) (Nat.add c (Nat.add d k)) a)) "
    );
    format!(
        concat!(
            "fun (e : KExpr) (c : Nat) (k : Nat) (a : Nat) (d : Nat) => ",
            "KExpr.rec {motive} ",
            // sort
            "(fun (sv : Level) (c : Nat) (k : Nat) (a : Nat) (d : Nat) => ",
            "Eq.refl KExpr (KExpr.sort sv)) ",
            // bvar
            "(fun (j : Nat) (c : Nat) (k : Nat) (a : Nat) (d : Nat) => ",
            "lift_at_lift_at_exchange_bvar j c k a d) ",
            // app
            "(fun (f : KExpr) (a0 : KExpr) ",
            "(ih_f : forall (c : Nat) (k : Nat) (a : Nat) (d : Nat), ",
            "Eq KExpr (lift_at (lift_at f (Nat.add c k) a) c d) ",
            "(lift_at (lift_at f c d) (Nat.add c (Nat.add d k)) a)) ",
            "(ih_a : forall (c : Nat) (k : Nat) (a : Nat) (d : Nat), ",
            "Eq KExpr (lift_at (lift_at a0 (Nat.add c k) a) c d) ",
            "(lift_at (lift_at a0 c d) (Nat.add c (Nat.add d k)) a)) ",
            "(c : Nat) (k : Nat) (a : Nat) (d : Nat) => ",
            // LHS lift(lift(app f a0, c+k, a), c, d)
            //   -> lift(app (lift f (c+k) a) (lift a0 (c+k) a), c, d)
            //   -> app (lift (lift f (c+k) a) c d) (lift (lift a0 (c+k) a) c d)
            // RHS lift(lift(app f a0, c, d), c+(d+k), a)
            //   -> app (lift (lift f c d) (c+(d+k)) a) (lift (lift a0 c d) (c+(d+k)) a)
            "Eq.trans KExpr ",
            "(lift_at (lift_at (KExpr.app f a0) (Nat.add c k) a) c d) ",
            "(KExpr.app (lift_at (lift_at f (Nat.add c k) a) c d) ",
            "(lift_at (lift_at a0 (Nat.add c k) a) c d)) ",
            "(lift_at (lift_at (KExpr.app f a0) c d) (Nat.add c (Nat.add d k)) a) ",
            // step 1: unfold LHS to app form
            "(Eq.trans KExpr ",
            "(lift_at (lift_at (KExpr.app f a0) (Nat.add c k) a) c d) ",
            "(lift_at (KExpr.app (lift_at f (Nat.add c k) a) (lift_at a0 (Nat.add c k) a)) c d) ",
            "(KExpr.app (lift_at (lift_at f (Nat.add c k) a) c d) ",
            "(lift_at (lift_at a0 (Nat.add c k) a) c d)) ",
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => lift_at x c d) ",
            "(lift_at (KExpr.app f a0) (Nat.add c k) a) ",
            "(KExpr.app (lift_at f (Nat.add c k) a) (lift_at a0 (Nat.add c k) a)) ",
            "(lift_at_app f a0 (Nat.add c k) a)) ",
            "(lift_at_app (lift_at f (Nat.add c k) a) (lift_at a0 (Nat.add c k) a) c d)) ",
            // step 2: apply IHs and fold RHS
            "(Eq.trans KExpr ",
            "(KExpr.app (lift_at (lift_at f (Nat.add c k) a) c d) ",
            "(lift_at (lift_at a0 (Nat.add c k) a) c d)) ",
            "(KExpr.app (lift_at (lift_at f c d) (Nat.add c (Nat.add d k)) a) ",
            "(lift_at (lift_at a0 c d) (Nat.add c (Nat.add d k)) a)) ",
            "(lift_at (lift_at (KExpr.app f a0) c d) (Nat.add c (Nat.add d k)) a) ",
            "(Eq.trans KExpr ",
            "(KExpr.app (lift_at (lift_at f (Nat.add c k) a) c d) ",
            "(lift_at (lift_at a0 (Nat.add c k) a) c d)) ",
            "(KExpr.app (lift_at (lift_at f c d) (Nat.add c (Nat.add d k)) a) ",
            "(lift_at (lift_at a0 (Nat.add c k) a) c d)) ",
            "(KExpr.app (lift_at (lift_at f c d) (Nat.add c (Nat.add d k)) a) ",
            "(lift_at (lift_at a0 c d) (Nat.add c (Nat.add d k)) a)) ",
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x ",
            "(lift_at (lift_at a0 (Nat.add c k) a) c d)) ",
            "(lift_at (lift_at f (Nat.add c k) a) c d) ",
            "(lift_at (lift_at f c d) (Nat.add c (Nat.add d k)) a) ",
            "(ih_f c k a d)) ",
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app ",
            "(lift_at (lift_at f c d) (Nat.add c (Nat.add d k)) a) x) ",
            "(lift_at (lift_at a0 (Nat.add c k) a) c d) ",
            "(lift_at (lift_at a0 c d) (Nat.add c (Nat.add d k)) a) ",
            "(ih_a c k a d))) ",
            // fold RHS app back: app (lift(lift f c d) .. ) (lift(lift a0 c d) ..) = lift(lift(app f a0,c,d),c+(d+k),a)
            "(Eq.symm KExpr ",
            "(lift_at (lift_at (KExpr.app f a0) c d) (Nat.add c (Nat.add d k)) a) ",
            "(KExpr.app (lift_at (lift_at f c d) (Nat.add c (Nat.add d k)) a) ",
            "(lift_at (lift_at a0 c d) (Nat.add c (Nat.add d k)) a)) ",
            "(Eq.trans KExpr ",
            "(lift_at (lift_at (KExpr.app f a0) c d) (Nat.add c (Nat.add d k)) a) ",
            "(lift_at (KExpr.app (lift_at f c d) (lift_at a0 c d)) (Nat.add c (Nat.add d k)) a) ",
            "(KExpr.app (lift_at (lift_at f c d) (Nat.add c (Nat.add d k)) a) ",
            "(lift_at (lift_at a0 c d) (Nat.add c (Nat.add d k)) a)) ",
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => lift_at x (Nat.add c (Nat.add d k)) a) ",
            "(lift_at (KExpr.app f a0) c d) ",
            "(KExpr.app (lift_at f c d) (lift_at a0 c d)) ",
            "(lift_at_app f a0 c d)) ",
            "(lift_at_app (lift_at f c d) (lift_at a0 c d) (Nat.add c (Nat.add d k)) a))))) ",
            // lam
            "(fun (ty : KExpr) (body : KExpr) {ih_ty}{ih_body}",
            "(c : Nat) (k : Nat) (a : Nat) (d : Nat) => {lam_arm}) ",
            // pi
            "(fun (ty : KExpr) (body : KExpr) {ih_ty}{ih_body}",
            "(c : Nat) (k : Nat) (a : Nat) (d : Nat) => {pi_arm}) ",
            // const
            "(fun (nm : Name) (us : ListType Level) ",
            "(c : Nat) (k : Nat) (a : Nat) (d : Nat) => ",
            "Eq.refl KExpr (KExpr.const nm us)) ",
            // let_
            "(fun (ty : KExpr) (val : KExpr) (body : KExpr) {ih_ty}{ih_val}{ih_body}",
            "(c : Nat) (k : Nat) (a : Nat) (d : Nat) => {let_arm}) ",
            // proj: 1-child node; ih_sub congruence (lift_at reduces through proj).
            "(fun (s : Name) (i : Nat) (sub : KExpr) ",
            "(ih_sub : forall (c : Nat) (k : Nat) (a : Nat) (d : Nat), Eq KExpr (lift_at (lift_at sub (Nat.add c k) a) c d) (lift_at (lift_at sub c d) (Nat.add c (Nat.add d k)) a)) ",
            "(c : Nat) (k : Nat) (a : Nat) (d : Nat) => ",
            "Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.proj s i x) (lift_at (lift_at sub (Nat.add c k) a) c d) (lift_at (lift_at sub c d) (Nat.add c (Nat.add d k)) a) (ih_sub c k a d)) ",
            // lit: leaf.
            "(fun (litn : Nat) (c : Nat) (k : Nat) (a : Nat) (d : Nat) => Eq.refl KExpr (KExpr.lit litn)) ",
            "e c k a d",
        ),
        motive = motive,
        ih_ty = ih_ty,
        ih_val = ih_val,
        ih_body = ih_body,
        lam_arm = lam_pi_arm("KExpr.lam", "lift_at_lam"),
        pi_arm = lam_pi_arm("KExpr.pi", "lift_at_pi"),
        let_arm = let_arm(),
    )
}

/// The lam/pi arm body, parametric in the constructor (`KExpr.lam`/`KExpr.pi`)
/// and its lift unfolder (`lift_at_lam`/`lift_at_pi`). Both have identical
/// structure: unfold both nested lifts each side, IH on ty at (c,k,a,d), IH on
/// body at (succ c, k, a, d) with the outer cutoff transport
/// succ(c+(d+k)) = (succ c)+(d+k) via nat_succ_add.
fn lam_pi_arm(ctor: &str, unfold: &str) -> String {
    format!(
        concat!(
            // LHS: lift(lift(C ty body, c+k, a), c, d)
            //  = lift(C (lift ty (c+k) a) (lift body (succ(c+k)) a), c, d)
            //  = C (lift (lift ty (c+k) a) c d) (lift (lift body (succ(c+k)) a) (succ c) d)
            "Eq.trans KExpr ",
            "(lift_at (lift_at ({ctor} ty body) (Nat.add c k) a) c d) ",
            "({ctor} (lift_at (lift_at ty (Nat.add c k) a) c d) ",
            "(lift_at (lift_at body (Nat.succ (Nat.add c k)) a) (Nat.succ c) d)) ",
            "(lift_at (lift_at ({ctor} ty body) c d) (Nat.add c (Nat.add d k)) a) ",
            // step1 unfold LHS
            "(Eq.trans KExpr ",
            "(lift_at (lift_at ({ctor} ty body) (Nat.add c k) a) c d) ",
            "(lift_at ({ctor} (lift_at ty (Nat.add c k) a) ",
            "(lift_at body (Nat.succ (Nat.add c k)) a)) c d) ",
            "({ctor} (lift_at (lift_at ty (Nat.add c k) a) c d) ",
            "(lift_at (lift_at body (Nat.succ (Nat.add c k)) a) (Nat.succ c) d)) ",
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => lift_at x c d) ",
            "(lift_at ({ctor} ty body) (Nat.add c k) a) ",
            "({ctor} (lift_at ty (Nat.add c k) a) (lift_at body (Nat.succ (Nat.add c k)) a)) ",
            "({unfold} ty body (Nat.add c k) a)) ",
            "({unfold} (lift_at ty (Nat.add c k) a) ",
            "(lift_at body (Nat.succ (Nat.add c k)) a) c d)) ",
            // step2: IH on ty, IH on body (with cutoff transport), fold RHS
            "(Eq.trans KExpr ",
            "({ctor} (lift_at (lift_at ty (Nat.add c k) a) c d) ",
            "(lift_at (lift_at body (Nat.succ (Nat.add c k)) a) (Nat.succ c) d)) ",
            "({ctor} (lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) ",
            "(lift_at (lift_at body (Nat.succ c) d) (Nat.add (Nat.succ c) (Nat.add d k)) a)) ",
            "(lift_at (lift_at ({ctor} ty body) c d) (Nat.add c (Nat.add d k)) a) ",
            // ty IH then body chain
            "(Eq.trans KExpr ",
            "({ctor} (lift_at (lift_at ty (Nat.add c k) a) c d) ",
            "(lift_at (lift_at body (Nat.succ (Nat.add c k)) a) (Nat.succ c) d)) ",
            "({ctor} (lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) ",
            "(lift_at (lift_at body (Nat.succ (Nat.add c k)) a) (Nat.succ c) d)) ",
            "({ctor} (lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) ",
            "(lift_at (lift_at body (Nat.succ c) d) (Nat.add (Nat.succ c) (Nat.add d k)) a)) ",
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => {ctor} x ",
            "(lift_at (lift_at body (Nat.succ (Nat.add c k)) a) (Nat.succ c) d)) ",
            "(lift_at (lift_at ty (Nat.add c k) a) c d) ",
            "(lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) ",
            "(ih_ty c k a d)) ",
            // body: cong on second slot. Need:
            //   lift (lift body (succ(c+k)) a) (succ c) d = lift (lift body (succ c) d) ((succ c)+(d+k)) a
            // The body IH at (succ c, k, a, d) gives:
            //   lift (lift body ((succ c)+k) a) (succ c) d = lift (lift body (succ c) d) ((succ c)+(d+k)) a
            // and succ(c+k) = (succ c)+k by nat_succ_add. Transport the inner cutoff.
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => {ctor} ",
            "(lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) x) ",
            "(lift_at (lift_at body (Nat.succ (Nat.add c k)) a) (Nat.succ c) d) ",
            "(lift_at (lift_at body (Nat.succ c) d) (Nat.add (Nat.succ c) (Nat.add d k)) a) ",
            "(Eq.trans KExpr ",
            "(lift_at (lift_at body (Nat.succ (Nat.add c k)) a) (Nat.succ c) d) ",
            "(lift_at (lift_at body (Nat.add (Nat.succ c) k) a) (Nat.succ c) d) ",
            "(lift_at (lift_at body (Nat.succ c) d) (Nat.add (Nat.succ c) (Nat.add d k)) a) ",
            // transport inner cutoff succ(c+k) -> (succ c)+k
            "(Eq.cong Nat KExpr ",
            "(fun (n : Nat) => lift_at (lift_at body n a) (Nat.succ c) d) ",
            "(Nat.succ (Nat.add c k)) (Nat.add (Nat.succ c) k) ",
            "(Eq.symm Nat (Nat.add (Nat.succ c) k) (Nat.succ (Nat.add c k)) ",
            "(nat_succ_add c k))) ",
            "(ih_body (Nat.succ c) k a d)))) ",
            // fold RHS: C (lift(lift ty c d) ..) (lift(lift body (succ c) d) ((succ c)+(d+k)) a)
            //   transport (succ c)+(d+k) -> succ(c+(d+k)) and fold via unfold lemma.
            "(Eq.symm KExpr ",
            "(lift_at (lift_at ({ctor} ty body) c d) (Nat.add c (Nat.add d k)) a) ",
            "({ctor} (lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) ",
            "(lift_at (lift_at body (Nat.succ c) d) (Nat.add (Nat.succ c) (Nat.add d k)) a)) ",
            "(Eq.trans KExpr ",
            "(lift_at (lift_at ({ctor} ty body) c d) (Nat.add c (Nat.add d k)) a) ",
            "(lift_at ({ctor} (lift_at ty c d) (lift_at body (Nat.succ c) d)) ",
            "(Nat.add c (Nat.add d k)) a) ",
            "({ctor} (lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) ",
            "(lift_at (lift_at body (Nat.succ c) d) (Nat.add (Nat.succ c) (Nat.add d k)) a)) ",
            "(Eq.cong KExpr KExpr (fun (x : KExpr) => lift_at x (Nat.add c (Nat.add d k)) a) ",
            "(lift_at ({ctor} ty body) c d) ",
            "({ctor} (lift_at ty c d) (lift_at body (Nat.succ c) d)) ",
            "({unfold} ty body c d)) ",
            // unfold outer lift on C, producing body cutoff succ(c+(d+k)); transport to (succ c)+(d+k)
            "(Eq.trans KExpr ",
            "(lift_at ({ctor} (lift_at ty c d) (lift_at body (Nat.succ c) d)) ",
            "(Nat.add c (Nat.add d k)) a) ",
            "({ctor} (lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) ",
            "(lift_at (lift_at body (Nat.succ c) d) (Nat.succ (Nat.add c (Nat.add d k))) a)) ",
            "({ctor} (lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) ",
            "(lift_at (lift_at body (Nat.succ c) d) (Nat.add (Nat.succ c) (Nat.add d k)) a)) ",
            "({unfold} (lift_at ty c d) (lift_at body (Nat.succ c) d) ",
            "(Nat.add c (Nat.add d k)) a) ",
            "(Eq.cong Nat KExpr ",
            "(fun (n : Nat) => {ctor} ",
            "(lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) ",
            "(lift_at (lift_at body (Nat.succ c) d) n a)) ",
            "(Nat.succ (Nat.add c (Nat.add d k))) (Nat.add (Nat.succ c) (Nat.add d k)) ",
            "(Eq.symm Nat (Nat.add (Nat.succ c) (Nat.add d k)) ",
            "(Nat.succ (Nat.add c (Nat.add d k))) ",
            "(nat_succ_add c (Nat.add d k))))))))",
        ),
        ctor = ctor,
        unfold = unfold,
    )
}

/// The let_ arm body for the full-expression exchange. Structurally mirrors
/// `lam_pi_arm` but for the three-field `KExpr.let_`: unfold both nested lifts
/// each side via `lift_at_let_`, IH on ty and val at (c,k,a,d), IH on body at
/// (succ c, k, a, d) with the inner/outer cutoff transports via nat_succ_add.
fn let_arm() -> String {
    concat!(
        "Eq.trans KExpr ",
        "(lift_at (lift_at (KExpr.let_ ty val body) (Nat.add c k) a) c d) ",
        "(KExpr.let_ (lift_at (lift_at ty (Nat.add c k) a) c d) ",
        "(lift_at (lift_at val (Nat.add c k) a) c d) ",
        "(lift_at (lift_at body (Nat.succ (Nat.add c k)) a) (Nat.succ c) d)) ",
        "(lift_at (lift_at (KExpr.let_ ty val body) c d) (Nat.add c (Nat.add d k)) a) ",
        "(Eq.trans KExpr ",
        "(lift_at (lift_at (KExpr.let_ ty val body) (Nat.add c k) a) c d) ",
        "(lift_at (KExpr.let_ (lift_at ty (Nat.add c k) a) ",
        "(lift_at val (Nat.add c k) a) ",
        "(lift_at body (Nat.succ (Nat.add c k)) a)) c d) ",
        "(KExpr.let_ (lift_at (lift_at ty (Nat.add c k) a) c d) ",
        "(lift_at (lift_at val (Nat.add c k) a) c d) ",
        "(lift_at (lift_at body (Nat.succ (Nat.add c k)) a) (Nat.succ c) d)) ",
        "(Eq.cong KExpr KExpr (fun (x : KExpr) => lift_at x c d) ",
        "(lift_at (KExpr.let_ ty val body) (Nat.add c k) a) ",
        "(KExpr.let_ (lift_at ty (Nat.add c k) a) (lift_at val (Nat.add c k) a) ",
        "(lift_at body (Nat.succ (Nat.add c k)) a)) ",
        "(lift_at_let_ ty val body (Nat.add c k) a)) ",
        "(lift_at_let_ (lift_at ty (Nat.add c k) a) (lift_at val (Nat.add c k) a) ",
        "(lift_at body (Nat.succ (Nat.add c k)) a) c d)) ",
        "(Eq.trans KExpr ",
        "(KExpr.let_ (lift_at (lift_at ty (Nat.add c k) a) c d) ",
        "(lift_at (lift_at val (Nat.add c k) a) c d) ",
        "(lift_at (lift_at body (Nat.succ (Nat.add c k)) a) (Nat.succ c) d)) ",
        "(KExpr.let_ (lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (lift_at val c d) (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (lift_at body (Nat.succ c) d) (Nat.add (Nat.succ c) (Nat.add d k)) a)) ",
        "(lift_at (lift_at (KExpr.let_ ty val body) c d) (Nat.add c (Nat.add d k)) a) ",
        "(Eq.trans KExpr ",
        "(KExpr.let_ (lift_at (lift_at ty (Nat.add c k) a) c d) ",
        "(lift_at (lift_at val (Nat.add c k) a) c d) ",
        "(lift_at (lift_at body (Nat.succ (Nat.add c k)) a) (Nat.succ c) d)) ",
        "(KExpr.let_ (lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (lift_at val (Nat.add c k) a) c d) ",
        "(lift_at (lift_at body (Nat.succ (Nat.add c k)) a) (Nat.succ c) d)) ",
        "(KExpr.let_ (lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (lift_at val c d) (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (lift_at body (Nat.succ c) d) (Nat.add (Nat.succ c) (Nat.add d k)) a)) ",
        "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.let_ x ",
        "(lift_at (lift_at val (Nat.add c k) a) c d) ",
        "(lift_at (lift_at body (Nat.succ (Nat.add c k)) a) (Nat.succ c) d)) ",
        "(lift_at (lift_at ty (Nat.add c k) a) c d) ",
        "(lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) ",
        "(ih_ty c k a d)) ",
        "(Eq.trans KExpr ",
        "(KExpr.let_ (lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (lift_at val (Nat.add c k) a) c d) ",
        "(lift_at (lift_at body (Nat.succ (Nat.add c k)) a) (Nat.succ c) d)) ",
        "(KExpr.let_ (lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (lift_at val c d) (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (lift_at body (Nat.succ (Nat.add c k)) a) (Nat.succ c) d)) ",
        "(KExpr.let_ (lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (lift_at val c d) (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (lift_at body (Nat.succ c) d) (Nat.add (Nat.succ c) (Nat.add d k)) a)) ",
        "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.let_ ",
        "(lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) x ",
        "(lift_at (lift_at body (Nat.succ (Nat.add c k)) a) (Nat.succ c) d)) ",
        "(lift_at (lift_at val (Nat.add c k) a) c d) ",
        "(lift_at (lift_at val c d) (Nat.add c (Nat.add d k)) a) ",
        "(ih_val c k a d)) ",
        "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.let_ ",
        "(lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (lift_at val c d) (Nat.add c (Nat.add d k)) a) x) ",
        "(lift_at (lift_at body (Nat.succ (Nat.add c k)) a) (Nat.succ c) d) ",
        "(lift_at (lift_at body (Nat.succ c) d) (Nat.add (Nat.succ c) (Nat.add d k)) a) ",
        "(Eq.trans KExpr ",
        "(lift_at (lift_at body (Nat.succ (Nat.add c k)) a) (Nat.succ c) d) ",
        "(lift_at (lift_at body (Nat.add (Nat.succ c) k) a) (Nat.succ c) d) ",
        "(lift_at (lift_at body (Nat.succ c) d) (Nat.add (Nat.succ c) (Nat.add d k)) a) ",
        "(Eq.cong Nat KExpr ",
        "(fun (n : Nat) => lift_at (lift_at body n a) (Nat.succ c) d) ",
        "(Nat.succ (Nat.add c k)) (Nat.add (Nat.succ c) k) ",
        "(Eq.symm Nat (Nat.add (Nat.succ c) k) (Nat.succ (Nat.add c k)) ",
        "(nat_succ_add c k))) ",
        "(ih_body (Nat.succ c) k a d))))) ",
        "(Eq.symm KExpr ",
        "(lift_at (lift_at (KExpr.let_ ty val body) c d) (Nat.add c (Nat.add d k)) a) ",
        "(KExpr.let_ (lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (lift_at val c d) (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (lift_at body (Nat.succ c) d) (Nat.add (Nat.succ c) (Nat.add d k)) a)) ",
        "(Eq.trans KExpr ",
        "(lift_at (lift_at (KExpr.let_ ty val body) c d) (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (KExpr.let_ (lift_at ty c d) (lift_at val c d) (lift_at body (Nat.succ c) d)) ",
        "(Nat.add c (Nat.add d k)) a) ",
        "(KExpr.let_ (lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (lift_at val c d) (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (lift_at body (Nat.succ c) d) (Nat.add (Nat.succ c) (Nat.add d k)) a)) ",
        "(Eq.cong KExpr KExpr (fun (x : KExpr) => lift_at x (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (KExpr.let_ ty val body) c d) ",
        "(KExpr.let_ (lift_at ty c d) (lift_at val c d) (lift_at body (Nat.succ c) d)) ",
        "(lift_at_let_ ty val body c d)) ",
        "(Eq.trans KExpr ",
        "(lift_at (KExpr.let_ (lift_at ty c d) (lift_at val c d) (lift_at body (Nat.succ c) d)) ",
        "(Nat.add c (Nat.add d k)) a) ",
        "(KExpr.let_ (lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (lift_at val c d) (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (lift_at body (Nat.succ c) d) (Nat.succ (Nat.add c (Nat.add d k))) a)) ",
        "(KExpr.let_ (lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (lift_at val c d) (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (lift_at body (Nat.succ c) d) (Nat.add (Nat.succ c) (Nat.add d k)) a)) ",
        "(lift_at_let_ (lift_at ty c d) (lift_at val c d) (lift_at body (Nat.succ c) d) ",
        "(Nat.add c (Nat.add d k)) a) ",
        "(Eq.cong Nat KExpr ",
        "(fun (n : Nat) => KExpr.let_ ",
        "(lift_at (lift_at ty c d) (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (lift_at val c d) (Nat.add c (Nat.add d k)) a) ",
        "(lift_at (lift_at body (Nat.succ c) d) n a)) ",
        "(Nat.succ (Nat.add c (Nat.add d k))) (Nat.add (Nat.succ c) (Nat.add d k)) ",
        "(Eq.symm Nat (Nat.add (Nat.succ c) (Nat.add d k)) ",
        "(Nat.succ (Nat.add c (Nat.add d k))) ",
        "(nat_succ_add c (Nat.add d k))))))))",
    )
    .to_string()
}

#[cfg(test)]
mod tests {
    use crate::spec::types::ProofStatus;
    use crate::test_utils::run_with_stack;
    use crate::Specification;

    #[test]
    fn test_lift_exchange_family_is_constructive() {
        let spec = run_with_stack(|| {
            Specification::new_substitution_test_spec()
                .expect("substitution/WHNF test spec should build")
        });

        for name in ["lift_at_lift_at_exchange_bvar", "lift_at_lift_at_exchange"] {
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
