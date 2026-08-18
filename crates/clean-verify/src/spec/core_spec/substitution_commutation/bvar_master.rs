// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Master bvar nested-commutation theorem split from substitution_commutation.rs.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_substitution_commutation_bvar_master(&mut self) -> Result<(), SpecError> {
        // ── Master bvar theorem: instantiate_at_nested_commutes_bvar ──
        //
        // Wires the three sub-case helpers together via a double Nat.rec convoy:
        //   outer convoy on `sub sd i`:
        //     - succ k (i < sd): below case
        //     - 0 (i >= sd): inner convoy on `sub i sd`:
        //       - 0 (i = sd): equal case (modulo subst_lift_interchange)
        //       - succ gap (i > sd): above case (modulo lift_at_shift_succ)
        //
        // DerivedProved modulo
        // {subst_lift_interchange, lift_at_shift_succ via the above helper}.
        // Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_nested_commutes_bvar".to_string(),
            type_src: concat!(
                "forall (i : Nat) (arg : KExpr) (w : KExpr) ",
                "(subst_depth : Nat) (outer_depth : Nat), ",
                "Eq KExpr ",
                "(instantiate_at (instantiate_at (KExpr.bvar i) arg subst_depth) w ",
                "(Nat.add subst_depth outer_depth)) ",
                "(instantiate_at (instantiate_at (KExpr.bvar i) w ",
                "(Nat.succ (Nat.add subst_depth outer_depth))) ",
                "(instantiate_at arg w outer_depth) subst_depth)",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (i : Nat) (arg : KExpr) (w : KExpr) ",
                    "(subst_depth : Nat) (outer_depth : Nat) => ",
                    "Nat.rec ",
                    "(fun (d : Nat) => ",
                    "Eq Nat (Nat.sub subst_depth i) d -> ",
                    "Eq KExpr ",
                    "(instantiate_at (instantiate_at (KExpr.bvar i) arg subst_depth) w ",
                    "(Nat.add subst_depth outer_depth)) ",
                    "(instantiate_at (instantiate_at (KExpr.bvar i) w ",
                    "(Nat.succ (Nat.add subst_depth outer_depth))) ",
                    "(instantiate_at arg w outer_depth) subst_depth)) ",
                    "(fun (h_sd_leq_i : Eq Nat (Nat.sub subst_depth i) Nat.zero) => ",
                    "Nat.rec ",
                    "(fun (g : Nat) => ",
                    "Eq Nat (Nat.sub i subst_depth) g -> ",
                    "Eq KExpr ",
                    "(instantiate_at (instantiate_at (KExpr.bvar i) arg subst_depth) w ",
                    "(Nat.add subst_depth outer_depth)) ",
                    "(instantiate_at (instantiate_at (KExpr.bvar i) w ",
                    "(Nat.succ (Nat.add subst_depth outer_depth))) ",
                    "(instantiate_at arg w outer_depth) subst_depth)) ",
                    "(fun (h_i_leq_sd : Eq Nat (Nat.sub i subst_depth) Nat.zero) => ",
                    "instantiate_at_nested_commutes_bvar_equal i arg w ",
                    "subst_depth outer_depth h_sd_leq_i h_i_leq_sd) ",
                    "(fun (gap : Nat) ",
                    "(_ : Eq Nat (Nat.sub i subst_depth) gap -> ",
                    "Eq KExpr ",
                    "(instantiate_at (instantiate_at (KExpr.bvar i) arg subst_depth) w ",
                    "(Nat.add subst_depth outer_depth)) ",
                    "(instantiate_at (instantiate_at (KExpr.bvar i) w ",
                    "(Nat.succ (Nat.add subst_depth outer_depth))) ",
                    "(instantiate_at arg w outer_depth) subst_depth)) ",
                    "(h_gap : Eq Nat (Nat.sub i subst_depth) (Nat.succ gap)) => ",
                    "instantiate_at_nested_commutes_bvar_above i arg w ",
                    "subst_depth outer_depth h_sd_leq_i gap h_gap) ",
                    "(Nat.sub i subst_depth) ",
                    "(Eq.refl Nat (Nat.sub i subst_depth))) ",
                    "(fun (k : Nat) ",
                    "(_ : Eq Nat (Nat.sub subst_depth i) k -> ",
                    "Eq KExpr ",
                    "(instantiate_at (instantiate_at (KExpr.bvar i) arg subst_depth) w ",
                    "(Nat.add subst_depth outer_depth)) ",
                    "(instantiate_at (instantiate_at (KExpr.bvar i) w ",
                    "(Nat.succ (Nat.add subst_depth outer_depth))) ",
                    "(instantiate_at arg w outer_depth) subst_depth)) ",
                    "(h_below : Eq Nat (Nat.sub subst_depth i) (Nat.succ k)) => ",
                    "instantiate_at_nested_commutes_bvar_below i arg w ",
                    "subst_depth outer_depth ",
                    "(Eq.trans Nat ",
                    "(Nat.sub subst_depth i) ",
                    "(Nat.succ k) ",
                    "(Nat.succ (Nat.sub (Nat.sub subst_depth i) (Nat.succ Nat.zero))) ",
                    "h_below ",
                    "(Eq.cong Nat Nat Nat.succ ",
                    "k ",
                    "(Nat.sub (Nat.sub subst_depth i) (Nat.succ Nat.zero)) ",
                    "(Eq.symm Nat ",
                    "(Nat.sub (Nat.sub subst_depth i) (Nat.succ Nat.zero)) ",
                    "k ",
                    "(Eq.trans Nat ",
                    "(Nat.sub (Nat.sub subst_depth i) (Nat.succ Nat.zero)) ",
                    "(Nat.sub (Nat.succ k) (Nat.succ Nat.zero)) ",
                    "k ",
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.sub x (Nat.succ Nat.zero)) ",
                    "(Nat.sub subst_depth i) ",
                    "(Nat.succ k) ",
                    "h_below) ",
                    "(nat_sub_succ_one k)))))) ",
                    "(Nat.sub subst_depth i) ",
                    "(Eq.refl Nat (Nat.sub subst_depth i))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "BVar case of binder-aware nested substitution commutation. ",
                "Wires below + equal + above cases via double Nat.rec convoy on ",
                "sub(sd,i) and sub(i,sd). DerivedProved modulo ",
                "subst_lift_interchange (from equal case) and ",
                "lift_at_shift_succ via instantiate_at_nested_commutes_bvar_above. ",
                "Part of #464.",
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
                "instantiate_at_nested_commutes_bvar_above".to_string(),
                "instantiate_at_nested_commutes_bvar_below".to_string(),
                "instantiate_at_nested_commutes_bvar_equal".to_string(),
                "nat_sub_succ_one".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::spec::ProofStatus;
    use crate::Specification;

    fn build_substitution_spec_with_stack() -> Specification {
        crate::test_utils::build_substitution_spec_with_stack()
    }

    #[test]
    fn test_nested_commutes_bvar_master_tracks_leaf_blockers() {
        let spec = build_substitution_spec_with_stack();
        let def = spec
            .definitions()
            .get("instantiate_at_nested_commutes_bvar")
            .expect("instantiate_at_nested_commutes_bvar should exist");

        assert!(
            def.value_src.is_some(),
            "master bvar theorem should have an explicit proof term"
        );
        assert!(
            !def.is_axiom,
            "master bvar theorem should not be a helper axiom"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "master bvar theorem should stay DerivedProved modulo its remaining blockers"
        );

        let actual = def
            .axiom_deps
            .iter()
            .map(String::as_str)
            .collect::<BTreeSet<_>>();
        let expected = BTreeSet::<&str>::new();
        assert_eq!(
            actual, expected,
            "master bvar theorem should have empty axiom_deps (all leaf blockers DerivedProved)"
        );
    }
}
