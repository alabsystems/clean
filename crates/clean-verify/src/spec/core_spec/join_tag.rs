// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Two rigid-headed terms with a common reduct have the **same head tag**.
//!
//! ```text
//! rigid_join_same_tag :
//!   rigid_app_head na -> rigid_app_head nb
//!     -> par_reduces_cd_star env na w -> par_reduces_cd_star env nb w
//!     -> Eq Nat (kexpr_tag na) (kexpr_tag nb)
//! ```
//!
//! One `Eq.trans` through the common reduct, given the one-sided preservation
//! lemma. That brevity is the point: the same conclusion reached by reasoning
//! about *pairs* of heads is a 7×7 grid with 42 cross-head absurdities. Here the
//! 42 collapse into a single arithmetic equation.
//!
//! Also registered: `nat_discr_t` / `nat_discr_p`, the `Nat` analogue of
//! `kexpr_discr`. At two concrete distinct numerals `nat_eqb` *computes* to
//! `false`, so the mismatch premise is always `Eq.refl Bool Bool.false` and the
//! caller supplies nothing — which is what makes the head grid's off-diagonal
//! cases one-liners rather than proofs. Both universe variants are provided up
//! front; the Prop/Type split has cost a full spec build five times in this
//! program, every time from shipping half a pair.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Same-tag agreement, and `Nat` discrimination.
    pub(super) fn add_join_tag(&mut self) -> Result<(), SpecError> {
        self.add_nat_discriminators()?;
        self.add_rigid_join_same_tag()?;
        Ok(())
    }

    /// `Nat` constructor discrimination, both universes.
    fn add_nat_discriminators(&mut self) -> Result<(), SpecError> {
        for (name, univ, absurd) in [
            ("nat_discr_t", "Type", "bool_false_ne_true_t"),
            ("nat_discr_p", "Prop", "bool_false_ne_true"),
        ] {
            self.add_recursive_def(
                &format!(
                    "def {name} (C : {univ}) (m : Nat) (n : Nat) (h : Eq Nat m n) \
                     (hne : Eq Bool (nat_eqb m n) Bool.false) : C := \
                     {absurd} C \
                     (Eq.trans Bool Bool.false (nat_eqb m n) Bool.true \
                     (Eq.symm Bool (nat_eqb m n) Bool.false hne) \
                     (Eq.substType Nat (fun (z : Nat) => Eq Bool (nat_eqb m z) Bool.true) \
                     m n h (nat_eqb_refl m)))"
                ),
                &format!(
                    "{name}: distinct naturals cannot be equal, so any {univ} follows. The Nat \
                     analogue of kexpr_discr, and used the same way: at two concrete numerals \
                     nat_eqb COMPUTES to false, so the mismatch premise is literally \
                     `Eq.refl Bool Bool.false` and callers write nothing. This is what turns the \
                     head grid's off-diagonal cases into one-liners — a tag mismatch is \
                     arithmetic, not a proof obligation. DerivedProved, zero axiom_deps."
                ),
            )?;
        }
        Ok(())
    }

    fn add_rigid_join_same_tag(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def rigid_join_same_tag (env : RedEnv) (na : KExpr) (nb : KExpr) (w : KExpr) \
             (hra : rigid_app_head na) (hrb : rigid_app_head nb) \
             (hsa : par_reduces_cd_star env na w) (hsb : par_reduces_cd_star env nb w) : \
             Eq Nat (kexpr_tag na) (kexpr_tag nb) := \
             Eq.trans Nat (kexpr_tag na) (kexpr_tag w) (kexpr_tag nb) \
             (rigid_app_head_star_preserves_tag env na hra w hsa) \
             (Eq.symm Nat (kexpr_tag nb) (kexpr_tag w) \
             (rigid_app_head_star_preserves_tag env nb hrb w hsb))",
            "rigid_join_same_tag: two rigid-headed terms that reduce to a COMMON REDUCT have the \
             same head tag. One Eq.trans through that reduct, given one-sided tag preservation. \
             The brevity is the whole point of the tag factoring: the same conclusion via a grid \
             over pairs of heads is 7 diagonal cases plus 42 cross-head absurdities, whereas here \
             the 42 collapse into a single arithmetic equation that nat_discr dispatches. This is \
             the form the completeness capstone consumes after the three diamonds hand it a common \
             meet for the two normal forms. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    /// Both universe variants must exist. Shipping half a Prop/Type pair has
    /// cost a full ~21-minute spec build five separate times in this program.
    #[test]
    fn test_nat_discriminators_provide_both_universes() {
        let src = include_str!("join_tag.rs");
        let impl_body = src
            .split("fn add_nat_discriminators")
            .nth(1)
            .expect("the generator is present");
        for (name, absurd) in [
            ("nat_discr_t", "bool_false_ne_true_t"),
            ("nat_discr_p", "bool_false_ne_true"),
        ] {
            assert!(impl_body.contains(name), "missing variant: {name}");
            assert!(impl_body.contains(absurd), "{name} must pair with {absurd}");
        }
    }

    /// `rigid_join_same_tag` must go through the common reduct on BOTH sides.
    /// A version that used only one leg would be claiming something stronger
    /// and false.
    #[test]
    fn test_same_tag_uses_both_legs() {
        let src = include_str!("join_tag.rs");
        let term_start = src
            .find("def rigid_join_same_tag")
            .expect("declaration present");
        let term = &src[term_start..src[term_start..].find("\",\n").unwrap() + term_start];
        assert_eq!(
            term.matches("rigid_app_head_star_preserves_tag env")
                .count(),
            2,
            "both legs must be pushed to the common reduct — one leg alone proves nothing about \
             the other term's head"
        );
        assert!(
            term.contains("(kexpr_tag w)"),
            "the transitivity must pass through the common reduct's tag"
        );
    }
}
