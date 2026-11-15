// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Additive semantic sort and Pi injectivity, preserving the legacy raw theory.
//!
//! SemanticJoin has two actual raw-star legs and universe-related endpoints.
//! Raw sort rigidity and Pi shape inversions are reused unchanged. Sort
//! conclusions are levelEqSem, never Eq Level; Pi conclusions are constructed
//! component DefEqIn derivations. Only DefEqIn-to-join corollaries require the
//! existing RedEnvFaithful interfaces. No typing or output-join premise is added.
//!
//! Unregistered proof-development unit. Independent exact-source checking and
//! registered whole-corpus replay are separate gates. This is not production
//! kernel refinement, environment-validity discharge, or semantic normalization.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Requires SemanticJoin and its proved DefEqIn inclusion, plus existing
    /// generic raw-star sort/Pi inverters and universe-relation views.
    pub(super) fn add_semantic_injectivity(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            r"def par_reduces_cd_star_to_def_eq_in (R : RedEnv) (a : KExpr) (b : KExpr)
 (h : par_reduces_cd_star R a b) : DefEqIn R a b :=
 par_reduces_cd_star.rec R
  (fun (x : KExpr) (y : KExpr) (_h : par_reduces_cd_star R x y) => DefEqIn R x y)
  (fun (x : KExpr) => DefEqIn.refl R x)
  (fun (x : KExpr) (y : KExpr) (z : KExpr) (xy : par_reduces_cd R x y)
    (_yz : par_reduces_cd_star R y z) (ih : DefEqIn R y z) =>
    DefEqIn.trans R x y z (DefEqIn.raw R x y xy) ih) a b h",
            "An actual finite raw parallel path embeds by induction into the supplied-environment semantic conversion relation.",
        )?;

        self.add_recursive_def(
            r"def semantic_join_to_def_eq_in (R : RedEnv) (a : KExpr) (b : KExpr)
 (h : SemanticJoin R a b) : DefEqIn R a b :=
 SemanticJoin.rec R a b (fun (_h : SemanticJoin R a b) => DefEqIn R a b)
  (fun (x : KExpr) (y : KExpr) (ax : par_reduces_cd_star R a x)
    (by_path : par_reduces_cd_star R b y) (xy : KExprUniverseEq x y) =>
    DefEqIn.trans R a x b (par_reduces_cd_star_to_def_eq_in R a x ax)
      (DefEqIn.trans R x y b (DefEqIn.levels R x y xy)
        (DefEqIn.symm R b y (par_reduces_cd_star_to_def_eq_in R b y by_path)))) h",
            "The two actual join legs and the endpoint universe relation construct conversion; no faithfulness or extra joinability premise is required for this direction.",
        )?;

        self.add_recursive_def(
            r"def kexprUniverseEq_sort_injective (u : Level) (v : Level)
 (h : KExprUniverseEq (KExpr.sort u) (KExpr.sort v)) : levelEqSem u v :=
 LiftP.rec (levelEqSem u v) (fun (_ : LiftP (levelEqSem u v)) => levelEqSem u v)
  (fun (p : levelEqSem u v) => p)
  (kexprUniverseEq_view (KExpr.sort u) (KExpr.sort v) h (LiftP (levelEqSem u v))
    (fun (w : Level) (uw : levelEqSem u w)
      (vw : Eq KExpr (KExpr.sort v) (KExpr.sort w)) =>
      LiftP.up (levelEqSem u v)
        (Eq.subst Level (fun (z : Level) => levelEqSem u z) w v
          (Eq.symm Level v w (kexpr_sort_inj v w vw)) uw)))",
            "Sort-level relation inversion yields equality of denotations, not equality of raw Level syntax. LiftP only adapts the existing Type-valued inversion API.",
        )?;

        self.add_recursive_def(
            r"def kexprUniverseEq_pi_components (A : KExpr) (B : KExpr)
 (A2 : KExpr) (B2 : KExpr) (h : KExprUniverseEq (KExpr.pi A B) (KExpr.pi A2 B2))
 (C : Type) (consume : KExprUniverseEq A A2 -> KExprUniverseEq B B2 -> C) : C :=
 kexprUniverseEq_view (KExpr.pi A B) (KExpr.pi A2 B2) h C
  (fun (A3 : KExpr) (B3 : KExpr) (hA : KExprUniverseEq A A3)
    (hB : KExprUniverseEq B B3) (shape : Eq KExpr (KExpr.pi A2 B2) (KExpr.pi A3 B3)) =>
    consume
      (Eq.substType KExpr (fun (z : KExpr) => KExprUniverseEq A z) A3 A2
        (Eq.symm KExpr A2 A3 (kexpr_pi_inj_fst A2 B2 A3 B3 shape)) hA)
      (Eq.substType KExpr (fun (z : KExpr) => KExprUniverseEq B z) B3 B2
        (Eq.symm KExpr B2 B3 (kexpr_pi_inj_snd A2 B2 A3 B3 shape)) hB))",
            "Actual constructor-view inversion derives both pointwise Pi relations; it does not erase or assume agreement of binder components.",
        )?;

        self.add_recursive_def(
            r"def semantic_join_sort_injective (R : RedEnv) (u : Level) (v : Level)
 (h : SemanticJoin R (KExpr.sort u) (KExpr.sort v)) : levelEqSem u v :=
 SemanticJoin.rec R (KExpr.sort u) (KExpr.sort v)
  (fun (_h : SemanticJoin R (KExpr.sort u) (KExpr.sort v)) => levelEqSem u v)
  (fun (x : KExpr) (y : KExpr)
    (ux : par_reduces_cd_star R (KExpr.sort u) x)
    (vy : par_reduces_cd_star R (KExpr.sort v) y) (xy : KExprUniverseEq x y) =>
    kexprUniverseEq_sort_injective u v
      (Eq.substType KExpr (fun (z : KExpr) => KExprUniverseEq (KExpr.sort u) z)
        y (KExpr.sort v) (par_reduces_cd_star_sort_inv_eq R v y vy)
        (Eq.substType KExpr (fun (z : KExpr) => KExprUniverseEq z y)
          x (KExpr.sort u) (par_reduces_cd_star_sort_inv_eq R u x ux) xy))) h",
            "Generic raw sort rigidity identifies each raw endpoint with its own original sort; semantic endpoint inversion then gives levelEqSem. No syntactic-level injectivity claim.",
        )?;

        self.add_recursive_def(
            r"def semantic_join_pi_components (R : RedEnv)
 (A : KExpr) (B : KExpr) (A2 : KExpr) (B2 : KExpr)
 (h : SemanticJoin R (KExpr.pi A B) (KExpr.pi A2 B2))
 (C : Type) (consume : DefEqIn R A A2 -> DefEqIn R B B2 -> C) : C :=
 SemanticJoin.rec R (KExpr.pi A B) (KExpr.pi A2 B2)
  (fun (_h : SemanticJoin R (KExpr.pi A B) (KExpr.pi A2 B2)) => C)
  (fun (x : KExpr) (y : KExpr)
    (left : par_reduces_cd_star R (KExpr.pi A B) x)
    (right : par_reduces_cd_star R (KExpr.pi A2 B2) y) (xy : KExprUniverseEq x y) =>
    par_reduces_cd_star_pi_inv_eq R A B x C left
      (fun (Ax : KExpr) (Bx : KExpr) (hx : Eq KExpr x (KExpr.pi Ax Bx))
        (hAx : par_reduces_cd_star R A Ax) (hBx : par_reduces_cd_star R B Bx) =>
        par_reduces_cd_star_pi_inv_eq R A2 B2 y C right
          (fun (Ay : KExpr) (By : KExpr) (hy : Eq KExpr y (KExpr.pi Ay By))
            (hAy : par_reduces_cd_star R A2 Ay) (hBy : par_reduces_cd_star R B2 By) =>
            kexprUniverseEq_pi_components Ax Bx Ay By
              (Eq.substType KExpr (fun (z : KExpr) => KExprUniverseEq (KExpr.pi Ax Bx) z)
                y (KExpr.pi Ay By) hy
                (Eq.substType KExpr (fun (z : KExpr) => KExprUniverseEq z y)
                  x (KExpr.pi Ax Bx) hx xy))
              C (fun (hA : KExprUniverseEq Ax Ay) (hB : KExprUniverseEq Bx By) =>
                consume
                  (semantic_join_to_def_eq_in R A A2 (SemanticJoin.mk R A A2 Ax Ay hAx hAy hA))
                  (semantic_join_to_def_eq_in R B B2 (SemanticJoin.mk R B B2 Bx By hBx hBy hB)))))) h",
            "Both actual raw Pi paths are inverted into component paths; the semantic endpoint view gives the two component relations and constructs conversion through those paths.",
        )?;

        self.add_recursive_def(
            r"def semantic_join_pi_domain (R : RedEnv)
 (A : KExpr) (B : KExpr) (A2 : KExpr) (B2 : KExpr)
 (h : SemanticJoin R (KExpr.pi A B) (KExpr.pi A2 B2)) : DefEqIn R A A2 :=
 semantic_join_pi_components R A B A2 B2 h (DefEqIn R A A2)
  (fun (hA : DefEqIn R A A2) (hB : DefEqIn R B B2) => hA)",
            "Projects the constructed domain conversion from semantic Pi join decomposition.",
        )?;

        self.add_recursive_def(
            r"def semantic_join_pi_codomain (R : RedEnv)
 (A : KExpr) (B : KExpr) (A2 : KExpr) (B2 : KExpr)
 (h : SemanticJoin R (KExpr.pi A B) (KExpr.pi A2 B2)) : DefEqIn R B B2 :=
 semantic_join_pi_components R A B A2 B2 h (DefEqIn R B B2)
  (fun (hA : DefEqIn R A A2) (hB : DefEqIn R B B2) => hB)",
            "Projects the constructed codomain conversion from semantic Pi join decomposition.",
        )?;

        self.add_recursive_def(
            r"def def_eq_in_sort_injective (R : RedEnv) (hf : RedEnvFaithful R)
 (u : Level) (v : Level) (h : DefEqIn R (KExpr.sort u) (KExpr.sort v)) : levelEqSem u v :=
 semantic_join_sort_injective R u v
  (def_eq_in_to_semantic_join R hf (KExpr.sort u) (KExpr.sort v) h)",
            "Semantic sort injectivity for supplied-environment conversion under the existing explicit raw confluence interfaces, via the proved conversion-to-semantic-join theorem.",
        )?;

        self.add_recursive_def(
            r"def def_eq_in_pi_components (R : RedEnv) (hf : RedEnvFaithful R)
 (A : KExpr) (B : KExpr) (A2 : KExpr) (B2 : KExpr)
 (h : DefEqIn R (KExpr.pi A B) (KExpr.pi A2 B2))
 (C : Type) (consume : DefEqIn R A A2 -> DefEqIn R B B2 -> C) : C :=
 semantic_join_pi_components R A B A2 B2
  (def_eq_in_to_semantic_join R hf (KExpr.pi A B) (KExpr.pi A2 B2) h) C consume",
            "Pi conversion decomposes into component conversions using existing RedEnvFaithful solely to derive semantic joinability, never as an assumed output-typing result.",
        )?;

        self.add_recursive_def(
            r"def def_eq_in_pi_domain (R : RedEnv) (hf : RedEnvFaithful R)
 (A : KExpr) (B : KExpr) (A2 : KExpr) (B2 : KExpr)
 (h : DefEqIn R (KExpr.pi A B) (KExpr.pi A2 B2)) : DefEqIn R A A2 :=
 def_eq_in_pi_components R hf A B A2 B2 h (DefEqIn R A A2)
  (fun (hA : DefEqIn R A A2) (hB : DefEqIn R B B2) => hA)",
            "Direct domain conversion corollary, retaining exactly the declared faithfulness premise.",
        )?;

        self.add_recursive_def(
            r"def def_eq_in_pi_codomain (R : RedEnv) (hf : RedEnvFaithful R)
 (A : KExpr) (B : KExpr) (A2 : KExpr) (B2 : KExpr)
 (h : DefEqIn R (KExpr.pi A B) (KExpr.pi A2 B2)) : DefEqIn R B B2 :=
 def_eq_in_pi_components R hf A B A2 B2 h (DefEqIn R B B2)
  (fun (hA : DefEqIn R A A2) (hB : DefEqIn R B B2) => hB)",
            "Direct codomain conversion corollary, retaining exactly the declared faithfulness premise.",
        )?;

        self.add_recursive_def(
            r"def semantic_sort_imax_zero_join (R : RedEnv) (u : Level) :
 SemanticJoin R (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort Level.zero) :=
 semantic_join_levels R (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort Level.zero)
  (kexprUniverseEq_imax_zero u)",
            "Concrete semantic equality of syntactically different sorts, with no raw reduction or environmental assumption.",
        )?;

        self.add_recursive_def(
            r"def semantic_sort_imax_zero_injective (R : RedEnv) (u : Level) :
 levelEqSem (Level.imax u Level.zero) Level.zero :=
 semantic_join_sort_injective R (Level.imax u Level.zero) Level.zero
  (semantic_sort_imax_zero_join R u)",
            "The semantic sort injectivity theorem accepts the imax-zero witness and returns denotational equality, not an impossible raw equality.",
        )?;

        self.add_recursive_def(
            r"def semantic_sort_imax_zero_syntax_distinct (u : Level)
 (h : Eq KExpr (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort Level.zero)) : Empty :=
 Eq.substType Level
  (fun (v : Level) => Level.rec (fun (_ : Level) => Type)
    Empty (fun (_ : Level) (_ : Type) => Empty)
    (fun (_ : Level) (_ : Level) (_ : Type) (_ : Type) => Empty)
    (fun (_ : Level) (_ : Level) (_ : Type) (_ : Type) => Nat)
    (fun (_ : Name) => Empty) v)
  (Level.imax u Level.zero) Level.zero
  (kexpr_sort_inj (Level.imax u Level.zero) Level.zero h) Nat.zero",
            "Concrete raw constructor discrimination confirms the accepted imax-zero semantic equality cannot be strengthened to equality of raw sort syntax.",
        )?;

        self.add_recursive_def(
            r"def semantic_join_sort_zero_succ_absurd (R : RedEnv) (u : Level)
 (h : SemanticJoin R (KExpr.sort Level.zero) (KExpr.sort (Level.succ u))) : Empty :=
 nat_zero_ne_succ (evalL (fun (_ : Name) => Nat.zero) u) Empty
  ((semantic_join_sort_injective R Level.zero (Level.succ u) h)
    (fun (_ : Name) => Nat.zero))",
            "Different universe denotations cannot have a semantic sort join; evaluate at the concrete zero valuation and use Nat discrimination.",
        )?;

        self.add_recursive_def(
            r"def def_eq_in_sort_zero_succ_absurd (R : RedEnv) (hf : RedEnvFaithful R) (u : Level)
 (h : DefEqIn R (KExpr.sort Level.zero) (KExpr.sort (Level.succ u))) : Empty :=
 semantic_join_sort_zero_succ_absurd R u
  (def_eq_in_to_semantic_join R hf (KExpr.sort Level.zero) (KExpr.sort (Level.succ u)) h)",
            "Unequal-universe refusal for semantic conversion, conditional only on the explicit existing faithful-environment interfaces.",
        )?;

        self.add_recursive_def(
            r"def def_eq_in_pi_zero_succ_domain_absurd (R : RedEnv) (hf : RedEnvFaithful R)
 (u : Level) (B : KExpr) (B2 : KExpr)
 (h : DefEqIn R (KExpr.pi (KExpr.sort Level.zero) B)
   (KExpr.pi (KExpr.sort (Level.succ u)) B2)) : Empty :=
 def_eq_in_sort_zero_succ_absurd R hf u
  (def_eq_in_pi_domain R hf (KExpr.sort Level.zero) B (KExpr.sort (Level.succ u)) B2 h)",
            "Actual Pi decomposition consumes the mismatched-domain conversion and derives the concrete unequal-universe contradiction, regardless of the codomain payloads.",
        )?;

        self.add_recursive_def(
            r"def semantic_pi_imax_zero_components (R : RedEnv) (u : Level) (payload : Nat)
 (C : Type)
 (consume : DefEqIn R (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort Level.zero) ->
   DefEqIn R (KExpr.lit payload) (KExpr.lit payload) -> C) : C :=
 semantic_join_pi_components R (KExpr.sort (Level.imax u Level.zero)) (KExpr.lit payload)
  (KExpr.sort Level.zero) (KExpr.lit payload)
  (semantic_join_levels R
    (KExpr.pi (KExpr.sort (Level.imax u Level.zero)) (KExpr.lit payload))
    (KExpr.pi (KExpr.sort Level.zero) (KExpr.lit payload))
    (KExprUniverseEq.pi (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort Level.zero)
      (KExpr.lit payload) (KExpr.lit payload)
      (kexprUniverseEq_imax_zero u) (KExprUniverseEq.lit payload))) C consume",
            "The real Pi component theorem accepts a semantically changed domain while retaining the exact tagged literal payload in the codomain.",
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::test_utils::{build_spec_with_stack, run_with_stack};

    #[test]
    fn semantic_injectivity_proofs_and_computational_controls_are_checked() {
        run_with_stack(|| {
            let spec = build_spec_with_stack();
            for name in [
                "par_reduces_cd_star_to_def_eq_in",
                "semantic_join_to_def_eq_in",
                "kexprUniverseEq_sort_injective",
                "kexprUniverseEq_pi_components",
                "semantic_join_sort_injective",
                "semantic_join_pi_components",
                "semantic_join_pi_domain",
                "semantic_join_pi_codomain",
                "def_eq_in_sort_injective",
                "def_eq_in_pi_components",
                "def_eq_in_pi_domain",
                "def_eq_in_pi_codomain",
                "semantic_sort_imax_zero_join",
                "semantic_sort_imax_zero_injective",
                "semantic_sort_imax_zero_syntax_distinct",
                "semantic_join_sort_zero_succ_absurd",
                "def_eq_in_sort_zero_succ_absurd",
                "def_eq_in_pi_zero_succ_domain_absurd",
                "semantic_pi_imax_zero_components",
            ] {
                let declaration = spec
                    .definitions()
                    .get(name)
                    .expect("registered semantic injectivity proof");
                assert!(!declaration.is_axiom, "{name}");
                assert!(declaration.elaborated_value.is_some(), "{name}");
                assert!(
                    crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                    "{name}"
                );
            }
        });
    }

    #[test]
    fn semantic_injectivity_does_not_collapse_raw_syntax_or_literal_payloads() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for source in [
                "def semantic_injectivity_forged_raw_equality : Eq KExpr (KExpr.sort (Level.imax Level.zero Level.zero)) (KExpr.sort Level.zero) := Eq.refl KExpr (KExpr.sort Level.zero)",
                "def semantic_injectivity_forged_level_equality : levelEqSem Level.zero (Level.succ Level.zero) := fun (valuation : Name -> Nat) => Eq.refl Nat Nat.zero",
                "def semantic_injectivity_forged_pi_payload : KExprUniverseEq (KExpr.pi (KExpr.sort Level.zero) (KExpr.lit Nat.zero)) (KExpr.pi (KExpr.sort Level.zero) (KExpr.lit (Nat.succ Nat.zero))) := kexprUniverseEq_refl (KExpr.pi (KExpr.sort Level.zero) (KExpr.lit Nat.zero))",
            ] {
                assert!(spec.add_recursive_def(source, "Negative semantic injectivity control.").is_err(),
                    "raw syntax, denotations, and tagged literal payloads must remain distinct");
            }
        });
    }
}
