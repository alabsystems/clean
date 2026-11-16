// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Semantic joins use two actual raw reduction paths and universe-equivalent
//! endpoints, not an asserted common syntactic reduct.
//!
//! Only transitivity and conversion inclusion need RedEnvFaithful. Transitivity
//! projects its existing eight interfaces into the proved raw-star diamond and
//! uses the actual semantic-star transport theorem to derive both remaining
//! paths. No joinability, output-step preservation or typing assumption is added.
//! This additive unit preserves legacy DefEq and its consumers unchanged.
//!
//! Independent check: 983 exact exported dependency blocks from checkpoint
//! 9f368f80a/hvs0z0 (export SHA256
//! b5ff6fa3fc255b6dd1bcce19223911ee2babde3374e91508243ccad7773f861f),
//! plus the actual semantic spine/delta/iota/parallel source declarations.
//! Pinned Lean 4.30.0-rc2 checked all 15 new declarations axiom-free on
//! 2026-09-08 (3.44 seconds, 1,137,819,648-byte max RSS, 2 GB reserved).
//! Exact scratch SHA256:
//! 3eebbb0785396f6551f8779b8980aba1c35f1d856d1a78ed9a8100ef2d26c22e.
//! Both forged controls were separately rejected at their intended endpoint
//! and raw-path type mismatches (3.93 seconds, 1,128,742,912-byte max RSS).
//! Reproduce the slice with scratch/clean_model_slice.rb, supplying the exact
//! export and those four source files followed by this file in that order.
//! Registered Clean checking and whole-corpus replay remain separate gates.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const JOIN: &str = r"inductive SemanticJoin (R : RedEnv) (a : KExpr) (b : KExpr) : Type
| mk : forall (x : KExpr) (y : KExpr),
    par_reduces_cd_star R a x -> par_reduces_cd_star R b y ->
    KExprUniverseEq x y -> SemanticJoin R a b";

const PROOFS: &[(&str, &str)] = &[
    (
        r"def semantic_join_refl (R : RedEnv) (a : KExpr) : SemanticJoin R a a :=
 @SemanticJoin.mk R a a a a (@par_reduces_cd_star.refl R a) (@par_reduces_cd_star.refl R a)
  (kexprUniverseEq_refl a)",
        "Semantic reflexivity uses two empty actual reduction paths and semantic reflexivity, not a confluence hypothesis.",
    ),
    (
        r"def semantic_join_levels (R : RedEnv) (a : KExpr) (b : KExpr)
 (h : KExprUniverseEq a b) : SemanticJoin R a b :=
 @SemanticJoin.mk R a b a b (@par_reduces_cd_star.refl R a) (@par_reduces_cd_star.refl R b) h",
        "Universe-only correspondence gives a semantic join with reflexive raw legs, without requiring a common syntactic reduct.",
    ),
    (
        r"def semantic_join_raw (R : RedEnv) (a : KExpr) (b : KExpr)
 (h : par_reduces_cd R a b) : SemanticJoin R a b :=
 @SemanticJoin.mk R a b b b
  (@par_reduces_cd_star.step R a b b h (@par_reduces_cd_star.refl R b))
  (@par_reduces_cd_star.refl R b) (kexprUniverseEq_refl b)",
        "An actual raw parallel step embeds as a semantic join with equal endpoints.",
    ),
    (
        r"def semantic_join_symm (R : RedEnv) (a : KExpr) (b : KExpr)
 (h : SemanticJoin R a b) : SemanticJoin R b a :=
 @SemanticJoin.rec R a b (fun (_h : SemanticJoin R a b) => SemanticJoin R b a)
  (fun (x : KExpr) (y : KExpr) (ax : par_reduces_cd_star R a x)
    (by_path : par_reduces_cd_star R b y) (xy : KExprUniverseEq x y) =>
    @SemanticJoin.mk R b a y x by_path ax (kexprUniverseEq_symm x y xy)) h",
        "Reverse the two raw paths and the semantic endpoint relation; no environmental assumption is needed.",
    ),
    (
        r"def semantic_join_trans (R : RedEnv) (hf : RedEnvFaithful R)
 (a : KExpr) (b : KExpr) (c : KExpr)
 (ab : SemanticJoin R a b) (bc : SemanticJoin R b c) : SemanticJoin R a c :=
 @SemanticJoin.rec R a b (fun (_ab : SemanticJoin R a b) => SemanticJoin R a c)
  (fun (x : KExpr) (y : KExpr) (ax : par_reduces_cd_star R a x)
    (by_path : par_reduces_cd_star R b y) (xy : KExprUniverseEq x y) =>
    @SemanticJoin.rec R b c (fun (_bc : SemanticJoin R b c) => SemanticJoin R a c)
      (fun (u : KExpr) (v : KExpr) (bu : par_reduces_cd_star R b u)
        (cv : par_reduces_cd_star R c v) (uv : KExprUniverseEq u v) =>
        @par_strips_witness_cd_star.rec R y u
          (fun (_join : par_strips_witness_cd_star R y u) => SemanticJoin R a c)
          (fun (z : KExpr) (yz : par_reduces_cd_star R y z) (uz : par_reduces_cd_star R u z) =>
            par_reduces_cd_star_universe_compat R y z yz x
              (kexprUniverseEq_symm x y xy) (SemanticJoin R a c)
              (fun (x2 : KExpr) (xx2 : par_reduces_cd_star R x x2) (zx2 : KExprUniverseEq z x2) =>
                par_reduces_cd_star_universe_compat R u z uz v uv (SemanticJoin R a c)
                  (fun (v2 : KExpr) (vv2 : par_reduces_cd_star R v v2) (zv2 : KExprUniverseEq z v2) =>
                    @SemanticJoin.mk R a c x2 v2
                      (par_reduces_cd_star_trans R a x x2 ax xx2)
                      (par_reduces_cd_star_trans R c v v2 cv vv2)
                      (kexprUniverseEq_trans x2 z (kexprUniverseEq_symm z x2 zx2) v2 zv2))))
          (par_reduces_cd_star_diamond R
            (redenv_faithful_i1 R hf) (redenv_faithful_i2 R hf)
            (redenv_faithful_i3 R hf) (redenv_faithful_i4 R hf)
            (redenv_faithful_i5 R hf) (redenv_faithful_i6 R hf)
            (redenv_faithful_i7 R hf) (redenv_faithful_i8 R hf)
            b y u by_path bu)) bc) ab",
        "Transitivity derives a raw diamond at the shared source from the eight actual faithful interfaces, then transports both residual star paths across semantic endpoint equivalences and composes the original legs. Neither joinability nor star preservation is a theorem premise.",
    ),
    (
        r"def semantic_join_app (R : RedEnv) (a : KExpr) (a2 : KExpr) (b : KExpr) (b2 : KExpr)
 (ha : SemanticJoin R a a2) (hb : SemanticJoin R b b2) :
 SemanticJoin R (KExpr.app a b) (KExpr.app a2 b2) :=
 @SemanticJoin.rec R a a2
  (fun (_ha : SemanticJoin R a a2) => SemanticJoin R (KExpr.app a b) (KExpr.app a2 b2))
  (fun (x : KExpr) (x2 : KExpr) (ax : par_reduces_cd_star R a x)
    (a2x2 : par_reduces_cd_star R a2 x2) (xx2 : KExprUniverseEq x x2) =>
    @SemanticJoin.rec R b b2
      (fun (_hb : SemanticJoin R b b2) => SemanticJoin R (KExpr.app a b) (KExpr.app a2 b2))
      (fun (y : KExpr) (y2 : KExpr) (by_path : par_reduces_cd_star R b y)
        (b2y2 : par_reduces_cd_star R b2 y2) (yy2 : KExprUniverseEq y y2) =>
        @SemanticJoin.mk R (KExpr.app a b) (KExpr.app a2 b2)
          (KExpr.app x y) (KExpr.app x2 y2)
          (par_reduces_cd_star_app R a x b y ax by_path)
          (par_reduces_cd_star_app R a2 x2 b2 y2 a2x2 b2y2)
          (KExprUniverseEq.app x x2 y y2 xx2 yy2)) hb) ha",
        "Semantic join is congruent through app: lift the two existing raw-star legs with the actual structural star theorem and rebuild related endpoints. No faithfulness or typing premise is needed.",
    ),
    (
        r"def semantic_join_lam (R : RedEnv) (a : KExpr) (a2 : KExpr) (b : KExpr) (b2 : KExpr)
 (ha : SemanticJoin R a a2) (hb : SemanticJoin R b b2) :
 SemanticJoin R (KExpr.lam a b) (KExpr.lam a2 b2) :=
 @SemanticJoin.rec R a a2
  (fun (_ha : SemanticJoin R a a2) => SemanticJoin R (KExpr.lam a b) (KExpr.lam a2 b2))
  (fun (x : KExpr) (x2 : KExpr) (ax : par_reduces_cd_star R a x)
    (a2x2 : par_reduces_cd_star R a2 x2) (xx2 : KExprUniverseEq x x2) =>
    @SemanticJoin.rec R b b2
      (fun (_hb : SemanticJoin R b b2) => SemanticJoin R (KExpr.lam a b) (KExpr.lam a2 b2))
      (fun (y : KExpr) (y2 : KExpr) (by_path : par_reduces_cd_star R b y)
        (b2y2 : par_reduces_cd_star R b2 y2) (yy2 : KExprUniverseEq y y2) =>
        @SemanticJoin.mk R (KExpr.lam a b) (KExpr.lam a2 b2)
          (KExpr.lam x y) (KExpr.lam x2 y2)
          (par_reduces_cd_star_lam R a x b y ax by_path)
          (par_reduces_cd_star_lam R a2 x2 b2 y2 a2x2 b2y2)
          (KExprUniverseEq.lam x x2 y y2 xx2 yy2)) hb) ha",
        "Semantic join is congruent through lam: lift the two existing raw-star legs with the actual structural star theorem and rebuild related endpoints. No faithfulness or typing premise is needed.",
    ),
    (
        r"def semantic_join_pi (R : RedEnv) (a : KExpr) (a2 : KExpr) (b : KExpr) (b2 : KExpr)
 (ha : SemanticJoin R a a2) (hb : SemanticJoin R b b2) :
 SemanticJoin R (KExpr.pi a b) (KExpr.pi a2 b2) :=
 @SemanticJoin.rec R a a2
  (fun (_ha : SemanticJoin R a a2) => SemanticJoin R (KExpr.pi a b) (KExpr.pi a2 b2))
  (fun (x : KExpr) (x2 : KExpr) (ax : par_reduces_cd_star R a x)
    (a2x2 : par_reduces_cd_star R a2 x2) (xx2 : KExprUniverseEq x x2) =>
    @SemanticJoin.rec R b b2
      (fun (_hb : SemanticJoin R b b2) => SemanticJoin R (KExpr.pi a b) (KExpr.pi a2 b2))
      (fun (y : KExpr) (y2 : KExpr) (by_path : par_reduces_cd_star R b y)
        (b2y2 : par_reduces_cd_star R b2 y2) (yy2 : KExprUniverseEq y y2) =>
        @SemanticJoin.mk R (KExpr.pi a b) (KExpr.pi a2 b2)
          (KExpr.pi x y) (KExpr.pi x2 y2)
          (par_reduces_cd_star_pi R a x b y ax by_path)
          (par_reduces_cd_star_pi R a2 x2 b2 y2 a2x2 b2y2)
          (KExprUniverseEq.pi x x2 y y2 xx2 yy2)) hb) ha",
        "Semantic join is congruent through pi: lift the two existing raw-star legs with the actual structural star theorem and rebuild related endpoints. No faithfulness or typing premise is needed.",
    ),
    (
        r"def semantic_join_let (R : RedEnv)
 (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr)
 (hA : SemanticJoin R A A2) (hv : SemanticJoin R v v2) (hb : SemanticJoin R b b2) :
 SemanticJoin R (KExpr.let_ A v b) (KExpr.let_ A2 v2 b2) :=
 @SemanticJoin.rec R A A2
  (fun (_hA : SemanticJoin R A A2) => SemanticJoin R (KExpr.let_ A v b) (KExpr.let_ A2 v2 b2))
  (fun (x : KExpr) (x2 : KExpr) (Ax : par_reduces_cd_star R A x)
    (A2x2 : par_reduces_cd_star R A2 x2) (xx2 : KExprUniverseEq x x2) =>
    @SemanticJoin.rec R v v2
      (fun (_hv : SemanticJoin R v v2) => SemanticJoin R (KExpr.let_ A v b) (KExpr.let_ A2 v2 b2))
      (fun (y : KExpr) (y2 : KExpr) (vy : par_reduces_cd_star R v y)
        (v2y2 : par_reduces_cd_star R v2 y2) (yy2 : KExprUniverseEq y y2) =>
        @SemanticJoin.rec R b b2
          (fun (_hb : SemanticJoin R b b2) => SemanticJoin R (KExpr.let_ A v b) (KExpr.let_ A2 v2 b2))
          (fun (z : KExpr) (z2 : KExpr) (bz : par_reduces_cd_star R b z)
            (b2z2 : par_reduces_cd_star R b2 z2) (zz2 : KExprUniverseEq z z2) =>
            @SemanticJoin.mk R (KExpr.let_ A v b) (KExpr.let_ A2 v2 b2)
              (KExpr.let_ x y z) (KExpr.let_ x2 y2 z2)
              (par_reduces_cd_star_let_cong R A x v y b z Ax vy bz)
              (par_reduces_cd_star_let_cong R A2 x2 v2 y2 b2 z2 A2x2 v2y2 b2z2)
              (KExprUniverseEq.let_ x x2 y y2 z z2 xx2 yy2 zz2)) hb) hv) hA",
        "Let congruence composes all three component joins through actual raw-star let congruence; it does not assume zeta preservation or typing.",
    ),
    (
        r"def semantic_join_proj (R : RedEnv) (n : Name) (i : Nat)
 (e : KExpr) (e2 : KExpr) (h : SemanticJoin R e e2) :
 SemanticJoin R (KExpr.proj n i e) (KExpr.proj n i e2) :=
 @SemanticJoin.rec R e e2
  (fun (_h : SemanticJoin R e e2) => SemanticJoin R (KExpr.proj n i e) (KExpr.proj n i e2))
  (fun (x : KExpr) (y : KExpr) (ex : par_reduces_cd_star R e x)
    (e2y : par_reduces_cd_star R e2 y) (xy : KExprUniverseEq x y) =>
    @SemanticJoin.mk R (KExpr.proj n i e) (KExpr.proj n i e2) (KExpr.proj n i x) (KExpr.proj n i y)
      (par_reduces_cd_star_proj R n i e x ex) (par_reduces_cd_star_proj R n i e2 y e2y)
      (KExprUniverseEq.proj n i x y xy)) h",
        "Projection congruence preserves the exact structure name and field index while lifting the subexpression's actual paths and semantic endpoint relation.",
    ),
    (
        r"def def_eq_in_to_semantic_join (R : RedEnv) (hf : RedEnvFaithful R)
 (a : KExpr) (b : KExpr) (h : DefEqIn R a b) : SemanticJoin R a b :=
 @DefEqIn.rec R
  (fun (x : KExpr) (y : KExpr) (_h : DefEqIn R x y) => SemanticJoin R x y)
  (fun (x : KExpr) => semantic_join_refl R x)
  (fun (x : KExpr) (y : KExpr) (_h : DefEqIn R x y) (ih : SemanticJoin R x y) =>
    semantic_join_symm R x y ih)
  (fun (x : KExpr) (m : KExpr) (y : KExpr) (_hx : DefEqIn R x m) (_hy : DefEqIn R m y)
    (ihx : SemanticJoin R x m) (ihy : SemanticJoin R m y) =>
    semantic_join_trans R hf x m y ihx ihy)
  (fun (x : KExpr) (y : KExpr) (raw : par_reduces_cd R x y) => semantic_join_raw R x y raw)
  (fun (x : KExpr) (y : KExpr) (levels : KExprUniverseEq x y) => semantic_join_levels R x y levels)
  (fun (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr) (_hf : DefEqIn R f f2) (_ha : DefEqIn R a a2)
    (ihf : SemanticJoin R f f2) (iha : SemanticJoin R a a2) => semantic_join_app R f f2 a a2 ihf iha)
  (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (_hA : DefEqIn R A A2) (_hb : DefEqIn R b b2)
    (ihA : SemanticJoin R A A2) (ihb : SemanticJoin R b b2) => semantic_join_lam R A A2 b b2 ihA ihb)
  (fun (A : KExpr) (A2 : KExpr) (B : KExpr) (B2 : KExpr) (_hA : DefEqIn R A A2) (_hB : DefEqIn R B B2)
    (ihA : SemanticJoin R A A2) (ihB : SemanticJoin R B B2) => semantic_join_pi R A A2 B B2 ihA ihB)
  (fun (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr)
    (_hA : DefEqIn R A A2) (_hv : DefEqIn R v v2) (_hb : DefEqIn R b b2)
    (ihA : SemanticJoin R A A2) (ihv : SemanticJoin R v v2) (ihb : SemanticJoin R b b2) =>
    semantic_join_let R A A2 v v2 b b2 ihA ihv ihb)
  (fun (n : Name) (i : Nat) (e : KExpr) (e2 : KExpr) (_h : DefEqIn R e e2)
    (ih : SemanticJoin R e e2) => semantic_join_proj R n i e e2 ih)
  a b h",
        "Every constructor of the additive semantic conversion judgment derives a semantic join under the actual faithful environment interfaces. Transitivity uses the proved raw diamond and actual semantic-star transport, not an assumed syntactic joinability contract; legacy DefEq remains unchanged.",
    ),
];

const CONTROLS: &[(&str, &str)] = &[
    (
        r"def semantic_join_mixed_source : KExpr :=
 KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))
   (KExpr.sort (Level.imax (Level.succ Level.zero) Level.zero))",
        "Closed concrete beta redex with a nonsyntactically normalized nonzero imax annotation in its argument.",
    ),
    (
        r"def semantic_join_mixed_conversion :
 DefEqIn the_red_env semantic_join_mixed_source (KExpr.sort Level.zero) :=
 @DefEqIn.trans the_red_env semantic_join_mixed_source
  (KExpr.sort (Level.imax (Level.succ Level.zero) Level.zero)) (KExpr.sort Level.zero)
  (@DefEqIn.raw the_red_env semantic_join_mixed_source
    (KExpr.sort (Level.imax (Level.succ Level.zero) Level.zero))
    (@par_reduces_cd.beta the_red_env (KExpr.sort Level.zero) (KExpr.sort Level.zero)
      (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)
      (KExpr.sort (Level.imax (Level.succ Level.zero) Level.zero))
      (KExpr.sort (Level.imax (Level.succ Level.zero) Level.zero))
      (@par_reduces_cd.refl the_red_env (KExpr.sort Level.zero))
      (@par_reduces_cd.refl the_red_env (KExpr.bvar Nat.zero))
      (@par_reduces_cd.refl the_red_env (KExpr.sort (Level.imax (Level.succ Level.zero) Level.zero)))))
  (@DefEqIn.levels the_red_env (KExpr.sort (Level.imax (Level.succ Level.zero) Level.zero)) (KExpr.sort Level.zero)
    (kexprUniverseEq_imax_zero (Level.succ Level.zero)))",
        "An inhabited conversion derivation under the actual reflected reduction environment, explicitly composing an actual beta step and semantic-universe normalization through transitivity.",
    ),
    (
        r"def semantic_join_mixed_caller :
 SemanticJoin the_red_env semantic_join_mixed_source (KExpr.sort Level.zero) :=
 def_eq_in_to_semantic_join the_red_env the_red_env_faithful
   semantic_join_mixed_source (KExpr.sort Level.zero) semantic_join_mixed_conversion",
        "Actual closed caller of the conversion-to-semantic-join theorem using the existing checked the_red_env_faithful bundle, not a carried uninhabited faithfulness premise.",
    ),
];

impl Specification {
    /// Requires the actual raw-star diamond and faithful projectors, semantic
    /// universe relations and star transport, and the additive DefEqIn judgment.
    pub(super) fn add_semantic_join(&mut self) -> Result<(), SpecError> {
        self.add_inductive(JOIN, "Type-valued semantic join: two actual raw parallel-star legs to endpoints related only by semantic universe equivalence.")?;
        for (source, description) in PROOFS.iter().chain(CONTROLS) {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn semantic_join_closure_and_actual_mixed_caller_are_kernel_checked() {
        let spec = crate::test_utils::build_spec_with_stack();
        for name in [
            "semantic_join_refl",
            "semantic_join_levels",
            "semantic_join_raw",
            "semantic_join_symm",
            "semantic_join_trans",
            "semantic_join_app",
            "semantic_join_lam",
            "semantic_join_pi",
            "semantic_join_let",
            "semantic_join_proj",
            "def_eq_in_to_semantic_join",
            "semantic_join_mixed_conversion",
            "semantic_join_mixed_caller",
        ] {
            let definition = spec
                .definitions()
                .get(name)
                .expect("registered checked semantic-join declaration");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
    }

    #[test]
    fn semantic_join_rejects_forged_universe_endpoints_and_raw_legs() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = crate::test_utils::build_spec_with_stack();
            for source in [
                "def semantic_join_forged_levels : SemanticJoin the_red_env (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero)) := @SemanticJoin.mk the_red_env (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero)) (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero)) (@par_reduces_cd_star.refl the_red_env (KExpr.sort Level.zero)) (@par_reduces_cd_star.refl the_red_env (KExpr.sort (Level.succ Level.zero))) (kexprUniverseEq_refl (KExpr.sort Level.zero))",
                "def semantic_join_forged_trace : SemanticJoin the_red_env semantic_join_mixed_source (KExpr.sort Level.zero) := @SemanticJoin.mk the_red_env semantic_join_mixed_source (KExpr.sort Level.zero) (KExpr.sort Level.zero) (KExpr.sort Level.zero) (@par_reduces_cd_star.refl the_red_env (KExpr.sort Level.zero)) (@par_reduces_cd_star.refl the_red_env (KExpr.sort Level.zero)) (kexprUniverseEq_refl (KExpr.sort Level.zero))",
            ] {
                assert!(spec.add_recursive_def(source,
                    "Rejected semantic-join control: neither endpoint equality nor a raw trace may be fabricated."
                ).is_err());
            }
        });
    }
}
