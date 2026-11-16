// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact mixed_strong proof tuples, with actual input derivations and explicit
//! environment assumptions. No acceptance or source-execution claim.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Proof(
        "projection_parallel_star_congr1",
        r"forall (R : RedEnv) (f : KExpr -> KExpr)
 (contextStep : forall (a b : KExpr), projection_parallel R a b -> projection_parallel R (f a) (f b))
 (a b : KExpr) (h : projection_parallel_star R a b), projection_parallel_star R (f a) (f b)",
        r"fun (R : RedEnv) (f : KExpr -> KExpr)
 (contextStep : forall (a b : KExpr), projection_parallel R a b -> projection_parallel R (f a) (f b))
 (a b : KExpr) (h : projection_parallel_star R a b) => @projection_parallel_star.rec R
  (fun (x y : KExpr) (_h : projection_parallel_star R x y) => projection_parallel_star R (f x) (f y))
  (fun (x : KExpr) => @projection_parallel_star.refl R (f x))
  (fun (x m y : KExpr) (xm : projection_parallel R x m) (_tail : projection_parallel_star R m y)
   (ih : projection_parallel_star R (f m) (f y)) =>
   @projection_parallel_star.step R (f x) (f m) (f y) (contextStep x m xm) ih) a b h",
    ),
    DeclarationInput::Proof(
        "projection_parallel_star_congr2",
        r"forall (R : RedEnv) (f : KExpr -> KExpr -> KExpr)
 (contextStep : forall (a a2 b b2 : KExpr), projection_parallel R a a2 -> projection_parallel R b b2 -> projection_parallel R (f a b) (f a2 b2))
 (a a2 b b2 : KExpr) (ha : projection_parallel_star R a a2) (hb : projection_parallel_star R b b2), projection_parallel_star R (f a b) (f a2 b2)",
        r"fun (R : RedEnv) (f : KExpr -> KExpr -> KExpr)
 (contextStep : forall (a a2 b b2 : KExpr), projection_parallel R a a2 -> projection_parallel R b b2 -> projection_parallel R (f a b) (f a2 b2))
 (a a2 b b2 : KExpr) (ha : projection_parallel_star R a a2) (hb : projection_parallel_star R b b2) => projection_parallel_star_trans R (f a b) (f a2 b) (f a2 b2)
  (projection_parallel_star_congr1 R (fun (x : KExpr) => f x b)
   (fun (x y : KExpr) (xy : projection_parallel R x y) => contextStep x y b b xy (@projection_parallel.refl R b)) a a2 ha)
  (projection_parallel_star_congr1 R (fun (x : KExpr) => f a2 x)
   (fun (x y : KExpr) (xy : projection_parallel R x y) => contextStep a2 a2 x y (@projection_parallel.refl R a2) xy) b b2 hb)",
    ),
    DeclarationInput::Proof(
        "projection_parallel_star_congr3",
        r"forall (R : RedEnv) (f : KExpr -> KExpr -> KExpr -> KExpr)
 (contextStep : forall (a a2 b b2 c c2 : KExpr), projection_parallel R a a2 -> projection_parallel R b b2 -> projection_parallel R c c2 -> projection_parallel R (f a b c) (f a2 b2 c2))
 (a a2 b b2 c c2 : KExpr) (ha : projection_parallel_star R a a2) (hb : projection_parallel_star R b b2) (hc : projection_parallel_star R c c2), projection_parallel_star R (f a b c) (f a2 b2 c2)",
        r"fun (R : RedEnv) (f : KExpr -> KExpr -> KExpr -> KExpr)
 (contextStep : forall (a a2 b b2 c c2 : KExpr), projection_parallel R a a2 -> projection_parallel R b b2 -> projection_parallel R c c2 -> projection_parallel R (f a b c) (f a2 b2 c2))
 (a a2 b b2 c c2 : KExpr) (ha : projection_parallel_star R a a2) (hb : projection_parallel_star R b b2) (hc : projection_parallel_star R c c2) => projection_parallel_star_trans R (f a b c) (f a2 b2 c) (f a2 b2 c2)
  (projection_parallel_star_congr2 R (fun (x y : KExpr) => f x y c)
   (fun (x x2 y y2 : KExpr) (hx : projection_parallel R x x2) (hy : projection_parallel R y y2) =>
    contextStep x x2 y y2 c c hx hy (@projection_parallel.refl R c)) a a2 b b2 ha hb)
  (projection_parallel_star_congr1 R (fun (x : KExpr) => f a2 b2 x)
   (fun (x y : KExpr) (xy : projection_parallel R x y) =>
    contextStep a2 a2 b2 b2 x y (@projection_parallel.refl R a2) (@projection_parallel.refl R b2) xy) c c2 hc)",
    ),
    DeclarationInput::Proof(
        "cd_projection_peak_app",
        r"forall (R : RedEnv)  (a0 b0 a1 b1 : KExpr) (p0 : CDProjectionPeak R a0 b0) (p1 : CDProjectionPeak R a1 b1), CDProjectionPeak R (KExpr.app a0 a1) (KExpr.app b0 b1)",
        r"fun (R : RedEnv)  (a0 b0 a1 b1 : KExpr) (p0 : CDProjectionPeak R a0 b0) (p1 : CDProjectionPeak R a1 b1) => @CDProjectionPeak.rec R a0 b0 (fun (_peak : CDProjectionPeak R a0 b0) => CDProjectionPeak R (KExpr.app a0 a1) (KExpr.app b0 b1))
 (fun (meet0 : KExpr) (hs0 : projection_parallel_star R a0 meet0) (hc0 : par_reduces_cd R b0 meet0) => @CDProjectionPeak.rec R a1 b1 (fun (_peak : CDProjectionPeak R a1 b1) => CDProjectionPeak R (KExpr.app a0 a1) (KExpr.app b0 b1))
 (fun (meet1 : KExpr) (hs1 : projection_parallel_star R a1 meet1) (hc1 : par_reduces_cd R b1 meet1) => @CDProjectionPeak.mk R (KExpr.app a0 a1) (KExpr.app b0 b1) (KExpr.app meet0 meet1) (projection_parallel_star_congr2 R KExpr.app (@projection_parallel.app R) a0 meet0 a1 meet1 hs0 hs1) (@par_reduces_cd.app R b0 meet0 b1 meet1 hc0 hc1)) p1) p0",
    ),
    DeclarationInput::Proof(
        "cd_projection_peak_lam",
        r"forall (R : RedEnv)  (a0 b0 a1 b1 : KExpr) (p0 : CDProjectionPeak R a0 b0) (p1 : CDProjectionPeak R a1 b1), CDProjectionPeak R (KExpr.lam a0 a1) (KExpr.lam b0 b1)",
        r"fun (R : RedEnv)  (a0 b0 a1 b1 : KExpr) (p0 : CDProjectionPeak R a0 b0) (p1 : CDProjectionPeak R a1 b1) => @CDProjectionPeak.rec R a0 b0 (fun (_peak : CDProjectionPeak R a0 b0) => CDProjectionPeak R (KExpr.lam a0 a1) (KExpr.lam b0 b1))
 (fun (meet0 : KExpr) (hs0 : projection_parallel_star R a0 meet0) (hc0 : par_reduces_cd R b0 meet0) => @CDProjectionPeak.rec R a1 b1 (fun (_peak : CDProjectionPeak R a1 b1) => CDProjectionPeak R (KExpr.lam a0 a1) (KExpr.lam b0 b1))
 (fun (meet1 : KExpr) (hs1 : projection_parallel_star R a1 meet1) (hc1 : par_reduces_cd R b1 meet1) => @CDProjectionPeak.mk R (KExpr.lam a0 a1) (KExpr.lam b0 b1) (KExpr.lam meet0 meet1) (projection_parallel_star_congr2 R KExpr.lam (@projection_parallel.lam R) a0 meet0 a1 meet1 hs0 hs1) (@par_reduces_cd.lam R b0 meet0 b1 meet1 hc0 hc1)) p1) p0",
    ),
    DeclarationInput::Proof(
        "cd_projection_peak_pi",
        r"forall (R : RedEnv)  (a0 b0 a1 b1 : KExpr) (p0 : CDProjectionPeak R a0 b0) (p1 : CDProjectionPeak R a1 b1), CDProjectionPeak R (KExpr.pi a0 a1) (KExpr.pi b0 b1)",
        r"fun (R : RedEnv)  (a0 b0 a1 b1 : KExpr) (p0 : CDProjectionPeak R a0 b0) (p1 : CDProjectionPeak R a1 b1) => @CDProjectionPeak.rec R a0 b0 (fun (_peak : CDProjectionPeak R a0 b0) => CDProjectionPeak R (KExpr.pi a0 a1) (KExpr.pi b0 b1))
 (fun (meet0 : KExpr) (hs0 : projection_parallel_star R a0 meet0) (hc0 : par_reduces_cd R b0 meet0) => @CDProjectionPeak.rec R a1 b1 (fun (_peak : CDProjectionPeak R a1 b1) => CDProjectionPeak R (KExpr.pi a0 a1) (KExpr.pi b0 b1))
 (fun (meet1 : KExpr) (hs1 : projection_parallel_star R a1 meet1) (hc1 : par_reduces_cd R b1 meet1) => @CDProjectionPeak.mk R (KExpr.pi a0 a1) (KExpr.pi b0 b1) (KExpr.pi meet0 meet1) (projection_parallel_star_congr2 R KExpr.pi (@projection_parallel.pi R) a0 meet0 a1 meet1 hs0 hs1) (@par_reduces_cd.pi R b0 meet0 b1 meet1 hc0 hc1)) p1) p0",
    ),
    DeclarationInput::Proof(
        "cd_projection_peak_forall_",
        r"forall (R : RedEnv)  (a0 b0 a1 b1 : KExpr) (p0 : CDProjectionPeak R a0 b0) (p1 : CDProjectionPeak R a1 b1), CDProjectionPeak R (KExpr.forall_ a0 a1) (KExpr.forall_ b0 b1)",
        r"fun (R : RedEnv)  (a0 b0 a1 b1 : KExpr) (p0 : CDProjectionPeak R a0 b0) (p1 : CDProjectionPeak R a1 b1) => @CDProjectionPeak.rec R a0 b0 (fun (_peak : CDProjectionPeak R a0 b0) => CDProjectionPeak R (KExpr.forall_ a0 a1) (KExpr.forall_ b0 b1))
 (fun (meet0 : KExpr) (hs0 : projection_parallel_star R a0 meet0) (hc0 : par_reduces_cd R b0 meet0) => @CDProjectionPeak.rec R a1 b1 (fun (_peak : CDProjectionPeak R a1 b1) => CDProjectionPeak R (KExpr.forall_ a0 a1) (KExpr.forall_ b0 b1))
 (fun (meet1 : KExpr) (hs1 : projection_parallel_star R a1 meet1) (hc1 : par_reduces_cd R b1 meet1) => @CDProjectionPeak.mk R (KExpr.forall_ a0 a1) (KExpr.forall_ b0 b1) (KExpr.forall_ meet0 meet1) (projection_parallel_star_congr2 R KExpr.forall_ (@projection_parallel.forall_ R) a0 meet0 a1 meet1 hs0 hs1) (@par_reduces_cd.forall_ R b0 meet0 b1 meet1 hc0 hc1)) p1) p0",
    ),
    DeclarationInput::Proof(
        "cd_projection_peak_let_cong",
        r"forall (R : RedEnv)  (a0 b0 a1 b1 a2 b2 : KExpr) (p0 : CDProjectionPeak R a0 b0) (p1 : CDProjectionPeak R a1 b1) (p2 : CDProjectionPeak R a2 b2), CDProjectionPeak R (KExpr.let_ a0 a1 a2) (KExpr.let_ b0 b1 b2)",
        r"fun (R : RedEnv)  (a0 b0 a1 b1 a2 b2 : KExpr) (p0 : CDProjectionPeak R a0 b0) (p1 : CDProjectionPeak R a1 b1) (p2 : CDProjectionPeak R a2 b2) => @CDProjectionPeak.rec R a0 b0 (fun (_peak : CDProjectionPeak R a0 b0) => CDProjectionPeak R (KExpr.let_ a0 a1 a2) (KExpr.let_ b0 b1 b2))
 (fun (meet0 : KExpr) (hs0 : projection_parallel_star R a0 meet0) (hc0 : par_reduces_cd R b0 meet0) => @CDProjectionPeak.rec R a1 b1 (fun (_peak : CDProjectionPeak R a1 b1) => CDProjectionPeak R (KExpr.let_ a0 a1 a2) (KExpr.let_ b0 b1 b2))
 (fun (meet1 : KExpr) (hs1 : projection_parallel_star R a1 meet1) (hc1 : par_reduces_cd R b1 meet1) => @CDProjectionPeak.rec R a2 b2 (fun (_peak : CDProjectionPeak R a2 b2) => CDProjectionPeak R (KExpr.let_ a0 a1 a2) (KExpr.let_ b0 b1 b2))
 (fun (meet2 : KExpr) (hs2 : projection_parallel_star R a2 meet2) (hc2 : par_reduces_cd R b2 meet2) => @CDProjectionPeak.mk R (KExpr.let_ a0 a1 a2) (KExpr.let_ b0 b1 b2) (KExpr.let_ meet0 meet1 meet2) (projection_parallel_star_congr3 R KExpr.let_ (@projection_parallel.let_cong R) a0 meet0 a1 meet1 a2 meet2 hs0 hs1 hs2) (@par_reduces_cd.let_cong R b0 meet0 b1 meet1 b2 meet2 hc0 hc1 hc2)) p2) p1) p0",
    ),
    DeclarationInput::Proof(
        "cd_projection_peak_proj",
        r"forall (R : RedEnv) (S : Name) (idx : Nat) (a0 b0 : KExpr) (p0 : CDProjectionPeak R a0 b0), CDProjectionPeak R (KExpr.proj S idx a0) (KExpr.proj S idx b0)",
        r"fun (R : RedEnv) (S : Name) (idx : Nat) (a0 b0 : KExpr) (p0 : CDProjectionPeak R a0 b0) => @CDProjectionPeak.rec R a0 b0 (fun (_peak : CDProjectionPeak R a0 b0) => CDProjectionPeak R (KExpr.proj S idx a0) (KExpr.proj S idx b0))
 (fun (meet0 : KExpr) (hs0 : projection_parallel_star R a0 meet0) (hc0 : par_reduces_cd R b0 meet0) => @CDProjectionPeak.mk R (KExpr.proj S idx a0) (KExpr.proj S idx b0) (KExpr.proj S idx meet0) (projection_parallel_star_congr1 R (KExpr.proj S idx) (fun (x y : KExpr) (h : projection_parallel R x y) => @projection_parallel.proj R S idx x y h) a0 meet0 hs0) (@par_reduces_cd.proj R S idx b0 meet0 hc0)) p0",
    ),
    DeclarationInput::Proof(
        "cd_projection_peak_beta",
        r"forall (R : RedEnv)  (a0 b0 a1 b1 a2 b2 : KExpr) (p0 : CDProjectionPeak R a0 b0) (p1 : CDProjectionPeak R a1 b1) (p2 : CDProjectionPeak R a2 b2), CDProjectionPeak R (instantiate a1 a2) (KExpr.app (KExpr.lam b0 b1) b2)",
        r"fun (R : RedEnv)  (a0 b0 a1 b1 a2 b2 : KExpr) (p0 : CDProjectionPeak R a0 b0) (p1 : CDProjectionPeak R a1 b1) (p2 : CDProjectionPeak R a2 b2) => @CDProjectionPeak.rec R a0 b0 (fun (_peak : CDProjectionPeak R a0 b0) => CDProjectionPeak R (instantiate a1 a2) (KExpr.app (KExpr.lam b0 b1) b2))
 (fun (meet0 : KExpr) (hs0 : projection_parallel_star R a0 meet0) (hc0 : par_reduces_cd R b0 meet0) => @CDProjectionPeak.rec R a1 b1 (fun (_peak : CDProjectionPeak R a1 b1) => CDProjectionPeak R (instantiate a1 a2) (KExpr.app (KExpr.lam b0 b1) b2))
 (fun (meet1 : KExpr) (hs1 : projection_parallel_star R a1 meet1) (hc1 : par_reduces_cd R b1 meet1) => @CDProjectionPeak.rec R a2 b2 (fun (_peak : CDProjectionPeak R a2 b2) => CDProjectionPeak R (instantiate a1 a2) (KExpr.app (KExpr.lam b0 b1) b2))
 (fun (meet2 : KExpr) (hs2 : projection_parallel_star R a2 meet2) (hc2 : par_reduces_cd R b2 meet2) => @CDProjectionPeak.mk R (instantiate a1 a2) (KExpr.app (KExpr.lam b0 b1) b2) (instantiate meet1 meet2) (projection_parallel_instantiate_star R a1 meet1 a2 meet2 hs1 hs2) (@par_reduces_cd.beta R b0 meet0 b1 meet1 b2 meet2 hc0 hc1 hc2)) p2) p1) p0",
    ),
    DeclarationInput::Proof(
        "cd_projection_peak_zeta",
        r"forall (R : RedEnv)  (a0 b0 a1 b1 a2 b2 : KExpr) (p0 : CDProjectionPeak R a0 b0) (p1 : CDProjectionPeak R a1 b1) (p2 : CDProjectionPeak R a2 b2), CDProjectionPeak R (instantiate a2 a1) (KExpr.let_ b0 b1 b2)",
        r"fun (R : RedEnv)  (a0 b0 a1 b1 a2 b2 : KExpr) (p0 : CDProjectionPeak R a0 b0) (p1 : CDProjectionPeak R a1 b1) (p2 : CDProjectionPeak R a2 b2) => @CDProjectionPeak.rec R a0 b0 (fun (_peak : CDProjectionPeak R a0 b0) => CDProjectionPeak R (instantiate a2 a1) (KExpr.let_ b0 b1 b2))
 (fun (meet0 : KExpr) (hs0 : projection_parallel_star R a0 meet0) (hc0 : par_reduces_cd R b0 meet0) => @CDProjectionPeak.rec R a1 b1 (fun (_peak : CDProjectionPeak R a1 b1) => CDProjectionPeak R (instantiate a2 a1) (KExpr.let_ b0 b1 b2))
 (fun (meet1 : KExpr) (hs1 : projection_parallel_star R a1 meet1) (hc1 : par_reduces_cd R b1 meet1) => @CDProjectionPeak.rec R a2 b2 (fun (_peak : CDProjectionPeak R a2 b2) => CDProjectionPeak R (instantiate a2 a1) (KExpr.let_ b0 b1 b2))
 (fun (meet2 : KExpr) (hs2 : projection_parallel_star R a2 meet2) (hc2 : par_reduces_cd R b2 meet2) => @CDProjectionPeak.mk R (instantiate a2 a1) (KExpr.let_ b0 b1 b2) (instantiate meet2 meet1) (projection_parallel_instantiate_star R a2 meet2 a1 meet1 hs2 hs1) (@par_reduces_cd.let_ R b0 meet0 b1 meet1 b2 meet2 hc0 hc1 hc2)) p2) p1) p0",
    ),
    DeclarationInput::Proof(
        "cd_projection_strong_commute",
        r"forall (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (e a b : KExpr) (ha : par_reduces_cd R e a) (hb : projection_parallel R e b), CDProjectionPeak R a b",
        r"fun (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (e a b : KExpr) (ha : par_reduces_cd R e a) (hb : projection_parallel R e b) => @par_reduces_cd.rec R
 (fun (x y : KExpr) (_step : par_reduces_cd R x y) => forall (z : KExpr), projection_parallel R x z -> CDProjectionPeak R y z)
 (fun (x z : KExpr) (h : projection_parallel R x z) => @CDProjectionPeak.mk R x z z (projection_parallel_to_star R x z h) (@par_reduces_cd.refl R z))
 (fun  (a0 b0 a1 b1 a2 b2 : KExpr) (h0 : par_reduces_cd R a0 b0) (h1 : par_reduces_cd R a1 b1) (h2 : par_reduces_cd R a2 b2) (ih0 : forall (z : KExpr), projection_parallel R a0 z -> CDProjectionPeak R b0 z) (ih1 : forall (z : KExpr), projection_parallel R a1 z -> CDProjectionPeak R b1 z) (ih2 : forall (z : KExpr), projection_parallel R a2 z -> CDProjectionPeak R b2 z) (z : KExpr) (hz : projection_parallel R (KExpr.app (KExpr.lam a0 a1) a2) z) => projection_parallel_inv_app R (KExpr.lam a0 a1) a2 z (CDProjectionPeak R (instantiate b1 b2) z) hz
 (fun (head2 g2 : KExpr) (headStep : projection_parallel R (KExpr.lam a0 a1) head2) (hg2 : projection_parallel R a2 g2) (outEq : @Eq KExpr z (KExpr.app head2 g2)) =>
  projection_parallel_inv_lam R a0 a1 head2 (CDProjectionPeak R (instantiate b1 b2) z) headStep
   (fun (g0 g1 : KExpr) (hg0 : projection_parallel R a0 g0) (hg1 : projection_parallel R a1 g1) (headEq : @Eq KExpr head2 (KExpr.lam g0 g1)) => Eq.substType KExpr (fun (changed : KExpr) => CDProjectionPeak R (instantiate b1 b2) changed) (KExpr.app (KExpr.lam g0 g1) g2) z (Eq.symm KExpr z (KExpr.app (KExpr.lam g0 g1) g2) (Eq.trans KExpr z (KExpr.app head2 g2) (KExpr.app (KExpr.lam g0 g1) g2) outEq (Eq.cong KExpr KExpr (fun (head3 : KExpr) => KExpr.app head3 g2) head2 (KExpr.lam g0 g1) headEq))) (cd_projection_peak_beta R b0 g0 b1 g1 b2 g2 (ih0 g0 hg0) (ih1 g1 hg1) (ih2 g2 hg2)))))
 (fun  (a0 b0 a1 b1 : KExpr) (h0 : par_reduces_cd R a0 b0) (h1 : par_reduces_cd R a1 b1) (ih0 : forall (z : KExpr), projection_parallel R a0 z -> CDProjectionPeak R b0 z) (ih1 : forall (z : KExpr), projection_parallel R a1 z -> CDProjectionPeak R b1 z) (z : KExpr) (hz : projection_parallel R (KExpr.app a0 a1) z) => projection_parallel_inv_app R a0 a1 z (CDProjectionPeak R (KExpr.app b0 b1) z) hz (fun (g0 g1 : KExpr) (hg0 : projection_parallel R a0 g0) (hg1 : projection_parallel R a1 g1) (outEq : @Eq KExpr z (KExpr.app g0 g1)) => Eq.substType KExpr (fun (changed : KExpr) => CDProjectionPeak R (KExpr.app b0 b1) changed) (KExpr.app g0 g1) z (Eq.symm KExpr z (KExpr.app g0 g1) outEq) (cd_projection_peak_app R b0 g0 b1 g1 (ih0 g0 hg0) (ih1 g1 hg1))) )
 (fun  (a0 b0 a1 b1 : KExpr) (h0 : par_reduces_cd R a0 b0) (h1 : par_reduces_cd R a1 b1) (ih0 : forall (z : KExpr), projection_parallel R a0 z -> CDProjectionPeak R b0 z) (ih1 : forall (z : KExpr), projection_parallel R a1 z -> CDProjectionPeak R b1 z) (z : KExpr) (hz : projection_parallel R (KExpr.lam a0 a1) z) => projection_parallel_inv_lam R a0 a1 z (CDProjectionPeak R (KExpr.lam b0 b1) z) hz (fun (g0 g1 : KExpr) (hg0 : projection_parallel R a0 g0) (hg1 : projection_parallel R a1 g1) (outEq : @Eq KExpr z (KExpr.lam g0 g1)) => Eq.substType KExpr (fun (changed : KExpr) => CDProjectionPeak R (KExpr.lam b0 b1) changed) (KExpr.lam g0 g1) z (Eq.symm KExpr z (KExpr.lam g0 g1) outEq) (cd_projection_peak_lam R b0 g0 b1 g1 (ih0 g0 hg0) (ih1 g1 hg1))) )
 (fun  (a0 b0 a1 b1 : KExpr) (h0 : par_reduces_cd R a0 b0) (h1 : par_reduces_cd R a1 b1) (ih0 : forall (z : KExpr), projection_parallel R a0 z -> CDProjectionPeak R b0 z) (ih1 : forall (z : KExpr), projection_parallel R a1 z -> CDProjectionPeak R b1 z) (z : KExpr) (hz : projection_parallel R (KExpr.pi a0 a1) z) => projection_parallel_inv_pi R a0 a1 z (CDProjectionPeak R (KExpr.pi b0 b1) z) hz (fun (g0 g1 : KExpr) (hg0 : projection_parallel R a0 g0) (hg1 : projection_parallel R a1 g1) (outEq : @Eq KExpr z (KExpr.pi g0 g1)) => Eq.substType KExpr (fun (changed : KExpr) => CDProjectionPeak R (KExpr.pi b0 b1) changed) (KExpr.pi g0 g1) z (Eq.symm KExpr z (KExpr.pi g0 g1) outEq) (cd_projection_peak_pi R b0 g0 b1 g1 (ih0 g0 hg0) (ih1 g1 hg1))) )
 (fun  (a0 b0 a1 b1 : KExpr) (h0 : par_reduces_cd R a0 b0) (h1 : par_reduces_cd R a1 b1) (ih0 : forall (z : KExpr), projection_parallel R a0 z -> CDProjectionPeak R b0 z) (ih1 : forall (z : KExpr), projection_parallel R a1 z -> CDProjectionPeak R b1 z) (z : KExpr) (hz : projection_parallel R (KExpr.forall_ a0 a1) z) => projection_parallel_inv_pi R a0 a1 z (CDProjectionPeak R (KExpr.forall_ b0 b1) z) hz (fun (g0 g1 : KExpr) (hg0 : projection_parallel R a0 g0) (hg1 : projection_parallel R a1 g1) (outEq : @Eq KExpr z (KExpr.forall_ g0 g1)) => Eq.substType KExpr (fun (changed : KExpr) => CDProjectionPeak R (KExpr.forall_ b0 b1) changed) (KExpr.forall_ g0 g1) z (Eq.symm KExpr z (KExpr.forall_ g0 g1) outEq) (cd_projection_peak_forall_ R b0 g0 b1 g1 (ih0 g0 hg0) (ih1 g1 hg1))) )
 (fun  (a0 b0 a1 b1 a2 b2 : KExpr) (h0 : par_reduces_cd R a0 b0) (h1 : par_reduces_cd R a1 b1) (h2 : par_reduces_cd R a2 b2) (ih0 : forall (z : KExpr), projection_parallel R a0 z -> CDProjectionPeak R b0 z) (ih1 : forall (z : KExpr), projection_parallel R a1 z -> CDProjectionPeak R b1 z) (ih2 : forall (z : KExpr), projection_parallel R a2 z -> CDProjectionPeak R b2 z) (z : KExpr) (hz : projection_parallel R (KExpr.let_ a0 a1 a2) z) => projection_parallel_inv_let_cong R a0 a1 a2 z (CDProjectionPeak R (instantiate b2 b1) z) hz (fun (g0 g1 g2 : KExpr) (hg0 : projection_parallel R a0 g0) (hg1 : projection_parallel R a1 g1) (hg2 : projection_parallel R a2 g2) (outEq : @Eq KExpr z (KExpr.let_ g0 g1 g2)) => Eq.substType KExpr (fun (changed : KExpr) => CDProjectionPeak R (instantiate b2 b1) changed) (KExpr.let_ g0 g1 g2) z (Eq.symm KExpr z (KExpr.let_ g0 g1 g2) outEq) (cd_projection_peak_zeta R b0 g0 b1 g1 b2 g2 (ih0 g0 hg0) (ih1 g1 hg1) (ih2 g2 hg2))) )
 (fun (x y : KExpr) (step : iota_step (red_rec R) x y) (z : KExpr) (hz : projection_parallel R x z) => cd_projection_iota_root R x z y hz step)
 (fun (x y : KExpr) (step : delta_step (red_def R) x y) (z : KExpr) (hz : projection_parallel R x z) => cd_projection_delta_root R x z y hz step)
 (fun  (a0 b0 a1 b1 a2 b2 : KExpr) (h0 : par_reduces_cd R a0 b0) (h1 : par_reduces_cd R a1 b1) (h2 : par_reduces_cd R a2 b2) (ih0 : forall (z : KExpr), projection_parallel R a0 z -> CDProjectionPeak R b0 z) (ih1 : forall (z : KExpr), projection_parallel R a1 z -> CDProjectionPeak R b1 z) (ih2 : forall (z : KExpr), projection_parallel R a2 z -> CDProjectionPeak R b2 z) (z : KExpr) (hz : projection_parallel R (KExpr.let_ a0 a1 a2) z) => projection_parallel_inv_let_cong R a0 a1 a2 z (CDProjectionPeak R (KExpr.let_ b0 b1 b2) z) hz (fun (g0 g1 g2 : KExpr) (hg0 : projection_parallel R a0 g0) (hg1 : projection_parallel R a1 g1) (hg2 : projection_parallel R a2 g2) (outEq : @Eq KExpr z (KExpr.let_ g0 g1 g2)) => Eq.substType KExpr (fun (changed : KExpr) => CDProjectionPeak R (KExpr.let_ b0 b1 b2) changed) (KExpr.let_ g0 g1 g2) z (Eq.symm KExpr z (KExpr.let_ g0 g1 g2) outEq) (cd_projection_peak_let_cong R b0 g0 b1 g1 b2 g2 (ih0 g0 hg0) (ih1 g1 hg1) (ih2 g2 hg2))) )
 (fun (S : Name) (idx : Nat) (a0 b0 : KExpr) (h0 : par_reduces_cd R a0 b0) (ih0 : forall (z : KExpr), projection_parallel R a0 z -> CDProjectionPeak R b0 z) (z : KExpr) (hz : projection_parallel R (KExpr.proj S idx a0) z) => projection_parallel_inv_proj R S idx a0 z (CDProjectionPeak R (KExpr.proj S idx b0) z) hz (fun (g0 : KExpr) (hg0 : projection_parallel R a0 g0) (outEq : @Eq KExpr z (KExpr.proj S idx g0)) => Eq.substType KExpr (fun (changed : KExpr) => CDProjectionPeak R (KExpr.proj S idx b0) changed) (KExpr.proj S idx g0) z (Eq.symm KExpr z (KExpr.proj S idx g0) outEq) (cd_projection_peak_proj R S idx b0 g0 (ih0 g0 hg0))) (fun (value : KExpr) (run : @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx a0)) (@OptionType.some KExpr value)) (outEq : @Eq KExpr z value) => Eq.substType KExpr (fun (changed : KExpr) => CDProjectionPeak R (KExpr.proj S idx b0) changed) value z (Eq.symm KExpr z value outEq) (cd_projection_extract_root R rigid S idx a0 b0 value h0 run))) e a ha b hb",
    ),
    DeclarationInput::Proof(
        "cd_projection_strong_dup_beta",
        r"CDProjectionPeak the_red_env cd_projection_dup_before
 (KExpr.app (KExpr.lam rfnz_nat cd_projection_dup_body) rfnz_zero)",
        r"cd_projection_strong_commute the_red_env reflected_ctor_metadata_rigid
  (KExpr.app (KExpr.lam rfnz_nat cd_projection_dup_body) cdp_prod_inner_projection)
  cd_projection_dup_before (KExpr.app (KExpr.lam rfnz_nat cd_projection_dup_body) rfnz_zero)
  cd_projection_dup_beta_left cd_projection_dup_beta_right",
    ),
    DeclarationInput::Proof(
        "cd_projection_strong_dup_zeta",
        r"CDProjectionPeak the_red_env cd_projection_dup_before
 (KExpr.let_ rfnz_nat rfnz_zero cd_projection_dup_body)",
        r"cd_projection_strong_commute the_red_env reflected_ctor_metadata_rigid
  (KExpr.let_ rfnz_nat cdp_prod_inner_projection cd_projection_dup_body)
  cd_projection_dup_before (KExpr.let_ rfnz_nat rfnz_zero cd_projection_dup_body)
  cd_projection_dup_zeta_left cd_projection_dup_zeta_right",
    ),
    DeclarationInput::Proof(
        "cd_projection_strong_actual_extract",
        r"CDProjectionPeak the_red_env
 (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) ctor_spine_prod_redex",
        r"cd_projection_strong_commute the_red_env reflected_ctor_metadata_rigid
  (KExpr.proj kcre_prod_type_name Nat.zero ctor_spine_prod_before)
  (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) ctor_spine_prod_redex
  cd_projection_extract_actual_left cd_projection_extract_actual_right",
    ),
    DeclarationInput::Proof(
        "cd_projection_strong_nested_context",
        r"CDProjectionPeak the_red_env
 (KExpr.lam rfnz_nat (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value))
 (KExpr.lam rfnz_nat ctor_spine_prod_redex)",
        r"cd_projection_strong_commute the_red_env reflected_ctor_metadata_rigid
  (KExpr.lam rfnz_nat (KExpr.proj kcre_prod_type_name Nat.zero ctor_spine_prod_before))
  (KExpr.lam rfnz_nat (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value))
  (KExpr.lam rfnz_nat ctor_spine_prod_redex)
  (@par_reduces_cd.lam the_red_env rfnz_nat rfnz_nat
   (KExpr.proj kcre_prod_type_name Nat.zero ctor_spine_prod_before)
   (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value)
   (@par_reduces_cd.refl the_red_env rfnz_nat) cd_projection_extract_actual_left)
  (@projection_parallel.lam the_red_env rfnz_nat rfnz_nat
   (KExpr.proj kcre_prod_type_name Nat.zero ctor_spine_prod_before) ctor_spine_prod_redex
   (@projection_parallel.refl the_red_env rfnz_nat) cd_projection_extract_actual_right)",
    ),
    DeclarationInput::Proof(
        "cd_projection_strong_nested_body",
        r"CDProjectionPeak the_red_env projection_parallel_retained_source
 (KExpr.app (KExpr.lam rfnz_nat (KExpr.bvar Nat.zero)) rfnz_zero)",
        r"cd_projection_strong_commute the_red_env reflected_ctor_metadata_rigid
  (KExpr.app (KExpr.lam rfnz_nat cd_projection_nested_body) cdp_prod_inner_projection)
  projection_parallel_retained_source (KExpr.app (KExpr.lam rfnz_nat (KExpr.bvar Nat.zero)) rfnz_zero)
  (cd_projection_beta_source_left the_red_env rfnz_nat cd_projection_nested_body cdp_prod_inner_projection)
  (cd_projection_beta_source_right the_red_env rfnz_nat rfnz_nat cd_projection_nested_body (KExpr.bvar Nat.zero)
   cdp_prod_inner_projection rfnz_zero (@projection_parallel.refl the_red_env rfnz_nat)
   cd_projection_nested_body_step projection_parallel_inner_step)",
    ),
    DeclarationInput::Proof(
        "cd_projection_strong_actual_legs",
        r"forall (C : Type)
 (consume : forall (meet : KExpr),
  projection_parallel_star the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) meet ->
  par_reduces_cd the_red_env ctor_spine_prod_redex meet -> C), C",
        r"fun (C : Type)
 (consume : forall (meet : KExpr),
  projection_parallel_star the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) meet ->
  par_reduces_cd the_red_env ctor_spine_prod_redex meet -> C) => @CDProjectionPeak.rec the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) ctor_spine_prod_redex
  (fun (_square : CDProjectionPeak the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) ctor_spine_prod_redex) => C)
  (fun (meet : KExpr)
   (left : projection_parallel_star the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) meet)
   (right : par_reduces_cd the_red_env ctor_spine_prod_redex meet) => consume meet left right)
  cd_projection_strong_actual_extract",
    ),
];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "forged_cd_projection_wrong_endpoint",
        r"CDProjectionPeak the_red_env
 (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) rfnz_zero",
        r"cd_projection_strong_actual_extract",
    ),
    (
        "forged_cd_projection_reversed_endpoints",
        r"CDProjectionPeak the_red_env
 ctor_spine_prod_redex (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value)",
        r"cd_projection_strong_actual_extract",
    ),
    (
        "forged_cd_projection_left_color",
        r"forall (C : Type)
 (consume : forall (meet : KExpr),
  par_reduces_cd the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) meet ->
  par_reduces_cd the_red_env ctor_spine_prod_redex meet -> C), C",
        r"fun (C : Type)
 (consume : forall (meet : KExpr),
  par_reduces_cd the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) meet ->
  par_reduces_cd the_red_env ctor_spine_prod_redex meet -> C) => @CDProjectionPeak.rec the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) ctor_spine_prod_redex
  (fun (_square : CDProjectionPeak the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) ctor_spine_prod_redex) => C)
  (fun (meet : KExpr)
   (left : projection_parallel_star the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) meet)
   (right : par_reduces_cd the_red_env ctor_spine_prod_redex meet) => consume meet left right)
  cd_projection_strong_actual_extract",
    ),
    (
        "forged_cd_projection_right_color",
        r"forall (C : Type)
 (consume : forall (meet : KExpr),
  projection_parallel_star the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) meet ->
  projection_parallel_star the_red_env ctor_spine_prod_redex meet -> C), C",
        r"fun (C : Type)
 (consume : forall (meet : KExpr),
  projection_parallel_star the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) meet ->
  projection_parallel_star the_red_env ctor_spine_prod_redex meet -> C) => @CDProjectionPeak.rec the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) ctor_spine_prod_redex
  (fun (_square : CDProjectionPeak the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) ctor_spine_prod_redex) => C)
  (fun (meet : KExpr)
   (left : projection_parallel_star the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) meet)
   (right : par_reduces_cd the_red_env ctor_spine_prod_redex meet) => consume meet left right)
  cd_projection_strong_actual_extract",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "projection_parallel_star_congr1",
    "projection_parallel_star_congr2",
    "projection_parallel_star_congr3",
    "cd_projection_peak_app",
    "cd_projection_peak_lam",
    "cd_projection_peak_pi",
    "cd_projection_peak_forall_",
    "cd_projection_peak_let_cong",
    "cd_projection_peak_proj",
    "cd_projection_peak_beta",
    "cd_projection_peak_zeta",
    "cd_projection_strong_commute",
    "cd_projection_strong_dup_beta",
    "cd_projection_strong_dup_zeta",
    "cd_projection_strong_actual_extract",
    "cd_projection_strong_nested_context",
    "cd_projection_strong_nested_body",
    "cd_projection_strong_actual_legs",
];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &[];
