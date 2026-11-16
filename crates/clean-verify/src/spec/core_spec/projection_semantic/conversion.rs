// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Additive projection-aware semantic conversion: conversion.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Proof(
        "par_reduces_cdp_star_app",
        r"forall (R : RedEnv) (a a2 b b2 : KExpr)
 (ha : par_reduces_cdp_star R a a2) (hb : par_reduces_cdp_star R b b2), par_reduces_cdp_star R (KExpr.app a b) (KExpr.app a2 b2)",
        r"fun (R : RedEnv) (a a2 b b2 : KExpr)
 (ha : par_reduces_cdp_star R a a2) (hb : par_reduces_cdp_star R b b2) => cd_projection_union_star_to_cdp_star R (KExpr.app a b) (KExpr.app a2 b2)
  (cd_projection_union_star_app R a a2 b b2
   (cdp_star_to_cd_projection_union_star R a a2 ha)
   (cdp_star_to_cd_projection_union_star R b b2 hb))",
    ),
    DeclarationInput::Proof(
        "par_reduces_cdp_star_lam",
        r"forall (R : RedEnv) (a a2 b b2 : KExpr)
 (ha : par_reduces_cdp_star R a a2) (hb : par_reduces_cdp_star R b b2), par_reduces_cdp_star R (KExpr.lam a b) (KExpr.lam a2 b2)",
        r"fun (R : RedEnv) (a a2 b b2 : KExpr)
 (ha : par_reduces_cdp_star R a a2) (hb : par_reduces_cdp_star R b b2) => cd_projection_union_star_to_cdp_star R (KExpr.lam a b) (KExpr.lam a2 b2)
  (cd_projection_union_star_lam R a a2 b b2
   (cdp_star_to_cd_projection_union_star R a a2 ha)
   (cdp_star_to_cd_projection_union_star R b b2 hb))",
    ),
    DeclarationInput::Proof(
        "par_reduces_cdp_star_pi",
        r"forall (R : RedEnv) (a a2 b b2 : KExpr)
 (ha : par_reduces_cdp_star R a a2) (hb : par_reduces_cdp_star R b b2), par_reduces_cdp_star R (KExpr.pi a b) (KExpr.pi a2 b2)",
        r"fun (R : RedEnv) (a a2 b b2 : KExpr)
 (ha : par_reduces_cdp_star R a a2) (hb : par_reduces_cdp_star R b b2) => cd_projection_union_star_to_cdp_star R (KExpr.pi a b) (KExpr.pi a2 b2)
  (cd_projection_union_star_pi R a a2 b b2
   (cdp_star_to_cd_projection_union_star R a a2 ha)
   (cdp_star_to_cd_projection_union_star R b b2 hb))",
    ),
    DeclarationInput::Proof(
        "par_reduces_cdp_star_forall_",
        r"forall (R : RedEnv) (a a2 b b2 : KExpr)
 (ha : par_reduces_cdp_star R a a2) (hb : par_reduces_cdp_star R b b2), par_reduces_cdp_star R (KExpr.forall_ a b) (KExpr.forall_ a2 b2)",
        r"fun (R : RedEnv) (a a2 b b2 : KExpr)
 (ha : par_reduces_cdp_star R a a2) (hb : par_reduces_cdp_star R b b2) => cd_projection_union_star_to_cdp_star R (KExpr.forall_ a b) (KExpr.forall_ a2 b2)
  (cd_projection_union_star_forall_ R a a2 b b2
   (cdp_star_to_cd_projection_union_star R a a2 ha)
   (cdp_star_to_cd_projection_union_star R b b2 hb))",
    ),
    DeclarationInput::Proof(
        "par_reduces_cdp_star_let_cong",
        r"forall (R : RedEnv) (A A2 a a2 b b2 : KExpr)
 (hA : par_reduces_cdp_star R A A2) (ha : par_reduces_cdp_star R a a2)
 (hb : par_reduces_cdp_star R b b2), par_reduces_cdp_star R (KExpr.let_ A a b) (KExpr.let_ A2 a2 b2)",
        r"fun (R : RedEnv) (A A2 a a2 b b2 : KExpr)
 (hA : par_reduces_cdp_star R A A2) (ha : par_reduces_cdp_star R a a2)
 (hb : par_reduces_cdp_star R b b2) => cd_projection_union_star_to_cdp_star R (KExpr.let_ A a b) (KExpr.let_ A2 a2 b2)
  (cd_projection_union_star_let_cong R A A2 a a2 b b2
   (cdp_star_to_cd_projection_union_star R A A2 hA)
   (cdp_star_to_cd_projection_union_star R a a2 ha)
   (cdp_star_to_cd_projection_union_star R b b2 hb))",
    ),
    DeclarationInput::Proof(
        "par_reduces_cdp_star_proj",
        r"forall (R : RedEnv) (S : Name) (i : Nat) (a b : KExpr)
 (h : par_reduces_cdp_star R a b), par_reduces_cdp_star R (KExpr.proj S i a) (KExpr.proj S i b)",
        r"fun (R : RedEnv) (S : Name) (i : Nat) (a b : KExpr)
 (h : par_reduces_cdp_star R a b) => cd_projection_union_star_to_cdp_star R (KExpr.proj S i a) (KExpr.proj S i b)
  (cd_projection_union_star_proj R S i a b (cdp_star_to_cd_projection_union_star R a b h))",
    ),
    DeclarationInput::Proof(
        "semantic_join_cdp_app",
        r"forall (R : RedEnv) (a : KExpr) (a2 : KExpr) (b : KExpr) (b2 : KExpr)
 (ha : SemanticJoinCDP R a a2) (hb : SemanticJoinCDP R b b2), SemanticJoinCDP R (KExpr.app a b) (KExpr.app a2 b2)",
        r"fun (R : RedEnv) (a : KExpr) (a2 : KExpr) (b : KExpr) (b2 : KExpr)
 (ha : SemanticJoinCDP R a a2) (hb : SemanticJoinCDP R b b2) => @SemanticJoinCDP.rec R a a2
  (fun (_ha : SemanticJoinCDP R a a2) => SemanticJoinCDP R (KExpr.app a b) (KExpr.app a2 b2))
  (fun (x : KExpr) (x2 : KExpr) (ax : par_reduces_cdp_star R a x)
    (a2x2 : par_reduces_cdp_star R a2 x2) (xx2 : KExprUniverseEq x x2) =>
    @SemanticJoinCDP.rec R b b2
      (fun (_hb : SemanticJoinCDP R b b2) => SemanticJoinCDP R (KExpr.app a b) (KExpr.app a2 b2))
      (fun (y : KExpr) (y2 : KExpr) (by_path : par_reduces_cdp_star R b y)
        (b2y2 : par_reduces_cdp_star R b2 y2) (yy2 : KExprUniverseEq y y2) =>
        @SemanticJoinCDP.mk R (KExpr.app a b) (KExpr.app a2 b2)
          (KExpr.app x y) (KExpr.app x2 y2)
          (par_reduces_cdp_star_app R a x b y ax by_path)
          (par_reduces_cdp_star_app R a2 x2 b2 y2 a2x2 b2y2)
          (KExprUniverseEq.app x x2 y y2 xx2 yy2)) hb) ha",
    ),
    DeclarationInput::Proof(
        "semantic_join_cdp_lam",
        r"forall (R : RedEnv) (a : KExpr) (a2 : KExpr) (b : KExpr) (b2 : KExpr)
 (ha : SemanticJoinCDP R a a2) (hb : SemanticJoinCDP R b b2), SemanticJoinCDP R (KExpr.lam a b) (KExpr.lam a2 b2)",
        r"fun (R : RedEnv) (a : KExpr) (a2 : KExpr) (b : KExpr) (b2 : KExpr)
 (ha : SemanticJoinCDP R a a2) (hb : SemanticJoinCDP R b b2) => @SemanticJoinCDP.rec R a a2
  (fun (_ha : SemanticJoinCDP R a a2) => SemanticJoinCDP R (KExpr.lam a b) (KExpr.lam a2 b2))
  (fun (x : KExpr) (x2 : KExpr) (ax : par_reduces_cdp_star R a x)
    (a2x2 : par_reduces_cdp_star R a2 x2) (xx2 : KExprUniverseEq x x2) =>
    @SemanticJoinCDP.rec R b b2
      (fun (_hb : SemanticJoinCDP R b b2) => SemanticJoinCDP R (KExpr.lam a b) (KExpr.lam a2 b2))
      (fun (y : KExpr) (y2 : KExpr) (by_path : par_reduces_cdp_star R b y)
        (b2y2 : par_reduces_cdp_star R b2 y2) (yy2 : KExprUniverseEq y y2) =>
        @SemanticJoinCDP.mk R (KExpr.lam a b) (KExpr.lam a2 b2)
          (KExpr.lam x y) (KExpr.lam x2 y2)
          (par_reduces_cdp_star_lam R a x b y ax by_path)
          (par_reduces_cdp_star_lam R a2 x2 b2 y2 a2x2 b2y2)
          (KExprUniverseEq.lam x x2 y y2 xx2 yy2)) hb) ha",
    ),
    DeclarationInput::Proof(
        "semantic_join_cdp_pi",
        r"forall (R : RedEnv) (a : KExpr) (a2 : KExpr) (b : KExpr) (b2 : KExpr)
 (ha : SemanticJoinCDP R a a2) (hb : SemanticJoinCDP R b b2), SemanticJoinCDP R (KExpr.pi a b) (KExpr.pi a2 b2)",
        r"fun (R : RedEnv) (a : KExpr) (a2 : KExpr) (b : KExpr) (b2 : KExpr)
 (ha : SemanticJoinCDP R a a2) (hb : SemanticJoinCDP R b b2) => @SemanticJoinCDP.rec R a a2
  (fun (_ha : SemanticJoinCDP R a a2) => SemanticJoinCDP R (KExpr.pi a b) (KExpr.pi a2 b2))
  (fun (x : KExpr) (x2 : KExpr) (ax : par_reduces_cdp_star R a x)
    (a2x2 : par_reduces_cdp_star R a2 x2) (xx2 : KExprUniverseEq x x2) =>
    @SemanticJoinCDP.rec R b b2
      (fun (_hb : SemanticJoinCDP R b b2) => SemanticJoinCDP R (KExpr.pi a b) (KExpr.pi a2 b2))
      (fun (y : KExpr) (y2 : KExpr) (by_path : par_reduces_cdp_star R b y)
        (b2y2 : par_reduces_cdp_star R b2 y2) (yy2 : KExprUniverseEq y y2) =>
        @SemanticJoinCDP.mk R (KExpr.pi a b) (KExpr.pi a2 b2)
          (KExpr.pi x y) (KExpr.pi x2 y2)
          (par_reduces_cdp_star_pi R a x b y ax by_path)
          (par_reduces_cdp_star_pi R a2 x2 b2 y2 a2x2 b2y2)
          (KExprUniverseEq.pi x x2 y y2 xx2 yy2)) hb) ha",
    ),
    DeclarationInput::Proof(
        "semantic_join_cdp_let",
        r"forall (R : RedEnv)
 (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr)
 (hA : SemanticJoinCDP R A A2) (hv : SemanticJoinCDP R v v2) (hb : SemanticJoinCDP R b b2), SemanticJoinCDP R (KExpr.let_ A v b) (KExpr.let_ A2 v2 b2)",
        r"fun (R : RedEnv)
 (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr)
 (hA : SemanticJoinCDP R A A2) (hv : SemanticJoinCDP R v v2) (hb : SemanticJoinCDP R b b2) => @SemanticJoinCDP.rec R A A2
  (fun (_hA : SemanticJoinCDP R A A2) => SemanticJoinCDP R (KExpr.let_ A v b) (KExpr.let_ A2 v2 b2))
  (fun (x : KExpr) (x2 : KExpr) (Ax : par_reduces_cdp_star R A x)
    (A2x2 : par_reduces_cdp_star R A2 x2) (xx2 : KExprUniverseEq x x2) =>
    @SemanticJoinCDP.rec R v v2
      (fun (_hv : SemanticJoinCDP R v v2) => SemanticJoinCDP R (KExpr.let_ A v b) (KExpr.let_ A2 v2 b2))
      (fun (y : KExpr) (y2 : KExpr) (vy : par_reduces_cdp_star R v y)
        (v2y2 : par_reduces_cdp_star R v2 y2) (yy2 : KExprUniverseEq y y2) =>
        @SemanticJoinCDP.rec R b b2
          (fun (_hb : SemanticJoinCDP R b b2) => SemanticJoinCDP R (KExpr.let_ A v b) (KExpr.let_ A2 v2 b2))
          (fun (z : KExpr) (z2 : KExpr) (bz : par_reduces_cdp_star R b z)
            (b2z2 : par_reduces_cdp_star R b2 z2) (zz2 : KExprUniverseEq z z2) =>
            @SemanticJoinCDP.mk R (KExpr.let_ A v b) (KExpr.let_ A2 v2 b2)
              (KExpr.let_ x y z) (KExpr.let_ x2 y2 z2)
              (par_reduces_cdp_star_let_cong R A x v y b z Ax vy bz)
              (par_reduces_cdp_star_let_cong R A2 x2 v2 y2 b2 z2 A2x2 v2y2 b2z2)
              (KExprUniverseEq.let_ x x2 y y2 z z2 xx2 yy2 zz2)) hb) hv) hA",
    ),
    DeclarationInput::Proof(
        "semantic_join_cdp_proj",
        r"forall (R : RedEnv) (n : Name) (i : Nat)
 (e : KExpr) (e2 : KExpr) (h : SemanticJoinCDP R e e2), SemanticJoinCDP R (KExpr.proj n i e) (KExpr.proj n i e2)",
        r"fun (R : RedEnv) (n : Name) (i : Nat)
 (e : KExpr) (e2 : KExpr) (h : SemanticJoinCDP R e e2) => @SemanticJoinCDP.rec R e e2
  (fun (_h : SemanticJoinCDP R e e2) => SemanticJoinCDP R (KExpr.proj n i e) (KExpr.proj n i e2))
  (fun (x : KExpr) (y : KExpr) (ex : par_reduces_cdp_star R e x)
    (e2y : par_reduces_cdp_star R e2 y) (xy : KExprUniverseEq x y) =>
    @SemanticJoinCDP.mk R (KExpr.proj n i e) (KExpr.proj n i e2) (KExpr.proj n i x) (KExpr.proj n i y)
      (par_reduces_cdp_star_proj R n i e x ex) (par_reduces_cdp_star_proj R n i e2 y e2y)
      (KExprUniverseEq.proj n i x y xy)) h",
    ),
    DeclarationInput::Inductive(
        r"inductive DefEqCDPIn (R : RedEnv) : KExpr -> KExpr -> Type
| refl : forall (e : KExpr), DefEqCDPIn R e e
| symm : forall (e : KExpr) (e' : KExpr), DefEqCDPIn R e e' -> DefEqCDPIn R e' e
| trans : forall (e : KExpr) (m : KExpr) (e' : KExpr), DefEqCDPIn R e m -> DefEqCDPIn R m e' -> DefEqCDPIn R e e'
| raw : forall (e : KExpr) (e' : KExpr), par_reduces_cdp R e e' -> DefEqCDPIn R e e'
| levels : forall (e : KExpr) (e' : KExpr), KExprUniverseEq e e' -> DefEqCDPIn R e e'
| app : forall (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), DefEqCDPIn R f f' -> DefEqCDPIn R a a' -> DefEqCDPIn R (KExpr.app f a) (KExpr.app f' a')
| lam : forall (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr), DefEqCDPIn R A A' -> DefEqCDPIn R b b' -> DefEqCDPIn R (KExpr.lam A b) (KExpr.lam A' b')
| pi : forall (A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr), DefEqCDPIn R A A' -> DefEqCDPIn R B B' -> DefEqCDPIn R (KExpr.pi A B) (KExpr.pi A' B')
| let_ : forall (A : KExpr) (A' : KExpr) (v : KExpr) (v' : KExpr) (b : KExpr) (b' : KExpr), DefEqCDPIn R A A' -> DefEqCDPIn R v v' -> DefEqCDPIn R b b' -> DefEqCDPIn R (KExpr.let_ A v b) (KExpr.let_ A' v' b')
| proj : forall (n : Name) (i : Nat) (e : KExpr) (e' : KExpr), DefEqCDPIn R e e' -> DefEqCDPIn R (KExpr.proj n i e) (KExpr.proj n i e')",
    ),
    DeclarationInput::Proof(
        "par_reduces_cdp_star_to_def_eq_cdp_in",
        r"forall (R : RedEnv) (a : KExpr) (b : KExpr)
 (h : par_reduces_cdp_star R a b), DefEqCDPIn R a b",
        r"fun (R : RedEnv) (a : KExpr) (b : KExpr)
 (h : par_reduces_cdp_star R a b) => @par_reduces_cdp_star.rec R
  (fun (x : KExpr) (y : KExpr) (_h : par_reduces_cdp_star R x y) => DefEqCDPIn R x y)
  (fun (x : KExpr) => @DefEqCDPIn.refl R x)
  (fun (x : KExpr) (y : KExpr) (z : KExpr) (xy : par_reduces_cdp R x y)
    (_yz : par_reduces_cdp_star R y z) (ih : DefEqCDPIn R y z) =>
    @DefEqCDPIn.trans R x y z (@DefEqCDPIn.raw R x y xy) ih) a b h",
    ),
    DeclarationInput::Proof(
        "semantic_join_cdp_to_def_eq_cdp_in",
        r"forall (R : RedEnv) (a : KExpr) (b : KExpr)
 (h : SemanticJoinCDP R a b), DefEqCDPIn R a b",
        r"fun (R : RedEnv) (a : KExpr) (b : KExpr)
 (h : SemanticJoinCDP R a b) => @SemanticJoinCDP.rec R a b (fun (_h : SemanticJoinCDP R a b) => DefEqCDPIn R a b)
  (fun (x : KExpr) (y : KExpr) (ax : par_reduces_cdp_star R a x)
    (by_path : par_reduces_cdp_star R b y) (xy : KExprUniverseEq x y) =>
    @DefEqCDPIn.trans R a x b (par_reduces_cdp_star_to_def_eq_cdp_in R a x ax)
      (@DefEqCDPIn.trans R x y b (@DefEqCDPIn.levels R x y xy)
        (@DefEqCDPIn.symm R b y (par_reduces_cdp_star_to_def_eq_cdp_in R b y by_path)))) h",
    ),
    DeclarationInput::Proof(
        "def_eq_cdp_in_to_semantic_join_cdp",
        r"forall (R : RedEnv) (hf : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (a : KExpr) (b : KExpr) (h : DefEqCDPIn R a b), SemanticJoinCDP R a b",
        r"fun (R : RedEnv) (hf : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (a : KExpr) (b : KExpr) (h : DefEqCDPIn R a b) => @DefEqCDPIn.rec R
  (fun (x : KExpr) (y : KExpr) (_h : DefEqCDPIn R x y) => SemanticJoinCDP R x y)
  (fun (x : KExpr) => semantic_join_cdp_refl R x)
  (fun (x : KExpr) (y : KExpr) (_h : DefEqCDPIn R x y) (ih : SemanticJoinCDP R x y) =>
    semantic_join_cdp_symm R x y ih)
  (fun (x : KExpr) (m : KExpr) (y : KExpr) (_hx : DefEqCDPIn R x m) (_hy : DefEqCDPIn R m y)
    (ihx : SemanticJoinCDP R x m) (ihy : SemanticJoinCDP R m y) =>
    semantic_join_cdp_trans R hf rigid x m y ihx ihy)
  (fun (x : KExpr) (y : KExpr) (raw : par_reduces_cdp R x y) => semantic_join_cdp_raw R x y raw)
  (fun (x : KExpr) (y : KExpr) (levels : KExprUniverseEq x y) => semantic_join_cdp_levels R x y levels)
  (fun (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr) (_hf : DefEqCDPIn R f f2) (_ha : DefEqCDPIn R a a2)
    (ihf : SemanticJoinCDP R f f2) (iha : SemanticJoinCDP R a a2) => semantic_join_cdp_app R f f2 a a2 ihf iha)
  (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (_hA : DefEqCDPIn R A A2) (_hb : DefEqCDPIn R b b2)
    (ihA : SemanticJoinCDP R A A2) (ihb : SemanticJoinCDP R b b2) => semantic_join_cdp_lam R A A2 b b2 ihA ihb)
  (fun (A : KExpr) (A2 : KExpr) (B : KExpr) (B2 : KExpr) (_hA : DefEqCDPIn R A A2) (_hB : DefEqCDPIn R B B2)
    (ihA : SemanticJoinCDP R A A2) (ihB : SemanticJoinCDP R B B2) => semantic_join_cdp_pi R A A2 B B2 ihA ihB)
  (fun (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr)
    (_hA : DefEqCDPIn R A A2) (_hv : DefEqCDPIn R v v2) (_hb : DefEqCDPIn R b b2)
    (ihA : SemanticJoinCDP R A A2) (ihv : SemanticJoinCDP R v v2) (ihb : SemanticJoinCDP R b b2) =>
    semantic_join_cdp_let R A A2 v v2 b b2 ihA ihv ihb)
  (fun (n : Name) (i : Nat) (e : KExpr) (e2 : KExpr) (_h : DefEqCDPIn R e e2)
    (ih : SemanticJoinCDP R e e2) => semantic_join_cdp_proj R n i e e2 ih)
  a b h",
    ),
    DeclarationInput::Proof(
        "def_eq_in_to_cdp_in",
        r"forall (R : RedEnv) (a b : KExpr) (h : DefEqIn R a b), DefEqCDPIn R a b",
        r"fun (R : RedEnv) (a b : KExpr) (h : DefEqIn R a b) => @DefEqIn.rec R (fun (x y : KExpr) (_h : DefEqIn R x y) => DefEqCDPIn R x y)
  (fun (x : KExpr) => @DefEqCDPIn.refl R x)
  (fun (x y : KExpr) (_h : DefEqIn R x y) (ih : DefEqCDPIn R x y) => @DefEqCDPIn.symm R x y ih)
  (fun (x m y : KExpr) (_hx : DefEqIn R x m) (_hy : DefEqIn R m y)
   (ihx : DefEqCDPIn R x m) (ihy : DefEqCDPIn R m y) => @DefEqCDPIn.trans R x m y ihx ihy)
  (fun (x y : KExpr) (step : par_reduces_cd R x y) =>
   @DefEqCDPIn.raw R x y (par_reduces_cd_to_cdp R x y step))
  (fun (x y : KExpr) (levels : KExprUniverseEq x y) => @DefEqCDPIn.levels R x y levels)
  (fun (f f2 a a2 : KExpr) (_hf : DefEqIn R f f2) (_ha : DefEqIn R a a2)
   (ihf : DefEqCDPIn R f f2) (iha : DefEqCDPIn R a a2) => @DefEqCDPIn.app R f f2 a a2 ihf iha)
  (fun (A A2 b b2 : KExpr) (_hA : DefEqIn R A A2) (_hb : DefEqIn R b b2)
   (ihA : DefEqCDPIn R A A2) (ihb : DefEqCDPIn R b b2) => @DefEqCDPIn.lam R A A2 b b2 ihA ihb)
  (fun (A A2 B B2 : KExpr) (_hA : DefEqIn R A A2) (_hB : DefEqIn R B B2)
   (ihA : DefEqCDPIn R A A2) (ihB : DefEqCDPIn R B B2) => @DefEqCDPIn.pi R A A2 B B2 ihA ihB)
  (fun (A A2 v v2 b b2 : KExpr) (_hA : DefEqIn R A A2) (_hv : DefEqIn R v v2) (_hb : DefEqIn R b b2)
   (ihA : DefEqCDPIn R A A2) (ihv : DefEqCDPIn R v v2) (ihb : DefEqCDPIn R b b2) =>
   @DefEqCDPIn.let_ R A A2 v v2 b b2 ihA ihv ihb)
  (fun (n : Name) (i : Nat) (e e2 : KExpr) (_h : DefEqIn R e e2)
   (ih : DefEqCDPIn R e e2) => @DefEqCDPIn.proj R n i e e2 ih) a b h",
    ),
    DeclarationInput::Proof(
        "def_eq_cdp_projection_computed",
        r"forall (R : RedEnv) (S : Name) (idx : Nat)
 (subject out : KExpr)
 (run : @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject))
  (@OptionType.some KExpr out)), DefEqCDPIn R (KExpr.proj S idx subject) out",
        r"fun (R : RedEnv) (S : Name) (idx : Nat)
 (subject out : KExpr)
 (run : @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject))
  (@OptionType.some KExpr out)) => @DefEqCDPIn.raw R (KExpr.proj S idx subject) out
  (@par_reduces_cdp.projection_beta R S idx subject out run)",
    ),
    DeclarationInput::Proof(
        "def_eq_cdp_nonzero_projection_conversion",
        r"DefEqCDPIn the_red_env
  (cdp_universe_projection (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (KExpr.sort (Level.succ Level.zero))",
        r"@DefEqCDPIn.trans the_red_env
  (cdp_universe_projection (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (KExpr.sort (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (KExpr.sort (Level.succ Level.zero))
  (@DefEqCDPIn.raw the_red_env
   (cdp_universe_projection (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
   (KExpr.sort (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
   (cdp_universe_projection_step (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero))))
  (@DefEqCDPIn.levels the_red_env
   (KExpr.sort (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
   (KExpr.sort (Level.succ Level.zero))
   (KExprUniverseEq.sort (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero))
    (Level.succ Level.zero) (cdp_universe_nonzero_levels (Level.param Name.anonymous))))",
    ),
    DeclarationInput::Proof(
        "def_eq_cdp_nonzero_projection_join",
        r"SemanticJoinCDP the_red_env
  (cdp_universe_projection (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (KExpr.sort (Level.succ Level.zero))",
        r"def_eq_cdp_in_to_semantic_join_cdp the_red_env the_red_env_faithful reflected_ctor_metadata_rigid
  (cdp_universe_projection (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (KExpr.sort (Level.succ Level.zero)) def_eq_cdp_nonzero_projection_conversion",
    ),
    DeclarationInput::Proof(
        "def_eq_cdp_nonzero_projection_roundtrip",
        r"DefEqCDPIn the_red_env
  (cdp_universe_projection (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (KExpr.sort (Level.succ Level.zero))",
        r"semantic_join_cdp_to_def_eq_cdp_in the_red_env
  (cdp_universe_projection (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (KExpr.sort (Level.succ Level.zero)) def_eq_cdp_nonzero_projection_join",
    ),
    DeclarationInput::Proof(
        "def_eq_cdp_capture_projection",
        r"DefEqCDPIn the_red_env
  (instantiate_at cdp_binding_projection (KExpr.bvar (Nat.succ Nat.zero)) Nat.zero)
  (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))",
        r"@DefEqCDPIn.raw the_red_env
  (instantiate_at cdp_binding_projection (KExpr.bvar (Nat.succ Nat.zero)) Nat.zero)
  (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))
  cdp_binding_same_subst_caller",
    ),
    DeclarationInput::Proof(
        "def_eq_cdp_old_mixed_embedding",
        r"DefEqCDPIn the_red_env semantic_join_mixed_source (KExpr.sort Level.zero)",
        r"def_eq_in_to_cdp_in the_red_env semantic_join_mixed_source (KExpr.sort Level.zero)
  semantic_join_mixed_conversion",
    ),
];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "forged_def_eq_cdp_missing_rigidity",
        r"forall (R : RedEnv) (hf : RedEnvFaithful R)
 (a b : KExpr) (h : DefEqCDPIn R a b), SemanticJoinCDP R a b",
        r"fun (R : RedEnv) (hf : RedEnvFaithful R)
 (a b : KExpr) (h : DefEqCDPIn R a b) => def_eq_cdp_in_to_semantic_join_cdp R hf a b h",
    ),
    (
        "forged_def_eq_cdp_zero_endpoint",
        r"DefEqCDPIn the_red_env
  (cdp_universe_projection (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (KExpr.sort Level.zero)",
        r"def_eq_cdp_nonzero_projection_conversion",
    ),
    (
        "forged_def_eq_cdp_captured_endpoint",
        r"DefEqCDPIn the_red_env
  (instantiate_at cdp_binding_projection (KExpr.bvar (Nat.succ Nat.zero)) Nat.zero)
  (KExpr.lam rfnz_nat (KExpr.bvar Nat.zero))",
        r"def_eq_cdp_capture_projection",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "par_reduces_cdp_star_app",
    "par_reduces_cdp_star_lam",
    "par_reduces_cdp_star_pi",
    "par_reduces_cdp_star_forall_",
    "par_reduces_cdp_star_let_cong",
    "par_reduces_cdp_star_proj",
    "semantic_join_cdp_app",
    "semantic_join_cdp_lam",
    "semantic_join_cdp_pi",
    "semantic_join_cdp_let",
    "semantic_join_cdp_proj",
    "par_reduces_cdp_star_to_def_eq_cdp_in",
    "semantic_join_cdp_to_def_eq_cdp_in",
    "def_eq_cdp_in_to_semantic_join_cdp",
    "def_eq_in_to_cdp_in",
    "def_eq_cdp_projection_computed",
    "def_eq_cdp_nonzero_projection_conversion",
    "def_eq_cdp_nonzero_projection_join",
    "def_eq_cdp_nonzero_projection_roundtrip",
    "def_eq_cdp_capture_projection",
    "def_eq_cdp_old_mixed_embedding",
];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &["DefEqCDPIn"];
