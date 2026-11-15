// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact checked mixed_roots cohort from projection-registration.RmczqJ.
//! Raw input types, values and carrier declarations are preserved verbatim.
//! This reduction evidence is not a typing or source-admission theorem.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Proof(
        "projection_parallel_lift",
        r"forall (R : RedEnv) (e e2 : KExpr) (c amount : Nat) (step : projection_parallel R e e2), projection_parallel R (lift_at e c amount) (lift_at e2 c amount)",
        r"fun (R : RedEnv) (e e2 : KExpr) (c amount : Nat) (step : projection_parallel R e e2) => projection_parallel.rec R
 (fun (x y : KExpr) (_h : projection_parallel R x y) => forall (c amount : Nat), projection_parallel R (lift_at x c amount) (lift_at y c amount))
 (fun (x : KExpr) (c amount : Nat) => projection_parallel.refl R (lift_at x c amount))
 (fun  (f f2 a a2 : KExpr) (_hf : projection_parallel R f f2) (_ha : projection_parallel R a a2) (ihf : forall (c amount : Nat), projection_parallel R (lift_at f c amount) (lift_at f2 c amount)) (iha : forall (c amount : Nat), projection_parallel R (lift_at a c amount) (lift_at a2 c amount)) (c amount : Nat) => (projection_parallel.app R  (lift_at f c amount) (lift_at f2 c amount) (lift_at a c amount) (lift_at a2 c amount) (ihf c amount) (iha c amount)))
 (fun  (A A2 b b2 : KExpr) (_hA : projection_parallel R A A2) (_hb : projection_parallel R b b2) (ihA : forall (c amount : Nat), projection_parallel R (lift_at A c amount) (lift_at A2 c amount)) (ihb : forall (c amount : Nat), projection_parallel R (lift_at b c amount) (lift_at b2 c amount)) (c amount : Nat) => (projection_parallel.lam R  (lift_at A c amount) (lift_at A2 c amount) (lift_at b (Nat.succ c) amount) (lift_at b2 (Nat.succ c) amount) (ihA c amount) (ihb (Nat.succ c) amount)))
 (fun  (A A2 b b2 : KExpr) (_hA : projection_parallel R A A2) (_hb : projection_parallel R b b2) (ihA : forall (c amount : Nat), projection_parallel R (lift_at A c amount) (lift_at A2 c amount)) (ihb : forall (c amount : Nat), projection_parallel R (lift_at b c amount) (lift_at b2 c amount)) (c amount : Nat) => (projection_parallel.pi R  (lift_at A c amount) (lift_at A2 c amount) (lift_at b (Nat.succ c) amount) (lift_at b2 (Nat.succ c) amount) (ihA c amount) (ihb (Nat.succ c) amount)))
 (fun  (A A2 b b2 : KExpr) (_hA : projection_parallel R A A2) (_hb : projection_parallel R b b2) (ihA : forall (c amount : Nat), projection_parallel R (lift_at A c amount) (lift_at A2 c amount)) (ihb : forall (c amount : Nat), projection_parallel R (lift_at b c amount) (lift_at b2 c amount)) (c amount : Nat) => (projection_parallel.forall_ R  (lift_at A c amount) (lift_at A2 c amount) (lift_at b (Nat.succ c) amount) (lift_at b2 (Nat.succ c) amount) (ihA c amount) (ihb (Nat.succ c) amount)))
 (fun  (A A2 a a2 b b2 : KExpr) (_hA : projection_parallel R A A2) (_ha : projection_parallel R a a2) (_hb : projection_parallel R b b2) (ihA : forall (c amount : Nat), projection_parallel R (lift_at A c amount) (lift_at A2 c amount)) (iha : forall (c amount : Nat), projection_parallel R (lift_at a c amount) (lift_at a2 c amount)) (ihb : forall (c amount : Nat), projection_parallel R (lift_at b c amount) (lift_at b2 c amount)) (c amount : Nat) => (projection_parallel.let_cong R  (lift_at A c amount) (lift_at A2 c amount) (lift_at a c amount) (lift_at a2 c amount) (lift_at b (Nat.succ c) amount) (lift_at b2 (Nat.succ c) amount) (ihA c amount) (iha c amount) (ihb (Nat.succ c) amount)))
 (fun (S : Name) (idx : Nat) (subject subject2 : KExpr) (_hsubject : projection_parallel R subject subject2) (ihsubject : forall (c amount : Nat), projection_parallel R (lift_at subject c amount) (lift_at subject2 c amount)) (c amount : Nat) => (projection_parallel.proj R S idx (lift_at subject c amount) (lift_at subject2 c amount) (ihsubject c amount)))
 (fun (S : Name) (idx : Nat) (subject result : KExpr) (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject)) (OptionType.some KExpr result)) (c amount : Nat) => projection_parallel.projection_beta R S idx (lift_at subject c amount) (lift_at result c amount) (projection_post_whnf_lift_at R S idx subject result c amount run))
 e e2 step c amount",
    ),
    DeclarationInput::Proof(
        "projection_parallel_subst_same",
        r"forall (R : RedEnv) (e e2 : KExpr) (v : KExpr) (d : Nat) (step : projection_parallel R e e2), projection_parallel R (instantiate_at e v d) (instantiate_at e2 v d)",
        r"fun (R : RedEnv) (e e2 : KExpr) (v : KExpr) (d : Nat) (step : projection_parallel R e e2) => projection_parallel.rec R
 (fun (x y : KExpr) (_h : projection_parallel R x y) => forall (v : KExpr) (d : Nat), projection_parallel R (instantiate_at x v d) (instantiate_at y v d))
 (fun (x : KExpr) (v : KExpr) (d : Nat) => projection_parallel.refl R (instantiate_at x v d))
 (fun  (f f2 a a2 : KExpr) (_hf : projection_parallel R f f2) (_ha : projection_parallel R a a2) (ihf : forall (v : KExpr) (d : Nat), projection_parallel R (instantiate_at f v d) (instantiate_at f2 v d)) (iha : forall (v : KExpr) (d : Nat), projection_parallel R (instantiate_at a v d) (instantiate_at a2 v d)) (v : KExpr) (d : Nat) => (projection_parallel.app R  (instantiate_at f v d) (instantiate_at f2 v d) (instantiate_at a v d) (instantiate_at a2 v d) (ihf v d) (iha v d)))
 (fun  (A A2 b b2 : KExpr) (_hA : projection_parallel R A A2) (_hb : projection_parallel R b b2) (ihA : forall (v : KExpr) (d : Nat), projection_parallel R (instantiate_at A v d) (instantiate_at A2 v d)) (ihb : forall (v : KExpr) (d : Nat), projection_parallel R (instantiate_at b v d) (instantiate_at b2 v d)) (v : KExpr) (d : Nat) => (projection_parallel.lam R  (instantiate_at A v d) (instantiate_at A2 v d) (instantiate_at b v (Nat.succ d)) (instantiate_at b2 v (Nat.succ d)) (ihA v d) (ihb v (Nat.succ d))))
 (fun  (A A2 b b2 : KExpr) (_hA : projection_parallel R A A2) (_hb : projection_parallel R b b2) (ihA : forall (v : KExpr) (d : Nat), projection_parallel R (instantiate_at A v d) (instantiate_at A2 v d)) (ihb : forall (v : KExpr) (d : Nat), projection_parallel R (instantiate_at b v d) (instantiate_at b2 v d)) (v : KExpr) (d : Nat) => (projection_parallel.pi R  (instantiate_at A v d) (instantiate_at A2 v d) (instantiate_at b v (Nat.succ d)) (instantiate_at b2 v (Nat.succ d)) (ihA v d) (ihb v (Nat.succ d))))
 (fun  (A A2 b b2 : KExpr) (_hA : projection_parallel R A A2) (_hb : projection_parallel R b b2) (ihA : forall (v : KExpr) (d : Nat), projection_parallel R (instantiate_at A v d) (instantiate_at A2 v d)) (ihb : forall (v : KExpr) (d : Nat), projection_parallel R (instantiate_at b v d) (instantiate_at b2 v d)) (v : KExpr) (d : Nat) => (projection_parallel.forall_ R  (instantiate_at A v d) (instantiate_at A2 v d) (instantiate_at b v (Nat.succ d)) (instantiate_at b2 v (Nat.succ d)) (ihA v d) (ihb v (Nat.succ d))))
 (fun  (A A2 a a2 b b2 : KExpr) (_hA : projection_parallel R A A2) (_ha : projection_parallel R a a2) (_hb : projection_parallel R b b2) (ihA : forall (v : KExpr) (d : Nat), projection_parallel R (instantiate_at A v d) (instantiate_at A2 v d)) (iha : forall (v : KExpr) (d : Nat), projection_parallel R (instantiate_at a v d) (instantiate_at a2 v d)) (ihb : forall (v : KExpr) (d : Nat), projection_parallel R (instantiate_at b v d) (instantiate_at b2 v d)) (v : KExpr) (d : Nat) => (projection_parallel.let_cong R  (instantiate_at A v d) (instantiate_at A2 v d) (instantiate_at a v d) (instantiate_at a2 v d) (instantiate_at b v (Nat.succ d)) (instantiate_at b2 v (Nat.succ d)) (ihA v d) (iha v d) (ihb v (Nat.succ d))))
 (fun (S : Name) (idx : Nat) (subject subject2 : KExpr) (_hsubject : projection_parallel R subject subject2) (ihsubject : forall (v : KExpr) (d : Nat), projection_parallel R (instantiate_at subject v d) (instantiate_at subject2 v d)) (v : KExpr) (d : Nat) => (projection_parallel.proj R S idx (instantiate_at subject v d) (instantiate_at subject2 v d) (ihsubject v d)))
 (fun (S : Name) (idx : Nat) (subject result : KExpr) (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject)) (OptionType.some KExpr result)) (v : KExpr) (d : Nat) => projection_parallel.projection_beta R S idx (instantiate_at subject v d) (instantiate_at result v d) (projection_post_whnf_instantiate_at R S idx subject result v d run))
 e e2 step v d",
    ),
    DeclarationInput::Proof(
        "projection_parallel_nat_select",
        r"forall (R : RedEnv) (n : Nat) (a a2 b : KExpr) (h : projection_parallel R a a2), projection_parallel R (Nat.rec (fun (_ : Nat) => KExpr) a (fun (_ : Nat) (_ : KExpr) => b) n) (Nat.rec (fun (_ : Nat) => KExpr) a2 (fun (_ : Nat) (_ : KExpr) => b) n)",
        r"fun (R : RedEnv) (n : Nat) (a a2 b : KExpr) (h : projection_parallel R a a2) => Nat.rec (fun (k : Nat) => projection_parallel R (Nat.rec (fun (_ : Nat) => KExpr) a (fun (_ : Nat) (_ : KExpr) => b) k) (Nat.rec (fun (_ : Nat) => KExpr) a2 (fun (_ : Nat) (_ : KExpr) => b) k)) h (fun (k : Nat) (_ih : projection_parallel R (Nat.rec (fun (_ : Nat) => KExpr) a (fun (_ : Nat) (_ : KExpr) => b) k) (Nat.rec (fun (_ : Nat) => KExpr) a2 (fun (_ : Nat) (_ : KExpr) => b) k)) => projection_parallel.refl R b) n",
    ),
    DeclarationInput::Proof(
        "projection_parallel_subst_bvar",
        r"forall (R : RedEnv) (i : Nat) (v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2), projection_parallel R (instantiate_at (KExpr.bvar i) v d) (instantiate_at (KExpr.bvar i) v2 d)",
        r"fun (R : RedEnv) (i : Nat) (v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2) => projection_parallel_nat_select R (Nat.sub d i) (instantiate_bvar_geq i d v) (instantiate_bvar_geq i d v2) (KExpr.bvar i) (projection_parallel_nat_select R (Nat.sub i d) (lift_at v Nat.zero d) (lift_at v2 Nat.zero d) (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (projection_parallel_lift R v v2 Nat.zero d   step))",
    ),
    DeclarationInput::Proof(
        "projection_parallel_subst_value",
        r"forall (R : RedEnv) (e v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2), projection_parallel R (instantiate_at e v d) (instantiate_at e v2 d)",
        r"fun (R : RedEnv) (e v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2) => KExpr.rec (fun (x : KExpr) => forall (v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2), projection_parallel R (instantiate_at x v d) (instantiate_at x v2 d))
  (fun (u : Level) (v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2) => projection_parallel.refl R (KExpr.sort u))
  (fun (i : Nat) (v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2) => projection_parallel_subst_bvar R i v v2 d   step)
  (fun (f a : KExpr) (ihx : forall (v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2), projection_parallel R (instantiate_at f v d) (instantiate_at f v2 d)) (ihy : forall (v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2), projection_parallel R (instantiate_at a v d) (instantiate_at a v2 d)) (v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2) => projection_parallel.app R (instantiate_at f v d) (instantiate_at f v2 d) (instantiate_at a v d) (instantiate_at a v2 d) (ihx v v2 d step) (ihy v v2 d step))
  (fun (A b : KExpr) (ihx : forall (v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2), projection_parallel R (instantiate_at A v d) (instantiate_at A v2 d)) (ihy : forall (v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2), projection_parallel R (instantiate_at b v d) (instantiate_at b v2 d)) (v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2) => projection_parallel.lam R (instantiate_at A v d) (instantiate_at A v2 d) (instantiate_at b v (Nat.succ d)) (instantiate_at b v2 (Nat.succ d)) (ihx v v2 d step) (ihy v v2 (Nat.succ d) step))
  (fun (A b : KExpr) (ihx : forall (v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2), projection_parallel R (instantiate_at A v d) (instantiate_at A v2 d)) (ihy : forall (v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2), projection_parallel R (instantiate_at b v d) (instantiate_at b v2 d)) (v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2) => projection_parallel.pi R (instantiate_at A v d) (instantiate_at A v2 d) (instantiate_at b v (Nat.succ d)) (instantiate_at b v2 (Nat.succ d)) (ihx v v2 d step) (ihy v v2 (Nat.succ d) step))
  (fun (n : Name) (us : ListType Level) (v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2) => projection_parallel.refl R (KExpr.const n us))
  (fun (A a b : KExpr) (ihA : forall (v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2), projection_parallel R (instantiate_at A v d) (instantiate_at A v2 d)) (iha : forall (v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2), projection_parallel R (instantiate_at a v d) (instantiate_at a v2 d)) (ihb : forall (v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2), projection_parallel R (instantiate_at b v d) (instantiate_at b v2 d)) (v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2) => projection_parallel.let_cong R (instantiate_at A v d) (instantiate_at A v2 d) (instantiate_at a v d) (instantiate_at a v2 d) (instantiate_at b v (Nat.succ d)) (instantiate_at b v2 (Nat.succ d)) (ihA v v2 d step) (iha v v2 d step) (ihb v v2 (Nat.succ d) step))
  (fun (S : Name) (idx : Nat) (subject : KExpr) (ihs : forall (v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2), projection_parallel R (instantiate_at subject v d) (instantiate_at subject v2 d)) (v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2) => projection_parallel.proj R S idx (instantiate_at subject v d) (instantiate_at subject v2 d) (ihs v v2 d step))
  (fun (n : Nat) (v v2 : KExpr) (d : Nat) (step : projection_parallel R v v2) => projection_parallel.refl R (KExpr.lit n))
  e v v2 d step",
    ),
    DeclarationInput::Proof(
        "projection_parallel_to_star",
        r"forall (R : RedEnv) (e e2 : KExpr) (h : projection_parallel R e e2), projection_parallel_star R e e2",
        r"fun (R : RedEnv) (e e2 : KExpr) (h : projection_parallel R e e2) => projection_parallel_star.step R e e2 e2 h (projection_parallel_star.refl R e2)",
    ),
    DeclarationInput::Proof(
        "projection_parallel_star_trans",
        r"forall (R : RedEnv) (e m e2 : KExpr) (h : projection_parallel_star R e m) (tail : projection_parallel_star R m e2), projection_parallel_star R e e2",
        r"fun (R : RedEnv) (e m e2 : KExpr) (h : projection_parallel_star R e m) (tail : projection_parallel_star R m e2) => projection_parallel_star.rec R (fun (x y : KExpr) (_h : projection_parallel_star R x y) => projection_parallel_star R y e2 -> projection_parallel_star R x e2) (fun (x : KExpr) (ht : projection_parallel_star R x e2) => ht) (fun (x y z : KExpr) (hs : projection_parallel R x y) (_ht : projection_parallel_star R y z) (ih : projection_parallel_star R z e2 -> projection_parallel_star R y e2) (rest : projection_parallel_star R z e2) => projection_parallel_star.step R x y e2 hs (ih rest)) e m h tail",
    ),
    DeclarationInput::Proof(
        "projection_parallel_lift_star",
        r"forall (R : RedEnv) (e e2 : KExpr) (c amount : Nat) (h : projection_parallel_star R e e2), projection_parallel_star R (lift_at e c amount) (lift_at e2 c amount)",
        r"fun (R : RedEnv) (e e2 : KExpr) (c amount : Nat) (h : projection_parallel_star R e e2) => projection_parallel_star.rec R (fun (x y : KExpr) (_h : projection_parallel_star R x y) => projection_parallel_star R (lift_at x c amount) (lift_at y c amount)) (fun (x : KExpr) => projection_parallel_star.refl R (lift_at x c amount)) (fun (x y z : KExpr) (hs : projection_parallel R x y) (_ht : projection_parallel_star R y z) (ih : projection_parallel_star R (lift_at y c amount) (lift_at z c amount)) => projection_parallel_star.step R (lift_at x c amount) (lift_at y c amount) (lift_at z c amount) (projection_parallel_lift R x y c amount   hs) ih) e e2 h",
    ),
    DeclarationInput::Proof(
        "projection_parallel_subst_same_star",
        r"forall (R : RedEnv) (e e2 : KExpr) (v : KExpr) (d : Nat) (h : projection_parallel_star R e e2), projection_parallel_star R (instantiate_at e v d) (instantiate_at e2 v d)",
        r"fun (R : RedEnv) (e e2 : KExpr) (v : KExpr) (d : Nat) (h : projection_parallel_star R e e2) => projection_parallel_star.rec R (fun (x y : KExpr) (_h : projection_parallel_star R x y) => projection_parallel_star R (instantiate_at x v d) (instantiate_at y v d)) (fun (x : KExpr) => projection_parallel_star.refl R (instantiate_at x v d)) (fun (x y z : KExpr) (hs : projection_parallel R x y) (_ht : projection_parallel_star R y z) (ih : projection_parallel_star R (instantiate_at y v d) (instantiate_at z v d)) => projection_parallel_star.step R (instantiate_at x v d) (instantiate_at y v d) (instantiate_at z v d) (projection_parallel_subst_same R x y v d   hs) ih) e e2 h",
    ),
    DeclarationInput::Proof(
        "projection_parallel_subst_value_star",
        r"forall (R : RedEnv) (e e2 : KExpr) (body : KExpr) (d : Nat) (h : projection_parallel_star R e e2), projection_parallel_star R (instantiate_at body e d) (instantiate_at body e2 d)",
        r"fun (R : RedEnv) (e e2 : KExpr) (body : KExpr) (d : Nat) (h : projection_parallel_star R e e2) => projection_parallel_star.rec R (fun (x y : KExpr) (_h : projection_parallel_star R x y) => projection_parallel_star R (instantiate_at body x d) (instantiate_at body y d)) (fun (x : KExpr) => projection_parallel_star.refl R (instantiate_at body x d)) (fun (x y z : KExpr) (hs : projection_parallel R x y) (_ht : projection_parallel_star R y z) (ih : projection_parallel_star R (instantiate_at body y d) (instantiate_at body z d)) => projection_parallel_star.step R (instantiate_at body x d) (instantiate_at body y d) (instantiate_at body z d) (projection_parallel_subst_value R body x y d   hs) ih) e e2 h",
    ),
    DeclarationInput::Proof(
        "projection_parallel_subst",
        r"forall (R : RedEnv) (e e2 v v2 : KExpr) (d : Nat) (he : projection_parallel R e e2) (hv : projection_parallel R v v2), projection_parallel_star R (instantiate_at e v d) (instantiate_at e2 v2 d)",
        r"fun (R : RedEnv) (e e2 v v2 : KExpr) (d : Nat) (he : projection_parallel R e e2) (hv : projection_parallel R v v2) => projection_parallel_star.step R (instantiate_at e v d) (instantiate_at e2 v d) (instantiate_at e2 v2 d) (projection_parallel_subst_same R e e2 v d   he) (projection_parallel_to_star R (instantiate_at e2 v d) (instantiate_at e2 v2 d) (projection_parallel_subst_value R e2 v v2 d   hv))",
    ),
    DeclarationInput::Proof(
        "projection_parallel_subst_star",
        r"forall (R : RedEnv) (e e2 v v2 : KExpr) (d : Nat) (he : projection_parallel_star R e e2) (hv : projection_parallel_star R v v2), projection_parallel_star R (instantiate_at e v d) (instantiate_at e2 v2 d)",
        r"fun (R : RedEnv) (e e2 v v2 : KExpr) (d : Nat) (he : projection_parallel_star R e e2) (hv : projection_parallel_star R v v2) => projection_parallel_star_trans R (instantiate_at e v d) (instantiate_at e2 v d) (instantiate_at e2 v2 d) (projection_parallel_subst_same_star R e e2 v d   he) (projection_parallel_subst_value_star R v v2 e2 d   hv)",
    ),
    DeclarationInput::Proof(
        "projection_parallel_instantiate",
        r"forall (R : RedEnv) (e e2 v v2 : KExpr) (he : projection_parallel R e e2) (hv : projection_parallel R v v2), projection_parallel_star R (instantiate e v) (instantiate e2 v2)",
        r"fun (R : RedEnv) (e e2 v v2 : KExpr) (he : projection_parallel R e e2) (hv : projection_parallel R v v2) => projection_parallel_subst R e e2 v v2 Nat.zero     he hv",
    ),
    DeclarationInput::Proof(
        "projection_parallel_instantiate_star",
        r"forall (R : RedEnv) (e e2 v v2 : KExpr) (he : projection_parallel_star R e e2) (hv : projection_parallel_star R v v2), projection_parallel_star R (instantiate e v) (instantiate e2 v2)",
        r"fun (R : RedEnv) (e e2 v v2 : KExpr) (he : projection_parallel_star R e e2) (hv : projection_parallel_star R v v2) => projection_parallel_subst_star R e e2 v v2 Nat.zero     he hv",
    ),
    DeclarationInput::Inductive(
        r"inductive CDProjectionPeak (R : RedEnv) (cdResult projectionResult : KExpr) : Type
| mk : forall (meet : KExpr), projection_parallel_star R cdResult meet -> par_reduces_cd R projectionResult meet -> CDProjectionPeak R cdResult projectionResult",
    ),
    DeclarationInput::Proof(
        "cd_projection_beta_root",
        r"forall (R : RedEnv) (A A2 b b2 a a2 : KExpr)
 (hA : projection_parallel R A A2) (hb : projection_parallel R b b2) (ha : projection_parallel R a a2), CDProjectionPeak R (instantiate b a) (KExpr.app (KExpr.lam A2 b2) a2)",
        r"fun (R : RedEnv) (A A2 b b2 a a2 : KExpr)
 (hA : projection_parallel R A A2) (hb : projection_parallel R b b2) (ha : projection_parallel R a a2) => CDProjectionPeak.mk R (instantiate b a) (KExpr.app (KExpr.lam A2 b2) a2) (instantiate b2 a2)
  (projection_parallel_instantiate R b b2 a a2 hb ha)
  (par_reduces_cd.beta R A2 A2 b2 b2 a2 a2 (par_reduces_cd.refl R A2) (par_reduces_cd.refl R b2) (par_reduces_cd.refl R a2))",
    ),
    DeclarationInput::Proof(
        "cd_projection_beta_source_left",
        r"forall (R : RedEnv) (A b a : KExpr), par_reduces_cd R (KExpr.app (KExpr.lam A b) a) (instantiate b a)",
        r"fun (R : RedEnv) (A b a : KExpr) => par_reduces_cd.beta R A A b b a a (par_reduces_cd.refl R A) (par_reduces_cd.refl R b) (par_reduces_cd.refl R a)",
    ),
    DeclarationInput::Proof(
        "cd_projection_beta_source_right",
        r"forall (R : RedEnv) (A A2 b b2 a a2 : KExpr)
 (hA : projection_parallel R A A2) (hb : projection_parallel R b b2) (ha : projection_parallel R a a2), projection_parallel R (KExpr.app (KExpr.lam A b) a) (KExpr.app (KExpr.lam A2 b2) a2)",
        r"fun (R : RedEnv) (A A2 b b2 a a2 : KExpr)
 (hA : projection_parallel R A A2) (hb : projection_parallel R b b2) (ha : projection_parallel R a a2) => projection_parallel.app R (KExpr.lam A b) (KExpr.lam A2 b2) a a2 (projection_parallel.lam R A A2 b b2 hA hb) ha",
    ),
    DeclarationInput::Proof(
        "cd_projection_zeta_root",
        r"forall (R : RedEnv) (A A2 b b2 a a2 : KExpr)
 (hA : projection_parallel R A A2) (hb : projection_parallel R b b2) (ha : projection_parallel R a a2), CDProjectionPeak R (instantiate b a) (KExpr.let_ A2 a2 b2)",
        r"fun (R : RedEnv) (A A2 b b2 a a2 : KExpr)
 (hA : projection_parallel R A A2) (hb : projection_parallel R b b2) (ha : projection_parallel R a a2) => CDProjectionPeak.mk R (instantiate b a) (KExpr.let_ A2 a2 b2) (instantiate b2 a2)
  (projection_parallel_instantiate R b b2 a a2 hb ha)
  (par_reduces_cd.let_ R A2 A2 a2 a2 b2 b2 (par_reduces_cd.refl R A2) (par_reduces_cd.refl R a2) (par_reduces_cd.refl R b2))",
    ),
    DeclarationInput::Proof(
        "cd_projection_zeta_source_left",
        r"forall (R : RedEnv) (A b a : KExpr), par_reduces_cd R (KExpr.let_ A a b) (instantiate b a)",
        r"fun (R : RedEnv) (A b a : KExpr) => par_reduces_cd.let_ R A A a a b b (par_reduces_cd.refl R A) (par_reduces_cd.refl R a) (par_reduces_cd.refl R b)",
    ),
    DeclarationInput::Proof(
        "cd_projection_zeta_source_right",
        r"forall (R : RedEnv) (A A2 b b2 a a2 : KExpr)
 (hA : projection_parallel R A A2) (hb : projection_parallel R b b2) (ha : projection_parallel R a a2), projection_parallel R (KExpr.let_ A a b) (KExpr.let_ A2 a2 b2)",
        r"fun (R : RedEnv) (A A2 b b2 a a2 : KExpr)
 (hA : projection_parallel R A A2) (hb : projection_parallel R b b2) (ha : projection_parallel R a a2) => projection_parallel.let_cong R A A2 a a2 b b2 hA ha hb",
    ),
    DeclarationInput::Proof(
        "cd_projection_extract_root",
        r"forall (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (S : Name) (idx : Nat) (sub sub2 a : KExpr) (h : par_reduces_cd R sub sub2)
 (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx sub)) (OptionType.some KExpr a)), CDProjectionPeak R (KExpr.proj S idx sub2) a",
        r"fun (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (S : Name) (idx : Nat) (sub sub2 a : KExpr) (h : par_reduces_cd R sub sub2)
 (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx sub)) (OptionType.some KExpr a)) => projection_post_whnf_transport R rigid S idx sub sub2 h a run (CDProjectionPeak R (KExpr.proj S idx sub2) a)
  (fun (b : KExpr) (run2 : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx sub2)) (OptionType.some KExpr b)) (ab : par_reduces_cd R a b) =>
   CDProjectionPeak.mk R (KExpr.proj S idx sub2) a b
    (projection_parallel_to_star R (KExpr.proj S idx sub2) b (projection_parallel.projection_beta R S idx sub2 b run2)) ab)",
    ),
    DeclarationInput::Proof(
        "cd_projection_extract_source_left",
        r"forall (R : RedEnv) (S : Name) (idx : Nat) (sub sub2 : KExpr)
 (h : par_reduces_cd R sub sub2), par_reduces_cd R (KExpr.proj S idx sub) (KExpr.proj S idx sub2)",
        r"fun (R : RedEnv) (S : Name) (idx : Nat) (sub sub2 : KExpr)
 (h : par_reduces_cd R sub sub2) => par_reduces_cd.proj R S idx sub sub2 h",
    ),
    DeclarationInput::Proof(
        "cd_projection_extract_source_right",
        r"forall (R : RedEnv) (S : Name) (idx : Nat) (sub a : KExpr)
 (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx sub)) (OptionType.some KExpr a)), projection_parallel R (KExpr.proj S idx sub) a",
        r"fun (R : RedEnv) (S : Name) (idx : Nat) (sub a : KExpr)
 (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx sub)) (OptionType.some KExpr a)) => projection_parallel.projection_beta R S idx sub a run",
    ),
    DeclarationInput::Proof(
        "projection_parallel_list_apply",
        r"forall (R : RedEnv) (xs ys : ListType KExpr)
 (h : projection_parallel_list R xs ys) (f g : KExpr) (fg : projection_parallel R f g), projection_parallel R (apply_spine xs f) (apply_spine ys g)",
        r"fun (R : RedEnv) (xs ys : ListType KExpr)
 (h : projection_parallel_list R xs ys) (f g : KExpr) (fg : projection_parallel R f g) => projection_parallel_list.rec R
  (fun (as bs : ListType KExpr) (step : projection_parallel_list R as bs) =>
   forall (a b : KExpr), projection_parallel R a b -> projection_parallel R (apply_spine as a) (apply_spine bs b))
  (fun (a b : KExpr) (ab : projection_parallel R a b) => ab)
  (fun (x y : KExpr) (as bs : ListType KExpr) (xy : projection_parallel R x y)
   (tail : projection_parallel_list R as bs)
   (ih : forall (a b : KExpr), projection_parallel R a b -> projection_parallel R (apply_spine as a) (apply_spine bs b))
   (a b : KExpr) (ab : projection_parallel R a b) =>
   ih (KExpr.app a x) (KExpr.app b y) (projection_parallel.app R a b x y ab xy)) xs ys h f g fg",
    ),
    DeclarationInput::Proof(
        "cd_projection_delta_root",
        r"forall (R : RedEnv) (e e2 out : KExpr)
 (step : projection_parallel R e e2) (run : delta_step (red_def R) e out), CDProjectionPeak R out e2",
        r"fun (R : RedEnv) (e e2 out : KExpr)
 (step : projection_parallel R e e2) (run : delta_step (red_def R) e out) => delta_reduct_some_inv_type (red_def R) e out (CDProjectionPeak R out e2) run
  (fun (n : Name) (rhs : KExpr)
   (head : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name n))
   (found : Eq (OptionType KExpr) (kdef_value_at (red_def R) n (kexpr_const_levels (kapp_fn e))) (OptionType.some KExpr rhs))
   (result : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (kapp_args e) rhs)) (OptionType.some KExpr out)) =>
   ProjectionConstSpineView.rec R e e2 (fun (_ : ProjectionConstSpineView R e e2) => CDProjectionPeak R out e2)
    (fun (whole : Eq KExpr (kapp_fn e2) (kapp_fn e))
     (args : projection_parallel_list R (kapp_args e) (kapp_args e2)) =>
     CDProjectionPeak.mk R out e2 (apply_spine (kapp_args e2) rhs)
      (Eq.substType KExpr (fun (v : KExpr) => projection_parallel_star R v (apply_spine (kapp_args e2) rhs))
       (apply_spine (kapp_args e) rhs) out
       (option_some_inj KExpr (apply_spine (kapp_args e) rhs) out result)
       (projection_parallel_to_star R (apply_spine (kapp_args e) rhs) (apply_spine (kapp_args e2) rhs)
        (projection_parallel_list_apply R (kapp_args e) (kapp_args e2) args rhs rhs (projection_parallel.refl R rhs))))
      (par_reduces_cd.delta R e2 (apply_spine (kapp_args e2) rhs)
       (delta_reduct_of_value_some (red_def R) e2 n rhs
        (Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn e2)) (kexpr_const_name (kapp_fn e)) (OptionType.some Name n)
         (Eq.cong KExpr (OptionType Name) kexpr_const_name (kapp_fn e2) (kapp_fn e) whole) head)
        (Eq.trans (OptionType KExpr)
         (kdef_value_at (red_def R) n (kexpr_const_levels (kapp_fn e2)))
         (kdef_value_at (red_def R) n (kexpr_const_levels (kapp_fn e))) (OptionType.some KExpr rhs)
         (Eq.cong KExpr (OptionType KExpr) (fun (hd : KExpr) => kdef_value_at (red_def R) n (kexpr_const_levels hd))
          (kapp_fn e2) (kapp_fn e) whole) found))))
    (projection_parallel_const_spine R n e e2 step head))",
    ),
    DeclarationInput::Data(
        "cd_projection_dup_body",
        r"KExpr",
        r"KExpr.app (KExpr.app ctor_spine_prod_prefix (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero)",
    ),
    DeclarationInput::Data(
        "cd_projection_dup_before",
        r"KExpr",
        r"KExpr.app (KExpr.app ctor_spine_prod_prefix cdp_prod_inner_projection) cdp_prod_inner_projection",
    ),
    DeclarationInput::Data(
        "cd_projection_dup_after",
        r"KExpr",
        r"KExpr.app (KExpr.app ctor_spine_prod_prefix rfnz_zero) rfnz_zero",
    ),
    DeclarationInput::Proof(
        "cd_projection_dup_instantiate",
        r"Eq KExpr (instantiate cd_projection_dup_body cdp_prod_inner_projection) cd_projection_dup_before",
        r"Eq.refl KExpr cd_projection_dup_before",
    ),
    DeclarationInput::Proof(
        "cd_projection_dup_zero_instantiate",
        r"Eq KExpr (instantiate cd_projection_dup_body rfnz_zero) cd_projection_dup_after",
        r"Eq.refl KExpr cd_projection_dup_after",
    ),
    DeclarationInput::Proof(
        "cd_projection_dup_residual",
        r"projection_parallel the_red_env cd_projection_dup_before cd_projection_dup_after",
        r"projection_parallel.app the_red_env
  (KExpr.app ctor_spine_prod_prefix cdp_prod_inner_projection) (KExpr.app ctor_spine_prod_prefix rfnz_zero)
  cdp_prod_inner_projection rfnz_zero
  (projection_parallel.app the_red_env ctor_spine_prod_prefix ctor_spine_prod_prefix cdp_prod_inner_projection rfnz_zero
   (projection_parallel.refl the_red_env ctor_spine_prod_prefix) projection_parallel_inner_step) projection_parallel_inner_step",
    ),
    DeclarationInput::Proof(
        "cd_projection_dup_beta_left",
        r"par_reduces_cd the_red_env
 (KExpr.app (KExpr.lam rfnz_nat cd_projection_dup_body) cdp_prod_inner_projection) cd_projection_dup_before",
        r"cd_projection_beta_source_left the_red_env rfnz_nat cd_projection_dup_body cdp_prod_inner_projection",
    ),
    DeclarationInput::Proof(
        "cd_projection_dup_beta_right",
        r"projection_parallel the_red_env
 (KExpr.app (KExpr.lam rfnz_nat cd_projection_dup_body) cdp_prod_inner_projection)
 (KExpr.app (KExpr.lam rfnz_nat cd_projection_dup_body) rfnz_zero)",
        r"cd_projection_beta_source_right the_red_env rfnz_nat rfnz_nat cd_projection_dup_body cd_projection_dup_body cdp_prod_inner_projection rfnz_zero
  (projection_parallel.refl the_red_env rfnz_nat) (projection_parallel.refl the_red_env cd_projection_dup_body) projection_parallel_inner_step",
    ),
    DeclarationInput::Proof(
        "cd_projection_dup_beta_peak",
        r"CDProjectionPeak the_red_env cd_projection_dup_before
 (KExpr.app (KExpr.lam rfnz_nat cd_projection_dup_body) rfnz_zero)",
        r"cd_projection_beta_root the_red_env rfnz_nat rfnz_nat cd_projection_dup_body cd_projection_dup_body cdp_prod_inner_projection rfnz_zero
  (projection_parallel.refl the_red_env rfnz_nat) (projection_parallel.refl the_red_env cd_projection_dup_body) projection_parallel_inner_step",
    ),
    DeclarationInput::Proof(
        "cd_projection_dup_beta_explicit_meet",
        r"CDProjectionPeak the_red_env cd_projection_dup_before
 (KExpr.app (KExpr.lam rfnz_nat cd_projection_dup_body) rfnz_zero)",
        r"CDProjectionPeak.mk the_red_env cd_projection_dup_before (KExpr.app (KExpr.lam rfnz_nat cd_projection_dup_body) rfnz_zero)
  cd_projection_dup_after (projection_parallel_to_star the_red_env cd_projection_dup_before cd_projection_dup_after cd_projection_dup_residual)
  (cd_projection_beta_source_left the_red_env rfnz_nat cd_projection_dup_body rfnz_zero)",
    ),
    DeclarationInput::Proof(
        "cd_projection_dup_zeta_left",
        r"par_reduces_cd the_red_env
 (KExpr.let_ rfnz_nat cdp_prod_inner_projection cd_projection_dup_body) cd_projection_dup_before",
        r"cd_projection_zeta_source_left the_red_env rfnz_nat cd_projection_dup_body cdp_prod_inner_projection",
    ),
    DeclarationInput::Proof(
        "cd_projection_dup_zeta_right",
        r"projection_parallel the_red_env
 (KExpr.let_ rfnz_nat cdp_prod_inner_projection cd_projection_dup_body) (KExpr.let_ rfnz_nat rfnz_zero cd_projection_dup_body)",
        r"cd_projection_zeta_source_right the_red_env rfnz_nat rfnz_nat cd_projection_dup_body cd_projection_dup_body cdp_prod_inner_projection rfnz_zero
  (projection_parallel.refl the_red_env rfnz_nat) (projection_parallel.refl the_red_env cd_projection_dup_body) projection_parallel_inner_step",
    ),
    DeclarationInput::Proof(
        "cd_projection_dup_zeta_peak",
        r"CDProjectionPeak the_red_env cd_projection_dup_before (KExpr.let_ rfnz_nat rfnz_zero cd_projection_dup_body)",
        r"cd_projection_zeta_root the_red_env rfnz_nat rfnz_nat cd_projection_dup_body cd_projection_dup_body cdp_prod_inner_projection rfnz_zero
  (projection_parallel.refl the_red_env rfnz_nat) (projection_parallel.refl the_red_env cd_projection_dup_body) projection_parallel_inner_step",
    ),
    DeclarationInput::Data(
        "cd_projection_nested_body",
        r"KExpr",
        r"KExpr.proj Name.anonymous Nat.zero (KExpr.app (KExpr.app ctor_spine_prod_prefix (KExpr.bvar Nat.zero)) (KExpr.app rfnz_succ rfnz_zero))",
    ),
    DeclarationInput::Proof(
        "cd_projection_nested_body_run",
        r"Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env cd_projection_nested_body) (OptionType.some KExpr (KExpr.bvar Nat.zero))",
        r"Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.bvar Nat.zero))",
    ),
    DeclarationInput::Proof(
        "cd_projection_nested_body_step",
        r"projection_parallel the_red_env cd_projection_nested_body (KExpr.bvar Nat.zero)",
        r"projection_parallel.projection_beta the_red_env Name.anonymous Nat.zero
  (KExpr.app (KExpr.app ctor_spine_prod_prefix (KExpr.bvar Nat.zero)) (KExpr.app rfnz_succ rfnz_zero))
  (KExpr.bvar Nat.zero) cd_projection_nested_body_run",
    ),
    DeclarationInput::Proof(
        "cd_projection_nested_instantiate",
        r"Eq KExpr (instantiate cd_projection_nested_body cdp_prod_inner_projection)
 projection_parallel_retained_source",
        r"Eq.refl KExpr projection_parallel_retained_source",
    ),
    DeclarationInput::Proof(
        "cd_projection_nested_simultaneous",
        r"projection_parallel_star the_red_env projection_parallel_retained_source rfnz_zero",
        r"projection_parallel_instantiate the_red_env cd_projection_nested_body (KExpr.bvar Nat.zero) cdp_prod_inner_projection rfnz_zero
  cd_projection_nested_body_step projection_parallel_inner_step",
    ),
    DeclarationInput::Proof(
        "cd_projection_nested_beta_peak",
        r"CDProjectionPeak the_red_env projection_parallel_retained_source
 (KExpr.app (KExpr.lam rfnz_nat (KExpr.bvar Nat.zero)) rfnz_zero)",
        r"cd_projection_beta_root the_red_env rfnz_nat rfnz_nat cd_projection_nested_body (KExpr.bvar Nat.zero) cdp_prod_inner_projection rfnz_zero
  (projection_parallel.refl the_red_env rfnz_nat) cd_projection_nested_body_step projection_parallel_inner_step",
    ),
    DeclarationInput::Proof(
        "cd_projection_extract_actual_left",
        r"par_reduces_cd the_red_env
 (KExpr.proj kcre_prod_type_name Nat.zero ctor_spine_prod_before) (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value)",
        r"cd_projection_extract_source_left the_red_env kcre_prod_type_name Nat.zero ctor_spine_prod_before kcre_witness_prod_value ctor_spine_prod_step",
    ),
    DeclarationInput::Proof(
        "cd_projection_extract_actual_right",
        r"projection_parallel the_red_env
 (KExpr.proj kcre_prod_type_name Nat.zero ctor_spine_prod_before) ctor_spine_prod_redex",
        r"cd_projection_extract_source_right the_red_env kcre_prod_type_name Nat.zero ctor_spine_prod_before ctor_spine_prod_redex projection_post_whnf_prod_before_zero",
    ),
    DeclarationInput::Proof(
        "cd_projection_extract_actual_peak",
        r"CDProjectionPeak the_red_env
 (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) ctor_spine_prod_redex",
        r"cd_projection_extract_root the_red_env reflected_ctor_metadata_rigid kcre_prod_type_name Nat.zero ctor_spine_prod_before kcre_witness_prod_value
  ctor_spine_prod_redex ctor_spine_prod_step projection_post_whnf_prod_before_zero",
    ),
    DeclarationInput::Proof(
        "cd_projection_extract_actual_explicit_meet",
        r"CDProjectionPeak the_red_env
 (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) ctor_spine_prod_redex",
        r"CDProjectionPeak.mk the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) ctor_spine_prod_redex rfnz_zero
  (projection_parallel_to_star the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) rfnz_zero projection_parallel_inner_step)
  ctor_spine_prod_beta",
    ),
    DeclarationInput::Data(
        "cd_projection_delta_env",
        r"RedEnv",
        r"RedEnv.mk (red_rec the_red_env)
 (DefEnv.addDef (red_def the_red_env) Name.anonymous (KDefSig.mk (KConstSig.mk (ListType.nil Name) rfnz_nat) cdp_prod_inner_projection))
 (red_ind_ctor the_red_env)",
    ),
    DeclarationInput::Data(
        "cd_projection_delta_head",
        r"KExpr",
        r"KExpr.const Name.anonymous (ListType.nil Level)",
    ),
    DeclarationInput::Proof(
        "cd_projection_delta_inner_run",
        r"Eq (OptionType KExpr)
 (projection_post_whnf_reduct cd_projection_delta_env cdp_prod_inner_projection) (OptionType.some KExpr rfnz_zero)",
        r"Eq.refl (OptionType KExpr) (OptionType.some KExpr rfnz_zero)",
    ),
    DeclarationInput::Proof(
        "cd_projection_delta_inner_step",
        r"projection_parallel cd_projection_delta_env cdp_prod_inner_projection rfnz_zero",
        r"projection_parallel.projection_beta cd_projection_delta_env kcre_prod_type_name Nat.zero kcre_witness_prod_value rfnz_zero cd_projection_delta_inner_run",
    ),
    DeclarationInput::Proof(
        "cd_projection_delta_lookup",
        r"Eq (OptionType KExpr)
 (kdef_value_at (red_def cd_projection_delta_env) Name.anonymous (ListType.nil Level)) (OptionType.some KExpr cdp_prod_inner_projection)",
        r"Eq.refl (OptionType KExpr) (OptionType.some KExpr cdp_prod_inner_projection)",
    ),
    DeclarationInput::Proof(
        "cd_projection_delta_run",
        r"delta_step (red_def cd_projection_delta_env)
 (KExpr.app cd_projection_delta_head cdp_prod_inner_projection) (KExpr.app cdp_prod_inner_projection cdp_prod_inner_projection)",
        r"Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.app cdp_prod_inner_projection cdp_prod_inner_projection))",
    ),
    DeclarationInput::Proof(
        "cd_projection_delta_left",
        r"par_reduces_cd cd_projection_delta_env
 (KExpr.app cd_projection_delta_head cdp_prod_inner_projection) (KExpr.app cdp_prod_inner_projection cdp_prod_inner_projection)",
        r"par_reduces_cd.delta cd_projection_delta_env (KExpr.app cd_projection_delta_head cdp_prod_inner_projection)
  (KExpr.app cdp_prod_inner_projection cdp_prod_inner_projection) cd_projection_delta_run",
    ),
    DeclarationInput::Proof(
        "cd_projection_delta_right",
        r"projection_parallel cd_projection_delta_env
 (KExpr.app cd_projection_delta_head cdp_prod_inner_projection) (KExpr.app cd_projection_delta_head rfnz_zero)",
        r"projection_parallel.app cd_projection_delta_env cd_projection_delta_head cd_projection_delta_head cdp_prod_inner_projection rfnz_zero
  (projection_parallel.refl cd_projection_delta_env cd_projection_delta_head) cd_projection_delta_inner_step",
    ),
    DeclarationInput::Proof(
        "cd_projection_delta_actual_peak",
        r"CDProjectionPeak cd_projection_delta_env
 (KExpr.app cdp_prod_inner_projection cdp_prod_inner_projection) (KExpr.app cd_projection_delta_head rfnz_zero)",
        r"cd_projection_delta_root cd_projection_delta_env (KExpr.app cd_projection_delta_head cdp_prod_inner_projection)
  (KExpr.app cd_projection_delta_head rfnz_zero) (KExpr.app cdp_prod_inner_projection cdp_prod_inner_projection)
  cd_projection_delta_right cd_projection_delta_run",
    ),
    DeclarationInput::Proof(
        "cd_projection_delta_refuses_arity",
        r"Eq (OptionType KExpr)
 (delta_reduct (red_def cd_projection_delta_env)
  (KExpr.app (KExpr.const Name.anonymous (ListType.cons Level Level.zero (ListType.nil Level))) cdp_prod_inner_projection))
 (OptionType.none KExpr)",
        r"Eq.refl (OptionType KExpr) (OptionType.none KExpr)",
    ),
];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "mixed_negative_duplicate_not_reduced",
        r"Eq KExpr
 (instantiate cd_projection_dup_body cdp_prod_inner_projection) cd_projection_dup_after",
        r"Eq.refl KExpr cd_projection_dup_after",
    ),
    (
        "mixed_negative_wrong_relation",
        r"par_reduces_cd the_red_env cdp_prod_inner_projection rfnz_zero",
        r"projection_parallel_inner_step",
    ),
    (
        "mixed_negative_wrong_selected_field",
        r"Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero ctor_spine_prod_before))
 (OptionType.some KExpr (KExpr.app rfnz_succ rfnz_zero))",
        r"Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.app rfnz_succ rfnz_zero))",
    ),
    (
        "mixed_negative_wrong_delta_arity",
        r"delta_step (red_def cd_projection_delta_env)
 (KExpr.app (KExpr.const Name.anonymous (ListType.cons Level Level.zero (ListType.nil Level))) cdp_prod_inner_projection)
 (KExpr.app cdp_prod_inner_projection cdp_prod_inner_projection)",
        r"Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.app cdp_prod_inner_projection cdp_prod_inner_projection))",
    ),
    (
        "mixed_negative_capture_lifted_selected_bvar",
        r"projection_parallel the_red_env
 (lift_at cd_projection_nested_body Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)",
        r"projection_parallel_lift the_red_env cd_projection_nested_body (KExpr.bvar Nat.zero) Nat.zero (Nat.succ Nat.zero) cd_projection_nested_body_step",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "projection_parallel_lift",
    "projection_parallel_subst_same",
    "projection_parallel_nat_select",
    "projection_parallel_subst_bvar",
    "projection_parallel_subst_value",
    "projection_parallel_to_star",
    "projection_parallel_star_trans",
    "projection_parallel_lift_star",
    "projection_parallel_subst_same_star",
    "projection_parallel_subst_value_star",
    "projection_parallel_subst",
    "projection_parallel_subst_star",
    "projection_parallel_instantiate",
    "projection_parallel_instantiate_star",
    "cd_projection_beta_root",
    "cd_projection_beta_source_left",
    "cd_projection_beta_source_right",
    "cd_projection_zeta_root",
    "cd_projection_zeta_source_left",
    "cd_projection_zeta_source_right",
    "cd_projection_extract_root",
    "cd_projection_extract_source_left",
    "cd_projection_extract_source_right",
    "projection_parallel_list_apply",
    "cd_projection_delta_root",
    "cd_projection_dup_instantiate",
    "cd_projection_dup_zero_instantiate",
    "cd_projection_dup_residual",
    "cd_projection_dup_beta_left",
    "cd_projection_dup_beta_right",
    "cd_projection_dup_beta_peak",
    "cd_projection_dup_beta_explicit_meet",
    "cd_projection_dup_zeta_left",
    "cd_projection_dup_zeta_right",
    "cd_projection_dup_zeta_peak",
    "cd_projection_nested_body_run",
    "cd_projection_nested_body_step",
    "cd_projection_nested_instantiate",
    "cd_projection_nested_simultaneous",
    "cd_projection_nested_beta_peak",
    "cd_projection_extract_actual_left",
    "cd_projection_extract_actual_right",
    "cd_projection_extract_actual_peak",
    "cd_projection_extract_actual_explicit_meet",
    "cd_projection_delta_inner_run",
    "cd_projection_delta_inner_step",
    "cd_projection_delta_lookup",
    "cd_projection_delta_run",
    "cd_projection_delta_left",
    "cd_projection_delta_right",
    "cd_projection_delta_actual_peak",
    "cd_projection_delta_refuses_arity",
];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[
    "cd_projection_dup_body",
    "cd_projection_dup_before",
    "cd_projection_dup_after",
    "cd_projection_nested_body",
    "cd_projection_delta_env",
    "cd_projection_delta_head",
];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &["CDProjectionPeak"];
