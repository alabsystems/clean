// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Projection-extended capture-avoiding binding operations and actual star.
//! Exact tuples from projection-cdp-bindings.oDjjpI; recursive children are CDP,
//! and the four environment closure assumptions remain explicit.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Proof(
        "cdp_lift_contract_eq",
        r"forall (b a : KExpr) (c amount : Nat), Eq KExpr (lift_at (instantiate b a) c amount) (instantiate (lift_at b (Nat.succ c) amount) (lift_at a c amount))",
        r"fun (b a : KExpr) (c amount : Nat) => Eq.subst Nat (fun (k : Nat) => Eq KExpr (lift_at (instantiate b a) k amount) (instantiate (lift_at b (Nat.succ k) amount) (lift_at a c amount))) (Nat.add Nat.zero c) c (nat_zero_add c) (lift_instantiate_swap b a Nat.zero c amount)",
    ),
    DeclarationInput::Proof(
        "par_lift_cdp",
        r"forall (R : RedEnv) (e e2 : KExpr) (c amount : Nat) (recclosed : RecEnvLiftClosed (red_rec R)) (defclosed : DefEnvLiftClosed (red_def R)) (step : par_reduces_cdp R e e2), par_reduces_cdp R (lift_at e c amount) (lift_at e2 c amount)",
        r"fun (R : RedEnv) (e e2 : KExpr) (c amount : Nat) (recclosed : RecEnvLiftClosed (red_rec R)) (defclosed : DefEnvLiftClosed (red_def R)) (step : par_reduces_cdp R e e2) => par_reduces_cdp.rec R (fun (x y : KExpr) (_h : par_reduces_cdp R x y) => forall (c amount : Nat), par_reduces_cdp R (lift_at x c amount) (lift_at y c amount))
  (fun (x : KExpr) (c amount : Nat) => par_reduces_cdp.refl R (lift_at x c amount))
  (fun  (A A2 b b2 a a2 : KExpr) (_hA : par_reduces_cdp R A A2) (_hb : par_reduces_cdp R b b2) (_ha : par_reduces_cdp R a a2) (ihA : forall (c amount : Nat), par_reduces_cdp R (lift_at A c amount) (lift_at A2 c amount)) (ihb : forall (c amount : Nat), par_reduces_cdp R (lift_at b c amount) (lift_at b2 c amount)) (iha : forall (c amount : Nat), par_reduces_cdp R (lift_at a c amount) (lift_at a2 c amount)) (c amount : Nat) => Eq.substType KExpr (fun (z : KExpr) => par_reduces_cdp R (lift_at (KExpr.app (KExpr.lam A b) a) c amount) z) (instantiate (lift_at b2 (Nat.succ c) amount) (lift_at a2 c amount)) (lift_at (instantiate b2 a2) c amount) (Eq.symm KExpr (lift_at (instantiate b2 a2) c amount) (instantiate (lift_at b2 (Nat.succ c) amount) (lift_at a2 c amount)) (cdp_lift_contract_eq b2 a2 c amount)) (par_reduces_cdp.beta R  (lift_at A c amount) (lift_at A2 c amount) (lift_at b (Nat.succ c) amount) (lift_at b2 (Nat.succ c) amount) (lift_at a c amount) (lift_at a2 c amount) (ihA c amount) (ihb (Nat.succ c) amount) (iha c amount)))
  (fun  (f f2 a a2 : KExpr) (_hf : par_reduces_cdp R f f2) (_ha : par_reduces_cdp R a a2) (ihf : forall (c amount : Nat), par_reduces_cdp R (lift_at f c amount) (lift_at f2 c amount)) (iha : forall (c amount : Nat), par_reduces_cdp R (lift_at a c amount) (lift_at a2 c amount)) (c amount : Nat) => (par_reduces_cdp.app R  (lift_at f c amount) (lift_at f2 c amount) (lift_at a c amount) (lift_at a2 c amount) (ihf c amount) (iha c amount)))
  (fun  (A A2 b b2 : KExpr) (_hA : par_reduces_cdp R A A2) (_hb : par_reduces_cdp R b b2) (ihA : forall (c amount : Nat), par_reduces_cdp R (lift_at A c amount) (lift_at A2 c amount)) (ihb : forall (c amount : Nat), par_reduces_cdp R (lift_at b c amount) (lift_at b2 c amount)) (c amount : Nat) => (par_reduces_cdp.lam R  (lift_at A c amount) (lift_at A2 c amount) (lift_at b (Nat.succ c) amount) (lift_at b2 (Nat.succ c) amount) (ihA c amount) (ihb (Nat.succ c) amount)))
  (fun  (A A2 b b2 : KExpr) (_hA : par_reduces_cdp R A A2) (_hb : par_reduces_cdp R b b2) (ihA : forall (c amount : Nat), par_reduces_cdp R (lift_at A c amount) (lift_at A2 c amount)) (ihb : forall (c amount : Nat), par_reduces_cdp R (lift_at b c amount) (lift_at b2 c amount)) (c amount : Nat) => (par_reduces_cdp.pi R  (lift_at A c amount) (lift_at A2 c amount) (lift_at b (Nat.succ c) amount) (lift_at b2 (Nat.succ c) amount) (ihA c amount) (ihb (Nat.succ c) amount)))
  (fun  (A A2 b b2 : KExpr) (_hA : par_reduces_cdp R A A2) (_hb : par_reduces_cdp R b b2) (ihA : forall (c amount : Nat), par_reduces_cdp R (lift_at A c amount) (lift_at A2 c amount)) (ihb : forall (c amount : Nat), par_reduces_cdp R (lift_at b c amount) (lift_at b2 c amount)) (c amount : Nat) => (par_reduces_cdp.forall_ R  (lift_at A c amount) (lift_at A2 c amount) (lift_at b (Nat.succ c) amount) (lift_at b2 (Nat.succ c) amount) (ihA c amount) (ihb (Nat.succ c) amount)))
  (fun  (A A2 a a2 b b2 : KExpr) (_hA : par_reduces_cdp R A A2) (_ha : par_reduces_cdp R a a2) (_hb : par_reduces_cdp R b b2) (ihA : forall (c amount : Nat), par_reduces_cdp R (lift_at A c amount) (lift_at A2 c amount)) (iha : forall (c amount : Nat), par_reduces_cdp R (lift_at a c amount) (lift_at a2 c amount)) (ihb : forall (c amount : Nat), par_reduces_cdp R (lift_at b c amount) (lift_at b2 c amount)) (c amount : Nat) => Eq.substType KExpr (fun (z : KExpr) => par_reduces_cdp R (lift_at (KExpr.let_ A a b) c amount) z) (instantiate (lift_at b2 (Nat.succ c) amount) (lift_at a2 c amount)) (lift_at (instantiate b2 a2) c amount) (Eq.symm KExpr (lift_at (instantiate b2 a2) c amount) (instantiate (lift_at b2 (Nat.succ c) amount) (lift_at a2 c amount)) (cdp_lift_contract_eq b2 a2 c amount)) (par_reduces_cdp.let_ R  (lift_at A c amount) (lift_at A2 c amount) (lift_at a c amount) (lift_at a2 c amount) (lift_at b (Nat.succ c) amount) (lift_at b2 (Nat.succ c) amount) (ihA c amount) (iha c amount) (ihb (Nat.succ c) amount)))
  (fun (x y : KExpr) (run : iota_step (red_rec R) x y) (c amount : Nat) => par_reduces_cdp.iota R (lift_at x c amount) (lift_at y c amount) (iota_lift_commutes (red_rec R) x y c amount recclosed run))
  (fun (x y : KExpr) (run : delta_step (red_def R) x y) (c amount : Nat) => par_reduces_cdp.delta R (lift_at x c amount) (lift_at y c amount) (delta_lift_commutes (red_def R) x y c amount defclosed run))
  (fun  (A A2 a a2 b b2 : KExpr) (_hA : par_reduces_cdp R A A2) (_ha : par_reduces_cdp R a a2) (_hb : par_reduces_cdp R b b2) (ihA : forall (c amount : Nat), par_reduces_cdp R (lift_at A c amount) (lift_at A2 c amount)) (iha : forall (c amount : Nat), par_reduces_cdp R (lift_at a c amount) (lift_at a2 c amount)) (ihb : forall (c amount : Nat), par_reduces_cdp R (lift_at b c amount) (lift_at b2 c amount)) (c amount : Nat) => (par_reduces_cdp.let_cong R  (lift_at A c amount) (lift_at A2 c amount) (lift_at a c amount) (lift_at a2 c amount) (lift_at b (Nat.succ c) amount) (lift_at b2 (Nat.succ c) amount) (ihA c amount) (iha c amount) (ihb (Nat.succ c) amount)))
  (fun (S : Name) (idx : Nat) (subject subject2 : KExpr) (_hsubject : par_reduces_cdp R subject subject2) (ihsubject : forall (c amount : Nat), par_reduces_cdp R (lift_at subject c amount) (lift_at subject2 c amount)) (c amount : Nat) => (par_reduces_cdp.proj R S idx (lift_at subject c amount) (lift_at subject2 c amount) (ihsubject c amount)))
  (fun (S : Name) (idx : Nat) (subject result : KExpr) (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject)) (OptionType.some KExpr result)) (c amount : Nat) => par_reduces_cdp.projection_beta R S idx (lift_at subject c amount) (lift_at result c amount) (projection_post_whnf_lift_at R S idx subject result c amount run))
  e e2 step c amount",
    ),
    DeclarationInput::Proof(
        "par_subst_same_cdp",
        r"forall (R : RedEnv) (e e2 : KExpr) (v : KExpr) (d : Nat) (recclosed : RecEnvClosed (red_rec R)) (defclosed : DefEnvClosed (red_def R)) (step : par_reduces_cdp R e e2), par_reduces_cdp R (instantiate_at e v d) (instantiate_at e2 v d)",
        r"fun (R : RedEnv) (e e2 : KExpr) (v : KExpr) (d : Nat) (recclosed : RecEnvClosed (red_rec R)) (defclosed : DefEnvClosed (red_def R)) (step : par_reduces_cdp R e e2) => par_reduces_cdp.rec R (fun (x y : KExpr) (_h : par_reduces_cdp R x y) => forall (v : KExpr) (d : Nat), par_reduces_cdp R (instantiate_at x v d) (instantiate_at y v d))
  (fun (x : KExpr) (v : KExpr) (d : Nat) => par_reduces_cdp.refl R (instantiate_at x v d))
  (fun  (A A2 b b2 a a2 : KExpr) (_hA : par_reduces_cdp R A A2) (_hb : par_reduces_cdp R b b2) (_ha : par_reduces_cdp R a a2) (ihA : forall (v : KExpr) (d : Nat), par_reduces_cdp R (instantiate_at A v d) (instantiate_at A2 v d)) (ihb : forall (v : KExpr) (d : Nat), par_reduces_cdp R (instantiate_at b v d) (instantiate_at b2 v d)) (iha : forall (v : KExpr) (d : Nat), par_reduces_cdp R (instantiate_at a v d) (instantiate_at a2 v d)) (v : KExpr) (d : Nat) => Eq.substType KExpr (fun (z : KExpr) => par_reduces_cdp R (instantiate_at (KExpr.app (KExpr.lam A b) a) v d) z) (instantiate (instantiate_at b2 v (Nat.succ d)) (instantiate_at a2 v d)) (instantiate_at (instantiate b2 a2) v d) (Eq.symm KExpr (instantiate_at (instantiate b2 a2) v d) (instantiate (instantiate_at b2 v (Nat.succ d)) (instantiate_at a2 v d)) (instantiate_nested_commutes_zero_subst b2 a2 v d)) (par_reduces_cdp.beta R  (instantiate_at A v d) (instantiate_at A2 v d) (instantiate_at b v (Nat.succ d)) (instantiate_at b2 v (Nat.succ d)) (instantiate_at a v d) (instantiate_at a2 v d) (ihA v d) (ihb v (Nat.succ d)) (iha v d)))
  (fun  (f f2 a a2 : KExpr) (_hf : par_reduces_cdp R f f2) (_ha : par_reduces_cdp R a a2) (ihf : forall (v : KExpr) (d : Nat), par_reduces_cdp R (instantiate_at f v d) (instantiate_at f2 v d)) (iha : forall (v : KExpr) (d : Nat), par_reduces_cdp R (instantiate_at a v d) (instantiate_at a2 v d)) (v : KExpr) (d : Nat) => (par_reduces_cdp.app R  (instantiate_at f v d) (instantiate_at f2 v d) (instantiate_at a v d) (instantiate_at a2 v d) (ihf v d) (iha v d)))
  (fun  (A A2 b b2 : KExpr) (_hA : par_reduces_cdp R A A2) (_hb : par_reduces_cdp R b b2) (ihA : forall (v : KExpr) (d : Nat), par_reduces_cdp R (instantiate_at A v d) (instantiate_at A2 v d)) (ihb : forall (v : KExpr) (d : Nat), par_reduces_cdp R (instantiate_at b v d) (instantiate_at b2 v d)) (v : KExpr) (d : Nat) => (par_reduces_cdp.lam R  (instantiate_at A v d) (instantiate_at A2 v d) (instantiate_at b v (Nat.succ d)) (instantiate_at b2 v (Nat.succ d)) (ihA v d) (ihb v (Nat.succ d))))
  (fun  (A A2 b b2 : KExpr) (_hA : par_reduces_cdp R A A2) (_hb : par_reduces_cdp R b b2) (ihA : forall (v : KExpr) (d : Nat), par_reduces_cdp R (instantiate_at A v d) (instantiate_at A2 v d)) (ihb : forall (v : KExpr) (d : Nat), par_reduces_cdp R (instantiate_at b v d) (instantiate_at b2 v d)) (v : KExpr) (d : Nat) => (par_reduces_cdp.pi R  (instantiate_at A v d) (instantiate_at A2 v d) (instantiate_at b v (Nat.succ d)) (instantiate_at b2 v (Nat.succ d)) (ihA v d) (ihb v (Nat.succ d))))
  (fun  (A A2 b b2 : KExpr) (_hA : par_reduces_cdp R A A2) (_hb : par_reduces_cdp R b b2) (ihA : forall (v : KExpr) (d : Nat), par_reduces_cdp R (instantiate_at A v d) (instantiate_at A2 v d)) (ihb : forall (v : KExpr) (d : Nat), par_reduces_cdp R (instantiate_at b v d) (instantiate_at b2 v d)) (v : KExpr) (d : Nat) => (par_reduces_cdp.forall_ R  (instantiate_at A v d) (instantiate_at A2 v d) (instantiate_at b v (Nat.succ d)) (instantiate_at b2 v (Nat.succ d)) (ihA v d) (ihb v (Nat.succ d))))
  (fun  (A A2 a a2 b b2 : KExpr) (_hA : par_reduces_cdp R A A2) (_ha : par_reduces_cdp R a a2) (_hb : par_reduces_cdp R b b2) (ihA : forall (v : KExpr) (d : Nat), par_reduces_cdp R (instantiate_at A v d) (instantiate_at A2 v d)) (iha : forall (v : KExpr) (d : Nat), par_reduces_cdp R (instantiate_at a v d) (instantiate_at a2 v d)) (ihb : forall (v : KExpr) (d : Nat), par_reduces_cdp R (instantiate_at b v d) (instantiate_at b2 v d)) (v : KExpr) (d : Nat) => Eq.substType KExpr (fun (z : KExpr) => par_reduces_cdp R (instantiate_at (KExpr.let_ A a b) v d) z) (instantiate (instantiate_at b2 v (Nat.succ d)) (instantiate_at a2 v d)) (instantiate_at (instantiate b2 a2) v d) (Eq.symm KExpr (instantiate_at (instantiate b2 a2) v d) (instantiate (instantiate_at b2 v (Nat.succ d)) (instantiate_at a2 v d)) (instantiate_nested_commutes_zero_subst b2 a2 v d)) (par_reduces_cdp.let_ R  (instantiate_at A v d) (instantiate_at A2 v d) (instantiate_at a v d) (instantiate_at a2 v d) (instantiate_at b v (Nat.succ d)) (instantiate_at b2 v (Nat.succ d)) (ihA v d) (iha v d) (ihb v (Nat.succ d))))
  (fun (x y : KExpr) (run : iota_step (red_rec R) x y) (v : KExpr) (d : Nat) => par_reduces_cdp.iota R (instantiate_at x v d) (instantiate_at y v d) (iota_subst_commutes (red_rec R) x y v d recclosed run))
  (fun (x y : KExpr) (run : delta_step (red_def R) x y) (v : KExpr) (d : Nat) => par_reduces_cdp.delta R (instantiate_at x v d) (instantiate_at y v d) (delta_subst_commutes (red_def R) x y v d defclosed run))
  (fun  (A A2 a a2 b b2 : KExpr) (_hA : par_reduces_cdp R A A2) (_ha : par_reduces_cdp R a a2) (_hb : par_reduces_cdp R b b2) (ihA : forall (v : KExpr) (d : Nat), par_reduces_cdp R (instantiate_at A v d) (instantiate_at A2 v d)) (iha : forall (v : KExpr) (d : Nat), par_reduces_cdp R (instantiate_at a v d) (instantiate_at a2 v d)) (ihb : forall (v : KExpr) (d : Nat), par_reduces_cdp R (instantiate_at b v d) (instantiate_at b2 v d)) (v : KExpr) (d : Nat) => (par_reduces_cdp.let_cong R  (instantiate_at A v d) (instantiate_at A2 v d) (instantiate_at a v d) (instantiate_at a2 v d) (instantiate_at b v (Nat.succ d)) (instantiate_at b2 v (Nat.succ d)) (ihA v d) (iha v d) (ihb v (Nat.succ d))))
  (fun (S : Name) (idx : Nat) (subject subject2 : KExpr) (_hsubject : par_reduces_cdp R subject subject2) (ihsubject : forall (v : KExpr) (d : Nat), par_reduces_cdp R (instantiate_at subject v d) (instantiate_at subject2 v d)) (v : KExpr) (d : Nat) => (par_reduces_cdp.proj R S idx (instantiate_at subject v d) (instantiate_at subject2 v d) (ihsubject v d)))
  (fun (S : Name) (idx : Nat) (subject result : KExpr) (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject)) (OptionType.some KExpr result)) (v : KExpr) (d : Nat) => par_reduces_cdp.projection_beta R S idx (instantiate_at subject v d) (instantiate_at result v d) (projection_post_whnf_instantiate_at R S idx subject result v d run))
  e e2 step v d",
    ),
    DeclarationInput::Proof(
        "par_cdp_nat_select",
        r"forall (R : RedEnv) (n : Nat) (a a2 b : KExpr) (h : par_reduces_cdp R a a2), par_reduces_cdp R (Nat.rec (fun (_ : Nat) => KExpr) a (fun (_ : Nat) (_ : KExpr) => b) n) (Nat.rec (fun (_ : Nat) => KExpr) a2 (fun (_ : Nat) (_ : KExpr) => b) n)",
        r"fun (R : RedEnv) (n : Nat) (a a2 b : KExpr) (h : par_reduces_cdp R a a2) => Nat.rec (fun (k : Nat) => par_reduces_cdp R (Nat.rec (fun (_ : Nat) => KExpr) a (fun (_ : Nat) (_ : KExpr) => b) k) (Nat.rec (fun (_ : Nat) => KExpr) a2 (fun (_ : Nat) (_ : KExpr) => b) k)) h (fun (k : Nat) (_ih : par_reduces_cdp R (Nat.rec (fun (_ : Nat) => KExpr) a (fun (_ : Nat) (_ : KExpr) => b) k) (Nat.rec (fun (_ : Nat) => KExpr) a2 (fun (_ : Nat) (_ : KExpr) => b) k)) => par_reduces_cdp.refl R b) n",
    ),
    DeclarationInput::Proof(
        "par_subst_bvar_cdp",
        r"forall (R : RedEnv) (i : Nat) (v v2 : KExpr) (d : Nat) (recclosed : RecEnvLiftClosed (red_rec R)) (defclosed : DefEnvLiftClosed (red_def R)) (step : par_reduces_cdp R v v2), par_reduces_cdp R (instantiate_at (KExpr.bvar i) v d) (instantiate_at (KExpr.bvar i) v2 d)",
        r"fun (R : RedEnv) (i : Nat) (v v2 : KExpr) (d : Nat) (recclosed : RecEnvLiftClosed (red_rec R)) (defclosed : DefEnvLiftClosed (red_def R)) (step : par_reduces_cdp R v v2) => par_cdp_nat_select R (Nat.sub d i) (instantiate_bvar_geq i d v) (instantiate_bvar_geq i d v2) (KExpr.bvar i) (par_cdp_nat_select R (Nat.sub i d) (lift_at v Nat.zero d) (lift_at v2 Nat.zero d) (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (par_lift_cdp R v v2 Nat.zero d recclosed defclosed step))",
    ),
    DeclarationInput::Proof(
        "par_subst_value_cdp",
        r"forall (R : RedEnv) (e v v2 : KExpr) (d : Nat) (recclosed : RecEnvLiftClosed (red_rec R)) (defclosed : DefEnvLiftClosed (red_def R)) (step : par_reduces_cdp R v v2), par_reduces_cdp R (instantiate_at e v d) (instantiate_at e v2 d)",
        r"fun (R : RedEnv) (e v v2 : KExpr) (d : Nat) (recclosed : RecEnvLiftClosed (red_rec R)) (defclosed : DefEnvLiftClosed (red_def R)) (step : par_reduces_cdp R v v2) => KExpr.rec (fun (x : KExpr) => forall (v v2 : KExpr) (d : Nat) (step : par_reduces_cdp R v v2), par_reduces_cdp R (instantiate_at x v d) (instantiate_at x v2 d))
  (fun (u : Level) (v v2 : KExpr) (d : Nat) (step : par_reduces_cdp R v v2) => par_reduces_cdp.refl R (KExpr.sort u))
  (fun (i : Nat) (v v2 : KExpr) (d : Nat) (step : par_reduces_cdp R v v2) => par_subst_bvar_cdp R i v v2 d recclosed defclosed step)
  (fun (f a : KExpr) (ihx : forall (v v2 : KExpr) (d : Nat) (step : par_reduces_cdp R v v2), par_reduces_cdp R (instantiate_at f v d) (instantiate_at f v2 d)) (ihy : forall (v v2 : KExpr) (d : Nat) (step : par_reduces_cdp R v v2), par_reduces_cdp R (instantiate_at a v d) (instantiate_at a v2 d)) (v v2 : KExpr) (d : Nat) (step : par_reduces_cdp R v v2) => par_reduces_cdp.app R (instantiate_at f v d) (instantiate_at f v2 d) (instantiate_at a v d) (instantiate_at a v2 d) (ihx v v2 d step) (ihy v v2 d step))
  (fun (A b : KExpr) (ihx : forall (v v2 : KExpr) (d : Nat) (step : par_reduces_cdp R v v2), par_reduces_cdp R (instantiate_at A v d) (instantiate_at A v2 d)) (ihy : forall (v v2 : KExpr) (d : Nat) (step : par_reduces_cdp R v v2), par_reduces_cdp R (instantiate_at b v d) (instantiate_at b v2 d)) (v v2 : KExpr) (d : Nat) (step : par_reduces_cdp R v v2) => par_reduces_cdp.lam R (instantiate_at A v d) (instantiate_at A v2 d) (instantiate_at b v (Nat.succ d)) (instantiate_at b v2 (Nat.succ d)) (ihx v v2 d step) (ihy v v2 (Nat.succ d) step))
  (fun (A b : KExpr) (ihx : forall (v v2 : KExpr) (d : Nat) (step : par_reduces_cdp R v v2), par_reduces_cdp R (instantiate_at A v d) (instantiate_at A v2 d)) (ihy : forall (v v2 : KExpr) (d : Nat) (step : par_reduces_cdp R v v2), par_reduces_cdp R (instantiate_at b v d) (instantiate_at b v2 d)) (v v2 : KExpr) (d : Nat) (step : par_reduces_cdp R v v2) => par_reduces_cdp.pi R (instantiate_at A v d) (instantiate_at A v2 d) (instantiate_at b v (Nat.succ d)) (instantiate_at b v2 (Nat.succ d)) (ihx v v2 d step) (ihy v v2 (Nat.succ d) step))
  (fun (n : Name) (us : ListType Level) (v v2 : KExpr) (d : Nat) (step : par_reduces_cdp R v v2) => par_reduces_cdp.refl R (KExpr.const n us))
  (fun (A a b : KExpr) (ihA : forall (v v2 : KExpr) (d : Nat) (step : par_reduces_cdp R v v2), par_reduces_cdp R (instantiate_at A v d) (instantiate_at A v2 d)) (iha : forall (v v2 : KExpr) (d : Nat) (step : par_reduces_cdp R v v2), par_reduces_cdp R (instantiate_at a v d) (instantiate_at a v2 d)) (ihb : forall (v v2 : KExpr) (d : Nat) (step : par_reduces_cdp R v v2), par_reduces_cdp R (instantiate_at b v d) (instantiate_at b v2 d)) (v v2 : KExpr) (d : Nat) (step : par_reduces_cdp R v v2) => par_reduces_cdp.let_cong R (instantiate_at A v d) (instantiate_at A v2 d) (instantiate_at a v d) (instantiate_at a v2 d) (instantiate_at b v (Nat.succ d)) (instantiate_at b v2 (Nat.succ d)) (ihA v v2 d step) (iha v v2 d step) (ihb v v2 (Nat.succ d) step))
  (fun (S : Name) (idx : Nat) (subject : KExpr) (ihs : forall (v v2 : KExpr) (d : Nat) (step : par_reduces_cdp R v v2), par_reduces_cdp R (instantiate_at subject v d) (instantiate_at subject v2 d)) (v v2 : KExpr) (d : Nat) (step : par_reduces_cdp R v v2) => par_reduces_cdp.proj R S idx (instantiate_at subject v d) (instantiate_at subject v2 d) (ihs v v2 d step))
  (fun (n : Nat) (v v2 : KExpr) (d : Nat) (step : par_reduces_cdp R v v2) => par_reduces_cdp.refl R (KExpr.lit n))
  e v v2 d step",
    ),
    DeclarationInput::Inductive(
        r"inductive par_reduces_cdp_star (R : RedEnv) : KExpr -> KExpr -> Type
| refl : forall (e : KExpr), par_reduces_cdp_star R e e
| step : forall (e m e2 : KExpr), par_reduces_cdp R e m -> par_reduces_cdp_star R m e2 -> par_reduces_cdp_star R e e2",
    ),
    DeclarationInput::Proof(
        "par_cdp_to_star",
        r"forall (R : RedEnv) (e e2 : KExpr) (h : par_reduces_cdp R e e2), par_reduces_cdp_star R e e2",
        r"fun (R : RedEnv) (e e2 : KExpr) (h : par_reduces_cdp R e e2) => par_reduces_cdp_star.step R e e2 e2 h (par_reduces_cdp_star.refl R e2)",
    ),
    DeclarationInput::Proof(
        "par_cdp_star_trans",
        r"forall (R : RedEnv) (e m e2 : KExpr) (h : par_reduces_cdp_star R e m) (tail : par_reduces_cdp_star R m e2), par_reduces_cdp_star R e e2",
        r"fun (R : RedEnv) (e m e2 : KExpr) (h : par_reduces_cdp_star R e m) (tail : par_reduces_cdp_star R m e2) => par_reduces_cdp_star.rec R (fun (x y : KExpr) (_h : par_reduces_cdp_star R x y) => par_reduces_cdp_star R y e2 -> par_reduces_cdp_star R x e2) (fun (x : KExpr) (ht : par_reduces_cdp_star R x e2) => ht) (fun (x y z : KExpr) (hs : par_reduces_cdp R x y) (_ht : par_reduces_cdp_star R y z) (ih : par_reduces_cdp_star R z e2 -> par_reduces_cdp_star R y e2) (rest : par_reduces_cdp_star R z e2) => par_reduces_cdp_star.step R x y e2 hs (ih rest)) e m h tail",
    ),
    DeclarationInput::Proof(
        "par_lift_cdp_star",
        r"forall (R : RedEnv) (e e2 : KExpr) (c amount : Nat) (recclosed : RecEnvLiftClosed (red_rec R)) (defclosed : DefEnvLiftClosed (red_def R)) (h : par_reduces_cdp_star R e e2), par_reduces_cdp_star R (lift_at e c amount) (lift_at e2 c amount)",
        r"fun (R : RedEnv) (e e2 : KExpr) (c amount : Nat) (recclosed : RecEnvLiftClosed (red_rec R)) (defclosed : DefEnvLiftClosed (red_def R)) (h : par_reduces_cdp_star R e e2) => par_reduces_cdp_star.rec R (fun (x y : KExpr) (_h : par_reduces_cdp_star R x y) => par_reduces_cdp_star R (lift_at x c amount) (lift_at y c amount)) (fun (x : KExpr) => par_reduces_cdp_star.refl R (lift_at x c amount)) (fun (x y z : KExpr) (hs : par_reduces_cdp R x y) (_ht : par_reduces_cdp_star R y z) (ih : par_reduces_cdp_star R (lift_at y c amount) (lift_at z c amount)) => par_reduces_cdp_star.step R (lift_at x c amount) (lift_at y c amount) (lift_at z c amount) (par_lift_cdp R x y c amount recclosed defclosed hs) ih) e e2 h",
    ),
    DeclarationInput::Proof(
        "par_subst_same_cdp_star",
        r"forall (R : RedEnv) (e e2 : KExpr) (v : KExpr) (d : Nat) (recclosed : RecEnvClosed (red_rec R)) (defclosed : DefEnvClosed (red_def R)) (h : par_reduces_cdp_star R e e2), par_reduces_cdp_star R (instantiate_at e v d) (instantiate_at e2 v d)",
        r"fun (R : RedEnv) (e e2 : KExpr) (v : KExpr) (d : Nat) (recclosed : RecEnvClosed (red_rec R)) (defclosed : DefEnvClosed (red_def R)) (h : par_reduces_cdp_star R e e2) => par_reduces_cdp_star.rec R (fun (x y : KExpr) (_h : par_reduces_cdp_star R x y) => par_reduces_cdp_star R (instantiate_at x v d) (instantiate_at y v d)) (fun (x : KExpr) => par_reduces_cdp_star.refl R (instantiate_at x v d)) (fun (x y z : KExpr) (hs : par_reduces_cdp R x y) (_ht : par_reduces_cdp_star R y z) (ih : par_reduces_cdp_star R (instantiate_at y v d) (instantiate_at z v d)) => par_reduces_cdp_star.step R (instantiate_at x v d) (instantiate_at y v d) (instantiate_at z v d) (par_subst_same_cdp R x y v d recclosed defclosed hs) ih) e e2 h",
    ),
    DeclarationInput::Proof(
        "par_subst_value_cdp_star",
        r"forall (R : RedEnv) (e e2 : KExpr) (body : KExpr) (d : Nat) (recclosed : RecEnvLiftClosed (red_rec R)) (defclosed : DefEnvLiftClosed (red_def R)) (h : par_reduces_cdp_star R e e2), par_reduces_cdp_star R (instantiate_at body e d) (instantiate_at body e2 d)",
        r"fun (R : RedEnv) (e e2 : KExpr) (body : KExpr) (d : Nat) (recclosed : RecEnvLiftClosed (red_rec R)) (defclosed : DefEnvLiftClosed (red_def R)) (h : par_reduces_cdp_star R e e2) => par_reduces_cdp_star.rec R (fun (x y : KExpr) (_h : par_reduces_cdp_star R x y) => par_reduces_cdp_star R (instantiate_at body x d) (instantiate_at body y d)) (fun (x : KExpr) => par_reduces_cdp_star.refl R (instantiate_at body x d)) (fun (x y z : KExpr) (hs : par_reduces_cdp R x y) (_ht : par_reduces_cdp_star R y z) (ih : par_reduces_cdp_star R (instantiate_at body y d) (instantiate_at body z d)) => par_reduces_cdp_star.step R (instantiate_at body x d) (instantiate_at body y d) (instantiate_at body z d) (par_subst_value_cdp R body x y d recclosed defclosed hs) ih) e e2 h",
    ),
    DeclarationInput::Proof(
        "par_subst_cdp",
        r"forall (R : RedEnv) (e e2 v v2 : KExpr) (d : Nat) (recclosed : RecEnvClosed (red_rec R)) (defclosed : DefEnvClosed (red_def R)) (reclift : RecEnvLiftClosed (red_rec R)) (deflift : DefEnvLiftClosed (red_def R)) (he : par_reduces_cdp R e e2) (hv : par_reduces_cdp R v v2), par_reduces_cdp_star R (instantiate_at e v d) (instantiate_at e2 v2 d)",
        r"fun (R : RedEnv) (e e2 v v2 : KExpr) (d : Nat) (recclosed : RecEnvClosed (red_rec R)) (defclosed : DefEnvClosed (red_def R)) (reclift : RecEnvLiftClosed (red_rec R)) (deflift : DefEnvLiftClosed (red_def R)) (he : par_reduces_cdp R e e2) (hv : par_reduces_cdp R v v2) => par_reduces_cdp_star.step R (instantiate_at e v d) (instantiate_at e2 v d) (instantiate_at e2 v2 d) (par_subst_same_cdp R e e2 v d recclosed defclosed he) (par_cdp_to_star R (instantiate_at e2 v d) (instantiate_at e2 v2 d) (par_subst_value_cdp R e2 v v2 d reclift deflift hv))",
    ),
    DeclarationInput::Proof(
        "par_subst_cdp_star",
        r"forall (R : RedEnv) (e e2 v v2 : KExpr) (d : Nat) (recclosed : RecEnvClosed (red_rec R)) (defclosed : DefEnvClosed (red_def R)) (reclift : RecEnvLiftClosed (red_rec R)) (deflift : DefEnvLiftClosed (red_def R)) (he : par_reduces_cdp_star R e e2) (hv : par_reduces_cdp_star R v v2), par_reduces_cdp_star R (instantiate_at e v d) (instantiate_at e2 v2 d)",
        r"fun (R : RedEnv) (e e2 v v2 : KExpr) (d : Nat) (recclosed : RecEnvClosed (red_rec R)) (defclosed : DefEnvClosed (red_def R)) (reclift : RecEnvLiftClosed (red_rec R)) (deflift : DefEnvLiftClosed (red_def R)) (he : par_reduces_cdp_star R e e2) (hv : par_reduces_cdp_star R v v2) => par_cdp_star_trans R (instantiate_at e v d) (instantiate_at e2 v d) (instantiate_at e2 v2 d) (par_subst_same_cdp_star R e e2 v d recclosed defclosed he) (par_subst_value_cdp_star R v v2 e2 d reclift deflift hv)",
    ),
    DeclarationInput::Proof(
        "par_instantiate_cdp",
        r"forall (R : RedEnv) (e e2 v v2 : KExpr) (recclosed : RecEnvClosed (red_rec R)) (defclosed : DefEnvClosed (red_def R)) (reclift : RecEnvLiftClosed (red_rec R)) (deflift : DefEnvLiftClosed (red_def R)) (he : par_reduces_cdp R e e2) (hv : par_reduces_cdp R v v2), par_reduces_cdp_star R (instantiate e v) (instantiate e2 v2)",
        r"fun (R : RedEnv) (e e2 v v2 : KExpr) (recclosed : RecEnvClosed (red_rec R)) (defclosed : DefEnvClosed (red_def R)) (reclift : RecEnvLiftClosed (red_rec R)) (deflift : DefEnvLiftClosed (red_def R)) (he : par_reduces_cdp R e e2) (hv : par_reduces_cdp R v v2) => par_subst_cdp R e e2 v v2 Nat.zero recclosed defclosed reclift deflift he hv",
    ),
    DeclarationInput::Proof(
        "par_instantiate_cdp_star",
        r"forall (R : RedEnv) (e e2 v v2 : KExpr) (recclosed : RecEnvClosed (red_rec R)) (defclosed : DefEnvClosed (red_def R)) (reclift : RecEnvLiftClosed (red_rec R)) (deflift : DefEnvLiftClosed (red_def R)) (he : par_reduces_cdp_star R e e2) (hv : par_reduces_cdp_star R v v2), par_reduces_cdp_star R (instantiate e v) (instantiate e2 v2)",
        r"fun (R : RedEnv) (e e2 v v2 : KExpr) (recclosed : RecEnvClosed (red_rec R)) (defclosed : DefEnvClosed (red_def R)) (reclift : RecEnvLiftClosed (red_rec R)) (deflift : DefEnvLiftClosed (red_def R)) (he : par_reduces_cdp_star R e e2) (hv : par_reduces_cdp_star R v v2) => par_subst_cdp_star R e e2 v v2 Nat.zero recclosed defclosed reclift deflift he hv",
    ),
    DeclarationInput::Data(
        "cdp_binding_projection",
        r"KExpr",
        r"KExpr.proj kcre_prod_type_name Nat.zero projection_binding_subject",
    ),
    DeclarationInput::Proof(
        "cdp_binding_projection_step",
        r"par_reduces_cdp the_red_env cdp_binding_projection projection_binding_field",
        r"par_reduces_cdp.projection_beta the_red_env kcre_prod_type_name Nat.zero projection_binding_subject projection_binding_field projection_binding_select",
    ),
    DeclarationInput::Proof(
        "cdp_binding_lift_caller",
        r"par_reduces_cdp the_red_env
 (lift_at cdp_binding_projection Nat.zero (Nat.succ (Nat.succ Nat.zero)))
 (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))",
        r"par_lift_cdp the_red_env cdp_binding_projection projection_binding_field Nat.zero (Nat.succ (Nat.succ Nat.zero))
  the_red_env_rec_lift_closed_via_checker_b2 the_red_env_def_lift_closed_via_checker_b2 cdp_binding_projection_step",
    ),
    DeclarationInput::Proof(
        "cdp_binding_same_subst_caller",
        r"par_reduces_cdp the_red_env
 (instantiate_at cdp_binding_projection (KExpr.bvar (Nat.succ Nat.zero)) Nat.zero)
 (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))",
        r"par_subst_same_cdp the_red_env cdp_binding_projection projection_binding_field (KExpr.bvar (Nat.succ Nat.zero)) Nat.zero
  the_red_env_rec_closed_via_checker_b2 the_red_env_def_closed_via_checker_b2 cdp_binding_projection_step",
    ),
    DeclarationInput::Proof(
        "cdp_binding_two_sided_caller",
        r"par_reduces_cdp_star the_red_env
 (instantiate cdp_binding_projection cdp_binding_projection)
 (KExpr.lam rfnz_nat (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))))",
        r"par_instantiate_cdp the_red_env cdp_binding_projection projection_binding_field cdp_binding_projection projection_binding_field
  the_red_env_rec_closed_via_checker_b2 the_red_env_def_closed_via_checker_b2
  the_red_env_rec_lift_closed_via_checker_b2 the_red_env_def_lift_closed_via_checker_b2
  cdp_binding_projection_step cdp_binding_projection_step",
    ),
    DeclarationInput::Proof(
        "cdp_binding_two_sided_star_caller",
        r"par_reduces_cdp_star the_red_env
 (instantiate cdp_binding_projection cdp_binding_projection)
 (KExpr.lam rfnz_nat (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))))",
        r"par_instantiate_cdp_star the_red_env cdp_binding_projection projection_binding_field cdp_binding_projection projection_binding_field
  the_red_env_rec_closed_via_checker_b2 the_red_env_def_closed_via_checker_b2
  the_red_env_rec_lift_closed_via_checker_b2 the_red_env_def_lift_closed_via_checker_b2
  (par_cdp_to_star the_red_env cdp_binding_projection projection_binding_field cdp_binding_projection_step)
  (par_cdp_to_star the_red_env cdp_binding_projection projection_binding_field cdp_binding_projection_step)",
    ),
    DeclarationInput::Proof(
        "cdp_binding_beta_step",
        r"par_reduces_cdp the_red_env
 (KExpr.app (KExpr.lam rfnz_nat cdp_binding_projection) (KExpr.bvar (Nat.succ Nat.zero)))
 (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))",
        r"par_reduces_cdp.beta the_red_env rfnz_nat rfnz_nat cdp_binding_projection projection_binding_field
  (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar (Nat.succ Nat.zero))
  (par_reduces_cdp.refl the_red_env rfnz_nat) cdp_binding_projection_step
  (par_reduces_cdp.refl the_red_env (KExpr.bvar (Nat.succ Nat.zero)))",
    ),
    DeclarationInput::Proof(
        "cdp_binding_beta_lift_caller",
        r"par_reduces_cdp the_red_env
 (lift_at (KExpr.app (KExpr.lam rfnz_nat cdp_binding_projection) (KExpr.bvar (Nat.succ Nat.zero))) Nat.zero (Nat.succ Nat.zero))
 (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))",
        r"par_lift_cdp the_red_env
  (KExpr.app (KExpr.lam rfnz_nat cdp_binding_projection) (KExpr.bvar (Nat.succ Nat.zero)))
  (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) Nat.zero (Nat.succ Nat.zero)
  the_red_env_rec_lift_closed_via_checker_b2 the_red_env_def_lift_closed_via_checker_b2 cdp_binding_beta_step",
    ),
    DeclarationInput::Proof(
        "cdp_binding_zeta_step",
        r"par_reduces_cdp the_red_env
 (KExpr.let_ rfnz_nat (KExpr.bvar (Nat.succ Nat.zero)) cdp_binding_projection)
 (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))",
        r"par_reduces_cdp.let_ the_red_env rfnz_nat rfnz_nat
  (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar (Nat.succ Nat.zero)) cdp_binding_projection projection_binding_field
  (par_reduces_cdp.refl the_red_env rfnz_nat)
  (par_reduces_cdp.refl the_red_env (KExpr.bvar (Nat.succ Nat.zero))) cdp_binding_projection_step",
    ),
    DeclarationInput::Proof(
        "cdp_binding_zeta_subst_caller",
        r"par_reduces_cdp the_red_env
 (instantiate_at (KExpr.let_ rfnz_nat (KExpr.bvar (Nat.succ Nat.zero)) cdp_binding_projection) (KExpr.bvar Nat.zero) Nat.zero)
 (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ Nat.zero)))",
        r"par_subst_same_cdp the_red_env
  (KExpr.let_ rfnz_nat (KExpr.bvar (Nat.succ Nat.zero)) cdp_binding_projection)
  (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero) Nat.zero
  the_red_env_rec_closed_via_checker_b2 the_red_env_def_closed_via_checker_b2 cdp_binding_zeta_step",
    ),
];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "forged_cdp_binding_capture",
        r"par_reduces_cdp the_red_env
 (instantiate_at cdp_binding_projection (KExpr.bvar (Nat.succ Nat.zero)) Nat.zero)
 (KExpr.lam rfnz_nat (KExpr.bvar Nat.zero))",
        r"cdp_binding_same_subst_caller",
    ),
    (
        "forged_cdp_binding_unlifted",
        r"par_reduces_cdp the_red_env
 (lift_at cdp_binding_projection Nat.zero (Nat.succ (Nat.succ Nat.zero))) projection_binding_field",
        r"cdp_binding_lift_caller",
    ),
    (
        "forged_cdp_binding_double_capture",
        r"par_reduces_cdp_star the_red_env
 (instantiate cdp_binding_projection cdp_binding_projection)
 (KExpr.lam rfnz_nat (KExpr.lam rfnz_nat (KExpr.bvar Nat.zero)))",
        r"cdp_binding_two_sided_caller",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "cdp_lift_contract_eq",
    "par_lift_cdp",
    "par_subst_same_cdp",
    "par_cdp_nat_select",
    "par_subst_bvar_cdp",
    "par_subst_value_cdp",
    "par_cdp_to_star",
    "par_cdp_star_trans",
    "par_lift_cdp_star",
    "par_subst_same_cdp_star",
    "par_subst_value_cdp_star",
    "par_subst_cdp",
    "par_subst_cdp_star",
    "par_instantiate_cdp",
    "par_instantiate_cdp_star",
    "cdp_binding_projection_step",
    "cdp_binding_lift_caller",
    "cdp_binding_same_subst_caller",
    "cdp_binding_two_sided_caller",
    "cdp_binding_two_sided_star_caller",
    "cdp_binding_beta_step",
    "cdp_binding_beta_lift_caller",
    "cdp_binding_zeta_step",
    "cdp_binding_zeta_subst_caller",
];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &["cdp_binding_projection"];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &["par_reduces_cdp_star"];
