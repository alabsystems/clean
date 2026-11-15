// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Additive projection-aware semantic conversion: injectivity.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Proof(
        "par_reduces_cdp_sort_inv_eq",
        r"forall (R : RedEnv) (u : Level) (out : KExpr) (h : par_reduces_cdp R (KExpr.sort u) out), Eq KExpr out (KExpr.sort u)",
        r"fun (R : RedEnv) (u : Level) (out : KExpr) (h : par_reduces_cdp R (KExpr.sort u) out) => par_reduces_cdp.rec R (fun (e e2 : KExpr) (_h : par_reduces_cdp R e e2) => Eq KExpr e (KExpr.sort u) -> Eq KExpr e2 (KExpr.sort u))
  (fun (e : KExpr) (same : Eq KExpr e (KExpr.sort u)) => same)
  (fun (A A2 b b2 a a2 : KExpr) (h_A : par_reduces_cdp R A A2) (h_b : par_reduces_cdp R b b2) (h_a : par_reduces_cdp R a a2) (_ih_A : Eq KExpr A (KExpr.sort u) -> Eq KExpr A2 (KExpr.sort u)) (_ih_b : Eq KExpr b (KExpr.sort u) -> Eq KExpr b2 (KExpr.sort u)) (_ih_a : Eq KExpr a (KExpr.sort u) -> Eq KExpr a2 (KExpr.sort u)) (same : Eq KExpr (KExpr.app (KExpr.lam A b) a) (KExpr.sort u)) => Empty.rec (fun (_bad : Empty) => Eq KExpr (instantiate b2 a2) (KExpr.sort u)) (kexpr_discr_t Empty (KExpr.app (KExpr.lam A b) a) (KExpr.sort u) same (Eq.refl Bool Bool.false)))
  (fun (f f2 a a2 : KExpr) (h_f : par_reduces_cdp R f f2) (h_a : par_reduces_cdp R a a2) (_ih_f : Eq KExpr f (KExpr.sort u) -> Eq KExpr f2 (KExpr.sort u)) (_ih_a : Eq KExpr a (KExpr.sort u) -> Eq KExpr a2 (KExpr.sort u)) (same : Eq KExpr (KExpr.app f a) (KExpr.sort u)) => Empty.rec (fun (_bad : Empty) => Eq KExpr (KExpr.app f2 a2) (KExpr.sort u)) (kexpr_discr_t Empty (KExpr.app f a) (KExpr.sort u) same (Eq.refl Bool Bool.false)))
  (fun (A A2 b b2 : KExpr) (h_A : par_reduces_cdp R A A2) (h_b : par_reduces_cdp R b b2) (_ih_A : Eq KExpr A (KExpr.sort u) -> Eq KExpr A2 (KExpr.sort u)) (_ih_b : Eq KExpr b (KExpr.sort u) -> Eq KExpr b2 (KExpr.sort u)) (same : Eq KExpr (KExpr.lam A b) (KExpr.sort u)) => Empty.rec (fun (_bad : Empty) => Eq KExpr (KExpr.lam A2 b2) (KExpr.sort u)) (kexpr_discr_t Empty (KExpr.lam A b) (KExpr.sort u) same (Eq.refl Bool Bool.false)))
  (fun (A A2 b b2 : KExpr) (h_A : par_reduces_cdp R A A2) (h_b : par_reduces_cdp R b b2) (_ih_A : Eq KExpr A (KExpr.sort u) -> Eq KExpr A2 (KExpr.sort u)) (_ih_b : Eq KExpr b (KExpr.sort u) -> Eq KExpr b2 (KExpr.sort u)) (same : Eq KExpr (KExpr.pi A b) (KExpr.sort u)) => Empty.rec (fun (_bad : Empty) => Eq KExpr (KExpr.pi A2 b2) (KExpr.sort u)) (kexpr_discr_t Empty (KExpr.pi A b) (KExpr.sort u) same (Eq.refl Bool Bool.false)))
  (fun (A A2 b b2 : KExpr) (h_A : par_reduces_cdp R A A2) (h_b : par_reduces_cdp R b b2) (_ih_A : Eq KExpr A (KExpr.sort u) -> Eq KExpr A2 (KExpr.sort u)) (_ih_b : Eq KExpr b (KExpr.sort u) -> Eq KExpr b2 (KExpr.sort u)) (same : Eq KExpr (KExpr.forall_ A b) (KExpr.sort u)) => Empty.rec (fun (_bad : Empty) => Eq KExpr (KExpr.forall_ A2 b2) (KExpr.sort u)) (kexpr_discr_t Empty (KExpr.forall_ A b) (KExpr.sort u) same (Eq.refl Bool Bool.false)))
  (fun (A A2 a a2 b b2 : KExpr) (h_A : par_reduces_cdp R A A2) (h_a : par_reduces_cdp R a a2) (h_b : par_reduces_cdp R b b2) (_ih_A : Eq KExpr A (KExpr.sort u) -> Eq KExpr A2 (KExpr.sort u)) (_ih_a : Eq KExpr a (KExpr.sort u) -> Eq KExpr a2 (KExpr.sort u)) (_ih_b : Eq KExpr b (KExpr.sort u) -> Eq KExpr b2 (KExpr.sort u)) (same : Eq KExpr (KExpr.let_ A a b) (KExpr.sort u)) => Empty.rec (fun (_bad : Empty) => Eq KExpr (instantiate b2 a2) (KExpr.sort u)) (kexpr_discr_t Empty (KExpr.let_ A a b) (KExpr.sort u) same (Eq.refl Bool Bool.false)))
  (fun (e e2 : KExpr) (run : iota_step (red_rec R) e e2) (same : Eq KExpr e (KExpr.sort u)) => iota_step_head_none_absurd (red_rec R) (KExpr.sort u) e2 (Eq KExpr e2 (KExpr.sort u)) (Eq.refl (OptionType Name) (OptionType.none Name)) (Eq.substType KExpr (fun (x : KExpr) => iota_step (red_rec R) x e2) e (KExpr.sort u) same run))
  (fun (e e2 : KExpr) (run : delta_step (red_def R) e e2) (same : Eq KExpr e (KExpr.sort u)) => delta_step_head_none_absurd (red_def R) (KExpr.sort u) e2 (Eq KExpr e2 (KExpr.sort u)) (Eq.refl (OptionType Name) (OptionType.none Name)) (Eq.substType KExpr (fun (x : KExpr) => delta_step (red_def R) x e2) e (KExpr.sort u) same run))
  (fun (A A2 a a2 b b2 : KExpr) (h_A : par_reduces_cdp R A A2) (h_a : par_reduces_cdp R a a2) (h_b : par_reduces_cdp R b b2) (_ih_A : Eq KExpr A (KExpr.sort u) -> Eq KExpr A2 (KExpr.sort u)) (_ih_a : Eq KExpr a (KExpr.sort u) -> Eq KExpr a2 (KExpr.sort u)) (_ih_b : Eq KExpr b (KExpr.sort u) -> Eq KExpr b2 (KExpr.sort u)) (same : Eq KExpr (KExpr.let_ A a b) (KExpr.sort u)) => Empty.rec (fun (_bad : Empty) => Eq KExpr (KExpr.let_ A2 a2 b2) (KExpr.sort u)) (kexpr_discr_t Empty (KExpr.let_ A a b) (KExpr.sort u) same (Eq.refl Bool Bool.false)))
  (fun (S : Name) (idx : Nat) (subject subject2 : KExpr) (h_subject : par_reduces_cdp R subject subject2) (_ih_subject : Eq KExpr subject (KExpr.sort u) -> Eq KExpr subject2 (KExpr.sort u)) (same : Eq KExpr (KExpr.proj S idx subject) (KExpr.sort u)) => Empty.rec (fun (_bad : Empty) => Eq KExpr (KExpr.proj S idx subject2) (KExpr.sort u)) (kexpr_discr_t Empty (KExpr.proj S idx subject) (KExpr.sort u) same (Eq.refl Bool Bool.false)))
  (fun (S : Name) (idx : Nat) (subject result : KExpr) (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject)) (OptionType.some KExpr result)) (same : Eq KExpr (KExpr.proj S idx subject) (KExpr.sort u)) => Empty.rec (fun (_bad : Empty) => Eq KExpr result (KExpr.sort u)) (kexpr_discr_t Empty (KExpr.proj S idx subject) (KExpr.sort u) same (Eq.refl Bool Bool.false)))
  (KExpr.sort u) out h (Eq.refl KExpr (KExpr.sort u))",
    ),
    DeclarationInput::Proof(
        "par_reduces_cdp_pi_inv_eq",
        r"forall (R : RedEnv) (dom body out : KExpr) (C : Type) (h : par_reduces_cdp R (KExpr.pi dom body) out) (consume : (forall (dom2 body2 : KExpr), Eq KExpr out (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C)), C",
        r"fun (R : RedEnv) (dom body out : KExpr) (C : Type) (h : par_reduces_cdp R (KExpr.pi dom body) out) (consume : (forall (dom2 body2 : KExpr), Eq KExpr out (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C)) => par_reduces_cdp.rec R (fun (e e2 : KExpr) (_h : par_reduces_cdp R e e2) => Eq KExpr e (KExpr.pi dom body) -> (forall (dom2 body2 : KExpr), Eq KExpr e2 (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C) -> C)
  (fun (e : KExpr) (same : Eq KExpr e (KExpr.pi dom body)) (next : (forall (dom2 body2 : KExpr), Eq KExpr e (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C)) => next dom body same (par_reduces_cdp.refl R dom) (par_reduces_cdp.refl R body))
  (fun (A A2 b b2 a a2 : KExpr) (h_A : par_reduces_cdp R A A2) (h_b : par_reduces_cdp R b b2) (h_a : par_reduces_cdp R a a2) (_ih_A : Eq KExpr A (KExpr.pi dom body) -> (forall (dom2 body2 : KExpr), Eq KExpr A2 (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C) -> C) (_ih_b : Eq KExpr b (KExpr.pi dom body) -> (forall (dom2 body2 : KExpr), Eq KExpr b2 (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C) -> C) (_ih_a : Eq KExpr a (KExpr.pi dom body) -> (forall (dom2 body2 : KExpr), Eq KExpr a2 (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C) -> C) (same : Eq KExpr (KExpr.app (KExpr.lam A b) a) (KExpr.pi dom body)) (next : (forall (dom2 body2 : KExpr), Eq KExpr (instantiate b2 a2) (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C)) => kexpr_discr_t C (KExpr.app (KExpr.lam A b) a) (KExpr.pi dom body) same (Eq.refl Bool Bool.false))
  (fun (f f2 a a2 : KExpr) (h_f : par_reduces_cdp R f f2) (h_a : par_reduces_cdp R a a2) (_ih_f : Eq KExpr f (KExpr.pi dom body) -> (forall (dom2 body2 : KExpr), Eq KExpr f2 (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C) -> C) (_ih_a : Eq KExpr a (KExpr.pi dom body) -> (forall (dom2 body2 : KExpr), Eq KExpr a2 (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C) -> C) (same : Eq KExpr (KExpr.app f a) (KExpr.pi dom body)) (next : (forall (dom2 body2 : KExpr), Eq KExpr (KExpr.app f2 a2) (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C)) => kexpr_discr_t C (KExpr.app f a) (KExpr.pi dom body) same (Eq.refl Bool Bool.false))
  (fun (A A2 b b2 : KExpr) (h_A : par_reduces_cdp R A A2) (h_b : par_reduces_cdp R b b2) (_ih_A : Eq KExpr A (KExpr.pi dom body) -> (forall (dom2 body2 : KExpr), Eq KExpr A2 (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C) -> C) (_ih_b : Eq KExpr b (KExpr.pi dom body) -> (forall (dom2 body2 : KExpr), Eq KExpr b2 (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C) -> C) (same : Eq KExpr (KExpr.lam A b) (KExpr.pi dom body)) (next : (forall (dom2 body2 : KExpr), Eq KExpr (KExpr.lam A2 b2) (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C)) => kexpr_discr_t C (KExpr.lam A b) (KExpr.pi dom body) same (Eq.refl Bool Bool.false))
  (fun (A A2 b b2 : KExpr) (h_A : par_reduces_cdp R A A2) (h_b : par_reduces_cdp R b b2) (_ih_A : Eq KExpr A (KExpr.pi dom body) -> (forall (dom2 body2 : KExpr), Eq KExpr A2 (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C) -> C) (_ih_b : Eq KExpr b (KExpr.pi dom body) -> (forall (dom2 body2 : KExpr), Eq KExpr b2 (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C) -> C) (same : Eq KExpr (KExpr.pi A b) (KExpr.pi dom body)) (next : (forall (dom2 body2 : KExpr), Eq KExpr (KExpr.pi A2 b2) (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C)) => next A2 b2 (Eq.refl KExpr (KExpr.pi A2 b2)) (Eq.substType KExpr (fun (x : KExpr) => par_reduces_cdp R x A2) A dom (pi_inj_fst A b dom body same) h_A) (Eq.substType KExpr (fun (x : KExpr) => par_reduces_cdp R x b2) b body (pi_inj_snd A b dom body same) h_b))
  (fun (A A2 b b2 : KExpr) (h_A : par_reduces_cdp R A A2) (h_b : par_reduces_cdp R b b2) (_ih_A : Eq KExpr A (KExpr.pi dom body) -> (forall (dom2 body2 : KExpr), Eq KExpr A2 (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C) -> C) (_ih_b : Eq KExpr b (KExpr.pi dom body) -> (forall (dom2 body2 : KExpr), Eq KExpr b2 (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C) -> C) (same : Eq KExpr (KExpr.forall_ A b) (KExpr.pi dom body)) (next : (forall (dom2 body2 : KExpr), Eq KExpr (KExpr.forall_ A2 b2) (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C)) => next A2 b2 (Eq.refl KExpr (KExpr.pi A2 b2)) (Eq.substType KExpr (fun (x : KExpr) => par_reduces_cdp R x A2) A dom (pi_inj_fst A b dom body same) h_A) (Eq.substType KExpr (fun (x : KExpr) => par_reduces_cdp R x b2) b body (pi_inj_snd A b dom body same) h_b))
  (fun (A A2 a a2 b b2 : KExpr) (h_A : par_reduces_cdp R A A2) (h_a : par_reduces_cdp R a a2) (h_b : par_reduces_cdp R b b2) (_ih_A : Eq KExpr A (KExpr.pi dom body) -> (forall (dom2 body2 : KExpr), Eq KExpr A2 (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C) -> C) (_ih_a : Eq KExpr a (KExpr.pi dom body) -> (forall (dom2 body2 : KExpr), Eq KExpr a2 (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C) -> C) (_ih_b : Eq KExpr b (KExpr.pi dom body) -> (forall (dom2 body2 : KExpr), Eq KExpr b2 (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C) -> C) (same : Eq KExpr (KExpr.let_ A a b) (KExpr.pi dom body)) (next : (forall (dom2 body2 : KExpr), Eq KExpr (instantiate b2 a2) (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C)) => kexpr_discr_t C (KExpr.let_ A a b) (KExpr.pi dom body) same (Eq.refl Bool Bool.false))
  (fun (e e2 : KExpr) (run : iota_step (red_rec R) e e2) (same : Eq KExpr e (KExpr.pi dom body)) (next : (forall (dom2 body2 : KExpr), Eq KExpr e2 (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C)) => iota_step_head_none_absurd_type (red_rec R) (KExpr.pi dom body) e2 C (Eq.refl (OptionType Name) (OptionType.none Name)) (Eq.substType KExpr (fun (x : KExpr) => iota_step (red_rec R) x e2) e (KExpr.pi dom body) same run))
  (fun (e e2 : KExpr) (run : delta_step (red_def R) e e2) (same : Eq KExpr e (KExpr.pi dom body)) (next : (forall (dom2 body2 : KExpr), Eq KExpr e2 (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C)) => delta_step_head_none_absurd_type (red_def R) (KExpr.pi dom body) e2 C (Eq.refl (OptionType Name) (OptionType.none Name)) (Eq.substType KExpr (fun (x : KExpr) => delta_step (red_def R) x e2) e (KExpr.pi dom body) same run))
  (fun (A A2 a a2 b b2 : KExpr) (h_A : par_reduces_cdp R A A2) (h_a : par_reduces_cdp R a a2) (h_b : par_reduces_cdp R b b2) (_ih_A : Eq KExpr A (KExpr.pi dom body) -> (forall (dom2 body2 : KExpr), Eq KExpr A2 (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C) -> C) (_ih_a : Eq KExpr a (KExpr.pi dom body) -> (forall (dom2 body2 : KExpr), Eq KExpr a2 (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C) -> C) (_ih_b : Eq KExpr b (KExpr.pi dom body) -> (forall (dom2 body2 : KExpr), Eq KExpr b2 (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C) -> C) (same : Eq KExpr (KExpr.let_ A a b) (KExpr.pi dom body)) (next : (forall (dom2 body2 : KExpr), Eq KExpr (KExpr.let_ A2 a2 b2) (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C)) => kexpr_discr_t C (KExpr.let_ A a b) (KExpr.pi dom body) same (Eq.refl Bool Bool.false))
  (fun (S : Name) (idx : Nat) (subject subject2 : KExpr) (h_subject : par_reduces_cdp R subject subject2) (_ih_subject : Eq KExpr subject (KExpr.pi dom body) -> (forall (dom2 body2 : KExpr), Eq KExpr subject2 (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C) -> C) (same : Eq KExpr (KExpr.proj S idx subject) (KExpr.pi dom body)) (next : (forall (dom2 body2 : KExpr), Eq KExpr (KExpr.proj S idx subject2) (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C)) => kexpr_discr_t C (KExpr.proj S idx subject) (KExpr.pi dom body) same (Eq.refl Bool Bool.false))
  (fun (S : Name) (idx : Nat) (subject result : KExpr) (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject)) (OptionType.some KExpr result)) (same : Eq KExpr (KExpr.proj S idx subject) (KExpr.pi dom body)) (next : (forall (dom2 body2 : KExpr), Eq KExpr result (KExpr.pi dom2 body2) -> par_reduces_cdp R dom dom2 -> par_reduces_cdp R body body2 -> C)) => kexpr_discr_t C (KExpr.proj S idx subject) (KExpr.pi dom body) same (Eq.refl Bool Bool.false))
  (KExpr.pi dom body) out h (Eq.refl KExpr (KExpr.pi dom body)) consume",
    ),
    DeclarationInput::Proof(
        "par_reduces_cdp_star_sort_inv_eq",
        r"forall (R : RedEnv) (u : Level) (out : KExpr)
 (h : par_reduces_cdp_star R (KExpr.sort u) out), Eq KExpr out (KExpr.sort u)",
        r"fun (R : RedEnv) (u : Level) (out : KExpr)
 (h : par_reduces_cdp_star R (KExpr.sort u) out) => par_reduces_cdp_star.rec R
  (fun (e e2 : KExpr) (_h : par_reduces_cdp_star R e e2) => Eq KExpr e (KExpr.sort u) -> Eq KExpr e2 (KExpr.sort u))
  (fun (e : KExpr) (same : Eq KExpr e (KExpr.sort u)) => same)
  (fun (e mid out : KExpr) (step : par_reduces_cdp R e mid) (_tail : par_reduces_cdp_star R mid out)
   (ih : Eq KExpr mid (KExpr.sort u) -> Eq KExpr out (KExpr.sort u)) (same : Eq KExpr e (KExpr.sort u)) =>
   ih (par_reduces_cdp_sort_inv_eq R u mid
    (Eq.substType KExpr (fun (x : KExpr) => par_reduces_cdp R x mid) e (KExpr.sort u) same step)))
  (KExpr.sort u) out h (Eq.refl KExpr (KExpr.sort u))",
    ),
    DeclarationInput::Proof(
        "par_reduces_cdp_star_pi_inv_eq",
        r"forall (R : RedEnv) (dom body out : KExpr) (C : Type)
 (h : par_reduces_cdp_star R (KExpr.pi dom body) out)
 (consume : forall (dom2 body2 : KExpr), Eq KExpr out (KExpr.pi dom2 body2) ->
  par_reduces_cdp_star R dom dom2 -> par_reduces_cdp_star R body body2 -> C), C",
        r"fun (R : RedEnv) (dom body out : KExpr) (C : Type)
 (h : par_reduces_cdp_star R (KExpr.pi dom body) out)
 (consume : forall (dom2 body2 : KExpr), Eq KExpr out (KExpr.pi dom2 body2) ->
  par_reduces_cdp_star R dom dom2 -> par_reduces_cdp_star R body body2 -> C) => par_reduces_cdp_star.rec R
  (fun (e e2 : KExpr) (_h : par_reduces_cdp_star R e e2) => forall (A B : KExpr), Eq KExpr e (KExpr.pi A B) ->
   (forall (A2 B2 : KExpr), Eq KExpr e2 (KExpr.pi A2 B2) -> par_reduces_cdp_star R A A2 -> par_reduces_cdp_star R B B2 -> C) -> C)
  (fun (e A B : KExpr) (same : Eq KExpr e (KExpr.pi A B))
   (next : forall (A2 B2 : KExpr), Eq KExpr e (KExpr.pi A2 B2) -> par_reduces_cdp_star R A A2 -> par_reduces_cdp_star R B B2 -> C) =>
   next A B same (par_reduces_cdp_star.refl R A) (par_reduces_cdp_star.refl R B))
  (fun (e mid out : KExpr) (step : par_reduces_cdp R e mid) (_tail : par_reduces_cdp_star R mid out)
   (ih : forall (A B : KExpr), Eq KExpr mid (KExpr.pi A B) ->
    (forall (A2 B2 : KExpr), Eq KExpr out (KExpr.pi A2 B2) -> par_reduces_cdp_star R A A2 -> par_reduces_cdp_star R B B2 -> C) -> C)
   (A B : KExpr) (same : Eq KExpr e (KExpr.pi A B))
   (next : forall (A2 B2 : KExpr), Eq KExpr out (KExpr.pi A2 B2) -> par_reduces_cdp_star R A A2 -> par_reduces_cdp_star R B B2 -> C) =>
   par_reduces_cdp_pi_inv_eq R A B mid C
    (Eq.substType KExpr (fun (x : KExpr) => par_reduces_cdp R x mid) e (KExpr.pi A B) same step)
    (fun (Am Bm : KExpr) (shape : Eq KExpr mid (KExpr.pi Am Bm)) (hA : par_reduces_cdp R A Am) (hB : par_reduces_cdp R B Bm) =>
     ih Am Bm shape
      (fun (A2 B2 : KExpr) (finalShape : Eq KExpr out (KExpr.pi A2 B2))
       (tailA : par_reduces_cdp_star R Am A2) (tailB : par_reduces_cdp_star R Bm B2) =>
       next A2 B2 finalShape (par_reduces_cdp_star.step R A Am A2 hA tailA) (par_reduces_cdp_star.step R B Bm B2 hB tailB))))
  (KExpr.pi dom body) out h dom body (Eq.refl KExpr (KExpr.pi dom body)) consume",
    ),
    DeclarationInput::Proof(
        "semantic_join_cdp_sort_injective",
        r"forall (R : RedEnv) (u : Level) (v : Level)
 (h : SemanticJoinCDP R (KExpr.sort u) (KExpr.sort v)), levelEqSem u v",
        r"fun (R : RedEnv) (u : Level) (v : Level)
 (h : SemanticJoinCDP R (KExpr.sort u) (KExpr.sort v)) => SemanticJoinCDP.rec R (KExpr.sort u) (KExpr.sort v)
  (fun (_h : SemanticJoinCDP R (KExpr.sort u) (KExpr.sort v)) => levelEqSem u v)
  (fun (x : KExpr) (y : KExpr)
    (ux : par_reduces_cdp_star R (KExpr.sort u) x)
    (vy : par_reduces_cdp_star R (KExpr.sort v) y) (xy : KExprUniverseEq x y) =>
    kexprUniverseEq_sort_injective u v
      (Eq.substType KExpr (fun (z : KExpr) => KExprUniverseEq (KExpr.sort u) z)
        y (KExpr.sort v) (par_reduces_cdp_star_sort_inv_eq R v y vy)
        (Eq.substType KExpr (fun (z : KExpr) => KExprUniverseEq z y)
          x (KExpr.sort u) (par_reduces_cdp_star_sort_inv_eq R u x ux) xy))) h",
    ),
    DeclarationInput::Proof(
        "semantic_join_cdp_pi_components",
        r"forall (R : RedEnv)
 (A : KExpr) (B : KExpr) (A2 : KExpr) (B2 : KExpr)
 (h : SemanticJoinCDP R (KExpr.pi A B) (KExpr.pi A2 B2))
 (C : Type) (consume : DefEqCDPIn R A A2 -> DefEqCDPIn R B B2 -> C), C",
        r"fun (R : RedEnv)
 (A : KExpr) (B : KExpr) (A2 : KExpr) (B2 : KExpr)
 (h : SemanticJoinCDP R (KExpr.pi A B) (KExpr.pi A2 B2))
 (C : Type) (consume : DefEqCDPIn R A A2 -> DefEqCDPIn R B B2 -> C) => SemanticJoinCDP.rec R (KExpr.pi A B) (KExpr.pi A2 B2)
  (fun (_h : SemanticJoinCDP R (KExpr.pi A B) (KExpr.pi A2 B2)) => C)
  (fun (x : KExpr) (y : KExpr)
    (left : par_reduces_cdp_star R (KExpr.pi A B) x)
    (right : par_reduces_cdp_star R (KExpr.pi A2 B2) y) (xy : KExprUniverseEq x y) =>
    par_reduces_cdp_star_pi_inv_eq R A B x C left
      (fun (Ax : KExpr) (Bx : KExpr) (hx : Eq KExpr x (KExpr.pi Ax Bx))
        (hAx : par_reduces_cdp_star R A Ax) (hBx : par_reduces_cdp_star R B Bx) =>
        par_reduces_cdp_star_pi_inv_eq R A2 B2 y C right
          (fun (Ay : KExpr) (By : KExpr) (hy : Eq KExpr y (KExpr.pi Ay By))
            (hAy : par_reduces_cdp_star R A2 Ay) (hBy : par_reduces_cdp_star R B2 By) =>
            kexprUniverseEq_pi_components Ax Bx Ay By
              (Eq.substType KExpr (fun (z : KExpr) => KExprUniverseEq (KExpr.pi Ax Bx) z)
                y (KExpr.pi Ay By) hy
                (Eq.substType KExpr (fun (z : KExpr) => KExprUniverseEq z y)
                  x (KExpr.pi Ax Bx) hx xy))
              C (fun (hA : KExprUniverseEq Ax Ay) (hB : KExprUniverseEq Bx By) =>
                consume
                  (semantic_join_cdp_to_def_eq_cdp_in R A A2 (SemanticJoinCDP.mk R A A2 Ax Ay hAx hAy hA))
                  (semantic_join_cdp_to_def_eq_cdp_in R B B2 (SemanticJoinCDP.mk R B B2 Bx By hBx hBy hB)))))) h",
    ),
    DeclarationInput::Proof(
        "semantic_join_cdp_pi_domain",
        r"forall (R : RedEnv)
 (A : KExpr) (B : KExpr) (A2 : KExpr) (B2 : KExpr)
 (h : SemanticJoinCDP R (KExpr.pi A B) (KExpr.pi A2 B2)), DefEqCDPIn R A A2",
        r"fun (R : RedEnv)
 (A : KExpr) (B : KExpr) (A2 : KExpr) (B2 : KExpr)
 (h : SemanticJoinCDP R (KExpr.pi A B) (KExpr.pi A2 B2)) => semantic_join_cdp_pi_components R A B A2 B2 h (DefEqCDPIn R A A2)
  (fun (hA : DefEqCDPIn R A A2) (hB : DefEqCDPIn R B B2) => hA)",
    ),
    DeclarationInput::Proof(
        "semantic_join_cdp_pi_codomain",
        r"forall (R : RedEnv)
 (A : KExpr) (B : KExpr) (A2 : KExpr) (B2 : KExpr)
 (h : SemanticJoinCDP R (KExpr.pi A B) (KExpr.pi A2 B2)), DefEqCDPIn R B B2",
        r"fun (R : RedEnv)
 (A : KExpr) (B : KExpr) (A2 : KExpr) (B2 : KExpr)
 (h : SemanticJoinCDP R (KExpr.pi A B) (KExpr.pi A2 B2)) => semantic_join_cdp_pi_components R A B A2 B2 h (DefEqCDPIn R B B2)
  (fun (hA : DefEqCDPIn R A A2) (hB : DefEqCDPIn R B B2) => hB)",
    ),
    DeclarationInput::Proof(
        "def_eq_cdp_in_sort_injective",
        r"forall (R : RedEnv) (hf : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (u : Level) (v : Level) (h : DefEqCDPIn R (KExpr.sort u) (KExpr.sort v)), levelEqSem u v",
        r"fun (R : RedEnv) (hf : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (u : Level) (v : Level) (h : DefEqCDPIn R (KExpr.sort u) (KExpr.sort v)) => semantic_join_cdp_sort_injective R u v
  (def_eq_cdp_in_to_semantic_join_cdp R hf rigid (KExpr.sort u) (KExpr.sort v) h)",
    ),
    DeclarationInput::Proof(
        "def_eq_cdp_in_pi_components",
        r"forall (R : RedEnv) (hf : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (A : KExpr) (B : KExpr) (A2 : KExpr) (B2 : KExpr)
 (h : DefEqCDPIn R (KExpr.pi A B) (KExpr.pi A2 B2))
 (C : Type) (consume : DefEqCDPIn R A A2 -> DefEqCDPIn R B B2 -> C), C",
        r"fun (R : RedEnv) (hf : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (A : KExpr) (B : KExpr) (A2 : KExpr) (B2 : KExpr)
 (h : DefEqCDPIn R (KExpr.pi A B) (KExpr.pi A2 B2))
 (C : Type) (consume : DefEqCDPIn R A A2 -> DefEqCDPIn R B B2 -> C) => semantic_join_cdp_pi_components R A B A2 B2
  (def_eq_cdp_in_to_semantic_join_cdp R hf rigid (KExpr.pi A B) (KExpr.pi A2 B2) h) C consume",
    ),
    DeclarationInput::Proof(
        "def_eq_cdp_in_pi_domain",
        r"forall (R : RedEnv) (hf : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (A : KExpr) (B : KExpr) (A2 : KExpr) (B2 : KExpr)
 (h : DefEqCDPIn R (KExpr.pi A B) (KExpr.pi A2 B2)), DefEqCDPIn R A A2",
        r"fun (R : RedEnv) (hf : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (A : KExpr) (B : KExpr) (A2 : KExpr) (B2 : KExpr)
 (h : DefEqCDPIn R (KExpr.pi A B) (KExpr.pi A2 B2)) => def_eq_cdp_in_pi_components R hf rigid A B A2 B2 h (DefEqCDPIn R A A2)
  (fun (hA : DefEqCDPIn R A A2) (hB : DefEqCDPIn R B B2) => hA)",
    ),
    DeclarationInput::Proof(
        "def_eq_cdp_in_pi_codomain",
        r"forall (R : RedEnv) (hf : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (A : KExpr) (B : KExpr) (A2 : KExpr) (B2 : KExpr)
 (h : DefEqCDPIn R (KExpr.pi A B) (KExpr.pi A2 B2)), DefEqCDPIn R B B2",
        r"fun (R : RedEnv) (hf : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (A : KExpr) (B : KExpr) (A2 : KExpr) (B2 : KExpr)
 (h : DefEqCDPIn R (KExpr.pi A B) (KExpr.pi A2 B2)) => def_eq_cdp_in_pi_components R hf rigid A B A2 B2 h (DefEqCDPIn R B B2)
  (fun (hA : DefEqCDPIn R A A2) (hB : DefEqCDPIn R B B2) => hB)",
    ),
    DeclarationInput::Proof(
        "cdp_sort_nonzero_step_rigid",
        r"forall (u : Level), Eq KExpr (KExpr.sort (Level.succ u)) (KExpr.sort (Level.succ u))",
        r"fun (u : Level) => par_reduces_cdp_sort_inv_eq the_red_env (Level.succ u) (KExpr.sort (Level.succ u))
  (par_reduces_cdp.refl the_red_env (KExpr.sort (Level.succ u)))",
    ),
    DeclarationInput::Proof(
        "cdp_sort_nonzero_star_rigid",
        r"forall (u : Level), Eq KExpr (KExpr.sort (Level.succ u)) (KExpr.sort (Level.succ u))",
        r"fun (u : Level) => par_reduces_cdp_star_sort_inv_eq the_red_env (Level.succ u) (KExpr.sort (Level.succ u))
  (par_reduces_cdp_star.step the_red_env (KExpr.sort (Level.succ u)) (KExpr.sort (Level.succ u)) (KExpr.sort (Level.succ u))
   (par_reduces_cdp.refl the_red_env (KExpr.sort (Level.succ u)))
   (par_reduces_cdp_star.refl the_red_env (KExpr.sort (Level.succ u))))",
    ),
    DeclarationInput::Proof(
        "cdp_sort_projection_roundtrip",
        r"forall (u : Level), DefEqCDPIn the_red_env (KExpr.sort (Level.succ (Level.imax u Level.zero))) (KExpr.sort (Level.succ Level.zero))",
        r"fun (u : Level) => DefEqCDPIn.trans the_red_env (KExpr.sort (Level.succ (Level.imax u Level.zero)))
  (cdp_universe_projection (Level.succ (Level.imax u Level.zero))) (KExpr.sort (Level.succ Level.zero))
  (DefEqCDPIn.symm the_red_env (cdp_universe_projection (Level.succ (Level.imax u Level.zero)))
   (KExpr.sort (Level.succ (Level.imax u Level.zero)))
   (DefEqCDPIn.raw the_red_env (cdp_universe_projection (Level.succ (Level.imax u Level.zero)))
    (KExpr.sort (Level.succ (Level.imax u Level.zero))) (cdp_universe_projection_step (Level.succ (Level.imax u Level.zero)))))
  (DefEqCDPIn.trans the_red_env (cdp_universe_projection (Level.succ (Level.imax u Level.zero)))
   (KExpr.sort (Level.succ (Level.imax u Level.zero))) (KExpr.sort (Level.succ Level.zero))
   (DefEqCDPIn.raw the_red_env (cdp_universe_projection (Level.succ (Level.imax u Level.zero)))
    (KExpr.sort (Level.succ (Level.imax u Level.zero))) (cdp_universe_projection_step (Level.succ (Level.imax u Level.zero))))
   (DefEqCDPIn.levels the_red_env (KExpr.sort (Level.succ (Level.imax u Level.zero))) (KExpr.sort (Level.succ Level.zero))
    (KExprUniverseEq.sort (Level.succ (Level.imax u Level.zero)) (Level.succ Level.zero) (cdp_universe_nonzero_levels u))))",
    ),
    DeclarationInput::Proof(
        "cdp_sort_projection_injective",
        r"forall (u : Level), levelEqSem (Level.succ (Level.imax u Level.zero)) (Level.succ Level.zero)",
        r"fun (u : Level) => def_eq_cdp_in_sort_injective the_red_env the_red_env_faithful reflected_ctor_metadata_rigid
  (Level.succ (Level.imax u Level.zero)) (Level.succ Level.zero) (cdp_sort_projection_roundtrip u)",
    ),
    DeclarationInput::Proof(
        "cdp_pi_projection_step",
        r"forall (u : Level), par_reduces_cdp the_red_env
  (KExpr.pi (cdp_universe_projection u) (cdp_universe_beta_source u)) (KExpr.pi (KExpr.sort u) (KExpr.sort u))",
        r"fun (u : Level) => par_reduces_cdp.pi the_red_env (cdp_universe_projection u) (KExpr.sort u)
  (cdp_universe_beta_source u) (KExpr.sort u) (cdp_universe_projection_step u) (cdp_universe_beta_parallel u)",
    ),
    DeclarationInput::Proof(
        "cdp_pi_projection_step_domain",
        r"forall (u : Level), par_reduces_cdp the_red_env (cdp_universe_projection u) (KExpr.sort u)",
        r"fun (u : Level) => par_reduces_cdp_pi_inv_eq the_red_env (cdp_universe_projection u) (cdp_universe_beta_source u)
  (KExpr.pi (KExpr.sort u) (KExpr.sort u)) (par_reduces_cdp the_red_env (cdp_universe_projection u) (KExpr.sort u))
  (cdp_pi_projection_step u)
  (fun (A B : KExpr) (shape : Eq KExpr (KExpr.pi (KExpr.sort u) (KExpr.sort u)) (KExpr.pi A B))
   (hA : par_reduces_cdp the_red_env (cdp_universe_projection u) A)
   (_hB : par_reduces_cdp the_red_env (cdp_universe_beta_source u) B) =>
   Eq.substType KExpr (fun (x : KExpr) => par_reduces_cdp the_red_env (cdp_universe_projection u) x)
    A (KExpr.sort u) (Eq.symm KExpr (KExpr.sort u) A (pi_inj_fst (KExpr.sort u) (KExpr.sort u) A B shape)) hA)",
    ),
    DeclarationInput::Proof(
        "cdp_pi_projection_star",
        r"forall (u : Level), par_reduces_cdp_star the_red_env
  (KExpr.pi (cdp_universe_projection u) (cdp_universe_beta_source u)) (KExpr.pi (KExpr.sort u) (KExpr.sort u))",
        r"fun (u : Level) => par_reduces_cdp_star_pi the_red_env (cdp_universe_projection u) (KExpr.sort u)
  (cdp_universe_beta_source u) (KExpr.sort u)
  (par_reduces_cdp_star.step the_red_env (cdp_universe_projection u) (KExpr.sort u) (KExpr.sort u)
   (cdp_universe_projection_step u) (par_reduces_cdp_star.refl the_red_env (KExpr.sort u)))
  (cdp_universe_beta_star u)",
    ),
    DeclarationInput::Proof(
        "cdp_pi_projection_star_components",
        r"forall (u : Level) (C : Type)
 (consume : par_reduces_cdp_star the_red_env (cdp_universe_projection u) (KExpr.sort u) ->
  par_reduces_cdp_star the_red_env (cdp_universe_beta_source u) (KExpr.sort u) -> C), C",
        r"fun (u : Level) (C : Type)
 (consume : par_reduces_cdp_star the_red_env (cdp_universe_projection u) (KExpr.sort u) ->
  par_reduces_cdp_star the_red_env (cdp_universe_beta_source u) (KExpr.sort u) -> C) => par_reduces_cdp_star_pi_inv_eq the_red_env (cdp_universe_projection u) (cdp_universe_beta_source u)
  (KExpr.pi (KExpr.sort u) (KExpr.sort u)) C (cdp_pi_projection_star u)
  (fun (A B : KExpr) (shape : Eq KExpr (KExpr.pi (KExpr.sort u) (KExpr.sort u)) (KExpr.pi A B))
   (hA : par_reduces_cdp_star the_red_env (cdp_universe_projection u) A)
   (hB : par_reduces_cdp_star the_red_env (cdp_universe_beta_source u) B) =>
   consume
    (Eq.substType KExpr (fun (x : KExpr) => par_reduces_cdp_star the_red_env (cdp_universe_projection u) x)
     A (KExpr.sort u) (Eq.symm KExpr (KExpr.sort u) A (pi_inj_fst (KExpr.sort u) (KExpr.sort u) A B shape)) hA)
    (Eq.substType KExpr (fun (x : KExpr) => par_reduces_cdp_star the_red_env (cdp_universe_beta_source u) x)
     B (KExpr.sort u) (Eq.symm KExpr (KExpr.sort u) B (pi_inj_snd (KExpr.sort u) (KExpr.sort u) A B shape)) hB))",
    ),
    DeclarationInput::Proof(
        "cdp_pi_projection_nonzero_join",
        r"forall (u : Level), SemanticJoinCDP the_red_env
  (KExpr.pi (cdp_universe_projection (Level.succ (Level.imax u Level.zero))) (cdp_universe_beta_source (Level.succ (Level.imax u Level.zero))))
  (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ Level.zero)))",
        r"fun (u : Level) => SemanticJoinCDP.mk the_red_env
  (KExpr.pi (cdp_universe_projection (Level.succ (Level.imax u Level.zero))) (cdp_universe_beta_source (Level.succ (Level.imax u Level.zero))))
  (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ Level.zero)))
  (KExpr.pi (KExpr.sort (Level.succ (Level.imax u Level.zero))) (KExpr.sort (Level.succ (Level.imax u Level.zero))))
  (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ Level.zero)))
  (cdp_pi_projection_star (Level.succ (Level.imax u Level.zero)))
  (par_reduces_cdp_star.refl the_red_env (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ Level.zero))))
  (KExprUniverseEq.pi (KExpr.sort (Level.succ (Level.imax u Level.zero))) (KExpr.sort (Level.succ Level.zero))
   (KExpr.sort (Level.succ (Level.imax u Level.zero))) (KExpr.sort (Level.succ Level.zero))
   (KExprUniverseEq.sort (Level.succ (Level.imax u Level.zero)) (Level.succ Level.zero) (cdp_universe_nonzero_levels u))
   (KExprUniverseEq.sort (Level.succ (Level.imax u Level.zero)) (Level.succ Level.zero) (cdp_universe_nonzero_levels u)))",
    ),
    DeclarationInput::Proof(
        "cdp_pi_projection_nonzero_domain",
        r"forall (u : Level), DefEqCDPIn the_red_env (cdp_universe_projection (Level.succ (Level.imax u Level.zero))) (KExpr.sort (Level.succ Level.zero))",
        r"fun (u : Level) => def_eq_cdp_in_pi_domain the_red_env the_red_env_faithful reflected_ctor_metadata_rigid
  (cdp_universe_projection (Level.succ (Level.imax u Level.zero))) (cdp_universe_beta_source (Level.succ (Level.imax u Level.zero)))
  (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ Level.zero))
  (semantic_join_cdp_to_def_eq_cdp_in the_red_env
   (KExpr.pi (cdp_universe_projection (Level.succ (Level.imax u Level.zero))) (cdp_universe_beta_source (Level.succ (Level.imax u Level.zero))))
   (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ Level.zero))) (cdp_pi_projection_nonzero_join u))",
    ),
    DeclarationInput::Proof(
        "cdp_pi_projection_nonzero_codomain",
        r"forall (u : Level), DefEqCDPIn the_red_env (cdp_universe_beta_source (Level.succ (Level.imax u Level.zero))) (KExpr.sort (Level.succ Level.zero))",
        r"fun (u : Level) => def_eq_cdp_in_pi_codomain the_red_env the_red_env_faithful reflected_ctor_metadata_rigid
  (cdp_universe_projection (Level.succ (Level.imax u Level.zero))) (cdp_universe_beta_source (Level.succ (Level.imax u Level.zero)))
  (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ Level.zero))
  (semantic_join_cdp_to_def_eq_cdp_in the_red_env
   (KExpr.pi (cdp_universe_projection (Level.succ (Level.imax u Level.zero))) (cdp_universe_beta_source (Level.succ (Level.imax u Level.zero))))
   (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ Level.zero))) (cdp_pi_projection_nonzero_join u))",
    ),
    DeclarationInput::Proof(
        "semantic_join_cdp_sort_zero_succ_absurd",
        r"forall (R : RedEnv) (u : Level)
 (h : SemanticJoinCDP R (KExpr.sort Level.zero) (KExpr.sort (Level.succ u))), Empty",
        r"fun (R : RedEnv) (u : Level)
 (h : SemanticJoinCDP R (KExpr.sort Level.zero) (KExpr.sort (Level.succ u))) => nat_zero_ne_succ (evalL (fun (_ : Name) => Nat.zero) u) Empty
  ((semantic_join_cdp_sort_injective R Level.zero (Level.succ u) h) (fun (_ : Name) => Nat.zero))",
    ),
    DeclarationInput::Proof(
        "def_eq_cdp_in_sort_zero_succ_absurd",
        r"forall (R : RedEnv) (hf : RedEnvFaithful R)
 (rigid : CtorMetadataRigid R (red_ind_ctor R)) (u : Level)
 (h : DefEqCDPIn R (KExpr.sort Level.zero) (KExpr.sort (Level.succ u))), Empty",
        r"fun (R : RedEnv) (hf : RedEnvFaithful R)
 (rigid : CtorMetadataRigid R (red_ind_ctor R)) (u : Level)
 (h : DefEqCDPIn R (KExpr.sort Level.zero) (KExpr.sort (Level.succ u))) => semantic_join_cdp_sort_zero_succ_absurd R u
  (def_eq_cdp_in_to_semantic_join_cdp R hf rigid (KExpr.sort Level.zero) (KExpr.sort (Level.succ u)) h)",
    ),
    DeclarationInput::Proof(
        "def_eq_cdp_in_pi_zero_succ_domain_absurd",
        r"forall (R : RedEnv) (hf : RedEnvFaithful R)
 (rigid : CtorMetadataRigid R (red_ind_ctor R)) (u : Level) (B B2 : KExpr)
 (h : DefEqCDPIn R (KExpr.pi (KExpr.sort Level.zero) B) (KExpr.pi (KExpr.sort (Level.succ u)) B2)), Empty",
        r"fun (R : RedEnv) (hf : RedEnvFaithful R)
 (rigid : CtorMetadataRigid R (red_ind_ctor R)) (u : Level) (B B2 : KExpr)
 (h : DefEqCDPIn R (KExpr.pi (KExpr.sort Level.zero) B) (KExpr.pi (KExpr.sort (Level.succ u)) B2)) => def_eq_cdp_in_sort_zero_succ_absurd R hf rigid u
  (def_eq_cdp_in_pi_domain R hf rigid (KExpr.sort Level.zero) B (KExpr.sort (Level.succ u)) B2 h)",
    ),
];
#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "forged_cdp_sort_wrong_level",
        r"levelEqSem Level.zero (Level.succ Level.zero)",
        r"cdp_sort_projection_injective (Level.param Name.anonymous)",
    ),
    (
        "forged_cdp_pi_wrong_domain",
        r"DefEqCDPIn the_red_env (cdp_universe_projection (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero))) (KExpr.sort Level.zero)",
        r"cdp_pi_projection_nonzero_domain (Level.param Name.anonymous)",
    ),
    (
        "forged_cdp_sort_raw_level_equality",
        r"Eq Level (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)) (Level.succ Level.zero)",
        r"Eq.refl Level (Level.succ Level.zero)",
    ),
    (
        "forged_cdp_pi_wrong_component_step",
        r"par_reduces_cdp the_red_env (cdp_universe_projection (Level.succ Level.zero)) (KExpr.sort Level.zero)",
        r"cdp_pi_projection_step_domain (Level.succ Level.zero)",
    ),
];
#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "par_reduces_cdp_sort_inv_eq",
    "par_reduces_cdp_pi_inv_eq",
    "par_reduces_cdp_star_sort_inv_eq",
    "par_reduces_cdp_star_pi_inv_eq",
    "semantic_join_cdp_sort_injective",
    "semantic_join_cdp_pi_components",
    "semantic_join_cdp_pi_domain",
    "semantic_join_cdp_pi_codomain",
    "def_eq_cdp_in_sort_injective",
    "def_eq_cdp_in_pi_components",
    "def_eq_cdp_in_pi_domain",
    "def_eq_cdp_in_pi_codomain",
    "cdp_sort_nonzero_step_rigid",
    "cdp_sort_nonzero_star_rigid",
    "cdp_sort_projection_roundtrip",
    "cdp_sort_projection_injective",
    "cdp_pi_projection_step",
    "cdp_pi_projection_step_domain",
    "cdp_pi_projection_star",
    "cdp_pi_projection_star_components",
    "cdp_pi_projection_nonzero_join",
    "cdp_pi_projection_nonzero_domain",
    "cdp_pi_projection_nonzero_codomain",
    "semantic_join_cdp_sort_zero_succ_absurd",
    "def_eq_cdp_in_sort_zero_succ_absurd",
    "def_eq_cdp_in_pi_zero_succ_domain_absurd",
];
#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[];
#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &[];
