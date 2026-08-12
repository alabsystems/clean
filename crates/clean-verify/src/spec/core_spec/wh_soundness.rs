// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The faithful loop is SOUND for `DefEq`.
//!
//! ```text
//! reduce_app_head_wh_defeq : the application dispatch's step is DefEq
//! reduce_once_red_wh_defeq : one step of the faithful loop is DefEq
//! whnf_fuel_red_wh_defeq   : and so is the whole loop
//! ```
//!
//! # Why `DefEq` and not `whnf_red_conv`
//!
//! The mirror of `whnf_fuel_red_conv` is not merely unproved, it is **unstatable**:
//! `whnf_red_step` has congruence arms for `app_left` and `proj` and **no
//! `app_right`**, so it cannot relate terms differing inside an *argument* — and a
//! recursor's major premise is an argument, which is exactly what the pre-pass
//! reduces. `DefEq` has `app_cong`, so it can.
//!
//! # The ι case is a hypothesis, deliberately
//!
//! `hiota` is carried as a blanket hypothesis over every `wh`, rather than
//! discharged. Discharging it *inside* the loop's induction would need the loop's
//! own soundness at lower fuel — a mutual recursion better made explicit than
//! hidden inside a proof term. It is a hypothesis and never an axiom, and
//! `whc_fires_plain_minimal` + `defeq_of_prepass_iota` discharge it for minimally
//! fully-applied spines.
//!
//! # What each layer costs
//!
//! The application dispatch is the only large term: nine arms over the head shape,
//! of which `lam` fires β and the other eight share **one** convoy — case on
//! whether the head itself steps, then either hand the pre-pass ι to `hiota` or
//! rebuild with `app_cong`. Generating eight arms from one template is the same
//! collapse that has worked throughout this program.
//!
//! The middle layer is pure assembly: five arms are dead because the step returns
//! `none`, `const` and `let_` are the two small bricks proved earlier, `proj` is a
//! convoy into `proj_cong`, and `app` delegates. The loop is the standard fuel
//! induction — `refl` when the step finds nothing, `trans` when it steps.
//!
//! `DerivedProved` throughout, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const T: &str = "the_red_env";

/// The blanket ι hypothesis.
fn hiota_ty() -> String {
    format!(
        "forall (w : KExpr -> OptionType KExpr) (g : KExpr) (x : KExpr) (r : KExpr), \
         Eq (OptionType KExpr) (iota_reduct_whc (red_rec {T}) w (KExpr.app g x)) \
         (OptionType.some KExpr r) -> DefEq (KExpr.app g x) r"
    )
}

/// `KExpr`'s nine constructors: (payload binders, recursive field names, applied form).
const SHAPES: [(&str, &[&str], &str); 9] = [
    ("(n : Level) ", &[], "(KExpr.sort n)"),
    ("(i : Nat) ", &[], "(KExpr.bvar i)"),
    (
        "(f : KExpr) (a2 : KExpr) ",
        &["f", "a2"],
        "(KExpr.app f a2)",
    ),
    (
        "(ty : KExpr) (b : KExpr) ",
        &["ty", "b"],
        "(KExpr.lam ty b)",
    ),
    ("(ty : KExpr) (b : KExpr) ", &["ty", "b"], "(KExpr.pi ty b)"),
    (
        "(n : Name) (us : ListType Level) ",
        &[],
        "(KExpr.const n us)",
    ),
    (
        "(ty : KExpr) (v : KExpr) (b : KExpr) ",
        &["ty", "v", "b"],
        "(KExpr.let_ ty v b)",
    ),
    (
        "(s : Name) (i : Nat) (sub : KExpr) ",
        &["sub"],
        "(KExpr.proj s i sub)",
    ),
    ("(v : Nat) ", &[], "(KExpr.lit v)"),
];

const CONST_DELTA_STEP: &str = "def const_delta_step (n : Name) (us : ListType Level) (v : KExpr) (h : Eq (OptionType KExpr) (defval_for (red_def the_red_env) n) (OptionType.some KExpr v)) : delta_step (red_def the_red_env) (KExpr.const n us) v := opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn (KExpr.const n us))) (fun (dname : Name) => opt_bind KExpr KExpr (defval_for (red_def the_red_env) dname) (fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args (KExpr.const n us)) val))) n v (Eq.refl (OptionType Name) (OptionType.some Name n)) (opt_bind_some_intro KExpr KExpr (defval_for (red_def the_red_env) n) (fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args (KExpr.const n us)) val)) v v h (Eq.refl (OptionType KExpr) (OptionType.some KExpr v)))";

const APP_HEAD_PAR: &str = "def reduce_app_head_wh_par (wh : KExpr -> OptionType KExpr) (hiota : forall (w : KExpr -> OptionType KExpr) (g : KExpr) (x : KExpr) (r : KExpr), Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) w (KExpr.app g x)) (OptionType.some KExpr r) -> par_reduces_cd_star the_red_env (KExpr.app g x) r) (a : KExpr) (f : KExpr) : (forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh f) (OptionType.some KExpr y) -> par_reduces_cd_star the_red_env f y) -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh a f (reduce_once_red_wh the_red_env wh f)) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env (KExpr.app f a) e2 := KExpr.rec (fun (x : KExpr) => (forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh x) (OptionType.some KExpr y) -> par_reduces_cd_star the_red_env x y) -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh a x (reduce_once_red_wh the_red_env wh x)) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env (KExpr.app x a) e2) (fun (n : Level) (ihf : forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.sort n)) (OptionType.some KExpr y) -> par_reduces_cd_star the_red_env (KExpr.sort n) y) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh a (KExpr.sort n) (reduce_once_red_wh the_red_env wh (KExpr.sort n))) (OptionType.some KExpr e2)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.sort n)) o -> Eq (OptionType KExpr) (opt_app_ilift_wh the_red_env wh (KExpr.sort n) a o) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env (KExpr.app (KExpr.sort n) a) e2) (fun (_hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.sort n)) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh (KExpr.app (KExpr.sort n) a)) (OptionType.some KExpr e2)) => hiota wh (KExpr.sort n) a e2 h2) (fun (f2 : KExpr) (hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.sort n)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (OptionType.some KExpr (KExpr.app f2 a)) (OptionType.some KExpr e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star the_red_env (KExpr.app (KExpr.sort n) a) X) (KExpr.app f2 a) e2 (option_some_inj KExpr (KExpr.app f2 a) e2 h2) (par_reduces_cd_star_app the_red_env (KExpr.sort n) f2 a a (ihf f2 hq) (par_reduces_cd_star.refl the_red_env a))) (reduce_once_red_wh the_red_env wh (KExpr.sort n)) (Eq.refl (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.sort n))) h) (fun (i : Nat) (ihf : forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.bvar i)) (OptionType.some KExpr y) -> par_reduces_cd_star the_red_env (KExpr.bvar i) y) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh a (KExpr.bvar i) (reduce_once_red_wh the_red_env wh (KExpr.bvar i))) (OptionType.some KExpr e2)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.bvar i)) o -> Eq (OptionType KExpr) (opt_app_ilift_wh the_red_env wh (KExpr.bvar i) a o) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env (KExpr.app (KExpr.bvar i) a) e2) (fun (_hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.bvar i)) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh (KExpr.app (KExpr.bvar i) a)) (OptionType.some KExpr e2)) => hiota wh (KExpr.bvar i) a e2 h2) (fun (f2 : KExpr) (hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.bvar i)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (OptionType.some KExpr (KExpr.app f2 a)) (OptionType.some KExpr e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star the_red_env (KExpr.app (KExpr.bvar i) a) X) (KExpr.app f2 a) e2 (option_some_inj KExpr (KExpr.app f2 a) e2 h2) (par_reduces_cd_star_app the_red_env (KExpr.bvar i) f2 a a (ihf f2 hq) (par_reduces_cd_star.refl the_red_env a))) (reduce_once_red_wh the_red_env wh (KExpr.bvar i)) (Eq.refl (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.bvar i))) h) (fun (f : KExpr) (a2 : KExpr) (_c0 : ((forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh f) (OptionType.some KExpr y) -> par_reduces_cd_star the_red_env f y) -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh a f (reduce_once_red_wh the_red_env wh f)) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env (KExpr.app f a) e2)) (_c1 : ((forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh a2) (OptionType.some KExpr y) -> par_reduces_cd_star the_red_env a2 y) -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh a a2 (reduce_once_red_wh the_red_env wh a2)) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env (KExpr.app a2 a) e2)) (ihf : forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.app f a2)) (OptionType.some KExpr y) -> par_reduces_cd_star the_red_env (KExpr.app f a2) y) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh a (KExpr.app f a2) (reduce_once_red_wh the_red_env wh (KExpr.app f a2))) (OptionType.some KExpr e2)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.app f a2)) o -> Eq (OptionType KExpr) (opt_app_ilift_wh the_red_env wh (KExpr.app f a2) a o) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env (KExpr.app (KExpr.app f a2) a) e2) (fun (_hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.app f a2)) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh (KExpr.app (KExpr.app f a2) a)) (OptionType.some KExpr e2)) => hiota wh (KExpr.app f a2) a e2 h2) (fun (f2 : KExpr) (hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.app f a2)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (OptionType.some KExpr (KExpr.app f2 a)) (OptionType.some KExpr e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star the_red_env (KExpr.app (KExpr.app f a2) a) X) (KExpr.app f2 a) e2 (option_some_inj KExpr (KExpr.app f2 a) e2 h2) (par_reduces_cd_star_app the_red_env (KExpr.app f a2) f2 a a (ihf f2 hq) (par_reduces_cd_star.refl the_red_env a))) (reduce_once_red_wh the_red_env wh (KExpr.app f a2)) (Eq.refl (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.app f a2))) h) (fun (ty : KExpr) (b : KExpr) (_c0 : ((forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh ty) (OptionType.some KExpr y) -> par_reduces_cd_star the_red_env ty y) -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh a ty (reduce_once_red_wh the_red_env wh ty)) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env (KExpr.app ty a) e2)) (_c1 : ((forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh b) (OptionType.some KExpr y) -> par_reduces_cd_star the_red_env b y) -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh a b (reduce_once_red_wh the_red_env wh b)) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env (KExpr.app b a) e2)) (ihf : forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.lam ty b)) (OptionType.some KExpr y) -> par_reduces_cd_star the_red_env (KExpr.lam ty b) y) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh a (KExpr.lam ty b) (reduce_once_red_wh the_red_env wh (KExpr.lam ty b))) (OptionType.some KExpr e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star the_red_env (KExpr.app (KExpr.lam ty b) a) X) (instantiate b a) e2 (option_some_inj KExpr (instantiate b a) e2 h) (par_reduces_cd_star.step the_red_env (KExpr.app (KExpr.lam ty b) a) (instantiate b a) (instantiate b a) (par_reduces_cd.beta the_red_env ty ty b b a a (par_reduces_cd.refl the_red_env ty) (par_reduces_cd.refl the_red_env b) (par_reduces_cd.refl the_red_env a)) (par_reduces_cd_star.refl the_red_env (instantiate b a)))) (fun (ty : KExpr) (b : KExpr) (_c0 : ((forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh ty) (OptionType.some KExpr y) -> par_reduces_cd_star the_red_env ty y) -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh a ty (reduce_once_red_wh the_red_env wh ty)) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env (KExpr.app ty a) e2)) (_c1 : ((forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh b) (OptionType.some KExpr y) -> par_reduces_cd_star the_red_env b y) -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh a b (reduce_once_red_wh the_red_env wh b)) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env (KExpr.app b a) e2)) (ihf : forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.pi ty b)) (OptionType.some KExpr y) -> par_reduces_cd_star the_red_env (KExpr.pi ty b) y) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh a (KExpr.pi ty b) (reduce_once_red_wh the_red_env wh (KExpr.pi ty b))) (OptionType.some KExpr e2)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.pi ty b)) o -> Eq (OptionType KExpr) (opt_app_ilift_wh the_red_env wh (KExpr.pi ty b) a o) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env (KExpr.app (KExpr.pi ty b) a) e2) (fun (_hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.pi ty b)) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh (KExpr.app (KExpr.pi ty b) a)) (OptionType.some KExpr e2)) => hiota wh (KExpr.pi ty b) a e2 h2) (fun (f2 : KExpr) (hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.pi ty b)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (OptionType.some KExpr (KExpr.app f2 a)) (OptionType.some KExpr e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star the_red_env (KExpr.app (KExpr.pi ty b) a) X) (KExpr.app f2 a) e2 (option_some_inj KExpr (KExpr.app f2 a) e2 h2) (par_reduces_cd_star_app the_red_env (KExpr.pi ty b) f2 a a (ihf f2 hq) (par_reduces_cd_star.refl the_red_env a))) (reduce_once_red_wh the_red_env wh (KExpr.pi ty b)) (Eq.refl (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.pi ty b))) h) (fun (n : Name) (us : ListType Level) (ihf : forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.const n us)) (OptionType.some KExpr y) -> par_reduces_cd_star the_red_env (KExpr.const n us) y) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh a (KExpr.const n us) (reduce_once_red_wh the_red_env wh (KExpr.const n us))) (OptionType.some KExpr e2)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.const n us)) o -> Eq (OptionType KExpr) (opt_app_ilift_wh the_red_env wh (KExpr.const n us) a o) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env (KExpr.app (KExpr.const n us) a) e2) (fun (_hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.const n us)) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh (KExpr.app (KExpr.const n us) a)) (OptionType.some KExpr e2)) => hiota wh (KExpr.const n us) a e2 h2) (fun (f2 : KExpr) (hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.const n us)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (OptionType.some KExpr (KExpr.app f2 a)) (OptionType.some KExpr e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star the_red_env (KExpr.app (KExpr.const n us) a) X) (KExpr.app f2 a) e2 (option_some_inj KExpr (KExpr.app f2 a) e2 h2) (par_reduces_cd_star_app the_red_env (KExpr.const n us) f2 a a (ihf f2 hq) (par_reduces_cd_star.refl the_red_env a))) (reduce_once_red_wh the_red_env wh (KExpr.const n us)) (Eq.refl (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.const n us))) h) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_c0 : ((forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh ty) (OptionType.some KExpr y) -> par_reduces_cd_star the_red_env ty y) -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh a ty (reduce_once_red_wh the_red_env wh ty)) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env (KExpr.app ty a) e2)) (_c1 : ((forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh v) (OptionType.some KExpr y) -> par_reduces_cd_star the_red_env v y) -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh a v (reduce_once_red_wh the_red_env wh v)) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env (KExpr.app v a) e2)) (_c2 : ((forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh b) (OptionType.some KExpr y) -> par_reduces_cd_star the_red_env b y) -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh a b (reduce_once_red_wh the_red_env wh b)) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env (KExpr.app b a) e2)) (ihf : forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.let_ ty v b)) (OptionType.some KExpr y) -> par_reduces_cd_star the_red_env (KExpr.let_ ty v b) y) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh a (KExpr.let_ ty v b) (reduce_once_red_wh the_red_env wh (KExpr.let_ ty v b))) (OptionType.some KExpr e2)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.let_ ty v b)) o -> Eq (OptionType KExpr) (opt_app_ilift_wh the_red_env wh (KExpr.let_ ty v b) a o) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env (KExpr.app (KExpr.let_ ty v b) a) e2) (fun (_hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.let_ ty v b)) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh (KExpr.app (KExpr.let_ ty v b) a)) (OptionType.some KExpr e2)) => hiota wh (KExpr.let_ ty v b) a e2 h2) (fun (f2 : KExpr) (hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.let_ ty v b)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (OptionType.some KExpr (KExpr.app f2 a)) (OptionType.some KExpr e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star the_red_env (KExpr.app (KExpr.let_ ty v b) a) X) (KExpr.app f2 a) e2 (option_some_inj KExpr (KExpr.app f2 a) e2 h2) (par_reduces_cd_star_app the_red_env (KExpr.let_ ty v b) f2 a a (ihf f2 hq) (par_reduces_cd_star.refl the_red_env a))) (reduce_once_red_wh the_red_env wh (KExpr.let_ ty v b)) (Eq.refl (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.let_ ty v b))) h) (fun (s : Name) (i : Nat) (sub : KExpr) (_c0 : ((forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh sub) (OptionType.some KExpr y) -> par_reduces_cd_star the_red_env sub y) -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh a sub (reduce_once_red_wh the_red_env wh sub)) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env (KExpr.app sub a) e2)) (ihf : forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.proj s i sub)) (OptionType.some KExpr y) -> par_reduces_cd_star the_red_env (KExpr.proj s i sub) y) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh a (KExpr.proj s i sub) (reduce_once_red_wh the_red_env wh (KExpr.proj s i sub))) (OptionType.some KExpr e2)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.proj s i sub)) o -> Eq (OptionType KExpr) (opt_app_ilift_wh the_red_env wh (KExpr.proj s i sub) a o) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env (KExpr.app (KExpr.proj s i sub) a) e2) (fun (_hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.proj s i sub)) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh (KExpr.app (KExpr.proj s i sub) a)) (OptionType.some KExpr e2)) => hiota wh (KExpr.proj s i sub) a e2 h2) (fun (f2 : KExpr) (hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.proj s i sub)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (OptionType.some KExpr (KExpr.app f2 a)) (OptionType.some KExpr e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star the_red_env (KExpr.app (KExpr.proj s i sub) a) X) (KExpr.app f2 a) e2 (option_some_inj KExpr (KExpr.app f2 a) e2 h2) (par_reduces_cd_star_app the_red_env (KExpr.proj s i sub) f2 a a (ihf f2 hq) (par_reduces_cd_star.refl the_red_env a))) (reduce_once_red_wh the_red_env wh (KExpr.proj s i sub)) (Eq.refl (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.proj s i sub))) h) (fun (v : Nat) (ihf : forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.lit v)) (OptionType.some KExpr y) -> par_reduces_cd_star the_red_env (KExpr.lit v) y) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh a (KExpr.lit v) (reduce_once_red_wh the_red_env wh (KExpr.lit v))) (OptionType.some KExpr e2)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.lit v)) o -> Eq (OptionType KExpr) (opt_app_ilift_wh the_red_env wh (KExpr.lit v) a o) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env (KExpr.app (KExpr.lit v) a) e2) (fun (_hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.lit v)) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh (KExpr.app (KExpr.lit v) a)) (OptionType.some KExpr e2)) => hiota wh (KExpr.lit v) a e2 h2) (fun (f2 : KExpr) (hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.lit v)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (OptionType.some KExpr (KExpr.app f2 a)) (OptionType.some KExpr e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star the_red_env (KExpr.app (KExpr.lit v) a) X) (KExpr.app f2 a) e2 (option_some_inj KExpr (KExpr.app f2 a) e2 h2) (par_reduces_cd_star_app the_red_env (KExpr.lit v) f2 a a (ihf f2 hq) (par_reduces_cd_star.refl the_red_env a))) (reduce_once_red_wh the_red_env wh (KExpr.lit v)) (Eq.refl (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.lit v))) h) f";

const STEP_PAR: &str = "def reduce_once_red_wh_par (wh : KExpr -> OptionType KExpr) (hiota : forall (w : KExpr -> OptionType KExpr) (g : KExpr) (x : KExpr) (r : KExpr), Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) w (KExpr.app g x)) (OptionType.some KExpr r) -> par_reduces_cd_star the_red_env (KExpr.app g x) r) (e : KExpr) : forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh e) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env e e2 := KExpr.rec (fun (x : KExpr) => forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh x) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env x e2) (fun (n : Level) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.sort n)) (OptionType.some KExpr e2)) => option_none_ne_some_type KExpr e2 (par_reduces_cd_star the_red_env (KExpr.sort n) e2) h) (fun (i : Nat) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.bvar i)) (OptionType.some KExpr e2)) => option_none_ne_some_type KExpr e2 (par_reduces_cd_star the_red_env (KExpr.bvar i) e2) h) (fun (f : KExpr) (a2 : KExpr) (_c0 : forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh f) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env f e2) (_c1 : forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh a2) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env a2 e2) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.app f a2)) (OptionType.some KExpr e2)) => reduce_app_head_wh_par wh hiota a2 f _c0 e2 h) (fun (ty : KExpr) (b : KExpr) (_c0 : forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh ty) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env ty e2) (_c1 : forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh b) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env b e2) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.lam ty b)) (OptionType.some KExpr e2)) => option_none_ne_some_type KExpr e2 (par_reduces_cd_star the_red_env (KExpr.lam ty b) e2) h) (fun (ty : KExpr) (b : KExpr) (_c0 : forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh ty) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env ty e2) (_c1 : forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh b) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env b e2) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.pi ty b)) (OptionType.some KExpr e2)) => option_none_ne_some_type KExpr e2 (par_reduces_cd_star the_red_env (KExpr.pi ty b) e2) h) (fun (n : Name) (us : ListType Level) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.const n us)) (OptionType.some KExpr e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star the_red_env (KExpr.const n us) X) e2 e2 (Eq.refl KExpr e2) (par_reduces_cd_star.step the_red_env (KExpr.const n us) e2 e2 (par_reduces_cd.delta the_red_env (KExpr.const n us) e2 (const_delta_step n us e2 h)) (par_reduces_cd_star.refl the_red_env e2))) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_c0 : forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh ty) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env ty e2) (_c1 : forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh v) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env v e2) (_c2 : forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh b) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env b e2) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.let_ ty v b)) (OptionType.some KExpr e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star the_red_env (KExpr.let_ ty v b) X) (instantiate b v) e2 (option_some_inj KExpr (instantiate b v) e2 h) (par_reduces_cd_star.step the_red_env (KExpr.let_ ty v b) (instantiate b v) (instantiate b v) (par_reduces_cd.let_ the_red_env ty ty v v b b (par_reduces_cd.refl the_red_env ty) (par_reduces_cd.refl the_red_env v) (par_reduces_cd.refl the_red_env b)) (par_reduces_cd_star.refl the_red_env (instantiate b v)))) (fun (s : Name) (i : Nat) (sub : KExpr) (_c0 : forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh sub) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env sub e2) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.proj s i sub)) (OptionType.some KExpr e2)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh sub) o -> Eq (OptionType KExpr) (opt_proj_lift s i o) (OptionType.some KExpr e2) -> par_reduces_cd_star the_red_env (KExpr.proj s i sub) e2) (fun (_hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh sub) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.some KExpr e2)) => option_none_ne_some_type KExpr e2 (par_reduces_cd_star the_red_env (KExpr.proj s i sub) e2) h2) (fun (sub2 : KExpr) (hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh sub) (OptionType.some KExpr sub2)) (h2 : Eq (OptionType KExpr) (OptionType.some KExpr (KExpr.proj s i sub2)) (OptionType.some KExpr e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star the_red_env (KExpr.proj s i sub) X) (KExpr.proj s i sub2) e2 (option_some_inj KExpr (KExpr.proj s i sub2) e2 h2) (par_reduces_cd_star_proj the_red_env s i sub sub2 (_c0 sub2 hq))) (reduce_once_red_wh the_red_env wh sub) (Eq.refl (OptionType KExpr) (reduce_once_red_wh the_red_env wh sub)) h) (fun (v : Nat) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.lit v)) (OptionType.some KExpr e2)) => option_none_ne_some_type KExpr e2 (par_reduces_cd_star the_red_env (KExpr.lit v) e2) h) e";

const LOOP_PAR: &str = "def whnf_fuel_red_wh_par (hiota : forall (w : KExpr -> OptionType KExpr) (g : KExpr) (x : KExpr) (r : KExpr), Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) w (KExpr.app g x)) (OptionType.some KExpr r) -> par_reduces_cd_star the_red_env (KExpr.app g x) r) (fuel : Nat) : forall (e : KExpr) (r : KExpr), Eq (OptionType KExpr) (whnf_fuel_red_wh the_red_env fuel e) (OptionType.some KExpr r) -> par_reduces_cd_star the_red_env e r := Nat.rec (fun (n : Nat) => forall (e : KExpr) (r : KExpr), Eq (OptionType KExpr) (whnf_fuel_red_wh the_red_env n e) (OptionType.some KExpr r) -> par_reduces_cd_star the_red_env e r) (fun (e : KExpr) (r : KExpr) (h : Eq (OptionType KExpr) (whnf_fuel_red_wh the_red_env Nat.zero e) (OptionType.some KExpr r)) => option_none_ne_some_type KExpr r (par_reduces_cd_star the_red_env e r) h) (fun (k : Nat) (ih : forall (e0 : KExpr) (r0 : KExpr), Eq (OptionType KExpr) (whnf_fuel_red_wh the_red_env k e0) (OptionType.some KExpr r0) -> par_reduces_cd_star the_red_env e0 r0) (e : KExpr) (r : KExpr) (h : Eq (OptionType KExpr) (whnf_fuel_red_wh the_red_env (Nat.succ k) e) (OptionType.some KExpr r)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red_wh the_red_env (fun (e3 : KExpr) => whnf_fuel_red_wh the_red_env k e3) e) o -> Eq (OptionType KExpr) (loop_dispatch o e (fun (e3 : KExpr) => whnf_fuel_red_wh the_red_env k e3)) (OptionType.some KExpr r) -> par_reduces_cd_star the_red_env e r) (fun (_hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env (fun (e3 : KExpr) => whnf_fuel_red_wh the_red_env k e3) e) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.none KExpr) e (fun (e3 : KExpr) => whnf_fuel_red_wh the_red_env k e3)) (OptionType.some KExpr r)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star the_red_env e X) e r (option_some_inj KExpr e r h2) (par_reduces_cd_star.refl the_red_env e)) (fun (e2 : KExpr) (hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env (fun (e3 : KExpr) => whnf_fuel_red_wh the_red_env k e3) e) (OptionType.some KExpr e2)) (h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.some KExpr e2) e (fun (e3 : KExpr) => whnf_fuel_red_wh the_red_env k e3)) (OptionType.some KExpr r)) => par_reduces_cd_star_trans the_red_env e e2 r (reduce_once_red_wh_par (fun (e3 : KExpr) => whnf_fuel_red_wh the_red_env k e3) hiota e e2 hq) (ih e2 r h2)) (reduce_once_red_wh the_red_env (fun (e3 : KExpr) => whnf_fuel_red_wh the_red_env k e3) e) (Eq.refl (OptionType KExpr) (reduce_once_red_wh the_red_env (fun (e3 : KExpr) => whnf_fuel_red_wh the_red_env k e3) e)) h) fuel";

impl Specification {
    /// The three soundness layers, innermost first.
    pub(super) fn add_wh_soundness(&mut self) -> Result<(), SpecError> {
        self.add_app_head_defeq()?;
        self.add_step_defeq()?;
        self.add_loop_defeq()?;
        self.add_algo_sound()?;
        self.add_par_leg()?;
        self.add_whnf_join_wh()?;
        Ok(())
    }

    /// The confluence join over the FAITHFUL loop.
    ///
    /// Derived in `defeq_whnf_join.rs`, next to the original it is derived from,
    /// so a change to that original fails loudly rather than silently leaving
    /// this one deriving from a stale shape. Registered *here*, because it
    /// consumes `whnf_fuel_red_wh_par` — registering it beside its original put
    /// it 62 stages before that leg existed, and the spec build rejected it with
    /// "Too many arguments", not "unknown identifier".
    fn add_whnf_join_wh(&mut self) -> Result<(), SpecError> {
        let (_orig, wh_src, _wh3) = super::defeq_whnf_join::join_sources();
        self.add_recursive_def(
            &wh_src,
            "def_eq_whnf_join_wh: the confluence join, over the faithful loop. \
             \
             The proof BODY is byte-identical to def_eq_whnf_join's: confluence does not care \
             which whnf produced the two endpoints, only that each is a par_reduces_cd_star \
             reduct of its source — which is exactly what whnf_fuel_red_wh_par supplies for the \
             pre-pass loop. So the entire confluence layer transfers to the faithful algorithm \
             with NO new mathematics, which is the return on having built the par leg as its own \
             brick. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// Paren balance — checked before registration, because an unbalanced source
    /// is a PARSE error that aborts the whole spec build.
    fn balanced_src(src: &str) -> bool {
        let mut d: i64 = 0;
        for c in src.chars() {
            match c {
                '(' => d += 1,
                ')' => d -= 1,
                _ => {}
            }
            if d < 0 {
                return false;
            }
        }
        d == 0
    }

    // ── layer 1: the application dispatch ────────────────────────────────────
    fn head_ih(x: &str) -> String {
        format!(
            "forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh {T} wh {x}) \
             (OptionType.some KExpr y) -> DefEq {x} y"
        )
    }
    fn head_goal(x: &str) -> String {
        format!(
            "forall (e2 : KExpr), Eq (OptionType KExpr) \
             (reduce_app_head_red_wh {T} wh a {x} (reduce_once_red_wh {T} wh {x})) \
             (OptionType.some KExpr e2) -> DefEq (KExpr.app {x} a) e2"
        )
    }
    fn head_motive(x: &str) -> String {
        format!("({}) -> {}", Self::head_ih(x), Self::head_goal(x))
    }

    /// The convoy shared by all eight non-`lam` head shapes: if the head does not
    /// step the whole application is a pre-pass ι; if it does, rebuild with
    /// `app_cong`.
    fn head_convoy(f: &str) -> String {
        format!(
            "OptionType.rec KExpr \
             (fun (o : OptionType KExpr) => Eq (OptionType KExpr) \
             (reduce_once_red_wh {T} wh {f}) o -> \
             Eq (OptionType KExpr) (opt_app_ilift_wh {T} wh {f} a o) \
             (OptionType.some KExpr e2) -> DefEq (KExpr.app {f} a) e2) \
             (fun (_hq : Eq (OptionType KExpr) (reduce_once_red_wh {T} wh {f}) \
             (OptionType.none KExpr)) \
             (h2 : Eq (OptionType KExpr) \
             (iota_reduct_whc (red_rec {T}) wh (KExpr.app {f} a)) \
             (OptionType.some KExpr e2)) => hiota wh {f} a e2 h2) \
             (fun (f2 : KExpr) (hq : Eq (OptionType KExpr) \
             (reduce_once_red_wh {T} wh {f}) (OptionType.some KExpr f2)) \
             (h2 : Eq (OptionType KExpr) (OptionType.some KExpr (KExpr.app f2 a)) \
             (OptionType.some KExpr e2)) => \
             Eq.substType KExpr (fun (X : KExpr) => DefEq (KExpr.app {f} a) X) \
             (KExpr.app f2 a) e2 (option_some_inj KExpr (KExpr.app f2 a) e2 h2) \
             (DefEq.app_cong {f} f2 a a (ihf f2 hq) (DefEq.refl a))) \
             (reduce_once_red_wh {T} wh {f}) \
             (Eq.refl (OptionType KExpr) (reduce_once_red_wh {T} wh {f})) h"
        )
    }

    pub(super) fn app_head_defeq_src() -> String {
        let mut arms = String::new();
        for (payload, fields, form) in SHAPES {
            let ihs: String = fields
                .iter()
                .enumerate()
                .map(|(k, fl)| format!("(_c{k} : ({})) ", Self::head_motive(fl)))
                .collect();
            // Only the lam head fires β; every other shape shares the convoy.
            let body = if form.starts_with("(KExpr.lam") {
                format!(
                    "Eq.substType KExpr (fun (X : KExpr) => DefEq (KExpr.app {form} a) X) \
                     (instantiate b a) e2 (option_some_inj KExpr (instantiate b a) e2 h) \
                     (DefEq.beta ty b a)"
                )
            } else {
                Self::head_convoy(form)
            };
            arms.push_str(&format!(
                "(fun {payload}{ihs}(ihf : {ih}) (e2 : KExpr) (h : Eq (OptionType KExpr) \
                 (reduce_app_head_red_wh {T} wh a {form} (reduce_once_red_wh {T} wh {form})) \
                 (OptionType.some KExpr e2)) => {body}) ",
                ih = Self::head_ih(form),
            ));
        }
        format!(
            "def reduce_app_head_wh_defeq (wh : KExpr -> OptionType KExpr) (hiota : {h}) \
             (a : KExpr) (f : KExpr) : {goal} := \
             KExpr.rec (fun (x : KExpr) => {motive}) {arms}f",
            h = hiota_ty(),
            goal = Self::head_motive("f"),
            motive = Self::head_motive("x"),
        )
    }

    fn add_app_head_defeq(&mut self) -> Result<(), SpecError> {
        let src = Self::app_head_defeq_src();
        debug_assert!(Self::balanced_src(&src), "app-head source parens");
        self.add_recursive_def(
            &src,
            "reduce_app_head_wh_defeq: the faithful loop's application dispatch is sound for \
             DefEq. Nine arms over the HEAD's shape: lam fires beta, and the other eight share \
             one convoy — case on whether the head itself steps, then either hand the whole \
             application to the iota hypothesis or rebuild it with app_cong on the head's \
             induction hypothesis. \
             \
             Generating eight arms from a single template rather than writing them out is the \
             same collapse this program has used throughout: the arms differ only in a form \
             string. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    // ── layer 2: one step of the loop ────────────────────────────────────────
    fn step_motive(x: &str) -> String {
        format!(
            "forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh {T} wh {x}) \
             (OptionType.some KExpr e2) -> DefEq {x} e2"
        )
    }

    pub(super) fn step_defeq_src() -> String {
        let mut arms = String::new();
        for (payload, fields, form) in SHAPES {
            let ihs: String = fields
                .iter()
                .enumerate()
                .map(|(k, fl)| format!("(_c{k} : {}) ", Self::step_motive(fl)))
                .collect();
            let body = if form.starts_with("(KExpr.app") {
                "reduce_app_head_wh_defeq wh hiota a2 f _c0 e2 h".to_string()
            } else if form.starts_with("(KExpr.const") {
                "defeq_of_const_delta n us e2 h".to_string()
            } else if form.starts_with("(KExpr.let_") {
                format!(
                    "Eq.substType KExpr (fun (X : KExpr) => DefEq {form} X) (instantiate b v) e2 \
                     (option_some_inj KExpr (instantiate b v) e2 h) (defeq_of_zeta_step ty v b)"
                )
            } else if form.starts_with("(KExpr.proj") {
                format!(
                    "OptionType.rec KExpr \
                     (fun (o : OptionType KExpr) => Eq (OptionType KExpr) \
                     (reduce_once_red_wh {T} wh sub) o -> \
                     Eq (OptionType KExpr) (opt_proj_lift s i o) (OptionType.some KExpr e2) -> \
                     DefEq {form} e2) \
                     (fun (_hq : Eq (OptionType KExpr) (reduce_once_red_wh {T} wh sub) \
                     (OptionType.none KExpr)) \
                     (h2 : Eq (OptionType KExpr) (OptionType.none KExpr) \
                     (OptionType.some KExpr e2)) => \
                     option_none_ne_some_type KExpr e2 (DefEq {form} e2) h2) \
                     (fun (sub2 : KExpr) (hq : Eq (OptionType KExpr) \
                     (reduce_once_red_wh {T} wh sub) (OptionType.some KExpr sub2)) \
                     (h2 : Eq (OptionType KExpr) (OptionType.some KExpr (KExpr.proj s i sub2)) \
                     (OptionType.some KExpr e2)) => \
                     Eq.substType KExpr (fun (X : KExpr) => DefEq {form} X) \
                     (KExpr.proj s i sub2) e2 \
                     (option_some_inj KExpr (KExpr.proj s i sub2) e2 h2) \
                     (DefEq.proj_cong s i sub sub2 (_c0 sub2 hq))) \
                     (reduce_once_red_wh {T} wh sub) \
                     (Eq.refl (OptionType KExpr) (reduce_once_red_wh {T} wh sub)) h"
                )
            } else {
                // sort, bvar, lam, pi, lit: the step returns none, so the
                // hypothesis is absurd.
                format!("option_none_ne_some_type KExpr e2 (DefEq {form} e2) h")
            };
            arms.push_str(&format!(
                "(fun {payload}{ihs}(e2 : KExpr) (h : Eq (OptionType KExpr) \
                 (reduce_once_red_wh {T} wh {form}) (OptionType.some KExpr e2)) => {body}) "
            ));
        }
        format!(
            "def reduce_once_red_wh_defeq (wh : KExpr -> OptionType KExpr) (hiota : {h}) \
             (e : KExpr) : {goal} := KExpr.rec (fun (x : KExpr) => {motive}) {arms}e",
            h = hiota_ty(),
            goal = Self::step_motive("e"),
            motive = Self::step_motive("x"),
        )
    }

    fn add_step_defeq(&mut self) -> Result<(), SpecError> {
        let src = Self::step_defeq_src();
        debug_assert!(Self::balanced_src(&src), "step source parens");
        self.add_recursive_def(
            &src,
            "reduce_once_red_wh_defeq: one step of the faithful loop is sound for DefEq. \
             \
             Pure assembly — nothing here is new work. FIVE of the nine arms are dead, because \
             the step returns none on a sort, bvar, lam, pi or lit and the hypothesis is absurd. \
             const and let_ are the two small bricks proved earlier (defeq_of_const_delta, \
             defeq_of_zeta_step). proj is a convoy into proj_cong. app delegates to the \
             application dispatch. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    // ── layer 3: the loop ────────────────────────────────────────────────────
    pub(super) fn loop_defeq_src() -> String {
        let whk = format!("(fun (e3 : KExpr) => whnf_fuel_red_wh {T} k e3)");
        format!(
            "def whnf_fuel_red_wh_defeq (hiota : {h}) (fuel : Nat) : \
             forall (e : KExpr) (r : KExpr), Eq (OptionType KExpr) \
             (whnf_fuel_red_wh {T} fuel e) (OptionType.some KExpr r) -> DefEq e r := \
             Nat.rec (fun (n : Nat) => forall (e : KExpr) (r : KExpr), Eq (OptionType KExpr) \
             (whnf_fuel_red_wh {T} n e) (OptionType.some KExpr r) -> DefEq e r) \
             (fun (e : KExpr) (r : KExpr) (h : Eq (OptionType KExpr) \
             (whnf_fuel_red_wh {T} Nat.zero e) (OptionType.some KExpr r)) => \
             option_none_ne_some_type KExpr r (DefEq e r) h) \
             (fun (k : Nat) (ih : forall (e0 : KExpr) (r0 : KExpr), Eq (OptionType KExpr) \
             (whnf_fuel_red_wh {T} k e0) (OptionType.some KExpr r0) -> DefEq e0 r0) \
             (e : KExpr) (r : KExpr) (h : Eq (OptionType KExpr) \
             (whnf_fuel_red_wh {T} (Nat.succ k) e) (OptionType.some KExpr r)) => \
             OptionType.rec KExpr (fun (o : OptionType KExpr) => \
             Eq (OptionType KExpr) (reduce_once_red_wh {T} {whk} e) o -> \
             Eq (OptionType KExpr) (loop_dispatch o e {whk}) (OptionType.some KExpr r) -> \
             DefEq e r) \
             (fun (_hq : Eq (OptionType KExpr) (reduce_once_red_wh {T} {whk} e) \
             (OptionType.none KExpr)) \
             (h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.none KExpr) e {whk}) \
             (OptionType.some KExpr r)) => \
             Eq.substType KExpr (fun (X : KExpr) => DefEq e X) e r \
             (option_some_inj KExpr e r h2) (DefEq.refl e)) \
             (fun (e2 : KExpr) (hq : Eq (OptionType KExpr) (reduce_once_red_wh {T} {whk} e) \
             (OptionType.some KExpr e2)) (h2 : Eq (OptionType KExpr) \
             (loop_dispatch (OptionType.some KExpr e2) e {whk}) (OptionType.some KExpr r)) => \
             DefEq.trans e e2 r (reduce_once_red_wh_defeq {whk} hiota e e2 hq) (ih e2 r h2)) \
             (reduce_once_red_wh {T} {whk} e) \
             (Eq.refl (OptionType KExpr) (reduce_once_red_wh {T} {whk} e)) h) fuel",
            h = hiota_ty(),
        )
    }

    fn add_loop_defeq(&mut self) -> Result<(), SpecError> {
        let src = Self::loop_defeq_src();
        debug_assert!(Self::balanced_src(&src), "loop source parens");
        self.add_recursive_def(
            &src,
            "whnf_fuel_red_wh_defeq: THE FAITHFUL LOOP IS SOUND — its result is definitionally \
             equal to its input. \
             \
             The standard fuel induction. At zero the loop returns none, so the hypothesis is \
             absurd. At succ k, case on the step: if it finds nothing the result IS the input and \
             DefEq.refl closes it; if it steps once, DefEq.trans composes that step's soundness \
             with the induction hypothesis on the tail. \
             \
             This is the half that makes completeness worth proving. A checker that accepts \
             everything is complete; soundness is what makes acceptance mean something. \
             DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    // ── layer 4: the algorithm ───────────────────────────────────────────────
    pub(super) fn algo_sound_src() -> String {
        let inner = format!("(fun (nb : KExpr) => def_eq_struct (def_eq_fuel_wh {T} k) na nb)");
        let outer = format!(
            "(fun (na : KExpr) => OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) \
             Bool.false {inner} (whnf_fuel_red_wh {T} k b))"
        );
        // SIMPLER than the original chain. def_eq_fuel_sound must route through
        // whnf_red_conv_to_def_eq, because whnf_fuel_red_conv only yields a
        // weak-head conversion; whnf_fuel_red_wh_defeq yields DefEq outright, so
        // that hop disappears. The retreat to DefEq — forced because
        // whnf_red_step has no app_right congruence — SIMPLIFIES what depends on
        // it rather than complicating it.
        let chain = format!(
            "DefEq.trans a na b (whnf_fuel_red_wh_defeq hiota k a na hna) \
             (DefEq.trans na nb b \
             (def_eq_struct_sound (def_eq_fuel_wh {T} k) ih na nb hgrid) \
             (DefEq.symm b nb (whnf_fuel_red_wh_defeq hiota k b nb hnb)))"
        );
        let succ = format!(
            "opt_rec_bool_true_inv (whnf_fuel_red_wh {T} k a) {outer} (DefEq a b) \
             (fun (na : KExpr) (hna : Eq (OptionType KExpr) (whnf_fuel_red_wh {T} k a) \
             (OptionType.some KExpr na)) \
             (hin : Eq Bool (OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) \
             Bool.false {inner} (whnf_fuel_red_wh {T} k b)) Bool.true) => \
             opt_rec_bool_true_inv (whnf_fuel_red_wh {T} k b) {inner} (DefEq a b) \
             (fun (nb : KExpr) (hnb : Eq (OptionType KExpr) (whnf_fuel_red_wh {T} k b) \
             (OptionType.some KExpr nb)) \
             (hgrid : Eq Bool (def_eq_struct (def_eq_fuel_wh {T} k) na nb) Bool.true) => \
             {chain}) hin) \
             (Eq.substType Bool (fun (x : Bool) => Eq Bool x Bool.true) \
             (def_eq_fuel_wh {T} (Nat.succ k) a b) \
             (OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false {outer} \
             (whnf_fuel_red_wh {T} k a)) (def_eq_fuel_wh_succ {T} k a b) h)"
        );
        format!(
            "def def_eq_fuel_wh_sound (hiota : {h}) : \
             forall (n : Nat) (a : KExpr) (b : KExpr), \
             Eq Bool (def_eq_fuel_wh {T} n a b) Bool.true -> DefEq a b := \
             Nat.rec (fun (z : Nat) => forall (a : KExpr) (b : KExpr), \
             Eq Bool (def_eq_fuel_wh {T} z a b) Bool.true -> DefEq a b) \
             (fun (a : KExpr) (b : KExpr) \
             (h : Eq Bool (def_eq_fuel_wh {T} Nat.zero a b) Bool.true) => \
             bool_false_ne_true_t (DefEq a b) \
             (Eq.trans Bool Bool.false (def_eq_fuel_wh {T} Nat.zero a b) Bool.true \
             (Eq.symm Bool (def_eq_fuel_wh {T} Nat.zero a b) Bool.false \
             (def_eq_fuel_wh_zero {T} a b)) h)) \
             (fun (k : Nat) (ih : forall (a : KExpr) (b : KExpr), \
             Eq Bool (def_eq_fuel_wh {T} k a b) Bool.true -> DefEq a b) \
             (a : KExpr) (b : KExpr) \
             (h : Eq Bool (def_eq_fuel_wh {T} (Nat.succ k) a b) Bool.true) => {succ})",
            h = hiota_ty(),
        )
    }

    fn add_algo_sound(&mut self) -> Result<(), SpecError> {
        let src = Self::algo_sound_src();
        debug_assert!(
            Self::balanced_src(&src),
            "algorithm-soundness source parens"
        );
        self.add_recursive_def(
            &src,
            "def_eq_fuel_wh_sound: THE FAITHFUL ALGORITHM IS SOUND — if it accepts a against b \
             then a and b really are definitionally equal. \
             \
             Two facts about the architecture show up here. First, def_eq_struct_sound appears \
             UNCHANGED, merely instantiated at the new comparator: the struct layer is declared \
             parametric in its comparator, so it carries over to the faithful algorithm for free. \
             That is 65 of the ~100 def_eq_fuel mentions in the completeness spine, discharged by \
             a design decision made long before this problem existed. \
             \
             Second, this proof is SIMPLER than def_eq_fuel_sound. That one routes through \
             whnf_red_conv_to_def_eq, because whnf_fuel_red_conv only yields a weak-head \
             conversion; whnf_fuel_red_wh_defeq yields DefEq outright, so the hop disappears. The \
             retreat to DefEq was forced — whnf_red_step has no app_right congruence and cannot \
             express a pre-pass at all — and it turns out to simplify everything downstream rather \
             than complicate it. \
             \
             With this the faithful algorithm has the half that makes the other half worth \
             proving: completeness alone is satisfied by the constant-true comparator. \
             DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    // ── the PAR LEG: the same three layers, retargeted to par_reduces_cd_star ──
    //
    // The existing whnf_fuel_red_par_leg routes through whnf_red_step_star, which
    // the faithful loop cannot use — the same missing app_right congruence that
    // forced soundness onto DefEq. So the par leg is rebuilt here as the DefEq
    // chain RETARGETED: DefEq.trans -> par_reduces_cd_star_trans, DefEq.refl ->
    // star.refl, app_cong -> par_reduces_cd_star_app, proj_cong ->
    // par_reduces_cd_star_proj, and every single step wrapped as
    // `star.step … star.refl`.
    //
    // That the second target cost a substitution table rather than a
    // re-derivation is the payoff for having built the first chain as a
    // generator. This is what def_eq_whnf_join needs — "whnf results are
    // par_reduces_cd_star reducts" — for the faithful loop.
    pub(super) fn const_delta_step_src() -> String {
        CONST_DELTA_STEP.to_string()
    }
    pub(super) fn app_head_par_src() -> String {
        APP_HEAD_PAR.to_string()
    }
    pub(super) fn step_par_src() -> String {
        STEP_PAR.to_string()
    }
    pub(super) fn loop_par_src() -> String {
        LOOP_PAR.to_string()
    }

    fn add_par_leg(&mut self) -> Result<(), SpecError> {
        for (name, src, desc) in [
            (
                "const_delta_step",
                Self::const_delta_step_src(),
                "const_delta_step: a constant with a definitional value takes a real delta step. \
              Extracted from defeq_of_const_delta because BOTH the DefEq chain and the par leg \
              need it — reusing rather than re-proving. DerivedProved, zero axiom_deps.",
            ),
            (
                "reduce_app_head_wh_par",
                Self::app_head_par_src(),
                "reduce_app_head_wh_par: the application dispatch's step is a par_reduces_cd_star \
              reduction. The DefEq proof retargeted; the arms are identical in shape. \
              DerivedProved, zero axiom_deps.",
            ),
            (
                "reduce_once_red_wh_par",
                Self::step_par_src(),
                "reduce_once_red_wh_par: one step of the faithful loop is a par_reduces_cd_star \
              reduction. DerivedProved, zero axiom_deps.",
            ),
            (
                "whnf_fuel_red_wh_par",
                Self::loop_par_src(),
                "whnf_fuel_red_wh_par: THE PAR LEG — every result of the faithful loop is a \
              par_reduces_cd_star reduct of its input. \
              \
              This is what def_eq_whnf_join consumes: the capstone joins the two sides' whnfs by \
              confluence, and confluence is stated over par_reduces_cd_star. The pre-existing \
              whnf_fuel_red_par_leg cannot serve, because it routes through whnf_red_step_star \
              and that relation has no app_right congruence — the same obstruction that forced \
              soundness onto DefEq. DerivedProved, zero axiom_deps.",
            ),
        ] {
            debug_assert!(Self::balanced_src(&src), "{name} parens");
            self.add_recursive_def(&src, desc)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    /// The derived join must be registered AFTER the par leg it consumes.
    ///
    /// This exact ordering was wrong once: the variant sat beside its original
    /// in `add_defeq_whnf_join` (stage 426), 62 stages before
    /// `whnf_fuel_red_wh_par` was registered (stage 488). The scratchpad could
    /// not see it — it appends to an already-built spec, where every dependency
    /// is trivially in scope — so it took a 24-minute `axiom_ratchet` to find.
    /// This test finds it in milliseconds.
    #[test]
    fn wh_join_is_registered_after_the_par_leg() {
        let src = include_str!("wh_soundness.rs");
        let body_start = src
            .find("pub(super) fn add_wh_soundness")
            .expect("fn present");
        let body = &src[body_start..];
        let leg = body.find("self.add_par_leg()").expect("par leg registered");
        let join = body
            .find("self.add_whnf_join_wh()")
            .expect("wh join registered");
        assert!(
            leg < join,
            "def_eq_whnf_join_wh consumes whnf_fuel_red_wh_par and must be registered after it"
        );
    }

    /// The wh join must NOT be registered next to the original it is derived from.
    #[test]
    fn wh_join_is_not_registered_in_defeq_whnf_join() {
        let src = include_str!("defeq_whnf_join.rs");
        assert!(
            !src.contains("&wh_src,"),
            "the derived join is REGISTERED in wh_soundness.rs, not beside its original — \
             registering it there places it before whnf_fuel_red_wh_par exists"
        );
    }
    use super::*;

    /// The soundness chain names `def_eq_fuel_wh` and its two computation rules,
    /// all registered by `add_hnf_conv`. So `add_wh_soundness` must be called
    /// AFTER it.
    ///
    /// This is the THIRD ordering bug in this program, so the guard is now
    /// mechanical rather than remembered. The scratchpad structurally cannot
    /// catch this class — it appends candidates to a fully-built spec, where
    /// every name is already in scope — which is exactly why a scratchpad PASS
    /// followed by a core_spec FAIL means "check the order", not "check the term".
    /// Here the two strings were byte-identical and only the environment differed.
    #[test]
    fn test_soundness_registers_after_the_algorithm() {
        let src = include_str!("defeq_fuel.rs");
        let hnf = src
            .find("self.add_hnf_conv()")
            .expect("hnf_conv registration");
        let snd = src
            .find("self.add_wh_soundness()")
            .expect("soundness registration");
        assert!(
            hnf < snd,
            "wh_soundness names def_eq_fuel_wh and its rules, so hnf_conv must register first"
        );
    }

    /// All three sources must be paren-balanced. An unbalanced source is a PARSE
    /// error, which aborts the entire spec build before any declaration is
    /// elaborated — the most expensive and least informative failure available.
    #[test]
    fn test_sources_are_paren_balanced() {
        for (name, src) in [
            ("app_head", Specification::app_head_defeq_src()),
            ("step", Specification::step_defeq_src()),
            ("loop", Specification::loop_defeq_src()),
            ("algo", Specification::algo_sound_src()),
        ] {
            assert!(
                Specification::balanced_src(&src),
                "{name} source is not paren-balanced"
            );
        }
    }

    /// Nine arms per `KExpr.rec`, one per constructor.
    #[test]
    fn test_nine_arms_per_recursor() {
        for (name, src) in [
            ("app_head", Specification::app_head_defeq_src()),
            ("step", Specification::step_defeq_src()),
        ] {
            let mut depth: i64 = 0;
            let mut top = 0usize;
            for (idx, ch) in src.char_indices() {
                match ch {
                    '(' => {
                        if depth == 0 && src[idx..].starts_with("(fun ") {
                            top += 1;
                        }
                        depth += 1;
                    }
                    ')' => depth -= 1,
                    _ => {}
                }
            }
            // One motive lambda plus nine arms.
            assert_eq!(top, 10, "{name}: expected a motive plus nine arms");
        }
    }

    /// Exactly five arms of the step lemma are dead — sort, bvar, lam, pi, lit.
    /// If that count moved, either the step function gained a case or an arm that
    /// should do work is being discharged as absurd.
    #[test]
    fn test_five_step_arms_are_absurd() {
        let src = Specification::step_defeq_src();
        assert_eq!(
            src.matches("option_none_ne_some_type KExpr e2 (DefEq (KExpr.")
                .count(),
            6,
            "five dead arms plus the proj convoy's none branch"
        );
    }
}
