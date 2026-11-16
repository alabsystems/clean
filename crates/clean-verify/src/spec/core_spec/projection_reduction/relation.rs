// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Projection-extended reduction, old embedding and actual new-step transport.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Inductive(
        r"inductive par_reduces_cdp (env : RedEnv) : KExpr → KExpr → Type
| refl : forall (e : KExpr), par_reduces_cdp env e e
| beta : forall (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr), par_reduces_cdp env A A' → par_reduces_cdp env body body' → par_reduces_cdp env arg arg' → par_reduces_cdp env (KExpr.app (KExpr.lam A body) arg) (instantiate body' arg')
| app : forall (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), par_reduces_cdp env f f' → par_reduces_cdp env a a' → par_reduces_cdp env (KExpr.app f a) (KExpr.app f' a')
| lam : forall (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_cdp env ty ty' → par_reduces_cdp env body body' → par_reduces_cdp env (KExpr.lam ty body) (KExpr.lam ty' body')
| pi : forall (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_cdp env dom dom' → par_reduces_cdp env body body' → par_reduces_cdp env (KExpr.pi dom body) (KExpr.pi dom' body')
| forall_ : forall (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_cdp env dom dom' → par_reduces_cdp env body body' → par_reduces_cdp env (KExpr.forall_ dom body) (KExpr.forall_ dom' body')
| let_ : forall (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_cdp env ty ty' → par_reduces_cdp env val val' → par_reduces_cdp env body body' → par_reduces_cdp env (KExpr.let_ ty val body) (instantiate body' val')
| iota : forall (e : KExpr) (e' : KExpr), iota_step (red_rec env) e e' → par_reduces_cdp env e e'
| delta : forall (e : KExpr) (e' : KExpr), delta_step (red_def env) e e' → par_reduces_cdp env e e'
| let_cong : forall (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_cdp env ty ty' → par_reduces_cdp env val val' → par_reduces_cdp env body body' → par_reduces_cdp env (KExpr.let_ ty val body) (KExpr.let_ ty' val' body')
| proj : forall (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr), par_reduces_cdp env sub sub' → par_reduces_cdp env (KExpr.proj s i sub) (KExpr.proj s i sub')
| projection_beta : forall (S : Name) (idx : Nat) (subject result : KExpr),
 @Eq (OptionType KExpr) (projection_post_whnf_reduct env (KExpr.proj S idx subject)) (@OptionType.some KExpr result) ->
 par_reduces_cdp env (KExpr.proj S idx subject) result",
    ),
    DeclarationInput::Proof(
        "par_reduces_cd_to_cdp",
        r"forall (R : RedEnv) (e e2 : KExpr) (h : par_reduces_cd R e e2), par_reduces_cdp R e e2",
        r"fun (R : RedEnv) (e e2 : KExpr) (h : par_reduces_cd R e e2) => @par_reduces_cd.rec R (fun (x y : KExpr) (_h : par_reduces_cd R x y) => par_reduces_cdp R x y)
  (fun (x : KExpr) => @par_reduces_cdp.refl R x)
  (fun (A A2 b b2 a a2 : KExpr) (_hA : par_reduces_cd R A A2) (_hb : par_reduces_cd R b b2) (_ha : par_reduces_cd R a a2)
   (hA : par_reduces_cdp R A A2) (hb : par_reduces_cdp R b b2) (ha : par_reduces_cdp R a a2) => @par_reduces_cdp.beta R A A2 b b2 a a2 hA hb ha)
  (fun (f f2 a a2 : KExpr) (_hf : par_reduces_cd R f f2) (_ha : par_reduces_cd R a a2)
   (hf : par_reduces_cdp R f f2) (ha : par_reduces_cdp R a a2) => @par_reduces_cdp.app R f f2 a a2 hf ha)
  (fun (A A2 b b2 : KExpr) (_hA : par_reduces_cd R A A2) (_hb : par_reduces_cd R b b2)
   (hA : par_reduces_cdp R A A2) (hb : par_reduces_cdp R b b2) => @par_reduces_cdp.lam R A A2 b b2 hA hb)
  (fun (A A2 b b2 : KExpr) (_hA : par_reduces_cd R A A2) (_hb : par_reduces_cd R b b2)
   (hA : par_reduces_cdp R A A2) (hb : par_reduces_cdp R b b2) => @par_reduces_cdp.pi R A A2 b b2 hA hb)
  (fun (A A2 b b2 : KExpr) (_hA : par_reduces_cd R A A2) (_hb : par_reduces_cd R b b2)
   (hA : par_reduces_cdp R A A2) (hb : par_reduces_cdp R b b2) => @par_reduces_cdp.forall_ R A A2 b b2 hA hb)
  (fun (A A2 v v2 b b2 : KExpr) (_hA : par_reduces_cd R A A2) (_hv : par_reduces_cd R v v2) (_hb : par_reduces_cd R b b2)
   (hA : par_reduces_cdp R A A2) (hv : par_reduces_cdp R v v2) (hb : par_reduces_cdp R b b2) => @par_reduces_cdp.let_ R A A2 v v2 b b2 hA hv hb)
  (fun (x y : KExpr) (step : iota_step (red_rec R) x y) => @par_reduces_cdp.iota R x y step)
  (fun (x y : KExpr) (step : delta_step (red_def R) x y) => @par_reduces_cdp.delta R x y step)
  (fun (A A2 v v2 b b2 : KExpr) (_hA : par_reduces_cd R A A2) (_hv : par_reduces_cd R v v2) (_hb : par_reduces_cd R b b2)
   (hA : par_reduces_cdp R A A2) (hv : par_reduces_cdp R v v2) (hb : par_reduces_cdp R b b2) => @par_reduces_cdp.let_cong R A A2 v v2 b b2 hA hv hb)
  (fun (S : Name) (idx : Nat) (x y : KExpr) (_h : par_reduces_cd R x y) (h : par_reduces_cdp R x y) => @par_reduces_cdp.proj R S idx x y h)
  e e2 h",
    ),
    DeclarationInput::Inductive(
        r"inductive par_reduces_cdp_list (R : RedEnv) : ListType KExpr -> ListType KExpr -> Type
| nil : par_reduces_cdp_list R (@ListType.nil KExpr) (@ListType.nil KExpr)
| cons : forall (a b : KExpr) (xs ys : ListType KExpr),
 par_reduces_cdp R a b -> par_reduces_cdp_list R xs ys ->
 par_reduces_cdp_list R (@ListType.cons KExpr a xs) (@ListType.cons KExpr b ys)",
    ),
    DeclarationInput::Proof(
        "par_reduces_cdp_list_refl",
        r"forall (R : RedEnv) (xs : ListType KExpr), par_reduces_cdp_list R xs xs",
        r"fun (R : RedEnv) (xs : ListType KExpr) => @ListType.rec KExpr (fun (zs : ListType KExpr) => par_reduces_cdp_list R zs zs)
  (@par_reduces_cdp_list.nil R)
  (fun (a : KExpr) (rest : ListType KExpr) (ih : par_reduces_cdp_list R rest rest) =>
   @par_reduces_cdp_list.cons R a a rest rest (@par_reduces_cdp.refl R a) ih) xs",
    ),
    DeclarationInput::Proof(
        "par_reduces_cdp_list_append",
        r"forall (R : RedEnv) (xs xs2 : ListType KExpr)
 (h : par_reduces_cdp_list R xs xs2) (ys ys2 : ListType KExpr) (hy : par_reduces_cdp_list R ys ys2), par_reduces_cdp_list R (list_append xs ys) (list_append xs2 ys2)",
        r"fun (R : RedEnv) (xs xs2 : ListType KExpr)
 (h : par_reduces_cdp_list R xs xs2) (ys ys2 : ListType KExpr) (hy : par_reduces_cdp_list R ys ys2) => @par_reduces_cdp_list.rec R
  (fun (as1 as2 : ListType KExpr) (_h : par_reduces_cdp_list R as1 as2) =>
   par_reduces_cdp_list R (list_append as1 ys) (list_append as2 ys2)) hy
  (fun (a b : KExpr) (as1 as2 : ListType KExpr) (hab : par_reduces_cdp R a b)
   (_ht : par_reduces_cdp_list R as1 as2)
   (ih : par_reduces_cdp_list R (list_append as1 ys) (list_append as2 ys2)) =>
   @par_reduces_cdp_list.cons R a b (list_append as1 ys) (list_append as2 ys2) hab ih) xs xs2 h",
    ),
    DeclarationInput::Proof(
        "par_reduces_cdp_list_tail",
        r"forall (R : RedEnv) (xs ys : ListType KExpr)
 (h : par_reduces_cdp_list R xs ys), par_reduces_cdp_list R (list_tail xs) (list_tail ys)",
        r"fun (R : RedEnv) (xs ys : ListType KExpr)
 (h : par_reduces_cdp_list R xs ys) => @par_reduces_cdp_list.rec R
  (fun (as1 as2 : ListType KExpr) (_h : par_reduces_cdp_list R as1 as2) =>
   par_reduces_cdp_list R (list_tail as1) (list_tail as2)) (@par_reduces_cdp_list.nil R)
  (fun (a b : KExpr) (as1 as2 : ListType KExpr) (_hab : par_reduces_cdp R a b)
   (ht : par_reduces_cdp_list R as1 as2)
   (_ih : par_reduces_cdp_list R (list_tail as1) (list_tail as2)) => ht) xs ys h",
    ),
    DeclarationInput::Proof(
        "par_reduces_cdp_list_drop",
        r"forall (R : RedEnv) (k : Nat) (xs ys : ListType KExpr)
 (h : par_reduces_cdp_list R xs ys), par_reduces_cdp_list R (list_drop k xs) (list_drop k ys)",
        r"fun (R : RedEnv) (k : Nat) (xs ys : ListType KExpr)
 (h : par_reduces_cdp_list R xs ys) => @Nat.rec
  (fun (n : Nat) => forall (as1 as2 : ListType KExpr), par_reduces_cdp_list R as1 as2 ->
   par_reduces_cdp_list R (list_drop n as1) (list_drop n as2))
  (fun (as1 as2 : ListType KExpr) (ht : par_reduces_cdp_list R as1 as2) => ht)
  (fun (n : Nat)
   (ih : forall (as1 as2 : ListType KExpr), par_reduces_cdp_list R as1 as2 ->
    par_reduces_cdp_list R (list_drop n as1) (list_drop n as2))
   (as1 as2 : ListType KExpr) (ht : par_reduces_cdp_list R as1 as2) =>
   ih (list_tail as1) (list_tail as2) (par_reduces_cdp_list_tail R as1 as2 ht)) k xs ys h",
    ),
    DeclarationInput::Proof(
        "par_reduces_cdp_list_head_some",
        r"forall (R : RedEnv) (xs ys : ListType KExpr)
 (h : par_reduces_cdp_list R xs ys) (a : KExpr) (C : Type)
 (found : @Eq (OptionType KExpr) (list_head xs) (@OptionType.some KExpr a))
 (next : forall (b : KExpr), @Eq (OptionType KExpr) (list_head ys) (@OptionType.some KExpr b) -> par_reduces_cdp R a b -> C), C",
        r"fun (R : RedEnv) (xs ys : ListType KExpr)
 (h : par_reduces_cdp_list R xs ys) (a : KExpr) (C : Type)
 (found : @Eq (OptionType KExpr) (list_head xs) (@OptionType.some KExpr a))
 (next : forall (b : KExpr), @Eq (OptionType KExpr) (list_head ys) (@OptionType.some KExpr b) -> par_reduces_cdp R a b -> C) => @par_reduces_cdp_list.rec R
  (fun (as1 as2 : ListType KExpr) (_h : par_reduces_cdp_list R as1 as2) =>
   @Eq (OptionType KExpr) (list_head as1) (@OptionType.some KExpr a) ->
   (forall (b : KExpr), @Eq (OptionType KExpr) (list_head as2) (@OptionType.some KExpr b) -> par_reduces_cdp R a b -> C) -> C)
  (fun (bad : @Eq (OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr a))
   (_next : forall (b : KExpr), @Eq (OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr b) -> par_reduces_cdp R a b -> C) =>
   option_none_ne_some_type KExpr a C bad)
  (fun (x y : KExpr) (as1 as2 : ListType KExpr) (hxy : par_reduces_cdp R x y)
   (_ht : par_reduces_cdp_list R as1 as2)
   (_ih : @Eq (OptionType KExpr) (list_head as1) (@OptionType.some KExpr a) ->
    (forall (b : KExpr), @Eq (OptionType KExpr) (list_head as2) (@OptionType.some KExpr b) -> par_reduces_cdp R a b -> C) -> C)
   (same : @Eq (OptionType KExpr) (@OptionType.some KExpr x) (@OptionType.some KExpr a))
   (proceed : forall (b : KExpr), @Eq (OptionType KExpr) (@OptionType.some KExpr y) (@OptionType.some KExpr b) -> par_reduces_cdp R a b -> C) =>
   proceed y (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr y))
    (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cdp R z y) x a (option_some_inj KExpr x a same) hxy))
  xs ys h found next",
    ),
    DeclarationInput::Inductive(
        r"inductive ParCDPCtorSpineView (R : RedEnv) (e e2 : KExpr) : Type
| mk : @Eq KExpr (kapp_fn e2) (kapp_fn e) ->
 par_reduces_cdp_list R (kapp_args e) (kapp_args e2) -> ParCDPCtorSpineView R e e2",
    ),
    DeclarationInput::Proof(
        "par_reduces_cdp_list_length",
        r"forall (R : RedEnv) (xs ys : ListType KExpr) (h : par_reduces_cdp_list R xs ys), @Eq Nat (list_length xs) (list_length ys)",
        r"fun (R : RedEnv) (xs ys : ListType KExpr) (h : par_reduces_cdp_list R xs ys) => @par_reduces_cdp_list.rec R
  (fun (as1 as2 : ListType KExpr) (_h : par_reduces_cdp_list R as1 as2) => @Eq Nat (list_length as1) (list_length as2))
  (@Eq.refl Nat Nat.zero)
  (fun (a b : KExpr) (as1 as2 : ListType KExpr) (_hab : par_reduces_cdp R a b)
   (_ht : par_reduces_cdp_list R as1 as2) (ih : @Eq Nat (list_length as1) (list_length as2)) =>
   Eq.cong Nat Nat Nat.succ (list_length as1) (list_length as2) ih) xs ys h",
    ),
    DeclarationInput::Proof(
        "ctor_metadata_spine_preserved_cdp",
        r"forall (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e e2 : KExpr) (h : par_reduces_cdp R e e2)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n)), ParCDPCtorSpineView R e e2",
        r"fun (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e e2 : KExpr) (h : par_reduces_cdp R e e2)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n)) => @par_reduces_cdp.rec R
  (fun (x y : KExpr) (_h : par_reduces_cdp R x y) =>
   @Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (@OptionType.some Name n) -> ParCDPCtorSpineView R x y)
  (fun (x : KExpr) (_head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (@OptionType.some Name n)) => @ParCDPCtorSpineView.mk R x x (@Eq.refl KExpr (kapp_fn x)) (par_reduces_cdp_list_refl R (kapp_args x)))
  (fun (A A2 body body2 arg arg2 : KExpr)
 (_hA : par_reduces_cdp R A A2)
 (_hbody : par_reduces_cdp R body body2)
 (_harg : par_reduces_cdp R arg arg2)
 (_ihA : @Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (@OptionType.some Name n) -> ParCDPCtorSpineView R A A2)
 (_ihbody : @Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (@OptionType.some Name n) -> ParCDPCtorSpineView R body body2)
 (_iharg : @Eq (OptionType Name) (kexpr_const_name (kapp_fn arg)) (@OptionType.some Name n) -> ParCDPCtorSpineView R arg arg2)
 (impossible : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app (KExpr.lam A body) arg))) (@OptionType.some Name n)) =>
 option_none_ne_some_type Name n (ParCDPCtorSpineView R (KExpr.app (KExpr.lam A body) arg) (instantiate body2 arg2)) impossible)
  (fun (f f2 a a2 : KExpr) (_hf : par_reduces_cdp R f f2) (ha : par_reduces_cdp R a a2)
 (ihf : @Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (@OptionType.some Name n) -> ParCDPCtorSpineView R f f2)
 (_iha : @Eq (OptionType Name) (kexpr_const_name (kapp_fn a)) (@OptionType.some Name n) -> ParCDPCtorSpineView R a a2)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (@OptionType.some Name n)) =>
 @ParCDPCtorSpineView.rec R f f2
  (fun (_v : ParCDPCtorSpineView R f f2) => ParCDPCtorSpineView R (KExpr.app f a) (KExpr.app f2 a2))
  (fun (same : @Eq KExpr (kapp_fn f2) (kapp_fn f))
   (args : par_reduces_cdp_list R (kapp_args f) (kapp_args f2)) =>
   @ParCDPCtorSpineView.mk R (KExpr.app f a) (KExpr.app f2 a2) same
    (par_reduces_cdp_list_append R (kapp_args f) (kapp_args f2) args
     (@ListType.cons KExpr a (@ListType.nil KExpr)) (@ListType.cons KExpr a2 (@ListType.nil KExpr))
     (@par_reduces_cdp_list.cons R a a2 (@ListType.nil KExpr) (@ListType.nil KExpr) ha (@par_reduces_cdp_list.nil R)))) (ihf head))
  (fun (A A2 body body2 : KExpr)
 (_hA : par_reduces_cdp R A A2)
 (_hbody : par_reduces_cdp R body body2)
 (_ihA : @Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (@OptionType.some Name n) -> ParCDPCtorSpineView R A A2)
 (_ihbody : @Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (@OptionType.some Name n) -> ParCDPCtorSpineView R body body2)
 (impossible : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam A body))) (@OptionType.some Name n)) =>
 option_none_ne_some_type Name n (ParCDPCtorSpineView R (KExpr.lam A body) (KExpr.lam A2 body2)) impossible)
  (fun (A A2 body body2 : KExpr)
 (_hA : par_reduces_cdp R A A2)
 (_hbody : par_reduces_cdp R body body2)
 (_ihA : @Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (@OptionType.some Name n) -> ParCDPCtorSpineView R A A2)
 (_ihbody : @Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (@OptionType.some Name n) -> ParCDPCtorSpineView R body body2)
 (impossible : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.pi A body))) (@OptionType.some Name n)) =>
 option_none_ne_some_type Name n (ParCDPCtorSpineView R (KExpr.pi A body) (KExpr.pi A2 body2)) impossible)
  (fun (A A2 body body2 : KExpr)
 (_hA : par_reduces_cdp R A A2)
 (_hbody : par_reduces_cdp R body body2)
 (_ihA : @Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (@OptionType.some Name n) -> ParCDPCtorSpineView R A A2)
 (_ihbody : @Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (@OptionType.some Name n) -> ParCDPCtorSpineView R body body2)
 (impossible : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.forall_ A body))) (@OptionType.some Name n)) =>
 option_none_ne_some_type Name n (ParCDPCtorSpineView R (KExpr.forall_ A body) (KExpr.forall_ A2 body2)) impossible)
  (fun (A A2 val val2 body body2 : KExpr)
 (_hA : par_reduces_cdp R A A2)
 (_hval : par_reduces_cdp R val val2)
 (_hbody : par_reduces_cdp R body body2)
 (_ihA : @Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (@OptionType.some Name n) -> ParCDPCtorSpineView R A A2)
 (_ihval : @Eq (OptionType Name) (kexpr_const_name (kapp_fn val)) (@OptionType.some Name n) -> ParCDPCtorSpineView R val val2)
 (_ihbody : @Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (@OptionType.some Name n) -> ParCDPCtorSpineView R body body2)
 (impossible : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ A val body))) (@OptionType.some Name n)) =>
 option_none_ne_some_type Name n (ParCDPCtorSpineView R (KExpr.let_ A val body) (instantiate body2 val2)) impossible)
  (fun (x y : KExpr) (step : iota_step (red_rec R) x y) (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (@OptionType.some Name n)) =>
 option_none_ne_some_type KExpr y (ParCDPCtorSpineView R x y)
  (Eq.trans (OptionType KExpr) (@OptionType.none KExpr) (iota_reduct (red_rec R) x) (@OptionType.some KExpr y)
   (Eq.symm (OptionType KExpr) (iota_reduct (red_rec R) x) (@OptionType.none KExpr)
    (ctor_metadata_iota_none R rigid n cm found x head)) step))
  (fun (x y : KExpr) (step : delta_step (red_def R) x y) (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (@OptionType.some Name n)) =>
 option_none_ne_some_type KExpr y (ParCDPCtorSpineView R x y)
  (Eq.trans (OptionType KExpr) (@OptionType.none KExpr) (delta_reduct (red_def R) x) (@OptionType.some KExpr y)
   (Eq.symm (OptionType KExpr) (delta_reduct (red_def R) x) (@OptionType.none KExpr)
    (ctor_metadata_delta_none R rigid n cm found x head)) step))
  (fun (A A2 val val2 body body2 : KExpr)
 (_hA : par_reduces_cdp R A A2)
 (_hval : par_reduces_cdp R val val2)
 (_hbody : par_reduces_cdp R body body2)
 (_ihA : @Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (@OptionType.some Name n) -> ParCDPCtorSpineView R A A2)
 (_ihval : @Eq (OptionType Name) (kexpr_const_name (kapp_fn val)) (@OptionType.some Name n) -> ParCDPCtorSpineView R val val2)
 (_ihbody : @Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (@OptionType.some Name n) -> ParCDPCtorSpineView R body body2)
 (impossible : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ A val body))) (@OptionType.some Name n)) =>
 option_none_ne_some_type Name n (ParCDPCtorSpineView R (KExpr.let_ A val body) (KExpr.let_ A2 val2 body2)) impossible)
  (fun (S : Name) (idx : Nat) (sub sub2 : KExpr) (_hs : par_reduces_cdp R sub sub2)
 (_ihs : @Eq (OptionType Name) (kexpr_const_name (kapp_fn sub)) (@OptionType.some Name n) -> ParCDPCtorSpineView R sub sub2)
 (impossible : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.proj S idx sub))) (@OptionType.some Name n)) =>
 option_none_ne_some_type Name n (ParCDPCtorSpineView R (KExpr.proj S idx sub) (KExpr.proj S idx sub2)) impossible)
(fun (S : Name) (idx : Nat) (sub result : KExpr)
 (_extract : @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx sub)) (@OptionType.some KExpr result))
 (impossible : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.proj S idx sub))) (@OptionType.some Name n)) =>
 option_none_ne_some_type Name n (ParCDPCtorSpineView R (KExpr.proj S idx sub) result) impossible)
  e e2 h head",
    ),
    DeclarationInput::Proof(
        "ctor_metadata_head_preserved_cdp",
        r"forall (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e e2 : KExpr) (h : par_reduces_cdp R e e2)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n)), @Eq KExpr (kapp_fn e2) (kapp_fn e)",
        r"fun (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e e2 : KExpr) (h : par_reduces_cdp R e e2)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n)) => @ParCDPCtorSpineView.rec R e e2
  (fun (_v : ParCDPCtorSpineView R e e2) => @Eq KExpr (kapp_fn e2) (kapp_fn e))
  (fun (same : @Eq KExpr (kapp_fn e2) (kapp_fn e)) (_args : par_reduces_cdp_list R (kapp_args e) (kapp_args e2)) => same)
  (ctor_metadata_spine_preserved_cdp R rigid n cm found e e2 h head)",
    ),
    DeclarationInput::Proof(
        "ctor_metadata_selected_position_cdp",
        r"forall (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e e2 : KExpr) (h : par_reduces_cdp R e e2)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n))
 (k : Nat) (a : KExpr) (C : Type)
 (selected : @Eq (OptionType KExpr) (list_head (list_drop k (kapp_args e))) (@OptionType.some KExpr a))
 (next : forall (b : KExpr), @Eq KExpr (kapp_fn e2) (kapp_fn e) ->
  @Eq (OptionType KExpr) (list_head (list_drop k (kapp_args e2))) (@OptionType.some KExpr b) ->
  par_reduces_cdp R a b -> C), C",
        r"fun (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e e2 : KExpr) (h : par_reduces_cdp R e e2)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n))
 (k : Nat) (a : KExpr) (C : Type)
 (selected : @Eq (OptionType KExpr) (list_head (list_drop k (kapp_args e))) (@OptionType.some KExpr a))
 (next : forall (b : KExpr), @Eq KExpr (kapp_fn e2) (kapp_fn e) ->
  @Eq (OptionType KExpr) (list_head (list_drop k (kapp_args e2))) (@OptionType.some KExpr b) ->
  par_reduces_cdp R a b -> C) => @ParCDPCtorSpineView.rec R e e2 (fun (_v : ParCDPCtorSpineView R e e2) => C)
  (fun (same : @Eq KExpr (kapp_fn e2) (kapp_fn e)) (args : par_reduces_cdp_list R (kapp_args e) (kapp_args e2)) =>
   par_reduces_cdp_list_head_some R (list_drop k (kapp_args e)) (list_drop k (kapp_args e2))
    (par_reduces_cdp_list_drop R k (kapp_args e) (kapp_args e2) args) a C selected
    (fun (b : KExpr)
     (found_b : @Eq (OptionType KExpr) (list_head (list_drop k (kapp_args e2))) (@OptionType.some KExpr b))
     (step : par_reduces_cdp R a b) => next b same found_b step))
  (ctor_metadata_spine_preserved_cdp R rigid n cm found e e2 h head)",
    ),
    DeclarationInput::Proof(
        "ctor_metadata_selected_field_cdp",
        r"forall (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e e2 : KExpr) (h : par_reduces_cdp R e e2)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n))
 (idx : Nat) (a : KExpr) (C : Type)
 (selected : @Eq (OptionType KExpr)
  (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args e))) (@OptionType.some KExpr a))
 (next : forall (b : KExpr), @Eq KExpr (kapp_fn e2) (kapp_fn e) ->
  @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args e2))) (@OptionType.some KExpr b) ->
  par_reduces_cdp R a b -> C), C",
        r"fun (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e e2 : KExpr) (h : par_reduces_cdp R e e2)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n))
 (idx : Nat) (a : KExpr) (C : Type)
 (selected : @Eq (OptionType KExpr)
  (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args e))) (@OptionType.some KExpr a))
 (next : forall (b : KExpr), @Eq KExpr (kapp_fn e2) (kapp_fn e) ->
  @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args e2))) (@OptionType.some KExpr b) ->
  par_reduces_cdp R a b -> C) => ctor_metadata_selected_position_cdp R rigid n cm found e e2 h head
  (Nat.add (kctor_num_params cm) idx) a C selected next",
    ),
    DeclarationInput::Proof(
        "ctor_metadata_spine_length_cdp",
        r"forall (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e e2 : KExpr) (h : par_reduces_cdp R e e2)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n)), @Eq Nat (list_length (kapp_args e)) (list_length (kapp_args e2))",
        r"fun (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e e2 : KExpr) (h : par_reduces_cdp R e e2)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n)) => @ParCDPCtorSpineView.rec R e e2
  (fun (_v : ParCDPCtorSpineView R e e2) => @Eq Nat (list_length (kapp_args e)) (list_length (kapp_args e2)))
  (fun (_same : @Eq KExpr (kapp_fn e2) (kapp_fn e)) (args : par_reduces_cdp_list R (kapp_args e) (kapp_args e2)) =>
   par_reduces_cdp_list_length R (kapp_args e) (kapp_args e2) args)
  (ctor_metadata_spine_preserved_cdp R rigid n cm found e e2 h head)",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_transport_cdp",
        r"forall (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (S : Name) (idx : Nat) (subject subject2 : KExpr) (step : par_reduces_cdp R subject subject2)
 (a : KExpr)
 (run : @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject)) (@OptionType.some KExpr a))
 (C : Type)
 (next : forall (b : KExpr),
  @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject2)) (@OptionType.some KExpr b) ->
  par_reduces_cdp R a b -> C), C",
        r"fun (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (S : Name) (idx : Nat) (subject subject2 : KExpr) (step : par_reduces_cdp R subject subject2)
 (a : KExpr)
 (run : @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject)) (@OptionType.some KExpr a))
 (C : Type)
 (next : forall (b : KExpr),
  @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject2)) (@OptionType.some KExpr b) ->
  par_reduces_cdp R a b -> C) => projection_post_whnf_field_inv_type R idx subject a C run
  (fun (n : Name) (cm : KCtorMeta)
   (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn subject)) (@OptionType.some Name n))
   (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
   (selected : @Eq (OptionType KExpr)
    (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject))) (@OptionType.some KExpr a)) =>
   ctor_metadata_selected_field_cdp R rigid n cm found subject subject2 step head idx a C selected
    (fun (b : KExpr) (same : @Eq KExpr (kapp_fn subject2) (kapp_fn subject))
     (selected2 : @Eq (OptionType KExpr)
      (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject2))) (@OptionType.some KExpr b))
     (field_step : par_reduces_cdp R a b) =>
     next b
      (projection_post_whnf_field_intro R idx subject2 n cm b
       (Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn subject2))
        (kexpr_const_name (kapp_fn subject)) (@OptionType.some Name n)
        (Eq.cong KExpr (OptionType Name) kexpr_const_name (kapp_fn subject2) (kapp_fn subject) same) head)
       found selected2) field_step))",
    ),
    DeclarationInput::Data(
        "cdp_prod_inner_projection",
        r"KExpr",
        r"KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value",
    ),
    DeclarationInput::Data(
        "cdp_prod_outer_before",
        r"KExpr",
        r"KExpr.app (KExpr.app ctor_spine_prod_prefix cdp_prod_inner_projection) (KExpr.app rfnz_succ rfnz_zero)",
    ),
    DeclarationInput::Proof(
        "cdp_prod_inner_extract",
        r"@Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env cdp_prod_inner_projection) (@OptionType.some KExpr rfnz_zero)",
        r"projection_post_whnf_prod_after_zero",
    ),
    DeclarationInput::Proof(
        "cdp_prod_inner_step",
        r"par_reduces_cdp the_red_env cdp_prod_inner_projection rfnz_zero",
        r"@par_reduces_cdp.projection_beta the_red_env kcre_prod_type_name Nat.zero kcre_witness_prod_value rfnz_zero cdp_prod_inner_extract",
    ),
    DeclarationInput::Proof(
        "cdp_prod_outer_step",
        r"par_reduces_cdp the_red_env cdp_prod_outer_before kcre_witness_prod_value",
        r"@par_reduces_cdp.app the_red_env
  (KExpr.app ctor_spine_prod_prefix cdp_prod_inner_projection) (KExpr.app ctor_spine_prod_prefix rfnz_zero)
  (KExpr.app rfnz_succ rfnz_zero) (KExpr.app rfnz_succ rfnz_zero)
  (@par_reduces_cdp.app the_red_env ctor_spine_prod_prefix ctor_spine_prod_prefix cdp_prod_inner_projection rfnz_zero
   (@par_reduces_cdp.refl the_red_env ctor_spine_prod_prefix) cdp_prod_inner_step)
  (@par_reduces_cdp.refl the_red_env (KExpr.app rfnz_succ rfnz_zero))",
    ),
    DeclarationInput::Proof(
        "cdp_prod_head_preserved",
        r"@Eq KExpr (kapp_fn kcre_witness_prod_value) (kapp_fn cdp_prod_outer_before)",
        r"ctor_metadata_head_preserved_cdp the_red_env reflected_ctor_metadata_rigid kcre_prod_mk_name kcre_prod_ctor_meta
  reflected_prod_ctor_lookup cdp_prod_outer_before kcre_witness_prod_value cdp_prod_outer_step
  (@Eq.refl (OptionType Name) (@OptionType.some Name kcre_prod_mk_name))",
    ),
    DeclarationInput::Proof(
        "cdp_prod_length_preserved",
        r"@Eq Nat (list_length (kapp_args cdp_prod_outer_before)) (list_length (kapp_args kcre_witness_prod_value))",
        r"ctor_metadata_spine_length_cdp the_red_env reflected_ctor_metadata_rigid kcre_prod_mk_name kcre_prod_ctor_meta
  reflected_prod_ctor_lookup cdp_prod_outer_before kcre_witness_prod_value cdp_prod_outer_step
  (@Eq.refl (OptionType Name) (@OptionType.some Name kcre_prod_mk_name))",
    ),
    DeclarationInput::Proof(
        "cdp_prod_selected_zero",
        r"par_reduces_cdp the_red_env cdp_prod_inner_projection rfnz_zero",
        r"ctor_metadata_selected_field_cdp the_red_env reflected_ctor_metadata_rigid
  kcre_prod_mk_name kcre_prod_ctor_meta reflected_prod_ctor_lookup cdp_prod_outer_before kcre_witness_prod_value cdp_prod_outer_step
  (@Eq.refl (OptionType Name) (@OptionType.some Name kcre_prod_mk_name)) Nat.zero cdp_prod_inner_projection
  (par_reduces_cdp the_red_env cdp_prod_inner_projection rfnz_zero)
  (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr cdp_prod_inner_projection))
  (fun (b : KExpr) (_same : @Eq KExpr (kapp_fn kcre_witness_prod_value) (kapp_fn cdp_prod_outer_before))
   (selected : @Eq (OptionType KExpr)
    (list_head (list_drop (Nat.add (kctor_num_params kcre_prod_ctor_meta) Nat.zero) (kapp_args kcre_witness_prod_value)))
    (@OptionType.some KExpr b))
   (step : par_reduces_cdp the_red_env cdp_prod_inner_projection b) =>
   Eq.substType KExpr (fun (v : KExpr) => par_reduces_cdp the_red_env cdp_prod_inner_projection v) b rfnz_zero
    (Eq.symm KExpr rfnz_zero b (option_some_inj KExpr rfnz_zero b selected)) step)",
    ),
    DeclarationInput::Proof(
        "cdp_prod_old_beta_embedded",
        r"par_reduces_cdp the_red_env ctor_spine_prod_redex rfnz_zero",
        r"par_reduces_cd_to_cdp the_red_env ctor_spine_prod_redex rfnz_zero ctor_spine_prod_beta",
    ),
    DeclarationInput::Proof(
        "cdp_prod_outer_extract",
        r"@Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero cdp_prod_outer_before))
 (@OptionType.some KExpr cdp_prod_inner_projection)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr cdp_prod_inner_projection)",
    ),
    DeclarationInput::Proof(
        "cdp_prod_selector_transport",
        r"par_reduces_cdp the_red_env cdp_prod_inner_projection rfnz_zero",
        r"projection_post_whnf_transport_cdp the_red_env reflected_ctor_metadata_rigid kcre_prod_type_name Nat.zero
  cdp_prod_outer_before kcre_witness_prod_value cdp_prod_outer_step cdp_prod_inner_projection cdp_prod_outer_extract
  (par_reduces_cdp the_red_env cdp_prod_inner_projection rfnz_zero)
  (fun (b : KExpr)
   (run2 : @Eq (OptionType KExpr)
    (projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value)) (@OptionType.some KExpr b))
   (step : par_reduces_cdp the_red_env cdp_prod_inner_projection b) =>
   Eq.substType KExpr (fun (v : KExpr) => par_reduces_cdp the_red_env cdp_prod_inner_projection v) b rfnz_zero
    (option_some_inj KExpr b rfnz_zero
     (Eq.trans (OptionType KExpr) (@OptionType.some KExpr b)
      (projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value))
      (@OptionType.some KExpr rfnz_zero)
      (Eq.symm (OptionType KExpr)
       (projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value))
       (@OptionType.some KExpr b) run2) projection_post_whnf_prod_after_zero)) step)",
    ),
];
