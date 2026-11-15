// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact checked projection_only cohort from projection-registration.RmczqJ.
//! Raw input types, values and carrier declarations are preserved verbatim.
//! This reduction evidence is not a typing or source-admission theorem.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Inductive(
        r"inductive projection_parallel (env : RedEnv) : KExpr → KExpr → Type
| refl : forall (e : KExpr), projection_parallel env e e
| app : forall (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), projection_parallel env f f' → projection_parallel env a a' → projection_parallel env (KExpr.app f a) (KExpr.app f' a')
| lam : forall (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr), projection_parallel env ty ty' → projection_parallel env body body' → projection_parallel env (KExpr.lam ty body) (KExpr.lam ty' body')
| pi : forall (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr), projection_parallel env dom dom' → projection_parallel env body body' → projection_parallel env (KExpr.pi dom body) (KExpr.pi dom' body')
| forall_ : forall (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr), projection_parallel env dom dom' → projection_parallel env body body' → projection_parallel env (KExpr.forall_ dom body) (KExpr.forall_ dom' body')
| let_cong : forall (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), projection_parallel env ty ty' → projection_parallel env val val' → projection_parallel env body body' → projection_parallel env (KExpr.let_ ty val body) (KExpr.let_ ty' val' body')
| proj : forall (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr), projection_parallel env sub sub' → projection_parallel env (KExpr.proj s i sub) (KExpr.proj s i sub')
| projection_beta : forall (S : Name) (idx : Nat) (subject result : KExpr),
 Eq (OptionType KExpr) (projection_post_whnf_reduct env (KExpr.proj S idx subject)) (OptionType.some KExpr result) ->
 projection_parallel env (KExpr.proj S idx subject) result",
    ),
    DeclarationInput::Inductive(
        r"inductive projection_parallel_list (R : RedEnv) : ListType KExpr -> ListType KExpr -> Type
| nil : projection_parallel_list R (ListType.nil KExpr) (ListType.nil KExpr)
| cons : forall (a b : KExpr) (xs ys : ListType KExpr),
 projection_parallel R a b -> projection_parallel_list R xs ys ->
 projection_parallel_list R (ListType.cons KExpr a xs) (ListType.cons KExpr b ys)",
    ),
    DeclarationInput::Proof(
        "projection_parallel_list_refl",
        r"forall (R : RedEnv) (xs : ListType KExpr), projection_parallel_list R xs xs",
        r"fun (R : RedEnv) (xs : ListType KExpr) => ListType.rec KExpr (fun (zs : ListType KExpr) => projection_parallel_list R zs zs)
  (projection_parallel_list.nil R)
  (fun (a : KExpr) (rest : ListType KExpr) (ih : projection_parallel_list R rest rest) =>
   projection_parallel_list.cons R a a rest rest (projection_parallel.refl R a) ih) xs",
    ),
    DeclarationInput::Proof(
        "projection_parallel_list_append",
        r"forall (R : RedEnv) (xs xs2 : ListType KExpr)
 (h : projection_parallel_list R xs xs2) (ys ys2 : ListType KExpr) (hy : projection_parallel_list R ys ys2), projection_parallel_list R (list_append xs ys) (list_append xs2 ys2)",
        r"fun (R : RedEnv) (xs xs2 : ListType KExpr)
 (h : projection_parallel_list R xs xs2) (ys ys2 : ListType KExpr) (hy : projection_parallel_list R ys ys2) => projection_parallel_list.rec R
  (fun (as1 as2 : ListType KExpr) (_h : projection_parallel_list R as1 as2) =>
   projection_parallel_list R (list_append as1 ys) (list_append as2 ys2)) hy
  (fun (a b : KExpr) (as1 as2 : ListType KExpr) (hab : projection_parallel R a b)
   (_ht : projection_parallel_list R as1 as2)
   (ih : projection_parallel_list R (list_append as1 ys) (list_append as2 ys2)) =>
   projection_parallel_list.cons R a b (list_append as1 ys) (list_append as2 ys2) hab ih) xs xs2 h",
    ),
    DeclarationInput::Proof(
        "projection_parallel_list_tail",
        r"forall (R : RedEnv) (xs ys : ListType KExpr)
 (h : projection_parallel_list R xs ys), projection_parallel_list R (list_tail xs) (list_tail ys)",
        r"fun (R : RedEnv) (xs ys : ListType KExpr)
 (h : projection_parallel_list R xs ys) => projection_parallel_list.rec R
  (fun (as1 as2 : ListType KExpr) (_h : projection_parallel_list R as1 as2) =>
   projection_parallel_list R (list_tail as1) (list_tail as2)) (projection_parallel_list.nil R)
  (fun (a b : KExpr) (as1 as2 : ListType KExpr) (_hab : projection_parallel R a b)
   (ht : projection_parallel_list R as1 as2)
   (_ih : projection_parallel_list R (list_tail as1) (list_tail as2)) => ht) xs ys h",
    ),
    DeclarationInput::Proof(
        "projection_parallel_list_drop",
        r"forall (R : RedEnv) (k : Nat) (xs ys : ListType KExpr)
 (h : projection_parallel_list R xs ys), projection_parallel_list R (list_drop k xs) (list_drop k ys)",
        r"fun (R : RedEnv) (k : Nat) (xs ys : ListType KExpr)
 (h : projection_parallel_list R xs ys) => Nat.rec
  (fun (n : Nat) => forall (as1 as2 : ListType KExpr), projection_parallel_list R as1 as2 ->
   projection_parallel_list R (list_drop n as1) (list_drop n as2))
  (fun (as1 as2 : ListType KExpr) (ht : projection_parallel_list R as1 as2) => ht)
  (fun (n : Nat)
   (ih : forall (as1 as2 : ListType KExpr), projection_parallel_list R as1 as2 ->
    projection_parallel_list R (list_drop n as1) (list_drop n as2))
   (as1 as2 : ListType KExpr) (ht : projection_parallel_list R as1 as2) =>
   ih (list_tail as1) (list_tail as2) (projection_parallel_list_tail R as1 as2 ht)) k xs ys h",
    ),
    DeclarationInput::Proof(
        "projection_parallel_list_head_some",
        r"forall (R : RedEnv) (xs ys : ListType KExpr)
 (h : projection_parallel_list R xs ys) (a : KExpr) (C : Type)
 (found : Eq (OptionType KExpr) (list_head xs) (OptionType.some KExpr a))
 (next : forall (b : KExpr), Eq (OptionType KExpr) (list_head ys) (OptionType.some KExpr b) -> projection_parallel R a b -> C), C",
        r"fun (R : RedEnv) (xs ys : ListType KExpr)
 (h : projection_parallel_list R xs ys) (a : KExpr) (C : Type)
 (found : Eq (OptionType KExpr) (list_head xs) (OptionType.some KExpr a))
 (next : forall (b : KExpr), Eq (OptionType KExpr) (list_head ys) (OptionType.some KExpr b) -> projection_parallel R a b -> C) => projection_parallel_list.rec R
  (fun (as1 as2 : ListType KExpr) (_h : projection_parallel_list R as1 as2) =>
   Eq (OptionType KExpr) (list_head as1) (OptionType.some KExpr a) ->
   (forall (b : KExpr), Eq (OptionType KExpr) (list_head as2) (OptionType.some KExpr b) -> projection_parallel R a b -> C) -> C)
  (fun (bad : Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.some KExpr a))
   (_next : forall (b : KExpr), Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.some KExpr b) -> projection_parallel R a b -> C) =>
   option_none_ne_some_type KExpr a C bad)
  (fun (x y : KExpr) (as1 as2 : ListType KExpr) (hxy : projection_parallel R x y)
   (_ht : projection_parallel_list R as1 as2)
   (_ih : Eq (OptionType KExpr) (list_head as1) (OptionType.some KExpr a) ->
    (forall (b : KExpr), Eq (OptionType KExpr) (list_head as2) (OptionType.some KExpr b) -> projection_parallel R a b -> C) -> C)
   (same : Eq (OptionType KExpr) (OptionType.some KExpr x) (OptionType.some KExpr a))
   (proceed : forall (b : KExpr), Eq (OptionType KExpr) (OptionType.some KExpr y) (OptionType.some KExpr b) -> projection_parallel R a b -> C) =>
   proceed y (Eq.refl (OptionType KExpr) (OptionType.some KExpr y))
    (Eq.substType KExpr (fun (z : KExpr) => projection_parallel R z y) x a (option_some_inj KExpr x a same) hxy))
  xs ys h found next",
    ),
    DeclarationInput::Inductive(
        r"inductive ProjectionConstSpineView (R : RedEnv) (e e2 : KExpr) : Type
| mk : Eq KExpr (kapp_fn e2) (kapp_fn e) ->
 projection_parallel_list R (kapp_args e) (kapp_args e2) -> ProjectionConstSpineView R e e2",
    ),
    DeclarationInput::Proof(
        "projection_parallel_list_length",
        r"forall (R : RedEnv) (xs ys : ListType KExpr) (h : projection_parallel_list R xs ys), Eq Nat (list_length xs) (list_length ys)",
        r"fun (R : RedEnv) (xs ys : ListType KExpr) (h : projection_parallel_list R xs ys) => projection_parallel_list.rec R
  (fun (as1 as2 : ListType KExpr) (_h : projection_parallel_list R as1 as2) => Eq Nat (list_length as1) (list_length as2))
  (Eq.refl Nat Nat.zero)
  (fun (a b : KExpr) (as1 as2 : ListType KExpr) (_hab : projection_parallel R a b)
   (_ht : projection_parallel_list R as1 as2) (ih : Eq Nat (list_length as1) (list_length as2)) =>
   Eq.cong Nat Nat Nat.succ (list_length as1) (list_length as2) ih) xs ys h",
    ),
    DeclarationInput::Proof(
        "projection_parallel_const_spine",
        r"forall (R : RedEnv)
 (n : Name)
 (e e2 : KExpr) (h : projection_parallel R e e2)
 (head : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name n)), ProjectionConstSpineView R e e2",
        r"fun (R : RedEnv)
 (n : Name)
 (e e2 : KExpr) (h : projection_parallel R e e2)
 (head : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name n)) => projection_parallel.rec R
(fun (x y : KExpr) (_h : projection_parallel R x y) =>
   Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (OptionType.some Name n) -> ProjectionConstSpineView R x y)
 (fun (x : KExpr) (_head : Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (OptionType.some Name n)) => ProjectionConstSpineView.mk R x x (Eq.refl KExpr (kapp_fn x)) (projection_parallel_list_refl R (kapp_args x)))
 (fun (f f2 a a2 : KExpr) (_hf : projection_parallel R f f2) (ha : projection_parallel R a a2)
 (ihf : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name n) -> ProjectionConstSpineView R f f2)
 (_iha : Eq (OptionType Name) (kexpr_const_name (kapp_fn a)) (OptionType.some Name n) -> ProjectionConstSpineView R a a2)
 (head : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name n)) =>
 ProjectionConstSpineView.rec R f f2
  (fun (_v : ProjectionConstSpineView R f f2) => ProjectionConstSpineView R (KExpr.app f a) (KExpr.app f2 a2))
  (fun (same : Eq KExpr (kapp_fn f2) (kapp_fn f))
   (args : projection_parallel_list R (kapp_args f) (kapp_args f2)) =>
   ProjectionConstSpineView.mk R (KExpr.app f a) (KExpr.app f2 a2) same
    (projection_parallel_list_append R (kapp_args f) (kapp_args f2) args
     (ListType.cons KExpr a (ListType.nil KExpr)) (ListType.cons KExpr a2 (ListType.nil KExpr))
     (projection_parallel_list.cons R a a2 (ListType.nil KExpr) (ListType.nil KExpr) ha (projection_parallel_list.nil R)))) (ihf head))
 (fun (A A2 body body2 : KExpr)
 (_hA : projection_parallel R A A2)
 (_hbody : projection_parallel R body body2)
 (_ihA : Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (OptionType.some Name n) -> ProjectionConstSpineView R A A2)
 (_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name n) -> ProjectionConstSpineView R body body2)
 (impossible : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam A body))) (OptionType.some Name n)) =>
 option_none_ne_some_type Name n (ProjectionConstSpineView R (KExpr.lam A body) (KExpr.lam A2 body2)) impossible)
 (fun (A A2 body body2 : KExpr)
 (_hA : projection_parallel R A A2)
 (_hbody : projection_parallel R body body2)
 (_ihA : Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (OptionType.some Name n) -> ProjectionConstSpineView R A A2)
 (_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name n) -> ProjectionConstSpineView R body body2)
 (impossible : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.pi A body))) (OptionType.some Name n)) =>
 option_none_ne_some_type Name n (ProjectionConstSpineView R (KExpr.pi A body) (KExpr.pi A2 body2)) impossible)
 (fun (A A2 body body2 : KExpr)
 (_hA : projection_parallel R A A2)
 (_hbody : projection_parallel R body body2)
 (_ihA : Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (OptionType.some Name n) -> ProjectionConstSpineView R A A2)
 (_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name n) -> ProjectionConstSpineView R body body2)
 (impossible : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.forall_ A body))) (OptionType.some Name n)) =>
 option_none_ne_some_type Name n (ProjectionConstSpineView R (KExpr.forall_ A body) (KExpr.forall_ A2 body2)) impossible)
 (fun (A A2 val val2 body body2 : KExpr)
 (_hA : projection_parallel R A A2)
 (_hval : projection_parallel R val val2)
 (_hbody : projection_parallel R body body2)
 (_ihA : Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (OptionType.some Name n) -> ProjectionConstSpineView R A A2)
 (_ihval : Eq (OptionType Name) (kexpr_const_name (kapp_fn val)) (OptionType.some Name n) -> ProjectionConstSpineView R val val2)
 (_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name n) -> ProjectionConstSpineView R body body2)
 (impossible : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ A val body))) (OptionType.some Name n)) =>
 option_none_ne_some_type Name n (ProjectionConstSpineView R (KExpr.let_ A val body) (KExpr.let_ A2 val2 body2)) impossible)
 (fun (S : Name) (idx : Nat) (sub sub2 : KExpr) (_hs : projection_parallel R sub sub2)
 (_ihs : Eq (OptionType Name) (kexpr_const_name (kapp_fn sub)) (OptionType.some Name n) -> ProjectionConstSpineView R sub sub2)
 (impossible : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.proj S idx sub))) (OptionType.some Name n)) =>
 option_none_ne_some_type Name n (ProjectionConstSpineView R (KExpr.proj S idx sub) (KExpr.proj S idx sub2)) impossible)
 (fun (S : Name) (idx : Nat) (sub result : KExpr)
 (_extract : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx sub)) (OptionType.some KExpr result))
 (impossible : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.proj S idx sub))) (OptionType.some Name n)) =>
 option_none_ne_some_type Name n (ProjectionConstSpineView R (KExpr.proj S idx sub) result) impossible)
 e e2 h head",
    ),
    DeclarationInput::Proof(
        "projection_parallel_selected_position",
        r"forall (R : RedEnv)
 (n : Name)
 (e e2 : KExpr) (h : projection_parallel R e e2)
 (head : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name n))
 (k : Nat) (a : KExpr) (C : Type)
 (selected : Eq (OptionType KExpr) (list_head (list_drop k (kapp_args e))) (OptionType.some KExpr a))
 (next : forall (b : KExpr), Eq KExpr (kapp_fn e2) (kapp_fn e) ->
  Eq (OptionType KExpr) (list_head (list_drop k (kapp_args e2))) (OptionType.some KExpr b) ->
  projection_parallel R a b -> C), C",
        r"fun (R : RedEnv)
 (n : Name)
 (e e2 : KExpr) (h : projection_parallel R e e2)
 (head : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name n))
 (k : Nat) (a : KExpr) (C : Type)
 (selected : Eq (OptionType KExpr) (list_head (list_drop k (kapp_args e))) (OptionType.some KExpr a))
 (next : forall (b : KExpr), Eq KExpr (kapp_fn e2) (kapp_fn e) ->
  Eq (OptionType KExpr) (list_head (list_drop k (kapp_args e2))) (OptionType.some KExpr b) ->
  projection_parallel R a b -> C) => ProjectionConstSpineView.rec R e e2 (fun (_v : ProjectionConstSpineView R e e2) => C)
  (fun (same : Eq KExpr (kapp_fn e2) (kapp_fn e)) (args : projection_parallel_list R (kapp_args e) (kapp_args e2)) =>
   projection_parallel_list_head_some R (list_drop k (kapp_args e)) (list_drop k (kapp_args e2))
    (projection_parallel_list_drop R k (kapp_args e) (kapp_args e2) args) a C selected
    (fun (b : KExpr)
     (found_b : Eq (OptionType KExpr) (list_head (list_drop k (kapp_args e2))) (OptionType.some KExpr b))
     (step : projection_parallel R a b) => next b same found_b step))
  (projection_parallel_const_spine R n e e2 h head)",
    ),
    DeclarationInput::Proof(
        "projection_parallel_selector_transport",
        r"forall (R : RedEnv)
 (S : Name) (idx : Nat) (subject subject2 : KExpr) (step : projection_parallel R subject subject2)
 (a : KExpr)
 (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject)) (OptionType.some KExpr a))
 (C : Type)
 (next : forall (b : KExpr),
  Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject2)) (OptionType.some KExpr b) ->
  projection_parallel R a b -> C), C",
        r"fun (R : RedEnv)
 (S : Name) (idx : Nat) (subject subject2 : KExpr) (step : projection_parallel R subject subject2)
 (a : KExpr)
 (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject)) (OptionType.some KExpr a))
 (C : Type)
 (next : forall (b : KExpr),
  Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject2)) (OptionType.some KExpr b) ->
  projection_parallel R a b -> C) => projection_post_whnf_field_inv_type R idx subject a C run
  (fun (n : Name) (cm : KCtorMeta)
   (head : Eq (OptionType Name) (kexpr_const_name (kapp_fn subject)) (OptionType.some Name n))
   (found : Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (OptionType.some KCtorMeta cm))
   (selected : Eq (OptionType KExpr)
    (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject))) (OptionType.some KExpr a)) =>
   projection_parallel_selected_position R n subject subject2 step head (Nat.add (kctor_num_params cm) idx) a C selected
    (fun (b : KExpr) (same : Eq KExpr (kapp_fn subject2) (kapp_fn subject))
     (selected2 : Eq (OptionType KExpr)
      (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject2))) (OptionType.some KExpr b))
     (field_step : projection_parallel R a b) =>
     next b
      (projection_post_whnf_field_intro R idx subject2 n cm b
       (Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn subject2))
        (kexpr_const_name (kapp_fn subject)) (OptionType.some Name n)
        (Eq.cong KExpr (OptionType Name) kexpr_const_name (kapp_fn subject2) (kapp_fn subject) same) head)
       found selected2) field_step))",
    ),
    DeclarationInput::Proof(
        "projection_parallel_to_cdp",
        r"forall (R : RedEnv) (e r : KExpr) (h : projection_parallel R e r), par_reduces_cdp R e r",
        r"fun (R : RedEnv) (e r : KExpr) (h : projection_parallel R e r) => projection_parallel.rec R (fun (x y : KExpr) (_h : projection_parallel R x y) => par_reduces_cdp R x y)
 (fun (x : KExpr) => par_reduces_cdp.refl R x)
 (fun (f f2 a a2 : KExpr) (hf : projection_parallel R f f2) (ha : projection_parallel R a a2) (ihf : par_reduces_cdp R f f2) (iha : par_reduces_cdp R a a2) => par_reduces_cdp.app R f f2 a a2 ihf iha)
 (fun (A A2 b b2 : KExpr) (hA : projection_parallel R A A2) (hb : projection_parallel R b b2) (ihA : par_reduces_cdp R A A2) (ihb : par_reduces_cdp R b b2) => par_reduces_cdp.lam R A A2 b b2 ihA ihb)
 (fun (A A2 b b2 : KExpr) (hA : projection_parallel R A A2) (hb : projection_parallel R b b2) (ihA : par_reduces_cdp R A A2) (ihb : par_reduces_cdp R b b2) => par_reduces_cdp.pi R A A2 b b2 ihA ihb)
 (fun (A A2 b b2 : KExpr) (hA : projection_parallel R A A2) (hb : projection_parallel R b b2) (ihA : par_reduces_cdp R A A2) (ihb : par_reduces_cdp R b b2) => par_reduces_cdp.forall_ R A A2 b b2 ihA ihb)
 (fun (A A2 v v2 b b2 : KExpr) (hA : projection_parallel R A A2) (hv : projection_parallel R v v2) (hb : projection_parallel R b b2) (ihA : par_reduces_cdp R A A2) (ihv : par_reduces_cdp R v v2) (ihb : par_reduces_cdp R b b2) => par_reduces_cdp.let_cong R A A2 v v2 b b2 ihA ihv ihb)
 (fun (S : Name) (idx : Nat) (sub sub2 : KExpr) (hsub : projection_parallel R sub sub2) (ihsub : par_reduces_cdp R sub sub2) => par_reduces_cdp.proj R S idx sub sub2 ihsub)
 (fun (S : Name) (idx : Nat) (sub out : KExpr) (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx sub)) (OptionType.some KExpr out)) => par_reduces_cdp.projection_beta R S idx sub out run) e r h",
    ),
    DeclarationInput::Inductive(
        r"inductive ProjectionParallelJoin (R : RedEnv) (a b : KExpr) : Type
| mk : forall (c : KExpr), projection_parallel R a c -> projection_parallel R b c -> ProjectionParallelJoin R a b",
    ),
    DeclarationInput::Proof(
        "projection_parallel_join_symm",
        r"forall (R : RedEnv) (a b : KExpr) (h : ProjectionParallelJoin R a b), ProjectionParallelJoin R b a",
        r"fun (R : RedEnv) (a b : KExpr) (h : ProjectionParallelJoin R a b) => ProjectionParallelJoin.rec R a b (fun (_h : ProjectionParallelJoin R a b) => ProjectionParallelJoin R b a)
  (fun (c : KExpr) (ac : projection_parallel R a c) (bc : projection_parallel R b c) => ProjectionParallelJoin.mk R b a c bc ac) h",
    ),
    DeclarationInput::Proof(
        "projection_parallel_join_app",
        r"forall (R : RedEnv) (f1 f2 a1 a2 : KExpr) (hf : ProjectionParallelJoin R f1 f2) (ha : ProjectionParallelJoin R a1 a2), ProjectionParallelJoin R (KExpr.app f1 a1) (KExpr.app f2 a2)",
        r"fun (R : RedEnv) (f1 f2 a1 a2 : KExpr) (hf : ProjectionParallelJoin R f1 f2) (ha : ProjectionParallelJoin R a1 a2) => ProjectionParallelJoin.rec R f1 f2 (fun (_h : ProjectionParallelJoin R f1 f2) => ProjectionParallelJoin R (KExpr.app f1 a1) (KExpr.app f2 a2)) (fun (f3 : KExpr) (f13 : projection_parallel R f1 f3) (f23 : projection_parallel R f2 f3) => ProjectionParallelJoin.rec R a1 a2 (fun (_h : ProjectionParallelJoin R a1 a2) => ProjectionParallelJoin R (KExpr.app f1 a1) (KExpr.app f2 a2)) (fun (a3 : KExpr) (a13 : projection_parallel R a1 a3) (a23 : projection_parallel R a2 a3) => ProjectionParallelJoin.mk R (KExpr.app f1 a1) (KExpr.app f2 a2) (KExpr.app f3 a3) (projection_parallel.app R f1 f3 a1 a3 f13 a13) (projection_parallel.app R f2 f3 a2 a3 f23 a23)) ha) hf",
    ),
    DeclarationInput::Proof(
        "projection_parallel_join_lam",
        r"forall (R : RedEnv) (A1 A2 b1 b2 : KExpr) (hA : ProjectionParallelJoin R A1 A2) (hb : ProjectionParallelJoin R b1 b2), ProjectionParallelJoin R (KExpr.lam A1 b1) (KExpr.lam A2 b2)",
        r"fun (R : RedEnv) (A1 A2 b1 b2 : KExpr) (hA : ProjectionParallelJoin R A1 A2) (hb : ProjectionParallelJoin R b1 b2) => ProjectionParallelJoin.rec R A1 A2 (fun (_h : ProjectionParallelJoin R A1 A2) => ProjectionParallelJoin R (KExpr.lam A1 b1) (KExpr.lam A2 b2)) (fun (A3 : KExpr) (A13 : projection_parallel R A1 A3) (A23 : projection_parallel R A2 A3) => ProjectionParallelJoin.rec R b1 b2 (fun (_h : ProjectionParallelJoin R b1 b2) => ProjectionParallelJoin R (KExpr.lam A1 b1) (KExpr.lam A2 b2)) (fun (b3 : KExpr) (b13 : projection_parallel R b1 b3) (b23 : projection_parallel R b2 b3) => ProjectionParallelJoin.mk R (KExpr.lam A1 b1) (KExpr.lam A2 b2) (KExpr.lam A3 b3) (projection_parallel.lam R A1 A3 b1 b3 A13 b13) (projection_parallel.lam R A2 A3 b2 b3 A23 b23)) hb) hA",
    ),
    DeclarationInput::Proof(
        "projection_parallel_join_pi",
        r"forall (R : RedEnv) (A1 A2 b1 b2 : KExpr) (hA : ProjectionParallelJoin R A1 A2) (hb : ProjectionParallelJoin R b1 b2), ProjectionParallelJoin R (KExpr.pi A1 b1) (KExpr.pi A2 b2)",
        r"fun (R : RedEnv) (A1 A2 b1 b2 : KExpr) (hA : ProjectionParallelJoin R A1 A2) (hb : ProjectionParallelJoin R b1 b2) => ProjectionParallelJoin.rec R A1 A2 (fun (_h : ProjectionParallelJoin R A1 A2) => ProjectionParallelJoin R (KExpr.pi A1 b1) (KExpr.pi A2 b2)) (fun (A3 : KExpr) (A13 : projection_parallel R A1 A3) (A23 : projection_parallel R A2 A3) => ProjectionParallelJoin.rec R b1 b2 (fun (_h : ProjectionParallelJoin R b1 b2) => ProjectionParallelJoin R (KExpr.pi A1 b1) (KExpr.pi A2 b2)) (fun (b3 : KExpr) (b13 : projection_parallel R b1 b3) (b23 : projection_parallel R b2 b3) => ProjectionParallelJoin.mk R (KExpr.pi A1 b1) (KExpr.pi A2 b2) (KExpr.pi A3 b3) (projection_parallel.pi R A1 A3 b1 b3 A13 b13) (projection_parallel.pi R A2 A3 b2 b3 A23 b23)) hb) hA",
    ),
    DeclarationInput::Proof(
        "projection_parallel_join_forall_",
        r"forall (R : RedEnv) (A1 A2 b1 b2 : KExpr) (hA : ProjectionParallelJoin R A1 A2) (hb : ProjectionParallelJoin R b1 b2), ProjectionParallelJoin R (KExpr.forall_ A1 b1) (KExpr.forall_ A2 b2)",
        r"fun (R : RedEnv) (A1 A2 b1 b2 : KExpr) (hA : ProjectionParallelJoin R A1 A2) (hb : ProjectionParallelJoin R b1 b2) => ProjectionParallelJoin.rec R A1 A2 (fun (_h : ProjectionParallelJoin R A1 A2) => ProjectionParallelJoin R (KExpr.forall_ A1 b1) (KExpr.forall_ A2 b2)) (fun (A3 : KExpr) (A13 : projection_parallel R A1 A3) (A23 : projection_parallel R A2 A3) => ProjectionParallelJoin.rec R b1 b2 (fun (_h : ProjectionParallelJoin R b1 b2) => ProjectionParallelJoin R (KExpr.forall_ A1 b1) (KExpr.forall_ A2 b2)) (fun (b3 : KExpr) (b13 : projection_parallel R b1 b3) (b23 : projection_parallel R b2 b3) => ProjectionParallelJoin.mk R (KExpr.forall_ A1 b1) (KExpr.forall_ A2 b2) (KExpr.forall_ A3 b3) (projection_parallel.forall_ R A1 A3 b1 b3 A13 b13) (projection_parallel.forall_ R A2 A3 b2 b3 A23 b23)) hb) hA",
    ),
    DeclarationInput::Proof(
        "projection_parallel_join_let_cong",
        r"forall (R : RedEnv) (A1 A2 v1 v2 b1 b2 : KExpr) (hA : ProjectionParallelJoin R A1 A2) (hv : ProjectionParallelJoin R v1 v2) (hb : ProjectionParallelJoin R b1 b2), ProjectionParallelJoin R (KExpr.let_ A1 v1 b1) (KExpr.let_ A2 v2 b2)",
        r"fun (R : RedEnv) (A1 A2 v1 v2 b1 b2 : KExpr) (hA : ProjectionParallelJoin R A1 A2) (hv : ProjectionParallelJoin R v1 v2) (hb : ProjectionParallelJoin R b1 b2) => ProjectionParallelJoin.rec R A1 A2 (fun (_h : ProjectionParallelJoin R A1 A2) => ProjectionParallelJoin R (KExpr.let_ A1 v1 b1) (KExpr.let_ A2 v2 b2)) (fun (A3 : KExpr) (A13 : projection_parallel R A1 A3) (A23 : projection_parallel R A2 A3) => ProjectionParallelJoin.rec R v1 v2 (fun (_h : ProjectionParallelJoin R v1 v2) => ProjectionParallelJoin R (KExpr.let_ A1 v1 b1) (KExpr.let_ A2 v2 b2)) (fun (v3 : KExpr) (v13 : projection_parallel R v1 v3) (v23 : projection_parallel R v2 v3) => ProjectionParallelJoin.rec R b1 b2 (fun (_h : ProjectionParallelJoin R b1 b2) => ProjectionParallelJoin R (KExpr.let_ A1 v1 b1) (KExpr.let_ A2 v2 b2)) (fun (b3 : KExpr) (b13 : projection_parallel R b1 b3) (b23 : projection_parallel R b2 b3) => ProjectionParallelJoin.mk R (KExpr.let_ A1 v1 b1) (KExpr.let_ A2 v2 b2) (KExpr.let_ A3 v3 b3) (projection_parallel.let_cong R A1 A3 v1 v3 b1 b3 A13 v13 b13) (projection_parallel.let_cong R A2 A3 v2 v3 b2 b3 A23 v23 b23)) hb) hv) hA",
    ),
    DeclarationInput::Proof(
        "projection_parallel_join_proj",
        r"forall (R : RedEnv) (S : Name) (idx : Nat) (sub1 sub2 : KExpr) (hsub : ProjectionParallelJoin R sub1 sub2), ProjectionParallelJoin R (KExpr.proj S idx sub1) (KExpr.proj S idx sub2)",
        r"fun (R : RedEnv) (S : Name) (idx : Nat) (sub1 sub2 : KExpr) (hsub : ProjectionParallelJoin R sub1 sub2) => ProjectionParallelJoin.rec R sub1 sub2 (fun (_h : ProjectionParallelJoin R sub1 sub2) => ProjectionParallelJoin R (KExpr.proj S idx sub1) (KExpr.proj S idx sub2)) (fun (sub3 : KExpr) (sub13 : projection_parallel R sub1 sub3) (sub23 : projection_parallel R sub2 sub3) => ProjectionParallelJoin.mk R (KExpr.proj S idx sub1) (KExpr.proj S idx sub2) (KExpr.proj S idx sub3) (projection_parallel.proj R S idx sub1 sub3 sub13) (projection_parallel.proj R S idx sub2 sub3 sub23)) hsub",
    ),
    DeclarationInput::Proof(
        "projection_parallel_inv_app",
        r"forall (R : RedEnv)  (f0 f1 out : KExpr) (C : Type) (h : projection_parallel R (KExpr.app f0 f1) out) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr out (KExpr.app g0 g1) -> C), C",
        r"fun (R : RedEnv)  (f0 f1 out : KExpr) (C : Type) (h : projection_parallel R (KExpr.app f0 f1) out) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr out (KExpr.app g0 g1) -> C) => projection_parallel.rec R (fun (x y : KExpr) (_h : projection_parallel R x y) => Eq KExpr x (KExpr.app f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr y (KExpr.app g0 g1) -> C) -> C)
 (fun (x : KExpr) (same : Eq KExpr x (KExpr.app f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr x (KExpr.app g0 g1) -> C)  => next f0 f1 (projection_parallel.refl R f0) (projection_parallel.refl R f1) same)
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (_ih0 : Eq KExpr a0 (KExpr.app f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b0 (KExpr.app g0 g1) -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.app f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b1 (KExpr.app g0 g1) -> C) -> C) (same : Eq KExpr (KExpr.app a0 a1) (KExpr.app f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr (KExpr.app b0 b1) (KExpr.app g0 g1) -> C)  => next b0 b1 (Eq.substType KExpr (fun (z : KExpr) => projection_parallel R z b0) a0 f0 (app_inj_fst a0 a1 f0 f1 same) h0) (Eq.substType KExpr (fun (z : KExpr) => projection_parallel R z b1) a1 f1 (app_inj_snd a0 a1 f0 f1 same) h1) (Eq.refl KExpr (KExpr.app b0 b1)))
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (_ih0 : Eq KExpr a0 (KExpr.app f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b0 (KExpr.app g0 g1) -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.app f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b1 (KExpr.app g0 g1) -> C) -> C) (same : Eq KExpr (KExpr.lam a0 a1) (KExpr.app f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr (KExpr.lam b0 b1) (KExpr.app g0 g1) -> C)  => kexpr_discr_t C (KExpr.lam a0 a1) (KExpr.app f0 f1) same (Eq.refl Bool Bool.false))
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (_ih0 : Eq KExpr a0 (KExpr.app f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b0 (KExpr.app g0 g1) -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.app f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b1 (KExpr.app g0 g1) -> C) -> C) (same : Eq KExpr (KExpr.pi a0 a1) (KExpr.app f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr (KExpr.pi b0 b1) (KExpr.app g0 g1) -> C)  => kexpr_discr_t C (KExpr.pi a0 a1) (KExpr.app f0 f1) same (Eq.refl Bool Bool.false))
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (_ih0 : Eq KExpr a0 (KExpr.app f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b0 (KExpr.app g0 g1) -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.app f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b1 (KExpr.app g0 g1) -> C) -> C) (same : Eq KExpr (KExpr.forall_ a0 a1) (KExpr.app f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr (KExpr.forall_ b0 b1) (KExpr.app g0 g1) -> C)  => kexpr_discr_t C (KExpr.forall_ a0 a1) (KExpr.app f0 f1) same (Eq.refl Bool Bool.false))
 (fun (a0 b0 a1 b1 a2 b2 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (h2 : projection_parallel R a2 b2) (_ih0 : Eq KExpr a0 (KExpr.app f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b0 (KExpr.app g0 g1) -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.app f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b1 (KExpr.app g0 g1) -> C) -> C) (_ih2 : Eq KExpr a2 (KExpr.app f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b2 (KExpr.app g0 g1) -> C) -> C) (same : Eq KExpr (KExpr.let_ a0 a1 a2) (KExpr.app f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr (KExpr.let_ b0 b1 b2) (KExpr.app g0 g1) -> C)  => kexpr_discr_t C (KExpr.let_ a0 a1 a2) (KExpr.app f0 f1) same (Eq.refl Bool Bool.false))
 (fun (N : Name) (I : Nat) (a0 b0 : KExpr) (h0 : projection_parallel R a0 b0) (_ih0 : Eq KExpr a0 (KExpr.app f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b0 (KExpr.app g0 g1) -> C) -> C) (same : Eq KExpr (KExpr.proj N I a0) (KExpr.app f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr (KExpr.proj N I b0) (KExpr.app g0 g1) -> C)  => kexpr_discr_t C (KExpr.proj N I a0) (KExpr.app f0 f1) same (Eq.refl Bool Bool.false))
 (fun (N : Name) (I : Nat) (sub rootOut : KExpr) (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj N I sub)) (OptionType.some KExpr rootOut)) (same : Eq KExpr (KExpr.proj N I sub) (KExpr.app f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr rootOut (KExpr.app g0 g1) -> C)  => kexpr_discr_t C (KExpr.proj N I sub) (KExpr.app f0 f1) same (Eq.refl Bool Bool.false)) (KExpr.app f0 f1) out h (Eq.refl KExpr (KExpr.app f0 f1)) next",
    ),
    DeclarationInput::Proof(
        "projection_parallel_inv_lam",
        r"forall (R : RedEnv)  (f0 f1 out : KExpr) (C : Type) (h : projection_parallel R (KExpr.lam f0 f1) out) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr out (KExpr.lam g0 g1) -> C), C",
        r"fun (R : RedEnv)  (f0 f1 out : KExpr) (C : Type) (h : projection_parallel R (KExpr.lam f0 f1) out) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr out (KExpr.lam g0 g1) -> C) => projection_parallel.rec R (fun (x y : KExpr) (_h : projection_parallel R x y) => Eq KExpr x (KExpr.lam f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr y (KExpr.lam g0 g1) -> C) -> C)
 (fun (x : KExpr) (same : Eq KExpr x (KExpr.lam f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr x (KExpr.lam g0 g1) -> C)  => next f0 f1 (projection_parallel.refl R f0) (projection_parallel.refl R f1) same)
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (_ih0 : Eq KExpr a0 (KExpr.lam f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b0 (KExpr.lam g0 g1) -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.lam f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b1 (KExpr.lam g0 g1) -> C) -> C) (same : Eq KExpr (KExpr.app a0 a1) (KExpr.lam f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr (KExpr.app b0 b1) (KExpr.lam g0 g1) -> C)  => kexpr_discr_t C (KExpr.app a0 a1) (KExpr.lam f0 f1) same (Eq.refl Bool Bool.false))
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (_ih0 : Eq KExpr a0 (KExpr.lam f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b0 (KExpr.lam g0 g1) -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.lam f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b1 (KExpr.lam g0 g1) -> C) -> C) (same : Eq KExpr (KExpr.lam a0 a1) (KExpr.lam f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr (KExpr.lam b0 b1) (KExpr.lam g0 g1) -> C)  => next b0 b1 (Eq.substType KExpr (fun (z : KExpr) => projection_parallel R z b0) a0 f0 (lam_inj_fst a0 a1 f0 f1 same) h0) (Eq.substType KExpr (fun (z : KExpr) => projection_parallel R z b1) a1 f1 (lam_inj_snd a0 a1 f0 f1 same) h1) (Eq.refl KExpr (KExpr.lam b0 b1)))
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (_ih0 : Eq KExpr a0 (KExpr.lam f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b0 (KExpr.lam g0 g1) -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.lam f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b1 (KExpr.lam g0 g1) -> C) -> C) (same : Eq KExpr (KExpr.pi a0 a1) (KExpr.lam f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr (KExpr.pi b0 b1) (KExpr.lam g0 g1) -> C)  => kexpr_discr_t C (KExpr.pi a0 a1) (KExpr.lam f0 f1) same (Eq.refl Bool Bool.false))
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (_ih0 : Eq KExpr a0 (KExpr.lam f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b0 (KExpr.lam g0 g1) -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.lam f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b1 (KExpr.lam g0 g1) -> C) -> C) (same : Eq KExpr (KExpr.forall_ a0 a1) (KExpr.lam f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr (KExpr.forall_ b0 b1) (KExpr.lam g0 g1) -> C)  => kexpr_discr_t C (KExpr.forall_ a0 a1) (KExpr.lam f0 f1) same (Eq.refl Bool Bool.false))
 (fun (a0 b0 a1 b1 a2 b2 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (h2 : projection_parallel R a2 b2) (_ih0 : Eq KExpr a0 (KExpr.lam f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b0 (KExpr.lam g0 g1) -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.lam f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b1 (KExpr.lam g0 g1) -> C) -> C) (_ih2 : Eq KExpr a2 (KExpr.lam f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b2 (KExpr.lam g0 g1) -> C) -> C) (same : Eq KExpr (KExpr.let_ a0 a1 a2) (KExpr.lam f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr (KExpr.let_ b0 b1 b2) (KExpr.lam g0 g1) -> C)  => kexpr_discr_t C (KExpr.let_ a0 a1 a2) (KExpr.lam f0 f1) same (Eq.refl Bool Bool.false))
 (fun (N : Name) (I : Nat) (a0 b0 : KExpr) (h0 : projection_parallel R a0 b0) (_ih0 : Eq KExpr a0 (KExpr.lam f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b0 (KExpr.lam g0 g1) -> C) -> C) (same : Eq KExpr (KExpr.proj N I a0) (KExpr.lam f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr (KExpr.proj N I b0) (KExpr.lam g0 g1) -> C)  => kexpr_discr_t C (KExpr.proj N I a0) (KExpr.lam f0 f1) same (Eq.refl Bool Bool.false))
 (fun (N : Name) (I : Nat) (sub rootOut : KExpr) (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj N I sub)) (OptionType.some KExpr rootOut)) (same : Eq KExpr (KExpr.proj N I sub) (KExpr.lam f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr rootOut (KExpr.lam g0 g1) -> C)  => kexpr_discr_t C (KExpr.proj N I sub) (KExpr.lam f0 f1) same (Eq.refl Bool Bool.false)) (KExpr.lam f0 f1) out h (Eq.refl KExpr (KExpr.lam f0 f1)) next",
    ),
    DeclarationInput::Proof(
        "projection_parallel_inv_pi",
        r"forall (R : RedEnv)  (f0 f1 out : KExpr) (C : Type) (h : projection_parallel R (KExpr.pi f0 f1) out) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr out (KExpr.pi g0 g1) -> C), C",
        r"fun (R : RedEnv)  (f0 f1 out : KExpr) (C : Type) (h : projection_parallel R (KExpr.pi f0 f1) out) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr out (KExpr.pi g0 g1) -> C) => projection_parallel.rec R (fun (x y : KExpr) (_h : projection_parallel R x y) => Eq KExpr x (KExpr.pi f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr y (KExpr.pi g0 g1) -> C) -> C)
 (fun (x : KExpr) (same : Eq KExpr x (KExpr.pi f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr x (KExpr.pi g0 g1) -> C)  => next f0 f1 (projection_parallel.refl R f0) (projection_parallel.refl R f1) same)
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (_ih0 : Eq KExpr a0 (KExpr.pi f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b0 (KExpr.pi g0 g1) -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.pi f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b1 (KExpr.pi g0 g1) -> C) -> C) (same : Eq KExpr (KExpr.app a0 a1) (KExpr.pi f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr (KExpr.app b0 b1) (KExpr.pi g0 g1) -> C)  => kexpr_discr_t C (KExpr.app a0 a1) (KExpr.pi f0 f1) same (Eq.refl Bool Bool.false))
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (_ih0 : Eq KExpr a0 (KExpr.pi f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b0 (KExpr.pi g0 g1) -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.pi f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b1 (KExpr.pi g0 g1) -> C) -> C) (same : Eq KExpr (KExpr.lam a0 a1) (KExpr.pi f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr (KExpr.lam b0 b1) (KExpr.pi g0 g1) -> C)  => kexpr_discr_t C (KExpr.lam a0 a1) (KExpr.pi f0 f1) same (Eq.refl Bool Bool.false))
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (_ih0 : Eq KExpr a0 (KExpr.pi f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b0 (KExpr.pi g0 g1) -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.pi f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b1 (KExpr.pi g0 g1) -> C) -> C) (same : Eq KExpr (KExpr.pi a0 a1) (KExpr.pi f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr (KExpr.pi b0 b1) (KExpr.pi g0 g1) -> C)  => next b0 b1 (Eq.substType KExpr (fun (z : KExpr) => projection_parallel R z b0) a0 f0 (pi_inj_fst a0 a1 f0 f1 same) h0) (Eq.substType KExpr (fun (z : KExpr) => projection_parallel R z b1) a1 f1 (pi_inj_snd a0 a1 f0 f1 same) h1) (Eq.refl KExpr (KExpr.pi b0 b1)))
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (_ih0 : Eq KExpr a0 (KExpr.pi f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b0 (KExpr.pi g0 g1) -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.pi f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b1 (KExpr.pi g0 g1) -> C) -> C) (same : Eq KExpr (KExpr.forall_ a0 a1) (KExpr.pi f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr (KExpr.forall_ b0 b1) (KExpr.pi g0 g1) -> C)  => next b0 b1 (Eq.substType KExpr (fun (z : KExpr) => projection_parallel R z b0) a0 f0 (pi_inj_fst a0 a1 f0 f1 same) h0) (Eq.substType KExpr (fun (z : KExpr) => projection_parallel R z b1) a1 f1 (pi_inj_snd a0 a1 f0 f1 same) h1) (Eq.refl KExpr (KExpr.forall_ b0 b1)))
 (fun (a0 b0 a1 b1 a2 b2 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (h2 : projection_parallel R a2 b2) (_ih0 : Eq KExpr a0 (KExpr.pi f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b0 (KExpr.pi g0 g1) -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.pi f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b1 (KExpr.pi g0 g1) -> C) -> C) (_ih2 : Eq KExpr a2 (KExpr.pi f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b2 (KExpr.pi g0 g1) -> C) -> C) (same : Eq KExpr (KExpr.let_ a0 a1 a2) (KExpr.pi f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr (KExpr.let_ b0 b1 b2) (KExpr.pi g0 g1) -> C)  => kexpr_discr_t C (KExpr.let_ a0 a1 a2) (KExpr.pi f0 f1) same (Eq.refl Bool Bool.false))
 (fun (N : Name) (I : Nat) (a0 b0 : KExpr) (h0 : projection_parallel R a0 b0) (_ih0 : Eq KExpr a0 (KExpr.pi f0 f1) -> (forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr b0 (KExpr.pi g0 g1) -> C) -> C) (same : Eq KExpr (KExpr.proj N I a0) (KExpr.pi f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr (KExpr.proj N I b0) (KExpr.pi g0 g1) -> C)  => kexpr_discr_t C (KExpr.proj N I a0) (KExpr.pi f0 f1) same (Eq.refl Bool Bool.false))
 (fun (N : Name) (I : Nat) (sub rootOut : KExpr) (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj N I sub)) (OptionType.some KExpr rootOut)) (same : Eq KExpr (KExpr.proj N I sub) (KExpr.pi f0 f1)) (next : forall (g0 g1 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> Eq KExpr rootOut (KExpr.pi g0 g1) -> C)  => kexpr_discr_t C (KExpr.proj N I sub) (KExpr.pi f0 f1) same (Eq.refl Bool Bool.false)) (KExpr.pi f0 f1) out h (Eq.refl KExpr (KExpr.pi f0 f1)) next",
    ),
    DeclarationInput::Proof(
        "projection_parallel_inv_let_cong",
        r"forall (R : RedEnv)  (f0 f1 f2 out : KExpr) (C : Type) (h : projection_parallel R (KExpr.let_ f0 f1 f2) out) (next : forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr out (KExpr.let_ g0 g1 g2) -> C), C",
        r"fun (R : RedEnv)  (f0 f1 f2 out : KExpr) (C : Type) (h : projection_parallel R (KExpr.let_ f0 f1 f2) out) (next : forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr out (KExpr.let_ g0 g1 g2) -> C) => projection_parallel.rec R (fun (x y : KExpr) (_h : projection_parallel R x y) => Eq KExpr x (KExpr.let_ f0 f1 f2) -> (forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr y (KExpr.let_ g0 g1 g2) -> C) -> C)
 (fun (x : KExpr) (same : Eq KExpr x (KExpr.let_ f0 f1 f2)) (next : forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr x (KExpr.let_ g0 g1 g2) -> C)  => next f0 f1 f2 (projection_parallel.refl R f0) (projection_parallel.refl R f1) (projection_parallel.refl R f2) same)
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (_ih0 : Eq KExpr a0 (KExpr.let_ f0 f1 f2) -> (forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr b0 (KExpr.let_ g0 g1 g2) -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.let_ f0 f1 f2) -> (forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr b1 (KExpr.let_ g0 g1 g2) -> C) -> C) (same : Eq KExpr (KExpr.app a0 a1) (KExpr.let_ f0 f1 f2)) (next : forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr (KExpr.app b0 b1) (KExpr.let_ g0 g1 g2) -> C)  => kexpr_discr_t C (KExpr.app a0 a1) (KExpr.let_ f0 f1 f2) same (Eq.refl Bool Bool.false))
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (_ih0 : Eq KExpr a0 (KExpr.let_ f0 f1 f2) -> (forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr b0 (KExpr.let_ g0 g1 g2) -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.let_ f0 f1 f2) -> (forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr b1 (KExpr.let_ g0 g1 g2) -> C) -> C) (same : Eq KExpr (KExpr.lam a0 a1) (KExpr.let_ f0 f1 f2)) (next : forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr (KExpr.lam b0 b1) (KExpr.let_ g0 g1 g2) -> C)  => kexpr_discr_t C (KExpr.lam a0 a1) (KExpr.let_ f0 f1 f2) same (Eq.refl Bool Bool.false))
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (_ih0 : Eq KExpr a0 (KExpr.let_ f0 f1 f2) -> (forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr b0 (KExpr.let_ g0 g1 g2) -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.let_ f0 f1 f2) -> (forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr b1 (KExpr.let_ g0 g1 g2) -> C) -> C) (same : Eq KExpr (KExpr.pi a0 a1) (KExpr.let_ f0 f1 f2)) (next : forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr (KExpr.pi b0 b1) (KExpr.let_ g0 g1 g2) -> C)  => kexpr_discr_t C (KExpr.pi a0 a1) (KExpr.let_ f0 f1 f2) same (Eq.refl Bool Bool.false))
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (_ih0 : Eq KExpr a0 (KExpr.let_ f0 f1 f2) -> (forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr b0 (KExpr.let_ g0 g1 g2) -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.let_ f0 f1 f2) -> (forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr b1 (KExpr.let_ g0 g1 g2) -> C) -> C) (same : Eq KExpr (KExpr.forall_ a0 a1) (KExpr.let_ f0 f1 f2)) (next : forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr (KExpr.forall_ b0 b1) (KExpr.let_ g0 g1 g2) -> C)  => kexpr_discr_t C (KExpr.forall_ a0 a1) (KExpr.let_ f0 f1 f2) same (Eq.refl Bool Bool.false))
 (fun (a0 b0 a1 b1 a2 b2 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (h2 : projection_parallel R a2 b2) (_ih0 : Eq KExpr a0 (KExpr.let_ f0 f1 f2) -> (forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr b0 (KExpr.let_ g0 g1 g2) -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.let_ f0 f1 f2) -> (forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr b1 (KExpr.let_ g0 g1 g2) -> C) -> C) (_ih2 : Eq KExpr a2 (KExpr.let_ f0 f1 f2) -> (forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr b2 (KExpr.let_ g0 g1 g2) -> C) -> C) (same : Eq KExpr (KExpr.let_ a0 a1 a2) (KExpr.let_ f0 f1 f2)) (next : forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr (KExpr.let_ b0 b1 b2) (KExpr.let_ g0 g1 g2) -> C)  => next b0 b1 b2 (Eq.substType KExpr (fun (z : KExpr) => projection_parallel R z b0) a0 f0 (let_inj_fst a0 a1 a2 f0 f1 f2 same) h0) (Eq.substType KExpr (fun (z : KExpr) => projection_parallel R z b1) a1 f1 (let_inj_snd a0 a1 a2 f0 f1 f2 same) h1) (Eq.substType KExpr (fun (z : KExpr) => projection_parallel R z b2) a2 f2 (let_inj_thd a0 a1 a2 f0 f1 f2 same) h2) (Eq.refl KExpr (KExpr.let_ b0 b1 b2)))
 (fun (N : Name) (I : Nat) (a0 b0 : KExpr) (h0 : projection_parallel R a0 b0) (_ih0 : Eq KExpr a0 (KExpr.let_ f0 f1 f2) -> (forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr b0 (KExpr.let_ g0 g1 g2) -> C) -> C) (same : Eq KExpr (KExpr.proj N I a0) (KExpr.let_ f0 f1 f2)) (next : forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr (KExpr.proj N I b0) (KExpr.let_ g0 g1 g2) -> C)  => kexpr_discr_t C (KExpr.proj N I a0) (KExpr.let_ f0 f1 f2) same (Eq.refl Bool Bool.false))
 (fun (N : Name) (I : Nat) (sub rootOut : KExpr) (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj N I sub)) (OptionType.some KExpr rootOut)) (same : Eq KExpr (KExpr.proj N I sub) (KExpr.let_ f0 f1 f2)) (next : forall (g0 g1 g2 : KExpr), projection_parallel R f0 g0 -> projection_parallel R f1 g1 -> projection_parallel R f2 g2 -> Eq KExpr rootOut (KExpr.let_ g0 g1 g2) -> C)  => kexpr_discr_t C (KExpr.proj N I sub) (KExpr.let_ f0 f1 f2) same (Eq.refl Bool Bool.false)) (KExpr.let_ f0 f1 f2) out h (Eq.refl KExpr (KExpr.let_ f0 f1 f2)) next",
    ),
    DeclarationInput::Proof(
        "projection_parallel_inv_proj",
        r"forall (R : RedEnv) (S : Name) (idx : Nat) (f0 out : KExpr) (C : Type) (h : projection_parallel R (KExpr.proj S idx f0) out) (next : forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr out (KExpr.proj S idx g0) -> C) (extract : forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr out v -> C), C",
        r"fun (R : RedEnv) (S : Name) (idx : Nat) (f0 out : KExpr) (C : Type) (h : projection_parallel R (KExpr.proj S idx f0) out) (next : forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr out (KExpr.proj S idx g0) -> C) (extract : forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr out v -> C) => projection_parallel.rec R (fun (x y : KExpr) (_h : projection_parallel R x y) => Eq KExpr x (KExpr.proj S idx f0) -> (forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr y (KExpr.proj S idx g0) -> C) -> (forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr y v -> C) -> C)
 (fun (x : KExpr) (same : Eq KExpr x (KExpr.proj S idx f0)) (next : forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr x (KExpr.proj S idx g0) -> C) (extract : forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr x v -> C) => next f0 (projection_parallel.refl R f0) same)
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (_ih0 : Eq KExpr a0 (KExpr.proj S idx f0) -> (forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr b0 (KExpr.proj S idx g0) -> C) -> (forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr b0 v -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.proj S idx f0) -> (forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr b1 (KExpr.proj S idx g0) -> C) -> (forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr b1 v -> C) -> C) (same : Eq KExpr (KExpr.app a0 a1) (KExpr.proj S idx f0)) (next : forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr (KExpr.app b0 b1) (KExpr.proj S idx g0) -> C) (extract : forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr (KExpr.app b0 b1) v -> C) => kexpr_discr_t C (KExpr.app a0 a1) (KExpr.proj S idx f0) same (Eq.refl Bool Bool.false))
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (_ih0 : Eq KExpr a0 (KExpr.proj S idx f0) -> (forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr b0 (KExpr.proj S idx g0) -> C) -> (forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr b0 v -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.proj S idx f0) -> (forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr b1 (KExpr.proj S idx g0) -> C) -> (forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr b1 v -> C) -> C) (same : Eq KExpr (KExpr.lam a0 a1) (KExpr.proj S idx f0)) (next : forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr (KExpr.lam b0 b1) (KExpr.proj S idx g0) -> C) (extract : forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr (KExpr.lam b0 b1) v -> C) => kexpr_discr_t C (KExpr.lam a0 a1) (KExpr.proj S idx f0) same (Eq.refl Bool Bool.false))
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (_ih0 : Eq KExpr a0 (KExpr.proj S idx f0) -> (forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr b0 (KExpr.proj S idx g0) -> C) -> (forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr b0 v -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.proj S idx f0) -> (forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr b1 (KExpr.proj S idx g0) -> C) -> (forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr b1 v -> C) -> C) (same : Eq KExpr (KExpr.pi a0 a1) (KExpr.proj S idx f0)) (next : forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr (KExpr.pi b0 b1) (KExpr.proj S idx g0) -> C) (extract : forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr (KExpr.pi b0 b1) v -> C) => kexpr_discr_t C (KExpr.pi a0 a1) (KExpr.proj S idx f0) same (Eq.refl Bool Bool.false))
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (_ih0 : Eq KExpr a0 (KExpr.proj S idx f0) -> (forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr b0 (KExpr.proj S idx g0) -> C) -> (forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr b0 v -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.proj S idx f0) -> (forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr b1 (KExpr.proj S idx g0) -> C) -> (forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr b1 v -> C) -> C) (same : Eq KExpr (KExpr.forall_ a0 a1) (KExpr.proj S idx f0)) (next : forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr (KExpr.forall_ b0 b1) (KExpr.proj S idx g0) -> C) (extract : forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr (KExpr.forall_ b0 b1) v -> C) => kexpr_discr_t C (KExpr.forall_ a0 a1) (KExpr.proj S idx f0) same (Eq.refl Bool Bool.false))
 (fun (a0 b0 a1 b1 a2 b2 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (h2 : projection_parallel R a2 b2) (_ih0 : Eq KExpr a0 (KExpr.proj S idx f0) -> (forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr b0 (KExpr.proj S idx g0) -> C) -> (forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr b0 v -> C) -> C) (_ih1 : Eq KExpr a1 (KExpr.proj S idx f0) -> (forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr b1 (KExpr.proj S idx g0) -> C) -> (forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr b1 v -> C) -> C) (_ih2 : Eq KExpr a2 (KExpr.proj S idx f0) -> (forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr b2 (KExpr.proj S idx g0) -> C) -> (forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr b2 v -> C) -> C) (same : Eq KExpr (KExpr.let_ a0 a1 a2) (KExpr.proj S idx f0)) (next : forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr (KExpr.let_ b0 b1 b2) (KExpr.proj S idx g0) -> C) (extract : forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr (KExpr.let_ b0 b1 b2) v -> C) => kexpr_discr_t C (KExpr.let_ a0 a1 a2) (KExpr.proj S idx f0) same (Eq.refl Bool Bool.false))
 (fun (N : Name) (I : Nat) (a0 b0 : KExpr) (h0 : projection_parallel R a0 b0) (_ih0 : Eq KExpr a0 (KExpr.proj S idx f0) -> (forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr b0 (KExpr.proj S idx g0) -> C) -> (forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr b0 v -> C) -> C) (same : Eq KExpr (KExpr.proj N I a0) (KExpr.proj S idx f0)) (next : forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr (KExpr.proj N I b0) (KExpr.proj S idx g0) -> C) (extract : forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr (KExpr.proj N I b0) v -> C) => next b0 (Eq.substType KExpr (fun (z : KExpr) => projection_parallel R z b0) a0 f0 (proj_inj_sub N I a0 S idx f0 same) h0) (Eq.trans KExpr (KExpr.proj N I b0) (KExpr.proj S I b0) (KExpr.proj S idx b0) (Eq.cong Name KExpr (fun (n : Name) => (KExpr.proj n I b0)) N S (proj_inj_name N I a0 S idx f0 same)) (Eq.cong Nat KExpr (fun (i : Nat) => (KExpr.proj S i b0)) I idx (proj_inj_idx N I a0 S idx f0 same))))
 (fun (N : Name) (I : Nat) (sub rootOut : KExpr) (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj N I sub)) (OptionType.some KExpr rootOut)) (same : Eq KExpr (KExpr.proj N I sub) (KExpr.proj S idx f0)) (next : forall (g0 : KExpr), projection_parallel R f0 g0 -> Eq KExpr rootOut (KExpr.proj S idx g0) -> C) (extract : forall (v : KExpr), Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx f0)) (OptionType.some KExpr v) -> Eq KExpr rootOut v -> C) => extract rootOut (Eq.subst KExpr (fun (z : KExpr) => Eq (OptionType KExpr) (projection_post_whnf_reduct R z) (OptionType.some KExpr rootOut)) (KExpr.proj N I sub) (KExpr.proj S idx f0) same run) (Eq.refl KExpr rootOut)) (KExpr.proj S idx f0) out h (Eq.refl KExpr (KExpr.proj S idx f0)) next extract",
    ),
    DeclarationInput::Proof(
        "projection_parallel_join_extract_cong",
        r"forall (R : RedEnv) (S : Name) (idx : Nat) (sub sub2 a : KExpr)
 (h : projection_parallel R sub sub2)
 (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx sub)) (OptionType.some KExpr a)), ProjectionParallelJoin R a (KExpr.proj S idx sub2)",
        r"fun (R : RedEnv) (S : Name) (idx : Nat) (sub sub2 a : KExpr)
 (h : projection_parallel R sub sub2)
 (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx sub)) (OptionType.some KExpr a)) => projection_parallel_selector_transport R S idx sub sub2 h a run (ProjectionParallelJoin R a (KExpr.proj S idx sub2))
  (fun (b : KExpr) (run2 : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx sub2)) (OptionType.some KExpr b)) (ab : projection_parallel R a b) =>
   ProjectionParallelJoin.mk R a (KExpr.proj S idx sub2) b ab (projection_parallel.projection_beta R S idx sub2 b run2))",
    ),
    DeclarationInput::Proof(
        "projection_parallel_join_extract_extract",
        r"forall (R : RedEnv) (e a b : KExpr)
 (ha : Eq (OptionType KExpr) (projection_post_whnf_reduct R e) (OptionType.some KExpr a))
 (hb : Eq (OptionType KExpr) (projection_post_whnf_reduct R e) (OptionType.some KExpr b)), ProjectionParallelJoin R a b",
        r"fun (R : RedEnv) (e a b : KExpr)
 (ha : Eq (OptionType KExpr) (projection_post_whnf_reduct R e) (OptionType.some KExpr a))
 (hb : Eq (OptionType KExpr) (projection_post_whnf_reduct R e) (OptionType.some KExpr b)) => ProjectionParallelJoin.mk R a b a (projection_parallel.refl R a)
  (Eq.substType KExpr (fun (v : KExpr) => projection_parallel R b v) b a
   (projection_post_whnf_deterministic R e b a hb ha) (projection_parallel.refl R b))",
    ),
    DeclarationInput::Proof(
        "projection_parallel_diamond",
        r"forall (R : RedEnv) (e a b : KExpr) (ha : projection_parallel R e a) (hb : projection_parallel R e b), ProjectionParallelJoin R a b",
        r"fun (R : RedEnv) (e a b : KExpr) (ha : projection_parallel R e a) (hb : projection_parallel R e b) => projection_parallel.rec R (fun (x y : KExpr) (_h : projection_parallel R x y) => forall (z : KExpr), projection_parallel R x z -> ProjectionParallelJoin R y z)
 (fun (x z : KExpr) (xz : projection_parallel R x z) => ProjectionParallelJoin.mk R x z z xz (projection_parallel.refl R z))
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (ih0 : forall (z : KExpr), projection_parallel R a0 z -> ProjectionParallelJoin R b0 z) (ih1 : forall (z : KExpr), projection_parallel R a1 z -> ProjectionParallelJoin R b1 z) (z : KExpr) (hz : projection_parallel R (KExpr.app a0 a1) z) => projection_parallel_inv_app R a0 a1 z (ProjectionParallelJoin R (KExpr.app b0 b1) z) hz (fun (g0 g1 : KExpr) (hg0 : projection_parallel R a0 g0) (hg1 : projection_parallel R a1 g1) (outEq : Eq KExpr z (KExpr.app g0 g1)) => Eq.substType KExpr (fun (v : KExpr) => ProjectionParallelJoin R (KExpr.app b0 b1) v) (KExpr.app g0 g1) z (Eq.symm KExpr z (KExpr.app g0 g1) outEq) (projection_parallel_join_app R b0 g0 b1 g1 (ih0 g0 hg0) (ih1 g1 hg1))) )
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (ih0 : forall (z : KExpr), projection_parallel R a0 z -> ProjectionParallelJoin R b0 z) (ih1 : forall (z : KExpr), projection_parallel R a1 z -> ProjectionParallelJoin R b1 z) (z : KExpr) (hz : projection_parallel R (KExpr.lam a0 a1) z) => projection_parallel_inv_lam R a0 a1 z (ProjectionParallelJoin R (KExpr.lam b0 b1) z) hz (fun (g0 g1 : KExpr) (hg0 : projection_parallel R a0 g0) (hg1 : projection_parallel R a1 g1) (outEq : Eq KExpr z (KExpr.lam g0 g1)) => Eq.substType KExpr (fun (v : KExpr) => ProjectionParallelJoin R (KExpr.lam b0 b1) v) (KExpr.lam g0 g1) z (Eq.symm KExpr z (KExpr.lam g0 g1) outEq) (projection_parallel_join_lam R b0 g0 b1 g1 (ih0 g0 hg0) (ih1 g1 hg1))) )
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (ih0 : forall (z : KExpr), projection_parallel R a0 z -> ProjectionParallelJoin R b0 z) (ih1 : forall (z : KExpr), projection_parallel R a1 z -> ProjectionParallelJoin R b1 z) (z : KExpr) (hz : projection_parallel R (KExpr.pi a0 a1) z) => projection_parallel_inv_pi R a0 a1 z (ProjectionParallelJoin R (KExpr.pi b0 b1) z) hz (fun (g0 g1 : KExpr) (hg0 : projection_parallel R a0 g0) (hg1 : projection_parallel R a1 g1) (outEq : Eq KExpr z (KExpr.pi g0 g1)) => Eq.substType KExpr (fun (v : KExpr) => ProjectionParallelJoin R (KExpr.pi b0 b1) v) (KExpr.pi g0 g1) z (Eq.symm KExpr z (KExpr.pi g0 g1) outEq) (projection_parallel_join_pi R b0 g0 b1 g1 (ih0 g0 hg0) (ih1 g1 hg1))) )
 (fun (a0 b0 a1 b1 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (ih0 : forall (z : KExpr), projection_parallel R a0 z -> ProjectionParallelJoin R b0 z) (ih1 : forall (z : KExpr), projection_parallel R a1 z -> ProjectionParallelJoin R b1 z) (z : KExpr) (hz : projection_parallel R (KExpr.forall_ a0 a1) z) => projection_parallel_inv_pi R a0 a1 z (ProjectionParallelJoin R (KExpr.forall_ b0 b1) z) hz (fun (g0 g1 : KExpr) (hg0 : projection_parallel R a0 g0) (hg1 : projection_parallel R a1 g1) (outEq : Eq KExpr z (KExpr.forall_ g0 g1)) => Eq.substType KExpr (fun (v : KExpr) => ProjectionParallelJoin R (KExpr.forall_ b0 b1) v) (KExpr.forall_ g0 g1) z (Eq.symm KExpr z (KExpr.forall_ g0 g1) outEq) (projection_parallel_join_forall_ R b0 g0 b1 g1 (ih0 g0 hg0) (ih1 g1 hg1))) )
 (fun (a0 b0 a1 b1 a2 b2 : KExpr) (h0 : projection_parallel R a0 b0) (h1 : projection_parallel R a1 b1) (h2 : projection_parallel R a2 b2) (ih0 : forall (z : KExpr), projection_parallel R a0 z -> ProjectionParallelJoin R b0 z) (ih1 : forall (z : KExpr), projection_parallel R a1 z -> ProjectionParallelJoin R b1 z) (ih2 : forall (z : KExpr), projection_parallel R a2 z -> ProjectionParallelJoin R b2 z) (z : KExpr) (hz : projection_parallel R (KExpr.let_ a0 a1 a2) z) => projection_parallel_inv_let_cong R a0 a1 a2 z (ProjectionParallelJoin R (KExpr.let_ b0 b1 b2) z) hz (fun (g0 g1 g2 : KExpr) (hg0 : projection_parallel R a0 g0) (hg1 : projection_parallel R a1 g1) (hg2 : projection_parallel R a2 g2) (outEq : Eq KExpr z (KExpr.let_ g0 g1 g2)) => Eq.substType KExpr (fun (v : KExpr) => ProjectionParallelJoin R (KExpr.let_ b0 b1 b2) v) (KExpr.let_ g0 g1 g2) z (Eq.symm KExpr z (KExpr.let_ g0 g1 g2) outEq) (projection_parallel_join_let_cong R b0 g0 b1 g1 b2 g2 (ih0 g0 hg0) (ih1 g1 hg1) (ih2 g2 hg2))) )
 (fun (S : Name) (idx : Nat) (a0 b0 : KExpr) (h0 : projection_parallel R a0 b0) (ih0 : forall (z : KExpr), projection_parallel R a0 z -> ProjectionParallelJoin R b0 z) (z : KExpr) (hz : projection_parallel R (KExpr.proj S idx a0) z) => projection_parallel_inv_proj R S idx a0 z (ProjectionParallelJoin R (KExpr.proj S idx b0) z) hz (fun (g0 : KExpr) (hg0 : projection_parallel R a0 g0) (outEq : Eq KExpr z (KExpr.proj S idx g0)) => Eq.substType KExpr (fun (v : KExpr) => ProjectionParallelJoin R (KExpr.proj S idx b0) v) (KExpr.proj S idx g0) z (Eq.symm KExpr z (KExpr.proj S idx g0) outEq) (projection_parallel_join_proj R S idx b0 g0 (ih0 g0 hg0))) (fun (v : KExpr) (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx a0)) (OptionType.some KExpr v)) (outEq : Eq KExpr z v) => Eq.substType KExpr (fun (w : KExpr) => ProjectionParallelJoin R (KExpr.proj S idx b0) w) v z (Eq.symm KExpr z v outEq) (projection_parallel_join_symm R v (KExpr.proj S idx b0) (projection_parallel_join_extract_cong R S idx a0 b0 v h0 run))))
 (fun (S : Name) (idx : Nat) (sub a : KExpr) (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx sub)) (OptionType.some KExpr a)) (z : KExpr) (hz : projection_parallel R (KExpr.proj S idx sub) z) =>
 projection_parallel_inv_proj R S idx sub z (ProjectionParallelJoin R a z) hz
  (fun (sub2 : KExpr) (hs : projection_parallel R sub sub2) (outEq : Eq KExpr z (KExpr.proj S idx sub2)) =>
   Eq.substType KExpr (fun (v : KExpr) => ProjectionParallelJoin R a v) (KExpr.proj S idx sub2) z (Eq.symm KExpr z (KExpr.proj S idx sub2) outEq)
    (projection_parallel_join_extract_cong R S idx sub sub2 a hs run))
  (fun (b : KExpr) (run2 : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx sub)) (OptionType.some KExpr b)) (outEq : Eq KExpr z b) =>
   Eq.substType KExpr (fun (v : KExpr) => ProjectionParallelJoin R a v) b z (Eq.symm KExpr z b outEq)
    (projection_parallel_join_extract_extract R (KExpr.proj S idx sub) a b run run2))) e a ha b hb",
    ),
    DeclarationInput::Inductive(
        r"inductive projection_parallel_star (R : RedEnv) : KExpr -> KExpr -> Type
| refl : forall (e : KExpr), projection_parallel_star R e e
| step : forall (e m r : KExpr), projection_parallel R e m -> projection_parallel_star R m r -> projection_parallel_star R e r",
    ),
    DeclarationInput::Inductive(
        r"inductive ProjectionParallelStrip (R : RedEnv) (a b : KExpr) : Type
| mk : forall (c : KExpr), projection_parallel_star R a c -> projection_parallel R b c -> ProjectionParallelStrip R a b",
    ),
    DeclarationInput::Inductive(
        r"inductive ProjectionParallelStarJoin (R : RedEnv) (a b : KExpr) : Type
| mk : forall (c : KExpr), projection_parallel_star R a c -> projection_parallel_star R b c -> ProjectionParallelStarJoin R a b",
    ),
    DeclarationInput::Proof(
        "projection_parallel_strip",
        r"forall (R : RedEnv) (e a b : KExpr)
 (ha : projection_parallel R e a) (hb : projection_parallel_star R e b), ProjectionParallelStrip R a b",
        r"fun (R : RedEnv) (e a b : KExpr)
 (ha : projection_parallel R e a) (hb : projection_parallel_star R e b) => projection_parallel_star.rec R
  (fun (x z : KExpr) (_h : projection_parallel_star R x z) => forall (y : KExpr), projection_parallel R x y -> ProjectionParallelStrip R y z)
  (fun (x y : KExpr) (xy : projection_parallel R x y) =>
   ProjectionParallelStrip.mk R y x y (projection_parallel_star.refl R y) xy)
  (fun (x m z : KExpr) (xm : projection_parallel R x m) (_mz : projection_parallel_star R m z)
   (ih : forall (y : KExpr), projection_parallel R m y -> ProjectionParallelStrip R y z)
   (y : KExpr) (xy : projection_parallel R x y) =>
   ProjectionParallelJoin.rec R y m
    (fun (_j : ProjectionParallelJoin R y m) => ProjectionParallelStrip R y z)
    (fun (c : KExpr) (yc : projection_parallel R y c) (mc : projection_parallel R m c) =>
     ProjectionParallelStrip.rec R c z
      (fun (_s : ProjectionParallelStrip R c z) => ProjectionParallelStrip R y z)
      (fun (d : KExpr) (cToD : projection_parallel_star R c d) (zd : projection_parallel R z d) =>
       ProjectionParallelStrip.mk R y z d (projection_parallel_star.step R y c d yc cToD) zd)
      (ih c mc))
    (projection_parallel_diamond R x y m xy xm)) e b hb a ha",
    ),
    DeclarationInput::Proof(
        "projection_parallel_star_confluent",
        r"forall (R : RedEnv) (e a b : KExpr)
 (ha : projection_parallel_star R e a) (hb : projection_parallel_star R e b), ProjectionParallelStarJoin R a b",
        r"fun (R : RedEnv) (e a b : KExpr)
 (ha : projection_parallel_star R e a) (hb : projection_parallel_star R e b) => projection_parallel_star.rec R
  (fun (x y : KExpr) (_h : projection_parallel_star R x y) => forall (z : KExpr), projection_parallel_star R x z -> ProjectionParallelStarJoin R y z)
  (fun (x z : KExpr) (xz : projection_parallel_star R x z) =>
   ProjectionParallelStarJoin.mk R x z z xz (projection_parallel_star.refl R z))
  (fun (x m y : KExpr) (xm : projection_parallel R x m) (_my : projection_parallel_star R m y)
   (ih : forall (z : KExpr), projection_parallel_star R m z -> ProjectionParallelStarJoin R y z)
   (z : KExpr) (xz : projection_parallel_star R x z) =>
   ProjectionParallelStrip.rec R m z
    (fun (_s : ProjectionParallelStrip R m z) => ProjectionParallelStarJoin R y z)
    (fun (c : KExpr) (mc : projection_parallel_star R m c) (zc : projection_parallel R z c) =>
     ProjectionParallelStarJoin.rec R y c
      (fun (_j : ProjectionParallelStarJoin R y c) => ProjectionParallelStarJoin R y z)
      (fun (d : KExpr) (yd : projection_parallel_star R y d) (cToD : projection_parallel_star R c d) =>
       ProjectionParallelStarJoin.mk R y z d yd (projection_parallel_star.step R z c d zc cToD))
      (ih c mc))
    (projection_parallel_strip R x m z xm xz)) e a ha b hb",
    ),
    DeclarationInput::Proof(
        "projection_parallel_inner_step",
        r"projection_parallel the_red_env cdp_prod_inner_projection rfnz_zero",
        r"projection_parallel.projection_beta the_red_env kcre_prod_type_name Nat.zero kcre_witness_prod_value rfnz_zero cdp_prod_inner_extract",
    ),
    DeclarationInput::Proof(
        "projection_parallel_outer_step",
        r"projection_parallel the_red_env cdp_prod_outer_before kcre_witness_prod_value",
        r"projection_parallel.app the_red_env
  (KExpr.app ctor_spine_prod_prefix cdp_prod_inner_projection) (KExpr.app ctor_spine_prod_prefix rfnz_zero)
  (KExpr.app rfnz_succ rfnz_zero) (KExpr.app rfnz_succ rfnz_zero)
  (projection_parallel.app the_red_env ctor_spine_prod_prefix ctor_spine_prod_prefix cdp_prod_inner_projection rfnz_zero
   (projection_parallel.refl the_red_env ctor_spine_prod_prefix) projection_parallel_inner_step)
  (projection_parallel.refl the_red_env (KExpr.app rfnz_succ rfnz_zero))",
    ),
    DeclarationInput::Data(
        "projection_parallel_retained_source",
        r"KExpr",
        r"KExpr.proj Name.anonymous Nat.zero cdp_prod_outer_before",
    ),
    DeclarationInput::Data(
        "projection_parallel_retained_residual",
        r"KExpr",
        r"KExpr.proj Name.anonymous Nat.zero kcre_witness_prod_value",
    ),
    DeclarationInput::Proof(
        "projection_parallel_retained_extract",
        r"Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env projection_parallel_retained_source) (OptionType.some KExpr cdp_prod_inner_projection)",
        r"Eq.refl (OptionType KExpr) (OptionType.some KExpr cdp_prod_inner_projection)",
    ),
    DeclarationInput::Proof(
        "projection_parallel_retained_root",
        r"projection_parallel the_red_env projection_parallel_retained_source cdp_prod_inner_projection",
        r"projection_parallel.projection_beta the_red_env Name.anonymous Nat.zero cdp_prod_outer_before cdp_prod_inner_projection projection_parallel_retained_extract",
    ),
    DeclarationInput::Proof(
        "projection_parallel_retained_cong",
        r"projection_parallel the_red_env projection_parallel_retained_source projection_parallel_retained_residual",
        r"projection_parallel.proj the_red_env Name.anonymous Nat.zero cdp_prod_outer_before kcre_witness_prod_value projection_parallel_outer_step",
    ),
    DeclarationInput::Proof(
        "projection_parallel_retained_join",
        r"ProjectionParallelJoin the_red_env cdp_prod_inner_projection projection_parallel_retained_residual",
        r"projection_parallel_diamond the_red_env projection_parallel_retained_source cdp_prod_inner_projection projection_parallel_retained_residual projection_parallel_retained_root projection_parallel_retained_cong",
    ),
    DeclarationInput::Proof(
        "projection_parallel_retained_tail",
        r"projection_parallel the_red_env projection_parallel_retained_residual rfnz_zero",
        r"projection_parallel.projection_beta the_red_env Name.anonymous Nat.zero kcre_witness_prod_value rfnz_zero projection_post_whnf_prod_after_zero",
    ),
    DeclarationInput::Proof(
        "projection_parallel_retained_explicit_meet",
        r"ProjectionParallelJoin the_red_env cdp_prod_inner_projection projection_parallel_retained_residual",
        r"ProjectionParallelJoin.mk the_red_env cdp_prod_inner_projection projection_parallel_retained_residual rfnz_zero projection_parallel_inner_step projection_parallel_retained_tail",
    ),
    DeclarationInput::Data(
        "projection_parallel_discarded_source",
        r"KExpr",
        r"KExpr.proj Name.anonymous (Nat.succ Nat.zero) cdp_prod_outer_before",
    ),
    DeclarationInput::Data(
        "projection_parallel_discarded_residual",
        r"KExpr",
        r"KExpr.proj Name.anonymous (Nat.succ Nat.zero) kcre_witness_prod_value",
    ),
    DeclarationInput::Proof(
        "projection_parallel_discarded_extract",
        r"Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env projection_parallel_discarded_source) (OptionType.some KExpr (KExpr.app rfnz_succ rfnz_zero))",
        r"Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.app rfnz_succ rfnz_zero))",
    ),
    DeclarationInput::Proof(
        "projection_parallel_discarded_root",
        r"projection_parallel the_red_env projection_parallel_discarded_source (KExpr.app rfnz_succ rfnz_zero)",
        r"projection_parallel.projection_beta the_red_env Name.anonymous (Nat.succ Nat.zero) cdp_prod_outer_before (KExpr.app rfnz_succ rfnz_zero) projection_parallel_discarded_extract",
    ),
    DeclarationInput::Proof(
        "projection_parallel_discarded_cong",
        r"projection_parallel the_red_env projection_parallel_discarded_source projection_parallel_discarded_residual",
        r"projection_parallel.proj the_red_env Name.anonymous (Nat.succ Nat.zero) cdp_prod_outer_before kcre_witness_prod_value projection_parallel_outer_step",
    ),
    DeclarationInput::Proof(
        "projection_parallel_discarded_join",
        r"ProjectionParallelJoin the_red_env (KExpr.app rfnz_succ rfnz_zero) projection_parallel_discarded_residual",
        r"projection_parallel_diamond the_red_env projection_parallel_discarded_source (KExpr.app rfnz_succ rfnz_zero) projection_parallel_discarded_residual projection_parallel_discarded_root projection_parallel_discarded_cong",
    ),
    DeclarationInput::Proof(
        "projection_parallel_discarded_tail",
        r"projection_parallel the_red_env projection_parallel_discarded_residual (KExpr.app rfnz_succ rfnz_zero)",
        r"projection_parallel.projection_beta the_red_env Name.anonymous (Nat.succ Nat.zero) kcre_witness_prod_value (KExpr.app rfnz_succ rfnz_zero) projection_post_whnf_prod_after_one",
    ),
    DeclarationInput::Proof(
        "projection_parallel_discarded_explicit_meet",
        r"ProjectionParallelJoin the_red_env (KExpr.app rfnz_succ rfnz_zero) projection_parallel_discarded_residual",
        r"ProjectionParallelJoin.mk the_red_env (KExpr.app rfnz_succ rfnz_zero) projection_parallel_discarded_residual (KExpr.app rfnz_succ rfnz_zero)
  (projection_parallel.refl the_red_env (KExpr.app rfnz_succ rfnz_zero)) projection_parallel_discarded_tail",
    ),
    DeclarationInput::Proof(
        "projection_parallel_retained_star_join",
        r"ProjectionParallelStarJoin the_red_env cdp_prod_inner_projection rfnz_zero",
        r"projection_parallel_star_confluent the_red_env projection_parallel_retained_source cdp_prod_inner_projection rfnz_zero
  (projection_parallel_star.step the_red_env projection_parallel_retained_source cdp_prod_inner_projection cdp_prod_inner_projection projection_parallel_retained_root (projection_parallel_star.refl the_red_env cdp_prod_inner_projection))
  (projection_parallel_star.step the_red_env projection_parallel_retained_source projection_parallel_retained_residual rfnz_zero projection_parallel_retained_cong
   (projection_parallel_star.step the_red_env projection_parallel_retained_residual rfnz_zero rfnz_zero projection_parallel_retained_tail (projection_parallel_star.refl the_red_env rfnz_zero)))",
    ),
    DeclarationInput::Proof(
        "projection_parallel_discarded_embedded",
        r"par_reduces_cdp the_red_env projection_parallel_discarded_source (KExpr.app rfnz_succ rfnz_zero)",
        r"projection_parallel_to_cdp the_red_env projection_parallel_discarded_source (KExpr.app rfnz_succ rfnz_zero) projection_parallel_discarded_root",
    ),
];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "projection_parallel_forged_retained",
        r"projection_parallel the_red_env projection_parallel_retained_residual (KExpr.app rfnz_succ rfnz_zero)",
        r"projection_parallel_retained_tail",
    ),
    (
        "projection_parallel_forged_discarded",
        r"projection_parallel the_red_env projection_parallel_discarded_residual rfnz_zero",
        r"projection_parallel_discarded_tail",
    ),
    (
        "projection_parallel_forged_root_equation",
        r"projection_parallel the_red_env cdp_prod_inner_projection (KExpr.app rfnz_succ rfnz_zero)",
        r"projection_parallel.projection_beta the_red_env kcre_prod_type_name Nat.zero kcre_witness_prod_value (KExpr.app rfnz_succ rfnz_zero) cdp_prod_inner_extract",
    ),
    (
        "projection_parallel_forged_beta",
        r"projection_parallel the_red_env ctor_spine_prod_redex rfnz_zero",
        r"ctor_spine_prod_beta",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "projection_parallel_list_refl",
    "projection_parallel_list_append",
    "projection_parallel_list_tail",
    "projection_parallel_list_drop",
    "projection_parallel_list_head_some",
    "projection_parallel_list_length",
    "projection_parallel_const_spine",
    "projection_parallel_selected_position",
    "projection_parallel_selector_transport",
    "projection_parallel_to_cdp",
    "projection_parallel_join_symm",
    "projection_parallel_join_app",
    "projection_parallel_join_lam",
    "projection_parallel_join_pi",
    "projection_parallel_join_forall_",
    "projection_parallel_join_let_cong",
    "projection_parallel_join_proj",
    "projection_parallel_inv_app",
    "projection_parallel_inv_lam",
    "projection_parallel_inv_pi",
    "projection_parallel_inv_let_cong",
    "projection_parallel_inv_proj",
    "projection_parallel_join_extract_cong",
    "projection_parallel_join_extract_extract",
    "projection_parallel_diamond",
    "projection_parallel_strip",
    "projection_parallel_star_confluent",
    "projection_parallel_inner_step",
    "projection_parallel_outer_step",
    "projection_parallel_retained_extract",
    "projection_parallel_retained_root",
    "projection_parallel_retained_cong",
    "projection_parallel_retained_join",
    "projection_parallel_retained_tail",
    "projection_parallel_retained_explicit_meet",
    "projection_parallel_discarded_extract",
    "projection_parallel_discarded_root",
    "projection_parallel_discarded_cong",
    "projection_parallel_discarded_join",
    "projection_parallel_discarded_tail",
    "projection_parallel_discarded_explicit_meet",
    "projection_parallel_retained_star_join",
    "projection_parallel_discarded_embedded",
];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[
    "projection_parallel_retained_source",
    "projection_parallel_retained_residual",
    "projection_parallel_discarded_source",
    "projection_parallel_discarded_residual",
];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &[
    "projection_parallel",
    "projection_parallel_list",
    "ProjectionConstSpineView",
    "ProjectionParallelJoin",
    "projection_parallel_star",
    "ProjectionParallelStrip",
    "ProjectionParallelStarJoin",
];
