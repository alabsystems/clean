// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The relations and their soundness: the projection walks, the declarative
//! target `TypingProjIn`, the algorithmic `KernelAcceptsIn`, and the proofs that
//! connect them to the existing env-indexed family.

use super::DeclarationInput;

/// The structure-application facts `infer_proj_type_from_impl` checks on the
/// whnf'd subject type `W` (head constant named `S`, one-constructor inductive,
/// field bound, universe and TYPE-argument counts), bundled so the arms stay
/// readable. Equations to computations, never assumed metadata.
pub(super) const PROJ_STRUCT: &str = r"inductive ProjStructIn (R : RedEnv) (S : Name) (idx : Nat) (W : KExpr) : KIndMeta -> KCtorMeta -> Type
| mk : forall (im : KIndMeta) (cn : Name) (cm : KCtorMeta), @Eq (OptionType Name) (kexpr_const_name (kapp_fn W)) (@OptionType.some Name S) -> @Eq (OptionType KIndMeta) (kind_for (red_ind_ctor R) S) (@OptionType.some KIndMeta im) -> @Eq (ListType Name) (kind_ctor_names im) (@ListType.cons Name cn (@ListType.nil Name)) -> @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) cn) (@OptionType.some KCtorMeta cm) -> @Eq Bool (nat_leb (Nat.succ idx) (kctor_num_fields cm)) Bool.true -> @Eq Bool (nat_eqb (name_list_len (kconst_params (kind_sig im))) (level_list_len (kexpr_const_levels (kapp_fn W)))) Bool.true -> @Eq Bool (nat_eqb (Nat.add (kctor_num_params cm) (kind_num_indices im)) (list_length (kapp_args W))) Bool.true -> ProjStructIn R S idx W im cm";

/// `instantiate_params`: each parameter is consumed under a finite
/// projection-extended reduction to a Pi. The source's premature non-Pi stop
/// is NOT an arm (the E4 inventory excludes it under `admitted_ctor_telescope`).
pub(super) const PROJ_PARAMS: &str = r"inductive ProjParamsIn (R : RedEnv) : KExpr -> ListType KExpr -> KExpr -> Type
| nil : forall (t : KExpr), ProjParamsIn R t (@ListType.nil KExpr) t
| cons : forall (t : KExpr) (A : KExpr) (B : KExpr) (a : KExpr) (rest : ListType KExpr) (out : KExpr), par_reduces_cdp_star R t (KExpr.pi A B) -> ProjParamsIn R (instantiate B a) rest out -> ProjParamsIn R t (@ListType.cons KExpr a rest) out";

/// The field walk of `cache_projection_field_types_non_prop` /
/// `walk_prop_telescope_to_idx` up to the requested field: each field's Pi
/// is exposed by `pi_domain_body_quick` (raw Pi or whnf), a preceding field's
/// body takes `Proj(S, j, e)` through the source's no-loose-bvar shortcut
/// (`projection_field_body`), and the requested field returns its domain.
pub(super) const PROJ_FIELD: &str = r"inductive ProjFieldIn (R : RedEnv) (S : Name) (e : KExpr) : Nat -> Nat -> KExpr -> KExpr -> Type
| here : forall (j : Nat) (t : KExpr) (A : KExpr) (B : KExpr), par_reduces_cdp_star R t (KExpr.pi A B) -> ProjFieldIn R S e j j t A
| next : forall (j : Nat) (idx : Nat) (t : KExpr) (A : KExpr) (B : KExpr) (F : KExpr), par_reduces_cdp_star R t (KExpr.pi A B) -> ProjFieldIn R S e (Nat.succ j) idx (projection_field_body B (KExpr.proj S j e)) F -> ProjFieldIn R S e j idx t F";

/// The declarative target: `TypingCDPCtxConvIn` plus Lean 4's primitive
/// projection rule. Its `proj` premises are the walks above over the subject's
/// structure type; the Prop-elimination guard is not a premise.
pub(super) const TYPING: &str = r"inductive TypingProjIn (R : RedEnv) (tenv : KDeclEnv) : ListType KExpr -> KExpr -> KExpr -> Type
| var : forall (G : ListType KExpr) (i : Nat) (A : KExpr), @Eq (OptionType KExpr) (ctx_lookup G i) (@OptionType.some KExpr A) -> TypingProjIn R tenv G (KExpr.bvar i) (lift_at A Nat.zero (Nat.succ i))
| sort : forall (G : ListType KExpr) (u : Level), TypingProjIn R tenv G (KExpr.sort u) (KExpr.sort (Level.succ u))
| pi : forall (G : ListType KExpr) (A : KExpr) (B : KExpr) (u : Level) (v : Level), TypingProjIn R tenv G A (KExpr.sort u) -> TypingProjIn R tenv (@ListType.cons KExpr A G) B (KExpr.sort v) -> TypingProjIn R tenv G (KExpr.pi A B) (KExpr.sort (Level.imax u v))
| lam : forall (G : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level), TypingProjIn R tenv G A (KExpr.sort u) -> TypingProjIn R tenv (@ListType.cons KExpr A G) b B -> TypingProjIn R tenv G (KExpr.lam A b) (KExpr.pi A B)
| app : forall (G : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr), TypingProjIn R tenv G f (KExpr.pi A B) -> TypingProjIn R tenv G a A -> TypingProjIn R tenv G (KExpr.app f a) (instantiate B a)
| const : forall (G : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr), @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A) -> TypingProjIn R tenv G (KExpr.const n us) A
| conv : forall (G : ListType KExpr) (e : KExpr) (A : KExpr) (B : KExpr), TypingProjIn R tenv G e A -> DefEqCDPIn R A B -> TypingProjIn R tenv G e B
| let_ : forall (G : ListType KExpr) (A : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level), TypingProjIn R tenv G A (KExpr.sort u) -> TypingProjIn R tenv G v A -> TypingProjIn R tenv (@ListType.cons KExpr A G) b B -> TypingProjIn R tenv G (KExpr.let_ A v b) (instantiate B v)
| lit_nat : forall (G : ListType KExpr) (n : Nat), TypingProjIn R tenv G (literal_nat n) literal_nat_type
| lit_string : forall (G : ListType KExpr) (n : Nat), TypingProjIn R tenv G (literal_string n) literal_string_type
| proj : forall (G : ListType KExpr) (S : Name) (idx : Nat) (e : KExpr) (W : KExpr) (im : KIndMeta) (cm : KCtorMeta) (start : KExpr) (F : KExpr), TypingProjIn R tenv G e W -> ProjStructIn R S idx W im cm -> ProjParamsIn R (projection_ctor_type (kconst_params (kind_sig im)) (kctor_sig cm) (kexpr_const_levels (kapp_fn W))) (list_take (kctor_num_params cm) (kapp_args W)) start -> ProjFieldIn R S e Nat.zero idx start F -> TypingProjIn R tenv G (KExpr.proj S idx e) F";

/// The algorithmic relation, in CHECK mode. `proj` mirrors
/// `infer_proj_type`: infer the subject, whnf its type to the structure
/// application, then the metadata facts and the two walks.
pub(super) const INFERENCE: &str = r"inductive KernelAcceptsIn (R : RedEnv) (tenv : KDeclEnv) : ListType KExpr -> KExpr -> KExpr -> Type
| sort : forall (G : ListType KExpr) (u : Level), KernelAcceptsIn R tenv G (KExpr.sort u) (KExpr.sort (Level.succ u))
| bvar : forall (G : ListType KExpr) (i : Nat) (A : KExpr), @Eq (OptionType KExpr) (ctx_lookup G i) (@OptionType.some KExpr A) -> KernelAcceptsIn R tenv G (KExpr.bvar i) (lift_at A Nat.zero (Nat.succ i))
| pi : forall (G : ListType KExpr) (A : KExpr) (B : KExpr) (SA : KExpr) (u : Level) (SB : KExpr) (v : Level) (r : Level), KernelAcceptsIn R tenv G A SA -> par_reduces_cdp_star R SA (KExpr.sort u) -> KernelAcceptsIn R tenv (@ListType.cons KExpr A G) B SB -> par_reduces_cdp_star R SB (KExpr.sort v) -> levelEqSem (Level.imax u v) r -> KernelAcceptsIn R tenv G (KExpr.pi A B) (KExpr.sort r)
| lam : forall (G : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (SA : KExpr) (u : Level), KernelAcceptsIn R tenv G A SA -> par_reduces_cdp_star R SA (KExpr.sort u) -> KernelAcceptsIn R tenv (@ListType.cons KExpr A G) b B -> KernelAcceptsIn R tenv G (KExpr.lam A b) (KExpr.pi A B)
| const : forall (G : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr) (T : KExpr), @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A) -> KExprUniverseEq A T -> KernelAcceptsIn R tenv G (KExpr.const n us) T
| app : forall (G : ListType KExpr) (f : KExpr) (a : KExpr) (F : KExpr) (A : KExpr) (B : KExpr) (A' : KExpr), KernelAcceptsIn R tenv G f F -> par_reduces_cdp_star R F (KExpr.pi A B) -> KernelAcceptsIn R tenv G a A' -> DefEqCDPIn R A' A -> KernelAcceptsIn R tenv G (KExpr.app f a) (instantiate B a)
| let_ : forall (G : ListType KExpr) (A : KExpr) (v : KExpr) (b : KExpr) (Ty : KExpr) (u : Level) (Tv : KExpr) (B : KExpr), KernelAcceptsIn R tenv G A Ty -> par_reduces_cdp_star R Ty (KExpr.sort u) -> KernelAcceptsIn R tenv G v Tv -> DefEqCDPIn R Tv A -> KernelAcceptsIn R tenv (@ListType.cons KExpr A G) b B -> KernelAcceptsIn R tenv G (KExpr.let_ A v b) (instantiate B v)
| lit_nat : forall (G : ListType KExpr) (n : Nat), KernelAcceptsIn R tenv G (literal_nat n) literal_nat_type
| lit_string : forall (G : ListType KExpr) (n : Nat), KernelAcceptsIn R tenv G (literal_string n) literal_string_type
| proj : forall (G : ListType KExpr) (S : Name) (idx : Nat) (e : KExpr) (E : KExpr) (W : KExpr) (im : KIndMeta) (cm : KCtorMeta) (start : KExpr) (F : KExpr), KernelAcceptsIn R tenv G e E -> par_reduces_cdp_star R E W -> ProjStructIn R S idx W im cm -> ProjParamsIn R (projection_ctor_type (kconst_params (kind_sig im)) (kctor_sig cm) (kexpr_const_levels (kapp_fn W))) (list_take (kctor_num_params cm) (kapp_args W)) start -> ProjFieldIn R S e Nat.zero idx start F -> KernelAcceptsIn R tenv G (KExpr.proj S idx e) F";

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Inductive(PROJ_STRUCT),
    DeclarationInput::Inductive(PROJ_PARAMS),
    DeclarationInput::Inductive(PROJ_FIELD),
    DeclarationInput::Inductive(TYPING),
    DeclarationInput::Inductive(INFERENCE),
    DeclarationInput::Proof(
        "typing_cdp_to_proj_in",
        r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr), TypingCDPCtxConvIn R tenv G e T -> TypingProjIn R tenv G e T",
        r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr)
(h : TypingCDPCtxConvIn R tenv G e T) =>
@TypingCDPCtxConvIn.rec R tenv
  (fun (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr) (_h : TypingCDPCtxConvIn R tenv G0 e0 T0) => TypingProjIn R tenv G0 e0 T0)
  (fun (G0 : ListType KExpr) (i : Nat) (A : KExpr) (get : @Eq (OptionType KExpr) (ctx_lookup G0 i) (@OptionType.some KExpr A)) => @TypingProjIn.var R tenv G0 i A get)
  (fun (G0 : ListType KExpr) (u : Level) => @TypingProjIn.sort R tenv G0 u)
  (fun (G0 : ListType KExpr) (A : KExpr) (B : KExpr) (u : Level) (v : Level)
   (_hA : TypingCDPCtxConvIn R tenv G0 A (KExpr.sort u)) (_hB : TypingCDPCtxConvIn R tenv (@ListType.cons KExpr A G0) B (KExpr.sort v))
   (ihA : TypingProjIn R tenv G0 A (KExpr.sort u)) (ihB : TypingProjIn R tenv (@ListType.cons KExpr A G0) B (KExpr.sort v)) =>
   @TypingProjIn.pi R tenv G0 A B u v ihA ihB)
  (fun (G0 : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level)
   (_hA : TypingCDPCtxConvIn R tenv G0 A (KExpr.sort u)) (_hb : TypingCDPCtxConvIn R tenv (@ListType.cons KExpr A G0) b B)
   (ihA : TypingProjIn R tenv G0 A (KExpr.sort u)) (ihb : TypingProjIn R tenv (@ListType.cons KExpr A G0) b B) =>
   @TypingProjIn.lam R tenv G0 A b B u ihA ihb)
  (fun (G0 : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr)
   (_hf : TypingCDPCtxConvIn R tenv G0 f (KExpr.pi A B)) (_ha : TypingCDPCtxConvIn R tenv G0 a A)
   (ihf : TypingProjIn R tenv G0 f (KExpr.pi A B)) (iha : TypingProjIn R tenv G0 a A) =>
   @TypingProjIn.app R tenv G0 f a A B ihf iha)
  (fun (G0 : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr) (get : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A)) =>
   @TypingProjIn.const R tenv G0 n us A get)
  (fun (G0 : ListType KExpr) (e0 : KExpr) (A : KExpr) (B : KExpr) (_he : TypingCDPCtxConvIn R tenv G0 e0 A) (heq : DefEqCDPIn R A B)
   (ihe : TypingProjIn R tenv G0 e0 A) => @TypingProjIn.conv R tenv G0 e0 A B ihe heq)
  (fun (G0 : ListType KExpr) (A : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level)
   (_hA : TypingCDPCtxConvIn R tenv G0 A (KExpr.sort u)) (_hv : TypingCDPCtxConvIn R tenv G0 v A) (_hb : TypingCDPCtxConvIn R tenv (@ListType.cons KExpr A G0) b B)
   (ihA : TypingProjIn R tenv G0 A (KExpr.sort u)) (ihv : TypingProjIn R tenv G0 v A) (ihb : TypingProjIn R tenv (@ListType.cons KExpr A G0) b B) =>
   @TypingProjIn.let_ R tenv G0 A v b B u ihA ihv ihb)
  (fun (G0 : ListType KExpr) (n : Nat) => @TypingProjIn.lit_nat R tenv G0 n)
  (fun (G0 : ListType KExpr) (n : Nat) => @TypingProjIn.lit_string R tenv G0 n)
  G e T h",
    ),
    DeclarationInput::Proof(
        "kernel_accepts_in_sound",
        r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr), KernelAcceptsIn R tenv G e T -> TypingProjIn R tenv G e T",
        r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr)
(h : KernelAcceptsIn R tenv G e T) =>
@KernelAcceptsIn.rec R tenv
  (fun (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr)
    (_h : KernelAcceptsIn R tenv G0 e0 T0) => TypingProjIn R tenv G0 e0 T0)
  (fun (G0 : ListType KExpr) (u : Level) => @TypingProjIn.sort R tenv G0 u)
  (fun (G0 : ListType KExpr) (i : Nat) (A : KExpr)
    (get : @Eq (OptionType KExpr) (ctx_lookup G0 i) (@OptionType.some KExpr A)) =>
      @TypingProjIn.var R tenv G0 i A get)
  (fun (G0 : ListType KExpr) (A : KExpr) (B : KExpr) (SA : KExpr) (u : Level)
    (SB : KExpr) (v : Level) (r : Level)
    (_ha : KernelAcceptsIn R tenv G0 A SA) (hwa : par_reduces_cdp_star R SA (KExpr.sort u))
    (_hb : KernelAcceptsIn R tenv (@ListType.cons KExpr A G0) B SB)
    (hwb : par_reduces_cdp_star R SB (KExpr.sort v)) (hr : levelEqSem (Level.imax u v) r)
    (iha : TypingProjIn R tenv G0 A SA)
    (ihb : TypingProjIn R tenv (@ListType.cons KExpr A G0) B SB) =>
      @TypingProjIn.conv R tenv G0 (KExpr.pi A B) (KExpr.sort (Level.imax u v)) (KExpr.sort r)
        (@TypingProjIn.pi R tenv G0 A B u v
          (@TypingProjIn.conv R tenv G0 A SA (KExpr.sort u) iha (par_reduces_cdp_star_to_def_eq_cdp_in R SA (KExpr.sort u) hwa))
          (@TypingProjIn.conv R tenv (@ListType.cons KExpr A G0) B SB (KExpr.sort v) ihb (par_reduces_cdp_star_to_def_eq_cdp_in R SB (KExpr.sort v) hwb)))
        (@DefEqCDPIn.levels R (KExpr.sort (Level.imax u v)) (KExpr.sort r) (KExprUniverseEq.sort (Level.imax u v) r hr)))
  (fun (G0 : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (SA : KExpr) (u : Level)
    (_ha : KernelAcceptsIn R tenv G0 A SA) (hwa : par_reduces_cdp_star R SA (KExpr.sort u))
    (_hb : KernelAcceptsIn R tenv (@ListType.cons KExpr A G0) b B)
    (iha : TypingProjIn R tenv G0 A SA)
    (ihb : TypingProjIn R tenv (@ListType.cons KExpr A G0) b B) =>
      @TypingProjIn.lam R tenv G0 A b B u
        (@TypingProjIn.conv R tenv G0 A SA (KExpr.sort u) iha (par_reduces_cdp_star_to_def_eq_cdp_in R SA (KExpr.sort u) hwa)) ihb)
  (fun (G0 : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr) (T0 : KExpr)
    (get : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A))
    (result : KExprUniverseEq A T0) =>
      @TypingProjIn.conv R tenv G0 (KExpr.const n us) A T0
        (@TypingProjIn.const R tenv G0 n us A get) (@DefEqCDPIn.levels R A T0 result))
  (fun (G0 : ListType KExpr) (f : KExpr) (a : KExpr) (F : KExpr) (A : KExpr) (B : KExpr) (A' : KExpr)
    (_hf : KernelAcceptsIn R tenv G0 f F) (hw : par_reduces_cdp_star R F (KExpr.pi A B))
    (_ha : KernelAcceptsIn R tenv G0 a A') (heq : DefEqCDPIn R A' A)
    (ihf : TypingProjIn R tenv G0 f F) (iha : TypingProjIn R tenv G0 a A') =>
      @TypingProjIn.app R tenv G0 f a A B
        (@TypingProjIn.conv R tenv G0 f F (KExpr.pi A B) ihf (par_reduces_cdp_star_to_def_eq_cdp_in R F (KExpr.pi A B) hw))
        (@TypingProjIn.conv R tenv G0 a A' A iha heq))
  (fun (G0 : ListType KExpr) (A : KExpr) (v : KExpr) (b : KExpr) (Ty : KExpr) (u : Level) (Tv : KExpr) (B : KExpr)
    (_ht : KernelAcceptsIn R tenv G0 A Ty) (hw : par_reduces_cdp_star R Ty (KExpr.sort u))
    (_hv : KernelAcceptsIn R tenv G0 v Tv) (heq : DefEqCDPIn R Tv A)
    (_hb : KernelAcceptsIn R tenv (@ListType.cons KExpr A G0) b B)
    (iht : TypingProjIn R tenv G0 A Ty) (ihv : TypingProjIn R tenv G0 v Tv)
    (ihb : TypingProjIn R tenv (@ListType.cons KExpr A G0) b B) =>
      @TypingProjIn.let_ R tenv G0 A v b B u
        (@TypingProjIn.conv R tenv G0 A Ty (KExpr.sort u) iht (par_reduces_cdp_star_to_def_eq_cdp_in R Ty (KExpr.sort u) hw))
        (@TypingProjIn.conv R tenv G0 v Tv A ihv heq) ihb)
  (fun (G0 : ListType KExpr) (n : Nat) => @TypingProjIn.lit_nat R tenv G0 n)
  (fun (G0 : ListType KExpr) (n : Nat) => @TypingProjIn.lit_string R tenv G0 n)
  (fun (G0 : ListType KExpr) (S : Name) (idx : Nat) (e0 : KExpr) (E : KExpr) (W : KExpr)
    (im : KIndMeta) (cm : KCtorMeta) (start : KExpr) (F : KExpr)
    (_he : KernelAcceptsIn R tenv G0 e0 E) (hw : par_reduces_cdp_star R E W)
    (hs : ProjStructIn R S idx W im cm)
    (hp : ProjParamsIn R (projection_ctor_type (kconst_params (kind_sig im)) (kctor_sig cm) (kexpr_const_levels (kapp_fn W))) (list_take (kctor_num_params cm) (kapp_args W)) start)
    (hf : ProjFieldIn R S e0 Nat.zero idx start F)
    (ihe : TypingProjIn R tenv G0 e0 E) =>
      @TypingProjIn.proj R tenv G0 S idx e0 W im cm start F
        (@TypingProjIn.conv R tenv G0 e0 E W ihe (par_reduces_cdp_star_to_def_eq_cdp_in R E W hw)) hs hp hf)
  G e T h",
    ),
    DeclarationInput::Proof(
        "whnf_red_step_star_to_par_cdp_star",
        r"forall (R : RedEnv) (e : KExpr) (e2 : KExpr), whnf_red_step_star R e e2 -> par_reduces_cdp_star R e e2",
        r"fun (R : RedEnv) (e : KExpr) (e2 : KExpr) (h : whnf_red_step_star R e e2) =>
semantic_join_cdp_old_star R e e2 (whnf_red_step_star_to_par_cd_star R e e2 h)",
    ),
    DeclarationInput::Proof(
        "kernel_infers_in_to_accepts_in",
        r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr), KernelInfersIn R tenv G e T -> KernelAcceptsIn R tenv G e T",
        r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr)
(h : KernelInfersIn R tenv G e T) =>
@KernelInfersIn.rec R tenv
  (fun (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr)
    (_h : KernelInfersIn R tenv G0 e0 T0) => KernelAcceptsIn R tenv G0 e0 T0)
  (fun (G0 : ListType KExpr) (u : Level) => @KernelAcceptsIn.sort R tenv G0 u)
  (fun (G0 : ListType KExpr) (i : Nat) (A : KExpr)
    (get : @Eq (OptionType KExpr) (ctx_lookup G0 i) (@OptionType.some KExpr A)) =>
      @KernelAcceptsIn.bvar R tenv G0 i A get)
  (fun (G0 : ListType KExpr) (A : KExpr) (B : KExpr) (SA : KExpr) (u : Level)
    (SB : KExpr) (v : Level) (r : Level)
    (_ha : KernelInfersIn R tenv G0 A SA) (hwa : whnf_red_step_star R SA (KExpr.sort u))
    (_hb : KernelInfersIn R tenv (@ListType.cons KExpr A G0) B SB)
    (hwb : whnf_red_step_star R SB (KExpr.sort v)) (hr : levelEqSem (Level.imax u v) r)
    (iha : KernelAcceptsIn R tenv G0 A SA)
    (ihb : KernelAcceptsIn R tenv (@ListType.cons KExpr A G0) B SB) =>
      @KernelAcceptsIn.pi R tenv G0 A B SA u SB v r
        iha (whnf_red_step_star_to_par_cdp_star R SA (KExpr.sort u) hwa)
        ihb (whnf_red_step_star_to_par_cdp_star R SB (KExpr.sort v) hwb) hr)
  (fun (G0 : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (SA : KExpr) (u : Level)
    (_ha : KernelInfersIn R tenv G0 A SA) (hwa : whnf_red_step_star R SA (KExpr.sort u))
    (_hb : KernelInfersIn R tenv (@ListType.cons KExpr A G0) b B)
    (iha : KernelAcceptsIn R tenv G0 A SA)
    (ihb : KernelAcceptsIn R tenv (@ListType.cons KExpr A G0) b B) =>
      @KernelAcceptsIn.lam R tenv G0 A b B SA u
        iha (whnf_red_step_star_to_par_cdp_star R SA (KExpr.sort u) hwa) ihb)
  (fun (G0 : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr) (T0 : KExpr)
    (get : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A))
    (result : KExprUniverseEq A T0) =>
      @KernelAcceptsIn.const R tenv G0 n us A T0 get result)
  (fun (G0 : ListType KExpr) (f : KExpr) (a : KExpr) (F : KExpr) (A : KExpr) (B : KExpr) (A' : KExpr)
    (_hf : KernelInfersIn R tenv G0 f F) (hw : whnf_red_step_star R F (KExpr.pi A B))
    (_ha : KernelInfersIn R tenv G0 a A') (heq : DefEqIn R A' A)
    (ihf : KernelAcceptsIn R tenv G0 f F) (iha : KernelAcceptsIn R tenv G0 a A') =>
      @KernelAcceptsIn.app R tenv G0 f a F A B A'
        ihf (whnf_red_step_star_to_par_cdp_star R F (KExpr.pi A B) hw)
        iha (def_eq_in_to_cdp_in R A' A heq))
  (fun (G0 : ListType KExpr) (A : KExpr) (v : KExpr) (b : KExpr) (Ty : KExpr) (u : Level) (Tv : KExpr) (B : KExpr)
    (_ht : KernelInfersIn R tenv G0 A Ty) (hw : whnf_red_step_star R Ty (KExpr.sort u))
    (_hv : KernelInfersIn R tenv G0 v Tv) (heq : DefEqIn R Tv A)
    (_hb : KernelInfersIn R tenv (@ListType.cons KExpr A G0) b B)
    (iht : KernelAcceptsIn R tenv G0 A Ty) (ihv : KernelAcceptsIn R tenv G0 v Tv)
    (ihb : KernelAcceptsIn R tenv (@ListType.cons KExpr A G0) b B) =>
      @KernelAcceptsIn.let_ R tenv G0 A v b Ty u Tv B
        iht (whnf_red_step_star_to_par_cdp_star R Ty (KExpr.sort u) hw)
        ihv (def_eq_in_to_cdp_in R Tv A heq) ihb)
  (fun (G0 : ListType KExpr) (n : Nat) => @KernelAcceptsIn.lit_nat R tenv G0 n)
  (fun (G0 : ListType KExpr) (n : Nat) => @KernelAcceptsIn.lit_string R tenv G0 n)
  G e T h",
    ),
];
