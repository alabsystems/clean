// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Connected metadata resolution for the existing projection telescope.
//!
//! The resolver uses the subject's actual modeled WHNF, not caller-selected
//! type heads, levels, or arguments. Runtime guards and admitted-record
//! agreement remain distinct. Its typing consumer derives constructor argument
//! typings from actual whole-application typing and guarded signature lookup.
//! It adds neither projection typing nor beta reduction. In particular, the
//! relevant Prop field checks, admission soundness, and Rust refinement remain
//! open. Actual successful three-way WHNF is consumed through its independently
//! proved arbitrary-environment semantic conversion bridge.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const DATA: &[&str] = &[
    r"inductive ProjectionMetadataResult : Type
| mk : KExpr -> KIndMeta -> Name -> KCtorMeta -> KExpr -> ProjectionMetadataResult",
    r"def projection_meta_whnf (r : ProjectionMetadataResult) : KExpr :=
@ProjectionMetadataResult.rec (fun (_ : ProjectionMetadataResult) => KExpr)
 (fun (w : KExpr) (_im : KIndMeta) (_cn : Name) (_cm : KCtorMeta) (_start : KExpr) => w) r",
    r"def projection_meta_ind (r : ProjectionMetadataResult) : KIndMeta :=
@ProjectionMetadataResult.rec (fun (_ : ProjectionMetadataResult) => KIndMeta)
 (fun (_w : KExpr) (im : KIndMeta) (_cn : Name) (_cm : KCtorMeta) (_start : KExpr) => im) r",
    r"def projection_meta_ctor_name (r : ProjectionMetadataResult) : Name :=
@ProjectionMetadataResult.rec (fun (_ : ProjectionMetadataResult) => Name)
 (fun (_w : KExpr) (_im : KIndMeta) (cn : Name) (_cm : KCtorMeta) (_start : KExpr) => cn) r",
    r"def projection_meta_ctor (r : ProjectionMetadataResult) : KCtorMeta :=
@ProjectionMetadataResult.rec (fun (_ : ProjectionMetadataResult) => KCtorMeta)
 (fun (_w : KExpr) (_im : KIndMeta) (_cn : Name) (cm : KCtorMeta) (_start : KExpr) => cm) r",
    r"def projection_meta_start (r : ProjectionMetadataResult) : KExpr :=
@ProjectionMetadataResult.rec (fun (_ : ProjectionMetadataResult) => KExpr)
 (fun (_w : KExpr) (_im : KIndMeta) (_cn : Name) (_cm : KCtorMeta) (start : KExpr) => start) r",
    r"def projection_meta_levels (r : ProjectionMetadataResult) : ListType Level :=
kexpr_const_levels (kapp_fn (projection_meta_whnf r))",
    r"def projection_meta_ctor_type (r : ProjectionMetadataResult) : KExpr :=
kconst_inst_type (kctor_sig (projection_meta_ctor r)) (projection_meta_levels r)",
    r"def projection_meta_guard (A : Type) (guard : Bool) (next : OptionType A) : OptionType A :=
@Bool.rec (fun (_ : Bool) => OptionType A) (@OptionType.none A) next guard",
    r"def projection_single_ctor (xs : ListType Name) : OptionType Name :=
@ListType.rec Name (fun (_ : ListType Name) => OptionType Name) (@OptionType.none Name)
 (fun (n : Name) (tail : ListType Name) (_ih : OptionType Name) =>
  @ListType.rec Name (fun (_ : ListType Name) => OptionType Name) (@OptionType.some Name n)
   (fun (_n : Name) (_ns : ListType Name) (_ih : OptionType Name) => @OptionType.none Name) tail) xs",
    r"def projection_resolve_ctor (R : RedEnv) (fuel : Nat) (idx : Nat) (w : KExpr)
 (im : KIndMeta) (cn : Name) (cm : KCtorMeta) : OptionType ProjectionMetadataResult :=
projection_meta_guard ProjectionMetadataResult (nat_leb (Nat.succ idx) (kctor_num_fields cm))
 (opt_bind KExpr ProjectionMetadataResult
   (projection_telescope_start R fuel (kconst_params (kind_sig im)) (kctor_sig cm)
    (kctor_num_params cm) (kind_num_indices im) (kexpr_const_levels (kapp_fn w)) (kapp_args w))
   (fun (start : KExpr) => @OptionType.some ProjectionMetadataResult (ProjectionMetadataResult.mk w im cn cm start)))",
    r"def projection_resolve_ind (R : RedEnv) (fuel : Nat) (idx : Nat) (w : KExpr)
 (im : KIndMeta) : OptionType ProjectionMetadataResult :=
opt_bind Name ProjectionMetadataResult (projection_single_ctor (kind_ctor_names im))
 (fun (cn : Name) => opt_bind KCtorMeta ProjectionMetadataResult (kctor_for (red_ind_ctor R) cn)
  (projection_resolve_ctor R fuel idx w im cn))",
    r"def projection_resolve_named (R : RedEnv) (fuel : Nat) (S : Name) (idx : Nat)
 (w : KExpr) (head : Name) : OptionType ProjectionMetadataResult :=
projection_meta_guard ProjectionMetadataResult (name_eqb head S)
 (opt_bind KIndMeta ProjectionMetadataResult (kind_for (red_ind_ctor R) S)
  (projection_resolve_ind R fuel idx w))",
    r"def projection_resolve_whnf (R : RedEnv) (fuel : Nat) (S : Name) (idx : Nat)
 (w : KExpr) : OptionType ProjectionMetadataResult :=
opt_bind Name ProjectionMetadataResult (kexpr_const_name (kapp_fn w))
 (projection_resolve_named R fuel S idx w)",
    r"def projection_resolve (R : RedEnv) (fuel : Nat) (S : Name) (idx : Nat)
 (E : KExpr) : OptionType ProjectionMetadataResult :=
opt_bind KExpr ProjectionMetadataResult (whnf_fuel_red_wh3 R fuel E)
 (projection_resolve_whnf R fuel S idx)",
    r"inductive ProjectionResolution (R : RedEnv) (fuel : Nat) (S : Name) (idx : Nat)
 (E : KExpr) : ProjectionMetadataResult -> Type
| mk : forall (w : KExpr) (head : Name) (im : KIndMeta) (cn : Name) (cm : KCtorMeta) (start : KExpr),
 @Eq (OptionType KExpr) (whnf_fuel_red_wh3 R fuel E) (@OptionType.some KExpr w) ->
 @Eq (OptionType Name) (kexpr_const_name (kapp_fn w)) (@OptionType.some Name head) ->
 @Eq Bool (name_eqb head S) Bool.true ->
 @Eq (OptionType KIndMeta) (kind_for (red_ind_ctor R) S) (@OptionType.some KIndMeta im) ->
 @Eq (ListType Name) (kind_ctor_names im) (@ListType.cons Name cn (@ListType.nil Name)) ->
 @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) cn) (@OptionType.some KCtorMeta cm) ->
 @Eq Bool (nat_leb (Nat.succ idx) (kctor_num_fields cm)) Bool.true ->
 @Eq (OptionType KExpr) (projection_telescope_start R fuel (kconst_params (kind_sig im)) (kctor_sig cm)
  (kctor_num_params cm) (kind_num_indices im) (kexpr_const_levels (kapp_fn w)) (kapp_args w))
  (@OptionType.some KExpr start) ->
 ProjectionResolution R fuel S idx E (ProjectionMetadataResult.mk w im cn cm start)",
    r"inductive ProjectionMetadataAgreement (tenv : KDeclEnv) (S : Name) (r : ProjectionMetadataResult) : Type
| mk : @Eq (OptionType KConstSig) (tenv S) (@OptionType.some KConstSig (kind_sig (projection_meta_ind r))) ->
 @Eq (OptionType KConstSig) (tenv (projection_meta_ctor_name r)) (@OptionType.some KConstSig (kctor_sig (projection_meta_ctor r))) ->
 @Eq (ListType Name) (kconst_params (kind_sig (projection_meta_ind r))) (kconst_params (kctor_sig (projection_meta_ctor r))) ->
 @Eq Name (kctor_parent (projection_meta_ctor r)) S ->
 @Eq Nat (kctor_num_params (projection_meta_ctor r)) (kind_num_params (projection_meta_ind r)) ->
 @Eq Nat (kctor_index (projection_meta_ctor r)) Nat.zero -> ProjectionMetadataAgreement tenv S r",
    r"inductive ProjectionTelescopeFacts (R : RedEnv) (fuel : Nat) (r : ProjectionMetadataResult) : Type
| mk : @Eq Nat (name_list_len (kconst_params (kind_sig (projection_meta_ind r)))) (level_list_len (projection_meta_levels r)) ->
 @Eq Nat (Nat.add (kctor_num_params (projection_meta_ctor r)) (kind_num_indices (projection_meta_ind r))) (list_length (kapp_args (projection_meta_whnf r))) ->
 ProjectionParameterGraph R fuel
  (projection_ctor_type (kconst_params (kind_sig (projection_meta_ind r))) (kctor_sig (projection_meta_ctor r)) (projection_meta_levels r))
  (list_take (kctor_num_params (projection_meta_ctor r)) (kapp_args (projection_meta_whnf r))) (projection_meta_start r) ->
 ProjectionTelescopeFacts R fuel r",
    r"inductive ProjectionSubjectReady (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
 (fuel : Nat) (S : Name) (idx : Nat) (e : KExpr) (E : KExpr) (result : ProjectionMetadataResult) : Type
| mk : KernelInfersIn R tenv G e E -> ProjectionResolution R fuel S idx E result ->
 forall (sortType : KExpr) (u : Level), KernelInfersIn R tenv G (projection_meta_whnf result) sortType ->
 @Eq (OptionType KExpr) (whnf_fuel_red_wh3 R fuel sortType) (@OptionType.some KExpr (KExpr.sort u)) ->
 ProjectionSubjectReady R tenv G fuel S idx e E result",
    r"inductive ProjectionSubjectSemantics (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
 (e : KExpr) (E : KExpr) (r : ProjectionMetadataResult) : Type
| mk : forall (u : Level), DefEqIn R E (projection_meta_whnf r) ->
 TypingCtxConvIn R tenv G e (projection_meta_whnf r) ->
 TypingCtxConvIn R tenv G (projection_meta_whnf r) (KExpr.sort u) ->
 ProjectionSubjectSemantics R tenv G e E r",
];

const CONTROL_DATA: &[&str] = &[
    r"def projection_metadata_control_cn : Name := Name.str Name.anonymous Nat.zero",
    r"def projection_metadata_control_sig : KConstSig := KConstSig.mk (@ListType.nil Name)
 (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.const Name.anonymous (@ListType.nil Level)))",
    r"def projection_metadata_control_ind : KIndMeta := KIndMeta.mk
 (KConstSig.mk (@ListType.nil Name) (KExpr.sort (Level.succ (Level.succ Level.zero)))) Nat.zero Nat.zero
 (@ListType.cons Name projection_metadata_control_cn (@ListType.nil Name))
 (@ListType.cons Name Name.anonymous (@ListType.nil Name))",
    r"def projection_metadata_control_ctor : KCtorMeta := KCtorMeta.mk projection_metadata_control_sig Name.anonymous Nat.zero (Nat.succ Nat.zero) Nat.zero",
    r"def projection_metadata_control_env : RedEnv := RedEnv.mk RecEnv.empty DefEnv.empty
 (IndCtorEnv.addCtor (IndCtorEnv.addInd IndCtorEnv.empty Name.anonymous projection_metadata_control_ind)
  projection_metadata_control_cn projection_metadata_control_ctor)",
    r"def projection_metadata_control_type : KExpr := KExpr.const Name.anonymous (@ListType.nil Level)",
    r"def projection_metadata_control_result : ProjectionMetadataResult :=
 ProjectionMetadataResult.mk projection_metadata_control_type projection_metadata_control_ind projection_metadata_control_cn
 projection_metadata_control_ctor (kconst_type projection_metadata_control_sig)",
    r"def projection_metadata_control_tenv : KDeclEnv := fun (n : Name) =>
 opt_pick KConstSig (name_eqb n projection_metadata_control_cn) projection_metadata_control_sig
 (opt_pick KConstSig (name_eqb n Name.anonymous) (kind_sig projection_metadata_control_ind) (@OptionType.none KConstSig))",
    r"def projection_metadata_wrong_parent_ctor : KCtorMeta := KCtorMeta.mk projection_metadata_control_sig projection_metadata_control_cn Nat.zero (Nat.succ Nat.zero) Nat.zero",
    r"def projection_metadata_wrong_parent_env : RedEnv := RedEnv.mk RecEnv.empty DefEnv.empty
 (IndCtorEnv.addCtor (IndCtorEnv.addInd IndCtorEnv.empty Name.anonymous projection_metadata_control_ind)
  projection_metadata_control_cn projection_metadata_wrong_parent_ctor)",
    r"def projection_metadata_wrong_parent_result : ProjectionMetadataResult :=
 ProjectionMetadataResult.mk projection_metadata_control_type projection_metadata_control_ind projection_metadata_control_cn
 projection_metadata_wrong_parent_ctor (kconst_type projection_metadata_control_sig)",
];

// These are only convenient views of the emitted application and signatures.
// The proof records check the expected telescope against actual source data;
// no constructor/inductive metadata or Name tag is handwritten here.
const GENERATED_DATA: &[&str] = &[
    r"def projection_prod_sort : KExpr := KExpr.sort (Level.succ Level.zero)",
    r"def projection_prod_family : KExpr := KExpr.const kcre_prod_type_name (@ListType.nil Level)",
    r"def projection_prod_ctor : KExpr := KExpr.const kcre_prod_mk_name (@ListType.nil Level)",
    r"def projection_prod_ctor_tail : KExpr := KExpr.pi projection_prod_sort
 (KExpr.pi (KExpr.bvar (Nat.succ Nat.zero))
  (KExpr.pi (KExpr.bvar (Nat.succ Nat.zero))
   (KExpr.app (KExpr.app projection_prod_family (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))))",
    r"def projection_prod_after_A : KExpr := KExpr.pi projection_prod_sort
 (KExpr.pi rfnz_nat (KExpr.pi (KExpr.bvar (Nat.succ Nat.zero))
  (KExpr.app (KExpr.app projection_prod_family rfnz_nat) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))))",
    r"def projection_prod_field_telescope : KExpr := KExpr.pi rfnz_nat (KExpr.pi rfnz_nat kcre_witness_prod_type)",
    r"def projection_prod_args : ListType KExpr := @ListType.cons KExpr rfnz_nat
 (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr rfnz_zero
  (@ListType.cons KExpr (KExpr.app rfnz_succ rfnz_zero) (@ListType.nil KExpr))))",
    r"def projection_prod_result : ProjectionMetadataResult := ProjectionMetadataResult.mk
 kcre_witness_prod_type kcre_prod_ind_meta kcre_prod_mk_name kcre_prod_ctor_meta projection_prod_field_telescope",
];

// Explicit static theorem records: add_definition checks each real term before
// assigning DerivedProved. No output-typing or output-conversion axiom is added.
const PROOFS: &[(&str, &str, &str)] = &[
    (
        "projection_substL_identity",
        r"forall (u : Level), @Eq Level (substL (fun (n : Name) => Level.param n) u) u",
        r"fun (u : Level) => @Level.rec (fun (v : Level) => @Eq Level (substL (fun (n : Name) => Level.param n) v) v)
 (@Eq.refl Level Level.zero)
 (fun (v : Level) (ih : @Eq Level (substL (fun (n : Name) => Level.param n) v) v) => Eq.cong Level Level (fun (x : Level) => Level.succ x) (substL (fun (n : Name) => Level.param n) v) v ih)
 (fun (a : Level) (b : Level) (ha : @Eq Level (substL (fun (n : Name) => Level.param n) a) a) (hb : @Eq Level (substL (fun (n : Name) => Level.param n) b) b) =>
 universe_bridge_congr2 Level Level Level (fun (x : Level) (y : Level) => Level.max x y) (substL (fun (n : Name) => Level.param n) a) a (substL (fun (n : Name) => Level.param n) b) b ha hb)
 (fun (a : Level) (b : Level) (ha : @Eq Level (substL (fun (n : Name) => Level.param n) a) a) (hb : @Eq Level (substL (fun (n : Name) => Level.param n) b) b) =>
 universe_bridge_congr2 Level Level Level (fun (x : Level) (y : Level) => Level.imax x y) (substL (fun (n : Name) => Level.param n) a) a (substL (fun (n : Name) => Level.param n) b) b ha hb)
 (fun (n : Name) => @Eq.refl Level (Level.param n)) u",
    ),
    (
        "projection_mapLL_identity",
        r"forall (us : ListType Level), @Eq (ListType Level) (mapLL (substL (fun (n : Name) => Level.param n)) us) us",
        r"fun (us : ListType Level) => @ListType.rec Level (fun (xs : ListType Level) => @Eq (ListType Level) (mapLL (substL (fun (n : Name) => Level.param n)) xs) xs)
 (@Eq.refl (ListType Level) (@ListType.nil Level))
 (fun (u : Level) (xs : ListType Level) (ih : @Eq (ListType Level) (mapLL (substL (fun (n : Name) => Level.param n)) xs) xs) =>
 universe_bridge_congr2 Level (ListType Level) (ListType Level) (fun (v : Level) (vs : ListType Level) => @ListType.cons Level v vs)
 (substL (fun (n : Name) => Level.param n) u) u (mapLL (substL (fun (n : Name) => Level.param n)) xs) xs (projection_substL_identity u) ih) us",
    ),
    (
        "projection_instL_identity",
        r"forall (e : KExpr), @Eq KExpr (instL (fun (n : Name) => Level.param n) e) e",
        r"fun (e : KExpr) => @KExpr.rec (fun (t : KExpr) => @Eq KExpr (instL (fun (n : Name) => Level.param n) t) t)
 (fun (u : Level) => Eq.cong Level KExpr (fun (v : Level) => KExpr.sort v) (substL (fun (n : Name) => Level.param n) u) u (projection_substL_identity u))
 (fun (i : Nat) => @Eq.refl KExpr (KExpr.bvar i))
 (fun (f : KExpr) (a : KExpr) (hf : @Eq KExpr (instL (fun (n : Name) => Level.param n) f) f) (ha : @Eq KExpr (instL (fun (n : Name) => Level.param n) a) a) =>
 universe_bridge_congr2 KExpr KExpr KExpr (fun (x : KExpr) (y : KExpr) => KExpr.app x y) (instL (fun (n : Name) => Level.param n) f) f (instL (fun (n : Name) => Level.param n) a) a hf ha)
 (fun (A : KExpr) (b : KExpr) (hA : @Eq KExpr (instL (fun (n : Name) => Level.param n) A) A) (hb : @Eq KExpr (instL (fun (n : Name) => Level.param n) b) b) =>
 universe_bridge_congr2 KExpr KExpr KExpr (fun (x : KExpr) (y : KExpr) => KExpr.lam x y) (instL (fun (n : Name) => Level.param n) A) A (instL (fun (n : Name) => Level.param n) b) b hA hb)
 (fun (A : KExpr) (B : KExpr) (hA : @Eq KExpr (instL (fun (n : Name) => Level.param n) A) A) (hB : @Eq KExpr (instL (fun (n : Name) => Level.param n) B) B) =>
 universe_bridge_congr2 KExpr KExpr KExpr (fun (x : KExpr) (y : KExpr) => KExpr.pi x y) (instL (fun (n : Name) => Level.param n) A) A (instL (fun (n : Name) => Level.param n) B) B hA hB)
 (fun (n : Name) (us : ListType Level) => Eq.cong (ListType Level) KExpr (fun (vs : ListType Level) => KExpr.const n vs) (mapLL (substL (fun (nm : Name) => Level.param nm)) us) us (projection_mapLL_identity us))
 (fun (A : KExpr) (v : KExpr) (b : KExpr) (hA : @Eq KExpr (instL (fun (n : Name) => Level.param n) A) A) (hv : @Eq KExpr (instL (fun (n : Name) => Level.param n) v) v) (hb : @Eq KExpr (instL (fun (n : Name) => Level.param n) b) b) =>
 Eq.trans KExpr (KExpr.let_ (instL (fun (n : Name) => Level.param n) A) (instL (fun (n : Name) => Level.param n) v) (instL (fun (n : Name) => Level.param n) b))
 (KExpr.let_ A v (instL (fun (n : Name) => Level.param n) b)) (KExpr.let_ A v b)
 (universe_bridge_congr2 KExpr KExpr KExpr (fun (x : KExpr) (y : KExpr) => KExpr.let_ x y (instL (fun (n : Name) => Level.param n) b))
  (instL (fun (n : Name) => Level.param n) A) A (instL (fun (n : Name) => Level.param n) v) v hA hv)
 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.let_ A v x) (instL (fun (n : Name) => Level.param n) b) b hb))
 (fun (S : Name) (i : Nat) (e0 : KExpr) (ih : @Eq KExpr (instL (fun (n : Name) => Level.param n) e0) e0) => Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.proj S i x) (instL (fun (n : Name) => Level.param n) e0) e0 ih)
 (fun (n : Nat) => @Eq.refl KExpr (KExpr.lit n)) e",
    ),
    (
        "projection_ctor_type_instantiation",
        r"forall (ps : ListType Name) (sig : KConstSig) (us : ListType Level),
 @Eq KExpr (projection_ctor_type ps sig us) (instLevels ps (kconst_type sig) us)",
        r"fun (ps : ListType Name) (sig : KConstSig) (us : ListType Level) =>
@ListType.rec Name (fun (qs : ListType Name) => @Eq KExpr (projection_ctor_type qs sig us) (instLevels qs (kconst_type sig) us))
 (Eq.symm KExpr (instL (fun (n : Name) => Level.param n) (kconst_type sig)) (kconst_type sig) (projection_instL_identity (kconst_type sig)))
 (fun (p : Name) (qs : ListType Name) (_ih : @Eq KExpr (projection_ctor_type qs sig us) (instLevels qs (kconst_type sig) us)) => @Eq.refl KExpr (instLevels (@ListType.cons Name p qs) (kconst_type sig) us)) ps",
    ),
    (
        "projection_ctor_type_coherent",
        r"forall (ps : ListType Name) (sig : KConstSig) (us : ListType Level), ProjectionUniverseCoherence ps sig ->
 @Eq KExpr (projection_ctor_type ps sig us) (kconst_inst_type sig us)",
        r"fun (ps : ListType Name) (sig : KConstSig) (us : ListType Level) (ordered : ProjectionUniverseCoherence ps sig) =>
Eq.trans KExpr (projection_ctor_type ps sig us) (instLevels ps (kconst_type sig) us) (kconst_inst_type sig us)
 (projection_ctor_type_instantiation ps sig us) (projection_ordered_instantiation_coherent ps sig us ordered)",
    ),
    (
        "projection_const_infers",
        r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (n : Name) (us : ListType Level) (F : KExpr),
 @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr F) -> KernelInfersIn R tenv G (KExpr.const n us) F",
        r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (n : Name) (us : ListType Level) (F : KExpr)
 (lookup : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr F)) =>
 @KernelInfersIn.const R tenv G n us F F lookup (kexprUniverseEq_refl F)",
    ),
    (
        "projection_app_infers_raw",
        r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr),
 KernelInfersIn R tenv G f (KExpr.pi A B) -> KernelInfersIn R tenv G a A -> KernelInfersIn R tenv G (KExpr.app f a) (instantiate B a)",
        r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr)
 (hf : KernelInfersIn R tenv G f (KExpr.pi A B)) (ha : KernelInfersIn R tenv G a A) =>
 @KernelInfersIn.app R tenv G f a (KExpr.pi A B) A B A hf (@whnf_red_step_star.refl R (KExpr.pi A B)) ha (@DefEqIn.refl R A)",
    ),
    (
        "projection_single_ctor_inv",
        r"forall (xs : ListType Name) (cn : Name), @Eq (OptionType Name) (projection_single_ctor xs) (@OptionType.some Name cn) ->
 @Eq (ListType Name) xs (@ListType.cons Name cn (@ListType.nil Name))",
        r"fun (xs : ListType Name) => @ListType.rec Name
 (fun (ys : ListType Name) => forall (cn : Name), @Eq (OptionType Name) (projection_single_ctor ys) (@OptionType.some Name cn) -> @Eq (ListType Name) ys (@ListType.cons Name cn (@ListType.nil Name)))
 (fun (cn : Name) (h : @Eq (OptionType Name) (@OptionType.none Name) (@OptionType.some Name cn)) => option_none_ne_some Name cn (@Eq (ListType Name) (@ListType.nil Name) (@ListType.cons Name cn (@ListType.nil Name))) h)
 (fun (n : Name) (tail : ListType Name) (_ih : forall (cn : Name), @Eq (OptionType Name) (projection_single_ctor tail) (@OptionType.some Name cn) -> @Eq (ListType Name) tail (@ListType.cons Name cn (@ListType.nil Name))) =>
  @ListType.rec Name (fun (ts : ListType Name) => forall (cn : Name), @Eq (OptionType Name) (projection_single_ctor (@ListType.cons Name n ts)) (@OptionType.some Name cn) -> @Eq (ListType Name) (@ListType.cons Name n ts) (@ListType.cons Name cn (@ListType.nil Name)))
   (fun (cn : Name) (h : @Eq (OptionType Name) (@OptionType.some Name n) (@OptionType.some Name cn)) => Eq.cong Name (ListType Name) (fun (x : Name) => @ListType.cons Name x (@ListType.nil Name)) n cn (option_some_inj Name n cn h))
   (fun (n2 : Name) (ts : ListType Name) (_ih2 : forall (cn : Name), @Eq (OptionType Name) (projection_single_ctor (@ListType.cons Name n ts)) (@OptionType.some Name cn) -> @Eq (ListType Name) (@ListType.cons Name n ts) (@ListType.cons Name cn (@ListType.nil Name)))
    (cn : Name) (h : @Eq (OptionType Name) (@OptionType.none Name) (@OptionType.some Name cn)) => option_none_ne_some Name cn (@Eq (ListType Name) (@ListType.cons Name n (@ListType.cons Name n2 ts)) (@ListType.cons Name cn (@ListType.nil Name))) h) tail) xs",
    ),
    (
        "projection_single_ctor_intro",
        r"forall (xs : ListType Name) (cn : Name), @Eq (ListType Name) xs (@ListType.cons Name cn (@ListType.nil Name)) ->
 @Eq (OptionType Name) (projection_single_ctor xs) (@OptionType.some Name cn)",
        r"fun (xs : ListType Name) (cn : Name) (h : @Eq (ListType Name) xs (@ListType.cons Name cn (@ListType.nil Name))) =>
Eq.cong (ListType Name) (OptionType Name) projection_single_ctor xs (@ListType.cons Name cn (@ListType.nil Name)) h",
    ),
    (
        "projection_meta_guard_inv",
        r"forall (A : Type) (guard : Bool) (next : OptionType A) (out : A) (C : Type),
 @Eq (OptionType A) (projection_meta_guard A guard next) (@OptionType.some A out) ->
 (@Eq Bool guard Bool.true -> @Eq (OptionType A) next (@OptionType.some A out) -> C) -> C",
        r"fun (A : Type) (guard : Bool) (next : OptionType A) (out : A) (C : Type) =>
@Bool.rec (fun (b : Bool) => @Eq (OptionType A) (projection_meta_guard A b next) (@OptionType.some A out) ->
 (@Eq Bool b Bool.true -> @Eq (OptionType A) next (@OptionType.some A out) -> C) -> C)
 (fun (h : @Eq (OptionType A) (@OptionType.none A) (@OptionType.some A out)) (_k : @Eq Bool Bool.false Bool.true -> @Eq (OptionType A) next (@OptionType.some A out) -> C) => option_none_ne_some_type A out C h)
 (fun (h : @Eq (OptionType A) next (@OptionType.some A out)) (k : @Eq Bool Bool.true Bool.true -> @Eq (OptionType A) next (@OptionType.some A out) -> C) => k (@Eq.refl Bool Bool.true) h) guard",
    ),
    (
        "projection_meta_guard_intro",
        r"forall (A : Type) (guard : Bool) (next : OptionType A) (out : A),
 @Eq Bool guard Bool.true -> @Eq (OptionType A) next (@OptionType.some A out) ->
 @Eq (OptionType A) (projection_meta_guard A guard next) (@OptionType.some A out)",
        r"fun (A : Type) (guard : Bool) (next : OptionType A) (out : A) (hg : @Eq Bool guard Bool.true) (hn : @Eq (OptionType A) next (@OptionType.some A out)) =>
Eq.trans (OptionType A) (projection_meta_guard A guard next) next (@OptionType.some A out)
 (Eq.cong Bool (OptionType A) (fun (b : Bool) => projection_meta_guard A b next) guard Bool.true hg) hn",
    ),
    (
        "projection_meta_bind_intro",
        r"forall (A : Type) (B : Type) (o : OptionType A) (f : A -> OptionType B) (a : A) (b : B),
 @Eq (OptionType A) o (@OptionType.some A a) -> @Eq (OptionType B) (f a) (@OptionType.some B b) ->
 @Eq (OptionType B) (opt_bind A B o f) (@OptionType.some B b)",
        r"fun (A : Type) (B : Type) (o : OptionType A) (f : A -> OptionType B) (a : A) (b : B)
 (ho : @Eq (OptionType A) o (@OptionType.some A a)) (hf : @Eq (OptionType B) (f a) (@OptionType.some B b)) =>
Eq.trans (OptionType B) (opt_bind A B o f) (f a) (@OptionType.some B b)
 (Eq.cong (OptionType A) (OptionType B) (fun (x : OptionType A) => opt_bind A B x f) o (@OptionType.some A a) ho) hf",
    ),
    (
        "projection_resolve_ctor_inv",
        r"forall (R : RedEnv) (fuel : Nat) (idx : Nat) (w : KExpr) (im : KIndMeta) (cn : Name) (cm : KCtorMeta) (out : ProjectionMetadataResult) (C : Type),
 @Eq (OptionType ProjectionMetadataResult) (projection_resolve_ctor R fuel idx w im cn cm) (@OptionType.some ProjectionMetadataResult out) ->
 (forall (start : KExpr), @Eq Bool (nat_leb (Nat.succ idx) (kctor_num_fields cm)) Bool.true ->
  @Eq (OptionType KExpr) (projection_telescope_start R fuel (kconst_params (kind_sig im)) (kctor_sig cm) (kctor_num_params cm) (kind_num_indices im) (kexpr_const_levels (kapp_fn w)) (kapp_args w)) (@OptionType.some KExpr start) ->
  @Eq ProjectionMetadataResult (ProjectionMetadataResult.mk w im cn cm start) out -> C) -> C",
        r"fun (R : RedEnv) (fuel : Nat) (idx : Nat) (w : KExpr) (im : KIndMeta) (cn : Name) (cm : KCtorMeta) (out : ProjectionMetadataResult) (C : Type)
 (h : @Eq (OptionType ProjectionMetadataResult) (projection_resolve_ctor R fuel idx w im cn cm) (@OptionType.some ProjectionMetadataResult out))
 (k : forall (start : KExpr), @Eq Bool (nat_leb (Nat.succ idx) (kctor_num_fields cm)) Bool.true ->
  @Eq (OptionType KExpr) (projection_telescope_start R fuel (kconst_params (kind_sig im)) (kctor_sig cm) (kctor_num_params cm) (kind_num_indices im) (kexpr_const_levels (kapp_fn w)) (kapp_args w)) (@OptionType.some KExpr start) -> @Eq ProjectionMetadataResult (ProjectionMetadataResult.mk w im cn cm start) out -> C) =>
projection_meta_guard_inv ProjectionMetadataResult (nat_leb (Nat.succ idx) (kctor_num_fields cm))
 (opt_bind KExpr ProjectionMetadataResult (projection_telescope_start R fuel (kconst_params (kind_sig im)) (kctor_sig cm) (kctor_num_params cm) (kind_num_indices im) (kexpr_const_levels (kapp_fn w)) (kapp_args w))
  (fun (start : KExpr) => @OptionType.some ProjectionMetadataResult (ProjectionMetadataResult.mk w im cn cm start))) out C h
 (fun (hg : @Eq Bool (nat_leb (Nat.succ idx) (kctor_num_fields cm)) Bool.true)
  (ht : @Eq (OptionType ProjectionMetadataResult) (opt_bind KExpr ProjectionMetadataResult (projection_telescope_start R fuel (kconst_params (kind_sig im)) (kctor_sig cm) (kctor_num_params cm) (kind_num_indices im) (kexpr_const_levels (kapp_fn w)) (kapp_args w)) (fun (start : KExpr) => @OptionType.some ProjectionMetadataResult (ProjectionMetadataResult.mk w im cn cm start))) (@OptionType.some ProjectionMetadataResult out)) =>
  opt_bind_some_inv_type KExpr ProjectionMetadataResult
   (projection_telescope_start R fuel (kconst_params (kind_sig im)) (kctor_sig cm) (kctor_num_params cm) (kind_num_indices im) (kexpr_const_levels (kapp_fn w)) (kapp_args w))
   (fun (start : KExpr) => @OptionType.some ProjectionMetadataResult (ProjectionMetadataResult.mk w im cn cm start)) out C ht
   (fun (start : KExpr) (hs : @Eq (OptionType KExpr) (projection_telescope_start R fuel (kconst_params (kind_sig im)) (kctor_sig cm) (kctor_num_params cm) (kind_num_indices im) (kexpr_const_levels (kapp_fn w)) (kapp_args w)) (@OptionType.some KExpr start))
    (he : @Eq (OptionType ProjectionMetadataResult) (@OptionType.some ProjectionMetadataResult (ProjectionMetadataResult.mk w im cn cm start)) (@OptionType.some ProjectionMetadataResult out)) =>
    k start hg hs (option_some_inj ProjectionMetadataResult (ProjectionMetadataResult.mk w im cn cm start) out he)))",
    ),
    (
        "projection_resolve_trace",
        r"forall (R : RedEnv) (fuel : Nat) (S : Name) (idx : Nat) (E : KExpr) (out : ProjectionMetadataResult),
 @Eq (OptionType ProjectionMetadataResult) (projection_resolve R fuel S idx E) (@OptionType.some ProjectionMetadataResult out) ->
 ProjectionResolution R fuel S idx E out",
        r"fun (R : RedEnv) (fuel : Nat) (S : Name) (idx : Nat) (E : KExpr) (out : ProjectionMetadataResult)
 (h : @Eq (OptionType ProjectionMetadataResult) (projection_resolve R fuel S idx E) (@OptionType.some ProjectionMetadataResult out)) =>
opt_bind_some_inv_type KExpr ProjectionMetadataResult (whnf_fuel_red_wh3 R fuel E) (projection_resolve_whnf R fuel S idx) out (ProjectionResolution R fuel S idx E out) h
 (fun (w : KExpr) (hw : @Eq (OptionType KExpr) (whnf_fuel_red_wh3 R fuel E) (@OptionType.some KExpr w))
  (h1 : @Eq (OptionType ProjectionMetadataResult) (projection_resolve_whnf R fuel S idx w) (@OptionType.some ProjectionMetadataResult out)) =>
 opt_bind_some_inv_type Name ProjectionMetadataResult (kexpr_const_name (kapp_fn w)) (projection_resolve_named R fuel S idx w) out (ProjectionResolution R fuel S idx E out) h1
 (fun (head : Name) (hh : @Eq (OptionType Name) (kexpr_const_name (kapp_fn w)) (@OptionType.some Name head))
  (h2 : @Eq (OptionType ProjectionMetadataResult) (projection_resolve_named R fuel S idx w head) (@OptionType.some ProjectionMetadataResult out)) =>
 projection_meta_guard_inv ProjectionMetadataResult (name_eqb head S)
  (opt_bind KIndMeta ProjectionMetadataResult (kind_for (red_ind_ctor R) S) (projection_resolve_ind R fuel idx w)) out (ProjectionResolution R fuel S idx E out) h2
 (fun (hn : @Eq Bool (name_eqb head S) Bool.true)
  (h3 : @Eq (OptionType ProjectionMetadataResult) (opt_bind KIndMeta ProjectionMetadataResult (kind_for (red_ind_ctor R) S) (projection_resolve_ind R fuel idx w)) (@OptionType.some ProjectionMetadataResult out)) =>
 opt_bind_some_inv_type KIndMeta ProjectionMetadataResult (kind_for (red_ind_ctor R) S) (projection_resolve_ind R fuel idx w) out (ProjectionResolution R fuel S idx E out) h3
 (fun (im : KIndMeta) (hi : @Eq (OptionType KIndMeta) (kind_for (red_ind_ctor R) S) (@OptionType.some KIndMeta im))
  (h4 : @Eq (OptionType ProjectionMetadataResult) (projection_resolve_ind R fuel idx w im) (@OptionType.some ProjectionMetadataResult out)) =>
 opt_bind_some_inv_type Name ProjectionMetadataResult (projection_single_ctor (kind_ctor_names im))
  (fun (cn : Name) => opt_bind KCtorMeta ProjectionMetadataResult (kctor_for (red_ind_ctor R) cn) (projection_resolve_ctor R fuel idx w im cn)) out (ProjectionResolution R fuel S idx E out) h4
 (fun (cn : Name) (hc : @Eq (OptionType Name) (projection_single_ctor (kind_ctor_names im)) (@OptionType.some Name cn))
  (h5 : @Eq (OptionType ProjectionMetadataResult) (opt_bind KCtorMeta ProjectionMetadataResult (kctor_for (red_ind_ctor R) cn) (projection_resolve_ctor R fuel idx w im cn)) (@OptionType.some ProjectionMetadataResult out)) =>
 opt_bind_some_inv_type KCtorMeta ProjectionMetadataResult (kctor_for (red_ind_ctor R) cn) (projection_resolve_ctor R fuel idx w im cn) out (ProjectionResolution R fuel S idx E out) h5
 (fun (cm : KCtorMeta) (hk : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) cn) (@OptionType.some KCtorMeta cm))
  (h6 : @Eq (OptionType ProjectionMetadataResult) (projection_resolve_ctor R fuel idx w im cn cm) (@OptionType.some ProjectionMetadataResult out)) =>
 projection_resolve_ctor_inv R fuel idx w im cn cm out (ProjectionResolution R fuel S idx E out) h6
 (fun (start : KExpr) (hf : @Eq Bool (nat_leb (Nat.succ idx) (kctor_num_fields cm)) Bool.true)
  (hs : @Eq (OptionType KExpr) (projection_telescope_start R fuel (kconst_params (kind_sig im)) (kctor_sig cm) (kctor_num_params cm) (kind_num_indices im) (kexpr_const_levels (kapp_fn w)) (kapp_args w)) (@OptionType.some KExpr start))
  (he : @Eq ProjectionMetadataResult (ProjectionMetadataResult.mk w im cn cm start) out) =>
 Eq.substType ProjectionMetadataResult (fun (r : ProjectionMetadataResult) => ProjectionResolution R fuel S idx E r)
  (ProjectionMetadataResult.mk w im cn cm start) out he
  (@ProjectionResolution.mk R fuel S idx E w head im cn cm start hw hh hn hi (projection_single_ctor_inv (kind_ctor_names im) cn hc) hk hf hs))))))))",
    ),
    (
        "projection_resolve_intro",
        r"forall (R : RedEnv) (fuel : Nat) (S : Name) (idx : Nat) (E : KExpr)
 (w : KExpr) (head : Name) (im : KIndMeta) (cn : Name) (cm : KCtorMeta) (start : KExpr),
 @Eq (OptionType KExpr) (whnf_fuel_red_wh3 R fuel E) (@OptionType.some KExpr w) ->
 @Eq (OptionType Name) (kexpr_const_name (kapp_fn w)) (@OptionType.some Name head) -> @Eq Bool (name_eqb head S) Bool.true ->
 @Eq (OptionType KIndMeta) (kind_for (red_ind_ctor R) S) (@OptionType.some KIndMeta im) ->
 @Eq (ListType Name) (kind_ctor_names im) (@ListType.cons Name cn (@ListType.nil Name)) ->
 @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) cn) (@OptionType.some KCtorMeta cm) ->
 @Eq Bool (nat_leb (Nat.succ idx) (kctor_num_fields cm)) Bool.true ->
 @Eq (OptionType KExpr) (projection_telescope_start R fuel (kconst_params (kind_sig im)) (kctor_sig cm) (kctor_num_params cm) (kind_num_indices im) (kexpr_const_levels (kapp_fn w)) (kapp_args w)) (@OptionType.some KExpr start) ->
 @Eq (OptionType ProjectionMetadataResult) (projection_resolve R fuel S idx E) (@OptionType.some ProjectionMetadataResult (ProjectionMetadataResult.mk w im cn cm start))",
        r"fun (R : RedEnv) (fuel : Nat) (S : Name) (idx : Nat) (E : KExpr)
 (w : KExpr) (head : Name) (im : KIndMeta) (cn : Name) (cm : KCtorMeta) (start : KExpr)
 (hw : @Eq (OptionType KExpr) (whnf_fuel_red_wh3 R fuel E) (@OptionType.some KExpr w))
 (hh : @Eq (OptionType Name) (kexpr_const_name (kapp_fn w)) (@OptionType.some Name head)) (hn : @Eq Bool (name_eqb head S) Bool.true)
 (hi : @Eq (OptionType KIndMeta) (kind_for (red_ind_ctor R) S) (@OptionType.some KIndMeta im))
 (hc : @Eq (ListType Name) (kind_ctor_names im) (@ListType.cons Name cn (@ListType.nil Name)))
 (hk : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) cn) (@OptionType.some KCtorMeta cm))
 (hf : @Eq Bool (nat_leb (Nat.succ idx) (kctor_num_fields cm)) Bool.true)
 (hs : @Eq (OptionType KExpr) (projection_telescope_start R fuel (kconst_params (kind_sig im)) (kctor_sig cm) (kctor_num_params cm) (kind_num_indices im) (kexpr_const_levels (kapp_fn w)) (kapp_args w)) (@OptionType.some KExpr start)) =>
projection_meta_bind_intro KExpr ProjectionMetadataResult (whnf_fuel_red_wh3 R fuel E) (projection_resolve_whnf R fuel S idx) w (ProjectionMetadataResult.mk w im cn cm start) hw
 (projection_meta_bind_intro Name ProjectionMetadataResult (kexpr_const_name (kapp_fn w)) (projection_resolve_named R fuel S idx w) head (ProjectionMetadataResult.mk w im cn cm start) hh
 (projection_meta_guard_intro ProjectionMetadataResult (name_eqb head S)
  (opt_bind KIndMeta ProjectionMetadataResult (kind_for (red_ind_ctor R) S) (projection_resolve_ind R fuel idx w)) (ProjectionMetadataResult.mk w im cn cm start) hn
 (projection_meta_bind_intro KIndMeta ProjectionMetadataResult (kind_for (red_ind_ctor R) S) (projection_resolve_ind R fuel idx w) im (ProjectionMetadataResult.mk w im cn cm start) hi
 (projection_meta_bind_intro Name ProjectionMetadataResult (projection_single_ctor (kind_ctor_names im))
  (fun (cn0 : Name) => opt_bind KCtorMeta ProjectionMetadataResult (kctor_for (red_ind_ctor R) cn0) (projection_resolve_ctor R fuel idx w im cn0)) cn (ProjectionMetadataResult.mk w im cn cm start)
  (projection_single_ctor_intro (kind_ctor_names im) cn hc)
 (projection_meta_bind_intro KCtorMeta ProjectionMetadataResult (kctor_for (red_ind_ctor R) cn) (projection_resolve_ctor R fuel idx w im cn) cm (ProjectionMetadataResult.mk w im cn cm start) hk
 (projection_meta_guard_intro ProjectionMetadataResult (nat_leb (Nat.succ idx) (kctor_num_fields cm))
  (opt_bind KExpr ProjectionMetadataResult (projection_telescope_start R fuel (kconst_params (kind_sig im)) (kctor_sig cm) (kctor_num_params cm) (kind_num_indices im) (kexpr_const_levels (kapp_fn w)) (kapp_args w)) (fun (start0 : KExpr) => @OptionType.some ProjectionMetadataResult (ProjectionMetadataResult.mk w im cn cm start0))) (ProjectionMetadataResult.mk w im cn cm start) hf
 (projection_meta_bind_intro KExpr ProjectionMetadataResult (projection_telescope_start R fuel (kconst_params (kind_sig im)) (kctor_sig cm) (kctor_num_params cm) (kind_num_indices im) (kexpr_const_levels (kapp_fn w)) (kapp_args w))
  (fun (start0 : KExpr) => @OptionType.some ProjectionMetadataResult (ProjectionMetadataResult.mk w im cn cm start0)) start (ProjectionMetadataResult.mk w im cn cm start) hs
  (@Eq.refl (OptionType ProjectionMetadataResult) (@OptionType.some ProjectionMetadataResult (ProjectionMetadataResult.mk w im cn cm start))))))))))",
    ),
    (
        "projection_resolve_inv_type",
        r"forall (R : RedEnv) (fuel : Nat) (S : Name) (idx : Nat) (E : KExpr) (out : ProjectionMetadataResult) (C : Type),
 @Eq (OptionType ProjectionMetadataResult) (projection_resolve R fuel S idx E) (@OptionType.some ProjectionMetadataResult out) ->
 (ProjectionResolution R fuel S idx E out -> C) -> C",
        r"fun (R : RedEnv) (fuel : Nat) (S : Name) (idx : Nat) (E : KExpr) (out : ProjectionMetadataResult) (C : Type)
 (h : @Eq (OptionType ProjectionMetadataResult) (projection_resolve R fuel S idx E) (@OptionType.some ProjectionMetadataResult out))
 (k : ProjectionResolution R fuel S idx E out -> C) => k (projection_resolve_trace R fuel S idx E out h)",
    ),
    (
        "projection_resolve_inv",
        r"forall (R : RedEnv) (fuel : Nat) (S : Name) (idx : Nat) (E : KExpr) (out : ProjectionMetadataResult) (C : Prop),
 @Eq (OptionType ProjectionMetadataResult) (projection_resolve R fuel S idx E) (@OptionType.some ProjectionMetadataResult out) ->
 (ProjectionResolution R fuel S idx E out -> C) -> C",
        r"fun (R : RedEnv) (fuel : Nat) (S : Name) (idx : Nat) (E : KExpr) (out : ProjectionMetadataResult) (C : Prop)
 (h : @Eq (OptionType ProjectionMetadataResult) (projection_resolve R fuel S idx E) (@OptionType.some ProjectionMetadataResult out))
 (k : ProjectionResolution R fuel S idx E out -> C) => k (projection_resolve_trace R fuel S idx E out h)",
    ),
    (
        "projection_resolution_whnf",
        r"forall (R : RedEnv) (fuel : Nat) (S : Name) (idx : Nat) (E : KExpr) (r : ProjectionMetadataResult),
 ProjectionResolution R fuel S idx E r -> @Eq (OptionType KExpr) (whnf_fuel_red_wh3 R fuel E) (@OptionType.some KExpr (projection_meta_whnf r))",
        r"fun (R : RedEnv) (fuel : Nat) (S : Name) (idx : Nat) (E : KExpr) (r : ProjectionMetadataResult) (trace : ProjectionResolution R fuel S idx E r) =>
@ProjectionResolution.rec R fuel S idx E (fun (out : ProjectionMetadataResult) (_trace : ProjectionResolution R fuel S idx E out) => @Eq (OptionType KExpr) (whnf_fuel_red_wh3 R fuel E) (@OptionType.some KExpr (projection_meta_whnf out)))
 (fun (w : KExpr) (head : Name) (im : KIndMeta) (cn : Name) (cm : KCtorMeta) (start : KExpr)
  (hw : @Eq (OptionType KExpr) (whnf_fuel_red_wh3 R fuel E) (@OptionType.some KExpr w))
  (_hh : @Eq (OptionType Name) (kexpr_const_name (kapp_fn w)) (@OptionType.some Name head))
  (_hn : @Eq Bool (name_eqb head S) Bool.true)
  (_hi : @Eq (OptionType KIndMeta) (kind_for (red_ind_ctor R) S) (@OptionType.some KIndMeta im))
  (_hc : @Eq (ListType Name) (kind_ctor_names im) (@ListType.cons Name cn (@ListType.nil Name)))
  (_hk : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) cn) (@OptionType.some KCtorMeta cm))
  (_hf : @Eq Bool (nat_leb (Nat.succ idx) (kctor_num_fields cm)) Bool.true)
  (_hs : @Eq (OptionType KExpr) (projection_telescope_start R fuel (kconst_params (kind_sig im)) (kctor_sig cm) (kctor_num_params cm) (kind_num_indices im) (kexpr_const_levels (kapp_fn w)) (kapp_args w)) (@OptionType.some KExpr start)) => hw) r trace",
    ),
    (
        "projection_resolution_telescope",
        r"forall (R : RedEnv) (fuel : Nat) (S : Name) (idx : Nat) (E : KExpr) (r : ProjectionMetadataResult),
 ProjectionResolution R fuel S idx E r -> ProjectionTelescopeFacts R fuel r",
        r"fun (R : RedEnv) (fuel : Nat) (S : Name) (idx : Nat) (E : KExpr) (r : ProjectionMetadataResult) (trace : ProjectionResolution R fuel S idx E r) =>
@ProjectionResolution.rec R fuel S idx E (fun (out : ProjectionMetadataResult) (_trace : ProjectionResolution R fuel S idx E out) => ProjectionTelescopeFacts R fuel out)
 (fun (w : KExpr) (_head : Name) (im : KIndMeta) (cn : Name) (cm : KCtorMeta) (start : KExpr)
  (_hw : @Eq (OptionType KExpr) (whnf_fuel_red_wh3 R fuel E) (@OptionType.some KExpr w))
  (_hh : @Eq (OptionType Name) (kexpr_const_name (kapp_fn w)) (@OptionType.some Name _head))
  (_hn : @Eq Bool (name_eqb _head S) Bool.true)
  (_hi : @Eq (OptionType KIndMeta) (kind_for (red_ind_ctor R) S) (@OptionType.some KIndMeta im))
  (_hc : @Eq (ListType Name) (kind_ctor_names im) (@ListType.cons Name cn (@ListType.nil Name)))
  (_hk : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) cn) (@OptionType.some KCtorMeta cm))
  (_hf : @Eq Bool (nat_leb (Nat.succ idx) (kctor_num_fields cm)) Bool.true)
  (hs : @Eq (OptionType KExpr) (projection_telescope_start R fuel (kconst_params (kind_sig im)) (kctor_sig cm) (kctor_num_params cm) (kind_num_indices im) (kexpr_const_levels (kapp_fn w)) (kapp_args w)) (@OptionType.some KExpr start)) =>
 projection_telescope_start_inv R fuel (kconst_params (kind_sig im)) (kctor_sig cm) (kctor_num_params cm) (kind_num_indices im) (kexpr_const_levels (kapp_fn w)) (kapp_args w) start hs
  (ProjectionTelescopeFacts R fuel (ProjectionMetadataResult.mk w im cn cm start))
  (fun (hu : @Eq Nat (name_list_len (kconst_params (kind_sig im))) (level_list_len (kexpr_const_levels (kapp_fn w))))
   (ha : @Eq Nat (Nat.add (kctor_num_params cm) (kind_num_indices im)) (list_length (kapp_args w)))
   (hp : ProjectionParameterGraph R fuel (projection_ctor_type (kconst_params (kind_sig im)) (kctor_sig cm) (kexpr_const_levels (kapp_fn w))) (list_take (kctor_num_params cm) (kapp_args w)) start) =>
   @ProjectionTelescopeFacts.mk R fuel (ProjectionMetadataResult.mk w im cn cm start) hu ha hp)) r trace",
    ),
    (
        "projection_metadata_ctor_lookup",
        r"forall (R : RedEnv) (fuel : Nat) (tenv : KDeclEnv) (S : Name) (r : ProjectionMetadataResult),
 ProjectionMetadataAgreement tenv S r -> ProjectionTelescopeFacts R fuel r ->
 @Eq (OptionType KExpr) (kdecl_type_at tenv (projection_meta_ctor_name r) (projection_meta_levels r)) (@OptionType.some KExpr (projection_meta_ctor_type r))",
        r"fun (R : RedEnv) (fuel : Nat) (tenv : KDeclEnv) (S : Name) (r : ProjectionMetadataResult)
 (agreement : ProjectionMetadataAgreement tenv S r) (facts : ProjectionTelescopeFacts R fuel r) =>
@ProjectionMetadataAgreement.rec tenv S r
 (fun (_agreement : ProjectionMetadataAgreement tenv S r) => @Eq (OptionType KExpr) (kdecl_type_at tenv (projection_meta_ctor_name r) (projection_meta_levels r)) (@OptionType.some KExpr (projection_meta_ctor_type r)))
 (fun (_hind : @Eq (OptionType KConstSig) (tenv S) (@OptionType.some KConstSig (kind_sig (projection_meta_ind r))))
  (hctor : @Eq (OptionType KConstSig) (tenv (projection_meta_ctor_name r)) (@OptionType.some KConstSig (kctor_sig (projection_meta_ctor r))))
  (ordered : @Eq (ListType Name) (kconst_params (kind_sig (projection_meta_ind r))) (kconst_params (kctor_sig (projection_meta_ctor r))))
  (_parent : @Eq Name (kctor_parent (projection_meta_ctor r)) S)
  (_params : @Eq Nat (kctor_num_params (projection_meta_ctor r)) (kind_num_params (projection_meta_ind r)))
  (_index : @Eq Nat (kctor_index (projection_meta_ctor r)) Nat.zero) =>
 @ProjectionTelescopeFacts.rec R fuel r
  (fun (_facts : ProjectionTelescopeFacts R fuel r) => @Eq (OptionType KExpr) (kdecl_type_at tenv (projection_meta_ctor_name r) (projection_meta_levels r)) (@OptionType.some KExpr (projection_meta_ctor_type r)))
  (fun (hu : @Eq Nat (name_list_len (kconst_params (kind_sig (projection_meta_ind r)))) (level_list_len (projection_meta_levels r)))
   (_ha : @Eq Nat (Nat.add (kctor_num_params (projection_meta_ctor r)) (kind_num_indices (projection_meta_ind r))) (list_length (kapp_args (projection_meta_whnf r))))
   (_hp : ProjectionParameterGraph R fuel (projection_ctor_type (kconst_params (kind_sig (projection_meta_ind r))) (kctor_sig (projection_meta_ctor r)) (projection_meta_levels r)) (list_take (kctor_num_params (projection_meta_ctor r)) (kapp_args (projection_meta_whnf r))) (projection_meta_start r)) =>
   kdecl_type_at_intro tenv (projection_meta_ctor_name r) (kctor_sig (projection_meta_ctor r)) (projection_meta_levels r) hctor
    (Eq.trans Nat (name_list_len (kconst_params (kctor_sig (projection_meta_ctor r)))) (name_list_len (kconst_params (kind_sig (projection_meta_ind r)))) (level_list_len (projection_meta_levels r))
     (Eq.symm Nat (name_list_len (kconst_params (kind_sig (projection_meta_ind r)))) (name_list_len (kconst_params (kctor_sig (projection_meta_ctor r))))
      (Eq.cong (ListType Name) Nat name_list_len (kconst_params (kind_sig (projection_meta_ind r))) (kconst_params (kctor_sig (projection_meta_ctor r))) ordered)) hu)) facts) agreement",
    ),
    (
        "projection_metadata_agreement_ordered",
        r"forall (tenv : KDeclEnv) (S : Name) (r : ProjectionMetadataResult), ProjectionMetadataAgreement tenv S r ->
 ProjectionUniverseCoherence (kconst_params (kind_sig (projection_meta_ind r))) (kctor_sig (projection_meta_ctor r))",
        r"fun (tenv : KDeclEnv) (S : Name) (r : ProjectionMetadataResult) (agreement : ProjectionMetadataAgreement tenv S r) =>
@ProjectionMetadataAgreement.rec tenv S r (fun (_agreement : ProjectionMetadataAgreement tenv S r) => ProjectionUniverseCoherence (kconst_params (kind_sig (projection_meta_ind r))) (kctor_sig (projection_meta_ctor r)))
 (fun (_hind : @Eq (OptionType KConstSig) (tenv S) (@OptionType.some KConstSig (kind_sig (projection_meta_ind r))))
  (_hctor : @Eq (OptionType KConstSig) (tenv (projection_meta_ctor_name r)) (@OptionType.some KConstSig (kctor_sig (projection_meta_ctor r))))
  (ordered : @Eq (ListType Name) (kconst_params (kind_sig (projection_meta_ind r))) (kconst_params (kctor_sig (projection_meta_ctor r))))
  (_parent : @Eq Name (kctor_parent (projection_meta_ctor r)) S)
  (_params : @Eq Nat (kctor_num_params (projection_meta_ctor r)) (kind_num_params (projection_meta_ind r)))
  (_index : @Eq Nat (kctor_index (projection_meta_ctor r)) Nat.zero) => ordered) agreement",
    ),
    (
        "projection_metadata_telescope_canonical",
        r"forall (R : RedEnv) (fuel : Nat) (tenv : KDeclEnv) (S : Name) (r : ProjectionMetadataResult),
 ProjectionMetadataAgreement tenv S r -> ProjectionTelescopeFacts R fuel r ->
 ProjectionParameterGraph R fuel (projection_meta_ctor_type r)
  (list_take (kctor_num_params (projection_meta_ctor r)) (kapp_args (projection_meta_whnf r))) (projection_meta_start r)",
        r"fun (R : RedEnv) (fuel : Nat) (tenv : KDeclEnv) (S : Name) (r : ProjectionMetadataResult)
 (agreement : ProjectionMetadataAgreement tenv S r) (facts : ProjectionTelescopeFacts R fuel r) =>
@ProjectionTelescopeFacts.rec R fuel r
 (fun (_facts : ProjectionTelescopeFacts R fuel r) => ProjectionParameterGraph R fuel (projection_meta_ctor_type r) (list_take (kctor_num_params (projection_meta_ctor r)) (kapp_args (projection_meta_whnf r))) (projection_meta_start r))
 (fun (_hu : @Eq Nat (name_list_len (kconst_params (kind_sig (projection_meta_ind r)))) (level_list_len (projection_meta_levels r)))
  (_ha : @Eq Nat (Nat.add (kctor_num_params (projection_meta_ctor r)) (kind_num_indices (projection_meta_ind r))) (list_length (kapp_args (projection_meta_whnf r))))
  (hp : ProjectionParameterGraph R fuel (projection_ctor_type (kconst_params (kind_sig (projection_meta_ind r))) (kctor_sig (projection_meta_ctor r)) (projection_meta_levels r)) (list_take (kctor_num_params (projection_meta_ctor r)) (kapp_args (projection_meta_whnf r))) (projection_meta_start r)) =>
 Eq.subst KExpr (fun (F : KExpr) => ProjectionParameterGraph R fuel F (list_take (kctor_num_params (projection_meta_ctor r)) (kapp_args (projection_meta_whnf r))) (projection_meta_start r))
  (projection_ctor_type (kconst_params (kind_sig (projection_meta_ind r))) (kctor_sig (projection_meta_ctor r)) (projection_meta_levels r)) (projection_meta_ctor_type r)
  (projection_ctor_type_coherent (kconst_params (kind_sig (projection_meta_ind r))) (kctor_sig (projection_meta_ctor r)) (projection_meta_levels r) (projection_metadata_agreement_ordered tenv S r agreement)) hp) facts",
    ),
    (
        "projection_resolved_ctor_spine",
        r"forall (R : RedEnv) (faithful : RedEnvFaithful R) (tenv : KDeclEnv) (G : ListType KExpr)
 (fuel : Nat) (S : Name) (idx : Nat) (E : KExpr) (r : ProjectionMetadataResult),
 ProjectionResolution R fuel S idx E r -> ProjectionMetadataAgreement tenv S r ->
 forall (args : ListType KExpr) (U : KExpr) (T : KExpr),
 @Eq (OptionType KExpr) (raw_pi_spine args (projection_meta_ctor_type r)) (@OptionType.some KExpr U) ->
 TypingCtxConvIn R tenv G (apply_spine args (KExpr.const (projection_meta_ctor_name r) (projection_meta_levels r))) T ->
 SemanticTypedSpineReturn R tenv G (KExpr.const (projection_meta_ctor_name r) (projection_meta_levels r)) (projection_meta_ctor_type r) args U T",
        r"fun (R : RedEnv) (faithful : RedEnvFaithful R) (tenv : KDeclEnv) (G : ListType KExpr)
 (fuel : Nat) (S : Name) (idx : Nat) (E : KExpr) (r : ProjectionMetadataResult)
 (trace : ProjectionResolution R fuel S idx E r) (agreement : ProjectionMetadataAgreement tenv S r)
 (args : ListType KExpr) (U : KExpr) (T : KExpr)
 (run : @Eq (OptionType KExpr) (raw_pi_spine args (projection_meta_ctor_type r)) (@OptionType.some KExpr U))
 (typed : TypingCtxConvIn R tenv G (apply_spine args (KExpr.const (projection_meta_ctor_name r) (projection_meta_levels r))) T) =>
typingctxconv_in_const_spine R faithful tenv G (projection_meta_ctor_name r) (projection_meta_levels r) (projection_meta_ctor_type r) args U T
 (projection_metadata_ctor_lookup R fuel tenv S r agreement (projection_resolution_telescope R fuel S idx E r trace)) run typed",
    ),
    (
        "projection_subject_ready_semantics",
        r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (fuel : Nat) (S : Name)
 (idx : Nat) (e : KExpr) (E : KExpr) (r : ProjectionMetadataResult),
 ProjectionSubjectReady R tenv G fuel S idx e E r -> ProjectionSubjectSemantics R tenv G e E r",
        r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (fuel : Nat) (S : Name)
 (idx : Nat) (e : KExpr) (E : KExpr) (r : ProjectionMetadataResult) (ready : ProjectionSubjectReady R tenv G fuel S idx e E r) =>
@ProjectionSubjectReady.rec R tenv G fuel S idx e E r
 (fun (_ready : ProjectionSubjectReady R tenv G fuel S idx e E r) => ProjectionSubjectSemantics R tenv G e E r)
 (fun (inferred : KernelInfersIn R tenv G e E) (trace : ProjectionResolution R fuel S idx E r)
  (sortType : KExpr) (u : Level) (formed : KernelInfersIn R tenv G (projection_meta_whnf r) sortType)
  (sortRun : @Eq (OptionType KExpr) (whnf_fuel_red_wh3 R fuel sortType) (@OptionType.some KExpr (KExpr.sort u))) =>
  @ProjectionSubjectSemantics.mk R tenv G e E r u
   (whnf_fuel_red_wh3_sound_in R fuel E (projection_meta_whnf r) (projection_resolution_whnf R fuel S idx E r trace))
   (@TypingCtxConvIn.conv R tenv G e E (projection_meta_whnf r) (kernel_infers_in_sound R tenv G e E inferred)
    (whnf_fuel_red_wh3_sound_in R fuel E (projection_meta_whnf r) (projection_resolution_whnf R fuel S idx E r trace)))
   (@TypingCtxConvIn.conv R tenv G (projection_meta_whnf r) sortType (KExpr.sort u)
    (kernel_infers_in_sound R tenv G (projection_meta_whnf r) sortType formed)
    (whnf_fuel_red_wh3_sound_in R fuel sortType (KExpr.sort u) sortRun))) ready",
    ),
    (
        "projection_subject_ctor_spine",
        r"forall (R : RedEnv) (faithful : RedEnvFaithful R) (tenv : KDeclEnv) (G : ListType KExpr)
 (fuel : Nat) (S : Name) (idx : Nat) (e : KExpr) (E : KExpr) (r : ProjectionMetadataResult),
 ProjectionSubjectReady R tenv G fuel S idx e E r -> ProjectionMetadataAgreement tenv S r ->
 forall (args : ListType KExpr) (U : KExpr),
 @Eq KExpr e (apply_spine args (KExpr.const (projection_meta_ctor_name r) (projection_meta_levels r))) ->
 @Eq (OptionType KExpr) (raw_pi_spine args (projection_meta_ctor_type r)) (@OptionType.some KExpr U) ->
 SemanticTypedSpineReturn R tenv G (KExpr.const (projection_meta_ctor_name r) (projection_meta_levels r)) (projection_meta_ctor_type r) args U E",
        r"fun (R : RedEnv) (faithful : RedEnvFaithful R) (tenv : KDeclEnv) (G : ListType KExpr)
 (fuel : Nat) (S : Name) (idx : Nat) (e : KExpr) (E : KExpr) (r : ProjectionMetadataResult)
 (ready : ProjectionSubjectReady R tenv G fuel S idx e E r) (agreement : ProjectionMetadataAgreement tenv S r)
 (args : ListType KExpr) (U : KExpr)
 (shape : @Eq KExpr e (apply_spine args (KExpr.const (projection_meta_ctor_name r) (projection_meta_levels r))))
 (run : @Eq (OptionType KExpr) (raw_pi_spine args (projection_meta_ctor_type r)) (@OptionType.some KExpr U)) =>
@ProjectionSubjectReady.rec R tenv G fuel S idx e E r
 (fun (_ready : ProjectionSubjectReady R tenv G fuel S idx e E r) => SemanticTypedSpineReturn R tenv G (KExpr.const (projection_meta_ctor_name r) (projection_meta_levels r)) (projection_meta_ctor_type r) args U E)
 (fun (inferred : KernelInfersIn R tenv G e E) (trace : ProjectionResolution R fuel S idx E r)
  (sortType : KExpr) (u : Level) (_formed : KernelInfersIn R tenv G (projection_meta_whnf r) sortType)
  (_sortRun : @Eq (OptionType KExpr) (whnf_fuel_red_wh3 R fuel sortType) (@OptionType.some KExpr (KExpr.sort u))) =>
  projection_resolved_ctor_spine R faithful tenv G fuel S idx E r trace agreement args U E run
   (Eq.substType KExpr (fun (subject : KExpr) => TypingCtxConvIn R tenv G subject E)
    e (apply_spine args (KExpr.const (projection_meta_ctor_name r) (projection_meta_levels r))) shape
    (kernel_infers_in_sound R tenv G e E inferred))) ready",
    ),
    (
        "projection_subject_ctor_spine_normalized",
        r"forall (R : RedEnv) (faithful : RedEnvFaithful R) (tenv : KDeclEnv) (G : ListType KExpr)
 (fuel : Nat) (S : Name) (idx : Nat) (e : KExpr) (E : KExpr) (r : ProjectionMetadataResult),
 ProjectionSubjectReady R tenv G fuel S idx e E r -> ProjectionMetadataAgreement tenv S r ->
 forall (args : ListType KExpr) (U : KExpr),
 @Eq KExpr e (apply_spine args (KExpr.const (projection_meta_ctor_name r) (projection_meta_levels r))) ->
 @Eq (OptionType KExpr) (raw_pi_spine args (projection_meta_ctor_type r)) (@OptionType.some KExpr U) ->
 SemanticTypedSpineReturn R tenv G (KExpr.const (projection_meta_ctor_name r) (projection_meta_levels r)) (projection_meta_ctor_type r) args U (projection_meta_whnf r)",
        r"fun (R : RedEnv) (faithful : RedEnvFaithful R) (tenv : KDeclEnv) (G : ListType KExpr)
 (fuel : Nat) (S : Name) (idx : Nat) (e : KExpr) (E : KExpr) (r : ProjectionMetadataResult)
 (ready : ProjectionSubjectReady R tenv G fuel S idx e E r) (agreement : ProjectionMetadataAgreement tenv S r)
 (args : ListType KExpr) (U : KExpr)
 (shape : @Eq KExpr e (apply_spine args (KExpr.const (projection_meta_ctor_name r) (projection_meta_levels r))))
 (run : @Eq (OptionType KExpr) (raw_pi_spine args (projection_meta_ctor_type r)) (@OptionType.some KExpr U)) =>
@ProjectionSubjectSemantics.rec R tenv G e E r
 (fun (_sem : ProjectionSubjectSemantics R tenv G e E r) => SemanticTypedSpineReturn R tenv G (KExpr.const (projection_meta_ctor_name r) (projection_meta_levels r)) (projection_meta_ctor_type r) args U (projection_meta_whnf r))
 (fun (_u : Level) (normalized : DefEqIn R E (projection_meta_whnf r))
  (_subject : TypingCtxConvIn R tenv G e (projection_meta_whnf r))
  (_formation : TypingCtxConvIn R tenv G (projection_meta_whnf r) (KExpr.sort _u)) =>
 @SemanticTypedSpineReturn.rec R tenv G (KExpr.const (projection_meta_ctor_name r) (projection_meta_levels r)) (projection_meta_ctor_type r) args U E
  (fun (_spine : SemanticTypedSpineReturn R tenv G (KExpr.const (projection_meta_ctor_name r) (projection_meta_levels r)) (projection_meta_ctor_type r) args U E) => SemanticTypedSpineReturn R tenv G (KExpr.const (projection_meta_ctor_name r) (projection_meta_levels r)) (projection_meta_ctor_type r) args U (projection_meta_whnf r))
  (fun (head : TypingCtxConvIn R tenv G (KExpr.const (projection_meta_ctor_name r) (projection_meta_levels r)) (projection_meta_ctor_type r))
   (arguments : TypedRawPiSpine R tenv G (projection_meta_ctor_type r) args U) (residual : DefEqIn R U E) =>
   @SemanticTypedSpineReturn.intro R tenv G (KExpr.const (projection_meta_ctor_name r) (projection_meta_levels r)) (projection_meta_ctor_type r) args U (projection_meta_whnf r)
    head arguments (@DefEqIn.trans R U E (projection_meta_whnf r) residual normalized))
  (projection_subject_ctor_spine R faithful tenv G fuel S idx e E r ready agreement args U shape run))
 (projection_subject_ready_semantics R tenv G fuel S idx e E r ready)",
    ),
];

const CONTROLS: &[(&str, &str, &str)] = &[
    (
        "projection_metadata_nonempty_resolves",
        r"@Eq (OptionType ProjectionMetadataResult)
 (projection_resolve projection_metadata_control_env (Nat.succ Nat.zero) Name.anonymous Nat.zero projection_metadata_control_type)
 (@OptionType.some ProjectionMetadataResult projection_metadata_control_result)",
        r"@Eq.refl (OptionType ProjectionMetadataResult) (@OptionType.some ProjectionMetadataResult projection_metadata_control_result)",
    ),
    (
        "projection_metadata_nonempty_trace",
        r"ProjectionResolution projection_metadata_control_env (Nat.succ Nat.zero) Name.anonymous Nat.zero projection_metadata_control_type projection_metadata_control_result",
        r"projection_resolve_trace projection_metadata_control_env (Nat.succ Nat.zero) Name.anonymous Nat.zero projection_metadata_control_type projection_metadata_control_result projection_metadata_nonempty_resolves",
    ),
    (
        "projection_metadata_nonempty_agreement",
        r"ProjectionMetadataAgreement projection_metadata_control_tenv Name.anonymous projection_metadata_control_result",
        r"@ProjectionMetadataAgreement.mk projection_metadata_control_tenv Name.anonymous projection_metadata_control_result
 (@Eq.refl (OptionType KConstSig) (@OptionType.some KConstSig (kind_sig projection_metadata_control_ind)))
 (@Eq.refl (OptionType KConstSig) (@OptionType.some KConstSig projection_metadata_control_sig))
 (@Eq.refl (ListType Name) (@ListType.nil Name)) (@Eq.refl Name Name.anonymous)
 (@Eq.refl Nat Nat.zero) (@Eq.refl Nat Nat.zero)",
    ),
    (
        "projection_metadata_missing_ind_refuses",
        r"@Eq (OptionType ProjectionMetadataResult)
 (projection_resolve (RedEnv.mk RecEnv.empty DefEnv.empty IndCtorEnv.empty) (Nat.succ Nat.zero) Name.anonymous Nat.zero projection_metadata_control_type)
 (@OptionType.none ProjectionMetadataResult)",
        r"@Eq.refl (OptionType ProjectionMetadataResult) (@OptionType.none ProjectionMetadataResult)",
    ),
    (
        "projection_metadata_missing_ctor_refuses",
        r"@Eq (OptionType ProjectionMetadataResult)
 (projection_resolve (RedEnv.mk RecEnv.empty DefEnv.empty (IndCtorEnv.addInd IndCtorEnv.empty Name.anonymous projection_metadata_control_ind))
 (Nat.succ Nat.zero) Name.anonymous Nat.zero projection_metadata_control_type) (@OptionType.none ProjectionMetadataResult)",
        r"@Eq.refl (OptionType ProjectionMetadataResult) (@OptionType.none ProjectionMetadataResult)",
    ),
    (
        "projection_metadata_two_ctors_refuse",
        r"@Eq (OptionType ProjectionMetadataResult)
 (projection_resolve_ind projection_metadata_control_env (Nat.succ Nat.zero) Nat.zero projection_metadata_control_type
 (KIndMeta.mk (kind_sig projection_metadata_control_ind) Nat.zero Nat.zero
  (@ListType.cons Name projection_metadata_control_cn (@ListType.cons Name projection_metadata_control_cn (@ListType.nil Name)))
  (kind_all_names projection_metadata_control_ind)))
 (@OptionType.none ProjectionMetadataResult)",
        r"@Eq.refl (OptionType ProjectionMetadataResult) (@OptionType.none ProjectionMetadataResult)",
    ),
    (
        "projection_metadata_zero_ctors_refuse",
        r"@Eq (OptionType ProjectionMetadataResult)
 (projection_resolve_ind projection_metadata_control_env (Nat.succ Nat.zero) Nat.zero projection_metadata_control_type
 (KIndMeta.mk (kind_sig projection_metadata_control_ind) Nat.zero Nat.zero (@ListType.nil Name)
  (kind_all_names projection_metadata_control_ind))) (@OptionType.none ProjectionMetadataResult)",
        r"@Eq.refl (OptionType ProjectionMetadataResult) (@OptionType.none ProjectionMetadataResult)",
    ),
    (
        "projection_metadata_field_bound_refuses",
        r"@Eq (OptionType ProjectionMetadataResult)
 (projection_resolve projection_metadata_control_env (Nat.succ Nat.zero) Name.anonymous (Nat.succ Nat.zero) projection_metadata_control_type)
 (@OptionType.none ProjectionMetadataResult)",
        r"@Eq.refl (OptionType ProjectionMetadataResult) (@OptionType.none ProjectionMetadataResult)",
    ),
    (
        "projection_metadata_universe_arity_refuses",
        r"@Eq (OptionType ProjectionMetadataResult)
 (projection_resolve projection_metadata_control_env (Nat.succ Nat.zero) Name.anonymous Nat.zero
  (KExpr.const Name.anonymous (@ListType.cons Level Level.zero (@ListType.nil Level)))) (@OptionType.none ProjectionMetadataResult)",
        r"@Eq.refl (OptionType ProjectionMetadataResult) (@OptionType.none ProjectionMetadataResult)",
    ),
    (
        "projection_metadata_type_arity_refuses",
        r"@Eq (OptionType ProjectionMetadataResult)
 (projection_resolve projection_metadata_control_env (Nat.succ Nat.zero) Name.anonymous Nat.zero
  (KExpr.app projection_metadata_control_type (KExpr.sort Level.zero))) (@OptionType.none ProjectionMetadataResult)",
        r"@Eq.refl (OptionType ProjectionMetadataResult) (@OptionType.none ProjectionMetadataResult)",
    ),
    (
        "projection_metadata_wrong_name_refuses",
        r"@Eq (OptionType ProjectionMetadataResult)
 (projection_resolve projection_metadata_control_env (Nat.succ Nat.zero) projection_metadata_control_cn Nat.zero projection_metadata_control_type)
 (@OptionType.none ProjectionMetadataResult)",
        r"@Eq.refl (OptionType ProjectionMetadataResult) (@OptionType.none ProjectionMetadataResult)",
    ),
    (
        "projection_metadata_wrong_parent_is_not_runtime_guard",
        r"@Eq (OptionType ProjectionMetadataResult)
 (projection_resolve projection_metadata_wrong_parent_env (Nat.succ Nat.zero) Name.anonymous Nat.zero projection_metadata_control_type)
 (@OptionType.some ProjectionMetadataResult projection_metadata_wrong_parent_result)",
        r"@Eq.refl (OptionType ProjectionMetadataResult) (@OptionType.some ProjectionMetadataResult projection_metadata_wrong_parent_result)",
    ),
];

const GENERATED_PROOFS: &[(&str, &str, &str)] = &[
    (
        "projection_prod_signature_shape",
        r"@Eq KExpr (kconst_inst_type kcre_prod_mk_signature (@ListType.nil Level)) (KExpr.pi projection_prod_sort projection_prod_ctor_tail)",
        r"@Eq.refl KExpr (KExpr.pi projection_prod_sort projection_prod_ctor_tail)",
    ),
    (
        "projection_prod_input_shape",
        r"@Eq KExpr kcre_witness_prod_value (apply_spine projection_prod_args projection_prod_ctor)",
        r"@Eq.refl KExpr kcre_witness_prod_value",
    ),
    (
        "projection_prod_nat_inferred",
        r"KernelInfersIn the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) rfnz_nat projection_prod_sort",
        r"projection_const_infers the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) literal_builtin_nat_name (@ListType.nil Level) projection_prod_sort
 (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr projection_prod_sort))",
    ),
    (
        "projection_prod_zero_inferred",
        r"KernelInfersIn the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) rfnz_zero rfnz_nat",
        r"projection_const_infers the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) fixture_nat_zero_name (@ListType.nil Level) rfnz_nat
 (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr rfnz_nat))",
    ),
    (
        "projection_prod_one_inferred",
        r"KernelInfersIn the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) (KExpr.app rfnz_succ rfnz_zero) rfnz_nat",
        r"projection_app_infers_raw the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) rfnz_succ rfnz_zero rfnz_nat rfnz_nat
 (projection_const_infers the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) fixture_nat_succ_name (@ListType.nil Level) (KExpr.pi rfnz_nat rfnz_nat)
  (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.pi rfnz_nat rfnz_nat)))) projection_prod_zero_inferred",
    ),
    (
        "projection_prod_head_inferred",
        r"KernelInfersIn the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) projection_prod_ctor (KExpr.pi projection_prod_sort projection_prod_ctor_tail)",
        r"projection_const_infers the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) kcre_prod_mk_name (@ListType.nil Level) (KExpr.pi projection_prod_sort projection_prod_ctor_tail)
 (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.pi projection_prod_sort projection_prod_ctor_tail)))",
    ),
    (
        "projection_prod_apply_A_inferred",
        r"KernelInfersIn the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) (KExpr.app projection_prod_ctor rfnz_nat) projection_prod_after_A",
        r"projection_app_infers_raw the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) projection_prod_ctor rfnz_nat projection_prod_sort projection_prod_ctor_tail
 projection_prod_head_inferred projection_prod_nat_inferred",
    ),
    (
        "projection_prod_apply_B_inferred",
        r"KernelInfersIn the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) (KExpr.app (KExpr.app projection_prod_ctor rfnz_nat) rfnz_nat) projection_prod_field_telescope",
        r"projection_app_infers_raw the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) (KExpr.app projection_prod_ctor rfnz_nat) rfnz_nat projection_prod_sort
 (KExpr.pi rfnz_nat (KExpr.pi (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.app (KExpr.app projection_prod_family rfnz_nat) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))))
 projection_prod_apply_A_inferred projection_prod_nat_inferred",
    ),
    (
        "projection_prod_apply_zero_inferred",
        r"KernelInfersIn the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) (KExpr.app (KExpr.app (KExpr.app projection_prod_ctor rfnz_nat) rfnz_nat) rfnz_zero) (KExpr.pi rfnz_nat kcre_witness_prod_type)",
        r"projection_app_infers_raw the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) (KExpr.app (KExpr.app projection_prod_ctor rfnz_nat) rfnz_nat) rfnz_zero rfnz_nat
 (KExpr.pi rfnz_nat kcre_witness_prod_type) projection_prod_apply_B_inferred projection_prod_zero_inferred",
    ),
    (
        "projection_prod_subject_inferred",
        r"KernelInfersIn the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) kcre_witness_prod_value kcre_witness_prod_type",
        r"projection_app_infers_raw the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) (KExpr.app (KExpr.app (KExpr.app projection_prod_ctor rfnz_nat) rfnz_nat) rfnz_zero)
 (KExpr.app rfnz_succ rfnz_zero) rfnz_nat kcre_witness_prod_type projection_prod_apply_zero_inferred projection_prod_one_inferred",
    ),
    (
        "projection_prod_type_inferred",
        r"KernelInfersIn the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) kcre_witness_prod_type projection_prod_sort",
        r"projection_app_infers_raw the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) (KExpr.app projection_prod_family rfnz_nat) rfnz_nat projection_prod_sort projection_prod_sort
 (projection_app_infers_raw the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) projection_prod_family rfnz_nat projection_prod_sort (KExpr.pi projection_prod_sort projection_prod_sort)
  (projection_const_infers the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) kcre_prod_type_name (@ListType.nil Level) (KExpr.pi projection_prod_sort (KExpr.pi projection_prod_sort projection_prod_sort))
   (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.pi projection_prod_sort (KExpr.pi projection_prod_sort projection_prod_sort))))) projection_prod_nat_inferred)
 projection_prod_nat_inferred",
    ),
    (
        "projection_prod_resolves",
        r"@Eq (OptionType ProjectionMetadataResult) (projection_resolve the_red_env (Nat.succ Nat.zero) kcre_prod_type_name Nat.zero kcre_witness_prod_type)
 (@OptionType.some ProjectionMetadataResult projection_prod_result)",
        r"@Eq.refl (OptionType ProjectionMetadataResult) (@OptionType.some ProjectionMetadataResult projection_prod_result)",
    ),
    (
        "projection_prod_agreement",
        r"ProjectionMetadataAgreement kcre_ind_ctor_tenv kcre_prod_type_name projection_prod_result",
        r"@ProjectionMetadataAgreement.mk kcre_ind_ctor_tenv kcre_prod_type_name projection_prod_result
 (@Eq.refl (OptionType KConstSig) (@OptionType.some KConstSig kcre_prod_type_signature))
 (@Eq.refl (OptionType KConstSig) (@OptionType.some KConstSig kcre_prod_mk_signature))
 (@Eq.refl (ListType Name) (@ListType.nil Name)) (@Eq.refl Name kcre_prod_type_name)
 (@Eq.refl Nat (Nat.succ (Nat.succ Nat.zero))) (@Eq.refl Nat Nat.zero)",
    ),
    (
        "projection_prod_subject_ready",
        r"ProjectionSubjectReady the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) (Nat.succ Nat.zero) kcre_prod_type_name Nat.zero
 kcre_witness_prod_value kcre_witness_prod_type projection_prod_result",
        r"@ProjectionSubjectReady.mk the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) (Nat.succ Nat.zero) kcre_prod_type_name Nat.zero
 kcre_witness_prod_value kcre_witness_prod_type projection_prod_result projection_prod_subject_inferred
 (projection_resolve_trace the_red_env (Nat.succ Nat.zero) kcre_prod_type_name Nat.zero kcre_witness_prod_type projection_prod_result projection_prod_resolves)
 projection_prod_sort (Level.succ Level.zero) projection_prod_type_inferred
 (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr projection_prod_sort))",
    ),
    (
        "projection_prod_subject_semantics",
        r"ProjectionSubjectSemantics the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) kcre_witness_prod_value kcre_witness_prod_type projection_prod_result",
        r"projection_subject_ready_semantics the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) (Nat.succ Nat.zero) kcre_prod_type_name Nat.zero
 kcre_witness_prod_value kcre_witness_prod_type projection_prod_result projection_prod_subject_ready",
    ),
    (
        "projection_prod_typed_constructor_spine",
        r"SemanticTypedSpineReturn the_red_env kcre_ind_ctor_tenv (@ListType.nil KExpr) projection_prod_ctor
 (projection_meta_ctor_type projection_prod_result) projection_prod_args kcre_witness_prod_type kcre_witness_prod_type",
        r"projection_subject_ctor_spine_normalized the_red_env the_red_env_faithful kcre_ind_ctor_tenv (@ListType.nil KExpr)
 (Nat.succ Nat.zero) kcre_prod_type_name Nat.zero kcre_witness_prod_value kcre_witness_prod_type projection_prod_result
 projection_prod_subject_ready projection_prod_agreement projection_prod_args kcre_witness_prod_type projection_prod_input_shape
 (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr kcre_witness_prod_type))",
    ),
    (
        "projection_prod_canonical_parameter_telescope",
        r"ProjectionParameterGraph the_red_env (Nat.succ Nat.zero) (projection_meta_ctor_type projection_prod_result)
 (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr rfnz_nat (@ListType.nil KExpr))) projection_prod_field_telescope",
        r"projection_metadata_telescope_canonical the_red_env (Nat.succ Nat.zero) kcre_ind_ctor_tenv kcre_prod_type_name projection_prod_result
 projection_prod_agreement
 (projection_resolution_telescope the_red_env (Nat.succ Nat.zero) kcre_prod_type_name Nat.zero kcre_witness_prod_type projection_prod_result
  (projection_resolve_trace the_red_env (Nat.succ Nat.zero) kcre_prod_type_name Nat.zero kcre_witness_prod_type projection_prod_result projection_prod_resolves))",
    ),
];

pub(super) const PROOF_ROOTS: &[&str] = &[
    "projection_substL_identity",
    "projection_mapLL_identity",
    "projection_instL_identity",
    "projection_ctor_type_instantiation",
    "projection_ctor_type_coherent",
    "projection_const_infers",
    "projection_app_infers_raw",
    "projection_single_ctor_inv",
    "projection_single_ctor_intro",
    "projection_meta_guard_inv",
    "projection_meta_guard_intro",
    "projection_meta_bind_intro",
    "projection_resolve_ctor_inv",
    "projection_resolve_trace",
    "projection_resolve_intro",
    "projection_resolve_inv_type",
    "projection_resolve_inv",
    "projection_resolution_whnf",
    "projection_resolution_telescope",
    "projection_metadata_ctor_lookup",
    "projection_metadata_agreement_ordered",
    "projection_metadata_telescope_canonical",
    "projection_resolved_ctor_spine",
    "projection_subject_ready_semantics",
    "projection_subject_ctor_spine",
    "projection_subject_ctor_spine_normalized",
    "projection_metadata_nonempty_resolves",
    "projection_metadata_nonempty_trace",
    "projection_metadata_nonempty_agreement",
    "projection_metadata_missing_ind_refuses",
    "projection_metadata_missing_ctor_refuses",
    "projection_metadata_two_ctors_refuse",
    "projection_metadata_zero_ctors_refuse",
    "projection_metadata_field_bound_refuses",
    "projection_metadata_universe_arity_refuses",
    "projection_metadata_type_arity_refuses",
    "projection_metadata_wrong_name_refuses",
    "projection_metadata_wrong_parent_is_not_runtime_guard",
    "projection_prod_signature_shape",
    "projection_prod_input_shape",
    "projection_prod_nat_inferred",
    "projection_prod_zero_inferred",
    "projection_prod_one_inferred",
    "projection_prod_head_inferred",
    "projection_prod_apply_A_inferred",
    "projection_prod_apply_B_inferred",
    "projection_prod_apply_zero_inferred",
    "projection_prod_subject_inferred",
    "projection_prod_type_inferred",
    "projection_prod_resolves",
    "projection_prod_agreement",
    "projection_prod_subject_ready",
    "projection_prod_subject_semantics",
    "projection_prod_typed_constructor_spine",
    "projection_prod_canonical_parameter_telescope",
];

impl Specification {
    /// After projection_telescope and semantic_typed_spine; full bundle only.
    pub(super) fn add_projection_metadata(&mut self) -> Result<(), SpecError> {
        debug_assert_eq!(
            PROOF_ROOTS.len(),
            PROOFS.len() + CONTROLS.len() + GENERATED_PROOFS.len()
        );
        for source in DATA.iter().chain(CONTROL_DATA).chain(GENERATED_DATA) {
            if source.starts_with("inductive ") {
                self.add_inductive(
                    source,
                    "Actual projection metadata/computation evidence; no output typing is carried.",
                )?;
            } else {
                self.add_recursive_def(source, "Computed metadata lookup and guarded telescope over the existing reduction environment.")?;
            }
        }
        for &(name, type_src, value_src) in PROOFS.iter().chain(CONTROLS).chain(GENERATED_PROOFS) {
            super::acceptance_in::theorem(self, name, type_src, value_src,
                "Checked connected metadata resolution/constructor-typing bridge, not projection preservation or Rust refinement.")?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "projection_metadata/tests.rs"]
mod tests;
