// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Universe substitution for the actual guarded iota evaluator.
//!
//! Selected raw RHS templates are supported under the selected metadata's own
//! ordered signature parameters. Actual head-level substitution, preserved
//! guards and support-sensitive fusion derive the once-instantiated output.
//! Parameter-free support is retained as an honest stronger compatibility case.
//! No output-step, per-instance typing, admission or Trust premise is added.
//!
//! Whole registered construction and independent replay remain integration gates.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const PROOFS: &[(&str, &str)] = &[
    (
        r"def substL_nil_support_id (s : Name -> Level) (u : Level)
 (h : LevelParamSupport (ListType.nil Name) u) : Eq Level (substL s u) u :=
 LevelParamSupport.rec (ListType.nil Name)
  (fun (v : Level) (_h : LevelParamSupport (ListType.nil Name) v) => Eq Level (substL s v) v)
  (Eq.refl Level Level.zero)
  (fun (v : Level) (_hv : LevelParamSupport (ListType.nil Name) v) (ih : Eq Level (substL s v) v) =>
    Eq.cong Level Level Level.succ (substL s v) v ih)
  (fun (a : Level) (b : Level) (_ha : LevelParamSupport (ListType.nil Name) a)
    (_hb : LevelParamSupport (ListType.nil Name) b) (iha : Eq Level (substL s a) a) (ihb : Eq Level (substL s b) b) =>
    universe_bridge_congr2 Level Level Level Level.max (substL s a) a (substL s b) b iha ihb)
  (fun (a : Level) (b : Level) (_ha : LevelParamSupport (ListType.nil Name) a)
    (_hb : LevelParamSupport (ListType.nil Name) b) (iha : Eq Level (substL s a) a) (ihb : Eq Level (substL s b) b) =>
    universe_bridge_congr2 Level Level Level Level.imax (substL s a) a (substL s b) b iha ihb)
  (fun (n : Name) (i : Nat) (found : Eq (OptionType Nat) (nameIdx (ListType.nil Name) n) (OptionType.some Nat i)) =>
    option_none_ne_some Nat i (Eq Level (substL s (Level.param n)) (Level.param n)) found) u h",
        "Actual empty-list universe support forces level substitution to be syntactic identity; the parameter case is impossible by computed nameIdx nil, not assumed away.",
    ),
    (
        r"def mapLL_nil_support_id (s : Name -> Level) (us : ListType Level)
 (h : LevelListParamSupport (ListType.nil Name) us) : Eq (ListType Level) (mapLL (substL s) us) us :=
 LevelListParamSupport.rec (ListType.nil Name)
  (fun (xs : ListType Level) (_h : LevelListParamSupport (ListType.nil Name) xs) =>
    Eq (ListType Level) (mapLL (substL s) xs) xs)
  (Eq.refl (ListType Level) (ListType.nil Level))
  (fun (u : Level) (xs : ListType Level) (hu : LevelParamSupport (ListType.nil Name) u)
    (_hxs : LevelListParamSupport (ListType.nil Name) xs)
    (ih : Eq (ListType Level) (mapLL (substL s) xs) xs) =>
    universe_bridge_congr2 Level (ListType Level) (ListType Level)
      (fun (u0 : Level) (xs0 : ListType Level) => ListType.cons Level u0 xs0)
      (substL s u) u (mapLL (substL s) xs) xs (substL_nil_support_id s u hu) ih) us h",
        "The actual constant-level map is identity under empty parameter support, element by element.",
    ),
    (
        r"def instL_nil_support_id (s : Name -> Level) (e : KExpr)
 (h : KExprParamSupport (ListType.nil Name) e) : Eq KExpr (instL s e) e :=
 KExprParamSupport.rec (ListType.nil Name)
  (fun (x : KExpr) (_h : KExprParamSupport (ListType.nil Name) x) => Eq KExpr (instL s x) x)
  (fun (u : Level) (hu : LevelParamSupport (ListType.nil Name) u) =>
    Eq.cong Level KExpr KExpr.sort (substL s u) u (substL_nil_support_id s u hu))
  (fun (i : Nat) => Eq.refl KExpr (KExpr.bvar i))
  (fun (f : KExpr) (a : KExpr) (_hf : KExprParamSupport (ListType.nil Name) f)
    (_ha : KExprParamSupport (ListType.nil Name) a) (ihf : Eq KExpr (instL s f) f) (iha : Eq KExpr (instL s a) a) =>
    universe_bridge_congr2 KExpr KExpr KExpr KExpr.app (instL s f) f (instL s a) a ihf iha)
  (fun (A : KExpr) (b : KExpr) (_hA : KExprParamSupport (ListType.nil Name) A)
    (_hb : KExprParamSupport (ListType.nil Name) b) (ihA : Eq KExpr (instL s A) A) (ihb : Eq KExpr (instL s b) b) =>
    universe_bridge_congr2 KExpr KExpr KExpr KExpr.lam (instL s A) A (instL s b) b ihA ihb)
  (fun (A : KExpr) (B : KExpr) (_hA : KExprParamSupport (ListType.nil Name) A)
    (_hB : KExprParamSupport (ListType.nil Name) B) (ihA : Eq KExpr (instL s A) A) (ihB : Eq KExpr (instL s B) B) =>
    universe_bridge_congr2 KExpr KExpr KExpr KExpr.pi (instL s A) A (instL s B) B ihA ihB)
  (fun (n : Name) (us : ListType Level) (hus : LevelListParamSupport (ListType.nil Name) us) =>
    Eq.cong (ListType Level) KExpr (fun (xs : ListType Level) => KExpr.const n xs)
      (mapLL (substL s) us) us (mapLL_nil_support_id s us hus))
  (fun (A : KExpr) (v : KExpr) (b : KExpr) (_hA : KExprParamSupport (ListType.nil Name) A)
    (_hv : KExprParamSupport (ListType.nil Name) v) (_hb : KExprParamSupport (ListType.nil Name) b)
    (ihA : Eq KExpr (instL s A) A) (ihv : Eq KExpr (instL s v) v) (ihb : Eq KExpr (instL s b) b) =>
    Eq.trans KExpr (KExpr.let_ (instL s A) (instL s v) (instL s b))
      (KExpr.let_ A v (instL s b)) (KExpr.let_ A v b)
      (universe_bridge_congr2 KExpr KExpr KExpr
        (fun (A0 : KExpr) (v0 : KExpr) => KExpr.let_ A0 v0 (instL s b))
        (instL s A) A (instL s v) v ihA ihv)
      (Eq.cong KExpr KExpr (fun (b0 : KExpr) => KExpr.let_ A v b0) (instL s b) b ihb))
  (fun (n : Name) (i : Nat) (sub : KExpr) (_hsub : KExprParamSupport (ListType.nil Name) sub)
    (ih : Eq KExpr (instL s sub) sub) =>
    Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.proj n i x) (instL s sub) sub ih)
  (fun (n : Nat) => Eq.refl KExpr (KExpr.lit n)) e h",
        "Derive stored RHS invariance from genuine parameter-free syntax over every KExpr constructor. Loose de Bruijn variables remain allowed; this is neither term-variable closedness nor a typing theorem.",
    ),
    (
        r"def mapLT_list_drop (f : KExpr -> KExpr) (n : Nat) :
 forall (xs : ListType KExpr), Eq (ListType KExpr) (list_drop n (mapLT f xs)) (mapLT f (list_drop n xs)) :=
 Nat.rec
  (fun (m : Nat) => forall (xs : ListType KExpr),
    Eq (ListType KExpr) (list_drop m (mapLT f xs)) (mapLT f (list_drop m xs)))
  (fun (xs : ListType KExpr) => Eq.refl (ListType KExpr) (mapLT f xs))
  (fun (m : Nat) (ih : forall (xs : ListType KExpr),
    Eq (ListType KExpr) (list_drop m (mapLT f xs)) (mapLT f (list_drop m xs)))
    (xs : ListType KExpr) =>
    Eq.trans (ListType KExpr) (list_drop m (list_tail (mapLT f xs)))
      (list_drop m (mapLT f (list_tail xs))) (mapLT f (list_drop m (list_tail xs)))
      (Eq.cong (ListType KExpr) (ListType KExpr) (list_drop m)
        (list_tail (mapLT f xs)) (mapLT f (list_tail xs)) (list_tail_mapLT f xs))
      (ih (list_tail xs))) n",
        "Actual list_drop commutes with mapLT at every count, including overlong drops, by Nat induction and the existing actual tail-map theorem.",
    ),
    (
        r"def mapLT_list_take (f : KExpr -> KExpr) (n : Nat) :
 forall (xs : ListType KExpr), Eq (ListType KExpr) (list_take n (mapLT f xs)) (mapLT f (list_take n xs)) :=
 Nat.rec
  (fun (m : Nat) => forall (xs : ListType KExpr),
    Eq (ListType KExpr) (list_take m (mapLT f xs)) (mapLT f (list_take m xs)))
  (fun (xs : ListType KExpr) => Eq.refl (ListType KExpr) (ListType.nil KExpr))
  (fun (m : Nat) (ih : forall (xs : ListType KExpr),
    Eq (ListType KExpr) (list_take m (mapLT f xs)) (mapLT f (list_take m xs)))
    (input : ListType KExpr) =>
    ListType.rec KExpr
      (fun (xs : ListType KExpr) =>
        Eq (ListType KExpr) (list_take (Nat.succ m) (mapLT f xs)) (mapLT f (list_take (Nat.succ m) xs)))
      (Eq.refl (ListType KExpr) (ListType.nil KExpr))
      (fun (x : KExpr) (xs : ListType KExpr)
        (_ihxs : Eq (ListType KExpr) (list_take (Nat.succ m) (mapLT f xs)) (mapLT f (list_take (Nat.succ m) xs))) =>
        Eq.cong (ListType KExpr) (ListType KExpr)
          (fun (tail : ListType KExpr) => ListType.cons KExpr (f x) tail)
          (list_take m (mapLT f xs)) (mapLT f (list_take m xs)) (ih xs)) input) n",
        "Actual list_take commutes with mapLT by the operator's Nat/List recursors, including truncation at nil.",
    ),
    (
        r"def iota_instL_drop_args (s : Name -> Level) (n : Nat) (e : KExpr) :
 Eq (ListType KExpr) (list_drop n (kapp_args (instL s e)))
   (mapLT (instL s) (list_drop n (kapp_args e))) :=
 Eq.trans (ListType KExpr) (list_drop n (kapp_args (instL s e)))
  (list_drop n (mapLT (instL s) (kapp_args e))) (mapLT (instL s) (list_drop n (kapp_args e)))
  (Eq.cong (ListType KExpr) (ListType KExpr) (list_drop n)
    (kapp_args (instL s e)) (mapLT (instL s) (kapp_args e)) (kapp_args_instL s e))
  (mapLT_list_drop (instL s) n (kapp_args e))",
        "Substituted application-spine suffixes are the actual mapLT of original suffixes, at arbitrary counts.",
    ),
    (
        r"def iota_instL_take_args (s : Name -> Level) (n : Nat) (e : KExpr) :
 Eq (ListType KExpr) (list_take n (kapp_args (instL s e)))
   (mapLT (instL s) (list_take n (kapp_args e))) :=
 Eq.trans (ListType KExpr) (list_take n (kapp_args (instL s e)))
  (list_take n (mapLT (instL s) (kapp_args e))) (mapLT (instL s) (list_take n (kapp_args e)))
  (Eq.cong (ListType KExpr) (ListType KExpr) (list_take n)
    (kapp_args (instL s e)) (mapLT (instL s) (kapp_args e)) (kapp_args_instL s e))
  (mapLT_list_take (instL s) n (kapp_args e))",
        "Substituted application-spine prefixes map exactly, retaining actual order and cutoff computation.",
    ),
    (
        r"def iota_instL_args_length (s : Name -> Level) (e : KExpr) :
 Eq Nat (list_length (kapp_args (instL s e))) (list_length (kapp_args e)) :=
 Eq.trans Nat (list_length (kapp_args (instL s e)))
  (list_length (mapLT (instL s) (kapp_args e))) (list_length (kapp_args e))
  (Eq.cong (ListType KExpr) Nat list_length
    (kapp_args (instL s e)) (mapLT (instL s) (kapp_args e)) (kapp_args_instL s e))
  (mapLT_length (instL s) (kapp_args e))",
        "Actual argument length is invariant under universe substitution, derived from the existing map length theorem.",
    ),
    (
        r"def iota_instL_major_at (s : Name -> Level) (n : Nat) (e : KExpr) (major : KExpr)
 (found : Eq (OptionType KExpr) (list_head (list_drop n (kapp_args e))) (OptionType.some KExpr major)) :
 Eq (OptionType KExpr) (list_head (list_drop n (kapp_args (instL s e)))) (OptionType.some KExpr (instL s major)) :=
 Eq.trans (OptionType KExpr) (list_head (list_drop n (kapp_args (instL s e))))
  (list_head (mapLT (instL s) (list_drop n (kapp_args e)))) (OptionType.some KExpr (instL s major))
  (Eq.cong (ListType KExpr) (OptionType KExpr) list_head
    (list_drop n (kapp_args (instL s e))) (mapLT (instL s) (list_drop n (kapp_args e)))
    (iota_instL_drop_args s n e))
  (list_head_mapLT (instL s) (list_drop n (kapp_args e)) major found)",
        "Recover the actual substituted major at the same metadata position by drop-map and genuine successful-head transport.",
    ),
    (
        r"def iota_instL_fields (s : Name -> Level) (major : KExpr) (num_fields : Nat) :
 Eq (ListType KExpr)
  (list_drop (Nat.sub (list_length (kapp_args (instL s major))) num_fields) (kapp_args (instL s major)))
  (mapLT (instL s) (list_drop (Nat.sub (list_length (kapp_args major)) num_fields) (kapp_args major))) :=
 Eq.trans (ListType KExpr)
  (list_drop (Nat.sub (list_length (kapp_args (instL s major))) num_fields) (kapp_args (instL s major)))
  (list_drop (Nat.sub (list_length (kapp_args major)) num_fields) (kapp_args (instL s major)))
  (mapLT (instL s) (list_drop (Nat.sub (list_length (kapp_args major)) num_fields) (kapp_args major)))
  (Eq.cong Nat (ListType KExpr)
    (fun (count : Nat) => list_drop (Nat.sub count num_fields) (kapp_args (instL s major)))
    (list_length (kapp_args (instL s major))) (list_length (kapp_args major)) (iota_instL_args_length s major))
  (iota_instL_drop_args s (Nat.sub (list_length (kapp_args major)) num_fields) major)",
        "Field suffix selection retains its actual Nat.sub count after deriving major-spine length equality; no assumed matching field partition.",
    ),
    (
        r"def iota_instL_apply_spine_reconstruct (s : Name -> Level)
 (args : ListType KExpr) (args2 : ListType KExpr) (head : KExpr) (head2 : KExpr)
 (hargs : Eq (ListType KExpr) args2 (mapLT (instL s) args))
 (hhead : Eq KExpr head2 (instL s head)) :
 Eq KExpr (apply_spine args2 head2) (instL s (apply_spine args head)) :=
 Eq.trans KExpr (apply_spine args2 head2) (apply_spine (mapLT (instL s) args) (instL s head))
  (instL s (apply_spine args head))
  (universe_bridge_congr2 (ListType KExpr) KExpr KExpr apply_spine
    args2 (mapLT (instL s) args) head2 (instL s head) hargs hhead)
  (Eq.symm KExpr (instL s (apply_spine args head))
    (apply_spine (mapLT (instL s) args) (instL s head)) (instL_apply_spine s args head))",
        "Reassemble actual substituted application-spine data using the existing instL/apply_spine commutation theorem, not a reduction premise.",
    ),
    (
        r"def iota_instL_contractum (s : Name -> Level) (e : KExpr) (major : KExpr) (md : RecMeta) (rule : RecRule)
 (body : KExpr) (body2 : KExpr) (hbody : Eq KExpr body2 (instL s body)) :
 Eq KExpr (iota_contractum md rule (kapp_args (instL s e)) (kapp_args (instL s major)) (body2)) (instL s (iota_contractum md rule (kapp_args e) (kapp_args major) (body))) :=
 iota_instL_apply_spine_reconstruct s (list_drop (Nat.succ (iota_major_index md)) (kapp_args e)) (list_drop (Nat.succ (iota_major_index md)) (kapp_args (instL s e))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (iota_prefix_count md) (kapp_args e)) body)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args (instL s major))) (recrule_num_fields rule)) (kapp_args (instL s major))) (apply_spine (list_take (iota_prefix_count md) (kapp_args (instL s e))) body2)) (iota_instL_drop_args s (Nat.succ (iota_major_index md)) e) (iota_instL_apply_spine_reconstruct s (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (list_drop (Nat.sub (list_length (kapp_args (instL s major))) (recrule_num_fields rule)) (kapp_args (instL s major))) (apply_spine (list_take (iota_prefix_count md) (kapp_args e)) body) (apply_spine (list_take (iota_prefix_count md) (kapp_args (instL s e))) body2) (iota_instL_fields s major (recrule_num_fields rule)) (iota_instL_apply_spine_reconstruct s (list_take (iota_prefix_count md) (kapp_args e)) (list_take (iota_prefix_count md) (kapp_args (instL s e))) (body) (body2) (iota_instL_take_args s (iota_prefix_count md) e) (hbody)))",
        "Actual three-spine contractum transport from a proved RHS-instance equality; stored RHS invariance is not required or assumed.",
    ),
    (
        r"def iota_instL_head_level_length (s : Name -> Level) (e : KExpr) :
 Eq Nat (level_list_len (kexpr_const_levels (kapp_fn (instL s e)))) (level_list_len (kexpr_const_levels (kapp_fn e))) :=
 Eq.trans Nat (level_list_len (kexpr_const_levels (kapp_fn (instL s e)))) (level_list_len (mapLL (substL s) (kexpr_const_levels (kapp_fn e)))) (level_list_len (kexpr_const_levels (kapp_fn e)))
  (Eq.cong (ListType Level) Nat level_list_len (kexpr_const_levels (kapp_fn (instL s e))) (mapLL (substL s) (kexpr_const_levels (kapp_fn e))) (delta_head_levels_instL s e))
  (level_list_len_mapLL (substL s) (kexpr_const_levels (kapp_fn e)))",
        "Actual head-universe argument count is preserved by raw substitution, including unknown parameters.",
    ),
    (
        r"def iota_instL_fields_guard (s : Name -> Level) (major : KExpr) (rule : RecRule)
 (accepted : Eq Bool (iota_fields_ok rule (kapp_args major)) Bool.true) :
 Eq Bool (iota_fields_ok rule (kapp_args (instL s major))) Bool.true :=
 Eq.trans Bool (iota_fields_ok rule (kapp_args (instL s major))) (iota_fields_ok rule (kapp_args major)) Bool.true
  (Eq.cong Nat Bool (fun (len : Nat) => nat_eqb (Nat.sub (recrule_num_fields rule) len) Nat.zero)
   (list_length (kapp_args (instL s major))) (list_length (kapp_args major)) (iota_instL_args_length s major)) accepted",
        "The actual field-availability Boolean guard is preserved by the derived constructor argument-length equation.",
    ),
    (
        r"def iota_instL_arity_guard (s : Name -> Level) (e : KExpr) (md : RecMeta)
 (accepted : Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature md))) (level_list_len (kexpr_const_levels (kapp_fn e)))) Bool.true) :
 Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature md))) (level_list_len (kexpr_const_levels (kapp_fn (instL s e))))) Bool.true :=
 Eq.trans Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature md))) (level_list_len (kexpr_const_levels (kapp_fn (instL s e)))))
  (nat_eqb (name_list_len (kconst_params (recmeta_signature md))) (level_list_len (kexpr_const_levels (kapp_fn e)))) Bool.true
  (Eq.cong Nat Bool (fun (len : Nat) => nat_eqb (name_list_len (kconst_params (recmeta_signature md))) len)
   (level_list_len (kexpr_const_levels (kapp_fn (instL s e)))) (level_list_len (kexpr_const_levels (kapp_fn e))) (iota_instL_head_level_length s e)) accepted",
        "The actual signature/head-argument Boolean arity guard remains true after universe substitution.",
    ),
    (
        r"def iota_instL_rhs_instance (s : Name -> Level) (e : KExpr) (md : RecMeta) (rule : RecRule)
 (supported : KExprParamSupport (kconst_params (recmeta_signature md)) (recrule_rhs rule)) :
 Eq KExpr (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (kexpr_const_levels (kapp_fn (instL s e)))) (instL s (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e)))) :=
 Eq.trans KExpr (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (kexpr_const_levels (kapp_fn (instL s e))))
  (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (mapLL (substL s) (kexpr_const_levels (kapp_fn e))))
  (instL s (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))))
  (Eq.cong (ListType Level) KExpr (fun (us : ListType Level) => recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) us)
   (kexpr_const_levels (kapp_fn (instL s e))) (mapLL (substL s) (kexpr_const_levels (kapp_fn e))) (delta_head_levels_instL s e))
  (Eq.symm KExpr (instL s (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))))
   (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (mapLL (substL s) (kexpr_const_levels (kapp_fn e))))
   (instL_instLevels_supported (kconst_params (recmeta_signature md)) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e)) supported s))",
        "Actual head levels and supported raw fusion derive once-instantiated RHS transport. No arity, NoDup, or desired output equality is a premise.",
    ),
    (
        r"def RecEnvRhsParamFree (env : RecEnv) : Prop :=
 forall (recname : Name) (cname : Name) (rule : RecRule),
 Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) ->
 KExprParamSupport (ListType.nil Name) (recrule_rhs rule)",
        "Legacy parameter-free support interface: every actually selected stored RHS has no universe parameters; retained as a strictly stronger sufficient condition. This structural invariant is not RecEnvClosed, an output-step theorem, or a production admission claim.",
    ),
    (
        r"def levelParamSupport_nil_weaken (ps : ListType Name) (u : Level)
 (h : LevelParamSupport (ListType.nil Name) u) : LevelParamSupport ps u :=
 LevelParamSupport.rec (ListType.nil Name)
  (fun (v : Level) (_h : LevelParamSupport (ListType.nil Name) v) => LevelParamSupport ps v)
  (LevelParamSupport.zero ps)
  (fun (v : Level) (_hv : LevelParamSupport (ListType.nil Name) v) (ih : LevelParamSupport ps v) => LevelParamSupport.succ ps v ih)
  (fun (a : Level) (b : Level) (_ha : LevelParamSupport (ListType.nil Name) a) (_hb : LevelParamSupport (ListType.nil Name) b)
   (iha : LevelParamSupport ps a) (ihb : LevelParamSupport ps b) => LevelParamSupport.max ps a b iha ihb)
  (fun (a : Level) (b : Level) (_ha : LevelParamSupport (ListType.nil Name) a) (_hb : LevelParamSupport (ListType.nil Name) b)
   (iha : LevelParamSupport ps a) (ihb : LevelParamSupport ps b) => LevelParamSupport.imax ps a b iha ihb)
  (fun (n : Name) (i : Nat) (found : Eq (OptionType Nat) (nameIdx (ListType.nil Name) n) (OptionType.some Nat i)) =>
   option_none_ne_some Nat i (LevelParamSupport ps (Level.param n)) found) u h",
        "Parameter-free level syntax is supported under any declared parameter list; the impossible parameter case uses actual nil lookup.",
    ),
    (
        r"def levelListParamSupport_nil_weaken (ps : ListType Name) (us : ListType Level)
 (h : LevelListParamSupport (ListType.nil Name) us) : LevelListParamSupport ps us :=
 LevelListParamSupport.rec (ListType.nil Name)
  (fun (xs : ListType Level) (_h : LevelListParamSupport (ListType.nil Name) xs) => LevelListParamSupport ps xs)
  (LevelListParamSupport.nil ps)
  (fun (u : Level) (xs : ListType Level) (hu : LevelParamSupport (ListType.nil Name) u)
   (_hxs : LevelListParamSupport (ListType.nil Name) xs) (ih : LevelListParamSupport ps xs) =>
   LevelListParamSupport.cons ps u xs (levelParamSupport_nil_weaken ps u hu) ih) us h",
        "Preserve every constant-level list element when weakening empty universe support.",
    ),
    (
        r"def kexprParamSupport_nil_weaken (ps : ListType Name) (e : KExpr)
 (h : KExprParamSupport (ListType.nil Name) e) : KExprParamSupport ps e :=
 KExprParamSupport.rec (ListType.nil Name)
  (fun (x : KExpr) (_h : KExprParamSupport (ListType.nil Name) x) => KExprParamSupport ps x)
  (fun (u : Level) (hu : LevelParamSupport (ListType.nil Name) u) =>
   KExprParamSupport.sort ps u (levelParamSupport_nil_weaken ps u hu))
  (fun (i : Nat) => KExprParamSupport.bvar ps i)
  (fun (a : KExpr) (b : KExpr) (_ha : KExprParamSupport (ListType.nil Name) a) (_hb : KExprParamSupport (ListType.nil Name) b)
   (iha : KExprParamSupport ps a) (ihb : KExprParamSupport ps b) => KExprParamSupport.app ps a b iha ihb)
  (fun (a : KExpr) (b : KExpr) (_ha : KExprParamSupport (ListType.nil Name) a) (_hb : KExprParamSupport (ListType.nil Name) b)
   (iha : KExprParamSupport ps a) (ihb : KExprParamSupport ps b) => KExprParamSupport.lam ps a b iha ihb)
  (fun (a : KExpr) (b : KExpr) (_ha : KExprParamSupport (ListType.nil Name) a) (_hb : KExprParamSupport (ListType.nil Name) b)
   (iha : KExprParamSupport ps a) (ihb : KExprParamSupport ps b) => KExprParamSupport.pi ps a b iha ihb)
  (fun (n : Name) (us : ListType Level) (hus : LevelListParamSupport (ListType.nil Name) us) =>
   KExprParamSupport.const ps n us (levelListParamSupport_nil_weaken ps us hus))
  (fun (A : KExpr) (v : KExpr) (b : KExpr) (_hA : KExprParamSupport (ListType.nil Name) A)
   (_hv : KExprParamSupport (ListType.nil Name) v) (_hb : KExprParamSupport (ListType.nil Name) b)
   (ihA : KExprParamSupport ps A) (ihv : KExprParamSupport ps v) (ihb : KExprParamSupport ps b) =>
   KExprParamSupport.let_ ps A v b ihA ihv ihb)
  (fun (n : Name) (i : Nat) (sub : KExpr) (_hsub : KExprParamSupport (ListType.nil Name) sub)
   (ih : KExprParamSupport ps sub) => KExprParamSupport.proj ps n i sub ih)
  (fun (n : Nat) => KExprParamSupport.lit ps n) e h",
        "All nine expression constructors preserve parameter-free support under an arbitrary stored signature; no semantic invariance is mistaken for syntactic support.",
    ),
    (
        r"def RecEnvRhsParamSupported (env : RecEnv) : Prop :=
 forall (recname : Name) (md : RecMeta) (cname : Name) (rule : RecRule),
 Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta md) ->
 Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) ->
 KExprParamSupport (kconst_params (recmeta_signature md)) (recrule_rhs rule)",
        "Every selected stored rule is supported under the actual selected metadata signature. Both lookup equations share the recursor key; no instance equality or output typing is a field.",
    ),
    (
        r"def rec_env_rhs_paramfree_supported (env : RecEnv) (free : RecEnvRhsParamFree env) :
 RecEnvRhsParamSupported env :=
 fun (rn : Name) (md : RecMeta) (cn : Name) (rule : RecRule)
  (_metadata : Eq (OptionType RecMeta) (recmeta_for env rn) (OptionType.some RecMeta md))
  (found : Eq (OptionType RecRule) (recrule_for env rn cn) (OptionType.some RecRule rule)) =>
  kexprParamSupport_nil_weaken (kconst_params (recmeta_signature md)) (recrule_rhs rule)
   (free rn cn rule found)",
        "The old parameter-free environment condition remains an honest stronger special case of signature-relative support.",
    ),
    (
        r"def iota_step_instL_supported (env : RecEnv) (supported : RecEnvRhsParamSupported env)
 (s : Name -> Level) (e : KExpr) (r : KExpr) (step : iota_step env e r) :
 iota_step env (instL s e) (instL s r) :=
 iota_reduct_full_inv env e r (iota_step env (instL s e) (instL s r)) step
  (fun (recname : Name) (md : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule)
   (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname))
   (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta md))
   (h3 : Eq (OptionType KExpr) (list_head (list_drop (iota_major_index md) (kapp_args e))) (OptionType.some KExpr major))
   (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname))
   (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule))
   (hfields : Eq Bool (iota_fields_ok rule (kapp_args major)) Bool.true)
   (harity : Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature md))) (level_list_len (kexpr_const_levels (kapp_fn e)))) Bool.true)
   (returned : Eq KExpr r (iota_contractum md rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))))) =>
   iota_reduct_full_recon env (instL s e) (instL s r) recname md (instL s major) cname rule
    (Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn (instL s e))) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname) (delta_head_name_instL s e) h1)
    h2 (iota_instL_major_at s (iota_major_index md) e major h3)
    (Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn (instL s major))) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) (delta_head_name_instL s major) h4)
    h5 (iota_instL_fields_guard s major rule hfields) (iota_instL_arity_guard s e md harity)
    (Eq.trans KExpr (instL s r) (instL s (iota_contractum md rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))))) (iota_contractum md rule (kapp_args (instL s e)) (kapp_args (instL s major)) (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (kexpr_const_levels (kapp_fn (instL s e)))))
     (Eq.cong KExpr KExpr (instL s) r (iota_contractum md rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e)))) returned)
     (Eq.symm KExpr (iota_contractum md rule (kapp_args (instL s e)) (kapp_args (instL s major)) (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (kexpr_const_levels (kapp_fn (instL s e))))) (instL s (iota_contractum md rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e)))))
      (iota_instL_contractum s e major md rule (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))) (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (kexpr_const_levels (kapp_fn (instL s e))))
       (iota_instL_rhs_instance s e md rule (supported recname md cname rule h2 h5))))))",
        "Actual guarded iota commutes with universe substitution from the selected stored RHS's signature-relative support. All lookups, guards and once-instantiated output are derived.",
    ),
    (
        r"def iota_step_instL_paramfree (env : RecEnv) (supported : RecEnvRhsParamFree env)
 (s : Name -> Level) (e : KExpr) (r : KExpr) (step : iota_step env e r) :
 iota_step env (instL s e) (instL s r) :=
 iota_step_instL_supported env (rec_env_rhs_paramfree_supported env supported) s e r step",
        "Compatibility theorem retaining the old genuine parameter-free premise as a proved stronger special case; the active operator remains guarded and instantiated.",
    ),
];

const CONTROLS: &[(&str, &str)] = &[
    (
        r"def rec_env_single_rhs_property (recname : Name) (cname : Name) (md : RecMeta)
 (num_fields : Nat) (body : KExpr) (P : KExpr -> Prop) (support : P body) :
 forall (rn : Name) (cn : Name) (selected : RecRule),
 Eq (OptionType RecRule) (recrule_for (RecEnv.addRec RecEnv.empty recname md (RecRules.cons (RecRule.mk cname num_fields body) RecRules.nil)) rn cn) (OptionType.some RecRule selected) ->
 P (recrule_rhs selected) :=
 fun (rn : Name) (cn : Name) (selected : RecRule)
   (found : Eq (OptionType RecRule) (recrule_for (RecEnv.addRec RecEnv.empty recname md (RecRules.cons (RecRule.mk cname num_fields body) RecRules.nil)) rn cn) (OptionType.some RecRule selected)) =>
 opt_bind_some_inv RecRules RecRule (recrules_for (RecEnv.addRec RecEnv.empty recname md (RecRules.cons (RecRule.mk cname num_fields body) RecRules.nil)) rn)
   (fun (rs : RecRules) => recrule_in_rules rs cn) selected (P (recrule_rhs selected)) found
   (fun (rs : RecRules)
     (found_list : Eq (OptionType RecRules) (recrules_for (RecEnv.addRec RecEnv.empty recname md (RecRules.cons (RecRule.mk cname num_fields body) RecRules.nil)) rn) (OptionType.some RecRules rs))
     (found_rule : Eq (OptionType RecRule) (recrule_in_rules rs cn) (OptionType.some RecRule selected)) =>
     opt_pick_some_inv RecRules (name_eqb recname rn) (RecRules.cons (RecRule.mk cname num_fields body) RecRules.nil) (OptionType.none RecRules) rs (P (recrule_rhs selected)) found_list
       (fun (_same_name : Eq Bool (name_eqb recname rn) Bool.true)
         (same_list : Eq RecRules (RecRules.cons (RecRule.mk cname num_fields body) RecRules.nil) rs) =>
         Eq.subst RecRules
           (fun (chosen : RecRules) =>
             Eq (OptionType RecRule) (recrule_in_rules chosen cn) (OptionType.some RecRule selected) -> (P (recrule_rhs selected)))
           (RecRules.cons (RecRule.mk cname num_fields body) RecRules.nil) rs same_list
           (fun (hit : Eq (OptionType RecRule) (recrule_in_rules (RecRules.cons (RecRule.mk cname num_fields body) RecRules.nil) cn) (OptionType.some RecRule selected)) =>
             opt_pick_some_inv RecRule (name_eqb cname cn) (RecRule.mk cname num_fields body) (OptionType.none RecRule) selected (P (recrule_rhs selected)) hit
               (fun (_same_ctor : Eq Bool (name_eqb cname cn) Bool.true) (same_rule : Eq RecRule (RecRule.mk cname num_fields body) selected) =>
                 Eq.subst RecRule (fun (r : RecRule) => P (recrule_rhs r))
                   (RecRule.mk cname num_fields body) selected same_rule support)
               (fun (_different_ctor : Eq Bool (name_eqb cname cn) Bool.false)
                 (impossible : Eq (OptionType RecRule) (OptionType.none RecRule) (OptionType.some RecRule selected)) =>
                 option_none_ne_some RecRule selected (P (recrule_rhs selected)) impossible))
           found_rule)
       (fun (_different_name : Eq Bool (name_eqb recname rn) Bool.false)
         (impossible : Eq (OptionType RecRules) (OptionType.none RecRules) (OptionType.some RecRules rs)) =>
         option_none_ne_some RecRules rs (P (recrule_rhs selected)) impossible))",
        "A property of the single stored raw RHS is transported through the actual rule-list and name lookups, without any output-evaluator premise.",
    ),
    (
        r"def rec_env_single_rhs_paramfree (recname : Name) (cname : Name) (md : RecMeta)
 (num_fields : Nat) (body : KExpr) (support : KExprParamSupport (ListType.nil Name) body) :
 RecEnvRhsParamFree (RecEnv.addRec RecEnv.empty recname md (RecRules.cons (RecRule.mk cname num_fields body) RecRules.nil)) :=
 rec_env_single_rhs_property recname cname md num_fields body
  (fun (e : KExpr) => KExprParamSupport (ListType.nil Name) e) support",
        "Compatibility singleton witness for genuine empty-parameter support; its lookup proof is shared with the signature-relative case.",
    ),
    (
        r"def rec_env_single_rhs_supported (recname : Name) (cname : Name) (md : RecMeta)
 (num_fields : Nat) (body : KExpr)
 (support : KExprParamSupport (kconst_params (recmeta_signature md)) body) :
 RecEnvRhsParamSupported (RecEnv.addRec RecEnv.empty recname md (RecRules.cons (RecRule.mk cname num_fields body) RecRules.nil)) :=
 fun (rn : Name) (selected_md : RecMeta) (cn : Name) (rule : RecRule)
  (metadata : Eq (OptionType RecMeta) (recmeta_for (RecEnv.addRec RecEnv.empty recname md (RecRules.cons (RecRule.mk cname num_fields body) RecRules.nil)) rn) (OptionType.some RecMeta selected_md))
  (found : Eq (OptionType RecRule) (recrule_for (RecEnv.addRec RecEnv.empty recname md (RecRules.cons (RecRule.mk cname num_fields body) RecRules.nil)) rn cn) (OptionType.some RecRule rule)) =>
 opt_pick_some_inv RecMeta (name_eqb recname rn) md (OptionType.none RecMeta) selected_md
  (KExprParamSupport (kconst_params (recmeta_signature selected_md)) (recrule_rhs rule)) metadata
  (fun (_same_name : Eq Bool (name_eqb recname rn) Bool.true) (same_md : Eq RecMeta md selected_md) =>
   rec_env_single_rhs_property recname cname md num_fields body
    (fun (e : KExpr) => KExprParamSupport (kconst_params (recmeta_signature selected_md)) e)
    (Eq.subst RecMeta (fun (m : RecMeta) => KExprParamSupport (kconst_params (recmeta_signature m)) body)
     md selected_md same_md support) rn cn rule found)
  (fun (_different_name : Eq Bool (name_eqb recname rn) Bool.false)
   (impossible : Eq (OptionType RecMeta) (OptionType.none RecMeta) (OptionType.some RecMeta selected_md)) =>
   option_none_ne_some RecMeta selected_md (KExprParamSupport (kconst_params (recmeta_signature selected_md)) (recrule_rhs rule)) impossible)",
        "The actual singleton metadata and rule lookups discharge signature-relative raw RHS support; metadata equality is derived from the same real name lookup.",
    ),
    (
        r"def iota_inst_schematic_meta : RecMeta :=
 RecMeta.mk Nat.zero Nat.zero Nat.zero Nat.zero Bool.true
  (KConstSig.mk (ListType.cons Name Name.anonymous (ListType.nil Name)) (KExpr.sort (Level.param Name.anonymous))) Nat.zero",
        "Synthetic reduction-only singleton-parameter metadata; no recursor type-validity or production admission claim.",
    ),
    (
        r"def iota_inst_schematic_rhs : KExpr := KExpr.lam (KExpr.sort (Level.param Name.anonymous)) (KExpr.bvar Nat.zero)",
        "One stored schematic lambda template, not an already instantiated RHS.",
    ),
    (
        r"def iota_inst_schematic_env : RecEnv :=
 RecEnv.addRec RecEnv.empty Name.anonymous iota_inst_schematic_meta
  (RecRules.cons (RecRule.mk (Name.str Name.anonymous Nat.zero) (Nat.succ Nat.zero) iota_inst_schematic_rhs) RecRules.nil)",
        "Actual singleton table used by the guarded universe-substitution caller.",
    ),
    (
        r"def iota_inst_schematic_supported : RecEnvRhsParamSupported iota_inst_schematic_env :=
 rec_env_single_rhs_supported Name.anonymous (Name.str Name.anonymous Nat.zero) iota_inst_schematic_meta
  (Nat.succ Nat.zero) iota_inst_schematic_rhs
  (KExprParamSupport.lam (ListType.cons Name Name.anonymous (ListType.nil Name)) (KExpr.sort (Level.param Name.anonymous)) (KExpr.bvar Nat.zero)
   (KExprParamSupport.sort (ListType.cons Name Name.anonymous (ListType.nil Name)) (Level.param Name.anonymous)
    (LevelParamSupport.param (ListType.cons Name Name.anonymous (ListType.nil Name)) Name.anonymous Nat.zero (Eq.refl (OptionType Nat) (OptionType.some Nat Nat.zero))))
   (KExprParamSupport.bvar (ListType.cons Name Name.anonymous (ListType.nil Name)) Nat.zero))",
        "Actual selected-template support under its declared parameter, with a genuine nonempty universe scope.",
    ),
    (
        r"def iota_inst_schematic_input (u : Level) : KExpr :=
 KExpr.app
  (KExpr.app (KExpr.const Name.anonymous (ListType.cons Level u (ListType.nil Level)))
   (KExpr.app (KExpr.const (Name.str Name.anonymous Nat.zero) (ListType.nil Level)) (KExpr.sort u)))
  (KExpr.lit Nat.zero)",
        "Actual redex carries the supplied head universe and a field plus an extra argument.",
    ),
    (
        r"def iota_inst_schematic_output (u : Level) : KExpr :=
 KExpr.app (KExpr.app (KExpr.lam (KExpr.sort u) (KExpr.bvar Nat.zero)) (KExpr.sort u)) (KExpr.lit Nat.zero)",
        "Independently spelled expected once-instantiated RHS applied to field and extra arguments.",
    ),
    (
        r"def iota_inst_schematic_initial (u : Level) :
 iota_step iota_inst_schematic_env (iota_inst_schematic_input u) (iota_inst_schematic_output u) :=
 Eq.refl (OptionType KExpr) (OptionType.some KExpr (iota_inst_schematic_output u))",
        "Actual guarded iota computes the schematic template instance for arbitrary supplied raw universes.",
    ),
    (
        r"def iota_inst_schematic_caller (s : Name -> Level) (u : Level) :
 iota_step iota_inst_schematic_env (instL s (iota_inst_schematic_input u)) (instL s (iota_inst_schematic_output u)) :=
 iota_step_instL_supported iota_inst_schematic_env iota_inst_schematic_supported s
  (iota_inst_schematic_input u) (iota_inst_schematic_output u) (iota_inst_schematic_initial u)",
        "Direct caller of the general actual-iota closure using the proved nonempty-signature support witness.",
    ),
    (
        r"def iota_inst_schematic_self_parameter :
 iota_step iota_inst_schematic_env
  (iota_inst_schematic_input (Level.succ (Level.param Name.anonymous)))
  (iota_inst_schematic_output (Level.succ (Level.param Name.anonymous))) :=
 iota_inst_schematic_initial (Level.succ (Level.param Name.anonymous))",
        "Nonclosed supplied universe contains the template parameter itself; the operator substitutes exactly once.",
    ),
    (
        r"def iota_inst_schematic_nonzero_transport :
 iota_step iota_inst_schematic_env
  (iota_inst_schematic_input (Level.succ (Level.succ Level.zero)))
  (iota_inst_schematic_output (Level.succ (Level.succ Level.zero))) :=
 iota_inst_schematic_caller (fun (_n : Name) => Level.succ Level.zero)
  (Level.succ (Level.param Name.anonymous))",
        "Nonidentity substitution through a nonclosed head level and schematic stored lambda derives the actual level-two step.",
    ),
    (
        r"def iota_inst_fixture_env (num_fields : Nat) (body : KExpr) : RecEnv :=
 RecEnv.addRec RecEnv.empty Name.anonymous
  (RecMeta.mk Nat.zero Nat.zero Nat.zero Nat.zero Bool.true (KConstSig.mk (ListType.nil Name) (KExpr.sort Level.zero)) Nat.zero)
  (RecRules.cons (RecRule.mk (Name.str Name.anonymous Nat.zero) num_fields body) RecRules.nil)",
        "Actual singleton current-model recursor environment parameterized by field count and RHS. The constructor key differs from the recursor key. The nil-parameter signature is reduction-test data, not a recursor typing claim.",
    ),
    (
        r"def iota_inst_supported_rhs : KExpr :=
 KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)",
        "Parameter-free stored RHS with a binder, so actual field application and later beta behavior are nontrivial.",
    ),
    (
        r"def iota_inst_supported_env : RecEnv :=
 iota_inst_fixture_env (Nat.succ Nat.zero) iota_inst_supported_rhs",
        "Actual one-field recursor fixture, not an assumed supporting environment.",
    ),
    (
        r"def iota_inst_supported_env_support : RecEnvRhsParamFree iota_inst_supported_env :=
 rec_env_single_rhs_paramfree Name.anonymous (Name.str Name.anonymous Nat.zero)
  (RecMeta.mk Nat.zero Nat.zero Nat.zero Nat.zero Bool.true (KConstSig.mk (ListType.nil Name) (KExpr.sort Level.zero)) Nat.zero) (Nat.succ Nat.zero) iota_inst_supported_rhs
  (KExprParamSupport.lam (ListType.nil Name) (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)
    (KExprParamSupport.sort (ListType.nil Name) Level.zero (LevelParamSupport.zero (ListType.nil Name)))
    (KExprParamSupport.bvar (ListType.nil Name) Nat.zero))",
        "Discharge the actual selected-RHS support interface for the concrete environment, with a real structural binder proof.",
    ),
    (
        r"def iota_inst_supported_input (u : Level) : KExpr :=
 KExpr.app
  (KExpr.app (KExpr.const Name.anonymous (ListType.nil Level))
    (KExpr.app (KExpr.const (Name.str Name.anonymous Nat.zero) (ListType.nil Level)) (KExpr.sort u)))
  (KExpr.lit Nat.zero)",
        "An actual constructor field plus extra application argument, exercising both inner field and outer extra spines.",
    ),
    (
        r"def iota_inst_supported_output (u : Level) : KExpr :=
 KExpr.app (KExpr.app iota_inst_supported_rhs (KExpr.sort u)) (KExpr.lit Nat.zero)",
        "The actual guarded-iota result: the nil-parameter RHS instance with field and extra arguments, without beta reduction.",
    ),
    (
        r"def iota_inst_supported_initial_step (u : Level) :
 iota_step iota_inst_supported_env (iota_inst_supported_input u) (iota_inst_supported_output u) :=
 Eq.refl (OptionType KExpr) (OptionType.some KExpr (iota_inst_supported_output u))",
        "Actual computed successful iota step for the field-plus-extra fixture at any universe argument.",
    ),
    (
        r"def iota_inst_supported_spine_caller (s : Name -> Level) (u : Level) :
 iota_step iota_inst_supported_env (instL s (iota_inst_supported_input u)) (instL s (iota_inst_supported_output u)) :=
 iota_step_instL_paramfree iota_inst_supported_env iota_inst_supported_env_support s
  (iota_inst_supported_input u) (iota_inst_supported_output u) (iota_inst_supported_initial_step u)",
        "An inhabited actual caller of generic iota universe-instantiation preservation, using the proved support interface and the original successful computation.",
    ),
    (
        r"def iota_inst_supported_nonzero :
 iota_step iota_inst_supported_env
  (iota_inst_supported_input (Level.succ Level.zero)) (iota_inst_supported_output (Level.succ Level.zero)) :=
 iota_inst_supported_spine_caller (fun (_n : Name) => Level.succ Level.zero) (Level.param Name.anonymous)",
        "Closed nonidentity-substitution caller replacing an open universe parameter with one; actual field and extra argument survive the reconstructed computation.",
    ),
    (
        r"def iota_inst_unsupported_env : RecEnv :=
 iota_inst_fixture_env Nat.zero (KExpr.sort (Level.param Name.anonymous))",
        "Counterexample environment: its RHS contains an undeclared universe parameter, outside its stored nil signature; actual instantiation leaves that unknown name unchanged.",
    ),
    (
        r"def iota_inst_unsupported_input : KExpr :=
 KExpr.app (KExpr.const Name.anonymous (ListType.nil Level))
  (KExpr.const (Name.str Name.anonymous Nat.zero) (ListType.nil Level))",
        "Universe-free redex input, unchanged by every instL substitution, selecting the parameter-bearing stored RHS.",
    ),
    (
        r"def iota_inst_unsupported_bvar_closed :
 is_closed_at (KExpr.sort (Level.param Name.anonymous)) Nat.zero :=
 is_closed_at.sort (Level.param Name.anonymous) Nat.zero",
        "The unsupported RHS is genuinely closed with respect to de Bruijn variables. Term-variable closedness is not the universe-support premise.",
    ),
    (
        r"def iota_inst_unsupported_initial_step :
 iota_step iota_inst_unsupported_env iota_inst_unsupported_input (KExpr.sort (Level.param Name.anonymous)) :=
 Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort (Level.param Name.anonymous)))",
        "Actual initial success does not imply parameter-free RHS support.",
    ),
    (
        r"def iota_inst_unsupported_closure_fails :
 iota_step iota_inst_unsupported_env
  (instL (fun (_n : Name) => Level.zero) iota_inst_unsupported_input)
  (instL (fun (_n : Name) => Level.zero) (KExpr.sort (Level.param Name.anonymous))) -> Empty :=
 fun (h : iota_step iota_inst_unsupported_env
  (instL (fun (_n : Name) => Level.zero) iota_inst_unsupported_input)
  (instL (fun (_n : Name) => Level.zero) (KExpr.sort (Level.param Name.anonymous)))) =>
 unsupported_fusion_fails
  (Eq.symm Level (Level.param Name.anonymous) Level.zero
    (kexpr_sort_inj (Level.param Name.anonymous) Level.zero
      (option_some_inj KExpr (KExpr.sort (Level.param Name.anonymous)) (KExpr.sort Level.zero) h)))",
        "Constructive counterexample: the input is unchanged, so actual iota still returns its stored parameter, while instL changes the alleged output to zero. Computed result equality would contradict the existing parameter/zero discriminator.",
    ),
];

impl Specification {
    /// Requires actual support syntax, generic delta spine/instL substrate,
    /// existing mapLT head/tail/length proofs, and iota inversion/reconstruction.
    pub(super) fn add_semantic_iota_universe_instantiation(&mut self) -> Result<(), SpecError> {
        for (source, description) in PROOFS.iter().chain(CONTROLS) {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }
}
#[cfg(test)]
mod tests {
    #[test]
    fn current_iota_universe_instantiation_has_checked_proofs_and_callers() {
        let spec = crate::test_utils::build_spec_with_stack();
        for name in [
            "substL_nil_support_id",
            "mapLL_nil_support_id",
            "instL_nil_support_id",
            "mapLT_list_drop",
            "mapLT_list_take",
            "iota_instL_drop_args",
            "iota_instL_take_args",
            "iota_instL_args_length",
            "iota_instL_major_at",
            "iota_instL_fields",
            "iota_instL_apply_spine_reconstruct",
            "iota_instL_contractum",
            "iota_step_instL_paramfree",
            "levelParamSupport_nil_weaken",
            "levelListParamSupport_nil_weaken",
            "kexprParamSupport_nil_weaken",
            "rec_env_rhs_paramfree_supported",
            "iota_instL_head_level_length",
            "iota_instL_fields_guard",
            "iota_instL_arity_guard",
            "iota_instL_rhs_instance",
            "iota_step_instL_supported",
            "rec_env_single_rhs_property",
            "rec_env_single_rhs_supported",
            "iota_inst_schematic_supported",
            "iota_inst_schematic_initial",
            "iota_inst_schematic_caller",
            "iota_inst_schematic_self_parameter",
            "iota_inst_schematic_nonzero_transport",
            "rec_env_single_rhs_paramfree",
            "iota_inst_supported_env_support",
            "iota_inst_supported_initial_step",
            "iota_inst_supported_spine_caller",
            "iota_inst_supported_nonzero",
            "iota_inst_unsupported_bvar_closed",
            "iota_inst_unsupported_initial_step",
            "iota_inst_unsupported_closure_fails",
        ] {
            let definition = spec
                .definitions()
                .get(name)
                .expect("registered checked current-iota instantiation declaration");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
    }
    #[test]
    fn guarded_iota_rejects_erasure_missing_arity_and_unscoped_support() {
        let mut spec = crate::test_utils::build_spec_with_stack();
        for source in [
            r"def iota_inst_forged_schematic_erasure :
 iota_step iota_inst_schematic_env
  (iota_inst_schematic_input (Level.succ Level.zero)) (iota_inst_schematic_output Level.zero) :=
 Eq.refl (OptionType KExpr) (OptionType.some KExpr (iota_inst_schematic_output Level.zero))",
            r"def iota_inst_forged_missing_arity :
 iota_step iota_inst_schematic_env
  (KExpr.app (KExpr.app (KExpr.const Name.anonymous (ListType.nil Level))
    (KExpr.app (KExpr.const (Name.str Name.anonymous Nat.zero) (ListType.nil Level)) (KExpr.sort Level.zero)))
   (KExpr.lit Nat.zero))
  (iota_inst_schematic_output Level.zero) :=
 Eq.refl (OptionType KExpr) (OptionType.some KExpr (iota_inst_schematic_output Level.zero))",
            r"def iota_inst_forged_unscoped_support :
 KExprParamSupport (ListType.nil Name) (KExpr.sort (Level.param Name.anonymous)) :=
 KExprParamSupport.sort (ListType.nil Name) (Level.param Name.anonymous)
  (LevelParamSupport.param (ListType.nil Name) Name.anonymous Nat.zero
   (Eq.refl (OptionType Nat) (OptionType.some Nat Nat.zero)))",
        ] {
            assert!(
                spec.add_recursive_def(source, "Negative actual guarded-iota migration control.").is_err(),
                "actual guards, once-instantiated RHS and declared parameter support cannot be forged"
            );
        }
    }
}
