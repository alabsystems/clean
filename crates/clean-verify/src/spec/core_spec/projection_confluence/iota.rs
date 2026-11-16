// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact checked iota cohort from projection-registration.RmczqJ.
//! Raw input types, values and carrier declarations are preserved verbatim.
//! This reduction evidence is not a typing or source-admission theorem.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Proof(
        "projection_parallel_list_take",
        r"forall (R : RedEnv) (k : Nat) (xs ys : ListType KExpr)
 (h : projection_parallel_list R xs ys), projection_parallel_list R (list_take k xs) (list_take k ys)",
        r"fun (R : RedEnv) (k : Nat) (xs ys : ListType KExpr)
 (h : projection_parallel_list R xs ys) => @Nat.rec
  (fun (n : Nat) => forall (as bs : ListType KExpr), projection_parallel_list R as bs ->
   projection_parallel_list R (list_take n as) (list_take n bs))
  (fun (as bs : ListType KExpr) (ht : projection_parallel_list R as bs) => @projection_parallel_list.nil R)
  (fun (n : Nat)
   (ih : forall (as bs : ListType KExpr), projection_parallel_list R as bs -> projection_parallel_list R (list_take n as) (list_take n bs))
   (as bs : ListType KExpr) (ht : projection_parallel_list R as bs) =>
   @projection_parallel_list.rec R
    (fun (aa bb : ListType KExpr) (step : projection_parallel_list R aa bb) =>
     projection_parallel_list R (list_take (Nat.succ n) aa) (list_take (Nat.succ n) bb))
    (@projection_parallel_list.nil R)
    (fun (a b : KExpr) (aa bb : ListType KExpr) (ab : projection_parallel R a b)
     (tail : projection_parallel_list R aa bb)
     (unused : projection_parallel_list R (list_take (Nat.succ n) aa) (list_take (Nat.succ n) bb)) =>
     @projection_parallel_list.cons R a b (list_take n aa) (list_take n bb) ab (ih aa bb tail)) as bs ht) k xs ys h",
    ),
    DeclarationInput::Proof(
        "projection_parallel_iota_fields_ok",
        r"forall (R : RedEnv) (rule : RecRule) (xs ys : ListType KExpr)
 (h : projection_parallel_list R xs ys), @Eq Bool (iota_fields_ok rule xs) (iota_fields_ok rule ys)",
        r"fun (R : RedEnv) (rule : RecRule) (xs ys : ListType KExpr)
 (h : projection_parallel_list R xs ys) => Eq.cong Nat Bool (fun (len : Nat) => nat_eqb (Nat.sub (recrule_num_fields rule) len) Nat.zero)
  (list_length xs) (list_length ys) (projection_parallel_list_length R xs ys h)",
    ),
    DeclarationInput::Proof(
        "projection_parallel_iota_contractum",
        r"forall (R : RedEnv) (mta : RecMeta) (rule : RecRule)
 (xs ys majorXs majorYs : ListType KExpr) (rhs : KExpr)
 (args : projection_parallel_list R xs ys) (majorArgs : projection_parallel_list R majorXs majorYs), projection_parallel R (iota_contractum mta rule xs majorXs rhs) (iota_contractum mta rule ys majorYs rhs)",
        r"fun (R : RedEnv) (mta : RecMeta) (rule : RecRule)
 (xs ys majorXs majorYs : ListType KExpr) (rhs : KExpr)
 (args : projection_parallel_list R xs ys) (majorArgs : projection_parallel_list R majorXs majorYs) => projection_parallel_list_apply R
  (list_drop (Nat.succ (iota_major_index mta)) xs) (list_drop (Nat.succ (iota_major_index mta)) ys)
  (projection_parallel_list_drop R (Nat.succ (iota_major_index mta)) xs ys args)
  (apply_spine (list_drop (Nat.sub (list_length majorXs) (recrule_num_fields rule)) majorXs)
   (apply_spine (list_take (iota_prefix_count mta) xs) rhs))
  (apply_spine (list_drop (Nat.sub (list_length majorYs) (recrule_num_fields rule)) majorYs)
   (apply_spine (list_take (iota_prefix_count mta) ys) rhs))
  (projection_parallel_list_apply R
   (list_drop (Nat.sub (list_length majorXs) (recrule_num_fields rule)) majorXs)
   (list_drop (Nat.sub (list_length majorYs) (recrule_num_fields rule)) majorYs)
   (Eq.substType Nat
    (fun (len : Nat) => projection_parallel_list R
     (list_drop (Nat.sub (list_length majorXs) (recrule_num_fields rule)) majorXs)
     (list_drop (Nat.sub len (recrule_num_fields rule)) majorYs))
    (list_length majorXs) (list_length majorYs) (projection_parallel_list_length R majorXs majorYs majorArgs)
    (projection_parallel_list_drop R (Nat.sub (list_length majorXs) (recrule_num_fields rule)) majorXs majorYs majorArgs))
   (apply_spine (list_take (iota_prefix_count mta) xs) rhs) (apply_spine (list_take (iota_prefix_count mta) ys) rhs)
   (projection_parallel_list_apply R (list_take (iota_prefix_count mta) xs) (list_take (iota_prefix_count mta) ys)
    (projection_parallel_list_take R (iota_prefix_count mta) xs ys args) rhs rhs (@projection_parallel.refl R rhs)))",
    ),
    DeclarationInput::Proof(
        "cd_projection_iota_root",
        r"forall (R : RedEnv) (e e2 out : KExpr)
 (step : projection_parallel R e e2) (run : iota_step (red_rec R) e out), CDProjectionPeak R out e2",
        r"fun (R : RedEnv) (e e2 out : KExpr)
 (step : projection_parallel R e e2) (run : iota_step (red_rec R) e out) => iota_reduct_full_inv_type (red_rec R) e out (CDProjectionPeak R out e2) run
  (fun (recname : Name) (mta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule)
   (h1 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname))
   (h2 : @Eq (OptionType RecMeta) (recmeta_for (red_rec R) recname) (@OptionType.some RecMeta mta))
   (h3 : @Eq (OptionType KExpr) (list_head (list_drop (iota_major_index mta) (kapp_args e))) (@OptionType.some KExpr major))
   (h4 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (@OptionType.some Name cname))
   (h5 : @Eq (OptionType RecRule) (recrule_for (red_rec R) recname cname) (@OptionType.some RecRule rule))
   (fields : @Eq Bool (iota_fields_ok rule (kapp_args major)) Bool.true)
   (arity : @Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len (kexpr_const_levels (kapp_fn e)))) Bool.true)
   (returned : @Eq KExpr out (iota_contractum mta rule (kapp_args e) (kapp_args major)
    (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))))) =>
   @ProjectionConstSpineView.rec R e e2 (fun (_ : ProjectionConstSpineView R e e2) => CDProjectionPeak R out e2)
    (fun (whole : @Eq KExpr (kapp_fn e2) (kapp_fn e))
     (args : projection_parallel_list R (kapp_args e) (kapp_args e2)) =>
     projection_parallel_list_head_some R
      (list_drop (iota_major_index mta) (kapp_args e)) (list_drop (iota_major_index mta) (kapp_args e2))
      (projection_parallel_list_drop R (iota_major_index mta) (kapp_args e) (kapp_args e2) args)
      major (CDProjectionPeak R out e2) h3
      (fun (major2 : KExpr)
       (selected : @Eq (OptionType KExpr) (list_head (list_drop (iota_major_index mta) (kapp_args e2))) (@OptionType.some KExpr major2))
       (majorStep : projection_parallel R major major2) =>
       @ProjectionConstSpineView.rec R major major2
        (fun (_ : ProjectionConstSpineView R major major2) => CDProjectionPeak R out e2)
        (fun (majorWhole : @Eq KExpr (kapp_fn major2) (kapp_fn major))
         (majorArgs : projection_parallel_list R (kapp_args major) (kapp_args major2)) =>
         @CDProjectionPeak.mk R out e2
          (iota_contractum mta rule (kapp_args e2) (kapp_args major2)
           (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))))
          (Eq.substType KExpr
           (fun (v : KExpr) => projection_parallel_star R v
            (iota_contractum mta rule (kapp_args e2) (kapp_args major2)
             (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e)))))
           (iota_contractum mta rule (kapp_args e) (kapp_args major)
            (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e)))) out
           (Eq.symm KExpr out (iota_contractum mta rule (kapp_args e) (kapp_args major)
            (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e)))) returned)
           (projection_parallel_to_star R
            (iota_contractum mta rule (kapp_args e) (kapp_args major)
             (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))))
            (iota_contractum mta rule (kapp_args e2) (kapp_args major2)
             (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))))
            (projection_parallel_iota_contractum R mta rule (kapp_args e) (kapp_args e2) (kapp_args major) (kapp_args major2)
             (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))) args majorArgs)))
          (@par_reduces_cd.iota R e2
           (iota_contractum mta rule (kapp_args e2) (kapp_args major2)
            (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))))
           (iota_reduct_full_recon (red_rec R) e2
            (iota_contractum mta rule (kapp_args e2) (kapp_args major2)
             (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))))
            recname mta major2 cname rule
            (Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn e2)) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname)
             (Eq.cong KExpr (OptionType Name) kexpr_const_name (kapp_fn e2) (kapp_fn e) whole) h1)
            h2 selected
            (Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn major2)) (kexpr_const_name (kapp_fn major)) (@OptionType.some Name cname)
             (Eq.cong KExpr (OptionType Name) kexpr_const_name (kapp_fn major2) (kapp_fn major) majorWhole) h4)
            h5
            (Eq.trans Bool (iota_fields_ok rule (kapp_args major2)) (iota_fields_ok rule (kapp_args major)) Bool.true
             (Eq.symm Bool (iota_fields_ok rule (kapp_args major)) (iota_fields_ok rule (kapp_args major2))
              (projection_parallel_iota_fields_ok R rule (kapp_args major) (kapp_args major2) majorArgs)) fields)
            (Eq.trans Bool
             (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len (kexpr_const_levels (kapp_fn e2))))
             (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len (kexpr_const_levels (kapp_fn e)))) Bool.true
             (Eq.cong KExpr Bool (fun (hd : KExpr) => nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len (kexpr_const_levels hd)))
              (kapp_fn e2) (kapp_fn e) whole) arity)
            (Eq.symm KExpr
             (iota_contractum mta rule (kapp_args e2) (kapp_args major2)
              (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e2))))
             (iota_contractum mta rule (kapp_args e2) (kapp_args major2)
              (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))))
             (Eq.cong KExpr KExpr
              (fun (hd : KExpr) => iota_contractum mta rule (kapp_args e2) (kapp_args major2)
               (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels hd)))
              (kapp_fn e2) (kapp_fn e) whole)))))
        (projection_parallel_const_spine R cname major major2 majorStep h4)))
    (projection_parallel_const_spine R recname e e2 step h1))",
    ),
    DeclarationInput::Data(
        "imix_ctor_name",
        r"Name",
        r"Name.str Name.anonymous Nat.zero",
    ),
    DeclarationInput::Data(
        "imix_rule",
        r"RecRule",
        r"RecRule.mk imix_ctor_name (Nat.succ Nat.zero) (recrule_rhs iota_tail_fixture_rule)",
    ),
    DeclarationInput::Data(
        "imix_rec_env",
        r"RecEnv",
        r"RecEnv.addRec RecEnv.empty Name.anonymous iota_tail_fixture_meta (RecRules.cons imix_rule RecRules.nil)",
    ),
    DeclarationInput::Data(
        "imix_env",
        r"RedEnv",
        r"RedEnv.mk imix_rec_env DefEnv.empty (red_ind_ctor the_red_env)",
    ),
    DeclarationInput::Data(
        "imix_us",
        r"ListType Level",
        r"(@ListType.cons Level iota_tail_fixture_level (@ListType.nil Level))",
    ),
    DeclarationInput::Data(
        "imix_rhs",
        r"KExpr",
        r"KExpr.lam (KExpr.sort iota_tail_fixture_level) (KExpr.bvar Nat.zero)",
    ),
    DeclarationInput::Data(
        "imix_major",
        r"forall (parameter field : KExpr), KExpr",
        r"fun (parameter field : KExpr) => (KExpr.app (KExpr.app (KExpr.const imix_ctor_name (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level))) parameter) field)",
    ),
    DeclarationInput::Data(
        "imix_source",
        r"forall (us : ListType Level) (preArg parameter field extra : KExpr), KExpr",
        r"fun (us : ListType Level) (preArg parameter field extra : KExpr) => (KExpr.app (KExpr.app (KExpr.app (KExpr.const Name.anonymous us) preArg) (imix_major parameter field)) extra)",
    ),
    DeclarationInput::Data(
        "imix_before",
        r"KExpr",
        r"(imix_source imix_us cdp_prod_inner_projection cdp_prod_inner_projection cdp_prod_inner_projection cdp_prod_inner_projection)",
    ),
    DeclarationInput::Data(
        "imix_after",
        r"KExpr",
        r"(imix_source imix_us rfnz_zero rfnz_zero rfnz_zero rfnz_zero)",
    ),
    DeclarationInput::Data(
        "imix_retained",
        r"KExpr",
        r"(imix_source imix_us cdp_prod_inner_projection cdp_prod_inner_projection rfnz_zero cdp_prod_inner_projection)",
    ),
    DeclarationInput::Data(
        "imix_discarded",
        r"KExpr",
        r"(imix_source imix_us cdp_prod_inner_projection rfnz_zero cdp_prod_inner_projection cdp_prod_inner_projection)",
    ),
    DeclarationInput::Data(
        "imix_result_before",
        r"KExpr",
        r"(KExpr.app (KExpr.app (KExpr.app imix_rhs cdp_prod_inner_projection) cdp_prod_inner_projection) cdp_prod_inner_projection)",
    ),
    DeclarationInput::Data(
        "imix_result_after",
        r"KExpr",
        r"(KExpr.app (KExpr.app (KExpr.app imix_rhs rfnz_zero) rfnz_zero) rfnz_zero)",
    ),
    DeclarationInput::Data(
        "imix_result_retained",
        r"KExpr",
        r"(KExpr.app (KExpr.app (KExpr.app imix_rhs cdp_prod_inner_projection) rfnz_zero) cdp_prod_inner_projection)",
    ),
    DeclarationInput::Proof(
        "imix_inner_run",
        r"@Eq (OptionType KExpr) (projection_post_whnf_reduct imix_env cdp_prod_inner_projection) (@OptionType.some KExpr rfnz_zero)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr rfnz_zero)",
    ),
    DeclarationInput::Proof(
        "imix_inner_step",
        r"projection_parallel imix_env cdp_prod_inner_projection rfnz_zero",
        r"@projection_parallel.projection_beta imix_env kcre_prod_type_name Nat.zero kcre_witness_prod_value rfnz_zero imix_inner_run",
    ),
    DeclarationInput::Proof(
        "imix_source_projection",
        r"forall (p0 p1 q0 q1 f0 f1 x0 x1 : KExpr)
 (hp : projection_parallel imix_env p0 p1) (hq : projection_parallel imix_env q0 q1)
 (hf : projection_parallel imix_env f0 f1) (hx : projection_parallel imix_env x0 x1), projection_parallel imix_env (imix_source imix_us p0 q0 f0 x0) (imix_source imix_us p1 q1 f1 x1)",
        r"fun (p0 p1 q0 q1 f0 f1 x0 x1 : KExpr)
 (hp : projection_parallel imix_env p0 p1) (hq : projection_parallel imix_env q0 q1)
 (hf : projection_parallel imix_env f0 f1) (hx : projection_parallel imix_env x0 x1) => (@projection_parallel.app imix_env (KExpr.app (KExpr.app (KExpr.const Name.anonymous imix_us) p0) (imix_major q0 f0)) (KExpr.app (KExpr.app (KExpr.const Name.anonymous imix_us) p1) (imix_major q1 f1)) x0 x1 (@projection_parallel.app imix_env (KExpr.app (KExpr.const Name.anonymous imix_us) p0) (KExpr.app (KExpr.const Name.anonymous imix_us) p1) (imix_major q0 f0) (imix_major q1 f1) (@projection_parallel.app imix_env (KExpr.const Name.anonymous imix_us) (KExpr.const Name.anonymous imix_us) p0 p1 (@projection_parallel.refl imix_env (KExpr.const Name.anonymous imix_us)) hp) (@projection_parallel.app imix_env (KExpr.app (KExpr.const imix_ctor_name (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level))) q0) (KExpr.app (KExpr.const imix_ctor_name (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level))) q1) f0 f1 (@projection_parallel.app imix_env (KExpr.const imix_ctor_name (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level))) (KExpr.const imix_ctor_name (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level))) q0 q1 (@projection_parallel.refl imix_env (KExpr.const imix_ctor_name (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level)))) hq) hf)) hx)",
    ),
    DeclarationInput::Proof(
        "imix_project_after",
        r"projection_parallel imix_env imix_before imix_after",
        r"imix_source_projection cdp_prod_inner_projection rfnz_zero cdp_prod_inner_projection rfnz_zero cdp_prod_inner_projection rfnz_zero cdp_prod_inner_projection rfnz_zero imix_inner_step imix_inner_step imix_inner_step imix_inner_step",
    ),
    DeclarationInput::Proof(
        "imix_project_retained",
        r"projection_parallel imix_env imix_before imix_retained",
        r"imix_source_projection cdp_prod_inner_projection cdp_prod_inner_projection cdp_prod_inner_projection cdp_prod_inner_projection cdp_prod_inner_projection rfnz_zero cdp_prod_inner_projection cdp_prod_inner_projection (@projection_parallel.refl imix_env cdp_prod_inner_projection) (@projection_parallel.refl imix_env cdp_prod_inner_projection) imix_inner_step (@projection_parallel.refl imix_env cdp_prod_inner_projection)",
    ),
    DeclarationInput::Proof(
        "imix_project_discarded",
        r"projection_parallel imix_env imix_before imix_discarded",
        r"imix_source_projection cdp_prod_inner_projection cdp_prod_inner_projection cdp_prod_inner_projection rfnz_zero cdp_prod_inner_projection cdp_prod_inner_projection cdp_prod_inner_projection cdp_prod_inner_projection (@projection_parallel.refl imix_env cdp_prod_inner_projection) imix_inner_step (@projection_parallel.refl imix_env cdp_prod_inner_projection) (@projection_parallel.refl imix_env cdp_prod_inner_projection)",
    ),
    DeclarationInput::Proof(
        "imix_run_before",
        r"@Eq (OptionType KExpr) (iota_reduct (red_rec imix_env) imix_before) (@OptionType.some KExpr imix_result_before)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr imix_result_before)",
    ),
    DeclarationInput::Proof(
        "imix_run_after",
        r"@Eq (OptionType KExpr) (iota_reduct (red_rec imix_env) imix_after) (@OptionType.some KExpr imix_result_after)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr imix_result_after)",
    ),
    DeclarationInput::Proof(
        "imix_run_retained",
        r"@Eq (OptionType KExpr) (iota_reduct (red_rec imix_env) imix_retained) (@OptionType.some KExpr imix_result_retained)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr imix_result_retained)",
    ),
    DeclarationInput::Proof(
        "imix_run_discarded",
        r"@Eq (OptionType KExpr) (iota_reduct (red_rec imix_env) imix_discarded) (@OptionType.some KExpr imix_result_before)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr imix_result_before)",
    ),
    DeclarationInput::Proof(
        "imix_old_iota_left",
        r"par_reduces_cd imix_env imix_before imix_result_before",
        r"@par_reduces_cd.iota imix_env imix_before imix_result_before imix_run_before",
    ),
    DeclarationInput::Proof(
        "imix_peak_after",
        r"CDProjectionPeak imix_env imix_result_before imix_after",
        r"cd_projection_iota_root imix_env imix_before imix_after imix_result_before imix_project_after imix_run_before",
    ),
    DeclarationInput::Proof(
        "imix_peak_retained",
        r"CDProjectionPeak imix_env imix_result_before imix_retained",
        r"cd_projection_iota_root imix_env imix_before imix_retained imix_result_before imix_project_retained imix_run_before",
    ),
    DeclarationInput::Proof(
        "imix_peak_discarded",
        r"CDProjectionPeak imix_env imix_result_before imix_discarded",
        r"cd_projection_iota_root imix_env imix_before imix_discarded imix_result_before imix_project_discarded imix_run_before",
    ),
    DeclarationInput::Proof(
        "imix_result_projection",
        r"projection_parallel imix_env imix_result_before imix_result_after",
        r"(@projection_parallel.app imix_env (KExpr.app (KExpr.app imix_rhs cdp_prod_inner_projection) cdp_prod_inner_projection) (KExpr.app (KExpr.app imix_rhs rfnz_zero) rfnz_zero) cdp_prod_inner_projection rfnz_zero (@projection_parallel.app imix_env (KExpr.app imix_rhs cdp_prod_inner_projection) (KExpr.app imix_rhs rfnz_zero) cdp_prod_inner_projection rfnz_zero (@projection_parallel.app imix_env imix_rhs imix_rhs cdp_prod_inner_projection rfnz_zero (@projection_parallel.refl imix_env imix_rhs) imix_inner_step) imix_inner_step) imix_inner_step)",
    ),
    DeclarationInput::Proof(
        "imix_explicit_after_meet",
        r"CDProjectionPeak imix_env imix_result_before imix_after",
        r"@CDProjectionPeak.mk imix_env imix_result_before imix_after imix_result_after (projection_parallel_to_star imix_env imix_result_before imix_result_after imix_result_projection) (@par_reduces_cd.iota imix_env imix_after imix_result_after imix_run_after)",
    ),
    DeclarationInput::Proof(
        "imix_discarded_explicit_meet",
        r"CDProjectionPeak imix_env imix_result_before imix_discarded",
        r"@CDProjectionPeak.mk imix_env imix_result_before imix_discarded imix_result_before (@projection_parallel_star.refl imix_env imix_result_before) (@par_reduces_cd.iota imix_env imix_discarded imix_result_before imix_run_discarded)",
    ),
    DeclarationInput::Proof(
        "imix_rhs_once",
        r"@Eq KExpr (recursor_rhs_instance (recmeta_signature iota_tail_fixture_meta) (recrule_rhs imix_rule) imix_us) imix_rhs",
        r"@Eq.refl KExpr imix_rhs",
    ),
    DeclarationInput::Proof(
        "imix_head_nonzero",
        r"@Eq (ListType Level) (kexpr_const_levels (kapp_fn imix_before)) imix_us",
        r"@Eq.refl (ListType Level) imix_us",
    ),
    DeclarationInput::Proof(
        "imix_fields_guard",
        r"@Eq Bool (iota_fields_ok imix_rule (kapp_args (imix_major cdp_prod_inner_projection cdp_prod_inner_projection))) Bool.true",
        r"@Eq.refl Bool Bool.true",
    ),
    DeclarationInput::Proof(
        "imix_arity_guard",
        r"@Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature iota_tail_fixture_meta))) (level_list_len (kexpr_const_levels (kapp_fn imix_before)))) Bool.true",
        r"@Eq.refl Bool Bool.true",
    ),
    DeclarationInput::Proof(
        "imix_refuses_missing_universe",
        r"@Eq (OptionType KExpr) (iota_reduct (red_rec imix_env) (imix_source (@ListType.nil Level) cdp_prod_inner_projection cdp_prod_inner_projection cdp_prod_inner_projection cdp_prod_inner_projection)) (@OptionType.none KExpr)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
    ),
    DeclarationInput::Proof(
        "imix_refuses_extra_universe",
        r"@Eq (OptionType KExpr) (iota_reduct (red_rec imix_env) (imix_source (@ListType.cons Level iota_tail_fixture_level (@ListType.cons Level Level.zero (@ListType.nil Level))) cdp_prod_inner_projection cdp_prod_inner_projection cdp_prod_inner_projection cdp_prod_inner_projection)) (@OptionType.none KExpr)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
    ),
    DeclarationInput::Data(
        "imix_short_source",
        r"KExpr",
        r"(KExpr.app (KExpr.app (KExpr.app (KExpr.const Name.anonymous imix_us) cdp_prod_inner_projection) (KExpr.const imix_ctor_name (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level)))) cdp_prod_inner_projection)",
    ),
    DeclarationInput::Proof(
        "imix_refuses_short_fields",
        r"@Eq (OptionType KExpr) (iota_reduct (red_rec imix_env) imix_short_source) (@OptionType.none KExpr)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
    ),
    DeclarationInput::Proof(
        "imix_short_guard_false",
        r"@Eq Bool (iota_fields_ok imix_rule (@ListType.nil KExpr)) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Data(
        "imix_nat_rule",
        r"RecRule",
        r"@OptionType.rec RecRule (fun (_ : OptionType RecRule) => RecRule)
  (RecRule.mk fixture_nat_succ_name Nat.zero (KExpr.sort Level.zero))
  (fun (r : RecRule) => r)
  (recrule_for (red_rec the_red_env) fixture_nat_rec_name fixture_nat_succ_name)",
    ),
    DeclarationInput::Proof(
        "imix_nat_rule_lookup",
        r"@Eq (OptionType RecRule)
 (recrule_for (red_rec the_red_env) fixture_nat_rec_name fixture_nat_succ_name)
 (@OptionType.some RecRule imix_nat_rule)",
        r"@Eq.refl (OptionType RecRule) (@OptionType.some RecRule imix_nat_rule)",
    ),
    DeclarationInput::Proof(
        "imix_nat_rule_fields",
        r"@Eq Nat (recrule_num_fields imix_nat_rule) (Nat.succ Nat.zero)",
        r"@Eq.refl Nat (Nat.succ Nat.zero)",
    ),
    DeclarationInput::Data(
        "imix_nat_us",
        r"ListType Level",
        r"@ListType.cons Level (Level.succ (Level.param rfnz_parameter)) (@ListType.nil Level)",
    ),
    DeclarationInput::Data(
        "imix_nat_rhs",
        r"KExpr",
        r"recursor_rhs_instance (recmeta_signature fixture_nat_rec_meta) (recrule_rhs imix_nat_rule) imix_nat_us",
    ),
    DeclarationInput::Data(
        "imix_nat_prefix",
        r"KExpr",
        r"KExpr.app (KExpr.app (KExpr.app (KExpr.const fixture_nat_rec_name imix_nat_us) rfnz_motive) rfnz_zero) rfnz_minor",
    ),
    DeclarationInput::Data(
        "imix_nat_result_prefix",
        r"KExpr",
        r"KExpr.app (KExpr.app (KExpr.app imix_nat_rhs rfnz_motive) rfnz_zero) rfnz_minor",
    ),
    DeclarationInput::Data(
        "imix_nat_before",
        r"KExpr",
        r"KExpr.app (KExpr.app imix_nat_prefix (KExpr.app rfnz_succ cdp_prod_inner_projection)) cdp_prod_inner_projection",
    ),
    DeclarationInput::Data(
        "imix_nat_after",
        r"KExpr",
        r"KExpr.app (KExpr.app imix_nat_prefix (KExpr.app rfnz_succ rfnz_zero)) rfnz_zero",
    ),
    DeclarationInput::Data(
        "imix_nat_result_before",
        r"KExpr",
        r"KExpr.app (KExpr.app imix_nat_result_prefix cdp_prod_inner_projection) cdp_prod_inner_projection",
    ),
    DeclarationInput::Data(
        "imix_nat_result_after",
        r"KExpr",
        r"KExpr.app (KExpr.app imix_nat_result_prefix rfnz_zero) rfnz_zero",
    ),
    DeclarationInput::Proof(
        "imix_nat_run_before",
        r"iota_step (red_rec the_red_env) imix_nat_before imix_nat_result_before",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr imix_nat_result_before)",
    ),
    DeclarationInput::Proof(
        "imix_nat_run_after",
        r"iota_step (red_rec the_red_env) imix_nat_after imix_nat_result_after",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr imix_nat_result_after)",
    ),
    DeclarationInput::Proof(
        "imix_nat_projection",
        r"projection_parallel the_red_env imix_nat_before imix_nat_after",
        r"@projection_parallel.app the_red_env
  (KExpr.app imix_nat_prefix (KExpr.app rfnz_succ cdp_prod_inner_projection)) (KExpr.app imix_nat_prefix (KExpr.app rfnz_succ rfnz_zero))
  cdp_prod_inner_projection rfnz_zero
  (@projection_parallel.app the_red_env imix_nat_prefix imix_nat_prefix
   (KExpr.app rfnz_succ cdp_prod_inner_projection) (KExpr.app rfnz_succ rfnz_zero)
   (@projection_parallel.refl the_red_env imix_nat_prefix)
   (@projection_parallel.app the_red_env rfnz_succ rfnz_succ cdp_prod_inner_projection rfnz_zero
    (@projection_parallel.refl the_red_env rfnz_succ) projection_parallel_inner_step)) projection_parallel_inner_step",
    ),
    DeclarationInput::Proof(
        "imix_nat_peak",
        r"CDProjectionPeak the_red_env imix_nat_result_before imix_nat_after",
        r"cd_projection_iota_root the_red_env imix_nat_before imix_nat_after imix_nat_result_before imix_nat_projection imix_nat_run_before",
    ),
    DeclarationInput::Proof(
        "imix_nat_old_iota",
        r"par_reduces_cd the_red_env imix_nat_before imix_nat_result_before",
        r"@par_reduces_cd.iota the_red_env imix_nat_before imix_nat_result_before imix_nat_run_before",
    ),
    DeclarationInput::Proof(
        "imix_nat_residual",
        r"projection_parallel the_red_env imix_nat_result_before imix_nat_result_after",
        r"@projection_parallel.app the_red_env
  (KExpr.app imix_nat_result_prefix cdp_prod_inner_projection) (KExpr.app imix_nat_result_prefix rfnz_zero)
  cdp_prod_inner_projection rfnz_zero
  (@projection_parallel.app the_red_env imix_nat_result_prefix imix_nat_result_prefix cdp_prod_inner_projection rfnz_zero
   (@projection_parallel.refl the_red_env imix_nat_result_prefix) projection_parallel_inner_step) projection_parallel_inner_step",
    ),
    DeclarationInput::Proof(
        "imix_nat_explicit_meet",
        r"CDProjectionPeak the_red_env imix_nat_result_before imix_nat_after",
        r"@CDProjectionPeak.mk the_red_env imix_nat_result_before imix_nat_after imix_nat_result_after
  (projection_parallel_to_star the_red_env imix_nat_result_before imix_nat_result_after imix_nat_residual)
  (@par_reduces_cd.iota the_red_env imix_nat_after imix_nat_result_after imix_nat_run_after)",
    ),
];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "imix_negative_missing_arity",
        r"iota_step (red_rec imix_env)
 (imix_source (@ListType.nil Level) cdp_prod_inner_projection cdp_prod_inner_projection cdp_prod_inner_projection cdp_prod_inner_projection)
 imix_result_before",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr imix_result_before)",
    ),
    (
        "imix_negative_short_fields",
        r"iota_step (red_rec imix_env) imix_short_source imix_result_before",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr imix_result_before)",
    ),
    (
        "imix_negative_double_instantiation",
        r"iota_step (red_rec imix_env) imix_before
 (KExpr.app (KExpr.app (KExpr.app
  (recursor_rhs_instance (recmeta_signature iota_tail_fixture_meta)
   (recursor_rhs_instance (recmeta_signature iota_tail_fixture_meta) (recrule_rhs imix_rule) imix_us) imix_us)
  cdp_prod_inner_projection) cdp_prod_inner_projection) cdp_prod_inner_projection)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr imix_result_before)",
    ),
    (
        "imix_negative_discarded_not_retained",
        r"iota_step (red_rec imix_env) imix_discarded imix_result_retained",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr imix_result_retained)",
    ),
    (
        "imix_negative_omit_extra",
        r"iota_step (red_rec imix_env) imix_before
 (KExpr.app (KExpr.app imix_rhs cdp_prod_inner_projection) cdp_prod_inner_projection)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.app (KExpr.app imix_rhs cdp_prod_inner_projection) cdp_prod_inner_projection))",
    ),
    (
        "imix_negative_change_head_universes",
        r"projection_parallel imix_env imix_before
 (imix_source (@ListType.nil Level) rfnz_zero rfnz_zero rfnz_zero rfnz_zero)",
        r"imix_project_after",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "projection_parallel_list_take",
    "projection_parallel_iota_fields_ok",
    "projection_parallel_iota_contractum",
    "cd_projection_iota_root",
    "imix_inner_run",
    "imix_inner_step",
    "imix_source_projection",
    "imix_project_after",
    "imix_project_retained",
    "imix_project_discarded",
    "imix_run_before",
    "imix_run_after",
    "imix_run_retained",
    "imix_run_discarded",
    "imix_old_iota_left",
    "imix_peak_after",
    "imix_peak_retained",
    "imix_peak_discarded",
    "imix_result_projection",
    "imix_explicit_after_meet",
    "imix_discarded_explicit_meet",
    "imix_rhs_once",
    "imix_head_nonzero",
    "imix_fields_guard",
    "imix_arity_guard",
    "imix_refuses_missing_universe",
    "imix_refuses_extra_universe",
    "imix_refuses_short_fields",
    "imix_short_guard_false",
    "imix_nat_rule_lookup",
    "imix_nat_rule_fields",
    "imix_nat_run_before",
    "imix_nat_run_after",
    "imix_nat_projection",
    "imix_nat_peak",
    "imix_nat_old_iota",
    "imix_nat_residual",
    "imix_nat_explicit_meet",
];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[
    "imix_ctor_name",
    "imix_rule",
    "imix_rec_env",
    "imix_env",
    "imix_us",
    "imix_rhs",
    "imix_major",
    "imix_source",
    "imix_before",
    "imix_after",
    "imix_retained",
    "imix_discarded",
    "imix_result_before",
    "imix_result_after",
    "imix_result_retained",
    "imix_short_source",
    "imix_nat_rule",
    "imix_nat_us",
    "imix_nat_rhs",
    "imix_nat_prefix",
    "imix_nat_result_prefix",
    "imix_nat_before",
    "imix_nat_after",
    "imix_nat_result_before",
    "imix_nat_result_after",
];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &[];
