// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Canonical success views for the direct guarded-tail migration of iota_reduct.
//!
//! Unregistered until the existing operator's final rule continuation is changed
//! to iota_contractum_at and its old inverter registrations are removed.
//! These proofs do not add a second operator or assume an output reduct/typing.
//! Type views reuse the existing opt_bind_some_inv_type; move its unchanged
//! definition and option_none_ne_some_type early instead of duplicating them.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const PROOFS: &[(&str, &str)] = &[
    (r"def iota_reduct_full_inv (env : RecEnv) (e : KExpr) (result : KExpr) (C : Prop)
 (h : Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr result))
 (k : forall (recname : Name) (mta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule),
 Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname) ->
 Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta mta) ->
 Eq (OptionType KExpr) (list_head (list_drop (iota_major_index mta) (kapp_args e))) (OptionType.some KExpr major) ->
 Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) ->
 Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) ->
 Eq Bool (iota_fields_ok rule (kapp_args major)) Bool.true -> Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len (kexpr_const_levels (kapp_fn e)))) Bool.true -> Eq KExpr result (iota_contractum mta rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e)))) -> C) : C :=
 opt_bind_some_inv Name KExpr (kexpr_const_name (kapp_fn e)) (fun (recname : Name) => (opt_bind RecMeta KExpr (recmeta_for env recname) (fun (mta : RecMeta) => (opt_bind KExpr KExpr (list_head (list_drop (iota_major_index mta) (kapp_args e))) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))))))))) result C h
 (fun (recname : Name) (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname))
  (h1r : Eq (OptionType KExpr) ((fun (recname : Name) => (opt_bind RecMeta KExpr (recmeta_for env recname) (fun (mta : RecMeta) => (opt_bind KExpr KExpr (list_head (list_drop (iota_major_index mta) (kapp_args e))) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))))))))) recname) (OptionType.some KExpr result)) =>
 opt_bind_some_inv RecMeta KExpr (recmeta_for env recname) (fun (mta : RecMeta) => (opt_bind KExpr KExpr (list_head (list_drop (iota_major_index mta) (kapp_args e))) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))))))) result C h1r
 (fun (mta : RecMeta) (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta mta))
  (h2r : Eq (OptionType KExpr) ((fun (mta : RecMeta) => (opt_bind KExpr KExpr (list_head (list_drop (iota_major_index mta) (kapp_args e))) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))))))) mta) (OptionType.some KExpr result)) =>
 opt_bind_some_inv KExpr KExpr (list_head (list_drop (iota_major_index mta) (kapp_args e))) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))))) result C h2r
 (fun (major : KExpr) (h3 : Eq (OptionType KExpr) (list_head (list_drop (iota_major_index mta) (kapp_args e))) (OptionType.some KExpr major))
  (h3r : Eq (OptionType KExpr) ((fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))))) major) (OptionType.some KExpr result)) =>
 opt_bind_some_inv Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))) result C h3r
 (fun (cname : Name) (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname))
  (h4r : Eq (OptionType KExpr) ((fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))) cname) (OptionType.some KExpr result)) =>
 opt_bind_some_inv RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))) result C h4r
 (fun (rule : RecRule) (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule))
  (h5r : Eq (OptionType KExpr) ((fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))) rule) (OptionType.some KExpr result)) =>
 iota_contractum_at_guard_inv mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major) result C h5r
  (fun (fields : Eq Bool (iota_fields_ok rule (kapp_args major)) Bool.true) (arity : Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len (kexpr_const_levels (kapp_fn e)))) Bool.true) (returned : Eq KExpr result (iota_contractum mta rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))))) =>
   k recname mta major cname rule h1 h2 h3 h4 h5 fields arity returned))))))", "Complete Prop-valued success view of the actual five-lookup iota chain and guarded tail: retain both guards and the computed once-instantiated result."),
    (r"def iota_reduct_full_inv_type (env : RecEnv) (e : KExpr) (result : KExpr) (C : Type)
 (h : Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr result))
 (k : forall (recname : Name) (mta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule),
 Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname) ->
 Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta mta) ->
 Eq (OptionType KExpr) (list_head (list_drop (iota_major_index mta) (kapp_args e))) (OptionType.some KExpr major) ->
 Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) ->
 Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) ->
 Eq Bool (iota_fields_ok rule (kapp_args major)) Bool.true -> Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len (kexpr_const_levels (kapp_fn e)))) Bool.true -> Eq KExpr result (iota_contractum mta rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e)))) -> C) : C :=
 opt_bind_some_inv_type Name KExpr (kexpr_const_name (kapp_fn e)) (fun (recname : Name) => (opt_bind RecMeta KExpr (recmeta_for env recname) (fun (mta : RecMeta) => (opt_bind KExpr KExpr (list_head (list_drop (iota_major_index mta) (kapp_args e))) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))))))))) result C h
 (fun (recname : Name) (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname))
  (h1r : Eq (OptionType KExpr) ((fun (recname : Name) => (opt_bind RecMeta KExpr (recmeta_for env recname) (fun (mta : RecMeta) => (opt_bind KExpr KExpr (list_head (list_drop (iota_major_index mta) (kapp_args e))) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))))))))) recname) (OptionType.some KExpr result)) =>
 opt_bind_some_inv_type RecMeta KExpr (recmeta_for env recname) (fun (mta : RecMeta) => (opt_bind KExpr KExpr (list_head (list_drop (iota_major_index mta) (kapp_args e))) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))))))) result C h1r
 (fun (mta : RecMeta) (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta mta))
  (h2r : Eq (OptionType KExpr) ((fun (mta : RecMeta) => (opt_bind KExpr KExpr (list_head (list_drop (iota_major_index mta) (kapp_args e))) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))))))) mta) (OptionType.some KExpr result)) =>
 opt_bind_some_inv_type KExpr KExpr (list_head (list_drop (iota_major_index mta) (kapp_args e))) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))))) result C h2r
 (fun (major : KExpr) (h3 : Eq (OptionType KExpr) (list_head (list_drop (iota_major_index mta) (kapp_args e))) (OptionType.some KExpr major))
  (h3r : Eq (OptionType KExpr) ((fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))))) major) (OptionType.some KExpr result)) =>
 opt_bind_some_inv_type Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))) result C h3r
 (fun (cname : Name) (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname))
  (h4r : Eq (OptionType KExpr) ((fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))) cname) (OptionType.some KExpr result)) =>
 opt_bind_some_inv_type RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))) result C h4r
 (fun (rule : RecRule) (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule))
  (h5r : Eq (OptionType KExpr) ((fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))) rule) (OptionType.some KExpr result)) =>
 iota_contractum_at_guard_inv_type mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major) result C h5r
  (fun (fields : Eq Bool (iota_fields_ok rule (kapp_args major)) Bool.true) (arity : Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len (kexpr_const_levels (kapp_fn e)))) Bool.true) (returned : Eq KExpr result (iota_contractum mta rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))))) =>
   k recname mta major cname rule h1 h2 h3 h4 h5 fields arity returned))))))", "Complete Type-valued success view of the actual five-lookup iota chain and guarded tail: retain both guards and the computed once-instantiated result."),
    (r"def iota_reduct_full_recon (env : RecEnv) (e : KExpr) (result : KExpr)
 (recname : Name) (mta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule)
 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname))
 (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta mta))
 (h3 : Eq (OptionType KExpr) (list_head (list_drop (iota_major_index mta) (kapp_args e))) (OptionType.some KExpr major))
 (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname))
 (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule))
 (fields : Eq Bool (iota_fields_ok rule (kapp_args major)) Bool.true) (arity : Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len (kexpr_const_levels (kapp_fn e)))) Bool.true) (returned : Eq KExpr result (iota_contractum mta rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))))) :
 Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr result) :=
 Eq.trans (OptionType KExpr) (opt_bind Name KExpr (kexpr_const_name (kapp_fn e)) (fun (recname : Name) => (opt_bind RecMeta KExpr (recmeta_for env recname) (fun (mta : RecMeta) => (opt_bind KExpr KExpr (list_head (list_drop (iota_major_index mta) (kapp_args e))) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major)))))))))))) (opt_bind Name KExpr (OptionType.some Name recname) (fun (recname : Name) => (opt_bind RecMeta KExpr (recmeta_for env recname) (fun (mta : RecMeta) => (opt_bind KExpr KExpr (list_head (list_drop (iota_major_index mta) (kapp_args e))) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major)))))))))))) (OptionType.some KExpr result)
 (Eq.cong (OptionType Name) (OptionType KExpr)
  (fun (o : OptionType Name) => opt_bind Name KExpr o (fun (recname : Name) => (opt_bind RecMeta KExpr (recmeta_for env recname) (fun (mta : RecMeta) => (opt_bind KExpr KExpr (list_head (list_drop (iota_major_index mta) (kapp_args e))) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))))))))))
  (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname) h1)
 (Eq.trans (OptionType KExpr) (opt_bind RecMeta KExpr (recmeta_for env recname) (fun (mta : RecMeta) => (opt_bind KExpr KExpr (list_head (list_drop (iota_major_index mta) (kapp_args e))) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major)))))))))) (opt_bind RecMeta KExpr (OptionType.some RecMeta mta) (fun (mta : RecMeta) => (opt_bind KExpr KExpr (list_head (list_drop (iota_major_index mta) (kapp_args e))) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major)))))))))) (OptionType.some KExpr result)
 (Eq.cong (OptionType RecMeta) (OptionType KExpr)
  (fun (o : OptionType RecMeta) => opt_bind RecMeta KExpr o (fun (mta : RecMeta) => (opt_bind KExpr KExpr (list_head (list_drop (iota_major_index mta) (kapp_args e))) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))))))))
  (recmeta_for env recname) (OptionType.some RecMeta mta) h2)
 (Eq.trans (OptionType KExpr) (opt_bind KExpr KExpr (list_head (list_drop (iota_major_index mta) (kapp_args e))) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major)))))))) (opt_bind KExpr KExpr (OptionType.some KExpr major) (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major)))))))) (OptionType.some KExpr result)
 (Eq.cong (OptionType KExpr) (OptionType KExpr)
  (fun (o : OptionType KExpr) => opt_bind KExpr KExpr o (fun (major : KExpr) => (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))))))
  (list_head (list_drop (iota_major_index mta) (kapp_args e))) (OptionType.some KExpr major) h3)
 (Eq.trans (OptionType KExpr) (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major)))))) (opt_bind Name KExpr (OptionType.some Name cname) (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major)))))) (OptionType.some KExpr result)
 (Eq.cong (OptionType Name) (OptionType KExpr)
  (fun (o : OptionType Name) => opt_bind Name KExpr o (fun (cname : Name) => (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))))
  (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) h4)
 (Eq.trans (OptionType KExpr) (opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major)))) (opt_bind RecRule KExpr (OptionType.some RecRule rule) (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major)))) (OptionType.some KExpr result)
 (Eq.cong (OptionType RecRule) (OptionType KExpr)
  (fun (o : OptionType RecRule) => opt_bind RecRule KExpr o (fun (rule : RecRule) => (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))
  (recrule_for env recname cname) (OptionType.some RecRule rule) h5)
 (Eq.trans (OptionType KExpr) (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major)) (OptionType.some KExpr (iota_contractum mta rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))))) (OptionType.some KExpr result)
 (iota_contractum_at_intro mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major) fields arity)
 (Eq.cong KExpr (OptionType KExpr) (fun (x : KExpr) => OptionType.some KExpr x)
   (iota_contractum mta rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e)))) result (Eq.symm KExpr result (iota_contractum mta rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e)))) returned)))))))", "Reconstruct the actual successful reduction from exactly the five lookups, both Boolean guards and result equality. Direct equality transport reuses the actual tail intro; no assumed output step."),
    (r"def iota_reduct_some_inv (env : RecEnv) (e : KExpr) (result : KExpr) (C : Prop)
 (h : Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr result))
 (k : forall (recname : Name) (mta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule),
 Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname) ->
 Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta mta) ->
 Eq (OptionType KExpr) (list_head (list_drop (iota_major_index mta) (kapp_args e))) (OptionType.some KExpr major) ->
 Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) ->
 Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) ->
 Eq (OptionType KExpr) (OptionType.some KExpr (iota_contractum mta rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))))) (OptionType.some KExpr result) -> C) : C :=
 iota_reduct_full_inv env e result C h
 (fun (recname : Name) (mta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule)
  (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname))
 (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta mta))
 (h3 : Eq (OptionType KExpr) (list_head (list_drop (iota_major_index mta) (kapp_args e))) (OptionType.some KExpr major))
 (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname))
 (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule))
  (_fields : Eq Bool (iota_fields_ok rule (kapp_args major)) Bool.true) (_arity : Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len (kexpr_const_levels (kapp_fn e)))) Bool.true) (returned : Eq KExpr result (iota_contractum mta rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))))) =>
   k recname mta major cname rule h1 h2 h3 h4 h5
    (Eq.cong KExpr (OptionType KExpr) (fun (x : KExpr) => OptionType.some KExpr x)
      (iota_contractum mta rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e)))) result (Eq.symm KExpr result (iota_contractum mta rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e)))) returned)))", "Compatibility Prop view preserves old argument/witness/lookup order and final some-computed=some-result orientation, while its computed RHS now instantiates actual head universes. Guards are discarded only here."),
    (r"def iota_reduct_some_inv_type (env : RecEnv) (e : KExpr) (result : KExpr) (C : Type)
 (h : Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr result))
 (k : forall (recname : Name) (mta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule),
 Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname) ->
 Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta mta) ->
 Eq (OptionType KExpr) (list_head (list_drop (iota_major_index mta) (kapp_args e))) (OptionType.some KExpr major) ->
 Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) ->
 Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) ->
 Eq (OptionType KExpr) (OptionType.some KExpr (iota_contractum mta rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))))) (OptionType.some KExpr result) -> C) : C :=
 iota_reduct_full_inv_type env e result C h
 (fun (recname : Name) (mta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule)
  (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname))
 (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta mta))
 (h3 : Eq (OptionType KExpr) (list_head (list_drop (iota_major_index mta) (kapp_args e))) (OptionType.some KExpr major))
 (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname))
 (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule))
  (_fields : Eq Bool (iota_fields_ok rule (kapp_args major)) Bool.true) (_arity : Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len (kexpr_const_levels (kapp_fn e)))) Bool.true) (returned : Eq KExpr result (iota_contractum mta rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))))) =>
   k recname mta major cname rule h1 h2 h3 h4 h5
    (Eq.cong KExpr (OptionType KExpr) (fun (x : KExpr) => OptionType.some KExpr x)
      (iota_contractum mta rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e)))) result (Eq.symm KExpr result (iota_contractum mta rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e)))) returned)))", "Compatibility Type view preserves old argument/witness/lookup order and final some-computed=some-result orientation, while its computed RHS now instantiates actual head universes. Guards are discarded only here."),
    (r"def iota_reduct_full_roundtrip (env : RecEnv) (e : KExpr) (result : KExpr)
 (h : Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr result)) :
 Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr result) :=
 iota_reduct_full_inv env e result
  (Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr result)) h
  (fun (recname : Name) (mta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule)
   (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname))
 (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta mta))
 (h3 : Eq (OptionType KExpr) (list_head (list_drop (iota_major_index mta) (kapp_args e))) (OptionType.some KExpr major))
 (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname))
 (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule))
   (fields : Eq Bool (iota_fields_ok rule (kapp_args major)) Bool.true) (arity : Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len (kexpr_const_levels (kapp_fn e)))) Bool.true) (returned : Eq KExpr result (iota_contractum mta rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))))) =>
   iota_reduct_full_recon env e result recname mta major cname rule
    h1 h2 h3 h4 h5 fields arity returned)", "Actual inversion and reconstruction compose on the same success graph; the concrete nonzero caller below witnesses inhabitation."),
];

const CONTROLS: &[(&str, &str)] = &[
    (r"def iota_view_fixture_env : RecEnv :=
 RecEnv.addRec RecEnv.empty (Name.str Name.anonymous Nat.zero) iota_tail_fixture_meta
  (RecRules.cons iota_tail_fixture_rule RecRules.nil)", "Finite test environment for the actual operator: source-signature/RHS typing validity is not claimed."),
    (r"def iota_view_fixture_major : KExpr :=
 KExpr.app (KExpr.app (KExpr.const Name.anonymous (ListType.nil Level)) (KExpr.bvar Nat.zero))
  (KExpr.sort (Level.succ Level.zero))", "Constructor parameter plus one field; the actual rule selects only the final field."),
    (r"def iota_view_fixture_expr : KExpr :=
 KExpr.app
  (KExpr.app
    (KExpr.app (KExpr.const (Name.str Name.anonymous Nat.zero)
      (ListType.cons Level iota_tail_fixture_level (ListType.nil Level))) (KExpr.sort Level.zero))
    iota_view_fixture_major)
  (KExpr.sort (Level.succ (Level.succ Level.zero)))", "Actual const-headed redex with nonzero self-parameter universes, prefix, major and extra."),
    (r"def iota_view_fixture_success :
 Eq (OptionType KExpr) (iota_reduct iota_view_fixture_env iota_view_fixture_expr)
  (OptionType.some KExpr iota_tail_fixture_result) :=
 Eq.refl (OptionType KExpr) (OptionType.some KExpr iota_tail_fixture_result)", "The updated actual operator computes the independently spelled result through all five real lookups and both guards."),
    (r"def iota_view_fixture_roundtrip :
 Eq (OptionType KExpr) (iota_reduct iota_view_fixture_env iota_view_fixture_expr)
  (OptionType.some KExpr iota_tail_fixture_result) :=
 iota_reduct_full_roundtrip iota_view_fixture_env iota_view_fixture_expr
  iota_tail_fixture_result iota_view_fixture_success", "Concrete nonempty/nonzero caller of complete success inversion and reconstruction."),
    (r"def iota_view_fixture_compat : Eq Nat Nat.zero Nat.zero :=
 iota_reduct_some_inv iota_view_fixture_env iota_view_fixture_expr
  iota_tail_fixture_result (Eq Nat Nat.zero Nat.zero) iota_view_fixture_success
  (fun (recname : Name) (mta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule)
   (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn iota_view_fixture_expr)) (OptionType.some Name recname))
 (h2 : Eq (OptionType RecMeta) (recmeta_for iota_view_fixture_env recname) (OptionType.some RecMeta mta))
 (h3 : Eq (OptionType KExpr) (list_head (list_drop (iota_major_index mta) (kapp_args iota_view_fixture_expr))) (OptionType.some KExpr major))
 (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname))
 (h5 : Eq (OptionType RecRule) (recrule_for iota_view_fixture_env recname cname) (OptionType.some RecRule rule))
   (_returned : Eq (OptionType KExpr)
     (OptionType.some KExpr (iota_contractum mta rule (kapp_args iota_view_fixture_expr) (kapp_args major) (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn iota_view_fixture_expr)))))
     (OptionType.some KExpr iota_tail_fixture_result)) => Eq.refl Nat Nat.zero)", "The actual Prop-valued compatibility view has a concrete success caller, not only a universal implication."),
    (r"def iota_view_fixture_compat_type : Nat :=
 iota_reduct_some_inv_type iota_view_fixture_env iota_view_fixture_expr
  iota_tail_fixture_result (Nat) iota_view_fixture_success
  (fun (recname : Name) (mta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule)
   (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn iota_view_fixture_expr)) (OptionType.some Name recname))
 (h2 : Eq (OptionType RecMeta) (recmeta_for iota_view_fixture_env recname) (OptionType.some RecMeta mta))
 (h3 : Eq (OptionType KExpr) (list_head (list_drop (iota_major_index mta) (kapp_args iota_view_fixture_expr))) (OptionType.some KExpr major))
 (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname))
 (h5 : Eq (OptionType RecRule) (recrule_for iota_view_fixture_env recname cname) (OptionType.some RecRule rule))
   (_returned : Eq (OptionType KExpr)
     (OptionType.some KExpr (iota_contractum mta rule (kapp_args iota_view_fixture_expr) (kapp_args major) (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) (kexpr_const_levels (kapp_fn iota_view_fixture_expr)))))
     (OptionType.some KExpr iota_tail_fixture_result)) => Nat.zero)", "The actual Type-valued compatibility view has a concrete success caller, not only a universal implication."),
    (r"def iota_view_fixture_missing_universe : Eq (OptionType KExpr)
 (iota_reduct iota_view_fixture_env (KExpr.app (KExpr.app (KExpr.app (KExpr.const (Name.str Name.anonymous Nat.zero) (ListType.nil Level)) (KExpr.sort Level.zero)) iota_view_fixture_major) (KExpr.sort (Level.succ (Level.succ Level.zero))))) (OptionType.none KExpr) :=
 Eq.refl (OptionType KExpr) (OptionType.none KExpr)", "The actual updated five-lookup operator refuses this malformed spine through its active guard; not merely a detached tail test."),
    (r"def iota_view_fixture_extra_universe : Eq (OptionType KExpr)
 (iota_reduct iota_view_fixture_env (KExpr.app (KExpr.app (KExpr.app (KExpr.const (Name.str Name.anonymous Nat.zero) (ListType.cons Level iota_tail_fixture_level (ListType.cons Level Level.zero (ListType.nil Level)))) (KExpr.sort Level.zero)) iota_view_fixture_major) (KExpr.sort (Level.succ (Level.succ Level.zero))))) (OptionType.none KExpr) :=
 Eq.refl (OptionType KExpr) (OptionType.none KExpr)", "The actual updated five-lookup operator refuses this malformed spine through its active guard; not merely a detached tail test."),
    (r"def iota_view_fixture_missing_field : Eq (OptionType KExpr)
 (iota_reduct iota_view_fixture_env (KExpr.app (KExpr.app (KExpr.app (KExpr.const (Name.str Name.anonymous Nat.zero) (ListType.cons Level iota_tail_fixture_level (ListType.nil Level))) (KExpr.sort Level.zero)) (KExpr.const Name.anonymous (ListType.nil Level))) (KExpr.sort (Level.succ (Level.succ Level.zero))))) (OptionType.none KExpr) :=
 Eq.refl (OptionType KExpr) (OptionType.none KExpr)", "The actual updated five-lookup operator refuses this malformed spine through its active guard; not merely a detached tail test."),
];

impl Specification {
    /// After actual guarded iota, its tail views/intro, and both existing opt_bind
    /// inversion helpers; before old iota_core/par_reduces_c callers.
    pub(super) fn add_iota_reduct_views(&mut self) -> Result<(), SpecError> {
        for (source, description) in PROOFS {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }

    /// After the actual tail fixture controls; does not constrain general views.
    pub(super) fn add_iota_reduct_view_controls(&mut self) -> Result<(), SpecError> {
        for (source, description) in CONTROLS {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::test_utils::{build_spec_with_stack, run_with_stack};

    #[test]
    fn guarded_iota_views_have_empty_actual_axiom_closures() {
        let spec = build_spec_with_stack();
        for name in [
            "iota_reduct_full_inv",
            "iota_reduct_full_inv_type",
            "iota_reduct_full_recon",
            "iota_reduct_some_inv",
            "iota_reduct_some_inv_type",
            "iota_reduct_full_roundtrip",
            "iota_view_fixture_success",
            "iota_view_fixture_roundtrip",
            "iota_view_fixture_compat",
            "iota_view_fixture_compat_type",
            "iota_view_fixture_missing_universe",
            "iota_view_fixture_extra_universe",
            "iota_view_fixture_missing_field",
        ] {
            let definition = spec
                .definitions()
                .get(name)
                .expect("registered actual iota view/control");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
    }

    #[test]
    fn guarded_iota_views_reject_forged_missing_extra_universes_and_fields() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for source in [
                "def iota_view_forged_missing_universe : Eq (OptionType KExpr) (iota_reduct iota_view_fixture_env (KExpr.app (KExpr.app (KExpr.app (KExpr.const (Name.str Name.anonymous Nat.zero) (ListType.nil Level)) (KExpr.sort Level.zero)) iota_view_fixture_major) (KExpr.sort (Level.succ (Level.succ Level.zero))))) (OptionType.some KExpr iota_tail_fixture_result) := Eq.refl (OptionType KExpr) (OptionType.some KExpr iota_tail_fixture_result)",
                "def iota_view_forged_extra_universe : Eq (OptionType KExpr) (iota_reduct iota_view_fixture_env (KExpr.app (KExpr.app (KExpr.app (KExpr.const (Name.str Name.anonymous Nat.zero) (ListType.cons Level iota_tail_fixture_level (ListType.cons Level Level.zero (ListType.nil Level)))) (KExpr.sort Level.zero)) iota_view_fixture_major) (KExpr.sort (Level.succ (Level.succ Level.zero))))) (OptionType.some KExpr iota_tail_fixture_result) := Eq.refl (OptionType KExpr) (OptionType.some KExpr iota_tail_fixture_result)",
                "def iota_view_forged_missing_field : Eq (OptionType KExpr) (iota_reduct iota_view_fixture_env (KExpr.app (KExpr.app (KExpr.app (KExpr.const (Name.str Name.anonymous Nat.zero) (ListType.cons Level iota_tail_fixture_level (ListType.nil Level))) (KExpr.sort Level.zero)) (KExpr.const Name.anonymous (ListType.nil Level))) (KExpr.sort (Level.succ (Level.succ Level.zero))))) (OptionType.some KExpr iota_tail_fixture_result) := Eq.refl (OptionType KExpr) (OptionType.some KExpr iota_tail_fixture_result)",
            ] {
                assert!(spec.add_recursive_def(source, "Actual iota guard bypass must be rejected").is_err());
            }
        });
    }
}
