// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Data("nig_eq_family", r"Name", r"kcre_eq_type_name"),
    DeclarationInput::Data(
        "nig_eq_levels",
        r"ListType Level",
        r"nig_param_levels (kconst_params kcre_eq_type_signature)",
    ),
    DeclarationInput::Data(
        "nig_eq_block",
        r"ListType Name",
        r"kind_all_names kcre_eq_ind_meta",
    ),
    DeclarationInput::Data(
        "nig_eq_former",
        r"KExpr",
        r"kconst_type kcre_eq_type_signature",
    ),
    DeclarationInput::Data(
        "nig_eq_ctor",
        r"KExpr",
        r"kconst_type kcre_eq_refl_signature",
    ),
    DeclarationInput::Data("nig_eq_return", r"KExpr", r"return_type nig_eq_ctor"),
    DeclarationInput::Data(
        "nig_eq_domains",
        r"ListType KExpr",
        r"list_take (kind_num_params kcre_eq_ind_meta) (nig_pi_domains nig_eq_former)",
    ),
    DeclarationInput::Proof(
        "nig_eq_actual_guard",
        r"@Eq Bool (nig_strict_app_b nig_eq_block nig_eq_levels nig_eq_family (count_pi nig_eq_ctor) (kind_num_params kcre_eq_ind_meta) (kind_num_indices kcre_eq_ind_meta) nig_eq_return) Bool.true",
        r"@Eq.refl Bool Bool.true",
    ),
    DeclarationInput::Proof(
        "nig_eq_actual_facts",
        r"NamedStrictAppFacts nig_eq_block nig_eq_levels nig_eq_family (count_pi nig_eq_ctor) (kind_num_params kcre_eq_ind_meta) (kind_num_indices kcre_eq_ind_meta) nig_eq_return",
        r"nig_strict_sound nig_eq_block nig_eq_levels nig_eq_family (count_pi nig_eq_ctor) (kind_num_params kcre_eq_ind_meta) (kind_num_indices kcre_eq_ind_meta) nig_eq_return nig_eq_actual_guard",
    ),
    DeclarationInput::Proof(
        "nig_eq_actual_arity",
        r"@Eq Nat (list_length (kapp_args nig_eq_return)) (Nat.add (kind_num_params kcre_eq_ind_meta) (kind_num_indices kcre_eq_ind_meta))",
        r"nig_strict_arity nig_eq_block nig_eq_levels nig_eq_family (count_pi nig_eq_ctor) (kind_num_params kcre_eq_ind_meta) (kind_num_indices kcre_eq_ind_meta) nig_eq_return nig_eq_actual_facts",
    ),
    DeclarationInput::Proof(
        "nig_eq_prefix_guard",
        r"@Eq Bool (nig_pi_prefix_b nig_eq_domains nig_eq_ctor) Bool.true",
        r"@Eq.refl Bool Bool.true",
    ),
    DeclarationInput::Proof(
        "nig_eq_caller_bound",
        r"Le (kind_num_params kcre_eq_ind_meta) (count_pi nig_eq_ctor)",
        r"nig_prefix_bound nig_eq_domains nig_eq_ctor nig_eq_prefix_guard",
    ),
    DeclarationInput::Proof(
        "nig_eq_member_count",
        r"@Eq Nat (count_pi nig_eq_former) (Nat.add (kind_num_params kcre_eq_ind_meta) (kind_num_indices kcre_eq_ind_meta))",
        r"nig_selected_member_count (kind_num_params kcre_eq_ind_meta) (kind_num_indices kcre_eq_ind_meta) Nat.zero (@ListType.cons KExpr nig_eq_former (@ListType.nil KExpr)) nig_eq_former
 (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr nig_eq_former))
 (@Eq.refl (OptionType Nat) (@OptionType.some Nat (kind_num_indices kcre_eq_ind_meta)))",
    ),
    DeclarationInput::Proof(
        "nig_eq_suffix_exclusion",
        r"@Eq Bool (const_occurs nig_eq_family (KExpr.bvar Nat.zero)) Bool.false",
        r"nig_index_excludes_member nig_eq_block (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr)) Nat.zero (KExpr.bvar Nat.zero) nig_eq_family
 (@Eq.refl Bool Bool.true) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.bvar Nat.zero))) (@Eq.refl Bool Bool.true)",
    ),
    DeclarationInput::Proof(
        "nig_eq_field_count_is_not_index_count",
        r"@Eq Bool (nat_eqb (kctor_num_fields kcre_eq_refl_meta) (kind_num_indices kcre_eq_ind_meta)) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_two_members_left",
        r"forall (f g : Name) (levels : ListType Level), @Eq Bool (nig_strict_app_b (@ListType.cons Name f (@ListType.cons Name g (@ListType.nil Name))) levels f (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr))) (KExpr.const f levels))) Bool.true",
        r"fun (f g : Name) (levels : ListType Level) => nig_strict_complete (@ListType.cons Name f (@ListType.cons Name g (@ListType.nil Name))) levels f (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr))) (KExpr.const f levels))
 (@NamedStrictAppFacts.mk (@ListType.cons Name f (@ListType.cons Name g (@ListType.nil Name))) levels f (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr))) (KExpr.const f levels)) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr))
  (@Eq.refl KExpr (KExpr.const f levels))
  (@Eq.refl (ListType KExpr) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr))))
  (@Eq.refl Nat (Nat.succ Nat.zero)) (@Eq.refl Bool Bool.true))",
    ),
    DeclarationInput::Proof(
        "nig_two_members_right",
        r"forall (f g : Name) (levels : ListType Level), @Eq Bool (nig_strict_app_b (@ListType.cons Name f (@ListType.cons Name g (@ListType.nil Name))) levels g (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ (Nat.succ Nat.zero)) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr)))) (KExpr.const g levels))) Bool.true",
        r"fun (f g : Name) (levels : ListType Level) => nig_strict_complete (@ListType.cons Name f (@ListType.cons Name g (@ListType.nil Name))) levels g (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ (Nat.succ Nat.zero)) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr)))) (KExpr.const g levels))
 (@NamedStrictAppFacts.mk (@ListType.cons Name f (@ListType.cons Name g (@ListType.nil Name))) levels g (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ (Nat.succ Nat.zero)) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr)))) (KExpr.const g levels)) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr)))
  (@Eq.refl KExpr (KExpr.const g levels))
  (@Eq.refl (ListType KExpr) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr)))))
  (@Eq.refl Nat (Nat.succ (Nat.succ Nat.zero))) (@Eq.refl Bool Bool.true))",
    ),
    DeclarationInput::Proof(
        "nig_two_member_selected_count",
        r"@Eq Nat (count_pi (KExpr.pi (KExpr.sort Level.zero) (KExpr.pi (KExpr.sort Level.zero) (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero))))) (Nat.add (Nat.succ Nat.zero) (Nat.succ (Nat.succ Nat.zero)))",
        r"nig_selected_member_count (Nat.succ Nat.zero) (Nat.succ (Nat.succ Nat.zero)) (Nat.succ Nat.zero) (@ListType.cons KExpr (KExpr.pi (KExpr.sort Level.zero) (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero))) (@ListType.cons KExpr (KExpr.pi (KExpr.sort Level.zero) (KExpr.pi (KExpr.sort Level.zero) (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero)))) (@ListType.nil KExpr))) (KExpr.pi (KExpr.sort Level.zero) (KExpr.pi (KExpr.sort Level.zero) (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero))))
 (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.pi (KExpr.sort Level.zero) (KExpr.pi (KExpr.sort Level.zero) (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero))))))
 (@Eq.refl (OptionType Nat) (@OptionType.some Nat (Nat.succ (Nat.succ Nat.zero))))",
    ),
    DeclarationInput::Proof(
        "nig_two_member_prefix_bound",
        r"Le (Nat.succ Nat.zero) (count_pi (KExpr.pi (KExpr.sort Level.zero) (KExpr.pi (KExpr.sort Level.zero) (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero)))))",
        r"nig_prefix_bound (@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.nil KExpr)) (KExpr.pi (KExpr.sort Level.zero) (KExpr.pi (KExpr.sort Level.zero) (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero)))) (@Eq.refl Bool Bool.true)",
    ),
    DeclarationInput::Proof(
        "nig_refuses_wrong_family",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr))) (KExpr.const (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Level)))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_nonconstant_head",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr))) (KExpr.bvar Nat.zero))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_missing_index",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr)) (KExpr.const Name.anonymous (@ListType.nil Level)))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_extra_index",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr)))) (KExpr.const Name.anonymous (@ListType.nil Level)))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_wrong_member_index_count",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ (Nat.succ Nat.zero)) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr))) (KExpr.const Name.anonymous (@ListType.nil Level)))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_constant_parameter",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr))) (KExpr.const Name.anonymous (@ListType.nil Level)))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_own_index",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.const Name.anonymous (@ListType.nil Level)) (@ListType.nil KExpr))) (KExpr.const Name.anonymous (@ListType.nil Level)))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_sibling_index",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.const (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Level)) (@ListType.nil KExpr))) (KExpr.const Name.anonymous (@ListType.nil Level)))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_wrong_levels",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr))) (KExpr.const Name.anonymous (@ListType.cons Level Level.zero (@ListType.nil Level))))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_shared_domain",
        r"@Eq Bool (nig_pi_prefix_b (@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.nil KExpr)) (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.sort Level.zero))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_prefix_underflow",
        r"@Eq Bool (nig_pi_prefix_b (@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.nil KExpr)) (KExpr.sort Level.zero)) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_mutual_app_function",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.app (KExpr.const (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Level)) (KExpr.bvar Nat.zero)) (@ListType.nil KExpr))) (KExpr.const Name.anonymous (@ListType.nil Level)))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_mutual_app_argument",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) (KExpr.const (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Level))) (@ListType.nil KExpr))) (KExpr.const Name.anonymous (@ListType.nil Level)))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_mutual_lam_domain",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.lam (KExpr.const (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Level)) (KExpr.bvar Nat.zero)) (@ListType.nil KExpr))) (KExpr.const Name.anonymous (@ListType.nil Level)))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_mutual_lam_body",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.lam (KExpr.sort Level.zero) (KExpr.const (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Level))) (@ListType.nil KExpr))) (KExpr.const Name.anonymous (@ListType.nil Level)))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_mutual_pi_domain",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.pi (KExpr.const (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Level)) (KExpr.bvar Nat.zero)) (@ListType.nil KExpr))) (KExpr.const Name.anonymous (@ListType.nil Level)))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_mutual_pi_body",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.pi (KExpr.sort Level.zero) (KExpr.const (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Level))) (@ListType.nil KExpr))) (KExpr.const Name.anonymous (@ListType.nil Level)))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_mutual_let_type",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.let_ (KExpr.const (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Level)) (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)) (@ListType.nil KExpr))) (KExpr.const Name.anonymous (@ListType.nil Level)))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_mutual_let_value",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.let_ (KExpr.sort Level.zero) (KExpr.const (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Level)) (KExpr.bvar Nat.zero)) (@ListType.nil KExpr))) (KExpr.const Name.anonymous (@ListType.nil Level)))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_mutual_let_body",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.let_ (KExpr.sort Level.zero) (KExpr.bvar Nat.zero) (KExpr.const (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Level))) (@ListType.nil KExpr))) (KExpr.const Name.anonymous (@ListType.nil Level)))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_mutual_projection_subject",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.proj Name.anonymous Nat.zero (KExpr.const (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Level))) (@ListType.nil KExpr))) (KExpr.const Name.anonymous (@ListType.nil Level)))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_raw_semantic_level",
        r"@Eq Bool (nig_head_b Name.anonymous (@ListType.cons Level (Level.param Name.anonymous) (@ListType.nil Level))
 (KExpr.const Name.anonymous (@ListType.cons Level (Level.max (Level.param Name.anonymous) Level.zero) (@ListType.nil Level)))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_projection_label_not_occurrence",
        r"@Eq Bool (nig_block_free_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (KExpr.proj Name.anonymous Nat.zero (KExpr.bvar Nat.zero))) Bool.true",
        r"@Eq.refl Bool Bool.true",
    ),
    DeclarationInput::Proof(
        "nig_level_parameter_not_occurrence",
        r"@Eq Bool (nig_block_free_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (KExpr.sort (Level.param (Name.str Name.anonymous (Nat.succ Nat.zero))))) Bool.true",
        r"@Eq.refl Bool Bool.true",
    ),
    DeclarationInput::Proof(
        "nig_checked_index_underflow",
        r"@Eq (OptionType Nat) (nig_checked_indices (Nat.succ Nat.zero) (KExpr.sort Level.zero)) (@OptionType.none Nat)",
        r"@Eq.refl (OptionType Nat) (@OptionType.none Nat)",
    ),
    DeclarationInput::Proof(
        "nig_missing_member",
        r"@Eq (OptionType Nat) (nig_member_indices (Nat.succ Nat.zero) (@ListType.cons KExpr (KExpr.pi (KExpr.sort Level.zero) (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero))) (@ListType.cons KExpr (KExpr.pi (KExpr.sort Level.zero) (KExpr.pi (KExpr.sort Level.zero) (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero)))) (@ListType.nil KExpr))) (Nat.succ (Nat.succ Nat.zero))) (@OptionType.none Nat)",
        r"@Eq.refl (OptionType Nat) (@OptionType.none Nat)",
    ),
    DeclarationInput::Proof(
        "nig_strict_computed_suffix",
        r"forall (block : ListType Name) (levels : ListType Level) (family : Name) (d p ni : Nat) (e : KExpr), NamedStrictAppFacts block levels family d p ni e -> @Eq Bool (nig_indices_free_b block (list_drop p (kapp_args e))) Bool.true",
        r"fun (block : ListType Name) (levels : ListType Level) (family : Name) (d p ni : Nat) (e : KExpr) (facts : NamedStrictAppFacts block levels family d p ni e) => @NamedStrictAppFacts.rec block levels family d p ni e
 (fun (_facts : NamedStrictAppFacts block levels family d p ni e) => @Eq Bool (nig_indices_free_b block (list_drop p (kapp_args e))) Bool.true)
 (fun (ix : ListType KExpr) (head : @Eq KExpr (kapp_fn e) (KExpr.const family levels))
 (spine : @Eq (ListType KExpr) (kapp_args e) (list_append (nig_slots d p Nat.zero) ix))
 (length : @Eq Nat (list_length ix) ni) (free : @Eq Bool (nig_indices_free_b block ix) Bool.true) => Eq.subst (ListType KExpr)
  (fun (xs : ListType KExpr) => @Eq Bool (nig_indices_free_b block xs) Bool.true) ix (list_drop p (kapp_args e))
  (Eq.symm (ListType KExpr) (list_drop p (kapp_args e)) ix (Eq.trans (ListType KExpr) (list_drop p (kapp_args e)) (list_drop p (list_append (nig_slots d p Nat.zero) ix)) ix
 (Eq.cong (ListType KExpr) (ListType KExpr) (fun (xs : ListType KExpr) => list_drop p xs)
  (kapp_args e) (list_append (nig_slots d p Nat.zero) ix) spine)
 (Eq.trans (ListType KExpr) (list_drop p (list_append (nig_slots d p Nat.zero) ix)) (list_drop (list_length (nig_slots d p Nat.zero)) (list_append (nig_slots d p Nat.zero) ix)) ix
  (Eq.cong Nat (ListType KExpr) (fun (q : Nat) => list_drop q (list_append (nig_slots d p Nat.zero) ix)) p (list_length (nig_slots d p Nat.zero))
   (Eq.symm Nat (list_length (nig_slots d p Nat.zero)) p (nig_slots_length d p Nat.zero)))
  (list_drop_append_gen (nig_slots d p Nat.zero) Nat.zero ix)))) free) facts",
    ),
    DeclarationInput::Proof(
        "nig_eq_actual_suffix_free",
        r"@Eq Bool (nig_indices_free_b nig_eq_block (list_drop (kind_num_params kcre_eq_ind_meta) (kapp_args nig_eq_return))) Bool.true",
        r"nig_strict_computed_suffix nig_eq_block nig_eq_levels nig_eq_family (count_pi nig_eq_ctor) (kind_num_params kcre_eq_ind_meta) (kind_num_indices kcre_eq_ind_meta) nig_eq_return nig_eq_actual_facts",
    ),
    DeclarationInput::Proof(
        "nig_eq_actual_decomposition",
        r"forall (C : Type), (forall (ix : ListType KExpr), @Eq KExpr nig_eq_return
 (apply_spine (list_append (nig_slots (count_pi nig_eq_ctor) (kind_num_params kcre_eq_ind_meta) Nat.zero) ix) (KExpr.const nig_eq_family nig_eq_levels)) ->
 @Eq Nat (list_length ix) (kind_num_indices kcre_eq_ind_meta) -> @Eq Bool (nig_indices_free_b nig_eq_block ix) Bool.true -> C) -> C",
        r"nig_strict_decompose nig_eq_block nig_eq_levels nig_eq_family (count_pi nig_eq_ctor) (kind_num_params kcre_eq_ind_meta) (kind_num_indices kcre_eq_ind_meta) nig_eq_return nig_eq_actual_facts",
    ),
    DeclarationInput::Proof(
        "nig_eq_actual_suffix_exact",
        r"@Eq (ListType KExpr) (list_drop (kind_num_params kcre_eq_ind_meta) (kapp_args nig_eq_return)) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr))",
        r"@Eq.refl (ListType KExpr) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr))",
    ),
    DeclarationInput::Proof(
        "nig_eq_actual_member_exclusion",
        r"@Eq Bool (const_occurs nig_eq_family (KExpr.bvar Nat.zero)) Bool.false",
        r"nig_index_excludes_member nig_eq_block (list_drop (kind_num_params kcre_eq_ind_meta) (kapp_args nig_eq_return)) Nat.zero (KExpr.bvar Nat.zero) nig_eq_family
 nig_eq_actual_suffix_free (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.bvar Nat.zero))) (@Eq.refl Bool Bool.true)",
    ),
    DeclarationInput::Proof(
        "nig_refuses_swapped_eq_parameters",
        r"@Eq Bool (nig_strict_app_b nig_eq_block nig_eq_levels nig_eq_family (count_pi nig_eq_ctor) (kind_num_params kcre_eq_ind_meta) (kind_num_indices kcre_eq_ind_meta)
 (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar (Nat.succ Nat.zero)) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr)))) (KExpr.const nig_eq_family nig_eq_levels))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_same_length_level_name",
        r"@Eq Bool (nig_head_b Name.anonymous (@ListType.cons Level (Level.param Name.anonymous) (@ListType.nil Level)) (KExpr.const Name.anonymous (@ListType.cons Level (Level.param (Name.str Name.anonymous (Nat.succ Nat.zero))) (@ListType.nil Level)))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_reordered_level_names",
        r"@Eq Bool (nig_head_b Name.anonymous (@ListType.cons Level (Level.param Name.anonymous) (@ListType.cons Level (Level.param (Name.str Name.anonymous (Nat.succ Nat.zero))) (@ListType.nil Level))) (KExpr.const Name.anonymous (@ListType.cons Level (Level.param (Name.str Name.anonymous (Nat.succ Nat.zero))) (@ListType.cons Level (Level.param Name.anonymous) (@ListType.nil Level))))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_refuses_genuine_const_parameter",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (@ListType.nil Level) Name.anonymous
 (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.const (Name.str Name.anonymous (Nat.succ (Nat.succ Nat.zero))) (@ListType.nil Level)) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr))) (KExpr.const Name.anonymous (@ListType.nil Level)))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nig_eq_stored_inductive_lookup",
        r"@Eq (OptionType KIndMeta) (kind_for (red_ind_ctor the_red_env) kcre_eq_type_name) (@OptionType.some KIndMeta kcre_eq_ind_meta)",
        r"@Eq.refl (OptionType KIndMeta) (@OptionType.some KIndMeta kcre_eq_ind_meta)",
    ),
    DeclarationInput::Proof(
        "nig_eq_stored_constructor_lookup",
        r"@Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor the_red_env) kcre_eq_refl_name) (@OptionType.some KCtorMeta kcre_eq_refl_meta)",
        r"@Eq.refl (OptionType KCtorMeta) (@OptionType.some KCtorMeta kcre_eq_refl_meta)",
    ),
    DeclarationInput::Proof(
        "nig_eq_stored_inductive_signature",
        r"@Eq KConstSig (kind_sig kcre_eq_ind_meta) kcre_eq_type_signature",
        r"@Eq.refl KConstSig kcre_eq_type_signature",
    ),
    DeclarationInput::Proof(
        "nig_eq_stored_constructor_signature",
        r"@Eq KConstSig (kctor_sig kcre_eq_refl_meta) kcre_eq_refl_signature",
        r"@Eq.refl KConstSig kcre_eq_refl_signature",
    ),
    DeclarationInput::Proof(
        "nig_eq_tenv_inductive_signature",
        r"@Eq (OptionType KConstSig) (kcre_ind_ctor_tenv kcre_eq_type_name) (@OptionType.some KConstSig kcre_eq_type_signature)",
        r"@Eq.refl (OptionType KConstSig) (@OptionType.some KConstSig kcre_eq_type_signature)",
    ),
    DeclarationInput::Proof(
        "nig_eq_tenv_constructor_signature",
        r"@Eq (OptionType KConstSig) (kcre_ind_ctor_tenv kcre_eq_refl_name) (@OptionType.some KConstSig kcre_eq_refl_signature)",
        r"@Eq.refl (OptionType KConstSig) (@OptionType.some KConstSig kcre_eq_refl_signature)",
    ),
    DeclarationInput::Proof(
        "nig_eq_stored_constructor_parent",
        r"@Eq Name (kctor_parent kcre_eq_refl_meta) kcre_eq_type_name",
        r"@Eq.refl Name kcre_eq_type_name",
    ),
    DeclarationInput::Proof(
        "nig_eq_stored_block_member",
        r"@Eq Bool (name_list_mem (kind_all_names kcre_eq_ind_meta) kcre_eq_type_name) Bool.true",
        r"@Eq.refl Bool Bool.true",
    ),
    DeclarationInput::Proof(
        "nig_eq_stored_constructor_member",
        r"@Eq Bool (name_list_mem (kind_ctor_names kcre_eq_ind_meta) kcre_eq_refl_name) Bool.true",
        r"@Eq.refl Bool Bool.true",
    ),
    DeclarationInput::Proof(
        "nig_eq_stored_block_exact",
        r"@Eq (ListType Name) (kind_all_names kcre_eq_ind_meta) (@ListType.cons Name kcre_eq_type_name (@ListType.nil Name))",
        r"@Eq.refl (ListType Name) (@ListType.cons Name kcre_eq_type_name (@ListType.nil Name))",
    ),
    DeclarationInput::Proof(
        "nig_eq_stored_constructor_index",
        r"@Eq Nat (kctor_index kcre_eq_refl_meta) Nat.zero",
        r"@Eq.refl Nat Nat.zero",
    ),
    DeclarationInput::Proof(
        "nig_eq_stored_parameter_agreement",
        r"@Eq Nat (kctor_num_params kcre_eq_refl_meta) (kind_num_params kcre_eq_ind_meta)",
        r"@Eq.refl Nat (kind_num_params kcre_eq_ind_meta)",
    ),
    DeclarationInput::Proof(
        "nig_eq_stored_universe_parameters",
        r"@Eq (ListType Name) (kconst_params kcre_eq_refl_signature) (kconst_params kcre_eq_type_signature)",
        r"@Eq.refl (ListType Name) (kconst_params kcre_eq_type_signature)",
    ),
    DeclarationInput::Proof(
        "nig_eq_stored_constructor_count",
        r"@Eq Nat (count_pi (kconst_type kcre_eq_refl_signature)) (Nat.add (kctor_num_params kcre_eq_refl_meta) (kctor_num_fields kcre_eq_refl_meta))",
        r"@Eq.refl Nat (Nat.add (kctor_num_params kcre_eq_refl_meta) (kctor_num_fields kcre_eq_refl_meta))",
    ),
    DeclarationInput::Proof(
        "nig_eq_extracted_former_count",
        r"@Eq Nat (list_length (nig_pi_domains (kconst_type kcre_eq_type_signature))) (Nat.add (kind_num_params kcre_eq_ind_meta) (kind_num_indices kcre_eq_ind_meta))",
        r"Eq.trans Nat (list_length (nig_pi_domains nig_eq_former)) (count_pi nig_eq_former) (Nat.add (kind_num_params kcre_eq_ind_meta) (kind_num_indices kcre_eq_ind_meta))
 (nig_pi_domains_length nig_eq_former) nig_eq_member_count",
    ),
    DeclarationInput::Proof(
        "nig_eq_extracted_domain_count",
        r"@Eq Nat (list_length nig_eq_domains) (kind_num_params kcre_eq_ind_meta)",
        r"@Eq.refl Nat (kind_num_params kcre_eq_ind_meta)",
    ),
    DeclarationInput::Proof(
        "nig_eq_domains_from_former",
        r"@Eq (ListType KExpr) nig_eq_domains (list_take (kind_num_params kcre_eq_ind_meta) (nig_pi_domains (kconst_type kcre_eq_type_signature)))",
        r"@Eq.refl (ListType KExpr) (list_take (kind_num_params kcre_eq_ind_meta) (nig_pi_domains (kconst_type kcre_eq_type_signature)))",
    ),
    DeclarationInput::Proof(
        "nig_eq_connected_stored_context",
        r"forall (C : Type), ((@Eq (OptionType KIndMeta) (kind_for (red_ind_ctor the_red_env) kcre_eq_type_name) (@OptionType.some KIndMeta kcre_eq_ind_meta)) -> (@Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor the_red_env) kcre_eq_refl_name) (@OptionType.some KCtorMeta kcre_eq_refl_meta)) -> (@Eq KConstSig (kind_sig kcre_eq_ind_meta) kcre_eq_type_signature) -> (@Eq KConstSig (kctor_sig kcre_eq_refl_meta) kcre_eq_refl_signature) -> (@Eq (OptionType KConstSig) (kcre_ind_ctor_tenv kcre_eq_type_name) (@OptionType.some KConstSig kcre_eq_type_signature)) -> (@Eq (OptionType KConstSig) (kcre_ind_ctor_tenv kcre_eq_refl_name) (@OptionType.some KConstSig kcre_eq_refl_signature)) -> (@Eq Name (kctor_parent kcre_eq_refl_meta) kcre_eq_type_name) -> (@Eq Bool (name_list_mem (kind_all_names kcre_eq_ind_meta) kcre_eq_type_name) Bool.true) -> (@Eq Bool (name_list_mem (kind_ctor_names kcre_eq_ind_meta) kcre_eq_refl_name) Bool.true) -> (@Eq (ListType Name) (kind_all_names kcre_eq_ind_meta) (@ListType.cons Name kcre_eq_type_name (@ListType.nil Name))) -> (@Eq Nat (kctor_index kcre_eq_refl_meta) Nat.zero) -> (@Eq Nat (kctor_num_params kcre_eq_refl_meta) (kind_num_params kcre_eq_ind_meta)) -> (@Eq (ListType Name) (kconst_params kcre_eq_refl_signature) (kconst_params kcre_eq_type_signature)) -> (@Eq Nat (count_pi (kconst_type kcre_eq_refl_signature)) (Nat.add (kctor_num_params kcre_eq_refl_meta) (kctor_num_fields kcre_eq_refl_meta))) -> (@Eq Nat (list_length (nig_pi_domains (kconst_type kcre_eq_type_signature))) (Nat.add (kind_num_params kcre_eq_ind_meta) (kind_num_indices kcre_eq_ind_meta))) -> (@Eq Nat (list_length nig_eq_domains) (kind_num_params kcre_eq_ind_meta)) -> (@Eq (ListType KExpr) nig_eq_domains (list_take (kind_num_params kcre_eq_ind_meta) (nig_pi_domains (kconst_type kcre_eq_type_signature)))) -> (@Eq Bool (nig_pi_prefix_b nig_eq_domains nig_eq_ctor) Bool.true) -> (Le (kind_num_params kcre_eq_ind_meta) (count_pi nig_eq_ctor)) -> (NamedStrictAppFacts nig_eq_block nig_eq_levels nig_eq_family (count_pi nig_eq_ctor) (kind_num_params kcre_eq_ind_meta) (kind_num_indices kcre_eq_ind_meta) nig_eq_return) -> (@Eq Bool (nig_indices_free_b nig_eq_block (list_drop (kind_num_params kcre_eq_ind_meta) (kapp_args nig_eq_return))) Bool.true) -> C) -> C",
        r"fun (C : Type) (k : (@Eq (OptionType KIndMeta) (kind_for (red_ind_ctor the_red_env) kcre_eq_type_name) (@OptionType.some KIndMeta kcre_eq_ind_meta)) -> (@Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor the_red_env) kcre_eq_refl_name) (@OptionType.some KCtorMeta kcre_eq_refl_meta)) -> (@Eq KConstSig (kind_sig kcre_eq_ind_meta) kcre_eq_type_signature) -> (@Eq KConstSig (kctor_sig kcre_eq_refl_meta) kcre_eq_refl_signature) -> (@Eq (OptionType KConstSig) (kcre_ind_ctor_tenv kcre_eq_type_name) (@OptionType.some KConstSig kcre_eq_type_signature)) -> (@Eq (OptionType KConstSig) (kcre_ind_ctor_tenv kcre_eq_refl_name) (@OptionType.some KConstSig kcre_eq_refl_signature)) -> (@Eq Name (kctor_parent kcre_eq_refl_meta) kcre_eq_type_name) -> (@Eq Bool (name_list_mem (kind_all_names kcre_eq_ind_meta) kcre_eq_type_name) Bool.true) -> (@Eq Bool (name_list_mem (kind_ctor_names kcre_eq_ind_meta) kcre_eq_refl_name) Bool.true) -> (@Eq (ListType Name) (kind_all_names kcre_eq_ind_meta) (@ListType.cons Name kcre_eq_type_name (@ListType.nil Name))) -> (@Eq Nat (kctor_index kcre_eq_refl_meta) Nat.zero) -> (@Eq Nat (kctor_num_params kcre_eq_refl_meta) (kind_num_params kcre_eq_ind_meta)) -> (@Eq (ListType Name) (kconst_params kcre_eq_refl_signature) (kconst_params kcre_eq_type_signature)) -> (@Eq Nat (count_pi (kconst_type kcre_eq_refl_signature)) (Nat.add (kctor_num_params kcre_eq_refl_meta) (kctor_num_fields kcre_eq_refl_meta))) -> (@Eq Nat (list_length (nig_pi_domains (kconst_type kcre_eq_type_signature))) (Nat.add (kind_num_params kcre_eq_ind_meta) (kind_num_indices kcre_eq_ind_meta))) -> (@Eq Nat (list_length nig_eq_domains) (kind_num_params kcre_eq_ind_meta)) -> (@Eq (ListType KExpr) nig_eq_domains (list_take (kind_num_params kcre_eq_ind_meta) (nig_pi_domains (kconst_type kcre_eq_type_signature)))) -> (@Eq Bool (nig_pi_prefix_b nig_eq_domains nig_eq_ctor) Bool.true) -> (Le (kind_num_params kcre_eq_ind_meta) (count_pi nig_eq_ctor)) -> (NamedStrictAppFacts nig_eq_block nig_eq_levels nig_eq_family (count_pi nig_eq_ctor) (kind_num_params kcre_eq_ind_meta) (kind_num_indices kcre_eq_ind_meta) nig_eq_return) -> (@Eq Bool (nig_indices_free_b nig_eq_block (list_drop (kind_num_params kcre_eq_ind_meta) (kapp_args nig_eq_return))) Bool.true) -> C) => k nig_eq_stored_inductive_lookup
 nig_eq_stored_constructor_lookup
 nig_eq_stored_inductive_signature
 nig_eq_stored_constructor_signature
 nig_eq_tenv_inductive_signature
 nig_eq_tenv_constructor_signature
 nig_eq_stored_constructor_parent
 nig_eq_stored_block_member
 nig_eq_stored_constructor_member
 nig_eq_stored_block_exact
 nig_eq_stored_constructor_index
 nig_eq_stored_parameter_agreement
 nig_eq_stored_universe_parameters
 nig_eq_stored_constructor_count
 nig_eq_extracted_former_count
 nig_eq_extracted_domain_count
 nig_eq_domains_from_former
 nig_eq_prefix_guard
 nig_eq_caller_bound
 nig_eq_actual_facts
 nig_eq_actual_suffix_free",
    ),
];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "nig_forged_wrong_family",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr))) (KExpr.const (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Level)))) Bool.true",
        r"nig_refuses_wrong_family",
    ),
    (
        "nig_forged_missing_index",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr)) (KExpr.const Name.anonymous (@ListType.nil Level)))) Bool.true",
        r"nig_refuses_missing_index",
    ),
    (
        "nig_forged_wrong_levels",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr))) (KExpr.const Name.anonymous (@ListType.cons Level Level.zero (@ListType.nil Level))))) Bool.true",
        r"nig_refuses_wrong_levels",
    ),
    (
        "nig_forged_mutual_projection_subject",
        r"@Eq Bool (nig_strict_app_b (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Name))) (@ListType.nil Level) Name.anonymous (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.proj Name.anonymous Nat.zero (KExpr.const (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Level))) (@ListType.nil KExpr))) (KExpr.const Name.anonymous (@ListType.nil Level)))) Bool.true",
        r"nig_refuses_mutual_projection_subject",
    ),
    (
        "nig_forged_prefix_underflow",
        r"@Eq Bool (nig_pi_prefix_b (@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.nil KExpr)) (KExpr.sort Level.zero)) Bool.true",
        r"nig_refuses_prefix_underflow",
    ),
    (
        "nig_forged_eq_zero_indices",
        r"@Eq Nat (list_length (kapp_args nig_eq_return)) (kind_num_params kcre_eq_ind_meta)",
        r"nig_eq_actual_arity",
    ),
    (
        "nig_forged_swapped_eq_parameters",
        r"@Eq Bool (nig_strict_app_b nig_eq_block nig_eq_levels nig_eq_family (count_pi nig_eq_ctor) (kind_num_params kcre_eq_ind_meta) (kind_num_indices kcre_eq_ind_meta)
 (apply_spine (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.cons KExpr (KExpr.bvar (Nat.succ Nat.zero)) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr)))) (KExpr.const nig_eq_family nig_eq_levels))) Bool.true",
        r"nig_refuses_swapped_eq_parameters",
    ),
    (
        "nig_forged_same_length_level_name",
        r"@Eq Bool (nig_head_b Name.anonymous (@ListType.cons Level (Level.param Name.anonymous) (@ListType.nil Level)) (KExpr.const Name.anonymous (@ListType.cons Level (Level.param (Name.str Name.anonymous (Nat.succ Nat.zero))) (@ListType.nil Level)))) Bool.true",
        r"nig_refuses_same_length_level_name",
    ),
    (
        "nig_forged_captured_empty_block",
        r"@Eq (ListType Name) (kind_all_names kcre_eq_ind_meta) (@ListType.nil Name)",
        r"nig_eq_stored_block_exact",
    ),
    (
        "nig_forged_constructor_as_parent",
        r"@Eq Name (kctor_parent kcre_eq_refl_meta) kcre_eq_refl_name",
        r"nig_eq_stored_constructor_parent",
    ),
    (
        "nig_forged_zero_extracted_domains",
        r"@Eq Nat (list_length nig_eq_domains) Nat.zero",
        r"nig_eq_extracted_domain_count",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "nig_eq_actual_guard",
    "nig_eq_actual_facts",
    "nig_eq_actual_arity",
    "nig_eq_prefix_guard",
    "nig_eq_caller_bound",
    "nig_eq_member_count",
    "nig_eq_suffix_exclusion",
    "nig_eq_field_count_is_not_index_count",
    "nig_two_members_left",
    "nig_two_members_right",
    "nig_two_member_selected_count",
    "nig_two_member_prefix_bound",
    "nig_refuses_wrong_family",
    "nig_refuses_nonconstant_head",
    "nig_refuses_missing_index",
    "nig_refuses_extra_index",
    "nig_refuses_wrong_member_index_count",
    "nig_refuses_constant_parameter",
    "nig_refuses_own_index",
    "nig_refuses_sibling_index",
    "nig_refuses_wrong_levels",
    "nig_refuses_shared_domain",
    "nig_refuses_prefix_underflow",
    "nig_refuses_mutual_app_function",
    "nig_refuses_mutual_app_argument",
    "nig_refuses_mutual_lam_domain",
    "nig_refuses_mutual_lam_body",
    "nig_refuses_mutual_pi_domain",
    "nig_refuses_mutual_pi_body",
    "nig_refuses_mutual_let_type",
    "nig_refuses_mutual_let_value",
    "nig_refuses_mutual_let_body",
    "nig_refuses_mutual_projection_subject",
    "nig_refuses_raw_semantic_level",
    "nig_projection_label_not_occurrence",
    "nig_level_parameter_not_occurrence",
    "nig_checked_index_underflow",
    "nig_missing_member",
    "nig_strict_computed_suffix",
    "nig_eq_actual_suffix_free",
    "nig_eq_actual_decomposition",
    "nig_eq_actual_suffix_exact",
    "nig_eq_actual_member_exclusion",
    "nig_refuses_swapped_eq_parameters",
    "nig_refuses_same_length_level_name",
    "nig_refuses_reordered_level_names",
    "nig_refuses_genuine_const_parameter",
    "nig_eq_stored_inductive_lookup",
    "nig_eq_stored_constructor_lookup",
    "nig_eq_stored_inductive_signature",
    "nig_eq_stored_constructor_signature",
    "nig_eq_tenv_inductive_signature",
    "nig_eq_tenv_constructor_signature",
    "nig_eq_stored_constructor_parent",
    "nig_eq_stored_block_member",
    "nig_eq_stored_constructor_member",
    "nig_eq_stored_block_exact",
    "nig_eq_stored_constructor_index",
    "nig_eq_stored_parameter_agreement",
    "nig_eq_stored_universe_parameters",
    "nig_eq_stored_constructor_count",
    "nig_eq_extracted_former_count",
    "nig_eq_extracted_domain_count",
    "nig_eq_domains_from_former",
    "nig_eq_connected_stored_context",
];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[
    "nig_eq_family",
    "nig_eq_levels",
    "nig_eq_block",
    "nig_eq_former",
    "nig_eq_ctor",
    "nig_eq_return",
    "nig_eq_domains",
];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &[];

#[cfg(test)]
pub(super) const PROP_PROOF_ROOTS: &[&str] = &[
    "nig_eq_actual_guard",
    "nig_eq_actual_arity",
    "nig_eq_prefix_guard",
    "nig_eq_caller_bound",
    "nig_eq_member_count",
    "nig_eq_suffix_exclusion",
    "nig_eq_field_count_is_not_index_count",
    "nig_two_members_left",
    "nig_two_members_right",
    "nig_two_member_selected_count",
    "nig_two_member_prefix_bound",
    "nig_refuses_wrong_family",
    "nig_refuses_nonconstant_head",
    "nig_refuses_missing_index",
    "nig_refuses_extra_index",
    "nig_refuses_wrong_member_index_count",
    "nig_refuses_constant_parameter",
    "nig_refuses_own_index",
    "nig_refuses_sibling_index",
    "nig_refuses_wrong_levels",
    "nig_refuses_shared_domain",
    "nig_refuses_prefix_underflow",
    "nig_refuses_mutual_app_function",
    "nig_refuses_mutual_app_argument",
    "nig_refuses_mutual_lam_domain",
    "nig_refuses_mutual_lam_body",
    "nig_refuses_mutual_pi_domain",
    "nig_refuses_mutual_pi_body",
    "nig_refuses_mutual_let_type",
    "nig_refuses_mutual_let_value",
    "nig_refuses_mutual_let_body",
    "nig_refuses_mutual_projection_subject",
    "nig_refuses_raw_semantic_level",
    "nig_projection_label_not_occurrence",
    "nig_level_parameter_not_occurrence",
    "nig_checked_index_underflow",
    "nig_missing_member",
    "nig_strict_computed_suffix",
    "nig_eq_actual_suffix_free",
    "nig_eq_actual_suffix_exact",
    "nig_eq_actual_member_exclusion",
    "nig_refuses_swapped_eq_parameters",
    "nig_refuses_same_length_level_name",
    "nig_refuses_reordered_level_names",
    "nig_refuses_genuine_const_parameter",
    "nig_eq_stored_inductive_lookup",
    "nig_eq_stored_constructor_lookup",
    "nig_eq_stored_inductive_signature",
    "nig_eq_stored_constructor_signature",
    "nig_eq_tenv_inductive_signature",
    "nig_eq_tenv_constructor_signature",
    "nig_eq_stored_constructor_parent",
    "nig_eq_stored_block_member",
    "nig_eq_stored_constructor_member",
    "nig_eq_stored_block_exact",
    "nig_eq_stored_constructor_index",
    "nig_eq_stored_parameter_agreement",
    "nig_eq_stored_universe_parameters",
    "nig_eq_stored_constructor_count",
    "nig_eq_extracted_former_count",
    "nig_eq_extracted_domain_count",
    "nig_eq_domains_from_former",
];

#[cfg(test)]
pub(super) const TYPE_PROOF_ROOTS: &[&str] = &[
    "nig_eq_actual_facts",
    "nig_eq_actual_decomposition",
    "nig_eq_connected_stored_context",
];
