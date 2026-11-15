// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! CLI/profile selection only. All profiles use the same live-Expr exporter.

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) enum ExportProfile {
    #[default]
    Full,
    EvalIrByteV1,
    EvalIrByteLiteralV1,
}

impl ExportProfile {
    pub(super) fn constructor_name(self) -> &'static str {
        match self {
            Self::Full => "Specification::new()",
            Self::EvalIrByteV1 => "Specification::new_eval_ir_byte_prelude_spec_v1()",
            Self::EvalIrByteLiteralV1 => "Specification::new_eval_ir_byte_literal_spec_v1()",
        }
    }

    pub(super) fn default_roots(self) -> Vec<String> {
        match self {
            Self::Full => super::audit_roots::default_roots()
                .map(str::to_owned)
                .collect(),
            Self::EvalIrByteV1 => BYTE_V1_ROOTS
                .iter()
                .map(|name| (*name).to_owned())
                .collect(),
            Self::EvalIrByteLiteralV1 => {
                let mut roots = Self::Full.default_roots();
                for name in BYTE_V1_ROOTS.iter().chain(BYTE_LITERAL_V1_ROOTS) {
                    if !roots.iter().any(|root| root.as_str() == *name) {
                        roots.push((*name).to_owned());
                    }
                }
                roots
            }
        }
    }
}

const BYTE_LITERAL_V1_ROOTS: &[&str] = &[
    "ir_byte_builtin_literal_type_v1",
    "ir_byte_literal_type_result_v1",
    "ir_byte_literal_type_v1",
    "ir_byte_literal_nat_input_v1",
    "ir_byte_literal_string_input_v1",
    "ir_byte_literal_infers_v1",
    "ir_byte_literal_typing_v1",
    "ir_byte_literal_infers_sound_v1",
    "ir_byte_literal_nat_infers_input_v1",
    "ir_byte_literal_string_infers_input_v1",
    "ir_byte_literal_nat_typing_input_v1",
    "ir_byte_literal_string_typing_input_v1",
];

// Operational composition and memory/world laws, not source-refinement or
// native-execution claims. Full-spec kernel-inference roots are not installed
// by the smaller byte prelude and must never be selected as its defaults.
const BYTE_V1_ROOTS: &[&str] = &[
    "ir_byte_nat_eqb_sound_walk_v1",
    "ir_byte_nat_eqb_sound_v1",
    "ir_byte_type_equality_sound_v1",
    "ir_byte_field_selected_extract_from_inputs_v1",
    "ir_byte_field_option_none_some_false_v1",
    "ir_byte_field_option_some_injective_v1",
    "ir_byte_field_spine_set_typed_v1",
    "ir_byte_field_spine_get_typed_v1",
    "ir_byte_field_enum_spine_set_succ_invariant_v1",
    "ir_byte_field_types_set_writable_invariant_v1",
    "ir_byte_field_aggregate_spine_equation_v1",
    "ir_byte_field_aggregate_selected_spine_equation_v1",
    "ir_byte_field_inserted_value_admission_v1",
    "ir_byte_field_selected_insert_from_inputs_v1",
    "ir_byte_field_checked_input_v1",
    "ir_byte_field_selected_extract_v1",
    "ir_byte_field_selected_insert_v1",
    "ir_byte_field_extract_old_refused_v1",
    "ir_byte_field_insert_old_refused_v1",
    "ir_byte_field_enum_tag_write_refused_v1",
    "ir_byte_field_extract_mkt_v1",
    "ir_byte_field_insert_mkt_v1",
    "ir_byte_field_extract_metadata_refused_v1",
    "ir_byte_field_insert_metadata_refused_v1",
    "ir_byte_field_bind_world_v1",
    "ir_byte_field_scalar_world_v1",
    "ir_byte_field_fault_world_v1",
    "ir_byte_step_field_extract_v1",
    "ir_byte_step_field_insert_v1",
    "ir_byte_const_checked_input_v1",
    "ir_byte_const_fields_nil_v1",
    "ir_byte_const_fields_cons_v1",
    "ir_byte_const_zero_pointer_v1",
    "ir_byte_const_zero_fatstr_v1",
    "ir_byte_const_zero_fatslice_v1",
    "ir_byte_const_zero_fatdyn_v1",
    "ir_byte_const_zero_containerlen_v1",
    "ir_byte_const_zero_containervtable_v1",
    "ir_byte_enum_selected_fields_v1",
    "ir_byte_enum_ssa_selected_v1",
    "ir_byte_enum_ssa_input_v1",
    "ir_byte_enum_ssa_tag_v1",
    "ir_byte_enum_ssa_payload_v1",
    "ir_byte_enum_empty_extension_v1",
    "ir_byte_enum_empty_context_refused_v1",
    "ir_byte_enum_raw_lane_refused_v1",
    "ir_byte_enum_raw_decode_refused_v1",
    "ir_byte_enum_raw_load_refused_v1",
    "ir_byte_enum_raw_store_refused_v1",
    "ir_byte_arc_clone_old_guard_v1",
    "ir_byte_arc_clone_increment_bounded_v1",
    "ir_byte_usize64_rep_disjoint_write_v1",
    "ir_byte_arc_count_pair_distinct_v1",
    "ir_byte_arc_count_pair_distinct_first_old_v1",
    "ir_byte_arc_count_pair_distinct_second_old_v1",
    "ir_byte_arc_count_pair_distinct_allocations_v1",
    "ir_byte_arc_count_pair_distinct_cursor_v1",
    "ir_byte_arc_count_pair_distinct_first_new_v1",
    "ir_byte_arc_count_pair_distinct_second_new_v1",
    "ir_byte_arc_count_pair_distinct_range_frame_v1",
    "ir_byte_arc_count_pair_distinct_sparse_frame_v1",
    "ir_byte_arc_count_pair_distinct_cached_word_v1",
    "ir_byte_arc_count_pair_distinct_nat_frame_v1",
    "ir_byte_arc_count_pair_distinct_string_frame_v1",
    "ir_byte_arc_count_pair_same_v1",
    "ir_byte_arc_count_pair_same_first_old_v1",
    "ir_byte_arc_count_pair_same_second_old_v1",
    "ir_byte_arc_count_pair_same_allocations_v1",
    "ir_byte_arc_count_pair_same_cursor_v1",
    "ir_byte_arc_count_pair_same_first_new_v1",
    "ir_byte_arc_count_pair_same_second_new_v1",
    "ir_byte_arc_count_pair_same_range_frame_v1",
    "ir_byte_arc_count_pair_same_sparse_frame_v1",
    "ir_byte_arc_count_pair_same_cached_word_v1",
    "ir_byte_arc_count_pair_same_nat_frame_v1",
    "ir_byte_arc_count_pair_same_string_frame_v1",
    "ir_byte_arc_tail_pointer_load_v1",
    "ir_byte_arc_tail_length_load_v1",
    "ir_byte_arc_tail_gep_v1",
    "ir_byte_arc_tail_project_v1",
    "ir_byte_arc_tail_project_input_v1",
    "ir_byte_arc_tail_observe_v1",
    "ir_byte_arc_tail_nat_input_v1",
    "ir_byte_arc_tail_string_input_v1",
    "ir_byte_run_zero_v1",
    "ir_byte_run_add_v1",
    "ir_byte_run_halted_v1",
    "ir_byte_internal_call_rule_v1",
    "ir_byte_indirect_call_exact_v1",
    "ir_byte_return_to_caller_v1",
    "ir_byte_store_reload_eight_v1",
    "ir_byte_import_return_world_v1",
    "ir_byte_u64_rep_v1",
    "ir_byte_fetch_add_relaxed_u64_seq_below_v1",
    "ir_byte_fetch_add_relaxed_u64_seq_old_v1",
    "ir_byte_fetch_add_relaxed_u64_seq_new_v1",
    "ir_byte_fetch_add_relaxed_u64_seq_allocations_v1",
    "ir_byte_fetch_add_relaxed_u64_seq_cursor_v1",
    "ir_byte_fetch_add_relaxed_u64_seq_frame_v1",
    "ir_byte_step_fetch_add_relaxed_u64_seq_below_v1",
    "ir_byte_run_fetch_add_relaxed_u64_seq_one_v1",
    "ir_byte_step_fetch_add_relaxed_u64_seq_world_v1",
    "ir_byte_step_fetch_add_relaxed_u64_seq_new_v1",
    "ir_byte_step_fetch_add_relaxed_u64_seq_frame_v1",
    "ir_byte_bitcast_ptr_identity_v1",
    "ir_byte_usize64_rep_v1",
    "ir_byte_fetch_add_relaxed_usize64_seq_below_v1",
    "ir_byte_fetch_add_relaxed_usize64_seq_old_v1",
    "ir_byte_fetch_add_relaxed_usize64_seq_new_v1",
    "ir_byte_fetch_add_relaxed_usize64_seq_allocations_v1",
    "ir_byte_fetch_add_relaxed_usize64_seq_cursor_v1",
    "ir_byte_fetch_add_relaxed_usize64_seq_frame_v1",
    "ir_byte_step_fetch_add_relaxed_usize64_seq_below_v1",
    "ir_byte_run_fetch_add_relaxed_usize64_seq_one_v1",
    "ir_byte_step_fetch_add_relaxed_usize64_seq_world_v1",
    "ir_byte_step_fetch_add_relaxed_usize64_seq_new_v1",
    "ir_byte_step_fetch_add_relaxed_usize64_seq_frame_v1",
    "ir_byte_icmp_usize64_ugt_canonical_v1",
    "ir_byte_icmp_usize64_ugt_le_v1",
    "ir_byte_icmp_usize64_ugt_lt_v1",
    "ir_byte_step_icmp_usize64_ugt_v1",
    "ir_byte_run_icmp_usize64_ugt_one_v1",
    "ir_byte_step_icmp_usize64_ugt_world_v1",
    "ir_byte_fatstr_data_v1",
    "ir_byte_fatstr_metadata_v1",
    "ir_byte_fatstr_fromparts_v1",
    "ir_byte_fatslice_data_v1",
    "ir_byte_fatslice_metadata_v1",
    "ir_byte_fatslice_fromparts_v1",
    "ir_byte_fatdyn_data_v1",
    "ir_byte_fatdyn_metadata_v1",
    "ir_byte_fatdyn_fromparts_v1",
    "ir_byte_containerlen_data_v1",
    "ir_byte_containerlen_metadata_v1",
    "ir_byte_containerlen_fromparts_v1",
    "ir_byte_containervtable_data_v1",
    "ir_byte_containervtable_metadata_v1",
    "ir_byte_containervtable_fromparts_v1",
    "ir_byte_builtin_name_atom_v1",
    "ir_byte_builtin_nat_read_v1",
    "ir_byte_builtin_nat_input_v1",
    "ir_byte_builtin_nat_range_frame_v1",
    "ir_byte_builtin_nat_write_frame_v1",
    "ir_byte_builtin_nat_clear_frame_v1",
    "ir_byte_builtin_string_read_v1",
    "ir_byte_builtin_string_input_v1",
    "ir_byte_builtin_string_range_frame_v1",
    "ir_byte_builtin_string_write_frame_v1",
    "ir_byte_builtin_string_clear_frame_v1",
];

#[derive(Debug, PartialEq, Eq)]
pub(super) struct Options {
    pub(super) out_path: String,
    pub(super) requested_roots: Vec<String>,
    pub(super) all_spec: bool,
    pub(super) profile: ExportProfile,
}

impl Default for Options {
    fn default() -> Self {
        Self {
            out_path: "CleanVerifyExport.lean".into(),
            requested_roots: Vec::new(),
            all_spec: false,
            profile: ExportProfile::Full,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(super) enum Command {
    Help,
    Export(Options),
}

pub(super) fn parse_args(args: impl IntoIterator<Item = String>) -> Result<Command, String> {
    let mut options = Options::default();
    let mut args = args.into_iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--out" => {
                options.out_path = args.next().ok_or("--out requires a path")?;
            }
            "--all-spec" => options.all_spec = true,
            "--eval-ir-byte-v1" | "--eval-ir-byte-literal-v1" => {
                let profile = if arg == "--eval-ir-byte-v1" {
                    ExportProfile::EvalIrByteV1
                } else {
                    ExportProfile::EvalIrByteLiteralV1
                };
                if options.profile != ExportProfile::Full && options.profile != profile {
                    return Err("profile selectors are mutually exclusive".into());
                }
                options.profile = profile;
            }
            "-h" | "--help" => return Ok(Command::Help),
            _ if arg.starts_with('-') => return Err(format!("unknown option {arg}")),
            _ => options.requested_roots.push(arg),
        }
    }
    Ok(Command::Export(options))
}

#[derive(Debug)]
pub(super) struct RootSelection {
    pub(super) roots: Vec<String>,
    pub(super) audit_roots: Vec<String>,
    pub(super) required_roots: Vec<String>,
    pub(super) refuse_skipped_closure: bool,
}

impl Options {
    pub(super) fn select_roots<'a>(
        &self,
        spec_names: impl IntoIterator<Item = &'a str>,
    ) -> RootSelection {
        let defaults = self.profile.default_roots();
        let mut roots = if self.all_spec || self.requested_roots.is_empty() {
            defaults.clone()
        } else {
            self.requested_roots.clone()
        };
        let audit_roots = if self.all_spec {
            // Explicitly requested roots remain obligations even with
            // --all-spec; the old parser silently discarded them here.
            for root in &self.requested_roots {
                if !roots.contains(root) {
                    roots.push(root.clone());
                }
            }
            let audit_roots = roots.clone();
            let mut names: Vec<_> = spec_names.into_iter().map(str::to_owned).collect();
            names.sort();
            for name in names {
                if !roots.contains(&name) {
                    roots.push(name);
                }
            }
            audit_roots
        } else {
            roots.clone()
        };
        let refuse_skipped_closure = self.profile != ExportProfile::Full;
        let required_roots = if refuse_skipped_closure {
            roots.clone()
        } else {
            self.requested_roots.clone()
        };
        RootSelection {
            roots,
            audit_roots,
            required_roots,
            refuse_skipped_closure,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{emit, require_export_coverage, require_roots_present, Walker};
    use clean_kernel::{Declaration, Environment, Expr, Level, Name};
    use std::collections::{HashMap, HashSet};

    fn options(args: &[&str]) -> Options {
        let Command::Export(options) =
            parse_args(args.iter().map(|arg| (*arg).to_owned())).expect("valid arguments")
        else {
            panic!("expected export command")
        };
        options
    }

    #[test]
    fn ordinary_default_and_all_spec_keep_full_profile_order() {
        let default = options(&[]);
        assert_eq!(default, Options::default());
        let selected = default.select_roots([]);
        assert_eq!(selected.roots, ExportProfile::Full.default_roots());
        assert_eq!(selected.audit_roots, selected.roots);
        assert!(selected.required_roots.is_empty());
        assert!(!selected.refuse_skipped_closure);

        let all = options(&["--all-spec"]).select_roots(["z_last", "a_first"]);
        let defaults = ExportProfile::Full.default_roots();
        assert_eq!(&all.roots[..defaults.len()], defaults.as_slice());
        assert_eq!(&all.roots[defaults.len()..], ["a_first", "z_last"]);
        assert_eq!(all.audit_roots, defaults);
    }

    #[test]
    fn byte_profile_has_its_own_default_and_audit_roots() {
        let options = options(&["--eval-ir-byte-v1", "--out", "Byte.lean"]);
        assert_eq!(options.profile, ExportProfile::EvalIrByteV1);
        assert_eq!(options.out_path, "Byte.lean");
        let selected = options.select_roots([]);
        assert_eq!(selected.roots, ExportProfile::EvalIrByteV1.default_roots());
        assert_eq!(selected.roots.len(), 149);
        for root in [
            "ir_byte_arc_clone_old_guard_v1",
            "ir_byte_arc_clone_increment_bounded_v1",
            "ir_byte_usize64_rep_disjoint_write_v1",
            "ir_byte_arc_count_pair_distinct_v1",
            "ir_byte_arc_count_pair_distinct_first_old_v1",
            "ir_byte_arc_count_pair_distinct_second_old_v1",
            "ir_byte_arc_count_pair_distinct_allocations_v1",
            "ir_byte_arc_count_pair_distinct_cursor_v1",
            "ir_byte_arc_count_pair_distinct_first_new_v1",
            "ir_byte_arc_count_pair_distinct_second_new_v1",
            "ir_byte_arc_count_pair_distinct_range_frame_v1",
            "ir_byte_arc_count_pair_distinct_sparse_frame_v1",
            "ir_byte_arc_count_pair_distinct_cached_word_v1",
            "ir_byte_arc_count_pair_distinct_nat_frame_v1",
            "ir_byte_arc_count_pair_distinct_string_frame_v1",
            "ir_byte_arc_count_pair_same_v1",
            "ir_byte_arc_count_pair_same_first_old_v1",
            "ir_byte_arc_count_pair_same_second_old_v1",
            "ir_byte_arc_count_pair_same_allocations_v1",
            "ir_byte_arc_count_pair_same_cursor_v1",
            "ir_byte_arc_count_pair_same_first_new_v1",
            "ir_byte_arc_count_pair_same_second_new_v1",
            "ir_byte_arc_count_pair_same_range_frame_v1",
            "ir_byte_arc_count_pair_same_sparse_frame_v1",
            "ir_byte_arc_count_pair_same_cached_word_v1",
            "ir_byte_arc_count_pair_same_nat_frame_v1",
            "ir_byte_arc_count_pair_same_string_frame_v1",
            "ir_byte_nat_eqb_sound_walk_v1",
            "ir_byte_nat_eqb_sound_v1",
            "ir_byte_type_equality_sound_v1",
            "ir_byte_field_selected_extract_from_inputs_v1",
            "ir_byte_field_option_none_some_false_v1",
            "ir_byte_field_option_some_injective_v1",
            "ir_byte_field_spine_set_typed_v1",
            "ir_byte_field_spine_get_typed_v1",
            "ir_byte_field_enum_spine_set_succ_invariant_v1",
            "ir_byte_field_types_set_writable_invariant_v1",
            "ir_byte_field_aggregate_spine_equation_v1",
            "ir_byte_field_aggregate_selected_spine_equation_v1",
            "ir_byte_field_inserted_value_admission_v1",
            "ir_byte_field_selected_insert_from_inputs_v1",
            "ir_byte_const_checked_input_v1",
            "ir_byte_const_fields_nil_v1",
            "ir_byte_const_fields_cons_v1",
            "ir_byte_const_zero_pointer_v1",
            "ir_byte_const_zero_fatstr_v1",
            "ir_byte_const_zero_fatslice_v1",
            "ir_byte_const_zero_fatdyn_v1",
            "ir_byte_const_zero_containerlen_v1",
            "ir_byte_const_zero_containervtable_v1",
            "ir_byte_enum_selected_fields_v1",
            "ir_byte_enum_ssa_selected_v1",
            "ir_byte_enum_ssa_input_v1",
            "ir_byte_enum_ssa_tag_v1",
            "ir_byte_enum_ssa_payload_v1",
            "ir_byte_enum_empty_extension_v1",
            "ir_byte_enum_empty_context_refused_v1",
            "ir_byte_enum_raw_lane_refused_v1",
            "ir_byte_enum_raw_decode_refused_v1",
            "ir_byte_enum_raw_load_refused_v1",
            "ir_byte_enum_raw_store_refused_v1",
            "ir_byte_arc_tail_pointer_load_v1",
            "ir_byte_arc_tail_length_load_v1",
            "ir_byte_arc_tail_gep_v1",
            "ir_byte_arc_tail_project_v1",
            "ir_byte_arc_tail_project_input_v1",
            "ir_byte_arc_tail_observe_v1",
            "ir_byte_arc_tail_nat_input_v1",
            "ir_byte_arc_tail_string_input_v1",
        ] {
            assert_eq!(
                selected
                    .roots
                    .iter()
                    .filter(|name| name.as_str() == root)
                    .count(),
                1,
                "each representation prerequisite must be selected exactly once"
            );
        }
        assert_eq!(selected.audit_roots, selected.roots);
        assert_eq!(selected.required_roots, selected.roots);
        assert!(selected.refuse_skipped_closure);
        assert!(!selected
            .roots
            .iter()
            .any(|root| root == "tc_infer_soundness"));
    }

    #[test]
    fn byte_all_spec_uses_selected_profile_and_sorted_registered_roots() {
        let options = options(&["--all-spec", "--eval-ir-byte-v1"]);
        let selected = options.select_roots(["z_registered", "ir_byte_run_add_v1", "a_registered"]);
        let defaults = ExportProfile::EvalIrByteV1.default_roots();
        assert_eq!(&selected.roots[..defaults.len()], defaults.as_slice());
        assert_eq!(
            &selected.roots[defaults.len()..],
            ["a_registered", "z_registered"]
        );
        assert_eq!(selected.audit_roots, defaults);
        assert_eq!(selected.required_roots, selected.roots);
    }

    #[test]
    fn explicit_roots_replace_defaults_but_are_never_discarded_by_all_spec() {
        for profile_flag in [
            None,
            Some("--eval-ir-byte-v1"),
            Some("--eval-ir-byte-literal-v1"),
        ] {
            let mut args = profile_flag.into_iter().collect::<Vec<_>>();
            args.push("a_user_root");
            let selected = options(&args).select_roots(["a_registered"]);
            assert_eq!(selected.roots, ["a_user_root"]);
            assert_eq!(selected.audit_roots, selected.roots);
            assert_eq!(selected.required_roots, selected.roots);
            args.push("--all-spec");
            let selected = options(&args).select_roots(["a_registered"]);
            for roots in [
                &selected.roots,
                &selected.audit_roots,
                &selected.required_roots,
            ] {
                assert!(roots.iter().any(|name| name == "a_user_root"));
            }
        }
    }

    #[test]
    fn joint_profile_requires_the_combined_roots_without_duplicates() {
        let options = options(&["--eval-ir-byte-literal-v1", "--all-spec"]);
        assert_eq!(
            options.profile.constructor_name(),
            "Specification::new_eval_ir_byte_literal_spec_v1()"
        );
        let selected = options.select_roots(["z_registered"]);
        let full = ExportProfile::Full.default_roots();
        assert_eq!(&selected.audit_roots[..full.len()], full.as_slice());
        for root in BYTE_V1_ROOTS.iter().chain(BYTE_LITERAL_V1_ROOTS) {
            assert!(selected
                .audit_roots
                .iter()
                .any(|name| name.as_str() == *root));
        }
        assert_eq!(
            selected.audit_roots.len(),
            selected.audit_roots.iter().collect::<HashSet<_>>().len()
        );
        assert!(selected.roots.contains(&"z_registered".into()));
        assert_eq!(selected.required_roots, selected.roots);
        assert!(selected.refuse_skipped_closure);
    }

    #[test]
    fn conflicting_profile_selectors_refuse_in_both_orders() {
        for args in [
            ["--eval-ir-byte-v1", "--eval-ir-byte-literal-v1"],
            ["--eval-ir-byte-literal-v1", "--eval-ir-byte-v1"],
        ] {
            assert_eq!(
                parse_args(args.map(str::to_owned)),
                Err("profile selectors are mutually exclusive".into())
            );
        }
    }

    #[test]
    fn help_and_bad_options_do_not_select_an_export() {
        assert_eq!(parse_args(["--help".into()]), Ok(Command::Help));
        assert_eq!(parse_args(["-h".into()]), Ok(Command::Help));
        assert_eq!(
            parse_args(["--out".into()]),
            Err("--out requires a path".into())
        );
        assert_eq!(
            parse_args(["--eval-ir-byte-v2".into()]),
            Err("unknown option --eval-ir-byte-v2".into())
        );
    }

    #[test]
    fn missing_explicit_root_refuses_even_when_all_spec_is_selected() {
        let env = Environment::default();
        let selected = options(&["--all-spec", "missing_root"]).select_roots([]);
        let error = require_roots_present(&env, &selected.required_roots).unwrap_err();
        assert!(error.contains("missing_root"));

        // The walker's historical fallback is not a fabricated declaration:
        // actual emission fails, and the strict boundary must retain failure.
        let mut walker = Walker::new(&env);
        walker.visit_name(&Name::from_string("missing_root"));
        let item = walker
            .order
            .first()
            .expect("unknown name records an attempted item");
        assert!(emit::emit_item(&env, item, &HashMap::new(), &HashSet::new()).is_err());
        assert!(require_export_coverage(&selected, &walker, &HashSet::new(), &[]).is_err());
    }

    #[test]
    fn byte_closure_refuses_skips_even_if_required_root_was_emitted() {
        let mut env = Environment::default();
        let root = Name::from_string("FixtureRoot");
        env.add_decl(Declaration::Axiom {
            name: root.clone(),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("explicit test axiom registers through checked API");
        let mut walker = Walker::new(&env);
        walker.visit_name(&root);
        let emitted = HashSet::from([root.to_string()]);
        let skipped = vec![(
            "FixtureDependency".into(),
            "unsupported test dependency".into(),
        )];
        for flag in ["--eval-ir-byte-v1", "--eval-ir-byte-literal-v1"] {
            let byte = options(&[flag, "FixtureRoot"]).select_roots([]);
            require_roots_present(&env, &byte.required_roots).expect("live requested root exists");
            let error = require_export_coverage(&byte, &walker, &emitted, &skipped).unwrap_err();
            assert!(error.contains("skipped closure") && error.contains("FixtureDependency"));
            assert!(require_export_coverage(&byte, &walker, &emitted, &[]).is_ok());
        }

        // Existing Full partial-export behavior is not globally tightened.
        let full = options(&[]).select_roots([]);
        assert!(require_export_coverage(&full, &walker, &emitted, &skipped).is_ok());
        let requested = options(&["FixtureRoot"]).select_roots([]);
        assert!(require_export_coverage(&requested, &walker, &HashSet::new(), &skipped).is_err());
    }

    #[test]
    fn missing_transitive_dependency_is_seen_by_the_real_walker() {
        let mut env = Environment::default();
        let dependency = Name::from_string("FixtureType");
        let root = Name::from_string("FixtureAlias");
        let type_ = Expr::sort(Level::succ(Level::zero()));
        env.add_decl(Declaration::Axiom {
            name: dependency.clone(),
            level_params: vec![],
            type_: type_.clone(),
        })
        .expect("explicit fixture type");
        env.add_decl(Declaration::Definition {
            name: root.clone(),
            level_params: vec![],
            type_,
            value: Expr::const_(dependency.clone(), vec![]),
            is_reducible: true,
        })
        .expect("checked fixture alias");
        // Deliberately damage only this test environment AFTER kernel checking.
        assert!(env.forget_decl(&dependency));
        let selected = options(&["--eval-ir-byte-v1", "FixtureAlias"]).select_roots([]);
        require_roots_present(&env, &selected.required_roots).expect("root itself still exists");
        let mut walker = Walker::new(&env);
        walker.visit_name(&root);
        assert!(walker.deps[&root].contains(&dependency));
        let item = walker
            .order
            .iter()
            .find(|item| item.name == dependency)
            .expect("dependency visited");
        let reason = emit::emit_item(&env, item, &HashMap::new(), &HashSet::new()).unwrap_err();
        let skipped = vec![(dependency.to_string(), reason)];
        // Even a mistakenly marked-emitted root cannot hide a closure skip.
        let emitted = HashSet::from([root.to_string()]);
        assert!(require_export_coverage(&selected, &walker, &emitted, &skipped).is_err());
    }

    #[test]
    fn real_constructor_and_recursor_roots_are_covered_by_their_inductive() {
        use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};

        let mut env = Environment::default();
        let tag = Name::from_string("FixtureTag");
        let constructor = Name::from_string("FixtureTag.mk");
        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: tag.clone(),
                type_: Expr::sort(Level::succ(Level::zero())),
                constructors: vec![Constructor {
                    name: constructor.clone(),
                    type_: Expr::const_(tag.clone(), vec![]),
                }],
            }],
        })
        .expect("checked one-constructor fixture");
        let recursor = Name::from_string("FixtureTag.rec");
        assert!(env.get_recursor(&recursor).is_some());
        let selected =
            options(&["--eval-ir-byte-v1", "FixtureTag.mk", "FixtureTag.rec"]).select_roots([]);
        require_roots_present(&env, &selected.required_roots).expect("real generated roots");
        let mut walker = Walker::new(&env);
        for root in [&constructor, &recursor] {
            walker.visit_name(root);
        }
        assert_eq!(
            walker.order.len(),
            1,
            "one inductive owner, not fabricated duplicate defs"
        );
        let emitted = HashSet::from([tag.to_string()]);
        assert!(require_export_coverage(&selected, &walker, &emitted, &[]).is_ok());
        assert!(!walker.root_was_emitted("FixtureTag.absent", &emitted));
    }
}
