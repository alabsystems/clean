// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! End-to-end soundness regressions for the vendored Carcara checker.
//!
//! Each `soundness/<name>.{smt2,alethe}` pair without the `ok_` prefix is a complete refutation
//! of a SATISFIABLE problem. Except for the `dt_` pairs (below), upstream Carcara d62d45cf fully
//! verified every one of them through `verify_alethe_proof`. The vendored copy in
//! `third-party/carcara` must reject each one at the step that used the unsound rule. AY 0.26.0
//! (cc347ee0a) reports `sat` for every problem it parses. It does not parse the lambda, choice,
//! regular-expression and symbolic-string problems, whose models are below:
//!
//! - `be_u3_partial_capture`: y = 1; the left side is `w -> 1 + w`, the right side `w -> 2w`.
//! - `ext_u4_capture_reported`, `ext_u5_capture_uf`: the choice binder captures the free `x`, so
//!   the witness can be an index where the two arrays agree.
//! - `sub_u2_beta_equiv_rename_capture`: y = true, y_renamed = false. The left side reduces to
//!   `y_renamed`, the right side to `y`.
//! - `sub_u5_beta_equiv_let_value`: x = false. The left side beta-reduces to `true`, the right
//!   side is `x`.
//! - `sd_u3_symbolic_split`: n = -1, s = "". The premise `(>= (str.len s) n)` holds and
//!   `(= (str.len (str.substr s 0 n)) n)` does not, a length never being negative.
//! - `re_u1_concat_unfold_pos_witness`, `re_u2_kleene_star_unfold_pos_witness`: the Skolem
//!   witness' defining formula quantifies the regular languages away, so it only says the witness
//!   is a factor of the word and the conclusion pins it to one particular split.
//! - `re_u3_unfold_neg_concat_capture`: y = "a", L = 0. The premise holds because
//!   `(str.substr y 0 0)` is the empty word, and the conclusion fails at the quantified L = 1,
//!   which the generated binder shares with the free `L` of the premise.
//! - `re_u4_unfold_neg_star_capture`: y = "ab", L = 2, failing at the quantified L = 1.
//! - `ev_u7_sign_extend_width_2p32`, `ev_u8_bvadd_width_2p32_plus1`: AY refuses the width
//!   (`sign_extend result width overflows`). The problems are ground: at width `2^32` the two
//!   sign extensions are all ones and zero, and at width `2^32 + 1` the sum `1 + 1` is `2`, not `0`,
//!   so each asserted negation is true.
//!
//! The `ae_u5`..`ae_u8` and `ev_u7`/`ev_u8` pairs are the ones the verifier of 902dc98bf found still
//! fully verified there; they fail on that commit and pass with fixes 34 and 35.
//!
//! Each `ok_` pair is a sound refutation of an UNSATISFIABLE problem that uses the corrected
//! rule, and it must fully verify. AY reports `unsat` for each of them except
//! `ok_re_unfold_neg` and `ok_sd_nonnegative`, which it does not decide (`unknown`); those two
//! are instances of the rules' own valid schemas.
//!
//! `ok_and_simplify_nested_result` and `ok_or_simplify_nested_result` are not soundness fixes but
//! the completeness extension of `and_simplify`/`or_simplify` (a single remaining argument that is
//! itself an application of the rule operator is the result); both fail on f3acd3dac, without the
//! extension. AY 0.27.0 (build 11378) reports `unsat` for both.
//!
//! The `dt_` pairs exercise `dt_project`, a rule only Clean's copy has (completeness extension
//! C2), so upstream rejects them all as an unknown rule. They are refutations through that rule
//! instead: `ok_dt_project` (AY's spelling, `__trust_*`), `ok_dt_project_symm` and
//! `ok_dt_project_mutual` must verify, and AY 0.27.0 (build 11536, fce0a8fae) reports `unsat`
//! for each (its own proofs still use `hole` for the step). The `dt_u*` problems are satisfiable,
//! or ill-formed and satisfiable under one of their readings, so each must be refused:
//!
//! - `dt_u1`..`dt_u4` at the `dt_project` step. They use another constructor's selector (both
//!   ways), an uninterpreted function and the other field, and AY 0.27.0 reports `sat` for each.
//! - `dt_u5`/`dt_u6` at the step inside the anchor that rebinds the selector or constructor name.
//!   Take `snd` constantly `b + 1`, or `mk` building `(mk x (+ y 1))`. AY does not parse
//!   function-sorted binders ("unsupported: parameterized sort: ->").
//! - `dt_u7`..`dt_u11` at parse time. They give a datatype symbol or sort a second meaning: a
//!   selector or constructor redeclared with its own sort (`dt_u7`, `dt_u8`), a second datatype
//!   whose constructor has the same argument sorts (`dt_u9`, satisfiable when `fst` and `mk` are
//!   `P`'s), a datatype named like a declared sort over which `snd` was already declared (`dt_u10`,
//!   satisfiable when `snd` is that function), and a `define-fun` named like a constructor
//!   (`dt_u11`, satisfiable when `mk` is the constructor). AY 0.27.0 refuses each of them too
//!   ("would conflate the user symbol with the builtin datatype operation", "ambiguous
//!   overloaded symbol", "sort 'P' is already declared").
//! - `dt_u12`..`dt_u17` at parse time. A parametric datatype `L` declares a constructor named
//!   like `P`'s selector `snd` (or constructor `mk`) with another arity, which the datatype guard
//!   allows, and the problem qualifies it as `(as snd (-> P Int))`, a sort that is not an
//!   instance of its own. Upstream built that term at any sort, so it was `P`'s selector and
//!   `dt_project` accepted the step. Read as a free symbol, as Carcara reads `(as snd Int)`, each
//!   problem is satisfiable: take `(as snd (-> P Int))` constantly `b + 1`, or `(as mk (-> Int Int
//!   P))` building `(mk y x)` with `a != b`. They cover a problem `define-fun` (`dt_u12`), the
//!   constructor (`dt_u13`), an equation (`dt_u14`), a binary constructor (`dt_u15`), one
//!   `declare-datatypes` block (`dt_u16`) and a sort that matches component by component only up
//!   to the shorter length (`dt_u17`, which needs the length check in `Sort::match_with`). AY
//!   0.27.0 reports `unknown` for each, as it does not parse a function symbol used as a value
//!   ("function 'g' requires arguments", "unknown constant f", "-> requires 2 type parameters").
//!
//! With the rule's anchor check or the parser's guard disabled, `dt_u5` and `dt_u7` verify
//! completely, and so does each of `dt_u12`..`dt_u17` without the `as` check.
//!
//! The `pr_` pairs are refutations of problems the parser read with premises other than the
//! script's (fixes 36 to 38 and 40), or (fix 39) through an axiom producers read differently,
//! and Clean's copy before those fixes verified every `pr_u*` one completely. `pr_u1`..`pr_u6`
//! are the adversarial review's B03, B04, B06, B07, B10 and B11 (a `define-fun` parameter
//! captured a global that a macro in its body mentions), `pr_u7`..`pr_u9` its B08, B09 and Z01
//! (`reset-assertions`, `check-sat-assuming`, `push`/`pop`). `pr_u10`..`pr_u18` were found while
//! fixing them: a binder that rebinds a macro's name or a name its definition mentions
//! (`pr_u10`..`pr_u13`), and assertions after the query or around a scoping command
//! (`pr_u14`..`pr_u18`). `pr_u19`..`pr_u30` are the second review's T6, T7, T9, T8, S6, S1, R1,
//! R1b, R5, R13, R10 and U1: a binder or sort parameter named like a built-in operator or sort, a
//! name declared or defined twice (fix 38), and AY's `check-sat-using` (fix 37).
//! `pr_u31`..`pr_u33` are the third review's R01, R03 and their `define-funs-rec` form, an
//! inconsistent recursive definition refuted through the SMT-LIB axiom (fix 39).
//! `pr_u34`..`pr_u38` were built on its note that the lexers differ: L01 (a comment ended by CR)
//! and four scripts the lexer read with numbers where SMT-LIB reads a declared symbol (`-5` with
//! `|-5|`, `1/2` with `/2`, `1.` with `.`, `-5abc` with `|-5abc|`; fix 40).
//!
//! Under SMT-LIB's reading every `pr_u*` problem is satisfiable except `pr_u31`..`pr_u33`, whose
//! axioms are inconsistent. AY 0.27.0 (build 11536, fce0a8fae) reports `sat` for `pr_u1`,
//! `pr_u7`, `pr_u9`, `pr_u10`, `pr_u11`, `pr_u13`, `pr_u15`, `pr_u17`, `pr_u18`,
//! `pr_u19`..`pr_u21`, `pr_u23`, `pr_u25`..`pr_u28` and `pr_u31`..`pr_u38`, `sat sat` for
//! `pr_u8`, `sat unsat` for `pr_u14` and `pr_u30` (two queries, neither of which the proof
//! refutes), `unknown` for `pr_u22`, and nothing for `pr_u16` (it stops at `exit`). It does not
//! parse a function symbol used as a value (`pr_u2`, `pr_u5`, `pr_u6`: take `g` at `(mk a b)` to
//! differ from the other side of the equation) or a `:named` label used as a term (`pr_u3`,
//! `pr_u4`, `pr_u12`: take `x = 0`), and refuses `pr_u24` (a sort parameter named `Bool`) and
//! `pr_u29` (a constant declared twice). Its `sat` for `pr_u31`..`pr_u33` is its lazy reading of
//! `define-fun-rec`: it reports `unsat` for `ok_pr_recursive_axiom_written_out`, R01's axiom
//! written out, and the refusal settles the disagreement by certifying neither reading. Each
//! `pr_u*` is now refused: the problems read with the right premises at a step, the others at
//! parse time. The `ok_pr_` pairs are sound refutations of the same shapes read correctly
//! (`ok_pr_quoted_numeric_name` declares and uses `|-1|` quoted throughout, as AY's printer
//! writes such a name). AY reports `unsat` for each except `ok_pr_named_label` and
//! `ok_pr_fresh_label` (a label used as a term), and each must verify.
//!
//! The two fixtures whose problem holds a CR (`pr_u34_cr_ends_comment` and
//! `ok_pr_comment_ended_by_cr`) are written inline, so no checkout or editor can rewrite it.
//!
//! Origin, license and the full list of local changes: `third-party/carcara/DOWNSTREAM.md`.

use super::verify_alethe_proof;

macro_rules! pair {
    ($name:literal) => {
        (
            $name,
            include_str!(concat!("soundness/", $name, ".smt2")),
            include_str!(concat!("soundness/", $name, ".alethe")),
        )
    };
}

/// (fixture, rejected step, rule)
const REFUTATIONS_OF_SATISFIABLE_PROBLEMS: [(&str, &str, &str, &str, &str); 51] = [
    with_step(pair!("aci_u1_int_add_dup"), "s", "aci_simp"),
    with_step(pair!("aci_u2_bvxor_dup"), "s", "aci_simp"),
    with_step(pair!("aci_u3_bvadd_dup"), "s", "aci_simp"),
    with_step(pair!("aci_u4_int_mul_dup"), "s", "aci_simp"),
    with_step(pair!("be_u3_partial_capture"), "s", "beta_equiv"),
    with_step(pair!("ctx_u1_onepoint_export"), "s", "onepoint"),
    with_step(pair!("ctx_u2_premise_crosses_anchor"), "s.t1", "cong"),
    with_step(pair!("bf_u3_real_strengthening"), "s", "bounded_farkas"),
    with_step(pair!("lg_u1_real_strengthening"), "s", "la_generic"),
    with_step(pair!("ev_u1_bvslt"), "e1", "evaluate"),
    with_step(pair!("ev_u2_bvsub"), "e1", "evaluate"),
    with_step(pair!("ev_u3_sign_extend"), "e1", "evaluate"),
    with_step(pair!("ev_u4_bvsmod"), "e1", "evaluate"),
    with_step(pair!("ext_u4_capture_reported"), "s", "arrays_ext"),
    with_step(pair!("ext_u5_capture_uf"), "s", "arrays_ext"),
    with_step(pair!("udiv_w2_2_1"), "e4", "bitblast_udiv"),
    with_step(pair!("urem_w2_1_1"), "e4", "bitblast_urem"),
    // Alpha-equivalence: binder lists of different lengths, and `let` values read in the
    // binder's own scope instead of the enclosing one
    with_step(pair!("ae_u1_refl_forall_extra_binder"), "s", "refl"),
    with_step(pair!("ae_u2_refl_let_extra_binding"), "s", "refl"),
    with_step(pair!("ae_u3_refl_exists_extra_binder"), "s", "refl"),
    with_step(pair!("ae_u4_refl_let_value_outer_scope"), "s", "refl"),
    // An equality found for a `let` value was cached in the `let`'s own scope and reused in the
    // body after the `let` had rebound one of its names
    with_step(pair!("ae_u5_refl_let_value_cache_outer_let"), "s", "refl"),
    with_step(pair!("ae_u6_refl_let_value_cache_forall"), "s", "refl"),
    with_step(pair!("ae_u7_refl_let_value_cache_exists"), "s", "refl"),
    with_step(
        pair!("ae_u8_refl_let_value_cache_three_bindings"),
        "s",
        "refl",
    ),
    // Capture-avoiding substitution: the `_renamed` name collided with a free variable, and the
    // substitution never reached a `let` value
    with_step(
        pair!("sub_u1_forall_inst_rename_capture"),
        "s",
        "forall_inst",
    ),
    with_step(pair!("sub_u2_beta_equiv_rename_capture"), "s", "beta_equiv"),
    with_step(pair!("sub_u3_bind_refl_rename_capture"), "s.t1", "refl"),
    with_step(pair!("sub_u4_forall_inst_let_value"), "s", "forall_inst"),
    with_step(pair!("sub_u5_beta_equiv_let_value"), "s", "beta_equiv"),
    with_step(pair!("sub_u6_bfun_elim_let_value"), "s", "bfun_elim"),
    // `onepoint` read points from under binders that rebind the eliminated variable, or that
    // bind a variable of the point's term
    with_step(pair!("op_u2_point_under_rebinding"), "s", "onepoint"),
    with_step(pair!("op_u3_point_mentions_bound"), "s", "onepoint"),
    with_step(pair!("op_u4_exists_and_rebinding"), "s", "onepoint"),
    // `string_decompose` split at a negative or unbounded point
    with_step(pair!("sd_u1_negative_forward"), "s", "string_decompose"),
    with_step(pair!("sd_u2_negative_reverse"), "s", "string_decompose"),
    with_step(pair!("sd_u3_symbolic_split"), "s", "string_decompose"),
    // `evaluate` read `(_ bv<n> <w>)` as `n` instead of `n mod 2^w`
    with_step(pair!("ev_u5_bv_literal_out_of_range"), "s", "evaluate"),
    with_step(pair!("ev_u6_bv_literal_bvult"), "s", "evaluate"),
    // `evaluate` cast bit-vector widths to `u32`, reading `2^32 + k` as `k`
    with_step(pair!("ev_u7_sign_extend_width_2p32"), "s", "evaluate"),
    with_step(pair!("ev_u8_bvadd_width_2p32_plus1"), "s", "evaluate"),
    // Regular expressions: an undetermined Skolem witness, and a captured length variable
    with_step(
        pair!("re_u1_concat_unfold_pos_witness"),
        "s",
        "re_concat_unfold_pos",
    ),
    with_step(
        pair!("re_u2_kleene_star_unfold_pos_witness"),
        "s",
        "re_kleene_star_unfold_pos",
    ),
    with_step(
        pair!("re_u3_unfold_neg_concat_capture"),
        "s",
        "re_unfold_neg",
    ),
    with_step(pair!("re_u4_unfold_neg_star_capture"), "s", "re_unfold_neg"),
    // `dt_project` (C2): only the selector of the constructor, projecting its own field
    with_step(pair!("dt_u1_other_constructor_selector"), "s", "dt_project"),
    with_step(pair!("dt_u2_mk_selector_on_other"), "s", "dt_project"),
    with_step(pair!("dt_u3_uninterpreted_function"), "s", "dt_project"),
    with_step(pair!("dt_u4_other_field"), "s", "dt_project"),
    // ... and never a variable that an anchor binds under the selector's or constructor's name
    with_step(pair!("dt_u5_anchor_rebinds_selector"), "s.t1", "dt_project"),
    with_step(
        pair!("dt_u6_anchor_rebinds_constructor"),
        "s.t1",
        "dt_project",
    ),
];

/// Problems that give a datatype symbol or sort a second meaning, each satisfiable under the
/// reading in which the symbol is not the datatype's own; refused when parsed, before any rule
/// runs. `dt_u11` and `dt_u12` are refused in both `define-fun` modes (the adapter retries a
/// problem with `define-fun` as macros when the first parse fails).
const AMBIGUOUS_DATATYPE_SYMBOLS: [(&str, &str, &str); 11] = [
    pair!("dt_u7_redeclared_selector"),
    pair!("dt_u8_redeclared_constructor"),
    pair!("dt_u9_twin_datatypes_overloaded_constructor"),
    pair!("dt_u10_declared_sort_then_datatype"),
    pair!("dt_u11_define_fun_named_like_constructor"),
    // A parametric symbol qualified with `as` at a sort that is not an instance of its own
    pair!("dt_u12_par_as_selector_problem_macro"),
    pair!("dt_u13_par_as_constructor"),
    pair!("dt_u14_par_as_selector_equation"),
    pair!("dt_u15_par_binary_constructor_as_selector"),
    pair!("dt_u16_par_as_selector_datatypes_block"),
    pair!("dt_u17_par_as_truncated_sort_match"),
];

/// Problems read with premises other than the script's before fixes 36 to 38 and 40, or (fix 39)
/// through an axiom producers read differently: (fixture, the refusal the diagnostic must name). A
/// `define-fun`, shadowing or lexing case is now read with the right premises, so its refutation
/// fails at a step; the others are refused at parse time, saying why.
const MISREAD_PROBLEMS: [(&str, &str, &str, &str); 38] = [
    with_reason(
        pair!("pr_u1_define_fun_capture"),
        "with define-fun expanded as macros: checking failed on step 't1' with rule 'symm'",
    ),
    with_reason(
        pair!("pr_u2_define_fun_capture_selector"),
        "with define-fun expanded as macros: checking failed on step 't2' with rule 'resolution'",
    ),
    with_reason(
        pair!("pr_u3_named_capture"),
        "with define-fun expanded as macros: checking failed on step 't1' with rule 'symm'",
    ),
    with_reason(
        pair!("pr_u4_named_capture_lambda"),
        "step 'd0' with rule 'assume'",
    ),
    with_reason(
        pair!("pr_u5_capture_into_dt_project"),
        "with define-fun expanded as macros: checking failed on step 't2' with rule 'resolution'",
    ),
    with_reason(
        pair!("pr_u6_capture_uninterpreted"),
        "with define-fun expanded as macros: checking failed on step 't2' with rule 'resolution'",
    ),
    with_reason(
        pair!("pr_u7_reset_assertions"),
        "'reset-assertions' is not supported",
    ),
    with_reason(
        pair!("pr_u8_check_sat_assuming_then_assert"),
        "'assert' after 'check-sat-assuming'",
    ),
    with_reason(pair!("pr_u9_push_pop"), "'push' is not supported"),
    with_reason(
        pair!("pr_u10_binder_shadows_define_fun"),
        "with define-fun expanded as macros: checking failed on step 't1' with rule \
         'qnt_rm_unused'",
    ),
    with_reason(
        pair!("pr_u11_binder_shadows_named"),
        "step 't1' with rule 'qnt_rm_unused'",
    ),
    with_reason(
        pair!("pr_u12_binder_captures_named"),
        "'k' is used where a binder rebinds 'x'",
    ),
    with_reason(
        pair!("pr_u13_binder_captures_define_fun"),
        "with define-fun expanded as macros: parser error on line 3, column 34: 'k' is used where \
         a binder rebinds 'x'",
    ),
    with_reason(pair!("pr_u14_two_check_sats"), "'assert' after 'check-sat'"),
    with_reason(
        pair!("pr_u15_assert_after_check_sat"),
        "'assert' after 'check-sat'",
    ),
    with_reason(pair!("pr_u16_assert_after_exit"), "'assert' after 'exit'"),
    with_reason(pair!("pr_u17_pop"), "'push' is not supported"),
    with_reason(pair!("pr_u18_reset"), "'reset' is not supported"),
    with_reason(
        pair!("pr_u19_parameter_named_like_operator"),
        "with define-fun expanded as macros: checking failed on step 't1' with rule 'resolution'",
    ),
    with_reason(
        pair!("pr_u20_parameter_named_like_real_pi"),
        "with define-fun expanded as macros: checking failed on step 't1' with rule 'resolution'",
    ),
    with_reason(
        pair!("pr_u21_let_named_like_operator"),
        "step 't3' with rule 'let'",
    ),
    with_reason(
        pair!("pr_u22_quantifier_named_like_operator"),
        "step 't1' with rule 'qnt_rm_unused'",
    ),
    with_reason(
        pair!("pr_u23_sort_parameter_named_like_bool"),
        "step 't1' with rule 'distinct_elim'",
    ),
    with_reason(
        pair!("pr_u24_define_sort_parameter_named_like_bool"),
        "step 't1' with rule 'distinct_elim'",
    ),
    with_reason(
        pair!("pr_u25_label_reuses_constant"),
        "'x' is already declared or defined",
    ),
    with_reason(
        pair!("pr_u26_label_before_constant"),
        "'x' is already declared or defined",
    ),
    with_reason(
        pair!("pr_u27_label_named_true"),
        "'true' is a built-in operator",
    ),
    with_reason(
        pair!("pr_u28_label_named_false"),
        "'false' is a built-in operator",
    ),
    with_reason(
        pair!("pr_u29_constant_declared_twice"),
        "'x' is already declared or defined",
    ),
    with_reason(
        pair!("pr_u30_check_sat_using"),
        "'check-sat-using' is not a command this checker reads",
    ),
    // Recursive definitions (fix 39)
    with_reason(
        pair!("pr_u31_recursive_definition_inconsistent"),
        "'define-fun-rec' is not supported: a recursive definition",
    ),
    with_reason(
        pair!("pr_u32_recursive_constant"),
        "'define-fun-rec' is not supported: a recursive definition",
    ),
    with_reason(
        pair!("pr_u33_recursive_definition_group"),
        "'define-funs-rec' is not supported: a recursive definition",
    ),
    // The lexicon (fix 40)
    (
        "pr_u34_cr_ends_comment",
        "(set-logic QF_UF)\n(declare-const a Bool)\n(declare-const b Bool)\n\
         (assert (or a ; c\r b)) (assert (or b\n a))\n(assert (not a))\n(check-sat)\n",
        "(assume h1 (or a a))\n(assume h2 (not a))\n(step t1 (cl a a) :rule or :premises (h1))\n\
         (step t2 (cl a) :rule contraction :premises (t1))\n\
         (step t3 (cl) :rule resolution :premises (t2 h2))\n",
        "checking failed on step 'h1' with rule 'assume'",
    ),
    with_reason(
        pair!("pr_u35_quoted_negative_numeral_symbol"),
        "'-5' is a declared or bound symbol, which this checker would read here as a number",
    ),
    with_reason(
        pair!("pr_u36_rational_splits_off_symbol"),
        "'/2' is a declared or bound symbol, which this checker would read here as a number",
    ),
    with_reason(
        pair!("pr_u37_decimal_point_symbol"),
        "checking failed on step 'a0' with rule 'assume'",
    ),
    with_reason(
        pair!("pr_u38_negative_numeral_prefix_symbol"),
        "'-5abc' is a declared or bound symbol, which this checker would read here as a number",
    ),
];

const fn with_reason(
    (name, problem, proof): (&'static str, &'static str, &'static str),
    reason: &'static str,
) -> (&'static str, &'static str, &'static str, &'static str) {
    (name, problem, proof, reason)
}

const fn with_step(
    (name, problem, proof): (&'static str, &'static str, &'static str),
    step: &'static str,
    rule: &'static str,
) -> (
    &'static str,
    &'static str,
    &'static str,
    &'static str,
    &'static str,
) {
    (name, problem, proof, step, rule)
}

const SOUND_REFUTATIONS: [(&str, &str, &str); 40] = [
    pair!("ok_aci_simp"),
    pair!("ok_aci_simp_bvxor"),
    pair!("ok_beta_equiv"),
    pair!("ok_la_generic_integer"),
    pair!("ok_bounded_farkas_integer"),
    pair!("ok_evaluate_bvslt"),
    pair!("ok_arrays_ext_fresh_witness"),
    pair!("ok_bind"),
    pair!("ok_onepoint"),
    pair!("ok_udiv"),
    pair!("ok_urem"),
    pair!("ok_ae_refl_alpha"),
    pair!("ok_ae_refl_let_parallel"),
    pair!("ok_sub_forall_inst_rename"),
    pair!("ok_sub_forall_inst_let_value"),
    pair!("ok_op_nested_binder"),
    pair!("ok_sd_nonnegative"),
    pair!("ok_ev_bv_literal"),
    pair!("ok_re_unfold_neg"),
    pair!("ok_re_concat_unfold_pos"),
    pair!("ok_ae_refl_let_value_nested"),
    pair!("ok_ev_wide_zero_extend"),
    pair!("ok_and_simplify_nested_result"),
    pair!("ok_or_simplify_nested_result"),
    pair!("ok_dt_project"),
    pair!("ok_dt_project_symm"),
    pair!("ok_dt_project_mutual"),
    // Problem reading (fixes 36 and 37)
    pair!("ok_pr_hygienic_define_fun"),
    pair!("ok_pr_define_fun_lambda"),
    pair!("ok_pr_named_label"),
    pair!("ok_pr_binder_shadows_define_fun"),
    pair!("ok_pr_check_sat_assuming"),
    pair!("ok_pr_commands_after_check_sat"),
    // Names (fix 38)
    pair!("ok_pr_parameter_named_like_operator"),
    pair!("ok_pr_sort_parameter_named_like_bool"),
    pair!("ok_pr_fresh_label"),
    // Recursive definitions and the lexicon (fixes 39 and 40)
    pair!("ok_pr_recursive_axiom_written_out"),
    pair!("ok_pr_numerals_in_problem"),
    pair!("ok_pr_quoted_numeric_name"),
    (
        "ok_pr_comment_ended_by_cr",
        "(set-logic QF_UF)\n(declare-const a Bool)\n(assert (not a)) ; c\r(assert a)\n\
         (check-sat)\n",
        "(assume h1 a)\n(assume h2 (not a))\n(step t1 (cl) :rule resolution :premises (h1 h2))\n",
    ),
];

#[test]
fn refutations_of_satisfiable_problems_are_rejected_at_the_unsound_step() {
    for (name, problem, proof, step, rule) in REFUTATIONS_OF_SATISFIABLE_PROBLEMS {
        let diagnostic = match verify_alethe_proof(problem, proof) {
            Err(error) => error.to_string(),
            Ok(valid) => {
                panic!("{name}: a refutation of a satisfiable problem returned Ok({valid})")
            }
        };
        assert!(
            diagnostic.contains(&format!("step '{step}' with rule '{rule}'")),
            "{name}: expected rejection at step '{step}' ({rule}), got: {diagnostic}"
        );
    }
}

#[test]
fn sound_refutations_with_the_corrected_rules_verify() {
    for (name, problem, proof) in SOUND_REFUTATIONS {
        match verify_alethe_proof(problem, proof) {
            Ok(true) => {}
            other => panic!("{name}: a complete sound refutation must verify, got {other:?}"),
        }
    }
}

#[test]
fn ambiguous_datatype_symbols_are_refused_by_the_parser() {
    for (name, problem, proof) in AMBIGUOUS_DATATYPE_SYMBOLS {
        let diagnostic = match verify_alethe_proof(problem, proof) {
            Err(error) => error.to_string(),
            Ok(valid) => {
                panic!("{name}: a refutation of a satisfiable problem returned Ok({valid})")
            }
        };
        assert!(
            diagnostic.contains("parser error"),
            "{name}: expected a parser refusal, got: {diagnostic}"
        );
    }
}

#[test]
fn misread_problems_are_read_correctly_or_refused() {
    for (name, problem, proof, reason) in MISREAD_PROBLEMS {
        let diagnostic = match verify_alethe_proof(problem, proof) {
            Err(error) => error.to_string(),
            Ok(valid) => {
                panic!("{name}: a refutation of a satisfiable problem returned Ok({valid})")
            }
        };
        assert!(
            diagnostic.contains(reason),
            "{name}: expected {reason:?}, got: {diagnostic}"
        );
    }
}

/// When both `define-fun` readings fail, the macro reading's refusal is reported too. Here the
/// ordinary reading fails at the assumption (it only matches with `q` expanded) and the macro
/// reading at the `dt_project` step (the other field); only the second names the real defect.
#[test]
fn both_define_fun_readings_are_reported_when_both_fail() {
    let problem = "(set-logic QF_UFDTLIA)
        (declare-datatype P ((mk (fst Int) (snd Int)) (other (oth Int))))
        (declare-const a Int)
        (declare-const b Int)
        (define-fun q () P (mk a b))
        (assert (not (= (snd q) a)))";
    let proof = "(assume h (not (= (snd (mk a b)) a)))
        (step s (cl (= (snd (mk a b)) a)) :rule dt_project)
        (step t (cl) :rule resolution :premises (h s))";
    let diagnostic = match verify_alethe_proof(problem, proof) {
        Err(error) => error.to_string(),
        Ok(valid) => panic!("a refutation of a satisfiable problem returned Ok({valid})"),
    };
    assert!(
        diagnostic.contains("step 'h'")
            && diagnostic.contains(
                "with define-fun expanded as macros: checking failed on step 's' with rule \
                 'dt_project'"
            ),
        "expected both readings' refusals, got: {diagnostic}"
    );
}
