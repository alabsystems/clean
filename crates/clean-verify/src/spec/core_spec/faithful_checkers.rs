// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Front #1 Stage 3/4 (the_red_env discharge program): the FAITHFUL-INTERFACE
//! CHECKERS — Bool folds + generic checker-soundness lemmas for the four
//! remaining `RedEnvFaithful` interfaces (i1 `RecEnvReductNotRedex`, i2
//! `RecEnvCtorNoRecMeta`, i7 `RecEnvDefEnvDisjoint`, i8 `RecEnvCtorNoDefVal`),
//! completing the one-rfl discharge tooling the closedness tier (i3..i6,
//! `env_closed_checkers_depth.rs`) already has. Ported from the
//! Aristotle-farmed zero-import Lean development
//! (`/tmp/ari-fchk/project_aristotle/FaithfulCheckers.lean`); every proof here
//! is an explicit kernel term in the Stage-1 fold-membership shape.
//!
//! ## The checker designs (mirroring `env_closed_checkers.rs`)
//!
//! - i1 `rec_env_rnr_b`: per-rule test — the rule rhs's HEAD is not a const
//!   (`opt_isnone (kexpr_const_name (kapp_fn (recrule_rhs r)))`). A DOCUMENTED
//!   SUFFICIENT condition (not necessary): the interface quantifies over all
//!   fired redexes; the reduct is a triple `apply_spine` around
//!   `recrule_rhs rule`, whose `kapp_fn` equals `kapp_fn (recrule_rhs rule)`
//!   (`kapp_fn_apply_spine` — apply_spine only adds app nodes), so a non-const
//!   rhs head makes `iota_reduct` short-circuit on the reduct at its very
//!   first `opt_bind`. The reflected real env has 36/36 rule RHSs lam-headed,
//!   so it passes.
//! - i2 `rec_env_ctor_no_recmeta_b env := rec_env_no_recmeta_go_b env env`:
//!   fold over the env's rule lists with the FULL env carried as the lookup
//!   context; per-rule test `opt_isnone (recmeta_for env0 (recrule_ctor_name r))`.
//! - i7 `red_env_disjoint_b`: fold over the DefEnv entries; per-entry test
//!   `opt_isnone (recmeta_for renv dname)`.
//! - i8 `red_env_ctor_no_defval_b`: i2's fold with the per-rule test swapped
//!   to `opt_isnone (defval_for denv (recrule_ctor_name r))`.
//!
//! ## Soundness shape
//!
//! The Stage-1 fold-membership pattern: induct on the env / rules list; the
//! `nil`/`empty` lookup is absurd (`option_none_ne_some`); the cons/addRec/
//! addDef step splits the `opt_pick` lookup on its Bool guard
//! (`opt_pick_some_inv`) — fire returns the head element, fall-through feeds
//! the IH — and `band_eq_true_left/right` split the checker conjunction.
//! KEY DIFFERENCE from the closedness tier: for i2/i7/i8 the per-element fact
//! is keyed on the STORED name while the interface conclusion is keyed on the
//! LOOKED-UP name, so the fire branch transports along decidable-equality
//! soundness (`name_eqb_eq`). For i1 additionally: invert the fired redex
//! (`iota_reduct_some_inv`), rewrite the reduct head through the three
//! `apply_spine` layers (`kapp_fn_apply_spine`), and short-circuit
//! (`iota_reduct_head_none`) — the generic-env form of the
//! `faithful_red_env_reduct_not_redex` term (faithful_red_env.rs R3).
//!
//! ## THE DISCHARGE (`add_the_red_env_faithful_discharge`)
//!
//! With the Stage-3 swap in place (`the_red_env := kernel_core_red_env`, the
//! fidelity-gated reflection of the real kernel foundation core), ALL EIGHT
//! faithful interfaces are discharged over `the_red_env` by the single-rfl
//! route — i3..i6 via the depth-aware `*_of_b2` closedness lemmas, i1/i2/i7/i8
//! via the checkers here — and assembled into
//! `the_red_env_faithful : RedEnvFaithful the_red_env` via `RedEnvFaithful.mk`.
//! This is the discharge moment for the carried-hypothesis track: an HONEST
//! `DerivedProved` witness of the full bundle over the metatheory's REAL
//! distinguished environment. The ~79 carried-hypothesis metatheory decls are
//! untouched (still parametric); instantiating them is follow-up work.
//!
//! ## Anti-masquerade
//!
//! ZERO new axioms (census stays 11). The checkers are value-ful recursive
//! defs; every lemma/witness is a real `DerivedProved` term with empty
//! axiom_deps, registered on the fully checked path.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// A `DerivedProved`, zero-axiom-dep `SpecDefinition` (local mirror of the
    /// Stage-1 `ecc_lemma` helper, which is private to `env_closed_checkers.rs`).
    fn fchk_lemma(
        name: &str,
        type_src: &str,
        value_src: &str,
        description: &str,
        deps: &[&str],
    ) -> SpecDefinition {
        SpecDefinition {
            name: name.to_string(),
            type_src: type_src.to_string(),
            value_src: Some(value_src.to_string()),
            is_axiom: false,
            description: description.to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(deps.iter().map(|s| (*s).to_string()).collect()),
            axiom_deps: HashSet::new(),
        }
    }

    /// Register the faithful-interface checkers (i1/i2/i7/i8), their
    /// fold-membership soundness, the generic `*_of_b` interface discharge,
    /// and the faithful_red_env regression probes.
    pub(super) fn add_faithful_checkers(&mut self) -> Result<(), SpecError> {
        self.add_faithful_checker_defs()?;
        self.add_faithful_checker_i1_soundness()?;
        self.add_faithful_checker_i2_soundness()?;
        self.add_faithful_checker_i7_soundness()?;
        self.add_faithful_checker_i8_soundness()?;
        self.add_faithful_checker_demo()?;
        Ok(())
    }

    /// The Bool helper + the ten checker folds. `opt_isnone` and the
    /// env0-carrying folds use the explicit-recursor registration style
    /// (`opt_bind` / `nat_lt_b` precedent); the single-argument i1 folds use
    /// the Stage-1 match style.
    fn add_faithful_checker_defs(&mut self) -> Result<(), SpecError> {
        // opt_isnone: Bool "is none" test on OptionType (no in-tree twin).
        self.add_recursive_def(
            r"def opt_isnone (alpha : Type) (o : OptionType alpha) : Bool := OptionType.rec alpha (fun (_ : OptionType alpha) => Bool) Bool.true (fun (_ : alpha) => Bool.false) o",
            "Bool none-test on OptionType: true iff the option is none. The per-element test of \
             the faithful-interface checkers (i1/i2/i7/i8). Kernel-evaluable. Front #1 Stage 3/4 \
             (faithful checkers).",
        )?;

        // opt_isnone_eq_none: a true verdict pins the option to none.
        self.add_definition(Self::fchk_lemma(
            "opt_isnone_eq_none",
            "forall (alpha : Type) (o : OptionType alpha), \
             Eq Bool (opt_isnone alpha o) Bool.true -> Eq (OptionType alpha) o (OptionType.none alpha)",
            "fun (alpha : Type) (o : OptionType alpha) => \
             OptionType.rec alpha \
             (fun (z : OptionType alpha) => \
             Eq Bool (opt_isnone alpha z) Bool.true -> Eq (OptionType alpha) z (OptionType.none alpha)) \
             (fun (_ : Eq Bool (opt_isnone alpha (OptionType.none alpha)) Bool.true) => \
             Eq.refl (OptionType alpha) (OptionType.none alpha)) \
             (fun (a : alpha) (h : Eq Bool (opt_isnone alpha (OptionType.some alpha a)) Bool.true) => \
             bool_false_ne_true (Eq (OptionType alpha) (OptionType.some alpha a) (OptionType.none alpha)) h) \
             o",
            "opt_isnone inversion: opt_isnone o = true -> o = none. OptionType.rec; the some arm \
             is absurd (the checker whnf-evaluates to false; bool_false_ne_true). DerivedProved, \
             zero axiom_deps. Front #1 Stage 3/4 (faithful checkers).",
            &["OptionType.rec", "opt_isnone", "bool_false_ne_true", "Eq.refl"],
        ))?;

        // i1 folds (match style, mirrors the Stage-1 checkers).
        self.add_recursive_def(
            r"def rec_rules_rnr_b (rs : RecRules) : Bool := match rs with
| RecRules.nil => Bool.true
| RecRules.cons r rest => Bool.and (opt_isnone Name (kexpr_const_name (kapp_fn (recrule_rhs r)))) (rec_rules_rnr_b rest)",
            "i1 checker (rules leg): every rule rhs has a NON-CONST head (kexpr_const_name \
             (kapp_fn rhs) = none) — the head shape on which iota_reduct short-circuits, so a \
             fired reduct is never itself a top redex. SUFFICIENT (not necessary) for \
             RecEnvReductNotRedex. Kernel-evaluable fold. Front #1 Stage 3/4 (faithful checkers).",
        )?;

        self.add_recursive_def(
            r"def rec_env_rnr_b (env : RecEnv) : Bool := match env with
| RecEnv.empty => Bool.true
| RecEnv.addRec tail rname mta rules => Bool.and (rec_rules_rnr_b rules) (rec_env_rnr_b tail)",
            "i1 checker: every recursor's rule list passes rec_rules_rnr_b (all rule rhs heads \
             non-const). A concrete env discharges RecEnvReductNotRedex by \
             rec_env_reduct_not_redex_of_b + a single Eq.refl Bool.true. Front #1 Stage 3/4 \
             (faithful checkers).",
        )?;

        // i2 folds (env0-carrying; explicit recursor style, nat_lt_b precedent).
        self.add_recursive_def(
            r"def rec_rules_no_recmeta_b (env0 : RecEnv) (rs : RecRules) : Bool := RecRules.rec (fun (_ : RecRules) => Bool) Bool.true (fun (r : RecRule) (rest : RecRules) (ih : Bool) => Bool.and (opt_isnone RecMeta (recmeta_for env0 (recrule_ctor_name r))) ih) rs",
            "i2 checker (rules leg, lookup context env0 carried): every rule's constructor name \
             carries no recursor metadata in env0. Kernel-evaluable fold (explicit RecRules.rec). \
             Front #1 Stage 3/4 (faithful checkers).",
        )?;

        self.add_recursive_def(
            r"def rec_env_no_recmeta_go_b (env0 : RecEnv) (env : RecEnv) : Bool := RecEnv.rec (fun (_ : RecEnv) => Bool) Bool.true (fun (tail : RecEnv) (rname : Name) (mta : RecMeta) (rules : RecRules) (ih : Bool) => Bool.and (rec_rules_no_recmeta_b env0 rules) ih) env",
            "i2 checker (env leg): every registered rule list passes rec_rules_no_recmeta_b, with \
             the lookup context env0 fixed. Front #1 Stage 3/4 (faithful checkers).",
        )?;

        self.add_recursive_def(
            r"def rec_env_ctor_no_recmeta_b (env : RecEnv) : Bool := rec_env_no_recmeta_go_b env env",
            "i2 checker: constructor names vs recursor names disjoint (the env is its own lookup \
             context). A concrete env discharges RecEnvCtorNoRecMeta by \
             rec_env_ctor_no_recmeta_of_b + a single Eq.refl Bool.true. Front #1 Stage 3/4 \
             (faithful checkers).",
        )?;

        // i7 fold (RecEnv lookup context carried).
        self.add_recursive_def(
            r"def def_env_no_recmeta_b (renv : RecEnv) (denv : DefEnv) : Bool := DefEnv.rec (fun (_ : DefEnv) => Bool) Bool.true (fun (tail : DefEnv) (dname : Name) (val : KExpr) (ih : Bool) => Bool.and (opt_isnone RecMeta (recmeta_for renv dname)) ih) denv",
            "i7 checker (def-env leg, RecEnv lookup context carried): every defined name carries \
             no recursor metadata. Front #1 Stage 3/4 (faithful checkers).",
        )?;

        self.add_recursive_def(
            r"def red_env_disjoint_b (env : RedEnv) : Bool := def_env_no_recmeta_b (red_rec env) (red_def env)",
            "i7 checker: definition names vs recursor names disjoint. A concrete env discharges \
             RecEnvDefEnvDisjoint by red_env_disjoint_of_b + a single Eq.refl Bool.true. Front #1 \
             Stage 3/4 (faithful checkers).",
        )?;

        // i8 folds (DefEnv lookup context carried).
        self.add_recursive_def(
            r"def rec_rules_no_defval_b (denv : DefEnv) (rs : RecRules) : Bool := RecRules.rec (fun (_ : RecRules) => Bool) Bool.true (fun (r : RecRule) (rest : RecRules) (ih : Bool) => Bool.and (opt_isnone KExpr (defval_for denv (recrule_ctor_name r))) ih) rs",
            "i8 checker (rules leg, DefEnv lookup context carried): every rule's constructor name \
             carries no def value. Front #1 Stage 3/4 (faithful checkers).",
        )?;

        self.add_recursive_def(
            r"def rec_env_no_defval_go_b (denv : DefEnv) (env : RecEnv) : Bool := RecEnv.rec (fun (_ : RecEnv) => Bool) Bool.true (fun (tail : RecEnv) (rname : Name) (mta : RecMeta) (rules : RecRules) (ih : Bool) => Bool.and (rec_rules_no_defval_b denv rules) ih) env",
            "i8 checker (env leg): every registered rule list passes rec_rules_no_defval_b, with \
             the DefEnv lookup context fixed. Front #1 Stage 3/4 (faithful checkers).",
        )?;

        self.add_recursive_def(
            r"def red_env_ctor_no_defval_b (env : RedEnv) : Bool := rec_env_no_defval_go_b (red_def env) (red_rec env)",
            "i8 checker: constructor names vs definition names disjoint. A concrete env \
             discharges RecEnvCtorNoDefVal by red_env_ctor_no_defval_of_b + a single Eq.refl \
             Bool.true. Front #1 Stage 3/4 (faithful checkers).",
        )?;

        Ok(())
    }

    /// i1 soundness: the two fold-membership lemmas, the recrule_for chain,
    /// and the GENERIC discharge `rec_env_reduct_not_redex_of_b`.
    fn add_faithful_checker_i1_soundness(&mut self) -> Result<(), SpecError> {
        const RNR: &str =
            "Eq (OptionType Name) (kexpr_const_name (kapp_fn (recrule_rhs rule))) (OptionType.none Name)";

        // rec_rules_rnr_b_sound: rules-level fold membership (conclusion keyed
        // on the returned rule, so the fire branch transports along r = rule).
        self.add_definition(Self::fchk_lemma(
            "rec_rules_rnr_b_sound",
            &format!(
                "forall (rs : RecRules) (cname : Name) (rule : RecRule), \
                 Eq (OptionType RecRule) (recrule_in_rules rs cname) (OptionType.some RecRule rule) -> \
                 Eq Bool (rec_rules_rnr_b rs) Bool.true -> {RNR}"
            ),
            &format!(
                "fun (rs : RecRules) (cname : Name) (rule : RecRule) => \
                 RecRules.rec \
                 (fun (l : RecRules) => \
                 Eq (OptionType RecRule) (recrule_in_rules l cname) (OptionType.some RecRule rule) -> \
                 Eq Bool (rec_rules_rnr_b l) Bool.true -> {RNR}) \
                 (fun (hlk : Eq (OptionType RecRule) (recrule_in_rules RecRules.nil cname) (OptionType.some RecRule rule)) \
                 (_hb : Eq Bool (rec_rules_rnr_b RecRules.nil) Bool.true) => \
                 option_none_ne_some RecRule rule ({RNR}) hlk) \
                 (fun (r : RecRule) (rest : RecRules) \
                 (ih : Eq (OptionType RecRule) (recrule_in_rules rest cname) (OptionType.some RecRule rule) -> \
                 Eq Bool (rec_rules_rnr_b rest) Bool.true -> {RNR}) \
                 (hlk : Eq (OptionType RecRule) (recrule_in_rules (RecRules.cons r rest) cname) (OptionType.some RecRule rule)) \
                 (hb : Eq Bool (rec_rules_rnr_b (RecRules.cons r rest)) Bool.true) => \
                 opt_pick_some_inv RecRule (name_eqb (recrule_ctor_name r) cname) r \
                 (recrule_in_rules rest cname) rule ({RNR}) hlk \
                 (fun (_ht : Eq Bool (name_eqb (recrule_ctor_name r) cname) Bool.true) \
                 (hval : Eq RecRule r rule) => \
                 Eq.subst RecRule \
                 (fun (z : RecRule) => Eq (OptionType Name) (kexpr_const_name (kapp_fn (recrule_rhs z))) (OptionType.none Name)) \
                 r rule hval \
                 (opt_isnone_eq_none Name (kexpr_const_name (kapp_fn (recrule_rhs r))) \
                 (band_eq_true_left (opt_isnone Name (kexpr_const_name (kapp_fn (recrule_rhs r)))) (rec_rules_rnr_b rest) hb))) \
                 (fun (_hf : Eq Bool (name_eqb (recrule_ctor_name r) cname) Bool.false) \
                 (hrest : Eq (OptionType RecRule) (recrule_in_rules rest cname) (OptionType.some RecRule rule)) => \
                 ih hrest \
                 (band_eq_true_right (opt_isnone Name (kexpr_const_name (kapp_fn (recrule_rhs r)))) (rec_rules_rnr_b rest) hb))) \
                 rs"
            ),
            "Fold-membership (rules level, i1): a successful recrule_in_rules lookup on a \
             checker-true list returns a rule whose rhs head is not a const. RecRules.rec; nil \
             lookup is absurd (option_none_ne_some); cons splits the opt_pick fire (transport the \
             left band conjunct along r = rule via opt_isnone_eq_none) / fall-through (IH on the \
             right band conjunct). DerivedProved, zero axiom_deps. Front #1 Stage 3/4 (faithful \
             checkers).",
            &[
                "RecRules.rec",
                "recrule_in_rules",
                "recrule_ctor_name",
                "recrule_rhs",
                "rec_rules_rnr_b",
                "opt_isnone",
                "opt_isnone_eq_none",
                "opt_pick_some_inv",
                "option_none_ne_some",
                "band_eq_true_left",
                "band_eq_true_right",
                "name_eqb",
                "kexpr_const_name",
                "kapp_fn",
                "Eq.subst",
            ],
        ))?;

        // rec_env_rnr_b_sound: env-level fold membership.
        self.add_definition(Self::fchk_lemma(
            "rec_env_rnr_b_sound",
            "forall (env : RecEnv) (rname : Name) (rules : RecRules), \
             Eq (OptionType RecRules) (recrules_for env rname) (OptionType.some RecRules rules) -> \
             Eq Bool (rec_env_rnr_b env) Bool.true -> \
             Eq Bool (rec_rules_rnr_b rules) Bool.true",
            "fun (env : RecEnv) (rname : Name) (rules : RecRules) => \
             RecEnv.rec \
             (fun (e : RecEnv) => \
             Eq (OptionType RecRules) (recrules_for e rname) (OptionType.some RecRules rules) -> \
             Eq Bool (rec_env_rnr_b e) Bool.true -> \
             Eq Bool (rec_rules_rnr_b rules) Bool.true) \
             (fun (hlk : Eq (OptionType RecRules) (recrules_for RecEnv.empty rname) (OptionType.some RecRules rules)) \
             (_hb : Eq Bool (rec_env_rnr_b RecEnv.empty) Bool.true) => \
             option_none_ne_some RecRules rules \
             (Eq Bool (rec_rules_rnr_b rules) Bool.true) hlk) \
             (fun (tail : RecEnv) (rn : Name) (mta : RecMeta) (rls : RecRules) \
             (ih : Eq (OptionType RecRules) (recrules_for tail rname) (OptionType.some RecRules rules) -> \
             Eq Bool (rec_env_rnr_b tail) Bool.true -> \
             Eq Bool (rec_rules_rnr_b rules) Bool.true) \
             (hlk : Eq (OptionType RecRules) (recrules_for (RecEnv.addRec tail rn mta rls) rname) (OptionType.some RecRules rules)) \
             (hb : Eq Bool (rec_env_rnr_b (RecEnv.addRec tail rn mta rls)) Bool.true) => \
             opt_pick_some_inv RecRules (name_eqb rn rname) rls \
             (recrules_for tail rname) rules \
             (Eq Bool (rec_rules_rnr_b rules) Bool.true) hlk \
             (fun (_ht : Eq Bool (name_eqb rn rname) Bool.true) \
             (hval : Eq RecRules rls rules) => \
             Eq.subst RecRules \
             (fun (z : RecRules) => Eq Bool (rec_rules_rnr_b z) Bool.true) \
             rls rules hval \
             (band_eq_true_left (rec_rules_rnr_b rls) (rec_env_rnr_b tail) hb)) \
             (fun (_hf : Eq Bool (name_eqb rn rname) Bool.false) \
             (htail : Eq (OptionType RecRules) (recrules_for tail rname) (OptionType.some RecRules rules)) => \
             ih htail \
             (band_eq_true_right (rec_rules_rnr_b rls) (rec_env_rnr_b tail) hb))) \
             env",
            "Fold-membership (env level, i1): a successful recrules_for lookup on a checker-true \
             env returns a checker-true rule list. RecEnv.rec; the Stage-1 fire/fall-through \
             split. DerivedProved, zero axiom_deps. Front #1 Stage 3/4 (faithful checkers).",
            &[
                "RecEnv.rec",
                "recrules_for",
                "rec_env_rnr_b",
                "rec_rules_rnr_b",
                "opt_pick_some_inv",
                "option_none_ne_some",
                "band_eq_true_left",
                "band_eq_true_right",
                "name_eqb",
                "Eq.subst",
            ],
        ))?;

        // recrule_for_rnr: chain the two fold-membership lemmas through the
        // recrule_for opt_bind decomposition.
        self.add_definition(Self::fchk_lemma(
            "recrule_for_rnr",
            &format!(
                "forall (env : RecEnv) (recname : Name) (cname : Name) (rule : RecRule), \
                 Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) -> \
                 Eq Bool (rec_env_rnr_b env) Bool.true -> {RNR}"
            ),
            &format!(
                "fun (env : RecEnv) (recname : Name) (cname : Name) (rule : RecRule) \
                 (hlk : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
                 (hb : Eq Bool (rec_env_rnr_b env) Bool.true) => \
                 opt_bind_some_inv RecRules RecRule (recrules_for env recname) \
                 (fun (rules : RecRules) => recrule_in_rules rules cname) rule ({RNR}) hlk \
                 (fun (rules : RecRules) \
                 (hrules : Eq (OptionType RecRules) (recrules_for env recname) (OptionType.some RecRules rules)) \
                 (hin : Eq (OptionType RecRule) (recrule_in_rules rules cname) (OptionType.some RecRule rule)) => \
                 rec_rules_rnr_b_sound rules cname rule hin \
                 (rec_env_rnr_b_sound env recname rules hrules hb))"
            ),
            "Local helper (i1): a successful recrule_for lookup on a checker-true env returns a \
             rule whose rhs head is not a const. Inverts recrule_for into its two lookups \
             (opt_bind_some_inv) and chains the two i1 fold-membership lemmas. DerivedProved, \
             zero axiom_deps. Front #1 Stage 3/4 (faithful checkers).",
            &[
                "recrule_for",
                "recrules_for",
                "recrule_in_rules",
                "opt_bind_some_inv",
                "rec_rules_rnr_b_sound",
                "rec_env_rnr_b_sound",
                "rec_env_rnr_b",
            ],
        ))?;

        // rec_env_reduct_not_redex_of_b: the GENERIC i1 discharge — the
        // env-generic form of faithful_red_env_reduct_not_redex (R3), with
        // the per-env rule inverter replaced by the checker chain.
        let major_idx = "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))";
        let prefix_n = "(Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta))";
        let extras_e = format!("(list_drop (Nat.succ {major_idx}) (kapp_args e))");
        let fields_e = "(list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major))";
        let prefix_e = format!("(list_take {prefix_n} (kapp_args e))");
        let inner3 = format!("(apply_spine {prefix_e} (recrule_rhs rule))");
        let inner2 = format!("(apply_spine {fields_e} {inner3})");
        let reduct_e = format!("(apply_spine {extras_e} {inner2})");
        // kapp_fn REDUCT = kapp_fn (recrule_rhs rule) (strip the three apply_spine layers).
        let kfreduct_eq = format!(
            "(Eq.trans KExpr (kapp_fn {reduct_e}) (kapp_fn {inner2}) (kapp_fn (recrule_rhs rule)) \
             (kapp_fn_apply_spine {extras_e} {inner2}) \
             (Eq.trans KExpr (kapp_fn {inner2}) (kapp_fn {inner3}) (kapp_fn (recrule_rhs rule)) \
             (kapp_fn_apply_spine {fields_e} {inner3}) \
             (kapp_fn_apply_spine {prefix_e} (recrule_rhs rule))))"
        );
        // kexpr_const_name (kapp_fn REDUCT) = none, via the checker chain.
        let head_none = format!(
            "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn {reduct_e})) \
             (kexpr_const_name (kapp_fn (recrule_rhs rule))) (OptionType.none Name) \
             (Eq.cong KExpr (OptionType Name) kexpr_const_name (kapp_fn {reduct_e}) (kapp_fn (recrule_rhs rule)) {kfreduct_eq}) \
             (recrule_for_rnr env recname cname rule h5 hb))"
        );
        let i1_value = format!(
            "fun (env : RecEnv) (hb : Eq Bool (rec_env_rnr_b env) Bool.true) => \
             RecEnvReductNotRedex.mk env \
             (fun (e : KExpr) (r : KExpr) (hyp : Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr r)) => \
             iota_reduct_some_inv env e r \
             (Eq (OptionType KExpr) (iota_reduct env r) (OptionType.none KExpr)) hyp \
             (fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
             (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname)) \
             (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
             (h3 : Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args e))) (OptionType.some KExpr major)) \
             (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
             (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
             (h5r : Eq (OptionType KExpr) (OptionType.some KExpr {reduct_e}) (OptionType.some KExpr r)) => \
             Eq.substType KExpr \
             (fun (x : KExpr) => Eq (OptionType KExpr) (iota_reduct env x) (OptionType.none KExpr)) \
             {reduct_e} r (option_some_inj KExpr {reduct_e} r h5r) \
             (iota_reduct_head_none env {reduct_e} {head_none})))"
        );
        self.add_definition(Self::fchk_lemma(
            "rec_env_reduct_not_redex_of_b",
            "forall (env : RecEnv), \
             Eq Bool (rec_env_rnr_b env) Bool.true -> RecEnvReductNotRedex env",
            &i1_value,
            "GENERIC i1 discharge: rec_env_rnr_b env = true -> RecEnvReductNotRedex env, for ANY \
             env. Invert the fired redex (iota_reduct_some_inv) to expose REDUCT = apply_spine .. \
             (recrule_rhs rule); the checker chain (recrule_for_rnr) pins the rhs head to \
             non-const; the apply_spine layers leave the head fixed (kapp_fn_apply_spine x3), so \
             iota_reduct REDUCT short-circuits to none (iota_reduct_head_none); transport \
             REDUCT = r (option_some_inj). The env-generic form of \
             faithful_red_env_reduct_not_redex. A concrete env now discharges \
             RecEnvReductNotRedex by a single Eq.refl Bool Bool.true. DerivedProved, zero \
             axiom_deps. Front #1 Stage 3/4 (faithful checkers).",
            &[
                "RecEnvReductNotRedex",
                "RecEnvReductNotRedex.mk",
                "rec_env_rnr_b",
                "recrule_for_rnr",
                "iota_reduct_some_inv",
                "iota_reduct_head_none",
                "kapp_fn_apply_spine",
                "option_some_inj",
                "iota_reduct",
                "kexpr_const_name",
                "kapp_fn",
                "recrule_rhs",
                "recrule_for",
                "Eq.substType",
                "Eq.trans",
                "Eq.cong",
            ],
        ))?;

        Ok(())
    }

    /// i2 soundness: fold membership (rules + env level, conclusion keyed on
    /// the LOOKED-UP name via name_eqb_eq) + the generic discharge.
    fn add_faithful_checker_i2_soundness(&mut self) -> Result<(), SpecError> {
        const NOMETA: &str =
            "Eq (OptionType RecMeta) (recmeta_for env0 cname) (OptionType.none RecMeta)";

        self.add_definition(Self::fchk_lemma(
            "rec_rules_no_recmeta_b_sound",
            &format!(
                "forall (env0 : RecEnv) (rs : RecRules) (cname : Name) (rule : RecRule), \
                 Eq (OptionType RecRule) (recrule_in_rules rs cname) (OptionType.some RecRule rule) -> \
                 Eq Bool (rec_rules_no_recmeta_b env0 rs) Bool.true -> {NOMETA}"
            ),
            &format!(
                "fun (env0 : RecEnv) (rs : RecRules) (cname : Name) (rule : RecRule) => \
                 RecRules.rec \
                 (fun (l : RecRules) => \
                 Eq (OptionType RecRule) (recrule_in_rules l cname) (OptionType.some RecRule rule) -> \
                 Eq Bool (rec_rules_no_recmeta_b env0 l) Bool.true -> {NOMETA}) \
                 (fun (hlk : Eq (OptionType RecRule) (recrule_in_rules RecRules.nil cname) (OptionType.some RecRule rule)) \
                 (_hb : Eq Bool (rec_rules_no_recmeta_b env0 RecRules.nil) Bool.true) => \
                 option_none_ne_some RecRule rule ({NOMETA}) hlk) \
                 (fun (r : RecRule) (rest : RecRules) \
                 (ih : Eq (OptionType RecRule) (recrule_in_rules rest cname) (OptionType.some RecRule rule) -> \
                 Eq Bool (rec_rules_no_recmeta_b env0 rest) Bool.true -> {NOMETA}) \
                 (hlk : Eq (OptionType RecRule) (recrule_in_rules (RecRules.cons r rest) cname) (OptionType.some RecRule rule)) \
                 (hb : Eq Bool (rec_rules_no_recmeta_b env0 (RecRules.cons r rest)) Bool.true) => \
                 opt_pick_some_inv RecRule (name_eqb (recrule_ctor_name r) cname) r \
                 (recrule_in_rules rest cname) rule ({NOMETA}) hlk \
                 (fun (ht : Eq Bool (name_eqb (recrule_ctor_name r) cname) Bool.true) \
                 (_hval : Eq RecRule r rule) => \
                 Eq.subst Name \
                 (fun (z : Name) => Eq (OptionType RecMeta) (recmeta_for env0 z) (OptionType.none RecMeta)) \
                 (recrule_ctor_name r) cname (name_eqb_eq (recrule_ctor_name r) cname ht) \
                 (opt_isnone_eq_none RecMeta (recmeta_for env0 (recrule_ctor_name r)) \
                 (band_eq_true_left (opt_isnone RecMeta (recmeta_for env0 (recrule_ctor_name r))) (rec_rules_no_recmeta_b env0 rest) hb))) \
                 (fun (_hf : Eq Bool (name_eqb (recrule_ctor_name r) cname) Bool.false) \
                 (hrest : Eq (OptionType RecRule) (recrule_in_rules rest cname) (OptionType.some RecRule rule)) => \
                 ih hrest \
                 (band_eq_true_right (opt_isnone RecMeta (recmeta_for env0 (recrule_ctor_name r))) (rec_rules_no_recmeta_b env0 rest) hb))) \
                 rs"
            ),
            "Fold-membership (rules level, i2): a successful lookup on a checker-true list pins \
             recmeta_for env0 cname = none. KEY: the conclusion is keyed on the LOOKED-UP name \
             cname, so the fire branch converts its guard via name_eqb_eq and transports the \
             per-element fact from the stored name onto cname. DerivedProved, zero axiom_deps. \
             Front #1 Stage 3/4 (faithful checkers).",
            &[
                "RecRules.rec",
                "recrule_in_rules",
                "recrule_ctor_name",
                "rec_rules_no_recmeta_b",
                "recmeta_for",
                "opt_isnone",
                "opt_isnone_eq_none",
                "opt_pick_some_inv",
                "option_none_ne_some",
                "band_eq_true_left",
                "band_eq_true_right",
                "name_eqb",
                "name_eqb_eq",
                "Eq.subst",
            ],
        ))?;

        self.add_definition(Self::fchk_lemma(
            "rec_env_no_recmeta_go_b_sound",
            "forall (env0 : RecEnv) (env : RecEnv) (rname : Name) (rules : RecRules), \
             Eq (OptionType RecRules) (recrules_for env rname) (OptionType.some RecRules rules) -> \
             Eq Bool (rec_env_no_recmeta_go_b env0 env) Bool.true -> \
             Eq Bool (rec_rules_no_recmeta_b env0 rules) Bool.true",
            "fun (env0 : RecEnv) (env : RecEnv) (rname : Name) (rules : RecRules) => \
             RecEnv.rec \
             (fun (e : RecEnv) => \
             Eq (OptionType RecRules) (recrules_for e rname) (OptionType.some RecRules rules) -> \
             Eq Bool (rec_env_no_recmeta_go_b env0 e) Bool.true -> \
             Eq Bool (rec_rules_no_recmeta_b env0 rules) Bool.true) \
             (fun (hlk : Eq (OptionType RecRules) (recrules_for RecEnv.empty rname) (OptionType.some RecRules rules)) \
             (_hb : Eq Bool (rec_env_no_recmeta_go_b env0 RecEnv.empty) Bool.true) => \
             option_none_ne_some RecRules rules \
             (Eq Bool (rec_rules_no_recmeta_b env0 rules) Bool.true) hlk) \
             (fun (tail : RecEnv) (rn : Name) (mta : RecMeta) (rls : RecRules) \
             (ih : Eq (OptionType RecRules) (recrules_for tail rname) (OptionType.some RecRules rules) -> \
             Eq Bool (rec_env_no_recmeta_go_b env0 tail) Bool.true -> \
             Eq Bool (rec_rules_no_recmeta_b env0 rules) Bool.true) \
             (hlk : Eq (OptionType RecRules) (recrules_for (RecEnv.addRec tail rn mta rls) rname) (OptionType.some RecRules rules)) \
             (hb : Eq Bool (rec_env_no_recmeta_go_b env0 (RecEnv.addRec tail rn mta rls)) Bool.true) => \
             opt_pick_some_inv RecRules (name_eqb rn rname) rls \
             (recrules_for tail rname) rules \
             (Eq Bool (rec_rules_no_recmeta_b env0 rules) Bool.true) hlk \
             (fun (_ht : Eq Bool (name_eqb rn rname) Bool.true) \
             (hval : Eq RecRules rls rules) => \
             Eq.subst RecRules \
             (fun (z : RecRules) => Eq Bool (rec_rules_no_recmeta_b env0 z) Bool.true) \
             rls rules hval \
             (band_eq_true_left (rec_rules_no_recmeta_b env0 rls) (rec_env_no_recmeta_go_b env0 tail) hb)) \
             (fun (_hf : Eq Bool (name_eqb rn rname) Bool.false) \
             (htail : Eq (OptionType RecRules) (recrules_for tail rname) (OptionType.some RecRules rules)) => \
             ih htail \
             (band_eq_true_right (rec_rules_no_recmeta_b env0 rls) (rec_env_no_recmeta_go_b env0 tail) hb))) \
             env",
            "Fold-membership (env level, i2): a successful recrules_for lookup on a checker-true \
             env (lookup context env0 fixed) returns a checker-true rule list. RecEnv.rec; the \
             Stage-1 fire/fall-through split. DerivedProved, zero axiom_deps. Front #1 Stage 3/4 \
             (faithful checkers).",
            &[
                "RecEnv.rec",
                "recrules_for",
                "rec_env_no_recmeta_go_b",
                "rec_rules_no_recmeta_b",
                "opt_pick_some_inv",
                "option_none_ne_some",
                "band_eq_true_left",
                "band_eq_true_right",
                "name_eqb",
                "Eq.subst",
            ],
        ))?;

        self.add_definition(Self::fchk_lemma(
            "rec_env_ctor_no_recmeta_of_b",
            "forall (env : RecEnv), \
             Eq Bool (rec_env_ctor_no_recmeta_b env) Bool.true -> RecEnvCtorNoRecMeta env",
            "fun (env : RecEnv) (hb : Eq Bool (rec_env_ctor_no_recmeta_b env) Bool.true) => \
             RecEnvCtorNoRecMeta.mk env \
             (fun (recname : Name) (cname : Name) (rule : RecRule) (major : KExpr) \
             (_hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
             (hrule : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) => \
             opt_bind_some_inv RecRules RecRule (recrules_for env recname) \
             (fun (rules : RecRules) => recrule_in_rules rules cname) rule \
             (Eq (OptionType RecMeta) (recmeta_for env cname) (OptionType.none RecMeta)) hrule \
             (fun (rules : RecRules) \
             (hrules : Eq (OptionType RecRules) (recrules_for env recname) (OptionType.some RecRules rules)) \
             (hin : Eq (OptionType RecRule) (recrule_in_rules rules cname) (OptionType.some RecRule rule)) => \
             rec_rules_no_recmeta_b_sound env rules cname rule hin \
             (rec_env_no_recmeta_go_b_sound env env recname rules hrules hb)))",
            "GENERIC i2 discharge: rec_env_ctor_no_recmeta_b env = true -> RecEnvCtorNoRecMeta \
             env, for ANY env. Invert recrule_for into its two lookups (opt_bind_some_inv), chain \
             the two fold-membership lemmas at env0 := env (the checker alias unfolds \
             definitionally). The major/head hypothesis is carried to match the interface \
             statement exactly. A concrete env now discharges by a single Eq.refl Bool Bool.true. \
             DerivedProved, zero axiom_deps. Front #1 Stage 3/4 (faithful checkers).",
            &[
                "RecEnvCtorNoRecMeta",
                "RecEnvCtorNoRecMeta.mk",
                "rec_env_ctor_no_recmeta_b",
                "rec_rules_no_recmeta_b_sound",
                "rec_env_no_recmeta_go_b_sound",
                "opt_bind_some_inv",
                "recrule_for",
                "recrules_for",
                "recrule_in_rules",
                "recmeta_for",
                "kexpr_const_name",
                "kapp_fn",
            ],
        ))?;

        Ok(())
    }

    /// i7 soundness: def-env fold membership + the generic discharge.
    fn add_faithful_checker_i7_soundness(&mut self) -> Result<(), SpecError> {
        const NOMETA_D: &str =
            "Eq (OptionType RecMeta) (recmeta_for renv dname) (OptionType.none RecMeta)";

        self.add_definition(Self::fchk_lemma(
            "def_env_no_recmeta_b_sound",
            &format!(
                "forall (renv : RecEnv) (denv : DefEnv) (dname : Name) (val : KExpr), \
                 Eq (OptionType KExpr) (defval_for denv dname) (OptionType.some KExpr val) -> \
                 Eq Bool (def_env_no_recmeta_b renv denv) Bool.true -> {NOMETA_D}"
            ),
            &format!(
                "fun (renv : RecEnv) (denv : DefEnv) (dname : Name) (val : KExpr) => \
                 DefEnv.rec \
                 (fun (e : DefEnv) => \
                 Eq (OptionType KExpr) (defval_for e dname) (OptionType.some KExpr val) -> \
                 Eq Bool (def_env_no_recmeta_b renv e) Bool.true -> {NOMETA_D}) \
                 (fun (hlk : Eq (OptionType KExpr) (defval_for DefEnv.empty dname) (OptionType.some KExpr val)) \
                 (_hb : Eq Bool (def_env_no_recmeta_b renv DefEnv.empty) Bool.true) => \
                 option_none_ne_some KExpr val ({NOMETA_D}) hlk) \
                 (fun (tail : DefEnv) (dn : Name) (dv : KExpr) \
                 (ih : Eq (OptionType KExpr) (defval_for tail dname) (OptionType.some KExpr val) -> \
                 Eq Bool (def_env_no_recmeta_b renv tail) Bool.true -> {NOMETA_D}) \
                 (hlk : Eq (OptionType KExpr) (defval_for (DefEnv.addDef tail dn dv) dname) (OptionType.some KExpr val)) \
                 (hb : Eq Bool (def_env_no_recmeta_b renv (DefEnv.addDef tail dn dv)) Bool.true) => \
                 opt_pick_some_inv KExpr (name_eqb dn dname) dv \
                 (defval_for tail dname) val ({NOMETA_D}) hlk \
                 (fun (ht : Eq Bool (name_eqb dn dname) Bool.true) \
                 (_hval : Eq KExpr dv val) => \
                 Eq.subst Name \
                 (fun (z : Name) => Eq (OptionType RecMeta) (recmeta_for renv z) (OptionType.none RecMeta)) \
                 dn dname (name_eqb_eq dn dname ht) \
                 (opt_isnone_eq_none RecMeta (recmeta_for renv dn) \
                 (band_eq_true_left (opt_isnone RecMeta (recmeta_for renv dn)) (def_env_no_recmeta_b renv tail) hb))) \
                 (fun (_hf : Eq Bool (name_eqb dn dname) Bool.false) \
                 (htail : Eq (OptionType KExpr) (defval_for tail dname) (OptionType.some KExpr val)) => \
                 ih htail \
                 (band_eq_true_right (opt_isnone RecMeta (recmeta_for renv dn)) (def_env_no_recmeta_b renv tail) hb))) \
                 denv"
            ),
            "Fold-membership (def-env level, i7): a successful defval_for lookup on a \
             checker-true def env pins recmeta_for renv dname = none (fire branch via name_eqb_eq \
             + transport, fall-through via IH). DerivedProved, zero axiom_deps. Front #1 \
             Stage 3/4 (faithful checkers).",
            &[
                "DefEnv.rec",
                "defval_for",
                "def_env_no_recmeta_b",
                "recmeta_for",
                "opt_isnone",
                "opt_isnone_eq_none",
                "opt_pick_some_inv",
                "option_none_ne_some",
                "band_eq_true_left",
                "band_eq_true_right",
                "name_eqb",
                "name_eqb_eq",
                "Eq.subst",
            ],
        ))?;

        self.add_definition(Self::fchk_lemma(
            "red_env_disjoint_of_b",
            "forall (env : RedEnv), \
             Eq Bool (red_env_disjoint_b env) Bool.true -> RecEnvDefEnvDisjoint env",
            "fun (env : RedEnv) (hb : Eq Bool (red_env_disjoint_b env) Bool.true) => \
             RecEnvDefEnvDisjoint.mk env \
             (fun (dname : Name) (val : KExpr) \
             (hdv : Eq (OptionType KExpr) (defval_for (red_def env) dname) (OptionType.some KExpr val)) => \
             def_env_no_recmeta_b_sound (red_rec env) (red_def env) dname val hdv hb)",
            "GENERIC i7 discharge: red_env_disjoint_b env = true -> RecEnvDefEnvDisjoint env, for \
             ANY env (the checker alias unfolds definitionally onto the def-env fold). A concrete \
             env now discharges by a single Eq.refl Bool Bool.true. DerivedProved, zero \
             axiom_deps. Front #1 Stage 3/4 (faithful checkers).",
            &[
                "RecEnvDefEnvDisjoint",
                "RecEnvDefEnvDisjoint.mk",
                "red_env_disjoint_b",
                "def_env_no_recmeta_b_sound",
                "defval_for",
                "red_rec",
                "red_def",
            ],
        ))?;

        Ok(())
    }

    /// i8 soundness: mirrors i2 with the per-element slot swapped to
    /// `defval_for denv` + the generic discharge.
    fn add_faithful_checker_i8_soundness(&mut self) -> Result<(), SpecError> {
        const NODEF: &str = "Eq (OptionType KExpr) (defval_for denv cname) (OptionType.none KExpr)";

        self.add_definition(Self::fchk_lemma(
            "rec_rules_no_defval_b_sound",
            &format!(
                "forall (denv : DefEnv) (rs : RecRules) (cname : Name) (rule : RecRule), \
                 Eq (OptionType RecRule) (recrule_in_rules rs cname) (OptionType.some RecRule rule) -> \
                 Eq Bool (rec_rules_no_defval_b denv rs) Bool.true -> {NODEF}"
            ),
            &format!(
                "fun (denv : DefEnv) (rs : RecRules) (cname : Name) (rule : RecRule) => \
                 RecRules.rec \
                 (fun (l : RecRules) => \
                 Eq (OptionType RecRule) (recrule_in_rules l cname) (OptionType.some RecRule rule) -> \
                 Eq Bool (rec_rules_no_defval_b denv l) Bool.true -> {NODEF}) \
                 (fun (hlk : Eq (OptionType RecRule) (recrule_in_rules RecRules.nil cname) (OptionType.some RecRule rule)) \
                 (_hb : Eq Bool (rec_rules_no_defval_b denv RecRules.nil) Bool.true) => \
                 option_none_ne_some RecRule rule ({NODEF}) hlk) \
                 (fun (r : RecRule) (rest : RecRules) \
                 (ih : Eq (OptionType RecRule) (recrule_in_rules rest cname) (OptionType.some RecRule rule) -> \
                 Eq Bool (rec_rules_no_defval_b denv rest) Bool.true -> {NODEF}) \
                 (hlk : Eq (OptionType RecRule) (recrule_in_rules (RecRules.cons r rest) cname) (OptionType.some RecRule rule)) \
                 (hb : Eq Bool (rec_rules_no_defval_b denv (RecRules.cons r rest)) Bool.true) => \
                 opt_pick_some_inv RecRule (name_eqb (recrule_ctor_name r) cname) r \
                 (recrule_in_rules rest cname) rule ({NODEF}) hlk \
                 (fun (ht : Eq Bool (name_eqb (recrule_ctor_name r) cname) Bool.true) \
                 (_hval : Eq RecRule r rule) => \
                 Eq.subst Name \
                 (fun (z : Name) => Eq (OptionType KExpr) (defval_for denv z) (OptionType.none KExpr)) \
                 (recrule_ctor_name r) cname (name_eqb_eq (recrule_ctor_name r) cname ht) \
                 (opt_isnone_eq_none KExpr (defval_for denv (recrule_ctor_name r)) \
                 (band_eq_true_left (opt_isnone KExpr (defval_for denv (recrule_ctor_name r))) (rec_rules_no_defval_b denv rest) hb))) \
                 (fun (_hf : Eq Bool (name_eqb (recrule_ctor_name r) cname) Bool.false) \
                 (hrest : Eq (OptionType RecRule) (recrule_in_rules rest cname) (OptionType.some RecRule rule)) => \
                 ih hrest \
                 (band_eq_true_right (opt_isnone KExpr (defval_for denv (recrule_ctor_name r))) (rec_rules_no_defval_b denv rest) hb))) \
                 rs"
            ),
            "Fold-membership (rules level, i8): mirror of rec_rules_no_recmeta_b_sound with the \
             per-element slot swapped to defval_for denv. DerivedProved, zero axiom_deps. Front \
             #1 Stage 3/4 (faithful checkers).",
            &[
                "RecRules.rec",
                "recrule_in_rules",
                "recrule_ctor_name",
                "rec_rules_no_defval_b",
                "defval_for",
                "opt_isnone",
                "opt_isnone_eq_none",
                "opt_pick_some_inv",
                "option_none_ne_some",
                "band_eq_true_left",
                "band_eq_true_right",
                "name_eqb",
                "name_eqb_eq",
                "Eq.subst",
            ],
        ))?;

        self.add_definition(Self::fchk_lemma(
            "rec_env_no_defval_go_b_sound",
            "forall (denv : DefEnv) (env : RecEnv) (rname : Name) (rules : RecRules), \
             Eq (OptionType RecRules) (recrules_for env rname) (OptionType.some RecRules rules) -> \
             Eq Bool (rec_env_no_defval_go_b denv env) Bool.true -> \
             Eq Bool (rec_rules_no_defval_b denv rules) Bool.true",
            "fun (denv : DefEnv) (env : RecEnv) (rname : Name) (rules : RecRules) => \
             RecEnv.rec \
             (fun (e : RecEnv) => \
             Eq (OptionType RecRules) (recrules_for e rname) (OptionType.some RecRules rules) -> \
             Eq Bool (rec_env_no_defval_go_b denv e) Bool.true -> \
             Eq Bool (rec_rules_no_defval_b denv rules) Bool.true) \
             (fun (hlk : Eq (OptionType RecRules) (recrules_for RecEnv.empty rname) (OptionType.some RecRules rules)) \
             (_hb : Eq Bool (rec_env_no_defval_go_b denv RecEnv.empty) Bool.true) => \
             option_none_ne_some RecRules rules \
             (Eq Bool (rec_rules_no_defval_b denv rules) Bool.true) hlk) \
             (fun (tail : RecEnv) (rn : Name) (mta : RecMeta) (rls : RecRules) \
             (ih : Eq (OptionType RecRules) (recrules_for tail rname) (OptionType.some RecRules rules) -> \
             Eq Bool (rec_env_no_defval_go_b denv tail) Bool.true -> \
             Eq Bool (rec_rules_no_defval_b denv rules) Bool.true) \
             (hlk : Eq (OptionType RecRules) (recrules_for (RecEnv.addRec tail rn mta rls) rname) (OptionType.some RecRules rules)) \
             (hb : Eq Bool (rec_env_no_defval_go_b denv (RecEnv.addRec tail rn mta rls)) Bool.true) => \
             opt_pick_some_inv RecRules (name_eqb rn rname) rls \
             (recrules_for tail rname) rules \
             (Eq Bool (rec_rules_no_defval_b denv rules) Bool.true) hlk \
             (fun (_ht : Eq Bool (name_eqb rn rname) Bool.true) \
             (hval : Eq RecRules rls rules) => \
             Eq.subst RecRules \
             (fun (z : RecRules) => Eq Bool (rec_rules_no_defval_b denv z) Bool.true) \
             rls rules hval \
             (band_eq_true_left (rec_rules_no_defval_b denv rls) (rec_env_no_defval_go_b denv tail) hb)) \
             (fun (_hf : Eq Bool (name_eqb rn rname) Bool.false) \
             (htail : Eq (OptionType RecRules) (recrules_for tail rname) (OptionType.some RecRules rules)) => \
             ih htail \
             (band_eq_true_right (rec_rules_no_defval_b denv rls) (rec_env_no_defval_go_b denv tail) hb))) \
             env",
            "Fold-membership (env level, i8): mirror of rec_env_no_recmeta_go_b_sound. \
             DerivedProved, zero axiom_deps. Front #1 Stage 3/4 (faithful checkers).",
            &[
                "RecEnv.rec",
                "recrules_for",
                "rec_env_no_defval_go_b",
                "rec_rules_no_defval_b",
                "opt_pick_some_inv",
                "option_none_ne_some",
                "band_eq_true_left",
                "band_eq_true_right",
                "name_eqb",
                "Eq.subst",
            ],
        ))?;

        self.add_definition(Self::fchk_lemma(
            "red_env_ctor_no_defval_of_b",
            "forall (env : RedEnv), \
             Eq Bool (red_env_ctor_no_defval_b env) Bool.true -> RecEnvCtorNoDefVal env",
            "fun (env : RedEnv) (hb : Eq Bool (red_env_ctor_no_defval_b env) Bool.true) => \
             RecEnvCtorNoDefVal.mk env \
             (fun (recname : Name) (cname : Name) (rule : RecRule) (major : KExpr) \
             (_hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
             (hrule : Eq (OptionType RecRule) (recrule_for (red_rec env) recname cname) (OptionType.some RecRule rule)) => \
             opt_bind_some_inv RecRules RecRule (recrules_for (red_rec env) recname) \
             (fun (rules : RecRules) => recrule_in_rules rules cname) rule \
             (Eq (OptionType KExpr) (defval_for (red_def env) cname) (OptionType.none KExpr)) hrule \
             (fun (rules : RecRules) \
             (hrules : Eq (OptionType RecRules) (recrules_for (red_rec env) recname) (OptionType.some RecRules rules)) \
             (hin : Eq (OptionType RecRule) (recrule_in_rules rules cname) (OptionType.some RecRule rule)) => \
             rec_rules_no_defval_b_sound (red_def env) rules cname rule hin \
             (rec_env_no_defval_go_b_sound (red_def env) (red_rec env) recname rules hrules hb)))",
            "GENERIC i8 discharge: red_env_ctor_no_defval_b env = true -> RecEnvCtorNoDefVal env, \
             for ANY env (the checker alias unfolds definitionally). A concrete env now \
             discharges by a single Eq.refl Bool Bool.true. DerivedProved, zero axiom_deps. Front \
             #1 Stage 3/4 (faithful checkers).",
            &[
                "RecEnvCtorNoDefVal",
                "RecEnvCtorNoDefVal.mk",
                "red_env_ctor_no_defval_b",
                "rec_rules_no_defval_b_sound",
                "rec_env_no_defval_go_b_sound",
                "opt_bind_some_inv",
                "recrule_for",
                "recrules_for",
                "recrule_in_rules",
                "defval_for",
                "kexpr_const_name",
                "kapp_fn",
                "red_rec",
                "red_def",
            ],
        ))?;

        Ok(())
    }

    /// Regression demo (checker-faithfulness gate): all four faithful
    /// interfaces over `faithful_red_env` by the single-rfl route — the exact
    /// shape the Stage-4 discharge uses over the swapped `the_red_env`.
    fn add_faithful_checker_demo(&mut self) -> Result<(), SpecError> {
        let demos: [(&str, String, &str); 4] = [
            (
                "faithful_red_env_reduct_not_redex_via_checker",
                "RecEnvReductNotRedex (red_rec faithful_red_env)".to_string(),
                "rec_env_reduct_not_redex_of_b (red_rec faithful_red_env) (Eq.refl Bool Bool.true)",
            ),
            (
                "faithful_red_env_ctor_no_recmeta_via_checker",
                "RecEnvCtorNoRecMeta (red_rec faithful_red_env)".to_string(),
                "rec_env_ctor_no_recmeta_of_b (red_rec faithful_red_env) (Eq.refl Bool Bool.true)",
            ),
            (
                "faithful_red_env_defenv_disjoint_via_checker",
                "RecEnvDefEnvDisjoint faithful_red_env".to_string(),
                "red_env_disjoint_of_b faithful_red_env (Eq.refl Bool Bool.true)",
            ),
            (
                "faithful_red_env_ctor_no_defval_via_checker",
                "RecEnvCtorNoDefVal faithful_red_env".to_string(),
                "red_env_ctor_no_defval_of_b faithful_red_env (Eq.refl Bool Bool.true)",
            ),
        ];

        for (name, type_src, value_src) in demos {
            let of_b = value_src
                .split_whitespace()
                .next()
                .expect("demo value_src starts with the generic lemma name");
            self.add_definition(Self::fchk_lemma(
                name,
                &type_src,
                value_src,
                &format!(
                    "Regression demo (Front #1 Stage 3/4 checker-faithfulness gate): {type_src} \
                     discharged over faithful_red_env by the SINGLE-RFL checker route — {of_b} + \
                     Eq.refl Bool Bool.true; the kernel whnf-evaluates the checker fold over the \
                     concrete env. Demo only (the per-env R1/R3 witnesses are untouched). \
                     DerivedProved, zero axiom_deps."
                ),
                &[of_b, "faithful_red_env", "Eq.refl"],
            ))?;
        }

        Ok(())
    }

    /// THE STAGE-4 DISCHARGE: with `the_red_env := kernel_core_red_env` (the
    /// Stage-3 swap), all EIGHT faithful interfaces hold over `the_red_env`
    /// by the single-rfl checker route, and the full bundle
    /// `the_red_env_faithful : RedEnvFaithful the_red_env` is assembled via
    /// `RedEnvFaithful.mk`. Registering each witness forces the kernel to
    /// whnf-EVALUATE the checker folds over the real reflected env down to
    /// `Bool.true`. The ~79 carried-hypothesis metatheory decls stay
    /// parametric (instantiating them is follow-up); NOTHING here is an
    /// axiom — census stays 11.
    pub(super) fn add_the_red_env_faithful_discharge(&mut self) -> Result<(), SpecError> {
        let witnesses: [(&str, String, &str); 8] = [
            (
                "the_red_env_reduct_not_redex_via_checker",
                "RecEnvReductNotRedex (red_rec the_red_env)".to_string(),
                "rec_env_reduct_not_redex_of_b (red_rec the_red_env) (Eq.refl Bool Bool.true)",
            ),
            (
                "the_red_env_ctor_no_recmeta_via_checker",
                "RecEnvCtorNoRecMeta (red_rec the_red_env)".to_string(),
                "rec_env_ctor_no_recmeta_of_b (red_rec the_red_env) (Eq.refl Bool Bool.true)",
            ),
            (
                "the_red_env_rec_closed_via_checker_b2",
                "RecEnvClosed (red_rec the_red_env)".to_string(),
                "rec_env_closed_of_b2 (red_rec the_red_env) (Eq.refl Bool Bool.true)",
            ),
            (
                "the_red_env_rec_lift_closed_via_checker_b2",
                "RecEnvLiftClosed (red_rec the_red_env)".to_string(),
                "rec_env_lift_closed_of_b2 (red_rec the_red_env) (Eq.refl Bool Bool.true)",
            ),
            (
                "the_red_env_def_closed_via_checker_b2",
                "DefEnvClosed (red_def the_red_env)".to_string(),
                "def_env_closed_of_b2 (red_def the_red_env) (Eq.refl Bool Bool.true)",
            ),
            (
                "the_red_env_def_lift_closed_via_checker_b2",
                "DefEnvLiftClosed (red_def the_red_env)".to_string(),
                "def_env_lift_closed_of_b2 (red_def the_red_env) (Eq.refl Bool Bool.true)",
            ),
            (
                "the_red_env_defenv_disjoint_via_checker",
                "RecEnvDefEnvDisjoint the_red_env".to_string(),
                "red_env_disjoint_of_b the_red_env (Eq.refl Bool Bool.true)",
            ),
            (
                "the_red_env_ctor_no_defval_via_checker",
                "RecEnvCtorNoDefVal the_red_env".to_string(),
                "red_env_ctor_no_defval_of_b the_red_env (Eq.refl Bool Bool.true)",
            ),
        ];

        for (name, type_src, value_src) in witnesses {
            let of_b = value_src
                .split_whitespace()
                .next()
                .expect("witness value_src starts with the generic lemma name");
            self.add_definition(Self::fchk_lemma(
                name,
                &type_src,
                value_src,
                &format!(
                    "THE STAGE-4 DISCHARGE (Front #1): {type_src} over the REAL distinguished \
                     environment (the_red_env := kernel_core_red_env, the fidelity-gated \
                     reflection of the kernel foundation core) by the SINGLE-RFL checker route — \
                     {of_b} + Eq.refl Bool Bool.true. The kernel whnf-evaluates the checker fold \
                     over the real reflected env down to Bool.true at registration. One of the \
                     eight honest interface witnesses the_red_env_faithful bundles. \
                     DerivedProved, zero axiom_deps."
                ),
                &[of_b, "the_red_env", "Eq.refl"],
            ))?;
        }

        // THE MILESTONE: the full RedEnvFaithful bundle over the_red_env,
        // assembled from the eight single-rfl witnesses.
        self.add_definition(Self::fchk_lemma(
            "the_red_env_faithful",
            "RedEnvFaithful the_red_env",
            "RedEnvFaithful.mk the_red_env \
             the_red_env_reduct_not_redex_via_checker \
             the_red_env_ctor_no_recmeta_via_checker \
             the_red_env_rec_closed_via_checker_b2 \
             the_red_env_rec_lift_closed_via_checker_b2 \
             the_red_env_def_closed_via_checker_b2 \
             the_red_env_def_lift_closed_via_checker_b2 \
             the_red_env_defenv_disjoint_via_checker \
             the_red_env_ctor_no_defval_via_checker",
            "THE STAGE-4 MILESTONE (Front #1): the FULL RedEnvFaithful bundle over the \
             metatheory's REAL distinguished environment the_red_env (:= kernel_core_red_env, \
             the fidelity-gated reflection of the real kernel foundation core), assembled by \
             RedEnvFaithful.mk from the eight honest single-rfl interface witnesses (i1 \
             RecEnvReductNotRedex, i2 RecEnvCtorNoRecMeta, i3 RecEnvClosed, i4 RecEnvLiftClosed, \
             i5 DefEnvClosed, i6 DefEnvLiftClosed, i7 RecEnvDefEnvDisjoint, i8 \
             RecEnvCtorNoDefVal) — every one a real DerivedProved term, NONE asserted/carried. \
             The carried-hypothesis metatheory can now be instantiated at the_red_env with THIS \
             witness. DerivedProved, zero axiom_deps.",
            &[
                "RedEnvFaithful",
                "RedEnvFaithful.mk",
                "the_red_env",
                "the_red_env_reduct_not_redex_via_checker",
                "the_red_env_ctor_no_recmeta_via_checker",
                "the_red_env_rec_closed_via_checker_b2",
                "the_red_env_rec_lift_closed_via_checker_b2",
                "the_red_env_def_closed_via_checker_b2",
                "the_red_env_def_lift_closed_via_checker_b2",
                "the_red_env_defenv_disjoint_via_checker",
                "the_red_env_ctor_no_defval_via_checker",
            ],
        ))?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::spec::types::{AxiomCategory, ProofStatus};
    use crate::test_utils::build_spec_with_stack;

    /// All ten checkers + opt_isnone register as value-ful, non-axiom defs
    /// with no axiom blockers.
    #[test]
    fn test_faithful_checkers_are_valueful_defs() {
        let spec = build_spec_with_stack();
        for name in [
            "opt_isnone",
            "rec_rules_rnr_b",
            "rec_env_rnr_b",
            "rec_rules_no_recmeta_b",
            "rec_env_no_recmeta_go_b",
            "rec_env_ctor_no_recmeta_b",
            "def_env_no_recmeta_b",
            "red_env_disjoint_b",
            "rec_rules_no_defval_b",
            "rec_env_no_defval_go_b",
            "red_env_ctor_no_defval_b",
        ] {
            let def = spec
                .definitions()
                .get(name)
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert!(def.value_src.is_some(), "{name} should have a value");
            assert!(!def.is_axiom, "{name} must not be an axiom");
            assert!(
                def.axiom_deps.is_empty(),
                "{name} must have no axiom blockers: {:?}",
                def.axiom_deps
            );
        }
    }

    /// The soundness + generic-discharge lemmas are real DerivedProved terms
    /// (zero axiom_deps) and re-typecheck against the live kernel env.
    #[test]
    fn test_faithful_checker_soundness_lemmas_are_derived_proved_zero_axioms() {
        let spec = build_spec_with_stack();
        for name in [
            "opt_isnone_eq_none",
            "rec_rules_rnr_b_sound",
            "rec_env_rnr_b_sound",
            "recrule_for_rnr",
            "rec_env_reduct_not_redex_of_b",
            "rec_rules_no_recmeta_b_sound",
            "rec_env_no_recmeta_go_b_sound",
            "rec_env_ctor_no_recmeta_of_b",
            "def_env_no_recmeta_b_sound",
            "red_env_disjoint_of_b",
            "rec_rules_no_defval_b_sound",
            "rec_env_no_defval_go_b_sound",
            "red_env_ctor_no_defval_of_b",
        ] {
            let def = spec
                .definitions()
                .get(name)
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert!(!def.is_axiom, "{name} must not be an axiom (no masquerade)");
            assert_eq!(
                def.category,
                AxiomCategory::DerivedLemma,
                "{name} should be a DerivedLemma"
            );
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "{name} should be DerivedProved"
            );
            assert!(
                def.axiom_deps.is_empty(),
                "{name} must carry zero axiom_deps: {:?}",
                def.axiom_deps
            );
            spec.verify_definition(name)
                .unwrap_or_else(|e| panic!("{name} should elaborate and type-check: {e:?}"));
        }
    }

    /// THE STAGE-4 GATE: the swapped the_red_env (= the reflected real kernel
    /// foundation core) discharges ALL EIGHT faithful interfaces by the
    /// single-rfl route, and the full RedEnvFaithful bundle assembles.
    #[test]
    fn test_the_red_env_discharges_full_faithful_bundle() {
        let spec = build_spec_with_stack();
        for name in [
            "the_red_env_reduct_not_redex_via_checker",
            "the_red_env_ctor_no_recmeta_via_checker",
            "the_red_env_rec_closed_via_checker_b2",
            "the_red_env_rec_lift_closed_via_checker_b2",
            "the_red_env_def_closed_via_checker_b2",
            "the_red_env_def_lift_closed_via_checker_b2",
            "the_red_env_defenv_disjoint_via_checker",
            "the_red_env_ctor_no_defval_via_checker",
            "the_red_env_faithful",
        ] {
            let def = spec
                .definitions()
                .get(name)
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert!(!def.is_axiom, "{name} must not be an axiom (no masquerade)");
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "{name} should be DerivedProved"
            );
            assert!(
                def.axiom_deps.is_empty(),
                "{name} must carry zero axiom_deps: {:?}",
                def.axiom_deps
            );
            spec.verify_definition(name)
                .unwrap_or_else(|e| panic!("{name} (Stage-4 witness) must kernel-check: {e:?}"));
        }
        let bundle = spec
            .definitions()
            .get("the_red_env_faithful")
            .expect("the_red_env_faithful should be registered");
        assert_eq!(
            bundle.type_src, "RedEnvFaithful the_red_env",
            "the bundle must be stated at the_red_env itself"
        );
    }

    /// The faithful_red_env regression probes (checker-faithfulness gate)
    /// discharge by the single-rfl route.
    #[test]
    fn test_faithful_env_discharges_by_single_rfl_faithful_checkers() {
        let spec = build_spec_with_stack();
        for name in [
            "faithful_red_env_reduct_not_redex_via_checker",
            "faithful_red_env_ctor_no_recmeta_via_checker",
            "faithful_red_env_defenv_disjoint_via_checker",
            "faithful_red_env_ctor_no_defval_via_checker",
        ] {
            let def = spec
                .definitions()
                .get(name)
                .unwrap_or_else(|| panic!("{name} should be registered"));
            let value = def
                .value_src
                .as_deref()
                .unwrap_or_else(|| panic!("{name} must carry a proof term"));
            assert!(
                value.contains("(Eq.refl Bool Bool.true)"),
                "{name} must be the single-rfl checker route, got: {value}"
            );
            spec.verify_definition(name)
                .unwrap_or_else(|e| panic!("{name} (single-rfl witness) must kernel-check: {e:?}"));
        }
    }
}
