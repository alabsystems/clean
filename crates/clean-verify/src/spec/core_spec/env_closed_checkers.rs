// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Front #1 Stage 1 (the_red_env discharge program): Bool CHECKERS + generic
//! checker-soundness lemmas — the scaling pattern that makes per-env closure
//! interface discharge a ONE-RFL operation.
//!
//! ## Why checkers
//!
//! Per-rule rfl fails on real rule RHSs: `instantiate_at rhs val depth = rhs`
//! is NOT a kernel computation when `rhs` has bvars under binders and `depth`
//! is symbolic — the recursion sticks on the free depth. The faithful-env
//! discharge (R2, `faithful_red_env.rs`) worked around this with per-env
//! lookup-inversion towers (`fre_rule_eq_rule` + a transported `Eq.refl`),
//! which is O(env-shape) proof text per environment.
//!
//! Instead: a recursive Bool CHECKER folds the decidable closedness test
//! `nat_eqb (bvar_ceiling rhs) 0` over the WHOLE env structure, and ONE
//! generic soundness lemma per interface converts `checker env = true` into
//! the interface. Any concrete env then discharges each closure interface by
//! a single `Eq.refl Bool Bool.true` — the kernel whnf-EVALUATES the checker
//! fold over the concrete env. New env, same one-liner.
//!
//! ## The pieces
//!
//! Checkers (recursive defs, kernel-evaluable on concrete envs):
//! - `rec_rules_closed_b : RecRules -> Bool` — every rule rhs has ceiling 0.
//! - `rec_env_closed_b : RecEnv -> Bool` — every recursor's rule list passes.
//! - `rec_env_lift_closed_b : RecEnv -> Bool` — alias of `rec_env_closed_b`:
//!   closedness is ONE test; only the discharging keystone differs
//!   (`lift_ceiling_id` vs `inst_above_ceiling_id`).
//! - `def_env_closed_b : DefEnv -> Bool` — every def value has ceiling 0.
//! - `def_env_lift_closed_b : DefEnv -> Bool` — alias of `def_env_closed_b`.
//!
//! Fold-membership soundness (the technical meat — structural induction over
//! the env lists + the `opt_pick` lookup fold):
//! - `rec_env_closed_b_sound` — a successful `recrules_for` lookup on a
//!   checker-true env returns a checker-true rule list.
//! - `rec_rules_closed_b_sound` — a successful `recrule_in_rules` lookup on a
//!   checker-true rule list returns a ceiling-0 rule.
//! - `def_env_closed_b_sound` — a successful `defval_for` lookup on a
//!   checker-true def env returns a ceiling-0 value.
//! - `ceiling_zero_le` — `nat_eqb (bvar_ceiling e) 0 = true -> Le
//!   (bvar_ceiling e) d` for ANY d (nat_eqb_eq + le_zero_n transport), the
//!   bridge into the two IN-TREE keystones.
//!
//! Generic interface discharge (one per closure interface):
//! - `rec_env_closed_of_b : rec_env_closed_b env = true -> RecEnvClosed env`
//! - `rec_env_lift_closed_of_b : ... -> RecEnvLiftClosed env`
//! - `def_env_closed_of_b : ... -> DefEnvClosed env`
//! - `def_env_lift_closed_of_b : ... -> DefEnvLiftClosed env`
//!
//! Regression demo (the Stage-1 gate; nothing carried is discharged yet, so
//! there is NO masquerade risk): all four interfaces instantiated at the toy
//! `faithful_red_env`, each by the single-rfl route
//! `<interface>_of_b (red_* env) (Eq.refl Bool Bool.true)`. (The former
//! `the_red_env` demos were deleted by the Front #1 Stage-3 swap: the real
//! reflected rule RHSs are closed lambdas, which the bvar-free ceiling-0 test
//! honestly rejects — the post-swap the_red_env closure discharge is the
//! depth-aware b2 route in `env_closed_checkers_depth.rs`.)
//!
//! ## Anti-masquerade
//!
//! ZERO new axioms (census stays 11). The checkers are value-ful recursive
//! defs; every lemma/witness is a real `DerivedProved` term with empty
//! axiom_deps. The demo witnesses are NEW names (the faithful i3-i6 witnesses
//! from R2 are untouched); no carried hypothesis is silently replaced.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// A `DerivedProved`, zero-axiom-dep `SpecDefinition` (local mirror of the
    /// `fre_eq_lemma` helper, which is private to `faithful_red_env.rs`).
    fn ecc_lemma(
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

    /// Register Front #1 Stage 1: the closure checkers, the generic
    /// checker-soundness lemmas, and the both-toys regression demo.
    pub(super) fn add_env_closed_checkers(&mut self) -> Result<(), SpecError> {
        self.add_env_closed_checker_defs()?;
        self.add_env_closed_checker_soundness()?;
        self.add_env_closed_generic_discharge()?;
        self.add_env_closed_checker_demo()?;
        Ok(())
    }

    /// The five checkers. Same recursion shape as the proven lookup folds
    /// (`recrule_in_rules` / `recrules_for` / `defval_for`): match on the list
    /// structure, self-call as a plain argument to a helper (`Bool.and`), so
    /// the kernel whnf-evaluates them over any concrete env.
    pub(super) fn add_env_closed_checker_defs(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            r"def rec_rules_closed_b (rs : RecRules) : Bool := match rs with
| RecRules.nil => Bool.true
| RecRules.cons r rest => Bool.and (nat_eqb (bvar_ceiling (recrule_rhs r)) Nat.zero) (rec_rules_closed_b rest)",
            "Closure checker for a recursor rule list: every rule's rhs has bvar_ceiling 0 \
             (closed). Kernel-evaluable fold; the RecRules leg of rec_env_closed_b. \
             Front #1 Stage 1 (checker pattern).",
        )?;

        self.add_recursive_def(
            r"def rec_env_closed_b (env : RecEnv) : Bool := match env with
| RecEnv.empty => Bool.true
| RecEnv.addRec tail rname mta rules => Bool.and (rec_rules_closed_b rules) (rec_env_closed_b tail)",
            "Closure checker for a recursor environment: every registered recursor's rule list \
             passes rec_rules_closed_b (all rule rhs closed). Kernel-evaluable fold; a concrete \
             env discharges RecEnvClosed by rec_env_closed_of_b + a single Eq.refl Bool.true. \
             Front #1 Stage 1 (checker pattern).",
        )?;

        // Lift alias: closedness (ceiling 0) is THE SAME decidable test for the
        // inst and lift interfaces — only the keystone that discharges the
        // interface field differs (inst_above_ceiling_id vs lift_ceiling_id).
        // A distinct name keeps the checker<->interface pairing uniform for the
        // Stage-2 reflection generator.
        self.add_recursive_def(
            r"def rec_env_lift_closed_b (env : RecEnv) : Bool := rec_env_closed_b env",
            "Lift-closure checker for a recursor environment: alias of rec_env_closed_b \
             (closedness is one test; the lift interface differs only in the discharging \
             keystone lift_ceiling_id). Front #1 Stage 1 (checker pattern).",
        )?;

        self.add_recursive_def(
            r"def def_env_closed_b (env : DefEnv) : Bool := match env with
| DefEnv.empty => Bool.true
| DefEnv.addDef tail dname val => Bool.and (nat_eqb (bvar_ceiling val) Nat.zero) (def_env_closed_b tail)",
            "Closure checker for a definition environment: every registered definition's value \
             has bvar_ceiling 0 (closed). Kernel-evaluable fold; a concrete env discharges \
             DefEnvClosed by def_env_closed_of_b + a single Eq.refl Bool.true. \
             Front #1 Stage 1 (checker pattern).",
        )?;

        self.add_recursive_def(
            r"def def_env_lift_closed_b (env : DefEnv) : Bool := def_env_closed_b env",
            "Lift-closure checker for a definition environment: alias of def_env_closed_b \
             (closedness is one test; the lift interface differs only in the discharging \
             keystone lift_ceiling_id). Front #1 Stage 1 (checker pattern).",
        )?;

        Ok(())
    }

    /// The fold-membership soundness lemmas: checker-true implies every
    /// looked-up element passes the per-element test. Structural induction
    /// (RecEnv.rec / RecRules.rec / DefEnv.rec) + `opt_pick_some_inv` on the
    /// lookup fold; the checker unfolds definitionally on the constructor-
    /// headed scrutinee, so `band_eq_true_left/right` split each fold step.
    fn add_env_closed_checker_soundness(&mut self) -> Result<(), SpecError> {
        // ceiling_zero_le: the bridge from the checker's per-element test to the
        // keystones' Le side-condition. nat_eqb true -> ceiling = 0 (nat_eqb_eq),
        // then Le 0 d (le_zero_n) transported backwards along the equation.
        self.add_definition(Self::ecc_lemma(
            "ceiling_zero_le",
            "forall (e : KExpr) (d : Nat), \
             Eq Bool (nat_eqb (bvar_ceiling e) Nat.zero) Bool.true -> Le (bvar_ceiling e) d",
            "fun (e : KExpr) (d : Nat) \
             (h : Eq Bool (nat_eqb (bvar_ceiling e) Nat.zero) Bool.true) => \
             Eq.subst Nat (fun (z : Nat) => Le z d) Nat.zero (bvar_ceiling e) \
             (Eq.symm Nat (bvar_ceiling e) Nat.zero \
             (nat_eqb_eq (bvar_ceiling e) Nat.zero h)) \
             (le_zero_n d)",
            "Checker-test bridge: nat_eqb (bvar_ceiling e) 0 = true -> Le (bvar_ceiling e) d for \
             ANY d. nat_eqb_eq pins the ceiling to 0; le_zero_n gives Le 0 d; Eq.subst transports. \
             Feeds inst_above_ceiling_id / lift_ceiling_id. DerivedProved, zero axiom_deps. \
             Front #1 Stage 1 (checker soundness).",
            &[
                "nat_eqb",
                "nat_eqb_eq",
                "bvar_ceiling",
                "le_zero_n",
                "Le",
                "Eq.subst",
                "Eq.symm",
            ],
        ))?;

        // rec_rules_closed_b_sound: the RULES-level fold-membership induction.
        // A successful recrule_in_rules lookup on a checker-true list returns a
        // rule whose rhs passes the ceiling-0 test. RecRules.rec; nil is absurd
        // (lookup = none), cons splits the opt_pick fire/fall-through.
        self.add_definition(Self::ecc_lemma(
            "rec_rules_closed_b_sound",
            "forall (rs : RecRules) (cname : Name) (rule : RecRule), \
             Eq (OptionType RecRule) (recrule_in_rules rs cname) (OptionType.some RecRule rule) -> \
             Eq Bool (rec_rules_closed_b rs) Bool.true -> \
             Eq Bool (nat_eqb (bvar_ceiling (recrule_rhs rule)) Nat.zero) Bool.true",
            "fun (rs : RecRules) (cname : Name) (rule : RecRule) => \
             RecRules.rec \
             (fun (l : RecRules) => \
             Eq (OptionType RecRule) (recrule_in_rules l cname) (OptionType.some RecRule rule) -> \
             Eq Bool (rec_rules_closed_b l) Bool.true -> \
             Eq Bool (nat_eqb (bvar_ceiling (recrule_rhs rule)) Nat.zero) Bool.true) \
             (fun (hlk : Eq (OptionType RecRule) (recrule_in_rules RecRules.nil cname) (OptionType.some RecRule rule)) \
             (_hb : Eq Bool (rec_rules_closed_b RecRules.nil) Bool.true) => \
             option_none_ne_some RecRule rule \
             (Eq Bool (nat_eqb (bvar_ceiling (recrule_rhs rule)) Nat.zero) Bool.true) hlk) \
             (fun (r : RecRule) (rest : RecRules) \
             (ih : Eq (OptionType RecRule) (recrule_in_rules rest cname) (OptionType.some RecRule rule) -> \
             Eq Bool (rec_rules_closed_b rest) Bool.true -> \
             Eq Bool (nat_eqb (bvar_ceiling (recrule_rhs rule)) Nat.zero) Bool.true) \
             (hlk : Eq (OptionType RecRule) (recrule_in_rules (RecRules.cons r rest) cname) (OptionType.some RecRule rule)) \
             (hb : Eq Bool (rec_rules_closed_b (RecRules.cons r rest)) Bool.true) => \
             opt_pick_some_inv RecRule (name_eqb (recrule_ctor_name r) cname) r \
             (recrule_in_rules rest cname) rule \
             (Eq Bool (nat_eqb (bvar_ceiling (recrule_rhs rule)) Nat.zero) Bool.true) hlk \
             (fun (_ht : Eq Bool (name_eqb (recrule_ctor_name r) cname) Bool.true) \
             (hval : Eq RecRule r rule) => \
             Eq.subst RecRule \
             (fun (z : RecRule) => Eq Bool (nat_eqb (bvar_ceiling (recrule_rhs z)) Nat.zero) Bool.true) \
             r rule hval \
             (band_eq_true_left (nat_eqb (bvar_ceiling (recrule_rhs r)) Nat.zero) (rec_rules_closed_b rest) hb)) \
             (fun (_hf : Eq Bool (name_eqb (recrule_ctor_name r) cname) Bool.false) \
             (hrest : Eq (OptionType RecRule) (recrule_in_rules rest cname) (OptionType.some RecRule rule)) => \
             ih hrest \
             (band_eq_true_right (nat_eqb (bvar_ceiling (recrule_rhs r)) Nat.zero) (rec_rules_closed_b rest) hb))) \
             rs",
            "Fold-membership (rules level): recrule_in_rules rs cname = some rule and \
             rec_rules_closed_b rs = true imply nat_eqb (bvar_ceiling (recrule_rhs rule)) 0 = true. \
             RecRules.rec; nil lookup is absurd (option_none_ne_some); cons splits the opt_pick \
             fire (transport the left band conjunct along r = rule) / fall-through (IH on the \
             right band conjunct). DerivedProved, zero axiom_deps. Front #1 Stage 1 (checker soundness).",
            &[
                "RecRules.rec",
                "recrule_in_rules",
                "recrule_ctor_name",
                "recrule_rhs",
                "rec_rules_closed_b",
                "opt_pick_some_inv",
                "option_none_ne_some",
                "band_eq_true_left",
                "band_eq_true_right",
                "name_eqb",
                "nat_eqb",
                "bvar_ceiling",
                "Eq.subst",
            ],
        ))?;

        // rec_env_closed_b_sound: the ENV-level fold-membership induction.
        // A successful recrules_for lookup on a checker-true env returns a
        // checker-true rule list. RecEnv.rec; same fire/fall-through split.
        self.add_definition(Self::ecc_lemma(
            "rec_env_closed_b_sound",
            "forall (env : RecEnv) (rname : Name) (rules : RecRules), \
             Eq (OptionType RecRules) (recrules_for env rname) (OptionType.some RecRules rules) -> \
             Eq Bool (rec_env_closed_b env) Bool.true -> \
             Eq Bool (rec_rules_closed_b rules) Bool.true",
            "fun (env : RecEnv) (rname : Name) (rules : RecRules) => \
             RecEnv.rec \
             (fun (e : RecEnv) => \
             Eq (OptionType RecRules) (recrules_for e rname) (OptionType.some RecRules rules) -> \
             Eq Bool (rec_env_closed_b e) Bool.true -> \
             Eq Bool (rec_rules_closed_b rules) Bool.true) \
             (fun (hlk : Eq (OptionType RecRules) (recrules_for RecEnv.empty rname) (OptionType.some RecRules rules)) \
             (_hb : Eq Bool (rec_env_closed_b RecEnv.empty) Bool.true) => \
             option_none_ne_some RecRules rules \
             (Eq Bool (rec_rules_closed_b rules) Bool.true) hlk) \
             (fun (tail : RecEnv) (rn : Name) (mta : RecMeta) (rls : RecRules) \
             (ih : Eq (OptionType RecRules) (recrules_for tail rname) (OptionType.some RecRules rules) -> \
             Eq Bool (rec_env_closed_b tail) Bool.true -> \
             Eq Bool (rec_rules_closed_b rules) Bool.true) \
             (hlk : Eq (OptionType RecRules) (recrules_for (RecEnv.addRec tail rn mta rls) rname) (OptionType.some RecRules rules)) \
             (hb : Eq Bool (rec_env_closed_b (RecEnv.addRec tail rn mta rls)) Bool.true) => \
             opt_pick_some_inv RecRules (name_eqb rn rname) rls \
             (recrules_for tail rname) rules \
             (Eq Bool (rec_rules_closed_b rules) Bool.true) hlk \
             (fun (_ht : Eq Bool (name_eqb rn rname) Bool.true) \
             (hval : Eq RecRules rls rules) => \
             Eq.subst RecRules \
             (fun (z : RecRules) => Eq Bool (rec_rules_closed_b z) Bool.true) \
             rls rules hval \
             (band_eq_true_left (rec_rules_closed_b rls) (rec_env_closed_b tail) hb)) \
             (fun (_hf : Eq Bool (name_eqb rn rname) Bool.false) \
             (htail : Eq (OptionType RecRules) (recrules_for tail rname) (OptionType.some RecRules rules)) => \
             ih htail \
             (band_eq_true_right (rec_rules_closed_b rls) (rec_env_closed_b tail) hb))) \
             env",
            "Fold-membership (env level): recrules_for env rname = some rules and \
             rec_env_closed_b env = true imply rec_rules_closed_b rules = true. RecEnv.rec; empty \
             lookup is absurd (option_none_ne_some); addRec splits the opt_pick fire (transport \
             the left band conjunct along rls = rules) / fall-through (IH on the right band \
             conjunct). DerivedProved, zero axiom_deps. Front #1 Stage 1 (checker soundness).",
            &[
                "RecEnv.rec",
                "recrules_for",
                "rec_env_closed_b",
                "rec_rules_closed_b",
                "opt_pick_some_inv",
                "option_none_ne_some",
                "band_eq_true_left",
                "band_eq_true_right",
                "name_eqb",
                "Eq.subst",
            ],
        ))?;

        // def_env_closed_b_sound: the DEF-ENV fold-membership induction (single-
        // level lookup, so the env and element steps fuse). DefEnv.rec.
        self.add_definition(Self::ecc_lemma(
            "def_env_closed_b_sound",
            "forall (env : DefEnv) (dname : Name) (defval : KExpr), \
             Eq (OptionType KExpr) (defval_for env dname) (OptionType.some KExpr defval) -> \
             Eq Bool (def_env_closed_b env) Bool.true -> \
             Eq Bool (nat_eqb (bvar_ceiling defval) Nat.zero) Bool.true",
            "fun (env : DefEnv) (dname : Name) (defval : KExpr) => \
             DefEnv.rec \
             (fun (e : DefEnv) => \
             Eq (OptionType KExpr) (defval_for e dname) (OptionType.some KExpr defval) -> \
             Eq Bool (def_env_closed_b e) Bool.true -> \
             Eq Bool (nat_eqb (bvar_ceiling defval) Nat.zero) Bool.true) \
             (fun (hlk : Eq (OptionType KExpr) (defval_for DefEnv.empty dname) (OptionType.some KExpr defval)) \
             (_hb : Eq Bool (def_env_closed_b DefEnv.empty) Bool.true) => \
             option_none_ne_some KExpr defval \
             (Eq Bool (nat_eqb (bvar_ceiling defval) Nat.zero) Bool.true) hlk) \
             (fun (tail : DefEnv) (dn : Name) (dv : KExpr) \
             (ih : Eq (OptionType KExpr) (defval_for tail dname) (OptionType.some KExpr defval) -> \
             Eq Bool (def_env_closed_b tail) Bool.true -> \
             Eq Bool (nat_eqb (bvar_ceiling defval) Nat.zero) Bool.true) \
             (hlk : Eq (OptionType KExpr) (defval_for (DefEnv.addDef tail dn dv) dname) (OptionType.some KExpr defval)) \
             (hb : Eq Bool (def_env_closed_b (DefEnv.addDef tail dn dv)) Bool.true) => \
             opt_pick_some_inv KExpr (name_eqb dn dname) dv \
             (defval_for tail dname) defval \
             (Eq Bool (nat_eqb (bvar_ceiling defval) Nat.zero) Bool.true) hlk \
             (fun (_ht : Eq Bool (name_eqb dn dname) Bool.true) \
             (hval : Eq KExpr dv defval) => \
             Eq.subst KExpr \
             (fun (z : KExpr) => Eq Bool (nat_eqb (bvar_ceiling z) Nat.zero) Bool.true) \
             dv defval hval \
             (band_eq_true_left (nat_eqb (bvar_ceiling dv) Nat.zero) (def_env_closed_b tail) hb)) \
             (fun (_hf : Eq Bool (name_eqb dn dname) Bool.false) \
             (htail : Eq (OptionType KExpr) (defval_for tail dname) (OptionType.some KExpr defval)) => \
             ih htail \
             (band_eq_true_right (nat_eqb (bvar_ceiling dv) Nat.zero) (def_env_closed_b tail) hb))) \
             env",
            "Fold-membership (def-env level): defval_for env dname = some defval and \
             def_env_closed_b env = true imply nat_eqb (bvar_ceiling defval) 0 = true. DefEnv.rec; \
             empty lookup is absurd (option_none_ne_some); addDef splits the opt_pick fire \
             (transport the left band conjunct along dv = defval) / fall-through (IH on the right \
             band conjunct). DerivedProved, zero axiom_deps. Front #1 Stage 1 (checker soundness).",
            &[
                "DefEnv.rec",
                "defval_for",
                "def_env_closed_b",
                "opt_pick_some_inv",
                "option_none_ne_some",
                "band_eq_true_left",
                "band_eq_true_right",
                "name_eqb",
                "nat_eqb",
                "bvar_ceiling",
                "Eq.subst",
            ],
        ))?;

        Ok(())
    }

    /// The four generic interface-discharge lemmas: checker-true -> interface.
    /// Decompose the interface's `recrule_for` lookup (opt_bind_some_inv), run
    /// the fold-membership chain to the per-element ceiling-0 fact, bridge to
    /// Le (ceiling_zero_le), and close with the IN-TREE keystone
    /// (inst_above_ceiling_id / lift_ceiling_id).
    fn add_env_closed_generic_discharge(&mut self) -> Result<(), SpecError> {
        // rec_env_closed_of_b: checker-true -> RecEnvClosed.
        self.add_definition(Self::ecc_lemma(
            "rec_env_closed_of_b",
            "forall (env : RecEnv), \
             Eq Bool (rec_env_closed_b env) Bool.true -> RecEnvClosed env",
            "fun (env : RecEnv) (hb : Eq Bool (rec_env_closed_b env) Bool.true) => \
             RecEnvClosed.mk env \
             (fun (rname : Name) (cname : Name) (rule : RecRule) (val : KExpr) (depth : Nat) \
             (hlk : Eq (OptionType RecRule) (recrule_for env rname cname) (OptionType.some RecRule rule)) => \
             opt_bind_some_inv RecRules RecRule (recrules_for env rname) \
             (fun (rules : RecRules) => recrule_in_rules rules cname) rule \
             (Eq KExpr (instantiate_at (recrule_rhs rule) val depth) (recrule_rhs rule)) hlk \
             (fun (rules : RecRules) \
             (hrules : Eq (OptionType RecRules) (recrules_for env rname) (OptionType.some RecRules rules)) \
             (hin : Eq (OptionType RecRule) (recrule_in_rules rules cname) (OptionType.some RecRule rule)) => \
             inst_above_ceiling_id (recrule_rhs rule) val depth \
             (ceiling_zero_le (recrule_rhs rule) depth \
             (rec_rules_closed_b_sound rules cname rule hin \
             (rec_env_closed_b_sound env rname rules hrules hb)))))",
            "GENERIC checker soundness (inst): rec_env_closed_b env = true -> RecEnvClosed env, \
             for ANY env. Decompose the recrule_for lookup (opt_bind_some_inv), chain the two \
             fold-membership lemmas to the rule's ceiling-0 fact, bridge to Le (ceiling_zero_le), \
             close with the keystone inst_above_ceiling_id. A concrete env now discharges \
             RecEnvClosed by a single Eq.refl Bool Bool.true (the kernel evaluates the checker). \
             DerivedProved, zero axiom_deps. Front #1 Stage 1 (generic discharge).",
            &[
                "RecEnvClosed",
                "RecEnvClosed.mk",
                "rec_env_closed_b",
                "rec_env_closed_b_sound",
                "rec_rules_closed_b_sound",
                "ceiling_zero_le",
                "inst_above_ceiling_id",
                "opt_bind_some_inv",
                "recrule_for",
                "recrules_for",
                "recrule_in_rules",
                "recrule_rhs",
                "instantiate_at",
            ],
        ))?;

        // rec_env_lift_closed_of_b: checker-true -> RecEnvLiftClosed. Same
        // membership chain (the lift checker is the alias); the keystone swaps
        // to lift_ceiling_id.
        self.add_definition(Self::ecc_lemma(
            "rec_env_lift_closed_of_b",
            "forall (env : RecEnv), \
             Eq Bool (rec_env_lift_closed_b env) Bool.true -> RecEnvLiftClosed env",
            "fun (env : RecEnv) (hb : Eq Bool (rec_env_lift_closed_b env) Bool.true) => \
             RecEnvLiftClosed.mk env \
             (fun (rname : Name) (cname : Name) (rule : RecRule) (cutoff : Nat) (amount : Nat) \
             (hlk : Eq (OptionType RecRule) (recrule_for env rname cname) (OptionType.some RecRule rule)) => \
             opt_bind_some_inv RecRules RecRule (recrules_for env rname) \
             (fun (rules : RecRules) => recrule_in_rules rules cname) rule \
             (Eq KExpr (lift_at (recrule_rhs rule) cutoff amount) (recrule_rhs rule)) hlk \
             (fun (rules : RecRules) \
             (hrules : Eq (OptionType RecRules) (recrules_for env rname) (OptionType.some RecRules rules)) \
             (hin : Eq (OptionType RecRule) (recrule_in_rules rules cname) (OptionType.some RecRule rule)) => \
             lift_ceiling_id (recrule_rhs rule) cutoff amount \
             (ceiling_zero_le (recrule_rhs rule) cutoff \
             (rec_rules_closed_b_sound rules cname rule hin \
             (rec_env_closed_b_sound env rname rules hrules hb)))))",
            "GENERIC checker soundness (lift): rec_env_lift_closed_b env = true -> \
             RecEnvLiftClosed env, for ANY env. Same fold-membership chain as \
             rec_env_closed_of_b (the lift checker is the closedness alias); the interface field \
             closes with the lift keystone lift_ceiling_id instead. DerivedProved, zero \
             axiom_deps. Front #1 Stage 1 (generic discharge).",
            &[
                "RecEnvLiftClosed",
                "RecEnvLiftClosed.mk",
                "rec_env_lift_closed_b",
                "rec_env_closed_b_sound",
                "rec_rules_closed_b_sound",
                "ceiling_zero_le",
                "lift_ceiling_id",
                "opt_bind_some_inv",
                "recrule_for",
                "recrules_for",
                "recrule_in_rules",
                "recrule_rhs",
                "lift_at",
            ],
        ))?;

        // def_env_closed_of_b: checker-true -> DefEnvClosed (single-level lookup,
        // so the discharge is one membership call + the keystone).
        self.add_definition(Self::ecc_lemma(
            "def_env_closed_of_b",
            "forall (env : DefEnv), \
             Eq Bool (def_env_closed_b env) Bool.true -> DefEnvClosed env",
            "fun (env : DefEnv) (hb : Eq Bool (def_env_closed_b env) Bool.true) => \
             DefEnvClosed.mk env \
             (fun (dname : Name) (defval : KExpr) (subval : KExpr) (depth : Nat) \
             (hlk : Eq (OptionType KExpr) (defval_for env dname) (OptionType.some KExpr defval)) => \
             inst_above_ceiling_id defval subval depth \
             (ceiling_zero_le defval depth \
             (def_env_closed_b_sound env dname defval hlk hb)))",
            "GENERIC checker soundness (inst): def_env_closed_b env = true -> DefEnvClosed env, \
             for ANY env. The def-env fold-membership lemma pins the looked-up value's ceiling to \
             0; ceiling_zero_le bridges to Le; inst_above_ceiling_id closes. A concrete env now \
             discharges DefEnvClosed by a single Eq.refl Bool Bool.true. DerivedProved, zero \
             axiom_deps. Front #1 Stage 1 (generic discharge).",
            &[
                "DefEnvClosed",
                "DefEnvClosed.mk",
                "def_env_closed_b",
                "def_env_closed_b_sound",
                "ceiling_zero_le",
                "inst_above_ceiling_id",
                "defval_for",
                "instantiate_at",
            ],
        ))?;

        // def_env_lift_closed_of_b: checker-true -> DefEnvLiftClosed.
        self.add_definition(Self::ecc_lemma(
            "def_env_lift_closed_of_b",
            "forall (env : DefEnv), \
             Eq Bool (def_env_lift_closed_b env) Bool.true -> DefEnvLiftClosed env",
            "fun (env : DefEnv) (hb : Eq Bool (def_env_lift_closed_b env) Bool.true) => \
             DefEnvLiftClosed.mk env \
             (fun (dname : Name) (defval : KExpr) (cutoff : Nat) (amount : Nat) \
             (hlk : Eq (OptionType KExpr) (defval_for env dname) (OptionType.some KExpr defval)) => \
             lift_ceiling_id defval cutoff amount \
             (ceiling_zero_le defval cutoff \
             (def_env_closed_b_sound env dname defval hlk hb)))",
            "GENERIC checker soundness (lift): def_env_lift_closed_b env = true -> \
             DefEnvLiftClosed env, for ANY env. Same membership chain as def_env_closed_of_b \
             (the lift checker is the closedness alias); closes with lift_ceiling_id. \
             DerivedProved, zero axiom_deps. Front #1 Stage 1 (generic discharge).",
            &[
                "DefEnvLiftClosed",
                "DefEnvLiftClosed.mk",
                "def_env_lift_closed_b",
                "def_env_closed_b_sound",
                "ceiling_zero_le",
                "lift_ceiling_id",
                "defval_for",
                "lift_at",
            ],
        ))?;

        Ok(())
    }

    /// REGRESSION DEMO (the Stage-1 gate): every closure interface at the toy
    /// `faithful_red_env`, each by the single-rfl route. The kernel must
    /// whnf-EVALUATE the checker fold over the concrete env down to Bool.true
    /// for the Eq.refl to typecheck — this is the property Stage 2's
    /// reflection generator relies on. Nothing carried is discharged (the
    /// retirement metatheory still consumes the CARRIED RedEnvFaithful
    /// bundle) — no masquerade.
    ///
    /// Front #1 Stage 3 NOTE: the four `the_red_env_*_via_checker` demos that
    /// used to live here are DELETED by the swap — the ceiling-0 test is an
    /// over-approximation that only certifies bvar-FREE terms, and the real
    /// reflected rule RHSs / def values are closed LAMBDAS (0/36 bvar-free),
    /// so the Stage-1 checker honestly evaluates to Bool.false over the
    /// post-swap the_red_env. The real-env closure discharge lives in the
    /// depth-aware b2 route (`env_closed_checkers_depth.rs`, the
    /// `the_red_env_*_via_checker_b2` Stage-4 witnesses).
    fn add_env_closed_checker_demo(&mut self) -> Result<(), SpecError> {
        // (name, type, value, env description)
        let demos: [(&str, String, &str, &str); 4] = [
            (
                "faithful_red_env_rec_closed_via_checker",
                "RecEnvClosed (red_rec faithful_red_env)".to_string(),
                "rec_env_closed_of_b (red_rec faithful_red_env) (Eq.refl Bool Bool.true)",
                "faithful_red_env (closed-lambda rule rhs)",
            ),
            (
                "faithful_red_env_rec_lift_closed_via_checker",
                "RecEnvLiftClosed (red_rec faithful_red_env)".to_string(),
                "rec_env_lift_closed_of_b (red_rec faithful_red_env) (Eq.refl Bool Bool.true)",
                "faithful_red_env (closed-lambda rule rhs)",
            ),
            (
                "faithful_red_env_def_closed_via_checker",
                "DefEnvClosed (red_def faithful_red_env)".to_string(),
                "def_env_closed_of_b (red_def faithful_red_env) (Eq.refl Bool Bool.true)",
                "faithful_red_env (closed-lambda def value)",
            ),
            (
                "faithful_red_env_def_lift_closed_via_checker",
                "DefEnvLiftClosed (red_def faithful_red_env)".to_string(),
                "def_env_lift_closed_of_b (red_def faithful_red_env) (Eq.refl Bool Bool.true)",
                "faithful_red_env (closed-lambda def value)",
            ),
        ];

        for (name, type_src, value_src, env_desc) in demos {
            let env_dep = "faithful_red_env";
            // The generic lemma this demo routes through is the value's head.
            let of_b = value_src
                .split_whitespace()
                .next()
                .expect("demo value_src starts with the generic lemma name");
            self.add_definition(Self::ecc_lemma(
                name,
                &type_src,
                value_src,
                &format!(
                    "Regression demo (Front #1 Stage 1 gate): {type_src} discharged over \
                     {env_desc} by the SINGLE-RFL checker route — {of_b} + Eq.refl Bool \
                     Bool.true; the kernel whnf-evaluates the checker fold over the concrete \
                     env. Demo only: the carried RedEnvFaithful hypotheses are untouched (no \
                     masquerade). DerivedProved, zero axiom_deps."
                ),
                &[of_b, env_dep, "Eq.refl"],
            ))?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::spec::types::{AxiomCategory, ProofStatus};
    use crate::test_utils::build_spec_with_stack;

    /// All five checkers register as value-ful, non-axiom recursive defs
    /// (DerivedPending, the standard status for elaborated defs — like
    /// bvar_ceiling / recrules_for), with no axiom blockers.
    #[test]
    fn test_env_closed_checkers_are_valueful_defs() {
        let spec = build_spec_with_stack();
        for name in [
            "rec_rules_closed_b",
            "rec_env_closed_b",
            "rec_env_lift_closed_b",
            "def_env_closed_b",
            "def_env_lift_closed_b",
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

    /// The fold-membership + generic discharge lemmas are real DerivedProved
    /// terms (zero axiom_deps) and re-typecheck against the live kernel env.
    #[test]
    fn test_checker_soundness_lemmas_are_derived_proved_zero_axioms() {
        let spec = build_spec_with_stack();
        for name in [
            "ceiling_zero_le",
            "rec_rules_closed_b_sound",
            "rec_env_closed_b_sound",
            "def_env_closed_b_sound",
            "rec_env_closed_of_b",
            "rec_env_lift_closed_of_b",
            "def_env_closed_of_b",
            "def_env_lift_closed_of_b",
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
            assert!(
                def.value_src.is_some(),
                "{name} must carry a constructive proof term"
            );
            spec.verify_definition(name)
                .unwrap_or_else(|e| panic!("{name} should elaborate and type-check: {e:?}"));
        }
    }

    /// THE STAGE-1 GATE: the toy faithful_red_env discharges the full
    /// closure-interface bundle by the single-rfl checker route. The
    /// registration itself already kernel-checked each Eq.refl (the checker
    /// whnf-evaluated to true over the concrete env); this re-verifies every
    /// witness and pins its status. (The the_red_env ceiling demos are gone:
    /// post-swap, the real env honestly fails the bvar-free ceiling-0 test —
    /// its closure discharge is the depth-aware b2 route.)
    #[test]
    fn test_both_toy_envs_discharge_by_single_rfl() {
        let spec = build_spec_with_stack();
        for name in [
            "faithful_red_env_rec_closed_via_checker",
            "faithful_red_env_rec_lift_closed_via_checker",
            "faithful_red_env_def_closed_via_checker",
            "faithful_red_env_def_lift_closed_via_checker",
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
