// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment G (#2859 computational-iota/delta track): the computational
//! `delta_step` and its determinism — the δ analogue of the Increment C keystone.
//!
//! `delta` unfolds a definitional `const` head to its value, keeping the
//! application spine: `c args… ⇒ val args…`. This is structurally SIMPLER than
//! iota (no recursor rules, no major premise, no segment arithmetic) — a 2-level
//! `opt_bind` on (head-const-name lookup) then (definition-value lookup), then
//! `apply_spine` of the original args over the value. Because `delta_reduct` is a
//! total FUNCTION and `delta_step` is its graph, determinism is free via
//! `OptionType.some` injectivity — exactly as for iota. This closes blocker #1
//! (the δ arm of `whnf_step` had no directed `par`-style step) once bridged.
//! Reuses the iota_step substrate (`opt_bind`, `kapp_fn`, `kapp_args`,
//! `apply_spine`, `kexpr_const_name`) and the rec_env lookup combinators
//! (`name_eqb`, `opt_pick`). See
//! `designs/2026-06-14-computational-iota-delta-track.md` (Increment G).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Core δ substrate (DefEnv / defval_for / delta_reduct / delta_step graph) —
    /// needs only the rec_env lookups (name_eqb/opt_pick) + the iota_step substrate
    /// (opt_bind/kapp_fn/kapp_args/apply_spine/kexpr_const_name), so it can run
    /// BEFORE the reduction families, which the Brick-4 tightening pins to
    /// `the_red_env` (church_rosser_whnf retirement track). The δ keystones that
    /// additionally need the iota CPS-inverter substrate stay in `add_delta_step`.
    pub(super) fn add_delta_step_core(&mut self) -> Result<(), SpecError> {
        // DefEnv: name-keyed association definition-name -> value. Mirrors RecEnv
        // (rec_env.rs) but stores the unfolding value (a KExpr) per defined const.
        self.add_inductive(
            r"inductive DefEnv : Type
| empty : DefEnv
| addDef : DefEnv → Name → KExpr → DefEnv",
            "Definition environment: empty, or a defined constant (by Name) with its unfolding value \
             (a KExpr) added to a tail environment. Name-keyed lookup. Part of #2859 (Increment G).",
        )?;

        // defval_for: the unfolding value of definition `target`, if present.
        // Mirrors recmeta_for (rec_env.rs) — match on env, opt_pick on name_eqb,
        // self-recurse on the tail.
        self.add_recursive_def(
            r"def defval_for (env : DefEnv) (target : Name) : OptionType KExpr := match env with
| DefEnv.empty => OptionType.none KExpr
| DefEnv.addDef tail dname val => opt_pick KExpr (name_eqb dname target) val (defval_for tail target)",
            "Look up a defined constant's unfolding value by name. Part of #2859 (Increment G).",
        )?;

        // delta_reduct: the computational delta reduct. If the head (after kapp_fn)
        // is a const with a definition value in env, unfold it and re-apply the
        // original spine args; else none. A 2-level opt_bind (head const name, then
        // value) + apply_spine. Mirrors iota_reduct but far simpler (no rules).
        self.add_recursive_def(
            r"def delta_reduct (env : DefEnv) (e : KExpr) : OptionType KExpr := opt_bind Name KExpr (kexpr_const_name (kapp_fn e)) (fun (dname : Name) => opt_bind KExpr KExpr (defval_for env dname) (fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args e) val)))",
            "Computational delta reduct: unfold a definitional const head to its value, re-applying the \
             original spine (c args… -> val args…). Total function via opt_bind. Part of #2859 (Increment G).",
        )?;

        // delta_step: the graph of delta_reduct — the directed step e -> e' holds
        // iff delta_reduct env e = some e'. A FUNCTION's graph, so deterministic.
        self.add_recursive_def(
            r"def delta_step (env : DefEnv) (e : KExpr) (e' : KExpr) : Prop := Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e')",
            "Directed delta step: delta_step env e e' holds iff delta_reduct env e = some e'. The graph of \
             the reduct function. Part of #2859 (Increment G).",
        )?;

        Ok(())
    }

    /// The δ keystones that need the iota CPS-inverter substrate (so this runs
    /// AFTER add_iota_subst, unlike the core above): delta_step determinism +
    /// delta_reduct_some_inv + delta_step_head_none_absurd.
    pub(super) fn add_delta_step(&mut self) -> Result<(), SpecError> {
        // delta_step_deterministic: the reduct is unique. Since delta_step is the
        // graph of the FUNCTION delta_reduct, two reducts of the same redex are both
        // equal to delta_reduct env e, hence equal by some-injectivity. The δ
        // analogue of the iota_step_deterministic keystone — the directed,
        // determinate capability the abstract delta_reduces lacked.
        self.add_definition(SpecDefinition {
            name: "delta_step_deterministic".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e1) -> ",
                "Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e2) -> ",
                "Eq KExpr e1 e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : DefEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
                    "(h1 : Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e1)) ",
                    "(h2 : Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e2)) => ",
                    "option_some_inj KExpr e1 e2 ",
                    "(Eq.trans (OptionType KExpr) ",
                    "(OptionType.some KExpr e1) (delta_reduct env e) (OptionType.some KExpr e2) ",
                    "(Eq.symm (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e1) h1) ",
                    "h2)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "delta_step determinism: delta_reduct env e = some e1 and = some e2 imply e1 = e2. Free ",
                "because delta_reduct is a total FUNCTION (graph + some-injectivity). The directed-determinate ",
                "capability the abstract delta_reduces lacked; the δ analogue of iota_step_deterministic. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment G)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_reduct".to_string(),
                "option_some_inj".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // delta_reduct_some_inv: CPS inversion of delta_reduct's 2-level opt_bind
        // chain. From delta_reduct env e = some e', recover the definition name and
        // value with each lookup equation and the reduct equation, delivered to a
        // continuation (the fragment has no Sigma/Exists). The δ analogue of
        // iota_reduct_some_inv (2 levels, not 5). Consumed by delta_step_head_none_
        // absurd and (later) the delta substitution-commutation.
        {
            let reduct = "(apply_spine (kapp_args e) val)";
            let l3 = format!("(fun (val : KExpr) => OptionType.some KExpr {reduct})");
            let l2 =
                format!("(fun (dname : Name) => opt_bind KExpr KExpr (defval_for env dname) {l3})");
            let kont = format!(
                "(forall (dname : Name) (val : KExpr), \
                 Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name dname) -> \
                 Eq (OptionType KExpr) (defval_for env dname) (OptionType.some KExpr val) -> \
                 Eq (OptionType KExpr) (OptionType.some KExpr {reduct}) (OptionType.some KExpr e') -> \
                 C)"
            );
            let value = format!(
                "fun (env : DefEnv) (e : KExpr) (e' : KExpr) (C : Prop) \
                 (h : Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e')) \
                 (k : {kont}) => \
                 opt_bind_some_inv Name KExpr (kexpr_const_name (kapp_fn e)) {l2} e' C h \
                 (fun (dname : Name) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name dname)) \
                 (h1r : Eq (OptionType KExpr) ({l2} dname) (OptionType.some KExpr e')) => \
                 opt_bind_some_inv KExpr KExpr (defval_for env dname) {l3} e' C h1r \
                 (fun (val : KExpr) \
                 (h2 : Eq (OptionType KExpr) (defval_for env dname) (OptionType.some KExpr val)) \
                 (h2r : Eq (OptionType KExpr) ({l3} val) (OptionType.some KExpr e')) => \
                 k dname val h1 h2 h2r))"
            );
            self.add_definition(SpecDefinition {
                name: "delta_reduct_some_inv".to_string(),
                type_src: format!(
                    "forall (env : DefEnv) (e : KExpr) (e' : KExpr) (C : Prop), \
                     Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e') -> {kont} -> C"
                ),
                value_src: Some(value),
                is_axiom: false,
                description: "CPS inversion of delta_reduct's 2-level opt_bind chain: from delta_reduct env e = some e', recover the definition name and value with each lookup equation and the reduct equation some (apply_spine (kapp_args e) val) = some e', delivered to a continuation. Two nested opt_bind_some_inv. The δ analogue of iota_reduct_some_inv. DerivedProved, zero axiom_deps. Part of #2859 (Increment G).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "delta_reduct".to_string(),
                    "opt_bind_some_inv".to_string(),
                    "kexpr_const_name".to_string(),
                    "defval_for".to_string(),
                    "apply_spine".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // delta_step_head_none_absurd: a genuine delta redex is const-headed. If the
        // head const-name is none (a non-const head after kapp_fn) then delta_step is
        // impossible — invert via delta_reduct_some_inv to recover h1 (the head IS
        // some dname), contradict via option_none_ne_some. The δ analogue of
        // iota_step_head_none_absurd (the discharge primitive for the binder/beta
        // arms of the eventual par_strips delta-source case).
        self.add_definition(SpecDefinition {
            name: "delta_step_head_none_absurd".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (e : KExpr) (e' : KExpr) (C : Prop), ",
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.none Name) -> ",
                "delta_step env e e' -> C"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : DefEnv) (e : KExpr) (e' : KExpr) (C : Prop) ",
                    "(hnone : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.none Name)) ",
                    "(h : Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e')) => ",
                    "delta_reduct_some_inv env e e' C h ",
                    "(fun (dname : Name) (val : KExpr) ",
                    "(h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name dname)) ",
                    "(h2 : Eq (OptionType KExpr) (defval_for env dname) (OptionType.some KExpr val)) ",
                    "(h2r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (kapp_args e) val)) (OptionType.some KExpr e')) => ",
                    "option_none_ne_some Name dname C ",
                    "(Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name dname) ",
                    "(Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.none Name) hnone) h1))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "A genuine delta redex is const-headed: if kexpr_const_name (kapp_fn e) = none then delta_step env e e' is impossible. Inverts via delta_reduct_some_inv (recovering h1: the head IS some dname) and contradicts the none-head hypothesis via option_none_ne_some. The δ analogue of iota_step_head_none_absurd. DerivedProved, zero axiom_deps. Part of #2859 (Increment G).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_reduct_some_inv".to_string(),
                "option_none_ne_some".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "delta_step".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
