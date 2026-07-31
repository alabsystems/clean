// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Env-GENERIC iota/delta DefEq rules from wellformedness (Stage-0 Brick 2).
//!
//! `RecEnvWellformed`/`DefEnvWellformed` (iota_step_bridge.rs / delta_step_bridge.rs)
//! carry the faithfulness fact `WF_SUBST`: every reduction step yields a reduct
//! DefEq to the redex *under any instantiation at any depth* —
//!   `iota_step env e e' -> forall val depth, DefEq (inst e val depth) (inst e' val depth)`.
//! That is intentionally indexed (it is the substitution-stable shape the
//! preservation lanes need). To recover the bare, env-generic single-step rule
//! `iota_step env e e' -> DefEq e e'` we instantiate WF_SUBST at a depth ABOVE
//! both free-variable ceilings, where the Stage-0 Brick-1 keystone
//! `inst_above_ceiling_id` collapses `instantiate_at x v d` back to `x`.
//!
//! Choosing `d := bvar_ceiling e + bvar_ceiling e'` (above BOTH ceilings via
//! `le_add_self_left` / `le_add_self_right`) and any closed `v := sort 0`:
//!   hde : DefEq (inst e v d) (inst e' v d)          -- WF_SUBST projection
//!   ce  : (inst e v d)  = e                          -- keystone, left ceiling
//!   ce' : (inst e' v d) = e'                         -- keystone, right ceiling
//! Transporting `hde` along `ce`, `ce'` (two `Eq.substType` rewrites — DefEq is
//! Type-valued, so the universe-polymorphic transport, the established
//! clean-verify idiom, e.g. typing_def_eq.rs) yields `DefEq e e'`.
//!
//! HONEST PRECONDITION: `RecEnvWellformed env` / `DefEnvWellformed env` is REQUIRED
//! and carried — it is the faithfulness obligation. A lying env cannot witness
//! WF_SUBST without a pre-existing false DefEq, so these rules add NO new trust:
//! zero axioms, both `is_axiom:false`, DerivedProved, empty axiom_deps. They rest
//! only on the carried inductive interfaces + the Brick-1 keystone + foundational
//! Eq/Le lemmas. In a later brick this env-generic shape lets us DELETE the 8
//! standalone iota/delta DefEq axioms (census 140 -> 132). Stage-0 Brick 2.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

// ── The three ι faithfulness fields of `RecEnvWellformed env` (the
// iota_step_bridge.rs WF_* constants, env GENERIC). Used as the explicit binder
// annotations of the `RecEnvWellformed.rec` minor premise.
const REC_WF_SUBST: &str = "forall (e : KExpr) (e' : KExpr), iota_step env e e' -> forall (val : KExpr) (depth : Nat), DefEq (instantiate_at e val depth) (instantiate_at e' val depth)";
const REC_WF_FWD: &str =
    "forall (e : KExpr) (e' : KExpr), iota_step env e e' -> forall (T : KExpr), Typing e T -> Typing e' T";
const REC_WF_BWD: &str =
    "forall (e : KExpr) (e' : KExpr), iota_step env e e' -> forall (T : KExpr), Typing e' T -> Typing e T";

// ── The three δ faithfulness fields of `DefEnvWellformed env` (the
// delta_step_bridge.rs DEF_WF_* constants, env GENERIC; reads `red_def env`).
const DEF_WF_SUBST: &str = "forall (e : KExpr) (e' : KExpr), delta_step (red_def env) e e' -> forall (val : KExpr) (depth : Nat), DefEq (instantiate_at e val depth) (instantiate_at e' val depth)";
const DEF_WF_FWD: &str = "forall (e : KExpr) (e' : KExpr), delta_step (red_def env) e e' -> forall (T : KExpr), Typing e T -> Typing e' T";
const DEF_WF_BWD: &str = "forall (e : KExpr) (e' : KExpr), delta_step (red_def env) e e' -> forall (T : KExpr), Typing e' T -> Typing e T";

/// The shared transport body, parametric only in the WF_SUBST field `hs`. The
/// depth `d := add (ceil e) (ceil e')` is above both ceilings; `v := sort 0` is
/// any closed expression. `hs e e' s v d : DefEq (inst e v d) (inst e' v d)` is
/// transported left and right by `inst_above_ceiling_id` to `DefEq e e'`.
///
/// Identical for ι and δ: the only difference (the step proof `s`'s type) is
/// absorbed by `hs`, which already has the matching shape in each interface.
const TRANSPORT_BODY: &str = concat!(
    "Eq.substType KExpr ",
    "(fun (x : KExpr) => DefEq x e') ",
    "(instantiate_at e (KExpr.sort Level.zero) (Nat.add (bvar_ceiling e) (bvar_ceiling e'))) ",
    "e ",
    // ce : (inst e v d) = e   (left ceiling: ceil e <= ceil e + ceil e')
    "(inst_above_ceiling_id e (KExpr.sort Level.zero) ",
    "(Nat.add (bvar_ceiling e) (bvar_ceiling e')) ",
    "(le_add_self_left (bvar_ceiling e) (bvar_ceiling e'))) ",
    // inner transport: DefEq (inst e v d) (inst e' v d) -> DefEq (inst e v d) e'
    "(Eq.substType KExpr ",
    "(fun (y : KExpr) => DefEq ",
    "(instantiate_at e (KExpr.sort Level.zero) (Nat.add (bvar_ceiling e) (bvar_ceiling e'))) y) ",
    "(instantiate_at e' (KExpr.sort Level.zero) (Nat.add (bvar_ceiling e) (bvar_ceiling e'))) ",
    "e' ",
    // ce' : (inst e' v d) = e'   (right ceiling: ceil e' <= ceil e + ceil e')
    "(inst_above_ceiling_id e' (KExpr.sort Level.zero) ",
    "(Nat.add (bvar_ceiling e) (bvar_ceiling e')) ",
    "(le_add_self_right (bvar_ceiling e) (bvar_ceiling e'))) ",
    // hde : DefEq (inst e v d) (inst e' v d)   (project WF_SUBST, apply at v, d)
    "(hs e e' s (KExpr.sort Level.zero) (Nat.add (bvar_ceiling e) (bvar_ceiling e'))))",
);

impl Specification {
    /// Stage-0 Brick 2: `DefEq.iota_gen` + `DefEq.delta_gen`. Env-generic
    /// single-step iota/delta DefEq rules, proven (zero axioms) from the carried
    /// `RecEnvWellformed`/`DefEnvWellformed` faithful interface + the Brick-1
    /// keystone. Must run AFTER `add_expr_model_inst_ceiling`
    /// (inst_above_ceiling_id/bvar_ceiling/le_add_self_right), `add_iota_step_bridge`
    /// (RecEnvWellformed), `add_delta_step_bridge` (DefEnvWellformed), and whatever
    /// defines DefEq/iota_step/delta_step/red_def + le_add_self_left.
    pub(super) fn add_defeq_iota_delta_gen(&mut self) -> Result<(), SpecError> {
        // DefEq.iota_gen: forall env, RecEnvWellformed env -> forall e e',
        //   iota_step env e e' -> DefEq e e'.
        // Project WF_SUBST from the carried RecEnvWellformed via its recursor
        // (constant motive DefEq e e'), apply at the over-ceiling depth, transport.
        self.add_definition(SpecDefinition {
            name: "DefEq.iota_gen".to_string(),
            type_src: concat!(
                "forall (env : RecEnv), RecEnvWellformed env -> ",
                "forall (e : KExpr) (e' : KExpr), iota_step env e e' -> DefEq e e'"
            )
            .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (env : RecEnv) (w : RecEnvWellformed env) ",
                    "(e : KExpr) (e' : KExpr) (s : iota_step env e e') => ",
                    "RecEnvWellformed.rec env ",
                    "(fun (_ : RecEnvWellformed env) => DefEq e e') ",
                    "(fun (hs : {SUBST}) (hf : {FWD}) (hb : {BWD}) => {BODY}) ",
                    "w"
                ),
                SUBST = REC_WF_SUBST,
                FWD = REC_WF_FWD,
                BWD = REC_WF_BWD,
                BODY = TRANSPORT_BODY,
            )),
            is_axiom: false,
            description: concat!(
                "Env-generic single-step iota DefEq rule: a faithful recursor env (carried ",
                "RecEnvWellformed) makes every iota_step a DefEq. Proven by projecting WF_SUBST ",
                "(via RecEnvWellformed.rec) at a depth above both bvar ceilings, where the Brick-1 ",
                "keystone inst_above_ceiling_id collapses the instantiation, then transporting the ",
                "resulting DefEq with two Eq.substType rewrites. RecEnvWellformed is REQUIRED and ",
                "carried (the faithfulness obligation), NOT an axiom. DerivedProved, zero axiom_deps. ",
                "Stage-0 Brick 2 (unblocks the later iota DefEq-axiom deletions, census 140 -> 132)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "RecEnvWellformed.rec".to_string(),
                "iota_step".to_string(),
                "DefEq".to_string(),
                "Eq.substType".to_string(),
                "inst_above_ceiling_id".to_string(),
                "bvar_ceiling".to_string(),
                "le_add_self_left".to_string(),
                "le_add_self_right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // DefEq.delta_gen: the δ mirror. forall env : RedEnv, DefEnvWellformed env ->
        //   forall e e', delta_step (red_def env) e e' -> DefEq e e'. Same proof
        // shape, projecting WF_SUBST from DefEnvWellformed.
        self.add_definition(SpecDefinition {
            name: "DefEq.delta_gen".to_string(),
            type_src: concat!(
                "forall (env : RedEnv), DefEnvWellformed env -> ",
                "forall (e : KExpr) (e' : KExpr), delta_step (red_def env) e e' -> DefEq e e'"
            )
            .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (env : RedEnv) (w : DefEnvWellformed env) ",
                    "(e : KExpr) (e' : KExpr) (s : delta_step (red_def env) e e') => ",
                    "DefEnvWellformed.rec env ",
                    "(fun (_ : DefEnvWellformed env) => DefEq e e') ",
                    "(fun (hs : {SUBST}) (hf : {FWD}) (hb : {BWD}) => {BODY}) ",
                    "w"
                ),
                SUBST = DEF_WF_SUBST,
                FWD = DEF_WF_FWD,
                BWD = DEF_WF_BWD,
                BODY = TRANSPORT_BODY,
            )),
            is_axiom: false,
            description: concat!(
                "Env-generic single-step delta DefEq rule (the δ mirror of DefEq.iota_gen): a ",
                "faithful definition env (carried DefEnvWellformed) makes every delta_step ",
                "(red_def env) a DefEq. Proven by projecting WF_SUBST (via DefEnvWellformed.rec) at ",
                "a depth above both bvar ceilings, collapsing the instantiation with the Brick-1 ",
                "keystone inst_above_ceiling_id, then two Eq.substType transports. DefEnvWellformed ",
                "is REQUIRED and carried (the faithfulness obligation), NOT an axiom. DerivedProved, ",
                "zero axiom_deps. Stage-0 Brick 2 (unblocks the later delta DefEq-axiom deletions)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "DefEnvWellformed.rec".to_string(),
                "delta_step".to_string(),
                "red_def".to_string(),
                "DefEq".to_string(),
                "Eq.substType".to_string(),
                "inst_above_ceiling_id".to_string(),
                "bvar_ceiling".to_string(),
                "le_add_self_left".to_string(),
                "le_add_self_right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::spec::types::ProofStatus;
    use crate::spec::Specification;
    use crate::test_utils::run_with_stack;

    #[test]
    fn test_defeq_iota_delta_gen_is_constructive() {
        // Build the minimal dependency prefix (through add_defeq_iota_delta_gen)
        // on a large-stack thread — the keystone's KExpr.rec proof recurses
        // deeply. This stops before the par_reduces confluence lane, so the
        // brick is validated independently of that (concurrent) machinery; the
        // proof terms are still fully kernel-checked at add_definition time
        // against the real RecEnvWellformed / DefEnvWellformed / keystone defs.
        let spec = run_with_stack(|| {
            Specification::new_defeq_iota_delta_gen_test_spec()
                .expect("Brick-2 prefix spec should build")
        });

        // Both env-generic rules are DerivedProved, non-axiom, zero-axiom-dep proof
        // terms (kernel-checked at add_definition time, so reaching here means the
        // proofs elaborated and type-checked). NO MASQUERADE: is_axiom:false.
        for name in ["DefEq.iota_gen", "DefEq.delta_gen"] {
            let def = spec
                .definitions()
                .get(name)
                .unwrap_or_else(|| panic!("Missing {name}"));
            assert!(def.value_src.is_some(), "{name} should have a proof term");
            assert!(!def.is_axiom, "{name} should not be an axiom");
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "{name} should be DerivedProved"
            );
            assert!(
                def.axiom_deps.is_empty(),
                "{name} should have no axiom blockers: {:?}",
                def.axiom_deps
            );
        }
    }
}
