// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment G (#2859 computational-iota/delta track): the δ substitution /
//! lift commutation substrate — the delta analogue of the Increment E iota
//! E-core (`iota_subst_commutes` / `iota_lift_commutes`).
//!
//! `delta_reduct env e = some (apply_spine (kapp_args e) val)`, where the guarded
//! `kdef_value_at env dname (kexpr_const_levels (kapp_fn e))` returns `some val`.
//! The reduct re-applies the ORIGINAL spine `kapp_args e` over the env's
//! definition value `val`. So commuting a substitution `s` past the directed
//! delta step needs only that `s` distributes over `apply_spine`/`kapp_args`
//! (the landed, unconditional `*_apply_spine` substrate) and that the def value
//! `val` is FIXED by `s` (a faithful closure condition on the env: the kernel's
//! definition values are closed terms). This is STRUCTURALLY SIMPLER than the
//! iota E-core: there is no rule rhs rebuilt from the env, no major-premise
//! window, no 5-level inversion — delta's reduct keeps the bare spine and the
//! whole-value `val` rides through by guarded-lookup inversion and preservation
//! of closedness under universe instantiation. The closure premise concerns the
//! stored schematic body, not a separately assumed fact about each instance.
//!
//! The closure condition is captured by `DefEnvClosed env` /
//! `DefEnvLiftClosed env` — real inductives (proper recursor, NOT axioms),
//! mirroring `RecEnvClosed` / `RecEnvLiftClosed` (`rec_env_closed.rs`). They are
//! defined HYPOTHESES (faithful interfaces); their witness for the kernel env is
//! discharged at the end of the track by modeling the definition-value store.
//!
//! Runs AFTER `add_delta_step` (consumes raw/guarded lookup and
//! `delta_reduct_some_inv`) and the early instL-closedness and term-invariance
//! stages, plus AFTER `add_iota_core` (consumes the inst/lift
//! commutation substrate: `instantiate_at_apply_spine`,
//! `instantiate_at_kapp_args_const`, `kexpr_const_name_instantiate_const`,
//! `lift_at_apply_spine`, `lift_at_kapp_args`, `kexpr_const_name_lift`,
//! `opt_bind_some_intro`, `option_some_inj`). Part of #2859 (Increment G).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// Both operational closure interfaces store ONLY closedness of raw schematic
/// bodies. Universe-instantiated invariance is derived below, never assumed.
const DEF_SCHEMATIC_CLOSED_FACT: &str = concat!(
    "forall (dname : Name) (defval : KExpr), ",
    "Eq (OptionType KExpr) (defval_for env dname) (OptionType.some KExpr defval) -> ",
    "is_closed_at defval Nat.zero"
);

impl Specification {
    pub(super) fn add_delta_subst(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            r"def kdef_inst_value_closed (defn : KDefSig) (us : ListType Level) (d : Nat)
(h : is_closed_at (kdef_value defn) d) : is_closed_at (kdef_inst_value defn us) d :=
instL_preserves_closed_at (paramSubstN (kconst_params (kdef_signature defn)) us) (kdef_value defn) d h",
            "Instantiate a shared definition's schematic body without changing de Bruijn closedness. Derived from the actual instL structural theorem, with no per-instantiation assumption.",
        )?;
        for (iface, prefix, operation, invariance) in [
            (
                "DefEnvClosed",
                "defenv_closed",
                "instantiate_at",
                "inst_closed_at_id",
            ),
            (
                "DefEnvLiftClosed",
                "defenv_lift_closed",
                "lift_at",
                "lift_closed_at_id",
            ),
        ] {
            self.add_inductive(
                &format!("inductive {iface} (env : DefEnv) : Type\n| mk : ({DEF_SCHEMATIC_CLOSED_FACT}) -> {iface} env"),
                "Schematic closure interface: every raw stored definition body is structurally closed at depth zero. This is not a premise about independently instantiated outputs.",
            )?;
            self.add_recursive_def(
                &format!("def {prefix}_raw (env : DefEnv) (n : Name) (body : KExpr) (w : {iface} env) (found : Eq (OptionType KExpr) (defval_for env n) (OptionType.some KExpr body)) : is_closed_at body Nat.zero := {iface}.rec env (fun (_ : {iface} env) => is_closed_at body Nat.zero) (fun (hc : {DEF_SCHEMATIC_CLOSED_FACT}) => hc n body found) w"),
                "Project structural closedness of the raw schematic body.",
            )?;
            let (extra, args, instantiate) = if operation == "instantiate_at" {
                ("(x : KExpr) (d : Nat)", "x d", format!("{invariance} body Nat.zero ({prefix}_raw env n body w found) x d (le_zero_n d)"))
            } else {
                ("(d : Nat) (x : Nat)", "d x", format!("{invariance} body Nat.zero ({prefix}_raw env n body w found) d x (le_zero_n d)"))
            };
            // `{prefix}_val` is the projector the keystone test pins as
            // DerivedProved with zero axiom_deps (tests/delta_subst_keystone.rs).
            // It goes through `add_definition`, which kernel-checks the value at
            // `add_decl` and records the derived-lemma status that registration
            // actually earned. `add_recursive_def` leaves every definition
            // DerivedPending by construction (declaration_registration.rs, "not
            // verified through the kernel promote pipeline"), and nothing later
            // promotes it — which is exactly what turned the keystone red when
            // 31fa57c00 moved this projector onto that path.
            self.add_definition(SpecDefinition {
                name: format!("{prefix}_val"),
                type_src: format!(
                    "forall (env : DefEnv) (n : Name) (body : KExpr) {extra}, \
                     {iface} env -> \
                     Eq (OptionType KExpr) (defval_for env n) (OptionType.some KExpr body) -> \
                     Eq KExpr ({operation} body {args}) body"
                ),
                value_src: Some(format!(
                    "fun (env : DefEnv) (n : Name) (body : KExpr) {extra} \
                     (w : {iface} env) \
                     (found : Eq (OptionType KExpr) (defval_for env n) (OptionType.some KExpr body)) => \
                     {instantiate}"
                )),
                is_axiom: false,
                description: "Preserve the old raw-body invariance interface, now derived from \
                              schematic structural closedness. DerivedProved; zero axiom_deps."
                    .to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    iface.to_string(),
                    format!("{prefix}_raw"),
                    invariance.to_string(),
                    "le_zero_n".to_string(),
                    "defval_for".to_string(),
                    operation.to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
            let derived_closed = format!("kdef_inst_value_closed defn us Nat.zero ({prefix}_raw env n (kdef_value defn) w (kdef_raw_value_of_lookup env n defn lookup))");
            let derived = if operation == "instantiate_at" {
                format!("{invariance} (kdef_inst_value defn us) Nat.zero ({derived_closed}) x d (le_zero_n d)")
            } else {
                format!("{invariance} (kdef_inst_value defn us) Nat.zero ({derived_closed}) d x (le_zero_n d)")
            };
            self.add_recursive_def(
                &format!(r"def {prefix}_value_at (env : DefEnv) (n : Name) (us : ListType Level) (body : KExpr) {extra}
(w : {iface} env)
(found : Eq (OptionType KExpr) (kdef_value_at env n us) (OptionType.some KExpr body)) :
Eq KExpr ({operation} body {args}) body :=
kdef_value_at_guard_inv env n us body (Eq KExpr ({operation} body {args}) body) found
  (fun (defn : KDefSig)
    (lookup : Eq (OptionType KDefSig) (kdef_for env n) (OptionType.some KDefSig defn))
    (_guard : Eq Bool (nat_eqb (name_list_len (kconst_params (kdef_signature defn))) (level_list_len us)) Bool.true)
    (result : Eq KExpr body (kdef_inst_value defn us)) =>
    Eq.substType KExpr (fun (v : KExpr) => Eq KExpr ({operation} v {args}) v)
      (kdef_inst_value defn us) body (Eq.symm KExpr body (kdef_inst_value defn us) result)
      ({derived}))"),
                "Actual unfolding bodies are invariant under term substitution/lift, derived by guarded-lookup inversion, raw schematic closedness, instL preservation and structural invariance. No per-instantiated-result assumption.",
            )?;
        }

        self.add_delta_subst_commutes()?;
        self.add_delta_lift_commutes()?;

        Ok(())
    }

    /// A known constant application head is fixed as a WHOLE expression by
    /// term substitution and lifting, so its universe argument list survives.
    pub(super) fn add_delta_head_invariance(&mut self) -> Result<(), SpecError> {
        for (suffix, params, operation, args, app_law, const_law) in [
            (
                "inst",
                "(v : KExpr) (d : Nat)",
                "instantiate_at",
                "v d",
                "instantiate_at_app",
                "instantiate_at_const",
            ),
            (
                "lift",
                "(c : Nat) (a0 : Nat)",
                "lift_at",
                "c a0",
                "lift_at_app",
                "lift_at_const",
            ),
        ] {
            let guard = |e: &str| {
                format!("Eq (OptionType Name) (kexpr_const_name (kapp_fn {e})) (OptionType.some Name n)")
            };
            let goal =
                |e: &str| format!("Eq KExpr (kapp_fn ({operation} {e} {args})) (kapp_fn {e})");
            let ih = |e: &str| format!("{} -> {}", guard(e), goal(e));
            let bad = |e: &str| {
                format!(
                    "(h : {}) => option_none_ne_some Name n ({}) h",
                    guard(e),
                    goal(e)
                )
            };
            let body = format!(
                r"fun {params} (n : Name) (e : KExpr) =>
KExpr.rec (fun (e0 : KExpr) => {motive})
  (fun (u : Level) {sort})
  (fun (i : Nat) {bvar})
  (fun (f : KExpr) (a : KExpr) (ihf : {ihf}) (_iha : {iha}) (h : {app_guard}) =>
    Eq.trans KExpr (kapp_fn ({operation} (KExpr.app f a) {args}))
      (kapp_fn ({operation} f {args})) (kapp_fn (KExpr.app f a))
      (Eq.cong KExpr KExpr kapp_fn ({operation} (KExpr.app f a) {args})
        (KExpr.app ({operation} f {args}) ({operation} a {args})) ({app_law} f a {args}))
      (ihf h))
  (fun (A : KExpr) (b : KExpr) (_ihA : {ihA}) (_ihb : {ihb}) {lam})
  (fun (A : KExpr) (b : KExpr) (_ihA : {ihA}) (_ihb : {ihb}) {pi})
  (fun (nm : Name) (us : ListType Level) (_h : {const_guard}) =>
    Eq.cong KExpr KExpr kapp_fn ({operation} (KExpr.const nm us) {args})
      (KExpr.const nm us) ({const_law} nm us {args}))
  (fun (A : KExpr) (v0 : KExpr) (b : KExpr) (_ihA : {ihA}) (_ihv : {ihv}) (_ihb : {ihb}) {let_})
  (fun (sn : Name) (i : Nat) (sub : KExpr) (_ihsub : {ihsub}) {proj})
  (fun (i : Nat) {lit}) e",
                motive = ih("e0"),
                sort = bad("(KExpr.sort u)"),
                bvar = bad("(KExpr.bvar i)"),
                ihf = ih("f"),
                iha = ih("a"),
                app_guard = guard("(KExpr.app f a)"),
                ihA = ih("A"),
                ihb = ih("b"),
                lam = bad("(KExpr.lam A b)"),
                pi = bad("(KExpr.pi A b)"),
                const_guard = guard("(KExpr.const nm us)"),
                ihv = ih("v0"),
                let_ = bad("(KExpr.let_ A v0 b)"),
                ihsub = ih("sub"),
                proj = bad("(KExpr.proj sn i sub)"),
                lit = bad("(KExpr.lit i)"),
            );
            self.add_definition(SpecDefinition {
                name: format!("delta_head_const_invariant_{suffix}"),
                type_src: format!("forall {params} (n : Name) (e : KExpr), {} -> {}", guard("e"), goal("e")),
                value_src: Some(body), is_axiom: false,
                description: "Term operations preserve a known constant application head including all supplied universe arguments, by actual KExpr induction. Only app and const arms survive the name guard.".to_string(),
                category: AxiomCategory::DerivedLemma, proof_status: ProofStatus::DerivedProved,
                elaborated_type: None, elaborated_value: None, dependencies: None, axiom_deps: HashSet::new(),
            })?;
        }
        Ok(())
    }

    /// Brick B: the instantiate_at delta commutation. `delta_reduct_inst_eq`
    /// (the reduct equation) + `delta_subst_commutes` (the E-core keystone).
    fn add_delta_subst_commutes(&mut self) -> Result<(), SpecError> {
        // F := (fun a0 => instantiate_at a0 v d), the per-arg substitution mapped
        // over the spine. Matches instantiate_at_kapp_args_const's list_map fn.
        let fmap = "(fun (a0 : KExpr) => instantiate_at a0 v d)";

        // delta_reduct_inst_eq: the REDUCT EQUATION — the spine algebra of the delta
        // E-core. Given the head-const guard (h1), the def-value lookup (h2), the
        // original reduct equation (h2r : some (apply_spine (kapp_args e) val) =
        // some e'), and a CLOSED env, the reduct recomputed on the inst side equals
        // inst of the original reduct (= inst e'):
        //   apply_spine (kapp_args (inst e)) val = inst (apply_spine (kapp_args e) val) = inst e'.
        // The spine survives inst: kapp_args (inst e) = list_map F (kapp_args e)
        // (instantiate_at_kapp_args_const, h1); the WHOLE val stays bare and equals
        // inst val only because the env is closed (defenv_closed_val, h2);
        // instantiate_at_apply_spine pushes inst through apply_spine; option_some_inj
        // on h2r gives (apply_spine (kapp_args e) val) = e'. The delta analogue of
        // iota_reduct_inst_eq, but on the bare whole-value spine (no rule rhs / no
        // 3-layer apply_spine / no major window).
        {
            // LHS = apply_spine (kapp_args (inst e)) val.
            let lhs = "(apply_spine (kapp_args (instantiate_at e v d)) val)";
            // B = apply_spine (list_map F (kapp_args e)) val.
            let b = format!("(apply_spine (list_map {fmap} (kapp_args e)) val)");
            // C = apply_spine (list_map F (kapp_args e)) (inst val).
            let c =
                format!("(apply_spine (list_map {fmap} (kapp_args e)) (instantiate_at val v d))");
            // MID = inst (apply_spine (kapp_args e) val).
            let mid = "(instantiate_at (apply_spine (kapp_args e) val) v d)";
            let rhs = "(instantiate_at e' v d)";

            // s1 : LHS = B  (kapp_args survives inst under the head-const guard).
            let s1 = format!(
                "(Eq.cong (ListType KExpr) KExpr (fun (L : ListType KExpr) => apply_spine L val) \
                 (kapp_args (instantiate_at e v d)) (list_map {fmap} (kapp_args e)) \
                 (instantiate_at_kapp_args_const v d dname e h1))"
            );
            // s2 : B = C  (the whole val is fixed by inst — closed env).
            let s2 = format!(
                "(Eq.cong KExpr KExpr (fun (Y : KExpr) => apply_spine (list_map {fmap} (kapp_args e)) Y) \
                 val (instantiate_at val v d) \
                 (Eq.symm KExpr (instantiate_at val v d) val \
                 (defenv_closed_value_at env dname (kexpr_const_levels (kapp_fn e)) val v d closed h2)))"
            );
            // s3 : C = MID  (symm of instantiate_at_apply_spine).
            let s3 = format!(
                "(Eq.symm KExpr {mid} {c} (instantiate_at_apply_spine (kapp_args e) val v d))"
            );
            // LHS = MID via s1 ∘ s2 ∘ s3.
            let lhs_to_mid = format!(
                "(Eq.trans KExpr {lhs} {b} {mid} {s1} (Eq.trans KExpr {b} {c} {mid} {s2} {s3}))"
            );
            // MID = RHS via cong F on option_some_inj h2r.
            let mid_to_rhs = format!(
                "(Eq.cong KExpr KExpr {fmap} (apply_spine (kapp_args e) val) e' \
                 (option_some_inj KExpr (apply_spine (kapp_args e) val) e' h2r))"
            );
            let value = format!(
                "fun (env : DefEnv) (v : KExpr) (d : Nat) (e : KExpr) (e' : KExpr) \
                 (dname : Name) (val : KExpr) \
                 (closed : DefEnvClosed env) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name dname)) \
                 (h2 : Eq (OptionType KExpr) (kdef_value_at env dname (kexpr_const_levels (kapp_fn e))) (OptionType.some KExpr val)) \
                 (h2r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (kapp_args e) val)) (OptionType.some KExpr e')) => \
                 Eq.trans KExpr {lhs} {mid} {rhs} {lhs_to_mid} {mid_to_rhs}"
            );
            self.add_definition(SpecDefinition {
                name: "delta_reduct_inst_eq".to_string(),
                type_src: "forall (env : DefEnv) (v : KExpr) (d : Nat) (e : KExpr) (e' : KExpr) \
                     (dname : Name) (val : KExpr), \
                     DefEnvClosed env -> \
                     Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name dname) -> \
                     Eq (OptionType KExpr) (kdef_value_at env dname (kexpr_const_levels (kapp_fn e))) (OptionType.some KExpr val) -> \
                     Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (kapp_args e) val)) (OptionType.some KExpr e') -> \
                     Eq KExpr (apply_spine (kapp_args (instantiate_at e v d)) val) (instantiate_at e' v d)"
                    .to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: "The reduct equation of the delta E-core: under a closed env and the redex head-const + def-value lookups, the delta reduct recomputed on the inst side equals inst of the original reduct (= inst e'). Composes instantiate_at_kapp_args_const (spine survives inst) + defenv_closed_val (the whole val is fixed) + instantiate_at_apply_spine (inst through apply_spine) + option_some_inj (reduct = e'). The delta analogue of iota_reduct_inst_eq, on the bare whole-value spine. DerivedProved, zero axiom_deps. Part of #2859 (Increment G).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "kapp_args".to_string(),
                    "apply_spine".to_string(),
                    "list_map".to_string(),
                    "instantiate_at".to_string(),
                    "instantiate_at_kapp_args_const".to_string(),
                    "instantiate_at_apply_spine".to_string(),
                    "defenv_closed_val".to_string(),
                    "option_some_inj".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // delta_subst_commutes: THE delta E-core keystone. instantiate_at commutes
        // past the directed delta step (delta_step = graph of delta_reduct):
        //   DefEnvClosed env -> delta_reduct env e = some e'
        //     -> delta_reduct env (inst e) = some (inst e').
        // Inverts the LHS via delta_reduct_some_inv (recovering the 2 redex witnesses
        // dname/val + the head lookup h1, the def-value lookup h2, and the reduct
        // equation h2r), then reconstructs the inst-side reduct via opt_bind_some_intro
        // 2×: the head-const lookup survives inst (kexpr_const_name_instantiate_const,
        // level 1), the def-value lookup is UNCHANGED (h2 — same env), and the reduct
        // slot is closed by delta_reduct_inst_eq (level 2). The delta analogue of
        // iota_subst_commutes (2 levels, not 5; no major window).
        {
            let ei = "(instantiate_at e v d)";
            let iep = "(instantiate_at e' v d)";

            // The inst-side opt_bind continuations (delta_reduct's def with e:=inst e).
            let f2 = format!(
                "(fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args {ei}) val))"
            );
            let f1 =
                format!("(fun (dname : Name) => opt_bind KExpr KExpr (kdef_value_at env dname (kexpr_const_levels (kapp_fn {ei}))) {f2})");

            // Level-1 inst-side lookup: the head const-name survives inst.
            let h1i = format!(
                "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn {ei})) (kexpr_const_name (kapp_fn e)) (OptionType.some Name dname) \
                 (kexpr_const_name_instantiate_const v d dname e h1) h1)"
            );
            // Level-2: some (apply_spine (kapp_args (inst e)) val) = some (inst e') via
            // delta_reduct_inst_eq + cong some.
            let hf2 = format!(
                "(Eq.cong KExpr (OptionType KExpr) (fun (X : KExpr) => OptionType.some KExpr X) \
                 (apply_spine (kapp_args {ei}) val) {iep} \
                 (delta_reduct_inst_eq env v d e e' dname val closed h1 h2 h2r))"
            );

            // The nested opt_bind_some_intro chain (outside-in, 2 levels).
            let h2i = format!(
                "(Eq.trans (OptionType KExpr) (kdef_value_at env dname (kexpr_const_levels (kapp_fn {ei}))) (kdef_value_at env dname (kexpr_const_levels (kapp_fn e))) (OptionType.some KExpr val) (Eq.cong KExpr (OptionType KExpr) (fun (head : KExpr) => kdef_value_at env dname (kexpr_const_levels head)) (kapp_fn {ei}) (kapp_fn e) (delta_head_const_invariant_inst v d dname e h1)) h2)"
            );

            let recon = format!(
                "opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn {ei})) {f1} dname {iep} {h1i} \
                 (opt_bind_some_intro KExpr KExpr (kdef_value_at env dname (kexpr_const_levels (kapp_fn {ei}))) {f2} val {iep} {h2i} {hf2})"
            );

            // The continuation k passed to delta_reduct_some_inv (binders match kont).
            let kont_lambda = format!(
                "(fun (dname : Name) (val : KExpr) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name dname)) \
                 (h2 : Eq (OptionType KExpr) (kdef_value_at env dname (kexpr_const_levels (kapp_fn e))) (OptionType.some KExpr val)) \
                 (h2r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (kapp_args e) val)) (OptionType.some KExpr e')) => \
                 {recon})"
            );

            let goal_c = format!(
                "(Eq (OptionType KExpr) (delta_reduct env {ei}) (OptionType.some KExpr {iep}))"
            );

            let value = format!(
                "fun (env : DefEnv) (e : KExpr) (e' : KExpr) (v : KExpr) (d : Nat) \
                 (closed : DefEnvClosed env) \
                 (h : Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e')) => \
                 delta_reduct_some_inv env e e' {goal_c} h {kont_lambda}"
            );

            self.add_definition(SpecDefinition {
                name: "delta_subst_commutes".to_string(),
                type_src: concat!(
                    "forall (env : DefEnv) (e : KExpr) (e' : KExpr) (v : KExpr) (d : Nat), ",
                    "DefEnvClosed env -> ",
                    "Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e') -> ",
                    "Eq (OptionType KExpr) (delta_reduct env (instantiate_at e v d)) (OptionType.some KExpr (instantiate_at e' v d))"
                )
                .to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: "delta E-core keystone: instantiate_at commutes past the directed delta step. From a closed env and delta_reduct env e = some e', derive delta_reduct env (inst e) = some (inst e'). Inverts via delta_reduct_some_inv then reconstructs via opt_bind_some_intro 2× (head-const lookup survives inst via kexpr_const_name_instantiate_const, def-value lookup unchanged, reduct slot closed by delta_reduct_inst_eq). The delta analogue of iota_subst_commutes (2 levels, no major window). DerivedProved, zero axiom_deps. Part of #2859 (Increment G).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "delta_reduct".to_string(),
                    "delta_reduct_some_inv".to_string(),
                    "opt_bind_some_intro".to_string(),
                    "delta_reduct_inst_eq".to_string(),
                    "kexpr_const_name_instantiate_const".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        Ok(())
    }

    /// Brick C: the lift_at delta commutation. `delta_reduct_lift_eq` (the reduct
    /// equation) + `delta_lift_commutes` (the LIFT E-core keystone). UNCONDITIONAL
    /// (no head-const guard — lift never changes the head), the lift mirror of
    /// Brick B.
    fn add_delta_lift_commutes(&mut self) -> Result<(), SpecError> {
        // G := (fun a0 => lift_at a0 c a), mapped over the spine. Matches
        // lift_at_kapp_args / lift_at_apply_spine's list_map fn.
        let gmap = "(fun (a0 : KExpr) => lift_at a0 c a)";

        // delta_reduct_lift_eq: the reduct equation of the LIFT delta E-core. Given
        // the def-value lookup (h2), the original reduct equation (h2r), and a
        // LIFT-CLOSED env, the reduct recomputed on the lift side equals lift of the
        // original reduct (= lift e'):
        //   apply_spine (kapp_args (lift e)) val = lift (apply_spine (kapp_args e) val) = lift e'.
        // UNCONDITIONAL: the spine survives lift (lift_at_kapp_args, no guard); the
        // WHOLE val is fixed by lift only because the env is lift-closed
        // (defenv_lift_closed_val, h2); lift_at_apply_spine pushes lift through
        // apply_spine; option_some_inj on h2r gives (apply_spine (kapp_args e) val) =
        // e'. The lift mirror of delta_reduct_inst_eq, no head-const guard.
        {
            let lhs = "(apply_spine (kapp_args (lift_at e c a)) val)";
            let b = format!("(apply_spine (list_map {gmap} (kapp_args e)) val)");
            let c = format!("(apply_spine (list_map {gmap} (kapp_args e)) (lift_at val c a))");
            let mid = "(lift_at (apply_spine (kapp_args e) val) c a)";
            let rhs = "(lift_at e' c a)";

            // s1 : LHS = B  (kapp_args survives lift — UNCONDITIONAL).
            let s1 = format!(
                "(Eq.cong (ListType KExpr) KExpr (fun (L : ListType KExpr) => apply_spine L val) \
                 (kapp_args (lift_at e c a)) (list_map {gmap} (kapp_args e)) \
                 (lift_at_kapp_args c a e))"
            );
            // s2 : B = C  (the whole val is fixed by lift — lift-closed env).
            let s2 = format!(
                "(Eq.cong KExpr KExpr (fun (Y : KExpr) => apply_spine (list_map {gmap} (kapp_args e)) Y) \
                 val (lift_at val c a) \
                 (Eq.symm KExpr (lift_at val c a) val \
                 (defenv_lift_closed_value_at env dname (kexpr_const_levels (kapp_fn e)) val c a liftclosed h2)))"
            );
            // s3 : C = MID  (symm of lift_at_apply_spine).
            let s3 =
                format!("(Eq.symm KExpr {mid} {c} (lift_at_apply_spine (kapp_args e) val c a))");
            let lhs_to_mid = format!(
                "(Eq.trans KExpr {lhs} {b} {mid} {s1} (Eq.trans KExpr {b} {c} {mid} {s2} {s3}))"
            );
            let mid_to_rhs = format!(
                "(Eq.cong KExpr KExpr {gmap} (apply_spine (kapp_args e) val) e' \
                 (option_some_inj KExpr (apply_spine (kapp_args e) val) e' h2r))"
            );
            let value = format!(
                "fun (env : DefEnv) (c : Nat) (a : Nat) (e : KExpr) (e' : KExpr) \
                 (dname : Name) (val : KExpr) \
                 (liftclosed : DefEnvLiftClosed env) \
                 (h2 : Eq (OptionType KExpr) (kdef_value_at env dname (kexpr_const_levels (kapp_fn e))) (OptionType.some KExpr val)) \
                 (h2r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (kapp_args e) val)) (OptionType.some KExpr e')) => \
                 Eq.trans KExpr {lhs} {mid} {rhs} {lhs_to_mid} {mid_to_rhs}"
            );
            self.add_definition(SpecDefinition {
                name: "delta_reduct_lift_eq".to_string(),
                type_src: "forall (env : DefEnv) (c : Nat) (a : Nat) (e : KExpr) (e' : KExpr) \
                     (dname : Name) (val : KExpr), \
                     DefEnvLiftClosed env -> \
                     Eq (OptionType KExpr) (kdef_value_at env dname (kexpr_const_levels (kapp_fn e))) (OptionType.some KExpr val) -> \
                     Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (kapp_args e) val)) (OptionType.some KExpr e') -> \
                     Eq KExpr (apply_spine (kapp_args (lift_at e c a)) val) (lift_at e' c a)"
                    .to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: "The reduct equation of the LIFT delta E-core: under a lift-closed env and the def-value lookup, the delta reduct recomputed on the lift side equals lift of the original reduct (= lift e'). Composes lift_at_kapp_args (spine survives lift, UNCONDITIONAL) + defenv_lift_closed_val (the whole val is fixed) + lift_at_apply_spine + option_some_inj. The lift mirror of delta_reduct_inst_eq, no head-const guard. DerivedProved, zero axiom_deps. Part of #2859 (Increment G).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "kapp_args".to_string(),
                    "apply_spine".to_string(),
                    "list_map".to_string(),
                    "lift_at".to_string(),
                    "lift_at_kapp_args".to_string(),
                    "lift_at_apply_spine".to_string(),
                    "defenv_lift_closed_val".to_string(),
                    "option_some_inj".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // delta_lift_commutes: THE LIFT delta E-core keystone. lift_at commutes past
        // the directed delta step:
        //   DefEnvLiftClosed env -> delta_reduct env e = some e'
        //     -> delta_reduct env (lift e) = some (lift e').
        // Mirror of delta_subst_commutes: invert via delta_reduct_some_inv, reconstruct
        // via opt_bind_some_intro 2×. UNCONDITIONALLY: the head-const lookup survives
        // lift (kexpr_const_name_lift, level 1), the def-value lookup is unchanged
        // (h2 — same env), and the reduct slot is closed by delta_reduct_lift_eq
        // (level 2). No const-head guard needed (lift never changes the head).
        {
            let el = "(lift_at e c a)";
            let epl = "(lift_at e' c a)";

            let f2 = format!(
                "(fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args {el}) val))"
            );
            let f1 =
                format!("(fun (dname : Name) => opt_bind KExpr KExpr (kdef_value_at env dname (kexpr_const_levels (kapp_fn {el}))) {f2})");

            // Level-1 lift-side lookup: the head const-name survives lift (no guard).
            let h1l = format!(
                "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn {el})) (kexpr_const_name (kapp_fn e)) (OptionType.some Name dname) \
                 (kexpr_const_name_lift c a e) h1)"
            );
            // Level-2: some (apply_spine (kapp_args (lift e)) val) = some (lift e') via
            // delta_reduct_lift_eq + cong some.
            let hf2 = format!(
                "(Eq.cong KExpr (OptionType KExpr) (fun (X : KExpr) => OptionType.some KExpr X) \
                 (apply_spine (kapp_args {el}) val) {epl} \
                 (delta_reduct_lift_eq env c a e e' dname val liftclosed h2 h2r))"
            );

            let h2l = format!(
                "(Eq.trans (OptionType KExpr) (kdef_value_at env dname (kexpr_const_levels (kapp_fn {el}))) (kdef_value_at env dname (kexpr_const_levels (kapp_fn e))) (OptionType.some KExpr val) (Eq.cong KExpr (OptionType KExpr) (fun (head : KExpr) => kdef_value_at env dname (kexpr_const_levels head)) (kapp_fn {el}) (kapp_fn e) (delta_head_const_invariant_lift c a dname e h1)) h2)"
            );

            let recon = format!(
                "opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn {el})) {f1} dname {epl} {h1l} \
                 (opt_bind_some_intro KExpr KExpr (kdef_value_at env dname (kexpr_const_levels (kapp_fn {el}))) {f2} val {epl} {h2l} {hf2})"
            );

            let kont_lambda = format!(
                "(fun (dname : Name) (val : KExpr) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name dname)) \
                 (h2 : Eq (OptionType KExpr) (kdef_value_at env dname (kexpr_const_levels (kapp_fn e))) (OptionType.some KExpr val)) \
                 (h2r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (kapp_args e) val)) (OptionType.some KExpr e')) => \
                 {recon})"
            );

            let goal_c = format!(
                "(Eq (OptionType KExpr) (delta_reduct env {el}) (OptionType.some KExpr {epl}))"
            );

            let value = format!(
                "fun (env : DefEnv) (e : KExpr) (e' : KExpr) (c : Nat) (a : Nat) \
                 (liftclosed : DefEnvLiftClosed env) \
                 (h : Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e')) => \
                 delta_reduct_some_inv env e e' {goal_c} h {kont_lambda}"
            );

            self.add_definition(SpecDefinition {
                name: "delta_lift_commutes".to_string(),
                type_src: concat!(
                    "forall (env : DefEnv) (e : KExpr) (e' : KExpr) (c : Nat) (a : Nat), ",
                    "DefEnvLiftClosed env -> ",
                    "Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e') -> ",
                    "Eq (OptionType KExpr) (delta_reduct env (lift_at e c a)) (OptionType.some KExpr (lift_at e' c a))"
                )
                .to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: "LIFT delta E-core keystone: lift_at commutes past the directed delta step. From a lift-closed env and delta_reduct env e = some e', derive delta_reduct env (lift e) = some (lift e'). Inverts via delta_reduct_some_inv then reconstructs via opt_bind_some_intro 2× (head-const lookup survives lift via kexpr_const_name_lift, def-value lookup unchanged, reduct slot closed by delta_reduct_lift_eq). UNCONDITIONAL (no head-const guard). The lift mirror of delta_subst_commutes. DerivedProved, zero axiom_deps. Part of #2859 (Increment G).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "delta_reduct".to_string(),
                    "delta_reduct_some_inv".to_string(),
                    "opt_bind_some_intro".to_string(),
                    "delta_reduct_lift_eq".to_string(),
                    "kexpr_const_name_lift".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        Ok(())
    }
}
