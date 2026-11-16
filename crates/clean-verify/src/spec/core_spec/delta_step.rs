// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment G (#2859 computational-iota/delta track): the computational
//! `delta_step` and its determinism — the δ analogue of the Increment C keystone.
//!
//! `delta` unfolds a definitional `const` head at its supplied universe arguments,
//! checking exact arity and keeping the application spine. Raw definition
//! lookup exposes a shared schematic signature; raw body lookup remains separate
//! from the actual instantiated unfolding value. This is structurally SIMPLER than
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

fn delta_lemma(
    spec: &mut Specification,
    name: &str,
    type_src: &str,
    value_src: &str,
    description: &str,
) -> Result<(), SpecError> {
    spec.add_definition(SpecDefinition {
        name: name.to_string(),
        type_src: type_src.to_string(),
        value_src: Some(value_src.to_string()),
        is_axiom: false,
        description: description.to_string(),
        category: AxiomCategory::DerivedLemma,
        proof_status: ProofStatus::DerivedProved,
        elaborated_type: None,
        elaborated_value: None,
        dependencies: None,
        axiom_deps: HashSet::new(),
    })
}

impl Specification {
    /// Core δ substrate (DefEnv / defval_for / delta_reduct / delta_step graph) —
    /// needs only the rec_env lookups (name_eqb/opt_pick) + the iota_step substrate
    /// (opt_bind/kapp_fn/kapp_args/apply_spine/kexpr_const_name), so it can run
    /// BEFORE the reduction families, which the Brick-4 tightening pins to
    /// `the_red_env` (church_rosser_whnf retirement track). The δ keystones that
    /// additionally need the iota CPS-inverter substrate stay in `add_delta_step`.
    pub(super) fn add_delta_step_core(&mut self) -> Result<(), SpecError> {
        // Store a single signature shared by the schematic type and body.
        self.add_inductive(
            r"inductive DefEnv : Type
| empty : DefEnv
| addDef : DefEnv → Name → KDefSig → DefEnv",
            "Definition environment storing one shared schematic signature and body per name. \
             The stored record alone proves no typing, admission or source correspondence.",
        )?;

        self.add_recursive_def(
            r"def kdef_for (env : DefEnv) (target : Name) : OptionType KDefSig := match env with
| DefEnv.empty => @OptionType.none KDefSig
| DefEnv.addDef tail dname defn => opt_pick KDefSig (name_eqb dname target) defn (kdef_for tail target)",
            "Raw name-keyed lookup of a definition's shared schematic signature and body. No universe instantiation occurs here.",
        )?;

        // defval_for: the RAW SCHEMATIC body of `target`, if present.
        // Mirrors recmeta_for (rec_env.rs) — match on env, opt_pick on name_eqb,
        // self-recurse on the tail.
        self.add_recursive_def(
            r"def defval_for (env : DefEnv) (target : Name) : OptionType KExpr := match env with
| DefEnv.empty => @OptionType.none KExpr
| DefEnv.addDef tail dname defn => opt_pick KExpr (name_eqb dname target) (kdef_value defn) (defval_for tail target)",
            "Raw schematic body lookup, retained for closure and name-absence interfaces. This is NOT the universe-instantiated unfolding operation; actual delta uses kdef_value_at.",
        )?;

        self.add_recursive_def(
            r"def kdef_guarded_value (defn : KDefSig) (us : ListType Level) : OptionType KExpr :=
@Bool.rec (fun (_guard : Bool) => OptionType KExpr)
    (@OptionType.none KExpr) (@OptionType.some KExpr (kdef_inst_value defn us))
    (nat_eqb (name_list_len (kconst_params (kdef_signature defn))) (level_list_len us))",
            "The exact-arity guard for one shared definition record; the raw instantiation result is exposed only in the true branch.",
        )?;
        self.add_recursive_def(
            r"def kdef_raw_value (found : OptionType KDefSig) : OptionType KExpr := @OptionType.rec KDefSig (fun (_found : OptionType KDefSig) => OptionType KExpr) (@OptionType.none KExpr) (fun (defn : KDefSig) => @OptionType.some KExpr (kdef_value defn)) found",
            "Project an optional stored signature to its raw schematic body, without instantiating universes.",
        )?;
        self.add_recursive_def(
            r"def kdef_value_at (env : DefEnv) (target : Name) (us : ListType Level) : OptionType KExpr :=
@OptionType.rec KDefSig (fun (_found : OptionType KDefSig) => OptionType KExpr)
  (@OptionType.none KExpr) (fun (defn : KDefSig) => kdef_guarded_value defn us) (kdef_for env target)",
            "Actual definition-value lookup: missing name or wrong universe arity returns none; success instantiates the schematic body with the shared signature's ordered parameter list.",
        )?;

        // delta_reduct: the computational delta reduct. If the head (after kapp_fn)
        // is a const with a definition value in env, unfold it and re-apply the
        // original spine args; else none. A 2-level opt_bind (head const name, then
        // value) + apply_spine. Mirrors iota_reduct but far simpler (no rules).
        self.add_recursive_def(
            r"def delta_reduct (env : DefEnv) (e : KExpr) : OptionType KExpr := opt_bind Name KExpr (kexpr_const_name (kapp_fn e)) (fun (dname : Name) => opt_bind KExpr KExpr (kdef_value_at env dname (kexpr_const_levels (kapp_fn e))) (fun (val : KExpr) => @OptionType.some KExpr (apply_spine (kapp_args e) val)))",
            "Universe-aware computational delta: retain the constant head's actual universe arguments, check declaration arity, instantiate the shared-signature body, and reapply the original spine. Missing definitions and arity mismatches do not step.",
        )?;

        // delta_step: the graph of delta_reduct — the directed step e -> e' holds
        // iff delta_reduct env e = some e'. A FUNCTION's graph, so deterministic.
        self.add_recursive_def(
            r"def delta_step (env : DefEnv) (e : KExpr) (e' : KExpr) : Prop := @Eq (OptionType KExpr) (delta_reduct env e) (@OptionType.some KExpr e')",
            "Directed delta step: delta_step env e e' holds iff delta_reduct env e = some e'. The graph of \
             the reduct function. Part of #2859 (Increment G).",
        )?;

        Ok(())
    }

    /// The δ keystones that need the iota CPS-inverter substrate (so this runs
    /// AFTER add_iota_subst, unlike the core above): delta_step determinism +
    /// delta_reduct_some_inv + delta_step_head_none_absurd.
    pub(super) fn add_delta_step(&mut self) -> Result<(), SpecError> {
        self.add_delta_raw_lookup_views()?;
        delta_lemma(self, "delta_reduct_no_value_at",
            r"forall (env : DefEnv) (e : KExpr) (n : Name),
@Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n) ->
@Eq (OptionType KExpr) (kdef_value_at env n (kexpr_const_levels (kapp_fn e))) (@OptionType.none KExpr) ->
@Eq (OptionType KExpr) (delta_reduct env e) (@OptionType.none KExpr)",
            r"fun (env : DefEnv) (e : KExpr) (n : Name)
(head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n))
(missing : @Eq (OptionType KExpr) (kdef_value_at env n (kexpr_const_levels (kapp_fn e))) (@OptionType.none KExpr)) =>
@Eq.trans (OptionType KExpr) (delta_reduct env e)
  (opt_bind KExpr KExpr (kdef_value_at env n (kexpr_const_levels (kapp_fn e)))
    (fun (v : KExpr) => @OptionType.some KExpr (apply_spine (kapp_args e) v)))
  (@OptionType.none KExpr)
  (@Eq.cong (OptionType Name) (OptionType KExpr)
    (fun (found : OptionType Name) => opt_bind Name KExpr found
      (fun (nm : Name) => opt_bind KExpr KExpr (kdef_value_at env nm (kexpr_const_levels (kapp_fn e)))
        (fun (v : KExpr) => @OptionType.some KExpr (apply_spine (kapp_args e) v))))
    (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n) head)
  (@Eq.cong (OptionType KExpr) (OptionType KExpr)
    (fun (value : OptionType KExpr) => opt_bind KExpr KExpr value
      (fun (v : KExpr) => @OptionType.some KExpr (apply_spine (kapp_args e) v)))
    (kdef_value_at env n (kexpr_const_levels (kapp_fn e))) (@OptionType.none KExpr)
    missing)",
            "A guarded missing value at the actual head universe arguments gives no delta reduct. This does not assert raw declaration absence.",
        )?;
        delta_lemma(self, "delta_reduct_no_raw_value",
            r"forall (env : DefEnv) (e : KExpr) (n : Name),
@Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n) ->
@Eq (OptionType KExpr) (defval_for env n) (@OptionType.none KExpr) ->
@Eq (OptionType KExpr) (delta_reduct env e) (@OptionType.none KExpr)",
            r"fun (env : DefEnv) (e : KExpr) (n : Name)
(head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n))
(missing : @Eq (OptionType KExpr) (defval_for env n) (@OptionType.none KExpr)) =>
@Eq.trans (OptionType KExpr) (delta_reduct env e)
  (opt_bind KExpr KExpr (kdef_value_at env n (kexpr_const_levels (kapp_fn e)))
    (fun (v : KExpr) => @OptionType.some KExpr (apply_spine (kapp_args e) v)))
  (@OptionType.none KExpr)
  (@Eq.cong (OptionType Name) (OptionType KExpr)
    (fun (found : OptionType Name) => opt_bind Name KExpr found
      (fun (nm : Name) => opt_bind KExpr KExpr (kdef_value_at env nm (kexpr_const_levels (kapp_fn e)))
        (fun (v : KExpr) => @OptionType.some KExpr (apply_spine (kapp_args e) v))))
    (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n) head)
  (@Eq.cong (OptionType KExpr) (OptionType KExpr)
    (fun (value : OptionType KExpr) => opt_bind KExpr KExpr value
      (fun (v : KExpr) => @OptionType.some KExpr (apply_spine (kapp_args e) v)))
    (kdef_value_at env n (kexpr_const_levels (kapp_fn e))) (@OptionType.none KExpr)
    (kdef_value_at_none env n (kexpr_const_levels (kapp_fn e)) missing))",
            "Existing raw name-absence guarantees no operational delta reduct at every retained universe argument list. Derived through the guarded-lookup absence theorem, not by equating raw and instantiated values.",
        )?;
        // delta_step_deterministic: the reduct is unique. Since delta_step is the
        // graph of the FUNCTION delta_reduct, two reducts of the same redex are both
        // equal to delta_reduct env e, hence equal by some-injectivity. The δ
        // analogue of the iota_step_deterministic keystone — the directed,
        // determinate capability the abstract delta_reduces lacked.
        self.add_definition(SpecDefinition {
            name: "delta_step_deterministic".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "@Eq (OptionType KExpr) (delta_reduct env e) (@OptionType.some KExpr e1) -> ",
                "@Eq (OptionType KExpr) (delta_reduct env e) (@OptionType.some KExpr e2) -> ",
                "@Eq KExpr e1 e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : DefEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
                    "(h1 : @Eq (OptionType KExpr) (delta_reduct env e) (@OptionType.some KExpr e1)) ",
                    "(h2 : @Eq (OptionType KExpr) (delta_reduct env e) (@OptionType.some KExpr e2)) => ",
                    "option_some_inj KExpr e1 e2 ",
                    "(@Eq.trans (OptionType KExpr) ",
                    "(@OptionType.some KExpr e1) (delta_reduct env e) (@OptionType.some KExpr e2) ",
                    "(@Eq.symm (OptionType KExpr) (delta_reduct env e) (@OptionType.some KExpr e1) h1) ",
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
            let l3 = format!("(fun (val : KExpr) => @OptionType.some KExpr {reduct})");
            let l2 =
                format!("(fun (dname : Name) => opt_bind KExpr KExpr (kdef_value_at env dname (kexpr_const_levels (kapp_fn e))) {l3})");
            let kont = format!(
                "(forall (dname : Name) (val : KExpr), \
                 @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name dname) -> \
                 @Eq (OptionType KExpr) (kdef_value_at env dname (kexpr_const_levels (kapp_fn e))) (@OptionType.some KExpr val) -> \
                 @Eq (OptionType KExpr) (@OptionType.some KExpr {reduct}) (@OptionType.some KExpr e') -> \
                 C)"
            );
            let value = format!(
                "fun (env : DefEnv) (e : KExpr) (e' : KExpr) (C : Prop) \
                 (h : @Eq (OptionType KExpr) (delta_reduct env e) (@OptionType.some KExpr e')) \
                 (k : {kont}) => \
                 opt_bind_some_inv Name KExpr (kexpr_const_name (kapp_fn e)) {l2} e' C h \
                 (fun (dname : Name) \
                 (h1 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name dname)) \
                 (h1r : @Eq (OptionType KExpr) ({l2} dname) (@OptionType.some KExpr e')) => \
                 opt_bind_some_inv KExpr KExpr (kdef_value_at env dname (kexpr_const_levels (kapp_fn e))) {l3} e' C h1r \
                 (fun (val : KExpr) \
                 (h2 : @Eq (OptionType KExpr) (kdef_value_at env dname (kexpr_const_levels (kapp_fn e))) (@OptionType.some KExpr val)) \
                 (h2r : @Eq (OptionType KExpr) ({l3} val) (@OptionType.some KExpr e')) => \
                 k dname val h1 h2 h2r))"
            );
            self.add_definition(SpecDefinition {
                name: "delta_reduct_some_inv".to_string(),
                type_src: format!(
                    "forall (env : DefEnv) (e : KExpr) (e' : KExpr) (C : Prop), \
                     @Eq (OptionType KExpr) (delta_reduct env e) (@OptionType.some KExpr e') -> {kont} -> C"
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
                    "kdef_value_at".to_string(),
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
                "@Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.none Name) -> ",
                "delta_step env e e' -> C"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : DefEnv) (e : KExpr) (e' : KExpr) (C : Prop) ",
                    "(hnone : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.none Name)) ",
                    "(h : @Eq (OptionType KExpr) (delta_reduct env e) (@OptionType.some KExpr e')) => ",
                    "delta_reduct_some_inv env e e' C h ",
                    "(fun (dname : Name) (val : KExpr) ",
                    "(h1 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name dname)) ",
                    "(h2 : @Eq (OptionType KExpr) (kdef_value_at env dname (kexpr_const_levels (kapp_fn e))) (@OptionType.some KExpr val)) ",
                    "(h2r : @Eq (OptionType KExpr) (@OptionType.some KExpr (apply_spine (kapp_args e) val)) (@OptionType.some KExpr e')) => ",
                    "option_none_ne_some Name dname C ",
                    "(@Eq.trans (OptionType Name) (@OptionType.none Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name dname) ",
                    "(@Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.none Name) hnone) h1))"
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

    /// Early operational views need only Option no-confusion into Prop; exact
    /// Nat-arity reflection remains in the later signature-lookup stage.
    fn add_delta_raw_lookup_views(&mut self) -> Result<(), SpecError> {
        delta_lemma(
            self,
            "kdef_raw_agrees",
            r"forall (env : DefEnv) (n : Name), @Eq (OptionType KExpr) (defval_for env n) (kdef_raw_value (kdef_for env n))",
            r"fun (env : DefEnv) (n : Name) =>
@DefEnv.rec (fun (env0 : DefEnv) => @Eq (OptionType KExpr) (defval_for env0 n) (kdef_raw_value (kdef_for env0 n)))
  (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
  (fun (tail : DefEnv) (dn : Name) (defn : KDefSig)
    (ih : @Eq (OptionType KExpr) (defval_for tail n) (kdef_raw_value (kdef_for tail n))) =>
    @Bool.rec
      (fun (b : Bool) => @Eq (OptionType KExpr)
        (opt_pick KExpr b (kdef_value defn) (defval_for tail n))
        (kdef_raw_value (opt_pick KDefSig b defn (kdef_for tail n))))
      ih (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (kdef_value defn)))
      (name_eqb dn n)) env",
            "The retained raw-body lookup is exactly projection of the actual shared-signature lookup, proved by environment and Boolean induction.",
        )?;
        delta_lemma(
            self,
            "kdef_raw_value_of_lookup",
            r"forall (env : DefEnv) (n : Name) (defn : KDefSig), @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.some KDefSig defn) -> @Eq (OptionType KExpr) (defval_for env n) (@OptionType.some KExpr (kdef_value defn))",
            r"fun (env : DefEnv) (n : Name) (defn : KDefSig)
  (h : @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.some KDefSig defn)) =>
@Eq.trans (OptionType KExpr) (defval_for env n) (kdef_raw_value (kdef_for env n))
  (@OptionType.some KExpr (kdef_value defn)) (kdef_raw_agrees env n)
  (@Eq.cong (OptionType KDefSig) (OptionType KExpr) kdef_raw_value
    (kdef_for env n) (@OptionType.some KDefSig defn) h)",
            "A successful shared-signature lookup yields the corresponding raw schematic body; no universe instantiation is silently identified with it.",
        )?;
        delta_lemma(
            self,
            "kdef_for_none_of_raw_none",
            r"forall (env : DefEnv) (n : Name), @Eq (OptionType KExpr) (defval_for env n) (@OptionType.none KExpr) -> @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.none KDefSig)",
            r"fun (env : DefEnv) (n : Name)
  (hn : @Eq (OptionType KExpr) (defval_for env n) (@OptionType.none KExpr)) =>
@OptionType.rec KDefSig
  (fun (found : OptionType KDefSig) => @Eq (OptionType KDefSig) (kdef_for env n) found -> @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.none KDefSig))
  (fun (h : @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.none KDefSig)) => h)
  (fun (defn : KDefSig) (h : @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.some KDefSig defn)) =>
    option_none_ne_some KExpr (kdef_value defn)
      (@Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.none KDefSig))
      (@Eq.trans (OptionType KExpr) (@OptionType.none KExpr) (defval_for env n)
        (@OptionType.some KExpr (kdef_value defn))
        (@Eq.symm (OptionType KExpr) (defval_for env n) (@OptionType.none KExpr) hn)
        (kdef_raw_value_of_lookup env n defn h)))
  (kdef_for env n) (@Eq.refl (OptionType KDefSig) (kdef_for env n))",
            "Raw body absence implies actual signature absence; the some-signature branch would contradict the proved raw projection equation.",
        )?;
        delta_lemma(
            self,
            "kdef_value_at_missing",
            r"forall (env : DefEnv) (n : Name) (us : ListType Level), @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.none KDefSig) -> @Eq (OptionType KExpr) (kdef_value_at env n us) (@OptionType.none KExpr)",
            r"fun (env : DefEnv) (n : Name) (us : ListType Level)
  (h : @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.none KDefSig)) =>
@Eq.cong (OptionType KDefSig) (OptionType KExpr)
  (fun (found : OptionType KDefSig) => @OptionType.rec KDefSig
    (fun (_ : OptionType KDefSig) => OptionType KExpr) (@OptionType.none KExpr)
    (fun (defn : KDefSig) => kdef_guarded_value defn us) found)
  (kdef_for env n) (@OptionType.none KDefSig) h",
            "Missing raw signature returns no unfolding value at every universe argument list.",
        )?;
        delta_lemma(
            self,
            "kdef_value_at_none",
            r"forall (env : DefEnv) (n : Name) (us : ListType Level), @Eq (OptionType KExpr) (defval_for env n) (@OptionType.none KExpr) -> @Eq (OptionType KExpr) (kdef_value_at env n us) (@OptionType.none KExpr)",
            r"fun (env : DefEnv) (n : Name) (us : ListType Level)
  (h : @Eq (OptionType KExpr) (defval_for env n) (@OptionType.none KExpr)) =>
kdef_value_at_missing env n us (kdef_for_none_of_raw_none env n h)",
            "Compatibility theorem for existing raw name-absence interfaces: a missing raw body cannot produce a guarded value at any universes.",
        )?;
        delta_lemma(
            self,
            "kdef_value_at_guard_inv",
            r"forall (env : DefEnv) (n : Name) (us : ListType Level) (v : KExpr) (C : Prop),
@Eq (OptionType KExpr) (kdef_value_at env n us) (@OptionType.some KExpr v) ->
(forall (defn : KDefSig), @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.some KDefSig defn) ->
  @Eq Bool (nat_eqb (name_list_len (kconst_params (kdef_signature defn))) (level_list_len us)) Bool.true ->
  @Eq KExpr v (kdef_inst_value defn us) -> C) -> C",
            r"fun (env : DefEnv) (n : Name) (us : ListType Level) (v : KExpr) (C : Prop)
  (h : @Eq (OptionType KExpr) (kdef_value_at env n us) (@OptionType.some KExpr v))
  (k : forall (defn : KDefSig), @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.some KDefSig defn) ->
    @Eq Bool (nat_eqb (name_list_len (kconst_params (kdef_signature defn))) (level_list_len us)) Bool.true ->
    @Eq KExpr v (kdef_inst_value defn us) -> C) =>
@OptionType.rec KDefSig
  (fun (found : OptionType KDefSig) => @Eq (OptionType KDefSig) (kdef_for env n) found ->
    @Eq (OptionType KExpr) (@OptionType.rec KDefSig (fun (_ : OptionType KDefSig) => OptionType KExpr)
      (@OptionType.none KExpr) (fun (defn : KDefSig) => kdef_guarded_value defn us) found)
      (@OptionType.some KExpr v) -> C)
  (fun (_hl : @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.none KDefSig))
    (hr : @Eq (OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr v)) => option_none_ne_some KExpr v C hr)
  (fun (defn : KDefSig) (hl : @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.some KDefSig defn))
    (hr : @Eq (OptionType KExpr) (kdef_guarded_value defn us) (@OptionType.some KExpr v)) =>
    @Bool.rec
      (fun (b : Bool) => @Eq Bool (nat_eqb (name_list_len (kconst_params (kdef_signature defn))) (level_list_len us)) b ->
        @Eq (OptionType KExpr) (@Bool.rec (fun (_ : Bool) => OptionType KExpr)
          (@OptionType.none KExpr) (@OptionType.some KExpr (kdef_inst_value defn us)) b) (@OptionType.some KExpr v) -> C)
      (fun (_hg : @Eq Bool (nat_eqb (name_list_len (kconst_params (kdef_signature defn))) (level_list_len us)) Bool.false)
        (hbad : @Eq (OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr v)) => option_none_ne_some KExpr v C hbad)
      (fun (hg : @Eq Bool (nat_eqb (name_list_len (kconst_params (kdef_signature defn))) (level_list_len us)) Bool.true)
        (hv : @Eq (OptionType KExpr) (@OptionType.some KExpr (kdef_inst_value defn us)) (@OptionType.some KExpr v)) =>
        k defn hl hg (@Eq.symm KExpr (kdef_inst_value defn us) v (option_some_inj KExpr (kdef_inst_value defn us) v hv)))
      (nat_eqb (name_list_len (kconst_params (kdef_signature defn))) (level_list_len us))
      (@Eq.refl Bool (nat_eqb (name_list_len (kconst_params (kdef_signature defn))) (level_list_len us))) hr)
  (kdef_for env n) (@Eq.refl (OptionType KDefSig) (kdef_for env n)) h",
            "Early CPS inversion exposes the actual stored definition, true computed arity guard and genuine instantiated result. It assumes no Nat reflection; the later exact-arity view consumes the existing reflection theorem.",
        )?;
        Ok(())
    }

    /// Exact arity and Type-valued inversion reuse the checked declaration
    /// guard reflection. Register after add_declaration_signature_lookup.
    pub(super) fn add_delta_signature_lookup(&mut self) -> Result<(), SpecError> {
        self.add_delta_raw_absence_controls()?;
        delta_lemma(self, "kdef_value_at_intro",
            r"forall (env : DefEnv) (n : Name) (sig : KDefSig) (us : ListType Level), @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.some KDefSig sig) -> kconst_arity (kdef_signature sig) us -> @Eq (OptionType KExpr) (kdef_value_at env n us) (@OptionType.some KExpr (kdef_inst_value sig us))",
            r"fun (env : DefEnv) (n : Name) (sig : KDefSig) (us : ListType Level) (hlookup : @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.some KDefSig sig)) (harity : kconst_arity (kdef_signature sig) us) =>
  @Eq.trans (OptionType KExpr) (kdef_value_at env n us) (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kdef_inst_value sig us)) (nat_eqb (name_list_len (kconst_params (kdef_signature sig))) (level_list_len us))) (@OptionType.some KExpr (kdef_inst_value sig us))
    (@Eq.cong (OptionType KDefSig) (OptionType KExpr)
    (fun (found : OptionType KDefSig) => (@OptionType.rec KDefSig (fun (_found : OptionType KDefSig) => OptionType KExpr) (@OptionType.none KExpr) (fun (sig : KDefSig) => (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kdef_inst_value sig us)) (nat_eqb (name_list_len (kconst_params (kdef_signature sig))) (level_list_len us)))) found))
    (kdef_for env n) (@OptionType.some KDefSig sig) hlookup)
    (@Eq.cong Bool (OptionType KExpr) (fun (b : Bool) => (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kdef_inst_value sig us)) b))
      (nat_eqb (name_list_len (kconst_params (kdef_signature sig))) (level_list_len us)) Bool.true (kconst_arity_check_true (kdef_signature sig) us harity))",
            "Exact-arity definition-value lookup theorem over the actual guarded delta operation. Reuses the proved arithmetic guard and exposes the stored shared signature; no per-instantiated typing assumption.",
        )?;
        delta_lemma(self, "kdef_value_at_wrong_arity",
            r"forall (env : DefEnv) (n : Name) (us : ListType Level) (sig : KDefSig), @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.some KDefSig sig) -> (kconst_arity (kdef_signature sig) us -> Empty) -> @Eq (OptionType KExpr) (kdef_value_at env n us) (@OptionType.none KExpr)",
            r"fun (env : DefEnv) (n : Name) (us : ListType Level) (sig : KDefSig) (hlookup : @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.some KDefSig sig)) (hbad : kconst_arity (kdef_signature sig) us -> Empty) =>
  @Eq.trans (OptionType KExpr) (kdef_value_at env n us) (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kdef_inst_value sig us)) (nat_eqb (name_list_len (kconst_params (kdef_signature sig))) (level_list_len us))) (@OptionType.none KExpr)
    (@Eq.cong (OptionType KDefSig) (OptionType KExpr)
    (fun (found : OptionType KDefSig) => (@OptionType.rec KDefSig (fun (_found : OptionType KDefSig) => OptionType KExpr) (@OptionType.none KExpr) (fun (sig : KDefSig) => (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kdef_inst_value sig us)) (nat_eqb (name_list_len (kconst_params (kdef_signature sig))) (level_list_len us)))) found))
    (kdef_for env n) (@OptionType.some KDefSig sig) hlookup)
    (@Eq.cong Bool (OptionType KExpr) (fun (b : Bool) => (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kdef_inst_value sig us)) b))
      (nat_eqb (name_list_len (kconst_params (kdef_signature sig))) (level_list_len us)) Bool.false (kconst_arity_check_false (kdef_signature sig) us hbad))",
            "Exact-arity definition-value lookup theorem over the actual guarded delta operation. Reuses the proved arithmetic guard and exposes the stored shared signature; no per-instantiated typing assumption.",
        )?;
        delta_lemma(self, "kdef_value_at_some_inv",
            r"forall (env : DefEnv) (n : Name) (us : ListType Level) (T : KExpr), @Eq (OptionType KExpr) (kdef_value_at env n us) (@OptionType.some KExpr T) ->
    forall (C : Type),
      (forall (sig : KDefSig), @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.some KDefSig sig) ->
        kconst_arity (kdef_signature sig) us -> @Eq KExpr T (kdef_inst_value sig us) -> C) -> C",
            r"fun (env : DefEnv) (n : Name) (us : ListType Level) (T : KExpr)
    (h : @Eq (OptionType KExpr) (kdef_value_at env n us) (@OptionType.some KExpr T))
    (C : Type)
    (k : forall (sig : KDefSig), @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.some KDefSig sig) ->
      kconst_arity (kdef_signature sig) us -> @Eq KExpr T (kdef_inst_value sig us) -> C) =>
  @OptionType.rec KDefSig
    (fun (found : OptionType KDefSig) =>
      @Eq (OptionType KDefSig) (kdef_for env n) found ->
      @Eq (OptionType KExpr) (@OptionType.rec KDefSig (fun (_found : OptionType KDefSig) => OptionType KExpr) (@OptionType.none KExpr) (fun (sig : KDefSig) => (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kdef_inst_value sig us)) (nat_eqb (name_list_len (kconst_params (kdef_signature sig))) (level_list_len us)))) found) (@OptionType.some KExpr T) -> C)
    (fun (_hlookup : @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.none KDefSig))
      (hresult : @Eq (OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr T)) =>
      option_none_ne_some_type KExpr T C hresult)
    (fun (sig : KDefSig) (hlookup : @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.some KDefSig sig))
      (hresult : @Eq (OptionType KExpr) (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kdef_inst_value sig us)) (nat_eqb (name_list_len (kconst_params (kdef_signature sig))) (level_list_len us))) (@OptionType.some KExpr T)) =>
      @Bool.rec
        (fun (b : Bool) => @Eq Bool (nat_eqb (name_list_len (kconst_params (kdef_signature sig))) (level_list_len us)) b ->
          @Eq (OptionType KExpr) (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kdef_inst_value sig us)) b) (@OptionType.some KExpr T) -> C)
        (fun (_hg : @Eq Bool (nat_eqb (name_list_len (kconst_params (kdef_signature sig))) (level_list_len us)) Bool.false)
          (hr : @Eq (OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr T)) =>
          option_none_ne_some_type KExpr T C hr)
        (fun (hg : @Eq Bool (nat_eqb (name_list_len (kconst_params (kdef_signature sig))) (level_list_len us)) Bool.true)
          (hr : @Eq (OptionType KExpr) (@OptionType.some KExpr (kdef_inst_value sig us)) (@OptionType.some KExpr T)) =>
          k sig hlookup (nat_eqb_eq (name_list_len (kconst_params (kdef_signature sig))) (level_list_len us) hg)
            (@Eq.symm KExpr (kdef_inst_value sig us) T (option_some_inj KExpr (kdef_inst_value sig us) T hr)))
        (nat_eqb (name_list_len (kconst_params (kdef_signature sig))) (level_list_len us)) (@Eq.refl Bool (nat_eqb (name_list_len (kconst_params (kdef_signature sig))) (level_list_len us))) hresult)
    (kdef_for env n) (@Eq.refl (OptionType KDefSig) (kdef_for env n)) h",
            "Exact-arity definition-value lookup theorem over the actual guarded delta operation. Reuses the proved arithmetic guard and exposes the stored shared signature; no per-instantiated typing assumption.",
        )?;
        delta_lemma(self, "kdef_value_at_some_inv_prop",
            r"forall (env : DefEnv) (n : Name) (us : ListType Level) (T : KExpr), @Eq (OptionType KExpr) (kdef_value_at env n us) (@OptionType.some KExpr T) ->
    forall (C : Prop),
      (forall (sig : KDefSig), @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.some KDefSig sig) ->
        kconst_arity (kdef_signature sig) us -> @Eq KExpr T (kdef_inst_value sig us) -> C) -> C",
            r"fun (env : DefEnv) (n : Name) (us : ListType Level) (T : KExpr)
    (h : @Eq (OptionType KExpr) (kdef_value_at env n us) (@OptionType.some KExpr T))
    (C : Prop)
    (k : forall (sig : KDefSig), @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.some KDefSig sig) ->
      kconst_arity (kdef_signature sig) us -> @Eq KExpr T (kdef_inst_value sig us) -> C) =>
  @OptionType.rec KDefSig
    (fun (found : OptionType KDefSig) =>
      @Eq (OptionType KDefSig) (kdef_for env n) found ->
      @Eq (OptionType KExpr) (@OptionType.rec KDefSig (fun (_found : OptionType KDefSig) => OptionType KExpr) (@OptionType.none KExpr) (fun (sig : KDefSig) => (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kdef_inst_value sig us)) (nat_eqb (name_list_len (kconst_params (kdef_signature sig))) (level_list_len us)))) found) (@OptionType.some KExpr T) -> C)
    (fun (_hlookup : @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.none KDefSig))
      (hresult : @Eq (OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr T)) =>
      @Empty.rec (fun (_ : Empty) => C) (option_none_ne_some_type KExpr T Empty hresult))
    (fun (sig : KDefSig) (hlookup : @Eq (OptionType KDefSig) (kdef_for env n) (@OptionType.some KDefSig sig))
      (hresult : @Eq (OptionType KExpr) (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kdef_inst_value sig us)) (nat_eqb (name_list_len (kconst_params (kdef_signature sig))) (level_list_len us))) (@OptionType.some KExpr T)) =>
      @Bool.rec
        (fun (b : Bool) => @Eq Bool (nat_eqb (name_list_len (kconst_params (kdef_signature sig))) (level_list_len us)) b ->
          @Eq (OptionType KExpr) (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kdef_inst_value sig us)) b) (@OptionType.some KExpr T) -> C)
        (fun (_hg : @Eq Bool (nat_eqb (name_list_len (kconst_params (kdef_signature sig))) (level_list_len us)) Bool.false)
          (hr : @Eq (OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr T)) =>
          @Empty.rec (fun (_ : Empty) => C) (option_none_ne_some_type KExpr T Empty hr))
        (fun (hg : @Eq Bool (nat_eqb (name_list_len (kconst_params (kdef_signature sig))) (level_list_len us)) Bool.true)
          (hr : @Eq (OptionType KExpr) (@OptionType.some KExpr (kdef_inst_value sig us)) (@OptionType.some KExpr T)) =>
          k sig hlookup (nat_eqb_eq (name_list_len (kconst_params (kdef_signature sig))) (level_list_len us) hg)
            (@Eq.symm KExpr (kdef_inst_value sig us) T (option_some_inj KExpr (kdef_inst_value sig us) T hr)))
        (nat_eqb (name_list_len (kconst_params (kdef_signature sig))) (level_list_len us)) (@Eq.refl Bool (nat_eqb (name_list_len (kconst_params (kdef_signature sig))) (level_list_len us))) hresult)
    (kdef_for env n) (@Eq.refl (OptionType KDefSig) (kdef_for env n)) h",
            "Exact-arity definition-value lookup theorem over the actual guarded delta operation. Reuses the proved arithmetic guard and exposes the stored shared signature; no per-instantiated typing assumption.",
        )?;
        Ok(())
    }

    /// Actual-model operational controls: guarded absence is not raw absence.
    fn add_delta_raw_absence_controls(&mut self) -> Result<(), SpecError> {
        delta_lemma(self, "delta_wrong_arity_is_stuck",
            r"@Eq (OptionType KExpr) (delta_reduct (DefEnv.addDef DefEnv.empty Name.anonymous (KDefSig.mk (KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (KExpr.sort Level.zero)) (KExpr.sort (Level.param Name.anonymous)))) (KExpr.const Name.anonymous (@ListType.nil Level))) (@OptionType.none KExpr)",
            r"@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
            "Actual guarded delta refuses a supplied empty universe list for a stored one-parameter declaration. The raw declaration and its supported body remain present.",
        )?;
        delta_lemma(self, "delta_wrong_arity_has_raw_body",
            r"@Eq (OptionType KExpr) (defval_for (DefEnv.addDef DefEnv.empty Name.anonymous (KDefSig.mk (KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (KExpr.sort Level.zero)) (KExpr.sort (Level.param Name.anonymous)))) Name.anonymous) (@OptionType.some KExpr (KExpr.sort (Level.param Name.anonymous)))",
            r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.param Name.anonymous)))",
            "The same wrong-arity delta-stuck witness has a genuine successful raw schematic body lookup. No declaration is absent.",
        )?;
        delta_lemma(self, "delta_stuck_raw_absence_converse_refuted",
            r"(forall (n : Name) (us : ListType Level), @Eq (OptionType KExpr) (delta_reduct (DefEnv.addDef DefEnv.empty Name.anonymous (KDefSig.mk (KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (KExpr.sort Level.zero)) (KExpr.sort (Level.param Name.anonymous)))) (KExpr.const n us)) (@OptionType.none KExpr) -> @Eq (OptionType KExpr) (defval_for (DefEnv.addDef DefEnv.empty Name.anonymous (KDefSig.mk (KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (KExpr.sort Level.zero)) (KExpr.sort (Level.param Name.anonymous)))) n) (@OptionType.none KExpr)) -> Empty",
            r"fun (bad : forall (n : Name) (us : ListType Level),
    @Eq (OptionType KExpr) (delta_reduct (DefEnv.addDef DefEnv.empty Name.anonymous (KDefSig.mk (KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (KExpr.sort Level.zero)) (KExpr.sort (Level.param Name.anonymous)))) (KExpr.const n us)) (@OptionType.none KExpr) ->
    @Eq (OptionType KExpr) (defval_for (DefEnv.addDef DefEnv.empty Name.anonymous (KDefSig.mk (KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (KExpr.sort Level.zero)) (KExpr.sort (Level.param Name.anonymous)))) n) (@OptionType.none KExpr)) =>
  option_none_ne_some_type KExpr (KExpr.sort (Level.param Name.anonymous)) Empty
    (@Eq.trans (OptionType KExpr) (@OptionType.none KExpr)
      (defval_for (DefEnv.addDef DefEnv.empty Name.anonymous (KDefSig.mk (KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (KExpr.sort Level.zero)) (KExpr.sort (Level.param Name.anonymous)))) Name.anonymous) (@OptionType.some KExpr (KExpr.sort (Level.param Name.anonymous)))
      (@Eq.symm (OptionType KExpr) (defval_for (DefEnv.addDef DefEnv.empty Name.anonymous (KDefSig.mk (KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (KExpr.sort Level.zero)) (KExpr.sort (Level.param Name.anonymous)))) Name.anonymous) (@OptionType.none KExpr)
        (bad Name.anonymous (@ListType.nil Level) delta_wrong_arity_is_stuck))
      delta_wrong_arity_has_raw_body)",
            "Constructive refutation of the old unrestricted stuckness-to-raw-absence converse. Wrong universe arity makes actual delta stuck while the supported stored body exists; no branch is excluded and no new premise is assumed.",
        )?;
        Ok(())
    }
}
