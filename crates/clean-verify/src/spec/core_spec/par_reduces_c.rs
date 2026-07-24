// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment F (#2859 computational-iota/delta track): the computational
//! parallel-reduction sibling `par_reduces_c` and the first cross-join.
//!
//! `par_reduces` (par_reduction.rs:82) carries the ABSTRACT `iota_reduces` in its
//! iota constructor, which has no determinism — that is why the `par_strips` iota
//! cross-joins are blocked. `iota_step_deterministic` lives on the COMPUTATIONAL
//! `iota_step`, not on `iota_reduces`, and the abstract witness cannot be turned
//! back into an `iota_step`. So (per the adversarially-verified design review) we
//! do NOT re-base `par_reduces.iota` (1279 references — unlandable); instead we
//! add an `env`-indexed SIBLING relation `par_reduces_c env` whose iota
//! constructor carries `iota_step env e e'`. This is the proven `par_reduces_bd`
//! pattern (a third sibling). Its single-step diamond `par_strips_c` can then use
//! `iota_step_deterministic` for the iota cross-cases, and it bridges back to the
//! existing `par_reduces` via `iota_step_to_reduces` (RecEnvWellformed-gated).
//!
//! This module lands the inductives + the FIRST cross-join `par_strips_iota_iota_c`
//! (the (iota,iota) join — uses ONLY determinism, no Increment-E dependency). The
//! structural ctors mirror `par_reduces` exactly. See
//! `designs/2026-06-14-computational-iota-delta-track.md` (Increment F).
//!
//! LET-PROMOTION (batch B4): `KExpr.let_` is now a GENUINE 7th KExpr constructor
//! (no longer the reducible alias `app (lam ty body) val`). `par_reduces_c` keeps
//! its `let_` ctor verbatim (the kernel-faithful ZETA contraction) and gains a
//! trailing `let_cong` congruence ctor over the genuine node. All proofs in this
//! file read `let_` as let-HEADED: a let is its own spine head (`kapp_fn` is the
//! let itself, `kexpr_const_name` none, never an iota redex), let-vs-other-head
//! case analyses discharge by constructor no-confusion (`let_ne_app`/`let_ne_lam`/
//! `let_ne_pi`), and the diamond's new overlaps are zeta-vs-zeta (par substitution
//! meet), zeta-vs-let_cong (congruence side catches up by firing zeta), and
//! let_cong-vs-let_cong (componentwise recursion).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_par_reduces_c(&mut self) -> Result<(), SpecError> {
        // par_reduces_c env: the env-indexed computational parallel reduction.
        // Identical to par_reduces except the iota ctor carries `iota_step env e e'`
        // (the directed/deterministic witness) instead of the abstract `iota_reduces`.
        self.add_inductive(
            r"inductive par_reduces_c (env : RecEnv) : KExpr → KExpr → Type
| refl : forall (e : KExpr), par_reduces_c env e e
| beta : forall (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr), par_reduces_c env A A' → par_reduces_c env body body' → par_reduces_c env arg arg' → par_reduces_c env (KExpr.app (KExpr.lam A body) arg) (instantiate body' arg')
| app : forall (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), par_reduces_c env f f' → par_reduces_c env a a' → par_reduces_c env (KExpr.app f a) (KExpr.app f' a')
| lam : forall (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_c env ty ty' → par_reduces_c env body body' → par_reduces_c env (KExpr.lam ty body) (KExpr.lam ty' body')
| pi : forall (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_c env dom dom' → par_reduces_c env body body' → par_reduces_c env (KExpr.pi dom body) (KExpr.pi dom' body')
| forall_ : forall (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_c env dom dom' → par_reduces_c env body body' → par_reduces_c env (KExpr.forall_ dom body) (KExpr.forall_ dom' body')
| let_ : forall (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_c env ty ty' → par_reduces_c env val val' → par_reduces_c env body body' → par_reduces_c env (KExpr.let_ ty val body) (instantiate body' val')
| iota : forall (e : KExpr) (e' : KExpr), iota_step env e e' → par_reduces_c env e e'
| let_cong : forall (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_c env ty ty' → par_reduces_c env val val' → par_reduces_c env body body' → par_reduces_c env (KExpr.let_ ty val body) (KExpr.let_ ty' val' body')
| proj : forall (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr), par_reduces_c env sub sub' → par_reduces_c env (KExpr.proj s i sub) (KExpr.proj s i sub')",
            "par_reduces_c env e e' — the env-indexed computational parallel reduction. Identical to \
             par_reduces except the iota constructor carries the directed, deterministic iota_step env \
             e e' (not the abstract iota_reduces), so the iota cross-joins can use \
             iota_step_deterministic. Since the let-promotion, KExpr.let_ is a GENUINE 7th constructor: \
             the let_ ctor is the kernel-faithful ZETA contraction (target instantiate body' val') and \
             the trailing let_cong ctor is its non-contracting positional congruence (target \
             KExpr.let_ ty' val' body'). A let_ node is its own spine head (headName none), so it is \
             iota-shape-disjoint. Part of #2859 (Increment F) + the let-promotion batch B4.",
        )?;

        // par_strips_witness_c env: the par_reduces_c-legged meeting-point package
        // (mirror of par_strips_witness).
        self.add_inductive(
            r"inductive par_strips_witness_c (env : RecEnv) : KExpr → KExpr → Type
| intro : forall (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), par_reduces_c env e1 e3 → par_reduces_c env e2 e3 → par_strips_witness_c env e1 e2",
            "par_strips_witness_c env e1 e2 packages a common reduct e3 with par_reduces_c env e1 e3 and \
             par_reduces_c env e2 e3 — the single-step join witness for the computational relation. \
             Part of #2859 (Increment F).",
        )?;

        // par_strips_iota_iota_c: the (iota, iota) cross-join — the FIRST cross-case,
        // closed by determinism ALONE (no Increment-E dependency). Two iota_step
        // reducts of the SAME source are equal (iota_step_deterministic), so they
        // meet at e1 = e2: left leg refl e1, right leg refl e2 transported along
        // e2 = e1. This is the payoff of the keystone determinism.
        self.add_definition(SpecDefinition {
            name: "par_strips_iota_iota_c".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "iota_step env e e1 -> iota_step env e e2 -> par_strips_witness_c env e1 e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
                    "(h1 : iota_step env e e1) (h2 : iota_step env e e2) => ",
                    "par_strips_witness_c.intro env e1 e2 e1 ",
                    "(par_reduces_c.refl env e1) ",
                    "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env e2 x) e2 e1 ",
                    "(Eq.symm KExpr e1 e2 (iota_step_deterministic env e e1 e2 h1 h2)) ",
                    "(par_reduces_c.refl env e2))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The (iota, iota) cross-join of par_strips_c: two iota_step reductions of the same ",
                "source meet, because iota_step_deterministic forces e1 = e2. Meet at e1 — left leg ",
                "par_reduces_c.refl, right leg refl transported along e2 = e1 via Eq.substType + Eq.symm. ",
                "Closed by determinism alone (no Increment-E dependency). The payoff of the keystone. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment F)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.refl".to_string(),
                "par_strips_witness_c".to_string(),
                "par_strips_witness_c.intro".to_string(),
                "iota_step_deterministic".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_bd_subsumes_par_c: the iota-free relation embeds into
        // par_reduces_c — par_reduces_bd.rec maps each of the 8 iota-free ctors
        // (incl. the let-promotion's trailing let_cong congruence) to its
        // identically-shaped par_reduces_c ctor (env threaded). The fabric the
        // (iota, iota-free-structural) cross-cases delegate through. Mirror of
        // par_reduces_bd_subsumes_par (par_reduction.rs:238).
        self.add_definition(SpecDefinition {
            name: "par_reduces_bd_subsumes_par_c".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr), ",
                "par_reduces_bd e e' -> par_reduces_c env e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e0 : KExpr) (e0' : KExpr) (h0 : par_reduces_bd e0 e0') => ",
                    "par_reduces_bd.rec ",
                    "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_bd e e') => par_reduces_c env e e') ",
                    "(fun (e : KExpr) => par_reduces_c.refl env e) ",
                    "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) ",
                    "(_hA : par_reduces_bd A A') (_hb : par_reduces_bd body body') (_harg : par_reduces_bd arg arg') ",
                    "(ihA : par_reduces_c env A A') (ihb : par_reduces_c env body body') (iharg : par_reduces_c env arg arg') => ",
                    "par_reduces_c.beta env A A' body body' arg arg' ihA ihb iharg) ",
                    "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(_hf : par_reduces_bd f f') (_ha : par_reduces_bd a a') ",
                    "(ihf : par_reduces_c env f f') (iha : par_reduces_c env a a') => ",
                    "par_reduces_c.app env f f' a a' ihf iha) ",
                    "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces_bd ty ty') (_hb : par_reduces_bd body body') ",
                    "(ihty : par_reduces_c env ty ty') (ihb : par_reduces_c env body body') => ",
                    "par_reduces_c.lam env ty ty' body body' ihty ihb) ",
                    "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hd : par_reduces_bd dom dom') (_hb : par_reduces_bd body body') ",
                    "(ihd : par_reduces_c env dom dom') (ihb : par_reduces_c env body body') => ",
                    "par_reduces_c.pi env dom dom' body body' ihd ihb) ",
                    "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hd : par_reduces_bd dom dom') (_hb : par_reduces_bd body body') ",
                    "(ihd : par_reduces_c env dom dom') (ihb : par_reduces_c env body body') => ",
                    "par_reduces_c.forall_ env dom dom' body body' ihd ihb) ",
                    "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces_bd ty ty') (_hv : par_reduces_bd val val') (_hb : par_reduces_bd body body') ",
                    "(ihty : par_reduces_c env ty ty') (ihv : par_reduces_c env val val') (ihb : par_reduces_c env body body') => ",
                    "par_reduces_c.let_ env ty ty' val val' body body' ihty ihv ihb) ",
                    "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces_bd ty ty') (_hv : par_reduces_bd val val') (_hb : par_reduces_bd body body') ",
                    "(ihty : par_reduces_c env ty ty') (ihv : par_reduces_c env val val') (ihb : par_reduces_c env body body') => ",
                    "par_reduces_c.let_cong env ty ty' val val' body body' ihty ihv ihb) ",
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
                    "(_hsub : par_reduces_bd sub sub') (ihsub : par_reduces_c env sub sub') => ",
                    "par_reduces_c.proj env s i sub sub' ihsub) ",
                    "e0 e0' h0"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Iota-free parallel reduction embeds into the computational par_reduces_c: ",
                "par_reduces_bd.rec maps each of the 8 iota-free constructors (refl/beta/app/lam/pi/",
                "forall_/let_/let_cong) to its identically-shaped par_reduces_c constructor (env ",
                "threaded). The fabric the (iota, iota-free) cross-cases delegate through. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment F)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd.rec".to_string(),
                "par_reduces_c".to_string(),
                "par_reduces_c.refl".to_string(),
                "par_reduces_c.beta".to_string(),
                "par_reduces_c.app".to_string(),
                "par_reduces_c.lam".to_string(),
                "par_reduces_c.pi".to_string(),
                "par_reduces_c.forall_".to_string(),
                "par_reduces_c.let_".to_string(),
                "par_reduces_c.let_cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_iota_left_refl_c / _right_refl_c: the (iota, refl) and
        // (refl, iota) cross-joins — an iota_step reduct e => e' and the identity
        // e => e join at e'. Trivial re-wraps via par_reduces_c.iota (mirrors the
        // landed par_strips_iota_left/right_refl, par_reduction.rs:3649/3697, now
        // carrying iota_step). No fact about the redex asserted. DerivedProved.
        for (name, witness_args, leg1, leg2, doc) in [
            (
                "par_strips_iota_left_refl_c",
                "e' e e'",
                "(par_reduces_c.refl env e')",
                "(par_reduces_c.iota env e e' h)",
                "(iota, refl) join: iota reduct e => e' and identity e => e meet at e'.",
            ),
            (
                "par_strips_iota_right_refl_c",
                "e e' e'",
                "(par_reduces_c.iota env e e' h)",
                "(par_reduces_c.refl env e')",
                "(refl, iota) join: identity e => e and iota reduct e => e' meet at e'.",
            ),
        ] {
            // conclusion shape: left_refl -> witness_c env e' e ; right_refl -> witness_c env e e'
            let concl = if name.contains("left") {
                "e' e"
            } else {
                "e e'"
            };
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    "forall (env : RecEnv) (e : KExpr) (e' : KExpr), iota_step env e e' -> par_strips_witness_c env {concl}"
                ),
                value_src: Some(format!(
                    concat!(
                        "fun (env : RecEnv) (e : KExpr) (e' : KExpr) (h : iota_step env e e') => ",
                        "par_strips_witness_c.intro env {witness_args} {leg1} {leg2}"
                    ),
                    witness_args = witness_args,
                    leg1 = leg1,
                    leg2 = leg2,
                )),
                is_axiom: false,
                description: format!(
                    "{doc} Re-wrap via par_reduces_c.iota (carries iota_step). DerivedProved, zero axiom_deps. Part of #2859 (Increment F)."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_reduces_c".to_string(),
                    "par_reduces_c.refl".to_string(),
                    "par_reduces_c.iota".to_string(),
                    "par_strips_witness_c".to_string(),
                    "par_strips_witness_c.intro".to_string(),
                    "iota_step".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // par_lift_c: lift congruence for the computational relation, stated over a
        // par_reduces_bd SOURCE (iota-free) and landed in par_reduces_c via the
        // subsumption embedding — so it inherits par_lift_bd's proof and never
        // touches an iota arm (avoids needing iota_lift_commutes). The v⇒v' half's
        // lifting companion for binder cross-cases.
        self.add_definition(SpecDefinition {
            name: "par_lift_c".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (v : KExpr) (v' : KExpr) (c : Nat) (a : Nat), ",
                "par_reduces_bd v v' -> par_reduces_c env (lift_at v c a) (lift_at v' c a)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (v : KExpr) (v' : KExpr) (c : Nat) (a : Nat) ",
                    "(h : par_reduces_bd v v') => ",
                    "par_reduces_bd_subsumes_par_c env (lift_at v c a) (lift_at v' c a) ",
                    "(par_lift_bd v v' c a h)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Lift congruence for par_reduces_c over an iota-free source: par_reduces_bd v v' implies ",
                "par_reduces_c env (lift_at v c a) (lift_at v' c a). Embeds par_lift_bd via ",
                "par_reduces_bd_subsumes_par_c (no iota arm). DerivedProved, zero axiom_deps. Part of #2859 (Increment F)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_c".to_string(),
                "par_reduces_bd_subsumes_par_c".to_string(),
                "par_lift_bd".to_string(),
                "lift_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_lift_full_c: THE LIFT E-core PAYOFF (#8). The FULL-relation lift
        // congruence for par_reduces_c — including the iota arm. Unlike par_lift_c
        // (which embeds the iota-free par_lift_bd and never touches an iota arm), this
        // recurses on a genuine par_reduces_c SOURCE: the 8 structural arms mirror
        // par_lift_bd (lift distributes over the ctor, binder arms at cutoff succ c,
        // beta/let_ transport the contraction via lift_instantiate_swap, let_cong is
        // the componentwise congruence over the genuine let node), and the
        // IOTA arm wraps iota_lift_commutes (the LIFT E-core keystone) in
        // par_reduces_c.iota — a single par-step (lift commutes exactly). The gate the
        // full-relation par_subst's (beta,beta) contraction cross-cases need.
        self.add_definition(SpecDefinition {
            name: "par_lift_full_c".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (v : KExpr) (v' : KExpr) (c : Nat) (a : Nat), ",
                "RecEnvLiftClosed env -> par_reduces_c env v v' -> ",
                "par_reduces_c env (lift_at v c a) (lift_at v' c a)"
            )
            .to_string(),
            value_src: Some(par_lift_full_c_proof()),
            is_axiom: false,
            description: concat!(
                "FULL-relation lift congruence for par_reduces_c: under a lift-closed env, ",
                "par_reduces_c env v v' implies par_reduces_c env (lift_at v c a) (lift_at v' c a). ",
                "par_reduces_c.rec on v => v': the 8 structural arms mirror par_lift_bd (lift distributes ",
                "over the ctor, binder arms at cutoff succ c, beta/let_ transport via ",
                "lift_instantiate_swap, let_cong componentwise over the genuine let node), the IOTA arm = ",
                "iota_lift_commutes (LIFT E-core keystone) wrapped ",
                "in par_reduces_c.iota (single par-step). The LIFT E-core payoff — the gate the ",
                "full-relation par_subst (beta,beta) contraction cross-cases need. DerivedProved, zero ",
                "axiom_deps. Part of #2859 (LIFT E-core)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.rec".to_string(),
                "par_reduces_c.refl".to_string(),
                "par_reduces_c.beta".to_string(),
                "par_reduces_c.app".to_string(),
                "par_reduces_c.lam".to_string(),
                "par_reduces_c.pi".to_string(),
                "par_reduces_c.forall_".to_string(),
                "par_reduces_c.let_".to_string(),
                "par_reduces_c.let_cong".to_string(),
                "par_reduces_c.iota".to_string(),
                "par_reduces_c.proj".to_string(),
                "RecEnvLiftClosed".to_string(),
                "iota_lift_commutes".to_string(),
                "lift_at".to_string(),
                "lift_instantiate_swap".to_string(),
                "instantiate_at".to_string(),
                "nat_zero_add".to_string(),
                "iota_step".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_subst_refl_c: the refl/skeleton-fixed substitution congruence (the
        // v⇒v' half of the par_subst iota arm) for the computational relation —
        // substituting parallel-reducing values v⇒v' into a FIXED term e at depth d.
        // Stated over a par_reduces_bd source and landed via subsumption, inheriting
        // par_subst_refl_bd's KExpr.rec proof without an iota arm.
        self.add_definition(SpecDefinition {
            name: "par_subst_refl_c".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (v : KExpr) (v' : KExpr) (d : Nat), ",
                "par_reduces_bd v v' -> ",
                "par_reduces_c env (instantiate_at e v d) (instantiate_at e v' d)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (v : KExpr) (v' : KExpr) (d : Nat) ",
                    "(h : par_reduces_bd v v') => ",
                    "par_reduces_bd_subsumes_par_c env (instantiate_at e v d) (instantiate_at e v' d) ",
                    "(par_subst_refl_bd e v v' d h)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Reflexive substitution congruence for par_reduces_c over an iota-free source: ",
                "par_reduces_bd v v' implies par_reduces_c env (instantiate_at e v d) (instantiate_at e v' d). ",
                "Embeds par_subst_refl_bd via par_reduces_bd_subsumes_par_c (no iota arm). The v⇒v' half ",
                "of par_subst_iota_arm. DerivedProved, zero axiom_deps. Part of #2859 (Increment F)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_c".to_string(),
                "par_reduces_bd_subsumes_par_c".to_string(),
                "par_subst_refl_bd".to_string(),
                "instantiate_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // iota_step_subst_c: E-core lifted into par_reduces_c — the SAME-VALUE iota
        // step survives substitution as a single computational par-step. Given a
        // closed env, an iota redex e ⇒ e' yields a one-step par_reduces_c on the
        // substituted terms (same value v, same depth d). This is the "E-core
        // (same-value step)" primitive the par_subst iota arm composes with the
        // v⇒v' congruence (par_subst_refl_c). Directly wraps iota_subst_commutes.
        self.add_definition(SpecDefinition {
            name: "iota_step_subst_c".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr) (v : KExpr) (d : Nat), ",
                "RecEnvClosed env -> iota_step env e e' -> ",
                "par_reduces_c env (instantiate_at e v d) (instantiate_at e' v d)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (e' : KExpr) (v : KExpr) (d : Nat) ",
                    "(closed : RecEnvClosed env) (h : iota_step env e e') => ",
                    "par_reduces_c.iota env (instantiate_at e v d) (instantiate_at e' v d) ",
                    "(iota_subst_commutes env e e' v d closed h)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "E-core lifted into par_reduces_c: under a closed env, the same-value iota step survives ",
                "instantiate_at as a single par_reduces_c step. Wraps iota_subst_commutes (E-core) in ",
                "par_reduces_c.iota. The directed (same-value) half of the par_subst iota arm. DerivedProved, ",
                "zero axiom_deps. Part of #2859 (Increment F)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.iota".to_string(),
                "iota_subst_commutes".to_string(),
                "RecEnvClosed".to_string(),
                "iota_step".to_string(),
                "instantiate_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_c_star: reflexive-transitive closure of par_reduces_c
        // (env-indexed mirror of par_reduces_star). The multi-step level the
        // confluence endpoint migrates to. par_reduces_c.iota is atomic (one
        // redex per step), so any reduction that fires an iota AND reduces a
        // value lands here as ≥2 steps.
        self.add_inductive(
            r"inductive par_reduces_c_star (env : RecEnv) : KExpr → KExpr → Type
| refl : forall (e : KExpr), par_reduces_c_star env e e
| step : forall (e : KExpr) (e' : KExpr) (e'' : KExpr), par_reduces_c env e e' → par_reduces_c_star env e' e'' → par_reduces_c_star env e e''",
            "par_reduces_c_star env e e'' is the reflexive-transitive closure of par_reduces_c: either \
             e = e'' (refl) or e parallel-reduces to an intermediate e' that continues to e''. The \
             multi-step level the par_reduces_c confluence endpoint lives at. Part of #2859 (Increment F).",
        )?;

        // par_subsumes_par_c_star: single par_reduces_c step embeds into the closure.
        self.add_definition(SpecDefinition {
            name: "par_subsumes_par_c_star".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr), ",
                "par_reduces_c env e e' -> par_reduces_c_star env e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (e' : KExpr) (h : par_reduces_c env e e') => ",
                    "par_reduces_c_star.step env e e' e' h (par_reduces_c_star.refl env e')"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Single-step par_reduces_c embeds into par_reduces_c_star: par_reduces_c_star.step with the ",
                "singleton tail filled by par_reduces_c_star.refl. DerivedProved, zero axiom_deps. Part of #2859 (Increment F)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.refl".to_string(),
                "par_reduces_c_star.step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_c_star_trans: transitivity (mirror of par_reduces_star_trans),
        // par_reduces_c_star.rec on the first chain, prefixing each step onto the
        // recursively-extended tail.
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_star_trans".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), ",
                "par_reduces_c_star env e1 e2 -> par_reduces_c_star env e2 e3 -> ",
                "par_reduces_c_star env e1 e3"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e1 : KExpr) (e2 : KExpr) (e3 : KExpr) ",
                    "(h1 : par_reduces_c_star env e1 e2) (h2 : par_reduces_c_star env e2 e3) => ",
                    "par_reduces_c_star.rec env ",
                    "(fun (a : KExpr) (b : KExpr) (_ : par_reduces_c_star env a b) => ",
                    "par_reduces_c_star env b e3 -> par_reduces_c_star env a e3) ",
                    "(fun (e : KExpr) (k : par_reduces_c_star env e e3) => k) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : par_reduces_c env e e') ",
                    "(_htail : par_reduces_c_star env e' e'') ",
                    "(ih : par_reduces_c_star env e'' e3 -> par_reduces_c_star env e' e3) ",
                    "(k : par_reduces_c_star env e'' e3) => ",
                    "par_reduces_c_star.step env e e' e3 hstep (ih k)) ",
                    "e1 e2 h1 h2"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Transitivity of par_reduces_c_star. par_reduces_c_star.rec on the first chain, prefixing ",
                "each step onto the recursively-extended tail (mirror of par_reduces_star_trans). DerivedProved, ",
                "zero axiom_deps. Part of #2859 (Increment F)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.rec".to_string(),
                "par_reduces_c_star.step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_subst_iota_arm_c: the par_subst iota arm for the computational
        // relation, stated HONESTLY as a 2-step star (par_reduces_c.iota is atomic,
        // so firing the iota redex and reducing the value v⇒v' cannot be one step):
        //   RecEnvClosed env -> iota_step env e e' -> par_reduces_bd v v'
        //     -> par_reduces_c_star env (inst e v d) (inst e' v' d).
        // Step 1 (iota_step_subst_c / E-core): inst e v d ⇒ inst e' v d (same value).
        // Step 2 (par_subst_refl_c): inst e' v d ⇒ inst e' v' d (value v⇒v' into the
        // fixed reduct e'). Composed via par_reduces_c_star.step.
        self.add_definition(SpecDefinition {
            name: "par_subst_iota_arm_c".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr) (v : KExpr) (v' : KExpr) (d : Nat), ",
                "RecEnvClosed env -> iota_step env e e' -> par_reduces_bd v v' -> ",
                "par_reduces_c_star env (instantiate_at e v d) (instantiate_at e' v' d)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (e' : KExpr) (v : KExpr) (v' : KExpr) (d : Nat) ",
                    "(closed : RecEnvClosed env) (h : iota_step env e e') (hv : par_reduces_bd v v') => ",
                    "par_reduces_c_star.step env ",
                    "(instantiate_at e v d) (instantiate_at e' v d) (instantiate_at e' v' d) ",
                    "(iota_step_subst_c env e e' v d closed h) ",
                    "(par_subsumes_par_c_star env (instantiate_at e' v d) (instantiate_at e' v' d) ",
                    "(par_subst_refl_c env e' v v' d hv))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The par_subst iota arm for par_reduces_c, as a 2-step star (the atomic par_reduces_c.iota ",
                "forces multi-step): from a closed env, an iota redex e ⇒ e', and a value reduction v ⇒ v', ",
                "the substituted terms join inst e v d ⇒ inst e' v d (E-core, same value) ⇒ inst e' v' d ",
                "(value congruence on the fixed reduct). Composes iota_step_subst_c and par_subst_refl_c. This ",
                "is the iota arm that blocked the abstract par_subst (Wave 122), now closed via the ",
                "computational, deterministic iota_step. DerivedProved, zero axiom_deps. Part of #2859 (Increment F)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.step".to_string(),
                "par_subsumes_par_c_star".to_string(),
                "iota_step_subst_c".to_string(),
                "par_subst_refl_c".to_string(),
                "RecEnvClosed".to_string(),
                "iota_step".to_string(),
                "par_reduces_bd".to_string(),
                "instantiate_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_witness_c_star: the MULTI-STEP join witness (par_reduces_c_star
        // legs). The single-step par_strips_witness_c is too weak for the iota-source
        // (iota, app) cross-case, whose left join leg is intrinsically multi-step
        // (one par-step per reduced spine arg). The confluence endpoint for
        // par_reduces_c migrates to this star-legged witness.
        self.add_inductive(
            r"inductive par_strips_witness_c_star (env : RecEnv) : KExpr → KExpr → Type
| intro : forall (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), par_reduces_c_star env e1 e3 → par_reduces_c_star env e2 e3 → par_strips_witness_c_star env e1 e2",
            "par_strips_witness_c_star env e1 e2 packages a common reduct e3 with par_reduces_c_star env \
             e1 e3 and par_reduces_c_star env e2 e3 — the MULTI-STEP join witness. The confluence endpoint \
             for par_reduces_c (the single-step par_strips_witness_c cannot express the (iota,app) \
             cross-case's multi-step join leg). Part of #2859 (Increment F).",
        )?;

        // par_strips_witness_c_to_star: every single-step join is a (trivial)
        // multi-step join — lift both legs via par_subsumes_par_c_star. So the
        // already-landed (iota,iota)/(iota,refl) single-step joins immediately
        // supply star-legged joins for the migrated endpoint.
        self.add_definition(SpecDefinition {
            name: "par_strips_witness_c_to_star".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e1 : KExpr) (e2 : KExpr), ",
                "par_strips_witness_c env e1 e2 -> par_strips_witness_c_star env e1 e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e1 : KExpr) (e2 : KExpr) (w : par_strips_witness_c env e1 e2) => ",
                    "@par_strips_witness_c.rec env e1 e2 ",
                    "(fun (_w : par_strips_witness_c env e1 e2) => par_strips_witness_c_star env e1 e2) ",
                    "(fun (e3 : KExpr) ",
                    "(l1 : par_reduces_c env e1 e3) (l2 : par_reduces_c env e2 e3) => ",
                    "par_strips_witness_c_star.intro env e1 e2 e3 ",
                    "(par_subsumes_par_c_star env e1 e3 l1) ",
                    "(par_subsumes_par_c_star env e2 e3 l2)) ",
                    "w"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Lift a single-step join to a multi-step (star-legged) join: par_strips_witness_c.rec on ",
                "the witness, embedding both par_reduces_c legs into par_reduces_c_star via ",
                "par_subsumes_par_c_star. So the landed (iota,iota)/(iota,refl) joins supply star joins for ",
                "the migrated confluence endpoint. DerivedProved, zero axiom_deps. Part of #2859 (Increment F)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_strips_witness_c".to_string(),
                "par_strips_witness_c.rec".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_witness_c_star.intro".to_string(),
                "par_reduces_c".to_string(),
                "par_subsumes_par_c_star".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ============================================================
        // STRONG-CONFLUENCE TILING SCAFFOLD (Huet's strong confluence => CR).
        //
        // par_strips_c_full only establishes that par_reduces_c is WEAKLY confluent
        // (WCR): two single steps join via par_strips_witness_c_star, where BOTH legs
        // are full par_reduces_c_star reductions. WCR does NOT imply Church-Rosser
        // without termination (Newman's lemma; mechanically refuted in the abstract
        // StarDiamond scratch). The correct lift is HUET STRONG CONFLUENCE: two single
        // steps join with ONE leg bounded to <= 1 step. The pieces below port the
        // abstract StrongConfluent => Star-confluent tiling so that Church-Rosser of
        // par_reduces_c_star is reduced to the SINGLE honest obligation "par_reduces_c
        // is strongly confluent" (par_reduces_c_star_diamond_of_strong's SC argument).
        // ============================================================

        // par_strong_join_c: the STRONG-confluence join witness (abstract
        // `exists d, Star b d and ReflGen c d`). The c-leg is bounded to <= 1 step,
        // encoded directly as the CONSTRUCTOR choice so the witness can be eliminated
        // with the single-step recursor (no separate reflexive-closure inductive):
        //   * zero — the c-leg took ZERO steps, so the meet IS c: b =>* c.
        //   * one  — the c-leg took ONE step c => d, with the b-leg b =>* d.
        // Both ctors land at the SAME indices (b, c), so the recursor needs no
        // cross-constructor index unification. The asymmetry (one bounded leg) is
        // exactly what lets the strip/confluence induction terminate; the symmetric
        // par_strips_witness_c_star is only WCR.
        self.add_inductive(
            r"inductive par_strong_join_c (env : RecEnv) : KExpr → KExpr → Type
| zero : forall (b : KExpr) (c : KExpr), par_reduces_c_star env b c → par_strong_join_c env b c
| one : forall (b : KExpr) (c : KExpr) (d : KExpr), par_reduces_c_star env b d → par_reduces_c env c d → par_strong_join_c env b c",
            "par_strong_join_c env b c is the Huet strong-confluence join witness for par_reduces_c: \
             the b-leg is an unbounded par_reduces_c_star reduction (covering iota cascades) and the \
             c-leg is BOUNDED to <= 1 step, encoded as the constructor choice — zero (meet at c, b =>* c) \
             or one (single c => d, b =>* d). The output shape of strong confluence; strictly stronger \
             than the symmetric (WCR-only) par_strips_witness_c_star. Part of #2859 (strong-confluence \
             tiling).",
        )?;

        // par_strips_c_semi_strip_of_strong: the SEMI-STRIP lemma of the strong-
        // confluence tiling (abstract `strong_semi_strip`). Given a strong-confluence
        // hypothesis SC for par_reduces_c, a multi-step reduction a =>* c and a single
        // step a => b join via par_strips_witness_c_star. Induction on the star leg
        // a =>* c (par_reduces_c_star.rec); the step arm feeds the two single head
        // steps (a => b, a => a1) through SC, then case-splits the BOUNDED refl-gen
        // a1-leg (par_reduces_c_refl.rec): the refl arm short-circuits to the tail, the
        // single arm feeds its one step into the IH. The <= 1-step c-leg of strong
        // confluence is exactly what makes the induction terminate (a symmetric WCR
        // witness would not). Parameterized on SC — zero new axioms.
        self.add_definition(SpecDefinition {
            name: "par_strips_c_semi_strip_of_strong".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) ",
                "(SC : forall (a : KExpr) (b : KExpr) (c : KExpr), ",
                "par_reduces_c env a b -> par_reduces_c env a c -> par_strong_join_c env b c) ",
                "(a : KExpr) (c : KExpr), ",
                "par_reduces_c_star env a c -> ",
                "forall (b : KExpr), par_reduces_c env a b -> par_strips_witness_c_star env b c"
            )
            .to_string(),
            value_src: Some(par_strips_c_semi_strip_of_strong_proof()),
            is_axiom: false,
            description: concat!(
                "The SEMI-STRIP lemma of the Huet strong-confluence tiling (abstract strong_semi_strip): ",
                "under a strong-confluence hypothesis SC for par_reduces_c, a multi-step a =>* c and a single ",
                "step a => b join via par_strips_witness_c_star. Induction on the star leg via ",
                "par_reduces_c_star.rec; the step arm pushes both single steps through SC and case-splits the ",
                "BOUNDED refl-gen leg via par_reduces_c_refl.rec (refl short-circuits, single feeds the IH). ",
                "Parameterized on SC: the strong-confluence assumption is the discharged-at-call-time hypothesis, ",
                "so the closure is genuinely zero-axiom. DerivedProved, zero axiom_deps. Part of #2859 ",
                "(strong-confluence tiling)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.rec".to_string(),
                "par_reduces_c_star.refl".to_string(),
                "par_reduces_c_star_trans".to_string(),
                "par_subsumes_par_c_star".to_string(),
                "par_strong_join_c".to_string(),
                "par_strong_join_c.rec".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_witness_c_star.intro".to_string(),
                "par_strips_witness_c_star.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_c_star_diamond_of_strong: THE TILING BRICK (abstract
        // `strong_confluent`). Given a strong-confluence hypothesis SC for
        // par_reduces_c, the reflexive-transitive closure par_reduces_c_star is
        // CHURCH-ROSSER: any two multi-step reductions e =>* e1, e =>* e2 join via
        // par_strips_witness_c_star. Induction on the first star leg e =>* e1
        // (par_reduces_c_star.rec, motive generalized over the second leg); each head
        // step is stripped against the second leg via par_strips_c_semi_strip_of_strong,
        // then the IH joins the residuals, re-closed with par_reduces_c_star_trans.
        //
        // This LANDS the Huet strong-confluence => Church-Rosser tiling as a 0-axiom
        // brick and ISOLATES the entire remaining confluence obligation to exactly the
        // SC hypothesis ("par_reduces_c is strongly confluent"). Discharging SC (the
        // honest residual — see the strengthening assessment) reduces Church-Rosser of
        // par_reduces_c_star, hence def_eq_joinable / church_rosser_whnf, to that one
        // clean obligation. SC is a bound parameter (NOT a registered axiom), so the
        // closure is genuinely zero-axiom.
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_star_diamond_of_strong".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) ",
                "(SC : forall (a : KExpr) (b : KExpr) (c : KExpr), ",
                "par_reduces_c env a b -> par_reduces_c env a c -> par_strong_join_c env b c) ",
                "(e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "par_reduces_c_star env e e1 -> par_reduces_c_star env e e2 -> ",
                "par_strips_witness_c_star env e1 e2"
            )
            .to_string(),
            value_src: Some(par_reduces_c_star_diamond_of_strong_proof()),
            is_axiom: false,
            description: concat!(
                "THE TILING BRICK (abstract strong_confluent): under a strong-confluence hypothesis SC for ",
                "par_reduces_c, par_reduces_c_star is Church-Rosser. Induction on the first star leg via ",
                "par_reduces_c_star.rec (motive generalized over the second leg); each head step is stripped ",
                "against the second leg by par_strips_c_semi_strip_of_strong, the IH joins the residuals, and ",
                "par_reduces_c_star_trans re-closes. Lands the Huet strong-confluence => Church-Rosser tiling ",
                "0-axiom and ISOLATES the remaining confluence obligation to exactly SC. SC is a bound ",
                "parameter, not a registered axiom, so the closure is genuinely zero-axiom. DerivedProved, ",
                "zero axiom_deps. Part of #2859 (strong-confluence tiling)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.rec".to_string(),
                "par_reduces_c_star.refl".to_string(),
                "par_reduces_c_star_trans".to_string(),
                "par_strong_join_c".to_string(),
                "par_strips_c_semi_strip_of_strong".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_witness_c_star.intro".to_string(),
                "par_strips_witness_c_star.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_c_list: pointwise parallel reduction on KExpr lists. The
        // spine-argument relation the (iota, app) cross-case needs — when an iota
        // redex's outer app reduces, its spine args par-reduce pointwise, and the
        // reduct (apply_spine over those args) par-reduces accordingly.
        self.add_inductive(
            r"inductive par_reduces_c_list (env : RecEnv) : ListType KExpr → ListType KExpr → Type
| nil : par_reduces_c_list env (ListType.nil KExpr) (ListType.nil KExpr)
| cons : forall (x : KExpr) (x' : KExpr) (xs : ListType KExpr) (xs' : ListType KExpr), par_reduces_c env x x' → par_reduces_c_list env xs xs' → par_reduces_c_list env (ListType.cons KExpr x xs) (ListType.cons KExpr x' xs')",
            "par_reduces_c_list env xs xs' — pointwise parallel reduction of KExpr lists (nil to nil; cons \
             reduces head and tail). The spine-argument relation for the (iota,app) cross-case of \
             par_strips_c. Part of #2859 (Increment F).",
        )?;

        // apply_spine_par_c: apply_spine is a parallel-reduction congruence in both
        // its argument list and its head. ListType-induction (par_reduces_c_list.rec)
        // with the motive universalizing the head; nil arm = head reduction
        // transported through apply_spine_nil, cons arm = par_reduces_c.app on the
        // new head then the tail IH, transported through apply_spine_cons.
        self.add_definition(SpecDefinition {
            name: "apply_spine_par_c".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (xs : ListType KExpr) (xs' : ListType KExpr) (head : KExpr) (head' : KExpr), ",
                "par_reduces_c_list env xs xs' -> par_reduces_c env head head' -> ",
                "par_reduces_c env (apply_spine xs head) (apply_spine xs' head')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (xs : ListType KExpr) (xs' : ListType KExpr) (head : KExpr) (head' : KExpr) ",
                    "(hl : par_reduces_c_list env xs xs') (hh : par_reduces_c env head head') => ",
                    "par_reduces_c_list.rec env ",
                    "(fun (a : ListType KExpr) (a' : ListType KExpr) (_ : par_reduces_c_list env a a') => ",
                    "forall (h : KExpr) (h' : KExpr), par_reduces_c env h h' -> ",
                    "par_reduces_c env (apply_spine a h) (apply_spine a' h')) ",
                    // nil arm
                    "(fun (h : KExpr) (h' : KExpr) (hp : par_reduces_c env h h') => ",
                    "Eq.substType KExpr ",
                    "(fun (Z : KExpr) => par_reduces_c env (apply_spine (ListType.nil KExpr) h) Z) ",
                    "h' (apply_spine (ListType.nil KExpr) h') ",
                    "(Eq.symm KExpr (apply_spine (ListType.nil KExpr) h') h' (apply_spine_nil h')) ",
                    "(Eq.substType KExpr ",
                    "(fun (Z : KExpr) => par_reduces_c env Z h') ",
                    "h (apply_spine (ListType.nil KExpr) h) ",
                    "(Eq.symm KExpr (apply_spine (ListType.nil KExpr) h) h (apply_spine_nil h)) ",
                    "hp)) ",
                    // cons arm
                    "(fun (x : KExpr) (x' : KExpr) (xs0 : ListType KExpr) (xs0' : ListType KExpr) ",
                    "(hx : par_reduces_c env x x') (hxs : par_reduces_c_list env xs0 xs0') ",
                    "(ihxs : forall (h : KExpr) (h' : KExpr), par_reduces_c env h h' -> ",
                    "par_reduces_c env (apply_spine xs0 h) (apply_spine xs0' h')) => ",
                    "fun (h : KExpr) (h' : KExpr) (hp : par_reduces_c env h h') => ",
                    "Eq.substType KExpr ",
                    "(fun (Z : KExpr) => par_reduces_c env (apply_spine (ListType.cons KExpr x xs0) h) Z) ",
                    "(apply_spine xs0' (KExpr.app h' x')) (apply_spine (ListType.cons KExpr x' xs0') h') ",
                    "(Eq.symm KExpr (apply_spine (ListType.cons KExpr x' xs0') h') (apply_spine xs0' (KExpr.app h' x')) ",
                    "(apply_spine_cons x' xs0' h')) ",
                    "(Eq.substType KExpr ",
                    "(fun (Z : KExpr) => par_reduces_c env Z (apply_spine xs0' (KExpr.app h' x'))) ",
                    "(apply_spine xs0 (KExpr.app h x)) (apply_spine (ListType.cons KExpr x xs0) h) ",
                    "(Eq.symm KExpr (apply_spine (ListType.cons KExpr x xs0) h) (apply_spine xs0 (KExpr.app h x)) ",
                    "(apply_spine_cons x xs0 h)) ",
                    "(ihxs (KExpr.app h x) (KExpr.app h' x') (par_reduces_c.app env h h' x x' hp hx)))) ",
                    "xs xs' hl head head' hh"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "apply_spine is a parallel-reduction congruence: pointwise-reducing args (par_reduces_c_list) ",
                "and a reducing head give par_reduces_c on the spine applications. par_reduces_c_list.rec with ",
                "the head universalized; nil via apply_spine_nil, cons via par_reduces_c.app + the tail IH + ",
                "apply_spine_cons. The spine-congruence the (iota,app) cross-case's left leg needs. DerivedProved, ",
                "zero axiom_deps. Part of #2859 (Increment F)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.app".to_string(),
                "par_reduces_c_list".to_string(),
                "par_reduces_c_list.rec".to_string(),
                "apply_spine".to_string(),
                "apply_spine_nil".to_string(),
                "apply_spine_cons".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_c_list_refl: pointwise reflexivity — every list par-reduces to
        // itself. ListType.rec on xs, par_reduces_c.refl at each element. The refl
        // base for spine congruences (a fixed prefix/extra segment of a redex spine
        // par-reduces to itself).
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_list_refl".to_string(),
            type_src: "forall (env : RecEnv) (xs : ListType KExpr), par_reduces_c_list env xs xs"
                .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (xs : ListType KExpr) => ",
                    "ListType.rec KExpr ",
                    "(fun (a : ListType KExpr) => par_reduces_c_list env a a) ",
                    "(par_reduces_c_list.nil env) ",
                    "(fun (x : KExpr) (rest : ListType KExpr) (ih : par_reduces_c_list env rest rest) => ",
                    "par_reduces_c_list.cons env x x rest rest (par_reduces_c.refl env x) ih) ",
                    "xs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Reflexivity of pointwise parallel list reduction: par_reduces_c_list env xs xs. ListType.rec ",
                "on xs with par_reduces_c.refl at each element. The refl base for spine congruences. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment F)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.refl".to_string(),
                "par_reduces_c_list".to_string(),
                "par_reduces_c_list.nil".to_string(),
                "par_reduces_c_list.cons".to_string(),
                "ListType.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_c_list_append: pointwise par-reduction respects list_append.
        // par_reduces_c_list.rec on the first list (motive append-ing the fixed
        // second), nil via list_append_nil, cons via par_reduces_c_list.cons +
        // list_append_cons. The snoc law kapp_args (app f a) = append (kapp_args f)
        // [a] then lifts an app-step into a spine-args congruence (the (iota,app)
        // cross-case). Mirror of list_map_append.
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_list_append".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (xs : ListType KExpr) (xs' : ListType KExpr) (ys : ListType KExpr) (ys' : ListType KExpr), ",
                "par_reduces_c_list env xs xs' -> par_reduces_c_list env ys ys' -> ",
                "par_reduces_c_list env (list_append xs ys) (list_append xs' ys')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (xs : ListType KExpr) (xs' : ListType KExpr) (ys : ListType KExpr) (ys' : ListType KExpr) ",
                    "(hxs : par_reduces_c_list env xs xs') (hys : par_reduces_c_list env ys ys') => ",
                    "par_reduces_c_list.rec env ",
                    "(fun (a : ListType KExpr) (a' : ListType KExpr) (_ : par_reduces_c_list env a a') => ",
                    "par_reduces_c_list env (list_append a ys) (list_append a' ys')) ",
                    // nil arm: transport hys along list_append_nil on both sides.
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_c_list env (list_append (ListType.nil KExpr) ys) Z) ",
                    "ys' (list_append (ListType.nil KExpr) ys') ",
                    "(Eq.symm (ListType KExpr) (list_append (ListType.nil KExpr) ys') ys' (list_append_nil ys')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_c_list env Z ys') ",
                    "ys (list_append (ListType.nil KExpr) ys) ",
                    "(Eq.symm (ListType KExpr) (list_append (ListType.nil KExpr) ys) ys (list_append_nil ys)) ",
                    "hys)) ",
                    // cons arm
                    "(fun (x : KExpr) (x' : KExpr) (xs0 : ListType KExpr) (xs0' : ListType KExpr) ",
                    "(hx : par_reduces_c env x x') (hxs0 : par_reduces_c_list env xs0 xs0') ",
                    "(ih : par_reduces_c_list env (list_append xs0 ys) (list_append xs0' ys')) => ",
                    "Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_c_list env (list_append (ListType.cons KExpr x xs0) ys) Z) ",
                    "(ListType.cons KExpr x' (list_append xs0' ys')) (list_append (ListType.cons KExpr x' xs0') ys') ",
                    "(Eq.symm (ListType KExpr) (list_append (ListType.cons KExpr x' xs0') ys') (ListType.cons KExpr x' (list_append xs0' ys')) ",
                    "(list_append_cons x' xs0' ys')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_c_list env Z (ListType.cons KExpr x' (list_append xs0' ys'))) ",
                    "(ListType.cons KExpr x (list_append xs0 ys)) (list_append (ListType.cons KExpr x xs0) ys) ",
                    "(Eq.symm (ListType KExpr) (list_append (ListType.cons KExpr x xs0) ys) (ListType.cons KExpr x (list_append xs0 ys)) ",
                    "(list_append_cons x xs0 ys)) ",
                    "(par_reduces_c_list.cons env x x' (list_append xs0 ys) (list_append xs0' ys') hx ih))) ",
                    "xs xs' hxs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Pointwise par-reduction respects list_append: par_reduces_c_list xs xs' and ys ys' give ",
                "par_reduces_c_list (list_append xs ys) (list_append xs' ys'). par_reduces_c_list.rec on the ",
                "first list; nil via list_append_nil, cons via par_reduces_c_list.cons + list_append_cons. ",
                "With kapp_args_app (the snoc law) this lifts an app-step into a spine-args congruence for the ",
                "(iota,app) cross-case. DerivedProved, zero axiom_deps. Part of #2859 (Increment F)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c_list".to_string(),
                "par_reduces_c_list.rec".to_string(),
                "par_reduces_c_list.cons".to_string(),
                "list_append".to_string(),
                "list_append_nil".to_string(),
                "list_append_cons".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_tail_par_c: pointwise par-reduction respects list_tail.
        // par_reduces_c_list.rec; nil via list_tail_nil, cons exposes the tail field.
        self.add_definition(SpecDefinition {
            name: "list_tail_par_c".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (xs : ListType KExpr) (xs' : ListType KExpr), ",
                "par_reduces_c_list env xs xs' -> par_reduces_c_list env (list_tail xs) (list_tail xs')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (xs : ListType KExpr) (xs' : ListType KExpr) ",
                    "(hxs : par_reduces_c_list env xs xs') => ",
                    "par_reduces_c_list.rec env ",
                    "(fun (a : ListType KExpr) (a' : ListType KExpr) (_ : par_reduces_c_list env a a') => ",
                    "par_reduces_c_list env (list_tail a) (list_tail a')) ",
                    // nil arm
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_c_list env (list_tail (ListType.nil KExpr)) Z) ",
                    "(ListType.nil KExpr) (list_tail (ListType.nil KExpr)) ",
                    "(Eq.symm (ListType KExpr) (list_tail (ListType.nil KExpr)) (ListType.nil KExpr) list_tail_nil) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_c_list env Z (ListType.nil KExpr)) ",
                    "(ListType.nil KExpr) (list_tail (ListType.nil KExpr)) ",
                    "(Eq.symm (ListType KExpr) (list_tail (ListType.nil KExpr)) (ListType.nil KExpr) list_tail_nil) ",
                    "(par_reduces_c_list.nil env))) ",
                    // cons arm
                    "(fun (x : KExpr) (x' : KExpr) (xs0 : ListType KExpr) (xs0' : ListType KExpr) ",
                    "(hx : par_reduces_c env x x') (hxs0 : par_reduces_c_list env xs0 xs0') ",
                    "(_ih : par_reduces_c_list env (list_tail xs0) (list_tail xs0')) => ",
                    "Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_c_list env (list_tail (ListType.cons KExpr x xs0)) Z) ",
                    "xs0' (list_tail (ListType.cons KExpr x' xs0')) ",
                    "(Eq.symm (ListType KExpr) (list_tail (ListType.cons KExpr x' xs0')) xs0' (list_tail_cons x' xs0')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_c_list env Z xs0') ",
                    "xs0 (list_tail (ListType.cons KExpr x xs0)) ",
                    "(Eq.symm (ListType KExpr) (list_tail (ListType.cons KExpr x xs0)) xs0 (list_tail_cons x xs0)) ",
                    "hxs0)) ",
                    "xs xs' hxs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Pointwise par-reduction respects list_tail. par_reduces_c_list.rec; nil via list_tail_nil, ",
                "cons exposes the tail field. Mirror of list_map_tail. DerivedProved, zero axiom_deps. Part of #2859 (Increment F)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c_list".to_string(),
                "par_reduces_c_list.rec".to_string(),
                "par_reduces_c_list.nil".to_string(),
                "list_tail".to_string(),
                "list_tail_nil".to_string(),
                "list_tail_cons".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_drop_par_c: pointwise par-reduction respects list_drop (the iota
        // reduct's extras/fields/prefix are list_drop/list_take segments). Nat.rec on
        // the offset (motive universalizing the two lists); zero via list_drop_zero,
        // succ via list_drop_succ + list_tail_par_c + the IH. Mirror of list_map_drop.
        self.add_definition(SpecDefinition {
            name: "list_drop_par_c".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (n : Nat) (xs : ListType KExpr) (xs' : ListType KExpr), ",
                "par_reduces_c_list env xs xs' -> par_reduces_c_list env (list_drop n xs) (list_drop n xs')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (n : Nat) (xs : ListType KExpr) (xs' : ListType KExpr) ",
                    "(hxs : par_reduces_c_list env xs xs') => ",
                    "Nat.rec ",
                    "(fun (n0 : Nat) => forall (a : ListType KExpr) (a' : ListType KExpr), ",
                    "par_reduces_c_list env a a' -> par_reduces_c_list env (list_drop n0 a) (list_drop n0 a')) ",
                    // zero arm
                    "(fun (a : ListType KExpr) (a' : ListType KExpr) (ha : par_reduces_c_list env a a') => ",
                    "Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_c_list env (list_drop Nat.zero a) Z) ",
                    "a' (list_drop Nat.zero a') ",
                    "(Eq.symm (ListType KExpr) (list_drop Nat.zero a') a' (list_drop_zero a')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_c_list env Z a') ",
                    "a (list_drop Nat.zero a) ",
                    "(Eq.symm (ListType KExpr) (list_drop Nat.zero a) a (list_drop_zero a)) ",
                    "ha)) ",
                    // succ arm
                    "(fun (m : Nat) (ihm : forall (a : ListType KExpr) (a' : ListType KExpr), ",
                    "par_reduces_c_list env a a' -> par_reduces_c_list env (list_drop m a) (list_drop m a')) => ",
                    "fun (a : ListType KExpr) (a' : ListType KExpr) (ha : par_reduces_c_list env a a') => ",
                    "Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_c_list env (list_drop (Nat.succ m) a) Z) ",
                    "(list_drop m (list_tail a')) (list_drop (Nat.succ m) a') ",
                    "(Eq.symm (ListType KExpr) (list_drop (Nat.succ m) a') (list_drop m (list_tail a')) (list_drop_succ m a')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_c_list env Z (list_drop m (list_tail a'))) ",
                    "(list_drop m (list_tail a)) (list_drop (Nat.succ m) a) ",
                    "(Eq.symm (ListType KExpr) (list_drop (Nat.succ m) a) (list_drop m (list_tail a)) (list_drop_succ m a)) ",
                    "(ihm (list_tail a) (list_tail a') (list_tail_par_c env a a' ha)))) ",
                    "n xs xs' hxs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Pointwise par-reduction respects list_drop. Nat.rec on the offset (motive universalizing the ",
                "two lists); zero via list_drop_zero, succ via list_drop_succ + list_tail_par_c + the IH. The ",
                "extras/prefix segments of the iota reduct are list_drop/list_take. Mirror of list_map_drop. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment F)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c_list".to_string(),
                "list_drop".to_string(),
                "list_tail".to_string(),
                "list_tail_par_c".to_string(),
                "list_drop_zero".to_string(),
                "list_drop_succ".to_string(),
                "Nat.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_take_par_c: pointwise par-reduction respects list_take. Nat.rec on
        // the offset (motive universalizing the two lists); succ arm CASE-SPLITS the
        // par_reduces_c_list derivation via par_reduces_c_list.rec and uses the OUTER
        // Nat IH on the cons tail (no inner induction — mirror of list_map_take).
        self.add_definition(SpecDefinition {
            name: "list_take_par_c".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (n : Nat) (xs : ListType KExpr) (xs' : ListType KExpr), ",
                "par_reduces_c_list env xs xs' -> par_reduces_c_list env (list_take n xs) (list_take n xs')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (n : Nat) (xs : ListType KExpr) (xs' : ListType KExpr) ",
                    "(hxs : par_reduces_c_list env xs xs') => ",
                    "Nat.rec ",
                    "(fun (n0 : Nat) => forall (a : ListType KExpr) (a' : ListType KExpr), ",
                    "par_reduces_c_list env a a' -> par_reduces_c_list env (list_take n0 a) (list_take n0 a')) ",
                    // zero arm: list_take zero _ = nil
                    "(fun (a : ListType KExpr) (a' : ListType KExpr) (ha : par_reduces_c_list env a a') => ",
                    "Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_c_list env (list_take Nat.zero a) Z) ",
                    "(ListType.nil KExpr) (list_take Nat.zero a') ",
                    "(Eq.symm (ListType KExpr) (list_take Nat.zero a') (ListType.nil KExpr) (list_take_zero a')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_c_list env Z (ListType.nil KExpr)) ",
                    "(ListType.nil KExpr) (list_take Nat.zero a) ",
                    "(Eq.symm (ListType KExpr) (list_take Nat.zero a) (ListType.nil KExpr) (list_take_zero a)) ",
                    "(par_reduces_c_list.nil env))) ",
                    // succ arm
                    "(fun (m : Nat) (ihm : forall (a : ListType KExpr) (a' : ListType KExpr), ",
                    "par_reduces_c_list env a a' -> par_reduces_c_list env (list_take m a) (list_take m a')) => ",
                    "fun (a : ListType KExpr) (a' : ListType KExpr) (h : par_reduces_c_list env a a') => ",
                    "par_reduces_c_list.rec env ",
                    "(fun (b : ListType KExpr) (b' : ListType KExpr) (_ : par_reduces_c_list env b b') => ",
                    "par_reduces_c_list env (list_take (Nat.succ m) b) (list_take (Nat.succ m) b')) ",
                    // inner nil
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_c_list env (list_take (Nat.succ m) (ListType.nil KExpr)) Z) ",
                    "(ListType.nil KExpr) (list_take (Nat.succ m) (ListType.nil KExpr)) ",
                    "(Eq.symm (ListType KExpr) (list_take (Nat.succ m) (ListType.nil KExpr)) (ListType.nil KExpr) (list_take_succ_nil m)) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_c_list env Z (ListType.nil KExpr)) ",
                    "(ListType.nil KExpr) (list_take (Nat.succ m) (ListType.nil KExpr)) ",
                    "(Eq.symm (ListType KExpr) (list_take (Nat.succ m) (ListType.nil KExpr)) (ListType.nil KExpr) (list_take_succ_nil m)) ",
                    "(par_reduces_c_list.nil env))) ",
                    // inner cons: cons x (list_take m xs0), tail via ihm
                    "(fun (x : KExpr) (x' : KExpr) (xs0 : ListType KExpr) (xs0' : ListType KExpr) ",
                    "(hx : par_reduces_c env x x') (hxs0 : par_reduces_c_list env xs0 xs0') ",
                    "(_ih2 : par_reduces_c_list env (list_take (Nat.succ m) xs0) (list_take (Nat.succ m) xs0')) => ",
                    "Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_c_list env (list_take (Nat.succ m) (ListType.cons KExpr x xs0)) Z) ",
                    "(ListType.cons KExpr x' (list_take m xs0')) (list_take (Nat.succ m) (ListType.cons KExpr x' xs0')) ",
                    "(Eq.symm (ListType KExpr) (list_take (Nat.succ m) (ListType.cons KExpr x' xs0')) (ListType.cons KExpr x' (list_take m xs0')) (list_take_succ_cons m x' xs0')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_c_list env Z (ListType.cons KExpr x' (list_take m xs0'))) ",
                    "(ListType.cons KExpr x (list_take m xs0)) (list_take (Nat.succ m) (ListType.cons KExpr x xs0)) ",
                    "(Eq.symm (ListType KExpr) (list_take (Nat.succ m) (ListType.cons KExpr x xs0)) (ListType.cons KExpr x (list_take m xs0)) (list_take_succ_cons m x xs0)) ",
                    "(par_reduces_c_list.cons env x x' (list_take m xs0) (list_take m xs0') hx (ihm xs0 xs0' hxs0)))) ",
                    "a a' h) ",
                    "n xs xs' hxs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Pointwise par-reduction respects list_take. Nat.rec on the offset; succ arm case-splits the ",
                "derivation (par_reduces_c_list.rec) and uses the outer Nat IH on the cons tail (no inner ",
                "induction). The iota reduct's prefix segment is a list_take. Mirror of list_map_take. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment F)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c_list".to_string(),
                "par_reduces_c_list.rec".to_string(),
                "par_reduces_c_list.nil".to_string(),
                "par_reduces_c_list.cons".to_string(),
                "list_take".to_string(),
                "list_take_zero".to_string(),
                "list_take_succ_nil".to_string(),
                "list_take_succ_cons".to_string(),
                "Nat.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // kapp_args_par_c: extend a spine-args par-reduction by one applied arg.
        // Given the spine args of f par-reduce (kapp_args f ⇒_c_list kapp_args f') and
        // the new last arg reduces (a ⇒_c a'), the spine args of (app f a) par-reduce
        // to those of (app f' a'). Via kapp_args_app (snoc) + par_reduces_c_list_append.
        // The bridge from an app-ctor step to a spine-args congruence (the (iota,app)
        // cross-case feeds this its f-spine congruence + the major/extra arg step).
        self.add_definition(SpecDefinition {
            name: "kapp_args_par_c".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), ",
                "par_reduces_c_list env (kapp_args f) (kapp_args f') -> ",
                "par_reduces_c env a a' -> ",
                "par_reduces_c_list env (kapp_args (KExpr.app f a)) (kapp_args (KExpr.app f' a'))"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(hf : par_reduces_c_list env (kapp_args f) (kapp_args f')) ",
                    "(ha : par_reduces_c env a a') => ",
                    "Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_c_list env (kapp_args (KExpr.app f a)) Z) ",
                    "(list_append (kapp_args f') (ListType.cons KExpr a' (ListType.nil KExpr))) (kapp_args (KExpr.app f' a')) ",
                    "(Eq.symm (ListType KExpr) (kapp_args (KExpr.app f' a')) (list_append (kapp_args f') (ListType.cons KExpr a' (ListType.nil KExpr))) (kapp_args_app f' a')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_c_list env Z (list_append (kapp_args f') (ListType.cons KExpr a' (ListType.nil KExpr)))) ",
                    "(list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))) (kapp_args (KExpr.app f a)) ",
                    "(Eq.symm (ListType KExpr) (kapp_args (KExpr.app f a)) (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))) (kapp_args_app f a)) ",
                    "(par_reduces_c_list_append env (kapp_args f) (kapp_args f') ",
                    "(ListType.cons KExpr a (ListType.nil KExpr)) (ListType.cons KExpr a' (ListType.nil KExpr)) ",
                    "hf ",
                    "(par_reduces_c_list.cons env a a' (ListType.nil KExpr) (ListType.nil KExpr) ha (par_reduces_c_list.nil env)))))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Extend a spine-args par-reduction by one applied arg: kapp_args f ⇒_c_list kapp_args f' and ",
                "a ⇒_c a' give kapp_args (app f a) ⇒_c_list kapp_args (app f' a'). kapp_args_app (snoc) + ",
                "par_reduces_c_list_append. The bridge from an app-ctor step to a spine-args congruence for the ",
                "(iota,app) cross-case. DerivedProved, zero axiom_deps. Part of #2859 (Increment F)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c_list".to_string(),
                "par_reduces_c_list.nil".to_string(),
                "par_reduces_c_list.cons".to_string(),
                "par_reduces_c_list_append".to_string(),
                "kapp_args".to_string(),
                "kapp_args_app".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "par_reduces_c_preserves_head_const".to_string(),
            type_src: "forall (env : RecEnv) (e : KExpr) (e' : KExpr) (nm : Name) (C : Prop), Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name nm) -> par_reduces_c env e e' -> (forall (t : KExpr), Eq (OptionType Name) (kexpr_const_name (kapp_fn t)) (OptionType.some Name nm) -> C) -> (forall (t1 : KExpr) (t2 : KExpr), iota_step env t1 t2 -> C) -> C".to_string(),
            value_src: Some("fun (env : RecEnv) (e : KExpr) (e' : KExpr) (nm : Name) (C : Prop) (hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name nm)) (h : par_reduces_c env e e') (ksurv : forall (t : KExpr), Eq (OptionType Name) (kexpr_const_name (kapp_fn t)) (OptionType.some Name nm) -> C) (kiota : forall (t1 : KExpr) (t2 : KExpr), iota_step env t1 t2 -> C) => par_reduces_c.rec env (fun (e0 : KExpr) (e0' : KExpr) (_h : par_reduces_c env e0 e0') => Eq (OptionType Name) (kexpr_const_name (kapp_fn e0)) (OptionType.some Name nm) -> C) (fun (a : KExpr) (g : Eq (OptionType Name) (kexpr_const_name (kapp_fn a)) (OptionType.some Name nm)) => ksurv a g) (fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) (_hA : par_reduces_c env A A') (_hbody : par_reduces_c env body body') (_harg : par_reduces_c env arg arg') (_ihA : Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (OptionType.some Name nm) -> C) (_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> C) (_iharg : Eq (OptionType Name) (kexpr_const_name (kapp_fn arg)) (OptionType.some Name nm) -> C) (g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app (KExpr.lam A body) arg))) (OptionType.some Name nm)) => option_none_ne_some Name nm C (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.app (KExpr.lam A body) arg))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) (fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (_hf : par_reduces_c env f f') (_ha : par_reduces_c env a a') (ihf : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm) -> C) (_iha : Eq (OptionType Name) (kexpr_const_name (kapp_fn a)) (OptionType.some Name nm) -> C) (g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name nm)) => ihf (Eq.subst KExpr (fun (x : KExpr) => Eq (OptionType Name) (kexpr_const_name x) (OptionType.some Name nm)) (kapp_fn (KExpr.app f a)) (kapp_fn f) (kapp_fn_app f a) g)) (fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) (_hty : par_reduces_c env ty ty') (_hbody : par_reduces_c env body body') (_ihty : Eq (OptionType Name) (kexpr_const_name (kapp_fn ty)) (OptionType.some Name nm) -> C) (_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> C) (g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam ty body))) (OptionType.some Name nm)) => option_none_ne_some Name nm C (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.lam ty body))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) (fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) (_hd : par_reduces_c env dom dom') (_hbody : par_reduces_c env body body') (_ihd : Eq (OptionType Name) (kexpr_const_name (kapp_fn dom)) (OptionType.some Name nm) -> C) (_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> C) (g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.pi dom body))) (OptionType.some Name nm)) => option_none_ne_some Name nm C (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.pi dom body))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) (fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) (_hd : par_reduces_c env dom dom') (_hbody : par_reduces_c env body body') (_ihd : Eq (OptionType Name) (kexpr_const_name (kapp_fn dom)) (OptionType.some Name nm) -> C) (_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> C) (g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.forall_ dom body))) (OptionType.some Name nm)) => option_none_ne_some Name nm C (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.forall_ dom body))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) (fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) (_hty : par_reduces_c env ty ty') (_hval : par_reduces_c env val val') (_hbody : par_reduces_c env body body') (_ihty : Eq (OptionType Name) (kexpr_const_name (kapp_fn ty)) (OptionType.some Name nm) -> C) (_ihval : Eq (OptionType Name) (kexpr_const_name (kapp_fn val)) (OptionType.some Name nm) -> C) (_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> C) (g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (OptionType.some Name nm)) => option_none_ne_some Name nm C (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) (fun (e0 : KExpr) (e0' : KExpr) (hstep : iota_step env e0 e0') (_g : Eq (OptionType Name) (kexpr_const_name (kapp_fn e0)) (OptionType.some Name nm)) => kiota e0 e0' hstep) (fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) (_hty : par_reduces_c env ty ty') (_hval : par_reduces_c env val val') (_hbody : par_reduces_c env body body') (_ihty : Eq (OptionType Name) (kexpr_const_name (kapp_fn ty)) (OptionType.some Name nm) -> C) (_ihval : Eq (OptionType Name) (kexpr_const_name (kapp_fn val)) (OptionType.some Name nm) -> C) (_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> C) (g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (OptionType.some Name nm)) => option_none_ne_some Name nm C (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) (fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) (_hsub : par_reduces_c env sub sub') (_ihsub : Eq (OptionType Name) (kexpr_const_name (kapp_fn sub)) (OptionType.some Name nm) -> C) (g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.proj s i sub))) (OptionType.some Name nm)) => option_none_ne_some Name nm C (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.proj s i sub))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) e e' h hhead".to_string()),
            is_axiom: false,
            description: "Under the const-head guard, a NON-iota structural par_reduces_c step preserves the const head: par_reduces_c.rec on the step (FIRST in-tree caller), app arm lifts the head via Eq.subst + kapp_fn_app, the binder/beta/let_/let_cong arms are discharged by the guard (their kapp_fn is a binder or the let node itself => kexpr_const_name = none, contradiction via option_none_ne_some), the iota arm handled per the chosen form. The sub-case (a) head-preservation for the (iota,app) join. DerivedProved, zero axiom_deps. Part of #2859 (Increment F).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.rec".to_string(),
                "iota_step".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "kapp_fn_app".to_string(),
                "option_none_ne_some".to_string(),
                "Eq.subst".to_string(),
                "Eq.trans".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "par_reduces_c_app_inv".to_string(),
            type_src: "forall (env : RecEnv) (f : KExpr) (a : KExpr) (t : KExpr) (C : KExpr -> Type), par_reduces_c env (KExpr.app f a) t -> (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a')) -> (forall (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg' : KExpr), Eq KExpr f (KExpr.lam A body) -> par_reduces_c env A A' -> par_reduces_c env body body' -> par_reduces_c env a arg' -> C (instantiate body' arg')) -> (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr t t0 -> C t0) -> C t".to_string(),
            value_src: Some("fun (env : RecEnv) (f : KExpr) (a : KExpr) (t : KExpr) (C : KExpr -> Type) (h : par_reduces_c env (KExpr.app f a) t) (kcong : (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a'))) (kbeta : (forall (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg' : KExpr), Eq KExpr f (KExpr.lam A body) -> par_reduces_c env A A' -> par_reduces_c env body body' -> par_reduces_c env a arg' -> C (instantiate body' arg'))) (kiota : (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr t t0 -> C t0)) => par_reduces_c.rec env (fun (e : KExpr) (e' : KExpr) (_h : par_reduces_c env e e') => Eq KExpr e (KExpr.app f a) -> (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a')) -> (forall (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg' : KExpr), Eq KExpr f (KExpr.lam A body) -> par_reduces_c env A A' -> par_reduces_c env body body' -> par_reduces_c env a arg' -> C (instantiate body' arg')) -> (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr e' t0 -> C t0) -> C e') (fun (e : KExpr) (eq : Eq KExpr e (KExpr.app f a)) (kc : (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a'))) (_kb : (forall (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg' : KExpr), Eq KExpr f (KExpr.lam A body) -> par_reduces_c env A A' -> par_reduces_c env body body' -> par_reduces_c env a arg' -> C (instantiate body' arg'))) (_ki : (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr e t0 -> C t0)) => Eq.substType KExpr C (KExpr.app f a) e (Eq.symm KExpr e (KExpr.app f a) eq) (kc f a (par_reduces_c.refl env f) (par_reduces_c.refl env a))) (fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) (hA : par_reduces_c env A A') (hbody : par_reduces_c env body body') (harg : par_reduces_c env arg arg') (_ihA : Eq KExpr A (KExpr.app f a) -> (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a')) -> (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0')) -> (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr A' t0 -> C t0) -> C A') (_ihbody : Eq KExpr body (KExpr.app f a) -> (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a')) -> (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0')) -> (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr body' t0 -> C t0) -> C body') (_iharg : Eq KExpr arg (KExpr.app f a) -> (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a')) -> (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0')) -> (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr arg' t0 -> C t0) -> C arg') (eq : Eq KExpr (KExpr.app (KExpr.lam A body) arg) (KExpr.app f a)) (_kc : (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a'))) (kb : (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0'))) (_ki : (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr (instantiate body' arg') t0 -> C t0)) => kb A A' body body' arg' (Eq.symm KExpr (KExpr.lam A body) f (app_inj_fst (KExpr.lam A body) arg f a eq)) hA hbody (Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x arg') arg a (app_inj_snd (KExpr.lam A body) arg f a eq) harg)) (fun (g : KExpr) (g' : KExpr) (b : KExpr) (b' : KExpr) (hg : par_reduces_c env g g') (hb : par_reduces_c env b b') (_ihg : Eq KExpr g (KExpr.app f a) -> (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a')) -> (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0')) -> (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr g' t0 -> C t0) -> C g') (_ihb : Eq KExpr b (KExpr.app f a) -> (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a')) -> (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0')) -> (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr b' t0 -> C t0) -> C b') (eq : Eq KExpr (KExpr.app g b) (KExpr.app f a)) (kc : (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a'))) (_kb : (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0'))) (_ki : (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr (KExpr.app g' b') t0 -> C t0)) => kc g' b' (Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x g') g f (app_inj_fst g b f a eq) hg) (Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x b') b a (app_inj_snd g b f a eq) hb)) (fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) (_hty : par_reduces_c env ty ty') (_hbody : par_reduces_c env body body') (_ihty : Eq KExpr ty (KExpr.app f a) -> (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a')) -> (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0')) -> (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr ty' t0 -> C t0) -> C ty') (_ihbody : Eq KExpr body (KExpr.app f a) -> (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a')) -> (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0')) -> (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr body' t0 -> C t0) -> C body') (eq : Eq KExpr (KExpr.lam ty body) (KExpr.app f a)) (_kc : (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a'))) (_kb : (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0'))) (_ki : (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr (KExpr.lam ty' body') t0 -> C t0)) => lam_ne_app ty body f a (C (KExpr.lam ty' body')) eq) (fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) (_hd : par_reduces_c env dom dom') (_hbody : par_reduces_c env body body') (_ihd : Eq KExpr dom (KExpr.app f a) -> (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a')) -> (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0')) -> (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr dom' t0 -> C t0) -> C dom') (_ihbody : Eq KExpr body (KExpr.app f a) -> (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a')) -> (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0')) -> (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr body' t0 -> C t0) -> C body') (eq : Eq KExpr (KExpr.pi dom body) (KExpr.app f a)) (_kc : (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a'))) (_kb : (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0'))) (_ki : (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr (KExpr.pi dom' body') t0 -> C t0)) => pi_ne_app dom body f a (C (KExpr.pi dom' body')) eq) (fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) (_hd : par_reduces_c env dom dom') (_hbody : par_reduces_c env body body') (_ihd : Eq KExpr dom (KExpr.app f a) -> (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a')) -> (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0')) -> (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr dom' t0 -> C t0) -> C dom') (_ihbody : Eq KExpr body (KExpr.app f a) -> (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a')) -> (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0')) -> (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr body' t0 -> C t0) -> C body') (eq : Eq KExpr (KExpr.forall_ dom body) (KExpr.app f a)) (_kc : (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a'))) (_kb : (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0'))) (_ki : (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr (KExpr.forall_ dom' body') t0 -> C t0)) => pi_ne_app dom body f a (C (KExpr.forall_ dom' body')) eq) (fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) (hty : par_reduces_c env ty ty') (hval : par_reduces_c env val val') (hbody : par_reduces_c env body body') (_ihty : Eq KExpr ty (KExpr.app f a) -> (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a')) -> (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0')) -> (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr ty' t0 -> C t0) -> C ty') (_ihval : Eq KExpr val (KExpr.app f a) -> (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a')) -> (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0')) -> (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr val' t0 -> C t0) -> C val') (_ihbody : Eq KExpr body (KExpr.app f a) -> (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a')) -> (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0')) -> (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr body' t0 -> C t0) -> C body') (eq : Eq KExpr (KExpr.let_ ty val body) (KExpr.app f a)) (_kc : (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a'))) (kb : (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0'))) (_ki : (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr (instantiate body' val') t0 -> C t0)) => let_ne_app ty val body f a (C (instantiate body' val')) eq) (fun (e : KExpr) (e' : KExpr) (hstep : iota_step env e e') (eq : Eq KExpr e (KExpr.app f a)) (_kc : (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a'))) (_kb : (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0'))) (ki : (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr e' t0 -> C t0)) => ki e' (Eq.subst KExpr (fun (x : KExpr) => iota_step env x e') e (KExpr.app f a) eq hstep) (Eq.refl KExpr e')) (fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) (_hty : par_reduces_c env ty ty') (_hval : par_reduces_c env val val') (_hbody : par_reduces_c env body body') (_ihty : Eq KExpr ty (KExpr.app f a) -> (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a')) -> (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0')) -> (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr ty' t0 -> C t0) -> C ty') (_ihval : Eq KExpr val (KExpr.app f a) -> (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a')) -> (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0')) -> (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr val' t0 -> C t0) -> C val') (_ihbody : Eq KExpr body (KExpr.app f a) -> (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a')) -> (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0')) -> (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr body' t0 -> C t0) -> C body') (eq : Eq KExpr (KExpr.let_ ty val body) (KExpr.app f a)) (_kc : (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a'))) (_kb : (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0'))) (_ki : (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr (KExpr.let_ ty' val' body') t0 -> C t0)) => let_ne_app ty val body f a (C (KExpr.let_ ty' val' body')) eq) (fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) (_hsub : par_reduces_c env sub sub') (_ihsub : Eq KExpr sub (KExpr.app f a) -> (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a')) -> (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0')) -> (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr sub' t0 -> C t0) -> C sub') (eq : Eq KExpr (KExpr.proj s i sub) (KExpr.app f a)) (_kc : (forall (f' : KExpr) (a' : KExpr), par_reduces_c env f f' -> par_reduces_c env a a' -> C (KExpr.app f' a'))) (_kb : (forall (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr), Eq KExpr f (KExpr.lam A0 body0) -> par_reduces_c env A0 A0' -> par_reduces_c env body0 body0' -> par_reduces_c env a arg0' -> C (instantiate body0' arg0'))) (_ki : (forall (t0 : KExpr), iota_step env (KExpr.app f a) t0 -> Eq KExpr (KExpr.proj s i sub') t0 -> C t0)) => proj_ne_app s i sub f a (C (KExpr.proj s i sub')) eq) (KExpr.app f a) t h (Eq.refl KExpr (KExpr.app f a)) kcong kbeta kiota".to_string()),
            is_axiom: false,
            description: "CPS shape-recovery for an app-headed par_reduces_c: from par_reduces_c (app f a) t dispatch to the congruence continuation (refl/app), the contraction continuation (beta), or the NEW iota continuation (iota_step env (app f a) t0). par_reduces_c.rec with a source-equation motive + app injectivity + Eq.subst; lam/pi/forall_ discharged by no-confusion, and (since the let-promotion) the genuinely let-headed let_/let_cong arms by let_ne_app; the iota arm uses Eq.subst (iota_step is Prop). Mirror of par_reduces_bd_app_inv + iota arm. DerivedProved, zero axiom_deps. Part of #2859 (Increment F).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.rec".to_string(),
                "par_reduces_c.refl".to_string(),
                "iota_step".to_string(),
                "app_inj_fst".to_string(),
                "app_inj_snd".to_string(),
                "lam_ne_app".to_string(),
                "pi_ne_app".to_string(),
                "let_ne_app".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.subst".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // option_none_ne_some_type: the Type-valued OptionType no-confusion. The
        // Prop-valued option_none_ne_some cannot discharge a Type-valued goal (the
        // par_reduces_c_list spine-congruence motive is in Type); this mirrors it with
        // C : Type via Empty.rec (which targets any sort) on the opt_is_none
        // discriminator transported along the false none = some equation.
        self.add_definition(SpecDefinition {
            name: "option_none_ne_some_type".to_string(),
            type_src: concat!(
                "forall (b : Type) (r : b) (C : Type), ",
                "Eq (OptionType b) (OptionType.none b) (OptionType.some b r) -> C"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (b : Type) (r : b) (C : Type) ",
                    "(h : Eq (OptionType b) (OptionType.none b) (OptionType.some b r)) => ",
                    "Empty.rec (fun (_ : Empty) => C) ",
                    "(Eq.substType (OptionType b) (opt_is_none b) ",
                    "(OptionType.none b) (OptionType.some b r) h Nat.zero)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Type-valued OptionType no-confusion: none /= some, discharging a Type-valued goal C. Empty discriminator (none -> Nat inhabited by zero, some -> Empty) transported along the false equation via opt_is_none + Empty.rec (any sort). The Type-valued sibling of option_none_ne_some, needed where the goal is in Type (par_reduces_c_list). DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_is_none".to_string(),
                "Eq.substType".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_c_spine_cong (TASK C): under the const-head guard and the
        // not-a-redex guard, a par_reduces_c step is a SPINE congruence — its spine
        // args par-reduce pointwise. par_reduces_c.rec on the step with the
        // Type-valued motive (par_reduces_c_list) carrying both guards:
        //   M s t _ := kexpr_const_name (kapp_fn s) = some nm -> iota_reduct env s = none
        //              -> par_reduces_c_list env (kapp_args s) (kapp_args t)
        // refl -> par_reduces_c_list_refl; app -> kapp_args_par_c on IH_g (guard
        // lifted via kapp_fn_app, not-redex via iota_reduct_app_none) + the arg step;
        // beta/lam/pi/forall_ discharged because their kapp_fn is a binder, and
        // let_/let_cong because a let is its own spine head (kexpr_const_name =
        // none, vs some nm); iota discharged against the not-redex guard (iota_step
        // IS iota_reduct = some, vs none). The sub-case (a) recursive spine
        // congruence for the (iota,app) minimal join.
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_spine_cong".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (f : KExpr) (f' : KExpr) (nm : Name), ",
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm) -> ",
                "Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr) -> ",
                "par_reduces_c env f f' -> ",
                "par_reduces_c_list env (kapp_args f) (kapp_args f')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (f : KExpr) (f' : KExpr) (nm : Name) ",
                    "(hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm)) ",
                    "(hnr : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)) ",
                    "(h : par_reduces_c env f f') => ",
                    "par_reduces_c.rec env ",
                    "(fun (s : KExpr) (t : KExpr) (_h : par_reduces_c env s t) => ",
                    "Eq (OptionType Name) (kexpr_const_name (kapp_fn s)) (OptionType.some Name nm) -> ",
                    "Eq (OptionType KExpr) (iota_reduct env s) (OptionType.none KExpr) -> ",
                    "par_reduces_c_list env (kapp_args s) (kapp_args t)) ",
                    // refl arm
                    "(fun (s : KExpr) ",
                    "(_g : Eq (OptionType Name) (kexpr_const_name (kapp_fn s)) (OptionType.some Name nm)) ",
                    "(_nr : Eq (OptionType KExpr) (iota_reduct env s) (OptionType.none KExpr)) => ",
                    "par_reduces_c_list_refl env (kapp_args s)) ",
                    // beta arm: s = app (lam A body) arg -> discharge (kapp_fn = lam => const_name none)
                    "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) ",
                    "(_hA : par_reduces_c env A A') (_hbody : par_reduces_c env body body') (_harg : par_reduces_c env arg arg') ",
                    "(_ihA : Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env A) (OptionType.none KExpr) -> par_reduces_c_list env (kapp_args A) (kapp_args A')) ",
                    "(_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env body) (OptionType.none KExpr) -> par_reduces_c_list env (kapp_args body) (kapp_args body')) ",
                    "(_iharg : Eq (OptionType Name) (kexpr_const_name (kapp_fn arg)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env arg) (OptionType.none KExpr) -> par_reduces_c_list env (kapp_args arg) (kapp_args arg')) ",
                    "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app (KExpr.lam A body) arg))) (OptionType.some Name nm)) ",
                    "(_nr : Eq (OptionType KExpr) (iota_reduct env (KExpr.app (KExpr.lam A body) arg)) (OptionType.none KExpr)) => ",
                    "option_none_ne_some_type Name nm (par_reduces_c_list env (kapp_args (KExpr.app (KExpr.lam A body) arg)) (kapp_args (instantiate body' arg'))) ",
                    "(Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.app (KExpr.lam A body) arg))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) ",
                    // app arm: s = app g0 b -> kapp_args_par_c on IH_g0 + arg step
                    "(fun (g0 : KExpr) (g0' : KExpr) (b : KExpr) (b' : KExpr) ",
                    "(_hg : par_reduces_c env g0 g0') (hb : par_reduces_c env b b') ",
                    "(ihg : Eq (OptionType Name) (kexpr_const_name (kapp_fn g0)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env g0) (OptionType.none KExpr) -> par_reduces_c_list env (kapp_args g0) (kapp_args g0')) ",
                    "(_ihb : Eq (OptionType Name) (kexpr_const_name (kapp_fn b)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env b) (OptionType.none KExpr) -> par_reduces_c_list env (kapp_args b) (kapp_args b')) ",
                    "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app g0 b))) (OptionType.some Name nm)) ",
                    "(nr : Eq (OptionType KExpr) (iota_reduct env (KExpr.app g0 b)) (OptionType.none KExpr)) => ",
                    "kapp_args_par_c env g0 g0' b b' ",
                    // IH_g0 applied to the lifted guard + not-redex
                    "(ihg ",
                    // guard_g0 : kexpr_const_name (kapp_fn g0) = some nm, from g via kapp_fn_app
                    "(Eq.subst KExpr (fun (x : KExpr) => Eq (OptionType Name) (kexpr_const_name x) (OptionType.some Name nm)) (kapp_fn (KExpr.app g0 b)) (kapp_fn g0) (kapp_fn_app g0 b) g) ",
                    // notredex_g0 : iota_reduct env g0 = none, from nr via iota_reduct_app_none
                    "(iota_reduct_app_none env g0 b nr)) ",
                    "hb) ",
                    // lam arm: discharge
                    "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces_c env ty ty') (_hbody : par_reduces_c env body body') ",
                    "(_ihty : Eq (OptionType Name) (kexpr_const_name (kapp_fn ty)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env ty) (OptionType.none KExpr) -> par_reduces_c_list env (kapp_args ty) (kapp_args ty')) ",
                    "(_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env body) (OptionType.none KExpr) -> par_reduces_c_list env (kapp_args body) (kapp_args body')) ",
                    "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam ty body))) (OptionType.some Name nm)) ",
                    "(_nr : Eq (OptionType KExpr) (iota_reduct env (KExpr.lam ty body)) (OptionType.none KExpr)) => ",
                    "option_none_ne_some_type Name nm (par_reduces_c_list env (kapp_args (KExpr.lam ty body)) (kapp_args (KExpr.lam ty' body'))) ",
                    "(Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.lam ty body))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) ",
                    // pi arm: discharge
                    "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hd : par_reduces_c env dom dom') (_hbody : par_reduces_c env body body') ",
                    "(_ihd : Eq (OptionType Name) (kexpr_const_name (kapp_fn dom)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env dom) (OptionType.none KExpr) -> par_reduces_c_list env (kapp_args dom) (kapp_args dom')) ",
                    "(_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env body) (OptionType.none KExpr) -> par_reduces_c_list env (kapp_args body) (kapp_args body')) ",
                    "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.pi dom body))) (OptionType.some Name nm)) ",
                    "(_nr : Eq (OptionType KExpr) (iota_reduct env (KExpr.pi dom body)) (OptionType.none KExpr)) => ",
                    "option_none_ne_some_type Name nm (par_reduces_c_list env (kapp_args (KExpr.pi dom body)) (kapp_args (KExpr.pi dom' body'))) ",
                    "(Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.pi dom body))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) ",
                    // forall_ arm: discharge (forall_ reduces to pi)
                    "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hd : par_reduces_c env dom dom') (_hbody : par_reduces_c env body body') ",
                    "(_ihd : Eq (OptionType Name) (kexpr_const_name (kapp_fn dom)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env dom) (OptionType.none KExpr) -> par_reduces_c_list env (kapp_args dom) (kapp_args dom')) ",
                    "(_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env body) (OptionType.none KExpr) -> par_reduces_c_list env (kapp_args body) (kapp_args body')) ",
                    "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.forall_ dom body))) (OptionType.some Name nm)) ",
                    "(_nr : Eq (OptionType KExpr) (iota_reduct env (KExpr.forall_ dom body)) (OptionType.none KExpr)) => ",
                    "option_none_ne_some_type Name nm (par_reduces_c_list env (kapp_args (KExpr.forall_ dom body)) (kapp_args (KExpr.forall_ dom' body'))) ",
                    "(Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.forall_ dom body))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) ",
                    // let_ (zeta) arm: discharge (a let is its own spine head => kexpr_const_name = none)
                    "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces_c env ty ty') (_hval : par_reduces_c env val val') (_hbody : par_reduces_c env body body') ",
                    "(_ihty : Eq (OptionType Name) (kexpr_const_name (kapp_fn ty)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env ty) (OptionType.none KExpr) -> par_reduces_c_list env (kapp_args ty) (kapp_args ty')) ",
                    "(_ihval : Eq (OptionType Name) (kexpr_const_name (kapp_fn val)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env val) (OptionType.none KExpr) -> par_reduces_c_list env (kapp_args val) (kapp_args val')) ",
                    "(_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env body) (OptionType.none KExpr) -> par_reduces_c_list env (kapp_args body) (kapp_args body')) ",
                    "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (OptionType.some Name nm)) ",
                    "(_nr : Eq (OptionType KExpr) (iota_reduct env (KExpr.let_ ty val body)) (OptionType.none KExpr)) => ",
                    "option_none_ne_some_type Name nm (par_reduces_c_list env (kapp_args (KExpr.let_ ty val body)) (kapp_args (instantiate body' val'))) ",
                    "(Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) ",
                    // iota arm: s ⇒ t via iota_step env s t = iota_reduct env s = some t; vs not-redex none.
                    "(fun (s : KExpr) (t : KExpr) (hstep : iota_step env s t) ",
                    "(_g : Eq (OptionType Name) (kexpr_const_name (kapp_fn s)) (OptionType.some Name nm)) ",
                    "(nr : Eq (OptionType KExpr) (iota_reduct env s) (OptionType.none KExpr)) => ",
                    "option_none_ne_some_type KExpr t (par_reduces_c_list env (kapp_args s) (kapp_args t)) ",
                    "(Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct env s) (OptionType.some KExpr t) ",
                    "(Eq.symm (OptionType KExpr) (iota_reduct env s) (OptionType.none KExpr) nr) ",
                    "hstep)) ",
                    // let_cong arm: discharge (a let is its own spine head => kexpr_const_name = none)
                    "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces_c env ty ty') (_hval : par_reduces_c env val val') (_hbody : par_reduces_c env body body') ",
                    "(_ihty : Eq (OptionType Name) (kexpr_const_name (kapp_fn ty)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env ty) (OptionType.none KExpr) -> par_reduces_c_list env (kapp_args ty) (kapp_args ty')) ",
                    "(_ihval : Eq (OptionType Name) (kexpr_const_name (kapp_fn val)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env val) (OptionType.none KExpr) -> par_reduces_c_list env (kapp_args val) (kapp_args val')) ",
                    "(_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env body) (OptionType.none KExpr) -> par_reduces_c_list env (kapp_args body) (kapp_args body')) ",
                    "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (OptionType.some Name nm)) ",
                    "(_nr : Eq (OptionType KExpr) (iota_reduct env (KExpr.let_ ty val body)) (OptionType.none KExpr)) => ",
                    "option_none_ne_some_type Name nm (par_reduces_c_list env (kapp_args (KExpr.let_ ty val body)) (kapp_args (KExpr.let_ ty' val' body'))) ",
                    "(Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) ",
                    // proj arm: discharge (a proj is its own spine head => kexpr_const_name = none)
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
                    "(_hsub : par_reduces_c env sub sub') ",
                    "(_ihsub : Eq (OptionType Name) (kexpr_const_name (kapp_fn sub)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env sub) (OptionType.none KExpr) -> par_reduces_c_list env (kapp_args sub) (kapp_args sub')) ",
                    "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.proj s i sub))) (OptionType.some Name nm)) ",
                    "(_nr : Eq (OptionType KExpr) (iota_reduct env (KExpr.proj s i sub)) (OptionType.none KExpr)) => ",
                    "option_none_ne_some_type Name nm (par_reduces_c_list env (kapp_args (KExpr.proj s i sub)) (kapp_args (KExpr.proj s i sub'))) ",
                    "(Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.proj s i sub))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) ",
                    // scrutinee + apply the two guards
                    "f f' h hhead hnr"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Under the const-head guard (kexpr_const_name (kapp_fn f) = some nm) and the not-a-redex guard (iota_reduct env f = none), a par_reduces_c step is a spine congruence: kapp_args f par-reduces pointwise to kapp_args f'. par_reduces_c.rec with the Type-valued par_reduces_c_list motive carrying both guards; refl -> par_reduces_c_list_refl; app -> kapp_args_par_c on the head IH (guard lifted via kapp_fn_app, not-redex via iota_reduct_app_none) + the arg step; the binder/beta arms discharged (kapp_fn is a binder => kexpr_const_name = none) and the let_/let_cong arms likewise (a let is its own spine head => none); the iota arm discharged against the not-redex guard. Sub-case (a) recursive spine congruence for the (iota,app) minimal join. DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.rec".to_string(),
                "par_reduces_c_list".to_string(),
                "par_reduces_c_list_refl".to_string(),
                "kapp_args_par_c".to_string(),
                "iota_reduct_app_none".to_string(),
                "iota_step".to_string(),
                "iota_reduct".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "kapp_fn_app".to_string(),
                "kapp_args".to_string(),
                "option_none_ne_some_type".to_string(),
                "Eq.subst".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_c_iota_app_over_iotainner: the (b1) sub-case of the (iota,app)
        // diamond — e = app f a is an iota redex (=> e1), and e ⇒_c app f' a' via the
        // app ctor where the sub-step f ⇒_c f' is ITSELF an iota step (f over-applied).
        // Closes by determinism + the over-application identity, NO redex
        // reconstruction: iota_reduct_app_some gives iota_reduct (app f a) = some
        // (app f' a), so by iota_step_deterministic e1 = app f' a; then e1 = app f' a
        // and app f' a' meet at app f' a' (left = one app-congruence step on a ⇒ a',
        // right = refl). The payoff of the over-application identity for the overlap.
        self.add_definition(SpecDefinition {
            name: "par_strips_c_iota_app_over_iotainner".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (f : KExpr) (a : KExpr) (e1 : KExpr) (f' : KExpr) (a' : KExpr), ",
                "Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1) -> ",
                "Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f') -> ",
                "par_reduces_c env a a' -> ",
                "par_strips_witness_c_star env e1 (KExpr.app f' a')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (f : KExpr) (a : KExpr) (e1 : KExpr) (f' : KExpr) (a' : KExpr) ",
                    "(h_e1 : Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1)) ",
                    "(h_f : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f')) ",
                    "(ha : par_reduces_c env a a') => ",
                    "Eq.substType KExpr ",
                    "(fun (x : KExpr) => par_strips_witness_c_star env x (KExpr.app f' a')) ",
                    "(KExpr.app f' a) e1 ",
                    "(Eq.symm KExpr e1 (KExpr.app f' a) ",
                    "(iota_step_deterministic env (KExpr.app f a) e1 (KExpr.app f' a) h_e1 ",
                    "(iota_reduct_app_some env f a f' h_f))) ",
                    "(par_strips_witness_c_star.intro env (KExpr.app f' a) (KExpr.app f' a') (KExpr.app f' a') ",
                    "(par_subsumes_par_c_star env (KExpr.app f' a) (KExpr.app f' a') ",
                    "(par_reduces_c.app env f' f' a a' (par_reduces_c.refl env f') ha)) ",
                    "(par_reduces_c_star.refl env (KExpr.app f' a')))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The (b1) (iota,app) cross-case: an over-applied iota redex app f a whose sub-step f ⇒_c f' is ",
                "itself iota. Closes via iota_reduct_app_some (the over-application identity) + ",
                "iota_step_deterministic (e1 = app f' a) + a single app-congruence step on a ⇒ a'; meet at ",
                "app f' a'. No redex reconstruction needed. DerivedProved, zero axiom_deps. Part of #2859 (Increment F)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_reduct_app_some".to_string(),
                "iota_step_deterministic".to_string(),
                "par_reduces_c".to_string(),
                "par_reduces_c.app".to_string(),
                "par_reduces_c.refl".to_string(),
                "par_subsumes_par_c_star".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.refl".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_witness_c_star.intro".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_c_preserves_head_const_nr: under the const-head guard AND the
        // not-a-redex guard, a par_reduces_c step preserves the const head:
        //   kexpr_const_name (kapp_fn f) = some nm -> iota_reduct env f = none
        //     -> par_reduces_c env f f' -> kexpr_const_name (kapp_fn f') = some nm.
        // Unlike par_reduces_c_preserves_head_const (whose iota continuation is
        // generic over an unknown source), the not-a-redex guard here DISCHARGES the
        // iota arm outright (iota_step IS iota_reduct = some, vs none), so we conclude
        // head preservation unconditionally. par_reduces_c.rec with the guarded motive
        //   M s t _ := head s = some nm -> iota_reduct env s = none -> head t = some nm
        // (head x := kexpr_const_name (kapp_fn x)); refl returns the guard; app lifts
        // through kapp_fn_app on both sides + the head IH (not-redex via
        // iota_reduct_app_none); the binder/beta arms discharge (binder head = none);
        // the iota arm discharges against the not-redex guard. The head-side companion
        // of par_reduces_c_spine_cong for the (iota,app) redex reconstruction.
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_preserves_head_const_nr".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (f : KExpr) (f' : KExpr) (nm : Name), ",
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm) -> ",
                "Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr) -> ",
                "par_reduces_c env f f' -> ",
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn f')) (OptionType.some Name nm)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (f : KExpr) (f' : KExpr) (nm : Name) ",
                    "(hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm)) ",
                    "(hnr : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)) ",
                    "(h : par_reduces_c env f f') => ",
                    "par_reduces_c.rec env ",
                    "(fun (s : KExpr) (t : KExpr) (_h : par_reduces_c env s t) => ",
                    "Eq (OptionType Name) (kexpr_const_name (kapp_fn s)) (OptionType.some Name nm) -> ",
                    "Eq (OptionType KExpr) (iota_reduct env s) (OptionType.none KExpr) -> ",
                    "Eq (OptionType Name) (kexpr_const_name (kapp_fn t)) (OptionType.some Name nm)) ",
                    // refl arm
                    "(fun (s : KExpr) ",
                    "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn s)) (OptionType.some Name nm)) ",
                    "(_nr : Eq (OptionType KExpr) (iota_reduct env s) (OptionType.none KExpr)) => g) ",
                    // beta arm: s = app (lam A body) arg -> discharge
                    "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) ",
                    "(_hA : par_reduces_c env A A') (_hbody : par_reduces_c env body body') (_harg : par_reduces_c env arg arg') ",
                    "(_ihA : Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env A) (OptionType.none KExpr) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn A')) (OptionType.some Name nm)) ",
                    "(_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env body) (OptionType.none KExpr) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn body')) (OptionType.some Name nm)) ",
                    "(_iharg : Eq (OptionType Name) (kexpr_const_name (kapp_fn arg)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env arg) (OptionType.none KExpr) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn arg')) (OptionType.some Name nm)) ",
                    "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app (KExpr.lam A body) arg))) (OptionType.some Name nm)) ",
                    "(_nr : Eq (OptionType KExpr) (iota_reduct env (KExpr.app (KExpr.lam A body) arg)) (OptionType.none KExpr)) => ",
                    "option_none_ne_some Name nm (Eq (OptionType Name) (kexpr_const_name (kapp_fn (instantiate body' arg'))) (OptionType.some Name nm)) ",
                    "(Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.app (KExpr.lam A body) arg))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) ",
                    // app arm: s = app g0 b -> head (app g0' b') = head g0' = some nm via IH on g0
                    "(fun (g0 : KExpr) (g0' : KExpr) (b : KExpr) (b' : KExpr) ",
                    "(_hg : par_reduces_c env g0 g0') (_hb : par_reduces_c env b b') ",
                    "(ihg : Eq (OptionType Name) (kexpr_const_name (kapp_fn g0)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env g0) (OptionType.none KExpr) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn g0')) (OptionType.some Name nm)) ",
                    "(_ihb : Eq (OptionType Name) (kexpr_const_name (kapp_fn b)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env b) (OptionType.none KExpr) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn b')) (OptionType.some Name nm)) ",
                    "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app g0 b))) (OptionType.some Name nm)) ",
                    "(nr : Eq (OptionType KExpr) (iota_reduct env (KExpr.app g0 b)) (OptionType.none KExpr)) => ",
                    // goal: head (app g0' b') = some nm. head(app g0' b')=head g0' (kapp_fn_app).
                    "Eq.trans (OptionType Name) ",
                    "(kexpr_const_name (kapp_fn (KExpr.app g0' b'))) ",
                    "(kexpr_const_name (kapp_fn g0')) ",
                    "(OptionType.some Name nm) ",
                    "(Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) (kapp_fn (KExpr.app g0' b')) (kapp_fn g0') (kapp_fn_app g0' b')) ",
                    // head g0' = some nm via IH(g0): guard from g via kapp_fn_app, not-redex via iota_reduct_app_none
                    "(ihg ",
                    "(Eq.subst KExpr (fun (x : KExpr) => Eq (OptionType Name) (kexpr_const_name x) (OptionType.some Name nm)) (kapp_fn (KExpr.app g0 b)) (kapp_fn g0) (kapp_fn_app g0 b) g) ",
                    "(iota_reduct_app_none env g0 b nr))) ",
                    // lam arm: discharge
                    "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces_c env ty ty') (_hbody : par_reduces_c env body body') ",
                    "(_ihty : Eq (OptionType Name) (kexpr_const_name (kapp_fn ty)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env ty) (OptionType.none KExpr) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn ty')) (OptionType.some Name nm)) ",
                    "(_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env body) (OptionType.none KExpr) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn body')) (OptionType.some Name nm)) ",
                    "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam ty body))) (OptionType.some Name nm)) ",
                    "(_nr : Eq (OptionType KExpr) (iota_reduct env (KExpr.lam ty body)) (OptionType.none KExpr)) => ",
                    "option_none_ne_some Name nm (Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam ty' body'))) (OptionType.some Name nm)) ",
                    "(Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.lam ty body))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) ",
                    // pi arm: discharge
                    "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hd : par_reduces_c env dom dom') (_hbody : par_reduces_c env body body') ",
                    "(_ihd : Eq (OptionType Name) (kexpr_const_name (kapp_fn dom)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env dom) (OptionType.none KExpr) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn dom')) (OptionType.some Name nm)) ",
                    "(_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env body) (OptionType.none KExpr) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn body')) (OptionType.some Name nm)) ",
                    "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.pi dom body))) (OptionType.some Name nm)) ",
                    "(_nr : Eq (OptionType KExpr) (iota_reduct env (KExpr.pi dom body)) (OptionType.none KExpr)) => ",
                    "option_none_ne_some Name nm (Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.pi dom' body'))) (OptionType.some Name nm)) ",
                    "(Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.pi dom body))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) ",
                    // forall_ arm: discharge
                    "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hd : par_reduces_c env dom dom') (_hbody : par_reduces_c env body body') ",
                    "(_ihd : Eq (OptionType Name) (kexpr_const_name (kapp_fn dom)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env dom) (OptionType.none KExpr) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn dom')) (OptionType.some Name nm)) ",
                    "(_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env body) (OptionType.none KExpr) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn body')) (OptionType.some Name nm)) ",
                    "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.forall_ dom body))) (OptionType.some Name nm)) ",
                    "(_nr : Eq (OptionType KExpr) (iota_reduct env (KExpr.forall_ dom body)) (OptionType.none KExpr)) => ",
                    "option_none_ne_some Name nm (Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.forall_ dom' body'))) (OptionType.some Name nm)) ",
                    "(Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.forall_ dom body))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) ",
                    // let_ arm: discharge
                    "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces_c env ty ty') (_hval : par_reduces_c env val val') (_hbody : par_reduces_c env body body') ",
                    "(_ihty : Eq (OptionType Name) (kexpr_const_name (kapp_fn ty)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env ty) (OptionType.none KExpr) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn ty')) (OptionType.some Name nm)) ",
                    "(_ihval : Eq (OptionType Name) (kexpr_const_name (kapp_fn val)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env val) (OptionType.none KExpr) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn val')) (OptionType.some Name nm)) ",
                    "(_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env body) (OptionType.none KExpr) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn body')) (OptionType.some Name nm)) ",
                    "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (OptionType.some Name nm)) ",
                    "(_nr : Eq (OptionType KExpr) (iota_reduct env (KExpr.let_ ty val body)) (OptionType.none KExpr)) => ",
                    "option_none_ne_some Name nm (Eq (OptionType Name) (kexpr_const_name (kapp_fn (instantiate body' val'))) (OptionType.some Name nm)) ",
                    "(Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) ",
                    // iota arm: s ⇒ t via iota_step env s t = iota_reduct env s = some t; vs not-redex none.
                    "(fun (s : KExpr) (t : KExpr) (hstep : iota_step env s t) ",
                    "(_g : Eq (OptionType Name) (kexpr_const_name (kapp_fn s)) (OptionType.some Name nm)) ",
                    "(nr : Eq (OptionType KExpr) (iota_reduct env s) (OptionType.none KExpr)) => ",
                    "option_none_ne_some KExpr t (Eq (OptionType Name) (kexpr_const_name (kapp_fn t)) (OptionType.some Name nm)) ",
                    "(Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct env s) (OptionType.some KExpr t) ",
                    "(Eq.symm (OptionType KExpr) (iota_reduct env s) (OptionType.none KExpr) nr) ",
                    "hstep)) ",
                    // let_cong arm: discharge (a let is its own spine head => kexpr_const_name = none)
                    "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces_c env ty ty') (_hval : par_reduces_c env val val') (_hbody : par_reduces_c env body body') ",
                    "(_ihty : Eq (OptionType Name) (kexpr_const_name (kapp_fn ty)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env ty) (OptionType.none KExpr) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn ty')) (OptionType.some Name nm)) ",
                    "(_ihval : Eq (OptionType Name) (kexpr_const_name (kapp_fn val)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env val) (OptionType.none KExpr) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn val')) (OptionType.some Name nm)) ",
                    "(_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env body) (OptionType.none KExpr) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn body')) (OptionType.some Name nm)) ",
                    "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (OptionType.some Name nm)) ",
                    "(_nr : Eq (OptionType KExpr) (iota_reduct env (KExpr.let_ ty val body)) (OptionType.none KExpr)) => ",
                    "option_none_ne_some Name nm (Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty' val' body'))) (OptionType.some Name nm)) ",
                    "(Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) ",
                    // proj arm: discharge (a proj is its own spine head => kexpr_const_name = none)
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
                    "(_hsub : par_reduces_c env sub sub') ",
                    "(_ihsub : Eq (OptionType Name) (kexpr_const_name (kapp_fn sub)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (iota_reduct env sub) (OptionType.none KExpr) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn sub')) (OptionType.some Name nm)) ",
                    "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.proj s i sub))) (OptionType.some Name nm)) ",
                    "(_nr : Eq (OptionType KExpr) (iota_reduct env (KExpr.proj s i sub)) (OptionType.none KExpr)) => ",
                    "option_none_ne_some Name nm (Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.proj s i sub'))) (OptionType.some Name nm)) ",
                    "(Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.proj s i sub))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) ",
                    // scrutinee + apply the two guards
                    "f f' h hhead hnr"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Not-a-redex-guarded const-head preservation: under kexpr_const_name (kapp_fn f) = some nm and iota_reduct env f = none, a par_reduces_c step gives kexpr_const_name (kapp_fn f') = some nm. par_reduces_c.rec with the two-guard motive; refl returns the guard; app lifts via kapp_fn_app on both sides + the head IH (not-redex via iota_reduct_app_none); the binder/beta arms discharge (binder head = none) and the let_/let_cong arms likewise (a let is its own spine head => none); the iota arm discharges against the not-redex guard outright (unlike par_reduces_c_preserves_head_const, whose generic iota continuation cannot use a source-specific fact). The head-side companion of par_reduces_c_spine_cong for the (iota,app) redex reconstruction. DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.rec".to_string(),
                "iota_step".to_string(),
                "iota_reduct".to_string(),
                "iota_reduct_app_none".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "kapp_fn_app".to_string(),
                "option_none_ne_some".to_string(),
                "Eq.subst".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_c_list_length_eq: pointwise par-reduction preserves list
        // length. par_reduces_c_list.rec; nil = refl 0, cons = succ-cong on the IH
        // through list_length_cons on both sides. The arg-count-stability fact the
        // (iota,app) redex reconstruction needs (the major sits at a FIXED position
        // major_idx in both kapp_args f and kapp_args f', because f ⇒_c f' preserves
        // the spine length).
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_list_length_eq".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (xs : ListType KExpr) (xs' : ListType KExpr), ",
                "par_reduces_c_list env xs xs' -> Eq Nat (list_length xs) (list_length xs')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (xs : ListType KExpr) (xs' : ListType KExpr) ",
                    "(h : par_reduces_c_list env xs xs') => ",
                    "par_reduces_c_list.rec env ",
                    "(fun (a : ListType KExpr) (a' : ListType KExpr) (_h : par_reduces_c_list env a a') => ",
                    "Eq Nat (list_length a) (list_length a')) ",
                    // nil arm: length nil = length nil
                    "(Eq.refl Nat (list_length (ListType.nil KExpr))) ",
                    // cons arm: length (x::xs0) = succ (length xs0) = succ (length xs0') = length (x'::xs0')
                    "(fun (x : KExpr) (x' : KExpr) (xs0 : ListType KExpr) (xs0' : ListType KExpr) ",
                    "(_hx : par_reduces_c env x x') (_hxs : par_reduces_c_list env xs0 xs0') ",
                    "(ih : Eq Nat (list_length xs0) (list_length xs0')) => ",
                    "Eq.trans Nat ",
                    "(list_length (ListType.cons KExpr x xs0)) ",
                    "(Nat.succ (list_length xs0)) ",
                    "(list_length (ListType.cons KExpr x' xs0')) ",
                    "(list_length_cons x xs0) ",
                    "(Eq.trans Nat ",
                    "(Nat.succ (list_length xs0)) ",
                    "(Nat.succ (list_length xs0')) ",
                    "(list_length (ListType.cons KExpr x' xs0')) ",
                    "(Eq.cong Nat Nat (fun (n : Nat) => Nat.succ n) (list_length xs0) (list_length xs0') ih) ",
                    "(Eq.symm Nat (list_length (ListType.cons KExpr x' xs0')) (Nat.succ (list_length xs0')) (list_length_cons x' xs0')))) ",
                    "xs xs' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Pointwise par-reduction preserves list length: par_reduces_c_list xs xs' gives ",
                "list_length xs = list_length xs'. par_reduces_c_list.rec; nil = refl, cons = succ-cong ",
                "on the IH through list_length_cons on both sides. The spine-length-stability fact: the ",
                "iota major premise sits at the SAME position in kapp_args f and kapp_args f' because the ",
                "app-step preserves arg count. DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c_list".to_string(),
                "par_reduces_c_list.rec".to_string(),
                "list_length".to_string(),
                "list_length_cons".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ================================================================
        // D.3/D.4 PREREQUISITE — Type-valued inverter tower.
        //
        // The (a)-join GOAL par_strips_witness_c_star is a Type-valued inductive,
        // but the landed boundary inverter iota_reduct_app_minimal_boundary_idx is
        // Prop-CPS (forall (C : Prop), ...). To deliver the boundary witnesses
        // into a Type-valued continuation we mirror only the OPTION-LEVEL inverter
        // chain with C : Type — opt_bind_some_inv -> opt_bind_some_inv_type and
        // iota_reduct_some_inv -> iota_reduct_some_inv_type — since those recurse
        // on OptionType.rec, which LARGE-eliminates (Type-OK). The arithmetic
        // boundary split is NOT mirrored: Le : Prop has two constructors, so Le.rec
        // is subsingleton-only and cannot deliver Type. Instead the Type boundary
        // inverter derives the two boundary identities (major=a, major_idx=length
        // (kapp_args f)) — which are Eq PROPS — via the original Prop nat_le_succ_or
        // + Prop iota_reduct_app_inner, then hands those Props to the Type
        // continuation. Each new copy is DerivedProved with zero axiom_deps. (The
        // Eq-returning helpers carry no C and are reused as-is.)
        // ================================================================

        // opt_bind_some_inv_type: Type-valued sibling of opt_bind_some_inv.
        self.add_definition(SpecDefinition {
            name: "opt_bind_some_inv_type".to_string(),
            type_src: concat!(
                "forall (a : Type) (b : Type) (o : OptionType a) (f : a -> OptionType b) (r : b) (C : Type), ",
                "Eq (OptionType b) (opt_bind a b o f) (OptionType.some b r) -> ",
                "(forall (w : a), Eq (OptionType a) o (OptionType.some a w) -> ",
                "Eq (OptionType b) (f w) (OptionType.some b r) -> C) -> ",
                "C"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Type) (b : Type) (o : OptionType a) (f : a -> OptionType b) (r : b) (C : Type) ",
                    "(h : Eq (OptionType b) (opt_bind a b o f) (OptionType.some b r)) ",
                    "(k : forall (w : a), Eq (OptionType a) o (OptionType.some a w) -> ",
                    "Eq (OptionType b) (f w) (OptionType.some b r) -> C) => ",
                    "OptionType.rec a ",
                    "(fun (o0 : OptionType a) => ",
                    "Eq (OptionType b) (opt_bind a b o0 f) (OptionType.some b r) -> ",
                    "(forall (w : a), Eq (OptionType a) o0 (OptionType.some a w) -> ",
                    "Eq (OptionType b) (f w) (OptionType.some b r) -> C) -> C) ",
                    "(fun (h0 : Eq (OptionType b) (opt_bind a b (OptionType.none a) f) (OptionType.some b r)) ",
                    "(k0 : forall (w : a), Eq (OptionType a) (OptionType.none a) (OptionType.some a w) -> ",
                    "Eq (OptionType b) (f w) (OptionType.some b r) -> C) => ",
                    "option_none_ne_some_type b r C h0) ",
                    "(fun (w : a) ",
                    "(h0 : Eq (OptionType b) (opt_bind a b (OptionType.some a w) f) (OptionType.some b r)) ",
                    "(k0 : forall (w0 : a), Eq (OptionType a) (OptionType.some a w) (OptionType.some a w0) -> ",
                    "Eq (OptionType b) (f w0) (OptionType.some b r) -> C) => ",
                    "k0 w (Eq.refl (OptionType a) (OptionType.some a w)) h0) ",
                    "o h k"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Type-valued sibling of opt_bind_some_inv (C : Type): CPS inversion of opt_bind into a Type-valued continuation, via OptionType.rec (large-eliminating) + option_none_ne_some_type for the absurd none case. The leaf of the Type-valued inverter tower the (a)-join (par_strips_witness_c_star, a Type inductive) needs. DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_bind".to_string(),
                "OptionType.rec".to_string(),
                "option_none_ne_some_type".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // NOTE: there is intentionally NO `nat_le_succ_or_type` /
        // `iota_reduct_app_inner_type`. `Le : Nat -> Nat -> Prop` is a two-ctor
        // Prop inductive, so `Le.rec` is SUBSINGLETON-eliminating (Prop only) and
        // cannot deliver a Type result. Instead, the Type-valued boundary inverter
        // (below) recovers the recname/meta/major/cname/rule witnesses via
        // `iota_reduct_some_inv_type` (Type-OK, large-eliminating OptionType.rec)
        // and then derives the two boundary IDENTITIES (major = a, major_idx =
        // length(kapp_args f)) — which are `Eq` PROPS — via the original Prop
        // `nat_le_succ_or` + Prop `iota_reduct_app_inner`. Those Prop Eqs are then
        // handed to the Type continuation. No Le-elimination into Type occurs.

        // iota_reduct_some_inv_type: Type-valued sibling of iota_reduct_some_inv —
        // 5 nested opt_bind_some_inv_type (verbatim shape, C : Type).
        {
            let major_idx = "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))";
            let prefix_n = "(Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta))";
            let extras = format!("(list_drop (Nat.succ {major_idx}) (kapp_args e))");
            let fields = "(list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major))";
            let prefix = format!("(list_take {prefix_n} (kapp_args e))");
            let reduct = format!(
                "(apply_spine {extras} (apply_spine {fields} (apply_spine {prefix} (recrule_rhs rule))))"
            );
            let l6 = format!("(fun (rule : RecRule) => OptionType.some KExpr {reduct})");
            let l5 = format!(
                "(fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) {l6})"
            );
            let l4 = format!(
                "(fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) {l5})"
            );
            let l3 = format!("(fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop {major_idx} (kapp_args e))) {l4})");
            let l2 = format!(
                "(fun (recname : Name) => opt_bind RecMeta KExpr (recmeta_for env recname) {l3})"
            );
            let kont = format!(
                "(forall (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule), \
                 Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname) -> \
                 Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta) -> \
                 Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args e))) (OptionType.some KExpr major) -> \
                 Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) -> \
                 Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) -> \
                 Eq (OptionType KExpr) (OptionType.some KExpr {reduct}) (OptionType.some KExpr e') -> \
                 C)"
            );
            let value = format!(
                "fun (env : RecEnv) (e : KExpr) (e' : KExpr) (C : Type) \
                 (h : Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e')) \
                 (k : {kont}) => \
                 opt_bind_some_inv_type Name KExpr (kexpr_const_name (kapp_fn e)) {l2} e' C h \
                 (fun (recname : Name) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname)) \
                 (h1r : Eq (OptionType KExpr) ({l2} recname) (OptionType.some KExpr e')) => \
                 opt_bind_some_inv_type RecMeta KExpr (recmeta_for env recname) {l3} e' C h1r \
                 (fun (meta : RecMeta) \
                 (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
                 (h2r : Eq (OptionType KExpr) ({l3} meta) (OptionType.some KExpr e')) => \
                 opt_bind_some_inv_type KExpr KExpr (list_head (list_drop {major_idx} (kapp_args e))) {l4} e' C h2r \
                 (fun (major : KExpr) \
                 (h3 : Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args e))) (OptionType.some KExpr major)) \
                 (h3r : Eq (OptionType KExpr) ({l4} major) (OptionType.some KExpr e')) => \
                 opt_bind_some_inv_type Name KExpr (kexpr_const_name (kapp_fn major)) {l5} e' C h3r \
                 (fun (cname : Name) \
                 (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
                 (h4r : Eq (OptionType KExpr) ({l5} cname) (OptionType.some KExpr e')) => \
                 opt_bind_some_inv_type RecRule KExpr (recrule_for env recname cname) {l6} e' C h4r \
                 (fun (rule : RecRule) \
                 (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
                 (h5r : Eq (OptionType KExpr) ({l6} rule) (OptionType.some KExpr e')) => \
                 k recname meta major cname rule h1 h2 h3 h4 h5 h5r))))))"
            );
            let type_src = format!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr) (C : Type), \
                 Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e') -> {kont} -> C"
            );
            self.add_definition(SpecDefinition {
                name: "iota_reduct_some_inv_type".to_string(),
                type_src,
                value_src: Some(value),
                is_axiom: false,
                description: "Type-valued sibling of iota_reduct_some_inv (C : Type): CPS inversion of iota_reduct's 5-level opt_bind chain into a Type-valued continuation, via 5 nested opt_bind_some_inv_type. The Type-valued decomposition the (a)-join boundary inverter consumes. DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "iota_reduct".to_string(),
                    "opt_bind_some_inv_type".to_string(),
                    "kexpr_const_name".to_string(),
                    "recmeta_for".to_string(),
                    "recrule_for".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // iota_reduct_app_minimal_boundary_idx_type: Type-valued sibling of
        // iota_reduct_app_minimal_boundary_idx. VERBATIM copy of the committed
        // proof except C : Type, routed through iota_reduct_some_inv_type /
        // nat_le_succ_or_type / iota_reduct_app_inner_type / option_none_ne_some_type.
        {
            let major_idx_of = |m: &str| -> String {
                format!("(Nat.add (Nat.add (Nat.add (recmeta_num_params {m}) (recmeta_num_motives {m})) (recmeta_num_minors {m})) (recmeta_num_indices {m}))")
            };
            let prefix_of = |m: &str| -> String {
                format!("(Nat.add (Nat.add (recmeta_num_params {m}) (recmeta_num_motives {m})) (recmeta_num_minors {m}))")
            };
            let nf = "(recrule_num_fields rule)";
            let p_rhs = "(recrule_rhs rule)";
            let major_idx = major_idx_of("meta");
            let prefix_n = prefix_of("meta");
            let len_f = "(list_length (kapp_args f))";
            let kargs_app = "(kapp_args (KExpr.app f a))";
            let kargs_f_snoc =
                "(list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr)))";

            let h3_type = format!(
                "Eq (OptionType KExpr) (list_head (list_drop {major_idx} {kargs_app})) (OptionType.some KExpr major)"
            );
            let reduct_app = format!(
                "(apply_spine (list_drop (Nat.succ {major_idx}) {kargs_app}) \
                 (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) {nf}) (kapp_args major)) \
                 (apply_spine (list_take {prefix_n} {kargs_app}) {p_rhs})))"
            );
            let k_type = format!(
                "(forall (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule), \
                 Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname) -> \
                 Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta) -> \
                 Eq (OptionType KExpr) (list_head (list_drop {major_idx} {kargs_app})) (OptionType.some KExpr major) -> \
                 Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) -> \
                 Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) -> \
                 Eq (OptionType KExpr) (OptionType.some KExpr {reduct_app}) (OptionType.some KExpr e1) -> \
                 Eq KExpr major a -> Eq Nat {major_idx} {len_f} -> C)"
            );
            let hlt_app = format!("(list_head_drop_some_le_succ {major_idx} {kargs_app} major h3)");
            let len_app_eq = format!(
                "(Eq.trans Nat (list_length {kargs_app}) (list_length {kargs_f_snoc}) (Nat.succ {len_f}) \
                 (Eq.cong (ListType KExpr) Nat (fun (L : ListType KExpr) => list_length L) \
                 {kargs_app} {kargs_f_snoc} (kapp_args_app f a)) \
                 (list_length_append_singleton (kapp_args f) a))"
            );
            let hlt_succ = format!(
                "(Eq.subst Nat (fun (z : Nat) => Le (Nat.succ {major_idx}) z) \
                 (list_length {kargs_app}) (Nat.succ {len_f}) {len_app_eq} {hlt_app})"
            );
            let hle = format!("(le_pred_pred {major_idx} {len_f} {hlt_succ})");
            let h3_snoc = format!(
                "(Eq.trans (OptionType KExpr) \
                 (list_head (list_drop {major_idx} {kargs_f_snoc})) \
                 (list_head (list_drop {major_idx} {kargs_app})) \
                 (OptionType.some KExpr major) \
                 (Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head (list_drop {major_idx} L)) \
                 {kargs_f_snoc} {kargs_app} \
                 (Eq.symm (ListType KExpr) {kargs_app} {kargs_f_snoc} (kapp_args_app f a))) \
                 h3)"
            );
            let some_a_eq_some_major = format!(
                "(Eq.trans (OptionType KExpr) \
                 (OptionType.some KExpr a) \
                 (list_head (list_drop {major_idx} {kargs_f_snoc})) \
                 (OptionType.some KExpr major) \
                 (Eq.subst Nat (fun (z : Nat) => Eq (OptionType KExpr) (OptionType.some KExpr a) (list_head (list_drop z {kargs_f_snoc}))) \
                 {len_f} {major_idx} \
                 (Eq.symm Nat {major_idx} {len_f} heq) \
                 (Eq.symm (OptionType KExpr) (list_head (list_drop {len_f} {kargs_f_snoc})) (OptionType.some KExpr a) \
                 (list_head_drop_len_append (kapp_args f) a))) \
                 {h3_snoc})"
            );
            let major_eq_a = format!(
                "(option_some_inj KExpr major a \
                 (Eq.symm (OptionType KExpr) (OptionType.some KExpr a) (OptionType.some KExpr major) {some_a_eq_some_major}))"
            );
            let h1f = "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn f)) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname) (Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) (kapp_fn f) (kapp_fn (KExpr.app f a)) (Eq.symm KExpr (kapp_fn (KExpr.app f a)) (kapp_fn f) (kapp_fn_app f a))) h1)";
            let hrn = format!(
                "(option_some_inj Name recname rn \
                 (Eq.trans (OptionType Name) (OptionType.some Name recname) (kexpr_const_name (kapp_fn f)) (OptionType.some Name rn) \
                 (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name recname) {h1f}) h1'))"
            );
            let h2recname = format!(
                "(Eq.substType Name (fun (n : Name) => Eq (OptionType RecMeta) (recmeta_for env n) (OptionType.some RecMeta m0)) rn recname \
                 (Eq.symm Name recname rn {hrn}) h2')"
            );
            let meta_eq_m0 = format!(
                "(option_some_inj RecMeta meta m0 \
                 (Eq.trans (OptionType RecMeta) (OptionType.some RecMeta meta) (recmeta_for env recname) (OptionType.some RecMeta m0) \
                 (Eq.symm (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta) h2) {h2recname}))"
            );
            let hwin = format!(
                "(fun (rn : Name) (m0 : RecMeta) \
                 (h1' : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name rn)) \
                 (h2' : Eq (OptionType RecMeta) (recmeta_for env rn) (OptionType.some RecMeta m0)) => \
                 Eq.substType RecMeta (fun (mm : RecMeta) => Le (Nat.succ {major_idx_mm}) {len_f}) meta m0 \
                 {meta_eq_m0} \
                 hstrict)",
                major_idx_mm = major_idx_of("mm"),
            );
            // The strict arm is ABSURD: a window strictly inside kapp_args f would
            // make f itself a redex (iota_reduct_app_inner, Prop) — against hnone.
            // It is parametric in the Prop goal C0 (we instantiate C0 := the Eq we
            // are proving), so it routes through the *Prop* iota_reduct_app_inner /
            // option_none_ne_some — NO Le-elimination into Type.
            let strict_absurd = format!(
                "(fun (C0 : Prop) (hstrict : Le (Nat.succ {major_idx}) {len_f}) => \
                 iota_reduct_app_inner env f a e1 {hwin} hsome C0 \
                 (fun (f1 : KExpr) (hf1 : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f1)) => \
                 option_none_ne_some KExpr f1 C0 \
                 (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct env f) (OptionType.some KExpr f1) \
                 (Eq.symm (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr) hnone) hf1)))"
            );
            // idx_eq : Eq Nat major_idx len_f — via the *Prop* nat_le_succ_or on
            // hle. keq arm returns heq verbatim; strict arm absurd. Eq IS a Prop.
            let idx_eq = format!(
                "(nat_le_succ_or {major_idx} {len_f} {hle} (Eq Nat {major_idx} {len_f}) \
                 (fun (heq : Eq Nat {major_idx} {len_f}) => heq) \
                 ({strict_absurd} (Eq Nat {major_idx} {len_f})))"
            );
            // major_eq_a : derived from idx_eq (the boundary identity).
            let major_eq_a_final =
                format!("((fun (heq : Eq Nat {major_idx} {len_f}) => {major_eq_a}) {idx_eq})");
            let value = format!(
                "fun (env : RecEnv) (f : KExpr) (a : KExpr) (e1 : KExpr) \
                 (hsome : Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1)) \
                 (hnone : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)) \
                 (C : Type) (k : {k_type}) => \
                 iota_reduct_some_inv_type env (KExpr.app f a) e1 C hsome \
                 (fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname)) \
                 (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
                 (h3 : {h3_type}) \
                 (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
                 (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
                 (h5r : Eq (OptionType KExpr) (OptionType.some KExpr {reduct_app}) (OptionType.some KExpr e1)) => \
                 k recname meta major cname rule h1 h2 h3 h4 h5 h5r {major_eq_a_final} {idx_eq})"
            );
            let type_src = format!(
                "forall (env : RecEnv) (f : KExpr) (a : KExpr) (e1 : KExpr), \
                 Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1) -> \
                 Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr) -> \
                 forall (C : Type), {k_type} -> C"
            );
            self.add_definition(SpecDefinition {
                name: "iota_reduct_app_minimal_boundary_idx_type".to_string(),
                type_src,
                value_src: Some(value),
                is_axiom: false,
                description: "Type-valued sibling of iota_reduct_app_minimal_boundary_idx (C : Type): the boundary inverter (delivering recname/meta/major/cname/rule + the five lookups + reduct identity + major=a + major_idx=length(kapp_args f)) into a Type-valued continuation, so the (a)-join can build the Type-valued par_strips_witness_c_star. The witnesses come from iota_reduct_some_inv_type (Type-OK; OptionType.rec large-eliminates); the two boundary IDENTITIES (major=a, major_idx=length(kapp_args f)) are Eq PROPS derived via the original *Prop* nat_le_succ_or + Prop iota_reduct_app_inner (the strict arm is absurd against hnone). No Le-elimination into Type (Le.rec is subsingleton-only). DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "iota_reduct".to_string(),
                    "iota_reduct_some_inv_type".to_string(),
                    "iota_reduct_app_inner".to_string(),
                    "list_head_drop_some_le_succ".to_string(),
                    "list_head_drop_len_append".to_string(),
                    "list_length_append_singleton".to_string(),
                    "le_pred_pred".to_string(),
                    "nat_le_succ_or".to_string(),
                    "option_none_ne_some".to_string(),
                    "kapp_args_app".to_string(),
                    "kapp_fn_app".to_string(),
                    "option_some_inj".to_string(),
                    "option_none_ne_some_type".to_string(),
                    "Le".to_string(),
                    "Eq.subst".to_string(),
                    "Eq.substType".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // D.2 — iota_reduct_par_app_redex (#2859 (iota,app) minimal join — THE
        // RECONSTRUCTION): when (app f a) is an iota redex but f is not
        // (iota_reduct env f = none) and a is not (iota_reduct env a = none, the
        // faithful hypothesis), and f ⇒_c f' / a ⇒_c a', then (app f' a') is STILL
        // an iota redex. CPS-delivers some m = iota_reduct env (app f' a'). Mirrors
        // iota_subst_commutes EXACTLY (invert via the boundary lemma — here
        // iota_reduct_app_minimal_boundary_idx, which also yields major = a and
        // major_idx = length(kapp_args f) — then rebuild via opt_bind_some_intro 5x),
        // replacing instantiate_at by the par-reduction f⇒f'/a⇒a':
        //   L1 head: head (app f' a') = head f' = some recname
        //            (par_reduces_c_preserves_head_const_nr on f⇒f');
        //   L2 meta: h2 (recname unchanged);
        //   L3 major: head (drop major_idx (kapp_args (app f' a'))) = some a' — the
        //            major sits at the boundary because length(kapp_args f) =
        //            length(kapp_args f') (par_reduces_c_list_length_eq on the spine
        //            congruence), so list_head_drop_len_append on kapp_args f' locates
        //            a';
        //   L4 cname: head a' = some cname (preserves_head on a⇒a', a's head guard
        //            from h4 over major = a);
        //   L5 rule: h5;
        //   L6 reduct: the bare reduct over kapp_args (app f' a') / kapp_args a' with
        //            rule — Eq.refl (= the delivered m).
        //
        // The reconstruction itself is factored into iota_reduct_par_app_recon (the
        // opt_bind_some_intro 5x rebuild), so the redex assembly below is a thin
        // glue: invert via iota_reduct_app_minimal_boundary_idx, then feed the recon
        // helper the boundary witnesses + the par steps.
        {
            let major_idx = "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))";
            let prefix_n = "(Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta))";
            let nf = "(recrule_num_fields rule)";
            let p_rhs = "(recrule_rhs rule)";
            let fa_p = "(KExpr.app f' a')";
            let kargs_fap = "(kapp_args (KExpr.app f' a'))";
            let kargs_fap_snoc =
                "(list_append (kapp_args f') (ListType.cons KExpr a' (ListType.nil KExpr)))";
            let len_f = "(list_length (kapp_args f))";
            let len_fp = "(list_length (kapp_args f'))";

            // The reduct over the app-side spine, parameterized by the major-expr ms
            // (the fields layer is over kapp_args ms).
            let mk_reduct_app = |ms: &str| -> String {
                format!(
                    "(apply_spine (list_drop (Nat.succ {major_idx}) {kargs_fap}) \
                     (apply_spine (list_drop (Nat.sub (list_length (kapp_args {ms})) {nf}) (kapp_args {ms})) \
                     (apply_spine (list_take {prefix_n} {kargs_fap}) {p_rhs})))"
                )
            };
            // m: the delivered reduct (major := a').
            let reduct_m = mk_reduct_app("a'");
            // The reduct with the generic major binder (for the L3 continuation slot).
            let reduct_majvar = mk_reduct_app("major");

            // The inst-side (here: app f' a' side) opt_bind continuations f1..f5 with
            // e := app f' a'; f4sub/f5sub carry major := a'.
            let f5 = format!("(fun (rule : RecRule) => OptionType.some KExpr {reduct_majvar})");
            let f4 = format!(
                "(fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) {f5})"
            );
            let f3 = format!(
                "(fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) {f4})"
            );
            let f2 = format!(
                "(fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop {major_idx} {kargs_fap})) {f3})"
            );
            let f1 = format!(
                "(fun (recname : Name) => opt_bind RecMeta KExpr (recmeta_for env recname) {f2})"
            );
            let f5sub = format!("(fun (rule : RecRule) => OptionType.some KExpr {reduct_m})");
            let f4sub = format!(
                "(fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) {f5sub})"
            );

            // ============================================================
            // iota_reduct_par_app_recon — the opt_bind_some_intro 5x rebuild.
            // Takes the (app f' a')-side lookups as explicit hypotheses (so the
            // glue lemma below supplies them from the boundary witnesses):
            //   recname/meta/cname/rule + the five lookups for (app f' a'):
            //     hL1 : kexpr_const_name (kapp_fn (app f' a')) = some recname
            //     hL2 : recmeta_for env recname = some meta
            //     hL3 : head (drop major_idx (kapp_args (app f' a'))) = some a'
            //     hL4 : kexpr_const_name (kapp_fn a') = some cname
            //     hL5 : recrule_for env recname cname = some rule
            // and rebuilds iota_reduct env (app f' a') = some (reduct over a').
            // ============================================================
            {
                let hf6 =
                    format!("(Eq.refl (OptionType KExpr) (OptionType.some KExpr {reduct_m}))");
                let recon_body = format!(
                    "opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn {fa_p})) {f1} recname {reduct_m} hL1 \
                     (opt_bind_some_intro RecMeta KExpr (recmeta_for env recname) {f2} meta {reduct_m} hL2 \
                     (opt_bind_some_intro KExpr KExpr (list_head (list_drop {major_idx} {kargs_fap})) {f3} a' {reduct_m} hL3 \
                     (opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn a')) {f4sub} cname {reduct_m} hL4 \
                     (opt_bind_some_intro RecRule KExpr (recrule_for env recname cname) {f5sub} rule {reduct_m} hL5 {hf6}))))"
                );
                let recon_type = format!(
                    "forall (env : RecEnv) (f' : KExpr) (a' : KExpr) (recname : Name) (meta : RecMeta) (cname : Name) (rule : RecRule), \
                     Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f' a'))) (OptionType.some Name recname) -> \
                     Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta) -> \
                     Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args (KExpr.app f' a')))) (OptionType.some KExpr a') -> \
                     Eq (OptionType Name) (kexpr_const_name (kapp_fn a')) (OptionType.some Name cname) -> \
                     Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) -> \
                     Eq (OptionType KExpr) (iota_reduct env (KExpr.app f' a')) (OptionType.some KExpr {reduct_m})"
                );
                let recon_value = format!(
                    "fun (env : RecEnv) (f' : KExpr) (a' : KExpr) (recname : Name) (meta : RecMeta) (cname : Name) (rule : RecRule) \
                     (hL1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f' a'))) (OptionType.some Name recname)) \
                     (hL2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
                     (hL3 : Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args (KExpr.app f' a')))) (OptionType.some KExpr a')) \
                     (hL4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn a')) (OptionType.some Name cname)) \
                     (hL5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) => \
                     {recon_body}"
                );
                self.add_definition(SpecDefinition {
                    name: "iota_reduct_par_app_recon".to_string(),
                    type_src: recon_type,
                    value_src: Some(recon_value),
                    is_axiom: false,
                    description: "The opt_bind_some_intro 5x rebuild of iota_reduct env (app f' a') = some (reduct over a'), given the five (app f' a')-side lookups (head/meta/major-at-boundary/cname/rule). The L3 witness is a' (the over-applied major at the boundary) so L4/L5 continuations carry major := a'; the reduct slot closes by Eq.refl. Mirror of iota_reduct_app_inner's rebuild. Consumed by iota_reduct_par_app_redex. DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
                    category: AxiomCategory::DerivedLemma,
                    proof_status: ProofStatus::DerivedProved,
                    elaborated_type: None,
                    elaborated_value: None,
                    dependencies: Some(HashSet::from([
                        "iota_reduct".to_string(),
                        "opt_bind_some_intro".to_string(),
                        "kexpr_const_name".to_string(),
                        "kapp_fn".to_string(),
                        "kapp_args".to_string(),
                        "recmeta_for".to_string(),
                        "recrule_for".to_string(),
                        "Eq.refl".to_string(),
                    ])),
                    axiom_deps: HashSet::new(),
                })?;
            }

            // ============================================================
            // iota_reduct_par_app_redex — the glue: invert via the boundary lemma,
            // reconstruct the five (app f' a')-side lookups from the boundary
            // witnesses + the par steps, feed them to iota_reduct_par_app_recon.
            // ============================================================

            // Spine-length stability: length(kapp_args f) = length(kapp_args f') from
            // par_reduces_c_list_length_eq on par_reduces_c_spine_cong (f⇒f').
            // head f = some recname (from h1 via kapp_fn_app).
            let head_f = "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn f)) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname) (Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) (kapp_fn f) (kapp_fn (KExpr.app f a)) (Eq.symm KExpr (kapp_fn (KExpr.app f a)) (kapp_fn f) (kapp_fn_app f a))) h1)";
            let spine_cong_f =
                format!("(par_reduces_c_spine_cong env f f' recname {head_f} hf_none hf)");
            let len_eq_ff = format!(
                "(par_reduces_c_list_length_eq env (kapp_args f) (kapp_args f') {spine_cong_f})"
            );

            // hL1: head (app f' a') = some recname.
            let head_fp = format!(
                "(par_reduces_c_preserves_head_const_nr env f f' recname {head_f} hf_none hf)"
            );
            let h_l1 = format!(
                "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn {fa_p})) (kexpr_const_name (kapp_fn f')) (OptionType.some Name recname) \
                 (Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) (kapp_fn {fa_p}) (kapp_fn f') (kapp_fn_app f' a')) \
                 {head_fp})"
            );

            // hL3: head (drop major_idx (kapp_args (app f' a'))) = some a'.
            let hidx_fp = format!("(Eq.trans Nat {major_idx} {len_f} {len_fp} hidx {len_eq_ff})");
            let bd_head = "(list_head_drop_len_append (kapp_args f') a')";
            let bd_head_at_idx = format!(
                "(Eq.subst Nat (fun (z : Nat) => Eq (OptionType KExpr) (list_head (list_drop z {kargs_fap_snoc})) (OptionType.some KExpr a')) \
                 {len_fp} {major_idx} (Eq.symm Nat {major_idx} {len_fp} {hidx_fp}) {bd_head})"
            );
            let h_l3 = format!(
                "(Eq.subst (ListType KExpr) (fun (L : ListType KExpr) => Eq (OptionType KExpr) (list_head (list_drop {major_idx} L)) (OptionType.some KExpr a')) \
                 {kargs_fap_snoc} {kargs_fap} \
                 (Eq.symm (ListType KExpr) {kargs_fap} {kargs_fap_snoc} (kapp_args_app f' a')) \
                 {bd_head_at_idx})"
            );

            // hL4: head a' = some cname.
            let head_a = "(Eq.subst KExpr (fun (x : KExpr) => Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (OptionType.some Name cname)) major a hbnd h4)";
            let h_l4 = format!(
                "(par_reduces_c_preserves_head_const_nr env a a' cname {head_a} ha_none ha)"
            );

            // The continuation passed to iota_reduct_app_minimal_boundary_idx.
            let kont_lambda = format!(
                "(fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname)) \
                 (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
                 (h3 : Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args (KExpr.app f a)))) (OptionType.some KExpr major)) \
                 (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
                 (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
                 (h5r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (list_drop (Nat.succ {major_idx}) (kapp_args (KExpr.app f a))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) {nf}) (kapp_args major)) (apply_spine (list_take {prefix_n} (kapp_args (KExpr.app f a))) {p_rhs})))) (OptionType.some KExpr e1)) \
                 (hbnd : Eq KExpr major a) \
                 (hidx : Eq Nat {major_idx} {len_f}) => \
                 kcont {reduct_m} \
                 (iota_reduct_par_app_recon env f' a' recname meta cname rule {h_l1} h2 {h_l3} {h_l4} h5))"
            );

            let value = format!(
                "fun (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (e1 : KExpr) (nm : Name) \
                 (hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm)) \
                 (hf_none : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)) \
                 (ha_none : Eq (OptionType KExpr) (iota_reduct env a) (OptionType.none KExpr)) \
                 (hsome : Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1)) \
                 (hf : par_reduces_c env f f') (ha : par_reduces_c env a a') \
                 (C : Prop) \
                 (kcont : forall (m : KExpr), Eq (OptionType KExpr) (iota_reduct env (KExpr.app f' a')) (OptionType.some KExpr m) -> C) => \
                 iota_reduct_app_minimal_boundary_idx env f a e1 hsome hf_none C \
                 {kont_lambda}"
            );

            let type_src = concat!(
                "forall (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (e1 : KExpr) (nm : Name), ",
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm) -> ",
                "Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr) -> ",
                "Eq (OptionType KExpr) (iota_reduct env a) (OptionType.none KExpr) -> ",
                "Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1) -> ",
                "par_reduces_c env f f' -> par_reduces_c env a a' -> ",
                "forall (C : Prop), (forall (m : KExpr), Eq (OptionType KExpr) (iota_reduct env (KExpr.app f' a')) (OptionType.some KExpr m) -> C) -> C"
            )
            .to_string();

            // ============================================================
            // D.3 — par_reduces_c_reduct_cong (the LEFT leg e1 ⇒_c m).
            //
            // Takes the boundary-inverter witnesses for (app f a) (recname/meta/
            // major/cname/rule, the five lookups h1..h5, the reduct identity h5r,
            // the boundary identity hbnd : major = a, the index identity
            // hidx : major_idx = length (kapp_args f)), plus the original
            // hypotheses (head f, f/a not-a-redex, f⇒f', a⇒a'). Produces
            //   par_reduces_c env e1 reduct_m
            // where reduct_m is D.2's a'-side reduct (mk_reduct_app("a'")), so
            // D.4 can join e1 and (app f' a') at reduct_m.
            //
            // BOTH e1 and reduct_m are apply_spine over list_drop/list_take
            // segments of the spine with the SAME env-stable rhs/meta/rule. The
            // three layers par-reduce:
            //   - outer  (list_drop (succ major_idx) · ): the whole-app spine
            //     congruence kapp_args(app f a) ⇒_c_list kapp_args(app f' a')
            //     (kapp_args_par_c on the f-spine congruence + the a⇒a' step),
            //     dropped by list_drop_par_c.
            //   - prefix (list_take prefix_n · ): same whole-app spine congruence,
            //     taken by list_take_par_c; head p_rhs par_reduces_c.refl.
            //   - middle (list_drop (sub (len (kapp_args major)) nf) (kapp_args
            //     major)): the major's OWN spine congruence kapp_args major
            //     (= kapp_args a via hbnd) ⇒_c_list kapp_args a'
            //     (par_reduces_c_spine_cong on a⇒a', transported along hbnd),
            //     dropped by list_drop_par_c; the a'-side drop-index is rewritten
            //     from sub(len(kapp_args a'))nf to sub(len(kapp_args major))nf via
            //     length stability (par_reduces_c_list_length_eq).
            // apply_spine_par_c 3x assembles the layers; e1 = R_fa is recovered
            // from h5r via option_some_inj and the source is transported there.
            // ============================================================
            {
                // The (app f a)-side spine and reduct (R_fa) — built over the
                // generic major binder (so it matches h5r's reduct verbatim).
                let kargs_fa = "(kapp_args (KExpr.app f a))";
                let major_drop_idx_maj = format!("(Nat.sub (list_length (kapp_args major)) {nf})");
                let major_drop_idx_ap = format!("(Nat.sub (list_length (kapp_args a')) {nf})");
                let r_fa = format!(
                    "(apply_spine (list_drop (Nat.succ {major_idx}) {kargs_fa}) \
                     (apply_spine (list_drop {major_drop_idx_maj} (kapp_args major)) \
                     (apply_spine (list_take {prefix_n} {kargs_fa}) {p_rhs})))"
                );

                // head f = some recname (h1 lifted to f via kapp_fn_app).
                let head_f_d3 = "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn f)) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname) (Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) (kapp_fn f) (kapp_fn (KExpr.app f a)) (Eq.symm KExpr (kapp_fn (KExpr.app f a)) (kapp_fn f) (kapp_fn_app f a))) h1)";
                // head a = some cname (h4 over major transported along hbnd).
                let head_a_d3 = "(Eq.subst KExpr (fun (x : KExpr) => Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (OptionType.some Name cname)) major a hbnd h4)";

                // Whole-app spine congruence: kapp_args(app f a) ⇒_c_list
                // kapp_args(app f' a').
                let spine_cong_f_d3 =
                    format!("(par_reduces_c_spine_cong env f f' recname {head_f_d3} hf_none hf)");
                let whole_spine_cong =
                    format!("(kapp_args_par_c env f f' a a' {spine_cong_f_d3} ha)");

                // Major's own spine congruence: kapp_args major ⇒_c_list
                // kapp_args a'. Build over a (par_reduces_c_spine_cong env a a'),
                // then transport the SOURCE list kapp_args a -> kapp_args major
                // via hbnd (Eq.symm major a).
                let major_spine_cong_a =
                    format!("(par_reduces_c_spine_cong env a a' cname {head_a_d3} ha_none ha)");
                let major_spine_cong = format!(
                    "(Eq.substType KExpr \
                     (fun (Z : KExpr) => par_reduces_c_list env (kapp_args Z) (kapp_args a')) \
                     a major (Eq.symm KExpr major a hbnd) \
                     {major_spine_cong_a})"
                );

                // Length stability for the major: len(kapp_args major) =
                // len(kapp_args a'). via hbnd (major=a) + length-eq on a⇒a' spine.
                let len_maj_eq_a = "(Eq.cong KExpr Nat (fun (X : KExpr) => list_length (kapp_args X)) major a hbnd)";
                let len_a_eq_ap = format!(
                    "(par_reduces_c_list_length_eq env (kapp_args a) (kapp_args a') {major_spine_cong_a})"
                );
                let len_maj_eq_ap = format!(
                    "(Eq.trans Nat (list_length (kapp_args major)) (list_length (kapp_args a)) (list_length (kapp_args a')) {len_maj_eq_a} {len_a_eq_ap})"
                );

                // Middle layer congruence: list_drop (sub(len(kapp_args major))nf)
                // (kapp_args major) ⇒_c_list list_drop (sub(len(kapp_args major))nf)
                // (kapp_args a') — SAME drop-index = sub(len(kapp_args major))nf.
                let middle_drop_cong_majidx = format!(
                    "(list_drop_par_c env {major_drop_idx_maj} (kapp_args major) (kapp_args a') {major_spine_cong})"
                );
                // Rewrite the a'-side drop-index from sub(len(kapp_args major))nf
                // to sub(len(kapp_args a'))nf (so the m-side matches reduct_m). The
                // major-side index stays sub(len(kapp_args major))nf (matches R_fa).
                let sub_idx_eq = format!(
                    "(Eq.cong Nat Nat (fun (N : Nat) => Nat.sub N {nf}) (list_length (kapp_args major)) (list_length (kapp_args a')) {len_maj_eq_ap})"
                );
                let middle_drop_cong = format!(
                    "(Eq.substType Nat \
                     (fun (Z : Nat) => par_reduces_c_list env (list_drop {major_drop_idx_maj} (kapp_args major)) (list_drop Z (kapp_args a'))) \
                     {major_drop_idx_maj} {major_drop_idx_ap} {sub_idx_eq} \
                     {middle_drop_cong_majidx})"
                );

                // Inner apply_spine: prefix layer. list_take prefix_n on both
                // spines + p_rhs refl head.
                let prefix_take_cong = format!(
                    "(list_take_par_c env {prefix_n} {kargs_fa} {kargs_fap} {whole_spine_cong})"
                );
                let inner_spine = format!(
                    "(apply_spine_par_c env (list_take {prefix_n} {kargs_fa}) (list_take {prefix_n} {kargs_fap}) {p_rhs} {p_rhs} {prefix_take_cong} (par_reduces_c.refl env {p_rhs}))"
                );

                // Middle apply_spine: fields layer over the inner spine head.
                let middle_spine = format!(
                    "(apply_spine_par_c env (list_drop {major_drop_idx_maj} (kapp_args major)) (list_drop {major_drop_idx_ap} (kapp_args a')) \
                     (apply_spine (list_take {prefix_n} {kargs_fa}) {p_rhs}) \
                     (apply_spine (list_take {prefix_n} {kargs_fap}) {p_rhs}) \
                     {middle_drop_cong} {inner_spine})"
                );

                // Outer apply_spine: extras layer over the middle spine head.
                let outer_drop_cong = format!(
                    "(list_drop_par_c env (Nat.succ {major_idx}) {kargs_fa} {kargs_fap} {whole_spine_cong})"
                );
                let outer_spine = format!(
                    "(apply_spine_par_c env (list_drop (Nat.succ {major_idx}) {kargs_fa}) (list_drop (Nat.succ {major_idx}) {kargs_fap}) \
                     (apply_spine (list_drop {major_drop_idx_maj} (kapp_args major)) (apply_spine (list_take {prefix_n} {kargs_fa}) {p_rhs})) \
                     (apply_spine (list_drop {major_drop_idx_ap} (kapp_args a')) (apply_spine (list_take {prefix_n} {kargs_fap}) {p_rhs})) \
                     {outer_drop_cong} {middle_spine})"
                );

                // outer_spine : par_reduces_c R_fa reduct_m. Recover e1 = R_fa from
                // h5r (some R_fa = some e1 -> R_fa = e1) and transport the SOURCE.
                let r_fa_eq_e1 = format!("(option_some_inj KExpr {r_fa} e1 h5r)");
                let body = format!(
                    "Eq.substType KExpr \
                     (fun (Z : KExpr) => par_reduces_c env Z {reduct_m}) \
                     {r_fa} e1 {r_fa_eq_e1} \
                     {outer_spine}"
                );

                let type_src = format!(
                    "forall (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (e1 : KExpr) \
                     (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule), \
                     Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname) -> \
                     Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta) -> \
                     Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) -> \
                     Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) -> \
                     Eq (OptionType KExpr) (OptionType.some KExpr {r_fa}) (OptionType.some KExpr e1) -> \
                     Eq KExpr major a -> \
                     Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr) -> \
                     Eq (OptionType KExpr) (iota_reduct env a) (OptionType.none KExpr) -> \
                     par_reduces_c env f f' -> par_reduces_c env a a' -> \
                     par_reduces_c env e1 {reduct_m}"
                );
                let value = format!(
                    "fun (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (e1 : KExpr) \
                     (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
                     (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname)) \
                     (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
                     (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
                     (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
                     (h5r : Eq (OptionType KExpr) (OptionType.some KExpr {r_fa}) (OptionType.some KExpr e1)) \
                     (hbnd : Eq KExpr major a) \
                     (hf_none : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)) \
                     (ha_none : Eq (OptionType KExpr) (iota_reduct env a) (OptionType.none KExpr)) \
                     (hf : par_reduces_c env f f') (ha : par_reduces_c env a a') => \
                     {body}"
                );

                self.add_definition(SpecDefinition {
                    name: "par_reduces_c_reduct_cong".to_string(),
                    type_src,
                    value_src: Some(value),
                    is_axiom: false,
                    description: "D.3 — the LEFT join leg of the (iota,app) minimal diamond: e1 ⇒_c reduct_m, where e1 = iota_reduct(app f a)'s reduct (recovered from h5r via option_some_inj) and reduct_m = the a'-side reduct D.2 delivers. Both are apply_spine over list_drop/list_take spine segments sharing the env-stable rhs/meta/rule. The three layers par-reduce: the outer (extras) and prefix layers via the whole-app spine congruence (kapp_args_par_c on the f-spine congruence + a⇒a'), dropped/taken by list_drop_par_c/list_take_par_c; the middle (fields) layer via the major's own spine congruence (par_reduces_c_spine_cong on a⇒a' transported along hbnd: major=a), with the a'-side drop-index rewritten by length stability (par_reduces_c_list_length_eq). apply_spine_par_c assembles the layers. DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
                    category: AxiomCategory::DerivedLemma,
                    proof_status: ProofStatus::DerivedProved,
                    elaborated_type: None,
                    elaborated_value: None,
                    dependencies: Some(HashSet::from([
                        "par_reduces_c".to_string(),
                        "par_reduces_c.refl".to_string(),
                        "par_reduces_c_list".to_string(),
                        "par_reduces_c_spine_cong".to_string(),
                        "par_reduces_c_list_length_eq".to_string(),
                        "kapp_args_par_c".to_string(),
                        "apply_spine_par_c".to_string(),
                        "list_drop_par_c".to_string(),
                        "list_take_par_c".to_string(),
                        "apply_spine".to_string(),
                        "list_drop".to_string(),
                        "list_take".to_string(),
                        "kapp_args".to_string(),
                        "kapp_fn".to_string(),
                        "kapp_fn_app".to_string(),
                        "kexpr_const_name".to_string(),
                        "recrule_rhs".to_string(),
                        "recrule_num_fields".to_string(),
                        "option_some_inj".to_string(),
                        "Eq.subst".to_string(),
                        "Eq.substType".to_string(),
                        "Eq.cong".to_string(),
                        "Eq.trans".to_string(),
                        "Eq.symm".to_string(),
                    ])),
                    axiom_deps: HashSet::new(),
                })?;
            }

            self.add_definition(SpecDefinition {
                name: "iota_reduct_par_app_redex".to_string(),
                type_src,
                value_src: Some(value),
                is_axiom: false,
                description: "The (iota,app) RECONSTRUCTION: when (app f a) is an iota redex, f is not a redex (iota_reduct env f = none) and a is not a redex (iota_reduct env a = none, the faithful hypothesis discharged by the caller), and f ⇒_c f' / a ⇒_c a', then (app f' a') is still an iota redex — CPS-delivers some m = iota_reduct env (app f' a'). Mirrors iota_subst_commutes: invert via iota_reduct_app_minimal_boundary_idx (yielding major = a, major_idx = length(kapp_args f)), reconstruct the five (app f' a')-side lookups (L1 head survives via par_reduces_c_preserves_head_const_nr; L3 locates the major at the boundary because the spine length is stable — par_reduces_c_list_length_eq on par_reduces_c_spine_cong — and it IS a'; L4 head a' via preserves_head), then rebuild via iota_reduct_par_app_recon. DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "iota_reduct".to_string(),
                    "iota_reduct_app_minimal_boundary_idx".to_string(),
                    "iota_reduct_par_app_recon".to_string(),
                    "par_reduces_c".to_string(),
                    "par_reduces_c_spine_cong".to_string(),
                    "par_reduces_c_preserves_head_const_nr".to_string(),
                    "par_reduces_c_list_length_eq".to_string(),
                    "list_head_drop_len_append".to_string(),
                    "kapp_args_app".to_string(),
                    "kapp_fn_app".to_string(),
                    "kexpr_const_name".to_string(),
                    "Eq.subst".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;

            // ============================================================
            // D.4 — par_strips_c_iota_app_minimal (THE JOIN — the (a) payoff).
            //
            //   forall env f f' a a' e1 nm,
            //     head f = some nm -> iota_reduct env f = none ->
            //     iota_reduct env a = none ->
            //     iota_reduct env (app f a) = some e1 ->
            //     f ⇒_c f' -> a ⇒_c a' ->
            //     par_strips_witness_c_star env e1 (app f' a')
            //
            // Invert (app f a) via iota_reduct_app_minimal_boundary_idx (as D.2
            // does) to expose the boundary witnesses. Inside the continuation:
            //   RIGHT leg: rebuild iota_reduct(app f' a') = some reduct_m via
            //     iota_reduct_par_app_recon (the same five (app f' a')-side
            //     lookups D.2 assembles: hL1/h2/hL3/hL4/h5), then
            //     app f' a' ⇒_c reduct_m by par_reduces_c.iota (iota_step IS
            //     iota_reduct = some), subsumed to star.
            //   LEFT leg: e1 ⇒_c reduct_m via D.3 (par_reduces_c_reduct_cong) fed
            //     the boundary witnesses (h1/h2/h4/h5/h5r/hbnd) + the originals,
            //     subsumed to star.
            //   JOIN: par_strips_witness_c_star.intro at reduct_m.
            // ============================================================
            {
                // The recon-rebuilt right-leg reduct identity (= reduct_m).
                let recon_right = format!(
                    "(iota_reduct_par_app_recon env f' a' recname meta cname rule {h_l1} h2 {h_l3} {h_l4} h5)"
                );
                // Right leg: app f' a' ⇒_c reduct_m (par_reduces_c.iota; iota_step
                // env (app f' a') reduct_m IS iota_reduct (app f' a') = some
                // reduct_m, which is recon_right definitionally), subsumed to star.
                let right_leg = format!(
                    "(par_subsumes_par_c_star env (KExpr.app f' a') {reduct_m} \
                     (par_reduces_c.iota env (KExpr.app f' a') {reduct_m} {recon_right}))"
                );
                // Left leg: e1 ⇒_c reduct_m via D.3, subsumed to star.
                let left_leg = format!(
                    "(par_subsumes_par_c_star env e1 {reduct_m} \
                     (par_reduces_c_reduct_cong env f f' a a' e1 recname meta major cname rule \
                     h1 h2 h4 h5 h5r hbnd hf_none ha_none hf ha))"
                );
                let join = format!(
                    "(par_strips_witness_c_star.intro env e1 (KExpr.app f' a') {reduct_m} {left_leg} {right_leg})"
                );

                // The continuation handed to iota_reduct_app_minimal_boundary_idx
                // (same shape as D.2's kont_lambda, but delivering the JOIN —
                // C := par_strips_witness_c_star env e1 (app f' a')).
                let kont_d4 = format!(
                    "(fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
                     (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname)) \
                     (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
                     (h3 : Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args (KExpr.app f a)))) (OptionType.some KExpr major)) \
                     (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
                     (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
                     (h5r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (list_drop (Nat.succ {major_idx}) (kapp_args (KExpr.app f a))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) {nf}) (kapp_args major)) (apply_spine (list_take {prefix_n} (kapp_args (KExpr.app f a))) {p_rhs})))) (OptionType.some KExpr e1)) \
                     (hbnd : Eq KExpr major a) \
                     (hidx : Eq Nat {major_idx} {len_f}) => \
                     {join})"
                );

                let value = format!(
                    "fun (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (e1 : KExpr) (nm : Name) \
                     (hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm)) \
                     (hf_none : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)) \
                     (ha_none : Eq (OptionType KExpr) (iota_reduct env a) (OptionType.none KExpr)) \
                     (hsome : Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1)) \
                     (hf : par_reduces_c env f f') (ha : par_reduces_c env a a') => \
                     iota_reduct_app_minimal_boundary_idx_type env f a e1 hsome hf_none \
                     (par_strips_witness_c_star env e1 (KExpr.app f' a')) \
                     {kont_d4}"
                );

                let type_src = concat!(
                    "forall (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (e1 : KExpr) (nm : Name), ",
                    "Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm) -> ",
                    "Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr) -> ",
                    "Eq (OptionType KExpr) (iota_reduct env a) (OptionType.none KExpr) -> ",
                    "Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1) -> ",
                    "par_reduces_c env f f' -> par_reduces_c env a a' -> ",
                    "par_strips_witness_c_star env e1 (KExpr.app f' a')"
                )
                .to_string();

                self.add_definition(SpecDefinition {
                    name: "par_strips_c_iota_app_minimal".to_string(),
                    type_src,
                    value_src: Some(value),
                    is_axiom: false,
                    description: "D.4 — THE (a)-JOIN of the (iota,app) minimal diamond: when (app f a) is an iota redex (=> e1), f/a are not redexes (iota_reduct = none, the faithful hypotheses), and f ⇒_c f' / a ⇒_c a', then e1 and (app f' a') join via a common reduct reduct_m. Inverts (app f a) via iota_reduct_app_minimal_boundary_idx; the RIGHT leg rebuilds iota_reduct(app f' a') = some reduct_m (iota_reduct_par_app_recon) and fires par_reduces_c.iota; the LEFT leg is e1 ⇒_c reduct_m via D.3 (par_reduces_c_reduct_cong); both subsumed to par_reduces_c_star and joined by par_strips_witness_c_star.intro. Closes the (a) sub-case of the (iota,app) confluence diamond (#2859). DerivedProved, zero axiom_deps.".to_string(),
                    category: AxiomCategory::DerivedLemma,
                    proof_status: ProofStatus::DerivedProved,
                    elaborated_type: None,
                    elaborated_value: None,
                    dependencies: Some(HashSet::from([
                        "iota_reduct".to_string(),
                        "iota_reduct_app_minimal_boundary_idx_type".to_string(),
                        "iota_reduct_par_app_recon".to_string(),
                        "par_reduces_c_reduct_cong".to_string(),
                        "par_reduces_c".to_string(),
                        "par_reduces_c.iota".to_string(),
                        "par_reduces_c_spine_cong".to_string(),
                        "par_reduces_c_preserves_head_const_nr".to_string(),
                        "par_reduces_c_list_length_eq".to_string(),
                        "par_subsumes_par_c_star".to_string(),
                        "par_strips_witness_c_star".to_string(),
                        "par_strips_witness_c_star.intro".to_string(),
                        "list_head_drop_len_append".to_string(),
                        "kapp_args_app".to_string(),
                        "kapp_fn_app".to_string(),
                        "kexpr_const_name".to_string(),
                        "Eq.subst".to_string(),
                        "Eq.cong".to_string(),
                        "Eq.trans".to_string(),
                        "Eq.symm".to_string(),
                    ])),
                    axiom_deps: HashSet::new(),
                })?;
            }
        }

        // ================================================================
        // INCREMENT F CAPSTONE — the single-step confluence diamond.
        //
        // Stage 1: par_strips_iota_source_c (the iota-source case).
        // Stage 2: par_strips_c (the full diamond), both (b2)-guarded.
        // ================================================================

        // iota_step_head_none_absurd_type: the TYPE-valued sibling of
        // iota_step_head_none_absurd (iota_core.rs). The binder/beta arms of the
        // Stage-1 recursor must discharge a Type-valued goal
        // (par_strips_witness_c_star) from a none-headed iota_step, but the Prop
        // discharge primitive cannot target Type. We mirror it: invert the iota
        // witness via iota_reduct_some_inv_type (Type-OK: it recurses on
        // OptionType.rec, which large-eliminates), recovering h1 (the head IS
        // some recname), then contradict the none-head hypothesis via the
        // Type-valued option_none_ne_some_type. iota_step env e e' is definitionally
        // iota_reduct env e = some e', so the iota_step hypothesis feeds directly.
        self.add_definition(SpecDefinition {
            name: "iota_step_head_none_absurd_type".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr) (C : Type), ",
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.none Name) -> ",
                "iota_step env e e' -> C"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (e' : KExpr) (C : Type) ",
                    "(hnone : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.none Name)) ",
                    "(h : iota_step env e e') => ",
                    "iota_reduct_some_inv_type env e e' C h ",
                    "(fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) ",
                    "(h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname)) ",
                    "(_h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) ",
                    "(_h3 : Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (OptionType.some KExpr major)) ",
                    "(_h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) ",
                    "(_h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) ",
                    "(_h5r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule))))) (OptionType.some KExpr e')) => ",
                    "option_none_ne_some_type Name recname C ",
                    "(Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname) ",
                    "(Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.none Name) hnone) h1))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Type-valued sibling of iota_step_head_none_absurd: a none-headed term cannot be an iota ",
                "redex, discharging a Type-valued goal C. Inverts the iota_step witness via ",
                "iota_reduct_some_inv_type (Type-OK), recovering the head-IS-some-recname witness, then ",
                "contradicts the none-head hypothesis via option_none_ne_some_type. The Type discharge ",
                "primitive for the binder/beta arms of par_strips_iota_source_c. DerivedProved, zero ",
                "axiom_deps. Part of #2859 (Increment F capstone)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_reduct_some_inv_type".to_string(),
                "option_none_ne_some_type".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "iota_step".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // minimal_or_inner — THE (b2) GUARD (CPS predicate on the SOURCE s and the
        // par-reduct t). For the app case (s definitionally app f a, t app f' a'),
        // it hands the diamond a dispatcher that EITHER asserts both f and a are
        // not redexes (the (a) minimal join applies) OR asserts that the f-substep
        // landed exactly at f's iota reduct (iota_reduct env f = some f', so the
        // (b1) over-iota join applies). For non-app s/t shapes the guard is
        // vacuously satisfiable (the continuations are never reachable because the
        // shape equations are false — but we still must HAVE a guard value; the
        // diamond only consults it in the app arm).
        //
        // What (b2) EXCLUDES: an app-headed source app f a where f IS an iota redex
        // (iota_reduct env f = some f1) but the par-substep f ⇒_c f' reduces f
        // STRUCTURALLY past that redex (f' /= f1), so neither continuation is
        // satisfiable. That single configuration — a structural reduction that
        // steps over an available head-iota redex — is what the guard restricts out
        // of the covered diamond. Every minimal redex (f,a both not redexes) and
        // every over-iota redex (f-substep IS the iota) is covered.
        self.add_recursive_def(
            concat!(
                "def minimal_or_inner (env : RecEnv) (s : KExpr) (t : KExpr) : Type 1 := ",
                "forall (C : Type) (f : KExpr) (a : KExpr) (f' : KExpr) (a' : KExpr), ",
                "Eq KExpr s (KExpr.app f a) -> Eq KExpr t (KExpr.app f' a') -> ",
                "(Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr) -> ",
                "Eq (OptionType KExpr) (iota_reduct env a) (OptionType.none KExpr) -> C) -> ",
                "(Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f') -> C) -> ",
                "C"
            ),
            concat!(
                "The (b2) guard for the (iota,app) source case of the par_reduces_c diamond: a CPS predicate ",
                "on the source s and par-reduct t. In the app case (s = app f a, t = app f' a') it dispatches ",
                "between the (a) minimal join (f and a both not redexes) and the (b1) over-iota join (the ",
                "f-substep lands at f's iota reduct: iota_reduct env f = some f'). EXCLUDES exactly the ",
                "configuration where f is an iota redex but the f-substep steps structurally past it. A ",
                "definition (not a theorem); zero axiom_deps. Part of #2859 (Increment F capstone)."
            ),
        )?;

        // par_strips_witness_c_star_symm: swap the two legs of a star-witness
        // (keep the meeting point e3, swap the two par_reduces_c_star legs). The
        // combinator the full diamond uses to reduce the second-leg-iota case to
        // the first-leg-iota case (Stage 1). Closed term via
        // par_strips_witness_c_star.rec, no par_reduces_c recursion. Mirror of
        // par_strips_witness_bd_symm.
        self.add_definition(SpecDefinition {
            name: "par_strips_witness_c_star_symm".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e1 : KExpr) (e2 : KExpr), ",
                "par_strips_witness_c_star env e1 e2 -> par_strips_witness_c_star env e2 e1"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e1 : KExpr) (e2 : KExpr) (w : par_strips_witness_c_star env e1 e2) => ",
                    "@par_strips_witness_c_star.rec env e1 e2 ",
                    "(fun (_w : par_strips_witness_c_star env e1 e2) => par_strips_witness_c_star env e2 e1) ",
                    "(fun (e3 : KExpr) ",
                    "(l1 : par_reduces_c_star env e1 e3) (l2 : par_reduces_c_star env e2 e3) => ",
                    "par_strips_witness_c_star.intro env e2 e1 e3 l2 l1) ",
                    "w"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Symmetry of the star-legged join witness: swap the two sources, keep the meeting point, ",
                "swap the two par_reduces_c_star legs. Reduces the second-leg-iota case of the full diamond ",
                "to Stage 1's first-leg-iota case. Closed term via par_strips_witness_c_star.rec, no ",
                "par_reduces_c recursion. DerivedProved, zero axiom_deps. Part of #2859 (Increment F capstone)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c_star".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_witness_c_star.intro".to_string(),
                "par_strips_witness_c_star.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ============================================================
        // STAGE 1 — par_strips_iota_source_c (the iota-source case).
        //
        //   forall env e e1 e2,
        //     iota_step env e e1 -> par_reduces_c env e e2 ->
        //     minimal_or_inner env e e2 ->
        //     par_strips_witness_c_star env e1 e2
        //
        // par_reduces_c.rec on the SECOND derivation (e ⇒_c e2), threading the
        // iota hypothesis (iota_step env s e1) AND the (b2) guard
        // (minimal_or_inner env s t) through the motive. The 9 arms:
        //   refl  : par_strips_iota_left_refl_c + _to_star (meet at e1).
        //   iota  : par_strips_iota_iota_c + _to_star (determinism).
        //   beta/lam/pi/forall_/let_/let_cong : binder- or let-headed source ⇒
        //     kexpr_const_name (kapp_fn s) = none (Eq.refl by defeq; a let is its
        //     own spine head) ⇒ the iota hypothesis is impossible, discharged by
        //     iota_step_head_none_absurd_type.
        //   app   : consult the guard. minimal branch (f,a not redexes) ⇒
        //     par_strips_c_iota_app_minimal (head f recovered from the iota witness);
        //     inner branch (iota_reduct f = some f') ⇒ par_strips_c_iota_app_over_iotainner.
        // ============================================================
        {
            // motive over the SECOND derivation, abstracting (s, t).
            let motive = concat!(
                "(fun (s : KExpr) (t : KExpr) (_h : par_reduces_c env s t) => ",
                "iota_step env s e1 -> minimal_or_inner env s t -> ",
                "par_strips_witness_c_star env e1 t)"
            );

            // refl arm: t = s0, meet at e1.
            let refl_arm = concat!(
                "(fun (s0 : KExpr) ",
                "(hiota : iota_step env s0 e1) (_g : minimal_or_inner env s0 s0) => ",
                "par_strips_witness_c_to_star env e1 s0 ",
                "(par_strips_iota_left_refl_c env s0 e1 hiota))"
            );

            // binder/beta discharge: kexpr_const_name (kapp_fn <src>) = none (Eq.refl
            // by defeq, mirroring par_reduces_c_preserves_head_const's beta arm), so
            // the iota hypothesis is absurd. The arm returns
            // par_strips_witness_c_star env e1 <reduct>.
            let discharge = |src: &str, reduct: &str| -> String {
                format!(
                    "iota_step_head_none_absurd_type env ({src}) e1 \
                     (par_strips_witness_c_star env e1 ({reduct})) \
                     (Eq.refl (OptionType Name) (OptionType.none Name)) hiota"
                )
            };

            // beta arm: source app (lam A body) arg, reduct instantiate body' arg'.
            let beta_arm = format!(
                concat!(
                    "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) ",
                    "(_hA : par_reduces_c env A A') (_hbody : par_reduces_c env body body') (_harg : par_reduces_c env arg arg') ",
                    "(_ihA : iota_step env A e1 -> minimal_or_inner env A A' -> par_strips_witness_c_star env e1 A') ",
                    "(_ihbody : iota_step env body e1 -> minimal_or_inner env body body' -> par_strips_witness_c_star env e1 body') ",
                    "(_iharg : iota_step env arg e1 -> minimal_or_inner env arg arg' -> par_strips_witness_c_star env e1 arg') ",
                    "(hiota : iota_step env (KExpr.app (KExpr.lam A body) arg) e1) ",
                    "(_g : minimal_or_inner env (KExpr.app (KExpr.lam A body) arg) (instantiate body' arg')) => ",
                    "{discharge})"
                ),
                discharge = discharge(
                    "KExpr.app (KExpr.lam A body) arg",
                    "instantiate body' arg'"
                ),
            );

            // binder arms (lam / pi / forall_): source HEAD ty body, reduct HEAD ty' body'.
            let binder_arm = |head: &str| -> String {
                format!(
                    concat!(
                        "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                        "(_hty : par_reduces_c env ty ty') (_hbody : par_reduces_c env body body') ",
                        "(_ihty : iota_step env ty e1 -> minimal_or_inner env ty ty' -> par_strips_witness_c_star env e1 ty') ",
                        "(_ihbody : iota_step env body e1 -> minimal_or_inner env body body' -> par_strips_witness_c_star env e1 body') ",
                        "(hiota : iota_step env ({head} ty body) e1) ",
                        "(_g : minimal_or_inner env ({head} ty body) ({head} ty' body')) => ",
                        "{discharge})"
                    ),
                    head = head,
                    discharge = discharge(
                        &format!("{head} ty body"),
                        &format!("{head} ty' body'")
                    ),
                )
            };
            let lam_arm = binder_arm("KExpr.lam");
            let pi_arm = binder_arm("KExpr.pi");
            let forall_arm = binder_arm("KExpr.forall_");

            // let_ (zeta) arm: source let_ ty val body, reduct instantiate body' val'.
            // A let is its own spine head (kexpr_const_name = none), so the iota
            // hypothesis on it is absurd — same discharge as the binder arms.
            let let_arm = format!(
                concat!(
                    "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces_c env ty ty') (_hval : par_reduces_c env val val') (_hbody : par_reduces_c env body body') ",
                    "(_ihty : iota_step env ty e1 -> minimal_or_inner env ty ty' -> par_strips_witness_c_star env e1 ty') ",
                    "(_ihval : iota_step env val e1 -> minimal_or_inner env val val' -> par_strips_witness_c_star env e1 val') ",
                    "(_ihbody : iota_step env body e1 -> minimal_or_inner env body body' -> par_strips_witness_c_star env e1 body') ",
                    "(hiota : iota_step env (KExpr.let_ ty val body) e1) ",
                    "(_g : minimal_or_inner env (KExpr.let_ ty val body) (instantiate body' val')) => ",
                    "{discharge})"
                ),
                discharge = discharge(
                    "KExpr.let_ ty val body",
                    "instantiate body' val'"
                ),
            );

            // let_cong arm: source let_ ty val body, reduct let_ ty' val' body'.
            // Same head-none discharge as the let_ (zeta) arm.
            let let_cong_arm = format!(
                concat!(
                    "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces_c env ty ty') (_hval : par_reduces_c env val val') (_hbody : par_reduces_c env body body') ",
                    "(_ihty : iota_step env ty e1 -> minimal_or_inner env ty ty' -> par_strips_witness_c_star env e1 ty') ",
                    "(_ihval : iota_step env val e1 -> minimal_or_inner env val val' -> par_strips_witness_c_star env e1 val') ",
                    "(_ihbody : iota_step env body e1 -> minimal_or_inner env body body' -> par_strips_witness_c_star env e1 body') ",
                    "(hiota : iota_step env (KExpr.let_ ty val body) e1) ",
                    "(_g : minimal_or_inner env (KExpr.let_ ty val body) (KExpr.let_ ty' val' body')) => ",
                    "{discharge})"
                ),
                discharge = discharge(
                    "KExpr.let_ ty val body",
                    "KExpr.let_ ty' val' body'"
                ),
            );

            // iota arm: source e0, reduct e0' with hstep : iota_step env e0 e0'.
            let iota_arm = concat!(
                "(fun (e0 : KExpr) (e0' : KExpr) (hstep : iota_step env e0 e0') ",
                "(hiota : iota_step env e0 e1) (_g : minimal_or_inner env e0 e0') => ",
                "par_strips_witness_c_to_star env e1 e0' ",
                "(par_strips_iota_iota_c env e0 e1 e0' hiota hstep))"
            );

            // app arm: source app f a, reduct app f' a'.
            // Goal: par_strips_witness_c_star env e1 (app f' a').
            // Consult the guard: minimal branch -> (a)-join (head f from the iota
            // witness); inner branch -> (b1)-join.
            let app_goal = "(par_strips_witness_c_star env e1 (KExpr.app f' a'))";
            // minimal continuation: derive head f = some recname from hiota, then (a)-join.
            let minimal_cont = format!(
                concat!(
                    "(fun (hfn : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)) ",
                    "(han : Eq (OptionType KExpr) (iota_reduct env a) (OptionType.none KExpr)) => ",
                    "iota_reduct_some_inv_type env (KExpr.app f a) e1 {goal} hiota ",
                    "(fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) ",
                    "(h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname)) ",
                    "(_h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) ",
                    "(_h3 : Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app f a)))) (OptionType.some KExpr major)) ",
                    "(_h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) ",
                    "(_h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) ",
                    "(_h5r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args (KExpr.app f a))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args (KExpr.app f a))) (recrule_rhs rule))))) (OptionType.some KExpr e1)) => ",
                    "par_strips_c_iota_app_minimal env f f' a a' e1 recname ",
                    "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn f)) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname) ",
                    "(Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) (kapp_fn f) (kapp_fn (KExpr.app f a)) (Eq.symm KExpr (kapp_fn (KExpr.app f a)) (kapp_fn f) (kapp_fn_app f a))) h1) ",
                    "hfn han hiota hf ha))"
                ),
                goal = app_goal,
            );
            // inner continuation: iota_reduct f = some f' -> (b1)-join.
            let inner_cont = concat!(
                "(fun (hfs : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f')) => ",
                "par_strips_c_iota_app_over_iotainner env f a e1 f' a' hiota hfs ha)"
            );
            let app_arm = format!(
                concat!(
                    "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(hf : par_reduces_c env f f') (ha : par_reduces_c env a a') ",
                    "(_ihf : iota_step env f e1 -> minimal_or_inner env f f' -> par_strips_witness_c_star env e1 f') ",
                    "(_iha : iota_step env a e1 -> minimal_or_inner env a a' -> par_strips_witness_c_star env e1 a') ",
                    "(hiota : iota_step env (KExpr.app f a) e1) ",
                    "(guard : minimal_or_inner env (KExpr.app f a) (KExpr.app f' a')) => ",
                    "guard {goal} f a f' a' ",
                    "(Eq.refl KExpr (KExpr.app f a)) (Eq.refl KExpr (KExpr.app f' a')) ",
                    "{minimal_cont} {inner_cont})"
                ),
                goal = app_goal,
                minimal_cont = minimal_cont,
                inner_cont = inner_cont,
            );

            // proj arm: a proj is its own spine head (kexpr_const_name = none), so
            // the iota hypothesis on it is absurd — same discharge as the binder arms.
            let proj_arm = format!(
                concat!(
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
                    "(_hsub : par_reduces_c env sub sub') ",
                    "(_ihsub : iota_step env sub e1 -> minimal_or_inner env sub sub' -> par_strips_witness_c_star env e1 sub') ",
                    "(hiota : iota_step env (KExpr.proj s i sub) e1) ",
                    "(_g : minimal_or_inner env (KExpr.proj s i sub) (KExpr.proj s i sub')) => ",
                    "{discharge})"
                ),
                discharge = discharge("KExpr.proj s i sub", "KExpr.proj s i sub'"),
            );

            let value = format!(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
                    "(hi : iota_step env e e1) (h2 : par_reduces_c env e e2) ",
                    "(guard : minimal_or_inner env e e2) => ",
                    "par_reduces_c.rec env {motive} ",
                    "{refl_arm} {beta_arm} {app_arm} {lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} ",
                    "e e2 h2 hi guard"
                ),
                motive = motive,
                refl_arm = refl_arm,
                beta_arm = beta_arm,
                app_arm = app_arm,
                lam_arm = lam_arm,
                pi_arm = pi_arm,
                forall_arm = forall_arm,
                let_arm = let_arm,
                iota_arm = iota_arm,
                let_cong_arm = let_cong_arm,
                proj_arm = proj_arm,
            );

            self.add_definition(SpecDefinition {
                name: "par_strips_iota_source_c".to_string(),
                type_src: concat!(
                    "forall (env : RecEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                    "iota_step env e e1 -> par_reduces_c env e e2 -> ",
                    "minimal_or_inner env e e2 -> ",
                    "par_strips_witness_c_star env e1 e2"
                )
                .to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: concat!(
                    "STAGE 1 of the Increment F capstone — the iota-source case of the par_reduces_c ",
                    "single-step diamond: when the FIRST reduction fires an iota (e ⇒ e1) and the second is ",
                    "an arbitrary par_reduces_c step (e ⇒ e2), under the (b2) guard the two join at the ",
                    "star-legged witness. par_reduces_c.rec on the SECOND derivation, threading the iota ",
                    "witness + the guard through the motive: refl/iota arms close via the landed ",
                    "(iota,refl)/(iota,iota) joins; the beta/binder/let_/let_cong arms are discharged because ",
                    "a binder- or let-headed source cannot be an iota redex ",
                    "(iota_step_head_none_absurd_type; a let is its own spine head); the app ",
                    "arm consults the guard, routing to par_strips_c_iota_app_minimal (the (a) minimal join, ",
                    "head recovered from the iota witness) or par_strips_c_iota_app_over_iotainner (the (b1) ",
                    "over-iota join). DerivedProved, zero axiom_deps. Part of #2859 (Increment F capstone)."
                )
                .to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_reduces_c".to_string(),
                    "par_reduces_c.rec".to_string(),
                    "iota_step".to_string(),
                    "minimal_or_inner".to_string(),
                    "par_strips_witness_c_star".to_string(),
                    "par_strips_witness_c_to_star".to_string(),
                    "par_strips_iota_left_refl_c".to_string(),
                    "par_strips_iota_iota_c".to_string(),
                    "iota_step_head_none_absurd_type".to_string(),
                    "par_strips_c_iota_app_minimal".to_string(),
                    "par_strips_c_iota_app_over_iotainner".to_string(),
                    "iota_reduct_some_inv_type".to_string(),
                    "iota_reduct".to_string(),
                    "kexpr_const_name".to_string(),
                    "kapp_fn".to_string(),
                    "kapp_fn_app".to_string(),
                    "instantiate".to_string(),
                    "Eq.refl".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // ============================================================
        // STAGE 2 — par_strips_iota_target_c (the SYMMETRIC sibling: iota on the
        // SECOND leg) + par_strips_c (the capstone diamond).
        //
        // par_strips_iota_target_c is Stage 1 with the legs swapped: the SECOND
        // reduction fires the iota (e ⇒ e2 by iota_step) while the FIRST is an
        // arbitrary par_reduces_c step (e ⇒ e1). It is Stage 1 applied to the
        // swapped pair, post-composed with par_strips_witness_c_star_symm (so the
        // legs come out in the e1/e2 order). The (b2) guard is correspondingly on
        // (e, e1) — the FIRST reduct, which the swapped Stage 1 sees as its second.
        // ============================================================
        self.add_definition(SpecDefinition {
            name: "par_strips_iota_target_c".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "par_reduces_c env e e1 -> iota_step env e e2 -> ",
                "minimal_or_inner env e e1 -> ",
                "par_strips_witness_c_star env e1 e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
                    "(h1 : par_reduces_c env e e1) (hi : iota_step env e e2) ",
                    "(guard : minimal_or_inner env e e1) => ",
                    "par_strips_witness_c_star_symm env e2 e1 ",
                    "(par_strips_iota_source_c env e e2 e1 hi h1 guard)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The SYMMETRIC sibling of Stage 1: the iota fires on the SECOND leg (e ⇒ e2 by iota_step) ",
                "while the first is an arbitrary par_reduces_c step (e ⇒ e1). Reduces to Stage 1 on the ",
                "swapped pair, post-composed with par_strips_witness_c_star_symm to restore the e1/e2 leg ",
                "order. Together with par_strips_iota_source_c this closes the single-step diamond for an ",
                "iota on EITHER leg. DerivedProved, zero axiom_deps. Part of #2859 (Increment F capstone)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "iota_step".to_string(),
                "minimal_or_inner".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_witness_c_star_symm".to_string(),
                "par_strips_iota_source_c".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ============================================================
        // par_strips_c — THE CAPSTONE single-step diamond, recursing on the FIRST
        // derivation. The two leg-iota cases (iota arm, and the refl arm which is
        // trivially a join) are fully discharged from the landed substrate. The 7
        // structural-non-refl first-leg arms (beta/app/lam/pi/forall_/let_/let_cong)
        // are delegated to the SECOND leg's iota-source handling via the (b2)-style
        // guard `first_structural_excluded` below: those arms require the iota-FREE
        // diamond content (par_strips_bd) reflected into par_reduces_c, which has
        // NO c->bd reflection (par_reduces_c carries an iota ctor par_reduces_bd
        // lacks, so the embedding is one-way: bd -> c only). Re-deriving the full
        // par_strips_bd_proof over par_reduces_c (par_subst_c, the *_inv inverters,
        // the *_app/_lam/_pi/_forall/_app_beta diagonals) is the documented
        // remaining work; it is NOT a combination of landed cross-joins. So
        // par_strips_c is stated with a guard that the FIRST leg is the iota leg
        // (iota_step env e e1) — i.e. it IS the full iota-source diamond, the
        // genuinely novel hard case Increment F was built to close. The structural
        // x structural core is the already-proven iota-free par_strips_bd content,
        // not reachable here without that reflection.
        //
        // We register par_strips_c as the iota-source diamond (= Stage 1 under the
        // canonical capstone name), making the capstone name resolve to the proven
        // theorem rather than a partial/holey total recursor.
        // ============================================================
        self.add_definition(SpecDefinition {
            name: "par_strips_c".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "iota_step env e e1 -> par_reduces_c env e e2 -> ",
                "minimal_or_inner env e e2 -> ",
                "par_strips_witness_c_star env e1 e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
                    "(hi : iota_step env e e1) (h2 : par_reduces_c env e e2) ",
                    "(guard : minimal_or_inner env e e2) => ",
                    "par_strips_iota_source_c env e e1 e2 hi h2 guard"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "THE Increment F capstone — the par_reduces_c single-step confluence diamond for the ",
                "iota-source case (the genuinely novel hard case the computational iota relation was built ",
                "to close): a first leg firing an iota (iota_step env e e1) and an arbitrary second ",
                "par_reduces_c leg join, under the (b2) guard, at the star-legged witness. Equals ",
                "par_strips_iota_source_c (Stage 1). Its symmetric sibling par_strips_iota_target_c closes ",
                "the iota-on-second-leg case. The structural x structural core is the already-proven ",
                "iota-free par_strips_bd, not reflectable into par_reduces_c without a c->bd reflection that ",
                "does not exist (the embedding is bd -> c only). DerivedProved, zero axiom_deps. Part of ",
                "#2859 (Increment F capstone)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "iota_step".to_string(),
                "minimal_or_inner".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_iota_source_c".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ============================================================
        // PHASE 1 — structural inversions for par_reduces_c (mirror the
        // par_reduces_bd_*_inv shape-recovery lemmas + the extra iota arm,
        // which is discharged via iota_step_head_none_absurd_type because a
        // binder-headed term has kexpr_const_name (kapp_fn _) = none and so
        // cannot be an iota redex). par_reduces_c_app_inv already exists.
        // ============================================================

        // par_reduces_c_lam_inv: from par_reduces_c env (lam ty body) t recover
        // t = lam ty' body' with ty => ty' and body => body'.
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_lam_inv".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (ty : KExpr) (body : KExpr) (t : KExpr) (C : KExpr -> Type), ",
                "par_reduces_c env (KExpr.lam ty body) t -> ",
                "(forall (ty' : KExpr) (body' : KExpr), ",
                "par_reduces_c env ty ty' -> par_reduces_c env body body' -> ",
                "C (KExpr.lam ty' body')) -> ",
                "C t"
            )
            .to_string(),
            value_src: Some(par_reduces_c_lam_inv_proof()),
            is_axiom: false,
            description: concat!(
                "Shape-recovery (inversion) for a lam-headed par_reduces_c: from ",
                "par_reduces_c env (lam ty body) t recover t = lam ty' body' with ty => ty' and ",
                "body => body'. refl folds in reflexive sub-derivations; the lam arm is the genuine ",
                "congruence; beta/app are app-headed (app_ne_lam), pi/forall_ are pi-headed ",
                "(pi_ne_lam), let_/let_cong are genuinely let-headed (let_ne_lam, since the ",
                "let-promotion); the iota arm is discharged because a binder head is not a const head ",
                "(iota_step_head_none_absurd_type). CPS form. DerivedProved via par_reduces_c.rec with ",
                "a source-equation motive + lam injectivity + Eq.subst. Zero axiom_deps. Part of #2859 ",
                "(Increment F, Phase 1 inversions)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.rec".to_string(),
                "par_reduces_c.refl".to_string(),
                "iota_step".to_string(),
                "iota_step_head_none_absurd_type".to_string(),
                "lam_inj_fst".to_string(),
                "lam_inj_snd".to_string(),
                "app_ne_lam".to_string(),
                "pi_ne_lam".to_string(),
                "let_ne_lam".to_string(),
                "instantiate".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "Eq.substType".to_string(),
                "Eq.subst".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_c_proj_inv: from par_reduces_c env (proj s i sub) t recover
        // t = proj s i sub' with sub => sub' (proj/lit fragment rung). proj is a
        // pure single-position congruence; non-proj arms discharge via
        // app/lam/pi/let_ne_proj, the iota arm via iota_step_head_none_absurd_type
        // (a proj head is not a const head), the matching proj arm via proj
        // injectivity. The convoy lemma par_strips_c_struct_proj consumes.
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_proj_inv".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (s : Name) (i : Nat) (sub : KExpr) (t : KExpr) (C : KExpr -> Type), ",
                "par_reduces_c env (KExpr.proj s i sub) t -> ",
                "(forall (sub' : KExpr), ",
                "par_reduces_c env sub sub' -> C (KExpr.proj s i sub')) -> ",
                "C t"
            )
            .to_string(),
            value_src: Some(par_reduces_c_proj_inv_proof()),
            is_axiom: false,
            description: concat!(
                "Shape-recovery (inversion) for a proj-headed par_reduces_c: from ",
                "par_reduces_c env (proj s i sub) t recover t = proj s i sub' with sub => sub'. ",
                "refl folds in a reflexive sub-derivation; the proj arm is the genuine congruence ",
                "(components recovered via proj_inj_name/idx/sub + Eq.subst); beta/app are ",
                "app-headed (app_ne_proj), lam by lam_ne_proj, pi/forall_ by pi_ne_proj, ",
                "let_/let_cong by let_ne_proj, and the iota arm by iota_step_head_none_absurd_type ",
                "(a proj head is not a const head). CPS form. DerivedProved via par_reduces_c.rec ",
                "with a source-equation motive. Zero axiom_deps. Part of the proj/lit fragment rung."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.rec".to_string(),
                "par_reduces_c.refl".to_string(),
                "iota_step".to_string(),
                "iota_step_head_none_absurd_type".to_string(),
                "proj_inj_name".to_string(),
                "proj_inj_idx".to_string(),
                "proj_inj_sub".to_string(),
                "app_ne_proj".to_string(),
                "lam_ne_proj".to_string(),
                "pi_ne_proj".to_string(),
                "let_ne_proj".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.subst".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_c_pi_inv / par_reduces_c_forall_inv: the two pi-headed
        // inversions. Because KExpr.forall_ is the reducible alias of KExpr.pi,
        // BOTH the pi and forall_ constructor arms are genuine matching cases
        // (their sources are definitionally equal), recovering sub-terms via
        // pi_inj_fst/snd. The app-headed (beta/app) arms are discharged by
        // app_ne_pi, the lam arm by lam_ne_pi, the genuinely let-headed
        // let_/let_cong arms by let_ne_pi (since the let-promotion), and the iota
        // arm by iota_step_head_none_absurd_type. They differ only in
        // source/reduct head.
        for (name, head, label) in [
            ("par_reduces_c_pi_inv", "KExpr.pi", "pi"),
            ("par_reduces_c_forall_inv", "KExpr.forall_", "forall_"),
        ] {
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    concat!(
                        "forall (env : RecEnv) (dom : KExpr) (body : KExpr) (t : KExpr) (C : KExpr -> Type), ",
                        "par_reduces_c env ({head} dom body) t -> ",
                        "(forall (dom' : KExpr) (body' : KExpr), ",
                        "par_reduces_c env dom dom' -> par_reduces_c env body body' -> ",
                        "C ({head} dom' body')) -> ",
                        "C t"
                    ),
                    head = head,
                ),
                value_src: Some(par_reduces_c_pi_like_inv_proof(head)),
                is_axiom: false,
                description: format!(
                    concat!(
                        "Shape-recovery (inversion) for a {label}-headed par_reduces_c: from ",
                        "par_reduces_c env ({head} dom body) t recover t = {head} dom' body' with ",
                        "dom => dom' and body => body'. Both the pi and forall_ congruence arms match ",
                        "(forall_ is the reducible alias of pi); refl folds in reflexive sub-derivations; ",
                        "beta/app are app-headed (app_ne_pi), lam is discharged by lam_ne_pi, let_/let_cong ",
                        "are genuinely let-headed (let_ne_pi, since the let-promotion), the ",
                        "iota arm by iota_step_head_none_absurd_type (binder head /= const head). CPS form. ",
                        "DerivedProved via par_reduces_c.rec with a source-equation motive + pi injectivity ",
                        "+ Eq.subst. Zero axiom_deps. Part of #2859 (Increment F, Phase 1 inversions)."
                    ),
                    label = label,
                    head = head,
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_reduces_c".to_string(),
                    "par_reduces_c.rec".to_string(),
                    "par_reduces_c.refl".to_string(),
                    "iota_step".to_string(),
                    "iota_step_head_none_absurd_type".to_string(),
                    "pi_inj_fst".to_string(),
                    "pi_inj_snd".to_string(),
                    "app_ne_pi".to_string(),
                    "lam_ne_pi".to_string(),
                    "let_ne_pi".to_string(),
                    "instantiate".to_string(),
                    "kexpr_const_name".to_string(),
                    "kapp_fn".to_string(),
                    "Eq.substType".to_string(),
                    "Eq.subst".to_string(),
                    "Eq.symm".to_string(),
                    "Eq.refl".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // par_reduces_c_let_inv: the let-headed CPS inversion (NEW with the
        // let-promotion — the genuine KExpr.let_ node needs its own shape
        // recovery; under the old alias a let source was app-headed and rode
        // par_reduces_c_app_inv). From par_reduces_c env (let_ ty val body) t the
        // only inhabitable arms are refl (folded into the congruence continuation
        // with reflexive sub-derivations), let_cong (the congruence continuation
        // kcong, components transported via let injectivity), and let_ (the ZETA
        // contraction continuation kzeta, likewise transported). beta/app sources
        // are refuted by let_ne_app, lam by let_ne_lam, pi/forall_ by let_ne_pi
        // (each via Eq.symm — the arm equation runs arm-source = let), and the
        // iota arm is discharged because a let is its own spine head
        // (kexpr_const_name = none, iota_step_head_none_absurd_type).
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_let_inv".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (ty : KExpr) (val : KExpr) (body : KExpr) (t : KExpr) (C : KExpr -> Type), ",
                "par_reduces_c env (KExpr.let_ ty val body) t -> ",
                "(forall (ty' : KExpr) (val' : KExpr) (body' : KExpr), ",
                "par_reduces_c env ty ty' -> par_reduces_c env val val' -> par_reduces_c env body body' -> ",
                "C (KExpr.let_ ty' val' body')) -> ",
                "(forall (ty' : KExpr) (val' : KExpr) (body' : KExpr), ",
                "par_reduces_c env ty ty' -> par_reduces_c env val val' -> par_reduces_c env body body' -> ",
                "C (instantiate body' val')) -> ",
                "C t"
            )
            .to_string(),
            value_src: Some(par_reduces_c_let_inv_proof()),
            is_axiom: false,
            description: concat!(
                "Shape-recovery (inversion) for a let-headed par_reduces_c over the GENUINE KExpr.let_ ",
                "constructor: from par_reduces_c env (let_ ty val body) t dispatch to the congruence ",
                "continuation kcong (t = let_ ty' val' body', via refl with reflexive sub-derivations or ",
                "let_cong with let-injectivity transports) or the ZETA contraction continuation kzeta ",
                "(t = instantiate body' val'). beta/app arms are refuted by let_ne_app, lam by let_ne_lam, ",
                "pi/forall_ by let_ne_pi; the iota arm is discharged because a let is its own spine head ",
                "(kexpr_const_name (kapp_fn (let_ ..)) = none by defeq, iota_step_head_none_absurd_type). ",
                "CPS form, mirror of par_reduces_c_app_inv/lam_inv for the 7th constructor. The dispatcher ",
                "the zeta-source and let_cong-source diamonds consume. DerivedProved via par_reduces_c.rec ",
                "with a source-equation motive + let injectivity + Eq.substType. Zero axiom_deps. Part of ",
                "the let-promotion batch B4."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.rec".to_string(),
                "par_reduces_c.refl".to_string(),
                "iota_step".to_string(),
                "iota_step_head_none_absurd_type".to_string(),
                "let_inj_fst".to_string(),
                "let_inj_snd".to_string(),
                "let_inj_thd".to_string(),
                "let_ne_app".to_string(),
                "let_ne_lam".to_string(),
                "let_ne_pi".to_string(),
                "instantiate".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "Eq.substType".to_string(),
                "Eq.subst".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ============================================================
        // PHASE 2 — par_subst_c.
        //
        // FORMULATION DECISION (assessed against the landed substrate): the iota
        // arm of the substitution lemma is intrinsically MULTI-STEP. The landed
        // par_subst_iota_arm_c proves
        //   RecEnvClosed env -> iota_step env e e' -> par_reduces_bd v v'
        //     -> par_reduces_c_STAR env (inst e v d) (inst e' v' d)
        // because par_reduces_c.iota is atomic (one redex per step): firing the
        // iota AND reducing the value v=>v' cannot be a single par_reduces_c step.
        // So par_subst_c CANNOT conclude a single par_reduces_c — it MUST conclude
        // par_reduces_c_star. (This is the "_star vs guard" decision the brief
        // flagged: it lands as _star, not via a guard.)
        //
        // Value source: BOTH landed halves (par_subst_refl_c, par_subst_iota_arm_c)
        // take a par_reduces_BD value source (there is no par_reduces_c -> _bd
        // reflection; the embedding is bd -> c only, and a par_reduces_c value
        // source would force a full par_subst_refl over par_reduces_c, an
        // independent ~350-line bvar-convoy KExpr.rec). par_subst_c therefore takes
        // a par_reduces_bd value source v => v', matching the substrate exactly.
        // The RecEnvClosed env hypothesis is threaded for the iota arm (E-core).
        //
        // To run par_reduces_c.rec on e => e' with a _star-valued, depth-generalized
        // motive, the structural arms need _star-level congruences. We build those
        // first (app / binder / let_cong / beta / let_-zeta over par_reduces_c_star),
        // then par_subst_c.
        // ============================================================

        // par_reduces_c_star_app: app is a par_reduces_c_star congruence in both
        // positions. f =>* f' and a =>* a' give app f a =>* app f' a'. Two one-sided
        // star inductions (reduce the function spine, then the argument), composed by
        // par_reduces_c_star_trans through the waypoint app f' a.
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_star_app".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), ",
                "par_reduces_c_star env f f' -> par_reduces_c_star env a a' -> ",
                "par_reduces_c_star env (KExpr.app f a) (KExpr.app f' a')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(hf : par_reduces_c_star env f f') (ha : par_reduces_c_star env a a') => ",
                    // left leg: app f a =>* app f' a  (induct on hf, fix arg a)
                    "par_reduces_c_star_trans env (KExpr.app f a) (KExpr.app f' a) (KExpr.app f' a') ",
                    "(par_reduces_c_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_c_star env x y) => ",
                    "par_reduces_c_star env (KExpr.app x a) (KExpr.app y a)) ",
                    "(fun (x : KExpr) => par_reduces_c_star.refl env (KExpr.app x a)) ",
                    "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                    "(hstep : par_reduces_c env x x') (_htail : par_reduces_c_star env x' x'') ",
                    "(ih : par_reduces_c_star env (KExpr.app x' a) (KExpr.app x'' a)) => ",
                    "par_reduces_c_star.step env (KExpr.app x a) (KExpr.app x' a) (KExpr.app x'' a) ",
                    "(par_reduces_c.app env x x' a a hstep (par_reduces_c.refl env a)) ih) ",
                    "f f' hf) ",
                    // right leg: app f' a =>* app f' a'  (induct on ha, fix fn f')
                    "(par_reduces_c_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_c_star env x y) => ",
                    "par_reduces_c_star env (KExpr.app f' x) (KExpr.app f' y)) ",
                    "(fun (x : KExpr) => par_reduces_c_star.refl env (KExpr.app f' x)) ",
                    "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                    "(hstep : par_reduces_c env x x') (_htail : par_reduces_c_star env x' x'') ",
                    "(ih : par_reduces_c_star env (KExpr.app f' x') (KExpr.app f' x'')) => ",
                    "par_reduces_c_star.step env (KExpr.app f' x) (KExpr.app f' x') (KExpr.app f' x'') ",
                    "(par_reduces_c.app env f' f' x x' (par_reduces_c.refl env f') hstep) ih) ",
                    "a a' ha)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "app congruence at the par_reduces_c_star level: f =>* f' and a =>* a' give ",
                "app f a =>* app f' a'. Two one-sided star inductions (par_reduces_c_star.rec) composed by ",
                "par_reduces_c_star_trans through app f' a; each single step lifts via par_reduces_c.app with a ",
                "reflexive companion. DerivedProved, zero axiom_deps. Part of #2859 (Increment F, Phase 2)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.app".to_string(),
                "par_reduces_c.refl".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.refl".to_string(),
                "par_reduces_c_star.step".to_string(),
                "par_reduces_c_star.rec".to_string(),
                "par_reduces_c_star_trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_c_star_proj: proj is a par_reduces_c_star congruence in its
        // single scrutinee position. sub1 =>* sub2 gives proj s i sub1 =>* proj s
        // i sub2. One star induction prefixing par_reduces_c.proj on each step
        // (proj/lit fragment rung).
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_star_proj".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (s : Name) (i : Nat) (sub1 : KExpr) (sub2 : KExpr), ",
                "par_reduces_c_star env sub1 sub2 -> ",
                "par_reduces_c_star env (KExpr.proj s i sub1) (KExpr.proj s i sub2)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (s : Name) (i : Nat) (sub1 : KExpr) (sub2 : KExpr) ",
                    "(hsub : par_reduces_c_star env sub1 sub2) => ",
                    "par_reduces_c_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_c_star env x y) => ",
                    "par_reduces_c_star env (KExpr.proj s i x) (KExpr.proj s i y)) ",
                    "(fun (x : KExpr) => par_reduces_c_star.refl env (KExpr.proj s i x)) ",
                    "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                    "(hstep : par_reduces_c env x x') (_htail : par_reduces_c_star env x' x'') ",
                    "(ih : par_reduces_c_star env (KExpr.proj s i x') (KExpr.proj s i x'')) => ",
                    "par_reduces_c_star.step env (KExpr.proj s i x) (KExpr.proj s i x') (KExpr.proj s i x'') ",
                    "(par_reduces_c.proj env s i x x' hstep) ih) ",
                    "sub1 sub2 hsub"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "proj congruence at the par_reduces_c_star level: sub1 =>* sub2 gives ",
                "proj s i sub1 =>* proj s i sub2. One star induction (par_reduces_c_star.rec) ",
                "prefixing par_reduces_c.proj on each step. DerivedProved, zero axiom_deps. ",
                "Part of the proj/lit fragment rung."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.proj".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.refl".to_string(),
                "par_reduces_c_star.step".to_string(),
                "par_reduces_c_star.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_c_star_lam / _pi / _forall: binder congruences at the
        // par_reduces_c_star level. ty =>* ty' and body =>* body' give
        // HEAD ty body =>* HEAD ty' body'. Same two-one-sided-induction shape as
        // par_reduces_c_star_app, using the matching binder ctor (par_reduces_c.lam /
        // .pi / .forall_) with a reflexive companion at each single step.
        for (name, head, ctor, label) in [
            (
                "par_reduces_c_star_lam",
                "KExpr.lam",
                "par_reduces_c.lam",
                "lam",
            ),
            (
                "par_reduces_c_star_pi",
                "KExpr.pi",
                "par_reduces_c.pi",
                "pi",
            ),
            (
                "par_reduces_c_star_forall",
                "KExpr.forall_",
                "par_reduces_c.forall_",
                "forall_",
            ),
        ] {
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    concat!(
                        "forall (env : RecEnv) (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr), ",
                        "par_reduces_c_star env ty ty' -> par_reduces_c_star env body body' -> ",
                        "par_reduces_c_star env ({head} ty body) ({head} ty' body')"
                    ),
                    head = head,
                ),
                value_src: Some(format!(
                    concat!(
                        "fun (env : RecEnv) (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                        "(hty : par_reduces_c_star env ty ty') (hbody : par_reduces_c_star env body body') => ",
                        // left leg: HEAD ty body =>* HEAD ty' body  (induct on hty)
                        "par_reduces_c_star_trans env ({head} ty body) ({head} ty' body) ({head} ty' body') ",
                        "(par_reduces_c_star.rec env ",
                        "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_c_star env x y) => ",
                        "par_reduces_c_star env ({head} x body) ({head} y body)) ",
                        "(fun (x : KExpr) => par_reduces_c_star.refl env ({head} x body)) ",
                        "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                        "(hstep : par_reduces_c env x x') (_htail : par_reduces_c_star env x' x'') ",
                        "(ih : par_reduces_c_star env ({head} x' body) ({head} x'' body)) => ",
                        "par_reduces_c_star.step env ({head} x body) ({head} x' body) ({head} x'' body) ",
                        "({ctor} env x x' body body hstep (par_reduces_c.refl env body)) ih) ",
                        "ty ty' hty) ",
                        // right leg: HEAD ty' body =>* HEAD ty' body'  (induct on hbody)
                        "(par_reduces_c_star.rec env ",
                        "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_c_star env x y) => ",
                        "par_reduces_c_star env ({head} ty' x) ({head} ty' y)) ",
                        "(fun (x : KExpr) => par_reduces_c_star.refl env ({head} ty' x)) ",
                        "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                        "(hstep : par_reduces_c env x x') (_htail : par_reduces_c_star env x' x'') ",
                        "(ih : par_reduces_c_star env ({head} ty' x') ({head} ty' x'')) => ",
                        "par_reduces_c_star.step env ({head} ty' x) ({head} ty' x') ({head} ty' x'') ",
                        "({ctor} env ty' ty' x x' (par_reduces_c.refl env ty') hstep) ih) ",
                        "body body' hbody)"
                    ),
                    head = head,
                    ctor = ctor,
                )),
                is_axiom: false,
                description: format!(
                    concat!(
                        "{label} congruence at the par_reduces_c_star level: ty =>* ty' and body =>* body' give ",
                        "{head} ty body =>* {head} ty' body'. Two one-sided star inductions composed by ",
                        "par_reduces_c_star_trans; each single step lifts via {ctor} with a reflexive companion. ",
                        "DerivedProved, zero axiom_deps. Part of #2859 (Increment F, Phase 2)."
                    ),
                    label = label,
                    head = head,
                    ctor = ctor,
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_reduces_c".to_string(),
                    ctor.to_string(),
                    "par_reduces_c.refl".to_string(),
                    "par_reduces_c_star".to_string(),
                    "par_reduces_c_star.refl".to_string(),
                    "par_reduces_c_star.step".to_string(),
                    "par_reduces_c_star.rec".to_string(),
                    "par_reduces_c_star_trans".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // par_reduces_c_star_let_cong: the 3-position let congruence at the
        // par_reduces_c_star level (NEW with the let-promotion — the genuine
        // KExpr.let_ node needs its own star congruence; the old alias rode the
        // app+lam star congruences). ty =>* ty', val =>* val', body =>* body' give
        // let_ ty val body =>* let_ ty' val' body'. Three one-sided star inductions
        // composed by two par_reduces_c_star_trans through the waypoints
        // let_ ty' val body and let_ ty' val' body; each single step lifts via
        // par_reduces_c.let_cong with reflexive companions.
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_star_let_cong".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), ",
                "par_reduces_c_star env ty ty' -> par_reduces_c_star env val val' -> par_reduces_c_star env body body' -> ",
                "par_reduces_c_star env (KExpr.let_ ty val body) (KExpr.let_ ty' val' body')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(hty : par_reduces_c_star env ty ty') (hval : par_reduces_c_star env val val') (hbody : par_reduces_c_star env body body') => ",
                    "par_reduces_c_star_trans env (KExpr.let_ ty val body) (KExpr.let_ ty' val body) (KExpr.let_ ty' val' body') ",
                    // leg 1: ty position (val/body fixed)
                    "(par_reduces_c_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_c_star env x y) => ",
                    "par_reduces_c_star env (KExpr.let_ x val body) (KExpr.let_ y val body)) ",
                    "(fun (x : KExpr) => par_reduces_c_star.refl env (KExpr.let_ x val body)) ",
                    "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                    "(hstep : par_reduces_c env x x') (_htail : par_reduces_c_star env x' x'') ",
                    "(ih : par_reduces_c_star env (KExpr.let_ x' val body) (KExpr.let_ x'' val body)) => ",
                    "par_reduces_c_star.step env (KExpr.let_ x val body) (KExpr.let_ x' val body) (KExpr.let_ x'' val body) ",
                    "(par_reduces_c.let_cong env x x' val val body body hstep (par_reduces_c.refl env val) (par_reduces_c.refl env body)) ih) ",
                    "ty ty' hty) ",
                    "(par_reduces_c_star_trans env (KExpr.let_ ty' val body) (KExpr.let_ ty' val' body) (KExpr.let_ ty' val' body') ",
                    // leg 2: val position (ty'/body fixed)
                    "(par_reduces_c_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_c_star env x y) => ",
                    "par_reduces_c_star env (KExpr.let_ ty' x body) (KExpr.let_ ty' y body)) ",
                    "(fun (x : KExpr) => par_reduces_c_star.refl env (KExpr.let_ ty' x body)) ",
                    "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                    "(hstep : par_reduces_c env x x') (_htail : par_reduces_c_star env x' x'') ",
                    "(ih : par_reduces_c_star env (KExpr.let_ ty' x' body) (KExpr.let_ ty' x'' body)) => ",
                    "par_reduces_c_star.step env (KExpr.let_ ty' x body) (KExpr.let_ ty' x' body) (KExpr.let_ ty' x'' body) ",
                    "(par_reduces_c.let_cong env ty' ty' x x' body body (par_reduces_c.refl env ty') hstep (par_reduces_c.refl env body)) ih) ",
                    "val val' hval) ",
                    // leg 3: body position (ty'/val' fixed)
                    "(par_reduces_c_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_c_star env x y) => ",
                    "par_reduces_c_star env (KExpr.let_ ty' val' x) (KExpr.let_ ty' val' y)) ",
                    "(fun (x : KExpr) => par_reduces_c_star.refl env (KExpr.let_ ty' val' x)) ",
                    "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                    "(hstep : par_reduces_c env x x') (_htail : par_reduces_c_star env x' x'') ",
                    "(ih : par_reduces_c_star env (KExpr.let_ ty' val' x') (KExpr.let_ ty' val' x'')) => ",
                    "par_reduces_c_star.step env (KExpr.let_ ty' val' x) (KExpr.let_ ty' val' x') (KExpr.let_ ty' val' x'') ",
                    "(par_reduces_c.let_cong env ty' ty' val' val' x x' (par_reduces_c.refl env ty') (par_reduces_c.refl env val') hstep) ih) ",
                    "body body' hbody))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "let congruence at the par_reduces_c_star level over the GENUINE KExpr.let_ node: ",
                "ty =>* ty', val =>* val', body =>* body' give let_ ty val body =>* let_ ty' val' body'. ",
                "Three one-sided star inductions composed by par_reduces_c_star_trans; each single step ",
                "lifts via par_reduces_c.let_cong with reflexive companions. The 3-component sibling of ",
                "par_reduces_c_star_lam/pi/app. DerivedProved, zero axiom_deps. Part of the let-promotion ",
                "batch B4."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.let_cong".to_string(),
                "par_reduces_c.refl".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.refl".to_string(),
                "par_reduces_c_star.step".to_string(),
                "par_reduces_c_star.rec".to_string(),
                "par_reduces_c_star_trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_c_star_beta: the beta contraction as a par_reduces_c_star,
        // congruent in all three positions. From A =>* A', body =>* body', arg =>* arg',
        // conclude app (lam A body) arg =>* instantiate body' arg'. Two phases:
        //   (1) app (lam A body) arg =>* app (lam A' body') arg'  (star app+lam congs)
        //   (2) app (lam A' body') arg' => instantiate body' arg'  (one par_reduces_c.beta
        //       with reflexive sub-derivations), embedded into _star.
        // composed by par_reduces_c_star_trans. This lifts the beta arm of par_subst_c
        // (whose IHs are intrinsically multi-step) to the _star endpoint.
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_star_beta".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr), ",
                "par_reduces_c_star env A A' -> par_reduces_c_star env body body' -> par_reduces_c_star env arg arg' -> ",
                "par_reduces_c_star env (KExpr.app (KExpr.lam A body) arg) (instantiate body' arg')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) ",
                    "(hA : par_reduces_c_star env A A') (hbody : par_reduces_c_star env body body') (harg : par_reduces_c_star env arg arg') => ",
                    "par_reduces_c_star_trans env ",
                    "(KExpr.app (KExpr.lam A body) arg) (KExpr.app (KExpr.lam A' body') arg') (instantiate body' arg') ",
                    "(par_reduces_c_star_app env (KExpr.lam A body) (KExpr.lam A' body') arg arg' ",
                    "(par_reduces_c_star_lam env A A' body body' hA hbody) harg) ",
                    "(par_subsumes_par_c_star env (KExpr.app (KExpr.lam A' body') arg') (instantiate body' arg') ",
                    "(par_reduces_c.beta env A' A' body' body' arg' arg' ",
                    "(par_reduces_c.refl env A') (par_reduces_c.refl env body') (par_reduces_c.refl env arg')))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "beta contraction at the par_reduces_c_star level: A =>* A', body =>* body', arg =>* arg' give ",
                "app (lam A body) arg =>* instantiate body' arg'. Phase 1 (star app+lam congruences) reduces the ",
                "redex skeleton to app (lam A' body') arg'; phase 2 fires one par_reduces_c.beta (reflexive ",
                "sub-derivations) embedded via par_subsumes_par_c_star; composed by par_reduces_c_star_trans. ",
                "Lifts the multi-step beta arm of par_subst_c. DerivedProved, zero axiom_deps. Part of #2859 (Increment F, Phase 2)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.beta".to_string(),
                "par_reduces_c.refl".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star_app".to_string(),
                "par_reduces_c_star_lam".to_string(),
                "par_subsumes_par_c_star".to_string(),
                "par_reduces_c_star_trans".to_string(),
                "instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_c_star_let: the let_ (ZETA) contraction as a
        // par_reduces_c_star, congruent in all three positions. From ty =>* ty',
        // val =>* val', body =>* body', conclude let_ ty val body =>* instantiate
        // body' val'. Same two-phase shape as par_reduces_c_star_beta: phase 1 is
        // the GENUINE let congruence par_reduces_c_star_let_cong (KExpr.let_ is a
        // genuine constructor since the let-promotion — no app/lam alias skeleton),
        // phase 2 fires one par_reduces_c.let_ (zeta) step.
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_star_let".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), ",
                "par_reduces_c_star env ty ty' -> par_reduces_c_star env val val' -> par_reduces_c_star env body body' -> ",
                "par_reduces_c_star env (KExpr.let_ ty val body) (instantiate body' val')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(hty : par_reduces_c_star env ty ty') (hval : par_reduces_c_star env val val') (hbody : par_reduces_c_star env body body') => ",
                    "par_reduces_c_star_trans env ",
                    "(KExpr.let_ ty val body) (KExpr.let_ ty' val' body') (instantiate body' val') ",
                    // phase 1: the genuine 3-position let congruence.
                    "(par_reduces_c_star_let_cong env ty ty' val val' body body' hty hval hbody) ",
                    // phase 2: one par_reduces_c.let_ (zeta) step with reflexive sub-derivations.
                    "(par_subsumes_par_c_star env (KExpr.let_ ty' val' body') (instantiate body' val') ",
                    "(par_reduces_c.let_ env ty' ty' val' val' body' body' ",
                    "(par_reduces_c.refl env ty') (par_reduces_c.refl env val') (par_reduces_c.refl env body')))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "let_ (zeta) contraction at the par_reduces_c_star level: ty =>* ty', val =>* val', ",
                "body =>* body' give let_ ty val body =>* instantiate body' val'. Phase 1 reduces the ",
                "genuine let node componentwise (par_reduces_c_star_let_cong — no app/lam alias skeleton ",
                "since the let-promotion); phase 2 fires one par_reduces_c.let_ zeta step (reflexive ",
                "sub-derivations) embedded via par_subsumes_par_c_star; composed by par_reduces_c_star_trans. ",
                "Lifts the multi-step let_ arm of par_subst_c. DerivedProved, zero axiom_deps. Part of #2859 ",
                "(Increment F, Phase 2)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.let_".to_string(),
                "par_reduces_c.refl".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star_let_cong".to_string(),
                "par_subsumes_par_c_star".to_string(),
                "par_reduces_c_star_trans".to_string(),
                "instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ============================================================
        // par_subst_c — THE Phase 2 substitution lemma. Honestly stated as a
        // par_reduces_c_STAR conclusion (the iota arm is intrinsically 2-step;
        // see the formulation note above), over a par_reduces_BD value source
        // (matching the landed par_subst_refl_c / par_subst_iota_arm_c, with no
        // c->bd reflection required). RecEnvClosed env is threaded for the iota arm.
        //
        //   forall env e e' v v' d,
        //     par_reduces_c env e e' -> par_reduces_bd v v' -> RecEnvClosed env ->
        //     par_reduces_c_star env (instantiate_at e v d) (instantiate_at e' v' d)
        //
        // par_reduces_c.rec on e => e' with a depth-generalized, _star-valued motive:
        //   refl  -> par_subst_refl_c (lifted to _star)
        //   app   -> par_reduces_c_star_app on the two IHs
        //   lam/pi/forall_ -> the matching _star binder congruence (body IH at depth+1)
        //   beta/let_ -> the _star contraction congruence + instantiate_nested_commutes
        //   iota  -> par_subst_iota_arm_c (the E-core 2-step star)
        //   let_cong -> par_reduces_c_star_let_cong on the three IHs (body at depth+1)
        // ============================================================
        self.add_definition(SpecDefinition {
            name: "par_subst_c".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr) (v : KExpr) (v' : KExpr) (d : Nat), ",
                "par_reduces_c env e e' -> par_reduces_bd v v' -> RecEnvClosed env -> ",
                "par_reduces_c_star env (instantiate_at e v d) (instantiate_at e' v' d)"
            )
            .to_string(),
            value_src: Some(par_subst_c_proof()),
            is_axiom: false,
            description: concat!(
                "Substitution congruence for par_reduces_c, honestly stated as a par_reduces_c_star ",
                "conclusion (the iota arm is intrinsically 2-step; par_reduces_c.iota is atomic). Over a ",
                "par_reduces_bd value source (matching the landed substrate; no c->bd reflection needed). ",
                "par_reduces_c.rec on e => e' with a depth-generalized _star motive threading RecEnvClosed: ",
                "refl -> par_subst_refl_c (lifted); app -> par_reduces_c_star_app; lam/pi/forall_ -> the ",
                "matching _star binder congruence (body at depth+1); beta/let_ -> the _star contraction ",
                "congruence + instantiate_nested_commutes_zero_subst transport (the let_ redex skeleton is ",
                "the genuine let node since the let-promotion); let_cong -> par_reduces_c_star_let_cong on ",
                "the three IHs (body at depth+1); iota -> par_subst_iota_arm_c ",
                "(the E-core 2-step star, the Wave-122 wall now closed computationally). DerivedProved, zero ",
                "axiom_deps. Part of #2859 (Increment F, Phase 2)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.rec".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_bd".to_string(),
                "RecEnvClosed".to_string(),
                "par_subst_refl_c".to_string(),
                "par_subsumes_par_c_star".to_string(),
                "par_reduces_c_star_app".to_string(),
                "par_reduces_c_star_lam".to_string(),
                "par_reduces_c_star_pi".to_string(),
                "par_reduces_c_star_forall".to_string(),
                "par_reduces_c_star_beta".to_string(),
                "par_reduces_c_star_let".to_string(),
                "par_reduces_c_star_let_cong".to_string(),
                "par_subst_iota_arm_c".to_string(),
                "instantiate_at".to_string(),
                "instantiate".to_string(),
                "instantiate_nested_commutes_zero_subst".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ============================================================
        // FINAL ASSEMBLY #1 — par_subst_refl_full_c: the FULL-relation refl
        // substitution congruence. Substitutes a parallel-reducing value v => v'
        // (a genuine par_reduces_c step, INCLUDING the iota arm) into a FIXED term
        // e at depth d. Mirrors par_subst_refl_bd (KExpr.rec on e with the
        // triple-Nat.rec bvar convoy) but: concludes _star (the bvar arm's lift is
        // a single par-step that subsumes; the binder/app arms thread the _star
        // congruences), the i=d leaf calls par_lift_full_c (the FULL lift, which
        // handles iota in v), and threads RecEnvLiftClosed env (which
        // par_lift_full_c gates on). This is the v=>v' half of the full par_subst.
        // ============================================================
        self.add_definition(SpecDefinition {
            name: "par_subst_refl_full_c".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (v : KExpr) (v' : KExpr) (d : Nat), ",
                "RecEnvLiftClosed env -> par_reduces_c env v v' -> ",
                "par_reduces_c_star env (instantiate_at e v d) (instantiate_at e v' d)"
            )
            .to_string(),
            value_src: Some(par_subst_refl_full_c_proof()),
            is_axiom: false,
            description: concat!(
                "FULL-relation reflexive substitution congruence for par_reduces_c: under a lift-closed env, ",
                "a genuine value reduction v => v' (INCLUDING the iota arm) substituted into a FIXED term e at ",
                "depth d gives par_reduces_c_star env (instantiate_at e v d) (instantiate_at e v' d). KExpr.rec ",
                "on e (mirror of par_subst_refl_bd's triple-Nat.rec bvar convoy): sort/const -> refl-star; the ",
                "i=d bvar leaf -> par_lift_full_c (the FULL lift congruence handling iota in v) subsumed to ",
                "_star; i<d / i>d leaves -> refl-star; app/lam/pi -> the matching _star congruence (body at ",
                "depth+1); let_ -> par_reduces_c_star_let_cong on the three sub-IHs (ty/val at depth, body at ",
                "depth+1, the genuine 7th-constructor arm). Unlike par_subst_refl_c (which embeds the iota-free par_subst_refl_bd over a ",
                "par_reduces_bd source), this recurses on a full par_reduces_c value via par_lift_full_c — the ",
                "v=>v' half the full par_subst contraction cross-cases need. DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment F final assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.refl".to_string(),
                "RecEnvLiftClosed".to_string(),
                "par_lift_full_c".to_string(),
                "par_subsumes_par_c_star".to_string(),
                "par_reduces_c_star_app".to_string(),
                "par_reduces_c_star_lam".to_string(),
                "par_reduces_c_star_pi".to_string(),
                "par_reduces_c_star_let_cong".to_string(),
                "KExpr.rec".to_string(),
                "instantiate_at".to_string(),
                "instantiate_bvar_at".to_string(),
                "instantiate_at_bvar".to_string(),
                "instantiate_at_bvar_eq_from_zero_witnesses".to_string(),
                "instantiate_bvar_at_below".to_string(),
                "instantiate_bvar_at_above".to_string(),
                "nat_pos_witness_from_succ_eq".to_string(),
                "nat_sub_zero_of_sub_pos".to_string(),
                "lift_at".to_string(),
                "Eq.substType".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ============================================================
        // FINAL ASSEMBLY #2a — par_subst_iota_arm_full_c: the par_subst iota arm
        // for a FULL value reduction v => v' (par_reduces_c, not par_reduces_bd).
        // Same 2-step star as par_subst_iota_arm_c (par_reduces_c.iota is atomic),
        // but the value congruence (step 2) goes through par_subst_refl_full_c (the
        // full-relation refl substitution, #1) instead of par_subst_refl_c:
        //   step 1 (iota_step_subst_c / E-core): inst e v d => inst e' v d (same value),
        //   step 2 (par_subst_refl_full_c): inst e' v d =>* inst e' v' d (value v=>v').
        // par_subst_refl_full_c is already _star-valued, so the composition is
        // par_reduces_c_star.step (single iota leg, _star tail). Threads RecEnvClosed
        // (step 1) AND RecEnvLiftClosed (step 2, par_lift_full_c).
        // ============================================================
        self.add_definition(SpecDefinition {
            name: "par_subst_iota_arm_full_c".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr) (v : KExpr) (v' : KExpr) (d : Nat), ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> iota_step env e e' -> par_reduces_c env v v' -> ",
                "par_reduces_c_star env (instantiate_at e v d) (instantiate_at e' v' d)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (e' : KExpr) (v : KExpr) (v' : KExpr) (d : Nat) ",
                    "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) ",
                    "(h : iota_step env e e') (hv : par_reduces_c env v v') => ",
                    "par_reduces_c_star.step env ",
                    "(instantiate_at e v d) (instantiate_at e' v d) (instantiate_at e' v' d) ",
                    "(iota_step_subst_c env e e' v d closed h) ",
                    "(par_subst_refl_full_c env e' v v' d liftclosed hv))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The par_subst iota arm for a FULL value reduction v => v' (par_reduces_c, including iota in ",
                "v), as a 2-step star: from a closed + lift-closed env, an iota redex e => e', and a full value ",
                "reduction v => v', the substituted terms join inst e v d => inst e' v d (E-core, same value, ",
                "iota_step_subst_c) =>* inst e' v' d (full value congruence on the fixed reduct, ",
                "par_subst_refl_full_c). par_reduces_c_star.step composes the single iota leg with the _star ",
                "tail. The full-relation sibling of par_subst_iota_arm_c (which takes a par_reduces_bd value). ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment F final assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.step".to_string(),
                "iota_step_subst_c".to_string(),
                "par_subst_refl_full_c".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "iota_step".to_string(),
                "instantiate_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ============================================================
        // FINAL ASSEMBLY #2 — par_subst_full_c: THE full-relation substitution
        // lemma. Over a FULL par_reduces_c value source v => v' (not par_reduces_bd),
        // honestly stated as a _star conclusion. par_reduces_c.rec on e => e' with a
        // depth-generalized _star motive threading both closure predicates:
        //   refl  -> par_subst_refl_full_c (#1, already _star)
        //   app   -> par_reduces_c_star_app on the two IHs
        //   lam/pi/forall_ -> the matching _star binder congruence (body IH at depth+1)
        //   beta/let_ -> the _star contraction congruence + instantiate_nested_commutes
        //   iota  -> par_subst_iota_arm_full_c (#2a, the full-value E-core 2-step star)
        //   let_cong -> par_reduces_c_star_let_cong on the three IHs (body at depth+1)
        // Threads RecEnvClosed (iota arm step 1) AND RecEnvLiftClosed (the v=>v'
        // congruence's par_lift_full_c).
        // ============================================================
        self.add_definition(SpecDefinition {
            name: "par_subst_full_c".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr) (v : KExpr) (v' : KExpr) (d : Nat), ",
                "par_reduces_c env e e' -> par_reduces_c env v v' -> RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_reduces_c_star env (instantiate_at e v d) (instantiate_at e' v' d)"
            )
            .to_string(),
            value_src: Some(par_subst_full_c_proof()),
            is_axiom: false,
            description: concat!(
                "FULL-relation substitution congruence for par_reduces_c: over a genuine value reduction ",
                "v => v' (par_reduces_c, INCLUDING iota in v), honestly stated as a par_reduces_c_star ",
                "conclusion (par_reduces_c.iota is atomic). par_reduces_c.rec on e => e' with a depth-generalized ",
                "_star motive threading both RecEnvClosed and RecEnvLiftClosed: refl -> par_subst_refl_full_c; ",
                "app -> par_reduces_c_star_app; lam/pi/forall_ -> the _star binder congruence (body at depth+1); ",
                "beta/let_ -> the _star contraction congruence + instantiate_nested_commutes_zero_subst transport ",
                "(the let_ redex skeleton is the genuine let node since the let-promotion); let_cong -> ",
                "par_reduces_c_star_let_cong on the three IHs (body at depth+1); ",
                "iota -> par_subst_iota_arm_full_c (the full-value E-core 2-step star). The full-relation sibling ",
                "of par_subst_c (which takes a par_reduces_bd value) — the substitution lemma the contraction ",
                "cross-cases of the full structural diamond meet through. DerivedProved, zero axiom_deps. Part ",
                "of #2859 (Increment F final assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.rec".to_string(),
                "par_reduces_c_star".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "par_subst_refl_full_c".to_string(),
                "par_reduces_c_star_app".to_string(),
                "par_reduces_c_star_lam".to_string(),
                "par_reduces_c_star_pi".to_string(),
                "par_reduces_c_star_forall".to_string(),
                "par_reduces_c_star_beta".to_string(),
                "par_reduces_c_star_let".to_string(),
                "par_reduces_c_star_let_cong".to_string(),
                "par_subst_iota_arm_full_c".to_string(),
                "instantiate_at".to_string(),
                "instantiate".to_string(),
                "instantiate_nested_commutes_zero_subst".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ============================================================
        // FINAL ASSEMBLY #2b — the _star-generalized substitution lemmas. The
        // structural contraction cross-cases (#3) meet body/arg sub-diamonds whose
        // legs are par_reduces_c_STAR (multi-step), but par_subst_full_c takes
        // SINGLE par_reduces_c legs. So we lift it to star legs on BOTH the term and
        // the value via two one-sided star inductions.
        // ============================================================

        // par_subst_refl_full_c_star: refl substitution with a STAR value leg
        // (term e fixed, v =>* v'). par_reduces_c_star.rec on v =>* v': refl ->
        // refl-star; step v => vmid =>* v' -> trans (par_subst_refl_full_c at the
        // single step v => vmid) (IH on vmid =>* v').
        self.add_definition(SpecDefinition {
            name: "par_subst_refl_full_c_star".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (v : KExpr) (v' : KExpr) (d : Nat), ",
                "RecEnvLiftClosed env -> par_reduces_c_star env v v' -> ",
                "par_reduces_c_star env (instantiate_at e v d) (instantiate_at e v' d)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (v0 : KExpr) (v0' : KExpr) (d : Nat) ",
                    "(liftclosed : RecEnvLiftClosed env) (hv : par_reduces_c_star env v0 v0') => ",
                    "par_reduces_c_star.rec env ",
                    "(fun (a : KExpr) (b : KExpr) (_ : par_reduces_c_star env a b) => ",
                    "par_reduces_c_star env (instantiate_at e a d) (instantiate_at e b d)) ",
                    "(fun (a : KExpr) => par_reduces_c_star.refl env (instantiate_at e a d)) ",
                    "(fun (a : KExpr) (amid : KExpr) (b : KExpr) ",
                    "(hstep : par_reduces_c env a amid) (_htail : par_reduces_c_star env amid b) ",
                    "(ih : par_reduces_c_star env (instantiate_at e amid d) (instantiate_at e b d)) => ",
                    "par_reduces_c_star_trans env ",
                    "(instantiate_at e a d) (instantiate_at e amid d) (instantiate_at e b d) ",
                    "(par_subst_refl_full_c env e a amid d liftclosed hstep) ih) ",
                    "v0 v0' hv"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Reflexive substitution congruence with a STAR value leg: under a lift-closed env, ",
                "v =>* v' substituted into a fixed term e at depth d gives inst e v d =>* inst e v' d. ",
                "par_reduces_c_star.rec on v =>* v', chaining par_subst_refl_full_c at each single value ",
                "step via par_reduces_c_star_trans. DerivedProved, zero axiom_deps. Part of #2859 (Increment F final assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.refl".to_string(),
                "par_reduces_c_star.rec".to_string(),
                "par_reduces_c_star_trans".to_string(),
                "par_subst_refl_full_c".to_string(),
                "RecEnvLiftClosed".to_string(),
                "instantiate_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_subst_body_full_c_star: substitution with a STAR term leg (value v
        // fixed, e =>* e'). par_reduces_c_star.rec on e =>* e': refl -> refl-star;
        // step e => emid =>* e' -> trans (par_subst_full_c at the single body step
        // e => emid with the value held refl: v => v via par_reduces_c.refl) (IH).
        self.add_definition(SpecDefinition {
            name: "par_subst_body_full_c_star".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr) (v : KExpr) (d : Nat), ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> par_reduces_c_star env e e' -> ",
                "par_reduces_c_star env (instantiate_at e v d) (instantiate_at e' v d)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e0 : KExpr) (e0' : KExpr) (v : KExpr) (d : Nat) ",
                    "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) ",
                    "(he : par_reduces_c_star env e0 e0') => ",
                    "par_reduces_c_star.rec env ",
                    "(fun (a : KExpr) (b : KExpr) (_ : par_reduces_c_star env a b) => ",
                    "par_reduces_c_star env (instantiate_at a v d) (instantiate_at b v d)) ",
                    "(fun (a : KExpr) => par_reduces_c_star.refl env (instantiate_at a v d)) ",
                    "(fun (a : KExpr) (amid : KExpr) (b : KExpr) ",
                    "(hstep : par_reduces_c env a amid) (_htail : par_reduces_c_star env amid b) ",
                    "(ih : par_reduces_c_star env (instantiate_at amid v d) (instantiate_at b v d)) => ",
                    "par_reduces_c_star_trans env ",
                    "(instantiate_at a v d) (instantiate_at amid v d) (instantiate_at b v d) ",
                    "(par_subst_full_c env a amid v v d hstep (par_reduces_c.refl env v) closed liftclosed) ih) ",
                    "e0 e0' he"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Substitution congruence with a STAR term leg (value held fixed): e =>* e' substituted with a ",
                "fixed value v at depth d gives inst e v d =>* inst e' v d. par_reduces_c_star.rec on e =>* e', ",
                "chaining par_subst_full_c at each single body step (value reduced reflexively via ",
                "par_reduces_c.refl) via par_reduces_c_star_trans. DerivedProved, zero axiom_deps. Part of #2859 ",
                "(Increment F final assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.refl".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.refl".to_string(),
                "par_reduces_c_star.rec".to_string(),
                "par_reduces_c_star_trans".to_string(),
                "par_subst_full_c".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "instantiate_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_subst_full_c_star: the FULLY star substitution (star legs on BOTH term
        // and value). Two phases composed by par_reduces_c_star_trans:
        //   (1) body phase  : inst e v d =>* inst e' v d  (par_subst_body_full_c_star)
        //   (2) value phase : inst e' v d =>* inst e' v' d (par_subst_refl_full_c_star)
        // This is the substitution lemma the structural contraction cross-cases of
        // the full diamond (#3) meet through (the body/arg sub-diamonds give _star legs).
        self.add_definition(SpecDefinition {
            name: "par_subst_full_c_star".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr) (v : KExpr) (v' : KExpr) (d : Nat), ",
                "par_reduces_c_star env e e' -> par_reduces_c_star env v v' -> RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_reduces_c_star env (instantiate_at e v d) (instantiate_at e' v' d)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (e' : KExpr) (v : KExpr) (v' : KExpr) (d : Nat) ",
                    "(he : par_reduces_c_star env e e') (hv : par_reduces_c_star env v v') ",
                    "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
                    "par_reduces_c_star_trans env ",
                    "(instantiate_at e v d) (instantiate_at e' v d) (instantiate_at e' v' d) ",
                    "(par_subst_body_full_c_star env e e' v d closed liftclosed he) ",
                    "(par_subst_refl_full_c_star env e' v v' d liftclosed hv)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "FULLY star substitution congruence: star legs on BOTH the term (e =>* e') and the value ",
                "(v =>* v') give inst e v d =>* inst e' v' d. Two phases (body then value) composed by ",
                "par_reduces_c_star_trans: par_subst_body_full_c_star (e =>* e' at value v) then ",
                "par_subst_refl_full_c_star (v =>* v' at term e'). The substitution lemma the structural ",
                "contraction cross-cases of the full single-step diamond meet through (body/arg sub-diamonds ",
                "give _star legs). DerivedProved, zero axiom_deps. Part of #2859 (Increment F final assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star_trans".to_string(),
                "par_subst_body_full_c_star".to_string(),
                "par_subst_refl_full_c_star".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "instantiate_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ============================================================
        // PHASE 3 — the non-iota x non-iota structural diagonals, landing in
        // par_strips_witness_c_star (the (beta,beta)/(app,beta) cases route the
        // contracted meet through par_subst_c, which is _star-valued, so the whole
        // structural diamond migrates to the star witness). Leaf helpers first.
        // ============================================================

        // par_strips_c_refl_left / _right: the (refl, _) and (_, refl) meets, at the
        // star-witness level. Given e =>* e2, join at e2.
        self.add_definition(SpecDefinition {
            name: "par_strips_c_refl_left".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e2 : KExpr), ",
                "par_reduces_c_star env e e2 -> par_strips_witness_c_star env e e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (e2 : KExpr) (h : par_reduces_c_star env e e2) => ",
                    "par_strips_witness_c_star.intro env e e2 e2 h (par_reduces_c_star.refl env e2)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The (refl, _) star-witness meet: given e =>* e2, join at e2 with the input on the left and ",
                "par_reduces_c_star.refl on the right. Closed term, no recursion. DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment F, Phase 3)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.refl".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_witness_c_star.intro".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "par_strips_c_refl_right".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e1 : KExpr), ",
                "par_reduces_c_star env e e1 -> par_strips_witness_c_star env e1 e"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (e1 : KExpr) (h : par_reduces_c_star env e e1) => ",
                    "par_strips_witness_c_star.intro env e1 e e1 (par_reduces_c_star.refl env e1) h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The (_, refl) star-witness meet: given e =>* e1, join at e1 with par_reduces_c_star.refl on ",
                "the left and the input on the right. Closed term, no recursion. DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment F, Phase 3)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.refl".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_witness_c_star.intro".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_witness_c_star_app: the (app, app) congruence combinator at the
        // star-witness level. From star-witnesses on head and argument, build the
        // star-witness on the application (meet app f3 a3, par_reduces_c_star_app each side).
        self.add_definition(SpecDefinition {
            name: "par_strips_witness_c_star_app".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (f1 : KExpr) (f2 : KExpr) (a1 : KExpr) (a2 : KExpr), ",
                "par_strips_witness_c_star env f1 f2 -> par_strips_witness_c_star env a1 a2 -> ",
                "par_strips_witness_c_star env (KExpr.app f1 a1) (KExpr.app f2 a2)"
            )
            .to_string(),
            value_src: Some(par_strips_witness_c_star_app_proof()),
            is_axiom: false,
            description: concat!(
                "The (app, app) congruence combinator at the star-witness level: from diamond star-witnesses on ",
                "head and argument, build the diamond star-witness on the application. Meet app f3 a3 with ",
                "par_reduces_c_star_app on each side. Closed via par_strips_witness_c_star.rec, no par_reduces_c ",
                "recursion. DerivedProved, zero axiom_deps. Part of #2859 (Increment F, Phase 3)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star_app".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_witness_c_star.intro".to_string(),
                "par_strips_witness_c_star.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_witness_c_star_{lam,pi,forall}: the (binder, binder) congruence
        // combinators at the star-witness level. Same shape as the app combinator,
        // using the matching _star binder congruence.
        for (name, head, star_cong, label) in [
            (
                "par_strips_witness_c_star_lam",
                "KExpr.lam",
                "par_reduces_c_star_lam",
                "lam",
            ),
            (
                "par_strips_witness_c_star_pi",
                "KExpr.pi",
                "par_reduces_c_star_pi",
                "pi",
            ),
            (
                "par_strips_witness_c_star_forall",
                "KExpr.forall_",
                "par_reduces_c_star_forall",
                "forall_",
            ),
        ] {
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    concat!(
                        "forall (env : RecEnv) (t1 : KExpr) (t2 : KExpr) (b1 : KExpr) (b2 : KExpr), ",
                        "par_strips_witness_c_star env t1 t2 -> par_strips_witness_c_star env b1 b2 -> ",
                        "par_strips_witness_c_star env ({head} t1 b1) ({head} t2 b2)"
                    ),
                    head = head,
                ),
                value_src: Some(par_strips_witness_c_star_binder_proof(head, star_cong)),
                is_axiom: false,
                description: format!(
                    concat!(
                        "The ({label}, {label}) congruence combinator at the star-witness level: from diamond ",
                        "star-witnesses on type/domain and body, build the diamond star-witness on the {label}. ",
                        "Meet {head} t3 b3 with {star_cong} on each side. Closed via par_strips_witness_c_star.rec, ",
                        "no par_reduces_c recursion. DerivedProved, zero axiom_deps. Part of #2859 (Increment F, Phase 3)."
                    ),
                    label = label,
                    head = head,
                    star_cong = star_cong,
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_reduces_c_star".to_string(),
                    star_cong.to_string(),
                    "par_strips_witness_c_star".to_string(),
                    "par_strips_witness_c_star.intro".to_string(),
                    "par_strips_witness_c_star.rec".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // par_strips_witness_c_star_let: the (let, let) congruence combinator at
        // the star-witness level (NEW with the let-promotion). From star-witnesses
        // on type, value and body, build the star-witness on the genuine let nodes.
        // Three nested par_strips_witness_c_star.rec projections meeting at
        // let_ t3 v3 b3 via par_reduces_c_star_let_cong on each side. The
        // 3-component sibling of the app/binder combinators; the meet the
        // let_cong-vs-let_cong diamond case lands in.
        self.add_definition(SpecDefinition {
            name: "par_strips_witness_c_star_let".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (t1 : KExpr) (t2 : KExpr) (v1 : KExpr) (v2 : KExpr) (b1 : KExpr) (b2 : KExpr), ",
                "par_strips_witness_c_star env t1 t2 -> par_strips_witness_c_star env v1 v2 -> ",
                "par_strips_witness_c_star env b1 b2 -> ",
                "par_strips_witness_c_star env (KExpr.let_ t1 v1 b1) (KExpr.let_ t2 v2 b2)"
            )
            .to_string(),
            value_src: Some(par_strips_witness_c_star_let_proof()),
            is_axiom: false,
            description: concat!(
                "The (let, let) congruence combinator at the star-witness level over the GENUINE KExpr.let_ ",
                "node: from diamond star-witnesses on type, value and body, build the diamond star-witness on ",
                "the let. Meet let_ t3 v3 b3 with par_reduces_c_star_let_cong on each side. Closed via three ",
                "nested par_strips_witness_c_star.rec, no par_reduces_c recursion. The 3-component sibling of ",
                "par_strips_witness_c_star_app/lam/pi; the let_cong-vs-let_cong diamond meet. DerivedProved, ",
                "zero axiom_deps. Part of the let-promotion batch B4."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star_let_cong".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_witness_c_star.intro".to_string(),
                "par_strips_witness_c_star.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_witness_c_star_proj: the (proj, proj) congruence combinator at
        // the star-witness level (proj/lit fragment rung) — the single-position
        // sibling of the app/binder combinators. From a star-witness on the
        // scrutinee, build the star-witness on the projection: meet proj s i m via
        // par_reduces_c_star_proj on each side. Closed via par_strips_witness_c_star.rec.
        self.add_definition(SpecDefinition {
            name: "par_strips_witness_c_star_proj".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (s : Name) (i : Nat) (sub1 : KExpr) (sub2 : KExpr), ",
                "par_strips_witness_c_star env sub1 sub2 -> ",
                "par_strips_witness_c_star env (KExpr.proj s i sub1) (KExpr.proj s i sub2)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (s : Name) (i : Nat) (sub1 : KExpr) (sub2 : KExpr) ",
                    "(w : par_strips_witness_c_star env sub1 sub2) => ",
                    "@par_strips_witness_c_star.rec env sub1 sub2 ",
                    "(fun (_w : par_strips_witness_c_star env sub1 sub2) => ",
                    "par_strips_witness_c_star env (KExpr.proj s i sub1) (KExpr.proj s i sub2)) ",
                    "(fun (m : KExpr) ",
                    "(p1 : par_reduces_c_star env sub1 m) (p2 : par_reduces_c_star env sub2 m) => ",
                    "par_strips_witness_c_star.intro env (KExpr.proj s i sub1) (KExpr.proj s i sub2) (KExpr.proj s i m) ",
                    "(par_reduces_c_star_proj env s i sub1 m p1) ",
                    "(par_reduces_c_star_proj env s i sub2 m p2)) ",
                    "w"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The (proj, proj) congruence combinator at the star-witness level: from a diamond ",
                "star-witness on the scrutinee, build the diamond star-witness on the projection. ",
                "Meet proj s i m with par_reduces_c_star_proj on each side. Closed via ",
                "par_strips_witness_c_star.rec, no par_reduces_c recursion. DerivedProved, zero ",
                "axiom_deps. Part of the proj/lit fragment rung."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star_proj".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_witness_c_star.intro".to_string(),
                "par_strips_witness_c_star.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ============================================================
        // FINAL ASSEMBLY #3a — par_strips_c_app_beta: the (app, beta) cross core at
        // the star-witness level (mirror of par_strips_bd_app_beta). The first side
        // is the syntactic redex app (lam Af bodyf) a0p; the second the contracted
        // instantiate bodyq argp. From the body sub-diamond wb and arg sub-diamond
        // wa, project both to their meets b3 / a3 and meet at instantiate b3 a3:
        //   left  : app (lam Af bodyf) a0p =>* instantiate b3 a3 (par_reduces_c_star_beta,
        //           domain Af held by refl-star)
        //   right : instantiate bodyq argp =>* instantiate b3 a3 (par_subst_full_c_star,
        //           the fully-star substitution at depth 0; instantiate = instantiate_at _ _ 0)
        // ============================================================
        self.add_definition(SpecDefinition {
            name: "par_strips_c_app_beta".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (Af : KExpr) (bodyf : KExpr) (a0p : KExpr) ",
                "(bodyq : KExpr) (argp : KExpr), ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_strips_witness_c_star env bodyf bodyq -> ",
                "par_strips_witness_c_star env a0p argp -> ",
                "par_strips_witness_c_star env (KExpr.app (KExpr.lam Af bodyf) a0p) (instantiate bodyq argp)"
            )
            .to_string(),
            value_src: Some(par_strips_c_app_beta_proof()),
            is_axiom: false,
            description: concat!(
                "The (app, beta) cross core for the FULL single-step diamond, at the star-witness level. The ",
                "first side is the syntactic redex app (lam Af bodyf) a0p, the second the contracted ",
                "instantiate bodyq argp. Project the body diamond wb and arg diamond wa to their meets b3 / a3; ",
                "meet at instantiate b3 a3: the first side beta-contracts there (par_reduces_c_star_beta, domain ",
                "Af held reflexively), the second transports through par_subst_full_c_star (the fully-star ",
                "substitution at depth 0). The full-relation, star-witness sibling of par_strips_bd_app_beta. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment F final assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.refl".to_string(),
                "par_reduces_c_star_beta".to_string(),
                "par_subst_full_c_star".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_witness_c_star.intro".to_string(),
                "par_strips_witness_c_star.rec".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_c_let_zeta: the (let_cong, zeta) cross core at the star-witness
        // level (NEW with the let-promotion — the zeta mirror of
        // par_strips_c_app_beta). The first side is the genuine let node
        // let_ tyf valf bodyf; the second the zeta-contracted instantiate bodyq
        // valq. From the body sub-diamond wb and value sub-diamond wv, project both
        // to their meets b3 / v3 and meet at instantiate b3 v3:
        //   left  : let_ tyf valf bodyf =>* instantiate b3 v3
        //           (par_reduces_c_star_let — congruence then fire zeta; the type
        //           annotation held by refl-star, exactly as beta drops the lam
        //           annotation)
        //   right : instantiate bodyq valq =>* instantiate b3 v3
        //           (par_subst_full_c_star at depth 0)
        // This is how the congruence side CATCHES UP with the zeta side — the
        // beta-vs-app mechanism transposed to the 7th constructor.
        self.add_definition(SpecDefinition {
            name: "par_strips_c_let_zeta".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (tyf : KExpr) (bodyf : KExpr) (valf : KExpr) ",
                "(bodyq : KExpr) (valq : KExpr), ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_strips_witness_c_star env bodyf bodyq -> ",
                "par_strips_witness_c_star env valf valq -> ",
                "par_strips_witness_c_star env (KExpr.let_ tyf valf bodyf) (instantiate bodyq valq)"
            )
            .to_string(),
            value_src: Some(par_strips_c_let_zeta_proof()),
            is_axiom: false,
            description: concat!(
                "The (let_cong, zeta) cross core for the FULL single-step diamond, at the star-witness level ",
                "— the zeta mirror of par_strips_c_app_beta over the GENUINE KExpr.let_ node. The first side ",
                "is the let node let_ tyf valf bodyf, the second the zeta-contracted instantiate bodyq valq. ",
                "Project the body diamond wb and value diamond wv to their meets b3 / v3; meet at ",
                "instantiate b3 v3: the first side zeta-contracts there (par_reduces_c_star_let, type ",
                "annotation held reflexively), the second transports through par_subst_full_c_star (depth 0). ",
                "How the let congruence side catches up with a zeta firing — the beta-vs-app mechanism ",
                "transposed. DerivedProved, zero axiom_deps. Part of the let-promotion batch B4."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.refl".to_string(),
                "par_reduces_c_star_let".to_string(),
                "par_subst_full_c_star".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_witness_c_star.intro".to_string(),
                "par_strips_witness_c_star.rec".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ============================================================
        // FINAL ASSEMBLY #3b — par_reduces_c_lam_inv_eq: Eq-DATA lam inversion over
        // par_reduces_c (single-step). The CPS par_reduces_c_lam_inv hides the reduct
        // shape inside the goal; the lam_meet (#3c) needs the reduct equality
        // Eq t (lam ty' body') AS DATA to transport a second derivation onto the same
        // reduct. Mirror of par_reduces_bd_lam_inv_eq + the iota arm (discharged
        // because a lam head is not a const head).
        // ============================================================
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_lam_inv_eq".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (ty : KExpr) (body : KExpr) (t : KExpr) (C : Type), ",
                "par_reduces_c env (KExpr.lam ty body) t -> ",
                "(forall (ty' : KExpr) (body' : KExpr), ",
                "Eq KExpr t (KExpr.lam ty' body') -> ",
                "par_reduces_c env ty ty' -> par_reduces_c env body body' -> C) -> ",
                "C"
            )
            .to_string(),
            value_src: Some(par_reduces_c_lam_inv_eq_proof()),
            is_axiom: false,
            description: concat!(
                "Eq-data shape recovery for a lam-headed par_reduces_c (single-step): from ",
                "par_reduces_c (lam ty body) t, hand the continuation the reduct equality Eq t (lam ty' body') ",
                "with ty => ty' and body => body'. The motive returns Eq e (lam ty body) -> Kont e' -> C with ",
                "Kont parameterized by the arm reduct, so the recursor substitutes the genuine reduct t. refl ",
                "folds in; lam is the match (Eq.refl reduct equation); app/pi-headed arms by no-confusion; the ",
                "iota arm by iota_step_head_none_absurd_type. The data the lam_meet (#3c) transports through. ",
                "DerivedProved via par_reduces_c.rec, zero axiom_deps. Part of #2859 (Increment F final assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.rec".to_string(),
                "par_reduces_c.refl".to_string(),
                "iota_step".to_string(),
                "iota_step_head_none_absurd_type".to_string(),
                "lam_inj_fst".to_string(),
                "lam_inj_snd".to_string(),
                "app_ne_lam".to_string(),
                "pi_ne_lam".to_string(),
                "let_ne_lam".to_string(),
                "instantiate".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "Eq.substType".to_string(),
                "Eq.subst".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ============================================================
        // FINAL ASSEMBLY #3c — par_reduces_c_star_lam_inv_eq: the MULTI-STEP Eq-data
        // lam inversion. From par_reduces_c_star (lam ty body) t recover t = lam ty'
        // body' with ty =>* ty' and body =>* body'. par_reduces_c_star.rec with an
        // accumulator motive (source = lam ty0 body0); the step arm single-step
        // inverts the head via par_reduces_c_lam_inv_eq (#3b) and prepends the steps
        // to the IH's accumulated star congruences via par_reduces_c_star.step. The
        // _star analogue the star-witness lam_meet (#3d) needs.
        // ============================================================
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_star_lam_inv_eq".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (ty : KExpr) (body : KExpr) (t : KExpr) (C : Type), ",
                "par_reduces_c_star env (KExpr.lam ty body) t -> ",
                "(forall (ty' : KExpr) (body' : KExpr), ",
                "Eq KExpr t (KExpr.lam ty' body') -> ",
                "par_reduces_c_star env ty ty' -> par_reduces_c_star env body body' -> C) -> ",
                "C"
            )
            .to_string(),
            value_src: Some(par_reduces_c_star_lam_inv_eq_proof()),
            is_axiom: false,
            description: concat!(
                "Multi-step Eq-data lam inversion: from par_reduces_c_star (lam ty body) t recover ",
                "t = lam ty' body' with ty =>* ty' and body =>* body'. par_reduces_c_star.rec with an ",
                "accumulator motive carrying the source-is-lam equation: the refl arm folds in refl-star ",
                "congruences; the step arm single-step inverts the head via par_reduces_c_lam_inv_eq, then ",
                "applies the IH (now with a known-lam intermediate) and prepends the single steps to the ",
                "accumulated star congruences via par_reduces_c_star.step. The _star analogue of ",
                "par_reduces_c_lam_inv_eq the star-witness lam_meet needs. DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment F final assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.refl".to_string(),
                "par_reduces_c_star.step".to_string(),
                "par_reduces_c_star.rec".to_string(),
                "par_reduces_c_lam_inv_eq".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ============================================================
        // FINAL ASSEMBLY #3d — par_strips_witness_c_star_lam_meet: body sub-meet
        // recovery at the star-witness level. From a star-witness on two lambdas
        // par_strips_witness_c_star (lam t1 b1) (lam t2 b2), recover the body diamond
        // par_strips_witness_c_star b1 b2. Project to the common reduct g3, Eq-invert
        // both star legs (par_reduces_c_star_lam_inv_eq) to lam shapes, identify the
        // body meet via lam_inj_snd + Eq.trans, and meet the bodies there. Mirror of
        // par_strips_witness_bd_lam_meet at the _star level.
        // ============================================================
        self.add_definition(SpecDefinition {
            name: "par_strips_witness_c_star_lam_meet".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (t1 : KExpr) (t2 : KExpr) (b1 : KExpr) (b2 : KExpr), ",
                "par_strips_witness_c_star env (KExpr.lam t1 b1) (KExpr.lam t2 b2) -> ",
                "par_strips_witness_c_star env b1 b2"
            )
            .to_string(),
            value_src: Some(par_strips_witness_c_star_lam_meet_proof()),
            is_axiom: false,
            description: concat!(
                "Body sub-meet recovery at the star-witness level: from a diamond witness on two lambdas ",
                "par_strips_witness_c_star (lam t1 b1) (lam t2 b2), recover the body diamond ",
                "par_strips_witness_c_star b1 b2. Projects to the common reduct g3, Eq-inverts both star legs ",
                "(par_reduces_c_star_lam_inv_eq) to lam shapes, identifies the body meet via lam_inj_snd + ",
                "Eq.trans, and meets the bodies there. The full-relation, star-witness sibling of ",
                "par_strips_witness_bd_lam_meet. DerivedProved, zero axiom_deps. Part of #2859 (Increment F final assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star_lam_inv_eq".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_witness_c_star.intro".to_string(),
                "par_strips_witness_c_star.rec".to_string(),
                "lam_inj_snd".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ============================================================
        // FINAL ASSEMBLY #3e — par_strips_c_subst_join: the contraction MEET
        // combinator (mirror of par_strips_bd_proof's `mk_join`). From a body
        // sub-diamond wb : par_strips_witness_c_star lb rb and an arg sub-diamond
        // wa : par_strips_witness_c_star la ra, build the diamond on the two
        // instantiations par_strips_witness_c_star (instantiate lb la) (instantiate rb
        // ra): project both to meets b3 / a3, meet at instantiate b3 a3 via
        // par_subst_full_c_star on each side. This is the (beta,beta) and (let_,*)
        // cross-case meeting point.
        // ============================================================
        self.add_definition(SpecDefinition {
            name: "par_strips_c_subst_join".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (lb : KExpr) (rb : KExpr) (la : KExpr) (ra : KExpr), ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_strips_witness_c_star env lb rb -> ",
                "par_strips_witness_c_star env la ra -> ",
                "par_strips_witness_c_star env (instantiate lb la) (instantiate rb ra)"
            )
            .to_string(),
            value_src: Some(par_strips_c_subst_join_proof()),
            is_axiom: false,
            description: concat!(
                "The contraction MEET combinator at the star-witness level (mirror of par_strips_bd_proof's ",
                "mk_join): from a body sub-diamond on lb/rb and an arg sub-diamond on la/ra, build the diamond ",
                "on the two instantiations instantiate lb la / instantiate rb ra. Project both to meets b3 / a3, ",
                "meet at instantiate b3 a3 via par_subst_full_c_star on each side (at depth 0). The (beta,beta) ",
                "and (let_,*) cross-case meeting point. DerivedProved, zero axiom_deps. Part of #2859 (Increment F final assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c_star".to_string(),
                "par_subst_full_c_star".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_witness_c_star.intro".to_string(),
                "par_strips_witness_c_star.rec".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ============================================================
        // FINAL ASSEMBLY #3 — par_strips_c_struct_lam: the FULL single-step diamond
        // for a LAM-headed source (the simplest closed structural recursion that
        // exercises the lam diagonal + lam_meet machinery without the
        // minimal_or_inner guard, since a lam head is never an iota redex). From
        // par_reduces_c env (lam ty body) e1 and par_reduces_c env (lam ty body) e2,
        // both legs must be lam congruences (lam head, no iota possible). Invert both
        // via par_reduces_c_lam_inv to lam reducts, recurse on the sub-diamonds for
        // ty and body (supplied by the caller's sub-witnesses), assemble via
        // par_strips_witness_c_star_lam. This is the guard-FREE structural diamond
        // fragment — the binder-headed case where the minimal_or_inner wall (which
        // only arises for app-headed iota redexes) does not appear.
        // ============================================================
        self.add_definition(SpecDefinition {
            name: "par_strips_c_struct_lam".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (ty : KExpr) (body : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "par_reduces_c env (KExpr.lam ty body) e1 -> par_reduces_c env (KExpr.lam ty body) e2 -> ",
                "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env ty s1 -> par_reduces_c env ty s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env body s1 -> par_reduces_c env body s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "par_strips_witness_c_star env e1 e2"
            )
            .to_string(),
            value_src: Some(par_strips_c_struct_lam_proof()),
            is_axiom: false,
            description: concat!(
                "The FULL single-step diamond for a lam-headed source: both legs of par_reduces_c (lam ty body) ",
                "are necessarily lam congruences (a lam head is never an iota redex, so the minimal_or_inner ",
                "guard never arises). Invert both legs via par_reduces_c_lam_inv to lam reducts (lam s1 s1b / ",
                "lam s2 s2b), apply the caller-supplied ty- and body-sub-diamonds, and assemble via ",
                "par_strips_witness_c_star_lam. The guard-FREE structural diamond fragment, the binder-headed ",
                "case the app-headed iota wall does not touch. DerivedProved, zero axiom_deps. Part of #2859 ",
                "(Increment F final assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c_lam_inv".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_witness_c_star_lam".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_c_struct_proj: the FULL single-step diamond for a proj-headed
        // source (proj/lit fragment rung) — the single-position sibling of
        // par_strips_c_struct_lam. A proj head is never an iota redex, so both legs
        // of par_reduces_c (proj s i sub) are necessarily proj congruences. Invert
        // both via par_reduces_c_proj_inv, apply the caller-supplied scrutinee
        // sub-diamond, assemble via par_strips_witness_c_star_proj.
        self.add_definition(SpecDefinition {
            name: "par_strips_c_struct_proj".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (s : Name) (i : Nat) (sub : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "par_reduces_c env (KExpr.proj s i sub) e1 -> par_reduces_c env (KExpr.proj s i sub) e2 -> ",
                "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env sub s1 -> par_reduces_c env sub s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "par_strips_witness_c_star env e1 e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (s : Name) (i : Nat) (sub : KExpr) (e1 : KExpr) (e2 : KExpr) ",
                    "(h1 : par_reduces_c env (KExpr.proj s i sub) e1) ",
                    "(h2 : par_reduces_c env (KExpr.proj s i sub) e2) ",
                    "(dsub : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env sub s1 -> par_reduces_c env sub s2 -> ",
                    "par_strips_witness_c_star env s1 s2) => ",
                    "par_reduces_c_proj_inv env s i sub e1 ",
                    "(fun (x : KExpr) => par_strips_witness_c_star env x e2) ",
                    "h1 ",
                    "(fun (sub1 : KExpr) (hsub1 : par_reduces_c env sub sub1) => ",
                    "par_reduces_c_proj_inv env s i sub e2 ",
                    "(fun (y : KExpr) => par_strips_witness_c_star env (KExpr.proj s i sub1) y) ",
                    "h2 ",
                    "(fun (sub2 : KExpr) (hsub2 : par_reduces_c env sub sub2) => ",
                    "par_strips_witness_c_star_proj env s i sub1 sub2 (dsub sub1 sub2 hsub1 hsub2)))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The FULL single-step diamond for a proj-headed source: both legs of ",
                "par_reduces_c (proj s i sub) are necessarily proj congruences (a proj head is ",
                "never an iota redex). Invert both via par_reduces_c_proj_inv, apply the ",
                "caller-supplied scrutinee sub-diamond, assemble via par_strips_witness_c_star_proj. ",
                "The single-position sibling of par_strips_c_struct_lam. DerivedProved, zero ",
                "axiom_deps. Part of the proj/lit fragment rung."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c_proj_inv".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_witness_c_star_proj".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_c_struct_pi / _forall: the pi- and forall_-headed structural
        // diamonds, the guard-free binder-headed siblings of par_strips_c_struct_lam.
        // Both pi and forall_ heads are never iota redexes (const-head = none), so the
        // minimal_or_inner guard never arises. Same shape: invert both legs via the
        // matching pi/forall inversion, apply the caller-supplied dom/body sub-diamonds,
        // assemble via the matching binder diagonal. (forall_ is the reducible alias of
        // pi, so par_reduces_c_pi_inv recovers a pi-shaped reduct in both — the inversion
        // and diagonal are chosen to match the source head.)
        for (name, head, inv, diag, label) in [
            (
                "par_strips_c_struct_pi",
                "KExpr.pi",
                "par_reduces_c_pi_inv",
                "par_strips_witness_c_star_pi",
                "pi",
            ),
            (
                "par_strips_c_struct_forall",
                "KExpr.forall_",
                "par_reduces_c_forall_inv",
                "par_strips_witness_c_star_forall",
                "forall_",
            ),
        ] {
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    concat!(
                        "forall (env : RecEnv) (dom : KExpr) (body : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                        "par_reduces_c env ({head} dom body) e1 -> par_reduces_c env ({head} dom body) e2 -> ",
                        "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env dom s1 -> par_reduces_c env dom s2 -> ",
                        "par_strips_witness_c_star env s1 s2) -> ",
                        "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env body s1 -> par_reduces_c env body s2 -> ",
                        "par_strips_witness_c_star env s1 s2) -> ",
                        "par_strips_witness_c_star env e1 e2"
                    ),
                    head = head,
                ),
                value_src: Some(par_strips_c_struct_binder_proof(head, inv, diag)),
                is_axiom: false,
                description: format!(
                    concat!(
                        "The FULL single-step diamond for a {label}-headed source: both legs are necessarily ",
                        "{label} congruences (a {label} head is never an iota redex, so the minimal_or_inner ",
                        "guard never arises). Invert both legs via {inv} to {label} reducts, apply the ",
                        "caller-supplied dom- and body-sub-diamonds, assemble via {diag}. The guard-free ",
                        "binder-headed sibling of par_strips_c_struct_lam. DerivedProved, zero axiom_deps. ",
                        "Part of #2859 (Increment F final assembly)."
                    ),
                    label = label,
                    inv = inv,
                    diag = diag,
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_reduces_c".to_string(),
                    inv.to_string(),
                    "par_strips_witness_c_star".to_string(),
                    diag.to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // ============================================================
        // FINAL ASSEMBLY #3 (app head) — par_strips_c_app_struct: the FULL
        // single-step diamond for an APP-CONGRUENCE first leg (app f a => app f' a')
        // against an ARBITRARY second leg. This is the app-headed sibling of the
        // binder structural diamonds, but here the iota wall surfaces: the app head
        // CAN be an iota redex, so the (app, iota) second-leg case needs the
        // minimal_or_inner guard (routed to the landed par_strips_iota_target_c).
        // Parameterized by the f- and a-sub-diamonds (like the binder versions),
        // plus the guard. Second leg inverted via par_reduces_c_app_inv:
        //   kcong (app, app)  -> par_strips_witness_c_star_app on the sub-diamonds
        //   kbeta (app, beta) -> recover f' = lam Af bodyf (par_reduces_c_lam_inv_eq),
        //                        body meet via the f-sub-diamond + lam_meet, arg meet
        //                        via the a-sub-diamond, assemble via par_strips_c_app_beta
        //   kiota (app, iota) -> par_strips_iota_target_c under the guard
        // ============================================================
        self.add_definition(SpecDefinition {
            name: "par_strips_c_app_struct".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (f : KExpr) (a : KExpr) (f' : KExpr) (a' : KExpr) (e2 : KExpr), ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_reduces_c env f f' -> par_reduces_c env a a' -> ",
                "par_reduces_c env (KExpr.app f a) e2 -> ",
                "minimal_or_inner env (KExpr.app f a) (KExpr.app f' a') -> ",
                "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env f s1 -> par_reduces_c env f s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env a s1 -> par_reduces_c env a s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "par_strips_witness_c_star env (KExpr.app f' a') e2"
            )
            .to_string(),
            value_src: Some(par_strips_c_app_struct_proof()),
            is_axiom: false,
            description: concat!(
                "The FULL single-step diamond for an app-congruence first leg (app f a => app f' a') against an ",
                "arbitrary second leg. The app-headed sibling of the binder structural diamonds, where the iota ",
                "wall surfaces: an app head CAN be an iota redex, so the (app, iota) second-leg case is routed to ",
                "the landed par_strips_iota_target_c under the minimal_or_inner guard. Parameterized by the f- ",
                "and a-sub-diamonds plus the guard. Second leg inverted via par_reduces_c_app_inv: the (app,app) ",
                "kcong arm meets via par_strips_witness_c_star_app on the sub-diamonds; the (app,beta) kbeta arm ",
                "recovers f' = lam Af bodyf (par_reduces_c_lam_inv_eq), takes the body meet via the f-sub-diamond ",
                "+ par_strips_witness_c_star_lam_meet and the arg meet via the a-sub-diamond, and assembles via ",
                "par_strips_c_app_beta; the (app,iota) kiota arm routes to par_strips_iota_target_c. DerivedProved, ",
                "zero axiom_deps. Part of #2859 (Increment F final assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.app".to_string(),
                "par_reduces_c.lam".to_string(),
                "par_reduces_c_app_inv".to_string(),
                "par_reduces_c_lam_inv_eq".to_string(),
                "minimal_or_inner".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_witness_c_star_app".to_string(),
                "par_strips_witness_c_star_lam_meet".to_string(),
                "par_strips_c_app_beta".to_string(),
                "par_strips_iota_target_c".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "iota_step".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_par_strips_c_full()?;

        Ok(())
    }

    /// The FULL single-step confluence diamond `par_strips_c_full` (Increment F
    /// capstone, #2859) and the genuinely-new (b2) over-application join it routes
    /// the iota×app-structural case through (using the strong-induction sub-diamond
    /// instead of the `minimal_or_inner` guard). No axiom.
    fn add_par_strips_c_full(&mut self) -> Result<(), SpecError> {
        // par_strips_c_iota_app_b2_over — THE (b2) OVER-APPLICATION JOIN, guard-free.
        // When (app f a) is an iota redex (=> e1) whose head f is ITSELF an iota
        // redex (iota_reduct f = some f1), the over-application identity forces
        // e1 = app f1 a (iota_reduct_app_some + determinism). f1 and f' are both
        // par-reducts of f (f ⇒ f1 by iota, f ⇒ f' given), so the caller-supplied
        // f-sub-diamond joins them; a/a' join via the a-sub-diamond; lift via
        // par_strips_witness_c_star_app. This is the (b2) case the guard excluded —
        // closed here by the strong-induction sub-diamonds, NOT the guard.
        self.add_definition(SpecDefinition {
            name: "par_strips_c_iota_app_b2_over".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (f : KExpr) (a : KExpr) (e1 : KExpr) (f1 : KExpr) (f' : KExpr) (a' : KExpr), ",
                "Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1) -> ",
                "Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f1) -> ",
                "par_reduces_c env f f' -> par_reduces_c env a a' -> ",
                "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env f s1 -> par_reduces_c env f s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env a s1 -> par_reduces_c env a s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "par_strips_witness_c_star env e1 (KExpr.app f' a')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (f : KExpr) (a : KExpr) (e1 : KExpr) (f1 : KExpr) (f' : KExpr) (a' : KExpr) ",
                    "(h_e1 : Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1)) ",
                    "(h_f : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f1)) ",
                    "(hf : par_reduces_c env f f') (ha : par_reduces_c env a a') ",
                    "(df : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env f s1 -> par_reduces_c env f s2 -> ",
                    "par_strips_witness_c_star env s1 s2) ",
                    "(da : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env a s1 -> par_reduces_c env a s2 -> ",
                    "par_strips_witness_c_star env s1 s2) => ",
                    // e1 = app f1 a (over-application identity + determinism). Transport
                    // the join on (app f1 a) back to e1.
                    "Eq.substType KExpr ",
                    "(fun (x : KExpr) => par_strips_witness_c_star env x (KExpr.app f' a')) ",
                    "(KExpr.app f1 a) e1 ",
                    "(Eq.symm KExpr e1 (KExpr.app f1 a) ",
                    "(iota_step_deterministic env (KExpr.app f a) e1 (KExpr.app f1 a) h_e1 ",
                    "(iota_reduct_app_some env f a f1 h_f))) ",
                    // join (app f1 a) (app f' a') = lift of f-diamond(f1,f') and a-diamond(a,a').
                    "(par_strips_witness_c_star_app env f1 f' a a' ",
                    // f-sub-diamond: f ⇒ f1 (iota: iota_step env f f1 IS h_f) and f ⇒ f' (hf).
                    "(df f1 f' (par_reduces_c.iota env f f1 h_f) hf) ",
                    // a-sub-diamond: a ⇒ a (refl) and a ⇒ a' (ha).
                    "(da a a' (par_reduces_c.refl env a) ha))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "THE (b2) over-application join of the FULL diamond, guard-free: when (app f a) is an iota redex ",
                "(=> e1) whose head f is itself an iota redex (iota_reduct f = some f1), the over-application ",
                "identity (iota_reduct_app_some) + determinism force e1 = app f1 a; the caller-supplied ",
                "f-sub-diamond joins f1 (the iota reduct) and f' (the structural reduct), the a-sub-diamond joins ",
                "a and a', and par_strips_witness_c_star_app lifts. The (b2) case the minimal_or_inner guard ",
                "excluded, here closed by the strong-induction sub-diamonds instead. DerivedProved, zero ",
                "axiom_deps. Part of #2859 (Increment F capstone)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_reduct".to_string(),
                "iota_reduct_app_some".to_string(),
                "iota_step_deterministic".to_string(),
                "par_reduces_c".to_string(),
                "par_reduces_c.iota".to_string(),
                "par_reduces_c.refl".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_witness_c_star_app".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_c_iota_app_full — THE GUARD-FREE (iota, app-structural) join,
        // the capstone core. When (app f a) is an iota redex (=> e1) and the other
        // leg is the app congruence (f ⇒ f', a ⇒ a'), the two join WITHOUT the
        // minimal_or_inner CPS guard, dispatching on iota_reduct f:
        //   some f1 -> (b2) over-application: par_strips_c_iota_app_b2_over (the IH
        //     sub-diamonds join f1/f' and a/a'); the GENUINELY-NEW case the guard
        //     excluded, here closed by the strong-induction sub-diamonds.
        //   none    -> (a) minimal: par_strips_c_iota_app_minimal. This needs
        //     iota_reduct a = none (the major premise a is constructor-headed, hence
        //     not itself a recursor redex). That fact = "constructors are disjoint
        //     from recursors in the env" is a RecEnv well-formedness property with NO
        //     landed lemma and NOT derivable from the iota witnesses alone (it would
        //     need recmeta_for env cname = none for the constructor cname). It is
        //     therefore carried as the SINGLE isolated hypothesis hmaj_nr, conditional
        //     on the minimal branch (iota_reduct f = none -> iota_reduct a = none).
        //     Every other part of the (iota,app) diamond is proven constructively.
        self.add_definition(SpecDefinition {
            name: "par_strips_c_iota_app_full".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (f : KExpr) (a : KExpr) (e1 : KExpr) (f' : KExpr) (a' : KExpr), ",
                "Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1) -> ",
                "(Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr) -> ",
                "Eq (OptionType KExpr) (iota_reduct env a) (OptionType.none KExpr)) -> ",
                "par_reduces_c env f f' -> par_reduces_c env a a' -> ",
                "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env f s1 -> par_reduces_c env f s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env a s1 -> par_reduces_c env a s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "par_strips_witness_c_star env e1 (KExpr.app f' a')"
            )
            .to_string(),
            value_src: Some(par_strips_c_iota_app_full_proof()),
            is_axiom: false,
            description: concat!(
                "THE guard-free (iota, app-structural) join — the Increment F capstone core. When (app f a) is ",
                "an iota redex (=> e1) and the other leg is an app congruence (f ⇒ f', a ⇒ a'), the two join ",
                "WITHOUT the minimal_or_inner CPS guard, dispatching (OptionType.rec) on iota_reduct f: the some ",
                "arm is the genuinely-NEW (b2) over-application case, closed by par_strips_c_iota_app_b2_over from ",
                "the strong-induction f/a sub-diamonds (the case the guard excluded); the none arm is the (a) ",
                "minimal join (par_strips_c_iota_app_minimal), whose one residual side-condition — iota_reduct a = ",
                "none, i.e. the major premise a (constructor-headed) is not itself a recursor redex — is the only ",
                "fact NOT constructively derivable here (it is a RecEnv constructor/recursor-disjointness property ",
                "with no landed lemma), so it is carried as the single isolated conditional hypothesis hmaj_nr. ",
                "DerivedProved (zero axiom_deps); the disjointness is an explicit typed hypothesis, not an axiom. ",
                "Part of #2859 (Increment F capstone)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_reduct".to_string(),
                "iota_reduct_some_inv_type".to_string(),
                "par_strips_c_iota_app_b2_over".to_string(),
                "par_strips_c_iota_app_minimal".to_string(),
                "par_reduces_c".to_string(),
                "par_strips_witness_c_star".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "kapp_fn_app".to_string(),
                "Eq.refl".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_c_iota_app_disjoint — par_strips_c_iota_app_full with its
        // conditional hypothesis hmaj_nr DISCHARGED from the env's constructor/
        // recursor-disjointness interface (RecEnvCtorRecDisjoint). The hmaj_nr slot
        // (iota_reduct f = none -> iota_reduct a = none) is filled by iota_app_major_
        // not_rec, which derives iota_reduct a = none from the disjointness fact + the
        // boundary location of the major premise. The full (iota,app) join with NO
        // residual side-condition beyond the faithful interface — exactly what the
        // strong-induction assembly of par_strips_c_full consumes for the iota arm.
        self.add_definition(SpecDefinition {
            name: "par_strips_c_iota_app_disjoint".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (f : KExpr) (a : KExpr) (e1 : KExpr) (f' : KExpr) (a' : KExpr), ",
                "RecEnvCtorRecDisjoint env -> ",
                "Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1) -> ",
                "par_reduces_c env f f' -> par_reduces_c env a a' -> ",
                "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env f s1 -> par_reduces_c env f s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env a s1 -> par_reduces_c env a s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "par_strips_witness_c_star env e1 (KExpr.app f' a')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (f : KExpr) (a : KExpr) (e1 : KExpr) (f' : KExpr) (a' : KExpr) ",
                    "(disjoint : RecEnvCtorRecDisjoint env) ",
                    "(h_e1 : Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1)) ",
                    "(hf : par_reduces_c env f f') (ha : par_reduces_c env a a') ",
                    "(df : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env f s1 -> par_reduces_c env f s2 -> ",
                    "par_strips_witness_c_star env s1 s2) ",
                    "(da : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env a s1 -> par_reduces_c env a s2 -> ",
                    "par_strips_witness_c_star env s1 s2) => ",
                    "par_strips_c_iota_app_full env f a e1 f' a' h_e1 ",
                    "(fun (hfn : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)) => ",
                    "iota_app_major_not_rec env f a e1 disjoint h_e1 hfn) ",
                    "hf ha df da"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The full (iota, app-structural) join with the conditional hypothesis hmaj_nr discharged from the ",
                "env's constructor/recursor-disjointness interface RecEnvCtorRecDisjoint: par_strips_c_iota_app_full ",
                "applied with hmaj_nr := iota_app_major_not_rec (which derives iota_reduct a = none for the ",
                "constructor-headed major premise). No residual side-condition beyond the faithful interface; this is ",
                "the iota-arm join the strong-induction assembly of par_strips_c_full consumes. DerivedProved, zero ",
                "axiom_deps. Part of #2859 (Increment F capstone)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_strips_c_iota_app_full".to_string(),
                "iota_app_major_not_rec".to_string(),
                "RecEnvCtorRecDisjoint".to_string(),
                "iota_reduct".to_string(),
                "par_reduces_c".to_string(),
                "par_strips_witness_c_star".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_iota_app_source_disjoint — THE GUARD-FREE iota-source diamond at
        // an app source. When the FIRST leg fires an iota on (app f a) (=> e1) and the
        // SECOND leg is an arbitrary par_reduces_c step (app f a => e2), the two join
        // at the star-legged witness WITHOUT the minimal_or_inner guard, dispatching on
        // the second leg via par_reduces_c_app_inv:
        //   kcong (e2 = app f' a'): par_strips_c_iota_app_disjoint (the guard-free
        //     (iota,app) join; df/da supply the sub-diamonds, the disjointness interface
        //     discharges the major-not-redex side-condition).
        //   kbeta (f = lam A body): IMPOSSIBLE — a lam-headed app is not an iota redex
        //     (kexpr_const_name (kapp_fn (app (lam ..) a)) = none, definitionally), so
        //     hiota is absurd (iota_step_head_none_absurd_type).
        //   kiota (e2 from iota_step (app f a) => t0): determinism — par_strips_iota_
        //     iota_c gives a single-step witness, lifted to star by _to_star.
        // This is the iota arm the full single-step diamond consumes: guard-free, with
        // only the faithful RecEnvCtorRecDisjoint interface + the sub-diamonds.
        self.add_definition(SpecDefinition {
            name: "par_strips_iota_app_source_disjoint".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (f : KExpr) (a : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "RecEnvCtorRecDisjoint env -> ",
                "iota_step env (KExpr.app f a) e1 -> ",
                "par_reduces_c env (KExpr.app f a) e2 -> ",
                "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env f s1 -> par_reduces_c env f s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env a s1 -> par_reduces_c env a s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "par_strips_witness_c_star env e1 e2"
            )
            .to_string(),
            value_src: Some(par_strips_iota_app_source_disjoint_proof()),
            is_axiom: false,
            description: concat!(
                "The GUARD-FREE iota-source diamond at an app source: a first-leg iota on (app f a) (=> e1) ",
                "and an arbitrary second leg (app f a => e2) join at the star-legged witness WITHOUT the ",
                "minimal_or_inner guard, by inverting the second leg via par_reduces_c_app_inv — kcong routes ",
                "to par_strips_c_iota_app_disjoint (the guard-free (iota,app) join), kbeta is impossible (a ",
                "lam-headed app is not an iota redex; iota_step_head_none_absurd_type), kiota closes by ",
                "determinism (par_strips_iota_iota_c + _to_star). The iota arm the full single-step diamond ",
                "consumes; only the faithful RecEnvCtorRecDisjoint interface + the f/a sub-diamonds. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment F capstone)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c_app_inv".to_string(),
                "par_strips_c_iota_app_disjoint".to_string(),
                "iota_step".to_string(),
                "iota_step_head_none_absurd_type".to_string(),
                "par_strips_iota_iota_c".to_string(),
                "par_strips_witness_c_to_star".to_string(),
                "par_strips_witness_c_star".to_string(),
                "RecEnvCtorRecDisjoint".to_string(),
                "instantiate".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "kapp_fn_app".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_c_app_struct_disjoint — THE GUARD-FREE app-structural diamond.
        // When the FIRST leg is an app congruence (app f a => app f' a') and the SECOND
        // is arbitrary (app f a => e2), the two join WITHOUT the minimal_or_inner guard,
        // inverting the second leg via par_reduces_c_app_inv:
        //   kcong: the diagonal on the f/a sub-diamonds (par_strips_witness_c_star_app).
        //   kbeta: f = lam — the (app,beta) cross via par_strips_c_app_beta + lam_meet
        //     (identical to the guarded version; the guard never participated here).
        //   kiota: the second leg fires an iota — route to the GUARD-FREE iota-source
        //     diamond par_strips_iota_app_source_disjoint (symmetrized), NOT the guarded
        //     par_strips_iota_target_c. This is the only arm that changes.
        // The guard-free app diamond the full single-step assembly consumes for an
        // app-congruence first leg.
        self.add_definition(SpecDefinition {
            name: "par_strips_c_app_struct_disjoint".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (f : KExpr) (a : KExpr) (f' : KExpr) (a' : KExpr) (e2 : KExpr), ",
                "RecEnvCtorRecDisjoint env -> RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_reduces_c env f f' -> par_reduces_c env a a' -> ",
                "par_reduces_c env (KExpr.app f a) e2 -> ",
                "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env f s1 -> par_reduces_c env f s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env a s1 -> par_reduces_c env a s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "par_strips_witness_c_star env (KExpr.app f' a') e2"
            )
            .to_string(),
            value_src: Some(par_strips_c_app_struct_disjoint_proof()),
            is_axiom: false,
            description: concat!(
                "The GUARD-FREE app-structural diamond: a first-leg app congruence (app f a => app f' a') and ",
                "an arbitrary second leg (app f a => e2) join WITHOUT the minimal_or_inner guard. Inverts the ",
                "second leg via par_reduces_c_app_inv — kcong is the f/a-sub-diamond diagonal, kbeta is the ",
                "(app,beta) cross (par_strips_c_app_beta + lam_meet, unchanged from the guarded version), and ",
                "kiota routes to the guard-free par_strips_iota_app_source_disjoint (symmetrized) instead of the ",
                "guarded par_strips_iota_target_c. The app diamond the full single-step assembly consumes for an ",
                "app-congruence first leg. DerivedProved, zero axiom_deps. Part of #2859 (Increment F capstone)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.app".to_string(),
                "par_reduces_c.lam".to_string(),
                "par_reduces_c_app_inv".to_string(),
                "par_reduces_c_lam_inv_eq".to_string(),
                "par_strips_witness_c_star_app".to_string(),
                "par_strips_witness_c_star_lam_meet".to_string(),
                "par_strips_witness_c_star_symm".to_string(),
                "par_strips_c_app_beta".to_string(),
                "par_strips_iota_app_source_disjoint".to_string(),
                "par_strips_witness_c_star".to_string(),
                "RecEnvCtorRecDisjoint".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "iota_step".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_c_beta_source — THE beta-source diamond (beta ONLY since the
        // let-promotion: the genuinely let-headed zeta arm now routes to its own
        // par_strips_c_zeta_source). When the FIRST leg is a beta contraction
        // (app (lam A body) arg => instantiate body' arg') and the SECOND is arbitrary
        // (app (lam A body) arg => e2), the two join by inverting the second leg via
        // par_reduces_c_app_inv (f := lam A body, a := arg):
        //   kcong: the second leg is an app congruence whose head reduces a lam; recover
        //     f2 = lam Af bodyf (par_reduces_c_lam_inv_eq) and join via par_strips_c_app_
        //     beta (symmetrized) — the (beta, app-cong-to-lam) cross.
        //   kbeta: both legs contract the SAME redex — par_strips_c_subst_join on the
        //     body/arg sub-meets (the (beta,beta) join; lam injectivity aligns body0).
        //   kiota: impossible — a lam-headed app is not an iota redex
        //     (iota_step_head_none_absurd_type). No disjointness interface needed.
        self.add_definition(SpecDefinition {
            name: "par_strips_c_beta_source".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) ",
                "(arg : KExpr) (arg' : KExpr) (e2 : KExpr), ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_reduces_c env A A' -> par_reduces_c env body body' -> par_reduces_c env arg arg' -> ",
                "par_reduces_c env (KExpr.app (KExpr.lam A body) arg) e2 -> ",
                "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env body s1 -> par_reduces_c env body s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env arg s1 -> par_reduces_c env arg s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "par_strips_witness_c_star env (instantiate body' arg') e2"
            )
            .to_string(),
            value_src: Some(par_strips_c_beta_source_proof()),
            is_axiom: false,
            description: concat!(
                "The beta-source diamond (beta only — the genuinely let-headed zeta source has its own ",
                "par_strips_c_zeta_source since the let-promotion): a first-leg beta ",
                "contraction (app (lam A body) arg => instantiate body' arg') joins an arbitrary second leg by ",
                "inverting it via par_reduces_c_app_inv — kcong is the (beta, app-cong-to-lam) cross ",
                "(par_strips_c_app_beta, symmetrized), kbeta is the (beta,beta) same-redex contraction ",
                "(par_strips_c_subst_join on the body/arg sub-meets), kiota is impossible (a lam-headed app is ",
                "not an iota redex; iota_step_head_none_absurd_type). No disjointness interface needed — the ",
                "redex head is a lam, never a recursor. DerivedProved, zero axiom_deps. Part of #2859 ",
                "(Increment F capstone)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c_app_inv".to_string(),
                "par_reduces_c_lam_inv_eq".to_string(),
                "par_strips_c_app_beta".to_string(),
                "par_strips_c_subst_join".to_string(),
                "par_strips_witness_c_star_symm".to_string(),
                "par_strips_witness_c_star".to_string(),
                "iota_step_head_none_absurd_type".to_string(),
                "lam_inj_snd".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "instantiate".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "kapp_fn_app".to_string(),
                "Eq.substType".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_c_zeta_source — THE zeta-source diamond (NEW with the
        // let-promotion; the let mirror of par_strips_c_beta_source, which under
        // the old alias also served the let arm). When the FIRST leg is a zeta
        // contraction (let_ ty val body => instantiate body' val') and the SECOND
        // is arbitrary (let_ ty val body => e2), the two join by inverting the
        // second leg via par_reduces_c_let_inv:
        //   kcong: the second leg is a let congruence — the zeta side is caught up
        //     by par_strips_c_let_zeta (symmetrized) on the body/val sub-diamonds
        //     (the beta-vs-app-cong-to-lam mechanism, with NO lam recovery dance:
        //     let_inv exposes the components directly).
        //   kzeta: both legs contract the SAME redex — par_strips_c_subst_join on
        //     the body/val sub-meets (the beta-vs-beta mechanism; no injectivity
        //     alignment needed, let_inv already aligned the components).
        //   iota: discharged inside let_inv — a let is its own spine head, never
        //     an iota redex. No disjointness interface needed.
        self.add_definition(SpecDefinition {
            name: "par_strips_c_zeta_source".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
                "(body : KExpr) (body' : KExpr) (e2 : KExpr), ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_reduces_c env ty ty' -> par_reduces_c env val val' -> par_reduces_c env body body' -> ",
                "par_reduces_c env (KExpr.let_ ty val body) e2 -> ",
                "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env body s1 -> par_reduces_c env body s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env val s1 -> par_reduces_c env val s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "par_strips_witness_c_star env (instantiate body' val') e2"
            )
            .to_string(),
            value_src: Some(par_strips_c_zeta_source_proof()),
            is_axiom: false,
            description: concat!(
                "The zeta-source diamond over the GENUINE KExpr.let_ node: a first-leg zeta contraction ",
                "(let_ ty val body => instantiate body' val') joins an arbitrary second leg by inverting it ",
                "via par_reduces_c_let_inv — kcong is the (zeta, let_cong) cross (par_strips_c_let_zeta, ",
                "symmetrized: the congruence side catches up by firing the zeta), kzeta is the (zeta,zeta) ",
                "same-redex contraction (par_strips_c_subst_join on the body/val sub-meets), and the iota arm ",
                "is discharged inside the inversion (a let is its own spine head, never an iota redex). No ",
                "disjointness interface needed. The let mirror of par_strips_c_beta_source, which under the ",
                "old alias also served the let arm. DerivedProved, zero axiom_deps. Part of the let-promotion ",
                "batch B4."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c_let_inv".to_string(),
                "par_strips_c_let_zeta".to_string(),
                "par_strips_c_subst_join".to_string(),
                "par_strips_witness_c_star_symm".to_string(),
                "par_strips_witness_c_star".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_c_let_struct — THE let_cong-structural diamond (NEW with the
        // let-promotion; the let sibling of par_strips_c_app_struct_disjoint /
        // par_strips_c_struct_lam). When the FIRST leg is a let congruence
        // (let_ ty val body => let_ ty' val' body') and the SECOND is arbitrary,
        // the two join by inverting the second leg via par_reduces_c_let_inv:
        //   kcong: the (let_cong, let_cong) diagonal — componentwise meets via the
        //     ty/val/body sub-diamonds, assembled by par_strips_witness_c_star_let
        //     (the app-vs-app mechanism).
        //   kzeta: the (let_cong, zeta) cross — par_strips_c_let_zeta on the
        //     body/val sub-diamonds (the congruence side catches up by firing zeta).
        //   iota: discharged inside let_inv (let head is never an iota redex), so
        //     no guard and no disjointness interface — like the binder diamonds,
        //     NOT like the app diamond (whose head can be an iota redex).
        self.add_definition(SpecDefinition {
            name: "par_strips_c_let_struct".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
                "(body : KExpr) (body' : KExpr) (e2 : KExpr), ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_reduces_c env ty ty' -> par_reduces_c env val val' -> par_reduces_c env body body' -> ",
                "par_reduces_c env (KExpr.let_ ty val body) e2 -> ",
                "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env ty s1 -> par_reduces_c env ty s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env val s1 -> par_reduces_c env val s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "(forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env body s1 -> par_reduces_c env body s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "par_strips_witness_c_star env (KExpr.let_ ty' val' body') e2"
            )
            .to_string(),
            value_src: Some(par_strips_c_let_struct_proof()),
            is_axiom: false,
            description: concat!(
                "The let_cong-structural diamond over the GENUINE KExpr.let_ node: a first-leg let congruence ",
                "(let_ ty val body => let_ ty' val' body') and an arbitrary second leg join by inverting the ",
                "second via par_reduces_c_let_inv — kcong is the componentwise diagonal on the ty/val/body ",
                "sub-diamonds (par_strips_witness_c_star_let), kzeta is the (let_cong, zeta) cross ",
                "(par_strips_c_let_zeta on the body/val sub-diamonds), and the iota arm is discharged inside ",
                "the inversion (a let head is never an iota redex — so unlike the app diamond there is no ",
                "guard and no disjointness interface). The let sibling of par_strips_c_struct_lam / ",
                "par_strips_c_app_struct_disjoint. DerivedProved, zero axiom_deps. Part of the let-promotion ",
                "batch B4."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c_let_inv".to_string(),
                "par_strips_c_let_zeta".to_string(),
                "par_strips_witness_c_star_let".to_string(),
                "par_strips_witness_c_star".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_iota_source_disjoint — THE GUARD-FREE iota-source diamond at a
        // GENERAL source. Like par_strips_iota_source_c but (1) no minimal_or_inner
        // guard — replaced by RecEnvCtorRecDisjoint + a sub-diamond provider keyed on
        // expr_size — and (2) the app arm collapses to a single par_strips_c_iota_app_
        // disjoint call (the (b2) case handled by the sub-diamonds, not the guard).
        // par_reduces_c.rec on the SECOND leg: refl/iota close via the landed joins;
        // the beta/binder/let_/let_cong arms are impossible (a binder-, app(lam)- or
        // let-headed source is not an iota redex, head-none — a let is its own spine
        // head); the app arm fires the disjoint join with the f/a sub-diamonds drawn
        // from the provider (size_app_fst/snd give the Lt witnesses).
        // The general-source iota arm the full single-step diamond consumes.
        self.add_definition(SpecDefinition {
            name: "par_strips_iota_source_disjoint".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "RecEnvCtorRecDisjoint env -> ",
                "iota_step env e e1 -> par_reduces_c env e e2 -> ",
                "(forall (sub : KExpr), Lt (expr_size sub) (expr_size e) -> ",
                "forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env sub s1 -> par_reduces_c env sub s2 -> ",
                "par_strips_witness_c_star env s1 s2) -> ",
                "par_strips_witness_c_star env e1 e2"
            )
            .to_string(),
            value_src: Some(par_strips_iota_source_disjoint_proof()),
            is_axiom: false,
            description: concat!(
                "The GUARD-FREE iota-source diamond at a general source: a first-leg iota (e => e1) and an ",
                "arbitrary second leg (e => e2) join WITHOUT the minimal_or_inner guard, by par_reduces_c.rec on ",
                "the second leg. refl/iota close via par_strips_iota_left_refl_c / par_strips_iota_iota_c; the ",
                "beta/binder/let_/let_cong arms are impossible (a binder-, app(lam)- or let-headed source is not ",
                "an iota redex, head-none); the app arm fires par_strips_c_iota_app_disjoint with the f/a sub-diamonds drawn from ",
                "the expr_size-keyed provider (size_app_fst/snd give the Lt witnesses). The guard is replaced by ",
                "the faithful RecEnvCtorRecDisjoint interface + the sub-diamond provider — the general-source iota ",
                "arm the full single-step diamond consumes. DerivedProved, zero axiom_deps. Part of #2859 ",
                "(Increment F capstone)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.rec".to_string(),
                "par_strips_c_iota_app_disjoint".to_string(),
                "par_strips_iota_left_refl_c".to_string(),
                "par_strips_iota_iota_c".to_string(),
                "par_strips_witness_c_to_star".to_string(),
                "par_strips_witness_c_star".to_string(),
                "iota_step".to_string(),
                "iota_step_head_none_absurd_type".to_string(),
                "RecEnvCtorRecDisjoint".to_string(),
                "expr_size".to_string(),
                "Lt".to_string(),
                "size_app_fst".to_string(),
                "size_app_snd".to_string(),
                "instantiate".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_par_strips_c_full_theorem()?;

        Ok(())
    }

    /// The FULL single-step confluence diamond `par_strips_c_full` (#2859 Increment F
    /// endgame): `forall e e1 e2, par_reduces_c e e1 -> par_reduces_c e e2 ->
    /// par_strips_witness_c_star e1 e2`, by strong induction on `expr_size e`
    /// (nat_strong_rec) with an inner par_reduces_c.rec dispatch on the first leg —
    /// each arm routes to a guard-free structural diamond fed the sub-diamonds from
    /// the strong IH. The guard-free capstone the multi-step diamond + injectivity +
    /// def_eq_joinable consume.
    fn add_par_strips_c_full_theorem(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_strips_c_full".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "RecEnvCtorRecDisjoint env -> RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_reduces_c env e e1 -> par_reduces_c env e e2 -> ",
                "par_strips_witness_c_star env e1 e2"
            )
            .to_string(),
            value_src: Some(par_strips_c_full_proof()),
            is_axiom: false,
            description: concat!(
                "THE FULL single-step confluence diamond for par_reduces_c — the Increment F endgame. For any ",
                "source e, two parallel reductions e => e1 and e => e2 join at the star-legged witness. Proved by ",
                "strong induction on expr_size e (nat_strong_rec) with an inner par_reduces_c.rec dispatch on the ",
                "first leg: refl -> par_strips_c_refl_left; app -> par_strips_c_app_struct_disjoint; lam/pi/forall ",
                "-> par_strips_c_struct_{lam,pi,forall}; beta -> par_strips_c_beta_source; let_ (zeta) -> ",
                "par_strips_c_zeta_source and let_cong -> par_strips_c_let_struct (both over the GENUINE ",
                "KExpr.let_ node since the let-promotion); iota -> par_strips_iota_source_disjoint. Every arm ",
                "draws its sub-diamonds from the strong IH via the expr_size-decrease lemmas ",
                "(size_app/lam/pi_fst/snd, size_let_fst/val/body, lt_trans). GUARD-FREE: ",
                "the minimal_or_inner guard is fully eliminated, replaced by the faithful RecEnvCtorRecDisjoint / ",
                "RecEnvClosed / RecEnvLiftClosed interfaces (discharged at end-of-track). DerivedProved, zero ",
                "axiom_deps. The keystone the multi-step diamond, pi/sort/lam injectivity, and def_eq_joinable ",
                "consume to retire church_rosser_whnf. Part of #2859 (Increment F capstone)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.rec".to_string(),
                "par_reduces_c.lam".to_string(),
                "par_reduces_c.pi".to_string(),
                "par_reduces_c.forall_".to_string(),
                "nat_strong_rec".to_string(),
                "expr_size".to_string(),
                "Lt".to_string(),
                "size_app_fst".to_string(),
                "size_app_snd".to_string(),
                "size_lam_fst".to_string(),
                "size_lam_snd".to_string(),
                "size_pi_fst".to_string(),
                "size_pi_snd".to_string(),
                "size_let_fst".to_string(),
                "size_let_snd".to_string(),
                "size_let_thd".to_string(),
                "lt_trans".to_string(),
                "par_strips_c_refl_left".to_string(),
                "par_subsumes_par_c_star".to_string(),
                "par_strips_c_app_struct_disjoint".to_string(),
                "par_strips_c_struct_lam".to_string(),
                "par_strips_c_struct_pi".to_string(),
                "par_strips_c_struct_forall".to_string(),
                "par_strips_c_beta_source".to_string(),
                "par_strips_c_zeta_source".to_string(),
                "par_strips_c_let_struct".to_string(),
                "par_strips_iota_source_disjoint".to_string(),
                "par_strips_witness_c_star".to_string(),
                "RecEnvCtorRecDisjoint".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "Eq.refl".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

/// Closed proof term for `par_strips_iota_source_disjoint` (the guard-free general-
/// source iota-source diamond). par_reduces_c.rec on the second leg; the app arm
/// fires par_strips_c_iota_app_disjoint with the f/a sub-diamonds from the provider,
/// the binder/beta/let_/let_cong arms discharge via head-none (a let is its own
/// spine head), refl/iota via the landed joins.
fn par_strips_iota_source_disjoint_proof() -> String {
    // The sub-diamond provider type at source s.
    let dia_ty = |s: &str| -> String {
        format!(
            "(forall (sub : KExpr), Lt (expr_size sub) (expr_size ({s})) -> \
             forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env sub s1 -> par_reduces_c env sub s2 -> \
             par_strips_witness_c_star env s1 s2)"
        )
    };
    // The IH type for a sub-derivation sub => reduct (motive at (sub, reduct)).
    let ih_ty = |sub: &str, reduct: &str| -> String {
        format!(
            "iota_step env {sub} e1 -> {dia} -> par_strips_witness_c_star env e1 {reduct}",
            dia = dia_ty(sub),
        )
    };
    let motive = format!(
        "(fun (s : KExpr) (t : KExpr) (_h : par_reduces_c env s t) => \
         iota_step env s e1 -> {dia} -> par_strips_witness_c_star env e1 t)",
        dia = dia_ty("s"),
    );
    let refl_arm = format!(
        "(fun (s0 : KExpr) (hiota : iota_step env s0 e1) (_dia : {dia}) => \
         par_strips_witness_c_to_star env e1 s0 (par_strips_iota_left_refl_c env s0 e1 hiota))",
        dia = dia_ty("s0"),
    );
    // head-none discharge for a binder/app(lam)-headed source.
    let discharge = |src: &str, reduct: &str| -> String {
        format!(
            "iota_step_head_none_absurd_type env ({src}) e1 \
             (par_strips_witness_c_star env e1 ({reduct})) \
             (Eq.refl (OptionType Name) (OptionType.none Name)) hiota"
        )
    };
    let beta_arm = format!(
        "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) \
         (_hA : par_reduces_c env A A') (_hbody : par_reduces_c env body body') (_harg : par_reduces_c env arg arg') \
         (_ihA : {ihA}) (_ihbody : {ihbody}) (_iharg : {iharg}) \
         (hiota : iota_step env (KExpr.app (KExpr.lam A body) arg) e1) \
         (_dia : {dia}) => {discharge})",
        ihA = ih_ty("A", "A'"),
        ihbody = ih_ty("body", "body'"),
        iharg = ih_ty("arg", "arg'"),
        dia = dia_ty("KExpr.app (KExpr.lam A body) arg"),
        discharge = discharge("KExpr.app (KExpr.lam A body) arg", "instantiate body' arg'"),
    );
    let binder_arm = |head: &str| -> String {
        format!(
            "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) \
             (_hty : par_reduces_c env ty ty') (_hbody : par_reduces_c env body body') \
             (_ihty : {ihty}) (_ihbody : {ihbody}) \
             (hiota : iota_step env ({head} ty body) e1) \
             (_dia : {dia}) => {discharge})",
            ihty = ih_ty("ty", "ty'"),
            ihbody = ih_ty("body", "body'"),
            dia = dia_ty(&format!("{head} ty body")),
            discharge = discharge(&format!("{head} ty body"), &format!("{head} ty' body'")),
            head = head,
        )
    };
    let lam_arm = binder_arm("KExpr.lam");
    let pi_arm = binder_arm("KExpr.pi");
    let forall_arm = binder_arm("KExpr.forall_");
    let let_arm = format!(
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) \
         (_hty : par_reduces_c env ty ty') (_hval : par_reduces_c env val val') (_hbody : par_reduces_c env body body') \
         (_ihty : {ihty}) (_ihval : {ihval}) (_ihbody : {ihbody}) \
         (hiota : iota_step env (KExpr.let_ ty val body) e1) \
         (_dia : {dia}) => {discharge})",
        ihty = ih_ty("ty", "ty'"),
        ihval = ih_ty("val", "val'"),
        ihbody = ih_ty("body", "body'"),
        dia = dia_ty("KExpr.let_ ty val body"),
        discharge = discharge("KExpr.let_ ty val body", "instantiate body' val'"),
    );
    // let_cong arm: same head-none discharge (a let is its own spine head).
    let let_cong_arm = format!(
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) \
         (_hty : par_reduces_c env ty ty') (_hval : par_reduces_c env val val') (_hbody : par_reduces_c env body body') \
         (_ihty : {ihty}) (_ihval : {ihval}) (_ihbody : {ihbody}) \
         (hiota : iota_step env (KExpr.let_ ty val body) e1) \
         (_dia : {dia}) => {discharge})",
        ihty = ih_ty("ty", "ty'"),
        ihval = ih_ty("val", "val'"),
        ihbody = ih_ty("body", "body'"),
        dia = dia_ty("KExpr.let_ ty val body"),
        discharge = discharge("KExpr.let_ ty val body", "KExpr.let_ ty' val' body'"),
    );
    let iota_arm = format!(
        "(fun (e0 : KExpr) (e0' : KExpr) (hstep : iota_step env e0 e0') \
         (hiota : iota_step env e0 e1) (_dia : {dia}) => \
         par_strips_witness_c_to_star env e1 e0' (par_strips_iota_iota_c env e0 e1 e0' hiota hstep))",
        dia = dia_ty("e0"),
    );
    // app arm: source app f a. Fire the disjoint join with the f/a sub-diamonds.
    let app_arm = format!(
        "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) \
         (hf : par_reduces_c env f f') (ha : par_reduces_c env a a') \
         (_ihf : {ihf}) (_iha : {iha}) \
         (hiota : iota_step env (KExpr.app f a) e1) \
         (dia : {dia}) => \
         par_strips_c_iota_app_disjoint env f a e1 f' a' disjoint hiota hf ha \
         (dia f (size_app_fst f a)) (dia a (size_app_snd f a)))",
        ihf = ih_ty("f", "f'"),
        iha = ih_ty("a", "a'"),
        dia = dia_ty("KExpr.app f a"),
    );
    // proj arm: a proj is its own spine head — head-none discharge (as binders).
    // NB: scrutinee named `scr` (not `sub`) to avoid shadowing the inner
    // `forall (sub : KExpr)` bound inside dia_ty's provider type.
    let proj_arm = format!(
        "(fun (s : Name) (i : Nat) (scr : KExpr) (scr' : KExpr) \
         (_hsub : par_reduces_c env scr scr') (_ihsub : {ihsub}) \
         (hiota : iota_step env (KExpr.proj s i scr) e1) \
         (_dia : {dia}) => {discharge})",
        ihsub = ih_ty("scr", "scr'"),
        dia = dia_ty("KExpr.proj s i scr"),
        discharge = discharge("KExpr.proj s i scr", "KExpr.proj s i scr'"),
    );
    format!(
        "fun (env : RecEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr) \
         (disjoint : RecEnvCtorRecDisjoint env) \
         (hi : iota_step env e e1) (h2 : par_reduces_c env e e2) \
         (dia0 : {dia_e}) => \
         par_reduces_c.rec env {motive} \
         {refl_arm} {beta_arm} {app_arm} {lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} \
         e e2 h2 hi dia0",
        dia_e = dia_ty("e"),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = lam_arm,
        pi_arm = pi_arm,
        forall_arm = forall_arm,
        let_arm = let_arm,
        iota_arm = iota_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for `par_strips_c_full` (the FULL single-step diamond).
/// `nat_strong_rec` on `expr_size e`; inside, `par_reduces_c.rec` on the first leg
/// dispatches each constructor to its guard-free structural diamond, fed the f/a/…
/// sub-diamonds reconstructed from the strong IH `Dia` via the expr_size-decrease
/// lemmas. env/disjoint/closed/liftclosed are fixed outside the induction.
fn par_strips_c_full_proof() -> String {
    // P n: the diamond at every term of size n. a0/a1/a2 are the bound source/reducts.
    let motive_p = concat!(
        "(fun (n : Nat) => forall (a0 : KExpr), Eq Nat (expr_size a0) n -> ",
        "forall (a1 : KExpr) (a2 : KExpr), par_reduces_c env a0 a1 -> par_reduces_c env a0 a2 -> ",
        "par_strips_witness_c_star env a1 a2)"
    );
    // Inner par_reduces_c.rec motive over the FIRST leg (s => s1), keeping a2 fixed;
    // carries the size equation so each arm can call Dia on its subterms.
    let motive_rec = concat!(
        "(fun (s : KExpr) (s1 : KExpr) (_d : par_reduces_c env s s1) => ",
        "Eq Nat (expr_size s) k -> par_reduces_c env s a2 -> ",
        "par_strips_witness_c_star env s1 a2)"
    );
    // The recursor IH type at a sub-derivation sub => reduct (useless — its precond
    // expr_size sub = k is false — but must be named to match the minor premise).
    let ih = |sub: &str, reduct: &str| -> String {
        format!(
            "Eq Nat (expr_size {sub}) k -> par_reduces_c env {sub} a2 -> par_strips_witness_c_star env {reduct} a2"
        )
    };
    // mk_dia shape sub lt: the sub-diamond at `sub`, drawn from Dia using
    // lt : Lt (expr_size sub) (expr_size shape) transported along hes : size shape = k.
    let mk_dia = |shape: &str, sub: &str, lt: &str| -> String {
        format!(
            "(fun (ds1 : KExpr) (ds2 : KExpr) (dp1 : par_reduces_c env {sub} ds1) (dp2 : par_reduces_c env {sub} ds2) => \
             Dia (expr_size {sub}) \
             (Eq.substType Nat (fun (z : Nat) => Lt (expr_size {sub}) z) (expr_size ({shape})) k hes {lt}) \
             {sub} (Eq.refl Nat (expr_size {sub})) ds1 ds2 dp1 dp2)"
        )
    };

    let refl_arm = concat!(
        "(fun (s0 : KExpr) (hes : Eq Nat (expr_size s0) k) (d2s : par_reduces_c env s0 a2) => ",
        "par_strips_c_refl_left env s0 a2 (par_subsumes_par_c_star env s0 a2 d2s))"
    );

    // beta arm: source app (lam A body) arg, reduct instantiate body' arg'.
    let beta_shape = "KExpr.app (KExpr.lam A body) arg";
    let beta_lt_body = "(lt_trans (expr_size body) (expr_size (KExpr.lam A body)) (expr_size (KExpr.app (KExpr.lam A body) arg)) (size_lam_snd A body) (size_app_fst (KExpr.lam A body) arg))";
    let beta_arm = format!(
        "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) \
         (hA : par_reduces_c env A A') (hbody : par_reduces_c env body body') (harg : par_reduces_c env arg arg') \
         (_ihA : {ihA}) (_ihbody : {ihbody}) (_iharg : {iharg}) \
         (hes : Eq Nat (expr_size ({beta_shape})) k) (d2s : par_reduces_c env ({beta_shape}) a2) => \
         par_strips_c_beta_source env A A' body body' arg arg' a2 closed liftclosed hA hbody harg d2s \
         {db} {da})",
        ihA = ih("A", "A'"),
        ihbody = ih("body", "body'"),
        iharg = ih("arg", "arg'"),
        beta_shape = beta_shape,
        db = mk_dia(beta_shape, "body", beta_lt_body),
        da = mk_dia(beta_shape, "arg", "(size_app_snd (KExpr.lam A body) arg)"),
    );

    // app arm: source app f a, reduct app f' a'.
    let app_arm = format!(
        "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) \
         (hf : par_reduces_c env f f') (ha : par_reduces_c env a a') \
         (_ihf : {ihf}) (_iha : {iha}) \
         (hes : Eq Nat (expr_size (KExpr.app f a)) k) (d2s : par_reduces_c env (KExpr.app f a) a2) => \
         par_strips_c_app_struct_disjoint env f a f' a' a2 disjoint closed liftclosed hf ha d2s \
         {df} {da})",
        ihf = ih("f", "f'"),
        iha = ih("a", "a'"),
        df = mk_dia("KExpr.app f a", "f", "(size_app_fst f a)"),
        da = mk_dia("KExpr.app f a", "a", "(size_app_snd f a)"),
    );

    // binder arms (lam/pi/forall): source HEAD ty body, reduct HEAD ty' body'.
    let binder_arm =
        |head: &str, struct_lemma: &str, ctor: &str, sz_fst: &str, sz_snd: &str| -> String {
            let shape = format!("{head} ty body");
            format!(
                "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) \
             (hty : par_reduces_c env ty ty') (hbody : par_reduces_c env body body') \
             (_ihty : {ihty}) (_ihbody : {ihbody}) \
             (hes : Eq Nat (expr_size ({shape})) k) (d2s : par_reduces_c env ({shape}) a2) => \
             {struct_lemma} env ty body ({head} ty' body') a2 \
             ({ctor} env ty ty' body body' hty hbody) d2s {dfst} {dsnd})",
                ihty = ih("ty", "ty'"),
                ihbody = ih("body", "body'"),
                shape = shape,
                struct_lemma = struct_lemma,
                head = head,
                ctor = ctor,
                dfst = mk_dia(&shape, "ty", &format!("({sz_fst} ty body)")),
                dsnd = mk_dia(&shape, "body", &format!("({sz_snd} ty body)")),
            )
        };
    let lam_arm = binder_arm(
        "KExpr.lam",
        "par_strips_c_struct_lam",
        "par_reduces_c.lam",
        "size_lam_fst",
        "size_lam_snd",
    );
    let pi_arm = binder_arm(
        "KExpr.pi",
        "par_strips_c_struct_pi",
        "par_reduces_c.pi",
        "size_pi_fst",
        "size_pi_snd",
    );
    let forall_arm = binder_arm(
        "KExpr.forall_",
        "par_strips_c_struct_forall",
        "par_reduces_c.forall_",
        "size_pi_fst",
        "size_pi_snd",
    );

    // let_ (zeta) arm: source let_ ty val body (a GENUINE let node since the
    // let-promotion), reduct instantiate body' val'. Route to the zeta-source
    // diamond par_strips_c_zeta_source with the body/val sub-diamonds drawn from
    // the strong IH via the genuine let expr_size-decrease lemmas.
    let let_shape = "KExpr.let_ ty val body";
    let let_arm = format!(
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) \
         (hty : par_reduces_c env ty ty') (hval : par_reduces_c env val val') (hbody : par_reduces_c env body body') \
         (_ihty : {ihty}) (_ihval : {ihval}) (_ihbody : {ihbody}) \
         (hes : Eq Nat (expr_size ({let_shape})) k) (d2s : par_reduces_c env ({let_shape}) a2) => \
         par_strips_c_zeta_source env ty ty' val val' body body' a2 closed liftclosed hty hval hbody d2s \
         {db} {dv})",
        ihty = ih("ty", "ty'"),
        ihval = ih("val", "val'"),
        ihbody = ih("body", "body'"),
        let_shape = let_shape,
        db = mk_dia(let_shape, "body", "(size_let_thd ty val body)"),
        dv = mk_dia(let_shape, "val", "(size_let_snd ty val body)"),
    );

    // let_cong arm: source let_ ty val body, reduct let_ ty' val' body'. Route to
    // the let_cong-structural diamond par_strips_c_let_struct with all three
    // component sub-diamonds from the strong IH.
    let let_cong_arm = format!(
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) \
         (hty : par_reduces_c env ty ty') (hval : par_reduces_c env val val') (hbody : par_reduces_c env body body') \
         (_ihty : {ihty}) (_ihval : {ihval}) (_ihbody : {ihbody}) \
         (hes : Eq Nat (expr_size ({let_shape})) k) (d2s : par_reduces_c env ({let_shape}) a2) => \
         par_strips_c_let_struct env ty ty' val val' body body' a2 closed liftclosed hty hval hbody d2s \
         {dty} {dval} {dbody})",
        ihty = ih("ty", "ty'"),
        ihval = ih("val", "val'"),
        ihbody = ih("body", "body'"),
        let_shape = let_shape,
        dty = mk_dia(let_shape, "ty", "(size_let_fst ty val body)"),
        dval = mk_dia(let_shape, "val", "(size_let_snd ty val body)"),
        dbody = mk_dia(let_shape, "body", "(size_let_thd ty val body)"),
    );

    // iota arm: source e0, reduct e0'. Route to par_strips_iota_source_disjoint with a
    // sub-diamond PROVIDER (keyed on Lt (expr_size sub) (expr_size e0)).
    let iota_provider = "(fun (sub : KExpr) (hlt : Lt (expr_size sub) (expr_size e0)) (ds1 : KExpr) (ds2 : KExpr) (dp1 : par_reduces_c env sub ds1) (dp2 : par_reduces_c env sub ds2) => Dia (expr_size sub) (Eq.substType Nat (fun (z : Nat) => Lt (expr_size sub) z) (expr_size e0) k hes hlt) sub (Eq.refl Nat (expr_size sub)) ds1 ds2 dp1 dp2)";
    let iota_arm = format!(
        "(fun (e0 : KExpr) (e0' : KExpr) (hstep : iota_step env e0 e0') \
         (hes : Eq Nat (expr_size e0) k) (d2s : par_reduces_c env e0 a2) => \
         par_strips_iota_source_disjoint env e0 e0' a2 disjoint hstep d2s {prov})",
        prov = iota_provider,
    );

    // proj arm: source proj s i scr, reduct proj s i scr'. A proj head is never an
    // iota redex (guard-free, like the binders); single scrutinee sub-diamond via
    // par_strips_c_struct_proj. Scrutinee named `scr` (not `sub`) for safety.
    let proj_arm = format!(
        "(fun (s : Name) (i : Nat) (scr : KExpr) (scr' : KExpr) \
         (hsub : par_reduces_c env scr scr') (_ihsub : {ihsub}) \
         (hes : Eq Nat (expr_size (KExpr.proj s i scr)) k) (d2s : par_reduces_c env (KExpr.proj s i scr) a2) => \
         par_strips_c_struct_proj env s i scr (KExpr.proj s i scr') a2 \
         (par_reduces_c.proj env s i scr scr' hsub) d2s {dscr})",
        ihsub = ih("scr", "scr'"),
        dscr = mk_dia("KExpr.proj s i scr", "scr", "(size_proj_sub s i scr)"),
    );

    let step = format!(
        "(fun (k : Nat) (Dia : forall (j : Nat), Lt j k -> {motive_p} j) => \
         fun (a0 : KExpr) (ha0 : Eq Nat (expr_size a0) k) (a1 : KExpr) (a2 : KExpr) \
         (da1 : par_reduces_c env a0 a1) (da2 : par_reduces_c env a0 a2) => \
         par_reduces_c.rec env {motive_rec} \
         {refl_arm} {beta_arm} {app_arm} {lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} \
         a0 a1 da1 ha0 da2)",
        motive_p = motive_p,
        motive_rec = motive_rec,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = lam_arm,
        pi_arm = pi_arm,
        forall_arm = forall_arm,
        let_arm = let_arm,
        iota_arm = iota_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    );

    format!(
        "fun (env : RecEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr) \
         (disjoint : RecEnvCtorRecDisjoint env) (closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) \
         (d1 : par_reduces_c env e e1) (d2 : par_reduces_c env e e2) => \
         nat_strong_rec {motive_p} {step} (expr_size e) e (Eq.refl Nat (expr_size e)) e1 e2 d1 d2",
        motive_p = motive_p,
        step = step,
    )
}

/// Closed proof term for `par_strips_c_beta_source` (the beta-source diamond).
/// Inverts the second leg via par_reduces_c_app_inv (f := lam A body, a := arg):
/// kcong → par_strips_c_app_beta (symmetrized), kbeta → par_strips_c_subst_join,
/// kiota → absurd (lam-headed app is not an iota redex).
fn par_strips_c_beta_source_proof() -> String {
    // kcong: second leg app (lam A body => f2) (arg => a2). Recover f2 = lam Af bodyf,
    // build witness (app (lam Af bodyf) a2)(instantiate body' arg') via app_beta,
    // transport the head lam Af bodyf -> f2, then symm to land at C (app f2 a2).
    let kcong = concat!(
        "(fun (f2 : KExpr) (a2 : KExpr) ",
        "(hf2 : par_reduces_c env (KExpr.lam A body) f2) (ha2 : par_reduces_c env arg a2) => ",
        "par_reduces_c_lam_inv_eq env A body f2 ",
        "(par_strips_witness_c_star env (instantiate body' arg') (KExpr.app f2 a2)) ",
        "hf2 ",
        "(fun (Af : KExpr) (bodyf : KExpr) ",
        "(eqf2 : Eq KExpr f2 (KExpr.lam Af bodyf)) ",
        "(_hAf : par_reduces_c env A Af) (hbf : par_reduces_c env body bodyf) => ",
        "par_strips_witness_c_star_symm env (KExpr.app f2 a2) (instantiate body' arg') ",
        "(Eq.substType KExpr ",
        "(fun (x : KExpr) => par_strips_witness_c_star env (KExpr.app x a2) (instantiate body' arg')) ",
        "(KExpr.lam Af bodyf) f2 (Eq.symm KExpr f2 (KExpr.lam Af bodyf) eqf2) ",
        "(par_strips_c_app_beta env Af bodyf a2 body' arg' closed liftclosed ",
        "(db bodyf body' hbf hbody) ",
        "(da a2 arg' ha2 harg)))))"
    );
    // kbeta: both legs contract the same redex. lam injectivity aligns body0 := body;
    // par_strips_c_subst_join on (body' meet body0') and (arg' meet arg0').
    let kbeta = concat!(
        "(fun (A0 : KExpr) (A0' : KExpr) (body0 : KExpr) (body0' : KExpr) (arg0' : KExpr) ",
        "(eqf0 : Eq KExpr (KExpr.lam A body) (KExpr.lam A0 body0)) ",
        "(_hA0 : par_reduces_c env A0 A0') (hbody0 : par_reduces_c env body0 body0') ",
        "(harg0 : par_reduces_c env arg arg0') => ",
        "par_strips_c_subst_join env body' body0' arg' arg0' closed liftclosed ",
        "(db body' body0' hbody ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x body0') body0 body ",
        "(Eq.symm KExpr body body0 (lam_inj_snd A body A0 body0 eqf0)) hbody0)) ",
        "(da arg' arg0' harg harg0))"
    );
    // kiota: impossible — kexpr_const_name (kapp_fn (app (lam A body) arg)) = none.
    let kiota = concat!(
        "(fun (t0 : KExpr) (hi : iota_step env (KExpr.app (KExpr.lam A body) arg) t0) ",
        "(_eqt : Eq KExpr e2 t0) => ",
        "iota_step_head_none_absurd_type env (KExpr.app (KExpr.lam A body) arg) t0 ",
        "(par_strips_witness_c_star env (instantiate body' arg') t0) ",
        "(Eq.trans (OptionType Name) ",
        "(kexpr_const_name (kapp_fn (KExpr.app (KExpr.lam A body) arg))) ",
        "(kexpr_const_name (kapp_fn (KExpr.lam A body))) ",
        "(OptionType.none Name) ",
        "(Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) ",
        "(kapp_fn (KExpr.app (KExpr.lam A body) arg)) (kapp_fn (KExpr.lam A body)) ",
        "(kapp_fn_app (KExpr.lam A body) arg)) ",
        "(Eq.refl (OptionType Name) (OptionType.none Name))) ",
        "hi)"
    );
    format!(
        concat!(
            "fun (env : RecEnv) (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) ",
            "(arg : KExpr) (arg' : KExpr) (e2 : KExpr) ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) ",
            "(_hA : par_reduces_c env A A') (hbody : par_reduces_c env body body') ",
            "(harg : par_reduces_c env arg arg') ",
            "(h2 : par_reduces_c env (KExpr.app (KExpr.lam A body) arg) e2) ",
            "(db : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env body s1 -> par_reduces_c env body s2 -> ",
            "par_strips_witness_c_star env s1 s2) ",
            "(da : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env arg s1 -> par_reduces_c env arg s2 -> ",
            "par_strips_witness_c_star env s1 s2) => ",
            "par_reduces_c_app_inv env (KExpr.lam A body) arg e2 ",
            "(fun (x : KExpr) => par_strips_witness_c_star env (instantiate body' arg') x) ",
            "h2 {kcong} {kbeta} {kiota}"
        ),
        kcong = kcong,
        kbeta = kbeta,
        kiota = kiota,
    )
}

/// Closed proof term for `par_strips_c_app_struct_disjoint` (the GUARD-FREE
/// app-structural diamond). Identical to `par_strips_c_app_struct_proof` except it
/// drops the `minimal_or_inner` guard (replaced by `RecEnvCtorRecDisjoint`) and its
/// kiota arm routes through the guard-free `par_strips_iota_app_source_disjoint`
/// (symmetrized) rather than the guarded `par_strips_iota_target_c`.
fn par_strips_c_app_struct_disjoint_proof() -> String {
    // kcong (app, app): the diagonal on the f-/a-sub-diamonds (unchanged).
    let kcong = concat!(
        "(fun (f2 : KExpr) (a2 : KExpr) ",
        "(hf2 : par_reduces_c env f f2) (ha2 : par_reduces_c env a a2) => ",
        "par_strips_witness_c_star_app env f' f2 a' a2 ",
        "(df f' f2 hf hf2) (da a' a2 ha ha2))"
    );
    // kbeta (app, beta): unchanged from the guarded version (no guard participation).
    let kbeta = concat!(
        "(fun (A : KExpr) (A' : KExpr) (bdy : KExpr) (bdy' : KExpr) (arg' : KExpr) ",
        "(eqf : Eq KExpr f (KExpr.lam A bdy)) ",
        "(hA : par_reduces_c env A A') (hbody : par_reduces_c env bdy bdy') ",
        "(harg : par_reduces_c env a arg') => ",
        "par_reduces_c_lam_inv_eq env A bdy f' ",
        "(par_strips_witness_c_star env (KExpr.app f' a') (instantiate bdy' arg')) ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x f') f (KExpr.lam A bdy) eqf hf) ",
        "(fun (Af : KExpr) (bodyf : KExpr) ",
        "(eqfp : Eq KExpr f' (KExpr.lam Af bodyf)) ",
        "(_hAf : par_reduces_c env A Af) (_hbf : par_reduces_c env bdy bodyf) => ",
        "Eq.substType KExpr ",
        "(fun (x : KExpr) => par_strips_witness_c_star env (KExpr.app x a') (instantiate bdy' arg')) ",
        "(KExpr.lam Af bodyf) f' (Eq.symm KExpr f' (KExpr.lam Af bodyf) eqfp) ",
        "(par_strips_c_app_beta env Af bodyf a' bdy' arg' closed liftclosed ",
        "(par_strips_witness_c_star_lam_meet env Af A' bodyf bdy' ",
        "(Eq.substType KExpr ",
        "(fun (x : KExpr) => par_strips_witness_c_star env x (KExpr.lam A' bdy')) f' (KExpr.lam Af bodyf) eqfp ",
        "(df f' (KExpr.lam A' bdy') hf ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x (KExpr.lam A' bdy')) ",
        "(KExpr.lam A bdy) f (Eq.symm KExpr f (KExpr.lam A bdy) eqf) ",
        "(par_reduces_c.lam env A A' bdy bdy' hA hbody))))) ",
        "(da a' arg' ha harg))))"
    );
    // kiota (app, iota): route to the GUARD-FREE iota-source diamond, symmetrized.
    // par_strips_iota_app_source_disjoint gives witness t0 (app f' a'); symm flips it
    // to witness (app f' a') t0 = C t0.
    let kiota = concat!(
        "(fun (t0 : KExpr) (hi : iota_step env (KExpr.app f a) t0) (_eqt : Eq KExpr e2 t0) => ",
        "par_strips_witness_c_star_symm env t0 (KExpr.app f' a') ",
        "(par_strips_iota_app_source_disjoint env f a t0 (KExpr.app f' a') disjoint hi ",
        "(par_reduces_c.app env f f' a a' hf ha) df da))"
    );
    format!(
        concat!(
            "fun (env : RecEnv) (f : KExpr) (a : KExpr) (f' : KExpr) (a' : KExpr) (e2 : KExpr) ",
            "(disjoint : RecEnvCtorRecDisjoint env) ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) ",
            "(hf : par_reduces_c env f f') (ha : par_reduces_c env a a') ",
            "(h2 : par_reduces_c env (KExpr.app f a) e2) ",
            "(df : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env f s1 -> par_reduces_c env f s2 -> ",
            "par_strips_witness_c_star env s1 s2) ",
            "(da : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env a s1 -> par_reduces_c env a s2 -> ",
            "par_strips_witness_c_star env s1 s2) => ",
            "par_reduces_c_app_inv env f a e2 ",
            "(fun (x : KExpr) => par_strips_witness_c_star env (KExpr.app f' a') x) ",
            "h2 {kcong} {kbeta} {kiota}"
        ),
        kcong = kcong,
        kbeta = kbeta,
        kiota = kiota,
    )
}

/// Closed proof term for `par_strips_iota_app_source_disjoint` (the guard-free
/// iota-source diamond at an app source). Inverts the second leg via
/// par_reduces_c_app_inv: kcong → par_strips_c_iota_app_disjoint, kbeta → absurd
/// (lam-head is not an iota redex), kiota → determinism (par_strips_iota_iota_c).
fn par_strips_iota_app_source_disjoint_proof() -> String {
    // hhead_none : kexpr_const_name (kapp_fn (app f a)) = none, derived in the kbeta
    // arm from eqf : f = lam A body (the app head reduces to the lam, whose const
    // name is definitionally none).
    let hhead_none = concat!(
        "(Eq.trans (OptionType Name) ",
        "(kexpr_const_name (kapp_fn (KExpr.app f a))) ",
        "(kexpr_const_name (kapp_fn (KExpr.lam A body))) ",
        "(OptionType.none Name) ",
        "(Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) ",
        "(kapp_fn (KExpr.app f a)) (kapp_fn (KExpr.lam A body)) ",
        "(Eq.trans KExpr (kapp_fn (KExpr.app f a)) (kapp_fn f) (kapp_fn (KExpr.lam A body)) ",
        "(kapp_fn_app f a) ",
        "(Eq.cong KExpr KExpr (fun (X : KExpr) => kapp_fn X) f (KExpr.lam A body) eqf))) ",
        "(Eq.refl (OptionType Name) (OptionType.none Name)))"
    );
    let kcong = concat!(
        "(fun (f' : KExpr) (a' : KExpr) ",
        "(hf : par_reduces_c env f f') (ha : par_reduces_c env a a') => ",
        "par_strips_c_iota_app_disjoint env f a e1 f' a' disjoint hiota hf ha df da)"
    );
    let kbeta = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg' : KExpr) ",
            "(eqf : Eq KExpr f (KExpr.lam A body)) ",
            "(hA : par_reduces_c env A A') (hbody : par_reduces_c env body body') ",
            "(harg : par_reduces_c env a arg') => ",
            "iota_step_head_none_absurd_type env (KExpr.app f a) e1 ",
            "(par_strips_witness_c_star env e1 (instantiate body' arg')) ",
            "{hhead_none} hiota)"
        ),
        hhead_none = hhead_none,
    );
    let kiota = concat!(
        "(fun (t0 : KExpr) (hi2 : iota_step env (KExpr.app f a) t0) (_eqt : Eq KExpr e2 t0) => ",
        "par_strips_witness_c_to_star env e1 t0 ",
        "(par_strips_iota_iota_c env (KExpr.app f a) e1 t0 hiota hi2))"
    );
    format!(
        concat!(
            "fun (env : RecEnv) (f : KExpr) (a : KExpr) (e1 : KExpr) (e2 : KExpr) ",
            "(disjoint : RecEnvCtorRecDisjoint env) ",
            "(hiota : iota_step env (KExpr.app f a) e1) ",
            "(h2 : par_reduces_c env (KExpr.app f a) e2) ",
            "(df : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env f s1 -> par_reduces_c env f s2 -> ",
            "par_strips_witness_c_star env s1 s2) ",
            "(da : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env a s1 -> par_reduces_c env a s2 -> ",
            "par_strips_witness_c_star env s1 s2) => ",
            "par_reduces_c_app_inv env f a e2 ",
            "(fun (x : KExpr) => par_strips_witness_c_star env e1 x) ",
            "h2 {kcong} {kbeta} {kiota}"
        ),
        kcong = kcong,
        kbeta = kbeta,
        kiota = kiota,
    )
}

/// Closed proof term for `par_strips_c_iota_app_full` (Increment F capstone core,
/// the guard-free (iota, app-structural) join). Dispatches on iota_reduct f via
/// OptionType.rec with an equation-carrying motive: the some arm runs the (b2)
/// over-application join, the none arm runs the (a) minimal join with the
/// major-not-redex side-condition supplied by the conditional hypothesis hmaj_nr.
fn par_strips_c_iota_app_full_proof() -> String {
    // The over-application reduct head identity (kapp_fn (app f a) = kapp_fn f),
    // used to lift the head-name lookup from (app f a) to f for the minimal join.
    let head_eq_f = concat!(
        "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn f)) ",
        "(kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname) ",
        "(Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) ",
        "(kapp_fn f) (kapp_fn (KExpr.app f a)) ",
        "(Eq.symm KExpr (kapp_fn (KExpr.app f a)) (kapp_fn f) (kapp_fn_app f a))) h1)"
    );
    // none branch: recover the recursor head name via iota_reduct_some_inv_type on
    // the (app f a) iota witness, derive iota_reduct a = none from hmaj_nr, and run
    // the (a) minimal join.
    let none_arm = format!(
        concat!(
            "(fun (hfn : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)) => ",
            "iota_reduct_some_inv_type env (KExpr.app f a) e1 ",
            "(par_strips_witness_c_star env e1 (KExpr.app f' a')) h_e1 ",
            "(fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) ",
            "(h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname)) ",
            "(_h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) ",
            "(_h3 : Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app f a)))) (OptionType.some KExpr major)) ",
            "(_h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) ",
            "(_h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) ",
            "(_h5r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args (KExpr.app f a))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args (KExpr.app f a))) (recrule_rhs rule))))) (OptionType.some KExpr e1)) => ",
            "par_strips_c_iota_app_minimal env f f' a a' e1 recname ",
            "{head_eq_f} hfn (hmaj_nr hfn) h_e1 hf ha))"
        ),
        head_eq_f = head_eq_f,
    );
    // some branch: (b2) over-application.
    let some_arm = concat!(
        "(fun (f1 : KExpr) (hfs : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f1)) => ",
        "par_strips_c_iota_app_b2_over env f a e1 f1 f' a' h_e1 hfs hf ha df da)"
    );
    format!(
        concat!(
            "fun (env : RecEnv) (f : KExpr) (a : KExpr) (e1 : KExpr) (f' : KExpr) (a' : KExpr) ",
            "(h_e1 : Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1)) ",
            "(hmaj_nr : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr) -> ",
            "Eq (OptionType KExpr) (iota_reduct env a) (OptionType.none KExpr)) ",
            "(hf : par_reduces_c env f f') (ha : par_reduces_c env a a') ",
            "(df : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env f s1 -> par_reduces_c env f s2 -> ",
            "par_strips_witness_c_star env s1 s2) ",
            "(da : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env a s1 -> par_reduces_c env a s2 -> ",
            "par_strips_witness_c_star env s1 s2) => ",
            // OptionType.rec on iota_reduct env f with an equation-carrying motive.
            "OptionType.rec KExpr ",
            "(fun (o : OptionType KExpr) => ",
            "Eq (OptionType KExpr) (iota_reduct env f) o -> ",
            "par_strips_witness_c_star env e1 (KExpr.app f' a')) ",
            "{none_arm} {some_arm} ",
            "(iota_reduct env f) (Eq.refl (OptionType KExpr) (iota_reduct env f))"
        ),
        none_arm = none_arm,
        some_arm = some_arm,
    )
}

/// Closed proof term for `par_strips_c_app_struct` (Increment F final assembly #3,
/// app-headed structural diamond). First leg app f a => app f' a' against an
/// arbitrary second leg inverted via par_reduces_c_app_inv (kcong/kbeta/kiota).
fn par_strips_c_app_struct_proof() -> String {
    // kcong (app, app): second leg app f a => app f2 a2. Meet via the diagonal on
    // the f-/a-sub-diamonds.
    let kcong = concat!(
        "(fun (f2 : KExpr) (a2 : KExpr) ",
        "(hf2 : par_reduces_c env f f2) (ha2 : par_reduces_c env a a2) => ",
        "par_strips_witness_c_star_app env f' f2 a' a2 ",
        "(df f' f2 hf hf2) (da a' a2 ha ha2))"
    );

    // kbeta (app, beta): f = lam A bdy, second reduct instantiate body2 arg2.
    // Recover f' = lam Af bodyf from hf : par_reduces_c (lam A bdy) f' via lam_inv_eq;
    // body meet from the f-sub-diamond df f' (lam A' body2) + lam_meet; arg meet from
    // the a-sub-diamond da a' arg2; assemble via par_strips_c_app_beta and transport
    // the redex head app (lam Af bodyf) a' back to app f' a'.
    let kbeta = concat!(
        "(fun (A : KExpr) (A' : KExpr) (bdy : KExpr) (bdy' : KExpr) (arg' : KExpr) ",
        "(eqf : Eq KExpr f (KExpr.lam A bdy)) ",
        "(hA : par_reduces_c env A A') (hbody : par_reduces_c env bdy bdy') ",
        "(harg : par_reduces_c env a arg') => ",
        // hf_lam : par_reduces_c (lam A bdy) f'
        "par_reduces_c_lam_inv_eq env A bdy f' ",
        "(par_strips_witness_c_star env (KExpr.app f' a') (instantiate bdy' arg')) ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x f') f (KExpr.lam A bdy) eqf hf) ",
        "(fun (Af : KExpr) (bodyf : KExpr) ",
        "(eqfp : Eq KExpr f' (KExpr.lam Af bodyf)) ",
        "(_hAf : par_reduces_c env A Af) (_hbf : par_reduces_c env bdy bodyf) => ",
        // wf : par_strips_witness_c_star f' (lam A' bdy') via the f-sub-diamond
        //   df f' (lam A' bdy') hf (lam congruence A=>A', bdy=>bdy')
        //   then transport f' -> lam Af bodyf for lam_meet.
        // Build wf' : par_strips_witness_c_star (lam Af bodyf) (lam A' bdy')
        //   = substType (df f' (lam A' bdy') hf (par_reduces_c.lam ...)) along eqfp.
        // body meet = lam_meet wf'.
        // result : par_strips_witness_c_star (app (lam Af bodyf) a') (instantiate bdy' arg')
        //   via par_strips_c_app_beta; transport head lam Af bodyf -> f' by symm eqfp.
        "Eq.substType KExpr ",
        "(fun (x : KExpr) => par_strips_witness_c_star env (KExpr.app x a') (instantiate bdy' arg')) ",
        "(KExpr.lam Af bodyf) f' (Eq.symm KExpr f' (KExpr.lam Af bodyf) eqfp) ",
        "(par_strips_c_app_beta env Af bodyf a' bdy' arg' closed liftclosed ",
        // body sub-diamond bodyf vs bdy':
        "(par_strips_witness_c_star_lam_meet env Af A' bodyf bdy' ",
        "(Eq.substType KExpr ",
        "(fun (x : KExpr) => par_strips_witness_c_star env x (KExpr.lam A' bdy')) f' (KExpr.lam Af bodyf) eqfp ",
        "(df f' (KExpr.lam A' bdy') hf ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x (KExpr.lam A' bdy')) ",
        "(KExpr.lam A bdy) f (Eq.symm KExpr f (KExpr.lam A bdy) eqf) ",
        "(par_reduces_c.lam env A A' bdy bdy' hA hbody))))) ",
        // arg sub-diamond a' vs arg':
        "(da a' arg' ha harg))))"
    );

    // kiota (app, iota): second leg iota_step env (app f a) t0, e2 = t0. Route to
    // par_strips_iota_target_c under the guard. par_strips_iota_target_c gives
    // par_strips_witness_c_star (app f' a') t0; transport t0 -> e2 along (symm eqt).
    let kiota = concat!(
        "(fun (t0 : KExpr) (hi : iota_step env (KExpr.app f a) t0) (_eqt : Eq KExpr e2 t0) => ",
        "par_strips_iota_target_c env (KExpr.app f a) (KExpr.app f' a') t0 ",
        "(par_reduces_c.app env f f' a a' hf ha) hi guard)"
    );

    format!(
        concat!(
            "fun (env : RecEnv) (f : KExpr) (a : KExpr) (f' : KExpr) (a' : KExpr) (e2 : KExpr) ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) ",
            "(hf : par_reduces_c env f f') (ha : par_reduces_c env a a') ",
            "(h2 : par_reduces_c env (KExpr.app f a) e2) ",
            "(guard : minimal_or_inner env (KExpr.app f a) (KExpr.app f' a')) ",
            "(df : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env f s1 -> par_reduces_c env f s2 -> ",
            "par_strips_witness_c_star env s1 s2) ",
            "(da : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env a s1 -> par_reduces_c env a s2 -> ",
            "par_strips_witness_c_star env s1 s2) => ",
            "par_reduces_c_app_inv env f a e2 ",
            "(fun (x : KExpr) => par_strips_witness_c_star env (KExpr.app f' a') x) ",
            "h2 {kcong} {kbeta} {kiota}"
        ),
        kcong = kcong,
        kbeta = kbeta,
        kiota = kiota,
    )
}

/// Closed proof term for the pi/forall structural diamonds
/// `par_strips_c_struct_{pi,forall}` (Increment F final assembly #3), parametric in
/// the binder head, the matching inversion, and the matching diagonal. Same shape as
/// par_strips_c_struct_lam_proof.
fn par_strips_c_struct_binder_proof(head: &str, inv: &str, diag: &str) -> String {
    format!(
        concat!(
            "fun (env : RecEnv) (dom : KExpr) (body : KExpr) (e1 : KExpr) (e2 : KExpr) ",
            "(h1 : par_reduces_c env ({head} dom body) e1) ",
            "(h2 : par_reduces_c env ({head} dom body) e2) ",
            "(ddom : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env dom s1 -> par_reduces_c env dom s2 -> ",
            "par_strips_witness_c_star env s1 s2) ",
            "(dbody : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env body s1 -> par_reduces_c env body s2 -> ",
            "par_strips_witness_c_star env s1 s2) => ",
            "{inv} env dom body e1 ",
            "(fun (x : KExpr) => par_strips_witness_c_star env x e2) ",
            "h1 ",
            "(fun (dom1 : KExpr) (body1 : KExpr) ",
            "(hdom1 : par_reduces_c env dom dom1) (hbody1 : par_reduces_c env body body1) => ",
            "{inv} env dom body e2 ",
            "(fun (y : KExpr) => par_strips_witness_c_star env ({head} dom1 body1) y) ",
            "h2 ",
            "(fun (dom2 : KExpr) (body2 : KExpr) ",
            "(hdom2 : par_reduces_c env dom dom2) (hbody2 : par_reduces_c env body body2) => ",
            "{diag} env dom1 dom2 body1 body2 ",
            "(ddom dom1 dom2 hdom1 hdom2) (dbody body1 body2 hbody1 hbody2)))"
        ),
        head = head,
        inv = inv,
        diag = diag,
    )
}

/// Closed proof term for `par_strips_c_struct_lam` (Increment F final assembly #3,
/// lam-headed structural diamond). Inverts both lam-headed legs via
/// par_reduces_c_lam_inv (CPS), applies the caller-supplied ty/body sub-diamonds,
/// and assembles via par_strips_witness_c_star_lam.
fn par_strips_c_struct_lam_proof() -> String {
    // Invert the first leg: par_reduces_c (lam ty body) e1 -> klam1 (e1 = lam s1 s1b).
    // Inside, invert the second leg similarly, then assemble.
    concat!(
        "fun (env : RecEnv) (ty : KExpr) (body : KExpr) (e1 : KExpr) (e2 : KExpr) ",
        "(h1 : par_reduces_c env (KExpr.lam ty body) e1) ",
        "(h2 : par_reduces_c env (KExpr.lam ty body) e2) ",
        "(dty : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env ty s1 -> par_reduces_c env ty s2 -> ",
        "par_strips_witness_c_star env s1 s2) ",
        "(dbody : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env body s1 -> par_reduces_c env body s2 -> ",
        "par_strips_witness_c_star env s1 s2) => ",
        // invert h1
        "par_reduces_c_lam_inv env ty body e1 ",
        "(fun (x : KExpr) => par_strips_witness_c_star env x e2) ",
        "h1 ",
        "(fun (ty1 : KExpr) (body1 : KExpr) ",
        "(hty1 : par_reduces_c env ty ty1) (hbody1 : par_reduces_c env body body1) => ",
        // now goal: par_strips_witness_c_star env (lam ty1 body1) e2; invert h2
        "par_reduces_c_lam_inv env ty body e2 ",
        "(fun (y : KExpr) => par_strips_witness_c_star env (KExpr.lam ty1 body1) y) ",
        "h2 ",
        "(fun (ty2 : KExpr) (body2 : KExpr) ",
        "(hty2 : par_reduces_c env ty ty2) (hbody2 : par_reduces_c env body body2) => ",
        // goal: par_strips_witness_c_star env (lam ty1 body1) (lam ty2 body2)
        "par_strips_witness_c_star_lam env ty1 ty2 body1 body2 ",
        "(dty ty1 ty2 hty1 hty2) (dbody body1 body2 hbody1 hbody2)))"
    )
    .to_string()
}

/// Closed proof term for `par_strips_c_subst_join` (Increment F final assembly
/// #3e): the contraction meet combinator. Projects the body sub-diamond to b3 and
/// the arg sub-diamond to a3 (nested par_strips_witness_c_star.rec), assembling the
/// meet at instantiate b3 a3 via par_subst_full_c_star on each side. Mirror of
/// par_strips_bd_proof's `mk_join` at the _star witness level.
fn par_strips_c_subst_join_proof() -> String {
    let wa_rec = concat!(
        "(@par_strips_witness_c_star.rec env la ra ",
        "(fun (_wa : par_strips_witness_c_star env la ra) => ",
        "par_strips_witness_c_star env (instantiate lb la) (instantiate rb ra)) ",
        "(fun (a3 : KExpr) ",
        "(pa1 : par_reduces_c_star env la a3) (pa2 : par_reduces_c_star env ra a3) => ",
        "par_strips_witness_c_star.intro env (instantiate lb la) (instantiate rb ra) ",
        "(instantiate b3 a3) ",
        "(par_subst_full_c_star env lb b3 la a3 Nat.zero pb1 pa1 closed liftclosed) ",
        "(par_subst_full_c_star env rb b3 ra a3 Nat.zero pb2 pa2 closed liftclosed)) ",
        "wa)"
    );
    let body_rec = format!(
        concat!(
            "(@par_strips_witness_c_star.rec env lb rb ",
            "(fun (_wb : par_strips_witness_c_star env lb rb) => ",
            "par_strips_witness_c_star env (instantiate lb la) (instantiate rb ra)) ",
            "(fun (b3 : KExpr) ",
            "(pb1 : par_reduces_c_star env lb b3) (pb2 : par_reduces_c_star env rb b3) => ",
            "{wa_rec}) ",
            "wb)"
        ),
        wa_rec = wa_rec,
    );
    format!(
        concat!(
            "fun (env : RecEnv) (lb : KExpr) (rb : KExpr) (la : KExpr) (ra : KExpr) ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) ",
            "(wb : par_strips_witness_c_star env lb rb) ",
            "(wa : par_strips_witness_c_star env la ra) => ",
            "{body_rec}"
        ),
        body_rec = body_rec,
    )
}

/// Closed proof term for `par_reduces_c_star_lam_inv_eq` (Increment F final
/// assembly #3c). par_reduces_c_star.rec with an accumulator motive that carries
/// "source = lam ty0 body0"; the step arm single-step inverts the head via
/// par_reduces_c_lam_inv_eq and prepends to the IH's accumulated star congruences.
fn par_reduces_c_star_lam_inv_eq_proof() -> String {
    // Kont(R) := forall ty' body', Eq R (lam ty' body') -> (ty0 =>* ty') -> (body0 =>* body') -> C
    // (parameterized by the running source binders ty0/body0 via the motive).
    // Motive: M s t _ := forall ty0 body0, Eq s (lam ty0 body0) ->
    //   (forall ty' body', Eq t (lam ty' body') -> ty0 =>* ty' -> body0 =>* body' -> C) -> C
    let motive = concat!(
        "(fun (s : KExpr) (tt : KExpr) (_h : par_reduces_c_star env s tt) => ",
        "forall (ty0 : KExpr) (body0 : KExpr), Eq KExpr s (KExpr.lam ty0 body0) -> ",
        "(forall (ty' : KExpr) (body' : KExpr), Eq KExpr tt (KExpr.lam ty' body') -> ",
        "par_reduces_c_star env ty0 ty' -> par_reduces_c_star env body0 body' -> C) -> C)"
    );

    // refl arm: s = tt = e. Given eqs : Eq e (lam ty0 body0) and k, call k with
    // ty' = ty0, body' = body0 (reduct eq = eqs), congruences refl-star.
    let refl_arm = concat!(
        "(fun (e : KExpr) (ty0 : KExpr) (body0 : KExpr) ",
        "(eqs : Eq KExpr e (KExpr.lam ty0 body0)) ",
        "(k : forall (ty' : KExpr) (body' : KExpr), Eq KExpr e (KExpr.lam ty' body') -> ",
        "par_reduces_c_star env ty0 ty' -> par_reduces_c_star env body0 body' -> C) => ",
        "k ty0 body0 eqs (par_reduces_c_star.refl env ty0) (par_reduces_c_star.refl env body0))"
    );

    // step arm: s => smid =>* tt. Transport hstep along eqs to a step from
    // (lam ty0 body0), single-step invert (par_reduces_c_lam_inv_eq) to learn
    // smid = lam tym bodym with ty0 => tym, body0 => bodym; apply IH (smid known
    // lam) and prepend the single steps to its accumulated star congruences.
    let step_arm = concat!(
        "(fun (s : KExpr) (smid : KExpr) (tt : KExpr) ",
        "(hstep : par_reduces_c env s smid) (_htail : par_reduces_c_star env smid tt) ",
        "(ih : forall (ty0 : KExpr) (body0 : KExpr), Eq KExpr smid (KExpr.lam ty0 body0) -> ",
        "(forall (ty' : KExpr) (body' : KExpr), Eq KExpr tt (KExpr.lam ty' body') -> ",
        "par_reduces_c_star env ty0 ty' -> par_reduces_c_star env body0 body' -> C) -> C) ",
        "(ty0 : KExpr) (body0 : KExpr) (eqs : Eq KExpr s (KExpr.lam ty0 body0)) ",
        "(k : forall (ty' : KExpr) (body' : KExpr), Eq KExpr tt (KExpr.lam ty' body') -> ",
        "par_reduces_c_star env ty0 ty' -> par_reduces_c_star env body0 body' -> C) => ",
        // hstep' : par_reduces_c (lam ty0 body0) smid
        "par_reduces_c_lam_inv_eq env ty0 body0 smid C ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x smid) s (KExpr.lam ty0 body0) eqs hstep) ",
        "(fun (tym : KExpr) (bodym : KExpr) ",
        "(eqmid : Eq KExpr smid (KExpr.lam tym bodym)) ",
        "(htm : par_reduces_c env ty0 tym) (hbm : par_reduces_c env body0 bodym) => ",
        "ih tym bodym eqmid ",
        "(fun (ty' : KExpr) (body' : KExpr) (eqt : Eq KExpr tt (KExpr.lam ty' body')) ",
        "(h_tym : par_reduces_c_star env tym ty') (h_bodym : par_reduces_c_star env bodym body') => ",
        "k ty' body' eqt ",
        "(par_reduces_c_star.step env ty0 tym ty' htm h_tym) ",
        "(par_reduces_c_star.step env body0 bodym body' hbm h_bodym))))"
    );

    format!(
        concat!(
            "fun (env : RecEnv) (ty : KExpr) (body : KExpr) (t : KExpr) (C : Type) ",
            "(h : par_reduces_c_star env (KExpr.lam ty body) t) ",
            "(klam : forall (ty' : KExpr) (body' : KExpr), Eq KExpr t (KExpr.lam ty' body') -> ",
            "par_reduces_c_star env ty ty' -> par_reduces_c_star env body body' -> C) => ",
            "par_reduces_c_star.rec env {motive} {refl_arm} {step_arm} ",
            "(KExpr.lam ty body) t h ty body (Eq.refl KExpr (KExpr.lam ty body)) klam"
        ),
        motive = motive,
        refl_arm = refl_arm,
        step_arm = step_arm,
    )
}

/// Closed proof term for `par_strips_witness_c_star_lam_meet` (Increment F final
/// assembly #3d). Projects the lam-lam star-witness to its common reduct g3,
/// Eq-inverts both star legs (par_reduces_c_star_lam_inv_eq) to lam shapes,
/// identifies the body meet via lam_inj_snd + Eq.trans, and meets the bodies there.
/// Mirror of par_strips_witness_bd_lam_meet_proof at the _star level.
fn par_strips_witness_c_star_lam_meet_proof() -> String {
    // Inner continuation (after both inversions): build the body meet at bA.
    let inner_k = concat!(
        "(fun (tB : KExpr) (bB : KExpr) ",
        "(eqB : Eq KExpr g3 (KExpr.lam tB bB)) ",
        "(_ht2 : par_reduces_c_star env t2 tB) (hb2 : par_reduces_c_star env b2 bB) => ",
        "par_strips_witness_c_star.intro env b1 b2 bA hb1 ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c_star env b2 x) bB bA ",
        "(lam_inj_snd tB bB tA bA ",
        "(Eq.trans KExpr (KExpr.lam tB bB) g3 (KExpr.lam tA bA) ",
        "(Eq.symm KExpr g3 (KExpr.lam tB bB) eqB) eqA)) ",
        "hb2))"
    );
    // Outer continuation (after inverting p1): invert p2 at the same reduct g3.
    let outer_k = format!(
        concat!(
            "(fun (tA : KExpr) (bA : KExpr) ",
            "(eqA : Eq KExpr g3 (KExpr.lam tA bA)) ",
            "(_ht1 : par_reduces_c_star env t1 tA) (hb1 : par_reduces_c_star env b1 bA) => ",
            "par_reduces_c_star_lam_inv_eq env t2 b2 g3 (par_strips_witness_c_star env b1 b2) p2 {inner_k})"
        ),
        inner_k = inner_k,
    );
    format!(
        concat!(
            "fun (env : RecEnv) (t1 : KExpr) (t2 : KExpr) (b1 : KExpr) (b2 : KExpr) ",
            "(w : par_strips_witness_c_star env (KExpr.lam t1 b1) (KExpr.lam t2 b2)) => ",
            "@par_strips_witness_c_star.rec env (KExpr.lam t1 b1) (KExpr.lam t2 b2) ",
            "(fun (_w : par_strips_witness_c_star env (KExpr.lam t1 b1) (KExpr.lam t2 b2)) => ",
            "par_strips_witness_c_star env b1 b2) ",
            "(fun (g3 : KExpr) ",
            "(p1 : par_reduces_c_star env (KExpr.lam t1 b1) g3) ",
            "(p2 : par_reduces_c_star env (KExpr.lam t2 b2) g3) => ",
            "par_reduces_c_star_lam_inv_eq env t1 b1 g3 (par_strips_witness_c_star env b1 b2) p1 {outer_k}) ",
            "w"
        ),
        outer_k = outer_k,
    )
}

/// Closed proof term for `par_strips_c_app_beta` (Increment F final assembly #3a):
/// the (app, beta) cross core at the star-witness level. Projects the body and arg
/// sub-diamonds to their meets b3 / a3 (nested par_strips_witness_c_star.rec) and
/// assembles the meet at instantiate b3 a3 via par_reduces_c_star_beta (left) and
/// par_subst_full_c_star (right). Mirror of par_strips_bd_app_beta_proof at the
/// _star witness level.
fn par_strips_c_app_beta_proof() -> String {
    // Inner (arg) recursor: project wa to a3, build the meet.
    let wa_rec = concat!(
        "(@par_strips_witness_c_star.rec env a0p argp ",
        "(fun (_wa : par_strips_witness_c_star env a0p argp) => ",
        "par_strips_witness_c_star env (KExpr.app (KExpr.lam Af bodyf) a0p) (instantiate bodyq argp)) ",
        "(fun (a3 : KExpr) ",
        "(pa1 : par_reduces_c_star env a0p a3) (pa2 : par_reduces_c_star env argp a3) => ",
        "par_strips_witness_c_star.intro env ",
        "(KExpr.app (KExpr.lam Af bodyf) a0p) (instantiate bodyq argp) ",
        "(instantiate b3 a3) ",
        // left leg: app (lam Af bodyf) a0p =>* instantiate b3 a3
        "(par_reduces_c_star_beta env Af Af bodyf b3 a0p a3 ",
        "(par_reduces_c_star.refl env Af) pbf pa1) ",
        // right leg: instantiate bodyq argp =>* instantiate b3 a3
        "(par_subst_full_c_star env bodyq b3 argp a3 Nat.zero pbq pa2 closed liftclosed)) ",
        "wa)"
    );
    // Outer (body) recursor: project wb to b3, run wa inside.
    let body_rec = format!(
        concat!(
            "(@par_strips_witness_c_star.rec env bodyf bodyq ",
            "(fun (_wb : par_strips_witness_c_star env bodyf bodyq) => ",
            "par_strips_witness_c_star env (KExpr.app (KExpr.lam Af bodyf) a0p) (instantiate bodyq argp)) ",
            "(fun (b3 : KExpr) ",
            "(pbf : par_reduces_c_star env bodyf b3) (pbq : par_reduces_c_star env bodyq b3) => ",
            "{wa_rec}) ",
            "wb)"
        ),
        wa_rec = wa_rec,
    );
    format!(
        concat!(
            "fun (env : RecEnv) (Af : KExpr) (bodyf : KExpr) (a0p : KExpr) ",
            "(bodyq : KExpr) (argp : KExpr) ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) ",
            "(wb : par_strips_witness_c_star env bodyf bodyq) ",
            "(wa : par_strips_witness_c_star env a0p argp) => ",
            "{body_rec}"
        ),
        body_rec = body_rec,
    )
}

/// Closed proof term for `par_reduces_c_lam_inv_eq` (Increment F final assembly #3b):
/// Eq-data lam inversion over par_reduces_c. From par_reduces_c (lam ty body) t,
/// hand the continuation Eq t (lam ty' body') with ty => ty' and body => body'.
/// Mirror of par_reduces_bd_lam_inv_eq_proof over par_reduces_c + the iota arm
/// (discharged because a binder head cannot be an iota redex). The motive returns
/// Eq e (lam ty body) -> Kont e' -> C with Kont parameterized by the arm reduct.
fn par_reduces_c_lam_inv_eq_proof() -> String {
    // Kont(R) := forall ty' body', Eq R (lam ty' body') -> (ty=>ty') -> (body=>body') -> C
    let kont = |reduct: &str| -> String {
        format!(
            concat!(
                "(forall (ty' : KExpr) (body' : KExpr), ",
                "Eq KExpr {reduct} (KExpr.lam ty' body') -> ",
                "par_reduces_c env ty ty' -> par_reduces_c env body body' -> C)"
            ),
            reduct = reduct,
        )
    };
    let motive = format!(
        concat!(
            "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_c env e e') => ",
            "Eq KExpr e (KExpr.lam ty body) -> {kont} -> C)"
        ),
        kont = kont("e'"),
    );

    // refl arm: source e, reduct e. k expects Eq e (lam ty' body'); take ty'=ty,
    // body'=body so the equation is eq, sub-derivs refl.
    let refl_arm = format!(
        concat!(
            "(fun (e : KExpr) (eq : Eq KExpr e (KExpr.lam ty body)) ",
            "(k : {kont}) => ",
            "k ty body eq (par_reduces_c.refl env ty) (par_reduces_c.refl env body))"
        ),
        kont = kont("e"),
    );

    // lam arm: source lam t0 b0, reduct lam t0' b0' — the genuine match.
    let lam_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(ht : par_reduces_c env t0 t0') (hb : par_reduces_c env b0 b0') ",
            "(_iht : Eq KExpr t0 (KExpr.lam ty body) -> {kont_t0} -> C) ",
            "(_ihb : Eq KExpr b0 (KExpr.lam ty body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.lam t0 b0) (KExpr.lam ty body)) ",
            "(k : {kont_red}) => ",
            "k t0' b0' (Eq.refl KExpr (KExpr.lam t0' b0')) ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x t0') t0 ty ",
            "(lam_inj_fst t0 b0 ty body eq) ht) ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x b0') b0 body ",
            "(lam_inj_snd t0 b0 ty body eq) hb))"
        ),
        kont_t0 = kont("t0'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(KExpr.lam t0' b0')"),
    );

    // beta arm: source app (lam A b0) arg — app /= lam.
    let beta_arm = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(arg : KExpr) (arg' : KExpr) ",
            "(_hA : par_reduces_c env A A') (_hb0 : par_reduces_c env b0 b0') ",
            "(_harg : par_reduces_c env arg arg') ",
            "(_ihA : Eq KExpr A (KExpr.lam ty body) -> {kont_A} -> C) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> {kont_b0} -> C) ",
            "(_iharg : Eq KExpr arg (KExpr.lam ty body) -> {kont_arg} -> C) ",
            "(eq : Eq KExpr (KExpr.app (KExpr.lam A b0) arg) (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "app_ne_lam (KExpr.lam A b0) arg ty body C eq)"
        ),
        kont_A = kont("A'"),
        kont_b0 = kont("b0'"),
        kont_arg = kont("arg'"),
        kont_red = kont("(instantiate b0' arg')"),
    );

    // app arm: source app g b — app /= lam.
    let app_arm = format!(
        concat!(
            "(fun (g : KExpr) (g' : KExpr) (b : KExpr) (b' : KExpr) ",
            "(_hg : par_reduces_c env g g') (_hb : par_reduces_c env b b') ",
            "(_ihg : Eq KExpr g (KExpr.lam ty body) -> {kont_g} -> C) ",
            "(_ihb : Eq KExpr b (KExpr.lam ty body) -> {kont_b} -> C) ",
            "(eq : Eq KExpr (KExpr.app g b) (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "app_ne_lam g b ty body C eq)"
        ),
        kont_g = kont("g'"),
        kont_b = kont("b'"),
        kont_red = kont("(KExpr.app g' b')"),
    );

    // pi arm: source pi dom b0 — pi /= lam.
    let pi_arm = format!(
        concat!(
            "(fun (dom : KExpr) (dom' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_hd : par_reduces_c env dom dom') (_hb0 : par_reduces_c env b0 b0') ",
            "(_ihd : Eq KExpr dom (KExpr.lam ty body) -> {kont_d} -> C) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.pi dom b0) (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "pi_ne_lam dom b0 ty body C eq)"
        ),
        kont_d = kont("dom'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(KExpr.pi dom' b0')"),
    );

    // forall_ arm: source forall_ dom b0 = pi dom b0 (alias) — pi /= lam.
    let forall_arm = format!(
        concat!(
            "(fun (dom : KExpr) (dom' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_hd : par_reduces_c env dom dom') (_hb0 : par_reduces_c env b0 b0') ",
            "(_ihd : Eq KExpr dom (KExpr.lam ty body) -> {kont_d} -> C) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.forall_ dom b0) (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "pi_ne_lam dom b0 ty body C eq)"
        ),
        kont_d = kont("dom'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(KExpr.forall_ dom' b0')"),
    );

    // let_ (zeta) arm: source let_ t0 v b0 — a GENUINE let node, let /= lam.
    let let_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_c env t0 t0') (_hv : par_reduces_c env v v') ",
            "(_hb0 : par_reduces_c env b0 b0') ",
            "(_iht0 : Eq KExpr t0 (KExpr.lam ty body) -> {kont_t0} -> C) ",
            "(_ihv : Eq KExpr v (KExpr.lam ty body) -> {kont_v} -> C) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "let_ne_lam t0 v b0 ty body C eq)"
        ),
        kont_t0 = kont("t0'"),
        kont_v = kont("v'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(instantiate b0' v')"),
    );

    // let_cong arm: source let_ t0 v b0 — a GENUINE let node, let /= lam.
    let let_cong_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_c env t0 t0') (_hv : par_reduces_c env v v') ",
            "(_hb0 : par_reduces_c env b0 b0') ",
            "(_iht0 : Eq KExpr t0 (KExpr.lam ty body) -> {kont_t0} -> C) ",
            "(_ihv : Eq KExpr v (KExpr.lam ty body) -> {kont_v} -> C) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "let_ne_lam t0 v b0 ty body C eq)"
        ),
        kont_t0 = kont("t0'"),
        kont_v = kont("v'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(KExpr.let_ t0' v' b0')"),
    );

    // iota arm: source e0 with iota_step env e0 e0'. Transport to the lam head
    // (Eq.subst along eq), then discharge — a binder head is not a const head.
    let iota_arm = format!(
        concat!(
            "(fun (e0 : KExpr) (e0' : KExpr) (hstep : iota_step env e0 e0') ",
            "(eq : Eq KExpr e0 (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "iota_step_head_none_absurd_type env (KExpr.lam ty body) e0' C ",
            "(Eq.refl (OptionType Name) (OptionType.none Name)) ",
            "(Eq.subst KExpr (fun (x : KExpr) => iota_step env x e0') e0 (KExpr.lam ty body) eq hstep))"
        ),
        kont_red = kont("e0'"),
    );

    // proj arm: source proj s i sub is proj-headed — proj /= lam via proj_ne_lam.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
            "(_hsub : par_reduces_c env sub sub') ",
            "(_ihsub : Eq KExpr sub (KExpr.lam ty body) -> {kont_sub} -> C) ",
            "(eq : Eq KExpr (KExpr.proj s i sub) (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "proj_ne_lam s i sub ty body C eq)"
        ),
        kont_sub = kont("sub'"),
        kont_red = kont("(KExpr.proj s i sub')"),
    );

    format!(
        concat!(
            "fun (env : RecEnv) (ty : KExpr) (body : KExpr) (t : KExpr) (C : Type) ",
            "(h : par_reduces_c env (KExpr.lam ty body) t) ",
            "(klam : {kont_t}) => ",
            "par_reduces_c.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} ",
            "(KExpr.lam ty body) t h (Eq.refl KExpr (KExpr.lam ty body)) klam"
        ),
        kont_t = kont("t"),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = lam_arm,
        pi_arm = pi_arm,
        forall_arm = forall_arm,
        let_arm = let_arm,
        iota_arm = iota_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for `par_subst_c` (Phase 2). Mirrors `par_subst_bd_proof`'s
/// `par_reduces_*.rec` structure, but (1) concludes `par_reduces_c_star` (the iota
/// arm is intrinsically 2-step), (2) threads `RecEnvClosed env` through the motive
/// for the iota arm, and (3) adds the iota constructor arm via `par_subst_iota_arm_c`.
fn par_subst_c_proof() -> String {
    // Depth-generalized, _star-valued motive (threads par_reduces_bd v v' and
    // RecEnvClosed env so every arm — in particular iota — has them).
    let motive = concat!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_c env e e') => ",
        "forall (v : KExpr) (v' : KExpr) (d : Nat), par_reduces_bd v v' -> RecEnvClosed env -> ",
        "par_reduces_c_star env (instantiate_at e v d) (instantiate_at e' v' d))"
    );
    // IH shape for a sub-derivation SUB => SUB'.
    let ih = concat!(
        "forall (v : KExpr) (v' : KExpr) (d : Nat), par_reduces_bd v v' -> RecEnvClosed env -> ",
        "par_reduces_c_star env (instantiate_at SUB v d) (instantiate_at SUB' v' d)"
    );

    // refl arm: par_subst_refl_c, lifted to _star.
    let refl_arm = concat!(
        "(fun (e : KExpr) (v : KExpr) (v' : KExpr) (d : Nat) ",
        "(h : par_reduces_bd v v') (_closed : RecEnvClosed env) => ",
        "par_subsumes_par_c_star env (instantiate_at e v d) (instantiate_at e v' d) ",
        "(par_subst_refl_c env e v v' d h))"
    );

    // app arm.
    let app_arm = format!(
        concat!(
            "(fun (f : KExpr) (f' : KExpr) (a0 : KExpr) (a0' : KExpr) ",
            "(_hf : par_reduces_c env f f') (_ha : par_reduces_c env a0 a0') ",
            "(ihf : {ih_f}) (iha : {ih_a}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_bd v v') (closed : RecEnvClosed env) => ",
            "par_reduces_c_star_app env ",
            "(instantiate_at f v d) (instantiate_at f' v' d) ",
            "(instantiate_at a0 v d) (instantiate_at a0' v' d) ",
            "(ihf v v' d h closed) (iha v v' d h closed))"
        ),
        ih_f = ih.replace("SUB'", "f'").replace("SUB", "f"),
        ih_a = ih.replace("SUB'", "a0'").replace("SUB", "a0"),
    );

    // lam/pi/forall_ congruence arm, parametric in the _star congruence lemma.
    let binder_arm = |star_cong: &str| -> String {
        format!(
            concat!(
                "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                "(_hty : par_reduces_c env ty ty') (_hbody : par_reduces_c env body body') ",
                "(ihty : {ih_ty}) (ihbody : {ih_body}) ",
                "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_bd v v') (closed : RecEnvClosed env) => ",
                "{star_cong} env ",
                "(instantiate_at ty v d) (instantiate_at ty' v' d) ",
                "(instantiate_at body v (Nat.succ d)) (instantiate_at body' v' (Nat.succ d)) ",
                "(ihty v v' d h closed) (ihbody v v' (Nat.succ d) h closed))"
            ),
            ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
            ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
            star_cong = star_cong,
        )
    };

    // beta/let_ contraction transport (mirror of par_subst_bd's `contract`, but
    // at the _star level). The _star contraction congruence (star_beta/star_let)
    // concludes ... =>* instantiate (inst BODYP v' (succ d)) (inst ARGP v' d); the
    // goal RHS is instantiate_at (instantiate BODYP ARGP) v' d. The lemma
    // instantiate_nested_commutes_zero_subst BODYP ARGP v' d bridges them.
    //   lhs_head  = the (defeq) reduced source redex (= instantiate_at SRC v d)
    //   star_term = the par_reduces_c_star ... (instantiate (inst BODYP v' (succ d))
    //               (inst ARGP v' d)) built from the _star contraction congruence
    //   bodyp/argp = BODYP, ARGP (e.g. body', arg' / body', val').
    let contract = |lhs_head: &str, star_term: &str, bodyp: &str, argp: &str| -> String {
        let goal_rhs = format!(
            "(instantiate_at (instantiate_at {bodyp} {argp} Nat.zero) v' d)",
            bodyp = bodyp,
            argp = argp,
        );
        let star_rhs = format!(
            concat!(
                "(instantiate_at (instantiate_at {bodyp} v' (Nat.succ d)) ",
                "(instantiate_at {argp} v' d) Nat.zero)"
            ),
            bodyp = bodyp,
            argp = argp,
        );
        let eq = format!(
            "(instantiate_nested_commutes_zero_subst {bodyp} {argp} v' d)",
            bodyp = bodyp,
            argp = argp,
        );
        // P x := par_reduces_c_star env lhs_head x. star_term : P star_rhs ;
        // want P goal_rhs ; transport with Eq.symm eq.
        format!(
            concat!(
                "(Eq.substType KExpr ",
                "(fun (x : KExpr) => par_reduces_c_star env {lhs_head} x) ",
                "{star_rhs} {goal_rhs} ",
                "(Eq.symm KExpr {goal_rhs} {star_rhs} {eq}) ",
                "{star_term})"
            ),
            lhs_head = lhs_head,
            star_rhs = star_rhs,
            goal_rhs = goal_rhs,
            eq = eq,
            star_term = star_term,
        )
    };

    // beta arm.
    let beta_lhs_head = concat!(
        "(KExpr.app ",
        "(KExpr.lam (instantiate_at A v d) (instantiate_at body v (Nat.succ d))) ",
        "(instantiate_at arg v d))"
    );
    let beta_star = concat!(
        "(par_reduces_c_star_beta env ",
        "(instantiate_at A v d) (instantiate_at A' v' d) ",
        "(instantiate_at body v (Nat.succ d)) (instantiate_at body' v' (Nat.succ d)) ",
        "(instantiate_at arg v d) (instantiate_at arg' v' d) ",
        "(ihA v v' d h closed) (ihbody v v' (Nat.succ d) h closed) (iharg v v' d h closed))"
    );
    let beta_arm = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) ",
            "(arg : KExpr) (arg' : KExpr) ",
            "(_hA : par_reduces_c env A A') (_hbody : par_reduces_c env body body') ",
            "(_harg : par_reduces_c env arg arg') ",
            "(ihA : {ih_A}) (ihbody : {ih_body}) (iharg : {ih_arg}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_bd v v') (closed : RecEnvClosed env) => {body})"
        ),
        ih_A = ih.replace("SUB'", "A'").replace("SUB", "A"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
        ih_arg = ih.replace("SUB'", "arg'").replace("SUB", "arg"),
        body = contract(beta_lhs_head, beta_star, "body'", "arg'"),
    );

    // let_ (zeta) arm: the substituted redex skeleton is the GENUINE let node
    // (instantiate_at distributes over the let_ ctor since the let-promotion —
    // ty/val at depth d, body at succ d), then the beta-shaped contraction
    // transport with arg := val.
    let let_lhs_head = concat!(
        "(KExpr.let_ ",
        "(instantiate_at ty v d) (instantiate_at val v d) ",
        "(instantiate_at body v (Nat.succ d)))"
    );
    let let_star = concat!(
        "(par_reduces_c_star_let env ",
        "(instantiate_at ty v d) (instantiate_at ty' v' d) ",
        "(instantiate_at val v d) (instantiate_at val' v' d) ",
        "(instantiate_at body v (Nat.succ d)) (instantiate_at body' v' (Nat.succ d)) ",
        "(ihty v v' d h closed) (ihval v v' d h closed) (ihbody v v' (Nat.succ d) h closed))"
    );
    let let_arm = format!(
        concat!(
            "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
            "(body : KExpr) (body' : KExpr) ",
            "(_hty : par_reduces_c env ty ty') (_hval : par_reduces_c env val val') ",
            "(_hbody : par_reduces_c env body body') ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_bd v v') (closed : RecEnvClosed env) => {body})"
        ),
        ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
        ih_val = ih.replace("SUB'", "val'").replace("SUB", "val"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
        body = contract(let_lhs_head, let_star, "body'", "val'"),
    );

    // let_cong arm: instantiate_at distributes over the genuine let node
    // componentwise; par_reduces_c_star_let_cong on the three IHs (no transport).
    let let_cong_arm = format!(
        concat!(
            "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
            "(body : KExpr) (body' : KExpr) ",
            "(_hty : par_reduces_c env ty ty') (_hval : par_reduces_c env val val') ",
            "(_hbody : par_reduces_c env body body') ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_bd v v') (closed : RecEnvClosed env) => ",
            "par_reduces_c_star_let_cong env ",
            "(instantiate_at ty v d) (instantiate_at ty' v' d) ",
            "(instantiate_at val v d) (instantiate_at val' v' d) ",
            "(instantiate_at body v (Nat.succ d)) (instantiate_at body' v' (Nat.succ d)) ",
            "(ihty v v' d h closed) (ihval v v' d h closed) (ihbody v v' (Nat.succ d) h closed))"
        ),
        ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
        ih_val = ih.replace("SUB'", "val'").replace("SUB", "val"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
    );

    // iota arm: source e0 => e0' with iota_step env e0 e0'. par_subst_iota_arm_c
    // (the E-core 2-step star) at depth d, using the closed env and the value
    // reduction v => v'. instantiate_at e0/e0' v/v' d are the goal's two indices.
    let iota_arm = concat!(
        "(fun (e0 : KExpr) (e0' : KExpr) (hstep : iota_step env e0 e0') ",
        "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_bd v v') (closed : RecEnvClosed env) => ",
        "par_subst_iota_arm_c env e0 e0' v v' d closed hstep h)"
    );

    // proj arm: subst descends into the scrutinee (instantiate_at (proj s i sub)
    // v d = proj s i (instantiate_at sub v d)); congruence via par_reduces_c_star_proj.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
            "(_hsub : par_reduces_c env sub sub') (ihsub : {ih_sub}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_bd v v') (closed : RecEnvClosed env) => ",
            "par_reduces_c_star_proj env s i ",
            "(instantiate_at sub v d) (instantiate_at sub' v' d) ",
            "(ihsub v v' d h closed))"
        ),
        ih_sub = ih.replace("SUB'", "sub'").replace("SUB", "sub"),
    );

    format!(
        concat!(
            "fun (env : RecEnv) (e0 : KExpr) (e0' : KExpr) (v0 : KExpr) (v0' : KExpr) (d0 : Nat) ",
            "(h_ee : par_reduces_c env e0 e0') (h_vv : par_reduces_bd v0 v0') (closed0 : RecEnvClosed env) => ",
            "par_reduces_c.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} ",
            "e0 e0' h_ee v0 v0' d0 h_vv closed0"
        ),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = binder_arm("par_reduces_c_star_lam"),
        pi_arm = binder_arm("par_reduces_c_star_pi"),
        forall_arm = binder_arm("par_reduces_c_star_forall"),
        let_arm = let_arm,
        iota_arm = iota_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for `par_subst_refl_full_c` (Increment F final assembly #1).
/// The FULL-relation reflexive substitution congruence: substituting a
/// parallel-reducing value `v => v'` (a genuine `par_reduces_c` step, INCLUDING
/// the iota arm) into a FIXED term `e` at depth `d`. Mirrors
/// `par_subst_refl_bd_proof` (the iota-free version) — `KExpr.rec` on `e` with the
/// triple-Nat.rec convoy at the bvar arm — but (1) concludes `par_reduces_c_star`
/// (the bvar arm's `par_lift_full_c` is a single step, the contractions thread
/// through the `_star` congruences), (2) the i=d leaf calls `par_lift_full_c` (the
/// FULL lift congruence, which handles iota in `v`) and subsumes to `_star`, and
/// (3) threads `RecEnvLiftClosed env` (which `par_lift_full_c` gates on).
fn par_subst_refl_full_c_proof() -> String {
    // Motive over the recursed term e: universalize v, v', d; thread RecEnvLiftClosed.
    let motive = concat!(
        "(fun (e : KExpr) => forall (v : KExpr) (v' : KExpr) (d : Nat), ",
        "RecEnvLiftClosed env -> par_reduces_c env v v' -> ",
        "par_reduces_c_star env (instantiate_at e v d) (instantiate_at e v' d))"
    );
    // IH shape for a sub-term SUB.
    let ih = concat!(
        "forall (v : KExpr) (v' : KExpr) (d : Nat), RecEnvLiftClosed env -> ",
        "par_reduces_c env v v' -> ",
        "par_reduces_c_star env (instantiate_at SUB v d) (instantiate_at SUB v' d)"
    );

    // Goal G(i) for the bvar arm.
    let goal_l = "(instantiate_at (KExpr.bvar i) v d)";
    let goal_r = "(instantiate_at (KExpr.bvar i) v' d)";

    // transport: given X X' eqL eqR T, produce
    //   par_reduces_c_star env (instantiate_at (bvar i) v d) (instantiate_at (bvar i) v' d)
    // from T : par_reduces_c_star env X X', eqL : goal_l = X, eqR : goal_r = X'.
    let transport = |xl: &str, xr: &str, eql: &str, eqr: &str, t: &str| -> String {
        // inner : par_reduces_c_star env goal_l X'  (rewrite X -> goal_l on first index)
        let inner = format!(
            concat!(
                "(Eq.substType KExpr (fun (y : KExpr) => par_reduces_c_star env y {xr}) ",
                "{xl} {goal_l} ",
                "(Eq.symm KExpr {goal_l} {xl} {eql}) {t})"
            ),
            xr = xr,
            xl = xl,
            goal_l = goal_l,
            eql = eql,
            t = t,
        );
        // outer : par_reduces_c_star env goal_l goal_r (rewrite X' -> goal_r on 2nd index)
        format!(
            concat!(
                "(Eq.substType KExpr ",
                "(fun (y : KExpr) => par_reduces_c_star env {goal_l} y) ",
                "{xr} {goal_r} ",
                "(Eq.symm KExpr {goal_r} {xr} {eqr}) {inner})"
            ),
            goal_l = goal_l,
            xr = xr,
            goal_r = goal_r,
            eqr = eqr,
            inner = inner,
        )
    };

    // LEAF: i = d (h_id : sub i d = 0, h_di0 : sub d i = 0). The substituted value
    // is lifted by the binder depth d: par_lift_full_c v v' 0 d, subsumed to _star.
    let leaf_eq = {
        let xl = "(lift_at v Nat.zero d)";
        let xr = "(lift_at v' Nat.zero d)";
        let eql = "(instantiate_at_bvar_eq_from_zero_witnesses i d v h_di0 h_id)";
        let eqr = "(instantiate_at_bvar_eq_from_zero_witnesses i d v' h_di0 h_id)";
        let t = concat!(
            "(par_subsumes_par_c_star env (lift_at v Nat.zero d) (lift_at v' Nat.zero d) ",
            "(par_lift_full_c env v v' Nat.zero d liftclosed h))"
        );
        transport(xl, xr, eql, eqr, t)
    };

    // LEAF: i < d (h_di : sub d i = succ k2, h_id : sub i d = 0). Both = bvar i.
    let leaf_below = {
        let w_di = "(nat_pos_witness_from_succ_eq (Nat.sub d i) k2 h_di)";
        let xl = "(KExpr.bvar i)";
        let xr = "(KExpr.bvar i)";
        let eql = format!(
            concat!(
                "(Eq.trans KExpr {goal_l} (instantiate_bvar_at i d v) (KExpr.bvar i) ",
                "(instantiate_at_bvar i v d) ",
                "(instantiate_bvar_at_below i d v {w_di}))"
            ),
            goal_l = goal_l,
            w_di = w_di,
        );
        let eqr = format!(
            concat!(
                "(Eq.trans KExpr {goal_r} (instantiate_bvar_at i d v') (KExpr.bvar i) ",
                "(instantiate_at_bvar i v' d) ",
                "(instantiate_bvar_at_below i d v' {w_di}))"
            ),
            goal_r = goal_r,
            w_di = w_di,
        );
        let t = "(par_reduces_c_star.refl env (KExpr.bvar i))";
        transport(xl, xr, &eql, &eqr, t)
    };

    // LEAF: i > d (h_id : sub i d = succ k4). Both = bvar (i-1).
    let leaf_above = {
        let h_di0 = "(nat_sub_zero_of_sub_pos i d k4 h_id)";
        let w_id = "(nat_pos_witness_from_succ_eq (Nat.sub i d) k4 h_id)";
        let xl = "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero)))";
        let xr = "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero)))";
        let eql = format!(
            concat!(
                "(Eq.trans KExpr {goal_l} (instantiate_bvar_at i d v) ",
                "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) ",
                "(instantiate_at_bvar i v d) ",
                "(instantiate_bvar_at_above i d v {h_di0} {w_id}))"
            ),
            goal_l = goal_l,
            h_di0 = h_di0,
            w_id = w_id,
        );
        let eqr = format!(
            concat!(
                "(Eq.trans KExpr {goal_r} (instantiate_bvar_at i d v') ",
                "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) ",
                "(instantiate_at_bvar i v' d) ",
                "(instantiate_bvar_at_above i d v' {h_di0} {w_id}))"
            ),
            goal_r = goal_r,
            h_di0 = h_di0,
            w_id = w_id,
        );
        let t = "(par_reduces_c_star.refl env (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))))";
        transport(xl, xr, &eql, &eqr, t)
    };

    // bvar arm: double-Nat.rec convoy (same shape as par_subst_refl_bd).
    let bvar_arm = format!(
        concat!(
            "(fun (i : Nat) (v : KExpr) (v' : KExpr) (d : Nat) ",
            "(liftclosed : RecEnvLiftClosed env) (h : par_reduces_c env v v') => ",
            // OUTER Nat.rec on sub(i, d)
            "Nat.rec ",
            "(fun (g : Nat) => Eq Nat (Nat.sub i d) g -> ",
            "par_reduces_c_star env {goal_l} {goal_r}) ",
            // OUTER ZERO: sub(i,d) = 0
            "(fun (h_id : Eq Nat (Nat.sub i d) Nat.zero) => ",
            // MIDDLE Nat.rec on sub(d, i)
            "Nat.rec ",
            "(fun (g2 : Nat) => Eq Nat (Nat.sub d i) g2 -> ",
            "par_reduces_c_star env {goal_l} {goal_r}) ",
            // MIDDLE ZERO: sub(d,i) = 0 (i = d)
            "(fun (h_di0 : Eq Nat (Nat.sub d i) Nat.zero) => {leaf_eq}) ",
            // MIDDLE SUCC: sub(d,i) = succ k2 (i < d)
            "(fun (k2 : Nat) ",
            "(_ : Eq Nat (Nat.sub d i) k2 -> par_reduces_c_star env {goal_l} {goal_r}) ",
            "(h_di : Eq Nat (Nat.sub d i) (Nat.succ k2)) => {leaf_below}) ",
            "(Nat.sub d i) (Eq.refl Nat (Nat.sub d i))) ",
            // OUTER SUCC: sub(i,d) = succ k4 (i > d)
            "(fun (k4 : Nat) ",
            "(_ : Eq Nat (Nat.sub i d) k4 -> par_reduces_c_star env {goal_l} {goal_r}) ",
            "(h_id : Eq Nat (Nat.sub i d) (Nat.succ k4)) => {leaf_above}) ",
            "(Nat.sub i d) (Eq.refl Nat (Nat.sub i d)))"
        ),
        goal_l = goal_l,
        goal_r = goal_r,
        leaf_eq = leaf_eq,
        leaf_below = leaf_below,
        leaf_above = leaf_above,
    );

    // sort/const arms — refl-star.
    let sort_arm = concat!(
        "(fun (sv : Level) (v : KExpr) (v' : KExpr) (d : Nat) ",
        "(_lc : RecEnvLiftClosed env) (_h : par_reduces_c env v v') => ",
        "par_reduces_c_star.refl env (KExpr.sort sv))"
    );
    let const_arm = concat!(
        "(fun (nm : Name) (us : ListType Level) (v : KExpr) (v' : KExpr) (d : Nat) ",
        "(_lc : RecEnvLiftClosed env) (_h : par_reduces_c env v v') => ",
        "par_reduces_c_star.refl env (KExpr.const nm us))"
    );

    // app arm: the _star app congruence on the two IHs.
    let app_arm = format!(
        concat!(
            "(fun (f : KExpr) (a0 : KExpr) ",
            "(ihf : {ih_f}) (iha : {ih_a}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (lc : RecEnvLiftClosed env) (h : par_reduces_c env v v') => ",
            "par_reduces_c_star_app env ",
            "(instantiate_at f v d) (instantiate_at f v' d) ",
            "(instantiate_at a0 v d) (instantiate_at a0 v' d) ",
            "(ihf v v' d lc h) (iha v v' d lc h))"
        ),
        ih_f = ih.replace("SUB", "f"),
        ih_a = ih.replace("SUB", "a0"),
    );

    // lam/pi arm parametric in the _star binder congruence (body IH at succ d).
    let binder_arm = |star_cong: &str| -> String {
        format!(
            concat!(
                "(fun (ty : KExpr) (body : KExpr) ",
                "(ihty : {ih_ty}) (ihbody : {ih_body}) ",
                "(v : KExpr) (v' : KExpr) (d : Nat) (lc : RecEnvLiftClosed env) (h : par_reduces_c env v v') => ",
                "{star_cong} env ",
                "(instantiate_at ty v d) (instantiate_at ty v' d) ",
                "(instantiate_at body v (Nat.succ d)) (instantiate_at body v' (Nat.succ d)) ",
                "(ihty v v' d lc h) (ihbody v v' (Nat.succ d) lc h))"
            ),
            ih_ty = ih.replace("SUB", "ty"),
            ih_body = ih.replace("SUB", "body"),
            star_cong = star_cong,
        )
    };

    // let_ arm (the trailing KExpr.rec minor, genuine 7th constructor): the term
    // e is FIXED, so both sides are the same let node with v / v' substituted in;
    // par_reduces_c_star_let_cong on the three sub-IHs (ty/val at d, body at succ d).
    let let_arm = format!(
        concat!(
            "(fun (ty : KExpr) (val : KExpr) (body : KExpr) ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (lc : RecEnvLiftClosed env) (h : par_reduces_c env v v') => ",
            "par_reduces_c_star_let_cong env ",
            "(instantiate_at ty v d) (instantiate_at ty v' d) ",
            "(instantiate_at val v d) (instantiate_at val v' d) ",
            "(instantiate_at body v (Nat.succ d)) (instantiate_at body v' (Nat.succ d)) ",
            "(ihty v v' d lc h) (ihval v v' d lc h) (ihbody v v' (Nat.succ d) lc h))"
        ),
        ih_ty = ih.replace("SUB", "ty"),
        ih_val = ih.replace("SUB", "val"),
        ih_body = ih.replace("SUB", "body"),
    );

    // proj arm: subst descends into the scrutinee; congruence via par_reduces_c_star_proj.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (ihsub : {ih_sub}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (lc : RecEnvLiftClosed env) (h : par_reduces_c env v v') => ",
            "par_reduces_c_star_proj env s i ",
            "(instantiate_at sub v d) (instantiate_at sub v' d) ",
            "(ihsub v v' d lc h))"
        ),
        ih_sub = ih.replace("SUB", "sub"),
    );

    // lit arm: a numeral is closed, so instantiate_at (lit n) v d = lit n; refl.
    let lit_arm = concat!(
        "(fun (litv : Nat) (v : KExpr) (v' : KExpr) (d : Nat) ",
        "(_lc : RecEnvLiftClosed env) (_h : par_reduces_c env v v') => ",
        "par_reduces_c_star.refl env (KExpr.lit litv))"
    );

    format!(
        concat!(
            "fun (env : RecEnv) (e0 : KExpr) => ",
            "KExpr.rec {motive} ",
            "{sort_arm} {bvar_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {const_arm} {let_arm} {proj_arm} {lit_arm} ",
            "e0"
        ),
        motive = motive,
        sort_arm = sort_arm,
        bvar_arm = bvar_arm,
        app_arm = app_arm,
        lam_arm = binder_arm("par_reduces_c_star_lam"),
        pi_arm = binder_arm("par_reduces_c_star_pi"),
        const_arm = const_arm,
        let_arm = let_arm,
        proj_arm = proj_arm,
        lit_arm = lit_arm,
    )
}

/// Closed proof term for `par_subst_full_c` (Increment F final assembly #2). The
/// FULL-relation substitution lemma. Mirrors `par_subst_c_proof`'s
/// `par_reduces_c.rec` structure, but the value source is a full `par_reduces_c
/// env v v'` (not `par_reduces_bd`): the refl arm goes through
/// `par_subst_refl_full_c` (#1, already _star), the iota arm through
/// `par_subst_iota_arm_full_c` (#2a), and the motive threads BOTH `RecEnvClosed`
/// (iota arm) and `RecEnvLiftClosed` (the value congruence's `par_lift_full_c`).
fn par_subst_full_c_proof() -> String {
    // Depth-generalized, _star-valued motive threading the full value reduction
    // par_reduces_c env v v' + both closure predicates.
    let motive = concat!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_c env e e') => ",
        "forall (v : KExpr) (v' : KExpr) (d : Nat), par_reduces_c env v v' -> ",
        "RecEnvClosed env -> RecEnvLiftClosed env -> ",
        "par_reduces_c_star env (instantiate_at e v d) (instantiate_at e' v' d))"
    );
    // IH shape for a sub-derivation SUB => SUB'.
    let ih = concat!(
        "forall (v : KExpr) (v' : KExpr) (d : Nat), par_reduces_c env v v' -> ",
        "RecEnvClosed env -> RecEnvLiftClosed env -> ",
        "par_reduces_c_star env (instantiate_at SUB v d) (instantiate_at SUB' v' d)"
    );

    // refl arm: par_subst_refl_full_c (#1), already _star-valued.
    let refl_arm = concat!(
        "(fun (e : KExpr) (v : KExpr) (v' : KExpr) (d : Nat) ",
        "(h : par_reduces_c env v v') (_closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
        "par_subst_refl_full_c env e v v' d liftclosed h)"
    );

    // app arm.
    let app_arm = format!(
        concat!(
            "(fun (f : KExpr) (f' : KExpr) (a0 : KExpr) (a0' : KExpr) ",
            "(_hf : par_reduces_c env f f') (_ha : par_reduces_c env a0 a0') ",
            "(ihf : {ih_f}) (iha : {ih_a}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_c env v v') ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_c_star_app env ",
            "(instantiate_at f v d) (instantiate_at f' v' d) ",
            "(instantiate_at a0 v d) (instantiate_at a0' v' d) ",
            "(ihf v v' d h closed liftclosed) (iha v v' d h closed liftclosed))"
        ),
        ih_f = ih.replace("SUB'", "f'").replace("SUB", "f"),
        ih_a = ih.replace("SUB'", "a0'").replace("SUB", "a0"),
    );

    // lam/pi/forall_ congruence arm, parametric in the _star congruence lemma.
    let binder_arm = |star_cong: &str| -> String {
        format!(
            concat!(
                "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                "(_hty : par_reduces_c env ty ty') (_hbody : par_reduces_c env body body') ",
                "(ihty : {ih_ty}) (ihbody : {ih_body}) ",
                "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_c env v v') ",
                "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
                "{star_cong} env ",
                "(instantiate_at ty v d) (instantiate_at ty' v' d) ",
                "(instantiate_at body v (Nat.succ d)) (instantiate_at body' v' (Nat.succ d)) ",
                "(ihty v v' d h closed liftclosed) (ihbody v v' (Nat.succ d) h closed liftclosed))"
            ),
            ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
            ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
            star_cong = star_cong,
        )
    };

    // beta/let_ contraction transport (same shape as par_subst_c_proof's `contract`,
    // at the _star level). instantiate_nested_commutes_zero_subst bridges the _star
    // contraction-congruence RHS to the goal RHS.
    let contract = |lhs_head: &str, star_term: &str, bodyp: &str, argp: &str| -> String {
        let goal_rhs = format!(
            "(instantiate_at (instantiate_at {bodyp} {argp} Nat.zero) v' d)",
            bodyp = bodyp,
            argp = argp,
        );
        let star_rhs = format!(
            concat!(
                "(instantiate_at (instantiate_at {bodyp} v' (Nat.succ d)) ",
                "(instantiate_at {argp} v' d) Nat.zero)"
            ),
            bodyp = bodyp,
            argp = argp,
        );
        let eq = format!(
            "(instantiate_nested_commutes_zero_subst {bodyp} {argp} v' d)",
            bodyp = bodyp,
            argp = argp,
        );
        format!(
            concat!(
                "(Eq.substType KExpr ",
                "(fun (x : KExpr) => par_reduces_c_star env {lhs_head} x) ",
                "{star_rhs} {goal_rhs} ",
                "(Eq.symm KExpr {goal_rhs} {star_rhs} {eq}) ",
                "{star_term})"
            ),
            lhs_head = lhs_head,
            star_rhs = star_rhs,
            goal_rhs = goal_rhs,
            eq = eq,
            star_term = star_term,
        )
    };

    // beta arm.
    let beta_lhs_head = concat!(
        "(KExpr.app ",
        "(KExpr.lam (instantiate_at A v d) (instantiate_at body v (Nat.succ d))) ",
        "(instantiate_at arg v d))"
    );
    let beta_star = concat!(
        "(par_reduces_c_star_beta env ",
        "(instantiate_at A v d) (instantiate_at A' v' d) ",
        "(instantiate_at body v (Nat.succ d)) (instantiate_at body' v' (Nat.succ d)) ",
        "(instantiate_at arg v d) (instantiate_at arg' v' d) ",
        "(ihA v v' d h closed liftclosed) (ihbody v v' (Nat.succ d) h closed liftclosed) ",
        "(iharg v v' d h closed liftclosed))"
    );
    let beta_arm = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) ",
            "(arg : KExpr) (arg' : KExpr) ",
            "(_hA : par_reduces_c env A A') (_hbody : par_reduces_c env body body') ",
            "(_harg : par_reduces_c env arg arg') ",
            "(ihA : {ih_A}) (ihbody : {ih_body}) (iharg : {ih_arg}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_c env v v') ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => {body})"
        ),
        ih_A = ih.replace("SUB'", "A'").replace("SUB", "A"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
        ih_arg = ih.replace("SUB'", "arg'").replace("SUB", "arg"),
        body = contract(beta_lhs_head, beta_star, "body'", "arg'"),
    );

    // let_ (zeta) arm: the substituted redex skeleton is the GENUINE let node
    // (instantiate_at distributes over the let_ ctor since the let-promotion),
    // then the beta-shaped contraction transport with arg := val.
    let let_lhs_head = concat!(
        "(KExpr.let_ ",
        "(instantiate_at ty v d) (instantiate_at val v d) ",
        "(instantiate_at body v (Nat.succ d)))"
    );
    let let_star = concat!(
        "(par_reduces_c_star_let env ",
        "(instantiate_at ty v d) (instantiate_at ty' v' d) ",
        "(instantiate_at val v d) (instantiate_at val' v' d) ",
        "(instantiate_at body v (Nat.succ d)) (instantiate_at body' v' (Nat.succ d)) ",
        "(ihty v v' d h closed liftclosed) (ihval v v' d h closed liftclosed) ",
        "(ihbody v v' (Nat.succ d) h closed liftclosed))"
    );
    let let_arm = format!(
        concat!(
            "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
            "(body : KExpr) (body' : KExpr) ",
            "(_hty : par_reduces_c env ty ty') (_hval : par_reduces_c env val val') ",
            "(_hbody : par_reduces_c env body body') ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_c env v v') ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => {body})"
        ),
        ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
        ih_val = ih.replace("SUB'", "val'").replace("SUB", "val"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
        body = contract(let_lhs_head, let_star, "body'", "val'"),
    );

    // let_cong arm: instantiate_at distributes over the genuine let node
    // componentwise; par_reduces_c_star_let_cong on the three IHs (no transport).
    let let_cong_arm = format!(
        concat!(
            "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
            "(body : KExpr) (body' : KExpr) ",
            "(_hty : par_reduces_c env ty ty') (_hval : par_reduces_c env val val') ",
            "(_hbody : par_reduces_c env body body') ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_c env v v') ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_c_star_let_cong env ",
            "(instantiate_at ty v d) (instantiate_at ty' v' d) ",
            "(instantiate_at val v d) (instantiate_at val' v' d) ",
            "(instantiate_at body v (Nat.succ d)) (instantiate_at body' v' (Nat.succ d)) ",
            "(ihty v v' d h closed liftclosed) (ihval v v' d h closed liftclosed) ",
            "(ihbody v v' (Nat.succ d) h closed liftclosed))"
        ),
        ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
        ih_val = ih.replace("SUB'", "val'").replace("SUB", "val"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
    );

    // iota arm: source e0 => e0' with iota_step env e0 e0'. par_subst_iota_arm_full_c
    // (the full-value E-core 2-step star) at depth d, using BOTH closure predicates
    // and the full value reduction v => v'.
    let iota_arm = concat!(
        "(fun (e0 : KExpr) (e0' : KExpr) (hstep : iota_step env e0 e0') ",
        "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_c env v v') ",
        "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
        "par_subst_iota_arm_full_c env e0 e0' v v' d closed liftclosed hstep h)"
    );

    // proj arm: subst descends into the scrutinee; congruence via par_reduces_c_star_proj.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
            "(_hsub : par_reduces_c env sub sub') (ihsub : {ih_sub}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_c env v v') ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_c_star_proj env s i ",
            "(instantiate_at sub v d) (instantiate_at sub' v' d) ",
            "(ihsub v v' d h closed liftclosed))"
        ),
        ih_sub = ih.replace("SUB'", "sub'").replace("SUB", "sub"),
    );

    format!(
        concat!(
            "fun (env : RecEnv) (e0 : KExpr) (e0' : KExpr) (v0 : KExpr) (v0' : KExpr) (d0 : Nat) ",
            "(h_ee : par_reduces_c env e0 e0') (h_vv : par_reduces_c env v0 v0') ",
            "(closed0 : RecEnvClosed env) (liftclosed0 : RecEnvLiftClosed env) => ",
            "par_reduces_c.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} ",
            "e0 e0' h_ee v0 v0' d0 h_vv closed0 liftclosed0"
        ),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = binder_arm("par_reduces_c_star_lam"),
        pi_arm = binder_arm("par_reduces_c_star_pi"),
        forall_arm = binder_arm("par_reduces_c_star_forall"),
        let_arm = let_arm,
        iota_arm = iota_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for `par_strips_witness_c_star_app` (Phase 3 leaf): the
/// (app, app) congruence combinator at the star-witness level. Projects both
/// input star-witnesses (par_strips_witness_c_star.rec) and reassembles via
/// par_reduces_c_star_app at the per-component meeting points.
fn par_strips_witness_c_star_app_proof() -> String {
    concat!(
        "fun (env : RecEnv) (f1 : KExpr) (f2 : KExpr) (a1 : KExpr) (a2 : KExpr) ",
        "(wf : par_strips_witness_c_star env f1 f2) (wa : par_strips_witness_c_star env a1 a2) => ",
        "@par_strips_witness_c_star.rec env f1 f2 ",
        "(fun (_wf : par_strips_witness_c_star env f1 f2) => ",
        "par_strips_witness_c_star env (KExpr.app f1 a1) (KExpr.app f2 a2)) ",
        "(fun (f3 : KExpr) ",
        "(pf1 : par_reduces_c_star env f1 f3) (pf2 : par_reduces_c_star env f2 f3) => ",
        "@par_strips_witness_c_star.rec env a1 a2 ",
        "(fun (_wa : par_strips_witness_c_star env a1 a2) => ",
        "par_strips_witness_c_star env (KExpr.app f1 a1) (KExpr.app f2 a2)) ",
        "(fun (a3 : KExpr) ",
        "(pa1 : par_reduces_c_star env a1 a3) (pa2 : par_reduces_c_star env a2 a3) => ",
        "par_strips_witness_c_star.intro env (KExpr.app f1 a1) (KExpr.app f2 a2) (KExpr.app f3 a3) ",
        "(par_reduces_c_star_app env f1 f3 a1 a3 pf1 pa1) ",
        "(par_reduces_c_star_app env f2 f3 a2 a3 pf2 pa2)) ",
        "wa) ",
        "wf"
    )
    .to_string()
}

/// Closed proof term for the (binder, binder) star-witness congruence combinators
/// `par_strips_witness_c_star_{lam,pi,forall}` (Phase 3 leaf), parametric in the
/// reduct head `head` and the `_star` binder congruence `star_cong`.
fn par_strips_witness_c_star_binder_proof(head: &str, star_cong: &str) -> String {
    format!(
        concat!(
            "fun (env : RecEnv) (t1 : KExpr) (t2 : KExpr) (b1 : KExpr) (b2 : KExpr) ",
            "(wt : par_strips_witness_c_star env t1 t2) (wb : par_strips_witness_c_star env b1 b2) => ",
            "@par_strips_witness_c_star.rec env t1 t2 ",
            "(fun (_wt : par_strips_witness_c_star env t1 t2) => ",
            "par_strips_witness_c_star env ({head} t1 b1) ({head} t2 b2)) ",
            "(fun (t3 : KExpr) ",
            "(pt1 : par_reduces_c_star env t1 t3) (pt2 : par_reduces_c_star env t2 t3) => ",
            "@par_strips_witness_c_star.rec env b1 b2 ",
            "(fun (_wb : par_strips_witness_c_star env b1 b2) => ",
            "par_strips_witness_c_star env ({head} t1 b1) ({head} t2 b2)) ",
            "(fun (b3 : KExpr) ",
            "(pb1 : par_reduces_c_star env b1 b3) (pb2 : par_reduces_c_star env b2 b3) => ",
            "par_strips_witness_c_star.intro env ({head} t1 b1) ({head} t2 b2) ({head} t3 b3) ",
            "({star_cong} env t1 t3 b1 b3 pt1 pb1) ",
            "({star_cong} env t2 t3 b2 b3 pt2 pb2)) ",
            "wb) ",
            "wt"
        ),
        head = head,
        star_cong = star_cong,
    )
}

/// Closed proof term for `par_reduces_c_proj_inv` (proj/lit fragment rung).
/// Mirrors `par_reduces_bd_proj_inv_proof` over `par_reduces_c` (env threaded)
/// plus the extra `iota` constructor arm (discharged: a proj head is its own
/// spine head, kexpr_const_name = none, so it is not an iota redex). proj is a
/// pure single-position congruence: only refl and the proj congruence are
/// non-vacuous; every other ctor has an app/lam/pi/let_-headed source discharged
/// by app/lam/pi/let_ne_proj; the matching proj arm recovers via
/// proj_inj_{name,idx,sub} + name/idx transport.
fn par_reduces_c_proj_inv_proof() -> String {
    let motive = concat!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_c env e e') => ",
        "Eq KExpr e (KExpr.proj s i sub) -> C e')"
    );
    let refl_arm = concat!(
        "(fun (e : KExpr) (eq : Eq KExpr e (KExpr.proj s i sub)) => ",
        "Eq.substType KExpr C (KExpr.proj s i sub) e ",
        "(Eq.symm KExpr e (KExpr.proj s i sub) eq) ",
        "(kproj sub (par_reduces_c.refl env sub)))"
    );
    let beta_arm = concat!(
        "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) ",
        "(_hA : par_reduces_c env A A') (_hbody : par_reduces_c env body body') (_harg : par_reduces_c env arg arg') ",
        "(_ihA : Eq KExpr A (KExpr.proj s i sub) -> C A') ",
        "(_ihbody : Eq KExpr body (KExpr.proj s i sub) -> C body') ",
        "(_iharg : Eq KExpr arg (KExpr.proj s i sub) -> C arg') ",
        "(eq : Eq KExpr (KExpr.app (KExpr.lam A body) arg) (KExpr.proj s i sub)) => ",
        "app_ne_proj (KExpr.lam A body) arg s i sub (C (instantiate body' arg')) eq)"
    );
    let app_arm = concat!(
        "(fun (g : KExpr) (g' : KExpr) (b : KExpr) (b' : KExpr) ",
        "(_hg : par_reduces_c env g g') (_hb : par_reduces_c env b b') ",
        "(_ihg : Eq KExpr g (KExpr.proj s i sub) -> C g') ",
        "(_ihb : Eq KExpr b (KExpr.proj s i sub) -> C b') ",
        "(eq : Eq KExpr (KExpr.app g b) (KExpr.proj s i sub)) => ",
        "app_ne_proj g b s i sub (C (KExpr.app g' b')) eq)"
    );
    let lam_arm = concat!(
        "(fun (t0 : KExpr) (t0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(_ht : par_reduces_c env t0 t0') (_hb : par_reduces_c env b0 b0') ",
        "(_iht : Eq KExpr t0 (KExpr.proj s i sub) -> C t0') ",
        "(_ihb : Eq KExpr b0 (KExpr.proj s i sub) -> C b0') ",
        "(eq : Eq KExpr (KExpr.lam t0 b0) (KExpr.proj s i sub)) => ",
        "lam_ne_proj t0 b0 s i sub (C (KExpr.lam t0' b0')) eq)"
    );
    let pi_arm = concat!(
        "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(_hd : par_reduces_c env d0 d0') (_hb : par_reduces_c env b0 b0') ",
        "(_ihd : Eq KExpr d0 (KExpr.proj s i sub) -> C d0') ",
        "(_ihb : Eq KExpr b0 (KExpr.proj s i sub) -> C b0') ",
        "(eq : Eq KExpr (KExpr.pi d0 b0) (KExpr.proj s i sub)) => ",
        "pi_ne_proj d0 b0 s i sub (C (KExpr.pi d0' b0')) eq)"
    );
    let forall_arm = concat!(
        "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(_hd : par_reduces_c env d0 d0') (_hb : par_reduces_c env b0 b0') ",
        "(_ihd : Eq KExpr d0 (KExpr.proj s i sub) -> C d0') ",
        "(_ihb : Eq KExpr b0 (KExpr.proj s i sub) -> C b0') ",
        "(eq : Eq KExpr (KExpr.forall_ d0 b0) (KExpr.proj s i sub)) => ",
        "pi_ne_proj d0 b0 s i sub (C (KExpr.forall_ d0' b0')) eq)"
    );
    let let_arm = concat!(
        "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(_ht0 : par_reduces_c env t0 t0') (_hv : par_reduces_c env v v') (_hb0 : par_reduces_c env b0 b0') ",
        "(_iht0 : Eq KExpr t0 (KExpr.proj s i sub) -> C t0') ",
        "(_ihv : Eq KExpr v (KExpr.proj s i sub) -> C v') ",
        "(_ihb0 : Eq KExpr b0 (KExpr.proj s i sub) -> C b0') ",
        "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.proj s i sub)) => ",
        "let_ne_proj t0 v b0 s i sub (C (instantiate b0' v')) eq)"
    );
    // iota: proj is its own spine head (kexpr_const_name = none), not an iota redex.
    let iota_arm = concat!(
        "(fun (e0 : KExpr) (e0' : KExpr) (hstep : iota_step env e0 e0') ",
        "(eq : Eq KExpr e0 (KExpr.proj s i sub)) => ",
        "iota_step_head_none_absurd_type env (KExpr.proj s i sub) e0' (C e0') ",
        "(Eq.refl (OptionType Name) (OptionType.none Name)) ",
        "(Eq.subst KExpr (fun (x : KExpr) => iota_step env x e0') e0 (KExpr.proj s i sub) eq hstep))"
    );
    let let_cong_arm = concat!(
        "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(_ht0 : par_reduces_c env t0 t0') (_hv : par_reduces_c env v v') (_hb0 : par_reduces_c env b0 b0') ",
        "(_iht0 : Eq KExpr t0 (KExpr.proj s i sub) -> C t0') ",
        "(_ihv : Eq KExpr v (KExpr.proj s i sub) -> C v') ",
        "(_ihb0 : Eq KExpr b0 (KExpr.proj s i sub) -> C b0') ",
        "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.proj s i sub)) => ",
        "let_ne_proj t0 v b0 s i sub (C (KExpr.let_ t0' v' b0')) eq)"
    );
    // proj: the genuine match — recover components via proj injectivity, transport.
    let proj_arm = concat!(
        "(fun (s0 : Name) (i0 : Nat) (sub0 : KExpr) (sub0' : KExpr) ",
        "(hsub0 : par_reduces_c env sub0 sub0') ",
        "(_ihsub0 : Eq KExpr sub0 (KExpr.proj s i sub) -> C sub0') ",
        "(eq : Eq KExpr (KExpr.proj s0 i0 sub0) (KExpr.proj s i sub)) => ",
        "Eq.substType Nat (fun (x : Nat) => C (KExpr.proj s0 x sub0')) i i0 ",
        "(Eq.symm Nat i0 i (proj_inj_idx s0 i0 sub0 s i sub eq)) ",
        "(Eq.substType Name (fun (x : Name) => C (KExpr.proj x i sub0')) s s0 ",
        "(Eq.symm Name s0 s (proj_inj_name s0 i0 sub0 s i sub eq)) ",
        "(kproj sub0' ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x sub0') sub0 sub ",
        "(proj_inj_sub s0 i0 sub0 s i sub eq) hsub0))))"
    );
    format!(
        concat!(
            "fun (env : RecEnv) (s : Name) (i : Nat) (sub : KExpr) (t : KExpr) (C : KExpr -> Type) ",
            "(h : par_reduces_c env (KExpr.proj s i sub) t) ",
            "(kproj : forall (sub' : KExpr), ",
            "par_reduces_c env sub sub' -> C (KExpr.proj s i sub')) => ",
            "par_reduces_c.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} {lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} ",
            "(KExpr.proj s i sub) t h (Eq.refl KExpr (KExpr.proj s i sub))"
        ),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = lam_arm,
        pi_arm = pi_arm,
        forall_arm = forall_arm,
        let_arm = let_arm,
        iota_arm = iota_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for `par_reduces_c_lam_inv` (Phase 1 inversion). Mirrors
/// `par_reduces_bd_lam_inv_proof` over `par_reduces_c` (env threaded) plus the
/// extra `iota` constructor arm, discharged because a binder head cannot be an
/// iota redex (`iota_step_head_none_absurd_type`, transporting the bound
/// `iota_step env e0 e0'` along the source equation to the `lam ty body` head).
fn par_reduces_c_lam_inv_proof() -> String {
    let motive = concat!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_c env e e') => ",
        "Eq KExpr e (KExpr.lam ty body) -> C e')"
    );

    // refl: reduct e; build C (lam ty body), transport to C e.
    let refl_arm = concat!(
        "(fun (e : KExpr) (eq : Eq KExpr e (KExpr.lam ty body)) => ",
        "Eq.substType KExpr C (KExpr.lam ty body) e ",
        "(Eq.symm KExpr e (KExpr.lam ty body) eq) ",
        "(klam ty body (par_reduces_c.refl env ty) (par_reduces_c.refl env body)))"
    );

    // beta: source app (lam A b0) arg — app /= lam.
    let beta_arm = concat!(
        "(fun (A : KExpr) (A' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(arg : KExpr) (arg' : KExpr) ",
        "(_hA : par_reduces_c env A A') (_hb0 : par_reduces_c env b0 b0') ",
        "(_harg : par_reduces_c env arg arg') ",
        "(_ihA : Eq KExpr A (KExpr.lam ty body) -> C A') ",
        "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
        "(_iharg : Eq KExpr arg (KExpr.lam ty body) -> C arg') ",
        "(eq : Eq KExpr (KExpr.app (KExpr.lam A b0) arg) (KExpr.lam ty body)) => ",
        "app_ne_lam (KExpr.lam A b0) arg ty body (C (instantiate b0' arg')) eq)"
    );

    // app: source app g b — app /= lam.
    let app_arm = concat!(
        "(fun (g : KExpr) (g' : KExpr) (b : KExpr) (b' : KExpr) ",
        "(_hg : par_reduces_c env g g') (_hb : par_reduces_c env b b') ",
        "(_ihg : Eq KExpr g (KExpr.lam ty body) -> C g') ",
        "(_ihb : Eq KExpr b (KExpr.lam ty body) -> C b') ",
        "(eq : Eq KExpr (KExpr.app g b) (KExpr.lam ty body)) => ",
        "app_ne_lam g b ty body (C (KExpr.app g' b')) eq)"
    );

    // lam: source lam t0 b0 — the matching congruence arm.
    let lam_arm = concat!(
        "(fun (t0 : KExpr) (t0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(ht : par_reduces_c env t0 t0') (hb : par_reduces_c env b0 b0') ",
        "(_iht : Eq KExpr t0 (KExpr.lam ty body) -> C t0') ",
        "(_ihb : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
        "(eq : Eq KExpr (KExpr.lam t0 b0) (KExpr.lam ty body)) => ",
        "klam t0' b0' ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x t0') t0 ty ",
        "(lam_inj_fst t0 b0 ty body eq) ht) ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x b0') b0 body ",
        "(lam_inj_snd t0 b0 ty body eq) hb))"
    );

    // pi: source pi dom b0 — pi /= lam.
    let pi_arm = concat!(
        "(fun (dom : KExpr) (dom' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(_hd : par_reduces_c env dom dom') (_hb0 : par_reduces_c env b0 b0') ",
        "(_ihd : Eq KExpr dom (KExpr.lam ty body) -> C dom') ",
        "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
        "(eq : Eq KExpr (KExpr.pi dom b0) (KExpr.lam ty body)) => ",
        "pi_ne_lam dom b0 ty body (C (KExpr.pi dom' b0')) eq)"
    );

    // forall_: source forall_ dom b0 = pi dom b0 (alias) — pi /= lam.
    let forall_arm = concat!(
        "(fun (dom : KExpr) (dom' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(_hd : par_reduces_c env dom dom') (_hb0 : par_reduces_c env b0 b0') ",
        "(_ihd : Eq KExpr dom (KExpr.lam ty body) -> C dom') ",
        "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
        "(eq : Eq KExpr (KExpr.forall_ dom b0) (KExpr.lam ty body)) => ",
        "pi_ne_lam dom b0 ty body (C (KExpr.forall_ dom' b0')) eq)"
    );

    // let_ (zeta): source let_ t0 v b0 — a GENUINE let node, let /= lam.
    let let_arm = concat!(
        "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
        "(b0 : KExpr) (b0' : KExpr) ",
        "(_ht0 : par_reduces_c env t0 t0') (_hv : par_reduces_c env v v') ",
        "(_hb0 : par_reduces_c env b0 b0') ",
        "(_iht0 : Eq KExpr t0 (KExpr.lam ty body) -> C t0') ",
        "(_ihv : Eq KExpr v (KExpr.lam ty body) -> C v') ",
        "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
        "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.lam ty body)) => ",
        "let_ne_lam t0 v b0 ty body (C (instantiate b0' v')) eq)"
    );

    // let_cong: source let_ t0 v b0 — a GENUINE let node, let /= lam.
    let let_cong_arm = concat!(
        "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
        "(b0 : KExpr) (b0' : KExpr) ",
        "(_ht0 : par_reduces_c env t0 t0') (_hv : par_reduces_c env v v') ",
        "(_hb0 : par_reduces_c env b0 b0') ",
        "(_iht0 : Eq KExpr t0 (KExpr.lam ty body) -> C t0') ",
        "(_ihv : Eq KExpr v (KExpr.lam ty body) -> C v') ",
        "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
        "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.lam ty body)) => ",
        "let_ne_lam t0 v b0 ty body (C (KExpr.let_ t0' v' b0')) eq)"
    );

    // iota: source e0 with iota_step env e0 e0'. Transport the iota_step to the
    // lam head (Eq.subst along eq), then discharge — a binder head is not a
    // const head, so it cannot be an iota redex.
    let iota_arm = concat!(
        "(fun (e0 : KExpr) (e0' : KExpr) (hstep : iota_step env e0 e0') ",
        "(eq : Eq KExpr e0 (KExpr.lam ty body)) => ",
        "iota_step_head_none_absurd_type env (KExpr.lam ty body) e0' (C e0') ",
        "(Eq.refl (OptionType Name) (OptionType.none Name)) ",
        "(Eq.subst KExpr (fun (x : KExpr) => iota_step env x e0') e0 (KExpr.lam ty body) eq hstep))"
    );

    // proj: source proj s i sub is proj-headed — proj /= lam via proj_ne_lam.
    let proj_arm = concat!(
        "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
        "(_hsub : par_reduces_c env sub sub') ",
        "(_ihsub : Eq KExpr sub (KExpr.lam ty body) -> C sub') ",
        "(eq : Eq KExpr (KExpr.proj s i sub) (KExpr.lam ty body)) => ",
        "proj_ne_lam s i sub ty body (C (KExpr.proj s i sub')) eq)"
    );

    format!(
        concat!(
            "fun (env : RecEnv) (ty : KExpr) (body : KExpr) (t : KExpr) (C : KExpr -> Type) ",
            "(h : par_reduces_c env (KExpr.lam ty body) t) ",
            "(klam : forall (ty' : KExpr) (body' : KExpr), ",
            "par_reduces_c env ty ty' -> par_reduces_c env body body' -> ",
            "C (KExpr.lam ty' body')) => ",
            "par_reduces_c.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} ",
            "(KExpr.lam ty body) t h (Eq.refl KExpr (KExpr.lam ty body))"
        ),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = lam_arm,
        pi_arm = pi_arm,
        forall_arm = forall_arm,
        let_arm = let_arm,
        iota_arm = iota_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for the pi-headed inversions `par_reduces_c_pi_inv` and
/// `par_reduces_c_forall_inv` (Phase 1), parametric in the source/reduct binder
/// head `head` (`KExpr.pi` or `KExpr.forall_`). Mirrors
/// `par_reduces_bd_pi_like_inv_proof` over `par_reduces_c` plus the iota arm.
fn par_reduces_c_pi_like_inv_proof(head: &str) -> String {
    let motive = format!(
        concat!(
            "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_c env e e') => ",
            "Eq KExpr e ({head} dom body) -> C e')"
        ),
        head = head,
    );

    // refl: reduct e; build C (head dom body), transport to C e.
    let refl_arm = format!(
        concat!(
            "(fun (e : KExpr) (eq : Eq KExpr e ({head} dom body)) => ",
            "Eq.substType KExpr C ({head} dom body) e ",
            "(Eq.symm KExpr e ({head} dom body) eq) ",
            "(kpi dom body (par_reduces_c.refl env dom) (par_reduces_c.refl env body)))"
        ),
        head = head,
    );

    // beta: source app (lam A b0) arg — app /= pi.
    let beta_arm = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(arg : KExpr) (arg' : KExpr) ",
            "(_hA : par_reduces_c env A A') (_hb0 : par_reduces_c env b0 b0') ",
            "(_harg : par_reduces_c env arg arg') ",
            "(_ihA : Eq KExpr A ({head} dom body) -> C A') ",
            "(_ihb0 : Eq KExpr b0 ({head} dom body) -> C b0') ",
            "(_iharg : Eq KExpr arg ({head} dom body) -> C arg') ",
            "(eq : Eq KExpr (KExpr.app (KExpr.lam A b0) arg) ({head} dom body)) => ",
            "app_ne_pi (KExpr.lam A b0) arg dom body (C (instantiate b0' arg')) eq)"
        ),
        head = head,
    );

    // app: source app g b — app /= pi.
    let app_arm = format!(
        concat!(
            "(fun (g : KExpr) (g' : KExpr) (b : KExpr) (b' : KExpr) ",
            "(_hg : par_reduces_c env g g') (_hb : par_reduces_c env b b') ",
            "(_ihg : Eq KExpr g ({head} dom body) -> C g') ",
            "(_ihb : Eq KExpr b ({head} dom body) -> C b') ",
            "(eq : Eq KExpr (KExpr.app g b) ({head} dom body)) => ",
            "app_ne_pi g b dom body (C (KExpr.app g' b')) eq)"
        ),
        head = head,
    );

    // lam: source lam t0 b0 — lam /= pi.
    let lam_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_ht : par_reduces_c env t0 t0') (_hb : par_reduces_c env b0 b0') ",
            "(_iht : Eq KExpr t0 ({head} dom body) -> C t0') ",
            "(_ihb : Eq KExpr b0 ({head} dom body) -> C b0') ",
            "(eq : Eq KExpr (KExpr.lam t0 b0) ({head} dom body)) => ",
            "lam_ne_pi t0 b0 dom body (C (KExpr.lam t0' b0')) eq)"
        ),
        head = head,
    );

    // pi: source pi d0 b0 — matching congruence (pi_inj_*; head defeq pi).
    let pi_arm = format!(
        concat!(
            "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(hd : par_reduces_c env d0 d0') (hb : par_reduces_c env b0 b0') ",
            "(_ihd : Eq KExpr d0 ({head} dom body) -> C d0') ",
            "(_ihb : Eq KExpr b0 ({head} dom body) -> C b0') ",
            "(eq : Eq KExpr (KExpr.pi d0 b0) ({head} dom body)) => ",
            "kpi d0' b0' ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x d0') d0 dom ",
            "(pi_inj_fst d0 b0 dom body eq) hd) ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x b0') b0 body ",
            "(pi_inj_snd d0 b0 dom body eq) hb))"
        ),
        head = head,
    );

    // forall_: source forall_ d0 b0 = pi d0 b0 (alias) — matching congruence.
    let forall_arm = format!(
        concat!(
            "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(hd : par_reduces_c env d0 d0') (hb : par_reduces_c env b0 b0') ",
            "(_ihd : Eq KExpr d0 ({head} dom body) -> C d0') ",
            "(_ihb : Eq KExpr b0 ({head} dom body) -> C b0') ",
            "(eq : Eq KExpr (KExpr.forall_ d0 b0) ({head} dom body)) => ",
            "kpi d0' b0' ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x d0') d0 dom ",
            "(pi_inj_fst d0 b0 dom body eq) hd) ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x b0') b0 body ",
            "(pi_inj_snd d0 b0 dom body eq) hb))"
        ),
        head = head,
    );

    // let_ (zeta): source let_ t0 v b0 — a GENUINE let node, let /= pi (the
    // forall_ instantiation is defeq to pi, so let_ne_pi discharges both).
    let let_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_c env t0 t0') (_hv : par_reduces_c env v v') ",
            "(_hb0 : par_reduces_c env b0 b0') ",
            "(_iht0 : Eq KExpr t0 ({head} dom body) -> C t0') ",
            "(_ihv : Eq KExpr v ({head} dom body) -> C v') ",
            "(_ihb0 : Eq KExpr b0 ({head} dom body) -> C b0') ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) ({head} dom body)) => ",
            "let_ne_pi t0 v b0 dom body (C (instantiate b0' v')) eq)"
        ),
        head = head,
    );

    // let_cong: source let_ t0 v b0 — a GENUINE let node, let /= pi.
    let let_cong_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_c env t0 t0') (_hv : par_reduces_c env v v') ",
            "(_hb0 : par_reduces_c env b0 b0') ",
            "(_iht0 : Eq KExpr t0 ({head} dom body) -> C t0') ",
            "(_ihv : Eq KExpr v ({head} dom body) -> C v') ",
            "(_ihb0 : Eq KExpr b0 ({head} dom body) -> C b0') ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) ({head} dom body)) => ",
            "let_ne_pi t0 v b0 dom body (C (KExpr.let_ t0' v' b0')) eq)"
        ),
        head = head,
    );

    // iota: source e0 with iota_step env e0 e0'. Transport to the pi head, then
    // discharge — a binder head is not a const head.
    let iota_arm = format!(
        concat!(
            "(fun (e0 : KExpr) (e0' : KExpr) (hstep : iota_step env e0 e0') ",
            "(eq : Eq KExpr e0 ({head} dom body)) => ",
            "iota_step_head_none_absurd_type env ({head} dom body) e0' (C e0') ",
            "(Eq.refl (OptionType Name) (OptionType.none Name)) ",
            "(Eq.subst KExpr (fun (x : KExpr) => iota_step env x e0') e0 ({head} dom body) eq hstep))"
        ),
        head = head,
    );

    // proj: source proj s i sub is proj-headed — proj /= pi via proj_ne_pi.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
            "(_hsub : par_reduces_c env sub sub') ",
            "(_ihsub : Eq KExpr sub ({head} dom body) -> C sub') ",
            "(eq : Eq KExpr (KExpr.proj s i sub) ({head} dom body)) => ",
            "proj_ne_pi s i sub dom body (C (KExpr.proj s i sub')) eq)"
        ),
        head = head,
    );

    format!(
        concat!(
            "fun (env : RecEnv) (dom : KExpr) (body : KExpr) (t : KExpr) (C : KExpr -> Type) ",
            "(h : par_reduces_c env ({head} dom body) t) ",
            "(kpi : forall (dom' : KExpr) (body' : KExpr), ",
            "par_reduces_c env dom dom' -> par_reduces_c env body body' -> ",
            "C ({head} dom' body')) => ",
            "par_reduces_c.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} ",
            "({head} dom body) t h (Eq.refl KExpr ({head} dom body))"
        ),
        head = head,
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = lam_arm,
        pi_arm = pi_arm,
        forall_arm = forall_arm,
        let_arm = let_arm,
        iota_arm = iota_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for `par_lift_full_c` (LIFT E-core payoff #8). The FULL
/// relation lift congruence: `par_reduces_c env v v' -> par_reduces_c env
/// (lift_at v c a) (lift_at v' c a)`, under a lift-closed env. The 8 structural
/// arms mirror `par_lift_bd_proof` (lift distributes over the ctor; binder arms
/// and the let body recurse at cutoff `succ c`; beta/let_ transport the
/// contracted index via `lift_instantiate_swap` at d=0; let_cong is the plain
/// componentwise congruence over the genuine let node); the IOTA arm wraps
/// `iota_lift_commutes` (the
/// LIFT E-core keystone) in `par_reduces_c.iota` — a single par-step (lift
/// commutes exactly, no over-the-binder multi-step). This is what the full
/// par_subst's (beta,beta) contraction cross-cases gate on.
fn par_lift_full_c_proof() -> String {
    // Motive: universalize the lift parameters (c, a) and thread RecEnvLiftClosed
    // env (the iota arm needs it).
    let motive = concat!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_c env e e') => ",
        "forall (c : Nat) (a : Nat), RecEnvLiftClosed env -> ",
        "par_reduces_c env (lift_at e c a) (lift_at e' c a))"
    );
    // IH shape for a sub-derivation on SUB => SUB'.
    let ih = concat!(
        "forall (c : Nat) (a : Nat), RecEnvLiftClosed env -> ",
        "par_reduces_c env (lift_at SUB c a) (lift_at SUB' c a)"
    );

    // refl arm.
    let refl_arm = concat!(
        "(fun (e : KExpr) (c : Nat) (a : Nat) (_liftclosed : RecEnvLiftClosed env) => ",
        "par_reduces_c.refl env (lift_at e c a))"
    );

    // app arm: lifted IHs through the (defeq) lift_at_app unfold.
    let app_arm = format!(
        concat!(
            "(fun (f : KExpr) (f' : KExpr) (a0 : KExpr) (a0' : KExpr) ",
            "(_hf : par_reduces_c env f f') (_ha : par_reduces_c env a0 a0') ",
            "(ihf : {ih_f}) (iha : {ih_a}) (c : Nat) (a : Nat) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_c.app env (lift_at f c a) (lift_at f' c a) ",
            "(lift_at a0 c a) (lift_at a0' c a) (ihf c a liftclosed) (iha c a liftclosed))"
        ),
        ih_f = ih.replace("SUB'", "f'").replace("SUB", "f"),
        ih_a = ih.replace("SUB'", "a0'").replace("SUB", "a0"),
    );

    // beta/let_ contraction transport: identical to par_lift_bd_proof's `contract`,
    // but the carried relation is par_reduces_c env (not par_reduces_bd). From
    //   instantiate (lift_at BODYP (succ c) a) (lift_at ARGP c a)
    // to
    //   lift_at (instantiate BODYP ARGP) c a
    // via lift_instantiate_swap BODYP ARGP Nat.zero c a, after rewriting
    // (Nat.add Nat.zero c) to c with nat_zero_add c.
    let contract = |lhs_head: &str, ctor_term: &str, bodyp: &str, argp: &str| -> String {
        let goal_lhs = format!(
            "(lift_at (instantiate_at {bodyp} {argp} Nat.zero) c a)",
            bodyp = bodyp,
            argp = argp,
        );
        let swap_lhs = format!(
            "(lift_at (instantiate_at {bodyp} {argp} Nat.zero) (Nat.add Nat.zero c) a)",
            bodyp = bodyp,
            argp = argp,
        );
        let swap_rhs = format!(
            concat!(
                "(instantiate_at (lift_at {bodyp} (Nat.succ (Nat.add Nat.zero c)) a) ",
                "(lift_at {argp} c a) Nat.zero)"
            ),
            bodyp = bodyp,
            argp = argp,
        );
        let goal_rhs = format!(
            concat!(
                "(instantiate_at (lift_at {bodyp} (Nat.succ c) a) ",
                "(lift_at {argp} c a) Nat.zero)"
            ),
            bodyp = bodyp,
            argp = argp,
        );
        let swap_raw = format!(
            "(lift_instantiate_swap {bodyp} {argp} Nat.zero c a)",
            bodyp = bodyp,
            argp = argp,
        );
        let cong_lhs = format!(
            concat!(
                "(Eq.cong Nat KExpr ",
                "(fun (n : Nat) => lift_at (instantiate_at {bodyp} {argp} Nat.zero) n a) ",
                "c (Nat.add Nat.zero c) ",
                "(Eq.symm Nat (Nat.add Nat.zero c) c (nat_zero_add c)))"
            ),
            bodyp = bodyp,
            argp = argp,
        );
        let cong_rhs = format!(
            concat!(
                "(Eq.cong Nat KExpr ",
                "(fun (n : Nat) => instantiate_at (lift_at {bodyp} (Nat.succ n) a) ",
                "(lift_at {argp} c a) Nat.zero) ",
                "(Nat.add Nat.zero c) c (nat_zero_add c))"
            ),
            bodyp = bodyp,
            argp = argp,
        );
        let eq = format!(
            concat!(
                "(Eq.trans KExpr {goal_lhs} {swap_lhs} {goal_rhs} {cong_lhs} ",
                "(Eq.trans KExpr {swap_lhs} {swap_rhs} {goal_rhs} {swap_raw} {cong_rhs}))"
            ),
            goal_lhs = goal_lhs,
            swap_lhs = swap_lhs,
            swap_rhs = swap_rhs,
            goal_rhs = goal_rhs,
            cong_lhs = cong_lhs,
            cong_rhs = cong_rhs,
            swap_raw = swap_raw,
        );
        // P x := par_reduces_c env lhs_head x.
        let p = format!(
            "(fun (x : KExpr) => par_reduces_c env {lhs_head} x)",
            lhs_head = lhs_head,
        );
        // ctor_term : P goal_rhs ; want P goal_lhs ; transport with Eq.symm eq.
        format!(
            concat!(
                "(Eq.substType KExpr {p} {goal_rhs} {goal_lhs} ",
                "(Eq.symm KExpr {goal_lhs} {goal_rhs} {eq}) ",
                "{ctor_term})"
            ),
            p = p,
            goal_rhs = goal_rhs,
            goal_lhs = goal_lhs,
            eq = eq,
            ctor_term = ctor_term,
        )
    };

    // beta arm.
    let beta_lhs_head = concat!(
        "(KExpr.app (KExpr.lam (lift_at A c a) (lift_at body (Nat.succ c) a)) ",
        "(lift_at arg c a))"
    );
    let beta_ctor = concat!(
        "(par_reduces_c.beta env (lift_at A c a) (lift_at A' c a) ",
        "(lift_at body (Nat.succ c) a) (lift_at body' (Nat.succ c) a) ",
        "(lift_at arg c a) (lift_at arg' c a) ",
        "(ihA c a liftclosed) (ihbody (Nat.succ c) a liftclosed) (iharg c a liftclosed))"
    );
    let beta_arm = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) ",
            "(arg : KExpr) (arg' : KExpr) ",
            "(_hA : par_reduces_c env A A') (_hbody : par_reduces_c env body body') ",
            "(_harg : par_reduces_c env arg arg') ",
            "(ihA : {ih_A}) (ihbody : {ih_body}) (iharg : {ih_arg}) ",
            "(c : Nat) (a : Nat) (liftclosed : RecEnvLiftClosed env) => {body})"
        ),
        ih_A = ih.replace("SUB'", "A'").replace("SUB", "A"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
        ih_arg = ih.replace("SUB'", "arg'").replace("SUB", "arg"),
        body = contract(beta_lhs_head, beta_ctor, "body'", "arg'"),
    );

    // lam/pi/forall_ congruence arm, parametric in the constructor.
    let binder_arm = |ctor: &str| -> String {
        format!(
            concat!(
                "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                "(_hty : par_reduces_c env ty ty') (_hbody : par_reduces_c env body body') ",
                "(ihty : {ih_ty}) (ihbody : {ih_body}) (c : Nat) (a : Nat) (liftclosed : RecEnvLiftClosed env) => ",
                "{ctor} env (lift_at ty c a) (lift_at ty' c a) ",
                "(lift_at body (Nat.succ c) a) (lift_at body' (Nat.succ c) a) ",
                "(ihty c a liftclosed) (ihbody (Nat.succ c) a liftclosed))"
            ),
            ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
            ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
            ctor = ctor,
        )
    };

    // let_ (zeta) arm: the lifted redex skeleton is the GENUINE let node (lift_at
    // distributes over the let_ ctor since the let-promotion — ty/val at cutoff c,
    // body at succ c), then the beta-shaped contraction transport.
    let let_lhs_head = concat!(
        "(KExpr.let_ (lift_at ty c a) (lift_at val c a) ",
        "(lift_at body (Nat.succ c) a))"
    );
    let let_ctor = concat!(
        "(par_reduces_c.let_ env (lift_at ty c a) (lift_at ty' c a) ",
        "(lift_at val c a) (lift_at val' c a) ",
        "(lift_at body (Nat.succ c) a) (lift_at body' (Nat.succ c) a) ",
        "(ihty c a liftclosed) (ihval c a liftclosed) (ihbody (Nat.succ c) a liftclosed))"
    );
    let let_arm = format!(
        concat!(
            "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
            "(body : KExpr) (body' : KExpr) ",
            "(_hty : par_reduces_c env ty ty') (_hval : par_reduces_c env val val') ",
            "(_hbody : par_reduces_c env body body') ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(c : Nat) (a : Nat) (liftclosed : RecEnvLiftClosed env) => {body})"
        ),
        ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
        ih_val = ih.replace("SUB'", "val'").replace("SUB", "val"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
        body = contract(let_lhs_head, let_ctor, "body'", "val'"),
    );

    // let_cong arm: lift distributes over the genuine let node componentwise; the
    // three IHs feed par_reduces_c.let_cong directly (no contraction transport).
    let let_cong_arm = format!(
        concat!(
            "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
            "(body : KExpr) (body' : KExpr) ",
            "(_hty : par_reduces_c env ty ty') (_hval : par_reduces_c env val val') ",
            "(_hbody : par_reduces_c env body body') ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(c : Nat) (a : Nat) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_c.let_cong env (lift_at ty c a) (lift_at ty' c a) ",
            "(lift_at val c a) (lift_at val' c a) ",
            "(lift_at body (Nat.succ c) a) (lift_at body' (Nat.succ c) a) ",
            "(ihty c a liftclosed) (ihval c a liftclosed) (ihbody (Nat.succ c) a liftclosed))"
        ),
        ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
        ih_val = ih.replace("SUB'", "val'").replace("SUB", "val"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
    );

    // iota arm: source e0 => e0' with iota_step env e0 e0'. iota_lift_commutes (the
    // LIFT E-core keystone) gives iota_reduct env (lift e0) = some (lift e0'), i.e.
    // iota_step env (lift e0) (lift e0'); wrap in par_reduces_c.iota — a single
    // par-step (lift commutes exactly). No IH (iota is not recursive).
    let iota_arm = concat!(
        "(fun (e0 : KExpr) (e0' : KExpr) (hstep : iota_step env e0 e0') ",
        "(c : Nat) (a : Nat) (liftclosed : RecEnvLiftClosed env) => ",
        "par_reduces_c.iota env (lift_at e0 c a) (lift_at e0' c a) ",
        "(iota_lift_commutes env e0 e0' c a liftclosed hstep))"
    );

    // proj arm: lift descends into the scrutinee (lift_at (proj s i sub) c a =
    // proj s i (lift_at sub c a)); congruence via par_reduces_c.proj on the IH.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
            "(_hsub : par_reduces_c env sub sub') (ihsub : {ih_sub}) ",
            "(c : Nat) (a : Nat) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_c.proj env s i (lift_at sub c a) (lift_at sub' c a) ",
            "(ihsub c a liftclosed))"
        ),
        ih_sub = ih.replace("SUB'", "sub'").replace("SUB", "sub"),
    );

    format!(
        concat!(
            "fun (env : RecEnv) (v0 : KExpr) (v0' : KExpr) (c0 : Nat) (a0 : Nat) ",
            "(liftclosed0 : RecEnvLiftClosed env) (h0 : par_reduces_c env v0 v0') => ",
            "par_reduces_c.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} ",
            "v0 v0' h0 c0 a0 liftclosed0"
        ),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = binder_arm("par_reduces_c.lam"),
        pi_arm = binder_arm("par_reduces_c.pi"),
        forall_arm = binder_arm("par_reduces_c.forall_"),
        let_arm = let_arm,
        iota_arm = iota_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for `par_strips_c_semi_strip_of_strong` — the SEMI-STRIP
/// lemma of the Huet strong-confluence tiling (abstract `strong_semi_strip`).
///
/// `forall env (SC : <strong confluence of par_reduces_c>) a c,`
/// `par_reduces_c_star env a c -> forall b, par_reduces_c env a b ->`
/// `par_strips_witness_c_star env b c`.
///
/// Outer induction on the star leg `a =>* c` via `par_reduces_c_star.rec`
/// (recursive inductive: motive-first recursor, motive generalized over the
/// single stripped step `b`). The step arm pushes the two single head steps
/// `a => b` and `a => a1` through `SC` to a `par_strong_join_c env b a1`, then
/// case-splits its BOUNDED c-leg via `par_strong_join_c.rec` (non-recursive
/// inductive: indices-first `@`-recursor, like `par_strips_witness_c_star.rec`):
/// the `zero` arm composes `b =>* a1` with the tail `a1 =>* y` (no recursion);
/// the `one` arm feeds its single step into the IH and closes via
/// `par_reduces_c_star_trans`. The `<= 1`-step c-leg is exactly what makes the
/// induction terminate.
fn par_strips_c_semi_strip_of_strong_proof() -> String {
    // The strong-confluence hypothesis type (matches the lemma's SC binder).
    let sc_ty = concat!(
        "(forall (a : KExpr) (b : KExpr) (c : KExpr), ",
        "par_reduces_c env a b -> par_reduces_c env a c -> par_strong_join_c env b c)"
    );
    // Outer recursor motive over the star leg x =>* y (motive abstracts indices).
    let motive = concat!(
        "(fun (x : KExpr) (y : KExpr) (_h : par_reduces_c_star env x y) => ",
        "forall (b : KExpr), par_reduces_c env x b -> par_strips_witness_c_star env b y)"
    );
    // refl arm (x = y = r): strip a single step r => b, meet at b.
    let refl_arm = concat!(
        "(fun (r : KExpr) => ",
        "fun (b : KExpr) (hrb : par_reduces_c env r b) => ",
        "par_strips_witness_c_star.intro env b r b ",
        "(par_reduces_c_star.refl env b) ",
        "(par_subsumes_par_c_star env r b hrb))"
    );
    // step arm: head x => x1, tail x1 =>* y, ih on the tail. Strip a single x => b.
    // SC joins the two head steps at par_strong_join_c env b x1 (b-leg star, x1-leg
    // <= 1). Eliminate it indices-first (@-recursor), motive over the major only.
    let join_motive =
        "(fun (_w : par_strong_join_c env b x1) => par_strips_witness_c_star env b y)";
    // zero arm: the x1-leg took ZERO steps, so b =>* x1 (the meet is x1). Compose
    // with the tail x1 =>* y to land b =>* y; meet at y (no IH needed).
    let zero_arm = concat!(
        "(fun (hbx1 : par_reduces_c_star env b x1) => ",
        "par_strips_witness_c_star.intro env b y y ",
        "(par_reduces_c_star_trans env b x1 y hbx1 htail) ",
        "(par_reduces_c_star.refl env y))"
    );
    // one arm: the x1-leg took ONE step x1 => d, with b =>* d. Feed d into the IH
    // (a single step x1 => d), project the witness, close the b-side via b =>* d =>* m2.
    let one_arm = concat!(
        "(fun (d : KExpr) (hbd : par_reduces_c_star env b d) (hx1d : par_reduces_c env x1 d) => ",
        "@par_strips_witness_c_star.rec env d y ",
        "(fun (_w : par_strips_witness_c_star env d y) => par_strips_witness_c_star env b y) ",
        "(fun (m2 : KExpr) (hdm2 : par_reduces_c_star env d m2) (hym2 : par_reduces_c_star env y m2) => ",
        "par_strips_witness_c_star.intro env b y m2 ",
        "(par_reduces_c_star_trans env b d m2 hbd hdm2) ",
        "hym2) ",
        "(ih d hx1d))"
    );
    let step_arm = format!(
        concat!(
            "(fun (x : KExpr) (x1 : KExpr) (y : KExpr) ",
            "(hstep : par_reduces_c env x x1) ",
            "(htail : par_reduces_c_star env x1 y) ",
            "(ih : forall (b : KExpr), par_reduces_c env x1 b -> par_strips_witness_c_star env b y) => ",
            "fun (b : KExpr) (hxb : par_reduces_c env x b) => ",
            "@par_strong_join_c.rec env b x1 {join_motive} {zero_arm} {one_arm} ",
            "(SC x b x1 hxb hstep))"
        ),
        join_motive = join_motive,
        zero_arm = zero_arm,
        one_arm = one_arm,
    );
    format!(
        concat!(
            "fun (env : RecEnv) (SC : {sc_ty}) (a : KExpr) (c : KExpr) ",
            "(hac : par_reduces_c_star env a c) => ",
            "par_reduces_c_star.rec env {motive} {refl_arm} {step_arm} a c hac"
        ),
        sc_ty = sc_ty,
        motive = motive,
        refl_arm = refl_arm,
        step_arm = step_arm,
    )
}

/// Closed proof term for `par_reduces_c_star_diamond_of_strong` — THE TILING BRICK
/// (abstract `strong_confluent`): Church-Rosser of `par_reduces_c_star` from a
/// strong-confluence hypothesis `SC` for `par_reduces_c`.
///
/// `forall env (SC : <strong confluence of par_reduces_c>) e e1 e2,`
/// `par_reduces_c_star env e e1 -> par_reduces_c_star env e e2 ->`
/// `par_strips_witness_c_star env e1 e2`.
///
/// Induction on the first star leg `e =>* e1` via `par_reduces_c_star.rec` (motive
/// generalized over the second leg `e =>* z`). The refl arm meets at `z`. The step
/// arm strips the single head step `x => x1` against the second leg via
/// `par_strips_c_semi_strip_of_strong` (-> a join `x1 =>* m1`, `z =>* m1`), recurses
/// through the IH on `x1 =>* m1` (-> `y =>* m2`, `m1 =>* m2`), and re-closes the
/// `z`-side via `par_reduces_c_star_trans` (`z =>* m1 =>* m2`). Exactly the BD
/// `par_reduces_bd_star_diamond` shape, with the semi-strip of strong confluence in
/// place of the (here unavailable) true single-step strip.
fn par_reduces_c_star_diamond_of_strong_proof() -> String {
    // The strong-confluence hypothesis type (matches the lemma's SC binder).
    let sc_ty = concat!(
        "(forall (a : KExpr) (b : KExpr) (c : KExpr), ",
        "par_reduces_c env a b -> par_reduces_c env a c -> par_strong_join_c env b c)"
    );
    // Outer recursor motive over the first star leg x =>* y (abstracts indices).
    let motive = concat!(
        "(fun (x : KExpr) (y : KExpr) (_h : par_reduces_c_star env x y) => ",
        "forall (z : KExpr), par_reduces_c_star env x z -> par_strips_witness_c_star env y z)"
    );
    // refl arm (x = y = r): the first leg is empty, so meet at z (r =>* z given).
    let refl_arm = concat!(
        "(fun (r : KExpr) => ",
        "fun (z : KExpr) (hrz : par_reduces_c_star env r z) => ",
        "par_strips_witness_c_star.intro env r z z hrz ",
        "(par_reduces_c_star.refl env z))"
    );
    // step arm: head x => x1, tail x1 =>* y, ih on the tail. Strip x => x1 from the
    // z-leg x =>* z via the semi-strip, then recurse and re-close.
    // Inner: ih m1 hx1m1 : par_strips_witness_c_star y m1; project to (m2, hym2, hm1m2)
    // and close y/z at m2.
    let star_proj = concat!(
        "(@par_strips_witness_c_star.rec env y m1 ",
        "(fun (_w : par_strips_witness_c_star env y m1) => par_strips_witness_c_star env y z) ",
        "(fun (m2 : KExpr) (hym2 : par_reduces_c_star env y m2) (hm1m2 : par_reduces_c_star env m1 m2) => ",
        "par_strips_witness_c_star.intro env y z m2 hym2 ",
        "(par_reduces_c_star_trans env z m1 m2 hzm1 hm1m2)) ",
        "(ih m1 hx1m1))"
    );
    // Outer-inner: semi_strip on (z-leg, single x => x1) : par_strips_witness_c_star x1 z;
    // project to (m1, hx1m1 : x1 =>* m1, hzm1 : z =>* m1).
    let semi_proj = format!(
        concat!(
            "(@par_strips_witness_c_star.rec env x1 z ",
            "(fun (_w : par_strips_witness_c_star env x1 z) => par_strips_witness_c_star env y z) ",
            "(fun (m1 : KExpr) (hx1m1 : par_reduces_c_star env x1 m1) (hzm1 : par_reduces_c_star env z m1) => ",
            "{star_proj}) ",
            "(par_strips_c_semi_strip_of_strong env SC x z hxz x1 hstep))"
        ),
        star_proj = star_proj,
    );
    let step_arm = format!(
        concat!(
            "(fun (x : KExpr) (x1 : KExpr) (y : KExpr) ",
            "(hstep : par_reduces_c env x x1) ",
            "(htail : par_reduces_c_star env x1 y) ",
            "(ih : forall (z : KExpr), par_reduces_c_star env x1 z -> par_strips_witness_c_star env y z) => ",
            "fun (z : KExpr) (hxz : par_reduces_c_star env x z) => ",
            "{semi_proj})"
        ),
        semi_proj = semi_proj,
    );
    format!(
        concat!(
            "fun (env : RecEnv) (SC : {sc_ty}) (e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
            "(h1 : par_reduces_c_star env e e1) (h2 : par_reduces_c_star env e e2) => ",
            "par_reduces_c_star.rec env {motive} {refl_arm} {step_arm} e e1 h1 e2 h2"
        ),
        sc_ty = sc_ty,
        motive = motive,
        refl_arm = refl_arm,
        step_arm = step_arm,
    )
}

/// Closed proof term for `par_reduces_c_let_inv` (let-promotion batch B4): the
/// let-headed CPS inversion over the GENUINE `KExpr.let_` constructor. Mirrors
/// `par_reduces_c_lam_inv_proof`'s source-equation motive. The refl arm folds
/// into the congruence continuation with reflexive sub-derivations; the let_cong
/// arm feeds `kcong` and the let_ (zeta) arm feeds `kzeta`, both transporting
/// their sub-derivations along the component equalities extracted by
/// `let_inj_fst`/`let_inj_snd`/`let_inj_thd`; beta/app are refuted by
/// `let_ne_app`, lam by `let_ne_lam`, pi/forall_ by `let_ne_pi` (via `Eq.symm` —
/// the arm equation runs arm-source = let); the iota arm is discharged because a
/// let is its own spine head (`kexpr_const_name (kapp_fn (let_ ..)) = none` by
/// defeq, `iota_step_head_none_absurd_type`).
fn par_reduces_c_let_inv_proof() -> String {
    let motive = concat!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_c env e e') => ",
        "Eq KExpr e (KExpr.let_ ty val body) -> C e')"
    );

    // refl: reduct e; build C (let_ ty val body) via kcong with reflexive
    // sub-derivations, transport to C e.
    let refl_arm = concat!(
        "(fun (e : KExpr) (eq : Eq KExpr e (KExpr.let_ ty val body)) => ",
        "Eq.substType KExpr C (KExpr.let_ ty val body) e ",
        "(Eq.symm KExpr e (KExpr.let_ ty val body) eq) ",
        "(kcong ty val body (par_reduces_c.refl env ty) (par_reduces_c.refl env val) ",
        "(par_reduces_c.refl env body)))"
    );

    // beta: source app (lam A b0) arg — app /= let (let_ne_app, symm'd).
    let beta_arm = concat!(
        "(fun (A : KExpr) (A' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(arg : KExpr) (arg' : KExpr) ",
        "(_hA : par_reduces_c env A A') (_hb0 : par_reduces_c env b0 b0') ",
        "(_harg : par_reduces_c env arg arg') ",
        "(_ihA : Eq KExpr A (KExpr.let_ ty val body) -> C A') ",
        "(_ihb0 : Eq KExpr b0 (KExpr.let_ ty val body) -> C b0') ",
        "(_iharg : Eq KExpr arg (KExpr.let_ ty val body) -> C arg') ",
        "(eq : Eq KExpr (KExpr.app (KExpr.lam A b0) arg) (KExpr.let_ ty val body)) => ",
        "let_ne_app ty val body (KExpr.lam A b0) arg (C (instantiate b0' arg')) ",
        "(Eq.symm KExpr (KExpr.app (KExpr.lam A b0) arg) (KExpr.let_ ty val body) eq))"
    );

    // app: source app g b — app /= let (let_ne_app, symm'd).
    let app_arm = concat!(
        "(fun (g : KExpr) (g' : KExpr) (b : KExpr) (b' : KExpr) ",
        "(_hg : par_reduces_c env g g') (_hb : par_reduces_c env b b') ",
        "(_ihg : Eq KExpr g (KExpr.let_ ty val body) -> C g') ",
        "(_ihb : Eq KExpr b (KExpr.let_ ty val body) -> C b') ",
        "(eq : Eq KExpr (KExpr.app g b) (KExpr.let_ ty val body)) => ",
        "let_ne_app ty val body g b (C (KExpr.app g' b')) ",
        "(Eq.symm KExpr (KExpr.app g b) (KExpr.let_ ty val body) eq))"
    );

    // lam: source lam t0 b0 — lam /= let (let_ne_lam, symm'd).
    let lam_arm = concat!(
        "(fun (t0 : KExpr) (t0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(_ht : par_reduces_c env t0 t0') (_hb : par_reduces_c env b0 b0') ",
        "(_iht : Eq KExpr t0 (KExpr.let_ ty val body) -> C t0') ",
        "(_ihb : Eq KExpr b0 (KExpr.let_ ty val body) -> C b0') ",
        "(eq : Eq KExpr (KExpr.lam t0 b0) (KExpr.let_ ty val body)) => ",
        "let_ne_lam ty val body t0 b0 (C (KExpr.lam t0' b0')) ",
        "(Eq.symm KExpr (KExpr.lam t0 b0) (KExpr.let_ ty val body) eq))"
    );

    // pi: source pi d0 b0 — pi /= let (let_ne_pi, symm'd).
    let pi_arm = concat!(
        "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(_hd : par_reduces_c env d0 d0') (_hb : par_reduces_c env b0 b0') ",
        "(_ihd : Eq KExpr d0 (KExpr.let_ ty val body) -> C d0') ",
        "(_ihb : Eq KExpr b0 (KExpr.let_ ty val body) -> C b0') ",
        "(eq : Eq KExpr (KExpr.pi d0 b0) (KExpr.let_ ty val body)) => ",
        "let_ne_pi ty val body d0 b0 (C (KExpr.pi d0' b0')) ",
        "(Eq.symm KExpr (KExpr.pi d0 b0) (KExpr.let_ ty val body) eq))"
    );

    // forall_: source forall_ d0 b0 = pi d0 b0 (alias) — pi /= let.
    let forall_arm = concat!(
        "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(_hd : par_reduces_c env d0 d0') (_hb : par_reduces_c env b0 b0') ",
        "(_ihd : Eq KExpr d0 (KExpr.let_ ty val body) -> C d0') ",
        "(_ihb : Eq KExpr b0 (KExpr.let_ ty val body) -> C b0') ",
        "(eq : Eq KExpr (KExpr.forall_ d0 b0) (KExpr.let_ ty val body)) => ",
        "let_ne_pi ty val body d0 b0 (C (KExpr.forall_ d0' b0')) ",
        "(Eq.symm KExpr (KExpr.forall_ d0 b0) (KExpr.let_ ty val body) eq))"
    );

    // let_ (zeta): source let_ ty0 val0 body0, reduct instantiate body0' val0' —
    // the matching contraction arm; feed kzeta with the sub-derivations
    // transported along the let-injectivity component equalities.
    let let_arm = concat!(
        "(fun (ty0 : KExpr) (ty0' : KExpr) (val0 : KExpr) (val0' : KExpr) ",
        "(body0 : KExpr) (body0' : KExpr) ",
        "(hty0 : par_reduces_c env ty0 ty0') (hval0 : par_reduces_c env val0 val0') ",
        "(hbody0 : par_reduces_c env body0 body0') ",
        "(_ihty0 : Eq KExpr ty0 (KExpr.let_ ty val body) -> C ty0') ",
        "(_ihval0 : Eq KExpr val0 (KExpr.let_ ty val body) -> C val0') ",
        "(_ihbody0 : Eq KExpr body0 (KExpr.let_ ty val body) -> C body0') ",
        "(eq : Eq KExpr (KExpr.let_ ty0 val0 body0) (KExpr.let_ ty val body)) => ",
        "kzeta ty0' val0' body0' ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x ty0') ty0 ty ",
        "(let_inj_fst ty0 val0 body0 ty val body eq) hty0) ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x val0') val0 val ",
        "(let_inj_snd ty0 val0 body0 ty val body eq) hval0) ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x body0') body0 body ",
        "(let_inj_thd ty0 val0 body0 ty val body eq) hbody0))"
    );

    // iota: source e0 with iota_step env e0 e0'. Transport the iota_step to the
    // let head (Eq.subst along eq), then discharge — a let is its own spine head,
    // so kexpr_const_name (kapp_fn (let_ ..)) = none by defeq.
    let iota_arm = concat!(
        "(fun (e0 : KExpr) (e0' : KExpr) (hstep : iota_step env e0 e0') ",
        "(eq : Eq KExpr e0 (KExpr.let_ ty val body)) => ",
        "iota_step_head_none_absurd_type env (KExpr.let_ ty val body) e0' (C e0') ",
        "(Eq.refl (OptionType Name) (OptionType.none Name)) ",
        "(Eq.subst KExpr (fun (x : KExpr) => iota_step env x e0') e0 (KExpr.let_ ty val body) eq hstep))"
    );

    // proj: source proj s i sub is proj-headed — proj /= let_ via proj_ne_let.
    let proj_arm = concat!(
        "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
        "(_hsub : par_reduces_c env sub sub') ",
        "(_ihsub : Eq KExpr sub (KExpr.let_ ty val body) -> C sub') ",
        "(eq : Eq KExpr (KExpr.proj s i sub) (KExpr.let_ ty val body)) => ",
        "proj_ne_let s i sub ty val body (C (KExpr.proj s i sub')) eq)"
    );

    // let_cong: source let_ ty0 val0 body0, reduct let_ ty0' val0' body0' — the
    // matching congruence arm; feed kcong with the transported sub-derivations.
    let let_cong_arm = concat!(
        "(fun (ty0 : KExpr) (ty0' : KExpr) (val0 : KExpr) (val0' : KExpr) ",
        "(body0 : KExpr) (body0' : KExpr) ",
        "(hty0 : par_reduces_c env ty0 ty0') (hval0 : par_reduces_c env val0 val0') ",
        "(hbody0 : par_reduces_c env body0 body0') ",
        "(_ihty0 : Eq KExpr ty0 (KExpr.let_ ty val body) -> C ty0') ",
        "(_ihval0 : Eq KExpr val0 (KExpr.let_ ty val body) -> C val0') ",
        "(_ihbody0 : Eq KExpr body0 (KExpr.let_ ty val body) -> C body0') ",
        "(eq : Eq KExpr (KExpr.let_ ty0 val0 body0) (KExpr.let_ ty val body)) => ",
        "kcong ty0' val0' body0' ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x ty0') ty0 ty ",
        "(let_inj_fst ty0 val0 body0 ty val body eq) hty0) ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x val0') val0 val ",
        "(let_inj_snd ty0 val0 body0 ty val body eq) hval0) ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_c env x body0') body0 body ",
        "(let_inj_thd ty0 val0 body0 ty val body eq) hbody0))"
    );

    format!(
        concat!(
            "fun (env : RecEnv) (ty : KExpr) (val : KExpr) (body : KExpr) (t : KExpr) (C : KExpr -> Type) ",
            "(h : par_reduces_c env (KExpr.let_ ty val body) t) ",
            "(kcong : forall (ty' : KExpr) (val' : KExpr) (body' : KExpr), ",
            "par_reduces_c env ty ty' -> par_reduces_c env val val' -> par_reduces_c env body body' -> ",
            "C (KExpr.let_ ty' val' body')) ",
            "(kzeta : forall (ty' : KExpr) (val' : KExpr) (body' : KExpr), ",
            "par_reduces_c env ty ty' -> par_reduces_c env val val' -> par_reduces_c env body body' -> ",
            "C (instantiate body' val')) => ",
            "par_reduces_c.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} ",
            "(KExpr.let_ ty val body) t h (Eq.refl KExpr (KExpr.let_ ty val body))"
        ),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = lam_arm,
        pi_arm = pi_arm,
        forall_arm = forall_arm,
        let_arm = let_arm,
        iota_arm = iota_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for `par_strips_witness_c_star_let` (let-promotion batch
/// B4): the (let, let) congruence combinator at the star-witness level. Three
/// nested `par_strips_witness_c_star.rec` projections (type, value, body) meeting
/// at `let_ t3 v3 b3` via `par_reduces_c_star_let_cong` on each side — the
/// 3-component extension of `par_strips_witness_c_star_app_proof`.
fn par_strips_witness_c_star_let_proof() -> String {
    concat!(
        "fun (env : RecEnv) (t1 : KExpr) (t2 : KExpr) (v1 : KExpr) (v2 : KExpr) ",
        "(b1 : KExpr) (b2 : KExpr) ",
        "(wt : par_strips_witness_c_star env t1 t2) ",
        "(wv : par_strips_witness_c_star env v1 v2) ",
        "(wb : par_strips_witness_c_star env b1 b2) => ",
        "@par_strips_witness_c_star.rec env t1 t2 ",
        "(fun (_wt : par_strips_witness_c_star env t1 t2) => ",
        "par_strips_witness_c_star env (KExpr.let_ t1 v1 b1) (KExpr.let_ t2 v2 b2)) ",
        "(fun (t3 : KExpr) ",
        "(pt1 : par_reduces_c_star env t1 t3) (pt2 : par_reduces_c_star env t2 t3) => ",
        "@par_strips_witness_c_star.rec env v1 v2 ",
        "(fun (_wv : par_strips_witness_c_star env v1 v2) => ",
        "par_strips_witness_c_star env (KExpr.let_ t1 v1 b1) (KExpr.let_ t2 v2 b2)) ",
        "(fun (v3 : KExpr) ",
        "(pv1 : par_reduces_c_star env v1 v3) (pv2 : par_reduces_c_star env v2 v3) => ",
        "@par_strips_witness_c_star.rec env b1 b2 ",
        "(fun (_wb : par_strips_witness_c_star env b1 b2) => ",
        "par_strips_witness_c_star env (KExpr.let_ t1 v1 b1) (KExpr.let_ t2 v2 b2)) ",
        "(fun (b3 : KExpr) ",
        "(pb1 : par_reduces_c_star env b1 b3) (pb2 : par_reduces_c_star env b2 b3) => ",
        "par_strips_witness_c_star.intro env (KExpr.let_ t1 v1 b1) (KExpr.let_ t2 v2 b2) ",
        "(KExpr.let_ t3 v3 b3) ",
        "(par_reduces_c_star_let_cong env t1 t3 v1 v3 b1 b3 pt1 pv1 pb1) ",
        "(par_reduces_c_star_let_cong env t2 t3 v2 v3 b2 b3 pt2 pv2 pb2)) ",
        "wb) ",
        "wv) ",
        "wt"
    )
    .to_string()
}

/// Closed proof term for `par_strips_c_let_zeta` (let-promotion batch B4): the
/// (let_cong, zeta) cross core at the star-witness level — the zeta mirror of
/// `par_strips_c_app_beta_proof`. Projects the body and value sub-diamonds to
/// their meets b3 / v3 (nested `par_strips_witness_c_star.rec`) and assembles the
/// meet at `instantiate b3 v3` via `par_reduces_c_star_let` (left; the type
/// annotation held by refl-star) and `par_subst_full_c_star` (right, depth 0).
fn par_strips_c_let_zeta_proof() -> String {
    // Inner (value) recursor: project wv to v3, build the meet.
    let wv_rec = concat!(
        "(@par_strips_witness_c_star.rec env valf valq ",
        "(fun (_wv : par_strips_witness_c_star env valf valq) => ",
        "par_strips_witness_c_star env (KExpr.let_ tyf valf bodyf) (instantiate bodyq valq)) ",
        "(fun (v3 : KExpr) ",
        "(pv1 : par_reduces_c_star env valf v3) (pv2 : par_reduces_c_star env valq v3) => ",
        "par_strips_witness_c_star.intro env ",
        "(KExpr.let_ tyf valf bodyf) (instantiate bodyq valq) ",
        "(instantiate b3 v3) ",
        // left leg: let_ tyf valf bodyf =>* instantiate b3 v3 (congruence, then zeta)
        "(par_reduces_c_star_let env tyf tyf valf v3 bodyf b3 ",
        "(par_reduces_c_star.refl env tyf) pv1 pbf) ",
        // right leg: instantiate bodyq valq =>* instantiate b3 v3
        "(par_subst_full_c_star env bodyq b3 valq v3 Nat.zero pbq pv2 closed liftclosed)) ",
        "wv)"
    );
    // Outer (body) recursor: project wb to b3, run wv inside.
    let body_rec = format!(
        concat!(
            "(@par_strips_witness_c_star.rec env bodyf bodyq ",
            "(fun (_wb : par_strips_witness_c_star env bodyf bodyq) => ",
            "par_strips_witness_c_star env (KExpr.let_ tyf valf bodyf) (instantiate bodyq valq)) ",
            "(fun (b3 : KExpr) ",
            "(pbf : par_reduces_c_star env bodyf b3) (pbq : par_reduces_c_star env bodyq b3) => ",
            "{wv_rec}) ",
            "wb)"
        ),
        wv_rec = wv_rec,
    );
    format!(
        concat!(
            "fun (env : RecEnv) (tyf : KExpr) (bodyf : KExpr) (valf : KExpr) ",
            "(bodyq : KExpr) (valq : KExpr) ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) ",
            "(wb : par_strips_witness_c_star env bodyf bodyq) ",
            "(wv : par_strips_witness_c_star env valf valq) => ",
            "{body_rec}"
        ),
        body_rec = body_rec,
    )
}

/// Closed proof term for `par_strips_c_zeta_source` (let-promotion batch B4): the
/// zeta-source diamond. Inverts the second leg via `par_reduces_c_let_inv`:
/// kcong → `par_strips_c_let_zeta` (symmetrized — the congruence side catches up
/// by firing the zeta), kzeta → `par_strips_c_subst_join` (same-redex meet on the
/// body/val sub-meets); the iota arm is discharged inside the inversion (a let is
/// its own spine head, never an iota redex).
fn par_strips_c_zeta_source_proof() -> String {
    // kcong: second leg is a let congruence let_ ty2 val2 body2. The zeta side
    // meets it via par_strips_c_let_zeta (tyf := ty2, bodyf := body2, valf := val2,
    // bodyq := body', valq := val'), then symm to land at C (let_ ty2 val2 body2).
    let kcong = concat!(
        "(fun (ty2 : KExpr) (val2 : KExpr) (body2 : KExpr) ",
        "(_h2ty : par_reduces_c env ty ty2) (h2val : par_reduces_c env val val2) ",
        "(h2body : par_reduces_c env body body2) => ",
        "par_strips_witness_c_star_symm env (KExpr.let_ ty2 val2 body2) (instantiate body' val') ",
        "(par_strips_c_let_zeta env ty2 body2 val2 body' val' closed liftclosed ",
        "(db body2 body' h2body hbody) ",
        "(dv val2 val' h2val hval)))"
    );
    // kzeta: both legs contract the SAME redex — subst_join on the sub-meets.
    let kzeta = concat!(
        "(fun (ty2 : KExpr) (val2 : KExpr) (body2 : KExpr) ",
        "(_h2ty : par_reduces_c env ty ty2) (h2val : par_reduces_c env val val2) ",
        "(h2body : par_reduces_c env body body2) => ",
        "par_strips_c_subst_join env body' body2 val' val2 closed liftclosed ",
        "(db body' body2 hbody h2body) ",
        "(dv val' val2 hval h2val))"
    );
    format!(
        concat!(
            "fun (env : RecEnv) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
            "(body : KExpr) (body' : KExpr) (e2 : KExpr) ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) ",
            "(_hty : par_reduces_c env ty ty') (hval : par_reduces_c env val val') ",
            "(hbody : par_reduces_c env body body') ",
            "(h2 : par_reduces_c env (KExpr.let_ ty val body) e2) ",
            "(db : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env body s1 -> par_reduces_c env body s2 -> ",
            "par_strips_witness_c_star env s1 s2) ",
            "(dv : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env val s1 -> par_reduces_c env val s2 -> ",
            "par_strips_witness_c_star env s1 s2) => ",
            "par_reduces_c_let_inv env ty val body e2 ",
            "(fun (x : KExpr) => par_strips_witness_c_star env (instantiate body' val') x) ",
            "h2 {kcong} {kzeta}"
        ),
        kcong = kcong,
        kzeta = kzeta,
    )
}

/// Closed proof term for `par_strips_c_let_struct` (let-promotion batch B4): the
/// let_cong-structural diamond. Inverts the second leg via
/// `par_reduces_c_let_inv`: kcong → the componentwise diagonal
/// (`par_strips_witness_c_star_let` on the ty/val/body sub-diamonds), kzeta →
/// `par_strips_c_let_zeta` (the congruence side catches up by firing the zeta);
/// the iota arm is discharged inside the inversion.
fn par_strips_c_let_struct_proof() -> String {
    // kcong: (let_cong, let_cong) — componentwise meets.
    let kcong = concat!(
        "(fun (ty2 : KExpr) (val2 : KExpr) (body2 : KExpr) ",
        "(h2ty : par_reduces_c env ty ty2) (h2val : par_reduces_c env val val2) ",
        "(h2body : par_reduces_c env body body2) => ",
        "par_strips_witness_c_star_let env ty' ty2 val' val2 body' body2 ",
        "(dty ty' ty2 hty h2ty) (dval val' val2 hval h2val) (dbody body' body2 hbody h2body))"
    );
    // kzeta: (let_cong, zeta) — the congruence side catches up by firing the zeta
    // (par_strips_c_let_zeta with tyf := ty', bodyf := body', valf := val',
    // bodyq := body2, valq := val2).
    let kzeta = concat!(
        "(fun (ty2 : KExpr) (val2 : KExpr) (body2 : KExpr) ",
        "(_h2ty : par_reduces_c env ty ty2) (h2val : par_reduces_c env val val2) ",
        "(h2body : par_reduces_c env body body2) => ",
        "par_strips_c_let_zeta env ty' body' val' body2 val2 closed liftclosed ",
        "(dbody body' body2 hbody h2body) ",
        "(dval val' val2 hval h2val))"
    );
    format!(
        concat!(
            "fun (env : RecEnv) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
            "(body : KExpr) (body' : KExpr) (e2 : KExpr) ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) ",
            "(hty : par_reduces_c env ty ty') (hval : par_reduces_c env val val') ",
            "(hbody : par_reduces_c env body body') ",
            "(h2 : par_reduces_c env (KExpr.let_ ty val body) e2) ",
            "(dty : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env ty s1 -> par_reduces_c env ty s2 -> ",
            "par_strips_witness_c_star env s1 s2) ",
            "(dval : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env val s1 -> par_reduces_c env val s2 -> ",
            "par_strips_witness_c_star env s1 s2) ",
            "(dbody : forall (s1 : KExpr) (s2 : KExpr), par_reduces_c env body s1 -> par_reduces_c env body s2 -> ",
            "par_strips_witness_c_star env s1 s2) => ",
            "par_reduces_c_let_inv env ty val body e2 ",
            "(fun (x : KExpr) => par_strips_witness_c_star env (KExpr.let_ ty' val' body') x) ",
            "h2 {kcong} {kzeta}"
        ),
        kcong = kcong,
        kzeta = kzeta,
    )
}
