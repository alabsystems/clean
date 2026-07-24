// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment H (#2859 computational-iota/delta track): the δ-extended
//! computational parallel reduction `par_reduces_cd` and the 3-way (β+ι+δ)
//! cross-joins.
//!
//! Stage 1 landed the delta operational substrate (`delta_step` + determinism +
//! `delta_subst_commutes` / `delta_lift_commutes`). This module (Stage 2) wires
//! `delta_step` into a parallel-reduction relation and begins the 3-way diamond.
//!
//! Architecture. `par_reduces_c` is indexed by `RecEnv` only — there is no place
//! for `delta_step`'s `DefEnv`. Re-indexing it by two envs would ripple through
//! the entire (already-landed) β+ι development. Instead we package the two envs
//! into a SINGLE product carrier `RedEnv = RecEnv × DefEnv` (so the relation stays
//! single-parameter, exactly like `par_reduces_c`), with projections `red_rec`
//! / `red_def`. The δ-extended relation `par_reduces_cd (env : RedEnv)` is the
//! `par_reduces_c` ctors (iota now reads `iota_step (red_rec env)`) PLUS a
//! `delta` ctor carrying `delta_step (red_def env) e e'`, PLUS a trailing
//! `let_cong` congruence ctor over the genuine `KExpr.let_` node (the
//! non-contracting sibling of the `let_` zeta ctor).
//!
//! delta is structurally SIMPLER than iota for confluence (recon
//! `scratch/delta-computationalize-feasibility.md`): it has NO boundary / major
//! position, so it dodges the §20–§21 over-application cascade that walls the iota
//! single-step diamond. The cross-pair analysis:
//!   - (δ,δ) — determinism (`delta_step_deterministic`); mirror of
//!     `par_strips_iota_iota_c`.
//!   - (δ,β) — head-disjoint: a β redex is `app (lam …) …` (lam-headed), a δ redex
//!     is const-app-headed. Different head ctors ⇒ no root overlap.
//!   - (δ,ι) — head-disjoint GIVEN a `RecEnv`/`DefEnv` name-disjointness interface:
//!     a δ redex's head const carries a `defval`, an ι redex's head const carries
//!     `recmeta`; a const is never simultaneously a definition and a recursor. This
//!     is the faithful interface `RecEnvDefEnvDisjoint` (a HYPOTHESIS, not an
//!     axiom — a real inductive mirroring `RecEnvCtorRecDisjoint`).
//!
//! Runs AFTER `add_par_reduces_c` (par_reduces_c + par_strips_witness_c pattern)
//! and AFTER `add_delta_subst` (DefEnv / defval_for / delta_step / determinism).
//! Part of #2859 (Increment H).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// The name-disjointness fact carried by `RecEnvDefEnvDisjoint env`: any const
/// name `dname` that carries a `DefEnv` unfolding value (`defval_for (red_def env)
/// dname = some _`) carries NO `RecEnv` recursor metadata (`recmeta_for (red_rec
/// env) dname = none`). A const is never simultaneously a definition and a
/// recursor; definitions and recursors occupy disjoint name slots in the kernel
/// env. This is the residual side-condition of the (δ,ι) cross-join: a δ redex's
/// head is a definition, hence not a recursor, hence cannot also be an ι redex
/// head. The δ analogue of `DISJOINT_FACT` (rec_env_closed.rs).
const REC_DEF_DISJOINT_FACT: &str = concat!(
    "forall (dname : Name) (val : KExpr), ",
    "Eq (OptionType KExpr) (defval_for (red_def env) dname) (OptionType.some KExpr val) -> ",
    "Eq (OptionType RecMeta) (recmeta_for (red_rec env) dname) (OptionType.none RecMeta)"
);

impl Specification {
    pub(super) fn add_par_reduces_cd(&mut self) -> Result<(), SpecError> {
        // add_red_env (RedEnv / red_rec / red_def) is now an EARLIER standalone
        // stage (it must precede the reduction families, which the church_rosser_whnf
        // retirement track pins to `the_red_env : RedEnv`). It is no longer called here.
        self.add_recenv_defenv_disjoint()?;
        self.add_par_reduces_cd_relation()?;
        self.add_par_strips_delta_delta_cd()?;
        self.add_delta_cross_disjoint()?;
        self.add_par_reduces_c_subsumes_cd()?;
        Ok(())
    }

    /// Brick 0: the combined reduction environment `RedEnv = RecEnv × DefEnv` and
    /// its projections. A single carrier so the δ-extended relation stays
    /// single-parameter (like `par_reduces_c`), with the recursor / definition
    /// envs recovered by `red_rec` / `red_def`.
    pub(super) fn add_red_env(&mut self) -> Result<(), SpecError> {
        // RedEnv: the product of a recursor environment and a definition
        // environment. The single index of par_reduces_cd.
        self.add_inductive(
            r"inductive RedEnv : Type
| mk : RecEnv → DefEnv → RedEnv",
            "Combined reduction environment RedEnv = RecEnv × DefEnv: a recursor environment (for iota) \
             paired with a definition environment (for delta). The single index of the δ-extended \
             parallel reduction par_reduces_cd; the two envs are recovered by red_rec / red_def. \
             Part of #2859 (Increment H).",
        )?;

        // red_rec: project the RecEnv component (large elimination into Type).
        self.add_recursive_def(
            r"def red_rec (env : RedEnv) : RecEnv := RedEnv.rec (fun (_ : RedEnv) => RecEnv) (fun (r : RecEnv) (d : DefEnv) => r) env",
            "Project the recursor-environment component of a RedEnv. Part of #2859 (Increment H).",
        )?;

        // red_def: project the DefEnv component.
        self.add_recursive_def(
            r"def red_def (env : RedEnv) : DefEnv := RedEnv.rec (fun (_ : RedEnv) => DefEnv) (fun (r : RecEnv) (d : DefEnv) => d) env",
            "Project the definition-environment component of a RedEnv. Part of #2859 (Increment H).",
        )?;

        Ok(())
    }

    /// Brick 1: the `RecEnv`/`DefEnv` name-disjointness faithful interface
    /// `RecEnvDefEnvDisjoint` and its projector `recenv_defenv_disjoint_recmeta`.
    /// The δ analogue of `RecEnvCtorRecDisjoint` (rec_env_closed.rs): a defined
    /// const is never a recursor, so a δ redex head never carries recursor
    /// metadata — which excludes the root (δ,ι) overlap. A defined HYPOTHESIS
    /// (real inductive, proper recursor, NOT an axiom); its witness for the kernel
    /// env is discharged at the end of the track.
    fn add_recenv_defenv_disjoint(&mut self) -> Result<(), SpecError> {
        // RecEnvDefEnvDisjoint env: the name-disjointness interface. Any const with
        // a DefEnv unfolding value carries no RecEnv recursor metadata.
        self.add_inductive(
            &format!(
                "inductive RecEnvDefEnvDisjoint (env : RedEnv) : Type\n| mk : ({REC_DEF_DISJOINT_FACT}) → RecEnvDefEnvDisjoint env"
            ),
            "Name-disjointness interface for a combined reduction environment: any const name with a \
             DefEnv unfolding value (defval_for (red_def env) dname = some _) carries no RecEnv recursor \
             metadata (recmeta_for (red_rec env) dname = none). A const is never simultaneously a \
             definition and a recursor. A defined hypothesis (NOT an axiom); its witness for the kernel \
             env is discharged at the end of the track. The (δ,ι) cross-join consumes its projector to \
             learn a delta redex's head is not a recursor head. The δ analogue of RecEnvCtorRecDisjoint. \
             Part of #2859 (Increment H).",
        )?;

        // recenv_defenv_disjoint_recmeta: the projector the (δ,ι) cross-join
        // consumes. Given the env is name-disjoint and a const has a def value, the
        // const carries no recursor metadata. Mirror of recenv_ctor_rec_disjoint_major.
        self.add_definition(SpecDefinition {
            name: "recenv_defenv_disjoint_recmeta".to_string(),
            type_src: "forall (env : RedEnv) (dname : Name) (val : KExpr), \
                 RecEnvDefEnvDisjoint env -> \
                 Eq (OptionType KExpr) (defval_for (red_def env) dname) (OptionType.some KExpr val) -> \
                 Eq (OptionType RecMeta) (recmeta_for (red_rec env) dname) (OptionType.none RecMeta)"
                .to_string(),
            value_src: Some(format!(
                "fun (env : RedEnv) (dname : Name) (val : KExpr) \
                 (w : RecEnvDefEnvDisjoint env) \
                 (hlk : Eq (OptionType KExpr) (defval_for (red_def env) dname) (OptionType.some KExpr val)) => \
                 RecEnvDefEnvDisjoint.rec env \
                 (fun (_ : RecEnvDefEnvDisjoint env) => \
                 Eq (OptionType RecMeta) (recmeta_for (red_rec env) dname) (OptionType.none RecMeta)) \
                 (fun (hc : {REC_DEF_DISJOINT_FACT}) => hc dname val hlk) \
                 w"
            )),
            is_axiom: false,
            description: concat!(
                "Projector for RecEnvDefEnvDisjoint: in a name-disjoint combined environment, a const ",
                "with a DefEnv unfolding value (defval_for (red_def env) dname = some val) carries no ",
                "RecEnv recursor metadata (recmeta_for (red_rec env) dname = none). Projects the single ",
                "disjointness fact via RecEnvDefEnvDisjoint.rec and applies it to the lookup witness. The ",
                "interface the (δ,ι) cross-join consumes to discharge its delta-head-is-not-a-recursor ",
                "side-condition. The δ analogue of recenv_ctor_rec_disjoint_major. DerivedProved; zero ",
                "axiom_deps. Part of #2859 (Increment H)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "RecEnvDefEnvDisjoint".to_string(),
                "RecEnvDefEnvDisjoint.rec".to_string(),
                "defval_for".to_string(),
                "recmeta_for".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Brick 2 (THE DELTA CTOR): the δ-extended computational parallel reduction
    /// `par_reduces_cd (env : RedEnv)` — the 8 `par_reduces_c` ctors (iota reading
    /// `iota_step (red_rec env)`) PLUS a 9th `delta` ctor carrying `delta_step
    /// (red_def env) e e'` — and the meeting-point package `par_strips_witness_cd`.
    fn add_par_reduces_cd_relation(&mut self) -> Result<(), SpecError> {
        // par_reduces_cd env: the env-indexed computational parallel reduction with
        // delta. Identical to par_reduces_c (over red_rec env) plus the delta arm.
        self.add_inductive(
            r"inductive par_reduces_cd (env : RedEnv) : KExpr → KExpr → Type
| refl : forall (e : KExpr), par_reduces_cd env e e
| beta : forall (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr), par_reduces_cd env A A' → par_reduces_cd env body body' → par_reduces_cd env arg arg' → par_reduces_cd env (KExpr.app (KExpr.lam A body) arg) (instantiate body' arg')
| app : forall (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), par_reduces_cd env f f' → par_reduces_cd env a a' → par_reduces_cd env (KExpr.app f a) (KExpr.app f' a')
| lam : forall (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_cd env ty ty' → par_reduces_cd env body body' → par_reduces_cd env (KExpr.lam ty body) (KExpr.lam ty' body')
| pi : forall (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_cd env dom dom' → par_reduces_cd env body body' → par_reduces_cd env (KExpr.pi dom body) (KExpr.pi dom' body')
| forall_ : forall (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_cd env dom dom' → par_reduces_cd env body body' → par_reduces_cd env (KExpr.forall_ dom body) (KExpr.forall_ dom' body')
| let_ : forall (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_cd env ty ty' → par_reduces_cd env val val' → par_reduces_cd env body body' → par_reduces_cd env (KExpr.let_ ty val body) (instantiate body' val')
| iota : forall (e : KExpr) (e' : KExpr), iota_step (red_rec env) e e' → par_reduces_cd env e e'
| delta : forall (e : KExpr) (e' : KExpr), delta_step (red_def env) e e' → par_reduces_cd env e e'
| let_cong : forall (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_cd env ty ty' → par_reduces_cd env val val' → par_reduces_cd env body body' → par_reduces_cd env (KExpr.let_ ty val body) (KExpr.let_ ty' val' body')
| proj : forall (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr), par_reduces_cd env sub sub' → par_reduces_cd env (KExpr.proj s i sub) (KExpr.proj s i sub')",
            "par_reduces_cd env e e' — the δ-extended computational parallel reduction over a combined \
             RedEnv. The par_reduces_c constructors (refl/beta/app/lam/pi/forall_/let_/iota, iota \
             carrying iota_step (red_rec env)) PLUS a delta constructor carrying the directed, \
             deterministic delta_step (red_def env) e e', PLUS a trailing let_cong constructor: the \
             positional congruence over a genuine let_ node (par-reducing ty/val/body componentwise \
             into KExpr.let_ ty' val' body'), the non-contracting sibling of the let_ (zeta) \
             constructor whose target is instantiate body' val'. delta has no boundary/major position, \
             so the (δ,β) and (δ,ι) cross-cases are head-disjoint and (δ,δ) is determinism; a let_ node \
             is iota/delta-shape-disjoint (its own spine head, headName none), so cross-cases against \
             it are constructor no-confusion. Part of #2859 (Increment H).",
        )?;

        // par_strips_witness_cd env: the par_reduces_cd-legged meeting-point package
        // (mirror of par_strips_witness_c).
        self.add_inductive(
            r"inductive par_strips_witness_cd (env : RedEnv) : KExpr → KExpr → Type
| intro : forall (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), par_reduces_cd env e1 e3 → par_reduces_cd env e2 e3 → par_strips_witness_cd env e1 e2",
            "par_strips_witness_cd env e1 e2 packages a common reduct e3 with par_reduces_cd env e1 e3 and \
             par_reduces_cd env e2 e3 — the single-step join witness for the δ-extended relation. \
             Part of #2859 (Increment H).",
        )?;

        Ok(())
    }

    /// Brick 3: the (δ,δ) cross-join `par_strips_delta_delta_cd` — closed by
    /// determinism ALONE. Two delta_step reducts of the SAME source are equal
    /// (`delta_step_deterministic`), so they meet at e1 = e2: left leg refl e1,
    /// right leg refl e2 transported along e2 = e1. The δ mirror of
    /// `par_strips_iota_iota_c`.
    fn add_par_strips_delta_delta_cd(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_strips_delta_delta_cd".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "delta_step (red_def env) e e1 -> delta_step (red_def env) e e2 -> par_strips_witness_cd env e1 e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
                    "(h1 : delta_step (red_def env) e e1) (h2 : delta_step (red_def env) e e2) => ",
                    "par_strips_witness_cd.intro env e1 e2 e1 ",
                    "(par_reduces_cd.refl env e1) ",
                    "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_cd env e2 x) e2 e1 ",
                    "(Eq.symm KExpr e1 e2 (delta_step_deterministic (red_def env) e e1 e2 h1 h2)) ",
                    "(par_reduces_cd.refl env e2))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The (δ,δ) cross-join of par_strips_cd: two delta_step reductions of the same source meet, ",
                "because delta_step_deterministic forces e1 = e2. Meet at e1 — left leg par_reduces_cd.refl, ",
                "right leg refl transported along e2 = e1 via Eq.substType + Eq.symm. Closed by determinism ",
                "alone (no boundary, no Increment-E dependency). The δ mirror of par_strips_iota_iota_c. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment H)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd".to_string(),
                "par_reduces_cd.refl".to_string(),
                "par_strips_witness_cd".to_string(),
                "par_strips_witness_cd.intro".to_string(),
                "delta_step_deterministic".to_string(),
                "red_def".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Bricks 4 & 5: the head-disjointness cross-case PRIMITIVES that discharge the
    /// (δ,β) and (δ,ι) root overlaps. delta has no boundary, so a δ redex's head is
    /// a definition-const; a β redex is lam-headed and an ι redex is a recursor —
    /// neither can also be a definition, so the overlaps are impossible.
    fn add_delta_cross_disjoint(&mut self) -> Result<(), SpecError> {
        // delta_step_beta_redex_absurd: (δ,β) — a δ step on a β redex is impossible.
        // The β redex `app (lam A body) arg` has head `kapp_fn = lam A body` (kapp_fn
        // descends through app, stops at lam), whose kexpr_const_name is none. So
        // delta_step_head_none_absurd discharges it. The none-head equation holds by
        // Eq.refl: kexpr_const_name (kapp_fn (app (lam A body) arg)) DEFINITIONALLY
        // reduces to none (casesOn on the concrete app then lam ctors, free subterms).
        self.add_definition(SpecDefinition {
            name: "delta_step_beta_redex_absurd".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (A : KExpr) (body : KExpr) (arg : KExpr) (e' : KExpr) (C : Prop), ",
                "delta_step (red_def env) (KExpr.app (KExpr.lam A body) arg) e' -> C"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (A : KExpr) (body : KExpr) (arg : KExpr) (e' : KExpr) (C : Prop) ",
                    "(hd : delta_step (red_def env) (KExpr.app (KExpr.lam A body) arg) e') => ",
                    "delta_step_head_none_absurd (red_def env) (KExpr.app (KExpr.lam A body) arg) e' C ",
                    "(Eq.refl (OptionType Name) (OptionType.none Name)) ",
                    "hd"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "(δ,β) head-disjointness: a delta step on a beta redex app (lam A body) arg is impossible. ",
                "The beta redex's head (kapp_fn descends through app, stops at the lam) has kexpr_const_name ",
                "= none (definitionally), so delta_step_head_none_absurd discharges it via Eq.refl on none. ",
                "The cross-case primitive a single-step strip's (delta,beta) sub-case consumes. DerivedProved, ",
                "zero axiom_deps. Part of #2859 (Increment H)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_step".to_string(),
                "delta_step_head_none_absurd".to_string(),
                "red_def".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // delta_iota_disjoint_absurd: (δ,ι) — a δ step and an ι step on the SAME
        // source are impossible together (given name-disjointness). δ inverts to
        // (head e = some dname, defval (red_def env) dname = some val); ι inverts to
        // (head e = some recname, recmeta (red_rec env) recname = some meta). The two
        // heads coincide (dname = recname by some-injectivity); name-disjointness
        // (recenv_defenv_disjoint_recmeta) forces recmeta (red_rec env) dname = none,
        // contradicting recmeta recname = some meta. The cross-case primitive a strip's
        // (delta,iota) sub-case consumes. NO boundary — strictly simpler than the iota
        // self-overlap.
        {
            let dinv_kont = concat!(
                "(fun (dname : Name) (val : KExpr) ",
                "(hd1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name dname)) ",
                "(hd2 : Eq (OptionType KExpr) (defval_for (red_def env) dname) (OptionType.some KExpr val)) ",
                "(_hd2r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (kapp_args e) val)) (OptionType.some KExpr e1)) => ",
                // invert the iota leg
                "iota_reduct_some_inv (red_rec env) e e2 C hi ",
                "(fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) ",
                "(hi1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname)) ",
                "(hi2 : Eq (OptionType RecMeta) (recmeta_for (red_rec env) recname) (OptionType.some RecMeta meta)) ",
                "(_hi3 : Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (OptionType.some KExpr major)) ",
                "(_hi4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) ",
                "(_hi5 : Eq (OptionType RecRule) (recrule_for (red_rec env) recname cname) (OptionType.some RecRule rule)) ",
                "(_hi5r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule))))) (OptionType.some KExpr e2)) => ",
                // dname = recname (both equal the head const name)
                "option_none_ne_some RecMeta meta C ",
                "(Eq.trans (OptionType RecMeta) (OptionType.none RecMeta) (recmeta_for (red_rec env) recname) (OptionType.some RecMeta meta) ",
                "(Eq.symm (OptionType RecMeta) (recmeta_for (red_rec env) recname) (OptionType.none RecMeta) ",
                "(Eq.trans (OptionType RecMeta) (recmeta_for (red_rec env) recname) (recmeta_for (red_rec env) dname) (OptionType.none RecMeta) ",
                "(Eq.symm (OptionType RecMeta) (recmeta_for (red_rec env) dname) (recmeta_for (red_rec env) recname) ",
                "(Eq.cong Name (OptionType RecMeta) (fun (n : Name) => recmeta_for (red_rec env) n) dname recname ",
                "(option_some_inj Name dname recname ",
                "(Eq.trans (OptionType Name) (OptionType.some Name dname) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname) ",
                "(Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name dname) hd1) hi1)))) ",
                "(recenv_defenv_disjoint_recmeta env dname val w hd2))) ",
                "hi2)))"
            );
            let value = format!(
                "fun (env : RedEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr) (C : Prop) \
                 (w : RecEnvDefEnvDisjoint env) \
                 (hd : delta_step (red_def env) e e1) \
                 (hi : iota_step (red_rec env) e e2) => \
                 delta_reduct_some_inv (red_def env) e e1 C hd {dinv_kont}"
            );
            self.add_definition(SpecDefinition {
                name: "delta_iota_disjoint_absurd".to_string(),
                type_src: concat!(
                    "forall (env : RedEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr) (C : Prop), ",
                    "RecEnvDefEnvDisjoint env -> ",
                    "delta_step (red_def env) e e1 -> iota_step (red_rec env) e e2 -> C"
                )
                .to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: concat!(
                    "(δ,ι) head-disjointness: a delta step and an iota step on the SAME source are impossible ",
                    "together, given the RecEnv/DefEnv name-disjointness interface. delta_reduct_some_inv recovers ",
                    "the def head (some dname) + def value; iota_reduct_some_inv recovers the recursor head (some ",
                    "recname) + recmeta = some meta. The heads coincide (option_some_inj), and ",
                    "recenv_defenv_disjoint_recmeta forces recmeta dname = none — contradicting recmeta recname = ",
                    "some meta via option_none_ne_some. The cross-case primitive a strip's (delta,iota) sub-case ",
                    "consumes (no boundary). DerivedProved, zero axiom_deps. Part of #2859 (Increment H)."
                )
                .to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "delta_step".to_string(),
                    "iota_step".to_string(),
                    "delta_reduct_some_inv".to_string(),
                    "iota_reduct_some_inv".to_string(),
                    "recenv_defenv_disjoint_recmeta".to_string(),
                    "RecEnvDefEnvDisjoint".to_string(),
                    "red_rec".to_string(),
                    "red_def".to_string(),
                    "option_some_inj".to_string(),
                    "option_none_ne_some".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        Ok(())
    }

    /// Brick 6: the embedding `par_reduces_c_subsumes_cd` — every β+ι computational
    /// par-step (over `red_rec env`) is a 3-way par_reduces_cd step. `par_reduces_c.rec`
    /// maps each of the 8 ctors to the identically-shaped par_reduces_cd ctor; the iota
    /// arm maps `iota_step (red_rec env)` straight onto `par_reduces_cd.iota`. The bridge
    /// that lifts the landed β+ι development into the δ-extended relation. Mirror of
    /// par_reduces_c_subsumes_par_p.
    fn add_par_reduces_c_subsumes_cd(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_subsumes_cd".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e : KExpr) (e' : KExpr), ",
                "par_reduces_c (red_rec env) e e' -> par_reduces_cd env e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (e0 : KExpr) (e0' : KExpr) (h0 : par_reduces_c (red_rec env) e0 e0') => ",
                    "par_reduces_c.rec (red_rec env) ",
                    "(fun (x : KExpr) (y : KExpr) (_h : par_reduces_c (red_rec env) x y) => par_reduces_cd env x y) ",
                    // refl
                    "(fun (a : KExpr) => par_reduces_cd.refl env a) ",
                    // beta
                    "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) ",
                    "(_hA : par_reduces_c (red_rec env) A A') (_hbody : par_reduces_c (red_rec env) body body') (_harg : par_reduces_c (red_rec env) arg arg') ",
                    "(ihA : par_reduces_cd env A A') (ihbody : par_reduces_cd env body body') (iharg : par_reduces_cd env arg arg') => ",
                    "par_reduces_cd.beta env A A' body body' arg arg' ihA ihbody iharg) ",
                    // app
                    "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(_hf : par_reduces_c (red_rec env) f f') (_ha : par_reduces_c (red_rec env) a a') ",
                    "(ihf : par_reduces_cd env f f') (iha : par_reduces_cd env a a') => ",
                    "par_reduces_cd.app env f f' a a' ihf iha) ",
                    // lam
                    "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces_c (red_rec env) ty ty') (_hbody : par_reduces_c (red_rec env) body body') ",
                    "(ihty : par_reduces_cd env ty ty') (ihbody : par_reduces_cd env body body') => ",
                    "par_reduces_cd.lam env ty ty' body body' ihty ihbody) ",
                    // pi
                    "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hd : par_reduces_c (red_rec env) dom dom') (_hbody : par_reduces_c (red_rec env) body body') ",
                    "(ihd : par_reduces_cd env dom dom') (ihbody : par_reduces_cd env body body') => ",
                    "par_reduces_cd.pi env dom dom' body body' ihd ihbody) ",
                    // forall_
                    "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hd : par_reduces_c (red_rec env) dom dom') (_hbody : par_reduces_c (red_rec env) body body') ",
                    "(ihd : par_reduces_cd env dom dom') (ihbody : par_reduces_cd env body body') => ",
                    "par_reduces_cd.forall_ env dom dom' body body' ihd ihbody) ",
                    // let_
                    "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces_c (red_rec env) ty ty') (_hval : par_reduces_c (red_rec env) val val') (_hbody : par_reduces_c (red_rec env) body body') ",
                    "(ihty : par_reduces_cd env ty ty') (ihval : par_reduces_cd env val val') (ihbody : par_reduces_cd env body body') => ",
                    "par_reduces_cd.let_ env ty ty' val val' body body' ihty ihval ihbody) ",
                    // iota
                    "(fun (a : KExpr) (a' : KExpr) (hi : iota_step (red_rec env) a a') => ",
                    "par_reduces_cd.iota env a a' hi) ",
                    // let_cong
                    "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces_c (red_rec env) ty ty') (_hval : par_reduces_c (red_rec env) val val') (_hbody : par_reduces_c (red_rec env) body body') ",
                    "(ihty : par_reduces_cd env ty ty') (ihval : par_reduces_cd env val val') (ihbody : par_reduces_cd env body body') => ",
                    "par_reduces_cd.let_cong env ty ty' val val' body body' ihty ihval ihbody) ",
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
                    "(_hsub : par_reduces_c (red_rec env) sub sub') (ihsub : par_reduces_cd env sub sub') => ",
                    "par_reduces_cd.proj env s i sub sub' ihsub) ",
                    "e0 e0' h0"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Embedding par_reduces_c (red_rec env) ⊆ par_reduces_cd env: every β+ι computational par-step ",
                "is a 3-way (β+ι+δ) step. par_reduces_c.rec maps refl/beta/app/lam/pi/forall_/let_/let_cong to the matching ",
                "par_reduces_cd ctor via the IHs; the iota arm maps iota_step (red_rec env) straight onto ",
                "par_reduces_cd.iota. The bridge that lifts the landed β+ι development into the δ-extended relation. ",
                "Mirror of par_reduces_c_subsumes_par_p. DerivedProved, zero axiom_deps. Part of #2859 (Increment H)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.rec".to_string(),
                "par_reduces_cd".to_string(),
                "par_reduces_cd.refl".to_string(),
                "par_reduces_cd.beta".to_string(),
                "par_reduces_cd.app".to_string(),
                "par_reduces_cd.lam".to_string(),
                "par_reduces_cd.pi".to_string(),
                "par_reduces_cd.forall_".to_string(),
                "par_reduces_cd.let_".to_string(),
                "par_reduces_cd.let_cong".to_string(),
                "par_reduces_cd.iota".to_string(),
                "red_rec".to_string(),
                "iota_step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
