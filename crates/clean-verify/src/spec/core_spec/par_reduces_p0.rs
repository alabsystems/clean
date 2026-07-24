// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment G (#2859, the literal-scrutinee development track): the PROPER
//! parallel reduction `par_reduces_p0` — the in-tree analogue of the blueprint's
//! `Par0` (scratch/confluence-proof/Basic.lean:283). It is the sibling of
//! `par_reduces_p` whose iota constructor fires on the LITERAL source redex (not a
//! developed premise), exactly matching the literal-scrutinee developer `dev0`.
//!
//! Why a NEW relation (design §18, 2026-06-24): `par_reduces_p.iota_p` fires on a
//! DEVELOPED premise (`e ⇒_p e2` then `iota_step env e2 r`). The Takahashi triangle
//! `Par0 e e' → Par0 e' (dev0 e)` for `dev0` would need its iota arm to discharge a
//! fire-vs-development join (the kiota wall / `iota_join_star`), which is
//! kernel-REFUTED for the look-ahead developer `cd`. `dev0` decides iota-firing on
//! the LITERAL source spine `iota_reduct env (app f a)`, so the matching parallel
//! relation must ALSO gate on the literal redex. `iota_0` does exactly that:
//!
//! ```text
//! iota_0 : f ⇒_p0 f' → a ⇒_p0 a' →
//!          iota_step env (app f a) r0 →   -- GATE: the LITERAL spine is a redex
//!          iota_step env (app f' a') r →  -- FIRE: the developed redex fires to r
//!          par_reduces_p0 env (app f a) r
//! ```
//!
//! The subterm reductions `f ⇒_p0 f'`, `a ⇒_p0 a'` are BAKED IN (the positive
//! recursive premises, mirroring `Par0.iotaS`'s three premises), and the result `r`
//! is the iota reduct of the DEVELOPED redex `app f' a'` — exactly `dev0`'s
//! reassemble-from-developed-components shape. There is NO look-ahead: the gate is
//! the literal source, so the triangle's iota arm needs NO commutation join.
//!
//! Substrate (this module, mirroring `Par0`'s `par0_lift` / `par0_subst`):
//!   * `par0_lift`  — a par0-step lifts through `lift_at` (both gate and fire commute
//!                    via the UNCONDITIONAL `iota_lift_commutes`; no reduct reassembly).
//!   * `par0_subst` — a par0-step survives `instantiate_at` (both fires commute via
//!                    `iota_subst_commutes`, under `RecEnvClosed`). The blueprint's
//!                    β-case `subst_subst` commutation is NOT needed in the iota arm
//!                    (the iota arm has no binder), exactly as the blueprint notes.
//!
//! These feed `dev0_refl` (`par_reduces_p0 e (dev0 e)`) and the triangle
//! `dev0_triangle` (`par_reduces_p0 e e' → par_reduces_p0 e' (dev0 e)`). Additive;
//! does NOT touch `par_reduces_p`, `cd`, or the marked tower.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// Inline `KExpr.rec` discriminator (7-ctor): non-Lam -> Nat, Lam -> Empty. Used to refute
/// `KExpr.let_ .. = KExpr.lam ..` now that `let_` is a genuine constructor (formerly the
/// app(lam) alias made `app_ne_lam` suffice). Mirrors the discrimination-lane
/// `KEXPR_NOT_LAM_INLINE` (with the trailing let_ minor). let_ maps to Nat.
const KEXPR_NOT_LAM_INLINE: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Nat) ",
    "(fun (_ : Nat) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : ListType Level) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) ",
    "(fun (_ : Nat) => Nat))"
);

impl Specification {
    pub(super) fn add_par_reduces_p0(&mut self) -> Result<(), SpecError> {
        // par_reduces_p0 env: the literal-scrutinee proper parallel reduction. Identical
        // to par_reduces_p EXCEPT the iota constructor iota_0 fires on the LITERAL source
        // redex (app f a) rather than a developed premise. The subterm reductions
        // f ⇒_p0 f', a ⇒_p0 a' are the positive recursive premises (baked-in development,
        // mirroring Par0.iotaS); the gate iota_step env (app f a) r0 proves the literal
        // spine is a redex; the fire iota_step env (app f' a') r delivers the reduct of
        // the DEVELOPED redex (exactly dev0's reassemble-from-developed shape).
        self.add_inductive(
            r"inductive par_reduces_p0 (env : RecEnv) : KExpr → KExpr → Type
| refl : forall (e : KExpr), par_reduces_p0 env e e
| beta : forall (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr), par_reduces_p0 env A A' → par_reduces_p0 env body body' → par_reduces_p0 env arg arg' → par_reduces_p0 env (KExpr.app (KExpr.lam A body) arg) (instantiate body' arg')
| app : forall (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), par_reduces_p0 env f f' → par_reduces_p0 env a a' → par_reduces_p0 env (KExpr.app f a) (KExpr.app f' a')
| lam : forall (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_p0 env ty ty' → par_reduces_p0 env body body' → par_reduces_p0 env (KExpr.lam ty body) (KExpr.lam ty' body')
| pi : forall (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_p0 env dom dom' → par_reduces_p0 env body body' → par_reduces_p0 env (KExpr.pi dom body) (KExpr.pi dom' body')
| forall_ : forall (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_p0 env dom dom' → par_reduces_p0 env body body' → par_reduces_p0 env (KExpr.forall_ dom body) (KExpr.forall_ dom' body')
| let_ : forall (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_p0 env ty ty' → par_reduces_p0 env val val' → par_reduces_p0 env body body' → par_reduces_p0 env (KExpr.let_ ty val body) (instantiate body' val')
| iota_0 : forall (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (r : KExpr) (r0 : KExpr), par_reduces_p0 env f f' → par_reduces_p0 env a a' → iota_step env (KExpr.app f a) r0 → iota_step env (KExpr.app f' a') r → par_reduces_p0 env (KExpr.app f a) r
| let_cong : forall (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_p0 env ty ty' → par_reduces_p0 env val val' → par_reduces_p0 env body body' → par_reduces_p0 env (KExpr.let_ ty val body) (KExpr.let_ ty' val' body')
| proj : forall (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr), par_reduces_p0 env sub sub' → par_reduces_p0 env (KExpr.proj s i sub) (KExpr.proj s i sub')",
            "par_reduces_p0 env e e' — the LITERAL-scrutinee proper parallel reduction (the in-tree \
             analogue of the blueprint's Par0). Identical to par_reduces_p except the iota constructor \
             iota_0 fires on the LITERAL source redex (app f a): the subterm reductions f ⇒_p0 f', \
             a ⇒_p0 a' are baked recursive premises, the gate iota_step env (app f a) r0 witnesses that \
             the literal spine is a redex, and the fire iota_step env (app f' a') r delivers the reduct \
             of the DEVELOPED redex. This is exactly dev0's gate-on-literal/reassemble-from-developed \
             shape — so the development triangle dev0_triangle has NO fire-vs-development iota wall \
             (design §18). The let_ arm is the ZETA contraction (KExpr.let_ ty val body ⇒_p0 instantiate \
             body' val'); the trailing let_cong arm is the positional let CONGRUENCE (⇒_p0 KExpr.let_ ty' \
             val' body') — required now that let_ is a genuine 7th KExpr constructor, not the app(lam) alias. \
             Additive; bridged to par_reduces_p via iota_0 ↦ iota_p. Part of #2859 \
             (Increment G, literal-scrutinee development).",
        )?;

        self.add_par_reduces_p0_bridge()?;
        self.add_par_reduces_p0_subst()?;
        self.add_par_reduces_p0_lam_inv()?;
        self.add_dev0_refl()?;
        self.add_par_reduces_p0_redex_preserved_boundary()?;
        Ok(())
    }

    /// `par_reduces_p0_redex_preserved_boundary` (#2859 Increment G, the dev0_triangle
    /// app-arm BOUNDARY gate): a MINIMAL/boundary iota redex (`iota_reduct env f = none`,
    /// so the major sits at the boundary argument `a`) is PRESERVED under par0-reduction
    /// of its spine. Given the boundary guard `iota_reduct env f = none`, the gate
    /// `iota_step env (app f a) r0`, the developments `f ⇒_p0 f'`, `a ⇒_p0 a'`, and the
    /// sharpened disjointness interface `RecEnvCtorNoRecMeta env`, the DEVELOPED spine
    /// `app f' a'` is STILL a redex — delivered concretely as `iota_reduct env (app f' a')
    /// = some reduct_m` (the a'-side reduct `par_reduces_p_app_redex` reconstructs).
    ///
    /// `iota_step env e e' := iota_reduct env e = some e'` definitionally, so the returned
    /// equation IS an `iota_step` and directly feeds `par_reduces_p0.iota_0`'s gate.
    ///
    /// Proof: invert the gate `iota_step env (app f a) r0` (= `iota_reduct env (app f a) =
    /// some r0`) via `iota_reduct_app_minimal_boundary_idx_type` (Type continuation,
    /// admissible since the boundary guard `iota_reduct env f = none` is in hand),
    /// recovering recname/meta/major/cname/rule + the five lookups + `major = a` +
    /// `major_idx = len(kapp_args f)`; bridge the two par0-steps to `par_reduces_p`
    /// (`par_reduces_p0_subsumes_par_p`); feed `par_reduces_p_app_redex` to reconstruct
    /// `iota_reduct env (app f' a') = some reduct_m`.
    ///
    /// SCOPE (honest): this covers the BOUNDARY case (`iota_reduct env f = none`). The
    /// over-application case (`f` itself a redex) re-introduces the cascading-iota
    /// difficulty that the literal-scrutinee `par_reduces_p0` localizes for the
    /// natRec-constructor blueprint but NOT for Clean's app-spine recursor encoding (an
    /// `iota_0` sub-derivation of `f` reduces `f` to its iota reduct, whose re-application
    /// need not be a redex); it is tracked as the dev0_triangle residual, not faked here.
    fn add_par_reduces_p0_redex_preserved_boundary(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_p0_redex_preserved_boundary".to_string(),
            type_src: par_reduces_p0_redex_preserved_boundary_type(),
            value_src: Some(par_reduces_p0_redex_preserved_boundary_proof()),
            is_axiom: false,
            description: concat!(
                "The dev0_triangle app-arm BOUNDARY gate (#2859 Increment G): a minimal/boundary iota redex ",
                "(iota_reduct env f = none) is PRESERVED under par0-reduction of its spine. Given the boundary ",
                "guard, iota_step env (app f a) r0, f ⇒_p0 f', a ⇒_p0 a', and RecEnvCtorNoRecMeta env, the ",
                "developed spine app f' a' is STILL a redex: iota_reduct env (app f' a') = some reduct_m. Inverts ",
                "the gate via iota_reduct_app_minimal_boundary_idx_type (Type continuation; admissible under the ",
                "boundary guard), bridges the par0-steps to par_reduces_p (par_reduces_p0_subsumes_par_p), and ",
                "reconstructs via par_reduces_p_app_redex. Since iota_step env e e' := iota_reduct env e = some e' ",
                "definitionally, the result IS the iota_0 gate. Covers the BOUNDARY case; the over-application ",
                "case is the tracked dev0_triangle residual (Clean's app-spine recursor re-introduces the cascade ",
                "the natRec-constructor blueprint localizes). DerivedProved, zero axiom_deps. Part of #2859 (G)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p0".to_string(),
                "par_reduces_p0_subsumes_par_p".to_string(),
                "par_reduces_p".to_string(),
                "par_reduces_p_app_redex".to_string(),
                "iota_reduct_app_minimal_boundary_idx_type".to_string(),
                "iota_reduct".to_string(),
                "iota_step".to_string(),
                "RecEnvCtorNoRecMeta".to_string(),
                "kapp_fn".to_string(),
                "kapp_args".to_string(),
                "list_length".to_string(),
                "recmeta_num_params".to_string(),
                "recmeta_num_motives".to_string(),
                "recmeta_num_minors".to_string(),
                "recmeta_num_indices".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// The lam-headed inversion for `par_reduces_p0` (`par_reduces_p0_lam_inv`) — the
    /// `par_reduces_p0` analogue of `par_reduces_p_lam_inv`. From
    /// `par_reduces_p0 env (lam ty body) t` recover that `t = lam ty' body'` with
    /// `ty ⇒_p0 ty'` and `body ⇒_p0 body'`. Identical to the `par_reduces_p` version
    /// EXCEPT the iota arm: `par_reduces_p0.iota_0`'s source is a LITERAL `app f a`,
    /// which is never a lam, so the iota_0 arm discharges directly via `app_ne_lam`
    /// (no `lam_reduct_not_redex` / head-none machinery — the literal-scrutinee design
    /// makes inversion trivial in the iota arm).
    fn add_par_reduces_p0_lam_inv(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_p0_lam_inv".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (ty : KExpr) (body : KExpr) (t : KExpr) (C : KExpr -> Type), ",
                "par_reduces_p0 env (KExpr.lam ty body) t -> ",
                "(forall (ty' : KExpr) (body' : KExpr), ",
                "par_reduces_p0 env ty ty' -> par_reduces_p0 env body body' -> ",
                "C (KExpr.lam ty' body')) -> ",
                "C t"
            )
            .to_string(),
            value_src: Some(par_reduces_p0_lam_inv_proof()),
            is_axiom: false,
            description: concat!(
                "Shape-recovery (inversion) for a lam-headed par_reduces_p0 — from ",
                "par_reduces_p0 env (lam ty body) t recover t = lam ty' body' with ty ⇒_p0 ty' and ",
                "body ⇒_p0 body'. par_reduces_p0.rec with a source-equation motive (e = lam ty body -> C ",
                "e'); the structural non-lam arms refute via app_ne_lam / pi_ne_lam (source /= lam), the ",
                "lam arm transports the component reductions via lam_inj_fst/snd into the klam continuation, ",
                "and the iota_0 arm discharges via app_ne_lam (the literal-scrutinee source app f a is never ",
                "a lam — no lam_reduct_not_redex needed, unlike par_reduces_p's iota_p). DerivedProved, zero ",
                "axiom_deps. Part of #2859 (Increment G)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p0".to_string(),
                "par_reduces_p0.rec".to_string(),
                "par_reduces_p0.refl".to_string(),
                "par_reduces_p0.let_cong".to_string(),
                "iota_step".to_string(),
                "app_ne_lam".to_string(),
                "pi_ne_lam".to_string(),
                "lam_inj_fst".to_string(),
                "lam_inj_snd".to_string(),
                "instantiate".to_string(),
                "KExpr.rec".to_string(),
                "Empty.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// `dev0_refl` (#2859 Increment G): the triangle's reflexive base — every term
    /// par0-reduces to its literal-scrutinee complete development,
    /// `par_reduces_p0 env e (dev0 env e)`. The blueprint obtains
    /// `Par0 e (dev0 e)` as `par0_triangle (par0_refl e)`; here it is a standalone
    /// structural `KExpr.rec` (the `cd_refl` analogue for `dev0` over `par_reduces_p0`).
    ///
    /// The app arm is the crux and is where `dev0`'s literal gate pays off: a NESTED
    /// OptionType convoy with NO redex reconstruction.
    ///   * sort/bvar/const: dev0 is the identity (refl).
    ///   * lam/pi: dev0 distributes (dev0_lam/dev0_pi); par_reduces_p0.lam/.pi on IHs.
    ///   * app, f a syntactic lam (f = lam A b0): dev0_app_lam gives instantiate (dev0
    ///     b0)(dev0 a); par_reduces_p0_lam_inv on ihf recovers A ⇒_p0 dev0 A, b0 ⇒_p0
    ///     dev0 b0, and par_reduces_p0.beta fires (same as cd_refl's lam branch).
    ///   * app, f not a lam: dev0_app exposes the LITERAL gate convoy on iota_reduct env
    ///     (app f a). The none arm reassembles app (dev0 f)(dev0 a) — par_reduces_p0.app
    ///     on the IHs. The some arm (gate eqn : iota_reduct (app f a) = some r0) opens an
    ///     INNER convoy on iota_reduct env (app (dev0 f)(dev0 a)): the inner some arm
    ///     (eqn2 : = some r) feeds par_reduces_p0.iota_0 (gate eqn, fire eqn2 — both
    ///     convoy witnesses, NO reconstruction); the inner none arm reassembles via
    ///     par_reduces_p0.app (opt_default none = the reassembled app).
    fn add_dev0_refl(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "dev0_refl".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr), ",
                "par_reduces_p0 env e (dev0 env e)"
            )
            .to_string(),
            value_src: Some(dev0_refl_proof()),
            is_axiom: false,
            description: concat!(
                "The triangle's reflexive base (#2859 Increment G): every term par0-reduces to its ",
                "literal-scrutinee complete development, par_reduces_p0 env e (dev0 env e). The cd_refl ",
                "analogue for dev0/par_reduces_p0. Structural KExpr.rec: sort/bvar/const via refl; lam/pi ",
                "via dev0_lam/dev0_pi + par_reduces_p0.lam/.pi; the app arm splits on kexpr_lam_cases f — ",
                "the syntactic-lam branch fires par_reduces_p0.beta (par_reduces_p0_lam_inv on ihf recovers ",
                "the binder components, same shape as cd_refl), the false branch opens dev0's LITERAL gate ",
                "convoy (dev0_app) on iota_reduct env (app f a) and, in the some/gate branch, a NESTED convoy ",
                "on iota_reduct env (app (dev0 f)(dev0 a)): the inner-some branch feeds par_reduces_p0.iota_0 ",
                "(gate + fire are BOTH convoy witnesses — no redex reconstruction, no over-application wall, ",
                "the literal-scrutinee payoff), the inner-none branch reassembles via par_reduces_p0.app. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment G, toward dev0_triangle)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p0".to_string(),
                "par_reduces_p0.refl".to_string(),
                "par_reduces_p0.beta".to_string(),
                "par_reduces_p0.app".to_string(),
                "par_reduces_p0.lam".to_string(),
                "par_reduces_p0.pi".to_string(),
                "par_reduces_p0.iota_0".to_string(),
                "par_reduces_p0.let_".to_string(),
                "par_reduces_p0_lam_inv".to_string(),
                "dev0".to_string(),
                "dev0_lam".to_string(),
                "dev0_pi".to_string(),
                "dev0_let".to_string(),
                "dev0_app".to_string(),
                "dev0_app_lam".to_string(),
                "kexpr_lam_cases".to_string(),
                "kexpr_is_lam".to_string(),
                "kexpr_lam_body".to_string(),
                "lam_inj_fst".to_string(),
                "lam_inj_snd".to_string(),
                "opt_default".to_string(),
                "iota_reduct".to_string(),
                "iota_step".to_string(),
                "instantiate".to_string(),
                "KExpr.rec".to_string(),
                "Bool.rec".to_string(),
                "OptionType.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.subst".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// The forward bridge `par_reduces_p0 ⊆ par_reduces_p`: every literal-scrutinee
    /// par0-step is a developed-premise par-step. The eight structural ctors (incl. the trailing let_cong) map to
    /// the matching `par_reduces_p` ctor on the IHs; the `iota_0` ctor maps to
    /// `iota_p` — the baked development `f ⇒_p f' → a ⇒_p a'` (lifted from the IHs via
    /// `par_reduces_p.app`) IS the developed premise `app f a ⇒_p app f' a'`, then the
    /// fire `iota_step env (app f' a') r` discharges `iota_p`. The gate `r0` is
    /// dropped (it only witnessed inhabitation of the literal redex, which `iota_p`
    /// does not need). This is the half that lets `par_reduces_p0`'s development feed
    /// any `par_reduces_p`-level confluence machinery.
    fn add_par_reduces_p0_bridge(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_p0_subsumes_par_p".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr), ",
                "par_reduces_p0 env e e' -> par_reduces_p env e e'"
            )
            .to_string(),
            value_src: Some(par_reduces_p0_subsumes_par_p_proof()),
            is_axiom: false,
            description: concat!(
                "Embedding par_reduces_p0 ⊆ par_reduces_p: every literal-scrutinee par0-step is a ",
                "developed-premise par-step. par_reduces_p0.rec mapping refl/beta/app/lam/pi/forall_/let_/let_cong ",
                "to the matching par_reduces_p ctor via the IHs; the iota_0 ctor maps to iota_p — the baked ",
                "development (app f a ⇒_p app f' a' via par_reduces_p.app on the two IHs) is the iota_p ",
                "developed premise, then the fire iota_step env (app f' a') r discharges iota_p (the gate r0 ",
                "is dropped, iota_p does not need it). Lets par_reduces_p0 development feed any ",
                "par_reduces_p-level machinery. DerivedProved, zero axiom_deps. Part of #2859 (Increment G)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p0".to_string(),
                "par_reduces_p0.rec".to_string(),
                "par_reduces_p".to_string(),
                "par_reduces_p.refl".to_string(),
                "par_reduces_p.beta".to_string(),
                "par_reduces_p.app".to_string(),
                "par_reduces_p.lam".to_string(),
                "par_reduces_p.pi".to_string(),
                "par_reduces_p.forall_".to_string(),
                "par_reduces_p.let_".to_string(),
                "par_reduces_p.iota_p".to_string(),
                "par_reduces_p.let_cong".to_string(),
                "iota_step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// The lift/subst substrate for `par_reduces_p0` — the blueprint's `par0_lift` /
    /// `par0_subst` (Basic.lean:330,351). Both induct on the par0-DERIVATION; the eight
    /// structural arms distribute over `lift_at` / `instantiate_at` definitionally and
    /// rebuild via the matching ctor on the IHs (binder arms recurse at `succ` depth),
    /// and the `iota_0` arm lifts/substitutes BOTH the gate and fire via the bare
    /// `iota_step` commutation lemmas (`iota_lift_commutes` / `iota_subst_commutes`) —
    /// NO reduct-reassembly, since `iota_0` carries only `iota_step`s, not a reduct
    /// congruence.
    fn add_par_reduces_p0_subst(&mut self) -> Result<(), SpecError> {
        // par0_lift: a par0-step lifts through lift_at, under RecEnvLiftClosed (which
        // iota_lift_commutes gates on). par_reduces_p0.rec on the derivation; the iota_0
        // arm lifts the gate iota_step env (app f a) r0 and the fire iota_step env (app
        // f' a') r via iota_lift_commutes (lift_at distributes over app definitionally),
        // and reassembles via iota_0 on the lifted subterm IHs.
        self.add_definition(SpecDefinition {
            name: "par0_lift".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr) (c : Nat) (a : Nat), ",
                "RecEnvLiftClosed env -> par_reduces_p0 env e e' -> ",
                "par_reduces_p0 env (lift_at e c a) (lift_at e' c a)"
            )
            .to_string(),
            value_src: Some(par0_lift_proof()),
            is_axiom: false,
            description: concat!(
                "The lift congruence for par_reduces_p0 (blueprint par0_lift): under RecEnvLiftClosed, ",
                "e ⇒_p0 e' gives lift_at e c a ⇒_p0 lift_at e' c a. par_reduces_p0.rec on the derivation; ",
                "the structural arms (incl. the trailing let_cong) mirror par_lift_p_full (lift distributes over app/binders ",
                "definitionally, binder arms recurse at succ cutoff, beta/let transport the contracted ",
                "index via lift_instantiate_swap), and the iota_0 arm lifts BOTH the gate iota_step (app f ",
                "a) r0 and the fire iota_step (app f' a') r via the UNCONDITIONAL iota_lift_commutes, then ",
                "reassembles via iota_0 on the lifted subterm IHs — no reduct reassembly (iota_0 carries ",
                "bare iota_steps). DerivedProved, zero axiom_deps. Part of #2859 (Increment G)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p0".to_string(),
                "par_reduces_p0.rec".to_string(),
                "par_reduces_p0.refl".to_string(),
                "par_reduces_p0.beta".to_string(),
                "par_reduces_p0.app".to_string(),
                "par_reduces_p0.lam".to_string(),
                "par_reduces_p0.pi".to_string(),
                "par_reduces_p0.forall_".to_string(),
                "par_reduces_p0.let_".to_string(),
                "par_reduces_p0.iota_0".to_string(),
                "par_reduces_p0.let_cong".to_string(),
                "iota_step".to_string(),
                "iota_lift_commutes".to_string(),
                "RecEnvLiftClosed".to_string(),
                "lift_at".to_string(),
                "instantiate_at".to_string(),
                "lift_instantiate_swap".to_string(),
                "nat_zero_add".to_string(),
                "Eq.substType".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par0_subst: a par0-step survives instantiate_at, under RecEnvClosed +
        // RecEnvLiftClosed. par_reduces_p0.rec on the derivation; the bvar-free
        // structural arms distribute over instantiate_at definitionally; the beta/let
        // arms transport the nested substitution via instantiate_nested_commutes_zero_subst
        // (the blueprint's subst_subst); the iota_0 arm substitutes BOTH gate and fire
        // via iota_subst_commutes (under RecEnvClosed). The substituted VALUE is held
        // FIXED (v not reduced) — this is the body-congruence direction par_subst_p0_full
        // is built on; the full two-sided version is left for the next chunk.
        self.add_definition(SpecDefinition {
            name: "par0_subst".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr) (v : KExpr) (d : Nat), ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> par_reduces_p0 env e e' -> ",
                "par_reduces_p0 env (instantiate_at e v d) (instantiate_at e' v d)"
            )
            .to_string(),
            value_src: Some(par0_subst_proof()),
            is_axiom: false,
            description: concat!(
                "The substitution congruence for par_reduces_p0 (blueprint par0_subst, body-congruence ",
                "direction): under RecEnvClosed + RecEnvLiftClosed, e ⇒_p0 e' gives instantiate_at e v d ",
                "⇒_p0 instantiate_at e' v d (the substituted value v held FIXED). par_reduces_p0.rec on the ",
                "derivation; structural arms distribute over instantiate_at definitionally (binder arms ",
                "recurse at succ depth), beta/let transport the nested substitution via ",
                "instantiate_nested_commutes_zero_subst (the blueprint subst_subst), and the iota_0 arm ",
                "substitutes BOTH the gate and fire via iota_subst_commutes (under RecEnvClosed) — the ",
                "blueprint notes the iota arm needs NO commutation, and indeed bare iota_steps survive ",
                "instantiate with no binder bookkeeping. The body-congruence base the full par_subst_p0 ",
                "(value-reducing) builds on. DerivedProved, zero axiom_deps. Part of #2859 (Increment G)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p0".to_string(),
                "par_reduces_p0.rec".to_string(),
                "par_reduces_p0.refl".to_string(),
                "par_reduces_p0.beta".to_string(),
                "par_reduces_p0.app".to_string(),
                "par_reduces_p0.lam".to_string(),
                "par_reduces_p0.pi".to_string(),
                "par_reduces_p0.forall_".to_string(),
                "par_reduces_p0.let_".to_string(),
                "par_reduces_p0.iota_0".to_string(),
                "par_reduces_p0.let_cong".to_string(),
                "iota_step".to_string(),
                "iota_subst_commutes".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "instantiate_at".to_string(),
                "instantiate_nested_commutes_zero_subst".to_string(),
                "Eq.substType".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_subst_refl_p0_full: the value-congruence at a FIXED body — under
        // RecEnvLiftClosed, v ⇒_p0 v' gives instantiate_at e v d ⇒_p0 instantiate_at e v'
        // d (the body e is held fixed; only the substituted value reduces). KExpr.rec on
        // e with the double-Nat.rec convoy at the bvar arm; the i=d leaf lifts the value
        // reduction by the binder depth via par0_lift (in ONE par0-step). The value-side
        // refl base the two-sided par_subst_p0 recurses into. Verbatim p→p0 port of
        // par_subst_refl_p_full.
        self.add_definition(SpecDefinition {
            name: "par_subst_refl_p0_full".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (v : KExpr) (v' : KExpr) (d : Nat), ",
                "RecEnvLiftClosed env -> par_reduces_p0 env v v' -> ",
                "par_reduces_p0 env (instantiate_at e v d) (instantiate_at e v' d)"
            )
            .to_string(),
            value_src: Some(par_subst_refl_p0_full_proof()),
            is_axiom: false,
            description: concat!(
                "The value-congruence at a FIXED body for par_reduces_p0: under RecEnvLiftClosed, ",
                "v ⇒_p0 v' gives instantiate_at e v d ⇒_p0 instantiate_at e v' d. KExpr.rec on e with the ",
                "double-Nat.rec bvar convoy (i<d / i=d / i>d); the i=d leaf calls par0_lift (the value is ",
                "lifted by the binder depth) in ONE par0-step, structural arms use par_reduces_p0.{refl,app,",
                "lam,pi}. Verbatim p→p0 port of par_subst_refl_p_full. The value-side refl base the two-sided ",
                "par_subst_p0 recurses into. DerivedProved, zero axiom_deps. Part of #2859 (Increment G)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p0".to_string(),
                "par_reduces_p0.refl".to_string(),
                "par_reduces_p0.app".to_string(),
                "par_reduces_p0.lam".to_string(),
                "par_reduces_p0.pi".to_string(),
                "par_reduces_p0.let_cong".to_string(),
                "par0_lift".to_string(),
                "RecEnvLiftClosed".to_string(),
                "instantiate_at".to_string(),
                "lift_at".to_string(),
                "KExpr.rec".to_string(),
                "Nat.rec".to_string(),
                "instantiate_at_bvar".to_string(),
                "instantiate_bvar_at".to_string(),
                "instantiate_bvar_at_below".to_string(),
                "instantiate_bvar_at_above".to_string(),
                "instantiate_at_bvar_eq_from_zero_witnesses".to_string(),
                "nat_pos_witness_from_succ_eq".to_string(),
                "nat_sub_zero_of_sub_pos".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_subst_p0: the FULL two-sided single-step substitution lemma for
        // par_reduces_p0 (the blueprint's par0_subst, Basic.lean:351). Given e ⇒_p0 e'
        // and v ⇒_p0 v' (and both closure predicates), the instantiations reduce in a
        // SINGLE par_reduces_p0 step. par_reduces_p0.rec on e ⇒_p0 e' with a depth-
        // generalized motive threading v ⇒_p0 v'; structural arms rebuild via the
        // matching ctor, beta/let_ transport the nested substitution via
        // instantiate_nested_commutes_zero_subst, and the iota_0 arm substitutes the
        // gate (under v) and the fire (under v') via iota_subst_commutes — assembling in
        // ONE par0-step with NO reduct reassembly. The substrate dev0_triangle's beta arm
        // needs. Verbatim p→p0 port of par_subst_p.
        self.add_definition(SpecDefinition {
            name: "par_subst_p0".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr) (v : KExpr) (v' : KExpr) (d : Nat), ",
                "par_reduces_p0 env e e' -> par_reduces_p0 env v v' -> ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_reduces_p0 env (instantiate_at e v d) (instantiate_at e' v' d)"
            )
            .to_string(),
            value_src: Some(par_subst_p0_proof()),
            is_axiom: false,
            description: concat!(
                "The FULL two-sided single-step substitution lemma for par_reduces_p0 (blueprint par0_subst). ",
                "Given e ⇒_p0 e' and v ⇒_p0 v' (and both closure predicates), the instantiations reduce in a ",
                "SINGLE par_reduces_p0 step. par_reduces_p0.rec on e ⇒_p0 e' with a depth-generalized motive ",
                "threading v ⇒_p0 v'; refl via par_subst_refl_p0_full, app/lam/pi/forall_ via the ctors, ",
                "beta/let_ via the ctor + instantiate_nested_commutes_zero_subst transport, and the iota_0 arm ",
                "substitutes the gate (under v) and the fire (under v') via iota_subst_commutes, reassembling ",
                "in ONE par0-step. Verbatim p→p0 port of par_subst_p; the substrate dev0_triangle's beta arm ",
                "consumes. DerivedProved, zero axiom_deps. Part of #2859 (Increment G)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p0".to_string(),
                "par_reduces_p0.rec".to_string(),
                "par_reduces_p0.refl".to_string(),
                "par_reduces_p0.beta".to_string(),
                "par_reduces_p0.app".to_string(),
                "par_reduces_p0.lam".to_string(),
                "par_reduces_p0.pi".to_string(),
                "par_reduces_p0.forall_".to_string(),
                "par_reduces_p0.let_".to_string(),
                "par_reduces_p0.iota_0".to_string(),
                "par_reduces_p0.let_cong".to_string(),
                "par_subst_refl_p0_full".to_string(),
                "iota_subst_commutes".to_string(),
                "iota_step".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "instantiate_at".to_string(),
                "instantiate_nested_commutes_zero_subst".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

/// Closed proof term for `par_reduces_p0_subsumes_par_p` — `par_reduces_p0.rec` into
/// `par_reduces_p`, ctor-for-ctor on the IHs; the `iota_0` arm builds the developed
/// premise `app f a ⇒_p app f' a'` (`par_reduces_p.app` on the two IHs) and fires
/// `iota_p`.
fn par_reduces_p0_subsumes_par_p_proof() -> String {
    let motive =
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_p0 env e e') => par_reduces_p env e e')";
    let refl_arm = "(fun (e : KExpr) => par_reduces_p.refl env e)";
    let beta_arm = concat!(
        "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) ",
        "(_hA : par_reduces_p0 env A A') (_hbody : par_reduces_p0 env body body') (_harg : par_reduces_p0 env arg arg') ",
        "(ihA : par_reduces_p env A A') (ihbody : par_reduces_p env body body') (iharg : par_reduces_p env arg arg') => ",
        "par_reduces_p.beta env A A' body body' arg arg' ihA ihbody iharg)"
    );
    let app_arm = concat!(
        "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
        "(_hf : par_reduces_p0 env f f') (_ha : par_reduces_p0 env a a') ",
        "(ihf : par_reduces_p env f f') (iha : par_reduces_p env a a') => ",
        "par_reduces_p.app env f f' a a' ihf iha)"
    );
    let binder_arm = |ctor: &str| -> String {
        format!(
            concat!(
                "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                "(_hty : par_reduces_p0 env ty ty') (_hbody : par_reduces_p0 env body body') ",
                "(ihty : par_reduces_p env ty ty') (ihbody : par_reduces_p env body body') => ",
                "{ctor} env ty ty' body body' ihty ihbody)"
            ),
            ctor = ctor,
        )
    };
    let let_arm = concat!(
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_p0 env ty ty') (_hval : par_reduces_p0 env val val') (_hbody : par_reduces_p0 env body body') ",
        "(ihty : par_reduces_p env ty ty') (ihval : par_reduces_p env val val') (ihbody : par_reduces_p env body body') => ",
        "par_reduces_p.let_ env ty ty' val val' body body' ihty ihval ihbody)"
    );
    // iota_0 arm: developed premise (app f a ⇒_p app f' a') via par_reduces_p.app on
    // the IHs, then iota_p fires iota_step env (app f' a') r. The gate r0 is dropped.
    let iota_arm = concat!(
        "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (r : KExpr) (r0 : KExpr) ",
        "(_hf : par_reduces_p0 env f f') (_ha : par_reduces_p0 env a a') ",
        "(_hgate : iota_step env (KExpr.app f a) r0) (hfire : iota_step env (KExpr.app f' a') r) ",
        "(ihf : par_reduces_p env f f') (iha : par_reduces_p env a a') => ",
        "par_reduces_p.iota_p env (KExpr.app f a) (KExpr.app f' a') r ",
        "(par_reduces_p.app env f f' a a' ihf iha) hfire)"
    );
    // let_cong arm: map the p0 let congruence to the matching par_reduces_p.let_cong.
    let let_cong_arm = concat!(
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_p0 env ty ty') (_hval : par_reduces_p0 env val val') (_hbody : par_reduces_p0 env body body') ",
        "(ihty : par_reduces_p env ty ty') (ihval : par_reduces_p env val val') (ihbody : par_reduces_p env body body') => ",
        "par_reduces_p.let_cong env ty ty' val val' body body' ihty ihval ihbody)"
    );
    let proj_arm = concat!(
        "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
        "(_hsub : par_reduces_p0 env sub sub') (ihsub : par_reduces_p env sub sub') => ",
        "par_reduces_p.proj env s i sub sub' ihsub)"
    );
    format!(
        concat!(
            "fun (env : RecEnv) (e0 : KExpr) (e0' : KExpr) (h0 : par_reduces_p0 env e0 e0') => ",
            "par_reduces_p0.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} {lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} ",
            "e0 e0' h0"
        ),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = binder_arm("par_reduces_p.lam"),
        pi_arm = binder_arm("par_reduces_p.pi"),
        forall_arm = binder_arm("par_reduces_p.forall_"),
        let_arm = let_arm,
        iota_arm = iota_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for `par0_lift` — `par_reduces_p0.rec` on the derivation. The
/// structural arms mirror `par_lift_p_full`'s arms verbatim (the lift algebra is
/// relation-agnostic); the `iota_0` arm lifts gate + fire via `iota_lift_commutes`
/// and reassembles via `iota_0` on the lifted subterm IHs.
fn par0_lift_proof() -> String {
    // Motive over the derivation: universalize c, a; thread RecEnvLiftClosed.
    let motive = concat!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_p0 env e e') => ",
        "forall (c : Nat) (a : Nat), RecEnvLiftClosed env -> ",
        "par_reduces_p0 env (lift_at e c a) (lift_at e' c a))"
    );
    // IH shape for a sub-pair SUB ⇒ SUB'.
    let ih = concat!(
        "forall (c : Nat) (a : Nat), RecEnvLiftClosed env -> ",
        "par_reduces_p0 env (lift_at SUB c a) (lift_at SUB' c a)"
    );
    let refl_arm = concat!(
        "(fun (e : KExpr) (c : Nat) (a : Nat) (_liftclosed : RecEnvLiftClosed env) => ",
        "par_reduces_p0.refl env (lift_at e c a))"
    );
    let app_arm = format!(
        concat!(
            "(fun (f : KExpr) (f' : KExpr) (a0 : KExpr) (a0' : KExpr) ",
            "(_hf : par_reduces_p0 env f f') (_ha : par_reduces_p0 env a0 a0') ",
            "(ihf : {ih_f}) (iha : {ih_a}) (c : Nat) (a : Nat) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_p0.app env (lift_at f c a) (lift_at f' c a) ",
            "(lift_at a0 c a) (lift_at a0' c a) (ihf c a liftclosed) (iha c a liftclosed))"
        ),
        ih_f = ih.replace("SUB'", "f'").replace("SUB", "f"),
        ih_a = ih.replace("SUB'", "a0'").replace("SUB", "a0"),
    );
    // beta/let contraction transport (relation = par_reduces_p0; eq is shared lift algebra,
    // verbatim from par_lift_p_full's `contract`).
    let contract = |lhs_head: &str, ctor_term: &str, bodyp: &str, argp: &str| -> String {
        let goal_lhs = format!("(lift_at (instantiate_at {bodyp} {argp} Nat.zero) c a)");
        let swap_lhs =
            format!("(lift_at (instantiate_at {bodyp} {argp} Nat.zero) (Nat.add Nat.zero c) a)");
        let swap_rhs = format!(
            "(instantiate_at (lift_at {bodyp} (Nat.succ (Nat.add Nat.zero c)) a) (lift_at {argp} c a) Nat.zero)"
        );
        let goal_rhs = format!(
            "(instantiate_at (lift_at {bodyp} (Nat.succ c) a) (lift_at {argp} c a) Nat.zero)"
        );
        let swap_raw = format!("(lift_instantiate_swap {bodyp} {argp} Nat.zero c a)");
        let cong_lhs = format!(
            "(Eq.cong Nat KExpr (fun (n : Nat) => lift_at (instantiate_at {bodyp} {argp} Nat.zero) n a) c (Nat.add Nat.zero c) (Eq.symm Nat (Nat.add Nat.zero c) c (nat_zero_add c)))"
        );
        let cong_rhs = format!(
            "(Eq.cong Nat KExpr (fun (n : Nat) => instantiate_at (lift_at {bodyp} (Nat.succ n) a) (lift_at {argp} c a) Nat.zero) (Nat.add Nat.zero c) c (nat_zero_add c))"
        );
        let eq = format!(
            "(Eq.trans KExpr {goal_lhs} {swap_lhs} {goal_rhs} {cong_lhs} (Eq.trans KExpr {swap_lhs} {swap_rhs} {goal_rhs} {swap_raw} {cong_rhs}))"
        );
        let p = format!("(fun (x : KExpr) => par_reduces_p0 env {lhs_head} x)");
        format!(
            "(Eq.substType KExpr {p} {goal_rhs} {goal_lhs} (Eq.symm KExpr {goal_lhs} {goal_rhs} {eq}) {ctor_term})"
        )
    };
    let beta_lhs_head = concat!(
        "(KExpr.app (KExpr.lam (lift_at A c a) (lift_at body (Nat.succ c) a)) ",
        "(lift_at arg c a))"
    );
    let beta_ctor = concat!(
        "(par_reduces_p0.beta env (lift_at A c a) (lift_at A' c a) ",
        "(lift_at body (Nat.succ c) a) (lift_at body' (Nat.succ c) a) ",
        "(lift_at arg c a) (lift_at arg' c a) ",
        "(ihA c a liftclosed) (ihbody (Nat.succ c) a liftclosed) (iharg c a liftclosed))"
    );
    let beta_arm = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) ",
            "(arg : KExpr) (arg' : KExpr) ",
            "(_hA : par_reduces_p0 env A A') (_hbody : par_reduces_p0 env body body') ",
            "(_harg : par_reduces_p0 env arg arg') ",
            "(ihA : {ih_A}) (ihbody : {ih_body}) (iharg : {ih_arg}) ",
            "(c : Nat) (a : Nat) (liftclosed : RecEnvLiftClosed env) => {body})"
        ),
        ih_A = ih.replace("SUB'", "A'").replace("SUB", "A"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
        ih_arg = ih.replace("SUB'", "arg'").replace("SUB", "arg"),
        body = contract(beta_lhs_head, beta_ctor, "body'", "arg'"),
    );
    let binder_arm = |ctor: &str| -> String {
        format!(
            concat!(
                "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                "(_hty : par_reduces_p0 env ty ty') (_hbody : par_reduces_p0 env body body') ",
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
    // let_ (ZETA): lift_at (KExpr.let_ ty val body) c a = KExpr.let_ (lift ty)(lift val)
    // (lift body succ) (genuine ctor); ctor target instantiates, transported by the contract.
    let let_lhs_head =
        "(KExpr.let_ (lift_at ty c a) (lift_at val c a) (lift_at body (Nat.succ c) a))";
    let let_ctor = concat!(
        "(par_reduces_p0.let_ env (lift_at ty c a) (lift_at ty' c a) ",
        "(lift_at val c a) (lift_at val' c a) ",
        "(lift_at body (Nat.succ c) a) (lift_at body' (Nat.succ c) a) ",
        "(ihty c a liftclosed) (ihval c a liftclosed) (ihbody (Nat.succ c) a liftclosed))"
    );
    let let_arm = format!(
        concat!(
            "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
            "(body : KExpr) (body' : KExpr) ",
            "(_hty : par_reduces_p0 env ty ty') (_hval : par_reduces_p0 env val val') ",
            "(_hbody : par_reduces_p0 env body body') ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(c : Nat) (a : Nat) (liftclosed : RecEnvLiftClosed env) => {body})"
        ),
        ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
        ih_val = ih.replace("SUB'", "val'").replace("SUB", "val"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
        body = contract(let_lhs_head, let_ctor, "body'", "val'"),
    );
    // let_cong (trailing CONGRUENCE): lift distributes over let_ definitionally, so
    // par_reduces_p0.let_cong on the lifted IHs concludes directly.
    let let_cong_arm = format!(
        concat!(
            "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
            "(body : KExpr) (body' : KExpr) ",
            "(_hty : par_reduces_p0 env ty ty') (_hval : par_reduces_p0 env val val') ",
            "(_hbody : par_reduces_p0 env body body') ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(c : Nat) (a : Nat) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_p0.let_cong env (lift_at ty c a) (lift_at ty' c a) ",
            "(lift_at val c a) (lift_at val' c a) ",
            "(lift_at body (Nat.succ c) a) (lift_at body' (Nat.succ c) a) ",
            "(ihty c a liftclosed) (ihval c a liftclosed) (ihbody (Nat.succ c) a liftclosed))"
        ),
        ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
        ih_val = ih.replace("SUB'", "val'").replace("SUB", "val"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
    );
    // iota_0 arm: lift the gate iota_step (app f a) r0 and the fire iota_step (app f'
    // a') r via iota_lift_commutes. lift_at distributes over app definitionally, so
    // iota_lift_commutes env (app f a) r0 c a' liftclosed hgate : iota_step (app (lift
    // f)(lift a)) (lift r0). Reassemble via iota_0 on the lifted subterm IHs.
    let iota_arm = format!(
        concat!(
            "(fun (f : KExpr) (f' : KExpr) (a0 : KExpr) (a0' : KExpr) (r : KExpr) (r0 : KExpr) ",
            "(_hf : par_reduces_p0 env f f') (_ha : par_reduces_p0 env a0 a0') ",
            "(hgate : iota_step env (KExpr.app f a0) r0) (hfire : iota_step env (KExpr.app f' a0') r) ",
            "(ihf : {ih_f}) (iha : {ih_a}) ",
            "(c : Nat) (a : Nat) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_p0.iota_0 env (lift_at f c a) (lift_at f' c a) ",
            "(lift_at a0 c a) (lift_at a0' c a) (lift_at r c a) (lift_at r0 c a) ",
            "(ihf c a liftclosed) (iha c a liftclosed) ",
            "(iota_lift_commutes env (KExpr.app f a0) r0 c a liftclosed hgate) ",
            "(iota_lift_commutes env (KExpr.app f' a0') r c a liftclosed hfire))"
        ),
        ih_f = ih.replace("SUB'", "f'").replace("SUB", "f"),
        ih_a = ih.replace("SUB'", "a0'").replace("SUB", "a0"),
    );
    // proj arm: lift descends into the scrutinee; congruence via par_reduces_p0.proj.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
            "(_hsub : par_reduces_p0 env sub sub') (ihsub : {ih_sub}) ",
            "(c : Nat) (a : Nat) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_p0.proj env s i (lift_at sub c a) (lift_at sub' c a) ",
            "(ihsub c a liftclosed))"
        ),
        ih_sub = ih.replace("SUB'", "sub'").replace("SUB", "sub"),
    );
    format!(
        concat!(
            "fun (env : RecEnv) (v0 : KExpr) (v0' : KExpr) (c0 : Nat) (a0 : Nat) ",
            "(liftclosed0 : RecEnvLiftClosed env) (h0 : par_reduces_p0 env v0 v0') => ",
            "par_reduces_p0.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} ",
            "v0 v0' h0 c0 a0 liftclosed0"
        ),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = binder_arm("par_reduces_p0.lam"),
        pi_arm = binder_arm("par_reduces_p0.pi"),
        forall_arm = binder_arm("par_reduces_p0.forall_"),
        let_arm = let_arm,
        iota_arm = iota_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for `par0_subst` — `par_reduces_p0.rec` on the derivation. The
/// value `v` is held FIXED (body-congruence direction). The structural arms
/// distribute over `instantiate_at` definitionally (binder arms recurse at `succ`
/// depth); the beta/let arms transport the nested substitution via
/// `instantiate_nested_commutes_zero_subst`; the `iota_0` arm substitutes gate + fire
/// via `iota_subst_commutes`.
fn par0_subst_proof() -> String {
    // Motive over the derivation: universalize v, d; thread the closure predicates.
    let motive = concat!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_p0 env e e') => ",
        "forall (v : KExpr) (d : Nat), RecEnvClosed env -> RecEnvLiftClosed env -> ",
        "par_reduces_p0 env (instantiate_at e v d) (instantiate_at e' v d))"
    );
    let ih = concat!(
        "forall (v : KExpr) (d : Nat), RecEnvClosed env -> RecEnvLiftClosed env -> ",
        "par_reduces_p0 env (instantiate_at SUB v d) (instantiate_at SUB' v d)"
    );
    let refl_arm = concat!(
        "(fun (e : KExpr) (v : KExpr) (d : Nat) (_closed : RecEnvClosed env) (_liftclosed : RecEnvLiftClosed env) => ",
        "par_reduces_p0.refl env (instantiate_at e v d))"
    );
    let app_arm = format!(
        concat!(
            "(fun (f : KExpr) (f' : KExpr) (a0 : KExpr) (a0' : KExpr) ",
            "(_hf : par_reduces_p0 env f f') (_ha : par_reduces_p0 env a0 a0') ",
            "(ihf : {ih_f}) (iha : {ih_a}) (v : KExpr) (d : Nat) (closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_p0.app env (instantiate_at f v d) (instantiate_at f' v d) ",
            "(instantiate_at a0 v d) (instantiate_at a0' v d) ",
            "(ihf v d closed liftclosed) (iha v d closed liftclosed))"
        ),
        ih_f = ih.replace("SUB'", "f'").replace("SUB", "f"),
        ih_a = ih.replace("SUB'", "a0'").replace("SUB", "a0"),
    );
    // beta/let contraction transport: instantiate_at (instantiate_at bodyp argp 0) v d
    //   = instantiate_at (instantiate_at bodyp v (succ d)) (instantiate_at argp v d) 0
    // via instantiate_nested_commutes_zero_subst (the blueprint subst_subst).
    let contract = |lhs_head: &str, ctor_term: &str, bodyp: &str, argp: &str| -> String {
        let goal_lhs = format!("(instantiate_at (instantiate_at {bodyp} {argp} Nat.zero) v d)");
        let goal_rhs = format!(
            "(instantiate_at (instantiate_at {bodyp} v (Nat.succ d)) (instantiate_at {argp} v d) Nat.zero)"
        );
        let eq = format!("(instantiate_nested_commutes_zero_subst {bodyp} {argp} v d)");
        let p = format!("(fun (x : KExpr) => par_reduces_p0 env {lhs_head} x)");
        format!(
            "(Eq.substType KExpr {p} {goal_rhs} {goal_lhs} (Eq.symm KExpr {goal_lhs} {goal_rhs} {eq}) {ctor_term})"
        )
    };
    let beta_lhs_head = concat!(
        "(KExpr.app (KExpr.lam (instantiate_at A v d) (instantiate_at body v (Nat.succ d))) ",
        "(instantiate_at arg v d))"
    );
    let beta_ctor = concat!(
        "(par_reduces_p0.beta env (instantiate_at A v d) (instantiate_at A' v d) ",
        "(instantiate_at body v (Nat.succ d)) (instantiate_at body' v (Nat.succ d)) ",
        "(instantiate_at arg v d) (instantiate_at arg' v d) ",
        "(ihA v d closed liftclosed) (ihbody v (Nat.succ d) closed liftclosed) (iharg v d closed liftclosed))"
    );
    let beta_arm = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) ",
            "(arg : KExpr) (arg' : KExpr) ",
            "(_hA : par_reduces_p0 env A A') (_hbody : par_reduces_p0 env body body') ",
            "(_harg : par_reduces_p0 env arg arg') ",
            "(ihA : {ih_A}) (ihbody : {ih_body}) (iharg : {ih_arg}) ",
            "(v : KExpr) (d : Nat) (closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => {body})"
        ),
        ih_A = ih.replace("SUB'", "A'").replace("SUB", "A"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
        ih_arg = ih.replace("SUB'", "arg'").replace("SUB", "arg"),
        body = contract(beta_lhs_head, beta_ctor, "body'", "arg'"),
    );
    let binder_arm = |ctor: &str| -> String {
        format!(
            concat!(
                "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                "(_hty : par_reduces_p0 env ty ty') (_hbody : par_reduces_p0 env body body') ",
                "(ihty : {ih_ty}) (ihbody : {ih_body}) (v : KExpr) (d : Nat) (closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
                "{ctor} env (instantiate_at ty v d) (instantiate_at ty' v d) ",
                "(instantiate_at body v (Nat.succ d)) (instantiate_at body' v (Nat.succ d)) ",
                "(ihty v d closed liftclosed) (ihbody v (Nat.succ d) closed liftclosed))"
            ),
            ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
            ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
            ctor = ctor,
        )
    };
    // let_ (ZETA): instantiate_at (KExpr.let_ ty val body) v d = KExpr.let_ (inst ty)(inst val)
    // (inst body succ) (genuine ctor); ctor target nests, bridged by the shared contract.
    let let_lhs_head =
        "(KExpr.let_ (instantiate_at ty v d) (instantiate_at val v d) (instantiate_at body v (Nat.succ d)))";
    let let_ctor = concat!(
        "(par_reduces_p0.let_ env (instantiate_at ty v d) (instantiate_at ty' v d) ",
        "(instantiate_at val v d) (instantiate_at val' v d) ",
        "(instantiate_at body v (Nat.succ d)) (instantiate_at body' v (Nat.succ d)) ",
        "(ihty v d closed liftclosed) (ihval v d closed liftclosed) (ihbody v (Nat.succ d) closed liftclosed))"
    );
    let let_arm = format!(
        concat!(
            "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
            "(body : KExpr) (body' : KExpr) ",
            "(_hty : par_reduces_p0 env ty ty') (_hval : par_reduces_p0 env val val') ",
            "(_hbody : par_reduces_p0 env body body') ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(v : KExpr) (d : Nat) (closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => {body})"
        ),
        ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
        ih_val = ih.replace("SUB'", "val'").replace("SUB", "val"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
        body = contract(let_lhs_head, let_ctor, "body'", "val'"),
    );
    // let_cong (trailing CONGRUENCE): instantiate_at distributes over let_ definitionally,
    // so par_reduces_p0.let_cong on the substituted IHs concludes directly (value v FIXED).
    let let_cong_arm = format!(
        concat!(
            "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
            "(body : KExpr) (body' : KExpr) ",
            "(_hty : par_reduces_p0 env ty ty') (_hval : par_reduces_p0 env val val') ",
            "(_hbody : par_reduces_p0 env body body') ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(v : KExpr) (d : Nat) (closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_p0.let_cong env (instantiate_at ty v d) (instantiate_at ty' v d) ",
            "(instantiate_at val v d) (instantiate_at val' v d) ",
            "(instantiate_at body v (Nat.succ d)) (instantiate_at body' v (Nat.succ d)) ",
            "(ihty v d closed liftclosed) (ihval v d closed liftclosed) (ihbody v (Nat.succ d) closed liftclosed))"
        ),
        ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
        ih_val = ih.replace("SUB'", "val'").replace("SUB", "val"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
    );
    // iota_0 arm: substitute the gate iota_step (app f a) r0 and the fire iota_step
    // (app f' a') r via iota_subst_commutes (under RecEnvClosed). instantiate_at
    // distributes over app definitionally. Reassemble via iota_0 on the substituted IHs.
    let iota_arm = format!(
        concat!(
            "(fun (f : KExpr) (f' : KExpr) (a0 : KExpr) (a0' : KExpr) (r : KExpr) (r0 : KExpr) ",
            "(_hf : par_reduces_p0 env f f') (_ha : par_reduces_p0 env a0 a0') ",
            "(hgate : iota_step env (KExpr.app f a0) r0) (hfire : iota_step env (KExpr.app f' a0') r) ",
            "(ihf : {ih_f}) (iha : {ih_a}) ",
            "(v : KExpr) (d : Nat) (closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_p0.iota_0 env (instantiate_at f v d) (instantiate_at f' v d) ",
            "(instantiate_at a0 v d) (instantiate_at a0' v d) (instantiate_at r v d) (instantiate_at r0 v d) ",
            "(ihf v d closed liftclosed) (iha v d closed liftclosed) ",
            "(iota_subst_commutes env (KExpr.app f a0) r0 v d closed hgate) ",
            "(iota_subst_commutes env (KExpr.app f' a0') r v d closed hfire))"
        ),
        ih_f = ih.replace("SUB'", "f'").replace("SUB", "f"),
        ih_a = ih.replace("SUB'", "a0'").replace("SUB", "a0"),
    );
    // proj arm: subst descends into the scrutinee; congruence via par_reduces_p0.proj.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
            "(_hsub : par_reduces_p0 env sub sub') (ihsub : {ih_sub}) ",
            "(v : KExpr) (d : Nat) (closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_p0.proj env s i ",
            "(instantiate_at sub v d) (instantiate_at sub' v d) ",
            "(ihsub v d closed liftclosed))"
        ),
        ih_sub = ih.replace("SUB'", "sub'").replace("SUB", "sub"),
    );
    format!(
        concat!(
            "fun (env : RecEnv) (v0 : KExpr) (v0' : KExpr) (vv0 : KExpr) (d0 : Nat) ",
            "(closed0 : RecEnvClosed env) (liftclosed0 : RecEnvLiftClosed env) (h0 : par_reduces_p0 env v0 v0') => ",
            "par_reduces_p0.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} ",
            "v0 v0' h0 vv0 d0 closed0 liftclosed0"
        ),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = binder_arm("par_reduces_p0.lam"),
        pi_arm = binder_arm("par_reduces_p0.pi"),
        forall_arm = binder_arm("par_reduces_p0.forall_"),
        let_arm = let_arm,
        proj_arm = proj_arm,
        iota_arm = iota_arm,
        let_cong_arm = let_cong_arm,
    )
}

/// Closed proof term for `par_reduces_p0_lam_inv`. Mirror of
/// `par_reduces_p_lam_inv_proof` over `par_reduces_p0` (env threaded). Every arm is a
/// verbatim p→p0 port EXCEPT the iota arm: `par_reduces_p0.iota_0`'s source is a
/// LITERAL `app f a`, so the source-equation `app f a = lam ty body` is refuted
/// directly by `app_ne_lam` (no `lam_reduct_not_redex` — the literal-scrutinee design
/// removes the head-none reasoning the `par_reduces_p` version needed).
fn par_reduces_p0_lam_inv_proof() -> String {
    let motive = concat!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_p0 env e e') => ",
        "Eq KExpr e (KExpr.lam ty body) -> C e')"
    );

    // refl: reduct e; build C (lam ty body), transport to C e.
    let refl_arm = concat!(
        "(fun (e : KExpr) (eq : Eq KExpr e (KExpr.lam ty body)) => ",
        "Eq.substType KExpr C (KExpr.lam ty body) e ",
        "(Eq.symm KExpr e (KExpr.lam ty body) eq) ",
        "(klam ty body (par_reduces_p0.refl env ty) (par_reduces_p0.refl env body)))"
    );

    // beta: source app (lam A b0) arg — app /= lam.
    let beta_arm = concat!(
        "(fun (A : KExpr) (A' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(arg : KExpr) (arg' : KExpr) ",
        "(_hA : par_reduces_p0 env A A') (_hb0 : par_reduces_p0 env b0 b0') ",
        "(_harg : par_reduces_p0 env arg arg') ",
        "(_ihA : Eq KExpr A (KExpr.lam ty body) -> C A') ",
        "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
        "(_iharg : Eq KExpr arg (KExpr.lam ty body) -> C arg') ",
        "(eq : Eq KExpr (KExpr.app (KExpr.lam A b0) arg) (KExpr.lam ty body)) => ",
        "app_ne_lam (KExpr.lam A b0) arg ty body (C (instantiate b0' arg')) eq)"
    );

    // app: source app g b — app /= lam.
    let app_arm = concat!(
        "(fun (g : KExpr) (g' : KExpr) (b : KExpr) (b' : KExpr) ",
        "(_hg : par_reduces_p0 env g g') (_hb : par_reduces_p0 env b b') ",
        "(_ihg : Eq KExpr g (KExpr.lam ty body) -> C g') ",
        "(_ihb : Eq KExpr b (KExpr.lam ty body) -> C b') ",
        "(eq : Eq KExpr (KExpr.app g b) (KExpr.lam ty body)) => ",
        "app_ne_lam g b ty body (C (KExpr.app g' b')) eq)"
    );

    // lam: source lam t0 b0 — the matching congruence arm.
    let lam_arm = concat!(
        "(fun (t0 : KExpr) (t0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(ht : par_reduces_p0 env t0 t0') (hb : par_reduces_p0 env b0 b0') ",
        "(_iht : Eq KExpr t0 (KExpr.lam ty body) -> C t0') ",
        "(_ihb : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
        "(eq : Eq KExpr (KExpr.lam t0 b0) (KExpr.lam ty body)) => ",
        "klam t0' b0' ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p0 env x t0') t0 ty ",
        "(lam_inj_fst t0 b0 ty body eq) ht) ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p0 env x b0') b0 body ",
        "(lam_inj_snd t0 b0 ty body eq) hb))"
    );

    // pi: source pi dom b0 — pi /= lam.
    let pi_arm = concat!(
        "(fun (dom : KExpr) (dom' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(_hd : par_reduces_p0 env dom dom') (_hb0 : par_reduces_p0 env b0 b0') ",
        "(_ihd : Eq KExpr dom (KExpr.lam ty body) -> C dom') ",
        "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
        "(eq : Eq KExpr (KExpr.pi dom b0) (KExpr.lam ty body)) => ",
        "pi_ne_lam dom b0 ty body (C (KExpr.pi dom' b0')) eq)"
    );

    // forall_: source forall_ dom b0 = pi dom b0 (alias) — pi /= lam.
    let forall_arm = concat!(
        "(fun (dom : KExpr) (dom' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(_hd : par_reduces_p0 env dom dom') (_hb0 : par_reduces_p0 env b0 b0') ",
        "(_ihd : Eq KExpr dom (KExpr.lam ty body) -> C dom') ",
        "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
        "(eq : Eq KExpr (KExpr.forall_ dom b0) (KExpr.lam ty body)) => ",
        "pi_ne_lam dom b0 ty body (C (KExpr.forall_ dom' b0')) eq)"
    );

    // let_ (ZETA): source let_ t0 v b0 (a genuine let, NEVER a lam) — refute the
    // source-equation via the KExpr let/lam discriminator (formerly app_ne_lam under
    // the app(lam) alias, now dead).
    let let_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_p0 env t0 t0') (_hv : par_reduces_p0 env v v') ",
            "(_hb0 : par_reduces_p0 env b0 b0') ",
            "(_iht0 : Eq KExpr t0 (KExpr.lam ty body) -> C t0') ",
            "(_ihv : Eq KExpr v (KExpr.lam ty body) -> C v') ",
            "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.lam ty body)) => ",
            "Empty.rec (fun (_ : Empty) => C (instantiate b0' v')) ",
            "(Eq.substType KExpr {discr} (KExpr.let_ t0 v b0) (KExpr.lam ty body) eq Nat.zero))"
        ),
        discr = KEXPR_NOT_LAM_INLINE,
    );

    // let_cong (trailing CONGRUENCE): source let_ t0 v b0 (never a lam) — same refutation,
    // reduct KExpr.let_ t0' v' b0'.
    let let_cong_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_p0 env t0 t0') (_hv : par_reduces_p0 env v v') ",
            "(_hb0 : par_reduces_p0 env b0 b0') ",
            "(_iht0 : Eq KExpr t0 (KExpr.lam ty body) -> C t0') ",
            "(_ihv : Eq KExpr v (KExpr.lam ty body) -> C v') ",
            "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.lam ty body)) => ",
            "Empty.rec (fun (_ : Empty) => C (KExpr.let_ t0' v' b0')) ",
            "(Eq.substType KExpr {discr} (KExpr.let_ t0 v b0) (KExpr.lam ty body) eq Nat.zero))"
        ),
        discr = KEXPR_NOT_LAM_INLINE,
    );

    // iota_0: source LITERAL app f a — app /= lam. Discharged directly by app_ne_lam
    // (the iota_0 source is always an app, never a lam — no head-none machinery).
    let iota_arm = concat!(
        "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (r : KExpr) (r0 : KExpr) ",
        "(_hf : par_reduces_p0 env f f') (_ha : par_reduces_p0 env a a') ",
        "(_hgate : iota_step env (KExpr.app f a) r0) (_hfire : iota_step env (KExpr.app f' a') r) ",
        "(_ihf : Eq KExpr f (KExpr.lam ty body) -> C f') ",
        "(_iha : Eq KExpr a (KExpr.lam ty body) -> C a') ",
        "(eq : Eq KExpr (KExpr.app f a) (KExpr.lam ty body)) => ",
        "app_ne_lam f a ty body (C r) eq)"
    );

    // proj arm: source proj s i sub is proj-headed — proj /= lam via proj_ne_lam.
    let proj_arm = concat!(
        "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
        "(_hsub : par_reduces_p0 env sub sub') ",
        "(_ihsub : Eq KExpr sub (KExpr.lam ty body) -> C sub') ",
        "(eq : Eq KExpr (KExpr.proj s i sub) (KExpr.lam ty body)) => ",
        "proj_ne_lam s i sub ty body (C (KExpr.proj s i sub')) eq)"
    );

    format!(
        concat!(
            "fun (env : RecEnv) (ty : KExpr) (body : KExpr) (t : KExpr) (C : KExpr -> Type) ",
            "(h : par_reduces_p0 env (KExpr.lam ty body) t) ",
            "(klam : forall (ty' : KExpr) (body' : KExpr), ",
            "par_reduces_p0 env ty ty' -> par_reduces_p0 env body body' -> ",
            "C (KExpr.lam ty' body')) => ",
            "par_reduces_p0.rec env {motive} ",
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

/// Closed proof term for `dev0_refl` — the `cd_refl` analogue for `dev0` /
/// `par_reduces_p0`. Structural `KExpr.rec` with motive `par_reduces_p0 env e (dev0
/// env e)`. The non-app arms are verbatim p→p0 ports of `cd_refl`'s arms (cd → dev0).
/// The app arm replaces `cd`'s look-ahead some-branch with `dev0`'s LITERAL gate
/// convoy + a NESTED inner convoy that picks `iota_0` (developed redex fires) vs
/// `app` (reassembled) — both `iota_step`s are convoy witnesses, so there is NO redex
/// reconstruction and NO over-application wall.
fn dev0_refl_proof() -> String {
    let motive = "(fun (e : KExpr) => par_reduces_p0 env e (dev0 env e))";

    let sort_arm = "(fun (n : Level) => par_reduces_p0.refl env (KExpr.sort n))";
    let bvar_arm = "(fun (i : Nat) => par_reduces_p0.refl env (KExpr.bvar i))";
    let const_arm =
        "(fun (nm : Name) (us : ListType Level) => par_reduces_p0.refl env (KExpr.const nm us))";

    // lam/pi binder arm: dev0 env (HEAD ty b) = HEAD (dev0 ty)(dev0 b) (dev0_lam/dev0_pi).
    let binder_arm = |ctor: &str, head: &str, unfold: &str| -> String {
        format!(
            concat!(
                "(fun (ty : KExpr) (b : KExpr) ",
                "(ihty : par_reduces_p0 env ty (dev0 env ty)) (ihb : par_reduces_p0 env b (dev0 env b)) => ",
                "Eq.substType KExpr ",
                "(fun (x : KExpr) => par_reduces_p0 env ({head} ty b) x) ",
                "({head} (dev0 env ty) (dev0 env b)) (dev0 env ({head} ty b)) ",
                "(Eq.symm KExpr (dev0 env ({head} ty b)) ({head} (dev0 env ty) (dev0 env b)) ({unfold} env ty b)) ",
                "({ctor} env ty (dev0 env ty) b (dev0 env b) ihty ihb))"
            ),
            ctor = ctor,
            head = head,
            unfold = unfold,
        )
    };

    // ---- app arm ----
    let df = "(dev0 env f)";
    let da = "(dev0 env a)";
    let dflt = "(KExpr.app (dev0 env f) (dev0 env a))";
    // the LITERAL gate option and the DEVELOPED-redex option.
    let gate_opt = "(iota_reduct env (KExpr.app f a))";
    let dev_opt = "(iota_reduct env (KExpr.app (dev0 env f) (dev0 env a)))";

    // app congruence on the two IHs: par_reduces_p0 env (app f a)(app df da).
    let app_cong = "(par_reduces_p0.app env f (dev0 env f) a (dev0 env a) ihf iha)";

    // INNER convoy over o2 : iota_reduct env (app df da). The some arm fires iota_0; the
    // none arm reassembles via app_cong (opt_default none dflt = dflt = app df da).
    // r0 is the gate witness; eqn : gate_opt = some r0 is the gate iota_step.
    let inner_none = format!(
        "(fun (eqn2 : Eq (OptionType KExpr) {dev_opt} (OptionType.none KExpr)) => {app_cong})",
        dev_opt = dev_opt,
        app_cong = app_cong,
    );
    let inner_some = format!(
        concat!(
            "(fun (r : KExpr) (eqn2 : Eq (OptionType KExpr) {dev_opt} (OptionType.some KExpr r)) => ",
            "par_reduces_p0.iota_0 env f (dev0 env f) a (dev0 env a) r r0 ihf iha eqn eqn2)"
        ),
        dev_opt = dev_opt,
    );
    let inner_motive = format!(
        concat!(
            "(fun (o : OptionType KExpr) => Eq (OptionType KExpr) {dev_opt} o -> ",
            "par_reduces_p0 env (KExpr.app f a) (opt_default o {dflt}))"
        ),
        dev_opt = dev_opt,
        dflt = dflt,
    );
    // proof of par_reduces_p0 env (app f a) (opt_default dev_opt dflt).
    let on_inner = format!(
        concat!(
            "(OptionType.rec KExpr {inner_motive} {inner_none} {inner_some} {dev_opt} ",
            "(Eq.refl (OptionType KExpr) {dev_opt}))"
        ),
        inner_motive = inner_motive,
        inner_none = inner_none,
        inner_some = inner_some,
        dev_opt = dev_opt,
    );

    // OUTER convoy over o : iota_reduct env (app f a) (dev0's LITERAL gate). The none
    // arm reassembles via app_cong; the some arm (binds r0, eqn) runs the inner convoy.
    let outer_none = format!(
        "(fun (eqn : Eq (OptionType KExpr) {gate_opt} (OptionType.none KExpr)) => {app_cong})",
        gate_opt = gate_opt,
        app_cong = app_cong,
    );
    let outer_some = format!(
        concat!(
            "(fun (r0 : KExpr) (eqn : Eq (OptionType KExpr) {gate_opt} (OptionType.some KExpr r0)) => ",
            "{on_inner})"
        ),
        gate_opt = gate_opt,
        on_inner = on_inner,
    );
    // outer convoy motive over o : OptionType KExpr. The some arm yields opt_default
    // dev_opt dflt (the dev0 some-branch reduct); the none arm yields dflt.
    let outer_motive = format!(
        concat!(
            "(fun (o : OptionType KExpr) => Eq (OptionType KExpr) {gate_opt} o -> ",
            "par_reduces_p0 env (KExpr.app f a) ",
            "(OptionType.rec KExpr (fun (_ : OptionType KExpr) => KExpr) ",
            "{dflt} ",
            "(fun (_ : KExpr) => opt_default {dev_opt} {dflt}) ",
            "o))"
        ),
        gate_opt = gate_opt,
        dflt = dflt,
        dev_opt = dev_opt,
    );
    let on_gate = format!(
        concat!(
            "(OptionType.rec KExpr {outer_motive} {outer_none} {outer_some} {gate_opt} ",
            "(Eq.refl (OptionType KExpr) {gate_opt}))"
        ),
        outer_motive = outer_motive,
        outer_none = outer_none,
        outer_some = outer_some,
        gate_opt = gate_opt,
    );
    // eq_dev0 : dev0 env (app f a) = the false-branch body (the OptionType.rec on
    // gate_opt). dev0_app gives the Bool.rec form; hfalse rewrites kexpr_is_lam f ->
    // false, computing to the false arm. The false-arm body IS the outer-motive's o-slot
    // evaluated at o = gate_opt — matches on_gate's conclusion.
    let false_body = format!(
        concat!(
            "(OptionType.rec KExpr (fun (_ : OptionType KExpr) => KExpr) ",
            "{dflt} ",
            "(fun (_ : KExpr) => opt_default {dev_opt} {dflt}) ",
            "{gate_opt})"
        ),
        dflt = dflt,
        dev_opt = dev_opt,
        gate_opt = gate_opt,
    );
    let eq_dev0 = format!(
        concat!(
            "(Eq.subst Bool ",
            "(fun (bcond : Bool) => Eq KExpr (dev0 env (KExpr.app f a)) ",
            "(Bool.rec (fun (_ : Bool) => KExpr) ",
            "{false_body} ",
            "(instantiate (kexpr_lam_body {df}) {da}) bcond)) ",
            "(kexpr_is_lam f) Bool.false hfalse ",
            "(dev0_app env f a))"
        ),
        false_body = false_body,
        df = df,
        da = da,
    );
    let false_branch = format!(
        concat!(
            "(fun (hfalse : Eq Bool (kexpr_is_lam f) Bool.false) => ",
            "Eq.substType KExpr ",
            "(fun (x : KExpr) => par_reduces_p0 env (KExpr.app f a) x) ",
            "{false_body} (dev0 env (KExpr.app f a)) ",
            "(Eq.symm KExpr (dev0 env (KExpr.app f a)) {false_body} {eq_dev0}) ",
            "{on_gate})"
        ),
        false_body = false_body,
        eq_dev0 = eq_dev0,
        on_gate = on_gate,
    );

    // LAM branch (f = lam A b0). dev0 env (app (lam A b0) a) = instantiate (dev0 b0)(dev0 a)
    // (dev0_app_lam). Recover A ⇒_p0 dev0 A, b0 ⇒_p0 dev0 b0 from ihf via dev0_lam +
    // par_reduces_p0_lam_inv, then par_reduces_p0.beta. Verbatim shape of cd_refl's lam branch.
    let ihf_lam = concat!(
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p0 env (KExpr.lam A b0) x) ",
        "(dev0 env (KExpr.lam A b0)) (KExpr.lam (dev0 env A) (dev0 env b0)) ",
        "(dev0_lam env A b0) ",
        "(Eq.substType KExpr (fun (g : KExpr) => par_reduces_p0 env g (dev0 env g)) ",
        "f (KExpr.lam A b0) hf ihf))"
    );
    let beta_goal =
        "(par_reduces_p0 env (KExpr.app (KExpr.lam A b0) a) (instantiate (dev0 env b0) (dev0 env a)))";
    let klam_inv = concat!(
        "(fun (ty2 : KExpr) (body2 : KExpr) ",
        "(hty2 : par_reduces_p0 env A ty2) (hbody2 : par_reduces_p0 env b0 body2) ",
        "(zeq : Eq KExpr (KExpr.lam ty2 body2) (KExpr.lam (dev0 env A) (dev0 env b0))) => ",
        "par_reduces_p0.beta env A (dev0 env A) b0 (dev0 env b0) a (dev0 env a) ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p0 env A x) ty2 (dev0 env A) ",
        "(lam_inj_fst ty2 body2 (dev0 env A) (dev0 env b0) zeq) hty2) ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p0 env b0 x) body2 (dev0 env b0) ",
        "(lam_inj_snd ty2 body2 (dev0 env A) (dev0 env b0) zeq) hbody2) ",
        "iha)"
    );
    let p_lam = format!(
        concat!(
            "(Eq.substType KExpr ",
            "(fun (x : KExpr) => par_reduces_p0 env (KExpr.app (KExpr.lam A b0) a) x) ",
            "(instantiate (dev0 env b0) (dev0 env a)) (dev0 env (KExpr.app (KExpr.lam A b0) a)) ",
            "(Eq.symm KExpr (dev0 env (KExpr.app (KExpr.lam A b0) a)) (instantiate (dev0 env b0) (dev0 env a)) ",
            "(dev0_app_lam env A b0 a)) ",
            "(par_reduces_p0_lam_inv env A b0 (KExpr.lam (dev0 env A) (dev0 env b0)) ",
            "(fun (z : KExpr) => Eq KExpr z (KExpr.lam (dev0 env A) (dev0 env b0)) -> {beta_goal}) ",
            "{ihf_lam} {klam_inv} ",
            "(Eq.refl KExpr (KExpr.lam (dev0 env A) (dev0 env b0)))))"
        ),
        beta_goal = beta_goal,
        ihf_lam = ihf_lam,
        klam_inv = klam_inv,
    );
    let lam_branch = format!(
        concat!(
            "(fun (A : KExpr) (b0 : KExpr) (hf : Eq KExpr f (KExpr.lam A b0)) => ",
            "Eq.substType KExpr ",
            "(fun (g : KExpr) => par_reduces_p0 env (KExpr.app g a) (dev0 env (KExpr.app g a))) ",
            "(KExpr.lam A b0) f ",
            "(Eq.symm KExpr f (KExpr.lam A b0) hf) ",
            "{p_lam})"
        ),
        p_lam = p_lam,
    );

    let app_arm = format!(
        concat!(
            "(fun (f : KExpr) (a : KExpr) ",
            "(ihf : par_reduces_p0 env f (dev0 env f)) (iha : par_reduces_p0 env a (dev0 env a)) => ",
            "kexpr_lam_cases f (par_reduces_p0 env (KExpr.app f a) (dev0 env (KExpr.app f a))) ",
            "{lam_branch} {false_branch})"
        ),
        lam_branch = lam_branch,
        false_branch = false_branch,
    );

    // let_ arm (KExpr's genuine 7th ctor): dev0 fires the top zeta (mirroring the beta
    // branch, which is a bare instantiate with no post-iota). dev0 env (let_ ty val body) =
    // instantiate (dev0 body)(dev0 val) (dev0_let), delivered by par_reduces_p0.let_ (zeta).
    let let_arm = concat!(
        "(fun (ty : KExpr) (val : KExpr) (body : KExpr) ",
        "(ihty : par_reduces_p0 env ty (dev0 env ty)) ",
        "(ihval : par_reduces_p0 env val (dev0 env val)) ",
        "(ihbody : par_reduces_p0 env body (dev0 env body)) => ",
        "Eq.substType KExpr ",
        "(fun (x : KExpr) => par_reduces_p0 env (KExpr.let_ ty val body) x) ",
        "(instantiate (dev0 env body) (dev0 env val)) (dev0 env (KExpr.let_ ty val body)) ",
        "(Eq.symm KExpr (dev0 env (KExpr.let_ ty val body)) (instantiate (dev0 env body) (dev0 env val)) ",
        "(dev0_let env ty val body)) ",
        "(par_reduces_p0.let_ env ty (dev0 env ty) val (dev0 env val) body (dev0 env body) ihty ihval ihbody))"
    );

    // proj arm: dev0 descends into the scrutinee (dev0 env (proj s i sub) = proj s i
    // (dev0 env sub) by defeq); congruence via par_reduces_p0.proj on the IH.
    let proj_arm = concat!(
        "(fun (s : Name) (i : Nat) (sub : KExpr) ",
        "(ihsub : par_reduces_p0 env sub (dev0 env sub)) => ",
        "par_reduces_p0.proj env s i sub (dev0 env sub) ihsub)"
    );

    // lit arm: dev0 env (lit v) = lit v (defeq); reflexive par-step.
    let lit_arm = "(fun (v : Nat) => par_reduces_p0.refl env (KExpr.lit v))";

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
        lam_arm = binder_arm("par_reduces_p0.lam", "KExpr.lam", "dev0_lam"),
        pi_arm = binder_arm("par_reduces_p0.pi", "KExpr.pi", "dev0_pi"),
        const_arm = const_arm,
        let_arm = let_arm,
        proj_arm = proj_arm,
        lit_arm = lit_arm,
    )
}

/// Closed proof term for `par_subst_refl_p0_full` — verbatim p→p0 port of
/// `par_subst_refl_p_full_proof` (KExpr.rec on the FIXED body e with the double-Nat.rec
/// bvar convoy). The i=d leaf lifts the value reduction by the binder depth via
/// `par0_lift` (the p0 analogue of `par_lift_p_full`); all eq-algebra helpers are
/// relation-agnostic and shared verbatim.
fn par_subst_refl_p0_full_proof() -> String {
    let motive = concat!(
        "(fun (e : KExpr) => forall (v : KExpr) (v' : KExpr) (d : Nat), ",
        "RecEnvLiftClosed env -> par_reduces_p0 env v v' -> ",
        "par_reduces_p0 env (instantiate_at e v d) (instantiate_at e v' d))"
    );
    let ih = concat!(
        "forall (v : KExpr) (v' : KExpr) (d : Nat), RecEnvLiftClosed env -> ",
        "par_reduces_p0 env v v' -> ",
        "par_reduces_p0 env (instantiate_at SUB v d) (instantiate_at SUB v' d)"
    );

    let goal_l = "(instantiate_at (KExpr.bvar i) v d)";
    let goal_r = "(instantiate_at (KExpr.bvar i) v' d)";

    let transport = |xl: &str, xr: &str, eql: &str, eqr: &str, t: &str| -> String {
        let inner = format!(
            concat!(
                "(Eq.substType KExpr (fun (y : KExpr) => par_reduces_p0 env y {xr}) ",
                "{xl} {goal_l} ",
                "(Eq.symm KExpr {goal_l} {xl} {eql}) {t})"
            ),
            xr = xr,
            xl = xl,
            goal_l = goal_l,
            eql = eql,
            t = t,
        );
        format!(
            concat!(
                "(Eq.substType KExpr ",
                "(fun (y : KExpr) => par_reduces_p0 env {goal_l} y) ",
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

    // LEAF: i = d. The substituted value is lifted by the binder depth d: par0_lift v v'
    // 0 d, in ONE par0-step.
    let leaf_eq = {
        let xl = "(lift_at v Nat.zero d)";
        let xr = "(lift_at v' Nat.zero d)";
        let eql = "(instantiate_at_bvar_eq_from_zero_witnesses i d v h_di0 h_id)";
        let eqr = "(instantiate_at_bvar_eq_from_zero_witnesses i d v' h_di0 h_id)";
        let t = "(par0_lift env v v' Nat.zero d liftclosed h)";
        transport(xl, xr, eql, eqr, t)
    };

    // LEAF: i < d. Both = bvar i.
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
        let t = "(par_reduces_p0.refl env (KExpr.bvar i))";
        transport(xl, xr, &eql, &eqr, t)
    };

    // LEAF: i > d. Both = bvar (i-1).
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
        let t = "(par_reduces_p0.refl env (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))))";
        transport(xl, xr, &eql, &eqr, t)
    };

    let bvar_arm = format!(
        concat!(
            "(fun (i : Nat) (v : KExpr) (v' : KExpr) (d : Nat) ",
            "(liftclosed : RecEnvLiftClosed env) (h : par_reduces_p0 env v v') => ",
            "Nat.rec ",
            "(fun (g : Nat) => Eq Nat (Nat.sub i d) g -> ",
            "par_reduces_p0 env {goal_l} {goal_r}) ",
            "(fun (h_id : Eq Nat (Nat.sub i d) Nat.zero) => ",
            "Nat.rec ",
            "(fun (g2 : Nat) => Eq Nat (Nat.sub d i) g2 -> ",
            "par_reduces_p0 env {goal_l} {goal_r}) ",
            "(fun (h_di0 : Eq Nat (Nat.sub d i) Nat.zero) => {leaf_eq}) ",
            "(fun (k2 : Nat) ",
            "(_ : Eq Nat (Nat.sub d i) k2 -> par_reduces_p0 env {goal_l} {goal_r}) ",
            "(h_di : Eq Nat (Nat.sub d i) (Nat.succ k2)) => {leaf_below}) ",
            "(Nat.sub d i) (Eq.refl Nat (Nat.sub d i))) ",
            "(fun (k4 : Nat) ",
            "(_ : Eq Nat (Nat.sub i d) k4 -> par_reduces_p0 env {goal_l} {goal_r}) ",
            "(h_id : Eq Nat (Nat.sub i d) (Nat.succ k4)) => {leaf_above}) ",
            "(Nat.sub i d) (Eq.refl Nat (Nat.sub i d)))"
        ),
        goal_l = goal_l,
        goal_r = goal_r,
        leaf_eq = leaf_eq,
        leaf_below = leaf_below,
        leaf_above = leaf_above,
    );

    let sort_arm = concat!(
        "(fun (sv : Level) (v : KExpr) (v' : KExpr) (d : Nat) ",
        "(_lc : RecEnvLiftClosed env) (_h : par_reduces_p0 env v v') => ",
        "par_reduces_p0.refl env (KExpr.sort sv))"
    );
    let const_arm = concat!(
        "(fun (nm : Name) (us : ListType Level) (v : KExpr) (v' : KExpr) (d : Nat) ",
        "(_lc : RecEnvLiftClosed env) (_h : par_reduces_p0 env v v') => ",
        "par_reduces_p0.refl env (KExpr.const nm us))"
    );

    let app_arm = format!(
        concat!(
            "(fun (f : KExpr) (a0 : KExpr) ",
            "(ihf : {ih_f}) (iha : {ih_a}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (lc : RecEnvLiftClosed env) (h : par_reduces_p0 env v v') => ",
            "par_reduces_p0.app env ",
            "(instantiate_at f v d) (instantiate_at f v' d) ",
            "(instantiate_at a0 v d) (instantiate_at a0 v' d) ",
            "(ihf v v' d lc h) (iha v v' d lc h))"
        ),
        ih_f = ih.replace("SUB", "f"),
        ih_a = ih.replace("SUB", "a0"),
    );

    let binder_arm = |star_cong: &str| -> String {
        format!(
            concat!(
                "(fun (ty : KExpr) (body : KExpr) ",
                "(ihty : {ih_ty}) (ihbody : {ih_body}) ",
                "(v : KExpr) (v' : KExpr) (d : Nat) (lc : RecEnvLiftClosed env) (h : par_reduces_p0 env v v') => ",
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

    // let_ arm (KExpr's genuine 7th ctor): three-subterm value-congruence.
    // instantiate_at (KExpr.let_ ty val body) v d = KExpr.let_ (inst ty)(inst val)(inst body
    // succ) definitionally, so par_reduces_p0.let_cong on the fixed-body IHs concludes.
    let let_arm = format!(
        concat!(
            "(fun (ty : KExpr) (val : KExpr) (body : KExpr) ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (lc : RecEnvLiftClosed env) (h : par_reduces_p0 env v v') => ",
            "par_reduces_p0.let_cong env ",
            "(instantiate_at ty v d) (instantiate_at ty v' d) ",
            "(instantiate_at val v d) (instantiate_at val v' d) ",
            "(instantiate_at body v (Nat.succ d)) (instantiate_at body v' (Nat.succ d)) ",
            "(ihty v v' d lc h) (ihval v v' d lc h) (ihbody v v' (Nat.succ d) lc h))"
        ),
        ih_ty = ih.replace("SUB", "ty"),
        ih_val = ih.replace("SUB", "val"),
        ih_body = ih.replace("SUB", "body"),
    );

    // proj arm: subst descends into the scrutinee; congruence via par_reduces_p0.proj.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (ihsub : {ih_sub}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (lc : RecEnvLiftClosed env) (h : par_reduces_p0 env v v') => ",
            "par_reduces_p0.proj env s i ",
            "(instantiate_at sub v d) (instantiate_at sub v' d) ",
            "(ihsub v v' d lc h))"
        ),
        ih_sub = ih.replace("SUB", "sub"),
    );

    // lit arm: a numeral is closed, so instantiate_at (lit n) v d = lit n; refl.
    let lit_arm = concat!(
        "(fun (litv : Nat) (v : KExpr) (v' : KExpr) (d : Nat) ",
        "(_lc : RecEnvLiftClosed env) (_h : par_reduces_p0 env v v') => ",
        "par_reduces_p0.refl env (KExpr.lit litv))"
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
        lam_arm = binder_arm("par_reduces_p0.lam"),
        pi_arm = binder_arm("par_reduces_p0.pi"),
        const_arm = const_arm,
        let_arm = let_arm,
        proj_arm = proj_arm,
        lit_arm = lit_arm,
    )
}

/// Closed proof term for `par_subst_p0` — the FULL two-sided single-step substitution
/// lemma for `par_reduces_p0`. Verbatim p→p0 port of `par_subst_p_proof` (rec on the
/// derivation with a depth-generalized motive threading `v ⇒_p0 v'`) with the
/// iota_0 arm: the two IHs give the substituted subterm reductions, and
/// `iota_subst_commutes` lifts the gate (under v) and the fire (under v') so iota_0
/// assembles in ONE par0-step.
fn par_subst_p0_proof() -> String {
    let motive = concat!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_p0 env e e') => ",
        "forall (v : KExpr) (v' : KExpr) (d : Nat), par_reduces_p0 env v v' -> ",
        "RecEnvClosed env -> RecEnvLiftClosed env -> ",
        "par_reduces_p0 env (instantiate_at e v d) (instantiate_at e' v' d))"
    );
    let ih = concat!(
        "forall (v : KExpr) (v' : KExpr) (d : Nat), par_reduces_p0 env v v' -> ",
        "RecEnvClosed env -> RecEnvLiftClosed env -> ",
        "par_reduces_p0 env (instantiate_at SUB v d) (instantiate_at SUB' v' d)"
    );

    let refl_arm = concat!(
        "(fun (e : KExpr) (v : KExpr) (v' : KExpr) (d : Nat) ",
        "(h : par_reduces_p0 env v v') (_closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
        "par_subst_refl_p0_full env e v v' d liftclosed h)"
    );

    let app_arm = format!(
        concat!(
            "(fun (f : KExpr) (f' : KExpr) (a0 : KExpr) (a0' : KExpr) ",
            "(_hf : par_reduces_p0 env f f') (_ha : par_reduces_p0 env a0 a0') ",
            "(ihf : {ih_f}) (iha : {ih_a}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_p0 env v v') ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_p0.app env ",
            "(instantiate_at f v d) (instantiate_at f' v' d) ",
            "(instantiate_at a0 v d) (instantiate_at a0' v' d) ",
            "(ihf v v' d h closed liftclosed) (iha v v' d h closed liftclosed))"
        ),
        ih_f = ih.replace("SUB'", "f'").replace("SUB", "f"),
        ih_a = ih.replace("SUB'", "a0'").replace("SUB", "a0"),
    );

    let binder_arm = |ctor: &str| -> String {
        format!(
            concat!(
                "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                "(_hty : par_reduces_p0 env ty ty') (_hbody : par_reduces_p0 env body body') ",
                "(ihty : {ih_ty}) (ihbody : {ih_body}) ",
                "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_p0 env v v') ",
                "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
                "{ctor} env ",
                "(instantiate_at ty v d) (instantiate_at ty' v' d) ",
                "(instantiate_at body v (Nat.succ d)) (instantiate_at body' v' (Nat.succ d)) ",
                "(ihty v v' d h closed liftclosed) (ihbody v v' (Nat.succ d) h closed liftclosed))"
            ),
            ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
            ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
            ctor = ctor,
        )
    };

    // beta/let_ contraction transport (single-step, value reduces to v').
    let contract = |lhs_head: &str, ctor_term: &str, bodyp: &str, argp: &str| -> String {
        let goal_rhs = format!(
            "(instantiate_at (instantiate_at {bodyp} {argp} Nat.zero) v' d)",
            bodyp = bodyp,
            argp = argp,
        );
        let ctor_rhs = format!(
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
                "(fun (x : KExpr) => par_reduces_p0 env {lhs_head} x) ",
                "{ctor_rhs} {goal_rhs} ",
                "(Eq.symm KExpr {goal_rhs} {ctor_rhs} {eq}) ",
                "{ctor_term})"
            ),
            lhs_head = lhs_head,
            ctor_rhs = ctor_rhs,
            goal_rhs = goal_rhs,
            eq = eq,
            ctor_term = ctor_term,
        )
    };

    let beta_lhs_head = concat!(
        "(KExpr.app ",
        "(KExpr.lam (instantiate_at A v d) (instantiate_at body v (Nat.succ d))) ",
        "(instantiate_at arg v d))"
    );
    let beta_ctor = concat!(
        "(par_reduces_p0.beta env ",
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
            "(_hA : par_reduces_p0 env A A') (_hbody : par_reduces_p0 env body body') ",
            "(_harg : par_reduces_p0 env arg arg') ",
            "(ihA : {ih_A}) (ihbody : {ih_body}) (iharg : {ih_arg}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_p0 env v v') ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => {body})"
        ),
        ih_A = ih.replace("SUB'", "A'").replace("SUB", "A"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
        ih_arg = ih.replace("SUB'", "arg'").replace("SUB", "arg"),
        body = contract(beta_lhs_head, beta_ctor, "body'", "arg'"),
    );

    // let_ (ZETA): instantiate_at (KExpr.let_ ty val body) v d = KExpr.let_ (inst ty)(inst val)
    // (inst body succ) (genuine ctor); ctor target nests, bridged by the shared contract.
    let let_lhs_head =
        "(KExpr.let_ (instantiate_at ty v d) (instantiate_at val v d) (instantiate_at body v (Nat.succ d)))";
    let let_ctor = concat!(
        "(par_reduces_p0.let_ env ",
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
            "(_hty : par_reduces_p0 env ty ty') (_hval : par_reduces_p0 env val val') ",
            "(_hbody : par_reduces_p0 env body body') ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_p0 env v v') ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => {body})"
        ),
        ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
        ih_val = ih.replace("SUB'", "val'").replace("SUB", "val"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
        body = contract(let_lhs_head, let_ctor, "body'", "val'"),
    );
    // let_cong (trailing CONGRUENCE): instantiate_at distributes over let_ definitionally,
    // so par_reduces_p0.let_cong on the two-sided-substituted IHs concludes directly.
    let let_cong_arm = format!(
        concat!(
            "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
            "(body : KExpr) (body' : KExpr) ",
            "(_hty : par_reduces_p0 env ty ty') (_hval : par_reduces_p0 env val val') ",
            "(_hbody : par_reduces_p0 env body body') ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_p0 env v v') ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_p0.let_cong env ",
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

    // iota_0 arm: source LITERAL app f a. The two IHs give inst f v d ⇒ inst f' v' d and
    // inst a v d ⇒ inst a' v' d; iota_subst_commutes lifts the GATE (under v) to
    // iota_step (inst (app f a) v d)(inst r0 v d) = iota_step (app (inst f v d)(inst a v
    // d))(inst r0 v d), and the FIRE (under v') to iota_step (app (inst f' v' d)(inst a'
    // v' d))(inst r v' d); iota_0 assembles. instantiate_at distributes over app
    // definitionally, so no rewrite is needed on the app spines.
    let iota_arm = format!(
        concat!(
            "(fun (f : KExpr) (f' : KExpr) (a0 : KExpr) (a0' : KExpr) (r : KExpr) (r0 : KExpr) ",
            "(_hf : par_reduces_p0 env f f') (_ha : par_reduces_p0 env a0 a0') ",
            "(hgate : iota_step env (KExpr.app f a0) r0) (hfire : iota_step env (KExpr.app f' a0') r) ",
            "(ihf : {ih_f}) (iha : {ih_a}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_p0 env v v') ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_p0.iota_0 env ",
            "(instantiate_at f v d) (instantiate_at f' v' d) ",
            "(instantiate_at a0 v d) (instantiate_at a0' v' d) ",
            "(instantiate_at r v' d) (instantiate_at r0 v d) ",
            "(ihf v v' d h closed liftclosed) (iha v v' d h closed liftclosed) ",
            "(iota_subst_commutes env (KExpr.app f a0) r0 v d closed hgate) ",
            "(iota_subst_commutes env (KExpr.app f' a0') r v' d closed hfire))"
        ),
        ih_f = ih.replace("SUB'", "f'").replace("SUB", "f"),
        ih_a = ih.replace("SUB'", "a0'").replace("SUB", "a0"),
    );

    // proj arm: subst descends into the scrutinee; congruence via par_reduces_p0.proj.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
            "(_hsub : par_reduces_p0 env sub sub') (ihsub : {ih_sub}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_p0 env v v') ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_p0.proj env s i ",
            "(instantiate_at sub v d) (instantiate_at sub' v' d) ",
            "(ihsub v v' d h closed liftclosed))"
        ),
        ih_sub = ih.replace("SUB'", "sub'").replace("SUB", "sub"),
    );

    format!(
        concat!(
            "fun (env : RecEnv) (e0 : KExpr) (e0' : KExpr) (v0 : KExpr) (v0' : KExpr) (d0 : Nat) ",
            "(h_ee : par_reduces_p0 env e0 e0') (h_vv : par_reduces_p0 env v0 v0') ",
            "(closed0 : RecEnvClosed env) (liftclosed0 : RecEnvLiftClosed env) => ",
            "par_reduces_p0.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} ",
            "e0 e0' h_ee v0 v0' d0 h_vv closed0 liftclosed0"
        ),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = binder_arm("par_reduces_p0.lam"),
        pi_arm = binder_arm("par_reduces_p0.pi"),
        forall_arm = binder_arm("par_reduces_p0.forall_"),
        let_arm = let_arm,
        iota_arm = iota_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// `major_idx(meta)` — the recursor's iota boundary (verbatim from `iota_reduct`).
fn p0_redex_major_idx() -> String {
    "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) \
     (recmeta_num_minors meta)) (recmeta_num_indices meta))"
        .to_string()
}

/// The `(app f' a')`-side iota reduct `reduct_m` (the `a'`-side reduct that
/// `par_reduces_p_app_redex` delivers; verbatim from `reduct_cong_spine_reducts().1`).
fn p0_redex_reduct_m() -> String {
    let major_idx = p0_redex_major_idx();
    let prefix_n = "(Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) \
         (recmeta_num_minors meta))";
    let nf = "(recrule_num_fields rule)";
    let p_rhs = "(recrule_rhs rule)";
    let kargs_fap = "(kapp_args (KExpr.app f' a'))";
    format!(
        "(apply_spine (list_drop (Nat.succ {major_idx}) {kargs_fap}) \
         (apply_spine (list_drop (Nat.sub (list_length (kapp_args a')) {nf}) (kapp_args a')) \
         (apply_spine (list_take {prefix_n} {kargs_fap}) {p_rhs})))"
    )
}

/// The `(app f a)`-side reduct slot `reduct_app` the boundary inverter's `h5r` carries
/// (verbatim from the inverter's `reduct_app`, over the generic `major`).
fn boundary_reduct_app() -> String {
    let major_idx = p0_redex_major_idx();
    let prefix_n = "(Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) \
         (recmeta_num_minors meta))";
    let nf = "(recrule_num_fields rule)";
    let p_rhs = "(recrule_rhs rule)";
    let kargs_app = "(kapp_args (KExpr.app f a))";
    format!(
        "(apply_spine (list_drop (Nat.succ {major_idx}) {kargs_app}) \
         (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) {nf}) (kapp_args major)) \
         (apply_spine (list_take {prefix_n} {kargs_app}) {p_rhs})))"
    )
}

/// Type of `par_reduces_p0_redex_preserved_boundary` — the boundary-case redex-
/// preservation gate. The boundary guard `iota_reduct env f = none` makes the inversion
/// admissible; the result is a CPS existence `iota_reduct env (app f' a') = some rg`
/// (definitionally an `iota_step env (app f' a') rg`).
fn par_reduces_p0_redex_preserved_boundary_type() -> String {
    "forall (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (r0 : KExpr), \
     RecEnvCtorNoRecMeta env -> \
     Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr) -> \
     iota_step env (KExpr.app f a) r0 -> \
     par_reduces_p0 env f f' -> par_reduces_p0 env a a' -> \
     forall (C : Type), \
     (forall (rg : KExpr), \
      Eq (OptionType KExpr) (iota_reduct env (KExpr.app f' a')) (OptionType.some KExpr rg) -> C) -> C"
        .to_string()
}

/// Closed proof term for `par_reduces_p0_redex_preserved_boundary`.
///
/// `iota_step env (app f a) r0` is DEFINITIONALLY `iota_reduct env (app f a) = some r0`,
/// so the gate feeds `iota_reduct_app_minimal_boundary_idx_type` directly as its `hsome`.
/// The boundary inverter (Type-continuation, admissible under `hnone : iota_reduct env f
/// = none`) recovers recname/meta/major/cname/rule + h1/h2/h3/h4/h5/h5r + `major = a` +
/// `major_idx = len(kapp_args f)`. We bridge the two par0-steps to `par_reduces_p`
/// (`par_reduces_p0_subsumes_par_p`) and feed `par_reduces_p_app_redex`, which rebuilds
/// `iota_reduct env (app f' a') = some reduct_m`. The continuation `k` is then called
/// with `reduct_m` and that equation.
fn par_reduces_p0_redex_preserved_boundary_proof() -> String {
    let major_idx = p0_redex_major_idx();
    let reduct_m = p0_redex_reduct_m();
    let len_f = "(list_length (kapp_args f))";
    let kargs_app = "(kapp_args (KExpr.app f a))";

    // The bridged par_reduces_p steps.
    let hf_p = "(par_reduces_p0_subsumes_par_p env f f' hf)";
    let ha_p = "(par_reduces_p0_subsumes_par_p env a a' ha)";

    // par_reduces_p_app_redex reconstruction: iota_reduct env (app f' a') = some reduct_m.
    let recon = format!(
        "(par_reduces_p_app_redex env f f' a a' recname meta major cname rule \
         disjoint h1 h2 h4 h5 hbnd hidx {hf_p} {ha_p})"
    );

    // The boundary inverter's continuation: recover the witnesses, build recon, call k.
    let kont = format!(
        "(fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
         (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname)) \
         (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
         (h3 : Eq (OptionType KExpr) (list_head (list_drop {major_idx} {kargs_app})) (OptionType.some KExpr major)) \
         (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
         (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
         (h5r : Eq (OptionType KExpr) (OptionType.some KExpr {reduct_app}) (OptionType.some KExpr r0)) \
         (hbnd : Eq KExpr major a) \
         (hidx : Eq Nat {major_idx} {len_f}) => \
         k {reduct_m} {recon})",
        reduct_app = boundary_reduct_app(),
    );

    format!(
        "fun (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (r0 : KExpr) \
         (disjoint : RecEnvCtorNoRecMeta env) \
         (hfn : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)) \
         (hgate : iota_step env (KExpr.app f a) r0) \
         (hf : par_reduces_p0 env f f') (ha : par_reduces_p0 env a a') \
         (C : Type) \
         (k : forall (rg : KExpr), \
              Eq (OptionType KExpr) (iota_reduct env (KExpr.app f' a')) (OptionType.some KExpr rg) -> C) => \
         iota_reduct_app_minimal_boundary_idx_type env f a r0 hgate hfn C {kont}",
        kont = kont,
    )
}
