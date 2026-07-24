// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment H++ (#2859 computational-iota/delta track, DELTA INCREMENT Stage 4,
//! the HINDLEY-ROSEN assembly): the δ-SUBSTITUTION TOWER — the congruence lemmas
//! that lift the directed δ commutation keystones (`delta_subst_commutes` /
//! `delta_lift_commutes`, `delta_subst.rs`) over the single-position δ congruence
//! relation `delta_cong` and its closure `delta_cong_star`.
//!
//! This is brick 1 of the single-step strong commutation `SC` (= `par_delta_sc`)
//! build (the sole remaining obligation that makes the 3-way β+ι+δ Church-Rosser
//! `par_reduces_cd_star_diamond` unconditional). Ported from the VERIFIED blueprint
//! `scratch/confluence-proof/HindleyRosen_delta_VERIFIED.lean`:
//!   - `delta_lift_cong`      <- blueprint `delta_lift_cong`     (delta commutes with `lift_at`)
//!   - `delta_subst_cong`     <- blueprint `delta_subst_cong`    (delta commutes with `instantiate_at`)
//!   - `delta_substStar_body` <- blueprint `delta_substStar_body`(delta* in the body lifted to subst)
//!
//! Every piece is a structural induction on `delta_cong` / `delta_cong_star`. The
//! `here` arm fires the directed keystone (`delta_subst_commutes` /
//! `delta_lift_commutes`, both of which carry the faithful closure interface
//! `DefEnvClosed` / `DefEnvLiftClosed` as a HYPOTHESIS — the kernel's definition
//! values are closed); the nine congruence arms (`app_f`/`app_a`, `lam_t`/`lam_b`,
//! `pi_d`/`pi_b`, and the trailing `let_t`/`let_v`/`let_b` over the genuine
//! `KExpr.let_` node — let promotion, task #28) recurse, pushing `instantiate_at`
//! / `lift_at` through the KExpr constructor by definitional unfolding (binder
//! arms — lam/pi body and the let body — recurse at `succ depth` / `succ cutoff`).
//! The closure carriers `DefEnvClosed (red_def env)` / `DefEnvLiftClosed (red_def
//! env)` are bound hypotheses, NOT registered axioms.
//!
//! ALSO HOME (let promotion, task #28) to the ζ-redex SC join builders consumed by
//! `par_delta_sc` (`par_reduces_iota_delta.rs`): the `sc_let_join_{ty,val,body}`
//! witness builders (the ζ-redex mirrors of `sc_beta_join_{type,body,arg}`). The
//! δ-at-let case-splitter `delta_cong_let_inv` itself lives with its app/lam/pi
//! siblings in `par_reduces_d_diamond.rs`.
//!
//! Runs AFTER `add_par_reduces_d` (so `delta_cong` / `delta_cong_star` / the star
//! congruences are in scope) and AFTER `add_delta_subst` (so `delta_subst_commutes`
//! / `delta_lift_commutes` are in scope). Part of #2859 (Increment H++, delta
//! increment Stage 4 — Hindley-Rosen assembly).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_par_reduces_delta_sc(&mut self) -> Result<(), SpecError> {
        self.add_delta_lift_cong()?;
        self.add_delta_subst_cong()?;
        self.add_delta_subststar_body()?;
        self.add_natrec_kexpr_cong0()?;
        self.add_delta_subst_val()?;
        self.add_delta_subststar_val()?;
        self.add_sc_let_join_helpers()?;
        Ok(())
    }

    /// Brick 1d-helper: `natrec_kexpr_cong0` — a δ*-congruence for a `Nat.rec` whose
    /// step ignores both the predecessor and the recursive result (a constant `Y`).
    /// If the zero-case bodies are δ*-related (`delta_cong_star env X X'`) then the
    /// whole `Nat.rec` is δ*-related at any depth `n` (the succ branch is the SHARED
    /// `Y`, hence refl). Proved by `Nat.rec` on `n` (zero arm = the hypothesis, succ
    /// arm = refl on `Y`). The case-splitter the `delta_subst_val` bvar arm uses to
    /// peel the `instantiate_bvar_at` / `instantiate_bvar_geq` three-way comparison
    /// (both unfold to exactly this `Nat.rec` shape).
    fn add_natrec_kexpr_cong0(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "natrec_kexpr_cong0".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (X : KExpr) (X' : KExpr) (Y : KExpr) (n : Nat), ",
                "delta_cong_star env X X' -> ",
                "delta_cong_star env ",
                "(Nat.rec (fun (_ : Nat) => KExpr) X (fun (_ : Nat) (_ : KExpr) => Y) n) ",
                "(Nat.rec (fun (_ : Nat) => KExpr) X' (fun (_ : Nat) (_ : KExpr) => Y) n)"
            )
            .to_string(),
            value_src: Some(natrec_kexpr_cong0_proof()),
            is_axiom: false,
            description: concat!(
                "natrec_kexpr_cong0 — δ*-congruence for a Nat.rec whose step is a constant Y (ignores ",
                "predecessor + recursive result). delta_cong_star env X X' lifts to delta_cong_star on the whole ",
                "Nat.rec at any depth n. Nat.rec on n: zero arm = the hypothesis, succ arm = refl on Y (both ",
                "branches give Y). The case-splitter delta_subst_val's bvar arm uses to peel the ",
                "instantiate_bvar_at / instantiate_bvar_geq three-way comparison (both unfold to this Nat.rec ",
                "shape). DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4 — ",
                "Hindley-Rosen assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong_star".to_string(),
                "delta_cong_star.refl".to_string(),
                "Nat.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Brick 1d: `delta_subst_val` — substituting a δ-stepped value DUPLICATES it
    /// across the bound-variable occurrences. A single δ step in the value `v -> v'`
    /// substituted into a FIXED body `t` gives a δ-CHAIN `delta_cong_star env
    /// (instantiate_at t v depth) (instantiate_at t v' depth)` (the value may appear
    /// 0, 1, or many times, so a star). KExpr induction on `t` (motive generalized
    /// over the depth): sort/const are refl; app/lam/pi recurse via the star
    /// congruences (`delta_cong_star_{app,lam,pi}`, binder arms at `succ depth`); the
    /// bvar arm peels the `instantiate_bvar_at` three-way comparison via
    /// `natrec_kexpr_cong0` twice, the matching occurrence being `lift_at v 0 depth`
    /// vs `lift_at v' 0 depth` (δ-related by `delta_lift_cong`). Blueprint
    /// `delta_subst_val`.
    fn add_delta_subst_val(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "delta_subst_val".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (liftclosed : DefEnvLiftClosed (red_def env)) ",
                "(v : KExpr) (v' : KExpr), delta_cong env v v' -> ",
                "forall (t : KExpr) (depth : Nat), ",
                "delta_cong_star env (instantiate_at t v depth) (instantiate_at t v' depth)"
            )
            .to_string(),
            value_src: Some(delta_subst_val_proof()),
            is_axiom: false,
            description: concat!(
                "delta_subst_val — substituting a δ-stepped value DUPLICATES it across the bound-variable ",
                "occurrences: a single δ step v -> v' substituted into a fixed body t gives a δ-CHAIN ",
                "delta_cong_star env (instantiate_at t v depth) (instantiate_at t v' depth). KExpr induction on t ",
                "(motive generalized over the depth): sort/const are refl; app/lam/pi recurse via ",
                "delta_cong_star_{app,lam,pi} (binder arms at succ depth); the genuine let_ node recurses via the ",
                "compound delta_cong_star_let (body at succ depth); the bvar arm peels the ",
                "instantiate_bvar_at three-way comparison via natrec_kexpr_cong0 twice, the matching occurrence ",
                "lift_at v 0 depth vs lift_at v' 0 depth being δ-related by delta_lift_cong. Blueprint ",
                "delta_subst_val. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta increment ",
                "Stage 4 — Hindley-Rosen assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong".to_string(),
                "delta_cong_star".to_string(),
                "delta_cong_star.refl".to_string(),
                "delta_cong_star_app".to_string(),
                "delta_cong_star_lam".to_string(),
                "delta_cong_star_pi".to_string(),
                "delta_cong_star_let".to_string(),
                "delta_cong_star_proj".to_string(),
                "delta_cong_subsumes_star".to_string(),
                "delta_lift_cong".to_string(),
                "natrec_kexpr_cong0".to_string(),
                "KExpr.rec".to_string(),
                "instantiate_at".to_string(),
                "instantiate_bvar_at".to_string(),
                "instantiate_bvar_geq".to_string(),
                "lift_at".to_string(),
                "DefEnvLiftClosed".to_string(),
                "red_def".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Brick 1e: `delta_substStar_val` — the δ*-version of `delta_subst_val`. A
    /// δ-CHAIN in the value `delta_cong_star env v v'` substituted into a fixed body
    /// gives `delta_cong_star env (instantiate_at t v depth) (instantiate_at t v'
    /// depth)`. Induction on the value chain (`delta_cong_star.rec`): refl is refl,
    /// step composes `delta_subst_val` on the head with the IH via
    /// `delta_cong_star_trans`. This is the lemma the β/let δ-on-arg subcase of `SC`
    /// uses to catch the substituted argument up. Blueprint `delta_substStar_val`.
    fn add_delta_subststar_val(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "delta_substStar_val".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (liftclosed : DefEnvLiftClosed (red_def env)) ",
                "(v : KExpr) (v' : KExpr), delta_cong_star env v v' -> ",
                "forall (t : KExpr) (depth : Nat), ",
                "delta_cong_star env (instantiate_at t v depth) (instantiate_at t v' depth)"
            )
            .to_string(),
            value_src: Some(delta_subststar_val_proof()),
            is_axiom: false,
            description: concat!(
                "delta_substStar_val — δ*-version of delta_subst_val: a δ-CHAIN in the value delta_cong_star env ",
                "v v' substituted into a fixed body gives delta_cong_star env (instantiate_at t v depth) ",
                "(instantiate_at t v' depth). Induction on the value chain (delta_cong_star.rec): refl is refl, ",
                "step composes delta_subst_val on the head with the IH via delta_cong_star_trans. The lemma the ",
                "β/let δ-on-arg subcase of SC uses to catch the substituted argument up. Blueprint ",
                "delta_substStar_val. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta ",
                "increment Stage 4 — Hindley-Rosen assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong".to_string(),
                "delta_cong_star".to_string(),
                "delta_cong_star.rec".to_string(),
                "delta_cong_star.refl".to_string(),
                "delta_cong_star_trans".to_string(),
                "delta_subst_val".to_string(),
                "instantiate_at".to_string(),
                "DefEnvLiftClosed".to_string(),
                "red_def".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Brick 1a: `delta_lift_cong` — delta commutes with `lift_at`. A single-position
    /// delta step `delta_cong env t t'` lifts to `delta_cong env (lift_at t c a)
    /// (lift_at t' c a)` for any cutoff `c` (amount `a` fixed). Induction on
    /// `delta_cong` (`delta_cong.rec`, motive generalized over the cutoff so binder
    /// arms can recurse at `succ c`): the `here` arm fires `delta_lift_commutes`
    /// (under `DefEnvLiftClosed`); the six congruence arms recurse, pushing `lift_at`
    /// through the KExpr ctor by definitional unfolding. Blueprint `delta_lift_cong`.
    fn add_delta_lift_cong(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "delta_lift_cong".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (liftclosed : DefEnvLiftClosed (red_def env)) (a : Nat) ",
                "(t : KExpr) (t' : KExpr), delta_cong env t t' -> ",
                "forall (c : Nat), delta_cong env (lift_at t c a) (lift_at t' c a)"
            )
            .to_string(),
            value_src: Some(delta_lift_cong_proof()),
            is_axiom: false,
            description: concat!(
                "delta_lift_cong — delta commutes with lift_at: a single-position delta step delta_cong env t ",
                "t' lifts to delta_cong env (lift_at t c a) (lift_at t' c a) for any cutoff c. Induction on ",
                "delta_cong (motive generalized over the cutoff): the here arm fires the directed keystone ",
                "delta_lift_commutes (under the faithful DefEnvLiftClosed interface); the nine congruence arms ",
                "(incl. the trailing let_t/let_v/let_b over the genuine let_ node) recurse, binder arms at succ ",
                "c, pushing lift_at through the KExpr ctor by definitional ",
                "unfolding. Blueprint delta_lift_cong. DerivedProved, zero axiom_deps. Part of #2859 (Increment ",
                "H++, delta increment Stage 4 — Hindley-Rosen assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong".to_string(),
                "delta_cong.rec".to_string(),
                "delta_cong.here".to_string(),
                "delta_cong.app_f".to_string(),
                "delta_cong.app_a".to_string(),
                "delta_cong.lam_t".to_string(),
                "delta_cong.lam_b".to_string(),
                "delta_cong.pi_d".to_string(),
                "delta_cong.pi_b".to_string(),
                "delta_cong.let_t".to_string(),
                "delta_cong.let_v".to_string(),
                "delta_cong.let_b".to_string(),
                "delta_step".to_string(),
                "delta_lift_commutes".to_string(),
                "DefEnvLiftClosed".to_string(),
                "lift_at".to_string(),
                "red_def".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Brick 1b: `delta_subst_cong` — delta commutes with `instantiate_at`. A
    /// single-position delta step `delta_cong env t t'` survives substitution as
    /// `delta_cong env (instantiate_at t v depth) (instantiate_at t' v depth)` for
    /// any depth (value `v` fixed; the in-tree `instantiate_at` keeps `v` fixed
    /// under binders, deferring the lift to the bvar match). Induction on
    /// `delta_cong` (motive generalized over the depth): the `here` arm fires
    /// `delta_subst_commutes` (under `DefEnvClosed`); the six congruence arms
    /// recurse, binder arms at `succ depth`. Blueprint `delta_subst_cong`.
    fn add_delta_subst_cong(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "delta_subst_cong".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (closed : DefEnvClosed (red_def env)) (v : KExpr) ",
                "(t : KExpr) (t' : KExpr), delta_cong env t t' -> ",
                "forall (depth : Nat), delta_cong env (instantiate_at t v depth) (instantiate_at t' v depth)"
            )
            .to_string(),
            value_src: Some(delta_subst_cong_proof()),
            is_axiom: false,
            description: concat!(
                "delta_subst_cong — delta commutes with instantiate_at: a single-position delta step delta_cong ",
                "env t t' survives substitution as delta_cong env (instantiate_at t v depth) (instantiate_at t' ",
                "v depth) for any depth. Induction on delta_cong (motive generalized over the depth): the here ",
                "arm fires the directed keystone delta_subst_commutes (under the faithful DefEnvClosed interface); ",
                "the nine congruence arms (incl. the trailing let_t/let_v/let_b over the genuine let_ node) ",
                "recurse, binder arms at succ depth, pushing instantiate_at through the ",
                "KExpr ctor by definitional unfolding. Blueprint delta_subst_cong. DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment H++, delta increment Stage 4 — Hindley-Rosen assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong".to_string(),
                "delta_cong.rec".to_string(),
                "delta_cong.here".to_string(),
                "delta_cong.app_f".to_string(),
                "delta_cong.app_a".to_string(),
                "delta_cong.lam_t".to_string(),
                "delta_cong.lam_b".to_string(),
                "delta_cong.pi_d".to_string(),
                "delta_cong.pi_b".to_string(),
                "delta_cong.let_t".to_string(),
                "delta_cong.let_v".to_string(),
                "delta_cong.let_b".to_string(),
                "delta_step".to_string(),
                "delta_subst_commutes".to_string(),
                "DefEnvClosed".to_string(),
                "instantiate_at".to_string(),
                "red_def".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Brick 1c: `delta_substStar_body` — delta* in the body lifted to substitution.
    /// A delta-chain `delta_cong_star env t t'` substituted into a fixed value/depth
    /// gives `delta_cong_star env (instantiate_at t v depth) (instantiate_at t' v
    /// depth)`. Induction on the closure (`delta_cong_star.rec`): refl is refl,
    /// step prefixes `delta_subst_cong` on the head. This is the lemma the beta/let
    /// delta-on-body subcase of `SC` uses to catch the substituted body up.
    /// Blueprint `delta_substStar_body`.
    fn add_delta_subststar_body(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "delta_substStar_body".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (closed : DefEnvClosed (red_def env)) (v : KExpr) (depth : Nat) ",
                "(t : KExpr) (t' : KExpr), delta_cong_star env t t' -> ",
                "delta_cong_star env (instantiate_at t v depth) (instantiate_at t' v depth)"
            )
            .to_string(),
            value_src: Some(delta_subststar_body_proof()),
            is_axiom: false,
            description: concat!(
                "delta_substStar_body — delta* in the body lifted to substitution: a delta-chain delta_cong_star ",
                "env t t' substituted at a fixed value/depth gives delta_cong_star env (instantiate_at t v depth) ",
                "(instantiate_at t' v depth). Induction on the closure (delta_cong_star.rec): refl is refl, step ",
                "prefixes delta_subst_cong on the head delta-step. The lemma the beta/let delta-on-body subcase of ",
                "SC uses to catch the substituted body up. Blueprint delta_substStar_body. DerivedProved, zero ",
                "axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4 — Hindley-Rosen assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong".to_string(),
                "delta_cong_star".to_string(),
                "delta_cong_star.rec".to_string(),
                "delta_cong_star.refl".to_string(),
                "delta_cong_star.step".to_string(),
                "delta_subst_cong".to_string(),
                "instantiate_at".to_string(),
                "DefEnvClosed".to_string(),
                "red_def".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Let promotion (task #28): the ζ-redex SC join helpers
    /// `sc_let_join_{ty,val,body}` — mirrors of `sc_beta_join_{type,body,arg}`
    /// (`par_reduces_iota_delta.rs`) at the genuine `KExpr.let_` node. Each takes an
    /// already-inverted δ step (a reduct equation + the relevant IH witness) and
    /// builds the `par_delta_sc_witness` for the ζ contraction `let_ ty val body ⇒
    /// instantiate body' val'`: δ-in-ty is discarded by ζ (join in one β+ι+ζ step),
    /// δ-in-val re-substitutes via `delta_substStar_val`, δ-in-body via
    /// `delta_substStar_body` — each firing one `par_reduces_c.let_` to catch up.
    fn add_sc_let_join_helpers(&mut self) -> Result<(), SpecError> {
        // ζ δ-in-ty: the let type annotation is discarded, so the join is one β+ι+ζ.
        self.add_definition(SpecDefinition {
            name: "sc_let_join_ty".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (At : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) ",
                "(body' : KExpr) (w : KExpr) (hval : par_reduces_c (red_rec env) val val') ",
                "(hbody : par_reduces_c (red_rec env) body body') ",
                "(heqr : Eq KExpr w (KExpr.let_ At val body)), ",
                "par_delta_sc_witness env (instantiate body' val') w"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (At : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) ",
                    "(body' : KExpr) (w : KExpr) (hval : par_reduces_c (red_rec env) val val') ",
                    "(hbody : par_reduces_c (red_rec env) body body') ",
                    "(heqr : Eq KExpr w (KExpr.let_ At val body)) => ",
                    "Eq.substType KExpr (fun (x : KExpr) => par_delta_sc_witness env (instantiate body' val') x) ",
                    "(KExpr.let_ At val body) w (Eq.symm KExpr w (KExpr.let_ At val body) heqr) ",
                    "(par_delta_sc_witness.intro env (instantiate body' val') (KExpr.let_ At val body) (instantiate body' val') ",
                    "(delta_cong_star.refl env (instantiate body' val')) ",
                    "(par_reduces_c.let_ (red_rec env) At At val val' body body' (par_reduces_c.refl (red_rec env) At) hval hbody))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "sc_let_join_ty — ζ-redex δ-in-type join: the let type annotation is discarded by the zeta contraction, so the δ-reduct fires one β+ι+ζ (par_reduces_c.let_) to the common reduct instantiate body' val'. Mirror of sc_beta_join_type at the genuine let_ node (let promotion, task #28). DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, Stage 4).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_delta_sc_witness".to_string(),
                "par_delta_sc_witness.intro".to_string(),
                "par_reduces_c.let_".to_string(),
                "par_reduces_c.refl".to_string(),
                "delta_cong_star.refl".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "red_rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ζ δ-in-val: val' δ* dv (from the IH witness), re-substituted via
        // delta_substStar_val.
        self.add_definition(SpecDefinition {
            name: "sc_let_join_val".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (liftclosed : DefEnvLiftClosed (red_def env)) (ty : KExpr) ",
                "(body : KExpr) (body' : KExpr) (val' : KExpr) (vt : KExpr) (w : KExpr) ",
                "(hbody : par_reduces_c (red_rec env) body body') ",
                "(heqr : Eq KExpr w (KExpr.let_ ty vt body)) ",
                "(ihw : par_delta_sc_witness env val' vt), ",
                "par_delta_sc_witness env (instantiate body' val') w"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (liftclosed : DefEnvLiftClosed (red_def env)) (ty : KExpr) ",
                    "(body : KExpr) (body' : KExpr) (val' : KExpr) (vt : KExpr) (w : KExpr) ",
                    "(hbody : par_reduces_c (red_rec env) body body') ",
                    "(heqr : Eq KExpr w (KExpr.let_ ty vt body)) ",
                    "(ihw : par_delta_sc_witness env val' vt) => ",
                    "@par_delta_sc_witness.rec env val' vt ",
                    "(fun (_ : par_delta_sc_witness env val' vt) => par_delta_sc_witness env (instantiate body' val') w) ",
                    "(fun (dv : KExpr) (hdv : delta_cong_star env val' dv) (hpv : par_reduces_c (red_rec env) vt dv) => ",
                    "Eq.substType KExpr (fun (x : KExpr) => par_delta_sc_witness env (instantiate body' val') x) ",
                    "(KExpr.let_ ty vt body) w (Eq.symm KExpr w (KExpr.let_ ty vt body) heqr) ",
                    "(par_delta_sc_witness.intro env (instantiate body' val') (KExpr.let_ ty vt body) (instantiate body' dv) ",
                    "(delta_substStar_val env liftclosed val' dv hdv body' Nat.zero) ",
                    "(par_reduces_c.let_ (red_rec env) ty ty vt dv body body' (par_reduces_c.refl (red_rec env) ty) hpv hbody))) ",
                    "ihw"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "sc_let_join_val — ζ-redex δ-in-value join: destructure the value IH witness (dv, δ* val' dv, par vt dv), re-substitute the δ-chain into the body via delta_substStar_val, fire one β+ι+ζ (par_reduces_c.let_). Mirror of sc_beta_join_arg at the genuine let_ node (let promotion, task #28). DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, Stage 4).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_delta_sc_witness".to_string(),
                "par_delta_sc_witness.intro".to_string(),
                "par_delta_sc_witness.rec".to_string(),
                "par_reduces_c.let_".to_string(),
                "par_reduces_c.refl".to_string(),
                "delta_substStar_val".to_string(),
                "DefEnvLiftClosed".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ζ δ-in-body: body' δ* db (from the IH witness), re-substituted via
        // delta_substStar_body.
        self.add_definition(SpecDefinition {
            name: "sc_let_join_body".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (closed : DefEnvClosed (red_def env)) (ty : KExpr) ",
                "(val : KExpr) (val' : KExpr) (body' : KExpr) (bt : KExpr) (w : KExpr) ",
                "(hval : par_reduces_c (red_rec env) val val') ",
                "(heqr : Eq KExpr w (KExpr.let_ ty val bt)) ",
                "(ihw : par_delta_sc_witness env body' bt), ",
                "par_delta_sc_witness env (instantiate body' val') w"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (closed : DefEnvClosed (red_def env)) (ty : KExpr) ",
                    "(val : KExpr) (val' : KExpr) (body' : KExpr) (bt : KExpr) (w : KExpr) ",
                    "(hval : par_reduces_c (red_rec env) val val') ",
                    "(heqr : Eq KExpr w (KExpr.let_ ty val bt)) ",
                    "(ihw : par_delta_sc_witness env body' bt) => ",
                    "@par_delta_sc_witness.rec env body' bt ",
                    "(fun (_ : par_delta_sc_witness env body' bt) => par_delta_sc_witness env (instantiate body' val') w) ",
                    "(fun (db : KExpr) (hdb : delta_cong_star env body' db) (hpb : par_reduces_c (red_rec env) bt db) => ",
                    "Eq.substType KExpr (fun (x : KExpr) => par_delta_sc_witness env (instantiate body' val') x) ",
                    "(KExpr.let_ ty val bt) w (Eq.symm KExpr w (KExpr.let_ ty val bt) heqr) ",
                    "(par_delta_sc_witness.intro env (instantiate body' val') (KExpr.let_ ty val bt) (instantiate db val') ",
                    "(delta_substStar_body env closed val' Nat.zero body' db hdb) ",
                    "(par_reduces_c.let_ (red_rec env) ty ty val val' bt db (par_reduces_c.refl (red_rec env) ty) hval hpb))) ",
                    "ihw"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "sc_let_join_body — ζ-redex δ-in-body join: destructure the body IH witness (db, δ* body' db, par bt db), re-substitute the δ-chain against the value via delta_substStar_body, fire one β+ι+ζ (par_reduces_c.let_). Mirror of sc_beta_join_body at the genuine let_ node (let promotion, task #28). DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, Stage 4).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_delta_sc_witness".to_string(),
                "par_delta_sc_witness.intro".to_string(),
                "par_delta_sc_witness.rec".to_string(),
                "par_reduces_c.let_".to_string(),
                "par_reduces_c.refl".to_string(),
                "delta_substStar_body".to_string(),
                "DefEnvClosed".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

/// Proof term for `delta_lift_cong`. `delta_cong.rec` with a cutoff-generalized
/// motive; `here` fires `delta_lift_commutes`, the nine congruence arms recurse
/// (binder arms at `Nat.succ c`).
fn delta_lift_cong_proof() -> String {
    let motive = concat!(
        "(fun (x : KExpr) (y : KExpr) (_h : delta_cong env x y) => ",
        "forall (c : Nat), delta_cong env (lift_at x c a) (lift_at y c a))"
    );
    let here_arm = concat!(
        "(fun (e : KExpr) (e' : KExpr) (hd : delta_step (red_def env) e e') => ",
        "fun (c : Nat) => delta_cong.here env (lift_at e c a) (lift_at e' c a) ",
        "(delta_lift_commutes (red_def env) e e' c a liftclosed hd))"
    );
    let app_f_arm = concat!(
        "(fun (f : KExpr) (f' : KExpr) (a0 : KExpr) (_h : delta_cong env f f') ",
        "(ih : forall (c : Nat), delta_cong env (lift_at f c a) (lift_at f' c a)) => ",
        "fun (c : Nat) => delta_cong.app_f env (lift_at f c a) (lift_at f' c a) (lift_at a0 c a) (ih c))"
    );
    let app_a_arm = concat!(
        "(fun (f : KExpr) (a0 : KExpr) (a0' : KExpr) (_h : delta_cong env a0 a0') ",
        "(ih : forall (c : Nat), delta_cong env (lift_at a0 c a) (lift_at a0' c a)) => ",
        "fun (c : Nat) => delta_cong.app_a env (lift_at f c a) (lift_at a0 c a) (lift_at a0' c a) (ih c))"
    );
    let lam_t_arm = concat!(
        "(fun (t0 : KExpr) (t0' : KExpr) (b : KExpr) (_h : delta_cong env t0 t0') ",
        "(ih : forall (c : Nat), delta_cong env (lift_at t0 c a) (lift_at t0' c a)) => ",
        "fun (c : Nat) => delta_cong.lam_t env (lift_at t0 c a) (lift_at t0' c a) (lift_at b (Nat.succ c) a) (ih c))"
    );
    let lam_b_arm = concat!(
        "(fun (t0 : KExpr) (b : KExpr) (b' : KExpr) (_h : delta_cong env b b') ",
        "(ih : forall (c : Nat), delta_cong env (lift_at b c a) (lift_at b' c a)) => ",
        "fun (c : Nat) => delta_cong.lam_b env (lift_at t0 c a) (lift_at b (Nat.succ c) a) (lift_at b' (Nat.succ c) a) (ih (Nat.succ c)))"
    );
    let pi_d_arm = concat!(
        "(fun (d0 : KExpr) (d0' : KExpr) (b : KExpr) (_h : delta_cong env d0 d0') ",
        "(ih : forall (c : Nat), delta_cong env (lift_at d0 c a) (lift_at d0' c a)) => ",
        "fun (c : Nat) => delta_cong.pi_d env (lift_at d0 c a) (lift_at d0' c a) (lift_at b (Nat.succ c) a) (ih c))"
    );
    let pi_b_arm = concat!(
        "(fun (d0 : KExpr) (b : KExpr) (b' : KExpr) (_h : delta_cong env b b') ",
        "(ih : forall (c : Nat), delta_cong env (lift_at b c a) (lift_at b' c a)) => ",
        "fun (c : Nat) => delta_cong.pi_b env (lift_at d0 c a) (lift_at b (Nat.succ c) a) (lift_at b' (Nat.succ c) a) (ih (Nat.succ c)))"
    );
    // Trailing let congruence arms (let promotion, task #28): ty/val recurse at the
    // current cutoff, the body under the binder at Nat.succ c (the lam treatment).
    let let_t_arm = concat!(
        "(fun (t0 : KExpr) (t0' : KExpr) (vv : KExpr) (bb : KExpr) (_h : delta_cong env t0 t0') ",
        "(ih : forall (c : Nat), delta_cong env (lift_at t0 c a) (lift_at t0' c a)) => ",
        "fun (c : Nat) => delta_cong.let_t env (lift_at t0 c a) (lift_at t0' c a) (lift_at vv c a) (lift_at bb (Nat.succ c) a) (ih c))"
    );
    let let_v_arm = concat!(
        "(fun (t0 : KExpr) (vv : KExpr) (vv' : KExpr) (bb : KExpr) (_h : delta_cong env vv vv') ",
        "(ih : forall (c : Nat), delta_cong env (lift_at vv c a) (lift_at vv' c a)) => ",
        "fun (c : Nat) => delta_cong.let_v env (lift_at t0 c a) (lift_at vv c a) (lift_at vv' c a) (lift_at bb (Nat.succ c) a) (ih c))"
    );
    let let_b_arm = concat!(
        "(fun (t0 : KExpr) (vv : KExpr) (bb : KExpr) (bb' : KExpr) (_h : delta_cong env bb bb') ",
        "(ih : forall (c : Nat), delta_cong env (lift_at bb c a) (lift_at bb' c a)) => ",
        "fun (c : Nat) => delta_cong.let_b env (lift_at t0 c a) (lift_at vv c a) (lift_at bb (Nat.succ c) a) (lift_at bb' (Nat.succ c) a) (ih (Nat.succ c)))"
    );
    // proj_s arm (proj/lit rung): proj has no binder — the scrutinee lifts at the
    // SAME cutoff c (lift_at descends into proj by defeq). Emit delta_cong.proj_s.
    let proj_s_arm = concat!(
        "(fun (ps : Name) (pidx : Nat) (sub : KExpr) (sub' : KExpr) (_h : delta_cong env sub sub') ",
        "(ih : forall (c : Nat), delta_cong env (lift_at sub c a) (lift_at sub' c a)) => ",
        "fun (c : Nat) => delta_cong.proj_s env ps pidx (lift_at sub c a) (lift_at sub' c a) (ih c))"
    );
    format!(
        concat!(
            "fun (env : RedEnv) (liftclosed : DefEnvLiftClosed (red_def env)) (a : Nat) ",
            "(t : KExpr) (t' : KExpr) (h : delta_cong env t t') => ",
            "delta_cong.rec env {motive} {here} {app_f} {app_a} {lam_t} {lam_b} {pi_d} {pi_b} {let_t} {let_v} {let_b} {proj_s} t t' h"
        ),
        motive = motive,
        here = here_arm,
        app_f = app_f_arm,
        app_a = app_a_arm,
        lam_t = lam_t_arm,
        lam_b = lam_b_arm,
        pi_d = pi_d_arm,
        pi_b = pi_b_arm,
        let_t = let_t_arm,
        let_v = let_v_arm,
        let_b = let_b_arm,
        proj_s = proj_s_arm,
    )
}

/// Proof term for `delta_subst_cong`. `delta_cong.rec` with a depth-generalized
/// motive; `here` fires `delta_subst_commutes`, the six congruence arms recurse
/// (binder arms at `Nat.succ depth`).
fn delta_subst_cong_proof() -> String {
    let motive = concat!(
        "(fun (x : KExpr) (y : KExpr) (_h : delta_cong env x y) => ",
        "forall (depth : Nat), delta_cong env (instantiate_at x v depth) (instantiate_at y v depth))"
    );
    let here_arm = concat!(
        "(fun (e : KExpr) (e' : KExpr) (hd : delta_step (red_def env) e e') => ",
        "fun (depth : Nat) => delta_cong.here env (instantiate_at e v depth) (instantiate_at e' v depth) ",
        "(delta_subst_commutes (red_def env) e e' v depth closed hd))"
    );
    let app_f_arm = concat!(
        "(fun (f : KExpr) (f' : KExpr) (a0 : KExpr) (_h : delta_cong env f f') ",
        "(ih : forall (depth : Nat), delta_cong env (instantiate_at f v depth) (instantiate_at f' v depth)) => ",
        "fun (depth : Nat) => delta_cong.app_f env (instantiate_at f v depth) (instantiate_at f' v depth) (instantiate_at a0 v depth) (ih depth))"
    );
    let app_a_arm = concat!(
        "(fun (f : KExpr) (a0 : KExpr) (a0' : KExpr) (_h : delta_cong env a0 a0') ",
        "(ih : forall (depth : Nat), delta_cong env (instantiate_at a0 v depth) (instantiate_at a0' v depth)) => ",
        "fun (depth : Nat) => delta_cong.app_a env (instantiate_at f v depth) (instantiate_at a0 v depth) (instantiate_at a0' v depth) (ih depth))"
    );
    let lam_t_arm = concat!(
        "(fun (t0 : KExpr) (t0' : KExpr) (b : KExpr) (_h : delta_cong env t0 t0') ",
        "(ih : forall (depth : Nat), delta_cong env (instantiate_at t0 v depth) (instantiate_at t0' v depth)) => ",
        "fun (depth : Nat) => delta_cong.lam_t env (instantiate_at t0 v depth) (instantiate_at t0' v depth) (instantiate_at b v (Nat.succ depth)) (ih depth))"
    );
    let lam_b_arm = concat!(
        "(fun (t0 : KExpr) (b : KExpr) (b' : KExpr) (_h : delta_cong env b b') ",
        "(ih : forall (depth : Nat), delta_cong env (instantiate_at b v depth) (instantiate_at b' v depth)) => ",
        "fun (depth : Nat) => delta_cong.lam_b env (instantiate_at t0 v depth) (instantiate_at b v (Nat.succ depth)) (instantiate_at b' v (Nat.succ depth)) (ih (Nat.succ depth)))"
    );
    let pi_d_arm = concat!(
        "(fun (d0 : KExpr) (d0' : KExpr) (b : KExpr) (_h : delta_cong env d0 d0') ",
        "(ih : forall (depth : Nat), delta_cong env (instantiate_at d0 v depth) (instantiate_at d0' v depth)) => ",
        "fun (depth : Nat) => delta_cong.pi_d env (instantiate_at d0 v depth) (instantiate_at d0' v depth) (instantiate_at b v (Nat.succ depth)) (ih depth))"
    );
    let pi_b_arm = concat!(
        "(fun (d0 : KExpr) (b : KExpr) (b' : KExpr) (_h : delta_cong env b b') ",
        "(ih : forall (depth : Nat), delta_cong env (instantiate_at b v depth) (instantiate_at b' v depth)) => ",
        "fun (depth : Nat) => delta_cong.pi_b env (instantiate_at d0 v depth) (instantiate_at b v (Nat.succ depth)) (instantiate_at b' v (Nat.succ depth)) (ih (Nat.succ depth)))"
    );
    // Trailing let congruence arms (let promotion, task #28): ty/val recurse at the
    // current depth, the body under the binder at Nat.succ depth (the lam treatment).
    let let_t_arm = concat!(
        "(fun (t0 : KExpr) (t0' : KExpr) (vv : KExpr) (bb : KExpr) (_h : delta_cong env t0 t0') ",
        "(ih : forall (depth : Nat), delta_cong env (instantiate_at t0 v depth) (instantiate_at t0' v depth)) => ",
        "fun (depth : Nat) => delta_cong.let_t env (instantiate_at t0 v depth) (instantiate_at t0' v depth) (instantiate_at vv v depth) (instantiate_at bb v (Nat.succ depth)) (ih depth))"
    );
    let let_v_arm = concat!(
        "(fun (t0 : KExpr) (vv : KExpr) (vv' : KExpr) (bb : KExpr) (_h : delta_cong env vv vv') ",
        "(ih : forall (depth : Nat), delta_cong env (instantiate_at vv v depth) (instantiate_at vv' v depth)) => ",
        "fun (depth : Nat) => delta_cong.let_v env (instantiate_at t0 v depth) (instantiate_at vv v depth) (instantiate_at vv' v depth) (instantiate_at bb v (Nat.succ depth)) (ih depth))"
    );
    let let_b_arm = concat!(
        "(fun (t0 : KExpr) (vv : KExpr) (bb : KExpr) (bb' : KExpr) (_h : delta_cong env bb bb') ",
        "(ih : forall (depth : Nat), delta_cong env (instantiate_at bb v depth) (instantiate_at bb' v depth)) => ",
        "fun (depth : Nat) => delta_cong.let_b env (instantiate_at t0 v depth) (instantiate_at vv v depth) (instantiate_at bb v (Nat.succ depth)) (instantiate_at bb' v (Nat.succ depth)) (ih (Nat.succ depth)))"
    );
    // proj_s arm (proj/lit rung): proj has no binder — the scrutinee substitutes at the
    // SAME depth (instantiate_at descends into proj by defeq). Emit delta_cong.proj_s.
    let proj_s_arm = concat!(
        "(fun (ps : Name) (pidx : Nat) (sub : KExpr) (sub' : KExpr) (_h : delta_cong env sub sub') ",
        "(ih : forall (depth : Nat), delta_cong env (instantiate_at sub v depth) (instantiate_at sub' v depth)) => ",
        "fun (depth : Nat) => delta_cong.proj_s env ps pidx (instantiate_at sub v depth) (instantiate_at sub' v depth) (ih depth))"
    );
    format!(
        concat!(
            "fun (env : RedEnv) (closed : DefEnvClosed (red_def env)) (v : KExpr) ",
            "(t : KExpr) (t' : KExpr) (h : delta_cong env t t') => ",
            "delta_cong.rec env {motive} {here} {app_f} {app_a} {lam_t} {lam_b} {pi_d} {pi_b} {let_t} {let_v} {let_b} {proj_s} t t' h"
        ),
        motive = motive,
        here = here_arm,
        app_f = app_f_arm,
        app_a = app_a_arm,
        lam_t = lam_t_arm,
        lam_b = lam_b_arm,
        pi_d = pi_d_arm,
        pi_b = pi_b_arm,
        let_t = let_t_arm,
        let_v = let_v_arm,
        let_b = let_b_arm,
        proj_s = proj_s_arm,
    )
}

/// Proof term for `delta_substStar_body`. `delta_cong_star.rec` lifting
/// `delta_subst_cong` over the closure.
fn delta_subststar_body_proof() -> String {
    concat!(
        "fun (env : RedEnv) (closed : DefEnvClosed (red_def env)) (v : KExpr) (depth : Nat) ",
        "(t : KExpr) (t' : KExpr) (h : delta_cong_star env t t') => ",
        "delta_cong_star.rec env ",
        "(fun (x : KExpr) (y : KExpr) (_ : delta_cong_star env x y) => ",
        "delta_cong_star env (instantiate_at x v depth) (instantiate_at y v depth)) ",
        "(fun (s : KExpr) => delta_cong_star.refl env (instantiate_at s v depth)) ",
        "(fun (s : KExpr) (s' : KExpr) (s'' : KExpr) ",
        "(hstep : delta_cong env s s') (_htail : delta_cong_star env s' s'') ",
        "(ih : delta_cong_star env (instantiate_at s' v depth) (instantiate_at s'' v depth)) => ",
        "delta_cong_star.step env (instantiate_at s v depth) (instantiate_at s' v depth) (instantiate_at s'' v depth) ",
        "(delta_subst_cong env closed v s s' hstep depth) ih) ",
        "t t' h"
    )
    .to_string()
}

/// Proof term for `natrec_kexpr_cong0`. `Nat.rec` on `n`: zero arm is the
/// hypothesis (`Nat.rec ... Nat.zero` reduces to the zero-case body), succ arm is
/// refl on `Y` (`Nat.rec ... (succ m)` reduces to the shared step body `Y`).
fn natrec_kexpr_cong0_proof() -> String {
    let natrec = |z: &str| {
        format!("(Nat.rec (fun (_ : Nat) => KExpr) {z} (fun (_ : Nat) (_ : KExpr) => Y) m)")
    };
    let motive = format!(
        "(fun (m : Nat) => delta_cong_star env {lhs} {rhs})",
        lhs = natrec("X"),
        rhs = natrec("X'"),
    );
    let succ_arm = format!(
        "(fun (m : Nat) (_ih : delta_cong_star env {lhs} {rhs}) => delta_cong_star.refl env Y)",
        lhs = natrec("X"),
        rhs = natrec("X'"),
    );
    format!(
        concat!(
            "fun (env : RedEnv) (X : KExpr) (X' : KExpr) (Y : KExpr) (n : Nat) ",
            "(hX : delta_cong_star env X X') => ",
            "Nat.rec {motive} hX {succ_arm} n"
        ),
        motive = motive,
        succ_arm = succ_arm,
    )
}

/// Proof term for `delta_subst_val`. `KExpr.rec` on `t` (motive generalized over
/// the depth); sort/const refl, app/lam/pi via the star congruences, bvar via
/// `natrec_kexpr_cong0` twice (the `instantiate_bvar_at` / `instantiate_bvar_geq`
/// three-way comparison) bottoming out at `delta_lift_cong` on the matching
/// occurrence.
fn delta_subst_val_proof() -> String {
    let motive = concat!(
        "(fun (e : KExpr) => forall (depth : Nat), ",
        "delta_cong_star env (instantiate_at e v depth) (instantiate_at e v' depth))"
    );
    let sort_arm =
        "(fun (n : Level) => fun (depth : Nat) => delta_cong_star.refl env (KExpr.sort n))";
    // bvar: peel instantiate_bvar_at (depth-idx split) then instantiate_bvar_geq
    // (idx-depth split); the matching occurrence is lift_at v 0 depth vs lift_at
    // v' 0 depth, δ-related by delta_lift_cong (amount = depth, cutoff = 0).
    let bvar_arm = concat!(
        "(fun (i : Nat) => fun (depth : Nat) => ",
        "natrec_kexpr_cong0 env ",
        "(instantiate_bvar_geq i depth v) (instantiate_bvar_geq i depth v') (KExpr.bvar i) (Nat.sub depth i) ",
        "(natrec_kexpr_cong0 env ",
        "(lift_at v Nat.zero depth) (lift_at v' Nat.zero depth) ",
        "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (Nat.sub i depth) ",
        "(delta_cong_subsumes_star env (lift_at v Nat.zero depth) (lift_at v' Nat.zero depth) ",
        "(delta_lift_cong env liftclosed depth v v' h Nat.zero))))"
    );
    let app_arm = concat!(
        "(fun (f : KExpr) (arg0 : KExpr) ",
        "(ihf : forall (depth : Nat), delta_cong_star env (instantiate_at f v depth) (instantiate_at f v' depth)) ",
        "(iharg : forall (depth : Nat), delta_cong_star env (instantiate_at arg0 v depth) (instantiate_at arg0 v' depth)) => ",
        "fun (depth : Nat) => delta_cong_star_app env ",
        "(instantiate_at f v depth) (instantiate_at f v' depth) ",
        "(instantiate_at arg0 v depth) (instantiate_at arg0 v' depth) ",
        "(ihf depth) (iharg depth))"
    );
    let lam_arm = concat!(
        "(fun (ty : KExpr) (b : KExpr) ",
        "(ihty : forall (depth : Nat), delta_cong_star env (instantiate_at ty v depth) (instantiate_at ty v' depth)) ",
        "(ihb : forall (depth : Nat), delta_cong_star env (instantiate_at b v depth) (instantiate_at b v' depth)) => ",
        "fun (depth : Nat) => delta_cong_star_lam env ",
        "(instantiate_at ty v depth) (instantiate_at ty v' depth) ",
        "(instantiate_at b v (Nat.succ depth)) (instantiate_at b v' (Nat.succ depth)) ",
        "(ihty depth) (ihb (Nat.succ depth)))"
    );
    let pi_arm = concat!(
        "(fun (dom : KExpr) (b : KExpr) ",
        "(ihd : forall (depth : Nat), delta_cong_star env (instantiate_at dom v depth) (instantiate_at dom v' depth)) ",
        "(ihb : forall (depth : Nat), delta_cong_star env (instantiate_at b v depth) (instantiate_at b v' depth)) => ",
        "fun (depth : Nat) => delta_cong_star_pi env ",
        "(instantiate_at dom v depth) (instantiate_at dom v' depth) ",
        "(instantiate_at b v (Nat.succ depth)) (instantiate_at b v' (Nat.succ depth)) ",
        "(ihd depth) (ihb (Nat.succ depth)))"
    );
    let const_arm = concat!(
        "(fun (nm : Name) (us : ListType Level) => fun (depth : Nat) => ",
        "delta_cong_star.refl env (KExpr.const nm us))"
    );
    // Trailing let_ minor (the genuine 7th KExpr ctor, let promotion, task #28):
    // ty/val recurse at the current depth, the body under the binder at Nat.succ
    // depth; the three component δ-chains recombine via the compound
    // delta_cong_star_let.
    let let_arm = concat!(
        "(fun (ty : KExpr) (vl : KExpr) (b : KExpr) ",
        "(ihty : forall (depth : Nat), delta_cong_star env (instantiate_at ty v depth) (instantiate_at ty v' depth)) ",
        "(ihvl : forall (depth : Nat), delta_cong_star env (instantiate_at vl v depth) (instantiate_at vl v' depth)) ",
        "(ihb : forall (depth : Nat), delta_cong_star env (instantiate_at b v depth) (instantiate_at b v' depth)) => ",
        "fun (depth : Nat) => delta_cong_star_let env ",
        "(instantiate_at ty v depth) (instantiate_at ty v' depth) ",
        "(instantiate_at vl v depth) (instantiate_at vl v' depth) ",
        "(instantiate_at b v (Nat.succ depth)) (instantiate_at b v' (Nat.succ depth)) ",
        "(ihty depth) (ihvl depth) (ihb (Nat.succ depth)))"
    );
    // proj minor (proj/lit rung): proj is a node with no binder — the scrutinee
    // substitutes at the SAME depth (instantiate_at descends into proj by defeq).
    // Mirror of the app arm via the single-hole delta_cong_star_proj congruence.
    let proj_arm = concat!(
        "(fun (ps : Name) (pidx : Nat) (sub : KExpr) ",
        "(ihsub : forall (depth : Nat), delta_cong_star env (instantiate_at sub v depth) (instantiate_at sub v' depth)) => ",
        "fun (depth : Nat) => delta_cong_star_proj env ps pidx ",
        "(instantiate_at sub v depth) (instantiate_at sub v' depth) (ihsub depth))"
    );
    // lit minor: lit is a leaf — instantiate_at (lit n) is the identity, so refl.
    let lit_arm = "(fun (n : Nat) => fun (depth : Nat) => delta_cong_star.refl env (KExpr.lit n))";
    format!(
        concat!(
            "fun (env : RedEnv) (liftclosed : DefEnvLiftClosed (red_def env)) ",
            "(v : KExpr) (v' : KExpr) (h : delta_cong env v v') (t : KExpr) => ",
            "KExpr.rec {motive} {sort_arm} {bvar_arm} {app_arm} {lam_arm} {pi_arm} {const_arm} {let_arm} {proj_arm} {lit_arm} t"
        ),
        motive = motive,
        sort_arm = sort_arm,
        bvar_arm = bvar_arm,
        app_arm = app_arm,
        lam_arm = lam_arm,
        pi_arm = pi_arm,
        const_arm = const_arm,
        let_arm = let_arm,
        proj_arm = proj_arm,
        lit_arm = lit_arm,
    )
}

/// Proof term for `delta_substStar_val`. `delta_cong_star.rec` on the value chain,
/// composing `delta_subst_val` on each head step with the IH.
fn delta_subststar_val_proof() -> String {
    concat!(
        "fun (env : RedEnv) (liftclosed : DefEnvLiftClosed (red_def env)) ",
        "(v : KExpr) (v' : KExpr) (hchain : delta_cong_star env v v') (t : KExpr) (depth : Nat) => ",
        "delta_cong_star.rec env ",
        "(fun (a : KExpr) (b : KExpr) (_ : delta_cong_star env a b) => ",
        "delta_cong_star env (instantiate_at t a depth) (instantiate_at t b depth)) ",
        "(fun (s : KExpr) => delta_cong_star.refl env (instantiate_at t s depth)) ",
        "(fun (s : KExpr) (s1 : KExpr) (s' : KExpr) ",
        "(hstep : delta_cong env s s1) (_htail : delta_cong_star env s1 s') ",
        "(ih : delta_cong_star env (instantiate_at t s1 depth) (instantiate_at t s' depth)) => ",
        "delta_cong_star_trans env (instantiate_at t s depth) (instantiate_at t s1 depth) (instantiate_at t s' depth) ",
        "(delta_subst_val env liftclosed s s1 hstep t depth) ih) ",
        "v v' hchain"
    )
    .to_string()
}

#[cfg(test)]
#[path = "par_reduces_delta_sc_tests.rs"]
mod par_reduces_delta_sc_tests;
