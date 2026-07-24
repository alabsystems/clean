// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment H++ (#2859 computational-iota/delta track, DELTA INCREMENT Stage 4,
//! the HINDLEY-ROSEN redirect): δ CONFLUENCE via Huet strong confluence.
//!
//! ## The Huet strong-confluence lift (verbatim δ mirror of the c-track tiling)
//!
//! `delta_cong` (par_reduces_d.rs) is the SINGLE-POSITION full-δ reduction; it is
//! ORTHOGONAL but has NO refl constructor, so its single-step diamond has STAR
//! legs (the same-leaf case is determinism ⟹ zero-step legs). A star-legged local
//! diamond is only WEAK confluence (WCR); WCR ⊬ Church-Rosser without termination
//! (Newman's lemma; mechanically refuted in scratch StarDiamond). The CORRECT lift
//! is HUET STRONG CONFLUENCE: two single steps join with ONE leg bounded to ≤ 1
//! step. This module ports the abstract `StrongConfluent ⟹ Star-confluent` tiling
//! to δ — VERBATIM the c-track scaffold (`par_strong_join_c` /
//! `par_strips_c_semi_strip_of_strong` / `par_reduces_c_star_diamond_of_strong`,
//! par_reduces_c.rs) — so that δ Church-Rosser is REDUCED to the single honest
//! obligation "delta_cong is strongly confluent" (`par_strong_join_d`-valued).
//!
//! The three bricks:
//!   1. `par_strong_join_d` — the SC join witness (b-leg star, c-leg ≤ 1 step,
//!      encoded as the `zero`/`one` constructor choice; mirror of `par_strong_join_c`).
//!   2. `delta_strips_semi_strip_of_strong` — the SEMI-STRIP lemma, parameterized on
//!      the SC hypothesis (mirror of `par_strips_c_semi_strip_of_strong`).
//!   3. `delta_cong_star_diamond_of_strong` — THE TILING BRICK: SC ⟹ `delta_cong_star`
//!      is Church-Rosser (mirror of `par_reduces_c_star_diamond_of_strong`).
//!
//! Both lemmas carry the strong-confluence hypothesis `SC` as a BOUND PARAMETER
//! (NOT a registered axiom), so the closure is genuinely zero-axiom. The remaining
//! δ-CR obligation is exactly `SC`: the single-step strong diamond of `delta_cong`
//! (`delta_cong env a b → delta_cong env a c → par_strong_join_d env b c`).
//!
//! Runs AFTER `add_par_reduces_d` (delta_cong / delta_cong_star / delta_cong_star_trans
//! / delta_cong_subsumes_star / par_strips_witness_d_star all in scope). Part of #2859
//! (Increment H++, delta increment Stage 4 — Hindley-Rosen route).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_par_reduces_d_conf(&mut self) -> Result<(), SpecError> {
        self.add_delta_step_app_factoring()?;
        self.add_par_strong_join_d()?;
        self.add_par_strong_join_d_congruences()?;
        self.add_delta_strips_semi_strip_of_strong()?;
        self.add_delta_cong_star_diamond_of_strong()?;
        Ok(())
    }

    /// Brick 0: the head-δ app-factoring substrate. A head-δ step on `app f arg`
    /// factors through a head-δ step on `f` (the head const of the whole spine IS
    /// the head const of `f`; the reduct re-applies the spine, whose last slot is the
    /// untouched `arg`). The single-step strong diamond of `delta_cong` consumes these
    /// in its (here, app_f)/(here, app_a) overlap cases, where a `here` step on an app
    /// node must be reconciled with a congruence step inside the function.
    ///
    ///   - `delta_reduct_app_eq` — the reduct factors: `apply_spine (kapp_args (app f x))
    ///     val = app (apply_spine (kapp_args f) val) x` (kapp_args_app + apply_spine_snoc).
    ///   - `delta_step_app_cong` — forward: `delta_step f f0 → delta_step (app f x)
    ///     (app f0 x)` (mirror of delta_lift_commutes, UNCONDITIONAL: app changes
    ///     neither the env nor the spine head's lookups).
    ///   - `delta_step_app_inv` — inverse (CPS): `delta_step (app f arg) b → ∃ f0,
    ///     delta_step f f0 ∧ b = app f0 arg`.
    fn add_delta_step_app_factoring(&mut self) -> Result<(), SpecError> {
        // delta_reduct_app_eq: the reduct of a head-δ on `app f x` is `app (reduct of
        // f) x`. apply_spine (kapp_args (app f x)) val = apply_spine (append (kapp_args
        // f) [x]) val = app (apply_spine (kapp_args f) val) x. Via kapp_args_app +
        // apply_spine_snoc.
        self.add_definition(SpecDefinition {
            name: "delta_reduct_app_eq".to_string(),
            type_src: concat!(
                "forall (f : KExpr) (x : KExpr) (val : KExpr), ",
                "Eq KExpr (apply_spine (kapp_args (KExpr.app f x)) val) ",
                "(KExpr.app (apply_spine (kapp_args f) val) x)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (f : KExpr) (x : KExpr) (val : KExpr) => ",
                    "Eq.trans KExpr ",
                    "(apply_spine (kapp_args (KExpr.app f x)) val) ",
                    "(apply_spine (list_append (kapp_args f) (ListType.cons KExpr x (ListType.nil KExpr))) val) ",
                    "(KExpr.app (apply_spine (kapp_args f) val) x) ",
                    "(Eq.cong (ListType KExpr) KExpr (fun (L : ListType KExpr) => apply_spine L val) ",
                    "(kapp_args (KExpr.app f x)) ",
                    "(list_append (kapp_args f) (ListType.cons KExpr x (ListType.nil KExpr))) ",
                    "(kapp_args_app f x)) ",
                    "(apply_spine_snoc (kapp_args f) x val)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The reduct of a head-δ on `app f x` factors: apply_spine (kapp_args (app f x)) val = ",
                "app (apply_spine (kapp_args f) val) x. Composes kapp_args_app (kapp_args (app f x) = ",
                "append (kapp_args f) [x]) with apply_spine_snoc (apply_spine of a snoc-ed spine is an outer ",
                "app). DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "apply_spine".to_string(),
                "kapp_args".to_string(),
                "kapp_args_app".to_string(),
                "apply_spine_snoc".to_string(),
                "list_append".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // delta_step_app_cong: a head-δ step on `f` lifts to a head-δ step on `app f x`
        // (keeping x). Mirror of delta_lift_commutes: invert via delta_reduct_some_inv,
        // reconstruct via opt_bind_some_intro 2× — head-const lookup survives app
        // (kapp_fn_app), def-value lookup unchanged (same env), reduct slot closed by
        // delta_reduct_app_eq. UNCONDITIONAL (app changes nothing the lookups depend on).
        {
            let ax = "(KExpr.app f x)";
            let af0x = "(KExpr.app f0 x)";
            let f2 = format!(
                "(fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args {ax}) val))"
            );
            let f1 =
                format!("(fun (dname : Name) => opt_bind KExpr KExpr (defval_for env dname) {f2})");
            // Level-1 app-side head lookup: const-name survives app (kapp_fn_app).
            let h1a = format!(
                "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn {ax})) (kexpr_const_name (kapp_fn f)) (OptionType.some Name dname) \
                 (Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) (kapp_fn {ax}) (kapp_fn f) (kapp_fn_app f x)) \
                 h1)"
            );
            // Level-2: some (apply_spine (kapp_args (app f x)) val) = some (app f0 x).
            // reduct factors (delta_reduct_app_eq) then app-congs the f0-equation (h2r).
            let hf2 = format!(
                "(Eq.cong KExpr (OptionType KExpr) (fun (X : KExpr) => OptionType.some KExpr X) \
                 (apply_spine (kapp_args {ax}) val) {af0x} \
                 (Eq.trans KExpr (apply_spine (kapp_args {ax}) val) (KExpr.app (apply_spine (kapp_args f) val) x) {af0x} \
                 (delta_reduct_app_eq f x val) \
                 (Eq.cong KExpr KExpr (fun (Y : KExpr) => KExpr.app Y x) (apply_spine (kapp_args f) val) f0 \
                 (option_some_inj KExpr (apply_spine (kapp_args f) val) f0 h2r))))"
            );
            let recon = format!(
                "opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn {ax})) {f1} dname {af0x} {h1a} \
                 (opt_bind_some_intro KExpr KExpr (defval_for env dname) {f2} val {af0x} h2 {hf2})"
            );
            let kont = format!(
                "(fun (dname : Name) (val : KExpr) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name dname)) \
                 (h2 : Eq (OptionType KExpr) (defval_for env dname) (OptionType.some KExpr val)) \
                 (h2r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (kapp_args f) val)) (OptionType.some KExpr f0)) => \
                 {recon})"
            );
            let goal_c = format!(
                "(Eq (OptionType KExpr) (delta_reduct env {ax}) (OptionType.some KExpr {af0x}))"
            );
            let value = format!(
                "fun (env : DefEnv) (f : KExpr) (f0 : KExpr) (x : KExpr) \
                 (h : Eq (OptionType KExpr) (delta_reduct env f) (OptionType.some KExpr f0)) => \
                 delta_reduct_some_inv env f f0 {goal_c} h {kont}"
            );
            self.add_definition(SpecDefinition {
                name: "delta_step_app_cong".to_string(),
                type_src: concat!(
                    "forall (env : DefEnv) (f : KExpr) (f0 : KExpr) (x : KExpr), ",
                    "delta_step env f f0 -> delta_step env (KExpr.app f x) (KExpr.app f0 x)"
                )
                .to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: concat!(
                    "Forward app-congruence of head-δ: delta_step env f f0 implies delta_step env (app f x) ",
                    "(app f0 x). Mirror of delta_lift_commutes — invert via delta_reduct_some_inv, reconstruct ",
                    "via opt_bind_some_intro 2× (head-const lookup survives app via kapp_fn_app, def-value lookup ",
                    "unchanged, reduct slot closed by delta_reduct_app_eq). UNCONDITIONAL. DerivedProved, zero ",
                    "axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4)."
                )
                .to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "delta_step".to_string(),
                    "delta_reduct".to_string(),
                    "delta_reduct_some_inv".to_string(),
                    "delta_reduct_app_eq".to_string(),
                    "opt_bind_some_intro".to_string(),
                    "kapp_fn_app".to_string(),
                    "kexpr_const_name".to_string(),
                    "option_some_inj".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // delta_step_app_inv: CPS inverse of delta_step_app_cong. A head-δ on `app f
        // arg` factors through a head-δ on `f`: from delta_step env (app f arg) b,
        // recover f0 = apply_spine (kapp_args f) val with delta_step env f f0 and
        // b = app f0 arg. Invert via delta_reduct_some_inv (recovering dname/val), then
        // reconstruct delta_step env f f0 (opt_bind_some_intro 2×, reduct slot Eq.refl)
        // and b = app f0 arg (option_some_inj h2r + delta_reduct_app_eq).
        {
            let afa = "(KExpr.app f arg)";
            let f0v = "(apply_spine (kapp_args f) val)";
            let f2f =
                "(fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args f) val))"
                    .to_string();
            let f1f = format!(
                "(fun (dname : Name) => opt_bind KExpr KExpr (defval_for env dname) {f2f})"
            );
            // head lookup on f from the app-head lookup (kapp_fn_app, symm).
            let h1f = format!(
                "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn f)) (kexpr_const_name (kapp_fn {afa})) (OptionType.some Name dname) \
                 (Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) (kapp_fn f) (kapp_fn {afa}) \
                 (Eq.symm KExpr (kapp_fn {afa}) (kapp_fn f) (kapp_fn_app f arg))) \
                 h1)"
            );
            // reduct slot on f is Eq.refl (f0 := apply_spine (kapp_args f) val).
            let hf2f = format!("(Eq.refl (OptionType KExpr) (OptionType.some KExpr {f0v}))");
            let reduct_f = format!(
                "opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn f)) {f1f} dname {f0v} {h1f} \
                 (opt_bind_some_intro KExpr KExpr (defval_for env dname) {f2f} val {f0v} h2 {hf2f})"
            );
            // b = app f0 arg : b = apply_spine (kapp_args (app f arg)) val = app f0 arg.
            let beq = format!(
                "(Eq.trans KExpr b (apply_spine (kapp_args {afa}) val) (KExpr.app {f0v} arg) \
                 (Eq.symm KExpr (apply_spine (kapp_args {afa}) val) b \
                 (option_some_inj KExpr (apply_spine (kapp_args {afa}) val) b h2r)) \
                 (delta_reduct_app_eq f arg val))"
            );
            let kont = format!(
                "(fun (dname : Name) (val : KExpr) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn {afa})) (OptionType.some Name dname)) \
                 (h2 : Eq (OptionType KExpr) (defval_for env dname) (OptionType.some KExpr val)) \
                 (h2r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (kapp_args {afa}) val)) (OptionType.some KExpr b)) => \
                 k {f0v} ({reduct_f}) ({beq}))"
            );
            let value = format!(
                "fun (env : DefEnv) (f : KExpr) (arg : KExpr) (b : KExpr) (C : Prop) \
                 (h : Eq (OptionType KExpr) (delta_reduct env {afa}) (OptionType.some KExpr b)) \
                 (k : forall (f0 : KExpr), delta_step env f f0 -> Eq KExpr b (KExpr.app f0 arg) -> C) => \
                 delta_reduct_some_inv env {afa} b C h {kont}"
            );
            self.add_definition(SpecDefinition {
                name: "delta_step_app_inv".to_string(),
                type_src: concat!(
                    "forall (env : DefEnv) (f : KExpr) (arg : KExpr) (b : KExpr) (C : Prop), ",
                    "delta_step env (KExpr.app f arg) b -> ",
                    "(forall (f0 : KExpr), delta_step env f f0 -> Eq KExpr b (KExpr.app f0 arg) -> C) -> C"
                )
                .to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: concat!(
                    "CPS inverse of delta_step_app_cong: a head-δ on `app f arg` factors through a head-δ on `f`. ",
                    "From delta_step env (app f arg) b, recover f0 = apply_spine (kapp_args f) val with ",
                    "delta_step env f f0 and b = app f0 arg, delivered to a continuation. Inverts via ",
                    "delta_reduct_some_inv, reconstructs delta_step env f f0 (opt_bind_some_intro 2×, reduct slot ",
                    "Eq.refl) and the reduct equation (option_some_inj + delta_reduct_app_eq). The (here, app) ",
                    "overlap discharger for the single-step strong diamond. DerivedProved, zero axiom_deps. Part ",
                    "of #2859 (Increment H++, delta increment Stage 4)."
                )
                .to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "delta_step".to_string(),
                    "delta_reduct".to_string(),
                    "delta_reduct_some_inv".to_string(),
                    "delta_reduct_app_eq".to_string(),
                    "opt_bind_some_intro".to_string(),
                    "kapp_fn_app".to_string(),
                    "kexpr_const_name".to_string(),
                    "option_some_inj".to_string(),
                    "Eq.refl".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        Ok(())
    }

    /// Brick 1b: the nine `par_strong_join_d` congruence lifts — a strong-confluence
    /// join on a subterm lifts to a join on the compound term with the other subterm(s)
    /// fixed. Each maps the `zero`/`one` ctor through the matching `delta_cong_star`
    /// congruence (`delta_cong_star_{app,lam,pi,let}`, with reflexive companions on the
    /// fixed subterms) for the star b-leg and the matching single-position `delta_cong`
    /// congruence ctor (`delta_cong.{app_f,app_a,lam_t,lam_b,pi_d,pi_b,let_t,let_v,let_b}`)
    /// for the ≤ 1 c-leg. The substrate the single-step strong diamond of `delta_cong`
    /// uses to lift its subterm IH joins through KExpr's compound ctors (app/lam/pi
    /// two-slot; the genuine let_ three-slot, with TWO fixed binders per lift).
    fn add_par_strong_join_d_congruences(&mut self) -> Result<(), SpecError> {
        // (name, head ctor, star congruence, single-position congruence,
        //  vary_first?, fixed binder name)
        for (name, head, star_cong, single_cong, vary_first, fixed) in [
            (
                "par_strong_join_d_app_f",
                "KExpr.app",
                "delta_cong_star_app",
                "delta_cong.app_f",
                true,
                "arg",
            ),
            (
                "par_strong_join_d_app_a",
                "KExpr.app",
                "delta_cong_star_app",
                "delta_cong.app_a",
                false,
                "f",
            ),
            (
                "par_strong_join_d_lam_t",
                "KExpr.lam",
                "delta_cong_star_lam",
                "delta_cong.lam_t",
                true,
                "body",
            ),
            (
                "par_strong_join_d_lam_b",
                "KExpr.lam",
                "delta_cong_star_lam",
                "delta_cong.lam_b",
                false,
                "ty",
            ),
            (
                "par_strong_join_d_pi_d",
                "KExpr.pi",
                "delta_cong_star_pi",
                "delta_cong.pi_d",
                true,
                "body",
            ),
            (
                "par_strong_join_d_pi_b",
                "KExpr.pi",
                "delta_cong_star_pi",
                "delta_cong.pi_b",
                false,
                "dom",
            ),
        ] {
            // wrap(x): the compound term with x in the varying slot, `fixed` in the
            // other; star_args/single_args: arg order (varying slot first or second).
            let wrap = |x: &str| {
                if vary_first {
                    format!("({head} {x} {fixed})")
                } else {
                    format!("({head} {fixed} {x})")
                }
            };
            // delta_cong_star env (wrap A) (wrap B) from hAB : delta_cong_star env A B.
            let star_call = |a: &str, b: &str, hab: &str| {
                if vary_first {
                    format!(
                        "({star_cong} env {a} {b} {fixed} {fixed} {hab} (delta_cong_star.refl env {fixed}))"
                    )
                } else {
                    format!(
                        "({star_cong} env {fixed} {fixed} {a} {b} (delta_cong_star.refl env {fixed}) {hab})"
                    )
                }
            };
            // delta_cong env (wrap C) (wrap D) from hcd : delta_cong env C D.
            let single_call = |c: &str, d: &str, hcd: &str| {
                if vary_first {
                    format!("({single_cong} env {c} {d} {fixed} {hcd})")
                } else {
                    format!("({single_cong} env {fixed} {c} {d} {hcd})")
                }
            };
            let type_src = format!(
                "forall (env : RedEnv) (u0 : KExpr) (u1 : KExpr) ({fixed} : KExpr), \
                 par_strong_join_d env u0 u1 -> \
                 par_strong_join_d env {wrap_u0} {wrap_u1}",
                wrap_u0 = wrap("u0"),
                wrap_u1 = wrap("u1"),
            );
            let value_src = format!(
                "fun (env : RedEnv) (u0 : KExpr) (u1 : KExpr) ({fixed} : KExpr) \
                 (h : par_strong_join_d env u0 u1) => \
                 @par_strong_join_d.rec env u0 u1 \
                 (fun (_w : par_strong_join_d env u0 u1) => \
                 par_strong_join_d env {wrap_u0} {wrap_u1}) \
                 (fun (hz : delta_cong_star env u0 u1) => \
                 par_strong_join_d.zero env {wrap_u0} {wrap_u1} {star_zero}) \
                 (fun (dd : KExpr) (hbd : delta_cong_star env u0 dd) (hcd : delta_cong env u1 dd) => \
                 par_strong_join_d.one env {wrap_u0} {wrap_u1} {wrap_dd} {star_one} {single_one}) \
                 h",
                wrap_u0 = wrap("u0"),
                wrap_u1 = wrap("u1"),
                wrap_dd = wrap("dd"),
                star_zero = star_call("u0", "u1", "hz"),
                star_one = star_call("u0", "dd", "hbd"),
                single_one = single_call("u1", "dd", "hcd"),
            );
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src,
                value_src: Some(value_src),
                is_axiom: false,
                description: format!(
                    "par_strong_join_d congruence lift through {head} (fixed {fixed}): a strong-confluence \
                     join on a subterm lifts to a join on the compound term. par_strong_join_d.rec maps zero \
                     via {star_cong} (refl on {fixed}) and one via {star_cong} + {single_cong}. The substrate \
                     the single-step strong diamond of delta_cong uses to lift subterm IH joins. DerivedProved, \
                     zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4)."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_strong_join_d".to_string(),
                    "par_strong_join_d.rec".to_string(),
                    "par_strong_join_d.zero".to_string(),
                    "par_strong_join_d.one".to_string(),
                    "delta_cong".to_string(),
                    "delta_cong_star".to_string(),
                    "delta_cong_star.refl".to_string(),
                    star_cong.to_string(),
                    single_cong.to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // par_strong_join_d_proj: the single-hole congruence lift through KExpr.proj
        // (no fixed binder). par_strong_join_d.rec maps zero via delta_cong_star_proj
        // and one via delta_cong_star_proj + delta_cong.proj_s. Part of the proj/lit rung.
        self.add_definition(SpecDefinition {
            name: "par_strong_join_d_proj".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (s : Name) (i : Nat) (u0 : KExpr) (u1 : KExpr), ",
                "par_strong_join_d env u0 u1 -> ",
                "par_strong_join_d env (KExpr.proj s i u0) (KExpr.proj s i u1)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (s : Name) (i : Nat) (u0 : KExpr) (u1 : KExpr) ",
                    "(h : par_strong_join_d env u0 u1) => ",
                    "@par_strong_join_d.rec env u0 u1 ",
                    "(fun (_w : par_strong_join_d env u0 u1) => ",
                    "par_strong_join_d env (KExpr.proj s i u0) (KExpr.proj s i u1)) ",
                    "(fun (hz : delta_cong_star env u0 u1) => ",
                    "par_strong_join_d.zero env (KExpr.proj s i u0) (KExpr.proj s i u1) ",
                    "(delta_cong_star_proj env s i u0 u1 hz)) ",
                    "(fun (dd : KExpr) (hbd : delta_cong_star env u0 dd) (hcd : delta_cong env u1 dd) => ",
                    "par_strong_join_d.one env (KExpr.proj s i u0) (KExpr.proj s i u1) (KExpr.proj s i dd) ",
                    "(delta_cong_star_proj env s i u0 dd hbd) ",
                    "(delta_cong.proj_s env s i u1 dd hcd)) ",
                    "h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "par_strong_join_d single-hole congruence lift through KExpr.proj: a strong-confluence join on the scrutinee lifts to a join on the projection. par_strong_join_d.rec maps zero via delta_cong_star_proj and one via delta_cong_star_proj + delta_cong.proj_s. DerivedProved, zero axiom_deps. Part of the proj/lit fragment rung.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_strong_join_d".to_string(),
                "par_strong_join_d.rec".to_string(),
                "par_strong_join_d.zero".to_string(),
                "par_strong_join_d.one".to_string(),
                "delta_cong".to_string(),
                "delta_cong.proj_s".to_string(),
                "delta_cong_star".to_string(),
                "delta_cong_star_proj".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // The three let_ congruence lifts (genuine three-slot ctor): same
        // par_strong_join_d.rec shape but with TWO fixed binders; the star b-leg goes
        // through delta_cong_star_let (reflexive companions on both fixed slots), the
        // ≤ 1 c-leg through the matching delta_cong.let_{t,v,b} ctor.
        for (name, single_cong, slot) in [
            ("par_strong_join_d_let_t", "delta_cong.let_t", 0usize),
            ("par_strong_join_d_let_v", "delta_cong.let_v", 1usize),
            ("par_strong_join_d_let_b", "delta_cong.let_b", 2usize),
        ] {
            // The two FIXED binder names (the varying slot is u0/u1/dd).
            let (f1, f2) = match slot {
                0 => ("val", "body"),
                1 => ("ty", "body"),
                _ => ("ty", "val"),
            };
            let wrap = |x: &str| match slot {
                0 => format!("(KExpr.let_ {x} {f1} {f2})"),
                1 => format!("(KExpr.let_ {f1} {x} {f2})"),
                _ => format!("(KExpr.let_ {f1} {f2} {x})"),
            };
            // delta_cong_star env (wrap A) (wrap B) from hAB : delta_cong_star env A B,
            // refl on the two fixed slots (delta_cong_star_let arg order: ty ty' val
            // val' body body', then the three star premises in that order).
            let star_call = |a: &str, b: &str, hab: &str| {
                match slot {
                0 => format!(
                    "(delta_cong_star_let env {a} {b} {f1} {f1} {f2} {f2} {hab} (delta_cong_star.refl env {f1}) (delta_cong_star.refl env {f2}))"
                ),
                1 => format!(
                    "(delta_cong_star_let env {f1} {f1} {a} {b} {f2} {f2} (delta_cong_star.refl env {f1}) {hab} (delta_cong_star.refl env {f2}))"
                ),
                _ => format!(
                    "(delta_cong_star_let env {f1} {f1} {f2} {f2} {a} {b} (delta_cong_star.refl env {f1}) (delta_cong_star.refl env {f2}) {hab})"
                ),
            }
            };
            // delta_cong env (wrap C) (wrap D) from hcd : delta_cong env C D
            // (ctor arg orders: let_t (t t' v b), let_v (t v v' b), let_b (t v b b')).
            let single_call = |c: &str, d: &str, hcd: &str| match slot {
                0 => format!("({single_cong} env {c} {d} {f1} {f2} {hcd})"),
                1 => format!("({single_cong} env {f1} {c} {d} {f2} {hcd})"),
                _ => format!("({single_cong} env {f1} {f2} {c} {d} {hcd})"),
            };
            let type_src = format!(
                "forall (env : RedEnv) (u0 : KExpr) (u1 : KExpr) ({f1} : KExpr) ({f2} : KExpr), \
                 par_strong_join_d env u0 u1 -> \
                 par_strong_join_d env {wrap_u0} {wrap_u1}",
                wrap_u0 = wrap("u0"),
                wrap_u1 = wrap("u1"),
            );
            let value_src = format!(
                "fun (env : RedEnv) (u0 : KExpr) (u1 : KExpr) ({f1} : KExpr) ({f2} : KExpr) \
                 (h : par_strong_join_d env u0 u1) => \
                 @par_strong_join_d.rec env u0 u1 \
                 (fun (_w : par_strong_join_d env u0 u1) => \
                 par_strong_join_d env {wrap_u0} {wrap_u1}) \
                 (fun (hz : delta_cong_star env u0 u1) => \
                 par_strong_join_d.zero env {wrap_u0} {wrap_u1} {star_zero}) \
                 (fun (dd : KExpr) (hbd : delta_cong_star env u0 dd) (hcd : delta_cong env u1 dd) => \
                 par_strong_join_d.one env {wrap_u0} {wrap_u1} {wrap_dd} {star_one} {single_one}) \
                 h",
                wrap_u0 = wrap("u0"),
                wrap_u1 = wrap("u1"),
                wrap_dd = wrap("dd"),
                star_zero = star_call("u0", "u1", "hz"),
                star_one = star_call("u0", "dd", "hbd"),
                single_one = single_call("u1", "dd", "hcd"),
            );
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src,
                value_src: Some(value_src),
                is_axiom: false,
                description: format!(
                    "par_strong_join_d congruence lift through the genuine KExpr.let_ ctor (fixed {f1}/{f2}): a \
                     strong-confluence join on a let component lifts to a join on the let term. \
                     par_strong_join_d.rec maps zero via delta_cong_star_let (refl on the fixed slots) and one \
                     via delta_cong_star_let + {single_cong}. The substrate the single-step strong diamond of \
                     delta_cong uses to lift subterm IH joins through let_ nodes. DerivedProved, zero \
                     axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4)."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_strong_join_d".to_string(),
                    "par_strong_join_d.rec".to_string(),
                    "par_strong_join_d.zero".to_string(),
                    "par_strong_join_d.one".to_string(),
                    "delta_cong".to_string(),
                    "delta_cong_star".to_string(),
                    "delta_cong_star.refl".to_string(),
                    "delta_cong_star_let".to_string(),
                    single_cong.to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }
        Ok(())
    }

    /// Brick 1: the Huet strong-confluence join witness `par_strong_join_d` — the
    /// b-leg is an unbounded `delta_cong_star` reduction, the c-leg is BOUNDED to
    /// ≤ 1 step, encoded as the constructor choice (`zero` = meet at c, b ⇒* c;
    /// `one` = single c ⇒ d, b ⇒* d). Both ctors land at the SAME indices (b, c),
    /// so the recursor needs no cross-constructor index unification. The asymmetry
    /// (one bounded leg) is what makes the strip/confluence induction terminate;
    /// the symmetric `par_strips_witness_d_star` is only WCR. Mirror of
    /// `par_strong_join_c`.
    fn add_par_strong_join_d(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            r"inductive par_strong_join_d (env : RedEnv) : KExpr → KExpr → Type
| zero : forall (b : KExpr) (c : KExpr), delta_cong_star env b c → par_strong_join_d env b c
| one : forall (b : KExpr) (c : KExpr) (d : KExpr), delta_cong_star env b d → delta_cong env c d → par_strong_join_d env b c",
            "par_strong_join_d env b c is the Huet strong-confluence join witness for delta_cong: the \
             b-leg is an unbounded delta_cong_star reduction and the c-leg is BOUNDED to ≤ 1 step, \
             encoded as the constructor choice — zero (meet at c, b ⇒* c) or one (single c ⇒ d, b ⇒* d). \
             The output shape of strong confluence; strictly stronger than the symmetric (WCR-only) \
             par_strips_witness_d_star. The δ mirror of par_strong_join_c. Part of #2859 (Increment H++, \
             delta increment Stage 4, strong-confluence tiling).",
        )?;
        Ok(())
    }

    /// Brick 2: the SEMI-STRIP lemma of the δ strong-confluence tiling (abstract
    /// `strong_semi_strip`). Given a strong-confluence hypothesis `SC` for
    /// `delta_cong`, a multi-step reduction `a ⇒* c` and a single step `a ⇒ b` join
    /// via `par_strips_witness_d_star`. Induction on the star leg `a ⇒* c`
    /// (`delta_cong_star.rec`); the step arm feeds the two single head steps through
    /// `SC`, then case-splits the BOUNDED leg via `par_strong_join_d.rec` (`zero`
    /// short-circuits to the tail, `one` feeds its one step into the IH). The ≤ 1-step
    /// c-leg of strong confluence is exactly what makes the induction terminate.
    /// Parameterized on `SC` — zero new axioms. Mirror of
    /// `par_strips_c_semi_strip_of_strong`.
    fn add_delta_strips_semi_strip_of_strong(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "delta_strips_semi_strip_of_strong".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) ",
                "(SC : forall (a : KExpr) (b : KExpr) (c : KExpr), ",
                "delta_cong env a b -> delta_cong env a c -> par_strong_join_d env b c) ",
                "(a : KExpr) (c : KExpr), ",
                "delta_cong_star env a c -> ",
                "forall (b : KExpr), delta_cong env a b -> par_strips_witness_d_star env b c"
            )
            .to_string(),
            value_src: Some(delta_strips_semi_strip_of_strong_proof()),
            is_axiom: false,
            description: concat!(
                "The SEMI-STRIP lemma of the Huet strong-confluence tiling for δ (abstract strong_semi_strip): ",
                "under a strong-confluence hypothesis SC for delta_cong, a multi-step a ⇒* c and a single step ",
                "a ⇒ b join via par_strips_witness_d_star. Induction on the star leg via delta_cong_star.rec; ",
                "the step arm pushes both single steps through SC and case-splits the BOUNDED leg via ",
                "par_strong_join_d.rec (zero short-circuits, one feeds the IH). Parameterized on SC (a bound ",
                "hypothesis, NOT a registered axiom), so the closure is genuinely zero-axiom. The δ mirror of ",
                "par_strips_c_semi_strip_of_strong. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, \
                 delta increment Stage 4, strong-confluence tiling)."
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
                "delta_cong_subsumes_star".to_string(),
                "par_strong_join_d".to_string(),
                "par_strong_join_d.rec".to_string(),
                "par_strips_witness_d_star".to_string(),
                "par_strips_witness_d_star.intro".to_string(),
                "par_strips_witness_d_star.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Brick 3: THE TILING BRICK (abstract `strong_confluent`). Given a strong-
    /// confluence hypothesis `SC` for `delta_cong`, the reflexive-transitive closure
    /// `delta_cong_star` is CHURCH-ROSSER: any two multi-step reductions `e ⇒* e1`,
    /// `e ⇒* e2` join via `par_strips_witness_d_star`. Induction on the first star leg
    /// `e ⇒* e1` (`delta_cong_star.rec`, motive generalized over the second leg); each
    /// head step is stripped against the second leg via
    /// `delta_strips_semi_strip_of_strong`, the IH joins the residuals, re-closed with
    /// `delta_cong_star_trans`. Lands the Huet strong-confluence ⟹ Church-Rosser tiling
    /// 0-axiom and ISOLATES the remaining δ-confluence obligation to exactly `SC` (the
    /// single-step strong diamond of `delta_cong`). Mirror of
    /// `par_reduces_c_star_diamond_of_strong`.
    fn add_delta_cong_star_diamond_of_strong(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "delta_cong_star_diamond_of_strong".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) ",
                "(SC : forall (a : KExpr) (b : KExpr) (c : KExpr), ",
                "delta_cong env a b -> delta_cong env a c -> par_strong_join_d env b c) ",
                "(e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "delta_cong_star env e e1 -> delta_cong_star env e e2 -> ",
                "par_strips_witness_d_star env e1 e2"
            )
            .to_string(),
            value_src: Some(delta_cong_star_diamond_of_strong_proof()),
            is_axiom: false,
            description: concat!(
                "THE δ TILING BRICK (abstract strong_confluent): under a strong-confluence hypothesis SC for ",
                "delta_cong, delta_cong_star is Church-Rosser. Induction on the first star leg via ",
                "delta_cong_star.rec (motive generalized over the second leg); each head step is stripped ",
                "against the second leg by delta_strips_semi_strip_of_strong, the IH joins the residuals, and ",
                "delta_cong_star_trans re-closes. Lands the Huet strong-confluence ⟹ Church-Rosser tiling for δ ",
                "0-axiom and ISOLATES the remaining δ-confluence obligation to exactly SC (the single-step strong ",
                "diamond of delta_cong). SC is a bound parameter, not a registered axiom, so the closure is ",
                "genuinely zero-axiom. The δ mirror of par_reduces_c_star_diamond_of_strong. DerivedProved, zero ",
                "axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4, strong-confluence tiling)."
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
                "par_strong_join_d".to_string(),
                "delta_strips_semi_strip_of_strong".to_string(),
                "par_strips_witness_d_star".to_string(),
                "par_strips_witness_d_star.intro".to_string(),
                "par_strips_witness_d_star.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }
}

/// Closed proof term for `delta_strips_semi_strip_of_strong` — the SEMI-STRIP of
/// the δ strong-confluence tiling. Verbatim δ mirror of
/// `par_strips_c_semi_strip_of_strong_proof`.
fn delta_strips_semi_strip_of_strong_proof() -> String {
    // The strong-confluence hypothesis type (matches the lemma's SC binder).
    let sc_ty = concat!(
        "(forall (a : KExpr) (b : KExpr) (c : KExpr), ",
        "delta_cong env a b -> delta_cong env a c -> par_strong_join_d env b c)"
    );
    // Outer recursor motive over the star leg x =>* y (motive abstracts indices).
    let motive = concat!(
        "(fun (x : KExpr) (y : KExpr) (_h : delta_cong_star env x y) => ",
        "forall (b : KExpr), delta_cong env x b -> par_strips_witness_d_star env b y)"
    );
    // refl arm (x = y = r): strip a single step r => b, meet at b.
    let refl_arm = concat!(
        "(fun (r : KExpr) => ",
        "fun (b : KExpr) (hrb : delta_cong env r b) => ",
        "par_strips_witness_d_star.intro env b r b ",
        "(delta_cong_star.refl env b) ",
        "(delta_cong_subsumes_star env r b hrb))"
    );
    // step arm: head x => x1, tail x1 =>* y, ih on the tail. Strip a single x => b.
    // SC joins the two head steps at par_strong_join_d env b x1 (b-leg star, x1-leg
    // <= 1). Eliminate it indices-first (@-recursor), motive over the major only.
    let join_motive =
        "(fun (_w : par_strong_join_d env b x1) => par_strips_witness_d_star env b y)";
    // zero arm: the x1-leg took ZERO steps, so b =>* x1 (the meet is x1). Compose
    // with the tail x1 =>* y to land b =>* y; meet at y (no IH needed).
    let zero_arm = concat!(
        "(fun (hbx1 : delta_cong_star env b x1) => ",
        "par_strips_witness_d_star.intro env b y y ",
        "(delta_cong_star_trans env b x1 y hbx1 htail) ",
        "(delta_cong_star.refl env y))"
    );
    // one arm: the x1-leg took ONE step x1 => d, with b =>* d. Feed d into the IH
    // (a single step x1 => d), project the witness, close the b-side via b =>* d =>* m2.
    let one_arm = concat!(
        "(fun (d : KExpr) (hbd : delta_cong_star env b d) (hx1d : delta_cong env x1 d) => ",
        "@par_strips_witness_d_star.rec env d y ",
        "(fun (_w : par_strips_witness_d_star env d y) => par_strips_witness_d_star env b y) ",
        "(fun (m2 : KExpr) (hdm2 : delta_cong_star env d m2) (hym2 : delta_cong_star env y m2) => ",
        "par_strips_witness_d_star.intro env b y m2 ",
        "(delta_cong_star_trans env b d m2 hbd hdm2) ",
        "hym2) ",
        "(ih d hx1d))"
    );
    let step_arm = format!(
        concat!(
            "(fun (x : KExpr) (x1 : KExpr) (y : KExpr) ",
            "(hstep : delta_cong env x x1) ",
            "(htail : delta_cong_star env x1 y) ",
            "(ih : forall (b : KExpr), delta_cong env x1 b -> par_strips_witness_d_star env b y) => ",
            "fun (b : KExpr) (hxb : delta_cong env x b) => ",
            "@par_strong_join_d.rec env b x1 {join_motive} {zero_arm} {one_arm} ",
            "(SC x b x1 hxb hstep))"
        ),
        join_motive = join_motive,
        zero_arm = zero_arm,
        one_arm = one_arm,
    );
    format!(
        concat!(
            "fun (env : RedEnv) (SC : {sc_ty}) (a : KExpr) (c : KExpr) ",
            "(hac : delta_cong_star env a c) => ",
            "delta_cong_star.rec env {motive} {refl_arm} {step_arm} a c hac"
        ),
        sc_ty = sc_ty,
        motive = motive,
        refl_arm = refl_arm,
        step_arm = step_arm,
    )
}

/// Closed proof term for `delta_cong_star_diamond_of_strong` — THE δ TILING BRICK
/// (abstract `strong_confluent`). Verbatim δ mirror of
/// `par_reduces_c_star_diamond_of_strong_proof`.
fn delta_cong_star_diamond_of_strong_proof() -> String {
    // The strong-confluence hypothesis type (matches the lemma's SC binder).
    let sc_ty = concat!(
        "(forall (a : KExpr) (b : KExpr) (c : KExpr), ",
        "delta_cong env a b -> delta_cong env a c -> par_strong_join_d env b c)"
    );
    // Outer recursor motive over the first star leg x =>* y (abstracts indices).
    let motive = concat!(
        "(fun (x : KExpr) (y : KExpr) (_h : delta_cong_star env x y) => ",
        "forall (z : KExpr), delta_cong_star env x z -> par_strips_witness_d_star env y z)"
    );
    // refl arm (x = y = r): the first leg is empty, so meet at z (r =>* z given).
    let refl_arm = concat!(
        "(fun (r : KExpr) => ",
        "fun (z : KExpr) (hrz : delta_cong_star env r z) => ",
        "par_strips_witness_d_star.intro env r z z hrz ",
        "(delta_cong_star.refl env z))"
    );
    // step arm: head x => x1, tail x1 =>* y, ih on the tail. Strip x => x1 from the
    // z-leg x =>* z via the semi-strip, then recurse and re-close.
    let star_proj = concat!(
        "(@par_strips_witness_d_star.rec env y m1 ",
        "(fun (_w : par_strips_witness_d_star env y m1) => par_strips_witness_d_star env y z) ",
        "(fun (m2 : KExpr) (hym2 : delta_cong_star env y m2) (hm1m2 : delta_cong_star env m1 m2) => ",
        "par_strips_witness_d_star.intro env y z m2 hym2 ",
        "(delta_cong_star_trans env z m1 m2 hzm1 hm1m2)) ",
        "(ih m1 hx1m1))"
    );
    let semi_proj = format!(
        concat!(
            "(@par_strips_witness_d_star.rec env x1 z ",
            "(fun (_w : par_strips_witness_d_star env x1 z) => par_strips_witness_d_star env y z) ",
            "(fun (m1 : KExpr) (hx1m1 : delta_cong_star env x1 m1) (hzm1 : delta_cong_star env z m1) => ",
            "{star_proj}) ",
            "(delta_strips_semi_strip_of_strong env SC x z hxz x1 hstep))"
        ),
        star_proj = star_proj,
    );
    let step_arm = format!(
        concat!(
            "(fun (x : KExpr) (x1 : KExpr) (y : KExpr) ",
            "(hstep : delta_cong env x x1) ",
            "(htail : delta_cong_star env x1 y) ",
            "(ih : forall (z : KExpr), delta_cong_star env x1 z -> par_strips_witness_d_star env y z) => ",
            "fun (z : KExpr) (hxz : delta_cong_star env x z) => ",
            "{semi_proj})"
        ),
        semi_proj = semi_proj,
    );
    format!(
        concat!(
            "fun (env : RedEnv) (SC : {sc_ty}) (e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
            "(h1 : delta_cong_star env e e1) (h2 : delta_cong_star env e e2) => ",
            "delta_cong_star.rec env {motive} {refl_arm} {step_arm} e e1 h1 e2 h2"
        ),
        sc_ty = sc_ty,
        motive = motive,
        refl_arm = refl_arm,
        step_arm = step_arm,
    )
}

#[cfg(test)]
#[path = "par_reduces_d_conf_tests.rs"]
mod par_reduces_d_conf_tests;
