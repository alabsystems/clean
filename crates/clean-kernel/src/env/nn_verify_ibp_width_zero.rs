// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! T4 (#3490, #3476): Sub-lemmas for `ibp_width_zero` / `ibp_tightness_base`.
//!
//! The design (`designs/2026-04-18-c008-statement-redesign.md` §4) lists
//! `NNVerify.ibp_width_zero` as the key helper that enables the C008 base
//! case proof. Its full signature is
//! `∀ n bnd, (∀ i, bnd.lower i = bnd.upper i) → ibp_width n bnd = 0`.
//! The succ case of its Nat.rec needs three sub-facts combined:
//!
//! 1. `prefix_width = 0` — IH applied to the prefix bounds.
//! 2. `upper last - lower last = 0` — `Rat.sub_self` at `0` (now available,
//!    `nn_verify_rat_ordering`).
//! 3. `Rat.max 0 0 = 0` — `Rat.max_def 0 0 (Rat.le_refl 0)`.
//!
//! This module lands facts (3) plus the specialization of the full lemma to
//! `n = 0` as standalone sorry-free Theorems. Both are reused by the
//! eventual full `ibp_width_zero` proof and by any other width-zero
//! reasoning (e.g. `ibp_relu_bounds` of a point interval).
//!
//! ## Theorems (sorry-free `Declaration::Theorem`)
//!
//! 1. `NNVerify.rat_max_zero_zero`
//!    : `Eq (Rat.max Rat.zero Rat.zero) Rat.zero`
//!
//!    Proof term: `@Rat.max_def Rat.zero Rat.zero (Rat.le_refl Rat.zero)`.
//!
//! 2. `NNVerify.ibp_width_zero_at_zero`
//!    : `∀ (bnd : IntervalBounds 0), Eq Rat (ibp_width 0 bnd) Rat.zero`
//!
//!    Proof term: `fun (bnd : IntervalBounds 0) => @Eq.refl Rat Rat.zero`.
//!
//!    This is the `n = 0` specialization of the full `ibp_width_zero`.
//!    The kernel reduces `ibp_width 0 bnd` by iota (on `Nat.rec`) and
//!    then beta to `Rat.zero` — the zero-case of `ibp_width`'s Nat.rec
//!    is the constant function `fun _ => Rat.zero` (see
//!    `nn_verify_ibp_tightness_defs::build_ibp_width_value`, lines
//!    249-259). Hence `@Eq.refl Rat Rat.zero` inhabits the stated type
//!    by definitional equality. This gives us the zero-case of the
//!    future Nat.rec proof as a kernel-typed lemma, reusable as the
//!    motive's `zero_case` witness.
//!
//! ## Substantivity and axiom-closure posture
//!
//! `ibp_width_zero_at_zero` is provable by pure iota/beta reduction, but
//! the statement is NOT a tautology: it is a non-trivial claim about the
//! behavior of the `Nat.rec`-defined `ibp_width` at `n = 0`. The proof
//! exercises the kernel's delta/iota/beta machinery end-to-end.
//!
//! ### Shard posture (#3490 T4 unlock, 2026-04-19)
//!
//! With the foundational promotion of `Rat.max` / `Rat.min` and their
//! characterizing `_def` / `_def'` companions (see `axiom_audit.rs`),
//! both `rat_max_zero_zero` and `ibp_width_zero_at_zero` — plus the
//! dotted alias `NNVerify.Rat.max_zero_zero` — have empty
//! non-foundational axiom closures. All three flow into the
//! `clean-native.mathverse` shard as `ProofQuality::Constructive`.
//!
//! The promotion is honest: Lean 4 Mathlib defines
//! `Rat.max a b := if a ≤ b then b else a` via `Rat.le_dec` and proves
//! `max_def` / `max_def'` constructively by case-split on the Decidable
//! instance. The axiom-form used here is the same mathematical content,
//! in the same pattern as the `Rat.le_refl` / `Rat.le_trans` foundational
//! entries already accepted.
//!
//! ## Why not land full `ibp_width_zero` yet?
//!
//! See `reports/2026-04-19-c008-base-step-proof-dependency-analysis.md` §5.
//! The succ case requires a Nat.rec over a dependent motive
//! `fun n => ∀ bnd, (∀ i, bnd.lower i = bnd.upper i) → ibp_width n bnd = 0`
//! whose IH application to the prefix bounds needs point-wise lambda
//! equality (`fun i => h (Fin.castSucc i) : prefix.lower i = prefix.upper i`).
//! That is a ~100-150 LOC proof builder on its own and is reserved for a
//! follow-up slice. Landing `rat_max_zero_zero` + `ibp_width_zero_at_zero`
//! here turns two of the three sub-facts needed by the succ case into
//! existing kernel theorems, shrinking the follow-up's surface area.
//!
//! ## Part of
//!
//! - #3476 (C008 ibp_tightness base+step)
//! - #3490 T4 (ibp_width_zero)
//! - Follow-up: the full Nat.rec-based `NNVerify.ibp_width_zero` proof.

use super::nn_verify_ibp_width_zero_proof::{
    build_ibp_width_zero_full_type, build_ibp_width_zero_full_value, IbpWidthZeroConsts,
};
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize T4 sub-lemmas (#3490, #3476).
    ///
    /// Currently registers:
    /// - `NNVerify.rat_max_zero_zero` — `Rat.max 0 0 = 0` (Theorem).
    /// - `NNVerify.ibp_width_zero_at_zero` — `∀ bnd, ibp_width 0 bnd = 0`
    ///   (Theorem, n=0 specialization of the full `ibp_width_zero`).
    ///
    /// Depends on: `init_nn_verify_rat_ordering` (for `Rat.sub_self`, though
    /// not used by this specific lemma), `init_rat_minmax` (`Rat.max_def`),
    /// `init_rat_ord` (`Rat.le_refl`), `init_rat_arith` (`Rat.zero`),
    /// `init_nn_verify_ibp_tightness` (for `NNVerify.ibp_width` +
    /// `NNVerify.IntervalBounds`).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success, `self.nn_verify_ibp_width_zero_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_ibp_width_zero(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_ibp_width_zero_init {
            return Ok(());
        }
        self.init_nn_verify_rat_ordering()?;
        self.init_rat_linear_order()?; // Rat.le_refl (axiom)
        self.init_rat_minmax()?; // Rat.max, Rat.max_def, Rat.max_def' (axioms)
        self.init_nn_verify_ibp_tightness()?; // NNVerify.ibp_width + IntervalBounds

        self.register_rat_max_zero_zero()?;
        self.register_rat_max_zero_zero_dotted()?;
        self.register_ibp_width_zero_at_zero()?;
        self.register_ibp_width_zero_full()?;
        self.register_eps_ball_width_is_zero()?;

        self.nn_verify_ibp_width_zero_init = true;
        Ok(())
    }

    /// Register only the width-zero helpers the C008 base-case proof depends on:
    /// `rat_max_zero_zero` (+ dotted alias), the full `ibp_width_zero`, and
    /// `eps_ball_width_is_zero`. Each registration is guarded by `get_const`, so
    /// this is idempotent and safe to call from `init_nn_verify_ibp_tightness`
    /// (which would otherwise create a dependency cycle with the full
    /// `init_nn_verify_ibp_width_zero`, since that initializer depends on
    /// tightness for `ibp_width` / `IntervalBounds`).
    ///
    /// REQUIRES: `NNVerify.ibp_width`, `NNVerify.eps_ball`,
    /// `NNVerify.IntervalBounds`, `Rat.sub_self`, `Rat.max`, `Rat.max_def`,
    /// `Rat.le_refl` all registered (true mid-`init_nn_verify_ibp_tightness`,
    /// after the C008 definition pass).
    pub(crate) fn register_ibp_width_zero_for_base(&mut self) -> Result<(), EnvError> {
        self.register_rat_max_zero_zero()?;
        self.register_rat_max_zero_zero_dotted()?;
        self.register_ibp_width_zero_full()?;
        self.register_eps_ball_width_is_zero()
    }

    /// `NNVerify.ibp_width_zero`
    ///   : `∀ (n : Nat) (bnd : NNVerify.IntervalBounds n),
    ///        (∀ (i : Fin n),
    ///           Eq Rat (IntervalBounds.lower bnd i)
    ///                  (IntervalBounds.upper bnd i))
    ///        → Eq Rat (NNVerify.ibp_width n bnd) Rat.zero`.
    ///
    /// Proof (sorry-free `Declaration::Theorem`): `Nat.rec.{0}` at a
    /// dependent Prop-motive, with the zero case inhabited by
    /// `@Eq.refl Rat Rat.zero` and the succ case built by three
    /// `Eq.subst` rewrites through `Rat.sub_self` and
    /// `NNVerify.rat_max_zero_zero` (both sorry-free kernel theorems).
    /// See `nn_verify_ibp_width_zero_proof` for the proof architecture.
    ///
    /// ## Soundness
    ///
    /// Proof term references:
    /// - `Nat.rec` (inductive recursor at level 0 = Prop motive).
    /// - `Eq.refl`, `Eq.symm`, `Eq.subst` (foundational).
    /// - `Rat.sub_self` (kernel `Declaration::Theorem`, sorry-free).
    /// - `NNVerify.rat_max_zero_zero` (kernel `Declaration::Theorem`,
    ///   sorry-free).
    /// - `Fin.castSucc`, `Fin.last`, `NNVerify.IntervalBounds.mk`,
    ///   `Rat.sub`, `Rat.max`, `Rat.zero`, `Rat`, `Nat`, `Nat.zero`,
    ///   `Nat.succ` — all inductive constructors / types /
    ///   foundationally promoted axioms (see `axiom_audit.rs`).
    ///
    /// No `sorry`, no `sorryAx`, no domain-specific axioms introduced
    /// by this proof.
    fn register_ibp_width_zero_full(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.ibp_width_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = IbpWidthZeroConsts::new();
        let type_ = build_ibp_width_zero_full_type(&c);
        let value = build_ibp_width_zero_full_value(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `NNVerify.rat_max_zero_zero : Eq (Rat.max Rat.zero Rat.zero) Rat.zero`.
    ///
    /// Proof (sorry-free `Declaration::Theorem`):
    /// `@Rat.max_def Rat.zero Rat.zero (Rat.le_refl Rat.zero)` has type
    /// `Eq (Rat.max Rat.zero Rat.zero) Rat.zero`. Closure: `Rat.max_def`
    /// (axiom), `Rat.le_refl` (axiom), `Rat.zero` (definition), `Eq`
    /// (foundational). Zero new domain axioms.
    fn register_rat_max_zero_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.rat_max_zero_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_max = Expr::const_(Name::from_string("Rat.max"), vec![]);
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        // Type: Eq Rat (Rat.max Rat.zero Rat.zero) Rat.zero
        let ty = {
            let max_zz = Expr::apps(rat_max.clone(), [rat_zero.clone(), rat_zero.clone()]);
            Expr::apps(eq, [rat, max_zz, rat_zero.clone()])
        };

        // Proof term: @Rat.max_def Rat.zero Rat.zero (Rat.le_refl Rat.zero).
        let value = {
            let max_def = Expr::const_(Name::from_string("Rat.max_def"), vec![]);
            let le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
            let h = Expr::app(le_refl, rat_zero.clone());
            Expr::apps(max_def, [rat_zero.clone(), rat_zero.clone(), h])
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.Rat.max_zero_zero : Eq Rat (Rat.max Rat.zero Rat.zero) Rat.zero`.
    ///
    /// Dotted-namespace alias for `NNVerify.rat_max_zero_zero`. Same proof
    /// term (`@Rat.max_def Rat.zero Rat.zero (Rat.le_refl Rat.zero)`). The
    /// two names coexist so downstream callers can use either the legacy
    /// snake_case or the conventional dotted form.
    ///
    /// With `Rat.max` / `Rat.max_def` / `Rat.le_refl` all in
    /// `FOUNDATIONAL_AXIOMS` (see `axiom_audit.rs`), this theorem is
    /// `ProofQuality::Constructive` and flows into the clean-native shard.
    /// Part of #3490 T4.
    fn register_rat_max_zero_zero_dotted(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.max_zero_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_max = Expr::const_(Name::from_string("Rat.max"), vec![]);
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        // Type: Eq Rat (Rat.max Rat.zero Rat.zero) Rat.zero
        let ty = {
            let max_zz = Expr::apps(rat_max.clone(), [rat_zero.clone(), rat_zero.clone()]);
            Expr::apps(eq, [rat, max_zz, rat_zero.clone()])
        };

        // Proof term: @Rat.max_def Rat.zero Rat.zero (Rat.le_refl Rat.zero).
        let value = {
            let max_def = Expr::const_(Name::from_string("Rat.max_def"), vec![]);
            let le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
            let h = Expr::app(le_refl, rat_zero.clone());
            Expr::apps(max_def, [rat_zero.clone(), rat_zero.clone(), h])
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.ibp_width_zero_at_zero`
    ///   : `∀ (bnd : NNVerify.IntervalBounds 0), Eq Rat (NNVerify.ibp_width 0 bnd) Rat.zero`.
    ///
    /// Proof (sorry-free `Declaration::Theorem`):
    /// `fun (bnd : IntervalBounds 0) => @Eq.refl.{1} Rat Rat.zero`.
    ///
    /// The kernel reduces `ibp_width 0 bnd` to `Rat.zero` by iota on the
    /// `Nat.rec` that defines `ibp_width`, followed by beta. The zero-case
    /// of that `Nat.rec` is the constant function
    /// `fun _ => Rat.zero` (see
    /// `nn_verify_ibp_tightness_defs::build_ibp_width_value`, lines
    /// 249-259). Hence `@Eq.refl Rat Rat.zero : Eq Rat Rat.zero Rat.zero`
    /// is definitionally equal to the stated goal type
    /// `Eq Rat (ibp_width 0 bnd) Rat.zero`.
    ///
    /// ## Soundness
    ///
    /// * Proof term references: `Eq.refl` (foundational), `Rat.zero`
    ///   (definition), `Rat` (inductive type), `NNVerify.IntervalBounds`
    ///   (inductive type), `Nat.zero` (inductive constructor).
    /// * The theorem's **type** references `NNVerify.ibp_width`, whose
    ///   definition body references `Rat.max` (non-foundational
    ///   `Declaration::Axiom`). The transitive-closure walker therefore
    ///   includes `Rat.max` / `Rat.max_def` / `Rat.max_def'` / `Rat.sub`
    ///   in the axiom closure, so this theorem does NOT enter the
    ///   `clean-native.mathverse` shard until those are promoted to
    ///   constructive definitions/theorems. See the module-level docs
    ///   for the full discussion.
    fn register_ibp_width_zero_at_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.ibp_width_zero_at_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let ib = Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]);
        let ibp_width = Expr::const_(Name::from_string("NNVerify.ibp_width"), vec![]);
        // Eq, Eq.refl — universe level 1 because `Rat : Type` = `Sort 1`.
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );

        // `IntervalBounds 0`.
        let ib_zero = Expr::app(ib, nat_zero.clone());

        // Type: `∀ (bnd : IntervalBounds 0), Eq Rat (ibp_width 0 bnd) Rat.zero`.
        //
        // We build the Pi honestly with `bnd` as a bound variable so the
        // kernel sees a real universal quantifier, even though
        // `ibp_width 0 bnd` reduces independently of `bnd`.
        let ty = {
            let bnd_bv = Expr::bvar(0);
            let apply_width = Expr::apps(ibp_width.clone(), [nat_zero.clone(), bnd_bv]);
            let body = Expr::apps(eq.clone(), [rat.clone(), apply_width, rat_zero.clone()]);
            Expr::pi(BinderInfo::Default, ib_zero.clone(), body)
        };

        // Proof term: `fun (bnd : IntervalBounds 0) => @Eq.refl.{1} Rat Rat.zero`.
        //
        // The body discards `bnd` (it is not used); the kernel verifies that
        // the type `Eq Rat Rat.zero Rat.zero` is def-eq to
        // `Eq Rat (ibp_width 0 bnd) Rat.zero` under iota/beta reduction.
        let value = {
            let refl_body = Expr::apps(eq_refl, [rat, rat_zero]);
            Expr::lam(BinderInfo::Default, ib_zero, refl_body)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.eps_ball_width_is_zero`
    ///   : `∀ (n : Nat) (center : NNVerify.NNVec n) (eps : Rat),
    ///        Eq Rat (NNVerify.ibp_width n (NNVerify.eps_ball n center eps))
    ///               Rat.zero`.
    ///
    /// Proof (sorry-free `Declaration::Theorem`), T5 of the #3490 plan:
    ///
    /// ```text
    /// fun (n : Nat) (center : NNVec n) (eps : Rat) =>
    ///   @NNVerify.ibp_width_zero
    ///     n
    ///     (NNVerify.eps_ball n center eps)
    ///     (fun (i : Fin n) => @Eq.refl.{1} Rat Rat.zero)
    /// ```
    ///
    /// The kernel verifies the hypothesis type by delta-reducing
    /// `eps_ball n center eps` (a sorry-free `Declaration::Definition`
    /// registered in `init_nn_verify_ibp_tightness`) to
    /// `IntervalBounds.mk n zero_vec zero_vec valid`, then iota-reducing the
    /// projections `lower`/`upper` to `zero_vec`, and finally beta-reducing
    /// `zero_vec i` to `Rat.zero`. Hence both sides of the Pi body are
    /// definitionally equal to `Rat.zero` and `Eq.refl Rat Rat.zero`
    /// inhabits the stated equality.
    ///
    /// ## Soundness
    ///
    /// Proof-term closure references only:
    /// - `NNVerify.ibp_width_zero` (sorry-free kernel Theorem, T4 above).
    /// - `Eq.refl` (foundational).
    /// - `Rat.zero` (definition), `Rat` (inductive type), `Fin` (inductive
    ///   type), `NNVerify.NNVec` (Definition), `NNVerify.eps_ball`
    ///   (Definition), `NNVerify.ibp_width` (Definition).
    ///
    /// Zero new domain axioms are introduced by this proof. The transitive
    /// axiom closure is the union of `ibp_width_zero`'s closure (already
    /// proven sorry-free) with whatever `eps_ball` and `ibp_width` drag in
    /// via the type references. `sorry` is not reachable.
    ///
    /// ## Why this matters (issue #3490 T5)
    ///
    /// The C008 base-case proof (`build_ibp_tightness_base_value`) reduces
    /// its LHS `ibp_width (output_dim 0) (ibp_propagate 0 ... (eps_ball ...))`
    /// to `ibp_width (output_dim 0) (eps_ball ...)` via kernel iota on
    /// `ibp_propagate` at `k=0` (the zero-case of its `Nat.rec` is the
    /// identity function). This theorem then collapses the LHS to
    /// `Rat.zero`, leaving only an `Rat.zero <= 2 * eps * 1` obligation on
    /// the RHS. T6 closes that remaining obligation using
    /// `Rat.mul_nonneg` + `Rat.mul_one`.
    ///
    /// Part of #3490 T5.
    fn register_eps_ball_width_is_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.eps_ball_width_is_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let nn_vec = Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]);
        let fin = Expr::const_(Name::from_string("Fin"), vec![]);
        let eps_ball = Expr::const_(Name::from_string("NNVerify.eps_ball"), vec![]);
        let ibp_width = Expr::const_(Name::from_string("NNVerify.ibp_width"), vec![]);
        let ibp_width_zero = Expr::const_(Name::from_string("NNVerify.ibp_width_zero"), vec![]);
        // Eq / Eq.refl at universe level 1 because `Rat : Type = Sort 1`.
        let u1 = Level::succ(Level::zero());
        let eq = Expr::const_(Name::from_string("Eq"), vec![u1.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![u1]);

        // Build the type:
        //   ∀ (n : Nat) (center : NNVec n) (eps : Rat),
        //     Eq Rat (ibp_width n (eps_ball n center eps)) Rat.zero.
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());
        let vec_n = Expr::app(nn_vec, n.clone());
        let (center_id, center) = b.fresh_local(vec_n.clone());
        let (eps_id, eps) = b.fresh_local(rat.clone());

        // eps_ball n center eps
        let ball = Expr::apps(eps_ball, [n.clone(), center.clone(), eps.clone()]);
        // ibp_width n ball
        let width = Expr::apps(ibp_width, [n.clone(), ball.clone()]);
        // Eq Rat width Rat.zero
        let concl = Expr::apps(eq, [rat.clone(), width, rat_zero.clone()]);
        let ty = {
            let e = b.mk_pi(eps_id, BinderInfo::Default, rat.clone(), concl);
            let e = b.mk_pi(center_id, BinderInfo::Default, vec_n.clone(), e);
            b.mk_pi(n_id, BinderInfo::Default, nat.clone(), e)
        };
        let ty = b.finish(ty);

        // Build the value:
        //   fun (n : Nat) (center : NNVec n) (eps : Rat) =>
        //     @ibp_width_zero n (eps_ball n center eps)
        //       (fun (i : Fin n) => @Eq.refl.{1} Rat Rat.zero).
        let mut bv = EnvDeclBuilder::new();
        let (n_id, n) = bv.fresh_local(nat.clone());
        let vec_n = Expr::app(
            Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            n.clone(),
        );
        let (center_id, center) = bv.fresh_local(vec_n.clone());
        let (eps_id, eps) = bv.fresh_local(rat.clone());

        let ball = Expr::apps(
            Expr::const_(Name::from_string("NNVerify.eps_ball"), vec![]),
            [n.clone(), center.clone(), eps.clone()],
        );
        // h : ∀ (i : Fin n), lower ball i = upper ball i.
        //   Body := @Eq.refl Rat Rat.zero (kernel reduces both sides to Rat.zero).
        let h = {
            let fin_n = Expr::app(fin, n.clone());
            let mut ch = EnvDeclBuilder::child_of(&bv);
            let (i_id, _i) = ch.fresh_local(fin_n.clone());
            let refl = Expr::apps(eq_refl, [rat.clone(), rat_zero.clone()]);
            let r = ch.mk_lam(i_id, BinderInfo::Default, fin_n, refl);
            ch.finish_child(r)
        };
        let body = Expr::apps(ibp_width_zero, [n.clone(), ball, h]);
        let value = {
            let e = bv.mk_lam(eps_id, BinderInfo::Default, rat, body);
            let e = bv.mk_lam(center_id, BinderInfo::Default, vec_n, e);
            bv.mk_lam(n_id, BinderInfo::Default, nat, e)
        };
        let value = bv.finish(value);

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if T4 sub-lemmas have been initialized.
    #[cfg(test)]
    pub(crate) fn has_nn_verify_ibp_width_zero(&self) -> bool {
        self.nn_verify_ibp_width_zero_init
    }
}
