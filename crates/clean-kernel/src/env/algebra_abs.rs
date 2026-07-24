// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Absolute value, min/max, and decidable ordering for Rat
//!
//! Contains:
//! - init_rat_decidable_ord: Decidable instances for Rat ordering
//! - init_rat_minmax: Rat.min, Rat.max and characterizing properties
//! - init_rat_abs: Rat.abs and triangle inequality
//!
//! Int functions are in `algebra_abs_int.rs`.
//! Nat functions are in `algebra_abs_nat.rs`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Decidable instances for Rat.lt and Rat.le
    ///
    /// This adds:
    /// - instDecidableRatLt : axiom ∀ a b : Rat, Decidable (Rat.lt a b)
    /// - instDecidableRatLe : axiom ∀ a b : Rat, Decidable (Rat.le a b)
    /// - Rat.decEq : axiom ∀ a b : Rat, Decidable (Eq a b)
    ///
    /// These enable decision procedures for Rat ordering and equality comparisons.
    /// Since Rat comparison reduces to Int comparison (cross-multiplication),
    /// decidability follows from decidability of Int ordering.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.rat_decidable_ord_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_rat_decidable_ord(&mut self) -> Result<(), EnvError> {
        if self.rat_decidable_ord_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_rat_ord()?; // Provides Rat.le, Rat.lt
        self.init_decidable()?; // Provides Decidable
        self.init_eq()?; // Provides Eq

        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let lt_const = Expr::const_(Name::from_string("Rat.lt"), vec![]);
        let le_const = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let decidable_const = Expr::const_(Name::from_string("Decidable"), vec![]);

        // instDecidableRatLt : ∀ a b : Rat, Decidable (Rat.lt a b)
        let decidable_lt_type = {
            let mut bd = EnvDeclBuilder::new();
            let (a_id, a) = bd.fresh_local(rat_const.clone());
            let (bv_id, bv) = bd.fresh_local(rat_const.clone());
            let body = Expr::app(
                decidable_const.clone(),
                Expr::app(Expr::app(lt_const.clone(), a), bv),
            );
            let e = bd.mk_pi(bv_id, BinderInfo::Default, rat_const.clone(), body);
            let e = bd.mk_pi(a_id, BinderInfo::Default, rat_const.clone(), e);
            bd.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("instDecidableRatLt"),
            level_params: vec![],
            type_: decidable_lt_type,
        })?;

        // instDecidableRatLe : ∀ a b : Rat, Decidable (Rat.le a b)
        let decidable_le_type = {
            let mut bd = EnvDeclBuilder::new();
            let (a_id, a) = bd.fresh_local(rat_const.clone());
            let (bv_id, bv) = bd.fresh_local(rat_const.clone());
            let body = Expr::app(
                decidable_const.clone(),
                Expr::app(Expr::app(le_const.clone(), a), bv),
            );
            let e = bd.mk_pi(bv_id, BinderInfo::Default, rat_const.clone(), body);
            let e = bd.mk_pi(a_id, BinderInfo::Default, rat_const.clone(), e);
            bd.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("instDecidableRatLe"),
            level_params: vec![],
            type_: decidable_le_type,
        })?;

        // Rat.decEq : ∀ a b : Rat, Decidable (Eq a b)
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let dec_eq_type = {
            let mut bd = EnvDeclBuilder::new();
            let (a_id, a) = bd.fresh_local(rat_const.clone());
            let (bv_id, bv) = bd.fresh_local(rat_const.clone());
            let body = Expr::app(
                decidable_const.clone(),
                Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), rat_const.clone()), a),
                    bv,
                ),
            );
            let e = bd.mk_pi(bv_id, BinderInfo::Default, rat_const.clone(), body);
            let e = bd.mk_pi(a_id, BinderInfo::Default, rat_const.clone(), e);
            bd.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Rat.decEq"),
            level_params: vec![],
            type_: dec_eq_type,
        })?;

        self.rat_decidable_ord_init = true;
        Ok(())
    }

    /// Check if Rat Decidable ordering instances have been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.rat_decidable_ord_init == true`
    pub(crate) fn has_rat_decidable_ord(&self) -> bool {
        self.rat_decidable_ord_init
    }

    /// Initialize Rat min/max functions
    ///
    /// This adds:
    /// - Rat.min : Rat → Rat → Rat (axiom)
    /// - Rat.max : Rat → Rat → Rat (axiom)
    /// - Rat.min_def : ∀ a b : Rat, Rat.le a b → Eq (Rat.min a b) a
    /// - Rat.min_def' : ∀ a b : Rat, Rat.le b a → Eq (Rat.min a b) b
    /// - Rat.max_def : ∀ a b : Rat, Rat.le a b → Eq (Rat.max a b) b
    /// - Rat.max_def' : ∀ a b : Rat, Rat.le b a → Eq (Rat.max a b) a
    ///
    /// Note: min and max are defined axiomatically with their characterizing properties.
    /// This avoids needing computational comparison infrastructure.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.rat_minmax_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    // Overlay-only: registers the constructive `Rat` min/max proofs, which live
    // behind `math-overlays`. Reached only from gated `nn_verify_*` modules and
    // tests, so gate this entry point on the same feature to keep the default
    // (trusted-kernel) build consistent. See `algebra_rat_minmax_proof`.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn init_rat_minmax(&mut self) -> Result<(), EnvError> {
        if self.rat_minmax_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_rat_ord()?; // Provides Rat.le
        self.init_eq()?; // Provides Eq

        // WS-B: register the constructive quotient-carrier `Rat.min` / `Rat.max`
        // Definitions + `Rat.{min,max}_def{,'}` Theorems FIRST. Each
        // `Declaration::Axiom` below is then guarded with a `get_const` check, so
        // the kernel-checked Theorems/Definitions win and the opaque axioms are
        // never registered. See `algebra_rat_minmax_proof.rs`.
        self.register_rat_minmax_proofs()?;

        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        // ========================================
        // Rat.min : Rat → Rat → Rat
        // ========================================
        let rat_minmax_type = Expr::pi(
            BinderInfo::Default,
            rat_const.clone(),
            Expr::pi(BinderInfo::Default, rat_const.clone(), rat_const.clone()),
        );

        if self.get_const(&Name::from_string("Rat.min")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Rat.min"),
                level_params: vec![],
                type_: rat_minmax_type.clone(),
            })?;
        }

        // ========================================
        // Rat.max : Rat → Rat → Rat
        // ========================================
        if self.get_const(&Name::from_string("Rat.max")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Rat.max"),
                level_params: vec![],
                type_: rat_minmax_type,
            })?;
        }

        let rat_min = Expr::const_(Name::from_string("Rat.min"), vec![]);
        let rat_max = Expr::const_(Name::from_string("Rat.max"), vec![]);

        // ========================================
        // Rat.min_def : ∀ a b : Rat, Rat.le a b → Eq (Rat.min a b) a
        // When a ≤ b, min a b = a
        // ========================================
        let min_def_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(rat_const.clone());
            let (b_id, bvar) = bldr.fresh_local(rat_const.clone());
            let le_a_b = Expr::app(Expr::app(rat_le.clone(), a.clone()), bvar.clone());
            let (h_id, _h) = bldr.fresh_local(le_a_b.clone());
            let min_a_b = Expr::app(Expr::app(rat_min.clone(), a.clone()), bvar.clone());
            let eq_min_a_b_a = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), rat_const.clone()), min_a_b),
                a.clone(),
            );
            let e = bldr.mk_pi(h_id, BinderInfo::Default, le_a_b, eq_min_a_b_a);
            let e = bldr.mk_pi(b_id, BinderInfo::Default, rat_const.clone(), e);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, rat_const.clone(), e);
            bldr.finish(e)
        };

        if self.get_const(&Name::from_string("Rat.min_def")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Rat.min_def"),
                level_params: vec![],
                type_: min_def_type,
            })?;
        }

        // ========================================
        // Rat.min_def' : ∀ a b : Rat, Rat.le b a → Eq (Rat.min a b) b
        // When b ≤ a, min a b = b
        // ========================================
        let min_def_alt_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(rat_const.clone());
            let (b_id, bvar) = bldr.fresh_local(rat_const.clone());
            let le_b_a = Expr::app(Expr::app(rat_le.clone(), bvar.clone()), a.clone());
            let (h_id, _h) = bldr.fresh_local(le_b_a.clone());
            let min_a_b = Expr::app(Expr::app(rat_min.clone(), a.clone()), bvar.clone());
            let eq_min_a_b_b = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), rat_const.clone()), min_a_b),
                bvar.clone(),
            );
            let e = bldr.mk_pi(h_id, BinderInfo::Default, le_b_a, eq_min_a_b_b);
            let e = bldr.mk_pi(b_id, BinderInfo::Default, rat_const.clone(), e);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, rat_const.clone(), e);
            bldr.finish(e)
        };

        if self.get_const(&Name::from_string("Rat.min_def'")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Rat.min_def'"),
                level_params: vec![],
                type_: min_def_alt_type,
            })?;
        }

        // ========================================
        // Rat.max_def : ∀ a b : Rat, Rat.le a b → Eq (Rat.max a b) b
        // When a ≤ b, max a b = b
        // ========================================
        let max_def_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(rat_const.clone());
            let (b_id, bvar) = bldr.fresh_local(rat_const.clone());
            let le_a_b = Expr::app(Expr::app(rat_le.clone(), a.clone()), bvar.clone());
            let (h_id, _h) = bldr.fresh_local(le_a_b.clone());
            let max_a_b = Expr::app(Expr::app(rat_max.clone(), a.clone()), bvar.clone());
            let eq_max_a_b_b = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), rat_const.clone()), max_a_b),
                bvar.clone(),
            );
            let e = bldr.mk_pi(h_id, BinderInfo::Default, le_a_b, eq_max_a_b_b);
            let e = bldr.mk_pi(b_id, BinderInfo::Default, rat_const.clone(), e);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, rat_const.clone(), e);
            bldr.finish(e)
        };

        if self.get_const(&Name::from_string("Rat.max_def")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Rat.max_def"),
                level_params: vec![],
                type_: max_def_type,
            })?;
        }

        // ========================================
        // Rat.max_def' : ∀ a b : Rat, Rat.le b a → Eq (Rat.max a b) a
        // When b ≤ a, max a b = a
        // ========================================
        let max_def_alt_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(rat_const.clone());
            let (b_id, bvar) = bldr.fresh_local(rat_const.clone());
            let le_b_a = Expr::app(Expr::app(rat_le.clone(), bvar.clone()), a.clone());
            let (h_id, _h) = bldr.fresh_local(le_b_a.clone());
            let max_a_b = Expr::app(Expr::app(rat_max.clone(), a.clone()), bvar.clone());
            let eq_max_a_b_a = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), rat_const.clone()), max_a_b),
                a.clone(),
            );
            let e = bldr.mk_pi(h_id, BinderInfo::Default, le_b_a, eq_max_a_b_a);
            let e = bldr.mk_pi(b_id, BinderInfo::Default, rat_const.clone(), e);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, rat_const.clone(), e);
            bldr.finish(e)
        };

        if self.get_const(&Name::from_string("Rat.max_def'")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Rat.max_def'"),
                level_params: vec![],
                type_: max_def_alt_type,
            })?;
        }

        self.rat_minmax_init = true;
        Ok(())
    }

    /// Check if Rat min/max functions have been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.rat_minmax_init == true`
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn has_rat_minmax(&self) -> bool {
        self.rat_minmax_init
    }

    /// Initialize Rat absolute value function and properties
    ///
    /// Adds:
    /// - `Rat.abs : Rat → Rat` — reducible Definition `fun a => Rat.max a (Rat.neg a)` (TCB-shrink Tier 1, Branch B)
    /// - `Rat.abs_nonneg : ∀ a : Rat, Rat.le Rat.zero (Rat.abs a)` — [Theorem, constructive]
    /// - `Rat.abs_of_nonneg : ∀ a : Rat, Rat.le Rat.zero a → Eq (Rat.abs a) a` — [Theorem, constructive]
    /// - `Rat.abs_of_neg : ∀ a : Rat, Rat.lt a Rat.zero → Eq (Rat.abs a) (Rat.neg a)` — [Theorem, constructive]
    /// - `Rat.abs_zero : Eq (Rat.abs Rat.zero) Rat.zero` — [Theorem, constructive]
    /// - `Rat.abs_neg : ∀ a : Rat, Eq (Rat.abs (Rat.neg a)) (Rat.abs a)` — [Theorem, constructive]
    /// - `Rat.abs_add_le : ∀ a b : Rat, Rat.le (Rat.abs (Rat.add a b)) (Rat.add (Rat.abs a) (Rat.abs b))` — [Theorem, constructive — hard batch]
    /// - `Rat.abs_sub_le : ∀ a b : Rat, Rat.le (Rat.abs (Rat.sub a b)) (Rat.add (Rat.abs a) (Rat.abs b))` — [Theorem, constructive — hard batch]
    /// - `Rat.abs_mul : ∀ a b : Rat, Eq (Rat.abs (Rat.mul a b)) (Rat.mul (Rat.abs a) (Rat.abs b))` — [Theorem, constructive — TCB-shrink Tier 3, `algebra_rat_abs_mul_proof.rs`]
    ///
    /// # Carrier remediation history (#3545 → #3565 → TCB-shrink Tier 1)
    ///
    /// Wave 2 (#3545) promoted four entries from `Axiom` to `Theorem` with
    /// `Eq.refl` / `Rat.le_refl` bodies that type-checked only via δ-collapse of
    /// the reducible IDENTITY carrier `Rat.abs = fun a => a` (#3435) — classic
    /// MASQUERADE (rules M1+M2+M4 of
    /// `designs/2026-04-19-demasquerade-cxxx-pattern.md`). Wave 3 (#3565, Branch
    /// A) demoted all four back to `Axiom` and co-demoted `Rat.abs` to `Opaque`
    /// so the identity body would not δ-reduce — but the carrier stayed the
    /// identity, so the axioms remained false in the intended model
    /// (`Rat.abs_nonneg : 0 ≤ |a|` ≡ `0 ≤ a`, FALSE for `a < 0`), merely masked
    /// by opacity.
    ///
    /// TCB-shrink Tier 1 (Branch B, `algebra_rat_abs_proof.rs`) fixes the cause:
    /// `Rat.abs` becomes the FAITHFUL reducible Definition
    /// `Rat.max a (Rat.neg a)` and the five tractable lemmas are PROVED as
    /// genuine kernel-checked constructive `Declaration::Theorem`s over the
    /// sound quotient (case-splitting on `Rat.le_total` and discharging via
    /// `Rat.max_def{,'}` / `Rat.le_max_left/right` / `Rat.neg_le_neg`). The M1
    /// masquerade is now closed STRUCTURALLY by the non-trivial body
    /// (`Rat.abs a` no longer reduces to `a`), not by opacity. The three
    /// sign/triangle lemmas (`abs_mul`, `abs_add_le`, `abs_sub_le`) remain
    /// honest admitted axioms pending the hard batch — but now over the REAL
    /// carrier, so they are non-refutable AND true in the intended model.
    ///
    /// The registrations below are GUARDED with `get_const(...).is_none()`, so
    /// once the proofs land the faithful Definition + Theorems win and the
    /// legacy opaque carrier / abs axioms never enter.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.rat_abs_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_rat_abs(&mut self) -> Result<(), EnvError> {
        if self.rat_abs_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_rat_ord()?; // Provides Rat.le, Rat.lt, Rat.zero
        self.init_rat_arith()?; // Provides Rat.neg, Rat.mul
        self.init_eq()?; // Provides Eq
        self.init_rat_linear_order()?;

        // TCB-shrink Tier 1 (Branch B carrier remediation, #3435 / #3470):
        // register the FAITHFUL reducible `Rat.abs := Rat.max a (Rat.neg a)`
        // Definition and the genuine kernel-checked `Rat.abs_*` Theorems FIRST.
        // Every carrier/axiom registration below is then guarded with a
        // `get_const(...).is_none()` (or already-Definition/Theorem) check, so
        // the real declarations win and the opaque identity carrier + the
        // honest-but-false-in-model abs axioms are NEVER registered. See
        // `algebra_rat_abs_proof.rs` for the soundness rationale: the old
        // `Opaque` identity body `fun a => a` made `Rat.abs_nonneg : 0 ≤ |a|`
        // semantically equivalent to `0 ≤ a` (FALSE for `a < 0`) — a latent
        // unsoundness masked only by the carrier's opacity. The faithful
        // `max a (-a)` carrier makes all the abs lemmas genuinely true.
        // Like `register_rat_abs_mul_proof` below, the abs proofs consume
        // `math-overlays`-gated lemma modules, so they run only in the
        // test/overlays build; the default build keeps the guarded honest
        // axioms over the faithful carrier.
        #[cfg(any(test, feature = "math-overlays"))]
        self.register_rat_abs_proofs_easy()?;
        #[cfg(any(test, feature = "math-overlays"))]
        self.register_rat_abs_proofs_hard()?;
        // TCB-shrink Tier 3: prove the last `Rat.abs_*` axiom `Rat.abs_mul`
        // (`|a·b| = |a|·|b|`) as a kernel-checked constructive Theorem over the
        // faithful `max a (-a)` carrier (four-way sign cases). Runs BEFORE the
        // `Rat.abs_mul` axiom fallback below, so the guarded `get_const(...)`
        // check there is a no-op and the false-in-model axiom never enters.
        // See `algebra_rat_abs_mul_proof.rs`. The proof consumes the
        // `math-overlays`-gated nn-verify Rat ordering/sign lemmas (Rat.mul_neg,
        // Rat.neg_le_neg, ...), so — like the hard-batch triangle proofs above —
        // it runs only in the test/overlays build (where the Soundness
        // Certificate is computed, giving the TCB the eliminated count); the
        // default build keeps the guarded honest axiom (sound over the faithful
        // carrier).
        #[cfg(any(test, feature = "math-overlays"))]
        self.register_rat_abs_mul_proof()?;

        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let rat_lt = Expr::const_(Name::from_string("Rat.lt"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_neg = Expr::const_(Name::from_string("Rat.neg"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        // ========================================
        // Rat.abs : Rat → Rat
        // ========================================
        //
        // Registered as a `Declaration::Opaque` with carrier body
        // `fun a : Rat => a`. The mathematical content of absolute value lives
        // in the named axiom lemmas (`Rat.abs_nonneg`, `Rat.abs_mul`,
        // `Rat.abs_add_le`, `Rat.abs_sub_le`, `Rat.abs_neg`) which characterize
        // the operation without relying on the body.
        //
        // WHY (original): `NNVerify.NNVec.l1_norm` expands to
        // `Fin.sum n (fun i => Rat.abs (v i))`, so any theorem mentioning
        // `l1_norm` — e.g. T21 `NNVerify.LayerNorm.zonotope_width_preserved` —
        // transitively references `Rat.abs`. Keeping `Rat.abs` as a
        // `Declaration::Axiom` put it into T21's transitive non-foundational
        // closure and caused the clean-native mathverse shard to reject T21 via
        // `ExcludeReason::AxiomDependent`. Switching to a carrier Definition
        // removed it from the closure without altering any downstream lemma
        // (those lemmas don't unfold `Rat.abs`; they treat it opaquely through
        // `Rat.abs_*` axioms). #3435.
        //
        // #3565 Branch A carrier co-demotion (2026-04-20): The reducible
        // `Declaration::Definition` with identity body
        // (`fun a : Rat => a`) was the enabler for the four MASQUERADE
        // `Rat.abs_*` Theorems landed in #3545 — under δ-reduction both
        // sides of `Rat.abs_zero`, `Rat.abs_mul`, `Rat.abs_of_nonneg`, and
        // `Rat.abs_add_le` collapsed to the same term and the Eq.refl /
        // Rat.le_refl proof terms type-checked via alias-collapse (Rules
        // M1 + M2 + M4 of
        // `designs/2026-04-19-demasquerade-cxxx-pattern.md`). The four
        // theorems were demoted to `Declaration::Axiom` in the first pass,
        // but the reducible identity carrier was left in place — a latent
        // attack surface for any future Theorem of the form
        // `f (Rat.abs a) = f a` or `Rat.abs a = a` to re-close via
        // `Eq.refl` on the δ-unfolded body.
        //
        // Flipping to `Declaration::Opaque` with the SAME body closes the
        // δ-reduction path (`Rat.abs a -> a` no longer fires during
        // `def_eq`) while keeping the axiom-audit semantics: Opaque has a
        // value so it is NOT counted as a domain axiom (see
        // `axiom_audit.rs:565` — Opaque contributes to `report.opaques`,
        // not `all_domain_axioms`), so T21's `l1_norm` → `Rat.abs`
        // transitive closure remains axiom-free, preserving the #3435
        // T21 inclusion invariant. Only the declaration kind flips.
        // Mirrors the co-demotion pattern in #3591 (`Zonotope.to_ibp`),
        // #3592 (`BlockCert.axiomProfile` / `composePair`), #3583
        // (`C004.jacobian_dense`), #3586 (`C001.tail_norm_sum`), #3578
        // (`C010.lipschitz_local`), #3579 (`C012.single_lp_form`).
        let rat_abs_type = Expr::pi(BinderInfo::Default, rat_const.clone(), rat_const.clone());
        let rat_abs_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat_const.clone());
            let r = b.mk_lam(a_id, BinderInfo::Default, rat_const.clone(), a);
            b.finish(r)
        };

        // GUARDED (TCB-shrink Tier 1): only register the legacy Opaque identity
        // carrier if `register_rat_abs_proofs_easy` did not already install the
        // faithful `Rat.max a (Rat.neg a)` Definition. With the proofs landed,
        // this is a no-op and the false-in-model identity body never enters.
        if self.get_const(&Name::from_string("Rat.abs")).is_none() {
            self.add_decl(Declaration::Opaque {
                name: Name::from_string("Rat.abs"),
                level_params: vec![],
                type_: rat_abs_type,
                value: rat_abs_value,
            })?;
        }

        let rat_abs = Expr::const_(Name::from_string("Rat.abs"), vec![]);

        // ========================================
        // Rat.abs_nonneg : ∀ a : Rat, Rat.le Rat.zero (Rat.abs a)
        // abs is always nonnegative
        // ========================================
        let abs_nonneg_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(rat_const.clone());
            let body = Expr::app(
                Expr::app(rat_le.clone(), rat_zero.clone()),
                Expr::app(rat_abs.clone(), a.clone()),
            );
            let e = bldr.mk_pi(a_id, BinderInfo::Default, rat_const.clone(), body);
            bldr.finish(e)
        };

        if self
            .get_const(&Name::from_string("Rat.abs_nonneg"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Rat.abs_nonneg"),
                level_params: vec![],
                type_: abs_nonneg_type,
            })?;
        }

        // ========================================
        // Rat.abs_of_nonneg : ∀ a : Rat, Rat.le Rat.zero a → Eq (Rat.abs a) a
        // When a ≥ 0, abs a = a
        //
        // #3565 (MASQUERADE demasquerade, Branch A): This was landed in #3545 as
        // a `Declaration::Theorem` with proof term
        // `fun a h => @Eq.refl.{1} Rat a`. Under the reducible identity
        // carrier `Rat.abs = fun a => a` (see `rat_abs_value` above, #3435),
        // the goal `Eq (Rat.abs a) a` delta-reduces to `Eq a a`, so the
        // `Eq.refl` body type-checks but encodes ZERO mathematical content —
        // it closes only because the carrier is a reducible alias. Per
        // `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rules M1 + M2 + M4,
        // this is the MASQUERADE anti-pattern. Demoted to honest
        // `Declaration::Axiom` until the #3435 / #3470 carrier remediation
        // gives `Rat.abs` a non-identity body and a real proof can be written.
        // ========================================
        let abs_of_nonneg_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(rat_const.clone());
            let le_zero_a = Expr::app(Expr::app(rat_le.clone(), rat_zero.clone()), a.clone());
            let (h_id, _h) = bldr.fresh_local(le_zero_a.clone());
            let eq_abs_a_a = Expr::app(
                Expr::app(
                    Expr::app(eq_const.clone(), rat_const.clone()),
                    Expr::app(rat_abs.clone(), a.clone()),
                ),
                a.clone(),
            );
            let e = bldr.mk_pi(h_id, BinderInfo::Default, le_zero_a, eq_abs_a_a);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, rat_const.clone(), e);
            bldr.finish(e)
        };

        if self
            .get_const(&Name::from_string("Rat.abs_of_nonneg"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Rat.abs_of_nonneg"),
                level_params: vec![],
                type_: abs_of_nonneg_type,
            })?;
        }

        // ========================================
        // Rat.abs_of_neg : ∀ a : Rat, Rat.lt a Rat.zero → Eq (Rat.abs a) (Rat.neg a)
        // When a < 0, abs a = -a
        // ========================================
        let abs_of_neg_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(rat_const.clone());
            let lt_a_zero = Expr::app(Expr::app(rat_lt.clone(), a.clone()), rat_zero.clone());
            let (h_id, _h) = bldr.fresh_local(lt_a_zero.clone());
            let eq_abs_a_neg_a = Expr::app(
                Expr::app(
                    Expr::app(eq_const.clone(), rat_const.clone()),
                    Expr::app(rat_abs.clone(), a.clone()),
                ),
                Expr::app(rat_neg.clone(), a.clone()),
            );
            let e = bldr.mk_pi(h_id, BinderInfo::Default, lt_a_zero, eq_abs_a_neg_a);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, rat_const.clone(), e);
            bldr.finish(e)
        };

        if self
            .get_const(&Name::from_string("Rat.abs_of_neg"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Rat.abs_of_neg"),
                level_params: vec![],
                type_: abs_of_neg_type,
            })?;
        }

        // ========================================
        // Rat.abs_zero : Eq (Rat.abs Rat.zero) Rat.zero
        // abs 0 = 0
        //
        // #3565 (MASQUERADE demasquerade, Branch A): This was landed in #3545 as
        // a `Declaration::Theorem` with proof term `@Eq.refl.{1} Rat Rat.zero`.
        // Under the reducible identity carrier `Rat.abs = fun a => a`
        // (see `rat_abs_value` above, #3435), the goal
        // `Eq (Rat.abs Rat.zero) Rat.zero` delta-reduces to
        // `Eq Rat.zero Rat.zero`, so `Eq.refl` type-checks trivially via
        // reducible alias collapse — ZERO mathematical content. Per
        // `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rules M1 + M2 + M4,
        // this is the MASQUERADE anti-pattern. Demoted to honest
        // `Declaration::Axiom` pending #3435 / #3470 carrier remediation.
        // ========================================
        let abs_zero_type = Expr::app(
            Expr::app(
                Expr::app(eq_const.clone(), rat_const.clone()),
                Expr::app(rat_abs.clone(), rat_zero.clone()),
            ),
            rat_zero.clone(),
        );

        if self.get_const(&Name::from_string("Rat.abs_zero")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Rat.abs_zero"),
                level_params: vec![],
                type_: abs_zero_type,
            })?;
        }

        // ========================================
        // Rat.abs_mul : ∀ a b : Rat, Eq (Rat.abs (Rat.mul a b)) (Rat.mul (Rat.abs a) (Rat.abs b))
        // abs is multiplicative: |a * b| = |a| * |b|
        //
        // TCB-shrink Tier 3 (ELIMINATED): `register_rat_abs_mul_proof` (called
        // above, before this block) now registers `Rat.abs_mul` as a
        // kernel-checked constructive `Declaration::Theorem` over the faithful
        // `max a (-a)` carrier (four-way sign-case proof,
        // `algebra_rat_abs_mul_proof.rs`). The `get_const(...).is_none()` guard
        // below is therefore a DEAD no-op kept only as defence-in-depth; the
        // honest-but-admitted axiom is never registered. It leaves the
        // Soundness-Certificate TCB (the last `Rat.abs_*` axiom to do so).
        //
        // #3565 (MASQUERADE demasquerade, Branch A): This was landed in #3545 as
        // a `Declaration::Theorem` with proof term
        // `fun a b => @Eq.refl.{1} Rat (Rat.mul a b)`. Under the reducible
        // identity carrier `Rat.abs = fun a => a` (see `rat_abs_value`
        // above, #3435), both sides of the equation delta-reduce to
        // `Rat.mul a b`, so `Eq.refl` type-checks via reducible alias
        // collapse — ZERO mathematical content. Per
        // `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rules M1 + M2 + M4,
        // this is the MASQUERADE anti-pattern. Demoted to honest
        // `Declaration::Axiom` pending #3435 / #3470 carrier remediation.
        // ========================================
        let abs_mul_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(rat_const.clone());
            let (b_id, bvar) = bldr.fresh_local(rat_const.clone());
            let abs_mul = Expr::app(
                rat_abs.clone(),
                Expr::app(Expr::app(rat_mul.clone(), a.clone()), bvar.clone()),
            );
            let mul_abs = Expr::app(
                Expr::app(rat_mul.clone(), Expr::app(rat_abs.clone(), a.clone())),
                Expr::app(rat_abs.clone(), bvar.clone()),
            );
            let body = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), rat_const.clone()), abs_mul),
                mul_abs,
            );
            let e = bldr.mk_pi(b_id, BinderInfo::Default, rat_const.clone(), body);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, rat_const.clone(), e);
            bldr.finish(e)
        };

        if self.get_const(&Name::from_string("Rat.abs_mul")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Rat.abs_mul"),
                level_params: vec![],
                type_: abs_mul_type,
            })?;
        }

        // ========================================
        // Rat.abs_add_le : ∀ a b : Rat, Rat.le (Rat.abs (Rat.add a b)) (Rat.add (Rat.abs a) (Rat.abs b))
        // Triangle inequality: |a + b| ≤ |a| + |b|
        //
        // #3565 (MASQUERADE demasquerade, Branch A): This was landed in #3545 as
        // a `Declaration::Theorem` with proof term
        // `fun a b => Rat.le_refl (Rat.add a b)`. Under the reducible
        // identity carrier `Rat.abs = fun a => a` (see `rat_abs_value`
        // above, #3435), LHS `Rat.abs (Rat.add a b)` and RHS
        // `Rat.add (Rat.abs a) (Rat.abs b)` both delta-reduce to
        // `Rat.add a b`, so `Rat.le_refl` type-checks via reducible alias
        // collapse — ZERO mathematical content. Per
        // `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rules M1 + M2 + M4,
        // this is the MASQUERADE anti-pattern. Demoted to honest
        // `Declaration::Axiom` pending #3435 / #3470 carrier remediation.
        // ========================================
        let rat_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let abs_add_le_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(rat_const.clone());
            let (b_id, bvar) = bldr.fresh_local(rat_const.clone());
            let lhs = Expr::app(
                rat_abs.clone(),
                Expr::app(Expr::app(rat_add.clone(), a.clone()), bvar.clone()),
            );
            let rhs = Expr::app(
                Expr::app(rat_add.clone(), Expr::app(rat_abs.clone(), a.clone())),
                Expr::app(rat_abs.clone(), bvar.clone()),
            );
            let body = Expr::app(Expr::app(rat_le.clone(), lhs), rhs);
            let e = bldr.mk_pi(b_id, BinderInfo::Default, rat_const.clone(), body);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, rat_const.clone(), e);
            bldr.finish(e)
        };

        if self
            .get_const(&Name::from_string("Rat.abs_add_le"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Rat.abs_add_le"),
                level_params: vec![],
                type_: abs_add_le_type,
            })?;
        }

        // ========================================
        // Rat.abs_sub_le : ∀ a b : Rat, Rat.le (Rat.abs (Rat.sub a b)) (Rat.add (Rat.abs a) (Rat.abs b))
        // Triangle inequality for subtraction: |a - b| ≤ |a| + |b|
        // ========================================
        let rat_sub = Expr::const_(Name::from_string("Rat.sub"), vec![]);
        let abs_sub_le_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(rat_const.clone());
            let (b_id, bvar) = bldr.fresh_local(rat_const.clone());
            let lhs = Expr::app(
                rat_abs.clone(),
                Expr::app(Expr::app(rat_sub.clone(), a.clone()), bvar.clone()),
            );
            let rhs = Expr::app(
                Expr::app(rat_add.clone(), Expr::app(rat_abs.clone(), a.clone())),
                Expr::app(rat_abs.clone(), bvar.clone()),
            );
            let body = Expr::app(Expr::app(rat_le.clone(), lhs), rhs);
            let e = bldr.mk_pi(b_id, BinderInfo::Default, rat_const.clone(), body);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, rat_const.clone(), e);
            bldr.finish(e)
        };

        if self
            .get_const(&Name::from_string("Rat.abs_sub_le"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Rat.abs_sub_le"),
                level_params: vec![],
                type_: abs_sub_le_type,
            })?;
        }

        // ========================================
        // Rat.abs_neg : ∀ a : Rat, Eq (Rat.abs (Rat.neg a)) (Rat.abs a)
        // abs of negation equals abs: |-a| = |a|
        // ========================================
        let abs_neg_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(rat_const.clone());
            let body = Expr::app(
                Expr::app(
                    Expr::app(eq_const.clone(), rat_const.clone()),
                    Expr::app(rat_abs.clone(), Expr::app(rat_neg.clone(), a.clone())),
                ),
                Expr::app(rat_abs.clone(), a.clone()),
            );
            let e = bldr.mk_pi(a_id, BinderInfo::Default, rat_const.clone(), body);
            bldr.finish(e)
        };

        if self.get_const(&Name::from_string("Rat.abs_neg")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Rat.abs_neg"),
                level_params: vec![],
                type_: abs_neg_type,
            })?;
        }

        self.rat_abs_init = true;
        Ok(())
    }

    /// Check if Rat absolute value function has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.rat_abs_init == true`
    pub(crate) fn has_rat_abs(&self) -> bool {
        self.rat_abs_init
    }
}

// NOTE: Int min/max and abs functions moved to algebra_abs_int.rs
// NOTE: Nat absDiff moved to algebra_abs_nat.rs
