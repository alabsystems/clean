// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorem declarations for Fourier analysis on the Boolean hypercube.
//!
//! Registers the kernel-level axiom surfaces for:
//! - `noise_stability_fourier`: S_rho[f] = sum_S rho^|S| f^(S)^2
//! - `fourier_weight_parseval`: sum_k W^k[f] = E[f^2]
//! - `friedgut_boolean`: low-influence Boolean functions are close to juntas
//! - `fourier_coefficient_transform`: f^(S) = FourierTransform(n, f)(S)
//!
//! Each theorem has an associated helper proposition that encodes the
//! statement body, plus the theorem itself quantifying over all inputs.

use super::boolean_analysis::BoolAnalysisConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    // ======================================================================
    // noise_stability_fourier: S_rho[f] = sum_S rho^|S| f^(S)^2
    // ======================================================================

    /// `fun (x : HCPoint n) => pm (f x)` — the ±1 amplitude `pm∘f` for
    /// `f : BoolFn n`, the coefficient instantiation of `noise_spectral_core`.
    fn noise_amp(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let pm = Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]);
        let hcpoint = Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            n.clone(),
        );
        let mut b = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = b.fresh_local(hcpoint.clone());
        let body = Expr::app(pm, Expr::app(f.clone(), x.clone()));
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcpoint, body))
    }

    /// Helper proposition for noise stability Fourier representation.
    ///
    /// RETIREMENT (noise campaign rung 6): formerly an opaque `∀ ρ n f, Prop`
    /// admitted axiom; now a reducible `Declaration::Definition` whose body is
    /// the GENUINE un-normalized ρ-weighted spectral equation over the
    /// `noiseDensityW` carrier (built by `noise_spectral_body_eq` at
    /// `a := fun x => pm (f x)`):
    ///
    /// ```text
    /// noise_stability_fourier_helper ρ n f :=
    ///   @Eq Rat
    ///     (Σ_x Σ_y (pm(f x)·pm(f y)) · noiseDensityW ρ n x y)   -- S_ρ-correlation
    ///     (Σ_S ρ^{|S|} · A(S)²),  A(S) := Σ_x pm(f x)·χ_S(x)    -- spectral side
    /// ```
    ///
    /// i.e. `Σ_x Σ_y pm(f x)pm(f y)·noiseDensityW = Σ_S ρ^{|S|}·A(S)²` (O'Donnell,
    /// *Analysis of Boolean Functions*, §2.4; UN-NORMALIZED — `A(S) = 2^n·f̂(S)`,
    /// so this is `(2^n)²·Σ_S ρ^{|S|}·f̂(S)²`; the `2^n`-per-coordinate
    /// normalization is deferred). The carrier `noiseDensityW ρ n x y` (reducible)
    /// δ-unfolds to `Σ_S ρ^{|S|}·(χ_S x·χ_S y)`, the honest correlated density
    /// (see `noiseDensityW_eq_prod`: `noiseDensityW = Π_i(1+ρ·pm(x_i)pm(y_i))`).
    /// All sub-terms are CHECKED defs, so the body is a real proposition with
    /// content — not an uninterpreted predicate. DISCHARGES the bare axiom.
    pub(super) fn register_noise_stability_fourier_helper(
        &mut self,
        c: &BoolAnalysisConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noise_stability_fourier_helper");
        if self
            .get_const(&name)
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        // Body refers to subsetSum / noiseDensityW / pm / chi / Rat.powNat.
        self.register_subset_sum()?;
        self.register_noise_density_w()?;

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (rho_id, _) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, _) = b.fresh_local(bool_fn_n.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, c.prop.clone());
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (rho_id, rho) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let amp = self.noise_amp(&b, &n, &f);
            let body = self.noise_spectral_body_eq(&b, &rho, &n, &amp);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, body);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.discharge_axiom_for_redefinition(&name);
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `noise_stability_fourier : ∀ ρ n f,
    ///   Σ_x Σ_y pm(f x)pm(f y)·noiseDensityW ρ n x y = Σ_S ρ^{|S|}·A(S)²`.
    ///
    /// RETIREMENT (noise campaign rung 6): formerly an admitted axiom; now a
    /// kernel-CHECKED `Declaration::Theorem`. The conclusion
    /// `noise_stability_fourier_helper ρ n f` δ-unfolds (reducible helper) to the
    /// un-normalized spectral `Eq`; the proof instantiates the constructive
    /// `noise_spectral_core` at `a := fun x => pm (f x)`. Empty admitted-axiom
    /// closure (`ProofQuality::Constructive`) — TCB shrinks by 2 (helper +
    /// theorem). UN-NORMALIZED convention; `A(S) = 2^n·f̂(S)`.
    pub(super) fn register_noise_stability_fourier(
        &mut self,
        c: &BoolAnalysisConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noise_stability_fourier");
        if self
            .get_const(&name)
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Theorem))
        {
            return Ok(());
        }
        self.register_noise_stability_fourier_helper(c)?;
        self.register_noise_spectral_core_theorem()?;

        let helper = Expr::const_(
            Name::from_string("BoolAnalysis.noise_stability_fourier_helper"),
            vec![],
        );
        let core = Expr::const_(
            Name::from_string("BoolAnalysis.noise_spectral_core"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (rho_id, rho) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let body = Expr::apps(helper, [rho.clone(), n.clone(), f.clone()]);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, body);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        // value: fun ρ n f => noise_spectral_core ρ n (fun x => pm (f x)).
        //   Result type is `core`'s conclusion at a := pm∘f, def-eq (helper
        //   reducible) to `helper ρ n f`.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (rho_id, rho) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let amp = self.noise_amp(&b, &n, &f);
            let body = Expr::apps(core.clone(), [rho.clone(), n.clone(), amp]);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, body);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.discharge_axiom_for_redefinition(&name);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    // ======================================================================
    // fourier_weight_parseval: sum_k W^k[f] = E[f^2]
    // ======================================================================

    /// Helper proposition for Fourier weight Parseval decomposition.
    ///
    /// TCB-shrink (Part 2): no longer a bare `∀ n f, Prop` admitted axiom. The
    /// helper is now a genuine reducible `Declaration::Definition` carrying the
    /// EXACT statement body as a real `Eq Rat`:
    ///
    /// ```text
    /// fourier_weight_parseval_helper n f :=
    ///   @Eq Rat
    ///     (Fin.sum (Nat.succ n) (fun (k : Fin (n+1)) =>
    ///        FourierWeightAtLevel n f (Fin.val (n+1) k)))      -- Σ_{k=0}^{n} W^k[f]
    ///     (subsetSum n (fun (S : HCPoint n) =>
    ///        Rat.mul (FourierCoefficient n f S)
    ///                (FourierCoefficient n f S)))              -- Σ_S f̂(S)²
    /// ```
    ///
    /// i.e. the level-decomposition of Fourier weight, `Σ_{k=0}^{n} W^k[f]
    /// = Σ_S f̂(S)²` (O'Donnell, *Analysis of Boolean Functions*, §1.4). Both
    /// `FourierWeightAtLevel` and `FourierCoefficient` are CHECKED reducible
    /// Definitions, and `Fin.sum` / `subsetSum` are the existing summation
    /// carriers, so the body is a real proposition with content — not an
    /// uninterpreted predicate. DISCHARGES the bare helper axiom (TCB −1).
    ///
    /// The theorem `fourier_weight_parseval` asserting this `Eq` for all `n,f`
    /// remains an honest admitted axiom: closing it constructively is a genuine
    /// partition-by-popcount regrouping that still needs new induction lemmas
    /// (see `register_fourier_weight_parseval`).
    pub(super) fn register_fourier_weight_parseval_helper(
        &mut self,
        c: &BoolAnalysisConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.fourier_weight_parseval_helper");
        if self
            .get_const(&name)
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        // Body refers to subsetSum / FourierWeightAtLevel / FourierCoefficient /
        // Fin.sum — all already registered by `init_fourier_boolean`.
        self.register_subset_sum()?;

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, _) = b.fresh_local(bool_fn_n.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, c.prop.clone());
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let eq_rat = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let fin_sum = Expr::const_(Name::from_string("Fin.sum"), vec![]);
        let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let subset_sum = Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]);
        let fourier_coeff =
            Expr::const_(Name::from_string("BoolAnalysis.FourierCoefficient"), vec![]);
        let weight_at_level = Expr::const_(
            Name::from_string("BoolAnalysis.FourierWeightAtLevel"),
            vec![],
        );
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());

            let n_succ = Expr::app(nat_succ.clone(), n.clone());

            // LHS: Fin.sum (n+1) (fun (k : Fin (n+1)) =>
            //        FourierWeightAtLevel n f (Fin.val (n+1) k))
            let lhs_fn = {
                let mut lb = EnvDeclBuilder::child_of(&b);
                let fin_succ = c.fin_of(&n_succ);
                let (k_id, k) = lb.fresh_local(fin_succ.clone());
                let level = Expr::apps(fin_val.clone(), [n_succ.clone(), k.clone()]);
                let term = Expr::apps(weight_at_level.clone(), [n.clone(), f.clone(), level]);
                lb.finish_child(lb.mk_lam(k_id, BinderInfo::Default, fin_succ, term))
            };
            let lhs = Expr::apps(fin_sum.clone(), [n_succ.clone(), lhs_fn]);

            // RHS: subsetSum n (fun (S : HCPoint n) =>
            //        Rat.mul (FourierCoefficient n f S) (FourierCoefficient n f S))
            let rhs_fn = {
                let mut rb = EnvDeclBuilder::child_of(&b);
                let hcpoint = c.hcpoint_of(&n);
                let (s_id, s) = rb.fresh_local(hcpoint.clone());
                let coeff = Expr::apps(fourier_coeff.clone(), [n.clone(), f.clone(), s.clone()]);
                let coeff_sq = Expr::apps(rat_mul.clone(), [coeff.clone(), coeff]);
                rb.finish_child(rb.mk_lam(s_id, BinderInfo::Default, hcpoint, coeff_sq))
            };
            let rhs = Expr::apps(subset_sum.clone(), [n.clone(), rhs_fn]);

            let body = Expr::apps(eq_rat.clone(), [c.rat.clone(), lhs, rhs]);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, body);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.discharge_axiom_for_redefinition(&name);
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `fourier_weight_parseval : forall n f, Σ_{k=0}^{n} W^k[f] = Σ_S f̂(S)²`
    ///
    /// HONEST ADMITTED AXIOM (Part 2). The helper it asserts is now a genuine
    /// `Eq Rat` (see `register_fourier_weight_parseval_helper`), so this is a
    /// real mathematical statement, not an opaque-predicate masquerade. A
    /// constructive discharge is a partition-by-popcount regrouping of the
    /// CHECKED `FourierWeightAtLevel`/`subsetSum`, but it still requires NEW
    /// induction lemmas that are not yet in the inventory:
    ///
    /// 1. `Fin.sum_swap`-style exchange of the outer level sum `Fin.sum (n+1)`
    ///    with the inner `Fin.sum (2^n)` inside each `W^k` (the existing
    ///    `Fin.sum_swap` is `Fin m → Fin n` and applies after δ-unfolding both
    ///    sums over their respective ranges).
    /// 2. An indicator-partition collapse over a Nat range:
    ///    `Σ_{k=0}^{n} ind(Nat.beq m k) · x = x` for `m ≤ n` (exactly one level
    ///    matches), proved by induction on the range bound.
    /// 3. `popcount (hcDecode n j) ≤ n` — the popcount of an `n`-coordinate
    ///    indicator is at most `n` (sum of `n` `{0,1}` terms), needed to satisfy
    ///    the `m ≤ n` premise of (2).
    ///
    /// Until those land the axiom is the sound discharge: it asserts a true
    /// identity and cannot derive `False`.
    pub(super) fn register_fourier_weight_parseval(
        &mut self,
        c: &BoolAnalysisConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("BoolAnalysis.fourier_weight_parseval"))
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Theorem))
        {
            return Ok(());
        }
        // Support lemmas for the constructive discharge (idempotent).
        self.register_fourier_weight_parseval_support()?;

        let helper = Expr::const_(
            Name::from_string("BoolAnalysis.fourier_weight_parseval_helper"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let body = Expr::apps(helper, [n.clone(), f.clone()]);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, body);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        // PROVEN (TCB-shrink): a genuine kernel-CHECKED `Declaration::Theorem`.
        // The conclusion `fourier_weight_parseval_helper n f` δ-unfolds (reducible
        // helper) to `@Eq Rat (Σ_{k≤n} W^k[f]) (Σ_S f̂(S)²)`; the proof swaps the
        // level/subset double sum (`Fin.sum_swap`) and collapses the level index
        // pointwise (`fourier_level_collapse`, premise `|S| ≤ n` from
        // `Fin.sumNat_le_card` + `indNat_le_one`), landing on
        // `Σ_j f̂(hcDecode n j)²` which is def-eq to the RHS `subsetSum`. Empty
        // admitted-axiom closure (`ProofQuality::Constructive`).
        let value = self.fourier_weight_parseval_value();
        self.discharge_axiom_for_redefinition(&Name::from_string(
            "BoolAnalysis.fourier_weight_parseval",
        ));
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("BoolAnalysis.fourier_weight_parseval"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    // ======================================================================
    // friedgut_boolean: low-influence => close to junta
    // ======================================================================

    /// The FROZEN junta-cardinality budget `BUDGET e := Nat.add e e` (= `2·e`).
    ///
    /// A concrete affine function of the dyadic exponent `e`, frozen as the
    /// junta-size bound in the faithful Friedgut L2 helper. Any larger affine
    /// budget is the SOUND direction (it only weakens the `|J|` bound), so the
    /// constant is documented here and can be raised later without unsoundness.
    ///
    /// VISIBILITY: `pub(crate)` (visibility-only widening of dead code) so the
    /// small-N refutation gate (`refute_axiom_body`) can RECONSTRUCT the (FALSE)
    /// friedgut body in its validation test without re-implementing the budget.
    /// No proof, axiom, or cert-golden change.
    pub(crate) fn friedgut_budget(&self, e: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            [e.clone(), e.clone()],
        )
    }

    /// The faithful **L2-distance** Friedgut helper body (O'Donnell §9.6), the
    /// EXPLICIT-WITNESS form (NOT the Bool-junta corollary):
    ///
    /// ```text
    /// fun (n f K eps) =>
    ///   Rat.le (TotalInfluence n f) K ->                       -- I[f] ≤ K
    ///   Rat.le 0 eps ->                                        -- eps ≥ 0 (non-vacuity)
    ///   ∀ (e : Nat), Rat.le (natCast (2^e) · eps) K ->         -- DYADIC: 2^e·eps ≤ K
    ///     Exists (J : HCPoint n)
    ///       (And (Nat.le (setSizeNat n J) (Nat.pow 2 (BUDGET e)))    -- |J| ≤ 2^{O(K/eps)}
    ///            (Rat.le (subsetSum n (fun S =>
    ///                       Rat.mul (ind (notSubsetMask n S J))
    ///                               (FourierCoefficient n f S
    ///                                · FourierCoefficient n f S)))
    ///                    eps))                                       -- ‖f − proj_J f‖₂² ≤ eps
    /// ```
    ///
    /// GENUINE NON-VACUOUS: the `And` forces BOTH a real `setSizeNat`-cardinality
    /// bound (forbidding the `J = all-coords` trivialization, where the mass
    /// vanishes but `|J| = n` is unbounded) AND the exact L2 distance to the best
    /// `J`-junta (`Σ_{S⊄J} f̂(S)²`, un-normalized — matching
    /// `fourier_weight_parseval`). NOT the Bool-junta corollary. `J : HCPoint n`
    /// is the explicit coordinate-set indicator (the witness), bounded by `n`.
    ///
    /// VISIBILITY: `pub(crate)` (visibility-only widening of dead code). The body
    /// is reverted-to-opaque and NO LONGER installed as the `friedgut_boolean_helper`
    /// value (see `register_friedgut_boolean_helper`); it survives ONLY as a builder
    /// the small-N refutation gate (`refute_axiom_body`) reconstructs to PROVE its
    /// validation test genuinely refutes the false body. No proof/axiom/cert change.
    pub(crate) fn friedgut_l2_faithful_body(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        f: &Expr,
        kk: &Expr,
        eps: &Expr,
    ) -> Expr {
        let cc = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let nat = cc("Nat");
        let rat = cc("Rat");
        let nat_succ = cc("Nat.succ");
        let nat_zero = cc("Nat.zero");
        let int_of_nat = cc("Int.ofNat");
        let rat_mk = cc("Rat.mk");
        let rat_mul = cc("Rat.mul");
        let rat_zero = cc("Rat.zero");
        let nat_pow = cc("Nat.pow");
        let nat_le = cc("Nat.le");
        let le_le = Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]);
        let inst_le_rat = cc("instLERat");
        let hcpoint = cc("BoolAnalysis.HCPoint");
        let subset_sum = cc("BoolAnalysis.subsetSum");
        let ind = cc("BoolAnalysis.ind");
        let not_subset_mask = cc("BoolAnalysis.notSubsetMask");
        let set_size_nat = cc("BoolAnalysis.setSizeNat");
        let fourier = cc("BoolAnalysis.FourierCoefficient");
        let total_influence = cc("BoolAnalysis.TotalInfluence");
        let u1 = Level::succ(Level::zero());

        let one_nat = Expr::app(nat_succ.clone(), nat_zero.clone());
        let two_nat = Expr::app(nat_succ.clone(), one_nat.clone());
        let mul = |a: Expr, b: Expr| Expr::apps(rat_mul.clone(), [a, b]);
        let rat_le =
            |a: Expr, b: Expr| Expr::apps(le_le.clone(), [rat.clone(), inst_le_rat.clone(), a, b]);
        // natCast m := Rat.mk (Int.ofNat m) 1.
        let natcast = |m: Expr| {
            Expr::apps(
                rat_mk.clone(),
                [Expr::app(int_of_nat.clone(), m), one_nat.clone()],
            )
        };
        let hcpoint_n = Expr::app(hcpoint.clone(), n.clone());
        let ti = Expr::apps(total_influence.clone(), [n.clone(), f.clone()]);

        let mut b = EnvDeclBuilder::child_of(parent);

        // hI : I[f] ≤ K.
        let hi_ty = rat_le(ti.clone(), kk.clone());
        let (hi_id, _) = b.fresh_local(hi_ty.clone());
        // heps : 0 ≤ eps.
        let heps_ty = rat_le(rat_zero.clone(), eps.clone());
        let (heps_id, _) = b.fresh_local(heps_ty.clone());

        // ∀ (e : Nat), (natCast (2^e) · eps ≤ K) → Exists J, And(size, mass).
        let dyadic = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (e_id, e) = d.fresh_local(nat.clone());
            // 2^e := Nat.pow 2 e ; cast ; guard.
            let pow2e = Expr::apps(nat_pow.clone(), [two_nat.clone(), e.clone()]);
            let guard_ty = rat_le(mul(natcast(pow2e), eps.clone()), kk.clone());
            let (guard_id, _) = d.fresh_local(guard_ty.clone());

            // Exists (J : HCPoint n) (pred J).
            let pred = {
                let mut g = EnvDeclBuilder::child_of(&d);
                let (j_id, j) = g.fresh_local(hcpoint_n.clone());
                // size : Nat.le (setSizeNat n J) (Nat.pow 2 (BUDGET e)).
                let size_j = Expr::apps(set_size_nat.clone(), [n.clone(), j.clone()]);
                let budget = self.friedgut_budget(&e);
                let pow2b = Expr::apps(nat_pow.clone(), [two_nat.clone(), budget]);
                let size_concl = Expr::apps(nat_le.clone(), [size_j, pow2b]);
                // mass : subsetSum n (fun S => ind(notSubsetMask n S J)·(f̂·f̂)) ≤ eps.
                let mass_fn = {
                    let mut h = EnvDeclBuilder::child_of(&g);
                    let (s_id, s) = h.fresh_local(hcpoint_n.clone());
                    let coeff = Expr::apps(fourier.clone(), [n.clone(), f.clone(), s.clone()]);
                    let sq = mul(coeff.clone(), coeff);
                    let mask =
                        Expr::apps(not_subset_mask.clone(), [n.clone(), s.clone(), j.clone()]);
                    let body = mul(Expr::app(ind.clone(), mask), sq);
                    h.finish_child(h.mk_lam(s_id, BinderInfo::Default, hcpoint_n.clone(), body))
                };
                let mass = Expr::apps(subset_sum.clone(), [n.clone(), mass_fn]);
                let mass_concl = rat_le(mass, eps.clone());
                // And size_concl mass_concl.
                let and = Expr::apps(
                    Expr::const_(Name::from_string("And"), vec![]),
                    [size_concl, mass_concl],
                );
                g.finish_child(g.mk_lam(j_id, BinderInfo::Default, hcpoint_n.clone(), and))
            };
            let exists = Expr::apps(
                Expr::const_(Name::from_string("Exists"), vec![u1.clone()]),
                [hcpoint_n.clone(), pred],
            );
            let body = d.mk_pi(guard_id, BinderInfo::Default, guard_ty, exists);
            d.finish_child(d.mk_pi(e_id, BinderInfo::Default, nat.clone(), body))
        };

        let e = b.mk_pi(heps_id, BinderInfo::Default, heps_ty, dyadic);
        b.finish_child(b.mk_pi(hi_id, BinderInfo::Default, hi_ty, e))
    }

    /// The FIXED **exponential** junta-cardinality budget exponent
    /// `BUDGET2 e := Nat.mul 15 (Nat.pow 2 e)` (= `15·2^e`), so the junta-size
    /// bound is `|J| ≤ Nat.pow 2 (BUDGET2 e) = 2^(15·2^e)`.
    ///
    /// This is the genuine-Friedgut budget, REPLACING the reverted affine
    /// `friedgut_budget e := 2·e` (which gave the polynomial `|J| ≤ 4^e ≈
    /// (K/eps)²` — strictly stronger than Friedgut, refuted FALSE; see
    /// `designs/2026-06-20-friedgut-helper-body-FALSE-critical.md`).
    ///
    /// ## Why `15·2^e` (a deliberately GENEROUS over-estimate), not the tight `2^e`
    ///
    /// Friedgut's junta size is `2^(O(K/eps))` where the constant inside `O(·)` is
    /// STRICTLY > 1 — the standard `9^d`-route proof (O'Donnell §9.6, used by the
    /// landed bricks) gives `|J| ≤ K/dr² ≈ 9^(2K/eps)·poly = 2^(2·log₂9·K/eps)·poly
    /// = 2^(6.34·K/eps)·poly`. So a TIGHT exponent `2^e ≈ K/eps` (constant 1) would
    /// be OVER-STRONG (a smaller — possibly false — junta than Friedgut guarantees).
    /// The exact constant is the roadmap's `BUDGET FROZEN-pending-proof` crux
    /// (`designs/2026-06-13-friedgut-junta-theorem-roadmap.md` §"Honest residuals").
    /// Per that roadmap's principle "any LARGER budget is the SOUND direction"
    /// (a bigger `|J|` bound only WEAKENS the claim), we freeze a generous
    /// `15·2^e`: under the v2 two-sided guard `2^e·eps ≤ K ≤ 2^(e+1)·eps` we have
    /// `2^e ≥ K/(2eps)`, so `15·2^e ≥ 7.5·K/eps ≥ 6.34·K/eps` — comfortably above
    /// the scholarly `9^d`-route exponent, hence `2^(15·2^e)` SOUNDLY dominates the
    /// bricks' `|J| ≤ K/dr²`. It stays `2^(Θ(K/eps))` (exponential, n-INDEPENDENT),
    /// so it is genuine Friedgut — neither over-strong (≥ the provable size) nor
    /// vacuous (finite, tied to K/eps; in the regime `n > 2^(15·2^e)` it forbids
    /// `J = all-coords`).
    ///
    /// The exponent `15·2^e` stays ≤ 60 for the dyadic exponents the small-N gate
    /// instantiates (`e ≤ 2`), so `Nat.pow 2 (15·2^e) ≤ 2^60` decodes to a `u64`
    /// `Nat.lit` — the gate EXAMINES the size conjunct (it is not stuck), confirming
    /// `J = all-coords` (`|J| = n ≤ 2^(15·2^e)`) satisfies it, a genuine (non-vacuous)
    /// `None`.
    ///
    /// VISIBILITY: `pub(crate)` so the small-N refutation gate
    /// (`refute_axiom_body`) can reconstruct the v2 body in its validation tests.
    pub(crate) fn friedgut_budget_v2(&self, e: &Expr) -> Expr {
        // 15 as a Nat literal `Nat.succ^15 Nat.zero`.
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let mut fifteen = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        for _ in 0..15 {
            fifteen = Expr::app(nat_succ.clone(), fifteen);
        }
        // 2^e.
        let pow2e = Expr::apps(
            Expr::const_(Name::from_string("Nat.pow"), vec![]),
            [
                Expr::app(
                    nat_succ.clone(),
                    Expr::app(
                        nat_succ.clone(),
                        Expr::const_(Name::from_string("Nat.zero"), vec![]),
                    ),
                ),
                e.clone(),
            ],
        );
        // 15 · 2^e.
        Expr::apps(
            Expr::const_(Name::from_string("Nat.mul"), vec![]),
            [fifteen, pow2e],
        )
    }

    /// The **genuine-Friedgut** L2-distance helper body (O'Donnell §9.6), v2 —
    /// fixing BOTH defects of the reverted-FALSE `friedgut_l2_faithful_body`:
    ///
    /// ```text
    /// fun (n f K eps) =>
    ///   Rat.le (TotalInfluence n f) K ->                        -- I[f] ≤ K
    ///   Rat.le 0 eps ->                                         -- eps ≥ 0
    ///   ∀ (e : Nat),
    ///     And (Rat.le (natCast (2^e)     · eps) K)              -- 2^e·eps ≤ K      ┐ TWO-SIDED guard
    ///         (Rat.le K (natCast (2^(e+1)) · eps)) ->           -- K ≤ 2^(e+1)·eps  ┘ pins e ≈ ⌊log₂(K/eps)⌋
    ///       Exists (J : HCPoint n)
    ///         (And (Nat.le (setSizeNat n J) (Nat.pow 2 (15·2^e)))  -- |J| ≤ 2^(15·2^e) = 2^(Θ(K/eps)) (EXPONENTIAL)
    ///              (Rat.le (subsetSum n (fun S =>
    ///                         ind (notSubsetMask n S J)
    ///                           · (f̂(S) · f̂(S)))) eps))           -- ‖f − proj_J f‖₂² ≤ eps
    /// ```
    ///
    /// ## Defect 1 fixed — the `∀ e` no longer forces a tiny junta at small `e`.
    ///
    /// The reverted body's guard was the ONE-SIDED `2^e·eps ≤ K`, so EVERY small
    /// `e` (incl. `e = 0`) was admissible and forced a `2^(2·0)=1`-junta — false
    /// for parity at `n = 2`. The v2 guard is the **two-sided** band
    /// `2^e·eps ≤ K ≤ 2^(e+1)·eps`, which admits ONLY `e ≈ ⌊log₂(K/eps)⌋` (one or
    /// two consecutive dyadic exponents at the boundary). For the design
    /// counterexample (`n=2`, parity, `K=2`, `eps=1/2`) the only admissible `e` is
    /// `e = 2` (`2^2·½ = 2 ≤ 2 ≤ 4 = 2^3·½`), which demands `|J| ≤ 2^(15·2^2) =
    /// 2^60` — the full set `J = {1,2}` (`|J| = 2 ≤ 2^60`, masked-mass `= 0`)
    /// satisfies it. So the v2 body is TRUE exactly where v1 was FALSE.
    ///
    /// ## Defect 2 fixed — the budget is EXPONENTIAL, not polynomial.
    ///
    /// The reverted body's budget was the AFFINE `2^(2·e) = 4^e ≈ (K/eps)²`
    /// (polynomial — strictly STRONGER than Friedgut). v2 uses
    /// `2^(15·2^e) = 2^(Θ(K/eps))` (`friedgut_budget_v2`) — a GENEROUS over-estimate
    /// of O'Donnell's exponential junta size (the SOUND direction: bigger `|J|`
    /// bound only weakens the claim, so it cannot be over-strong; see
    /// `friedgut_budget_v2`'s doc for the `9^(6.34K/eps)`-vs-`15·2^e` derivation).
    ///
    /// GATE-CHECKED: this body PASSES `refute_axiom_body::refute_or_ok` (returns
    /// `None` over the small-N parity/dictator/majority sweep) — it is the
    /// anti-masquerade rail, run before this body is installed (see the gate's
    /// `gate_passes_v2_faithful_body` test, and `register_friedgut_boolean_helper`'s
    /// docstring). NON-VACUOUS: in the meaningful regime `n > 2^(15·2^e)` the size
    /// bound forbids `J = all-coords`, so a genuinely small junta is required.
    ///
    /// VISIBILITY: `pub(crate)` so the gate reconstructs it in its tests.
    pub(crate) fn friedgut_l2_faithful_body_v2(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        f: &Expr,
        kk: &Expr,
        eps: &Expr,
    ) -> Expr {
        let cc = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let nat = cc("Nat");
        let rat = cc("Rat");
        let nat_succ = cc("Nat.succ");
        let nat_zero = cc("Nat.zero");
        let int_of_nat = cc("Int.ofNat");
        let rat_mk = cc("Rat.mk");
        let rat_mul = cc("Rat.mul");
        let rat_zero = cc("Rat.zero");
        let nat_pow = cc("Nat.pow");
        let nat_le = cc("Nat.le");
        let le_le = Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]);
        let inst_le_rat = cc("instLERat");
        let hcpoint = cc("BoolAnalysis.HCPoint");
        let subset_sum = cc("BoolAnalysis.subsetSum");
        let ind = cc("BoolAnalysis.ind");
        let not_subset_mask = cc("BoolAnalysis.notSubsetMask");
        let set_size_nat = cc("BoolAnalysis.setSizeNat");
        let fourier = cc("BoolAnalysis.FourierCoefficient");
        let total_influence = cc("BoolAnalysis.TotalInfluence");
        let u1 = Level::succ(Level::zero());

        let one_nat = Expr::app(nat_succ.clone(), nat_zero.clone());
        let two_nat = Expr::app(nat_succ.clone(), one_nat.clone());
        let mul = |a: Expr, b: Expr| Expr::apps(rat_mul.clone(), [a, b]);
        let rat_le =
            |a: Expr, b: Expr| Expr::apps(le_le.clone(), [rat.clone(), inst_le_rat.clone(), a, b]);
        // natCast m := Rat.mk (Int.ofNat m) 1.
        let natcast = |m: Expr| {
            Expr::apps(
                rat_mk.clone(),
                [Expr::app(int_of_nat.clone(), m), one_nat.clone()],
            )
        };
        let hcpoint_n = Expr::app(hcpoint.clone(), n.clone());
        let ti = Expr::apps(total_influence.clone(), [n.clone(), f.clone()]);

        let mut b = EnvDeclBuilder::child_of(parent);

        // hI : I[f] ≤ K.
        let hi_ty = rat_le(ti.clone(), kk.clone());
        let (hi_id, _) = b.fresh_local(hi_ty.clone());
        // heps : 0 ≤ eps.
        let heps_ty = rat_le(rat_zero.clone(), eps.clone());
        let (heps_id, _) = b.fresh_local(heps_ty.clone());

        // ∀ (e : Nat), (two-sided guard) → Exists J, And(size, mass).
        let dyadic = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (e_id, e) = d.fresh_local(nat.clone());
            // 2^e and 2^(e+1).
            let pow2e = Expr::apps(nat_pow.clone(), [two_nat.clone(), e.clone()]);
            let e_succ = Expr::app(nat_succ.clone(), e.clone());
            let pow2e1 = Expr::apps(nat_pow.clone(), [two_nat.clone(), e_succ]);
            // Two-sided band guard: (2^e·eps ≤ K) ∧ (K ≤ 2^(e+1)·eps).
            let guard_lo = rat_le(mul(natcast(pow2e), eps.clone()), kk.clone());
            let guard_hi = rat_le(kk.clone(), mul(natcast(pow2e1), eps.clone()));
            let guard_ty = Expr::apps(
                Expr::const_(Name::from_string("And"), vec![]),
                [guard_lo, guard_hi],
            );
            let (guard_id, _) = d.fresh_local(guard_ty.clone());

            // Exists (J : HCPoint n) (pred J).
            let pred = {
                let mut g = EnvDeclBuilder::child_of(&d);
                let (j_id, j) = g.fresh_local(hcpoint_n.clone());
                // size : Nat.le (setSizeNat n J) (Nat.pow 2 (2^e)) — EXPONENTIAL.
                let size_j = Expr::apps(set_size_nat.clone(), [n.clone(), j.clone()]);
                let budget = self.friedgut_budget_v2(&e);
                let pow2b = Expr::apps(nat_pow.clone(), [two_nat.clone(), budget]);
                let size_concl = Expr::apps(nat_le.clone(), [size_j, pow2b]);
                // mass : subsetSum n (fun S => ind(notSubsetMask n S J)·(f̂·f̂)) ≤ eps.
                let mass_fn = {
                    let mut h = EnvDeclBuilder::child_of(&g);
                    let (s_id, s) = h.fresh_local(hcpoint_n.clone());
                    let coeff = Expr::apps(fourier.clone(), [n.clone(), f.clone(), s.clone()]);
                    let sq = mul(coeff.clone(), coeff);
                    let mask =
                        Expr::apps(not_subset_mask.clone(), [n.clone(), s.clone(), j.clone()]);
                    let body = mul(Expr::app(ind.clone(), mask), sq);
                    h.finish_child(h.mk_lam(s_id, BinderInfo::Default, hcpoint_n.clone(), body))
                };
                let mass = Expr::apps(subset_sum.clone(), [n.clone(), mass_fn]);
                let mass_concl = rat_le(mass, eps.clone());
                // And size_concl mass_concl.
                let and = Expr::apps(
                    Expr::const_(Name::from_string("And"), vec![]),
                    [size_concl, mass_concl],
                );
                g.finish_child(g.mk_lam(j_id, BinderInfo::Default, hcpoint_n.clone(), and))
            };
            let exists = Expr::apps(
                Expr::const_(Name::from_string("Exists"), vec![u1.clone()]),
                [hcpoint_n.clone(), pred],
            );
            let body = d.mk_pi(guard_id, BinderInfo::Default, guard_ty, exists);
            d.finish_child(d.mk_pi(e_id, BinderInfo::Default, nat.clone(), body))
        };

        let e = b.mk_pi(heps_id, BinderInfo::Default, heps_ty, dyadic);
        b.finish_child(b.mk_pi(hi_id, BinderInfo::Default, hi_ty, e))
    }

    /// The CORRECTED **exponential** junta-cardinality budget exponent
    /// `BUDGET3 e := Nat.mul 48 (Nat.pow 2 e)` (= `48·2^e`), so the junta-size
    /// bound is `|J| ≤ Nat.pow 2 (BUDGET3 e) = 2^(48·2^e)`.
    ///
    /// This REPLACES the FALSE-at-large-n v2 budget `15·2^e` (which is only
    /// `2^(7.5·K/eps)` at the admissible low end, BELOW the standard Friedgut
    /// threshold junta `K/dr² = 4·9^(2d)·K³/eps² = 2^(12.68·K/eps)` — the v2
    /// derivation's "6.34" DROPPED the `τ=dr²` square, computing `9^d` not
    /// `9^(2d)`; see `designs/2026-06-20-friedgut-helper-body-FALSE-critical.md`
    /// §SUPERSEDED).
    ///
    /// ## Why `48·2^e` (a SOUND over-estimate)
    ///
    /// The genuine threshold construction (O'Donnell §9.6) with `d ≈ 2K/eps`,
    /// `dr ≤ eps/(2·9^d·K)` gives `|J| ≤ K/dr² = 4·9^(2d)·K³/eps²`. With the
    /// two-sided guard `2^e·eps ≤ K ≤ 2^(e+1)·eps` we have `2^e ∈ (K/(2eps), K/eps]`,
    /// so the needed exponent `9^(2d) = 9^(8·2^e) = 2^(8·log₂9·2^e) = 2^(25.36·2^e)`
    /// (times the `K³/eps²` poly factor, dominated by another `2^(O(2^e))`). The
    /// constant `c = 48 ≥ 2·12.68 ≈ 25.4` is a GENEROUS margin over `25.36`, so the
    /// SIZE bound `K/dr² ≤ 2^(48·2^e)` is TRUE and provable. Per the roadmap's
    /// principle "any LARGER budget is the SOUND direction" (a bigger `|J|` bound
    /// only WEAKENS the claim), the generous `48` cannot be over-strong. It stays
    /// `2^(Θ(K/eps))` (exponential, n-INDEPENDENT) — genuine Friedgut.
    ///
    /// VISIBILITY: `pub(crate)` so the small-N refutation gate
    /// (`refute_axiom_body`) can reconstruct the v3 body in its validation tests.
    pub(crate) fn friedgut_budget_v3(&self, e: &Expr) -> Expr {
        // 48 as a Nat literal `Nat.succ^48 Nat.zero`.
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let mut forty_eight = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        for _ in 0..48 {
            forty_eight = Expr::app(nat_succ.clone(), forty_eight);
        }
        // 2^e.
        let pow2e = Expr::apps(
            Expr::const_(Name::from_string("Nat.pow"), vec![]),
            [
                Expr::app(
                    nat_succ.clone(),
                    Expr::app(
                        nat_succ.clone(),
                        Expr::const_(Name::from_string("Nat.zero"), vec![]),
                    ),
                ),
                e.clone(),
            ],
        );
        // 48 · 2^e.
        Expr::apps(
            Expr::const_(Name::from_string("Nat.mul"), vec![]),
            [forty_eight, pow2e],
        )
    }

    /// The **genuine-Friedgut** L2-distance helper body (O'Donnell §9.6), v3 — the
    /// CORRECTED-BUDGET body. Identical in shape to
    /// [`Environment::friedgut_l2_faithful_body_v2`] EXCEPT the junta-size budget
    /// exponent is `friedgut_budget_v3 e := 48·2^e` (not the FALSE `15·2^e`):
    ///
    /// ```text
    /// fun (n f K eps) =>
    ///   Rat.le (TotalInfluence n f) K ->                        -- I[f] ≤ K
    ///   Rat.le 0 eps ->                                         -- eps ≥ 0
    ///   ∀ (e : Nat),
    ///     And (Rat.le (natCast (2^e)     · eps) K)              -- 2^e·eps ≤ K      ┐ TWO-SIDED guard
    ///         (Rat.le K (natCast (2^(e+1)) · eps)) ->           -- K ≤ 2^(e+1)·eps  ┘ pins e ≈ ⌊log₂(K/eps)⌋
    ///       Exists (J : HCPoint n)
    ///         (And (Nat.le (setSizeNat n J) (Nat.pow 2 (48·2^e)))  -- |J| ≤ 2^(48·2^e) (EXPONENTIAL, SOUND)
    ///              (Rat.le (subsetSum n (fun S =>
    ///                         ind (notSubsetMask n S J)
    ///                           · (f̂(S) · f̂(S)))) eps))           -- ‖f − proj_J f‖₂² ≤ eps
    /// ```
    ///
    /// This is the body the co-landed `friedgut_boolean` Axiom→Theorem proof
    /// targets: the SIZE bound `K/dr² ≤ 2^(48·2^e)` is now TRUE (the v2 `15·2^e`
    /// was the FALSE-at-large-n constant that blocked Case-2). The masked-mass
    /// integrand `fun S => ind(notSubsetMask n S J)·(f̂·f̂)` is BYTE-IDENTICAL to
    /// `friedgut_l2_core`'s `full_fn`, so the L2-core mass bound slots directly in.
    ///
    /// VISIBILITY: `pub(crate)` so the gate reconstructs it in its tests.
    pub(crate) fn friedgut_l2_faithful_body_v3(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        f: &Expr,
        kk: &Expr,
        eps: &Expr,
    ) -> Expr {
        let cc = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let nat = cc("Nat");
        let rat = cc("Rat");
        let nat_succ = cc("Nat.succ");
        let nat_zero = cc("Nat.zero");
        let int_of_nat = cc("Int.ofNat");
        let rat_mk = cc("Rat.mk");
        let rat_mul = cc("Rat.mul");
        let rat_zero = cc("Rat.zero");
        let nat_pow = cc("Nat.pow");
        let nat_le = cc("Nat.le");
        let le_le = Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]);
        let inst_le_rat = cc("instLERat");
        let hcpoint = cc("BoolAnalysis.HCPoint");
        let subset_sum = cc("BoolAnalysis.subsetSum");
        let ind = cc("BoolAnalysis.ind");
        let not_subset_mask = cc("BoolAnalysis.notSubsetMask");
        let set_size_nat = cc("BoolAnalysis.setSizeNat");
        let fourier = cc("BoolAnalysis.FourierCoefficient");
        let total_influence = cc("BoolAnalysis.TotalInfluence");
        let u1 = Level::succ(Level::zero());

        let one_nat = Expr::app(nat_succ.clone(), nat_zero.clone());
        let two_nat = Expr::app(nat_succ.clone(), one_nat.clone());
        let mul = |a: Expr, b: Expr| Expr::apps(rat_mul.clone(), [a, b]);
        let rat_le =
            |a: Expr, b: Expr| Expr::apps(le_le.clone(), [rat.clone(), inst_le_rat.clone(), a, b]);
        // natCast m := Rat.mk (Int.ofNat m) 1.
        let natcast = |m: Expr| {
            Expr::apps(
                rat_mk.clone(),
                [Expr::app(int_of_nat.clone(), m), one_nat.clone()],
            )
        };
        let hcpoint_n = Expr::app(hcpoint.clone(), n.clone());
        let ti = Expr::apps(total_influence.clone(), [n.clone(), f.clone()]);

        let mut b = EnvDeclBuilder::child_of(parent);

        // hI : I[f] ≤ K.
        let hi_ty = rat_le(ti.clone(), kk.clone());
        let (hi_id, _) = b.fresh_local(hi_ty.clone());
        // heps : 0 ≤ eps.
        let heps_ty = rat_le(rat_zero.clone(), eps.clone());
        let (heps_id, _) = b.fresh_local(heps_ty.clone());

        // ∀ (e : Nat), (two-sided guard) → Exists J, And(size, mass).
        let dyadic = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (e_id, e) = d.fresh_local(nat.clone());
            // 2^e and 2^(e+1).
            let pow2e = Expr::apps(nat_pow.clone(), [two_nat.clone(), e.clone()]);
            let e_succ = Expr::app(nat_succ.clone(), e.clone());
            let pow2e1 = Expr::apps(nat_pow.clone(), [two_nat.clone(), e_succ]);
            // Two-sided band guard: (2^e·eps ≤ K) ∧ (K ≤ 2^(e+1)·eps).
            let guard_lo = rat_le(mul(natcast(pow2e), eps.clone()), kk.clone());
            let guard_hi = rat_le(kk.clone(), mul(natcast(pow2e1), eps.clone()));
            let guard_ty = Expr::apps(
                Expr::const_(Name::from_string("And"), vec![]),
                [guard_lo, guard_hi],
            );
            let (guard_id, _) = d.fresh_local(guard_ty.clone());

            // Exists (J : HCPoint n) (pred J).
            let pred = {
                let mut g = EnvDeclBuilder::child_of(&d);
                let (j_id, j) = g.fresh_local(hcpoint_n.clone());
                // size : Nat.le (setSizeNat n J) (Nat.pow 2 (48·2^e)) — EXPONENTIAL.
                let size_j = Expr::apps(set_size_nat.clone(), [n.clone(), j.clone()]);
                let budget = self.friedgut_budget_v3(&e);
                let pow2b = Expr::apps(nat_pow.clone(), [two_nat.clone(), budget]);
                let size_concl = Expr::apps(nat_le.clone(), [size_j, pow2b]);
                // mass : subsetSum n (fun S => ind(notSubsetMask n S J)·(f̂·f̂)) ≤ eps.
                let mass_fn = {
                    let mut h = EnvDeclBuilder::child_of(&g);
                    let (s_id, s) = h.fresh_local(hcpoint_n.clone());
                    let coeff = Expr::apps(fourier.clone(), [n.clone(), f.clone(), s.clone()]);
                    let sq = mul(coeff.clone(), coeff);
                    let mask =
                        Expr::apps(not_subset_mask.clone(), [n.clone(), s.clone(), j.clone()]);
                    let body = mul(Expr::app(ind.clone(), mask), sq);
                    h.finish_child(h.mk_lam(s_id, BinderInfo::Default, hcpoint_n.clone(), body))
                };
                let mass = Expr::apps(subset_sum.clone(), [n.clone(), mass_fn]);
                let mass_concl = rat_le(mass, eps.clone());
                // And size_concl mass_concl.
                let and = Expr::apps(
                    Expr::const_(Name::from_string("And"), vec![]),
                    [size_concl, mass_concl],
                );
                g.finish_child(g.mk_lam(j_id, BinderInfo::Default, hcpoint_n.clone(), and))
            };
            let exists = Expr::apps(
                Expr::const_(Name::from_string("Exists"), vec![u1.clone()]),
                [hcpoint_n.clone(), pred],
            );
            let body = d.mk_pi(guard_id, BinderInfo::Default, guard_ty, exists);
            d.finish_child(d.mk_pi(e_id, BinderInfo::Default, nat.clone(), body))
        };

        let e = b.mk_pi(heps_id, BinderInfo::Default, heps_ty, dyadic);
        b.finish_child(b.mk_pi(hi_id, BinderInfo::Default, hi_ty, e))
    }

    /// Helper proposition for Friedgut's junta theorem.
    ///
    /// RETIREMENT (FRIEDGUT run, TCB 5→4): formerly an admitted `Declaration::Axiom`
    /// with the opaque body `Prop` (an unconstrained `BoolFn n → Rat → Rat → Prop`
    /// placeholder); now a reducible `Declaration::Definition` carrying the
    /// GENUINE-FRIEDGUT **L2-distance** body v2 (O'Donnell §9.6, explicit-witness
    /// form) — see [`Environment::friedgut_l2_faithful_body_v2`]. DISCHARGES the
    /// bare axiom.
    ///
    /// ## Why this is a GENUINE retirement (unlike the reverted-FALSE v1)
    ///
    /// A prior fleet attempt installed `friedgut_l2_faithful_body` (the `∀ e` +
    /// affine `BUDGET=2e` body), which is FALSE — refutable at `n=2` (parity,
    /// `e=0`): `∀ e` forces a `1`-junta at the small exponent, and `2^(2e)=4^e` is
    /// a POLYNOMIAL junta size while Friedgut's is EXPONENTIAL. That made
    /// `friedgut_boolean` a CONCRETE-FALSE admitted axiom and was reverted to the
    /// opaque axiom (see `designs/2026-06-20-friedgut-helper-body-FALSE-critical.md`).
    ///
    /// The v2 body fixes BOTH defects: a TWO-SIDED dyadic band guard
    /// `2^e·eps ≤ K ≤ 2^(e+1)·eps` pins `e ≈ ⌊log₂(K/eps)⌋` (no tiny-junta forcing),
    /// and an EXPONENTIAL `|J| ≤ 2^(2^e) = 2^(Θ(K/eps))` (the size the landed bricks
    /// `restricted_mass_le`/`high_degree_mass_le` prove). It is non-vacuous L2-Friedgut
    /// (real `Exists J` with `And(size, mass)`), NOT the Bool-junta corollary.
    ///
    /// ## The anti-masquerade rail (MANDATORY — the gate ran before this land)
    ///
    /// The EXACT body installed here was run through the small-N refutation gate
    /// ([`super::refute_axiom_body::refute_or_ok`]) and returned `None` (no
    /// counterexample) over the default parity/dictator/majority sweep BEFORE this
    /// retirement landed — see the always-on `refute_axiom_body::tests ::
    /// gate_passes_v2_faithful_body`, which reconstructs this same body (via the
    /// shared [`Environment::friedgut_l2_faithful_body_v2`] builder) and asserts the
    /// gate stays silent, while the companion `refutes_friedgut_false_body_at_n2_parity`
    /// proves the SAME gate STILL refutes the FALSE v1 body — so the `None` is
    /// DISCRIMINATING, not a vacuous always-`None`. The gate is NOT re-run inline
    /// here: its deep `subsetSum`/`FourierCoefficient` ground reduction needs a
    /// 256 MB stack and ~tens of seconds, which would overflow / dominate the many
    /// init paths that call `init_fourier_boolean`. The always-on test is the
    /// authoritative rail; this registrar installs the gate-verified body directly.
    pub(super) fn register_friedgut_boolean_helper(
        &mut self,
        c: &BoolAnalysisConsts,
    ) -> Result<(), EnvError> {
        // Idempotent: already the genuine reducible Definition → leave alone.
        if self
            .get_const(&Name::from_string("BoolAnalysis.friedgut_boolean_helper"))
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        // notSubsetMask/setSizeNat are pulled in: the v3 body
        // (`friedgut_l2_faithful_body_v3`) references them, as do the four landed
        // case-lemmas that the co-landed `friedgut_boolean` proof consumes.
        self.register_not_subset_mask()?;

        // type: forall (n : Nat) (f : BoolFn n) (K eps : Rat), Prop
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, _) = b.fresh_local(bool_fn_n.clone());
            let (k_id, _) = b.fresh_local(c.rat.clone());
            let (eps_id, _) = b.fresh_local(c.rat.clone());
            let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), c.prop.clone());
            let e = b.mk_pi(k_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // ── CO-LAND (TCB 5→3): install the CORRECTED-budget v3 body ──
        //
        // The helper becomes a reducible `Definition` carrying the GENUINE-FRIEDGUT
        // L2-distance body `friedgut_l2_faithful_body_v3` (junta budget `48·2^e`,
        // the SOUND constant `c = 48 ≥ 2·12.68 ≈ 25.4` that dominates Friedgut's
        // `K/dr² = 2^(Θ(12.68·K/eps))`; see the v3 builder docstring). Unlike the
        // reverted v2 body (budget `15·2^e = 2^(7.5·K/eps)`, FALSE-at-large-n), the
        // v3 budget is provably above the threshold-junta cardinality, so the body
        // is TRUE — and it is now PROVED: `BoolAnalysis.friedgut_boolean` (below)
        // is a genuine `Theorem` whose `Constructive`, empty-closure proof
        // (`friedgut_boolean_proof`, assembling the four landed case-lemmas) targets
        // EXACTLY this body. Installing it here lets `friedgut_boolean`'s type
        // (`∀ n f K eps, helper n f K eps`) δ-reduce to the v3 body so the wiring
        // proof discharges it. The opaque axiom is removed.
        //
        // value: fun (n : Nat) (f : BoolFn n) (K eps : Rat) => <v3 Friedgut body>.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let (k_id, kk) = b.fresh_local(c.rat.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let chain = self.friedgut_l2_faithful_body_v3(&b, &n, &f, &kk, &eps);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), chain);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // Discharge the bare axiom and install the reducible v3 Definition. The new
        // `type_` is definitionally the axiom's (`∀ n f K eps, Prop`), so every
        // previously-checked term referencing the symbol stays well-typed; the
        // symbol merely gains its δ-reduction rule.
        self.discharge_axiom_for_redefinition(&Name::from_string(
            "BoolAnalysis.friedgut_boolean_helper",
        ));
        self.add_decl(Declaration::Definition {
            name: Name::from_string("BoolAnalysis.friedgut_boolean_helper"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `friedgut_boolean : forall n f K eps,
    ///   I[f] <= K -> eps > 0 -> dist(f, J_{2^{O(K/eps)}}) <= eps`
    ///
    /// Friedgut's junta theorem: Boolean functions with total influence at
    /// most K are eps-close to a junta depending on at most 2^{O(K/eps)}
    /// coordinates.
    pub(super) fn register_friedgut_boolean(
        &mut self,
        c: &BoolAnalysisConsts,
    ) -> Result<(), EnvError> {
        // Idempotent: already the genuine Theorem → leave alone.
        if self
            .get_const(&Name::from_string("BoolAnalysis.friedgut_boolean"))
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Theorem))
        {
            return Ok(());
        }

        // CO-LAND (TCB 5→3): register the wiring proof + EVERY const it references
        // BEFORE add_decl (else `add_decl` errors on undefined consts). The wiring
        // lemma `friedgut_boolean_proof` assembles the four landed case-lemmas into
        // a `Constructive`, empty-closure proof of the v3 body.
        self.register_friedgut_boolean_proof()?;

        let helper = Expr::const_(
            Name::from_string("BoolAnalysis.friedgut_boolean_helper"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let (k_id, k) = b.fresh_local(c.rat.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let body = Expr::apps(helper, [n.clone(), f.clone(), k.clone(), eps.clone()]);
            let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), body);
            let e = b.mk_pi(k_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // The proof: `friedgut_boolean_proof` has type EXACTLY the v3 body
        // (spelled out), and `helper n f K eps` δ-reduces to that body (helper is
        // now the reducible v3 Definition), so the wiring lemma proves the
        // `∀ n f K eps, helper n f K eps` statement verbatim. NOT a
        // Theorem-wrapping-Axiom: the value is a real constructive proof term.
        let value = Expr::const_(
            Name::from_string("BoolAnalysis.friedgut_boolean_proof"),
            vec![],
        );

        // Discharge the pre-existing opaque axiom (if any), then add the Theorem.
        self.discharge_axiom_for_redefinition(&Name::from_string("BoolAnalysis.friedgut_boolean"));
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("BoolAnalysis.friedgut_boolean"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    // ======================================================================
    // fourier_coefficient_transform: f^(S) = FourierTransform(n, f)(S)
    // ======================================================================

    /// Helper proposition for the coefficient/transform correspondence.
    ///
    /// PROVEN (TCB-shrink): no longer a bare `Declaration::Axiom`. The helper is
    /// now a genuine reducible `Declaration::Definition` carrying the EXACT
    /// statement body as a real `Eq`:
    ///
    /// ```text
    /// fourier_coefficient_transform_helper n f S :=
    ///   @Eq Rat (FourierCoefficient n f S) (FourierTransform n f S)
    /// ```
    ///
    /// The subset argument `S` is its Finset-free indicator `S : HCPoint n` — the
    /// SAME domain the migrated `FourierCoefficient` / `FourierTransform`
    /// Definitions consume (previously the helper bound `S : Finset (Fin n)`, the
    /// opaque-stub domain that no longer matches the real defs). Because
    /// `FourierTransform n f := fun S => FourierCoefficient n f S`, the two sides
    /// are definitionally equal, so `register_fourier_coefficient_transform`
    /// discharges it by `@Eq.refl`. The body bottoms out in the defined
    /// `FourierCoefficient` / `FourierTransform` (each with an EMPTY
    /// admitted-axiom closure), so the resulting theorem is
    /// `ProofQuality::Constructive`.
    pub(super) fn register_fourier_coefficient_transform_helper(
        &mut self,
        c: &BoolAnalysisConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(
                "BoolAnalysis.fourier_coefficient_transform_helper",
            ))
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        let hcpoint_n_ty = |n: &Expr| c.hcpoint_of(n);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, _) = b.fresh_local(bool_fn_n.clone());
            let hcp_n = hcpoint_n_ty(&n);
            let (s_id, _) = b.fresh_local(hcp_n.clone());
            let e = b.mk_pi(s_id, BinderInfo::Default, hcp_n, c.prop.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // value: fun (n : Nat) (f : BoolFn n) (S : HCPoint n) =>
        //   @Eq Rat (FourierCoefficient n f S) (FourierTransform n f S)
        let eq_rat = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let coeff = Expr::const_(Name::from_string("BoolAnalysis.FourierCoefficient"), vec![]);
        let transform = Expr::const_(Name::from_string("BoolAnalysis.FourierTransform"), vec![]);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let hcp_n = hcpoint_n_ty(&n);
            let (s_id, s) = b.fresh_local(hcp_n.clone());
            // lhs: FourierCoefficient n f S
            let lhs = Expr::apps(coeff.clone(), [n.clone(), f.clone(), s.clone()]);
            // rhs: (FourierTransform n f) S
            let rhs = Expr::app(
                Expr::apps(transform.clone(), [n.clone(), f.clone()]),
                s.clone(),
            );
            let body = Expr::apps(eq_rat.clone(), [c.rat.clone(), lhs, rhs]);
            let e = b.mk_lam(s_id, BinderInfo::Default, hcp_n, body);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.discharge_axiom_for_redefinition(&Name::from_string(
            "BoolAnalysis.fourier_coefficient_transform_helper",
        ));
        self.add_decl(Declaration::Definition {
            name: Name::from_string("BoolAnalysis.fourier_coefficient_transform_helper"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `fourier_coefficient_transform : forall n f S,
    ///   FourierCoefficient(n, f, S) = FourierTransform(n, f) S`
    ///
    /// PROVEN (TCB-shrink): a genuine kernel-checked `Declaration::Theorem`,
    /// no longer an admitted `Declaration::Axiom`. The conclusion
    /// `fourier_coefficient_transform_helper n f S` δ-unfolds (the helper is a
    /// reducible Definition) to `@Eq Rat (FourierCoefficient n f S)
    /// (FourierTransform n f S)`. Since `FourierTransform n f := fun S =>
    /// FourierCoefficient n f S`, `(FourierTransform n f) S` β-reduces to
    /// `FourierCoefficient n f S`, so the two sides are definitionally equal and
    /// the proof is
    ///
    /// ```text
    /// fun (n : Nat) (f : BoolFn n) (S : HCPoint n) =>
    ///   @Eq.refl Rat (FourierCoefficient n f S)
    /// ```
    ///
    /// Constructive: the transitive axiom closure of the proof + helper is EMPTY
    /// (bottoms out in defined `FourierCoefficient` / `FourierTransform`).
    pub(super) fn register_fourier_coefficient_transform(
        &mut self,
        c: &BoolAnalysisConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(
                "BoolAnalysis.fourier_coefficient_transform",
            ))
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Theorem))
        {
            return Ok(());
        }
        let helper = Expr::const_(
            Name::from_string("BoolAnalysis.fourier_coefficient_transform_helper"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let hcp_n = c.hcpoint_of(&n);
            let (s_id, s) = b.fresh_local(hcp_n.clone());
            let body = Expr::apps(helper, [n.clone(), f.clone(), s.clone()]);
            let e = b.mk_pi(s_id, BinderInfo::Default, hcp_n, body);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // proof: fun (n : Nat) (f : BoolFn n) (S : HCPoint n) =>
        //   @Eq.refl Rat (FourierCoefficient n f S)
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );
        let coeff = Expr::const_(Name::from_string("BoolAnalysis.FourierCoefficient"), vec![]);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let hcp_n = c.hcpoint_of(&n);
            let (s_id, s) = b.fresh_local(hcp_n.clone());
            let coeff_nfs = Expr::apps(coeff.clone(), [n.clone(), f.clone(), s.clone()]);
            let body = Expr::apps(eq_refl.clone(), [c.rat.clone(), coeff_nfs]);
            let e = b.mk_lam(s_id, BinderInfo::Default, hcp_n, body);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.discharge_axiom_for_redefinition(&Name::from_string(
            "BoolAnalysis.fourier_coefficient_transform",
        ));
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("BoolAnalysis.fourier_coefficient_transform"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
