// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorem declarations for Boolean analysis and KKL formalization.
//!
//! Registers the kernel-level axiom surfaces for:
//! - S41: Parseval's identity
//! - S42: Influence/Fourier identity
//! - S46: Total influence identity
//! - S50: Bonami-Beckner hypercontractivity
//! - S43: KKL inequality
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
    /// `fun (x : HCPoint n) => Rat.mul (pm (f x)) (chi n S x)` — the `S`-Fourier
    /// correlation integrand `pm∘f · χ_S` for `f : BoolFn n`.
    fn parseval_amp_chi(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let pm = Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]);
        let chi = Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let hcpoint = Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            n.clone(),
        );
        let mut b = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = b.fresh_local(hcpoint.clone());
        let pm_fx = Expr::app(pm, Expr::app(f.clone(), x.clone()));
        let chi_sx = Expr::apps(chi, [n.clone(), s.clone(), x.clone()]);
        let body = Expr::apps(rat_mul, [pm_fx, chi_sx]);
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcpoint, body))
    }

    /// The genuine (unnormalized) Parseval equation body at `(n, f)`:
    /// `subsetSum n (fun S => (subsetSum n (pm∘f·χ_S))²)
    ///    = (2^n/1) · subsetSum n (fun x => pm(f x)·pm(f x))`.
    /// This is exactly `subsetSum_parseval_core n (fun x => pm (f x))` — the
    /// character orthonormality `Σ_S ⟨pm∘f, χ_S⟩² = 2^n·Σ_x (pm∘f)²`.
    fn parseval_body_eq(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let subset_sum = Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let rat_mk = Expr::const_(Name::from_string("Rat.mk"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let pm = Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]);
        let eq1 = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let hcpoint = Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            n.clone(),
        );

        let one = Expr::app(nat_succ.clone(), nat_zero);
        let two = Expr::app(nat_succ, one.clone());
        let pow2 = Expr::apps(nat_pow, [two, n.clone()]);
        let cube = Expr::apps(rat_mk, [Expr::app(int_of_nat, pow2), one]);

        // LHS: subsetSum n (fun S => (subsetSum n (amp_chi))²)
        let lhs_s_fn = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = b.fresh_local(hcpoint.clone());
            let inner = Expr::apps(
                subset_sum.clone(),
                [n.clone(), self.parseval_amp_chi(&b, n, f, &s)],
            );
            let body = Expr::apps(rat_mul.clone(), [inner.clone(), inner]);
            b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcpoint.clone(), body))
        };
        let lhs = Expr::apps(subset_sum.clone(), [n.clone(), lhs_s_fn]);

        // RHS: (2^n/1) · subsetSum n (fun x => pm(f x)·pm(f x))
        let a_sq_fn = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = b.fresh_local(hcpoint.clone());
            let pm_fx = Expr::app(pm.clone(), Expr::app(f.clone(), x.clone()));
            let body = Expr::apps(rat_mul.clone(), [pm_fx.clone(), pm_fx]);
            b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcpoint, body))
        };
        let rhs = Expr::apps(
            rat_mul,
            [cube, Expr::apps(subset_sum, [n.clone(), a_sq_fn])],
        );

        Expr::apps(eq1, [rat, lhs, rhs])
    }

    /// Helper proposition for S41: Parseval identity.
    ///
    /// RETIREMENT (RUNG 4): formerly an opaque `∀ n f, Prop` admitted axiom;
    /// now a reducible `Declaration::Definition` whose body is the GENUINE
    /// unnormalized Parseval equation (`parseval_body_eq`). DISCHARGES the bare
    /// axiom — the helper now carries real mathematical content, not an
    /// uninterpreted predicate.
    pub(super) fn register_parseval_identity_helper(
        &mut self,
        c: &BoolAnalysisConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.parseval_identity_helper");
        if self
            .get_const(&name)
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        // The body refers to subsetSum / pm / chi / Rat / Nat foundations.
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
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let body = self.parseval_body_eq(&b, &n, &f);
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

    /// S41 `parseval_identity : ∀ n f,
    ///   subsetSum n (fun S => (subsetSum n (pm∘f·χ_S))²)
    ///     = 2^n · subsetSum n (fun x => pm(f x)²)`.
    ///
    /// RETIREMENT (RUNG 4): formerly an admitted axiom; now a kernel-CHECKED
    /// `Declaration::Theorem`. The proof instantiates the constructive
    /// `subsetSum_parseval_core` at `a := fun x => pm (f x)`; the helper unfolds
    /// (reducible) to that conclusion. Empty admitted-axiom closure
    /// (`ProofQuality::Constructive`) — TCB shrinks by 2 (helper + identity).
    pub(super) fn register_parseval_identity(
        &mut self,
        c: &BoolAnalysisConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.parseval_identity");
        if self
            .get_const(&name)
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Theorem))
        {
            return Ok(());
        }
        self.register_parseval_identity_helper(c)?;
        self.register_subset_sum_parseval_core_theorem()?;

        let helper = Expr::const_(
            Name::from_string("BoolAnalysis.parseval_identity_helper"),
            vec![],
        );
        let core = Expr::const_(
            Name::from_string("BoolAnalysis.subsetSum_parseval_core"),
            vec![],
        );
        let pm = Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let body = Expr::apps(helper.clone(), [n.clone(), f.clone()]);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, body);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        // value: fun n f => subsetSum_parseval_core n (fun x => pm (f x)).
        //   Result type `core`'s conclusion at a := pm∘f, which is def-eq
        //   (helper reducible) to `helper n f`.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let hcpoint = Expr::app(
                Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
                n.clone(),
            );
            // a := fun (x : HCPoint n) => pm (f x)
            let amp = {
                let mut ab = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = ab.fresh_local(hcpoint.clone());
                let body = Expr::app(pm.clone(), Expr::app(f.clone(), x.clone()));
                ab.finish_child(ab.mk_lam(x_id, BinderInfo::Default, hcpoint, body))
            };
            let body = Expr::apps(core.clone(), [n.clone(), amp]);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, body);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
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

    /// Helper proposition for S42: influence/Fourier identity.
    ///
    /// TCB-shrink (Part 3): no longer a bare `∀ n f i, Prop` admitted axiom. The
    /// helper is now a genuine reducible `Declaration::Definition` carrying the
    /// EXACT statement body as a real `Eq Rat`:
    ///
    /// ```text
    /// influence_fourier_helper n f i :=
    ///   @Eq Rat
    ///     (Influence n f i)                                     -- Inf_i[f]
    ///     (subsetSum n (fun (S : HCPoint n) =>
    ///        Rat.mul (ind (S i))                                -- gate: i ∈ S ?
    ///                (Rat.mul (FourierCoefficient n f S)
    ///                         (FourierCoefficient n f S))))     -- Σ_{S∋i} f̂(S)²
    /// ```
    ///
    /// i.e. the spectral formula for coordinate influence, `Inf_i[f]
    /// = Σ_{S∋i} f̂(S)²` (O'Donnell, *Analysis of Boolean Functions*, Thm. 2.20).
    /// `Influence` and `FourierCoefficient` are CHECKED reducible Definitions,
    /// `ind : Bool → Rat` is the `{0,1}` embedding, `S i : Bool` is the
    /// membership bit (`S : HCPoint n = Fin n → Bool`), and `subsetSum` is the
    /// existing subset-sum carrier, so the body is a real proposition with
    /// content — not an uninterpreted predicate. DISCHARGES the bare helper
    /// axiom (TCB −1).
    ///
    /// The theorem `influence_fourier` asserting this `Eq` for all `n,f,i`
    /// remains an honest admitted axiom (see `register_influence_fourier`): a
    /// constructive discharge needs the discrete-derivative (`D_i f`) spectral
    /// expansion, which is genuinely new machinery, not regrouping.
    pub(super) fn register_influence_fourier_helper(
        &mut self,
        c: &BoolAnalysisConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.influence_fourier_helper");
        if self
            .get_const(&name)
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        // Body refers to Influence / subsetSum / FourierCoefficient / ind — all
        // registered by `init_boolean_analysis`. `subsetSum` re-registration is
        // idempotent.
        self.register_subset_sum()?;

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, _) = b.fresh_local(bool_fn_n.clone());
            let fin_n = c.fin_of(&n);
            let (i_id, _) = b.fresh_local(fin_n.clone());
            let e = b.mk_pi(i_id, BinderInfo::Default, fin_n, c.prop.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let eq_rat = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let influence = Expr::const_(Name::from_string("BoolAnalysis.Influence"), vec![]);
        let subset_sum = Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]);
        let fourier_coeff =
            Expr::const_(Name::from_string("BoolAnalysis.FourierCoefficient"), vec![]);
        let ind = Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let fin_n = c.fin_of(&n);
            let (i_id, i) = b.fresh_local(fin_n.clone());

            // LHS: Influence n f i
            let lhs = Expr::apps(influence.clone(), [n.clone(), f.clone(), i.clone()]);

            // RHS: subsetSum n (fun (S : HCPoint n) =>
            //   Rat.mul (ind (S i)) (Rat.mul (f̂(S)) (f̂(S))))
            let rhs_fn = {
                let mut rb = EnvDeclBuilder::child_of(&b);
                let hcpoint = c.hcpoint_of(&n);
                let (s_id, s) = rb.fresh_local(hcpoint.clone());
                // membership gate: ind (S i) — S i : Bool
                let gate = Expr::app(ind.clone(), Expr::app(s.clone(), i.clone()));
                let coeff = Expr::apps(fourier_coeff.clone(), [n.clone(), f.clone(), s.clone()]);
                let coeff_sq = Expr::apps(rat_mul.clone(), [coeff.clone(), coeff]);
                let term = Expr::apps(rat_mul.clone(), [gate, coeff_sq]);
                rb.finish_child(rb.mk_lam(s_id, BinderInfo::Default, hcpoint, term))
            };
            let rhs = Expr::apps(subset_sum.clone(), [n.clone(), rhs_fn]);

            let body = Expr::apps(eq_rat.clone(), [c.rat.clone(), lhs, rhs]);
            let e = b.mk_lam(i_id, BinderInfo::Default, fin_n, body);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
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

    /// S42 `influence_fourier : forall n f i, Inf_i[f] = Σ_{S∋i} f̂(S)²`
    ///
    /// HONEST ADMITTED AXIOM (Part 3). The helper it asserts is now a genuine
    /// `Eq Rat` (see `register_influence_fourier_helper`), so this is a real
    /// mathematical statement, not an opaque-predicate masquerade. A constructive
    /// discharge is genuinely NEW machinery (not a regrouping of existing
    /// lemmas): it requires the discrete-derivative / Fourier-shift apparatus —
    ///
    /// 1. the derivative operator `D_i f` and its spectral action
    ///    `\widehat{D_i f}(S) = if i ∈ S then f̂(S) else 0`,
    /// 2. the identity `Inf_i[f] = E[(D_i f)²]` (influence as derivative energy),
    /// 3. Parseval applied to `D_i f`, collapsing `E[(D_i f)²]` to
    ///    `Σ_S \widehat{D_i f}(S)² = Σ_{S∋i} f̂(S)²`.
    ///
    /// None of `D_i`, its spectral lemma, or the Boolean-derivative Parseval
    /// instance exist yet, so this is correctly DEFERRED rather than forced.
    /// Until they land the axiom is the sound discharge: it asserts a true
    /// identity and cannot derive `False`.
    pub(super) fn register_influence_fourier(
        &mut self,
        c: &BoolAnalysisConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.influence_fourier");
        // Already a kernel-CHECKED Theorem? Nothing to do.
        if self
            .get_const(&name)
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Theorem))
        {
            return Ok(());
        }
        // The full constructive assembly (subsetSum_influence_unnorm + the
        // Expect=Σ/2^n + f̂=A/2^n normalization). All idempotent.
        self.register_subset_sum_influence_unnorm()?;
        self.register_subset_sum_smul_theorem()?;

        let helper = Expr::const_(
            Name::from_string("BoolAnalysis.influence_fourier_helper"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let fin_n = c.fin_of(&n);
            let (i_id, i) = b.fresh_local(fin_n.clone());
            let body = Expr::apps(helper, [n.clone(), f.clone(), i.clone()]);
            let e = b.mk_pi(i_id, BinderInfo::Default, fin_n, body);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        // The proof value: `Influence n f i = subsetSum n (fun S => ind(S i)·f̂(S)²)`,
        // def-eq to `influence_fourier_helper n f i` (helper reducible). Built in
        // `boolean_analysis_influence_chain.rs` (`influence_fourier_value`).
        let value = self.influence_fourier_proof_value();
        // Discharge the legacy admitted axiom (if present) and install the Theorem.
        self.discharge_axiom_for_redefinition(&name);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Helper proposition for S46: total influence identity.
    ///
    /// PROVEN (TCB-shrink): no longer a bare `Declaration::Axiom`. The helper is
    /// now a genuine reducible `Declaration::Definition` carrying the EXACT
    /// statement body as a real `Eq`:
    ///
    /// ```text
    /// total_influence_identity_helper n f :=
    ///   @Eq Rat (TotalInfluence n f) (Fin.sum n (fun (i : Fin n) => Influence n f i))
    /// ```
    ///
    /// i.e. `I[f] = Σ_i Inf_i[f]` (O'Donnell, *Analysis of Boolean Functions*,
    /// Def. 2.27). Because `TotalInfluence` is DEFINED as exactly that sum
    /// (`register_total_influence`), the two sides are definitionally equal, so
    /// `register_total_influence_identity` discharges it by `@Eq.refl`. The body
    /// bottoms out in the defined `TotalInfluence` / `Fin.sum` / `Influence`
    /// (each with an EMPTY admitted-axiom closure), so the resulting theorem is
    /// `ProofQuality::Constructive`.
    pub(super) fn register_total_influence_identity_helper(
        &mut self,
        c: &BoolAnalysisConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(
                "BoolAnalysis.total_influence_identity_helper",
            ))
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, _) = b.fresh_local(bool_fn_n.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, c.prop.clone());
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // value: fun (n : Nat) (f : BoolFn n) =>
        //   @Eq Rat (TotalInfluence n f) (Fin.sum n (fun i => Influence n f i))
        let eq_rat = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let total = Expr::const_(Name::from_string("BoolAnalysis.TotalInfluence"), vec![]);
        let influence = Expr::const_(Name::from_string("BoolAnalysis.Influence"), vec![]);
        let fin_sum = Expr::const_(Name::from_string("Fin.sum"), vec![]);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let fin_n = c.fin_of(&n);
            // lhs: TotalInfluence n f
            let lhs = Expr::apps(total.clone(), [n.clone(), f.clone()]);
            // rhs: Fin.sum n (fun (i : Fin n) => Influence n f i)
            let summand = {
                let (i_id, i) = b.fresh_local(fin_n.clone());
                let body = Expr::apps(influence.clone(), [n.clone(), f.clone(), i]);
                b.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), body)
            };
            let rhs = Expr::apps(fin_sum.clone(), [n.clone(), summand]);
            let body = Expr::apps(eq_rat.clone(), [c.rat.clone(), lhs, rhs]);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, body);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.discharge_axiom_for_redefinition(&Name::from_string(
            "BoolAnalysis.total_influence_identity_helper",
        ));
        self.add_decl(Declaration::Definition {
            name: Name::from_string("BoolAnalysis.total_influence_identity_helper"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// S46 `total_influence_identity : forall n f, I(f) = Σ_i Inf_i(f)`
    ///
    /// PROVEN (TCB-shrink): a genuine kernel-checked `Declaration::Theorem`,
    /// no longer an admitted `Declaration::Axiom`. The conclusion
    /// `total_influence_identity_helper n f` δ-unfolds (the helper is a reducible
    /// Definition) to `@Eq Rat (TotalInfluence n f) (Fin.sum n (fun i => Influence
    /// n f i))`. Since `TotalInfluence` is DEFINED as exactly that sum, the two
    /// sides are definitionally equal, so the proof is
    ///
    /// ```text
    /// fun (n : Nat) (f : BoolFn n) => @Eq.refl Rat (TotalInfluence n f)
    /// ```
    ///
    /// which the kernel accepts because `Eq (TotalInfluence n f) (TotalInfluence
    /// n f)` is def-eq to the unfolded helper goal. Constructive: the transitive
    /// axiom closure of the proof + helper is EMPTY (bottoms out in defined
    /// `TotalInfluence` / `Fin.sum` / `Influence`, all admitted-axiom-free).
    pub(super) fn register_total_influence_identity(
        &mut self,
        c: &BoolAnalysisConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("BoolAnalysis.total_influence_identity"))
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Theorem))
        {
            return Ok(());
        }
        let helper = Expr::const_(
            Name::from_string("BoolAnalysis.total_influence_identity_helper"),
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

        // proof: fun (n : Nat) (f : BoolFn n) => @Eq.refl Rat (TotalInfluence n f)
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );
        let total = Expr::const_(Name::from_string("BoolAnalysis.TotalInfluence"), vec![]);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let total_nf = Expr::apps(total.clone(), [n.clone(), f.clone()]);
            let body = Expr::apps(eq_refl.clone(), [c.rat.clone(), total_nf]);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, body);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.discharge_axiom_for_redefinition(&Name::from_string(
            "BoolAnalysis.total_influence_identity",
        ));
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("BoolAnalysis.total_influence_identity"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Bonami-Beckner side conditions — the (2,4)-hypercontractivity regime.
    ///
    /// RETIREMENT (bonami run 16): formerly an opaque `∀ ρ p q, Prop` admitted
    /// axiom; now a reducible `Declaration::Definition` whose body is the GENUINE
    /// (2,4) condition predicate
    /// `conditions ρ p q := (p = 2) ∧ ((q = 4) ∧ (3·(ρ·ρ) ≤ 1))`
    /// (`2 := Rat.mk (Int.ofNat 2) 1`, `4 := Rat.mk (Int.ofNat 4) 1`). DISCHARGES
    /// the bare axiom — the conditions now carry real content (the precise
    /// exponent pair + noise bound the `hc24_core` proof consumes), not an
    /// uninterpreted predicate.
    pub(super) fn register_bonami_beckner_conditions(
        &mut self,
        c: &BoolAnalysisConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.bonami_beckner_conditions");
        if self
            .get_const(&name)
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (rho_id, _) = b.fresh_local(c.rat.clone());
            let (p_id, _) = b.fresh_local(c.rat.clone());
            let (q_id, _) = b.fresh_local(c.rat.clone());
            let e = b.mk_pi(q_id, BinderInfo::Default, c.rat.clone(), c.prop.clone());
            let e = b.mk_pi(p_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (rho_id, rho) = b.fresh_local(c.rat.clone());
            let (p_id, p) = b.fresh_local(c.rat.clone());
            let (q_id, q) = b.fresh_local(c.rat.clone());
            let body = bonami_conditions_body(c, &rho, &p, &q);
            let e = b.mk_lam(q_id, BinderInfo::Default, c.rat.clone(), body);
            let e = b.mk_lam(p_id, BinderInfo::Default, c.rat.clone(), e);
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

    /// S50 Bonami-Beckner conclusion body.
    ///
    /// RETIREMENT (bonami run 16): formerly an opaque `∀ n f ρ p q, Prop`
    /// admitted axiom; now a reducible `Declaration::Definition` whose body is
    /// the GENUINE (2,4)-hypercontractivity operator bound — the `hc24_core`
    /// conclusion at `F := pm∘f`:
    ///
    /// ```text
    /// helper n f ρ p q :=
    ///   Σ_{2^n} pow4(noiseFn ρ n (pm∘f) jx)
    ///     ≤ (Rat.powNat 8 n) · sq(Σ_{2^n} sq((pm∘f)(hcDecode n jx)))
    /// ```
    ///
    /// The phantom exponent binders `p`, `q` are preserved (the regime they pin
    /// lives in `bonami_beckner_conditions`). `noiseFn ρ n (pm∘f)` is the
    /// (un-normalized) noise operator `2^n·T_ρ` applied to the real-valued
    /// embedding of `f`, so the body is a real `LE.le` proposition with content,
    /// not an uninterpreted predicate. DISCHARGES the bare helper axiom.
    pub(super) fn register_bonami_beckner_helper(
        &mut self,
        c: &BoolAnalysisConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.bonami_beckner_helper");
        if self
            .get_const(&name)
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        // Body refers to noiseFn / hcDecode / pm / Rat.powNat — pulled in by the
        // hc24_core base statement deps.
        self.init_boolean_analysis_hc24_core_base()?;

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, _) = b.fresh_local(bool_fn_n.clone());
            let (rho_id, _) = b.fresh_local(c.rat.clone());
            let (p_id, _) = b.fresh_local(c.rat.clone());
            let (q_id, _) = b.fresh_local(c.rat.clone());
            let e = b.mk_pi(q_id, BinderInfo::Default, c.rat.clone(), c.prop.clone());
            let e = b.mk_pi(p_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        let value = {
            let hc = super::boolean_analysis_hc24_core_base::Hc24Consts::new();
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let (rho_id, rho) = b.fresh_local(c.rat.clone());
            let (p_id, _) = b.fresh_local(c.rat.clone());
            let (q_id, _) = b.fresh_local(c.rat.clone());
            // F := fun (x : HCPoint n) => pm (f x)
            let pm_f = bonami_pm_f(c, &b, &n, &f);
            let body =
                super::boolean_analysis_hc24_core_base::hc24_core_concl(&hc, &b, &rho, &n, &pm_f);
            let e = b.mk_lam(q_id, BinderInfo::Default, c.rat.clone(), body);
            let e = b.mk_lam(p_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
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

    /// S50 `bonami_beckner : ∀ n f ρ p q, conditions ρ p q → helper n f ρ p q`
    /// — the (2,4)-hypercontractivity operator bound.
    ///
    /// RETIREMENT (bonami run 16): formerly an admitted axiom; now a kernel-
    /// CHECKED `Declaration::Theorem`. The proof unpacks the `3·(ρ·ρ) ≤ 1` noise
    /// bound from the conditions (`And.right ∘ And.right`, the conditions being
    /// reducibly `(p=2) ∧ ((q=4) ∧ (3ρ²≤1))`) and feeds it to `hc24_core` at
    /// `F := pm∘f`:
    ///
    /// ```text
    /// fun n f ρ p q h => hc24_core ρ n (pm∘f) (And.right (And.right h))
    /// ```
    ///
    /// whose result type is `hc24_core`'s conclusion at `pm∘f`, def-eq (helper
    /// reducible) to `helper n f ρ p q`. Empty admitted-axiom closure
    /// (`ProofQuality::Constructive`) — TCB shrinks by 3 (conditions + helper +
    /// theorem). The full (2,4) operator induction is `hc24_core`; this is its
    /// `BoolFn`-level corollary.
    pub(super) fn register_bonami_beckner(
        &mut self,
        c: &BoolAnalysisConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.bonami_beckner");
        if self
            .get_const(&name)
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Theorem))
        {
            return Ok(());
        }
        self.register_bonami_beckner_conditions(c)?;
        self.register_bonami_beckner_helper(c)?;
        self.init_boolean_analysis_hc24_core()?;

        let conditions = Expr::const_(
            Name::from_string("BoolAnalysis.bonami_beckner_conditions"),
            vec![],
        );
        let helper = Expr::const_(
            Name::from_string("BoolAnalysis.bonami_beckner_helper"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let (rho_id, rho) = b.fresh_local(c.rat.clone());
            let (p_id, p) = b.fresh_local(c.rat.clone());
            let (q_id, q) = b.fresh_local(c.rat.clone());
            let cond = Expr::apps(conditions.clone(), [rho.clone(), p.clone(), q.clone()]);
            let concl = Expr::apps(
                helper.clone(),
                [n.clone(), f.clone(), rho.clone(), p.clone(), q.clone()],
            );
            let (h_id, _) = b.fresh_local(cond.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, cond, concl);
            let e = b.mk_pi(q_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        // value: fun n f ρ p q h => hc24_core ρ n (pm∘f) (And.right (And.right h)).
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let (rho_id, rho) = b.fresh_local(c.rat.clone());
            let (p_id, p) = b.fresh_local(c.rat.clone());
            let (q_id, q) = b.fresh_local(c.rat.clone());
            let cond = Expr::apps(conditions, [rho.clone(), p.clone(), q.clone()]);
            let (h_id, h) = b.fresh_local(cond.clone());

            // Extract `3·(ρ·ρ) ≤ 1` from the conditions And-chain.
            let h_noise = bonami_extract_noise_bound(c, &rho, &p, &q, h);
            // F := pm∘f.
            let pm_f = bonami_pm_f(c, &b, &n, &f);
            let hc24 = Expr::const_(Name::from_string("BoolAnalysis.hc24_core"), vec![]);
            let body = Expr::apps(hc24, [rho.clone(), n.clone(), pm_f, h_noise]);

            let e = b.mk_lam(h_id, BinderInfo::Default, cond, body);
            let e = b.mk_lam(q_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(p_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
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

    /// The FAITHFUL **UNCONDITIONAL** KKL max-influence body at `(n, f)` —
    /// BYTE-IDENTICAL to the `(k, …) → ∃ i, …` tail of
    /// `kkl_exists_max_influence_uncond`'s type with `n, f` fixed (so its
    /// instance discharges the proof). Returns
    ///
    /// ```text
    /// ∀ (k : Nat),
    ///   0 < n →                                   -- KKL is about n ≥ 1 variables
    ///   (k+1)·((natCast(k+1)·9^k + 1)²) ≤ (n + n) →   -- threshold (Rat-stated)
    ///   (∀ i, 0 ≤ Inf_i) →                        -- influences nonneg (always true)
    ///   ∃ i, (k+1)·Var ≤ (n·Inf_i)+(n·Inf_i)
    /// ```
    ///
    /// No `d`, no small-influence side condition — the GENUINE unconditional KKL
    /// max-influence inequality (O'Donnell Thm 9.28): under the threshold
    /// `(k+1)·((k+1)·9^k+1)² ≤ 2n` (non-vacuous, holds for `k` up to `~log₈₁ n`),
    /// SOME coordinate `i` carries influence `Inf_i ≥ ((k+1)·Var)/(2n)`.
    fn kkl_faithful_body(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let kk = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let nat = kk("Nat");
        let nat_zero = kk("Nat.zero");
        let nat_succ = kk("Nat.succ");
        let int_of_nat = kk("Int.ofNat");
        let rat_mk = kk("Rat.mk");
        let rat_of_nat = kk("Rat.ofNat");
        let rat_mul = kk("Rat.mul");
        let rat_add = kk("Rat.add");
        let rat_le = kk("Rat.le");
        let rat_zero = kk("Rat.zero");
        let rat_one = kk("Rat.one");
        let pow_nat = kk("Rat.powNat");
        let fin = kk("Fin");
        let influence = kk("BoolAnalysis.Influence");
        let variance = kk("BoolAnalysis.Variance");
        let u1 = Level::succ(Level::zero());

        let succ = |x: &Expr| Expr::app(nat_succ.clone(), x.clone());
        let one_nat = succ(&nat_zero);
        let nat_lit = |v: u64| {
            let mut e = nat_zero.clone();
            for _ in 0..v {
                e = Expr::app(nat_succ.clone(), e);
            }
            e
        };
        let mul = |a: Expr, b: Expr| Expr::apps(rat_mul.clone(), [a, b]);
        let add = |a: Expr, b: Expr| Expr::apps(rat_add.clone(), [a, b]);
        let le = |a: Expr, b: Expr| Expr::apps(rat_le.clone(), [a, b]);
        let natcast = |m: &Expr| {
            Expr::apps(
                rat_mk.clone(),
                [Expr::app(int_of_nat.clone(), m.clone()), one_nat.clone()],
            )
        };
        let infl = |i: &Expr| Expr::apps(influence.clone(), [n.clone(), f.clone(), i.clone()]);
        let fin_n = Expr::app(fin.clone(), n.clone());
        let var = Expr::apps(variance.clone(), [n.clone(), f.clone()]);

        let mut b = EnvDeclBuilder::child_of(parent);
        let (k_id, k) = b.fresh_local(nat.clone());

        let kcast = natcast(&succ(&k)); // K := natCast(k+1)
        let nn = natcast(n); // Nn := natCast n
        let two_nn = add(nn.clone(), nn.clone()); // 2n := Nn+Nn
                                                  // P := K·9^k ; Q := P+1 ; QQ := Q·Q  (BYTE-MATCH uncond's UncondConsts).
        let p9 = Expr::apps(
            pow_nat.clone(),
            [Expr::app(rat_of_nat.clone(), nat_lit(9)), k.clone()],
        );
        let p = mul(kcast.clone(), p9.clone());
        let q = add(p.clone(), rat_one.clone());
        let qq = mul(q.clone(), q.clone());

        // hpos : Nat.lt 0 n  ≡ Nat.le (succ 0) n.
        let hpos_ty = Expr::apps(
            Expr::const_(Name::from_string("Nat.le"), vec![]),
            [succ(&nat_zero), n.clone()],
        );
        let (hpos_id, _) = b.fresh_local(hpos_ty.clone());
        // hthr : (k+1)·QQ ≤ Nn+Nn.
        let hthr_ty = le(mul(kcast.clone(), qq.clone()), two_nn.clone());
        let (hthr_id, _) = b.fresh_local(hthr_ty.clone());
        // h0 : ∀ i, 0 ≤ Inf_i.
        let h0_ty = {
            let mut d2 = EnvDeclBuilder::child_of(&b);
            let (i_id, i) = d2.fresh_local(fin_n.clone());
            let body = le(rat_zero.clone(), infl(&i));
            d2.finish_child(d2.mk_pi(i_id, BinderInfo::Default, fin_n.clone(), body))
        };
        let (h0_id, _) = b.fresh_local(h0_ty.clone());

        // ∃ i, (k+1)·Var ≤ (n·Inf_i)+(n·Inf_i).
        let k_v = mul(kcast.clone(), var.clone());
        let pred = {
            let mut d2 = EnvDeclBuilder::child_of(&b);
            let (i_id, i) = d2.fresh_local(fin_n.clone());
            let g_i = mul(nn.clone(), infl(&i));
            let body = le(k_v.clone(), add(g_i.clone(), g_i));
            d2.finish_child(d2.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), body))
        };
        let concl = Expr::apps(
            Expr::const_(Name::from_string("Exists"), vec![u1]),
            [fin_n.clone(), pred],
        );

        let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, concl);
        let e = b.mk_pi(hthr_id, BinderInfo::Default, hthr_ty, e);
        let e = b.mk_pi(hpos_id, BinderInfo::Default, hpos_ty, e);
        b.finish_child(b.mk_pi(k_id, BinderInfo::Default, nat.clone(), e))
    }

    /// FAITHFUL helper proposition for S43: KKL max-influence inequality.
    ///
    /// RETIREMENT (KKL run): formerly an admitted `Declaration::Axiom` with the
    /// vacuous body `c.prop` (an opaque `BoolFn n → Prop` placeholder); now a
    /// reducible `Declaration::Definition` carrying the GENUINE **UNCONDITIONAL**
    /// max-influence KKL statement — under the explicit-constant threshold
    /// `(k+1)·((k+1)·9^k + 1)² ≤ 2n` ALONE (no small-influence side condition),
    /// SOME coordinate `i` carries influence `Inf_i ≥ ((k+1)·Var)/(2·n)`:
    ///
    /// ```text
    /// kkl_inequality_helper n f :=
    ///   ∀ (k : Nat), 0 < n →
    ///     (k+1)·((natCast(k+1)·9^k + 1)²) ≤ (n + n) →
    ///     (∀ i, 0 ≤ Inf_i) →
    ///     ∃ i, (k+1)·Var ≤ (n·Inf_i)+(n·Inf_i)
    /// ```
    ///
    /// Genuine non-vacuous `∃ i` bound (the threshold is satisfiable for `k` up to
    /// `~log₈₁ n`), explicit positive constants (`k+1`, the factor 2 via the
    /// doubled summand, `n`). The small-influence `d` regime is discharged
    /// internally by the large-influence dichotomy + `Var ≤ 1`
    /// ([`kkl_exists_max_influence_uncond`]). DISCHARGES the bare axiom.
    pub(super) fn register_kkl_inequality_helper(
        &mut self,
        c: &BoolAnalysisConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("BoolAnalysis.kkl_inequality_helper"))
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        // Body atoms (Influence/Variance/powNat/natCast) — pulled in by the
        // unconditional maxinf chain; ensure present for the def-body typecheck.
        self.register_kkl_exists_max_influence_uncond()?;

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, _) = b.fresh_local(bool_fn_n.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, c.prop.clone());
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let body = self.kkl_faithful_body(&b, &n, &f);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, body);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.discharge_axiom_for_redefinition(&Name::from_string(
            "BoolAnalysis.kkl_inequality_helper",
        ));
        self.add_decl(Declaration::Definition {
            name: Name::from_string("BoolAnalysis.kkl_inequality_helper"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// S43 `kkl_inequality : ∀ n f, kkl_inequality_helper n f`.
    ///
    /// RETIREMENT (KKL run): formerly an admitted `Declaration::Axiom`; now a
    /// kernel-CHECKED `Declaration::Theorem`. The proof unpacks the faithful
    /// **unconditional** helper body (the `∀ k, 0<n → threshold → (∀i 0≤Inf_i) →
    /// ∃ i, …` statement) and discharges it with `kkl_exists_max_influence_uncond`:
    ///
    /// ```text
    /// fun n f k hpos hthr h0 =>
    ///   kkl_exists_max_influence_uncond n k f hpos hthr h0
    /// ```
    ///
    /// whose result type IS the helper body (helper reducible). Empty admitted-
    /// axiom closure (`ProofQuality::Constructive`); the name is now honestly
    /// earned — UNCONDITIONAL KKL, no small-influence overclaim.
    pub(super) fn register_kkl_inequality(
        &mut self,
        c: &BoolAnalysisConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("BoolAnalysis.kkl_inequality"))
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Theorem))
        {
            return Ok(());
        }
        self.register_kkl_inequality_helper(c)?;
        self.register_kkl_exists_max_influence_uncond()?;

        let helper = Expr::const_(
            Name::from_string("BoolAnalysis.kkl_inequality_helper"),
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
        // value: fun n f => the helper body's introduction via kkl_exists_max_influence.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            // The helper body's binders, re-bound and forwarded to maxinf.
            let inner = self.kkl_inequality_proof_body(&b, &n, &f);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, inner);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.discharge_axiom_for_redefinition(&Name::from_string("BoolAnalysis.kkl_inequality"));
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("BoolAnalysis.kkl_inequality"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `fun (k)(hpos)(hthr)(h0) =>
    ///    kkl_exists_max_influence_uncond n k f hpos hthr h0`
    /// — the proof of the faithful UNCONDITIONAL helper body at fixed `(n, f)`.
    /// Binder spellings BYTE-MATCH `kkl_faithful_body` so its type IS the helper
    /// body, and the application arguments BYTE-MATCH
    /// `kkl_exists_max_influence_uncond`'s `(n, k, f, hpos, hthr, h0)` order.
    fn kkl_inequality_proof_body(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let kk = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let nat = kk("Nat");
        let nat_zero = kk("Nat.zero");
        let nat_succ = kk("Nat.succ");
        let int_of_nat = kk("Int.ofNat");
        let rat_mk = kk("Rat.mk");
        let rat_of_nat = kk("Rat.ofNat");
        let rat_mul = kk("Rat.mul");
        let rat_add = kk("Rat.add");
        let rat_le = kk("Rat.le");
        let rat_zero = kk("Rat.zero");
        let rat_one = kk("Rat.one");
        let pow_nat = kk("Rat.powNat");
        let fin = kk("Fin");
        let influence = kk("BoolAnalysis.Influence");

        let succ = |x: &Expr| Expr::app(nat_succ.clone(), x.clone());
        let one_nat = succ(&nat_zero);
        let nat_lit = |v: u64| {
            let mut e = nat_zero.clone();
            for _ in 0..v {
                e = Expr::app(nat_succ.clone(), e);
            }
            e
        };
        let mul = |a: Expr, b: Expr| Expr::apps(rat_mul.clone(), [a, b]);
        let add = |a: Expr, b: Expr| Expr::apps(rat_add.clone(), [a, b]);
        let le = |a: Expr, b: Expr| Expr::apps(rat_le.clone(), [a, b]);
        let natcast = |m: &Expr| {
            Expr::apps(
                rat_mk.clone(),
                [Expr::app(int_of_nat.clone(), m.clone()), one_nat.clone()],
            )
        };
        let infl = |i: &Expr| Expr::apps(influence.clone(), [n.clone(), f.clone(), i.clone()]);
        let fin_n = Expr::app(fin.clone(), n.clone());

        let mut b = EnvDeclBuilder::child_of(parent);
        let (k_id, k) = b.fresh_local(nat.clone());

        let kcast = natcast(&succ(&k)); // K := natCast(k+1)
        let nn = natcast(n); // Nn := natCast n
        let two_nn = add(nn.clone(), nn.clone());
        let p9 = Expr::apps(
            pow_nat.clone(),
            [Expr::app(rat_of_nat.clone(), nat_lit(9)), k.clone()],
        );
        let p = mul(kcast.clone(), p9.clone());
        let q = add(p.clone(), rat_one.clone());
        let qq = mul(q.clone(), q.clone());

        let hpos_ty = Expr::apps(
            Expr::const_(Name::from_string("Nat.le"), vec![]),
            [succ(&nat_zero), n.clone()],
        );
        let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());
        let hthr_ty = le(mul(kcast.clone(), qq.clone()), two_nn.clone());
        let (hthr_id, hthr) = b.fresh_local(hthr_ty.clone());
        let h0_ty = {
            let mut d2 = EnvDeclBuilder::child_of(&b);
            let (i_id, i) = d2.fresh_local(fin_n.clone());
            let body = le(rat_zero.clone(), infl(&i));
            d2.finish_child(d2.mk_pi(i_id, BinderInfo::Default, fin_n.clone(), body))
        };
        let (h0_id, h0) = b.fresh_local(h0_ty.clone());

        // kkl_exists_max_influence_uncond n k f hpos hthr h0.
        let body = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.kkl_exists_max_influence_uncond"),
                vec![],
            ),
            [n.clone(), k.clone(), f.clone(), hpos, hthr, h0],
        );

        let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, body);
        let e = b.mk_lam(hthr_id, BinderInfo::Default, hthr_ty, e);
        let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, e);
        b.finish_child(b.mk_lam(k_id, BinderInfo::Default, nat.clone(), e))
    }
}

// ─── Bonami-Beckner retirement helpers (bonami run 16) ──────────────────────

/// The rational literal `Rat.mk (Int.ofNat k) 1`.
fn rat_lit(k: u64) -> Expr {
    let mut nat = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    for _ in 0..k {
        nat = Expr::app(succ.clone(), nat);
    }
    let nat_one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mk"), vec![]),
        [
            Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), nat),
            nat_one,
        ],
    )
}

/// `@Eq Rat a b`.
fn eq_rat(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [Expr::const_(Name::from_string("Rat"), vec![]), a, b],
    )
}

/// `LE.le.{0} Rat instLERat a b` — the same `Rat.le` representation `hc24_core`'s
/// `3·(ρ·ρ) ≤ 1` hypothesis uses (`OrderConsts.rat_le`).
fn rat_le(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
        [
            Expr::const_(Name::from_string("Rat"), vec![]),
            Expr::const_(Name::from_string("instLERat"), vec![]),
            a,
            b,
        ],
    )
}

/// `3·(ρ·ρ) ≤ 1`  (`3 := (1+1)+1`, matching `HcBoundsConsts.three`).
fn three_rho_sq_le_one(rho: &Expr) -> Expr {
    let one = Expr::const_(Name::from_string("Rat.one"), vec![]);
    let add =
        |a: Expr, b: Expr| Expr::apps(Expr::const_(Name::from_string("Rat.add"), vec![]), [a, b]);
    let mul =
        |a: Expr, b: Expr| Expr::apps(Expr::const_(Name::from_string("Rat.mul"), vec![]), [a, b]);
    let two = add(one.clone(), one.clone());
    let three = add(two, one.clone());
    let rho_sq = mul(rho.clone(), rho.clone());
    rat_le(mul(three, rho_sq), one)
}

/// `And A B`.
fn and_prop(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("And"), vec![]), [a, b])
}

/// The conditions body `(p = 2) ∧ ((q = 4) ∧ (3·(ρ·ρ) ≤ 1))`.
fn bonami_conditions_body(_c: &BoolAnalysisConsts, rho: &Expr, p: &Expr, q: &Expr) -> Expr {
    let p_eq_2 = eq_rat(p.clone(), rat_lit(2));
    let q_eq_4 = eq_rat(q.clone(), rat_lit(4));
    let noise = three_rho_sq_le_one(rho);
    and_prop(p_eq_2, and_prop(q_eq_4, noise))
}

/// `@And.right A B h : B` for `h : And A B`.
fn and_right(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.right"), vec![]),
        [a, b, h],
    )
}

/// Extract `3·(ρ·ρ) ≤ 1` from `h : conditions ρ p q` (def-eq to the And-chain):
/// `And.right (q=4) (3ρ²≤1) (And.right (p=2) ((q=4)∧(3ρ²≤1)) h)`.
fn bonami_extract_noise_bound(
    _c: &BoolAnalysisConsts,
    rho: &Expr,
    p: &Expr,
    q: &Expr,
    h: Expr,
) -> Expr {
    let p_eq_2 = eq_rat(p.clone(), rat_lit(2));
    let q_eq_4 = eq_rat(q.clone(), rat_lit(4));
    let noise = three_rho_sq_le_one(rho);
    let inner = and_prop(q_eq_4.clone(), noise.clone());
    // h : (p=2) ∧ inner  ⟹  And.right gives inner
    let h_inner = and_right(p_eq_2, inner, h);
    // h_inner : (q=4) ∧ noise  ⟹  And.right gives noise
    and_right(q_eq_4, noise, h_inner)
}

/// `F := fun (x : HCPoint n) => pm (f x)` — the real-valued `±1` embedding of
/// `f : BoolFn n`, the bridge from `BoolFn` to `HCPoint n → Rat`.
fn bonami_pm_f(c: &BoolAnalysisConsts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
    let pm = Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]);
    let hcpoint = c.hcpoint_of(n);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = b.fresh_local(hcpoint.clone());
    let body = Expr::app(pm, Expr::app(f.clone(), x.clone()));
    b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcpoint, body))
}

#[cfg(test)]
mod parseval_retirement_tests {
    use super::*;
    use crate::env::types::ConstantKind;

    #[test]
    fn test_parseval_identity_is_checked_theorem() {
        let mut env = Environment::new();
        // The Parseval retirement is now part of the always-on init chain.
        env.init_boolean_analysis().expect("init ba");
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.parseval_identity"))
            .expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "parseval must be Theorem");
        let hinfo = env
            .get_const(&Name::from_string("BoolAnalysis.parseval_identity_helper"))
            .expect("helper registered");
        assert_eq!(
            hinfo.kind,
            ConstantKind::Definition,
            "helper must be reducible Definition"
        );
    }

    #[test]
    fn test_bonami_beckner_is_checked_theorem() {
        use crate::env::ProofQuality;
        use crate::tc::TypeChecker;
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis().expect("init ba");

        // conditions + helper are reducible Definitions (retired axioms).
        for n in [
            "BoolAnalysis.bonami_beckner_conditions",
            "BoolAnalysis.bonami_beckner_helper",
        ] {
            let info = env.get_const(&Name::from_string(n)).expect("registered");
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{n} must be Definition"
            );
        }

        // bonami_beckner is a kernel-CHECKED Theorem reducing to hc24_core.
        let name = Name::from_string("BoolAnalysis.bonami_beckner");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "bonami_beckner must be Theorem"
        );
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("bonami_beckner proof must check against its type");
        let deps = env.axiom_deps(&name).expect("deps");
        let dep_names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(
            dep_names.is_empty(),
            "bonami_beckner must be axiom-free, got {dep_names:?}"
        );
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "bonami_beckner must be Constructive"
        );
    }

    #[test]
    fn test_kkl_inequality_is_checked_theorem() {
        use crate::env::ProofQuality;
        use crate::tc::TypeChecker;
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis().expect("init ba");

        // helper is a reducible Definition (retired axiom) carrying the genuine
        // max-influence KKL statement.
        let hinfo = env
            .get_const(&Name::from_string("BoolAnalysis.kkl_inequality_helper"))
            .expect("helper registered");
        assert_eq!(
            hinfo.kind,
            ConstantKind::Definition,
            "kkl_inequality_helper must be reducible Definition"
        );

        // kkl_inequality is a kernel-CHECKED constructive Theorem with empty
        // admitted-axiom closure.
        let name = Name::from_string("BoolAnalysis.kkl_inequality");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "kkl_inequality must be Theorem"
        );
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("kkl_inequality proof must check against its type");
        let deps = env.axiom_deps(&name).expect("deps");
        let dep_names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(
            dep_names.is_empty(),
            "kkl_inequality must be axiom-free, got {dep_names:?}"
        );
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "kkl_inequality must be Constructive"
        );
    }
}
