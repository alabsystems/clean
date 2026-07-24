// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for Boolean analysis and KKL formalization.
//!
//! Registers the foundational types and theorem surfaces needed to state:
//! - Parseval's identity (S41)
//! - Influence/Fourier identity (S42)
//! - KKL inequality (S43)
//! - Total influence/Fourier identity (S46)
//! - Bonami-Beckner hypercontractivity (S50)
//!
//! Type and operation definitions live here; theorem registrations are in
//! `boolean_analysis_theorems.rs`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants used across all Boolean analysis declarations.
pub(super) struct BoolAnalysisConsts {
    pub(super) nat: Expr,
    pub(super) bool_: Expr,
    pub(super) rat: Expr,
    pub(super) fin: Expr,
    pub(super) type0: Expr,
    pub(super) prop: Expr,
    pub(super) bool_fn: Expr,
    pub(super) fourier_coeff: Expr,
}

impl BoolAnalysisConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            bool_fn: Expr::const_(Name::from_string("BoolAnalysis.BoolFn"), vec![]),
            fourier_coeff: Expr::const_(Name::from_string("BoolAnalysis.FourierCoeff"), vec![]),
        }
    }

    pub(super) fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }

    pub(super) fn fourier_coeff_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fourier_coeff.clone(), n.clone())
    }

    pub(super) fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }

    /// `BoolAnalysis.HCPoint n` — a cube point `Fin n -> Bool`.
    pub(super) fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            n.clone(),
        )
    }
}

/// `Rat.mk (Int.ofNat k) 1` — the rational numeral `k/1` for a small `k`
/// (built as a `Nat.succ` tower). Used by the Stage-2 Fourier-quantity bodies.
fn rat_nat_lit(k: u64) -> Expr {
    let mut nat = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    for _ in 0..k {
        nat = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), nat);
    }
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mk"), vec![]),
        [
            Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), nat),
            one,
        ],
    )
}

/// `fun (_ : Bool) => Rat` — the shared `Type`-valued motive for a `Bool.rec`
/// at universe 1 (the `{0,1}` / `{-1,+1}` Rat embeddings reduce through it).
fn bool_to_rat_motive() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        Expr::const_(Name::from_string("Bool"), vec![]),
        Expr::const_(Name::from_string("Rat"), vec![]),
    )
}

impl Environment {
    /// Initialize Boolean analysis declarations for KKL formalization.
    ///
    /// Depends on: `init_bool()`, `init_rat()`, `init_fin()`.
    pub fn init_boolean_analysis(&mut self) -> Result<(), EnvError> {
        if self.boolean_analysis_init || self.boolean_analysis_init_in_progress {
            // The in-progress latch breaks the bonami/hc24 retirement cycle:
            // the single in-flight pass registers foundations (`hcDecode`,
            // `pm`) before the hc24 chain at the end, so a latched re-entry
            // from inside that chain already has its prerequisites.
            return Ok(());
        }
        self.boolean_analysis_init_in_progress = true;
        self.init_bool()?;
        self.init_rat()?;
        self.init_fin()?;
        // Stage-1 BoolFn-redesign foundations (Fin.prod, HCPoint, hcDecode,
        // Expect, chi). CHECKED Definitions only — no axiom added/removed, so the
        // soundness certificate's golden TCB is unchanged. Wiring them here makes
        // `soundness_certificate_env()` (via `init_fourier_boolean` ->
        // `init_boolean_analysis`) re-verify them under C1.
        // See `designs/2026-06-08-boolfn-redesign.md` Stage 1.
        self.init_boolean_analysis_foundations()?;

        let c = BoolAnalysisConsts::new();
        self.register_bool_fn(&c)?;
        // Stage-2 {0,1} and {-1,+1} Bool->Rat embeddings (the σ-character base of
        // every Fourier average). CHECKED reducible Definitions.
        self.register_boolfn_embeddings(&c)?;
        // Stage-2 coordinate-flip `x ⊕ eᵢ` on cube points (the discrete partial
        // derivative used by Influence). CHECKED reducible Definition.
        self.register_hc_flip(&c)?;
        self.register_fourier_coeff(&c)?;
        self.register_influence(&c)?;
        self.register_total_influence(&c)?;
        self.register_variance(&c)?;
        // Stage-2 single Fourier coefficient f̂(S) = E[(pm∘f)·χ_S] and the
        // transform f̂ = (S ↦ f̂(S)). CHECKED reducible Definitions. Registered
        // here (before the fourier_boolean.rs overlay) so the bare-axiom
        // `register_fourier_coefficient` there no-ops on the existing Definition.
        self.register_fourier_coefficient_def(&c)?;
        self.register_fourier_transform(&c)?;
        // Constructive `Fin.prod_mul` (multiplicativity of the cube product) —
        // the first reusable building block of the character-orthonormality /
        // Parseval machinery. A kernel-checked Theorem, no axiom added/removed
        // (TCB unchanged), so the soundness certificate re-verifies it under C1.
        self.register_fin_prod_mul_theorem()?;
        // Cube-tensor factorization `chi_mul_chi` (χ_S·χ_T merged into a single
        // Fin.prod of per-coordinate products, split by Fin.prod_mul) — the next
        // reusable building block on the character-orthonormality path. A
        // kernel-checked, constructive Theorem; no axiom added/removed (TCB
        // unchanged), so the soundness certificate re-verifies it under C1.
        self.register_chi_mul_chi_theorem()?;
        // `pm b · pm b = 1` (the {+1,-1} embedding squares to 1) — the per-
        // coordinate `f̃² = 1` fact underpinning the diagonal character inner
        // product and the E[f̃²]=1 normalization. Kernel-checked constructive
        // Theorem; no axiom added/removed (TCB unchanged).
        self.register_pm_mul_self_theorem()?;
        // `pm false + pm true = 0` (the per-coordinate vanishing average numerator
        // (+1)+(-1)=0) — the coordinate-factor fact that makes the off-diagonal
        // cube average E[χ_U] vanish for any U containing that coordinate.
        // Kernel-checked constructive Theorem; TCB unchanged.
        self.register_pm_coordinate_vanishing_theorem()?;
        // `Fin.prod_const_one` (Π 1 = 1) and `Fin.prod_congr` (pointwise-equal
        // factors ⇒ equal products) — reusable multiplicative twins of the
        // landed Fin.sum lemmas, needed to collapse the diagonal character
        // product. Kernel-checked constructive Theorems; TCB unchanged.
        self.register_fin_prod_one_theorems()?;
        // `Fin.prod_succ` (the successor peel `Π_{i<n+1} = (Π_{i<n} ·∘castSucc) ·
        // (·(last n))`) — the multiplicative twin of `Fin.sum_succ`, the rung
        // that factors the cube product `chi (n+1)` into a `chi n` prefix times
        // its top-coordinate factor. Kernel-checked constructive Theorem (a real
        // Nat.rec ι-step); TCB unchanged.
        self.register_fin_prod_succ_theorem()?;
        // Character coordinate peel `chi_succ`: chi (n+1) S x factors as
        // (chi n (S∘castSucc) (x∘castSucc)) · (top-coordinate factor), via
        // Fin.prod_succ. The inductive peel the off-diagonal E[χ_U]=0 argument
        // consumes. Kernel-checked constructive Theorem; TCB unchanged.
        self.register_chi_succ_theorem()?;
        // Character group law `chi_mul_chi_symmDiff : χ_S·χ_T = χ_{S Δ T}`
        // (pointwise 2×2 factor merge + Fin.prod_congr) — reduces every
        // off-diagonal inner product E[χ_S·χ_T] (S ≠ T) to a single-character
        // average E[χ_{SΔT}] with a nonempty index set. Kernel-checked
        // constructive Theorem; TCB unchanged.
        self.register_chi_symm_diff_theorem()?;
        // Diagonal character identity `chi_mul_self : chi n S x * chi n S x = 1`
        // (the per-point integrand of the self inner product). Composes
        // chi_mul_chi + a 2×2 Bool.rec per-coordinate factor²=1 + Fin.prod_congr
        // + Fin.prod_const_one. Kernel-checked constructive Theorem; TCB unchanged.
        self.register_chi_mul_self_theorem()?;
        // `Expect_congr` (the uniform cube expectation respects pointwise
        // equality of its integrand) — the integrand-substitution lemma that
        // lets the orthonormality argument replace χ_S(x)·χ_S(x) by its proven
        // constant value 1 under E. Kernel-checked constructive Theorem;
        // TCB unchanged.
        self.register_expect_congr_theorem()?;
        // Inner-product → single-character reduction
        // `chi_inner_eq_expect_symmDiff : E[χ_S·χ_T] = E[χ_{S Δ T}]`
        // (Expect_congr over the proven pointwise group law
        // chi_mul_chi_symmDiff). Collapses EVERY character inner product to a
        // single-character average — the form the off-diagonal cancellation
        // E[χ_U]=0 (U≠∅) and the diagonal E[χ_∅]=1 dispatch. Kernel-checked
        // constructive Theorem; TCB unchanged.
        self.register_chi_inner_symm_diff_theorem()?;
        // Diagonal self inner product collapses to the constant-1 average:
        // E[χ_S²] = E[1] (Expect_congr over the proven chi_mul_self). The final
        // = 1 is the single remaining normalization fact E[1]=1. Kernel-checked
        // constructive Theorem; TCB unchanged.
        self.register_chi_self_inner_theorem()?;
        // `Rat.add_natCast_one` (symbolic `(k/1)+1 = (k+1)/1` over the Rat
        // quotient) and `Fin.sum_const_one` (Σ_{i<n} 1 = n/1) — the additive
        // twins that supply the cube-sum normalization `Σ 1 = 2^n / 1`, the
        // numerator side of the uniform expectation `E[1] = 1`. Kernel-checked
        // constructive Theorems; TCB unchanged.
        self.register_fin_sum_const_one_theorems()?;
        // A4-A6: cube-size positivity (`Nat.one_le_two_pow`), positive-Nat-cast
        // nonzero over the Rat quotient (`Rat.natCast_ne_zero_of_pos`, a
        // Quot.lift zero-class discriminator), the uniform-expectation
        // normalization `Expect_const_one : E[1] = 1`, and the CLOSED diagonal
        // character orthonormality `chi_self_inner_eq_one : E[χ_S·χ_S] = 1`.
        // Kernel-checked constructive Theorems; TCB unchanged.
        self.register_expect_one_theorems()?;
        // NOTE: the off-diagonal character orthonormality
        // `chi_inner_offdiag_zero` (E[χ_S·χ_T] = 0 when S, T differ at the top
        // coordinate) is fully PROVEN and kernel-checked
        // (`register_chi_inner_offdiag_zero_theorem`, pinned by its `Constructive`
        // empty-closure test), but is intentionally NOT wired into the always-on
        // init chain yet: its proof uses `funext` (foundational) and a Nat-order
        // `Trans` instance, which would grow the live soundness-certificate axiom
        // census without yet RETIRING `parseval_identity`. It will be wired in
        // together with the Fourier-expansion bridge that eliminates
        // `parseval_identity` (net TCB shrink). The diagonal orthonormality
        // `chi_self_inner_eq_one` and the group/inner-product reductions
        // (`chi_mul_chi_symmDiff`, `chi_inner_eq_expect_symmDiff`) ARE wired above
        // (funext-free, TCB-neutral).
        // Mark init complete BEFORE the theorem layer: the Parseval retirement
        // (`register_parseval_identity` → `subsetSum_parseval_core`) re-enters
        // `init_boolean_analysis` for its `pm`/`chi`/foundation dependencies,
        // which are ALL registered above (lines up to here). Setting the flag
        // now lets that re-entrant call short-circuit and breaks the otherwise
        // infinite core↔init recursion. Everything below needs only what is
        // already present.
        self.boolean_analysis_init_in_progress = false;
        self.boolean_analysis_init = true;

        // Theorem registrations (in boolean_analysis_theorems.rs)
        self.register_parseval_identity_helper(&c)?;
        self.register_parseval_identity(&c)?;
        self.register_influence_fourier_helper(&c)?;
        self.register_influence_fourier(&c)?;
        self.register_total_influence_identity_helper(&c)?;
        self.register_total_influence_identity(&c)?;
        self.register_bonami_beckner_conditions(&c)?;
        self.register_bonami_beckner_helper(&c)?;
        self.register_bonami_beckner(&c)?;
        self.register_kkl_inequality_helper(&c)?;
        self.register_kkl_inequality(&c)?;

        // ── KKL spectral / low-band chain (wired into the always-on aggregate) ──
        //
        // The audit found these KKL-finish inputs registered but ORPHANED — only
        // their own `#[cfg(test)]` sites called them, so they never entered the
        // live/cert Environment (`init_fourier_boolean → init_boolean_analysis`).
        // Wire them here, AFTER the completion flag is set (line above), so each
        // rung's re-entrant `init_boolean_analysis()` short-circuits. Every rung is
        // a kernel-checked, `Constructive`, empty-domain-axiom-closure Theorem (no
        // axiom added/removed — the soundness-certificate golden TCB is unchanged),
        // and each registrar is idempotent + order-independent.
        //
        //   * the `Rat.powNat` exponent-monotonicity primitives (the antitone
        //     `b ∈ [0,1]` rung is the load-bearing atom of the low-band extraction);
        self.register_rat_pow_nat_le_pow_nat_right()?;
        self.register_rat_pow_nat_le_pow_nat_right_antitone()?;
        //   * the level-split 4-norm↔spectral bridge (`levelWt_eq_powNat`,
        //     `noise_spectral_level` — the spectral-side `‖T_ρ a‖₂²` interface);
        self.register_noise_spectral_level()?;
        //   * RUNG A — the low-band Fourier-mass extraction
        //     `b^k·W^{≤k}_b[w] ≤ Σ_S b^{|S|}·w S` (the inverse-free rational core of
        //     `(1/9)^k·W^{≤k}[g] ≤ ‖T_{1/3} g‖₂²`);
        self.init_boolean_analysis_kkl_lowband_extract()?;
        //   * the discrete-derivative 4-norm / 2-norm collapse bricks.
        self.init_boolean_analysis_deriv_4norm()?;

        // NOTE — `variance_low_band_influence` (`init_boolean_analysis_kkl_lowband`,
        // the audit-named target) and `Rat.eq_sub_of_sub_eq` are PROVEN, kernel-
        // checked, `Constructive`, empty-domain-axiom-closure Theorems (see the
        // `boolean_analysis_kkl_lowband` tests), but are intentionally NOT pulled
        // into this always-on aggregate: their dependency `kkl_threshold_mass_le`
        // transitively REGISTERS the abstract-carrier `Trans` typeclass-instance
        // axioms `instTransNatLt` / `instTransNatLtLtLe` (present-but-unused — they
        // are NOT in any wired theorem's proof closure, which stays empty), which
        // would GROW the live soundness-certificate axiom census by 2 with no
        // offsetting retirement. This is the SAME deferral policy applied to
        // `chi_inner_offdiag_zero` above (see the `funext`/`Trans` note). They will
        // be wired together with a `Trans`-instance discharge (or the KKL retirement
        // that offsets them). `variance_low_band_influence` remains reachable in any
        // overlay env via `init_boolean_analysis_kkl_lowband()`; the dedicated
        // wiring test pins the full chain through `init_boolean_analysis`.

        Ok(())
    }

    /// `BoolFn (n : Nat) : Type := HCPoint n -> Bool`
    ///
    /// Stage-2 BoolFn-redesign migration (`designs/2026-06-08-boolfn-redesign.md`).
    /// A `BoolFn n` is now an *actual* Boolean function on the hypercube — it maps
    /// each cube point `HCPoint n = Fin n -> Bool` to a `Bool`, i.e. its type is
    /// `(Fin n -> Bool) -> Bool`. (Previously it was the single-point type
    /// `Fin n -> Bool`, which could not type the cube averages `E[f]`, `Var[f]`,
    /// `Inf_i[f]`, `f̂(S)` — those range over the `2^n` cube points.) `HCPoint` is
    /// the reducible foundation registered by `init_boolean_analysis_foundations`
    /// (pulled in just above), so `BoolFn n` unfolds to `(Fin n -> Bool) -> Bool`.
    /// The `f` binder remains a function type (kind `Other` for the C4 refutation
    /// engine), so every BoolAnalysis axiom over it stays non-refutable.
    fn register_bool_fn(&mut self, c: &BoolAnalysisConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("BoolAnalysis.BoolFn"))
            .is_some()
        {
            return Ok(());
        }
        let hcpoint = Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]);
        let bool_fn_type = Expr::pi(BinderInfo::Default, c.nat.clone(), c.type0.clone());
        let bool_fn_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hcpoint_n = Expr::app(hcpoint.clone(), n.clone());
            let body = Expr::pi(BinderInfo::Default, hcpoint_n, c.bool_.clone());
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("BoolAnalysis.BoolFn"),
            level_params: vec![],
            type_: bool_fn_type,
            value: bool_fn_value,
            is_reducible: true,
        })
    }

    /// The two `Bool -> Rat` embeddings underpinning every Fourier average:
    ///
    /// - `BoolAnalysis.ind (b : Bool) : Rat := @Bool.rec (fun _ => Rat) 0 1 b`
    ///   — the `{0,1}` indicator (`false -> 0`, `true -> 1`).
    /// - `BoolAnalysis.pm (b : Bool) : Rat := Rat.sub 1 (Rat.mul 2 (ind b))`
    ///   — the `{+1,-1}` sign embedding `(-1)^b` (`false -> +1`, `true -> -1`),
    ///   exactly the per-coordinate factor used in `chi`.
    ///
    /// Both are CHECKED reducible `Declaration::Definition`s over the Stage-1
    /// foundations (`Bool.rec`, the Rat field tower). They DISCHARGE no axiom on
    /// their own — they are new building blocks — but ground-reduce to the right
    /// closed numerals (pinned by the `tests` module).
    fn register_boolfn_embeddings(&mut self, c: &BoolAnalysisConsts) -> Result<(), EnvError> {
        let bool_rec = Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        );
        // ind : Bool -> Rat := @Bool.rec (fun _ => Rat) Rat.zero Rat.one b
        if self
            .get_const(&Name::from_string("BoolAnalysis.ind"))
            .is_none()
        {
            let ty = Expr::pi(BinderInfo::Default, c.bool_.clone(), c.rat.clone());
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (b_id, bval) = b.fresh_local(c.bool_.clone());
                let body = Expr::apps(
                    bool_rec.clone(),
                    [
                        bool_to_rat_motive(),
                        Expr::const_(Name::from_string("Rat.zero"), vec![]),
                        Expr::const_(Name::from_string("Rat.one"), vec![]),
                        bval,
                    ],
                );
                let e = b.mk_lam(b_id, BinderInfo::Default, c.bool_.clone(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("BoolAnalysis.ind"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }
        // pm : Bool -> Rat := fun b => Rat.sub Rat.one (Rat.mul 2 (ind b))
        if self
            .get_const(&Name::from_string("BoolAnalysis.pm"))
            .is_none()
        {
            let ind = Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]);
            let rat_sub = Expr::const_(Name::from_string("Rat.sub"), vec![]);
            let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
            let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
            let ty = Expr::pi(BinderInfo::Default, c.bool_.clone(), c.rat.clone());
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (b_id, bval) = b.fresh_local(c.bool_.clone());
                let ind_b = Expr::app(ind.clone(), bval);
                let two_ind = Expr::apps(rat_mul.clone(), [rat_nat_lit(2), ind_b]);
                let body = Expr::apps(rat_sub.clone(), [rat_one.clone(), two_ind]);
                let e = b.mk_lam(b_id, BinderInfo::Default, c.bool_.clone(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("BoolAnalysis.pm"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }
        Ok(())
    }

    /// `FourierCoeff (n : Nat) : Type := HCPoint n -> Rat`
    ///
    /// Stage-2 BoolFn redesign: a Fourier coefficient family `f̂` is a function
    /// from subsets-as-indicators (`S : HCPoint n`, the design's Finset-free
    /// representation) to `Rat`. (Previously `Finset (Fin n) -> Rat` over the
    /// opaque `Finset` stub.) This re-targets `FourierTransform` / `FourierSpectrum`
    /// onto the real indicator-subset domain `chi` consumes.
    fn register_fourier_coeff(&mut self, c: &BoolAnalysisConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("BoolAnalysis.FourierCoeff"))
            .is_some()
        {
            return Ok(());
        }
        let fourier_coeff_type = Expr::pi(BinderInfo::Default, c.nat.clone(), c.type0.clone());
        let fourier_coeff_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hcp = c.hcpoint_of(&n);
            let body = Expr::pi(BinderInfo::Default, hcp, c.rat.clone());
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("BoolAnalysis.FourierCoeff"),
            level_params: vec![],
            type_: fourier_coeff_type,
            value: fourier_coeff_value,
            is_reducible: true,
        })
    }

    /// `hcFlip (n : Nat) (x : HCPoint n) (i : Fin n) : HCPoint n` — toggle the
    /// `i`-th coordinate of the cube point `x` (the basis-vector XOR `x ⊕ eᵢ`):
    ///
    /// ```text
    /// hcFlip n x i := fun (j : Fin n) =>
    ///   @Bool.rec (fun _ => Bool) (x j) (Bool.not (x j))
    ///     (Nat.beq (Fin.val n j) (Fin.val n i))
    /// ```
    ///
    /// Coordinates are compared by their `Fin.val` via the reducible `Nat.beq`:
    /// when `j` and `i` are the same coordinate the bit is negated, otherwise it
    /// is copied. CHECKED reducible `Declaration::Definition` over the Stage-1
    /// foundations (`Bool.rec`, `Bool.not`, `Nat.beq`, `Fin.val`).
    fn register_hc_flip(&mut self, c: &BoolAnalysisConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("BoolAnalysis.hcFlip"))
            .is_some()
        {
            return Ok(());
        }
        // `Nat.beq` lives in the Nat-compare overlay; ensure it is present.
        self.init_nat_cmp()?;

        let bool_rec = Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        );
        let bool_not = Expr::const_(Name::from_string("Bool.not"), vec![]);
        let nat_beq = Expr::const_(Name::from_string("Nat.beq"), vec![]);
        let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
        // `fun (_ : Bool) => Bool` — the Bool-valued motive (universe 1).
        let bool_motive = || Expr::lam(BinderInfo::Default, c.bool_.clone(), c.bool_.clone());

        // Type: (n : Nat) -> (x : HCPoint n) -> (i : Fin n) -> HCPoint n
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hcp = c.hcpoint_of(&n);
            let (x_id, _x) = b.fresh_local(hcp.clone());
            let fin_n = c.fin_of(&n);
            let (i_id, _i) = b.fresh_local(fin_n.clone());
            let e = b.mk_pi(i_id, BinderInfo::Default, fin_n, hcp.clone());
            let e = b.mk_pi(x_id, BinderInfo::Default, hcp, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // Value.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hcp = c.hcpoint_of(&n);
            let (x_id, x) = b.fresh_local(hcp.clone());
            let fin_n = c.fin_of(&n);
            let (i_id, i) = b.fresh_local(fin_n.clone());

            // fun (j : Fin n) => Bool.rec (x j) (Bool.not (x j)) (Nat.beq (val j) (val i))
            let point = {
                let (j_id, j) = b.fresh_local(fin_n.clone());
                let x_j = Expr::app(x.clone(), j.clone());
                let not_x_j = Expr::app(bool_not.clone(), x_j.clone());
                let val_j = Expr::apps(fin_val.clone(), [n.clone(), j.clone()]);
                let val_i = Expr::apps(fin_val.clone(), [n.clone(), i.clone()]);
                let same = Expr::apps(nat_beq.clone(), [val_j, val_i]);
                let gated = Expr::apps(bool_rec.clone(), [bool_motive(), x_j, not_x_j, same]);
                b.mk_lam(j_id, BinderInfo::Default, fin_n.clone(), gated)
            };

            let e = b.mk_lam(i_id, BinderInfo::Default, fin_n, point);
            let e = b.mk_lam(x_id, BinderInfo::Default, hcp, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("BoolAnalysis.hcFlip"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `Influence (n : Nat) (f : BoolFn n) (i : Fin n) : Rat`
    ///
    /// Stage-2 BoolFn redesign: the per-coordinate influence as the average
    /// sensitivity at coordinate `i` (O'Donnell, *Analysis of Boolean
    /// Functions*, Def. 2.13):
    /// `Inf_i[f] = Pr_x[f(x) ≠ f(x ⊕ eᵢ)]`. A genuine CHECKED
    /// `Declaration::Definition`:
    ///
    /// ```text
    /// Influence n f i :=
    ///   Expect n (fun x => ind (Bool.not (Bool.beq (f x) (f (hcFlip n x i)))))
    /// ```
    ///
    /// over the Stage-1 `Expect`, the `{0,1}` embedding `ind`, the cube flip
    /// `hcFlip`, and the reducible `Bool.beq`/`Bool.not`. The indicator is `1`
    /// exactly when `f` disagrees on `x` and its `i`-flip, so the expectation is
    /// the flip-sensitivity probability. DISCHARGES the bare `Influence` axiom,
    /// shrinking the TCB by one. (`TotalInfluence = Σᵢ Influence` now resolves to
    /// a fully-defined quantity.)
    fn register_influence(&mut self, c: &BoolAnalysisConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("BoolAnalysis.Influence"))
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        // `Bool.beq` lives in the BEq overlay; ensure it is present.
        self.init_beq()?;

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, _) = b.fresh_local(bool_fn_n.clone());
            let fin_n = c.fin_of(&n);
            let (i_id, _) = b.fresh_local(fin_n.clone());
            let e = b.mk_pi(i_id, BinderInfo::Default, fin_n, c.rat.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let expect = Expr::const_(Name::from_string("BoolAnalysis.Expect"), vec![]);
        let ind = Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]);
        let hc_flip = Expr::const_(Name::from_string("BoolAnalysis.hcFlip"), vec![]);
        let bool_beq = Expr::const_(Name::from_string("Bool.beq"), vec![]);
        let bool_not = Expr::const_(Name::from_string("Bool.not"), vec![]);

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let fin_n = c.fin_of(&n);
            let (i_id, i) = b.fresh_local(fin_n.clone());
            let hcp = c.hcpoint_of(&n);

            // fun (x : HCPoint n) =>
            //   ind (Bool.not (Bool.beq (f x) (f (hcFlip n x i))))
            let summand = {
                let (x_id, x) = b.fresh_local(hcp.clone());
                let f_x = Expr::app(f.clone(), x.clone());
                let flipped = Expr::apps(hc_flip.clone(), [n.clone(), x.clone(), i.clone()]);
                let f_flip = Expr::app(f.clone(), flipped);
                let beq = Expr::apps(bool_beq.clone(), [f_x, f_flip]);
                let differ = Expr::app(bool_not.clone(), beq);
                let body = Expr::app(ind.clone(), differ);
                b.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body)
            };

            let body = Expr::apps(expect.clone(), [n.clone(), summand]);
            let e = b.mk_lam(i_id, BinderInfo::Default, fin_n, body);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.discharge_axiom_for_redefinition(&Name::from_string("BoolAnalysis.Influence"));
        self.add_decl(Declaration::Definition {
            name: Name::from_string("BoolAnalysis.Influence"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `TotalInfluence (n : Nat) (f : BoolFn n) : Rat`
    ///
    /// Total influence is, by definition (O'Donnell, *Analysis of Boolean
    /// Functions*, Def. 2.27), the sum of the per-coordinate influences:
    /// `I[f] = Σ_{i=1}^n Inf_i[f]`. We register it as a genuine
    /// `Declaration::Definition` carrying exactly that formula:
    /// `fun n f => Fin.sum n (fun (i : Fin n) => Influence n f i)`,
    /// over the existing `Fin.sum : (n) → (Fin n → Rat) → Rat` carrier and the
    /// `BoolAnalysis.Influence` accessor. This DISCHARGES the bare
    /// `TotalInfluence` axiom (the formula is definitionally correct, not just
    /// type-correct). Its transitive axiom closure still reaches the admitted
    /// `BoolAnalysis.Influence` (which genuinely needs hypercube-expectation
    /// machinery that does not yet exist) — that is honest and unchanged.
    fn register_total_influence(&mut self, c: &BoolAnalysisConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("BoolAnalysis.TotalInfluence"))
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        // `Fin.sum` lives in the Fin-sum overlay; ensure it is present so the
        // definitional body type-checks regardless of the entry point.
        self.init_fin_sum()?;

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, _) = b.fresh_local(bool_fn_n.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, c.rat.clone());
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // value: fun (n : Nat) (f : BoolFn n) =>
        //          Fin.sum n (fun (i : Fin n) => Influence n f i)
        let influence = Expr::const_(Name::from_string("BoolAnalysis.Influence"), vec![]);
        let fin_sum = Expr::const_(Name::from_string("Fin.sum"), vec![]);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let fin_n = c.fin_of(&n);
            // summand: fun (i : Fin n) => Influence n f i
            let summand = {
                let (i_id, i) = b.fresh_local(fin_n.clone());
                let body = Expr::apps(influence.clone(), [n.clone(), f.clone(), i]);
                b.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), body)
            };
            let body = Expr::apps(fin_sum.clone(), [n.clone(), summand]);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, body);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // Discharge the bare axiom (no-op if absent) and install the Definition.
        self.discharge_axiom_for_redefinition(&Name::from_string("BoolAnalysis.TotalInfluence"));
        self.add_decl(Declaration::Definition {
            name: Name::from_string("BoolAnalysis.TotalInfluence"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `Variance (n : Nat) (f : BoolFn n) : Rat`
    ///
    /// Stage-2 BoolFn redesign: a genuine CHECKED `Declaration::Definition`
    /// carrying the textbook variance of `f` under the `{+1,-1}` embedding
    /// (O'Donnell, *Analysis of Boolean Functions*, §1.4):
    /// `Var[f] = E[f̃²] - (E[f̃])²` where `f̃ = pm ∘ f` is the `{+1,-1}`
    /// representation. Concretely
    ///
    /// ```text
    /// Variance n f :=
    ///   Rat.sub (Expect n (fun x => Rat.mul (pm (f x)) (pm (f x))))
    ///           (Rat.mul (Expect n (fun x => pm (f x)))
    ///                    (Expect n (fun x => pm (f x))))
    /// ```
    ///
    /// over the Stage-1 `Expect` (uniform cube average) and the `pm` embedding.
    /// DISCHARGES the bare `Variance` axiom (definitionally correct, not just
    /// type-correct), shrinking the TCB by one. `x : HCPoint n`, `f x : Bool`,
    /// `pm (f x) : Rat` — all type-correct under the migrated `BoolFn`.
    fn register_variance(&mut self, c: &BoolAnalysisConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("BoolAnalysis.Variance"))
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, _) = b.fresh_local(bool_fn_n.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, c.rat.clone());
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let expect = Expr::const_(Name::from_string("BoolAnalysis.Expect"), vec![]);
        let pm = Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]);
        let rat_sub = Expr::const_(Name::from_string("Rat.sub"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let hcp = c.hcpoint_of(&n);

            // fun (x : HCPoint n) => pm (f x)
            let pm_f = {
                let (x_id, x) = b.fresh_local(hcp.clone());
                let body = Expr::app(pm.clone(), Expr::app(f.clone(), x));
                b.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body)
            };
            // fun (x : HCPoint n) => Rat.mul (pm (f x)) (pm (f x))
            let pm_f_sq = {
                let (x_id, x) = b.fresh_local(hcp.clone());
                let pmfx = Expr::app(pm.clone(), Expr::app(f.clone(), x));
                let body = Expr::apps(rat_mul.clone(), [pmfx.clone(), pmfx]);
                b.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body)
            };

            let e_sq = Expr::apps(expect.clone(), [n.clone(), pm_f_sq]);
            let e_pm = Expr::apps(expect.clone(), [n.clone(), pm_f]);
            let sq_e = Expr::apps(rat_mul.clone(), [e_pm.clone(), e_pm]);
            let body = Expr::apps(rat_sub.clone(), [e_sq, sq_e]);

            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, body);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.discharge_axiom_for_redefinition(&Name::from_string("BoolAnalysis.Variance"));
        self.add_decl(Declaration::Definition {
            name: Name::from_string("BoolAnalysis.Variance"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `FourierCoefficient (n : Nat) (f : BoolFn n) (S : HCPoint n) : Rat`
    ///
    /// Stage-2 BoolFn redesign: the single Fourier coefficient
    /// `f̂(S) = E_x[ (pm∘f)(x) · χ_S(x) ]` (O'Donnell §1.2), a genuine CHECKED
    /// reducible `Declaration::Definition`:
    ///
    /// ```text
    /// FourierCoefficient n f S :=
    ///   Expect n (fun x => Rat.mul (pm (f x)) (chi n S x))
    /// ```
    ///
    /// over the Stage-1 `Expect` / parity character `chi` and the `pm`
    /// embedding. The subset `S` is its indicator `HCPoint n` (the Finset-free
    /// representation). DISCHARGES the bare `FourierCoefficient` axiom that the
    /// `fourier_boolean.rs` overlay would otherwise register (its registrar
    /// guards on presence, so it no-ops once this Definition is installed).
    fn register_fourier_coefficient_def(&mut self, c: &BoolAnalysisConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("BoolAnalysis.FourierCoefficient"))
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, _) = b.fresh_local(bool_fn_n.clone());
            let hcp = c.hcpoint_of(&n);
            let (s_id, _) = b.fresh_local(hcp.clone());
            let e = b.mk_pi(s_id, BinderInfo::Default, hcp, c.rat.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let expect = Expr::const_(Name::from_string("BoolAnalysis.Expect"), vec![]);
        let pm = Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]);
        let chi = Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = b.fresh_local(hcp.clone());

            // fun (x : HCPoint n) => Rat.mul (pm (f x)) (chi n S x)
            let summand = {
                let (x_id, x) = b.fresh_local(hcp.clone());
                let pm_fx = Expr::app(pm.clone(), Expr::app(f.clone(), x.clone()));
                let chi_sx = Expr::apps(chi.clone(), [n.clone(), s.clone(), x]);
                let body = Expr::apps(rat_mul.clone(), [pm_fx, chi_sx]);
                b.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body)
            };

            let body = Expr::apps(expect.clone(), [n.clone(), summand]);
            let e = b.mk_lam(s_id, BinderInfo::Default, hcp, body);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.discharge_axiom_for_redefinition(&Name::from_string(
            "BoolAnalysis.FourierCoefficient",
        ));
        self.add_decl(Declaration::Definition {
            name: Name::from_string("BoolAnalysis.FourierCoefficient"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `FourierTransform (n : Nat) (f : BoolFn n) : FourierCoeff n`
    ///
    /// Stage-2 BoolFn redesign: the Fourier transform IS the coefficient family
    /// `f̂ = (S ↦ f̂(S))`, a genuine CHECKED reducible `Declaration::Definition`:
    ///
    /// ```text
    /// FourierTransform n f := fun (S : HCPoint n) => FourierCoefficient n f S
    /// ```
    ///
    /// Its result type is the re-targeted `FourierCoeff n = HCPoint n -> Rat`.
    /// DISCHARGES the bare `FourierTransform` axiom (the closure now bottoms out
    /// in the defined `FourierCoefficient` / `Expect` / `chi`, no admitted axiom).
    fn register_fourier_transform(&mut self, c: &BoolAnalysisConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("BoolAnalysis.FourierTransform"))
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, _) = b.fresh_local(bool_fn_n.clone());
            let result = c.fourier_coeff_of(&n);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, result);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let fourier_coefficient =
            Expr::const_(Name::from_string("BoolAnalysis.FourierCoefficient"), vec![]);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let hcp = c.hcpoint_of(&n);
            // fun (S : HCPoint n) => FourierCoefficient n f S
            let coeff_fn = {
                let (s_id, s) = b.fresh_local(hcp.clone());
                let body = Expr::apps(fourier_coefficient.clone(), [n.clone(), f.clone(), s]);
                b.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body)
            };
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, coeff_fn);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.discharge_axiom_for_redefinition(&Name::from_string("BoolAnalysis.FourierTransform"));
        self.add_decl(Declaration::Definition {
            name: Name::from_string("BoolAnalysis.FourierTransform"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::env::Environment;
    use crate::expr::Expr;
    use crate::expr::ExprKind;
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env
    }

    /// TCB-shrink: `BoolAnalysis.total_influence_identity` is a genuine
    /// kernel-checked `Declaration::Theorem` (NOT an admitted Axiom), proven by
    /// `@Eq.refl Rat (TotalInfluence n f)` over the reducible-Definition helper
    /// `total_influence_identity_helper := @Eq Rat (TotalInfluence n f) (Fin.sum n
    /// (fun i => Influence n f i))`. Its proof_quality is `Constructive` (empty
    /// admitted-axiom closure) and the helper is a reducible Definition.
    #[test]
    fn test_total_influence_identity_is_constructive_theorem() {
        use crate::env::types::ConstantKind;
        use crate::env::ProofQuality;
        let env = make_env();

        let thm = env
            .get_const(&Name::from_string("BoolAnalysis.total_influence_identity"))
            .expect("total_influence_identity registered");
        assert_eq!(
            thm.kind,
            ConstantKind::Theorem,
            "total_influence_identity must be a kernel-checked Theorem, not an Axiom"
        );
        assert!(thm.value.is_some(), "the theorem must carry its proof term");

        let helper = env
            .get_const(&Name::from_string(
                "BoolAnalysis.total_influence_identity_helper",
            ))
            .expect("helper registered");
        assert_eq!(
            helper.kind,
            ConstantKind::Definition,
            "the helper must be a reducible Definition carrying the real Eq, not an Axiom"
        );

        // Independent C1-style re-verification: the proof term type-checks.
        let value = thm.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &thm.type_)
            .expect("total_influence_identity proof must check against its declared type");

        // Constructive: empty admitted-axiom closure.
        assert_eq!(
            env.proof_quality(&Name::from_string("BoolAnalysis.total_influence_identity")),
            Some(ProofQuality::Constructive),
            "total_influence_identity must be Constructive (no admitted-axiom dependency)"
        );
        assert!(
            env.axiom_deps(&Name::from_string("BoolAnalysis.total_influence_identity"))
                .expect("deps")
                .is_empty(),
            "total_influence_identity's transitive axiom closure must be empty"
        );
    }

    /// `Fin.prod_mul` — multiplicativity of the cube product — is a genuine
    /// kernel-checked, `Constructive` `Declaration::Theorem` (empty admitted-axiom
    /// closure), wired into `init_boolean_analysis`. The first reusable building
    /// block of the character-orthonormality / Parseval Fubini machinery.
    #[test]
    fn test_fin_prod_mul_is_constructive_theorem() {
        use crate::env::types::ConstantKind;
        use crate::env::ProofQuality;
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("Fin.prod_mul"))
            .expect("Fin.prod_mul should be registered by init_boolean_analysis");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "Fin.prod_mul must be a kernel-checked Theorem"
        );
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("Fin.prod_mul proof must check against its declared type");
        assert_eq!(
            env.proof_quality(&Name::from_string("Fin.prod_mul")),
            Some(ProofQuality::Constructive),
            "Fin.prod_mul must be Constructive (no admitted-axiom dependency)"
        );
        assert!(
            env.axiom_deps(&Name::from_string("Fin.prod_mul"))
                .expect("deps")
                .is_empty(),
            "Fin.prod_mul's transitive axiom closure must be empty"
        );
    }

    /// Ground-reduction sanity for `Fin.prod_mul`: at `n = 2` with the constant
    /// factor functions `a = b = (fun _ => 2/1)`, both sides ground-reduce to the
    /// same closed numeral. LHS `Fin.prod 2 (fun i => 2·2) = Fin.prod 2 (fun _ =>
    /// 4) = 16`; RHS `(Fin.prod 2 a)·(Fin.prod 2 b) = 4·4 = 16`. Confirms the
    /// statement is the genuine multiplicativity equation, not a vacuous shell.
    #[test]
    fn test_fin_prod_mul_ground_reduces() {
        use crate::env::decl_builder::EnvDeclBuilder;
        use crate::expr::BinderInfo;
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());

        let two = nat_lit(2);
        let fin2 = Expr::app(k("Fin"), two.clone());
        // a = b = fun (_ : Fin 2) => 2/1
        let two_over_one = Expr::apps(
            k("Rat.mk"),
            [Expr::app(k("Int.ofNat"), nat_lit(2)), nat_lit(1)],
        );
        let const_two = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, _i) = b.fresh_local(fin2.clone());
            let lam = b.mk_lam(
                i_id,
                BinderInfo::Default,
                fin2.clone(),
                two_over_one.clone(),
            );
            b.finish(lam)
        };
        // lhs: Fin.prod 2 (fun i => Rat.mul (a i) (b i))
        let pointwise = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(fin2.clone());
            let body = Expr::apps(
                k("Rat.mul"),
                [
                    Expr::app(const_two.clone(), i.clone()),
                    Expr::app(const_two.clone(), i),
                ],
            );
            let lam = b.mk_lam(i_id, BinderInfo::Default, fin2.clone(), body);
            b.finish(lam)
        };
        let lhs = Expr::apps(k("Fin.prod"), [two.clone(), pointwise]);
        let prod_a = Expr::apps(k("Fin.prod"), [two.clone(), const_two.clone()]);
        let prod_b = Expr::apps(k("Fin.prod"), [two.clone(), const_two]);
        let rhs = Expr::apps(k("Rat.mul"), [prod_a, prod_b]);
        assert!(
            tc.is_def_eq(&lhs, &rhs),
            "Fin.prod_mul instance must ground-reduce (both sides = 16)"
        );
    }

    #[test]
    fn test_bool_fn_registered() {
        let env = make_env();
        assert!(env
            .get_const(&Name::from_string("BoolAnalysis.BoolFn"))
            .is_some());
    }

    #[test]
    fn test_fourier_coeff_registered() {
        let env = make_env();
        assert!(env
            .get_const(&Name::from_string("BoolAnalysis.FourierCoeff"))
            .is_some());
    }

    #[test]
    fn test_boolean_analysis_axioms_registered() {
        let env = make_env();
        for name in [
            "BoolAnalysis.Influence",
            "BoolAnalysis.TotalInfluence",
            "BoolAnalysis.Variance",
            "BoolAnalysis.FourierTransform",
            "BoolAnalysis.parseval_identity",
            "BoolAnalysis.influence_fourier",
            "BoolAnalysis.total_influence_identity",
            "BoolAnalysis.bonami_beckner",
            "BoolAnalysis.kkl_inequality",
        ] {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{name} should be registered"
            );
        }
    }

    #[test]
    fn test_bool_fn_type_checks() {
        let env = make_env();
        let bool_fn = Expr::const_(Name::from_string("BoolAnalysis.BoolFn"), vec![]);
        let tc = TypeChecker::with_mode(&env, env.mode());
        let ty = tc
            .infer_type(&bool_fn)
            .expect("infer BoolAnalysis.BoolFn type");
        assert!(matches!(ty.kind(), ExprKind::Pi(..)));
    }

    /// Stage-2 migration pin: `BoolAnalysis.BoolFn n` is now an *actual* Boolean
    /// function on the cube — def-eq to `(Fin n -> Bool) -> Bool` (i.e.
    /// `HCPoint n -> Bool`), NOT the old single-point type `Fin n -> Bool`.
    #[test]
    fn test_bool_fn_is_hcpoint_to_bool() {
        use crate::expr::BinderInfo;
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let bool_ = Expr::const_(Name::from_string("Bool"), vec![]);
        let fin = Expr::const_(Name::from_string("Fin"), vec![]);
        let n = {
            let mut e = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            for _ in 0..3 {
                e = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), e);
            }
            e
        };
        let bool_fn_n = Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.BoolFn"), vec![]),
            n.clone(),
        );
        // (Fin 3 -> Bool) -> Bool
        let fin_n_to_bool = Expr::pi(
            BinderInfo::Default,
            Expr::app(fin.clone(), n.clone()),
            bool_.clone(),
        );
        let expected = Expr::pi(BinderInfo::Default, fin_n_to_bool.clone(), bool_.clone());
        assert!(
            tc.is_def_eq(&bool_fn_n, &expected),
            "BoolFn 3 must be def-eq to (Fin 3 -> Bool) -> Bool (the migrated cube-function type)"
        );
        // It is NOT the old single-point type `Fin 3 -> Bool`.
        assert!(
            !tc.is_def_eq(&bool_fn_n, &fin_n_to_bool),
            "BoolFn 3 must NOT be the old point-type Fin 3 -> Bool"
        );
        // It unfolds through HCPoint: BoolFn n ≡ HCPoint n -> Bool.
        let hcpoint_n_to_bool = Expr::pi(
            BinderInfo::Default,
            Expr::app(
                Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
                n,
            ),
            bool_,
        );
        assert!(
            tc.is_def_eq(&bool_fn_n, &hcpoint_n_to_bool),
            "BoolFn n must be def-eq to HCPoint n -> Bool"
        );
        let _ = nat;
    }

    #[test]
    fn test_fourier_coeff_type_checks() {
        let env = make_env();
        let fourier_coeff = Expr::const_(Name::from_string("BoolAnalysis.FourierCoeff"), vec![]);
        let tc = TypeChecker::with_mode(&env, env.mode());
        let ty = tc
            .infer_type(&fourier_coeff)
            .expect("infer BoolAnalysis.FourierCoeff type");
        assert!(matches!(ty.kind(), ExprKind::Pi(..)));
    }

    #[test]
    fn test_idempotent() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("first init");
        env.init_boolean_analysis().expect("second init");
    }

    #[test]
    fn test_boolean_analysis_naming_convention() {
        let env = make_env();
        for name in [
            "BoolAnalysis.BoolFn",
            "BoolAnalysis.FourierCoeff",
            "BoolAnalysis.Influence",
            "BoolAnalysis.TotalInfluence",
            "BoolAnalysis.Variance",
            "BoolAnalysis.FourierTransform",
            "BoolAnalysis.parseval_identity",
            "BoolAnalysis.influence_fourier",
            "BoolAnalysis.total_influence_identity",
            "BoolAnalysis.bonami_beckner",
            "BoolAnalysis.kkl_inequality",
        ] {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{name} should be registered with BoolAnalysis. prefix",
            );
        }

        for name in [
            "BoolFn",
            "FourierCoeff",
            "Influence",
            "TotalInfluence",
            "Variance",
            "FourierTransform",
        ] {
            assert!(
                env.get_const(&Name::from_string(name)).is_none(),
                "{name} should NOT be registered without BoolAnalysis. prefix",
            );
        }
    }

    /// TCB-shrink Tier-0: `BoolAnalysis.TotalInfluence` is a genuine
    /// `Declaration::Definition` (NOT an Axiom): the textbook definition
    /// `I[f] = Σ_i Inf_i[f]`, registered as `Fin.sum n (fun i => Influence n f i)`.
    #[test]
    fn test_total_influence_is_definition_not_axiom() {
        use crate::env::types::ConstantKind;
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.TotalInfluence"))
            .expect("TotalInfluence should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "TotalInfluence must be DEFINED (= sum of influences), not admitted as an axiom"
        );
        assert!(info.value.is_some(), "TotalInfluence must retain its body");
    }

    /// The `TotalInfluence` definition type-checks: `infer_type(value)` is def-eq
    /// to the declared `(n) → (f : BoolFn n) → Rat` type — the same independent
    /// re-verification C1 of the soundness certificate performs.
    #[test]
    fn test_total_influence_definition_type_checks() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.TotalInfluence"))
            .expect("TotalInfluence registered");
        let value = info.value.clone().expect("TotalInfluence has a value");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("TotalInfluence body must check against its declared type");
    }

    /// Definitional-correctness pin: the η-expanded `fun n f => TotalInfluence n f`
    /// is def-eq to `fun n f => Fin.sum n (fun i => Influence n f i)` — i.e. the
    /// body is exactly the sum-of-influences formula, not a same-typed shell.
    #[test]
    fn test_total_influence_equals_sum_of_influences() {
        use crate::env::decl_builder::EnvDeclBuilder;
        use crate::expr::BinderInfo;
        // `make_env` here only inits boolean_analysis; that pulls in `init_fin_sum`
        // transitively via `register_total_influence`, so `Fin.sum` is present.
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let bool_fn = Expr::const_(Name::from_string("BoolAnalysis.BoolFn"), vec![]);
        let fin = Expr::const_(Name::from_string("Fin"), vec![]);
        let total = Expr::const_(Name::from_string("BoolAnalysis.TotalInfluence"), vec![]);
        let influence = Expr::const_(Name::from_string("BoolAnalysis.Influence"), vec![]);
        let fin_sum = Expr::const_(Name::from_string("Fin.sum"), vec![]);

        // lhs: fun (n : Nat) (f : BoolFn n) => TotalInfluence n f
        let lhs = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let bool_fn_n = Expr::app(bool_fn.clone(), n.clone());
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let body = Expr::apps(total.clone(), [n.clone(), f.clone()]);
            let lam = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n.clone(), body);
            let lam = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), lam);
            b.finish(lam)
        };
        // rhs: fun (n : Nat) (f : BoolFn n) =>
        //        Fin.sum n (fun (i : Fin n) => Influence n f i)
        let rhs = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let bool_fn_n = Expr::app(bool_fn.clone(), n.clone());
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let fin_n = Expr::app(fin.clone(), n.clone());
            let summand = {
                let (i_id, i) = b.fresh_local(fin_n.clone());
                let body = Expr::apps(influence.clone(), [n.clone(), f.clone(), i]);
                b.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), body)
            };
            let body = Expr::apps(fin_sum.clone(), [n.clone(), summand]);
            let lam = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n.clone(), body);
            let lam = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), lam);
            b.finish(lam)
        };
        assert!(
            tc.is_def_eq(&lhs, &rhs),
            "fun n f => TotalInfluence n f must be def-eq to the sum-of-influences formula"
        );
    }

    // ── Stage-2 Bool->Rat embeddings (pm / ind) ──

    fn k(s: &str) -> Expr {
        Expr::const_(Name::from_string(s), vec![])
    }

    /// `Rat.mk (Int.ofNat n) 1` as a `Rat` numeral, with `n` an `Int` numeral.
    fn rat_int(n: i64) -> Expr {
        let one = Expr::app(k("Nat.succ"), k("Nat.zero"));
        let int_lit = if n >= 0 {
            let mut nat = k("Nat.zero");
            for _ in 0..n {
                nat = Expr::app(k("Nat.succ"), nat);
            }
            Expr::app(k("Int.ofNat"), nat)
        } else {
            // Int.negSucc m represents -(m+1); so -1 = Int.negSucc 0.
            let mut nat = k("Nat.zero");
            for _ in 0..(-n - 1) {
                nat = Expr::app(k("Nat.succ"), nat);
            }
            Expr::app(k("Int.negSucc"), nat)
        };
        Expr::apps(k("Rat.mk"), [int_lit, one])
    }

    /// `ind` / `pm` are CHECKED reducible Definitions with the right closed
    /// ground reductions: `ind false ≡ 0`, `ind true ≡ 1`, `pm false ≡ +1`,
    /// `pm true ≡ -1` (the `{0,1}` and `{+1,-1}` embeddings).
    #[test]
    fn test_boolfn_embeddings_ground_reduce() {
        use crate::env::types::ConstantKind;
        let env = make_env();
        for name in ["BoolAnalysis.ind", "BoolAnalysis.pm"] {
            let info = env.get_const(&Name::from_string(name)).expect("registered");
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{name} must be a Definition"
            );
        }
        let tc = TypeChecker::with_mode(&env, env.mode());

        // ind false = 0, ind true = 1
        let ind_false = Expr::app(k("BoolAnalysis.ind"), k("Bool.false"));
        let ind_true = Expr::app(k("BoolAnalysis.ind"), k("Bool.true"));
        assert!(tc.is_def_eq(&ind_false, &k("Rat.zero")), "ind false ≡ 0");
        assert!(tc.is_def_eq(&ind_true, &k("Rat.one")), "ind true ≡ 1");

        // pm false ≡ +1 (= 1 - 2·0), pm true ≡ -1 (= 1 - 2·1)
        let pm_false = Expr::app(k("BoolAnalysis.pm"), k("Bool.false"));
        let pm_true = Expr::app(k("BoolAnalysis.pm"), k("Bool.true"));
        assert!(
            tc.is_def_eq(&pm_false, &rat_int(1)),
            "pm false must ground-reduce to +1"
        );
        assert!(
            tc.is_def_eq(&pm_true, &rat_int(-1)),
            "pm true must ground-reduce to -1"
        );
        // Discriminator: pm true is NOT +1.
        assert!(
            !tc.is_def_eq(&pm_true, &rat_int(1)),
            "pm true must be -1, not +1 (genuine sign embedding)"
        );
    }

    // ── Stage-2 Variance ──

    /// `BoolAnalysis.Variance` is a genuine `Declaration::Definition` (NOT an
    /// Axiom): `Var[f] = E[f̃²] - (E[f̃])²` over `pm` and `Expect`.
    #[test]
    fn test_variance_is_definition_not_axiom() {
        use crate::env::types::ConstantKind;
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.Variance"))
            .expect("Variance registered");
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "Variance must be DEFINED, not admitted as an axiom"
        );
        let value = info.value.clone().expect("Variance has a body");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("Variance body must check against its declared type");
    }

    /// Definitional-correctness pin: `fun n f => Variance n f` is def-eq to the
    /// explicit `E[(pm∘f)²] - (E[pm∘f])²` formula — the body is exactly that,
    /// not a same-typed shell.
    #[test]
    fn test_variance_equals_expectation_formula() {
        use crate::env::decl_builder::EnvDeclBuilder;
        use crate::expr::BinderInfo;
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());

        let nat = k("Nat");
        let bool_fn = k("BoolAnalysis.BoolFn");
        let hcpoint = k("BoolAnalysis.HCPoint");
        let variance = k("BoolAnalysis.Variance");
        let expect = k("BoolAnalysis.Expect");
        let pm = k("BoolAnalysis.pm");
        let rat_sub = k("Rat.sub");
        let rat_mul = k("Rat.mul");

        // lhs: fun (n) (f : BoolFn n) => Variance n f
        let lhs = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let bool_fn_n = Expr::app(bool_fn.clone(), n.clone());
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let body = Expr::apps(variance.clone(), [n.clone(), f.clone()]);
            let lam = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n.clone(), body);
            let lam = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), lam);
            b.finish(lam)
        };
        // rhs: the explicit formula.
        let rhs = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let bool_fn_n = Expr::app(bool_fn.clone(), n.clone());
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let hcp = Expr::app(hcpoint.clone(), n.clone());
            let pm_f = {
                let (x_id, x) = b.fresh_local(hcp.clone());
                let body = Expr::app(pm.clone(), Expr::app(f.clone(), x));
                b.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body)
            };
            let pm_f_sq = {
                let (x_id, x) = b.fresh_local(hcp.clone());
                let pmfx = Expr::app(pm.clone(), Expr::app(f.clone(), x));
                let body = Expr::apps(rat_mul.clone(), [pmfx.clone(), pmfx]);
                b.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body)
            };
            let e_sq = Expr::apps(expect.clone(), [n.clone(), pm_f_sq]);
            let e_pm = Expr::apps(expect.clone(), [n.clone(), pm_f]);
            let sq_e = Expr::apps(rat_mul.clone(), [e_pm.clone(), e_pm]);
            let body = Expr::apps(rat_sub.clone(), [e_sq, sq_e]);
            let lam = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n.clone(), body);
            let lam = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), lam);
            b.finish(lam)
        };
        assert!(
            tc.is_def_eq(&lhs, &rhs),
            "fun n f => Variance n f must be def-eq to E[(pm∘f)²] - (E[pm∘f])²"
        );
    }

    /// Sanity (constant function): `Variance 0 (fun _ => Bool.true)` ground-reduces
    /// to `0`-valued content. At `n = 0` the cube has a single point and `Expect`
    /// divides by `2^0 = 1` (the genuine reducible Rat case), so the variance is
    /// `Rat.sub a a` for the closed `a = pm(true)² = 1`. The Rat quotient does not
    /// definitionally normalize `a - a` to canonical `Rat.zero` (that is the
    /// `Rat.add_neg_self` *theorem*, not a reduction), so we pin the genuine
    /// reducible witness `Rat.sub (E[f̃²]) ((E[f̃])²)` with both inner expectations
    /// reduced — proving the average/embedding machinery computed the right closed
    /// values for a constant function (E[f̃²] = E[f̃]² = 1).
    #[test]
    fn test_variance_constant_function_n0_balances() {
        use crate::env::decl_builder::EnvDeclBuilder;
        use crate::expr::BinderInfo;
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());

        // f : BoolFn 0 := fun (_ : HCPoint 0) => Bool.true
        let hcp0 = Expr::app(k("BoolAnalysis.HCPoint"), k("Nat.zero"));
        let f_const_true = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, _x) = b.fresh_local(hcp0.clone());
            let lam = b.mk_lam(x_id, BinderInfo::Default, hcp0.clone(), k("Bool.true"));
            b.finish(lam)
        };
        let variance = Expr::apps(k("BoolAnalysis.Variance"), [k("Nat.zero"), f_const_true]);

        // For a constant +1/-1 function at n=0: E[f̃²] and (E[f̃])² are equal closed
        // Rat values, so Variance reduces to `Rat.sub a a`. Pin that it reduces to
        // `Rat.sub a a` for the SAME a (the balance), via Rat.sub x x with x the
        // common reduced value `Expect 0 (fun _ => pm true · pm true)`.
        let hcp0b = Expr::app(k("BoolAnalysis.HCPoint"), k("Nat.zero"));
        let pm_true = Expr::app(k("BoolAnalysis.pm"), k("Bool.true"));
        let sq_summand = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, _x) = b.fresh_local(hcp0b.clone());
            let body = Expr::apps(k("Rat.mul"), [pm_true.clone(), pm_true.clone()]);
            let lam = b.mk_lam(x_id, BinderInfo::Default, hcp0b.clone(), body);
            b.finish(lam)
        };
        let e_sq = Expr::apps(k("BoolAnalysis.Expect"), [k("Nat.zero"), sq_summand]);
        // (E[f̃])² for the constant: E[f̃] = pm true (single point /1), squared.
        let pm_summand = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, _x) = b.fresh_local(hcp0b.clone());
            let lam = b.mk_lam(x_id, BinderInfo::Default, hcp0b.clone(), pm_true.clone());
            b.finish(lam)
        };
        let e_pm = Expr::apps(k("BoolAnalysis.Expect"), [k("Nat.zero"), pm_summand]);
        let sq_e = Expr::apps(k("Rat.mul"), [e_pm.clone(), e_pm]);
        let expected = Expr::apps(k("Rat.sub"), [e_sq, sq_e.clone()]);
        assert!(
            tc.is_def_eq(&variance, &expected),
            "Variance 0 (const true) must reduce to E[f̃²] - (E[f̃])² with both \
             expectations computed (the constant-function balance)"
        );
        // And E[f̃²] ≡ (E[f̃])² for this constant function (both reduce to pm(true)²),
        // i.e. the two subtracted terms are def-eq — the mathematical content of
        // "constant functions have zero variance" at the reduction level.
        let e_sq2 = Expr::apps(
            k("BoolAnalysis.Expect"),
            [k("Nat.zero"), {
                let mut b = EnvDeclBuilder::new();
                let (x_id, _x) = b.fresh_local(hcp0b.clone());
                let body = Expr::apps(k("Rat.mul"), [pm_true.clone(), pm_true.clone()]);
                let lam = b.mk_lam(x_id, BinderInfo::Default, hcp0b.clone(), body);
                b.finish(lam)
            }],
        );
        assert!(
            tc.is_def_eq(&e_sq2, &sq_e),
            "for a constant function E[f̃²] must be def-eq to (E[f̃])² (zero-variance balance)"
        );
    }

    // ── Stage-2 hcFlip + Influence ──

    /// `Fin.mk` with a `True : Prop` witness in the `isLt` slot (mirrors the
    /// foundations tests' `fin_mk`).
    fn fin_mk(m: Expr, val: Expr) -> Expr {
        Expr::apps(k("Fin.mk"), [m, val, k("True")])
    }

    fn nat_lit(n: u64) -> Expr {
        let mut e = k("Nat.zero");
        for _ in 0..n {
            e = Expr::app(k("Nat.succ"), e);
        }
        e
    }

    /// `hcFlip` toggles exactly the targeted coordinate and leaves the others
    /// fixed. With `n = 2`, `x = hcDecode 2 ⟨0⟩` (the all-false point `00`),
    /// flipping coordinate 0 gives `true` at coord 0 and `false` at coord 1.
    #[test]
    fn test_hc_flip_toggles_target_coordinate() {
        use crate::env::types::ConstantKind;
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.hcFlip"))
            .expect("hcFlip registered");
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "hcFlip must be a Definition"
        );
        let tc = TypeChecker::with_mode(&env, env.mode());

        let n = nat_lit(2);
        // x = hcDecode 2 ⟨0⟩ : HCPoint 2  (the point 00 — all false).
        let x = Expr::apps(
            k("BoolAnalysis.hcDecode"),
            [n.clone(), fin_mk(nat_lit(4), nat_lit(0))],
        );
        // flip coordinate 0.
        let i0 = fin_mk(n.clone(), nat_lit(0));
        let flipped = Expr::apps(k("BoolAnalysis.hcFlip"), [n.clone(), x.clone(), i0]);

        // coord 0 of flipped = true (toggled from false).
        let c0 = Expr::app(flipped.clone(), fin_mk(n.clone(), nat_lit(0)));
        assert!(
            tc.is_def_eq(&c0, &k("Bool.true")),
            "hcFlip at coord 0 of 00 must set coord 0 to true"
        );
        // coord 1 of flipped = false (untouched).
        let c1 = Expr::app(flipped, fin_mk(n, nat_lit(1)));
        assert!(
            tc.is_def_eq(&c1, &k("Bool.false")),
            "hcFlip at coord 0 must leave coord 1 false"
        );
    }

    /// `BoolAnalysis.Influence` is a genuine `Declaration::Definition` whose body
    /// type-checks against `(n) → (f : BoolFn n) → (i : Fin n) → Rat`.
    #[test]
    fn test_influence_is_definition_not_axiom() {
        use crate::env::types::ConstantKind;
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.Influence"))
            .expect("Influence registered");
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "Influence must be DEFINED (avg flip-sensitivity), not admitted"
        );
        let value = info.value.clone().expect("Influence has a body");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("Influence body must check against its declared type");
    }

    /// Sanity (constant function has zero influence at the reduction level):
    /// `Influence 1 (fun _ => Bool.true) ⟨0⟩` ground-reduces to `Expect 1 (fun _
    /// => ind (Bool.not (Bool.beq true true)))`. Since `f` is constant, `f x` and
    /// `f (flip x 0)` agree, `Bool.beq true true = true`, `Bool.not true = false`,
    /// and `ind false = 0` — so the summand is uniformly `0` and the influence
    /// reduces to `Expect 1 (fun _ => 0)`, which we pin (= `0/2`, the genuine
    /// reducible value; the Rat quotient does not collapse `0/2` to canonical
    /// `Rat.zero`). This proves the flip/disagreement machinery computed "no
    /// sensitivity" for a constant function.
    #[test]
    fn test_influence_constant_function_is_insensitive() {
        use crate::env::decl_builder::EnvDeclBuilder;
        use crate::expr::BinderInfo;
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());

        let n = nat_lit(1);
        // f : BoolFn 1 := fun (_ : HCPoint 1) => Bool.true
        let hcp1 = Expr::app(k("BoolAnalysis.HCPoint"), n.clone());
        let f = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, _x) = b.fresh_local(hcp1.clone());
            let lam = b.mk_lam(x_id, BinderInfo::Default, hcp1.clone(), k("Bool.true"));
            b.finish(lam)
        };
        let i0 = fin_mk(n.clone(), nat_lit(0));
        let influence = Expr::apps(k("BoolAnalysis.Influence"), [n.clone(), f, i0]);

        // Expected: Expect 1 (fun _ => Rat.zero) — every summand is ind(false)=0.
        let zero_summand = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, _x) = b.fresh_local(hcp1.clone());
            let lam = b.mk_lam(x_id, BinderInfo::Default, hcp1.clone(), k("Rat.zero"));
            b.finish(lam)
        };
        let expected = Expr::apps(k("BoolAnalysis.Expect"), [n, zero_summand]);
        assert!(
            tc.is_def_eq(&influence, &expected),
            "Influence of a constant function must reduce to Expect of the all-zero \
             sensitivity (no coordinate matters)"
        );
    }

    // ── Stage-2 FourierCoeff retype + FourierCoefficient / FourierTransform ──

    /// `BoolAnalysis.FourierCoeff n` is now `HCPoint n -> Rat` (indicator-subset
    /// domain), NOT `Finset (Fin n) -> Rat`.
    #[test]
    fn test_fourier_coeff_is_hcpoint_to_rat() {
        use crate::expr::BinderInfo;
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let n = nat_lit(2);
        let fc_n = Expr::app(k("BoolAnalysis.FourierCoeff"), n.clone());
        let expected = Expr::pi(
            BinderInfo::Default,
            Expr::app(k("BoolAnalysis.HCPoint"), n),
            k("Rat"),
        );
        assert!(
            tc.is_def_eq(&fc_n, &expected),
            "FourierCoeff 2 must be def-eq to HCPoint 2 -> Rat"
        );
    }

    /// `FourierCoefficient` and `FourierTransform` are genuine Definitions whose
    /// bodies type-check against their declared types.
    #[test]
    fn test_fourier_coefficient_and_transform_are_definitions() {
        use crate::env::types::ConstantKind;
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in [
            "BoolAnalysis.FourierCoefficient",
            "BoolAnalysis.FourierTransform",
        ] {
            let info = env.get_const(&Name::from_string(name)).expect("registered");
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{name} must be DEFINED, not admitted as an axiom"
            );
            let value = info.value.clone().expect("has body");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} body must check against its type: {e:?}"));
        }
    }

    /// Definitional-correctness pin: `fun n f S => FourierTransform n f S` is
    /// def-eq to `fun n f S => FourierCoefficient n f S` — the transform IS the
    /// coefficient family (the design's `FourierTransform n f := fun S => f̂(S)`).
    #[test]
    fn test_fourier_transform_equals_coefficient_family() {
        use crate::env::decl_builder::EnvDeclBuilder;
        use crate::expr::BinderInfo;
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());

        let nat = k("Nat");
        let bool_fn = k("BoolAnalysis.BoolFn");
        let hcpoint = k("BoolAnalysis.HCPoint");
        let transform = k("BoolAnalysis.FourierTransform");
        let coeff = k("BoolAnalysis.FourierCoefficient");

        let mk_eta = |head_is_transform: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let bool_fn_n = Expr::app(bool_fn.clone(), n.clone());
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let hcp = Expr::app(hcpoint.clone(), n.clone());
            let (s_id, s) = b.fresh_local(hcp.clone());
            // transform: FourierTransform n f S ; coeff: FourierCoefficient n f S
            let body = if head_is_transform {
                Expr::apps(
                    Expr::apps(transform.clone(), [n.clone(), f.clone()]),
                    [s.clone()],
                )
            } else {
                Expr::apps(coeff.clone(), [n.clone(), f.clone(), s.clone()])
            };
            let lam = b.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body);
            let lam = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n.clone(), lam);
            let lam = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), lam);
            b.finish(lam)
        };
        let lhs = mk_eta(true);
        let rhs = mk_eta(false);
        assert!(
            tc.is_def_eq(&lhs, &rhs),
            "fun n f S => FourierTransform n f S must be def-eq to FourierCoefficient n f S"
        );
    }

    /// Sanity (empty-subset coefficient = mean): `FourierCoefficient n f S0` for
    /// the all-false indicator `S0` (the empty subset ∅) ground-reduces to
    /// `Expect n (fun x => pm (f x))` — i.e. `f̂(∅) = E[f̃]`. Because `chi n S0 x`
    /// reduces to `Rat.one` for the empty subset, `pm (f x) · 1 = pm (f x)`. We
    /// pin this at `n = 1` for `f = fun _ => Bool.true` against the explicit mean.
    #[test]
    fn test_fourier_coefficient_empty_subset_is_mean() {
        use crate::env::decl_builder::EnvDeclBuilder;
        use crate::expr::BinderInfo;
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());

        let n = nat_lit(1);
        let hcp1 = Expr::app(k("BoolAnalysis.HCPoint"), n.clone());
        // f : BoolFn 1 := fun _ => Bool.true
        let f = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, _x) = b.fresh_local(hcp1.clone());
            let lam = b.mk_lam(x_id, BinderInfo::Default, hcp1.clone(), k("Bool.true"));
            b.finish(lam)
        };
        // S0 : HCPoint 1 := fun _ => Bool.false  (empty subset)
        let s0 = {
            let mut b = EnvDeclBuilder::new();
            let fin1 = Expr::app(k("Fin"), n.clone());
            let (i_id, _i) = b.fresh_local(fin1.clone());
            let lam = b.mk_lam(i_id, BinderInfo::Default, fin1, k("Bool.false"));
            b.finish(lam)
        };
        let coeff = Expr::apps(
            k("BoolAnalysis.FourierCoefficient"),
            [n.clone(), f.clone(), s0],
        );

        // expected: Expect 1 (fun x => pm (f x)) — the mean of f̃.
        let mean = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(hcp1.clone());
            let body = Expr::app(k("BoolAnalysis.pm"), Expr::app(f.clone(), x));
            let lam = b.mk_lam(x_id, BinderInfo::Default, hcp1.clone(), body);
            b.finish(lam)
        };
        let expected = Expr::apps(k("BoolAnalysis.Expect"), [n, mean]);
        assert!(
            tc.is_def_eq(&coeff, &expected),
            "f̂(∅) must reduce to E[f̃] (empty-subset Fourier coefficient = mean)"
        );
    }
}
