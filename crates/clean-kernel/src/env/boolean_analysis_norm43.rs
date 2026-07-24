// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/`4/3`-norm layer — the **n-dimensional `4/3`-norm carrier** over the
//! cube, the RHS object the `(4/3, 4)` tensorization (the genuine M2 route) needs,
//! axiom-free and M2-route-independent.
//!
//! # What `norm43` is
//!
//! For a general `g : HCPoint n → Rat` on the n-cube, the (un-normalised)
//! `4/3`-norm is the sum of the per-point contributions `|g x|^{4/3}`:
//!
//! ```text
//!   ‖g‖_{4/3} := Σ_{x ∈ cube} |g x|^{4/3}.
//! ```
//!
//! Unlike the landed `m1_norm` materialisation — which is specialised to the FLAT
//! indicator `2^{4/3}·h` — this carrier is GENERAL: each point contributes
//! `pow43Gen |g x| (s x) (r x)`, the general `^{4/3}` of an ARBITRARY nonneg
//! argument (`algebra_nnreal_cbrt_gen.rs`). The cube is laid out over `Fin (2^n)`
//! and enumerated by `hcDecode`, mirroring how the `(2,4)` RHS object is built in
//! `hc24_core_base`.
//!
//! # Witness threading (the per-point scaling witnesses)
//!
//! `pow43Gen x s r hx hs : NNReal := mul (ofRat x hx) (cbrtGen s r hs)` needs, per
//! point, a nonneg argument `hx : 0 ≤ x` and a nonneg scale `hs : 0 ≤ s`. We
//! thread these as follows:
//!
//! * **The argument is `|g x| := Rat.abs (g x)`**, whose nonneg proof is the
//!   landed constructive `Rat.abs_nonneg (g x) : 0 ≤ |g x|` — supplied
//!   automatically per point, NO extra hypothesis required.
//! * **The scale `s` and reduced arg `r` are bundled per-point functions**
//!   `s r : HCPoint n → Rat`, with a SINGLE bundled hypothesis `hs : ∀ x, 0 ≤ s x`
//!   (which `cbrtGen` consumes per point). For every nonneg `|g x|` such a
//!   `(s, r)` exists by the archimedean scaling reduction
//!   (`NNReal.cbrtGen_cubed_at`); here it is supplied abstractly so the carrier is
//!   general over every choice of valid witnesses.
//!
//! The `r < 1` and reconstruction `|g x| = ((s·s)·s)·r` constraints are NOT needed
//! to TYPE the carrier (`pow43Gen` does not consume them); they are consumed only
//! by the cube identity `pow43Gen_cubed`. So `norm43` is honestly the `4/3`-norm
//! value, with the cube-evaluation identity left to the tensorization step.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `BoolAnalysis.norm43 : (n : Nat) → (g s r : HCPoint n → Rat)
//!       → (hs : ∀ x, 0 ≤ s x) → NNReal`
//!     `:= NNReal.finSum (2^n) (fun jx => pow43Gen |g (hcDecode n jx)| …)`.
//!   Reducible `Definition` — the honest `4/3`-norm carrier.
//!
//! - `BoolAnalysis.norm43_cubed : (n : Nat) → (g s r) → (hs) → NNReal`
//!     `:= ((norm43 …)·(norm43 …))·(norm43 …)`. The cube of the norm (the RHS of
//!     the dual HC is `norm43³`). Reducible `Definition`.
//!
//! - `BoolAnalysis.norm43_card_zero` / `BoolAnalysis.norm43_card_succ`: the
//!   `NNReal.finSum` cardinality recursion specialised to the `pow43Gen` summand
//!   `Φ jx := pow43Gen |g (hcDecode N jx)| …`. These are the defining `Nat.rec`
//!   equations the tensorization step consumes — at general cardinality `m` they
//!   give `Σ_{m+1} Φ = (Σ_m (Φ∘castSucc)) ⊕ Φ(last m)`, the low-prefix/last split.
//!   They close by `NNReal.finSum_zero` / `NNReal.finSum_succ` (the genuine
//!   `Nat.rec` ι-steps), so they are real reductions, not placeholder collapses.
//!
//! `Declaration::Definition` (carriers) / `Declaration::Theorem` (equations),
//! `ProofQuality::Constructive`, empty admitted-axiom closure (foundational only).
//! NO `sorry` / `add_decl_unchecked` / `add_decl_structural`. FORBIDDEN here:
//! `Rat.dist`, `Real` / `Real.sqrt`, `NNReal.toRat`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the n-dim `4/3`-norm carrier.
pub(crate) struct Norm43Consts {
    nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_le: Expr,
    rat_abs: Expr,
    rat_abs_nonneg: Expr,
    nat_pow: Expr,
    two: Expr,
    fin: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    nat_succ: Expr,
    hcpoint: Expr,
    hc_decode: Expr,
    nnreal: Expr,
    nnreal_mul: Expr,
    nnreal_add: Expr,
    nnreal_finsum: Expr,
    nnreal_finsum_zero: Expr,
    nnreal_finsum_succ: Expr,
    pow43_gen: Expr,
}

impl Norm43Consts {
    pub(crate) fn new() -> Self {
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let n1 = Expr::app(nat_succ.clone(), nat_zero);
        let two = Expr::app(nat_succ.clone(), n1);
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_le: k("Rat.le"),
            rat_abs: k("Rat.abs"),
            rat_abs_nonneg: k("Rat.abs_nonneg"),
            nat_pow: k("Nat.pow"),
            two,
            fin: k("Fin"),
            fin_cast_succ: k("Fin.castSucc"),
            fin_last: k("Fin.last"),
            nat_succ,
            hcpoint: k("BoolAnalysis.HCPoint"),
            hc_decode: k("BoolAnalysis.hcDecode"),
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_add: k("NNReal.add"),
            nnreal_finsum: k("NNReal.finSum"),
            nnreal_finsum_zero: k("NNReal.finSum_zero"),
            nnreal_finsum_succ: k("NNReal.finSum_succ"),
            pow43_gen: k("NNReal.pow43Gen"),
        }
    }

    // ── type helpers ──────────────────────────────────────────────────────────
    /// `HCPoint n`.
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    /// `HCPoint n → Rat` (the type of `g`, `s`, `r`).
    fn fn_type(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    /// `2^n := Nat.pow 2 n`.
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    /// `Fin m`.
    fn fin_of(&self, m: &Expr) -> Expr {
        Expr::app(self.fin.clone(), m.clone())
    }
    /// `Fin m → NNReal` (the type of an `NNReal.finSum` summand).
    fn fin_to_nnreal(&self, m: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(m), self.nnreal.clone())
    }
    /// `∀ x : HCPoint n, 0 ≤ s x` — the bundled per-point scale-nonneg hyp.
    fn forall_scale_nonneg_ty(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let body = self.le(&self.rat_zero, &Expr::app(s.clone(), x));
        d.finish_child(d.mk_pi(x_id, BinderInfo::Default, hcp, body))
    }

    // ── term helpers ──────────────────────────────────────────────────────────
    fn le(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a.clone(), b.clone()])
    }
    fn abs(&self, a: &Expr) -> Expr {
        Expr::app(self.rat_abs.clone(), a.clone())
    }
    fn abs_nonneg(&self, a: &Expr) -> Expr {
        Expr::app(self.rat_abs_nonneg.clone(), a.clone())
    }
    /// `hcDecode n jx : HCPoint n`.
    fn decode(&self, n: &Expr, jx: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), jx.clone()])
    }
    fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn nnadd(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [a.clone(), b.clone()])
    }
    fn finsum(&self, m: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.nnreal_finsum.clone(), [m.clone(), f.clone()])
    }
    /// `pow43Gen |g x| (s x) (r x) (abs_nonneg (g x)) (hs x)`.
    fn contribution(&self, g: &Expr, s: &Expr, r: &Expr, hs: &Expr, x: &Expr) -> Expr {
        let gx = Expr::app(g.clone(), x.clone());
        let abs_gx = self.abs(&gx);
        let sx = Expr::app(s.clone(), x.clone());
        let rx = Expr::app(r.clone(), x.clone());
        let hx = self.abs_nonneg(&gx); // 0 ≤ |g x|
        let hsx = Expr::app(hs.clone(), x.clone()); // 0 ≤ s x
        Expr::apps(self.pow43_gen.clone(), [abs_gx, sx, rx, hx, hsx])
    }
    /// The cube summand `fun jx : Fin (2^n) => pow43Gen |g (hcDecode n jx)| …`.
    fn cube_summand(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        g: &Expr,
        s: &Expr,
        r: &Expr,
        hs: &Expr,
    ) -> Expr {
        let p2 = self.pow2(n);
        let fin_p2 = self.fin_of(&p2);
        let mut b = EnvDeclBuilder::child_of(parent);
        let (jx_id, jx) = b.fresh_local(fin_p2.clone());
        let x = self.decode(n, &jx);
        let body = self.contribution(g, s, r, hs, &x);
        b.finish_child(b.mk_lam(jx_id, BinderInfo::Default, fin_p2, body))
    }
    /// `NNReal.finSum (2^n) (cube_summand …)` — the carrier body of `norm43`.
    fn norm43_body(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        g: &Expr,
        s: &Expr,
        r: &Expr,
        hs: &Expr,
    ) -> Expr {
        let p2 = self.pow2(n);
        let summand = self.cube_summand(parent, n, g, s, r, hs);
        self.finsum(&p2, &summand)
    }

    // ── Eq.{1} plumbing over NNReal ──────────────────────────────────────────
    fn eq_nn(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [self.nnreal.clone(), a.clone(), b.clone()],
        )
    }
}

impl Environment {
    /// Register the n-dim `4/3`-norm carrier `BoolAnalysis.norm43`, its cube
    /// `BoolAnalysis.norm43_cubed`, and the two `NNReal.finSum` cardinality
    /// recursion equations (`norm43_card_zero`, `norm43_card_succ`) the
    /// tensorization step consumes. Idempotent; foundational-only closure.
    pub fn init_boolean_analysis_norm43(&mut self) -> Result<(), EnvError> {
        self.init_boolean_analysis()?; // HCPoint, hcDecode, Nat.pow
        self.init_algebra_nnreal_finsum()?; // NNReal.finSum, finSum_zero, finSum_succ
        self.init_algebra_nnreal_cbrt_gen()?; // NNReal.pow43Gen, cbrtGen
        self.init_rat_abs()?; // Rat.abs, Rat.abs_nonneg (faithful carrier)
        self.init_eq()?;

        let c = Norm43Consts::new();
        self.register_norm43_def(&c)?;
        self.register_norm43_cubed_def(&c)?;
        self.register_norm43_card_zero(&c)?;
        self.register_norm43_card_succ(&c)?;
        Ok(())
    }

    /// `BoolAnalysis.norm43 : (n : Nat) → (g s r : HCPoint n → Rat)
    ///    → (hs : ∀ x, 0 ≤ s x) → NNReal`
    ///   `:= NNReal.finSum (2^n) (fun jx => pow43Gen |g (hcDecode n jx)| …)`.
    fn register_norm43_def(&mut self, c: &Norm43Consts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.norm43");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = norm43_type(c, &c.nnreal);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let fn_ty = c.fn_type(&n);
            let (g_id, g) = b.fresh_local(fn_ty.clone());
            let (s_id, s) = b.fresh_local(fn_ty.clone());
            let (r_id, r) = b.fresh_local(fn_ty.clone());
            let hs_ty = c.forall_scale_nonneg_ty(&b, &n, &s);
            let (hs_id, hs) = b.fresh_local(hs_ty.clone());
            let body = c.norm43_body(&b, &n, &g, &s, &r, &hs);
            let e = b.mk_lam(hs_id, BinderInfo::Default, hs_ty, body);
            let e = b.mk_lam(r_id, BinderInfo::Default, fn_ty.clone(), e);
            let e = b.mk_lam(s_id, BinderInfo::Default, fn_ty.clone(), e);
            let e = b.mk_lam(g_id, BinderInfo::Default, fn_ty, e);
            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `BoolAnalysis.norm43_cubed : (n : Nat) → (g s r) → (hs) → NNReal`
    ///   `:= ((norm43 …)·(norm43 …))·(norm43 …)` — the cube of the `4/3`-norm
    ///   (the RHS of the dual HC is `norm43³`).
    fn register_norm43_cubed_def(&mut self, c: &Norm43Consts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.norm43_cubed");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = norm43_type(c, &c.nnreal);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let fn_ty = c.fn_type(&n);
            let (g_id, g) = b.fresh_local(fn_ty.clone());
            let (s_id, s) = b.fresh_local(fn_ty.clone());
            let (r_id, r) = b.fresh_local(fn_ty.clone());
            let hs_ty = c.forall_scale_nonneg_ty(&b, &n, &s);
            let (hs_id, hs) = b.fresh_local(hs_ty.clone());
            let nrm = norm43_app(c, &n, &g, &s, &r, &hs);
            let body = c.nnmul(&c.nnmul(&nrm, &nrm), &nrm);
            let e = b.mk_lam(hs_id, BinderInfo::Default, hs_ty, body);
            let e = b.mk_lam(r_id, BinderInfo::Default, fn_ty.clone(), e);
            let e = b.mk_lam(s_id, BinderInfo::Default, fn_ty.clone(), e);
            let e = b.mk_lam(g_id, BinderInfo::Default, fn_ty, e);
            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `BoolAnalysis.norm43_card_zero` — the `n = 0` (single-point) collapse of
    /// the cube `4/3`-norm sum. `2^0 ≡ 1`, so the `NNReal.finSum 1` over the
    /// `pow43Gen` summand `Φ` reduces, via `NNReal.finSum_succ` + `_zero` +
    /// `NNReal.add` on the `NNReal.zero` left summand, to its single cube
    /// contribution. Stated as the genuine `finSum 1`/`finSum 0` recursion brick.
    fn register_norm43_card_zero(&mut self, c: &Norm43Consts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.norm43_card_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = norm43_card_zero(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.norm43_card_succ` — the `NNReal.finSum` last-coordinate
    /// split brick specialised to the `pow43Gen` cube summand. For any summand
    /// function `Φ : Fin (m+1) → NNReal` (here the `4/3`-norm contribution), it
    /// relates the `(m+1)`-point sum to the low-prefix `m`-point sum plus the last
    /// contribution:
    /// `Σ_{m+1} Φ = (Σ_m (fun i => Φ (castSucc i))) ⊕ Φ (last m)`. This is exactly
    /// the brick the `(4/3,4)` tensorization induction step consumes.
    fn register_norm43_card_succ(&mut self, c: &Norm43Consts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.norm43_card_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = norm43_card_succ(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `(n : Nat) → (g s r : HCPoint n → Rat) → (hs : ∀ x, 0 ≤ s x) → out` — the
/// shared Π-telescope of `norm43` / `norm43_cubed` (with `out := NNReal`).
fn norm43_type(c: &Norm43Consts, out: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fn_ty = c.fn_type(&n);
    let (g_id, _g) = b.fresh_local(fn_ty.clone());
    let (s_id, s) = b.fresh_local(fn_ty.clone());
    let (r_id, _r) = b.fresh_local(fn_ty.clone());
    let hs_ty = c.forall_scale_nonneg_ty(&b, &n, &s);
    let (hs_id, _hs) = b.fresh_local(hs_ty.clone());
    let e = b.mk_pi(hs_id, BinderInfo::Default, hs_ty, out.clone());
    let e = b.mk_pi(r_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_pi(s_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_pi(g_id, BinderInfo::Default, fn_ty, e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

/// `BoolAnalysis.norm43 n g s r hs : NNReal` (applied form).
fn norm43_app(c: &Norm43Consts, n: &Expr, g: &Expr, s: &Expr, r: &Expr, hs: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.norm43"), vec![]),
        [n.clone(), g.clone(), s.clone(), r.clone(), hs.clone()],
    )
}

/// `norm43_card_zero` type + proof.
///
/// `∀ (g s r : HCPoint 0 → Rat)(hs : ∀ x, 0 ≤ s x),`
///   `NNReal.finSum (2^0) Φ = NNReal.add NNReal.zero (Φ (Fin.last 0))`
/// where `Φ := cube_summand 0 g s r hs : Fin (2^0) → NNReal`. `2^0 ≡ 1 ≡ succ 0`,
/// so `NNReal.finSum_succ 0 Φ` gives
/// `finSum 1 Φ = add (finSum 0 (Φ∘castSucc)) (Φ (last 0))`, and `finSum_zero`
/// rewrites the left summand to `NNReal.zero` (`congrArg (add · (Φ(last 0)))`).
fn norm43_card_zero(c: &Norm43Consts) -> (Expr, Expr) {
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nnreal_zero = Expr::const_(Name::from_string("NNReal.zero"), vec![]);

    // Build the type.
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let fn_ty = c.fn_type(&zero);
        let (g_id, g) = b.fresh_local(fn_ty.clone());
        let (s_id, s) = b.fresh_local(fn_ty.clone());
        let (r_id, r) = b.fresh_local(fn_ty.clone());
        let hs_ty = c.forall_scale_nonneg_ty(&b, &zero, &s);
        let (hs_id, hs) = b.fresh_local(hs_ty.clone());

        let p2 = c.pow2(&zero); // 2^0
        let summand = c.cube_summand(&b, &zero, &g, &s, &r, &hs);
        let lhs = c.finsum(&p2, &summand);
        // last term: Φ (Fin.last 0)  (Fin.last 0 : Fin (0+1) ≡ Fin 1 ≡ Fin (2^0)).
        let last0 = Expr::app(c.fin_last.clone(), zero.clone());
        let phi_last = Expr::app(summand.clone(), last0);
        let rhs = c.nnadd(&nnreal_zero, &phi_last);
        let concl = c.eq_nn(&lhs, &rhs);

        let e = b.mk_pi(hs_id, BinderInfo::Default, hs_ty, concl);
        let e = b.mk_pi(r_id, BinderInfo::Default, fn_ty.clone(), e);
        let e = b.mk_pi(s_id, BinderInfo::Default, fn_ty.clone(), e);
        b.finish(b.mk_pi(g_id, BinderInfo::Default, fn_ty, e))
    };

    // Build the proof.
    let value = {
        let mut b = EnvDeclBuilder::new();
        let fn_ty = c.fn_type(&zero);
        let (g_id, g) = b.fresh_local(fn_ty.clone());
        let (s_id, s) = b.fresh_local(fn_ty.clone());
        let (r_id, r) = b.fresh_local(fn_ty.clone());
        let hs_ty = c.forall_scale_nonneg_ty(&b, &zero, &s);
        let (hs_id, hs) = b.fresh_local(hs_ty.clone());

        let summand = c.cube_summand(&b, &zero, &g, &s, &r, &hs);
        let last0 = Expr::app(c.fin_last.clone(), zero.clone());
        let phi_last = Expr::app(summand.clone(), last0);

        // Σ_{1} Φ via finSum_succ 0 Φ : finSum 1 Φ = add (finSum 0 (Φ∘castSucc)) (Φ(last 0)).
        // (2^0 ≡ 1 ≡ succ 0 defeq, so finSum_succ 0 has LHS finSum 1 ≡ finSum (2^0).)
        let succ_eq = Expr::apps(
            c.nnreal_finsum_succ.clone(),
            [zero.clone(), summand.clone()],
        );
        // cast-prefix function fun i : Fin 0 => Φ (Fin.castSucc 0 i).
        let cast_prefix = {
            let mut cb = EnvDeclBuilder::child_of(&b);
            let fin0 = c.fin_of(&zero);
            let (i_id, i) = cb.fresh_local(fin0.clone());
            let cast_i = Expr::apps(c.fin_cast_succ.clone(), [zero.clone(), i]);
            let body = Expr::app(summand.clone(), cast_i);
            cb.finish_child(cb.mk_lam(i_id, BinderInfo::Default, fin0, body))
        };
        let prefix_sum = c.finsum(&zero, &cast_prefix); // finSum 0 (Φ∘castSucc)
        let mid = c.nnadd(&prefix_sum, &phi_last); // add prefix_sum (Φ(last 0))

        // finSum_zero (Φ∘castSucc) : finSum 0 (Φ∘castSucc) = NNReal.zero.
        let prefix_zero = Expr::app(
            Expr::const_(Name::from_string("NNReal.finSum_zero"), vec![]),
            cast_prefix.clone(),
        );
        // congrArg (fun w => add w (Φ(last 0))) prefix_zero : mid = add zero (Φ(last 0)).
        let add_motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (w_id, w) = mb.fresh_local(c.nnreal.clone());
            let body = c.nnadd(&w, &phi_last);
            mb.finish_child(mb.mk_lam(w_id, BinderInfo::Default, c.nnreal.clone(), body))
        };
        let congr = Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
            ),
            [
                c.nnreal.clone(),
                c.nnreal.clone(),
                prefix_sum.clone(),
                nnreal_zero.clone(),
                add_motive,
                prefix_zero,
            ],
        );
        let rhs = c.nnadd(&nnreal_zero, &phi_last);

        // chain: finSum (2^0) Φ =[succ_eq] mid =[congr] add zero (Φ(last 0)).
        let p2 = c.pow2(&zero);
        let lhs = c.finsum(&p2, &summand);
        let proof = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.trans"),
                vec![Level::succ(Level::zero())],
            ),
            [c.nnreal.clone(), lhs, mid, rhs, succ_eq, congr],
        );

        let e = b.mk_lam(hs_id, BinderInfo::Default, hs_ty, proof);
        let e = b.mk_lam(r_id, BinderInfo::Default, fn_ty.clone(), e);
        let e = b.mk_lam(s_id, BinderInfo::Default, fn_ty.clone(), e);
        b.finish(b.mk_lam(g_id, BinderInfo::Default, fn_ty, e))
    };

    (ty, value)
}

/// `norm43_card_succ` type + proof — the last-coordinate split brick.
///
/// `∀ (m : Nat)(Φ : Fin (m+1) → NNReal),`
///   `NNReal.finSum (m+1) Φ
///       = NNReal.add (NNReal.finSum m (fun i => Φ (Fin.castSucc m i)))
///                     (Φ (Fin.last m))`
/// closing by `NNReal.finSum_succ m Φ` directly. (Stated over an abstract summand
/// `Φ` — the `pow43Gen` contribution is one such `Φ — so the tensorization step
/// can specialise it to its own cube summand without re-deriving the recursion.)
fn norm43_card_succ(c: &Norm43Consts) -> (Expr, Expr) {
    let nat_succ = c.nat_succ.clone();

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(c.nat.clone());
        let succ_m = Expr::app(nat_succ.clone(), m.clone());
        let phi_ty = c.fin_to_nnreal(&succ_m);
        let (phi_id, phi) = b.fresh_local(phi_ty.clone());

        let lhs = c.finsum(&succ_m, &phi);
        let cast_prefix = cast_prefix_fn(c, &b, &m, &phi);
        let prefix_sum = c.finsum(&m, &cast_prefix);
        let last_m = Expr::app(c.fin_last.clone(), m.clone());
        let phi_last = Expr::app(phi.clone(), last_m);
        let rhs = c.nnadd(&prefix_sum, &phi_last);
        let concl = c.eq_nn(&lhs, &rhs);

        let e = b.mk_pi(phi_id, BinderInfo::Default, phi_ty, concl);
        b.finish(b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e))
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(c.nat.clone());
        let succ_m = Expr::app(nat_succ.clone(), m.clone());
        let phi_ty = c.fin_to_nnreal(&succ_m);
        let (phi_id, phi) = b.fresh_local(phi_ty.clone());

        // NNReal.finSum_succ m Φ : finSum (m+1) Φ = add (finSum m (Φ∘castSucc)) (Φ(last m)).
        let proof = Expr::apps(c.nnreal_finsum_succ.clone(), [m.clone(), phi.clone()]);

        let e = b.mk_lam(phi_id, BinderInfo::Default, phi_ty, proof);
        b.finish(b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e))
    };

    (ty, value)
}

/// `fun i : Fin m => Φ (Fin.castSucc m i)` — the cast-prefix reindexing function
/// (byte-identical to `NNReal.finSum_succ`'s LHS shape so the recursion closes).
fn cast_prefix_fn(c: &Norm43Consts, parent: &EnvDeclBuilder, m: &Expr, phi: &Expr) -> Expr {
    let fin_m = c.fin_of(m);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = b.fresh_local(fin_m.clone());
    let cast_i = Expr::apps(c.fin_cast_succ.clone(), [m.clone(), i]);
    let body = Expr::app(phi.clone(), cast_i);
    b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_m, body))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const DEFS: &[&str] = &["BoolAnalysis.norm43", "BoolAnalysis.norm43_cubed"];
    const THEOREMS: &[&str] = &[
        "BoolAnalysis.norm43_card_zero",
        "BoolAnalysis.norm43_card_succ",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_norm43()
            .expect("init_boolean_analysis_norm43");
        env.init_boolean_analysis_norm43().expect("idempotent");
        env
    }

    #[test]
    fn test_norm43_defs_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in DEFS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{name} must be Definition"
            );
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_norm43_equations_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_norm43_equations_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
