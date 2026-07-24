// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Stage B2: the finite-prefix running max `NNRat.prefixMax`.
//!
//! # Why this module exists
//!
//! `NNReal.CauSeq` boundedness (the precise rung the `NNReal.mul` respect proof
//! needs — plan `designs/2026-06-18-kkl-real-sqrt-layer-plan.md`, Stage B2) is
//! built as `B = max(prefix max over [0,N], f N + 1)`. The "prefix max over a
//! finite initial segment" is a running `max` defined by `Nat`-recursion. This
//! module builds that fold and the single fact the bound needs:
//! **every prefix element is `≤` the running max**.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNRat.prefixMax : (Nat → NNRat) → Nat → NNRat`
//!     `prefixMax g 0       := g 0`
//!     `prefixMax g (n+1)   := NNRat.max (prefixMax g n) (g (n+1))`
//!   (`@Nat.rec (fun _ => NNRat) (g 0) (fun n ih => NNRat.max ih (g (n+1))) k`.)
//! - `NNRat.self_le_prefixMax  : ∀ g n, NNRat.le (g n) (prefixMax g n)`
//!     (`Nat.rec` on `n`: base `le_refl`, step `le_max_right` — no IH needed).
//! - `NNRat.prefixMax_le_succ  : ∀ g n, NNRat.le (prefixMax g n) (prefixMax g (n+1))`
//!     (one step of `le_max_left` — no induction).
//! - `NNRat.prefixMax_mono     : ∀ g k n, Nat.le k n →`
//!     `NNRat.le (prefixMax g k) (prefixMax g n)`
//!     (`Nat.le.rec` on the `≤` proof: base `le_refl`, step chains the IH through
//!     `prefixMax_le_succ` with `NNRat.le_trans`).
//! - `NNRat.le_prefixMax       : ∀ g k n, Nat.le k n → NNRat.le (g k) (prefixMax g n)`
//!     (`le_trans (self_le_prefixMax g k) (prefixMax_mono g k n h)`).
//!
//! `le_prefixMax` is the load-bearing finite-prefix bound: it says the running
//! max over `[0,n]` dominates every entry up to `n` — exactly the prefix piece
//! of the boundedness `B`. Every declaration is a `Definition` or kernel-checked
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the running-max fold.
pub(crate) struct PrefixMaxConsts {
    nat: Expr,
    nnrat: Expr,
    nnrat_max: Expr,
    nnrat_le: Expr,
    nnrat_le_refl: Expr,
    nnrat_le_trans: Expr,
    nnrat_le_max_left: Expr,
    nnrat_le_max_right: Expr,
    prefix_max: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_le: Expr,
    // Nat.rec eliminating into Sort 1 (NNRat : Type 0) — motive returns NNRat.
    nat_rec_nnrat: Expr,
    // Nat.le.rec for induction on the ≤ proof (the refl/step minors are built
    // from `NNRat.le_refl` / `NNRat.le_trans`, so the Nat.le ctors are not used
    // directly here).
    nat_le_rec: Expr,
}

impl PrefixMaxConsts {
    pub(crate) fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nnrat: k("NNRat"),
            nnrat_max: k("NNRat.max"),
            nnrat_le: k("NNRat.le"),
            nnrat_le_refl: k("NNRat.le_refl"),
            nnrat_le_trans: k("NNRat.le_trans"),
            nnrat_le_max_left: k("NNRat.le_max_left"),
            nnrat_le_max_right: k("NNRat.le_max_right"),
            prefix_max: k("NNRat.prefixMax"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_le: k("Nat.le"),
            // NNRat : Type 0 = Sort 1, so eliminating into NNRat is Nat.rec.{1}.
            nat_rec_nnrat: Expr::const_(
                Name::from_string("Nat.rec"),
                vec![Level::succ(Level::zero())],
            ),
            nat_le_rec: k("Nat.le.rec"),
        }
    }

    fn seq_ty(&self) -> Expr {
        Expr::pi(BinderInfo::Default, self.nat.clone(), self.nnrat.clone())
    }
    /// `g n : NNRat`.
    fn at(&self, g: Expr, n: Expr) -> Expr {
        Expr::app(g, n)
    }
    /// `Nat.succ n`.
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    /// `NNRat.max a b`.
    fn nmax(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnrat_max.clone(), [a, b])
    }
    /// `NNRat.le p q : Prop`.
    fn le(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_le.clone(), [p, q])
    }
    /// `NNRat.prefixMax g n : NNRat`.
    fn pmax(&self, g: Expr, n: Expr) -> Expr {
        Expr::apps(self.prefix_max.clone(), [g, n])
    }
    /// `Nat.le a b : Prop`.
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    /// `NNRat.le_refl p`.
    fn le_refl(&self, p: Expr) -> Expr {
        Expr::app(self.nnrat_le_refl.clone(), p)
    }
    /// `NNRat.le_trans p q r h1 h2`.
    fn le_trans(&self, p: Expr, q: Expr, r: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.nnrat_le_trans.clone(), [p, q, r, h1, h2])
    }
    /// `NNRat.le_max_left p q`.
    fn le_max_left(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_le_max_left.clone(), [p, q])
    }
    /// `NNRat.le_max_right p q`.
    fn le_max_right(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_le_max_right.clone(), [p, q])
    }
}

impl Environment {
    /// Register `NNRat.prefixMax` + its four monotonicity facts. Idempotent.
    /// Pulls in the Stage-B1 base, `NNRat.max`/lattice, and `NNRat` order lemmas.
    pub fn init_algebra_nnreal_nnrat_prefixmax(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_nnrat_max()?;
        self.init_algebra_nnreal_nnrat_order()?;
        let c = PrefixMaxConsts::new();
        self.register_nnrat_prefix_max(&c)?;
        self.register_nnrat_self_le_prefix_max(&c)?;
        self.register_nnrat_prefix_max_le_succ(&c)?;
        self.register_nnrat_prefix_max_mono(&c)?;
        self.register_nnrat_le_prefix_max(&c)?;
        Ok(())
    }

    /// `NNRat.prefixMax g n := Nat.rec (g 0) (fun n ih => NNRat.max ih (g (succ n))) n`.
    fn register_nnrat_prefix_max(&mut self, c: &PrefixMaxConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNRat.prefixMax"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.seq_ty(),
            Expr::pi(BinderInfo::Default, c.nat.clone(), c.nnrat.clone()),
        );
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (g_id, g) = b.fresh_local(c.seq_ty());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            // motive := fun _ : Nat => NNRat
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (x_id, _x) = m.fresh_local(c.nat.clone());
                m.finish_child(m.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), c.nnrat.clone()))
            };
            // zero-case := g 0
            let zero_case = c.at(g.clone(), c.nat_zero.clone());
            // succ-case := fun (k : Nat) (ih : NNRat) => NNRat.max ih (g (succ k))
            let succ_case = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (k_id, k) = s.fresh_local(c.nat.clone());
                let (ih_id, ih) = s.fresh_local(c.nnrat.clone());
                let body = c.nmax(ih, c.at(g.clone(), c.succ(k.clone())));
                let e = s.mk_lam(ih_id, BinderInfo::Default, c.nnrat.clone(), body);
                let e = s.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
                s.finish_child(e)
            };
            let rec = Expr::apps(
                c.nat_rec_nnrat.clone(),
                [motive, zero_case, succ_case, n.clone()],
            );
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec);
            let e = b.mk_lam(g_id, BinderInfo::Default, c.seq_ty(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNRat.prefixMax"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNRat.self_le_prefixMax : ∀ g n, NNRat.le (g n) (prefixMax g n)`.
    ///
    /// `Nat.rec` on `n`. base: `prefixMax g 0 ≡ g 0`, so `g 0 ≤ g 0` = `le_refl`.
    /// step at `k` (NO IH used): `prefixMax g (k+1) ≡ NNRat.max (prefixMax g k)
    /// (g (k+1))`, so `g (k+1) ≤ that` = `le_max_right (prefixMax g k)(g (k+1))`.
    fn register_nnrat_self_le_prefix_max(&mut self, c: &PrefixMaxConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNRat.self_le_prefixMax"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (g_id, g) = b.fresh_local(c.seq_ty());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let concl = c.le(c.at(g.clone(), n.clone()), c.pmax(g.clone(), n.clone()));
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(g_id, BinderInfo::Default, c.seq_ty(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (g_id, g) = b.fresh_local(c.seq_ty());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            // motive := fun (m : Nat) => NNRat.le (g m) (prefixMax g m)
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (mm_id, mm) = m.fresh_local(c.nat.clone());
                let body = c.le(c.at(g.clone(), mm.clone()), c.pmax(g.clone(), mm.clone()));
                m.finish_child(m.mk_lam(mm_id, BinderInfo::Default, c.nat.clone(), body))
            };
            // zero-case : NNRat.le (g 0) (prefixMax g 0)  ≡  le (g 0)(g 0) = le_refl (g 0).
            let zero_case = c.le_refl(c.at(g.clone(), c.nat_zero.clone()));
            // succ-case := fun (k : Nat) (_ih) =>
            //   le_max_right (prefixMax g k) (g (k+1))
            //   : NNRat.le (g (k+1)) (NNRat.max (prefixMax g k)(g (k+1)))
            //   ≡ NNRat.le (g (k+1)) (prefixMax g (k+1)).
            let succ_case = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (k_id, k) = s.fresh_local(c.nat.clone());
                // ih type : motive k = NNRat.le (g k)(prefixMax g k)
                let ih_ty = c.le(c.at(g.clone(), k.clone()), c.pmax(g.clone(), k.clone()));
                let (ih_id, _ih) = s.fresh_local(ih_ty.clone());
                let body = c.le_max_right(
                    c.pmax(g.clone(), k.clone()),
                    c.at(g.clone(), c.succ(k.clone())),
                );
                let e = s.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                let e = s.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
                s.finish_child(e)
            };
            // Nat.rec into Prop (motive : Nat → Prop) — Nat.rec.{0}.
            let nat_rec_prop = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
            let rec = Expr::apps(nat_rec_prop, [motive, zero_case, succ_case, n.clone()]);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec);
            let e = b.mk_lam(g_id, BinderInfo::Default, c.seq_ty(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNRat.self_le_prefixMax"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNRat.prefixMax_le_succ : ∀ g n, NNRat.le (prefixMax g n)(prefixMax g (n+1))`.
    ///
    /// `prefixMax g (n+1) ≡ NNRat.max (prefixMax g n)(g (n+1))`; the LHS is the
    /// left argument of that max, so `le_max_left (prefixMax g n)(g (n+1))`.
    fn register_nnrat_prefix_max_le_succ(&mut self, c: &PrefixMaxConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNRat.prefixMax_le_succ"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (g_id, g) = b.fresh_local(c.seq_ty());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let concl = c.le(
                c.pmax(g.clone(), n.clone()),
                c.pmax(g.clone(), c.succ(n.clone())),
            );
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(g_id, BinderInfo::Default, c.seq_ty(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (g_id, g) = b.fresh_local(c.seq_ty());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let body = c.le_max_left(
                c.pmax(g.clone(), n.clone()),
                c.at(g.clone(), c.succ(n.clone())),
            );
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_lam(g_id, BinderInfo::Default, c.seq_ty(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNRat.prefixMax_le_succ"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNRat.prefixMax_mono : ∀ g k n, Nat.le k n → NNRat.le (prefixMax g k)(prefixMax g n)`.
    ///
    /// `Nat.le.rec` on the `Nat.le k n` proof (parameter `k`). Motive
    /// `fun (t : Nat)(_ : Nat.le k t) => NNRat.le (prefixMax g k)(prefixMax g t)`:
    /// - refl (`t = k`): `NNRat.le_refl (prefixMax g k)`.
    /// - step (`t → succ m`, `ih : NNRat.le (prefixMax g k)(prefixMax g m)`):
    ///   chain `ih` with `prefixMax_le_succ g m : prefixMax g m ≤ prefixMax g (m+1)`
    ///   via `NNRat.le_trans`.
    fn register_nnrat_prefix_max_mono(&mut self, c: &PrefixMaxConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNRat.prefixMax_mono"))
            .is_some()
        {
            return Ok(());
        }
        let prefix_max_le_succ = Expr::const_(Name::from_string("NNRat.prefixMax_le_succ"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (g_id, g) = b.fresh_local(c.seq_ty());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hyp = c.nat_le(k.clone(), n.clone());
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let concl = c.le(c.pmax(g.clone(), k.clone()), c.pmax(g.clone(), n.clone()));
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(g_id, BinderInfo::Default, c.seq_ty(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (g_id, g) = b.fresh_local(c.seq_ty());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hyp = c.nat_le(k.clone(), n.clone());
            let (h_id, h) = b.fresh_local(hyp.clone());

            // motive := fun (t : Nat) (_ : Nat.le k t) =>
            //   NNRat.le (prefixMax g k)(prefixMax g t)
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = m.fresh_local(c.nat.clone());
                let le_k_t = c.nat_le(k.clone(), t.clone());
                let (ht_id, _ht) = m.fresh_local(le_k_t.clone());
                let body = c.le(c.pmax(g.clone(), k.clone()), c.pmax(g.clone(), t.clone()));
                let lam_h = m.mk_lam(ht_id, BinderInfo::Default, le_k_t, body);
                let lam_t = m.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), lam_h);
                m.finish_child(lam_t)
            };
            // refl minor : NNRat.le (prefixMax g k)(prefixMax g k) = le_refl (prefixMax g k).
            let minor_refl = c.le_refl(c.pmax(g.clone(), k.clone()));
            // step minor : fun {m}(_ : Nat.le k m)(ih : NNRat.le (pmax g k)(pmax g m)) =>
            //   le_trans (pmax g k)(pmax g m)(pmax g (m+1)) ih (prefixMax_le_succ g m).
            let minor_step = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (m_id, m) = s.fresh_local(c.nat.clone());
                let le_k_m = c.nat_le(k.clone(), m.clone());
                let (hm_id, _hm) = s.fresh_local(le_k_m.clone());
                let ih_ty = c.le(c.pmax(g.clone(), k.clone()), c.pmax(g.clone(), m.clone()));
                let (ih_id, ih) = s.fresh_local(ih_ty.clone());
                let step_le = Expr::apps(prefix_max_le_succ.clone(), [g.clone(), m.clone()]);
                let body = c.le_trans(
                    c.pmax(g.clone(), k.clone()),
                    c.pmax(g.clone(), m.clone()),
                    c.pmax(g.clone(), c.succ(m.clone())),
                    ih,
                    step_le,
                );
                let lam_ih = s.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                let lam_hm = s.mk_lam(hm_id, BinderInfo::Default, le_k_m, lam_ih);
                let lam_m = s.mk_lam(m_id, BinderInfo::Implicit, c.nat.clone(), lam_hm);
                s.finish_child(lam_m)
            };
            // @Nat.le.rec k motive minor_refl minor_step n h
            let rec = Expr::apps(
                c.nat_le_rec.clone(),
                [
                    k.clone(),
                    motive,
                    minor_refl,
                    minor_step,
                    n.clone(),
                    h.clone(),
                ],
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, rec);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(g_id, BinderInfo::Default, c.seq_ty(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNRat.prefixMax_mono"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNRat.le_prefixMax : ∀ g k n, Nat.le k n → NNRat.le (g k)(prefixMax g n)`.
    ///
    /// `le_trans (g k)(prefixMax g k)(prefixMax g n) (self_le_prefixMax g k)
    /// (prefixMax_mono g k n h)`.
    fn register_nnrat_le_prefix_max(&mut self, c: &PrefixMaxConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNRat.le_prefixMax"))
            .is_some()
        {
            return Ok(());
        }
        let self_le = Expr::const_(Name::from_string("NNRat.self_le_prefixMax"), vec![]);
        let mono = Expr::const_(Name::from_string("NNRat.prefixMax_mono"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (g_id, g) = b.fresh_local(c.seq_ty());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hyp = c.nat_le(k.clone(), n.clone());
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let concl = c.le(c.at(g.clone(), k.clone()), c.pmax(g.clone(), n.clone()));
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(g_id, BinderInfo::Default, c.seq_ty(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (g_id, g) = b.fresh_local(c.seq_ty());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hyp = c.nat_le(k.clone(), n.clone());
            let (h_id, h) = b.fresh_local(hyp.clone());
            // self_le g k : NNRat.le (g k)(prefixMax g k)
            let h_self = Expr::apps(self_le.clone(), [g.clone(), k.clone()]);
            // mono g k n h : NNRat.le (prefixMax g k)(prefixMax g n)
            let h_mono = Expr::apps(mono.clone(), [g.clone(), k.clone(), n.clone(), h]);
            let body = c.le_trans(
                c.at(g.clone(), k.clone()),
                c.pmax(g.clone(), k.clone()),
                c.pmax(g.clone(), n.clone()),
                h_self,
                h_mono,
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(g_id, BinderInfo::Default, c.seq_ty(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNRat.le_prefixMax"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const DEFS: &[&str] = &["NNRat.prefixMax"];
    const THEOREMS: &[&str] = &[
        "NNRat.self_le_prefixMax",
        "NNRat.prefixMax_le_succ",
        "NNRat.prefixMax_mono",
        "NNRat.le_prefixMax",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_nnrat_prefixmax()
            .expect("init_algebra_nnreal_nnrat_prefixmax");
        env.init_algebra_nnreal_nnrat_prefixmax()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_nnrat_prefixmax_all_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in DEFS.iter().chain(THEOREMS.iter()) {
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
    fn test_nnrat_prefixmax_theorems_constructive_empty_closure() {
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
