// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — `NNReal.IsCauchy_bounded` (the load-bearing lemma
//! `NNReal.mul` needs).
//!
//! # Why this module exists
//!
//! The sqrt panel proved `NNReal.mul` IMPOSSIBLE over an unbounded rep: the
//! multiplicative `Quot.lift` respect proof needs the shared factor BOUNDED.
//! With the Cauchy SUBTYPE carrier every representative is Cauchy, hence
//! bounded. This module proves that:
//!
//! - `NNReal.IsCauchy_bounded : ∀ (f : Nat → NNRat), IsCauchy f →
//!       ∃ (B : NNRat), ∀ n, NNRat.le (f n) B`
//!
//! # Proof shape
//!
//! Take `ε = 1` (`Rat.zero_lt_one`) to get `N0` with: for `m,n ≥ N0`,
//! `val (f m) < val (f n) + 1`. Define the running max
//! `runMax f : Nat → NNRat` by `Nat.rec`:
//!   `runMax f 0 = f 0`,  `runMax f (k+1) = NNRat.max (runMax f k) (f (k+1))`,
//! and prove the prefix-domination
//!   `runMax_dominates : ∀ f N, ∀ k, Nat.le k N → NNRat.le (f k) (runMax f N)`
//! by `Nat.rec` on `N` (base: `casesOn k` + `Nat.not_succ_le_zero`; step:
//! `Nat.lt_or_eq_of_le` split into `k ≤ N` [ih + `le_max_left` + `le_trans`] or
//! `k = succ N` [`le_max_right`]).
//!
//! The bound is `B := NNRat.max (runMax f N0) (NNRat.add (f N0) NNRat.one)`.
//! For any `n`, `Nat.le_total n N0` splits:
//!   * `n ≤ N0`:  `f n ≤ runMax f N0 ≤ B`  (`runMax_dominates` + `le_max_left`).
//!   * `N0 ≤ n`:  the Cauchy bound at `(m=n, n=N0, ε=1)` gives
//!     `val (f n) < val (f N0) + 1`, hence `f n ≤ f N0 + 1 ≤ B`
//!     (strict→`≤` via `Rat.lt_iff_le_not_le`; `NNRat.val_add`/`val_one`
//!     transport; `le_max_right`).
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `IsCauchy_bounded`.
pub(crate) struct BoundedConsts {
    prop: Expr,
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nnrat: Expr,
    nnrat_max: Expr,
    nnrat_le: Expr,
    nnrat_le_refl: Expr,
    nnrat_le_trans: Expr,
    nnrat_le_max_left: Expr,
    nnrat_le_max_right: Expr,
    is_cauchy: Expr,
    nat_le: Expr,
    nat_lt: Expr,
    // Nat lemmas.
    nat_le_of_succ_le_succ: Expr,
    nat_not_succ_le_zero: Expr,
    nat_lt_or_eq_of_le: Expr,
    nat_le_total: Expr,
    // logic.
    exists_c: Expr,
    exists_intro: Expr,
    or_c: Expr,
    or_rec: Expr,
    eq_c: Expr,
    eq_subst: Expr,
    false_elim: Expr,
    // Nat.rec (motive into Prop for the induction).
    nat_rec_prop: Expr,
    nat_rec_nnrat: Expr,
    nat_cases_prop: Expr,
    // Rat / NNRat surface for the tail bound.
    rat: Expr,
    rat_one: Expr,
    rat_lt: Expr,
    rat_le: Expr,
    rat_add: Expr,
    rat_zero_lt_one: Expr,
    rat_lt_iff_le_not_le: Expr,
    rat_le_trans: Expr,
    nnrat_val: Expr,
    nnrat_add: Expr,
    nnrat_one: Expr,
    nnrat_val_add: Expr,
    nnrat_val_of_rat: Expr,
    rat_zero_le_one: Expr,
    and_c: Expr,
    and_left: Expr,
    not_c: Expr,
    iff_mp: Expr,
    eq_symm: Expr,
}

impl BoundedConsts {
    pub(crate) fn new() -> Self {
        let lvl0 = Level::zero();
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nnrat: k("NNRat"),
            nnrat_max: k("NNRat.max"),
            nnrat_le: k("NNRat.le"),
            nnrat_le_refl: k("NNRat.le_refl"),
            nnrat_le_trans: k("NNRat.le_trans"),
            nnrat_le_max_left: k("NNRat.le_max_left"),
            nnrat_le_max_right: k("NNRat.le_max_right"),
            is_cauchy: k("NNReal.IsCauchy"),
            nat_le: k("Nat.le"),
            nat_lt: k("Nat.lt"),
            nat_le_of_succ_le_succ: k("Nat.le_of_succ_le_succ"),
            nat_not_succ_le_zero: k("Nat.not_succ_le_zero"),
            nat_lt_or_eq_of_le: k("Nat.lt_or_eq_of_le"),
            nat_le_total: k("Nat.le_total"),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![lvl1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![lvl1.clone()]),
            or_c: k("Or"),
            or_rec: k("Or.rec"),
            eq_c: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1.clone()]),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![lvl0.clone()]),
            nat_rec_prop: Expr::const_(Name::from_string("Nat.rec"), vec![lvl0.clone()]),
            nat_rec_nnrat: Expr::const_(Name::from_string("Nat.rec"), vec![lvl1.clone()]),
            nat_cases_prop: Expr::const_(Name::from_string("Nat.casesOn"), vec![lvl0]),
            rat: k("Rat"),
            rat_one: k("Rat.one"),
            rat_lt: k("Rat.lt"),
            rat_le: k("Rat.le"),
            rat_add: k("Rat.add"),
            rat_zero_lt_one: k("Rat.zero_lt_one"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            rat_le_trans: k("Rat.le_trans"),
            nnrat_val: k("NNRat.val"),
            nnrat_add: k("NNRat.add"),
            nnrat_one: k("NNRat.one"),
            nnrat_val_add: k("NNRat.val_add"),
            nnrat_val_of_rat: k("NNRat.val_ofRat"),
            rat_zero_le_one: k("Rat.zero_le_one"),
            and_c: k("And"),
            and_left: k("And.left"),
            not_c: k("Not"),
            iff_mp: k("Iff.mp"),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1]),
        }
    }

    fn seq_ty(&self) -> Expr {
        Expr::pi(BinderInfo::Default, self.nat.clone(), self.nnrat.clone())
    }
    fn at(&self, f: &Expr, n: &Expr) -> Expr {
        Expr::app(f.clone(), n.clone())
    }
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn nle(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_le.clone(), [p, q])
    }
    fn nmax(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_max.clone(), [p, q])
    }
    fn is_cauchy(&self, f: Expr) -> Expr {
        Expr::app(self.is_cauchy.clone(), f)
    }
    fn nle_refl(&self, p: Expr) -> Expr {
        Expr::app(self.nnrat_le_refl.clone(), p)
    }
    fn nle_trans(&self, p: Expr, q: Expr, r: Expr, hpq: Expr, hqr: Expr) -> Expr {
        Expr::apps(self.nnrat_le_trans.clone(), [p, q, r, hpq, hqr])
    }
    fn nle_max_left(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_le_max_left.clone(), [p, q])
    }
    fn nle_max_right(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_le_max_right.clone(), [p, q])
    }
    fn val(&self, q: Expr) -> Expr {
        Expr::app(self.nnrat_val.clone(), q)
    }
    fn radd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn rlt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn nnadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnrat_add.clone(), [a, b])
    }
    /// `NNRat.val_add p q : Eq Rat (val (NNRat.add p q)) ((val p)+(val q))`.
    fn val_add(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_val_add.clone(), [p, q])
    }
    /// `Rat.le_trans a b c hab hbc : Rat.le a c`.
    fn rle_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.rat_le_trans.clone(), [a, b, cc, hab, hbc])
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `@Eq.symm Rat a b h : Eq Rat b a`.
    fn eq_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    /// `Rat.le_of_lt`-style bridge: from `hlt : Rat.lt a b`, extract `Rat.le a b`
    /// via `And.left (Iff.mp (Rat.lt_iff_le_not_le a b) hlt)`.
    fn le_of_lt(&self, a: Expr, b: Expr, hlt: Expr) -> Expr {
        let le_ab = self.rle(a.clone(), b.clone());
        let not_le_ba = Expr::app(self.not_c.clone(), self.rle(b.clone(), a.clone()));
        let and_ty = Expr::apps(self.and_c.clone(), [le_ab.clone(), not_le_ba.clone()]);
        let lt_ab = self.rlt(a.clone(), b.clone());
        let iff = Expr::apps(self.rat_lt_iff_le_not_le.clone(), [a, b]);
        let mp = Expr::apps(self.iff_mp.clone(), [lt_ab, and_ty, iff, hlt]);
        Expr::apps(self.and_left.clone(), [le_ab, not_le_ba, mp])
    }

    /// `NNReal.runMax f N : NNRat` — the running max
    ///   `@Nat.rec.{1} (fun _ => NNRat) (f 0) (fun k ih => NNRat.max ih (f (succ k))) N`.
    fn run_max(&self, parent: &EnvDeclBuilder, f: &Expr, n: &Expr) -> Expr {
        let motive = {
            let mut m = EnvDeclBuilder::child_of(parent);
            let (x_id, _x) = m.fresh_local(self.nat.clone());
            m.finish_child(m.mk_lam(
                x_id,
                BinderInfo::Default,
                self.nat.clone(),
                self.nnrat.clone(),
            ))
        };
        let base = self.at(f, &self.nat_zero.clone());
        let step = {
            let mut s = EnvDeclBuilder::child_of(parent);
            let (k_id, kk) = s.fresh_local(self.nat.clone());
            let (ih_id, ih) = s.fresh_local(self.nnrat.clone());
            let body = self.nmax(ih, self.at(f, &self.succ(kk.clone())));
            let e = s.mk_lam(ih_id, BinderInfo::Default, self.nnrat.clone(), body);
            let e = s.mk_lam(k_id, BinderInfo::Default, self.nat.clone(), e);
            s.finish_child(e)
        };
        Expr::apps(self.nat_rec_nnrat.clone(), [motive, base, step, n.clone()])
    }
}

impl Environment {
    /// Register `NNReal.runMax`, `NNReal.runMax_dominates`, and
    /// `NNReal.IsCauchy_bounded`. Idempotent.
    pub fn init_algebra_nnreal_bounded(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_cauchy()?; // NNReal.IsCauchy, CauSeq, NNRat.*
        self.init_algebra_nnreal_nnrat_max()?; // NNRat.max, le_refl/trans/le_max_*
        self.init_nat()?; // Nat, Nat.rec, Nat.casesOn, Nat.zero, Nat.succ
        self.init_classical()?; // Or, Or.elim
        self.init_true_false()?; // False, False.elim
        self.init_eq()?;
        self.init_exists()?;
        self.register_nat_not_succ_le_zero_theorem()?;
        self.register_nat_le_of_succ_le_succ_theorem()?;
        self.init_nat_totality_proofs()?; // Nat.lt_or_eq_of_le, Nat.le_total
        self.init_nat_lt_or_eq_of_le()?;
        self.init_iff()?; // Iff.mp (strict→le bridge)
        self.init_and()?; // And.left

        let c = BoundedConsts::new();
        self.register_nnreal_run_max(&c)?;
        self.register_nnreal_run_max_dominates(&c)?;
        self.register_nnreal_is_cauchy_bounded(&c)?;
        Ok(())
    }

    /// `NNReal.IsCauchy_bounded : ∀ (f : Nat → NNRat), IsCauchy f →
    ///    ∃ (B : NNRat), ∀ n, NNRat.le (f n) B`.
    fn register_nnreal_is_cauchy_bounded(&mut self, c: &BoundedConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.IsCauchy_bounded");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // bound_pred B := ∀ n, NNRat.le (f n) B — but f is bound in the type, so
        // we build it with f in scope.
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.seq_ty());
            let hcau = c.is_cauchy(f.clone());
            let (h_id, _h) = b.fresh_local(hcau.clone());
            // ∃ B : NNRat, ∀ n, NNRat.le (f n) B.
            let pred_b = {
                let mut pb = EnvDeclBuilder::child_of(&b);
                let (bb_id, bb) = pb.fresh_local(c.nnrat.clone());
                let inner = {
                    let mut ib = EnvDeclBuilder::child_of(&pb);
                    let (n_id, n) = ib.fresh_local(c.nat.clone());
                    let concl = c.nle(c.at(&f, &n), bb.clone());
                    ib.finish_child(ib.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl))
                };
                pb.finish_child(pb.mk_lam(bb_id, BinderInfo::Default, c.nnrat.clone(), inner))
            };
            let exists_b = Expr::apps(c.exists_c.clone(), [c.nnrat.clone(), pred_b]);
            let e = b.mk_pi(h_id, BinderInfo::Default, hcau, exists_b);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.seq_ty(), e);
            b.finish(e)
        };
        let value = build_is_cauchy_bounded_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.runMax : (Nat → NNRat) → Nat → NNRat`.
    fn register_nnreal_run_max(&mut self, c: &BoundedConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.runMax");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.seq_ty(),
            Expr::pi(BinderInfo::Default, c.nat.clone(), c.nnrat.clone()),
        );
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.seq_ty());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let body = c.run_max(&b, &f, &n);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_lam(f_id, BinderInfo::Default, c.seq_ty(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNReal.runMax_dominates :
    ///    ∀ (f : Nat → NNRat) (N : Nat), ∀ (k : Nat), Nat.le k N →
    ///      NNRat.le (f k) (NNReal.runMax f N)`.
    fn register_nnreal_run_max_dominates(&mut self, c: &BoundedConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.runMax_dominates");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let run_max = Expr::const_(Name::from_string("NNReal.runMax"), vec![]);
        let rmax = |f: &Expr, n: &Expr| Expr::apps(run_max.clone(), [f.clone(), n.clone()]);

        // Type: ∀ f N k, Nat.le k N → NNRat.le (f k) (runMax f N).
        let dom_at = |f: &Expr, nn: &Expr, parent: &EnvDeclBuilder| -> Expr {
            // ∀ k, Nat.le k N → NNRat.le (f k)(runMax f N).
            let mut b = EnvDeclBuilder::child_of(parent);
            let (k_id, kk) = b.fresh_local(c.nat.clone());
            let hle = c.nat_le(kk.clone(), nn.clone());
            let (h_id, _h) = b.fresh_local(hle.clone());
            let concl = c.nle(c.at(f, &kk), rmax(f, nn));
            let e = b.mk_pi(h_id, BinderInfo::Default, hle, concl);
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish_child(e)
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.seq_ty());
            let (nn_id, nn) = b.fresh_local(c.nat.clone());
            let body = dom_at(&f, &nn, &b);
            let e = b.mk_pi(nn_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.seq_ty(), e);
            b.finish(e)
        };

        let value = build_run_max_dominates_proof(c, &dom_at, &rmax);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build the proof of `NNReal.runMax_dominates` by `Nat.rec` on `N`.
fn build_run_max_dominates_proof(
    c: &BoundedConsts,
    dom_at: &dyn Fn(&Expr, &Expr, &EnvDeclBuilder) -> Expr,
    rmax: &dyn Fn(&Expr, &Expr) -> Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (f_id, f) = b.fresh_local(c.seq_ty());

    // motive P : Nat → Prop := fun N => ∀ k, Nat.le k N → NNRat.le (f k)(runMax f N).
    let motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (nn_id, nn) = m.fresh_local(c.nat.clone());
        let body = dom_at(&f, &nn, &m);
        m.finish_child(m.mk_lam(nn_id, BinderInfo::Default, c.nat.clone(), body))
    };

    // base : P 0 = ∀ k, Nat.le k 0 → NNRat.le (f k)(runMax f 0).
    //   runMax f 0 ≡ f 0.  casesOn k:
    //     k = 0    → NNRat.le (f 0)(f 0) = le_refl (f 0).
    //     k = s k' → Nat.le (s k') 0 is False (not_succ_le_zero); False.elim.
    let base = build_base_case(c, &b, &f, rmax);

    // step : ∀ N, P N → P (succ N).
    let step = build_step_case(c, &b, &f, rmax);

    let rec = Expr::apps(c.nat_rec_prop.clone(), [motive, base, step]);
    // @Nat.rec motive base step : ∀ N, P N.  Apply nothing more (it's ∀ N, P N).
    let e = b.mk_lam(f_id, BinderInfo::Default, c.seq_ty(), rec);
    b.finish(e)
}

/// `P 0`: `∀ k, Nat.le k 0 → NNRat.le (f k)(runMax f 0)`.
fn build_base_case(
    c: &BoundedConsts,
    parent: &EnvDeclBuilder,
    f: &Expr,
    rmax: &dyn Fn(&Expr, &Expr) -> Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (k_id, kk) = b.fresh_local(c.nat.clone());
    let hle_ty = c.nat_le(kk.clone(), c.nat_zero.clone());
    let (h_id, h) = b.fresh_local(hle_ty.clone());

    // runMax f 0 (definitional carrier in the goal).
    let rm0 = rmax(f, &c.nat_zero.clone());

    // casesOn motive over k: fun k => Nat.le k 0 → NNRat.le (f k)(runMax f 0).
    // We build `@Nat.casesOn.{1} (motive) k zero_case succ_case`, but the goal
    // already fixes k; we need the cases applied to `k` returning the proof
    // GIVEN h. Simpler: build a `Nat.casesOn` whose motive is
    //   fun k => Nat.le k 0 → NNRat.le (f k)(runMax f 0)
    // then apply it to k and then to h.
    let cases_motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = m.fresh_local(c.nat.clone());
        let hx = c.nat_le(x.clone(), c.nat_zero.clone());
        let (hx_id, _hx) = m.fresh_local(hx.clone());
        let concl = c.nle(c.at(f, &x), rm0.clone());
        let e = m.mk_pi(hx_id, BinderInfo::Default, hx, concl);
        let e = m.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), e);
        m.finish_child(e)
    };

    // zero_case : Nat.le 0 0 → NNRat.le (f 0)(runMax f 0).
    //   runMax f 0 ≡ f 0, so NNRat.le (f 0)(f 0) = le_refl (f 0).
    let zero_case = {
        let mut z = EnvDeclBuilder::child_of(&b);
        let h0 = c.nat_le(c.nat_zero.clone(), c.nat_zero.clone());
        let (h0_id, _h0) = z.fresh_local(h0.clone());
        let proof = c.nle_refl(c.at(f, &c.nat_zero.clone()));
        let e = z.mk_lam(h0_id, BinderInfo::Default, h0, proof);
        z.finish_child(e)
    };

    // succ_case : ∀ k', Nat.le (succ k') 0 → NNRat.le (f (succ k'))(runMax f 0).
    //   from h' : succ k' ≤ 0, not_succ_le_zero k' h' : False; False.elim.
    let succ_case = {
        let mut s = EnvDeclBuilder::child_of(&b);
        let (kp_id, kp) = s.fresh_local(c.nat.clone());
        let hsle = c.nat_le(c.succ(kp.clone()), c.nat_zero.clone());
        let (hsle_id, hsle_h) = s.fresh_local(hsle.clone());
        // not_succ_le_zero k' : ¬ (succ k' ≤ 0) = (succ k' ≤ 0 → False).
        let false_pf = Expr::app(
            Expr::app(c.nat_not_succ_le_zero.clone(), kp.clone()),
            hsle_h,
        );
        // goal type at this branch.
        let goal = c.nle(c.at(f, &c.succ(kp.clone())), rm0.clone());
        let proof = Expr::apps(c.false_elim.clone(), [goal, false_pf]);
        let e = s.mk_lam(hsle_id, BinderInfo::Default, hsle, proof);
        let e = s.mk_lam(kp_id, BinderInfo::Default, c.nat.clone(), e);
        s.finish_child(e)
    };

    // @Nat.casesOn.{1} cases_motive k zero_case succ_case : (Nat.le k 0 → …),
    // then apply h.
    let cases = Expr::apps(
        c.nat_cases_prop.clone(),
        [cases_motive, kk.clone(), zero_case, succ_case],
    );
    let applied = Expr::app(cases, h);
    let e = b.mk_lam(h_id, BinderInfo::Default, hle_ty, applied);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish_child(e)
}

/// `step : ∀ N, P N → P (succ N)`.
fn build_step_case(
    c: &BoundedConsts,
    parent: &EnvDeclBuilder,
    f: &Expr,
    rmax: &dyn Fn(&Expr, &Expr) -> Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (nn_id, nn) = b.fresh_local(c.nat.clone());
    // ih : P N = ∀ k, Nat.le k N → NNRat.le (f k)(runMax f N).
    let ih_ty = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (k_id, kk) = m.fresh_local(c.nat.clone());
        let hle = c.nat_le(kk.clone(), nn.clone());
        let (h_id, _h) = m.fresh_local(hle.clone());
        let concl = c.nle(c.at(f, &kk), rmax(f, &nn));
        let e = m.mk_pi(h_id, BinderInfo::Default, hle, concl);
        let e = m.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
        m.finish_child(e)
    };
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());

    let sn = c.succ(nn.clone());
    let rm_n = rmax(f, &nn);
    let rm_sn = rmax(f, &sn); // ≡ NNRat.max (runMax f N)(f (succ N))
    let f_sn = c.at(f, &sn);

    // Goal: ∀ k, Nat.le k (succ N) → NNRat.le (f k)(runMax f (succ N)).
    let (k_id, kk) = b.fresh_local(c.nat.clone());
    let hk_ty = c.nat_le(kk.clone(), sn.clone());
    let (hk_id, hk) = b.fresh_local(hk_ty.clone());

    // lt_or_eq_of_le k (succ N) hk : Or (Nat.lt k (succ N)) (Eq k (succ N)).
    let lt_k_sn = Expr::apps(c.nat_lt.clone(), [kk.clone(), sn.clone()]); // = Nat.le (succ k)(succ N)
    let eq_k_sn = Expr::apps(c.eq_c.clone(), [c.nat.clone(), kk.clone(), sn.clone()]);
    let disj = Expr::apps(
        c.nat_lt_or_eq_of_le.clone(),
        [kk.clone(), sn.clone(), hk.clone()],
    );

    let goal = c.nle(c.at(f, &kk), rm_sn.clone());

    // left : Nat.lt k (succ N) → goal.
    //   Nat.lt k (succ N) ≡ Nat.le (succ k)(succ N); le_of_succ_le_succ → k ≤ N.
    //   ih k (that) : NNRat.le (f k)(runMax f N).
    //   le_max_left (runMax f N)(f (succ N)) : NNRat.le (runMax f N) (max …) = runMax f (succ N).
    //   le_trans (f k)(runMax f N)(runMax f (succ N)).
    let left = {
        let mut l = EnvDeclBuilder::child_of(&b);
        let (hlt_id, hlt) = l.fresh_local(lt_k_sn.clone());
        // le_of_succ_le_succ k N hlt : Nat.le k N.  (hlt : succ k ≤ succ N)
        let k_le_n = Expr::apps(
            c.nat_le_of_succ_le_succ.clone(),
            [kk.clone(), nn.clone(), hlt],
        );
        let ih_k = Expr::apps(ih.clone(), [kk.clone(), k_le_n]); // NNRat.le (f k)(runMax f N)
        let le_ml = c.nle_max_left(rm_n.clone(), f_sn.clone()); // runMax f N ≤ max(runMax f N)(f(sN))
        let proof = c.nle_trans(c.at(f, &kk), rm_n.clone(), rm_sn.clone(), ih_k, le_ml);
        let e = l.mk_lam(hlt_id, BinderInfo::Default, lt_k_sn.clone(), proof);
        l.finish_child(e)
    };

    // right : Eq k (succ N) → goal.
    //   subst goal's `f k` using `Eq k (succ N)`: motive j := NNRat.le (f j)(runMax f (succ N)).
    //   At j = succ N: NNRat.le (f (succ N))(max (runMax f N)(f (succ N))) = le_max_right.
    let right = {
        let mut r = EnvDeclBuilder::child_of(&b);
        let (heq_id, heq) = r.fresh_local(eq_k_sn.clone());
        // proof_at_sn : NNRat.le (f (succ N))(runMax f (succ N)).
        let proof_at_sn = c.nle_max_right(rm_n.clone(), f_sn.clone());
        // motive j := NNRat.le (f j)(runMax f (succ N)).
        let motive = {
            let mut m = EnvDeclBuilder::child_of(&r);
            let (j_id, j) = m.fresh_local(c.nat.clone());
            let body = c.nle(c.at(f, &j), rm_sn.clone());
            m.finish_child(m.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), body))
        };
        // subst from (succ N) to k along Eq.symm heq (heq : k = succ N).
        // We want motive k from motive (succ N); subst needs h : Eq (succ N) k.
        let eq_sn_k = Expr::apps(c.eq_c.clone(), [c.nat.clone(), sn.clone(), kk.clone()]);
        let _ = eq_sn_k;
        let heq_symm = {
            let eq_symm = Expr::const_(
                Name::from_string("Eq.symm"),
                vec![Level::succ(Level::zero())],
            );
            Expr::apps(eq_symm, [c.nat.clone(), kk.clone(), sn.clone(), heq])
        };
        // @Eq.subst Nat motive (succ N) k (Eq.symm heq) proof_at_sn : motive k.
        let subst = Expr::const_(
            Name::from_string("Eq.subst"),
            vec![Level::succ(Level::zero())],
        );
        let proof = Expr::apps(
            subst,
            [
                c.nat.clone(),
                motive,
                sn.clone(),
                kk.clone(),
                heq_symm,
                proof_at_sn,
            ],
        );
        let e = r.mk_lam(heq_id, BinderInfo::Default, eq_k_sn.clone(), proof);
        r.finish_child(e)
    };

    // @Or.rec (Nat.lt k (succ N)) (Eq k (succ N)) motive left right disj, where
    // motive (_ : Or …) := goal (non-dependent).
    let or_motive = {
        let mut ob = EnvDeclBuilder::child_of(&b);
        let or_ty = Expr::apps(c.or_c.clone(), [lt_k_sn.clone(), eq_k_sn.clone()]);
        let (d_id, _d) = ob.fresh_local(or_ty.clone());
        ob.finish_child(ob.mk_lam(d_id, BinderInfo::Default, or_ty, goal.clone()))
    };
    let or_elim = Expr::apps(
        c.or_rec.clone(),
        [lt_k_sn, eq_k_sn, or_motive, left, right, disj],
    );

    let e = b.mk_lam(hk_id, BinderInfo::Default, hk_ty, or_elim);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, e);
    let e = b.mk_lam(nn_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish_child(e)
}

/// Build the proof of `NNReal.IsCauchy_bounded`.
fn build_is_cauchy_bounded_proof(c: &BoundedConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (f_id, f) = b.fresh_local(c.seq_ty());
    let hcau_ty = c.is_cauchy(f.clone());
    let (h_id, h) = b.fresh_local(hcau_ty.clone());

    let run_max = Expr::const_(Name::from_string("NNReal.runMax"), vec![]);
    let dominates = Expr::const_(Name::from_string("NNReal.runMax_dominates"), vec![]);
    let nat_le_refl = Expr::const_(Name::from_string("Nat.le_refl"), vec![]);

    let one_r = c.rat_one.clone();
    let nnone = c.nnrat_one.clone();

    // pred_N0 N0 := ∀ m n, N0≤m → N0≤n → bound_pair (val(f m))(val(f n)) Rat.one.
    let pred_n0 = |parent: &EnvDeclBuilder| -> Expr {
        let mut pb = EnvDeclBuilder::child_of(parent);
        let (cap_id, cap) = pb.fresh_local(c.nat.clone());
        let body = bound_pred_at(c, &pb, &f, &cap, &one_r);
        pb.finish_child(pb.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), body))
    };

    // ∃ B, ∀ n, NNRat.le (f n) B — the goal of the outer Exists.elim.
    let pred_b = |parent: &EnvDeclBuilder| -> Expr {
        let mut pb = EnvDeclBuilder::child_of(parent);
        let (bb_id, bb) = pb.fresh_local(c.nnrat.clone());
        let inner = {
            let mut ib = EnvDeclBuilder::child_of(&pb);
            let (n_id, n) = ib.fresh_local(c.nat.clone());
            let concl = c.nle(c.at(&f, &n), bb.clone());
            ib.finish_child(ib.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl))
        };
        pb.finish_child(pb.mk_lam(bb_id, BinderInfo::Default, c.nnrat.clone(), inner))
    };
    let exists_b = Expr::apps(c.exists_c.clone(), [c.nnrat.clone(), pred_b(&b)]);

    // hcau Rat.one Rat.zero_lt_one : ∃ N0, pred_N0 N0.
    let exists_n0 = Expr::apps(h.clone(), [one_r.clone(), c.rat_zero_lt_one.clone()]);

    // elim_fn : (N0 : Nat) → pred_N0 N0 → exists_b.
    let elim_fn = {
        let mut be = EnvDeclBuilder::child_of(&b);
        let (n0_id, n0) = be.fresh_local(c.nat.clone());
        let hn0_ty = bound_pred_at(c, &be, &f, &n0, &one_r);
        let (hn0_id, hn0) = be.fresh_local(hn0_ty.clone());

        // B := NNRat.max (runMax f N0) (NNRat.add (f N0) NNRat.one).
        let rm_n0 = Expr::apps(run_max.clone(), [f.clone(), n0.clone()]);
        let f_n0_plus_one = c.nnadd(c.at(&f, &n0), nnone.clone());
        let big_b = c.nmax(rm_n0.clone(), f_n0_plus_one.clone());

        // body : ∀ n, NNRat.le (f n) B.
        let body = {
            let mut bw = EnvDeclBuilder::child_of(&be);
            let (n_id, n) = bw.fresh_local(c.nat.clone());

            let goal = c.nle(c.at(&f, &n), big_b.clone());

            // le_total n N0 : Or (Nat.le n N0) (Nat.le N0 n).
            let le_n_n0 = c.nat_le(n.clone(), n0.clone());
            let le_n0_n = c.nat_le(n0.clone(), n.clone());
            let disj = Expr::apps(c.nat_le_total.clone(), [n.clone(), n0.clone()]);

            // left : n ≤ N0 → goal.
            let left = {
                let mut l = EnvDeclBuilder::child_of(&bw);
                let (hle_id, hle) = l.fresh_local(le_n_n0.clone());
                // dominates f N0 n hle : NNRat.le (f n)(runMax f N0).
                let dom = Expr::apps(dominates.clone(), [f.clone(), n0.clone(), n.clone(), hle]);
                // le_max_left (runMax f N0)(f N0 + one) : NNRat.le (runMax f N0) B.
                let lml = c.nle_max_left(rm_n0.clone(), f_n0_plus_one.clone());
                let proof = c.nle_trans(c.at(&f, &n), rm_n0.clone(), big_b.clone(), dom, lml);
                l.finish_child(l.mk_lam(hle_id, BinderInfo::Default, le_n_n0.clone(), proof))
            };

            // right : N0 ≤ n → goal.
            let right = {
                let mut r = EnvDeclBuilder::child_of(&bw);
                let (hle_id, hle) = r.fresh_local(le_n0_n.clone());
                // base := hN0 n N0 (hle : N0≤n) (Nat.le_refl N0 : N0≤N0)
                //   : bound_pair (val(f n))(val(f N0)) Rat.one.
                let n0_le_n0 = Expr::app(nat_le_refl.clone(), n0.clone());
                let base = Expr::apps(hn0.clone(), [n.clone(), n0.clone(), hle, n0_le_n0]);
                let vfn = c.val(c.at(&f, &n));
                let vfn0 = c.val(c.at(&f, &n0));
                // conjuncts of base: l := vfn < vfn0+1 ; rr := vfn0 < vfn+1.
                let lhs_conj = c.rlt(vfn.clone(), c.radd(vfn0.clone(), one_r.clone()));
                let rhs_conj = c.rlt(vfn0.clone(), c.radd(vfn.clone(), one_r.clone()));
                let a_lt = Expr::apps(
                    c.and_left.clone(),
                    [lhs_conj.clone(), rhs_conj.clone(), base],
                ); // vfn < vfn0+1
                   // hle1 : Rat.le vfn (vfn0+1).
                let hle1 = c.le_of_lt(vfn.clone(), c.radd(vfn0.clone(), one_r.clone()), a_lt);
                // transport RHS (vfn0+1) → val(NNRat.add (f N0) one):
                //   val_add (f N0) one : val(add (f N0) one) = vfn0 + val(one).
                //   val(one) ≡ Rat.one (def), so RHS is vfn0 + Rat.one defeq;
                //   Eq.symm gives (vfn0 + Rat.one) = val(add (f N0) one) under defeq.
                let v_add = c.val(c.nnadd(c.at(&f, &n0), nnone.clone()));
                let val_add_eq = c.val_add(c.at(&f, &n0), nnone.clone());
                // motive t := Rat.le vfn t.
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&r);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.rle(vfn.clone(), t);
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                // h_eq : Eq Rat (vfn0 + Rat.one) (val(add (f N0) one)).
                //   val_add_eq : val(add (f N0) one) = vfn0 + val(one); val(one)≡Rat.one
                //   so val_add_eq : val(add..) = vfn0 + Rat.one (defeq). Eq.symm:
                let h_eq = c.eq_symm(
                    v_add.clone(),
                    c.radd(vfn0.clone(), one_r.clone()),
                    val_add_eq,
                );
                // hle2 : Rat.le vfn (val(add (f N0) one)) = NNRat.le (f n)(add (f N0) one).
                let hle2 = c.subst(
                    motive,
                    c.radd(vfn0.clone(), one_r.clone()),
                    v_add,
                    h_eq,
                    hle1,
                );
                // le_max_right (runMax f N0)(f N0 + one) : NNRat.le (f N0 + one) B.
                let lmr = c.nle_max_right(rm_n0.clone(), f_n0_plus_one.clone());
                let proof = c.nle_trans(
                    c.at(&f, &n),
                    f_n0_plus_one.clone(),
                    big_b.clone(),
                    hle2,
                    lmr,
                );
                r.finish_child(r.mk_lam(hle_id, BinderInfo::Default, le_n0_n.clone(), proof))
            };

            // Or.rec (n≤N0)(N0≤n) motive left right disj : goal.
            let or_motive = {
                let mut ob = EnvDeclBuilder::child_of(&bw);
                let or_ty = Expr::apps(c.or_c.clone(), [le_n_n0.clone(), le_n0_n.clone()]);
                let (d_id, _d) = ob.fresh_local(or_ty.clone());
                ob.finish_child(ob.mk_lam(d_id, BinderInfo::Default, or_ty, goal.clone()))
            };
            let cases = Expr::apps(
                c.or_rec.clone(),
                [le_n_n0, le_n0_n, or_motive, left, right, disj],
            );
            bw.finish_child(bw.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), cases))
        };

        // Exists.intro NNRat pred_b B body : ∃ B, ∀ n, …
        let intro = Expr::apps(
            c.exists_intro.clone(),
            [c.nnrat.clone(), pred_b(&be), big_b, body],
        );
        let e = be.mk_lam(hn0_id, BinderInfo::Default, hn0_ty, intro);
        let e = be.mk_lam(n0_id, BinderInfo::Default, c.nat.clone(), e);
        be.finish_child(e)
    };

    // @Exists.elim Nat pred_N0 exists_b exists_n0 elim_fn.
    let exists_elim = Expr::const_(
        Name::from_string("Exists.elim"),
        vec![Level::succ(Level::zero())],
    );
    let elim = Expr::apps(
        exists_elim,
        [c.nat.clone(), pred_n0(&b), exists_b, exists_n0, elim_fn],
    );

    let e = b.mk_lam(h_id, BinderInfo::Default, hcau_ty, elim);
    let e = b.mk_lam(f_id, BinderInfo::Default, c.seq_ty(), e);
    b.finish(e)
}

/// `bound_pred_at f cap eps := ∀ m n, Nat.le cap m → Nat.le cap n →
///    And (Rat.lt (val(f m)) (val(f n) + eps)) (Rat.lt (val(f n)) (val(f m) + eps))`
/// — the inner `∀`-body of `IsCauchy f` instantiated at the witness `cap`.
fn bound_pred_at(
    c: &BoundedConsts,
    parent: &EnvDeclBuilder,
    f: &Expr,
    cap: &Expr,
    eps: &Expr,
) -> Expr {
    let mut bn = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = bn.fresh_local(c.nat.clone());
    let (n_id, n) = bn.fresh_local(c.nat.clone());
    let hle_m = c.nat_le(cap.clone(), m.clone());
    let (hlem_id, _h) = bn.fresh_local(hle_m.clone());
    let hle_n = c.nat_le(cap.clone(), n.clone());
    let (hlen_id, _h2) = bn.fresh_local(hle_n.clone());
    let vm = c.val(c.at(f, &m));
    let vn = c.val(c.at(f, &n));
    let left = c.rlt(vm.clone(), c.radd(vn.clone(), eps.clone()));
    let right = c.rlt(vn, c.radd(vm, eps.clone()));
    let concl = Expr::apps(c.and_c.clone(), [left, right]);
    let e = bn.mk_pi(hlen_id, BinderInfo::Default, hle_n, concl);
    let e = bn.mk_pi(hlem_id, BinderInfo::Default, hle_m, e);
    let e = bn.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = bn.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    bn.finish_child(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const DEFS: &[&str] = &["NNReal.runMax"];
    const THEOREMS: &[&str] = &["NNReal.runMax_dominates", "NNReal.IsCauchy_bounded"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_bounded()
            .expect("init_algebra_nnreal_bounded");
        env.init_algebra_nnreal_bounded().expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_bounded_present_and_kernel_check() {
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
    fn test_nnreal_bounded_theorems_constructive_empty_closure() {
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
