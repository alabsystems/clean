// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proofs of the `Fin.prod` collapse lemmas on the road to the
//! Parseval product→indicator identity
//! `Fin.prod n (fun i => 1 + pm(x i)·pm(y i)) = if x=y then 2^n else 0`.
//!
//! - `Fin.prod_eq_zero_of_factor_zero :`
//!   `∀ (n : Nat) (f : Fin n → Rat) (j : Fin n),`
//!   `  f j = Rat.zero → Fin.prod n f = Rat.zero`
//!   — a single zero factor annihilates the whole `Fin.prod`. Proved by
//!   `Nat.rec` on `n`; the successor step peels the top factor with
//!   `Fin.prod_succ` and case-splits the witness index `j` with `Fin.lastCases`:
//!   if `j = Fin.last n` the top factor is `0` so `Rat.mul_zero` kills the
//!   product; if `j = Fin.castSucc n j'` the prefix product is `0` by the IH so
//!   `Rat.zero_mul` kills it. The base `n = 0` is vacuous (`Fin 0` is
//!   uninhabited: its `Fin.mk` minor carries `Nat.lt val 0`, discharged by
//!   `Nat.not_succ_le_zero` + `False.elim`).
//!
//! Kernel-checked, `ProofQuality::Constructive` (closure ⊆ {`Fin.prod_succ`,
//! `Fin.lastCases`, `Rat.mul_zero`, `Rat.zero_mul`, `Nat.not_succ_le_zero`} ∪
//! `Eq`/`Nat.rec`/`Fin.rec`/`False.elim`/`congrArg` built-ins — all admitted-
//! axiom-free).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants for the `Fin.prod` collapse lemmas.
struct ProdCollapseConsts {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    rat_zero: Expr,
    rat_mul: Expr,
    fin_prod: Expr,
    nat_succ: Expr,
    nat_rec: Expr,
    fin_rec1: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    fin_prod_succ: Expr,
    fin_last_cases1: Expr,
    rat_mul_zero: Expr,
    rat_zero_mul: Expr,
    not_succ_le_zero: Expr,
    false_elim1: Expr,
    eq1: Expr,
    eq_trans1: Expr,
    congr_arg: Expr,
}

impl ProdCollapseConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            fin_prod: Expr::const_(Name::from_string("Fin.prod"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            // Motive of the outer induction is a `∀ … Prop` (Sort 0), so the
            // Nat.rec elimination is at universe 0.
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            // base-case `Fin.rec` produces a `Prop` (the vacuous goal), universe 0.
            fin_rec1: Expr::const_(Name::from_string("Fin.rec"), vec![Level::zero()]),
            fin_cast_succ: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            fin_prod_succ: Expr::const_(Name::from_string("Fin.prod_succ"), vec![]),
            // `Fin.lastCases` over a `Prop`-valued motive, universe 0.
            fin_last_cases1: Expr::const_(Name::from_string("Fin.lastCases"), vec![Level::zero()]),
            rat_mul_zero: Expr::const_(Name::from_string("Rat.mul_zero"), vec![]),
            rat_zero_mul: Expr::const_(Name::from_string("Rat.zero_mul"), vec![]),
            not_succ_le_zero: Expr::const_(Name::from_string("Nat.not_succ_le_zero"), vec![]),
            false_elim1: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn fin_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat.clone())
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn prod(&self, n: Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_prod.clone(), [n, g])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    /// `@congrArg Rat Rat from to g h : g from = g to`.
    fn congr_arg_rat(&self, from: Expr, to: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), from, to, g, h],
        )
    }
    fn cast_succ(&self, n: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.fin_cast_succ.clone(), [n.clone(), i.clone()])
    }
    fn last(&self, n: &Expr) -> Expr {
        Expr::app(self.fin_last.clone(), n.clone())
    }
    /// `fun i : Fin k => f (Fin.castSucc k i)` — the prefix restriction.
    fn prefix_fn(&self, parent: &EnvDeclBuilder, k: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_k = self.fin_of(k);
        let (i_id, i) = b.fresh_local(fin_k.clone());
        let body = Expr::app(f.clone(), self.cast_succ(k, &i));
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_k, body))
    }

    /// The proposition body `Fin.prod m f = Rat.zero` for fixed `f`.
    fn goal(&self, m: Expr, f: Expr) -> Expr {
        self.eq_rat(self.prod(m, f), self.rat_zero.clone())
    }

    /// `motive k := ∀ (f : Fin k → Rat) (j : Fin k), f j = 0 → Fin.prod k f = 0`.
    fn motive_body(&self, parent: &EnvDeclBuilder, k: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let ft = self.fin_to_rat(k);
        let (f_id, f) = b.fresh_local(ft.clone());
        let (j_id, j) = b.fresh_local(self.fin_of(k));
        let hyp = self.eq_rat(Expr::app(f.clone(), j), self.rat_zero.clone());
        let (h_id, _h) = b.fresh_local(hyp.clone());
        let concl = self.goal(k.clone(), f.clone());
        let r = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
        let r = b.mk_pi(j_id, BinderInfo::Default, self.fin_of(k), r);
        let r = b.mk_pi(f_id, BinderInfo::Default, ft, r);
        b.finish_child(r)
    }
}

// ── Fin.prod_eq_zero_of_factor_zero ──

fn prod_zero_type(c: &ProdCollapseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let body = c.motive_body(&b, &n);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), body);
    b.finish(ty)
}

fn prod_zero_motive(c: &ProdCollapseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let body = c.motive_body(&b, &k);
    b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
}

/// Base `motive 0`: `∀ (f : Fin 0 → Rat) (j : Fin 0), f j = 0 → Fin.prod 0 f = 0`.
/// Vacuous: `j : Fin 0` is uninhabited. Dispatch on `j` with `Fin.rec`; the only
/// `Fin.mk` minor carries `isLt : Nat.lt val 0 ≡ Nat.le (succ val) 0`, refuted by
/// `Nat.not_succ_le_zero val isLt : False`, then `False.elim` to the goal.
fn prod_zero_base(c: &ProdCollapseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let ft = c.fin_to_rat(&nat_zero);
    let (f_id, f) = b.fresh_local(ft.clone());
    let (j_id, j) = b.fresh_local(c.fin_of(&nat_zero));
    let hyp = c.eq_rat(Expr::app(f.clone(), j.clone()), c.rat_zero.clone());
    let (h_id, _h) = b.fresh_local(hyp.clone());
    // After binding f, j, h the residual goal is `Fin.prod 0 f = 0` (a Prop). We
    // refute the (uninhabited) index `j : Fin 0` via `Fin.rec` with the constant
    // motive `fun _ => goal`; the only `Fin.mk` minor carries `isLt : Nat.lt val 0`
    // ≡ `Nat.le (succ val) 0`, refuted by `Nat.not_succ_le_zero`.
    let goal = c.goal(nat_zero.clone(), f.clone());

    // Fin.rec motive: fun (_ : Fin 0) => goal
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (w_id, _w) = d.fresh_local(c.fin_of(&nat_zero));
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.fin_of(&nat_zero), goal.clone()))
    };
    // mk minor: fun (val : Nat) (isLt : Nat.lt val 0) => False.elim goal (not_succ_le_zero val isLt)
    let mk_case = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (val_id, val) = d.fresh_local(c.nat.clone());
        let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let islt_ty = Expr::apps(nat_lt, [val.clone(), nat_zero.clone()]);
        let (islt_id, islt) = d.fresh_local(islt_ty.clone());
        let contra = Expr::apps(c.not_succ_le_zero.clone(), [val.clone(), islt]);
        let body = Expr::apps(c.false_elim1.clone(), [goal.clone(), contra]);
        let r = d.mk_lam(islt_id, BinderInfo::Default, islt_ty, body);
        let r = d.mk_lam(val_id, BinderInfo::Default, c.nat.clone(), r);
        d.finish_child(r)
    };
    // @Fin.rec.{0} 0 motive mk_case j : goal
    let rec = Expr::apps(
        c.fin_rec1.clone(),
        [nat_zero.clone(), motive, mk_case, j.clone()],
    );
    let val = b.mk_lam(h_id, BinderInfo::Default, hyp, rec);
    let val = b.mk_lam(j_id, BinderInfo::Default, c.fin_of(&nat_zero), val);
    let val = b.mk_lam(f_id, BinderInfo::Default, ft, val);
    b.finish(val)
}

impl Environment {
    /// Register `Fin.prod_eq_zero_of_factor_zero` as a kernel-checked,
    /// constructive theorem. Idempotent.
    pub(crate) fn register_fin_prod_eq_zero_of_factor_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.prod_eq_zero_of_factor_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?;
        self.init_rat()?;
        self.register_fin_prod_succ_theorem()?;
        self.register_fin_last_cases()?;

        let c = ProdCollapseConsts::new();
        let ty = prod_zero_type(&c);
        let value = prod_zero_value(&c);
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Step `motive k → motive (k+1)`.
///
/// Goal: `∀ (f : Fin (k+1) → Rat) (j : Fin (k+1)), f j = 0 → Fin.prod (k+1) f = 0`.
///
/// `Fin.prod_succ k f : Fin.prod (k+1) f = Rat.mul (Fin.prod k (f∘castSucc))
/// (f (last k))`. Case-split `j` with `Fin.lastCases`:
///   - `j = last k`: hyp `f (last k) = 0`; `Rat.mul P 0 = 0` via `Rat.mul_zero P`;
///     chain with `congrArg (mul P) hyp` after rewriting the RHS factor.
///   - `j = castSucc k j'`: hyp `f (castSucc k j') = 0`, i.e. `(f∘castSucc) j' = 0`
///     so IH gives `Fin.prod k (f∘castSucc) = 0`; `Rat.zero_mul L = 0` then
///     `congrArg (·L) ih`.
fn prod_zero_step(c: &ProdCollapseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    // ih : motive k
    let ih_ty = c.motive_body(&b, &k);
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());

    let sk = c.succ(&k);
    let ft = c.fin_to_rat(&sk);
    let (f_id, f) = b.fresh_local(ft.clone());

    // pre := f ∘ castSucc k : Fin k → Rat ; P := Fin.prod k pre ; T := f (last k)
    let pre = c.prefix_fn(&b, &k, &f);
    let prod_pre = c.prod(k.clone(), pre.clone());
    let f_last = Expr::app(f.clone(), c.last(&k));
    // peel : Fin.prod (k+1) f = Rat.mul P T
    let peel = Expr::apps(c.fin_prod_succ.clone(), [k.clone(), f.clone()]);
    let mul_pt = c.mul(prod_pre.clone(), f_last.clone());

    // --- lastCases motive: fun (j : Fin (k+1)) => f j = 0 → Fin.prod (k+1) f = 0 ---
    let lc_motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = d.fresh_local(c.fin_of(&sk));
        let hyp = c.eq_rat(Expr::app(f.clone(), j.clone()), c.rat_zero.clone());
        let concl = c.goal(sk.clone(), f.clone());
        let body = Expr::pi(BinderInfo::Default, hyp, concl);
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, c.fin_of(&sk), body))
    };

    // --- last case: j = last k. motive (last k) = (f (last k) = 0) → goal ---
    let last_case = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hyp_ty = c.eq_rat(f_last.clone(), c.rat_zero.clone());
        let (hl_id, hl) = d.fresh_local(hyp_ty.clone());
        // step1 : Fin.prod (k+1) f = Rat.mul P T   (peel)
        // step2 : Rat.mul P T = Rat.mul P 0         (congrArg (mul P) hl)
        let mul_p = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (x_id, x) = e.fresh_local(c.rat.clone());
            let body = c.mul(prod_pre.clone(), x);
            e.finish_child(e.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let step2 = c.congr_arg_rat(f_last.clone(), c.rat_zero.clone(), mul_p, hl);
        let mul_p_zero = c.mul(prod_pre.clone(), c.rat_zero.clone());
        // step3 : Rat.mul P 0 = 0   (Rat.mul_zero P)
        let step3 = Expr::app(c.rat_mul_zero.clone(), prod_pre.clone());
        // chain: prod = mul_pt = mul_p_zero = 0
        let t23 = c.trans_rat(
            mul_pt.clone(),
            mul_p_zero.clone(),
            c.rat_zero.clone(),
            step2,
            step3,
        );
        let proof = c.trans_rat(
            c.prod(sk.clone(), f.clone()),
            mul_pt.clone(),
            c.rat_zero.clone(),
            peel.clone(),
            t23,
        );
        d.finish_child(d.mk_lam(hl_id, BinderInfo::Default, hyp_ty, proof))
    };

    // --- cast case: j = castSucc k j'. motive (castSucc k j') = (f (castSucc k j') = 0) → goal ---
    let cast_case = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (jp_id, jp) = d.fresh_local(c.fin_of(&k));
        // hyp : f (castSucc k j') = 0 ; note pre j' ≡ f (castSucc k j') definitionally.
        let f_cs = Expr::app(f.clone(), c.cast_succ(&k, &jp));
        let hyp_ty = c.eq_rat(f_cs.clone(), c.rat_zero.clone());
        let (hc_id, hc) = d.fresh_local(hyp_ty.clone());
        // ih applied: ih pre j' hc' : Fin.prod k pre = 0.
        // pre j' ≡ f (castSucc k j') so hc : pre j' = 0 too (def-eq), reuse hc.
        let ih_app = Expr::apps(c.fin_prod_succ_ih(&d, &ih, &pre, &jp, hc.clone()), []);
        // step1 : prod = mul_pt (peel)
        // step2 : mul_pt = mul 0 T  via congrArg (·T) ih_app
        let mul_t = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (x_id, x) = e.fresh_local(c.rat.clone());
            let body = c.mul(x, f_last.clone());
            e.finish_child(e.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let step2 = c.congr_arg_rat(prod_pre.clone(), c.rat_zero.clone(), mul_t, ih_app);
        let mul_zero_t = c.mul(c.rat_zero.clone(), f_last.clone());
        // step3 : mul 0 T = 0  (Rat.zero_mul T)
        let step3 = Expr::app(c.rat_zero_mul.clone(), f_last.clone());
        let t23 = c.trans_rat(
            mul_pt.clone(),
            mul_zero_t.clone(),
            c.rat_zero.clone(),
            step2,
            step3,
        );
        let proof = c.trans_rat(
            c.prod(sk.clone(), f.clone()),
            mul_pt.clone(),
            c.rat_zero.clone(),
            peel.clone(),
            t23,
        );
        let _ = hc;
        let r = d.mk_lam(hc_id, BinderInfo::Default, hyp_ty, proof);
        let r = d.mk_lam(jp_id, BinderInfo::Default, c.fin_of(&k), r);
        d.finish_child(r)
    };

    // @Fin.lastCases.{0} k lc_motive last_case cast_case : (j : Fin (k+1)) → lc_motive j
    let lc = Expr::apps(
        c.fin_last_cases1.clone(),
        [k.clone(), lc_motive, last_case, cast_case],
    );

    // Now build `fun (f) (j) (h) => lc j h`.
    let (j_id, j) = b.fresh_local(c.fin_of(&sk));
    let hyp = c.eq_rat(Expr::app(f.clone(), j.clone()), c.rat_zero.clone());
    let (h_id, h) = b.fresh_local(hyp.clone());
    let applied = Expr::apps(lc, [j.clone(), h]);
    let val = b.mk_lam(h_id, BinderInfo::Default, hyp, applied);
    let val = b.mk_lam(j_id, BinderInfo::Default, c.fin_of(&sk), val);
    let val = b.mk_lam(f_id, BinderInfo::Default, ft, val);
    let val = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, val);
    let val = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

fn prod_zero_value(c: &ProdCollapseConsts) -> Expr {
    let motive = prod_zero_motive(c);
    let base = prod_zero_base(c);
    let step = prod_zero_step(c);
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let body = Expr::apps(c.nat_rec.clone(), [motive, base, step, n]);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
}

impl ProdCollapseConsts {
    /// `ih pre j' hc : Fin.prod k pre = 0`, where `pre = f∘castSucc` and
    /// `hc : f (castSucc k j') = 0` (def-eq to `pre j' = 0`).
    fn fin_prod_succ_ih(
        &self,
        _parent: &EnvDeclBuilder,
        ih: &Expr,
        pre: &Expr,
        jp: &Expr,
        hc: Expr,
    ) -> Expr {
        Expr::apps(ih.clone(), [pre.clone(), jp.clone(), hc])
    }
}

// ===========================================================================
// Fin.prod_diag_eq_two — the DIAGONAL collapse of the Parseval product integrand.
//
//   ∀ (n : Nat) (x : HCPoint n),
//     Fin.prod n (fun i => Rat.one + pm(x i)·pm(x i))
//       = Fin.prod n (fun _ => Rat.one + Rat.one)
//
// On the diagonal (`x = y`) the delta's product integrand `1 + pm(x i)·pm(y i)`
// becomes `1 + pm(x i)·pm(x i)`, and each coordinate factor is `1 + 1` because
// `pm(x i)·pm(x i) = 1` (`pm_mul_self`). The identification of the constant
// factor `1 + 1` with the closed numeral `2` and the const-product collapse
// `Fin.prod n (const (1+1)) = 2^n` are downstream numeral steps; this lemma
// isolates the `Fin.prod_congr` rung that does not touch Rat-numeral algebra.
//
// Proof: `Fin.prod_congr n diag_int (const (1+1)) h`, where
//   `h : ∀ i, 1 + pm(x i)·pm(x i) = 1 + 1`
//   `h i = @congrArg Rat Rat (pm(x i)·pm(x i)) 1 (Rat.add 1) (pm_mul_self (x i))`.
// Kernel-checked, constructive (closure ⊆ {Fin.prod_congr, pm_mul_self} ∪ Eq/
// congrArg built-ins).
// ===========================================================================

impl ProdCollapseConsts {
    fn rat_add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.add"), vec![]), [a, b])
    }
    fn rat_one(&self) -> Expr {
        Expr::const_(Name::from_string("Rat.one"), vec![])
    }
    fn pm(&self, b: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]),
            b,
        )
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            n.clone(),
        )
    }
    /// `fun (i : Fin n) => Rat.one + pm(x i)·pm(x i)` — the diagonal integrand.
    fn diag_int(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let pmxi = self.pm(Expr::app(x.clone(), i.clone()));
        let body = self.rat_add(self.rat_one(), self.mul(pmxi.clone(), pmxi));
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `fun (_ : Fin n) => Rat.one + Rat.one`.
    fn const_two_sum(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, _i) = b.fresh_local(fin_n.clone());
        let body = self.rat_add(self.rat_one(), self.rat_one());
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
}

fn prod_diag_type(c: &ProdCollapseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let lhs = c.prod(n.clone(), c.diag_int(&b, &n, &x));
    let rhs = c.prod(n.clone(), c.const_two_sum(&b, &n));
    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(x_id, BinderInfo::Default, hcp, concl);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    b.finish(ty)
}

fn prod_diag_value(c: &ProdCollapseConsts) -> Expr {
    let fin_prod_congr = Expr::const_(Name::from_string("Fin.prod_congr"), vec![]);
    let pm_mul_self = Expr::const_(Name::from_string("BoolAnalysis.pm_mul_self"), vec![]);
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());

    let diag = c.diag_int(&b, &n, &x);
    let const2 = c.const_two_sum(&b, &n);

    // h : ∀ i : Fin n, (1 + pm(x i)·pm(x i)) = (1 + 1)
    //   = fun i => @congrArg Rat Rat (pm(x i)·pm(x i)) 1 (Rat.add 1) (pm_mul_self (x i))
    let h = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let pmxi = c.pm(Expr::app(x.clone(), i.clone()));
        let sq = c.mul(pmxi.clone(), pmxi.clone());
        // motive g := Rat.add Rat.one  (so g sq = 1 + sq, g 1 = 1 + 1)
        let add_one = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (t_id, t) = e.fresh_local(c.rat.clone());
            let body = c.rat_add(c.rat_one(), t);
            e.finish_child(e.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let pms = Expr::app(pm_mul_self.clone(), Expr::app(x.clone(), i.clone()));
        let body = c.congr_arg_rat(sq, c.rat_one(), add_one, pms);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };

    let proof = Expr::apps(fin_prod_congr, [n.clone(), diag, const2, h]);
    let val = b.mk_lam(x_id, BinderInfo::Default, hcp, proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Fin.prod_diag_eq_two` (the diagonal Parseval product collapse)
    /// as a kernel-checked, constructive theorem. Idempotent.
    pub(crate) fn register_fin_prod_diag_eq_two(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.prod_diag_eq_two");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?;
        self.init_rat()?;
        // `Fin.prod_congr` and `pm_mul_self` are registered inside
        // `init_boolean_analysis`; depend on them (registered before this in the
        // init chain).
        self.register_fin_prod_one_theorems()?;
        self.register_pm_mul_self_theorem()?;

        let c = ProdCollapseConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: prod_diag_type(&c),
            value: prod_diag_value(&c),
        })
    }
}

// ===========================================================================
// BoolAnalysis.factor_vanish_of_xor — the OFF-DIAGONAL coordinate factor.
//
//   ∀ (a b : Bool), Bool.xor a b = true →
//     Rat.add Rat.one (Rat.mul (pm a) (pm b)) = Rat.zero
//
// When two cube points differ at a coordinate (`a ≠ b`, expressed as the
// differ-witness `Bool.xor a b = true`), the Parseval product factor
// `1 + pm(a)·pm(b)` is `1 + (+1)(−1) = 0`. Proof: a 2×2 `Bool.rec` on `a`
// then `b`, carrying the differ-hypothesis into the motive:
//   - the two OFF-diagonal leaves (`a≠b`) make the factor a CLOSED `Rat`
//     computing to `Rat.zero`, closed by `@Eq.refl Rat (1 + pm(a)·pm(b))`;
//   - the two DIAGONAL leaves (`a=b`) have `Bool.xor a a ≡ false`, so the
//     hypothesis is `false = true`, refuted by `@Bool.noConfusion goal …`.
// Kernel-checked, constructive (closure ⊆ {pm} ∪ Eq/Bool.rec/Bool.noConfusion
// built-ins; the off-diagonal leaves rely only on the kernel's faithful Rat
// reduction of the closed numerator).
// ===========================================================================

impl ProdCollapseConsts {
    fn eq_refl_rat(&self, x: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [self.rat.clone(), x],
        )
    }
    /// The factor `Rat.add Rat.one (Rat.mul (pm a) (pm b))`.
    fn factor(&self, a: Expr, b: Expr) -> Expr {
        self.rat_add(self.rat_one(), self.mul(self.pm(a), self.pm(b)))
    }
}

fn factor_vanish_type(c: &ProdCollapseConsts) -> Expr {
    let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
    let bool_xor = Expr::const_(Name::from_string("Bool.xor"), vec![]);
    let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let eqb = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(bool_c.clone());
    let (bv_id, bv) = b.fresh_local(bool_c.clone());
    let xor_ab = Expr::apps(bool_xor.clone(), [a.clone(), bv.clone()]);
    let hyp = Expr::apps(eqb.clone(), [bool_c.clone(), xor_ab, btrue.clone()]);
    let concl = c.eq_rat(c.factor(a.clone(), bv.clone()), c.rat_zero.clone());
    let (h_id, _h) = b.fresh_local(hyp.clone());
    let r = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let r = b.mk_pi(bv_id, BinderInfo::Default, bool_c.clone(), r);
    let r = b.mk_pi(a_id, BinderInfo::Default, bool_c.clone(), r);
    b.finish(r)
}

fn factor_vanish_value(c: &ProdCollapseConsts) -> Expr {
    let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
    let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
    let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let bool_xor = Expr::const_(Name::from_string("Bool.xor"), vec![]);
    let eqb = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    // Bool.rec into Prop (the implication is a Prop): universe 0.
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
    let no_conf = Expr::const_(Name::from_string("Bool.noConfusion"), vec![Level::zero()]);

    let hyp_ty = |a: Expr, bb: Expr| {
        let xor_ab = Expr::apps(bool_xor.clone(), [a, bb]);
        Expr::apps(eqb.clone(), [bool_c.clone(), xor_ab, btrue.clone()])
    };
    let goal = |a: Expr, bb: Expr| c.eq_rat(c.factor(a, bb), c.rat_zero.clone());
    // implication body `(Bool.xor a b = true) → goal a b`
    let imp = |a: Expr, bb: Expr| {
        Expr::pi(
            BinderInfo::Default,
            hyp_ty(a.clone(), bb.clone()),
            goal(a, bb),
        )
    };

    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(bool_c.clone());
    let (bv_id, bv) = b.fresh_local(bool_c.clone());

    // motive_a : fun a' => (Bool.xor a' b = true) → goal a' b
    let motive_a = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (ap_id, ap) = d.fresh_local(bool_c.clone());
        d.finish_child(d.mk_lam(
            ap_id,
            BinderInfo::Default,
            bool_c.clone(),
            imp(ap, bv.clone()),
        ))
    };

    // Build the inner b-split for a fixed `lhs` (a constructor).
    let inner = |lhs: Expr, parent: &EnvDeclBuilder| -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        // motive_b : fun b' => (Bool.xor lhs b' = true) → goal lhs b'
        let motive_b = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (bp_id, bp) = e.fresh_local(bool_c.clone());
            e.finish_child(e.mk_lam(
                bp_id,
                BinderInfo::Default,
                bool_c.clone(),
                imp(lhs.clone(), bp),
            ))
        };
        // leaf builder: either refl (off-diagonal) or noConfusion (diagonal).
        let leaf = |rhs: Expr, parent2: &EnvDeclBuilder| -> Expr {
            let mut e = EnvDeclBuilder::child_of(parent2);
            let ht = hyp_ty(lhs.clone(), rhs.clone());
            let (h_id, h) = e.fresh_local(ht.clone());
            let body = if lhs == rhs {
                // diagonal: Bool.xor lhs lhs ≡ false, so h : false = true. Refute.
                Expr::apps(
                    no_conf.clone(),
                    [
                        goal(lhs.clone(), rhs.clone()),
                        bfalse.clone(),
                        btrue.clone(),
                        h,
                    ],
                )
            } else {
                // off-diagonal: factor is a closed Rat = 0; @Eq.refl Rat factor.
                let _ = h;
                c.eq_refl_rat(c.factor(lhs.clone(), rhs.clone()))
            };
            e.finish_child(e.mk_lam(h_id, BinderInfo::Default, ht, body))
        };
        let b_false = leaf(bfalse.clone(), &d);
        let b_true = leaf(btrue.clone(), &d);
        d.finish_child(Expr::apps(
            bool_rec.clone(),
            [motive_b, b_false, b_true, bv.clone()],
        ))
    };

    let a_false = inner(bfalse.clone(), &b);
    let a_true = inner(btrue.clone(), &b);
    let rec_a = Expr::apps(bool_rec.clone(), [motive_a, a_false, a_true, a.clone()]);
    let val = b.mk_lam(bv_id, BinderInfo::Default, bool_c.clone(), rec_a);
    let val = b.mk_lam(a_id, BinderInfo::Default, bool_c.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.factor_vanish_of_xor` as a kernel-checked,
    /// constructive theorem. Idempotent.
    pub(crate) fn register_factor_vanish_of_xor(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.factor_vanish_of_xor");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?;
        self.init_rat()?;
        // `pm` is registered by `register_boolfn_embeddings` inside
        // `init_boolean_analysis`; depend on it.
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = ProdCollapseConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: factor_vanish_type(&c),
            value: factor_vanish_value(&c),
        })
    }
}

// ===========================================================================
// BoolAnalysis.prod_const_two_eq_pow — the diagonal numeral collapse.
//
//   ∀ (n : Nat),
//     Fin.prod n (fun _ => Rat.add Rat.one Rat.one)
//       = Rat.mk (Int.ofNat (Nat.pow 2 n)) 1
//
// The constant `2`-product over `n` coordinates is the cube size `2^n` (as the
// Rat numeral `2^n / 1`). This identifies the `prod_diag_eq_two` right-hand
// side `Fin.prod n (const (1+1))` with the closed cube-size numeral `D`, the
// last rung of the diagonal Parseval collapse. Proved by `Nat.rec` on `n`:
//   - base `n = 0`: `Fin.prod 0 _ ≡ 1 ≡ Rat.mk (ofNat (2^0)) 1` (ground def-eq),
//     `@Eq.refl Rat (Rat.mk (ofNat (2^0)) 1)`;
//   - step: `Fin.prod (k+1) (const c) ≡ (Fin.prod k (const c))·c` (`Fin.prod_succ`,
//     and `const c ∘ castSucc ≡ const c`), `congrArg (·c) IH` rewrites the prefix
//     to `(2^k/1)`, and `(2^k/1)·(1+1) ≡ Rat.mk (ofNat (2^(k+1))) 1` by the
//     kernel's faithful Rat-numeral reduction (`(1+1) ≡ 2/1`, `Int.mul (ofNat a)
//     (ofNat b) ≡ ofNat (a·b)`, `Nat.mul 1 1 ≡ 1`, `pow 2 (k+1) ≡ (pow 2 k)·2`).
// Kernel-checked, constructive (closure ⊆ {Fin.prod_succ} ∪ Eq/Nat.rec/congrArg).
// ===========================================================================

impl ProdCollapseConsts {
    fn rat_two(&self) -> Expr {
        self.rat_add(self.rat_one(), self.rat_one())
    }
    /// `Rat.mk (Int.ofNat (Nat.pow 2 n)) 1` — the cube-size numeral `D(n)`.
    fn cube_size(&self, n: &Expr) -> Expr {
        let nat_succ = self.nat_succ.clone();
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let one = Expr::app(nat_succ.clone(), nat_zero);
        let two = Expr::app(nat_succ, one.clone());
        let pow = Expr::apps(
            Expr::const_(Name::from_string("Nat.pow"), vec![]),
            [two, n.clone()],
        );
        let ofnat = Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), pow);
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [ofnat, one],
        )
    }
    /// `fun (_ : Fin m) => Rat.one + Rat.one` — the constant-`2` factor function.
    fn const_two_fn(&self, parent: &EnvDeclBuilder, m: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_m = self.fin_of(m);
        let (i_id, _i) = b.fresh_local(fin_m.clone());
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_m, self.rat_two()))
    }
}

fn prod_const_two_type(c: &ProdCollapseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let lhs = c.prod(n.clone(), c.const_two_fn(&b, &n));
    let concl = c.eq_rat(lhs, c.cube_size(&n));
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl))
}

fn prod_const_two_motive(c: &ProdCollapseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let lhs = c.prod(k.clone(), c.const_two_fn(&b, &k));
    let concl = c.eq_rat(lhs, c.cube_size(&k));
    b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), concl))
}

/// Base `motive 0`: `Fin.prod 0 (const 2) = Rat.mk (ofNat (2^0)) 1`. Both sides
/// ground-reduce to `1/1`, so `@Eq.refl Rat (Rat.mk (ofNat (2^0)) 1)` closes it
/// (the LHS is def-eq to the stated RHS).
fn prod_const_two_base(c: &ProdCollapseConsts) -> Expr {
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    c.eq_refl_rat(c.cube_size(&nat_zero))
}

/// Step `motive k → motive (k+1)`. `Fin.prod_succ k (const 2)` peels the top
/// factor; the prefix `Fin.prod k (const 2 ∘ castSucc) ≡ Fin.prod k (const 2)`,
/// so `congrArg (·(1+1)) ih : (Fin.prod k (const 2))·(1+1) = (2^k/1)·(1+1)`, and
/// the RHS `(2^k/1)·(1+1) ≡ Rat.mk (ofNat (2^(k+1))) 1` by faithful Rat-numeral
/// reduction. The proof chains `Fin.prod_succ` then the `congrArg`; the final
/// numeral is def-eq to `cube_size (k+1)`.
fn prod_const_two_step(c: &ProdCollapseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let ih_lhs = c.prod(k.clone(), c.const_two_fn(&b, &k));
    let ih_ty = c.eq_rat(ih_lhs.clone(), c.cube_size(&k));
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());

    let sk = c.succ(&k);
    let const_sk = c.const_two_fn(&b, &sk);
    // peel : Fin.prod (k+1) const = (Fin.prod k (const∘castSucc))·(const last)
    //   const∘castSucc ≡ const k, const last ≡ (1+1), so RHS ≡ ih_lhs·(1+1).
    let peel = Expr::apps(c.fin_prod_succ.clone(), [k.clone(), const_sk.clone()]);
    let mul_pt = c.mul(ih_lhs.clone(), c.rat_two());

    // mul_by_two := fun (s : Rat) => s · (1+1)
    let mul_two = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (s_id, s) = d.fresh_local(c.rat.clone());
        let body = c.mul(s, c.rat_two());
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), body))
    };
    // step2 : ih_lhs·(1+1) = (2^k/1)·(1+1)   (congrArg (·(1+1)) ih).
    let step2 = c.congr_arg_rat(ih_lhs.clone(), c.cube_size(&k), mul_two, ih);
    let cube_k_two = c.mul(c.cube_size(&k), c.rat_two());

    // proof : Fin.prod (k+1) const = (2^k/1)·(1+1)   [= cube_size (k+1) by def-eq].
    let proof = c.trans_rat(
        c.prod(sk.clone(), const_sk),
        mul_pt,
        cube_k_two,
        peel,
        step2,
    );
    let val = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
    b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), val))
}

fn prod_const_two_value(c: &ProdCollapseConsts) -> Expr {
    let motive = prod_const_two_motive(c);
    let base = prod_const_two_base(c);
    let step = prod_const_two_step(c);
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let body = Expr::apps(c.nat_rec.clone(), [motive, base, step, n]);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
}

impl Environment {
    /// Register `BoolAnalysis.prod_const_two_eq_pow` (the diagonal numeral
    /// collapse `Π_{i<n} 2 = 2^n/1`) as a kernel-checked, constructive theorem.
    /// Idempotent.
    pub(crate) fn register_prod_const_two_eq_pow(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.prod_const_two_eq_pow");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?;
        self.init_rat()?;
        self.register_fin_prod_succ_theorem()?;

        let c = ProdCollapseConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: prod_const_two_type(&c),
            value: prod_const_two_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_fin_prod_eq_zero_of_factor_zero()
            .expect("register_fin_prod_eq_zero_of_factor_zero");
        env.register_fin_prod_diag_eq_two()
            .expect("register_fin_prod_diag_eq_two");
        env.register_factor_vanish_of_xor()
            .expect("register_factor_vanish_of_xor");
        env
    }

    fn check_constructive(env: &Environment, name: &str) {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} proof must check: {e:?}"));
        assert_eq!(
            env.proof_quality(&Name::from_string(name)),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
        assert!(
            env.axiom_deps(&Name::from_string(name))
                .expect("deps")
                .is_empty(),
            "{name}'s transitive axiom closure must be empty"
        );
    }

    #[test]
    fn test_fin_prod_eq_zero_of_factor_zero_is_constructive_theorem() {
        let env = make_env();
        check_constructive(&env, "Fin.prod_eq_zero_of_factor_zero");
    }

    #[test]
    fn test_fin_prod_diag_eq_two_is_constructive_theorem() {
        let env = make_env();
        check_constructive(&env, "BoolAnalysis.prod_diag_eq_two");
    }

    #[test]
    fn test_factor_vanish_of_xor_is_constructive_theorem() {
        let env = make_env();
        check_constructive(&env, "BoolAnalysis.factor_vanish_of_xor");
    }

    #[test]
    fn test_prod_const_two_eq_pow_is_constructive_theorem() {
        let mut env = make_env();
        env.register_prod_const_two_eq_pow()
            .expect("register_prod_const_two_eq_pow");
        check_constructive(&env, "BoolAnalysis.prod_const_two_eq_pow");
    }

    #[test]
    fn test_register_idempotent() {
        let mut env = make_env();
        env.register_fin_prod_eq_zero_of_factor_zero()
            .expect("idempotent re-register");
        env.register_fin_prod_diag_eq_two()
            .expect("idempotent re-register");
        env.register_factor_vanish_of_xor()
            .expect("idempotent re-register");
    }
}
