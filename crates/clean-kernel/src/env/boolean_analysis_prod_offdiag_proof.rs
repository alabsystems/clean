// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Step 1 of the Parseval assembly: the OFF-DIAGONAL collapse of the indexed
//! product integrand. The missing rung between `factor_vanish_of_xor` /
//! `Fin.prod_eq_zero_of_factor_zero` (already landed) and the Kronecker collapse
//! the assembly needs.
//!
//! Two declarations, both kernel-checked `Declaration::Theorem`s with an EMPTY
//! admitted-axiom closure (`ProofQuality::Constructive`):
//!
//! - `BoolAnalysis.prod_factor_zero_or_pointwise_eq :`
//!   `∀ (n : Nat) (x y : HCPoint n),`
//!   `  Or (Eq Rat (Fin.prod n (fun i => 1 + pm(x i)·pm(y i))) Rat.zero)`
//!   `     (∀ (i : Fin n), Eq Bool (x i) (y i))`
//!   — the constructive dichotomy: EITHER the Parseval product integrand
//!   vanishes (the two cube points differ at some coordinate), OR the two points
//!   agree at every coordinate. Proved by `Nat.rec` on `n`. The base `n = 0` is
//!   the right branch (vacuous over the empty `Fin 0`). The step peels the top
//!   coordinate (`Fin.lastCases` + a `Bool.rec` 2×2 decision on `x last`,
//!   `y last`): if they DIFFER at the top, `factor_vanish_of_xor` makes the top
//!   factor `0` and `Fin.prod_eq_zero_of_factor_zero` (at `Fin.last`) collapses
//!   the whole product (left branch); if they AGREE at the top, the IH on the
//!   `Fin.castSucc` restrictions either gives a zero PREFIX factor (collapse at a
//!   `Fin.castSucc` index, left branch) or all-prefix-agreement, which combines
//!   with the top agreement via `Fin.lastCases` into full agreement (right).
//!
//! - `BoolAnalysis.prod_offdiag_eq_zero :`
//!   `∀ (n : Nat) (j k : Fin (Nat.pow 2 n)),`
//!   `  (Eq (Fin (Nat.pow 2 n)) j k → False) →`
//!   `  Eq Rat (Fin.prod n (fun i => 1 + pm(hcDecode n j i)·pm(hcDecode n k i)))`
//!   `         Rat.zero`
//!   — the off-diagonal product collapse the Kronecker step consumes. Apply the
//!   dichotomy at `x = hcDecode n j`, `y = hcDecode n k`. The right branch
//!   (`∀ i, hcDecode n j i = hcDecode n k i`, i.e. all bits of `val j` and
//!   `val k` below `n` agree) forces `val j = val k` (`Nat.eq_of_testBit_eq`
//!   after equalizing the bits ≥ n via `Nat.testBit_lt_pow`), hence `j = k`
//!   (`Fin.eq_of_val_eq`), contradicting the hypothesis — `False.elim`. So the
//!   left branch holds: the product is `0`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants for the off-diagonal collapse proofs.
struct OffDiagConsts {
    nat: Expr,
    bool_: Expr,
    rat: Expr,
    fin: Expr,
    rat_one: Expr,
    rat_zero: Expr,
    rat_mul: Expr,
    rat_add: Expr,
    pm: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_rec: Expr,
    fin_rec0: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    fin_prod: Expr,
    bool_rec0: Expr,
    btrue: Expr,
    bfalse: Expr,
    bool_xor: Expr,
    factor_vanish: Expr,
    prod_zero: Expr,
    last_cases0: Expr,
    not_succ_le_zero: Expr,
    false_elim0: Expr,
    or_c: Expr,
    or_inl: Expr,
    or_inr: Expr,
    or_rec: Expr,
    eq_bool: Expr,
    eq_refl_bool: Expr,
    hcpoint: Expr,
}

impl OffDiagConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            pm: Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            // Motive of the outer induction is `∀ x y, Or … …` (a Prop), so the
            // Nat.rec elimination is at universe 0.
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            // base-case `Fin.rec` produces a `Prop` (the vacuous goal), universe 0.
            fin_rec0: Expr::const_(Name::from_string("Fin.rec"), vec![Level::zero()]),
            fin_cast_succ: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            fin_prod: Expr::const_(Name::from_string("Fin.prod"), vec![]),
            // Bool.rec into Prop (the dichotomy / pointwise goal), universe 0.
            bool_rec0: Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            btrue: Expr::const_(Name::from_string("Bool.true"), vec![]),
            bfalse: Expr::const_(Name::from_string("Bool.false"), vec![]),
            bool_xor: Expr::const_(Name::from_string("Bool.xor"), vec![]),
            factor_vanish: Expr::const_(
                Name::from_string("BoolAnalysis.factor_vanish_of_xor"),
                vec![],
            ),
            prod_zero: Expr::const_(Name::from_string("Fin.prod_eq_zero_of_factor_zero"), vec![]),
            last_cases0: Expr::const_(Name::from_string("Fin.lastCases"), vec![Level::zero()]),
            not_succ_le_zero: Expr::const_(Name::from_string("Nat.not_succ_le_zero"), vec![]),
            false_elim0: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            or_c: Expr::const_(Name::from_string("Or"), vec![]),
            or_inl: Expr::const_(Name::from_string("Or.inl"), vec![]),
            or_inr: Expr::const_(Name::from_string("Or.inr"), vec![]),
            or_rec: Expr::const_(Name::from_string("Or.rec"), vec![]),
            eq_bool: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl_bool: Expr::const_(Name::from_string("Eq.refl"), vec![l1]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn pm(&self, b: Expr) -> Expr {
        Expr::app(self.pm.clone(), b)
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn prod(&self, n: Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_prod.clone(), [n, g])
    }
    fn cast_succ(&self, n: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.fin_cast_succ.clone(), [n.clone(), i.clone()])
    }
    fn last(&self, n: &Expr) -> Expr {
        Expr::app(self.fin_last.clone(), n.clone())
    }
    fn xor(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.bool_xor.clone(), [a, b])
    }
    fn eq_b(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq_bool.clone(), [self.bool_.clone(), l, r])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [self.rat.clone(), l, r],
        )
    }

    /// The Parseval product factor function `fun (i : Fin m) => 1 + pm(x i)·pm(y i)`.
    fn integrand(&self, parent: &EnvDeclBuilder, m: &Expr, x: &Expr, y: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_m = self.fin_of(m);
        let (i_id, i) = b.fresh_local(fin_m.clone());
        let pm_x = self.pm(Expr::app(x.clone(), i.clone()));
        let pm_y = self.pm(Expr::app(y.clone(), i.clone()));
        let body = self.add(self.rat_one.clone(), self.mul(pm_x, pm_y));
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_m, body))
    }

    /// `Fin.prod m (integrand m x y) = Rat.zero` — the LEFT disjunct.
    fn left_prop(&self, parent: &EnvDeclBuilder, m: &Expr, x: &Expr, y: &Expr) -> Expr {
        self.eq_rat(
            self.prod(m.clone(), self.integrand(parent, m, x, y)),
            self.rat_zero.clone(),
        )
    }

    /// `∀ (i : Fin m), Eq Bool (x i) (y i)` — the RIGHT disjunct.
    fn right_prop(&self, parent: &EnvDeclBuilder, m: &Expr, x: &Expr, y: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_m = self.fin_of(m);
        let (i_id, i) = b.fresh_local(fin_m.clone());
        let body = self.eq_b(Expr::app(x.clone(), i.clone()), Expr::app(y.clone(), i));
        b.finish_child(b.mk_pi(i_id, BinderInfo::Default, fin_m, body))
    }

    /// `Or (left) (right)` — the dichotomy conclusion for `(m, x, y)`.
    fn or_goal(&self, parent: &EnvDeclBuilder, m: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.or_c.clone(),
            [
                self.left_prop(parent, m, x, y),
                self.right_prop(parent, m, x, y),
            ],
        )
    }

    /// `fun (i : Fin k) => p (Fin.castSucc k i)` — the prefix restriction of a
    /// cube point `p : HCPoint (k+1)` to `HCPoint k`.
    fn restrict(&self, parent: &EnvDeclBuilder, k: &Expr, p: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_k = self.fin_of(k);
        let (i_id, i) = b.fresh_local(fin_k.clone());
        let body = Expr::app(p.clone(), self.cast_succ(k, &i));
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_k, body))
    }

    /// `motive m := ∀ (x y : HCPoint m), Or (left) (right)`.
    fn motive_body(&self, parent: &EnvDeclBuilder, m: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(m);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let (y_id, y) = b.fresh_local(hcp.clone());
        let concl = self.or_goal(&b, m, &x, &y);
        let r = b.mk_pi(y_id, BinderInfo::Default, hcp.clone(), concl);
        let r = b.mk_pi(x_id, BinderInfo::Default, hcp, r);
        b.finish_child(r)
    }
}

// ── BoolAnalysis.prod_factor_zero_or_pointwise_eq ──

fn dichotomy_type(c: &OffDiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let body = c.motive_body(&b, &n);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), body);
    b.finish(ty)
}

fn dichotomy_motive(c: &OffDiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let body = c.motive_body(&b, &k);
    b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
}

/// Base `motive 0`: `∀ (x y : HCPoint 0), Or (...) (∀ i : Fin 0, x i = y i)`.
/// Take the RIGHT disjunct: `∀ i : Fin 0, x i = y i` is vacuous (`Fin 0` empty),
/// proved by `Fin.rec` refuting the index via `Nat.not_succ_le_zero` + `False.elim`.
fn dichotomy_base(c: &OffDiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let zero = c.nat_zero.clone();
    let hcp = c.hcpoint_of(&zero);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (y_id, y) = b.fresh_local(hcp.clone());

    let left = c.left_prop(&b, &zero, &x, &y);
    let right = c.right_prop(&b, &zero, &x, &y);

    // proof of `right` = fun (i : Fin 0) => False.elim (x i = y i) (not_succ_le_zero (val i) (isLt i))
    // built via Fin.rec refuting the index.
    let right_proof = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin0 = c.fin_of(&zero);
        let (i_id, i) = d.fresh_local(fin0.clone());
        let goal = c.eq_b(
            Expr::app(x.clone(), i.clone()),
            Expr::app(y.clone(), i.clone()),
        );
        // Fin.rec motive: fun (_ : Fin 0) => goal
        let motive = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (w_id, _w) = e.fresh_local(fin0.clone());
            e.finish_child(e.mk_lam(w_id, BinderInfo::Default, fin0.clone(), goal.clone()))
        };
        // mk minor: fun (val : Nat) (isLt : Nat.lt val 0) =>
        //   False.elim goal (not_succ_le_zero val isLt)
        let mk_case = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (val_id, val) = e.fresh_local(c.nat.clone());
            let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
            let islt_ty = Expr::apps(nat_lt, [val.clone(), zero.clone()]);
            let (islt_id, islt) = e.fresh_local(islt_ty.clone());
            let contra = Expr::apps(c.not_succ_le_zero.clone(), [val.clone(), islt]);
            let body = Expr::apps(c.false_elim0.clone(), [goal.clone(), contra]);
            let r = e.mk_lam(islt_id, BinderInfo::Default, islt_ty, body);
            let r = e.mk_lam(val_id, BinderInfo::Default, c.nat.clone(), r);
            e.finish_child(r)
        };
        let rec = Expr::apps(
            c.fin_rec0.clone(),
            [zero.clone(), motive, mk_case, i.clone()],
        );
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin0, rec))
    };

    // Or.inr left right right_proof : Or left right
    let inr = Expr::apps(c.or_inr.clone(), [left, right, right_proof]);
    let val = b.mk_lam(y_id, BinderInfo::Default, hcp.clone(), inr);
    let val = b.mk_lam(x_id, BinderInfo::Default, hcp, val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.prod_factor_zero_or_pointwise_eq` — the constructive
    /// dichotomy (product vanishes OR points agree pointwise). Kernel-checked,
    /// constructive. Idempotent.
    pub(crate) fn register_prod_factor_zero_or_pointwise_eq(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.prod_factor_zero_or_pointwise_eq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?;
        self.init_rat()?;
        self.register_fin_prod_succ_theorem()?;
        self.register_fin_last_cases()?;
        self.register_fin_prod_eq_zero_of_factor_zero()?;
        self.register_factor_vanish_of_xor()?;

        let c = OffDiagConsts::new();
        let ty = dichotomy_type(&c);
        let value = dichotomy_value(&c);
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

fn dichotomy_value(c: &OffDiagConsts) -> Expr {
    let motive = dichotomy_motive(c);
    let base = dichotomy_base(c);
    let step = dichotomy_step(c);
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let body = Expr::apps(c.nat_rec.clone(), [motive, base, step, n]);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
}

impl OffDiagConsts {
    fn rat_zero_mul(&self, a: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Rat.zero_mul"), vec![]), a)
    }
    /// `@congrArg Rat Rat from to g h : g from = g to`.
    fn congr_arg_rat(&self, from: Expr, to: Expr, g: Expr, h: Expr) -> Expr {
        let l1 = Level::succ(Level::zero());
        Expr::apps(
            Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            [self.rat.clone(), self.rat.clone(), from, to, g, h],
        )
    }
    fn trans_rat(&self, a: Expr, bb: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.trans"),
                vec![Level::succ(Level::zero())],
            ),
            [self.rat.clone(), a, bb, cc, h1, h2],
        )
    }
    /// `@Eq.trans Bool a b c h1 h2`.
    fn trans_bool(&self, a: Expr, bb: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.trans"),
                vec![Level::succ(Level::zero())],
            ),
            [self.bool_.clone(), a, bb, cc, h1, h2],
        )
    }
    /// `@Eq.symm Bool l r h : Eq Bool r l`.
    fn symm_bool(&self, l: Expr, r: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.symm"),
                vec![Level::succ(Level::zero())],
            ),
            [self.bool_.clone(), l, r, h],
        )
    }
    /// `@congrArg Bool Bool from to g h : g from = g to`.
    fn congr_arg_bool(&self, from: Expr, to: Expr, g: Expr, h: Expr) -> Expr {
        let l1 = Level::succ(Level::zero());
        Expr::apps(
            Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            [self.bool_.clone(), self.bool_.clone(), from, to, g, h],
        )
    }
    fn eq_refl_b(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl_bool.clone(), [self.bool_.clone(), x])
    }
}

/// Step `motive k → motive (k+1)`.
///
/// `fun (k : Nat) (ih : motive k) (x y : HCPoint (k+1)) =>`
///   case on `x (last k)` then `y (last k)` (nested `Bool.rec`, each with an
///   implication motive recording the value); in each of the four leaves either
///   the top coords DIFFER (→ `Or.inl`, top factor `0` collapses the product) or
///   AGREE (→ run `ih` on the `Fin.castSucc` restrictions and case its `Or`).
fn dichotomy_step(c: &OffDiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let ih_ty = c.motive_body(&b, &k);
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());

    let sk = c.succ(&k);
    let hcp_sk = c.hcpoint_of(&sk);
    let (x_id, x) = b.fresh_local(hcp_sk.clone());
    let (y_id, y) = b.fresh_local(hcp_sk.clone());

    // Restrictions to HCPoint k.
    let xr = c.restrict(&b, &k, &x);
    let yr = c.restrict(&b, &k, &y);

    // The (k+1)-integrand and the overall Or goal.
    let integ = c.integrand(&b, &sk, &x, &y);
    let goal = c.or_goal(&b, &sk, &x, &y);
    let left = c.left_prop(&b, &sk, &x, &y);
    let right = c.right_prop(&b, &sk, &x, &y);

    let x_last = Expr::app(x.clone(), c.last(&k));
    let y_last = Expr::app(y.clone(), c.last(&k));

    // ── leaf builder: given concrete top values `va,vb` and proofs
    //    `ea : x last = va`, `eb : y last = vb`, build the Or goal. ──
    let leaf = |va: Expr,
                vb: Expr,
                ea: Expr,
                eb: Expr,
                agree: bool,
                parent: &EnvDeclBuilder|
     -> Expr {
        let _d = EnvDeclBuilder::child_of(parent);
        if !agree {
            // DIFFER at top: xor (x last)(y last) = true (def-eq to xor va vb).
            // hxor := congr (congrArg xor ea) eb  : xor (x last)(y last) = xor va vb
            // (kernel accepts as `… = true` since xor va vb ≡ true).
            let xor_fn = |bb: Expr| {
                // fun (t : Bool) => xor t bb   — to congrArg over ea.
                let mut e = EnvDeclBuilder::child_of(&_d);
                let (t_id, t) = e.fresh_local(c.bool_.clone());
                e.finish_child(e.mk_lam(t_id, BinderInfo::Default, c.bool_.clone(), c.xor(t, bb)))
            };
            // step over ea: xor (x last)(y last) = xor va (y last)
            let s1 = c.congr_arg_bool(
                x_last.clone(),
                va.clone(),
                xor_fn(y_last.clone()),
                ea.clone(),
            );
            // step over eb: xor va (y last) = xor va vb
            let xor_va = {
                let mut e = EnvDeclBuilder::child_of(&_d);
                let (t_id, t) = e.fresh_local(c.bool_.clone());
                e.finish_child(e.mk_lam(
                    t_id,
                    BinderInfo::Default,
                    c.bool_.clone(),
                    c.xor(va.clone(), t),
                ))
            };
            let s2 = c.congr_arg_bool(y_last.clone(), vb.clone(), xor_va, eb.clone());
            let hxor = c.trans_bool(
                c.xor(x_last.clone(), y_last.clone()),
                c.xor(va.clone(), y_last.clone()),
                c.xor(va.clone(), vb.clone()),
                s1,
                s2,
            );
            // factor_vanish_of_xor (x last) (y last) hxor : 1 + pm(x last)·pm(y last) = 0
            // (def-eq to integ (last k) = 0).
            let hfac = Expr::apps(
                c.factor_vanish.clone(),
                [x_last.clone(), y_last.clone(), hxor],
            );
            // Fin.prod_eq_zero_of_factor_zero (k+1) integ (last k) hfac : prod (k+1) integ = 0
            let pz = Expr::apps(
                c.prod_zero.clone(),
                [sk.clone(), integ.clone(), c.last(&k), hfac],
            );
            // Or.inl left right pz
            Expr::apps(c.or_inl.clone(), [left.clone(), right.clone(), pz])
        } else {
            // AGREE at top. va ≡ vb (same constructor). `eb : y last = va`, so
            // top_eq : x last = y last  via Eq.trans ea (Eq.symm eb).
            let top_eq = c.trans_bool(
                x_last.clone(),
                va.clone(),
                y_last.clone(),
                ea.clone(),
                c.symm_bool(y_last.clone(), vb.clone(), eb.clone()),
            );
            // ih xr yr : Or (prod k (integ k xr yr) = 0) (∀ i:Fin k, xr i = yr i)
            let ih_app = Expr::apps(ih.clone(), [xr.clone(), yr.clone()]);
            let ih_left = c.left_prop(&_d, &k, &xr, &yr);
            let ih_right = c.right_prop(&_d, &k, &xr, &yr);

            // Or.rec motive: fun (_ : Or ih_left ih_right) => goal
            let or_motive = {
                let mut e = EnvDeclBuilder::child_of(&_d);
                let or_ty = Expr::apps(c.or_c.clone(), [ih_left.clone(), ih_right.clone()]);
                let (h_id, _h) = e.fresh_local(or_ty.clone());
                e.finish_child(e.mk_lam(h_id, BinderInfo::Default, or_ty, goal.clone()))
            };

            // case ih_left: prefix product = 0 ⇒ full product = 0.
            //   prod_succ (k) integ : prod (k+1) integ = (prod k (integ∘castSucc))·(integ last)
            //   integ∘castSucc ≡ integ k xr yr definitionally.
            //   congrArg (·(integ last)) ih_left' : (prod k …)·(integ last) = 0·(integ last)
            //   Rat.zero_mul (integ last) : 0·(integ last) = 0.
            let case_left = {
                let mut e = EnvDeclBuilder::child_of(&_d);
                let (hl_id, hl) = e.fresh_local(ih_left.clone());
                // peel : prod (k+1) integ = (prod k (integ∘castSucc)) · (integ (last k))
                let peel = Expr::apps(
                    Expr::const_(Name::from_string("Fin.prod_succ"), vec![]),
                    [k.clone(), integ.clone()],
                );
                // prefix product (def-eq to prod k (integ k xr yr)) and top factor.
                let pre = c.restrict_integrand_prod(&e, &k, &integ);
                let integ_last = Expr::app(integ.clone(), c.last(&k));
                let mul_pt = c.mul(pre.clone(), integ_last.clone());
                // mul_by_top := fun (s : Rat) => s · (integ last)
                let mul_top = {
                    let mut g = EnvDeclBuilder::child_of(&e);
                    let (s_id, s) = g.fresh_local(c.rat.clone());
                    let body = c.mul(s, integ_last.clone());
                    g.finish_child(g.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), body))
                };
                // hl : prod k (integ k xr yr) = 0 (def-eq to `pre = 0`).
                let step2 = c.congr_arg_rat(pre.clone(), c.rat_zero.clone(), mul_top, hl);
                let mul_zero_t = c.mul(c.rat_zero.clone(), integ_last.clone());
                let step3 = c.rat_zero_mul(integ_last.clone());
                let t23 = c.trans_rat(mul_pt.clone(), mul_zero_t, c.rat_zero.clone(), step2, step3);
                let proof = c.trans_rat(
                    c.prod(sk.clone(), integ.clone()),
                    mul_pt,
                    c.rat_zero.clone(),
                    peel,
                    t23,
                );
                let inl = Expr::apps(c.or_inl.clone(), [left.clone(), right.clone(), proof]);
                e.finish_child(e.mk_lam(hl_id, BinderInfo::Default, ih_left.clone(), inl))
            };

            // case ih_right: all prefix coords agree ⇒ all coords agree (combine
            //   with top_eq via Fin.lastCases).
            let case_right = {
                let mut e = EnvDeclBuilder::child_of(&_d);
                let (hr_id, hr) = e.fresh_local(ih_right.clone());
                // build `∀ i : Fin (k+1), x i = y i` via Fin.lastCases.
                //   lc_motive : fun (i : Fin (k+1)) => Eq Bool (x i) (y i)
                let lc_motive = {
                    let mut g = EnvDeclBuilder::child_of(&e);
                    let (i_id, i) = g.fresh_local(c.fin_of(&sk));
                    let body = c.eq_b(Expr::app(x.clone(), i.clone()), Expr::app(y.clone(), i));
                    g.finish_child(g.mk_lam(i_id, BinderInfo::Default, c.fin_of(&sk), body))
                };
                //   last_case : Eq Bool (x (last k)) (y (last k))  = top_eq
                //   cast_case : fun (i' : Fin k) => Eq Bool (x (castSucc i')) (y (castSucc i'))
                //     = fun i' => hr i'   (def-eq: xr i' ≡ x (castSucc i')).
                let cast_case = {
                    let mut g = EnvDeclBuilder::child_of(&e);
                    let (ip_id, ip) = g.fresh_local(c.fin_of(&k));
                    let body = Expr::app(hr.clone(), ip.clone());
                    g.finish_child(g.mk_lam(ip_id, BinderInfo::Default, c.fin_of(&k), body))
                };
                // @Fin.lastCases k lc_motive last_case cast_case : (i:Fin(k+1)) → x i = y i
                let lc = Expr::apps(
                    c.last_cases0.clone(),
                    [k.clone(), lc_motive, top_eq.clone(), cast_case],
                );
                let inr = Expr::apps(c.or_inr.clone(), [left.clone(), right.clone(), lc]);
                e.finish_child(e.mk_lam(hr_id, BinderInfo::Default, ih_right.clone(), inr))
            };

            // Or.rec ih_left ih_right or_motive case_left case_right ih_app
            Expr::apps(
                c.or_rec.clone(),
                [ih_left, ih_right, or_motive, case_left, case_right, ih_app],
            )
        }
    };

    // ── inner Bool.rec on `y last`, given outer top value `va` and `ea`. ──
    let inner = |va: Expr, ea: Expr, parent: &EnvDeclBuilder| -> Expr {
        let d = EnvDeclBuilder::child_of(parent);
        // motive_b : fun (b' : Bool) => Eq Bool (y last) b' → goal
        let motive_b = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (bp_id, bp) = e.fresh_local(c.bool_.clone());
            let eb_ty = c.eq_b(y_last.clone(), bp.clone());
            let body = Expr::pi(BinderInfo::Default, eb_ty, goal.clone());
            e.finish_child(e.mk_lam(bp_id, BinderInfo::Default, c.bool_.clone(), body))
        };
        // b = false leaf
        let leaf_bf = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let eb_ty = c.eq_b(y_last.clone(), c.bfalse.clone());
            let (eb_id, eb) = e.fresh_local(eb_ty.clone());
            let agree = va == c.bfalse;
            let body = leaf(va.clone(), c.bfalse.clone(), ea.clone(), eb, agree, &e);
            e.finish_child(e.mk_lam(eb_id, BinderInfo::Default, eb_ty, body))
        };
        // b = true leaf
        let leaf_bt = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let eb_ty = c.eq_b(y_last.clone(), c.btrue.clone());
            let (eb_id, eb) = e.fresh_local(eb_ty.clone());
            let agree = va == c.btrue;
            let body = leaf(va.clone(), c.btrue.clone(), ea.clone(), eb, agree, &e);
            e.finish_child(e.mk_lam(eb_id, BinderInfo::Default, eb_ty, body))
        };
        // @Bool.rec motive_b leaf_bf leaf_bt (y last) : Eq Bool (y last)(y last) → goal
        let rec = Expr::apps(
            c.bool_rec0.clone(),
            [motive_b, leaf_bf, leaf_bt, y_last.clone()],
        );
        // apply to Eq.refl (y last)
        d.finish_child(Expr::app(rec, c.eq_refl_b(y_last.clone())))
    };

    // ── outer Bool.rec on `x last`. ──
    let motive_a = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (ap_id, ap) = d.fresh_local(c.bool_.clone());
        let ea_ty = c.eq_b(x_last.clone(), ap.clone());
        let body = Expr::pi(BinderInfo::Default, ea_ty, goal.clone());
        d.finish_child(d.mk_lam(ap_id, BinderInfo::Default, c.bool_.clone(), body))
    };
    let leaf_af = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let ea_ty = c.eq_b(x_last.clone(), c.bfalse.clone());
        let (ea_id, ea) = d.fresh_local(ea_ty.clone());
        let body = inner(c.bfalse.clone(), ea, &d);
        d.finish_child(d.mk_lam(ea_id, BinderInfo::Default, ea_ty, body))
    };
    let leaf_at = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let ea_ty = c.eq_b(x_last.clone(), c.btrue.clone());
        let (ea_id, ea) = d.fresh_local(ea_ty.clone());
        let body = inner(c.btrue.clone(), ea, &d);
        d.finish_child(d.mk_lam(ea_id, BinderInfo::Default, ea_ty, body))
    };
    let rec_a = Expr::apps(
        c.bool_rec0.clone(),
        [motive_a, leaf_af, leaf_at, x_last.clone()],
    );
    let applied = Expr::app(rec_a, c.eq_refl_b(x_last.clone()));

    let val = b.mk_lam(y_id, BinderInfo::Default, hcp_sk.clone(), applied);
    let val = b.mk_lam(x_id, BinderInfo::Default, hcp_sk, val);
    let val = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, val);
    let val = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl OffDiagConsts {
    /// `Fin.prod k (fun i => integ (Fin.castSucc k i))` — the prefix product the
    /// `Fin.prod_succ` peel produces (def-eq to `Fin.prod k (integrand k xr yr)`).
    fn restrict_integrand_prod(&self, parent: &EnvDeclBuilder, k: &Expr, integ: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_k = self.fin_of(k);
        let (i_id, i) = b.fresh_local(fin_k.clone());
        let body = Expr::app(integ.clone(), self.cast_succ(k, &i));
        let f = b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_k, body));
        self.prod(k.clone(), f)
    }
}

// ===========================================================================
// BoolAnalysis.prod_offdiag_eq_zero — the off-diagonal product collapse.
//
//   ∀ (n : Nat) (j k : Fin (Nat.pow 2 n)),
//     (Eq (Fin (Nat.pow 2 n)) j k → False) →
//     Eq Rat (Fin.prod n (fun i => 1 + pm(hcDecode n j i)·pm(hcDecode n k i)))
//            Rat.zero
//
// Apply the dichotomy at x = hcDecode n j, y = hcDecode n k. The LEFT disjunct
// IS the goal. The RIGHT disjunct (`∀ i:Fin n, hcDecode n j i = hcDecode n k i`)
// forces j = k (every low-n bit agrees, every bit ≥ n is false on both since
// val j, val k < 2^n), contradicting the hypothesis — `False.elim`.
// ===========================================================================

/// Const set for the off-diagonal wrapper (Fin/Nat order + testBit plumbing).
struct OffDiagWrapConsts {
    nat: Expr,
    bool_: Expr,
    fin: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_pow: Expr,
    two: Expr,
    fin_val: Expr,
    fin_mk: Expr,
    fin_islt: Expr,
    nat_lt: Expr,
    nat_le: Expr,
    testbit: Expr,
    hc_decode: Expr,
    or_rec: Expr,
    false_elim0: Expr,
    le_or_lt: Expr,
    pow_le_pow_right: Expr,
    lt_of_lt_of_le: Expr,
    testbit_lt_pow: Expr,
    eq_of_testbit_eq: Expr,
    fin_eq_of_val_eq: Expr,
    nat_le_step: Expr,
    nat_le_refl: Expr,
    eq_bool: Expr,
    eq_trans_bool: Expr,
    eq_symm_bool: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    btrue: Expr,
    bfalse: Expr,
    dichotomy: Expr,
}

impl OffDiagWrapConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let z = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let s = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let two = Expr::app(s.clone(), Expr::app(s.clone(), z.clone()));
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nat_succ: s.clone(),
            nat_zero: z,
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            two,
            fin_val: Expr::const_(Name::from_string("Fin.val"), vec![]),
            fin_mk: Expr::const_(Name::from_string("Fin.mk"), vec![]),
            fin_islt: Expr::const_(Name::from_string("Fin.isLt"), vec![]),
            nat_lt: Expr::const_(Name::from_string("Nat.lt"), vec![]),
            nat_le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            testbit: Expr::const_(Name::from_string("Nat.testBit"), vec![]),
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            or_rec: Expr::const_(Name::from_string("Or.rec"), vec![]),
            false_elim0: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            le_or_lt: Expr::const_(Name::from_string("Nat.le_or_lt"), vec![]),
            pow_le_pow_right: Expr::const_(Name::from_string("Nat.pow_le_pow_right"), vec![]),
            lt_of_lt_of_le: Expr::const_(Name::from_string("Nat.lt_of_lt_of_le"), vec![]),
            testbit_lt_pow: Expr::const_(Name::from_string("Nat.testBit_lt_pow"), vec![]),
            eq_of_testbit_eq: Expr::const_(Name::from_string("Nat.eq_of_testBit_eq"), vec![]),
            fin_eq_of_val_eq: Expr::const_(Name::from_string("Fin.eq_of_val_eq"), vec![]),
            nat_le_step: Expr::const_(Name::from_string("Nat.le.step"), vec![]),
            nat_le_refl: Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
            eq_bool: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans_bool: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm_bool: Expr::const_(Name::from_string("Eq.symm"), vec![l1]),
            #[cfg(test)]
            btrue: Expr::const_(Name::from_string("Bool.true"), vec![]),
            bfalse: Expr::const_(Name::from_string("Bool.false"), vec![]),
            dichotomy: Expr::const_(
                Name::from_string("BoolAnalysis.prod_factor_zero_or_pointwise_eq"),
                vec![],
            ),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    /// `@Fin.val n x`.
    fn val(&self, n: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [n.clone(), x.clone()])
    }
    /// `Nat.testBit a b`.
    fn testbit(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.testbit.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_lt.clone(), [a, b])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn eq_b(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq_bool.clone(), [self.bool_.clone(), l, r])
    }
    fn hc_decode(&self, n: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), j.clone()])
    }
    /// `1 ≤ 2` proof: `Nat.le.step 1 1 (Nat.le.refl 1)`.
    fn one_le_two(&self) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let refl = Expr::app(self.nat_le_refl.clone(), one.clone());
        Expr::apps(self.nat_le_step.clone(), [one.clone(), one, refl])
    }
}

fn offdiag_zero_type(c: &OffDiagWrapConsts, oc: &OffDiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fin_pow = c.fin_of(&c.pow2(&n));
    let (j_id, j) = b.fresh_local(fin_pow.clone());
    let (k_id, k) = b.fresh_local(fin_pow.clone());
    // ne : Eq (Fin (2^n)) j k → False
    let eq_jk = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [fin_pow.clone(), j.clone(), k.clone()],
    );
    let false_c = Expr::const_(Name::from_string("False"), vec![]);
    let ne = Expr::pi(BinderInfo::Default, eq_jk, false_c);
    let (ne_id, _ne) = b.fresh_local(ne.clone());
    // goal: Fin.prod n (integrand n (hcDecode n j) (hcDecode n k)) = 0
    let xd = c.hc_decode(&n, &j);
    let yd = c.hc_decode(&n, &k);
    let concl = oc.left_prop(&b, &n, &xd, &yd);
    let r = b.mk_pi(ne_id, BinderInfo::Default, ne, concl);
    let r = b.mk_pi(k_id, BinderInfo::Default, fin_pow.clone(), r);
    let r = b.mk_pi(j_id, BinderInfo::Default, fin_pow, r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

fn offdiag_zero_value(c: &OffDiagWrapConsts, oc: &OffDiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fin_pow = c.fin_of(&c.pow2(&n));
    let (j_id, j) = b.fresh_local(fin_pow.clone());
    let (k_id, k) = b.fresh_local(fin_pow.clone());
    let eq_jk = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [fin_pow.clone(), j.clone(), k.clone()],
    );
    let false_c = Expr::const_(Name::from_string("False"), vec![]);
    let ne_ty = Expr::pi(BinderInfo::Default, eq_jk.clone(), false_c.clone());
    let (ne_id, ne) = b.fresh_local(ne_ty.clone());

    let xd = c.hc_decode(&n, &j);
    let yd = c.hc_decode(&n, &k);
    let goal = oc.left_prop(&b, &n, &xd, &yd);

    // dichotomy n xd yd : Or (left) (right)
    let dich = Expr::apps(c.dichotomy.clone(), [n.clone(), xd.clone(), yd.clone()]);
    let left = oc.left_prop(&b, &n, &xd, &yd);
    let right = oc.right_prop(&b, &n, &xd, &yd);

    // Or.rec motive: fun (_ : Or left right) => goal (= left).
    let or_motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let or_ty = Expr::apps(
            Expr::const_(Name::from_string("Or"), vec![]),
            [left.clone(), right.clone()],
        );
        let (h_id, _h) = d.fresh_local(or_ty.clone());
        d.finish_child(d.mk_lam(h_id, BinderInfo::Default, or_ty, goal.clone()))
    };
    // case_left: the witness directly.
    let case_left = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (hl_id, hl) = d.fresh_local(left.clone());
        d.finish_child(d.mk_lam(hl_id, BinderInfo::Default, left.clone(), hl))
    };
    // case_right: contradiction via j = k.
    let case_right = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (hr_id, hr) = d.fresh_local(right.clone());

        // all_bits : ∀ (bpos : Nat), testBit (val j) bpos = testBit (val k) bpos
        let val_j = c.val(&c.pow2(&n), &j);
        let val_k = c.val(&c.pow2(&n), &k);
        let all_bits = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (bp_id, bp) = e.fresh_local(c.nat.clone());
            // case on Nat.le_or_lt n bp : Or (n ≤ bp) (bp < n)
            let le_n_bp = c.le(n.clone(), bp.clone());
            let lt_bp_n = c.lt(bp.clone(), n.clone());
            let bit_eq = c.eq_b(
                c.testbit(val_j.clone(), bp.clone()),
                c.testbit(val_k.clone(), bp.clone()),
            );
            let inner_or_motive = {
                let mut g = EnvDeclBuilder::child_of(&e);
                let or_ty = Expr::apps(
                    Expr::const_(Name::from_string("Or"), vec![]),
                    [le_n_bp.clone(), lt_bp_n.clone()],
                );
                let (h_id, _h) = g.fresh_local(or_ty.clone());
                g.finish_child(g.mk_lam(h_id, BinderInfo::Default, or_ty, bit_eq.clone()))
            };
            // HI case: n ≤ bp ⇒ both bits false.
            //   pow_le_pow_right 2 n bp (1≤2) hle : pow 2 n ≤ pow 2 bp
            //   isLt j : val j < pow 2 n ; lt_of_lt_of_le (val j) (pow 2 n) (pow 2 bp) … : val j < pow 2 bp
            //   testBit_lt_pow bp (val j) … : testBit (val j) bp = false  (likewise for k)
            //   chain: testBit (val j) bp = false = testBit (val k) bp.
            let case_hi = {
                let mut g = EnvDeclBuilder::child_of(&e);
                let (hle_id, hle) = g.fresh_local(le_n_bp.clone());
                let p2n = c.pow2(&n);
                let p2bp = c.pow2(&bp);
                let pmono = Expr::apps(
                    c.pow_le_pow_right.clone(),
                    [
                        c.two.clone(),
                        n.clone(),
                        bp.clone(),
                        c.one_le_two(),
                        hle.clone(),
                    ],
                );
                // For x ∈ {j, k}: testBit (val x) bp = false.
                let bit_false = |xfin: &Expr, gg: &EnvDeclBuilder| -> (Expr, Expr) {
                    let val_x = c.val(&p2n, xfin);
                    let islt = Expr::apps(c.fin_islt.clone(), [p2n.clone(), xfin.clone()]);
                    let lt_x_p2bp = Expr::apps(
                        c.lt_of_lt_of_le.clone(),
                        [
                            val_x.clone(),
                            p2n.clone(),
                            p2bp.clone(),
                            islt,
                            pmono.clone(),
                        ],
                    );
                    let _ = gg;
                    let h = Expr::apps(
                        c.testbit_lt_pow.clone(),
                        [bp.clone(), val_x.clone(), lt_x_p2bp],
                    );
                    (c.testbit(val_x, bp.clone()), h)
                };
                let (tj, hj_false) = bit_false(&j, &g);
                let (tk, hk_false) = bit_false(&k, &g);
                // tj = false (hj_false) ; false = tk (Eq.symm hk_false) ; trans.
                let symm_k = Expr::apps(
                    c.eq_symm_bool.clone(),
                    [c.bool_.clone(), tk.clone(), c.bfalse.clone(), hk_false],
                );
                let proof = Expr::apps(
                    c.eq_trans_bool.clone(),
                    [c.bool_.clone(), tj, c.bfalse.clone(), tk, hj_false, symm_k],
                );
                g.finish_child(g.mk_lam(hle_id, BinderInfo::Default, le_n_bp.clone(), proof))
            };
            // LO case: bp < n ⇒ use the dichotomy's right branch at i = ⟨bp, hlt⟩.
            //   hr (Fin.mk n bp hlt) : hcDecode n j ⟨bp⟩ = hcDecode n k ⟨bp⟩
            //     ≡ testBit (val j) bp = testBit (val k) bp  (Fin.val ⟨bp⟩ ≡ bp).
            let case_lo = {
                let mut g = EnvDeclBuilder::child_of(&e);
                let (hlt_id, hlt) = g.fresh_local(lt_bp_n.clone());
                let idx = Expr::apps(c.fin_mk.clone(), [n.clone(), bp.clone(), hlt.clone()]);
                let proof = Expr::app(hr.clone(), idx);
                g.finish_child(g.mk_lam(hlt_id, BinderInfo::Default, lt_bp_n.clone(), proof))
            };
            let major = Expr::apps(c.le_or_lt.clone(), [n.clone(), bp.clone()]);
            let body = Expr::apps(
                c.or_rec.clone(),
                [le_n_bp, lt_bp_n, inner_or_motive, case_hi, case_lo, major],
            );
            e.finish_child(e.mk_lam(bp_id, BinderInfo::Default, c.nat.clone(), body))
        };

        // val_eq : val j = val k  (Nat.eq_of_testBit_eq (val j) (val k) all_bits).
        let val_eq = Expr::apps(
            c.eq_of_testbit_eq.clone(),
            [val_j.clone(), val_k.clone(), all_bits],
        );
        // jk_eq : j = k  (Fin.eq_of_val_eq (2^n) j k val_eq) — n implicit.
        let jk_eq = Expr::apps(
            c.fin_eq_of_val_eq.clone(),
            [c.pow2(&n), j.clone(), k.clone(), val_eq],
        );
        // ne jk_eq : False ; False.elim goal (ne jk_eq).
        let contra = Expr::app(ne.clone(), jk_eq);
        let body = Expr::apps(c.false_elim0.clone(), [goal.clone(), contra]);
        d.finish_child(d.mk_lam(hr_id, BinderInfo::Default, right.clone(), body))
    };

    let rec = Expr::apps(
        c.or_rec.clone(),
        [left, right, or_motive, case_left, case_right, dich],
    );
    let val = b.mk_lam(ne_id, BinderInfo::Default, ne_ty, rec);
    let val = b.mk_lam(k_id, BinderInfo::Default, fin_pow.clone(), val);
    let val = b.mk_lam(j_id, BinderInfo::Default, fin_pow, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.prod_offdiag_eq_zero` — the off-diagonal collapse
    /// `j ≠ k ⇒ Fin.prod n (1 + pm(hcDecode j ·)·pm(hcDecode k ·)) = 0`.
    /// Kernel-checked, constructive. Idempotent.
    pub(crate) fn register_prod_offdiag_eq_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.prod_offdiag_eq_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?;
        self.init_rat()?;
        self.register_prod_factor_zero_or_pointwise_eq()?;
        // Nat order / pow monotonicity / testBit plumbing.
        self.register_nat_mul_left_cancel_succ_proof()?; // Nat.le_or_lt, Nat.le_trans
        self.init_nat_trans_lt_le_lt()?; // Nat.lt_of_lt_of_le
        self.register_nat_pow_le_pow_right_proof()?;
        self.register_nat_testbit_lt_pow_proof()?; // testBit_lt_pow (+ testBit_eq_false_of_ge)
        self.register_nat_eq_of_testbit_proof()?;
        self.register_fin_dec_eq_proof()?; // Fin.eq_of_val_eq

        let c = OffDiagWrapConsts::new();
        let oc = OffDiagConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: offdiag_zero_type(&c, &oc),
            value: offdiag_zero_value(&c, &oc),
        })
    }
}

// ===========================================================================
// BoolAnalysis.prod_diag_eq_cube — the DIAGONAL product value.
//
//   ∀ (n : Nat) (x : HCPoint n),
//     Fin.prod n (fun i => 1 + pm(x i)·pm(x i))
//       = Rat.mk (Int.ofNat (Nat.pow 2 n)) 1
//
// The companion of `prod_offdiag_eq_zero`: on the diagonal the Parseval product
// integrand collapses to the cube size `2^n`. Just `Eq.trans` of the two landed
// rungs: `prod_diag_eq_two` (Π (1+pm(x i)²) = Π (1+1)) then
// `prod_const_two_eq_pow` (Π (1+1) = 2^n/1). Kernel-checked, constructive.
// ===========================================================================

impl OffDiagConsts {
    /// `Rat.mk (Int.ofNat (Nat.pow 2 n)) 1` — the cube-size numeral `D(n)`.
    fn cube_size(&self, n: &Expr) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let two = Expr::app(self.nat_succ.clone(), one.clone());
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
    /// `fun (_ : Fin n) => Rat.one + Rat.one` — the constant-`2` factor function.
    fn const_two_fn(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, _i) = b.fresh_local(fin_n.clone());
        let body = self.add(self.rat_one.clone(), self.rat_one.clone());
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
}

fn prod_diag_cube_type(c: &OffDiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let lhs = c.prod(n.clone(), c.integrand(&b, &n, &x, &x));
    let concl = c.eq_rat(lhs, c.cube_size(&n));
    let r = b.mk_pi(x_id, BinderInfo::Default, hcp, concl);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

fn prod_diag_cube_value(c: &OffDiagConsts) -> Expr {
    let diag_two = Expr::const_(Name::from_string("BoolAnalysis.prod_diag_eq_two"), vec![]);
    let const_pow = Expr::const_(
        Name::from_string("BoolAnalysis.prod_const_two_eq_pow"),
        vec![],
    );
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());

    let diag = c.prod(n.clone(), c.integrand(&b, &n, &x, &x));
    let const2 = c.prod(n.clone(), c.const_two_fn(&b, &n));
    // leg1 : Fin.prod n (integrand x x) = Fin.prod n (const 2)   [prod_diag_eq_two n x]
    let leg1 = Expr::apps(diag_two, [n.clone(), x.clone()]);
    // leg2 : Fin.prod n (const 2) = 2^n/1   [prod_const_two_eq_pow n]
    let leg2 = Expr::app(const_pow, n.clone());
    let proof = c.trans_rat(diag, const2, c.cube_size(&n), leg1, leg2);

    let r = b.mk_lam(x_id, BinderInfo::Default, hcp, proof);
    let r = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

impl Environment {
    /// Register `BoolAnalysis.prod_diag_eq_cube` — the diagonal product value
    /// `Fin.prod n (1 + pm(x i)²) = 2^n/1`. Kernel-checked, constructive.
    /// Idempotent.
    pub(crate) fn register_prod_diag_eq_cube(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.prod_diag_eq_cube");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?;
        self.init_rat()?;
        self.register_fin_prod_diag_eq_two()?;
        self.register_prod_const_two_eq_pow()?;

        let c = OffDiagConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: prod_diag_cube_type(&c),
            value: prod_diag_cube_value(&c),
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
        env.register_prod_factor_zero_or_pointwise_eq()
            .expect("register_prod_factor_zero_or_pointwise_eq");
        env.register_prod_offdiag_eq_zero()
            .expect("register_prod_offdiag_eq_zero");
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
    fn test_prod_factor_zero_or_pointwise_eq_is_constructive_theorem() {
        let env = make_env();
        check_constructive(&env, "BoolAnalysis.prod_factor_zero_or_pointwise_eq");
    }

    #[test]
    fn test_prod_offdiag_eq_zero_is_constructive_theorem() {
        let env = make_env();
        check_constructive(&env, "BoolAnalysis.prod_offdiag_eq_zero");
    }

    #[test]
    fn test_prod_diag_eq_cube_is_constructive_theorem() {
        let mut env = make_env();
        env.register_prod_diag_eq_cube()
            .expect("register_prod_diag_eq_cube");
        check_constructive(&env, "BoolAnalysis.prod_diag_eq_cube");
    }

    #[test]
    fn test_register_idempotent() {
        let mut env = make_env();
        env.register_prod_factor_zero_or_pointwise_eq()
            .expect("idempotent re-register");
        env.register_prod_offdiag_eq_zero()
            .expect("idempotent re-register");
    }
}
