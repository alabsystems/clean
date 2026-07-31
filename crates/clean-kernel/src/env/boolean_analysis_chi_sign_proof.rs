// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SIGN-side character orthonormality — the dual of `subsetSum_chi_bilinear`.
//!
//! The gate-side delta `subsetSum_chi_bilinear` sums over the GATE index `S`:
//!   `Σ_S χ_S(x)·χ_S(y) = Π_i (1 + pm(x_i)·pm(y_i))`.
//! The x-side Parseval core needs the SIGN-side dual: with the gates `S, T`
//! fixed, sum the character product over the SIGN cube point `x`:
//!   `Σ_x χ_S(x)·χ_T(x) = Π_i (1 + pm(S_i)·pm(T_i))`.
//! Both collapse to the SAME product form, so the diagonal value (`2^n`) and the
//! off-diagonal vanishing (`= 0` when `S ≠ T`) are then read off by the EXISTING
//! `prod_diag_eq_cube` / `prod_offdiag_eq_zero` Kronecker collapse — no new
//! product machinery.
//!
//! This module lands the self-contained, axiom-free per-coordinate LEAF of that
//! dual: the sign-side pair sum
//!
//!   `BoolAnalysis.chi_sign_factor_pair_sum : ∀ (s t : Bool),
//!      cf(s,false)·cf(t,false) + cf(s,true)·cf(t,true) = 1 + pm(s)·pm(t)`
//!
//! where `cf(g,b) := @Bool.rec (fun _ => Rat) 1 (1 - 2·⟦b⟧) g` is the per-
//! coordinate character factor (the gate `g` selects `1` vs the signed value).
//! This is the dual of `chi_factor_pair_sum` (which sums the GATE slot of `cf`);
//! here we sum the SIGN slot. Unlike the gate-side, `cf(s,false)` is NOT def-eq
//! to a constant, so we decide both `s` and `t` with a 2×2 `Bool.rec`: each of
//! the four leaves is a CLOSED Rat-numeral identity (`2 = 2`, `2 = 2`, `0 = 0`,
//! `0 = 0`) closed by `@Eq.refl Rat <LHS>` (native Rat reducers normalize both
//! sides to the same `Rat.mk` numeral), exactly as in `disagree_sq_bridge`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for the sign-side per-coordinate combine.
struct SignConsts {
    rat: Expr,
    bool_: Expr,
    btrue: Expr,
    bfalse: Expr,
    rat_one: Expr,
    rat_zero: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    rat_add: Expr,
    rat_two: Expr,
    pm: Expr,
    bool_rec1: Expr,
    bool_rec0: Expr,
    eq1: Expr,
    eq_refl1: Expr,
}

impl SignConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_one = Expr::app(nat_succ.clone(), nat_zero);
        let two = Expr::app(nat_succ.clone(), nat_one.clone());
        // `Rat.mk (Int.ofNat 2) 1` — the rational 2, matching chi's body.
        let rat_two = Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [
                Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), two),
                nat_one,
            ],
        );
        Self {
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            btrue: Expr::const_(Name::from_string("Bool.true"), vec![]),
            bfalse: Expr::const_(Name::from_string("Bool.false"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_two,
            pm: Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]),
            bool_rec1: Expr::const_(Name::from_string("Bool.rec"), vec![type1.clone()]),
            bool_rec0: Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![type1]),
        }
    }

    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn refl_rat(&self, e: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.rat.clone(), e])
    }

    /// `fun (_ : Bool) => Rat` — the Type-valued motive for `cf`'s `Bool.rec`.
    fn bool_to_rat_motive(&self, parent: &EnvDeclBuilder) -> Expr {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, _t) = mb.fresh_local(self.bool_.clone());
        let lam = mb.mk_lam(
            t_id,
            BinderInfo::Default,
            self.bool_.clone(),
            self.rat.clone(),
        );
        mb.finish_child(lam)
    }

    /// `cf sb xb = @Bool.rec (fun _ => Rat) Rat.one (1 - 2·⟦xb⟧) sb`,
    /// byte-for-byte the per-coordinate factor `register_chi` / `chi_succ` build.
    fn factor(&self, parent: &EnvDeclBuilder, sb: Expr, xb: Expr) -> Expr {
        let embed = Expr::apps(
            self.bool_rec1.clone(),
            [
                self.bool_to_rat_motive(parent),
                self.rat_zero.clone(),
                self.rat_one.clone(),
                xb,
            ],
        );
        let two_embed = Expr::apps(self.rat_mul.clone(), [self.rat_two.clone(), embed]);
        let signed = Expr::apps(self.rat_sub.clone(), [self.rat_one.clone(), two_embed]);
        Expr::apps(
            self.bool_rec1.clone(),
            [
                self.bool_to_rat_motive(parent),
                self.rat_one.clone(),
                signed,
                sb,
            ],
        )
    }

    /// LHS at `(s,t)`: `cf(s,false)·cf(t,false) + cf(s,true)·cf(t,true)`.
    fn lhs(&self, parent: &EnvDeclBuilder, s: Expr, t: Expr) -> Expr {
        let low = self.mul(
            self.factor(parent, s.clone(), self.bfalse.clone()),
            self.factor(parent, t.clone(), self.bfalse.clone()),
        );
        let high = self.mul(
            self.factor(parent, s, self.btrue.clone()),
            self.factor(parent, t, self.btrue.clone()),
        );
        self.add(low, high)
    }
    /// RHS at `(s,t)`: `1 + pm(s)·pm(t)`.
    fn rhs(&self, s: Expr, t: Expr) -> Expr {
        let pm_s = Expr::app(self.pm.clone(), s);
        let pm_t = Expr::app(self.pm.clone(), t);
        self.add(self.rat_one.clone(), self.mul(pm_s, pm_t))
    }

    // ── helpers shared by the sign-side coordinate peel (`chi_sign_pair_succ`) ──

    fn nat(&self) -> Expr {
        Expr::const_(Name::from_string("Nat"), vec![])
    }
    fn chi(&self) -> Expr {
        Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![])
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            n.clone(),
        )
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), n.clone())
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            n.clone(),
        )
    }
    fn last(&self, n: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Fin.last"), vec![]),
            n.clone(),
        )
    }
    /// `fun (i : Fin n) => p (Fin.castSucc n i)` — restrict to first `n` coords.
    fn restrict(&self, parent: &EnvDeclBuilder, n: &Expr, p: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let cs = Expr::apps(
            Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            [n.clone(), i],
        );
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, Expr::app(p.clone(), cs)))
    }
    /// `chi (k+1) S x`.
    fn chi_sn(&self, k: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi(), [self.succ(k), s.clone(), x.clone()])
    }
    /// `chi_succ k S x : chi (k+1) S x = chi k (restrict S)(restrict x) · factor(S last)(x last)`.
    fn chi_succ(&self, k: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.chi_succ"), vec![]),
            [k.clone(), s.clone(), x.clone()],
        )
    }
    /// RHS of chi_succ: `chi k (restrict S)(restrict x) · factor(S last)(x last)`.
    fn chi_succ_rhs(&self, parent: &EnvDeclBuilder, k: &Expr, s: &Expr, x: &Expr) -> Expr {
        let rs = self.restrict(parent, k, s);
        let rx = self.restrict(parent, k, x);
        let chi_pre = Expr::apps(self.chi(), [k.clone(), rs, rx]);
        let s_last = Expr::app(s.clone(), self.last(k));
        let x_last = Expr::app(x.clone(), self.last(k));
        let top = self.factor(parent, s_last, x_last);
        self.mul(chi_pre, top)
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        let eq_trans = Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        );
        Expr::apps(eq_trans, [self.rat.clone(), a, b, cc, h1, h2])
    }
    /// `congrArg Rat Rat from to motive h : motive from = motive to`.
    fn congr_rat(&self, from: Expr, to: Expr, motive: Expr, h: Expr) -> Expr {
        let congr_arg = Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        );
        Expr::apps(
            congr_arg,
            [self.rat.clone(), self.rat.clone(), from, to, motive, h],
        )
    }
    /// `fun (z : Rat) => Rat.mul a z`.
    fn mul_left_motive(&self, parent: &EnvDeclBuilder, a: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(self.rat.clone());
        let body = self.mul(a.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }
}

fn build_sign_pair_sum_type(c: &SignConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (s_id, s) = b.fresh_local(c.bool_.clone());
    let (t_id, t) = b.fresh_local(c.bool_.clone());
    let concl = c.eq_rat(c.lhs(&b, s.clone(), t.clone()), c.rhs(s.clone(), t.clone()));
    let ty = b.mk_pi(t_id, BinderInfo::Default, c.bool_.clone(), concl);
    let ty = b.mk_pi(s_id, BinderInfo::Default, c.bool_.clone(), ty);
    b.finish(ty)
}

fn build_sign_pair_sum_value(c: &SignConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (s_id, s) = b.fresh_local(c.bool_.clone());
    let (t_id, t) = b.fresh_local(c.bool_.clone());

    // motive_s : fun (s' : Bool) => lhs(s',t) = rhs(s',t)
    let motive_s = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (sp_id, sp) = d.fresh_local(c.bool_.clone());
        let body = c.eq_rat(
            c.lhs(&d, sp.clone(), t.clone()),
            c.rhs(sp.clone(), t.clone()),
        );
        d.finish_child(d.mk_lam(sp_id, BinderInfo::Default, c.bool_.clone(), body))
    };

    // For a fixed concrete `sv`, split on `t` and emit Eq.refl leaves
    // (each leaf lhs(sv,tv) ≡ rhs(sv,tv) by ground Rat reduction).
    let inner_rec = |sv: Expr, parent: &EnvDeclBuilder| {
        let d = EnvDeclBuilder::child_of(parent);
        // motive_t : fun (t' : Bool) => lhs(sv,t') = rhs(sv,t')
        let motive_t = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (tp_id, tp) = e.fresh_local(c.bool_.clone());
            let body = c.eq_rat(
                c.lhs(&e, sv.clone(), tp.clone()),
                c.rhs(sv.clone(), tp.clone()),
            );
            e.finish_child(e.mk_lam(tp_id, BinderInfo::Default, c.bool_.clone(), body))
        };
        let leaf = |tv: Expr| c.refl_rat(c.lhs(&d, sv.clone(), tv));
        let t_false = leaf(c.bfalse.clone());
        let t_true = leaf(c.btrue.clone());
        let e = Expr::apps(c.bool_rec0.clone(), [motive_t, t_false, t_true, t.clone()]);
        d.finish_child(e)
    };

    let s_false_case = inner_rec(c.bfalse.clone(), &b);
    let s_true_case = inner_rec(c.btrue.clone(), &b);

    let rec_s = Expr::apps(
        c.bool_rec0.clone(),
        [motive_s, s_false_case, s_true_case, s.clone()],
    );
    let val = b.mk_lam(t_id, BinderInfo::Default, c.bool_.clone(), rec_s);
    let val = b.mk_lam(s_id, BinderInfo::Default, c.bool_.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.chi_sign_factor_pair_sum`: the SIGN-side per-
    /// coordinate pair sum
    /// `cf(s,false)·cf(t,false) + cf(s,true)·cf(t,true) = 1 + pm(s)·pm(t)`,
    /// for all `s t : Bool`. The dual of `chi_factor_pair_sum` (which sums the
    /// gate slot); here we sum the SIGN slot of the character factor `cf`.
    ///
    /// `Bool.rec` on `s` then `t` (four leaves). Each leaf is a closed Rat
    /// identity that ground-reduces (`pm` and `cf` reduce on concrete bools,
    /// native Rat reducers normalize both sides to the same `Rat.mk` numeral),
    /// closed by `@Eq.refl Rat <LHS>`. Constructive, empty admitted-axiom
    /// closure. Idempotent.
    pub(crate) fn register_chi_sign_factor_pair_sum_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_sign_factor_pair_sum");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        // `pm` is registered by `register_boolfn_embeddings` inside
        // `init_boolean_analysis`. Callers wire this theorem in after that.
        self.init_boolean_analysis()?;

        // Re-entrancy guard: `init_boolean_analysis` may register this name.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = SignConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_sign_pair_sum_type(&c),
            value: build_sign_pair_sum_value(&c),
        })
    }
}

// ===========================================================================
// chi_sign_pair_succ — the SIGN-side bilinear coordinate peel.
//
//   ∀ (k) (S T x : HCPoint (k+1)),
//     chi (k+1) S x · chi (k+1) T x
//       = (chi k (restrict S)(restrict x) · chi k (restrict T)(restrict x))
//         · (cf(S last)(x last) · cf(T last)(x last))
//
// Dual of `chi_pair_succ`: there the GATE `S` is shared and the two SIGNS `x,y`
// vary; here the SIGN `x` is shared and the two GATES `S,T` vary. `chi_succ`
// peels each character into its k-cube restriction times the top factor;
// `Rat.mul_mul_mul_comm` regroups the four atoms into the (prefix·prefix)·(top·top)
// grouping. Kernel-checked, constructive (closure ⊆ {chi_succ, Rat.mul_mul_mul_comm}
// ∪ Eq built-ins).
// ===========================================================================

fn build_sign_pair_succ_type(c: &SignConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat());
    let sn = c.succ(&k);
    let hcp = c.hcpoint_of(&sn);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (t_id, t) = b.fresh_local(hcp.clone());
    let (x_id, x) = b.fresh_local(hcp.clone());

    // LHS: chi (k+1) S x · chi (k+1) T x
    let lhs = c.mul(c.chi_sn(&k, &s, &x), c.chi_sn(&k, &t, &x));

    // RHS: (chi k rS rx · chi k rT rx) · (cf(S last)(x last) · cf(T last)(x last))
    let rs = c.restrict(&b, &k, &s);
    let rt = c.restrict(&b, &k, &t);
    let rx = c.restrict(&b, &k, &x);
    let chi_s_pre = Expr::apps(c.chi(), [k.clone(), rs, rx.clone()]);
    let chi_t_pre = Expr::apps(c.chi(), [k.clone(), rt, rx]);
    let s_last = Expr::app(s.clone(), c.last(&k));
    let t_last = Expr::app(t.clone(), c.last(&k));
    let x_last = Expr::app(x.clone(), c.last(&k));
    let cf_s = c.factor(&b, s_last, x_last.clone());
    let cf_t = c.factor(&b, t_last, x_last);
    let rhs = c.mul(c.mul(chi_s_pre, chi_t_pre), c.mul(cf_s, cf_t));

    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(x_id, BinderInfo::Default, hcp.clone(), concl);
    let ty = b.mk_pi(t_id, BinderInfo::Default, hcp.clone(), ty);
    let ty = b.mk_pi(s_id, BinderInfo::Default, hcp, ty);
    let ty = b.mk_pi(k_id, BinderInfo::Default, c.nat(), ty);
    b.finish(ty)
}

fn build_sign_pair_succ_value(c: &SignConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat());
    let sn = c.succ(&k);
    let hcp = c.hcpoint_of(&sn);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (t_id, t) = b.fresh_local(hcp.clone());
    let (x_id, x) = b.fresh_local(hcp.clone());

    // A·p := chi_succ rhs for (S,x);  B·q := chi_succ rhs for (T,x).
    let ap = c.chi_succ_rhs(&b, &k, &s, &x);
    let bq = c.chi_succ_rhs(&b, &k, &t, &x);
    let chi_s = c.chi_sn(&k, &s, &x);
    let chi_t = c.chi_sn(&k, &t, &x);

    // e0 := chi_s · chi_t
    let e0 = c.mul(chi_s.clone(), chi_t.clone());
    // e1 := (A·p) · chi_t      congr (·chi_t) (chi_succ k S x)
    let e1 = c.mul(ap.clone(), chi_t.clone());
    let mul_right_chi_t = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.mul(z, chi_t.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let leg1 = c.congr_rat(
        chi_s.clone(),
        ap.clone(),
        mul_right_chi_t,
        c.chi_succ(&k, &s, &x),
    );
    // e2 := (A·p) · (B·q)      congr ((A·p)·) (chi_succ k T x)
    let e2 = c.mul(ap.clone(), bq.clone());
    let leg2 = c.congr_rat(
        chi_t.clone(),
        bq.clone(),
        c.mul_left_motive(&b, &ap),
        c.chi_succ(&k, &t, &x),
    );
    // e3 := (A·B) · (p·q)      Rat.mul_mul_mul_comm A p B q
    let rs = c.restrict(&b, &k, &s);
    let rt = c.restrict(&b, &k, &t);
    let rx = c.restrict(&b, &k, &x);
    let a_atom = Expr::apps(c.chi(), [k.clone(), rs, rx.clone()]);
    let b_atom = Expr::apps(c.chi(), [k.clone(), rt, rx]);
    let s_last = Expr::app(s.clone(), c.last(&k));
    let t_last = Expr::app(t.clone(), c.last(&k));
    let x_last = Expr::app(x.clone(), c.last(&k));
    let p_atom = c.factor(&b, s_last, x_last.clone());
    let q_atom = c.factor(&b, t_last, x_last);
    let e3 = c.mul(
        c.mul(a_atom.clone(), b_atom.clone()),
        c.mul(p_atom.clone(), q_atom.clone()),
    );
    let leg3 = Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
        [a_atom, p_atom, b_atom, q_atom],
    );

    // Chain: e0 = e1 = e2 = e3.
    let t1 = c.trans_rat(e0.clone(), e1.clone(), e2.clone(), leg1, leg2);
    let proof = c.trans_rat(e0, e2, e3, t1, leg3);

    let val = b.mk_lam(x_id, BinderInfo::Default, hcp.clone(), proof);
    let val = b.mk_lam(t_id, BinderInfo::Default, hcp.clone(), val);
    let val = b.mk_lam(s_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(k_id, BinderInfo::Default, c.nat(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.chi_sign_pair_succ`: the SIGN-side bilinear
    /// coordinate peel
    /// `χ_S(x)·χ_T(x) = (χ_k(rS)(rx)·χ_k(rT)(rx))·(cf(S last)(x last)·cf(T last)(x last))`.
    /// Dual of `chi_pair_succ` (shared gate / varying signs); here the sign `x`
    /// is shared and the gates `S,T` vary. `chi_succ` peels each character into
    /// its k-cube restriction times the top factor, `Rat.mul_mul_mul_comm`
    /// regroups. Kernel-checked, constructive (closure ⊆ {`chi_succ`,
    /// `Rat.mul_mul_mul_comm`} ∪ Eq built-ins). Idempotent.
    pub(crate) fn register_chi_sign_pair_succ_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_sign_pair_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_chi_succ_theorem()?;
        self.register_rat_mul_mul_mul_comm_theorem()?;

        let c = SignConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_sign_pair_succ_type(&c),
            value: build_sign_pair_succ_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_chi_sign_factor_pair_sum_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_chi_sign_factor_pair_sum_theorem()
            .expect("register_chi_sign_factor_pair_sum_theorem");
        env.register_chi_sign_factor_pair_sum_theorem()
            .expect("idempotent");
        let name = Name::from_string("BoolAnalysis.chi_sign_factor_pair_sum");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("proof"), &info.type_)
            .expect("chi_sign_factor_pair_sum must type-check");
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "chi_sign_factor_pair_sum must be axiom-free, got {:?}",
            env.axiom_deps(&name)
        );
        assert_eq!(
            env.proof_quality(&name).expect("quality"),
            ProofQuality::Constructive,
        );
    }

    #[test]
    fn test_chi_sign_pair_succ_is_constructive_theorem() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_chi_sign_pair_succ_theorem()
            .expect("register_chi_sign_pair_succ_theorem");
        env.register_chi_sign_pair_succ_theorem()
            .expect("idempotent");
        let name = Name::from_string("BoolAnalysis.chi_sign_pair_succ");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("proof"), &info.type_)
            .expect("chi_sign_pair_succ must type-check");
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "chi_sign_pair_succ must be axiom-free, got {:?}",
            env.axiom_deps(&name)
        );
        assert_eq!(
            env.proof_quality(&name).expect("quality"),
            ProofQuality::Constructive,
        );
    }
}
