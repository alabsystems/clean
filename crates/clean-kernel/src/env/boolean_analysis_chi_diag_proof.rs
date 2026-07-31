// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `BoolAnalysis.chi_mul_self` — the diagonal character
//! identity (the integrand of the self inner product `⟨χ_S, χ_S⟩`):
//!
//! `chi_mul_self : ∀ (n : Nat) (S x : HCPoint n), chi n S x * chi n S x = 1`
//!
//! Proof outline (no induction here beyond the landed `Fin.prod` lemmas):
//!   1. `chi_mul_chi n S S x` rewrites `χ_S(x)·χ_S(x)` into the single product
//!      `Fin.prod n (fun i => factor S x i · factor S x i)`.
//!   2. each per-coordinate factor is `±1`, so its square is `1`:
//!      `∀ i, factor S x i · factor S x i = 1` — a 2×2 `Bool.rec` case split on
//!      `S i` (gate) and `x i` (sign) where every closed leaf computes to `1`
//!      (`@Eq.refl Rat (factor·factor)`). `Fin.prod_congr` then rewrites the
//!      product to `Fin.prod n (fun _ => 1)`.
//!   3. `Fin.prod_const_one n` collapses that to `1`.
//!
//! Chaining 1→2→3 with `Eq.trans` gives `χ_S(x)·χ_S(x) = 1`.
//!
//! This is the per-point integrand of the diagonal orthonormality
//! `E_x[χ_S(x)²] = 1` (and, since `f̃ = pm∘f` is also `±1`, the same shape gives
//! `E[f̃²] = 1` for Boolean `f`). Kernel-checked, `ProofQuality::Constructive`
//! (closure ⊆ {`chi_mul_chi`, `Fin.prod_congr`, `Fin.prod_const_one`} ∪ Eq/Bool
//! built-ins — all axiom-free).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct ChiDiagConsts {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    bool_: Expr,
    rat_one: Expr,
    rat_zero: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    rat_two: Expr,
    fin_prod: Expr,
    bool_rec_rat: Expr,
    eq1: Expr,
    eq_refl: Expr,
    eq_trans: Expr,
}

impl ChiDiagConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_one = Expr::app(nat_succ.clone(), nat_zero);
        let two = Expr::app(nat_succ, nat_one.clone());
        let rat_two = Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [
                Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), two),
                nat_one,
            ],
        );
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            rat_two,
            fin_prod: Expr::const_(Name::from_string("Fin.prod"), vec![]),
            // `Bool.rec` for the Type-valued `chi` factor (universe 1).
            bool_rec_rat: Expr::const_(Name::from_string("Bool.rec"), vec![type1.clone()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            n.clone(),
        )
    }
    fn chi(&self, n: Expr, s: Expr, x: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            [n, s, x],
        )
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn prod(&self, n: Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_prod.clone(), [n, g])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn eq_trans_rat(&self, a: Expr, b: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, d, h1, h2])
    }

    /// `fun (_ : Bool) => Rat` — the Type-valued motive for `chi`'s `Bool.rec`.
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

    /// The per-coordinate gated factor for a GIVEN gate Bool `sb` and sign-arg
    /// Bool `xb` (both arbitrary expressions):
    /// `@Bool.rec (fun _ => Rat) Rat.one`
    /// `  (1 - 2·(@Bool.rec (fun _ => Rat) 0 1 xb)) sb`.
    fn factor(&self, parent: &EnvDeclBuilder, sb: Expr, xb: Expr) -> Expr {
        let embed = Expr::apps(
            self.bool_rec_rat.clone(),
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
            self.bool_rec_rat.clone(),
            [
                self.bool_to_rat_motive(parent),
                self.rat_one.clone(),
                signed,
                sb,
            ],
        )
    }

    /// The `chi` factor function `factor S x` as a `Fin n → Rat` lambda
    /// (byte-for-byte `register_chi`'s inner factor), so `Fin.prod n (this)` is
    /// def-eq to `chi n S x`.
    fn factor_fn(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let s_i = Expr::app(s.clone(), i.clone());
        let x_i = Expr::app(x.clone(), i.clone());
        let gated = self.factor(&b, s_i, x_i);
        let lam = b.mk_lam(i_id, BinderInfo::Default, fin_n, gated);
        b.finish_child(lam)
    }
}

/// `fun (i : Fin n) => factor S x i · factor S x i` — the pointwise square,
/// exactly the shape `chi_mul_chi n S S x` produces on its RHS.
fn pointwise_sq_fn(
    c: &ChiDiagConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    s: &Expr,
    x: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let fs = c.factor_fn(&b, n, s, x);
    let ft = c.factor_fn(&b, n, s, x);
    let body = c.mul(Expr::app(fs, i.clone()), Expr::app(ft, i));
    let lam = b.mk_lam(i_id, BinderInfo::Default, fin_n, body);
    b.finish_child(lam)
}

/// Per-coordinate `factor S x i · factor S x i = 1`, as a function of `i`:
/// `fun (i : Fin n) => <2×2 Bool.rec on (S i, x i), every leaf @Eq.refl>`.
///
/// This is the hypothesis `Fin.prod_congr` consumes. Built by nesting `Bool.rec`
/// at the Prop level (universe 0): outer on `S i`, and in the gate-true branch a
/// further `Bool.rec` on `x i`; each of the (≤3 distinct) closed leaves has the
/// squared factor reduce to the closed Rat `1`, closed by `@Eq.refl Rat (sq)`.
fn pointwise_sq_eq_one(
    c: &ChiDiagConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    s: &Expr,
    x: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (i_id, i) = b.fresh_local(fin_n.clone());

    let s_i = Expr::app(s.clone(), i.clone());
    let x_i = Expr::app(x.clone(), i.clone());

    let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
    let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
    // Prop-level Bool.rec (motive lands in Sort 0).
    let bool_rec_prop = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);

    // The proposition `factor sb xb · factor sb xb = 1`, for given gate/sign
    // Bools.
    let goal = |c: &ChiDiagConsts, parent: &EnvDeclBuilder, sb: Expr, xb: Expr| {
        let f = c.factor(parent, sb, xb);
        c.eq_rat(c.mul(f.clone(), f), c.rat_one.clone())
    };
    let leaf = |c: &ChiDiagConsts, parent: &EnvDeclBuilder, sb: Expr, xb: Expr| {
        let f = c.factor(parent, sb, xb);
        Expr::apps(c.eq_refl.clone(), [c.rat.clone(), c.mul(f.clone(), f)])
    };

    // Inner split on `x i` (only needed in the gate-true branch, but we build a
    // generic helper splitting on `x i` for a fixed gate Bool `sb`).
    let split_on_x = |c: &ChiDiagConsts, parent: &EnvDeclBuilder, sb: Expr| {
        let d = EnvDeclBuilder::child_of(parent);
        // motive_x : fun (xb : Bool) => factor sb xb · factor sb xb = 1
        let motive_x = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (xp_id, xp) = e.fresh_local(c.bool_.clone());
            e.finish_child(e.mk_lam(
                xp_id,
                BinderInfo::Default,
                c.bool_.clone(),
                goal(c, &e, sb.clone(), xp),
            ))
        };
        let x_false = leaf(c, &d, sb.clone(), bfalse.clone());
        let x_true = leaf(c, &d, sb.clone(), btrue.clone());
        let rec = Expr::apps(
            bool_rec_prop.clone(),
            [motive_x, x_false, x_true, x_i.clone()],
        );
        d.finish_child(rec)
    };

    // Outer split on `S i`.
    // motive_s : fun (sb : Bool) => factor sb (x i) · factor sb (x i) = 1
    let motive_s = {
        let mut e = EnvDeclBuilder::child_of(&b);
        let (sp_id, sp) = e.fresh_local(c.bool_.clone());
        e.finish_child(e.mk_lam(
            sp_id,
            BinderInfo::Default,
            c.bool_.clone(),
            goal(c, &e, sp, x_i.clone()),
        ))
    };
    // gate-false branch: factor false (x i) = 1, so 1·1 = 1 — but `x i` is still
    // symbolic; the leaf `@Eq.refl Rat (1·1)` works because the gate reduces the
    // factor to `1` independent of `x i`.
    let s_false = leaf(c, &b, bfalse.clone(), x_i.clone());
    // gate-true branch: factor = signed(x i); split on `x i`.
    let s_true = split_on_x(c, &b, btrue.clone());

    let rec = Expr::apps(bool_rec_prop.clone(), [motive_s, s_false, s_true, s_i]);
    let lam = b.mk_lam(i_id, BinderInfo::Default, fin_n, rec);
    b.finish_child(lam)
}

fn build_type(c: &ChiDiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (x_id, x) = b.fresh_local(hcp.clone());
    let chi_sx = c.chi(n.clone(), s.clone(), x.clone());
    let concl = c.eq_rat(c.mul(chi_sx.clone(), chi_sx), c.rat_one.clone());
    let ty = b.mk_pi(x_id, BinderInfo::Default, hcp.clone(), concl);
    let ty = b.mk_pi(s_id, BinderInfo::Default, hcp, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    b.finish(ty)
}

fn build_value(c: &ChiDiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (x_id, x) = b.fresh_local(hcp.clone());

    let chi_sx = c.chi(n.clone(), s.clone(), x.clone());
    let lhs = c.mul(chi_sx.clone(), chi_sx);

    // step1: chi·chi = Fin.prod n (fun i => factor·factor)
    //   = chi_mul_chi n S S x
    let prod_sq = c.prod(n.clone(), pointwise_sq_fn(c, &b, &n, &s, &x));
    let chi_mul_chi = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.chi_mul_chi"), vec![]),
        [n.clone(), s.clone(), s.clone(), x.clone()],
    );

    // step2: Fin.prod n (fun i => factor·factor) = Fin.prod n (fun _ => 1)
    //   = Fin.prod_congr n (sq_fn) (const_one_fn) (pointwise_sq_eq_one)
    let const_one_fn = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, _i) = d.fresh_local(fin_n.clone());
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, c.rat_one.clone()))
    };
    let prod_const_one = c.prod(n.clone(), const_one_fn.clone());
    let prod_congr = Expr::apps(
        Expr::const_(Name::from_string("Fin.prod_congr"), vec![]),
        [
            n.clone(),
            pointwise_sq_fn(c, &b, &n, &s, &x),
            const_one_fn,
            pointwise_sq_eq_one(c, &b, &n, &s, &x),
        ],
    );

    // step3: Fin.prod n (fun _ => 1) = 1  = Fin.prod_const_one n
    let prod_const_one_thm = Expr::app(
        Expr::const_(Name::from_string("Fin.prod_const_one"), vec![]),
        n.clone(),
    );

    // chain: lhs = prod_sq = prod_const_one = 1
    let chain12 = c.eq_trans_rat(
        lhs.clone(),
        prod_sq.clone(),
        prod_const_one.clone(),
        chi_mul_chi,
        prod_congr,
    );
    let proof = c.eq_trans_rat(
        lhs,
        prod_const_one,
        c.rat_one.clone(),
        chain12,
        prod_const_one_thm,
    );

    let val = b.mk_lam(x_id, BinderInfo::Default, hcp.clone(), proof);
    let val = b.mk_lam(s_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

// ── chi_self_inner_eq_expect_one : E[χ_S²] = E[1] ──

/// `BoolAnalysis.Expect n g`.
fn expect_of(n: Expr, g: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.Expect"), vec![]),
        [n, g],
    )
}

/// `fun (x : HCPoint n) => chi n S x · chi n S x` — the self-inner-product
/// integrand.
fn chi_sq_integrand(c: &ChiDiagConsts, parent: &EnvDeclBuilder, n: &Expr, s: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let chi_sx = c.chi(n.clone(), s.clone(), x);
    let body = c.mul(chi_sx.clone(), chi_sx);
    let lam = b.mk_lam(x_id, BinderInfo::Default, hcp, body);
    b.finish_child(lam)
}

/// `fun (_ : HCPoint n) => Rat.one`.
fn const_one_integrand(c: &ChiDiagConsts, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (x_id, _x) = b.fresh_local(hcp.clone());
    let lam = b.mk_lam(x_id, BinderInfo::Default, hcp, c.rat_one.clone());
    b.finish_child(lam)
}

fn self_inner_type(c: &ChiDiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let lhs = expect_of(n.clone(), chi_sq_integrand(c, &b, &n, &s));
    let rhs = expect_of(n.clone(), const_one_integrand(c, &b, &n));
    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(s_id, BinderInfo::Default, hcp, concl);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    b.finish(ty)
}

fn self_inner_value(c: &ChiDiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());

    // pointwise hyp: fun (x : HCPoint n) => chi_mul_self n S x
    //   : chi n S x · chi n S x = 1
    let pointwise = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let body = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.chi_mul_self"), vec![]),
            [n.clone(), s.clone(), x],
        );
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
    };

    // Expect_congr n (chi_sq_integrand) (const_one_integrand) pointwise
    //   : Expect n (chi_sq) = Expect n (const 1)
    let proof = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.Expect_congr"), vec![]),
        [
            n.clone(),
            chi_sq_integrand(c, &b, &n, &s),
            const_one_integrand(c, &b, &n),
            pointwise,
        ],
    );

    let val = b.mk_lam(s_id, BinderInfo::Default, hcp, proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.chi_self_inner_eq_expect_one` as a kernel-checked,
    /// constructive theorem:
    ///
    /// `∀ n S, Expect n (fun x => chi n S x * chi n S x) = Expect n (fun _ => 1)`.
    ///
    /// The self inner product `⟨χ_S, χ_S⟩` averages identically to the constant
    /// `1`, by `Expect_congr` over the proven per-point `chi_mul_self`. The final
    /// `= 1` is then the single normalization fact `Expect n (fun _ => 1) = 1`.
    /// Idempotent.
    pub(crate) fn register_chi_self_inner_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_self_inner_eq_expect_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?;
        self.register_chi_mul_self_theorem()?;
        self.register_expect_congr_theorem()?;

        let c = ChiDiagConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: self_inner_type(&c),
            value: self_inner_value(&c),
        })
    }

    /// Register `BoolAnalysis.chi_mul_self : ∀ n S x, chi n S x * chi n S x = 1`
    /// as a kernel-checked, constructive theorem. Idempotent.
    pub(crate) fn register_chi_mul_self_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_mul_self");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?;
        self.register_chi_mul_chi_theorem()?;
        self.register_fin_prod_one_theorems()?;

        let c = ChiDiagConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_type(&c),
            value: build_value(&c),
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
        env
    }

    /// `chi_mul_self` is a genuine kernel-checked, `Constructive`
    /// `Declaration::Theorem` (empty admitted-axiom closure), and its proof term
    /// re-checks under C1.
    #[test]
    fn test_chi_mul_self_is_constructive_theorem() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.chi_mul_self"))
            .expect("chi_mul_self should be registered by init_boolean_analysis");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "chi_mul_self must be a kernel-checked Theorem, not an Axiom"
        );
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("chi_mul_self proof must check against its declared type");

        assert_eq!(
            env.proof_quality(&Name::from_string("BoolAnalysis.chi_mul_self")),
            Some(ProofQuality::Constructive),
            "chi_mul_self must be Constructive"
        );
        assert!(
            env.axiom_deps(&Name::from_string("BoolAnalysis.chi_mul_self"))
                .expect("deps")
                .is_empty(),
            "chi_mul_self's transitive axiom closure must be empty"
        );
    }

    /// `chi_self_inner_eq_expect_one` is a genuine kernel-checked, `Constructive`
    /// `Declaration::Theorem` (empty admitted-axiom closure): the diagonal self
    /// inner product `E[χ_S²]` averages identically to `E[1]`.
    #[test]
    fn test_chi_self_inner_is_constructive_theorem() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "BoolAnalysis.chi_self_inner_eq_expect_one",
            ))
            .expect("chi_self_inner_eq_expect_one should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "chi_self_inner_eq_expect_one must be a kernel-checked Theorem"
        );
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("chi_self_inner_eq_expect_one proof must check against its type");
        assert_eq!(
            env.proof_quality(&Name::from_string(
                "BoolAnalysis.chi_self_inner_eq_expect_one"
            )),
            Some(ProofQuality::Constructive),
            "chi_self_inner_eq_expect_one must be Constructive"
        );
        assert!(
            env.axiom_deps(&Name::from_string(
                "BoolAnalysis.chi_self_inner_eq_expect_one"
            ))
            .expect("deps")
            .is_empty(),
            "chi_self_inner_eq_expect_one's transitive axiom closure must be empty"
        );
    }
}
