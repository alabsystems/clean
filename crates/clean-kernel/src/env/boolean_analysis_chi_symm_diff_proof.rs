// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `BoolAnalysis.chi_mul_chi_symmDiff` — the character
//! product merges into the character of the symmetric difference:
//!
//! ```text
//! chi_mul_chi_symmDiff : ∀ (n : Nat) (S T x : HCPoint n),
//!   Rat.mul (chi n S x) (chi n T x)
//!     = chi n (fun i => Bool.xor (S i) (T i)) x
//! ```
//!
//! This is the group law of the parity characters (`χ_S·χ_T = χ_{S Δ T}`,
//! O'Donnell §1.4) — the rung that reduces EVERY off-diagonal inner product
//! `E[χ_S·χ_T]` (`S ≠ T`) to a single-character average `E[χ_U]` with
//! `U = S Δ T` nonempty, which the cube-split induction then cancels to `0`.
//! Together with the landed diagonal `chi_self_inner_eq_one` this is the full
//! orthonormality skeleton.
//!
//! Proof route:
//! 1. `chi_mul_chi n S T x` rewrites `χ_S·χ_T` into the single cube product
//!    `Fin.prod n (fun i => factor (S i) (x i) · factor (T i) (x i))`.
//! 2. Per coordinate, `factor sb xb · factor tb xb = factor (xor sb tb) xb` by
//!    a 2×2 `Bool.rec` split on `(S i, T i)`:
//!      - `S i = false`: `1·f = f` — `Rat.one_mul` (`xor false t ≡ t`).
//!      - `S i = true, T i = false`: `f·1 = f` — `Rat.mul_one` (`xor true false ≡ true`).
//!      - `S i = true, T i = true`: `signed²  = 1` — an inner `Bool.rec` on
//!        `x i` whose two closed leaves ground-reduce (`(+1)² ≡ 1`, `(-1)² ≡ 1`),
//!        each closed by `@Eq.refl Rat` (`xor true true ≡ false`, so the RHS
//!        factor is gated off to `1`).
//!
//!    `Fin.prod_congr` lifts the pointwise identity to the products.
//! 3. The congruent product `Fin.prod n (fun i => factor (xor (S i) (T i)) (x i))`
//!    IS `chi n (fun i => xor (S i) (T i)) x` by δβ (chi is a reducible
//!    Definition), so an `Eq.trans` of 1 and 2 closes the goal.
//!
//! Kernel-checked, `ProofQuality::Constructive` (closure ⊆ {`chi_mul_chi`,
//! `Fin.prod_congr`, `Rat.one_mul`, `Rat.mul_one`} ∪ Bool/Eq built-ins — all
//! axiom-free).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct ChiSymmDiffConsts {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    bool_: Expr,
    btrue: Expr,
    bfalse: Expr,
    bool_xor: Expr,
    rat_one: Expr,
    rat_zero: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    rat_two: Expr,
    fin_prod: Expr,
    bool_rec_rat: Expr,  // Bool.rec.{1} — Type-valued (the chi factor).
    bool_rec_prop: Expr, // Bool.rec.{0} — Prop-valued (the case splits).
    chi: Expr,
    chi_mul_chi: Expr,
    fin_prod_congr: Expr,
    rat_one_mul: Expr,
    rat_mul_one: Expr,
    eq1: Expr,
    eq_refl: Expr,
    eq_trans: Expr,
}

impl ChiSymmDiffConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_one = Expr::app(nat_succ.clone(), nat_zero);
        let two = Expr::app(nat_succ, nat_one.clone());
        // `Rat.mk (Int.ofNat 2) 1` — the rational 2, matching chi's body.
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
            btrue: Expr::const_(Name::from_string("Bool.true"), vec![]),
            bfalse: Expr::const_(Name::from_string("Bool.false"), vec![]),
            bool_xor: Expr::const_(Name::from_string("Bool.xor"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            rat_two,
            fin_prod: Expr::const_(Name::from_string("Fin.prod"), vec![]),
            bool_rec_rat: Expr::const_(Name::from_string("Bool.rec"), vec![type1.clone()]),
            bool_rec_prop: Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            chi: Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            chi_mul_chi: Expr::const_(Name::from_string("BoolAnalysis.chi_mul_chi"), vec![]),
            fin_prod_congr: Expr::const_(Name::from_string("Fin.prod_congr"), vec![]),
            rat_one_mul: Expr::const_(Name::from_string("Rat.one_mul"), vec![]),
            rat_mul_one: Expr::const_(Name::from_string("Rat.mul_one"), vec![]),
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
        Expr::apps(self.chi.clone(), [n, s, x])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn prod(&self, n: Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_prod.clone(), [n, g])
    }
    fn xor(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.bool_xor.clone(), [a, b])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn trans_rat(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, c, h1, h2])
    }

    /// `fun (_ : Bool) => Rat` — the Type-valued motive for chi's `Bool.rec`.
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

    /// `factor sb xb = @Bool.rec (fun _ => Rat) Rat.one (1 - 2·⟦xb⟧) sb`,
    /// byte-for-byte the per-coordinate factor `register_chi` builds.
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

    /// `fun (i : Fin n) => Bool.xor (S i) (T i)` — the symmetric-difference
    /// indicator.
    fn symm_diff_fn(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.xor(Expr::app(s.clone(), i.clone()), Expr::app(t.clone(), i));
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }

    /// `fun (i : Fin n) => factor (S i) (x i) · factor (T i) (x i)` — the
    /// pointwise factor product (the β-reduced form of `chi_mul_chi`'s RHS
    /// integrand).
    fn pointwise_mul_fn(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        s: &Expr,
        t: &Expr,
        x: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let x_i = Expr::app(x.clone(), i.clone());
        let fs = self.factor(&b, Expr::app(s.clone(), i.clone()), x_i.clone());
        let ft = self.factor(&b, Expr::app(t.clone(), i.clone()), x_i);
        let body = self.mul(fs, ft);
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }

    /// `fun (i : Fin n) => factor (Bool.xor (S i) (T i)) (x i)` — the merged
    /// factor (δβ-equal to `chi n (symmDiff S T) x`'s integrand).
    fn xor_factor_fn(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        s: &Expr,
        t: &Expr,
        x: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let gate = self.xor(
            Expr::app(s.clone(), i.clone()),
            Expr::app(t.clone(), i.clone()),
        );
        let body = self.factor(&b, gate, Expr::app(x.clone(), i));
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
}

/// The pointwise merge `∀ i, factor (S i) (x i) · factor (T i) (x i)`
/// `= factor (xor (S i) (T i)) (x i)`, as the function of `i` that
/// `Fin.prod_congr` consumes. 2×2 `Bool.rec` on `(S i, T i)` with an inner
/// split on `x i` in the (true, true) square case.
fn pointwise_merge_eq(
    c: &ChiSymmDiffConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    s: &Expr,
    t: &Expr,
    x: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (i_id, i) = b.fresh_local(fin_n.clone());

    let s_i = Expr::app(s.clone(), i.clone());
    let t_i = Expr::app(t.clone(), i.clone());
    let x_i = Expr::app(x.clone(), i.clone());

    // The proposition `factor sb xb · factor tb xb = factor (xor sb tb) xb`.
    let goal = |parent: &EnvDeclBuilder, sb: Expr, tb: Expr, xb: Expr| -> Expr {
        let f1 = c.factor(parent, sb.clone(), xb.clone());
        let f2 = c.factor(parent, tb.clone(), xb.clone());
        let merged = c.factor(parent, c.xor(sb, tb), xb);
        c.eq_rat(c.mul(f1, f2), merged)
    };

    // ── (S i = true, T i = true): signed² = 1 — inner split on x i. ──
    let case_tt = {
        let mut d = EnvDeclBuilder::child_of(&b);
        // motive_x : fun xb => factor true xb · factor true xb = factor (xor true true) xb.
        let motive_x = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (xb_id, xb) = e.fresh_local(c.bool_.clone());
            let body = goal(&e, c.btrue.clone(), c.btrue.clone(), xb);
            e.finish_child(e.mk_lam(xb_id, BinderInfo::Default, c.bool_.clone(), body))
        };
        // Closed leaves: the squared signed factor ground-reduces to 1, and the
        // RHS gate `xor true true ≡ false` reduces the merged factor to 1.
        let leaf = |parent: &EnvDeclBuilder, xb: Expr| -> Expr {
            let f = c.factor(parent, c.btrue.clone(), xb);
            Expr::apps(c.eq_refl.clone(), [c.rat.clone(), c.mul(f.clone(), f)])
        };
        let leaf_f = leaf(&d, c.bfalse.clone());
        let leaf_t = leaf(&d, c.btrue.clone());
        let rec = Expr::apps(
            c.bool_rec_prop.clone(),
            [motive_x, leaf_f, leaf_t, x_i.clone()],
        );
        d.finish_child(rec)
    };

    // ── (S i = true): split on T i. ──
    let case_s_true = {
        let mut d = EnvDeclBuilder::child_of(&b);
        // motive_t : fun tb => factor true (x i) · factor tb (x i)
        //              = factor (xor true tb) (x i).
        let motive_t = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (tb_id, tb) = e.fresh_local(c.bool_.clone());
            let body = goal(&e, c.btrue.clone(), tb, x_i.clone());
            e.finish_child(e.mk_lam(tb_id, BinderInfo::Default, c.bool_.clone(), body))
        };
        // T i = false: `f·1 = f` — Rat.mul_one (factor true (x i)).
        // (`factor false (x i) ≡ 1` and `xor true false ≡ true` by ι.)
        let case_tf = Expr::app(
            c.rat_mul_one.clone(),
            c.factor(&d, c.btrue.clone(), x_i.clone()),
        );
        let rec = Expr::apps(
            c.bool_rec_prop.clone(),
            [motive_t, case_tf, case_tt, t_i.clone()],
        );
        d.finish_child(rec)
    };

    // ── (S i = false): `1·f = f` — Rat.one_mul (factor (T i) (x i)). ──
    // (`factor false (x i) ≡ 1` and `xor false (T i) ≡ T i` by ι.)
    let case_s_false = Expr::app(
        c.rat_one_mul.clone(),
        c.factor(&b, t_i.clone(), x_i.clone()),
    );

    // motive_s : fun sb => factor sb (x i) · factor (T i) (x i)
    //              = factor (xor sb (T i)) (x i).
    let motive_s = {
        let mut e = EnvDeclBuilder::child_of(&b);
        let (sb_id, sb) = e.fresh_local(c.bool_.clone());
        let body = goal(&e, sb, t_i.clone(), x_i.clone());
        e.finish_child(e.mk_lam(sb_id, BinderInfo::Default, c.bool_.clone(), body))
    };

    let rec = Expr::apps(
        c.bool_rec_prop.clone(),
        [motive_s, case_s_false, case_s_true, s_i],
    );
    let lam = b.mk_lam(i_id, BinderInfo::Default, fin_n, rec);
    b.finish_child(lam)
}

fn build_type(c: &ChiSymmDiffConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (t_id, t) = b.fresh_local(hcp.clone());
    let (x_id, x) = b.fresh_local(hcp.clone());

    let lhs = c.mul(
        c.chi(n.clone(), s.clone(), x.clone()),
        c.chi(n.clone(), t.clone(), x.clone()),
    );
    let rhs = c.chi(n.clone(), c.symm_diff_fn(&b, &n, &s, &t), x.clone());
    let concl = c.eq_rat(lhs, rhs);

    let ty = b.mk_pi(x_id, BinderInfo::Default, hcp.clone(), concl);
    let ty = b.mk_pi(t_id, BinderInfo::Default, hcp.clone(), ty);
    let ty = b.mk_pi(s_id, BinderInfo::Default, hcp, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    b.finish(ty)
}

fn build_value(c: &ChiSymmDiffConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (t_id, t) = b.fresh_local(hcp.clone());
    let (x_id, x) = b.fresh_local(hcp.clone());

    let chi_mul = c.mul(
        c.chi(n.clone(), s.clone(), x.clone()),
        c.chi(n.clone(), t.clone(), x.clone()),
    );
    let pmul = c.pointwise_mul_fn(&b, &n, &s, &t, &x);
    let xfac = c.xor_factor_fn(&b, &n, &s, &t, &x);
    let prod_pmul = c.prod(n.clone(), pmul.clone());
    let rhs = c.chi(n.clone(), c.symm_diff_fn(&b, &n, &s, &t), x.clone());

    // step1 : χ_S·χ_T = Fin.prod n (pointwise mul) — chi_mul_chi (its stated
    // RHS integrand is β-equal to ours; the kernel retypes by defeq).
    let step1 = Expr::apps(
        c.chi_mul_chi.clone(),
        [n.clone(), s.clone(), t.clone(), x.clone()],
    );
    // step2 : Fin.prod n (pointwise mul) = Fin.prod n (merged factor)
    //   — Fin.prod_congr over the pointwise 2×2 merge.
    let step2 = Expr::apps(
        c.fin_prod_congr.clone(),
        [
            n.clone(),
            pmul,
            xfac,
            pointwise_merge_eq(c, &b, &n, &s, &t, &x),
        ],
    );

    // trans: χ_S·χ_T = prod (pointwise mul) = chi n (S Δ T) x
    //   (step2's RHS `Fin.prod n (merged factor)` is δβ-equal to the goal RHS).
    let proof = c.trans_rat(chi_mul, prod_pmul, rhs, step1, step2);

    let val = b.mk_lam(x_id, BinderInfo::Default, hcp.clone(), proof);
    let val = b.mk_lam(t_id, BinderInfo::Default, hcp.clone(), val);
    let val = b.mk_lam(s_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.chi_mul_chi_symmDiff` as a kernel-checked,
    /// constructive theorem. Idempotent.
    pub(crate) fn register_chi_symm_diff_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_mul_chi_symmDiff");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?; // Rat.one_mul / Rat.mul_one
        self.init_boolean_analysis_foundations()?; // chi / Fin.prod / Bool.xor
        self.register_chi_mul_chi_theorem()?;
        self.register_fin_prod_one_theorems()?; // Fin.prod_congr

        let c = ChiSymmDiffConsts::new();
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
        env.register_chi_symm_diff_theorem()
            .expect("register_chi_symm_diff_theorem");
        env
    }

    /// `chi_mul_chi_symmDiff` is a genuine kernel-checked, `Constructive`
    /// `Declaration::Theorem` (empty admitted-axiom closure), and its proof
    /// term re-checks under C1.
    #[test]
    fn test_chi_symm_diff_is_constructive_theorem() {
        let env = make_env();
        let name = Name::from_string("BoolAnalysis.chi_mul_chi_symmDiff");
        let info = env
            .get_const(&name)
            .expect("chi_mul_chi_symmDiff should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "chi_mul_chi_symmDiff must be a kernel-checked Theorem"
        );
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("chi_mul_chi_symmDiff proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "chi_mul_chi_symmDiff must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "chi_mul_chi_symmDiff's transitive axiom closure must be empty"
        );
    }
}
