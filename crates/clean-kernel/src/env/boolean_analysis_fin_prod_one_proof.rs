// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proofs of two reusable `Fin.prod` lemmas on the road to the
//! diagonal character inner product `⟨χ_S, χ_S⟩ = 1`:
//!
//! - `Fin.prod_const_one : ∀ (n : Nat), Fin.prod n (fun _ => Rat.one) = Rat.one`
//!   — the product of `n` copies of `1` is `1`.
//! - `Fin.prod_congr : ∀ (n : Nat) (f g : Fin n → Rat),`
//!   `  (∀ i, f i = g i) → Fin.prod n f = Fin.prod n g`
//!   — pointwise-equal factors have equal products (the multiplicative twin of
//!   the landed `Fin.sum_congr`).
//!
//! Both are `Nat.rec` inductions over the faithful `Fin.prod` carrier (identity
//! `Rat.one`, fold `Rat.mul`), using only landed constructive `Rat` algebra
//! (`Rat.mul_one`) and the `Eq`/`congr`/`congrArg` built-ins. Kernel-checked,
//! `ProofQuality::Constructive` (empty admitted-axiom closure).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct FinProdOneConsts {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    fin_prod: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    nat_rec: Expr,
    eq1: Expr,
    eq_refl: Expr,
    eq_trans: Expr,
    congr: Expr,
    congr_arg: Expr,
    rat_mul_one: Expr,
}

impl FinProdOneConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            fin_prod: Expr::const_(Name::from_string("Fin.prod"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            fin_cast_succ: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            congr: Expr::const_(
                Name::from_string("congr"),
                vec![type1.clone(), type1.clone()],
            ),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            rat_mul_one: Expr::const_(Name::from_string("Rat.mul_one"), vec![]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn fin_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat.clone())
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
    /// `@congrArg Rat Rat a b g h : g a = g b`.
    fn congr_arg_rat(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, g, h],
        )
    }

    /// `fun (_ : Fin n) => Rat.one`.
    fn const_one_fn(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, _i) = b.fresh_local(fin_n.clone());
        let lam = b.mk_lam(i_id, BinderInfo::Default, fin_n, self.rat_one.clone());
        b.finish_child(lam)
    }

    /// `fun (x : Rat) => Rat.mul x Rat.one`.
    fn mul_one_right_fn(&self, parent: &EnvDeclBuilder) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = b.fresh_local(self.rat.clone());
        let body = self.mul(x, self.rat_one.clone());
        let lam = b.mk_lam(x_id, BinderInfo::Default, self.rat.clone(), body);
        b.finish_child(lam)
    }
}

// ── Fin.prod_const_one ──

fn const_one_type(c: &FinProdOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let lhs = c.prod(n.clone(), c.const_one_fn(&b, &n));
    let concl = c.eq_rat(lhs, c.rat_one.clone());
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
    b.finish(ty)
}

fn const_one_motive(c: &FinProdOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let lhs = c.prod(k.clone(), c.const_one_fn(&b, &k));
    let body = c.eq_rat(lhs, c.rat_one.clone());
    let lam = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body);
    b.finish(lam)
}

/// Base `motive 0`: `Fin.prod 0 (const 1) ≡ Rat.one`, so `@Eq.refl Rat Rat.one`.
fn const_one_base(c: &FinProdOneConsts) -> Expr {
    Expr::apps(c.eq_refl.clone(), [c.rat.clone(), c.rat_one.clone()])
}

/// Step `motive k → motive (k+1)`:
///   `Fin.prod (k+1) (const 1) ≡ Fin.prod k (const 1) · 1`   (ι; cast prefix of
///       `const 1` is `const 1`, last is `1`)
///   `= 1 · 1`                                                (congrArg (·1) IH)
///   `= 1`                                                    (Rat.mul_one 1)
fn const_one_step(c: &FinProdOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    // ih : Fin.prod k (const 1) = 1
    let ih_ty = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let lhs = c.prod(k.clone(), c.const_one_fn(&d, &k));
        d.finish_child(c.eq_rat(lhs, c.rat_one.clone()))
    };
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());

    let prod_k = c.prod(k.clone(), c.const_one_fn(&b, &k));
    // lhs ≡ Fin.prod k (const 1) · 1
    let lhs = c.mul(prod_k.clone(), c.rat_one.clone());
    // mid = 1 · 1
    let mid = c.mul(c.rat_one.clone(), c.rat_one.clone());

    // step1 : lhs = mid    via congrArg (·1) ih
    let step1 = c.congr_arg_rat(prod_k, c.rat_one.clone(), c.mul_one_right_fn(&b), ih);
    // step2 : mid = 1      via Rat.mul_one 1  (Rat.mul 1 1 = 1)
    let step2 = Expr::app(c.rat_mul_one.clone(), c.rat_one.clone());
    let proof = c.eq_trans_rat(lhs, mid, c.rat_one.clone(), step1, step2);

    let val = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
    let val = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

fn const_one_value(c: &FinProdOneConsts) -> Expr {
    let motive = const_one_motive(c);
    let base = const_one_base(c);
    let step = const_one_step(c);
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let body = Expr::apps(c.nat_rec.clone(), [motive, base, step, n]);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
    b.finish(val)
}

// ── Fin.prod_congr ──

/// `fun i : Fin k => f (Fin.castSucc k i)`.
fn cast_succ_fn(c: &FinProdOneConsts, parent: &EnvDeclBuilder, k: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_k = c.fin_of(k);
    let (i_id, i) = b.fresh_local(fin_k.clone());
    let cast_i = Expr::apps(c.fin_cast_succ.clone(), [k.clone(), i]);
    let body = Expr::app(f.clone(), cast_i);
    let lam = b.mk_lam(i_id, BinderInfo::Default, fin_k, body);
    b.finish_child(lam)
}

/// Pointwise hypothesis type `∀ i : Fin n, f i = g i`.
fn hyp_ty(c: &FinProdOneConsts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, g: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let body = c.eq_rat(Expr::app(f.clone(), i.clone()), Expr::app(g.clone(), i));
    b.finish_child(b.mk_pi(i_id, BinderInfo::Default, fin_n, body))
}

fn congr_type(c: &FinProdOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let ft = c.fin_to_rat(&n);
    let (f_id, f) = b.fresh_local(ft.clone());
    let (g_id, g) = b.fresh_local(ft.clone());
    let h = hyp_ty(c, &b, &n, &f, &g);
    let (h_id, _h) = b.fresh_local(h.clone());
    let concl = c.eq_rat(c.prod(n.clone(), f.clone()), c.prod(n.clone(), g.clone()));
    let r = b.mk_pi(h_id, BinderInfo::Default, h, concl);
    let r = b.mk_pi(g_id, BinderInfo::Default, ft.clone(), r);
    let r = b.mk_pi(f_id, BinderInfo::Default, ft, r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

/// motive: `fun k => ∀ f g, (∀ i, f i = g i) → Fin.prod k f = Fin.prod k g`.
fn congr_motive(c: &FinProdOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let inner = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let ft = c.fin_to_rat(&k);
        let (f_id, f) = d.fresh_local(ft.clone());
        let (g_id, g) = d.fresh_local(ft.clone());
        let h = hyp_ty(c, &d, &k, &f, &g);
        let (h_id, _h) = d.fresh_local(h.clone());
        let concl = c.eq_rat(c.prod(k.clone(), f.clone()), c.prod(k.clone(), g.clone()));
        let r = d.mk_pi(h_id, BinderInfo::Default, h, concl);
        let r = d.mk_pi(g_id, BinderInfo::Default, ft.clone(), r);
        let r = d.mk_pi(f_id, BinderInfo::Default, ft, r);
        d.finish_child(r)
    };
    b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), inner))
}

/// Base `motive 0`: `Fin.prod 0 f ≡ 1 ≡ Fin.prod 0 g`, so `@Eq.refl Rat Rat.one`.
fn congr_base(c: &FinProdOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let ft = c.fin_to_rat(&c.nat_zero);
    let (f_id, f) = b.fresh_local(ft.clone());
    let (g_id, g) = b.fresh_local(ft.clone());
    let h = hyp_ty(c, &b, &c.nat_zero, &f, &g);
    let (h_id, _h) = b.fresh_local(h.clone());
    let refl = Expr::apps(c.eq_refl.clone(), [c.rat.clone(), c.rat_one.clone()]);
    let r = b.mk_lam(h_id, BinderInfo::Default, h, refl);
    let r = b.mk_lam(g_id, BinderInfo::Default, ft.clone(), r);
    let r = b.mk_lam(f_id, BinderInfo::Default, ft, r);
    b.finish(r)
}

/// Step `motive k → motive (k+1)`:
///   `Fin.prod (k+1) f ≡ Fin.prod k (f∘cs) · f(last)`,  similarly for `g`.
///   Goal `Fin.prod (k+1) f = Fin.prod (k+1) g` is
///   `congr (congrArg Rat.mul (ih (f∘cs) (g∘cs) (fun i => h (castSucc k i))))
///          (h (last k))`.
fn congr_step(c: &FinProdOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    // ih : ∀ f g, (∀ i, f i = g i) → Fin.prod k f = Fin.prod k g
    let ih_ty = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let ft = c.fin_to_rat(&k);
        let (f_id, f) = d.fresh_local(ft.clone());
        let (g_id, g) = d.fresh_local(ft.clone());
        let h = hyp_ty(c, &d, &k, &f, &g);
        let (h_id, _h) = d.fresh_local(h.clone());
        let concl = c.eq_rat(c.prod(k.clone(), f.clone()), c.prod(k.clone(), g.clone()));
        let r = d.mk_pi(h_id, BinderInfo::Default, h, concl);
        let r = d.mk_pi(g_id, BinderInfo::Default, ft.clone(), r);
        let r = d.mk_pi(f_id, BinderInfo::Default, ft, r);
        d.finish_child(r)
    };
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());

    let succ_k = Expr::app(c.nat_succ.clone(), k.clone());
    let ft_sk = c.fin_to_rat(&succ_k);
    let (f_id, f) = b.fresh_local(ft_sk.clone());
    let (g_id, g) = b.fresh_local(ft_sk.clone());
    let h_sk = hyp_ty(c, &b, &succ_k, &f, &g);
    let (h_id, h) = b.fresh_local(h_sk.clone());

    let f_cast = cast_succ_fn(c, &b, &k, &f);
    let g_cast = cast_succ_fn(c, &b, &k, &g);
    let prod_f_pre = c.prod(k.clone(), f_cast.clone());
    let prod_g_pre = c.prod(k.clone(), g_cast.clone());
    let f_last = Expr::app(f.clone(), Expr::app(c.fin_last.clone(), k.clone()));
    let g_last = Expr::app(g.clone(), Expr::app(c.fin_last.clone(), k.clone()));

    // h_pre : ∀ i : Fin k, f(castSucc k i) = g(castSucc k i)
    //   = fun i => h (Fin.castSucc k i)
    let h_pre = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin_k = c.fin_of(&k);
        let (i_id, i) = d.fresh_local(fin_k.clone());
        let cast_i = Expr::apps(c.fin_cast_succ.clone(), [k.clone(), i]);
        let body = Expr::app(h.clone(), cast_i);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_k, body))
    };
    // ih_app : Fin.prod k (f∘cs) = Fin.prod k (g∘cs)
    let ih_app = Expr::apps(ih.clone(), [f_cast.clone(), g_cast.clone(), h_pre]);

    // congrArg Rat.mul ih_app : Rat.mul (prod_f_pre) = Rat.mul (prod_g_pre)
    //   (the partially-applied `Rat.mul` of type Rat → Rat)
    let rat_to_rat = Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone());
    let congr_arg_mul = Expr::apps(
        c.congr_arg.clone(),
        [
            c.rat.clone(),
            rat_to_rat.clone(),
            prod_f_pre.clone(),
            prod_g_pre.clone(),
            c.rat_mul.clone(),
            ih_app,
        ],
    );
    // h_last : f(last k) = g(last k)
    let h_last = Expr::app(h.clone(), Expr::app(c.fin_last.clone(), k.clone()));

    // congr (congrArg Rat.mul ih_app) h_last
    //   : Rat.mul prod_f_pre f_last = Rat.mul prod_g_pre g_last
    // @congr.{1,1} Rat Rat (Rat.mul prod_f_pre) (Rat.mul prod_g_pre) f_last g_last
    //              congr_arg_mul h_last
    let mul_f_pre = Expr::app(c.rat_mul.clone(), prod_f_pre);
    let mul_g_pre = Expr::app(c.rat_mul.clone(), prod_g_pre);
    let proof = Expr::apps(
        c.congr.clone(),
        [
            c.rat.clone(),
            c.rat.clone(),
            mul_f_pre,
            mul_g_pre,
            f_last,
            g_last,
            congr_arg_mul,
            h_last,
        ],
    );

    let val = b.mk_lam(h_id, BinderInfo::Default, h_sk, proof);
    let val = b.mk_lam(g_id, BinderInfo::Default, ft_sk.clone(), val);
    let val = b.mk_lam(f_id, BinderInfo::Default, ft_sk, val);
    let val = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, val);
    let val = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

fn congr_value(c: &FinProdOneConsts) -> Expr {
    let motive = congr_motive(c);
    let base = congr_base(c);
    let step = congr_step(c);
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let body = Expr::apps(c.nat_rec.clone(), [motive, base, step, n]);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
    b.finish(val)
}

impl Environment {
    /// Register `Fin.prod_const_one` and `Fin.prod_congr` as kernel-checked,
    /// constructive theorems. Idempotent.
    pub(crate) fn register_fin_prod_one_theorems(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?;
        self.init_rat()?;

        let c = FinProdOneConsts::new();
        if self
            .get_const(&Name::from_string("Fin.prod_const_one"))
            .is_none()
        {
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Fin.prod_const_one"),
                level_params: vec![],
                type_: const_one_type(&c),
                value: const_one_value(&c),
            })?;
        }
        if self
            .get_const(&Name::from_string("Fin.prod_congr"))
            .is_none()
        {
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Fin.prod_congr"),
                level_params: vec![],
                type_: congr_type(&c),
                value: congr_value(&c),
            })?;
        }
        Ok(())
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
        env.register_fin_prod_one_theorems()
            .expect("register_fin_prod_one_theorems");
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
    fn test_fin_prod_const_one_is_constructive_theorem() {
        let env = make_env();
        check_constructive(&env, "Fin.prod_const_one");
    }

    #[test]
    fn test_fin_prod_congr_is_constructive_theorem() {
        let env = make_env();
        check_constructive(&env, "Fin.prod_congr");
    }
}
