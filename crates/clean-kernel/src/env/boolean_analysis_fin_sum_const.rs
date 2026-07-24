// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Fin.sum_const` — the constant-function finite sum `Σ_n (fun _ => c) =
//! natCast n · c`. The general (`c`-parametric) twin of `Fin.sum_const_one`
//! (which is the `c = 1` instance). This is reusable plumbing the KKL
//! `kkl_inequality` assembly's pigeonhole step needs (the constant-sum LHS of
//! `Fin.exists_ge_of_sum_ge`).
//!
//! ```text
//! Fin.sum_const : ∀ (n : Nat) (c : Rat),
//!   @Eq Rat (Fin.sum n (fun _ => c)) (Rat.mul (Rat.mk (Int.ofNat n) 1) c)
//! ```
//!
//! ## Proof (constructive, empty admitted-axiom closure)
//!
//! `Nat.rec.{0}` on `n` (the faithful `Fin.sum` carrier), motive
//! `λ k => Fin.sum k (const c) = natCast k · c` (c fixed by the outer binder).
//!
//! - **base** `Fin.sum 0 (const c) = natCast 0 · c`: `Fin.sum 0 _ ≡ Rat.zero`
//!   and `natCast 0 · c ≡ Rat.zero · c`; closed by `Eq.symm (Rat.zero_mul c)`
//!   (`Rat.zero_mul c : 0·c = 0`).
//! - **step** `motive k → motive (k+1)`:
//!   `Fin.sum (k+1) (const c) ≡ Rat.add (Fin.sum k (const c)) c` (`Fin.sum_succ`
//!   ι: cast-prefix of `const c` is `const c`, last factor is `c`).
//!   - `s1 : = Rat.add (natCast k · c) c`  (`congrArg (· + c)` of the IH).
//!   - `s2 : Rat.add (natCast k · c) c = natCast (k+1) · c`. Built from
//!     `Rat.right_distrib (natCast k) 1 c : (natCast k + 1)·c = natCast k·c + 1·c`,
//!     `Rat.one_mul c : 1·c = c` (rewrites `1·c → c` on the RHS), and
//!     `Rat.add_natCast_one k : natCast k + 1 = natCast (k+1)` (rewrites the LHS
//!     scalar), glued by `congrArg`/`Eq.trans`/`Eq.symm`.
//!   - `Eq.trans s1 s2` closes the step.
//!
//! Every leaf is a `Nat.rec`/`congrArg`/`Eq.*` built-in or a landed constructive
//! Theorem (`Fin.sum_succ`, `Rat.zero_mul`, `Rat.one_mul`, `Rat.right_distrib`,
//! `Rat.add_natCast_one`), so `Fin.sum_const` is `Constructive` with empty
//! closure. No axiom is added or removed. Idempotent.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for `Fin.sum_const`.
struct FinSumConstConsts {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    rat_one: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_mk: Expr,
    int_of_nat: Expr,
    fin_sum: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_rec0: Expr,
    eq1: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
    zero_mul: Expr,
    one_mul: Expr,
    right_distrib: Expr,
    add_natcast_one: Expr,
}

impl FinSumConstConsts {
    fn new() -> Self {
        let u1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_mk: Expr::const_(Name::from_string("Rat.mk"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_rec0: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![u1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![u1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![u1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![u1.clone(), u1]),
            zero_mul: Expr::const_(Name::from_string("Rat.zero_mul"), vec![]),
            one_mul: Expr::const_(Name::from_string("Rat.one_mul"), vec![]),
            right_distrib: Expr::const_(Name::from_string("Rat.right_distrib"), vec![]),
            add_natcast_one: Expr::const_(Name::from_string("Rat.add_natCast_one"), vec![]),
        }
    }

    fn one_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }
    fn natcast(&self, n: Expr) -> Expr {
        Expr::apps(self.rat_mk.clone(), [self.of_nat(n), self.one_nat()])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn radd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn sum(&self, n: Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n, g])
    }
    fn eq_rat(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), x, y])
    }
    fn symm_rat(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), x, y, h])
    }
    fn trans_rat(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), x, y, z, h1, h2])
    }
    /// `@congrArg Rat Rat a b f h : f a = f b`.
    fn congr_rat(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    /// `fun (_ : Fin n) => c`.
    fn const_fn(&self, parent: &EnvDeclBuilder, n: &Expr, c: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, _i) = b.fresh_local(fin_n.clone());
        let lam = b.mk_lam(i_id, BinderInfo::Default, fin_n, c.clone());
        b.finish_child(lam)
    }
    /// `fun (r : Rat) => Rat.add r c` — the congrArg closure for the step.
    fn add_c_right_fn(&self, parent: &EnvDeclBuilder, c: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (r_id, r) = b.fresh_local(self.rat.clone());
        let body = self.radd(r, c.clone());
        let lam = b.mk_lam(r_id, BinderInfo::Default, self.rat.clone(), body);
        b.finish_child(lam)
    }
    /// `fun (s : Rat) => Rat.mul s c` — congrArg closure to lift a scalar
    /// equality through `·*c`.
    fn mul_c_right_fn(&self, parent: &EnvDeclBuilder, c: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (s_id, s) = b.fresh_local(self.rat.clone());
        let body = self.mul(s, c.clone());
        let lam = b.mk_lam(s_id, BinderInfo::Default, self.rat.clone(), body);
        b.finish_child(lam)
    }
}

impl Environment {
    /// Register `Fin.sum_const : ∀ (n : Nat) (c : Rat),
    ///   Fin.sum n (fun _ => c) = Rat.mk (Int.ofNat n) 1 · c`. See module docs.
    pub(crate) fn register_fin_sum_const(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_const");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?; // Rat.zero_mul, Rat.one_mul, Rat.right_distrib
        self.init_fin_sum()?; // Fin.sum, Fin.sum_succ
        self.register_fin_sum_const_one_theorems()?; // Rat.add_natCast_one

        let c = FinSumConstConsts::new();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (cc_id, cc) = b.fresh_local(c.rat.clone());
            let lhs = c.sum(n.clone(), c.const_fn(&b, &n, &cc));
            let rhs = c.mul(c.natcast(n.clone()), cc.clone());
            let concl = c.eq_rat(lhs, rhs);
            let e = b.mk_pi(cc_id, BinderInfo::Default, c.rat.clone(), concl);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (cc_id, cc) = b.fresh_local(c.rat.clone());

            // motive : λ (k : Nat) => Fin.sum k (const c) = natCast k · c
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (k_id, k) = m.fresh_local(c.nat.clone());
                let lhs = c.sum(k.clone(), c.const_fn(&m, &k, &cc));
                let rhs = c.mul(c.natcast(k.clone()), cc.clone());
                let body = c.eq_rat(lhs, rhs);
                m.finish_child(m.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
            };

            // base : Fin.sum 0 (const c) = natCast 0 · c
            //   LHS ≡ Rat.zero ; RHS ≡ Rat.zero · c ; Rat.zero_mul c : 0·c = 0.
            //   So symm (zero_mul c) : 0 = 0·c ≡ Fin.sum 0 _ = natCast 0 · c.
            let base = {
                let zero_mul_c = Expr::app(c.zero_mul.clone(), cc.clone()); // 0·c = 0
                let zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
                let natcast0_c = c.mul(c.natcast(c.nat_zero.clone()), cc.clone());
                // symm (zero_mul c) : 0 = 0·c   (≡ Fin.sum 0 (const c) = natCast 0 · c)
                c.symm_rat(natcast0_c, zero, zero_mul_c)
            };

            // step : λ (k) (ih : Fin.sum k (const c) = natCast k · c) => proof
            let step = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (k_id, k) = s.fresh_local(c.nat.clone());
                let ih_ty = {
                    let lhs = c.sum(k.clone(), c.const_fn(&s, &k, &cc));
                    let rhs = c.mul(c.natcast(k.clone()), cc.clone());
                    c.eq_rat(lhs, rhs)
                };
                let (ih_id, ih) = s.fresh_local(ih_ty.clone());

                let sum_k = c.sum(k.clone(), c.const_fn(&s, &k, &cc));
                let natcast_k = c.natcast(k.clone());
                let nk_c = c.mul(natcast_k.clone(), cc.clone()); // natCast k · c

                // lhs ≡ Rat.add (Fin.sum k (const c)) c    (Fin.sum_succ ι)
                let lhs = c.radd(sum_k.clone(), cc.clone());
                // mid = Rat.add (natCast k · c) c
                let mid = c.radd(nk_c.clone(), cc.clone());
                let sk = Expr::app(c.nat_succ.clone(), k.clone());
                let rhs = c.mul(c.natcast(sk.clone()), cc.clone()); // natCast (k+1) · c

                // s1 : lhs = mid    via congrArg (· + c) ih
                let s1 = c.congr_rat(sum_k, nk_c.clone(), c.add_c_right_fn(&s, &cc), ih);

                // s2 : mid = rhs, i.e. (natCast k · c + c) = natCast(k+1)·c.
                //   rd : (natCast k + 1)·c = natCast k · c + 1·c   (right_distrib)
                let nk1 = c.radd(natcast_k.clone(), c.rat_one.clone()); // natCast k + 1
                let nk1_c = c.mul(nk1.clone(), cc.clone()); // (natCast k + 1)·c
                let one_c = c.mul(c.rat_one.clone(), cc.clone()); // 1·c
                let nkc_plus_onec = c.radd(nk_c.clone(), one_c.clone()); // natCast k·c + 1·c
                let rd = Expr::apps(
                    c.right_distrib.clone(),
                    [natcast_k.clone(), c.rat_one.clone(), cc.clone()],
                );
                //   h_onec : 1·c = c   (Rat.one_mul c)
                let h_onec = Expr::app(c.one_mul.clone(), cc.clone());
                //   rewrite RHS of rd: natCast k·c + 1·c = natCast k·c + c via congrArg (natCast k·c + ·)
                let add_left_fn = {
                    let mut ab = EnvDeclBuilder::child_of(&s);
                    let (r_id, r) = ab.fresh_local(c.rat.clone());
                    let body = c.radd(nk_c.clone(), r);
                    ab.finish_child(ab.mk_lam(r_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let h_rhs = c.congr_rat(one_c.clone(), cc.clone(), add_left_fn, h_onec);
                //   rd2 : (natCast k + 1)·c = natCast k·c + c   (trans rd h_rhs)
                let rd2 = c.trans_rat(nk1_c.clone(), nkc_plus_onec.clone(), mid.clone(), rd, h_rhs);
                //   symm rd2 : natCast k·c + c = (natCast k + 1)·c   (= mid = nk1_c)
                let mid_eq_nk1c = c.symm_rat(nk1_c.clone(), mid.clone(), rd2);
                //   h_anc : natCast k + 1 = natCast (k+1)   (Rat.add_natCast_one k)
                let h_anc = Expr::app(c.add_natcast_one.clone(), k.clone());
                //   lift through ·*c: (natCast k + 1)·c = natCast(k+1)·c
                let h_scalar =
                    c.congr_rat(nk1.clone(), c.natcast(sk), c.mul_c_right_fn(&s, &cc), h_anc);
                //   s2 : mid = rhs   (trans mid_eq_nk1c h_scalar)
                let s2 = c.trans_rat(
                    mid.clone(),
                    nk1_c.clone(),
                    rhs.clone(),
                    mid_eq_nk1c,
                    h_scalar,
                );

                // proof : lhs = rhs   (trans s1 s2)
                let proof = c.trans_rat(lhs, mid, rhs, s1, s2);

                let e = s.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
                let e = s.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
                s.finish_child(e)
            };

            let rec_app = Expr::apps(c.nat_rec0.clone(), [motive, base, step, n.clone()]);
            let e = b.mk_lam(cc_id, BinderInfo::Default, c.rat.clone(), rec_app);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_fin_sum_const()
            .expect("register_fin_sum_const");
        env.register_fin_sum_const().expect("idempotent");
        env
    }

    #[test]
    fn test_fin_sum_const_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("Fin.sum_const");
        let info = env.get_const(&nm).expect("Fin.sum_const registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("Fin.sum_const must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty"
        );
    }
}
