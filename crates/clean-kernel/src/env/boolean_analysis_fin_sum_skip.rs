// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Fin.skipNth` (a.k.a. `Fin.succAbove`) and the remove-one-index sum
//! `Fin.sum_remove`, the deep finite-sum infrastructure for the
//! `Fin.sum_reindex_involution` keystone (kkl retirement).
//!
//! ```text
//! Fin.skipNth : (k : Nat) → (p : Fin (k+1)) → Fin k → Fin (k+1)
//! ```
//!
//! `Fin.skipNth k p` is the order-embedding `Fin k ↪ Fin (k+1)` whose image is
//! everything *except* `p`. It maps `j` to `Fin.castSucc k j` (val `= val j`)
//! when `val j < val p`, and to the shifted index (val `= val j + 1`) otherwise.
//! Built by `Decidable.rec` on `Nat.decLt (val j) (val p)`, so `val (skipNth k p
//! j)` reduces computably in each branch.
//!
//! `Fin.skipNth` is a **reducible `Declaration::Definition`** with the faithful
//! `Fin.mk` shape, axiom-free.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct SkipConsts {
    nat: Expr,
    nat_succ: Expr,
    nat_lt: Expr,
    nat_dec_lt: Expr,
    nat_succ_lt_succ: Expr,
    fin: Expr,
    fin_mk: Expr,
    fin_val: Expr,
    fin_islt: Expr,
    fin_cast_succ: Expr,
    ite: Expr, // @ite.{1} — into Sort 1 (Fin (k+1))
}

impl SkipConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_succ: k("Nat.succ"),
            nat_lt: k("Nat.lt"),
            nat_dec_lt: k("Nat.decLt"),
            nat_succ_lt_succ: k("Nat.succ_lt_succ"),
            fin: k("Fin"),
            fin_mk: k("Fin.mk"),
            fin_val: k("Fin.val"),
            fin_islt: k("Fin.isLt"),
            fin_cast_succ: k("Fin.castSucc"),
            ite: Expr::const_(Name::from_string("ite"), vec![l1]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn val(&self, n: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [n.clone(), x.clone()])
    }
    fn lt(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nat_lt.clone(), [a.clone(), b.clone()])
    }
    fn cast_succ(&self, k: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.fin_cast_succ.clone(), [k.clone(), j.clone()])
    }
}

/// `Fin.mk (k+1) (succ (val k j)) (Nat.succ_lt_succ (val j) k (Fin.isLt k j))`
/// — the "shifted" image of `j` (val `= val j + 1`), the `else` branch of
/// `skipNth`. Factored out because both `skipNth`'s value and `skipNth_ge` use
/// the exact same term.
fn skip_shift(c: &SkipConsts, k: &Expr, j: &Expr) -> Expr {
    let succ_k = c.succ(k);
    let val_j = c.val(k, j);
    let succ_val = c.succ(&val_j);
    let islt = Expr::apps(c.fin_islt.clone(), [k.clone(), j.clone()]);
    let bound = Expr::apps(c.nat_succ_lt_succ.clone(), [val_j, k.clone(), islt]);
    Expr::apps(c.fin_mk.clone(), [succ_k, succ_val, bound])
}

// ===========================================================================
// Fin.skipNth : (k : Nat) → (p : Fin (k+1)) → Fin k → Fin (k+1)
//
//   fun k p j =>
//     @ite.{1} (Fin (k+1)) (Nat.lt (val j) (val p)) (Nat.decLt (val j) (val p))
//       (Fin.castSucc k j)                       -- then (val j < val p)
//       (Fin.mk (k+1) (succ (val j)) bound)       -- else
//
// Using `ite` (not a raw `Decidable.rec`) lets `if_pos` / `if_neg` collapse the
// branch GIVEN a proof / disproof of `val j < val p`, even when the instance
// `Nat.decLt …` cannot ι-reduce on a symbolic `val j`.
// ===========================================================================
fn skip_nth_type(c: &SkipConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let succ_k = c.succ(&k);
    let fin_succ = c.fin_of(&succ_k);
    let fin_k = c.fin_of(&k);
    let (p_id, _p) = b.fresh_local(fin_succ.clone());
    let (j_id, _j) = b.fresh_local(fin_k.clone());
    let r = b.mk_pi(j_id, BinderInfo::Default, fin_k, fin_succ.clone());
    let r = b.mk_pi(p_id, BinderInfo::Default, fin_succ, r);
    b.finish(b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r))
}

fn skip_nth_value(c: &SkipConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let succ_k = c.succ(&k);
    let fin_succ = c.fin_of(&succ_k);
    let fin_k = c.fin_of(&k);
    let (p_id, p) = b.fresh_local(fin_succ.clone());
    let (j_id, j) = b.fresh_local(fin_k.clone());

    let val_j = c.val(&k, &j);
    let val_p = c.val(&succ_k, &p);
    let prop = c.lt(&val_j, &val_p); // Nat.lt (val j) (val p)

    let then_v = c.cast_succ(&k, &j); // Fin.castSucc k j
    let else_v = skip_shift(c, &k, &j); // Fin.mk (k+1) (succ (val j)) _
    let discr = Expr::apps(c.nat_dec_lt.clone(), [val_j.clone(), val_p.clone()]);
    // @ite.{1} (Fin (k+1)) prop discr then else
    let body = Expr::apps(
        c.ite.clone(),
        [fin_succ.clone(), prop, discr, then_v, else_v],
    );

    let r = b.mk_lam(j_id, BinderInfo::Default, fin_k, body);
    let r = b.mk_lam(p_id, BinderInfo::Default, fin_succ, r);
    b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), r))
}

impl Environment {
    /// Register `Fin.skipNth` — the remove-one-index order embedding
    /// `Fin k ↪ Fin (k+1)` skipping `p` (see module docs). Reducible
    /// `Declaration::Definition`, axiom-free. Idempotent.
    pub(crate) fn register_fin_skip_nth(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.skipNth");
        if self
            .get_const(&name)
            .is_some_and(|d| d.kind == super::types::ConstantKind::Definition)
        {
            return Ok(());
        }
        self.init_nat()?;
        self.init_lt()?;
        self.init_fin()?;
        self.init_decidable()?;
        self.init_ite()?; // ite
        self.register_nat_dec_le_lt_proof()?; // Nat.decLt
        self.init_nat_top_level_ordering()?; // Nat.succ_lt_succ (constructive Theorem)
        {
            let fc = super::nn_verify_fin_sum::FinSumConsts::new();
            self.ensure_fin_cast_succ(&fc)?;
            self.ensure_fin_last(&fc)?;
        }

        let c = SkipConsts::new();
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: skip_nth_type(&c),
            value: skip_nth_value(&c),
            is_reducible: true,
        })
    }

    /// `Fin.skipNth_castSucc_of_last : (k)(j : Fin k) →
    ///     @Eq (Fin (k+1)) (Fin.skipNth k (Fin.last k) j) (Fin.castSucc k j)`.
    ///
    /// When `p = Fin.last k` (val `≡ k`), the guard `val j < val (last k) ≡
    /// val j < k` is ALWAYS true (`Fin.isLt k j`), so `skipNth` collapses to its
    /// `then` branch `Fin.castSucc k j` via `if_pos`. Constructive, axiom-free.
    pub(crate) fn register_fin_skip_nth_last(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.skipNth_castSucc_of_last");
        if self
            .get_const(&name)
            .is_some_and(|d| d.kind == super::types::ConstantKind::Theorem)
        {
            return Ok(());
        }
        self.register_fin_skip_nth()?;
        self.register_ite_pos_neg_lemmas()?; // if_pos / if_neg

        let c = SkipConsts::new();
        let l1 = Level::succ(Level::zero());
        let eq1 = Expr::const_(Name::from_string("Eq"), vec![l1.clone()]);
        let if_pos = Expr::const_(Name::from_string("if_pos"), vec![l1]);
        let fin_last = Expr::const_(Name::from_string("Fin.last"), vec![]);
        let skip = Expr::const_(Name::from_string("Fin.skipNth"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let fin_k = c.fin_of(&k);
            let (j_id, j) = b.fresh_local(fin_k.clone());
            let last_k = Expr::app(fin_last.clone(), k.clone());
            let lhs = Expr::apps(skip.clone(), [k.clone(), last_k, j.clone()]);
            let rhs = c.cast_succ(&k, &j);
            let succ_k = c.succ(&k);
            let concl = Expr::apps(eq1.clone(), [c.fin_of(&succ_k), lhs, rhs]);
            let r = b.mk_pi(j_id, BinderInfo::Default, fin_k, concl);
            b.finish(b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r))
        };
        // Value: fun k j =>
        //   @if_pos.{1} (Nat.lt (val j) (val (last k))) (Fin (k+1))
        //     (Nat.decLt (val j) (val (last k))) (Fin.isLt k j)
        //     (Fin.castSucc k j) (skip_shift k j)
        // `Fin.isLt k j : Nat.lt (val j) k`; `val (last k) ≡ k` (defeq), so it
        // has the required type `Nat.lt (val j) (val (last k))`.  `if_pos`
        // rewrites `@ite … = (Fin.castSucc k j)` — and `skipNth k (last k) j`
        // δ-unfolds to exactly that `@ite`.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let fin_k = c.fin_of(&k);
            let (j_id, j) = b.fresh_local(fin_k.clone());
            let succ_k = c.succ(&k);
            let fin_succ = c.fin_of(&succ_k);
            let last_k = Expr::app(fin_last.clone(), k.clone());
            let val_j = c.val(&k, &j);
            let val_last = c.val(&succ_k, &last_k); // ≡ k
            let prop = c.lt(&val_j, &val_last);
            let discr = Expr::apps(c.nat_dec_lt.clone(), [val_j.clone(), val_last.clone()]);
            // proof of `val j < val (last k)`: Fin.isLt k j : val j < k, defeq.
            let hc = Expr::apps(c.fin_islt.clone(), [k.clone(), j.clone()]);
            let then_v = c.cast_succ(&k, &j);
            let else_v = skip_shift(&c, &k, &j);
            // Lean order: @if_pos {c} {inst} (hc) {α} {t} {e}.
            let body = Expr::apps(if_pos.clone(), [prop, discr, hc, fin_succ, then_v, else_v]);
            let r = b.mk_lam(j_id, BinderInfo::Default, fin_k, body);
            b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), r))
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Fin.skipNth_lt : (k)(p : Fin (k+1))(j : Fin k) →
    ///     Nat.lt (Fin.val j) (Fin.val p) →
    ///     @Eq (Fin (k+1)) (Fin.skipNth k p j) (Fin.castSucc k j)`
    /// and
    /// `Fin.skipNth_ge : (k)(p : Fin (k+1))(j : Fin k) →
    ///     (Nat.lt (Fin.val j) (Fin.val p) → False) →
    ///     @Eq (Fin (k+1)) (Fin.skipNth k p j)
    ///         (Fin.mk (k+1) (Nat.succ (Fin.val j)) _)`.
    ///
    /// The two `ite`-collapse equations for `skipNth`, given a proof / disproof
    /// of the guard `val j < val p`. `if_pos` / `if_neg` rewrite the `ite` that
    /// `skipNth` δ-unfolds to. Constructive, axiom-free. Idempotent.
    pub(crate) fn register_fin_skip_nth_collapse(&mut self) -> Result<(), EnvError> {
        let lt_name = Name::from_string("Fin.skipNth_lt");
        let ge_name = Name::from_string("Fin.skipNth_ge");
        let have = self
            .get_const(&lt_name)
            .is_some_and(|d| d.kind == super::types::ConstantKind::Theorem)
            && self
                .get_const(&ge_name)
                .is_some_and(|d| d.kind == super::types::ConstantKind::Theorem);
        if have {
            return Ok(());
        }
        self.register_fin_skip_nth()?;
        self.register_ite_pos_neg_lemmas()?;

        let c = SkipConsts::new();
        let l1 = Level::succ(Level::zero());
        let eq1 = Expr::const_(Name::from_string("Eq"), vec![l1.clone()]);
        let if_pos = Expr::const_(Name::from_string("if_pos"), vec![l1.clone()]);
        let if_neg = Expr::const_(Name::from_string("if_neg"), vec![l1]);
        let false_c = Expr::const_(Name::from_string("False"), vec![]);
        let skip = Expr::const_(Name::from_string("Fin.skipNth"), vec![]);

        // Shared header: ∀ k (p : Fin (k+1)) (j : Fin k), <prem> → @Eq (Fin (k+1)) (skip k p j) rhs.
        for is_lt in [true, false] {
            let name = if is_lt {
                lt_name.clone()
            } else {
                ge_name.clone()
            };
            if self
                .get_const(&name)
                .is_some_and(|d| d.kind == super::types::ConstantKind::Theorem)
            {
                continue;
            }
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (k_id, k) = b.fresh_local(c.nat.clone());
                let succ_k = c.succ(&k);
                let fin_succ = c.fin_of(&succ_k);
                let fin_k = c.fin_of(&k);
                let (p_id, p) = b.fresh_local(fin_succ.clone());
                let (j_id, j) = b.fresh_local(fin_k.clone());
                let val_j = c.val(&k, &j);
                let val_p = c.val(&succ_k, &p);
                let prop = c.lt(&val_j, &val_p);
                let prem = if is_lt {
                    prop.clone()
                } else {
                    Expr::pi(BinderInfo::Default, prop.clone(), false_c.clone())
                };
                let (h_id, _h) = b.fresh_local(prem.clone());
                let lhs = Expr::apps(skip.clone(), [k.clone(), p.clone(), j.clone()]);
                let rhs = if is_lt {
                    c.cast_succ(&k, &j)
                } else {
                    skip_shift(&c, &k, &j)
                };
                let concl = Expr::apps(eq1.clone(), [fin_succ.clone(), lhs, rhs]);
                let r = b.mk_pi(h_id, BinderInfo::Default, prem, concl);
                let r = b.mk_pi(j_id, BinderInfo::Default, fin_k, r);
                let r = b.mk_pi(p_id, BinderInfo::Default, fin_succ, r);
                b.finish(b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r))
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (k_id, k) = b.fresh_local(c.nat.clone());
                let succ_k = c.succ(&k);
                let fin_succ = c.fin_of(&succ_k);
                let fin_k = c.fin_of(&k);
                let (p_id, p) = b.fresh_local(fin_succ.clone());
                let (j_id, j) = b.fresh_local(fin_k.clone());
                let val_j = c.val(&k, &j);
                let val_p = c.val(&succ_k, &p);
                let prop = c.lt(&val_j, &val_p);
                let prem = if is_lt {
                    prop.clone()
                } else {
                    Expr::pi(BinderInfo::Default, prop.clone(), false_c.clone())
                };
                let (h_id, h) = b.fresh_local(prem.clone());
                let discr = Expr::apps(c.nat_dec_lt.clone(), [val_j.clone(), val_p.clone()]);
                let then_v = c.cast_succ(&k, &j);
                let else_v = skip_shift(&c, &k, &j);
                // Lean order: @if_pos/neg.{1} {prop} {discr} (h) {Fin (k+1)} {then} {else}
                let lemma = if is_lt {
                    if_pos.clone()
                } else {
                    if_neg.clone()
                };
                let body = Expr::apps(lemma, [prop, discr, h, fin_succ.clone(), then_v, else_v]);
                let r = b.mk_lam(h_id, BinderInfo::Default, prem, body);
                let r = b.mk_lam(j_id, BinderInfo::Default, fin_k, r);
                let r = b.mk_lam(p_id, BinderInfo::Default, fin_succ, r);
                b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), r))
            };
            self.add_decl(Declaration::Theorem {
                name,
                level_params: vec![],
                type_: ty,
                value,
            })?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::ConstantKind;
    use crate::tc::TypeChecker;

    #[test]
    fn test_fin_skip_nth_type_checks_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_fin_skip_nth().expect("register");
        env.register_fin_skip_nth().expect("idempotent");

        let name = Name::from_string("Fin.skipNth");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Definition);
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("value"), &info.type_)
            .expect("Fin.skipNth must kernel-check");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(
            names.is_empty(),
            "Fin.skipNth must be axiom-free, got {names:?}"
        );
    }

    /// Ground sanity: `Fin.skipNth 1 (Fin.last 1) (Fin.last 0)` has val 0:
    /// `p = Fin.last 1 : Fin 2` (val 1), `j = Fin.last 0 : Fin 1` (val 0),
    /// `0 < 1` true → `castSucc` branch → val 0. The `ite` collapses on the
    /// ground `Nat.decLt 0 1` instance via a real ι-step.
    #[test]
    fn test_fin_skip_nth_ground_val() {
        let mut env = Environment::with_prelude();
        env.register_fin_skip_nth().expect("register");
        let tc = TypeChecker::with_mode(&env, env.mode());

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let one = Expr::app(succ.clone(), zero.clone());
        let fin_last = Expr::const_(Name::from_string("Fin.last"), vec![]);
        let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
        let skip = Expr::const_(Name::from_string("Fin.skipNth"), vec![]);
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );

        let p = Expr::app(fin_last.clone(), one.clone()); // Fin.last 1 : Fin 2, val 1
        let j = Expr::app(fin_last.clone(), zero.clone()); // Fin.last 0 : Fin 1, val 0
        let sk = Expr::apps(skip.clone(), [one.clone(), p, j]); // Fin 2
        let two = Expr::app(succ.clone(), one.clone());
        let sk_val = Expr::apps(fin_val.clone(), [two.clone(), sk]);
        let goal = Expr::apps(eq.clone(), [nat.clone(), sk_val, zero.clone()]);
        let refl = Expr::apps(eq_refl.clone(), [nat.clone(), zero.clone()]);
        tc.check_type(&refl, &goal)
            .expect("skipNth 1 (last 1) (last 0) should have val 0 (castSucc branch)");
    }

    #[test]
    fn test_fin_skip_nth_last_constructive_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_fin_skip_nth_last().expect("register");
        env.register_fin_skip_nth_last().expect("idempotent");

        let name = Name::from_string("Fin.skipNth_castSucc_of_last");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("value"), &info.type_)
            .expect("skipNth_castSucc_of_last must kernel-check");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
    }

    #[test]
    fn test_fin_skip_nth_collapse_constructive_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_fin_skip_nth_collapse().expect("register");
        env.register_fin_skip_nth_collapse().expect("idempotent");
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in ["Fin.skipNth_lt", "Fin.skipNth_ge"] {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem);
            tc.check_type(&info.value.clone().expect("value"), &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
            let deps = env.axiom_deps(&nm).expect("deps");
            let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
            assert!(names.is_empty(), "{name} must be axiom-free, got {names:?}");
        }
    }
}
