// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Nat.strongRecOnLt` — strong (course-of-values) induction on `Nat` for a
//! `Prop`-valued motive, built directly on the kernel recursor `Acc.rec` over
//! the axiom-free accessibility witness `Nat.accNatLt`. NO `WellFounded.fix`
//! (which the audit lists as foundational) — `Acc.rec` keeps the closure empty.
//!
//! ```text
//! Nat.strongRecOnLt :
//!   (M : Nat → Prop)
//!   → ((x : Nat) → ((y : Nat) → Nat.lt y x → M y) → M x)
//!   → (n : Nat) → M n
//! ```
//!
//! This is the recursion principle the `Fin.sum_reindex_involution` keystone
//! needs: its 2-cycle branch recurses at size `k-1` (a decrease by two), which
//! plain `Nat.rec` cannot express but strong induction handles uniformly.
//!
//! ## Construction
//!
//! `fun M step n => @Acc.rec.{0,1} Nat Nat.lt C STEP n (Nat.accNatLt n)` with
//! - motive `C := fun (x : Nat) (_ : Acc Nat.lt x) => M x` (ignores the Acc
//!   proof, so the recursion is genuine strong induction);
//! - `STEP := fun (x) (h : ∀ y, Nat.lt y x → Acc Nat.lt y)
//!     (ih : ∀ y (p : Nat.lt y x), M y) => step x ih`.
//!   `Acc.rec`'s `ih` argument has type `∀ y (p : Nat.lt y x), C y (h y p)`
//!   which ≡ `∀ y (p : Nat.lt y x), M y` because `C` discards its Acc argument.
//!
//! Mentions only `Acc`/`Acc.rec` (kernel recursor), `Nat`/`Nat.lt`/
//! `Nat.accNatLt` (axiom-free). Empty admitted-axiom closure.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Nat.strongRecOnLt` (see module docs). Constructive Definition,
    /// empty axiom closure. Idempotent.
    pub(crate) fn register_nat_strong_rec_on_lt(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.strongRecOnLt");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_nat()?;
        self.init_lt()?;
        self.init_well_founded()?; // Acc / Acc.intro / Acc.rec
        self.init_nat_lt_wf()?; // Nat.accNatLt (+ Nat.lt_wf, lbound)

        let l0 = Level::zero();
        let l1 = Level::succ(l0.clone());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let acc = Expr::const_(Name::from_string("Acc"), vec![l1.clone()]);
        // @Acc.rec.{motive_level=0, alpha_level=1} — motive returns M y : Prop (0),
        // alpha = Nat lives in Sort 1.
        let acc_rec = Expr::const_(Name::from_string("Acc.rec"), vec![l0.clone(), l1.clone()]);
        let acc_nat_lt = Expr::const_(Name::from_string("Nat.accNatLt"), vec![]);
        let prop = Expr::sort(l0.clone());

        let nat_to_prop = Expr::pi(BinderInfo::Default, nat.clone(), prop.clone());
        let lt = |a: Expr, b: Expr| Expr::apps(nat_lt.clone(), [a, b]);
        let acc_lt = |x: Expr| Expr::apps(acc.clone(), [nat.clone(), nat_lt.clone(), x]);

        // step type: (x : Nat) → ((y : Nat) → Nat.lt y x → M y) → M x
        let step_ty = |b: &EnvDeclBuilder, m: &Expr| -> Expr {
            let mut s = EnvDeclBuilder::child_of(b);
            let (x_id, x) = s.fresh_local(nat.clone());
            let ih_ty = {
                let mut t = EnvDeclBuilder::child_of(&s);
                let (y_id, y) = t.fresh_local(nat.clone());
                let inner = {
                    let mut u = EnvDeclBuilder::child_of(&t);
                    let lt_ty = lt(y.clone(), x.clone());
                    let (p_id, _p) = u.fresh_local(lt_ty.clone());
                    let my = Expr::app(m.clone(), y.clone());
                    u.finish_child(u.mk_pi(p_id, BinderInfo::Default, lt_ty, my))
                };
                t.finish_child(t.mk_pi(y_id, BinderInfo::Default, nat.clone(), inner))
            };
            let mx = Expr::app(m.clone(), x.clone());
            let (ih_id, _ih) = s.fresh_local(ih_ty.clone());
            let inner = s.mk_pi(ih_id, BinderInfo::Default, ih_ty, mx);
            s.finish_child(s.mk_pi(x_id, BinderInfo::Default, nat.clone(), inner))
        };

        // ── Type: (M : Nat → Prop) → step_ty → (n : Nat) → M n
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat_to_prop.clone());
            let sty = step_ty(&b, &m);
            let (s_id, _s) = b.fresh_local(sty.clone());
            let (n_id, n) = b.fresh_local(nat.clone());
            let concl = Expr::app(m.clone(), n.clone());
            let e = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), concl);
            let e = b.mk_pi(s_id, BinderInfo::Default, sty, e);
            let e = b.mk_pi(m_id, BinderInfo::Default, nat_to_prop.clone(), e);
            b.finish(e)
        };

        // ── Value
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat_to_prop.clone());
            let sty = step_ty(&b, &m);
            let (s_id, step) = b.fresh_local(sty.clone());
            let (n_id, n) = b.fresh_local(nat.clone());

            // C := fun (x : Nat) (_ : Acc Nat.lt x) => M x
            let cmotive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = d.fresh_local(nat.clone());
                let acc_x = acc_lt(x.clone());
                let (a_id, _a) = d.fresh_local(acc_x.clone());
                let mx = Expr::app(m.clone(), x.clone());
                let inner = d.mk_lam(a_id, BinderInfo::Default, acc_x, mx);
                d.finish_child(d.mk_lam(x_id, BinderInfo::Default, nat.clone(), inner))
            };

            // STEP := fun (x) (h : ∀ y, Nat.lt y x → Acc Nat.lt y)
            //             (ih : ∀ y (p : Nat.lt y x), M y) => step x ih
            let step_fn = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = d.fresh_local(nat.clone());
                // h : ∀ y, Nat.lt y x → Acc Nat.lt y
                let h_ty = {
                    let mut t = EnvDeclBuilder::child_of(&d);
                    let (y_id, y) = t.fresh_local(nat.clone());
                    let inner = {
                        let mut u = EnvDeclBuilder::child_of(&t);
                        let lt_ty = lt(y.clone(), x.clone());
                        let (p_id, _p) = u.fresh_local(lt_ty.clone());
                        let acc_y = acc_lt(y.clone());
                        u.finish_child(u.mk_pi(p_id, BinderInfo::Default, lt_ty, acc_y))
                    };
                    t.finish_child(t.mk_pi(y_id, BinderInfo::Default, nat.clone(), inner))
                };
                let (h_id, _h) = d.fresh_local(h_ty.clone());
                // ih : ∀ y (p : Nat.lt y x), M y  (≡ ∀ y p, C y (h y p))
                let ih_ty = {
                    let mut t = EnvDeclBuilder::child_of(&d);
                    let (y_id, y) = t.fresh_local(nat.clone());
                    let inner = {
                        let mut u = EnvDeclBuilder::child_of(&t);
                        let lt_ty = lt(y.clone(), x.clone());
                        let (p_id, _p) = u.fresh_local(lt_ty.clone());
                        let my = Expr::app(m.clone(), y.clone());
                        u.finish_child(u.mk_pi(p_id, BinderInfo::Default, lt_ty, my))
                    };
                    t.finish_child(t.mk_pi(y_id, BinderInfo::Default, nat.clone(), inner))
                };
                let (ih_id, ih) = d.fresh_local(ih_ty.clone());
                // step x ih : M x
                let body = Expr::apps(step.clone(), [x.clone(), ih.clone()]);
                let r = d.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                let r = d.mk_lam(h_id, BinderInfo::Default, h_ty, r);
                d.finish_child(d.mk_lam(x_id, BinderInfo::Default, nat.clone(), r))
            };

            // @Acc.rec.{0,1} Nat Nat.lt C STEP n (Nat.accNatLt n)
            let acc_n = Expr::app(acc_nat_lt.clone(), n.clone());
            let rec_app = Expr::apps(
                acc_rec.clone(),
                [
                    nat.clone(),
                    nat_lt.clone(),
                    cmotive,
                    step_fn,
                    n.clone(),
                    acc_n,
                ],
            );
            let e = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), rec_app);
            let e = b.mk_lam(s_id, BinderInfo::Default, sty, e);
            let e = b.mk_lam(m_id, BinderInfo::Default, nat_to_prop, e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_,
            value,
            is_reducible: true,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::ConstantKind;
    use crate::tc::TypeChecker;

    #[test]
    fn test_nat_strong_rec_on_lt_constructive_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_nat_strong_rec_on_lt().expect("register");
        env.register_nat_strong_rec_on_lt().expect("idempotent");

        let name = Name::from_string("Nat.strongRecOnLt");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Definition);
        let value = info.value.clone().expect("value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("strongRecOnLt must kernel-check");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
    }
}
