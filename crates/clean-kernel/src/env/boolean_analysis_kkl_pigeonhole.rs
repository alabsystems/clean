// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL pre-build — K4 pigeonhole layer (run 3b): the existence-from-sum-bound
//! lemma (the "averaging" / pigeonhole step).
//!
//! Stated in the multiplicative no-division (`succ m`) form, using the
//! constant-function sum `Fin.sum (succ m) (fun _ => c)` as the `c · n`-form (no
//! `natCast`, no division):
//!
//! ```text
//! Fin.exists_ge_of_sum_ge : ∀ (m : Nat) (c : Rat) (f : Fin (Nat.succ m) → Rat),
//!   Fin.sum (Nat.succ m) (fun _ => c) ≤ Fin.sum (Nat.succ m) f
//!     → ∃ i : Fin (Nat.succ m), c ≤ f i
//! ```
//!
//! ## Proof (constructive, empty domain-axiom closure)
//!
//! `Classical.em (∃ i, c ≤ f i)` (em is a kernel-checked Theorem with
//! foundational-only closure, so the result stays `Constructive`); `Or.rec`:
//!
//! - **yes-branch** (`∃ i, c ≤ f i`): returned directly — done.
//! - **no-branch** (`¬∃ i, c ≤ f i`): build `∀ i, f i < c` and derive a
//!   contradiction with the hypothesis:
//!     1. For each `i`: `¬(c ≤ f i)` is `fun (hci : c ≤ f i) =>
//!        hne (Exists.intro _ p i hci)` (the witness `i` would inhabit `∃`).
//!     2. `Rat.le_total c (f i) : Or (c ≤ f i)(f i ≤ c)`; the left disjunct is
//!        refuted by (1), so `f i ≤ c`; with `¬(c ≤ f i)`,
//!        `lt_iff.mpr ⟨f i ≤ c, ¬(c ≤ f i)⟩ : f i < c`.
//!     3. `Fin.sum_lt_sum m f (fun _ => c) (∀i, f i < c)
//!          : Fin.sum (succ m) f < Fin.sum (succ m) (fun _ => c)`.
//!     4. `Rat.lt_of_lt_of_le (Σf)(Σconst)(Σf) (step 3) hyp : Σf < Σf`, whose
//!        `lt_iff.mp` `.right` applied to `.left` is `False`; `False.elim`
//!        closes the existential goal.
//!
//! Every dependency (`Classical.em`, `Fin.sum_lt_sum`, `Rat.le_total`,
//! `Rat.lt_iff_le_not_le`, `Rat.lt_of_lt_of_le`, `Exists`/`Exists.intro`) has a
//! domain-axiom closure that is empty (em's foundational closure is filtered),
//! so the lemma is `Constructive`.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the pigeonhole construction.
struct PhConsts {
    order: OrderConsts,
    nat: Expr,
    nat_succ: Expr,
    fin: Expr,
    fin_sum: Expr,
    fin_sum_lt_sum: Expr,
    u1: Level,
}

impl PhConsts {
    fn new() -> Self {
        let u1 = Level::succ(Level::zero());
        Self {
            order: OrderConsts::new(),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin_sum_lt_sum: Expr::const_(Name::from_string("Fin.sum_lt_sum"), vec![]),
            u1,
        }
    }

    fn rat(&self) -> Expr {
        self.order.rat.clone()
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn fin_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat())
    }
    fn sum(&self, n: Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n, f])
    }
    fn rat_lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.lt"), vec![]), [a, b])
    }
    fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_le(a, b)
    }
    /// `Exists.{1} (Fin (succ m)) p`.
    fn exists_(&self, m: &Expr, p: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Exists"), vec![self.u1.clone()]),
            [self.fin_of(&self.succ(m)), p],
        )
    }
    /// `fun (i : Fin (succ m)) => c ≤ f i` — the existential predicate.
    fn pred_fn(&self, parent: &EnvDeclBuilder, m: &Expr, c: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_sm = self.fin_of(&self.succ(m));
        let (i_id, i) = b.fresh_local(fin_sm.clone());
        let body = self.rat_le(c.clone(), Expr::app(f.clone(), i));
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_sm, body))
    }
    /// `fun (_ : Fin (succ m)) => c` — the constant integrand.
    fn const_fn(&self, parent: &EnvDeclBuilder, m: &Expr, c: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_sm = self.fin_of(&self.succ(m));
        let (i_id, _i) = b.fresh_local(fin_sm.clone());
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_sm, c.clone()))
    }
}

// ── Prop plumbing ───────────────────────────────────────────────────────────

fn not_(p: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p)
}
/// `Not P` as a raw `Pi` (`P → False`), matching the shape Iff.mpr expects.
fn not_pi(parent: &EnvDeclBuilder, p: Expr) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(parent);
    let false_ = Expr::const_(Name::from_string("False"), vec![]);
    let (x_id, _) = ch.fresh_local(p.clone());
    ch.finish_child(ch.mk_pi(x_id, BinderInfo::Default, p, false_))
}
fn and_(p: Expr, q: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("And"), vec![]), [p, q])
}
fn and_intro(p: Expr, q: Expr, hp: Expr, hq: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.intro"), vec![]),
        [p, q, hp, hq],
    )
}
fn and_left(p: Expr, q: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [p, q, h],
    )
}
fn and_right(p: Expr, q: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.right"), vec![]),
        [p, q, h],
    )
}
fn iff_mp(lhs: Expr, rhs: Expr, hiff: Expr, hlhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Iff.mp"), vec![]),
        [lhs, rhs, hiff, hlhs],
    )
}
fn iff_mpr(lhs: Expr, rhs: Expr, hiff: Expr, hrhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Iff.mpr"), vec![]),
        [lhs, rhs, hiff, hrhs],
    )
}
fn lt_iff(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]),
        [a, b],
    )
}
fn false_elim(goal: Expr, h_false: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
        [goal, h_false],
    )
}

/// Case-split on `h_or : Or p q` into a (non-dependent) `goal`.
fn or_elim(
    parent: &EnvDeclBuilder,
    p: Expr,
    q: Expr,
    goal: Expr,
    h_or: Expr,
    h_left: Expr,
    h_right: Expr,
) -> Expr {
    let or_c = Expr::const_(Name::from_string("Or"), vec![]);
    let or_rec = Expr::const_(Name::from_string("Or.rec"), vec![]);
    let motive = {
        let mut m = EnvDeclBuilder::child_of(parent);
        let or_ty = Expr::apps(or_c, [p.clone(), q.clone()]);
        let (h_id, _) = m.fresh_local(or_ty.clone());
        let lam = m.mk_lam(h_id, BinderInfo::Default, or_ty, goal);
        m.finish_child(lam)
    };
    Expr::apps(or_rec, [p, q, motive, h_left, h_right, h_or])
}

impl Environment {
    /// `Fin.exists_ge_of_sum_ge : ∀ (m : Nat) (c : Rat) (f : Fin (succ m) → Rat),
    ///   Fin.sum (succ m) (fun _ => c) ≤ Fin.sum (succ m) f → ∃ i, c ≤ f i`.
    ///
    /// The pigeonhole / averaging step in the multiplicative no-division
    /// (`succ m`) form. Kernel-checked, constructive, empty closure. Idempotent.
    pub fn register_fin_exists_ge_of_sum_ge(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.exists_ge_of_sum_ge");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_fin_sum_lt_sum()?; // also brings Fin.sum, the lt spine
        self.init_exists()?; // Exists / Exists.intro
        self.init_classical()?; // Classical.em + Or + Or.rec (foundational closure)
        self.init_boolean_analysis_order_toolkit_b1c()?; // lt_of_lt_of_le, lt_iff
        self.init_boolean_analysis_order_toolkit()?; // le_total

        let c = PhConsts::new();
        let ty = build_type(&c);
        let value = build_proof(&c);
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

/// Type `∀ (m) (c : Rat) (f : Fin (succ m) → Rat),
///   Fin.sum (succ m) (fun _ => c) ≤ Fin.sum (succ m) f → ∃ i, c ≤ f i`.
fn build_type(c: &PhConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat());
    let fn_ty = c.fin_to_rat(&c.succ(&m));
    let (f_id, f) = b.fresh_local(fn_ty.clone());

    let const_c = c.const_fn(&b, &m, &cv);
    let sum_const = c.sum(c.succ(&m), const_c);
    let sum_f = c.sum(c.succ(&m), f.clone());
    let h_ty = c.rat_le(sum_const, sum_f);
    let (h_id, _) = b.fresh_local(h_ty.clone());

    let pred = c.pred_fn(&b, &m, &cv, &f);
    let concl = c.exists_(&m, pred);

    let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
    let e = b.mk_pi(f_id, BinderInfo::Default, fn_ty, e);
    let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the proof term for `Fin.exists_ge_of_sum_ge`.
fn build_proof(c: &PhConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat());
    let fn_ty = c.fin_to_rat(&c.succ(&m));
    let (f_id, f) = b.fresh_local(fn_ty.clone());

    let const_c = c.const_fn(&b, &m, &cv);
    let sum_const = c.sum(c.succ(&m), const_c.clone());
    let sum_f = c.sum(c.succ(&m), f.clone());
    let h_ty = c.rat_le(sum_const.clone(), sum_f.clone());
    let (h_id, h) = b.fresh_local(h_ty.clone());

    let pred = c.pred_fn(&b, &m, &cv, &f); // fun i => c ≤ f i
    let exists_goal = c.exists_(&m, pred.clone()); // ∃ i, c ≤ f i

    // em (∃ i, c ≤ f i) : Or (∃…) (¬∃…)
    let em = Expr::const_(Name::from_string("Classical.em"), vec![]);
    let h_em = Expr::app(em, exists_goal.clone());
    let not_exists = not_(exists_goal.clone());

    // Positive branch: λ (he : ∃ i, c ≤ f i) => he
    let em_pos = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (he_id, he) = ch.fresh_local(exists_goal.clone());
        ch.finish_child(ch.mk_lam(he_id, BinderInfo::Default, exists_goal.clone(), he))
    };

    // Negative branch: λ (hne : ¬∃ i, c ≤ f i) => <contradiction>
    let em_neg = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (hne_id, hne) = ch.fresh_local(not_exists.clone());

        // pointwise strict: fun (i : Fin (succ m)) => (f i < c)
        let ptwise = {
            let mut d = EnvDeclBuilder::child_of(&ch);
            let fin_sm = c.fin_of(&c.succ(&m));
            let (i_id, i) = d.fresh_local(fin_sm.clone());
            let c_le_fi = c.rat_le(cv.clone(), Expr::app(f.clone(), i.clone())); // c ≤ f i
            let fi_le_c = c.rat_le(Expr::app(f.clone(), i.clone()), cv.clone()); // f i ≤ c

            // ¬(c ≤ f i) = fun (hci : c ≤ f i) => hne (Exists.intro _ pred i hci)
            let not_c_le_fi = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let (hci_id, hci) = e.fresh_local(c_le_fi.clone());
                // Exists.intro.{1} (Fin (succ m)) pred i hci : ∃ j, c ≤ f j
                let exi = Expr::apps(
                    Expr::const_(Name::from_string("Exists.intro"), vec![c.u1.clone()]),
                    [c.fin_of(&c.succ(&m)), pred.clone(), i.clone(), hci],
                );
                let body = Expr::app(hne.clone(), exi); // hne exi : False
                e.finish_child(e.mk_lam(hci_id, BinderInfo::Default, c_le_fi.clone(), body))
            };

            // le_total c (f i) : Or (c ≤ f i)(f i ≤ c)
            let le_total = Expr::const_(Name::from_string("Rat.le_total"), vec![]);
            let h_total = Expr::apps(le_total, [cv.clone(), Expr::app(f.clone(), i.clone())]);

            // left branch: c ≤ f i contradicts not_c_le_fi → False.elim (f i < c)
            let tot_left = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let (hcfi_id, hcfi) = e.fresh_local(c_le_fi.clone());
                let h_false = Expr::app(not_c_le_fi.clone(), hcfi); // : False
                let body = false_elim(
                    c.rat_lt(Expr::app(f.clone(), i.clone()), cv.clone()),
                    h_false,
                );
                e.finish_child(e.mk_lam(hcfi_id, BinderInfo::Default, c_le_fi.clone(), body))
            };
            // right branch: f i ≤ c → lt_iff.mpr ⟨f i ≤ c, ¬(c ≤ f i)⟩ : f i < c
            let tot_right = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let (hfic_id, hfic) = e.fresh_local(fi_le_c.clone());
                let not_pi_c_le_fi = not_pi(&e, c_le_fi.clone());
                let and_proof = and_intro(
                    fi_le_c.clone(),
                    not_pi_c_le_fi.clone(),
                    hfic,
                    not_c_le_fi.clone(),
                );
                let body = iff_mpr(
                    c.rat_lt(Expr::app(f.clone(), i.clone()), cv.clone()),
                    and_(fi_le_c.clone(), not_pi_c_le_fi),
                    lt_iff(Expr::app(f.clone(), i.clone()), cv.clone()),
                    and_proof,
                );
                e.finish_child(e.mk_lam(hfic_id, BinderInfo::Default, fi_le_c.clone(), body))
            };

            let body = or_elim(
                &d,
                c_le_fi.clone(),
                fi_le_c.clone(),
                c.rat_lt(Expr::app(f.clone(), i.clone()), cv.clone()),
                h_total,
                tot_left,
                tot_right,
            );
            d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_sm, body))
        };

        // sum_lt : Fin.sum (succ m) f < Fin.sum (succ m) (fun _ => c)
        //   [Fin.sum_lt_sum m f (fun _ => c) ptwise]
        let sum_lt = Expr::apps(
            c.fin_sum_lt_sum.clone(),
            [m.clone(), f.clone(), const_c.clone(), ptwise],
        );

        // sum_lt_self : Σf < Σf  [lt_of_lt_of_le (Σf)(Σconst)(Σf) sum_lt hyp]
        let sum_lt_self = Expr::apps(
            Expr::const_(Name::from_string("Rat.lt_of_lt_of_le"), vec![]),
            [
                sum_f.clone(),
                sum_const.clone(),
                sum_f.clone(),
                sum_lt,
                h.clone(),
            ],
        );

        // mp sum_lt_self : (Σf ≤ Σf) ∧ ¬(Σf ≤ Σf) → False
        let le_ff = c.rat_le(sum_f.clone(), sum_f.clone());
        let not_le_ff = not_pi(&ch, le_ff.clone());
        let rhs_ff = and_(le_ff.clone(), not_le_ff.clone());
        let mp = iff_mp(
            c.rat_lt(sum_f.clone(), sum_f.clone()),
            rhs_ff,
            lt_iff(sum_f.clone(), sum_f.clone()),
            sum_lt_self,
        );
        let h_le_ff = and_left(le_ff.clone(), not_le_ff.clone(), mp.clone());
        let h_not_le_ff = and_right(le_ff.clone(), not_le_ff.clone(), mp);
        let h_false = Expr::app(h_not_le_ff, h_le_ff); // : False

        let body = false_elim(exists_goal.clone(), h_false);
        ch.finish_child(ch.mk_lam(hne_id, BinderInfo::Default, not_exists.clone(), body))
    };

    let body = or_elim(
        &b,
        exists_goal.clone(),
        not_exists.clone(),
        exists_goal.clone(),
        h_em,
        em_pos,
        em_neg,
    );

    let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
    let e = b.mk_lam(f_id, BinderInfo::Default, fn_ty, e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_exists_ge_of_sum_ge_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_fin_exists_ge_of_sum_ge()
            .expect("register_fin_exists_ge_of_sum_ge");
        let name = Name::from_string("Fin.exists_ge_of_sum_ge");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("exists_ge_of_sum_ge proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "exists_ge_of_sum_ge must be Constructive (em's closure is foundational)"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "exists_ge_of_sum_ge's transitive domain-axiom closure must be empty"
        );
    }

    #[test]
    fn test_exists_ge_of_sum_ge_idempotent() {
        let mut env = Environment::new();
        env.register_fin_exists_ge_of_sum_ge().expect("first");
        env.register_fin_exists_ge_of_sum_ge()
            .expect("second (idempotent)");
    }
}
