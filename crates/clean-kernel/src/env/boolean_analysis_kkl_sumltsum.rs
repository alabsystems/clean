// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL pre-build — K4 pigeonhole layer (run 3a): strict finite-sum
//! monotonicity.
//!
//! ```text
//! Fin.sum_lt_sum : ∀ (m : Nat) (f g : Fin (Nat.succ m) → Rat),
//!   (∀ i : Fin (Nat.succ m), f i < g i)
//!     → Fin.sum (Nat.succ m) f < Fin.sum (Nat.succ m) g
//! ```
//!
//! Stated in the `Nat.succ m` (non-empty) form — the consumable shape, with no
//! separate `0 < n` premise (the empty sum is not strictly below itself, so
//! the lemma is simply about positive-length sums, which is exactly what the
//! pigeonhole and the KKL assembly apply it at, since `2^n = Nat.succ _`).
//!
//! ## Proof (constructive, empty domain-axiom closure)
//!
//! No induction is needed: `Fin.sum_succ` peels the last coordinate off both
//! sides, and the prefix is handled non-strictly while the last coordinate
//! carries the strictness.
//!
//! `Fin.sum (succ m) f = Fin.sum m (f∘castSucc) + f(last m)`   [Fin.sum_succ]
//! `Fin.sum (succ m) g = Fin.sum m (g∘castSucc) + g(last m)`   [Fin.sum_succ]
//!
//! 1. **prefix ≤**: `Fin.sum m (f∘cast) ≤ Fin.sum m (g∘cast)` via `Fin.sum_le`,
//!    where the pointwise `(f∘cast)(i) ≤ (g∘cast)(i)` is the `And.left` of
//!    `Iff.mp (lt_iff …) (hyp (castSucc m i))` (le-component of the strict
//!    hypothesis).
//! 2. **last <**: `f(last m) < g(last m)` is `hyp (last m)`.
//! 3. **combine** (prefix `≤` + last `<` ⟹ sum `<`) via the mixed
//!    `Rat.lt_of_le_of_lt` chain through the intermediate `Σg∘cast + f last`:
//!      - le_step : `Σf∘cast + f last ≤ Σg∘cast + f last`
//!        [`Rat.add_le_add_right` on prefix (1)]
//!      - lt_step : `Σg∘cast + f last < Σg∘cast + g last`
//!        [`Rat.add_lt_add_left` on last (2)]
//!      - `Rat.lt_of_le_of_lt (Σf∘cast + f last)(Σg∘cast + f last)
//!                            (Σg∘cast + g last) le_step lt_step`
//!        gives `(Σf∘cast + f last) < (Σg∘cast + g last)`.
//! 4. **transport endpoints** to `Fin.sum (succ m) f` / `g` via
//!    `Eq.symm (Fin.sum_succ m f)` / `…g` lifted through `Eq.subst` over
//!    `Rat.lt` (both `Fin.sum (succ m) _` δ-unfold to the peeled `Σ_∘cast + _
//!    last` form `Fin.sum_succ` names).
//!
//! Every dependency (`Fin.sum_succ`, `Fin.sum_le`, `Rat.add_le_add_right`,
//! `Rat.add_lt_add_left`, `Rat.lt_of_le_of_lt`, `Rat.lt_iff_le_not_le`) is
//! `Constructive` with empty closure, so the lemma is too.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the strict-sum construction.
struct SumLtConsts {
    order: OrderConsts,
    nat: Expr,
    nat_succ: Expr,
    fin: Expr,
    fin_sum: Expr,
    fin_sum_succ: Expr,
    fin_sum_le: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    eq_subst: Expr,
}

impl SumLtConsts {
    fn new() -> Self {
        let u1 = Level::succ(Level::zero());
        Self {
            order: OrderConsts::new(),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin_sum_succ: Expr::const_(Name::from_string("Fin.sum_succ"), vec![]),
            fin_sum_le: Expr::const_(Name::from_string("Fin.sum_le"), vec![]),
            fin_cast_succ: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![u1]),
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
    fn add(&self, a: Expr, b: Expr) -> Expr {
        self.order.add(a, b)
    }
    /// `fun (i : Fin m) => f (Fin.castSucc m i)` — the cast-prefix function.
    fn cast_fn(&self, parent: &EnvDeclBuilder, m: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_m = self.fin_of(m);
        let (i_id, i) = b.fresh_local(fin_m.clone());
        let cast_i = Expr::apps(self.fin_cast_succ.clone(), [m.clone(), i]);
        let body = Expr::app(f.clone(), cast_i);
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_m, body))
    }
    fn last(&self, m: &Expr) -> Expr {
        Expr::app(self.fin_last.clone(), m.clone())
    }
    /// `Eq.subst.{1} @Rat motive @a @b h_eq h_motive_a : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_motive_a: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat(), motive, a, b, h_eq, h_motive_a],
        )
    }
}

/// `Iff.mp` plumbing for extracting the `≤` from a `<`.
fn iff_mp(lhs: Expr, rhs: Expr, hiff: Expr, hlhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Iff.mp"), vec![]),
        [lhs, rhs, hiff, hlhs],
    )
}
fn and_left(p: Expr, q: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [p, q, h],
    )
}
fn not_(p: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p)
}
fn and_(p: Expr, q: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("And"), vec![]), [p, q])
}
fn lt_iff(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]),
        [a, b],
    )
}

impl Environment {
    /// `Fin.sum_lt_sum : ∀ (m : Nat) (f g : Fin (succ m) → Rat),
    ///   (∀ i, f i < g i) → Fin.sum (succ m) f < Fin.sum (succ m) g`.
    ///
    /// Strict finite-sum monotonicity in the non-empty (`succ m`) form.
    /// Kernel-checked, constructive, empty closure. Idempotent.
    pub fn register_fin_sum_lt_sum(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_lt_sum");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_fin_sum()?; // Fin.sum, Fin.sum_succ, Fin.sum_le, castSucc, last
                              // Rat.add_lt_add_left, Rat.add_le_add_right, Rat.lt_of_le_of_lt, lt_iff.
        self.init_boolean_analysis_kkl_strictadd2()?;
        self.register_rat_add_le_add_right()?;
        self.init_boolean_analysis_order_toolkit_b1c()?;

        let c = SumLtConsts::new();
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

/// `∀ i : Fin (succ m), f i < g i` — the strict pointwise hypothesis.
fn pointwise_lt(c: &SumLtConsts, parent: &EnvDeclBuilder, m: &Expr, f: &Expr, g: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_sm = c.fin_of(&c.succ(m));
    let (i_id, i) = b.fresh_local(fin_sm.clone());
    let body = c.rat_lt(Expr::app(f.clone(), i.clone()), Expr::app(g.clone(), i));
    b.finish_child(b.mk_pi(i_id, BinderInfo::Default, fin_sm, body))
}

/// Type `∀ (m) (f g : Fin (succ m) → Rat), (∀ i, f i < g i)
///   → Fin.sum (succ m) f < Fin.sum (succ m) g`.
fn build_type(c: &SumLtConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let fn_ty = c.fin_to_rat(&c.succ(&m));
    let (f_id, f) = b.fresh_local(fn_ty.clone());
    let (g_id, g) = b.fresh_local(fn_ty.clone());
    let hyp = pointwise_lt(c, &b, &m, &f, &g);
    let (h_id, _) = b.fresh_local(hyp.clone());
    let concl = c.rat_lt(c.sum(c.succ(&m), f.clone()), c.sum(c.succ(&m), g.clone()));
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(g_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_pi(f_id, BinderInfo::Default, fn_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the proof term for `Fin.sum_lt_sum`.
fn build_proof(c: &SumLtConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let fn_ty = c.fin_to_rat(&c.succ(&m));
    let (f_id, f) = b.fresh_local(fn_ty.clone());
    let (g_id, g) = b.fresh_local(fn_ty.clone());
    let hyp = pointwise_lt(c, &b, &m, &f, &g);
    let (h_id, h) = b.fresh_local(hyp.clone());

    // Prefix functions f∘cast, g∘cast : Fin m → Rat.
    let f_cast = c.cast_fn(&b, &m, &f);
    let g_cast = c.cast_fn(&b, &m, &g);
    let sum_f_cast = c.sum(m.clone(), f_cast.clone()); // Σ f∘cast
    let sum_g_cast = c.sum(m.clone(), g_cast.clone()); // Σ g∘cast

    // Last coordinates.
    let f_last = Expr::app(f.clone(), c.last(&m)); // f(last m)
    let g_last = Expr::app(g.clone(), c.last(&m)); // g(last m)

    // ── prefix ≤ via Fin.sum_le ────────────────────────────────────────────
    // pointwise le : fun (i : Fin m) =>
    //   And.left (Iff.mp (lt_iff (f(cast i))(g(cast i))) (h (cast i)))
    let pointwise_le = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let fin_m = c.fin_of(&m);
        let (i_id, i) = ch.fresh_local(fin_m.clone());
        let cast_i = Expr::apps(c.fin_cast_succ.clone(), [m.clone(), i]);
        let fci = Expr::app(f.clone(), cast_i.clone()); // f(cast i) = (f∘cast) i
        let gci = Expr::app(g.clone(), cast_i.clone()); // g(cast i) = (g∘cast) i
        let h_lt = Expr::app(h.clone(), cast_i); // h (cast i) : f(cast i) < g(cast i)
        let rhs = and_(
            c.rat_le(fci.clone(), gci.clone()),
            not_(c.rat_le(gci.clone(), fci.clone())),
        );
        let mp = iff_mp(
            c.rat_lt(fci.clone(), gci.clone()),
            rhs,
            lt_iff(fci.clone(), gci.clone()),
            h_lt,
        );
        let le = and_left(
            c.rat_le(fci.clone(), gci.clone()),
            not_(c.rat_le(gci.clone(), fci.clone())),
            mp,
        );
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_m, le))
    };
    // Fin.sum_le m (f∘cast) (g∘cast) pointwise_le : Σf∘cast ≤ Σg∘cast
    let prefix_le = Expr::apps(
        c.fin_sum_le.clone(),
        [m.clone(), f_cast.clone(), g_cast.clone(), pointwise_le],
    );

    // ── last < : h (last m) : f(last m) < g(last m) ────────────────────────
    let last_lt = Expr::app(h.clone(), c.last(&m));

    // ── combine: le_step then lt_step, via lt_of_le_of_lt ──────────────────
    // le_step : (Σf∘cast + f last) ≤ (Σg∘cast + f last)
    //   [Rat.add_le_add_right a b c h, app order a b c h]
    let le_step = Expr::apps(
        Expr::const_(Name::from_string("Rat.add_le_add_right"), vec![]),
        [
            sum_f_cast.clone(),
            sum_g_cast.clone(),
            f_last.clone(),
            prefix_le,
        ],
    );
    // lt_step : (Σg∘cast + f last) < (Σg∘cast + g last)
    //   [Rat.add_lt_add_left (f last)(g last)(Σg∘cast) last_lt]
    let lt_step = Expr::apps(
        Expr::const_(Name::from_string("Rat.add_lt_add_left"), vec![]),
        [f_last.clone(), g_last.clone(), sum_g_cast.clone(), last_lt],
    );

    let lhs_add = c.add(sum_f_cast.clone(), f_last.clone()); // Σf∘cast + f last
    let mid_add = c.add(sum_g_cast.clone(), f_last.clone()); // Σg∘cast + f last
    let rhs_add = c.add(sum_g_cast.clone(), g_last.clone()); // Σg∘cast + g last

    // lt_combined : (Σf∘cast + f last) < (Σg∘cast + g last)
    //   [Rat.lt_of_le_of_lt lhs_add mid_add rhs_add le_step lt_step]
    let lt_combined = Expr::apps(
        Expr::const_(Name::from_string("Rat.lt_of_le_of_lt"), vec![]),
        [lhs_add.clone(), mid_add, rhs_add.clone(), le_step, lt_step],
    );

    // ── transport endpoints to Fin.sum (succ m) f / g via Fin.sum_succ ─────
    // Fin.sum_succ m f : Fin.sum (succ m) f = (Σf∘cast + f last)
    //   so Eq.symm gives (Σf∘cast + f last) = Fin.sum (succ m) f, used as the
    //   equation to rewrite the LHS of lt_combined.
    let sum_succ_f = Expr::apps(c.fin_sum_succ.clone(), [m.clone(), f.clone()]);
    let sum_succ_g = Expr::apps(c.fin_sum_succ.clone(), [m.clone(), g.clone()]);
    let sum_sm_f = c.sum(c.succ(&m), f.clone()); // Fin.sum (succ m) f
    let sum_sm_g = c.sum(c.succ(&m), g.clone()); // Fin.sum (succ m) g

    // Eq.symm sum_succ_f : (Σf∘cast + f last) = Fin.sum (succ m) f
    let eq_symm = Expr::const_(
        Name::from_string("Eq.symm"),
        vec![Level::succ(Level::zero())],
    );
    let symm_f = Expr::apps(
        eq_symm.clone(),
        [c.rat(), sum_sm_f.clone(), lhs_add.clone(), sum_succ_f],
    );
    // rewrite LHS : motive_l := fun t => Rat.lt t (Σg∘cast + g last)
    let motive_l = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.rat());
        let body = c.rat_lt(t, rhs_add.clone());
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
    };
    // subst motive_l (lhs_add) (Fin.sum (succ m) f) symm_f lt_combined
    //   : Rat.lt (Fin.sum (succ m) f) (Σg∘cast + g last)
    let step_l = c.subst(motive_l, lhs_add, sum_sm_f.clone(), symm_f, lt_combined);

    // Eq.symm sum_succ_g : (Σg∘cast + g last) = Fin.sum (succ m) g
    let symm_g = Expr::apps(
        eq_symm,
        [c.rat(), sum_sm_g.clone(), rhs_add.clone(), sum_succ_g],
    );
    // rewrite RHS : motive_r := fun t => Rat.lt (Fin.sum (succ m) f) t
    let motive_r = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.rat());
        let body = c.rat_lt(sum_sm_f.clone(), t);
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
    };
    let body = c.subst(motive_r, rhs_add, sum_sm_g, symm_g, step_l);

    let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
    let e = b.mk_lam(g_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_lam(f_id, BinderInfo::Default, fn_ty, e);
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
    fn test_fin_sum_lt_sum_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_fin_sum_lt_sum()
            .expect("register_fin_sum_lt_sum");
        let name = Name::from_string("Fin.sum_lt_sum");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("fin_sum_lt_sum proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "fin_sum_lt_sum must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "fin_sum_lt_sum's transitive axiom closure must be empty"
        );
    }

    #[test]
    fn test_fin_sum_lt_sum_idempotent() {
        let mut env = Environment::new();
        env.register_fin_sum_lt_sum().expect("first");
        env.register_fin_sum_lt_sum().expect("second (idempotent)");
    }
}
