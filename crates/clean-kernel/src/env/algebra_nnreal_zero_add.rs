// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — `NNReal.zero_add` (`NNReal.add NNReal.zero x = x`): the
//! additive-zero identity the `NNReal.finSum_add` base case (L3 sub-lemma) needs.
//!
//! # Why this module exists (L3 base brick)
//!
//! The `NNReal.finSum_add` four-way split (`Σ(A+B) = ΣA + ΣB`) is a `Nat.rec`
//! induction whose BASE case `finSum 0 (A+B) = finSum 0 A + finSum 0 B` reduces to
//! `NNReal.zero = NNReal.add NNReal.zero NNReal.zero`. The carrier never shipped a
//! `0+x=x` lemma (the `norm43_card_zero` brick keeps the `add 0 _` explicit
//! precisely because `NNReal.zero_add` was absent). This module supplies it.
//!
//! # The brick (axiom-free, kernel-checked)
//!
//! ```text
//!   NNReal.zero_add : ∀ x : NNReal, NNReal.add NNReal.zero x = x
//! ```
//!
//! # Proof shape (mirrors `NNReal.mul_zero`)
//!
//! `Quot.ind` on `x` reduces to a CauSeq representative `fx`; the goal becomes
//! `Eq NNReal (mk (CauSeq.add zc fx)) (mk fx)` (with `zc := CauSeq.const (NNRat.ofRat
//! 0)`), closed by `Quot.sound` on the `Equiv (CauSeq.add zc fx) fx`. The Equiv's
//! pointwise val-equality is just `Rat.zero_add (val (seq fx m))`: because
//! `NNRat.val_add` holds by `refl`, `val(seq(add zc fx) m) ≡ val(zc m) + val(fx m)
//! ≡ 0 + val(fx m)`, which `Rat.zero_add` identifies with `val(fx m) ≡ val(seq fx
//! m)`. The two `<…+ε` bounds then transport `vL ↔ vR` along that equality
//! (`Eq.subst` + `Rat.add_lt_add_left`/`Rat.add_zero`), exactly as `mul_zero`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Handles for `NNReal.zero_add` (the `Quot.sound`/CauSeq surface).
struct ZeroAddConsts {
    nat: Expr,
    nat_zero: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_lt: Expr,
    rat_add: Expr,
    rat_add_lt_add_left: Expr,
    rat_add_zero: Expr,
    rat_zero_add: Expr,
    nnrat_val: Expr,
    nnrat_of_rat: Expr,
    nnreal_zero: Expr,
    causeq: Expr,
    causeq_seq: Expr,
    causeq_equiv: Expr,
    causeq_add: Expr,
    causeq_const: Expr,
    nat_le: Expr,
    exists_intro: Expr,
    and_c: Expr,
    and_intro: Expr,
    eq1: Expr,
    eq_symm1: Expr,
    eq_subst1: Expr,
    #[cfg(test)]
    quot_mk: Expr,
    quot_sound: Expr,
    quot_ind: Expr,
}

impl ZeroAddConsts {
    fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_lt: k("Rat.lt"),
            rat_add: k("Rat.add"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_add_zero: k("Rat.add_zero"),
            rat_zero_add: k("Rat.zero_add"),
            nnrat_val: k("NNRat.val"),
            nnrat_of_rat: k("NNRat.ofRat"),
            nnreal_zero: k("NNReal.zero"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            causeq_add: k("NNReal.CauSeq.add"),
            causeq_const: k("NNReal.CauSeq.const"),
            nat_le: k("Nat.le"),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![lvl1.clone()]),
            and_c: k("And"),
            and_intro: k("And.intro"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1.clone()]),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1.clone()]),
            #[cfg(test)]
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![lvl1.clone()]),
            quot_sound: Expr::const_(Name::from_string("Quot.sound"), vec![lvl1.clone()]),
            quot_ind: Expr::const_(Name::from_string("Quot.ind"), vec![lvl1]),
        }
    }

    fn nnreal(&self) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Quot"), vec![Level::succ(Level::zero())]),
            [self.causeq.clone(), self.causeq_equiv.clone()],
        )
    }
    fn nnreal_add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.add"), vec![]),
            [a, b],
        )
    }
    fn eq_nnreal(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nnreal(), a, b])
    }
    fn radd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn val(&self, q: Expr) -> Expr {
        Expr::app(self.nnrat_val.clone(), q)
    }
    fn seq_at(&self, x: &Expr, n: &Expr) -> Expr {
        Expr::app(Expr::app(self.causeq_seq.clone(), x.clone()), n.clone())
    }
    fn vseq(&self, x: &Expr, n: &Expr) -> Expr {
        self.val(self.seq_at(x, n))
    }
    fn causeq_add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_add.clone(), [a, b])
    }
    /// `NNReal.CauSeq.const (NNRat.ofRat 0 h0)` — the zero const seq.
    fn zero_const(&self, h0: &Expr) -> Expr {
        let zero_nn = Expr::apps(
            self.nnrat_of_rat.clone(),
            [self.rat_zero.clone(), h0.clone()],
        );
        Expr::app(self.causeq_const.clone(), zero_nn)
    }
    fn quot_sound(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.quot_sound.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), a, b, h],
        )
    }
    fn eq_symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.rat.clone(), a, b, h])
    }
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
}

impl Environment {
    /// Register `NNReal.zero_add`. Idempotent; foundational-only closure.
    pub fn init_algebra_nnreal_zero_add(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_finsum()?; // NNReal.zero, NNReal.add, carrier
        self.init_rat_field_inst()?; // Rat.zero_add, Rat.add_zero
        self.register_rat_add_lt_add_left()?; // Rat.add_lt_add_left
        self.init_eq()?;

        let name = Name::from_string("NNReal.zero_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = ZeroAddConsts::new();
        let nnreal = c.nnreal();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(nnreal.clone());
            let lhs = c.nnreal_add(c.nnreal_zero.clone(), x.clone());
            let concl = c.eq_nnreal(lhs, x.clone());
            let e = b.mk_pi(x_id, BinderInfo::Default, nnreal.clone(), concl);
            b.finish(e)
        };
        let value = build_zero_add_value(&c, &nnreal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build `NNReal.zero_add` value via `Quot.ind` on `x`.
fn build_zero_add_value(c: &ZeroAddConsts, nnreal: &Expr) -> Expr {
    // 0 ≤ 0 witness inside NNReal.zero (NNRat.ofRat 0 _).
    let rat_le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
    let h0 = Expr::app(rat_le_refl, c.rat_zero.clone());

    let mut b = EnvDeclBuilder::new();
    let (xv_id, xv) = b.fresh_local(nnreal.clone());

    // Quot.ind motive: fun y => Eq NNReal (add NNReal.zero y) y.
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (y_id, y) = mb.fresh_local(nnreal.clone());
        let lhs = c.nnreal_add(c.nnreal_zero.clone(), y.clone());
        let body = c.eq_nnreal(lhs, y.clone());
        mb.finish_child(mb.mk_lam(y_id, BinderInfo::Default, nnreal.clone(), body))
    };
    // minor fx : Eq NNReal (add NNReal.zero (mk fx)) (mk fx).
    //   add NNReal.zero (mk fx) ≡ mk (CauSeq.add zc fx) ; (mk fx) is the RHS.
    //   Close by Quot.sound on Equiv (CauSeq.add zc fx) fx.
    let minor = {
        let mut mf = EnvDeclBuilder::child_of(&b);
        let (fx_id, fx) = mf.fresh_local(c.causeq.clone());
        let zc = c.zero_const(&h0);
        let cl = c.causeq_add(zc.clone(), fx.clone());
        let cr = fx.clone();
        let equiv = build_zero_add_equiv(c, &mf, &fx, &h0);
        let body = c.quot_sound(cl, cr, equiv);
        mf.finish_child(mf.mk_lam(fx_id, BinderInfo::Default, c.causeq.clone(), body))
    };
    let ind = Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            xv.clone(),
        ],
    );
    let e = b.mk_lam(xv_id, BinderInfo::Default, nnreal.clone(), ind);
    b.finish(e)
}

/// Build `Equiv (CauSeq.add zc fx) fx`. Pointwise: `val(seq(add zc fx) m) ≡
/// val(zc m) + val(fx m) ≡ 0 + val(fx m)`, and `Rat.zero_add` identifies that with
/// `val(fx m) ≡ val(seq fx m)`.
fn build_zero_add_equiv(c: &ZeroAddConsts, parent: &EnvDeclBuilder, fx: &Expr, h0: &Expr) -> Expr {
    let zc = c.zero_const(h0);
    let cl = c.causeq_add(zc.clone(), fx.clone());
    let cr = fx.clone();

    let mut b = EnvDeclBuilder::child_of(parent);
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    let pred = build_za_pred(c, &b, &cl, &cr, &eps);
    let witness = {
        let mut bw = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = bw.fresh_local(c.nat.clone());
        let hle_ty = c.nat_le(c.nat_zero.clone(), m.clone());
        let (hle_id, _hle) = bw.fresh_local(hle_ty.clone());

        let vl = c.vseq(&cl, &m);
        let vr = c.vseq(&cr, &m);
        // h_eq : vL = vR.  vL ≡ 0 + val(fx m) (NNRat.val_add holds by refl,
        // val(zc m) ≡ 0); vR ≡ val(fx m). So `Rat.zero_add vR : 0 + vR = vR`
        // is DEFEQ to `vL = vR`.
        let h_eq = Expr::app(c.rat_zero_add.clone(), vr.clone());

        // vL < vR + ε from vR < vR+ε, subst vR → vL via symm h_eq.
        let vr_eps = c.radd(vr.clone(), eps.clone());
        let vr_lt = build_self_lt_add(c, &bw, &vr, &eps, &hpos);
        let motive_l = {
            let mut mb = EnvDeclBuilder::child_of(&bw);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.lt(t, vr_eps.clone());
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let left = c.subst_rat(
            motive_l,
            vr.clone(),
            vl.clone(),
            c.eq_symm_rat(vl.clone(), vr.clone(), h_eq.clone()),
            vr_lt,
        );

        // vR < vL + ε from vL < vL+ε, subst LHS vL → vR via h_eq.
        let vl_eps = c.radd(vl.clone(), eps.clone());
        let vl_lt = build_self_lt_add(c, &bw, &vl, &eps, &hpos);
        let motive_r = {
            let mut mb = EnvDeclBuilder::child_of(&bw);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.lt(t, vl_eps.clone());
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let right = c.subst_rat(motive_r, vl.clone(), vr.clone(), h_eq, vl_lt);

        let l_ty = c.lt(vl.clone(), vr_eps);
        let r_ty = c.lt(vr.clone(), vl_eps);
        let proof = Expr::apps(c.and_intro.clone(), [l_ty, r_ty, left, right]);

        let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
        let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
        bw.finish_child(e)
    };

    let intro = Expr::apps(
        c.exists_intro.clone(),
        [c.nat.clone(), pred, c.nat_zero.clone(), witness],
    );
    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, intro);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish_child(e)
}

/// `v < v + ε` from `0<ε`.
fn build_self_lt_add(
    c: &ZeroAddConsts,
    parent: &EnvDeclBuilder,
    v: &Expr,
    eps: &Expr,
    hpos: &Expr,
) -> Expr {
    let h = Expr::apps(
        c.rat_add_lt_add_left.clone(),
        [c.rat_zero.clone(), eps.clone(), v.clone(), hpos.clone()],
    );
    let v_zero = c.radd(v.clone(), c.rat_zero.clone());
    let v_eps = c.radd(v.clone(), eps.clone());
    let add_zero = Expr::app(c.rat_add_zero.clone(), v.clone());
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(t, v_eps.clone());
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    c.subst_rat(motive, v_zero, v.clone(), add_zero, h)
}

/// `fun N => ∀ n, N≤n → And (vseq cl n < vseq cr n + ε)(vseq cr n < vseq cl n + ε)`.
fn build_za_pred(
    c: &ZeroAddConsts,
    parent: &EnvDeclBuilder,
    cl: &Expr,
    cr: &Expr,
    eps: &Expr,
) -> Expr {
    let mut bn = EnvDeclBuilder::child_of(parent);
    let (n_id, n_cap) = bn.fresh_local(c.nat.clone());
    let inner = {
        let mut bi = EnvDeclBuilder::child_of(&bn);
        let (m_id, m) = bi.fresh_local(c.nat.clone());
        let hle = c.nat_le(n_cap.clone(), m.clone());
        let (hle_id, _h) = bi.fresh_local(hle.clone());
        let vl = c.vseq(cl, &m);
        let vr = c.vseq(cr, &m);
        let left = c.lt(vl.clone(), c.radd(vr.clone(), eps.clone()));
        let right = c.lt(vr.clone(), c.radd(vl.clone(), eps.clone()));
        let concl = Expr::apps(c.and_c.clone(), [left, right]);
        let e = bi.mk_pi(hle_id, BinderInfo::Default, hle, concl);
        let e = bi.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
        bi.finish_child(e)
    };
    bn.finish_child(bn.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), inner))
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_zero_add()
            .expect("init_algebra_nnreal_zero_add");
        env.init_algebra_nnreal_zero_add().expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_zero_add_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("NNReal.zero_add");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("NNReal.zero_add must kernel-check: {e:?}"));
    }

    #[test]
    fn test_nnreal_zero_add_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("NNReal.zero_add");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be foundational-only: {:?}",
            env.axiom_deps(&nm)
        );
    }
}
