// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — `NNReal.le_self_add` (`a ≤ a + b`): adding a nonneg
//! `NNReal` only increases. The rational dual scaffolding the `(4/3,4)` dual-HC
//! tensorization needs (cube super-additivity `u³+v³ ≤ (u+v)³` stands on it).
//!
//! # Why this module exists (the dual cross-term scaffolding)
//!
//! The `(4/3,4)` dual-HC tensorization step (design
//! `2026-06-20-hc43-dual-tensorization-cross-term.md`) folds the two IH cube-RHS
//! objects `NG³`, `NH³` into the single `(NG+NH)³` shape via the CUBE
//! super-additivity `u³+v³ ≤ (u+v)³`. That super-additivity reduces — after
//! expanding `(u+v)³ = (u³+v³) + (3u²v+3uv²)` — to the monotone-add fact
//! `x ≤ x + y` on `NNReal` (every `NNReal` is `≥ 0`, so the cross block
//! `3u²v+3uv²` only widens). The `(2,4)` FORWARD chain never needed this brick
//! (its IH RHS was a SQUARE handled by `le_of_sq_le_sq`); the dual's CUBE RHS
//! makes it the natural rational scaffolding.
//!
//! # The brick (axiom-free, kernel-checked)
//!
//! ```text
//!   NNReal.le_self_add : ∀ a b : NNReal, NNReal.le a (NNReal.add a b)
//! ```
//!
//! # Proof shape (axiom-free)
//!
//! The genuine content is the standalone `CauSeq`-level lemma
//! `NNReal.CauSeq.le_self_add fa fb : CauSeq.le fa (CauSeq.add fa fb)`. Its body,
//! for `ε>0`, supplies the witness `N := Nat.zero` (the bound holds at EVERY
//! index, no anchoring), and at index `m`:
//!
//! - `va := val(seq fa m)`, `vb := val(seq fb m)` with `0 ≤ vb`
//!   (`NNRat.property (seq fb m)`).
//! - `va ≤ va + vb`           (`Rat.le_add_of_nonneg_right va vb (0≤vb)`).
//! - `va+vb < (va+vb) + ε`    (`Rat.add_lt_add_left Rat.zero ε (va+vb) hpos` gives
//!   `(va+vb)+0 < (va+vb)+ε`, transported `(va+vb)+0 → va+vb` via `Rat.add_zero`).
//! - `va < (va+vb)+ε`         (`Rat.lt_of_le_of_lt`).
//! - transport `(va+vb) → val(seq(add fa fb) m)` via `Eq.symm (NNRat.val_add …)`
//!   (`seq(add fa fb) m ≡ NNRat.add (seq fa m)(seq fb m)` defeq), landing the
//!   `CauSeq.le` domination conclusion `va < val(seq(add fa fb) m) + ε`.
//!
//! `NNReal.le_self_add` is the two-fold nested `Quot.ind` lift reducing each leaf
//! `NNReal.le (mk fa)(NNReal.add (mk fa)(mk fb))` (≡ `NNReal.le (mk fa)(mk(add fa
//! fb))` by the `NNReal.add` `Quot.lift` computation) to `CauSeq.le fa (add fa
//! fb)`, closing by `NNReal.CauSeq.le_self_add`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `NNReal.le_self_add`.
pub(crate) struct LeSelfAddConsts {
    nat: Expr,
    nat_zero: Expr,
    rat: Expr,
    rat_zero: Expr,
    nnrat_val: Expr,
    nnrat_add: Expr,
    nnrat_val_add: Expr,
    nnrat_property: Expr,
    causeq: Expr,
    causeq_seq: Expr,
    causeq_equiv: Expr,
    causeq_le: Expr,
    causeq_add: Expr,
    rat_add: Expr,
    rat_lt: Expr,
    nat_le: Expr,
    rat_add_zero: Expr,
    rat_add_lt_add_left: Expr,
    rat_le_add_of_nonneg_right: Expr,
    rat_lt_of_le_of_lt: Expr,
    // Logic / Eq.{1}.
    exists_c: Expr,
    exists_intro: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
    quot_mk: Expr,
    quot_ind: Expr,
}

impl LeSelfAddConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            nnrat_val: k("NNRat.val"),
            nnrat_add: k("NNRat.add"),
            nnrat_val_add: k("NNRat.val_add"),
            nnrat_property: k("NNRat.property"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            causeq_le: k("NNReal.CauSeq.le"),
            causeq_add: k("NNReal.CauSeq.add"),
            rat_add: k("Rat.add"),
            rat_lt: k("Rat.lt"),
            nat_le: k("Nat.le"),
            rat_add_zero: k("Rat.add_zero"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_le_add_of_nonneg_right: k("Rat.le_add_of_nonneg_right"),
            rat_lt_of_le_of_lt: k("Rat.lt_of_le_of_lt"),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![lvl1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![lvl1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1.clone()]),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![lvl1.clone()]),
            quot_ind: Expr::const_(Name::from_string("Quot.ind"), vec![lvl1]),
        }
    }

    // ── term constructors ───────────────────────────────────────────────────
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    /// `NNRat.val (CauSeq.seq x n) : Rat`.
    fn vseq(&self, x: &Expr, n: &Expr) -> Expr {
        let seq = Expr::app(self.causeq_seq.clone(), x.clone());
        let at = Expr::app(seq, n.clone());
        Expr::app(self.nnrat_val.clone(), at)
    }
    /// `CauSeq.seq x n : NNRat`.
    fn seq_at(&self, x: &Expr, n: &Expr) -> Expr {
        Expr::app(Expr::app(self.causeq_seq.clone(), x.clone()), n.clone())
    }
    /// `CauSeq.add a b : CauSeq`.
    fn causeq_add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_add.clone(), [a, b])
    }
    /// `CauSeq.le a b : Prop`.
    fn causeq_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_le.clone(), [a, b])
    }
    /// `vseq a m < vseq b m + ε`.
    fn dom(&self, a: &Expr, b: &Expr, m: &Expr, eps: &Expr) -> Expr {
        self.lt(self.vseq(a, m), self.add(self.vseq(b, m), eps.clone()))
    }
    /// `∀ n, N≤n → vseq a n < vseq b n + ε` (predicate fully applied at `cap`).
    fn pred_n_at(
        &self,
        parent: &EnvDeclBuilder,
        a: &Expr,
        b: &Expr,
        eps: &Expr,
        cap: &Expr,
    ) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (m_id, m) = bn.fresh_local(self.nat.clone());
        let hle = self.nat_le(cap.clone(), m.clone());
        let (hle_id, _hle) = bn.fresh_local(hle.clone());
        let concl = self.dom(a, b, &m, eps);
        let e = bn.mk_pi(hle_id, BinderInfo::Default, hle, concl);
        let e = bn.mk_pi(m_id, BinderInfo::Default, self.nat.clone(), e);
        bn.finish_child(e)
    }
    /// `fun N => ∀ n, N≤n → vseq a n < vseq b n + ε`.
    fn pred_n(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, eps: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (n_id, n_cap) = bn.fresh_local(self.nat.clone());
        let inner = self.pred_n_at(&bn, a, b, eps, &n_cap);
        bn.finish_child(bn.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), inner))
    }
    /// `∃ N, pred_n a b eps N : Prop`.
    fn exists_pred(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, eps: &Expr) -> Expr {
        Expr::apps(
            self.exists_c.clone(),
            [self.nat.clone(), self.pred_n(parent, a, b, eps)],
        )
    }

    // ── proof helpers ────────────────────────────────────────────────────────
    /// `NNRat.property q : Rat.le Rat.zero (NNRat.val q)`.
    fn nnrat_property(&self, q: Expr) -> Expr {
        Expr::app(self.nnrat_property.clone(), q)
    }
    /// `NNRat.val_add p q : Eq Rat (val (add p q)) ((val p)+(val q))`.
    fn val_add(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_val_add.clone(), [p, q])
    }
    /// `Rat.le_add_of_nonneg_right a b h : Rat.le a (a+b)`.
    fn le_add_nonneg_right(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_le_add_of_nonneg_right.clone(), [a, b, h])
    }
    /// `Rat.add_lt_add_left a b c h : (c+a) < (c+b)`.
    fn add_lt_add_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add_left.clone(), [a, b, cc, h])
    }
    /// `Rat.add_zero a : Eq Rat (a+0) a`.
    fn add_zero(&self, a: Expr) -> Expr {
        Expr::app(self.rat_add_zero.clone(), a)
    }
    /// `Rat.lt_of_le_of_lt a b c h1 h2 : Rat.lt a c`.
    fn lt_of_le_of_lt(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_le_of_lt.clone(), [a, b, cc, h1, h2])
    }
    /// `@Eq.symm Rat a b h : Eq Rat b a`.
    fn eq_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `@Quot.mk.{1} CauSeq Equiv l : NNReal`.
    fn quot_mk(&self, l: Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), l],
        )
    }
    fn nnreal(&self) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Quot"), vec![Level::succ(Level::zero())]),
            [self.causeq.clone(), self.causeq_equiv.clone()],
        )
    }
}

impl Environment {
    /// Register `NNReal.le_self_add` (+ the `CauSeq.le_self_add` core). Idempotent.
    pub fn init_algebra_nnreal_le_self_add(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_add()?; // CauSeq.add, NNReal.add, NNRat.val_add
        self.init_algebra_nnreal_le()?; // CauSeq.le, NNReal.le
        self.init_algebra_nnreal_nnrat()?; // NNRat.property
        self.init_rat_field_inst()?; // Rat.add_zero
        self.register_rat_add_lt_add_left()?; // Rat.add_lt_add_left
        self.init_rat_quotient_poc()?; // Rat.le_add_of_nonneg_right
        self.init_boolean_analysis_order_toolkit_b1c()?; // Rat.lt_of_le_of_lt
        self.init_exists()?;

        let c = LeSelfAddConsts::new();
        self.register_causeq_le_self_add(&c)?;
        self.register_nnreal_le_self_add(&c)?;
        Ok(())
    }

    /// `NNReal.CauSeq.le_self_add : ∀ fa fb, CauSeq.le fa (CauSeq.add fa fb)`.
    fn register_causeq_le_self_add(&mut self, c: &LeSelfAddConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.CauSeq.le_self_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (fa_id, fa) = b.fresh_local(c.causeq.clone());
            let (fb_id, fb) = b.fresh_local(c.causeq.clone());
            let concl = c.causeq_le(fa.clone(), c.causeq_add(fa.clone(), fb.clone()));
            let e = b.mk_pi(fb_id, BinderInfo::Default, c.causeq.clone(), concl);
            let e = b.mk_pi(fa_id, BinderInfo::Default, c.causeq.clone(), e);
            b.finish(e)
        };
        let value = build_causeq_le_self_add_fn(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.le_self_add : ∀ a b : NNReal, NNReal.le a (NNReal.add a b)`.
    fn register_nnreal_le_self_add(&mut self, c: &LeSelfAddConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.le_self_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nnreal = c.nnreal();
        let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
        let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nnreal.clone());
            let (bv_id, bv) = b.fresh_local(nnreal.clone());
            let add_ab = Expr::apps(nnadd.clone(), [a.clone(), bv.clone()]);
            let concl = Expr::apps(nnle.clone(), [a.clone(), add_ab]);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nnreal.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_nnreal_le_self_add(c, &nnreal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// The standalone `CauSeq.le_self_add` proof value.
fn build_causeq_le_self_add_fn(c: &LeSelfAddConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (fa_id, fa) = b.fresh_local(c.causeq.clone());
    let (fb_id, fb) = b.fresh_local(c.causeq.clone());

    // goal: CauSeq.le fa (add fa fb)
    //   = ∀ ε, 0<ε → ∃ N, ∀ m, N≤m → vseq fa m < vseq(add fa fb) m + ε.
    let cl = fa.clone();
    let cr = c.causeq_add(fa.clone(), fb.clone());

    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    // witness N := Nat.zero (bound holds at every index).
    let witness = {
        let mut bw = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = bw.fresh_local(c.nat.clone());
        let hle_ty = c.nat_le(c.nat_zero.clone(), m.clone());
        let (hle_id, _hle) = bw.fresh_local(hle_ty.clone());
        let proof = build_leaf(c, &bw, &fa, &fb, &m, &eps, &hpos);
        let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
        let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
        bw.finish_child(e)
    };

    let intro = Expr::apps(
        c.exists_intro.clone(),
        [
            c.nat.clone(),
            c.pred_n(&b, &cl, &cr, &eps),
            c.nat_zero.clone(),
            witness,
        ],
    );

    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, intro);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(fb_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(fa_id, BinderInfo::Default, c.causeq.clone(), e);
    b.finish(e)
}

/// At index `m`, the domination leaf `vseq fa m < vseq(add fa fb) m + ε`.
fn build_leaf(
    c: &LeSelfAddConsts,
    parent: &EnvDeclBuilder,
    fa: &Expr,
    fb: &Expr,
    m: &Expr,
    eps: &Expr,
    hpos: &Expr,
) -> Expr {
    let va = c.vseq(fa, m);
    let vb = c.vseq(fb, m);
    let va_vb = c.add(va.clone(), vb.clone()); // va + vb

    // h_le : va ≤ va + vb   (Rat.le_add_of_nonneg_right va vb (0≤vb)).
    let h_nonneg = c.nnrat_property(c.seq_at(fb, m)); // 0 ≤ val(seq fb m) = vb
    let h_le = c.le_add_nonneg_right(va.clone(), vb.clone(), h_nonneg);

    // h_lt0 : (va+vb)+0 < (va+vb)+ε   (Rat.add_lt_add_left 0 ε (va+vb) hpos).
    let h_lt0 = c.add_lt_add_left(c.rat_zero.clone(), eps.clone(), va_vb.clone(), hpos.clone());
    // transport (va+vb)+0 → va+vb on the LHS of the `<` via Rat.add_zero (va+vb).
    let va_vb_zero = c.add(va_vb.clone(), c.rat_zero.clone());
    let va_vb_eps = c.add(va_vb.clone(), eps.clone());
    let motive_lt = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(t, va_vb_eps.clone());
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    // h_lt : va+vb < (va+vb)+ε.
    let h_lt = c.subst(
        motive_lt,
        va_vb_zero,
        va_vb.clone(),
        c.add_zero(va_vb.clone()),
        h_lt0,
    );

    // chain : va < (va+vb)+ε   (lt_of_le_of_lt va (va+vb) ((va+vb)+ε) h_le h_lt).
    let chain = c.lt_of_le_of_lt(va.clone(), va_vb.clone(), va_vb_eps, h_le, h_lt);

    // transport (va+vb) → val(seq(add fa fb) m) on the RHS summand via
    // Eq.symm (NNRat.val_add (seq fa m)(seq fb m)). The goal's RHS form is
    // vseq(add fa fb) m + ε ≡ val(NNRat.add (seq fa m)(seq fb m)) + ε (defeq).
    let seq_fa = c.seq_at(fa, m);
    let seq_fb = c.seq_at(fb, m);
    let val_add = c.val_add(seq_fa.clone(), seq_fb.clone()); // val(add..) = va+vb
    let vr_form = Expr::app(
        c.nnrat_val.clone(),
        Expr::apps(c.nnrat_add.clone(), [seq_fa, seq_fb]),
    );
    let motive_rhs = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(va.clone(), c.add(t, eps.clone()));
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    // subst va_vb → vr_form via symm(val_add) : (va+vb) = vr_form.
    c.subst(
        motive_rhs,
        va_vb.clone(),
        vr_form.clone(),
        c.eq_symm(vr_form, va_vb, val_add),
        chain,
    )
}

/// `NNReal.le_self_add` via two nested `Quot.ind`s reducing each leaf to
/// `NNReal.CauSeq.le_self_add`.
fn build_nnreal_le_self_add(c: &LeSelfAddConsts, nnreal: &Expr) -> Expr {
    let core = Expr::const_(Name::from_string("NNReal.CauSeq.le_self_add"), vec![]);
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nnreal.clone());
    let (bv_id, bv) = b.fresh_local(nnreal.clone());

    let body = descend_a(c, &b, nnreal, &a, &bv, &core);

    let e = b.mk_lam(bv_id, BinderInfo::Default, nnreal.clone(), body);
    let e = b.mk_lam(a_id, BinderInfo::Default, nnreal.clone(), e);
    b.finish(e)
}

/// Descend on `a` with motive `P x := NNReal.le x (NNReal.add x bv)`. The minor
/// (rep `fa`) descends on `bv`.
fn descend_a(
    c: &LeSelfAddConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    a: &Expr,
    bv: &Expr,
    core: &Expr,
) -> Expr {
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
    let add = |x: Expr, y: Expr| Expr::apps(nnadd.clone(), [x, y]);

    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = mb.fresh_local(nnreal.clone());
        let concl = Expr::apps(nnle.clone(), [x.clone(), add(x.clone(), bv.clone())]);
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), concl))
    };
    let minor = {
        let mut mf = EnvDeclBuilder::child_of(parent);
        let (fa_id, fa) = mf.fresh_local(c.causeq.clone());
        let mka = c.quot_mk(fa.clone());
        let body = descend_b(c, &mf, nnreal, &mka, &fa, bv, core);
        mf.finish_child(mf.mk_lam(fa_id, BinderInfo::Default, c.causeq.clone(), body))
    };
    Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            a.clone(),
        ],
    )
}

/// Descend on `bv` with motive `Q y := NNReal.le (mk fa)(NNReal.add (mk fa) y)`.
/// Leaf supplies rep `fb`; the goal then reduces (NNReal.add `Quot.lift`) to
/// `NNReal.le (mk fa)(mk(add fa fb))`, i.e. `CauSeq.le fa (add fa fb)`.
fn descend_b(
    c: &LeSelfAddConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    mka: &Expr,
    fa: &Expr,
    bv: &Expr,
    core: &Expr,
) -> Expr {
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
    let add = |x: Expr, y: Expr| Expr::apps(nnadd.clone(), [x, y]);

    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (y_id, y) = mb.fresh_local(nnreal.clone());
        let concl = Expr::apps(nnle.clone(), [mka.clone(), add(mka.clone(), y.clone())]);
        mb.finish_child(mb.mk_lam(y_id, BinderInfo::Default, nnreal.clone(), concl))
    };
    let minor = {
        let mut mf = EnvDeclBuilder::child_of(parent);
        let (fb_id, fb) = mf.fresh_local(c.causeq.clone());
        // CauSeq.le_self_add fa fb : CauSeq.le fa (add fa fb)
        //   ≡ NNReal.le (mk fa)(mk(add fa fb)) ≡ NNReal.le (mk fa)(NNReal.add (mk fa)(mk fb)).
        let body = Expr::apps(core.clone(), [fa.clone(), fb.clone()]);
        mf.finish_child(mf.mk_lam(fb_id, BinderInfo::Default, c.causeq.clone(), body))
    };
    Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            bv.clone(),
        ],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["NNReal.CauSeq.le_self_add", "NNReal.le_self_add"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_le_self_add()
            .expect("init_algebra_nnreal_le_self_add");
        env.init_algebra_nnreal_le_self_add().expect("idempotent");
        env
    }

    #[test]
    fn test_le_self_add_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_le_self_add_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
