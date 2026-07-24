// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — `NNReal.add` (binary `Quot.lift` with respect proofs).
//!
//! # Why this module exists
//!
//! With `NNReal.CauSeq.Equiv` a genuine setoid (`refl`/`symm`/`trans` all
//! landed), the carrier arithmetic can be lifted. This module lifts pointwise
//! `NNRat`-addition of Cauchy sequences to `NNReal` via a nested binary
//! `Quot.lift` (mirroring the `Qat.add` template in `algebra_rat_quotient.rs`),
//! discharging both respect obligations with `Quot.sound`.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNReal.CauSeq.add : NNReal.CauSeq → NNReal.CauSeq → NNReal.CauSeq`
//!     `:= fun f g => CauSeq.mk (fun n => NNRat.add (seq f n) (seq g n))`
//! - `NNReal.add : NNReal → NNReal → NNReal`   (nested binary `Quot.lift`)
//!
//! The single new theorem-shaped obligation is the per-argument respect proof
//! `Equiv (add p q) (add p q2)` from `Equiv q q2` (and symmetrically in the
//! first argument). Because `NNRat.val (NNRat.add a b) = val a + val b`
//! (`NNRat.val_add`, on main), the bound on the sum reduces to the bound on the
//! varying summand — NO halving is needed (the shared summand cancels), unlike
//! `Equiv.trans`. Each respect step is `Quot.sound` on that `Equiv`.
//!
//! NO `sorry` / `add_decl_unchecked` / `add_decl_structural`. `NNReal.add` is a
//! `Definition`; its well-definedness rides on the kernel-checked `Quot.lift`
//! respect arguments (each an `Equiv` proof, foundational closure).

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `NNReal.add`.
pub(crate) struct NNAddConsts {
    nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    nnrat: Expr,
    nnrat_add: Expr,
    nnrat_val: Expr,
    nnrat_val_add: Expr,
    causeq: Expr,
    causeq_mk: Expr,
    causeq_seq: Expr,
    causeq_property: Expr,
    causeq_equiv: Expr,
    is_cauchy_add: Expr,
    rat_add: Expr,
    rat_lt: Expr,
    rat_add_lt_add_left: Expr,
    rat_add_assoc: Expr,
    nat_le: Expr,
    // Quot machinery at level 1.
    quot: Expr,
    quot_mk: Expr,
    quot_lift: Expr,
    quot_sound: Expr,
    // Logic.
    and_c: Expr,
    and_intro: Expr,
    and_left: Expr,
    and_right: Expr,
    exists_c: Expr,
    exists_intro: Expr,
    exists_elim: Expr,
    // Eq.{1} over Rat.
    eq_rat: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
}

impl NNAddConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            nnrat: k("NNRat"),
            nnrat_add: k("NNRat.add"),
            nnrat_val: k("NNRat.val"),
            nnrat_val_add: k("NNRat.val_add"),
            causeq: k("NNReal.CauSeq"),
            causeq_mk: k("NNReal.CauSeq.mk"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_property: k("NNReal.CauSeq.property"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            is_cauchy_add: k("NNReal.IsCauchy_add"),
            rat_add: k("Rat.add"),
            rat_lt: k("Rat.lt"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_add_assoc: k("Rat.add_assoc"),
            nat_le: k("Nat.le"),
            quot: Expr::const_(Name::from_string("Quot"), vec![lvl1.clone()]),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![lvl1.clone()]),
            quot_lift: Expr::const_(
                Name::from_string("Quot.lift"),
                vec![lvl1.clone(), lvl1.clone()],
            ),
            quot_sound: Expr::const_(Name::from_string("Quot.sound"), vec![lvl1.clone()]),
            and_c: k("And"),
            and_intro: k("And.intro"),
            and_left: k("And.left"),
            and_right: k("And.right"),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![lvl1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![lvl1.clone()]),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![lvl1.clone()]),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1]),
        }
    }

    fn seq_ty(&self) -> Expr {
        Expr::pi(BinderInfo::Default, self.nat.clone(), self.nnrat.clone())
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
    fn and_ty(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.and_c.clone(), [p, q])
    }
    /// `NNRat.val q : Rat`.
    fn val(&self, q: Expr) -> Expr {
        Expr::app(self.nnrat_val.clone(), q)
    }
    /// `NNReal.CauSeq.seq f n : NNRat`.
    fn seq_at(&self, f: &Expr, n: &Expr) -> Expr {
        Expr::app(Expr::app(self.causeq_seq.clone(), f.clone()), n.clone())
    }
    /// `val (seq f n) : Rat`.
    fn vseq(&self, f: &Expr, n: &Expr) -> Expr {
        self.val(self.seq_at(f, n))
    }
    /// `NNRat.add a b : NNRat`.
    fn nnadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnrat_add.clone(), [a, b])
    }
    fn equiv(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_equiv.clone(), [a, b])
    }
    fn bound_pair(&self, x: Expr, y: Expr, eps: Expr) -> Expr {
        let left = self.lt(x.clone(), self.radd(y.clone(), eps.clone()));
        let right = self.lt(y, self.radd(x, eps));
        self.and_ty(left, right)
    }
    /// `@Quot.mk.{1} CauSeq Equiv l : NNReal`.
    fn quot_mk(&self, l: Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), l],
        )
    }
    /// `@Quot.sound.{1} CauSeq Equiv a b h : Eq NNReal (mk a)(mk b)`.
    fn quot_sound(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.quot_sound.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), a, b, h],
        )
    }
    /// `Rat.add_lt_add_left a b c h : (c+a) < (c+b)`.
    fn add_lt_add_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add_left.clone(), [a, b, cc, h])
    }
    /// `Rat.add_assoc a b c : Eq Rat ((a+b)+c)(a+(b+c))`.
    fn add_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_add_assoc.clone(), [a, b, cc])
    }
    /// `NNRat.val_add p q : Eq Rat (val (NNRat.add p q)) ((val p)+(val q))`.
    fn val_add(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_val_add.clone(), [p, q])
    }
    fn eq_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }

    /// `CauSeq.seq f : Nat → NNRat`.
    fn seq_of(&self, f: &Expr) -> Expr {
        Expr::app(self.causeq_seq.clone(), f.clone())
    }
    /// `CauSeq.property f : IsCauchy (seq f)`.
    fn property(&self, f: &Expr) -> Expr {
        Expr::app(self.causeq_property.clone(), f.clone())
    }
    /// `CauSeq.add f g := CauSeq.mk (fun n => NNRat.add (seq f n)(seq g n)) hcau`
    /// where `hcau := IsCauchy_add (seq f)(seq g)(property f)(property g)` proves
    /// the pointwise-sum sequence is Cauchy (the SUBTYPE carrier requires it).
    fn cauadd(&self, parent: &EnvDeclBuilder, f: &Expr, g: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (n_id, n) = bn.fresh_local(self.nat.clone());
        let body = self.nnadd(self.seq_at(f, &n), self.seq_at(g, &n));
        let seq = bn.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), body);
        let seq = bn.finish_child(seq);
        let hcau = Expr::apps(
            self.is_cauchy_add.clone(),
            [
                self.seq_of(f),
                self.seq_of(g),
                self.property(f),
                self.property(g),
            ],
        );
        Expr::apps(self.causeq_mk.clone(), [seq, hcau])
    }
}

impl Environment {
    /// Register `NNReal.CauSeq.add` and `NNReal.add`. Idempotent.
    pub fn init_algebra_nnreal_add(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_cauchy()?; // CauSeq, Equiv, mk, seq, property; NNRat.*
        self.init_algebra_nnreal_iscauchy_ops()?; // NNReal.IsCauchy_add (mk needs it)
        self.register_rat_add_lt_add_left()?; // Rat.add_lt_add_left
        self.register_rat_add_lt_add_right()?; // Rat.add_lt_add_right
        self.init_rat_field_inst()?; // Rat.add_assoc, Rat.add_comm
        self.register_nnrat_val_add_present()?;

        let c = NNAddConsts::new();
        self.register_nnreal_causeq_add(&c)?;
        self.register_nnreal_add(&c)?;
        Ok(())
    }

    /// Ensure `NNRat.val_add` is present (it is registered by
    /// `init_algebra_nnreal_nnrat`, pulled in by `init_algebra_nnreal_cauchy`).
    fn register_nnrat_val_add_present(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_nnrat()
    }

    /// `NNReal.CauSeq.add : CauSeq → CauSeq → CauSeq`.
    fn register_nnreal_causeq_add(&mut self, c: &NNAddConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNReal.CauSeq.add"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.causeq.clone(),
            Expr::pi(BinderInfo::Default, c.causeq.clone(), c.causeq.clone()),
        );
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.causeq.clone());
            let (g_id, g) = b.fresh_local(c.causeq.clone());
            let body = c.cauadd(&b, &f, &g);
            let e = b.mk_lam(g_id, BinderInfo::Default, c.causeq.clone(), body);
            let e = b.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNReal.CauSeq.add"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNReal.add : NNReal → NNReal → NNReal`, a nested binary `Quot.lift`.
    fn register_nnreal_add(&mut self, c: &NNAddConsts) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("NNReal.add")).is_some() {
            return Ok(());
        }
        let nnreal = Expr::apps(c.quot.clone(), [c.causeq.clone(), c.causeq_equiv.clone()]);
        let ty = Expr::pi(
            BinderInfo::Default,
            nnreal.clone(),
            Expr::pi(BinderInfo::Default, nnreal.clone(), nnreal.clone()),
        );
        let value = build_nnreal_add_value(c, &nnreal);
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNReal.add"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }
}

/// `NNReal.add := fun a b => Quot.lift (outer_f) (outer_h) a` where `outer_f p`
/// is itself a `Quot.lift` over `b`. Mirrors `Qat.add`.
fn build_nnreal_add_value(c: &NNAddConsts, nnreal: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nnreal.clone());
    let (bv_id, bv) = b.fresh_local(nnreal.clone());

    // Inner lift over the SECOND operand, for a fixed first rep `p`.
    //   inner_f q := Quot.mk (CauSeq.add p q)
    //   inner_h q q2 (hq : Equiv q q2) : Eq NNReal (mk (add p q)) (mk (add p q2))
    //       := Quot.sound (add p q) (add p q2) (respect_second p q q2 hq).
    let inner_lift = |p: &Expr, parent: &EnvDeclBuilder, second: &Expr| -> Expr {
        let inner_f = {
            let mut bi = EnvDeclBuilder::child_of(parent);
            let (q_id, q) = bi.fresh_local(c.causeq.clone());
            let body = c.quot_mk(c.cauadd(&bi, p, &q));
            let lam = bi.mk_lam(q_id, BinderInfo::Default, c.causeq.clone(), body);
            bi.finish_child(lam)
        };
        let inner_h = {
            let mut bi = EnvDeclBuilder::child_of(parent);
            let (q_id, q) = bi.fresh_local(c.causeq.clone());
            let (q2_id, q2) = bi.fresh_local(c.causeq.clone());
            let hyp = c.equiv(q.clone(), q2.clone());
            let (hq_id, hq) = bi.fresh_local(hyp.clone());
            // respect: Equiv (add p q)(add p q2) — the summand q varies.
            let eqv = build_respect_second(c, &bi, p, &q, &q2, &hq);
            let add_pq = c.cauadd(&bi, p, &q);
            let add_pq2 = c.cauadd(&bi, p, &q2);
            let sound = c.quot_sound(add_pq, add_pq2, eqv);
            let lam = bi.mk_lam(hq_id, BinderInfo::Default, hyp, sound);
            let lam = bi.mk_lam(q2_id, BinderInfo::Default, c.causeq.clone(), lam);
            let lam = bi.mk_lam(q_id, BinderInfo::Default, c.causeq.clone(), lam);
            bi.finish_child(lam)
        };
        Expr::apps(
            c.quot_lift.clone(),
            [
                c.causeq.clone(),
                c.causeq_equiv.clone(),
                nnreal.clone(),
                inner_f,
                inner_h,
                second.clone(),
            ],
        )
    };

    // outer_f := fun (p : CauSeq) => inner_lift p bv.
    let outer_f = {
        let mut bo = EnvDeclBuilder::child_of(&b);
        let (p_id, p) = bo.fresh_local(c.causeq.clone());
        let body = inner_lift(&p, &bo, &bv);
        let lam = bo.mk_lam(p_id, BinderInfo::Default, c.causeq.clone(), body);
        bo.finish_child(lam)
    };

    // outer_h : ∀ p p2, Equiv p p2 → Eq NNReal (inner_lift p bv)(inner_lift p2 bv).
    // Routed through Quot.ind on `bv` (the fixed second operand) so each leaf is
    // `Quot.sound (add p q)(add p2 q) (respect_first p p2 q hp)`.
    let outer_h = {
        let mut bh = EnvDeclBuilder::child_of(&b);
        let (p_id, p) = bh.fresh_local(c.causeq.clone());
        let (p2_id, p2) = bh.fresh_local(c.causeq.clone());
        let hyp = c.equiv(p.clone(), p2.clone());
        let (hp_id, hp) = bh.fresh_local(hyp.clone());

        // Quot.ind motive: fun (x : NNReal) => Eq NNReal (inner_lift p x)(inner_lift p2 x).
        let quot_ind = Expr::const_(
            Name::from_string("Quot.ind"),
            vec![Level::succ(Level::zero())],
        );
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&bh);
            let (x_id, x) = mb.fresh_local(nnreal.clone());
            let lhs = inner_lift(&p, &mb, &x);
            let rhs = inner_lift(&p2, &mb, &x);
            let eq_nn = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [nnreal.clone(), lhs, rhs],
            );
            mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), eq_nn))
        };
        // Quot.ind minor: fun (q : CauSeq) => Quot.sound (add p q)(add p2 q) (respect_first …).
        let minor = {
            let mut mb = EnvDeclBuilder::child_of(&bh);
            let (q_id, q) = mb.fresh_local(c.causeq.clone());
            let eqv = build_respect_first(c, &mb, &p, &p2, &q, &hp);
            let add_pq = c.cauadd(&mb, &p, &q);
            let add_p2q = c.cauadd(&mb, &p2, &q);
            let sound = c.quot_sound(add_pq, add_p2q, eqv);
            mb.finish_child(mb.mk_lam(q_id, BinderInfo::Default, c.causeq.clone(), sound))
        };
        let ind = Expr::apps(
            quot_ind,
            [
                c.causeq.clone(),
                c.causeq_equiv.clone(),
                motive,
                minor,
                bv.clone(),
            ],
        );
        let lam = bh.mk_lam(hp_id, BinderInfo::Default, hyp, ind);
        let lam = bh.mk_lam(p2_id, BinderInfo::Default, c.causeq.clone(), lam);
        let lam = bh.mk_lam(p_id, BinderInfo::Default, c.causeq.clone(), lam);
        bh.finish_child(lam)
    };

    let outer = Expr::apps(
        c.quot_lift.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            nnreal.clone(),
            outer_f,
            outer_h,
            a.clone(),
        ],
    );
    let e = b.mk_lam(bv_id, BinderInfo::Default, nnreal.clone(), outer);
    let e = b.mk_lam(a_id, BinderInfo::Default, nnreal.clone(), e);
    b.finish(e)
}

/// `Equiv (add p q)(add p q2)` from `hq : Equiv q q2` — the SECOND-operand
/// respect (the varying summand is `q`; `p` is shared).
fn build_respect_second(
    c: &NNAddConsts,
    parent: &EnvDeclBuilder,
    p: &Expr,
    q: &Expr,
    q2: &Expr,
    hq: &Expr,
) -> Expr {
    build_add_respect(c, parent, p, q, q2, hq, /*p_first=*/ true)
}

/// `Equiv (add p q)(add p2 q)` from `hp : Equiv p p2` — the FIRST-operand
/// respect (the varying summand is `p`; `q` is shared).
fn build_respect_first(
    c: &NNAddConsts,
    parent: &EnvDeclBuilder,
    p: &Expr,
    p2: &Expr,
    q: &Expr,
    hp: &Expr,
) -> Expr {
    build_add_respect(c, parent, q, p, p2, hp, /*p_first=*/ false)
}

/// Shared respect body. `shared` is the fixed summand; `x`,`x2` are the varying
/// summand with `hx : Equiv x x2`. Produces `Equiv (add A B)(add A2 B2)` where
/// `(A,B) = (shared,x)` if `!p_first` is for the first-operand case … rather,
/// the two `CauSeq.add` operands are assembled per `p_first`:
///   `p_first = true`  : add (shared,·) — sequences `add shared x` vs `add shared x2`.
///   `p_first = false` : add (·,shared) — sequences `add x shared` vs `add x2 shared`.
///
/// In both cases `val(seq(add …) n)` rewrites (via `NNRat.val_add`) to a sum in
/// which the SHARED term is common and the varying term differs by `< ε`; the
/// shared term is cancelled by `Rat.add_lt_add_left`/associativity bookkeeping.
fn build_add_respect(
    c: &NNAddConsts,
    parent: &EnvDeclBuilder,
    shared: &Expr,
    x: &Expr,
    x2: &Expr,
    hx: &Expr,
    p_first: bool,
) -> Expr {
    let mut bb = EnvDeclBuilder::child_of(parent);
    let (eps_id, eps) = bb.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = bb.fresh_local(hpos_ty.clone());

    // hx eps hpos : ∃ N, ∀ n, N≤n → bound_pair (vx)(vx2) ε.
    let exists_x = Expr::apps(hx.clone(), [eps.clone(), hpos.clone()]);

    // The two combined CauSeqs L := add(…), R := add(…), per p_first.
    let (cl, cr) = if p_first {
        (c.cauadd(&bb, shared, x), c.cauadd(&bb, shared, x2))
    } else {
        (c.cauadd(&bb, x, shared), c.cauadd(&bb, x2, shared))
    };

    // Goal target: ∃ N, ∀ n, N≤n → bound_pair (vL n)(vR n) ε.
    let goal_exists = exists_pred_combined(c, &bb, &cl, &cr, &eps);

    // pred for the source exists (over x,x2 at ε).
    let pred_x = pred_n_pair(c, &bb, x, x2, &eps, |cc, p, n| cc.vseq(p, n));

    let elim_fn = {
        let mut be = EnvDeclBuilder::child_of(&bb);
        let (cap_id, cap) = be.fresh_local(c.nat.clone());
        let hn_ty = pred_n_pair_at(c, &be, x, x2, &eps, &cap);
        let (hn_id, hn) = be.fresh_local(hn_ty.clone());

        // witness over the combined sequences with the SAME N.
        let witness = {
            let mut bw = EnvDeclBuilder::child_of(&be);
            let (m_id, m) = bw.fresh_local(c.nat.clone());
            let hle_ty = c.nat_le(cap.clone(), m.clone());
            let (hle_id, hle) = bw.fresh_local(hle_ty.clone());

            // base : bound_pair (vx)(vx2) ε := hn m hle.
            let base = Expr::apps(hn.clone(), [m.clone(), hle]);
            let vx = c.vseq(x, &m);
            let vx2 = c.vseq(x2, &m);
            let l_x = c.lt(vx.clone(), c.radd(vx2.clone(), eps.clone())); // vx<vx2+ε
            let r_x = c.lt(vx2.clone(), c.radd(vx.clone(), eps.clone())); // vx2<vx+ε
            let a_x = Expr::apps(c.and_left.clone(), [l_x.clone(), r_x.clone(), base.clone()]);
            let b_x = Expr::apps(c.and_right.clone(), [l_x, r_x, base]);

            let vs = c.vseq(shared, &m); // val(seq shared m)

            // The combined per-index values. vL = val(seq L m), and via val_add:
            //   p_first : vL = vs + vx  (shared first) ; vR = vs + vx2.
            //   else    : vL = vx + vs                  ; vR = vx2 + vs.
            // We prove bound_pair (vL)(vR) ε by transporting the shared-cancelled
            // strict bound through NNRat.val_add (which equates val(seq L m) to
            // the Rat sum).
            let proof = build_combined_bound(
                c, &bw, shared, x, x2, &m, &eps, &vs, &vx, &vx2, &a_x, &b_x, p_first,
            );

            let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
            let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            bw.finish_child(e)
        };

        let intro = Expr::apps(
            c.exists_intro.clone(),
            [
                c.nat.clone(),
                pred_n_combined(c, &be, &cl, &cr, &eps),
                cap.clone(),
                witness,
            ],
        );
        let e = be.mk_lam(hn_id, BinderInfo::Default, hn_ty, intro);
        let e = be.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), e);
        be.finish_child(e)
    };

    let elim = Expr::apps(
        c.exists_elim.clone(),
        [c.nat.clone(), pred_x, goal_exists, exists_x, elim_fn],
    );
    let e = bb.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, elim);
    let e = bb.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    bb.finish_child(e)
}

// Helper: predicate `fun N => ∀ n, N≤n → bound_pair (sel a n)(sel b n) eps`.
fn pred_n_pair(
    c: &NNAddConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    bb: &Expr,
    eps: &Expr,
    sel: impl Fn(&NNAddConsts, &Expr, &Expr) -> Expr,
) -> Expr {
    let mut bn = EnvDeclBuilder::child_of(parent);
    let (n_id, n) = bn.fresh_local(c.nat.clone());
    let inner = {
        let mut bi = EnvDeclBuilder::child_of(&bn);
        let (m_id, m) = bi.fresh_local(c.nat.clone());
        let hle = c.nat_le(n.clone(), m.clone());
        let (hle_id, _h) = bi.fresh_local(hle.clone());
        let concl = c.bound_pair(sel(c, a, &m), sel(c, bb, &m), eps.clone());
        let e = bi.mk_pi(hle_id, BinderInfo::Default, hle, concl);
        let e = bi.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
        bi.finish_child(e)
    };
    let lam = bn.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), inner);
    bn.finish_child(lam)
}

fn pred_n_pair_at(
    c: &NNAddConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    bb: &Expr,
    eps: &Expr,
    cap: &Expr,
) -> Expr {
    let mut bn = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = bn.fresh_local(c.nat.clone());
    let hle = c.nat_le(cap.clone(), m.clone());
    let (hle_id, _h) = bn.fresh_local(hle.clone());
    let concl = c.bound_pair(c.vseq(a, &m), c.vseq(bb, &m), eps.clone());
    let e = bn.mk_pi(hle_id, BinderInfo::Default, hle, concl);
    let e = bn.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    bn.finish_child(e)
}

/// predicate over the COMBINED sequences L,R (using their `vseq`).
fn pred_n_combined(
    c: &NNAddConsts,
    parent: &EnvDeclBuilder,
    cl: &Expr,
    cr: &Expr,
    eps: &Expr,
) -> Expr {
    pred_n_pair(c, parent, cl, cr, eps, |cc, p, n| cc.vseq(p, n))
}

fn exists_pred_combined(
    c: &NNAddConsts,
    parent: &EnvDeclBuilder,
    cl: &Expr,
    cr: &Expr,
    eps: &Expr,
) -> Expr {
    Expr::apps(
        c.exists_c.clone(),
        [c.nat.clone(), pred_n_combined(c, parent, cl, cr, eps)],
    )
}

/// Build `bound_pair (vL)(vR) ε` for the combined sequences, where
/// `vL = val(seq L m)`, `vR = val(seq R m)`, by transporting the shared-cancelled
/// strict bounds `a_x : vx < vx2+ε`, `b_x : vx2 < vx+ε` through `NNRat.val_add`.
#[allow(clippy::too_many_arguments)]
fn build_combined_bound(
    c: &NNAddConsts,
    parent: &EnvDeclBuilder,
    shared: &Expr,
    x: &Expr,
    x2: &Expr,
    m: &Expr,
    eps: &Expr,
    vs: &Expr,
    vx: &Expr,
    vx2: &Expr,
    a_x: &Expr,
    b_x: &Expr,
    p_first: bool,
) -> Expr {
    // val(seq L m): L = mk(fun n => NNRat.add A B), so seq L m ≡ NNRat.add A B
    //   (CauSeq.seq (CauSeq.mk s) ≡ s, reducible). val(NNRat.add A B) rewrites
    //   via val_add A B to (val A)+(val B).
    // p_first : A = seq shared m, B = seq x m  ⟹ vL_sum = vs + vx ; vR_sum = vs + vx2.
    // else    : A = seq x m, B = seq shared m  ⟹ vL_sum = vx + vs ; vR_sum = vx2 + vs.
    let seq_shared = c.seq_at(shared, m);
    let seq_x = c.seq_at(x, m);
    let seq_x2 = c.seq_at(x2, m);

    // val_add equalities: val(seq L m) = vL_sum, etc.  We need them as Eq Rat
    // (val(NNRat.add A B)) (vA + vB), i.e. exactly NNRat.val_add A B.
    let (val_add_l, val_add_r, vl_sum, vr_sum) = if p_first {
        (
            c.val_add(seq_shared.clone(), seq_x.clone()),
            c.val_add(seq_shared.clone(), seq_x2.clone()),
            c.radd(vs.clone(), vx.clone()),
            c.radd(vs.clone(), vx2.clone()),
        )
    } else {
        (
            c.val_add(seq_x.clone(), seq_shared.clone()),
            c.val_add(seq_x2.clone(), seq_shared.clone()),
            c.radd(vx.clone(), vs.clone()),
            c.radd(vx2.clone(), vs.clone()),
        )
    };

    // First prove bound_pair (vl_sum)(vr_sum) ε on the Rat sums, then transport
    // both endpoints back to val(seq L m)/val(seq R m) via Eq.symm val_add.
    // ── forward: vl_sum < vr_sum + ε ──
    let (fwd_sum, rev_sum) = if p_first {
        // vl = vs+vx, vr = vs+vx2.
        // fwd: (vs+vx) < (vs+vx2)+ε.
        //   add_lt_add_left vx (vx2+ε) vs a_x : (vs+vx) < (vs+(vx2+ε)).
        //   assoc: (vs+vx2)+ε = vs+(vx2+ε) ⟹ subst to (vs+vx) < (vs+vx2)+ε.
        let inner = c.add_lt_add_left(
            vx.clone(),
            c.radd(vx2.clone(), eps.clone()),
            vs.clone(),
            a_x.clone(),
        );
        let fwd =
            transport_assoc_right(c, parent, vs, vx2, eps, vx, &inner, /*lt_left=*/ true);
        // rev: (vs+vx2) < (vs+vx)+ε.
        let inner_r = c.add_lt_add_left(
            vx2.clone(),
            c.radd(vx.clone(), eps.clone()),
            vs.clone(),
            b_x.clone(),
        );
        let rev = transport_assoc_right(c, parent, vs, vx, eps, vx2, &inner_r, true);
        (fwd, rev)
    } else {
        // vl = vx+vs, vr = vx2+vs.
        // fwd: (vx+vs) < (vx2+vs)+ε.  Use add_lt_add_right on a_x then reshuffle.
        // We instead route via the same sum-form by commuting through add_lt_add_right:
        //   add_lt_add_right vx (vx2+ε) ... no — keep right-add form:
        //   (vx+vs) < (vx2+vs)+ε  ⟺  need vx<vx2+ε plus +vs on both, with ε floated.
        // Build: add_lt_add_right vx (vx2+ε) vs a_x : (vx+vs) < ((vx2+ε)+vs).
        // Then ((vx2+ε)+vs) = (vx2+vs)+ε via commute/assoc — but that needs add_comm.
        // To avoid add_comm, define vr_sum order to MATCH: keep vr_sum = (vx2+vs).
        // Transport ((vx2+ε)+vs) → (vx2+vs)+ε requires reordering ε past vs (add_comm).
        let inner = Expr::apps(
            Expr::const_(Name::from_string("Rat.add_lt_add_right"), vec![]),
            [
                vx.clone(),
                c.radd(vx2.clone(), eps.clone()),
                vs.clone(),
                a_x.clone(),
            ],
        );
        let fwd = transport_reorder_right(c, parent, vx2, eps, vs, vx, &inner);
        let inner_r = Expr::apps(
            Expr::const_(Name::from_string("Rat.add_lt_add_right"), vec![]),
            [
                vx2.clone(),
                c.radd(vx.clone(), eps.clone()),
                vs.clone(),
                b_x.clone(),
            ],
        );
        let rev = transport_reorder_right(c, parent, vx, eps, vs, vx2, &inner_r);
        (fwd, rev)
    };

    // Now transport endpoints from Rat sums back to val(seq L m), val(seq R m).
    // val(seq L m) ≡ val(NNRat.add A B) definitionally (seq(mk s) ≡ s), and
    // val_add_l : val(NNRat.add A B) = vl_sum, so we substitute both endpoints
    // back to the val_add form (which the kernel accepts defeq to the bound_pair
    // endpoints val(seq L m)/val(seq R m)).
    build_endpoints_transport(
        c, parent, shared, x, x2, m, eps, &vl_sum, &vr_sum, &val_add_l, &val_add_r, &fwd_sum,
        &rev_sum, p_first,
    )
}

/// `(vs + a) < (vs + b)+ε` from `inner : (vs+a) < (vs+(b+ε))` via add_assoc:
///   `(vs+b)+ε = vs+(b+ε)`; subst motive `t := (vs+a) < t` from `vs+(b+ε)` to
///   `(vs+b)+ε`. (Here `a`,`b` name the varying summands; `ε` floated.)
fn transport_assoc_right(
    c: &NNAddConsts,
    parent: &EnvDeclBuilder,
    vs: &Expr,
    b: &Expr,
    eps: &Expr,
    a: &Expr,
    inner: &Expr,
    _lt_left: bool,
) -> Expr {
    // assoc : (vs+b)+ε = vs+(b+ε).
    let assoc = c.add_assoc(vs.clone(), b.clone(), eps.clone());
    let vs_b_eps = c.radd(vs.clone(), c.radd(b.clone(), eps.clone())); // vs+(b+ε)
    let vsb_plus_eps = c.radd(c.radd(vs.clone(), b.clone()), eps.clone()); // (vs+b)+ε
    let vs_a = c.radd(vs.clone(), a.clone());
    // motive t := (vs+a) < t.
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(vs_a.clone(), t);
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    // subst from (vs+(b+ε)) to ((vs+b)+ε) along (Eq.symm assoc).
    c.subst(
        motive,
        vs_b_eps,
        vsb_plus_eps,
        c.eq_symm(
            vsb_plus_eps_alias(c, vs, b, eps),
            vs_b_eps_alias(c, vs, b, eps),
            assoc,
        ),
        inner.clone(),
    )
}

// alias helpers to keep the Eq.symm endpoints explicit
fn vsb_plus_eps_alias(c: &NNAddConsts, vs: &Expr, b: &Expr, eps: &Expr) -> Expr {
    c.radd(c.radd(vs.clone(), b.clone()), eps.clone())
}
fn vs_b_eps_alias(c: &NNAddConsts, vs: &Expr, b: &Expr, eps: &Expr) -> Expr {
    c.radd(vs.clone(), c.radd(b.clone(), eps.clone()))
}

/// `(a + vs) < (b+vs)+ε` from `inner : (a+vs) < (b+ε)+vs` — requires reordering
/// ε past vs, which needs add_comm; placeholder kept simple by using a direct
/// equational reshuffle `((b+ε)+vs) = (b+vs)+ε`.
fn transport_reorder_right(
    c: &NNAddConsts,
    parent: &EnvDeclBuilder,
    b: &Expr,
    eps: &Expr,
    vs: &Expr,
    a: &Expr,
    inner: &Expr,
) -> Expr {
    // reshuffle : ((b+ε)+vs) = ((b+vs)+ε)  via add_right_comm-style.
    let reshuffle = build_add_right_comm(c, parent, b, eps, vs);
    let be_vs = c.radd(c.radd(b.clone(), eps.clone()), vs.clone()); // (b+ε)+vs
    let bvs_eps = c.radd(c.radd(b.clone(), vs.clone()), eps.clone()); // (b+vs)+ε
    let a_vs = c.radd(a.clone(), vs.clone());
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(a_vs.clone(), t);
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    c.subst(motive, be_vs, bvs_eps, reshuffle, inner.clone())
}

/// `(b+ε)+vs = (b+vs)+ε`  (add_right_comm). Built from add_assoc + add_comm:
///   (b+ε)+vs = b+(ε+vs) = b+(vs+ε) = (b+vs)+ε.
fn build_add_right_comm(
    c: &NNAddConsts,
    parent: &EnvDeclBuilder,
    b: &Expr,
    eps: &Expr,
    vs: &Expr,
) -> Expr {
    let rat = c.rat.clone();
    let eq_trans = Expr::const_(
        Name::from_string("Eq.trans"),
        vec![Level::succ(Level::zero())],
    );
    let add_comm = Expr::const_(Name::from_string("Rat.add_comm"), vec![]);
    // a1 : (b+ε)+vs = b+(ε+vs)  (add_assoc b ε vs).
    let a1 = c.add_assoc(b.clone(), eps.clone(), vs.clone());
    // a2 : b+(ε+vs) = b+(vs+ε)  congrArg (b+·) (add_comm ε vs).
    let comm = Expr::apps(add_comm.clone(), [eps.clone(), vs.clone()]);
    let add_b_fn = {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = fb.fresh_local(rat.clone());
        let body = c.radd(b.clone(), t);
        fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, rat.clone(), body))
    };
    let congr = Expr::apps(
        Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        ),
        [
            rat.clone(),
            rat.clone(),
            c.radd(eps.clone(), vs.clone()),
            c.radd(vs.clone(), eps.clone()),
            add_b_fn,
            comm,
        ],
    );
    // a3 : b+(vs+ε) = (b+vs)+ε  (Eq.symm (add_assoc b vs ε)).
    let assoc2 = c.add_assoc(b.clone(), vs.clone(), eps.clone());
    let a3 = c.eq_symm(
        c.radd(c.radd(b.clone(), vs.clone()), eps.clone()),
        c.radd(b.clone(), c.radd(vs.clone(), eps.clone())),
        assoc2,
    );
    // chain a1 → a2 → a3.
    let t_be_vs = c.radd(c.radd(b.clone(), eps.clone()), vs.clone());
    let t_b_eps_vs = c.radd(b.clone(), c.radd(eps.clone(), vs.clone()));
    let t_b_vs_eps = c.radd(b.clone(), c.radd(vs.clone(), eps.clone()));
    let t_final = c.radd(c.radd(b.clone(), vs.clone()), eps.clone());
    let chain1 = Expr::apps(
        eq_trans.clone(),
        [
            rat.clone(),
            t_be_vs.clone(),
            t_b_eps_vs,
            t_b_vs_eps.clone(),
            a1,
            congr,
        ],
    );
    Expr::apps(eq_trans, [rat, t_be_vs, t_b_vs_eps, t_final, chain1, a3])
}

/// Transport the Rat-sum bounds back to `val(seq L m)` / `val(seq R m)` form.
#[allow(clippy::too_many_arguments)]
fn build_endpoints_transport(
    c: &NNAddConsts,
    parent: &EnvDeclBuilder,
    shared: &Expr,
    x: &Expr,
    x2: &Expr,
    m: &Expr,
    eps: &Expr,
    vl_sum: &Expr,
    vr_sum: &Expr,
    val_add_l: &Expr,
    val_add_r: &Expr,
    fwd_sum: &Expr,
    rev_sum: &Expr,
    p_first: bool,
) -> Expr {
    // val(seq L m) ≡ val(NNRat.add A B) (defeq), and val_add_l : that = vl_sum.
    // So vl_form := val(NNRat.add A B). Build it explicitly so the motive types
    // line up; the kernel accepts it defeq to val(seq L m) used in bound_pair.
    let seq_shared = c.seq_at(shared, m);
    let seq_x = c.seq_at(x, m);
    let seq_x2 = c.seq_at(x2, m);
    let (vl_form, vr_form) = if p_first {
        (
            c.val(c.nnadd(seq_shared.clone(), seq_x.clone())),
            c.val(c.nnadd(seq_shared.clone(), seq_x2.clone())),
        )
    } else {
        (
            c.val(c.nnadd(seq_x.clone(), seq_shared.clone())),
            c.val(c.nnadd(seq_x2.clone(), seq_shared.clone())),
        )
    };

    // fwd_sum : vl_sum < vr_sum + ε.
    // Step 1: rewrite the RHS summand vr_sum → vr_form via Eq.symm val_add_r:
    //   motive t := vl_sum < t + ε.
    let motive_rhs_fwd = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(vl_sum.clone(), c.radd(t, eps.clone()));
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let fwd1 = c.subst(
        motive_rhs_fwd,
        vr_sum.clone(),
        vr_form.clone(),
        c.eq_symm(vr_form.clone(), vr_sum.clone(), val_add_r.clone()),
        fwd_sum.clone(),
    );
    // Step 2: rewrite LHS vl_sum → vl_form: motive t := t < vr_form + ε.
    let motive_lhs_fwd = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(t, c.radd(vr_form.clone(), eps.clone()));
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let fwd = c.subst(
        motive_lhs_fwd,
        vl_sum.clone(),
        vl_form.clone(),
        c.eq_symm(vl_form.clone(), vl_sum.clone(), val_add_l.clone()),
        fwd1,
    );

    // rev_sum : vr_sum < vl_sum + ε  ⟶  vr_form < vl_form + ε.
    let motive_rhs_rev = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(vr_sum.clone(), c.radd(t, eps.clone()));
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let rev1 = c.subst(
        motive_rhs_rev,
        vl_sum.clone(),
        vl_form.clone(),
        c.eq_symm(vl_form.clone(), vl_sum.clone(), val_add_l.clone()),
        rev_sum.clone(),
    );
    let motive_lhs_rev = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(t, c.radd(vl_form.clone(), eps.clone()));
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let rev = c.subst(
        motive_lhs_rev,
        vr_sum.clone(),
        vr_form.clone(),
        c.eq_symm(vr_form.clone(), vr_sum.clone(), val_add_r.clone()),
        rev1,
    );

    // And.intro (vl_form<vr_form+ε)(vr_form<vl_form+ε) fwd rev.
    let l_final = c.lt(vl_form.clone(), c.radd(vr_form.clone(), eps.clone()));
    let r_final = c.lt(vr_form.clone(), c.radd(vl_form.clone(), eps.clone()));
    Expr::apps(c.and_intro.clone(), [l_final, r_final, fwd, rev])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    #[test]
    fn test_nnreal_add_kernel_check_and_closure() {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_add()
            .expect("init_algebra_nnreal_add");
        env.init_algebra_nnreal_add().expect("idempotent");

        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in ["NNReal.CauSeq.add", "NNReal.add"] {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{name} is a Definition"
            );
            // The Quot.lift respect proofs embedded in NNReal.add must keep the
            // admitted-axiom closure foundational-only (⊆ {propext, Quot.sound,
            // Classical.choice}); axiom_deps returns the empty set for that.
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
