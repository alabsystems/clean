// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — `NNReal` additive-monoid laws + the `0`/`1` points.
//!
//! # Why this module exists
//!
//! With `NNReal.add` landed (`algebra_nnreal_add.rs`, a nested binary
//! `Quot.lift`), the carrier needs its commutative-monoid laws so downstream
//! order/`mul`/`sqrt` reasoning can rewrite freely. Those laws all lift through
//! `Quot.ind`: they reduce, at each `Quot.mk` leaf, to a `Quot.sound` on an
//! `Equiv` between two combined Cauchy sequences whose per-index `.val`s are
//! *pointwise equal* (by the underlying `Rat`/`NNRat` law). Pointwise val
//! equality is far stronger than `Equiv`, so the per-leaf `Equiv` proof is the
//! cheap "refl-up-to-rewrite" pattern — NO ε/2 modulus bookkeeping is needed
//! (unlike `add`'s respect proof or `trans`).
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! Points (Definitions):
//! - `NNReal.zero : NNReal := NNReal.ofRat Rat.zero (Rat.le_refl Rat.zero)`
//! - `NNReal.one  : NNReal := NNReal.ofRat Rat.one  Rat.zero_le_one`
//!
//! Additive-monoid laws (Theorems, Constructive, foundational closure):
//! - `NNReal.add_comm  : ∀ x y,   NNReal.add x y = NNReal.add y x`
//! - `NNReal.add_assoc : ∀ x y z, NNReal.add (NNReal.add x y) z`
//!                                `= NNReal.add x (NNReal.add y z)`
//! - `NNReal.add_zero  : ∀ x,     NNReal.add x NNReal.zero = x`
//!
//! # The shared engine — `equiv_of_vals_eq`
//!
//! Each law's per-leaf goal is `Quot.mk L = Quot.mk R` for two CauSeqs `L`, `R`
//! with `val (seq L m) = val (seq R m)` for every `m` (the rewrite is the
//! corresponding `Rat` law lifted through `NNRat.val_add`). `equiv_of_vals_eq`
//! turns such a pointwise val-equality (supplied as a per-`m` proof builder)
//! into `Equiv L R`: for any `ε>0` take `N := Nat.zero`; for `m ≥ 0` both
//! conjuncts `val(L m) < val(R m)+ε` reduce — after substituting the equality
//! `val(L m) = val(R m)` — to `v < v+ε`, the `refl`-pattern term
//! (`add_lt_add_left 0 ε v hpos` transported along `Rat.add_zero v`).
//!
//! NO `sorry` / `add_decl_unchecked` / `add_decl_structural`. Every law is a
//! `Declaration::Theorem`; `NNReal.zero`/`NNReal.one` are `Definition`s. The
//! `Quot.ind` route uses only the foundational `Quot.*` primitives + `propext`
//! is NOT used (these are `Eq`-of-`NNReal` goals, discharged by `Quot.sound`).

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the `NNReal` additive laws.
pub(crate) struct NNAddLawConsts {
    nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    #[cfg(test)]
    nnrat: Expr,
    nnrat_val: Expr,
    nnrat_add: Expr,
    nnrat_val_add: Expr,
    causeq: Expr,
    #[cfg(test)]
    causeq_mk: Expr,
    causeq_seq: Expr,
    causeq_equiv: Expr,
    causeq_add: Expr,
    nnreal: Expr,
    nnreal_add: Expr,
    rat_add: Expr,
    rat_lt: Expr,
    #[cfg(test)]
    rat_zero_pt: Expr,
    rat_add_zero: Expr,
    rat_add_comm: Expr,
    rat_add_assoc: Expr,
    rat_add_lt_add_left: Expr,
    nat_le: Expr,
    nat_zero: Expr,
    // Quot machinery at level 1.
    quot_mk: Expr,
    quot_sound: Expr,
    quot_ind: Expr,
    // Logic.
    and_c: Expr,
    and_intro: Expr,
    exists_intro: Expr,
    // Eq.{1} over Rat / NNReal.
    #[cfg(test)]
    eq_rat: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    eq_subst: Expr,
    eq_nnreal: Expr,
    congr_arg: Expr,
}

impl NNAddLawConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            #[cfg(test)]
            nnrat: k("NNRat"),
            nnrat_val: k("NNRat.val"),
            nnrat_add: k("NNRat.add"),
            nnrat_val_add: k("NNRat.val_add"),
            causeq: k("NNReal.CauSeq"),
            #[cfg(test)]
            causeq_mk: k("NNReal.CauSeq.mk"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            causeq_add: k("NNReal.CauSeq.add"),
            nnreal: k("NNReal"),
            nnreal_add: k("NNReal.add"),
            rat_add: k("Rat.add"),
            rat_lt: k("Rat.lt"),
            #[cfg(test)]
            rat_zero_pt: k("Rat.zero"),
            rat_add_zero: k("Rat.add_zero"),
            rat_add_comm: k("Rat.add_comm"),
            rat_add_assoc: k("Rat.add_assoc"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            nat_le: k("Nat.le"),
            nat_zero: k("Nat.zero"),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![lvl1.clone()]),
            quot_sound: Expr::const_(Name::from_string("Quot.sound"), vec![lvl1.clone()]),
            quot_ind: Expr::const_(Name::from_string("Quot.ind"), vec![lvl1.clone()]),
            and_c: k("And"),
            and_intro: k("And.intro"),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![lvl1.clone()]),
            #[cfg(test)]
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1.clone()]),
            eq_nnreal: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![lvl1.clone(), lvl1]),
        }
    }

    // ── term constructors ───────────────────────────────────────────────────

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
    /// `NNReal.CauSeq.add f g : NNReal.CauSeq`.
    fn cauadd(&self, f: Expr, g: Expr) -> Expr {
        Expr::apps(self.causeq_add.clone(), [f, g])
    }
    /// `NNReal.add x y : NNReal`.
    fn nnreal_add(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [x, y])
    }
    /// `NNReal.CauSeq.Equiv a b : Prop`.
    #[cfg(test)]
    fn equiv(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_equiv.clone(), [a, b])
    }
    /// The two-sided strict-bound conjunction for `(x,y)` at `eps`.
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
    /// `@Eq.{1} NNReal a b`.
    fn eq_nnreal_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_nnreal.clone(), [self.nnreal.clone(), a, b])
    }
    /// `@Eq.{1} Rat a b`.
    #[cfg(test)]
    fn eq_rat_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_rat.clone(), [self.rat.clone(), a, b])
    }
    /// `Rat.add_lt_add_left a b c h : (c+a) < (c+b)`.
    fn add_lt_add_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add_left.clone(), [a, b, cc, h])
    }
    /// `Rat.add_zero a : Eq Rat (a+0) a`.
    fn add_zero(&self, a: Expr) -> Expr {
        Expr::app(self.rat_add_zero.clone(), a)
    }
    /// `Rat.add_comm a b : Eq Rat (a+b) (b+a)`.
    fn add_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add_comm.clone(), [a, b])
    }
    /// `Rat.add_assoc a b c : Eq Rat ((a+b)+c) (a+(b+c))`.
    fn add_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_add_assoc.clone(), [a, b, cc])
    }
    /// `NNRat.val_add p q : Eq Rat (val (NNRat.add p q)) ((val p)+(val q))`.
    fn val_add(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_val_add.clone(), [p, q])
    }
    /// `@Eq.symm Rat a b h : Eq Rat b a`.
    fn eq_symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    /// `@Eq.trans Rat a b c hab hbc : Eq Rat a c`.
    fn eq_trans_rat(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.rat.clone(), a, b, cc, hab, hbc],
        )
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b`.
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `@congrArg Rat Rat a a' f h : Eq Rat (f a)(f a')`.
    fn congr_arg(&self, a: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, a2, f, h],
        )
    }
}

impl Environment {
    /// Register the `NNReal` additive-monoid laws and the `0`/`1` points.
    /// Idempotent. Pulls in `NNReal.add` (hence the whole Cauchy carrier and
    /// `NNRat.val_add`).
    pub fn init_algebra_nnreal_add_laws(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_add()?; // NNReal.add, CauSeq.add, val_add, …
        self.register_rat_add_comm_proof()?; // Rat.add_comm
        self.register_rat_add_assoc_proof()?; // Rat.add_assoc
        self.init_rat_field_inst()?; // ensure Rat.add_zero / add_comm / add_assoc

        let c = NNAddLawConsts::new();
        self.register_nnreal_points(&c)?;
        self.register_nnreal_add_comm_recovered(&c)?;
        self.register_nnreal_add_assoc_recovered(&c)?;
        self.register_nnreal_add_zero_recovered(&c)?;
        self.register_nnreal_zero_add(&c)?;
        Ok(())
    }

    /// `NNReal.zero` / `NNReal.one` via `NNReal.ofRat`.
    fn register_nnreal_points(&mut self, c: &NNAddLawConsts) -> Result<(), EnvError> {
        let of_rat = Expr::const_(Name::from_string("NNReal.ofRat"), vec![]);

        if self.get_const(&Name::from_string("NNReal.zero")).is_none() {
            // 0 ≤ 0 via Rat.le_refl Rat.zero.
            let le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
            let h00 = Expr::app(le_refl, c.rat_zero.clone());
            let value = Expr::apps(of_rat.clone(), [c.rat_zero.clone(), h00]);
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNReal.zero"),
                level_params: vec![],
                type_: c.nnreal.clone(),
                value,
                is_reducible: true,
            })?;
        }

        if self.get_const(&Name::from_string("NNReal.one")).is_none() {
            // 0 ≤ 1 via the on-main Rat.zero_le_one (registered by the NNRat lane).
            let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
            let h01 = Expr::const_(Name::from_string("Rat.zero_le_one"), vec![]);
            let value = Expr::apps(of_rat, [rat_one, h01]);
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNReal.one"),
                level_params: vec![],
                type_: c.nnreal.clone(),
                value,
                is_reducible: true,
            })?;
        }

        Ok(())
    }

    /// `NNReal.add_comm : ∀ x y, NNReal.add x y = NNReal.add y x`.
    ///
    /// Double `Quot.ind`: at the `(mk p)(mk q)` leaf the goal reduces to
    /// `mk (CauSeq.add p q) = mk (CauSeq.add q p)`, discharged by `Quot.sound`
    /// on `Equiv (CauSeq.add p q) (CauSeq.add q p)`. That `Equiv` follows from
    /// the pointwise val-equality
    /// `val(seq(add p q) m) = (val(p m)+val(q m)) = (val(q m)+val(p m)) = val(seq(add q p) m)`
    /// (`val_add` both ways + `Rat.add_comm`).
    fn register_nnreal_add_comm_recovered(&mut self, c: &NNAddLawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.add_comm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.nnreal.clone());
            let (y_id, y) = b.fresh_local(c.nnreal.clone());
            let concl = c.eq_nnreal_ty(
                c.nnreal_add(x.clone(), y.clone()),
                c.nnreal_add(y.clone(), x.clone()),
            );
            let e = b.mk_pi(y_id, BinderInfo::Default, c.nnreal.clone(), concl);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_add_comm_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.add_assoc : ∀ x y z, add (add x y) z = add x (add y z)`.
    fn register_nnreal_add_assoc_recovered(&mut self, c: &NNAddLawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.add_assoc");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.nnreal.clone());
            let (y_id, y) = b.fresh_local(c.nnreal.clone());
            let (z_id, z) = b.fresh_local(c.nnreal.clone());
            let lhs = c.nnreal_add(c.nnreal_add(x.clone(), y.clone()), z.clone());
            let rhs = c.nnreal_add(x.clone(), c.nnreal_add(y.clone(), z.clone()));
            let concl = c.eq_nnreal_ty(lhs, rhs);
            let e = b.mk_pi(z_id, BinderInfo::Default, c.nnreal.clone(), concl);
            let e = b.mk_pi(y_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_add_assoc_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.add_zero : ∀ x, NNReal.add x NNReal.zero = x`.
    ///
    /// `Quot.ind` on `x`: at the `mk p` leaf the goal reduces to
    /// `mk (CauSeq.add p (CauSeq.const NNRat.zero)) = mk p`. `Quot.sound` on
    /// `Equiv (CauSeq.add p zero-seq) p` from the pointwise val-equality
    /// `val(seq(add p zc) m) = val(p m) + 0 = val(p m)` (`val_add` + the
    /// `val(zero-const) m = 0` reduction + `Rat.add_zero`).
    fn register_nnreal_add_zero_recovered(&mut self, c: &NNAddLawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.add_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.nnreal.clone());
            let nnreal_zero = Expr::const_(Name::from_string("NNReal.zero"), vec![]);
            let concl = c.eq_nnreal_ty(c.nnreal_add(x.clone(), nnreal_zero), x.clone());
            let e = b.mk_pi(x_id, BinderInfo::Default, c.nnreal.clone(), concl);
            b.finish(e)
        };
        let value = build_add_zero_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.zero_add : ∀ x, NNReal.add NNReal.zero x = x`.
    ///
    /// The left-identity law, derived purely from the two already-registered
    /// theorems (no fresh `Quot.ind`): `add_comm 0 x : add 0 x = add x 0` chained
    /// through `add_zero x : add x 0 = x` by `Eq.trans`.
    fn register_nnreal_zero_add(&mut self, c: &NNAddLawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.zero_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nnreal_zero = Expr::const_(Name::from_string("NNReal.zero"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.nnreal.clone());
            let concl = c.eq_nnreal_ty(c.nnreal_add(nnreal_zero.clone(), x.clone()), x.clone());
            let e = b.mk_pi(x_id, BinderInfo::Default, c.nnreal.clone(), concl);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.nnreal.clone());

            let add_0x = c.nnreal_add(nnreal_zero.clone(), x.clone());
            let add_x0 = c.nnreal_add(x.clone(), nnreal_zero.clone());

            // h1 : add 0 x = add x 0   (NNReal.add_comm 0 x).
            let add_comm = Expr::const_(Name::from_string("NNReal.add_comm"), vec![]);
            let h1 = Expr::apps(add_comm, [nnreal_zero.clone(), x.clone()]);
            // h2 : add x 0 = x          (NNReal.add_zero x).
            let add_zero = Expr::const_(Name::from_string("NNReal.add_zero"), vec![]);
            let h2 = Expr::app(add_zero, x.clone());
            // Eq.trans NNReal (add 0 x)(add x 0) x h1 h2.
            let eq_trans_nn = Expr::const_(
                Name::from_string("Eq.trans"),
                vec![Level::succ(Level::zero())],
            );
            let body = Expr::apps(
                eq_trans_nn,
                [c.nnreal.clone(), add_0x, add_x0, x.clone(), h1, h2],
            );
            let e = b.mk_lam(x_id, BinderInfo::Default, c.nnreal.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build `Equiv L R` from a per-`m` proof of `val(seq L m) = val(seq R m)`.
///
/// `vals_eq(parent, m) : Eq Rat (val(seq L m)) (val(seq R m))`. For any `ε,0<ε`
/// pick `N := Nat.zero`; for `m ≥ 0`:
///   `p : val(L m) < val(L m) + ε`  (`add_lt_add_left 0 ε v hpos` ▷ `add_zero v`)
/// then transport the RHS summand `val(L m) → val(R m)` (via `vals_eq m`) to get
/// `val(L m) < val(R m) + ε`, and the LHS `val(L m) → val(R m)` to get
/// `val(R m) < val(L m) + ε`. `And.intro` pairs them; `Exists.intro Nat.zero …`.
fn build_equiv_of_vals_eq(
    c: &NNAddLawConsts,
    parent: &EnvDeclBuilder,
    l: &Expr,
    r: &Expr,
    vals_eq: &dyn Fn(&EnvDeclBuilder, &Expr) -> Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    // pred_n N := ∀ m, Nat.le N m → bound_pair (vseq L m)(vseq R m) ε
    let pred_n = {
        let mut bn = EnvDeclBuilder::child_of(&b);
        let (n_id, n_cap) = bn.fresh_local(c.nat.clone());
        let inner = {
            let mut bi = EnvDeclBuilder::child_of(&bn);
            let (m_id, m) = bi.fresh_local(c.nat.clone());
            let hle = c.nat_le(n_cap.clone(), m.clone());
            let (hle_id, _h) = bi.fresh_local(hle.clone());
            let concl = c.bound_pair(c.vseq(l, &m), c.vseq(r, &m), eps.clone());
            let e = bi.mk_pi(hle_id, BinderInfo::Default, hle, concl);
            let e = bi.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            bi.finish_child(e)
        };
        let lam = bn.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), inner);
        bn.finish_child(lam)
    };

    // witness : ∀ m, Nat.le 0 m → bound_pair (vseq L m)(vseq R m) ε.
    let witness = {
        let mut bw = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = bw.fresh_local(c.nat.clone());
        let hle = c.nat_le(c.nat_zero.clone(), m.clone());
        let (hle_id, _h) = bw.fresh_local(hle.clone());

        let vl = c.vseq(l, &m); // val(seq L m)
        let vr = c.vseq(r, &m); // val(seq R m)
        let heq = vals_eq(&bw, &m); // val(L m) = val(R m)

        // p0 : (vl + 0) < (vl + ε)  := add_lt_add_left 0 ε vl hpos.
        let p0 = c.add_lt_add_left(c.rat_zero.clone(), eps.clone(), vl.clone(), hpos.clone());
        // p : vl < vl + ε  — transport LHS (vl+0)→vl via add_zero vl.
        //   motive t := t < vl+ε.
        let vl_plus_eps = c.radd(vl.clone(), eps.clone());
        let motive_p = {
            let mut mb = EnvDeclBuilder::child_of(&bw);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.lt(t, vl_plus_eps.clone());
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let vl_plus_zero = c.radd(vl.clone(), c.rat_zero.clone());
        let p = c.subst_rat(
            motive_p,
            vl_plus_zero,
            vl.clone(),
            c.add_zero(vl.clone()),
            p0,
        );

        // left : vl < vr + ε  — from p : vl < vl + ε, rewrite the RHS summand
        //   vl → vr via heq.  motive t := vl < t + ε.
        let motive_l = {
            let mut mb = EnvDeclBuilder::child_of(&bw);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.lt(vl.clone(), c.radd(t, eps.clone()));
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let left = c.subst_rat(motive_l, vl.clone(), vr.clone(), heq.clone(), p);

        // right : vr < vl + ε  — symmetric. Start from p' : vr < vr + ε, then
        //   rewrite the RHS summand vr → vl via (Eq.symm heq).
        let p0r = c.add_lt_add_left(c.rat_zero.clone(), eps.clone(), vr.clone(), hpos.clone());
        let vr_plus_eps = c.radd(vr.clone(), eps.clone());
        let motive_pr = {
            let mut mb = EnvDeclBuilder::child_of(&bw);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.lt(t, vr_plus_eps.clone());
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let vr_plus_zero = c.radd(vr.clone(), c.rat_zero.clone());
        let pr = c.subst_rat(
            motive_pr,
            vr_plus_zero,
            vr.clone(),
            c.add_zero(vr.clone()),
            p0r,
        );
        // motive t := vr < t + ε ; rewrite vr → vl via Eq.symm heq.
        let motive_r = {
            let mut mb = EnvDeclBuilder::child_of(&bw);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.lt(vr.clone(), c.radd(t, eps.clone()));
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let heq_sym = c.eq_symm_rat(vl.clone(), vr.clone(), heq);
        let right = c.subst_rat(motive_r, vr.clone(), vl.clone(), heq_sym, pr);

        // And.intro (vl<vr+ε)(vr<vl+ε) left right.
        let l_ty = c.lt(vl.clone(), c.radd(vr.clone(), eps.clone()));
        let r_ty = c.lt(vr.clone(), c.radd(vl.clone(), eps.clone()));
        let proof = Expr::apps(c.and_intro.clone(), [l_ty, r_ty, left, right]);

        let e = bw.mk_lam(hle_id, BinderInfo::Default, hle, proof);
        let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
        bw.finish_child(e)
    };

    let intro = Expr::apps(
        c.exists_intro.clone(),
        [c.nat.clone(), pred_n, c.nat_zero.clone(), witness],
    );
    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, intro);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish_child(e)
}

/// Run a binary `Quot.ind` (on `x` then `y`) producing, at each `(mk p)(mk q)`
/// leaf, the term `leaf(p, q) : Eq NNReal (lhs(mk p)(mk q)) (rhs(mk p)(mk q))`.
///
/// `lhs`/`rhs` are functions of the two `NNReal` arguments giving the two sides
/// of the goal equality; `leaf` builds the proof at the representative level.
/// Returns `fun x y => …` of type `∀ x y, Eq NNReal (lhs x y)(rhs x y)`.
fn build_binary_quot_ind(
    c: &NNAddLawConsts,
    lhs: &dyn Fn(&Expr, &Expr) -> Expr,
    rhs: &dyn Fn(&Expr, &Expr) -> Expr,
    leaf: &dyn Fn(&EnvDeclBuilder, &Expr, &Expr) -> Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.nnreal.clone());
    let (y_id, y) = b.fresh_local(c.nnreal.clone());

    // Outer ind on x: motive_x u := Eq NNReal (lhs u y)(rhs u y).
    let motive_x = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (u_id, u) = mb.fresh_local(c.nnreal.clone());
        let body = c.eq_nnreal_ty(lhs(&u, &y), rhs(&u, &y));
        mb.finish_child(mb.mk_lam(u_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    // Outer minor: fun (p : CauSeq) => inner-ind on y at (mk p).
    let minor_x = {
        let mut bp = EnvDeclBuilder::child_of(&b);
        let (p_id, p) = bp.fresh_local(c.causeq.clone());
        let mk_p = c.quot_mk(p.clone());

        // Inner ind on y: motive_y v := Eq NNReal (lhs (mk p) v)(rhs (mk p) v).
        let motive_y = {
            let mut mb = EnvDeclBuilder::child_of(&bp);
            let (v_id, v) = mb.fresh_local(c.nnreal.clone());
            let body = c.eq_nnreal_ty(lhs(&mk_p, &v), rhs(&mk_p, &v));
            mb.finish_child(mb.mk_lam(v_id, BinderInfo::Default, c.nnreal.clone(), body))
        };
        let minor_y = {
            let mut bq = EnvDeclBuilder::child_of(&bp);
            let (q_id, q) = bq.fresh_local(c.causeq.clone());
            let body = leaf(&bq, &p, &q);
            bq.finish_child(bq.mk_lam(q_id, BinderInfo::Default, c.causeq.clone(), body))
        };
        let inner = Expr::apps(
            c.quot_ind.clone(),
            [
                c.causeq.clone(),
                c.causeq_equiv.clone(),
                motive_y,
                minor_y,
                y.clone(),
            ],
        );
        bp.finish_child(bp.mk_lam(p_id, BinderInfo::Default, c.causeq.clone(), inner))
    };
    let outer = Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive_x,
            minor_x,
            x.clone(),
        ],
    );
    let e = b.mk_lam(y_id, BinderInfo::Default, c.nnreal.clone(), outer);
    let e = b.mk_lam(x_id, BinderInfo::Default, c.nnreal.clone(), e);
    b.finish(e)
}

/// Proof of `NNReal.add_comm` (see registration doc).
fn build_add_comm_proof(c: &NNAddLawConsts) -> Expr {
    let lhs = |x: &Expr, y: &Expr| c.nnreal_add(x.clone(), y.clone());
    let rhs = |x: &Expr, y: &Expr| c.nnreal_add(y.clone(), x.clone());
    let leaf = |parent: &EnvDeclBuilder, p: &Expr, q: &Expr| -> Expr {
        // L := CauSeq.add p q ; R := CauSeq.add q p.
        let cl = c.cauadd(p.clone(), q.clone());
        let cr = c.cauadd(q.clone(), p.clone());
        // vals_eq m : val(seq L m) = val(seq R m).
        //   val(seq L m) ≡ val(NNRat.add (p m)(q m))  →[val_add]  (vp+vq)
        //                ≡  →[add_comm]  (vq+vp)  ≡[val_add⁻¹]  val(seq R m).
        let vals_eq = |_bb: &EnvDeclBuilder, m: &Expr| -> Expr {
            let pm = c.seq_at(p, m);
            let qm = c.seq_at(q, m);
            let vp = c.val(pm.clone());
            let vq = c.val(qm.clone());
            // e1 : val(NNRat.add (p m)(q m)) = vp+vq.
            let e1 = c.val_add(pm.clone(), qm.clone());
            // e2 : vp+vq = vq+vp.
            let e2 = c.add_comm(vp.clone(), vq.clone());
            // e3 : val(NNRat.add (q m)(p m)) = vq+vp ; we want its symm.
            let e3 = c.val_add(qm.clone(), pm.clone());
            let v_add_pq = c.val(c.nnadd(pm.clone(), qm.clone()));
            let v_add_qp = c.val(c.nnadd(qm.clone(), pm.clone()));
            let vp_vq = c.radd(vp.clone(), vq.clone());
            let vq_vp = c.radd(vq.clone(), vp.clone());
            // chain: v_add_pq =[e1] vp+vq =[e2] vq+vp =[symm e3] v_add_qp.
            let t1 = c.eq_trans_rat(v_add_pq.clone(), vp_vq, vq_vp.clone(), e1, e2);
            let e3_sym = c.eq_symm_rat(v_add_qp.clone(), vq_vp.clone(), e3);
            c.eq_trans_rat(v_add_pq, vq_vp, v_add_qp, t1, e3_sym)
        };
        let eqv = build_equiv_of_vals_eq(c, parent, &cl, &cr, &vals_eq);
        c.quot_sound(cl, cr, eqv)
    };
    build_binary_quot_ind(c, &lhs, &rhs, &leaf)
}

/// Proof of `NNReal.add_assoc` (ternary `Quot.ind`).
fn build_add_assoc_proof(c: &NNAddLawConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.nnreal.clone());
    let (y_id, y) = b.fresh_local(c.nnreal.clone());
    let (z_id, z) = b.fresh_local(c.nnreal.clone());

    let lhs =
        |x: &Expr, y: &Expr, z: &Expr| c.nnreal_add(c.nnreal_add(x.clone(), y.clone()), z.clone());
    let rhs =
        |x: &Expr, y: &Expr, z: &Expr| c.nnreal_add(x.clone(), c.nnreal_add(y.clone(), z.clone()));

    // Ternary nested Quot.ind on x, then y, then z.
    let motive_x = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (u_id, u) = mb.fresh_local(c.nnreal.clone());
        let body = c.eq_nnreal_ty(lhs(&u, &y, &z), rhs(&u, &y, &z));
        mb.finish_child(mb.mk_lam(u_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let minor_x = {
        let mut bp = EnvDeclBuilder::child_of(&b);
        let (p_id, p) = bp.fresh_local(c.causeq.clone());
        let mk_p = c.quot_mk(p.clone());
        let motive_y = {
            let mut mb = EnvDeclBuilder::child_of(&bp);
            let (v_id, v) = mb.fresh_local(c.nnreal.clone());
            let body = c.eq_nnreal_ty(lhs(&mk_p, &v, &z), rhs(&mk_p, &v, &z));
            mb.finish_child(mb.mk_lam(v_id, BinderInfo::Default, c.nnreal.clone(), body))
        };
        let minor_y = {
            let mut bq = EnvDeclBuilder::child_of(&bp);
            let (q_id, q) = bq.fresh_local(c.causeq.clone());
            let mk_q = c.quot_mk(q.clone());
            let motive_z = {
                let mut mb = EnvDeclBuilder::child_of(&bq);
                let (w_id, w) = mb.fresh_local(c.nnreal.clone());
                let body = c.eq_nnreal_ty(lhs(&mk_p, &mk_q, &w), rhs(&mk_p, &mk_q, &w));
                mb.finish_child(mb.mk_lam(w_id, BinderInfo::Default, c.nnreal.clone(), body))
            };
            let minor_z = {
                let mut br = EnvDeclBuilder::child_of(&bq);
                let (r_id, rr) = br.fresh_local(c.causeq.clone());
                let body = build_assoc_leaf(c, &br, &p, &q, &rr);
                br.finish_child(br.mk_lam(r_id, BinderInfo::Default, c.causeq.clone(), body))
            };
            let inner_z = Expr::apps(
                c.quot_ind.clone(),
                [
                    c.causeq.clone(),
                    c.causeq_equiv.clone(),
                    motive_z,
                    minor_z,
                    z.clone(),
                ],
            );
            bq.finish_child(bq.mk_lam(q_id, BinderInfo::Default, c.causeq.clone(), inner_z))
        };
        let inner_y = Expr::apps(
            c.quot_ind.clone(),
            [
                c.causeq.clone(),
                c.causeq_equiv.clone(),
                motive_y,
                minor_y,
                y.clone(),
            ],
        );
        bp.finish_child(bp.mk_lam(p_id, BinderInfo::Default, c.causeq.clone(), inner_y))
    };
    let outer = Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive_x,
            minor_x,
            x.clone(),
        ],
    );
    let e = b.mk_lam(z_id, BinderInfo::Default, c.nnreal.clone(), outer);
    let e = b.mk_lam(y_id, BinderInfo::Default, c.nnreal.clone(), e);
    let e = b.mk_lam(x_id, BinderInfo::Default, c.nnreal.clone(), e);
    b.finish(e)
}

/// `add_assoc` leaf: `mk (CauSeq.add (CauSeq.add p q) r) = mk (CauSeq.add p (CauSeq.add q r))`.
fn build_assoc_leaf(
    c: &NNAddLawConsts,
    parent: &EnvDeclBuilder,
    p: &Expr,
    q: &Expr,
    r: &Expr,
) -> Expr {
    let cl = c.cauadd(c.cauadd(p.clone(), q.clone()), r.clone());
    let cr = c.cauadd(p.clone(), c.cauadd(q.clone(), r.clone()));
    // vals_eq m : val(seq L m) = val(seq R m).
    //   L m ≡ NNRat.add (NNRat.add (p m)(q m)) (r m)
    //       val =[val_add] (val(add(p m)(q m)) + vr) =[congr val_add] ((vp+vq)+vr)
    //                      =[add_assoc] (vp+(vq+vr))
    //   R m ≡ NNRat.add (p m) (NNRat.add (q m)(r m))
    //       val =[val_add] (vp + val(add(q m)(r m))) =[congr val_add] (vp+(vq+vr)).
    let vals_eq = |bb: &EnvDeclBuilder, m: &Expr| -> Expr {
        let pm = c.seq_at(p, m);
        let qm = c.seq_at(q, m);
        let rm = c.seq_at(r, m);
        let vp = c.val(pm.clone());
        let vq = c.val(qm.clone());
        let vr = c.val(rm.clone());

        let add_pq = c.nnadd(pm.clone(), qm.clone()); // NNRat.add (p m)(q m)
        let add_qr = c.nnadd(qm.clone(), rm.clone()); // NNRat.add (q m)(r m)
        let v_add_pq = c.val(add_pq.clone()); // val(add(p m)(q m))
        let v_add_qr = c.val(add_qr.clone());

        let vp_vq = c.radd(vp.clone(), vq.clone());
        let vq_vr = c.radd(vq.clone(), vr.clone());
        let lhs_outer_nn = c.nnadd(add_pq.clone(), rm.clone()); // NNRat.add (add pq)(r m)
        let rhs_outer_nn = c.nnadd(pm.clone(), add_qr.clone()); // NNRat.add (p m)(add qr)
        let v_lhs = c.val(lhs_outer_nn.clone());
        let v_rhs = c.val(rhs_outer_nn.clone());

        // ── LHS chain: v_lhs = (vp+(vq+vr)) ──
        // l1 : v_lhs = (v_add_pq + vr)            [val_add (add pq) (r m)].
        let l1 = c.val_add(add_pq.clone(), rm.clone());
        // l2 : (v_add_pq + vr) = ((vp+vq) + vr)   [congrArg (·+vr) (val_add p q)].
        let add_vr_fn = {
            let mut fb = EnvDeclBuilder::child_of(bb);
            let (t_id, t) = fb.fresh_local(c.rat.clone());
            let body = c.radd(t, vr.clone());
            fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let l2 = c.congr_arg(
            v_add_pq.clone(),
            vp_vq.clone(),
            add_vr_fn,
            c.val_add(pm.clone(), qm.clone()),
        );
        // l3 : ((vp+vq)+vr) = (vp+(vq+vr))         [add_assoc vp vq vr].
        let l3 = c.add_assoc(vp.clone(), vq.clone(), vr.clone());
        let v_add_pq_vr = c.radd(v_add_pq.clone(), vr.clone());
        let vpvq_vr = c.radd(vp_vq.clone(), vr.clone());
        let vp_vqvr = c.radd(vp.clone(), vq_vr.clone());
        let lc1 = c.eq_trans_rat(v_lhs.clone(), v_add_pq_vr, vpvq_vr.clone(), l1, l2);
        let l_chain = c.eq_trans_rat(v_lhs.clone(), vpvq_vr, vp_vqvr.clone(), lc1, l3);

        // ── RHS chain: v_rhs = (vp+(vq+vr)) ──
        // r1 : v_rhs = (vp + v_add_qr)             [val_add (p m)(add qr)].
        let r1 = c.val_add(pm.clone(), add_qr.clone());
        // r2 : (vp + v_add_qr) = (vp + (vq+vr))    [congrArg (vp+·) (val_add q r)].
        let add_vp_fn = {
            let mut fb = EnvDeclBuilder::child_of(bb);
            let (t_id, t) = fb.fresh_local(c.rat.clone());
            let body = c.radd(vp.clone(), t);
            fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let r2 = c.congr_arg(
            v_add_qr.clone(),
            vq_vr.clone(),
            add_vp_fn,
            c.val_add(qm.clone(), rm.clone()),
        );
        let vp_vaddqr = c.radd(vp.clone(), v_add_qr.clone());
        let r_chain = c.eq_trans_rat(v_rhs.clone(), vp_vaddqr, vp_vqvr.clone(), r1, r2);

        // vals_eq := v_lhs =[l_chain] (vp+(vq+vr)) =[symm r_chain] v_rhs.
        let r_chain_sym = c.eq_symm_rat(v_rhs.clone(), vp_vqvr.clone(), r_chain);
        c.eq_trans_rat(v_lhs, vp_vqvr, v_rhs, l_chain, r_chain_sym)
    };
    let eqv = build_equiv_of_vals_eq(c, parent, &cl, &cr, &vals_eq);
    c.quot_sound(cl, cr, eqv)
}

/// Proof of `NNReal.add_zero` (unary `Quot.ind`).
fn build_add_zero_proof(c: &NNAddLawConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.nnreal.clone());
    let nnreal_zero = Expr::const_(Name::from_string("NNReal.zero"), vec![]);

    let lhs = |x: &Expr| c.nnreal_add(x.clone(), nnreal_zero.clone());
    let rhs = |x: &Expr| x.clone();

    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (u_id, u) = mb.fresh_local(c.nnreal.clone());
        let body = c.eq_nnreal_ty(lhs(&u), rhs(&u));
        mb.finish_child(mb.mk_lam(u_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let minor = {
        let mut bp = EnvDeclBuilder::child_of(&b);
        let (p_id, p) = bp.fresh_local(c.causeq.clone());
        let body = build_add_zero_leaf(c, &bp, &p);
        bp.finish_child(bp.mk_lam(p_id, BinderInfo::Default, c.causeq.clone(), body))
    };
    let ind = Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            x.clone(),
        ],
    );
    let e = b.mk_lam(x_id, BinderInfo::Default, c.nnreal.clone(), ind);
    b.finish(e)
}

/// `add_zero` leaf: `mk (CauSeq.add p (CauSeq.const NNRat.zero)) = mk p`.
///
/// `NNReal.zero ≡ mk (CauSeq.const (NNRat.ofRat 0 _))` and
/// `NNReal.add (mk p) NNReal.zero ≡ mk (CauSeq.add p (CauSeq.const z))` where
/// `z := NNRat.ofRat Rat.zero _`. The Equiv `Equiv (CauSeq.add p zc) p` follows
/// from `val(seq(add p zc) m) = val(p m) + val(zc m) = val(p m) + 0 = val(p m)`:
/// `val_add` then `val(zc m) ≡ 0` (`val(ofRat 0 _) = 0` by `val_ofRat`/reduction)
/// then `Rat.add_zero`.
fn build_add_zero_leaf(c: &NNAddLawConsts, parent: &EnvDeclBuilder, p: &Expr) -> Expr {
    // z := NNRat.ofRat Rat.zero (Rat.le_refl Rat.zero) — the same nonneg witness
    // NNReal.zero / NNRat.zero use, so the CauSeq matches definitionally.
    let le_refl0 = Expr::app(
        Expr::const_(Name::from_string("Rat.le_refl"), vec![]),
        c.rat_zero.clone(),
    );
    let z = Expr::apps(
        Expr::const_(Name::from_string("NNRat.ofRat"), vec![]),
        [c.rat_zero.clone(), le_refl0],
    );
    let const_zc = Expr::app(
        Expr::const_(Name::from_string("NNReal.CauSeq.const"), vec![]),
        z.clone(),
    );
    let cl = c.cauadd(p.clone(), const_zc.clone());

    // vals_eq m : val(seq L m) = val(seq p m).
    //   L m ≡ NNRat.add (p m) (NNReal.CauSeq.seq (const z) m) ≡ NNRat.add (p m) z.
    //   val =[val_add] (vp + val z) ; val z ≡ 0 (Subtype.val (Subtype.mk 0 _)).
    //   So (vp + val z) ≡ (vp + 0) =[add_zero] vp.
    let vals_eq = |_bb: &EnvDeclBuilder, m: &Expr| -> Expr {
        let pm = c.seq_at(p, m); // p m
        let vp = c.val(pm.clone()); // vp
                                    // seq(const z) m ≡ z (CauSeq.const reduces), so L m ≡ NNRat.add (p m) z.
        let add_pz = c.nnadd(pm.clone(), z.clone());
        let v_lhs = c.val(add_pz.clone()); // val(seq L m) (defeq)
                                           // e1 : v_lhs = (vp + val z)         [val_add (p m) z].
        let e1 = c.val_add(pm.clone(), z.clone());
        let vz = c.val(z.clone()); // val z  (≡ Rat.zero definitionally)
        let vp_vz = c.radd(vp.clone(), vz.clone());
        // val z ≡ Rat.zero, so (vp + val z) ≡ (vp + 0); add_zero vp : (vp+0)=vp.
        // The kernel accepts add_zero vp at type (vp + val z) = vp by defeq
        // (val z reduces to Rat.zero), so e2 : (vp + val z) = vp.
        let e2 = c.add_zero(vp.clone());
        // chain: v_lhs =[e1] (vp+val z) =[e2] vp.
        c.eq_trans_rat(v_lhs, vp_vz, vp.clone(), e1, e2)
    };
    let eqv = build_equiv_of_vals_eq(c, parent, &cl, p, &vals_eq);
    c.quot_sound(cl, p.clone(), eqv)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const DEFS: &[&str] = &["NNReal.zero", "NNReal.one"];
    const THEOREMS: &[&str] = &[
        "NNReal.add_comm",
        "NNReal.add_assoc",
        "NNReal.add_zero",
        "NNReal.zero_add",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_add_laws()
            .expect("init_algebra_nnreal_add_laws");
        env.init_algebra_nnreal_add_laws().expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_add_laws_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in DEFS.iter().chain(THEOREMS.iter()) {
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
    fn test_nnreal_add_laws_constructive_empty_closure() {
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
