// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! NNReal `finSum` block split — the NNReal duals of the landed Rat
//! `Fin.sum_cast` / `Fin.sum_split_add`, the structural bricks the `(4/3,4)`
//! tensorization norm-split residual (D) needs at the NNReal level (the
//! `contribution`/`pow43Gen` summand is NOT `ofRat`, so the Rat `finSumPow2*`
//! cannot be lifted — the split must live natively over `NNReal.finSum`).
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNReal.finSum_cast : ∀ (a b : Nat) (e : @Eq Nat b a) (F : Fin a → NNReal),`
//!   `  @Eq NNReal (NNReal.finSum a F)`
//!   `             (NNReal.finSum b (fun i => F (cast_{b→a} i)))`
//!   where `cast_{b→a} i := @Eq.ndrec Nat b (fun m => Fin m) i a e`. Proved by
//!   `@Eq.rec` on `e`: in the `e = rfl` case the transport collapses to the
//!   identity, so the goal is `rfl`.
//!
//! - `NNReal.finSum_split_add : ∀ (a b : Nat) (h : Fin (a+b) → NNReal),`
//!   `  @Eq NNReal (NNReal.finSum (a+b) h)`
//!   `            (NNReal.add (NNReal.finSum a (fun i => h (Fin.castAdd a b i)))`
//!   `                         (NNReal.finSum b (fun j => h (Fin.addNat a b j))))`
//!   — induction on `b` via `Nat.rec.{0}` with `a` fixed (the conclusion is an
//!   `Eq` in `Prop`). Byte-for-byte the structure of the landed Rat
//!   `Fin.sum_split_add` (`nn_verify_fin_sum_split_proof.rs`): `NNReal.finSum_succ`
//!   peels the top index, the IH splits the prefix, three
//!   `NNReal.finSum_congr`/`congrArg` reindexings (`castSucc∘castAdd ≈ castAdd`,
//!   `castSucc∘addNat ≈ addNat∘castSucc`, `last ≈ addNat … last`) line the pieces
//!   up, and a single `NNReal.add_assoc` reassociates. Every `Fin` index
//!   correspondence is "equal `val` ⟹ propositionally equal `Fin`", discharged by
//!   `Fin.eq_of_val_eq` on `@Eq.refl Nat`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural` / `Declaration::Axiom`.

use super::algebra_nnreal_finsum::NNFinSumConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached constants + smart-constructors for the NNReal block split. Wraps the
/// shared `NNFinSumConsts` (finSum carrier surface) with the `Fin` reindex maps,
/// `Fin.eq_of_val_eq`, the `NNReal` add field lemmas, and the `Eq` plumbing.
struct C {
    base: NNFinSumConsts,
    nat: Expr,
    nat_zero: Expr,
    nat_add: Expr,
    fin: Expr,
    fin_val: Expr,
    fin_cast_succ: Expr,
    fin_cast_add: Expr,
    fin_add_nat: Expr,
    fin_last: Expr,
    fin_eq_of_val: Expr,
    nnreal_finsum_congr: Expr,
    nnreal_finsum_succ: Expr,
    nnreal_add_zero: Expr,
    nnreal_add_assoc: Expr,
    nat_rec0: Expr,     // Nat.rec.{0} (Prop-valued motive)
    eq_nat: Expr,       // Eq.{1} over Nat
    eq_refl_nat: Expr,  // Eq.refl.{1} over Nat
    eq_trans1: Expr,    // Eq.trans.{1}
    eq_symm1: Expr,     // Eq.symm.{1}
    eq_refl1: Expr,     // Eq.refl.{1}
    eq_rec01: Expr,     // Eq.rec.{0,1} : Prop-valued motive over Nat (Sort 1)
    eq_ndrec_fin: Expr, // Eq.ndrec.{1,1} : Nat-motive → Fin m
    congr_arg_nn: Expr, // congrArg.{1,1} : NNReal → NNReal
    congr_arg_fn: Expr, // congrArg.{1,1} : Fin big → NNReal
}

impl C {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            base: NNFinSumConsts::new(),
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_add: k("Nat.add"),
            fin: k("Fin"),
            fin_val: k("Fin.val"),
            fin_cast_succ: k("Fin.castSucc"),
            fin_cast_add: k("Fin.castAdd"),
            fin_add_nat: k("Fin.addNat"),
            fin_last: k("Fin.last"),
            fin_eq_of_val: k("Fin.eq_of_val_eq"),
            nnreal_finsum_congr: k("NNReal.finSum_congr"),
            nnreal_finsum_succ: k("NNReal.finSum_succ"),
            nnreal_add_zero: k("NNReal.add_zero"),
            nnreal_add_assoc: k("NNReal.add_assoc"),
            nat_rec0: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            eq_nat: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl_nat: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_rec01: Expr::const_(Name::from_string("Eq.rec"), vec![Level::zero(), l1.clone()]),
            eq_ndrec_fin: Expr::const_(Name::from_string("Eq.ndrec"), vec![l1.clone(), l1.clone()]),
            congr_arg_nn: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            congr_arg_fn: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn nnreal(&self) -> Expr {
        self.base.nnreal.clone()
    }
    fn fin_n(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn fin_to_nnreal(&self, n: &Expr) -> Expr {
        self.base.fin_to_nnreal(n.clone())
    }
    fn add_nat_(&self, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [x.clone(), y.clone()])
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.base.nat_succ.clone(), n.clone())
    }
    fn val(&self, n: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [n.clone(), x.clone()])
    }
    fn sum(&self, n: &Expr, f: &Expr) -> Expr {
        self.base.sum(n.clone(), f.clone())
    }
    fn nadd(&self, x: &Expr, y: &Expr) -> Expr {
        self.base.add(x.clone(), y.clone())
    }
    fn eq_nn(&self, l: &Expr, r: &Expr) -> Expr {
        self.base.eq_nnreal(l.clone(), r.clone())
    }
    fn eq_nat_(&self, l: &Expr, r: &Expr) -> Expr {
        Expr::apps(
            self.eq_nat.clone(),
            [self.nat.clone(), l.clone(), r.clone()],
        )
    }
    /// `@Eq.trans NNReal l m r h1 h2`.
    fn trans(&self, l: &Expr, m: &Expr, r: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans1.clone(),
            [self.nnreal(), l.clone(), m.clone(), r.clone(), h1, h2],
        )
    }
    /// `@Eq.symm NNReal l r h`.
    fn symm(&self, l: &Expr, r: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_symm1.clone(),
            [self.nnreal(), l.clone(), r.clone(), h],
        )
    }
    /// `@congrArg NNReal NNReal l r f h` — `f : NNReal → NNReal`.
    fn congr_nn_fn(&self, l: &Expr, r: &Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg_nn.clone(),
            [self.nnreal(), self.nnreal(), l.clone(), r.clone(), f, h],
        )
    }
    fn cast_add(&self, a: &Expr, b: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.fin_cast_add.clone(), [a.clone(), b.clone(), i.clone()])
    }
    fn add_nat_idx(&self, a: &Expr, b: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.fin_add_nat.clone(), [a.clone(), b.clone(), j.clone()])
    }
    fn cast_succ(&self, n: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.fin_cast_succ.clone(), [n.clone(), i.clone()])
    }
    fn last(&self, n: &Expr) -> Expr {
        Expr::app(self.fin_last.clone(), n.clone())
    }
    /// `@NNReal.finSum_congr k f g pw : finSum k f = finSum k g`.
    fn sum_congr(&self, k: &Expr, f: &Expr, g: &Expr, pw: Expr) -> Expr {
        Expr::apps(
            self.nnreal_finsum_congr.clone(),
            [k.clone(), f.clone(), g.clone(), pw],
        )
    }
}

/// `fun (x : Fin k) => body(x)`.
fn lam_fin<Fb>(c: &C, parent: &EnvDeclBuilder, k: &Expr, body: Fb) -> Expr
where
    Fb: FnOnce(&mut EnvDeclBuilder, Expr) -> Expr,
{
    let fin_k = c.fin_n(k);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = b.fresh_local(fin_k.clone());
    let bd = body(&mut b, x);
    let lam = b.mk_lam(x_id, BinderInfo::Default, fin_k, bd);
    b.finish_child(lam)
}

/// The pointwise reindex hypothesis `fun (x : Fin k) =>
///   @congrArg (Fin big) NNReal (m1 x) (m2 x) h
///     (@Fin.eq_of_val_eq big (m1 x) (m2 x) (@Eq.refl Nat (val big (m1 x))))`.
/// `m1 x`/`m2 x` are two `Fin big` elements with DEFINITIONALLY EQUAL `val`, so
/// the `Eq.refl` discharges `val (m1 x) = val (m2 x)`, proving `h (m1 x) = h (m2 x)`.
fn reindex_pw<M1, M2>(
    c: &C,
    parent: &EnvDeclBuilder,
    k: &Expr,
    big: &Expr,
    h: &Expr,
    m1: M1,
    m2: M2,
) -> Expr
where
    M1: Fn(&C, Expr) -> Expr,
    M2: Fn(&C, Expr) -> Expr,
{
    let fin_big = c.fin_n(big);
    lam_fin(c, parent, k, |_b, x| {
        let lhs = m1(c, x.clone());
        let rhs = m2(c, x);
        let refl = Expr::apps(c.eq_refl_nat.clone(), [c.nat.clone(), c.val(big, &lhs)]);
        let eqf = Expr::apps(
            c.fin_eq_of_val.clone(),
            [big.clone(), lhs.clone(), rhs.clone(), refl],
        );
        Expr::apps(
            c.congr_arg_fn.clone(),
            [fin_big.clone(), c.nnreal(), lhs, rhs, h.clone(), eqf],
        )
    })
}

/// `Eq NNReal (finSum (a+b) h)
///            (add (finSum a (h∘castAdd a b)) (finSum b (h∘addNat a b)))`.
fn concl_body(c: &C, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, h: &Expr) -> Expr {
    let ab = c.add_nat_(a, b);
    let lhs = c.sum(&ab, h);
    let low = {
        let h = h.clone();
        let av = a.clone();
        let bv = b.clone();
        lam_fin(c, parent, a, move |_bd, i| {
            Expr::app(h.clone(), c.cast_add(&av, &bv, &i))
        })
    };
    let high = {
        let h = h.clone();
        let av = a.clone();
        let bv = b.clone();
        lam_fin(c, parent, b, move |_bd, j| {
            Expr::app(h.clone(), c.add_nat_idx(&av, &bv, &j))
        })
    };
    let rhs = c.nadd(&c.sum(a, &low), &c.sum(b, &high));
    c.eq_nn(&lhs, &rhs)
}

include!("algebra_nnreal_finsum_split_step.rs");

impl Environment {
    /// Register `NNReal.finSum_cast` and `NNReal.finSum_split_add`. Idempotent;
    /// both kernel-checked, `Constructive`, empty admitted-axiom closure.
    pub fn init_algebra_nnreal_finsum_split(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_finsum()?; // NNReal.finSum, finSum_succ, finSum_zero
        self.init_algebra_nnreal_finsum_add()?; // NNReal.finSum_congr / finSum_add
        self.init_algebra_nnreal_semiring_units()?; // NNReal.add_zero (+ mul_one)
        self.init_algebra_nnreal_add_comm_assoc()?; // NNReal.add_assoc
        self.init_fin_sum()?; // Fin.last / Fin.castSucc / Fin.val
        self.register_fin_split_index()?; // Fin.castAdd / Fin.addNat
        self.register_fin_dec_eq_proof()?; // Fin.eq_of_val_eq
        self.init_eq()?;

        let c = C::new();
        self.register_nnreal_finsum_cast(&c)?;
        self.register_nnreal_finsum_split_add(&c)?;
        Ok(())
    }

    fn register_nnreal_finsum_cast(&mut self, c: &C) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.finSum_cast");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_finsum_cast(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    fn register_nnreal_finsum_split_add(&mut self, c: &C) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.finSum_split_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_split_type(c);
        let value = build_split_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `NNReal.finSum_cast` type + proof (clean `Eq.rec` on the bound equality).
fn build_finsum_cast(c: &C) -> (Expr, Expr) {
    // cast_fin b a i e := @Eq.ndrec Nat b (fun m => Fin m) i a e : Fin a.
    let cast_fin = |parent: &EnvDeclBuilder, b: &Expr, a: &Expr, i: &Expr, e: &Expr| -> Expr {
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (m_id, m) = mb.fresh_local(c.nat.clone());
            let body = c.fin_n(&m);
            mb.finish_child(mb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body))
        };
        Expr::apps(
            c.eq_ndrec_fin.clone(),
            [
                c.nat.clone(),
                b.clone(),
                motive,
                i.clone(),
                a.clone(),
                e.clone(),
            ],
        )
    };
    let summand_rhs = |parent: &EnvDeclBuilder, a: &Expr, b: &Expr, e: &Expr, f: &Expr| -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let (i_id, i) = sb.fresh_local(c.fin_n(b));
        let casted = cast_fin(&sb, b, a, &i, e);
        let body = Expr::app(f.clone(), casted);
        sb.finish_child(sb.mk_lam(i_id, BinderInfo::Default, c.fin_n(b), body))
    };
    let concl = |parent: &EnvDeclBuilder, a: &Expr, b: &Expr, e: &Expr, f: &Expr| -> Expr {
        let lhs = c.sum(a, f);
        let rhs = c.sum(b, &summand_rhs(parent, a, b, e, f));
        c.eq_nn(&lhs, &rhs)
    };

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let e_ty = c.eq_nat_(&bb, &a);
        let (e_id, e) = b.fresh_local(e_ty.clone());
        let f_ty = c.fin_to_nnreal(&a);
        let (f_id, f) = b.fresh_local(f_ty.clone());
        let body = concl(&b, &a, &bb, &e, &f);
        let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, body);
        let r = b.mk_pi(e_id, BinderInfo::Default, e_ty, r);
        let r = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), r))
    };

    // value: fun a b e => @Eq.rec Nat b motive base a e, where
    //   motive a' e' := ∀ F : Fin a' → NNReal, concl a' b e' F;
    //   base F := @Eq.refl NNReal (finSum b F)  (at a=b, e=rfl, cast ≡ id).
    let value = {
        let mut vb = EnvDeclBuilder::new();
        let (a_id, a) = vb.fresh_local(c.nat.clone());
        let (bb_id, bb) = vb.fresh_local(c.nat.clone());
        let e_ty = c.eq_nat_(&bb, &a);
        let (e_id, e) = vb.fresh_local(e_ty.clone());

        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&vb);
            let (ap_id, ap) = mb.fresh_local(c.nat.clone());
            let ep_ty = c.eq_nat_(&bb, &ap);
            let (ep_id, ep) = mb.fresh_local(ep_ty.clone());
            let f_ty = c.fin_to_nnreal(&ap);
            let (f_id, f) = mb.fresh_local(f_ty.clone());
            let body = concl(&mb, &ap, &bb, &ep, &f);
            let pi = mb.mk_pi(f_id, BinderInfo::Default, f_ty, body);
            let lam = mb.mk_lam(ep_id, BinderInfo::Default, ep_ty, pi);
            mb.finish_child(mb.mk_lam(ap_id, BinderInfo::Default, c.nat.clone(), lam))
        };
        let base = {
            let mut bb_b = EnvDeclBuilder::child_of(&vb);
            let f_ty = c.fin_to_nnreal(&bb);
            let (f_id, f) = bb_b.fresh_local(f_ty.clone());
            let sum_bf = c.sum(&bb, &f);
            let refl = Expr::apps(c.eq_refl1.clone(), [c.nnreal(), sum_bf]);
            bb_b.finish_child(bb_b.mk_lam(f_id, BinderInfo::Default, f_ty, refl))
        };
        let rec_app = Expr::apps(
            c.eq_rec01.clone(),
            [
                c.nat.clone(),
                bb.clone(),
                motive,
                base,
                a.clone(),
                e.clone(),
            ],
        );
        let lam = vb.mk_lam(e_id, BinderInfo::Default, e_ty, rec_app);
        let lam = vb.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), lam);
        vb.finish(vb.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), lam))
    };

    (type_, value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["NNReal.finSum_cast", "NNReal.finSum_split_add"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_finsum_split()
            .expect("init_algebra_nnreal_finsum_split");
        env.init_algebra_nnreal_finsum_split().expect("idempotent");
        env
    }

    #[test]
    fn test_finsum_split_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_finsum_split_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
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
