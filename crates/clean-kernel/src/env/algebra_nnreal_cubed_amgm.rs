// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — the **cubed 3-term AM-GM lifted to arbitrary `NNReal`**:
//! `27·(P²·Q) ≤ (2P+Q)³`, with the `27·`/`2·` coefficients in the SUBTRACTION-FREE
//! ADDITIVE forms (`27·X := X+X+…+X` 27-fold left-nested, `2P := P+P`) the
//! sqrt-free dual `(4/3,4)` cube-Minkowski MERGE consumes.
//!
//! # Why this module exists (the genuine analytic content, carried to NNReal)
//!
//! The MERGE's two split inequalities `3U₁²U₂ ≤ 2P+Q` close root-freely (design
//! `2026-06-20-hc43-dual-tensorization-cross-term.md`, §11) through the cubed
//! chain `(3U₁²U₂)³ = 27·U₁⁶U₂³ ≤ 27·P²Q ≤ (2P+Q)³`, whose terminal `≤` is the
//! cubed AM-GM `27·P²Q ≤ (2P+Q)³`. The SOS certificate
//! `(2P+Q)³ − 27P²Q = (P−Q)²(8P+Q) ≥ 0` lives in the rationals (it uses
//! subtraction, which subtraction-free `NNReal` lacks). So the genuine content is
//! the landed `Rat.cube_amgm_two_one`; this module carries it up to arbitrary
//! `NNReal` by the SAME pointwise `CauSeq` lift `algebra_nnreal_reverse_cube.rs`
//! uses — nested `Quot.ind`, NO `NNReal.ofRat` shortcut, valid for ALL `NNReal`.
//!
//! # The lemma (axiom-free, kernel-checked, GENUINE lift)
//!
//! ```text
//!   NNReal.cubed_amgm : ∀ P Q : NNReal,
//!     NNReal.le (add27 ((P·P)·Q)) (((P+P)+Q)·((P+P)+Q)·((P+P)+Q))
//! ```
//! where `add27 X = (((…((X+X)+X)…)+X)` is the left-nested 27-fold additive sum
//! and the cube is left-nested `(z·z)·z`.
//!
//! # Proof (two stages, both axiom-free)
//!
//! 1. A pure-`Rat` ADDITIVE restatement `Rat.cube_amgm_additive`:
//!    `∀ p q, 0≤p → 0≤q → Rat.le (add27 (p²q)) (((p+p)+q)³)`, derived from
//!    `Rat.cube_amgm_two_one` by transporting its multiplicative numerals
//!    (`27num · X`, `2num · p`) onto the additive forms via two `Rat`
//!    distributivity bridges `E1 : Rat.mul 27num X = add27 X` (27-fold
//!    `right_distrib`+`one_mul`) and `E2 : Rat.mul 2num p = p+p`
//!    (`right_distrib`+`one_mul` twice), then `Eq.subst` on the LHS (along `E1`)
//!    and on the cube base (along the `congrArg`-lifted `E2`).
//! 2. The pointwise `CauSeq` lift: `add` / `mul` push through `Rat.add` /
//!    `Rat.mul` on the `.val` component by `Eq.refl` (the `Subtype` projection),
//!    so at each rep index `n` the `NNReal.le` goal reduces DEFINITIONALLY to the
//!    `Rat` additive inequality at `(vP n, vQ n)`, with `0 ≤ vP n`, `0 ≤ vQ n`
//!    from `NNRat.property`. The `CauSeq.le` `∀ε>0 ∃N ∀n≥N, vL n < vR n + ε`
//!    obligation is met pointwise: `vL n ≤ vR n` (the `Rat` lemma) and
//!    `vR n < vR n + ε` (`add_lt_add_left` + `add_zero`), chained by
//!    `Rat.lt_of_le_of_lt`. `NNReal.cubed_amgm` is the nested `Quot.ind`² of the
//!    `CauSeq` core.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`. NO new axiom: the AM-GM is `Rat.cube_amgm_two_one`'s
//! SOS, the lift is a genuine `CauSeq` argument. FORBIDDEN here: `Rat.dist`,
//! `Real`, `Real.sqrt`, `NNReal.sqrt`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// The number of additive copies in `27·X` (the AM-GM constant).
const AMGM_COEFF: u32 = 27;

/// Pre-resolved handles + smart-constructors for the cubed-AM-GM lift.
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
struct CubedAmGmConsts {
    nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_lt: Expr,
    rat_le: Expr,
    nat_le: Expr,
    nnrat_val: Expr,
    nnrat_property: Expr,
    causeq: Expr,
    causeq_seq: Expr,
    causeq_equiv: Expr,
    causeq_le: Expr,
    causeq_add: Expr,
    causeq_mul: Expr,
    // Rat lemmas.
    rat_one_mul: Expr,
    rat_right_distrib: Expr,
    rat_add_zero: Expr,
    rat_add_lt_add_left: Expr,
    rat_lt_of_le_of_lt: Expr,
    cube_amgm_two_one: Expr,
    // Logic / Eq / Quot.
    #[cfg(test)]
    exists_c: Expr,
    exists_intro: Expr,
    #[cfg(test)]
    eq_rat: Expr,
    eq_trans: Expr,
    #[cfg(test)]
    eq_symm: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
    quot_mk: Expr,
    quot_ind: Expr,
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
impl CubedAmGmConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_lt: k("Rat.lt"),
            rat_le: k("Rat.le"),
            nat_le: k("Nat.le"),
            nnrat_val: k("NNRat.val"),
            nnrat_property: k("NNRat.property"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            causeq_le: k("NNReal.CauSeq.le"),
            causeq_add: k("NNReal.CauSeq.add"),
            causeq_mul: k("NNReal.CauSeq.mul"),
            rat_one_mul: k("Rat.one_mul"),
            rat_right_distrib: k("Rat.right_distrib"),
            rat_add_zero: k("Rat.add_zero"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_lt_of_le_of_lt: k("Rat.lt_of_le_of_lt"),
            cube_amgm_two_one: k("Rat.cube_amgm_two_one"),
            #[cfg(test)]
            exists_c: Expr::const_(Name::from_string("Exists"), vec![l1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1.clone()]),
            #[cfg(test)]
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            #[cfg(test)]
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![l1.clone()]),
            quot_ind: Expr::const_(Name::from_string("Quot.ind"), vec![l1]),
        }
    }

    // ── Rat carrier constructors ──
    fn radd(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a.clone(), b.clone()])
    }
    fn rmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a.clone(), b.clone()])
    }
    fn rlt(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a.clone(), b.clone()])
    }
    fn rle(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a.clone(), b.clone()])
    }
    fn nonneg(&self, a: &Expr) -> Expr {
        self.rle(&self.rat_zero, a)
    }
    /// `(a·a)·a` (left-nested cube).
    fn rcube(&self, a: &Expr) -> Expr {
        self.rmul(&self.rmul(a, a), a)
    }
    /// `(p·p)·q` (left-nested `p²q`).
    fn rsq_t(&self, p: &Expr, q: &Expr) -> Expr {
        self.rmul(&self.rmul(p, p), q)
    }
    /// The left-nested `n`-fold additive sum `(((y+y)+y)…)+y` (`n ≥ 1`).
    fn radd_n(&self, y: &Expr, n: u32) -> Expr {
        debug_assert!(n >= 1);
        let mut acc = y.clone();
        for _ in 1..n {
            acc = self.radd(&acc, y);
        }
        acc
    }
    /// The left-nested numeral `n` as a sum of `Rat.one` (`n ≥ 1`).
    fn rnumeral(&self, n: u32) -> Expr {
        debug_assert!(n >= 1);
        let mut acc = self.rat_one.clone();
        for _ in 1..n {
            acc = self.radd(&acc, &self.rat_one);
        }
        acc
    }

    // ── Rat lemma applications ──
    /// `Rat.one_mul a : Rat.mul Rat.one a = a`.
    fn one_mul(&self, a: &Expr) -> Expr {
        Expr::app(self.rat_one_mul.clone(), a.clone())
    }
    /// `Rat.right_distrib a b c : Rat.mul (a+b) c = (a·c) + (b·c)`.
    fn right_distrib(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        Expr::apps(
            self.rat_right_distrib.clone(),
            [a.clone(), b.clone(), cc.clone()],
        )
    }
    /// `Rat.add_zero a : Rat.add a Rat.zero = a`.
    fn add_zero(&self, a: &Expr) -> Expr {
        Expr::app(self.rat_add_zero.clone(), a.clone())
    }
    /// `Rat.add_lt_add_left a b c (a<b) : Rat.lt (c+a) (c+b)`.
    fn add_lt_add_left(&self, a: &Expr, b: &Expr, cc: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.rat_add_lt_add_left.clone(),
            [a.clone(), b.clone(), cc.clone(), h],
        )
    }
    /// `Rat.lt_of_le_of_lt a b c (a≤b)(b<c) : Rat.lt a c`.
    fn lt_of_le_of_lt(&self, a: &Expr, b: &Expr, cc: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.rat_lt_of_le_of_lt.clone(),
            [a.clone(), b.clone(), cc.clone(), h1, h2],
        )
    }

    // ── Eq toolkit (over Rat) ──
    fn eq_trans(&self, a: &Expr, b: &Expr, cc: &Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.rat.clone(), a.clone(), b.clone(), cc.clone(), hab, hbc],
        )
    }
    #[cfg(test)]
    fn eq_symm(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_symm.clone(),
            [self.rat.clone(), a.clone(), b.clone(), h],
        )
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b`.
    fn subst(&self, motive: Expr, a: &Expr, b: &Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a.clone(), b.clone(), h_eq, h],
        )
    }
    /// `@congrArg Rat Rat a a2 f h : f a = f a2`.
    fn congr_arg(&self, a: &Expr, a2: &Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [
                self.rat.clone(),
                self.rat.clone(),
                a.clone(),
                a2.clone(),
                f,
                h,
            ],
        )
    }

    // ── CauSeq surface ──
    fn vseq(&self, x: &Expr, n: &Expr) -> Expr {
        let seq = Expr::app(Expr::app(self.causeq_seq.clone(), x.clone()), n.clone());
        Expr::app(self.nnrat_val.clone(), seq)
    }
    fn property_seq(&self, x: &Expr, n: &Expr) -> Expr {
        let seq = Expr::app(Expr::app(self.causeq_seq.clone(), x.clone()), n.clone());
        Expr::app(self.nnrat_property.clone(), seq)
    }
    fn causeq_le(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.causeq_le.clone(), [a.clone(), b.clone()])
    }
    fn cau_add(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.causeq_add.clone(), [a.clone(), b.clone()])
    }
    fn cau_mul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.causeq_mul.clone(), [a.clone(), b.clone()])
    }
    fn nat_le(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a.clone(), b.clone()])
    }
    #[cfg(test)]
    fn nnreal(&self) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Quot"), vec![Level::succ(Level::zero())]),
            [self.causeq.clone(), self.causeq_equiv.clone()],
        )
    }
    fn quot_mk(&self, l: Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), l],
        )
    }
}

/// Pre-resolved NNReal carrier handles for the final `NNReal.cubed_amgm` statement.
struct NNConsts {
    nnreal: Expr,
    nnreal_add: Expr,
    nnreal_mul: Expr,
    nnreal_le: Expr,
}

impl NNConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nnreal: k("NNReal"),
            nnreal_add: k("NNReal.add"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_le: k("NNReal.le"),
        }
    }
    fn add(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [a.clone(), b.clone()])
    }
    fn mul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn le(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a.clone(), b.clone()])
    }
    fn cube(&self, a: &Expr) -> Expr {
        self.mul(&self.mul(a, a), a)
    }
    fn sq_t(&self, p: &Expr, q: &Expr) -> Expr {
        self.mul(&self.mul(p, p), q)
    }
    /// `(((P+P)+Q)` — the `2P+Q` additive split base.
    fn two_plus(&self, p: &Expr, q: &Expr) -> Expr {
        self.add(&self.add(p, p), q)
    }
    /// The left-nested `n`-fold additive sum `(((X+X)+X)…)+X` (`n ≥ 1`).
    fn add_n(&self, x: &Expr, n: u32) -> Expr {
        debug_assert!(n >= 1);
        let mut acc = x.clone();
        for _ in 1..n {
            acc = self.add(&acc, x);
        }
        acc
    }
}

impl Environment {
    /// Register `Rat.cube_amgm_additive`, the `NNReal.CauSeq` core, and the
    /// `NNReal.cubed_amgm` lift. Idempotent; foundational-only closure.
    pub fn init_algebra_nnreal_cubed_amgm(&mut self) -> Result<(), EnvError> {
        // Rat SOS leaf + the numeral/order/distributivity surface its additive
        // restatement and the per-point lift cite.
        self.init_algebra_rat_cube_amgm()?; // Rat.cube_amgm_two_one
        self.init_rat_quotient_poc()?; // Rat.right_distrib, Rat.add_zero, Rat.add_le_add_left
        self.init_rat_field_inst()?; // Rat.one_mul (register_rat_q_structural)
        self.register_rat_add_lt_add_left()?; // Rat.add_lt_add_left
        self.init_boolean_analysis_order_toolkit_b1c()?; // Rat.lt_of_le_of_lt
                                                         // CauSeq carrier + the lift surface.
        self.init_algebra_nnreal_mul_lift()?; // NNReal.mul, CauSeq.mul, NNRat.*
        self.init_algebra_nnreal_add()?; // NNReal.add, CauSeq.add
        self.init_algebra_nnreal_le()?; // CauSeq.le, NNReal.le
        self.init_algebra_nnreal_nnrat()?; // NNRat.property/val
        self.init_eq()?;
        self.init_exists()?;

        let c = CubedAmGmConsts::new();
        let nn = NNConsts::new();
        self.register_rat_cube_amgm_additive(&c)?;
        self.register_causeq_cubed_amgm(&c)?;
        self.register_nnreal_cubed_amgm(&c, &nn)?;
        Ok(())
    }

    /// `Rat.cube_amgm_additive : ∀ p q, 0≤p → 0≤q →
    ///     Rat.le (add27 (p²q)) (((p+p)+q)·((p+p)+q)·((p+p)+q))`.
    fn register_rat_cube_amgm_additive(&mut self, c: &CubedAmGmConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.cube_amgm_additive");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.rat.clone());
            let (q_id, q) = b.fresh_local(c.rat.clone());
            let hp_ty = c.nonneg(&p);
            let (hp_id, _) = b.fresh_local(hp_ty.clone());
            let hq_ty = c.nonneg(&q);
            let (hq_id, _) = b.fresh_local(hq_ty.clone());
            let lhs = c.radd_n(&c.rsq_t(&p, &q), AMGM_COEFF);
            let base = c.radd(&c.radd(&p, &p), &q);
            let concl = c.rle(&lhs, &c.rcube(&base));
            let e = b.mk_pi(hq_id, BinderInfo::Default, hq_ty, concl);
            let e = b.mk_pi(hp_id, BinderInfo::Default, hp_ty, e);
            let e = b.mk_pi(q_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_rat_cube_amgm_additive(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.CauSeq.cubed_amgm : ∀ f g,
    ///     CauSeq.le (add27 ((f·f)·g)) (((f+f)+g)·((f+f)+g)·((f+f)+g))`.
    fn register_causeq_cubed_amgm(&mut self, c: &CubedAmGmConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.CauSeq.cubed_amgm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.causeq.clone());
            let (g_id, g) = b.fresh_local(c.causeq.clone());
            let lhs = cau_add_n(c, &cau_sq_t(c, &f, &g), AMGM_COEFF);
            let base = c.cau_add(&c.cau_add(&f, &f), &g);
            let rhs = cau_cube(c, &base);
            let concl = c.causeq_le(&lhs, &rhs);
            let e = b.mk_pi(g_id, BinderInfo::Default, c.causeq.clone(), concl);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.causeq.clone(), e);
            b.finish(e)
        };
        let value = build_causeq_cubed_amgm(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.cubed_amgm : ∀ P Q, NNReal.le (add27 (P²Q)) (((P+P)+Q)³)`.
    fn register_nnreal_cubed_amgm(
        &mut self,
        c: &CubedAmGmConsts,
        nn: &NNConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.cubed_amgm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(nn.nnreal.clone());
            let (q_id, q) = b.fresh_local(nn.nnreal.clone());
            let lhs = nn.add_n(&nn.sq_t(&p, &q), AMGM_COEFF);
            let rhs = nn.cube(&nn.two_plus(&p, &q));
            let concl = nn.le(&lhs, &rhs);
            let e = b.mk_pi(q_id, BinderInfo::Default, nn.nnreal.clone(), concl);
            let e = b.mk_pi(p_id, BinderInfo::Default, nn.nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_nnreal_cubed_amgm(c, nn);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

// ── CauSeq form helpers (mirror the carrier helpers on the CauSeq side) ──

/// `(f·f)·g` as a `CauSeq`.
fn cau_sq_t(c: &CubedAmGmConsts, f: &Expr, g: &Expr) -> Expr {
    c.cau_mul(&c.cau_mul(f, f), g)
}
/// `(z·z)·z` as a `CauSeq`.
fn cau_cube(c: &CubedAmGmConsts, z: &Expr) -> Expr {
    c.cau_mul(&c.cau_mul(z, z), z)
}
/// The left-nested `n`-fold `CauSeq.add` sum (`n ≥ 1`).
fn cau_add_n(c: &CubedAmGmConsts, x: &Expr, n: u32) -> Expr {
    debug_assert!(n >= 1);
    let mut acc = x.clone();
    for _ in 1..n {
        acc = c.cau_add(&acc, x);
    }
    acc
}

include!("algebra_nnreal_cubed_amgm_proof.rs");

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "Rat.cube_amgm_additive",
        "NNReal.CauSeq.cubed_amgm",
        "NNReal.cubed_amgm",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_cubed_amgm()
            .expect("init_algebra_nnreal_cubed_amgm");
        env.init_algebra_nnreal_cubed_amgm().expect("idempotent");
        env
    }

    #[test]
    fn test_cubed_amgm_kernel_check() {
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
    fn test_cubed_amgm_constructive_empty_closure() {
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
