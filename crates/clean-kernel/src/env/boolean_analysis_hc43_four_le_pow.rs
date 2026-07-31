// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual `(4/3,4)` campaign — the trivial constant premise (C) of the §11.1
//! `H_CLOSE` discharge: `4 ≤ 4^{m+1}` lifted to `NNReal`.
//!
//! `BoolAnalysis.finSum_two_point_close` (the §11.1 algebraic skeleton) consumes
//! a minor premise `h_const : NNReal.le c4 cN` where, at the `H_CLOSE` instance,
//! `c4 := NNReal.ofRat 4 h4` (the `n=1` dual-HC constant) and
//! `cN := NNReal.ofRat (4^{m+1}) h4n` (the `4^{m+1}` tensorization scalar). This
//! module discharges that premise GENUINELY (no axiom, no hypothesis on the
//! inequality itself):
//!
//! ```text
//! BoolAnalysis.four_le_four_pow_succ :
//!   ∀ (m : Nat) (h4 : Rat.le Rat.zero 4) (h4n : Rat.le Rat.zero (4^{m+1})),
//!     NNReal.le (NNReal.ofRat 4 h4) (NNReal.ofRat (Rat.powNat 4 (m+1)) h4n)
//! ```
//!
//! where `4 := Rat.mk (Int.ofNat 4) 1` (byte-for-byte `Hc43Consts.four_rat()`,
//! defeq `Rat.ofNat 4`). The two nonneg witnesses are taken as hypotheses because
//! `NNReal.ofRat`'s value carries them dependently — they are exactly the `h4` /
//! `h4n` already threaded through the `H_CLOSE` telescope; the INEQUALITY itself
//! is proven, not assumed.
//!
//! # Proof (axiom-free, root-free)
//!
//! 1. `BoolAnalysis.rat_one_le_pow_four : ∀ (m : Nat), Rat.le 1 (Rat.powNat 4 m)`
//!    by `Nat.rec`: base `1 ≤ 4^0 = 1` (`powNat_zero` + `le_refl`); step
//!    `1 ≤ 4^k → 1 ≤ 4^{k+1} = 4·4^k` via `4 = 4·1 ≤ 4·4^k`
//!    (`mul_le_mul_of_nonneg_left`) and `1 ≤ 4 ≤ 4·4^k` (`le_trans`).
//! 2. `Rat.le 4 (4^{m+1})`: `4^{m+1} = 4·4^k` (`powNat_succ`), `4 = 4·1 ≤ 4·4^k`.
//! 3. Lift via `NNReal.ofRat_le_ofRat 4 (4^{m+1}) h4 h4n <step 2>`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural` / `Declaration::Axiom`. FORBIDDEN here: `Rat.dist`,
//! `Real` / `Real.sqrt`, `NNReal.sqrt`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the (C) constant lemmas.
struct FourPowConsts {
    nat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_le: Expr,
    pow_nat: Expr,
    #[cfg(test)]
    nnreal: Expr,
    l1: Level,
    // proof leaves
    le_refl: Expr,
    le_trans: Expr,
    mul_le_left: Expr, // Rat.mul_le_mul_of_nonneg_left
    mul_one: Expr,
    pow_zero: Expr,
    pow_succ: Expr,
    nat_rec: Expr,
    of_rat: Expr,
    ofrat_le_ofrat: Expr,
}

impl FourPowConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let l1 = Level::succ(Level::zero());
        Self {
            nat: k("Nat"),
            nat_succ: k("Nat.succ"),
            nat_zero: k("Nat.zero"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_le: k("Rat.le"),
            pow_nat: k("Rat.powNat"),
            #[cfg(test)]
            nnreal: k("NNReal"),
            l1: l1.clone(),
            le_refl: k("Rat.le_refl"),
            le_trans: k("Rat.le_trans"),
            mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            mul_one: k("Rat.mul_one"),
            pow_zero: k("Rat.powNat_zero"),
            pow_succ: k("Rat.powNat_succ"),
            // The `1 ≤ 4^m` motive is `Prop`-valued, so `Nat.rec.{0}`.
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            of_rat: k("NNReal.ofRat"),
            ofrat_le_ofrat: k("NNReal.ofRat_le_ofRat"),
        }
    }

    /// `4 := Rat.mk (Int.ofNat 4) 1` — byte-for-byte `Hc43Consts.four_rat()`.
    fn four(&self) -> Expr {
        let rat_mk = Expr::const_(Name::from_string("Rat.mk"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let nat_one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        // 4 = succ^4 0
        let mut four = self.nat_zero.clone();
        for _ in 0..4 {
            four = Expr::app(self.nat_succ.clone(), four);
        }
        Expr::apps(rat_mk, [Expr::app(int_of_nat, four), nat_one])
    }

    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn mul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a.clone(), b.clone()])
    }
    fn le(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a.clone(), b.clone()])
    }
    fn pow(&self, b: &Expr, n: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [b.clone(), n.clone()])
    }
    /// `Rat.le_refl a : a ≤ a`.
    fn le_refl(&self, a: &Expr) -> Expr {
        Expr::app(self.le_refl.clone(), a.clone())
    }
    /// `Rat.le_trans a b c hab hbc : a ≤ c`.
    fn le_trans(&self, a: &Expr, b: &Expr, cc: &Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.le_trans.clone(),
            [a.clone(), b.clone(), cc.clone(), hab, hbc],
        )
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c h_bc h_a : a·b ≤ a·c`.
    fn mul_le_left(&self, a: &Expr, b: &Expr, cc: &Expr, h_bc: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            self.mul_le_left.clone(),
            [a.clone(), b.clone(), cc.clone(), h_bc, h_a],
        )
    }
    /// `Rat.mul_one a : a·1 = a`.
    fn mul_one(&self, a: &Expr) -> Expr {
        Expr::app(self.mul_one.clone(), a.clone())
    }
    /// `Rat.powNat_zero b : b^0 = 1`.
    fn pow_zero(&self, b: &Expr) -> Expr {
        Expr::app(self.pow_zero.clone(), b.clone())
    }
    /// `Rat.powNat_succ b e : b^(e+1) = b·b^e`.
    fn pow_succ(&self, b: &Expr, e: &Expr) -> Expr {
        Expr::apps(self.pow_succ.clone(), [b.clone(), e.clone()])
    }
    #[cfg(test)]
    fn eq_rat(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.rat.clone(), a.clone(), b.clone()],
        )
    }
    fn symm_rat(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.rat.clone(), a.clone(), b.clone(), h],
        )
    }
    /// `subst` with motive `fun x => l ≤ x` along `h_eq : from = to`, given
    /// `h : l ≤ from`, producing `l ≤ to`.
    fn subst_le_right(
        &self,
        parent: &EnvDeclBuilder,
        l: &Expr,
        from: &Expr,
        to: &Expr,
        h_eq: Expr,
        h: Expr,
    ) -> Expr {
        let motive = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = d.fresh_local(self.rat.clone());
            let body = self.le(l, &x);
            d.finish_child(d.mk_lam(x_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.l1.clone()]),
            [self.rat.clone(), motive, from.clone(), to.clone(), h_eq, h],
        )
    }
}

impl Environment {
    /// Register `BoolAnalysis.rat_one_le_pow_four` and
    /// `BoolAnalysis.four_le_four_pow_succ` (premise (C) of §11.1). Idempotent;
    /// both kernel-checked, `Constructive`, empty admitted-axiom closure.
    pub fn init_boolean_analysis_hc43_four_le_pow(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_le()?; // Nat.le.refl / Nat.le.step
        self.register_rat_pow_nat()?; // Rat.powNat
        self.register_rat_pow_nat_zero_theorem()?; // Rat.powNat_zero
        self.register_rat_pow_nat_succ_theorem()?; // Rat.powNat_succ
        self.register_rat_pow_nat_mul_base()?; // Rat.mul_le_mul_of_nonneg_left (via order proofs)
        self.init_algebra_rat_archimedean()?; // Rat.ofNat, Rat.ofNat_le_ofNat_of_le
        self.init_algebra_nnreal_le()?; // NNReal.ofRat_le_ofRat
                                        // Rat.le_refl / Rat.le_trans / Rat.mul_one come from the order surface
                                        // pulled in by the powNat-mul-base / nnreal-le inits above; ensure them.
        self.register_rat_order_proofs()?; // Rat.le_refl, Rat.le_trans, mul_le_mul_of_nonneg_*
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?; // Rat.mul_one
        }

        let c = FourPowConsts::new();
        self.register_rat_one_le_pow_four(&c)?;
        self.register_four_le_four_pow_succ(&c)?;
        Ok(())
    }

    /// `BoolAnalysis.rat_one_le_pow_four : ∀ (m : Nat), Rat.le 1 (Rat.powNat 4 m)`.
    fn register_rat_one_le_pow_four(&mut self, c: &FourPowConsts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.rat_one_le_pow_four");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_one_le_pow_four(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.four_le_four_pow_succ` — premise (C). See module docs.
    fn register_four_le_four_pow_succ(&mut self, c: &FourPowConsts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.four_le_four_pow_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_four_le_four_pow_succ(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `BoolAnalysis.rat_one_le_pow_four` type + proof: `1 ≤ 4^m` by `Nat.rec`.
fn build_one_le_pow_four(c: &FourPowConsts) -> (Expr, Expr) {
    let four = c.four();
    let one = c.rat_one.clone();

    // Type: ∀ (m : Nat), Rat.le 1 (Rat.powNat 4 m).
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(c.nat.clone());
        let concl = c.le(&one, &c.pow(&four, &m));
        b.finish(b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), concl))
    };

    // Value: Nat.rec motive base step.
    let value = {
        let mut b = EnvDeclBuilder::new();

        // motive : fun (k : Nat) => Rat.le 1 (Rat.powNat 4 k).
        let motive = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = d.fresh_local(c.nat.clone());
            let body = c.le(&one, &c.pow(&four, &k));
            d.finish_child(d.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
        };

        // base : Rat.le 1 (Rat.powNat 4 0).
        //   4^0 = 1 (powNat_zero); 1 ≤ 1 (le_refl); subst to RHS = 4^0.
        let base = {
            let pow0 = c.pow(&four, &c.nat_zero);
            // pz : 4^0 = 1.
            let pz = c.pow_zero(&four);
            // le_refl 1 : 1 ≤ 1; subst RHS along (1 = 4^0) = symm pz.
            let one_le_one = c.le_refl(&one);
            c.subst_le_right(
                &b,
                &one,
                &one,
                &pow0,
                c.symm_rat(&pow0, &one, pz),
                one_le_one,
            )
        };

        // step : fun (k : Nat) (ih : 1 ≤ 4^k) => <1 ≤ 4^(k+1)>.
        let step = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = d.fresh_local(c.nat.clone());
            let ih_ty = c.le(&one, &c.pow(&four, &k));
            let (ih_id, ih) = d.fresh_local(ih_ty.clone());

            let pow_k = c.pow(&four, &k);
            let pow_sk = c.pow(&four, &c.succ(&k));
            let four_pow_k = c.mul(&four, &pow_k); // 4·4^k
            let four_one = c.mul(&four, &one); // 4·1

            // `mul_le_mul_of_nonneg_left` needs `h_a : 0 ≤ 4`; `1 ≤ 4` feeds the
            // final `le_trans`. Both are numeral facts via `ofNat_le_ofNat_of_le`.
            let zero_le_four = build_zero_le_four(c, &d);
            let one_le_four = build_one_le_four(c, &d);

            // 4·1 ≤ 4·4^k  (mul_le_mul_of_nonneg_left 4 1 (4^k) ih (0≤4)).
            let mul_step = c.mul_le_left(&four, &one, &pow_k, ih.clone(), zero_le_four);
            // 4 = 4·1  (symm (mul_one 4)); rewrite LHS 4·1 → 4 via subst on the LEFT
            // of `≤`. We want `1 ≤ 4·4^k`. Build `1 ≤ 4` then `4 ≤ 4·4^k` then trans.
            // 4 ≤ 4·1  along (4·1 = 4) = mul_one 4: from `4 ≤ 4` (le_refl) subst LEFT.
            // Easier: 4·1 = 4 (mul_one); so 4 ≤ 4·4^k via subst LEFT of mul_step along mul_one.
            let four_eq = c.mul_one(&four); // 4·1 = 4
                                            // subst LEFT: from `4·1 ≤ 4·4^k` to `4 ≤ 4·4^k`.
            let four_le_mul = {
                let motive = {
                    let mut md = EnvDeclBuilder::child_of(&d);
                    let (x_id, x) = md.fresh_local(c.rat.clone());
                    let body = c.le(&x, &four_pow_k);
                    md.finish_child(md.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body))
                };
                Expr::apps(
                    Expr::const_(Name::from_string("Eq.subst"), vec![c.l1.clone()]),
                    [
                        c.rat.clone(),
                        motive,
                        four_one.clone(),
                        four.clone(),
                        four_eq,
                        mul_step,
                    ],
                )
            };
            // 1 ≤ 4·4^k  via le_trans 1 4 (4·4^k) (1≤4)(4 ≤ 4·4^k).
            let one_le_mul = c.le_trans(&one, &four, &four_pow_k, one_le_four, four_le_mul);
            // 4·4^k = 4^(k+1)  (symm (powNat_succ 4 k)); rewrite RHS to 4^(k+1).
            let psucc = c.pow_succ(&four, &k); // 4^(k+1) = 4·4^k
            let goal = c.subst_le_right(
                &d,
                &one,
                &four_pow_k,
                &pow_sk,
                c.symm_rat(&pow_sk, &four_pow_k, psucc),
                one_le_mul,
            );
            let r = d.mk_lam(ih_id, BinderInfo::Default, ih_ty, goal);
            d.finish_child(d.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), r))
        };

        let rec = Expr::apps(c.nat_rec.clone(), [motive, base, step]);
        // Nat.rec motive base step : ∀ m, motive m. Eta as fun m => rec m.
        let (m_id, m) = b.fresh_local(c.nat.clone());
        let body = Expr::app(rec, m);
        b.finish(b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body))
    };

    (ty, value)
}

/// `0 ≤ 4` (`Rat.le Rat.zero (Rat.mk (Int.ofNat 4) 1)`) — the constructive
/// `four_rat` nonneg witness, exposed so `hc43_core_step_v2` can build the `c4 :=
/// ofRat 4 h4` it shares with premise (C) WITHOUT taking `h4` as a hypothesis.
/// Same term as `build_zero_le_four` (defeq `ofNat 0`/`ofNat 4`).
pub(super) fn four_rat_zero_le() -> Expr {
    let c = FourPowConsts::new();
    let b = EnvDeclBuilder::new();
    build_zero_le_four(&c, &b)
}

/// `0 ≤ 4` via `Rat.ofNat_le_ofNat_of_le 0 4 (Nat.le 0 4)` (defeq `4 = ofNat 4`,
/// `Rat.zero` defeq `ofNat 0`). The `Nat.le 0 4` is built constructor-only
/// (`Nat.le.refl 0` + four `Nat.le.step`s) to keep the closure self-contained.
fn build_zero_le_four(c: &FourPowConsts, _parent: &EnvDeclBuilder) -> Expr {
    let zero_le = Expr::const_(Name::from_string("Rat.ofNat_le_ofNat_of_le"), vec![]);
    let of_nat = |n: u64| {
        let mut e = c.nat_zero.clone();
        for _ in 0..n {
            e = Expr::app(c.nat_succ.clone(), e);
        }
        e
    };
    let nat0 = of_nat(0);
    let nat4 = of_nat(4);
    let h_nat = build_nat_le(c, 0, 4);
    // Rat.ofNat_le_ofNat_of_le 0 4 (Nat.le 0 4) : Rat.le (ofNat 0) (ofNat 4).
    // ofNat 0 = Rat.mk (Int.ofNat 0) 1; defeq Rat.zero; ofNat 4 defeq `four`.
    Expr::apps(zero_le, [nat0, nat4, h_nat])
}

/// `1 ≤ 4` via `Rat.ofNat_le_ofNat_of_le 1 4 (Nat.le 1 4)` (defeq `1 = ofNat 1`,
/// `4 = ofNat 4`).
fn build_one_le_four(c: &FourPowConsts, _parent: &EnvDeclBuilder) -> Expr {
    let le = Expr::const_(Name::from_string("Rat.ofNat_le_ofNat_of_le"), vec![]);
    let of_nat = |n: u64| {
        let mut e = c.nat_zero.clone();
        for _ in 0..n {
            e = Expr::app(c.nat_succ.clone(), e);
        }
        e
    };
    let nat1 = of_nat(1);
    let nat4 = of_nat(4);
    let h_nat = build_nat_le(c, 1, 4);
    Expr::apps(le, [nat1, nat4, h_nat])
}

/// `Nat.le base top` via `top-base` `Nat.le.step`s on `Nat.le.refl base`.
/// `Nat.le.step` has signature `{n m : Nat} → Nat.le n m → Nat.le n (succ m)`;
/// the kernel's raw application takes the implicit `{n m}` POSITIONALLY, so we
/// supply both indices explicitly before the proof.
fn build_nat_le(c: &FourPowConsts, base: u64, top: u64) -> Expr {
    debug_assert!(base <= top);
    let of_nat = |n: u64| {
        let mut e = c.nat_zero.clone();
        for _ in 0..n {
            e = Expr::app(c.nat_succ.clone(), e);
        }
        e
    };
    let nbase = of_nat(base);
    // Nat.le.refl base : Nat.le base base.
    let mut acc = Expr::app(
        Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
        nbase.clone(),
    );
    // For cur = base, base+1, …, top-1: Nat.le.step base cur (acc : base ≤ cur).
    for cur in base..top {
        acc = Expr::apps(
            Expr::const_(Name::from_string("Nat.le.step"), vec![]),
            [nbase.clone(), of_nat(cur), acc],
        );
    }
    acc
}

/// `BoolAnalysis.four_le_four_pow_succ` type + proof (premise (C)).
fn build_four_le_four_pow_succ(c: &FourPowConsts) -> (Expr, Expr) {
    let four = c.four();
    let nonneg = |x: &Expr| c.le(&c.rat_zero, x);

    // Build TYPE: ∀ m (h4 : 0 ≤ 4)(h4n : 0 ≤ 4^{m+1}),
    //   NNReal.le (ofRat 4 h4)(ofRat (4^{m+1}) h4n).
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(c.nat.clone());
        let sm = c.succ(&m);
        let pow_sm = c.pow(&four, &sm);
        let h4_ty = nonneg(&four);
        let (h4_id, h4) = b.fresh_local(h4_ty.clone());
        let h4n_ty = nonneg(&pow_sm);
        let (h4n_id, h4n) = b.fresh_local(h4n_ty.clone());
        let oa = Expr::apps(c.of_rat.clone(), [four.clone(), h4.clone()]);
        let ob = Expr::apps(c.of_rat.clone(), [pow_sm.clone(), h4n.clone()]);
        let concl = Expr::apps(
            Expr::const_(Name::from_string("NNReal.le"), vec![]),
            [oa, ob],
        );
        let e = b.mk_pi(h4n_id, BinderInfo::Default, h4n_ty, concl);
        let e = b.mk_pi(h4_id, BinderInfo::Default, h4_ty, e);
        b.finish(b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e))
    };

    // Build VALUE.
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(c.nat.clone());
        let sm = c.succ(&m);
        let pow_sm = c.pow(&four, &sm);
        let pow_m = c.pow(&four, &m);
        let four_pow_m = c.mul(&four, &pow_m); // 4·4^m
        let h4_ty = nonneg(&four);
        let (h4_id, h4) = b.fresh_local(h4_ty.clone());
        let h4n_ty = nonneg(&pow_sm);
        let (h4n_id, h4n) = b.fresh_local(h4n_ty.clone());

        // rat_step : Rat.le 4 (4^{m+1}).
        //   one_le_pow : 1 ≤ 4^m;  4·1 ≤ 4·4^m (mul_le_left);  4 ≤ 4·4^m;
        //   4·4^m = 4^{m+1} (symm powNat_succ): subst RHS.
        let one = c.rat_one.clone();
        let one_le_pow = Expr::app(
            Expr::const_(
                Name::from_string("BoolAnalysis.rat_one_le_pow_four"),
                vec![],
            ),
            m.clone(),
        );
        let zero_le_four = build_zero_le_four(c, &b);
        let mul_step = c.mul_le_left(&four, &one, &pow_m, one_le_pow, zero_le_four);
        let four_one = c.mul(&four, &one);
        let four_eq = c.mul_one(&four); // 4·1 = 4
                                        // subst LEFT: 4·1 ≤ 4·4^m  →  4 ≤ 4·4^m.
        let four_le_mul = {
            let motive = {
                let mut md = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = md.fresh_local(c.rat.clone());
                let body = c.le(&x, &four_pow_m);
                md.finish_child(md.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body))
            };
            Expr::apps(
                Expr::const_(Name::from_string("Eq.subst"), vec![c.l1.clone()]),
                [
                    c.rat.clone(),
                    motive,
                    four_one.clone(),
                    four.clone(),
                    four_eq,
                    mul_step,
                ],
            )
        };
        // 4 ≤ 4^{m+1}  via subst RHS along (4·4^m = 4^{m+1}) = symm(powNat_succ).
        let psucc = c.pow_succ(&four, &m); // 4^{m+1} = 4·4^m
        let rat_step = c.subst_le_right(
            &b,
            &four,
            &four_pow_m,
            &pow_sm,
            c.symm_rat(&pow_sm, &four_pow_m, psucc),
            four_le_mul,
        );

        // NNReal.ofRat_le_ofRat 4 (4^{m+1}) h4 h4n rat_step.
        let lifted = Expr::apps(
            c.ofrat_le_ofrat.clone(),
            [
                four.clone(),
                pow_sm.clone(),
                h4.clone(),
                h4n.clone(),
                rat_step,
            ],
        );

        let e = b.mk_lam(h4n_id, BinderInfo::Default, h4n_ty, lifted);
        let e = b.mk_lam(h4_id, BinderInfo::Default, h4_ty, e);
        b.finish(b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e))
    };

    (ty, value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "BoolAnalysis.rat_one_le_pow_four",
        "BoolAnalysis.four_le_four_pow_succ",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_hc43_four_le_pow()
            .expect("init_boolean_analysis_hc43_four_le_pow");
        env.init_boolean_analysis_hc43_four_le_pow()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_four_le_pow_kernel_check() {
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
    fn test_four_le_pow_constructive_empty_closure() {
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
