// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.mul_assoc : ∀ a b c : Int,
//!     Eq Int (Int.mul (Int.mul a b) c) (Int.mul a (Int.mul b c))`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_int_lemmas.rs` with a `Declaration::Theorem` built by a triple
//! nested `@Int.rec.{0}` case analysis (outer on `a`, then `b`, then `c`),
//! producing eight constructor leaves.
//!
//! # Sign-magnitude normalization
//!
//! Every `Int` constructor is, up to definitional equality, a signed
//! `Int.ofNat`:
//!
//! ```text
//! ofNat n   ≡ +(ofNat n)
//! negSucc n ≡ -(ofNat (Nat.succ n))      -- Int.neg (ofNat (succ n)) ι→ negSucc n
//! ```
//!
//! With each factor written `ε_i · ofNat m_i` (`ε_i ∈ {+, neg}`), both
//! `(a*b)*c` and `a*(b*c)` collapse — using only the constructive sign lemmas
//! `Int.neg_mul_left`, `Int.neg_mul_right`, `Int.neg_neg` and the definitional
//! `ofNat × ofNat ι→ ofNat (Nat.mul · ·)` — to the same net sign applied to a
//! `Nat`-magnitude product. The two magnitude products differ only in
//! association, so the residual goal is `Nat.mul_assoc m_a m_b m_c` lifted
//! through `Int.ofNat` (and the shared sign wrapper).
//!
//! Concretely, per leaf with magnitudes `A`, `B`, `C` (each a literal `Nat`
//! expr: `j`, `Nat.succ p`, `Nat.succ r`, …) and signs `(sa, sb, sc)`:
//!
//! ```text
//!   eqL : (a*b)*c        = sign (ofNat (Nat.mul (Nat.mul A B) C))
//!   core: congrArg (sign ∘ ofNat) (Nat.mul_assoc A B C)
//!       : sign (ofNat (Nat.mul (Nat.mul A B) C))
//!       = sign (ofNat (Nat.mul A (Nat.mul B C)))
//!   eqR : sign (ofNat (Nat.mul A (Nat.mul B C))) = a*(b*c)
//!   leaf = Eq.trans eqL (Eq.trans core eqR)
//! ```
//!
//! where `sign` is `Int.neg` when an odd number of `sa,sb,sc` are negative and
//! the identity otherwise.
//!
//! The signed-product equalities `ε_x (ofNat X) * ε_y (ofNat Y)
//! = (ε_x·ε_y) (ofNat (Nat.mul X Y))` are assembled by `signed_mul_eq`:
//!
//! ```text
//! (+X)*(+Y) = +(X*Y)                                   Eq.refl  (ι on Int.mul)
//! (-X)*(+Y) = -(X*Y)   symm (neg_mul_left  (ofNat X)(ofNat Y))
//! (+X)*(-Y) = -(X*Y)   symm (neg_mul_right (ofNat X)(ofNat Y))
//! (-X)*(-Y) = +(X*Y)   trans (symm (neg_mul_right (-(ofNat X)) (ofNat Y)))
//!                            (trans (neg_mul_left (ofNat X)(ofNat Y))
//!                                   (neg_neg (X*Y)))
//! ```
//!
//! # Axiom closure
//!
//! Mentions only kernel machinery / constructors / reducible Definitions and
//! the constructive `Declaration::Theorem`s `Int.neg_mul_left`,
//! `Int.neg_mul_right`, `Int.neg_neg`, `Nat.mul_assoc` (all #3604). None are
//! `Declaration::Axiom`, so `env.axiom_deps("Int.mul_assoc")` is empty and the
//! proof quality is `ProofQuality::Constructive`.
//!
//! Tracks #3604. Sibling: `algebra_int_left_distrib_proof.rs`,
//! `algebra_int_mul_comm_proof.rs`, `algebra_nat_mul_assoc_proof.rs`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Sign of a factor / product in the sign-magnitude normal form.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Sign {
    Pos,
    Neg,
}

impl Sign {
    fn mul(self, other: Sign) -> Sign {
        match (self, other) {
            (Sign::Pos, Sign::Pos) | (Sign::Neg, Sign::Neg) => Sign::Pos,
            _ => Sign::Neg,
        }
    }
}

/// Cached kernel constants reused across type and value construction.
struct IntMulAssocConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_succ: Expr,
    nat_mul: Expr,
    int_rec: Expr,
    int_mul: Expr,
    int_neg: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    eq_const: Expr,
    eq_refl: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
    nml: Expr,
    nmr: Expr,
    nn: Expr,
    nma: Expr,
}

impl IntMulAssocConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            int_rec: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_neg: Expr::const_(Name::from_string("Int.neg"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            nml: Expr::const_(Name::from_string("Int.neg_mul_left"), vec![]),
            nmr: Expr::const_(Name::from_string("Int.neg_mul_right"), vec![]),
            nn: Expr::const_(Name::from_string("Int.neg_neg"), vec![]),
            nma: Expr::const_(Name::from_string("Nat.mul_assoc"), vec![]),
        }
    }

    fn mul(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_mul.clone(), x), y)
    }

    fn neg(&self, x: Expr) -> Expr {
        Expr::app(self.int_neg.clone(), x)
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn nmul(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_mul.clone(), x), y)
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }

    fn refl_int(&self, t: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.int_type.clone(), t])
    }

    fn symm_int(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.int_type.clone(), a, b, h])
    }

    fn trans_int(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.int_type.clone(), x, y, z, h1, h2],
        )
    }

    /// `congrArg Int Int a1 a2 f h : Eq Int (f a1) (f a2)`.
    fn congr_arg_int(&self, a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.int_type.clone(), self.int_type.clone(), a1, a2, f, h],
        )
    }

    /// `congrArg Nat Int a1 a2 g h : Eq Int (g a1) (g a2)`.
    fn congr_arg_nat_int(&self, a1: Expr, a2: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.nat_type.clone(), self.int_type.clone(), a1, a2, g, h],
        )
    }

    fn eq_nat(&self, lhs: Expr, rhs: Expr) -> Expr {
        let type1 = Level::succ(Level::zero());
        let eqn = Expr::const_(Name::from_string("Eq"), vec![type1]);
        Expr::apps(eqn, [self.nat_type.clone(), lhs, rhs])
    }

    // ---- feeder lemma applications ----

    fn nml(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nml.clone(), [a, b])
    }

    fn nmr(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nmr.clone(), [a, b])
    }

    fn nn(&self, a: Expr) -> Expr {
        Expr::app(self.nn.clone(), a)
    }

    fn nma(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.nma.clone(), [a, b, cc])
    }

    /// `λ n : Nat => Int.ofNat n`.
    fn of_nat_fn(&self, parent: &EnvDeclBuilder) -> Expr {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (n_id, n) = fb.fresh_local(self.nat_type.clone());
        let body = self.of_nat(n);
        let lam = fb.mk_lam(n_id, BinderInfo::Default, self.nat_type.clone(), body);
        fb.finish_child(lam)
    }

    /// `λ n : Nat => Int.neg (Int.ofNat n)`.
    fn neg_of_nat_fn(&self, parent: &EnvDeclBuilder) -> Expr {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (n_id, n) = fb.fresh_local(self.nat_type.clone());
        let body = self.neg(self.of_nat(n));
        let lam = fb.mk_lam(n_id, BinderInfo::Default, self.nat_type.clone(), body);
        fb.finish_child(lam)
    }

    /// Apply the net `sign` to an `Int`: `Pos => x`, `Neg => Int.neg x`.
    fn apply_sign(&self, sign: Sign, x: Expr) -> Expr {
        match sign {
            Sign::Pos => x,
            Sign::Neg => self.neg(x),
        }
    }

    /// `λ n : Nat => sign (Int.ofNat n)` — the wrapper threaded through
    /// `congrArg` to lift `Nat.mul_assoc`.
    fn signed_of_nat_fn(&self, parent: &EnvDeclBuilder, sign: Sign) -> Expr {
        match sign {
            Sign::Pos => self.of_nat_fn(parent),
            Sign::Neg => self.neg_of_nat_fn(parent),
        }
    }

    /// Signed factor as an `Int` expression: `Pos => ofNat m`,
    /// `Neg => Int.neg (ofNat m)`.
    fn signed(&self, sign: Sign, m: Expr) -> Expr {
        self.apply_sign(sign, self.of_nat(m))
    }

    /// Build `Eq Int ((sx · ofNat X) * (sy · ofNat Y))
    ///               ((sx·sy) · ofNat (Nat.mul X Y))`.
    ///
    /// The left side is built from the literal factor expressions; the right
    /// side is the signed `Nat`-magnitude product. Pure sign algebra over
    /// `Int.neg_mul_left` / `Int.neg_mul_right` / `Int.neg_neg`.
    fn signed_mul_eq(&self, sx: Sign, x_mag: &Expr, sy: Sign, y_mag: &Expr) -> Expr {
        let of_x = self.of_nat(x_mag.clone());
        let of_y = self.of_nat(y_mag.clone());
        let pos_prod = self.of_nat(self.nmul(x_mag.clone(), y_mag.clone())); // ofNat (X*Y)
        match (sx, sy) {
            // (+X)*(+Y) = ofNat (X*Y): definitional (ι on Int.mul), Eq.refl.
            (Sign::Pos, Sign::Pos) => self.refl_int(self.mul(of_x, of_y)),
            // (-X)*(+Y) = -(X*Y): symm (neg_mul_left (ofNat X)(ofNat Y)).
            //   neg_mul_left (ofNat X)(ofNat Y)
            //     : Eq (-(ofNat X * ofNat Y)) ((-(ofNat X)) * ofNat Y)
            //     ≡ Eq (-(ofNat (X*Y)))       ((-(ofNat X)) * ofNat Y)
            (Sign::Neg, Sign::Pos) => {
                let lhs = self.mul(self.neg(of_x.clone()), of_y.clone());
                let rhs = self.neg(pos_prod);
                self.symm_int(rhs.clone(), lhs, self.nml(of_x, of_y))
            }
            // (+X)*(-Y) = -(X*Y): symm (neg_mul_right (ofNat X)(ofNat Y)).
            (Sign::Pos, Sign::Neg) => {
                let lhs = self.mul(of_x.clone(), self.neg(of_y.clone()));
                let rhs = self.neg(pos_prod);
                self.symm_int(rhs.clone(), lhs, self.nmr(of_x, of_y))
            }
            // (-X)*(-Y) = +(X*Y):
            //   e1 := symm (neg_mul_right (-(ofNat X)) (ofNat Y))
            //         : Eq ((-(ofNat X)) * (-(ofNat Y))) (-((-(ofNat X)) * ofNat Y))
            //   e2 := neg_mul_left (ofNat X)(ofNat Y)
            //         : Eq (-(ofNat X * ofNat Y)) ((-(ofNat X)) * ofNat Y)
            //   e2' := congrArg Int.neg e2
            //         : Eq (-(-(ofNat X * ofNat Y))) (-((-(ofNat X)) * ofNat Y))
            //   e3 := neg_neg (ofNat X * ofNat Y)
            //         : Eq (-(-(ofNat X * ofNat Y))) (ofNat X * ofNat Y)
            //   chain: ((-X)*(-Y)) = -((-X)*Y)        [e1]
            //                       = -(-(X*Y))        [symm e2']
            //                       = (X*Y) = ofNat(X*Y)[e3, ι]
            (Sign::Neg, Sign::Neg) => {
                let neg_x = self.neg(of_x.clone());
                let neg_y = self.neg(of_y.clone());
                let lhs = self.mul(neg_x.clone(), neg_y); // (-X)*(-Y)
                let nx_y = self.mul(neg_x, of_y.clone()); // (-X)*Y
                let neg_nx_y = self.neg(nx_y.clone()); // -((-X)*Y)
                let x_y = self.mul(of_x.clone(), of_y.clone()); // X*Y (≡ ofNat (X*Y))
                let neg_x_y = self.neg(x_y.clone()); // -(X*Y)
                let neg_neg_x_y = self.neg(neg_x_y.clone()); // -(-(X*Y))

                // e1 : Eq lhs neg_nx_y
                //   neg_mul_right (-(ofNat X)) (ofNat Y)
                //     : Eq (-((-(ofNat X)) * ofNat Y)) ((-(ofNat X)) * (-(ofNat Y)))
                //     = Eq neg_nx_y lhs;  symm flips to Eq lhs neg_nx_y.
                let neg_x_for_nmr = self.neg(of_x.clone());
                let e1 = self.symm_int(
                    neg_nx_y.clone(),
                    lhs.clone(),
                    self.nmr(neg_x_for_nmr, of_y.clone()),
                );
                // e2 : Eq neg_x_y nx_y   (neg_mul_left (ofNat X)(ofNat Y))
                let e2 = self.nml(of_x.clone(), of_y.clone());
                // e2' : Eq neg_neg_x_y neg_nx_y  (congrArg Int.neg e2)
                let neg_fn = {
                    let mut fb = EnvDeclBuilder::new();
                    let (z_id, z) = fb.fresh_local(self.int_type.clone());
                    let body = self.neg(z);
                    let lam = fb.mk_lam(z_id, BinderInfo::Default, self.int_type.clone(), body);
                    fb.finish(lam)
                };
                let e2_prime = self.congr_arg_int(neg_x_y.clone(), nx_y.clone(), neg_fn, e2);
                // symm e2' : Eq neg_nx_y neg_neg_x_y
                let symm_e2_prime = self.symm_int(neg_neg_x_y.clone(), neg_nx_y.clone(), e2_prime);
                // e3 : Eq neg_neg_x_y x_y   (neg_neg (X*Y))
                let e3 = self.nn(x_y.clone());
                // chain: lhs --e1--> neg_nx_y --symm_e2'--> neg_neg_x_y --e3--> x_y
                let t1 = self.trans_int(
                    lhs.clone(),
                    neg_nx_y.clone(),
                    neg_neg_x_y.clone(),
                    e1,
                    symm_e2_prime,
                );
                self.trans_int(lhs, neg_neg_x_y, x_y, t1, e3)
            }
        }
    }

    /// Full leaf proof for a fixed sign pattern `(sa, sb, sc)` and magnitudes
    /// `A`, `B`, `C`:
    /// `Eq Int (Int.mul (Int.mul a b) c) (Int.mul a (Int.mul b c))`
    /// where `a = signed(sa, A)`, etc.
    fn leaf(
        &self,
        parent: &EnvDeclBuilder,
        sa: Sign,
        a_mag: &Expr,
        sb: Sign,
        b_mag: &Expr,
        sc: Sign,
        c_mag: &Expr,
    ) -> Expr {
        let a = self.signed(sa, a_mag.clone());
        let b = self.signed(sb, b_mag.clone());
        let cc = self.signed(sc, c_mag.clone());

        let sab = sa.mul(sb);
        let sbc = sb.mul(sc);
        let net = sab.mul(sc); // = sa·sb·sc = sab·sc = sa·sbc

        let ab_mag = self.nmul(a_mag.clone(), b_mag.clone()); // A*B
        let bc_mag = self.nmul(b_mag.clone(), c_mag.clone()); // B*C
        let abc_left = self.nmul(ab_mag.clone(), c_mag.clone()); // (A*B)*C
        let abc_right = self.nmul(a_mag.clone(), bc_mag.clone()); // A*(B*C)

        // --- LHS chain: (a*b)*c = net (ofNat ((A*B)*C)) ---
        // step La : a*b = sab (ofNat (A*B))
        let la = self.signed_mul_eq(sa, a_mag, sb, b_mag);
        let ab_int = self.mul(a.clone(), b.clone());
        let sab_ab = self.signed(sab, ab_mag.clone());
        // congrArg (λ z => z * c) La : (a*b)*c = (sab (ofNat (A*B))) * c
        let mul_c_fn = {
            let mut fb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = fb.fresh_local(self.int_type.clone());
            let body = self.mul(z, cc.clone());
            let lam = fb.mk_lam(z_id, BinderInfo::Default, self.int_type.clone(), body);
            fb.finish_child(lam)
        };
        let lhs0 = self.mul(ab_int.clone(), cc.clone()); // (a*b)*c
        let lhs1 = self.mul(sab_ab.clone(), cc.clone()); // (sab (ofNat (A*B))) * c
        let l_congr = self.congr_arg_int(ab_int.clone(), sab_ab.clone(), mul_c_fn, la);
        // step Lb : (sab (ofNat (A*B))) * c = net (ofNat ((A*B)*C))
        let lb = self.signed_mul_eq(sab, &ab_mag, sc, c_mag);
        let lhs2 = self.signed(net, abc_left.clone()); // net (ofNat ((A*B)*C))
                                                       // eqL := trans l_congr lb
        let eq_l = self.trans_int(lhs0.clone(), lhs1, lhs2.clone(), l_congr, lb);

        // --- RHS chain: net (ofNat (A*(B*C))) = a*(b*c) ---
        // step Ra : b*c = sbc (ofNat (B*C))
        let ra = self.signed_mul_eq(sb, b_mag, sc, c_mag);
        let bc_int = self.mul(b.clone(), cc.clone());
        let sbc_bc = self.signed(sbc, bc_mag.clone());
        // congrArg (λ z => a * z) Ra : a*(b*c) = a * (sbc (ofNat (B*C)))
        let mul_a_fn = {
            let mut fb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = fb.fresh_local(self.int_type.clone());
            let body = self.mul(a.clone(), z);
            let lam = fb.mk_lam(z_id, BinderInfo::Default, self.int_type.clone(), body);
            fb.finish_child(lam)
        };
        let rhs0 = self.mul(a.clone(), bc_int.clone()); // a*(b*c)
        let rhs1 = self.mul(a.clone(), sbc_bc.clone()); // a * (sbc (ofNat (B*C)))
        let r_congr = self.congr_arg_int(bc_int.clone(), sbc_bc.clone(), mul_a_fn, ra);
        // step Rb : a * (sbc (ofNat (B*C))) = net (ofNat (A*(B*C)))
        let rb = self.signed_mul_eq(sa, a_mag, sbc, &bc_mag);
        let rhs2 = self.signed(net, abc_right.clone()); // net (ofNat (A*(B*C)))
                                                        // a*(b*c) = a * (sbc (ofNat (B*C))) = net (ofNat (A*(B*C)))
        let rhs_fwd = self.trans_int(rhs0.clone(), rhs1, rhs2.clone(), r_congr, rb);
        // eqR := symm rhs_fwd : net (ofNat (A*(B*C))) = a*(b*c)
        let eq_r = self.symm_int(rhs0.clone(), rhs2.clone(), rhs_fwd);

        // --- core: lift Nat.mul_assoc through (net ∘ ofNat) ---
        let signed_fn = self.signed_of_nat_fn(parent, net);
        let nat_assoc = self.nma(a_mag.clone(), b_mag.clone(), c_mag.clone());
        // nat_assoc : Eq Nat (Nat.mul (Nat.mul A B) C) (Nat.mul A (Nat.mul B C))
        //           = Eq Nat abc_left abc_right
        let core = self.congr_arg_nat_int(abc_left, abc_right, signed_fn, nat_assoc);

        // leaf := trans eq_l (trans core eq_r)
        //   eq_l : lhs0 (=(a*b)*c)              = lhs2 (= net (ofNat ((A*B)*C)))
        //   core : lhs2                         = rhs2 (= net (ofNat (A*(B*C))))
        //   eq_r : rhs2                         = rhs0 (= a*(b*c))
        let inner = self.trans_int(lhs2.clone(), rhs2, rhs0.clone(), core, eq_r);
        self.trans_int(lhs0, lhs2, rhs0, eq_l, inner)
    }
}

/// `∀ a b c : Int, Eq (mul (mul a b) c) (mul a (mul b c))`.
fn build_type(c: &IntMulAssocConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());
    let (cv_id, cv) = b.fresh_local(c.int_type.clone());
    let lhs = c.mul(c.mul(a.clone(), bv.clone()), cv.clone());
    let rhs = c.mul(a.clone(), c.mul(bv.clone(), cv.clone()));
    let concl = c.eq_int(lhs, rhs);
    let ty = b.mk_pi(cv_id, BinderInfo::Default, c.int_type.clone(), concl);
    let ty = b.mk_pi(bv_id, BinderInfo::Default, c.int_type.clone(), ty);
    let ty = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), ty);
    b.finish(ty)
}

/// Outer motive `λ x : Int => ∀ b c, Eq (mul (mul x b) c) (mul x (mul b c))`.
fn assoc_pi(c: &IntMulAssocConsts, parent: &EnvDeclBuilder, x: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (bv_id, bv) = mb.fresh_local(c.int_type.clone());
    let (cv_id, cv) = mb.fresh_local(c.int_type.clone());
    let lhs = c.mul(c.mul(x.clone(), bv.clone()), cv.clone());
    let rhs = c.mul(x.clone(), c.mul(bv.clone(), cv.clone()));
    let body = c.eq_int(lhs, rhs);
    let pi = mb.mk_pi(cv_id, BinderInfo::Default, c.int_type.clone(), body);
    let pi = mb.mk_pi(bv_id, BinderInfo::Default, c.int_type.clone(), pi);
    mb.finish_child(pi)
}

fn outer_motive(c: &IntMulAssocConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = mb.fresh_local(c.int_type.clone());
    let body = assoc_pi(c, &mb, &x);
    let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
    mb.finish_child(lam)
}

/// b-level motive for fixed `a`: `λ y : Int => ∀ c, Eq (mul (mul a y) c)(...)`.
fn b_motive(c: &IntMulAssocConsts, parent: &EnvDeclBuilder, a: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (y_id, y) = mb.fresh_local(c.int_type.clone());
    let (cc_id, cc) = mb.fresh_local(c.int_type.clone());
    let lhs = c.mul(c.mul(a.clone(), y.clone()), cc.clone());
    let rhs = c.mul(a.clone(), c.mul(y.clone(), cc.clone()));
    let body = c.eq_int(lhs, rhs);
    let pi = mb.mk_pi(cc_id, BinderInfo::Default, c.int_type.clone(), body);
    let lam = mb.mk_lam(y_id, BinderInfo::Default, c.int_type.clone(), pi);
    mb.finish_child(lam)
}

/// c-level motive for fixed `a`, `bval`: `λ z : Int => Eq (mul (mul a bval) z)(...)`.
fn c_motive(c: &IntMulAssocConsts, parent: &EnvDeclBuilder, a: &Expr, bval: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (z_id, z) = mb.fresh_local(c.int_type.clone());
    let lhs = c.mul(c.mul(a.clone(), bval.clone()), z.clone());
    let rhs = c.mul(a.clone(), c.mul(bval.clone(), z.clone()));
    let body = c.eq_int(lhs, rhs);
    let lam = mb.mk_lam(z_id, BinderInfo::Default, c.int_type.clone(), body);
    mb.finish_child(lam)
}

/// Build the c-level `Int.rec` for fixed outer `a` and middle `bval`.
fn build_c_rec(
    c: &IntMulAssocConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    bval: &Expr,
    leaf_c_ofnat: Expr,
    leaf_c_negsucc: Expr,
    cv: &Expr,
) -> Expr {
    let motive = c_motive(c, parent, a, bval);
    Expr::apps(
        c.int_rec.clone(),
        [motive, leaf_c_ofnat, leaf_c_negsucc, cv.clone()],
    )
}

/// Build one outer constructor case (`a = ofNat j` or `a = negSucc j`).
///
/// `sa` is the outer sign and `a_mag` the outer magnitude expression as a
/// function of the bound Nat `j` (`ofNat`: `A = j`; `negSucc`: `A = succ j`).
fn build_a_case(c: &IntMulAssocConsts, parent: &EnvDeclBuilder, sa: Sign) -> Expr {
    let mut jb = EnvDeclBuilder::child_of(parent);
    let (j_id, j) = jb.fresh_local(c.nat_type.clone());
    let a = match sa {
        Sign::Pos => c.of_nat(j.clone()),
        Sign::Neg => c.neg_succ(j.clone()),
    };
    let a_mag = match sa {
        Sign::Pos => j.clone(),
        Sign::Neg => c.succ(j.clone()),
    };
    let (bv_id, bv) = jb.fresh_local(c.int_type.clone());
    let (cv_id, cv) = jb.fresh_local(c.int_type.clone());

    // Middle constructor cases.
    //
    // The `b`-level `Int.rec` minor premise for constructor `ctor` must have
    // type `Π (p : Nat), b_motive (ctor p)`, and `b_motive (ctor p)` is the
    // `Π (c : Int), Eq …` produced by `b_motive`. The minor premise must
    // therefore be a FUNCTION of the inner `c` (the b-recursor is later
    // applied to `cv` at the a-case level, `App(brec, cv)` below). So each
    // case binds its OWN fresh inner `c` and runs the `c`-level `Int.rec` on
    // that bound variable — NOT on the outer `cv` (doing the latter collapses
    // the minor premise to a bare `Eq` for a fixed `cv`, which does not match
    // the `Π c` shape `b_motive` demands).
    let build_b_case = |sb: Sign| -> Expr {
        let mut pb = EnvDeclBuilder::child_of(&jb);
        let (p_id, p) = pb.fresh_local(c.nat_type.clone());
        let bval = match sb {
            Sign::Pos => c.of_nat(p.clone()),
            Sign::Neg => c.neg_succ(p.clone()),
        };
        let b_mag = match sb {
            Sign::Pos => p.clone(),
            Sign::Neg => c.succ(p.clone()),
        };

        // Fresh inner `c` abstracted by this minor premise (matches the `Π c`
        // in `b_motive (ctor p)`).
        let (cinner_id, cinner) = pb.fresh_local(c.int_type.clone());

        // Inner constructor cases (`c = ofNat r` / `c = negSucc r`).
        let build_c_leaf = |sc: Sign| -> Expr {
            let mut rb = EnvDeclBuilder::child_of(&pb);
            let (r_id, r) = rb.fresh_local(c.nat_type.clone());
            let c_mag = match sc {
                Sign::Pos => r.clone(),
                Sign::Neg => c.succ(r.clone()),
            };
            let proof = c.leaf(&rb, sa, &a_mag, sb, &b_mag, sc, &c_mag);
            let lam = rb.mk_lam(r_id, BinderInfo::Default, c.nat_type.clone(), proof);
            rb.finish_child(lam)
        };

        let leaf_c_ofnat = build_c_leaf(Sign::Pos);
        let leaf_c_negsucc = build_c_leaf(Sign::Neg);
        let crec = build_c_rec(c, &pb, &a, &bval, leaf_c_ofnat, leaf_c_negsucc, &cinner);
        let lam = pb.mk_lam(cinner_id, BinderInfo::Default, c.int_type.clone(), crec);
        let lam = pb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), lam);
        pb.finish_child(lam)
    };

    let b_ofnat = build_b_case(Sign::Pos);
    let b_negsucc = build_b_case(Sign::Neg);
    let brec = Expr::apps(
        c.int_rec.clone(),
        [b_motive(c, &jb, &a), b_ofnat, b_negsucc, bv.clone()],
    );
    let body = Expr::app(brec, cv);
    let lam = jb.mk_lam(cv_id, BinderInfo::Default, c.int_type.clone(), body);
    let lam = jb.mk_lam(bv_id, BinderInfo::Default, c.int_type.clone(), lam);
    let lam = jb.mk_lam(j_id, BinderInfo::Default, c.nat_type.clone(), lam);
    jb.finish_child(lam)
}

/// Body: `λ (a b c : Int) => (@Int.rec.{0} outer_motive a_ofNat a_negSucc a) b c`.
fn build_value(c: &IntMulAssocConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (a_id, a) = vb.fresh_local(c.int_type.clone());
    let (bv_id, bv) = vb.fresh_local(c.int_type.clone());
    let (cv_id, cv) = vb.fresh_local(c.int_type.clone());

    let motive = outer_motive(c, &vb);
    let a_ofnat = build_a_case(c, &vb, Sign::Pos);
    let a_negsucc = build_a_case(c, &vb, Sign::Neg);
    let rec_a = Expr::apps(c.int_rec.clone(), [motive, a_ofnat, a_negsucc, a]);
    let body = Expr::app(Expr::app(rec_a, bv), cv);
    let val = vb.mk_lam(cv_id, BinderInfo::Default, c.int_type.clone(), body);
    let val = vb.mk_lam(bv_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = vb.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    vb.finish(val)
}

impl Environment {
    /// Register `Int.mul_assoc` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`, `Int.ofNat`,
    ///           `Int.negSucc`, `Int.neg`, `Int.mul`, `Int.rec`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.succ`,
    ///           `Nat.mul`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`, `Eq.symm`,
    ///           `Eq.trans`, `congrArg`.
    /// REQUIRES: `Int.neg_mul_left`, `Int.neg_mul_right`, `Int.neg_neg`,
    ///           `Nat.mul_assoc` are registered as constructive
    ///           `Declaration::Theorem`s.
    /// ENSURES: On success, `Int.mul_assoc` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_mul_assoc_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.mul_assoc");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_int_neg_mul_left_proof()?;
        self.register_int_neg_mul_right_proof()?;
        self.register_int_neg_neg_proof()?;
        self.register_nat_mul_assoc_proof()?;

        let c = IntMulAssocConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Triple nested
        // `@Int.rec.{0}` (outer on `a`, then `b`, then `c`) with eight
        // constructor leaves. Each leaf normalizes both `(a*b)*c` and
        // `a*(b*c)` to a common net-signed `Int.ofNat` magnitude product via
        // the constructive sign lemmas `Int.neg_mul_left`,
        // `Int.neg_mul_right`, `Int.neg_neg`, then closes the residual
        // magnitude goal with `Nat.mul_assoc` lifted through the shared
        // (sign ∘ Int.ofNat) wrapper by `congrArg`. No `sorry`, no
        // self-reference, no domain-axiom dependency (every feeder lemma is
        // constructive #3604). Replaces the prior `Declaration::Axiom` in
        // `data_types_int_lemmas.rs::init_int_arith_lemmas`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};

    #[test]
    fn test_int_mul_assoc_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_mul_assoc_proof()
            .expect("first registration");
        env.register_int_mul_assoc_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.mul_assoc"))
            .expect("Int.mul_assoc should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_mul_assoc_proof_uses_int_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_mul_assoc_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.mul_assoc"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Peel three outer λ (a, b, c); body is `(Int.rec ... a) b c`.
        let mut body = value.clone();
        for _ in 0..3 {
            body = match body.kind() {
                ExprKind::Lam(_, _, inner) => (**inner).clone(),
                k => panic!("expected outer λ, got {:?}", k),
            };
        }
        let mut head = body;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Int.rec",
                "proof root must be Int.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Int.rec, ..) at proof root, got {:?}", k),
        }
    }

    #[test]
    fn test_int_mul_assoc_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_mul_assoc_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.mul_assoc"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.mul_assoc must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_mul_assoc_proof_quality_constructive() {
        let mut env = Environment::new();
        env.register_int_mul_assoc_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.mul_assoc"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.mul_assoc must be Constructive, got {:?}",
            quality
        );
    }
}
