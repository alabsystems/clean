// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Noise-operator semigroup campaign — the **per-coordinate noise convolution**
//! scalar engine (rung 1 of #1, the noiseOp Parseval diagonalization).
//!
//! ## What this file builds
//!
//! The single-coordinate noise kernel that rides each factor of
//! `noiseDensityW`'s product form (`noiseDensityW_eq_prod`) is
//!
//! ```text
//!   w(ρ, a, b) := 1 + ρ·(pm(a)·pm(b))            (a b : Bool)
//! ```
//!
//! (the `prod_int_rho` integrand in `boolean_analysis_noise_delta_proof.rs`:
//! `Rat.add Rat.one (Rat.mul ρ (Rat.mul (pm a) (pm b)))`). Composing the noise
//! operator with itself convolves this kernel over the lone intermediate
//! coordinate `z : Bool`. Since `pm(false) ≡ +1`, `pm(true) ≡ −1`, the two-term
//! `z`-sum collapses (`|Bool| = 2`) to
//!
//! ```text
//!   Σ_{z:Bool} w(ρ, a, z)·w(ρ, z, b) = 2·w(ρ², a, b)        (rho^2 appears)
//! ```
//!
//! The leading `2` is the per-coordinate `|Bool|` factor — it is the seed of the
//! `2^n` un-normalization the full cube semigroup carries (un-normalized
//! `subsetSum_z dens ρ x z · dens ρ z y = 2^n · dens ρ² x y`). Tracking it
//! honestly here is what makes the eventual noiseOp Parseval diagonalization
//! carry the correct `8^n` un-normalization.
//!
//! ## The scalar core (the reusable ring engine)
//!
//! All of the `pm`/Bool structure factors out of a single PURE-RATIONAL ring
//! identity in two free scalars `a b : Rat`:
//!
//! ```text
//!   BoolAnalysis.noise_conv_scalar :
//!     ∀ (a b : Rat),
//!       (1 + a)·(1 + b) + (1 + (−a))·(1 + (−b)) = (1 + 1)·(1 + a·b)
//! ```
//!
//! i.e. `(1+a)(1+b) + (1−a)(1−b) = 2·(1+ab)`. Instantiating `a := ρ·pm(x_i)`,
//! `b := ρ·pm(y_i)` (and the per-coordinate `z=true` sign-flip `ρ·u·(−1) =
//! −(ρ·u)`) turns the two `z`-summands into `(1±a)(1±b)` and the RHS into
//! `2·(1 + (ρ pm x_i)(ρ pm y_i)) = 2·(1 + ρ²·pm(x_i)·pm(y_i))` once
//! `mul_mul_mul_comm` regroups `(ρ·u)(ρ·v) = (ρ·ρ)(u·v)`.
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure)
//!
//! Both sides normalize to the canonical 2-block form `(1 + a·b) + (1 + a·b)`:
//!
//! * RHS `(1+1)·(1+ab)` →[`right_distrib 1 1 (1+ab)`] `1·(1+ab) + 1·(1+ab)`
//!   →[`one_mul` twice] `(1+ab) + (1+ab)`.
//! * LHS — each product expands by `right_distrib`+`left_distrib`+`one_mul`:
//!     `(1+a)(1+b)      = (1 + b) + (a + a·b)`
//!     `(1+(−a))(1+(−b)) = (1 + (−b)) + ((−a) + a·b)`     (`neg_mul_neg`, `mul_neg`)
//!   summing and reassociating (`add_assoc`/`add_comm`, with `b + (−b) = 0`,
//!   `a + (−a) = 0` via `add_neg_self`) collapses to `(1 + a·b) + (1 + a·b)`.
//!
//! The Rat ring lemmas (`Rat.left_distrib`, `Rat.right_distrib`, `Rat.one_mul`,
//! `Rat.mul_one`, `Rat.add_assoc`, `Rat.add_comm`, `Rat.add_neg_self`,
//! `Rat.add_zero`, `Rat.zero_add`, `Rat.mul_neg`, `Rat.neg_mul_neg`,
//! `Rat.mul_mul_mul_comm`) are all kernel-checked quotient Theorems whose axiom
//! closure is `⊆ FOUNDATIONAL` (`Quot.sound`/`propext`), so this is
//! `ProofQuality::Constructive` with an EMPTY domain-axiom closure. No axiom is
//! added or removed.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared Rat ring atoms for the convolution scalar engine.
pub(crate) struct ConvConsts {
    pub(crate) rat: Expr,
    pub(crate) rat_one: Expr,
    pub(crate) rat_mul: Expr,
    pub(crate) rat_add: Expr,
    pub(crate) rat_neg: Expr,
    eq1: Expr,
    pub(crate) eq_trans: Expr,
    pub(crate) eq_symm: Expr,
    pub(crate) congr_arg: Expr,
    // ring lemmas
    pub(crate) left_distrib: Expr,
    pub(crate) right_distrib: Expr,
    pub(crate) one_mul: Expr,
    pub(crate) add_assoc: Expr,
    pub(crate) add_comm: Expr,
    pub(crate) add_neg_self: Expr,
    pub(crate) add_zero: Expr,
    pub(crate) zero_add: Expr,
    pub(crate) neg_mul_neg: Expr,
    // factor atoms (for the Bool-level convolution wrapper)
    pub(crate) bool_: Expr,
    pub(crate) pm: Expr,
    pub(crate) mul_one: Expr,
    pub(crate) mul_neg: Expr,
    pub(crate) mul_comm: Expr,
    pub(crate) mmmc: Expr,
    pub(crate) pm_not: Expr,
    pub(crate) pm_mul_self: Expr,
    pub(crate) bfalse: Expr,
    pub(crate) btrue: Expr,
}

impl ConvConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_add: k("Rat.add"),
            rat_neg: k("Rat.neg"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            left_distrib: k("Rat.left_distrib"),
            right_distrib: k("Rat.right_distrib"),
            one_mul: k("Rat.one_mul"),
            add_assoc: k("Rat.add_assoc"),
            add_comm: k("Rat.add_comm"),
            add_neg_self: k("Rat.add_neg_self"),
            add_zero: k("Rat.add_zero"),
            zero_add: k("Rat.zero_add"),
            neg_mul_neg: k("Rat.neg_mul_neg"),
            bool_: k("Bool"),
            pm: k("BoolAnalysis.pm"),
            mul_one: k("Rat.mul_one"),
            mul_neg: k("Rat.mul_neg"),
            mul_comm: k("Rat.mul_comm"),
            mmmc: k("Rat.mul_mul_mul_comm"),
            pm_not: k("BoolAnalysis.pm_not"),
            pm_mul_self: k("BoolAnalysis.pm_mul_self"),
            bfalse: k("Bool.false"),
            btrue: k("Bool.true"),
        }
    }

    pub(crate) fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    pub(crate) fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    pub(crate) fn neg(&self, a: Expr) -> Expr {
        Expr::app(self.rat_neg.clone(), a)
    }
    pub(crate) fn one(&self) -> Expr {
        self.rat_one.clone()
    }
    pub(crate) fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    pub(crate) fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    pub(crate) fn symm(&self, l: Expr, r: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), l, r, h])
    }
    /// `congrArg.{1,1} Rat Rat from to motive h : motive from = motive to`.
    pub(crate) fn congr(&self, from: Expr, to: Expr, motive: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), from, to, motive, h],
        )
    }
    /// `fun (z : Rat) => Rat.add z r` — congruence on the LEFT summand.
    pub(crate) fn add_left_motive(&self, parent: &EnvDeclBuilder, r: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(self.rat.clone());
        let body = self.add(z, r.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }
    /// `fun (z : Rat) => Rat.add l z` — congruence on the RIGHT summand.
    pub(crate) fn add_right_motive(&self, parent: &EnvDeclBuilder, l: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(self.rat.clone());
        let body = self.add(l.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }

    // ── named lemma applications ────────────────────────────────────────────
    /// `Rat.right_distrib a b c : (a+b)·c = a·c + b·c`.
    pub(crate) fn h_right_distrib(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        Expr::apps(
            self.right_distrib.clone(),
            [a.clone(), b.clone(), cc.clone()],
        )
    }
    /// `Rat.left_distrib a b c : a·(b+c) = a·b + a·c`.
    pub(crate) fn h_left_distrib(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        Expr::apps(
            self.left_distrib.clone(),
            [a.clone(), b.clone(), cc.clone()],
        )
    }
    /// `Rat.one_mul a : 1·a = a`.
    pub(crate) fn h_one_mul(&self, a: &Expr) -> Expr {
        Expr::app(self.one_mul.clone(), a.clone())
    }
    /// `Rat.add_assoc a b c : (a+b)+c = a+(b+c)`.
    pub(crate) fn h_add_assoc(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        Expr::apps(self.add_assoc.clone(), [a.clone(), b.clone(), cc.clone()])
    }
    /// `Rat.add_comm a b : a+b = b+a`.
    pub(crate) fn h_add_comm(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.add_comm.clone(), [a.clone(), b.clone()])
    }
    /// `Rat.add_neg_self a : a + (−a) = 0`.
    pub(crate) fn h_add_neg_self(&self, a: &Expr) -> Expr {
        Expr::app(self.add_neg_self.clone(), a.clone())
    }
    /// `Rat.add_zero a : a + 0 = a`.
    pub(crate) fn h_add_zero(&self, a: &Expr) -> Expr {
        Expr::app(self.add_zero.clone(), a.clone())
    }
    /// `Rat.zero_add a : 0 + a = a`.
    pub(crate) fn h_zero_add(&self, a: &Expr) -> Expr {
        Expr::app(self.zero_add.clone(), a.clone())
    }
    /// `Rat.neg_mul_neg a b : (−a)·(−b) = a·b`.
    pub(crate) fn h_neg_mul_neg(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.neg_mul_neg.clone(), [a.clone(), b.clone()])
    }

    // ── factor-level helpers ────────────────────────────────────────────────
    /// `BoolAnalysis.pm b`.
    pub(crate) fn pm(&self, b: &Expr) -> Expr {
        Expr::app(self.pm.clone(), b.clone())
    }
    /// The per-coordinate noise factor `w(ρ,a,b) := 1 + ρ·(pm a · pm b)`.
    pub(crate) fn factor(&self, rho: &Expr, a: &Expr, b: &Expr) -> Expr {
        self.add(
            self.one(),
            self.mul(rho.clone(), self.mul(self.pm(a), self.pm(b))),
        )
    }
    /// `Rat.mul_one a : a·1 = a`.
    pub(crate) fn h_mul_one(&self, a: &Expr) -> Expr {
        Expr::app(self.mul_one.clone(), a.clone())
    }
    /// `Rat.mul_neg a b : a·(−b) = −(a·b)`.
    pub(crate) fn h_mul_neg(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.mul_neg.clone(), [a.clone(), b.clone()])
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    pub(crate) fn h_mul_comm(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a.clone(), b.clone()])
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    pub(crate) fn h_mmmc(&self, a: &Expr, b: &Expr, cc: &Expr, d: &Expr) -> Expr {
        Expr::apps(
            self.mmmc.clone(),
            [a.clone(), b.clone(), cc.clone(), d.clone()],
        )
    }
    /// `fun (z : Rat) => Rat.mul l z` — congruence on the RIGHT mul factor.
    pub(crate) fn mul_right_motive(&self, parent: &EnvDeclBuilder, l: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(self.rat.clone());
        let body = self.mul(l.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }
    /// `fun (z : Rat) => Rat.mul z r` — congruence on the LEFT mul factor.
    pub(crate) fn mul_left_motive(&self, parent: &EnvDeclBuilder, r: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(self.rat.clone());
        let body = self.mul(z, r.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }
    /// `BoolAnalysis.pm_not b : pm (Bool.not b) = Rat.neg (pm b)`.
    pub(crate) fn h_pm_not(&self, b: &Expr) -> Expr {
        Expr::app(self.pm_not.clone(), b.clone())
    }
    /// `BoolAnalysis.pm_mul_self b : pm b · pm b = 1`.
    pub(crate) fn h_pm_mul_self(&self, b: &Expr) -> Expr {
        Expr::app(self.pm_mul_self.clone(), b.clone())
    }
}

// ===========================================================================
// noise_conv_scalar : ∀ (a b : Rat),
//   (1+a)·(1+b) + (1+(−a))·(1+(−b)) = (1+1)·(1 + a·b)
//
// We prove `LHS = N` and `RHS = N` for the shared normal form
//   N := (1 + a·b) + (1 + a·b)
// then chain `LHS = N = RHS` (the second leg reversed by Eq.symm).
// ===========================================================================

impl Environment {
    /// Register `BoolAnalysis.noise_conv_scalar` — the pure-rational ring
    /// identity `(1+a)(1+b) + (1−a)(1−b) = 2·(1+ab)`, the scalar engine of the
    /// per-coordinate noise convolution. Kernel-checked, `Constructive`, EMPTY
    /// domain-axiom closure. Idempotent.
    pub(crate) fn register_noise_conv_scalar(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noise_conv_scalar");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.init_rat_arith()?; // Rat.add, Rat.mul, Rat.neg
                                // The quotient ring Theorems (left_distrib, …, add_neg_self) are wired by
                                // the live Rat field instance build.
        self.init_rat_field_inst()?;
        // `Rat.neg_mul_neg : (−a)·(−b) = a·b` is registered by the order toolkit.
        self.init_boolean_analysis_order_toolkit()?;

        let c = ConvConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_conv_scalar_type(&c),
            value: build_conv_scalar_value(&c),
        })
    }
}

fn build_conv_scalar_type(c: &ConvConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let concl = c.eq_rat(conv_lhs(c, &a, &bv), conv_rhs(c, &a, &bv));
    let ty = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), concl);
    let ty = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), ty);
    b.finish(ty)
}

/// `(1+a)·(1+b) + (1+(−a))·(1+(−b))`.
fn conv_lhs(c: &ConvConsts, a: &Expr, bv: &Expr) -> Expr {
    let p = c.mul(c.add(c.one(), a.clone()), c.add(c.one(), bv.clone()));
    let q = c.mul(
        c.add(c.one(), c.neg(a.clone())),
        c.add(c.one(), c.neg(bv.clone())),
    );
    c.add(p, q)
}

/// `(1+1)·(1 + a·b)`.
fn conv_rhs(c: &ConvConsts, a: &Expr, bv: &Expr) -> Expr {
    c.mul(
        c.add(c.one(), c.one()),
        c.add(c.one(), c.mul(a.clone(), bv.clone())),
    )
}

/// The shared normal form `N := (1 + a·b) + (1 + a·b)`.
fn conv_nf(c: &ConvConsts, a: &Expr, bv: &Expr) -> Expr {
    let blk = c.add(c.one(), c.mul(a.clone(), bv.clone()));
    c.add(blk.clone(), blk)
}

fn build_conv_scalar_value(c: &ConvConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());

    let lhs = conv_lhs(c, &a, &bv);
    let rhs = conv_rhs(c, &a, &bv);
    let nf = conv_nf(c, &a, &bv);

    // leg L : lhs = nf
    let leg_l = prove_lhs_eq_nf(c, &b, &a, &bv);
    // leg R : rhs = nf ; symm → nf = rhs
    let rhs_eq_nf = prove_rhs_eq_nf(c, &b, &a, &bv);
    let nf_eq_rhs = c.symm(rhs.clone(), nf.clone(), rhs_eq_nf);

    // proof : lhs = rhs
    let proof = c.trans(lhs, nf, rhs, leg_l, nf_eq_rhs);

    let val = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), proof);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}

/// `rhs = nf`: `(1+1)·(1+ab) = (1+ab) + (1+ab)`.
///   step1 `right_distrib 1 1 (1+ab)` : (1+1)·blk = 1·blk + 1·blk
///   step2 congr-left (one_mul blk) : 1·blk + 1·blk = blk + 1·blk
///   step3 congr-right (one_mul blk) : blk + 1·blk = blk + blk = nf
fn prove_rhs_eq_nf(c: &ConvConsts, parent: &EnvDeclBuilder, a: &Expr, bv: &Expr) -> Expr {
    let one = c.one();
    let blk = c.add(one.clone(), c.mul(a.clone(), bv.clone()));
    let rhs = c.mul(c.add(one.clone(), one.clone()), blk.clone());

    let one_blk = c.mul(one.clone(), blk.clone());
    // step1 : (1+1)·blk = 1·blk + 1·blk
    let step1 = c.h_right_distrib(&one, &one, &blk);
    let s1_rhs = c.add(one_blk.clone(), one_blk.clone());
    // step2 : 1·blk + 1·blk = blk + 1·blk   (congr left, one_mul blk)
    let oml = c.h_one_mul(&blk);
    let m_left = c.add_left_motive(parent, &one_blk);
    let step2 = c.congr(one_blk.clone(), blk.clone(), m_left, oml.clone());
    let s2_rhs = c.add(blk.clone(), one_blk.clone());
    // step3 : blk + 1·blk = blk + blk   (congr right, one_mul blk)
    let m_right = c.add_right_motive(parent, &blk);
    let step3 = c.congr(one_blk.clone(), blk.clone(), m_right, oml);
    let nf = c.add(blk.clone(), blk.clone());

    let t1 = c.trans(rhs, s1_rhs.clone(), s2_rhs.clone(), step1, step2);
    c.trans(
        c.mul(c.add(one.clone(), one), blk.clone()),
        s2_rhs,
        nf,
        t1,
        step3,
    )
}

/// `lhs = nf`. Builds via the documented expand-and-cancel chain.
///
/// First expand the two products into their distributed forms, then collapse.
/// We compute, as named Exprs:
///   P  := (1+a)·(1+b)              ; PD := (1 + b) + (a + a·b)
///   Q  := (1+(−a))·(1+(−b))        ; QD := (1 + (−b)) + ((−a) + a·b)
/// `lhs = P + Q`. We prove `P = PD`, `Q = QD`, then `PD + QD = nf`.
fn prove_lhs_eq_nf(c: &ConvConsts, parent: &EnvDeclBuilder, a: &Expr, bv: &Expr) -> Expr {
    let one = c.one();
    let ab = c.mul(a.clone(), bv.clone());

    // ── P := (1+a)·(1+b) ; show P = PD := (1+b) + (a + a·b) ───────────────────
    let one_p_a = c.add(one.clone(), a.clone());
    let one_p_b = c.add(one.clone(), bv.clone());
    let p = c.mul(one_p_a.clone(), one_p_b.clone());
    // right_distrib 1 a (1+b) : (1+a)·(1+b) = 1·(1+b) + a·(1+b)
    let rd_p = c.h_right_distrib(&one, a, &one_p_b);
    let one_mul_1pb = c.mul(one.clone(), one_p_b.clone());
    let a_mul_1pb = c.mul(a.clone(), one_p_b.clone());
    let p_split = c.add(one_mul_1pb.clone(), a_mul_1pb.clone());
    // congr-left one_mul (1+b) : 1·(1+b) + a·(1+b) = (1+b) + a·(1+b)
    let oml_1pb = c.h_one_mul(&one_p_b);
    let ml = c.add_left_motive(parent, &a_mul_1pb);
    let p_c1 = c.congr(one_mul_1pb.clone(), one_p_b.clone(), ml, oml_1pb);
    let p_after_c1 = c.add(one_p_b.clone(), a_mul_1pb.clone());
    // left_distrib a 1 b : a·(1+b) = a·1 + a·b
    let ld_a = c.h_left_distrib(a, &one, bv);
    let a_mul_1 = c.mul(a.clone(), one.clone());
    let a1_p_ab = c.add(a_mul_1.clone(), ab.clone());
    // congr-right (a·(1+b) → a·1 + a·b)
    let mr_p = c.add_right_motive(parent, &one_p_b);
    let p_c2 = c.congr(a_mul_1pb.clone(), a1_p_ab.clone(), mr_p, ld_a);
    let p_after_c2 = c.add(one_p_b.clone(), a1_p_ab.clone());
    // congr-right inside: a·1 → a  (mul_one a) wrapped: (a·1 + a·b) = (a + a·b)
    let mo_a = mul_one(c, a);
    let a_p_ab = c.add(a.clone(), ab.clone());
    // motive: fun z => (1+b) + (z + a·b)
    let m_inner = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let inner = c.add(z, ab.clone());
        let body = c.add(one_p_b.clone(), inner);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let p_c3 = c.congr(a_mul_1.clone(), a.clone(), m_inner, mo_a);
    let pd = c.add(one_p_b.clone(), a_p_ab.clone());

    // chain P = PD
    let p_t1 = c.trans(p.clone(), p_split.clone(), p_after_c1.clone(), rd_p, p_c1);
    let p_t2 = c.trans(
        p.clone(),
        p_after_c1.clone(),
        p_after_c2.clone(),
        p_t1,
        p_c2,
    );
    let p_eq_pd = c.trans(p.clone(), p_after_c2, pd.clone(), p_t2, p_c3);

    // ── Q := (1+(−a))·(1+(−b)) ; show Q = QD := (1+(−b)) + ((−a) + a·b) ──────
    let neg_a = c.neg(a.clone());
    let neg_b = c.neg(bv.clone());
    let one_p_na = c.add(one.clone(), neg_a.clone());
    let one_p_nb = c.add(one.clone(), neg_b.clone());
    let q = c.mul(one_p_na.clone(), one_p_nb.clone());
    // right_distrib 1 (−a) (1+(−b)) : (1+(−a))·(1+(−b)) = 1·(1+(−b)) + (−a)·(1+(−b))
    let rd_q = c.h_right_distrib(&one, &neg_a, &one_p_nb);
    let one_mul_1pnb = c.mul(one.clone(), one_p_nb.clone());
    let na_mul_1pnb = c.mul(neg_a.clone(), one_p_nb.clone());
    let q_split = c.add(one_mul_1pnb.clone(), na_mul_1pnb.clone());
    // congr-left one_mul (1+(−b))
    let oml_1pnb = c.h_one_mul(&one_p_nb);
    let ml_q = c.add_left_motive(parent, &na_mul_1pnb);
    let q_c1 = c.congr(one_mul_1pnb.clone(), one_p_nb.clone(), ml_q, oml_1pnb);
    let q_after_c1 = c.add(one_p_nb.clone(), na_mul_1pnb.clone());
    // left_distrib (−a) 1 (−b) : (−a)·(1+(−b)) = (−a)·1 + (−a)·(−b)
    let ld_na = c.h_left_distrib(&neg_a, &one, &neg_b);
    let na_mul_1 = c.mul(neg_a.clone(), one.clone());
    let na_mul_nb = c.mul(neg_a.clone(), neg_b.clone());
    let na1_p_nanb = c.add(na_mul_1.clone(), na_mul_nb.clone());
    let mr_q = c.add_right_motive(parent, &one_p_nb);
    let q_c2 = c.congr(na_mul_1pnb.clone(), na1_p_nanb.clone(), mr_q, ld_na);
    let q_after_c2 = c.add(one_p_nb.clone(), na1_p_nanb.clone());
    // collapse (−a)·1 → (−a)  [mul_one] and (−a)·(−b) → a·b  [neg_mul_neg]
    // motive: fun z => (1+(−b)) + z, with z stepping  (na·1 + na·nb) → (na + na·nb) → (na + ab)
    // step A: na·1 → na inside left of inner add
    let mo_na = mul_one(c, &neg_a);
    let m_inner_q_a = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let inner = c.add(z, na_mul_nb.clone());
        let body = c.add(one_p_nb.clone(), inner);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let q_c3 = c.congr(na_mul_1.clone(), neg_a.clone(), m_inner_q_a, mo_na);
    let q_after_c3 = c.add(one_p_nb.clone(), c.add(neg_a.clone(), na_mul_nb.clone()));
    // step B: na·nb → a·b inside right of inner add
    let nmn = c.h_neg_mul_neg(a, bv);
    let m_inner_q_b = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let inner = c.add(neg_a.clone(), z);
        let body = c.add(one_p_nb.clone(), inner);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let q_c4 = c.congr(na_mul_nb.clone(), ab.clone(), m_inner_q_b, nmn);
    let na_p_ab = c.add(neg_a.clone(), ab.clone());
    let qd = c.add(one_p_nb.clone(), na_p_ab.clone());

    // chain Q = QD
    let q_t1 = c.trans(q.clone(), q_split.clone(), q_after_c1.clone(), rd_q, q_c1);
    let q_t2 = c.trans(
        q.clone(),
        q_after_c1.clone(),
        q_after_c2.clone(),
        q_t1,
        q_c2,
    );
    let q_t3 = c.trans(
        q.clone(),
        q_after_c2.clone(),
        q_after_c3.clone(),
        q_t2,
        q_c3,
    );
    let q_eq_qd = c.trans(q.clone(), q_after_c3.clone(), qd.clone(), q_t3, q_c4);

    // ── lhs = P + Q  →[congr P→PD, Q→QD]  PD + QD  →[collapse]  nf ───────────
    let lhs = c.add(p.clone(), q.clone());
    // congr-left P→PD
    let m_lhs_l = c.add_left_motive(parent, &q);
    let lhs_c1 = c.congr(p.clone(), pd.clone(), m_lhs_l, p_eq_pd);
    let mid1 = c.add(pd.clone(), q.clone());
    // congr-right Q→QD
    let m_lhs_r = c.add_right_motive(parent, &pd);
    let lhs_c2 = c.congr(q.clone(), qd.clone(), m_lhs_r, q_eq_qd);
    let pd_qd = c.add(pd.clone(), qd.clone());

    // collapse PD + QD = nf
    let collapse = prove_pdqd_eq_nf(c, parent, a, bv);

    let l_t1 = c.trans(lhs.clone(), mid1.clone(), pd_qd.clone(), lhs_c1, lhs_c2);
    c.trans(lhs, pd_qd.clone(), conv_nf(c, a, bv), l_t1, collapse)
}

/// `PD + QD = nf` where
///   PD = (1+b) + (a + a·b),  QD = (1+(−b)) + ((−a) + a·b),  nf = (1+ab)+(1+ab).
///
/// Strategy: rearrange the eight atoms `{1, b, a, ab, 1, −b, −a, ab}` so the
/// `b + (−b)` and `a + (−a)` cancel. We prove this by establishing the two
/// regrouped halves explicitly. We use the "split-and-recombine" identity:
///   PD + QD = ((1+b)+(a+ab)) + ((1+(−b))+((−a)+ab))
/// We transport each PD/QD into the form `(1 + ab) + (b + a)` resp.
/// `(1 + ab) + ((−b) + (−a))` first (pure add_assoc/add_comm), then add and
/// cancel `(b+a) + ((−b)+(−a)) = 0`.
fn prove_pdqd_eq_nf(c: &ConvConsts, parent: &EnvDeclBuilder, a: &Expr, bv: &Expr) -> Expr {
    let one = c.one();
    let ab = c.mul(a.clone(), bv.clone());
    let neg_a = c.neg(a.clone());
    let neg_b = c.neg(bv.clone());

    // PD = (1+b) + (a+ab)
    let pd = c.add(c.add(one.clone(), bv.clone()), c.add(a.clone(), ab.clone()));
    // QD = (1+(−b)) + ((−a)+ab)
    let qd = c.add(
        c.add(one.clone(), neg_b.clone()),
        c.add(neg_a.clone(), ab.clone()),
    );
    let pd_qd = c.add(pd.clone(), qd.clone());

    // We re-express PD as (1+ab) + (b+a):
    //   pd_re : PD = (1+ab) + (b+a)
    let pd_re = prove_pd_regroup(c, parent, a, bv);
    let pd_target = c.add(c.add(one.clone(), ab.clone()), c.add(bv.clone(), a.clone()));
    //   qd_re : QD = (1+ab) + ((−b)+(−a))
    let qd_re = prove_qd_regroup(c, parent, a, bv);
    let qd_target = c.add(
        c.add(one.clone(), ab.clone()),
        c.add(neg_b.clone(), neg_a.clone()),
    );

    // congr both: PD+QD = pd_target + qd_target
    let m_l = c.add_left_motive(parent, &qd);
    let step_l = c.congr(pd.clone(), pd_target.clone(), m_l, pd_re);
    let mid = c.add(pd_target.clone(), qd.clone());
    let m_r = c.add_right_motive(parent, &pd_target);
    let step_r = c.congr(qd.clone(), qd_target.clone(), m_r, qd_re);
    let both = c.add(pd_target.clone(), qd_target.clone());
    let t_regroup = c.trans(pd_qd.clone(), mid.clone(), both.clone(), step_l, step_r);

    // Now: both = ((1+ab)+(b+a)) + ((1+ab)+((−b)+(−a)))
    // collapse to ((1+ab) + (1+ab)) + 0 = nf via add_neg cancel.  We prove
    //   both = nf  by `prove_blocks_cancel`.
    let blocks = prove_blocks_cancel(c, parent, a, bv);
    c.trans(pd_qd, both, conv_nf(c, a, bv), t_regroup, blocks)
}

/// PD = (1+b)+(a+ab)  ⟶  (1+ab)+(b+a).
/// We go: (1+b)+(a+ab)
///   →[add_assoc 1 b (a+ab)]  1 + (b + (a+ab))
///   →[congr-right: b+(a+ab) → b+(ab+a) via add_comm a ab; then →(b+ab)+a? ]
/// To keep it tractable we instead derive the target as a fully right-normalized
/// form and compare. Concretely we prove BOTH `PD` and `(1+ab)+(b+a)` equal the
/// right-nested normal form `1 + (b + (a + ab))` up to add_comm of the (a,ab)
/// and (b,a)+ab reshuffles, chaining add_assoc/add_comm.
fn prove_pd_regroup(c: &ConvConsts, parent: &EnvDeclBuilder, a: &Expr, bv: &Expr) -> Expr {
    let one = c.one();
    let ab = c.mul(a.clone(), bv.clone());

    // pd = (1+b)+(a+ab)
    let pd = c.add(c.add(one.clone(), bv.clone()), c.add(a.clone(), ab.clone()));
    // target = (1+ab)+(b+a)
    let target = c.add(c.add(one.clone(), ab.clone()), c.add(bv.clone(), a.clone()));

    // Normal form NF1 := 1 + (ab + (b + a))   (right-nested)
    let nf1 = c.add(one.clone(), c.add(ab.clone(), c.add(bv.clone(), a.clone())));
    let pd_to_nf1 = prove_pd_to_nf1(c, parent, a, bv);
    let tgt_to_nf1 = prove_pair_to_nf1(c, parent, &one, &ab, bv, a); // (1+ab)+(b+a) → 1+(ab+(b+a))
    let tgt_eq_nf1 = tgt_to_nf1; // already (target = nf1)
    let nf1_eq_tgt = c.symm(target.clone(), nf1.clone(), tgt_eq_nf1);
    c.trans(pd, nf1, target, pd_to_nf1, nf1_eq_tgt)
}

/// QD = (1+(−b))+((−a)+ab)  ⟶  (1+ab)+((−b)+(−a)).
fn prove_qd_regroup(c: &ConvConsts, parent: &EnvDeclBuilder, a: &Expr, bv: &Expr) -> Expr {
    let one = c.one();
    let ab = c.mul(a.clone(), bv.clone());
    let neg_a = c.neg(a.clone());
    let neg_b = c.neg(bv.clone());

    let qd = c.add(
        c.add(one.clone(), neg_b.clone()),
        c.add(neg_a.clone(), ab.clone()),
    );
    let target = c.add(
        c.add(one.clone(), ab.clone()),
        c.add(neg_b.clone(), neg_a.clone()),
    );
    // NF := 1 + (ab + ((−b) + (−a)))
    let nf1 = c.add(
        one.clone(),
        c.add(ab.clone(), c.add(neg_b.clone(), neg_a.clone())),
    );
    let qd_to_nf1 = prove_qd_to_nf1(c, parent, a, bv);
    let tgt_to_nf1 = prove_pair_to_nf1(c, parent, &one, &ab, &neg_b, &neg_a);
    let nf1_eq_tgt = c.symm(target.clone(), nf1.clone(), tgt_to_nf1);
    c.trans(qd, nf1, target, qd_to_nf1, nf1_eq_tgt)
}

/// `(x + p) + (q + r) = x + (p + (q + r))`  — but here we need
/// `(1 + s) + (t + u) → 1 + (s + (t + u))` then reshuffle `s,t,u`.
/// This helper proves `(1+b)+(a+ab) = 1 + (ab + (b + a))`.
fn prove_pd_to_nf1(c: &ConvConsts, parent: &EnvDeclBuilder, a: &Expr, bv: &Expr) -> Expr {
    let one = c.one();
    let ab = c.mul(a.clone(), bv.clone());

    // (1+b)+(a+ab)
    let pd = c.add(c.add(one.clone(), bv.clone()), c.add(a.clone(), ab.clone()));
    // step1 add_assoc 1 b (a+ab) : (1+b)+(a+ab) = 1 + (b + (a+ab))
    let a_ab = c.add(a.clone(), ab.clone());
    let s1 = c.h_add_assoc(&one, bv, &a_ab);
    let after1 = c.add(one.clone(), c.add(bv.clone(), a_ab.clone()));
    // We must reshuffle  (b + (a+ab))  →  (ab + (b+a)).
    let inner_from = c.add(bv.clone(), a_ab.clone()); // b + (a+ab)
    let inner_to = c.add(ab.clone(), c.add(bv.clone(), a.clone())); // ab + (b+a)
    let reshuf = prove_b_a_ab_reshuffle(c, parent, a, bv);
    let m = c.add_right_motive(parent, &one);
    let s2 = c.congr(inner_from.clone(), inner_to.clone(), m, reshuf);
    let nf1 = c.add(one.clone(), inner_to);
    c.trans(pd, after1, nf1, s1, s2)
}

/// `(1+(−b))+((−a)+ab) = 1 + (ab + ((−b)+(−a)))`.
fn prove_qd_to_nf1(c: &ConvConsts, parent: &EnvDeclBuilder, a: &Expr, bv: &Expr) -> Expr {
    let one = c.one();
    let ab = c.mul(a.clone(), bv.clone());
    let neg_a = c.neg(a.clone());
    let neg_b = c.neg(bv.clone());

    let qd = c.add(
        c.add(one.clone(), neg_b.clone()),
        c.add(neg_a.clone(), ab.clone()),
    );
    let na_ab = c.add(neg_a.clone(), ab.clone());
    let s1 = c.h_add_assoc(&one, &neg_b, &na_ab);
    let after1 = c.add(one.clone(), c.add(neg_b.clone(), na_ab.clone()));
    let inner_from = c.add(neg_b.clone(), na_ab.clone()); // (−b) + ((−a)+ab)
    let inner_to = c.add(ab.clone(), c.add(neg_b.clone(), neg_a.clone())); // ab + ((−b)+(−a))
                                                                           // Build the reshuffle directly:  (−b) + ((−a)+ab) → ab + ((−b)+(−a))
    let direct = prove_reshuffle_general(c, parent, &neg_b, &neg_a, &ab);
    let m = c.add_right_motive(parent, &one);
    let s2 = c.congr(inner_from.clone(), inner_to.clone(), m, direct);
    let nf1 = c.add(one.clone(), inner_to);
    c.trans(qd, after1, nf1, s1, s2)
}

/// `(x + ab) + (y + z)`-form helper. Proves `(1 + ab) + (s + t) = 1 + (ab + (s + t))`
/// via a single `add_assoc 1 ab (s+t)`.
fn prove_pair_to_nf1(
    c: &ConvConsts,
    _parent: &EnvDeclBuilder,
    one: &Expr,
    ab: &Expr,
    s: &Expr,
    t: &Expr,
) -> Expr {
    let st = c.add(s.clone(), t.clone());
    // add_assoc 1 ab (s+t) : (1+ab)+(s+t) = 1 + (ab + (s+t))
    c.h_add_assoc(one, ab, &st)
}

/// Reshuffle `b + (a + ab) = ab + (b + a)` via add_comm/add_assoc.
///   b + (a + ab)
///     →[congr-right add_comm a ab]   b + (ab + a)
///     →[add_comm b (ab+a)]           (ab + a) + b
///     →[add_assoc ab a b]            ab + (a + b)
///     →[congr-right add_comm a b]    ab + (b + a)
fn prove_b_a_ab_reshuffle(c: &ConvConsts, parent: &EnvDeclBuilder, a: &Expr, bv: &Expr) -> Expr {
    let ab = c.mul(a.clone(), bv.clone());
    let from = c.add(bv.clone(), c.add(a.clone(), ab.clone())); // b + (a+ab)

    // step1: a+ab → ab+a  (add_comm a ab), under right motive (b + ·)
    let comm_a_ab = c.h_add_comm(a, &ab);
    let m1 = c.add_right_motive(parent, bv);
    let s1 = c.congr(
        c.add(a.clone(), ab.clone()),
        c.add(ab.clone(), a.clone()),
        m1,
        comm_a_ab,
    );
    let after1 = c.add(bv.clone(), c.add(ab.clone(), a.clone())); // b + (ab+a)

    // step2: add_comm b (ab+a) : b + (ab+a) = (ab+a) + b
    let aba = c.add(ab.clone(), a.clone());
    let s2 = c.h_add_comm(bv, &aba);
    let after2 = c.add(aba.clone(), bv.clone()); // (ab+a) + b

    // step3: add_assoc ab a b : (ab+a)+b = ab + (a+b)
    let s3 = c.h_add_assoc(&ab, a, bv);
    let after3 = c.add(ab.clone(), c.add(a.clone(), bv.clone())); // ab + (a+b)

    // step4: congr-right add_comm a b : ab + (a+b) = ab + (b+a)
    let comm_a_b = c.h_add_comm(a, bv);
    let m4 = c.add_right_motive(parent, &ab);
    let s4 = c.congr(
        c.add(a.clone(), bv.clone()),
        c.add(bv.clone(), a.clone()),
        m4,
        comm_a_b,
    );
    let after4 = c.add(ab.clone(), c.add(bv.clone(), a.clone())); // ab + (b+a)

    let t1 = c.trans(from.clone(), after1.clone(), after2.clone(), s1, s2);
    let t2 = c.trans(from.clone(), after2.clone(), after3.clone(), t1, s3);
    c.trans(from, after3, after4, t2, s4)
}

/// General reshuffle `s + (u + w) = w + (s + u)`.
///   s + (u + w)
///     →[congr-right add_comm u w]   s + (w + u)
///     →[add_comm s (w+u)]           (w + u) + s
///     →[add_assoc w u s]            w + (u + s)
///     →[congr-right add_comm u s]   w + (s + u)
fn prove_reshuffle_general(
    c: &ConvConsts,
    parent: &EnvDeclBuilder,
    s: &Expr,
    u: &Expr,
    w: &Expr,
) -> Expr {
    let from = c.add(s.clone(), c.add(u.clone(), w.clone())); // s + (u+w)

    let comm_u_w = c.h_add_comm(u, w);
    let m1 = c.add_right_motive(parent, s);
    let s1 = c.congr(
        c.add(u.clone(), w.clone()),
        c.add(w.clone(), u.clone()),
        m1,
        comm_u_w,
    );
    let after1 = c.add(s.clone(), c.add(w.clone(), u.clone())); // s + (w+u)

    let wu = c.add(w.clone(), u.clone());
    let s2 = c.h_add_comm(s, &wu);
    let after2 = c.add(wu.clone(), s.clone()); // (w+u) + s

    let s3 = c.h_add_assoc(w, u, s);
    let after3 = c.add(w.clone(), c.add(u.clone(), s.clone())); // w + (u+s)

    let comm_u_s = c.h_add_comm(u, s);
    let m4 = c.add_right_motive(parent, w);
    let s4 = c.congr(
        c.add(u.clone(), s.clone()),
        c.add(s.clone(), u.clone()),
        m4,
        comm_u_s,
    );
    let after4 = c.add(w.clone(), c.add(s.clone(), u.clone())); // w + (s+u)

    let t1 = c.trans(from.clone(), after1.clone(), after2.clone(), s1, s2);
    let t2 = c.trans(from.clone(), after2.clone(), after3.clone(), t1, s3);
    c.trans(from, after3, after4, t2, s4)
}

/// `((1+ab)+(b+a)) + ((1+ab)+((−b)+(−a))) = (1+ab) + (1+ab)`.
///
/// Let `B := 1 + ab`. We must show `(B+(b+a)) + (B+((−b)+(−a))) = B + B`.
/// Set `P := b+a`, `M := (−b)+(−a)`. Then `P + M = 0` (since `b+(−b)=0`,
/// `a+(−a)=0`; we prove `(b+a)+((−b)+(−a)) = 0`). The shape
/// `(B+P) + (B+M) = (B+B) + (P+M) = (B+B)+0 = B+B`.
fn prove_blocks_cancel(c: &ConvConsts, parent: &EnvDeclBuilder, a: &Expr, bv: &Expr) -> Expr {
    let one = c.one();
    let ab = c.mul(a.clone(), bv.clone());
    let big_b = c.add(one.clone(), ab.clone());
    let neg_a = c.neg(a.clone());
    let neg_b = c.neg(bv.clone());
    let p = c.add(bv.clone(), a.clone()); // b + a
    let m = c.add(neg_b.clone(), neg_a.clone()); // (−b)+(−a)

    let bp = c.add(big_b.clone(), p.clone()); // B + P
    let bm = c.add(big_b.clone(), m.clone()); // B + M
    let from = c.add(bp.clone(), bm.clone());

    // step1: (B+P)+(B+M) = ((B+P)+B) + M    [Eq.symm (add_assoc (B+P) B M)]
    let s1 = c.symm(
        c.add(c.add(bp.clone(), big_b.clone()), m.clone()),
        from.clone(),
        c.h_add_assoc(&bp, &big_b, &m),
    );
    let after1 = c.add(c.add(bp.clone(), big_b.clone()), m.clone());

    // step2: (B+P)+B = B+(P+B)  [add_assoc B P B], under left motive (· + M)
    let s2_inner = c.h_add_assoc(&big_b, &p, &big_b);
    let m2 = c.add_left_motive(parent, &m);
    let s2 = c.congr(
        c.add(bp.clone(), big_b.clone()),
        c.add(big_b.clone(), c.add(p.clone(), big_b.clone())),
        m2,
        s2_inner,
    );
    let after2 = c.add(
        c.add(big_b.clone(), c.add(p.clone(), big_b.clone())),
        m.clone(),
    );

    // step3: P+B → B+P   (add_comm P B), under motive (B + ·) + M
    let comm_pb = c.h_add_comm(&p, &big_b);
    let m3 = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let inner = c.add(big_b.clone(), z);
        let body = c.add(inner, m.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let s3 = c.congr(
        c.add(p.clone(), big_b.clone()),
        c.add(big_b.clone(), p.clone()),
        m3,
        comm_pb,
    );
    let after3 = c.add(
        c.add(big_b.clone(), c.add(big_b.clone(), p.clone())),
        m.clone(),
    );

    // step4: B+(B+P) = (B+B)+P   [Eq.symm (add_assoc B B P)], under (· + M)
    let s4_inner = c.symm(
        c.add(c.add(big_b.clone(), big_b.clone()), p.clone()),
        c.add(big_b.clone(), c.add(big_b.clone(), p.clone())),
        c.h_add_assoc(&big_b, &big_b, &p),
    );
    let m4 = c.add_left_motive(parent, &m);
    let s4 = c.congr(
        c.add(big_b.clone(), c.add(big_b.clone(), p.clone())),
        c.add(c.add(big_b.clone(), big_b.clone()), p.clone()),
        m4,
        s4_inner,
    );
    let bb = c.add(big_b.clone(), big_b.clone());
    let after4 = c.add(c.add(bb.clone(), p.clone()), m.clone());

    // step5: ((B+B)+P)+M = (B+B)+(P+M)   [add_assoc (B+B) P M]
    let s5 = c.h_add_assoc(&bb, &p, &m);
    let after5 = c.add(bb.clone(), c.add(p.clone(), m.clone()));

    // step6: P+M → 0   (prove_pm_zero), under motive (B+B) + ·
    let pm_zero = prove_pm_zero(c, parent, a, bv);
    let zero = c.add(p.clone(), m.clone());
    let m6 = c.add_right_motive(parent, &bb);
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let s6 = c.congr(zero.clone(), rat_zero.clone(), m6, pm_zero);
    let after6 = c.add(bb.clone(), rat_zero.clone());

    // step7: (B+B)+0 = B+B   (add_zero (B+B))
    let s7 = c.h_add_zero(&bb);

    let t1 = c.trans(from.clone(), after1.clone(), after2.clone(), s1, s2);
    let t2 = c.trans(from.clone(), after2.clone(), after3.clone(), t1, s3);
    let t3 = c.trans(from.clone(), after3.clone(), after4.clone(), t2, s4);
    let t4 = c.trans(from.clone(), after4.clone(), after5.clone(), t3, s5);
    let t5 = c.trans(from.clone(), after5.clone(), after6.clone(), t4, s6);
    c.trans(from, after6, bb, t5, s7)
}

/// `(b + a) + ((−b) + (−a)) = 0`.
///   (b+a) + ((−b)+(−a))
///     →[reshuffle to (b+(−b)) + (a+(−a))]    via add_assoc/add_comm
///     →[add_neg_self b, add_neg_self a]       0 + 0 = 0.
/// We build the reshuffle directly:
///   (b+a)+((−b)+(−a))
///     →[add_assoc b a ((−b)+(−a))]    b + (a + ((−b)+(−a)))
///     →[congr-right: a+((−b)+(−a)) → (−b)+(a+(−a)) ] ...
/// Simpler: prove via `(b+a)+((−b)+(−a)) = (b+(−b)) + (a+(−a))` with a generic
/// 4-term swap, then collapse.
fn prove_pm_zero(c: &ConvConsts, parent: &EnvDeclBuilder, a: &Expr, bv: &Expr) -> Expr {
    let neg_a = c.neg(a.clone());
    let neg_b = c.neg(bv.clone());
    let p = c.add(bv.clone(), a.clone()); // b + a
    let m = c.add(neg_b.clone(), neg_a.clone()); // (−b)+(−a)
    let from = c.add(p.clone(), m.clone());

    // target intermediate: (b + (−b)) + (a + (−a))
    let bnb = c.add(bv.clone(), neg_b.clone());
    let ana = c.add(a.clone(), neg_a.clone());
    let swapped = c.add(bnb.clone(), ana.clone());

    // four-term swap: (b+a)+((−b)+(−a)) = (b+(−b))+(a+(−a))
    let swap = prove_four_swap(c, parent, bv, a, &neg_b, &neg_a);

    // collapse: (b+(−b))+(a+(−a)) = 0+0 = 0
    let bnb_zero = c.h_add_neg_self(bv); // b+(−b) = 0
    let ana_zero = c.h_add_neg_self(a); // a+(−a) = 0
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    // congr-left bnb→0
    let ml = c.add_left_motive(parent, &ana);
    let cl = c.congr(bnb.clone(), rat_zero.clone(), ml, bnb_zero);
    let after_l = c.add(rat_zero.clone(), ana.clone());
    // congr-right ana→0
    let mr = c.add_right_motive(parent, &rat_zero);
    let cr = c.congr(ana.clone(), rat_zero.clone(), mr, ana_zero);
    let zero_zero = c.add(rat_zero.clone(), rat_zero.clone());
    // 0+0 = 0  (zero_add 0)
    let zz = c.h_zero_add(&rat_zero);

    let t1 = c.trans(from.clone(), swapped.clone(), after_l.clone(), swap, cl);
    let t2 = c.trans(from.clone(), after_l.clone(), zero_zero.clone(), t1, cr);
    c.trans(from, zero_zero, rat_zero, t2, zz)
}

/// Generic four-term swap: `(w+x) + (y+z) = (w+y) + (x+z)`.
/// This is exactly the additive analogue of `mul_mul_mul_comm`; we build it from
/// add_assoc/add_comm:
///   (w+x)+(y+z)
///     →[add_assoc w x (y+z)]            w + (x + (y+z))
///     →[congr-right: x+(y+z) → y+(x+z)] w + (y + (x+z))     (reshuffle_general x y z gives x+(y+z)=z+(x+y); not quite)
/// We instead reshuffle `x + (y+z) = y + (x+z)` directly.
fn prove_four_swap(
    c: &ConvConsts,
    parent: &EnvDeclBuilder,
    w: &Expr,
    x: &Expr,
    y: &Expr,
    z: &Expr,
) -> Expr {
    let from = c.add(c.add(w.clone(), x.clone()), c.add(y.clone(), z.clone()));

    // step1 add_assoc w x (y+z) : (w+x)+(y+z) = w + (x+(y+z))
    let yz = c.add(y.clone(), z.clone());
    let s1 = c.h_add_assoc(w, x, &yz);
    let after1 = c.add(w.clone(), c.add(x.clone(), yz.clone()));

    // step2: x+(y+z) → y+(x+z)   (mid reshuffle), under right motive (w + ·)
    let mid = prove_mid_swap(c, parent, x, y, z);
    let m2 = c.add_right_motive(parent, w);
    let xz = c.add(x.clone(), z.clone());
    let s2 = c.congr(
        c.add(x.clone(), yz.clone()),
        c.add(y.clone(), xz.clone()),
        m2,
        mid,
    );
    let after2 = c.add(w.clone(), c.add(y.clone(), xz.clone()));

    // step3 Eq.symm (add_assoc w y (x+z)) : w + (y+(x+z)) = (w+y)+(x+z)
    let s3 = c.symm(
        c.add(c.add(w.clone(), y.clone()), xz.clone()),
        c.add(w.clone(), c.add(y.clone(), xz.clone())),
        c.h_add_assoc(w, y, &xz),
    );
    let after3 = c.add(c.add(w.clone(), y.clone()), xz.clone());

    let t1 = c.trans(from.clone(), after1.clone(), after2.clone(), s1, s2);
    c.trans(from, after2, after3, t1, s3)
}

/// `x + (y + z) = y + (x + z)`.
///   x + (y+z)
///     →[Eq.symm add_assoc x y z]   (x+y) + z
///     →[congr-left add_comm x y]   (y+x) + z
///     →[add_assoc y x z]           y + (x+z)
fn prove_mid_swap(c: &ConvConsts, parent: &EnvDeclBuilder, x: &Expr, y: &Expr, z: &Expr) -> Expr {
    let from = c.add(x.clone(), c.add(y.clone(), z.clone()));
    // step1 symm add_assoc x y z : x+(y+z) = (x+y)+z
    let s1 = c.symm(
        c.add(c.add(x.clone(), y.clone()), z.clone()),
        from.clone(),
        c.h_add_assoc(x, y, z),
    );
    let after1 = c.add(c.add(x.clone(), y.clone()), z.clone());
    // step2 congr-left add_comm x y : (x+y)+z = (y+x)+z
    let comm = c.h_add_comm(x, y);
    let ml = c.add_left_motive(parent, z);
    let s2 = c.congr(
        c.add(x.clone(), y.clone()),
        c.add(y.clone(), x.clone()),
        ml,
        comm,
    );
    let after2 = c.add(c.add(y.clone(), x.clone()), z.clone());
    // step3 add_assoc y x z : (y+x)+z = y+(x+z)
    let s3 = c.h_add_assoc(y, x, z);
    let after3 = c.add(y.clone(), c.add(x.clone(), z.clone()));

    let t1 = c.trans(from.clone(), after1.clone(), after2.clone(), s1, s2);
    c.trans(from, after2, after3, t1, s3)
}

// ── small helpers ──────────────────────────────────────────────────────────

/// `Rat.mul_one a : a·1 = a`.
fn mul_one(c: &ConvConsts, a: &Expr) -> Expr {
    let _ = c;
    Expr::app(
        Expr::const_(Name::from_string("Rat.mul_one"), vec![]),
        a.clone(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_noise_conv_scalar_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_noise_conv_scalar()
            .expect("register_noise_conv_scalar");
        env.register_noise_conv_scalar().expect("idempotent");
        let name = Name::from_string("BoolAnalysis.noise_conv_scalar");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("noise_conv_scalar proof must check against its type");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
    }
}
