// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proofs on the way to NOISE STABILITY: the ρ-weighted character
//! bilinear-collapse delta
//!
//! ```text
//! subsetSum_chi_bilinear_rho : ∀ (ρ : Rat) (n : Nat) (x y : HCPoint n),
//!   subsetSum n (fun S => ρ^{|S|} · (χ_S(x) · χ_S(y)))
//!     = Fin.prod n (fun i => 1 + ρ · pm(x_i) · pm(y_i))
//! ```
//!
//! This GENERALIZES the proven `subsetSum_chi_bilinear`
//! (`boolean_analysis_delta_proof.rs`): its exact statement+proof is the `ρ = 1`
//! case. Summing the per-point integrand `ρ^{|S|}·χ_S(x)·χ_S(y)` over ALL `2^n`
//! subsets `S` factors (by independence of the per-coordinate subset bits) into a
//! product over coordinates of the per-coordinate sum
//! `Σ_{S_i∈{0,1}} ρ^{S_i}·cf(S_i,x_i)·cf(S_i,y_i) = 1·1 + ρ·pm(x_i)·pm(y_i)`. The
//! factor `1 + ρ·pm(a)·pm(b)` is the un-normalized correlated per-coordinate
//! weight `w_i = 1 + ρ·pm(x_i)·pm(y_i)` (= `1+ρ` when `x_i = y_i`, `1−ρ`
//! otherwise; the `/2`-per-coordinate normalization is deferred to a later run).
//!
//! Proof is by induction on `n` (the `Nat.rec` carrier under `subsetSum` /
//! `Fin.prod`), mirroring `subsetSum_chi_bilinear` with the ρ-weight `ρ^{|S|}`
//! threaded through:
//! - the popcount `|S|` splits over the top coordinate
//!   (`popcount (n+1) S ≡ popcount n (S∘castSucc) + indNat (S last)`, the
//!   `Fin.sumNat` ι-step) and so does its ρ-power
//!   (`ρ^{a+b} = ρ^a·ρ^b`, `powNat_add`);
//! - on the LOW half the top factor contributes `ρ^0 = 1`, on the HIGH half
//!   `ρ^1 = ρ` (`indNat false = 0`, `indNat true = 1` defeq; `powNat_zero` /
//!   `powNat_succ`);
//! - the per-coordinate pair-sum becomes
//!   `1·(cf F·cf F) + ρ·(cf T·cf T) = 1 + ρ·pm·pm`
//!   (`chi_factor_pair_sum_rho`);
//! - the induction hypothesis collapses each `2^n`-cube prefix sum into the
//!   `Fin.prod n` over the first `n` coordinates;
//! - `Fin.prod_succ` reassembles the `(n+1)`-coordinate product.
//!
//! Every rung is a kernel-checked `Declaration::Theorem` / reducible
//! `Declaration::Definition` with an EMPTY admitted-axiom closure
//! (`ProofQuality::Constructive`); no axiom is added or removed.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

// ===========================================================================
// Rat.powNat — the Nat-exponent power of a rational.
//
//   Rat.powNat (ρ : Rat) (k : Nat) : Rat
//     := @Nat.rec.{1} (fun _ => Rat) Rat.one (fun _k ih => Rat.mul ρ ih) k
//
//   ρ^0     = 1
//   ρ^(k+1) = ρ · ρ^k
//
// Reducible Definition. The `Nat.rec` carrier gives both reduction equations
// by a single ι-step, so `powNat_zero` / `powNat_succ` are `Eq.refl`-able.
// ===========================================================================

/// Shared constants for the ρ-weighted delta proofs. The `factor` / `pm` /
/// `rat_two` constants mirror `DeltaConsts` (`boolean_analysis_delta_proof.rs`)
/// byte-for-byte so the ρ-weighted terms are def-eq to the kernel's `chi` peel.
struct NoiseConsts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    rat_one: Expr,
    rat_zero: Expr,
    rat_mul: Expr,
    rat_add: Expr,
    rat_sub: Expr,
    rat_two: Expr,
    pm: Expr,
    pow_nat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    bool_rec1: Expr,
    eq1: Expr,
    eq_refl1: Expr,
}

impl NoiseConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_one = Expr::app(nat_succ.clone(), nat_zero.clone());
        let two = Expr::app(nat_succ.clone(), nat_one.clone());
        // `Rat.mk (Int.ofNat 2) 1` — the rational 2, matching chi/pm's body.
        let rat_two = Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [
                Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), two),
                nat_one,
            ],
        );
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            rat_two,
            pm: Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]),
            pow_nat: Expr::const_(Name::from_string("Rat.powNat"), vec![]),
            nat_succ,
            nat_zero,
            bool_rec1: Expr::const_(Name::from_string("Bool.rec"), vec![type1.clone()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![type1]),
        }
    }

    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn nadd(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            [a.clone(), b.clone()],
        )
    }
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]),
            [a, b, cc],
        )
    }
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
            [a, b],
        )
    }
    fn mul_one(&self, a: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.mul_one"), vec![]), [a])
    }
    fn pow(&self, rho: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [rho.clone(), k.clone()])
    }
    fn pm(&self, b: Expr) -> Expr {
        Expr::app(self.pm.clone(), b)
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn refl_rat(&self, e: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.rat.clone(), e])
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        let eq_trans = Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        );
        Expr::apps(eq_trans, [self.rat.clone(), a, b, cc, h1, h2])
    }
    fn congr_rat(&self, from: Expr, to: Expr, motive: Expr, h: Expr) -> Expr {
        let congr_arg = Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        );
        Expr::apps(
            congr_arg,
            [self.rat.clone(), self.rat.clone(), from, to, motive, h],
        )
    }
    fn eq_symm_rat(&self, l: Expr, r: Expr, h: Expr) -> Expr {
        let eq_symm = Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        );
        Expr::apps(eq_symm, [self.rat.clone(), l, r, h])
    }
    fn eq_nat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nat.clone(), l, r])
    }
    fn refl_nat(&self, e: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.nat.clone(), e])
    }
    /// `congrArg.{1,1} Nat Rat from to motive h` — congruence on a `Nat → Rat`
    /// motive (used to lift a Nat-popcount equality up to a `ρ^·` Rat equality).
    fn congr_nat_rat(&self, from: Expr, to: Expr, motive: Expr, h: Expr) -> Expr {
        let congr_arg = Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        );
        Expr::apps(
            congr_arg,
            [self.nat.clone(), self.rat.clone(), from, to, motive, h],
        )
    }
    /// `fun (i : Fin n) => p (Fin.castSucc n i)` — restrict to first `n` coords,
    /// byte-for-byte the `DeltaConsts::restrict` build.
    fn restrict(&self, parent: &EnvDeclBuilder, n: &Expr, p: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let cs = Expr::apps(
            Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            [n.clone(), i],
        );
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, Expr::app(p.clone(), cs)))
    }
    fn last(&self, n: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.last"), vec![]),
            [n.clone()],
        )
    }
    fn trans_nat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        let eq_trans = Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        );
        Expr::apps(eq_trans, [self.nat.clone(), a, b, cc, h1, h2])
    }
    /// `congrArg.{1,1} Nat Nat from to motive h` — congruence on a `Nat → Nat`
    /// motive (used inside the popcount split's Nat.add slots).
    fn congr_nat(&self, from: Expr, to: Expr, motive: Expr, h: Expr) -> Expr {
        let congr_arg = Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        );
        Expr::apps(
            congr_arg,
            [self.nat.clone(), self.nat.clone(), from, to, motive, h],
        )
    }
    /// `Rat.powNat_add ρ a b : ρ^(a+b) = ρ^a · ρ^b`.
    fn pow_add(&self, rho: &Expr, a: &Expr, bb: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.powNat_add"), vec![]),
            [rho.clone(), a.clone(), bb.clone()],
        )
    }
    /// `Rat.powNat_zero ρ : ρ^0 = 1`.
    fn pow_zero(&self, rho: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.powNat_zero"), vec![]),
            [rho.clone()],
        )
    }
    /// `Rat.powNat_succ ρ k : ρ^(k+1) = ρ · ρ^k`.
    fn pow_succ(&self, rho: &Expr, k: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.powNat_succ"), vec![]),
            [rho.clone(), k.clone()],
        )
    }
    /// `Rat.left_distrib a b c : a·(b+c) = a·b + a·c`.
    fn left_distrib(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.left_distrib"), vec![]),
            [a, b, cc],
        )
    }

    /// `fun (_ : Bool) => Rat` — the Type-valued motive for chi's `Bool.rec`.
    fn bool_to_rat_motive(&self, parent: &EnvDeclBuilder) -> Expr {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, _t) = mb.fresh_local(self.bool_.clone());
        let lam = mb.mk_lam(
            t_id,
            BinderInfo::Default,
            self.bool_.clone(),
            self.rat.clone(),
        );
        mb.finish_child(lam)
    }

    /// `factor sb xb = @Bool.rec (fun _ => Rat) Rat.one (1 - 2·⟦xb⟧) sb`,
    /// byte-for-byte the per-coordinate factor `register_chi` / `chi_succ` build.
    /// `factor false _ ≡ 1`; `factor true b ≡ pm b` (def-eq).
    fn factor(&self, parent: &EnvDeclBuilder, sb: Expr, xb: Expr) -> Expr {
        let embed = Expr::apps(
            self.bool_rec1.clone(),
            [
                self.bool_to_rat_motive(parent),
                self.rat_zero.clone(),
                self.rat_one.clone(),
                xb,
            ],
        );
        let two_embed = Expr::apps(self.rat_mul.clone(), [self.rat_two.clone(), embed]);
        let signed = Expr::apps(self.rat_sub.clone(), [self.rat_one.clone(), two_embed]);
        Expr::apps(
            self.bool_rec1.clone(),
            [
                self.bool_to_rat_motive(parent),
                self.rat_one.clone(),
                signed,
                sb,
            ],
        )
    }
}

fn build_pow_nat_value(c: &NoiseConsts) -> Expr {
    // fun (ρ : Rat) (k : Nat) =>
    //   @Nat.rec.{1} (fun _ => Rat) Rat.one (fun _k ih => Rat.mul ρ ih) k
    let nat_rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());

    // motive : fun (_ : Nat) => Rat
    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (m_id, _m) = ch.fresh_local(c.nat.clone());
        ch.finish_child(ch.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), c.rat.clone()))
    };
    // succ_case : fun (_k : Nat) (ih : Rat) => Rat.mul ρ ih
    let succ_case = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (sk_id, _sk) = ch.fresh_local(c.nat.clone());
        let (ih_id, ih) = ch.fresh_local(c.rat.clone());
        let body = c.mul(rho.clone(), ih);
        let r = ch.mk_lam(ih_id, BinderInfo::Default, c.rat.clone(), body);
        let r = ch.mk_lam(sk_id, BinderInfo::Default, c.nat.clone(), r);
        ch.finish_child(r)
    };
    let rec_app = Expr::apps(nat_rec, [motive, c.rat_one.clone(), succ_case, k.clone()]);
    let val = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), rec_app);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}

fn build_pow_nat_type(c: &NoiseConsts) -> Expr {
    // (ρ : Rat) → (k : Nat) → Rat
    let mut b = EnvDeclBuilder::new();
    let (rho_id, _) = b.fresh_local(c.rat.clone());
    let (k_id, _) = b.fresh_local(c.nat.clone());
    let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), c.rat.clone());
    let r = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), r);
    b.finish(r)
}

fn build_pow_zero_type(c: &NoiseConsts) -> Expr {
    // ∀ (ρ : Rat), Rat.powNat ρ Nat.zero = Rat.one
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let concl = c.eq_rat(c.pow(&rho, &c.nat_zero), c.rat_one.clone());
    b.finish(b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), concl))
}

fn build_pow_zero_value(c: &NoiseConsts) -> Expr {
    // fun (ρ : Rat) => @Eq.refl Rat (Rat.powNat ρ Nat.zero)
    // (LHS ι-reduces to Rat.one; the kernel closes the refl by def-eq.)
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let proof = c.refl_rat(c.pow(&rho, &c.nat_zero));
    b.finish(b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), proof))
}

fn build_pow_succ_type(c: &NoiseConsts) -> Expr {
    // ∀ (ρ : Rat) (k : Nat),
    //   Rat.powNat ρ (Nat.succ k) = Rat.mul ρ (Rat.powNat ρ k)
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let lhs = c.pow(&rho, &c.succ(&k));
    let rhs = c.mul(rho.clone(), c.pow(&rho, &k));
    let concl = c.eq_rat(lhs, rhs);
    let t = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), concl);
    b.finish(b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), t))
}

fn build_pow_succ_value(c: &NoiseConsts) -> Expr {
    // fun (ρ : Rat) (k : Nat) => @Eq.refl Rat (Rat.powNat ρ (Nat.succ k))
    // (LHS ι-reduces one Nat.rec step to Rat.mul ρ (Rat.powNat ρ k).)
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let proof = c.refl_rat(c.pow(&rho, &c.succ(&k)));
    let val = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), proof);
    b.finish(b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), val))
}

impl Environment {
    /// Register `Rat.powNat (ρ : Rat) (k : Nat) : Rat` — the Nat-exponent power
    /// `ρ^0 = 1`, `ρ^(k+1) = ρ·ρ^k`, a reducible `Nat.rec` Definition. Idempotent.
    pub(crate) fn register_rat_pow_nat(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.powNat");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?;
        self.init_rat_arith()?; // Rat.mul

        let c = NoiseConsts::new();
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: build_pow_nat_type(&c),
            value: build_pow_nat_value(&c),
            is_reducible: true,
        })
    }

    /// Register `Rat.powNat_zero : ∀ ρ, ρ^0 = 1`. Kernel-checked, constructive
    /// (single ι-step `Eq.refl`; empty admitted-axiom closure). Idempotent.
    pub(crate) fn register_rat_pow_nat_zero_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.powNat_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_rat_pow_nat()?;

        let c = NoiseConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_pow_zero_type(&c),
            value: build_pow_zero_value(&c),
        })
    }

    /// Register `Rat.powNat_succ : ∀ ρ k, ρ^(k+1) = ρ·ρ^k`. Kernel-checked,
    /// constructive (single ι-step `Eq.refl`; empty closure). Idempotent.
    pub(crate) fn register_rat_pow_nat_succ_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.powNat_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_rat_pow_nat()?;

        let c = NoiseConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_pow_succ_type(&c),
            value: build_pow_succ_value(&c),
        })
    }
}

// ===========================================================================
// Rat.powNat_add — the exponent-additivity bridge (ladder rung 2).
//
//   ∀ (ρ : Rat) (a b : Nat),
//     Rat.powNat ρ (Nat.add a b) = Rat.mul (Rat.powNat ρ a) (Rat.powNat ρ b)
//
// `Nat.rec` on `b`. Since `Nat.add` recurses on its SECOND argument
// (`a + 0 ≡ a`, `a + succ k ≡ succ (a + k)`) and `Rat.powNat` ι-reduces by one
// `Nat.rec` step (`ρ^(succ m) ≡ ρ·ρ^m`):
//   * base `b = 0`: goal ≡ `ρ^a = ρ^a · ρ^0` ≡ `ρ^a = ρ^a · 1`, closed by
//     `Eq.symm (Rat.mul_one (ρ^a))`;
//   * step `b = k+1`, ih `ρ^(a+k) = ρ^a · ρ^k`: goal ≡
//     `ρ·ρ^(a+k) = ρ^a · (ρ·ρ^k)`, closed by the chain
//       ρ·ρ^(a+k) = ρ·(ρ^a·ρ^k)            congr (ρ·) ih
//                 = (ρ·ρ^a)·ρ^k            Eq.symm (mul_assoc ρ ρ^a ρ^k)
//                 = (ρ^a·ρ)·ρ^k            congr (·ρ^k) (mul_comm ρ ρ^a)
//                 = ρ^a·(ρ·ρ^k)            mul_assoc ρ^a ρ ρ^k.
// Kernel-checked, constructive (closure ⊆ {Rat.mul_one, Rat.mul_assoc,
// Rat.mul_comm} ∪ Eq built-ins).
// ===========================================================================

fn build_pow_add_type(c: &NoiseConsts) -> Expr {
    // ∀ (ρ : Rat) (a b : Nat),
    //   Rat.powNat ρ (Nat.add a b) = Rat.mul (Rat.powNat ρ a) (Rat.powNat ρ b)
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (a_id, a) = b.fresh_local(c.nat.clone());
    let (bv_id, bv) = b.fresh_local(c.nat.clone());
    let lhs = c.pow(&rho, &c.nadd(&a, &bv));
    let rhs = c.mul(c.pow(&rho, &a), c.pow(&rho, &bv));
    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(bv_id, BinderInfo::Default, c.nat.clone(), concl);
    let ty = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), ty);
    let ty = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), ty);
    b.finish(ty)
}

fn build_pow_add_value(c: &NoiseConsts) -> Expr {
    // fun (ρ : Rat) (a : Nat) =>
    //   @Nat.rec.{0} (motive) base step  -- motive b := ρ^(a+b) = ρ^a·ρ^b
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (a_id, a) = b.fresh_local(c.nat.clone());

    let pow_a = c.pow(&rho, &a);

    // motive : fun (bv : Nat) => ρ^(a+bv) = ρ^a·ρ^bv
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (bv_id, bv) = d.fresh_local(c.nat.clone());
        let body = c.eq_rat(
            c.pow(&rho, &c.nadd(&a, &bv)),
            c.mul(pow_a.clone(), c.pow(&rho, &bv)),
        );
        d.finish_child(d.mk_lam(bv_id, BinderInfo::Default, c.nat.clone(), body))
    };

    // base : ρ^(a+0) = ρ^a·ρ^0   (def-eq to  ρ^a = ρ^a·1)
    //   = Eq.symm (Rat.mul_one (ρ^a))  :  ρ^a = Rat.mul (ρ^a) Rat.one
    let base = {
        let mul_a_one = c.mul(pow_a.clone(), c.rat_one.clone());
        c.eq_symm_rat(mul_a_one, pow_a.clone(), c.mul_one(pow_a.clone()))
    };

    // step : fun (k : Nat) (ih : ρ^(a+k) = ρ^a·ρ^k) =>
    //   <chain> : ρ·ρ^(a+k) = ρ^a·(ρ·ρ^k)
    //   (def-eq to motive (succ k): ρ^(a+(k+1)) = ρ^a·ρ^(k+1))
    let step = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (k_id, k) = d.fresh_local(c.nat.clone());
        let ih_ty = c.eq_rat(
            c.pow(&rho, &c.nadd(&a, &k)),
            c.mul(pow_a.clone(), c.pow(&rho, &k)),
        );
        let (ih_id, ih) = d.fresh_local(ih_ty.clone());

        let pow_ak = c.pow(&rho, &c.nadd(&a, &k));
        let pow_k = c.pow(&rho, &k);
        let pa_pk = c.mul(pow_a.clone(), pow_k.clone());

        // leg1 : ρ·ρ^(a+k) = ρ·(ρ^a·ρ^k)   congr (ρ·) ih
        let mul_left_rho = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (z_id, z) = e.fresh_local(c.rat.clone());
            let body = c.mul(rho.clone(), z);
            e.finish_child(e.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let leg1 = c.congr_rat(pow_ak.clone(), pa_pk.clone(), mul_left_rho, ih);

        // leg2 : ρ·(ρ^a·ρ^k) = (ρ·ρ^a)·ρ^k   Eq.symm (mul_assoc ρ ρ^a ρ^k)
        // mul_assoc ρ ρ^a ρ^k : (ρ·ρ^a)·ρ^k = ρ·(ρ^a·ρ^k);  @Eq.symm Rat A B h : B=A.
        let rho_pa = c.mul(rho.clone(), pow_a.clone());
        let assoc1 = c.mul_assoc(rho.clone(), pow_a.clone(), pow_k.clone());
        let rho_times_papk = c.mul(rho.clone(), pa_pk.clone());
        let rhopa_pk = c.mul(rho_pa.clone(), pow_k.clone());
        let leg2 = c.eq_symm_rat(rhopa_pk.clone(), rho_times_papk.clone(), assoc1);

        // leg3 : (ρ·ρ^a)·ρ^k = (ρ^a·ρ)·ρ^k   congr (·ρ^k) (mul_comm ρ ρ^a)
        let mul_right_pk = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (z_id, z) = e.fresh_local(c.rat.clone());
            let body = c.mul(z, pow_k.clone());
            e.finish_child(e.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let pa_rho = c.mul(pow_a.clone(), rho.clone());
        let comm = c.mul_comm(rho.clone(), pow_a.clone());
        let parho_pk = c.mul(pa_rho.clone(), pow_k.clone());
        let leg3 = c.congr_rat(rho_pa.clone(), pa_rho.clone(), mul_right_pk, comm);

        // leg4 : (ρ^a·ρ)·ρ^k = ρ^a·(ρ·ρ^k)   mul_assoc ρ^a ρ ρ^k
        let rho_pk = c.mul(rho.clone(), pow_k.clone());
        let pa_rhopk = c.mul(pow_a.clone(), rho_pk.clone());
        let leg4 = c.mul_assoc(pow_a.clone(), rho.clone(), pow_k.clone());

        // chain: ρ·ρ^(a+k) = ρ·(ρ^a·ρ^k) = (ρ·ρ^a)·ρ^k = (ρ^a·ρ)·ρ^k = ρ^a·(ρ·ρ^k)
        let t1 = c.trans_rat(
            rho_times_papk.clone(),
            rhopa_pk.clone(),
            parho_pk.clone(),
            leg2,
            leg3,
        );
        let t2 = c.trans_rat(rho_times_papk.clone(), parho_pk, pa_rhopk.clone(), t1, leg4);
        // prepend leg1 : (ρ·ρ^(a+k)) = (ρ·(ρ^a·ρ^k)) then t2.
        let proof = c.trans_rat(
            c.mul(rho.clone(), pow_ak.clone()),
            rho_times_papk,
            pa_rhopk,
            leg1,
            t2,
        );

        let r = d.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
        d.finish_child(d.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), r))
    };

    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let body = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (bv_id, bv) = d.fresh_local(c.nat.clone());
        let rec_app = Expr::apps(nat_rec, [motive, base, step, bv.clone()]);
        d.finish_child(d.mk_lam(bv_id, BinderInfo::Default, c.nat.clone(), rec_app))
    };
    let val = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), body);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Rat.powNat_add : ∀ ρ a b, ρ^(a+b) = ρ^a · ρ^b`. The
    /// exponent-additivity bridge for the popcount split (ladder rung 2).
    /// `Nat.rec` on `b`; kernel-checked, constructive (closure ⊆
    /// {`Rat.mul_one`, `Rat.mul_assoc`, `Rat.mul_comm`} ∪ Eq built-ins).
    /// Idempotent.
    pub(crate) fn register_rat_pow_nat_add_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.powNat_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_rat_pow_nat()?;
        self.init_rat_arith()?;
        // `Rat.mul_one` / `Rat.mul_assoc` / `Rat.mul_comm` are the quotient
        // structural lemmas (idempotent; each guarded on its own name).
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?;
        }

        let c = NoiseConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_pow_add_type(&c),
            value: build_pow_add_value(&c),
        })
    }
}

// ===========================================================================
// subsetSum_chi_bilinear_zero_rho — the n = 0 base of the ρ-weighted delta.
//
//   ∀ (ρ : Rat) (x y : HCPoint 0),
//     subsetSum 0 (fun S => ρ^{pc 0 S} · (χ 0 S x · χ 0 S y))
//       = Fin.prod 0 (fun i => 1 + ρ · pm(x_i) · pm(y_i))
//
// At n = 0 the only subset is empty: `pc 0 S ≡ Fin.sumNat 0 _ ≡ 0`, so
// `ρ^0 ≡ 1`, and `χ 0 _ _ ≡ 1`; the LHS `Fin.sum (2^0=1) (fun _ => 1·(1·1))`
// ι-reduces to `Rat.add Rat.zero (1·(1·1))`. The RHS `Fin.prod 0 _` ι-reduces
// to `Rat.one`. Goal `0 + 1·(1·1) = 1` is closed by
//   Eq.trans (zero_add (1·(1·1)))
//   (Eq.trans (one_mul (1·1)) (one_mul 1)).
// The ρ = 1 case mirrors `subsetSum_chi_bilinear_zero` exactly (the extra
// `ρ^0`-factored `1·` is the only structural difference; both ι-reduce away).
// Kernel-checked, constructive (closure ⊆ {Rat.zero_add, Rat.one_mul} ∪ Eq).
// ===========================================================================

impl NoiseConsts {
    fn nat_zero_e(&self) -> Expr {
        self.nat_zero.clone()
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            n.clone(),
        )
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), n.clone())
    }
    fn chi(&self, n: Expr, s: Expr, x: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            [n, s, x],
        )
    }
    /// `indNat (S i) = @Bool.rec.{1} (fun _ => Nat) 0 1 (S i)` — the per-bit
    /// {0,1} popcount summand, byte-for-byte the form `FourierWeightAtLevel`
    /// and the popcount carrier build.
    fn ind_nat(&self, s_i: Expr) -> Expr {
        let nat_one = self.succ(&self.nat_zero);
        let nat_motive = Expr::lam(BinderInfo::Default, self.bool_.clone(), self.nat.clone());
        let bool_rec_nat = Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        );
        Expr::apps(
            bool_rec_nat,
            [nat_motive, self.nat_zero.clone(), nat_one, s_i],
        )
    }
    /// `pc n S = Fin.sumNat n (fun i => indNat (S i))` — the popcount `|S|`.
    fn popcount(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.ind_nat(Expr::app(s.clone(), i.clone()));
        let pc_fn = b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body));
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sumNat"), vec![]),
            [n.clone(), pc_fn],
        )
    }
    /// The ρ-weighted subset integrand
    /// `fun S => ρ^{pc n S} · (χ n S x · χ n S y)`.
    fn ss_int_rho(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        x: &Expr,
        y: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let weight = self.pow(rho, &self.popcount(&b, n, &s));
        let chis = self.mul(
            self.chi(n.clone(), s.clone(), x.clone()),
            self.chi(n.clone(), s.clone(), y.clone()),
        );
        let body = self.mul(weight, chis);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    fn ss_lhs_rho(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        x: &Expr,
        y: &Expr,
    ) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            [n.clone(), self.ss_int_rho(parent, rho, n, x, y)],
        )
    }
    /// The ρ-weighted product integrand `fun i => 1 + ρ·(pm(x i)·pm(y i))`.
    fn prod_int_rho(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        x: &Expr,
        y: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let pm_x = self.pm(Expr::app(x.clone(), i.clone()));
        let pm_y = self.pm(Expr::app(y.clone(), i.clone()));
        let body = self.add(
            self.rat_one.clone(),
            self.mul(rho.clone(), self.mul(pm_x, pm_y)),
        );
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    fn prod_rhs_rho(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        x: &Expr,
        y: &Expr,
    ) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.prod"), vec![]),
            [n.clone(), self.prod_int_rho(parent, rho, n, x, y)],
        )
    }
}

fn build_base_rho_type(c: &NoiseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let zero = c.nat_zero_e();
    let hcp = c.hcpoint_of(&zero);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (y_id, y) = b.fresh_local(hcp.clone());
    let lhs = c.ss_lhs_rho(&b, &rho, &zero, &x, &y);
    let rhs = c.prod_rhs_rho(&b, &rho, &zero, &x, &y);
    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(y_id, BinderInfo::Default, hcp.clone(), concl);
    let ty = b.mk_pi(x_id, BinderInfo::Default, hcp, ty);
    let ty = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), ty);
    b.finish(ty)
}

fn build_base_rho_value(c: &NoiseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, _rho) = b.fresh_local(c.rat.clone());
    let zero = c.nat_zero_e();
    let hcp = c.hcpoint_of(&zero);
    let (x_id, _x) = b.fresh_local(hcp.clone());
    let (y_id, _y) = b.fresh_local(hcp.clone());

    // LHS ι-reduces to `Rat.add Rat.zero (Rat.mul Rat.one (Rat.mul Rat.one Rat.one))`
    // (ρ^0 ≡ 1, χ 0 _ _ ≡ 1). RHS ι-reduces to `Rat.one`.
    let one_one = c.mul(c.rat_one.clone(), c.rat_one.clone());
    let one_oneone = c.mul(c.rat_one.clone(), one_one.clone());
    let zero_add_term = c.add(c.rat_zero.clone(), one_oneone.clone());

    let zero_add =
        |e: Expr| Expr::apps(Expr::const_(Name::from_string("Rat.zero_add"), vec![]), [e]);
    let one_mul = |e: Expr| Expr::apps(Expr::const_(Name::from_string("Rat.one_mul"), vec![]), [e]);

    // leg1 : 0 + 1·(1·1) = 1·(1·1)   (zero_add (1·(1·1)))
    let leg1 = zero_add(one_oneone.clone());
    // leg2 : 1·(1·1) = 1·1           (one_mul (1·1))
    let leg2 = one_mul(one_one.clone());
    // leg3 : 1·1 = 1                 (one_mul 1)
    let leg3 = one_mul(c.rat_one.clone());
    // t1 : 0 + 1·(1·1) = 1·1
    let t1 = c.trans_rat(zero_add_term, one_oneone, one_one.clone(), leg1, leg2);
    // proof : 0 + 1·(1·1) = 1   (def-eq to LHS = RHS).
    let proof = c.trans_rat(
        c.add(
            c.rat_zero.clone(),
            c.mul(c.rat_one.clone(), one_one.clone()),
        ),
        one_one,
        c.rat_one.clone(),
        t1,
        leg3,
    );

    let val = b.mk_lam(y_id, BinderInfo::Default, hcp.clone(), proof);
    let val = b.mk_lam(x_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.subsetSum_chi_bilinear_zero_rho`: the `n = 0` base
    /// of the ρ-weighted bilinear delta (ladder rung 3, base). Kernel-checked,
    /// constructive (closure ⊆ {`Rat.zero_add`, `Rat.one_mul`} ∪ Eq built-ins).
    /// Idempotent.
    pub(crate) fn register_subset_sum_chi_bilinear_zero_rho_theorem(
        &mut self,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_chi_bilinear_zero_rho");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.init_rat_arith()?;
        self.register_rat_pow_nat()?;
        self.register_subset_sum()?;
        // `chi`, `pm`, `Fin.prod`, `Fin.sumNat` come with boolean analysis.
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Re-check: the `init_boolean_analysis` pass (bonami/hc24 retirement)
        // registers this theorem transitively.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = NoiseConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_base_rho_type(&c),
            value: build_base_rho_value(&c),
        })
    }
}

// ===========================================================================
// chi_factor_pair_sum_rho — the ρ-weighted per-coordinate pair-sum collapse.
//
//   ∀ (ρ : Rat) (a c : Bool),
//     1·(cf(false,a)·cf(false,c)) + ρ·(cf(true,a)·cf(true,c))
//       = 1 + ρ·(pm(a)·pm(c))
//
// The ρ-weighted generalization of `chi_factor_pair_sum`: the LOW half carries
// `ρ^0 = 1`, the HIGH half `ρ^1 = ρ`. Since `cf false _ ≡ 1` and
// `cf true b ≡ pm b` definitionally, the LHS def-eq-reduces to
//   `Rat.mul 1 (Rat.mul 1 1) + Rat.mul ρ (Rat.mul (pm a)(pm c))`.
// The RHS is `1 + ρ·(pm(a)·pm(c))`. The right summand is byte-identical; the
// only non-trivial step is `1·(1·1) = 1`, supplied by
//   `Eq.trans (congrArg (Rat.mul 1 ·) (Rat.one_mul 1)) (Rat.one_mul 1)`.
// We close with a single `congrArg` over the addition's left argument.
// ===========================================================================

fn build_pair_sum_rho_type(c: &NoiseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (a_id, a) = b.fresh_local(c.bool_.clone());
    let (cc_id, cc) = b.fresh_local(c.bool_.clone());

    let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
    let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);

    // LHS: 1·(cf(false,a)·cf(false,c)) + ρ·(cf(true,a)·cf(true,c))
    let low = c.mul(
        c.rat_one.clone(),
        c.mul(
            c.factor(&b, bfalse.clone(), a.clone()),
            c.factor(&b, bfalse.clone(), cc.clone()),
        ),
    );
    let high = c.mul(
        rho.clone(),
        c.mul(
            c.factor(&b, btrue.clone(), a.clone()),
            c.factor(&b, btrue.clone(), cc.clone()),
        ),
    );
    let lhs = c.add(low, high);

    // RHS: 1 + ρ·(pm(a)·pm(c))
    let pm_a = c.pm(a.clone());
    let pm_c = c.pm(cc.clone());
    let rhs = c.add(c.rat_one.clone(), c.mul(rho.clone(), c.mul(pm_a, pm_c)));

    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(cc_id, BinderInfo::Default, c.bool_.clone(), concl);
    let ty = b.mk_pi(a_id, BinderInfo::Default, c.bool_.clone(), ty);
    let ty = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), ty);
    b.finish(ty)
}

fn build_pair_sum_rho_value(c: &NoiseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (a_id, a) = b.fresh_local(c.bool_.clone());
    let (cc_id, cc) = b.fresh_local(c.bool_.clone());

    let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
    let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);

    // high term `ρ·(cf(true,a)·cf(true,c))`, def-eq to `ρ·(pm(a)·pm(c))`,
    // the (fixed) right summand of both goal sides.
    let high = c.mul(
        rho.clone(),
        c.mul(
            c.factor(&b, btrue.clone(), a.clone()),
            c.factor(&b, btrue.clone(), cc.clone()),
        ),
    );

    // `low_lhs := 1·(cf(false,a)·cf(false,c))`, def-eq to `Rat.mul 1 (Rat.mul 1 1)`.
    let low_lhs = c.mul(
        c.rat_one.clone(),
        c.mul(
            c.factor(&b, bfalse.clone(), a.clone()),
            c.factor(&b, bfalse.clone(), cc.clone()),
        ),
    );

    // inner_eq : Rat.mul Rat.one Rat.one = Rat.one   (Rat.one_mul Rat.one).
    let one_mul_one_inner = Expr::apps(
        Expr::const_(Name::from_string("Rat.one_mul"), vec![]),
        [c.rat_one.clone()],
    );
    let one_one = c.mul(c.rat_one.clone(), c.rat_one.clone());
    // step_a : Rat.mul 1 (1·1) = Rat.mul 1 1   (congr (Rat.mul 1 ·) inner_eq).
    let mul_left_one = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.mul(c.rat_one.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let one_times_oneone = c.mul(c.rat_one.clone(), one_one.clone());
    let step_a = c.congr_rat(
        one_one.clone(),
        c.rat_one.clone(),
        mul_left_one,
        one_mul_one_inner,
    );
    // step_b : Rat.mul 1 1 = Rat.one   (Rat.one_mul Rat.one).
    let step_b = Expr::apps(
        Expr::const_(Name::from_string("Rat.one_mul"), vec![]),
        [c.rat_one.clone()],
    );
    // low_to_one : Rat.mul 1 (1·1) = Rat.one  (def-eq to low_lhs = 1).
    let low_to_one = c.trans_rat(one_times_oneone, one_one, c.rat_one.clone(), step_a, step_b);

    // motive : fun (z : Rat) => Rat.add z high.
    let add_motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.add(z, high.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    // proof : Rat.add low_lhs high = Rat.add Rat.one high
    //   (both sides def-eq to goal sides: low_lhs ≡ 1·(1·1), high ≡ ρ·(pm a·pm c)).
    let proof = c.congr_rat(low_lhs, c.rat_one.clone(), add_motive, low_to_one);

    let val = b.mk_lam(cc_id, BinderInfo::Default, c.bool_.clone(), proof);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.bool_.clone(), val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.chi_factor_pair_sum_rho`: the ρ-weighted
    /// per-coordinate pair-sum collapse
    /// `1·(cf F a·cf F c) + ρ·(cf T a·cf T c) = 1 + ρ·(pm a·pm c)`.
    /// Kernel-checked, constructive (closure ⊆ {`Rat.one_mul`} ∪ Eq built-ins).
    /// Idempotent.
    pub(crate) fn register_chi_factor_pair_sum_rho_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_factor_pair_sum_rho");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.init_rat_arith()?;
        // `pm` is registered by `register_boolfn_embeddings` inside
        // `init_boolean_analysis`. Callers wire this theorem in after that.
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Re-check: the `init_boolean_analysis` pass (bonami/hc24 retirement)
        // registers this theorem transitively.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = NoiseConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_pair_sum_rho_type(&c),
            value: build_pair_sum_rho_value(&c),
        })
    }
}

// ===========================================================================
// popcount_succ_split — the popcount top-coordinate split (rung 3, sub-lemma a).
//
//   ∀ (n : Nat) (S : HCPoint (n+1)),
//     pc (n+1) S = Nat.add (pc n (restrict S)) (indNat (S (last n)))
//
// where `pc m S = Fin.sumNat m (fun i => indNat (S i))`. This is the
// `Fin.sumNat` ι-step instanced at the popcount integrand: `Fin.sumNat (n+1) g`
// ι-reduces (one `Nat.rec` step) to `Nat.add (Fin.sumNat n (g∘castSucc)) (g
// (last n))`, and `(fun i => indNat (S i)) ∘ castSucc` is β-equal to
// `fun i => indNat ((restrict S) i)` (since `restrict S = fun i => S (castSucc
// n i)`). So both sides are definitionally equal and the proof is a single
// `Eq.refl`. Kernel-checked, constructive (EMPTY admitted-axiom closure).
// ===========================================================================

fn build_popcount_split_type(c: &NoiseConsts) -> Expr {
    // ∀ (n : Nat) (S : HCPoint (n+1)),
    //   pc (n+1) S = Nat.add (pc n (restrict S)) (indNat (S (last n)))
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&n);
    let hcp = c.hcpoint_of(&sn);
    let (s_id, s) = b.fresh_local(hcp.clone());

    let lhs = c.popcount(&b, &sn, &s);
    let s_restrict = c.restrict(&b, &n, &s);
    let pc_restrict = c.popcount(&b, &n, &s_restrict);
    let ind_last = c.ind_nat(Expr::app(s.clone(), c.last(&n)));
    let rhs = c.nadd(&pc_restrict, &ind_last);

    let concl = c.eq_nat(lhs, rhs);
    let ty = b.mk_pi(s_id, BinderInfo::Default, hcp, concl);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    b.finish(ty)
}

fn build_popcount_split_value(c: &NoiseConsts) -> Expr {
    // fun (n : Nat) (S : HCPoint (n+1)) => @Eq.refl Nat (pc (n+1) S)
    // (LHS ι-reduces, then β-reduces, to the RHS; the kernel closes the refl.)
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&n);
    let hcp = c.hcpoint_of(&sn);
    let (s_id, s) = b.fresh_local(hcp.clone());

    let lhs = c.popcount(&b, &sn, &s);
    let proof = c.refl_nat(lhs);
    let val = b.mk_lam(s_id, BinderInfo::Default, hcp, proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.popcount_succ_split`: the popcount top-coordinate
    /// split `pc (n+1) S = pc n (restrict S) + indNat (S last)` (rung 3,
    /// sub-lemma a). The `Fin.sumNat` ι-step at the popcount integrand; single
    /// `Eq.refl`. Kernel-checked, constructive (EMPTY closure). Idempotent.
    pub(crate) fn register_popcount_succ_split_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.popcount_succ_split");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        // `Fin.sumNat`, `Fin.castSucc`, `Fin.last`, `HCPoint` from boolean analysis.
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Re-check: the `init_boolean_analysis` pass (bonami/hc24 retirement)
        // registers this theorem transitively.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = NoiseConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_popcount_split_type(&c),
            value: build_popcount_split_value(&c),
        })
    }
}

// ===========================================================================
// chi_bilinear_pair_combine_rho — the ρ-weighted per-index LOW+HIGH combine
// (rung 3, sub-lemma b; THE keystone's per-coordinate engine).
//
//   ∀ (ρ : Rat) (k : Nat) (x y : HCPoint (k+1)) (j : Fin (2^k)),
//     LOρ(j) + HIρ(j) = (W · P) · (1 + ρ·(pm(x last)·pm(y last)))
//
// where  W      = ρ^{pc k (hcDecode k j)}                 (the prefix ρ-weight),
//        P      = χ k (hcDecode k j) xr · χ k (hcDecode k j) yr,
//        LOρ(j) = ρ^{pc(k+1)(Slo)} · (χ(k+1)(Slo)x · χ(k+1)(Slo)y),
//        HIρ(j) = ρ^{pc(k+1)(Shi)} · (χ(k+1)(Shi)x · χ(k+1)(Shi)y),
//        Slo/Shi are the LOW/HIGH decoded subsets (top bit false/true),
//        xr = restrict x,  yr = restrict y.
//
// Each ρ-weighted half is shown `= (W·P)·(ρ_b·(cf_b·cf_b))` (ρ_b = 1 for LOW,
// ρ for HIGH) by combining two equations:
//   (weight) ρ^{pc(k+1)(S_half)} = W · ρ_b   — `popcount_succ_split` rewrites
//     the popcount over the top coordinate, the restrict/bit lemmas pin the
//     prefix popcount to `pc k (dec)` and the top bit to false/true, and
//     `powNat_add`/`powNat_zero`/`powNat_succ` collapse `ρ^{pc+ind}` to `W·ρ_b`;
//   (chi)    χ(k+1)(S_half)x·χ(k+1)(S_half)y = P · (cf_b·cf_b)   — the χ peel,
//     identical to the ρ=1 `chi_bilinear_pair_combine`'s half-eq.
// The two combine (congr into Rat.mul) to `(W·ρ_b)·(P·cf_b)`, then
// `Rat.mul_mul_mul_comm` regroups to `(W·P)·(ρ_b·cf_b)`. Summing the halves,
// `Rat.left_distrib` factors `W·P` out and `chi_factor_pair_sum_rho` collapses
// the `1·(cf_F·cf_F) + ρ·(cf_T·cf_T)` bracket to `1 + ρ·(pm·pm)`.
// Kernel-checked, constructive (closure ⊆ {popcount_succ_split, powNat_*,
// chi_pair_succ, chi_factor_pair_sum_rho, hcDecode/testBit split lemmas,
// Rat structural lemmas} ∪ Eq built-ins).
// ===========================================================================

/// Richer const set for the ρ-weighted per-index combine. Wraps `NoiseConsts`
/// plus the decode / restriction / testBit apparatus (mirrors `CombineConsts`).
struct CombineRhoConsts {
    c: NoiseConsts,
    nat_pow: Expr,
    nat_add_c: Expr,
    fin: Expr,
    fin_val: Expr,
    fin_islt: Expr,
    cast_add: Expr,
    add_nat: Expr,
    hc_decode: Expr,
    pow_two_succ: Expr,
    eq_symm_nat: Expr,
    eq_ndrec_fin: Expr,
    two: Expr,
    btrue: Expr,
    bfalse: Expr,
    congr_arg_br: Expr, // congrArg Bool→Rat
    congr_arg_hr: Expr, // congrArg HCPoint→Rat
    congr_arg_hn: Expr, // congrArg HCPoint→Nat (popcount congr over restrict eq)
    eq_trans_bool: Expr,
    restrict_lo: Expr,
    restrict_hi: Expr,
    decode_lo_bit: Expr,
    decode_hi_bit: Expr,
    testbit_lt_pow: Expr,
    testbit_add_self: Expr,
    testbit: Expr,
    chi_pair_succ: Expr,
    popcount_split: Expr,
    factor_pair_sum_rho: Expr,
    mmmc: Expr,
}

impl CombineRhoConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let z = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let s = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        Self {
            c: NoiseConsts::new(),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            nat_add_c: Expr::const_(Name::from_string("Nat.add"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            fin_val: Expr::const_(Name::from_string("Fin.val"), vec![]),
            fin_islt: Expr::const_(Name::from_string("Fin.isLt"), vec![]),
            cast_add: Expr::const_(Name::from_string("Fin.castAdd"), vec![]),
            add_nat: Expr::const_(Name::from_string("Fin.addNat"), vec![]),
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            pow_two_succ: Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]),
            eq_symm_nat: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_ndrec_fin: Expr::const_(Name::from_string("Eq.ndrec"), vec![l1.clone(), l1.clone()]),
            two: Expr::app(s.clone(), Expr::app(s, z)),
            btrue: Expr::const_(Name::from_string("Bool.true"), vec![]),
            bfalse: Expr::const_(Name::from_string("Bool.false"), vec![]),
            congr_arg_br: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            congr_arg_hr: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            congr_arg_hn: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            eq_trans_bool: Expr::const_(Name::from_string("Eq.trans"), vec![l1]),
            restrict_lo: Expr::const_(
                Name::from_string("BoolAnalysis.hcDecode_restrict_castAdd"),
                vec![],
            ),
            restrict_hi: Expr::const_(
                Name::from_string("BoolAnalysis.hcDecode_restrict_addNat"),
                vec![],
            ),
            decode_lo_bit: Expr::const_(
                Name::from_string("BoolAnalysis.hcDecode_castP_castAdd"),
                vec![],
            ),
            decode_hi_bit: Expr::const_(
                Name::from_string("BoolAnalysis.hcDecode_castP_addNat"),
                vec![],
            ),
            testbit_lt_pow: Expr::const_(Name::from_string("Nat.testBit_lt_pow"), vec![]),
            testbit_add_self: Expr::const_(
                Name::from_string("Nat.testBit_add_two_pow_self"),
                vec![],
            ),
            testbit: Expr::const_(Name::from_string("Nat.testBit"), vec![]),
            chi_pair_succ: Expr::const_(Name::from_string("BoolAnalysis.chi_pair_succ"), vec![]),
            popcount_split: Expr::const_(
                Name::from_string("BoolAnalysis.popcount_succ_split"),
                vec![],
            ),
            factor_pair_sum_rho: Expr::const_(
                Name::from_string("BoolAnalysis.chi_factor_pair_sum_rho"),
                vec![],
            ),
            mmmc: Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    fn nadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_add_c.clone(), [a, b])
    }
    fn succ(&self, n: &Expr) -> Expr {
        self.c.succ(n)
    }
    fn val(&self, n: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [n.clone(), i.clone()])
    }
    fn last(&self, n: &Expr) -> Expr {
        self.c.last(n)
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        self.c.hcpoint_of(n)
    }
    fn chi(&self, n: Expr, s: Expr, x: Expr) -> Expr {
        self.c.chi(n, s, x)
    }
    fn restrict(&self, parent: &EnvDeclBuilder, n: &Expr, p: &Expr) -> Expr {
        self.c.restrict(parent, n, p)
    }
    fn factor(&self, parent: &EnvDeclBuilder, sb: Expr, xb: Expr) -> Expr {
        self.c.factor(parent, sb, xb)
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.c.mul(a, b)
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        self.c.add(a, b)
    }
    fn pc(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr) -> Expr {
        self.c.popcount(parent, n, s)
    }
    fn pow(&self, rho: &Expr, k: &Expr) -> Expr {
        self.c.pow(rho, k)
    }
    fn rat(&self) -> Expr {
        self.c.rat.clone()
    }
    fn bool_(&self) -> Expr {
        self.c.bool_.clone()
    }
    fn nat(&self) -> Expr {
        self.c.nat.clone()
    }

    /// `castP n (idx_map (2^n) (2^n) j) : Fin (2^(n+1))`.
    fn cast_p(&self, parent: &EnvDeclBuilder, n: &Expr, idx_map: &Expr, j: &Expr) -> Expr {
        let p2n = self.pow2(n);
        let mapped = Expr::apps(idx_map.clone(), [p2n.clone(), p2n.clone(), j.clone()]);
        let sum_pow = self.nadd(p2n.clone(), p2n);
        let p2sn = self.pow2(&self.succ(n));
        let e_fwd = Expr::app(self.pow_two_succ.clone(), n.clone());
        let e = Expr::apps(
            self.eq_symm_nat.clone(),
            [self.nat(), p2sn.clone(), sum_pow.clone(), e_fwd],
        );
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (m_id, m) = mb.fresh_local(self.nat());
            mb.finish_child(mb.mk_lam(m_id, BinderInfo::Default, self.nat(), self.fin_of(&m)))
        };
        Expr::apps(
            self.eq_ndrec_fin.clone(),
            [self.nat(), sum_pow, motive, mapped, p2sn, e],
        )
    }
    /// `hcDecode (n+1) (castP n idx_map j) : HCPoint (n+1)`.
    fn decoded(&self, parent: &EnvDeclBuilder, n: &Expr, idx_map: &Expr, j: &Expr) -> Expr {
        let cp = self.cast_p(parent, n, idx_map, j);
        Expr::apps(self.hc_decode.clone(), [self.succ(n), cp])
    }
}

/// Build the ρ-weighted half equation
///   `ρ^{pc(k+1)(S_half)} · (χ(k+1)(S_half)x · χ(k+1)(S_half)y)
///       = (W · P) · (ρ_b · (cf_b x_last · cf_b y_last))`
/// where `W = ρ^{pc k (hcDecode k j)}`, `P = χ k dec xr · χ k dec yr`, and
/// `ρ_b = Rat.one` (LOW) / `ρ` (HIGH). Returns `(proof, w, p, rho_b, cf_pair)`.
#[allow(clippy::too_many_arguments)]
fn build_half_eq_rho(
    c: &CombineRhoConsts,
    b: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    x: &Expr,
    y: &Expr,
    j: &Expr,
    idx_map: &Expr,
    restrict_lemma: &Expr,
    decode_bit_lemma: &Expr,
    testbit_value_lemma: &Expr,
    bit_target: &Expr, // Bool.false | Bool.true
    bit_inner: &Expr,  // Nat the testBit reads
    rho_b: &Expr,      // Rat.one (LOW) | ρ (HIGH)  — defeq target of ρ^{indNat bit}
    bit_is_true: bool, // false → LOW, true → HIGH (selects the ρ^{ind} collapse)
) -> (Expr, Expr, Expr, Expr) {
    let sn = c.succ(n);
    let s_half = c.decoded(b, n, idx_map, j);
    let xr = c.restrict(b, n, x);
    let yr = c.restrict(b, n, y);
    let dec_n_j = Expr::apps(c.hc_decode.clone(), [n.clone(), j.clone()]);
    let r_half = c.restrict(b, n, &s_half);

    // ---- prefix bilinear P and weight W ----
    let p_x = c.chi(n.clone(), dec_n_j.clone(), xr.clone());
    let p_y = c.chi(n.clone(), dec_n_j.clone(), yr.clone());
    let p = c.mul(p_x.clone(), p_y.clone());
    let pc_dec = c.pc(b, n, &dec_n_j);
    let w = c.pow(rho, &pc_dec);

    let s_half_last = Expr::app(s_half.clone(), c.last(n));
    let x_last = Expr::app(x.clone(), c.last(n));
    let y_last = Expr::app(y.clone(), c.last(n));

    // ============================ chi peel (= ρ=1 build_half_eq) ============
    // chi_pair_succ n S_half x y :
    //   χ(n+1)S_half x · χ(n+1)S_half y
    //     = (χ n r_half xr · χ n r_half yr) · (cf(s_half_last,x_last)·cf(s_half_last,y_last))
    let chi_lhs = c.mul(
        c.chi(sn.clone(), s_half.clone(), x.clone()),
        c.chi(sn.clone(), s_half.clone(), y.clone()),
    );
    let chi_pre_x = c.chi(n.clone(), r_half.clone(), xr.clone());
    let chi_pre_y = c.chi(n.clone(), r_half.clone(), yr.clone());
    let pre = c.mul(chi_pre_x.clone(), chi_pre_y.clone());
    let cf_sx = c.factor(b, s_half_last.clone(), x_last.clone());
    let cf_sy = c.factor(b, s_half_last.clone(), y_last.clone());
    let cf_pair = c.mul(cf_sx.clone(), cf_sy.clone());
    let peeled = c.mul(pre.clone(), cf_pair.clone());
    let leg_peel = Expr::apps(
        c.chi_pair_succ.clone(),
        [n.clone(), s_half.clone(), x.clone(), y.clone()],
    );

    // restrict_eq : r_half = hcDecode n j.
    let restrict_eq = Expr::apps(restrict_lemma.clone(), [n.clone(), j.clone()]);

    // Rewrite the prefix χ·χ → P (two congr into Rat.mul, in the subset slot).
    let chi_fix_x = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (s_id, s) = d.fresh_local(c.hcpoint_of(n));
        let body = c.chi(n.clone(), s, xr.clone());
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, c.hcpoint_of(n), body))
    };
    let h_px = Expr::apps(
        c.congr_arg_hr.clone(),
        [
            c.hcpoint_of(n),
            c.rat(),
            r_half.clone(),
            dec_n_j.clone(),
            chi_fix_x,
            restrict_eq.clone(),
        ],
    );
    let chi_fix_y = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (s_id, s) = d.fresh_local(c.hcpoint_of(n));
        let body = c.chi(n.clone(), s, yr.clone());
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, c.hcpoint_of(n), body))
    };
    let h_py = Expr::apps(
        c.congr_arg_hr.clone(),
        [
            c.hcpoint_of(n),
            c.rat(),
            r_half.clone(),
            dec_n_j.clone(),
            chi_fix_y,
            restrict_eq.clone(),
        ],
    );
    let mul_right_pre_y = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.rat());
        let body = c.mul(z, chi_pre_y.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
    };
    let h_pre1 =
        c.c.congr_rat(chi_pre_x.clone(), p_x.clone(), mul_right_pre_y, h_px);
    let mul_left_px = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.rat());
        let body = c.mul(p_x.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
    };
    let h_pre2 =
        c.c.congr_rat(chi_pre_y.clone(), p_y.clone(), mul_left_px, h_py);
    let pre_mid = c.mul(p_x.clone(), chi_pre_y.clone());
    let h_pre =
        c.c.trans_rat(pre.clone(), pre_mid, p.clone(), h_pre1, h_pre2);

    // bit : s_half_last = bit_target.
    let bit_corr = Expr::apps(decode_bit_lemma.clone(), [n.clone(), j.clone(), c.last(n)]);
    let val_islt = Expr::apps(c.fin_islt.clone(), [c.pow2(n), j.clone()]);
    let val_j = c.val(&c.pow2(n), j);
    let bit_value = Expr::apps(
        testbit_value_lemma.clone(),
        [n.clone(), val_j.clone(), val_islt],
    );
    let testbit_n = Expr::apps(
        c.testbit.clone(),
        [bit_inner.clone(), c.val(&sn, &c.last(n))],
    );
    let bit = Expr::apps(
        c.eq_trans_bool.clone(),
        [
            c.bool_(),
            s_half_last.clone(),
            testbit_n,
            bit_target.clone(),
            bit_corr,
            bit_value,
        ],
    );

    // Rewrite cf pair → cf(bit_target,·)·cf(bit_target,·).
    let cf_tx = c.factor(b, bit_target.clone(), x_last.clone());
    let cf_ty = c.factor(b, bit_target.clone(), y_last.clone());
    let cf_motive_x = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (sb_id, sb) = d.fresh_local(c.bool_());
        let body = c.factor(&d, sb, x_last.clone());
        d.finish_child(d.mk_lam(sb_id, BinderInfo::Default, c.bool_(), body))
    };
    let h_cfx = Expr::apps(
        c.congr_arg_br.clone(),
        [
            c.bool_(),
            c.rat(),
            s_half_last.clone(),
            bit_target.clone(),
            cf_motive_x,
            bit.clone(),
        ],
    );
    let cf_motive_y = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (sb_id, sb) = d.fresh_local(c.bool_());
        let body = c.factor(&d, sb, y_last.clone());
        d.finish_child(d.mk_lam(sb_id, BinderInfo::Default, c.bool_(), body))
    };
    let h_cfy = Expr::apps(
        c.congr_arg_br.clone(),
        [
            c.bool_(),
            c.rat(),
            s_half_last.clone(),
            bit_target.clone(),
            cf_motive_y,
            bit.clone(),
        ],
    );
    let mul_right_cf_sy = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.rat());
        let body = c.mul(z, cf_sy.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
    };
    let h_cf1 =
        c.c.congr_rat(cf_sx.clone(), cf_tx.clone(), mul_right_cf_sy, h_cfx);
    let mul_left_cf_tx = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.rat());
        let body = c.mul(cf_tx.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
    };
    let h_cf2 =
        c.c.congr_rat(cf_sy.clone(), cf_ty.clone(), mul_left_cf_tx, h_cfy);
    let cf_mid = c.mul(cf_tx.clone(), cf_sy.clone());
    let cf_target = c.mul(cf_tx.clone(), cf_ty.clone());
    let h_cf =
        c.c.trans_rat(cf_pair.clone(), cf_mid, cf_target.clone(), h_cf1, h_cf2);

    // h_chi_body : peeled = P · cf_target.
    let mul_right_cf_pair = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.rat());
        let body = c.mul(z, cf_pair.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
    };
    let h_body1 =
        c.c.congr_rat(pre.clone(), p.clone(), mul_right_cf_pair, h_pre);
    let mul_left_p = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.rat());
        let body = c.mul(p.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
    };
    let h_body2 =
        c.c.congr_rat(cf_pair.clone(), cf_target.clone(), mul_left_p, h_cf);
    let body_mid = c.mul(p.clone(), cf_pair.clone());
    let chi_target = c.mul(p.clone(), cf_target.clone());
    let h_chi_body = c.c.trans_rat(
        peeled.clone(),
        body_mid,
        chi_target.clone(),
        h_body1,
        h_body2,
    );

    // h_chi : χ(n+1)S_half x·χ(n+1)S_half y = P · cf_target.
    let h_chi = c.c.trans_rat(
        chi_lhs.clone(),
        peeled,
        chi_target.clone(),
        leg_peel,
        h_chi_body,
    );

    // ============================ weight peel ===============================
    // popcount_succ_split n S_half :
    //   pc(n+1)(S_half) = Nat.add (pc n (restrict S_half)) (indNat (S_half last))
    let pc_sn = c.pc(b, &sn, &s_half);
    let pc_restrict = c.pc(b, n, &r_half);
    let ind_last = c.c.ind_nat(s_half_last.clone());
    let nat_split_rhs = c.nadd(pc_restrict.clone(), ind_last.clone());
    let leg_pcs = Expr::apps(c.popcount_split.clone(), [n.clone(), s_half.clone()]);

    // n1 : pc n (restrict S_half) = pc n (hcDecode n j)  (congr (pc n ·) restrict_eq).
    let pc_motive = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (s_id, s) = d.fresh_local(c.hcpoint_of(n));
        let body = c.pc(&d, n, &s);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, c.hcpoint_of(n), body))
    };
    let n1 = Expr::apps(
        c.congr_arg_hn.clone(),
        [
            c.hcpoint_of(n),
            c.nat(),
            r_half.clone(),
            dec_n_j.clone(),
            pc_motive,
            restrict_eq.clone(),
        ],
    );
    // n2 : indNat (S_half last) = indNat bit_target  (congr indNat bit).
    let ind_target = c.c.ind_nat(bit_target.clone());
    let ind_motive = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (bb_id, bb) = d.fresh_local(c.bool_());
        let body = c.c.ind_nat(bb);
        d.finish_child(d.mk_lam(bb_id, BinderInfo::Default, c.bool_(), body))
    };
    let n2 = Expr::apps(
        c.congr_arg_br.clone(),
        [
            c.bool_(),
            c.nat(),
            s_half_last.clone(),
            bit_target.clone(),
            ind_motive,
            bit.clone(),
        ],
    );
    // nat_add_eq : pc(restrict) + indNat(S_half last) = pc(dec) + indNat(bit_target).
    let add_right_ind = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.nat());
        let body = c.nadd(z, ind_last.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.nat(), body))
    };
    let na1 =
        c.c.congr_nat(pc_restrict.clone(), pc_dec.clone(), add_right_ind, n1);
    let add_left_pcdec = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.nat());
        let body = c.nadd(pc_dec.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.nat(), body))
    };
    let na2 =
        c.c.congr_nat(ind_last.clone(), ind_target.clone(), add_left_pcdec, n2);
    let nat_mid = c.nadd(pc_dec.clone(), ind_last.clone());
    let nat_target = c.nadd(pc_dec.clone(), ind_target.clone());
    let nat_add_eq =
        c.c.trans_nat(nat_split_rhs.clone(), nat_mid, nat_target.clone(), na1, na2);
    // nat_eq : pc(n+1)(S_half) = pc(dec) + indNat(bit_target).
    let nat_eq = c.c.trans_nat(
        pc_sn.clone(),
        nat_split_rhs,
        nat_target.clone(),
        leg_pcs,
        nat_add_eq,
    );

    // lift to ρ-power: ρ^{pc(n+1)(S_half)} = ρ^{pc(dec) + indNat(bit_target)}.
    let pow_motive = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (m_id, m) = d.fresh_local(c.nat());
        let body = c.pow(rho, &m);
        d.finish_child(d.mk_lam(m_id, BinderInfo::Default, c.nat(), body))
    };
    let w_half = c.pow(rho, &pc_sn);
    let pow_target = c.pow(rho, &nat_target);
    let hw1 =
        c.c.congr_nat_rat(pc_sn.clone(), nat_target.clone(), pow_motive, nat_eq);
    // powNat_add : ρ^{pc(dec)+ind} = ρ^{pc(dec)} · ρ^{ind} = W · ρ^{indNat bit_target}.
    //   indNat bit_target ι-reduces to 0 (LOW) / 1 (HIGH) defeq, so ρ^{ind} is
    //   defeq to ρ^0 / ρ^1; we further collapse ρ^{ind} = ρ_b below.
    let pow_ind = c.pow(rho, &ind_target);
    let w_times_powind = c.mul(w.clone(), pow_ind.clone());
    let hw2 = c.c.pow_add(rho, &pc_dec, &ind_target);
    // hw_ind : ρ^{indNat bit_target} = ρ_b.
    //   LOW : indNat false ≡ 0, ρ^0 = 1 = ρ_b  (powNat_zero).
    //   HIGH: indNat true ≡ 1, ρ^1 = ρ·ρ^0 = ρ·1 = ρ = ρ_b  (powNat_succ; mul_one).
    // We pass `rho_b` and the matching `hw_ind` proof from the caller-agnostic
    // path: build it from bit_target structurally.
    let hw_ind = build_pow_ind_eq(c, b, rho, bit_is_true, rho_b, &ind_target);
    let mul_left_w = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.rat());
        let body = c.mul(w.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
    };
    let w_rho_b = c.mul(w.clone(), rho_b.clone());
    let hw3 =
        c.c.congr_rat(pow_ind.clone(), rho_b.clone(), mul_left_w, hw_ind);
    // hw : ρ^{pc(n+1)(S_half)} = W · ρ_b.
    let tw1 =
        c.c.trans_rat(w_half.clone(), pow_target, w_times_powind.clone(), hw1, hw2);
    let hw =
        c.c.trans_rat(w_half.clone(), w_times_powind, w_rho_b.clone(), tw1, hw3);

    // ============================ combine weight × chi ======================
    // LOρ = ρ^{pc(n+1)(S_half)} · (χ·χ).
    let lo_rho = c.mul(w_half.clone(), chi_lhs.clone());
    // step_w : LOρ = (W·ρ_b) · (χ·χ)   (congr (·χχ) hw).
    let mul_right_chi = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.rat());
        let body = c.mul(z, chi_lhs.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
    };
    let wrb_chi = c.mul(w_rho_b.clone(), chi_lhs.clone());
    let step_w =
        c.c.congr_rat(w_half.clone(), w_rho_b.clone(), mul_right_chi, hw);
    // step_chi : (W·ρ_b)·(χ·χ) = (W·ρ_b)·(P·cf_target)   (congr ((W·ρ_b)·) h_chi).
    let mul_left_wrb = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.rat());
        let body = c.mul(w_rho_b.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
    };
    let wrb_pcf = c.mul(w_rho_b.clone(), chi_target.clone());
    let step_chi =
        c.c.congr_rat(chi_lhs.clone(), chi_target.clone(), mul_left_wrb, h_chi);
    // step_mmmc : (W·ρ_b)·(P·cf_target) = (W·P)·(ρ_b·cf_target)
    //   Rat.mul_mul_mul_comm W ρ_b P cf_target.
    let wp = c.mul(w.clone(), p.clone());
    let rb_cf = c.mul(rho_b.clone(), cf_target.clone());
    let final_target = c.mul(wp.clone(), rb_cf.clone());
    let step_mmmc = Expr::apps(
        c.mmmc.clone(),
        [w.clone(), rho_b.clone(), p.clone(), cf_target.clone()],
    );

    // Chain: LOρ = (W·ρ_b)·(χχ) = (W·ρ_b)·(P·cf) = (W·P)·(ρ_b·cf).
    let t1 =
        c.c.trans_rat(lo_rho.clone(), wrb_chi, wrb_pcf.clone(), step_w, step_chi);
    let proof = c.c.trans_rat(lo_rho, wrb_pcf, final_target, t1, step_mmmc);

    (proof, w, p, cf_target)
}

/// `ρ^{indNat bit_target} = ρ_b` where `bit_target` is a literal `Bool.false`
/// (→ ρ_b = `Rat.one`) or `Bool.true` (→ ρ_b = ρ). The `indNat` ι-reduces, so
/// the proof is `powNat_zero ρ` (LOW) or a `powNat_succ`/`mul_one` chain (HIGH).
fn build_pow_ind_eq(
    c: &CombineRhoConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    bit_is_true: bool,
    rho_b: &Expr,
    ind_target: &Expr,
) -> Expr {
    let pow_ind = c.pow(rho, ind_target);
    if bit_is_true {
        // ρ^{indNat true} ≡ ρ^1 = ρ·ρ^0 (powNat_succ ρ 0); ρ^0 = 1 (powNat_zero);
        // ρ·ρ^0 = ρ·1 (congr (ρ·) pow_zero); ρ·1 = ρ (mul_one ρ).  ρ_b = ρ.
        let pow_zero_e = c.pow(rho, &c.c.nat_zero);
        let rho_pow0 = c.mul(rho.clone(), pow_zero_e.clone());
        let succ_eq = c.c.pow_succ(rho, &c.c.nat_zero); // ρ^1 = ρ·ρ^0
        let pz = c.c.pow_zero(rho); // ρ^0 = 1
        let mul_left_rho = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(c.rat());
            let body = c.mul(rho.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
        };
        let rho_one = c.mul(rho.clone(), c.c.rat_one.clone());
        let congr_pz =
            c.c.congr_rat(pow_zero_e, c.c.rat_one.clone(), mul_left_rho, pz);
        let mo = c.c.mul_one(rho.clone()); // ρ·1 = ρ
                                           // chain: ρ^1 = ρ·ρ^0 = ρ·1 = ρ.
        let t1 =
            c.c.trans_rat(pow_ind, rho_pow0, rho_one.clone(), succ_eq, congr_pz);
        c.c.trans_rat(c.pow(rho, ind_target), rho_one, rho_b.clone(), t1, mo)
    } else {
        // ρ^{indNat false} ≡ ρ^0 = 1 = ρ_b  (powNat_zero).
        c.c.pow_zero(rho)
    }
}

fn build_combine_rho_type(c: &CombineRhoConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat());
    let (n_id, n) = b.fresh_local(c.nat());
    let sn = c.succ(&n);
    let hcp = c.hcpoint_of(&sn);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (y_id, y) = b.fresh_local(hcp.clone());
    let p2n = c.pow2(&n);
    let (j_id, j) = b.fresh_local(c.fin_of(&p2n));

    // LOρ + HIρ.
    let s_lo = c.decoded(&b, &n, &c.cast_add, &j);
    let s_hi = c.decoded(&b, &n, &c.add_nat, &j);
    let chi_lo = c.mul(
        c.chi(sn.clone(), s_lo.clone(), x.clone()),
        c.chi(sn.clone(), s_lo.clone(), y.clone()),
    );
    let chi_hi = c.mul(
        c.chi(sn.clone(), s_hi.clone(), x.clone()),
        c.chi(sn.clone(), s_hi.clone(), y.clone()),
    );
    let w_lo = c.pow(&rho, &c.pc(&b, &sn, &s_lo));
    let w_hi = c.pow(&rho, &c.pc(&b, &sn, &s_hi));
    let lo_rho = c.mul(w_lo, chi_lo);
    let hi_rho = c.mul(w_hi, chi_hi);
    let lhs = c.add(lo_rho, hi_rho);

    // (W·P)·(1 + ρ·(pm x_last · pm y_last)).
    let dec_n_j = Expr::apps(c.hc_decode.clone(), [n.clone(), j.clone()]);
    let xr = c.restrict(&b, &n, &x);
    let yr = c.restrict(&b, &n, &y);
    let p = c.mul(
        c.chi(n.clone(), dec_n_j.clone(), xr),
        c.chi(n.clone(), dec_n_j.clone(), yr),
    );
    let w = c.pow(&rho, &c.pc(&b, &n, &dec_n_j));
    let wp = c.mul(w, p);
    let x_last = Expr::app(x.clone(), c.last(&n));
    let y_last = Expr::app(y.clone(), c.last(&n));
    let pm_x = c.c.pm(x_last);
    let pm_y = c.c.pm(y_last);
    let pair = c.add(c.c.rat_one.clone(), c.mul(rho.clone(), c.mul(pm_x, pm_y)));
    let rhs = c.mul(wp, pair);

    let concl = c.c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(j_id, BinderInfo::Default, c.fin_of(&p2n), concl);
    let ty = b.mk_pi(y_id, BinderInfo::Default, hcp.clone(), ty);
    let ty = b.mk_pi(x_id, BinderInfo::Default, hcp, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat(), ty);
    let ty = b.mk_pi(rho_id, BinderInfo::Default, c.rat(), ty);
    b.finish(ty)
}

fn build_combine_rho_value(c: &CombineRhoConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat());
    let (n_id, n) = b.fresh_local(c.nat());
    let sn = c.succ(&n);
    let hcp = c.hcpoint_of(&sn);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (y_id, y) = b.fresh_local(hcp.clone());
    let p2n = c.pow2(&n);
    let (j_id, j) = b.fresh_local(c.fin_of(&p2n));

    let val_j = c.val(&p2n, &j);
    let bit_inner_lo = val_j.clone();
    let bit_inner_hi = c.nadd(p2n.clone(), val_j);

    // LOW half: LOρ = (W·P)·(1·(cf_F·cf_F)).
    let (h_lo, w, p, cf_f) = build_half_eq_rho(
        c,
        &b,
        &rho,
        &n,
        &x,
        &y,
        &j,
        &c.cast_add,
        &c.restrict_lo,
        &c.decode_lo_bit,
        &c.testbit_lt_pow,
        &c.bfalse,
        &bit_inner_lo,
        &c.c.rat_one.clone(),
        false,
    );
    // HIGH half: HIρ = (W·P)·(ρ·(cf_T·cf_T)).
    let (h_hi, _w2, _p2, cf_t) = build_half_eq_rho(
        c,
        &b,
        &rho,
        &n,
        &x,
        &y,
        &j,
        &c.add_nat,
        &c.restrict_hi,
        &c.decode_hi_bit,
        &c.testbit_add_self,
        &c.btrue,
        &bit_inner_hi,
        &rho,
        true,
    );

    // LOρ + HIρ terms (the goal LHS).
    let s_lo = c.decoded(&b, &n, &c.cast_add, &j);
    let s_hi = c.decoded(&b, &n, &c.add_nat, &j);
    let chi_lo = c.mul(
        c.chi(sn.clone(), s_lo.clone(), x.clone()),
        c.chi(sn.clone(), s_lo.clone(), y.clone()),
    );
    let chi_hi = c.mul(
        c.chi(sn.clone(), s_hi.clone(), x.clone()),
        c.chi(sn.clone(), s_hi.clone(), y.clone()),
    );
    let w_lo = c.pow(&rho, &c.pc(&b, &sn, &s_lo));
    let w_hi = c.pow(&rho, &c.pc(&b, &sn, &s_hi));
    let lo_rho = c.mul(w_lo, chi_lo);
    let hi_rho = c.mul(w_hi, chi_hi);
    let lhs = c.add(lo_rho.clone(), hi_rho.clone());

    let wp = c.mul(w.clone(), p.clone());
    // ρ_b · cf_b targets.
    let one_cf_f = c.mul(c.c.rat_one.clone(), cf_f.clone());
    let rho_cf_t = c.mul(rho.clone(), cf_t.clone());
    let target_lo = c.mul(wp.clone(), one_cf_f.clone());
    let target_hi = c.mul(wp.clone(), rho_cf_t.clone());

    // step1 : LOρ + HIρ = (WP·1cfF) + (WP·ρcfT)  (congr both summands).
    let add_right_hi = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat());
        let body = c.add(z, hi_rho.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
    };
    let s1a =
        c.c.congr_rat(lo_rho.clone(), target_lo.clone(), add_right_hi, h_lo);
    let add_left_tlo = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat());
        let body = c.add(target_lo.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
    };
    let s1b =
        c.c.congr_rat(hi_rho.clone(), target_hi.clone(), add_left_tlo, h_hi);
    let add_mid = c.add(target_lo.clone(), hi_rho.clone());
    let add_targets = c.add(target_lo.clone(), target_hi.clone());
    let step1 =
        c.c.trans_rat(lhs.clone(), add_mid, add_targets.clone(), s1a, s1b);

    // step2 : (WP·1cfF) + (WP·ρcfT) = WP·(1cfF + ρcfT)  (Eq.symm left_distrib).
    let distrib =
        c.c.left_distrib(wp.clone(), one_cf_f.clone(), rho_cf_t.clone());
    let cf_sum = c.add(one_cf_f.clone(), rho_cf_t.clone());
    let wp_sum = c.mul(wp.clone(), cf_sum.clone());
    let step2 =
        c.c.eq_symm_rat(wp_sum.clone(), add_targets.clone(), distrib);

    // step3 : WP·(1cfF + ρcfT) = WP·(1 + ρ·(pm·pm))
    //   congr (WP·) (chi_factor_pair_sum_rho ρ x_last y_last).
    let x_last = Expr::app(x.clone(), c.last(&n));
    let y_last = Expr::app(y.clone(), c.last(&n));
    let pair_sum = Expr::apps(
        c.factor_pair_sum_rho.clone(),
        [rho.clone(), x_last.clone(), y_last.clone()],
    );
    let pm_x = c.c.pm(x_last);
    let pm_y = c.c.pm(y_last);
    let pair_rhs = c.add(c.c.rat_one.clone(), c.mul(rho.clone(), c.mul(pm_x, pm_y)));
    let mul_left_wp = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat());
        let body = c.mul(wp.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
    };
    let step3 =
        c.c.congr_rat(cf_sum, pair_rhs.clone(), mul_left_wp, pair_sum);
    let final_rhs = c.mul(wp.clone(), pair_rhs);

    // Chain: lhs = add_targets = wp_sum = final_rhs.
    let t1 =
        c.c.trans_rat(lhs.clone(), add_targets, wp_sum.clone(), step1, step2);
    let proof = c.c.trans_rat(lhs, wp_sum, final_rhs, t1, step3);

    let val = b.mk_lam(j_id, BinderInfo::Default, c.fin_of(&p2n), proof);
    let val = b.mk_lam(y_id, BinderInfo::Default, hcp.clone(), val);
    let val = b.mk_lam(x_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat(), val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.chi_bilinear_pair_combine_rho`: the ρ-weighted
    /// per-index LOW+HIGH combine (rung 3, sub-lemma b). Kernel-checked,
    /// constructive. Idempotent.
    pub(crate) fn register_chi_bilinear_pair_combine_rho_theorem(
        &mut self,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_bilinear_pair_combine_rho");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.init_rat_arith()?;
        // ρ-power apparatus + popcount split + the ρ-pair-sum collapse.
        self.register_rat_pow_nat_zero_theorem()?;
        self.register_rat_pow_nat_succ_theorem()?;
        self.register_rat_pow_nat_add_theorem()?;
        self.register_popcount_succ_split_theorem()?;
        self.register_chi_factor_pair_sum_rho_theorem()?;
        // χ peel + Rat structural regroup.
        self.register_chi_pair_succ_theorem()?;
        self.register_rat_mul_mul_mul_comm_theorem()?;
        // Rat.mul_one / mul_comm / mul_assoc / left_distrib (quotient structural).
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?;
        }
        // restriction / decode-bit / testBit / hcDecode / isLt split lemmas.
        self.register_hc_decode_split_theorems()?;
        // Re-check: the dep chain may run the `init_boolean_analysis` pass,
        // whose hc24 retirement chain registers this theorem transitively.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = CombineRhoConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_combine_rho_type(&c),
            value: build_combine_rho_value(&c),
        })
    }
}

// ===========================================================================
// subsetSum_chi_bilinear_rho — THE ρ-weighted bilinear-collapse keystone
// (rung 3, sub-lemma c; the induction assembly).
//
//   ∀ (ρ : Rat) (n : Nat) (x y : HCPoint n),
//     subsetSum n (fun S => ρ^{pc n S} · (χ n S x · χ n S y))
//       = Fin.prod n (fun i => 1 + ρ·(pm(x i)·pm(y i)))
//
// `Nat.rec` on `n`, ρ riding through. Base `subsetSum_chi_bilinear_zero_rho`.
// Step mirrors the ρ=1 `subsetSum_chi_bilinear` leg-for-leg:
//   A `subsetSum_split`     ss_lhsρ(k+1) = Σ LOρ + Σ HIρ
//   B Eq.symm `Fin.sum_add` Σ LOρ + Σ HIρ = Σ (LOρ+HIρ)
//   C `Fin.sum_congr`       Σ (LOρ+HIρ) = Σ (c_top · prefixρ)   [combineρ + mul_comm]
//   D `Fin.sum_smul`        Σ (c_top·prefixρ) = c_top · Σ prefixρ
//   E congr+IH              c_top · Σ prefixρ = c_top · Fin.prod k   [Σ prefixρ ≡ subsetSum k]
//   F `Rat.mul_comm`        c_top · Fin.prod k = Fin.prod k · c_top
//   G Eq.symm `Fin.prod_succ`  Fin.prod k · c_top = Fin.prod (k+1)
// The only ρ-specific change is the "prefix" now carries the per-subset ρ-weight
// `ρ^{pc k (decode k j)}` (so `Σ prefixρ ≡ subsetSum k (ss_intρ k xr yr)`), while
// the scalar `c_top = 1 + ρ·pm·pm` is still constant in `j` and factors out by
// `Fin.sum_smul`. Kernel-checked, constructive (closure ⊆ {subsetSum_split,
// chi_bilinear_pair_combine_rho, Fin.sum_*, Fin.prod_succ, Rat.mul_comm} ∪ Eq).
// ===========================================================================

/// Const set for the inductive ρ-delta (mirrors `DeltaIndConsts`).
struct DeltaIndRhoConsts {
    c: NoiseConsts,
    fin: Expr,
    nat_pow: Expr,
    fin_sum: Expr,
    #[cfg(test)]
    fin_prod: Expr,
    #[cfg(test)]
    subset_sum: Expr,
    cast_add: Expr,
    add_nat: Expr,
    hc_decode: Expr,
    nat_rec: Expr,
    subset_sum_split: Expr,
    sum_add: Expr,
    sum_smul: Expr,
    sum_congr: Expr,
    prod_succ: Expr,
    combine_rho: Expr,
    base_zero_rho: Expr,
    two: Expr,
    nat_add_c: Expr,
    pow_two_succ: Expr,
    eq_symm_nat: Expr,
    eq_ndrec_fin: Expr,
}

impl DeltaIndRhoConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let z = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let s = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        Self {
            c: NoiseConsts::new(),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            #[cfg(test)]
            fin_prod: Expr::const_(Name::from_string("Fin.prod"), vec![]),
            #[cfg(test)]
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            cast_add: Expr::const_(Name::from_string("Fin.castAdd"), vec![]),
            add_nat: Expr::const_(Name::from_string("Fin.addNat"), vec![]),
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            subset_sum_split: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_split"),
                vec![],
            ),
            sum_add: Expr::const_(Name::from_string("Fin.sum_add"), vec![]),
            sum_smul: Expr::const_(Name::from_string("Fin.sum_smul"), vec![]),
            sum_congr: Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
            prod_succ: Expr::const_(Name::from_string("Fin.prod_succ"), vec![]),
            combine_rho: Expr::const_(
                Name::from_string("BoolAnalysis.chi_bilinear_pair_combine_rho"),
                vec![],
            ),
            base_zero_rho: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_chi_bilinear_zero_rho"),
                vec![],
            ),
            two: Expr::app(s.clone(), Expr::app(s, z)),
            nat_add_c: Expr::const_(Name::from_string("Nat.add"), vec![]),
            pow_two_succ: Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]),
            eq_symm_nat: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_ndrec_fin: Expr::const_(Name::from_string("Eq.ndrec"), vec![l1.clone(), l1]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    fn succ(&self, n: &Expr) -> Expr {
        self.c.succ(n)
    }
    fn nadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_add_c.clone(), [a, b])
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        self.c.hcpoint_of(n)
    }
    fn last(&self, n: &Expr) -> Expr {
        self.c.last(n)
    }
    fn chi(&self, n: Expr, s: Expr, x: Expr) -> Expr {
        self.c.chi(n, s, x)
    }
    fn restrict(&self, parent: &EnvDeclBuilder, n: &Expr, p: &Expr) -> Expr {
        self.c.restrict(parent, n, p)
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.c.mul(a, b)
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        self.c.add(a, b)
    }
    fn pow(&self, rho: &Expr, k: &Expr) -> Expr {
        self.c.pow(rho, k)
    }
    fn pc(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr) -> Expr {
        self.c.popcount(parent, n, s)
    }
    fn rat(&self) -> Expr {
        self.c.rat.clone()
    }
    fn nat(&self) -> Expr {
        self.c.nat.clone()
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        self.c.eq_rat(l, r)
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        self.c.trans_rat(a, b, cc, h1, h2)
    }
    fn congr_rat(&self, from: Expr, to: Expr, motive: Expr, h: Expr) -> Expr {
        self.c.congr_rat(from, to, motive, h)
    }
    fn eq_symm_rat(&self, l: Expr, r: Expr, h: Expr) -> Expr {
        self.c.eq_symm_rat(l, r, h)
    }
    fn fsum(&self, n: Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n, f])
    }
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        self.c.mul_comm(a, b)
    }

    fn ss_lhs_rho(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        x: &Expr,
        y: &Expr,
    ) -> Expr {
        self.c.ss_lhs_rho(parent, rho, n, x, y)
    }
    fn prod_int_rho(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        x: &Expr,
        y: &Expr,
    ) -> Expr {
        self.c.prod_int_rho(parent, rho, n, x, y)
    }
    fn prod_rhs_rho(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        x: &Expr,
        y: &Expr,
    ) -> Expr {
        self.c.prod_rhs_rho(parent, rho, n, x, y)
    }

    /// `castP n (idx_map (2^n) (2^n) j) : Fin (2^(n+1))`.
    fn cast_p(&self, parent: &EnvDeclBuilder, n: &Expr, idx_map: &Expr, j: &Expr) -> Expr {
        let p2n = self.pow2(n);
        let mapped = Expr::apps(idx_map.clone(), [p2n.clone(), p2n.clone(), j.clone()]);
        let sum_pow = self.nadd(p2n.clone(), p2n);
        let p2sn = self.pow2(&self.succ(n));
        let e_fwd = Expr::app(self.pow_two_succ.clone(), n.clone());
        let e = Expr::apps(
            self.eq_symm_nat.clone(),
            [self.nat(), p2sn.clone(), sum_pow.clone(), e_fwd],
        );
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (m_id, m) = mb.fresh_local(self.nat());
            mb.finish_child(mb.mk_lam(m_id, BinderInfo::Default, self.nat(), self.fin_of(&m)))
        };
        Expr::apps(
            self.eq_ndrec_fin.clone(),
            [self.nat(), sum_pow, motive, mapped, p2sn, e],
        )
    }
    /// `fun (j : Fin (2^n)) => ρ^{pc(n+1)(Shalf j)} · (χ(n+1)(Shalf)x·χ(n+1)(Shalf)y)`
    /// — the ρ-weighted cube-split half integrand `subsetSum_split` produces
    /// (`ss_intρ (n+1) x y` applied to the decoded half subset).
    fn half_int_rho(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        x: &Expr,
        y: &Expr,
        idx_map: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let p2n = self.pow2(n);
        let sn = self.succ(n);
        let (j_id, j) = b.fresh_local(self.fin_of(&p2n));
        let cp = self.cast_p(&b, n, idx_map, &j);
        let s_half = Expr::apps(self.hc_decode.clone(), [sn.clone(), cp]);
        let weight = self.pow(rho, &self.pc(&b, &sn, &s_half));
        let chis = self.mul(
            self.chi(sn.clone(), s_half.clone(), x.clone()),
            self.chi(sn.clone(), s_half, y.clone()),
        );
        let body = self.mul(weight, chis);
        b.finish_child(b.mk_lam(j_id, BinderInfo::Default, self.fin_of(&p2n), body))
    }
    /// `fun (j : Fin (2^n)) => ρ^{pc n (hcDecode n j)} · (χ n dec xr · χ n dec yr)`
    /// — the ρ-weighted prefix integrand, def-eq to `ss_intρ n xr yr ∘ hcDecode n`
    /// (i.e. to the summand of `subsetSum n (ss_intρ n xr yr)`).
    fn prefix_int_rho(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        xr: &Expr,
        yr: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let p2n = self.pow2(n);
        let (j_id, j) = b.fresh_local(self.fin_of(&p2n));
        let dec = Expr::apps(self.hc_decode.clone(), [n.clone(), j.clone()]);
        let weight = self.pow(rho, &self.pc(&b, n, &dec));
        let chis = self.mul(
            self.chi(n.clone(), dec.clone(), xr.clone()),
            self.chi(n.clone(), dec, yr.clone()),
        );
        let body = self.mul(weight, chis);
        b.finish_child(b.mk_lam(j_id, BinderInfo::Default, self.fin_of(&p2n), body))
    }
    /// `fun (j : Fin (2^n)) => c · prefixρ(j)` — the scaled integrand for Fin.sum_smul.
    fn scaled_int_rho(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        xr: &Expr,
        yr: &Expr,
        cc: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let p2n = self.pow2(n);
        let (j_id, j) = b.fresh_local(self.fin_of(&p2n));
        let dec = Expr::apps(self.hc_decode.clone(), [n.clone(), j.clone()]);
        let weight = self.pow(rho, &self.pc(&b, n, &dec));
        let chis = self.mul(
            self.chi(n.clone(), dec.clone(), xr.clone()),
            self.chi(n.clone(), dec, yr.clone()),
        );
        let pre = self.mul(weight, chis);
        let body = self.mul(cc.clone(), pre);
        b.finish_child(b.mk_lam(j_id, BinderInfo::Default, self.fin_of(&p2n), body))
    }
}

fn build_ind_rho_step(c: &DeltaIndRhoConsts, rho: &Expr, parent: &EnvDeclBuilder) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = b.fresh_local(c.nat());
    let sn = c.succ(&k);

    // ih : ∀ x y : HCPoint k, ss_lhsρ k = prod_rhsρ k
    let ih_ty = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&k);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let (y_id, y) = d.fresh_local(hcp.clone());
        let lhs = c.ss_lhs_rho(&d, rho, &k, &x, &y);
        let rhs = c.prod_rhs_rho(&d, rho, &k, &x, &y);
        let concl = c.eq_rat(lhs, rhs);
        let t = d.mk_pi(y_id, BinderInfo::Default, hcp.clone(), concl);
        d.finish_child(d.mk_pi(x_id, BinderInfo::Default, hcp, t))
    };
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());

    let hcp_sn = c.hcpoint_of(&sn);
    let (x_id, x) = b.fresh_local(hcp_sn.clone());
    let (y_id, y) = b.fresh_local(hcp_sn.clone());

    let p2k = c.pow2(&k);
    let xr = c.restrict(&b, &k, &x);
    let yr = c.restrict(&b, &k, &y);
    // c_top := 1 + ρ·(pm(x last)·pm(y last))
    let x_last = Expr::app(x.clone(), c.last(&k));
    let y_last = Expr::app(y.clone(), c.last(&k));
    let c_top = c.add(
        c.c.rat_one.clone(),
        c.mul(rho.clone(), c.mul(c.c.pm(x_last), c.c.pm(y_last))),
    );

    // Σ LOρ, Σ HIρ.
    let lo_int = c.half_int_rho(&b, rho, &k, &x, &y, &c.cast_add);
    let hi_int = c.half_int_rho(&b, rho, &k, &x, &y, &c.add_nat);
    let sum_lo = c.fsum(p2k.clone(), lo_int.clone());
    let sum_hi = c.fsum(p2k.clone(), hi_int.clone());
    let split_rhs = c.add(sum_lo.clone(), sum_hi.clone());

    // ss_lhsρ(k+1).
    let ss_lhs_sn = c.ss_lhs_rho(&b, rho, &sn, &x, &y);

    // A : ss_lhsρ(k+1) = Σ LOρ + Σ HIρ   (subsetSum_split k (ss_intρ (k+1) x y)).
    let g_sn = c.c.ss_int_rho(&b, rho, &sn, &x, &y);
    let leg_a = Expr::apps(c.subset_sum_split.clone(), [k.clone(), g_sn]);

    // pair_int : fun j => LOρ(j) + HIρ(j).
    let pair_int = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = d.fresh_local(c.fin_of(&p2k));
        let body = c.add(
            Expr::app(lo_int.clone(), j.clone()),
            Expr::app(hi_int.clone(), j.clone()),
        );
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, c.fin_of(&p2k), body))
    };
    let sum_pair = c.fsum(p2k.clone(), pair_int.clone());

    // B : Σ LOρ + Σ HIρ = Σ (LOρ+HIρ)   (Eq.symm (Fin.sum_add (2^k) lo hi)).
    let sum_add_fwd = Expr::apps(
        c.sum_add.clone(),
        [p2k.clone(), lo_int.clone(), hi_int.clone()],
    );
    let leg_b = c.eq_symm_rat(sum_pair.clone(), split_rhs.clone(), sum_add_fwd);

    // scaled_int : fun j => c_top · prefixρ(j).
    let scaled_int = c.scaled_int_rho(&b, rho, &k, &xr, &yr, &c_top);
    let sum_scaled = c.fsum(p2k.clone(), scaled_int.clone());

    // C : Σ (LOρ+HIρ) = Σ (c_top · prefixρ)   (Fin.sum_congr + per-index).
    let pointwise = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = d.fresh_local(c.fin_of(&p2k));
        // combineρ ρ k x y j : LOρ(j)+HIρ(j) = (W·P)·c_top.
        let combine_j = Expr::apps(
            c.combine_rho.clone(),
            [rho.clone(), k.clone(), x.clone(), y.clone(), j.clone()],
        );
        let dec = Expr::apps(c.hc_decode.clone(), [k.clone(), j.clone()]);
        let weight = c.pow(rho, &c.pc(&d, &k, &dec));
        let prefix_j = c.mul(
            c.chi(k.clone(), dec.clone(), xr.clone()),
            c.chi(k.clone(), dec, yr.clone()),
        );
        let wp = c.mul(weight, prefix_j); // = prefixρ(j)  (def-eq)
        let lo_j = Expr::app(lo_int.clone(), j.clone());
        let hi_j = Expr::app(hi_int.clone(), j.clone());
        let pair_j = c.add(lo_j, hi_j);
        let wp_top = c.mul(wp.clone(), c_top.clone());
        let top_wp = c.mul(c_top.clone(), wp.clone());
        // mul_comm (W·P) c_top : (W·P)·c_top = c_top·(W·P) = c_top·prefixρ(j).
        let comm = c.mul_comm(wp.clone(), c_top.clone());
        let proof_j = c.trans_rat(pair_j, wp_top, top_wp, combine_j, comm);
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, c.fin_of(&p2k), proof_j))
    };
    let leg_c = Expr::apps(
        c.sum_congr.clone(),
        [p2k.clone(), pair_int.clone(), scaled_int.clone(), pointwise],
    );

    // D : Σ (c_top·prefixρ) = c_top · Σ prefixρ   (Fin.sum_smul (2^k) c_top prefixρ).
    let prefix_int = c.prefix_int_rho(&b, rho, &k, &xr, &yr);
    let sum_prefix = c.fsum(p2k.clone(), prefix_int.clone());
    let c_sum_prefix = c.mul(c_top.clone(), sum_prefix.clone());
    let leg_d = Expr::apps(
        c.sum_smul.clone(),
        [p2k.clone(), c_top.clone(), prefix_int.clone()],
    );

    // Σ prefixρ ≡ subsetSum k (ss_intρ k xr yr)  (def-eq); IH gives = Fin.prod k.
    let ss_k = c.ss_lhs_rho(&b, rho, &k, &xr, &yr);
    let prod_k = c.prod_rhs_rho(&b, rho, &k, &xr, &yr);
    // E : c_top · subsetSum k = c_top · Fin.prod k   (congr (c_top ·) (ih xr yr)).
    let ih_xy = Expr::apps(ih.clone(), [xr.clone(), yr.clone()]);
    let mul_left_ctop = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat());
        let body = c.mul(c_top.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
    };
    let c_prod_k = c.mul(c_top.clone(), prod_k.clone());
    let leg_e = c.congr_rat(ss_k.clone(), prod_k.clone(), mul_left_ctop, ih_xy);

    // F : c_top · Fin.prod k = Fin.prod k · c_top   (mul_comm).
    let prod_c = c.mul(prod_k.clone(), c_top.clone());
    let leg_f = c.mul_comm(c_top.clone(), prod_k.clone());

    // G : Fin.prod k · c_top = Fin.prod (k+1)   (Eq.symm (Fin.prod_succ k (prod_intρ(k+1)x y))).
    let prod_int_sn = c.prod_int_rho(&b, rho, &sn, &x, &y);
    let prod_succ_fwd = Expr::apps(c.prod_succ.clone(), [k.clone(), prod_int_sn]);
    let prod_rhs_sn = c.prod_rhs_rho(&b, rho, &sn, &x, &y);
    let leg_g = c.eq_symm_rat(prod_rhs_sn.clone(), prod_c.clone(), prod_succ_fwd);

    // Chain.
    let t1 = c.trans_rat(
        ss_lhs_sn.clone(),
        split_rhs.clone(),
        sum_pair.clone(),
        leg_a,
        leg_b,
    );
    let t2 = c.trans_rat(ss_lhs_sn.clone(), sum_pair, sum_scaled.clone(), t1, leg_c);
    let t3 = c.trans_rat(
        ss_lhs_sn.clone(),
        sum_scaled,
        c_sum_prefix.clone(),
        t2,
        leg_d,
    );
    let t4 = c.trans_rat(ss_lhs_sn.clone(), c_sum_prefix, c_prod_k.clone(), t3, leg_e);
    let t5 = c.trans_rat(ss_lhs_sn.clone(), c_prod_k, prod_c.clone(), t4, leg_f);
    let proof = c.trans_rat(ss_lhs_sn, prod_c, prod_rhs_sn, t5, leg_g);

    let val = b.mk_lam(y_id, BinderInfo::Default, hcp_sn.clone(), proof);
    let val = b.mk_lam(x_id, BinderInfo::Default, hcp_sn, val);
    let val = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, val);
    b.finish_child(b.mk_lam(k_id, BinderInfo::Default, c.nat(), val))
}

fn build_ind_rho_type(c: &DeltaIndRhoConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat());
    let (n_id, n) = b.fresh_local(c.nat());
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (y_id, y) = b.fresh_local(hcp.clone());
    let lhs = c.ss_lhs_rho(&b, &rho, &n, &x, &y);
    let rhs = c.prod_rhs_rho(&b, &rho, &n, &x, &y);
    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(y_id, BinderInfo::Default, hcp.clone(), concl);
    let ty = b.mk_pi(x_id, BinderInfo::Default, hcp, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat(), ty);
    let ty = b.mk_pi(rho_id, BinderInfo::Default, c.rat(), ty);
    b.finish(ty)
}

fn build_ind_rho_value(c: &DeltaIndRhoConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat());
    let (n_id, n) = b.fresh_local(c.nat());

    // motive (over k, ρ fixed) : fun k => ∀ x y, ss_lhsρ k = prod_rhsρ k.
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (k_id, k) = d.fresh_local(c.nat());
        let hcp = c.hcpoint_of(&k);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let (y_id, y) = d.fresh_local(hcp.clone());
        let lhs = c.ss_lhs_rho(&d, &rho, &k, &x, &y);
        let rhs = c.prod_rhs_rho(&d, &rho, &k, &x, &y);
        let concl = c.eq_rat(lhs, rhs);
        let body = d.mk_pi(y_id, BinderInfo::Default, hcp.clone(), concl);
        let body = d.mk_pi(x_id, BinderInfo::Default, hcp, body);
        d.finish_child(d.mk_lam(k_id, BinderInfo::Default, c.nat(), body))
    };
    // base : motive 0 ≡ subsetSum_chi_bilinear_zero_rho ρ.
    let base = Expr::app(c.base_zero_rho.clone(), rho.clone());
    let step = build_ind_rho_step(c, &rho, &b);

    let body = Expr::apps(c.nat_rec.clone(), [motive, base, step, n.clone()]);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat(), body);
    b.finish(b.mk_lam(rho_id, BinderInfo::Default, c.rat(), val))
}

impl Environment {
    /// Register `BoolAnalysis.subsetSum_chi_bilinear_rho`: THE ρ-weighted
    /// character bilinear-collapse keystone `Σ_S ρ^{|S|}·χ_S(x)·χ_S(y) =
    /// Π_i (1 + ρ·pm(x_i)·pm(y_i))`. `Nat.rec` induction on `n`, ρ riding.
    /// Kernel-checked, constructive. Idempotent.
    pub(crate) fn register_subset_sum_chi_bilinear_rho_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_chi_bilinear_rho");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.init_rat_arith()?;
        self.register_rat_pow_nat()?;
        self.register_subset_sum_chi_bilinear_zero_rho_theorem()?;
        self.register_subset_sum_split()?;
        self.register_chi_bilinear_pair_combine_rho_theorem()?;
        self.register_fin_prod_succ_theorem()?;
        // Fin.sum_add / Fin.sum_smul / Fin.sum_congr live in the Fin.sum overlay.
        self.init_fin_sum()?;
        // Rat.mul_comm (quotient structural).
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?;
        }
        // Re-check: the dep chain may run the `init_boolean_analysis` pass,
        // whose hc24 retirement chain registers this theorem transitively.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = DeltaIndRhoConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_ind_rho_type(&c),
            value: build_ind_rho_value(&c),
        })
    }
}

// ===========================================================================
// noiseDensityW — the un-normalized ρ-weighted correlated density (rung 4).
//
//   noiseDensityW (ρ : Rat) (n : Nat) (x y : HCPoint n) : Rat
//     := subsetSum n (fun S => ρ^{pc n S} · (χ n S x · χ n S y))
//
// A reducible Definition naming the keystone's LHS — the un-normalized
// ρ-correlated density of the pair of cube points `x, y` (`= Σ_S ρ^{|S|}
// χ_S(x)·χ_S(y)`). Its closed form is the keystone's RHS, so the companion
// corollary
//
//   noiseDensityW_eq_prod : ∀ ρ n x y,
//     noiseDensityW ρ n x y = Fin.prod n (fun i => 1 + ρ·(pm(x i)·pm(y i)))
//
// is the keystone restated through the Definition (the LHS δ-unfolds to the
// keystone's `subsetSum` LHS), proven by `subsetSum_chi_bilinear_rho ρ n x y`.
// Both kernel-checked; the corollary is constructive (EMPTY admitted-axiom
// closure). No axiom added — `noiseDensityW` is reducible, `_eq_prod` is a real
// `Eq` Theorem closed by the keystone (not a masquerade).
// ===========================================================================

fn build_noise_density_type(c: &NoiseConsts) -> Expr {
    // (ρ : Rat) → (n : Nat) → (x y : HCPoint n) → Rat
    let mut b = EnvDeclBuilder::new();
    let (rho_id, _rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (x_id, _x) = b.fresh_local(hcp.clone());
    let (y_id, _y) = b.fresh_local(hcp.clone());
    let r = b.mk_pi(y_id, BinderInfo::Default, hcp.clone(), c.rat.clone());
    let r = b.mk_pi(x_id, BinderInfo::Default, hcp, r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    let r = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), r);
    b.finish(r)
}

fn build_noise_density_value(c: &NoiseConsts) -> Expr {
    // fun ρ n x y => subsetSum n (fun S => ρ^{pc n S} · (χ n S x · χ n S y))
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (y_id, y) = b.fresh_local(hcp.clone());
    let body = c.ss_lhs_rho(&b, &rho, &n, &x, &y);
    let val = b.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body);
    let val = b.mk_lam(x_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}

impl NoiseConsts {
    fn noise_density(&self, rho: &Expr, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.noiseDensityW"), vec![]),
            [rho.clone(), n.clone(), x.clone(), y.clone()],
        )
    }
}

fn build_noise_density_eq_prod_type(c: &NoiseConsts) -> Expr {
    // ∀ ρ n x y, noiseDensityW ρ n x y = Fin.prod n (prod_int_rho ρ n x y)
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (y_id, y) = b.fresh_local(hcp.clone());
    let lhs = c.noise_density(&rho, &n, &x, &y);
    let rhs = c.prod_rhs_rho(&b, &rho, &n, &x, &y);
    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(y_id, BinderInfo::Default, hcp.clone(), concl);
    let ty = b.mk_pi(x_id, BinderInfo::Default, hcp, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    let ty = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), ty);
    b.finish(ty)
}

fn build_noise_density_eq_prod_value(c: &NoiseConsts) -> Expr {
    // fun ρ n x y => subsetSum_chi_bilinear_rho ρ n x y
    // (noiseDensityW ρ n x y δ-unfolds to the keystone's subsetSum LHS, so the
    //  keystone's proof inhabits this statement's type directly.)
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (y_id, y) = b.fresh_local(hcp.clone());
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.subsetSum_chi_bilinear_rho"),
            vec![],
        ),
        [rho.clone(), n.clone(), x.clone(), y.clone()],
    );
    let val = b.mk_lam(y_id, BinderInfo::Default, hcp.clone(), proof);
    let val = b.mk_lam(x_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.noiseDensityW`: the un-normalized ρ-weighted
    /// correlated density `Σ_S ρ^{|S|}·χ_S(x)·χ_S(y)`, a reducible Definition
    /// naming the keystone's LHS (rung 4). Idempotent.
    pub(crate) fn register_noise_density_w(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noiseDensityW");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?;
        self.init_rat_arith()?;
        self.register_rat_pow_nat()?;
        self.register_subset_sum()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Re-check: the `init_boolean_analysis` pass registers the hc24 chain
        // (bonami retirement), which includes `noiseDensityW` itself.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = NoiseConsts::new();
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: build_noise_density_type(&c),
            value: build_noise_density_value(&c),
            is_reducible: true,
        })
    }

    /// Register `BoolAnalysis.noiseDensityW_eq_prod`: the closed form
    /// `noiseDensityW ρ n x y = Π_i (1 + ρ·pm(x_i)·pm(y_i))` (rung 4 corollary).
    /// The keystone restated through the Definition; kernel-checked, constructive
    /// (EMPTY admitted-axiom closure). Idempotent.
    pub(crate) fn register_noise_density_w_eq_prod_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noiseDensityW_eq_prod");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_noise_density_w()?;
        self.register_subset_sum_chi_bilinear_rho_theorem()?;
        // Re-check: the dep chain may run the `init_boolean_analysis` pass,
        // whose hc24 retirement chain registers `noiseDensityW_eq_prod`.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = NoiseConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_noise_density_eq_prod_type(&c),
            value: build_noise_density_eq_prod_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn assert_constructive(env: &Environment, name_str: &str) {
        let name = Name::from_string(name_str);
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "transitive axiom closure must be empty"
        );
    }

    #[test]
    fn test_rat_pow_nat_is_reducible_definition() {
        let mut env = Environment::new();
        env.register_rat_pow_nat().expect("register_rat_pow_nat");
        let info = env
            .get_const(&Name::from_string("Rat.powNat"))
            .expect("registered");
        assert_eq!(info.kind, ConstantKind::Definition);
        let value = info.value.clone().expect("body present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("Rat.powNat body must check against its type");
    }

    #[test]
    fn test_rat_pow_nat_zero_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_rat_pow_nat_zero_theorem()
            .expect("register_rat_pow_nat_zero_theorem");
        assert_constructive(&env, "Rat.powNat_zero");
    }

    #[test]
    fn test_rat_pow_nat_succ_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_rat_pow_nat_succ_theorem()
            .expect("register_rat_pow_nat_succ_theorem");
        assert_constructive(&env, "Rat.powNat_succ");
    }

    #[test]
    fn test_rat_pow_nat_add_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_rat_pow_nat_add_theorem()
            .expect("register_rat_pow_nat_add_theorem");
        assert_constructive(&env, "Rat.powNat_add");
    }

    #[test]
    fn test_chi_factor_pair_sum_rho_is_constructive_theorem() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_chi_factor_pair_sum_rho_theorem()
            .expect("register_chi_factor_pair_sum_rho_theorem");
        assert_constructive(&env, "BoolAnalysis.chi_factor_pair_sum_rho");
    }

    #[test]
    fn test_subset_sum_chi_bilinear_zero_rho_is_constructive_theorem() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_subset_sum_chi_bilinear_zero_rho_theorem()
            .expect("register_subset_sum_chi_bilinear_zero_rho_theorem");
        assert_constructive(&env, "BoolAnalysis.subsetSum_chi_bilinear_zero_rho");
    }

    #[test]
    fn test_popcount_succ_split_is_constructive_theorem() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_popcount_succ_split_theorem()
            .expect("register_popcount_succ_split_theorem");
        assert_constructive(&env, "BoolAnalysis.popcount_succ_split");
    }

    #[test]
    fn test_chi_bilinear_pair_combine_rho_is_constructive_theorem() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_chi_bilinear_pair_combine_rho_theorem()
            .expect("register_chi_bilinear_pair_combine_rho_theorem");
        assert_constructive(&env, "BoolAnalysis.chi_bilinear_pair_combine_rho");
    }

    #[test]
    fn test_subset_sum_chi_bilinear_rho_is_constructive_theorem() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_subset_sum_chi_bilinear_rho_theorem()
            .expect("register_subset_sum_chi_bilinear_rho_theorem");
        assert_constructive(&env, "BoolAnalysis.subsetSum_chi_bilinear_rho");
    }

    #[test]
    fn test_noise_density_w_is_reducible_definition() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_noise_density_w()
            .expect("register_noise_density_w");
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.noiseDensityW"))
            .expect("registered");
        assert_eq!(info.kind, ConstantKind::Definition);
        let value = info.value.clone().expect("body present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("noiseDensityW body must check against its type");
    }

    #[test]
    fn test_noise_density_w_eq_prod_is_constructive_theorem() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_noise_density_w_eq_prod_theorem()
            .expect("register_noise_density_w_eq_prod_theorem");
        assert_constructive(&env, "BoolAnalysis.noiseDensityW_eq_prod");
    }

    #[test]
    fn test_rat_pow_nat_ground_two_cubed() {
        // ρ = 2, k = 3 → ρ^3. Check `powNat 2 3` is well-typed and reduces.
        let mut env = Environment::new();
        env.register_rat_pow_nat().expect("register_rat_pow_nat");
        let c = NoiseConsts::new();
        // 2 := Rat.mk (Int.ofNat 2) 1
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let one = Expr::app(nat_succ.clone(), nat_zero.clone());
        let two_nat = Expr::app(nat_succ.clone(), one.clone());
        let three_nat = Expr::app(nat_succ, two_nat.clone());
        let rho = Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [
                Expr::app(
                    Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                    two_nat,
                ),
                one,
            ],
        );
        let e = c.pow(&rho, &three_nat);
        let tc = TypeChecker::with_mode(&env, env.mode());
        let ty = tc.infer_type(&e).expect("powNat 2 3 type-infers");
        assert_eq!(ty, c.rat, "powNat 2 3 : Rat");
    }
}
