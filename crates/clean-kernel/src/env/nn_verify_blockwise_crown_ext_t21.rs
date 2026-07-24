// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! T21 `LayerNorm.zonotope_width_preserved` — MASQUERADE/AXIOM RETIRED via a
//! FAITHFUL GAIN-BOUND RESTATEMENT proven constructively.
//!
//! **Status:** Replaces the body-less `Declaration::Axiom` (#3509 Branch A)
//! with a kernel-checked `Declaration::Theorem` of the GAIN-BOUND form. The
//! prior axiom was FALSE-as-written (unconditional width preservation fails
//! under faithful LayerNorm gain `|γ_i| > 1`). Under the genuine gain bound
//! `|γ_i| ≤ 1` it is TRUE and proven here, so the axiom retires (domain TCB
//! 5 → 4, toward the 3-Lean-4-axiom finish line).
//!
//! ### Statement (GAIN-BOUND form)
//!
//! ```text
//! ∀ (n k : Nat) (γ β : NNVec n) (ε : Rat) (z : Zonotope n k),
//!   (∀ (i : Fin n), |γ i| ≤ 1)
//!   → l1_norm n (width n (zonotope_output n k γ β ε z))
//!       ≤ l1_norm n (width n (to_ibp n k z))
//! ```
//!
//! ### Why TRUE + the proof
//!
//! Faithful carriers (`nn_verify_blockwise_crown_ext_t20.rs`):
//! `zonotope_output = to_ibp ∘ layernorm_zono`, where `layernorm_zono` builds
//! `center'_i = γ_i·c_i + β_i` and `gens'_ij = γ_i·G_ij`. So per component:
//!
//! ```text
//! width(out)_i = (m_i + S'_i) − (m_i − S'_i),  m_i = γ_i·c_i+β_i,
//!                S'_i = Σⱼ|γ_i·G_ij|
//! width(in)_i  = (c_i + S_i)  − (c_i − S_i),   S_i = Σⱼ|G_ij|
//! l1_norm n v  = Σᵢ |v i|
//! ```
//!
//! Per-component lemma `width_out_le_width_in_pointwise` (L2):
//! `|γ_i| ≤ 1 → |width(out)_i| ≤ |width(in)_i|`. Proof rungs:
//! - **RUNG 1 (eq_S'):** `S'_i = |γ_i|·S_i`. Summand congruence under the
//!   `Fin.sum k` binder via `funext` + `Fin.sum_congr` with pointwise
//!   `Rat.abs_mul`; then `Fin.sum_smul` collapses `Σⱼ |γ_i|·|G_ij|` to
//!   `|γ_i|·Σⱼ|G_ij| = |γ_i|·S_i`.
//! - **RUNG 2 (core S'_i ≤ S_i):** `S_i ≥ 0` (`Fin.sum_nonneg` +
//!   `Rat.abs_nonneg`); `Rat.mul_le_mul_of_nonneg_right` with `|γ_i| ≤ 1` and
//!   `S_i ≥ 0` gives `|γ_i|·S_i ≤ 1·S_i`; `Rat.one_mul` collapses the RHS to
//!   `S_i`; transport through eq_S' yields `S'_i ≤ S_i`.
//! - **width(out)_i ≤ width(in)_i WITHOUT distributivity:** the cancellation
//!   lemma L0 `(x+r) − (x−r) = r+r` (`Rat.sub_add_sub` + `Rat.neg_neg` +
//!   `Rat.add_neg_self` + `Rat.zero_add`, all foundational/constructive — NO
//!   `Rat.left_distrib`) rewrites both widths to `S'_i+S'_i` resp. `S_i+S_i`;
//!   `Rat.add_le_add` gives `S'_i+S'_i ≤ S_i+S_i`; transport back through L0.
//! - **strip the outer `|·|`:** `S_i+S_i ≥ 0` and `S'_i+S'_i ≥ 0`, so
//!   `Rat.abs_of_nonneg` gives `|width(·)_i| = width(·)_i`; transport.
//!
//! **RUNG 3 (T21):** `Fin.sum_le n F G (fun i => L2 … i (h i))` with
//! `F = fun i => |width(out)_i|`, `G = fun i => |width(in)_i|`. The
//! `Fin.sum_le` result is defeq (l1_norm/width δ) to the registered
//! conclusion, so it checks directly.
//!
//! ### Soundness
//!
//! NO `Rat.left_distrib`/`Rat.right_distrib` (the #3654 unsound distributive
//! bridge): the `(x+r)−(x−r)=r+r` route is purely additive-group + `neg_neg`.
//! Transitive axiom closure of T21 and L2 is `⊆ FOUNDATIONAL_AXIOMS`
//! (`Constructive`). NO `sorry`, NO `add_decl_structural`, NO `native_decide`.
//!
//! Part of #3509 (Branch B, T21 half). Tranche B #4 of
//! `designs/2026-06-13-nnverify-5axiom-retirement-roadmap.md`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

const ZONO: &str = "NNVerify.Zonotope";
const L2_NAME: &str = "NNVerify.LayerNorm.width_out_le_width_in_pointwise";
const L0_NAME: &str = "Rat.add_sub_sub_self_eq_add";
const T21_NAME: &str = "NNVerify.LayerNorm.zonotope_width_preserved";

/// Cached constants for the T21 gain-bound theorem + its per-component lemma.
struct T21Consts {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    nn_vec: Expr,
    zonotope: Expr,
    // Rat arithmetic.
    rat_add: Expr,
    rat_sub: Expr,
    rat_mul: Expr,
    rat_abs: Expr,
    rat_one: Expr,
    rat_zero: Expr,
    // Order / le.
    le_le: Expr,
    inst_le_rat: Expr,
    // Carriers.
    fin_sum: Expr,
    zono_to_ibp: Expr,
    zonotope_output: Expr,
    ib_width: Expr,
    nn_vec_l1: Expr,
    // Bricks.
    fin_sum_le: Expr,
    fin_sum_smul: Expr,
    fin_sum_nonneg: Expr,
    fin_sum_congr: Expr,
    abs_mul: Expr,
    abs_of_nonneg: Expr,
    abs_nonneg: Expr,
    mul_le_mul_right: Expr,
    one_mul: Expr,
    add_le_add: Expr,
    add_zero: Expr,
    l0: Expr,
    // Eq machinery (Sort 1 / Rat).
    eq: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
    // `fin_sum_congr` takes the pointwise proof directly; `funext` is not used.
}

impl T21Consts {
    fn new() -> Self {
        let c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let l0 = Level::zero();
        let l1 = Level::succ(Level::zero());
        Self {
            nat: c("Nat"),
            rat: c("Rat"),
            fin: c("Fin"),
            nn_vec: c("NNVerify.NNVec"),
            zonotope: c("NNVerify.Zonotope"),
            rat_add: c("Rat.add"),
            rat_sub: c("Rat.sub"),
            rat_mul: c("Rat.mul"),
            rat_abs: c("Rat.abs"),
            rat_one: c("Rat.one"),
            rat_zero: c("Rat.zero"),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![l0.clone()]),
            inst_le_rat: c("instLERat"),
            fin_sum: c("Fin.sum"),
            zono_to_ibp: c("NNVerify.Zonotope.to_ibp"),
            zonotope_output: c("NNVerify.LayerNorm.zonotope_output"),
            ib_width: c("NNVerify.IntervalBounds.width"),
            nn_vec_l1: c("NNVerify.NNVec.l1_norm"),
            fin_sum_le: c("Fin.sum_le"),
            fin_sum_smul: c("Fin.sum_smul"),
            fin_sum_nonneg: c("Fin.sum_nonneg"),
            fin_sum_congr: c("Fin.sum_congr"),
            abs_mul: c("Rat.abs_mul"),
            abs_of_nonneg: c("Rat.abs_of_nonneg"),
            abs_nonneg: c("Rat.abs_nonneg"),
            mul_le_mul_right: c("Rat.mul_le_mul_of_nonneg_right"),
            one_mul: c("Rat.one_mul"),
            add_le_add: c("Rat.add_le_add"),
            add_zero: c("Rat.add_zero"),
            l0: c(L0_NAME),
            eq: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn vec_of(&self, n: &Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n.clone())
    }
    fn zono_of(&self, n: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.zonotope.clone(), [n.clone(), k.clone()])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn abs(&self, a: Expr) -> Expr {
        Expr::app(self.rat_abs.clone(), a)
    }
    fn sum(&self, k: &Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [k.clone(), f])
    }
    fn rat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), lhs, rhs],
        )
    }
    fn rat_eq(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq.clone(), [self.rat.clone(), lhs, rhs])
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    fn trans(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, c, h1, h2])
    }
    /// `@Eq.subst.{1} Rat motive a b h_eq h_pa : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_pa: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h_pa],
        )
    }
    /// `@congrArg.{1,1} Rat Rat a b f h : f a = f b`.
    fn congr_arg(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    /// `width n B` (a `NNVec n`).
    fn width_vec(&self, n: &Expr, bounds: Expr) -> Expr {
        Expr::apps(self.ib_width.clone(), [n.clone(), bounds])
    }
    /// `l1_norm n v`.
    fn l1(&self, n: &Expr, v: Expr) -> Expr {
        Expr::apps(self.nn_vec_l1.clone(), [n.clone(), v])
    }
    /// `to_ibp n k z`.
    fn to_ibp(&self, n: &Expr, k: &Expr, z: &Expr) -> Expr {
        Expr::apps(self.zono_to_ibp.clone(), [n.clone(), k.clone(), z.clone()])
    }
    /// `zonotope_output n k γ β ε z`.
    fn zout(&self, n: &Expr, k: &Expr, g: &Expr, b: &Expr, e: &Expr, z: &Expr) -> Expr {
        Expr::apps(
            self.zonotope_output.clone(),
            [
                n.clone(),
                k.clone(),
                g.clone(),
                b.clone(),
                e.clone(),
                z.clone(),
            ],
        )
    }
}

// ---------------------------------------------------------------------------
// L0: `Rat.add_sub_sub_self_eq_add : ∀ (x r : Rat), (x + r) − (x − r) = r + r`.
// ---------------------------------------------------------------------------

/// `Rat.sub_add_sub : ∀ (A B a b : Rat), (A − B) + (a − b) = (A + a) − (B + b)`.
/// `Rat.neg_neg`, `Rat.add_neg_self`, `Rat.zero_add` as registered.
fn build_l0_proof(c: &T21Consts) -> Expr {
    let neg = |e: Expr| Expr::app(Expr::const_(Name::from_string("Rat.neg"), vec![]), e);
    let sub_add_sub = Expr::const_(Name::from_string("Rat.sub_add_sub"), vec![]);
    let neg_neg = Expr::const_(Name::from_string("Rat.neg_neg"), vec![]);
    let add_neg_self = Expr::const_(Name::from_string("Rat.add_neg_self"), vec![]);
    let zero_add = Expr::const_(Name::from_string("Rat.zero_add"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let (r_id, r) = b.fresh_local(c.rat.clone());

    // Target: (x + r) − (x − r) = r + r.
    // Step A: sub_add_sub x x r (-r) : (x − x) + (r − (-r)) = (x + r) − (x + (-r)).
    //   Note `x + (-r) ≡ x − r` (defeq), so the RHS is defeq to `(x+r) − (x−r)`,
    //   the target LHS.
    let neg_r = neg(r.clone());
    let x_sub_x = c.sub(x.clone(), x.clone());
    let r_sub_negr = c.sub(r.clone(), neg_r.clone());
    let lhs_sas = c.add(x_sub_x.clone(), r_sub_negr.clone()); // (x−x)+(r−(-r))
    let target_lhs = c.sub(c.add(x.clone(), r.clone()), c.sub(x.clone(), r.clone())); // (x+r)−(x−r)
                                                                                      // `sub_add_sub` RHS is `(x+r) − (x + (-r))`, defeq to `target_lhs`.
    let sas = Expr::apps(
        sub_add_sub,
        [x.clone(), x.clone(), r.clone(), neg_r.clone()],
    );
    // sas : lhs_sas = target_lhs (after defeq of `x+(-r)` ↦ `x−r`).
    // symm: target_lhs = lhs_sas.
    let sas_symm = c.symm(lhs_sas.clone(), target_lhs.clone(), sas);

    // Step B: rewrite lhs_sas to `r + r`.
    //   B1: (r − (-r)) = r + r.
    //       r − (-r) ≡ r + (-(-r)); neg_neg r : -(-r) = r; congrArg (r + ·) gives
    //       r + (-(-r)) = r + r. Since `r − (-r) ≡ r + (-(-r))` defeq, this is a
    //       proof of `r − (-r) = r + r`.
    let nn_r = Expr::apps(neg_neg, [r.clone()]); // -(-r) = r
    let add_left_r = {
        // f := fun y => r + y
        let mut d = EnvDeclBuilder::child_of(&b);
        let (y_id, y) = d.fresh_local(c.rat.clone());
        let body = c.add(r.clone(), y);
        d.finish_child(d.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), body))
    };
    // congrArg : (r + (-(-r))) = (r + r); defeq LHS to (r − (-r)).
    let r_add_r = c.add(r.clone(), r.clone());
    let b1 = c.congr_arg(neg(neg_r.clone()), r.clone(), add_left_r, nn_r);
    // b1 : (r + (-(-r))) = (r + r), defeq to `(r − (-r)) = (r + r)`.

    //   B2: (x − x) = 0  via `Rat.add_neg_self x : x + (-x) = 0` (defeq `x−x`).
    let b2 = Expr::apps(add_neg_self, [x.clone()]); // : x + (-x) = 0, defeq `x − x = 0`.

    //   Assemble lhs_sas = (x−x) + (r−(-r)).
    //   Rewrite the right summand `(r − (-r))` to `(r + r)` via congrArg (x−x + ·) b1,
    //   producing `(x−x) + (r−(-r)) = (x−x) + (r+r)`.
    let add_left_xsubx = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (y_id, y) = d.fresh_local(c.rat.clone());
        let body = c.add(x_sub_x.clone(), y);
        d.finish_child(d.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), body))
    };
    // step1 : (x−x)+(r−(-r)) = (x−x)+(r+r).
    //   We pass `a = r − (-r)` (the syntactic form in `lhs_sas`); `b1`'s type is
    //   `(r+(-(-r))) = (r+r)`, defeq to `(r−(-r)) = (r+r)`, so the kernel accepts.
    let xsubx_add_rr = c.add(x_sub_x.clone(), r_add_r.clone());
    let step1 = c.congr_arg(
        r_sub_negr.clone(),
        r_add_r.clone(),
        add_left_xsubx,
        b1.clone(),
    );

    //   step2 : (x−x)+(r+r) = 0 + (r+r) via congrArg (· + (r+r)) b2.
    let add_right_rr = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (y_id, y) = d.fresh_local(c.rat.clone());
        let body = c.add(y, r_add_r.clone());
        d.finish_child(d.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let zero_add_rr = c.add(c.rat_zero.clone(), r_add_r.clone());
    let step2 = c.congr_arg(x_sub_x.clone(), c.rat_zero.clone(), add_right_rr, b2);

    //   step3 : 0 + (r+r) = (r+r) via Rat.zero_add (r+r).
    let step3 = Expr::apps(zero_add, [r_add_r.clone()]);

    //   chain: lhs_sas = (x−x)+(r+r) = 0+(r+r) = (r+r).
    let chain_a = c.trans(
        lhs_sas.clone(),
        xsubx_add_rr.clone(),
        zero_add_rr.clone(),
        step1,
        step2,
    );
    let chain = c.trans(
        lhs_sas.clone(),
        zero_add_rr,
        r_add_r.clone(),
        chain_a,
        step3,
    );
    // chain : lhs_sas = r + r.

    //   final: target_lhs = lhs_sas = (r+r)  via trans sas_symm chain.
    let proof = c.trans(
        target_lhs.clone(),
        lhs_sas,
        r_add_r.clone(),
        sas_symm,
        chain,
    );

    let val = b.mk_lam(r_id, BinderInfo::Default, c.rat.clone(), proof);
    let val = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}

fn build_l0_type(c: &T21Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let (r_id, r) = b.fresh_local(c.rat.clone());
    let lhs = c.sub(c.add(x.clone(), r.clone()), c.sub(x.clone(), r.clone()));
    let rhs = c.add(r.clone(), r.clone());
    let concl = c.rat_eq(lhs, rhs);
    let ty = b.mk_pi(r_id, BinderInfo::Default, c.rat.clone(), concl);
    let ty = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), ty);
    b.finish(ty)
}

// ---------------------------------------------------------------------------
// L2: per-component gain bound
//   `width_out_le_width_in_pointwise :
//      ∀ n k γ β ε z i, |γ i| ≤ 1 → |width(out)_i| ≤ |width(in)_i|`.
// ---------------------------------------------------------------------------

/// Per-component reduced-form expressions, given the bound vars. All are defeq
/// to the corresponding `width …` indexings via δ/ι/β reduction.
struct PerComp {
    c_i: Expr,     // z.center i
    gamma_i: Expr, // γ i
    /// `z.generators i` (a `Fin k → Rat` row).
    gens_i: Expr,
    /// `S_i  = Σⱼ |G_ij|`.
    s_i: Expr,
    /// `S'_i = Σⱼ |γ_i · G_ij|`.
    s_prime_i: Expr,
    /// `m_i  = γ_i·c_i + β_i`.
    m_i: Expr,
    /// `|G_·|`-summand `fun j => |G_ij|`.
    abs_g_fn: Expr,
    /// `|γ_i·G_·|`-summand `fun j => |γ_i · G_ij|`.
    abs_scaled_fn: Expr,
    /// `|γ_i|·|G_·|`-summand `fun j => |γ_i| · |G_ij|`.
    scaled_abs_fn: Expr,
}

impl T21Consts {
    /// Build the per-component reduced-form expressions. `parent` owns
    /// `n, k, γ, β, z, i` (the summand lambdas are `child_of(parent)`).
    fn per_comp(
        &self,
        parent: &EnvDeclBuilder,
        k: &Expr,
        gamma: &Expr,
        beta: &Expr,
        z: &Expr,
        i: &Expr,
    ) -> PerComp {
        let zono = Name::from_string(ZONO);
        let center = Expr::proj(zono.clone(), 0, z.clone());
        let gens = Expr::proj(zono, 1, z.clone());
        let c_i = Expr::app(center, i.clone());
        let gens_i = Expr::app(gens, i.clone());
        let gamma_i = Expr::app(gamma.clone(), i.clone());
        let beta_i = Expr::app(beta.clone(), i.clone());
        let m_i = self.add(self.mul(gamma_i.clone(), c_i.clone()), beta_i);
        let fin_k = self.fin_of(k);

        // fun j => |G_ij|.
        let abs_g_fn = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (j_id, j) = d.fresh_local(fin_k.clone());
            let body = self.abs(Expr::app(gens_i.clone(), j));
            d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body))
        };
        // fun j => |γ_i · G_ij|.
        let abs_scaled_fn = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (j_id, j) = d.fresh_local(fin_k.clone());
            let body = self.abs(self.mul(gamma_i.clone(), Expr::app(gens_i.clone(), j)));
            d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body))
        };
        // fun j => |γ_i| · |G_ij|.
        let scaled_abs_fn = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (j_id, j) = d.fresh_local(fin_k.clone());
            let body = self.mul(
                self.abs(gamma_i.clone()),
                self.abs(Expr::app(gens_i.clone(), j)),
            );
            d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body))
        };

        let s_i = self.sum(k, abs_g_fn.clone());
        let s_prime_i = self.sum(k, abs_scaled_fn.clone());
        PerComp {
            c_i,
            gamma_i,
            gens_i,
            s_i,
            s_prime_i,
            m_i,
            abs_g_fn,
            abs_scaled_fn,
            scaled_abs_fn,
        }
    }

    /// `width(out)_i = (m_i + S'_i) − (m_i − S'_i)` — defeq to the indexed
    /// `width n (zonotope_output …) i`.
    fn w_out(&self, p: &PerComp) -> Expr {
        self.sub(
            self.add(p.m_i.clone(), p.s_prime_i.clone()),
            self.sub(p.m_i.clone(), p.s_prime_i.clone()),
        )
    }
    /// `width(in)_i = (c_i + S_i) − (c_i − S_i)`.
    fn w_in(&self, p: &PerComp) -> Expr {
        self.sub(
            self.add(p.c_i.clone(), p.s_i.clone()),
            self.sub(p.c_i.clone(), p.s_i.clone()),
        )
    }
}

/// L2 conclusion (per `i`, under `|γ i| ≤ 1`): `|width(out)_i| ≤ |width(in)_i|`,
/// stated over the literal `width`/`l1_norm` surface so that
/// `Fin.sum_le`'s pointwise hypothesis matches.
///
/// `w_out_i := (width n (zonotope_output n k γ β ε z)) i`,
/// `w_in_i  := (width n (to_ibp n k z)) i`.
fn l2_conclusion(
    c: &T21Consts,
    n: &Expr,
    k: &Expr,
    gamma: &Expr,
    beta: &Expr,
    eps: &Expr,
    z: &Expr,
    i: &Expr,
) -> Expr {
    let out = c.zout(n, k, gamma, beta, eps, z);
    let w_out_i = Expr::app(c.width_vec(n, out), i.clone());
    let ibp = c.to_ibp(n, k, z);
    let w_in_i = Expr::app(c.width_vec(n, ibp), i.clone());
    c.rat_le(c.abs(w_out_i), c.abs(w_in_i))
}

/// `fun (i : Fin n) => Rat.abs ((width n B) i)` — the summand `Fin.sum_le`
/// expects (`B` an `IntervalBounds n`).
fn abs_width_fn(c: &T21Consts, parent: &EnvDeclBuilder, n: &Expr, bounds: Expr) -> Expr {
    let fin_n = c.fin_of(n);
    let w = c.width_vec(n, bounds);
    let mut d = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = d.fresh_local(fin_n.clone());
    let body = c.abs(Expr::app(w, i));
    d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
}

fn build_l2_type(c: &T21Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(&n);
    let zono_nk = c.zono_of(&n, &k);
    let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
    let (beta_id, beta) = b.fresh_local(vec_n.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (z_id, z) = b.fresh_local(zono_nk.clone());
    let fin_n = c.fin_of(&n);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    // h : |γ i| ≤ 1.
    let h_ty = c.rat_le(
        c.abs(Expr::app(gamma.clone(), i.clone())),
        c.rat_one.clone(),
    );
    let (h_id, _h) = b.fresh_local(h_ty.clone());
    let concl = l2_conclusion(c, &n, &k, &gamma, &beta, &eps, &z, &i);
    let r = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
    let r = b.mk_pi(i_id, BinderInfo::Default, fin_n, r);
    let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
    let r = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), r);
    let r = b.mk_pi(beta_id, BinderInfo::Default, vec_n.clone(), r);
    let r = b.mk_pi(gamma_id, BinderInfo::Default, vec_n, r);
    let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

fn build_l2_value(c: &T21Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(&n);
    let zono_nk = c.zono_of(&n, &k);
    let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
    let (beta_id, beta) = b.fresh_local(vec_n.clone());
    let (eps_id, _eps) = b.fresh_local(c.rat.clone());
    let (z_id, z) = b.fresh_local(zono_nk.clone());
    let fin_n = c.fin_of(&n);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let h_ty = c.rat_le(
        c.abs(Expr::app(gamma.clone(), i.clone())),
        c.rat_one.clone(),
    );
    let (h_id, h) = b.fresh_local(h_ty.clone());

    let p = c.per_comp(&b, &k, &gamma, &beta, &z, &i);
    let proof = build_l2_proof(c, &b, &k, &h, &p);

    let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, proof);
    let e = b.mk_lam(i_id, BinderInfo::Default, fin_n, e);
    let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, e);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_lam(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Proof of `|width(out)_i| ≤ |width(in)_i|` given `h : |γ_i| ≤ 1`.
fn build_l2_proof(c: &T21Consts, parent: &EnvDeclBuilder, k: &Expr, h: &Expr, p: &PerComp) -> Expr {
    let abs_gamma_i = c.abs(p.gamma_i.clone());
    let s = p.s_i.clone();
    let s_prime = p.s_prime_i.clone();
    let rr = |e: &Expr| c.add(e.clone(), e.clone());
    let s_plus_s = rr(&s);
    let sp_plus_sp = rr(&s_prime);
    let g_ij = |j: Expr| Expr::app(p.gens_i.clone(), j);

    // ---- RUNG 1: eq_S' : S'_i = |γ_i| · S_i. ----------------------------
    // (1a) summand congruence: (fun j => |γ_i·G_ij|) = (fun j => |γ_i|·|G_ij|).
    //   pointwise via Rat.abs_mul γ_i G_ij : |γ_i·G_ij| = |γ_i|·|G_ij|; lift by
    //   Fin.sum_congr to the sums.
    let pointwise_abs_mul = {
        let fin_k = c.fin_of(k);
        let mut d = EnvDeclBuilder::child_of(parent);
        let (j_id, j) = d.fresh_local(fin_k.clone());
        // |γ_i · G_ij| = |γ_i| · |G_ij|.
        let body = Expr::apps(c.abs_mul.clone(), [p.gamma_i.clone(), g_ij(j)]);
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_k, body))
    };
    // Fin.sum_congr k abs_scaled_fn scaled_abs_fn pointwise_abs_mul
    //   : Fin.sum k abs_scaled_fn = Fin.sum k scaled_abs_fn  (= S'_i = Σ|γ_i||G_ij|).
    let congr_sums = Expr::apps(
        c.fin_sum_congr.clone(),
        [
            k.clone(),
            p.abs_scaled_fn.clone(),
            p.scaled_abs_fn.clone(),
            pointwise_abs_mul,
        ],
    );
    // (1b) Fin.sum_smul k |γ_i| abs_g_fn : Σⱼ |γ_i|·|G_ij| = |γ_i| · Σⱼ|G_ij|.
    let sum_smul = Expr::apps(
        c.fin_sum_smul.clone(),
        [k.clone(), abs_gamma_i.clone(), p.abs_g_fn.clone()],
    );
    // eq_S' : S'_i = |γ_i| · S_i  via trans.
    let sum_scaled_abs = c.sum(k, p.scaled_abs_fn.clone()); // Σ |γ_i|·|G_ij|
    let gi_s = c.mul(abs_gamma_i.clone(), s.clone());
    let eq_s_prime = c.trans(
        s_prime.clone(),
        sum_scaled_abs,
        gi_s.clone(),
        congr_sums,
        sum_smul,
    );

    // ---- RUNG 2a: S_i ≥ 0 (and S'_i ≥ 0) -------------------------------
    // h_s_nn : 0 ≤ S_i via Fin.sum_nonneg k abs_g_fn (fun j => Rat.abs_nonneg (G_ij)).
    let pointwise_nonneg = |scaled: bool| -> Expr {
        let fin_k = c.fin_of(k);
        let mut d = EnvDeclBuilder::child_of(parent);
        let (j_id, j) = d.fresh_local(fin_k.clone());
        let arg = if scaled {
            // for S'_i: 0 ≤ |γ_i·G_ij|
            c.mul(p.gamma_i.clone(), g_ij(j))
        } else {
            // for S_i: 0 ≤ |G_ij|
            g_ij(j)
        };
        let body = Expr::app(c.abs_nonneg.clone(), arg);
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_k, body))
    };
    let h_s_nn = Expr::apps(
        c.fin_sum_nonneg.clone(),
        [k.clone(), p.abs_g_fn.clone(), pointwise_nonneg(false)],
    );
    let h_sp_nn = Expr::apps(
        c.fin_sum_nonneg.clone(),
        [k.clone(), p.abs_scaled_fn.clone(), pointwise_nonneg(true)],
    );

    // ---- RUNG 2c: core S'_i ≤ S_i --------------------------------------
    // mul_le_mul_of_nonneg_right S_i |γ_i| 1 h h_s_nn : |γ_i|·S_i ≤ 1·S_i.
    let core_mul = Expr::apps(
        c.mul_le_mul_right.clone(),
        [
            s.clone(),
            abs_gamma_i.clone(),
            c.rat_one.clone(),
            h.clone(),
            h_s_nn.clone(),
        ],
    );
    // one_mul S_i : 1·S_i = S_i. Transport RHS of core_mul: |γ_i|·S_i ≤ S_i.
    let one_s = c.mul(c.rat_one.clone(), s.clone());
    let one_mul_s = Expr::apps(c.one_mul.clone(), [s.clone()]);
    // motive : fun y => |γ_i|·S_i ≤ y.
    let motive_rhs = motive_le_right(c, parent, gi_s.clone());
    let gi_s_le_s = c.subst(motive_rhs, one_s, s.clone(), one_mul_s, core_mul);
    // gi_s_le_s : |γ_i|·S_i ≤ S_i. Transport LHS back through eq_S' (symm):
    //   motive : fun y => y ≤ S_i ; along (|γ_i|·S_i = S'_i) i.e. symm eq_S'.
    let motive_lhs = motive_le_left(c, parent, s.clone());
    let eq_s_prime_symm = c.symm(s_prime.clone(), gi_s.clone(), eq_s_prime.clone());
    let sp_le_s = c.subst(
        motive_lhs,
        gi_s.clone(),
        s_prime.clone(),
        eq_s_prime_symm,
        gi_s_le_s,
    );
    // sp_le_s : S'_i ≤ S_i.

    // ---- RUNG 2d: width(out)_i ≤ width(in)_i (no distributivity) --------
    // add_le_add S'_i S_i S'_i S_i sp_le_s sp_le_s : (S'_i+S'_i) ≤ (S_i+S_i).
    let sums_le = Expr::apps(
        c.add_le_add.clone(),
        [
            s_prime.clone(),
            s.clone(),
            s_prime.clone(),
            s.clone(),
            sp_le_s.clone(),
            sp_le_s,
        ],
    );
    // L0 m_i S'_i : (m_i+S'_i)−(m_i−S'_i) = S'_i+S'_i  i.e. w_out = S'_i+S'_i.
    let l0_out = Expr::apps(c.l0.clone(), [p.m_i.clone(), s_prime.clone()]);
    // L0 c_i S_i  : (c_i+S_i)−(c_i−S_i) = S_i+S_i      i.e. w_in = S_i+S_i.
    let l0_in = Expr::apps(c.l0.clone(), [p.c_i.clone(), s.clone()]);
    let w_out = c.w_out(p);
    let w_in = c.w_in(p);
    // Transport sums_le LHS (S'_i+S'_i) ↦ w_out via symm(l0_out):
    //   motive : fun y => y ≤ (S_i+S_i).
    let motive2_lhs = motive_le_left(c, parent, s_plus_s.clone());
    let l0_out_symm = c.symm(w_out.clone(), sp_plus_sp.clone(), l0_out);
    let lhs_w_le = c.subst(
        motive2_lhs,
        sp_plus_sp.clone(),
        w_out.clone(),
        l0_out_symm,
        sums_le,
    );
    // lhs_w_le : w_out ≤ (S_i+S_i). Transport RHS (S_i+S_i) ↦ w_in via symm(l0_in):
    //   motive : fun y => w_out ≤ y.
    let motive2_rhs = motive_le_right(c, parent, w_out.clone());
    let l0_in_symm = c.symm(w_in.clone(), s_plus_s.clone(), l0_in);
    let w_out_le_w_in = c.subst(
        motive2_rhs,
        s_plus_s.clone(),
        w_in.clone(),
        l0_in_symm,
        lhs_w_le,
    );
    // w_out_le_w_in : w_out ≤ w_in.

    // ---- RUNG 2e: strip the outer |·| -----------------------------------
    // 0 ≤ w_out and 0 ≤ w_in via L0 transport of (0 ≤ S'+S') / (0 ≤ S+S).
    // L0 (re-applied) maps `(r+r) ↦ w`; `nonneg_of_sum` transports `0 ≤ r+r`.
    let l0_out2 = Expr::apps(c.l0.clone(), [p.m_i.clone(), s_prime.clone()]);
    let l0_in2 = Expr::apps(c.l0.clone(), [p.c_i.clone(), s.clone()]);
    let h_w_out_nn = nonneg_of_sum(c, parent, &s_prime, &h_sp_nn, &w_out, &sp_plus_sp, l0_out2);
    let h_w_in_nn = nonneg_of_sum(c, parent, &s, &h_s_nn, &w_in, &s_plus_s, l0_in2);

    // abs_of_nonneg w_out h_w_out_nn : |w_out| = w_out.
    let abs_out_eq = Expr::apps(c.abs_of_nonneg.clone(), [w_out.clone(), h_w_out_nn]);
    let abs_in_eq = Expr::apps(c.abs_of_nonneg.clone(), [w_in.clone(), h_w_in_nn]);
    // Goal: |w_out| ≤ |w_in|. Transport w_out_le_w_in:
    //   LHS w_out ↦ |w_out| via symm(abs_out_eq): w_out = |w_out|.
    let abs_w_out = c.abs(w_out.clone());
    let abs_w_in = c.abs(w_in.clone());
    let motive3_lhs = motive_le_left(c, parent, w_in.clone());
    let abs_out_eq_symm = c.symm(abs_w_out.clone(), w_out.clone(), abs_out_eq);
    let lhs_abs_le = c.subst(
        motive3_lhs,
        w_out.clone(),
        abs_w_out.clone(),
        abs_out_eq_symm,
        w_out_le_w_in,
    );
    // lhs_abs_le : |w_out| ≤ w_in. Transport RHS w_in ↦ |w_in|.
    let motive3_rhs = motive_le_right(c, parent, abs_w_out.clone());
    let abs_in_eq_symm = c.symm(abs_w_in.clone(), w_in.clone(), abs_in_eq);
    c.subst(
        motive3_rhs,
        w_in.clone(),
        abs_w_in.clone(),
        abs_in_eq_symm,
        lhs_abs_le,
    )
}

/// `0 ≤ w` where `w = (x+r)−(x−r)` and `rr = r+r`, given `h_rnn : 0 ≤ r` and
/// `l0 : w = rr` (the `L0 x r` proof). `0 ≤ r+r` comes from
/// `add_le_add 0 r 0 r h_rnn h_rnn : (0+0) ≤ (r+r)` (LHS `0+0` ↦ `0` via
/// `add_zero 0`); then transport `(r+r) ↦ w` via `symm l0`.
#[allow(clippy::too_many_arguments)]
fn nonneg_of_sum(
    c: &T21Consts,
    parent: &EnvDeclBuilder,
    r: &Expr,
    h_rnn: &Expr,
    w: &Expr,
    rr: &Expr,
    l0: Expr,
) -> Expr {
    // add_le_add 0 r 0 r h_rnn h_rnn : (0+0) ≤ (r+r).
    let zero = c.rat_zero.clone();
    let sum_nn = Expr::apps(
        c.add_le_add.clone(),
        [
            zero.clone(),
            r.clone(),
            zero.clone(),
            r.clone(),
            h_rnn.clone(),
            h_rnn.clone(),
        ],
    );
    // add_zero 0 : 0+0 = 0. Transport LHS: motive fun y => y ≤ (r+r).
    let zero_plus_zero = c.add(zero.clone(), zero.clone());
    let add_zero_0 = Expr::apps(c.add_zero.clone(), [zero.clone()]);
    let motive = motive_le_left(c, parent, rr.clone());
    let zero_le_rr = c.subst(motive, zero_plus_zero, zero.clone(), add_zero_0, sum_nn);
    // zero_le_rr : 0 ≤ (r+r). Transport RHS (r+r) ↦ w via symm(l0):
    //   l0 : w = (r+r), so symm l0 : (r+r) = w. motive fun y => 0 ≤ y.
    let motive_r = motive_le_right(c, parent, zero.clone());
    let l0_symm = c.symm(w.clone(), rr.clone(), l0);
    c.subst(motive_r, rr.clone(), w.clone(), l0_symm, zero_le_rr)
}

/// `motive : fun (y : Rat) => lhs ≤ y` (`lhs` may reference parent FVars).
fn motive_le_right(c: &T21Consts, parent: &EnvDeclBuilder, lhs: Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let (y_id, y) = d.fresh_local(c.rat.clone());
    let body = c.rat_le(lhs, y);
    d.finish_child(d.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), body))
}

/// `motive : fun (y : Rat) => y ≤ rhs`.
fn motive_le_left(c: &T21Consts, parent: &EnvDeclBuilder, rhs: Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let (y_id, y) = d.fresh_local(c.rat.clone());
    let body = c.rat_le(y, rhs);
    d.finish_child(d.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), body))
}

// ---------------------------------------------------------------------------
// T21 (RUNG 3): the GAIN-BOUND theorem, by Fin.sum_le over L2.
// ---------------------------------------------------------------------------

/// T21 type (the GAIN-BOUND form): the registered conclusion with the gain
/// hypothesis `h : ∀ i, |γ i| ≤ 1` inserted between the `z` Pi and the body.
fn build_t21_type(c: &T21Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(&n);
    let zono_nk = c.zono_of(&n, &k);
    let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
    let (beta_id, beta) = b.fresh_local(vec_n.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (z_id, z) = b.fresh_local(zono_nk.clone());
    let fin_n = c.fin_of(&n);

    // h : ∀ (i : Fin n), |γ i| ≤ 1.
    let h_ty = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let body = c.rat_le(c.abs(Expr::app(gamma.clone(), i)), c.rat_one.clone());
        d.finish_child(d.mk_pi(i_id, BinderInfo::Default, fin_n.clone(), body))
    };

    // Conclusion: l1(width(zonotope_output …)) ≤ l1(width(to_ibp …)).
    let out = c.zout(&n, &k, &gamma, &beta, &eps, &z);
    let l1_out = c.l1(&n, c.width_vec(&n, out));
    let ibp = c.to_ibp(&n, &k, &z);
    let l1_ibp = c.l1(&n, c.width_vec(&n, ibp));
    let concl = c.rat_le(l1_out, l1_ibp);

    let (h_id, _h) = b.fresh_local(h_ty.clone());
    let r = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
    let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
    let r = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), r);
    let r = b.mk_pi(beta_id, BinderInfo::Default, vec_n.clone(), r);
    let r = b.mk_pi(gamma_id, BinderInfo::Default, vec_n, r);
    let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

/// T21 value: `fun n k γ β ε z h => Fin.sum_le n F G (fun i => L2 … i (h i))`,
/// `F = fun i => |width(out)_i|`, `G = fun i => |width(in)_i|`. The
/// `Fin.sum_le` result type is defeq (l1_norm/width δ) to the T21 conclusion.
fn build_t21_value(c: &T21Consts) -> Expr {
    let l2 = Expr::const_(Name::from_string(L2_NAME), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(&n);
    let zono_nk = c.zono_of(&n, &k);
    let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
    let (beta_id, beta) = b.fresh_local(vec_n.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (z_id, z) = b.fresh_local(zono_nk.clone());
    let fin_n = c.fin_of(&n);
    let h_ty = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let body = c.rat_le(c.abs(Expr::app(gamma.clone(), i)), c.rat_one.clone());
        d.finish_child(d.mk_pi(i_id, BinderInfo::Default, fin_n.clone(), body))
    };
    let (h_id, h) = b.fresh_local(h_ty.clone());

    // F = fun i => |width(out)_i| ; G = fun i => |width(in)_i|.
    let out = c.zout(&n, &k, &gamma, &beta, &eps, &z);
    let ibp = c.to_ibp(&n, &k, &z);
    let f_out = abs_width_fn(c, &b, &n, out);
    let g_in = abs_width_fn(c, &b, &n, ibp);

    // pointwise : fun (i : Fin n) => L2 n k γ β ε z i (h i) : F i ≤ G i.
    let pointwise = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let h_i = Expr::app(h.clone(), i.clone());
        let body = Expr::apps(
            l2.clone(),
            [
                n.clone(),
                k.clone(),
                gamma.clone(),
                beta.clone(),
                eps.clone(),
                z.clone(),
                i.clone(),
                h_i,
            ],
        );
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), body))
    };

    // Fin.sum_le n F G pointwise : Fin.sum n F ≤ Fin.sum n G.
    //   Defeq to l1(width(out)) ≤ l1(width(in)) via l1_norm/width δ.
    let proof = Expr::apps(c.fin_sum_le.clone(), [n.clone(), f_out, g_in, pointwise]);

    let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, proof);
    let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, e);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_lam(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

impl Environment {
    /// Register the `(x+r)−(x−r) = r+r` cancellation lemma (L0) used by T21.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_rat_add_sub_sub_self_eq_add(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string(L0_NAME);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = T21Consts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_l0_type(&c),
            value: build_l0_proof(&c),
        })
    }

    /// Register the per-component gain-bound lemma L2.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_width_out_le_width_in_pointwise(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string(L2_NAME);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = T21Consts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_l2_type(&c),
            value: build_l2_value(&c),
        })
    }

    /// T21 `NNVerify.LayerNorm.zonotope_width_preserved` — the GAIN-BOUND
    /// theorem. Retires the body-less #3509 Branch A Axiom (domain TCB 5 → 4).
    /// See the module docs for the statement and the full proof plan.
    ///
    /// Wires the brick inits (idempotent), registers L0 + L2, then the T21
    /// Theorem. The kernel checks the proof at `add_decl`.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_t21_layernorm_width_preserved(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string(T21_NAME);
        // Short-circuit only once the faithful Theorem (with a proof value) is in
        // place — replace the legacy body-less Axiom otherwise.
        if self.get_const(&name).is_some_and(|ci| ci.value.is_some()) {
            return Ok(());
        }

        // Brick inits (idempotent). `init_fin_sum` brings Fin.sum_le / _smul /
        // _nonneg; `register_fin_sum_congr` brings Fin.sum_congr; the order
        // toolkit brings Rat.mul_le_mul_of_nonneg_right (and Rat.mul_nonneg,
        // Rat.one_mul transitively); `init_rat_abs` brings the Rat.abs_* family;
        // `register_rat_add_le_add` brings Rat.add_le_add; `Rat.sub_add_sub`
        // backs L0.
        self.init_fin_sum()?;
        {
            let fc = super::nn_verify_fin_sum::FinSumConsts::new();
            self.register_fin_sum_congr(&fc)?;
        }
        self.init_rat_abs()?;
        self.init_boolean_analysis_order_toolkit()?;
        self.register_rat_add_le_add()?;
        self.register_rat_sub_add_sub_theorem()?;
        self.register_rat_add_sub_sub_self_eq_add()?;
        self.register_width_out_le_width_in_pointwise()?;

        let c = T21Consts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_t21_type(&c),
            value: build_t21_value(&c),
        })
    }
}
