// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — the noise-density **point peel**: how the
//! un-normalized ρ-correlated density `noiseDensityW` factors when both cube
//! points gain a top coordinate.
//!
//! ```text
//! BoolAnalysis.noiseDensityW_point_peel_<b><c> :
//!   ∀ (ρ : Rat) (n : Nat) (x y : HCPoint n),
//!     noiseDensityW ρ (n+1) (extend_b n x) (extend_c n y)
//!       = Rat.mul (noiseDensityW ρ n x y)
//!                 (1 + ρ · (pm <bit_b> · pm <bit_c>))
//! ```
//!
//! where `<b><c>` ranges over the four extension-map choices `ff`, `ft`, `tf`,
//! `tt` (LOW/HIGH top bit on each of `x` / `y`), `extend_b ∈ {extendF, extendT}`,
//! and `bit_b ∈ {Bool.false, Bool.true}` the appended bit.
//!
//! This is the multiplicative coordinate-peel of the correlated density: the new
//! top coordinate contributes exactly one product factor `1 + ρ·pm(b)·pm(c)`,
//! the prefix is the `n`-level density on the restricted points. It is the
//! density-level companion of the function-level `peel_reconstruct`, and the raw
//! material the operator peel `noiseFn_succ` consumes (one factor per cube half).
//!
//! ## Proof route
//!
//! Both sides run through the closed product form `noiseDensityW_eq_prod`:
//! `noiseDensityW ρ m u v = Fin.prod m (fun i => 1 + ρ·(pm(u i)·pm(v i)))`.
//!
//! 1. `noiseDensityW_eq_prod` on the LHS: rewrite the `(n+1)`-density to
//!    `Fin.prod (n+1) (integ_{n+1})` with `integ_{n+1} i = 1+ρ·(pm((ext_b x) i)·
//!    pm((ext_c y) i))`.
//! 2. `Fin.prod_succ`: peel the `(n+1)`-product to
//!    `Rat.mul (Fin.prod n (integ_{n+1}∘castSucc)) (integ_{n+1}(last n))`.
//! 3. **prefix** — `Fin.prod_congr` lifts the leaf-wise identity
//!    `integ_{n+1}(castSucc i) = integ_n x y i` (each obtained by `congrArg pm`
//!    on `extend_b_castSucc : (ext_b x)(castSucc i) = x i`) to
//!    `Fin.prod n (integ_{n+1}∘castSucc) = Fin.prod n (integ_n x y)`, then
//!    `Eq.symm (noiseDensityW_eq_prod ρ n x y)` folds the `Fin.prod n (integ_n x
//!    y)` back to `noiseDensityW ρ n x y`.
//! 4. **last factor** — `integ_{n+1}(last n) = 1+ρ·(pm bit_b · pm bit_c)` by
//!    `congrArg pm` on `extend_b_last : (ext_b x)(last n) = bit_b`.
//! 5. Congruence into `Rat.mul` reassembles `Rat.mul (noiseDensityW ρ n x y)
//!    (1+ρ·(pm bit_b · pm bit_c))`.
//!
//! All four are `ProofQuality::Constructive` with empty domain-axiom closure
//! (closure ⊆ {`noiseDensityW_eq_prod`, `Fin.prod_succ`, `Fin.prod_congr`,
//! `extend*_castSucc`, `extend*_last`} ∪ `Eq`/`congrArg` built-ins).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for the noise-density point peel.
struct NoisePeelConsts {
    l1: Level,
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    nat_succ: Expr,
    fin: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_add: Expr,
    pm: Expr,
    bool_false: Expr,
    bool_true: Expr,
    extend_f: Expr,
    extend_t: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    fin_prod: Expr,
    fin_prod_succ: Expr,
    fin_prod_congr: Expr,
    noise_density: Expr,
    noise_density_eq_prod: Expr,
    hcpoint: Expr,
}

impl NoisePeelConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            l1,
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            pm: Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]),
            bool_false: Expr::const_(Name::from_string("Bool.false"), vec![]),
            bool_true: Expr::const_(Name::from_string("Bool.true"), vec![]),
            extend_f: Expr::const_(Name::from_string("BoolAnalysis.extendF"), vec![]),
            extend_t: Expr::const_(Name::from_string("BoolAnalysis.extendT"), vec![]),
            fin_cast_succ: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            fin_prod: Expr::const_(Name::from_string("Fin.prod"), vec![]),
            fin_prod_succ: Expr::const_(Name::from_string("Fin.prod_succ"), vec![]),
            fin_prod_congr: Expr::const_(Name::from_string("Fin.prod_congr"), vec![]),
            noise_density: Expr::const_(Name::from_string("BoolAnalysis.noiseDensityW"), vec![]),
            noise_density_eq_prod: Expr::const_(
                Name::from_string("BoolAnalysis.noiseDensityW_eq_prod"),
                vec![],
            ),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn pm_of(&self, b: Expr) -> Expr {
        Expr::app(self.pm.clone(), b)
    }
    /// The extension-map constant for the chosen top bit.
    fn extend_const(&self, use_true: bool) -> &Expr {
        if use_true {
            &self.extend_t
        } else {
            &self.extend_f
        }
    }
    /// The appended bit (`Bool.false` / `Bool.true`).
    fn bit(&self, use_true: bool) -> &Expr {
        if use_true {
            &self.bool_true
        } else {
            &self.bool_false
        }
    }
    /// `extend_b n x` — the chosen extension of `x` by one top bit.
    fn extend(&self, use_true: bool, n: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.extend_const(use_true).clone(), [n.clone(), x.clone()])
    }
    /// `Fin.castSucc n i`.
    fn cast_succ(&self, n: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.fin_cast_succ.clone(), [n.clone(), i.clone()])
    }
    /// `Fin.last n`.
    fn last(&self, n: &Expr) -> Expr {
        Expr::app(self.fin_last.clone(), n.clone())
    }
    /// `noiseDensityW ρ n x y`.
    fn density(&self, rho: &Expr, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.noise_density.clone(),
            [rho.clone(), n.clone(), x.clone(), y.clone()],
        )
    }
    /// `noiseDensityW_eq_prod ρ n x y`.
    fn density_eq_prod(&self, rho: &Expr, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.noise_density_eq_prod.clone(),
            [rho.clone(), n.clone(), x.clone(), y.clone()],
        )
    }
    /// `Fin.prod n f`.
    fn prod(&self, n: &Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_prod.clone(), [n.clone(), f])
    }
    /// The per-coordinate density integrand `1 + ρ·(pm(u i)·pm(v i))`, applied at
    /// a *concrete* index expression (the body of `prod_int_rho`).
    fn integ_at(&self, rho: &Expr, u: &Expr, v: &Expr, idx: &Expr) -> Expr {
        let pm_u = self.pm_of(Expr::app(u.clone(), idx.clone()));
        let pm_v = self.pm_of(Expr::app(v.clone(), idx.clone()));
        self.add(
            self.rat_one.clone(),
            self.mul(rho.clone(), self.mul(pm_u, pm_v)),
        )
    }
    /// The integrand function `fun (i : Fin m) => 1 + ρ·(pm(u i)·pm(v i))`,
    /// byte-for-byte the `prod_int_rho` build (so `noiseDensityW_eq_prod`'s RHS
    /// product is defeq to `Fin.prod m (this)`).
    fn integ_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, m: &Expr, u: &Expr, v: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_m = self.fin_of(m);
        let (i_id, i) = b.fresh_local(fin_m.clone());
        let body = self.integ_at(rho, u, v, &i);
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_m, body))
    }
    /// `@Eq Rat l r`.
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.rat.clone(), l, r],
        )
    }
    /// `@Eq Bool l r`.
    fn eq_bool(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.bool_.clone(), l, r],
        )
    }
    /// `@Eq.trans Rat a b c h1 h2`.
    fn trans_rat(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, c, h1, h2],
        )
    }
    /// `@Eq.symm Rat a b h`.
    fn symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, h],
        )
    }
    /// `@congrArg α Rat from to f h` for a unary `f : α → Rat`.
    fn congr_arg_to_rat(&self, alpha: Expr, from: Expr, to: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [alpha, self.rat.clone(), from, to, f, h],
        )
    }
}

impl Environment {
    /// Initialize the four noise-density point-peel lemmas (`ff`/`ft`/`tf`/`tt`).
    /// Idempotent; axiom-free.
    pub(crate) fn init_boolean_analysis_noise_peel(&mut self) -> Result<(), EnvError> {
        if self.boolean_analysis_noise_peel_init {
            return Ok(());
        }
        self.init_eq()?;
        self.register_noise_density_w()?;
        self.register_noise_density_w_eq_prod_theorem()?;
        self.register_fin_prod_succ_theorem()?;
        self.register_fin_prod_one_theorems()?; // Fin.prod_congr
        self.init_boolean_analysis_peel()?; // extendF / extendT
        self.init_boolean_analysis_peel_compute()?; // extend*_castSucc / extend*_last
        self.init_boolean_analysis()?; // BoolAnalysis.pm

        let c = NoisePeelConsts::new();
        for (b_use_true, c_use_true, suffix) in [
            (false, false, "ff"),
            (false, true, "ft"),
            (true, false, "tf"),
            (true, true, "tt"),
        ] {
            let name =
                Name::from_string(&format!("BoolAnalysis.noiseDensityW_point_peel_{suffix}"));
            if self.get_const(&name).is_none() {
                let (ty, value) = build_point_peel(&c, b_use_true, c_use_true);
                self.add_decl(Declaration::Theorem {
                    name,
                    level_params: vec![],
                    type_: ty,
                    value,
                })?;
            }
        }

        self.boolean_analysis_noise_peel_init = true;
        Ok(())
    }

    /// Whether the noise-density point-peel lemmas have been initialized.
    pub(crate) fn has_boolean_analysis_noise_peel(&self) -> bool {
        self.boolean_analysis_noise_peel_init
    }
}

/// Build the type + proof of one `noiseDensityW_point_peel_<b><c>` lemma.
fn build_point_peel(c: &NoisePeelConsts, b_use_true: bool, c_use_true: bool) -> (Expr, Expr) {
    let ty = build_point_peel_type(c, b_use_true, c_use_true);
    let value = build_point_peel_value(c, b_use_true, c_use_true);
    (ty, value)
}

/// `∀ ρ n x y, noiseDensityW ρ (n+1) (ext_b x) (ext_c y) =
///   noiseDensityW ρ n x y · (1 + ρ·(pm bit_b · pm bit_c))`.
fn build_point_peel_type(c: &NoisePeelConsts, b_use_true: bool, c_use_true: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (y_id, y) = b.fresh_local(hcp.clone());

    let ext_x = c.extend(b_use_true, &n, &x);
    let ext_y = c.extend(c_use_true, &n, &y);
    let lhs = c.density(&rho, &c.succ(&n), &ext_x, &ext_y);
    let top_factor = {
        let pm_b = c.pm_of(c.bit(b_use_true).clone());
        let pm_c = c.pm_of(c.bit(c_use_true).clone());
        c.add(c.rat_one.clone(), c.mul(rho.clone(), c.mul(pm_b, pm_c)))
    };
    let rhs = c.mul(c.density(&rho, &n, &x, &y), top_factor);
    let concl = c.eq_rat(lhs, rhs);

    let e = b.mk_pi(y_id, BinderInfo::Default, hcp.clone(), concl);
    let e = b.mk_pi(x_id, BinderInfo::Default, hcp, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Proof of `noiseDensityW_point_peel_<b><c>`.
fn build_point_peel_value(c: &NoisePeelConsts, b_use_true: bool, c_use_true: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (y_id, y) = b.fresh_local(hcp.clone());

    let succ_n = c.succ(&n);
    let ext_x = c.extend(b_use_true, &n, &x);
    let ext_y = c.extend(c_use_true, &n, &y);

    // integ_{n+1} : Fin (n+1) → Rat, the (n+1)-density integrand on (ext_x, ext_y).
    let integ_succ = c.integ_fn(&b, &rho, &succ_n, &ext_x, &ext_y);
    // integ_n : Fin n → Rat, the n-density integrand on (x, y).
    let integ_n = c.integ_fn(&b, &rho, &n, &x, &y);

    // ── Step 1 : noiseDensityW_eq_prod ρ (n+1) (ext_x) (ext_y).
    //   h1 : noiseDensityW ρ (n+1) ext_x ext_y = Fin.prod (n+1) integ_{n+1}
    let lhs = c.density(&rho, &succ_n, &ext_x, &ext_y);
    let prod_succ_full = c.prod(&succ_n, integ_succ.clone());
    let h1 = c.density_eq_prod(&rho, &succ_n, &ext_x, &ext_y);

    // ── Step 2 : Fin.prod_succ n integ_{n+1}.
    //   h2 : Fin.prod (n+1) integ_{n+1}
    //          = Rat.mul (Fin.prod n (integ_{n+1}∘castSucc)) (integ_{n+1}(last n))
    let h2 = Expr::apps(c.fin_prod_succ.clone(), [n.clone(), integ_succ.clone()]);
    // prefix function: fun (i : Fin n) => integ_{n+1} (castSucc n i)
    let prefix_fn = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let body = Expr::app(integ_succ.clone(), c.cast_succ(&n, &i));
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };
    let prod_prefix = c.prod(&n, prefix_fn.clone());
    let last_factor = Expr::app(integ_succ.clone(), c.last(&n));
    let mul_prefix_last = c.mul(prod_prefix.clone(), last_factor.clone());

    // ── Step 3 : prefix product folds back to noiseDensityW ρ n x y.
    //   leaf : ∀ i : Fin n, integ_{n+1}(castSucc i) = integ_n x y i
    let leaf_proof = build_prefix_leaf(c, &b, b_use_true, c_use_true, &rho, &n, &x, &y);
    let prod_n_integ_n = c.prod(&n, integ_n.clone());
    //   congr : Fin.prod n (prefix_fn) = Fin.prod n integ_n
    let prod_congr = Expr::apps(
        c.fin_prod_congr.clone(),
        [n.clone(), prefix_fn.clone(), integ_n.clone(), leaf_proof],
    );
    //   fold : Fin.prod n integ_n = noiseDensityW ρ n x y  (Eq.symm of eq_prod)
    let density_n = c.density(&rho, &n, &x, &y);
    let fold = c.symm_rat(
        density_n.clone(),
        prod_n_integ_n.clone(),
        c.density_eq_prod(&rho, &n, &x, &y),
    );
    //   prefix_eq : Fin.prod n prefix_fn = noiseDensityW ρ n x y
    let prefix_eq = c.trans_rat(
        prod_prefix.clone(),
        prod_n_integ_n,
        density_n.clone(),
        prod_congr,
        fold,
    );

    // ── Step 4 : last factor = 1 + ρ·(pm bit_b · pm bit_c).
    let top_factor = {
        let pm_b = c.pm_of(c.bit(b_use_true).clone());
        let pm_c = c.pm_of(c.bit(c_use_true).clone());
        c.add(c.rat_one.clone(), c.mul(rho.clone(), c.mul(pm_b, pm_c)))
    };
    let last_eq = build_last_factor(c, &b, b_use_true, c_use_true, &rho, &n, &x, &y);

    // ── Step 5 : reassemble Rat.mul.
    //   congr on first slot:  (prod_prefix · last_factor) = (density_n · last_factor)
    let mul_by_last = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (s_id, s) = d.fresh_local(c.rat.clone());
        let body = c.mul(s, last_factor.clone());
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let step_first = c.congr_arg_to_rat(
        c.rat.clone(),
        prod_prefix.clone(),
        density_n.clone(),
        mul_by_last,
        prefix_eq,
    );
    let mid = c.mul(density_n.clone(), last_factor.clone());
    //   congr on second slot: (density_n · last_factor) = (density_n · top_factor)
    let mul_density = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (s_id, s) = d.fresh_local(c.rat.clone());
        let body = c.mul(density_n.clone(), s);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let step_second = c.congr_arg_to_rat(
        c.rat.clone(),
        last_factor.clone(),
        top_factor.clone(),
        mul_density,
        last_eq,
    );
    let rhs = c.mul(density_n.clone(), top_factor);

    // Chain: lhs = prod_succ_full = mul_prefix_last = mid = rhs.
    let t1 = c.trans_rat(
        lhs.clone(),
        prod_succ_full.clone(),
        mul_prefix_last.clone(),
        h1,
        h2,
    );
    let t2 = c.trans_rat(
        lhs.clone(),
        mul_prefix_last.clone(),
        mid.clone(),
        t1,
        step_first,
    );
    let proof = c.trans_rat(lhs, mid, rhs, t2, step_second);

    let e = b.mk_lam(y_id, BinderInfo::Default, hcp.clone(), proof);
    let e = b.mk_lam(x_id, BinderInfo::Default, hcp, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// The leaf-wise prefix identity proof:
/// `fun (i : Fin n) => <proof : integ_{n+1}(castSucc i) = integ_n x y i>`.
///
/// Both sides are `1 + ρ·(pm A · pm B)`. The LHS pm-arguments are
/// `(ext_b x)(castSucc i)` / `(ext_c y)(castSucc i)`; the RHS are `x i` / `y i`.
/// `congrArg pm (extend_b_castSucc n x i)` bridges each, and a two-step `congrArg`
/// chain lifts the bridge through `pm A · pm B` then `1 + ρ·(·)`.
#[allow(clippy::too_many_arguments)]
fn build_prefix_leaf(
    c: &NoisePeelConsts,
    parent: &EnvDeclBuilder,
    b_use_true: bool,
    c_use_true: bool,
    rho: &Expr,
    n: &Expr,
    x: &Expr,
    y: &Expr,
) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (i_id, i) = d.fresh_local(fin_n.clone());

    let ext_x = c.extend(b_use_true, n, x);
    let ext_y = c.extend(c_use_true, n, y);
    let cs = c.cast_succ(n, &i);

    // A  = (ext_x)(castSucc i),  A' = x i ;  B = (ext_y)(castSucc i),  B' = y i.
    let a = Expr::app(ext_x.clone(), cs.clone());
    let a_prime = Expr::app(x.clone(), i.clone());
    let bb = Expr::app(ext_y.clone(), cs.clone());
    let b_prime = Expr::app(y.clone(), i.clone());

    // extend_b_castSucc n x i : (ext_x)(castSucc i) = x i.
    let cast_lemma_b = extend_castsucc_lemma(c, b_use_true, n, x, &i);
    let cast_lemma_c = extend_castsucc_lemma(c, c_use_true, n, y, &i);

    // ea : pm A = pm A'  ;  eb : pm B = pm B'.
    let ea = c.congr_arg_to_rat(
        c.bool_.clone(),
        a.clone(),
        a_prime.clone(),
        c.pm.clone(),
        cast_lemma_b,
    );
    let eb = c.congr_arg_to_rat(
        c.bool_.clone(),
        bb.clone(),
        b_prime.clone(),
        c.pm.clone(),
        cast_lemma_c,
    );

    let pm_a = c.pm_of(a);
    let pm_a_prime = c.pm_of(a_prime);
    let pm_b = c.pm_of(bb);
    let pm_b_prime = c.pm_of(b_prime);

    // Lift ea, eb through `pm A · pm B → pm A' · pm B'`:
    //   m1 : pm A · pm B = pm A' · pm B   (congr on first mul slot)
    let mul_by_pm_b = {
        let mut e = EnvDeclBuilder::child_of(&d);
        let (s_id, s) = e.fresh_local(c.rat.clone());
        let body = c.mul(s, pm_b.clone());
        e.finish_child(e.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let m1 = c.congr_arg_to_rat(
        c.rat.clone(),
        pm_a.clone(),
        pm_a_prime.clone(),
        mul_by_pm_b,
        ea,
    );
    //   m2 : pm A' · pm B = pm A' · pm B'   (congr on second mul slot)
    let mul_pm_a_prime = {
        let mut e = EnvDeclBuilder::child_of(&d);
        let (s_id, s) = e.fresh_local(c.rat.clone());
        let body = c.mul(pm_a_prime.clone(), s);
        e.finish_child(e.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let m2 = c.congr_arg_to_rat(
        c.rat.clone(),
        pm_b.clone(),
        pm_b_prime.clone(),
        mul_pm_a_prime,
        eb,
    );
    let prod_a = c.mul(pm_a.clone(), pm_b.clone());
    let prod_ab_mixed = c.mul(pm_a_prime.clone(), pm_b.clone());
    let prod_a_prime = c.mul(pm_a_prime.clone(), pm_b_prime.clone());
    //   mprod : pm A · pm B = pm A' · pm B'
    let mprod = c.trans_rat(prod_a.clone(), prod_ab_mixed, prod_a_prime.clone(), m1, m2);

    // Lift mprod through `1 + ρ·(·)`:
    //   r1 : ρ·(pm A·pm B) = ρ·(pm A'·pm B')
    let mul_rho = {
        let mut e = EnvDeclBuilder::child_of(&d);
        let (s_id, s) = e.fresh_local(c.rat.clone());
        let body = c.mul(rho.clone(), s);
        e.finish_child(e.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let r1 = c.congr_arg_to_rat(
        c.rat.clone(),
        prod_a.clone(),
        prod_a_prime.clone(),
        mul_rho,
        mprod,
    );
    //   r2 : (1 + ρ·(pm A·pm B)) = (1 + ρ·(pm A'·pm B'))
    let rho_prod_a = c.mul(rho.clone(), prod_a);
    let rho_prod_a_prime = c.mul(rho.clone(), prod_a_prime);
    let add_one = {
        let mut e = EnvDeclBuilder::child_of(&d);
        let (s_id, s) = e.fresh_local(c.rat.clone());
        let body = c.add(c.rat_one.clone(), s);
        e.finish_child(e.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let r2 = c.congr_arg_to_rat(c.rat.clone(), rho_prod_a, rho_prod_a_prime, add_one, r1);

    d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, r2))
}

/// The last-factor identity proof:
/// `integ_{n+1}(last n) = 1 + ρ·(pm bit_b · pm bit_c)`.
/// `(ext_b x)(last n) = bit_b` by `extend_b_last`, lifted through `pm` and the
/// `1 + ρ·(·)` shape exactly as the prefix leaf.
#[allow(clippy::too_many_arguments)]
fn build_last_factor(
    c: &NoisePeelConsts,
    parent: &EnvDeclBuilder,
    b_use_true: bool,
    c_use_true: bool,
    rho: &Expr,
    n: &Expr,
    x: &Expr,
    y: &Expr,
) -> Expr {
    let ext_x = c.extend(b_use_true, n, x);
    let ext_y = c.extend(c_use_true, n, y);
    let last = c.last(n);

    // A  = (ext_x)(last n),  A' = bit_b ;  B = (ext_y)(last n),  B' = bit_c.
    let a = Expr::app(ext_x.clone(), last.clone());
    let a_prime = c.bit(b_use_true).clone();
    let bb = Expr::app(ext_y.clone(), last.clone());
    let b_prime = c.bit(c_use_true).clone();

    let last_lemma_b = extend_last_lemma(c, b_use_true, n, x);
    let last_lemma_c = extend_last_lemma(c, c_use_true, n, y);

    let ea = c.congr_arg_to_rat(
        c.bool_.clone(),
        a.clone(),
        a_prime.clone(),
        c.pm.clone(),
        last_lemma_b,
    );
    let eb = c.congr_arg_to_rat(
        c.bool_.clone(),
        bb.clone(),
        b_prime.clone(),
        c.pm.clone(),
        last_lemma_c,
    );

    let pm_a = c.pm_of(a);
    let pm_a_prime = c.pm_of(a_prime);
    let pm_b = c.pm_of(bb);
    let pm_b_prime = c.pm_of(b_prime);

    let mul_by_pm_b = {
        let mut e = EnvDeclBuilder::child_of(parent);
        let (s_id, s) = e.fresh_local(c.rat.clone());
        let body = c.mul(s, pm_b.clone());
        e.finish_child(e.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let m1 = c.congr_arg_to_rat(
        c.rat.clone(),
        pm_a.clone(),
        pm_a_prime.clone(),
        mul_by_pm_b,
        ea,
    );
    let mul_pm_a_prime = {
        let mut e = EnvDeclBuilder::child_of(parent);
        let (s_id, s) = e.fresh_local(c.rat.clone());
        let body = c.mul(pm_a_prime.clone(), s);
        e.finish_child(e.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let m2 = c.congr_arg_to_rat(
        c.rat.clone(),
        pm_b.clone(),
        pm_b_prime.clone(),
        mul_pm_a_prime,
        eb,
    );
    let prod_a = c.mul(pm_a.clone(), pm_b.clone());
    let prod_ab_mixed = c.mul(pm_a_prime.clone(), pm_b.clone());
    let prod_a_prime = c.mul(pm_a_prime.clone(), pm_b_prime.clone());
    let mprod = c.trans_rat(prod_a.clone(), prod_ab_mixed, prod_a_prime.clone(), m1, m2);

    let mul_rho = {
        let mut e = EnvDeclBuilder::child_of(parent);
        let (s_id, s) = e.fresh_local(c.rat.clone());
        let body = c.mul(rho.clone(), s);
        e.finish_child(e.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let r1 = c.congr_arg_to_rat(
        c.rat.clone(),
        prod_a.clone(),
        prod_a_prime.clone(),
        mul_rho,
        mprod,
    );
    let rho_prod_a = c.mul(rho.clone(), prod_a);
    let rho_prod_a_prime = c.mul(rho.clone(), prod_a_prime);
    let add_one = {
        let mut e = EnvDeclBuilder::child_of(parent);
        let (s_id, s) = e.fresh_local(c.rat.clone());
        let body = c.add(c.rat_one.clone(), s);
        e.finish_child(e.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), body))
    };
    c.congr_arg_to_rat(c.rat.clone(), rho_prod_a, rho_prod_a_prime, add_one, r1)
}

/// `extend_b_castSucc n x i : (extend_b n x)(Fin.castSucc n i) = x i`.
fn extend_castsucc_lemma(
    c: &NoisePeelConsts,
    use_true: bool,
    n: &Expr,
    x: &Expr,
    i: &Expr,
) -> Expr {
    let name = if use_true {
        "BoolAnalysis.extendT_castSucc"
    } else {
        "BoolAnalysis.extendF_castSucc"
    };
    let _ = c;
    Expr::apps(
        Expr::const_(Name::from_string(name), vec![]),
        [n.clone(), x.clone(), i.clone()],
    )
}

/// `extend_b_last n x : (extend_b n x)(Fin.last n) = bit_b`.
fn extend_last_lemma(c: &NoisePeelConsts, use_true: bool, n: &Expr, x: &Expr) -> Expr {
    let name = if use_true {
        "BoolAnalysis.extendT_last"
    } else {
        "BoolAnalysis.extendF_last"
    };
    let _ = c;
    Expr::apps(
        Expr::const_(Name::from_string(name), vec![]),
        [n.clone(), x.clone()],
    )
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    const PEELS: &[&str] = &[
        "BoolAnalysis.noiseDensityW_point_peel_ff",
        "BoolAnalysis.noiseDensityW_point_peel_ft",
        "BoolAnalysis.noiseDensityW_point_peel_tf",
        "BoolAnalysis.noiseDensityW_point_peel_tt",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_noise_peel()
            .expect("init_boolean_analysis_noise_peel");
        env
    }

    #[test]
    fn test_init_idempotent() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_noise_peel().expect("first init");
        env.init_boolean_analysis_noise_peel()
            .expect("second init should be a no-op");
        assert!(env.has_boolean_analysis_noise_peel());
    }

    #[test]
    fn test_point_peels_are_constructive_theorems() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name_str in PEELS {
            let name = Name::from_string(name_str);
            let info = env
                .get_const(&name)
                .unwrap_or_else(|| panic!("{name_str} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name_str} is a Theorem");
            let value = info.value.clone().expect("proof present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name_str} proof must check: {e:?}"));
            let deps = env.axiom_deps(&name).expect("deps");
            let dep_names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
            assert!(
                dep_names.is_empty(),
                "{name_str} must be axiom-free, got {dep_names:?}"
            );
            assert_eq!(
                env.proof_quality(&name),
                Some(ProofQuality::Constructive),
                "{name_str} must be Constructive"
            );
        }
    }
}
