// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — the **operator-peel half-split** of `noiseFn`.
//!
//! The un-normalized noise operator `noiseFn ρ (n+1) F jx` is a sum over the
//! `2^(n+1)` cube points `jy`. `hcSumSplit` splits that sum into the LOW / HIGH
//! cube halves, and the decode↔extend bridges identify each half's reindexed
//! point as an `extendF` / `extendT` of the `n`-level decode. The result is the
//! operator-level cube-bit recursion:
//!
//! ```text
//! BoolAnalysis.noiseFn_succ_split :
//!   ∀ (ρ : Rat) (n : Nat) (F : HCPoint (n+1) → Rat) (jx : Fin (2^(n+1))),
//!     noiseFn ρ (n+1) F jx
//!       = Rat.add
//!           (Fin.sum (2^n) (fun i =>
//!              Rat.mul (F (extendF n (hcDecode n i)))
//!                      (noiseDensityW ρ (n+1) (hcDecode (n+1) jx)
//!                                            (extendF n (hcDecode n i)))))
//!           (Fin.sum (2^n) (fun j =>
//!              Rat.mul (F (extendT n (hcDecode n j)))
//!                      (noiseDensityW ρ (n+1) (hcDecode (n+1) jx)
//!                                            (extendT n (hcDecode n j)))))
//! ```
//!
//! This is the structural half-split the `hc24` operator induction consumes:
//! the `(n+1)`-cube sum becomes two `2^n` half-sums, one over the `extendF`
//! (top bit 0) images and one over the `extendT` (top bit 1) images. The next
//! run applies the density point-peel (`noiseDensityW_point_peel_*`) to each
//! `noiseDensityW ρ (n+1) (extend_b …) (extend_c …)` factor — pinning the outer
//! point `hcDecode (n+1) jx` to `extend_b (hcDecode n jx')` — to peel the
//! correlated weight and regroup into the `gPart` / `−hPart` lifted integrands.
//!
//! ## Proof route
//!
//! 1. `noiseFn ρ (n+1) F jx` δ-unfolds to `Fin.sum (2^(n+1)) (fun jy =>
//!    g (hcDecode (n+1) jy))` with `g p := F p · noiseDensityW ρ (n+1) X p`
//!    (`X := hcDecode (n+1) jx`) — exactly the `hcSumSplit` LHS shape.
//! 2. `hcSumSplit n g` splits it into `Rat.add LOW HIGH` with
//!    `LOW i = g (hcDecode (n+1) (castP (castAdd i)))`,
//!    `HIGH j = g (hcDecode (n+1) (castP (addNat j)))`.
//! 3. `Fin.sum_congr` rewrites each half's integrand via the decode↔extend
//!    bridge (`congrArg g` on `hcDecode_castP_*_extend*`), folding
//!    `g (hcDecode (n+1) (castP (castAdd i)))` to `g (extendF n (hcDecode n i))`
//!    (and the `extendT` mirror).
//!
//! Kernel-checked, `ProofQuality::Constructive` (empty domain-axiom closure):
//! leaves are `hcSumSplit`, `Fin.sum_congr`, the decode↔extend bridges, and
//! `congrArg` / `Eq.*` built-ins.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for the `noiseFn` half-split.
struct NoiseFnSplitConsts {
    l1: Level,
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    nat_add: Expr,
    two: Expr,
    fin: Expr,
    rat_mul: Expr,
    rat_add: Expr,
    fin_sum: Expr,
    fin_sum_congr: Expr,
    hcpoint: Expr,
    hc_decode: Expr,
    noise_density: Expr,
    noise_fn: Expr,
    hc_sum_split: Expr,
    extend_f: Expr,
    extend_t: Expr,
    cast_add: Expr,
    add_nat: Expr,
    pow_two_succ: Expr,
    eq_symm_nat: Expr,
    eq_ndrec_fin: Expr,
}

impl NoiseFnSplitConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let one = Expr::app(nat_succ.clone(), nat_zero);
        let two = Expr::app(nat_succ.clone(), one);
        Self {
            l1: l1.clone(),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            nat_succ,
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            two,
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin_sum_congr: Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            noise_density: Expr::const_(Name::from_string("BoolAnalysis.noiseDensityW"), vec![]),
            noise_fn: Expr::const_(Name::from_string("BoolAnalysis.noiseFn"), vec![]),
            hc_sum_split: Expr::const_(Name::from_string("BoolAnalysis.hcSumSplit"), vec![]),
            extend_f: Expr::const_(Name::from_string("BoolAnalysis.extendF"), vec![]),
            extend_t: Expr::const_(Name::from_string("BoolAnalysis.extendT"), vec![]),
            cast_add: Expr::const_(Name::from_string("Fin.castAdd"), vec![]),
            add_nat: Expr::const_(Name::from_string("Fin.addNat"), vec![]),
            pow_two_succ: Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]),
            eq_symm_nat: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_ndrec_fin: Expr::const_(Name::from_string("Eq.ndrec"), vec![l1.clone(), l1]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    /// `HCPoint n → Rat` — the type of the input function `F`.
    fn f_type(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    fn nadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [a, b])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    /// `Fin.sum n f`.
    fn sum(&self, n: &Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), f])
    }
    /// `hcDecode m p`.
    fn decode(&self, m: &Expr, p: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [m.clone(), p.clone()])
    }
    /// `noiseDensityW ρ m x p`.
    fn density(&self, rho: &Expr, m: &Expr, x: &Expr, p: &Expr) -> Expr {
        Expr::apps(
            self.noise_density.clone(),
            [rho.clone(), m.clone(), x.clone(), p.clone()],
        )
    }
    /// `noiseFn ρ m F jx`.
    fn noise_fn(&self, rho: &Expr, m: &Expr, f: &Expr, jx: &Expr) -> Expr {
        Expr::apps(
            self.noise_fn.clone(),
            [rho.clone(), m.clone(), f.clone(), jx.clone()],
        )
    }
    /// `extend_b m p` for the chosen top bit (`extendF` / `extendT`).
    fn extend(&self, use_true: bool, m: &Expr, p: &Expr) -> Expr {
        let cst = if use_true {
            &self.extend_t
        } else {
            &self.extend_f
        };
        Expr::apps(cst.clone(), [m.clone(), p.clone()])
    }
    /// `@Eq Rat l r`.
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.rat.clone(), l, r],
        )
    }
    /// `@Eq.trans Rat a b c h1 h2`.
    fn trans_rat(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, c, h1, h2],
        )
    }
    /// `castP n M` — the split transport (byte-for-byte the `hcSumSplit` form).
    fn cast_p(&self, parent: &EnvDeclBuilder, n: &Expr, mapped: &Expr) -> Expr {
        let p2n = self.pow2(n);
        let sum_pow = self.nadd(p2n.clone(), p2n);
        let p2sn = self.pow2(&self.succ(n));
        let e_fwd = Expr::app(self.pow_two_succ.clone(), n.clone());
        let e = Expr::apps(
            self.eq_symm_nat.clone(),
            [self.nat.clone(), p2sn.clone(), sum_pow.clone(), e_fwd],
        );
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (m_id, m) = mb.fresh_local(self.nat.clone());
            let body = self.fin_of(&m);
            mb.finish_child(mb.mk_lam(m_id, BinderInfo::Default, self.nat.clone(), body))
        };
        Expr::apps(
            self.eq_ndrec_fin.clone(),
            [self.nat.clone(), sum_pow, motive, mapped.clone(), p2sn, e],
        )
    }
}

impl Environment {
    /// Register `BoolAnalysis.noiseFn_succ_split`: the operator-peel half-split.
    /// Idempotent; axiom-free.
    pub(crate) fn register_noise_fn_succ_split(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noiseFn_succ_split");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_noise_fn()?;
        self.register_hc_sum_split_theorem()?;
        self.init_fin_sum()?; // Fin.sum_congr (Fin.sum single-proof overlay)
        self.init_boolean_analysis_noise_extend_bridge()?; // the decode↔extend bridges
                                                           // Re-check: `register_noise_fn`'s `init_boolean_analysis` pass registers
                                                           // the hc24 chain (bonami retirement), which includes `noiseFn_succ_split`.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = NoiseFnSplitConsts::new();
        let (ty, value) = build_succ_split(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build the type + proof of `noiseFn_succ_split`.
fn build_succ_split(c: &NoiseFnSplitConsts) -> (Expr, Expr) {
    (build_succ_split_type(c), build_succ_split_value(c))
}

/// The `g`-integrand of the inner sum: `fun (p : HCPoint (n+1)) =>
/// F p · noiseDensityW ρ (n+1) (hcDecode (n+1) jx) p`.
fn g_fn(
    c: &NoiseFnSplitConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    sn: &Expr,
    f: &Expr,
    x: &Expr,
) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(sn);
    let (p_id, p) = d.fresh_local(hcp.clone());
    let body = c.mul(Expr::app(f.clone(), p.clone()), c.density(rho, sn, x, &p));
    d.finish_child(d.mk_lam(p_id, BinderInfo::Default, hcp, body))
}

/// One half-sum's *folded* integrand:
/// `fun (i : Fin (2^n)) => F (extend_b n (decode n i)) ·
///   noiseDensityW ρ (n+1) (decode (n+1) jx) (extend_b n (decode n i))`.
fn folded_half_fn(
    c: &NoiseFnSplitConsts,
    parent: &EnvDeclBuilder,
    use_true: bool,
    rho: &Expr,
    n: &Expr,
    f: &Expr,
    x: &Expr,
) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (i_id, i) = d.fresh_local(c.fin_of(&p2n));
    let ext = c.extend(use_true, n, &c.decode(n, &i));
    let body = c.mul(
        Expr::app(f.clone(), ext.clone()),
        c.density(rho, &c.succ(n), x, &ext),
    );
    d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_of(&p2n), body))
}

/// One half-sum's *raw* integrand (the form `hcSumSplit` produces):
/// `fun (i : Fin (2^n)) => g (hcDecode (n+1) (castP (idx_map i)))`.
fn raw_half_fn(
    c: &NoiseFnSplitConsts,
    parent: &EnvDeclBuilder,
    use_true: bool,
    g: &Expr,
    n: &Expr,
) -> Expr {
    let idx_map = if use_true { &c.add_nat } else { &c.cast_add };
    let mut d = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (i_id, i) = d.fresh_local(c.fin_of(&p2n));
    let mapped = Expr::apps(idx_map.clone(), [p2n.clone(), p2n.clone(), i.clone()]);
    let casted = c.cast_p(&d, n, &mapped);
    let decoded = c.decode(&c.succ(n), &casted);
    let body = Expr::app(g.clone(), decoded);
    d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_of(&p2n), body))
}

fn build_succ_split_type(c: &NoiseFnSplitConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&n);
    let (f_id, f) = b.fresh_local(c.f_type(&sn));
    let (jx_id, jx) = b.fresh_local(c.fin_of(&c.pow2(&sn)));

    let x = c.decode(&sn, &jx);
    let lhs = c.noise_fn(&rho, &sn, &f, &jx);
    let low = c.sum(&c.pow2(&n), folded_half_fn(c, &b, false, &rho, &n, &f, &x));
    let high = c.sum(&c.pow2(&n), folded_half_fn(c, &b, true, &rho, &n, &f, &x));
    let rhs = c.add(low, high);
    let concl = c.eq_rat(lhs, rhs);

    let e = b.mk_pi(jx_id, BinderInfo::Default, c.fin_of(&c.pow2(&sn)), concl);
    let e = b.mk_pi(f_id, BinderInfo::Default, c.f_type(&sn), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

fn build_succ_split_value(c: &NoiseFnSplitConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&n);
    let (f_id, f) = b.fresh_local(c.f_type(&sn));
    let (jx_id, jx) = b.fresh_local(c.fin_of(&c.pow2(&sn)));

    let x = c.decode(&sn, &jx);
    let g = g_fn(c, &b, &rho, &sn, &f, &x);
    let p2n = c.pow2(&n);

    // lhs ≡ Fin.sum (2^(n+1)) (fun jy => g (hcDecode (n+1) jy))  (δ-defeq to noiseFn).
    let lhs = c.noise_fn(&rho, &sn, &f, &jx);

    // step1 : hcSumSplit n g : lhs' = Rat.add (Σ raw_low) (Σ raw_high).
    let step1 = Expr::apps(c.hc_sum_split.clone(), [n.clone(), g.clone()]);
    let raw_low_fn = raw_half_fn(c, &b, false, &g, &n);
    let raw_high_fn = raw_half_fn(c, &b, true, &g, &n);
    let raw_low = c.sum(&p2n, raw_low_fn.clone());
    let raw_high = c.sum(&p2n, raw_high_fn.clone());
    let split_rhs = c.add(raw_low.clone(), raw_high.clone());

    // step2 : rewrite each half's integrand to the folded form via Fin.sum_congr.
    let folded_low_fn = folded_half_fn(c, &b, false, &rho, &n, &f, &x);
    let folded_high_fn = folded_half_fn(c, &b, true, &rho, &n, &f, &x);
    let folded_low = c.sum(&p2n, folded_low_fn.clone());
    let folded_high = c.sum(&p2n, folded_high_fn.clone());

    //   leaf_low : ∀ i, raw_low_fn i = folded_low_fn i  via congrArg g (bridge i).
    let leaf_low = build_half_leaf(c, &b, false, &g, &n);
    let leaf_high = build_half_leaf(c, &b, true, &g, &n);
    let congr_low = Expr::apps(
        c.fin_sum_congr.clone(),
        [p2n.clone(), raw_low_fn, folded_low_fn, leaf_low],
    );
    let congr_high = Expr::apps(
        c.fin_sum_congr.clone(),
        [p2n.clone(), raw_high_fn, folded_high_fn, leaf_high],
    );

    //   rewrite the Rat.add: (raw_low + raw_high) = (folded_low + folded_high).
    //   add_left : (raw_low + raw_high) = (folded_low + raw_high)
    let add_left_fn = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (s_id, s) = d.fresh_local(c.rat.clone());
        let body = c.add(s, raw_high.clone());
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let add_left = c.congr_arg_rat(raw_low.clone(), folded_low.clone(), add_left_fn, congr_low);
    let mid = c.add(folded_low.clone(), raw_high.clone());
    //   add_right : (folded_low + raw_high) = (folded_low + folded_high)
    let add_right_fn = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (s_id, s) = d.fresh_local(c.rat.clone());
        let body = c.add(folded_low.clone(), s);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let add_right = c.congr_arg_rat(
        raw_high.clone(),
        folded_high.clone(),
        add_right_fn,
        congr_high,
    );
    let final_rhs = c.add(folded_low, folded_high);

    // chain: lhs = split_rhs = mid = final_rhs.
    let t1 = c.trans_rat(lhs.clone(), split_rhs.clone(), mid.clone(), step1, add_left);
    let proof = c.trans_rat(lhs, mid, final_rhs, t1, add_right);

    let e = b.mk_lam(jx_id, BinderInfo::Default, c.fin_of(&c.pow2(&sn)), proof);
    let e = b.mk_lam(f_id, BinderInfo::Default, c.f_type(&sn), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// The leaf-wise congruence for one half:
/// `fun (i : Fin (2^n)) => congrArg g (bridge n i) :
///   g (hcDecode (n+1) (castP (idx_map i))) = g (extend_b n (hcDecode n i))`.
fn build_half_leaf(
    c: &NoiseFnSplitConsts,
    parent: &EnvDeclBuilder,
    use_true: bool,
    g: &Expr,
    n: &Expr,
) -> Expr {
    let bridge_name = if use_true {
        "BoolAnalysis.hcDecode_castP_addNat_extendT"
    } else {
        "BoolAnalysis.hcDecode_castP_castAdd_extendF"
    };
    let idx_map = if use_true { &c.add_nat } else { &c.cast_add };

    let mut d = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (i_id, i) = d.fresh_local(c.fin_of(&p2n));

    // bridge n i : hcDecode (n+1) (castP (idx_map i)) = extend_b n (hcDecode n i).
    let bridge = Expr::apps(
        Expr::const_(Name::from_string(bridge_name), vec![]),
        [n.clone(), i.clone()],
    );
    let mapped = Expr::apps(idx_map.clone(), [p2n.clone(), p2n.clone(), i.clone()]);
    let casted = c.cast_p(&d, n, &mapped);
    let lhs_pt = c.decode(&c.succ(n), &casted);
    let rhs_pt = c.extend(use_true, n, &c.decode(n, &i));
    // congrArg.{1,1} (HCPoint (n+1)) Rat lhs_pt rhs_pt g bridge.
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("congrArg"),
            vec![c.l1.clone(), c.l1.clone()],
        ),
        [
            c.hcpoint_of(&c.succ(n)),
            c.rat.clone(),
            lhs_pt,
            rhs_pt,
            g.clone(),
            bridge,
        ],
    );
    d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_of(&p2n), proof))
}

impl NoiseFnSplitConsts {
    /// `@congrArg Rat Rat from to f h` for a unary `f : Rat → Rat`.
    fn congr_arg_rat(&self, from: Expr, to: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [self.rat.clone(), self.rat.clone(), from, to, f, h],
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    #[test]
    fn test_noise_fn_succ_split_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_noise_fn_succ_split()
            .expect("register_noise_fn_succ_split");
        let name = Name::from_string("BoolAnalysis.noiseFn_succ_split");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("noiseFn_succ_split proof must check against its type");
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
