// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proofs on the way to PARSEVAL: the character bilinear-collapse
//! ("delta") lemma `Σ_S χ_S(x)·χ_S(y) = Π_i (1 + pm(x_i)·pm(y_i))`.
//!
//! The keystone is the *subset-sum bilinear collapse*
//!
//! ```text
//! subsetSum_chi_bilinear : ∀ (n : Nat) (x y : HCPoint n),
//!   subsetSum n (fun S => Rat.mul (chi n S x) (chi n S y))
//!     = Fin.prod n (fun i => Rat.add Rat.one (Rat.mul (pm (x i)) (pm (y i))))
//! ```
//!
//! Summing the per-point integrand `χ_S(x)·χ_S(y)` over ALL `2^n` subsets `S`
//! factors (by independence of the per-coordinate subset bits) into a product
//! over coordinates of the per-coordinate sum `Σ_{S_i∈{0,1}} cf(S_i,x_i)·cf(S_i,y_i)
//! = 1·1 + pm(x_i)·pm(y_i)`. The factor `1 + pm(a)·pm(b)` equals `2` when
//! `a = b` and `0` otherwise — i.e. `Π_i (1 + pm(x_i)pm(y_i)) = 2^n·[x=y]`, the
//! discrete orthogonality of the parity characters in the *subset* direction.
//! That is the delta the Fourier-expansion → Parseval bridge collapses against.
//!
//! Proof is by induction on `n` (the `Nat.rec` carrier under `subsetSum` /
//! `Fin.prod`):
//! - `subsetSum (n+1) G` splits (`subsetSum_split`) into the LOW half (subsets
//!   with top bit `0`) plus the HIGH half (top bit `1`);
//! - `chi_succ` peels each character into its `n`-cube restriction times the
//!   top-coordinate factor; on the LOW half the top factor is `cf(false,·) = 1`,
//!   on the HIGH half it is `cf(true,·) = pm(·)`;
//! - the induction hypothesis collapses each `2^n`-cube prefix sum into the
//!   `Fin.prod n` over the first `n` coordinates;
//! - `Fin.prod_succ` reassembles the `(n+1)`-coordinate product, with the new
//!   top factor `1 + pm(x_n)·pm(y_n)` supplied by the per-coordinate pair-sum
//!   algebra lemma `chi_factor_pair_sum`.
//!
//! Every rung is a kernel-checked `Declaration::Theorem` with an EMPTY admitted-
//! axiom closure (`ProofQuality::Constructive`); no axiom is added or removed,
//! so the soundness certificate's golden TCB is unchanged and each re-verifies
//! under C1.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for the delta-lemma proofs. Mirrors the `chi` body's
/// per-coordinate factor exactly so the assembled terms are byte-identical
/// (up to def-eq) to the ones the kernel produces when it δ-unfolds `chi`.
struct DeltaConsts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    rat_one: Expr,
    rat_zero: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    rat_add: Expr,
    rat_two: Expr,
    pm: Expr,
    bool_rec1: Expr,
    eq1: Expr,
    eq_refl1: Expr,
}

impl DeltaConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_one = Expr::app(nat_succ.clone(), nat_zero);
        let two = Expr::app(nat_succ.clone(), nat_one.clone());
        // `Rat.mk (Int.ofNat 2) 1` — the rational 2, matching chi's body.
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
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_two,
            pm: Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]),
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
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn refl_rat(&self, e: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.rat.clone(), e])
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

// ===========================================================================
// Rat.mul_mul_mul_comm — the 4-factor middle-swap regroup
//
//   (a·b)·(c·d) = (a·c)·(b·d)
//
// Pure `Rat.mul_assoc` / `Rat.mul_comm` chain (5 Eq.trans legs). Reusable for
// the character peel `χ(S,x)χ(S,y)` regrouping. Kernel-checked, constructive.
// ===========================================================================

impl DeltaConsts {
    fn eq_symm_rat(&self, l: Expr, r: Expr, h: Expr) -> Expr {
        let eq_symm = Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        );
        Expr::apps(eq_symm, [self.rat.clone(), l, r, h])
    }
    /// `congrArg Rat Rat from to motive h : motive from = motive to`.
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
    /// `fun (z : Rat) => Rat.mul a z`.
    fn mul_left_motive(&self, parent: &EnvDeclBuilder, a: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(self.rat.clone());
        let body = self.mul(a.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }
}

fn build_mmmc_type(c: &DeltaConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bb_id, bb) = b.fresh_local(c.rat.clone());
    let (cc_id, cc) = b.fresh_local(c.rat.clone());
    let (d_id, d) = b.fresh_local(c.rat.clone());
    let lhs = c.mul(c.mul(a.clone(), bb.clone()), c.mul(cc.clone(), d.clone()));
    let rhs = c.mul(c.mul(a.clone(), cc.clone()), c.mul(bb.clone(), d.clone()));
    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(d_id, BinderInfo::Default, c.rat.clone(), concl);
    let ty = b.mk_pi(cc_id, BinderInfo::Default, c.rat.clone(), ty);
    let ty = b.mk_pi(bb_id, BinderInfo::Default, c.rat.clone(), ty);
    let ty = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), ty);
    b.finish(ty)
}

fn build_mmmc_value(c: &DeltaConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bb_id, bb) = b.fresh_local(c.rat.clone());
    let (cc_id, cc) = b.fresh_local(c.rat.clone());
    let (d_id, d) = b.fresh_local(c.rat.clone());

    let cd = c.mul(cc.clone(), d.clone());
    let bd = c.mul(bb.clone(), d.clone());
    let bc = c.mul(bb.clone(), cc.clone());
    let cb = c.mul(cc.clone(), bb.clone());

    // e0 := (a·b)·(c·d)
    let e0 = c.mul(c.mul(a.clone(), bb.clone()), cd.clone());
    // e1 := a·(b·(c·d))        mul_assoc a b (c·d) : (a·b)·(c·d) = a·(b·(c·d))
    let e1 = c.mul(a.clone(), c.mul(bb.clone(), cd.clone()));
    let leg1 = c.mul_assoc(a.clone(), bb.clone(), cd.clone());
    // e2 := a·((b·c)·d)        congr (a··) (symm mul_assoc b c d) : b·(c·d) = (b·c)·d
    let e2 = c.mul(a.clone(), c.mul(bc.clone(), d.clone()));
    let assoc_bcd = c.mul_assoc(bb.clone(), cc.clone(), d.clone()); // (b·c)·d = b·(c·d)
    let assoc_bcd_sym = c.eq_symm_rat(
        c.mul(bc.clone(), d.clone()),
        c.mul(bb.clone(), cd.clone()),
        assoc_bcd,
    ); // b·(c·d) = (b·c)·d
    let leg2 = c.congr_rat(
        c.mul(bb.clone(), cd.clone()),
        c.mul(bc.clone(), d.clone()),
        c.mul_left_motive(&b, &a),
        assoc_bcd_sym,
    );
    // e3 := a·((c·b)·d)        congr (a··) (congr (··d) (mul_comm b c)) : (b·c)·d = (c·b)·d
    let e3 = c.mul(a.clone(), c.mul(cb.clone(), d.clone()));
    let comm_bc = c.mul_comm(bb.clone(), cc.clone()); // b·c = c·b
                                                      // motive_dr : fun z => z·d
    let mul_right_d = {
        let mut dd = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = dd.fresh_local(c.rat.clone());
        let body = c.mul(z, d.clone());
        dd.finish_child(dd.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let comm_bc_d = c.congr_rat(bc.clone(), cb.clone(), mul_right_d, comm_bc); // (b·c)·d = (c·b)·d
    let leg3 = c.congr_rat(
        c.mul(bc.clone(), d.clone()),
        c.mul(cb.clone(), d.clone()),
        c.mul_left_motive(&b, &a),
        comm_bc_d,
    );
    // e4 := a·(c·(b·d))        congr (a··) (mul_assoc c b d) : (c·b)·d = c·(b·d)
    let e4 = c.mul(a.clone(), c.mul(cc.clone(), bd.clone()));
    let assoc_cbd = c.mul_assoc(cc.clone(), bb.clone(), d.clone()); // (c·b)·d = c·(b·d)
    let leg4 = c.congr_rat(
        c.mul(cb.clone(), d.clone()),
        c.mul(cc.clone(), bd.clone()),
        c.mul_left_motive(&b, &a),
        assoc_cbd,
    );
    // e5 := (a·c)·(b·d)        symm (mul_assoc a c (b·d)) : (a·c)·(b·d) = a·(c·(b·d))
    let e5 = c.mul(c.mul(a.clone(), cc.clone()), bd.clone());
    let assoc_acbd = c.mul_assoc(a.clone(), cc.clone(), bd.clone()); // (a·c)·(b·d) = a·(c·(b·d))
    let leg5 = c.eq_symm_rat(e5.clone(), e4.clone(), assoc_acbd); // a·(c·(b·d)) = (a·c)·(b·d)

    // Chain: e0 = e1 = e2 = e3 = e4 = e5.
    let t1 = c.trans_rat(e0.clone(), e1.clone(), e2.clone(), leg1, leg2);
    let t2 = c.trans_rat(e0.clone(), e2.clone(), e3.clone(), t1, leg3);
    let t3 = c.trans_rat(e0.clone(), e3.clone(), e4.clone(), t2, leg4);
    let proof = c.trans_rat(e0, e4, e5, t3, leg5);

    let val = b.mk_lam(d_id, BinderInfo::Default, c.rat.clone(), proof);
    let val = b.mk_lam(cc_id, BinderInfo::Default, c.rat.clone(), val);
    let val = b.mk_lam(bb_id, BinderInfo::Default, c.rat.clone(), val);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Rat.mul_mul_mul_comm : ∀ a b c d, (a·b)·(c·d) = (a·c)·(b·d)`.
    /// The 4-factor middle-swap regroup, a `Rat.mul_assoc`/`Rat.mul_comm` chain.
    /// Kernel-checked, constructive. Idempotent.
    pub(crate) fn register_rat_mul_mul_mul_comm_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_mul_mul_comm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;

        let c = DeltaConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_mmmc_type(&c),
            value: build_mmmc_value(&c),
        })
    }
}

// ===========================================================================
// chi_factor_pair_sum — the per-coordinate pair-sum collapse.
//
//   cf(false,a)·cf(false,c) + cf(true,a)·cf(true,c) = 1 + pm(a)·pm(c)
//
// for all Bool a, c. Since `cf false _ ≡ 1` and `cf true b ≡ 1 - 2·⟦b⟧ ≡ pm b`
// definitionally, the LHS computes to `1·1 + pm(a)·pm(c)`. The RHS is
// `1 + pm(a)·pm(c)`. The only non-trivial step is `1·1 = 1`, supplied by
// `Rat.one_mul Rat.one` and a `congrArg` into the first summand; the second
// summand is byte-identical. We close with a single `congrArg` over the
// addition's left argument.
// ===========================================================================

// ===========================================================================
// chi_pair_succ — the bilinear character coordinate peel.
//
//   ∀ (k) (S x y : HCPoint (k+1)),
//     chi (k+1) S x · chi (k+1) S y
//       = (chi k (restrict S) (restrict x) · chi k (restrict S) (restrict y))
//         · (cf (S last) (x last) · cf (S last) (y last))
//
// `chi_succ` peels each character into its `k`-cube restriction times the top-
// coordinate factor; `Rat.mul_mul_mul_comm` regroups the four factors into the
// (prefix·prefix)·(top·top) grouping. Kernel-checked, constructive (closure ⊆
// {chi_succ, Rat.mul_mul_mul_comm} ∪ Eq built-ins).
// ===========================================================================

impl DeltaConsts {
    fn nat_succ_e(&self) -> Expr {
        Expr::const_(Name::from_string("Nat.succ"), vec![])
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ_e(), n.clone())
    }
    fn last(&self, n: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.last"), vec![]),
            [n.clone()],
        )
    }
    /// `fun (i : Fin n) => p (Fin.castSucc n i)` — restrict to first `n` coords.
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
    /// `chi_succ k S x : chi (k+1) S x = chi k (restrict S)(restrict x) · cf(S last)(x last)`.
    fn chi_succ(&self, k: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.chi_succ"), vec![]),
            [k.clone(), s.clone(), x.clone()],
        )
    }
    /// `chi (k+1) S x` (the LHS factor chi_succ rewrites).
    fn chi_sn(&self, k: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi(), [self.succ(k), s.clone(), x.clone()])
    }
    /// RHS of chi_succ: `chi k (restrict S)(restrict x) · cf(S last)(x last)`.
    fn chi_succ_rhs(&self, parent: &EnvDeclBuilder, k: &Expr, s: &Expr, x: &Expr) -> Expr {
        let rs = self.restrict(parent, k, s);
        let rx = self.restrict(parent, k, x);
        let chi_pre = Expr::apps(self.chi(), [k.clone(), rs, rx]);
        let s_last = Expr::app(s.clone(), self.last(k));
        let x_last = Expr::app(x.clone(), self.last(k));
        let top = self.factor(parent, s_last, x_last);
        self.mul(chi_pre, top)
    }
}

fn build_pair_succ_type(c: &DeltaConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&k);
    let hcp = c.hcpoint_of(&sn);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (y_id, y) = b.fresh_local(hcp.clone());

    // LHS: chi (k+1) S x · chi (k+1) S y
    let lhs = c.mul(c.chi_sn(&k, &s, &x), c.chi_sn(&k, &s, &y));

    // RHS: (chi k rS rx · chi k rS ry) · (cf(S last)(x last) · cf(S last)(y last))
    let rs = c.restrict(&b, &k, &s);
    let rx = c.restrict(&b, &k, &x);
    let ry = c.restrict(&b, &k, &y);
    let chi_x_pre = Expr::apps(c.chi(), [k.clone(), rs.clone(), rx]);
    let chi_y_pre = Expr::apps(c.chi(), [k.clone(), rs, ry]);
    let s_last = Expr::app(s.clone(), c.last(&k));
    let x_last = Expr::app(x.clone(), c.last(&k));
    let y_last = Expr::app(y.clone(), c.last(&k));
    let cf_x = c.factor(&b, s_last.clone(), x_last);
    let cf_y = c.factor(&b, s_last, y_last);
    let rhs = c.mul(c.mul(chi_x_pre, chi_y_pre), c.mul(cf_x, cf_y));

    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(y_id, BinderInfo::Default, hcp.clone(), concl);
    let ty = b.mk_pi(x_id, BinderInfo::Default, hcp.clone(), ty);
    let ty = b.mk_pi(s_id, BinderInfo::Default, hcp, ty);
    let ty = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), ty);
    b.finish(ty)
}

fn build_pair_succ_value(c: &DeltaConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&k);
    let hcp = c.hcpoint_of(&sn);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (y_id, y) = b.fresh_local(hcp.clone());

    // A·p := chi_succ rhs for x;  B·q := chi_succ rhs for y.
    let ap = c.chi_succ_rhs(&b, &k, &s, &x);
    let bq = c.chi_succ_rhs(&b, &k, &s, &y);
    let chi_x = c.chi_sn(&k, &s, &x);
    let chi_y = c.chi_sn(&k, &s, &y);

    // e0 := chi_x · chi_y
    let e0 = c.mul(chi_x.clone(), chi_y.clone());
    // e1 := (A·p) · chi_y      congr (·chi_y) (chi_succ k S x)
    let e1 = c.mul(ap.clone(), chi_y.clone());
    let mul_right_chi_y = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.mul(z, chi_y.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let leg1 = c.congr_rat(
        chi_x.clone(),
        ap.clone(),
        mul_right_chi_y,
        c.chi_succ(&k, &s, &x),
    );
    // e2 := (A·p) · (B·q)      congr ((A·p)·) (chi_succ k S y)
    let e2 = c.mul(ap.clone(), bq.clone());
    let leg2 = c.congr_rat(
        chi_y.clone(),
        bq.clone(),
        c.mul_left_motive(&b, &ap),
        c.chi_succ(&k, &s, &y),
    );
    // e3 := (A·B) · (p·q)      Rat.mul_mul_mul_comm A p B q
    // Decompose A·p, B·q into the 4 atoms.
    let rs = c.restrict(&b, &k, &s);
    let rx = c.restrict(&b, &k, &x);
    let ry = c.restrict(&b, &k, &y);
    let a_atom = Expr::apps(c.chi(), [k.clone(), rs.clone(), rx]);
    let b_atom = Expr::apps(c.chi(), [k.clone(), rs, ry]);
    let s_last = Expr::app(s.clone(), c.last(&k));
    let x_last = Expr::app(x.clone(), c.last(&k));
    let y_last = Expr::app(y.clone(), c.last(&k));
    let p_atom = c.factor(&b, s_last.clone(), x_last);
    let q_atom = c.factor(&b, s_last, y_last);
    let e3 = c.mul(
        c.mul(a_atom.clone(), b_atom.clone()),
        c.mul(p_atom.clone(), q_atom.clone()),
    );
    let leg3 = Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
        [a_atom, p_atom, b_atom, q_atom],
    );

    // Chain: e0 = e1 = e2 = e3.
    let t1 = c.trans_rat(e0.clone(), e1.clone(), e2.clone(), leg1, leg2);
    let proof = c.trans_rat(e0, e2, e3, t1, leg3);

    let val = b.mk_lam(y_id, BinderInfo::Default, hcp.clone(), proof);
    let val = b.mk_lam(x_id, BinderInfo::Default, hcp.clone(), val);
    let val = b.mk_lam(s_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.chi_pair_succ`: the bilinear character coordinate
    /// peel. Kernel-checked, constructive (closure ⊆ {`chi_succ`,
    /// `Rat.mul_mul_mul_comm`} ∪ Eq built-ins). Idempotent.
    pub(crate) fn register_chi_pair_succ_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_pair_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_chi_succ_theorem()?;
        self.register_rat_mul_mul_mul_comm_theorem()?;

        let c = DeltaConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_pair_succ_type(&c),
            value: build_pair_succ_value(&c),
        })
    }
}

fn build_pair_sum_type(c: &DeltaConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.bool_.clone());
    let (cc_id, cc) = b.fresh_local(c.bool_.clone());

    let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
    let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);

    // LHS: cf(false,a)·cf(false,c) + cf(true,a)·cf(true,c)
    let low = c.mul(
        c.factor(&b, bfalse.clone(), a.clone()),
        c.factor(&b, bfalse.clone(), cc.clone()),
    );
    let high = c.mul(
        c.factor(&b, btrue.clone(), a.clone()),
        c.factor(&b, btrue.clone(), cc.clone()),
    );
    let lhs = c.add(low, high);

    // RHS: 1 + pm(a)·pm(c)
    let pm_a = Expr::app(c.pm.clone(), a.clone());
    let pm_c = Expr::app(c.pm.clone(), cc.clone());
    let rhs = c.add(c.rat_one.clone(), c.mul(pm_a, pm_c));

    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(cc_id, BinderInfo::Default, c.bool_.clone(), concl);
    let ty = b.mk_pi(a_id, BinderInfo::Default, c.bool_.clone(), ty);
    b.finish(ty)
}

fn build_pair_sum_value(c: &DeltaConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.bool_.clone());
    let (cc_id, cc) = b.fresh_local(c.bool_.clone());

    let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);

    // The goal `LHS = 1 + pm(a)·pm(c)` is, after δ/ι-reduction of cf,
    //   `Rat.mul 1 1 + pm(a)·pm(c)  =  Rat.one + pm(a)·pm(c)`.
    // `Rat.one_mul Rat.one : Rat.mul 1 1 = Rat.one`. congrArg the addition's
    // left slot with the *high* term as the (def-eq) fixed right argument.
    let high = c.mul(
        c.factor(
            &b,
            Expr::const_(Name::from_string("Bool.true"), vec![]),
            a.clone(),
        ),
        c.factor(
            &b,
            Expr::const_(Name::from_string("Bool.true"), vec![]),
            cc.clone(),
        ),
    );
    // `cf(false,a)·cf(false,c)` is def-eq to `Rat.mul Rat.one Rat.one`.
    let low_lhs = c.mul(
        c.factor(&b, bfalse.clone(), a.clone()),
        c.factor(&b, bfalse.clone(), cc.clone()),
    );

    let one_mul_one = Expr::apps(
        Expr::const_(Name::from_string("Rat.one_mul"), vec![]),
        [c.rat_one.clone()],
    );

    // motive: fun (z : Rat) => Rat.add z high
    let add_motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.add(z, high.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };

    // congrArg Rat Rat low_lhs Rat.one add_motive one_mul_one
    //   : Rat.add low_lhs high = Rat.add Rat.one high
    // both sides def-eq to goal sides (low_lhs ≡ 1·1, high ≡ pm(a)·pm(c)).
    let congr_arg = Expr::const_(
        Name::from_string("congrArg"),
        vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
    );
    let proof = Expr::apps(
        congr_arg,
        [
            c.rat.clone(),
            c.rat.clone(),
            low_lhs,
            c.rat_one.clone(),
            add_motive,
            one_mul_one,
        ],
    );

    let val = b.mk_lam(cc_id, BinderInfo::Default, c.bool_.clone(), proof);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.bool_.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.chi_factor_pair_sum`: the per-coordinate pair-sum
    /// collapse `cf(false,a)cf(false,c) + cf(true,a)cf(true,c) = 1 + pm(a)pm(c)`.
    /// Kernel-checked, constructive (closure ⊆ {`Rat.one_mul`} ∪ Eq built-ins).
    /// Idempotent.
    pub(crate) fn register_chi_factor_pair_sum_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_factor_pair_sum");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        // `pm` is registered by `register_boolfn_embeddings` inside
        // `init_boolean_analysis`. Callers wire this theorem in after that.

        let c = DeltaConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_pair_sum_type(&c),
            value: build_pair_sum_value(&c),
        })
    }
}

// ===========================================================================
// subsetSum_chi_bilinear_zero — the n = 0 base case of the bilinear delta.
//
//   ∀ (x y : HCPoint 0),
//     subsetSum 0 (fun S => chi 0 S x · chi 0 S y)
//       = Fin.prod 0 (fun i => 1 + pm(x i)·pm(y i))
//
// At n = 0 the only subset is the empty one and `chi 0 _ _ ≡ Fin.prod 0 _ ≡ 1`,
// so the LHS `Fin.sum (2^0=1) (fun _ => 1·1)` ι-reduces to `Rat.add Rat.zero
// (Rat.mul Rat.one Rat.one)` and the RHS `Fin.prod 0 _` ι-reduces to `Rat.one`.
// The goal `0 + 1·1 = 1` is closed by `Eq.trans (Rat.zero_add (1·1))
// (Rat.one_mul Rat.one)` (after the def-eq massage of both ι-reductions).
// ===========================================================================

impl DeltaConsts {
    fn fin_prod(&self) -> Expr {
        Expr::const_(Name::from_string("Fin.prod"), vec![])
    }
    fn subset_sum(&self) -> Expr {
        Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![])
    }
    fn chi(&self) -> Expr {
        Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![])
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
    fn nat_zero(&self) -> Expr {
        Expr::const_(Name::from_string("Nat.zero"), vec![])
    }
    /// `fun i => Rat.add Rat.one (Rat.mul (pm (x i)) (pm (y i)))` on `Fin n`.
    fn prod_integrand(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let pm_x = Expr::app(self.pm.clone(), Expr::app(x.clone(), i.clone()));
        let pm_y = Expr::app(self.pm.clone(), Expr::app(y.clone(), i.clone()));
        let body = self.add(self.rat_one.clone(), self.mul(pm_x, pm_y));
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `fun S => Rat.mul (chi n S x) (chi n S y)` on `HCPoint n`.
    fn ss_integrand(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let chi_x = Expr::apps(self.chi(), [n.clone(), s.clone(), x.clone()]);
        let chi_y = Expr::apps(self.chi(), [n.clone(), s.clone(), y.clone()]);
        let body = self.mul(chi_x, chi_y);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    fn ss_lhs(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.subset_sum(),
            [n.clone(), self.ss_integrand(parent, n, x, y)],
        )
    }
    fn prod_rhs(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.fin_prod(),
            [n.clone(), self.prod_integrand(parent, n, x, y)],
        )
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        let eq_trans = Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        );
        Expr::apps(eq_trans, [self.rat.clone(), a, b, cc, h1, h2])
    }
}

fn build_base_type(c: &DeltaConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let zero = c.nat_zero();
    let hcp = c.hcpoint_of(&zero);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (y_id, y) = b.fresh_local(hcp.clone());
    let lhs = c.ss_lhs(&b, &zero, &x, &y);
    let rhs = c.prod_rhs(&b, &zero, &x, &y);
    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(y_id, BinderInfo::Default, hcp.clone(), concl);
    let ty = b.mk_pi(x_id, BinderInfo::Default, hcp, ty);
    b.finish(ty)
}

fn build_base_value(c: &DeltaConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let zero = c.nat_zero();
    let hcp = c.hcpoint_of(&zero);
    let (x_id, _x) = b.fresh_local(hcp.clone());
    let (y_id, _y) = b.fresh_local(hcp.clone());

    // LHS ι-reduces to `Rat.add Rat.zero (Rat.mul Rat.one Rat.one)`.
    // RHS ι-reduces to `Rat.one`.
    let one_mul_one = c.mul(c.rat_one.clone(), c.rat_one.clone());
    let zero_add_term = c.add(c.rat_zero.clone(), one_mul_one.clone());

    // leg1 : Rat.add Rat.zero (1·1) = 1·1     (Rat.zero_add (1·1))
    let leg1 = Expr::apps(
        Expr::const_(Name::from_string("Rat.zero_add"), vec![]),
        [one_mul_one.clone()],
    );
    // leg2 : Rat.mul Rat.one Rat.one = Rat.one  (Rat.one_mul Rat.one)
    let leg2 = Expr::apps(
        Expr::const_(Name::from_string("Rat.one_mul"), vec![]),
        [c.rat_one.clone()],
    );
    // proof : (0 + 1·1) = 1   (def-eq to LHS = RHS).
    let proof = c.trans_rat(zero_add_term, one_mul_one, c.rat_one.clone(), leg1, leg2);

    let val = b.mk_lam(y_id, BinderInfo::Default, hcp.clone(), proof);
    let val = b.mk_lam(x_id, BinderInfo::Default, hcp, val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.subsetSum_chi_bilinear_zero`: the `n = 0` base case
    /// of the bilinear delta. Kernel-checked, constructive (closure ⊆
    /// {`Rat.zero_add`, `Rat.one_mul`} ∪ Eq built-ins). Idempotent.
    pub(crate) fn register_subset_sum_chi_bilinear_zero_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_chi_bilinear_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.register_subset_sum()?;

        let c = DeltaConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_base_type(&c),
            value: build_base_value(&c),
        })
    }
}

// ===========================================================================
// chi_bilinear_pair_combine — the per-index LOW+HIGH combine.
//
//   ∀ (k) (x y : HCPoint (k+1)) (j : Fin (2^k)),
//     LO(j) + HI(j)
//       = (chi k (hcDecode k j) xr · chi k (hcDecode k j) yr)
//         · (1 + pm(x last)·pm(y last))
//
// where  LO(j) = chi(k+1)(Slo j)x · chi(k+1)(Slo j)y,
//        HI(j) = chi(k+1)(Shi j)x · chi(k+1)(Shi j)y,
//        Slo j = hcDecode (k+1) (castP (castAdd j)),   top bit false,
//        Shi j = hcDecode (k+1) (castP (addNat j)),    top bit true,
//        xr = restrict x,  yr = restrict y.
//
// Each half is `chi_pair_succ`-peeled, then its restricted subset is rewritten
// `restrict (Sxx j) → hcDecode k j` (the `hcDecode_restrict_*` lemmas, congr in
// BOTH χ factors) and its top bit `(Sxx j)(last) → false/true` (the
// `hcDecode_castP_*` + `Nat.testBit_*` lemmas, congr in BOTH cf factors). The
// two halves then share the common prefix `P = χ·χ`; `Rat.left_distrib`
// factors `P` out of `P·(cf_F·cf_F) + P·(cf_T·cf_T)`, and `chi_factor_pair_sum`
// collapses the per-coordinate pair-sum to `1 + pm(x_last)·pm(y_last)`.
// Kernel-checked, constructive.
// ===========================================================================

/// Richer const set for the per-index combine (decode/restriction/testBit).
struct CombineConsts {
    d: DeltaConsts,
    nat_pow: Expr,
    nat_add: Expr,
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
    nat_succ: Expr,
    btrue: Expr,
    bfalse: Expr,
    bool_rec1: Expr,
    congr_arg_br: Expr, // congrArg Bool→Rat
    congr_arg_hr: Expr, // congrArg HCPoint→Rat (level 2,2)
    eq_trans_bool: Expr,
    restrict_lo: Expr,
    restrict_hi: Expr,
    decode_lo_bit: Expr,
    decode_hi_bit: Expr,
    testbit_lt_pow: Expr,
    testbit_add_self: Expr,
    testbit: Expr,
    left_distrib: Expr,
    chi_pair_succ: Expr,
    factor_pair_sum: Expr,
}

impl CombineConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            d: DeltaConsts::new(),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            fin_val: Expr::const_(Name::from_string("Fin.val"), vec![]),
            fin_islt: Expr::const_(Name::from_string("Fin.isLt"), vec![]),
            cast_add: Expr::const_(Name::from_string("Fin.castAdd"), vec![]),
            add_nat: Expr::const_(Name::from_string("Fin.addNat"), vec![]),
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            pow_two_succ: Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]),
            eq_symm_nat: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_ndrec_fin: Expr::const_(Name::from_string("Eq.ndrec"), vec![l1.clone(), l1.clone()]),
            two: {
                let z = Expr::const_(Name::from_string("Nat.zero"), vec![]);
                let s = Expr::const_(Name::from_string("Nat.succ"), vec![]);
                Expr::app(s.clone(), Expr::app(s, z))
            },
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            btrue: Expr::const_(Name::from_string("Bool.true"), vec![]),
            bfalse: Expr::const_(Name::from_string("Bool.false"), vec![]),
            bool_rec1: Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]),
            congr_arg_br: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            congr_arg_hr: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            eq_trans_bool: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
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
            left_distrib: Expr::const_(Name::from_string("Rat.left_distrib"), vec![]),
            chi_pair_succ: Expr::const_(Name::from_string("BoolAnalysis.chi_pair_succ"), vec![]),
            factor_pair_sum: Expr::const_(
                Name::from_string("BoolAnalysis.chi_factor_pair_sum"),
                vec![],
            ),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    fn nadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [a, b])
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn val(&self, n: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [n.clone(), i.clone()])
    }
    fn last(&self, n: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.last"), vec![]),
            [n.clone()],
        )
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            n.clone(),
        )
    }
    fn chi(&self, n: Expr, s: Expr, x: Expr) -> Expr {
        Expr::apps(self.d.chi(), [n, s, x])
    }
    fn pm(&self, b: Expr) -> Expr {
        Expr::app(self.d.pm.clone(), b)
    }

    /// `castP n (idx_map (2^n) (2^n) j) : Fin (2^(n+1))` (transport along
    /// `Nat.pow_two_succ`, matching hcSumSplit / offdiag).
    fn cast_p(&self, parent: &EnvDeclBuilder, n: &Expr, idx_map: &Expr, j: &Expr) -> Expr {
        let p2n = self.pow2(n);
        let mapped = Expr::apps(idx_map.clone(), [p2n.clone(), p2n.clone(), j.clone()]);
        let sum_pow = self.nadd(p2n.clone(), p2n);
        let p2sn = self.pow2(&self.succ(n));
        let e_fwd = Expr::app(self.pow_two_succ.clone(), n.clone());
        let e = Expr::apps(
            self.eq_symm_nat.clone(),
            [self.d.nat.clone(), p2sn.clone(), sum_pow.clone(), e_fwd],
        );
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (m_id, m) = mb.fresh_local(self.d.nat.clone());
            mb.finish_child(mb.mk_lam(
                m_id,
                BinderInfo::Default,
                self.d.nat.clone(),
                self.fin_of(&m),
            ))
        };
        Expr::apps(
            self.eq_ndrec_fin.clone(),
            [self.d.nat.clone(), sum_pow, motive, mapped, p2sn, e],
        )
    }
    /// `hcDecode (n+1) (castP n idx_map j) : HCPoint (n+1)` — the decoded
    /// subset for one cube half.
    fn decoded(&self, parent: &EnvDeclBuilder, n: &Expr, idx_map: &Expr, j: &Expr) -> Expr {
        let cp = self.cast_p(parent, n, idx_map, j);
        Expr::apps(self.hc_decode.clone(), [self.succ(n), cp])
    }
    /// `fun (i : Fin n) => p (Fin.castSucc n i)`.
    fn restrict(&self, parent: &EnvDeclBuilder, n: &Expr, p: &Expr) -> Expr {
        self.d.restrict(parent, n, p)
    }
    /// `factor sb xb` (matches chi/chi_succ).
    fn factor(&self, parent: &EnvDeclBuilder, sb: Expr, xb: Expr) -> Expr {
        self.d.factor(parent, sb, xb)
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.d.mul(a, b)
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        self.d.add(a, b)
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        self.d.eq_rat(l, r)
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        self.d.trans_rat(a, b, cc, h1, h2)
    }
    fn congr_rat(&self, from: Expr, to: Expr, motive: Expr, h: Expr) -> Expr {
        self.d.congr_rat(from, to, motive, h)
    }
    fn eq_symm_rat(&self, l: Expr, r: Expr, h: Expr) -> Expr {
        self.d.eq_symm_rat(l, r, h)
    }
}

/// Build `hHalf : chi_pair_succ-peeled half = P · (cf b x_last · cf b y_last)`,
/// where the restricted subset is rewritten to `hcDecode n j` and the top bit
/// to `bit_target` (false for LOW, true for HIGH). Returns the proof that
///   chi(n+1)(Shalf)x · chi(n+1)(Shalf)y  =  P · (cf bit x_last · cf bit y_last).
#[allow(clippy::too_many_arguments)]
fn build_half_eq(
    c: &CombineConsts,
    b: &EnvDeclBuilder,
    n: &Expr,
    x: &Expr,
    y: &Expr,
    j: &Expr,
    idx_map: &Expr,
    restrict_lemma: &Expr,
    decode_bit_lemma: &Expr,
    testbit_value_lemma: &Expr, // testbit_lt_pow (→false) | testbit_add_self (→true)
    bit_target: &Expr,          // Bool.false | Bool.true
    bit_inner: &Expr,           // Nat the testBit reads: val j (lo) | 2^n+val j (hi)
) -> (Expr, Expr, Expr) {
    let sn = c.succ(n);
    let s_half = c.decoded(b, n, idx_map, j);
    let xr = c.restrict(b, n, x);
    let yr = c.restrict(b, n, y);
    let dec_n_j = Expr::apps(c.hc_decode.clone(), [n.clone(), j.clone()]);

    // r_half := restrict (S_half) — the subset chi_pair_succ produces.
    let r_half = c.restrict(b, n, &s_half);

    // P := chi n (hcDecode n j) xr · chi n (hcDecode n j) yr   (the target prefix).
    let p_x = c.chi(n.clone(), dec_n_j.clone(), xr.clone());
    let p_y = c.chi(n.clone(), dec_n_j.clone(), yr.clone());
    let p = c.mul(p_x.clone(), p_y.clone());

    // s_half_last := S_half (last n);  x_last := x (last n);  y_last := y (last n).
    let s_half_last = Expr::app(s_half.clone(), c.last(n));
    let x_last = Expr::app(x.clone(), c.last(n));
    let y_last = Expr::app(y.clone(), c.last(n));

    // chi_pair_succ n S_half x y :
    //   chi(n+1)S_half x · chi(n+1)S_half y
    //     = (chi n r_half xr · chi n r_half yr) · (cf(s_half_last,x_last) · cf(s_half_last,y_last))
    let lhs = c.mul(
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

    // restrict_eq : r_half = hcDecode n j   (restrict lemma).
    let restrict_eq = Expr::apps(restrict_lemma.clone(), [n.clone(), j.clone()]);

    // Rewrite the prefix `chi n r_half xr · chi n r_half yr` → `P` in two steps.
    // step px : chi n r_half xr = chi n (dec n j) xr   (congr in subset slot, point xr fixed)
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
            c.d.rat.clone(),
            r_half.clone(),
            dec_n_j.clone(),
            chi_fix_x,
            restrict_eq.clone(),
        ],
    );
    // step py : chi n r_half yr = chi n (dec n j) yr
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
            c.d.rat.clone(),
            r_half.clone(),
            dec_n_j.clone(),
            chi_fix_y,
            restrict_eq.clone(),
        ],
    );
    // h_pre : pre = P  via two congrArg into Rat.mul (left then right).
    //   congr (·chi_pre_y) h_px : (chi_pre_x · chi_pre_y) = (p_x · chi_pre_y)
    let mul_right_pre_y = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.d.rat.clone());
        let body = c.mul(z, chi_pre_y.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.d.rat.clone(), body))
    };
    let h_pre1 = c.congr_rat(chi_pre_x.clone(), p_x.clone(), mul_right_pre_y, h_px);
    //   congr (p_x ·) h_py : (p_x · chi_pre_y) = (p_x · p_y) = P
    let mul_left_px = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.d.rat.clone());
        let body = c.mul(p_x.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.d.rat.clone(), body))
    };
    let h_pre2 = c.congr_rat(chi_pre_y.clone(), p_y.clone(), mul_left_px, h_py);
    let pre_mid = c.mul(p_x.clone(), chi_pre_y.clone());
    let h_pre = c.trans_rat(pre.clone(), pre_mid, p.clone(), h_pre1, h_pre2);

    // bit : s_half_last = bit_target   via decode_bit_lemma + testbit_value_lemma.
    //   decode_bit_lemma n j (last n) : s_half_last = testBit (bit_inner) (val (n+1)(last n))
    //     and val (n+1)(last n) ≡ n defeq, so RHS ≡ testBit (bit_inner) n.
    let bit_corr = Expr::apps(decode_bit_lemma.clone(), [n.clone(), j.clone(), c.last(n)]);
    let val_islt = Expr::apps(c.fin_islt.clone(), [c.pow2(n), j.clone()]);
    let val_j = c.val(&c.pow2(n), j);
    // testbit_value_lemma n (val j) (isLt) : testBit (bit_inner) n = bit_target.
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
            c.d.bool_.clone(),
            s_half_last.clone(),
            testbit_n,
            bit_target.clone(),
            bit_corr,
            bit_value,
        ],
    );

    // Rewrite the cf pair `cf(s_half_last,x_last) · cf(s_half_last,y_last)`
    //   → `cf(bit_target,x_last) · cf(bit_target,y_last)`.
    let cf_tx = c.factor(b, bit_target.clone(), x_last.clone());
    let cf_ty = c.factor(b, bit_target.clone(), y_last.clone());
    // h_cfx : cf(s_half_last,x_last) = cf(bit_target,x_last)  (congr in subset-bit slot)
    let cf_motive_x = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (sb_id, sb) = d.fresh_local(c.d.bool_.clone());
        let body = c.factor(&d, sb, x_last.clone());
        d.finish_child(d.mk_lam(sb_id, BinderInfo::Default, c.d.bool_.clone(), body))
    };
    let h_cfx = Expr::apps(
        c.congr_arg_br.clone(),
        [
            c.d.bool_.clone(),
            c.d.rat.clone(),
            s_half_last.clone(),
            bit_target.clone(),
            cf_motive_x,
            bit.clone(),
        ],
    );
    let cf_motive_y = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (sb_id, sb) = d.fresh_local(c.d.bool_.clone());
        let body = c.factor(&d, sb, y_last.clone());
        d.finish_child(d.mk_lam(sb_id, BinderInfo::Default, c.d.bool_.clone(), body))
    };
    let h_cfy = Expr::apps(
        c.congr_arg_br.clone(),
        [
            c.d.bool_.clone(),
            c.d.rat.clone(),
            s_half_last.clone(),
            bit_target.clone(),
            cf_motive_y,
            bit.clone(),
        ],
    );
    // h_cf : cf_pair = cf(bit,x_last)·cf(bit,y_last)  via two congr into Rat.mul.
    let mul_right_cf_sy = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.d.rat.clone());
        let body = c.mul(z, cf_sy.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.d.rat.clone(), body))
    };
    let h_cf1 = c.congr_rat(cf_sx.clone(), cf_tx.clone(), mul_right_cf_sy, h_cfx);
    let mul_left_cf_tx = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.d.rat.clone());
        let body = c.mul(cf_tx.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.d.rat.clone(), body))
    };
    let h_cf2 = c.congr_rat(cf_sy.clone(), cf_ty.clone(), mul_left_cf_tx, h_cfy);
    let cf_mid = c.mul(cf_tx.clone(), cf_sy.clone());
    let cf_target = c.mul(cf_tx.clone(), cf_ty.clone());
    let h_cf = c.trans_rat(cf_pair.clone(), cf_mid, cf_target.clone(), h_cf1, h_cf2);

    // h_body : peeled = P · cf_target   via two congr into Rat.mul.
    let mul_right_cf_pair = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.d.rat.clone());
        let body = c.mul(z, cf_pair.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.d.rat.clone(), body))
    };
    let h_body1 = c.congr_rat(pre.clone(), p.clone(), mul_right_cf_pair, h_pre);
    let mul_left_p = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.d.rat.clone());
        let body = c.mul(p.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.d.rat.clone(), body))
    };
    let h_body2 = c.congr_rat(cf_pair.clone(), cf_target.clone(), mul_left_p, h_cf);
    let body_mid = c.mul(p.clone(), cf_pair.clone());
    let target = c.mul(p.clone(), cf_target.clone());
    let h_body = c.trans_rat(peeled.clone(), body_mid, target.clone(), h_body1, h_body2);

    // Full half eq: lhs = peeled (chi_pair_succ) then peeled = target (h_body).
    let proof = c.trans_rat(lhs.clone(), peeled, target.clone(), leg_peel, h_body);
    (proof, p, target)
}

fn build_combine_type(c: &CombineConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.d.nat.clone());
    let sn = c.succ(&n);
    let hcp = c.hcpoint_of(&sn);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (y_id, y) = b.fresh_local(hcp.clone());
    let p2n = c.pow2(&n);
    let (j_id, j) = b.fresh_local(c.fin_of(&p2n));

    let s_lo = c.decoded(&b, &n, &c.cast_add, &j);
    let s_hi = c.decoded(&b, &n, &c.add_nat, &j);
    let lo = c.mul(
        c.chi(sn.clone(), s_lo.clone(), x.clone()),
        c.chi(sn.clone(), s_lo, y.clone()),
    );
    let hi = c.mul(
        c.chi(sn.clone(), s_hi.clone(), x.clone()),
        c.chi(sn.clone(), s_hi, y.clone()),
    );
    let lhs = c.add(lo, hi);

    let dec_n_j = Expr::apps(c.hc_decode.clone(), [n.clone(), j.clone()]);
    let xr = c.restrict(&b, &n, &x);
    let yr = c.restrict(&b, &n, &y);
    let p = c.mul(
        c.chi(n.clone(), dec_n_j.clone(), xr),
        c.chi(n.clone(), dec_n_j, yr),
    );
    let x_last = Expr::app(x.clone(), c.last(&n));
    let y_last = Expr::app(y.clone(), c.last(&n));
    let pair = c.add(c.d.rat_one.clone(), c.mul(c.pm(x_last), c.pm(y_last)));
    let rhs = c.mul(p, pair);

    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(j_id, BinderInfo::Default, c.fin_of(&p2n), concl);
    let ty = b.mk_pi(y_id, BinderInfo::Default, hcp.clone(), ty);
    let ty = b.mk_pi(x_id, BinderInfo::Default, hcp, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.d.nat.clone(), ty);
    b.finish(ty)
}

fn build_combine_value(c: &CombineConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.d.nat.clone());
    let sn = c.succ(&n);
    let hcp = c.hcpoint_of(&sn);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (y_id, y) = b.fresh_local(hcp.clone());
    let p2n = c.pow2(&n);
    let (j_id, j) = b.fresh_local(c.fin_of(&p2n));

    let val_j = c.val(&p2n, &j);
    let bit_inner_lo = val_j.clone();
    let bit_inner_hi = c.nadd(p2n.clone(), val_j);

    // LOW half eq: LO = P · (cf false x_last · cf false y_last).
    let (h_lo, p, target_lo) = build_half_eq(
        c,
        &b,
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
    );
    // HIGH half eq: HI = P · (cf true x_last · cf true y_last).
    let (h_hi, _p2, target_hi) = build_half_eq(
        c,
        &b,
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
    );

    // LO + HI terms.
    let s_lo = c.decoded(&b, &n, &c.cast_add, &j);
    let s_hi = c.decoded(&b, &n, &c.add_nat, &j);
    let lo = c.mul(
        c.chi(sn.clone(), s_lo.clone(), x.clone()),
        c.chi(sn.clone(), s_lo, y.clone()),
    );
    let hi = c.mul(
        c.chi(sn.clone(), s_hi.clone(), x.clone()),
        c.chi(sn.clone(), s_hi, y.clone()),
    );
    let lhs = c.add(lo.clone(), hi.clone());

    // cf pairs (false / true).
    let x_last = Expr::app(x.clone(), c.last(&n));
    let y_last = Expr::app(y.clone(), c.last(&n));
    let cf_f = c.mul(
        c.factor(&b, c.bfalse.clone(), x_last.clone()),
        c.factor(&b, c.bfalse.clone(), y_last.clone()),
    );
    let cf_t = c.mul(
        c.factor(&b, c.btrue.clone(), x_last.clone()),
        c.factor(&b, c.btrue.clone(), y_last.clone()),
    );

    // step1 : LO + HI = (P·cf_f) + (P·cf_t)   (congr both summands).
    let add_right_hi = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.d.rat.clone());
        let body = c.add(z, hi.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.d.rat.clone(), body))
    };
    let s1a = c.congr_rat(lo.clone(), target_lo.clone(), add_right_hi, h_lo);
    let add_left_tlo = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.d.rat.clone());
        let body = c.add(target_lo.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.d.rat.clone(), body))
    };
    let s1b = c.congr_rat(hi.clone(), target_hi.clone(), add_left_tlo, h_hi);
    let add_mid = c.add(target_lo.clone(), hi.clone());
    let add_targets = c.add(target_lo.clone(), target_hi.clone());
    let step1 = c.trans_rat(lhs.clone(), add_mid, add_targets.clone(), s1a, s1b);

    // step2 : (P·cf_f) + (P·cf_t) = P · (cf_f + cf_t)   (Eq.symm left_distrib).
    let distrib = Expr::apps(
        c.left_distrib.clone(),
        [p.clone(), cf_f.clone(), cf_t.clone()],
    );
    let p_sum = c.mul(p.clone(), c.add(cf_f.clone(), cf_t.clone()));
    let step2 = c.eq_symm_rat(p_sum.clone(), add_targets.clone(), distrib);

    // step3 : P · (cf_f + cf_t) = P · (1 + pm(x_last)·pm(y_last))
    //   congr (P·) (chi_factor_pair_sum x_last y_last).
    let pair_sum = Expr::apps(c.factor_pair_sum.clone(), [x_last.clone(), y_last.clone()]);
    let pair_rhs = c.add(c.d.rat_one.clone(), c.mul(c.pm(x_last), c.pm(y_last)));
    let mul_left_p2 = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.d.rat.clone());
        let body = c.mul(p.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.d.rat.clone(), body))
    };
    let cf_sum = c.add(cf_f.clone(), cf_t.clone());
    let step3 = c.congr_rat(cf_sum, pair_rhs.clone(), mul_left_p2, pair_sum);
    let final_rhs = c.mul(p.clone(), pair_rhs);

    // Chain: lhs = add_targets = p_sum = final_rhs.
    let t1 = c.trans_rat(lhs.clone(), add_targets, p_sum.clone(), step1, step2);
    let proof = c.trans_rat(lhs, p_sum, final_rhs, t1, step3);

    let val = b.mk_lam(j_id, BinderInfo::Default, c.fin_of(&p2n), proof);
    let val = b.mk_lam(y_id, BinderInfo::Default, hcp.clone(), val);
    let val = b.mk_lam(x_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.d.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.chi_bilinear_pair_combine`: the per-index LOW+HIGH
    /// combine. Kernel-checked, constructive. Idempotent.
    pub(crate) fn register_chi_bilinear_pair_combine_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_bilinear_pair_combine");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?; // Rat.left_distrib (constructive Rat-quotient theorem)
        self.register_chi_pair_succ_theorem()?;
        self.register_chi_factor_pair_sum_theorem()?;
        // restriction / decode-bit lemmas + testBit lemmas + hcDecode + isLt.
        self.register_hc_decode_split_theorems()?;

        let c = CombineConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_combine_type(&c),
            value: build_combine_value(&c),
        })
    }
}

// ===========================================================================
// subsetSum_chi_bilinear — the character bilinear-collapse delta (induction).
//
//   ∀ (n : Nat) (x y : HCPoint n),
//     subsetSum n (fun S => chi n S x · chi n S y)
//       = Fin.prod n (fun i => 1 + pm(x i)·pm(y i))
//
// `Nat.rec` on `n`. Base `subsetSum_chi_bilinear_zero`. Step uses
// `subsetSum_split` (split subsets by the top coordinate), the per-index
// `chi_bilinear_pair_combine` (LO+HIGH = prefix · top-pair-sum), `Fin.sum_smul`
// (pull the common top factor out of the cube sum), the induction hypothesis at
// the restricted points, and `Fin.prod_succ` (reassemble the (n+1)-product).
// Kernel-checked, constructive.
// ===========================================================================

/// Const set for the inductive delta.
struct DeltaIndConsts {
    d: DeltaConsts,
    fin: Expr,
    nat_pow: Expr,
    nat_succ: Expr,
    fin_sum: Expr,
    fin_prod: Expr,
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
    combine: Expr,
    base_zero: Expr,
    two: Expr,
    nat_add: Expr,
    pow_two_succ: Expr,
    eq_symm_nat: Expr,
    eq_ndrec_fin: Expr,
}

impl DeltaIndConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let z = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let s = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        Self {
            d: DeltaConsts::new(),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            nat_succ: s.clone(),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin_prod: Expr::const_(Name::from_string("Fin.prod"), vec![]),
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
            combine: Expr::const_(
                Name::from_string("BoolAnalysis.chi_bilinear_pair_combine"),
                vec![],
            ),
            base_zero: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_chi_bilinear_zero"),
                vec![],
            ),
            two: Expr::app(s.clone(), Expr::app(s, z)),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
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
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn nadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [a, b])
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            n.clone(),
        )
    }
    fn last(&self, n: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.last"), vec![]),
            [n.clone()],
        )
    }
    fn chi(&self, n: Expr, s: Expr, x: Expr) -> Expr {
        Expr::apps(self.d.chi(), [n, s, x])
    }
    fn pm(&self, b: Expr) -> Expr {
        Expr::app(self.d.pm.clone(), b)
    }
    fn restrict(&self, parent: &EnvDeclBuilder, n: &Expr, p: &Expr) -> Expr {
        self.d.restrict(parent, n, p)
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.d.mul(a, b)
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        self.d.add(a, b)
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        self.d.eq_rat(l, r)
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        self.d.trans_rat(a, b, cc, h1, h2)
    }
    fn congr_rat(&self, from: Expr, to: Expr, motive: Expr, h: Expr) -> Expr {
        self.d.congr_rat(from, to, motive, h)
    }
    fn eq_symm_rat(&self, l: Expr, r: Expr, h: Expr) -> Expr {
        self.d.eq_symm_rat(l, r, h)
    }
    fn fsum(&self, n: Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n, f])
    }
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
            [a, b],
        )
    }

    /// The subset-sum integrand `fun S => chi n S x · chi n S y`.
    fn ss_int(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let body = self.mul(
            self.chi(n.clone(), s.clone(), x.clone()),
            self.chi(n.clone(), s, y.clone()),
        );
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// The product integrand `fun i => 1 + pm(x i)·pm(y i)` on `Fin n`.
    fn prod_int(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let pm_x = self.pm(Expr::app(x.clone(), i.clone()));
        let pm_y = self.pm(Expr::app(y.clone(), i.clone()));
        let body = self.add(self.d.rat_one.clone(), self.mul(pm_x, pm_y));
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    fn ss_lhs(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.subset_sum.clone(),
            [n.clone(), self.ss_int(parent, n, x, y)],
        )
    }
    fn prod_rhs(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.fin_prod.clone(),
            [n.clone(), self.prod_int(parent, n, x, y)],
        )
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
            [self.d.nat.clone(), p2sn.clone(), sum_pow.clone(), e_fwd],
        );
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (m_id, m) = mb.fresh_local(self.d.nat.clone());
            mb.finish_child(mb.mk_lam(
                m_id,
                BinderInfo::Default,
                self.d.nat.clone(),
                self.fin_of(&m),
            ))
        };
        Expr::apps(
            self.eq_ndrec_fin.clone(),
            [self.d.nat.clone(), sum_pow, motive, mapped, p2sn, e],
        )
    }
    /// `fun (j : Fin (2^n)) => chi(n+1)(Shalf j)x · chi(n+1)(Shalf j)y` — the
    /// cube-split half integrand subsetSum_split produces (G applied to the
    /// decoded subset).
    fn half_int(
        &self,
        parent: &EnvDeclBuilder,
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
        let body = self.mul(
            self.chi(sn.clone(), s_half.clone(), x.clone()),
            self.chi(sn.clone(), s_half, y.clone()),
        );
        b.finish_child(b.mk_lam(j_id, BinderInfo::Default, self.fin_of(&p2n), body))
    }
    /// `fun (j : Fin (2^n)) => chi n (hcDecode n j) xr · chi n (hcDecode n j) yr`
    /// — the prefix integrand, def-eq to `ss_int n xr yr ∘ hcDecode n` (i.e. to
    /// the summand of `subsetSum n (ss_int n xr yr)`).
    fn prefix_int(&self, parent: &EnvDeclBuilder, n: &Expr, xr: &Expr, yr: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let p2n = self.pow2(n);
        let (j_id, j) = b.fresh_local(self.fin_of(&p2n));
        let dec = Expr::apps(self.hc_decode.clone(), [n.clone(), j.clone()]);
        let body = self.mul(
            self.chi(n.clone(), dec.clone(), xr.clone()),
            self.chi(n.clone(), dec, yr.clone()),
        );
        b.finish_child(b.mk_lam(j_id, BinderInfo::Default, self.fin_of(&p2n), body))
    }
    /// `fun (j : Fin (2^n)) => c · prefix(j)` — the scaled integrand for Fin.sum_smul.
    fn scaled_int(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        xr: &Expr,
        yr: &Expr,
        cc: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let p2n = self.pow2(n);
        let (j_id, j) = b.fresh_local(self.fin_of(&p2n));
        let dec = Expr::apps(self.hc_decode.clone(), [n.clone(), j.clone()]);
        let pre = self.mul(
            self.chi(n.clone(), dec.clone(), xr.clone()),
            self.chi(n.clone(), dec, yr.clone()),
        );
        let body = self.mul(cc.clone(), pre);
        b.finish_child(b.mk_lam(j_id, BinderInfo::Default, self.fin_of(&p2n), body))
    }
}

fn build_ind_motive(c: &DeltaIndConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.d.nat.clone());
    let hcp = c.hcpoint_of(&k);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (y_id, y) = b.fresh_local(hcp.clone());
    let lhs = c.ss_lhs(&b, &k, &x, &y);
    let rhs = c.prod_rhs(&b, &k, &x, &y);
    let concl = c.eq_rat(lhs, rhs);
    let body = b.mk_pi(y_id, BinderInfo::Default, hcp.clone(), concl);
    let body = b.mk_pi(x_id, BinderInfo::Default, hcp, body);
    b.finish(b.mk_lam(k_id, BinderInfo::Default, c.d.nat.clone(), body))
}

fn build_ind_base(c: &DeltaIndConsts) -> Expr {
    // motive 0 := ∀ x y : HCPoint 0, ... — exactly subsetSum_chi_bilinear_zero
    // (its statement is def-eq to `motive Nat.zero`).
    c.base_zero.clone()
}

fn build_ind_step(c: &DeltaIndConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.d.nat.clone());
    let sn = c.succ(&k);

    // ih : ∀ x y : HCPoint k, subsetSum k (ss_int) = Fin.prod k (prod_int)
    let ih_ty = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&k);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let (y_id, y) = d.fresh_local(hcp.clone());
        let lhs = c.ss_lhs(&d, &k, &x, &y);
        let rhs = c.prod_rhs(&d, &k, &x, &y);
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
    // c_top := 1 + pm(x last)·pm(y last)
    let x_last = Expr::app(x.clone(), c.last(&k));
    let y_last = Expr::app(y.clone(), c.last(&k));
    let c_top = c.add(c.d.rat_one.clone(), c.mul(c.pm(x_last), c.pm(y_last)));

    // Σ LO, Σ HI (subsetSum_split halves).
    let lo_int = c.half_int(&b, &k, &x, &y, &c.cast_add);
    let hi_int = c.half_int(&b, &k, &x, &y, &c.add_nat);
    let sum_lo = c.fsum(p2k.clone(), lo_int.clone());
    let sum_hi = c.fsum(p2k.clone(), hi_int.clone());
    let split_rhs = c.add(sum_lo.clone(), sum_hi.clone());

    // ss_lhs(k+1) := subsetSum (k+1) (ss_int (k+1) x y).
    let ss_lhs_sn = c.ss_lhs(&b, &sn, &x, &y);

    // A : ss_lhs(k+1) = Σ LO + Σ HI    (subsetSum_split k (ss_int (k+1) x y))
    let g_sn = c.ss_int(&b, &sn, &x, &y);
    let leg_a = Expr::apps(c.subset_sum_split.clone(), [k.clone(), g_sn]);

    // pair_int : fun j => LO(j) + HI(j)
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

    // B : Σ LO + Σ HI = Σ (LO+HI)     (Eq.symm (Fin.sum_add (2^k) lo hi))
    let sum_add_fwd = Expr::apps(
        c.sum_add.clone(),
        [p2k.clone(), lo_int.clone(), hi_int.clone()],
    );
    let leg_b = c.eq_symm_rat(sum_pair.clone(), split_rhs.clone(), sum_add_fwd);

    // scaled_int : fun j => c_top · prefix(j)
    let scaled_int = c.scaled_int(&b, &k, &xr, &yr, &c_top);
    let sum_scaled = c.fsum(p2k.clone(), scaled_int.clone());

    // C : Σ (LO+HI) = Σ (c_top · prefix)   via Fin.sum_congr + per-index
    //     (combine then mul_comm to put scalar on the LEFT).
    let pointwise = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = d.fresh_local(c.fin_of(&p2k));
        // combine k x y j : LO(j)+HI(j) = prefix(j) · c_top
        let combine_j = Expr::apps(
            c.combine.clone(),
            [k.clone(), x.clone(), y.clone(), j.clone()],
        );
        // prefix(j) and the pair LO(j)+HI(j) terms.
        let dec = Expr::apps(c.hc_decode.clone(), [k.clone(), j.clone()]);
        let prefix_j = c.mul(
            c.chi(k.clone(), dec.clone(), xr.clone()),
            c.chi(k.clone(), dec, yr.clone()),
        );
        let lo_j = Expr::app(lo_int.clone(), j.clone());
        let hi_j = Expr::app(hi_int.clone(), j.clone());
        let pair_j = c.add(lo_j, hi_j);
        let pref_top = c.mul(prefix_j.clone(), c_top.clone());
        let top_pref = c.mul(c_top.clone(), prefix_j.clone());
        // mul_comm prefix(j) c_top : prefix(j)·c_top = c_top·prefix(j)
        let comm = c.mul_comm(prefix_j.clone(), c_top.clone());
        // pair_j = prefix(j)·c_top = c_top·prefix(j)
        let proof_j = c.trans_rat(pair_j, pref_top, top_pref, combine_j, comm);
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, c.fin_of(&p2k), proof_j))
    };
    let leg_c = Expr::apps(
        c.sum_congr.clone(),
        [p2k.clone(), pair_int.clone(), scaled_int.clone(), pointwise],
    );

    // D : Σ (c_top · prefix) = c_top · Σ prefix   (Fin.sum_smul (2^k) c_top prefix_int)
    let prefix_int = c.prefix_int(&b, &k, &xr, &yr);
    let sum_prefix = c.fsum(p2k.clone(), prefix_int.clone());
    let c_sum_prefix = c.mul(c_top.clone(), sum_prefix.clone());
    let leg_d = Expr::apps(
        c.sum_smul.clone(),
        [p2k.clone(), c_top.clone(), prefix_int.clone()],
    );

    // Σ prefix ≡ subsetSum k (ss_int k xr yr)  (def-eq); IH gives = Fin.prod k.
    let ss_k = c.ss_lhs(&b, &k, &xr, &yr);
    let prod_k = c.prod_rhs(&b, &k, &xr, &yr);
    // E : c_top · subsetSum k (ss xr yr) = c_top · Fin.prod k (prod xr yr)
    //     congr (c_top ·) (ih xr yr).   (sum_prefix def-eq to ss_k.)
    let ih_xy = Expr::apps(ih.clone(), [xr.clone(), yr.clone()]);
    let mul_left_ctop = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.d.rat.clone());
        let body = c.mul(c_top.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.d.rat.clone(), body))
    };
    let c_prod_k = c.mul(c_top.clone(), prod_k.clone());
    let leg_e = c.congr_rat(ss_k.clone(), prod_k.clone(), mul_left_ctop, ih_xy);

    // F : c_top · Fin.prod k = Fin.prod k · c_top   (mul_comm)
    let prod_c = c.mul(prod_k.clone(), c_top.clone());
    let leg_f = c.mul_comm(c_top.clone(), prod_k.clone());

    // G : Fin.prod k (prod xr yr) · c_top = Fin.prod (k+1) (prod (k+1) x y)
    //     Eq.symm (Fin.prod_succ k (prod_int (k+1) x y)).
    //     (prod_int(k+1)x y ∘ castSucc ≡ prod_int k xr yr, top factor ≡ c_top.)
    let prod_int_sn = c.prod_int(&b, &sn, &x, &y);
    let prod_succ_fwd = Expr::apps(c.prod_succ.clone(), [k.clone(), prod_int_sn]);
    let prod_rhs_sn = c.prod_rhs(&b, &sn, &x, &y);
    let leg_g = c.eq_symm_rat(prod_rhs_sn.clone(), prod_c.clone(), prod_succ_fwd);

    // Chain: ss_lhs(k+1) = split_rhs = sum_pair = sum_scaled = c·Σprefix
    //        = c·Fin.prod k = Fin.prod k·c = Fin.prod (k+1).
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
    let val = b.mk_lam(k_id, BinderInfo::Default, c.d.nat.clone(), val);
    b.finish(val)
}

fn build_ind_type(c: &DeltaIndConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.d.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (y_id, y) = b.fresh_local(hcp.clone());
    let lhs = c.ss_lhs(&b, &n, &x, &y);
    let rhs = c.prod_rhs(&b, &n, &x, &y);
    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(y_id, BinderInfo::Default, hcp.clone(), concl);
    let ty = b.mk_pi(x_id, BinderInfo::Default, hcp, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.d.nat.clone(), ty);
    b.finish(ty)
}

fn build_ind_value(c: &DeltaIndConsts) -> Expr {
    let motive = build_ind_motive(c);
    let base = build_ind_base(c);
    let step = build_ind_step(c);
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.d.nat.clone());
    // @Nat.rec motive base step n  : motive n  (= ∀ x y, ...)
    let body = Expr::apps(c.nat_rec.clone(), [motive, base, step, n.clone()]);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.d.nat.clone(), body))
}

impl Environment {
    /// Register `BoolAnalysis.subsetSum_chi_bilinear`: the character bilinear-
    /// collapse delta `Σ_S χ_S(x)·χ_S(y) = Π_i (1 + pm(x_i)·pm(y_i))`. `Nat.rec`
    /// induction on `n`. Kernel-checked, constructive. Idempotent.
    pub(crate) fn register_subset_sum_chi_bilinear_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_chi_bilinear");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.register_subset_sum_chi_bilinear_zero_theorem()?;
        self.register_subset_sum_split()?;
        self.register_chi_bilinear_pair_combine_theorem()?;
        self.register_fin_prod_succ_theorem()?;
        // Fin.sum_add / Fin.sum_smul / Fin.sum_congr live in the Fin.sum overlay.
        self.init_fin_sum()?;

        let c = DeltaIndConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_ind_type(&c),
            value: build_ind_value(&c),
        })
    }
}

// ===========================================================================
// Fin.sum_swap — the finite Fubini engine.
//
//   ∀ (m n : Nat) (F : Fin m → Fin n → Rat),
//     Fin.sum m (fun i => Fin.sum n (fun j => F i j))
//       = Fin.sum n (fun j => Fin.sum m (fun i => F i j))
//
// `Nat.rec` on `m` (n fixed). Base m=0: both sides reduce to 0 (LHS `Fin.sum 0`,
// RHS `Fin.sum n (fun _ => 0)` via `Fin.sum_zero_fn`). Step: `Fin.sum_succ` on
// the outer i-index, the IH on the prefix, `Fin.sum_add` to merge the j-sums,
// and `Fin.sum_congr` to peel the RHS inner i-sum. Kernel-checked, constructive.
// ===========================================================================

struct SumSwapConsts {
    rat: Expr,
    nat: Expr,
    fin: Expr,
    nat_succ: Expr,
    fin_sum: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    nat_rec: Expr,
    sum_succ: Expr,
    sum_add: Expr,
    sum_congr: Expr,
    sum_zero_fn: Expr,
    rat_add: Expr,
    eq1: Expr,
    eq_refl1: Expr,
    eq_trans1: Expr,
    eq_symm1: Expr,
    congr_arg: Expr,
}

impl SumSwapConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin_cast_succ: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            sum_succ: Expr::const_(Name::from_string("Fin.sum_succ"), vec![]),
            sum_add: Expr::const_(Name::from_string("Fin.sum_add"), vec![]),
            sum_congr: Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
            sum_zero_fn: Expr::const_(Name::from_string("Fin.sum_zero_fn"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn fsum(&self, n: Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n, f])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    fn symm(&self, l: Expr, r: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.rat.clone(), l, r, h])
    }
    fn congr(&self, from: Expr, to: Expr, motive: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), from, to, motive, h],
        )
    }
    fn cast_succ(&self, m: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.fin_cast_succ.clone(), [m.clone(), i.clone()])
    }
    fn last(&self, m: &Expr) -> Expr {
        Expr::app(self.fin_last.clone(), m.clone())
    }
    /// `fun (i : Fin m) => Fin.sum n (fun j => F i j)` — the outer (i) integrand
    /// for the LHS double sum.
    fn outer_i(&self, parent: &EnvDeclBuilder, m: &Expr, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (i_id, i) = b.fresh_local(self.fin_of(m));
        let inner = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (j_id, j) = d.fresh_local(self.fin_of(n));
            let body = Expr::apps(f.clone(), [i.clone(), j]);
            d.finish_child(d.mk_lam(j_id, BinderInfo::Default, self.fin_of(n), body))
        };
        let body = self.fsum(n.clone(), inner);
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, self.fin_of(m), body))
    }
    /// `fun (j : Fin n) => Fin.sum m (fun i => F i j)` — the outer (j) integrand
    /// for the RHS double sum.
    fn outer_j(&self, parent: &EnvDeclBuilder, m: &Expr, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (j_id, j) = b.fresh_local(self.fin_of(n));
        let inner = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (i_id, i) = d.fresh_local(self.fin_of(m));
            let body = Expr::apps(f.clone(), [i.clone(), j.clone()]);
            d.finish_child(d.mk_lam(i_id, BinderInfo::Default, self.fin_of(m), body))
        };
        let body = self.fsum(m.clone(), inner);
        b.finish_child(b.mk_lam(j_id, BinderInfo::Default, self.fin_of(n), body))
    }
    /// `fun (i : Fin m) (j : Fin n) => F (castSucc i) j` — F restricted to the
    /// first `m` outer indices (the IH's F').
    fn f_restrict(&self, parent: &EnvDeclBuilder, m: &Expr, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (i_id, i) = b.fresh_local(self.fin_of(m));
        let inner = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (j_id, j) = d.fresh_local(self.fin_of(n));
            let body = Expr::apps(f.clone(), [self.cast_succ(m, &i), j]);
            d.finish_child(d.mk_lam(j_id, BinderInfo::Default, self.fin_of(n), body))
        };
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, self.fin_of(m), inner))
    }
    /// `Fin n → Rat` type.
    fn fin_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat.clone())
    }
    /// `(Fin m → Fin n → Rat)` type.
    fn f_type(&self, m: &Expr, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(m), self.fin_to_rat(n))
    }
}

/// motive m := ∀ (F : Fin m → Fin n → Rat),
///   Fin.sum m (outer_i) = Fin.sum n (outer_j)   (n a free param of the builder).
fn build_swap_motive(c: &SumSwapConsts, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let inner = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let f_ty = c.f_type(&m, n);
        let (f_id, f) = d.fresh_local(f_ty.clone());
        let lhs = c.fsum(m.clone(), c.outer_i(&d, &m, n, &f));
        let rhs = c.fsum(n.clone(), c.outer_j(&d, &m, n, &f));
        let concl = c.eq_rat(lhs, rhs);
        d.finish_child(d.mk_pi(f_id, BinderInfo::Default, f_ty, concl))
    };
    b.finish_child(b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), inner))
}

/// base : motive 0 := fun (F : Fin 0 → Fin n → Rat) =>
///   Eq.symm (Fin.sum_zero_fn n)   (both sides def-eq to 0).
fn build_swap_base(c: &SumSwapConsts, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let f_ty = c.f_type(&zero, n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    // Goal: Fin.sum 0 (outer_i 0 n F) = Fin.sum n (outer_j 0 n F).
    //   LHS ≡ Rat.zero (Fin.sum 0 ι-reduces).
    //   outer_j 0 n F = fun j => Fin.sum 0 (fun i => F i j).
    // We prove `Fin.sum n (outer_j) = Rat.zero` explicitly, then Eq.symm + LHS defeq:
    //   r1 : Fin.sum n (outer_j) = Fin.sum n (fun _ => 0)   [Fin.sum_congr, per-j Fin.sum_zero]
    //   r2 : Fin.sum n (fun _ => 0) = 0                     [Fin.sum_zero_fn n]
    let lhs = c.fsum(zero.clone(), c.outer_i(&b, &zero, n, &f));
    let outer_j0 = c.outer_j(&b, &zero, n, &f);
    let rhs = c.fsum(n.clone(), outer_j0.clone());
    // const-zero fn on Fin n.
    let zero_fn = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (j_id, _j) = d.fresh_local(c.fin_of(n));
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, c.fin_of(n), rat_zero))
    };
    // per-j: Fin.sum_zero (fun i => F i j) : Fin.sum 0 (fun i => F i j) = Rat.zero.
    let fin_sum_zero = Expr::const_(Name::from_string("Fin.sum_zero"), vec![]);
    let pointwise = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = d.fresh_local(c.fin_of(n));
        let inner = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (i_id, i) = e.fresh_local(c.fin_of(&zero));
            let body = Expr::apps(f.clone(), [i, j.clone()]);
            e.finish_child(e.mk_lam(i_id, BinderInfo::Default, c.fin_of(&zero), body))
        };
        let proof_j = Expr::app(fin_sum_zero.clone(), inner);
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, c.fin_of(n), proof_j))
    };
    let r1 = Expr::apps(
        c.sum_congr.clone(),
        [n.clone(), outer_j0, zero_fn.clone(), pointwise],
    );
    let sum_zero_fn = Expr::app(c.sum_zero_fn.clone(), n.clone());
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let sum_zerofn = c.fsum(n.clone(), zero_fn);
    // r : Fin.sum n (outer_j) = 0   (Eq.trans r1 sum_zero_fn).
    let r = c.trans(rhs.clone(), sum_zerofn, rat_zero.clone(), r1, sum_zero_fn);
    // Eq.symm r : 0 = rhs;  since lhs ≡ 0 (Fin.sum 0 ι-reduces), this inhabits
    // the goal `lhs = rhs`.
    let _ = lhs;
    let proof = c.symm(rhs.clone(), rat_zero, r);
    b.finish_child(b.mk_lam(f_id, BinderInfo::Default, f_ty, proof))
}

/// step : motive m → motive (m+1).
fn build_swap_step(c: &SumSwapConsts, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let sm = c.succ(&m);

    // ih : ∀ (F : Fin m → Fin n → Rat), Fin.sum m (outer_i) = Fin.sum n (outer_j)
    let ih_ty = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let f_ty = c.f_type(&m, n);
        let (f_id, f) = d.fresh_local(f_ty.clone());
        let lhs = c.fsum(m.clone(), c.outer_i(&d, &m, n, &f));
        let rhs = c.fsum(n.clone(), c.outer_j(&d, &m, n, &f));
        d.finish_child(d.mk_pi(f_id, BinderInfo::Default, f_ty, c.eq_rat(lhs, rhs)))
    };
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());

    let f_ty = c.f_type(&sm, n);
    let (f_id, f) = b.fresh_local(f_ty.clone());

    // LHS := Fin.sum (m+1) (outer_i (m+1) n F).
    let lhs = c.fsum(sm.clone(), c.outer_i(&b, &sm, n, &f));
    // RHS := Fin.sum n (outer_j (m+1) n F).
    let rhs = c.fsum(n.clone(), c.outer_j(&b, &sm, n, &f));

    // F' := fun i j => F (castSucc i) j  (the IH instance).
    let f_prime = c.f_restrict(&b, &m, n, &f);

    // ── LHS leg ──
    // step1 : LHS = Fin.sum m (outer_i m n F') + (outer_i (m+1) n F)(last m)
    //   Fin.sum_succ m (outer_i (m+1) n F).
    //   (outer_i (m+1) n F) ∘ castSucc ≡ outer_i m n F'  (defeq);
    //   (outer_i (m+1) n F)(last m) ≡ Fin.sum n (fun j => F (last m) j).
    let sum_succ_lhs = Expr::apps(c.sum_succ.clone(), [m.clone(), c.outer_i(&b, &sm, n, &f)]);
    let lhs_prefix = c.fsum(m.clone(), c.outer_i(&b, &m, n, &f_prime));
    // last term: Fin.sum n (fun j => F (last m) j).
    let last_term = {
        let inner = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (j_id, j) = d.fresh_local(c.fin_of(n));
            let body = Expr::apps(f.clone(), [c.last(&m), j]);
            d.finish_child(d.mk_lam(j_id, BinderInfo::Default, c.fin_of(n), body))
        };
        c.fsum(n.clone(), inner)
    };
    let lhs_split = c.add(lhs_prefix.clone(), last_term.clone());

    // step2 : prefix = Fin.sum n (outer_j m n F')   (ih F').
    let ih_fp = Expr::apps(ih.clone(), [f_prime.clone()]);
    let rhs_prefix = c.fsum(n.clone(), c.outer_j(&b, &m, n, &f_prime));
    // congr (· + last_term) (ih F') : prefix + last = rhs_prefix + last.
    let add_right_last = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.add(z, last_term.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let split_swapped = c.add(rhs_prefix.clone(), last_term.clone());
    let step2 = c.congr(
        lhs_prefix.clone(),
        rhs_prefix.clone(),
        add_right_last,
        ih_fp,
    );

    // step3 : rhs_prefix + last = Fin.sum n (fun j => outer_j m n F' j + (fun j => F (last m) j) j)
    //   Eq.symm (Fin.sum_add n (outer_j m n F') (fun j => F (last m) j)).
    let last_fn = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = d.fresh_local(c.fin_of(n));
        let body = Expr::apps(f.clone(), [c.last(&m), j]);
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, c.fin_of(n), body))
    };
    let outer_j_fp = c.outer_j(&b, &m, n, &f_prime);
    let merged_fn = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = d.fresh_local(c.fin_of(n));
        let a = Expr::app(outer_j_fp.clone(), j.clone());
        let bb = Expr::app(last_fn.clone(), j.clone());
        let body = c.add(a, bb);
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, c.fin_of(n), body))
    };
    let sum_merged = c.fsum(n.clone(), merged_fn.clone());
    let sum_add_fwd = Expr::apps(
        c.sum_add.clone(),
        [n.clone(), outer_j_fp.clone(), last_fn.clone()],
    );
    let step3 = c.symm(sum_merged.clone(), split_swapped.clone(), sum_add_fwd);

    // ── RHS leg ──
    // The RHS `Fin.sum n (outer_j (m+1) n F)` has integrand at j:
    //   Fin.sum (m+1) (fun i => F i j).
    // By Fin.sum_succ on i (inside, per j): = Fin.sum m (fun i => F (castSucc i) j) + F (last m) j
    //   = outer_j m n F' j + last_fn j = merged_fn j  (defeq).
    // So `Fin.sum n (outer_j (m+1) n F) = Fin.sum n merged_fn`  via Fin.sum_congr +
    // per-j Fin.sum_succ.  We prove this as `rhs = sum_merged` then chain.
    let pointwise_rhs = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = d.fresh_local(c.fin_of(n));
        // Fin.sum_succ m (fun i => F i j) : Fin.sum (m+1)(fun i=>F i j)
        //   = Fin.sum m (fun i => F (castSucc i) j) + F (last m) j
        let inner_full = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (i_id, i) = e.fresh_local(c.fin_of(&sm));
            let body = Expr::apps(f.clone(), [i, j.clone()]);
            e.finish_child(e.mk_lam(i_id, BinderInfo::Default, c.fin_of(&sm), body))
        };
        let proof_j = Expr::apps(c.sum_succ.clone(), [m.clone(), inner_full]);
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, c.fin_of(n), proof_j))
    };
    let outer_j_sm = c.outer_j(&b, &sm, n, &f);
    let step_rhs = Expr::apps(
        c.sum_congr.clone(),
        [
            n.clone(),
            outer_j_sm.clone(),
            merged_fn.clone(),
            pointwise_rhs,
        ],
    );
    // step_rhs : Fin.sum n (outer_j (m+1) n F) = Fin.sum n merged_fn = sum_merged.

    // Chain forward: LHS = lhs_split = split_swapped = sum_merged.
    let t1 = c.trans(
        lhs.clone(),
        lhs_split.clone(),
        split_swapped.clone(),
        sum_succ_lhs,
        step2,
    );
    let lhs_to_merged = c.trans(lhs.clone(), split_swapped, sum_merged.clone(), t1, step3);
    // RHS = sum_merged via step_rhs;  so LHS = sum_merged = RHS via Eq.symm step_rhs.
    let merged_to_rhs = c.symm(rhs.clone(), sum_merged.clone(), step_rhs);
    let proof = c.trans(lhs, sum_merged, rhs, lhs_to_merged, merged_to_rhs);

    let val = b.mk_lam(f_id, BinderInfo::Default, f_ty, proof);
    let val = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, val);
    let val = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish_child(val)
}

fn build_swap_type(c: &SumSwapConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.f_type(&m, &n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let lhs = c.fsum(m.clone(), c.outer_i(&b, &m, &n, &f));
    let rhs = c.fsum(n.clone(), c.outer_j(&b, &m, &n, &f));
    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(f_id, BinderInfo::Default, f_ty, concl);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    let ty = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), ty);
    b.finish(ty)
}

fn build_swap_value(c: &SumSwapConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let motive = build_swap_motive(c, &b, &n);
    let base = build_swap_base(c, &b, &n);
    let step = build_swap_step(c, &b, &n);
    // @Nat.rec motive base step m : motive m  (= ∀ F, ...).
    let rec = Expr::apps(c.nat_rec.clone(), [motive, base, step, m.clone()]);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec);
    let val = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Fin.sum_swap : ∀ (m n) (F : Fin m → Fin n → Rat),
    ///   Σ_i Σ_j F i j = Σ_j Σ_i F i j`. The finite Fubini engine. `Nat.rec` on
    /// `m`. Kernel-checked, constructive. Idempotent.
    pub(crate) fn register_fin_sum_swap_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_swap");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_fin_sum()?; // sum_succ, sum_add, sum_congr, sum_zero_fn

        let c = SumSwapConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_swap_type(&c),
            value: build_swap_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_chi_factor_pair_sum_theorem()
            .expect("register_chi_factor_pair_sum_theorem");
        env
    }

    #[test]
    fn test_chi_factor_pair_sum_is_constructive_theorem() {
        let env = make_env();
        let name = Name::from_string("BoolAnalysis.chi_factor_pair_sum");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("chi_factor_pair_sum proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "chi_factor_pair_sum must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "chi_factor_pair_sum's transitive axiom closure must be empty"
        );
    }

    #[test]
    fn test_fin_sum_swap_is_constructive_theorem() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_fin_sum_swap_theorem()
            .expect("register_fin_sum_swap_theorem");
        let name = Name::from_string("Fin.sum_swap");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("Fin.sum_swap proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "Fin.sum_swap must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "Fin.sum_swap's transitive axiom closure must be empty"
        );
    }

    #[test]
    fn test_subset_sum_chi_bilinear_is_constructive_theorem() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_subset_sum_chi_bilinear_theorem()
            .expect("register_subset_sum_chi_bilinear_theorem");
        let name = Name::from_string("BoolAnalysis.subsetSum_chi_bilinear");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("subsetSum_chi_bilinear proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "subsetSum_chi_bilinear must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "subsetSum_chi_bilinear's transitive axiom closure must be empty"
        );
    }

    #[test]
    fn test_chi_bilinear_pair_combine_is_constructive_theorem() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_chi_bilinear_pair_combine_theorem()
            .expect("register_chi_bilinear_pair_combine_theorem");
        let name = Name::from_string("BoolAnalysis.chi_bilinear_pair_combine");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("chi_bilinear_pair_combine proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "chi_bilinear_pair_combine must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "chi_bilinear_pair_combine's transitive axiom closure must be empty"
        );
    }

    #[test]
    fn test_chi_pair_succ_is_constructive_theorem() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_chi_pair_succ_theorem()
            .expect("register_chi_pair_succ_theorem");
        let name = Name::from_string("BoolAnalysis.chi_pair_succ");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("chi_pair_succ proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "chi_pair_succ must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "chi_pair_succ's transitive axiom closure must be empty"
        );
    }

    #[test]
    fn test_rat_mul_mul_mul_comm_is_constructive_theorem() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_rat_mul_mul_mul_comm_theorem()
            .expect("register_rat_mul_mul_mul_comm_theorem");
        let name = Name::from_string("Rat.mul_mul_mul_comm");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("Rat.mul_mul_mul_comm proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "Rat.mul_mul_mul_comm must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "Rat.mul_mul_mul_comm's transitive axiom closure must be empty"
        );
    }

    #[test]
    fn test_subset_sum_chi_bilinear_zero_is_constructive_theorem() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_subset_sum_chi_bilinear_zero_theorem()
            .expect("register_subset_sum_chi_bilinear_zero_theorem");
        let name = Name::from_string("BoolAnalysis.subsetSum_chi_bilinear_zero");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("subsetSum_chi_bilinear_zero proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "subsetSum_chi_bilinear_zero must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "subsetSum_chi_bilinear_zero's transitive axiom closure must be empty"
        );
    }
}
