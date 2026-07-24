// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rung 5 of the Parseval infrastructure ladder — the cube-bit recursion split.
//!
//! Two kernel-checked, axiom-free terms:
//!
//! - `Fin.sum_cast : ∀ (a b : Nat), @Eq Nat b a → (F : Fin a → Rat) →`
//!   `  @Eq Rat (Fin.sum a F) (Fin.sum b (fun i => F (cast_{b→a} i)))`
//!   where `cast_{b→a} i := @Eq.ndrec Nat b (fun m => Fin m) i a e`. Reindex a
//!   `Fin.sum` along a propositional equality of the index bound. Proved by
//!   `Eq.rec` on `e`: in the `e = rfl` case the transport collapses to the
//!   identity and the goal is `rfl`.
//!
//! - `BoolAnalysis.hcSumSplit : ∀ (n : Nat) (g : HCPoint (n+1) → Rat),`
//!   `  @Eq Rat (Fin.sum (2^(n+1)) (fun k => g (hcDecode (n+1) k)))`
//!   `          (Rat.add (Fin.sum (2^n) (fun i => g (hcDecode (n+1) (castP (castAdd (2^n) (2^n) i)))))`
//!   `                   (Fin.sum (2^n) (fun j => g (hcDecode (n+1) (castP (addNat  (2^n) (2^n) j))))))`
//!   where `castP : Fin (2^n + 2^n) → Fin (2^(n+1))` is the index transport
//!   built from `(Nat.pow_two_succ n).symm`. This is the `2^(n+1)`-cube sum
//!   split into its `2^n` low/high halves (bit `n` = 0 / bit `n` = 1).
//!
//! Route: `Fin.sum_cast` (rung-5 helper) transports the `2^(n+1)` sum to a
//! `2^n + 2^n` sum (via `Nat.pow_two_succ`, rung 3), and `Fin.sum_split_add`
//! (rung 2) splits the `2^n + 2^n` sum into the `Fin.castAdd` / `Fin.addNat`
//! halves (rung 1). Pure composition of the lower rungs — no `sorry`, no
//! axiom: the closure routes through `Fin.sum_cast` / `Fin.sum_split_add` /
//! `Nat.pow_two_succ` and the `Eq` built-ins only.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct C {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    two: Expr,
    fin_sum: Expr,
    rat_add: Expr,
    eq_nat: Expr, // Eq.{1} for Nat / Rat (Sort 1)
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_rec: Expr,       // Eq.rec.{u=1, v=1}
    eq_ndrec_fin: Expr, // Eq.ndrec.{motive_u=1, alpha_u=1}: motive Nat → Type (Fin m)
    cast_add: Expr,
    add_nat: Expr,
    hc_decode: Expr,
    fin_sum_cast: Expr,
    fin_sum_split: Expr,
    pow_two_succ: Expr,
}

impl C {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_one = Expr::app(nat_succ.clone(), nat_zero);
        let two = Expr::app(nat_succ.clone(), nat_one);
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nat_succ,
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            two,
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            eq_nat: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            // Eq.rec.{motive_u, alpha_u}; here motive lands in Sort 1 (Prop is
            // Sort 0 but our equation is in Prop). Use motive_u = 0 (Prop), α in
            // Sort 1 (Nat : Type 0 = Sort 1).
            eq_rec: Expr::const_(Name::from_string("Eq.rec"), vec![Level::zero(), l1.clone()]),
            // Eq.ndrec transporting `i : Fin b` to `Fin a`: motive `fun m => Fin m`
            // lands in `Type 0 = Sort 1`, α = Nat in Sort 1.
            eq_ndrec_fin: Expr::const_(Name::from_string("Eq.ndrec"), vec![l1.clone(), l1.clone()]),
            cast_add: Expr::const_(Name::from_string("Fin.castAdd"), vec![]),
            add_nat: Expr::const_(Name::from_string("Fin.addNat"), vec![]),
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            fin_sum_cast: Expr::const_(Name::from_string("Fin.sum_cast"), vec![]),
            fin_sum_split: Expr::const_(Name::from_string("Fin.sum_split_add"), vec![]),
            pow_two_succ: Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn fin_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat.clone())
    }
    fn sum(&self, n: Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n, f])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq_nat.clone(), [self.rat.clone(), l, r])
    }
    fn eq_nat_(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq_nat.clone(), [self.nat.clone(), l, r])
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    /// `@Eq.ndrec Nat b (fun m => Fin m) i a e : Fin a` — transport `i : Fin b`
    /// to `Fin a` along `e : @Eq Nat b a`.
    fn cast_fin(&self, parent: &EnvDeclBuilder, b: &Expr, a: &Expr, i: &Expr, e: &Expr) -> Expr {
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (m_id, m) = mb.fresh_local(self.nat.clone());
            let body = self.fin_of(&m);
            mb.finish_child(mb.mk_lam(m_id, BinderInfo::Default, self.nat.clone(), body))
        };
        Expr::apps(
            self.eq_ndrec_fin.clone(),
            [
                self.nat.clone(),
                b.clone(),
                motive,
                i.clone(),
                a.clone(),
                e.clone(),
            ],
        )
    }
}

// ===========================================================================
// Fin.sum_cast
// ===========================================================================

/// `Fin.sum_cast : ∀ (a b : Nat) (e : @Eq Nat b a) (F : Fin a → Rat),`
/// `  @Eq Rat (Fin.sum a F) (Fin.sum b (fun i => F (cast_{b→a} i)))`.
fn build_fin_sum_cast(c: &C) -> (Expr, Expr) {
    // summand_rhs(a, b, e, F) := fun (i : Fin b) => F (cast_fin b a i e)
    let summand_rhs = |parent: &EnvDeclBuilder, a: &Expr, b: &Expr, e: &Expr, f: &Expr| -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let (i_id, i) = sb.fresh_local(c.fin_of(b));
        let casted = c.cast_fin(&sb, b, a, &i, e);
        let body = Expr::app(f.clone(), casted);
        sb.finish_child(sb.mk_lam(i_id, BinderInfo::Default, c.fin_of(b), body))
    };

    // concl(a, b, e, F) := Eq Rat (Fin.sum a F) (Fin.sum b (summand_rhs))
    let concl = |parent: &EnvDeclBuilder, a: &Expr, b: &Expr, e: &Expr, f: &Expr| -> Expr {
        let lhs = c.sum(a.clone(), f.clone());
        let rhs = c.sum(b.clone(), summand_rhs(parent, a, b, e, f));
        c.eq_rat(lhs, rhs)
    };

    // Type: ∀ (a b : Nat) (e : Eq Nat b a) (F : Fin a → Rat), concl
    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let e_ty = c.eq_nat_(bb.clone(), a.clone());
        let (e_id, e) = b.fresh_local(e_ty.clone());
        let f_ty = c.fin_to_rat(&a);
        let (f_id, f) = b.fresh_local(f_ty.clone());
        let body = concl(&b, &a, &bb, &e, &f);
        let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, body);
        let r = b.mk_pi(e_id, BinderInfo::Default, e_ty, r);
        let r = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), r);
        let r = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };

    // Value: fun (a b : Nat) (e : Eq Nat b a) =>
    //   @Eq.rec Nat b
    //     (motive := fun (a' : Nat) (e' : Eq Nat b a') => ∀ F : Fin a' → Rat, concl a' b e' F)
    //     (base   := fun F => @Eq.refl Rat (Fin.sum b F))
    //     a e
    //
    // Note: motive abstracts the TARGET `a`, leaving `b` fixed; `Eq.rec` on
    // `e : b = a`. At `a = b, e = rfl`, cast_fin collapses to identity so the
    // RHS summand is `fun i => F i` ≡ `F`, hence `Fin.sum b F = Fin.sum b F`.
    let value = {
        let mut vb = EnvDeclBuilder::new();
        let (a_id, a) = vb.fresh_local(c.nat.clone());
        let (bb_id, bb) = vb.fresh_local(c.nat.clone());
        let e_ty = c.eq_nat_(bb.clone(), a.clone());
        let (e_id, e) = vb.fresh_local(e_ty.clone());

        // motive : (a' : Nat) → (e' : Eq Nat b a') → Prop
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&vb);
            let (ap_id, ap) = mb.fresh_local(c.nat.clone());
            let ep_ty = c.eq_nat_(bb.clone(), ap.clone());
            let (ep_id, ep) = mb.fresh_local(ep_ty.clone());
            // ∀ F : Fin a' → Rat, concl a' b e' F
            let f_ty = c.fin_to_rat(&ap);
            let (f_id, f) = mb.fresh_local(f_ty.clone());
            let body = concl(&mb, &ap, &bb, &ep, &f);
            let pi = mb.mk_pi(f_id, BinderInfo::Default, f_ty, body);
            let lam = mb.mk_lam(ep_id, BinderInfo::Default, ep_ty, pi);
            let lam = mb.mk_lam(ap_id, BinderInfo::Default, c.nat.clone(), lam);
            mb.finish_child(lam)
        };

        // base : motive b rfl = ∀ F : Fin b → Rat, Fin.sum b F = Fin.sum b (fun i => F (cast_id i))
        //   cast_id with e = rfl reduces to i, so summand ≡ F; refl.
        let base = {
            let mut bb_b = EnvDeclBuilder::child_of(&vb);
            let f_ty = c.fin_to_rat(&bb);
            let (f_id, f) = bb_b.fresh_local(f_ty.clone());
            // @Eq.refl Rat (Fin.sum b F)
            let sum_bf = c.sum(bb.clone(), f.clone());
            let refl = Expr::apps(c.eq_refl1.clone(), [c.rat.clone(), sum_bf]);
            let lam = bb_b.mk_lam(f_id, BinderInfo::Default, f_ty, refl);
            bb_b.finish_child(lam)
        };

        // @Eq.rec Nat b motive base a e : motive a e
        let rec_app = Expr::apps(
            c.eq_rec.clone(),
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
        let lam = vb.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), lam);
        vb.finish(lam)
    };

    (type_, value)
}

// ===========================================================================
// BoolAnalysis.hcSumSplit
// ===========================================================================

/// `BoolAnalysis.hcSumSplit : ∀ (n : Nat) (g : HCPoint (n+1) → Rat),`
/// `  @Eq Rat (Fin.sum (2^(n+1)) (fun k => g (hcDecode (n+1) k)))`
/// `          (Rat.add LOW HIGH)` — the cube-bit recursion split.
fn build_hc_sum_split(c: &C) -> (Expr, Expr) {
    let hcpoint = Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]);
    let hcpoint_of = |n: &Expr| Expr::app(hcpoint.clone(), n.clone());
    let hcpoint_to_rat = |n: &Expr| Expr::pi(BinderInfo::Default, hcpoint_of(n), c.rat.clone());

    // g_decode(n+1, g) := fun (k : Fin (2^(n+1))) => g (hcDecode (n+1) k)
    let g_decode = |parent: &EnvDeclBuilder, sn: &Expr, g: &Expr| -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let p2sn = c.pow2(sn);
        let (k_id, k) = sb.fresh_local(c.fin_of(&p2sn));
        let decoded = Expr::apps(c.hc_decode.clone(), [sn.clone(), k.clone()]);
        let body = Expr::app(g.clone(), decoded);
        sb.finish_child(sb.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2sn), body))
    };

    // half-summand for the LOW block:
    //   fun (i : Fin (2^n)) => g (hcDecode (n+1) (castP (castAdd (2^n) (2^n) i)))
    // where castP : Fin (2^n+2^n) → Fin (2^(n+1)) := cast_fin (2^n+2^n) (2^(n+1)) _ (pow_two_succ n).symm
    // We reuse the SAME body the rung-2 split produces after rung-5 cast, so we
    // build LOW/HIGH directly to match the proof's reduced form.
    // mk_half(idx_map) := fun (i : Fin (2^n)) => g (hcDecode (n+1) (castP (idx_map (2^n) (2^n) i)))
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let mk_half =
        |parent: &EnvDeclBuilder, n: &Expr, sn: &Expr, g: &Expr, idx_map: &Expr| -> Expr {
            let mut hb = EnvDeclBuilder::child_of(parent);
            let p2n = c.pow2(n);
            let (i_id, i) = hb.fresh_local(c.fin_of(&p2n));
            // idx_map (2^n) (2^n) i : Fin (2^n + 2^n)
            let mapped = Expr::apps(idx_map.clone(), [p2n.clone(), p2n.clone(), i.clone()]);
            // castP : transport Fin (2^n+2^n) → Fin (2^(n+1)) along e : (2^n+2^n) = 2^(n+1)
            let sum_pow = Expr::apps(nat_add.clone(), [p2n.clone(), p2n.clone()]);
            let p2sn = c.pow2(sn);
            // e_fwd : Eq Nat (2^(n+1)) (2^n+2^n) := pow_two_succ n
            let e_fwd = Expr::app(c.pow_two_succ.clone(), n.clone());
            // e : Eq Nat (2^n+2^n) (2^(n+1)) := Eq.symm e_fwd
            let e = Expr::apps(
                c.eq_symm1.clone(),
                [c.nat.clone(), p2sn.clone(), sum_pow.clone(), e_fwd],
            );
            let casted = c.cast_fin(&hb, &sum_pow, &p2sn, &mapped, &e);
            let decoded = Expr::apps(c.hc_decode.clone(), [sn.clone(), casted]);
            let body = Expr::app(g.clone(), decoded);
            hb.finish_child(hb.mk_lam(i_id, BinderInfo::Default, c.fin_of(&p2n), body))
        };

    // concl(n, g):  Fin.sum (2^(n+1)) (g_decode) = Rat.add (Fin.sum (2^n) LOW) (Fin.sum (2^n) HIGH)
    let concl = |parent: &EnvDeclBuilder, n: &Expr, g: &Expr| -> (Expr, Expr) {
        let sn = c.succ(n.clone());
        let p2sn = c.pow2(&sn);
        let p2n = c.pow2(n);
        let lhs = c.sum(p2sn, g_decode(parent, &sn, g));
        let low = c.sum(p2n.clone(), mk_half(parent, n, &sn, g, &c.cast_add));
        let high = c.sum(p2n, mk_half(parent, n, &sn, g, &c.add_nat));
        let rhs = c.add(low, high);
        (lhs, rhs)
    };

    // Type: ∀ (n : Nat) (g : HCPoint (n+1) → Rat), Eq Rat lhs rhs
    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let sn = c.succ(n.clone());
        let g_ty = hcpoint_to_rat(&sn);
        let (g_id, g) = b.fresh_local(g_ty.clone());
        let (lhs, rhs) = concl(&b, &n, &g);
        let body = c.eq_rat(lhs, rhs);
        let r = b.mk_pi(g_id, BinderInfo::Default, g_ty, body);
        let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };

    // Value: fun (n : Nat) (g : HCPoint (n+1) → Rat) =>
    //   let sn := succ n; F := g_decode sn g : Fin (2^(n+1)) → Rat
    //   e_fwd : 2^(n+1) = 2^n+2^n := pow_two_succ n
    //   step1 : Fin.sum (2^(n+1)) F = Fin.sum (2^n+2^n) (fun i => F (cast_fin (2^n+2^n) (2^(n+1)) i (symm e_fwd)))
    //         := Fin.sum_cast (2^(n+1)) (2^n+2^n) (symm e_fwd) F
    //   step2 : Fin.sum (2^n+2^n) F' = Rat.add (Fin.sum (2^n) low') (Fin.sum (2^n) high')
    //         := Fin.sum_split_add (2^n) (2^n) F'
    //   where F' := fun i => F (cast_fin ... i (symm e_fwd))
    //         low'  := fun i => F' (castAdd (2^n) (2^n) i)
    //         high' := fun j => F' (addNat  (2^n) (2^n) j)
    //   By δ-reduction F' (castAdd ... i) ≡ F (cast_fin (castAdd ... i)) ≡
    //     g (hcDecode sn (castP (castAdd ... i))) = LOW i, definitionally; same
    //     for HIGH. So Eq.trans step1 step2 : lhs = rhs.
    let value = {
        let mut vb = EnvDeclBuilder::new();
        let (n_id, n) = vb.fresh_local(c.nat.clone());
        let sn = c.succ(n.clone());
        let g_ty = hcpoint_to_rat(&sn);
        let (g_id, g) = vb.fresh_local(g_ty.clone());

        let p2sn = c.pow2(&sn);
        let p2n = c.pow2(&n);
        let sum_pow = Expr::apps(nat_add.clone(), [p2n.clone(), p2n.clone()]);

        // F : Fin (2^(n+1)) → Rat
        let big_f = g_decode(&vb, &sn, &g);

        // e_fwd : 2^(n+1) = 2^n+2^n
        let e_fwd = Expr::app(c.pow_two_succ.clone(), n.clone());
        // e_sym : 2^n+2^n = 2^(n+1)
        let e_sym = Expr::apps(
            c.eq_symm1.clone(),
            [c.nat.clone(), p2sn.clone(), sum_pow.clone(), e_fwd.clone()],
        );

        // F' : Fin (2^n+2^n) → Rat := fun i => F (cast_fin (2^n+2^n) (2^(n+1)) i e_sym)
        let big_f_prime = {
            let mut fb = EnvDeclBuilder::child_of(&vb);
            let (i_id, i) = fb.fresh_local(c.fin_of(&sum_pow));
            let casted = c.cast_fin(&fb, &sum_pow, &p2sn, &i, &e_sym);
            let body = Expr::app(big_f.clone(), casted);
            fb.finish_child(fb.mk_lam(i_id, BinderInfo::Default, c.fin_of(&sum_pow), body))
        };

        // step1 : Fin.sum (2^(n+1)) F = Fin.sum (2^n+2^n) F'
        //   = Fin.sum_cast (2^(n+1)) (2^n+2^n) e_sym F
        let step1 = Expr::apps(
            c.fin_sum_cast.clone(),
            [p2sn.clone(), sum_pow.clone(), e_sym.clone(), big_f.clone()],
        );

        // step2 : Fin.sum (2^n+2^n) F' = Rat.add (Fin.sum (2^n) low') (Fin.sum (2^n) high')
        //   = Fin.sum_split_add (2^n) (2^n) F'
        let step2 = Expr::apps(
            c.fin_sum_split.clone(),
            [p2n.clone(), p2n.clone(), big_f_prime.clone()],
        );

        // Compose: Eq.trans (lhs) (mid) (rhs) step1 step2
        // lhs = Fin.sum (2^(n+1)) F ; mid = Fin.sum (2^n+2^n) F'
        // rhs = Rat.add (Fin.sum (2^n) low') (Fin.sum (2^n) high')
        let lhs = c.sum(p2sn.clone(), big_f.clone());
        let mid = c.sum(sum_pow.clone(), big_f_prime.clone());
        // rhs from split: build low'/high' summands the way Fin.sum_split_add states them
        let low_prime = {
            let mut lb = EnvDeclBuilder::child_of(&vb);
            let (i_id, i) = lb.fresh_local(c.fin_of(&p2n));
            let ca = Expr::apps(c.cast_add.clone(), [p2n.clone(), p2n.clone(), i.clone()]);
            let body = Expr::app(big_f_prime.clone(), ca);
            lb.finish_child(lb.mk_lam(i_id, BinderInfo::Default, c.fin_of(&p2n), body))
        };
        let high_prime = {
            let mut hb = EnvDeclBuilder::child_of(&vb);
            let (j_id, j) = hb.fresh_local(c.fin_of(&p2n));
            let an = Expr::apps(c.add_nat.clone(), [p2n.clone(), p2n.clone(), j.clone()]);
            let body = Expr::app(big_f_prime.clone(), an);
            hb.finish_child(hb.mk_lam(j_id, BinderInfo::Default, c.fin_of(&p2n), body))
        };
        let rhs = c.add(
            c.sum(p2n.clone(), low_prime),
            c.sum(p2n.clone(), high_prime),
        );

        let eq_trans = Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        );
        let composed = Expr::apps(eq_trans, [c.rat.clone(), lhs, mid, rhs, step1, step2]);

        let lam = vb.mk_lam(g_id, BinderInfo::Default, g_ty, composed);
        let lam = vb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
        vb.finish(lam)
    };

    (type_, value)
}

impl Environment {
    /// Register `Fin.sum_cast` and `BoolAnalysis.hcSumSplit` — rung 5 of the
    /// Parseval infrastructure ladder.
    pub(crate) fn register_hc_sum_split_theorem(&mut self) -> Result<(), EnvError> {
        // Dependencies: rungs 1-3 and the Fin.sum / hcDecode foundations.
        self.init_eq()?;
        self.init_fin_sum()?;
        self.register_fin_split_index()?; // Fin.castAdd, Fin.addNat (rung 1)
        self.register_fin_sum_split_add_theorem()?; // Fin.sum_split_add (rung 2)
        self.register_nat_pow_two_succ_proof()?; // Nat.pow_two_succ (rung 3)
        self.init_boolean_analysis_foundations()?; // HCPoint, hcDecode

        let c = C::new();

        if self.get_const(&Name::from_string("Fin.sum_cast")).is_none() {
            let (type_, value) = build_fin_sum_cast(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Fin.sum_cast"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        if self
            .get_const(&Name::from_string("BoolAnalysis.hcSumSplit"))
            .is_none()
        {
            let (type_, value) = build_hc_sum_split(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("BoolAnalysis.hcSumSplit"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // B1: `Fin.val_cast` — the value-preservation of the `castP` index
        // transport (`@Eq.ndrec Nat b (fun m => Fin m) i a e`) used in the split
        // above. The off-diagonal induction consumes it to push `Fin.val`
        // through `castP` and reach the rung-4 `testBit_*` bit lemmas.
        self.register_fin_val_cast_theorem()?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    #[test]
    fn test_hc_sum_split_type_checks_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_hc_sum_split_theorem().expect("register");
        env.register_hc_sum_split_theorem().expect("idempotent");
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in ["Fin.sum_cast", "BoolAnalysis.hcSumSplit"] {
            let n = Name::from_string(name);
            let _ = tc
                .infer_type(&Expr::const_(n.clone(), vec![]))
                .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
            assert_eq!(
                env.get_const(&n).expect("registered").kind,
                ConstantKind::Theorem,
                "{name} must be a Theorem"
            );
            let deps = env.axiom_deps(&n).expect("registered");
            let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
            assert!(names.is_empty(), "{name} must be axiom-free, got {names:?}");
            assert!(
                matches!(env.proof_quality(&n), Some(ProofQuality::Constructive)),
                "{name} must be Constructive"
            );
        }
    }
}
