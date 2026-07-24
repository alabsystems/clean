//! Constructive proof of the rung-4b Parseval ladder facts about the bit
//! pattern of `2^n + k` for `k < 2^n`.
//!
//! ```text
//! Nat.testBit_add_two_pow_self : ∀ (n k : Nat),
//!   Nat.lt k (Nat.pow 2 n) →
//!     @Eq Bool (Nat.testBit (Nat.add (Nat.pow 2 n) k) n) Bool.true
//!
//! Nat.testBit_add_two_pow_lo : ∀ (n k i : Nat),
//!   Nat.lt k (Nat.pow 2 n) → Nat.lt i n →
//!     @Eq Bool (Nat.testBit (Nat.add (Nat.pow 2 n) k) i) (Nat.testBit k i)
//! ```
//!
//! Together with rung 4a (`Nat.testBit_lt_pow`) these pin down every bit of
//! `2^n + k`: bit `n` is set, bits below `n` agree with `k`, bits above are
//! clear. This is the per-coordinate description of the "high half" of the
//! `2^(n+1)`-Walsh/Hadamard block split.
//!
//! # Supporting div2 lemmas (general `e`, not just `e = 2^m`)
//!
//! - `Nat.div2Par_add_two_mul : ∀ e k, div2Par ((e+e)+k) = div2Par k`
//!   — `Nat.rec` on `k`. Base: `div2Par ((e+e)+0) ≡ div2Par (e+e) = 0 ≡
//!   div2Par 0` (`div2Par_two_mul`). Step: `div2Par (succ x) ≡ 1 - div2Par x`
//!   definitionally, so `M (succ k') ≡ (1 - div2Par ((e+e)+k')) = (1 -
//!   div2Par k')`, i.e. `congrArg (1 - ·)` of the IH.
//! - `Nat.div2_add_two_mul : ∀ e k, div2 ((e+e)+k) = e + div2 k`
//!   — `Nat.rec` on `k`. Base: `div2 ((e+e)+0) ≡ div2 (e+e) = e ≡ e + div2 0`
//!   (`div2_two_mul`). Step: `div2 (succ x) ≡ div2 x + div2Par x`, so
//!   `div2 ((e+e)+succ k') ≡ div2 ((e+e)+k') + div2Par ((e+e)+k')`; rewrite the
//!   first summand with the IH and the second with `div2Par_add_two_mul`, then
//!   `add_assoc` recombines to `e + (div2 k' + div2Par k') ≡ e + div2 (succ k')`.
//!
//! # The two ladder facts
//!
//! Both induct on `n`; the peel `testBit x (succ m) ≡ testBit (div2 x) m`
//! reduces a bit of `2^(succ n') + k` to a bit of `div2 (2^(succ n') + k)`,
//! which `div2_add_two_mul` (after `pow_two_succ` rewrites `2^(succ n')` to
//! `e + e`, `e := 2^n'`) turns into `e + div2 k`. The bound `div2 k < 2^n'`
//! comes from `k < 2^(succ n')` exactly as in rung 4a. Bit `0` / index base
//! cases compute by ground `div2Par` parity after `Nat.le_antisymm` pins
//! `k = 0`.
//!
//! # Axiom closure
//!
//! Every declaration is a `Declaration::Theorem` over `Nat.rec`, `Or.rec`,
//! `Eq.*`, `congrArg`, `Eq.subst`, `False.elim` and the constructive
//! `Nat.div2*` / `Nat.testBit` / order / `Nat.pow_two_succ` chain. No axioms,
//! so `proof_quality == Constructive` and `axiom_deps` is empty.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants for the rung-4b proofs.
struct C {
    nat: Expr,
    zero: Expr,
    succ: Expr,
    one: Expr,
    add: Expr,
    sub: Expr,
    rec0: Expr, // Nat.rec.{0} — Prop motive
    rec1: Expr, // Nat.rec.{1} — type-valued motive (for div2 helper recursion)
    bool_ty: Expr,
    btrue: Expr,
    bfalse: Expr,
    div2: Expr,
    div2par: Expr,
    testbit: Expr,
    pow: Expr,
    two: Expr,
    nat_lt: Expr,
    nat_le: Expr,
    eq1: Expr,
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    congr11: Expr,
    eq_subst: Expr,
    false_elim0: Expr,
}

impl C {
    fn new() -> Self {
        let one_lvl = Level::succ(Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let one = Expr::app(succ.clone(), zero.clone());
        let two = Expr::app(succ.clone(), one.clone());
        Self {
            nat,
            zero,
            succ,
            one,
            two,
            add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            sub: Expr::const_(Name::from_string("Nat.sub"), vec![]),
            rec0: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            rec1: Expr::const_(Name::from_string("Nat.rec"), vec![one_lvl.clone()]),
            bool_ty: Expr::const_(Name::from_string("Bool"), vec![]),
            btrue: Expr::const_(Name::from_string("Bool.true"), vec![]),
            bfalse: Expr::const_(Name::from_string("Bool.false"), vec![]),
            div2: Expr::const_(Name::from_string("Nat.div2"), vec![]),
            div2par: Expr::const_(Name::from_string("Nat.div2Par"), vec![]),
            testbit: Expr::const_(Name::from_string("Nat.testBit"), vec![]),
            pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            nat_lt: Expr::const_(Name::from_string("Nat.lt"), vec![]),
            nat_le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![one_lvl.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![one_lvl.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![one_lvl.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![one_lvl.clone()]),
            congr11: Expr::const_(
                Name::from_string("congrArg"),
                vec![one_lvl.clone(), one_lvl.clone()],
            ),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![one_lvl]),
            false_elim0: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
        }
    }

    fn succ(&self, x: Expr) -> Expr {
        Expr::app(self.succ.clone(), x)
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.add.clone(), [a, b])
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.sub.clone(), [a, b])
    }
    fn div2(&self, n: Expr) -> Expr {
        Expr::app(self.div2.clone(), n)
    }
    fn par(&self, n: Expr) -> Expr {
        Expr::app(self.div2par.clone(), n)
    }
    fn testbit(&self, n: Expr, i: Expr) -> Expr {
        Expr::apps(self.testbit.clone(), [n, i])
    }
    fn pow2(&self, n: Expr) -> Expr {
        Expr::apps(self.pow.clone(), [self.two.clone(), n])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_lt.clone(), [a, b])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn eq_nat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nat.clone(), a, b])
    }
    fn eq_bool(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.bool_ty.clone(), a, b])
    }
    fn refl_nat(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.nat.clone(), a])
    }
    fn refl_bool(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.bool_ty.clone(), a])
    }
    fn symm_nat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.nat.clone(), a, b, h])
    }
    fn trans_nat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.nat.clone(), a, b, cc, h1, h2])
    }
    fn trans_bool(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans1.clone(),
            [self.bool_ty.clone(), a, b, cc, h1, h2],
        )
    }
    /// `@congrArg.{1,1} Nat Nat a1 a2 f h : Eq (f a1) (f a2)`.
    fn congr_nat_nat(&self, a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr11.clone(),
            [self.nat.clone(), self.nat.clone(), a1, a2, f, h],
        )
    }
    /// `@congrArg.{1,1} Nat Bool a1 a2 f h : Eq (f a1) (f a2)`.
    fn congr_nat_bool(&self, a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr11.clone(),
            [self.nat.clone(), self.bool_ty.clone(), a1, a2, f, h],
        )
    }
    fn pow_two_succ(&self, n: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]),
            n,
        )
    }
    fn rejoin(&self, n: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Nat.div2_rejoin"), vec![]),
            n,
        )
    }
    fn div2_two_mul(&self, r: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Nat.div2_two_mul"), vec![]),
            r,
        )
    }
    fn div2par_two_mul(&self, r: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Nat.div2Par_two_mul"), vec![]),
            r,
        )
    }
    fn add_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Nat.add_assoc"), vec![]),
            [a, b, cc],
        )
    }
    /// `Nat.testBit_lt_pow n k h : testBit k n = false` (rung 4a).
    fn testbit_lt_pow(&self, n: Expr, k: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Nat.testBit_lt_pow"), vec![]),
            [n, k, h],
        )
    }
}

// ===========================================================================
// Helper H2: Nat.div2Par_add_two_mul : ∀ e k, div2Par ((e+e)+k) = div2Par k
// ===========================================================================
fn build_div2par_add_two_mul(c: &C) -> (Expr, Expr) {
    // type: (e k : Nat) → div2Par ((e+e)+k) = div2Par k
    let mk_lhs = |e: &Expr, k: &Expr| c.par(c.add(c.add(e.clone(), e.clone()), k.clone()));
    let mk_concl = |e: &Expr, k: &Expr| c.eq_nat(mk_lhs(e, k), c.par(k.clone()));

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (e_id, e) = b.fresh_local(c.nat.clone());
        let (k_id, k) = b.fresh_local(c.nat.clone());
        let concl = mk_concl(&e, &k);
        let pi = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), concl);
        let pi = b.mk_pi(e_id, BinderInfo::Default, c.nat.clone(), pi);
        b.finish(pi)
    };

    let value = {
        let mut vb = EnvDeclBuilder::new();
        let (e_id, e) = vb.fresh_local(c.nat.clone());
        let ee = c.add(e.clone(), e.clone());

        // motive : fun (k : Nat) => div2Par ((e+e)+k) = div2Par k
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&vb);
            let (k_id, k) = mb.fresh_local(c.nat.clone());
            let body = mk_concl(&e, &k);
            let lam = mb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body);
            mb.finish_child(lam)
        };

        // base : M 0 = (div2Par ((e+e)+0) = div2Par 0) ≡ (div2Par (e+e) = 0)
        //   div2Par_two_mul e : div2Par (e+e) = 0
        let base = c.div2par_two_mul(e.clone());

        // step : (k') → M k' → M (succ k')
        //   M (succ k') ≡ (1 - div2Par ((e+e)+k')) = (1 - div2Par k')
        //   = congrArg (fun z => 1 - z) ih
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&vb);
            let (kp_id, kp) = sb.fresh_local(c.nat.clone());
            let ih_ty = mk_concl(&e, &kp);
            let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
            // f := fun z => 1 - z
            let one_minus = {
                let mut lb = EnvDeclBuilder::child_of(&sb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                let body = c.sub(c.one.clone(), z);
                let lam = lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body);
                lb.finish_child(lam)
            };
            let out = c.congr_nat_nat(mk_lhs(&e, &kp), c.par(kp.clone()), one_minus, ih);
            let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, out);
            let lam = sb.mk_lam(kp_id, BinderInfo::Default, c.nat.clone(), lam);
            sb.finish_child(lam)
        };

        // fun k => Nat.rec.{0} motive base step k   (motive into Prop)
        let (k_id, k) = vb.fresh_local(c.nat.clone());
        let rec_app = Expr::apps(c.rec0.clone(), [motive, base, step, k.clone()]);
        let lam_k = vb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), rec_app);
        let lam_e = vb.mk_lam(e_id, BinderInfo::Default, c.nat.clone(), lam_k);
        vb.finish(lam_e)
    };
    (type_, value)
}

// ===========================================================================
// Helper H1: Nat.div2_add_two_mul : ∀ e k, div2 ((e+e)+k) = e + div2 k
// ===========================================================================
fn build_div2_add_two_mul(c: &C) -> (Expr, Expr) {
    let mk_lhs = |e: &Expr, k: &Expr| c.div2(c.add(c.add(e.clone(), e.clone()), k.clone()));
    let mk_concl = |e: &Expr, k: &Expr| c.eq_nat(mk_lhs(e, k), c.add(e.clone(), c.div2(k.clone())));

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (e_id, e) = b.fresh_local(c.nat.clone());
        let (k_id, k) = b.fresh_local(c.nat.clone());
        let concl = mk_concl(&e, &k);
        let pi = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), concl);
        let pi = b.mk_pi(e_id, BinderInfo::Default, c.nat.clone(), pi);
        b.finish(pi)
    };

    let value = {
        let mut vb = EnvDeclBuilder::new();
        let (e_id, e) = vb.fresh_local(c.nat.clone());

        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&vb);
            let (k_id, k) = mb.fresh_local(c.nat.clone());
            let body = mk_concl(&e, &k);
            let lam = mb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body);
            mb.finish_child(lam)
        };

        // base : M 0 = (div2 ((e+e)+0) = e + div2 0) ≡ (div2 (e+e) = e)
        //   div2_two_mul e : div2 (e+e) = e
        let base = c.div2_two_mul(e.clone());

        // step : (k') → M k' → M (succ k')
        // Goal M (succ k') ≡ (div2 ((e+e)+k') + div2Par ((e+e)+k')) = e + (div2 k' + div2Par k')
        //   ih    : div2 ((e+e)+k') = e + div2 k'
        //   hpar  : div2Par ((e+e)+k') = div2Par k'     [div2Par_add_two_mul e k']
        //   line1 : div2 ((e+e)+k') + div2Par ((e+e)+k')
        //         = (e + div2 k') + div2Par ((e+e)+k')    [congrArg (·+par) ih]
        //         = (e + div2 k') + div2Par k'            [congrArg ((e+div2k')+·) hpar]
        //   assoc : (e + div2 k') + div2Par k' = e + (div2 k' + div2Par k')  [add_assoc]
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&vb);
            let (kp_id, kp) = sb.fresh_local(c.nat.clone());
            let ih_ty = mk_concl(&e, &kp);
            let (ih_id, ih) = sb.fresh_local(ih_ty.clone());

            let lhs0 = mk_lhs(&e, &kp); // div2 ((e+e)+k')
            let e_d2kp = c.add(e.clone(), c.div2(kp.clone())); // e + div2 k'
            let par_lhs = c.par(c.add(c.add(e.clone(), e.clone()), kp.clone())); // div2Par ((e+e)+k')
            let par_kp = c.par(kp.clone()); // div2Par k'

            // hpar : div2Par ((e+e)+k') = div2Par k'
            let hpar = Expr::apps(
                Expr::const_(Name::from_string("Nat.div2Par_add_two_mul"), vec![]),
                [e.clone(), kp.clone()],
            );

            // A := div2 ((e+e)+k') + div2Par ((e+e)+k')   (≡ div2 (succ ((e+e)+k')) = LHS of goal)
            // step1 : A = (e + div2 k') + div2Par ((e+e)+k')   via congrArg (· + par_lhs) ih
            let add_par_lhs_fn = {
                let mut lb = EnvDeclBuilder::child_of(&sb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                let body = c.add(z, par_lhs.clone());
                let lam = lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body);
                lb.finish_child(lam)
            };
            let a_expr = c.add(lhs0.clone(), par_lhs.clone());
            let b1_expr = c.add(e_d2kp.clone(), par_lhs.clone());
            let step1 = c.congr_nat_nat(lhs0.clone(), e_d2kp.clone(), add_par_lhs_fn, ih);

            // step2 : (e + div2 k') + div2Par ((e+e)+k') = (e + div2 k') + div2Par k'
            //   via congrArg ((e+div2k') + ·) hpar
            let pre_add_fn = {
                let mut lb = EnvDeclBuilder::child_of(&sb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                let body = c.add(e_d2kp.clone(), z);
                let lam = lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body);
                lb.finish_child(lam)
            };
            let b2_expr = c.add(e_d2kp.clone(), par_kp.clone());
            let step2 = c.congr_nat_nat(par_lhs.clone(), par_kp.clone(), pre_add_fn, hpar);

            // assoc : (e + div2 k') + div2Par k' = e + (div2 k' + div2Par k')
            let d2kp = c.div2(kp.clone());
            let assoc = c.add_assoc(e.clone(), d2kp.clone(), par_kp.clone());
            let c3_expr = c.add(e.clone(), c.add(d2kp.clone(), par_kp.clone()));

            // chain: A = b1 = b2 = c3
            let t12 = c.trans_nat(
                a_expr.clone(),
                b1_expr.clone(),
                b2_expr.clone(),
                step1,
                step2,
            );
            let out = c.trans_nat(a_expr, b2_expr, c3_expr, t12, assoc);

            let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, out);
            let lam = sb.mk_lam(kp_id, BinderInfo::Default, c.nat.clone(), lam);
            sb.finish_child(lam)
        };

        let (k_id, k) = vb.fresh_local(c.nat.clone());
        let rec_app = Expr::apps(c.rec0.clone(), [motive, base, step, k.clone()]);
        let lam_k = vb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), rec_app);
        let lam_e = vb.mk_lam(e_id, BinderInfo::Default, c.nat.clone(), lam_k);
        vb.finish(lam_e)
    };
    (type_, value)
}

// ===========================================================================
// Bound helper: Nat.div2_lt_of_lt_two_pow_succ
//   ∀ n k, lt k (pow 2 (succ n)) → lt (div2 k) (pow 2 n)
// ===========================================================================
//
// Identical to the rung-4a step bound, factored for reuse by both 4b facts.
// le_or_lt p r where p := pow 2 n, r := div2 k. The `le p r` branch is
// vacuous: add_le_add gives le (p+p) (r+r); div2_rejoin + le_add_right give
// le (r+r) k; le_trans → le (p+p) k; transport along (pow_two_succ n).symm →
// le (pow 2 (succ n)) k; lt_of_le_of_lt with h → lt X X; lt_irrefl.
fn build_div2_lt_of_lt_two_pow_succ(c: &C) -> (Expr, Expr) {
    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (k_id, k) = b.fresh_local(c.nat.clone());
        let h_ty = c.lt(k.clone(), c.pow2(c.succ(n.clone())));
        let (h_id, _h) = b.fresh_local(h_ty.clone());
        let concl = c.lt(c.div2(k.clone()), c.pow2(n.clone()));
        let imp = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
        let pi = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), imp);
        let pi = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), pi);
        b.finish(pi)
    };

    let value = {
        let mut vb = EnvDeclBuilder::new();
        let (n_id, n) = vb.fresh_local(c.nat.clone());
        let (k_id, k) = vb.fresh_local(c.nat.clone());
        let h_ty = c.lt(k.clone(), c.pow2(c.succ(n.clone())));
        let (h_id, h) = vb.fresh_local(h_ty.clone());

        let r = c.div2(k.clone());
        let p = c.pow2(n.clone());
        let sn = c.succ(n.clone());

        let le_pr_ty = c.le(p.clone(), r.clone());
        let lt_rp_ty = c.lt(r.clone(), p.clone());
        let or_ty = Expr::apps(
            Expr::const_(Name::from_string("Or"), vec![]),
            [le_pr_ty.clone(), lt_rp_ty.clone()],
        );

        let disj = Expr::apps(
            Expr::const_(Name::from_string("Nat.le_or_lt"), vec![]),
            [p.clone(), r.clone()],
        );

        let or_motive = {
            let mut ob = EnvDeclBuilder::child_of(&vb);
            let (d_id, _d) = ob.fresh_local(or_ty.clone());
            let lam = ob.mk_lam(d_id, BinderInfo::Default, or_ty.clone(), lt_rp_ty.clone());
            ob.finish_child(lam)
        };

        // inl : le p r → lt r p (vacuous via False.elim)
        let inl = {
            let mut ib = EnvDeclBuilder::child_of(&vb);
            let (hpr_id, hpr) = ib.fresh_local(le_pr_ty.clone());

            let rr = c.add(r.clone(), r.clone());
            let pp = c.add(p.clone(), p.clone());
            let park = c.par(k.clone());
            let joined = c.add(rr.clone(), park.clone());

            // add_le_add p r p r hpr hpr : le (p+p) (r+r)
            let h_pp_rr = Expr::apps(
                Expr::const_(Name::from_string("Nat.add_le_add"), vec![]),
                [
                    p.clone(),
                    r.clone(),
                    p.clone(),
                    r.clone(),
                    hpr.clone(),
                    hpr.clone(),
                ],
            );
            // le_add_right (r+r) (park) : le (r+r) ((r+r)+park)
            let h_rr_join = Expr::apps(
                Expr::const_(Name::from_string("Nat.le_add_right"), vec![]),
                [rr.clone(), park.clone()],
            );
            // rejoin k : k = (r+r)+park ; symm : ((r+r)+park) = k
            let rejoin_symm = c.symm_nat(k.clone(), joined.clone(), c.rejoin(k.clone()));
            // Eq.subst motive (fun z => le (r+r) z) joined k symm h_rr_join : le (r+r) k
            let m_le_rr = {
                let mut lb = EnvDeclBuilder::child_of(&ib);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                let body = c.le(rr.clone(), z);
                let lam = lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body);
                lb.finish_child(lam)
            };
            let h_rr_k = Expr::apps(
                c.eq_subst.clone(),
                [
                    c.nat.clone(),
                    m_le_rr,
                    joined.clone(),
                    k.clone(),
                    rejoin_symm,
                    h_rr_join,
                ],
            );
            // le_trans (p+p) (r+r) k : le (p+p) k
            let h_pp_k = Expr::apps(
                Expr::const_(Name::from_string("Nat.le_trans"), vec![]),
                [pp.clone(), rr.clone(), k.clone(), h_pp_rr, h_rr_k],
            );
            // transport along (pow_two_succ n).symm : (p+p) = pow 2 (succ n)
            let m_le_z_k = {
                let mut lb = EnvDeclBuilder::child_of(&ib);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                let body = c.le(z, k.clone());
                let lam = lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body);
                lb.finish_child(lam)
            };
            let pts_symm = c.symm_nat(c.pow2(sn.clone()), pp.clone(), c.pow_two_succ(n.clone()));
            let h_pow_k = Expr::apps(
                c.eq_subst.clone(),
                [
                    c.nat.clone(),
                    m_le_z_k,
                    pp.clone(),
                    c.pow2(sn.clone()),
                    pts_symm,
                    h_pp_k,
                ],
            );
            // lt_of_le_of_lt (pow 2 (succ n)) k (pow 2 (succ n)) h_pow_k h : lt X X
            let h_lt_self = Expr::apps(
                Expr::const_(Name::from_string("Nat.lt_of_le_of_lt"), vec![]),
                [
                    c.pow2(sn.clone()),
                    k.clone(),
                    c.pow2(sn.clone()),
                    h_pow_k,
                    h.clone(),
                ],
            );
            let false_pf = Expr::apps(
                Expr::const_(Name::from_string("Nat.lt_irrefl"), vec![]),
                [c.pow2(sn.clone()), h_lt_self],
            );
            let out = Expr::apps(c.false_elim0.clone(), [lt_rp_ty.clone(), false_pf]);
            let lam = ib.mk_lam(hpr_id, BinderInfo::Default, le_pr_ty.clone(), out);
            ib.finish_child(lam)
        };

        // inr : lt r p → lt r p (identity)
        let inr = {
            let mut rb = EnvDeclBuilder::child_of(&vb);
            let (hlt_id, hlt) = rb.fresh_local(lt_rp_ty.clone());
            let lam = rb.mk_lam(hlt_id, BinderInfo::Default, lt_rp_ty.clone(), hlt);
            rb.finish_child(lam)
        };

        let or_rec = Expr::const_(Name::from_string("Or.rec"), vec![]);
        let bound = Expr::apps(or_rec, [le_pr_ty, lt_rp_ty, or_motive, inl, inr, disj]);

        let lam = vb.mk_lam(h_id, BinderInfo::Default, h_ty, bound);
        let lam = vb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam);
        let lam = vb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
        vb.finish(lam)
    };
    (type_, value)
}

// ===========================================================================
// Fact 4b-i: Nat.testBit_add_two_pow_self
//   ∀ n k, lt k (pow 2 n) → testBit ((pow 2 n) + k) n = true
// ===========================================================================
fn build_testbit_add_two_pow_self(c: &C) -> (Expr, Expr) {
    // P n := (k) → lt k (pow 2 n) → testBit ((pow 2 n)+k) n = true
    let p_of = |n: &Expr, parent: &EnvDeclBuilder| -> Expr {
        let mut pb = EnvDeclBuilder::child_of(parent);
        let (k_id, k) = pb.fresh_local(c.nat.clone());
        let h_ty = c.lt(k.clone(), c.pow2(n.clone()));
        let (h_id, _h) = pb.fresh_local(h_ty.clone());
        let val = c.add(c.pow2(n.clone()), k.clone());
        let concl = c.eq_bool(c.testbit(val, n.clone()), c.btrue.clone());
        let imp = pb.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
        let pi = pb.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), imp);
        pb.finish_child(pi)
    };

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let concl = p_of(&n, &b);
        let pi = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
        b.finish(pi)
    };

    let value = {
        let mut vb = EnvDeclBuilder::new();

        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&vb);
            let (n_id, n) = mb.fresh_local(c.nat.clone());
            let body = p_of(&n, &mb);
            let lam = mb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            mb.finish_child(lam)
        };

        // base : P 0 — fun k h => transport (refl true : testBit ((pow 2 0)+0) 0 = true)
        //   along (k=0).symm.  k=0 from le_antisymm k 0 (le_of_succ_le_succ k 0 h)(zero_le k).
        let base = {
            let mut bb = EnvDeclBuilder::child_of(&vb);
            let (k_id, k) = bb.fresh_local(c.nat.clone());
            let h_ty = c.lt(k.clone(), c.pow2(c.zero.clone()));
            let (h_id, h) = bb.fresh_local(h_ty.clone());
            // le k 0
            let le_k0 = Expr::apps(
                Expr::const_(Name::from_string("Nat.le_of_succ_le_succ"), vec![]),
                [k.clone(), c.zero.clone(), h.clone()],
            );
            let zero_le_k = Expr::app(
                Expr::const_(Name::from_string("Nat.zero_le"), vec![]),
                k.clone(),
            );
            // le_antisymm k 0 (le k 0) (le 0 k) : k = 0
            let hk0 = Expr::apps(
                Expr::const_(Name::from_string("Nat.le_antisymm"), vec![]),
                [k.clone(), c.zero.clone(), le_k0, zero_le_k],
            );
            // motive z := testBit ((pow 2 0)+z) 0 = true
            let m = {
                let mut lb = EnvDeclBuilder::child_of(&bb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                let val = c.add(c.pow2(c.zero.clone()), z);
                let body = c.eq_bool(c.testbit(val, c.zero.clone()), c.btrue.clone());
                let lam = lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body);
                lb.finish_child(lam)
            };
            // base proof at z=0 : testBit ((pow 2 0)+0) 0 = true  by rfl (ground reduces to true)
            let m0 = c.refl_bool(c.btrue.clone());
            // Eq.subst Nat m 0 k (hk0.symm : 0 = k) m0 : m k
            let hk0_symm = c.symm_nat(k.clone(), c.zero.clone(), hk0);
            let out = Expr::apps(
                c.eq_subst.clone(),
                [c.nat.clone(), m, c.zero.clone(), k.clone(), hk0_symm, m0],
            );
            let lam = bb.mk_lam(h_id, BinderInfo::Default, h_ty, out);
            let lam = bb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam);
            bb.finish_child(lam)
        };

        // step : (n') → P n' → P (succ n')
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&vb);
            let (np_id, np) = sb.fresh_local(c.nat.clone());
            let ih_ty = p_of(&np, &sb);
            let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
            let sn = c.succ(np.clone());
            let e = c.pow2(np.clone()); // e := pow 2 n'

            let (k_id, k) = sb.fresh_local(c.nat.clone());
            let h_ty = c.lt(k.clone(), c.pow2(sn.clone()));
            let (h_id, h) = sb.fresh_local(h_ty.clone());

            // bound : lt (div2 k) (pow 2 n')   [div2_lt_of_lt_two_pow_succ n' k h]
            let bound = Expr::apps(
                Expr::const_(Name::from_string("Nat.div2_lt_of_lt_two_pow_succ"), vec![]),
                [np.clone(), k.clone(), h.clone()],
            );

            // Goal (≡ after peel) : testBit (div2 ((pow 2 (succ n'))+k)) n' = true.
            // hdiv : div2 ((pow 2 (succ n'))+k) = e + div2 k.
            //   step A: congrArg (· + k) (pow_two_succ n') : (pow 2 (succ n'))+k = (e+e)+k
            //   step B: div2_add_two_mul e k : div2 ((e+e)+k) = e + div2 k
            //   hdiv = trans (congrArg div2 stepA) stepB
            let ee = c.add(e.clone(), e.clone());
            let lhs_val = c.add(c.pow2(sn.clone()), k.clone()); // (pow 2 (succ n'))+k
            let ee_val = c.add(ee.clone(), k.clone()); // (e+e)+k
                                                       // stepA : lhs_val = ee_val   via congrArg (· + k) (pow_two_succ n')
            let add_k_fn = {
                let mut lb = EnvDeclBuilder::child_of(&sb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                let body = c.add(z, k.clone());
                let lam = lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body);
                lb.finish_child(lam)
            };
            let step_a = c.congr_nat_nat(
                c.pow2(sn.clone()),
                ee.clone(),
                add_k_fn,
                c.pow_two_succ(np.clone()),
            );
            // congrArg div2 stepA : div2 lhs_val = div2 ee_val
            let dcongr = c.congr_nat_nat(lhs_val.clone(), ee_val.clone(), c.div2.clone(), step_a);
            // step_b : div2 ee_val = e + div2 k
            let step_b = Expr::apps(
                Expr::const_(Name::from_string("Nat.div2_add_two_mul"), vec![]),
                [e.clone(), k.clone()],
            );
            let e_d2k = c.add(e.clone(), c.div2(k.clone())); // e + div2 k
            let hdiv = c.trans_nat(
                c.div2(lhs_val.clone()),
                c.div2(ee_val.clone()),
                e_d2k.clone(),
                dcongr,
                step_b,
            );

            // congrArg (testBit · n') hdiv : testBit (div2 lhs_val) n' = testBit (e+div2 k) n'
            let testbit_n_fn = {
                let mut lb = EnvDeclBuilder::child_of(&sb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                let body = c.testbit(z, np.clone());
                let lam = lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body);
                lb.finish_child(lam)
            };
            let tcongr =
                c.congr_nat_bool(c.div2(lhs_val.clone()), e_d2k.clone(), testbit_n_fn, hdiv);
            // ih (div2 k) bound : testBit ((pow 2 n')+div2 k) n' = true ≡ testBit (e+div2 k) n' = true
            let ih_out = Expr::apps(ih.clone(), [c.div2(k.clone()), bound]);
            // chain : testBit (div2 lhs_val) n' = testBit (e+div2 k) n' = true
            let tb_div = c.testbit(c.div2(lhs_val.clone()), np.clone());
            let tb_e = c.testbit(e_d2k.clone(), np.clone());
            let out = c.trans_bool(tb_div, tb_e, c.btrue.clone(), tcongr, ih_out);

            let lam = sb.mk_lam(h_id, BinderInfo::Default, h_ty, out);
            let lam = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam);
            let lam = sb.mk_lam(np_id, BinderInfo::Default, c.nat.clone(), lam);
            sb.finish_child(lam)
        };

        let (n_id, n) = vb.fresh_local(c.nat.clone());
        let rec_app = Expr::apps(c.rec0.clone(), [motive, base, step, n.clone()]);
        let lam = vb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec_app);
        vb.finish(lam)
    };
    (type_, value)
}

// ===========================================================================
// Fact 4b-ii: Nat.testBit_add_two_pow_lo
//   ∀ n k i, lt k (pow 2 n) → lt i n → testBit ((pow 2 n)+k) i = testBit k i
// ===========================================================================
fn build_testbit_add_two_pow_lo(c: &C) -> (Expr, Expr) {
    // P n := (k) → lt k (pow 2 n) → (i) → lt i n → testBit ((pow 2 n)+k) i = testBit k i
    // (k and its bound bind first so the per-n div2/parity facts about
    // `(pow 2 n)+k` can be computed once, outside the inner induction on i.)
    let p_of = |n: &Expr, parent: &EnvDeclBuilder| -> Expr {
        let mut pb = EnvDeclBuilder::child_of(parent);
        let (k_id, k) = pb.fresh_local(c.nat.clone());
        let hk_ty = c.lt(k.clone(), c.pow2(n.clone()));
        let (hk_id, _hk) = pb.fresh_local(hk_ty.clone());
        let (i_id, i) = pb.fresh_local(c.nat.clone());
        let hi_ty = c.lt(i.clone(), n.clone());
        let (hi_id, _hi) = pb.fresh_local(hi_ty.clone());
        let val = c.add(c.pow2(n.clone()), k.clone());
        let concl = c.eq_bool(c.testbit(val, i.clone()), c.testbit(k.clone(), i.clone()));
        let imp_hi = pb.mk_pi(hi_id, BinderInfo::Default, hi_ty, concl);
        let pi_i = pb.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), imp_hi);
        let imp_hk = pb.mk_pi(hk_id, BinderInfo::Default, hk_ty, pi_i);
        let pi_k = pb.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), imp_hk);
        pb.finish_child(pi_k)
    };

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let concl = p_of(&n, &b);
        let pi = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
        b.finish(pi)
    };

    let value = {
        let mut vb = EnvDeclBuilder::new();

        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&vb);
            let (n_id, n) = mb.fresh_local(c.nat.clone());
            let body = p_of(&n, &mb);
            let lam = mb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            mb.finish_child(lam)
        };

        // base : P 0 — lt i 0 is absurd.
        //   fun k hk i hi => False.elim concl (not_succ_le_zero i hi)
        let base = {
            let mut bb = EnvDeclBuilder::child_of(&vb);
            let (k_id, k) = bb.fresh_local(c.nat.clone());
            let hk_ty = c.lt(k.clone(), c.pow2(c.zero.clone()));
            let (hk_id, _hk) = bb.fresh_local(hk_ty.clone());
            let (i_id, i) = bb.fresh_local(c.nat.clone());
            let hi_ty = c.lt(i.clone(), c.zero.clone());
            let (hi_id, hi) = bb.fresh_local(hi_ty.clone());
            let nslz = Expr::apps(
                Expr::const_(Name::from_string("Nat.not_succ_le_zero"), vec![]),
                [i.clone(), hi.clone()],
            );
            let val = c.add(c.pow2(c.zero.clone()), k.clone());
            let concl = c.eq_bool(c.testbit(val, i.clone()), c.testbit(k.clone(), i.clone()));
            let out = Expr::apps(c.false_elim0.clone(), [concl, nslz]);
            let lam = bb.mk_lam(hi_id, BinderInfo::Default, hi_ty, out);
            let lam = bb.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = bb.mk_lam(hk_id, BinderInfo::Default, hk_ty, lam);
            let lam = bb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam);
            bb.finish_child(lam)
        };

        // step : (n') → P n' → P (succ n')
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&vb);
            let (np_id, np) = sb.fresh_local(c.nat.clone());
            let ih_ty = p_of(&np, &sb);
            let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
            let sn = c.succ(np.clone());
            let e = c.pow2(np.clone());

            let (k_id, k) = sb.fresh_local(c.nat.clone());
            let hk_ty = c.lt(k.clone(), c.pow2(sn.clone()));
            let (hk_id, hk) = sb.fresh_local(hk_ty.clone());

            let val = c.add(c.pow2(sn.clone()), k.clone()); // (pow 2 (succ n'))+k
            let ee = c.add(e.clone(), e.clone());

            // bound : lt (div2 k) (pow 2 n')
            let bound = Expr::apps(
                Expr::const_(Name::from_string("Nat.div2_lt_of_lt_two_pow_succ"), vec![]),
                [np.clone(), k.clone(), hk.clone()],
            );

            // hdiv : div2 ((pow 2 (succ n'))+k) = e + div2 k   (shared by i=succ branch)
            //   trans (congrArg div2 (congrArg (·+k) (pow_two_succ n'))) (div2_add_two_mul e k)
            let ee_val = c.add(ee.clone(), k.clone());
            let add_k_fn = {
                let mut lb = EnvDeclBuilder::child_of(&sb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                let body = c.add(z, k.clone());
                let lam = lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body);
                lb.finish_child(lam)
            };
            let step_a = c.congr_nat_nat(
                c.pow2(sn.clone()),
                ee.clone(),
                add_k_fn,
                c.pow_two_succ(np.clone()),
            );
            let dcongr = c.congr_nat_nat(val.clone(), ee_val.clone(), c.div2.clone(), step_a);
            let step_b = Expr::apps(
                Expr::const_(Name::from_string("Nat.div2_add_two_mul"), vec![]),
                [e.clone(), k.clone()],
            );
            let e_d2k = c.add(e.clone(), c.div2(k.clone()));
            let hdiv = c.trans_nat(
                c.div2(val.clone()),
                c.div2(ee_val.clone()),
                e_d2k.clone(),
                dcongr,
                step_b,
            );

            // hpar : div2Par ((pow 2 (succ n'))+k) = div2Par k   (for i=0 branch)
            //   trans (congrArg (fun z => div2Par (z+k)) (pow_two_succ n')) (div2Par_add_two_mul e k)
            let par_z_fn = {
                let mut lb = EnvDeclBuilder::child_of(&sb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                let body = c.par(c.add(z, k.clone()));
                let lam = lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body);
                lb.finish_child(lam)
            };
            let par_step_a = c.congr_nat_nat(
                c.pow2(sn.clone()),
                ee.clone(),
                par_z_fn,
                c.pow_two_succ(np.clone()),
            );
            let par_step_b = Expr::apps(
                Expr::const_(Name::from_string("Nat.div2Par_add_two_mul"), vec![]),
                [e.clone(), k.clone()],
            );
            let hpar = c.trans_nat(
                c.par(val.clone()),
                c.par(ee_val.clone()),
                c.par(k.clone()),
                par_step_a,
                par_step_b,
            );

            // Inner Nat.rec on i. Ni i := lt i (succ n') → testBit val i = testBit k i
            let ni_of = |i: &Expr, parent: &EnvDeclBuilder| -> Expr {
                let mut qb = EnvDeclBuilder::child_of(parent);
                let hi_ty = c.lt(i.clone(), sn.clone());
                let (hi_id, _hi) = qb.fresh_local(hi_ty.clone());
                let concl = c.eq_bool(
                    c.testbit(val.clone(), i.clone()),
                    c.testbit(k.clone(), i.clone()),
                );
                let imp = qb.mk_pi(hi_id, BinderInfo::Default, hi_ty, concl);
                qb.finish_child(imp)
            };
            let ni_motive = {
                let mut mb = EnvDeclBuilder::child_of(&sb);
                let (i_id, i) = mb.fresh_local(c.nat.clone());
                let body = ni_of(&i, &mb);
                let lam = mb.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), body);
                mb.finish_child(lam)
            };

            // i=0 : Ni 0 = lt 0 (succ n') → testBit val 0 = testBit k 0
            //   fun _hi => congrArg toBoolPar hpar
            //   (testBit x 0 ≡ toBoolPar (div2Par x), so the goal is exactly that.)
            let i0_base = {
                let mut ib = EnvDeclBuilder::child_of(&sb);
                let hi_ty = c.lt(c.zero.clone(), sn.clone());
                let (hi_id, _hi) = ib.fresh_local(hi_ty.clone());
                let tobool = Expr::const_(Name::from_string("Nat.toBoolPar"), vec![]);
                // congrArg.{1,1} Nat Bool (div2Par val) (div2Par k) toBoolPar hpar
                let out =
                    c.congr_nat_bool(c.par(val.clone()), c.par(k.clone()), tobool, hpar.clone());
                let lam = ib.mk_lam(hi_id, BinderInfo::Default, hi_ty, out);
                ib.finish_child(lam)
            };

            // i=succ i' : (i') → Ni i' → Ni (succ i')
            //   fun i' _ihni (hi : lt (succ i')(succ n')) =>
            //     testBit val (succ i') ≡ testBit (div2 val) i'
            //       = testBit (e+div2 k) i'     [congrArg (testBit · i') hdiv]
            //       = testBit (div2 k) i'       [ih (div2 k) i' bound hi']
            //     ≡ testBit k (succ i')
            let i_step = {
                let mut ib = EnvDeclBuilder::child_of(&sb);
                let (ip_id, ip) = ib.fresh_local(c.nat.clone());
                let ni_ip = ni_of(&ip, &ib);
                let (ihni_id, _ihni) = ib.fresh_local(ni_ip.clone());
                let sip = c.succ(ip.clone());
                let hi_ty = c.lt(sip.clone(), sn.clone());
                let (hi_id, hi) = ib.fresh_local(hi_ty.clone());

                // hi' : lt i' n'   from le_of_succ_le_succ i' n' hi  (lt (succ i')(succ n') ≡ le (succ(succ i'))(succ n'))
                let hip = Expr::apps(
                    Expr::const_(Name::from_string("Nat.le_of_succ_le_succ"), vec![]),
                    [sip.clone(), np.clone(), hi.clone()],
                );
                // congrArg (testBit · i') hdiv : testBit (div2 val) i' = testBit (e+div2 k) i'
                let testbit_ip_fn = {
                    let mut lb = EnvDeclBuilder::child_of(&ib);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    let body = c.testbit(z, ip.clone());
                    let lam = lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body);
                    lb.finish_child(lam)
                };
                let tcongr = c.congr_nat_bool(
                    c.div2(val.clone()),
                    e_d2k.clone(),
                    testbit_ip_fn,
                    hdiv.clone(),
                );
                // ih (div2 k) bound i' hip : testBit ((pow 2 n')+div2 k) i' = testBit (div2 k) i'
                //   ≡ testBit (e+div2 k) i' = testBit (div2 k) i'
                //   (P n' order is k → hk → i → hi.)
                let ih_out = Expr::apps(
                    ih.clone(),
                    [c.div2(k.clone()), bound.clone(), ip.clone(), hip],
                );
                // chain: testBit (div2 val) i' = testBit (e+div2 k) i' = testBit (div2 k) i'
                let tb_div = c.testbit(c.div2(val.clone()), ip.clone());
                let tb_e = c.testbit(e_d2k.clone(), ip.clone());
                let tb_k = c.testbit(c.div2(k.clone()), ip.clone());
                let out = c.trans_bool(tb_div, tb_e, tb_k, tcongr, ih_out);
                let lam = ib.mk_lam(hi_id, BinderInfo::Default, hi_ty, out);
                let lam = ib.mk_lam(ihni_id, BinderInfo::Default, ni_ip, lam);
                let lam = ib.mk_lam(ip_id, BinderInfo::Default, c.nat.clone(), lam);
                ib.finish_child(lam)
            };

            // P (succ n') = (k i) → lt k (..) → lt i (succ n') → ...
            //   build fun i => Nat.rec Ni i0_base i_step i, then wrap binders.
            let (i_id, i) = sb.fresh_local(c.nat.clone());
            let rec_i = Expr::apps(c.rec0.clone(), [ni_motive, i0_base, i_step, i.clone()]);
            // rec_i : Ni i = lt i (succ n') → testBit val i = testBit k i
            let lam_i = sb.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), rec_i);
            // wrap hk then k (note: hk used inside bound/hdiv/hpar — those captured hk,k,np)
            let lam_hk = sb.mk_lam(hk_id, BinderInfo::Default, hk_ty, lam_i);
            let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_hk);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam_k);
            let lam_np = sb.mk_lam(np_id, BinderInfo::Default, c.nat.clone(), lam_ih);
            sb.finish_child(lam_np)
        };

        let (n_id, n) = vb.fresh_local(c.nat.clone());
        let rec_app = Expr::apps(c.rec0.clone(), [motive, base, step, n.clone()]);
        let lam = vb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec_app);
        vb.finish(lam)
    };
    (type_, value)
}

impl Environment {
    /// Register the rung-4b div2 helpers + the two ladder facts.
    ///
    /// Registers `Nat.div2Par_add_two_mul`, `Nat.div2_add_two_mul`,
    /// `Nat.testBit_add_two_pow_self`, and `Nat.testBit_add_two_pow_lo` — all
    /// kernel-checked `Declaration::Theorem`s with empty axiom closures.
    pub(crate) fn register_nat_testbit_add_two_pow_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget):
        // Nat bitwise-cluster proof content — states/proves properties of the
        // import-suppressed div2/testBit/bitwise/Bool.xor web (see
        // register_nat_testbit_def). Suppressed with it.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        // Dependencies (all idempotent): testBit / div2 / div2_two_mul /
        // div2Par_two_mul foundation, rung 3 (pow_two_succ) and rung 4a
        // (testBit_lt_pow), and the order/arith chain.
        self.register_nat_testbit_lt_pow_proof()?; // 4a + its whole dep chain
        self.register_nat_add_assoc_proof()?; // Nat.add_assoc
        self.register_nat_le_antisymm_proof()?; // Nat.le_antisymm
        self.register_nat_ble_le_lemmas()?; // Nat.zero_le

        let c = C::new();

        if self
            .get_const(&Name::from_string("Nat.div2Par_add_two_mul"))
            .is_none()
        {
            let (type_, value) = build_div2par_add_two_mul(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.div2Par_add_two_mul"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        if self
            .get_const(&Name::from_string("Nat.div2_add_two_mul"))
            .is_none()
        {
            let (type_, value) = build_div2_add_two_mul(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.div2_add_two_mul"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        if self
            .get_const(&Name::from_string("Nat.div2_lt_of_lt_two_pow_succ"))
            .is_none()
        {
            let (type_, value) = build_div2_lt_of_lt_two_pow_succ(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.div2_lt_of_lt_two_pow_succ"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        if self
            .get_const(&Name::from_string("Nat.testBit_add_two_pow_self"))
            .is_none()
        {
            let (type_, value) = build_testbit_add_two_pow_self(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.testBit_add_two_pow_self"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        if self
            .get_const(&Name::from_string("Nat.testBit_add_two_pow_lo"))
            .is_none()
        {
            let (type_, value) = build_testbit_add_two_pow_lo(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.testBit_add_two_pow_lo"),
                level_params: vec![],
                type_,
                value,
            })?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_nat_testbit_add_two_pow_proof()
            .expect("register 4b");
        env
    }

    fn check(env: &Environment, name: &str) {
        let tc = TypeChecker::with_mode(env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string(name), vec![]))
            .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
        let deps = env
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} registered; axiom_deps Some"));
        let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(names.is_empty(), "{name} must be axiom-free, got {names:?}");
    }

    #[test]
    fn test_div2_helpers_axiom_free() {
        let env = env();
        check(&env, "Nat.div2Par_add_two_mul");
        check(&env, "Nat.div2_add_two_mul");
    }

    #[test]
    fn test_testbit_add_two_pow_self_axiom_free() {
        let env = env();
        check(&env, "Nat.testBit_add_two_pow_self");
    }

    #[test]
    fn test_testbit_add_two_pow_lo_axiom_free() {
        let env = env();
        check(&env, "Nat.testBit_add_two_pow_lo");
    }

    /// Ground sanity for `testBit_add_two_pow_self`: bit 2 of (2^2 + 1) = 5 is
    /// true (5 = 0b101). `@Eq.refl Bool true` checks against
    /// `testBit (4+1) 2 = true` by reduction.
    #[test]
    fn test_self_ground_rfl() {
        let env = env();
        let c = C::new();
        let two = c.succ(c.succ(c.zero.clone()));
        let one = c.one.clone();
        let val = c.add(c.pow2(two.clone()), one); // 2^2 + 1 = 5
        let stmt = c.eq_bool(c.testbit(val, two), c.btrue.clone());
        let refl = c.refl_bool(c.btrue.clone());
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&refl, &stmt)
            .expect("ground testBit (2^2+1) 2 = true must hold by rfl");
    }

    /// Ground sanity for `testBit_add_two_pow_lo`: bit 0 of (2^2 + 1) = 5
    /// equals bit 0 of 1 (both true; 5 = 0b101, 1 = 0b001).
    #[test]
    fn test_lo_ground_rfl() {
        let env = env();
        let c = C::new();
        let two = c.succ(c.succ(c.zero.clone()));
        let one = c.one.clone();
        let val = c.add(c.pow2(two.clone()), one.clone()); // 5
        let stmt = c.eq_bool(
            c.testbit(val, c.zero.clone()),
            c.testbit(one, c.zero.clone()),
        );
        let refl = c.refl_bool(c.btrue.clone());
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&refl, &stmt)
            .expect("ground testBit (2^2+1) 0 = testBit 1 0 must hold by rfl");
    }
}
