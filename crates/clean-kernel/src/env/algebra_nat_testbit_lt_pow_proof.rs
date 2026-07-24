//! Constructive proof of `Nat.testBit_lt_pow` — rung 4a of the Parseval ladder.
//!
//! ```text
//! Nat.testBit_lt_pow : ∀ (n k : Nat),
//!   Nat.lt k (Nat.pow 2 n) → @Eq Bool (Nat.testBit k n) Bool.false
//! ```
//!
//! "Any bit `n` of a value `k < 2^n` is `false`." This is the per-coordinate
//! high-bit-vanishing fact underpinning the Hadamard / Walsh coordinate
//! arguments (the bound `k < 2^n` means `k` has no bit at position `n` or
//! above; rung 4a is the position-`n` slice).
//!
//! # Proof
//!
//! Plain `Nat.rec` induction on the bit index `n` with predicate
//! ```text
//! P n := ∀ k, Nat.lt k (Nat.pow 2 n) → testBit k n = false.
//! ```
//!
//! - **Base `n = 0`.** `Nat.pow 2 0 ≡ 1 ≡ Nat.succ Nat.zero`, so
//!   `lt k 1 ≡ le (succ k) (succ 0)`. `le_of_succ_le_succ k 0 h : le k 0`, and
//!   the already-proven `Nat.testBit_eq_false_of_ge k 0 (le k 0)` discharges
//!   `testBit k 0 = false` (bit `0` of any `k ≤ 0`, i.e. `k = 0`, is false).
//!
//! - **Step `n = succ n'`.** Given `k`, `h : lt k (pow 2 (succ n'))`. By the
//!   inner `iterDiv2` recursion,
//!   `testBit k (succ n') ≡ testBit (div2 k) n'`, so it suffices to feed the
//!   IH `∀ k, lt k (pow 2 n') → testBit k n' = false` at `div2 k`. Producing
//!   `lt (div2 k) (pow 2 n')`: case-split `le_or_lt (pow 2 n') (div2 k)`.
//!   - `inr`: exactly `lt (div2 k) (pow 2 n')`. Done.
//!   - `inl (le (pow 2 n') (div2 k))`: derive a contradiction. With
//!     `r := div2 k`, `p := pow 2 n'`,
//!     `add_le_add p r p r hpr hpr : le (p+p) (r+r)`; `div2_rejoin k`
//!     and `le_add_right (r+r) (div2Par k)` give `le (r+r) k`; `le_trans`
//!     yields `le (p+p) k`, transported by `(pow_two_succ n').symm` (via
//!     `Eq.subst`) to `le (pow 2 (succ n')) k`. Combined with
//!     `h : lt k (pow 2 (succ n'))` through `lt_of_le_of_lt` this gives
//!     `lt (pow 2 (succ n')) (pow 2 (succ n'))`, refuted by `lt_irrefl`.
//!
//! # Axiom closure
//!
//! `testBit_lt_pow` is a `Declaration::Theorem` built from `Nat.rec`,
//! `Or.rec`, `Eq.subst`, `False.elim` and the constructive `Nat.div2*` /
//! `Nat.testBit` / order / `Nat.pow_two_succ` lemma chain. No axioms, so
//! `env.axiom_deps` is empty and `proof_quality == Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants for the `testBit_lt_pow` proof.
struct C {
    nat: Expr,
    zero: Expr,
    succ: Expr,
    add: Expr,
    rec0: Expr, // Nat.rec.{0} — Prop motive
    bool_ty: Expr,
    bfalse: Expr,
    div2: Expr,
    div2par: Expr,
    testbit: Expr,
    pow: Expr,
    two: Expr,
    nat_lt: Expr,
    nat_le: Expr,
    eq1: Expr,      // Eq.{1}
    eq_symm1: Expr, // Eq.symm.{1}
    eq_subst: Expr, // Eq.subst.{1}
    false_elim0: Expr,
}

impl C {
    fn new() -> Self {
        let one_lvl = Level::succ(Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let one = Expr::app(succ.clone(), zero.clone());
        let two = Expr::app(succ.clone(), one);
        Self {
            nat,
            zero,
            succ,
            add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            rec0: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            bool_ty: Expr::const_(Name::from_string("Bool"), vec![]),
            bfalse: Expr::const_(Name::from_string("Bool.false"), vec![]),
            div2: Expr::const_(Name::from_string("Nat.div2"), vec![]),
            div2par: Expr::const_(Name::from_string("Nat.div2Par"), vec![]),
            testbit: Expr::const_(Name::from_string("Nat.testBit"), vec![]),
            pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            two,
            nat_lt: Expr::const_(Name::from_string("Nat.lt"), vec![]),
            nat_le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![one_lvl.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![one_lvl.clone()]),
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
    fn div2(&self, n: Expr) -> Expr {
        Expr::app(self.div2.clone(), n)
    }
    fn par(&self, n: Expr) -> Expr {
        Expr::app(self.div2par.clone(), n)
    }
    fn testbit(&self, n: Expr, i: Expr) -> Expr {
        Expr::apps(self.testbit.clone(), [n, i])
    }
    /// `Nat.pow 2 n`.
    fn pow2(&self, n: Expr) -> Expr {
        Expr::apps(self.pow.clone(), [self.two.clone(), n])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_lt.clone(), [a, b])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    /// `@Eq.{1} Bool a b`.
    fn eq_bool(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.bool_ty.clone(), a, b])
    }
    /// `@Eq.symm.{1} Nat a b h : Eq b a`.
    fn symm_nat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.nat.clone(), a, b, h])
    }
    /// `Nat.pow_two_succ n : Eq Nat (pow 2 (succ n)) (add (pow 2 n) (pow 2 n))`.
    fn pow_two_succ(&self, n: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]),
            n,
        )
    }
    /// `Nat.div2_rejoin n : Eq Nat n ((div2 n + div2 n) + div2Par n)`.
    fn rejoin(&self, n: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Nat.div2_rejoin"), vec![]),
            n,
        )
    }
}

// ===========================================================================
// Nat.testBit_lt_pow : ∀ n k, lt k (pow 2 n) → testBit k n = false
// ===========================================================================

fn build_testbit_lt_pow(c: &C) -> (Expr, Expr) {
    // P n := (k) → lt k (pow 2 n) → testBit k n = false
    let p_of = |n: &Expr, parent: &EnvDeclBuilder| -> Expr {
        let mut pb = EnvDeclBuilder::child_of(parent);
        let (k_id, k) = pb.fresh_local(c.nat.clone());
        let h_ty = c.lt(k.clone(), c.pow2(n.clone()));
        let (h_id, _h) = pb.fresh_local(h_ty.clone());
        let concl = c.eq_bool(c.testbit(k.clone(), n.clone()), c.bfalse.clone());
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

        // motive : fun (n : Nat) => P n
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&vb);
            let (n_id, n) = mb.fresh_local(c.nat.clone());
            let body = p_of(&n, &mb);
            let lam = mb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            mb.finish_child(lam)
        };

        // base : P 0 = (k) → lt k (pow 2 0) → testBit k 0 = false
        //   fun k h => testBit_eq_false_of_ge k 0 (le_of_succ_le_succ k 0 h)
        // Note: pow 2 0 ≡ 1 ≡ succ 0, and lt k 1 ≡ le (succ k)(succ 0) defeq, so
        //   h : le (succ k)(succ 0); le_of_succ_le_succ k 0 h : le k 0.
        let base = {
            let mut bb = EnvDeclBuilder::child_of(&vb);
            let (k_id, k) = bb.fresh_local(c.nat.clone());
            let h_ty = c.lt(k.clone(), c.pow2(c.zero.clone()));
            let (h_id, h) = bb.fresh_local(h_ty.clone());
            // le_of_succ_le_succ k 0 h : le k 0
            let le_k0 = Expr::apps(
                Expr::const_(Name::from_string("Nat.le_of_succ_le_succ"), vec![]),
                [k.clone(), c.zero.clone(), h.clone()],
            );
            // testBit_eq_false_of_ge k 0 le_k0 : testBit k 0 = false
            let out = Expr::apps(
                Expr::const_(Name::from_string("Nat.testBit_eq_false_of_ge"), vec![]),
                [k.clone(), c.zero.clone(), le_k0],
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

            // body : P (succ n') = (k) → lt k (pow 2 (succ n')) → testBit k (succ n') = false
            let (k_id, k) = sb.fresh_local(c.nat.clone());
            let h_ty = c.lt(k.clone(), c.pow2(sn.clone()));
            let (h_id, h) = sb.fresh_local(h_ty.clone());

            // r := div2 k, p := pow 2 n'
            let r = c.div2(k.clone());
            let p = c.pow2(np.clone());

            // We need bound : lt (div2 k) (pow 2 n'), then
            //   ih (div2 k) bound : testBit (div2 k) n' = false
            //   ≡ testBit k (succ n') = false   (iterDiv2 peel, defeq).

            // ---- contradiction branch helper: from hpr : le p r, derive lt r p (vacuously) ----
            // disj := le_or_lt p r : Or (le p r) (lt r p)
            let disj = Expr::apps(
                Expr::const_(Name::from_string("Nat.le_or_lt"), vec![]),
                [p.clone(), r.clone()],
            );
            let le_pr_ty = c.le(p.clone(), r.clone());
            let lt_rp_ty = c.lt(r.clone(), p.clone());

            // target of the Or.rec : lt (div2 k) (pow 2 n')   (≡ lt_rp_ty)
            let or_motive = {
                let mut ob = EnvDeclBuilder::child_of(&sb);
                let (_d_id, _d) = ob.fresh_local(Expr::apps(
                    Expr::const_(Name::from_string("Or"), vec![]),
                    [le_pr_ty.clone(), lt_rp_ty.clone()],
                ));
                // fun (_ : Or ..) => lt r p
                let lam = ob.mk_lam(
                    _d_id,
                    BinderInfo::Default,
                    Expr::apps(
                        Expr::const_(Name::from_string("Or"), vec![]),
                        [le_pr_ty.clone(), lt_rp_ty.clone()],
                    ),
                    lt_rp_ty.clone(),
                );
                ob.finish_child(lam)
            };

            // inl : (hpr : le p r) → lt r p   — derive False, then False.elim.
            let inl = {
                let mut ib = EnvDeclBuilder::child_of(&sb);
                let (hpr_id, hpr) = ib.fresh_local(le_pr_ty.clone());

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
                // le_add_right (r+r) (div2Par k) : le (r+r) ((r+r) + div2Par k)
                let rr = c.add(r.clone(), r.clone());
                let park = c.par(k.clone());
                let h_rr_join = Expr::apps(
                    Expr::const_(Name::from_string("Nat.le_add_right"), vec![]),
                    [rr.clone(), park.clone()],
                );
                // div2_rejoin k : k = (r+r) + div2Par k
                let rejoin = c.rejoin(k.clone());
                let joined = c.add(rr.clone(), park.clone()); // (r+r) + div2Par k
                                                              // transport h_rr_join along (div2_rejoin k).symm : ((r+r)+park) = k
                                                              //   motive fun z => le (r+r) z.  base : le (r+r) ((r+r)+park).
                                                              //   Eq.subst Nat motive ((r+r)+park) k symm base : le (r+r) k.
                let m_le_rr = {
                    let mut lb = EnvDeclBuilder::child_of(&ib);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    let body = c.le(rr.clone(), z);
                    let lam = lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body);
                    lb.finish_child(lam)
                };
                let rejoin_symm = c.symm_nat(k.clone(), joined.clone(), rejoin.clone());
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
                // le_trans (p+p) (r+r) k h_pp_rr h_rr_k : le (p+p) k
                let pp = c.add(p.clone(), p.clone());
                let h_pp_k = Expr::apps(
                    Expr::const_(Name::from_string("Nat.le_trans"), vec![]),
                    [pp.clone(), rr.clone(), k.clone(), h_pp_rr, h_rr_k],
                );
                // transport along (pow_two_succ n').symm : (p+p) = pow 2 (succ n')
                //   motive fun z => le z k.  base : le (p+p) k ⇒ le (pow 2 (succ n')) k.
                let m_le_z_k = {
                    let mut lb = EnvDeclBuilder::child_of(&ib);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    let body = c.le(z, k.clone());
                    let lam = lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body);
                    lb.finish_child(lam)
                };
                let pts = c.pow_two_succ(np.clone()); // pow 2 (succ n') = p+p
                let pts_symm = c.symm_nat(c.pow2(sn.clone()), pp.clone(), pts);
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
                // lt_of_le_of_lt (pow 2 (succ n')) k (pow 2 (succ n')) h_pow_k h
                //   : lt (pow 2 (succ n')) (pow 2 (succ n'))
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
                // lt_irrefl (pow 2 (succ n')) h_lt_self : False
                let false_pf = Expr::apps(
                    Expr::const_(Name::from_string("Nat.lt_irrefl"), vec![]),
                    [c.pow2(sn.clone()), h_lt_self],
                );
                // False.elim (lt r p) false_pf
                let out = Expr::apps(c.false_elim0.clone(), [lt_rp_ty.clone(), false_pf]);
                let lam = ib.mk_lam(hpr_id, BinderInfo::Default, le_pr_ty.clone(), out);
                ib.finish_child(lam)
            };

            // inr : (hlt : lt r p) → lt r p   — identity.
            let inr = {
                let mut rb = EnvDeclBuilder::child_of(&sb);
                let (hlt_id, hlt) = rb.fresh_local(lt_rp_ty.clone());
                let lam = rb.mk_lam(hlt_id, BinderInfo::Default, lt_rp_ty.clone(), hlt);
                rb.finish_child(lam)
            };

            // @Or.rec (le p r) (lt r p) or_motive inl inr disj : lt r p
            // (`Or.rec` has no explicit universe params — its motive is in Prop.)
            let or_rec = Expr::const_(Name::from_string("Or.rec"), vec![]);
            let bound = Expr::apps(or_rec, [le_pr_ty, lt_rp_ty, or_motive, inl, inr, disj]);

            // ih (div2 k) bound : testBit (div2 k) n' = false ≡ testBit k (succ n') = false
            let out = Expr::apps(ih.clone(), [r.clone(), bound]);

            let lam = sb.mk_lam(h_id, BinderInfo::Default, h_ty, out);
            let lam = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam);
            let lam = sb.mk_lam(np_id, BinderInfo::Default, c.nat.clone(), lam);
            sb.finish_child(lam)
        };

        // Nat.rec.{0} motive base step n : P n ; wrap in fun n => ...
        let (n_id, n) = vb.fresh_local(c.nat.clone());
        let rec_app = Expr::apps(c.rec0.clone(), [motive, base, step, n.clone()]);
        let lam = vb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec_app);
        vb.finish(lam)
    };
    (type_, value)
}

impl Environment {
    /// Register `Nat.testBit_lt_pow` as a kernel-checked `Declaration::Theorem`.
    ///
    /// `∀ n k, Nat.lt k (Nat.pow 2 n) → @Eq Bool (Nat.testBit k n) Bool.false`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid `Environment`.
    /// ENSURES: On success, `Nat.testBit_lt_pow` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive` (empty axiom closure).
    /// ENSURES: Idempotent — guarded by `get_const`; dependencies are
    ///          themselves idempotent.
    pub(crate) fn register_nat_testbit_lt_pow_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget):
        // Nat bitwise-cluster proof content — states/proves properties of the
        // import-suppressed div2/testBit/bitwise/Bool.xor web (see
        // register_nat_testbit_def). Suppressed with it.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Nat.testBit_lt_pow");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Dependencies: testBit / div2 foundation, Nat.pow_two_succ (rung 3),
        // div2_rejoin, and the order/arith lemma chain.
        self.register_nat_eq_of_testbit_proof()?; // testBit, div2_rejoin, div2*
        self.register_nat_testbit_bitwise_proof()?; // testBit_eq_false_of_ge
        self.register_nat_pow_two_succ_proof()?; // pow_two_succ (rung 3)
                                                 // Order/arith chain: le_or_lt, le_add_right, lt_irrefl, le_trans
                                                 // (mul_left_cancel bundle); add_le_add (arith_order); lt_of_le_of_lt
                                                 // (le-lt-lt trans); le_of_succ_le_succ is registered by the prelude.
        self.register_nat_mul_left_cancel_succ_proof()?;
        self.register_nat_arith_order_proofs()?;
        self.init_nat_trans_le_lt_lt()?;

        let c = C::new();
        let (type_, value) = build_testbit_lt_pow(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    fn env_with() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_nat_testbit_lt_pow_proof()
            .expect("register testBit_lt_pow");
        env
    }

    #[test]
    fn test_testbit_lt_pow_type_checks_and_axiom_free() {
        let mut env = env_with();
        env.register_nat_testbit_lt_pow_proof().expect("idempotent");
        let name = Name::from_string("Nat.testBit_lt_pow");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(name.clone(), vec![]))
            .unwrap_or_else(|e| panic!("Nat.testBit_lt_pow should type-check: {e:?}"));
        assert_eq!(
            env.get_const(&name).expect("registered").kind,
            ConstantKind::Theorem
        );
        let deps = env.axiom_deps(&name).expect("registered");
        let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert!(matches!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive)
        ));
    }

    /// Ground sanity: bit 2 of 3 (= 0b011) is false, since 3 < 2^2 = 4.
    /// The ground `testBit 3 2 ≡ false`, so `@Eq.refl Bool false` checks
    /// against `testBit 3 2 = false` purely by iota/delta reduction.
    #[test]
    fn test_testbit_lt_pow_ground_rfl() {
        let env = env_with();
        let c = C::new();
        let three = c.succ(c.succ(c.succ(c.zero.clone())));
        let two = c.succ(c.succ(c.zero.clone()));
        let stmt = c.eq_bool(c.testbit(three, two), c.bfalse.clone());
        let refl = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [c.bool_ty.clone(), c.bfalse.clone()],
        );
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&refl, &stmt)
            .expect("ground testBit 3 2 = false must hold by rfl");
    }
}
