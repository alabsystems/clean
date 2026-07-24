// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Component (A), sub-build (1): Int positive-numerator
//! extraction.
//!
//! # Why this module exists
//!
//! The dyadic-modulus convergence witness `Rat.exists_pow_gt` (the additive,
//! `inv`-free Archimedean primitive in `algebra_rat_archimedean.rs`) reduces, by
//! `Quot.ind` on `eps`, to a representative `Rat.Raw.mk a d`. From the
//! hypothesis `Rat.lt Rat.zero (Rat.mk a d)` — whose lift cross-multiplies to
//! `Int.lt Int.zero (Int.mul a (Int.ofNat 1))`, i.e. `Int.lt Int.zero a` — one
//! must EXTRACT that the numerator `a` is a POSITIVE integer
//! `a = Int.ofNat (Nat.succ m)`. That is the heavy "sign-analysis" sub-build
//! the plan flags (`designs/2026-06-18-kkl-real-sqrt-layer-plan.md` §7,
//! blocker (1)).
//!
//! This module builds that extraction AXIOM-FREE:
//!
//! ```text
//! Int.exists_eq_ofNat_succ_of_zero_lt :
//!   ∀ (a : Int), Int.lt Int.zero a →
//!     Exists (fun (m : Nat) => Eq Int a (Int.ofNat (Nat.succ m)))
//! ```
//!
//! # Proof strategy
//!
//! A single `@Int.rec.{0}` case-analysis on `a`, with an equation-carrying
//! motive that threads the strict-positivity hypothesis through each branch:
//!
//! ```text
//! M := fun (i : Int) => Int.lt Int.zero i →
//!        Exists (fun m => Eq Int i (Int.ofNat (Nat.succ m)))
//! ```
//!
//! applied to `a` and the incoming `h : Int.lt Int.zero a`. The recursor's two
//! minors receive the constructor pattern directly:
//!
//! - `Int.ofNat n` minor → inner `@Nat.rec.{0}` on `n`:
//!   - `n = Nat.zero`: the threaded `hn : Int.lt Int.zero (Int.ofNat Nat.zero)`
//!     delta-reduces to `Int.NonNeg (Int.negSucc Nat.zero)` (since
//!     `Int.sub 0 (0+1) ≡ Int.negSucc 0`), which the `True`/`False`
//!     discriminator turns into `False`; `@False.elim` closes the (vacuous)
//!     `Exists`.
//!   - `n = Nat.succ m`: the witness is `m`, and
//!     `Eq Int (Int.ofNat (Nat.succ m)) (Int.ofNat (Nat.succ m))` is `Eq.refl`.
//! - `Int.negSucc n` minor: the threaded `hn : Int.lt Int.zero (Int.negSucc n)`
//!   delta-reduces to `Int.NonNeg (Int.negSucc (Nat.succ n))` (negative), again
//!   discriminated to `False` and closed by `@False.elim`. (Vacuous.)
//!
//! The discrimination `NonNeg (negSucc _) → False` mirrors `Int.abs_of_neg`
//! (`algebra_int_abs_cond_proof.rs`): a `Prop`-valued `@Int.rec.{1}` predicate
//! `disc := fun i => Int.rec (fun _ => Prop) (fun _ => True) (fun _ => False) i`
//! reduces `disc (ofNat _) ≡ True`, `disc (negSucc _) ≡ False`; feeding the
//! `NonNeg` datum into `@Int.NonNeg.rec.{0}` with motive `fun i _ => disc i`
//! and minor `fun _ => True.intro` yields `disc (negSucc _) ≡ False`.
//!
//! # Axiom closure
//!
//! The proof term mentions only `Int`, `Int.lt`, `Int.NonNeg`,
//! `Int.NonNeg.rec`, `Int.rec`, `Int.ofNat`, `Int.negSucc`, `Nat`, `Nat.rec`,
//! `Nat.zero`, `Nat.succ`, `Exists`, `Exists.intro`, `Eq`, `Eq.refl`,
//! `True`, `True.intro`, `False`, `False.elim` — none a `Declaration::Axiom`.
//! So `env.axiom_deps("Int.exists_eq_ofNat_succ_of_zero_lt")` is empty and the
//! theorem is `ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved constant handles for the Int positive-extraction proof.
struct IntPosConsts {
    int: Expr,
    nat: Expr,
    int_zero: Expr,
    int_lt: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nonneg: Expr,
    nonneg_rec: Expr,
    /// `@Int.rec.{0}` — producing a `Prop` (`Sort 0`) proof.
    int_rec_type: Expr,
    /// `@Int.rec.{1}` — producing the `Prop`-valued discriminator (`Sort 1`).
    int_rec_prop: Expr,
    /// `@Nat.rec.{0}`.
    nat_rec_type: Expr,
    true_const: Expr,
    true_intro: Expr,
    false_const: Expr,
    false_elim: Expr,
    eq1: Expr,
    eq_refl1: Expr,
    exists_c: Expr,
    exists_intro: Expr,
}

impl IntPosConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            int: k("Int"),
            nat: k("Nat"),
            int_zero: k("Int.zero"),
            int_lt: k("Int.lt"),
            int_of_nat: k("Int.ofNat"),
            int_neg_succ: k("Int.negSucc"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nonneg: k("Int.NonNeg"),
            nonneg_rec: Expr::const_(Name::from_string("Int.NonNeg.rec"), vec![]),
            int_rec_type: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            int_rec_prop: Expr::const_(Name::from_string("Int.rec"), vec![l1.clone()]),
            nat_rec_type: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            true_const: k("True"),
            true_intro: k("True.intro"),
            false_const: k("False"),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![l1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1]),
        }
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
    /// `Int.lt Int.zero x`.
    fn pos(&self, x: Expr) -> Expr {
        Expr::apps(self.int_lt.clone(), [self.int_zero.clone(), x])
    }
    /// `Int.NonNeg x`.
    fn nonneg_of(&self, x: Expr) -> Expr {
        Expr::app(self.nonneg.clone(), x)
    }
    /// `@Eq Int x y`.
    fn eq_int(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.int.clone(), x, y])
    }
    /// `@Eq.refl Int x`.
    fn refl_int(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.int.clone(), x])
    }

    /// The `Exists` predicate `fun (m : Nat) => Eq Int target (ofNat (succ m))`.
    fn exists_pred(&self, parent: &EnvDeclBuilder, target: Expr) -> Expr {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (m_id, m) = mb.fresh_local(self.nat.clone());
        let body = self.eq_int(target, self.of_nat(self.succ(m)));
        let lam = mb.mk_lam(m_id, BinderInfo::Default, self.nat.clone(), body);
        mb.finish_child(lam)
    }

    /// `Exists (fun m => Eq Int target (ofNat (succ m)))`.
    fn exists_goal(&self, parent: &EnvDeclBuilder, target: Expr) -> Expr {
        let pred = self.exists_pred(parent, target);
        Expr::apps(self.exists_c.clone(), [self.nat.clone(), pred])
    }

    /// The `True`/`False` discriminator `disc : Int → Prop` with
    /// `disc (ofNat _) ≡ True`, `disc (negSucc _) ≡ False`.
    fn discriminator(&self, parent: &EnvDeclBuilder) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let prop_motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (i_id, _i) = mb.fresh_local(self.int.clone());
            let lam = mb.mk_lam(i_id, BinderInfo::Default, self.int.clone(), Expr::prop());
            mb.finish_child(lam)
        };
        let of_nat_minor = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (n_id, _n) = mb.fresh_local(self.nat.clone());
            let lam = mb.mk_lam(
                n_id,
                BinderInfo::Default,
                self.nat.clone(),
                self.true_const.clone(),
            );
            mb.finish_child(lam)
        };
        let neg_succ_minor = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (n_id, _n) = mb.fresh_local(self.nat.clone());
            let lam = mb.mk_lam(
                n_id,
                BinderInfo::Default,
                self.nat.clone(),
                self.false_const.clone(),
            );
            mb.finish_child(lam)
        };
        let (i_id, i) = b.fresh_local(self.int.clone());
        let rec_app = Expr::apps(
            self.int_rec_prop.clone(),
            [prop_motive, of_nat_minor, neg_succ_minor, i.clone()],
        );
        let lam = b.mk_lam(i_id, BinderInfo::Default, self.int.clone(), rec_app);
        b.finish_child(lam)
    }

    /// From `hn : Int.NonNeg (Int.negSucc k)`, derive `False`, then any goal.
    ///
    /// `@Int.NonNeg.rec.{0} (fun i _ => disc i) (fun _ => True.intro)
    ///   (Int.negSucc k) hn : disc (negSucc k) ≡ False`, then `@False.elim goal`.
    fn elim_nonneg_negsucc(
        &self,
        parent: &EnvDeclBuilder,
        neg_succ_k: Expr,
        hn: Expr,
        goal: Expr,
    ) -> Expr {
        let disc = self.discriminator(parent);
        // motive: fun (i : Int) (_ : NonNeg i) => disc i
        let nn_motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (i_id, i) = mb.fresh_local(self.int.clone());
            let hi_ty = self.nonneg_of(i.clone());
            let (hi_id, _hi) = mb.fresh_local(hi_ty.clone());
            let body = Expr::app(disc.clone(), i.clone());
            let lam = mb.mk_lam(hi_id, BinderInfo::Default, hi_ty, body);
            let lam = mb.mk_lam(i_id, BinderInfo::Default, self.int.clone(), lam);
            mb.finish_child(lam)
        };
        // minor: fun (m : Nat) => True.intro  (goal `disc (ofNat m) ≡ True`)
        let nn_minor = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (m_id, _m) = mb.fresh_local(self.nat.clone());
            let lam = mb.mk_lam(
                m_id,
                BinderInfo::Default,
                self.nat.clone(),
                self.true_intro.clone(),
            );
            mb.finish_child(lam)
        };
        let false_proof = Expr::apps(
            self.nonneg_rec.clone(),
            [nn_motive, nn_minor, neg_succ_k, hn],
        );
        Expr::apps(self.false_elim.clone(), [goal, false_proof])
    }
}

impl Environment {
    /// Register `Int.exists_eq_ofNat_succ_of_zero_lt`. Idempotent.
    ///
    /// `∀ a : Int, Int.lt Int.zero a →
    ///    Exists (fun m : Nat => Eq Int a (Int.ofNat (Nat.succ m)))`.
    /// Constructive, empty admitted-axiom closure.
    pub fn register_int_exists_eq_ofnat_succ_of_zero_lt(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Int.exists_eq_ofNat_succ_of_zero_lt");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_int()?;
        self.init_int_ord()?; // Int.lt, Int.NonNeg, Int.NonNeg.rec
        self.init_eq()?;
        self.init_true_false()?;
        self.init_exists()?;

        let c = IntPosConsts::new();

        // Type: ∀ a, Int.lt 0 a → Exists (fun m => Eq Int a (ofNat (succ m))).
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.int.clone());
            let h_ty = c.pos(a.clone());
            let (h_id, _h) = b.fresh_local(h_ty.clone());
            let concl = c.exists_goal(&b, a.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.int.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.int.clone());
            let h_ty = c.pos(a.clone());
            let (h_id, h) = b.fresh_local(h_ty.clone());

            // Int.rec motive: fun (i : Int) => Int.lt 0 i → Exists (… i …).
            let rec_motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = mb.fresh_local(c.int.clone());
                let hyp = c.pos(i.clone());
                let (hyp_id, _hyp) = mb.fresh_local(hyp.clone());
                let concl = c.exists_goal(&mb, i.clone());
                let body = mb.mk_pi(hyp_id, BinderInfo::Default, hyp, concl);
                let lam = mb.mk_lam(i_id, BinderInfo::Default, c.int.clone(), body);
                mb.finish_child(lam)
            };

            // ofNat case: fun (n : Nat) (hn : Int.lt 0 (ofNat n)) => Nat.rec on n.
            let of_nat_case = {
                let mut ob = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = ob.fresh_local(c.nat.clone());
                let hn_ty = c.pos(c.of_nat(n.clone()));
                let (hn_id, hn) = ob.fresh_local(hn_ty.clone());

                // Nat.rec motive: fun (k : Nat) => Int.lt 0 (ofNat k) → Exists (… (ofNat k) …).
                let nat_motive = {
                    let mut mb = EnvDeclBuilder::child_of(&ob);
                    let (k_id, kk) = mb.fresh_local(c.nat.clone());
                    let hyp = c.pos(c.of_nat(kk.clone()));
                    let (hyp_id, _hyp) = mb.fresh_local(hyp.clone());
                    let concl = c.exists_goal(&mb, c.of_nat(kk.clone()));
                    let body = mb.mk_pi(hyp_id, BinderInfo::Default, hyp, concl);
                    let lam = mb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body);
                    mb.finish_child(lam)
                };

                // zero minor: fun (hz : Int.lt 0 (ofNat 0)) => False.elim (…).
                //   hz : Int.lt 0 0 ≡ NonNeg (negSucc 0).
                let zero_minor = {
                    let mut zb = EnvDeclBuilder::child_of(&ob);
                    let hz_ty = c.pos(c.of_nat(c.nat_zero.clone()));
                    let (hz_id, hz) = zb.fresh_local(hz_ty.clone());
                    let neg_succ_0 = c.neg_succ(c.nat_zero.clone());
                    let goal = c.exists_goal(&zb, c.of_nat(c.nat_zero.clone()));
                    let body = c.elim_nonneg_negsucc(&zb, neg_succ_0, hz, goal);
                    let lam = zb.mk_lam(hz_id, BinderInfo::Default, hz_ty, body);
                    zb.finish_child(lam)
                };

                // succ minor: fun (m : Nat) (_ih) (hs : Int.lt 0 (ofNat (succ m))) =>
                //   Exists.intro Nat pred m (Eq.refl Int (ofNat (succ m))).
                let succ_minor = {
                    let mut sb = EnvDeclBuilder::child_of(&ob);
                    let (m_id, m) = sb.fresh_local(c.nat.clone());
                    // ih : Int.lt 0 (ofNat m) → Exists (… (ofNat m) …).
                    let ih_ty = {
                        let mut ib = EnvDeclBuilder::child_of(&sb);
                        let hyp = c.pos(c.of_nat(m.clone()));
                        let (hyp_id, _hyp) = ib.fresh_local(hyp.clone());
                        let concl = c.exists_goal(&ib, c.of_nat(m.clone()));
                        let e = ib.mk_pi(hyp_id, BinderInfo::Default, hyp, concl);
                        ib.finish_child(e)
                    };
                    let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());
                    let succ_m = c.succ(m.clone());
                    let target = c.of_nat(succ_m.clone());
                    let hs_ty = c.pos(target.clone());
                    let (hs_id, _hs) = sb.fresh_local(hs_ty.clone());

                    // witness m, proof Eq.refl : Eq Int (ofNat (succ m)) (ofNat (succ m)).
                    let pred = c.exists_pred(&sb, target.clone());
                    let refl = c.refl_int(target.clone());
                    let intro = Expr::apps(
                        c.exists_intro.clone(),
                        [c.nat.clone(), pred, m.clone(), refl],
                    );
                    let lam = sb.mk_lam(hs_id, BinderInfo::Default, hs_ty, intro);
                    let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam);
                    let lam = sb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam);
                    sb.finish_child(lam)
                };

                // @Nat.rec.{0} nat_motive zero_minor succ_minor n : motive n
                //   ≡ (Int.lt 0 (ofNat n) → Exists …); apply to hn.
                let nat_rec_app = Expr::apps(
                    c.nat_rec_type.clone(),
                    [nat_motive, zero_minor, succ_minor, n.clone()],
                );
                let applied = Expr::app(nat_rec_app, hn.clone());
                let lam = ob.mk_lam(hn_id, BinderInfo::Default, hn_ty, applied);
                let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
                ob.finish_child(lam)
            };

            // negSucc case: fun (n : Nat) (hn : Int.lt 0 (negSucc n)) => False.elim (…).
            //   hn : Int.lt 0 (negSucc n) ≡ NonNeg (negSucc (succ n)).
            let neg_succ_case = {
                let mut nb = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = nb.fresh_local(c.nat.clone());
                let neg_succ_n = c.neg_succ(n.clone());
                let hn_ty = c.pos(neg_succ_n.clone());
                let (hn_id, hn) = nb.fresh_local(hn_ty.clone());
                let neg_succ_succ_n = c.neg_succ(c.succ(n.clone()));
                let goal = c.exists_goal(&nb, neg_succ_n.clone());
                let body = c.elim_nonneg_negsucc(&nb, neg_succ_succ_n, hn, goal);
                let lam = nb.mk_lam(hn_id, BinderInfo::Default, hn_ty, body);
                let lam = nb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
                nb.finish_child(lam)
            };

            // @Int.rec.{0} rec_motive of_nat_case neg_succ_case a : motive a;
            // apply to h.
            let rec_app = Expr::apps(
                c.int_rec_type.clone(),
                [rec_motive, of_nat_case, neg_succ_case, a.clone()],
            );
            let applied = Expr::app(rec_app, h.clone());
            let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, applied);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.int.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Nat.lt_two_pow_succ_self : ∀ (k : Nat), Nat.lt k (Nat.pow 2 (Nat.succ k))`.
    ///
    /// The STRICT two-power Archimedean fact `k < 2^(k+1)`. Constructive, empty
    /// admitted-axiom closure. Distinct from the on-main NON-strict
    /// `Nat.le_two_pow_self` (`k ≤ 2^k`): the `Rat.exists_pow_gt` witness needs
    /// the STRICT margin, supplied by choosing the dyadic exponent `succ e`
    /// rather than `e`.
    ///
    /// Proof: `Nat.lt k m ≡ Nat.le (Nat.succ k) m`. With `Nat.add_le_add k (2^k)
    /// (Nat.succ Nat.zero) (2^k) (Nat.le_two_pow_self k) (Nat.one_le_two_pow k)`
    /// we get `Nat.le (Nat.add k 1) (Nat.add (2^k) (2^k))`, and `Nat.add k 1 ≡
    /// Nat.succ k` (def-eq, `Nat.add` recurses on the right). Transport across
    /// `Eq.symm (Nat.pow_two_succ k) : Nat.add (2^k) (2^k) = 2^(succ k)` (motive
    /// `fun t => Nat.le (succ k) t`) lands `Nat.le (succ k) (2^(succ k))` ≡ goal.
    pub fn register_nat_lt_two_pow_succ_self(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.lt_two_pow_succ_self");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_nat()?;
        self.init_le()?;
        self.init_lt()?;
        self.init_eq()?;
        self.register_nat_le_two_pow_self()?; // Nat.le_two_pow_self (+ Nat.one_le_two_pow)
        self.register_nat_arith_order_proofs()?; // Nat.add_le_add
        self.register_nat_pow_two_succ_proof()?; // Nat.pow_two_succ

        let l1 = Level::succ(Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let add_le_add = Expr::const_(Name::from_string("Nat.add_le_add"), vec![]);
        let le_two_pow_self = Expr::const_(Name::from_string("Nat.le_two_pow_self"), vec![]);
        let one_le_two_pow = Expr::const_(Name::from_string("Nat.one_le_two_pow"), vec![]);
        let pow_two_succ = Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]);
        let eq1 = Expr::const_(Name::from_string("Eq"), vec![l1.clone()]);
        let eq_symm = Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]);
        let eq_subst = Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]);
        let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);

        let two = Expr::app(
            nat_succ.clone(),
            Expr::app(nat_succ.clone(), nat_zero.clone()),
        );
        let nat_one = Expr::app(nat_succ.clone(), nat_zero.clone());
        let pow2 = |e: Expr| Expr::apps(nat_pow.clone(), [two.clone(), e]);
        let add = |x: Expr, y: Expr| Expr::apps(nat_add.clone(), [x, y]);
        let nle = |x: Expr, y: Expr| Expr::apps(nat_le.clone(), [x, y]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, kk) = b.fresh_local(nat.clone());
            let concl = Expr::apps(
                nat_lt.clone(),
                [kk.clone(), pow2(Expr::app(nat_succ.clone(), kk.clone()))],
            );
            let e = b.mk_pi(k_id, BinderInfo::Default, nat.clone(), concl);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, kk) = b.fresh_local(nat.clone());
            let p = pow2(kk.clone());
            let succ_k = Expr::app(nat_succ.clone(), kk.clone());
            // h_add : Nat.le (Nat.add k 1) (Nat.add (2^k) (2^k))
            //   ≡ Nat.le (succ k) (2^k + 2^k).
            let h_add = Expr::apps(
                add_le_add.clone(),
                [
                    kk.clone(),
                    p.clone(),
                    nat_one.clone(),
                    p.clone(),
                    Expr::app(le_two_pow_self.clone(), kk.clone()),
                    Expr::app(one_le_two_pow.clone(), kk.clone()),
                ],
            );
            // e_sym : Eq Nat (2^k + 2^k) (2^(succ k))  := symm (pow_two_succ k).
            let sum = add(p.clone(), p.clone());
            let pow_succ = pow2(succ_k.clone());
            let e_sym = Expr::apps(
                eq_symm.clone(),
                [
                    nat.clone(),
                    pow_succ.clone(),
                    sum.clone(),
                    Expr::app(pow_two_succ.clone(), kk.clone()),
                ],
            );
            // motive : fun t => Nat.le (succ k) t.
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = mb.fresh_local(nat.clone());
                let body = nle(succ_k.clone(), t);
                let lam = mb.mk_lam(t_id, BinderInfo::Default, nat.clone(), body);
                mb.finish_child(lam)
            };
            // @Eq.subst Nat motive (2^k+2^k) (2^(succ k)) e_sym h_add
            //   : Nat.le (succ k) (2^(succ k)) ≡ Nat.lt k (2^(succ k)).
            let body = Expr::apps(
                eq_subst.clone(),
                [nat.clone(), motive, sum, pow_succ, e_sym, h_add],
            );
            let _ = &eq1; // Eq used only via symm/subst helpers above.
            b.finish(b.mk_lam(k_id, BinderInfo::Default, nat.clone(), body))
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis().expect("init_boolean_analysis"); // Nat two-pow deps
        env.register_int_exists_eq_ofnat_succ_of_zero_lt()
            .expect("register Int.exists_eq_ofNat_succ_of_zero_lt");
        env.register_int_exists_eq_ofnat_succ_of_zero_lt()
            .expect("idempotent");
        env.register_nat_lt_two_pow_succ_self()
            .expect("register Nat.lt_two_pow_succ_self");
        env.register_nat_lt_two_pow_succ_self().expect("idempotent");
        env
    }

    fn check_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env
            .get_const(&nm)
            .unwrap_or_else(|| panic!("{name} registered"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "{name} closure must be empty (foundational-only), got {:?}",
            env.axiom_deps(&nm)
        );
    }

    #[test]
    fn test_int_exists_eq_ofnat_succ_of_zero_lt_constructive() {
        let env = env();
        check_constructive(&env, "Int.exists_eq_ofNat_succ_of_zero_lt");
    }

    #[test]
    fn test_nat_lt_two_pow_succ_self_constructive() {
        let env = env();
        check_constructive(&env, "Nat.lt_two_pow_succ_self");
    }
}
