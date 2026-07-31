// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Nat.testBit_bitwise` (Track II step 3) and the
//! `Nat.testBit_and` / `Nat.testBit_or` / `Nat.testBit_xor` corollaries:
//!
//! ```text
//! Nat.testBit_bitwise :
//!   (f : Bool → Bool → Bool) → (f false false = false) →
//!   (m n i : Nat) → Nat.testBit (Nat.bitwise f m n) i
//!                 = f (Nat.testBit m i) (Nat.testBit n i)
//! Nat.testBit_and (m n i) : testBit (Nat.land m n) i = (testBit m i && testBit n i)
//! Nat.testBit_or  (m n i) : testBit (Nat.lor  m n) i = (testBit m i || testBit n i)
//! Nat.testBit_xor (m n i) : testBit (Nat.xor  m n) i = xor (testBit m i) (testBit n i)
//! ```
//!
//! # Definitional facts (all `rfl`, verified by the module probe tests)
//!
//! - `Nat.bitwiseAux f (succ k) m n ≡ (r + r) + Nat.ofBool (f (testBit m 0)(testBit n 0))`
//!   where `r := Nat.bitwiseAux f k (div2 m)(div2 n)`  (single `Nat.rec` step,
//!   inner-recursion `iterDiv2`-style ⇒ `ih = bitwiseAux f k`).
//! - `Nat.bitwiseAux f 0 m n ≡ 0`.
//! - `Nat.bitwise f m n ≡ Nat.bitwiseAux f (m + n) m n`.
//! - `Nat.testBit x (succ i) ≡ Nat.testBit (div2 x) i`,
//!   `Nat.testBit x 0 ≡ Nat.toBoolPar (div2Par x)`.
//! - `Nat.ofBool false ≡ 0`, `Nat.ofBool true ≡ 1`.
//! - `div2 (succ m) ≡ div2 m + div2Par m`, `div2Par (succ m) ≡ 1 - div2Par m`.
//! - `x + 0 ≡ x`, `x + 1 ≡ succ x`, `x + succ y ≡ succ (x + y)`.
//!
//! # Lemma chain (every one a real kernel-checked, axiom-free term)
//!
//! 1. `Nat.div2_two_mul : (r : Nat) → div2 (r + r) = r`  — induction on `r`
//!    (`succ r + succ r ≡ succ (succ (r + r))`; `div2 (succ (succ x)) ≡
//!    div2 (succ x) + div2Par (succ x)`; via `div2Par_zero_or_one` the parity of
//!    `r+r` cancels so the step closes).
//! 2. `Nat.div2Par_two_mul : (r : Nat) → div2Par (r + r) = 0`  — induction on `r`.
//! 3. `Nat.bitNat_lo : (b : Bool)(r : Nat) → testBit ((r + r) + ofBool b) 0 = b`
//!    — `Bool.rec` on `b`; each branch is a `div2Par`-parity computation built on
//!    lemma 2 (`(r+r)+0` and `(r+r)+1 ≡ succ (r+r)`).
//! 4. `Nat.bitNat_hi : (b : Bool)(r : Nat) → div2 ((r + r) + ofBool b) = r`
//!    — `Bool.rec` on `b`; lemma 1 directly for `false`, and
//!    `div2 (succ (r+r)) ≡ div2 (r+r) + div2Par (r+r)` + lemmas 1,2 for `true`.
//! 5. `Nat.testBit_eq_false_of_ge : (x i : Nat) → Nat.le x i → testBit x i = false`
//!    — strong induction on `x` (Acc.rec over Nat.accNatLt): bit `i ≥ x` of `x`
//!    is `false` because `div2 x < x ≤ i` recurses, and `x = 0` is all-false.
//! 6. `Nat.testBit_bitwiseAux : (f)(k i m n) → Nat.lt i k →
//!       testBit (bitwiseAux f k m n) i = f (testBit m i)(testBit n i)`
//!    — induction on the fuel `k`; the `succ k` case splits `i = 0` (lemma 3) vs
//!    `i = succ j` (lemma 4 to peel `div2`, then the IH at `k` on `div2 m`,
//!    `div2 n`, `j`).
//! 7. `Nat.testBit_bitwiseAux_high : (f)(hf : f false false = false)(k i m n) →
//!       Nat.le k i → Nat.le m k_ignored …` — the truncation half: for `i ≥ fuel`
//!       and `i ≥ m`, `i ≥ n`, the result bit is `false = f false false`.
//!    (Implemented as `Nat.testBit_bitwiseAux_eq` combining both halves over the
//!    full fuel `m + n`.)
//! 8. `Nat.testBit_bitwise` — instantiates fuel `= m + n`: lemma 6 covers
//!    `i < m+n`; for `i ≥ m+n` both `testBit (bitwise …) i` (lemma 5, since the
//!    result `< 2^(m+n)`… in fact `≤ ` bit-length) and `f (testBit m i)(testBit n
//!    i) = f false false = false` (lemma 5 on `m`,`n` since `i ≥ m+n ≥ m,n`).
//!
//! # Axiom closure
//!
//! Every declaration is a `Declaration::Theorem` built from `Nat.rec`/`Or.rec`/
//! `Bool.rec`/`Acc.rec`/`Eq.*`/`congrArg`, the constructive `Nat.div2*` /
//! `Nat.testBit` / `Nat.ofBool` / `Nat.bitwise*` defs, `Nat.accNatLt`, and the
//! constructive order/arith lemmas. None is an axiom, so `env.axiom_deps` is
//! empty for each and `proof_quality == Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants shared across the testBit-bitwise lemmas.
struct C {
    nat: Expr,
    zero: Expr,
    succ: Expr,
    one: Expr,
    add: Expr,
    rec0: Expr, // Nat.rec.{0} — Prop motive
    bool_ty: Expr,
    #[cfg(test)]
    btrue: Expr,
    bfalse: Expr,
    div2: Expr,
    div2par: Expr,
    tobool: Expr,
    of_bool: Expr,
    testbit: Expr,
    sub: Expr,
    eq1: Expr, // Eq.{1}
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    congr11: Expr, // congrArg.{1,1}
}

impl C {
    fn new() -> Self {
        let one_lvl = Level::succ(Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let one = Expr::app(succ.clone(), zero.clone());
        Self {
            nat,
            zero,
            succ,
            one,
            add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            rec0: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            bool_ty: Expr::const_(Name::from_string("Bool"), vec![]),
            #[cfg(test)]
            btrue: Expr::const_(Name::from_string("Bool.true"), vec![]),
            bfalse: Expr::const_(Name::from_string("Bool.false"), vec![]),
            div2: Expr::const_(Name::from_string("Nat.div2"), vec![]),
            div2par: Expr::const_(Name::from_string("Nat.div2Par"), vec![]),
            tobool: Expr::const_(Name::from_string("Nat.toBoolPar"), vec![]),
            of_bool: Expr::const_(Name::from_string("Nat.ofBool"), vec![]),
            testbit: Expr::const_(Name::from_string("Nat.testBit"), vec![]),
            sub: Expr::const_(Name::from_string("Nat.sub"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![one_lvl.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![one_lvl.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![one_lvl.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![one_lvl.clone()]),
            congr11: Expr::const_(
                Name::from_string("congrArg"),
                vec![one_lvl.clone(), one_lvl.clone()],
            ),
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
    #[cfg(test)]
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
    /// `@congrArg.{1,1} Bool Bool a1 a2 g h : Eq (g a1) (g a2)`.
    fn congr_bool_bool(&self, a1: Expr, a2: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr11.clone(),
            [self.bool_ty.clone(), self.bool_ty.clone(), a1, a2, g, h],
        )
    }
    fn symm_bool(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.bool_ty.clone(), a, b, h])
    }
    fn tobool(&self, n: Expr) -> Expr {
        Expr::app(self.tobool.clone(), n)
    }
    fn of_bool(&self, b: Expr) -> Expr {
        Expr::app(self.of_bool.clone(), b)
    }
    fn testbit0(&self, x: Expr) -> Expr {
        Expr::apps(self.testbit.clone(), [x, self.zero.clone()])
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.sub.clone(), [a, b])
    }
    /// `(r + r) + Nat.ofBool b`.
    fn bit_nat(&self, b: Expr, r: Expr) -> Expr {
        self.add(self.add(r.clone(), r), self.of_bool(b))
    }
    /// A `fun (p : Nat) => body(p)` lambda (Nat → Nat).
    fn lam_nat_nat(&self, parent: &EnvDeclBuilder, body: &dyn Fn(Expr) -> Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (p_id, p) = b.fresh_local(self.nat.clone());
        b.mk_lam(p_id, BinderInfo::Default, self.nat.clone(), body(p))
    }
}

// ===========================================================================
// Lemma 1: Nat.div2_two_mul  (r : Nat) → div2 (r + r) = r
// ===========================================================================
//
// Induction on r via Nat.rec.{0}.
//   base r=0: div2 (0+0) ≡ div2 0 ≡ 0 = 0       → refl 0
//   step r=succ k, ih : div2 (k+k) = k:
//     (succ k)+(succ k) ≡ succ (succ k + k) ≡ succ (succ (k+k))
//       [add_succ then succ_add — both rfl on Nat.add 2nd-arg recursion? succ_add
//        is NOT rfl, so we route via the proven Nat.succ_add theorem]
//     We avoid needing succ_add by instead proving the equation with the LHS
//     written so that only DEFINITIONAL reductions are used:
//       div2 ((succ k)+(succ k))
//         ≡ div2 (succ (succ k + k))            [add_succ: x+succ y ≡ succ(x+y)]
//     and succ k + k  needs succ_add to become succ (k+k). We use the registered
//     Nat.succ_add theorem (an Eq) to rewrite under div2∘succ via congrArg, then
//     reduce div2 (succ (succ (k+k))) ≡ div2 (succ (k+k)) + div2Par (succ (k+k))
//       ≡ (div2 (k+k) + div2Par (k+k)) + (1 - div2Par (k+k)).
//     With lemma 2 (div2Par (k+k) = 0) this is (div2(k+k)+0)+(1-0) ≡ div2(k+k)+1
//       ≡ succ (div2 (k+k)) ; and congrArg succ ih gives succ (div2(k+k)) = succ k.
//
// To keep lemma 1 and lemma 2 mutually independent we prove lemma 2 FIRST and
// reference it from lemma 1.

/// `Nat.div2Par_two_mul : (r : Nat) → div2Par (r + r) = 0`.
///
/// Induction on r.  base: div2Par 0 ≡ 0.  step: with succ_add,
///   div2Par ((succ k)+(succ k)) ≡ div2Par (succ (succ k + k))
///     = div2Par (succ (succ (k+k)))            [congr via succ_add]
///     ≡ 1 - div2Par (succ (k+k)) ≡ 1 - (1 - div2Par (k+k))
///   with ih (div2Par (k+k) = 0): 1 - (1 - 0) ≡ 1 - 1 ≡ 0.
fn build_div2par_two_mul(c: &C) -> (Expr, Expr) {
    let mk_concl = |r: &Expr| c.eq_nat(c.par(c.add(r.clone(), r.clone())), c.zero.clone());
    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (r_id, r) = b.fresh_local(c.nat.clone());
        let concl = mk_concl(&r);
        let pi = b.mk_pi(r_id, BinderInfo::Default, c.nat.clone(), concl);
        b.finish(pi)
    };

    let mut vb = EnvDeclBuilder::new();
    let (r_id, r) = vb.fresh_local(c.nat.clone());
    // motive : fun t => div2Par (t + t) = 0
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&vb);
        let (t_id, t) = mb.fresh_local(c.nat.clone());
        let body = mk_concl(&t);
        let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
        mb.finish_child(lam)
    };
    // base : div2Par (0 + 0) = 0  ≡ div2Par 0 = 0 ≡ 0 = 0  → refl 0
    let base = c.refl_nat(c.zero.clone());
    // step : (k) → motive k → motive (succ k)
    let step = {
        let mut sb = EnvDeclBuilder::child_of(&vb);
        let (k_id, k) = sb.fresh_local(c.nat.clone());
        let ih_ty = mk_concl(&k);
        let (ih_id, ih) = sb.fresh_local(ih_ty.clone());

        let sk = c.succ(k.clone());
        // goal : div2Par ((succ k)+(succ k)) = 0
        // LHS ≡ div2Par (succ (succ k + k))   [add_succ rfl]
        // succ_add k k : succ k + k = succ (k + k)
        let succ_add = Expr::apps(
            Expr::const_(Name::from_string("Nat.succ_add"), vec![]),
            [k.clone(), k.clone()],
        );
        // bridge1 : div2Par (succ (succ k + k)) = div2Par (succ (succ (k+k)))
        //   congrArg (fun z => div2Par (succ z)) (succ_add k k)
        //   succ_add maps  succ k + k  ↦  succ (k + k), so the congr endpoints are
        //   succ_kk and (succ kk).
        let succ_kk = c.add(c.succ(k.clone()), k.clone()); // succ k + k
        let kk = c.add(k.clone(), k.clone()); // k + k
        let succ_of_kk = c.succ(kk.clone()); // succ (k + k)
        let f_div2par_succ = {
            let div2par_succ = |z: Expr| c.par(c.succ(z));
            c.lam_nat_nat(&sb, &|z| div2par_succ(z))
        };
        let bridge1 = c.congr_nat_nat(
            succ_kk.clone(),
            succ_of_kk.clone(),
            f_div2par_succ,
            succ_add,
        );
        // LHS (div2Par ((succ k)+(succ k))) ≡ div2Par (succ (succ k + k)) defeq,
        // so bridge1 : LHS = div2Par (succ (succ (k+k))).
        let lhs = c.par(c.add(sk.clone(), sk.clone()));
        let mid = c.par(c.succ(c.succ(kk.clone()))); // div2Par (succ (succ (k+k)))
                                                     // tail : div2Par (succ (succ (k+k))) = 0
                                                     //   div2Par (succ (succ (k+k))) ≡ 1 - div2Par (succ (k+k)) ≡ 1 - (1 - div2Par (k+k))
                                                     //   congrArg (fun p => 1 - (1 - p)) ih : 1 - (1 - div2Par (k+k)) = 1 - (1 - 0)
                                                     //   and 1 - (1 - 0) ≡ 0, so the RHS literal is 0.
        let one = c.one.clone();
        let sub = Expr::const_(Name::from_string("Nat.sub"), vec![]);
        let f_one_sub_one_sub = {
            let mut fb = EnvDeclBuilder::child_of(&sb);
            let (p_id, p) = fb.fresh_local(c.nat.clone());
            // 1 - (1 - p)
            let inner = Expr::apps(sub.clone(), [one.clone(), p.clone()]);
            let outer = Expr::apps(sub.clone(), [one.clone(), inner]);
            let lam = fb.mk_lam(p_id, BinderInfo::Default, c.nat.clone(), outer);
            fb.finish_child(lam)
        };
        // congrArg f_one_sub_one_sub ih : 1-(1-div2Par(k+k)) = 1-(1-0)
        let par_kk = c.par(kk.clone());
        let tail_src = {
            // 1 - (1 - div2Par(k+k))
            let inner = Expr::apps(sub.clone(), [one.clone(), par_kk.clone()]);
            Expr::apps(sub.clone(), [one.clone(), inner])
        };
        let tail_dst = {
            // 1 - (1 - 0)  ≡ 0
            let inner = Expr::apps(sub.clone(), [one.clone(), c.zero.clone()]);
            Expr::apps(sub.clone(), [one.clone(), inner])
        };
        let tail0 = c.congr_nat_nat(par_kk.clone(), c.zero.clone(), f_one_sub_one_sub, ih);
        // tail0 : tail_src = tail_dst ; tail_dst ≡ 0, mid ≡ tail_src (defeq), so
        // we can chain: mid = tail_src (refl, defeq) then tail0 then tail_dst = 0 (refl).
        // Compose: bridge1 (LHS = mid) ; (mid = tail_dst via tail0, defeq mid≡tail_src) ; (tail_dst = 0 refl)
        // Build mid = tail_dst : Eq.trans (refl: mid = tail_src) tail0 — but mid ≡ tail_src
        // definitionally, so tail0 already has type mid = tail_dst up to defeq. We
        // wrap with Eq objects carefully:
        //   step_a : LHS = mid          (bridge1)
        //   step_b : mid = 0            (tail0 retyped: src≡mid, dst≡0)
        // out : Eq.trans step_a step_b : LHS = 0.
        let out = c.trans_nat(lhs, mid, c.zero.clone(), bridge1, tail0);
        let _ = (tail_src, tail_dst);
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, out);
        let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_ih);
        sb.finish_child(lam_k)
    };
    let rec_app = Expr::apps(c.rec0.clone(), [motive, base, step, r]);
    let value = {
        let lam = vb.mk_lam(r_id, BinderInfo::Default, c.nat.clone(), rec_app);
        vb.finish(lam)
    };
    (type_, value)
}

/// `Nat.div2_two_mul : (r : Nat) → div2 (r + r) = r`.
///
/// Induction on r.  base: div2 (0+0) ≡ 0.  step:
///   div2 ((succ k)+(succ k)) ≡ div2 (succ (succ k + k))
///     = div2 (succ (succ (k+k)))                 [congr via succ_add]
///     ≡ div2 (succ (k+k)) + div2Par (succ (k+k))
///     ≡ (div2 (k+k) + div2Par (k+k)) + (1 - div2Par (k+k))
///   with div2Par_two_mul k (div2Par (k+k) = 0):
///     ≡ (div2 (k+k) + 0) + (1 - 0) ≡ div2 (k+k) + 1 ≡ succ (div2 (k+k))
///   and congrArg succ ih : succ (div2 (k+k)) = succ k.
fn build_div2_two_mul(c: &C) -> (Expr, Expr) {
    let mk_concl = |r: &Expr| c.eq_nat(c.div2(c.add(r.clone(), r.clone())), r.clone());
    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (r_id, r) = b.fresh_local(c.nat.clone());
        let concl = mk_concl(&r);
        let pi = b.mk_pi(r_id, BinderInfo::Default, c.nat.clone(), concl);
        b.finish(pi)
    };

    let mut vb = EnvDeclBuilder::new();
    let (r_id, r) = vb.fresh_local(c.nat.clone());
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&vb);
        let (t_id, t) = mb.fresh_local(c.nat.clone());
        let body = mk_concl(&t);
        let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
        mb.finish_child(lam)
    };
    let base = c.refl_nat(c.zero.clone());
    let step = {
        let mut sb = EnvDeclBuilder::child_of(&vb);
        let (k_id, k) = sb.fresh_local(c.nat.clone());
        let ih_ty = mk_concl(&k);
        let (ih_id, ih) = sb.fresh_local(ih_ty.clone());

        let sk = c.succ(k.clone());
        let kk = c.add(k.clone(), k.clone());
        let succ_kk = c.add(c.succ(k.clone()), k.clone());

        // bridge1 : LHS = div2 (succ (succ (k+k)))
        //   succ_add maps  succ k + k  ↦  succ (k + k).
        let succ_add = Expr::apps(
            Expr::const_(Name::from_string("Nat.succ_add"), vec![]),
            [k.clone(), k.clone()],
        );
        let succ_of_kk = c.succ(kk.clone()); // succ (k + k)
        let f_div2_succ = c.lam_nat_nat(&sb, &|z| c.div2(c.succ(z)));
        let bridge1 = c.congr_nat_nat(succ_kk.clone(), succ_of_kk.clone(), f_div2_succ, succ_add);
        let lhs = c.div2(c.add(sk.clone(), sk.clone()));
        let mid = c.div2(c.succ(c.succ(kk.clone()))); // div2 (succ (succ (k+k)))

        // mid ≡ div2 (succ (k+k)) + div2Par (succ (k+k))
        //     ≡ (div2 (k+k) + div2Par (k+k)) + (1 - div2Par (k+k))
        // Use div2Par_two_mul k : div2Par (k+k) = 0 to rewrite both occurrences.
        // congrArg (fun p => (div2 (k+k) + p) + (1 - p)) (div2Par_two_mul k)
        //   : (div2(k+k)+P)+(1-P) = (div2(k+k)+0)+(1-0)
        // and (div2(k+k)+0)+(1-0) ≡ div2(k+k)+1 ≡ succ(div2(k+k)).
        let d2kk = c.div2(kk.clone());
        let par_kk = c.par(kk.clone());
        let sub = Expr::const_(Name::from_string("Nat.sub"), vec![]);
        let f_rebuild = {
            let mut fb = EnvDeclBuilder::child_of(&sb);
            let (p_id, p) = fb.fresh_local(c.nat.clone());
            let lo = c.add(d2kk.clone(), p.clone());
            let hi = Expr::apps(sub.clone(), [c.one.clone(), p.clone()]);
            let body = c.add(lo, hi);
            let lam = fb.mk_lam(p_id, BinderInfo::Default, c.nat.clone(), body);
            fb.finish_child(lam)
        };
        let par_two_mul = Expr::app(
            Expr::const_(Name::from_string("Nat.div2Par_two_mul"), vec![]),
            k.clone(),
        );
        // step_b : mid = (div2(k+k)+0)+(1-0)   (mid ≡ src defeq; congr to dst)
        let src = {
            let lo = c.add(d2kk.clone(), par_kk.clone());
            let hi = Expr::apps(sub.clone(), [c.one.clone(), par_kk.clone()]);
            c.add(lo, hi)
        };
        let dst = {
            let lo = c.add(d2kk.clone(), c.zero.clone());
            let hi = Expr::apps(sub.clone(), [c.one.clone(), c.zero.clone()]);
            c.add(lo, hi)
        };
        let congr_dst = c.congr_nat_nat(par_kk.clone(), c.zero.clone(), f_rebuild, par_two_mul);
        // congr_dst : src = dst ; src ≡ mid defeq ; dst ≡ succ (div2(k+k)) defeq.
        // step_b : mid = succ (div2 (k+k))   (retype src↦mid, dst↦succ(div2 kk))
        let succ_d2kk = c.succ(d2kk.clone());
        // out_tail : mid = succ k  via Eq.trans (mid = succ(div2 kk)) (congrArg succ ih)
        let congr_succ_ih = c.congr_nat_nat(d2kk.clone(), k.clone(), c.succ.clone(), ih);
        // congr_succ_ih : succ (div2 (k+k)) = succ k
        let mid_to_succd2 = congr_dst; // typed src=dst ≡ mid = succ(div2 kk)
        let _ = (src, dst);
        let mid_to_succk = c.trans_nat(
            mid.clone(),
            succ_d2kk.clone(),
            sk.clone(),
            mid_to_succd2,
            congr_succ_ih,
        );
        // out : LHS = succ k  via Eq.trans bridge1 mid_to_succk
        let out = c.trans_nat(lhs, mid, sk.clone(), bridge1, mid_to_succk);
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, out);
        let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_ih);
        sb.finish_child(lam_k)
    };
    let rec_app = Expr::apps(c.rec0.clone(), [motive, base, step, r]);
    let value = {
        let lam = vb.mk_lam(r_id, BinderInfo::Default, c.nat.clone(), rec_app);
        vb.finish(lam)
    };
    (type_, value)
}

// ===========================================================================
// Lemma 3: Nat.bitNat_hi  (b : Bool)(r : Nat) → div2 ((r+r) + ofBool b) = r
// ===========================================================================
//
// Bool.rec on b (motive : fun b' => div2 ((r+r)+ofBool b') = r).
//   b=false: ofBool false ≡ 0, (r+r)+0 ≡ r+r, div2 (r+r) = r  →  div2_two_mul r.
//   b=true : ofBool true ≡ 1, (r+r)+1 ≡ succ (r+r),
//            div2 (succ (r+r)) ≡ div2 (r+r) + div2Par (r+r)
//            = r + div2Par (r+r)   [congrArg (·+div2Par(r+r)) (div2_two_mul r)]
//            = r + 0               [congrArg (r+·) (div2Par_two_mul r)]
//            ≡ r.
fn build_bit_nat_hi(c: &C) -> (Expr, Expr) {
    let mk_concl =
        |b: &Expr, r: &Expr| c.eq_nat(c.div2(c.bit_nat(b.clone(), r.clone())), r.clone());
    let type_ = {
        let mut bd = EnvDeclBuilder::new();
        let (b_id, b) = bd.fresh_local(c.bool_ty.clone());
        let (r_id, r) = bd.fresh_local(c.nat.clone());
        let concl = mk_concl(&b, &r);
        let pir = bd.mk_pi(r_id, BinderInfo::Default, c.nat.clone(), concl);
        let pib = bd.mk_pi(b_id, BinderInfo::Default, c.bool_ty.clone(), pir);
        bd.finish(pib)
    };
    let value = {
        let mut vb = EnvDeclBuilder::new();
        let (b_id, b) = vb.fresh_local(c.bool_ty.clone());
        let (r_id, r) = vb.fresh_local(c.nat.clone());
        let rr = c.add(r.clone(), r.clone());
        // motive : fun b' => div2 ((r+r)+ofBool b') = r
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&vb);
            let (bp_id, bp) = mb.fresh_local(c.bool_ty.clone());
            let body = mk_concl(&bp, &r);
            let lam = mb.mk_lam(bp_id, BinderInfo::Default, c.bool_ty.clone(), body);
            mb.finish_child(lam)
        };
        // false case: div2 ((r+r)+ofBool false) = r ; LHS ≡ div2 (r+r), so div2_two_mul r.
        let two_mul = Expr::app(
            Expr::const_(Name::from_string("Nat.div2_two_mul"), vec![]),
            r.clone(),
        );
        let false_case = two_mul.clone();
        // true case: div2 ((r+r)+ofBool true) = r
        //   LHS ≡ div2 (succ (r+r)) ≡ div2 (r+r) + div2Par (r+r)
        let par_rr = c.par(rr.clone());
        let d2rr = c.div2(rr.clone());
        // e1 : div2 (r+r) + div2Par (r+r) = r + div2Par (r+r)
        let f_add_par = c.lam_nat_nat(&vb, &|q| c.add(q, par_rr.clone()));
        let e1 = c.congr_nat_nat(d2rr.clone(), r.clone(), f_add_par, two_mul.clone());
        // e2 : r + div2Par (r+r) = r + 0
        let par_two_mul = Expr::app(
            Expr::const_(Name::from_string("Nat.div2Par_two_mul"), vec![]),
            r.clone(),
        );
        let f_r_add = c.lam_nat_nat(&vb, &|p| c.add(r.clone(), p));
        let e2 = c.congr_nat_nat(par_rr.clone(), c.zero.clone(), f_r_add, par_two_mul);
        // true_case : LHS = r  via Eq.trans e1 e2 (LHS ≡ div2(r+r)+div2Par(r+r) defeq;
        //   r + 0 ≡ r defeq).
        let lhs_true = c.add(d2rr.clone(), par_rr.clone()); // ≡ div2 (succ (r+r))
        let r_add_par = c.add(r.clone(), par_rr.clone());
        let r_add_0 = c.add(r.clone(), c.zero.clone());
        let true_case = c.trans_nat(lhs_true, r_add_par, r_add_0, e1, e2);
        // Bool.rec.{0} motive false_case true_case b
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
        let rec_app = Expr::apps(bool_rec, [motive, false_case, true_case, b.clone()]);
        let lam_r = vb.mk_lam(r_id, BinderInfo::Default, c.nat.clone(), rec_app);
        let lam_b = vb.mk_lam(b_id, BinderInfo::Default, c.bool_ty.clone(), lam_r);
        vb.finish(lam_b)
    };
    (type_, value)
}

// ===========================================================================
// Lemma 4: Nat.bitNat_lo  (b : Bool)(r : Nat) → testBit ((r+r)+ofBool b) 0 = b
// ===========================================================================
//
// testBit x 0 ≡ toBoolPar (div2Par x).  Bool.rec on b.
//   b=false: (r+r)+0 ≡ r+r; toBoolPar (div2Par (r+r)) = toBoolPar 0 ≡ false = b
//            via congrArg toBoolPar (div2Par_two_mul r).
//   b=true : (r+r)+1 ≡ succ (r+r); div2Par (succ (r+r)) ≡ 1 - div2Par (r+r);
//            toBoolPar (1 - div2Par (r+r)) = toBoolPar (1 - 0) ≡ toBoolPar 1 ≡ true = b
//            via congrArg (fun p => toBoolPar (1 - p)) (div2Par_two_mul r).
fn build_bit_nat_lo(c: &C) -> (Expr, Expr) {
    let mk_concl =
        |b: &Expr, r: &Expr| c.eq_bool(c.testbit0(c.bit_nat(b.clone(), r.clone())), b.clone());
    let type_ = {
        let mut bd = EnvDeclBuilder::new();
        let (b_id, b) = bd.fresh_local(c.bool_ty.clone());
        let (r_id, r) = bd.fresh_local(c.nat.clone());
        let concl = mk_concl(&b, &r);
        let pir = bd.mk_pi(r_id, BinderInfo::Default, c.nat.clone(), concl);
        let pib = bd.mk_pi(b_id, BinderInfo::Default, c.bool_ty.clone(), pir);
        bd.finish(pib)
    };
    let value = {
        let mut vb = EnvDeclBuilder::new();
        let (b_id, b) = vb.fresh_local(c.bool_ty.clone());
        let (r_id, r) = vb.fresh_local(c.nat.clone());
        let rr = c.add(r.clone(), r.clone());
        let par_rr = c.par(rr.clone());
        let par_two_mul = Expr::app(
            Expr::const_(Name::from_string("Nat.div2Par_two_mul"), vec![]),
            r.clone(),
        );
        // motive : fun b' => testBit ((r+r)+ofBool b') 0 = b'
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&vb);
            let (bp_id, bp) = mb.fresh_local(c.bool_ty.clone());
            let body = mk_concl(&bp, &r);
            let lam = mb.mk_lam(bp_id, BinderInfo::Default, c.bool_ty.clone(), body);
            mb.finish_child(lam)
        };
        // false case: testBit ((r+r)+0) 0 = false
        //   LHS ≡ toBoolPar (div2Par (r+r)); congrArg toBoolPar (div2Par_two_mul r)
        //   : toBoolPar (div2Par (r+r)) = toBoolPar 0 ; toBoolPar 0 ≡ false.
        let false_case = c.congr_nat_bool(
            par_rr.clone(),
            c.zero.clone(),
            c.tobool.clone(),
            par_two_mul.clone(),
        );
        // true case: testBit ((r+r)+1) 0 = true
        //   LHS ≡ toBoolPar (div2Par (succ (r+r))) ≡ toBoolPar (1 - div2Par (r+r))
        //   congrArg (fun p => toBoolPar (1 - p)) (div2Par_two_mul r)
        //   : toBoolPar (1 - div2Par(r+r)) = toBoolPar (1 - 0) ; toBoolPar (1-0) ≡ true.
        let f_tobool_one_sub = {
            let mut fb = EnvDeclBuilder::child_of(&vb);
            let (p_id, p) = fb.fresh_local(c.nat.clone());
            let body = c.tobool(c.sub(c.one.clone(), p));
            let lam = fb.mk_lam(p_id, BinderInfo::Default, c.nat.clone(), body);
            fb.finish_child(lam)
        };
        let true_case = c.congr_nat_bool(
            par_rr.clone(),
            c.zero.clone(),
            f_tobool_one_sub,
            par_two_mul,
        );
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
        let rec_app = Expr::apps(bool_rec, [motive, false_case, true_case, b.clone()]);
        let lam_r = vb.mk_lam(r_id, BinderInfo::Default, c.nat.clone(), rec_app);
        let lam_b = vb.mk_lam(b_id, BinderInfo::Default, c.bool_ty.clone(), lam_r);
        vb.finish(lam_b)
    };
    (type_, value)
}

// ===========================================================================
// Lemma 6: Nat.testBit_bitwiseAux
//   (f : Bool → Bool → Bool) → (k i m n : Nat) → Nat.lt i k →
//      testBit (bitwiseAux f k m n) i = f (testBit m i) (testBit n i)
// ===========================================================================
//
// Induction on the fuel `k` (Nat.rec.{0}), motive
//   Q k := (i m n : Nat) → lt i k → testBit (bitwiseAux f k m n) i
//                                  = f (testBit m i) (testBit n i)
//  k=0:  lt i 0 ≡ le (succ i) 0 absurd → False.elim ∘ not_succ_le_zero.
//  k=succ k': inner Nat.rec on `i` (constructor exposure) with motive
//    Mi t := (m n : Nat) → lt t (succ k') → testBit (bitwiseAux f (succ k') m n) t
//                                          = f (testBit m t) (testBit n t)
//    i=0:  bitwiseAux f (succ k') m n ≡ (r+r)+ofBool b  (r = bitwiseAux f k' (div2 m)(div2 n),
//          b = f (testBit m 0)(testBit n 0)); bitNat_lo b r : testBit … 0 = b.
//    i=succ j: testBit (bitwiseAux f (succ k') m n)(succ j)
//          ≡ testBit (div2 (bitwiseAux f (succ k') m n)) j
//          = testBit r j                       [congrArg (testBit · j) (bitNat_hi b r)]
//          = f (testBit (div2 m) j)(testBit (div2 n) j)   [IH at k', lt j k']
//          ≡ f (testBit m (succ j))(testBit n (succ j)).
fn build_testbit_bitwise_aux(c: &C) -> (Expr, Expr) {
    let bool_to_bool_to_bool = Expr::pi(
        BinderInfo::Default,
        c.bool_ty.clone(),
        Expr::pi(BinderInfo::Default, c.bool_ty.clone(), c.bool_ty.clone()),
    );
    let aux = Expr::const_(Name::from_string("Nat.bitwiseAux"), vec![]);
    let testbit = c.testbit.clone();
    // helpers parameterized by f (a parent fvar)
    let mk_testbit = |x: Expr, i: Expr| Expr::apps(testbit.clone(), [x, i]);

    // type: (f) → (k i m n) → lt i k → testBit (bitwiseAux f k m n) i = f (testBit m i)(testBit n i)
    let mut tb = EnvDeclBuilder::new();
    let (f_id, f) = tb.fresh_local(bool_to_bool_to_bool.clone());
    let bw = |k: Expr, m: Expr, n: Expr| Expr::apps(aux.clone(), [f.clone(), k, m, n]);
    let fapp = |a: Expr, b: Expr| Expr::apps(f.clone(), [a, b]);
    let lt =
        |a: Expr, b: Expr| Expr::apps(Expr::const_(Name::from_string("Nat.lt"), vec![]), [a, b]);
    // concl(k,i,m,n)
    let concl = |k: &Expr, i: &Expr, m: &Expr, n: &Expr| {
        c.eq_bool(
            mk_testbit(bw(k.clone(), m.clone(), n.clone()), i.clone()),
            fapp(
                mk_testbit(m.clone(), i.clone()),
                mk_testbit(n.clone(), i.clone()),
            ),
        )
    };
    let type_ = {
        let (k_id, k) = tb.fresh_local(c.nat.clone());
        let (i_id, i) = tb.fresh_local(c.nat.clone());
        let (m_id, m) = tb.fresh_local(c.nat.clone());
        let (n_id, n) = tb.fresh_local(c.nat.clone());
        let h_ty = lt(i.clone(), k.clone());
        let (h_id, _h) = tb.fresh_local(h_ty.clone());
        let body = concl(&k, &i, &m, &n);
        let imp = tb.mk_pi(h_id, BinderInfo::Default, h_ty, body);
        let pn = tb.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), imp);
        let pm = tb.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), pn);
        let pi = tb.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), pm);
        let pk = tb.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), pi);
        let pf = tb.mk_pi(f_id, BinderInfo::Default, bool_to_bool_to_bool.clone(), pk);
        tb.finish(pf)
    };

    // value: fun f => Nat.rec.{0} Q base step  applied per k via outer lam
    let mut vb = EnvDeclBuilder::new();
    let (f_id, f) = vb.fresh_local(bool_to_bool_to_bool.clone());
    let bw = |k: Expr, m: Expr, n: Expr| Expr::apps(aux.clone(), [f.clone(), k, m, n]);
    let fapp = |a: Expr, b: Expr| Expr::apps(f.clone(), [a, b]);
    let lt =
        |a: Expr, b: Expr| Expr::apps(Expr::const_(Name::from_string("Nat.lt"), vec![]), [a, b]);
    let concl = |k: &Expr, i: &Expr, m: &Expr, n: &Expr| {
        c.eq_bool(
            mk_testbit(bw(k.clone(), m.clone(), n.clone()), i.clone()),
            fapp(
                mk_testbit(m.clone(), i.clone()),
                mk_testbit(n.clone(), i.clone()),
            ),
        )
    };

    // Q k := (i m n) → lt i k → concl(k,i,m,n)
    let q_of = |k: &Expr, parent: &EnvDeclBuilder| -> Expr {
        let mut qb = EnvDeclBuilder::child_of(parent);
        let (i_id, i) = qb.fresh_local(c.nat.clone());
        let (m_id, m) = qb.fresh_local(c.nat.clone());
        let (n_id, n) = qb.fresh_local(c.nat.clone());
        let h_ty = lt(i.clone(), k.clone());
        let (h_id, _h) = qb.fresh_local(h_ty.clone());
        let body = concl(k, &i, &m, &n);
        let imp = qb.mk_pi(h_id, BinderInfo::Default, h_ty, body);
        let pn = qb.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), imp);
        let pm = qb.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), pn);
        let pi = qb.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), pm);
        qb.finish_child(pi)
    };

    // motive : fun k => Q k
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&vb);
        let (k_id, k) = mb.fresh_local(c.nat.clone());
        let body = q_of(&k, &mb);
        let lam = mb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body);
        mb.finish_child(lam)
    };

    // base : Q 0 = (i m n) → lt i 0 → concl(0,...)
    //   fun i m n (h : lt i 0 ≡ le (succ i) 0) => False.elim (not_succ_le_zero i h)
    let base = {
        let mut bb = EnvDeclBuilder::child_of(&vb);
        let (i_id, i) = bb.fresh_local(c.nat.clone());
        let (m_id, m) = bb.fresh_local(c.nat.clone());
        let (n_id, n) = bb.fresh_local(c.nat.clone());
        let h_ty = lt(i.clone(), c.zero.clone());
        let (h_id, h) = bb.fresh_local(h_ty.clone());
        // not_succ_le_zero i h : False  (h : le (succ i) 0 ≡ lt i 0)
        let nslz = Expr::apps(
            Expr::const_(Name::from_string("Nat.not_succ_le_zero"), vec![]),
            [i.clone(), h.clone()],
        );
        let target = concl(&c.zero, &i, &m, &n);
        let false_elim = Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);
        let body = Expr::apps(false_elim, [target, nslz]);
        let lam = bb.mk_lam(h_id, BinderInfo::Default, h_ty, body);
        let lam = bb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
        let lam = bb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam);
        let lam = bb.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), lam);
        bb.finish_child(lam)
    };

    // step : (k') → Q k' → Q (succ k')
    let step = {
        let mut sb = EnvDeclBuilder::child_of(&vb);
        let (kp_id, kp) = sb.fresh_local(c.nat.clone());
        let q_kp = q_of(&kp, &sb);
        let (ih_id, ih) = sb.fresh_local(q_kp.clone());
        let skp = c.succ(kp.clone());

        // We must produce Q (succ k') = (i m n) → lt i (succ k') → concl(succ k', i, m, n).
        // Inner Nat.rec on i with motive
        //   Mi t := (m n) → lt t (succ k') → concl(succ k', t, m, n)
        let mi_of = |t: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut qb = EnvDeclBuilder::child_of(parent);
            let (m_id, m) = qb.fresh_local(c.nat.clone());
            let (n_id, n) = qb.fresh_local(c.nat.clone());
            let h_ty = lt(t.clone(), skp.clone());
            let (h_id, _h) = qb.fresh_local(h_ty.clone());
            let body = concl(&skp, t, &m, &n);
            let imp = qb.mk_pi(h_id, BinderInfo::Default, h_ty, body);
            let pn = qb.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), imp);
            let pm = qb.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), pn);
            qb.finish_child(pm)
        };
        let mi_motive = {
            let mut mb = EnvDeclBuilder::child_of(&sb);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let body = mi_of(&t, &mb);
            let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
            mb.finish_child(lam)
        };

        // i=0 base: Mi 0 = (m n) → lt 0 (succ k') → concl(succ k', 0, m, n)
        //   fun m n _h => bitNat_lo (f (testBit m 0)(testBit n 0)) (bitwiseAux f k' (div2 m)(div2 n))
        let i0_base = {
            let mut bb = EnvDeclBuilder::child_of(&sb);
            let (m_id, m) = bb.fresh_local(c.nat.clone());
            let (n_id, n) = bb.fresh_local(c.nat.clone());
            let h_ty = lt(c.zero.clone(), skp.clone());
            let (h_id, _h) = bb.fresh_local(h_ty.clone());
            // b := f (testBit m 0)(testBit n 0)
            let bbit = fapp(
                mk_testbit(m.clone(), c.zero.clone()),
                mk_testbit(n.clone(), c.zero.clone()),
            );
            // r := bitwiseAux f k' (div2 m)(div2 n)
            let r = bw(kp.clone(), c.div2(m.clone()), c.div2(n.clone()));
            // bitNat_lo b r : testBit ((r+r)+ofBool b) 0 = b
            let blo = Expr::apps(
                Expr::const_(Name::from_string("Nat.bitNat_lo"), vec![]),
                [bbit.clone(), r.clone()],
            );
            // concl(succ k', 0, m, n) LHS ≡ testBit (bitwiseAux f (succ k') m n) 0
            //   ≡ testBit ((r+r)+ofBool b) 0 (defeq via bitwiseAux step) ; RHS ≡ b. So blo fits.
            let lam = bb.mk_lam(h_id, BinderInfo::Default, h_ty, blo);
            let lam = bb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = bb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam);
            bb.finish_child(lam)
        };

        // i=succ j step: (j) → Mi j → Mi (succ j)
        //   fun j _ihMi => fun m n (h : lt (succ j)(succ k')) =>
        //     <concl(succ k', succ j, m, n)>
        let i_step = {
            let mut ib = EnvDeclBuilder::child_of(&sb);
            let (j_id, j) = ib.fresh_local(c.nat.clone());
            let mi_j = mi_of(&j, &ib);
            let (ihmi_id, _ihmi) = ib.fresh_local(mi_j.clone());
            let (m_id, m) = ib.fresh_local(c.nat.clone());
            let (n_id, n) = ib.fresh_local(c.nat.clone());
            let sj = c.succ(j.clone());
            let h_ty = lt(sj.clone(), skp.clone());
            let (h_id, h) = ib.fresh_local(h_ty.clone());

            // b, r as before
            let bbit = fapp(
                mk_testbit(m.clone(), c.zero.clone()),
                mk_testbit(n.clone(), c.zero.clone()),
            );
            let r = bw(kp.clone(), c.div2(m.clone()), c.div2(n.clone()));
            // bitNat_hi b r : div2 ((r+r)+ofBool b) = r
            let bhi = Expr::apps(
                Expr::const_(Name::from_string("Nat.bitNat_hi"), vec![]),
                [bbit.clone(), r.clone()],
            );
            // The full bitwise term and its div2:
            let full = bw(skp.clone(), m.clone(), n.clone()); // bitwiseAux f (succ k') m n
                                                              // div2_full ≡ (r+r)+ofBool b 's div2 — we express via bit_nat
            let bit_term = c.bit_nat(bbit.clone(), r.clone()); // (r+r)+ofBool b ; full ≡ bit_term defeq
                                                               // step1 : testBit full (succ j) = testBit (div2 full) j  (rfl: testBit x (succ j) ≡ testBit (div2 x) j)
                                                               //   We don't need an explicit Eq for the rfl; we work with goal LHS =
                                                               //   testBit full (succ j) and use that it is defeq to testBit (div2 bit_term) j.
                                                               // congrArg (fun x => testBit x j) bhi : testBit (div2 bit_term) j = testBit r j
            let f_testbit_j = {
                let mut fb = EnvDeclBuilder::child_of(&ib);
                let (x_id, x) = fb.fresh_local(c.nat.clone());
                let body = mk_testbit(x, j.clone());
                let lam = fb.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), body);
                fb.finish_child(lam)
            };
            let div2_bit = c.div2(bit_term.clone());
            let e_div2 = c.congr_nat_bool(div2_bit.clone(), r.clone(), f_testbit_j, bhi);
            // e_div2 : testBit (div2 bit_term) j = testBit r j
            // IH at k': ih (div2 m) (div2 n) — wait ih has type Q k' = (i m n) → lt i k' → …
            //   We instantiate ih j (div2 m)(div2 n) (hlt : lt j k').
            // hlt : lt j k' = le (succ j) k'  from h : lt (succ j)(succ k') = le (succ(succ j))(succ k')
            //   le_of_succ_le_succ (succ j) k' h : le (succ j) k' ≡ lt j k'
            let hlt = Expr::apps(
                Expr::const_(Name::from_string("Nat.le_of_succ_le_succ"), vec![]),
                [sj.clone(), kp.clone(), h.clone()],
            );
            // ih_app : testBit (bitwiseAux f k' (div2 m)(div2 n)) j
            //            = f (testBit (div2 m) j)(testBit (div2 n) j)
            let ih_app = Expr::apps(
                ih.clone(),
                [j.clone(), c.div2(m.clone()), c.div2(n.clone()), hlt],
            );
            // ih_app's LHS is testBit r j (r = bitwiseAux f k' (div2 m)(div2 n)).
            // RHS ≡ f (testBit m (succ j))(testBit n (succ j))  (defeq: testBit x (succ j) ≡ testBit (div2 x) j)
            //   which is exactly concl's RHS f (testBit m (succ j))(testBit n (succ j)).
            // Compose: goal LHS = testBit full (succ j) ≡ testBit (div2 bit_term) j  (defeq)
            //   e_div2 : that = testBit r j
            //   ih_app : testBit r j = f (testBit (div2 m) j)(testBit (div2 n) j)
            //   final RHS ≡ f (testBit m (succ j))(testBit n (succ j)) (defeq)
            let testbit_div2bit_j = mk_testbit(div2_bit.clone(), j.clone());
            let testbit_r_j = mk_testbit(r.clone(), j.clone());
            let rhs_f = fapp(
                mk_testbit(c.div2(m.clone()), j.clone()),
                mk_testbit(c.div2(n.clone()), j.clone()),
            );
            // out : testBit (div2 bit_term) j = rhs_f  via Eq.trans e_div2 ih_app
            let out = c.trans_bool(testbit_div2bit_j, testbit_r_j, rhs_f, e_div2, ih_app);
            // out has type `testBit (div2 bit_term) j = f (testBit (div2 m) j)(testBit (div2 n) j)`,
            // which is defeq to concl(succ k', succ j, m, n):
            //   LHS testBit full (succ j) ≡ testBit (div2 full) j ≡ testBit (div2 bit_term) j;
            //   RHS f (testBit m (succ j))(testBit n (succ j)) ≡ f (testBit (div2 m) j)(testBit (div2 n) j).
            let _ = full;
            let lam = ib.mk_lam(h_id, BinderInfo::Default, h_ty, out);
            let lam = ib.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = ib.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = ib.mk_lam(ihmi_id, BinderInfo::Default, mi_j, lam);
            let lam = ib.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), lam);
            ib.finish_child(lam)
        };

        // Build the per-i function: fun (i : Nat) => Nat.rec.{0} Mi i0_base i_step i : Mi i
        // Then Q (succ k') = (i m n) → … = (i) → Mi i, so we lam over i and apply rec.
        let (i_id, i) = sb.fresh_local(c.nat.clone());
        let rec_i = Expr::apps(c.rec0.clone(), [mi_motive, i0_base, i_step, i.clone()]);
        // rec_i : Mi i = (m n) → lt i (succ k') → concl(succ k', i, m, n)
        let lam_i = sb.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), rec_i);
        // lam_i : (i) → Mi i ≡ Q (succ k')
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, q_kp, lam_i);
        let lam_kp = sb.mk_lam(kp_id, BinderInfo::Default, c.nat.clone(), lam_ih);
        sb.finish_child(lam_kp)
    };

    // value: fun f => fun k => Nat.rec.{0} motive base step k  (applied to k)
    // But Q is per-k; the recursor produces Q k = (i m n) → lt i k → concl. So
    // value f = fun k i m n h => (Nat.rec motive base step k) i m n h.
    let (k_id, k) = vb.fresh_local(c.nat.clone());
    let (i_id, i) = vb.fresh_local(c.nat.clone());
    let (m_id, m) = vb.fresh_local(c.nat.clone());
    let (n_id, n) = vb.fresh_local(c.nat.clone());
    let h_ty = lt(i.clone(), k.clone());
    let (h_id, h) = vb.fresh_local(h_ty.clone());
    let rec_k = Expr::apps(c.rec0.clone(), [motive, base, step, k.clone()]);
    let applied = Expr::apps(rec_k, [i.clone(), m.clone(), n.clone(), h.clone()]);
    let lam = vb.mk_lam(h_id, BinderInfo::Default, h_ty, applied);
    let lam = vb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
    let lam = vb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam);
    let lam = vb.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), lam);
    let lam = vb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam);
    let lam = vb.mk_lam(f_id, BinderInfo::Default, bool_to_bool_to_bool.clone(), lam);
    let value = vb.finish(lam);
    (type_, value)
}

// ===========================================================================
// Lemma 7: Nat.testBit_bitwiseAux_high
//   (f) → (k i m n) → Nat.le k i → testBit (bitwiseAux f k m n) i = false
// ===========================================================================
//
// Induction on k.  k=0: bitwiseAux f 0 m n ≡ 0; testBit 0 i = false
//   (Nat.testBit_zero_eq_false). k=succ k': from le (succ k') i, i = succ j with
//   le k' j; testBit (bitwiseAux f (succ k') m n)(succ j) ≡ testBit (div2 …) j
//   = testBit r j  [bitNat_hi] = false  [IH at k', le k' j]. The inner Nat.rec on
//   i discharges i=0 by `not_succ_le_zero` (le (succ k') 0 is absurd).
fn build_testbit_bitwise_aux_high(c: &C) -> (Expr, Expr) {
    let bool_to_bool_to_bool = Expr::pi(
        BinderInfo::Default,
        c.bool_ty.clone(),
        Expr::pi(BinderInfo::Default, c.bool_ty.clone(), c.bool_ty.clone()),
    );
    let aux = Expr::const_(Name::from_string("Nat.bitwiseAux"), vec![]);
    let testbit = c.testbit.clone();
    let mk_testbit = |x: Expr, i: Expr| Expr::apps(testbit.clone(), [x, i]);
    let le =
        |a: Expr, b: Expr| Expr::apps(Expr::const_(Name::from_string("Nat.le"), vec![]), [a, b]);

    // type
    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (f_id, f) = b.fresh_local(bool_to_bool_to_bool.clone());
        let bw = |k: Expr, m: Expr, n: Expr| Expr::apps(aux.clone(), [f.clone(), k, m, n]);
        let (k_id, k) = b.fresh_local(c.nat.clone());
        let (i_id, i) = b.fresh_local(c.nat.clone());
        let (m_id, m) = b.fresh_local(c.nat.clone());
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let h_ty = le(k.clone(), i.clone());
        let (h_id, _h) = b.fresh_local(h_ty.clone());
        let body = c.eq_bool(
            mk_testbit(bw(k.clone(), m.clone(), n.clone()), i.clone()),
            c.bfalse.clone(),
        );
        let imp = b.mk_pi(h_id, BinderInfo::Default, h_ty, body);
        let pn = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), imp);
        let pm = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), pn);
        let pii = b.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), pm);
        let pk = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), pii);
        let pf = b.mk_pi(f_id, BinderInfo::Default, bool_to_bool_to_bool.clone(), pk);
        b.finish(pf)
    };

    // value
    let mut vb = EnvDeclBuilder::new();
    let (f_id, f) = vb.fresh_local(bool_to_bool_to_bool.clone());
    let bw = |k: Expr, m: Expr, n: Expr| Expr::apps(aux.clone(), [f.clone(), k, m, n]);
    let fapp = |a: Expr, b: Expr| Expr::apps(f.clone(), [a, b]);
    let concl = |k: &Expr, i: &Expr, m: &Expr, n: &Expr| {
        c.eq_bool(
            mk_testbit(bw(k.clone(), m.clone(), n.clone()), i.clone()),
            c.bfalse.clone(),
        )
    };

    // Q k := (i m n) → le k i → concl(k,i,m,n)
    let q_of = |k: &Expr, parent: &EnvDeclBuilder| -> Expr {
        let mut qb = EnvDeclBuilder::child_of(parent);
        let (i_id, i) = qb.fresh_local(c.nat.clone());
        let (m_id, m) = qb.fresh_local(c.nat.clone());
        let (n_id, n) = qb.fresh_local(c.nat.clone());
        let h_ty = le(k.clone(), i.clone());
        let (h_id, _h) = qb.fresh_local(h_ty.clone());
        let body = concl(k, &i, &m, &n);
        let imp = qb.mk_pi(h_id, BinderInfo::Default, h_ty, body);
        let pn = qb.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), imp);
        let pm = qb.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), pn);
        let pi = qb.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), pm);
        qb.finish_child(pi)
    };

    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&vb);
        let (k_id, k) = mb.fresh_local(c.nat.clone());
        let body = q_of(&k, &mb);
        let lam = mb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body);
        mb.finish_child(lam)
    };

    // base : Q 0 = (i m n) → le 0 i → testBit (bitwiseAux f 0 m n) i = false
    //   bitwiseAux f 0 m n ≡ 0; fun i m n _h => testBit_zero_eq_false i
    let base = {
        let mut bb = EnvDeclBuilder::child_of(&vb);
        let (i_id, i) = bb.fresh_local(c.nat.clone());
        let (m_id, _m) = bb.fresh_local(c.nat.clone());
        let (n_id, _n) = bb.fresh_local(c.nat.clone());
        let h_ty = le(c.zero.clone(), i.clone());
        let (h_id, _h) = bb.fresh_local(h_ty.clone());
        // testBit_zero_eq_false i : testBit 0 i = false ; concl LHS ≡ testBit 0 i.
        let tzf = Expr::app(
            Expr::const_(Name::from_string("Nat.testBit_zero_eq_false"), vec![]),
            i.clone(),
        );
        let lam = bb.mk_lam(h_id, BinderInfo::Default, h_ty, tzf);
        let lam = bb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
        let lam = bb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam);
        let lam = bb.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), lam);
        bb.finish_child(lam)
    };

    // step : (k') → Q k' → Q (succ k')
    let step = {
        let mut sb = EnvDeclBuilder::child_of(&vb);
        let (kp_id, kp) = sb.fresh_local(c.nat.clone());
        let q_kp = q_of(&kp, &sb);
        let (ih_id, ih) = sb.fresh_local(q_kp.clone());
        let skp = c.succ(kp.clone());

        // Mi t := (m n) → le (succ k') t → concl(succ k', t, m, n)
        let mi_of = |t: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut qb = EnvDeclBuilder::child_of(parent);
            let (m_id, m) = qb.fresh_local(c.nat.clone());
            let (n_id, n) = qb.fresh_local(c.nat.clone());
            let h_ty = le(skp.clone(), t.clone());
            let (h_id, _h) = qb.fresh_local(h_ty.clone());
            let body = concl(&skp, t, &m, &n);
            let imp = qb.mk_pi(h_id, BinderInfo::Default, h_ty, body);
            let pn = qb.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), imp);
            let pm = qb.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), pn);
            qb.finish_child(pm)
        };
        let mi_motive = {
            let mut mb = EnvDeclBuilder::child_of(&sb);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let body = mi_of(&t, &mb);
            let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
            mb.finish_child(lam)
        };

        // i=0 base: Mi 0 = (m n) → le (succ k') 0 → … ; le (succ k') 0 absurd.
        let i0_base = {
            let mut bb = EnvDeclBuilder::child_of(&sb);
            let (m_id, m) = bb.fresh_local(c.nat.clone());
            let (n_id, n) = bb.fresh_local(c.nat.clone());
            let h_ty = le(skp.clone(), c.zero.clone());
            let (h_id, h) = bb.fresh_local(h_ty.clone());
            let nslz = Expr::apps(
                Expr::const_(Name::from_string("Nat.not_succ_le_zero"), vec![]),
                [kp.clone(), h.clone()],
            );
            let target = concl(&skp, &c.zero, &m, &n);
            let false_elim = Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);
            let body = Expr::apps(false_elim, [target, nslz]);
            let lam = bb.mk_lam(h_id, BinderInfo::Default, h_ty, body);
            let lam = bb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = bb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam);
            bb.finish_child(lam)
        };

        // i=succ j step: (j) → Mi j → Mi (succ j)
        let i_step = {
            let mut ib = EnvDeclBuilder::child_of(&sb);
            let (j_id, j) = ib.fresh_local(c.nat.clone());
            let mi_j = mi_of(&j, &ib);
            let (ihmi_id, _ihmi) = ib.fresh_local(mi_j.clone());
            let (m_id, m) = ib.fresh_local(c.nat.clone());
            let (n_id, n) = ib.fresh_local(c.nat.clone());
            let sj = c.succ(j.clone());
            let h_ty = le(skp.clone(), sj.clone());
            let (h_id, h) = ib.fresh_local(h_ty.clone());

            let bbit = fapp(
                mk_testbit(m.clone(), c.zero.clone()),
                mk_testbit(n.clone(), c.zero.clone()),
            );
            let r = bw(kp.clone(), c.div2(m.clone()), c.div2(n.clone()));
            let bhi = Expr::apps(
                Expr::const_(Name::from_string("Nat.bitNat_hi"), vec![]),
                [bbit.clone(), r.clone()],
            );
            let bit_term = c.bit_nat(bbit.clone(), r.clone());
            // congrArg (fun x => testBit x j) bhi : testBit (div2 bit_term) j = testBit r j
            let f_testbit_j = {
                let mut fb = EnvDeclBuilder::child_of(&ib);
                let (x_id, x) = fb.fresh_local(c.nat.clone());
                let body = mk_testbit(x, j.clone());
                let lam = fb.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), body);
                fb.finish_child(lam)
            };
            let div2_bit = c.div2(bit_term.clone());
            let e_div2 = c.congr_nat_bool(div2_bit.clone(), r.clone(), f_testbit_j, bhi);
            // hle' : le k' j  from h : le (succ k')(succ j)  via le_of_succ_le_succ k' j h
            let hle = Expr::apps(
                Expr::const_(Name::from_string("Nat.le_of_succ_le_succ"), vec![]),
                [kp.clone(), j.clone(), h.clone()],
            );
            // ih j (div2 m)(div2 n) hle : testBit r j = false
            let ih_app = Expr::apps(
                ih.clone(),
                [j.clone(), c.div2(m.clone()), c.div2(n.clone()), hle],
            );
            // out : testBit (div2 bit_term) j = false  via Eq.trans e_div2 ih_app
            let testbit_div2bit_j = mk_testbit(div2_bit.clone(), j.clone());
            let testbit_r_j = mk_testbit(r.clone(), j.clone());
            let out = c.trans_bool(
                testbit_div2bit_j,
                testbit_r_j,
                c.bfalse.clone(),
                e_div2,
                ih_app,
            );
            // concl(succ k', succ j, m, n) LHS ≡ testBit (bitwiseAux f (succ k') m n)(succ j)
            //   ≡ testBit (div2 bit_term) j (defeq). RHS = false. out fits.
            let lam = ib.mk_lam(h_id, BinderInfo::Default, h_ty, out);
            let lam = ib.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = ib.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = ib.mk_lam(ihmi_id, BinderInfo::Default, mi_j, lam);
            let lam = ib.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), lam);
            ib.finish_child(lam)
        };

        let (i_id, i) = sb.fresh_local(c.nat.clone());
        let rec_i = Expr::apps(c.rec0.clone(), [mi_motive, i0_base, i_step, i.clone()]);
        let lam_i = sb.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), rec_i);
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, q_kp, lam_i);
        let lam_kp = sb.mk_lam(kp_id, BinderInfo::Default, c.nat.clone(), lam_ih);
        sb.finish_child(lam_kp)
    };

    let (k_id, k) = vb.fresh_local(c.nat.clone());
    let (i_id, i) = vb.fresh_local(c.nat.clone());
    let (m_id, m) = vb.fresh_local(c.nat.clone());
    let (n_id, n) = vb.fresh_local(c.nat.clone());
    let h_ty = le(k.clone(), i.clone());
    let (h_id, h) = vb.fresh_local(h_ty.clone());
    let rec_k = Expr::apps(c.rec0.clone(), [motive, base, step, k.clone()]);
    let applied = Expr::apps(rec_k, [i.clone(), m.clone(), n.clone(), h.clone()]);
    let lam = vb.mk_lam(h_id, BinderInfo::Default, h_ty, applied);
    let lam = vb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
    let lam = vb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam);
    let lam = vb.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), lam);
    let lam = vb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam);
    let lam = vb.mk_lam(f_id, BinderInfo::Default, bool_to_bool_to_bool.clone(), lam);
    let value = vb.finish(lam);
    (type_, value)
}

// ===========================================================================
// Lemma 5: Nat.testBit_eq_false_of_ge  (x i : Nat) → Nat.le x i → testBit x i = false
// ===========================================================================
//
// Strong induction on x via Acc.rec over Nat.accNatLt.  Predicate
//   P x := (i : Nat) → le x i → testBit x i = false.
// Inner Nat.rec exposes x's constructor (motive Mx t := (∀ y, lt y t → P y) → P t):
//   x=0:  testBit 0 i = false  (testBit_zero_eq_false).
//   x=succ x': given i, h : le (succ x') i. Inner Nat.rec on i:
//       i=0: le (succ x') 0 absurd → not_succ_le_zero.
//       i=succ j: testBit (succ x')(succ j) ≡ testBit (div2 (succ x')) j.
//         div2 (succ x') ≡ div2 x' + div2Par x' ≤ x'   [div2_add_par_le x']
//         x' ≤ j                                        [le_of_succ_le_succ x' j h]
//         ⇒ le (div2 (succ x')) j  [le_trans].  Strong IH at div2 (succ x') <
//         succ x'  (div2_lt_self (succ x') (zero_lt_succ x')) gives
//         testBit (div2 (succ x')) j = false.
fn build_testbit_eq_false_of_ge(c: &C) -> (Expr, Expr) {
    let testbit = c.testbit.clone();
    let mk_testbit = |x: Expr, i: Expr| Expr::apps(testbit.clone(), [x, i]);
    let le =
        |a: Expr, b: Expr| Expr::apps(Expr::const_(Name::from_string("Nat.le"), vec![]), [a, b]);
    let lt =
        |a: Expr, b: Expr| Expr::apps(Expr::const_(Name::from_string("Nat.lt"), vec![]), [a, b]);
    let acc1 = Expr::const_(Name::from_string("Acc"), vec![Level::succ(Level::zero())]);
    let nat_lt_const = Expr::const_(Name::from_string("Nat.lt"), vec![]);
    let acc_lt = |x: Expr| Expr::apps(acc1.clone(), [c.nat.clone(), nat_lt_const.clone(), x]);

    // P t := (i) → le t i → testBit t i = false
    let p_of = |t: &Expr, parent: &EnvDeclBuilder| -> Expr {
        let mut pb = EnvDeclBuilder::child_of(parent);
        let (i_id, i) = pb.fresh_local(c.nat.clone());
        let h_ty = le(t.clone(), i.clone());
        let (h_id, _h) = pb.fresh_local(h_ty.clone());
        let body = c.eq_bool(mk_testbit(t.clone(), i.clone()), c.bfalse.clone());
        let imp = pb.mk_pi(h_id, BinderInfo::Default, h_ty, body);
        let pi = pb.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), imp);
        pb.finish_child(pi)
    };

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(c.nat.clone());
        let concl = p_of(&x, &b);
        let pi = b.mk_pi(x_id, BinderInfo::Default, c.nat.clone(), concl);
        b.finish(pi)
    };

    // helper: ∀ y, lt y bound → P y
    let ih_quant = |bound: &Expr, parent: &EnvDeclBuilder| -> Expr {
        let mut ib = EnvDeclBuilder::child_of(parent);
        let (y_id, y) = ib.fresh_local(c.nat.clone());
        let lt_yb = lt(y.clone(), bound.clone());
        let (l_id, _l) = ib.fresh_local(lt_yb.clone());
        let py = p_of(&y, &ib);
        let imp = ib.mk_pi(l_id, BinderInfo::Default, lt_yb, py);
        let pi = ib.mk_pi(y_id, BinderInfo::Default, c.nat.clone(), imp);
        ib.finish_child(pi)
    };

    let value = {
        let mut vb = EnvDeclBuilder::new();
        let (x0_id, x0) = vb.fresh_local(c.nat.clone());

        // accMotive : fun (x : Nat) (_ : Acc lt x) => P x
        let acc_motive = {
            let mut mb = EnvDeclBuilder::child_of(&vb);
            let (x_id, x) = mb.fresh_local(c.nat.clone());
            let acc_x = acc_lt(x.clone());
            let (a_id, _a) = mb.fresh_local(acc_x.clone());
            let body = p_of(&x, &mb);
            let lam = mb.mk_lam(a_id, BinderInfo::Default, acc_x, body);
            let lam = mb.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), lam);
            mb.finish_child(lam)
        };

        // F : (x) → (hacc) → (ihx : ∀ y, lt y x → P y) → P x
        let f_step = {
            let mut fb = EnvDeclBuilder::child_of(&vb);
            let (x_id, x) = fb.fresh_local(c.nat.clone());

            let hacc_ty = {
                let mut hb = EnvDeclBuilder::child_of(&fb);
                let (y_id, y) = hb.fresh_local(c.nat.clone());
                let lt_yx = lt(y.clone(), x.clone());
                let (l_id, _l) = hb.fresh_local(lt_yx.clone());
                let acc_y = acc_lt(y.clone());
                let imp = hb.mk_pi(l_id, BinderInfo::Default, lt_yx, acc_y);
                let pi = hb.mk_pi(y_id, BinderInfo::Default, c.nat.clone(), imp);
                hb.finish_child(pi)
            };
            let (hacc_id, _hacc) = fb.fresh_local(hacc_ty.clone());

            let ihx_ty = ih_quant(&x, &fb);
            let (ihx_id, ihx) = fb.fresh_local(ihx_ty.clone());

            // Mx t := (∀y, lt y t → P y) → P t
            let mx = {
                let mut mb = EnvDeclBuilder::child_of(&fb);
                let (t_id, t) = mb.fresh_local(c.nat.clone());
                let ih_t = ih_quant(&t, &mb);
                let p_t = p_of(&t, &mb);
                let body = {
                    let mut bb = EnvDeclBuilder::child_of(&mb);
                    let (u_id, _u) = bb.fresh_local(ih_t.clone());
                    let e = bb.mk_pi(u_id, BinderInfo::Default, ih_t.clone(), p_t.clone());
                    bb.finish_child(e)
                };
                let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
                mb.finish_child(lam)
            };

            // base : Mx 0 = (∀y, lt y 0 → P y) → (i) → le 0 i → testBit 0 i = false
            //   fun _ihz i _h => testBit_zero_eq_false i
            let base = {
                let mut bb = EnvDeclBuilder::child_of(&fb);
                let ihz_ty = ih_quant(&c.zero, &bb);
                let (ihz_id, _ihz) = bb.fresh_local(ihz_ty.clone());
                let (i_id, i) = bb.fresh_local(c.nat.clone());
                let h_ty = le(c.zero.clone(), i.clone());
                let (h_id, _h) = bb.fresh_local(h_ty.clone());
                let tzf = Expr::app(
                    Expr::const_(Name::from_string("Nat.testBit_zero_eq_false"), vec![]),
                    i.clone(),
                );
                let lam = bb.mk_lam(h_id, BinderInfo::Default, h_ty, tzf);
                let lam = bb.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), lam);
                let lam = bb.mk_lam(ihz_id, BinderInfo::Default, ihz_ty, lam);
                bb.finish_child(lam)
            };

            // step : (x') → Mx x' → Mx (succ x')
            //   fun x' _ihnat (ihk : ∀y, lt y (succ x') → P y) =>
            //     fun (i) (h : le (succ x') i) => <inner Nat.rec on i>
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&fb);
                let (xp_id, xp) = sb.fresh_local(c.nat.clone());
                let s = c.succ(xp.clone());
                let mx_xp = {
                    let mb = EnvDeclBuilder::child_of(&sb);
                    let ih_xp = ih_quant(&xp, &mb);
                    let p_xp = p_of(&xp, &mb);
                    let mut bb = EnvDeclBuilder::child_of(&mb);
                    let (u_id, _u) = bb.fresh_local(ih_xp.clone());
                    let e = bb.mk_pi(u_id, BinderInfo::Default, ih_xp.clone(), p_xp.clone());
                    bb.finish_child(e)
                };
                let (ihnat_id, _ihnat) = sb.fresh_local(mx_xp.clone());

                let ihk_ty = ih_quant(&s, &sb);
                let (ihk_id, ihk) = sb.fresh_local(ihk_ty.clone());

                // Now build P (succ x') = (i) → le (succ x') i → testBit (succ x') i = false
                //   via inner Nat.rec on i:  Ni t := le (succ x') t → testBit (succ x') t = false
                let ni_of = |t: &Expr, parent: &EnvDeclBuilder| -> Expr {
                    let mut qb = EnvDeclBuilder::child_of(parent);
                    let h_ty = le(s.clone(), t.clone());
                    let (h_id, _h) = qb.fresh_local(h_ty.clone());
                    let body = c.eq_bool(mk_testbit(s.clone(), t.clone()), c.bfalse.clone());
                    let imp = qb.mk_pi(h_id, BinderInfo::Default, h_ty, body);
                    qb.finish_child(imp)
                };
                let ni_motive = {
                    let mut mb = EnvDeclBuilder::child_of(&sb);
                    let (t_id, t) = mb.fresh_local(c.nat.clone());
                    let body = ni_of(&t, &mb);
                    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
                    mb.finish_child(lam)
                };
                // i=0: Ni 0 = le (succ x') 0 → … ; absurd.
                let i0_base = {
                    let mut bb = EnvDeclBuilder::child_of(&sb);
                    let h_ty = le(s.clone(), c.zero.clone());
                    let (h_id, h) = bb.fresh_local(h_ty.clone());
                    let nslz = Expr::apps(
                        Expr::const_(Name::from_string("Nat.not_succ_le_zero"), vec![]),
                        [xp.clone(), h.clone()],
                    );
                    let target = c.eq_bool(mk_testbit(s.clone(), c.zero.clone()), c.bfalse.clone());
                    let false_elim =
                        Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);
                    let body = Expr::apps(false_elim, [target, nslz]);
                    let lam = bb.mk_lam(h_id, BinderInfo::Default, h_ty, body);
                    bb.finish_child(lam)
                };
                // i=succ j: (j) → Ni j → Ni (succ j)
                let i_step = {
                    let mut ib = EnvDeclBuilder::child_of(&sb);
                    let (j_id, j) = ib.fresh_local(c.nat.clone());
                    let ni_j = ni_of(&j, &ib);
                    let (ihni_id, _ihni) = ib.fresh_local(ni_j.clone());
                    let sj = c.succ(j.clone());
                    let h_ty = le(s.clone(), sj.clone());
                    let (h_id, h) = ib.fresh_local(h_ty.clone());

                    // div2 (succ x')
                    let d2s = c.div2(s.clone());
                    // hlt : lt (div2 (succ x')) (succ x')
                    let hpos = Expr::app(
                        Expr::const_(Name::from_string("Nat.zero_lt_succ"), vec![]),
                        xp.clone(),
                    );
                    let hlt = Expr::apps(
                        Expr::const_(Name::from_string("Nat.div2_lt_self"), vec![]),
                        [s.clone(), hpos],
                    );
                    // h1 : le (div2 (succ x')) x'  — div2_add_par_le x' has type
                    //   le (div2 x' + div2Par x') x' ≡ le (div2 (succ x')) x' (defeq).
                    let h1 = Expr::app(
                        Expr::const_(Name::from_string("Nat.div2_add_par_le"), vec![]),
                        xp.clone(),
                    );
                    // h2 : le x' j  from h : le (succ x')(succ j) via le_of_succ_le_succ x' j h
                    let h2 = Expr::apps(
                        Expr::const_(Name::from_string("Nat.le_of_succ_le_succ"), vec![]),
                        [xp.clone(), j.clone(), h.clone()],
                    );
                    // hle : le (div2 (succ x')) j  via le_trans (div2 (succ x')) x' j h1 h2
                    let hle = Expr::apps(
                        Expr::const_(Name::from_string("Nat.le_trans"), vec![]),
                        [d2s.clone(), xp.clone(), j.clone(), h1, h2],
                    );
                    // ihk (div2 (succ x')) hlt : P (div2 (succ x'))
                    //   then apply to j and hle : testBit (div2 (succ x')) j = false
                    let p_d2s = Expr::apps(ihk.clone(), [d2s.clone(), hlt]);
                    let out = Expr::apps(p_d2s, [j.clone(), hle]);
                    // out : testBit (div2 (succ x')) j = false ; concl Ni (succ j) is
                    //   testBit (succ x')(succ j) = false ≡ testBit (div2 (succ x')) j = false (defeq).
                    let lam = ib.mk_lam(h_id, BinderInfo::Default, h_ty, out);
                    let lam = ib.mk_lam(ihni_id, BinderInfo::Default, ni_j, lam);
                    let lam = ib.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), lam);
                    ib.finish_child(lam)
                };

                // P (succ x') = (i) → Ni i ; build fun i => Nat.rec Ni i0_base i_step i
                let (i_id, i) = sb.fresh_local(c.nat.clone());
                let rec_i = Expr::apps(c.rec0.clone(), [ni_motive, i0_base, i_step, i.clone()]);
                let lam_i = sb.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), rec_i);
                let lam_ihk = sb.mk_lam(ihk_id, BinderInfo::Default, ihk_ty, lam_i);
                let lam_ihnat = sb.mk_lam(ihnat_id, BinderInfo::Default, mx_xp, lam_ihk);
                let lam_xp = sb.mk_lam(xp_id, BinderInfo::Default, c.nat.clone(), lam_ihnat);
                sb.finish_child(lam_xp)
            };

            // Nat.rec.{0} Mx base step x : Mx x ; apply to ihx ⇒ P x
            let rec_x = Expr::apps(c.rec0.clone(), [mx, base, step, x.clone()]);
            let body = Expr::app(rec_x, ihx);
            let lam = fb.mk_lam(ihx_id, BinderInfo::Default, ihx_ty, body);
            let lam = fb.mk_lam(hacc_id, BinderInfo::Default, hacc_ty, lam);
            let lam = fb.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), lam);
            fb.finish_child(lam)
        };

        // Acc.rec.{0,1} Nat lt accMotive F x (Nat.accNatLt x)
        let acc_rec = Expr::const_(
            Name::from_string("Acc.rec"),
            vec![Level::zero(), Level::succ(Level::zero())],
        );
        let accnatlt = Expr::const_(Name::from_string("Nat.accNatLt"), vec![]);
        let acc_x = Expr::app(accnatlt, x0.clone());
        let rec_app = Expr::apps(
            acc_rec,
            [
                c.nat.clone(),
                nat_lt_const.clone(),
                acc_motive,
                f_step,
                x0.clone(),
                acc_x,
            ],
        );
        let lam = vb.mk_lam(x0_id, BinderInfo::Default, c.nat.clone(), rec_app);
        vb.finish(lam)
    };
    (type_, value)
}

// ===========================================================================
// Lemma 8 (the goal): Nat.testBit_bitwise
//   (f) → (f false false = false) → (m n i) →
//      testBit (bitwise f m n) i = f (testBit m i) (testBit n i)
// ===========================================================================
//
// bitwise f m n ≡ bitwiseAux f (m+n) m n. Case-split Nat.le_or_lt (m+n) i:
//   lt i (m+n): testBit_bitwiseAux f (m+n) i m n hlt.
//   le (m+n) i: LHS = false (testBit_bitwiseAux_high), and
//     f (testBit m i)(testBit n i) = f false false = false
//       [testBit_eq_false_of_ge on m (m ≤ m+n ≤ i) and n (n ≤ m+n ≤ i), then hf].
fn build_testbit_bitwise(c: &C) -> (Expr, Expr) {
    let bool_to_bool_to_bool = Expr::pi(
        BinderInfo::Default,
        c.bool_ty.clone(),
        Expr::pi(BinderInfo::Default, c.bool_ty.clone(), c.bool_ty.clone()),
    );
    let bitwise = Expr::const_(Name::from_string("Nat.bitwise"), vec![]);
    let testbit = c.testbit.clone();
    let mk_testbit = |x: Expr, i: Expr| Expr::apps(testbit.clone(), [x, i]);

    // hf type: f false false = false
    let hf_ty_of = |f: &Expr| {
        let ff = Expr::apps(f.clone(), [c.bfalse.clone(), c.bfalse.clone()]);
        c.eq_bool(ff, c.bfalse.clone())
    };

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (f_id, f) = b.fresh_local(bool_to_bool_to_bool.clone());
        let (hf_id, _hf) = b.fresh_local(hf_ty_of(&f));
        let (m_id, m) = b.fresh_local(c.nat.clone());
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (i_id, i) = b.fresh_local(c.nat.clone());
        let lhs = mk_testbit(
            Expr::apps(bitwise.clone(), [f.clone(), m.clone(), n.clone()]),
            i.clone(),
        );
        let rhs = Expr::apps(
            f.clone(),
            [
                mk_testbit(m.clone(), i.clone()),
                mk_testbit(n.clone(), i.clone()),
            ],
        );
        let body = c.eq_bool(lhs, rhs);
        let pi = b.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), body);
        let pn = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), pi);
        let pm = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), pn);
        let phf = b.mk_pi(hf_id, BinderInfo::Default, hf_ty_of(&f), pm);
        let pf = b.mk_pi(f_id, BinderInfo::Default, bool_to_bool_to_bool.clone(), phf);
        b.finish(pf)
    };

    let value = {
        let mut vb = EnvDeclBuilder::new();
        let (f_id, f) = vb.fresh_local(bool_to_bool_to_bool.clone());
        let (hf_id, hf) = vb.fresh_local(hf_ty_of(&f));
        let (m_id, m) = vb.fresh_local(c.nat.clone());
        let (n_id, n) = vb.fresh_local(c.nat.clone());
        let (i_id, i) = vb.fresh_local(c.nat.clone());

        let mn = c.add(m.clone(), n.clone());
        let nm = c.add(n.clone(), m.clone());
        let aux = Expr::const_(Name::from_string("Nat.bitwiseAux"), vec![]);
        let full = Expr::apps(aux.clone(), [f.clone(), mn.clone(), m.clone(), n.clone()]);
        // goal LHS ≡ testBit full i  (bitwise f m n ≡ bitwiseAux f (m+n) m n)
        let lhs = mk_testbit(full.clone(), i.clone());
        let rhs = Expr::apps(
            f.clone(),
            [
                mk_testbit(m.clone(), i.clone()),
                mk_testbit(n.clone(), i.clone()),
            ],
        );
        let goal = c.eq_bool(lhs.clone(), rhs.clone());

        let le = |a: Expr, b: Expr| {
            Expr::apps(Expr::const_(Name::from_string("Nat.le"), vec![]), [a, b])
        };
        let lt = |a: Expr, b: Expr| {
            Expr::apps(Expr::const_(Name::from_string("Nat.lt"), vec![]), [a, b])
        };

        // le_or_lt (m+n) i : Or (le (m+n) i) (lt i (m+n))
        let le_or_lt = Expr::apps(
            Expr::const_(Name::from_string("Nat.le_or_lt"), vec![]),
            [mn.clone(), i.clone()],
        );
        let or_a = le(mn.clone(), i.clone());
        let or_b = lt(i.clone(), mn.clone());
        let or_rec = Expr::const_(Name::from_string("Or.rec"), vec![]);
        let motive_or = {
            let mut mb = EnvDeclBuilder::child_of(&vb);
            let or_ty = Expr::apps(
                Expr::const_(Name::from_string("Or"), vec![]),
                [or_a.clone(), or_b.clone()],
            );
            let (u_id, _u) = mb.fresh_local(or_ty.clone());
            let lam = mb.mk_lam(u_id, BinderInfo::Default, or_ty, goal.clone());
            mb.finish_child(lam)
        };

        // inl: hge : le (m+n) i  ⇒  LHS = false ; false = RHS.
        let inl = {
            let mut ib = EnvDeclBuilder::child_of(&vb);
            let (hge_id, hge) = ib.fresh_local(or_a.clone());
            // LHS = false : testBit_bitwiseAux_high f (m+n) i m n hge
            let high = Expr::apps(
                Expr::const_(Name::from_string("Nat.testBit_bitwiseAux_high"), vec![]),
                [
                    f.clone(),
                    mn.clone(),
                    i.clone(),
                    m.clone(),
                    n.clone(),
                    hge.clone(),
                ],
            );
            // hle_m : le m i  via le_trans m (m+n) i (le_add_right m n) hge
            let le_add_right_mn = Expr::apps(
                Expr::const_(Name::from_string("Nat.le_add_right"), vec![]),
                [m.clone(), n.clone()],
            );
            let hle_m = Expr::apps(
                Expr::const_(Name::from_string("Nat.le_trans"), vec![]),
                [
                    m.clone(),
                    mn.clone(),
                    i.clone(),
                    le_add_right_mn,
                    hge.clone(),
                ],
            );
            // hge_nm : le (n+m) i  via congrArg(?) — we need le (n+m) i from le (m+n) i.
            //   add_comm m n : m+n = n+m ; congrArg (fun z => le z i)? le lives in Prop;
            //   simpler: cast hge along add_comm using Eq.mpr-free route — use
            //   le_trans n (n+m) i (le_add_right n m) (hge re-typed). We get le (n+m) i
            //   by rewriting hge : le (m+n) i with add_comm. Build it via
            //   `(Nat.add_comm m n) ▸ hge`. We implement the cast with Eq.mpr on the
            //   proposition `le · i`. Cleaner: hle_n via le_trans n (m+n) i hn_le_mn hge,
            //   where hn_le_mn : le n (m+n).  n ≤ m+n  =  le_add_left? Use add_comm:
            //   le n (m+n) ← le n (n+m) [le_add_right n m] rewritten by add_comm.
            // hn_le_nm : le n (n+m)
            let le_add_right_nm = Expr::apps(
                Expr::const_(Name::from_string("Nat.le_add_right"), vec![]),
                [n.clone(), m.clone()],
            );
            // add_comm n m : n+m = m+n   (so we can retype le n (n+m) → le n (m+n))
            let add_comm_nm = Expr::apps(
                Expr::const_(Name::from_string("Nat.add_comm"), vec![]),
                [n.clone(), m.clone()],
            );
            // congrArg (fun z => le n z)?? le returns Prop; congrArg into Prop needs
            // congrArg.{1,1} Nat (Sort 0)? Not allowed at Bool level. Instead transport
            // hn_le_nm : le n (n+m) to le n (m+n) using Eq.mpr over the motive
            // (fun z => le n z) applied to add_comm. We use `Eq.subst`-style:
            //   @Eq.mpr is for Prop equalities; here we have a Nat equality and a
            //   Prop family. Use @Eq.rec / @congrArg to Prop is fine: congrArg over a
            //   Prop-valued function f : Nat → Prop gives an Eq in Prop's type (Sort 1),
            //   then we transport the proof with Eq.mp. Implement with Eq.mp:
            //     fam : Nat → Prop := fun z => le n z
            //     e : (le n (n+m)) = (le n (m+n))   via congrArg.{1, ?} — Prop = Sort 0,
            //       congrArg : {α : Sort u}{β : Sort v}... here β = Prop = Sort 1? No:
            //       fam z : Prop, fam : Nat → Prop = Nat → Sort 0, so β = Sort 0 ⇒ the
            //       OUTPUT type of fam is Sort 0, congrArg needs the codomain SORT which
            //       is Sort 1; congrArg.{1,1} Nat Prop won't match. We instead use
            //       @Eq.subst / @Eq.ndrec to transport. Use h : n+m = m+n and
            //       motive (fun z => le n z): Eq.ndrec hn_le_nm transported.
            // Build via Eq.mpr is messy; use `Nat.add_comm`-driven `Eq.mp` with the
            // proper congrArg into Sort 1 (Prop : Sort 1). fam : Nat → Sort 0; its
            // congrArg result is Eq (Sort 1) (fam a)(fam b) — but fam a : Prop : Sort 1,
            // so the level args are (1, 1) over base types Nat and (Sort 0). We use a
            // dedicated helper below.
            let fam_le_n = {
                let mut fb = EnvDeclBuilder::child_of(&ib);
                let (z_id, z) = fb.fresh_local(c.nat.clone());
                let body = le(n.clone(), z.clone());
                let lam = fb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body);
                fb.finish_child(lam)
            };
            // congrArg.{1,1} Nat (Sort 0) (n+m) (m+n) fam_le_n add_comm_nm
            //   : (le n (n+m)) = (le n (m+n))   [an Eq in Prop : Sort 1]
            let prop_sort = Expr::sort(Level::zero());
            let congr_to_prop = Expr::apps(
                Expr::const_(
                    Name::from_string("congrArg"),
                    vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
                ),
                [
                    c.nat.clone(),
                    prop_sort.clone(),
                    nm.clone(),
                    mn.clone(),
                    fam_le_n,
                    add_comm_nm,
                ],
            );
            // @Eq.mp.{0} (le n (n+m)) (le n (m+n)) congr_to_prop hn_le_nm : le n (m+n)
            //   (α,β : Prop = Sort 0 ⇒ universe arg 0).
            let eq_mp = Expr::const_(Name::from_string("Eq.mp"), vec![Level::zero()]);
            let hn_le_mn = Expr::apps(
                eq_mp,
                [
                    le(n.clone(), nm.clone()),
                    le(n.clone(), mn.clone()),
                    congr_to_prop,
                    le_add_right_nm,
                ],
            );
            // hle_n : le n i  via le_trans n (m+n) i hn_le_mn hge
            let hle_n = Expr::apps(
                Expr::const_(Name::from_string("Nat.le_trans"), vec![]),
                [n.clone(), mn.clone(), i.clone(), hn_le_mn, hge.clone()],
            );
            // tb_m_false : testBit m i = false ; tb_n_false : testBit n i = false
            let l5 = Expr::const_(Name::from_string("Nat.testBit_eq_false_of_ge"), vec![]);
            let tb_m_false = Expr::apps(l5.clone(), [m.clone(), i.clone(), hle_m]);
            let tb_n_false = Expr::apps(l5, [n.clone(), i.clone(), hle_n]);
            // RHS = f (testBit m i)(testBit n i)
            // e1 : f (testBit m i)(testBit n i) = f false (testBit n i)
            let tbm = mk_testbit(m.clone(), i.clone());
            let tbn = mk_testbit(n.clone(), i.clone());
            let g_fst = {
                let mut fb = EnvDeclBuilder::child_of(&ib);
                let (b_id, bvar) = fb.fresh_local(c.bool_ty.clone());
                let body = Expr::apps(f.clone(), [bvar, tbn.clone()]);
                let lam = fb.mk_lam(b_id, BinderInfo::Default, c.bool_ty.clone(), body);
                fb.finish_child(lam)
            };
            let e1 = c.congr_bool_bool(tbm.clone(), c.bfalse.clone(), g_fst, tb_m_false);
            // e2 : f false (testBit n i) = f false false
            let g_snd = {
                let mut fb = EnvDeclBuilder::child_of(&ib);
                let (b_id, bvar) = fb.fresh_local(c.bool_ty.clone());
                let body = Expr::apps(f.clone(), [c.bfalse.clone(), bvar]);
                let lam = fb.mk_lam(b_id, BinderInfo::Default, c.bool_ty.clone(), body);
                fb.finish_child(lam)
            };
            let e2 = c.congr_bool_bool(tbn.clone(), c.bfalse.clone(), g_snd, tb_n_false);
            // rhs_to_false : RHS = false  via Eq.trans e1 (Eq.trans e2 hf)
            let f_false_tbn = Expr::apps(f.clone(), [c.bfalse.clone(), tbn.clone()]);
            let f_false_false = Expr::apps(f.clone(), [c.bfalse.clone(), c.bfalse.clone()]);
            let e2_hf = c.trans_bool(
                f_false_tbn.clone(),
                f_false_false.clone(),
                c.bfalse.clone(),
                e2,
                hf.clone(),
            );
            let rhs_to_false = c.trans_bool(
                rhs.clone(),
                f_false_tbn.clone(),
                c.bfalse.clone(),
                e1,
                e2_hf,
            );
            // false = RHS  via Eq.symm rhs_to_false
            let false_to_rhs = c.symm_bool(rhs.clone(), c.bfalse.clone(), rhs_to_false);
            // out : LHS = RHS  via Eq.trans high false_to_rhs
            let out = c.trans_bool(
                lhs.clone(),
                c.bfalse.clone(),
                rhs.clone(),
                high,
                false_to_rhs,
            );
            let _ = nm;
            let lam = ib.mk_lam(hge_id, BinderInfo::Default, or_a.clone(), out);
            ib.finish_child(lam)
        };

        // inr: hlt : lt i (m+n)  ⇒  testBit_bitwiseAux f (m+n) i m n hlt
        let inr = {
            let mut ib = EnvDeclBuilder::child_of(&vb);
            let (hlt_id, hlt) = ib.fresh_local(or_b.clone());
            let body = Expr::apps(
                Expr::const_(Name::from_string("Nat.testBit_bitwiseAux"), vec![]),
                [
                    f.clone(),
                    mn.clone(),
                    i.clone(),
                    m.clone(),
                    n.clone(),
                    hlt.clone(),
                ],
            );
            let lam = ib.mk_lam(hlt_id, BinderInfo::Default, or_b.clone(), body);
            ib.finish_child(lam)
        };

        let rec_app = Expr::apps(or_rec, [or_a, or_b, motive_or, inl, inr, le_or_lt]);
        let lam = vb.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), rec_app);
        let lam = vb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
        let lam = vb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam);
        let lam = vb.mk_lam(hf_id, BinderInfo::Default, hf_ty_of(&f), lam);
        let lam = vb.mk_lam(f_id, BinderInfo::Default, bool_to_bool_to_bool.clone(), lam);
        vb.finish(lam)
    };
    (type_, value)
}

// ===========================================================================
// Corollaries: Nat.testBit_and / testBit_or / testBit_xor
//   testBit (Nat.<op> m n) i = <boolop> (testBit m i) (testBit n i)
// ===========================================================================
//
// Nat.land ≡ Nat.bitwise Bool.and (the Track II redefinition), so
//   testBit_bitwise Bool.and (rfl : Bool.and false false = false) m n i
// already has the corollary's type up to definitional unfolding of Nat.land.
// `Bool.<op> false false ≡ false` holds by `rfl` for and/or/xor.
fn build_testbit_op_corollary(c: &C, op_name: &str, bool_op: &str) -> (Expr, Expr) {
    let nat_op = Expr::const_(Name::from_string(op_name), vec![]);
    let bop = Expr::const_(Name::from_string(bool_op), vec![]);
    let testbit = c.testbit.clone();
    let mk_testbit = |x: Expr, i: Expr| Expr::apps(testbit.clone(), [x, i]);

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(c.nat.clone());
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (i_id, i) = b.fresh_local(c.nat.clone());
        let lhs = mk_testbit(
            Expr::apps(nat_op.clone(), [m.clone(), n.clone()]),
            i.clone(),
        );
        let rhs = Expr::apps(
            bop.clone(),
            [
                mk_testbit(m.clone(), i.clone()),
                mk_testbit(n.clone(), i.clone()),
            ],
        );
        let body = c.eq_bool(lhs, rhs);
        let pi = b.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), body);
        let pn = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), pi);
        let pm = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), pn);
        b.finish(pm)
    };
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(c.nat.clone());
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (i_id, i) = b.fresh_local(c.nat.clone());
        // hf : Bool.<op> false false = false  (rfl: reduces to false)
        let ff = Expr::apps(bop.clone(), [c.bfalse.clone(), c.bfalse.clone()]);
        let hf = c.refl_bool(ff);
        // testBit_bitwise Bool.<op> hf m n i
        //   : testBit (bitwise Bool.<op> m n) i = Bool.<op> (testBit m i)(testBit n i)
        //   ≡ corollary type (Nat.<op> m n ≡ bitwise Bool.<op> m n defeq).
        let body = Expr::apps(
            Expr::const_(Name::from_string("Nat.testBit_bitwise"), vec![]),
            [bop.clone(), hf, m.clone(), n.clone(), i.clone()],
        );
        let lam = b.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), body);
        let lam = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
        let lam = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam);
        b.finish(lam)
    };
    (type_, value)
}

impl Environment {
    /// Register the `Nat.testBit_bitwise` lemma chain (Track II step 3) plus the
    /// `Nat.testBit_and`/`or`/`xor` corollaries.
    pub(crate) fn register_nat_testbit_bitwise_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget
        // 2026-07-04): Clean-native Nat bitwise cluster (div2/testBit/bitwise
        // + par helpers) — the value-bearing definitions shadow the genuine
        // v4.31 bodies whose symbolic reduction the Mathlib.Data.Nat.Bitwise
        // lemma family needs (~20-decl Data cluster), and `Bool.xor` (which
        // this web references) is import-suppressed. Suppressed together; the
        // genuine olean declarations import through the checked path.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.init_nat()?;
        self.init_eq()?;
        self.init_bool()?;
        self.init_or()?;
        self.init_true_false()?;
        self.init_lt()?;
        self.init_well_founded()?;
        self.register_nat_div2_lt_self_proof()?;
        self.register_nat_testbit_def()?;
        self.register_nat_eq_of_testbit_proof()?; // div2_rejoin, div2Par_zero_or_one, ...
        self.register_nat_bitwise_def()?;
        self.register_nat_succ_add_proof()?; // Nat.succ_add
        self.init_nat_lt_wf()?;
        // Nat.le_add_right, Nat.le_or_lt, Nat.le_of_succ_le_succ (used by the
        // fuel-sufficiency case split in testBit_bitwise).
        self.register_nat_mul_left_cancel_succ_proof()?;
        self.register_nat_le_total_proof()?;
        self.register_nat_add_comm_proof()?; // Nat.add_comm (n+m = m+n cast)

        let c = C::new();

        if self
            .get_const(&Name::from_string("Nat.div2Par_two_mul"))
            .is_none()
        {
            let (type_, value) = build_div2par_two_mul(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.div2Par_two_mul"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        if self
            .get_const(&Name::from_string("Nat.div2_two_mul"))
            .is_none()
        {
            let (type_, value) = build_div2_two_mul(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.div2_two_mul"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        if self
            .get_const(&Name::from_string("Nat.bitNat_hi"))
            .is_none()
        {
            let (type_, value) = build_bit_nat_hi(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.bitNat_hi"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        if self
            .get_const(&Name::from_string("Nat.bitNat_lo"))
            .is_none()
        {
            let (type_, value) = build_bit_nat_lo(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.bitNat_lo"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        if self
            .get_const(&Name::from_string("Nat.testBit_bitwiseAux"))
            .is_none()
        {
            let (type_, value) = build_testbit_bitwise_aux(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.testBit_bitwiseAux"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        if self
            .get_const(&Name::from_string("Nat.testBit_bitwiseAux_high"))
            .is_none()
        {
            let (type_, value) = build_testbit_bitwise_aux_high(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.testBit_bitwiseAux_high"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        if self
            .get_const(&Name::from_string("Nat.testBit_eq_false_of_ge"))
            .is_none()
        {
            let (type_, value) = build_testbit_eq_false_of_ge(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.testBit_eq_false_of_ge"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        if self
            .get_const(&Name::from_string("Nat.testBit_bitwise"))
            .is_none()
        {
            let (type_, value) = build_testbit_bitwise(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.testBit_bitwise"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        for (op_name, bool_op, thm) in [
            ("Nat.land", "Bool.and", "Nat.testBit_and"),
            ("Nat.lor", "Bool.or", "Nat.testBit_or"),
            ("Nat.xor", "Bool.xor", "Nat.testBit_xor"),
        ] {
            if self.get_const(&Name::from_string(thm)).is_none() {
                let (type_, value) = build_testbit_op_corollary(&c, op_name, bool_op);
                self.add_decl(Declaration::Theorem {
                    name: Name::from_string(thm),
                    level_params: vec![],
                    type_,
                    value,
                })?;
            }
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
        env.register_nat_testbit_bitwise_proof().expect("register");
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
    fn test_lemma1_div2par_two_mul() {
        let env = env();
        check(&env, "Nat.div2Par_two_mul");
    }

    #[test]
    fn test_lemma2_div2_two_mul() {
        let env = env();
        check(&env, "Nat.div2_two_mul");
    }

    #[test]
    fn test_lemma3_bit_nat_hi() {
        let env = env();
        check(&env, "Nat.bitNat_hi");
    }

    #[test]
    fn test_lemma4_bit_nat_lo() {
        let env = env();
        check(&env, "Nat.bitNat_lo");
    }

    #[test]
    fn test_lemma6_testbit_bitwise_aux() {
        let env = env();
        check(&env, "Nat.testBit_bitwiseAux");
    }

    #[test]
    fn test_lemma7_testbit_bitwise_aux_high() {
        let env = env();
        check(&env, "Nat.testBit_bitwiseAux_high");
    }

    #[test]
    fn test_lemma5_testbit_eq_false_of_ge() {
        let env = env();
        check(&env, "Nat.testBit_eq_false_of_ge");
    }

    #[test]
    fn test_lemma8_testbit_bitwise() {
        let env = env();
        check(&env, "Nat.testBit_bitwise");
    }

    #[test]
    fn test_corollaries_testbit_and_or_xor() {
        let env = env();
        check(&env, "Nat.testBit_and");
        check(&env, "Nat.testBit_or");
        check(&env, "Nat.testBit_xor");
    }
}
