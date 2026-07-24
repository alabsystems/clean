// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Nat.eq_of_testBit_eq`:
//!
//! ```text
//! Nat.eq_of_testBit_eq : (m n : Nat) →
//!   ((i : Nat) → Nat.testBit m i = Nat.testBit n i) → m = n
//! ```
//!
//! i.e. a `Nat` is uniquely determined by its bits (Track HH). This is the
//! companion extensionality lemma for the constructive `Nat.testBit`
//! Definition (`algebra_nat_testbit_def.rs`) and the `Nat.div2` parity-carry
//! foundation (`algebra_nat_div2_lt_self_proof.rs`).
//!
//! # The definitional facts we lean on (all `rfl`, verified before writing)
//!
//! - `Nat.testBit k 0          ≡ Nat.toBoolPar (Nat.div2Par k)`   (parity bit)
//! - `Nat.testBit k (succ i)   ≡ Nat.testBit (Nat.div2 k) i`      (inner-rec)
//! - `Nat.div2 (succ k)        ≡ Nat.div2 k + Nat.div2Par k`
//! - `Nat.div2Par (succ k)     ≡ 1 - Nat.div2Par k`
//! - `Nat.div2 0 ≡ 0`, `Nat.div2Par 0 ≡ 0`, `Nat.toBoolPar 0 ≡ false`,
//!   `Nat.toBoolPar 1 ≡ true`, `1 - 0 ≡ 1`, `1 - 1 ≡ 0`
//! - `x + 0 ≡ x`, `x + 1 ≡ succ x`, `x + 2 ≡ succ (succ x)`,
//!   `x + succ y ≡ succ (x + y)`   (Nat.add recurses on its 2nd argument)
//!
//! # Lemma chain (every one a real kernel-checked, axiom-free term)
//!
//! 1. `Nat.div2Par_zero_or_one : (n : Nat) → Or (div2Par n = 0) (div2Par n = 1)`
//!    — `Nat.rec` induction; step case-splits the IH `Or` (the parity carry of
//!    `succ k` is `1 - div2Par k`, which is `1` or `0`).
//!
//! 2. `Nat.div2_rejoin : (n : Nat) → n = (div2 n + div2 n) + div2Par n`
//!    — `Nat.rec` induction; step case-splits `div2Par_zero_or_one k` so the
//!    `1 - div2Par k` carry becomes a ground `1` or `0` and every arithmetic
//!    step closes by `rfl` over `Nat.add`'s second-argument recursion.
//!
//! 3. `Nat.div2Par_eq_zero_of_toBoolPar_false :
//!      (k : Nat) → toBoolPar (div2Par k) = false → div2Par k = 0`
//!    — case-splits `div2Par_zero_or_one k`; the `div2Par k = 1` branch makes
//!    the hypothesis `true = false`, refuted by `Bool.noConfusion`.
//!
//! 4. `Nat.div2Par_inj_of_toBoolPar :
//!      (m n : Nat) → toBoolPar (div2Par m) = toBoolPar (div2Par n)
//!        → div2Par m = div2Par n`
//!    — nested case-split of `div2Par_zero_or_one m` / `… n`; matching parities
//!    chain by `Eq.trans`, the two cross parities make the hypothesis
//!    `false = true` (or `true = false`), refuted by `Bool.noConfusion`.
//!
//! 5. `Nat.testBit_zero_eq_false : (i : Nat) → testBit 0 i = false`
//!    — `Nat.rec` induction on `i` (`testBit 0 (succ i) ≡ testBit (div2 0) i ≡
//!    testBit 0 i`).
//!
//! 6. `Nat.eq_zero_of_testBit_all_false :
//!      (n : Nat) → ((i : Nat) → testBit n i = false) → n = 0`
//!    — strong induction on `n` via `Acc.rec` over `Nat.accNatLt`. With the
//!    parity bit `div2Par n = 0` (from lemma 3 at `i = 0`) and `div2 n = 0`
//!    (the IH at `div2 n < n`, only invoked for `n = succ _`), `div2_rejoin`
//!    folds `n = (0 + 0) + 0 = 0`.
//!
//! 7. `Nat.eq_of_testBit_eq` (the goal) — strong induction on `m` via `Acc.rec`
//!    over `Nat.accNatLt`. For `m = succ k`: the IH at `div2 m < m` gives
//!    `div2 m = div2 n` (from the hypothesis at `succ i`), and lemma 4 at
//!    `i = 0` gives `div2Par m = div2Par n`; `div2_rejoin` on both sides plus
//!    `Eq.trans`/`congr` recombine to `m = n`. For `m = 0`: lemma 6 (after
//!    rewriting the hypothesis through `testBit_zero_eq_false`) gives `n = 0`.
//!
//! # Axiom closure
//!
//! Every declaration is a `Declaration::Theorem`/`Definition` built from
//! `Nat.rec`/`Or.rec`/`Acc.rec`/`Bool.noConfusion`/`False.elim`/`Eq.*`/
//! `congrArg`, the constructive `Nat.div2*` / `Nat.testBit` / `Nat.toBoolPar`
//! defs, `Nat.accNatLt`, and the constructive order lemmas `Nat.div2_lt_self`
//! / `Nat.zero_lt_succ`. None is an axiom, so `env.axiom_deps` is empty for
//! each and `proof_quality == Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants shared across the testBit-extensionality lemmas.
struct C {
    nat: Expr,
    zero: Expr,
    succ: Expr,
    one: Expr,
    two: Expr,
    add: Expr,
    sub: Expr,
    rec0: Expr, // Nat.rec.{0} — Prop motive
    bool_ty: Expr,
    btrue: Expr,
    bfalse: Expr,
    div2: Expr,
    div2par: Expr,
    tobool: Expr,
    testbit: Expr,
    or_const: Expr,
    eq1: Expr, // Eq.{1}
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    congr11: Expr, // congrArg.{1,1}
    nat_lt: Expr,
    acc1: Expr,
    accnatlt: Expr,
    false_const: Expr,
    false_elim0: Expr, // False.elim.{0}
    noconf0: Expr,     // Bool.noConfusion.{0}
    succ_add: Expr,    // Nat.succ_add
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
            bool_ty: Expr::const_(Name::from_string("Bool"), vec![]),
            btrue: Expr::const_(Name::from_string("Bool.true"), vec![]),
            bfalse: Expr::const_(Name::from_string("Bool.false"), vec![]),
            div2: Expr::const_(Name::from_string("Nat.div2"), vec![]),
            div2par: Expr::const_(Name::from_string("Nat.div2Par"), vec![]),
            tobool: Expr::const_(Name::from_string("Nat.toBoolPar"), vec![]),
            testbit: Expr::const_(Name::from_string("Nat.testBit"), vec![]),
            or_const: Expr::const_(Name::from_string("Or"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![one_lvl.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![one_lvl.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![one_lvl.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![one_lvl.clone()]),
            congr11: Expr::const_(
                Name::from_string("congrArg"),
                vec![one_lvl.clone(), one_lvl.clone()],
            ),
            nat_lt: Expr::const_(Name::from_string("Nat.lt"), vec![]),
            acc1: Expr::const_(Name::from_string("Acc"), vec![one_lvl.clone()]),
            accnatlt: Expr::const_(Name::from_string("Nat.accNatLt"), vec![]),
            false_const: Expr::const_(Name::from_string("False"), vec![]),
            false_elim0: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            noconf0: Expr::const_(Name::from_string("Bool.noConfusion"), vec![Level::zero()]),
            succ_add: Expr::const_(Name::from_string("Nat.succ_add"), vec![]),
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
    fn tobool(&self, n: Expr) -> Expr {
        Expr::app(self.tobool.clone(), n)
    }
    fn testbit(&self, n: Expr, i: Expr) -> Expr {
        Expr::apps(self.testbit.clone(), [n, i])
    }
    /// `@Eq.{1} Nat a b`.
    fn eq_nat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nat.clone(), a, b])
    }
    /// `@Eq.{1} Bool a b`.
    fn eq_bool(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.bool_ty.clone(), a, b])
    }
    /// `@Eq.refl.{1} Nat a`.
    fn refl_nat(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.nat.clone(), a])
    }
    /// `@Eq.refl.{1} Bool a`.
    fn refl_bool(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.bool_ty.clone(), a])
    }
    /// `@Eq.symm.{1} Bool a b h : Eq b a`.
    fn symm_bool(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.bool_ty.clone(), a, b, h])
    }
    /// `@Eq.trans.{1} Bool a b c h1 h2 : Eq a c`.
    fn trans_bool(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans1.clone(),
            [self.bool_ty.clone(), a, b, cc, h1, h2],
        )
    }
    /// `@Bool.noConfusion.{0} P a b h` — for distinct ground constructors `a`,
    /// `b` (true/false) this yields a term of type `P`.
    fn noconf(&self, p: Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.noconf0.clone(), [p, a, b, h])
    }
    /// `@Eq.symm.{1} Nat a b h : Eq b a`.
    fn symm_nat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.nat.clone(), a, b, h])
    }
    /// `@Eq.trans.{1} Nat a b c h1 h2 : Eq a c`.
    fn trans_nat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.nat.clone(), a, b, cc, h1, h2])
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
    /// `Or A B` (A, B : Prop).
    fn or(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.or_const.clone(), [a, b])
    }
    /// `@Or.inl A B h`.
    fn or_inl(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Or.inl"), vec![]), [a, b, h])
    }
    /// `@Or.inr A B h`.
    fn or_inr(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Or.inr"), vec![]), [a, b, h])
    }
    /// `Nat.lt a b`.
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_lt.clone(), [a, b])
    }
    /// `@Acc.{1} Nat Nat.lt x`.
    fn acc_lt(&self, x: Expr) -> Expr {
        Expr::apps(
            self.acc1.clone(),
            [self.nat.clone(), self.nat_lt.clone(), x],
        )
    }
    /// `Nat.sub a b`.
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.sub.clone(), [a, b])
    }
    /// The closed lambda `fun (p : Nat) => 1 - p` (captures nothing).
    fn one_minus_fn(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (p_id, p) = b.fresh_local(self.nat.clone());
        let lam = b.mk_lam(
            p_id,
            BinderInfo::Default,
            self.nat.clone(),
            self.sub(self.one.clone(), p),
        );
        b.finish(lam)
    }
    /// A `fun (p : Nat) => body(p)` lambda (Nat → Nat). The body MAY capture
    /// outer free variables; `p` is allocated from a child of `parent` so its
    /// id is disjoint from every caller fvar (only `p` is abstracted).
    fn lam_nat_nat(&self, parent: &EnvDeclBuilder, body: &dyn Fn(Expr) -> Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (p_id, p) = b.fresh_local(self.nat.clone());
        b.mk_lam(p_id, BinderInfo::Default, self.nat.clone(), body(p))
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
// Lemma 1: Nat.div2Par_zero_or_one
//   (n : Nat) → Or (Eq Nat (div2Par n) 0) (Eq Nat (div2Par n) 1)
// ===========================================================================

/// `motive := fun (t : Nat) => Or (div2Par t = 0) (div2Par t = 1)`.
fn par01_motive(c: &C, parent: &EnvDeclBuilder) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = mb.fresh_local(c.nat.clone());
    let a = c.eq_nat(c.par(t.clone()), c.zero.clone());
    let b = c.eq_nat(c.par(t.clone()), c.one.clone());
    let body = c.or(a, b);
    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
    mb.finish_child(lam)
}

fn build_div2par_zero_or_one(c: &C) -> (Expr, Expr) {
    // type: (n : Nat) → Or (div2Par n = 0) (div2Par n = 1)
    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let a = c.eq_nat(c.par(n.clone()), c.zero.clone());
        let bb = c.eq_nat(c.par(n.clone()), c.one.clone());
        let concl = c.or(a, bb);
        let pi = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
        b.finish(pi)
    };

    let mut vb = EnvDeclBuilder::new();
    let (n_id, n) = vb.fresh_local(c.nat.clone());
    let motive = par01_motive(c, &vb);

    // base : motive 0 = Or (div2Par 0 = 0) (div2Par 0 = 1)
    //   Or.inl (refl : div2Par 0 = div2Par 0)  (div2Par 0 ≡ 0)
    let base = {
        let a = c.eq_nat(c.par(c.zero.clone()), c.zero.clone());
        let bb = c.eq_nat(c.par(c.zero.clone()), c.one.clone());
        c.or_inl(a, bb, c.refl_nat(c.par(c.zero.clone())))
    };

    // step : (k : Nat) → motive k → motive (succ k)
    let step = {
        let mut sb = EnvDeclBuilder::child_of(&vb);
        let (k_id, k) = sb.fresh_local(c.nat.clone());
        // ih : Or (div2Par k = 0) (div2Par k = 1)
        let ih_a = c.eq_nat(c.par(k.clone()), c.zero.clone());
        let ih_b = c.eq_nat(c.par(k.clone()), c.one.clone());
        let ih_ty = c.or(ih_a.clone(), ih_b.clone());
        let (ih_id, ih) = sb.fresh_local(ih_ty.clone());

        // goal := motive (succ k) = Or (par(succ k) = 0) (par(succ k) = 1)
        let goal_a = c.eq_nat(c.par(c.succ(k.clone())), c.zero.clone());
        let goal_b = c.eq_nat(c.par(c.succ(k.clone())), c.one.clone());

        // Or.rec ih_a ih_b motive_or inl-case inr-case ih  (Prop-only eliminator,
        // motive fixed to Prop ⇒ no explicit universe parameter)
        let or_rec = Expr::const_(Name::from_string("Or.rec"), vec![]);
        // motive_or : fun (_ : Or ih_a ih_b) => Or (par(succ k)=0) (par(succ k)=1)
        let motive_or = {
            let mut mb = EnvDeclBuilder::child_of(&sb);
            let (u_id, _u) = mb.fresh_local(ih_ty.clone());
            let body = c.or(goal_a.clone(), goal_b.clone());
            let lam = mb.mk_lam(u_id, BinderInfo::Default, ih_ty.clone(), body);
            mb.finish_child(lam)
        };
        // inl-case : (hk : par k = 0) →  Or (par(succ k)=0) (par(succ k)=1)
        //   par(succ k) ≡ 1 - par k.  congrArg (fun p => 1-p) hk : 1 - par k = 1 - 0,
        //   and 1 - 0 ≡ 1, so type ≡ par(succ k) = 1. ⇒ Or.inr.
        let inl_case = {
            let mut ib = EnvDeclBuilder::child_of(&sb);
            let (hk_id, hk) = ib.fresh_local(ih_a.clone());
            // congrArg (fun p => 1 - p) hk : Eq (1 - par k) (1 - 0)
            let proof = c.congr_nat_nat(c.par(k.clone()), c.zero.clone(), c.one_minus_fn(), hk);
            // type of proof ≡ Eq (par(succ k)) 1 ; wrap in Or.inr
            let body = c.or_inr(goal_a.clone(), goal_b.clone(), proof);
            let lam = ib.mk_lam(hk_id, BinderInfo::Default, ih_a.clone(), body);
            ib.finish_child(lam)
        };
        // inr-case : (hk : par k = 1) → ...  par(succ k) ≡ 1 - par k, 1 - 1 ≡ 0 ⇒ Or.inl
        let inr_case = {
            let mut ib = EnvDeclBuilder::child_of(&sb);
            let (hk_id, hk) = ib.fresh_local(ih_b.clone());
            let proof = c.congr_nat_nat(c.par(k.clone()), c.one.clone(), c.one_minus_fn(), hk);
            // proof : Eq (1 - par k) (1 - 1) ≡ Eq (par(succ k)) 0 ⇒ Or.inl
            let body = c.or_inl(goal_a.clone(), goal_b.clone(), proof);
            let lam = ib.mk_lam(hk_id, BinderInfo::Default, ih_b.clone(), body);
            ib.finish_child(lam)
        };

        let rec_app = Expr::apps(or_rec, [ih_a, ih_b, motive_or, inl_case, inr_case, ih]);
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, rec_app);
        let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_ih);
        sb.finish_child(lam_k)
    };

    let rec_app = Expr::apps(c.rec0.clone(), [motive, base, step, n]);
    let value = {
        let lam = vb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec_app);
        vb.finish(lam)
    };
    (type_, value)
}

// ===========================================================================
// Lemma 2: Nat.div2_rejoin
//   (n : Nat) → Eq Nat n ((div2 n + div2 n) + div2Par n)
// ===========================================================================

/// `RHS(t) := (div2 t + div2 t) + div2Par t`.
fn rejoin_rhs(c: &C, t: Expr) -> Expr {
    c.add(c.add(c.div2(t.clone()), c.div2(t.clone())), c.par(t))
}

fn build_div2_rejoin(c: &C) -> (Expr, Expr) {
    // type: (n : Nat) → Eq Nat n (RHS n)
    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let concl = c.eq_nat(n.clone(), rejoin_rhs(c, n.clone()));
        let pi = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
        b.finish(pi)
    };

    let mut vb = EnvDeclBuilder::new();
    let (n_id, n) = vb.fresh_local(c.nat.clone());

    // motive := fun t => Eq Nat t (RHS t)
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&vb);
        let (t_id, t) = mb.fresh_local(c.nat.clone());
        let body = c.eq_nat(t.clone(), rejoin_rhs(c, t.clone()));
        let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
        mb.finish_child(lam)
    };

    // base : motive 0 = Eq 0 (RHS 0) ; RHS 0 ≡ (0+0)+0 ≡ 0, so refl 0.
    let base = c.refl_nat(c.zero.clone());

    // step : (k : Nat) → motive k → motive (succ k)
    let step = {
        let mut sb = EnvDeclBuilder::child_of(&vb);
        let (k_id, k) = sb.fresh_local(c.nat.clone());
        let d = c.div2(k.clone()); // D
        let p = c.par(k.clone()); // P

        // ih : k = (D + D) + P
        let dd = c.add(d.clone(), d.clone());
        let ih_ty = c.eq_nat(k.clone(), c.add(dd.clone(), p.clone()));
        let (ih_id, ih) = sb.fresh_local(ih_ty.clone());

        // goal RHS for succ k:  R = ((D+P)+(D+P)) + (1-P) ≡ RHS(succ k)
        let goal = c.eq_nat(c.succ(k.clone()), rejoin_rhs(c, c.succ(k.clone())));

        // f := fun p => ((D + p) + (D + p)) + (1 - p)   so f P ≡ RHS(succ k).
        let f = {
            let mut fb = EnvDeclBuilder::child_of(&sb);
            let (q_id, q) = fb.fresh_local(c.nat.clone());
            let dq = c.add(d.clone(), q.clone());
            let body = c.add(
                c.add(dq.clone(), dq.clone()),
                c.sub(c.one.clone(), q.clone()),
            );
            let lam = fb.mk_lam(q_id, BinderInfo::Default, c.nat.clone(), body);
            fb.finish_child(lam)
        };
        // g := fun p => (D + D) + p
        let g = {
            let mut gb = EnvDeclBuilder::child_of(&sb);
            let (q_id, q) = gb.fresh_local(c.nat.clone());
            let body = c.add(dd.clone(), q.clone());
            let lam = gb.mk_lam(q_id, BinderInfo::Default, c.nat.clone(), body);
            gb.finish_child(lam)
        };

        // div2Par_zero_or_one k  : Or (P = 0) (P = 1)
        let par01 = Expr::app(
            Expr::const_(Name::from_string("Nat.div2Par_zero_or_one"), vec![]),
            k.clone(),
        );
        let or_a = c.eq_nat(p.clone(), c.zero.clone());
        let or_b = c.eq_nat(p.clone(), c.one.clone());
        let or_rec = Expr::const_(Name::from_string("Or.rec"), vec![]);
        // motive_or : fun (_ : Or (P=0) (P=1)) => goal
        let motive_or = {
            let mut mb = EnvDeclBuilder::child_of(&sb);
            let or_ty = c.or(or_a.clone(), or_b.clone());
            let (u_id, _u) = mb.fresh_local(or_ty.clone());
            let lam = mb.mk_lam(u_id, BinderInfo::Default, or_ty, goal.clone());
            mb.finish_child(lam)
        };

        // ---- inl case: hk : P = 0 (V = 0) ----
        // ihk : k = (D+D)+0       = Eq.trans ih (congrArg g hk)
        // L   : succ k = succ((D+D)+0)   = congrArg succ ihk
        //         succ((D+D)+0) ≡ succ(D+D) ≡ f 0  (defeq)
        // Rr  : f 0 = R                  = congrArg f (Eq.symm hk)
        // out : Eq.trans L Rr  : succ k = R
        let inl_case = {
            let mut ib = EnvDeclBuilder::child_of(&sb);
            let (hk_id, hk) = ib.fresh_local(or_a.clone());
            let dd_p = c.add(dd.clone(), p.clone()); // (D+D)+P
            let dd_0 = c.add(dd.clone(), c.zero.clone()); // (D+D)+0
                                                          // congrArg g hk : (D+D)+P = (D+D)+0
            let cg = c.congr_nat_nat(p.clone(), c.zero.clone(), g.clone(), hk.clone());
            // ihk : k = (D+D)+0
            let ihk = c.trans_nat(k.clone(), dd_p.clone(), dd_0.clone(), ih.clone(), cg);
            // L : succ k = succ((D+D)+0)
            let succ_k = c.succ(k.clone());
            let succ_dd0 = c.succ(dd_0.clone());
            let l = c.congr_nat_nat(k.clone(), dd_0.clone(), c.succ.clone(), ihk);
            // Rr : f 0 = f P (=R) ; congrArg f (Eq.symm hk)
            let f0 = Expr::app(f.clone(), c.zero.clone());
            let r_big = Expr::app(f.clone(), p.clone()); // = R
            let symm_hk = c.symm_nat(p.clone(), c.zero.clone(), hk.clone());
            let rr = c.congr_nat_nat(c.zero.clone(), p.clone(), f.clone(), symm_hk);
            // Eq.trans L Rr : succ k = R   (mid: succ((D+D)+0) ≡ f 0 defeq)
            let out = c.trans_nat(succ_k, succ_dd0, r_big, l, rr);
            let _ = f0;
            let lam = ib.mk_lam(hk_id, BinderInfo::Default, or_a.clone(), out);
            ib.finish_child(lam)
        };

        // ---- inr case: hk : P = 1 (V = 1) ----
        // ihk : k = (D+D)+1            (≡ succ(D+D))
        // L   : succ k = succ((D+D)+1) (≡ succ(succ(D+D)))
        // bridge B : succ((D+D)+1) = f 1
        //     succ((D+D)+1) ≡ succ(succ(D+D)); f 1 ≡ succ D + succ D ≡ succ(succ D + D)
        //     succ_add D D : succ D + D = succ(D+D)
        //     B = congrArg succ (Eq.symm (succ_add D D))
        //         : succ(succ(D+D)) = succ(succ D + D)   ≡  succ((D+D)+1) = f 1
        // Rr  : f 1 = R               = congrArg f (Eq.symm hk)
        // out : Eq.trans (Eq.trans L B) Rr
        let inr_case = {
            let mut ib = EnvDeclBuilder::child_of(&sb);
            let (hk_id, hk) = ib.fresh_local(or_b.clone());
            let dd_p = c.add(dd.clone(), p.clone()); // (D+D)+P
            let dd_1 = c.add(dd.clone(), c.one.clone()); // (D+D)+1
            let cg = c.congr_nat_nat(p.clone(), c.one.clone(), g.clone(), hk.clone());
            let ihk = c.trans_nat(k.clone(), dd_p.clone(), dd_1.clone(), ih.clone(), cg);
            let succ_k = c.succ(k.clone());
            let succ_dd1 = c.succ(dd_1.clone()); // succ((D+D)+1)
            let l = c.congr_nat_nat(k.clone(), dd_1.clone(), c.succ.clone(), ihk);
            // bridge: succ_add D D : succ D + D = succ(D+D)
            let succ_d_plus_d = c.add(c.succ(d.clone()), d.clone()); // succ D + D
            let succ_dd = c.succ(dd.clone()); // succ(D+D)
            let succ_add_dd = Expr::apps(c.succ_add.clone(), [d.clone(), d.clone()]);
            // Eq.symm : succ(D+D) = succ D + D
            let symm_sa = c.symm_nat(succ_d_plus_d.clone(), succ_dd.clone(), succ_add_dd);
            // congrArg succ : succ(succ(D+D)) = succ(succ D + D)
            let bridge = c.congr_nat_nat(
                succ_dd.clone(),
                succ_d_plus_d.clone(),
                c.succ.clone(),
                symm_sa,
            );
            // f 1 ≡ succ(succ D + D) defeq ; target type of bridge RHS
            let f1 = Expr::app(f.clone(), c.one.clone());
            // L then bridge : succ k = f 1  (succ((D+D)+1) ≡ succ(succ(D+D)) defeq to bridge LHS)
            let l_bridge = c.trans_nat(succ_k.clone(), succ_dd1.clone(), f1.clone(), l, bridge);
            // Rr : f 1 = R
            let r_big = Expr::app(f.clone(), p.clone());
            let symm_hk = c.symm_nat(p.clone(), c.one.clone(), hk.clone());
            let rr = c.congr_nat_nat(c.one.clone(), p.clone(), f.clone(), symm_hk);
            let out = c.trans_nat(succ_k, f1, r_big, l_bridge, rr);
            let lam = ib.mk_lam(hk_id, BinderInfo::Default, or_b.clone(), out);
            ib.finish_child(lam)
        };

        let rec_app = Expr::apps(or_rec, [or_a, or_b, motive_or, inl_case, inr_case, par01]);
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, rec_app);
        let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_ih);
        sb.finish_child(lam_k)
    };

    let rec_app = Expr::apps(c.rec0.clone(), [motive, base, step, n]);
    let value = {
        let lam = vb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec_app);
        vb.finish(lam)
    };
    (type_, value)
}

// ===========================================================================
// Lemma 3: Nat.div2Par_eq_zero_of_toBoolPar_false
//   (k : Nat) → Eq Bool (toBoolPar (div2Par k)) false → Eq Nat (div2Par k) 0
// ===========================================================================
fn build_div2par_eq_zero_of_tobool_false(c: &C) -> (Expr, Expr) {
    // type: (k : Nat) → (toBoolPar (div2Par k) = false) → (div2Par k = 0)
    let mk_hyp = |k: &Expr| c.eq_bool(c.tobool(c.par(k.clone())), c.bfalse.clone());
    let mk_concl = |k: &Expr| c.eq_nat(c.par(k.clone()), c.zero.clone());

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (k_id, k) = b.fresh_local(c.nat.clone());
        let hyp = mk_hyp(&k);
        let (h_id, _h) = b.fresh_local(hyp.clone());
        let concl = mk_concl(&k);
        let imp = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
        let pi = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), imp);
        b.finish(pi)
    };

    let value = {
        let mut vb = EnvDeclBuilder::new();
        let (k_id, k) = vb.fresh_local(c.nat.clone());
        let hyp = mk_hyp(&k);
        let (h_id, h) = vb.fresh_local(hyp.clone());
        let concl = mk_concl(&k); // div2Par k = 0
        let p = c.par(k.clone());

        // div2Par_zero_or_one k : Or (P=0) (P=1)
        let par01 = Expr::app(
            Expr::const_(Name::from_string("Nat.div2Par_zero_or_one"), vec![]),
            k.clone(),
        );
        let or_a = c.eq_nat(p.clone(), c.zero.clone());
        let or_b = c.eq_nat(p.clone(), c.one.clone());
        let or_rec = Expr::const_(Name::from_string("Or.rec"), vec![]);
        let motive_or = {
            let mut mb = EnvDeclBuilder::child_of(&vb);
            let or_ty = c.or(or_a.clone(), or_b.clone());
            let (u_id, _u) = mb.fresh_local(or_ty.clone());
            let lam = mb.mk_lam(u_id, BinderInfo::Default, or_ty, concl.clone());
            mb.finish_child(lam)
        };
        // inl: hk : P = 0  ⇒ return hk
        let inl_case = {
            let mut ib = EnvDeclBuilder::child_of(&vb);
            let (hk_id, hk) = ib.fresh_local(or_a.clone());
            let lam = ib.mk_lam(hk_id, BinderInfo::Default, or_a.clone(), hk);
            ib.finish_child(lam)
        };
        // inr: hk : P = 1.  H : toBoolPar P = false.
        //   congrArg toBoolPar hk : toBoolPar P = toBoolPar 1
        //   symm -> toBoolPar 1 = toBoolPar P ; trans H -> toBoolPar 1 = false
        //   toBoolPar 1 ≡ true ⇒ H' : true = false ; Bool.noConfusion ⇒ concl
        let inr_case = {
            let mut ib = EnvDeclBuilder::child_of(&vb);
            let (hk_id, hk) = ib.fresh_local(or_b.clone());
            let tb_p = c.tobool(p.clone());
            let tb_1 = c.tobool(c.one.clone());
            let cg = c.congr_nat_bool(p.clone(), c.one.clone(), c.tobool.clone(), hk); // tb P = tb 1
            let symm = c.symm_bool(tb_p.clone(), tb_1.clone(), cg); // tb 1 = tb P
            let h_prime = c.trans_bool(
                tb_1.clone(),
                tb_p.clone(),
                c.bfalse.clone(),
                symm,
                h.clone(),
            );
            // h_prime : tb 1 = false ≡ true = false
            let nc = c.noconf(concl.clone(), c.btrue.clone(), c.bfalse.clone(), h_prime);
            let lam = ib.mk_lam(hk_id, BinderInfo::Default, or_b.clone(), nc);
            ib.finish_child(lam)
        };

        let rec_app = Expr::apps(or_rec, [or_a, or_b, motive_or, inl_case, inr_case, par01]);
        let lam_h = vb.mk_lam(h_id, BinderInfo::Default, hyp, rec_app);
        let lam_k = vb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_h);
        vb.finish(lam_k)
    };
    (type_, value)
}

// ===========================================================================
// Lemma 5: Nat.testBit_zero_eq_false
//   (i : Nat) → Eq Bool (testBit 0 i) false
// ===========================================================================
fn build_testbit_zero_eq_false(c: &C) -> (Expr, Expr) {
    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (i_id, i) = b.fresh_local(c.nat.clone());
        let concl = c.eq_bool(c.testbit(c.zero.clone(), i.clone()), c.bfalse.clone());
        let pi = b.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), concl);
        b.finish(pi)
    };
    let value = {
        let mut vb = EnvDeclBuilder::new();
        let (i_id, i) = vb.fresh_local(c.nat.clone());
        // motive := fun t => Eq Bool (testBit 0 t) false
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&vb);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let body = c.eq_bool(c.testbit(c.zero.clone(), t.clone()), c.bfalse.clone());
            let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
            mb.finish_child(lam)
        };
        // base: testBit 0 0 ≡ toBoolPar(div2Par 0) ≡ false ⇒ refl false
        let base = c.refl_bool(c.bfalse.clone());
        // step: (j) (ih : testBit 0 j = false) => ih
        //   testBit 0 (succ j) ≡ testBit (div2 0) j ≡ testBit 0 j, so motive(succ j) ≡ motive j.
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&vb);
            let (j_id, j) = sb.fresh_local(c.nat.clone());
            let ih_ty = c.eq_bool(c.testbit(c.zero.clone(), j.clone()), c.bfalse.clone());
            let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, ih);
            let lam_j = sb.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), lam_ih);
            sb.finish_child(lam_j)
        };
        let rec_app = Expr::apps(c.rec0.clone(), [motive, base, step, i]);
        let lam = vb.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), rec_app);
        vb.finish(lam)
    };
    (type_, value)
}

// ===========================================================================
// Lemma 4: Nat.div2Par_inj_of_toBoolPar
//   (m n : Nat) → toBoolPar (div2Par m) = toBoolPar (div2Par n)
//              → div2Par m = div2Par n
// ===========================================================================
fn build_div2par_inj_of_tobool(c: &C) -> (Expr, Expr) {
    let mk_hyp =
        |m: &Expr, n: &Expr| c.eq_bool(c.tobool(c.par(m.clone())), c.tobool(c.par(n.clone())));
    let mk_concl = |m: &Expr, n: &Expr| c.eq_nat(c.par(m.clone()), c.par(n.clone()));

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(c.nat.clone());
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let hyp = mk_hyp(&m, &n);
        let (h_id, _h) = b.fresh_local(hyp.clone());
        let concl = mk_concl(&m, &n);
        let imp = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
        let pin = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), imp);
        let pim = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), pin);
        b.finish(pim)
    };

    let value = {
        let mut vb = EnvDeclBuilder::new();
        let (m_id, m) = vb.fresh_local(c.nat.clone());
        let (n_id, n) = vb.fresh_local(c.nat.clone());
        let hyp = mk_hyp(&m, &n);
        let (h_id, h) = vb.fresh_local(hyp.clone());
        let pm = c.par(m.clone());
        let pn = c.par(n.clone());
        let concl = mk_concl(&m, &n); // pm = pn

        // Outer Or.rec on div2Par_zero_or_one m.
        let par01_m = Expr::app(
            Expr::const_(Name::from_string("Nat.div2Par_zero_or_one"), vec![]),
            m.clone(),
        );
        let m_a = c.eq_nat(pm.clone(), c.zero.clone());
        let m_b = c.eq_nat(pm.clone(), c.one.clone());
        let or_rec = Expr::const_(Name::from_string("Or.rec"), vec![]);

        let motive_m = {
            let mut mb = EnvDeclBuilder::child_of(&vb);
            let or_ty = c.or(m_a.clone(), m_b.clone());
            let (u_id, _u) = mb.fresh_local(or_ty.clone());
            let lam = mb.mk_lam(u_id, BinderInfo::Default, or_ty, concl.clone());
            mb.finish_child(lam)
        };

        // Helper that, given hm (pm = vm-literal) and the parent builder, builds
        // the inner Or.rec on div2Par_zero_or_one n.
        // vm_lit is the Nat literal (zero or one) that pm equals.
        let make_outer_case = |hm_eq: &Expr, vm_lit: &Expr, vm_is_zero: bool| -> Expr {
            let mut ob = EnvDeclBuilder::child_of(&vb);
            let (hm_id, hm) = ob.fresh_local(hm_eq.clone());

            let par01_n = Expr::app(
                Expr::const_(Name::from_string("Nat.div2Par_zero_or_one"), vec![]),
                n.clone(),
            );
            let n_a = c.eq_nat(pn.clone(), c.zero.clone());
            let n_b = c.eq_nat(pn.clone(), c.one.clone());
            let motive_n = {
                let mut mb = EnvDeclBuilder::child_of(&ob);
                let or_ty = c.or(n_a.clone(), n_b.clone());
                let (u_id, _u) = mb.fresh_local(or_ty.clone());
                let lam = mb.mk_lam(u_id, BinderInfo::Default, or_ty, concl.clone());
                mb.finish_child(lam)
            };

            // Build an inner leaf given hn (pn = vn-literal).
            // If same parity: pm = vm = vn = pn via Eq.trans.
            // Else (cross): derive  tb vm = tb vn  (≡ false=true or true=false)
            // and refute with Bool.noConfusion.
            let inner_leaf = |hn_eq: &Expr, vn_lit: &Expr, same: bool| -> Expr {
                let mut lb = EnvDeclBuilder::child_of(&ob);
                let (hn_id, hn) = lb.fresh_local(hn_eq.clone());
                let body = if same {
                    let symm_hn = c.symm_nat(pn.clone(), vn_lit.clone(), hn.clone());
                    c.trans_nat(pm.clone(), vm_lit.clone(), pn.clone(), hm.clone(), symm_hn)
                } else {
                    let tb_pm = c.tobool(pm.clone());
                    let tb_pn = c.tobool(pn.clone());
                    let tb_vm = c.tobool(vm_lit.clone());
                    let tb_vn = c.tobool(vn_lit.clone());
                    let cg_m =
                        c.congr_nat_bool(pm.clone(), vm_lit.clone(), c.tobool.clone(), hm.clone());
                    let symm_m = c.symm_bool(tb_pm.clone(), tb_vm.clone(), cg_m);
                    let cg_n =
                        c.congr_nat_bool(pn.clone(), vn_lit.clone(), c.tobool.clone(), hn.clone());
                    let h_to_vn =
                        c.trans_bool(tb_pm.clone(), tb_pn.clone(), tb_vn.clone(), h.clone(), cg_n);
                    let h2 =
                        c.trans_bool(tb_vm.clone(), tb_pm.clone(), tb_vn.clone(), symm_m, h_to_vn);
                    let a_ctor = c.tobool(vm_lit.clone());
                    let b_ctor = c.tobool(vn_lit.clone());
                    c.noconf(concl.clone(), a_ctor, b_ctor, h2)
                };
                let lam = lb.mk_lam(hn_id, BinderInfo::Default, hn_eq.clone(), body);
                lb.finish_child(lam)
            };

            // n=0 leaf: same iff vm is zero ; n=1 leaf: same iff vm is one
            let n_inl = inner_leaf(&n_a, &c.zero, vm_is_zero);
            let n_inr = inner_leaf(&n_b, &c.one, !vm_is_zero);

            let inner_rec = Expr::apps(or_rec.clone(), [n_a, n_b, motive_n, n_inl, n_inr, par01_n]);
            let lam = ob.mk_lam(hm_id, BinderInfo::Default, hm_eq.clone(), inner_rec);
            ob.finish_child(lam)
        };

        let m_inl = make_outer_case(&m_a, &c.zero, true);
        let m_inr = make_outer_case(&m_b, &c.one, false);

        let outer_rec = Expr::apps(or_rec, [m_a, m_b, motive_m, m_inl, m_inr, par01_m]);
        let lam_h = vb.mk_lam(h_id, BinderInfo::Default, hyp, outer_rec);
        let lam_n = vb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam_h);
        let lam_m = vb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam_n);
        vb.finish(lam_m)
    };
    (type_, value)
}

// ===========================================================================
// Lemma 6: Nat.eq_zero_of_testBit_all_false
//   (n : Nat) → ((i : Nat) → testBit n i = false) → n = 0
// ===========================================================================
//
// Strong induction on `n` via Acc.rec over Nat.accNatLt.  Inside the Acc step
// for `x` (strong IH `ihx : ∀ y, lt y x → P y`), we expose the constructor of
// `x` with an inner Nat.rec whose motive ABSTRACTS both the IH and the bit
// hypothesis over the scrutinee:
//   Mx t := (∀ y, lt y t → P y) → (∀ i, testBit t i = false) → t = 0
// so the `succ k` branch may invoke the strong IH at `div2 (succ k) < succ k`
// without the dependent-elimination friction of a free `x`.
fn build_eq_zero_of_testbit_all_false(c: &C) -> (Expr, Expr) {
    // P t := (∀ i, testBit t i = false) → t = 0
    // Built within a single child builder; references only `t` (a parent fvar).
    let p_of = |t: &Expr, b: &EnvDeclBuilder| -> Expr {
        let mut pb = EnvDeclBuilder::child_of(b);
        let (i_id, i) = pb.fresh_local(c.nat.clone());
        let bit = c.eq_bool(c.testbit(t.clone(), i.clone()), c.bfalse.clone());
        let all_false = pb.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), bit);
        let concl = c.eq_nat(t.clone(), c.zero.clone());
        let (h_id, _h) = pb.fresh_local(all_false.clone());
        let imp = pb.mk_pi(h_id, BinderInfo::Default, all_false.clone(), concl);
        pb.finish_child(imp)
    };

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let concl = p_of(&n, &b);
        let pi = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
        b.finish(pi)
    };

    // value: fun n => Acc.rec.{0,1} Nat lt accMotive F n (Nat.accNatLt n)
    let value = {
        let mut vb = EnvDeclBuilder::new();
        let (n_id, n) = vb.fresh_local(c.nat.clone());

        // accMotive : fun (x : Nat) (_ : Acc lt x) => P x
        let acc_motive = {
            let mut mb = EnvDeclBuilder::child_of(&vb);
            let (x_id, x) = mb.fresh_local(c.nat.clone());
            let acc_x = c.acc_lt(x.clone());
            let (a_id, _a) = mb.fresh_local(acc_x.clone());
            let body = p_of(&x, &mb);
            let lam = mb.mk_lam(a_id, BinderInfo::Default, acc_x, body);
            let lam = mb.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), lam);
            mb.finish_child(lam)
        };

        // F : (x) → (hacc : ∀ y, lt y x → Acc lt y)
        //        → (ihx : ∀ y (hy : lt y x), P y)
        //        → P x
        let f_step = {
            let mut fb = EnvDeclBuilder::child_of(&vb);
            let (x_id, x) = fb.fresh_local(c.nat.clone());

            // hacc type : (y : Nat) → lt y x → Acc lt y
            let hacc_ty = {
                let mut hb = EnvDeclBuilder::child_of(&fb);
                let (y_id, y) = hb.fresh_local(c.nat.clone());
                let lt_yx = c.lt(y.clone(), x.clone());
                let (l_id, _l) = hb.fresh_local(lt_yx.clone());
                let acc_y = c.acc_lt(y.clone());
                let imp = hb.mk_pi(l_id, BinderInfo::Default, lt_yx, acc_y);
                let pi = hb.mk_pi(y_id, BinderInfo::Default, c.nat.clone(), imp);
                hb.finish_child(pi)
            };
            let (hacc_id, _hacc) = fb.fresh_local(hacc_ty.clone());

            // ihx type : (y : Nat) → (hy : lt y x) → P y
            let ihx_ty = {
                let mut ib = EnvDeclBuilder::child_of(&fb);
                let (y_id, y) = ib.fresh_local(c.nat.clone());
                let lt_yx = c.lt(y.clone(), x.clone());
                let (l_id, _l) = ib.fresh_local(lt_yx.clone());
                let py = p_of(&y, &ib);
                let imp = ib.mk_pi(l_id, BinderInfo::Default, lt_yx, py);
                let pi = ib.mk_pi(y_id, BinderInfo::Default, c.nat.clone(), imp);
                ib.finish_child(pi)
            };
            let (ihx_id, ihx) = fb.fresh_local(ihx_ty.clone());

            // Inner Nat.rec over x:
            //   Mx t := (∀ y, lt y t → P y) → (∀ i, testBit t i = false) → t = 0
            // value : Nat.rec.{0} Mx base step x  : Mx x
            // then apply to ihx and (the eventual hbits) — but P x ITSELF already
            // is `(∀i,…) → x=0`, and Mx x = (∀y, lt y x → P y) → P x. So we apply
            // Nat.rec…x to ihx, yielding P x exactly.
            let mx = {
                let mut mb = EnvDeclBuilder::child_of(&fb);
                let (t_id, t) = mb.fresh_local(c.nat.clone());
                // (∀ y, lt y t → P y)
                let ih_t = {
                    let mut ib = EnvDeclBuilder::child_of(&mb);
                    let (y_id, y) = ib.fresh_local(c.nat.clone());
                    let lt_yt = c.lt(y.clone(), t.clone());
                    let (l_id, _l) = ib.fresh_local(lt_yt.clone());
                    let py = p_of(&y, &ib);
                    let imp = ib.mk_pi(l_id, BinderInfo::Default, lt_yt, py);
                    let pi = ib.mk_pi(y_id, BinderInfo::Default, c.nat.clone(), imp);
                    ib.finish_child(pi)
                };
                let p_t = p_of(&t, &mb);
                // Mx t = ih_t → P t
                let body = {
                    let mut bb = EnvDeclBuilder::child_of(&mb);
                    let (u_id, _u) = bb.fresh_local(ih_t.clone());
                    let e = bb.mk_pi(u_id, BinderInfo::Default, ih_t.clone(), p_t.clone());
                    bb.finish_child(e)
                };
                let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
                mb.finish_child(lam)
            };

            // base : Mx 0 = (∀y, lt y 0 → P y) → (∀i, testBit 0 i=false) → 0=0
            //   fun _ihz _hbits => refl 0
            let base = {
                let mut bb = EnvDeclBuilder::child_of(&fb);
                // ihz : ∀ y, lt y 0 → P y
                let ihz_ty = {
                    let mut ib = EnvDeclBuilder::child_of(&bb);
                    let (y_id, y) = ib.fresh_local(c.nat.clone());
                    let lt_y0 = c.lt(y.clone(), c.zero.clone());
                    let (l_id, _l) = ib.fresh_local(lt_y0.clone());
                    let py = p_of(&y, &ib);
                    let imp = ib.mk_pi(l_id, BinderInfo::Default, lt_y0, py);
                    let pi = ib.mk_pi(y_id, BinderInfo::Default, c.nat.clone(), imp);
                    ib.finish_child(pi)
                };
                let (ihz_id, _ihz) = bb.fresh_local(ihz_ty.clone());
                // hbits : ∀ i, testBit 0 i = false
                let hbits_ty = {
                    let mut hb = EnvDeclBuilder::child_of(&bb);
                    let (i_id, i) = hb.fresh_local(c.nat.clone());
                    let bit = c.eq_bool(c.testbit(c.zero.clone(), i.clone()), c.bfalse.clone());
                    let pi = hb.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), bit);
                    hb.finish_child(pi)
                };
                let (hb_id, _hbv) = bb.fresh_local(hbits_ty.clone());
                let refl0 = c.refl_nat(c.zero.clone());
                let lam = bb.mk_lam(hb_id, BinderInfo::Default, hbits_ty, refl0);
                let lam = bb.mk_lam(ihz_id, BinderInfo::Default, ihz_ty, lam);
                bb.finish_child(lam)
            };

            // step : (k) → Mx k → Mx (succ k)
            //   fun k _ihnat (ihk : ∀y, lt y (succ k) → P y)
            //                (hbk : ∀ i, testBit (succ k) i = false) => <succ k = 0>
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&fb);
                let (k_id, k) = sb.fresh_local(c.nat.clone());
                let s = c.succ(k.clone());
                // ih_nat : Mx k  (unused)
                let mx_k = {
                    // recompute Mx k inline = ih_k → P k
                    let mut mb = EnvDeclBuilder::child_of(&sb);
                    let ih_k = {
                        let mut ib = EnvDeclBuilder::child_of(&mb);
                        let (y_id, y) = ib.fresh_local(c.nat.clone());
                        let lt_yk = c.lt(y.clone(), k.clone());
                        let (l_id, _l) = ib.fresh_local(lt_yk.clone());
                        let py = p_of(&y, &ib);
                        let imp = ib.mk_pi(l_id, BinderInfo::Default, lt_yk, py);
                        let pi = ib.mk_pi(y_id, BinderInfo::Default, c.nat.clone(), imp);
                        ib.finish_child(pi)
                    };
                    let p_k = p_of(&k, &mb);
                    let e = {
                        let mut bb = EnvDeclBuilder::child_of(&mb);
                        let (u_id, _u) = bb.fresh_local(ih_k.clone());
                        let ee = bb.mk_pi(u_id, BinderInfo::Default, ih_k.clone(), p_k.clone());
                        bb.finish_child(ee)
                    };
                    let _ = mb;
                    e
                };
                let (ihnat_id, _ihnat) = sb.fresh_local(mx_k.clone());

                // ihk : ∀ y, lt y (succ k) → P y
                let ihk_ty = {
                    let mut ib = EnvDeclBuilder::child_of(&sb);
                    let (y_id, y) = ib.fresh_local(c.nat.clone());
                    let lt_ys = c.lt(y.clone(), s.clone());
                    let (l_id, _l) = ib.fresh_local(lt_ys.clone());
                    let py = p_of(&y, &ib);
                    let imp = ib.mk_pi(l_id, BinderInfo::Default, lt_ys, py);
                    let pi = ib.mk_pi(y_id, BinderInfo::Default, c.nat.clone(), imp);
                    ib.finish_child(pi)
                };
                let (ihk_id, ihk) = sb.fresh_local(ihk_ty.clone());

                // hbk : ∀ i, testBit (succ k) i = false
                let hbk_ty = {
                    let mut hb = EnvDeclBuilder::child_of(&sb);
                    let (i_id, i) = hb.fresh_local(c.nat.clone());
                    let bit = c.eq_bool(c.testbit(s.clone(), i.clone()), c.bfalse.clone());
                    let pi = hb.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), bit);
                    hb.finish_child(pi)
                };
                let (hbk_id, hbk) = sb.fresh_local(hbk_ty.clone());

                // hp0 : div2Par (succ k) = 0
                //   div2Par_eq_zero_of_toBoolPar_false (succ k) (hbk 0)
                //   hbk 0 : testBit (succ k) 0 = false ≡ toBoolPar(div2Par(succ k)) = false
                let l3 = Expr::const_(
                    Name::from_string("Nat.div2Par_eq_zero_of_toBoolPar_false"),
                    vec![],
                );
                let hbk0 = Expr::app(hbk.clone(), c.zero.clone());
                let hp0 = Expr::apps(l3, [s.clone(), hbk0]); // div2Par (succ k) = 0

                // hlt : lt (div2 (succ k)) (succ k)
                //   div2_lt_self (succ k) (zero_lt_succ k)
                let div2_lt = Expr::const_(Name::from_string("Nat.div2_lt_self"), vec![]);
                let zero_lt_succ = Expr::const_(Name::from_string("Nat.zero_lt_succ"), vec![]);
                let hpos = Expr::app(zero_lt_succ, k.clone());
                let hlt = Expr::apps(div2_lt, [s.clone(), hpos]); // lt (div2 (succ k)) (succ k)

                // hbits_div2 : ∀ i, testBit (div2 (succ k)) i = false
                //   fun i => hbk (succ i)    (defeq: testBit (succ k)(succ i) ≡ testBit (div2(succ k)) i)
                let ds = c.div2(s.clone());
                let hbits_div2 = {
                    let mut hb = EnvDeclBuilder::child_of(&sb);
                    let (i_id, i) = hb.fresh_local(c.nat.clone());
                    let body = Expr::app(hbk.clone(), c.succ(i.clone()));
                    let lam = hb.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), body);
                    hb.finish_child(lam)
                };

                // hd0 : div2 (succ k) = 0  =  ihk (div2 (succ k)) hlt hbits_div2
                let hd0 = Expr::apps(ihk.clone(), [ds.clone(), hlt, hbits_div2]);

                // recombine: rejoin (succ k) : succ k = (Ds+Ds)+Ps
                //   step_p : (Ds+Ds)+Ps = (Ds+Ds)+0   = congrArg (fun p=>(Ds+Ds)+p) hp0
                //            (Ds+Ds)+0 ≡ Ds+Ds
                //   step_d : Ds+Ds = 0+0              = congrArg (fun d=>d+d) hd0   (0+0 ≡ 0)
                //   e1 : (Ds+Ds)+Ps = 0   = Eq.trans step_p step_d  (defeq mids)
                //   out : succ k = 0      = Eq.trans (rejoin (succ k)) e1
                let ps = c.par(s.clone());
                let dd = c.add(ds.clone(), ds.clone());
                let dd_ps = c.add(dd.clone(), ps.clone()); // (Ds+Ds)+Ps
                let dd_0 = c.add(dd.clone(), c.zero.clone()); // (Ds+Ds)+0
                                                              // step_p : (Ds+Ds)+Ps = (Ds+Ds)+0
                let g_p = c.lam_nat_nat(&sb, &|p| c.add(dd.clone(), p));
                let step_p = c.congr_nat_nat(ps.clone(), c.zero.clone(), g_p, hp0);
                // step_d : Ds+Ds = 0+0
                let zero_zero = c.add(c.zero.clone(), c.zero.clone());
                let g_d = c.lam_nat_nat(&sb, &|d| c.add(d.clone(), d.clone()));
                let step_d = c.congr_nat_nat(ds.clone(), c.zero.clone(), g_d, hd0);
                // e1 : (Ds+Ds)+Ps = 0   via mids (Ds+Ds)+0 ≡ Ds+Ds, then Ds+Ds = 0+0 ≡ 0
                // Eq.trans step_p step_d : (Ds+Ds)+Ps = 0+0  ; 0+0 ≡ 0
                let e1 = c.trans_nat(
                    dd_ps.clone(),
                    dd_0.clone(),
                    zero_zero.clone(),
                    step_p,
                    step_d,
                );
                // out : succ k = 0
                let rejoin_s = c.rejoin(s.clone()); // succ k = (Ds+Ds)+Ps
                let out = c.trans_nat(s.clone(), dd_ps.clone(), c.zero.clone(), rejoin_s, e1);

                let lam = sb.mk_lam(hbk_id, BinderInfo::Default, hbk_ty, out);
                let lam = sb.mk_lam(ihk_id, BinderInfo::Default, ihk_ty, lam);
                let lam = sb.mk_lam(ihnat_id, BinderInfo::Default, mx_k, lam);
                let lam = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam);
                sb.finish_child(lam)
            };

            // Nat.rec.{0} Mx base step x : Mx x = (∀y, lt y x → P y) → P x
            let rec_x = Expr::apps(c.rec0.clone(), [mx, base, step, x.clone()]);
            // apply to ihx  ⇒  P x
            let body = Expr::app(rec_x, ihx);

            let lam = fb.mk_lam(ihx_id, BinderInfo::Default, ihx_ty, body);
            let lam = fb.mk_lam(hacc_id, BinderInfo::Default, hacc_ty, lam);
            let lam = fb.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), lam);
            fb.finish_child(lam)
        };

        // Acc.rec.{0,1} Nat lt accMotive F n (Nat.accNatLt n)
        let acc_rec = Expr::const_(
            Name::from_string("Acc.rec"),
            vec![Level::zero(), Level::succ(Level::zero())],
        );
        let acc_n = Expr::app(c.accnatlt.clone(), n.clone());
        let rec_app = Expr::apps(
            acc_rec,
            [
                c.nat.clone(),
                c.nat_lt.clone(),
                acc_motive,
                f_step,
                n.clone(),
                acc_n,
            ],
        );
        let lam = vb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec_app);
        vb.finish(lam)
    };
    (type_, value)
}

// ===========================================================================
// Lemma 7 (the goal): Nat.eq_of_testBit_eq
//   (m n : Nat) → ((i : Nat) → testBit m i = testBit n i) → m = n
// ===========================================================================
//
// Same Acc.rec strong-induction skeleton as Lemma 6, with the binary predicate
//   P t := (n : Nat) → (∀ i, testBit t i = testBit n i) → t = n.
// The `succ k` branch invokes the strong IH at `div2 (succ k) < succ k` to get
// `div2 (succ k) = div2 n`, Lemma 4 (at bit 0) to get the parity equality, and
// `div2_rejoin` on both sides to recombine `succ k = n`.  The `0` branch uses
// `testBit_zero_eq_false` + Lemma 6 to force `n = 0`.
fn build_eq_of_testbit_eq(c: &C) -> (Expr, Expr) {
    // P t := (n : Nat) → (∀ i, testBit t i = testBit n i) → t = n
    let p_of = |t: &Expr, b: &EnvDeclBuilder| -> Expr {
        let mut pb = EnvDeclBuilder::child_of(b);
        let (n_id, n) = pb.fresh_local(c.nat.clone());
        // ∀ i, testBit t i = testBit n i
        let (i_id, i) = pb.fresh_local(c.nat.clone());
        let bit = c.eq_bool(
            c.testbit(t.clone(), i.clone()),
            c.testbit(n.clone(), i.clone()),
        );
        let all_eq = pb.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), bit);
        let concl = c.eq_nat(t.clone(), n.clone());
        let (h_id, _h) = pb.fresh_local(all_eq.clone());
        let imp = pb.mk_pi(h_id, BinderInfo::Default, all_eq.clone(), concl);
        let pi = pb.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), imp);
        pb.finish_child(pi)
    };

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(c.nat.clone());
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (i_id, i) = b.fresh_local(c.nat.clone());
        let bit = c.eq_bool(
            c.testbit(m.clone(), i.clone()),
            c.testbit(n.clone(), i.clone()),
        );
        let all_eq = b.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), bit);
        let concl = c.eq_nat(m.clone(), n.clone());
        let (h_id, _h) = b.fresh_local(all_eq.clone());
        let imp = b.mk_pi(h_id, BinderInfo::Default, all_eq.clone(), concl);
        let pin = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), imp);
        let pim = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), pin);
        b.finish(pim)
    };

    // Helper: build `∀ y, lt y <bound> → P y`.
    let ih_quant = |bound: &Expr, b: &EnvDeclBuilder| -> Expr {
        let mut ib = EnvDeclBuilder::child_of(b);
        let (y_id, y) = ib.fresh_local(c.nat.clone());
        let lt_yb = c.lt(y.clone(), bound.clone());
        let (l_id, _l) = ib.fresh_local(lt_yb.clone());
        let py = p_of(&y, &ib);
        let imp = ib.mk_pi(l_id, BinderInfo::Default, lt_yb, py);
        let pi = ib.mk_pi(y_id, BinderInfo::Default, c.nat.clone(), imp);
        ib.finish_child(pi)
    };

    let value = {
        let mut vb = EnvDeclBuilder::new();
        let (m_id, m) = vb.fresh_local(c.nat.clone());

        // accMotive : fun (x : Nat) (_ : Acc lt x) => P x
        let acc_motive = {
            let mut mb = EnvDeclBuilder::child_of(&vb);
            let (x_id, x) = mb.fresh_local(c.nat.clone());
            let acc_x = c.acc_lt(x.clone());
            let (a_id, _a) = mb.fresh_local(acc_x.clone());
            let body = p_of(&x, &mb);
            let lam = mb.mk_lam(a_id, BinderInfo::Default, acc_x, body);
            let lam = mb.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), lam);
            mb.finish_child(lam)
        };

        // F : (x) → (hacc) → (ihx : ∀y, lt y x → P y) → P x
        let f_step = {
            let mut fb = EnvDeclBuilder::child_of(&vb);
            let (x_id, x) = fb.fresh_local(c.nat.clone());

            let hacc_ty = {
                let mut hb = EnvDeclBuilder::child_of(&fb);
                let (y_id, y) = hb.fresh_local(c.nat.clone());
                let lt_yx = c.lt(y.clone(), x.clone());
                let (l_id, _l) = hb.fresh_local(lt_yx.clone());
                let acc_y = c.acc_lt(y.clone());
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

            // base : Mx 0
            //   fun (_ihz : ∀y, lt y 0 → P y) (n : Nat) (hbits : ∀i, testBit 0 i = testBit n i) =>
            //     Eq.symm (eq_zero_of_testBit_all_false n (fun i =>
            //         Eq.trans (Eq.symm (hbits i)) (testBit_zero_eq_false i)))
            let base = {
                let mut bb = EnvDeclBuilder::child_of(&fb);
                let ihz_ty = ih_quant(&c.zero, &bb);
                let (ihz_id, _ihz) = bb.fresh_local(ihz_ty.clone());
                let (n_id, n) = bb.fresh_local(c.nat.clone());
                // hbits : ∀ i, testBit 0 i = testBit n i
                let hbits_ty = {
                    let mut hb = EnvDeclBuilder::child_of(&bb);
                    let (i_id, i) = hb.fresh_local(c.nat.clone());
                    let bit = c.eq_bool(
                        c.testbit(c.zero.clone(), i.clone()),
                        c.testbit(n.clone(), i.clone()),
                    );
                    let pi = hb.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), bit);
                    hb.finish_child(pi)
                };
                let (hb_id, hbv) = bb.fresh_local(hbits_ty.clone());
                // all_false_n : ∀ i, testBit n i = false
                let all_false_n = {
                    let mut hb = EnvDeclBuilder::child_of(&bb);
                    let (i_id, i) = hb.fresh_local(c.nat.clone());
                    // hbits i : testBit 0 i = testBit n i ; symm: testBit n i = testBit 0 i
                    let tb0 = c.testbit(c.zero.clone(), i.clone());
                    let tbn = c.testbit(n.clone(), i.clone());
                    let hbi = Expr::app(hbv.clone(), i.clone());
                    let symm = c.symm_bool(tb0.clone(), tbn.clone(), hbi);
                    // testBit_zero_eq_false i : testBit 0 i = false
                    let tzf = Expr::app(
                        Expr::const_(Name::from_string("Nat.testBit_zero_eq_false"), vec![]),
                        i.clone(),
                    );
                    // Eq.trans symm tzf : testBit n i = false
                    let body = c.trans_bool(tbn.clone(), tb0.clone(), c.bfalse.clone(), symm, tzf);
                    let lam = hb.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), body);
                    hb.finish_child(lam)
                };
                // eq_zero_of_testBit_all_false n all_false_n : n = 0
                let l6 = Expr::const_(
                    Name::from_string("Nat.eq_zero_of_testBit_all_false"),
                    vec![],
                );
                let n_eq_0 = Expr::apps(l6, [n.clone(), all_false_n]);
                // Eq.symm : 0 = n
                let zero_eq_n = c.symm_nat(n.clone(), c.zero.clone(), n_eq_0);
                let lam = bb.mk_lam(hb_id, BinderInfo::Default, hbits_ty, zero_eq_n);
                let lam = bb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
                let lam = bb.mk_lam(ihz_id, BinderInfo::Default, ihz_ty, lam);
                bb.finish_child(lam)
            };

            // step : (k) → Mx k → Mx (succ k)
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&fb);
                let (k_id, k) = sb.fresh_local(c.nat.clone());
                let s = c.succ(k.clone());
                let mx_k = {
                    let mut mb = EnvDeclBuilder::child_of(&sb);
                    let ih_k = ih_quant(&k, &mb);
                    let p_k = p_of(&k, &mb);
                    let mut bb = EnvDeclBuilder::child_of(&mb);
                    let (u_id, _u) = bb.fresh_local(ih_k.clone());
                    let e = bb.mk_pi(u_id, BinderInfo::Default, ih_k.clone(), p_k.clone());
                    bb.finish_child(e)
                };
                let (ihnat_id, _ihnat) = sb.fresh_local(mx_k.clone());

                let ihk_ty = ih_quant(&s, &sb);
                let (ihk_id, ihk) = sb.fresh_local(ihk_ty.clone());

                // P (succ k) =  fun (n) (hbits : ∀i, testBit (succ k) i = testBit n i) => succ k = n
                let (n_id, n) = sb.fresh_local(c.nat.clone());
                let hbits_ty = {
                    let mut hb = EnvDeclBuilder::child_of(&sb);
                    let (i_id, i) = hb.fresh_local(c.nat.clone());
                    let bit = c.eq_bool(
                        c.testbit(s.clone(), i.clone()),
                        c.testbit(n.clone(), i.clone()),
                    );
                    let pi = hb.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), bit);
                    hb.finish_child(pi)
                };
                let (hb_id, hbv) = sb.fresh_local(hbits_ty.clone());

                let ds = c.div2(s.clone());
                let dn = c.div2(n.clone());
                let ps = c.par(s.clone());
                let pn = c.par(n.clone());

                // hpeq : div2Par (succ k) = div2Par n
                //   div2Par_inj_of_toBoolPar (succ k) n (hbits 0)
                //   hbits 0 : testBit (succ k) 0 = testBit n 0
                //           ≡ toBoolPar(div2Par(succ k)) = toBoolPar(div2Par n)
                let l4 = Expr::const_(Name::from_string("Nat.div2Par_inj_of_toBoolPar"), vec![]);
                let hbits0 = Expr::app(hbv.clone(), c.zero.clone());
                let hpeq = Expr::apps(l4, [s.clone(), n.clone(), hbits0]); // Ps = Pn

                // hlt : lt (div2 (succ k)) (succ k)
                let div2_lt = Expr::const_(Name::from_string("Nat.div2_lt_self"), vec![]);
                let zero_lt_succ = Expr::const_(Name::from_string("Nat.zero_lt_succ"), vec![]);
                let hpos = Expr::app(zero_lt_succ, k.clone());
                let hlt = Expr::apps(div2_lt, [s.clone(), hpos]);

                // hbits_div2 : ∀ i, testBit (div2(succ k)) i = testBit (div2 n) i
                //   fun i => hbits (succ i)
                let hbits_div2 = {
                    let mut hb = EnvDeclBuilder::child_of(&sb);
                    let (i_id, i) = hb.fresh_local(c.nat.clone());
                    let body = Expr::app(hbv.clone(), c.succ(i.clone()));
                    let lam = hb.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), body);
                    hb.finish_child(lam)
                };

                // hdeq : div2 (succ k) = div2 n
                //   ihk (div2(succ k)) hlt (div2 n) hbits_div2
                let hdeq = Expr::apps(ihk.clone(), [ds.clone(), hlt, dn.clone(), hbits_div2]);

                // Recombine: succ k = n
                //   rejoin(succ k) : succ k = (Ds+Ds)+Ps
                //   e_p : (Ds+Ds)+Ps = (Ds+Ds)+Pn      = congrArg (fun p=>(Ds+Ds)+p) hpeq
                //   e_d : (Ds+Ds)+Pn = (Dn+Dn)+Pn      = congrArg (fun d=>(d+d)+Pn) hdeq
                //   mid : (Ds+Ds)+Ps = (Dn+Dn)+Pn      = Eq.trans e_p e_d
                //   rj_n : n = (Dn+Dn)+Pn ; symm: (Dn+Dn)+Pn = n
                //   out : succ k = n = Eq.trans (rejoin (succ k)) (Eq.trans mid (Eq.symm rj_n))
                let dds = c.add(ds.clone(), ds.clone()); // Ds+Ds
                let ddn = c.add(dn.clone(), dn.clone()); // Dn+Dn
                let dds_ps = c.add(dds.clone(), ps.clone());
                let dds_pn = c.add(dds.clone(), pn.clone());
                let ddn_pn = c.add(ddn.clone(), pn.clone());
                let g_p = c.lam_nat_nat(&sb, &|p| c.add(dds.clone(), p));
                let e_p = c.congr_nat_nat(ps.clone(), pn.clone(), g_p, hpeq);
                let g_d = c.lam_nat_nat(&sb, &|d| c.add(c.add(d.clone(), d.clone()), pn.clone()));
                let e_d = c.congr_nat_nat(ds.clone(), dn.clone(), g_d, hdeq);
                let mid = c.trans_nat(dds_ps.clone(), dds_pn.clone(), ddn_pn.clone(), e_p, e_d);
                let rj_n = c.rejoin(n.clone()); // n = (Dn+Dn)+Pn
                let symm_rjn = c.symm_nat(n.clone(), ddn_pn.clone(), rj_n); // (Dn+Dn)+Pn = n
                let tail = c.trans_nat(dds_ps.clone(), ddn_pn.clone(), n.clone(), mid, symm_rjn);
                let rejoin_s = c.rejoin(s.clone()); // succ k = (Ds+Ds)+Ps
                let out = c.trans_nat(s.clone(), dds_ps.clone(), n.clone(), rejoin_s, tail);

                let lam = sb.mk_lam(hb_id, BinderInfo::Default, hbits_ty, out);
                let lam = sb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
                let lam = sb.mk_lam(ihk_id, BinderInfo::Default, ihk_ty, lam);
                let lam = sb.mk_lam(ihnat_id, BinderInfo::Default, mx_k, lam);
                let lam = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam);
                sb.finish_child(lam)
            };

            // Nat.rec.{0} Mx base step x : Mx x ; apply to ihx ⇒ P x
            let rec_x = Expr::apps(c.rec0.clone(), [mx, base, step, x.clone()]);
            let body = Expr::app(rec_x, ihx);
            let lam = fb.mk_lam(ihx_id, BinderInfo::Default, ihx_ty, body);
            let lam = fb.mk_lam(hacc_id, BinderInfo::Default, hacc_ty, lam);
            let lam = fb.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), lam);
            fb.finish_child(lam)
        };

        // Acc.rec.{0,1} Nat lt accMotive F m (Nat.accNatLt m)
        let acc_rec = Expr::const_(
            Name::from_string("Acc.rec"),
            vec![Level::zero(), Level::succ(Level::zero())],
        );
        let acc_m = Expr::app(c.accnatlt.clone(), m.clone());
        let rec_app = Expr::apps(
            acc_rec,
            [
                c.nat.clone(),
                c.nat_lt.clone(),
                acc_motive,
                f_step,
                m.clone(),
                acc_m,
            ],
        );
        let lam = vb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), rec_app);
        vb.finish(lam)
    };
    (type_, value)
}

impl Environment {
    /// Register the `Nat.eq_of_testBit_eq` lemma chain (Track HH).
    pub(crate) fn register_nat_eq_of_testbit_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget):
        // Nat bitwise-cluster proof content — states/proves properties of the
        // import-suppressed div2/testBit/bitwise/Bool.xor web (see
        // register_nat_testbit_def). Suppressed with it.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        // Dependencies (each idempotent).
        self.init_nat()?;
        self.init_eq()?;
        self.init_bool()?;
        self.init_or()?;
        self.init_true_false()?;
        self.init_lt()?;
        self.init_well_founded()?;
        self.register_nat_div2_lt_self_proof()?; // div2, div2Par, div2_lt_self
        self.register_nat_testbit_def()?; // testBit, toBoolPar
        self.init_nat_lt_wf()?; // Nat.accNatLt
        self.register_nat_succ_add_proof()?; // Nat.succ_add

        let c = C::new();

        // Lemma 1
        if self
            .get_const(&Name::from_string("Nat.div2Par_zero_or_one"))
            .is_none()
        {
            let (type_, value) = build_div2par_zero_or_one(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.div2Par_zero_or_one"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // Lemma 2
        if self
            .get_const(&Name::from_string("Nat.div2_rejoin"))
            .is_none()
        {
            let (type_, value) = build_div2_rejoin(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.div2_rejoin"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // Lemma 3
        if self
            .get_const(&Name::from_string("Nat.div2Par_eq_zero_of_toBoolPar_false"))
            .is_none()
        {
            let (type_, value) = build_div2par_eq_zero_of_tobool_false(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.div2Par_eq_zero_of_toBoolPar_false"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // Lemma 4
        if self
            .get_const(&Name::from_string("Nat.div2Par_inj_of_toBoolPar"))
            .is_none()
        {
            let (type_, value) = build_div2par_inj_of_tobool(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.div2Par_inj_of_toBoolPar"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // Lemma 5
        if self
            .get_const(&Name::from_string("Nat.testBit_zero_eq_false"))
            .is_none()
        {
            let (type_, value) = build_testbit_zero_eq_false(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.testBit_zero_eq_false"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // Lemma 6
        if self
            .get_const(&Name::from_string("Nat.eq_zero_of_testBit_all_false"))
            .is_none()
        {
            let (type_, value) = build_eq_zero_of_testbit_all_false(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.eq_zero_of_testBit_all_false"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // Lemma 7 (the goal)
        if self
            .get_const(&Name::from_string("Nat.eq_of_testBit_eq"))
            .is_none()
        {
            let (type_, value) = build_eq_of_testbit_eq(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.eq_of_testBit_eq"),
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
        env.register_nat_eq_of_testbit_proof().expect("register");
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
    fn test_lemma1_div2par_zero_or_one() {
        let env = env();
        check(&env, "Nat.div2Par_zero_or_one");
    }

    #[test]
    fn test_lemma2_div2_rejoin() {
        let env = env();
        check(&env, "Nat.div2_rejoin");
    }

    #[test]
    fn test_lemma3_and_5() {
        let env = env();
        check(&env, "Nat.div2Par_eq_zero_of_toBoolPar_false");
        check(&env, "Nat.testBit_zero_eq_false");
    }

    #[test]
    fn test_lemma4_div2par_inj() {
        let env = env();
        check(&env, "Nat.div2Par_inj_of_toBoolPar");
    }

    #[test]
    fn test_lemma6_eq_zero() {
        let env = env();
        check(&env, "Nat.eq_zero_of_testBit_all_false");
    }

    #[test]
    fn test_lemma7_eq_of_testbit_eq() {
        let env = env();
        check(&env, "Nat.eq_of_testBit_eq");
    }

    #[test]
    fn test_all_lemmas_axiom_free() {
        let env = env();
        for name in [
            "Nat.div2Par_zero_or_one",
            "Nat.div2_rejoin",
            "Nat.div2Par_eq_zero_of_toBoolPar_false",
            "Nat.div2Par_inj_of_toBoolPar",
            "Nat.testBit_zero_eq_false",
            "Nat.eq_zero_of_testBit_all_false",
            "Nat.eq_of_testBit_eq",
        ] {
            check(&env, name);
        }
    }
}
