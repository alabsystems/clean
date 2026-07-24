// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Component (A): the dyadic Archimedean witness
//! `Rat.exists_pow_gt` (the additive, `inv`-free convergence primitive the
//! Cauchy-modulus arguments consume).
//!
//! # The theorem
//!
//! ```text
//! Rat.exists_pow_gt :
//!   ∀ (eps : Rat), Rat.lt Rat.zero eps →
//!     Exists (fun (N : Nat) =>
//!       Rat.lt Rat.one (Rat.mul eps (Rat.ofNat (Nat.pow 2 N))))
//! ```
//!
//! "For every positive `eps` there is an `N` with `1 < eps · 2^N`." This is the
//! `inv`-free multiplicative shape of the dyadic modulus (the recommended target
//! of `designs/2026-06-18-kkl-real-sqrt-layer-plan.md` §7); every sqrt/Cauchy
//! convergence route in Stage B consumes it.
//!
//! # Proof
//!
//! `Quot.ind` on `eps` (with the hypothesis threaded through the motive
//! `β e := Rat.lt Rat.zero e → ∃ N, …`). For a representative `p : Rat.Raw`,
//! write `na := Rat.Raw.num p`, `e := Rat.Raw.effDenom p` (a `Nat`, always
//! `Nat.succ`-headed since `effDenom ≡ succ (pred denom)`).
//!
//! 1. **Positive numerator.** `hp : Rat.lt Rat.zero (Quot.mk p)` ι-reduces to
//!    `Int.lt (Int.mul Int.zero (Int.ofNat e)) (Int.mul na (Int.ofNat 1))`.
//!    Transport across `Int.zero_mul` (left) and `Int.mul_one` (right) to
//!    `Int.lt Int.zero na`, then `Int.exists_eq_ofNat_succ_of_zero_lt` gives
//!    `m` with `na = Int.ofNat (Nat.succ m)`.
//!
//! 2. **Witness `N := Nat.succ e`** (the STRICT dyadic exponent). The goal
//!    `Rat.lt Rat.one (Rat.mul (Quot.mk p) (Rat.ofNat (Nat.pow 2 (succ e))))`
//!    ι-reduces (`Rat.mul` multiplies numerators and effective denominators;
//!    `Rat.ofNat M`'s rep is `Raw.mk (ofNat M) 1`, `effDenom 1 ≡ 1`) to
//!    ```text
//!    Int.lt (Int.mul (Int.ofNat 1) (Int.ofNat (succ (pred (Nat.mul e 1)))))
//!           (Int.mul (Int.mul na (Int.ofNat 2^(succ e))) (Int.ofNat 1)).
//!    ```
//!
//! 3. **Core strict inequality.** Build
//!    `core : Int.lt (Int.ofNat e) (Int.mul na (Int.ofNat 2^(succ e)))`:
//!    - `core_lt : Int.lt (Int.ofNat e) (Int.ofNat 2^(succ e))` is
//!      `Int.ofNat_le_ofNat_of_le (succ e) (2^(succ e)) (Nat.lt_two_pow_succ_self e)`
//!      — because `Int.lt (ofNat e) (ofNat M) ≡ Int.le (ofNat (succ e)) (ofNat M)`
//!      (`Int.add (ofNat e) 1 ≡ ofNat (succ e)`), and `Nat.lt e M ≡ Nat.le (succ e) M`.
//!    - `le_step : Int.le (Int.ofNat 2^(succ e)) (Int.mul na (Int.ofNat 2^(succ e)))`
//!      from `Int.mul_le_mul_of_nonneg_right (ofNat 1) na X (1 ≤ na) (0 ≤ X)`
//!      (with `na = ofNat (succ m) ≥ ofNat 1`) transported across
//!      `Int.one_mul X : ofNat 1 · X = X`.
//!    - `core := Int.lt_of_lt_of_le … core_lt le_step`.
//!
//! 4. **Bridge to the goal.** `eL : Int.mul (ofNat 1) (ofNat (succ (pred
//!    (Nat.mul e 1)))) = Int.ofNat e` (via `Int.one_mul` then `congrArg
//!    (ofNat ∘ succ ∘ pred) (Nat.mul_one e)`, whose RHS `ofNat (succ (pred e))`
//!    is def-eq `ofNat e`); `eR : Int.mul na (ofNat 2^(succ e)) = Int.mul (…)
//!    (ofNat 1)` (symm `Int.mul_one`). Two `Eq.subst` transports carry `core`
//!    onto the reduced goal; `Exists.intro` packages `succ e` + that proof.
//!
//! # Axiom closure
//!
//! Mentions only `Rat`/`Rat.mk`/`Rat.lt`/`Rat.one`/`Rat.zero`/`Rat.mul`/
//! `Rat.ofNat`, the `Quot` primitives (`Quot.ind`/`Quot.mk`), the `Rat.Raw`
//! projections, the constructive Int theorems above, `Int.exists_eq_ofNat_succ_of_zero_lt`,
//! `Nat.lt_two_pow_succ_self`, `Nat.succ_le_succ`/`Nat.zero_le`, and the
//! foundational `Eq`/`Exists`/`congrArg` — none a `Declaration::Axiom`. So
//! `env.axiom_deps("Rat.exists_pow_gt")` is empty and the theorem is
//! `ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved constant handles + smart-constructors for the witness proof.
struct WitnessConsts {
    nat: Expr,
    int: Expr,
    raw: Expr,
    ratq: Expr,
    // Carrier.
    raw_mk: Expr,
    raw_num: Expr,
    raw_eff_denom: Expr,
    raw_equiv: Expr,
    quot_mk: Expr,
    quot_ind: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_ofnat: Expr,
    rat_lt: Expr,
    // Nat / Int literals + ops.
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pred: Expr,
    nat_pow: Expr,
    nmul: Expr,
    int_zero: Expr,
    int_of_nat: Expr,
    int_mul: Expr,
    // Int lemmas.
    int_zero_mul: Expr,
    int_mul_one: Expr,
    int_one_mul: Expr,
    int_ofnat_le_ofnat: Expr,
    int_mul_le_nonneg_right: Expr,
    int_ofnat_zero_le: Expr,
    int_lt_of_lt_of_le: Expr,
    int_exists_pos: Expr,
    // Nat lemmas.
    nat_lt_two_pow_succ: Expr,
    nat_succ_le_succ: Expr,
    nat_zero_le: Expr,
    nat_mul_one: Expr,
    // Eq / Exists.
    eq1: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
    exists_c: Expr,
    exists_intro: Expr,
}

impl WitnessConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            int: k("Int"),
            raw: k("Rat.Raw"),
            ratq: k("Rat"),
            raw_mk: k("Rat.Raw.mk"),
            raw_num: k("Rat.Raw.num"),
            raw_eff_denom: k("Rat.Raw.effDenom"),
            raw_equiv: k("Rat.Raw.Equiv"),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![l1.clone()]),
            quot_ind: Expr::const_(Name::from_string("Quot.ind"), vec![l1.clone()]),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_ofnat: k("Rat.ofNat"),
            rat_lt: k("Rat.lt"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_pred: k("Nat.pred"),
            nat_pow: k("Nat.pow"),
            nmul: k("Nat.mul"),
            int_zero: k("Int.zero"),
            int_of_nat: k("Int.ofNat"),
            int_mul: k("Int.mul"),
            int_zero_mul: k("Int.zero_mul"),
            int_mul_one: k("Int.mul_one"),
            int_one_mul: k("Int.one_mul"),
            int_ofnat_le_ofnat: k("Int.ofNat_le_ofNat_of_le"),
            int_mul_le_nonneg_right: k("Int.mul_le_mul_of_nonneg_right"),
            int_ofnat_zero_le: k("Int.ofNat_zero_le"),
            int_lt_of_lt_of_le: k("Int.lt_of_lt_of_le"),
            int_exists_pos: k("Int.exists_eq_ofNat_succ_of_zero_lt"),
            nat_lt_two_pow_succ: k("Nat.lt_two_pow_succ_self"),
            nat_succ_le_succ: k("Nat.succ_le_succ"),
            nat_zero_le: k("Nat.zero_le"),
            nat_mul_one: k("Nat.mul_one"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![l1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1.clone()]),
        }
    }

    fn nat_one(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    fn nat_two(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_one())
    }
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn pred(&self, n: Expr) -> Expr {
        Expr::app(self.nat_pred.clone(), n)
    }
    fn nmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nmul.clone(), [a, b])
    }
    fn two_pow(&self, n: Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.nat_two(), n])
    }
    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }
    fn imul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.int_mul.clone(), [a, b])
    }
    fn num(&self, p: Expr) -> Expr {
        Expr::app(self.raw_num.clone(), p)
    }
    /// `Int.ofNat (Rat.Raw.effDenom p)`.
    fn eff(&self, p: Expr) -> Expr {
        self.of_nat(Expr::app(self.raw_eff_denom.clone(), p))
    }
    fn eff_nat(&self, p: Expr) -> Expr {
        Expr::app(self.raw_eff_denom.clone(), p)
    }
    fn raw_mk(&self, n: Expr, d: Expr) -> Expr {
        Expr::apps(self.raw_mk.clone(), [n, d])
    }
    fn quot_mk(&self, l: Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.raw.clone(), self.raw_equiv.clone(), l],
        )
    }
    /// `Rat.lt a b`.
    fn rlt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    /// `Rat.mul a b`.
    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    /// `Rat.ofNat n`.
    fn rofnat(&self, n: Expr) -> Expr {
        Expr::app(self.rat_ofnat.clone(), n)
    }
    fn ilt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Int.lt"), vec![]), [a, b])
    }
    fn ile(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Int.le"), vec![]), [a, b])
    }
    fn eq_int(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.int.clone(), x, y])
    }
    /// `@Eq.symm Int x y h`.
    fn symm_int(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.int.clone(), x, y, h])
    }
    /// `@Eq.trans Int x y z h1 h2`.
    fn trans_int(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.int.clone(), x, y, z, h1, h2])
    }
    /// `@congrArg Nat Int x y f h : Eq Int (f x) (f y)`.
    fn congr_nat_int(&self, x: Expr, y: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.nat.clone(), self.int.clone(), x, y, f, h],
        )
    }
}

impl Environment {
    /// Register `Rat.exists_pow_gt`. Idempotent.
    ///
    /// `∀ eps, Rat.lt Rat.zero eps →
    ///    Exists (fun N => Rat.lt Rat.one (Rat.mul eps (Rat.ofNat (Nat.pow 2 N))))`.
    /// Constructive, empty admitted-axiom closure.
    pub fn register_rat_exists_pow_gt(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.exists_pow_gt");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Carrier + order + arith + ofNat.
        self.init_rat()?;
        self.init_rat_arith()?;
        self.init_rat_ord()?;
        self.init_eq()?;
        self.init_exists()?;
        self.init_quot();
        self.register_rat_ofnat()?;
        // Int helpers.
        self.register_int_exists_eq_ofnat_succ_of_zero_lt()?;
        self.register_int_zero_mul_proof()?;
        self.register_int_mul_one_proof()?;
        self.register_int_one_mul_proof()?;
        self.register_int_ofnat_zero_le_proof()?;
        self.register_int_mul_le_mul_of_nonneg_right_proof()?;
        self.register_int_lt_of_lt_of_le_proof()?;
        self.register_int_ofnat_mul_proof()?;
        // Int.ofNat_le_ofNat_of_le (+ Int.mul_one) via the Nat-bridge entry.
        self.register_nat_cast_le_of_ble()?;
        // Nat helpers.
        self.register_nat_lt_two_pow_succ_self()?;
        self.init_nat_top_level_ordering()?; // Nat.succ_le_succ
        self.register_nat_le_total_proof()?; // Nat.zero_le
        self.register_nat_mul_one_proof()?; // Nat.mul_one

        let c = WitnessConsts::new();

        let ty = build_type(&c);
        let value = build_value(&c);

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `∀ eps, Rat.lt Rat.zero eps → ∃ N, Rat.lt Rat.one (Rat.mul eps (ofNat 2^N))`.
fn build_type(c: &WitnessConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (eps_id, eps) = b.fresh_local(c.ratq.clone());
    let h_ty = c.rlt(c.rat_zero.clone(), eps.clone());
    let (h_id, _h) = b.fresh_local(h_ty.clone());
    let concl = exists_goal(c, &b, eps.clone());
    let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.ratq.clone(), e);
    b.finish(e)
}

/// The `Exists` predicate `fun (N : Nat) => Rat.lt Rat.one (Rat.mul target
/// (Rat.ofNat (Nat.pow 2 N)))`.
fn exists_pred(c: &WitnessConsts, parent: &EnvDeclBuilder, target: Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (n_id, n) = mb.fresh_local(c.nat.clone());
    let body = c.rlt(
        c.rat_one.clone(),
        c.rmul(target, c.rofnat(c.two_pow(n.clone()))),
    );
    let lam = mb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
    mb.finish_child(lam)
}

fn exists_goal(c: &WitnessConsts, parent: &EnvDeclBuilder, target: Expr) -> Expr {
    let pred = exists_pred(c, parent, target);
    Expr::apps(c.exists_c.clone(), [c.nat.clone(), pred])
}

fn build_value(c: &WitnessConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (eps_id, eps) = b.fresh_local(c.ratq.clone());
    let h_ty = c.rlt(c.rat_zero.clone(), eps.clone());
    let (h_id, h) = b.fresh_local(h_ty.clone());

    // Quot.ind motive β := fun (e : Rat) => Rat.lt Rat.zero e → ∃ N, … e ….
    let beta = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.ratq.clone());
        let hyp = c.rlt(c.rat_zero.clone(), x.clone());
        let (hyp_id, _hyp) = mb.fresh_local(hyp.clone());
        let concl = exists_goal(c, &mb, x.clone());
        let body = mb.mk_pi(hyp_id, BinderInfo::Default, hyp, concl);
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
        mb.finish_child(lam)
    };

    // minor: fun (p : Rat.Raw) => fun (hp : Rat.lt 0 (Quot.mk p)) => proof.
    let minor = build_minor(c, &b);

    // @Quot.ind Rat.Raw Equiv beta minor eps : beta eps
    //   ≡ (Rat.lt 0 eps → ∃ N, …); apply to h.
    let ind = Expr::apps(
        c.quot_ind.clone(),
        [c.raw.clone(), c.raw_equiv.clone(), beta, minor, eps.clone()],
    );
    let applied = Expr::app(ind, h.clone());
    let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, applied);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.ratq.clone(), e);
    b.finish(e)
}

/// The `Quot.ind` minor: `fun (p : Rat.Raw) (hp : Rat.lt 0 (Quot.mk p)) => …`.
fn build_minor(c: &WitnessConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (p_id, p) = mb.fresh_local(c.raw.clone());
    let mk_p = c.quot_mk(p.clone());
    let hp_ty = c.rlt(c.rat_zero.clone(), mk_p.clone());
    let (hp_id, hp) = mb.fresh_local(hp_ty.clone());

    let na = c.num(p.clone());
    let e_nat = c.eff_nat(p.clone()); // Rat.Raw.effDenom p : Nat.
    let e_int = c.of_nat(e_nat.clone()); // Int.ofNat (effDenom p).
    let succ_e = c.succ(e_nat.clone()); // Nat witness N.
    let two_pow_succ_e = c.two_pow(succ_e.clone());
    let x_int = c.of_nat(two_pow_succ_e.clone()); // Int.ofNat 2^(succ e).
    let na_x = c.imul(na.clone(), x_int.clone()); // na · 2^(succ e).
    let int_one = c.of_nat(c.nat_one());

    // --- Step 1: positive numerator -----------------------------------------
    // hp : Int.lt (Int.mul Int.zero e_int) (Int.mul na int_one)  (ι-reduced).
    // Transport across Int.zero_mul (left) and Int.mul_one (right).
    let zero_mul_e = c.imul(c.int_zero.clone(), e_int.clone());
    // e1 : Int.mul Int.zero e_int = Int.zero
    let e1 = Expr::app(c.int_zero_mul.clone(), e_int.clone());
    // motive_l : fun L => Int.lt L (Int.mul na int_one)
    let motive_l = {
        let mut d = EnvDeclBuilder::child_of(&mb);
        let (l_id, l) = d.fresh_local(c.int.clone());
        let body = c.ilt(l, c.imul(na.clone(), int_one.clone()));
        d.finish_child(d.mk_lam(l_id, BinderInfo::Default, c.int.clone(), body))
    };
    // hp1 : Int.lt Int.zero (Int.mul na int_one)
    let hp1 = Expr::apps(
        c.eq_subst.clone(),
        [
            c.int.clone(),
            motive_l,
            zero_mul_e,
            c.int_zero.clone(),
            e1,
            hp.clone(),
        ],
    );
    // e2 : Int.mul na int_one = na
    let e2 = Expr::app(c.int_mul_one.clone(), na.clone());
    let mul_na_one = c.imul(na.clone(), int_one.clone());
    // motive_r : fun R => Int.lt Int.zero R
    let motive_r = {
        let mut d = EnvDeclBuilder::child_of(&mb);
        let (r_id, r) = d.fresh_local(c.int.clone());
        let body = c.ilt(c.int_zero.clone(), r);
        d.finish_child(d.mk_lam(r_id, BinderInfo::Default, c.int.clone(), body))
    };
    // hp2 : Int.lt Int.zero na
    let hp2 = Expr::apps(
        c.eq_subst.clone(),
        [c.int.clone(), motive_r, mul_na_one, na.clone(), e2, hp1],
    );

    // ex : Exists (fun m => Eq Int na (Int.ofNat (Nat.succ m))).
    let ex = Expr::apps(c.int_exists_pos.clone(), [na.clone(), hp2]);

    // --- Eliminate the Exists with Exists.elim into the final ∃-goal ---------
    // We continue under `fun (m : Nat) (hm : Eq Int na (ofNat (succ m))) => …`.
    let final_goal = exists_goal(c, &mb, mk_p.clone());
    let elim_fn = build_exists_elim_fn(
        c, &mb, &p, &na, &e_nat, &e_int, &succ_e, &x_int, &na_x, &int_one,
    );
    // @Exists.elim.{0,0} Nat pred final_goal ex elim_fn  — but this kernel uses
    // Exists.elim with explicit args; we instead reuse `ex`'s recursor.
    let elim = exists_elim(c, &mb, &na, final_goal, ex, elim_fn);

    let lam = mb.mk_lam(hp_id, BinderInfo::Default, hp_ty, elim);
    let lam = mb.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), lam);
    mb.finish_child(lam)
}

/// `@Exists.elim` applied. The witness predicate is `fun m => Eq Int na (ofNat
/// (succ m))`. Produces `goal` from `ex` and the eliminator function.
fn exists_elim(
    c: &WitnessConsts,
    parent: &EnvDeclBuilder,
    na: &Expr,
    goal: Expr,
    ex: Expr,
    elim_fn: Expr,
) -> Expr {
    // pred : Nat → Prop := fun m => Eq Int na (ofNat (succ m)).
    let pred = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (m_id, m) = d.fresh_local(c.nat.clone());
        let body = c.eq_int(na.clone(), c.of_nat(c.succ(m)));
        d.finish_child(d.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body))
    };
    // @Exists.elim.{1} {Nat} {pred} {goal} ex elim_fn  — Exists.elim signature:
    //   ∀ {α : Sort u} {p} {b : Prop}, (∃ x, p x) → (∀ a, p a → b) → b.
    //   `Nat : Sort 1`, so `u = 1`.
    Expr::apps(
        Expr::const_(
            Name::from_string("Exists.elim"),
            vec![Level::succ(Level::zero())],
        ),
        [c.nat.clone(), pred, goal, ex, elim_fn],
    )
}

/// `fun (m : Nat) (hm : Eq Int na (ofNat (succ m))) => <proof of goal>`.
#[allow(clippy::too_many_arguments)]
fn build_exists_elim_fn(
    c: &WitnessConsts,
    parent: &EnvDeclBuilder,
    p: &Expr,
    na: &Expr,
    e_nat: &Expr,
    e_int: &Expr,
    succ_e: &Expr,
    x_int: &Expr,
    na_x: &Expr,
    int_one: &Expr,
) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = fb.fresh_local(c.nat.clone());
    let hm_ty = c.eq_int(na.clone(), c.of_nat(c.succ(m.clone())));
    let (hm_id, hm) = fb.fresh_local(hm_ty.clone());

    // core : Int.lt e_int na_x.
    let core = build_core(
        c, &fb, na, e_nat, e_int, succ_e, x_int, na_x, int_one, &m, &hm,
    );

    // --- Bridge core onto the reduced goal -----------------------------------
    // Goal (ι-reduced) :
    //   Int.lt (Int.mul int_one (eff prod)) (Int.mul na_x int_one)
    // where eff prod = Int.ofNat (succ (pred (Nat.mul e_nat 1))).
    let eff_prod_nat = c.succ(c.pred(c.nmul(e_nat.clone(), c.nat_one())));
    let eff_prod = c.of_nat(eff_prod_nat.clone());
    let goal_lhs = c.imul(int_one.clone(), eff_prod.clone());
    let goal_rhs = c.imul(na_x.clone(), int_one.clone());

    // eL : goal_lhs = e_int.
    //   step_a : Int.mul int_one eff_prod = eff_prod   (Int.one_mul eff_prod)
    let step_a = Expr::app(c.int_one_mul.clone(), eff_prod.clone());
    //   step_b : eff_prod = e_int
    //     congrArg (fun t : Nat => Int.ofNat (succ (pred t))) (Nat.mul_one e_nat).
    //     LHS = Int.ofNat (succ (pred (Nat.mul e_nat 1))) = eff_prod,
    //     RHS = Int.ofNat (succ (pred e_nat)) ≡ Int.ofNat e_nat = e_int (def-eq).
    let cong_f = {
        let mut d = EnvDeclBuilder::child_of(&fb);
        let (t_id, t) = d.fresh_local(c.nat.clone());
        let body = c.of_nat(c.succ(c.pred(t)));
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body))
    };
    let nat_mul_e_one = c.nmul(e_nat.clone(), c.nat_one());
    let nat_mul_one_proof = Expr::app(c.nat_mul_one.clone(), e_nat.clone());
    let step_b = c.congr_nat_int(nat_mul_e_one, e_nat.clone(), cong_f, nat_mul_one_proof);
    // eL = trans step_a step_b : goal_lhs = e_int.
    let e_l = c.trans_int(
        goal_lhs.clone(),
        eff_prod.clone(),
        e_int.clone(),
        step_a,
        step_b,
    );
    // symm eL : e_int = goal_lhs.
    let e_l_symm = c.symm_int(goal_lhs.clone(), e_int.clone(), e_l);

    // Transport core's LHS (e_int → goal_lhs) with motive fun L => Int.lt L na_x.
    let motive_lhs = {
        let mut d = EnvDeclBuilder::child_of(&fb);
        let (l_id, l) = d.fresh_local(c.int.clone());
        let body = c.ilt(l, na_x.clone());
        d.finish_child(d.mk_lam(l_id, BinderInfo::Default, c.int.clone(), body))
    };
    // core1 : Int.lt goal_lhs na_x.
    let core1 = Expr::apps(
        c.eq_subst.clone(),
        [
            c.int.clone(),
            motive_lhs,
            e_int.clone(),
            goal_lhs.clone(),
            e_l_symm,
            core,
        ],
    );

    // eR : na_x = Int.mul na_x int_one  := symm (Int.mul_one na_x).
    let e_r = c.symm_int(
        goal_rhs.clone(),
        na_x.clone(),
        Expr::app(c.int_mul_one.clone(), na_x.clone()),
    );
    // Transport core1's RHS (na_x → goal_rhs) with motive fun R => Int.lt goal_lhs R.
    let motive_rhs = {
        let mut d = EnvDeclBuilder::child_of(&fb);
        let (r_id, r) = d.fresh_local(c.int.clone());
        let body = c.ilt(goal_lhs.clone(), r);
        d.finish_child(d.mk_lam(r_id, BinderInfo::Default, c.int.clone(), body))
    };
    // core2 : Int.lt goal_lhs goal_rhs ≡ the reduced goal.
    let core2 = Expr::apps(
        c.eq_subst.clone(),
        [
            c.int.clone(),
            motive_rhs,
            na_x.clone(),
            goal_rhs.clone(),
            e_r,
            core1,
        ],
    );

    // Exists.intro Nat pred (succ e) core2  : ∃ N, Rat.lt 1 (Rat.mul (mk p) (ofNat 2^N)).
    let mk_p = c.quot_mk(p.clone());
    let pred = exists_pred(c, &fb, mk_p);
    let intro = Expr::apps(
        c.exists_intro.clone(),
        [c.nat.clone(), pred, succ_e.clone(), core2],
    );

    let lam = fb.mk_lam(hm_id, BinderInfo::Default, hm_ty, intro);
    let lam = fb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam);
    fb.finish_child(lam)
}

/// `core : Int.lt e_int (Int.mul na x_int)` where `na = ofNat (succ m)`.
#[allow(clippy::too_many_arguments)]
fn build_core(
    c: &WitnessConsts,
    parent: &EnvDeclBuilder,
    na: &Expr,
    e_nat: &Expr,
    e_int: &Expr,
    succ_e: &Expr,
    x_int: &Expr,
    na_x: &Expr,
    _int_one: &Expr,
    m: &Expr,
    hm: &Expr,
) -> Expr {
    // core_lt : Int.lt e_int x_int.
    //   ≡ Int.le (Int.ofNat (succ e_nat)) x_int  (Int.lt (ofNat e)(ofNat M)
    //     ≡ Int.le (ofNat (succ e)) (ofNat M)), and
    //   Int.ofNat_le_ofNat_of_le (succ e_nat) (2^(succ e_nat)) (Nat.lt_two_pow_succ_self e_nat)
    //     : Int.le (ofNat (succ e_nat)) (ofNat 2^(succ e_nat)).
    let two_pow_succ_e = c.two_pow(succ_e.clone());
    let h_nat_lt = Expr::app(c.nat_lt_two_pow_succ.clone(), e_nat.clone());
    let core_lt = Expr::apps(
        c.int_ofnat_le_ofnat.clone(),
        [succ_e.clone(), two_pow_succ_e.clone(), h_nat_lt],
    );

    // le_step : Int.le x_int (Int.mul na x_int).
    //   one_le_na : Int.le (ofNat 1) na.
    //     na = ofNat (succ m); Int.ofNat_le_ofNat_of_le 1 (succ m) h1le
    //     transported across hm (na = ofNat (succ m)) backwards.
    //   First build at the ofNat (succ m) form, then subst by symm hm.
    let int_one = c.of_nat(c.nat_one());
    let ofnat_succ_m = c.of_nat(c.succ(m.clone()));
    // h1le_nat : Nat.le 1 (succ m) ≡ Nat.le (succ 0) (succ m)
    //   := Nat.succ_le_succ Nat.zero m (Nat.zero_le m).
    let h1le_nat = Expr::apps(
        c.nat_succ_le_succ.clone(),
        [
            c.nat_zero.clone(),
            m.clone(),
            Expr::app(c.nat_zero_le.clone(), m.clone()),
        ],
    );
    // one_le_ofnat_succ_m : Int.le (ofNat 1) (ofNat (succ m)).
    let one_le_ofnat_succ_m = Expr::apps(
        c.int_ofnat_le_ofnat.clone(),
        [c.nat_one(), c.succ(m.clone()), h1le_nat],
    );
    // Transport to Int.le (ofNat 1) na via symm hm : ofNat (succ m) = na.
    let hm_symm = c.symm_int(na.clone(), ofnat_succ_m.clone(), hm.clone());
    let motive_one_le = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (q_id, q) = d.fresh_local(c.int.clone());
        let body = c.ile(int_one.clone(), q);
        d.finish_child(d.mk_lam(q_id, BinderInfo::Default, c.int.clone(), body))
    };
    let one_le_na = Expr::apps(
        c.eq_subst.clone(),
        [
            c.int.clone(),
            motive_one_le,
            ofnat_succ_m.clone(),
            na.clone(),
            hm_symm,
            one_le_ofnat_succ_m,
        ],
    );

    // zero_le_x : Int.le (Int.ofNat 0) x_int := Int.ofNat_zero_le (2^(succ e)).
    let zero_le_x = Expr::app(c.int_ofnat_zero_le.clone(), two_pow_succ_e.clone());

    // mul_le : Int.le (Int.mul int_one x_int) (Int.mul na x_int).
    let mul_le = Expr::apps(
        c.int_mul_le_nonneg_right.clone(),
        [
            int_one.clone(),
            na.clone(),
            x_int.clone(),
            one_le_na,
            zero_le_x,
        ],
    );
    // one_mul_x : Int.mul int_one x_int = x_int  (Int.one_mul x_int).
    let one_mul_x = Expr::app(c.int_one_mul.clone(), x_int.clone());
    let mul_one_x = c.imul(int_one.clone(), x_int.clone());
    // Transport mul_le's LHS (int_one·x → x) with motive fun L => Int.le L (na·x).
    let motive_le_lhs = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (l_id, l) = d.fresh_local(c.int.clone());
        let body = c.ile(l, na_x.clone());
        d.finish_child(d.mk_lam(l_id, BinderInfo::Default, c.int.clone(), body))
    };
    // le_step : Int.le x_int (Int.mul na x_int).
    let le_step = Expr::apps(
        c.eq_subst.clone(),
        [
            c.int.clone(),
            motive_le_lhs,
            mul_one_x,
            x_int.clone(),
            one_mul_x,
            mul_le,
        ],
    );

    // core := Int.lt_of_lt_of_le e_int x_int na_x core_lt le_step.
    Expr::apps(
        c.int_lt_of_lt_of_le.clone(),
        [e_int.clone(), x_int.clone(), na_x.clone(), core_lt, le_step],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_rat_exists_pow_gt()
            .expect("register Rat.exists_pow_gt");
        env.register_rat_exists_pow_gt().expect("idempotent");
        env
    }

    #[test]
    fn test_rat_exists_pow_gt_constructive() {
        let env = env();
        let nm = Name::from_string("Rat.exists_pow_gt");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("must kernel-check");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty (foundational-only), got {:?}",
            env.axiom_deps(&nm)
        );
    }
}
