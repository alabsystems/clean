// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive demotions of the `Nat.*` arithmetic ordering lemmas
//! (`add_le_add*`, `mul_le_mul*`, the `lt`-family, and `Nat.sub_le`) from
//! `Declaration::Axiom` to kernel-checked `Declaration::Theorem`s with empty
//! domain-axiom closures.
//!
//! These were previously registered as `Declaration::Axiom` stubs in
//! `order_arith.rs`:
//!
//! - `Nat.add_le_add_left`  : `∀ a b, Nat.le a b → ∀ c, Nat.le (a+c sym) (..)`
//! - `Nat.add_le_add_right`
//! - `Nat.add_le_add`
//! - `Nat.mul_le_mul_right` (mirror of the already-demoted `Nat.mul_le_mul_left`)
//! - `Nat.mul_le_mul`
//! - `Nat.add_lt_add_left` / `Nat.add_lt_add_right` / `Nat.add_lt_add` — the
//!   `lt`-family, via `Nat.lt a b ≡ Nat.le (Nat.succ a) b`.
//! - `Nat.mul_lt_mul_left` — positivity (`0 < c`) dispatched through
//!   `Nat.add_le_add_left` at the increment `Nat.succ 0`.
//! - `Nat.sub_le` — via the `Nat.pred_le` helper (also registered here).
//!
//! Each legacy axiom site in `order_arith.rs` is now guarded by a `get_const`
//! check so that when `init_nat_arith_order` has already registered the
//! Theorem form, the legacy `Declaration::Axiom` registration is skipped
//! (idempotent no-op). The Theorem form therefore wins on every init path.
//!
//! # Proof strategy
//!
//! All proofs are built from the `Nat.le` inductive (`Nat.le.refl`,
//! `Nat.le.step`, `Nat.le.rec`), `Nat.rec`, and the *already constructive*
//! support lemmas `Nat.succ_le_succ`, `Nat.le_trans`, `Nat.le_add_right`,
//! `Nat.zero_le`, and `Nat.mul_le_mul_left` (all `Declaration::Theorem`s with
//! empty axiom closures). No `Declaration::Axiom` and no trust markers
//! (`sorry`, `sorryAx`, `trustedArith`, `trustedAy`) are referenced, so
//! `env.axiom_deps(name)` is empty for each and
//! `env.proof_quality(name) == ProofQuality::Constructive`.
//!
//! Key definitional-equality facts used (both recurse on their *second*
//! argument, per `data_types_nat.rs`):
//!
//! - `Nat.add x (Nat.succ k) ≡ Nat.succ (Nat.add x k)` and `Nat.add x 0 ≡ x`.
//! - `Nat.mul x (Nat.succ k) ≡ Nat.add (Nat.mul x k) x` and `Nat.mul x 0 ≡ 0`.
//!
//! 1. **`Nat.add_le_add_left : ∀ a b, Nat.le a b → ∀ c, Nat.le (c+a) (c+b)`** —
//!    induction on `h : Nat.le a b` via `Nat.le.rec` (parameter `a`) with
//!    motive `fun t _ => Nat.le (c+a) (c+t)`. Refl: `Nat.le.refl (c+a)`. Step:
//!    `Nat.le.step (c+a) (c+t) ih` (`c + succ t ≡ succ (c + t)`).
//!
//! 2. **`Nat.add_le_add_right : ∀ a b, Nat.le a b → ∀ c, Nat.le (a+c) (b+c)`** —
//!    induction on `c` via `Nat.rec` with motive `fun t => Nat.le (a+t) (b+t)`.
//!    Base (`t = 0`): `a+0 ≡ a`, `b+0 ≡ b`, witnessed by `h`. Step:
//!    `Nat.succ_le_succ (a+k) (b+k) ih` (`x + succ k ≡ succ (x + k)`).
//!
//! 3. **`Nat.add_le_add : ∀ a b c d, Nat.le a b → Nat.le c d → Nat.le (a+c) (b+d)`** —
//!    `Nat.le_trans (a+c) (b+c) (b+d) (add_le_add_right a b h1 c)
//!    (add_le_add_left c d h2 b)`.
//!
//! 4. **`Nat.mul_le_mul_right : ∀ a b c, Nat.le a b → Nat.le (a*c) (b*c)`** —
//!    induction on `c` via `Nat.rec` with motive `fun t => Nat.le (a*t) (b*t)`.
//!    Base (`t = 0`): `a*0 ≡ 0`, `b*0 ≡ 0`, witnessed by `Nat.le.refl 0`. Step:
//!    `a * succ k ≡ (a*k) + a`, so `Nat.add_le_add (a*k) (b*k) a b ih h`.
//!
//! 5. **`Nat.mul_le_mul : ∀ {n₁ m₁ n₂ m₂}, n₁ ≤ n₂ → m₁ ≤ m₂ → n₁*m₁ ≤ n₂*m₂`**
//!    (Lean core's real signature — hypotheses pair 1st-with-3rd and
//!    2nd-with-4th, result multiplies adjacent binders) —
//!    `Nat.le_trans (n₁*m₁) (n₂*m₁) (n₂*m₂) (mul_le_mul_right n₁ n₂ m₁ h₁)
//!    (mul_le_mul_left m₁ m₂ n₂ h₂)`.
//!
//! Tracking: #3604 (kernel-soundness arithmetic-ordering demotion vein).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::ConstantKind;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Kernel constants reused across the arithmetic-order proof terms.
struct NatArithOrderConsts {
    nat: Expr,
    zero: Expr,
    succ: Expr,
    add: Expr,
    mul: Expr,
    sub: Expr,
    pred: Expr,
    /// `Nat.rec.{0}` — Prop motive.
    nat_rec: Expr,
    le: Expr,
    lt: Expr,
    le_refl_ctor: Expr,
    le_step_ctor: Expr,
    le_rec: Expr,
    le_trans_thm: Expr,
    le_of_lt_thm: Expr,
    succ_le_succ_thm: Expr,
    add_le_add_left_thm: Expr,
    add_le_add_right_thm: Expr,
    add_le_add_thm: Expr,
    add_lt_add_right_thm: Expr,
    mul_le_mul_left_thm: Expr,
    mul_le_mul_right_thm: Expr,
    pred_le_thm: Expr,
}

impl NatArithOrderConsts {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            sub: Expr::const_(Name::from_string("Nat.sub"), vec![]),
            pred: Expr::const_(Name::from_string("Nat.pred"), vec![]),
            nat_rec: Expr::const_(
                Name::from_string("Nat.rec"),
                vec![crate::level::Level::zero()],
            ),
            le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            lt: Expr::const_(Name::from_string("Nat.lt"), vec![]),
            le_refl_ctor: Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
            le_step_ctor: Expr::const_(Name::from_string("Nat.le.step"), vec![]),
            le_rec: Expr::const_(Name::from_string("Nat.le.rec"), vec![]),
            le_trans_thm: Expr::const_(Name::from_string("Nat.le_trans"), vec![]),
            le_of_lt_thm: Expr::const_(Name::from_string("Nat.le_of_lt"), vec![]),
            succ_le_succ_thm: Expr::const_(Name::from_string("Nat.succ_le_succ"), vec![]),
            add_le_add_left_thm: Expr::const_(Name::from_string("Nat.add_le_add_left"), vec![]),
            add_le_add_right_thm: Expr::const_(Name::from_string("Nat.add_le_add_right"), vec![]),
            add_le_add_thm: Expr::const_(Name::from_string("Nat.add_le_add"), vec![]),
            add_lt_add_right_thm: Expr::const_(Name::from_string("Nat.add_lt_add_right"), vec![]),
            mul_le_mul_left_thm: Expr::const_(Name::from_string("Nat.mul_le_mul_left"), vec![]),
            mul_le_mul_right_thm: Expr::const_(Name::from_string("Nat.mul_le_mul_right"), vec![]),
            pred_le_thm: Expr::const_(Name::from_string("Nat.pred_le"), vec![]),
        }
    }

    fn add_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.add.clone(), [x, y])
    }

    fn mul_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.mul.clone(), [x, y])
    }

    fn sub_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.sub.clone(), [x, y])
    }

    fn pred_of(&self, x: Expr) -> Expr {
        Expr::app(self.pred.clone(), x)
    }

    fn succ_of(&self, x: Expr) -> Expr {
        Expr::app(self.succ.clone(), x)
    }

    fn le_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.le.clone(), [x, y])
    }

    fn lt_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.lt.clone(), [x, y])
    }

    /// `@Nat.le.refl n : Nat.le n n`.
    fn le_refl_app(&self, n: Expr) -> Expr {
        Expr::app(self.le_refl_ctor.clone(), n)
    }

    /// `@Nat.le.step n m h : Nat.le n (Nat.succ m)`.
    fn le_step(&self, n: Expr, m: Expr, h: Expr) -> Expr {
        Expr::apps(self.le_step_ctor.clone(), [n, m, h])
    }

    /// `Nat.le_trans a b c hab hbc : Nat.le a c` (raw `Nat.le`, accepted by defeq
    /// through the reducible `instLENat`).
    fn le_trans(&self, a: Expr, b: Expr, c: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.le_trans_thm.clone(), [a, b, c, hab, hbc])
    }
}

impl Environment {
    /// Register the `Nat.*` arithmetic ordering lemmas as constructive
    /// `Declaration::Theorem`s (#3604).
    ///
    /// Registers (in dependency order, each idempotent on `get_const`):
    ///
    /// - `Nat.add_le_add_left`
    /// - `Nat.add_le_add_right`
    /// - `Nat.add_le_add`
    /// - `Nat.mul_le_mul_right`
    /// - `Nat.mul_le_mul`
    ///
    /// Must be called *before* the legacy axiom registration sites in
    /// `init_nat_add_ord` / `init_nat_mul_ord` so the Theorem form wins; those
    /// sites carry a `get_const` guard and become no-ops once the Theorem has
    /// been registered here.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment.
    /// ENSURES: On success, the five lemmas above are `Declaration::Theorem`s
    ///          with `proof_quality == Constructive` and empty axiom closures.
    /// ENSURES: Idempotent.
    pub(crate) fn register_nat_arith_order_proofs(&mut self) -> Result<(), EnvError> {
        // SOUNDNESS: import-mode Nat core arithmetic cluster gate — the whole
        // add/mul/sub order-lemma family here is stated over the import-gated
        // Nat.add/Nat.mul/Nat.sub seeds (see data_types_nat.rs::init_nat); the
        // genuine olean lemmas import through the checked path instead.
        // Default lane byte-identical.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.init_nat()?; // Nat, Nat.zero, Nat.succ, Nat.add, Nat.mul, Nat.rec
        self.init_le()?; // Nat.le, Nat.le.refl, Nat.le.step, Nat.le.rec
                         // Constructive support lemmas (`Nat.succ_le_succ`, `Nat.le_refl`).
        self.init_nat_top_level_ordering()?;
        // `Nat.le_trans` (constructive).
        self.register_nat_le_trans_proof()?;
        // `Nat.mul_le_mul_left`, `Nat.le_add_right`, `Nat.zero_le` (constructive).
        self.register_nat_mul_le_mul_left_proof()?;

        // `Nat.le_of_lt` (constructive, registered by `init_nat_top_level_ordering`).

        let c = NatArithOrderConsts::new();
        self.register_nat_add_le_add_left(&c)?;
        self.register_nat_add_le_add_right(&c)?;
        self.register_nat_add_le_add(&c)?;
        self.register_nat_mul_le_mul_right(&c)?;
        self.register_nat_mul_le_mul(&c)?;
        // `Nat.lt`-family and `Nat.sub` order lemmas (#3604 lt cluster). All flow
        // through the constructive `le`-family above plus `Nat.lt`'s reducible
        // unfolding `Nat.lt a b ≡ Nat.le (Nat.succ a) b`.
        self.register_nat_pred_le(&c)?;
        self.register_nat_add_lt_add_left(&c)?;
        self.register_nat_add_lt_add_right(&c)?;
        self.register_nat_add_lt_add(&c)?;
        self.register_nat_mul_lt_mul_left(&c)?;
        self.register_nat_sub_le(&c)?;
        Ok(())
    }

    /// `Nat.pred_le : ∀ n : Nat, Nat.le (Nat.pred n) n`.
    ///
    /// Helper backing `Nat.sub_le`. Induction on `n` via `Nat.rec` with motive
    /// `fun t => Nat.le (Nat.pred t) t`. Base (`t = 0`): `Nat.pred 0 ≡ 0`,
    /// witnessed by `Nat.le.refl 0`. Step (`t = succ k`): `Nat.pred (succ k) ≡ k`,
    /// so the goal is `Nat.le k (succ k)`, witnessed by
    /// `Nat.le.step k k (Nat.le.refl k)`.
    fn register_nat_pred_le(&mut self, c: &NatArithOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.pred_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());

        // Type: ∀ n : Nat, Nat.le (Nat.pred n) n
        let type_ = {
            let concl = c.le_of(c.pred_of(n.clone()), n.clone());
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
            b.finish(e)
        };

        // motive: fun (t : Nat) => Nat.le (Nat.pred t) t
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let body = c.le_of(c.pred_of(t.clone()), t.clone());
            let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
            mb.finish_child(lam)
        };
        // base (t = 0): `Nat.pred 0 ≡ 0`, so `Nat.le 0 0` = `Nat.le.refl 0`.
        let base = c.le_refl_app(c.zero.clone());
        // step: fun (k : Nat) (_ih : Nat.le (Nat.pred k) k) =>
        //   Nat.le.step k k (Nat.le.refl k)
        //     : Nat.le k (succ k) ≡ Nat.le (Nat.pred (succ k)) (succ k)
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(c.nat.clone());
            let ih_type = c.le_of(c.pred_of(k.clone()), k.clone());
            let (ih_id, _ih) = sb.fresh_local(ih_type.clone());
            // Nat.le k (succ k) via Nat.le.step k k (Nat.le.refl k).
            let body = c.le_step(k.clone(), k.clone(), c.le_refl_app(k.clone()));
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
            let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_ih);
            sb.finish_child(lam_k)
        };

        let value = {
            let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, n.clone()]);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec_app);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked `Nat.rec` term over `Nat.pred` (reducible
        // Definition). Uses only `Nat.le.refl`/`Nat.le.step` constructors; no
        // `Declaration::Axiom`, no `sorry`, no self-reference.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.add_lt_add_left : ∀ a b, Nat.lt a b → ∀ c, Nat.lt (c+a) (c+b)`.
    ///
    /// `Nat.lt a b ≡ Nat.le (Nat.succ a) b`, so `h : Nat.le (Nat.succ a) b`.
    /// The goal `Nat.lt (c+a) (c+b) ≡ Nat.le (Nat.succ (c+a)) (c+b)`. Since
    /// `Nat.add` recurses on its *second* argument, `c + Nat.succ a ≡
    /// Nat.succ (c+a)`, so `Nat.add_le_add_left (Nat.succ a) b h c :
    /// Nat.le (c + Nat.succ a) (c+b)` is *definitionally* the goal.
    fn register_nat_add_lt_add_left(&mut self, c: &NatArithOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.add_lt_add_left");
        if self.is_theorem(&name) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let h_type = c.lt_of(a.clone(), bb.clone());
        let (h_id, h) = b.fresh_local(h_type.clone());
        let (cc_id, cc) = b.fresh_local(c.nat.clone());

        // Type: ∀ a b, Nat.lt a b → ∀ c, Nat.lt (c+a) (c+b)
        let type_ = {
            let concl = c.lt_of(
                c.add_of(cc.clone(), a.clone()),
                c.add_of(cc.clone(), bb.clone()),
            );
            let e = b.mk_pi(cc_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type.clone(), e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // value: fun a b (h : Nat.le (succ a) b) c =>
        //   Nat.add_le_add_left (succ a) b h c : Nat.le (c + succ a) (c + b)
        //     ≡ Nat.le (succ (c+a)) (c+b) ≡ Nat.lt (c+a) (c+b)
        let value = {
            let succ_a = c.succ_of(a.clone());
            let inner = Expr::apps(
                c.add_le_add_left_thm.clone(),
                [succ_a, bb.clone(), h.clone(), cc.clone()],
            );
            let e = b.mk_lam(cc_id, BinderInfo::Default, c.nat.clone(), inner);
            let e = b.mk_lam(h_id, BinderInfo::Default, h_type, e);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked. `Nat.lt`/`Nat.add` reductions plus the
        // constructive `Nat.add_le_add_left`. Replaces the legacy
        // `Declaration::Axiom` in `order_arith.rs::init_nat_add_ord`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.add_lt_add_right : ∀ a b, Nat.lt a b → ∀ c, Nat.lt (a+c) (b+c)`.
    ///
    /// `h : Nat.le (Nat.succ a) b`. Induction on `c` via `Nat.rec` with motive
    /// `fun t => Nat.le (Nat.succ (a+t)) (b+t)` (the unfolded `Nat.lt (a+t)(b+t)`).
    /// Base (`t = 0`): `a+0 ≡ a`, `b+0 ≡ b`, so the motive at 0 is
    /// `Nat.le (Nat.succ a) b` = `h`. Step (`t = succ k`): `x + succ k ≡
    /// Nat.succ (x+k)`, so the goal `Nat.le (Nat.succ (Nat.succ (a+k)))
    /// (Nat.succ (b+k))` is `Nat.succ_le_succ (Nat.succ (a+k)) (b+k) ih`.
    fn register_nat_add_lt_add_right(&mut self, c: &NatArithOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.add_lt_add_right");
        if self.is_theorem(&name) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let h_type = c.lt_of(a.clone(), bb.clone());
        let (h_id, h) = b.fresh_local(h_type.clone());
        let (cc_id, cc) = b.fresh_local(c.nat.clone());

        // Type: ∀ a b, Nat.lt a b → ∀ c, Nat.lt (a+c) (b+c)
        let type_ = {
            let concl = c.lt_of(
                c.add_of(a.clone(), cc.clone()),
                c.add_of(bb.clone(), cc.clone()),
            );
            let e = b.mk_pi(cc_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type.clone(), e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // motive: fun (t : Nat) => Nat.le (Nat.succ (a+t)) (b+t)
        // (defeq to `Nat.lt (a+t) (b+t)`).
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let body = c.le_of(
                c.succ_of(c.add_of(a.clone(), t.clone())),
                c.add_of(bb.clone(), t.clone()),
            );
            let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
            mb.finish_child(lam)
        };
        // base (t = 0): `a+0 ≡ a`, `b+0 ≡ b`, so motive at 0 is
        // `Nat.le (Nat.succ a) b` = `h` (the unfolded `Nat.lt a b`).
        let base = h.clone();
        // step: fun (k : Nat) (ih : Nat.le (Nat.succ (a+k)) (b+k)) =>
        //   Nat.succ_le_succ (Nat.succ (a+k)) (b+k) ih
        //     : Nat.le (Nat.succ (Nat.succ (a+k))) (Nat.succ (b+k))
        //     ≡ Nat.le (Nat.succ (a + succ k)) (b + succ k)
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(c.nat.clone());
            let succ_add_a_k = c.succ_of(c.add_of(a.clone(), k.clone()));
            let add_b_k = c.add_of(bb.clone(), k.clone());
            let ih_type = c.le_of(succ_add_a_k.clone(), add_b_k.clone());
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let body = Expr::apps(c.succ_le_succ_thm.clone(), [succ_add_a_k, add_b_k, ih]);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
            let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_ih);
            sb.finish_child(lam_k)
        };

        let value = {
            let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, cc.clone()]);
            let e = b.mk_lam(cc_id, BinderInfo::Default, c.nat.clone(), rec_app);
            let e = b.mk_lam(h_id, BinderInfo::Default, h_type, e);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked `Nat.rec` term. `Nat.lt`/`Nat.add`
        // reductions plus the constructive `Nat.succ_le_succ`. Replaces the
        // legacy `Declaration::Axiom` in `order_arith.rs::init_nat_add_ord`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.add_lt_add : ∀ a b c d, Nat.lt a b → Nat.lt c d → Nat.lt (a+c) (b+d)`.
    ///
    /// `Nat.le_trans (Nat.succ (a+c)) (b+c) (b+d) X Y` where
    /// `X = Nat.add_lt_add_right a b h1 c : Nat.lt (a+c)(b+c) ≡
    /// Nat.le (Nat.succ (a+c)) (b+c)` and
    /// `Y = Nat.add_le_add_left c d (Nat.le_of_lt c d h2) b : Nat.le (b+c)(b+d)`.
    /// The result `Nat.le (Nat.succ (a+c)) (b+d)` is defeq to `Nat.lt (a+c)(b+d)`.
    fn register_nat_add_lt_add(&mut self, c: &NatArithOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.add_lt_add");
        if self.is_theorem(&name) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let (cc_id, cc) = b.fresh_local(c.nat.clone());
        let (d_id, d) = b.fresh_local(c.nat.clone());
        let h1_type = c.lt_of(a.clone(), bb.clone());
        let (h1_id, h1) = b.fresh_local(h1_type.clone());
        let h2_type = c.lt_of(cc.clone(), d.clone());
        let (h2_id, h2) = b.fresh_local(h2_type.clone());

        // Type: ∀ a b c d, Nat.lt a b → Nat.lt c d → Nat.lt (a+c) (b+d)
        let type_ = {
            let concl = c.lt_of(
                c.add_of(a.clone(), cc.clone()),
                c.add_of(bb.clone(), d.clone()),
            );
            let e = b.mk_pi(h2_id, BinderInfo::Default, h2_type.clone(), concl);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_type.clone(), e);
            let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(cc_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // value: Nat.le_trans (succ (a+c)) (b+c) (b+d)
        //          (Nat.add_lt_add_right a b h1 c)              : Nat.le (succ (a+c)) (b+c)
        //          (Nat.add_le_add_left c d (Nat.le_of_lt c d h2) b) : Nat.le (b+c) (b+d)
        let value = {
            let succ_add_a_c = c.succ_of(c.add_of(a.clone(), cc.clone()));
            let add_b_c = c.add_of(bb.clone(), cc.clone());
            let add_b_d = c.add_of(bb.clone(), d.clone());
            // X : Nat.lt (a+c) (b+c) ≡ Nat.le (succ (a+c)) (b+c)
            let left = Expr::apps(
                c.add_lt_add_right_thm.clone(),
                [a.clone(), bb.clone(), h1.clone(), cc.clone()],
            );
            // le_of_lt c d h2 : Nat.le c d (typeclass form, defeq to raw Nat.le).
            let le_c_d = Expr::apps(c.le_of_lt_thm.clone(), [cc.clone(), d.clone(), h2.clone()]);
            // Y : Nat.le (b+c) (b+d)
            let right = Expr::apps(
                c.add_le_add_left_thm.clone(),
                [cc.clone(), d.clone(), le_c_d, bb.clone()],
            );
            let body = c.le_trans(succ_add_a_c, add_b_c, add_b_d, left, right);
            let e = b.mk_lam(h2_id, BinderInfo::Default, h2_type, body);
            let e = b.mk_lam(h1_id, BinderInfo::Default, h1_type, e);
            let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(cc_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked composition of the constructive
        // `Nat.add_lt_add_right`, `Nat.add_le_add_left`, `Nat.le_of_lt`, and
        // `Nat.le_trans`. Replaces the legacy `Declaration::Axiom` in
        // `order_arith.rs::init_nat_add_ord`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.mul_lt_mul_left : ∀ a b c, Nat.lt 0 c → Nat.lt a b → Nat.lt (c*a) (c*b)`.
    ///
    /// `h1 : Nat.le (Nat.succ 0) c` (`= 1 ≤ c`), `h2 : Nat.le (Nat.succ a) b`.
    /// Goal `Nat.lt (c*a) (c*b) ≡ Nat.le (Nat.succ (c*a)) (c*b)`.
    /// `Nat.le_trans (Nat.succ (c*a)) (c*a + c) (c*b) A B` where:
    /// - `A = Nat.add_le_add_left (Nat.succ 0) c h1 (c*a) :
    ///   Nat.le (c*a + Nat.succ 0) (c*a + c)`; and `c*a + Nat.succ 0 ≡
    ///   Nat.succ (c*a + 0) ≡ Nat.succ (c*a)`.
    /// - `B = Nat.mul_le_mul_left (Nat.succ a) b h2 c :
    ///   Nat.le (c * Nat.succ a) (c*b)`; and `c * Nat.succ a ≡ (c*a) + c`
    ///   (`Nat.mul` recurses on its second argument).
    fn register_nat_mul_lt_mul_left(&mut self, c: &NatArithOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.mul_lt_mul_left");
        if self.is_theorem(&name) {
            return Ok(());
        }

        // IMPORT MODE (`suppress_lossy_structure_stubs`): WITHHOLD Clean's
        // hand-rolled `Nat.mul_lt_mul_left`. It is registered here with the
        // IMPLICATION signature `∀ a b c, 0 < c → a < b → c*a < c*b`, but Lean
        // core's genuine `Nat.mul_lt_mul_left` is an IFF:
        // `∀ {a b c}, 0 < a → (a*b < a*c ↔ b < c)`. These are different
        // theorems, so the implication Theorem SHADOWS (via `is_theorem`) the
        // real Iff on import, and every Mathlib proof that applies the Iff
        // (`Nat.lt_mul_iff_one_lt_right`, `Nat.mul_lt_mul_pow_succ`,
        // `Nat.lt_div_iff_mul_lt`, … all do `(Nat.mul_lt_mul_left h).2` / rewrite
        // with it) fails `check_type` with a spurious TypeMismatch. Withholding
        // the stub lets the genuine kernel-checked Iff-form import register in
        // its place. The real `Nat.mul_lt_mul_left` lives in Lean's `Init` and is
        // in every Mathlib import closure, so the import lane loses nothing.
        //
        // SOUNDNESS: identical to the `Nat.decEq`/`Nat.succ_inj`/Nat-arith
        // overlay gates — suppression only lets the genuine Mathlib/Init constant
        // import in the overlay's place; nothing here touches
        // `is_def_eq`/`check_type`/`whnf`. The NON-import lane (`clean check`,
        // every Clean-native `Nat.mul_lt_mul_left` consumer and the ordering
        // tests) keeps Clean's implication form UNCHANGED. No production prelude
        // declaration consumes `Nat.mul_lt_mul_left`.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let (cc_id, cc) = b.fresh_local(c.nat.clone());
        let h1_type = c.lt_of(c.zero.clone(), cc.clone());
        let (h1_id, h1) = b.fresh_local(h1_type.clone());
        let h2_type = c.lt_of(a.clone(), bb.clone());
        let (h2_id, h2) = b.fresh_local(h2_type.clone());

        // Type: ∀ a b c, Nat.lt 0 c → Nat.lt a b → Nat.lt (c*a) (c*b)
        let type_ = {
            let concl = c.lt_of(
                c.mul_of(cc.clone(), a.clone()),
                c.mul_of(cc.clone(), bb.clone()),
            );
            let e = b.mk_pi(h2_id, BinderInfo::Default, h2_type.clone(), concl);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_type.clone(), e);
            let e = b.mk_pi(cc_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mul_c_a = c.mul_of(cc.clone(), a.clone());
            let mul_c_b = c.mul_of(cc.clone(), bb.clone());
            // succ (c*a) — also `≡ c*a + Nat.succ 0` and the trans midpoint
            // `c*a + c` `≡ c * Nat.succ a`.
            let succ_mul_c_a = c.succ_of(mul_c_a.clone());
            let mid = c.add_of(mul_c_a.clone(), cc.clone()); // c*a + c
            let succ_zero = c.succ_of(c.zero.clone());
            // A : Nat.le (c*a + succ 0) (c*a + c) ≡ Nat.le (succ (c*a)) (c*a + c)
            let lower = Expr::apps(
                c.add_le_add_left_thm.clone(),
                [succ_zero, cc.clone(), h1.clone(), mul_c_a.clone()],
            );
            // B : Nat.le (c * succ a) (c*b) ≡ Nat.le (c*a + c) (c*b)
            let upper = Expr::apps(
                c.mul_le_mul_left_thm.clone(),
                [c.succ_of(a.clone()), bb.clone(), cc.clone(), h2.clone()],
            );
            let body = c.le_trans(succ_mul_c_a, mid, mul_c_b, lower, upper);
            let e = b.mk_lam(h2_id, BinderInfo::Default, h2_type, body);
            let e = b.mk_lam(h1_id, BinderInfo::Default, h1_type, e);
            let e = b.mk_lam(cc_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked composition of the constructive
        // `Nat.add_le_add_left`, `Nat.mul_le_mul_left`, and `Nat.le_trans`,
        // discharging the positivity hypothesis `Nat.lt 0 c ≡ Nat.le 1 c`
        // through `Nat.add_le_add_left` at the increment `Nat.succ 0`. Replaces
        // the legacy `Declaration::Axiom` in `order_arith.rs::init_nat_mul_ord`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.sub_le : ∀ a b, Nat.le (Nat.sub a b) a`.
    ///
    /// Induction on `b` via `Nat.rec` with motive `fun t => Nat.le (a - t) a`.
    /// Base (`t = 0`): `a - 0 ≡ a`, witnessed by `Nat.le.refl a`. Step
    /// (`t = succ k`): `a - succ k ≡ Nat.pred (a - k)` (`Nat.sub` recurses on its
    /// second argument), so `Nat.le_trans (Nat.pred (a-k)) (a-k) a
    /// (Nat.pred_le (a-k)) ih`.
    fn register_nat_sub_le(&mut self, c: &NatArithOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.sub_le");
        if self.is_theorem(&name) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());

        // Type: ∀ a b, Nat.le (a - b) a
        let type_ = {
            let concl = c.le_of(c.sub_of(a.clone(), bb.clone()), a.clone());
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // motive: fun (t : Nat) => Nat.le (a - t) a
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let body = c.le_of(c.sub_of(a.clone(), t.clone()), a.clone());
            let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
            mb.finish_child(lam)
        };
        // base (t = 0): `a - 0 ≡ a`, so `Nat.le a a` = `Nat.le.refl a`.
        let base = c.le_refl_app(a.clone());
        // step: fun (k : Nat) (ih : Nat.le (a-k) a) =>
        //   Nat.le_trans (Nat.pred (a-k)) (a-k) a (Nat.pred_le (a-k)) ih
        //     : Nat.le (Nat.pred (a-k)) a ≡ Nat.le (a - succ k) a
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(c.nat.clone());
            let sub_a_k = c.sub_of(a.clone(), k.clone());
            let ih_type = c.le_of(sub_a_k.clone(), a.clone());
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let pred_sub = c.pred_of(sub_a_k.clone());
            let pred_le = Expr::app(c.pred_le_thm.clone(), sub_a_k.clone());
            let body = c.le_trans(pred_sub, sub_a_k, a.clone(), pred_le, ih);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
            let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_ih);
            sb.finish_child(lam_k)
        };

        let value = {
            let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, bb.clone()]);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), rec_app);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked `Nat.rec` term over `Nat.sub` (reducible
        // Definition). Uses only the constructive `Nat.pred_le` and
        // `Nat.le_trans`. Replaces the legacy `Declaration::Axiom` in
        // `order_arith.rs::init_nat_sub_ord`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.add_le_add_left : ∀ a b, Nat.le a b → ∀ c, Nat.le (c+a) (c+b)`.
    fn register_nat_add_le_add_left(&mut self, c: &NatArithOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.add_le_add_left");
        if self.is_theorem(&name) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let h_type = c.le_of(a.clone(), bb.clone());
        let (h_id, h) = b.fresh_local(h_type.clone());
        let (cc_id, cc) = b.fresh_local(c.nat.clone());

        // Type: ∀ a b, Nat.le a b → ∀ c, Nat.le (c+a) (c+b)
        let type_ = {
            let concl = c.le_of(
                c.add_of(cc.clone(), a.clone()),
                c.add_of(cc.clone(), bb.clone()),
            );
            let e = b.mk_pi(cc_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type.clone(), e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let add_c_a = c.add_of(cc.clone(), a.clone());

        // motive: fun (t : Nat) (_ : Nat.le a t) => Nat.le (c+a) (c+t)
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let le_a_t = c.le_of(a.clone(), t.clone());
            let (ht_id, _ht) = mb.fresh_local(le_a_t.clone());
            let body = c.le_of(add_c_a.clone(), c.add_of(cc.clone(), t.clone()));
            let lam_h = mb.mk_lam(ht_id, BinderInfo::Default, le_a_t, body);
            let lam_t = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), lam_h);
            mb.finish_child(lam_t)
        };
        // refl minor: Nat.le.refl (c+a)
        let minor_refl = c.le_refl_app(add_c_a.clone());
        // step minor: fun {t} (_ : Nat.le a t) (ih : Nat.le (c+a) (c+t)) =>
        //   Nat.le.step (c+a) (c+t) ih : Nat.le (c+a) (succ (c+t)) ≡ Nat.le (c+a) (c + succ t)
        let minor_step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = sb.fresh_local(c.nat.clone());
            let le_a_t = c.le_of(a.clone(), t.clone());
            let (ht_id, _ht) = sb.fresh_local(le_a_t.clone());
            let add_c_t = c.add_of(cc.clone(), t.clone());
            let ih_type = c.le_of(add_c_a.clone(), add_c_t.clone());
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let body = c.le_step(add_c_a.clone(), add_c_t, ih);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
            let lam_h = sb.mk_lam(ht_id, BinderInfo::Default, le_a_t, lam_ih);
            let lam_t = sb.mk_lam(t_id, BinderInfo::Implicit, c.nat.clone(), lam_h);
            sb.finish_child(lam_t)
        };

        let value = {
            let rec_app = Expr::apps(
                c.le_rec.clone(),
                [
                    a.clone(),
                    motive,
                    minor_refl,
                    minor_step,
                    bb.clone(),
                    h.clone(),
                ],
            );
            // ∀-bind `c` *outside* the induction (motive closes over `c`).
            let e = b.mk_lam(cc_id, BinderInfo::Default, c.nat.clone(), rec_app);
            let e = b.mk_lam(h_id, BinderInfo::Default, h_type, e);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked `Nat.le.rec` term; replaces the legacy
        // `Declaration::Axiom` in `order_arith.rs::init_nat_add_ord`. No
        // `sorry`, no self-reference, no `Declaration::Axiom` dependency.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.add_le_add_right : ∀ a b, Nat.le a b → ∀ c, Nat.le (a+c) (b+c)`.
    fn register_nat_add_le_add_right(&mut self, c: &NatArithOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.add_le_add_right");
        if self.is_theorem(&name) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let h_type = c.le_of(a.clone(), bb.clone());
        let (h_id, h) = b.fresh_local(h_type.clone());
        let (cc_id, cc) = b.fresh_local(c.nat.clone());

        // Type: ∀ a b, Nat.le a b → ∀ c, Nat.le (a+c) (b+c)
        let type_ = {
            let concl = c.le_of(
                c.add_of(a.clone(), cc.clone()),
                c.add_of(bb.clone(), cc.clone()),
            );
            let e = b.mk_pi(cc_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type.clone(), e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // motive: fun (t : Nat) => Nat.le (a+t) (b+t)
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let body = c.le_of(
                c.add_of(a.clone(), t.clone()),
                c.add_of(bb.clone(), t.clone()),
            );
            let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
            mb.finish_child(lam)
        };
        // base (t = 0): `a+0 ≡ a`, `b+0 ≡ b`, so the motive at 0 is `Nat.le a b` = h.
        let base = h.clone();
        // step: fun (k : Nat) (ih : Nat.le (a+k) (b+k)) =>
        //   Nat.succ_le_succ (a+k) (b+k) ih
        //     : Nat.le (succ (a+k)) (succ (b+k)) ≡ Nat.le (a + succ k) (b + succ k)
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(c.nat.clone());
            let add_a_k = c.add_of(a.clone(), k.clone());
            let add_b_k = c.add_of(bb.clone(), k.clone());
            let ih_type = c.le_of(add_a_k.clone(), add_b_k.clone());
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let body = Expr::apps(c.succ_le_succ_thm.clone(), [add_a_k, add_b_k, ih]);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
            let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_ih);
            sb.finish_child(lam_k)
        };

        let value = {
            let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, cc.clone()]);
            let e = b.mk_lam(cc_id, BinderInfo::Default, c.nat.clone(), rec_app);
            let e = b.mk_lam(h_id, BinderInfo::Default, h_type, e);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked `Nat.rec` term; replaces the legacy
        // `Declaration::Axiom` in `order_arith.rs::init_nat_add_ord`. Depends
        // only on the constructive `Nat.succ_le_succ`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.add_le_add : ∀ a b c d, Nat.le a b → Nat.le c d → Nat.le (a+c) (b+d)`.
    fn register_nat_add_le_add(&mut self, c: &NatArithOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.add_le_add");
        if self.is_theorem(&name) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let (cc_id, cc) = b.fresh_local(c.nat.clone());
        let (d_id, d) = b.fresh_local(c.nat.clone());
        let h1_type = c.le_of(a.clone(), bb.clone());
        let (h1_id, h1) = b.fresh_local(h1_type.clone());
        let h2_type = c.le_of(cc.clone(), d.clone());
        let (h2_id, h2) = b.fresh_local(h2_type.clone());

        // Type: ∀ a b c d, Nat.le a b → Nat.le c d → Nat.le (a+c) (b+d)
        let type_ = {
            let concl = c.le_of(
                c.add_of(a.clone(), cc.clone()),
                c.add_of(bb.clone(), d.clone()),
            );
            let e = b.mk_pi(h2_id, BinderInfo::Default, h2_type.clone(), concl);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_type.clone(), e);
            let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(cc_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // value: Nat.le_trans (a+c) (b+c) (b+d)
        //          (Nat.add_le_add_right a b h1 c)   : Nat.le (a+c) (b+c)
        //          (Nat.add_le_add_left  c d h2 b)   : Nat.le (b+c) (b+d)
        let value = {
            let add_a_c = c.add_of(a.clone(), cc.clone());
            let add_b_c = c.add_of(bb.clone(), cc.clone());
            let add_b_d = c.add_of(bb.clone(), d.clone());
            let left = Expr::apps(
                c.add_le_add_right_thm.clone(),
                [a.clone(), bb.clone(), h1.clone(), cc.clone()],
            );
            let right = Expr::apps(
                c.add_le_add_left_thm.clone(),
                [cc.clone(), d.clone(), h2.clone(), bb.clone()],
            );
            let body = c.le_trans(add_a_c, add_b_c, add_b_d, left, right);
            let e = b.mk_lam(h2_id, BinderInfo::Default, h2_type, body);
            let e = b.mk_lam(h1_id, BinderInfo::Default, h1_type, e);
            let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(cc_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked composition of the constructive
        // `Nat.add_le_add_left`, `Nat.add_le_add_right`, and `Nat.le_trans`.
        // Replaces the legacy `Declaration::Axiom` in `init_nat_add_ord`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.mul_le_mul_right : ∀ a b c, Nat.le a b → Nat.le (a*c) (b*c)`.
    ///
    /// Mirror of the already-demoted `Nat.mul_le_mul_left`. Induction on `c`
    /// via `Nat.rec` with motive `fun t => Nat.le (a*t) (b*t)`. Base (`t = 0`):
    /// `a*0 ≡ 0`, `b*0 ≡ 0`, witnessed by `Nat.le.refl 0`. Step (`t = succ k`):
    /// `x * succ k ≡ (x*k) + x`, so `Nat.add_le_add (a*k) (b*k) a b ih h`.
    fn register_nat_mul_le_mul_right(&mut self, c: &NatArithOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.mul_le_mul_right");
        if self.is_theorem(&name) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let (cc_id, cc) = b.fresh_local(c.nat.clone());
        let h_type = c.le_of(a.clone(), bb.clone());
        let (h_id, h) = b.fresh_local(h_type.clone());

        // Type: ∀ a b c, Nat.le a b → Nat.le (a*c) (b*c)
        let type_ = {
            let concl = c.le_of(
                c.mul_of(a.clone(), cc.clone()),
                c.mul_of(bb.clone(), cc.clone()),
            );
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type.clone(), concl);
            let e = b.mk_pi(cc_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // motive: fun (t : Nat) => Nat.le (a*t) (b*t)
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let body = c.le_of(
                c.mul_of(a.clone(), t.clone()),
                c.mul_of(bb.clone(), t.clone()),
            );
            let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
            mb.finish_child(lam)
        };
        // base (t = 0): `a*0 ≡ 0`, `b*0 ≡ 0`, witnessed by Nat.le.refl 0.
        let base = c.le_refl_app(c.zero.clone());
        // step: fun (k : Nat) (ih : Nat.le (a*k) (b*k)) =>
        //   Nat.add_le_add (a*k) (b*k) a b ih h
        //     : Nat.le ((a*k)+a) ((b*k)+b) ≡ Nat.le (a * succ k) (b * succ k)
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(c.nat.clone());
            let mul_a_k = c.mul_of(a.clone(), k.clone());
            let mul_b_k = c.mul_of(bb.clone(), k.clone());
            let ih_type = c.le_of(mul_a_k.clone(), mul_b_k.clone());
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let body = Expr::apps(
                c.add_le_add_thm.clone(),
                [mul_a_k, mul_b_k, a.clone(), bb.clone(), ih, h.clone()],
            );
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
            let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_ih);
            sb.finish_child(lam_k)
        };

        let value = {
            let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, cc.clone()]);
            let e = b.mk_lam(h_id, BinderInfo::Default, h_type, rec_app);
            let e = b.mk_lam(cc_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked `Nat.rec` term; replaces the legacy
        // `Declaration::Axiom` in `order_arith.rs::init_nat_mul_ord`. Depends
        // only on the constructive `Nat.add_le_add`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.mul_le_mul : ∀ {n₁ m₁ n₂ m₂}, n₁ ≤ n₂ → m₁ ≤ m₂ → n₁*m₁ ≤ n₂*m₂`.
    ///
    /// FIDELITY: this must match Lean core's real signature EXACTLY. Lean's
    /// `Nat.mul_le_mul` binds `{n₁ m₁ n₂ m₂ : Nat}` and pairs the hypotheses
    /// as `(h₁ : n₁ ≤ n₂) (h₂ : m₁ ≤ m₂)`, concluding `n₁*m₁ ≤ n₂*m₂`. An
    /// earlier version of this prelude declaration used a *transposed* pairing
    /// (`∀ a b c d, a ≤ b → c ≤ d → a*c ≤ b*d`), which is a genuinely DIFFERENT
    /// theorem. Because this prelude stub shadows the olean import (the
    /// `is_theorem` guard below keeps the prelude version and the olean import
    /// never overwrites it), every real Mathlib proof that applied
    /// `Nat.mul_le_mul` with the real `{n₁ m₁ n₂ m₂}` argument order was
    /// rejected during kernel re-check: the term supplied for `h₁` proved
    /// `n₁ ≤ n₂`, but the transposed prelude type expected `n₁ ≤ m₁`, so
    /// `is_def_eq` correctly (given the wrong type) rejected it. Matching
    /// Lean's pairing here is a pure prelude import-fidelity fix — no kernel
    /// (`is_def_eq`/`whnf`/`infer`) change. The four Nat binders are `Implicit`
    /// to mirror Lean.
    fn register_nat_mul_le_mul(&mut self, c: &NatArithOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.mul_le_mul");
        if self.is_theorem(&name) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (n1_id, n1) = b.fresh_local(c.nat.clone());
        let (m1_id, m1) = b.fresh_local(c.nat.clone());
        let (n2_id, n2) = b.fresh_local(c.nat.clone());
        let (m2_id, m2) = b.fresh_local(c.nat.clone());
        let h1_type = c.le_of(n1.clone(), n2.clone());
        let (h1_id, h1) = b.fresh_local(h1_type.clone());
        let h2_type = c.le_of(m1.clone(), m2.clone());
        let (h2_id, h2) = b.fresh_local(h2_type.clone());

        // Type: ∀ {n₁ m₁ n₂ m₂}, n₁ ≤ n₂ → m₁ ≤ m₂ → n₁*m₁ ≤ n₂*m₂
        let type_ = {
            let concl = c.le_of(
                c.mul_of(n1.clone(), m1.clone()),
                c.mul_of(n2.clone(), m2.clone()),
            );
            let e = b.mk_pi(h2_id, BinderInfo::Default, h2_type.clone(), concl);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_type.clone(), e);
            let e = b.mk_pi(m2_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_pi(n2_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_pi(m1_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_pi(n1_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };

        // value: Nat.le_trans (n₁*m₁) (n₂*m₁) (n₂*m₂)
        //          (Nat.mul_le_mul_right n₁ n₂ m₁ h₁) : n₁*m₁ ≤ n₂*m₁
        //          (Nat.mul_le_mul_left  m₁ m₂ n₂ h₂) : n₂*m₁ ≤ n₂*m₂
        // `Nat.mul_le_mul_right a b c (h:a≤b) : a*c ≤ b*c`, at
        // `a := n₁, b := n₂, c := m₁` gives `n₁*m₁ ≤ n₂*m₁`.
        // `Nat.mul_le_mul_left  a b c (h:a≤b) : c*a ≤ c*b`, at
        // `a := m₁, b := m₂, c := n₂` gives `n₂*m₁ ≤ n₂*m₂`.
        let value = {
            let mul_n1_m1 = c.mul_of(n1.clone(), m1.clone());
            let mul_n2_m1 = c.mul_of(n2.clone(), m1.clone());
            let mul_n2_m2 = c.mul_of(n2.clone(), m2.clone());
            let left = Expr::apps(
                c.mul_le_mul_right_thm.clone(),
                [n1.clone(), n2.clone(), m1.clone(), h1.clone()],
            );
            let right = Expr::apps(
                c.mul_le_mul_left_thm.clone(),
                [m1.clone(), m2.clone(), n2.clone(), h2.clone()],
            );
            let body = c.le_trans(mul_n1_m1, mul_n2_m1, mul_n2_m2, left, right);
            let e = b.mk_lam(h2_id, BinderInfo::Default, h2_type, body);
            let e = b.mk_lam(h1_id, BinderInfo::Default, h1_type, e);
            let e = b.mk_lam(m2_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(n2_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(m1_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(n1_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked composition of the constructive
        // `Nat.mul_le_mul_right`, `Nat.mul_le_mul_left`, and `Nat.le_trans`.
        // Replaces the legacy `Declaration::Axiom` in `init_nat_mul_ord`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Whether `name` is already registered as a `Declaration::Theorem`.
    fn is_theorem(&self, name: &Name) -> bool {
        matches!(
            self.get_const(name).map(|i| i.kind),
            Some(ConstantKind::Theorem)
        )
    }
}
