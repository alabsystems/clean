// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive demotions of the `Nat.min` / `Nat.max` ordering lemmas from
//! `Declaration::Axiom` to kernel-checked `Declaration::Theorem`s with empty
//! domain-axiom closures.
//!
//! These were previously registered as `Declaration::Axiom` stubs in
//! `order_lemmas_minmax.rs`:
//!
//! - `Nat.min_le_left`  : `∀ a b, Nat.le (Nat.min a b) a`
//! - `Nat.min_le_right` : `∀ a b, Nat.le (Nat.min a b) b`
//! - `Nat.le_min`       : `∀ a b c, Nat.le c a → Nat.le c b → Nat.le c (Nat.min a b)`
//! - `Nat.min_comm`     : `∀ a b, Eq Nat (Nat.min a b) (Nat.min b a)`
//! - `Nat.le_max_left`  : `∀ a b, Nat.le a (Nat.max a b)`
//! - `Nat.le_max_right` : `∀ a b, Nat.le b (Nat.max a b)`
//! - `Nat.max_le`       : `∀ a b c, Nat.le a c → Nat.le b c → Nat.le (Nat.max a b) c`
//! - `Nat.max_comm`     : `∀ a b, Eq Nat (Nat.max a b) (Nat.max b a)`
//!
//! Each legacy axiom site in `order_lemmas_minmax.rs` is now guarded by a
//! `get_const` check so that when `register_nat_minmax_proofs` has already
//! registered the Theorem form, the legacy `Declaration::Axiom` registration is
//! skipped (idempotent no-op). The Theorem form therefore wins on every init
//! path.
//!
//! # Definitional facts
//!
//! `Nat.min` / `Nat.max` are reducible `Definition`s (see `order_ord.rs`):
//!
//! - `Nat.min a b ≡ @Bool.rec.{1} (fun _ => Nat) b a (Nat.ble a b)`
//!   (false-minor `b`, true-minor `a`).
//! - `Nat.max a b ≡ @Bool.rec.{1} (fun _ => Nat) a b (Nat.ble a b)`
//!   (false-minor `a`, true-minor `b`).
//!
//! `Nat.ble` (also reducible) reduces on closed prefixes:
//!
//! - `Nat.ble 0 n ≡ Bool.true` (for any `n`),
//! - `Nat.ble (Nat.succ k) 0 ≡ Bool.false`,
//! - `Nat.ble (Nat.succ k) (Nat.succ j) ≡ Nat.ble k j`.
//!
//! # Proof strategy
//!
//! All proofs are built from the `Nat.le` inductive (`Nat.le.refl`,
//! `Nat.le.step`, `Nat.le.rec`), `Nat.rec`, `Bool.rec`, `Eq` / `Eq.refl` /
//! `Eq.trans` / `Eq.symm` / `congrArg`, and the already-constructive support
//! lemmas `Nat.zero_le` and `Nat.succ_le_succ` (both `Declaration::Theorem`s
//! with empty axiom closures). No `Declaration::Axiom` and no trust markers
//! (`sorry`, `sorryAx`, `trustedArith`, `trustedAy`) are referenced, so
//! `env.axiom_deps(name)` is empty for each and
//! `env.proof_quality(name) == ProofQuality::Constructive`.
//!
//! - **`Nat.le_min` / `Nat.max_le`** — a single dependent `Bool.rec.{0}` over
//!   `Nat.ble a b`. For `le_min` the motive `fun bl => Nat.le c (Bool.rec b a bl)`
//!   has false-branch `Nat.le c b` (= `h2`) and true-branch `Nat.le c a`
//!   (= `h1`). `max_le` is the mirror.
//! - **`Nat.min_le_left` / `Nat.min_le_right` / `Nat.le_max_left` /
//!   `Nat.le_max_right`** — double `Nat.rec` over `a` then `b`, so that
//!   `Nat.ble` reduces at every leaf. The single non-degenerate leaf
//!   (`a = succ k`, `b = succ j`) lifts the inductive hypothesis through a
//!   dependent `Bool.rec.{0}` that pushes `Nat.succ` past the `Bool.rec`.
//! - **`Nat.min_comm` / `Nat.max_comm`** — double `Nat.rec` over `a` then `b`.
//!   Leaves are `Eq.refl`; the `(succ k, succ j)` leaf chains `congrArg Nat.succ`
//!   on the inductive hypothesis with two dependent-`Bool.rec` "succ-push"
//!   congruences via `Eq.trans` / `Eq.symm`.
//!
//! Tracking: #3604 (kernel-soundness arithmetic-ordering demotion vein, final
//! `Nat.min` / `Nat.max` cluster).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::ConstantKind;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Kernel constants reused across the min/max proof terms.
struct MinMaxConsts {
    nat: Expr,
    zero: Expr,
    succ: Expr,
    ble: Expr,
    min: Expr,
    max: Expr,
    bool_ty: Expr,
    /// `@Bool.rec.{1}` — `Nat`-valued (`Sort 1`) motive.
    bool_rec_nat: Expr,
    /// `@Bool.rec.{0}` — `Prop`-valued (`Sort 0`) motive.
    bool_rec_prop: Expr,
    /// `Nat.rec.{0}` — Prop motive.
    nat_rec: Expr,
    le: Expr,
    le_refl_ctor: Expr,
    zero_le_thm: Expr,
    succ_le_succ_thm: Expr,
    /// `Eq.{1}` on `Nat`.
    eq_const: Expr,
    eq_refl: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    /// `congrArg.{1,1}`.
    congr_arg: Expr,
}

impl MinMaxConsts {
    fn new() -> Self {
        let one = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            ble: Expr::const_(Name::from_string("Nat.ble"), vec![]),
            min: Expr::const_(Name::from_string("Nat.min"), vec![]),
            max: Expr::const_(Name::from_string("Nat.max"), vec![]),
            bool_ty: Expr::const_(Name::from_string("Bool"), vec![]),
            bool_rec_nat: Expr::const_(Name::from_string("Bool.rec"), vec![one.clone()]),
            bool_rec_prop: Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            le_refl_ctor: Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
            zero_le_thm: Expr::const_(Name::from_string("Nat.zero_le"), vec![]),
            succ_le_succ_thm: Expr::const_(Name::from_string("Nat.succ_le_succ"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![one.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![one.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![one.clone(), one]),
        }
    }

    fn succ_of(&self, n: Expr) -> Expr {
        Expr::app(self.succ.clone(), n)
    }

    fn ble_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.ble.clone(), [a, b])
    }

    fn min_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.min.clone(), [a, b])
    }

    fn max_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.max.clone(), [a, b])
    }

    fn le_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.le.clone(), [x, y])
    }

    fn eq_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.nat.clone(), x, y])
    }

    /// `@Nat.le.refl n : Nat.le n n`.
    fn le_refl_app(&self, n: Expr) -> Expr {
        Expr::app(self.le_refl_ctor.clone(), n)
    }

    /// `@Nat.zero_le n : Nat.le Nat.zero n`.
    fn zero_le_app(&self, n: Expr) -> Expr {
        Expr::app(self.zero_le_thm.clone(), n)
    }

    /// `@Nat.succ_le_succ n m : Nat.le n m → Nat.le (succ n) (succ m)`
    /// (partially applied — yields the lifting function).
    fn succ_le_succ_fn(&self, n: Expr, m: Expr) -> Expr {
        Expr::apps(self.succ_le_succ_thm.clone(), [n, m])
    }

    /// `@Eq.refl Nat x : Eq Nat x x`.
    fn eq_refl_app(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.nat.clone(), x])
    }

    /// `@Eq.symm Nat a b h : Eq Nat b a` (from `h : Eq Nat a b`).
    fn eq_symm_app(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.nat.clone(), a, b, h])
    }

    /// `@Eq.trans Nat a b c hab hbc : Eq Nat a c`.
    fn eq_trans_app(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.nat.clone(), a, b, cc, hab, hbc],
        )
    }

    /// `@congrArg Nat Nat a b Nat.succ h : Eq Nat (succ a) (succ b)`.
    fn congr_succ(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [
                self.nat.clone(),
                self.nat.clone(),
                a,
                b,
                self.succ.clone(),
                h,
            ],
        )
    }

    /// The constant `Nat`-valued motive `fun _ : Bool => Nat`.
    fn nat_motive(&self) -> Expr {
        Expr::lam(BinderInfo::Default, self.bool_ty.clone(), self.nat.clone())
    }

    /// `@Bool.rec.{1} (fun _ => Nat) false_minor true_minor scrut : Nat`.
    fn bool_rec_nat_app(&self, false_minor: Expr, true_minor: Expr, scrut: Expr) -> Expr {
        Expr::apps(
            self.bool_rec_nat.clone(),
            [self.nat_motive(), false_minor, true_minor, scrut],
        )
    }
}

impl Environment {
    /// Register the `Nat.min` / `Nat.max` ordering lemmas as constructive
    /// `Declaration::Theorem`s (#3604).
    ///
    /// Registers (each idempotent on `get_const`):
    /// `Nat.le_min`, `Nat.max_le`, `Nat.min_le_left`, `Nat.min_le_right`,
    /// `Nat.le_max_left`, `Nat.le_max_right`, `Nat.min_comm`, `Nat.max_comm`.
    ///
    /// Must be called *before* the legacy axiom registration sites in
    /// `init_nat_minmax_lemmas` so the Theorem form wins; those sites carry a
    /// `get_const` guard and become no-ops once the Theorem has been registered
    /// here.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment.
    /// ENSURES: On success, the eight lemmas above are `Declaration::Theorem`s
    ///          with `proof_quality == Constructive` and empty axiom closures.
    /// ENSURES: Idempotent.
    pub(crate) fn register_nat_minmax_proofs(&mut self) -> Result<(), EnvError> {
        self.init_nat()?; // Nat, Nat.zero, Nat.succ, Nat.rec
        self.init_nat_cmp()?; // Nat.ble
        self.init_bool()?; // Bool, Bool.rec
        self.init_nat_minmax()?; // Nat.min, Nat.max
        self.init_le()?; // Nat.le, Nat.le.refl, Nat.le.step, Nat.le.rec
        self.init_eq()?; // Eq, Eq.refl, Eq.trans, Eq.symm, congrArg
                         // Constructive support lemmas.
        self.init_nat_top_level_ordering()?; // Nat.succ_le_succ
        self.register_nat_zero_le_only()?; // Nat.zero_le

        let c = MinMaxConsts::new();
        self.register_nat_le_min(&c)?;
        self.register_nat_max_le(&c)?;
        self.register_nat_min_le_left(&c)?;
        self.register_nat_min_le_right(&c)?;
        self.register_nat_le_max_left(&c)?;
        self.register_nat_le_max_right(&c)?;
        self.register_nat_min_comm(&c)?;
        self.register_nat_max_comm(&c)?;
        self.register_nat_min_self(&c)?;
        self.register_nat_max_self(&c)?;
        Ok(())
    }

    /// `Nat.min_self : ∀ a, Eq Nat (Nat.min a a) a`.
    fn register_nat_min_self(&mut self, c: &MinMaxConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.min_self");
        if self.minmax_is_theorem(&name) {
            return Ok(());
        }
        self.register_minmax_self(c, &name, true)
    }

    /// `Nat.max_self : ∀ a, Eq Nat (Nat.max a a) a`.
    fn register_nat_max_self(&mut self, c: &MinMaxConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.max_self");
        if self.minmax_is_theorem(&name) {
            return Ok(());
        }
        self.register_minmax_self(c, &name, false)
    }

    /// Shared body of `Nat.min_self` (`is_min == true`) / `Nat.max_self`
    /// (`is_min == false`).
    ///
    /// Both have shape `∀ a, Eq Nat (OP a a) a`. The definitions reduce to
    /// `OP a a ≡ @Bool.rec (fun _ => Nat) a a (Nat.ble a a)` — i.e. BOTH the
    /// `false` and `true` minors of the `Bool.rec` are the same `a`, regardless
    /// of `min` vs `max` (min selects `Bool.rec b a`, max selects `Bool.rec a b`,
    /// and with `b = a` both collapse to `Bool.rec a a`). The proof is a single
    /// dependent `Bool.rec.{0}` over the scrutinee `Nat.ble a a` with motive
    /// `fun bl => Eq Nat (@Bool.rec (fun _ => Nat) a a bl) a`; in each branch the
    /// `Bool.rec` reduces to `a`, so both minors are `Eq.refl a`. No induction on
    /// `a` is required.
    fn register_minmax_self(
        &mut self,
        c: &MinMaxConsts,
        name: &Name,
        is_min: bool,
    ) -> Result<(), EnvError> {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());

        let op_aa = if is_min {
            c.min_of(a.clone(), a.clone())
        } else {
            c.max_of(a.clone(), a.clone())
        };

        let type_ = {
            let concl = c.eq_of(op_aa.clone(), a.clone());
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), concl);
            b.finish(e)
        };

        // motive: fun (bl : Bool) => Eq Nat (@Bool.rec (fun _ => Nat) a a bl) a
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (bl_id, bl) = mb.fresh_local(c.bool_ty.clone());
            let body = c.eq_of(c.bool_rec_nat_app(a.clone(), a.clone(), bl), a.clone());
            let lam = mb.mk_lam(bl_id, BinderInfo::Default, c.bool_ty.clone(), body);
            mb.finish_child(lam)
        };

        // both minors: Eq.refl a (Bool.rec a a {false,true} ≡ a).
        let minor = c.eq_refl_app(a.clone());

        let value = {
            // @Bool.rec.{0} motive (Eq.refl a) (Eq.refl a) (Nat.ble a a) : OP a a = a
            let rec_app = Expr::apps(
                c.bool_rec_prop.clone(),
                [motive, minor.clone(), minor, c.ble_of(a.clone(), a.clone())],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), rec_app);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked dependent `Bool.rec.{0}` over the reducible
        // `Nat.ble a a`; both minors are `Eq.refl a` and the only axioms in the
        // closure are foundational (`Eq.refl`). Empty domain-axiom closure.
        self.add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Ensure `Nat.zero_le` is registered as a constructive Theorem.
    ///
    /// `register_nat_mul_le_mul_left_proof` registers `Nat.zero_le` (among
    /// others) as a constructive Theorem; route through it when missing.
    fn register_nat_zero_le_only(&mut self) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("Nat.zero_le")).is_some() {
            return Ok(());
        }
        self.register_nat_mul_le_mul_left_proof()
    }

    /// `Nat.le_min : ∀ a b c, Nat.le c a → Nat.le c b → Nat.le c (Nat.min a b)`.
    fn register_nat_le_min(&mut self, c: &MinMaxConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.le_min");
        if self.minmax_is_theorem(&name) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let (cc_id, cc) = b.fresh_local(c.nat.clone());
        let h1_type = c.le_of(cc.clone(), a.clone());
        let (h1_id, h1) = b.fresh_local(h1_type.clone());
        let h2_type = c.le_of(cc.clone(), bb.clone());
        let (h2_id, h2) = b.fresh_local(h2_type.clone());

        let type_ = {
            let concl = c.le_of(cc.clone(), c.min_of(a.clone(), bb.clone()));
            let e = b.mk_pi(h2_id, BinderInfo::Default, h2_type.clone(), concl);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_type.clone(), e);
            let e = b.mk_pi(cc_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // motive: fun (bl : Bool) => Nat.le c (@Bool.rec.{1} (fun _ => Nat) b a bl)
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (bl_id, bl) = mb.fresh_local(c.bool_ty.clone());
            let body = c.le_of(cc.clone(), c.bool_rec_nat_app(bb.clone(), a.clone(), bl));
            let lam = mb.mk_lam(bl_id, BinderInfo::Default, c.bool_ty.clone(), body);
            mb.finish_child(lam)
        };

        let value = {
            // @Bool.rec.{0} motive (false -> h2) (true -> h1) (Nat.ble a b)
            let rec_app = Expr::apps(
                c.bool_rec_prop.clone(),
                [
                    motive,
                    h2.clone(),
                    h1.clone(),
                    c.ble_of(a.clone(), bb.clone()),
                ],
            );
            let e = b.mk_lam(h2_id, BinderInfo::Default, h2_type, rec_app);
            let e = b.mk_lam(h1_id, BinderInfo::Default, h1_type, e);
            let e = b.mk_lam(cc_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked dependent `Bool.rec` over the reducible
        // `Nat.ble`; depends only on the supplied hypotheses. Replaces the
        // legacy `Declaration::Axiom` in `order_lemmas_minmax.rs`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.max_le : ∀ a b c, Nat.le a c → Nat.le b c → Nat.le (Nat.max a b) c`.
    fn register_nat_max_le(&mut self, c: &MinMaxConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.max_le");
        if self.minmax_is_theorem(&name) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let (cc_id, cc) = b.fresh_local(c.nat.clone());
        let h1_type = c.le_of(a.clone(), cc.clone());
        let (h1_id, h1) = b.fresh_local(h1_type.clone());
        let h2_type = c.le_of(bb.clone(), cc.clone());
        let (h2_id, h2) = b.fresh_local(h2_type.clone());

        let type_ = {
            let concl = c.le_of(c.max_of(a.clone(), bb.clone()), cc.clone());
            let e = b.mk_pi(h2_id, BinderInfo::Default, h2_type.clone(), concl);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_type.clone(), e);
            let e = b.mk_pi(cc_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // motive: fun (bl : Bool) => Nat.le (@Bool.rec.{1} (fun _ => Nat) a b bl) c
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (bl_id, bl) = mb.fresh_local(c.bool_ty.clone());
            let body = c.le_of(c.bool_rec_nat_app(a.clone(), bb.clone(), bl), cc.clone());
            let lam = mb.mk_lam(bl_id, BinderInfo::Default, c.bool_ty.clone(), body);
            mb.finish_child(lam)
        };

        let value = {
            // @Bool.rec.{0} motive (false -> h1) (true -> h2) (Nat.ble a b)
            let rec_app = Expr::apps(
                c.bool_rec_prop.clone(),
                [
                    motive,
                    h1.clone(),
                    h2.clone(),
                    c.ble_of(a.clone(), bb.clone()),
                ],
            );
            let e = b.mk_lam(h2_id, BinderInfo::Default, h2_type, rec_app);
            let e = b.mk_lam(h1_id, BinderInfo::Default, h1_type, e);
            let e = b.mk_lam(cc_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked dependent `Bool.rec` over the reducible
        // `Nat.ble`; depends only on the supplied hypotheses. Replaces the
        // legacy `Declaration::Axiom` in `order_lemmas_minmax.rs`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Build a dependent `Bool.rec.{0}` "succ-lift" for the extraction lemmas.
    ///
    /// Returns a term of type
    /// `Nat.le (@Bool.rec lf lt scrut) rhs_lo
    ///   → Nat.le (@Bool.rec (succ lf) (succ lt) scrut) (succ rhs_hi)`,
    /// applied to `ih`. The two minors are full `Nat.succ_le_succ` partial
    /// applications, valid because at `scrut = false` the goal is
    /// `Nat.le lf rhs_lo → Nat.le (succ lf) (succ rhs_hi)` and at `scrut = true`
    /// it is `Nat.le lt rhs_lo → Nat.le (succ lt) (succ rhs_hi)`; the caller
    /// guarantees `rhs_lo = lf` and `rhs_hi = lf` (false leaf) / `rhs_lo = lt`,
    /// `rhs_hi = lt` matching shapes so `succ_le_succ` types align.
    #[allow(clippy::too_many_arguments)]
    fn succ_push_le(
        &self,
        c: &MinMaxConsts,
        parent: &EnvDeclBuilder,
        lf: Expr,
        lt: Expr,
        rhs_lo: Expr,
        rhs_hi: Expr,
        minor_false: Expr,
        minor_true: Expr,
        scrut: Expr,
        ih: Expr,
    ) -> Expr {
        let _ = self;
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (bl_id, bl) = mb.fresh_local(c.bool_ty.clone());
            let lo = c.le_of(
                c.bool_rec_nat_app(lf.clone(), lt.clone(), bl.clone()),
                rhs_lo.clone(),
            );
            let hi = c.le_of(
                c.bool_rec_nat_app(c.succ_of(lf.clone()), c.succ_of(lt.clone()), bl),
                c.succ_of(rhs_hi.clone()),
            );
            let (lo_id, _lo) = mb.fresh_local(lo.clone());
            let imp = mb.mk_pi(lo_id, BinderInfo::Default, lo, hi);
            let lam = mb.mk_lam(bl_id, BinderInfo::Default, c.bool_ty.clone(), imp);
            mb.finish_child(lam)
        };
        let rec_app = Expr::apps(
            c.bool_rec_prop.clone(),
            [motive, minor_false, minor_true, scrut],
        );
        Expr::app(rec_app, ih)
    }

    /// `Nat.min_le_left : ∀ a b, Nat.le (Nat.min a b) a`.
    fn register_nat_min_le_left(&mut self, c: &MinMaxConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.min_le_left");
        if self.minmax_is_theorem(&name) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());

        let type_ = {
            let concl = c.le_of(c.min_of(a.clone(), bb.clone()), a.clone());
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // outer motive: fun (t : Nat) => ∀ b, Nat.le (Nat.min t b) t
        let outer_motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let (m_id, mv) = mb.fresh_local(c.nat.clone());
            let inner = c.le_of(c.min_of(t.clone(), mv), t.clone());
            let pi = mb.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), inner);
            let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), pi);
            mb.finish_child(lam)
        };

        // outer base (a = 0): fun (b : Nat) => Nat.le.refl 0
        // (Nat.min 0 b ≡ 0, goal Nat.le 0 0).
        let outer_base = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (m_id, _mv) = sb.fresh_local(c.nat.clone());
            let body = c.le_refl_app(c.zero.clone());
            let lam = sb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body);
            sb.finish_child(lam)
        };

        // outer step (a = succ k): induct on b.
        let outer_step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(c.nat.clone());
            // iha : ∀ b, Nat.le (Nat.min k b) k
            let iha_type = {
                let mut ib = EnvDeclBuilder::child_of(&sb);
                let (ib_id, ibv) = ib.fresh_local(c.nat.clone());
                let body = c.le_of(c.min_of(k.clone(), ibv), k.clone());
                let pi = ib.mk_pi(ib_id, BinderInfo::Default, c.nat.clone(), body);
                ib.finish_child(pi)
            };
            let (iha_id, iha) = sb.fresh_local(iha_type.clone());

            // lambda over b, inner Nat.rec on b.
            let body = {
                let mut bind = EnvDeclBuilder::child_of(&sb);
                let (b2_id, b2) = bind.fresh_local(c.nat.clone());

                // inner motive: fun (t : Nat) => Nat.le (Nat.min (succ k) t) (succ k)
                let inner_motive = {
                    let mut mb = EnvDeclBuilder::child_of(&bind);
                    let (t_id, t) = mb.fresh_local(c.nat.clone());
                    let bdy = c.le_of(c.min_of(c.succ_of(k.clone()), t), c.succ_of(k.clone()));
                    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), bdy);
                    mb.finish_child(lam)
                };
                // inner base (b = 0): Nat.min (succ k) 0 ≡ 0; goal Nat.le 0 (succ k).
                let inner_base = c.zero_le_app(c.succ_of(k.clone()));
                // inner step (b = succ j): lift iha j.
                let inner_step = {
                    let mut jb = EnvDeclBuilder::child_of(&bind);
                    let (j_id, j) = jb.fresh_local(c.nat.clone());
                    let ih_inner_type = c.le_of(
                        c.min_of(c.succ_of(k.clone()), j.clone()),
                        c.succ_of(k.clone()),
                    );
                    let (ihj_id, _ihj) = jb.fresh_local(ih_inner_type.clone());
                    // iha j : Nat.le (@Bool.rec j k (ble k j)) k
                    let iha_j = Expr::app(iha.clone(), j.clone());
                    // Goal: Nat.le (@Bool.rec (succ j) (succ k) (ble k j)) (succ k).
                    // succ-lift: false-minor succ_le_succ j k, true-minor succ_le_succ k k.
                    let minor_false = c.succ_le_succ_fn(j.clone(), k.clone());
                    let minor_true = c.succ_le_succ_fn(k.clone(), k.clone());
                    let lift = self.succ_push_le(
                        c,
                        &jb,
                        j.clone(),
                        k.clone(),
                        k.clone(),
                        k.clone(),
                        minor_false,
                        minor_true,
                        c.ble_of(k.clone(), j.clone()),
                        iha_j,
                    );
                    let lam_ih = jb.mk_lam(ihj_id, BinderInfo::Default, ih_inner_type, lift);
                    let lam_j = jb.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), lam_ih);
                    jb.finish_child(lam_j)
                };
                let rec2 = Expr::apps(
                    c.nat_rec.clone(),
                    [inner_motive, inner_base, inner_step, b2.clone()],
                );
                bind.mk_lam(b2_id, BinderInfo::Default, c.nat.clone(), rec2)
            };

            let lam_iha = sb.mk_lam(iha_id, BinderInfo::Default, iha_type, body);
            let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_iha);
            sb.finish_child(lam_k)
        };

        let value = {
            let rec_app = Expr::apps(
                c.nat_rec.clone(),
                [outer_motive, outer_base, outer_step, a.clone()],
            );
            let applied = Expr::app(rec_app, bb.clone());
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), applied);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked double `Nat.rec` over the reducible
        // `Nat.min` / `Nat.ble`; uses only `Nat.le.refl`, `Nat.zero_le`,
        // `Nat.succ_le_succ`. Replaces the legacy `Declaration::Axiom`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.min_le_right : ∀ a b, Nat.le (Nat.min a b) b`.
    ///
    /// Double `Nat.rec` over `a` then `b`. Leaves:
    /// - `a = 0`: `Nat.min 0 b ≡ 0`, goal `Nat.le 0 b` = `Nat.zero_le b`.
    /// - `a = succ k`, `b = 0`: `Nat.min (succ k) 0 ≡ 0`, goal `Nat.le 0 0`
    ///   = `Nat.le.refl 0`.
    /// - `a = succ k`, `b = succ j`: lift `iha j : Nat.le (Nat.min k j) j` by the
    ///   succ-push `Bool.rec` (false-minor `succ_le_succ j j`, true-minor
    ///   `succ_le_succ k j`), matching `rhs_lo = rhs_hi = j`.
    fn register_nat_min_le_right(&mut self, c: &MinMaxConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.min_le_right");
        if self.minmax_is_theorem(&name) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());

        let type_ = {
            let concl = c.le_of(c.min_of(a.clone(), bb.clone()), bb.clone());
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // outer motive: fun (t : Nat) => ∀ b, Nat.le (Nat.min t b) b
        let outer_motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let (m_id, mv) = mb.fresh_local(c.nat.clone());
            let inner = c.le_of(c.min_of(t.clone(), mv.clone()), mv);
            let pi = mb.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), inner);
            let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), pi);
            mb.finish_child(lam)
        };

        // outer base (a = 0): fun (b : Nat) => Nat.zero_le b  (Nat.min 0 b ≡ 0).
        let outer_base = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (m_id, mv) = sb.fresh_local(c.nat.clone());
            let body = c.zero_le_app(mv.clone());
            let lam = sb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body);
            sb.finish_child(lam)
        };

        let outer_step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(c.nat.clone());
            let iha_type = {
                let mut ib = EnvDeclBuilder::child_of(&sb);
                let (ib_id, ibv) = ib.fresh_local(c.nat.clone());
                let body = c.le_of(c.min_of(k.clone(), ibv.clone()), ibv);
                let pi = ib.mk_pi(ib_id, BinderInfo::Default, c.nat.clone(), body);
                ib.finish_child(pi)
            };
            let (iha_id, iha) = sb.fresh_local(iha_type.clone());

            let body = {
                let mut bind = EnvDeclBuilder::child_of(&sb);
                let (b2_id, b2) = bind.fresh_local(c.nat.clone());

                // inner motive: fun (t : Nat) => Nat.le (Nat.min (succ k) t) t
                let inner_motive = {
                    let mut mb = EnvDeclBuilder::child_of(&bind);
                    let (t_id, t) = mb.fresh_local(c.nat.clone());
                    let bdy = c.le_of(c.min_of(c.succ_of(k.clone()), t.clone()), t);
                    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), bdy);
                    mb.finish_child(lam)
                };
                // inner base (b = 0): Nat.min (succ k) 0 ≡ 0; goal Nat.le 0 0.
                let inner_base = c.le_refl_app(c.zero.clone());
                // inner step (b = succ j): lift iha j.
                let inner_step = {
                    let mut jb = EnvDeclBuilder::child_of(&bind);
                    let (j_id, j) = jb.fresh_local(c.nat.clone());
                    let ih_inner_type =
                        c.le_of(c.min_of(c.succ_of(k.clone()), j.clone()), j.clone());
                    let (ihj_id, _ihj) = jb.fresh_local(ih_inner_type.clone());
                    // iha j : Nat.le (@Bool.rec j k (ble k j)) j
                    let iha_j = Expr::app(iha.clone(), j.clone());
                    // Goal: Nat.le (@Bool.rec (succ j) (succ k) (ble k j)) (succ j).
                    // rhs_lo = rhs_hi = j. false-minor succ_le_succ j j, true succ_le_succ k j.
                    let minor_false = c.succ_le_succ_fn(j.clone(), j.clone());
                    let minor_true = c.succ_le_succ_fn(k.clone(), j.clone());
                    let lift = self.succ_push_le(
                        c,
                        &jb,
                        j.clone(),
                        k.clone(),
                        j.clone(),
                        j.clone(),
                        minor_false,
                        minor_true,
                        c.ble_of(k.clone(), j.clone()),
                        iha_j,
                    );
                    let lam_ih = jb.mk_lam(ihj_id, BinderInfo::Default, ih_inner_type, lift);
                    let lam_j = jb.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), lam_ih);
                    jb.finish_child(lam_j)
                };
                let rec2 = Expr::apps(
                    c.nat_rec.clone(),
                    [inner_motive, inner_base, inner_step, b2.clone()],
                );
                bind.mk_lam(b2_id, BinderInfo::Default, c.nat.clone(), rec2)
            };

            let lam_iha = sb.mk_lam(iha_id, BinderInfo::Default, iha_type, body);
            let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_iha);
            sb.finish_child(lam_k)
        };

        let value = {
            let rec_app = Expr::apps(
                c.nat_rec.clone(),
                [outer_motive, outer_base, outer_step, a.clone()],
            );
            let applied = Expr::app(rec_app, bb.clone());
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), applied);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked double `Nat.rec`; uses only `Nat.le.refl`,
        // `Nat.zero_le`, `Nat.succ_le_succ`. Replaces the legacy Axiom.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.le_max_left : ∀ a b, Nat.le a (Nat.max a b)`.
    ///
    /// `Nat.max a b ≡ @Bool.rec a b (Nat.ble a b)`. Double `Nat.rec`. Leaves:
    /// - `a = 0`: goal `Nat.le 0 (Nat.max 0 b)` = `Nat.zero_le (Nat.max 0 b)`.
    /// - `a = succ k`, `b = 0`: `Nat.max (succ k) 0 ≡ succ k`, goal
    ///   `Nat.le (succ k) (succ k)` = `Nat.le.refl (succ k)`.
    /// - `a = succ k`, `b = succ j`: lift `iha j : Nat.le k (Nat.max k j)
    ///   ≡ Nat.le k (@Bool.rec k j (ble k j))` by succ-push; the selection lives
    ///   on the *right*, so `lf = k`, `lt = j`, `rhs_lo = rhs_hi = k` and we use
    ///   the mirrored helper `succ_push_le_right`.
    fn register_nat_le_max_left(&mut self, c: &MinMaxConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.le_max_left");
        if self.minmax_is_theorem(&name) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());

        let type_ = {
            let concl = c.le_of(a.clone(), c.max_of(a.clone(), bb.clone()));
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // outer motive: fun (t : Nat) => ∀ b, Nat.le t (Nat.max t b)
        let outer_motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let (m_id, mv) = mb.fresh_local(c.nat.clone());
            let inner = c.le_of(t.clone(), c.max_of(t.clone(), mv));
            let pi = mb.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), inner);
            let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), pi);
            mb.finish_child(lam)
        };

        // outer base (a = 0): fun (b : Nat) => Nat.zero_le (Nat.max 0 b).
        let outer_base = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (m_id, mv) = sb.fresh_local(c.nat.clone());
            let body = c.zero_le_app(c.max_of(c.zero.clone(), mv));
            let lam = sb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body);
            sb.finish_child(lam)
        };

        let outer_step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(c.nat.clone());
            let iha_type = {
                let mut ib = EnvDeclBuilder::child_of(&sb);
                let (ib_id, ibv) = ib.fresh_local(c.nat.clone());
                let body = c.le_of(k.clone(), c.max_of(k.clone(), ibv));
                let pi = ib.mk_pi(ib_id, BinderInfo::Default, c.nat.clone(), body);
                ib.finish_child(pi)
            };
            let (iha_id, iha) = sb.fresh_local(iha_type.clone());

            let body = {
                let mut bind = EnvDeclBuilder::child_of(&sb);
                let (b2_id, b2) = bind.fresh_local(c.nat.clone());

                // inner motive: fun (t : Nat) => Nat.le (succ k) (Nat.max (succ k) t)
                let inner_motive = {
                    let mut mb = EnvDeclBuilder::child_of(&bind);
                    let (t_id, t) = mb.fresh_local(c.nat.clone());
                    let bdy = c.le_of(c.succ_of(k.clone()), c.max_of(c.succ_of(k.clone()), t));
                    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), bdy);
                    mb.finish_child(lam)
                };
                // inner base (b = 0): Nat.max (succ k) 0 ≡ succ k; goal
                // Nat.le (succ k) (succ k).
                let inner_base = c.le_refl_app(c.succ_of(k.clone()));
                let inner_step = {
                    let mut jb = EnvDeclBuilder::child_of(&bind);
                    let (j_id, j) = jb.fresh_local(c.nat.clone());
                    let ih_inner_type = c.le_of(
                        c.succ_of(k.clone()),
                        c.max_of(c.succ_of(k.clone()), j.clone()),
                    );
                    let (ihj_id, _ihj) = jb.fresh_local(ih_inner_type.clone());
                    // iha j : Nat.le k (@Bool.rec k j (ble k j))
                    let iha_j = Expr::app(iha.clone(), j.clone());
                    // Goal: Nat.le (succ k) (@Bool.rec (succ k) (succ j) (ble k j)).
                    // Right-selection succ-push: lf=k, lt=j, lhs=k.
                    let minor_false = c.succ_le_succ_fn(k.clone(), k.clone());
                    let minor_true = c.succ_le_succ_fn(k.clone(), j.clone());
                    let lift = self.succ_push_le_right(
                        c,
                        &jb,
                        k.clone(),
                        k.clone(),
                        j.clone(),
                        k.clone(),
                        minor_false,
                        minor_true,
                        c.ble_of(k.clone(), j.clone()),
                        iha_j,
                    );
                    let lam_ih = jb.mk_lam(ihj_id, BinderInfo::Default, ih_inner_type, lift);
                    let lam_j = jb.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), lam_ih);
                    jb.finish_child(lam_j)
                };
                let rec2 = Expr::apps(
                    c.nat_rec.clone(),
                    [inner_motive, inner_base, inner_step, b2.clone()],
                );
                bind.mk_lam(b2_id, BinderInfo::Default, c.nat.clone(), rec2)
            };

            let lam_iha = sb.mk_lam(iha_id, BinderInfo::Default, iha_type, body);
            let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_iha);
            sb.finish_child(lam_k)
        };

        let value = {
            let rec_app = Expr::apps(
                c.nat_rec.clone(),
                [outer_motive, outer_base, outer_step, a.clone()],
            );
            let applied = Expr::app(rec_app, bb.clone());
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), applied);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked double `Nat.rec`; uses only `Nat.le.refl`,
        // `Nat.zero_le`, `Nat.succ_le_succ`. Replaces the legacy Axiom.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.le_max_right : ∀ a b, Nat.le b (Nat.max a b)`.
    ///
    /// Double `Nat.rec`. Leaves:
    /// - `a = 0`: `Nat.max 0 b ≡ b` (`ble 0 b ≡ true`, `Bool.rec 0 b true = b`),
    ///   goal `Nat.le b b` = `Nat.le.refl b`.
    /// - `a = succ k`, `b = 0`: goal `Nat.le 0 (Nat.max (succ k) 0)` =
    ///   `Nat.zero_le (Nat.max (succ k) 0)`.
    /// - `a = succ k`, `b = succ j`: lift `iha j : Nat.le j (Nat.max k j)
    ///   ≡ Nat.le j (@Bool.rec k j (ble k j))`; right-selection succ-push with
    ///   `lf = k`, `lt = j`, `lhs = j`.
    fn register_nat_le_max_right(&mut self, c: &MinMaxConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.le_max_right");
        if self.minmax_is_theorem(&name) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());

        let type_ = {
            let concl = c.le_of(bb.clone(), c.max_of(a.clone(), bb.clone()));
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // outer motive: fun (t : Nat) => ∀ b, Nat.le b (Nat.max t b)
        let outer_motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let (m_id, mv) = mb.fresh_local(c.nat.clone());
            let inner = c.le_of(mv.clone(), c.max_of(t.clone(), mv));
            let pi = mb.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), inner);
            let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), pi);
            mb.finish_child(lam)
        };

        // outer base (a = 0): fun (b : Nat) => Nat.le.refl b  (Nat.max 0 b ≡ b).
        let outer_base = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (m_id, mv) = sb.fresh_local(c.nat.clone());
            let body = c.le_refl_app(mv);
            let lam = sb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body);
            sb.finish_child(lam)
        };

        let outer_step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(c.nat.clone());
            let iha_type = {
                let mut ib = EnvDeclBuilder::child_of(&sb);
                let (ib_id, ibv) = ib.fresh_local(c.nat.clone());
                let body = c.le_of(ibv.clone(), c.max_of(k.clone(), ibv));
                let pi = ib.mk_pi(ib_id, BinderInfo::Default, c.nat.clone(), body);
                ib.finish_child(pi)
            };
            let (iha_id, iha) = sb.fresh_local(iha_type.clone());

            let body = {
                let mut bind = EnvDeclBuilder::child_of(&sb);
                let (b2_id, b2) = bind.fresh_local(c.nat.clone());

                // inner motive: fun (t : Nat) => Nat.le t (Nat.max (succ k) t)
                let inner_motive = {
                    let mut mb = EnvDeclBuilder::child_of(&bind);
                    let (t_id, t) = mb.fresh_local(c.nat.clone());
                    let bdy = c.le_of(t.clone(), c.max_of(c.succ_of(k.clone()), t));
                    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), bdy);
                    mb.finish_child(lam)
                };
                // inner base (b = 0): goal Nat.le 0 (Nat.max (succ k) 0).
                let inner_base = c.zero_le_app(c.max_of(c.succ_of(k.clone()), c.zero.clone()));
                let inner_step = {
                    let mut jb = EnvDeclBuilder::child_of(&bind);
                    let (j_id, j) = jb.fresh_local(c.nat.clone());
                    let ih_inner_type =
                        c.le_of(j.clone(), c.max_of(c.succ_of(k.clone()), j.clone()));
                    let (ihj_id, _ihj) = jb.fresh_local(ih_inner_type.clone());
                    // iha j : Nat.le j (@Bool.rec k j (ble k j))
                    let iha_j = Expr::app(iha.clone(), j.clone());
                    // Goal: Nat.le (succ j) (@Bool.rec (succ k) (succ j) (ble k j)).
                    // Right-selection succ-push: lf=k, lt=j, lhs=j.
                    let minor_false = c.succ_le_succ_fn(j.clone(), k.clone());
                    let minor_true = c.succ_le_succ_fn(j.clone(), j.clone());
                    let lift = self.succ_push_le_right(
                        c,
                        &jb,
                        j.clone(),
                        k.clone(),
                        j.clone(),
                        j.clone(),
                        minor_false,
                        minor_true,
                        c.ble_of(k.clone(), j.clone()),
                        iha_j,
                    );
                    let lam_ih = jb.mk_lam(ihj_id, BinderInfo::Default, ih_inner_type, lift);
                    let lam_j = jb.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), lam_ih);
                    jb.finish_child(lam_j)
                };
                let rec2 = Expr::apps(
                    c.nat_rec.clone(),
                    [inner_motive, inner_base, inner_step, b2.clone()],
                );
                bind.mk_lam(b2_id, BinderInfo::Default, c.nat.clone(), rec2)
            };

            let lam_iha = sb.mk_lam(iha_id, BinderInfo::Default, iha_type, body);
            let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_iha);
            sb.finish_child(lam_k)
        };

        let value = {
            let rec_app = Expr::apps(
                c.nat_rec.clone(),
                [outer_motive, outer_base, outer_step, a.clone()],
            );
            let applied = Expr::app(rec_app, bb.clone());
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), applied);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked double `Nat.rec`; uses only `Nat.le.refl`,
        // `Nat.zero_le`, `Nat.succ_le_succ`. Replaces the legacy Axiom.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Mirror of `succ_push_le` where the `Bool.rec` selection lives on the
    /// *right* of the `Nat.le`.
    ///
    /// Returns a term of type
    /// `Nat.le lhs_lo (@Bool.rec rf rt scrut)
    ///   → Nat.le (succ lhs_hi) (@Bool.rec (succ rf) (succ rt) scrut)`,
    /// applied to `ih`.
    #[allow(clippy::too_many_arguments)]
    fn succ_push_le_right(
        &self,
        c: &MinMaxConsts,
        parent: &EnvDeclBuilder,
        lhs_lo: Expr,
        rf: Expr,
        rt: Expr,
        lhs_hi: Expr,
        minor_false: Expr,
        minor_true: Expr,
        scrut: Expr,
        ih: Expr,
    ) -> Expr {
        let _ = self;
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (bl_id, bl) = mb.fresh_local(c.bool_ty.clone());
            let lo = c.le_of(
                lhs_lo.clone(),
                c.bool_rec_nat_app(rf.clone(), rt.clone(), bl.clone()),
            );
            let hi = c.le_of(
                c.succ_of(lhs_hi.clone()),
                c.bool_rec_nat_app(c.succ_of(rf.clone()), c.succ_of(rt.clone()), bl),
            );
            let (lo_id, _lo) = mb.fresh_local(lo.clone());
            let imp = mb.mk_pi(lo_id, BinderInfo::Default, lo, hi);
            let lam = mb.mk_lam(bl_id, BinderInfo::Default, c.bool_ty.clone(), imp);
            mb.finish_child(lam)
        };
        let rec_app = Expr::apps(
            c.bool_rec_prop.clone(),
            [motive, minor_false, minor_true, scrut],
        );
        Expr::app(rec_app, ih)
    }

    /// Build the dependent `Bool.rec.{0}` "succ-push" *equation* congruence:
    /// `Eq Nat (Nat.succ (@Bool.rec f t scrut))
    ///         (@Bool.rec (Nat.succ f) (Nat.succ t) scrut)`.
    ///
    /// Proof: dependent `Bool.rec.{0}` with motive
    /// `fun bl => Eq Nat (succ (Bool.rec f t bl)) (Bool.rec (succ f) (succ t) bl)`;
    /// both minors are `Eq.refl`.
    fn succ_push_eq(
        &self,
        c: &MinMaxConsts,
        parent: &EnvDeclBuilder,
        f: Expr,
        t: Expr,
        scrut: Expr,
    ) -> Expr {
        let _ = self;
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (bl_id, bl) = mb.fresh_local(c.bool_ty.clone());
            let lhs = c.succ_of(c.bool_rec_nat_app(f.clone(), t.clone(), bl.clone()));
            let rhs = c.bool_rec_nat_app(c.succ_of(f.clone()), c.succ_of(t.clone()), bl);
            let body = c.eq_of(lhs, rhs);
            let lam = mb.mk_lam(bl_id, BinderInfo::Default, c.bool_ty.clone(), body);
            mb.finish_child(lam)
        };
        // false-minor: Eq.refl (succ f); true-minor: Eq.refl (succ t).
        let minor_false = c.eq_refl_app(c.succ_of(f.clone()));
        let minor_true = c.eq_refl_app(c.succ_of(t.clone()));
        Expr::apps(
            c.bool_rec_prop.clone(),
            [motive, minor_false, minor_true, scrut],
        )
    }

    /// `Nat.min_comm : ∀ a b, Eq Nat (Nat.min a b) (Nat.min b a)`.
    fn register_nat_min_comm(&mut self, c: &MinMaxConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.min_comm");
        if self.minmax_is_theorem(&name) {
            return Ok(());
        }
        self.register_minmax_comm(c, &name, ConstantKind::Theorem, true)
    }

    /// `Nat.max_comm : ∀ a b, Eq Nat (Nat.max a b) (Nat.max b a)`.
    fn register_nat_max_comm(&mut self, c: &MinMaxConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.max_comm");
        if self.minmax_is_theorem(&name) {
            return Ok(());
        }
        self.register_minmax_comm(c, &name, ConstantKind::Theorem, false)
    }

    /// Shared body of `Nat.min_comm` (`is_min == true`) / `Nat.max_comm`
    /// (`is_min == false`).
    ///
    /// Both have shape `∀ a b, Eq Nat (OP a b) (OP b a)`, proved by double
    /// `Nat.rec` over `a` then `b`. For `min`: `min a b ≡ Bool.rec b a (ble a b)`;
    /// for `max`: `max a b ≡ Bool.rec a b (ble a b)`. The structural shape of
    /// each leaf is identical between min/max because all reduce through the same
    /// `ble` recursion; the `(succ k, succ j)` leaf chains:
    ///
    /// ```text
    ///   OP (succ k) (succ j)
    ///     = succ (OP k j)                 -- symm (succ_push_eq for the LHS selection)
    ///     = succ (OP j k)                 -- congrArg Nat.succ (iha j)
    ///     = OP (succ j) (succ k)          -- succ_push_eq for the RHS selection
    /// ```
    fn register_minmax_comm(
        &mut self,
        c: &MinMaxConsts,
        name: &Name,
        _kind: ConstantKind,
        is_min: bool,
    ) -> Result<(), EnvError> {
        // Selection helper for OP a b as `Bool.rec`: returns (false_minor, true_minor)
        // given the two arguments; min => (b, a), max => (a, b).
        let op_of = |x: Expr, y: Expr| -> Expr {
            if is_min {
                c.min_of(x, y)
            } else {
                c.max_of(x, y)
            }
        };

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());

        let type_ = {
            let concl = c.eq_of(op_of(a.clone(), bb.clone()), op_of(bb.clone(), a.clone()));
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // outer motive: fun (t : Nat) => ∀ b, Eq Nat (OP t b) (OP b t)
        let outer_motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let (m_id, mv) = mb.fresh_local(c.nat.clone());
            let inner = c.eq_of(op_of(t.clone(), mv.clone()), op_of(mv, t.clone()));
            let pi = mb.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), inner);
            let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), pi);
            mb.finish_child(lam)
        };

        // outer base (a = 0): fun (b : Nat) => proof that OP 0 b = OP b 0.
        // Induct on b: both leaves reduce to a common value with Eq.refl.
        let outer_base = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (b2_id, b2) = sb.fresh_local(c.nat.clone());
            // inner motive: fun (t : Nat) => Eq Nat (OP 0 t) (OP t 0)
            let inner_motive = {
                let mut mb = EnvDeclBuilder::child_of(&sb);
                let (t_id, t) = mb.fresh_local(c.nat.clone());
                let bdy = c.eq_of(op_of(c.zero.clone(), t.clone()), op_of(t, c.zero.clone()));
                let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), bdy);
                mb.finish_child(lam)
            };
            // inner base (b = 0): OP 0 0 = OP 0 0; Eq.refl (OP 0 0).
            let inner_base = c.eq_refl_app(op_of(c.zero.clone(), c.zero.clone()));
            // inner step (b = succ j): for min, OP 0 (succ j) ≡ 0 and
            // OP (succ j) 0 ≡ 0, so Eq.refl 0. For max, OP 0 (succ j) ≡ succ j and
            // OP (succ j) 0 ≡ succ j, so Eq.refl (succ j).
            let inner_step = {
                let mut jb = EnvDeclBuilder::child_of(&sb);
                let (j_id, j) = jb.fresh_local(c.nat.clone());
                let ih_inner_type = c.eq_of(
                    op_of(c.zero.clone(), j.clone()),
                    op_of(j.clone(), c.zero.clone()),
                );
                let (ihj_id, _ihj) = jb.fresh_local(ih_inner_type.clone());
                // common reduced value: min => 0, max => succ j.
                let refl_val = if is_min {
                    c.zero.clone()
                } else {
                    c.succ_of(j.clone())
                };
                let body = c.eq_refl_app(refl_val);
                let lam_ih = jb.mk_lam(ihj_id, BinderInfo::Default, ih_inner_type, body);
                let lam_j = jb.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), lam_ih);
                jb.finish_child(lam_j)
            };
            let rec2 = Expr::apps(
                c.nat_rec.clone(),
                [inner_motive, inner_base, inner_step, b2.clone()],
            );
            sb.mk_lam(b2_id, BinderInfo::Default, c.nat.clone(), rec2)
        };

        // outer step (a = succ k).
        let outer_step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(c.nat.clone());
            let iha_type = {
                let mut ib = EnvDeclBuilder::child_of(&sb);
                let (ib_id, ibv) = ib.fresh_local(c.nat.clone());
                let body = c.eq_of(op_of(k.clone(), ibv.clone()), op_of(ibv, k.clone()));
                let pi = ib.mk_pi(ib_id, BinderInfo::Default, c.nat.clone(), body);
                ib.finish_child(pi)
            };
            let (iha_id, iha) = sb.fresh_local(iha_type.clone());

            let body = {
                let mut bind = EnvDeclBuilder::child_of(&sb);
                let (b2_id, b2) = bind.fresh_local(c.nat.clone());

                // inner motive: fun (t : Nat) => Eq Nat (OP (succ k) t) (OP t (succ k))
                let inner_motive = {
                    let mut mb = EnvDeclBuilder::child_of(&bind);
                    let (t_id, t) = mb.fresh_local(c.nat.clone());
                    let bdy = c.eq_of(
                        op_of(c.succ_of(k.clone()), t.clone()),
                        op_of(t, c.succ_of(k.clone())),
                    );
                    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), bdy);
                    mb.finish_child(lam)
                };
                // inner base (b = 0):
                // min: OP (succ k) 0 ≡ 0, OP 0 (succ k) ≡ 0 -> Eq.refl 0.
                // max: OP (succ k) 0 ≡ succ k, OP 0 (succ k) ≡ succ k -> Eq.refl (succ k).
                let inner_base = {
                    let v = if is_min {
                        c.zero.clone()
                    } else {
                        c.succ_of(k.clone())
                    };
                    c.eq_refl_app(v)
                };
                // inner step (b = succ j): the chained congruence.
                let inner_step = {
                    let mut jb = EnvDeclBuilder::child_of(&bind);
                    let (j_id, j) = jb.fresh_local(c.nat.clone());
                    // IH binder = inner motive at `j`, i.e. `M j`, NOT `M (succ j)`:
                    // `Nat.rec`'s succ minor has type `(j) → M j → M (succ j)`.
                    let ih_inner_type = c.eq_of(
                        op_of(c.succ_of(k.clone()), j.clone()),
                        op_of(j.clone(), c.succ_of(k.clone())),
                    );
                    let (ihj_id, _ihj) = jb.fresh_local(ih_inner_type.clone());
                    let proof = self.minmax_comm_succ_leaf(
                        c,
                        &jb,
                        k.clone(),
                        j.clone(),
                        iha.clone(),
                        is_min,
                    );
                    let lam_ih = jb.mk_lam(ihj_id, BinderInfo::Default, ih_inner_type, proof);
                    let lam_j = jb.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), lam_ih);
                    jb.finish_child(lam_j)
                };
                let rec2 = Expr::apps(
                    c.nat_rec.clone(),
                    [inner_motive, inner_base, inner_step, b2.clone()],
                );
                bind.mk_lam(b2_id, BinderInfo::Default, c.nat.clone(), rec2)
            };

            let lam_iha = sb.mk_lam(iha_id, BinderInfo::Default, iha_type, body);
            let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_iha);
            sb.finish_child(lam_k)
        };

        let value = {
            let rec_app = Expr::apps(
                c.nat_rec.clone(),
                [outer_motive, outer_base, outer_step, a.clone()],
            );
            let applied = Expr::app(rec_app, bb.clone());
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), applied);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked double `Nat.rec`; uses only `Eq.refl`,
        // `Eq.trans`, `Eq.symm`, `congrArg`, and dependent `Bool.rec`
        // congruences. Replaces the legacy `Declaration::Axiom`.
        self.add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `(succ k, succ j)` leaf of `min_comm` / `max_comm`.
    ///
    /// Builds `Eq Nat (OP (succ k) (succ j)) (OP (succ j) (succ k))` from
    /// `iha : ∀ b, Eq Nat (OP k b) (OP b k)` (so `iha j : Eq Nat (OP k j) (OP j k)`).
    ///
    /// For `min`, `OP (succ k) (succ j) ≡ Bool.rec (succ j) (succ k) (ble k j)`
    /// and `OP k j ≡ Bool.rec j k (ble k j)`. Chain:
    ///   `Bool.rec (succ j) (succ k) (ble k j)`
    ///   = `succ (Bool.rec j k (ble k j))`              [symm succ_push_eq, f=j t=k]
    ///   = `succ (Bool.rec k j (ble j k))`              [congrArg succ (iha j)]
    ///   = `Bool.rec (succ k) (succ j) (ble j k)`       [succ_push_eq, f=k t=j]
    ///   ≡ `OP (succ j) (succ k)`.
    /// For `max`, the false/true minors of the `Bool.rec` swap (selection is
    /// `Bool.rec a b`), giving f/t = (k, j) on the LHS and (j, k) on the RHS.
    fn minmax_comm_succ_leaf(
        &self,
        c: &MinMaxConsts,
        parent: &EnvDeclBuilder,
        k: Expr,
        j: Expr,
        iha: Expr,
        is_min: bool,
    ) -> Expr {
        // LHS selection minors for OP k j (un-succ'd):
        //   min: Bool.rec j k (ble k j)  -> (f_lhs, t_lhs) = (j, k)
        //   max: Bool.rec k j (ble k j)  -> (f_lhs, t_lhs) = (k, j)
        // RHS selection minors for OP j k (un-succ'd):
        //   min: Bool.rec k j (ble j k)  -> (f_rhs, t_rhs) = (k, j)
        //   max: Bool.rec j k (ble j k)  -> (f_rhs, t_rhs) = (j, k)
        let (f_lhs, t_lhs) = if is_min {
            (j.clone(), k.clone())
        } else {
            (k.clone(), j.clone())
        };
        let (f_rhs, t_rhs) = if is_min {
            (k.clone(), j.clone())
        } else {
            (j.clone(), k.clone())
        };
        let ble_kj = c.ble_of(k.clone(), j.clone());
        let ble_jk = c.ble_of(j.clone(), k.clone());

        // term A = Bool.rec (succ f_lhs) (succ t_lhs) (ble k j)  ≡ OP (succ k) (succ j)
        let op_succ_succ_lhs = c.bool_rec_nat_app(
            c.succ_of(f_lhs.clone()),
            c.succ_of(t_lhs.clone()),
            ble_kj.clone(),
        );
        // term B = succ (Bool.rec f_lhs t_lhs (ble k j))  ≡ succ (OP k j)
        let succ_op_kj =
            c.succ_of(c.bool_rec_nat_app(f_lhs.clone(), t_lhs.clone(), ble_kj.clone()));
        // term C = succ (Bool.rec f_rhs t_rhs (ble j k))  ≡ succ (OP j k)
        let succ_op_jk =
            c.succ_of(c.bool_rec_nat_app(f_rhs.clone(), t_rhs.clone(), ble_jk.clone()));
        // term D = Bool.rec (succ f_rhs) (succ t_rhs) (ble j k)  ≡ OP (succ j) (succ k)
        let op_succ_succ_rhs = c.bool_rec_nat_app(
            c.succ_of(f_rhs.clone()),
            c.succ_of(t_rhs.clone()),
            ble_jk.clone(),
        );

        // step1 : A = B  (symm of succ_push_eq f_lhs t_lhs (ble k j) : B = A)
        let push_lhs = self.succ_push_eq(c, parent, f_lhs.clone(), t_lhs.clone(), ble_kj.clone());
        let step1 = c.eq_symm_app(succ_op_kj.clone(), op_succ_succ_lhs.clone(), push_lhs);
        // step2 : B = C  (congrArg Nat.succ (iha j : OP k j = OP j k))
        let iha_j = Expr::app(iha, j.clone());
        let op_kj = c.bool_rec_nat_app(f_lhs.clone(), t_lhs.clone(), ble_kj.clone());
        let op_jk = c.bool_rec_nat_app(f_rhs.clone(), t_rhs.clone(), ble_jk.clone());
        let step2 = c.congr_succ(op_kj.clone(), op_jk.clone(), iha_j);
        // step3 : C = D  (succ_push_eq f_rhs t_rhs (ble j k))
        let step3 = self.succ_push_eq(c, parent, f_rhs.clone(), t_rhs.clone(), ble_jk.clone());

        // chain A = B = C = D.
        let ab_c = c.eq_trans_app(
            op_succ_succ_lhs.clone(),
            succ_op_kj,
            succ_op_jk.clone(),
            step1,
            step2,
        );
        c.eq_trans_app(op_succ_succ_lhs, succ_op_jk, op_succ_succ_rhs, ab_c, step3)
    }

    /// Whether `name` is already registered as a `Declaration::Theorem`.
    fn minmax_is_theorem(&self, name: &Name) -> bool {
        matches!(
            self.get_const(name).map(|i| i.kind),
            Some(ConstantKind::Theorem)
        )
    }
}
