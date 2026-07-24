// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Well-foundedness of `Nat.lt` (Track EE — `Nat.accNatLt`).
//!
//! Registers the accessibility witness for the strict `Nat` ordering as
//! sorry-free `Declaration::Theorem`/`Definition`s with empty domain-specific
//! axiom closures:
//!
//! - `Nat.lt_wfLBound : (n : Nat) → (m : Nat) → Nat.lt m n → Acc Nat.lt m`
//! - `Nat.accNatLt   : (n : Nat) → Acc Nat.lt n`
//! - `Nat.lt_wf      : WellFounded Nat.lt`
//!
//! # Proof strategy (pure structural induction + order lemmas)
//!
//! `Nat.lt_wfLBound` is the Lean-core "lower-bound" lemma. It is proved by
//! **structural `Nat.rec` on the upper bound `n`** with the `Prop` motive
//!
//! ```text
//! C n := (m : Nat) → Nat.lt m n → Acc Nat.lt m
//! ```
//!
//! - **Base (`n = 0`):** `Nat.lt m 0` is the reducible definition
//!   `Nat.le (Nat.succ m) Nat.zero`, which is uninhabited:
//!   `Nat.not_succ_le_zero m : Nat.le (Nat.succ m) Nat.zero → False`. We feed
//!   that contradiction to `@False.rec` at the motive
//!   `fun _ => Acc Nat.lt m`, discharging the vacuous case.
//!
//! - **Step (`n = succ k`)** with `ih : C k`: given `h : Nat.lt m (succ k)`
//!   (reducibly `Nat.le (succ m) (succ k)`) we build `Acc.intro m g` where
//!   `g : (y : Nat) → Nat.lt y m → Acc Nat.lt y`. For each such `y` and
//!   `hy : Nat.lt y m` (reducibly `Nat.le (succ y) m`) we apply `ih y`,
//!   discharging its `Nat.lt y k` obligation by
//!
//!   ```text
//!   Nat.le_trans (Nat.succ y) m k hy (Nat.le_of_succ_le_succ m k h)
//!     : Nat.le (Nat.succ y) k   -- definitionally  Nat.lt y k
//!   ```
//!
//! `Nat.accNatLt n := Acc.intro n (fun m h => Nat.lt_wfLBound n m h)` and
//! `Nat.lt_wf := WellFounded.intro Nat.accNatLt`.
//!
//! All three proof terms reference only:
//!
//! - the kernel-primitive `Acc` / `Acc.intro` inductive and `Nat.rec` /
//!   `False.rec` recursors, and
//! - the already-constructive theorems `Nat.le_trans`,
//!   `Nat.le_of_succ_le_succ`, `Nat.not_succ_le_zero`
//!
//! every one of which has an empty `env.axiom_deps`. No `sorry`, `sorryAx`,
//! `trustedArith`, `trustedAy`, or `Declaration::Axiom` is touched, so each of
//! the three registered constants has an empty domain axiom closure and
//! `ProofQuality::Constructive`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register the `Nat.lt` well-foundedness witnesses (`Nat.lt_wfLBound`,
    /// `Nat.accNatLt`, `Nat.lt_wf`) as constructive declarations.
    ///
    /// # Contract
    ///
    /// REQUIRES: `Acc` (`init_well_founded`) and the constructive Nat order
    /// theorems `Nat.le_trans`, `Nat.le_of_succ_le_succ`,
    /// `Nat.not_succ_le_zero` are registered (their `register_*` methods are
    /// idempotently invoked here as a safeguard).
    /// ENSURES: On success, the three constants above are present as
    /// `Declaration::Theorem`/`Definition`s with empty axiom closures.
    /// ENSURES: Idempotent.
    pub(crate) fn init_nat_lt_wf(&mut self) -> Result<(), EnvError> {
        // Dependencies (each idempotent).
        self.init_nat()?; // Nat, Nat.zero, Nat.succ, Nat.rec
        self.init_lt()?; // Nat.lt (reducible Definition) + Nat.le / Nat.le.rec
        self.init_well_founded()?;
        self.register_nat_le_trans_proof()?;
        self.register_nat_not_succ_le_zero_theorem()?;
        self.register_nat_le_of_succ_le_succ_theorem()?;

        self.register_nat_lt_wf_lbound()?;
        self.register_nat_acc_nat_lt()?;
        self.register_nat_lt_wf()?;
        Ok(())
    }

    /// `Nat.lt_wfLBound : (n : Nat) → (m : Nat) → Nat.lt m n → Acc Nat.lt m`.
    fn register_nat_lt_wf_lbound(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.lt_wfLBound");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        // α = Nat : Sort 1, so the `Acc` family lives at universe 1.
        let lvl1 = Level::succ(Level::zero());
        let acc = Expr::const_(Name::from_string("Acc"), vec![lvl1.clone()]);
        let acc_intro = Expr::const_(Name::from_string("Acc.intro"), vec![lvl1.clone()]);
        let nat_le_trans = Expr::const_(Name::from_string("Nat.le_trans"), vec![]);
        let nat_le_of_succ_le_succ =
            Expr::const_(Name::from_string("Nat.le_of_succ_le_succ"), vec![]);
        let nat_not_succ_le_zero = Expr::const_(Name::from_string("Nat.not_succ_le_zero"), vec![]);
        // `Nat.rec.{0}` — Prop motive.
        let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
        // `False.rec.{1}` — eliminates the empty type into `Acc Nat.lt m : Prop`.
        // (The base-case target is `Acc … : Prop = Sort 0`; `False.rec`'s
        // motive universe param is therefore `0`, but we pass the Acc target via
        // an explicit motive `fun _ => Acc Nat.lt m`.)
        let false_rec = Expr::const_(Name::from_string("False.rec"), vec![Level::zero()]);
        let false_const = Expr::const_(Name::from_string("False"), vec![]);

        // `@Acc.{1} Nat Nat.lt e` — α = Nat (explicit in raw kernel form),
        // relation = the *raw* const `Nat.lt`.
        let acc_lt =
            |e: Expr| -> Expr { Expr::apps(acc.clone(), [nat.clone(), nat_lt.clone(), e]) };
        // `Nat.lt a b`.
        let lt = |a: Expr, b: Expr| -> Expr { Expr::apps(nat_lt.clone(), [a, b]) };
        let succ = |e: Expr| -> Expr { Expr::app(nat_succ.clone(), e) };

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());

        // Type: (n : Nat) → (m : Nat) → Nat.lt m n → Acc Nat.lt m
        let ty = {
            let mut tb = EnvDeclBuilder::child_of(&b);
            let (m_id, m) = tb.fresh_local(nat.clone());
            let h_ty = lt(m.clone(), n.clone());
            let (h_id, _h) = tb.fresh_local(h_ty.clone());
            let concl = acc_lt(m.clone());
            let e = tb.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
            let e = tb.mk_pi(m_id, BinderInfo::Default, nat.clone(), e);
            let inner = tb.finish_child(e);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), inner);
            b.finish(e)
        };

        // Motive of the outer `Nat.rec`:
        //   C := fun (t : Nat) => (m : Nat) → Nat.lt m t → Acc Nat.lt m
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(nat.clone());
            let (m_id, m) = mb.fresh_local(nat.clone());
            let h_ty = lt(m.clone(), t.clone());
            let (h_id, _h) = mb.fresh_local(h_ty.clone());
            let concl = acc_lt(m.clone());
            let e = mb.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
            let e = mb.mk_pi(m_id, BinderInfo::Default, nat.clone(), e);
            let lam = mb.mk_lam(t_id, BinderInfo::Default, nat.clone(), e);
            mb.finish_child(lam)
        };

        // Base case (motive at `Nat.zero`):
        //   fun (m : Nat) (h : Nat.lt m Nat.zero) =>
        //     @False.rec (fun _ => Acc Nat.lt m) (Nat.not_succ_le_zero m h)
        // `Nat.lt m Nat.zero` reduces to `Nat.le (Nat.succ m) Nat.zero`, so
        // `Nat.not_succ_le_zero m h : False`.
        let base = {
            let mut bb = EnvDeclBuilder::child_of(&b);
            let (m_id, m) = bb.fresh_local(nat.clone());
            let h_ty = lt(m.clone(), nat_zero.clone());
            let (h_id, h) = bb.fresh_local(h_ty.clone());

            // false_proof : False
            let false_proof = Expr::apps(nat_not_succ_le_zero.clone(), [m.clone(), h.clone()]);
            // false_motive : False → Sort 0 := fun (_ : False) => Acc Nat.lt m
            let false_motive = {
                let mut fb = EnvDeclBuilder::child_of(&bb);
                let (u_id, _u) = fb.fresh_local(false_const.clone());
                let body = acc_lt(m.clone());
                let lam = fb.mk_lam(u_id, BinderInfo::Default, false_const.clone(), body);
                fb.finish_child(lam)
            };
            let body = Expr::apps(false_rec.clone(), [false_motive, false_proof]);

            let lam_h = bb.mk_lam(h_id, BinderInfo::Default, h_ty, body);
            let lam_m = bb.mk_lam(m_id, BinderInfo::Default, nat.clone(), lam_h);
            bb.finish_child(lam_m)
        };

        // Step case (motive at `Nat.succ k` from motive at `k`):
        //   fun (k : Nat) (ih : C k) (m : Nat) (h : Nat.lt m (Nat.succ k)) =>
        //     @Acc.intro Nat.lt m
        //       (fun (y : Nat) (hy : Nat.lt y m) =>
        //          ih y (Nat.le_trans (Nat.succ y) m k hy
        //                 (Nat.le_of_succ_le_succ m k h)))
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(nat.clone());

            // ih : (m : Nat) → Nat.lt m k → Acc Nat.lt m   (= motive at k)
            let ih_ty = {
                let mut ib = EnvDeclBuilder::child_of(&sb);
                let (m_id, m) = ib.fresh_local(nat.clone());
                let h_ty = lt(m.clone(), k.clone());
                let (h_id, _h) = ib.fresh_local(h_ty.clone());
                let concl = acc_lt(m.clone());
                let e = ib.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
                let e = ib.mk_pi(m_id, BinderInfo::Default, nat.clone(), e);
                ib.finish_child(e)
            };
            let (ih_id, ih) = sb.fresh_local(ih_ty.clone());

            let (m_id, m) = sb.fresh_local(nat.clone());
            let h_ty = lt(m.clone(), succ(k.clone()));
            let (h_id, h) = sb.fresh_local(h_ty.clone());

            // g : (y : Nat) → Nat.lt y m → Acc Nat.lt y
            let g = {
                let mut gb = EnvDeclBuilder::child_of(&sb);
                let (y_id, y) = gb.fresh_local(nat.clone());
                let hy_ty = lt(y.clone(), m.clone());
                let (hy_id, hy) = gb.fresh_local(hy_ty.clone());

                // Nat.le_of_succ_le_succ m k h : Nat.le m k
                let m_le_k = Expr::apps(
                    nat_le_of_succ_le_succ.clone(),
                    [m.clone(), k.clone(), h.clone()],
                );
                // Nat.le_trans (succ y) m k hy m_le_k : Nat.le (succ y) k = Nat.lt y k
                let lt_y_k = Expr::apps(
                    nat_le_trans.clone(),
                    [succ(y.clone()), m.clone(), k.clone(), hy.clone(), m_le_k],
                );
                // ih y lt_y_k : Acc Nat.lt y
                let body = Expr::apps(ih.clone(), [y.clone(), lt_y_k]);

                let lam_hy = gb.mk_lam(hy_id, BinderInfo::Default, hy_ty, body);
                let lam_y = gb.mk_lam(y_id, BinderInfo::Default, nat.clone(), lam_hy);
                gb.finish_child(lam_y)
            };

            // @Acc.intro.{1} Nat Nat.lt m g : Acc Nat.lt m
            let acc_m = Expr::apps(
                acc_intro.clone(),
                [nat.clone(), nat_lt.clone(), m.clone(), g],
            );

            let lam_h = sb.mk_lam(h_id, BinderInfo::Default, h_ty, acc_m);
            let lam_m = sb.mk_lam(m_id, BinderInfo::Default, nat.clone(), lam_h);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam_m);
            let lam_k = sb.mk_lam(k_id, BinderInfo::Default, nat.clone(), lam_ih);
            sb.finish_child(lam_k)
        };

        // @Nat.rec.{0} C base step n
        let rec_app = Expr::apps(nat_rec, [motive, base, step, n.clone()]);
        let value = {
            let e = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), rec_app);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Nat.accNatLt : (n : Nat) → Acc Nat.lt n`.
    ///
    /// Proof: `fun (n : Nat) => @Acc.intro Nat.lt n
    ///           (fun (m : Nat) (h : Nat.lt m n) => Nat.lt_wfLBound n m h)`.
    fn register_nat_acc_nat_lt(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.accNatLt");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let lvl1 = Level::succ(Level::zero());
        let acc = Expr::const_(Name::from_string("Acc"), vec![lvl1.clone()]);
        let acc_intro = Expr::const_(Name::from_string("Acc.intro"), vec![lvl1.clone()]);
        let lbound = Expr::const_(Name::from_string("Nat.lt_wfLBound"), vec![]);

        let acc_lt =
            |e: Expr| -> Expr { Expr::apps(acc.clone(), [nat.clone(), nat_lt.clone(), e]) };
        let lt = |a: Expr, c: Expr| -> Expr { Expr::apps(nat_lt.clone(), [a, c]) };

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());

        // Type: (n : Nat) → Acc Nat.lt n
        let ty = {
            let concl = acc_lt(n.clone());
            let e = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), concl);
            b.finish(e)
        };

        // g : (m : Nat) → Nat.lt m n → Acc Nat.lt m
        let g = {
            let mut gb = EnvDeclBuilder::child_of(&b);
            let (m_id, m) = gb.fresh_local(nat.clone());
            let h_ty = lt(m.clone(), n.clone());
            let (h_id, h) = gb.fresh_local(h_ty.clone());
            // Nat.lt_wfLBound n m h : Acc Nat.lt m
            let body = Expr::apps(lbound.clone(), [n.clone(), m.clone(), h.clone()]);
            let lam_h = gb.mk_lam(h_id, BinderInfo::Default, h_ty, body);
            let lam_m = gb.mk_lam(m_id, BinderInfo::Default, nat.clone(), lam_h);
            gb.finish_child(lam_m)
        };

        // @Acc.intro.{1} Nat Nat.lt n g
        let acc_n = Expr::apps(acc_intro, [nat.clone(), nat_lt.clone(), n.clone(), g]);
        let value = {
            let e = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), acc_n);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Nat.lt_wf : WellFounded Nat.lt`.
    ///
    /// Proof: `@WellFounded.intro Nat Nat.lt Nat.accNatLt`.
    fn register_nat_lt_wf(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.lt_wf");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let lvl1 = Level::succ(Level::zero());
        let wf = Expr::const_(Name::from_string("WellFounded"), vec![lvl1.clone()]);
        let wf_intro = Expr::const_(Name::from_string("WellFounded.intro"), vec![lvl1]);
        let acc_nat_lt = Expr::const_(Name::from_string("Nat.accNatLt"), vec![]);

        // Type: WellFounded Nat.lt   (= @WellFounded Nat Nat.lt)
        let ty = Expr::apps(wf, [nat.clone(), nat_lt.clone()]);
        // Value: @WellFounded.intro Nat Nat.lt Nat.accNatLt
        let value = Expr::apps(wf_intro, [nat.clone(), nat_lt.clone(), acc_nat_lt]);

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: false,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    const TARGETS: [&str; 3] = ["Nat.lt_wfLBound", "Nat.accNatLt", "Nat.lt_wf"];

    /// Each target must (a) type-check via the kernel `infer_type` and
    /// (b) have an EMPTY `axiom_deps` closure — no `sorry`, no domain axiom.
    fn check_sound(env: &Environment, name: &str) {
        let tc = TypeChecker::with_mode(env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string(name), vec![]))
            .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
        let deps = env
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(names.is_empty(), "{name} must be axiom-free, got {names:?}");
    }

    #[test]
    fn test_nat_lt_wf_registered_constructive_and_axiom_free() {
        let mut env = Environment::new();
        // `init_nat_lt_wf` self-bootstraps its dependencies (init_nat, init_lt,
        // init_well_founded, and the constructive Nat order theorems).
        env.init_nat_lt_wf().expect("first init_nat_lt_wf");
        // Idempotent re-registration must succeed.
        env.init_nat_lt_wf().expect("idempotent init_nat_lt_wf");

        // Kinds: two Theorems + one Definition, all retaining their value.
        for (name, kind) in [
            ("Nat.lt_wfLBound", ConstantKind::Theorem),
            ("Nat.accNatLt", ConstantKind::Theorem),
            ("Nat.lt_wf", ConstantKind::Definition),
        ] {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert_eq!(info.kind, kind, "{name} kind");
            assert!(info.value.is_some(), "{name} must retain its proof value");
        }

        // All three: type-check + empty axiom closure.
        for name in TARGETS {
            check_sound(&env, name);
        }

        // The two Theorems carry a `ProofQuality`; the `Nat.lt_wf` Definition
        // is reported `NotATheorem` (quality only ranks Theorems), so it is
        // covered by the `check_sound` axiom-closure assertion above.
        for name in ["Nat.lt_wfLBound", "Nat.accNatLt"] {
            let quality = env
                .proof_quality(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} proof_quality"));
            assert!(
                matches!(quality, ProofQuality::Constructive),
                "{name} must be Constructive, got {quality:?}"
            );
        }
    }

    /// The witnesses must also be present (and sound) when reached through the
    /// full default prelude, since `init_nat_lt_wf` is now wired into
    /// `init_prelude_extended`.
    #[test]
    fn test_nat_lt_wf_available_in_default_prelude() {
        let env = Environment::with_prelude();
        for name in TARGETS {
            check_sound(&env, name);
        }
    }
}
