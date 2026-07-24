// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Nat.sub`-level simplification equalities registered as real, kernel-checked
//! `Declaration::Theorem`s (NO axiom, NO `sorry`):
//!
//! - `Nat.sub_zero`       : `a - 0 = a`            (pure `@Eq.refl`; reused)
//! - `Nat.sub_self`       : `a - a = 0`            (`Nat.rec`; reused)
//! - `Nat.add_sub_cancel` : `a + b - b = a`        (`Nat.rec` on `b`; NEW)
//! - `Nat.zero_sub`       : `0 - a = 0`            (`Nat.rec` on `a`; NEW)
//! - `Nat.sub_one`        : `a - 1 = Nat.pred a`   (pure `@Eq.refl`; NEW)
//!
//! `Nat.sub_zero`/`Nat.sub_self` (and the helper `Nat.succ_sub_succ`) are
//! reused verbatim from `algebra_nat_sub_zero_proof.rs` and
//! `nat_sub_order_remaining_proof.rs`; this module seeds them via the existing
//! registration entry points and adds the three new lemmas.
//!
//! # Definitional facts (`data_types_nat.rs`)
//!
//! `Nat.sub m n := Nat.rec m (λ _ ih => Nat.pred ih) n` (recurses on the SECOND
//! arg) and `Nat.add m n := Nat.rec m (λ _ ih => Nat.succ ih) n` (recurses on
//! the SECOND arg). Hence:
//!
//! - `a - 0 ≡ a`, `a - Nat.succ k ≡ Nat.pred (a - k)`.
//! - `a + 0 ≡ a`, `a + Nat.succ k ≡ Nat.succ (a + k)`  (so `Nat.add_succ` is
//!   definitional and needs no separate lemma).
//! - `a - Nat.succ Nat.zero ≡ Nat.pred a` (special case → `Nat.sub_one` by rfl).
//! - `Nat.pred Nat.zero ≡ Nat.zero`.
//!
//! # Proof strategy (new lemmas)
//!
//! - **`Nat.add_sub_cancel`** — `Nat.rec` on `b`. Base (`b = 0`):
//!   `a + 0 - 0 ≡ a`, so `@Eq.refl Nat a`. Step (`b = succ k`,
//!   `ih : a + k - k = a`): `a + succ k - succ k ≡ succ (a + k) - succ k`
//!   (defeq via `Nat.add_succ`), then `Nat.succ_sub_succ (a+k) k :
//!   succ (a+k) - succ k = (a+k) - k`, chained with `ih` via `Eq.trans`.
//! - **`Nat.zero_sub`** — `Nat.rec` on `a`. Base (`a = 0`): `0 - 0 ≡ 0`, so
//!   `@Eq.refl Nat 0`. Step (`a = succ k`, `ih : 0 - k = 0`):
//!   `0 - succ k ≡ Nat.pred (0 - k)`, and `@congrArg Nat Nat (0 - k) 0
//!   Nat.pred ih : Nat.pred (0 - k) = Nat.pred 0 ≡ 0`.
//! - **`Nat.sub_one`** — `a - Nat.succ Nat.zero ≡ Nat.pred a`, so
//!   `@Eq.refl Nat (Nat.pred a)`.
//!
//! # Axiom closure
//!
//! Every lemma's transitive axiom closure is empty (`Nat.rec`/`Eq.refl`/
//! `Eq.trans`/`congrArg`/`Nat.succ_sub_succ` are recursor/constructor/empty-
//! closure theorems), so the domain-specific axiom count in
//! `data/axiom_audit.json` is unchanged. Each new lemma is routed through the
//! normal checked `add_decl` so the kernel re-verifies the proof term.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Kernel constants reused when building the `Nat.sub`-simp proof terms.
struct NatSubSimpConsts {
    nat: Expr,
    zero: Expr,
    succ: Expr,
    sub: Expr,
    pred: Expr,
    add: Expr,
    /// `Nat.rec.{0}` — the motive lands in `Prop = Sort 0`.
    nat_rec: Expr,
    succ_sub_succ_thm: Expr,
    /// `Eq.{1}` (`Nat : Sort 1`).
    eq: Expr,
    /// `Eq.refl.{1}`.
    eq_refl: Expr,
    /// `Eq.trans.{1}`.
    eq_trans: Expr,
    /// `congrArg.{1,1}`.
    congr_arg: Expr,
}

impl NatSubSimpConsts {
    fn new() -> Self {
        let one = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            sub: Expr::const_(Name::from_string("Nat.sub"), vec![]),
            pred: Expr::const_(Name::from_string("Nat.pred"), vec![]),
            add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            succ_sub_succ_thm: Expr::const_(Name::from_string("Nat.succ_sub_succ"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![one.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![one.clone(), one]),
        }
    }

    fn sub_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.sub.clone(), [x, y])
    }
    fn add_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.add.clone(), [x, y])
    }
    fn pred_of(&self, x: Expr) -> Expr {
        Expr::app(self.pred.clone(), x)
    }
    fn succ_of(&self, x: Expr) -> Expr {
        Expr::app(self.succ.clone(), x)
    }
    /// `@Eq Nat x y`.
    fn eq_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq.clone(), [self.nat.clone(), x, y])
    }
    /// `@Eq.refl Nat x : Eq Nat x x`.
    fn eq_refl_app(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.nat.clone(), x])
    }
}

impl Environment {
    /// Register the `Nat.sub`-level simp equalities as real, kernel-checked
    /// `Declaration::Theorem`s.
    ///
    /// Reuses `Nat.sub_zero`, `Nat.sub_self` (+ helper `Nat.succ_sub_succ`)
    /// from the existing constructive registrations, and adds the new
    /// `Nat.add_sub_cancel`, `Nat.zero_sub`, `Nat.sub_one`.
    ///
    /// # Contract
    ///
    /// REQUIRES: nothing — seeds `Nat`/`Eq` and the reused lemmas via the
    ///           idempotent registration entry points below.
    /// ENSURES: On success each lemma resolves via `env.get_const(name)`.
    /// ENSURES: Idempotent.
    /// ENSURES: Each lemma's transitive axiom closure is empty; the
    ///          domain-specific axiom count is unchanged.
    pub(crate) fn init_nat_sub_simp_lemmas(&mut self) -> Result<(), EnvError> {
        // SOUNDNESS: import-mode Nat core arithmetic cluster gate — every lemma
        // here is stated over the import-gated Nat.sub/Nat.add seeds (see
        // data_types_nat.rs::init_nat); the genuine olean lemma web imports
        // through the checked path instead. Default lane byte-identical.
        if self.suppress_lossy_structure_stubs {
            self.nat_sub_simp_lemmas_init = true;
            return Ok(());
        }
        if self.nat_sub_simp_lemmas_init {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;
        // Reuse: `Nat.sub_zero` (pure rfl Theorem).
        self.register_nat_sub_zero_proof()?;
        // Reuse: `Nat.succ_sub_succ` + `Nat.sub_self` (Nat.rec Theorems). This
        // also registers the rest of the `Nat.sub`-order family (all empty-
        // closure constructive Theorems).
        self.register_nat_sub_order_remaining_proofs()?;

        let c = NatSubSimpConsts::new();
        self.register_nat_add_sub_cancel(&c)?;
        self.register_nat_zero_sub(&c)?;
        self.register_nat_sub_one(&c)?;

        self.nat_sub_simp_lemmas_init = true;
        Ok(())
    }

    /// `Nat.add_sub_cancel : ∀ a b, Eq (a + b - b) a`.
    fn register_nat_add_sub_cancel(&mut self, c: &NatSubSimpConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.add_sub_cancel");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());

        // Type: ∀ a b, Eq (a + b - b) a
        let type_ = {
            let concl = c.eq_of(
                c.sub_of(c.add_of(a.clone(), bb.clone()), bb.clone()),
                a.clone(),
            );
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // motive: fun (t : Nat) => Eq (a + t - t) a
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let body = c.eq_of(
                c.sub_of(c.add_of(a.clone(), t.clone()), t.clone()),
                a.clone(),
            );
            let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
            mb.finish_child(lam)
        };
        // base (t = 0): `a + 0 - 0 ≡ a - 0 ≡ a`, so `@Eq.refl Nat a`.
        let base = c.eq_refl_app(a.clone());
        // step: fun (k : Nat) (ih : Eq (a + k - k) a) =>
        //   @Eq.trans Nat (a + succ k - succ k) ((a + k) - k) a
        //     (Nat.succ_sub_succ (a + k) k)  -- succ (a+k) - succ k = (a+k) - k,
        //                                       defeq to a + succ k - succ k.
        //     ih
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(c.nat.clone());
            let add_a_k = c.add_of(a.clone(), k.clone());
            let sub_addak_k = c.sub_of(add_a_k.clone(), k.clone());
            let ih_type = c.eq_of(sub_addak_k.clone(), a.clone());
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            // LHS of the conclusion at `succ k`: `a + succ k - succ k`.
            let lhs = c.sub_of(
                c.add_of(a.clone(), c.succ_of(k.clone())),
                c.succ_of(k.clone()),
            );
            // Nat.succ_sub_succ (a+k) k : succ (a+k) - succ k = (a+k) - k,
            // whose LHS is defeq to `a + succ k - succ k`.
            let succ_sub_succ = Expr::apps(c.succ_sub_succ_thm.clone(), [add_a_k, k.clone()]);
            let body = Expr::apps(
                c.eq_trans.clone(),
                [
                    c.nat.clone(),
                    lhs,
                    sub_addak_k,
                    a.clone(),
                    succ_sub_succ,
                    ih,
                ],
            );
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

        // SOUNDNESS: kernel-checked `Nat.rec` term over `Nat.add`/`Nat.sub`
        // (reducible Definitions). Uses only the foundational `Eq.refl`/
        // `Eq.trans` and the empty-closure `Nat.succ_sub_succ`. No
        // `Declaration::Axiom`, no `sorry`, no self-reference.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.zero_sub : ∀ a, Eq (0 - a) 0`.
    fn register_nat_zero_sub(&mut self, c: &NatSubSimpConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.zero_sub");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());

        // Type: ∀ a, Eq (0 - a) 0
        let type_ = {
            let concl = c.eq_of(c.sub_of(c.zero.clone(), a.clone()), c.zero.clone());
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), concl);
            b.finish(e)
        };

        // motive: fun (t : Nat) => Eq (0 - t) 0
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let body = c.eq_of(c.sub_of(c.zero.clone(), t.clone()), c.zero.clone());
            let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
            mb.finish_child(lam)
        };
        // base (t = 0): `0 - 0 ≡ 0`, so `@Eq.refl Nat 0`.
        let base = c.eq_refl_app(c.zero.clone());
        // step: fun (k : Nat) (ih : Eq (0 - k) 0) =>
        //   @congrArg Nat Nat (0 - k) 0 Nat.pred ih
        //     : Eq (pred (0 - k)) (pred 0)
        //     ≡ Eq (0 - succ k) 0   (since `0 - succ k ≡ pred (0 - k)` and
        //                            `pred 0 ≡ 0`).
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(c.nat.clone());
            let sub_zero_k = c.sub_of(c.zero.clone(), k.clone());
            let ih_type = c.eq_of(sub_zero_k.clone(), c.zero.clone());
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let body = Expr::apps(
                c.congr_arg.clone(),
                [
                    c.nat.clone(),
                    c.nat.clone(),
                    sub_zero_k,
                    c.zero.clone(),
                    c.pred.clone(),
                    ih,
                ],
            );
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
            let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_ih);
            sb.finish_child(lam_k)
        };

        let value = {
            let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, a.clone()]);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), rec_app);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked `Nat.rec` term over `Nat.sub`/`Nat.pred`
        // (reducible Definitions). Uses only the foundational `Eq.refl` and
        // `congrArg`. No `Declaration::Axiom`, no `sorry`, no self-reference.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.sub_one : ∀ a, Eq (a - 1) (Nat.pred a)`.
    ///
    /// `1 ≡ Nat.succ Nat.zero`, so `a - succ 0 ≡ Nat.pred (a - 0) ≡ Nat.pred a`,
    /// and `@Eq.refl Nat (Nat.pred a)` type-checks against the stated type.
    fn register_nat_sub_one(&mut self, c: &NatSubSimpConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.sub_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let one = c.succ_of(c.zero.clone());

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());

        // Type: ∀ a, Eq (a - 1) (Nat.pred a)
        let type_ = {
            let concl = c.eq_of(c.sub_of(a.clone(), one.clone()), c.pred_of(a.clone()));
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), concl);
            b.finish(e)
        };

        // Value: fun (a : Nat) => @Eq.refl Nat (Nat.pred a)
        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(c.nat.clone());
            let refl = c.eq_refl_app(c.pred_of(va));
            let e = vb.mk_lam(va_id, BinderInfo::Default, c.nat.clone(), refl);
            vb.finish(e)
        };

        // SOUNDNESS: pure `@Eq.refl Nat (Nat.pred a)`; the kernel accepts it
        // against `a - 1 = Nat.pred a` because `a - Nat.succ Nat.zero`
        // iota/delta-reduces to `Nat.pred a`. No `Declaration::Axiom`, no
        // `sorry`, no self-reference. Axiom closure empty.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    const FAMILY: [&str; 5] = [
        "Nat.sub_zero",
        "Nat.sub_self",
        "Nat.add_sub_cancel",
        "Nat.zero_sub",
        "Nat.sub_one",
    ];

    fn registered() -> Environment {
        let mut env = Environment::new();
        env.init_nat_sub_simp_lemmas().expect("registration");
        env.init_nat_sub_simp_lemmas()
            .expect("idempotent re-registration");
        env
    }

    #[test]
    fn test_nat_sub_simp_family_registered_as_theorems() {
        let env = registered();
        for name in FAMILY {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{name} must be a Theorem, not {:?}",
                info.kind
            );
            assert!(
                info.value.is_some(),
                "{name} must retain its proof value (not a body-less Axiom)"
            );
        }
    }

    #[test]
    fn test_nat_sub_simp_family_proof_terms_typecheck() {
        let env = registered();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in FAMILY {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.as_ref().expect("Theorem has value");
            tc.check_type(value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} proof term must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_nat_sub_simp_family_axiom_closure_empty() {
        let env = registered();
        for name in FAMILY {
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} registered, axiom_deps should be Some"));
            let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                names.is_empty(),
                "{name} must have EMPTY domain-axiom closure, got {names:?}"
            );
            assert_eq!(
                env.proof_quality(&Name::from_string(name)),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
        }
    }

    #[test]
    fn test_nat_sub_simp_family_present_in_prelude() {
        let env = Environment::with_prelude();
        for name in FAMILY {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{name} must resolve in the default prelude env"
            );
        }
    }
}
