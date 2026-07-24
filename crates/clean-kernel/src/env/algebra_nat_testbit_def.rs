// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive definition of `Nat.testBit : Nat → Nat → Bool`, replacing the
//! historical `Declaration::Axiom` admitted in `data_types_nat.rs`.
//!
//! `Nat.testBit n i` is the `i`-th bit of `n`, i.e. the parity of `n` shifted
//! right `i` times. We build it from the already-constructive `Nat.div2`
//! parity foundation (`algebra_nat_div2_lt_self_proof.rs`):
//!
//! ```text
//! Nat.iterDiv2 i n  := iterate Nat.div2 i times on n   -- = n / 2^i
//! Nat.toBoolPar p   := match p with 0 => false | _+1 => true
//! Nat.testBit n i   := Nat.toBoolPar (Nat.div2Par (Nat.iterDiv2 i n))
//! ```
//!
//! Here `Nat.div2Par x ∈ {0, 1}` is `x mod 2` (the parity carry of the
//! div2 pair-fold), so `toBoolPar (div2Par x)` is exactly "x is odd". Applied
//! to `iterDiv2 i n = n / 2^i`, that is bit `i` of `n`.
//!
//! # Reducer agreement (soundness)
//!
//! There is NO native reducer for `Nat.testBit` (only `Nat.land`/`lor`/`xor`/
//! `shiftRight`/`shiftLeft` have one — see `native_reducers_arith.rs`), so
//! every ground `Nat.testBit` evaluation goes through delta+iota of THIS
//! definition. Ground `rfl` checks like `Nat.testBit 6 1 = true := rfl` are
//! verified by the kernel reducing the body, with no fast-path shortcut to
//! disagree with.
//!
//! # Axiom closure
//!
//! `Nat.iterDiv2` / `Nat.toBoolPar` are reducible Definitions over `Nat.rec`,
//! `Bool.rec`, `Nat.div2`, `Bool.true`, `Bool.false`; `Nat.testBit` composes
//! them with `Nat.div2Par`. None of these are axioms, so `env.axiom_deps` is
//! empty for every declaration introduced here. (`Nat.div2`/`Nat.div2Par` are
//! themselves axiom-free Definitions from `register_nat_div2_lt_self_proof`.)

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Nat.iterDiv2`, `Nat.toBoolPar`, and the real `Nat.testBit`
    /// Definition, replacing the admitted `Nat.testBit` axiom.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` (Nat, zero, succ, rec), `self.init_bool()`
    ///           (Bool, Bool.true, Bool.false, Bool.rec), and
    ///           `self.register_nat_div2_lt_self_proof()` (Nat.div2,
    ///           Nat.div2Par).
    /// ENSURES: On success, `Nat.iterDiv2` / `Nat.toBoolPar` are reducible
    ///          Definitions and `Nat.testBit` is a reducible
    ///          `Declaration::Definition` (NOT an Axiom).
    /// ENSURES: Idempotent — re-invocation is a no-op once `Nat.testBit` is a
    ///          Definition.
    pub(crate) fn register_nat_testbit_def(&mut self) -> Result<(), EnvError> {
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
        // Dependencies (each idempotent).
        self.init_nat()?;
        self.init_bool()?;
        self.register_nat_div2_lt_self_proof()?; // Nat.div2, Nat.div2Par

        // If testBit is already a real Definition we are done. If it is still
        // the admitted Axiom, discharge it so the real Definition can be added.
        let testbit_name = Name::from_string("Nat.testBit");
        if let Some(info) = self.get_const(&testbit_name) {
            if matches!(info.kind, super::types::ConstantKind::Definition) {
                return Ok(());
            }
        }
        // Discharge the admitted `Nat.testBit` axiom (no-op if already absent).
        self.discharge_axiom_for_redefinition(&testbit_name);

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let div2 = Expr::const_(Name::from_string("Nat.div2"), vec![]);
        let div2_par = Expr::const_(Name::from_string("Nat.div2Par"), vec![]);

        // 1. Nat.iterDiv2 : Nat → Nat → Nat
        //    iterDiv2 i = Nat.rec (fun n => n) (fun _ ih => fun n => ih (div2 n)) i
        //    i.e. iterate Nat.div2 i times, recursing on the *inside*:
        //        iterDiv2 0       ≡ fun n => n          (identity)
        //        iterDiv2 (succ k) n ≡ iterDiv2 k (div2 n)
        //    This INNER recursion is what makes `testBit n (succ i)` reduce to
        //    `testBit (div2 n) i` definitionally (the key step-3 unfolding).
        //    The motive is `Nat → Nat` (a Type), so Nat.rec lives at universe 1.
        if self.get_const(&Name::from_string("Nat.iterDiv2")).is_none() {
            // Nat → Nat
            let nat_to_nat = Expr::pi(BinderInfo::Default, nat.clone(), nat.clone());
            let type_ = Expr::pi(BinderInfo::Default, nat.clone(), nat_to_nat.clone());
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (i_id, i) = b.fresh_local(nat.clone());
                // motive: fun (_ : Nat) => (Nat → Nat)
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&b);
                    let (t_id, _t) = mb.fresh_local(nat.clone());
                    let lam = mb.mk_lam(t_id, BinderInfo::Default, nat.clone(), nat_to_nat.clone());
                    mb.finish_child(lam)
                };
                // base: fun (n : Nat) => n   (identity : Nat → Nat)
                let base = {
                    let mut bb = EnvDeclBuilder::child_of(&b);
                    let (n_id, n) = bb.fresh_local(nat.clone());
                    let lam = bb.mk_lam(n_id, BinderInfo::Default, nat.clone(), n);
                    bb.finish_child(lam)
                };
                // step: fun (_ : Nat) (ih : Nat → Nat) => fun (n : Nat) => ih (div2 n)
                let step = {
                    let mut sb = EnvDeclBuilder::child_of(&b);
                    let (k_id, _k) = sb.fresh_local(nat.clone());
                    let (ih_id, ih) = sb.fresh_local(nat_to_nat.clone());
                    let (n_id, n) = sb.fresh_local(nat.clone());
                    let body = Expr::app(ih.clone(), Expr::app(div2.clone(), n));
                    let lam = sb.mk_lam(n_id, BinderInfo::Default, nat.clone(), body);
                    let lam = sb.mk_lam(ih_id, BinderInfo::Default, nat_to_nat.clone(), lam);
                    let lam = sb.mk_lam(k_id, BinderInfo::Default, nat.clone(), lam);
                    sb.finish_child(lam)
                };
                // @Nat.rec.{1} motive base step i   (motive is Type-valued ⇒ universe 1)
                let nat_rec1 = Expr::const_(
                    Name::from_string("Nat.rec"),
                    vec![Level::succ(Level::zero())],
                );
                let rec_app = Expr::apps(nat_rec1, [motive, base, step, i]);
                let val = b.mk_lam(i_id, BinderInfo::Default, nat.clone(), rec_app);
                b.finish(val)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Nat.iterDiv2"),
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            })?;
        }

        // 2. Nat.toBoolPar : Nat → Bool
        //    toBoolPar p = Nat.rec Bool.false (fun _ _ => Bool.true) p
        //    so toBoolPar 0 ≡ false, toBoolPar (succ _) ≡ true.
        if self
            .get_const(&Name::from_string("Nat.toBoolPar"))
            .is_none()
        {
            let type_ = Expr::pi(BinderInfo::Default, nat.clone(), bool_ty.clone());
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(nat.clone());
                // motive: fun (_ : Nat) => Bool
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&b);
                    let (t_id, _t) = mb.fresh_local(nat.clone());
                    let lam = mb.mk_lam(t_id, BinderInfo::Default, nat.clone(), bool_ty.clone());
                    mb.finish_child(lam)
                };
                // step: fun (_ : Nat) (_ : Bool) => Bool.true
                let step = {
                    let mut sb = EnvDeclBuilder::child_of(&b);
                    let (k_id, _k) = sb.fresh_local(nat.clone());
                    let (ih_id, _ih) = sb.fresh_local(bool_ty.clone());
                    let lam = sb.mk_lam(
                        ih_id,
                        BinderInfo::Default,
                        bool_ty.clone(),
                        bool_true.clone(),
                    );
                    let lam = sb.mk_lam(k_id, BinderInfo::Default, nat.clone(), lam);
                    sb.finish_child(lam)
                };
                // @Nat.rec.{1} motive Bool.false step p   (Bool : Type ⇒ universe 1)
                let nat_rec1 = Expr::const_(
                    Name::from_string("Nat.rec"),
                    vec![Level::succ(Level::zero())],
                );
                let rec_app = Expr::apps(nat_rec1, [motive, bool_false.clone(), step, p]);
                let val = b.mk_lam(p_id, BinderInfo::Default, nat.clone(), rec_app);
                b.finish(val)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Nat.toBoolPar"),
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            })?;
        }

        // 3. Nat.testBit : Nat → Nat → Bool
        //    testBit n i := toBoolPar (div2Par (iterDiv2 i n))
        let testbit_type = Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::pi(BinderInfo::Default, nat.clone(), bool_ty.clone()),
        );
        let testbit_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (i_id, i) = b.fresh_local(nat.clone());
            let iter_div2 = Expr::const_(Name::from_string("Nat.iterDiv2"), vec![]);
            let to_bool_par = Expr::const_(Name::from_string("Nat.toBoolPar"), vec![]);
            // iterDiv2 i n
            let shifted = Expr::apps(iter_div2, [i.clone(), n.clone()]);
            // div2Par (iterDiv2 i n)
            let parity = Expr::app(div2_par.clone(), shifted);
            // toBoolPar (...)
            let body = Expr::app(to_bool_par, parity);
            let val = b.mk_lam(i_id, BinderInfo::Default, nat.clone(), body);
            let val = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), val);
            b.finish(val)
        };

        // Replace the admitted axiom (if present) with the real Definition.
        // `add_decl` overwrites an existing declaration of the same name.
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Nat.testBit"),
            level_params: vec![],
            type_: testbit_type,
            value: testbit_value,
            is_reducible: true,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    fn env_with_testbit() -> Environment {
        let mut env = Environment::new();
        env.register_nat_testbit_def()
            .expect("testBit registration");
        env
    }

    fn nat_lit(n: u64) -> Expr {
        let mut e = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        for _ in 0..n {
            e = Expr::app(succ.clone(), e.clone());
        }
        e
    }

    #[test]
    fn test_testbit_is_definition_not_axiom() {
        let env = env_with_testbit();
        for (name, kind) in [
            ("Nat.iterDiv2", ConstantKind::Definition),
            ("Nat.toBoolPar", ConstantKind::Definition),
            ("Nat.testBit", ConstantKind::Definition),
        ] {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert_eq!(info.kind, kind, "{name} kind mismatch");
            assert!(info.value.is_some(), "{name} must retain its value");
        }
    }

    #[test]
    fn test_testbit_idempotent() {
        let mut env = env_with_testbit();
        env.register_nat_testbit_def()
            .expect("idempotent re-registration");
    }

    #[test]
    fn test_testbit_type_checks() {
        let env = env_with_testbit();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in ["Nat.iterDiv2", "Nat.toBoolPar", "Nat.testBit"] {
            let _ = tc
                .infer_type(&Expr::const_(Name::from_string(name), vec![]))
                .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
        }
    }

    /// `Nat.testBit` actually computes the bit of `n` on ground inputs.
    /// Builds `@Eq.refl Bool (testBit N I)` and checks it against the stated
    /// type `Eq Bool (testBit N I) B`, forcing the kernel to reduce.
    #[test]
    fn test_testbit_ground_computations() {
        let mut env = env_with_testbit();
        env.init_eq().expect("init_eq");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );
        let testbit = Expr::const_(Name::from_string("Nat.testBit"), vec![]);

        // (n, i, expected bit)  — bit i of n.
        // 6 = 0b110 : bit0=0, bit1=1, bit2=1, bit3=0
        // 5 = 0b101 : bit0=1, bit1=0, bit2=1
        // 0 : all bits 0
        for (n, i, expected) in [
            (6u64, 0u64, false),
            (6, 1, true),
            (6, 2, true),
            (6, 3, false),
            (5, 0, true),
            (5, 1, false),
            (5, 2, true),
            (0, 0, false),
            (0, 5, false),
            (1, 0, true),
            (13, 0, true), // 0b1101
            (13, 1, false),
            (13, 2, true),
            (13, 3, true),
        ] {
            let exp = if expected {
                bool_true.clone()
            } else {
                bool_false.clone()
            };
            let lhs = Expr::apps(testbit.clone(), [nat_lit(n), nat_lit(i)]);
            let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
            let stated = Expr::apps(eq_const, [bool_ty.clone(), lhs.clone(), exp.clone()]);
            let proof = Expr::apps(eq_refl.clone(), [bool_ty.clone(), lhs]);
            let inferred = tc
                .infer_type(&proof)
                .unwrap_or_else(|e| panic!("testBit {n} {i} refl should infer: {e:?}"));
            assert!(
                tc.is_def_eq(&inferred, &stated),
                "testBit {n} {i} should be {expected}"
            );
        }
    }

    /// The two definitional unfolding equations of `Nat.testBit` hold by
    /// `rfl` for a SYMBOLIC (free-variable) `n`, which is the foundation for
    /// the step-3 `testBit_bitwise` induction:
    ///   - `Nat.testBit n 0           ≡ Nat.toBoolPar (Nat.div2Par n)`
    ///   - `Nat.testBit n (Nat.succ i) ≡ Nat.testBit (Nat.div2 n) i`
    ///
    /// The second is the load-bearing one (inner-recursion of `iterDiv2`).
    #[test]
    fn test_testbit_symbolic_unfolding_eqs() {
        use crate::env::decl_builder::EnvDeclBuilder;
        let mut env = env_with_testbit();
        env.init_eq().expect("init_eq");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
        let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let testbit = Expr::const_(Name::from_string("Nat.testBit"), vec![]);
        let div2 = Expr::const_(Name::from_string("Nat.div2"), vec![]);
        let div2_par = Expr::const_(Name::from_string("Nat.div2Par"), vec![]);
        let to_bool_par = Expr::const_(Name::from_string("Nat.toBoolPar"), vec![]);

        // Build `∀ (n i : Nat), <lhs> = <rhs>` proved by `fun n i => rfl`, and
        // type-check it: kernel only accepts it if lhs ≡ rhs definitionally.
        let check_eq = |build_lhs_rhs: &dyn Fn(&Expr, &Expr) -> (Expr, Expr)| {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (i_id, i) = b.fresh_local(nat.clone());
            let (lhs, rhs) = build_lhs_rhs(&n, &i);
            let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
            let stated = Expr::apps(eq_const, [bool_ty.clone(), lhs.clone(), rhs]);
            let eq_refl = Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            );
            let proof = Expr::apps(eq_refl, [bool_ty.clone(), lhs]);
            // ∀ n i, stated  ;  proof  fun n i => rfl
            let pi = {
                let inner = b.mk_pi(i_id, BinderInfo::Default, nat.clone(), stated.clone());
                b.mk_pi(n_id, BinderInfo::Default, nat.clone(), inner)
            };
            let lam = {
                let inner = b.mk_lam(i_id, BinderInfo::Default, nat.clone(), proof);
                b.mk_lam(n_id, BinderInfo::Default, nat.clone(), inner)
            };
            let pi = b.finish(pi);
            let lam = b.finish(lam);
            let inferred = tc
                .infer_type(&lam)
                .unwrap_or_else(|e| panic!("symbolic testBit eq refl should infer: {e:?}"));
            assert!(
                tc.is_def_eq(&inferred, &pi),
                "symbolic testBit unfolding equation must hold by rfl"
            );
        };

        // testBit n 0 ≡ toBoolPar (div2Par n)
        check_eq(&|n, _i| {
            let lhs = Expr::apps(testbit.clone(), [n.clone(), zero.clone()]);
            let rhs = Expr::app(to_bool_par.clone(), Expr::app(div2_par.clone(), n.clone()));
            (lhs, rhs)
        });
        // testBit n (succ i) ≡ testBit (div2 n) i
        check_eq(&|n, i| {
            let lhs = Expr::apps(
                testbit.clone(),
                [n.clone(), Expr::app(succ.clone(), i.clone())],
            );
            let rhs = Expr::apps(
                testbit.clone(),
                [Expr::app(div2.clone(), n.clone()), i.clone()],
            );
            (lhs, rhs)
        });
    }

    #[test]
    fn test_testbit_axiom_deps_empty() {
        let env = env_with_testbit();
        for name in ["Nat.iterDiv2", "Nat.toBoolPar", "Nat.testBit"] {
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} registered; axiom_deps should be Some"));
            let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                names.is_empty(),
                "{name} must have empty axiom closure, got {names:?}"
            );
        }
    }
}
