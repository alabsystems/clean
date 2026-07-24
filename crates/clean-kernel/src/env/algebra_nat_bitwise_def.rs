// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive definition of `Nat.bitwise (f : Bool → Bool → Bool) : Nat → Nat
//! → Nat`, and the discharge of the admitted `Nat.land` / `Nat.lor` / `Nat.xor`
//! domain axioms to real reducible Definitions `Nat.bitwise and/or/xor`
//! (Track II step 1 + 2).
//!
//! # Why a fuel fold instead of well-founded recursion
//!
//! Lean-core defines `Nat.bitwise` by well-founded recursion on the first
//! argument. In Clean, the recursive call would carry an `Acc` proof
//! (`Nat.lt_wfLBound …`) that is only PROPOSITIONALLY — not DEFINITIONALLY —
//! equal to the canonical `Nat.accNatLt (div2 m)`. So the load-bearing
//! div2-commutation equation
//!     `div2 (bitwise f m n) = bitwise f (div2 m) (div2 n)`
//! would be STUCK under `rfl` (the `fixFEq`/Acc-proof mismatch lesson). We
//! therefore use a TOTAL primitive-recursive fold on an explicit `fuel`
//! counter, recursing on `(div2 m, div2 n)` inside the fold (the same
//! inner-recursion trick as `Nat.iterDiv2`), so every single unfolding step is
//! definitional. The fuel `m + n` is always ≥ the bit-length of both inputs, and
//! the bit-extension lemma (`testBit_bitwise`, step 3) only needs `f false
//! false = false` to absorb the truncation — which holds for `and`/`or`/`xor`.
//!
//! ```text
//! Nat.ofBool b        := Bool.rec 0 1 b                  -- false→0, true→1
//! Nat.bitwiseAux f fuel m n :=
//!   Nat.rec
//!     (fun _ _ => 0)                                     -- fuel = 0
//!     (fun _ ih => fun m n =>                            -- fuel = succ k
//!        let r := ih (div2 m) (div2 n)
//!        (r + r) + Nat.ofBool (f (testBit m 0) (testBit n 0)))
//!     fuel
//! Nat.bitwise f m n   := bitwiseAux f (m + n) m n
//! ```
//!
//! The motive of the inner `Nat.rec` is `Nat → Nat → Nat`, so it lives at
//! universe 1; `Nat.ofBool` uses `Bool.rec.{1}` over the `fun _ => Nat` motive.
//!
//! # Reducer agreement (soundness, the migration's central risk)
//!
//! `Nat.land`/`lor`/`xor` each have a NATIVE reducer (`native_reducers_arith.rs`)
//! that computes the true bignat bitwise op on GROUND literals and fires BEFORE
//! delta-unfolding. After this redefinition, `Nat.land := Nat.bitwise and` is a
//! reducible Definition that ALSO computes the bitwise AND. The two paths must
//! agree on ground inputs; the module tests
//! (`test_ground_bitwise_matches_reducer`, `test_ground_bitwise_def_unfold`)
//! pin def-eq of `Nat.land 6 3` to the literal `2` through BOTH the reducer fast
//! path AND (with the reducer suppressed by a symbolic wrapper) the delta path.
//!
//! # Axiom closure
//!
//! `Nat.ofBool` / `Nat.bitwiseAux` / `Nat.bitwise` / the three redefined
//! bitwise ops are reducible Definitions over `Nat.rec`, `Bool.rec`, `Nat.add`,
//! `Nat.div2`, `Nat.testBit` — none axioms. So `env.axiom_deps` is empty for
//! every declaration introduced here, and the redefinition DISCHARGES three
//! previously-admitted domain axioms.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants for the bitwise definitions.
struct BW {
    nat: Expr,
    zero: Expr,
    succ: Expr,
    one: Expr,
    add: Expr,
    div2: Expr,
    testbit: Expr,
    bool_ty: Expr,
    bool_to_bool_to_bool: Expr,
    nat_to_nat_to_nat: Expr,
}

impl BW {
    fn new() -> Self {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let one = Expr::app(succ.clone(), zero.clone());
        let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
        // Bool → Bool → Bool
        let bool_to_bool_to_bool = Expr::pi(
            BinderInfo::Default,
            bool_ty.clone(),
            Expr::pi(BinderInfo::Default, bool_ty.clone(), bool_ty.clone()),
        );
        // Nat → Nat → Nat
        let nat_to_nat_to_nat = Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
        );
        Self {
            nat,
            zero,
            succ,
            one,
            add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            div2: Expr::const_(Name::from_string("Nat.div2"), vec![]),
            testbit: Expr::const_(Name::from_string("Nat.testBit"), vec![]),
            bool_ty,
            bool_to_bool_to_bool,
            nat_to_nat_to_nat,
        }
    }

    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.add.clone(), [a, b])
    }
    fn div2(&self, n: Expr) -> Expr {
        Expr::app(self.div2.clone(), n)
    }
    /// `Nat.testBit n 0`.
    fn bit0(&self, n: Expr) -> Expr {
        Expr::apps(self.testbit.clone(), [n, self.zero.clone()])
    }
}

/// `Nat.ofBool : Bool → Nat`, reducible Definition
/// `fun b => Bool.rec.{1} (fun _ => Nat) 0 1 b`.
fn build_of_bool(c: &BW) -> (Expr, Expr) {
    let type_ = Expr::pi(BinderInfo::Default, c.bool_ty.clone(), c.nat.clone());
    let mut b = EnvDeclBuilder::new();
    let (bv_id, bv) = b.fresh_local(c.bool_ty.clone());
    // motive: fun (_ : Bool) => Nat
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, _t) = mb.fresh_local(c.bool_ty.clone());
        let lam = mb.mk_lam(t_id, BinderInfo::Default, c.bool_ty.clone(), c.nat.clone());
        mb.finish_child(lam)
    };
    // Bool.rec.{1} motive <false=0> <true=1> b
    let bool_rec = Expr::const_(
        Name::from_string("Bool.rec"),
        vec![Level::succ(Level::zero())],
    );
    let rec_app = Expr::apps(bool_rec, [motive, c.zero.clone(), c.one.clone(), bv]);
    let val = b.mk_lam(bv_id, BinderInfo::Default, c.bool_ty.clone(), rec_app);
    (type_, b.finish(val))
}

/// `Nat.bitwiseAux : (Bool → Bool → Bool) → Nat → Nat → Nat → Nat`.
///
/// `fun f fuel => Nat.rec.{1} (fun _ _ => 0)
///     (fun _ ih => fun m n =>
///        (ih (div2 m) (div2 n) + ih (div2 m) (div2 n))
///        + Nat.ofBool (f (testBit m 0) (testBit n 0)))
///     fuel`.
///
/// The inner `Nat.rec` motive is `Nat → Nat → Nat`, so it is at universe 1,
/// recursing on the INSIDE: `bitwiseAux f (succ k) m n` reduces to the step body
/// with `ih = bitwiseAux f k`, i.e. recurses at `(div2 m, div2 n)` with fuel `k`.
fn build_bitwise_aux(c: &BW) -> (Expr, Expr) {
    let of_bool = Expr::const_(Name::from_string("Nat.ofBool"), vec![]);
    // type: (Bool→Bool→Bool) → Nat → Nat → Nat → Nat
    let type_ = Expr::pi(
        BinderInfo::Default,
        c.bool_to_bool_to_bool.clone(),
        Expr::pi(
            BinderInfo::Default,
            c.nat.clone(), // fuel
            c.nat_to_nat_to_nat.clone(),
        ),
    );

    let mut b = EnvDeclBuilder::new();
    let (f_id, f) = b.fresh_local(c.bool_to_bool_to_bool.clone());
    let (fuel_id, fuel) = b.fresh_local(c.nat.clone());

    // motive: fun (_ : Nat) => (Nat → Nat → Nat)
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, _t) = mb.fresh_local(c.nat.clone());
        let lam = mb.mk_lam(
            t_id,
            BinderInfo::Default,
            c.nat.clone(),
            c.nat_to_nat_to_nat.clone(),
        );
        mb.finish_child(lam)
    };

    // base: fun (m n : Nat) => 0
    let base = {
        let mut bb = EnvDeclBuilder::child_of(&b);
        let (m_id, _m) = bb.fresh_local(c.nat.clone());
        let (n_id, _n) = bb.fresh_local(c.nat.clone());
        let lam = bb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), c.zero.clone());
        let lam = bb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam);
        bb.finish_child(lam)
    };

    // step: fun (_ : Nat) (ih : Nat → Nat → Nat) => fun (m n : Nat) =>
    //         let r := ih (div2 m) (div2 n);
    //         (r + r) + Nat.ofBool (f (testBit m 0) (testBit n 0))
    let step = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let (k_id, _k) = sb.fresh_local(c.nat.clone());
        let (ih_id, ih) = sb.fresh_local(c.nat_to_nat_to_nat.clone());
        let (m_id, m) = sb.fresh_local(c.nat.clone());
        let (n_id, n) = sb.fresh_local(c.nat.clone());
        // r := ih (div2 m) (div2 n)
        let r = Expr::apps(ih.clone(), [c.div2(m.clone()), c.div2(n.clone())]);
        // f (testBit m 0) (testBit n 0)
        let fbit = Expr::apps(f.clone(), [c.bit0(m.clone()), c.bit0(n.clone())]);
        let ofb = Expr::app(of_bool.clone(), fbit);
        // (r + r) + ofBool(...)
        let body = c.add(c.add(r.clone(), r), ofb);
        let lam = sb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
        let lam = sb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam);
        let lam = sb.mk_lam(ih_id, BinderInfo::Default, c.nat_to_nat_to_nat.clone(), lam);
        let lam = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam);
        sb.finish_child(lam)
    };

    // Nat.rec.{1} motive base step fuel : Nat → Nat → Nat
    let nat_rec1 = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    let rec_app = Expr::apps(nat_rec1, [motive, base, step, fuel]);
    let val = b.mk_lam(fuel_id, BinderInfo::Default, c.nat.clone(), rec_app);
    let val = b.mk_lam(
        f_id,
        BinderInfo::Default,
        c.bool_to_bool_to_bool.clone(),
        val,
    );
    (type_, b.finish(val))
}

/// `Nat.bitwise : (Bool → Bool → Bool) → Nat → Nat → Nat`, reducible Definition
/// `fun f m n => Nat.bitwiseAux f (m + n) m n`.
fn build_bitwise(c: &BW) -> (Expr, Expr) {
    let aux = Expr::const_(Name::from_string("Nat.bitwiseAux"), vec![]);
    // type: (Bool→Bool→Bool) → Nat → Nat → Nat
    let type_ = Expr::pi(
        BinderInfo::Default,
        c.bool_to_bool_to_bool.clone(),
        c.nat_to_nat_to_nat.clone(),
    );
    let mut b = EnvDeclBuilder::new();
    let (f_id, f) = b.fresh_local(c.bool_to_bool_to_bool.clone());
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fuel = c.add(m.clone(), n.clone());
    let body = Expr::apps(aux, [f.clone(), fuel, m.clone(), n.clone()]);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
    let val = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), val);
    let val = b.mk_lam(
        f_id,
        BinderInfo::Default,
        c.bool_to_bool_to_bool.clone(),
        val,
    );
    (type_, b.finish(val))
}

/// `Nat.<op> : Nat → Nat → Nat` as `fun m n => Nat.bitwise <boolop> m n`, the
/// reducible Definition that replaces the admitted `Nat.<op>` axiom.
fn build_bitwise_instance(c: &BW, boolop: &str) -> (Expr, Expr) {
    let bitwise = Expr::const_(Name::from_string("Nat.bitwise"), vec![]);
    let op = Expr::const_(Name::from_string(boolop), vec![]);
    let type_ = c.nat_to_nat_to_nat.clone();
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let body = Expr::apps(bitwise, [op, m.clone(), n.clone()]);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
    let val = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), val);
    (type_, b.finish(val))
}

impl Environment {
    /// Register `Nat.ofBool`, `Nat.bitwiseAux`, `Nat.bitwise`, and redefine
    /// `Nat.land`/`Nat.lor`/`Nat.xor` as `Nat.bitwise and/or/xor`, discharging
    /// the three admitted bitwise domain axioms.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` (Nat, add, rec), `self.init_bool()`
    ///           (Bool, and, or, xor, Bool.rec), and
    ///           `self.register_nat_testbit_def()` (Nat.testBit, Nat.div2).
    /// ENSURES: `Nat.ofBool` / `Nat.bitwiseAux` / `Nat.bitwise` are reducible
    ///          Definitions, and `Nat.land`/`Nat.lor`/`Nat.xor` are reducible
    ///          `Declaration::Definition`s (NOT Axioms).
    /// ENSURES: Idempotent — re-invocation is a no-op once `Nat.bitwise` and the
    ///          three ops are Definitions.
    pub(crate) fn register_nat_bitwise_def(&mut self) -> Result<(), EnvError> {
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
        self.init_bool()?;
        self.register_nat_div2_lt_self_proof()?; // Nat.div2
        self.register_nat_testbit_def()?; // Nat.testBit

        let c = BW::new();

        if self.get_const(&Name::from_string("Nat.ofBool")).is_none() {
            let (type_, value) = build_of_bool(&c);
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Nat.ofBool"),
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            })?;
        }

        if self
            .get_const(&Name::from_string("Nat.bitwiseAux"))
            .is_none()
        {
            let (type_, value) = build_bitwise_aux(&c);
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Nat.bitwiseAux"),
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            })?;
        }

        if self.get_const(&Name::from_string("Nat.bitwise")).is_none() {
            let (type_, value) = build_bitwise(&c);
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Nat.bitwise"),
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            })?;
        }

        // Redefine the three bitwise ops, discharging the admitted axioms.
        // SOUNDNESS: `discharge_axiom_for_redefinition` only removes a bare
        // Axiom; the immediately-following `add_decl` installs a Definition of
        // the SAME type `Nat → Nat → Nat`. Every term previously type-checked
        // against the axiom stays well-typed; the constant merely gains a
        // reduction rule. The native reducer (ground fast path) is unchanged and
        // computes the same bitwise value (pinned by the module tests).
        for (op_name, bool_op) in [
            ("Nat.land", "Bool.and"),
            ("Nat.lor", "Bool.or"),
            ("Nat.xor", "Bool.xor"),
        ] {
            let name = Name::from_string(op_name);
            let already_def = self
                .get_const(&name)
                .is_some_and(|info| matches!(info.kind, super::types::ConstantKind::Definition));
            if !already_def {
                self.discharge_axiom_for_redefinition(&name);
                let (type_, value) = build_bitwise_instance(&c, bool_op);
                self.add_decl(Declaration::Definition {
                    name: name.clone(),
                    level_params: vec![],
                    type_,
                    value,
                    is_reducible: false,
                })?;
            }
            // Kept as a NON-reducible (`Regular`) Definition via `is_reducible:
            // false` above — NOT `Irreducible`. `Irreducible` blocks the
            // kernel-transparency reductions that the downstream `Int.land_comm`
            // nested-`cases` motive construction needs (regressing those proofs);
            // `Regular` keeps `cases` working AND keeps the constant out of the
            // elaborator's eager reducible-transparency unfolding. The `apply`-time
            // head preservation that `nat_land_comm`'s `rw [Nat.testBit_and]`
            // relies on is handled in the unifier (`head_is_protected_def` + the
            // App-arg meta guard), which fires for a non-`Reducible` def head only
            // when it is being assigned to a bare metavariable. Ground
            // `Nat.land 6 3 = 2 := rfl` holds via the native reducer; the corollary
            // `testBit_and` type-checks via the kernel's full-transparency def-eq.
        }

        Ok(())
    }

    /// Register the real `Nat.shiftRight : Nat → Nat → Nat` Definition
    /// `fun m n => Nat.iterDiv2 n m`, discharging the admitted `Nat.shiftRight`
    /// domain axiom.
    ///
    /// `Nat.iterDiv2 i x` iterates `Nat.div2` `i` times on `x` (= `x / 2^i`), so
    /// `shiftRight m n = Nat.iterDiv2 n m = m / 2^n = m >> n` — exactly the
    /// semantics of the native `reduce_nat_shift_right` reducer (`a.shr_big(b)`),
    /// so the delta path and the ground fast path agree.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` and `self.register_nat_testbit_def()`
    ///           (the latter registers `Nat.iterDiv2`).
    /// ENSURES: `Nat.shiftRight` is a `Declaration::Definition` (NOT an Axiom).
    /// ENSURES: Idempotent — re-invocation is a no-op once `Nat.shiftRight` is a
    ///          Definition.
    ///
    /// `pub` so the clean-verify spec build (which constructs its env from a bare
    /// `Environment::new()`, not `with_prelude`) can discharge the `Nat.shiftRight`
    /// EnvInjected axiom out of its self-verification census.
    pub fn register_nat_shiftright_def(&mut self) -> Result<(), EnvError> {
        self.init_nat()?;
        self.register_nat_div2_lt_self_proof()?; // Nat.div2 (transitive dep of iterDiv2)
        self.register_nat_testbit_def()?; // Nat.iterDiv2

        let name = Name::from_string("Nat.shiftRight");
        let already_def = self
            .get_const(&name)
            .is_some_and(|info| matches!(info.kind, super::types::ConstantKind::Definition));
        if already_def {
            return Ok(());
        }

        let c = BW::new();
        let iter_div2 = Expr::const_(Name::from_string("Nat.iterDiv2"), vec![]);
        // Nat.shiftRight := fun m n => Nat.iterDiv2 n m
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let body = Expr::apps(iter_div2, [n.clone(), m.clone()]);
            let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            let val = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), val);
            b.finish(val)
        };

        // SOUNDNESS: `discharge_axiom_for_redefinition` only removes a bare Axiom;
        // the immediately-following `add_decl` installs a Definition of the SAME
        // type `Nat → Nat → Nat`. Every term previously type-checked against the
        // axiom stays well-typed; the constant merely gains a reduction rule that
        // agrees with the native ground reducer.
        self.discharge_axiom_for_redefinition(&name);
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: c.nat_to_nat_to_nat.clone(),
            value,
            is_reducible: false,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    fn env_with_bitwise() -> Environment {
        let mut env = Environment::new();
        env.register_nat_bitwise_def()
            .expect("bitwise registration");
        env
    }

    fn nat_lit(n: u64) -> Expr {
        Expr::nat_lit(n)
    }

    #[test]
    fn test_bitwise_defs_are_definitions() {
        let env = env_with_bitwise();
        for name in [
            "Nat.ofBool",
            "Nat.bitwiseAux",
            "Nat.bitwise",
            "Nat.land",
            "Nat.lor",
            "Nat.xor",
        ] {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{name} must be a Definition"
            );
            assert!(info.value.is_some(), "{name} must retain its value");
        }
    }

    #[test]
    fn test_bitwise_idempotent() {
        let mut env = env_with_bitwise();
        env.register_nat_bitwise_def()
            .expect("idempotent re-registration");
    }

    #[test]
    fn test_bitwise_type_checks() {
        let env = env_with_bitwise();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in [
            "Nat.ofBool",
            "Nat.bitwiseAux",
            "Nat.bitwise",
            "Nat.land",
            "Nat.lor",
            "Nat.xor",
        ] {
            let _ = tc
                .infer_type(&Expr::const_(Name::from_string(name), vec![]))
                .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
        }
    }

    #[test]
    fn test_bitwise_axiom_deps_empty() {
        let env = env_with_bitwise();
        for name in [
            "Nat.ofBool",
            "Nat.bitwiseAux",
            "Nat.bitwise",
            "Nat.land",
            "Nat.lor",
            "Nat.xor",
        ] {
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

    /// The redefined `Nat.land`/`lor`/`xor` compute the true bitwise op on
    /// ground inputs. The native reducer fires first (fast path); this confirms
    /// it agrees with the math, and that the constant resolves to the literal.
    #[test]
    fn test_ground_bitwise_matches_reducer() {
        let mut env = env_with_bitwise();
        env.init_eq().expect("init_eq");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );

        // (op, a, b, expected)
        for (op, a, b, expected) in [
            ("Nat.land", 6u64, 3u64, 2u64),
            ("Nat.land", 12, 10, 8),
            ("Nat.land", 0, 5, 0),
            ("Nat.land", 255, 170, 170),
            ("Nat.lor", 6, 3, 7),
            ("Nat.lor", 12, 10, 14),
            ("Nat.lor", 0, 5, 5),
            ("Nat.xor", 6, 3, 5),
            ("Nat.xor", 12, 10, 6),
            ("Nat.xor", 255, 170, 85),
        ] {
            let op_c = Expr::const_(Name::from_string(op), vec![]);
            let lhs = Expr::apps(op_c, [nat_lit(a), nat_lit(b)]);
            let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
            let stated = Expr::apps(eq_const, [nat.clone(), lhs.clone(), nat_lit(expected)]);
            let proof = Expr::apps(eq_refl.clone(), [nat.clone(), lhs]);
            let inferred = tc
                .infer_type(&proof)
                .unwrap_or_else(|e| panic!("{op} {a} {b} refl should infer: {e:?}"));
            assert!(
                tc.is_def_eq(&inferred, &stated),
                "{op} {a} {b} should equal {expected}"
            );
        }
    }

    /// Critical soundness check: with the native reducer SUPPRESSED (the head is
    /// `Nat.bitwise <op>` rather than `Nat.land`, and `Nat.bitwise` has NO native
    /// reducer), the DEFINITION body alone must compute the same bitwise value.
    /// This pins that the def-eq holds via the delta+iota path, independent of
    /// the fast-path reducer — i.e. the Definition is faithful, not a shell whose
    /// only correct behavior comes from the reducer.
    #[test]
    fn test_ground_bitwise_def_unfold() {
        let mut env = env_with_bitwise();
        env.init_eq().expect("init_eq");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );
        let bitwise = Expr::const_(Name::from_string("Nat.bitwise"), vec![]);

        for (bool_op, a, b, expected) in [
            ("Bool.and", 6u64, 3u64, 2u64),
            ("Bool.and", 12, 10, 8),
            ("Bool.or", 6, 3, 7),
            ("Bool.or", 5, 2, 7),
            ("Bool.xor", 6, 3, 5),
            ("Bool.xor", 13, 6, 11),
        ] {
            let op = Expr::const_(Name::from_string(bool_op), vec![]);
            let lhs = Expr::apps(bitwise.clone(), [op, nat_lit(a), nat_lit(b)]);
            let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
            let stated = Expr::apps(eq_const, [nat.clone(), lhs.clone(), nat_lit(expected)]);
            let proof = Expr::apps(eq_refl.clone(), [nat.clone(), lhs]);
            let inferred = tc
                .infer_type(&proof)
                .unwrap_or_else(|e| panic!("bitwise {bool_op} {a} {b} refl should infer: {e:?}"));
            assert!(
                tc.is_def_eq(&inferred, &stated),
                "bitwise {bool_op} {a} {b} (def-unfold path) should equal {expected}"
            );
        }
    }

    fn env_with_shiftright() -> Environment {
        let mut env = Environment::new();
        env.register_nat_shiftright_def()
            .expect("shiftRight registration");
        env
    }

    #[test]
    fn test_shiftright_is_definition_not_axiom() {
        let env = env_with_shiftright();
        let info = env
            .get_const(&Name::from_string("Nat.shiftRight"))
            .expect("Nat.shiftRight should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "Nat.shiftRight must be a Definition"
        );
        assert!(info.value.is_some(), "Nat.shiftRight must retain its value");
    }

    #[test]
    fn test_shiftright_idempotent() {
        let mut env = env_with_shiftright();
        env.register_nat_shiftright_def()
            .expect("idempotent re-registration");
    }

    #[test]
    fn test_shiftright_axiom_deps_empty() {
        let env = env_with_shiftright();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.shiftRight"))
            .expect("Nat.shiftRight registered; axiom_deps should be Some");
        let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            names.is_empty(),
            "Nat.shiftRight must have empty axiom closure, got {names:?}"
        );
    }

    /// Critical soundness check: with the native reducer SUPPRESSED (the head is
    /// `Nat.iterDiv2` rather than `Nat.shiftRight`, and `Nat.iterDiv2` has NO
    /// native reducer), the DEFINITION body alone must compute the same shift
    /// value. Pinned both through the `Nat.shiftRight` head (fast path) and the
    /// `Nat.iterDiv2 n m` body (delta+iota path), so the Definition is faithful.
    #[test]
    fn test_ground_shiftright_matches_reducer_and_body() {
        let mut env = env_with_shiftright();
        env.init_eq().expect("init_eq");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );
        let shr = Expr::const_(Name::from_string("Nat.shiftRight"), vec![]);
        let iter_div2 = Expr::const_(Name::from_string("Nat.iterDiv2"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        // (m, n, expected = m >> n = m / 2^n)
        for (m, n, expected) in [
            (13u64, 2u64, 3u64),
            (13, 0, 13),
            (1, 1, 0),
            (255, 4, 15),
            (1024, 10, 1),
            (6, 1, 3),
            (0, 5, 0),
        ] {
            // Fast path: head `Nat.shiftRight m n`.
            let lhs_fast = Expr::apps(shr.clone(), [nat_lit(m), nat_lit(n)]);
            let stated_fast = Expr::apps(
                eq_const.clone(),
                [nat.clone(), lhs_fast.clone(), nat_lit(expected)],
            );
            let proof_fast = Expr::apps(eq_refl.clone(), [nat.clone(), lhs_fast]);
            let inferred_fast = tc
                .infer_type(&proof_fast)
                .unwrap_or_else(|e| panic!("shiftRight {m} {n} refl should infer: {e:?}"));
            assert!(
                tc.is_def_eq(&inferred_fast, &stated_fast),
                "Nat.shiftRight {m} {n} should equal {expected}"
            );

            // Delta path: body `Nat.iterDiv2 n m` (no native reducer for iterDiv2).
            let lhs_body = Expr::apps(iter_div2.clone(), [nat_lit(n), nat_lit(m)]);
            let stated_body = Expr::apps(
                eq_const.clone(),
                [nat.clone(), lhs_body.clone(), nat_lit(expected)],
            );
            let proof_body = Expr::apps(eq_refl.clone(), [nat.clone(), lhs_body]);
            let inferred_body = tc
                .infer_type(&proof_body)
                .unwrap_or_else(|e| panic!("iterDiv2 {n} {m} refl should infer: {e:?}"));
            assert!(
                tc.is_def_eq(&inferred_body, &stated_body),
                "iterDiv2 {n} {m} (def-unfold path) should equal {expected}"
            );
        }
    }
}
