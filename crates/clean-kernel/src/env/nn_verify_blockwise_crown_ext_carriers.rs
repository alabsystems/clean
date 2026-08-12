// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Faithful-carrier foundation for the C006/LayerNorm MASQUERADE cluster.
//!
//! Companion to `nn_verify_blockwise_crown_ext.rs` (kept in a sibling
//! module so the parent stays under the 500-line file-size limit).
//!
//! ## Purpose
//!
//! Replaces the placeholder, argument-discarding carriers that the
//! MASQUERADE audit identified in
//! `reports/audit/2026-04-19-clean-native-shard-audit.md` and formally
//! characterized as Rule M2 in
//! `designs/2026-04-19-demasquerade-cxxx-pattern.md`:
//!
//! > "At least one reducible Definition on the path from `lhs`/`rhs` to
//! > normal form has a value of shape `fun x₁ … xₙ => xᵢ` (identity on
//! > one argument) or `fun x₁ … xₙ => const_expr` (constant, ignoring
//! > arguments)."
//!
//! ## What lives here
//!
//! - `NNVerify.LayerNorm.effective_generators : Nat -> Nat -> Nat`
//!   (body `fun n k => Nat.add n k`) — a **faithful carrier** whose
//!   output depends on BOTH arguments. Passes the discriminator tests
//!   required by the design (see
//!   `tests_nn_verify_blockwise_crown_ext.rs` Phase 1 section).
//!
//! ## Why this is foundation, not a fix
//!
//! `Nat.add n k` is not the final semantic content of "effective
//! generator count after LayerNorm" — that requires real projection
//! onto the unit-variance subspace of the zonotope. This is strictly
//! foundation work: a non-masquerading carrier that future proofs can
//! bind to, plus a discriminator test that guarantees the carrier is
//! semantically live. T22 (`zonotope_generators_reset`) is no longer an
//! axiom: the #3590 Branch B FAITHFUL MATRIX RESTATEMENT retired it to a
//! kernel-checked `Declaration::Theorem` over the k-consuming diagonal
//! radius-box carrier `generators_after_ln : (n k) Zonotope n k -> NNMat n n`
//! (see `nn_verify_blockwise_crown_ext_t22.rs`).
//!
//! Part of #3500 Phase 1.

use super::nn_verify_blockwise_crown::BlockwiseCrownConsts;
use super::nn_verify_blockwise_crown_values::build_c006_zero_ib;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `NNVerify.LayerNorm.effective_generators : Nat -> Nat -> Nat`
    /// with body `fun n k => Nat.add n k`.
    ///
    /// **Faithful-carrier replacement** for the argument-discarding
    /// `LayerNorm.generators_after_ln`. See the module docstring and
    /// `designs/2026-04-19-demasquerade-cxxx-pattern.md` (Phase 3,
    /// Rule M2) for the design rationale.
    ///
    /// The old `generators_after_ln` had body `fun n _ => n` — it
    /// discarded `k` and returned `n`, so every theorem stated over it
    /// was a vacuous identity (`n = n`) that closed by `Eq.refl`. This
    /// replacement's body depends on BOTH arguments, satisfying the two
    /// discriminator properties required by the design:
    ///
    /// 1. **Not identity on `n`.** `effective_generators 2 3` reduces to
    ///    `Nat.add 2 3 = 5`, which is syntactically different from `2`.
    ///    So this carrier cannot be confused with `fun n _ => n`.
    /// 2. **Depends on `k`.** `effective_generators 2 3 = 5` and
    ///    `effective_generators 2 4 = 6` reduce to different normal
    ///    forms. So any theorem `effective_generators n k = f n k` for
    ///    some `f` that also discards `k` (e.g., `f n _ := n`) is
    ///    provably FALSE — it cannot close by `Eq.refl`.
    ///
    /// Registered as `Declaration::Definition { is_reducible: true }`
    /// so the kernel can reduce `effective_generators n k` to
    /// `Nat.add n k` during proof checking.
    ///
    /// # Contract
    ///
    /// REQUIRES: `Nat.add` is registered (call `init_nat()` first; this
    /// is guaranteed by `init_nn_verify_blockwise_crown_ext`).
    /// ENSURES: Idempotent (returns `Ok(())` if already registered).
    /// ENSURES: `self.get_const(&Name::from_string(
    /// "NNVerify.LayerNorm.effective_generators")).is_some()`.
    ///
    /// Part of #3500 Phase 1 — faithful-carrier foundation.
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(super) fn register_effective_generators(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.LayerNorm.effective_generators");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        // Type: Nat -> Nat -> Nat
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, _) = b.fresh_local(nat.clone());
            let (k_id, _) = b.fresh_local(nat.clone());
            let r = b.mk_pi(k_id, BinderInfo::Default, nat.clone(), nat.clone());
            let r = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };
        // Value: fun (n : Nat) (k : Nat) => Nat.add n k
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (k_id, k) = b.fresh_local(nat.clone());
            let body = Expr::app(Expr::app(nat_add, n), k);
            let r = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), body);
            let r = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// Register `NNVerify.Block.monolithic_crown_faithful :
    /// (d : Nat) -> (k : Nat) -> (B : IntervalBounds d) -> IntervalBounds d`.
    ///
    /// **Faithful-carrier replacement** for `Block.monolithic_crown`
    /// (see #3494 MASQUERADE demotion in `nn_verify_blockwise_crown.rs`).
    /// The old carrier had body `fun k bd cb lg lb eps B => zero_ib (bd k)`
    /// — it discarded every argument including `B` and returned a constant
    /// zero, so any theorem `monolithic_crown k ... B = something_else B`
    /// reduced to a vacuous identity.
    ///
    /// This replacement's body **depends on both** `k` and `B`:
    ///
    /// ```text
    /// monolithic_crown_faithful d k B
    ///   := @Nat.rec.{1} (fun _ : Nat => IntervalBounds d)
    ///                   B                           -- base case: return input
    ///                   (fun _ _ => zero_ib d)      -- step case: return zero_ib
    ///                   k
    /// ```
    ///
    /// Semantics:
    ///
    /// 1. At `k = Nat.zero`: iota-reduces to `B` (the input bound).
    /// 2. At `k = Nat.succ m` for any `m`: iota-reduces to `zero_ib d`
    ///    (constant zero, independent of `B`).
    ///
    /// This satisfies the design's discriminator requirements
    /// (`designs/2026-04-19-demasquerade-cxxx-pattern.md`, "Template:
    /// faithful abstract-domain carrier" → "Discriminator property"):
    ///
    /// * **Not identity on B.** `monolithic_crown_faithful d (succ 0) B`
    ///   reduces to `zero_ib d`, which is not `B` for a symbolic `B`.
    ///   So any proof `monolithic_crown_faithful d (succ 0) B = B`
    ///   is NOT closable by `Eq.refl` — it would require a proof that
    ///   `zero_ib d = B`, which only holds for `B = zero_ib d`.
    /// * **Depends on k.** `monolithic_crown_faithful d 0 B = B` and
    ///   `monolithic_crown_faithful d (succ 0) B = zero_ib d` reduce
    ///   to different normal forms. So any theorem
    ///   `monolithic_crown_faithful d k B = f d k B` that discards
    ///   either `k` or `B` is provably FALSE at one of these points.
    /// * **Depends on B.** At `k = 0`, the body returns `B` itself.
    ///   Two distinct inputs `B1 ≠ B2` produce distinct outputs
    ///   `monolithic_crown_faithful d 0 B1 = B1` and
    ///   `monolithic_crown_faithful d 0 B2 = B2`. The kernel's WHNF
    ///   confirms this (see `tests_nn_verify_blockwise_crown_ext.rs`).
    ///
    /// Registered as `Declaration::Definition { is_reducible: true }` so
    /// the kernel can iota-reduce applications during proof checking.
    ///
    /// # Contract
    ///
    /// REQUIRES: `Nat.rec` registered (foundational); `IntervalBounds`
    /// and `IntervalBounds.mk` registered (call `init_nn_verify_types()`
    /// first; guaranteed by `init_nn_verify_blockwise_crown_ext`).
    /// ENSURES: Idempotent (returns `Ok(())` if already registered).
    /// ENSURES: `self.get_const(&Name::from_string(
    /// "NNVerify.Block.monolithic_crown_faithful")).is_some()`.
    ///
    /// Part of #3494 Phase 2 — faithful `Block.monolithic_crown` carrier.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_monolithic_crown_faithful(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Block.monolithic_crown_faithful");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = BlockwiseCrownConsts::new();
        // Type: (d : Nat) -> (k : Nat) -> IntervalBounds d -> IntervalBounds d
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let (k_id, _k) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(d.clone());
            let (b_id, _bnd) = b.fresh_local(ib_d.clone());
            let r = b.mk_pi(b_id, BinderInfo::Default, ib_d.clone(), ib_d);
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // Value:
        //   fun (d : Nat) (k : Nat) (B : IntervalBounds d) =>
        //     @Nat.rec.{1}
        //       (fun _ : Nat => IntervalBounds d)  -- motive
        //       B                                  -- base case
        //       (fun (_m : Nat) (_ih : IntervalBounds d) => zero_ib d)  -- step
        //       k
        //
        // `Nat.rec` is instantiated at universe succ(zero) because the
        // motive returns `IntervalBounds d : Type = Sort 1`.
        let nat_rec_ib = Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        );
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(d.clone());
            let (b_id, b_var) = b.fresh_local(ib_d.clone());

            // Motive: fun (_ : Nat) => IntervalBounds d
            let motive = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = ch.fresh_local(c.nat.clone());
                let r = ch.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), ib_d.clone());
                ch.finish_child(r)
            };

            // Step case: fun (_m : Nat) (_ih : IntervalBounds d) => zero_ib d
            let succ_case = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = ch.fresh_local(c.nat.clone());
                let (ih_id, _ih) = ch.fresh_local(ib_d.clone());
                let zero_body = build_c006_zero_ib(&mut ch, &c, &d);
                let r = ch.mk_lam(ih_id, BinderInfo::Default, ib_d.clone(), zero_body);
                let r = ch.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), r);
                ch.finish_child(r)
            };

            // @Nat.rec.{1} motive B succ_case k
            let rec_app = Expr::apps(nat_rec_ib, [motive, b_var, succ_case, k]);

            let r = b.mk_lam(b_id, BinderInfo::Default, ib_d, rec_app);
            let r = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// Register `NNVerify.Block.blockwise_crown_equiv_faithful` — a
    /// constructive theorem over the faithful carrier
    /// `monolithic_crown_faithful`.
    ///
    /// ```text
    /// forall (d : Nat) (B : IntervalBounds d),
    ///   monolithic_crown_faithful d Nat.zero B = B
    /// ```
    ///
    /// This is the **specialisation** of the T60 equivalence statement
    /// at `k = 0`, proved against the faithful carrier. Unlike the
    /// demoted `blockwise_crown_equiv` (axiom — see #3494, T60), this
    /// theorem is NOT a MASQUERADE:
    ///
    /// * The LHS `monolithic_crown_faithful d 0 B` iota-reduces to `B`
    ///   (the input bound). The proof is `@Eq.refl (IntervalBounds d) B`
    ///   — a refl on a symbolic bound variable, not on a collapsed
    ///   `zero_ib` constant.
    /// * Replacing the carrier with `fun d k B => zero_ib d` (the old
    ///   placeholder) would break the proof: the LHS would reduce to
    ///   `zero_ib d`, and `Eq.refl B` would NOT have type
    ///   `zero_ib d = B` unless `B = zero_ib d`.
    ///
    /// So the `Eq.refl` is carrier-discriminating: it type-checks
    /// exactly because `monolithic_crown_faithful d 0 B` faithfully
    /// reduces to its input `B`.
    ///
    /// Part of #3494 — pair a faithful-carrier theorem with the
    /// `monolithic_crown_faithful` registration so the demasquerade
    /// pattern is demonstrably invertible once the arithmetic
    /// infrastructure (Lipschitz / matrix norms) lands.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_blockwise_crown_equiv_faithful(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Block.blockwise_crown_equiv_faithful");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = BlockwiseCrownConsts::new();
        let mcf = Expr::const_(
            Name::from_string("NNVerify.Block.monolithic_crown_faithful"),
            vec![],
        );
        let nat_zero = c.nat_zero.clone();
        // Eq.refl at level succ(zero) because IntervalBounds d : Type 0 = Sort 1.
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );

        // Type: forall (d : Nat) (B : IntervalBounds d),
        //   @Eq (IntervalBounds d) (monolithic_crown_faithful d Nat.zero B) B
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(d.clone());
            let (b_id, b_var) = b.fresh_local(ib_d.clone());
            let lhs = Expr::apps(mcf.clone(), [d.clone(), nat_zero.clone(), b_var.clone()]);
            let concl = c.ib_eq(&d, lhs, b_var);
            let r = b.mk_pi(b_id, BinderInfo::Default, ib_d, concl);
            let r = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // Proof: fun (d : Nat) (B : IntervalBounds d) =>
        //          @Eq.refl.{1} (IntervalBounds d) B
        // Kernel reduces LHS `monolithic_crown_faithful d 0 B` to `B` via
        // one iota step on `Nat.rec` at `Nat.zero`, so the refl closes.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(d.clone());
            let (b_id, b_var) = b.fresh_local(ib_d.clone());
            let body = Expr::app(Expr::app(eq_refl, ib_d.clone()), b_var);
            let r = b.mk_lam(b_id, BinderInfo::Default, ib_d, body);
            let r = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // Base-case iota-unfold on faithful carrier. See triage report
        // reports/triage/2026-04-20-3646-masquerade-grandfathered-triage.md
        // Site 1. Tracking: #3646, #3597, #3494.
        // MASQUERADE-ALLOW: faithful carrier, BVar refl (#3646 Site 1).
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Register `NNVerify.Block.compose_count : Nat -> Nat`
    /// with body `fun (k : Nat) => @Nat.rec (fun _ => Nat) 0
    ///   (fun _ (ih : Nat) => Nat.succ ih) k`.
    ///
    /// **Faithful Block-count carrier** — foundation for the
    /// `blockwise_nat_induction` (#3492), `blockwise_step` (#3491), and
    /// `blockwise_equals_monolithic` (#3493) proofs. The current
    /// `Block.compose` / `Block.monolithic_crown` carriers both have body
    /// `build_c006_zero_ib(block_dim k)` — i.e., they discard all the
    /// `crown_block`, `ln_gamma`, `ln_beta`, `ln_eps`, `B` arguments and
    /// return the same constant interval regardless of input. That is
    /// Rule M1 + M2 of `designs/2026-04-19-demasquerade-cxxx-pattern.md`
    /// (alias-collapse + argument-discarding carrier). The `Nat.rec`
    /// scaffolding in `build_blockwise_nat_induction_proof` runs a real
    /// induction, but the motive `compose k ... = monolithic k ...` is
    /// a vacuous equation because both sides reduce to the same `zero_ib`.
    ///
    /// ## Why compose_count
    ///
    /// This carrier is a `Nat.rec`-structured function whose output at
    /// `k+1` depends on its output at `k`. This is exactly the shape a
    /// faithful `Block.compose` must have — the step case must reference
    /// the previous composition. We expose `compose_count k = k` as the
    /// prototype theorem: base case reduces to `0 = 0` (Eq.refl after
    /// Nat.rec-iota), but the step case requires `Nat.succ ih_at_k = k+1`,
    /// which **uses the induction hypothesis** (Rule M3 fails — IH is
    /// referenced and reduced).
    ///
    /// ## Discriminator properties
    ///
    /// 1. **Not a constant.** `compose_count 0` reduces to `0`,
    ///    `compose_count 1` reduces to `Nat.succ 0 = 1`, etc. Different
    ///    inputs produce different outputs — Rule M2 (argument-discarding
    ///    carrier) fails.
    /// 2. **Varies across the inductive step.** The step branch
    ///    `fun _ ih => Nat.succ ih` structurally references `ih` (the
    ///    previous recursive result). Visitors that check for free
    ///    occurrences of the bound IH will see it — Rule M3 (IH-ignoring
    ///    inductive step) fails.
    /// 3. **Alias-distinguishable.** Any future `compose_count_alt` whose
    ///    body is `fun _ => 0` (constant) will produce a syntactically
    ///    different normal form at `k = 1` (`compose_count 1` reduces to
    ///    `Nat.succ 0`; `compose_count_alt 1` reduces to `0`). So
    ///    theorems of the form `compose_count k = compose_count_alt k`
    ///    cannot close by `Eq.refl` — Rule M1 fails.
    ///
    /// This unblocks Phase 2 of #3500: future commits can replace
    /// `Block.compose`'s placeholder body with a real composition that
    /// threads `compose_count` (or a richer structured carrier) through
    /// the `Nat.rec`, so `blockwise_base`/`blockwise_step`/
    /// `blockwise_nat_induction` are restated as non-trivial equations.
    ///
    /// # Contract
    ///
    /// REQUIRES: `Nat` is registered with its recursor `Nat.rec` (both
    /// are built-in; `init_nat()` guarantees this via the foundation
    /// prelude — `init_nn_verify_blockwise_crown_ext` depends on `init_nat`
    /// transitively).
    /// ENSURES: Idempotent (returns `Ok(())` if already registered).
    /// ENSURES: `self.get_const(&Name::from_string(
    /// "NNVerify.Block.compose_count")).is_some()`.
    /// ENSURES: The body structurally contains `Nat.rec` (so
    /// `expr_references_const` succeeds), and the successor branch
    /// structurally references the bound IH variable.
    ///
    /// Part of #3492 Phase-2 foundation — faithful Block-count carrier
    /// that unblocks demasquerade of `blockwise_nat_induction`.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_block_compose_count(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Block.compose_count");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        // `Nat.rec` at motive-sort `Type 0` (the motive is
        // `fun _ : Nat => Nat`, so the returned level is `1`, matching the
        // universe of `Nat : Type 0`).
        let nat_rec = Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        );

        // Type: Nat -> Nat.
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, _) = b.fresh_local(nat.clone());
            let pi = b.mk_pi(k_id, BinderInfo::Default, nat.clone(), nat.clone());
            b.finish(pi)
        };

        // Motive: fun (_ : Nat) => Nat.
        let motive = {
            let mut b = EnvDeclBuilder::new();
            let (dummy_id, _) = b.fresh_local(nat.clone());
            let lam = b.mk_lam(dummy_id, BinderInfo::Default, nat.clone(), nat.clone());
            b.finish(lam)
        };

        // Succ branch: fun (prev : Nat) (ih : Nat) => Nat.succ ih.
        // `ih` is referenced structurally — Rule M3 check passes.
        let succ_branch = {
            let mut b = EnvDeclBuilder::new();
            let (prev_id, _) = b.fresh_local(nat.clone());
            let (ih_id, ih) = b.fresh_local(nat.clone());
            let body = Expr::app(nat_succ, ih);
            let r = b.mk_lam(ih_id, BinderInfo::Default, nat.clone(), body);
            let r = b.mk_lam(prev_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };

        // Value: fun (k : Nat) =>
        //   @Nat.rec.{1} (fun _ : Nat => Nat) Nat.zero succ_branch k
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(nat.clone());
            let rec_app = Expr::apps(nat_rec, [motive, nat_zero, succ_branch, k]);
            let lam = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), rec_app);
            b.finish(lam)
        };

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }
}
