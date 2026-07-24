// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `NNVerify.Block.compose_count_eq_self` — genuine Nat.rec induction
//! proof on the `Block.compose_count` carrier (#3375 C006 helper).
//!
//! Split from `nn_verify_blockwise_crown_ext_carriers.rs` to keep that
//! file under the 500-line size cap. The carrier itself
//! (`NNVerify.Block.compose_count`) continues to live in the carriers
//! module; this file only registers the companion theorem.
//!
//! See `register_compose_count_eq_self` below for proof architecture,
//! axiom profile, and discriminator rationale.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `NNVerify.Block.compose_count_eq_self` — a genuinely
    /// constructive `Nat.rec` theorem over the faithful
    /// `Block.compose_count` carrier (#3375 C006 helper lemma).
    ///
    /// ```text
    /// forall (k : Nat), compose_count k = k
    /// ```
    ///
    /// ## Why this is a non-masquerade genuine proof
    ///
    /// `Block.compose_count` is registered as a reducible Definition
    /// with body `@Nat.rec.{1} (fun _ : Nat => Nat) Nat.zero
    /// (fun _ ih => Nat.succ ih) k` (see `register_block_compose_count`
    /// in the sibling carriers module). Its step branch **structurally
    /// uses its induction hypothesis `ih`** (Rule M3 inverted) — a step
    /// branch of `fun _ ih => ih` or `fun _ _ => 0` would break this
    /// proof:
    ///
    /// * With `fun _ _ => 0`, `compose_count (succ 0)` would iota-reduce
    ///   to `0`, and we'd need `Eq.refl` between `0` and `Nat.succ 0` —
    ///   provably false.
    /// * With `fun _ ih => ih`, the step case target would reduce to
    ///   `compose_count m = Nat.succ m`, which is provably false (at
    ///   `m = 0` it claims `0 = 1`).
    ///
    /// So the proof term genuinely witnesses the `compose_count`
    /// carrier's step branch computing `Nat.succ ih` and NOTHING ELSE.
    ///
    /// ## Proof architecture
    ///
    /// `@Nat.rec.{0}` at Prop-motive (motive
    /// `fun k : Nat => compose_count k = k` returns `Prop = Sort 0`):
    ///
    /// - **Base**: `@Eq.refl.{1} Nat Nat.zero` proves
    ///   `compose_count Nat.zero = Nat.zero`. The LHS iota-reduces to
    ///   `Nat.zero` via one Nat.rec step on zero, and the RHS is
    ///   syntactically `Nat.zero`. So both sides are def-equal and
    ///   `Eq.refl Nat.zero` closes. **Crucially**, this is `Eq.refl`
    ///   on the canonical constructor `Nat.zero`, NOT on a bound
    ///   variable aliased to a collapsed carrier — the refl witnesses
    ///   a real computation (one iota step on `Nat.rec`).
    /// - **Step**: `fun (m : Nat) (ih : compose_count m = m) =>
    ///   @congrArg.{1,1} Nat Nat (compose_count m) m Nat.succ ih`.
    ///   This produces a term of type
    ///   `Nat.succ (compose_count m) = Nat.succ m`. The goal at the
    ///   step case is `compose_count (Nat.succ m) = Nat.succ m`, whose
    ///   LHS iota-reduces via one Nat.rec-succ step to
    ///   `Nat.succ (compose_count m)` (because `compose_count`'s step
    ///   branch is `fun _ ih => Nat.succ ih` and `ih` there is the
    ///   recursive call `compose_count m`). So the `congrArg` output
    ///   types check against the goal. **The IH is genuinely consumed**
    ///   — replacing `congrArg Nat.succ ih` with `h : 0 = 0` would not
    ///   type-check.
    ///
    /// ## Axiom profile
    ///
    /// Proof term references only `Nat.rec` (inductive recursor),
    /// `Eq.refl` (foundational), `congrArg` (foundational, already used
    /// in `mul_nonpos_le_left` / `rat_add_comm` chains), `Nat.zero`,
    /// `Nat.succ` (constructors), and `compose_count` (reducible
    /// Definition). The transitive axiom closure is a subset of
    /// `FOUNDATIONAL_AXIOMS` — ZERO domain-specific axioms.
    ///
    /// ## What this does NOT close
    ///
    /// This is a **helper lemma** for the `Block.compose_count` carrier
    /// — it does NOT close #3492/#3493 (`blockwise_nat_induction` /
    /// `blockwise_equals_monolithic` headline claims), which require a
    /// faithful `Block.compose` body that threads real per-block CROWN
    /// content through its `Nat.rec` scaffolding. It is a genuine
    /// constructive proof that demonstrates the `compose_count` carrier
    /// is semantically live and that a real induction over it is
    /// expressible in the kernel. Future faithful `Block.compose`
    /// demasquerade work can bind to the same proof pattern.
    ///
    /// # Contract
    ///
    /// REQUIRES: `compose_count` registered (call
    /// `register_block_compose_count` first).
    /// REQUIRES: `congrArg`, `Eq.refl`, `Nat.rec`, `Nat.zero`,
    /// `Nat.succ` registered (foundational; guaranteed by `init_eq`
    /// and core Nat setup).
    /// ENSURES: Idempotent (returns `Ok(())` if already registered).
    /// ENSURES: Registered as `Declaration::Theorem` — NOT an axiom
    /// wrapper.
    ///
    /// Part of #3375 — genuine constructive helper lemma for C006
    /// carrier scaffolding. First Nat.rec proof on the C006 track
    /// whose step branch structurally consumes its induction
    /// hypothesis.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_compose_count_eq_self(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Block.compose_count_eq_self");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let compose_count = Expr::const_(Name::from_string("NNVerify.Block.compose_count"), vec![]);
        // Eq at level succ(zero) because Nat : Type = Sort 1.
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );
        // congrArg at universes [1, 1]: Nat : Sort 1 -> Nat : Sort 1.
        let congr_arg = Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        );
        // Nat.rec at motive-level 0 (Prop): the motive returns
        // `@Eq Nat _ _ : Prop = Sort 0`.
        let nat_rec_prop = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);

        // Helper: build `@Eq.{1} Nat lhs rhs`.
        let nat_eq = |lhs: Expr, rhs: Expr| -> Expr {
            Expr::app(
                Expr::app(Expr::app(eq_const.clone(), nat.clone()), lhs),
                rhs,
            )
        };

        // Type: forall (k : Nat), compose_count k = k.
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(nat.clone());
            let cc_k = Expr::app(compose_count.clone(), k.clone());
            let concl = nat_eq(cc_k, k);
            let r = b.mk_pi(k_id, BinderInfo::Default, nat.clone(), concl);
            b.finish(r)
        };

        // Motive: fun (k : Nat) => @Eq.{1} Nat (compose_count k) k.
        let motive = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(nat.clone());
            let cc_k = Expr::app(compose_count.clone(), k.clone());
            let body = nat_eq(cc_k, k);
            let r = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), body);
            b.finish(r)
        };

        // Base case: @Eq.refl.{1} Nat Nat.zero.
        // Target: @Eq Nat (compose_count Nat.zero) Nat.zero.
        // LHS iota-reduces (one Nat.rec step at zero) to `Nat.zero`,
        // so `Eq.refl Nat Nat.zero` type-checks.
        let base_case = Expr::app(Expr::app(eq_refl.clone(), nat.clone()), nat_zero.clone());

        // Step case: fun (m : Nat) (ih : compose_count m = m) =>
        //   @congrArg.{1,1} Nat Nat (compose_count m) m Nat.succ ih.
        //
        // Output term type:
        //   @Eq Nat (Nat.succ (compose_count m)) (Nat.succ m).
        // Step-case goal (from Nat.rec):
        //   @Eq Nat (compose_count (Nat.succ m)) (Nat.succ m).
        // LHS iota-reduces (one Nat.rec-succ step) to
        //   Nat.succ (Nat.rec ... m)  =  Nat.succ (compose_count m),
        // so the output term's type is def-equal to the goal via one
        // iota step on the compose_count step branch.
        let step_case = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat.clone());
            let cc_m = Expr::app(compose_count.clone(), m.clone());
            let ih_ty = nat_eq(cc_m.clone(), m.clone());
            let (ih_id, ih) = b.fresh_local(ih_ty.clone());
            // @congrArg.{1,1} Nat Nat (compose_count m) m Nat.succ ih
            let body = Expr::apps(
                congr_arg.clone(),
                [
                    nat.clone(),
                    nat.clone(),
                    cc_m,
                    m.clone(),
                    nat_succ.clone(),
                    ih,
                ],
            );
            let r = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
            let r = b.mk_lam(m_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };

        // Proof: fun (k : Nat) =>
        //   @Nat.rec.{0} motive base_case step_case k.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(nat.clone());
            let rec_app = Expr::apps(nat_rec_prop, [motive, base_case, step_case, k]);
            let r = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), rec_app);
            b.finish(r)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
