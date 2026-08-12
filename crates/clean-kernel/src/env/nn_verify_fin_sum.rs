// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level registration of `Fin.sum` and associated lemmas.
//!
//! Registers the foundational summation operation needed to state and prove
//! NN verification theorems (T01: interval_hull_sound, T80: IBP linear
//! soundness, T02: linear_transform_exact) in the kernel:
//!
//! - `Fin.sum (n : Nat) (f : Fin n -> Rat) : Rat`
//! - `Fin.sum_zero : Fin.sum 0 f = Rat.zero`
//! - `Fin.sum_succ : Fin.sum (n+1) f = Rat.add (Fin.sum n (f . Fin.castSucc)) (f <n, ...>)`
//! - `Fin.sum_le : (forall i, LE.le (f i) (g i)) -> LE.le (Fin.sum n f) (Fin.sum n g)`
//! - `Fin.sum_add : Fin.sum n (fun i => Rat.add (f i) (g i)) = Rat.add (Fin.sum n f) (Fin.sum n g)`
//! - `Fin.sum_nonneg : (forall i, LE.le Rat.zero (f i)) -> LE.le Rat.zero (Fin.sum n f)`
//! - `Fin.sum_smul : Fin.sum n (fun i => Rat.mul c (f i)) = Rat.mul c (Fin.sum n f)`
//! - `Fin.sum_sub : Fin.sum n (fun i => Rat.sub (f i) (g i)) = Rat.sub (Fin.sum n f) (Fin.sum n g)`
//! - `Fin.sum_zero_fn : Fin.sum n (fun _ => Rat.zero) = Rat.zero`
//! - `Fin.sum_single : forall (n : Nat) (i : Fin n) (x : Rat),
//!       Nat.lt (Fin.val i) n ->
//!       Eq @Rat (Fin.sum n (fun j => ite (j = i) x Rat.zero)) x`
//!       (the `i.val < n` in-range premise is load-bearing: it excludes the
//!       `Fin.mk _ _ True` junk witnesses — `n = 0` / `val >= n` — under which
//!       the empty/all-zero sum would falsely equal an arbitrary `x`.)
//!
//! Part of #3219.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for Fin.sum registration.
pub(super) struct FinSumConsts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) fin: Expr,
    pub(super) rat_zero: Expr,
    pub(super) rat_add: Expr,
    pub(super) rat_sub: Expr,
    pub(super) rat_mul: Expr,
    pub(super) fin_sum: Expr,
    pub(super) le_le: Expr,
    pub(super) inst_le_rat: Expr,
    pub(super) eq: Expr,
    /// `@ite : {α : Sort u} → (c : Prop) → [Decidable c] → α → α → α`
    pub(super) ite: Expr,
    /// `instDecidableEqFin : {n : Nat} → (a b : Fin n) → Decidable (a = b)`
    pub(super) inst_dec_eq_fin: Expr,
    /// `@Eq (Fin n)` at universe 1
    pub(super) eq_fin: Expr,
}

impl FinSumConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            ite: Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
            inst_dec_eq_fin: Expr::const_(Name::from_string("instDecidableEqFin"), vec![]),
            eq_fin: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        }
    }

    /// Build `Eq @Rat lhs rhs`.
    pub(super) fn rat_eq(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.eq.clone(), self.rat.clone()), lhs),
            rhs,
        )
    }

    /// Build `LE.le @Rat instLERat lhs rhs`.
    pub(super) fn rat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.le_le.clone(), self.rat.clone()),
                    self.inst_le_rat.clone(),
                ),
                lhs,
            ),
            rhs,
        )
    }

    /// Build `Fin n -> Rat` (the type of a summand function).
    pub(super) fn fin_to_rat(&self, n: Expr) -> Expr {
        let fin_n = Expr::app(self.fin.clone(), n);
        Expr::pi(BinderInfo::Default, fin_n, self.rat.clone())
    }
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
impl Environment {
    /// Initialize `Fin.sum` and associated linearity/monotonicity lemmas.
    ///
    /// Depends on: `init_rat()`, `init_rat_arith()`, `init_rat_field_inst()`,
    /// `init_fin()`, `init_rat_ord()`, `init_eq()`.
    pub(crate) fn init_fin_sum(&mut self) -> Result<(), EnvError> {
        if self.fin_sum_init {
            return Ok(());
        }
        self.init_rat()?;
        self.init_rat_arith()?;
        // `Fin.sum_zero_fn` is now a theorem whose step case closes via
        // `Rat.add_zero`, so the Rat field theorem layer must be present
        // before we register the Fin.sum theorem family.
        self.init_rat_field_inst()?;
        self.init_fin()?;
        self.init_rat_ord()?;
        self.init_eq()?;

        let c = FinSumConsts::new();
        self.ensure_fin_cast_succ(&c)?; // (#3546) before Fin.sum
        self.ensure_fin_last(&c)?; // (#3546) before Fin.sum
        self.register_fin_sum(&c)?;
        self.register_fin_sum_zero(&c)?;
        self.register_fin_sum_succ(&c)?;
        self.register_fin_sum_le_theorem()?;
        self.register_fin_sum_add_theorem()?;
        self.register_fin_sum_zero_fn(&c)?;
        self.register_fin_sum_nonneg_theorem(&c)?;
        self.register_fin_sum_smul_theorem()?;
        self.register_fin_sum_sub_theorem()?;
        // `Fin.sum_single` (the last TCB `Fin` axiom): register the kernel-checked
        // constructive Theorem (`nn_verify_fin_sum_single_proof.rs`), which
        // overwrites the legacy admitted Axiom so the Theorem wins. The Axiom path
        // is retained only as a fallback if the proof ever fails to register.
        match self.register_fin_sum_single_theorem(&c) {
            Ok(()) => {}
            Err(_) => self.register_fin_sum_single(&c)?,
        }

        self.fin_sum_init = true;
        Ok(())
    }

    /// `Fin.sum (n : Nat) (f : Fin n -> Rat) : Rat` — **faithful Nat.rec carrier**.
    ///
    /// Registered as a reducible `Declaration::Definition` with the standard
    /// Lean 4 recursive shape:
    ///
    /// ```text
    /// Fin.sum := fun (n : Nat) (f : Fin n -> Rat) =>
    ///   @Nat.rec.{1}
    ///     (fun k : Nat => (Fin k -> Rat) -> Rat)                     -- Π-motive
    ///     (fun _f => Rat.zero)                                         -- zero case
    ///     (fun (k : Nat) (ih : (Fin k -> Rat) -> Rat)
    ///          (f' : Fin (Nat.succ k) -> Rat) =>
    ///        Rat.add (ih (fun i : Fin k => f' (Fin.castSucc k i)))
    ///                 (f' (Fin.last k)))                                -- succ case
    ///     n
    ///     f
    /// ```
    ///
    /// # Discriminator properties
    ///
    /// 1. **Base case (n = 0):** `Fin.sum 0 f` iota-reduces to `Rat.zero`, so
    ///    `Fin.sum_zero : Fin.sum 0 f = Rat.zero` closes by `@Eq.refl.{1} Rat Rat.zero`
    ///    on a **real** ι-step, not a placeholder collapse.
    /// 2. **Step case (n = k+1):** `Fin.sum (k+1) f` iota-reduces to
    ///    `Rat.add (Fin.sum k (fun i => f (Fin.castSucc k i))) (f (Fin.last k))`.
    ///    The carrier's defining equation IS `Fin.sum_succ`, so that lemma
    ///    closes by `@Eq.refl` after ι on Nat.rec.
    /// 3. **Not constant in `f`:** `Fin.sum 1 (fun _ => x) = x`, so the carrier
    ///    depends genuinely on `f` — unlike the old `fun _ _ => Rat.zero`
    ///    placeholder which was rejected as MASQUERADE (#3546).
    ///
    /// # Universe
    ///
    /// `Nat.rec.{1}` because the motive returns `(Fin k -> Rat) -> Rat : Type 0 = Sort 1`.
    ///
    /// # Prerequisites (registered before this call by `init_fin_sum`)
    ///
    /// - `Nat.rec` — foundational, `data_types_nat.rs`.
    /// - `Fin.castSucc`, `Fin.last` — via `ensure_fin_cast_succ`/`ensure_fin_last`,
    ///   whitelisted in `FOUNDATIONAL_AXIOMS` (`axiom_audit.rs:146-147`).
    /// - `Rat.add`, `Rat.zero` — Rat field foundation.
    ///
    /// # References
    ///
    /// - Design: `designs/2026-04-20-fin-sum-faithful-carrier.md` Phase 1.
    /// - Demasquerade pattern: `designs/2026-04-19-demasquerade-cxxx-pattern.md`.
    /// - Prior art (non-Π motive): `register_monolithic_crown_faithful` in
    ///   `nn_verify_blockwise_crown_ext_carriers.rs:186`.
    /// - Whnf spike: `crates/clean-kernel/src/tc/tests2/iota_pi_motive_fin_sum.rs`.
    /// - Part of #3546.
    fn register_fin_sum(&mut self, c: &FinSumConsts) -> Result<(), EnvError> {
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let fin_cast_succ = Expr::const_(Name::from_string("Fin.castSucc"), vec![]);
        let fin_last = Expr::const_(Name::from_string("Fin.last"), vec![]);
        let nat_rec = Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        );

        // Type: (n : Nat) -> (Fin n -> Rat) -> Rat
        let fin_sum_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let f_type = c.fin_to_rat(n);
            let (f_id, _f) = b.fresh_local(f_type.clone());
            let r = b.mk_pi(f_id, BinderInfo::Default, f_type, c.rat.clone());
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // Value: fun (n : Nat) (f : Fin n -> Rat) => Nat.rec.{1} motive zero_case succ_case n f
        let fin_sum_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let f_type = c.fin_to_rat(n.clone());
            let (f_id, f_outer) = b.fresh_local(f_type.clone());

            // Motive: fun (k : Nat) => (Fin k -> Rat) -> Rat
            let motive = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (k_id, k) = ch.fresh_local(c.nat.clone());
                let fk_to_rat = c.fin_to_rat(k.clone());
                // Body: (Fin k -> Rat) -> Rat
                let body = Expr::pi(BinderInfo::Default, fk_to_rat, c.rat.clone());
                let r = ch.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body);
                ch.finish_child(r)
            };

            // Zero case: fun (_f : Fin 0 -> Rat) => Rat.zero
            let zero_case = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
                let f0_type = c.fin_to_rat(nat_zero);
                let (f0_id, _f0) = ch.fresh_local(f0_type.clone());
                let r = ch.mk_lam(f0_id, BinderInfo::Default, f0_type, c.rat_zero.clone());
                ch.finish_child(r)
            };

            // Succ case: fun (k : Nat) (ih : (Fin k -> Rat) -> Rat) (f' : Fin (k+1) -> Rat) =>
            //              Rat.add (ih (fun i : Fin k => f' (Fin.castSucc k i)))
            //                       (f' (Fin.last k))
            let succ_case = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (k_id, k) = ch.fresh_local(c.nat.clone());
                let ih_type = Expr::pi(BinderInfo::Default, c.fin_to_rat(k.clone()), c.rat.clone());
                let (ih_id, ih) = ch.fresh_local(ih_type.clone());
                let succ_k = Expr::app(nat_succ.clone(), k.clone());
                let f_type_succ = c.fin_to_rat(succ_k);
                let (fp_id, fp) = ch.fresh_local(f_type_succ.clone());

                // Build composed function: fun (i : Fin k) => f' (Fin.castSucc k i)
                let composed = {
                    let mut ch2 = EnvDeclBuilder::child_of(&ch);
                    let fin_k = Expr::app(c.fin.clone(), k.clone());
                    let (i_id, i) = ch2.fresh_local(fin_k.clone());
                    // Fin.castSucc takes implicit n; when applied directly, the n is provided
                    // positionally (since all args emitted post-register are positional).
                    let cast_i = Expr::app(Expr::app(fin_cast_succ.clone(), k.clone()), i);
                    let body = Expr::app(fp.clone(), cast_i);
                    let r = ch2.mk_lam(i_id, BinderInfo::Default, fin_k, body);
                    ch2.finish_child(r)
                };

                // ih applied to composed
                let ih_app = Expr::app(ih, composed);

                // f' (Fin.last k)
                let last_k = Expr::app(fin_last.clone(), k.clone());
                let f_last = Expr::app(fp, last_k);

                // Rat.add (ih composed) (f' (Fin.last k))
                let sum = Expr::app(Expr::app(c.rat_add.clone(), ih_app), f_last);

                let r = ch.mk_lam(fp_id, BinderInfo::Default, f_type_succ, sum);
                let r = ch.mk_lam(ih_id, BinderInfo::Default, ih_type, r);
                let r = ch.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), r);
                ch.finish_child(r)
            };

            // Build @Nat.rec.{1} motive zero_case succ_case n f
            let rec_app = Expr::app(
                Expr::app(
                    Expr::app(Expr::app(Expr::app(nat_rec, motive), zero_case), succ_case),
                    n.clone(),
                ),
                f_outer,
            );

            let r = b.mk_lam(f_id, BinderInfo::Default, f_type, rec_app);
            let r = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Fin.sum"),
            level_params: vec![],
            type_: fin_sum_type,
            value: fin_sum_value,
            is_reducible: true,
        })
    }

    /// `Fin.sum_zero : forall (f : Fin 0 -> Rat), Eq @Rat (Fin.sum 0 f) Rat.zero`
    ///
    /// **Constructive proof** (on the faithful `Fin.sum` carrier, #3546):
    ///
    /// ```text
    /// Fin.sum_zero := fun (f : Fin 0 -> Rat) => @Eq.refl.{1} Rat Rat.zero
    /// ```
    ///
    /// The `Eq.refl` type-checks because `Fin.sum 0 f` iota-reduces via the
    /// Nat.rec zero-case branch to `Rat.zero` — the carrier's `zero_case`
    /// body is `fun _ => Rat.zero`, and the extras-forwarding beta on `f`
    /// vanishes since `f` is not used. This is a genuine ι+β step, not a
    /// placeholder collapse.
    ///
    /// Under the old `fun _ _ => Rat.zero` placeholder carrier this proof
    /// WOULD also have type-checked but would have been a MASQUERADE under
    /// the demasquerade rules (M1: alias-collapse via placeholder). The
    /// faithful carrier (Phase 1, this commit) makes the refl genuine.
    ///
    /// Part of #3546 Phase 2.
    fn register_fin_sum_zero(&mut self, c: &FinSumConsts) -> Result<(), EnvError> {
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );

        let sum_zero_type = {
            let mut b = EnvDeclBuilder::new();
            let f_type = c.fin_to_rat(nat_zero.clone());
            let (f_id, f) = b.fresh_local(f_type.clone());
            let lhs = Expr::app(Expr::app(c.fin_sum.clone(), nat_zero.clone()), f);
            let body = c.rat_eq(lhs, c.rat_zero.clone());
            let r = b.mk_pi(f_id, BinderInfo::Default, f_type, body);
            b.finish(r)
        };

        // Proof: fun (f : Fin 0 -> Rat) => @Eq.refl.{1} Rat Rat.zero
        let sum_zero_value = {
            let mut b = EnvDeclBuilder::new();
            let f_type = c.fin_to_rat(nat_zero.clone());
            let (f_id, _f) = b.fresh_local(f_type.clone());
            let body = Expr::app(Expr::app(eq_refl, c.rat.clone()), c.rat_zero.clone());
            let r = b.mk_lam(f_id, BinderInfo::Default, f_type, body);
            b.finish(r)
        };

        // MASQUERADE-ALLOW: faithful `Fin.sum` carrier (Phase 1 of this commit)
        // iota-reduces `Fin.sum 0 f` to `Rat.zero`. The Eq.refl is on the
        // right-hand side `Rat.zero`; the kernel closes the goal
        // `Eq (Fin.sum 0 f) Rat.zero` by reducing LHS to RHS via Nat.rec ι.
        // This is a real reduction step, not a placeholder collapse.
        // See `designs/2026-04-20-fin-sum-faithful-carrier.md` Phase 2.
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Fin.sum_zero"),
            level_params: vec![],
            type_: sum_zero_type,
            value: sum_zero_value,
        })
    }

    /// `Fin.sum_succ : forall (n : Nat) (f : Fin (Nat.succ n) -> Rat),
    ///     Eq @Rat (Fin.sum (Nat.succ n) f)
    ///              (Rat.add (Fin.sum n (fun i => f (Fin.castSucc n i))) (f (Fin.last n)))`
    ///
    /// **Constructive proof** (on the faithful `Fin.sum` carrier, #3546):
    ///
    /// ```text
    /// Fin.sum_succ := fun (n : Nat) (f : Fin (Nat.succ n) -> Rat) =>
    ///   @Eq.refl.{1} Rat (Fin.sum (Nat.succ n) f)
    /// ```
    ///
    /// This is the carrier's defining equation for the successor case. The
    /// `Eq.refl` refl's on the LHS `Fin.sum (Nat.succ n) f`; the kernel
    /// closes the goal
    /// `Eq (Fin.sum (Nat.succ n) f) (Rat.add (Fin.sum n (f ∘ castSucc n)) (f (last n)))`
    /// by iota-reducing LHS one step via Nat.rec, which produces the RHS.
    ///
    /// This is a **genuine** step: Nat.rec's ι-rule on `Nat.succ k`
    /// rewrites `@Nat.rec M z s (Nat.succ k) args` to
    /// `s k (@Nat.rec M z s k) args` — and under our step-case body
    /// `fun k ih f' => Rat.add (ih (fun i => f' (castSucc k i))) (f' (last k))`,
    /// that is exactly the RHS after beta.
    ///
    /// Part of #3546 Phase 3.
    fn register_fin_sum_succ(&mut self, c: &FinSumConsts) -> Result<(), EnvError> {
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let fin_cast_succ = Expr::const_(Name::from_string("Fin.castSucc"), vec![]);
        let fin_last = Expr::const_(Name::from_string("Fin.last"), vec![]);
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );

        let sum_succ_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let succ_n = Expr::app(nat_succ.clone(), n.clone());
            let f_type = c.fin_to_rat(succ_n.clone());
            let (f_id, f) = b.fresh_local(f_type.clone());

            // LHS: Fin.sum (Nat.succ n) f
            let lhs = Expr::app(Expr::app(c.fin_sum.clone(), succ_n.clone()), f.clone());

            // Build the composed function: fun i : Fin n => f (Fin.castSucc n i)
            let composed = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let fin_n = Expr::app(c.fin.clone(), n.clone());
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                // Fin.castSucc @n i : Fin (n+1)
                let cast_i = Expr::app(Expr::app(fin_cast_succ.clone(), n.clone()), i);
                let body = Expr::app(f.clone(), cast_i);
                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_n, body);
                ch.finish_child(r)
            };

            // Fin.sum n composed
            let sum_prefix = Expr::app(Expr::app(c.fin_sum.clone(), n.clone()), composed);

            // f (Fin.last n)
            let f_last = Expr::app(f, Expr::app(fin_last.clone(), n.clone()));

            // RHS: Rat.add (Fin.sum n composed) (f (Fin.last n))
            let rhs = Expr::app(Expr::app(c.rat_add.clone(), sum_prefix), f_last);

            let body = c.rat_eq(lhs, rhs);
            let r = b.mk_pi(f_id, BinderInfo::Default, f_type, body);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // Proof: fun (n : Nat) (f : Fin (succ n) -> Rat) =>
        //          @Eq.refl.{1} Rat (Fin.sum (succ n) f)
        // Closes by iota on Nat.rec at `Nat.succ n`: LHS reduces to RHS.
        let sum_succ_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let succ_n = Expr::app(nat_succ.clone(), n.clone());
            let f_type = c.fin_to_rat(succ_n.clone());
            let (f_id, f) = b.fresh_local(f_type.clone());
            let lhs = Expr::app(Expr::app(c.fin_sum.clone(), succ_n), f);
            let refl = Expr::app(Expr::app(eq_refl, c.rat.clone()), lhs);
            let r = b.mk_lam(f_id, BinderInfo::Default, f_type, refl);
            let r = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // MASQUERADE-ALLOW: faithful `Fin.sum` carrier (Phase 1). The `Eq.refl`
        // closes by a real Nat.rec ι-step on `Nat.succ n`, producing the RHS
        // from the step-case body. This is the carrier's defining equation.
        // See `designs/2026-04-20-fin-sum-faithful-carrier.md` Phase 3.
        // Fin.castSucc / Fin.last already registered by init_fin_sum (#3546).
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Fin.sum_succ"),
            level_params: vec![],
            type_: sum_succ_type,
            value: sum_succ_value,
        })
    }

    /// Ensure `Fin.castSucc : {n : Nat} -> Fin n -> Fin (Nat.succ n)` is registered.
    ///
    /// **Computable `Declaration::Definition`** (#3470 axiom elimination): re-embeds
    /// a `Fin n` element into `Fin (Nat.succ n)` keeping the same `val`:
    ///
    /// ```text
    /// Fin.castSucc := fun {n : Nat} (x : Fin n) =>
    ///   @Fin.mk (Nat.succ n) (@Fin.val n x) True
    /// ```
    ///
    /// `Fin.mk : {m : Nat} -> (val : Nat) -> (isLt : Prop) -> Fin m`; the
    /// `isLt` slot is typed `Prop` (a *proposition*, not a `val < m` proof — see
    /// `data.rs:332`), so any inhabitant of `Prop` fits. We use `True : Prop`.
    /// `Fin.val` (a reducible `Fin.rec` carrier, `data.rs:436`) reads the value.
    ///
    /// This keeps the **exact same declared type** as the former axiom and is
    /// definitionally transparent: `Fin.castSucc n i` is an applied constant in
    /// `Fin.sum`'s carrier / `Fin.sum_succ`'s RHS, so the Nat.rec ι-step that
    /// powers `Fin.sum_succ`'s `Eq.refl` is unaffected by this swap.
    pub(super) fn ensure_fin_cast_succ(&mut self, c: &FinSumConsts) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("Fin.castSucc")).is_some() {
            return Ok(());
        }
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let fin_mk = Expr::const_(Name::from_string("Fin.mk"), vec![]);
        let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
        let fin_islt = Expr::const_(Name::from_string("Fin.isLt"), vec![]);
        let nat_le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);

        let cast_succ_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let fin_n = Expr::app(c.fin.clone(), n.clone());
            let succ_n = Expr::app(nat_succ.clone(), n);
            let fin_succ_n = Expr::app(c.fin.clone(), succ_n);
            let (x_id, _x) = b.fresh_local(fin_n.clone());
            let r = b.mk_pi(x_id, BinderInfo::Default, fin_n, fin_succ_n);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };

        // Value: fun {n : Nat} (x : Fin n) =>
        //          @Fin.mk (Nat.succ n) (@Fin.val n x) <proof>
        // where <proof> : Nat.lt (Fin.val x) (Nat.succ n) is the REAL bound
        // built from the faithful `Fin.isLt x : Nat.lt (Fin.val x) n` via
        // `Nat.le.step`:
        //   Nat.lt (val x) n          ≡ Nat.le (succ (val x)) n
        //   @Nat.le.step (succ (val x)) n (isLt x)
        //     : Nat.le (succ (val x)) (succ n) ≡ Nat.lt (val x) (succ n)
        let cast_succ_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let fin_n = Expr::app(c.fin.clone(), n.clone());
            let (x_id, x) = b.fresh_local(fin_n.clone());
            let succ_n = Expr::app(nat_succ.clone(), n.clone());
            // @Fin.val n x : Nat
            let val = Expr::app(Expr::app(fin_val.clone(), n.clone()), x.clone());
            let succ_val = Expr::app(nat_succ.clone(), val.clone());
            // @Fin.isLt n x : Nat.lt (Fin.val x) n  ≡  Nat.le (succ (val x)) n
            let islt_x = Expr::app(Expr::app(fin_islt.clone(), n.clone()), x);
            // @Nat.le.step (succ (val x)) n (isLt x)
            //   : Nat.le (succ (val x)) (succ n) ≡ Nat.lt (val x) (succ n)
            let proof = Expr::app(
                Expr::app(Expr::app(nat_le_step.clone(), succ_val), n.clone()),
                islt_x,
            );
            // @Fin.mk (Nat.succ n) val proof : Fin (Nat.succ n)
            let body = Expr::app(Expr::app(Expr::app(fin_mk.clone(), succ_n), val), proof);
            let r = b.mk_lam(x_id, BinderInfo::Default, fin_n, body);
            let r = b.mk_lam(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Fin.castSucc"),
            level_params: vec![],
            type_: cast_succ_type,
            value: cast_succ_value,
            is_reducible: true,
        })
    }

    /// Ensure `Fin.last : (n : Nat) -> Fin (Nat.succ n)` is registered.
    ///
    /// **Computable `Declaration::Definition`** (#3470 axiom elimination): the
    /// top element of `Fin (Nat.succ n)`, with `val = n`:
    ///
    /// ```text
    /// Fin.last := fun (n : Nat) => @Fin.mk (Nat.succ n) n (@Nat.le.refl (Nat.succ n))
    /// ```
    ///
    /// `Fin.mk : {m : Nat} -> (val : Nat) -> (isLt : Nat.lt val m) -> Fin m`; the
    /// faithful `isLt` slot needs a REAL proof of `Nat.lt n (Nat.succ n)`, which
    /// δ-reduces to `Nat.le (Nat.succ n) (Nat.succ n)` — discharged by
    /// `@Nat.le.refl (Nat.succ n)`. No recursion. Same declared type as the former
    /// axiom; definitionally transparent to `Fin.sum_succ`'s ι-step (`Fin.last n`
    /// stays an applied constant in the carrier / the step-case RHS).
    pub(super) fn ensure_fin_last(&mut self, c: &FinSumConsts) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("Fin.last")).is_some() {
            return Ok(());
        }
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let fin_mk = Expr::const_(Name::from_string("Fin.mk"), vec![]);
        let nat_le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);

        let fin_last_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let succ_n = Expr::app(nat_succ.clone(), n);
            let fin_succ_n = Expr::app(c.fin.clone(), succ_n);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), fin_succ_n);
            b.finish(r)
        };

        // Value: fun (n : Nat) => @Fin.mk (Nat.succ n) n (@Nat.le.refl (Nat.succ n))
        // The faithful bound `Nat.lt n (Nat.succ n) ≡ Nat.le (Nat.succ n)
        // (Nat.succ n)` is exactly `Nat.le.refl (Nat.succ n)`.
        let fin_last_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let succ_n = Expr::app(nat_succ.clone(), n.clone());
            // @Nat.le.refl (Nat.succ n) : Nat.le (succ n) (succ n) ≡ Nat.lt n (succ n)
            let proof = Expr::app(nat_le_refl.clone(), succ_n.clone());
            // @Fin.mk (Nat.succ n) n proof : Fin (Nat.succ n)
            let body = Expr::app(
                Expr::app(Expr::app(fin_mk.clone(), succ_n), n.clone()),
                proof,
            );
            let r = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Fin.last"),
            level_params: vec![],
            type_: fin_last_type,
            value: fin_last_value,
            is_reducible: true,
        })
    }

    /// `Fin.sum_le : forall (n : Nat) (f g : Fin n -> Rat),
    ///     (forall (i : Fin n), LE.le @Rat instLERat (f i) (g i)) ->
    ///     LE.le @Rat instLERat (Fin.sum n f) (Fin.sum n g)`
    #[cfg(test)]
    fn register_fin_sum_le(&mut self, c: &FinSumConsts) -> Result<(), EnvError> {
        let sum_le_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let f_type = c.fin_to_rat(n.clone());
            let (f_id, f) = b.fresh_local(f_type.clone());
            let (g_id, g) = b.fresh_local(f_type.clone());

            // Hypothesis: forall (i : Fin n), LE.le @Rat instLERat (f i) (g i)
            let hyp = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let fin_n = Expr::app(c.fin.clone(), n.clone());
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let f_i = Expr::app(f.clone(), i.clone());
                let g_i = Expr::app(g.clone(), i);
                let body = c.rat_le(f_i, g_i);
                let r = ch.mk_pi(i_id, BinderInfo::Default, fin_n, body);
                ch.finish_child(r)
            };
            let (h_id, _h) = b.fresh_local(hyp.clone());

            // Conclusion: LE.le @Rat instLERat (Fin.sum n f) (Fin.sum n g)
            let sum_f = Expr::app(Expr::app(c.fin_sum.clone(), n.clone()), f);
            let sum_g = Expr::app(Expr::app(c.fin_sum.clone(), n.clone()), g);
            let concl = c.rat_le(sum_f, sum_g);

            let r = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let r = b.mk_pi(g_id, BinderInfo::Default, f_type.clone(), r);
            let r = b.mk_pi(f_id, BinderInfo::Default, f_type, r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Fin.sum_le"),
            level_params: vec![],
            type_: sum_le_type,
        })
    }

    /// `Fin.sum_add : forall (n : Nat) (f g : Fin n -> Rat),
    ///     Eq @Rat (Fin.sum n (fun i => Rat.add (f i) (g i))) (Rat.add (Fin.sum n f) (Fin.sum n g))`
    #[cfg(test)]
    fn register_fin_sum_add(&mut self, c: &FinSumConsts) -> Result<(), EnvError> {
        let sum_add_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let f_type = c.fin_to_rat(n.clone());
            let (f_id, f) = b.fresh_local(f_type.clone());
            let (g_id, g) = b.fresh_local(f_type.clone());

            // Build the pointwise sum: fun i : Fin n => Rat.add (f i) (g i)
            let pointwise_sum = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let fin_n = Expr::app(c.fin.clone(), n.clone());
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let f_i = Expr::app(f.clone(), i.clone());
                let g_i = Expr::app(g.clone(), i);
                let sum_i = Expr::app(Expr::app(c.rat_add.clone(), f_i), g_i);
                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_n, sum_i);
                ch.finish_child(r)
            };

            // LHS: Fin.sum n (fun i => Rat.add (f i) (g i))
            let lhs = Expr::app(Expr::app(c.fin_sum.clone(), n.clone()), pointwise_sum);

            // RHS: Rat.add (Fin.sum n f) (Fin.sum n g)
            let sum_f = Expr::app(Expr::app(c.fin_sum.clone(), n.clone()), f);
            let sum_g = Expr::app(Expr::app(c.fin_sum.clone(), n.clone()), g);
            let rhs = Expr::app(Expr::app(c.rat_add.clone(), sum_f), sum_g);

            let body = c.rat_eq(lhs, rhs);
            let r = b.mk_pi(g_id, BinderInfo::Default, f_type.clone(), body);
            let r = b.mk_pi(f_id, BinderInfo::Default, f_type, r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Fin.sum_add"),
            level_params: vec![],
            type_: sum_add_type,
        })
    }

    /// `Fin.sum_nonneg : forall (n : Nat) (f : Fin n -> Rat),
    ///     (forall (i : Fin n), LE.le @Rat instLERat Rat.zero (f i)) ->
    ///     LE.le @Rat instLERat Rat.zero (Fin.sum n f)`
    ///
    /// If every summand is non-negative, the total sum is non-negative.
    /// This is T06 in the NN verification proof plan.
    #[cfg(test)]
    fn register_fin_sum_nonneg(&mut self, c: &FinSumConsts) -> Result<(), EnvError> {
        let sum_nonneg_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let f_type = c.fin_to_rat(n.clone());
            let (f_id, f) = b.fresh_local(f_type.clone());

            // Hypothesis: forall (i : Fin n), LE.le @Rat instLERat Rat.zero (f i)
            let hyp = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let fin_n = Expr::app(c.fin.clone(), n.clone());
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let f_i = Expr::app(f.clone(), i);
                let body = c.rat_le(c.rat_zero.clone(), f_i);
                let r = ch.mk_pi(i_id, BinderInfo::Default, fin_n, body);
                ch.finish_child(r)
            };
            let (h_id, _h) = b.fresh_local(hyp.clone());

            // Conclusion: LE.le @Rat instLERat Rat.zero (Fin.sum n f)
            let sum_f = Expr::app(Expr::app(c.fin_sum.clone(), n.clone()), f);
            let concl = c.rat_le(c.rat_zero.clone(), sum_f);

            let r = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let r = b.mk_pi(f_id, BinderInfo::Default, f_type, r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Fin.sum_nonneg"),
            level_params: vec![],
            type_: sum_nonneg_type,
        })
    }
}
