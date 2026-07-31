// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Additional `Fin.sum` linearity lemmas: subtraction, constant-zero, and
//! Kronecker-delta (single-index) summation.
//!
//! Split from `nn_verify_fin_sum.rs` to keep files under the 500-line limit.
//!
//! - `Fin.sum_sub : Fin.sum n (fun i => Rat.sub (f i) (g i)) = Rat.sub (Fin.sum n f) (Fin.sum n g)`
//! - `Fin.sum_zero_fn : Fin.sum n (fun _ => Rat.zero) = Rat.zero`
//! - `Fin.sum_single : Nat.lt (Fin.val i) n -> Fin.sum n (fun j => ite (j = i) x 0) = x`
//!   (the `i.val < n` in-range premise is load-bearing — see the soundness note
//!   on `register_fin_sum_single`.)
//!
//! Part of #3219.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::nn_verify_fin_sum::FinSumConsts;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// `Fin.sum_sub : forall (n : Nat) (f g : Fin n -> Rat),
    ///     Eq @Rat (Fin.sum n (fun i => Rat.sub (f i) (g i)))
    ///            (Rat.sub (Fin.sum n f) (Fin.sum n g))`
    ///
    /// Subtraction distributes over finite sums (linearity).
    #[cfg(test)]
    pub(super) fn register_fin_sum_sub(&mut self, c: &FinSumConsts) -> Result<(), EnvError> {
        let sum_sub_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let f_type = c.fin_to_rat(n.clone());
            let (f_id, f) = b.fresh_local(f_type.clone());
            let (g_id, g) = b.fresh_local(f_type.clone());

            // fun i : Fin n => Rat.sub (f i) (g i)
            let pointwise_diff = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let fin_n = Expr::app(c.fin.clone(), n.clone());
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let f_i = Expr::app(f.clone(), i.clone());
                let g_i = Expr::app(g.clone(), i);
                let diff_i = Expr::app(Expr::app(c.rat_sub.clone(), f_i), g_i);
                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_n, diff_i);
                ch.finish_child(r)
            };

            let lhs = Expr::app(Expr::app(c.fin_sum.clone(), n.clone()), pointwise_diff);

            let sum_f = Expr::app(Expr::app(c.fin_sum.clone(), n.clone()), f);
            let sum_g = Expr::app(Expr::app(c.fin_sum.clone(), n.clone()), g);
            let rhs = Expr::app(Expr::app(c.rat_sub.clone(), sum_f), sum_g);

            let body = c.rat_eq(lhs, rhs);
            let r = b.mk_pi(g_id, BinderInfo::Default, f_type.clone(), body);
            let r = b.mk_pi(f_id, BinderInfo::Default, f_type, r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Fin.sum_sub"),
            level_params: vec![],
            type_: sum_sub_type,
        })
    }

    /// `Fin.sum_zero_fn : forall (n : Nat),
    ///     Eq @Rat (Fin.sum n (fun _ : Fin n => Rat.zero)) Rat.zero`
    ///
    /// **Constructive proof** (on the faithful `Fin.sum` carrier, #3546):
    ///
    /// Genuine `@Nat.rec.{0}` induction over the Prop motive
    /// `fun (k : Nat) => @Eq.{1} Rat (Fin.sum k (fun _ : Fin k => 0)) Rat.zero`.
    ///
    /// - **Base (n = 0):** `@Eq.refl.{1} Rat Rat.zero`. Closes because
    ///   `Fin.sum 0 f` iota-reduces to `Rat.zero` via the zero-case body.
    /// - **Step (n = k+1):** `fun (k : Nat) (ih : Fin.sum k (fun _ => 0) = 0) =>
    ///   @Eq.trans.{1} Rat
    ///     (Rat.add (Fin.sum k (fun _ : Fin k => 0)) Rat.zero)
    ///     (Rat.add Rat.zero Rat.zero)
    ///     Rat.zero
    ///     (@congrArg.{1,1} Rat Rat (Fin.sum k (fun _ => 0)) Rat.zero
    ///                       (fun r : Rat => Rat.add r Rat.zero) ih)
    ///     (Rat.add_zero Rat.zero)`.
    ///   Step goal is
    ///   `Fin.sum (Nat.succ k) (fun _ : Fin (k+1) => 0) = 0`. Iota on the
    ///   `Fin.sum` carrier reduces LHS to
    ///   `Rat.add (Fin.sum k (fun i : Fin k => (fun _ : Fin (k+1) => 0) (Fin.castSucc k i))) ((fun _ : Fin (k+1) => 0) (Fin.last k))`,
    ///   which beta-reduces to
    ///   `Rat.add (Fin.sum k (fun _ : Fin k => 0)) Rat.zero`. The
    ///   `congrArg` rewrites the inner `Fin.sum` via `ih`, and
    ///   `Rat.add_zero Rat.zero` finishes.
    ///
    /// The IH is **genuinely consumed** (M3 inverted): replacing
    /// `congrArg ... ih` with anything trivial would not type-check.
    ///
    /// Axiom profile: only foundational (`Nat.rec`, `Eq.refl`, `Eq.trans`,
    /// `congrArg`, `Rat.add_zero` = Theorem). Zero domain-specific axioms.
    ///
    /// Part of #3546 Phase 4.
    pub(super) fn register_fin_sum_zero_fn(&mut self, c: &FinSumConsts) -> Result<(), EnvError> {
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );
        let eq_trans = Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        );
        let congr_arg = Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        );
        let rat_add_zero = Expr::const_(Name::from_string("Rat.add_zero"), vec![]);
        // Nat.rec at motive-level 0 (Prop): motive returns `Eq : Prop = Sort 0`.
        let nat_rec_prop = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);

        // Helper: build `fun _ : Fin k => Rat.zero` using a child builder
        // of the given parent. Parent's fvars (like `k`) are tolerated.
        fn zero_fn_of(parent: &EnvDeclBuilder, c: &FinSumConsts, k: &Expr) -> Expr {
            let fin_k = Expr::app(c.fin.clone(), k.clone());
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (i_id, _i) = ch.fresh_local(fin_k.clone());
            let r = ch.mk_lam(i_id, BinderInfo::Default, fin_k, c.rat_zero.clone());
            ch.finish_child(r)
        }

        // Type: forall (n : Nat), Fin.sum n (fun _ : Fin n => 0) = Rat.zero.
        let sum_zero_fn_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let zero_fn = zero_fn_of(&b, c, &n);
            let lhs = Expr::app(Expr::app(c.fin_sum.clone(), n.clone()), zero_fn);
            let body = c.rat_eq(lhs, c.rat_zero.clone());
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), body);
            b.finish(r)
        };

        // Motive: fun (k : Nat) => Fin.sum k (fun _ : Fin k => 0) = Rat.zero.
        let motive = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let zero_fn = zero_fn_of(&b, c, &k);
            let lhs = Expr::app(Expr::app(c.fin_sum.clone(), k.clone()), zero_fn);
            let body = c.rat_eq(lhs, c.rat_zero.clone());
            let r = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body);
            b.finish(r)
        };

        // Base: @Eq.refl.{1} Rat Rat.zero.
        // Target: @Eq Rat (Fin.sum 0 (fun _ : Fin 0 => 0)) Rat.zero.
        // Fin.sum 0 f ι-reduces (one Nat.rec-zero step + β on the unused `f`)
        // to Rat.zero, so Eq.refl Rat.zero closes.
        let base_case = Expr::app(
            Expr::app(eq_refl.clone(), c.rat.clone()),
            c.rat_zero.clone(),
        );

        // Step: fun (k : Nat) (ih : Fin.sum k (fun _ => 0) = 0) =>
        //   Eq.trans (congrArg (fun r => Rat.add r 0) ih) (Rat.add_zero 0)
        //
        // Step goal (after Nat.rec ι at Nat.succ k):
        //   @Eq Rat (Fin.sum (Nat.succ k) (fun _ : Fin (k+1) => 0)) Rat.zero.
        // One iota step on Fin.sum's step branch + β reduces LHS to
        //   Rat.add (Fin.sum k (fun _ : Fin k => 0)) Rat.zero,
        // which is the `a` side of our Eq.trans below.
        let step_case = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let zero_fn_k = zero_fn_of(&b, c, &k);
            // sum_k_zero : Rat := Fin.sum k (fun _ : Fin k => 0)
            let sum_k_zero = Expr::app(Expr::app(c.fin_sum.clone(), k.clone()), zero_fn_k);
            // IH type: sum_k_zero = Rat.zero.
            let ih_ty = c.rat_eq(sum_k_zero.clone(), c.rat_zero.clone());
            let (ih_id, ih) = b.fresh_local(ih_ty.clone());

            // Closure g := fun (r : Rat) => Rat.add r Rat.zero.
            let add_r_zero_lam = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (r_id, r_var) = ch.fresh_local(c.rat.clone());
                let body = Expr::app(Expr::app(c.rat_add.clone(), r_var), c.rat_zero.clone());
                let lam = ch.mk_lam(r_id, BinderInfo::Default, c.rat.clone(), body);
                ch.finish_child(lam)
            };

            // congr : @congrArg.{1,1} Rat Rat sum_k_zero Rat.zero g ih.
            // Output type: Rat.add sum_k_zero Rat.zero = Rat.add Rat.zero Rat.zero
            //              (after β on the closure applications).
            let congr = Expr::apps(
                congr_arg.clone(),
                [
                    c.rat.clone(),
                    c.rat.clone(),
                    sum_k_zero.clone(),
                    c.rat_zero.clone(),
                    add_r_zero_lam,
                    ih,
                ],
            );

            // add_zero_app : Rat.add_zero Rat.zero
            //   : Rat.add Rat.zero Rat.zero = Rat.zero.
            let add_zero_app = Expr::app(rat_add_zero.clone(), c.rat_zero.clone());

            // LHS of Eq.trans output: Rat.add sum_k_zero Rat.zero.
            let lhs_trans = Expr::app(Expr::app(c.rat_add.clone(), sum_k_zero), c.rat_zero.clone());
            // Middle: Rat.add Rat.zero Rat.zero.
            let mid_trans = Expr::app(
                Expr::app(c.rat_add.clone(), c.rat_zero.clone()),
                c.rat_zero.clone(),
            );

            // @Eq.trans.{1} Rat lhs_trans mid_trans Rat.zero congr add_zero_app.
            let trans_app = Expr::apps(
                eq_trans.clone(),
                [
                    c.rat.clone(),
                    lhs_trans,
                    mid_trans,
                    c.rat_zero.clone(),
                    congr,
                    add_zero_app,
                ],
            );

            let r = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, trans_app);
            let r = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // Proof: fun (n : Nat) => @Nat.rec.{0} motive base_case step_case n.
        let sum_zero_fn_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let rec_app = Expr::apps(nat_rec_prop, [motive, base_case, step_case, n]);
            let r = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec_app);
            b.finish(r)
        };

        // Silence unused import warnings; `nat_succ` is only referenced
        // indirectly via the Fin.sum carrier's iota pattern. Capture it
        // in a discardable binding to document the dependency.
        let _ = nat_succ;
        let _ = nat_zero;

        // MASQUERADE-ALLOW: genuine Nat.rec.{0} induction over the Prop
        // motive. Base closes by ι on Fin.sum at 0; step consumes IH via
        // congrArg and Rat.add_zero. Zero domain-specific axioms — all
        // references are foundational (Nat.rec, Eq.refl, Eq.trans,
        // congrArg) or previously proven Theorems (Rat.add_zero).
        // See `designs/2026-04-20-fin-sum-faithful-carrier.md` Phase 4.
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Fin.sum_zero_fn"),
            level_params: vec![],
            type_: sum_zero_fn_type,
            value: sum_zero_fn_value,
        })
    }

    /// Ensure `instDecidableEqFin` is registered.
    ///
    /// TCB-shrink: now delegates to the constructive, axiom-free
    /// `register_fin_dec_eq_proof` (`algebra_fin_dec_eq_proof.rs`), which
    /// registers a real `Declaration::Definition` deciding `Eq (Fin n) a b` by
    /// `Nat.decEq (Fin.val a)(Fin.val b)` (`isTrue` lifts via `Fin.eq_of_val_eq`,
    /// `isFalse` refutes via `congrArg Fin.val`). The native reducer
    /// (`reduce_fin_dec_eq`) fast-paths concrete literals; the kernel's iota on
    /// this Definition is the fallback.
    fn ensure_inst_decidable_eq_fin(&mut self, _c: &FinSumConsts) -> Result<(), EnvError> {
        self.register_fin_dec_eq_proof()
    }

    /// `Fin.sum_single : forall (n : Nat) (i : Fin n) (x : Rat),
    ///     Nat.lt (Fin.val i) n ->
    ///     Eq @Rat (Fin.sum n (fun j => @ite Rat (Eq (Fin n) j i)
    ///         (instDecidableEqFin j i) x Rat.zero)) x`
    ///
    /// The sum of a Kronecker-delta function evaluates to the single nonzero
    /// value at the selected index. Depends on `ite` and `instDecidableEqFin`.
    ///
    /// # SOUNDNESS: the `Nat.lt (Fin.val i) n` in-range premise is LOAD-BEARING.
    ///
    /// Clean's `Fin.mk : {n} -> (val : Nat) -> (isLt : Prop) -> Fin n` (see
    /// `data.rs:332`) admits JUNK: the `isLt` slot is a bare `Prop` (e.g. `True`),
    /// NOT a proof of `val < n`. So `Fin n` is inhabited even for `n = 0`
    /// (`Fin.mk 0 v True`), and a `Fin n` index may carry `val >= n`. Without the
    /// premise this axiom is PROVABLY FALSE:
    ///
    /// - `n = 0`: `Fin.sum 0 _` iota-reduces to `Rat.zero` (empty sum), so the
    ///   axiom would assert `Rat.zero = x` for arbitrary `x` (e.g. `x = 1`).
    /// - junk `i` with `Fin.val i >= n`: the index `i` is never enumerated by
    ///   `Fin.sum` (which runs over `Fin.castSucc`/`Fin.last`, all in range), so
    ///   every Kronecker term is `Rat.zero` and the sum is `Rat.zero != x`.
    ///
    /// Adding `Nat.lt (Fin.val i) n` (`i.val < n`) restricts to genuinely
    /// in-range indices, where the index has exactly one enumerated occurrence
    /// (its term is `x`, all others `Rat.zero`, and `Rat.add` collapses the
    /// rest), so the equation is TRUE. The refutation witnesses above are
    /// excluded because their premise `Nat.lt v 0` / `Nat.lt v n` (with `v >= n`)
    /// is UNINHABITED.
    ///
    /// Admitted `Declaration::Axiom` (not a `Theorem`): a constructive `Eq.refl`
    /// proof is blocked because `@ite Rat (Eq (Fin n) j i) (@instDecidableEqFin
    /// n j i) ...` is STUCK — `instDecidableEqFin` is itself a bare
    /// `Declaration::Axiom` (no `isTrue`/`isFalse` constructor body), so the
    /// `Decidable.casesOn` inside `ite` never iota-reduces and the sum cannot
    /// compute to `x`. A full proof would require a computable `Fin` decidable-
    /// equality and induction with case analysis (future work). With the premise
    /// the statement is TRUE-but-admitted (no longer false), and the `Fin`-carrier
    /// prevention gate (`tests_false_axiom_prevention.rs`) pins that it is no
    /// longer refutable under the `Fin.mk _ _ True` junk witnesses.
    pub(super) fn register_fin_sum_single(&mut self, c: &FinSumConsts) -> Result<(), EnvError> {
        self.init_ite()?;
        self.init_decidable_eq()?;
        self.init_lt()?; // Nat.lt for the in-range validity premise
        self.ensure_inst_decidable_eq_fin(c)?;

        let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);

        let sum_single_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let fin_n = Expr::app(c.fin.clone(), n.clone());
            let (i_id, i) = b.fresh_local(fin_n.clone());
            let (x_id, x) = b.fresh_local(c.rat.clone());

            // fun j : Fin n =>
            //   @ite Rat (@Eq (Fin n) j i) (@instDecidableEqFin n j i)
            //     x Rat.zero
            let kronecker = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let fin_n_inner = Expr::app(c.fin.clone(), n.clone());
                let (j_id, j) = ch.fresh_local(fin_n_inner.clone());

                // @Eq (Fin n) j i
                let eq_cond = Expr::app(
                    Expr::app(Expr::app(c.eq_fin.clone(), fin_n_inner.clone()), j.clone()),
                    i.clone(),
                );

                // @instDecidableEqFin n j i
                let dec_inst = Expr::app(
                    Expr::app(Expr::app(c.inst_dec_eq_fin.clone(), n.clone()), j),
                    i.clone(),
                );

                // @ite Rat eq_cond dec_inst x Rat.zero
                let ite_expr = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(Expr::app(c.ite.clone(), c.rat.clone()), eq_cond),
                            dec_inst,
                        ),
                        x.clone(),
                    ),
                    c.rat_zero.clone(),
                );

                let r = ch.mk_lam(j_id, BinderInfo::Default, fin_n_inner, ite_expr);
                ch.finish_child(r)
            };

            let lhs = Expr::app(Expr::app(c.fin_sum.clone(), n.clone()), kronecker);

            let body = c.rat_eq(lhs, x);

            // SOUNDNESS premise: Nat.lt (@Fin.val n i) n  (i.val < n).
            let val_i = Expr::app(Expr::app(fin_val.clone(), n.clone()), i.clone());
            let in_range = Expr::app(Expr::app(nat_lt.clone(), val_i), n.clone());
            let (h_id, _h) = b.fresh_local(in_range.clone());

            let r = b.mk_pi(h_id, BinderInfo::Default, in_range, body);
            let r = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(i_id, BinderInfo::Default, fin_n, r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Fin.sum_single"),
            level_params: vec![],
            type_: sum_single_type,
        })
    }
}
