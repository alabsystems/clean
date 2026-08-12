// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Stage 1 foundations of the BoolFn subsystem redesign
//! (`designs/2026-06-08-boolfn-redesign.md`).
//!
//! Registers the representational machinery that makes Boolean Fourier analysis
//! *definable* — a hypercube point type, a bit-decode, a uniform expectation,
//! and the parity character — as genuine reducible `Declaration::Definition`s.
//! This stage adds CHECKED definitions ONLY; it does NOT migrate `BoolFn` or
//! eliminate any axiom, so the trusted base (golden TCB) is UNCHANGED and the
//! soundness certificate stays SOUND. Migration is Stage 2+.
//!
//! Registered (all reducible Definitions):
//!
//! - `Fin.prod (m : Nat) (g : Fin m -> Rat) : Rat` — a `Nat.rec` carrier mirroring
//!   `Fin.sum` (`nn_verify_fin_sum.rs`), with product instead of sum and identity
//!   `Rat.one`. Defining equations:
//!     `Fin.prod 0 g       ≡ Rat.one`
//!     `Fin.prod (k+1) g   ≡ Rat.mul (Fin.prod k (g ∘ Fin.castSucc k)) (g (Fin.last k))`
//! - `BoolAnalysis.HCPoint (n : Nat) : Type := Fin n -> Bool` — a cube point.
//! - `BoolAnalysis.hcDecode (n : Nat) (k : Fin (Nat.pow 2 n)) : HCPoint n :=`
//!     `fun i => Nat.testBit (Fin.val k) (Fin.val i)` — the `k`-th cube point by its bits.
//! - `BoolAnalysis.Expect (n : Nat) (g : HCPoint n -> Rat) : Rat :=`
//!     `Rat.div (Fin.sum (Nat.pow 2 n) (fun k => g (hcDecode n k)))`
//!            `(Rat.mk (Int.ofNat (Nat.pow 2 n)) 1)` — uniform expectation over the cube.
//! - `BoolAnalysis.chi (n : Nat) (S x : HCPoint n) : Rat :=`
//!     `Fin.prod n (fun i => Bool.rec Rat.one (1 - 2·⟦x i⟧) (S i))` — the parity
//!   character `χ_S(x) = Π_{i : S i} (1 - 2·⟦x i⟧)`, value in {-1, +1}.
//!
//! Each foundation carries a GROUND-REDUCTION sanity test (`is_def_eq` on closed
//! numerals — definitional correctness, not merely type-correctness). See the
//! `tests` module below.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for the Stage-1 boolean-analysis foundations.
struct FoundationConsts {
    nat: Expr,
    bool_: Expr,
    rat: Expr,
    fin: Expr,
    /// `Type 0` = `Sort 1` (the universe `HCPoint` lives in).
    type0: Expr,
    rat_one: Expr,
    rat_zero: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    nat_succ: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
}

impl FoundationConsts {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            fin_cast_succ: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
        }
    }

    /// `Fin n` for a concrete `n` expression.
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }

    /// `Fin n -> Rat` (the type of a `Fin.prod` factor function).
    fn fin_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat.clone())
    }

    /// `HCPoint n` (= `BoolAnalysis.HCPoint n`).
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            n.clone(),
        )
    }
}

impl Environment {
    /// Initialize the Stage-1 boolean-analysis foundations.
    ///
    /// Depends on (each idempotent): `init_fin_sum()` (brings `Fin.sum`, the Rat
    /// field tower, `Fin.castSucc`/`Fin.last`, `Fin`, `Rat.div`/`mk`/`mul`/`sub`/
    /// `one`/`zero`, `Int.ofNat`, `Nat.pow`), `register_nat_testbit_def()`
    /// (`Nat.testBit`, and `init_bool` for `Bool`/`Bool.rec`).
    ///
    /// Registers CHECKED `Declaration::Definition`s only — no axiom is added or
    /// removed, so the soundness certificate's golden TCB is unchanged.
    pub(crate) fn init_boolean_analysis_foundations(&mut self) -> Result<(), EnvError> {
        if self.boolean_analysis_foundations_init {
            return Ok(());
        }
        // `Fin.sum` overlay pulls in the Rat field tower (Rat.div/mk/mul/sub/one/
        // zero, Int.ofNat, Nat.pow via init_nat) and Fin.castSucc/Fin.last.
        self.init_fin_sum()?;
        // `register_nat_testbit_def` pulls in init_nat/init_bool, giving Nat.pow,
        // Bool, Bool.rec, and the real reducible `Nat.testBit` Definition.
        self.register_nat_testbit_def()?;

        let c = FoundationConsts::new();
        self.register_fin_prod(&c)?;
        self.register_fin_sum_nat(&c)?;
        self.register_hcpoint(&c)?;
        self.register_hc_decode(&c)?;
        self.register_expect(&c)?;
        self.register_chi(&c)?;

        self.boolean_analysis_foundations_init = true;
        Ok(())
    }

    /// `Fin.prod (m : Nat) (g : Fin m -> Rat) : Rat` — faithful `Nat.rec` carrier.
    ///
    /// The multiplicative twin of `Fin.sum`: identity `Rat.one`, fold `Rat.mul`.
    /// Same recursive shape as `register_fin_sum`, so the same `Nat.rec` ι-rule
    /// powers its defining equations:
    ///
    /// ```text
    /// Fin.prod := fun (m : Nat) (g : Fin m -> Rat) =>
    ///   @Nat.rec.{1}
    ///     (fun k : Nat => (Fin k -> Rat) -> Rat)
    ///     (fun _g => Rat.one)
    ///     (fun (k : Nat) (ih : (Fin k -> Rat) -> Rat) (g' : Fin (Nat.succ k) -> Rat) =>
    ///        Rat.mul (ih (fun i : Fin k => g' (Fin.castSucc k i))) (g' (Fin.last k)))
    ///     m g
    /// ```
    ///
    /// Ground reductions (verified by the `tests` module): `Fin.prod 0 g ≡ Rat.one`
    /// and `Fin.prod 3 (fun _ => 2/1) ≡ 8/1`.
    fn register_fin_prod(&mut self, c: &FoundationConsts) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("Fin.prod")).is_some() {
            return Ok(());
        }
        let nat_rec = Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        );

        // Type: (m : Nat) -> (Fin m -> Rat) -> Rat
        let fin_prod_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let g_type = c.fin_to_rat(&m);
            let (g_id, _g) = b.fresh_local(g_type.clone());
            let r = b.mk_pi(g_id, BinderInfo::Default, g_type, c.rat.clone());
            let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // Value: fun (m : Nat) (g : Fin m -> Rat) => Nat.rec.{1} motive one_case mul_case m g
        let fin_prod_value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let g_type = c.fin_to_rat(&m);
            let (g_id, g_outer) = b.fresh_local(g_type.clone());

            // Motive: fun (k : Nat) => (Fin k -> Rat) -> Rat
            let motive = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (k_id, k) = ch.fresh_local(c.nat.clone());
                let body = Expr::pi(BinderInfo::Default, c.fin_to_rat(&k), c.rat.clone());
                let r = ch.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body);
                ch.finish_child(r)
            };

            // Zero case: fun (_g : Fin 0 -> Rat) => Rat.one
            let one_case = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
                let g0_type = c.fin_to_rat(&nat_zero);
                let (g0_id, _g0) = ch.fresh_local(g0_type.clone());
                let r = ch.mk_lam(g0_id, BinderInfo::Default, g0_type, c.rat_one.clone());
                ch.finish_child(r)
            };

            // Succ case: fun (k : Nat) (ih : (Fin k -> Rat) -> Rat) (g' : Fin (k+1) -> Rat) =>
            //              Rat.mul (ih (fun i : Fin k => g' (Fin.castSucc k i))) (g' (Fin.last k))
            let mul_case = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (k_id, k) = ch.fresh_local(c.nat.clone());
                let ih_type = Expr::pi(BinderInfo::Default, c.fin_to_rat(&k), c.rat.clone());
                let (ih_id, ih) = ch.fresh_local(ih_type.clone());
                let succ_k = Expr::app(c.nat_succ.clone(), k.clone());
                let g_type_succ = c.fin_to_rat(&succ_k);
                let (gp_id, gp) = ch.fresh_local(g_type_succ.clone());

                // composed: fun (i : Fin k) => g' (Fin.castSucc k i)
                let composed = {
                    let mut ch2 = EnvDeclBuilder::child_of(&ch);
                    let fin_k = c.fin_of(&k);
                    let (i_id, i) = ch2.fresh_local(fin_k.clone());
                    let cast_i = Expr::app(Expr::app(c.fin_cast_succ.clone(), k.clone()), i);
                    let body = Expr::app(gp.clone(), cast_i);
                    let r = ch2.mk_lam(i_id, BinderInfo::Default, fin_k, body);
                    ch2.finish_child(r)
                };

                let ih_app = Expr::app(ih, composed);
                let last_k = Expr::app(c.fin_last.clone(), k.clone());
                let g_last = Expr::app(gp, last_k);
                let prod = Expr::app(Expr::app(c.rat_mul.clone(), ih_app), g_last);

                let r = ch.mk_lam(gp_id, BinderInfo::Default, g_type_succ, prod);
                let r = ch.mk_lam(ih_id, BinderInfo::Default, ih_type, r);
                let r = ch.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), r);
                ch.finish_child(r)
            };

            let rec_app = Expr::apps(nat_rec, [motive, one_case, mul_case, m.clone(), g_outer]);
            let r = b.mk_lam(g_id, BinderInfo::Default, g_type, rec_app);
            let r = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Fin.prod"),
            level_params: vec![],
            type_: fin_prod_type,
            value: fin_prod_value,
            is_reducible: true,
        })
    }

    /// `Fin.sumNat (m : Nat) (g : Fin m -> Nat) : Nat` — Nat-valued `Fin.sum`.
    ///
    /// The additive `Nat.rec` carrier with identity `Nat.zero` and fold `Nat.add`
    /// (same recursive shape as `Fin.prod`/`Fin.sum`). Used by
    /// `FourierWeightAtLevel` to count the true coordinates of a subset indicator
    /// (its popcount `|S|`) as a `Nat`, so the level restriction `|S| = k` is a
    /// reducible `Nat.beq` test. Defining equations:
    ///
    /// ```text
    /// Fin.sumNat 0 g       ≡ Nat.zero
    /// Fin.sumNat (k+1) g   ≡ Nat.add (Fin.sumNat k (g ∘ Fin.castSucc k)) (g (Fin.last k))
    /// ```
    ///
    /// Ground reduction (pinned by the `tests` module): `Fin.sumNat 3 (fun _ => 1)
    /// ≡ 3`.
    fn register_fin_sum_nat(&mut self, c: &FoundationConsts) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("Fin.sumNat")).is_some() {
            return Ok(());
        }
        let nat_rec = Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        );
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);

        // `Fin n -> Nat`.
        let fin_to_nat = |n: &Expr| Expr::pi(BinderInfo::Default, c.fin_of(n), c.nat.clone());

        // Type: (m : Nat) -> (Fin m -> Nat) -> Nat
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let g_type = fin_to_nat(&m);
            let (g_id, _g) = b.fresh_local(g_type.clone());
            let r = b.mk_pi(g_id, BinderInfo::Default, g_type, c.nat.clone());
            let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // Value: fun (m) (g) => Nat.rec.{1} motive zero_case add_case m g
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let g_type = fin_to_nat(&m);
            let (g_id, g_outer) = b.fresh_local(g_type.clone());

            // Motive: fun (k : Nat) => (Fin k -> Nat) -> Nat
            let motive = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (k_id, k) = ch.fresh_local(c.nat.clone());
                let body = Expr::pi(BinderInfo::Default, fin_to_nat(&k), c.nat.clone());
                let r = ch.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body);
                ch.finish_child(r)
            };

            // Zero case: fun (_g : Fin 0 -> Nat) => Nat.zero
            let zero_case = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let nz = Expr::const_(Name::from_string("Nat.zero"), vec![]);
                let g0_type = fin_to_nat(&nz);
                let (g0_id, _g0) = ch.fresh_local(g0_type.clone());
                let r = ch.mk_lam(g0_id, BinderInfo::Default, g0_type, nat_zero.clone());
                ch.finish_child(r)
            };

            // Succ case: fun (k) (ih : (Fin k -> Nat) -> Nat) (g' : Fin (k+1) -> Nat) =>
            //   Nat.add (ih (fun i : Fin k => g' (Fin.castSucc k i))) (g' (Fin.last k))
            let add_case = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (k_id, k) = ch.fresh_local(c.nat.clone());
                let ih_type = Expr::pi(BinderInfo::Default, fin_to_nat(&k), c.nat.clone());
                let (ih_id, ih) = ch.fresh_local(ih_type.clone());
                let succ_k = Expr::app(c.nat_succ.clone(), k.clone());
                let g_type_succ = fin_to_nat(&succ_k);
                let (gp_id, gp) = ch.fresh_local(g_type_succ.clone());

                let composed = {
                    let mut ch2 = EnvDeclBuilder::child_of(&ch);
                    let fin_k = c.fin_of(&k);
                    let (i_id, i) = ch2.fresh_local(fin_k.clone());
                    let cast_i = Expr::app(Expr::app(c.fin_cast_succ.clone(), k.clone()), i);
                    let body = Expr::app(gp.clone(), cast_i);
                    let r = ch2.mk_lam(i_id, BinderInfo::Default, fin_k, body);
                    ch2.finish_child(r)
                };

                let ih_app = Expr::app(ih, composed);
                let last_k = Expr::app(c.fin_last.clone(), k.clone());
                let g_last = Expr::app(gp, last_k);
                let sum = Expr::app(Expr::app(nat_add.clone(), ih_app), g_last);

                let r = ch.mk_lam(gp_id, BinderInfo::Default, g_type_succ, sum);
                let r = ch.mk_lam(ih_id, BinderInfo::Default, ih_type, r);
                let r = ch.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), r);
                ch.finish_child(r)
            };

            let rec_app = Expr::apps(nat_rec, [motive, zero_case, add_case, m.clone(), g_outer]);
            let r = b.mk_lam(g_id, BinderInfo::Default, g_type, rec_app);
            let r = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Fin.sumNat"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `BoolAnalysis.HCPoint (n : Nat) : Type := Fin n -> Bool` — a cube point.
    ///
    /// Type alias Definition: `n` coordinates, each a `Bool`. (This is today's
    /// misnamed `BoolFn`; the Stage-2 migration retargets the public name.)
    fn register_hcpoint(&mut self, c: &FoundationConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("BoolAnalysis.HCPoint"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.type0.clone());
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let body = Expr::pi(BinderInfo::Default, c.fin_of(&n), c.bool_.clone());
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("BoolAnalysis.HCPoint"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `BoolAnalysis.hcDecode (n : Nat) (k : Fin (Nat.pow 2 n)) : HCPoint n :=`
    /// `fun (i : Fin n) => Nat.testBit (Fin.val k) (Fin.val i)`.
    ///
    /// The `k`-th cube point read off the bits of `k`. Reuses the real reducible
    /// `Nat.testBit`, `Fin.val`, and `Nat.pow` Definitions. `Fin.val`'s `n` slot
    /// is implicit; the kernel fills binders positionally on a raw const
    /// application (`@Fin.val (Nat.pow 2 n) k`, `@Fin.val n i`).
    fn register_hc_decode(&mut self, c: &FoundationConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("BoolAnalysis.hcDecode"))
            .is_some()
        {
            return Ok(());
        }
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
        let testbit = Expr::const_(Name::from_string("Nat.testBit"), vec![]);
        let two = Expr::app(
            c.nat_succ.clone(),
            Expr::app(
                c.nat_succ.clone(),
                Expr::const_(Name::from_string("Nat.zero"), vec![]),
            ),
        );

        // `Nat.pow 2 n` for a given `n`.
        let pow2 = |n: &Expr| Expr::apps(nat_pow.clone(), [two.clone(), n.clone()]);

        // Type: (n : Nat) -> (k : Fin (Nat.pow 2 n)) -> HCPoint n
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let fin_pow = c.fin_of(&pow2(&n));
            let (k_id, _k) = b.fresh_local(fin_pow.clone());
            let result = c.hcpoint_of(&n);
            let r = b.mk_pi(k_id, BinderInfo::Default, fin_pow, result);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // Value: fun (n : Nat) (k : Fin (Nat.pow 2 n)) =>
        //          fun (i : Fin n) => Nat.testBit (Fin.val k) (Fin.val i)
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let fin_pow = c.fin_of(&pow2(&n));
            let (k_id, k) = b.fresh_local(fin_pow.clone());
            // fun (i : Fin n) => Nat.testBit (@Fin.val (Nat.pow 2 n) k) (@Fin.val n i)
            let point = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let val_k = Expr::apps(fin_val.clone(), [pow2(&n), k.clone()]);
                let val_i = Expr::apps(fin_val.clone(), [n.clone(), i]);
                let bit = Expr::apps(testbit.clone(), [val_k, val_i]);
                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_n, bit);
                ch.finish_child(r)
            };
            let r = b.mk_lam(k_id, BinderInfo::Default, fin_pow, point);
            let r = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("BoolAnalysis.hcDecode"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `BoolAnalysis.Expect (n : Nat) (g : HCPoint n -> Rat) : Rat :=`
    /// `Rat.div (Fin.sum (Nat.pow 2 n) (fun k => g (hcDecode n k)))`
    ///        `(Rat.mk (Int.ofNat (Nat.pow 2 n)) 1)`.
    ///
    /// The uniform expectation `E[g] = (Σ_{cube points} g) / 2^n`, summing `g`
    /// over the `2^n` cube points enumerated by `hcDecode`.
    fn register_expect(&mut self, c: &FoundationConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("BoolAnalysis.Expect"))
            .is_some()
        {
            return Ok(());
        }
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let fin_sum = Expr::const_(Name::from_string("Fin.sum"), vec![]);
        let rat_div = Expr::const_(Name::from_string("Rat.div"), vec![]);
        let rat_mk = Expr::const_(Name::from_string("Rat.mk"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let hc_decode = Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]);
        let nat_one = Expr::app(
            c.nat_succ.clone(),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        );
        let two = Expr::app(c.nat_succ.clone(), nat_one.clone());
        let pow2 = |n: &Expr| Expr::apps(nat_pow.clone(), [two.clone(), n.clone()]);

        // `HCPoint n -> Rat`.
        let hcpoint_to_rat =
            |n: &Expr| Expr::pi(BinderInfo::Default, c.hcpoint_of(n), c.rat.clone());

        // Type: (n : Nat) -> (HCPoint n -> Rat) -> Rat
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let g_type = hcpoint_to_rat(&n);
            let (g_id, _g) = b.fresh_local(g_type.clone());
            let r = b.mk_pi(g_id, BinderInfo::Default, g_type, c.rat.clone());
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // Value: fun (n : Nat) (g : HCPoint n -> Rat) =>
        //   Rat.div (Fin.sum (Nat.pow 2 n) (fun (k : Fin (Nat.pow 2 n)) => g (hcDecode n k)))
        //           (Rat.mk (Int.ofNat (Nat.pow 2 n)) 1)
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let g_type = hcpoint_to_rat(&n);
            let (g_id, g) = b.fresh_local(g_type.clone());

            // summand: fun (k : Fin (Nat.pow 2 n)) => g (hcDecode n k)
            let summand = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let fin_pow = c.fin_of(&pow2(&n));
                let (k_id, k) = ch.fresh_local(fin_pow.clone());
                let decoded = Expr::apps(hc_decode.clone(), [n.clone(), k]);
                let body = Expr::app(g.clone(), decoded);
                let r = ch.mk_lam(k_id, BinderInfo::Default, fin_pow, body);
                ch.finish_child(r)
            };

            let numerator = Expr::apps(fin_sum.clone(), [pow2(&n), summand]);
            let denom_int = Expr::app(int_of_nat.clone(), pow2(&n));
            let denominator = Expr::apps(rat_mk.clone(), [denom_int, nat_one.clone()]);
            let body = Expr::apps(rat_div.clone(), [numerator, denominator]);

            let r = b.mk_lam(g_id, BinderInfo::Default, g_type, body);
            let r = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("BoolAnalysis.Expect"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `BoolAnalysis.chi (n : Nat) (S x : HCPoint n) : Rat :=`
    /// `Fin.prod n (fun (i : Fin n) =>`
    /// `  @Bool.rec (fun _ => Rat) Rat.one`
    /// `    (Rat.sub Rat.one (Rat.mul (Rat.mk (Int.ofNat 2) 1)`
    /// `       (@Bool.rec (fun _ => Rat) Rat.zero Rat.one (x i)))) (S i))`.
    ///
    /// The parity character `χ_S(x) = Π_{i : S i} (1 - 2·⟦x i⟧)`, value in
    /// {-1, +1}. The inner `Bool.rec` is the `{0,1}` embedding `⟦x i⟧`; the outer
    /// `Bool.rec` gates the factor by the indicator `S i` (identity `Rat.one`
    /// when `S i = false`). `Bool.rec`'s minor premises are in constructor order
    /// `Bool.false` then `Bool.true`, and the `Type`-valued motive `fun _ => Rat`
    /// puts the recursor at universe 1.
    fn register_chi(&mut self, c: &FoundationConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("BoolAnalysis.chi"))
            .is_some()
        {
            return Ok(());
        }
        let fin_prod = Expr::const_(Name::from_string("Fin.prod"), vec![]);
        let rat_mk = Expr::const_(Name::from_string("Rat.mk"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let bool_rec = Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        );
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_one = Expr::app(c.nat_succ.clone(), nat_zero.clone());
        let two = Expr::app(c.nat_succ.clone(), nat_one.clone());
        // `Rat.mk (Int.ofNat 2) 1` — the rational constant `2`.
        let rat_two = Expr::apps(
            rat_mk.clone(),
            [Expr::app(int_of_nat.clone(), two), nat_one.clone()],
        );

        // `fun (_ : Bool) => Rat` — the shared Type-valued motive.
        let make_motive = |parent: &EnvDeclBuilder| {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (t_id, _t) = mb.fresh_local(c.bool_.clone());
            let lam = mb.mk_lam(t_id, BinderInfo::Default, c.bool_.clone(), c.rat.clone());
            mb.finish_child(lam)
        };

        // Type: (n : Nat) -> (S : HCPoint n) -> (x : HCPoint n) -> Rat
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hcp = c.hcpoint_of(&n);
            let (s_id, _s) = b.fresh_local(hcp.clone());
            let (x_id, _x) = b.fresh_local(hcp.clone());
            let r = b.mk_pi(x_id, BinderInfo::Default, hcp.clone(), c.rat.clone());
            let r = b.mk_pi(s_id, BinderInfo::Default, hcp, r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // Value: fun (n : Nat) (S x : HCPoint n) =>
        //   Fin.prod n (fun (i : Fin n) => <factor>)
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = b.fresh_local(hcp.clone());
            let (x_id, x) = b.fresh_local(hcp.clone());

            // factor: fun (i : Fin n) =>
            //   @Bool.rec (fun _ => Rat) Rat.one
            //     (Rat.sub Rat.one (Rat.mul rat_two (@Bool.rec (fun _ => Rat) Rat.zero Rat.one (x i))))
            //     (S i)
            let factor = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = ch.fresh_local(fin_n.clone());

                // ⟦x i⟧ = @Bool.rec (fun _ => Rat) Rat.zero Rat.one (x i)
                let x_i = Expr::app(x.clone(), i.clone());
                let embed = Expr::apps(
                    bool_rec.clone(),
                    [make_motive(&ch), c.rat_zero.clone(), c.rat_one.clone(), x_i],
                );

                // 1 - 2·⟦x i⟧
                let two_embed = Expr::apps(c.rat_mul.clone(), [rat_two.clone(), embed]);
                let signed = Expr::apps(c.rat_sub.clone(), [c.rat_one.clone(), two_embed]);

                // @Bool.rec (fun _ => Rat) Rat.one <signed> (S i)
                let s_i = Expr::app(s.clone(), i.clone());
                let gated = Expr::apps(
                    bool_rec.clone(),
                    [make_motive(&ch), c.rat_one.clone(), signed, s_i],
                );

                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_n, gated);
                ch.finish_child(r)
            };

            let body = Expr::apps(fin_prod.clone(), [n.clone(), factor]);
            let r = b.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body);
            let r = b.mk_lam(s_id, BinderInfo::Default, hcp, r);
            let r = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("BoolAnalysis.chi"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::env::decl_builder::EnvDeclBuilder;
    use crate::env::types::ConstantKind;
    use crate::env::Environment;
    use crate::expr::{BinderInfo, Expr, ExprKind};

    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_boolean_analysis_foundations()
            .expect("init_boolean_analysis_foundations");
        env
    }

    fn k(s: &str) -> Expr {
        Expr::const_(Name::from_string(s), vec![])
    }

    fn nat_lit(n: u64) -> Expr {
        let mut e = k("Nat.zero");
        for _ in 0..n {
            e = Expr::app(k("Nat.succ"), e);
        }
        e
    }

    /// `n/1` as a `Rat` numeral: `Rat.mk (Int.ofNat n) 1`.
    fn rat_nat(n: u64) -> Expr {
        Expr::apps(
            k("Rat.mk"),
            [Expr::app(k("Int.ofNat"), nat_lit(n)), nat_lit(1)],
        )
    }

    /// `fun (_ : Fin n) => val`.
    fn const_fin_fn(n: &Expr, val: Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let fin_n = Expr::app(k("Fin"), n.clone());
        let (i_id, _i) = b.fresh_local(fin_n.clone());
        let lam = b.mk_lam(i_id, BinderInfo::Default, fin_n, val);
        b.finish(lam)
    }

    #[test]
    fn test_foundations_registered_as_definitions() {
        let env = make_env();
        for name in [
            "Fin.prod",
            "BoolAnalysis.HCPoint",
            "BoolAnalysis.hcDecode",
            "BoolAnalysis.Expect",
            "BoolAnalysis.chi",
        ] {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{name} must be a Definition (CHECKED), not an Axiom"
            );
            assert!(info.value.is_some(), "{name} must retain a reducible body");
        }
    }

    #[test]
    fn test_idempotent() {
        let mut env = Environment::new();
        env.init_boolean_analysis_foundations().expect("first init");
        env.init_boolean_analysis_foundations()
            .expect("second init");
    }

    /// Every foundation's body re-checks against its declared type — the same
    /// C1 re-verification the soundness certificate performs.
    #[test]
    fn test_foundations_definitions_type_check() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in [
            "Fin.prod",
            "BoolAnalysis.HCPoint",
            "BoolAnalysis.hcDecode",
            "BoolAnalysis.Expect",
            "BoolAnalysis.chi",
        ] {
            let info = env.get_const(&Name::from_string(name)).expect("registered");
            let value = info.value.clone().expect("has value");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} body must check against its type: {e:?}"));
        }
    }

    // ── Fin.prod ground reductions ──

    /// `Fin.prod 0 g ≡ Rat.one` — the empty product is the identity.
    #[test]
    fn test_fin_prod_zero_reduces_to_one() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let g = const_fin_fn(&nat_lit(0), k("Rat.one"));
        let prod = Expr::apps(k("Fin.prod"), [nat_lit(0), g]);
        assert!(
            tc.is_def_eq(&prod, &k("Rat.one")),
            "Fin.prod 0 _ must reduce to Rat.one"
        );
    }

    /// `Fin.prod 3 (fun _ => 2/1) ≡ 8/1` — genuine product 2·2·2 = 8, NOT a
    /// constant shell (a sum carrier would give 6/1; the identity-1 placeholder
    /// would give 1/1).
    #[test]
    fn test_fin_prod_three_twos_reduces_to_eight() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let g = const_fin_fn(&nat_lit(3), rat_nat(2));
        let prod = Expr::apps(k("Fin.prod"), [nat_lit(3), g]);
        assert!(
            tc.is_def_eq(&prod, &rat_nat(8)),
            "Fin.prod 3 (fun _ => 2/1) must reduce to 8/1 (genuine product)"
        );
        // Discriminator: it is NOT 6/1 (a sum) nor 1/1 (a degenerate identity).
        assert!(
            !tc.is_def_eq(&prod, &rat_nat(6)),
            "Fin.prod must be a PRODUCT, not Fin.sum (got 6/1)"
        );
        assert!(
            !tc.is_def_eq(&prod, &k("Rat.one")),
            "Fin.prod 3 (2/1) must not collapse to the identity 1/1"
        );
    }

    // ── Fin.sumNat ground reductions ──

    /// `Fin.sumNat 0 g ≡ Nat.zero` and `Fin.sumNat 3 (fun _ => 1) ≡ 3` — a
    /// genuine Nat sum 1+1+1 = 3 (NOT a product, which would give 1; NOT a
    /// degenerate 0).
    #[test]
    fn test_fin_sum_nat_reduces() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());

        // Fin.sumNat 0 (fun _ => 1) ≡ 0
        let g0 = const_fin_fn(&nat_lit(0), nat_lit(1));
        let s0 = Expr::apps(k("Fin.sumNat"), [nat_lit(0), g0]);
        assert!(
            tc.is_def_eq(&s0, &nat_lit(0)),
            "Fin.sumNat 0 _ must reduce to Nat.zero"
        );

        // Fin.sumNat 3 (fun _ => 1) ≡ 3
        let g3 = const_fin_fn(&nat_lit(3), nat_lit(1));
        let s3 = Expr::apps(k("Fin.sumNat"), [nat_lit(3), g3]);
        assert!(
            tc.is_def_eq(&s3, &nat_lit(3)),
            "Fin.sumNat 3 (fun _ => 1) must reduce to 3 (genuine Nat sum)"
        );
        assert!(
            !tc.is_def_eq(&s3, &nat_lit(1)),
            "Fin.sumNat must be a SUM, not a product (got 1)"
        );
    }

    // ── HCPoint type alias ──

    /// `BoolAnalysis.HCPoint n ≡ Fin n -> Bool` for a closed `n`.
    #[test]
    fn test_hcpoint_unfolds_to_fin_to_bool() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let n = nat_lit(3);
        let hcp = Expr::app(k("BoolAnalysis.HCPoint"), n.clone());
        let expected = Expr::pi(BinderInfo::Default, Expr::app(k("Fin"), n), k("Bool"));
        assert!(
            tc.is_def_eq(&hcp, &expected),
            "HCPoint 3 must be def-eq to Fin 3 -> Bool"
        );
        // It lives in Type 0 = Sort 1.
        let sort = tc.infer_type(&hcp).expect("infer HCPoint 3 sort");
        assert!(
            matches!(sort.kind(), ExprKind::Sort(_)),
            "HCPoint 3 must be a type (Sort), got {sort:?}"
        );
    }

    // ── hcDecode coordinate readback ──

    /// Coordinate readback on a small closed `k`: with `n = 2` and
    /// `k = ⟨1, _⟩ : Fin 4` (binary `01`), `hcDecode 2 k` reads bit 0 = `true`
    /// and bit 1 = `false`. We apply the decoded point to concrete `Fin 2`
    /// indices `⟨0,_⟩` and `⟨1,_⟩` and check the resulting `Bool`.
    #[test]
    fn test_hc_decode_coordinate_readback() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());

        // Fin.mk : {m} -> (val : Nat) -> (isLt : Prop) -> Fin m. The isLt slot is
        // a `Prop`, so `True : Prop` inhabits it (mirrors Fin.castSucc/Fin.last).
        let true_prop = k("True");
        let fin_mk = |m: Expr, val: Expr| Expr::apps(k("Fin.mk"), [m, val, true_prop.clone()]);

        let n = nat_lit(2);
        let four = nat_lit(4);
        // k = ⟨1, _⟩ : Fin 4  (bits: bit0 = 1, bit1 = 0).
        let k_pt = fin_mk(four, nat_lit(1));
        let decoded = Expr::apps(k("BoolAnalysis.hcDecode"), [n.clone(), k_pt]);

        // coordinate 0: ⟨0, _⟩ : Fin 2  => testBit 1 0 = true
        let i0 = fin_mk(n.clone(), nat_lit(0));
        let coord0 = Expr::app(decoded.clone(), i0);
        assert!(
            tc.is_def_eq(&coord0, &k("Bool.true")),
            "hcDecode 2 ⟨1⟩ at coordinate 0 must be true (bit 0 of 1)"
        );

        // coordinate 1: ⟨1, _⟩ : Fin 2  => testBit 1 1 = false
        let i1 = fin_mk(n, nat_lit(1));
        let coord1 = Expr::app(decoded, i1);
        assert!(
            tc.is_def_eq(&coord1, &k("Bool.false")),
            "hcDecode 2 ⟨1⟩ at coordinate 1 must be false (bit 1 of 1)"
        );
    }

    // ── Expect ──

    /// `Expect 0 (fun _ => Rat.one) ≡ Rat.one`: Σ over the single (2^0 = 1) cube
    /// point of `1`, divided by `2^0 = 1`. The numerator reduces to `1/1` and the
    /// denominator is `1/1`, so `Rat.div (1/1) (1/1) ≡ Rat.one` (division by `1`
    /// is the genuine reducible case in the Rat quotient).
    #[test]
    fn test_expect_n0_ones_reduces_to_one() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());

        // g : HCPoint 0 -> Rat := fun _ => Rat.one
        let hcp0 = Expr::app(k("BoolAnalysis.HCPoint"), nat_lit(0));
        let g = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, _p) = b.fresh_local(hcp0.clone());
            let lam = b.mk_lam(p_id, BinderInfo::Default, hcp0, k("Rat.one"));
            b.finish(lam)
        };
        let expect = Expr::apps(k("BoolAnalysis.Expect"), [nat_lit(0), g]);
        assert!(
            tc.is_def_eq(&expect, &k("Rat.one")),
            "Expect 0 (fun _ => 1) must reduce to Rat.one"
        );
    }

    /// `Expect 1 (fun _ => Rat.one)` ground-reduces to `Rat.div (2/1) (2/1)` — the
    /// CORRECT closed value: numerator `Σ_{k<2} 1 = 2/1` and denominator
    /// `2^1 = 2/1`. This is mathematically `1`, but the Rat quotient does not
    /// definitionally normalize `2/2` to the canonical `Rat.one` form (only
    /// division by `1` does); so the faithful definitional-correctness pin is the
    /// genuine reducible witness `2/1 ÷ 2/1`, which proves the sum-over-cube and
    /// `2^n` denominator both computed correctly. (Proving it propositionally
    /// equal to `Rat.one` is a Stage-2+ theorem, not a Stage-1 reduction fact.)
    #[test]
    fn test_expect_n1_ones_reduces_to_two_over_two() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());

        // g : HCPoint 1 -> Rat := fun _ => Rat.one
        let hcp1 = Expr::app(k("BoolAnalysis.HCPoint"), nat_lit(1));
        let g = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, _p) = b.fresh_local(hcp1.clone());
            let lam = b.mk_lam(p_id, BinderInfo::Default, hcp1, k("Rat.one"));
            b.finish(lam)
        };
        let expect = Expr::apps(k("BoolAnalysis.Expect"), [nat_lit(1), g]);

        // The genuine reducible ground value: 2/1 ÷ 2/1.
        let two = rat_nat(2);
        let expected = Expr::apps(k("Rat.div"), [two.clone(), two]);
        assert!(
            tc.is_def_eq(&expect, &expected),
            "Expect 1 (fun _ => 1) must reduce to Rat.div (2/1) (2/1)"
        );
        // The numerator is genuinely 2/1 (Σ of two ones), not a degenerate value.
        assert!(
            !tc.is_def_eq(&expect, &k("Rat.zero")),
            "Expect 1 (fun _ => 1) must not be the degenerate 0"
        );
    }

    // ── chi ──

    /// `chi n S0 x ≡ Rat.one` where `S0` = all-false (the empty subset): every
    /// factor is gated off to `Rat.one`, so the product over `n` coordinates is
    /// `Rat.one`. Checked at `n = 3` over an arbitrary `x` (a symbolic point):
    /// the all-false indicator makes the value independent of `x`.
    #[test]
    fn test_chi_empty_subset_reduces_to_one() {
        let n = nat_lit(3);
        let hcp_n = Expr::app(k("BoolAnalysis.HCPoint"), n.clone());

        // x : HCPoint 3 — an arbitrary symbolic point. With an all-false S, chi
        // does not depend on x, so a registered opaque witness is fine. Register
        // it BEFORE building a TypeChecker so the env is borrowed only once.
        let mut env = make_env();
        env.add_decl(crate::env::Declaration::Axiom {
            name: Name::from_string("__test_chi_x"),
            level_params: vec![],
            type_: hcp_n,
        })
        .expect("register symbolic x");
        let tc = TypeChecker::with_mode(&env, env.mode());

        // S0 : HCPoint 3 := fun _ => Bool.false  (empty subset)
        let s0 = {
            let mut b = EnvDeclBuilder::new();
            let fin_n = Expr::app(k("Fin"), n.clone());
            let (i_id, _i) = b.fresh_local(fin_n.clone());
            let lam = b.mk_lam(i_id, BinderInfo::Default, fin_n, k("Bool.false"));
            b.finish(lam)
        };
        let x = Expr::const_(Name::from_string("__test_chi_x"), vec![]);

        let chi = Expr::apps(k("BoolAnalysis.chi"), [n, s0, x]);
        assert!(
            tc.is_def_eq(&chi, &k("Rat.one")),
            "chi 3 (all-false S) x must reduce to Rat.one (empty-subset character)"
        );
    }
}
