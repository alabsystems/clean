// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Int arithmetic operations and sign/abs initialization for Environment
//!
//! Split into separate files (#307):
//! - data_types_arithmetic.rs: Int operations (init_int_arith, init_int_sign_abs) (this file)
//! - data_types_int_lemmas.rs: Int lemmas + Int/Nat conversion lemmas
//! - data_types_nat_lemmas.rs: Nat arithmetic lemmas

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Int arithmetic operations
    ///
    /// This adds:
    /// - Int.subNatNat : Nat → Nat → Int (computes n - m as Int)
    /// - Int.negOfNat : Nat → Int (computes -n)
    /// - Int.add : Int → Int → Int
    /// - Int.sub : Int → Int → Int
    /// - Int.mul : Int → Int → Int
    ///
    /// These follow the Lean 4 definitions:
    /// - subNatNat m n := if m >= n then ofNat (m - n) else negSucc (n - m - 1)
    /// - negOfNat n := if n = 0 then ofNat 0 else negSucc (n - 1)
    /// - add uses subNatNat for mixed-sign cases
    /// - sub m n := m + (- n)
    /// - mul handles all four sign combinations
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_arith_init == true`
    /// ENSURES: On success, required dependencies (`int`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_arith(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, residual-to-zero
        // campaign 2026-07-03): the Clean-native Int arithmetic cluster is
        // NOT Lean-faithful in its SYMBOLIC reduction behaviour —
        // `Int.subNatNat` is an iterated-decrement loop (vs Lean's single
        // case on `Nat.sub n m`), so Lean-valid rfl-proofs over open Int
        // terms (`Int.exists_strictMono`: `negSucc (n+1) + 1 ≟ negSucc n`)
        // are rejected when the stubs SHADOW the genuine olean definitions.
        // In import mode skip the whole cluster so Lean's genuine
        // `Int.add`/`Int.subNatNat`/instances import through the checked
        // path (the caller-closure audit shows nothing else in the import
        // prelude references these names). The default proof-execution lane
        // (stubs + their constructive lemma web) is byte-identical.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.int_arith_init {
            return Ok(());
        }

        // Ensure Int and Nat operations are initialized
        self.init_int()?;

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let _nat_sub = Expr::const_(Name::from_string("Nat.sub"), vec![]);
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let nat_rec = Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        );
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let int_neg_succ = Expr::const_(Name::from_string("Int.negSucc"), vec![]);
        let int_rec = Expr::const_(
            Name::from_string("Int.rec"),
            vec![Level::succ(Level::zero())],
        );

        // ========================================
        // Int.negOfNat : Nat → Int
        // negOfNat n := Nat.rec (ofNat 0) (λ k _ => negSucc k) n
        // negOfNat 0 = ofNat 0
        // negOfNat (succ k) = negSucc k
        // ========================================
        let neg_of_nat_type = Expr::pi(BinderInfo::Default, nat_const.clone(), int_const.clone());

        let neg_of_nat_motive =
            Expr::lam(BinderInfo::Default, nat_const.clone(), int_const.clone());

        // zero case: ofNat 0
        let neg_of_nat_zero_case = Expr::app(int_of_nat.clone(), nat_zero.clone());

        let neg_of_nat_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            // succ case: λ k : Nat => λ _ : Int => negSucc k
            let (k_id, k) = b.fresh_local(nat_const.clone());
            let (ih_id, _ih) = b.fresh_local(int_const.clone());
            let succ_case = b.mk_lam(
                ih_id,
                BinderInfo::Default,
                int_const.clone(),
                Expr::app(int_neg_succ.clone(), k),
            );
            let succ_case = b.mk_lam(k_id, BinderInfo::Default, nat_const.clone(), succ_case);
            let body = Expr::apps(
                nat_rec.clone(),
                [
                    neg_of_nat_motive.clone(),
                    neg_of_nat_zero_case,
                    succ_case,
                    n,
                ],
            );
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Int.negOfNat"),
            level_params: vec![],
            type_: neg_of_nat_type,
            value: neg_of_nat_value,
            is_reducible: true,
        })?;

        let int_neg_of_nat = Expr::const_(Name::from_string("Int.negOfNat"), vec![]);

        // ========================================
        // Int.subNatNat : Nat → Nat → Int
        // subNatNat m n := Nat.rec (ofNat m) (λ k ih =>
        //   Int.rec (λ i => Int)
        //     (λ p => Nat.rec (negSucc 0) (λ q _ => negSucc (succ q)) p)
        //     (λ p => negSucc (succ p))
        //     ih
        // ) n
        //
        // This is complex. Simpler approach:
        // subNatNat m 0 = ofNat m
        // subNatNat 0 (succ n) = negSucc n
        // subNatNat (succ m) (succ n) = subNatNat m n
        //
        // We can express this as:
        // subNatNat m n := Nat.rec (ofNat m) (λ k ih =>
        //   Int.rec (λ _ => Int)
        //     (λ p => Nat.rec (negSucc 0) (λ q _ => negSucc (succ q)) p)
        //     (λ p => negSucc (succ p))
        //     ih
        // ) n
        //
        // Actually, let's use a cleaner definition based on subtraction:
        // subNatNat m n :=
        //   Nat.rec (ofNat m)
        //     (λ _ (ih : Int) =>
        //       Int.rec (λ _ => Int)
        //         (λ p => Nat.rec (negSucc 0) (λ q _ => negSucc (succ q)) p)  -- ofNat p -> decrease
        //         (λ p => negSucc (succ p))  -- negSucc p -> negSucc (succ p)
        //         ih)
        //     n
        // ========================================
        let sub_nat_nat_type = Expr::pi(
            BinderInfo::Default,
            nat_const.clone(),
            Expr::pi(BinderInfo::Default, nat_const.clone(), int_const.clone()),
        );

        // We need a simpler approach. Let's use the fact that:
        // subNatNat m n = if m >= n then ofNat (m - n) else negSucc (n - m - 1)
        //
        // Using Nat.rec on n:
        // subNatNat m 0 = ofNat m
        // subNatNat m (succ n') =
        //   match (subNatNat m n') with
        //   | ofNat 0 => negSucc 0
        //   | ofNat (succ p) => ofNat p
        //   | negSucc p => negSucc (succ p)
        //
        // motive: λ _ : Nat => Int
        let snn_motive = Expr::lam(BinderInfo::Default, nat_const.clone(), int_const.clone());

        // int_motive: λ _ : Int => Int
        let int_motive = Expr::lam(BinderInfo::Default, int_const.clone(), int_const.clone());

        // Build of_nat_case_for_snn and neg_succ_case_for_snn as closed lambda terms
        let of_nat_case_for_snn = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(nat_const.clone());
            // succ case: λ q : Nat => λ _ : Int => ofNat q
            let (q_id, q) = b.fresh_local(nat_const.clone());
            let (ih_id, _ih) = b.fresh_local(int_const.clone());
            let sc = b.mk_lam(
                ih_id,
                BinderInfo::Default,
                int_const.clone(),
                Expr::app(int_of_nat.clone(), q),
            );
            let sc = b.mk_lam(q_id, BinderInfo::Default, nat_const.clone(), sc);
            let body = Expr::apps(
                nat_rec.clone(),
                [
                    snn_motive.clone(),
                    Expr::app(int_neg_succ.clone(), nat_zero.clone()),
                    sc,
                    p,
                ],
            );
            let e = b.mk_lam(p_id, BinderInfo::Default, nat_const.clone(), body);
            b.finish(e)
        };

        // negSucc case: λ p : Nat => negSucc (succ p)
        let neg_succ_case_for_snn = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(nat_const.clone());
            let body = Expr::app(int_neg_succ.clone(), Expr::app(nat_succ.clone(), p));
            let e = b.mk_lam(p_id, BinderInfo::Default, nat_const.clone(), body);
            b.finish(e)
        };

        // subNatNat value:
        // λ m n : Nat => Nat.rec (ofNat m) (λ k ih => Int.rec int_motive of_nat_case neg_succ_case ih) n
        let sub_nat_nat_value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat_const.clone());
            let (n_id, n) = b.fresh_local(nat_const.clone());
            // step: λ k : Nat => λ ih : Int => Int.rec int_motive of_nat_case neg_succ_case ih
            let (k_id, _k) = b.fresh_local(nat_const.clone());
            let (ih_id, ih) = b.fresh_local(int_const.clone());
            let step = Expr::apps(
                int_rec.clone(),
                [
                    int_motive.clone(),
                    of_nat_case_for_snn.clone(),
                    neg_succ_case_for_snn.clone(),
                    ih,
                ],
            );
            let step = b.mk_lam(ih_id, BinderInfo::Default, int_const.clone(), step);
            let step = b.mk_lam(k_id, BinderInfo::Default, nat_const.clone(), step);
            let body = Expr::apps(
                nat_rec.clone(),
                [
                    snn_motive.clone(),
                    Expr::app(int_of_nat.clone(), m),
                    step,
                    n,
                ],
            );
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            let e = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Int.subNatNat"),
            level_params: vec![],
            type_: sub_nat_nat_type,
            value: sub_nat_nat_value,
            is_reducible: true,
        })?;

        let int_sub_nat_nat = Expr::const_(Name::from_string("Int.subNatNat"), vec![]);

        // ========================================
        // Int.add : Int → Int → Int
        // add m n := Int.rec (Int.rec (λ _ => Int) ... ...) ... m n
        //
        // Based on Lean 4:
        // | ofNat m, ofNat n => ofNat (m + n)
        // | ofNat m, negSucc n => subNatNat m (succ n)
        // | negSucc m, ofNat n => subNatNat n (succ m)
        // | negSucc m, negSucc n => negSucc (succ (m + n))
        // ========================================
        let int_add_type = Expr::pi(
            BinderInfo::Default,
            int_const.clone(),
            Expr::pi(BinderInfo::Default, int_const.clone(), int_const.clone()),
        );

        // add_motive: λ _ : Int => Int → Int
        let add_motive = Expr::lam(
            BinderInfo::Default,
            int_const.clone(),
            Expr::pi(BinderInfo::Default, int_const.clone(), int_const.clone()),
        );

        // inner_motive: λ _ : Int => Int
        let inner_motive = Expr::lam(BinderInfo::Default, int_const.clone(), int_const.clone());

        // Int.add value using builder
        let int_add_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(int_const.clone());
            let (bv_id, bv) = b.fresh_local(int_const.clone());

            // ofNat case: λ m : Nat => λ n : Int => ...
            let (m_id, m) = b.fresh_local(nat_const.clone());
            let (n_id, n) = b.fresh_local(int_const.clone());

            // ofNat + ofNat: λ n' => ofNat (m + n')
            let (np1_id, np1) = b.fresh_local(nat_const.clone());
            let oo = b.mk_lam(
                np1_id,
                BinderInfo::Default,
                nat_const.clone(),
                Expr::app(
                    int_of_nat.clone(),
                    Expr::app(Expr::app(nat_add.clone(), m.clone()), np1),
                ),
            );
            // ofNat + negSucc: λ n' => subNatNat m (succ n')
            let (np2_id, np2) = b.fresh_local(nat_const.clone());
            let on = b.mk_lam(
                np2_id,
                BinderInfo::Default,
                nat_const.clone(),
                Expr::app(
                    Expr::app(int_sub_nat_nat.clone(), m.clone()),
                    Expr::app(nat_succ.clone(), np2),
                ),
            );
            let add_of_nat_body =
                Expr::apps(int_rec.clone(), [inner_motive.clone(), oo, on, n.clone()]);
            let add_of_nat_case = b.mk_lam(
                n_id,
                BinderInfo::Default,
                int_const.clone(),
                add_of_nat_body,
            );
            let add_of_nat_case = b.mk_lam(
                m_id,
                BinderInfo::Default,
                nat_const.clone(),
                add_of_nat_case,
            );

            // negSucc case: λ m : Nat => λ n : Int => ...
            let (m2_id, m2) = b.fresh_local(nat_const.clone());
            let (n2_id, n2) = b.fresh_local(int_const.clone());

            // negSucc + ofNat: λ n' => subNatNat n' (succ m)
            let (np3_id, np3) = b.fresh_local(nat_const.clone());
            let no = b.mk_lam(
                np3_id,
                BinderInfo::Default,
                nat_const.clone(),
                Expr::app(
                    Expr::app(int_sub_nat_nat.clone(), np3),
                    Expr::app(nat_succ.clone(), m2.clone()),
                ),
            );
            // negSucc + negSucc: λ n' => negSucc (succ (m + n'))
            let (np4_id, np4) = b.fresh_local(nat_const.clone());
            let nn = b.mk_lam(
                np4_id,
                BinderInfo::Default,
                nat_const.clone(),
                Expr::app(
                    int_neg_succ.clone(),
                    Expr::app(
                        nat_succ.clone(),
                        Expr::app(Expr::app(nat_add.clone(), m2.clone()), np4),
                    ),
                ),
            );
            let add_neg_succ_body =
                Expr::apps(int_rec.clone(), [inner_motive.clone(), no, nn, n2.clone()]);
            let add_neg_succ_case = b.mk_lam(
                n2_id,
                BinderInfo::Default,
                int_const.clone(),
                add_neg_succ_body,
            );
            let add_neg_succ_case = b.mk_lam(
                m2_id,
                BinderInfo::Default,
                nat_const.clone(),
                add_neg_succ_case,
            );

            // λ a b => (Int.rec add_motive add_of_nat_case add_neg_succ_case a) b
            let body = Expr::app(
                Expr::apps(
                    int_rec.clone(),
                    [add_motive.clone(), add_of_nat_case, add_neg_succ_case, a],
                ),
                bv,
            );
            let e = b.mk_lam(bv_id, BinderInfo::Default, int_const.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, int_const.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Int.add"),
            level_params: vec![],
            type_: int_add_type,
            value: int_add_value,
            is_reducible: true,
        })?;

        let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
        let int_neg = Expr::const_(Name::from_string("Int.neg"), vec![]);

        // ========================================
        // Int.sub : Int → Int → Int
        // sub m n := Int.add m (Int.neg n)
        // ========================================
        let int_sub_type = Expr::pi(
            BinderInfo::Default,
            int_const.clone(),
            Expr::pi(BinderInfo::Default, int_const.clone(), int_const.clone()),
        );

        let int_sub_value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(int_const.clone());
            let (n_id, n) = b.fresh_local(int_const.clone());
            let body = Expr::app(Expr::app(int_add.clone(), m), Expr::app(int_neg.clone(), n));
            let e = b.mk_lam(n_id, BinderInfo::Default, int_const.clone(), body);
            let e = b.mk_lam(m_id, BinderInfo::Default, int_const.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Int.sub"),
            level_params: vec![],
            type_: int_sub_type,
            value: int_sub_value,
            is_reducible: true,
        })?;

        // ========================================
        // Int.mul : Int → Int → Int
        // | ofNat m, ofNat n => ofNat (m * n)
        // | ofNat m, negSucc n => negOfNat (m * succ n)
        // | negSucc m, ofNat n => negOfNat (succ m * n)
        // | negSucc m, negSucc n => ofNat (succ m * succ n)
        // ========================================
        let int_mul_type = Expr::pi(
            BinderInfo::Default,
            int_const.clone(),
            Expr::pi(BinderInfo::Default, int_const.clone(), int_const.clone()),
        );

        // mul_motive: λ _ : Int => Int → Int
        let mul_motive = Expr::lam(
            BinderInfo::Default,
            int_const.clone(),
            Expr::pi(BinderInfo::Default, int_const.clone(), int_const.clone()),
        );

        // Int.mul value using builder
        let int_mul_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(int_const.clone());
            let (bv_id, bv) = b.fresh_local(int_const.clone());

            // ofNat case: λ m : Nat => λ n : Int => ...
            let (m_id, m) = b.fresh_local(nat_const.clone());
            let (n_id, n) = b.fresh_local(int_const.clone());
            // ofNat * ofNat: λ n' => ofNat (m * n')
            let (np1_id, np1) = b.fresh_local(nat_const.clone());
            let oo = b.mk_lam(
                np1_id,
                BinderInfo::Default,
                nat_const.clone(),
                Expr::app(
                    int_of_nat.clone(),
                    Expr::app(Expr::app(nat_mul.clone(), m.clone()), np1),
                ),
            );
            // ofNat * negSucc: λ n' => negOfNat (m * succ n')
            let (np2_id, np2) = b.fresh_local(nat_const.clone());
            let on = b.mk_lam(
                np2_id,
                BinderInfo::Default,
                nat_const.clone(),
                Expr::app(
                    int_neg_of_nat.clone(),
                    Expr::app(
                        Expr::app(nat_mul.clone(), m.clone()),
                        Expr::app(nat_succ.clone(), np2),
                    ),
                ),
            );
            let mul_of_nat_body =
                Expr::apps(int_rec.clone(), [inner_motive.clone(), oo, on, n.clone()]);
            let mul_of_nat_case = b.mk_lam(
                n_id,
                BinderInfo::Default,
                int_const.clone(),
                mul_of_nat_body,
            );
            let mul_of_nat_case = b.mk_lam(
                m_id,
                BinderInfo::Default,
                nat_const.clone(),
                mul_of_nat_case,
            );

            // negSucc case: λ m : Nat => λ n : Int => ...
            let (m2_id, m2) = b.fresh_local(nat_const.clone());
            let (n2_id, n2) = b.fresh_local(int_const.clone());
            let succ_m2 = Expr::app(nat_succ.clone(), m2.clone());
            // negSucc * ofNat: λ n' => negOfNat (succ m * n')
            let (np3_id, np3) = b.fresh_local(nat_const.clone());
            let no = b.mk_lam(
                np3_id,
                BinderInfo::Default,
                nat_const.clone(),
                Expr::app(
                    int_neg_of_nat.clone(),
                    Expr::app(Expr::app(nat_mul.clone(), succ_m2.clone()), np3),
                ),
            );
            // negSucc * negSucc: λ n' => ofNat (succ m * succ n')
            let (np4_id, np4) = b.fresh_local(nat_const.clone());
            let nn = b.mk_lam(
                np4_id,
                BinderInfo::Default,
                nat_const.clone(),
                Expr::app(
                    int_of_nat.clone(),
                    Expr::app(
                        Expr::app(nat_mul.clone(), succ_m2),
                        Expr::app(nat_succ.clone(), np4),
                    ),
                ),
            );
            let mul_neg_succ_body =
                Expr::apps(int_rec.clone(), [inner_motive.clone(), no, nn, n2.clone()]);
            let mul_neg_succ_case = b.mk_lam(
                n2_id,
                BinderInfo::Default,
                int_const.clone(),
                mul_neg_succ_body,
            );
            let mul_neg_succ_case = b.mk_lam(
                m2_id,
                BinderInfo::Default,
                nat_const.clone(),
                mul_neg_succ_case,
            );

            // λ a b => (Int.rec mul_motive mul_of_nat_case mul_neg_succ_case a) b
            let body = Expr::app(
                Expr::apps(
                    int_rec.clone(),
                    [mul_motive.clone(), mul_of_nat_case, mul_neg_succ_case, a],
                ),
                bv,
            );
            let e = b.mk_lam(bv_id, BinderInfo::Default, int_const.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, int_const.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Int.mul"),
            level_params: vec![],
            type_: int_mul_type,
            value: int_mul_value,
            is_reducible: true,
        })?;

        // ========================================
        // Int.div / Int.mod : Int → Int → Int
        //
        // These mirror `Nat.div` / `Nat.mod` (data_types_nat.rs): registered as
        // `Declaration::Opaque` with a type-correct placeholder body that the
        // kernel never unfolds. Concrete evaluation is supplied by the
        // already-registered `Int.div`/`Int.mod` native reducers
        // (native_reducers_int.rs). `Opaque` is NOT an `Axiom`, so a term
        // referencing these does not gain an axiom dependency — `env.axiom_deps`
        // only counts `ConstantKind::Axiom` (axiom_audit.rs). This unblocks the
        // HDiv/HMod Int instances without introducing any axiom. (Track PP)
        //
        // NB: deliberately does NOT register `Int.land`/`Int.lor`/`Int.xor` —
        // trust-ir's Basic.lean *defines its own* `Int.land`/`Int.lor`/`Int.xor`
        // (Lean 4.8.0 omits them), and a prelude copy would collide with a
        // `Duplicate declaration` error when Basic.lean is checked. Arith.lean
        // imports Basic, so those bitwise ops resolve to Basic's definitions.
        //
        // `add_decl_if_absent` keeps this idempotent and avoids clobbering the
        // separate EuclideanDomain wiring (algebra_advanced/euclidean_domain_int.rs)
        // which — outside the default prelude — registers `Int.div`/`Int.mod`
        // as axioms for its Euclidean-domain instance.
        let int_binop_ty = Expr::pi(
            BinderInfo::Default,
            int_const.clone(),
            Expr::pi(BinderInfo::Default, int_const.clone(), int_const.clone()),
        );
        let int_binop_placeholder = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _a) = b.fresh_local(int_const.clone());
            let (b_id, _b) = b.fresh_local(int_const.clone());
            let zero = Expr::app(int_of_nat.clone(), Expr::nat_lit(0));
            let e = b.mk_lam(b_id, BinderInfo::Default, int_const.clone(), zero);
            let e = b.mk_lam(a_id, BinderInfo::Default, int_const.clone(), e);
            b.finish(e)
        };
        for op in ["Int.div", "Int.mod"] {
            self.add_decl_if_absent(Declaration::Opaque {
                name: Name::from_string(op),
                level_params: vec![],
                type_: int_binop_ty.clone(),
                value: int_binop_placeholder.clone(),
            })?;
        }

        // Int.beq : Int → Int → Bool
        //
        // Backs the `instBEqInt` instance and thus `==`/`!=` over `Int` (`rhs ==
        // 0`, `w1 != width`, … throughout trust-ir's `Semantics/Arith.lean`).
        // The `Int.beq` native reducer (native_reducers_int.rs) still fires first
        // on closed LITERAL operands (the hot path). Two forms, chosen by whether
        // `Nat.beq` is available in THIS environment:
        //
        //  - full form (Nat.beq present, e.g. `with_prelude`): a genuine `Int.rec`
        //    Definition (mirroring `Int.add`) matching ofNat/negSucc → `Nat.beq`,
        //    so `Int.beq (ofNat n)(ofNat n)` iota-reduces to `Nat.beq n n` for
        //    SYMBOLIC `n`. The former Opaque `fun _ _ => Bool.false` placeholder
        //    could never reduce symbolically, which blocked clean-auto from
        //    discharging any `Int.beq _ _ = true` goal (the shape the trust-wp
        //    signed lane emits). Semantics (Lean 4): ofNat m,ofNat n => Nat.beq m
        //    n; ofNat _,negSucc _ => false; negSucc _,ofNat _ => false; negSucc
        //    m,negSucc n => Nat.beq m n. `is_reducible` matches `Int.add`; the body
        //    agrees with the native reducer.
        //  - fallback (Nat.beq absent, e.g. the minimal `init_boolean_analysis`
        //    envs): the original Opaque placeholder, so those environments — which
        //    never declare `Nat.beq` — keep declaring `Int.beq` successfully and
        //    are byte-identical to before. `Opaque` is NOT an `Axiom`.
        let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);
        let int_beq_ty = Expr::pi(
            BinderInfo::Default,
            int_const.clone(),
            Expr::pi(BinderInfo::Default, int_const.clone(), bool_const.clone()),
        );
        if self.get_const(&Name::from_string("Nat.beq")).is_some() {
            let nat_beq = Expr::const_(Name::from_string("Nat.beq"), vec![]);
            let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
            // beq_motive : λ _ : Int => Int → Bool ; beq_inner_motive : λ _ : Int => Bool
            let beq_motive = Expr::lam(
                BinderInfo::Default,
                int_const.clone(),
                Expr::pi(BinderInfo::Default, int_const.clone(), bool_const.clone()),
            );
            let beq_inner_motive =
                Expr::lam(BinderInfo::Default, int_const.clone(), bool_const.clone());
            let int_beq_value = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(int_const.clone());
                let (bv_id, bv) = b.fresh_local(int_const.clone());
                // ofNat case: λ m:Nat => λ n:Int => Int.rec inner (λ n' => Nat.beq m n') (λ n' => false) n
                let (m_id, m) = b.fresh_local(nat_const.clone());
                let (n_id, n) = b.fresh_local(int_const.clone());
                let (np1_id, np1) = b.fresh_local(nat_const.clone());
                let oo = b.mk_lam(
                    np1_id,
                    BinderInfo::Default,
                    nat_const.clone(),
                    Expr::app(Expr::app(nat_beq.clone(), m.clone()), np1),
                );
                let (np2_id, _np2) = b.fresh_local(nat_const.clone());
                let on = b.mk_lam(
                    np2_id,
                    BinderInfo::Default,
                    nat_const.clone(),
                    bool_false.clone(),
                );
                let beq_of_nat_body = Expr::apps(
                    int_rec.clone(),
                    [beq_inner_motive.clone(), oo, on, n.clone()],
                );
                let beq_of_nat_case = b.mk_lam(
                    n_id,
                    BinderInfo::Default,
                    int_const.clone(),
                    beq_of_nat_body,
                );
                let beq_of_nat_case = b.mk_lam(
                    m_id,
                    BinderInfo::Default,
                    nat_const.clone(),
                    beq_of_nat_case,
                );
                // negSucc case: λ m:Nat => λ n:Int => Int.rec inner (λ n' => false) (λ n' => Nat.beq m n') n
                let (m2_id, m2) = b.fresh_local(nat_const.clone());
                let (n2_id, n2) = b.fresh_local(int_const.clone());
                let (np3_id, _np3) = b.fresh_local(nat_const.clone());
                let no = b.mk_lam(
                    np3_id,
                    BinderInfo::Default,
                    nat_const.clone(),
                    bool_false.clone(),
                );
                let (np4_id, np4) = b.fresh_local(nat_const.clone());
                let nn = b.mk_lam(
                    np4_id,
                    BinderInfo::Default,
                    nat_const.clone(),
                    Expr::app(Expr::app(nat_beq.clone(), m2.clone()), np4),
                );
                let beq_neg_succ_body = Expr::apps(
                    int_rec.clone(),
                    [beq_inner_motive.clone(), no, nn, n2.clone()],
                );
                let beq_neg_succ_case = b.mk_lam(
                    n2_id,
                    BinderInfo::Default,
                    int_const.clone(),
                    beq_neg_succ_body,
                );
                let beq_neg_succ_case = b.mk_lam(
                    m2_id,
                    BinderInfo::Default,
                    nat_const.clone(),
                    beq_neg_succ_case,
                );
                // λ a b => (Int.rec beq_motive of_nat_case neg_succ_case a) b
                let body = Expr::app(
                    Expr::apps(
                        int_rec.clone(),
                        [beq_motive.clone(), beq_of_nat_case, beq_neg_succ_case, a],
                    ),
                    bv,
                );
                let e = b.mk_lam(bv_id, BinderInfo::Default, int_const.clone(), body);
                let e = b.mk_lam(a_id, BinderInfo::Default, int_const.clone(), e);
                b.finish(e)
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string("Int.beq"),
                level_params: vec![],
                type_: int_beq_ty,
                value: int_beq_value,
                is_reducible: true,
            })?;
        } else {
            let int_beq_placeholder = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, _a) = b.fresh_local(int_const.clone());
                let (b_id, _b) = b.fresh_local(int_const.clone());
                let false_v = Expr::const_(Name::from_string("Bool.false"), vec![]);
                let e = b.mk_lam(b_id, BinderInfo::Default, int_const.clone(), false_v);
                let e = b.mk_lam(a_id, BinderInfo::Default, int_const.clone(), e);
                b.finish(e)
            };
            self.add_decl_if_absent(Declaration::Opaque {
                name: Name::from_string("Int.beq"),
                level_params: vec![],
                type_: int_beq_ty,
                value: int_beq_placeholder,
            })?;
        }

        // ========================================
        // Int.pow : Int → Nat → Int   (base : Int, exponent : Nat)
        //   pow base 0       = 1
        //   pow base (n + 1) = (pow base n) * base
        //
        // A genuine, axiom-free `Nat.rec` recursion on the exponent — mirrors
        // `Nat.pow` but with an `Int` base/result. Backs `HPow Int Nat Int`
        // (the `(2 : Int) ^ width` shape used throughout trust-ir's Arith.lean,
        // where the exponent is a `Nat`). Axiom-free: built from `Nat.rec`,
        // `Int.mul`, and `Int.ofNat 1`. (Track PP)
        let int_pow_type = Expr::pi(
            BinderInfo::Default,
            int_const.clone(),
            Expr::pi(BinderInfo::Default, nat_const.clone(), int_const.clone()),
        );
        let int_mul_const = Expr::const_(Name::from_string("Int.mul"), vec![]);
        let int_one = Expr::app(int_of_nat.clone(), Expr::nat_lit(1));
        // motive : Nat → Int (constant Int)
        let int_pow_motive = Expr::lam(BinderInfo::Default, nat_const.clone(), int_const.clone());
        let int_pow_value = {
            let mut b = EnvDeclBuilder::new();
            let (base_id, base) = b.fresh_local(int_const.clone());
            let (n_id, n) = b.fresh_local(nat_const.clone());
            // succ case: fun (_ : Nat) (ih : Int) => Int.mul ih base
            let (k_id, _k) = b.fresh_local(nat_const.clone());
            let (ih_id, ih) = b.fresh_local(int_const.clone());
            let pow_succ = b.mk_lam(
                ih_id,
                BinderInfo::Default,
                int_const.clone(),
                Expr::app(Expr::app(int_mul_const.clone(), ih), base.clone()),
            );
            let pow_succ = b.mk_lam(k_id, BinderInfo::Default, nat_const.clone(), pow_succ);
            let body = Expr::apps(
                nat_rec.clone(),
                [int_pow_motive.clone(), int_one.clone(), pow_succ, n],
            );
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            let e = b.mk_lam(base_id, BinderInfo::Default, int_const.clone(), e);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string("Int.pow"),
            level_params: vec![],
            type_: int_pow_type,
            value: int_pow_value,
            is_reducible: true,
        })?;

        self.int_arith_init = true;
        Ok(())
    }

    /// Check if Int arithmetic operations have been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_int_arith` has completed successfully
    /// ENSURES: Pure - no side effects
    pub(crate) fn has_int_arith(&self) -> bool {
        self.int_arith_init
    }

    /// Initialize Int sign and absolute value operations
    ///
    /// This adds:
    /// - `Int.natAbs : Int → Nat` - absolute value as natural number
    ///   - natAbs (ofNat n) = n
    ///   - natAbs (negSucc n) = succ n
    /// - `Int.sign : Int → Int` - signum function
    ///   - sign (ofNat 0) = 0
    ///   - sign (ofNat (succ n)) = 1
    ///   - sign (negSucc n) = -1
    /// - `Int.abs : Int → Int` - absolute value
    ///   - abs n = ofNat (natAbs n)
    ///
    /// Note: Int.neg is already defined in init_int().
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_sign_abs_init == true`
    /// ENSURES: On success, required dependencies (`int_arith`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_sign_abs(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, residual-to-zero
        // campaign 2026-07-03): the Clean-native Int arithmetic cluster is
        // NOT Lean-faithful in its SYMBOLIC reduction behaviour —
        // `Int.subNatNat` is an iterated-decrement loop (vs Lean's single
        // case on `Nat.sub n m`), so Lean-valid rfl-proofs over open Int
        // terms (`Int.exists_strictMono`: `negSucc (n+1) + 1 ≟ negSucc n`)
        // are rejected when the stubs SHADOW the genuine olean definitions.
        // In import mode skip the whole cluster so Lean's genuine
        // `Int.add`/`Int.subNatNat`/instances import through the checked
        // path (the caller-closure audit shows nothing else in the import
        // prelude references these names). The default proof-execution lane
        // (stubs + their constructive lemma web) is byte-identical.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.int_sign_abs_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_int_arith()?; // Provides Int type, ofNat, negSucc

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_rec = Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        );
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let int_neg_succ = Expr::const_(Name::from_string("Int.negSucc"), vec![]);
        let int_rec = Expr::const_(
            Name::from_string("Int.rec"),
            vec![Level::succ(Level::zero())],
        );

        // ========================================
        // Int.natAbs : Int → Nat
        // natAbs (ofNat n) = n
        // natAbs (negSucc n) = succ n
        // ========================================
        let nat_abs_type = Expr::pi(BinderInfo::Default, int_const.clone(), nat_const.clone());

        // motive: λ _ : Int => Nat
        let nat_abs_motive = Expr::lam(BinderInfo::Default, int_const.clone(), nat_const.clone());

        let nat_abs_value = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(int_const.clone());
            // ofNat case: λ n : Nat => n
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let of_nat_case = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), n);
            // negSucc case: λ n : Nat => succ n
            let (n2_id, n2) = b.fresh_local(nat_const.clone());
            let neg_succ_case = b.mk_lam(
                n2_id,
                BinderInfo::Default,
                nat_const.clone(),
                Expr::app(nat_succ.clone(), n2),
            );
            let body = Expr::apps(
                int_rec.clone(),
                [nat_abs_motive, of_nat_case, neg_succ_case, i],
            );
            let e = b.mk_lam(i_id, BinderInfo::Default, int_const.clone(), body);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Int.natAbs"),
            level_params: vec![],
            type_: nat_abs_type,
            value: nat_abs_value,
            is_reducible: true,
        })?;

        let int_nat_abs = Expr::const_(Name::from_string("Int.natAbs"), vec![]);

        // Note: Int.neg is already defined in init_int()

        // ========================================
        // Int.abs : Int → Int
        // abs n = ofNat (natAbs n)
        // ========================================
        let abs_type = Expr::pi(BinderInfo::Default, int_const.clone(), int_const.clone());

        // Int.abs := λ i : Int => ofNat (natAbs i)
        let abs_value = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(int_const.clone());
            let body = Expr::app(int_of_nat.clone(), Expr::app(int_nat_abs.clone(), i));
            let e = b.mk_lam(i_id, BinderInfo::Default, int_const.clone(), body);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Int.abs"),
            level_params: vec![],
            type_: abs_type,
            value: abs_value,
            is_reducible: true,
        })?;

        // ========================================
        // Int.sign : Int → Int
        // sign (ofNat 0) = 0
        // sign (ofNat (succ n)) = 1
        // sign (negSucc n) = -1 (i.e., negSucc 0)
        // ========================================
        let sign_type = Expr::pi(BinderInfo::Default, int_const.clone(), int_const.clone());

        // sign motive: λ _ : Int => Int
        let sign_motive = Expr::lam(BinderInfo::Default, int_const.clone(), int_const.clone());

        // ofNat case: λ n : Nat => Nat.rec (ofNat 0) (λ _ _ => ofNat 1) n
        // sign (ofNat 0) = 0, sign (ofNat (succ _)) = 1
        let one_nat = Expr::app(nat_succ.clone(), nat_zero.clone());
        let int_one = Expr::app(int_of_nat.clone(), one_nat);
        let int_zero = Expr::app(int_of_nat.clone(), nat_zero.clone());
        let int_neg_one = Expr::app(int_neg_succ.clone(), nat_zero.clone()); // negSucc 0 = -1

        let sign_value = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(int_const.clone());
            let nat_to_int_motive =
                Expr::lam(BinderInfo::Default, nat_const.clone(), int_const.clone());

            // ofNat case: λ n => Nat.rec motive 0 (λ _ _ => 1) n
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let (k_id, _k) = b.fresh_local(nat_const.clone());
            let (ih_id, _ih) = b.fresh_local(int_const.clone());
            let succ_br = b.mk_lam(
                ih_id,
                BinderInfo::Default,
                int_const.clone(),
                int_one.clone(),
            );
            let succ_br = b.mk_lam(k_id, BinderInfo::Default, nat_const.clone(), succ_br);
            let of_nat_body = Expr::apps(
                nat_rec.clone(),
                [nat_to_int_motive, int_zero.clone(), succ_br, n],
            );
            let of_nat_case = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), of_nat_body);

            // negSucc case: λ _ => -1
            let (n2_id, _n2) = b.fresh_local(nat_const.clone());
            let neg_succ_case = b.mk_lam(
                n2_id,
                BinderInfo::Default,
                nat_const.clone(),
                int_neg_one.clone(),
            );

            let body = Expr::apps(
                int_rec.clone(),
                [sign_motive, of_nat_case, neg_succ_case, i],
            );
            let e = b.mk_lam(i_id, BinderInfo::Default, int_const.clone(), body);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Int.sign"),
            level_params: vec![],
            type_: sign_type,
            value: sign_value,
            is_reducible: true,
        })?;

        self.int_sign_abs_init = true;
        Ok(())
    }

    /// Check if Int sign/abs operations have been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_int_sign_abs` has completed successfully
    /// ENSURES: Pure - no side effects
    pub(crate) fn has_int_sign_abs(&self) -> bool {
        self.int_sign_abs_init
    }
}
