// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Int arithmetic lemmas and Int/Nat conversion lemmas
//!
//! Split from data_types_arithmetic.rs (#307):
//! - data_types_arithmetic.rs: Int operations (init_int_arith, init_int_sign_abs)
//! - data_types_int_lemmas.rs: Int lemmas + Int/Nat conversion lemmas (this file)
//! - data_types_nat_lemmas.rs: Nat arithmetic lemmas

use crate::env::{EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Int arithmetic lemmas
    ///
    /// This adds fundamental algebraic lemmas for Int (all kernel-checked
    /// `Declaration::Theorem`s; the former #3604 axioms were promoted to
    /// constructive proofs):
    /// - Int.add_negSucc_ofNat_succ : theorem ∀ m n : Nat, Eq (Int.add (Int.negSucc n) (Int.ofNat (Nat.succ m))) (Int.subNatNat m n)
    /// - Int.add_negSucc_negSucc_subNatNat_zero : theorem ∀ n k : Nat, Eq (Int.add (Int.negSucc n) (Int.negSucc k)) (Int.subNatNat Nat.zero (Nat.add (Nat.succ n) (Nat.succ k)))
    /// - Int.add_negSucc_subNatNat : theorem ∀ k m n : Nat, Eq (Int.add (Int.negSucc k) (Int.subNatNat m n)) (Int.subNatNat m (Nat.add n (Nat.succ k)))
    /// - Int.add_ofNat_negSucc : theorem ∀ m n : Nat, Eq (Int.add (Int.ofNat m) (Int.negSucc n)) (Int.subNatNat m (Nat.succ n))
    /// - Int.add_ofNat_succ_negSucc : theorem ∀ m n : Nat, Eq (Int.add (Int.ofNat (Nat.succ m)) (Int.negSucc n)) (Int.subNatNat m n)
    /// - Int.add_ofNat_succ_subNatNat : theorem ∀ m n k : Nat, Eq (Int.add (Int.ofNat (Nat.succ m)) (Int.subNatNat n k)) (Int.subNatNat (Nat.add n (Nat.succ m)) k)
    /// - Int.add_subNatNat_negSucc : theorem ∀ m n k : Nat, Eq (Int.add (Int.subNatNat m n) (Int.negSucc k)) (Int.subNatNat m (Nat.add n (Nat.succ k)))
    /// - Int.add_subNatNat_ofNat_succ : theorem ∀ m n k : Nat, Eq (Int.add (Int.subNatNat m n) (Int.ofNat (Nat.succ k))) (Int.subNatNat (Nat.add m (Nat.succ k)) n)
    /// - Int.add_subNatNat_zero_left_ofNat_succ : theorem ∀ n k : Nat, Eq (Int.add (Int.subNatNat Nat.zero n) (Int.ofNat (Nat.succ k))) (Int.subNatNat (Nat.succ k) n)
    /// - Int.add_subNatNat_zero_right_ofNat_succ : theorem ∀ m k : Nat, Eq (Int.add (Int.subNatNat m Nat.zero) (Int.ofNat (Nat.succ k))) (Int.subNatNat (Nat.add m (Nat.succ k)) Nat.zero)
    /// - Int.add_subNatNat_zero_right_negSucc : theorem ∀ m k : Nat, Eq (Int.add (Int.subNatNat m Nat.zero) (Int.negSucc k)) (Int.subNatNat m (Nat.succ k))
    /// - Int.subNatNat_succ_succ : theorem ∀ m n : Nat, Eq (Int.subNatNat (Nat.succ m) (Nat.succ n)) (Int.subNatNat m n)
    /// - Int.subNatNat_zero_right : theorem ∀ m : Nat, Eq (Int.subNatNat m Nat.zero) (Int.ofNat m)
    /// - Int.subNatNat_zero_succ : theorem ∀ n : Nat, Eq (Int.subNatNat Nat.zero (Nat.succ n)) (Int.negSucc n)
    /// - Int.subNatNat_eq_add : theorem ∀ m n : Nat, Eq (Int.subNatNat m n) (Int.add (Int.ofNat m) (Int.negOfNat n)) -- #3604 (constructive via @Nat.rec on n + Nat.add_zero)
    /// - Int.add_comm : theorem ∀ a b : Int, Eq (Int.add a b) (Int.add b a) -- #3604 (constructive via @Int.rec)
    /// - Int.add_assoc_negSucc_ofNat_succ_negSucc : theorem ∀ k m n : Nat, Eq (Int.add (Int.add (Int.negSucc k) (Int.ofNat (Nat.succ m))) (Int.negSucc n)) (Int.add (Int.negSucc k) (Int.add (Int.ofNat (Nat.succ m)) (Int.negSucc n)))
    /// - Int.add_assoc_negSucc_ofNat_succ_ofNat_succ : theorem ∀ k m n : Nat, Eq (Int.add (Int.add (Int.negSucc k) (Int.ofNat (Nat.succ m))) (Int.ofNat (Nat.succ n))) (Int.add (Int.negSucc k) (Int.add (Int.ofNat (Nat.succ m)) (Int.ofNat (Nat.succ n))))
    /// - Int.add_assoc_negSucc_negSucc_negSucc : theorem ∀ m n k : Nat, Eq (Int.add (Int.add (Int.negSucc m) (Int.negSucc n)) (Int.negSucc k)) (Int.add (Int.negSucc m) (Int.add (Int.negSucc n) (Int.negSucc k)))
    /// - Int.add_assoc_negSucc_negSucc_ofNat_succ : theorem ∀ m n k : Nat, Eq (Int.add (Int.add (Int.negSucc m) (Int.negSucc n)) (Int.ofNat (Nat.succ k))) (Int.add (Int.negSucc m) (Int.add (Int.negSucc n) (Int.ofNat (Nat.succ k))))
    /// - Int.add_assoc_ofNat : theorem ∀ m n k : Nat, Eq (Int.add (Int.add (Int.ofNat m) (Int.ofNat n)) (Int.ofNat k)) (Int.add (Int.ofNat m) (Int.add (Int.ofNat n) (Int.ofNat k)))
    /// - Int.add_assoc_ofNat_succ_negSucc_negSucc : theorem ∀ m n k : Nat, Eq (Int.add (Int.add (Int.ofNat (Nat.succ m)) (Int.negSucc n)) (Int.negSucc k)) (Int.add (Int.ofNat (Nat.succ m)) (Int.add (Int.negSucc n) (Int.negSucc k)))
    /// - Int.add_assoc_ofNat_succ_negSucc_ofNat_succ : theorem ∀ m n k : Nat, Eq (Int.add (Int.add (Int.ofNat (Nat.succ m)) (Int.negSucc n)) (Int.ofNat (Nat.succ k))) (Int.add (Int.ofNat (Nat.succ m)) (Int.add (Int.negSucc n) (Int.ofNat (Nat.succ k))))
    /// - Int.add_assoc_ofNat_succ_ofNat_negSucc : theorem ∀ m n k : Nat, Eq (Int.add (Int.add (Int.ofNat (Nat.succ m)) (Int.ofNat n)) (Int.negSucc k)) (Int.add (Int.ofNat (Nat.succ m)) (Int.add (Int.ofNat n) (Int.negSucc k)))
    /// - Int.add_assoc_zero_left : theorem ∀ b c : Int, Eq (Int.add (Int.add Int.zero b) c) (Int.add Int.zero (Int.add b c))
    /// - Int.add_assoc_zero_middle : theorem ∀ a c : Int, Eq (Int.add (Int.add a Int.zero) c) (Int.add a (Int.add Int.zero c))
    /// - Int.add_assoc_zero_right : theorem ∀ a b : Int, Eq (Int.add (Int.add a b) Int.zero) (Int.add a (Int.add b Int.zero))
    /// - Int.add_zero : theorem ∀ a : Int, Eq (Int.add a Int.zero) a
    /// - Int.add_assoc : theorem ∀ a b c : Int, Eq (Int.add (Int.add a b) c) (Int.add a (Int.add b c))
    /// - Int.add_right_cancel : theorem ∀ a b c : Int, Eq (Int.add a b) (Int.add c b) → Eq a c -- #3604 (constructive via Int.add_neg_cancel_right; empty domain-axiom closure)
    /// - Int.zero_add : theorem ∀ a : Int, Eq (Int.add Int.zero a) a
    /// - Int.add_neg_self : theorem ∀ a : Int, Eq (Int.add a (Int.neg a)) Int.zero -- #3604 (constructive via nested Int.rec + Nat.rec + Int.subNatNat_self)
    /// - Int.neg_add_self : theorem ∀ a : Int, Eq (Int.add (Int.neg a) a) Int.zero -- #3604 (constructive via nested Int.rec + Nat.rec + Int.subNatNat_self)
    /// - Int.mul_comm : theorem ∀ a b : Int, Eq (Int.mul a b) (Int.mul b a) -- #3604 (constructive via nested @Int.rec + Nat.mul_comm)
    /// - Int.mul_assoc : theorem ∀ a b c : Int, Eq (Int.mul (Int.mul a b) c) (Int.mul a (Int.mul b c)) -- #3604 (constructive via triple nested @Int.rec + sign lemmas + Nat.mul_assoc)
    /// - Int.mul_left_cancel_ofNat_succ : theorem ∀ (n : Nat) (a b : Int), Eq (Int.mul (Int.ofNat (Nat.succ n)) a) (Int.mul (Int.ofNat (Nat.succ n)) b) → Eq a b -- #3604 (constructive via nested @Int.rec + Int.noConfusion + Nat.mul_left_cancel_succ + Nat.succ_inj)
    /// - Int.mul_one : theorem ∀ a : Int, Eq (Int.mul a (Int.ofNat 1)) a -- #3604 (constructive via @Int.rec + Nat.mul_one)
    /// - Int.one_mul : theorem ∀ a : Int, Eq (Int.mul (Int.ofNat 1) a) a -- #3604 (constructive via @Int.rec + Nat.one_mul)
    /// - Int.mul_zero : theorem ∀ a : Int, Eq (Int.mul a Int.zero) Int.zero -- #3604 (constructive via @Int.rec, pure Eq.refl)
    /// - Int.zero_mul : theorem ∀ a : Int, Eq (Int.mul Int.zero a) Int.zero -- #3604 (constructive via @Int.rec + Nat.zero_mul)
    /// - Int.left_distrib : theorem ∀ a b c : Int, Eq (Int.mul a (Int.add b c)) (Int.add (Int.mul a b) (Int.mul a c)) -- #3604 (constructive via triple nested @Int.rec + Int.{ofNat,negSucc}_mul_subNatNat)
    /// - Int.right_distrib : theorem ∀ a b c : Int, Eq (Int.mul (Int.add a b) c) (Int.add (Int.mul a c) (Int.mul b c)) -- #3604 (constructive via Int.left_distrib + Int.mul_comm)
    /// - Int.neg_neg : theorem ∀ a : Int, Eq (Int.neg (Int.neg a)) a -- #3604 (constructive via @Int.rec + nested @Nat.rec, pure Eq.refl)
    /// - Int.neg_subNatNat : theorem ∀ m n : Nat, Eq (Int.neg (Int.subNatNat m n)) (Int.subNatNat n m) -- #3604 (constructive via nested Nat.rec)
    /// - Int.neg_add : theorem ∀ a b : Int, Eq (Int.neg (Int.add a b)) (Int.add (Int.neg a) (Int.neg b)) -- #3604 (constructive via nested Int.rec/Nat.rec + Int.neg_subNatNat)
    /// - Int.neg_mul_left : theorem ∀ a b : Int, Eq (Int.neg (Int.mul a b)) (Int.mul (Int.neg a) b) -- #3604 (constructive via nested Int.rec + Nat.rec helpers + Nat.zero_mul)
    /// - Int.neg_mul_right : theorem ∀ a b : Int, Eq (Int.neg (Int.mul a b)) (Int.mul a (Int.neg b)) -- #3604 (constructive via nested Int.rec + Nat.rec helpers)
    /// - Int.sub_self : theorem ∀ a : Int, Eq (Int.sub a a) Int.zero -- #3604 (constructive via λ a => Int.add_neg_self a)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_arith_lemmas_init == true`
    /// ENSURES: On success, required dependencies (`int_arith`, `eq`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_arith_lemmas(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): the Int arithmetic
        // stub cluster is suppressed in import mode (see `init_int_arith`);
        // these lemmas state/prove properties of the suppressed stubs, so
        // they are suppressed with them (the genuine olean lemmas import).
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.int_arith_lemmas_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_int_arith()?; // Provides Int.add, Int.sub, Int.mul, Int.neg
        self.init_eq()?; // Provides Eq

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let _int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
        let _int_mul = Expr::const_(Name::from_string("Int.mul"), vec![]);
        let _int_neg = Expr::const_(Name::from_string("Int.neg"), vec![]);
        let _int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let _nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let _nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let _nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        // Helper: build Eq Int lhs rhs
        let _mk_int_eq =
            |lhs: Expr, rhs: Expr| Expr::apps(eq_const.clone(), [int_const.clone(), lhs, rhs]);

        // Int.subNatNat_zero_right : ∀ m : Nat, Eq (Int.subNatNat m Nat.zero) (Int.ofNat m)
        //
        // SOUNDNESS (#3604 prerequisite): Real kernel-checked
        // normalization theorem for the mixed-sign `Int.add` substrate.
        // `Int.subNatNat` recurses on its second Nat argument, so the
        // zero case reduces directly to `Int.ofNat m`; the proof is
        // pure `Eq.refl`.
        self.register_int_sub_nat_nat_zero_right_proof()?;

        // Int.subNatNat_zero_succ : ∀ n : Nat, Eq (Int.subNatNat Nat.zero (Nat.succ n)) (Int.negSucc n)
        //
        // SOUNDNESS (#3604 prerequisite): Real kernel-checked
        // negative-branch normalization theorem for `Int.subNatNat`.
        // The proof inducts on n and maps the induction hypothesis
        // through the same decrement function used by the reducible
        // `Int.subNatNat` definition.
        self.register_int_sub_nat_nat_zero_succ_proof()?;

        // Int.subNatNat_succ_succ : ∀ m n : Nat, Eq (Int.subNatNat (Nat.succ m) (Nat.succ n)) (Int.subNatNat m n)
        //
        // SOUNDNESS (#3604 prerequisite): Real kernel-checked
        // successor/successor cancellation for `Int.subNatNat`.
        // This is the core mixed-sign arithmetic normalization needed
        // before `Int.add_assoc` can be removed.
        self.register_int_sub_nat_nat_succ_succ_proof()?;

        // Int.subNatNat_eq_add : ∀ m n : Nat,
        //   Eq (Int.subNatNat m n) (Int.add (Int.ofNat m) (Int.negOfNat n))
        //
        // SOUNDNESS (#3604 prerequisite): Real kernel-checked normalization
        // theorem re-expressing the mixed-sign `Int.subNatNat m n` as the
        // honest two-term `Int.add` of its positive part `Int.ofNat m` and
        // negative part `Int.negOfNat n`. Proven by `@Nat.rec.{0}` on `n`
        // (case analysis): the zero case maps `Nat.add_zero` through
        // `congrArg Int.ofNat`, the succ case closes by `Eq.refl` because
        // both sides reduce to `Int.subNatNat m (Nat.succ k)`. Empty
        // domain-axiom closure. Bridge lemma toward a constructive
        // `Int.left_distrib` / `Int.right_distrib`: it rewrites the
        // mixed-sign `Int.add` branches into a genuine `Int.add` sum.
        // See `algebra_int_sub_nat_nat_eq_add_proof.rs`.
        self.register_int_sub_nat_nat_eq_add_proof()?;

        // Int.add_ofNat_negSucc : ∀ m n : Nat, Eq (Int.add (Int.ofNat m) (Int.negSucc n)) (Int.subNatNat m (Nat.succ n))
        //
        // SOUNDNESS (#3604 prerequisite): Real kernel-checked
        // mixed-sign branch theorem for `Int.add`. This gives later
        // `Int.add_assoc` work a named normalization step for the
        // ofNat/negSucc case without depending on associativity.
        self.register_int_add_ofnat_negsucc_proof()?;

        // Int.add_ofNat_succ_negSucc : ∀ m n : Nat, Eq (Int.add (Int.ofNat (Nat.succ m)) (Int.negSucc n)) (Int.subNatNat m n)
        //
        // SOUNDNESS (#3604 prerequisite): Two-step mixed-sign
        // normalization. It composes `Int.add_ofNat_negSucc` with
        // `Int.subNatNat_succ_succ` via `Eq.trans`, giving the explicit
        // positive-successor/negative cancellation used by associativity.
        self.register_int_add_ofnat_succ_negsucc_proof()?;

        // Int.add_negSucc_ofNat_succ : ∀ m n : Nat, Eq (Int.add (Int.negSucc n) (Int.ofNat (Nat.succ m))) (Int.subNatNat m n)
        //
        // SOUNDNESS (#3604 prerequisite): Right-mixed-order companion
        // to `Int.add_ofNat_succ_negSucc`. It exposes the nested
        // `negSucc + ofNat` branch needed by associativity.
        self.register_int_add_negsucc_ofnat_succ_proof()?;

        // Int.add_zero : ∀ a : Int, Eq (a + 0) a
        //
        // SOUNDNESS (#3604 prerequisite): Real kernel-checked zero
        // transport theorem. The `ofNat` branch maps `Nat.add_zero`
        // through `Int.ofNat`; the `negSucc` branch reuses
        // `Int.subNatNat_zero_succ`.
        self.register_int_add_zero_proof()?;

        // Int.add_subNatNat_zero_left_ofNat_succ :
        //   ∀ n k : Nat,
        //     Eq ((subNatNat 0 n) + ofNat (succ k)) (subNatNat (succ k) n)
        //
        // SOUNDNESS (#3604 prerequisite): First nonzero positive transport
        // theorem over an intermediate `Int.subNatNat` result. The zero
        // case maps `Nat.zero_add` through `Int.ofNat`; the successor case
        // chains `Int.subNatNat_zero_succ`,
        // `Int.add_negSucc_ofNat_succ`, and
        // `Int.subNatNat_succ_succ`.
        self.register_int_add_sub_nat_nat_zero_left_ofnat_succ_proof()?;

        // Int.add_subNatNat_zero_right_ofNat_succ :
        //   ∀ m k : Nat,
        //     Eq ((subNatNat m 0) + ofNat (succ k))
        //        (subNatNat (m + succ k) 0)
        //
        // SOUNDNESS (#3604 prerequisite): Arbitrary-`m` zero-right base
        // case for positive transport over an intermediate `Int.subNatNat`
        // result. Both sides reduce to `Int.ofNat (Nat.add m (Nat.succ k))`.
        self.register_int_add_sub_nat_nat_zero_right_ofnat_succ_proof()?;

        // Int.add_subNatNat_ofNat_succ :
        //   ∀ m n k : Nat,
        //     Eq ((subNatNat m n) + ofNat (succ k))
        //        (subNatNat (m + succ k) n)
        //
        // SOUNDNESS (#3604 prerequisite): General positive transport
        // theorem over an intermediate `Int.subNatNat` result. The proof
        // inducts on n, uses the zero-right transport as the base case,
        // and in the successor case combines the zero-left frontier,
        // `Nat.zero_add`, `Nat.succ_add`, `Int.subNatNat_succ_succ`,
        // and the induction hypothesis.
        self.register_int_add_sub_nat_nat_ofnat_succ_proof()?;

        // Int.add_subNatNat_zero_right_negSucc :
        //   ∀ m k : Nat,
        //     Eq ((subNatNat m 0) + negSucc k) (subNatNat m (succ k))
        //
        // SOUNDNESS (#3604 prerequisite): Arbitrary-`m` zero-right base
        // case for negative transport over an intermediate `Int.subNatNat`
        // result. Both sides reduce to `Int.subNatNat m (Nat.succ k)`.
        self.register_int_add_sub_nat_nat_zero_right_negsucc_proof()?;

        // Int.add_negSucc_negSucc_subNatNat_zero :
        //   ∀ n k : Nat,
        //     Eq (negSucc n + negSucc k) (subNatNat 0 (succ n + succ k))
        //
        // SOUNDNESS (#3604 prerequisite): Zero-left/successor branch for
        // negative transport over an intermediate `Int.subNatNat` result.
        // The proof combines `Nat.add_succ`, `Nat.succ_add`, and
        // `Int.subNatNat_zero_succ` to expose the target index required by
        // the full negative transport theorem.
        self.register_int_add_negsucc_negsucc_sub_nat_nat_zero_proof()?;

        // Int.add_subNatNat_negSucc :
        //   ∀ m n k : Nat,
        //     Eq ((subNatNat m n) + negSucc k)
        //        (subNatNat m (n + succ k))
        //
        // SOUNDNESS (#3604 prerequisite): General negative transport
        // theorem over an intermediate `Int.subNatNat` result. The proof
        // inducts on n, uses the zero-right negative transport as the
        // base case, and in the successor case combines the zero-left
        // negSucc/negSucc frontier, `Nat.zero_add`, `Nat.succ_add`,
        // `Int.subNatNat_zero_succ`, `Int.subNatNat_succ_succ`, and the
        // induction hypothesis.
        self.register_int_add_sub_nat_nat_negsucc_proof()?;

        // Int.add_ofNat_succ_subNatNat :
        //   ∀ m n k : Nat,
        //     Eq (ofNat (succ m) + subNatNat n k)
        //        (subNatNat (n + succ m) k)
        //
        // SOUNDNESS (#3604 prerequisite): Left-operand positive transport
        // for reassociation once `b + c` has normalized to `subNatNat`.
        // This composes checked `Int.add_comm` with the full positive
        // right-operand transport `Int.add_subNatNat_ofNat_succ`.
        self.register_int_add_ofnat_succ_sub_nat_nat_proof()?;

        // Int.add_negSucc_subNatNat :
        //   ∀ k m n : Nat,
        //     Eq (negSucc k + subNatNat m n)
        //        (subNatNat m (n + succ k))
        //
        // SOUNDNESS (#3604 prerequisite): Left-operand negative transport
        // for reassociation once `b + c` has normalized to `subNatNat`.
        // This composes checked `Int.add_comm` with the full negative
        // right-operand transport `Int.add_subNatNat_negSucc`.
        self.register_int_add_negsucc_sub_nat_nat_proof()?;

        // Int.add_assoc_ofNat_succ_ofNat_negSucc :
        //   ∀ m n k : Nat,
        //     Eq (((ofNat (succ m)) + ofNat n) + negSucc k)
        //        ((ofNat (succ m)) + (ofNat n + negSucc k))
        //
        // SOUNDNESS (#3604 prerequisite): Positive outer / mixed
        // inner-negative branch of `Int.add_assoc`. This rewrites through
        // checked `Int.add_ofNat_succ_subNatNat` and checked `Nat.add_comm`
        // over the `Int.subNatNat` index.
        self.register_int_add_assoc_ofnat_succ_ofnat_negsucc_proof()?;

        // Int.add_assoc_negSucc_ofNat_succ_ofNat_succ :
        //   ∀ k m n : Nat,
        //     Eq ((negSucc k + ofNat (succ m)) + ofNat (succ n))
        //        (negSucc k + (ofNat (succ m) + ofNat (succ n)))
        //
        // SOUNDNESS (#3604 prerequisite): Negative outer / positive-positive
        // branch of `Int.add_assoc`. This transports checked
        // `Int.add_negSucc_ofNat_succ` through right addition and then uses
        // checked positive `Int.subNatNat` transport.
        self.register_int_add_assoc_negsucc_ofnat_succ_ofnat_succ_proof()?;

        // Int.add_assoc_negSucc_ofNat_succ_negSucc :
        //   ∀ k m n : Nat,
        //     Eq ((negSucc k + ofNat (succ m)) + negSucc n)
        //        (negSucc k + (ofNat (succ m) + negSucc n))
        //
        // SOUNDNESS (#3604 prerequisite): Negative outer / mixed
        // inner-negative branch of `Int.add_assoc`. This composes the
        // checked left/right `Int.subNatNat` transports and reconciles the
        // Nat index order with checked `Nat.add_succ` and `Nat.add_comm`.
        self.register_int_add_assoc_negsucc_ofnat_succ_negsucc_proof()?;

        // Int.add_assoc_ofNat :
        //   ∀ m n k : Nat,
        //     Eq ((ofNat m + ofNat n) + ofNat k)
        //        (ofNat m + (ofNat n + ofNat k))
        //
        // SOUNDNESS (#3604 prerequisite): All-positive branch of
        // `Int.add_assoc`. This lifts checked `Nat.add_assoc` through
        // `congrArg Int.ofNat` after definitional normalization of
        // `Int.add` on `Int.ofNat` operands.
        self.register_int_add_assoc_ofnat_proof()?;

        // Int.add_assoc_ofNat_succ_negSucc_ofNat_succ :
        //   ∀ m n k : Nat,
        //     Eq ((ofNat (succ m) + negSucc n) + ofNat (succ k))
        //        (ofNat (succ m) + (negSucc n + ofNat (succ k)))
        //
        // SOUNDNESS (#3604 prerequisite): Positive outer / mixed
        // inner-positive branch of `Int.add_assoc`. This composes checked
        // left/right `Int.subNatNat` transports and reconciles the Nat index
        // order with checked `Nat.add_succ` and `Nat.add_comm`.
        self.register_int_add_assoc_ofnat_succ_negsucc_ofnat_succ_proof()?;

        // Int.add_assoc_ofNat_succ_negSucc_negSucc :
        //   ∀ m n k : Nat,
        //     Eq ((ofNat (succ m) + negSucc n) + negSucc k)
        //        (ofNat (succ m) + (negSucc n + negSucc k))
        //
        // SOUNDNESS (#3604 prerequisite): Positive outer / negative-negative
        // branch of `Int.add_assoc`. This composes checked mixed-sign
        // normalization, checked negative `Int.subNatNat` transport, and
        // checked `Nat.add_succ` index transport.
        self.register_int_add_assoc_ofnat_succ_negsucc_negsucc_proof()?;

        // Int.add_assoc_negSucc_negSucc_negSucc :
        //   ∀ m n k : Nat,
        //     Eq ((negSucc m + negSucc n) + negSucc k)
        //        (negSucc m + (negSucc n + negSucc k))
        //
        // SOUNDNESS (#3604 prerequisite): All-negative branch of
        // `Int.add_assoc`. This lifts checked `Nat.succ_add`,
        // `Nat.add_assoc`, and `Nat.add_succ` through `Int.negSucc`.
        self.register_int_add_assoc_negsucc_negsucc_negsucc_proof()?;

        // Int.add_assoc_negSucc_negSucc_ofNat_succ :
        //   ∀ m n k : Nat,
        //     Eq ((negSucc m + negSucc n) + ofNat (succ k))
        //        (negSucc m + (negSucc n + ofNat (succ k)))
        //
        // SOUNDNESS (#3604 prerequisite): Negative-negative-positive branch
        // of `Int.add_assoc`. This composes checked mixed-sign normalization,
        // checked left `Int.subNatNat` transport, and checked `Nat.add_comm`
        // / `Nat.add_succ` index transport.
        self.register_int_add_assoc_negsucc_negsucc_ofnat_succ_proof()?;

        // Int.add_assoc_zero_right :
        //   ∀ a b : Int,
        //     Eq ((a + b) + 0) (a + (b + 0))
        //
        // SOUNDNESS (#3604 prerequisite): Right-zero branch of the remaining
        // `Int.add_assoc` split. It maps `(a + b) + 0` to `a + b` with
        // `Int.add_zero`, then transports `b + 0` to `b` under left addition.
        self.register_int_add_assoc_zero_right_proof()?;

        // Int.add_assoc_zero_middle :
        //   ∀ a c : Int,
        //     Eq ((a + 0) + c) (a + (0 + c))
        //
        // SOUNDNESS (#3604 prerequisite): Middle-zero branch of the
        // remaining `Int.add_assoc` split. It composes checked `Int.add_zero`
        // with checked `Int.zero_add` and transports both under addition.
        self.register_int_add_assoc_zero_middle_proof()?;

        // Int.add_assoc : ∀ a b c : Int, Eq ((a+b)+c) (a+(b+c))
        //
        // SOUNDNESS (#3604): Top-level nested `Int.rec` / `Nat.rec`
        // assembly dispatching to the checked zero/sign branch theorems
        // above. This replaces the previous inline `Declaration::Axiom`.
        self.register_int_add_assoc_proof()?;

        // Int.add_comm : ∀ a b : Int, Eq (Int.add a b) (Int.add b a)
        //
        // #3604: Converted from Declaration::Axiom to Declaration::Theorem.
        // Nested `@Int.rec.{0}` induction — outer on `a`, inner on `b` —
        // with four cases:
        //   (ofNat m, ofNat n): congrArg Int.ofNat (Nat.add_comm m n)
        //   (ofNat m, negSucc n): Eq.refl (subNatNat m (succ n)) [iota + delta]
        //   (negSucc m, ofNat n): Eq.refl (subNatNat n (succ m)) [iota + delta]
        //   (negSucc m, negSucc n): congrArg (λ x => negSucc (succ x)) (Nat.add_comm m n)
        self.register_int_add_comm_proof()?;

        // Int.add_right_cancel : ∀ a b c : Int, Eq (a + b) (c + b) → Eq a c
        //
        // #3604: Converted from Declaration::Axiom to Declaration::Theorem.
        // Purely algebraic (non-inductive) derivation: add `-b` to both sides
        // of the hypothesis and collapse via the right-cancellation identity
        // `Int.add_neg_cancel_right`. The proof chains
        //   s1 := Eq.symm (Int.add_neg_cancel_right a b)
        //   s2 := congrArg (\x => Int.add x (Int.neg b)) h
        //   s3 := Int.add_neg_cancel_right c b
        // via two `Eq.trans` steps. See `algebra_int_add_right_cancel_proof.rs`
        // for construction details. Depends on `Int.add_neg_cancel_right`
        // (constructive #3604); the resulting proof has empty domain-axiom
        // closure.
        self.register_int_add_right_cancel_proof()?;

        // Int.mul_left_cancel_ofNat_succ : ∀ n : Nat, ∀ a b : Int,
        //   Eq ((Int.ofNat (Nat.succ n)) * a) ((Int.ofNat (Nat.succ n)) * b) → Eq a b
        //
        // SOUNDNESS (#3604): Converted from Declaration::Axiom to
        // Declaration::Theorem. Nested `@Int.rec.{0}` (outer on `a`, inner on
        // `b`): the positive scalar `Int.ofNat (Nat.succ n)` preserves the
        // operand constructor under `Int.mul`, so the two same-sign leaves
        // reduce to a `Nat` magnitude equality discharged by the constructive
        // `Nat.mul_left_cancel_succ` (after `Int.noConfusion` injectivity, plus
        // `Nat.succ_inj` for the negSucc leaf) and re-lifted by `congrArg`,
        // while the two mixed-sign leaves are impossible equalities discharged
        // directly by `Int.noConfusion`. See
        // `algebra_int_mul_left_cancel_ofnat_succ_proof.rs`. Every feeder is a
        // #3604 Theorem or generated reducible definition, so the closure is
        // empty.
        self.register_int_mul_left_cancel_ofnat_succ_proof()?;

        // Int.zero_add : ∀ a : Int, Eq (0 + a) a
        //
        // SOUNDNESS (#3604 prerequisite): Real kernel-checked zero-left
        // addition theorem. It composes `Int.add_comm` with `Int.add_zero`,
        // removing the zero-left reassociation blocker for `Int.add_assoc`.
        self.register_int_zero_add_proof()?;

        // Int.add_assoc_zero_left :
        //   ∀ b c : Int, Eq ((0 + b) + c) (0 + (b + c))
        //
        // SOUNDNESS (#3604 prerequisite): Zero-left final-case theorem for
        // the remaining `Int.add_assoc` split. It maps `Int.zero_add b`
        // through right addition and composes with symmetric
        // `Int.zero_add (b + c)`.
        self.register_int_add_assoc_zero_left_proof()?;

        // Int.add_neg_self : ∀ a : Int, Eq (a + (-a)) 0
        //
        // SOUNDNESS (#3604): Converted from Declaration::Axiom to
        // Declaration::Theorem. Outer `@Int.rec.{0}` case-analysis on `a`;
        // the `ofNat` branch recurses with an inner `@Nat.rec.{0}` (zero
        // closes by `@Eq.refl.{1}`, succ by `Int.subNatNat_self (succ k)`),
        // and the `negSucc` branch closes by `Int.subNatNat_self (succ m)`.
        // The kernel reduces `Int.add a (Int.neg a)` to
        // `Int.subNatNat (succ ·) (succ ·)` on the non-zero constructor
        // branches via iota + delta. See `algebra_int_add_neg_self_proof.rs`
        // (and its dependency `algebra_int_sub_nat_nat_self_proof.rs`). Empty
        // domain-axiom closure.
        self.register_int_add_neg_self_proof()?;

        // Int.neg_add_self : ∀ a : Int, Eq ((-a) + a) 0
        //
        // SOUNDNESS (#3604): Converted from Declaration::Axiom to
        // Declaration::Theorem. Mirrors `Int.add_neg_self` with the addends
        // swapped; same nested `@Int.rec.{0}` / `@Nat.rec.{0}` shape closing
        // via `Int.subNatNat_self`. See `algebra_int_neg_add_self_proof.rs`.
        // Empty domain-axiom closure.
        self.register_int_neg_add_self_proof()?;

        // Int.mul_comm : ∀ a b : Int, Eq (a*b) (b*a)
        //
        // #3604: Converted from Declaration::Axiom to Declaration::Theorem.
        // Nested `@Int.rec.{0}` induction — outer on `a`, inner on `b` —
        // with four cases, each lifting `Nat.mul_comm` through
        // `Int.ofNat` / `Int.negOfNat` via `congrArg`:
        //   (ofNat m, ofNat n):   congrArg Int.ofNat    (Nat.mul_comm m n)
        //   (ofNat m, negSucc n): congrArg Int.negOfNat (Nat.mul_comm m (succ n))
        //   (negSucc m, ofNat n): congrArg Int.negOfNat (Nat.mul_comm (succ m) n)
        //   (negSucc m, negSucc n): congrArg Int.ofNat  (Nat.mul_comm (succ m) (succ n))
        // See `algebra_int_mul_comm_proof.rs` for details. Depends on
        // `Nat.mul_comm` (constructive #3604); the resulting proof has
        // empty domain-axiom closure.
        self.register_int_mul_comm_proof()?;

        // Int.mul_assoc : ∀ a b c : Int, Eq ((a*b)*c) (a*(b*c))
        //
        // SOUNDNESS (#3604): Converted from Declaration::Axiom to
        // Declaration::Theorem. Triple nested `@Int.rec.{0}` (outer on `a`,
        // then `b`, then `c`) with eight constructor leaves. Each leaf
        // normalizes both `(a*b)*c` and `a*(b*c)` to a common net-signed
        // `Int.ofNat` magnitude product via the constructive sign lemmas
        // `Int.neg_mul_left` / `Int.neg_mul_right` / `Int.neg_neg`, then
        // closes the residual magnitude goal with `Nat.mul_assoc` lifted
        // through the shared (sign ∘ Int.ofNat) wrapper by `congrArg`. See
        // `algebra_int_mul_assoc_proof.rs`. All feeders are #3604 Theorems
        // with empty domain-axiom closure, so `Int.mul_assoc` has empty
        // closure too.
        self.register_int_mul_assoc_proof()?;

        // Int.mul_one : ∀ a : Int, Eq (a * 1) a
        //
        // SOUNDNESS (#3604): Converted from Declaration::Axiom to
        // Declaration::Theorem. Single `@Int.rec.{0}` case-analysis on `a`,
        // each branch lifting constructive `Nat.mul_one` through
        // `Int.ofNat` / `Int.negOfNat` via `congrArg`. See
        // `algebra_int_mul_one_proof.rs`. Empty domain-axiom closure.
        self.register_int_mul_one_proof()?;

        // Int.one_mul : ∀ a : Int, Eq (1 * a) a
        //
        // SOUNDNESS (#3604): Converted from Declaration::Axiom to
        // Declaration::Theorem. Single `@Int.rec.{0}` case-analysis on `a`,
        // each branch lifting constructive `Nat.one_mul` through
        // `Int.ofNat` / `Int.negOfNat` via `congrArg`. See
        // `algebra_int_one_mul_proof.rs`. Empty domain-axiom closure.
        self.register_int_one_mul_proof()?;

        // Int.mul_zero : ∀ a : Int, Eq (a * 0) 0
        //
        // SOUNDNESS (#3604): Converted from Declaration::Axiom to
        // Declaration::Theorem. Single `@Int.rec.{0}` case-analysis on `a`;
        // both branches close by pure `@Eq.refl.{1} Int Int.zero` because
        // `Int.mul a Int.zero` reduces to `Int.zero` via iota on the inner
        // `Nat.rec` (Nat.mul zero-case) + iota on `Int.negOfNat`. See
        // `algebra_int_mul_zero_proof.rs`. Empty domain-axiom closure.
        self.register_int_mul_zero_proof()?;

        // Int.zero_mul : ∀ a : Int, Eq (0 * a) 0
        //
        // SOUNDNESS (#3604): Converted from Declaration::Axiom to
        // Declaration::Theorem. Single `@Int.rec.{0}` case-analysis on `a`,
        // each branch lifting constructive `Nat.zero_mul` through
        // `Int.ofNat` / `Int.negOfNat` via `congrArg`. See
        // `algebra_int_zero_mul_proof.rs`. Empty domain-axiom closure.
        self.register_int_zero_mul_proof()?;

        // Int.left_distrib : ∀ a b c : Int, Eq (a*(b+c)) (a*b + a*c)
        //
        // SOUNDNESS (#3604): Converted from Declaration::Axiom to
        // Declaration::Theorem. Triple nested `@Int.rec.{0}` (outer on `a`,
        // then `b`, then `c`) with eight constructor leaves; the same-sign
        // leaves lift `Nat.left_distrib` through `Int.ofNat` / `Int.negOfNat`
        // and the mixed-sign leaves cross the normalized `Int.subNatNat` via
        // the constructive multiplication-over-truncated-subtraction lemmas
        // `Int.ofNat_mul_subNatNat` / `Int.negSucc_mul_subNatNat` plus
        // `Int.subNatNat_eq_add` / `Int.add_comm` / `Int.negOfNat_add`. See
        // `algebra_int_left_distrib_proof.rs` (and its helper proofs
        // `algebra_int_{ofnat,negsucc}_mul_sub_nat_nat_proof.rs`,
        // `algebra_int_sub_nat_nat_{zero_left,add_add}_proof.rs`,
        // `algebra_int_negofnat_add_proof.rs`). Empty domain-axiom closure.
        self.register_int_left_distrib_proof()?;

        // Int.right_distrib : ∀ a b c : Int, Eq ((a+b)*c) (a*c + b*c)
        //
        // SOUNDNESS (#3604): Converted from Declaration::Axiom to
        // Declaration::Theorem. Composes the constructive `Int.left_distrib`
        // with `Int.mul_comm` via a four-step `Eq.trans` / `congrArg` chain
        // (no fresh induction). See `algebra_int_right_distrib_proof.rs`.
        // Empty domain-axiom closure.
        self.register_int_right_distrib_proof()?;

        // Int.neg_neg : ∀ a : Int, Eq (-(-a)) a
        //
        // SOUNDNESS (#3604): Converted from Declaration::Axiom to
        // Declaration::Theorem. Outer `@Int.rec.{0}` case-analysis on `a`;
        // the `negSucc` branch closes by pure `@Eq.refl.{1}` and the
        // `ofNat` branch by an inner `@Nat.rec.{0}` (both branches pure
        // `@Eq.refl.{1}`, inductive hypothesis unused) because
        // `Int.neg (Int.neg ·)` reduces to the identity on each constructor
        // via iota + delta on the reducible `Int.neg`. See
        // `algebra_int_neg_neg_proof.rs`. Empty domain-axiom closure.
        self.register_int_neg_neg_proof()?;

        // Int.neg_subNatNat : ∀ m n : Nat,
        //   Eq (Int.neg (Int.subNatNat m n)) (Int.subNatNat n m)
        //
        // SOUNDNESS (#3604 prerequisite): Real kernel-checked normalization
        // theorem `-(m - n) = n - m` over the mixed-sign `Int.subNatNat`
        // substrate. Proven by nested `@Nat.rec.{0}` (outer on `m`, inner on
        // `n`); three constructor corners close by pure `@Eq.refl.{1}` and the
        // (succ, succ) corner by the outer induction hypothesis. The key local
        // lemma behind the constructive `Int.neg_add`. See
        // `algebra_int_neg_sub_nat_nat_proof.rs`. Empty domain-axiom closure.
        self.register_int_neg_sub_nat_nat_proof()?;

        // Int.neg_add : ∀ a b : Int, Eq (-(a+b)) ((-a)+(-b))
        //
        // SOUNDNESS (#3604): Converted from Declaration::Axiom to
        // Declaration::Theorem. Nested `@Int.rec.{0}` (outer on `a`, inner on
        // `b`) with `@Nat.rec.{0}` splits on the underlying `Nat` wherever
        // `Int.neg (Int.ofNat _)` is otherwise stuck. The four `Int.add`
        // constructor cases reduce `Int.neg (Int.add a b)` and
        // `Int.add (Int.neg a) (Int.neg b)` to `Int.subNatNat` /
        // `Int.ofNat` / `Int.negSucc` forms closed by the constructive
        // `Int.neg_subNatNat`, `Int.subNatNat_zero_succ`, `Nat.zero_add`,
        // `Nat.succ_add` glued with `congrArg` / `Eq.symm` / `Eq.trans` /
        // `Eq.refl`. See `algebra_int_neg_add_proof.rs`. Empty domain-axiom
        // closure.
        self.register_int_neg_add_proof()?;

        // Int.neg_mul_left : ∀ a b : Int, Eq (-(a*b)) ((-a)*b)
        //
        // SOUNDNESS (#3604): Converted from Declaration::Axiom to
        // Declaration::Theorem. Nested `@Int.rec.{0}` induction (outer on
        // `a`, inner on `b`); the outer `ofNat` case further splits the
        // underlying `Nat` via `@Nat.rec.{0}` so `Int.neg (Int.ofNat m)`
        // reduces to a constructor and the right-hand `Int.mul` fires. Two
        // inline `@Nat.rec.{0}` helper lemmas (both branches pure
        // `@Eq.refl.{1}`) discharge the constructor-form leaves; the two
        // `a = ofNat 0` leaves transport `@Eq.refl.{1} Int (ofNat 0)` along
        // the constructive `Nat.zero_mul` via `@Eq.subst.{1}`. See
        // `algebra_int_neg_mul_left_proof.rs`. Empty domain-axiom closure.
        self.register_int_neg_mul_left_proof()?;

        // Int.neg_mul_right : ∀ a b : Int, Eq (-(a*b)) (a*(-b))
        //
        // SOUNDNESS (#3604): Converted from Declaration::Axiom to
        // Declaration::Theorem. Nested `@Int.rec.{0}` induction (outer on
        // `b`, inner on `a`); the outer `ofNat` case further splits the
        // underlying `Nat` via `@Nat.rec.{0}` so `Int.neg (Int.ofNat n)`
        // reduces to a constructor and the right-hand `Int.mul a (Int.neg b)`
        // fires. Two inline `@Nat.rec.{0}` helper lemmas (both branches pure
        // `@Eq.refl.{1}`) discharge the `b ≠ ofNat 0` leaves; the
        // `b = ofNat 0` leaves close by pure `@Eq.refl.{1}` (`Nat.mul _ 0`
        // reduces definitionally). See `algebra_int_neg_mul_right_proof.rs`.
        // Empty domain-axiom closure.
        self.register_int_neg_mul_right_proof()?;

        // Int.sub_self : ∀ a : Int, Eq (a - a) 0
        //
        // SOUNDNESS (#3604): Converted from Declaration::Axiom to
        // Declaration::Theorem. Proof term `λ a => Int.add_neg_self a`;
        // `Int.sub a a` reduces to `Int.add a (Int.neg a)` by delta on the
        // reducible `Int.sub` definition + beta, making the goal
        // definitionally equal to the type of the constructive
        // `Int.add_neg_self a`. See `algebra_int_sub_self_proof.rs`. Empty
        // domain-axiom closure.
        self.register_int_sub_self_proof()?;

        // Int.sub_eq_add_neg : ∀ a b : Int, Eq (Int.sub a b) (Int.add a (Int.neg b))
        // Key lemma for ring normalization: rewrites subtraction as addition + negation.
        // Part of #3368.
        //
        // SOUNDNESS (#3604): Converted from Declaration::Axiom to
        // Declaration::Theorem. Pure `@Eq.refl.{1} Int (Int.sub a b)`; the
        // conclusion's two sides are definitionally equal because `Int.sub`
        // is the reducible Definition `λ m n => Int.add m (Int.neg n)`, so
        // `Int.sub a b` reduces to `Int.add a (Int.neg b)` by delta + beta.
        // See `algebra_int_sub_eq_add_neg_proof.rs`. Empty domain-axiom
        // closure.
        self.register_int_sub_eq_add_neg_proof()?;

        // Int.add_neg_cancel_right : ∀ a b : Int, Eq (Int.add (Int.add a b) (Int.neg b)) a
        // Part of #3368.
        //
        // SOUNDNESS (#3604): Converted from Declaration::Axiom to
        // Declaration::Theorem. Proof term is a two-step `Eq.trans` chain over
        // the constructive `Int.add_assoc`, `Int.add_neg_self` (transported
        // through `Int.add a ·` by `congrArg`), and `Int.add_zero` — no
        // recursion of its own. All three feeders are #3604 Theorems with
        // empty domain-axiom closure, so `Int.add_neg_cancel_right` has empty
        // closure too. See `algebra_int_add_neg_cancel_right_proof.rs`.
        self.register_int_add_neg_cancel_right_proof()?;

        self.int_arith_lemmas_init = true;
        Ok(())
    }

    /// Check if Int arithmetic lemmas have been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_int_arith_lemmas` has completed successfully
    /// ENSURES: Pure - no side effects
    #[allow(dead_code)]
    pub(crate) fn has_int_arith_lemmas(&self) -> bool {
        self.int_arith_lemmas_init
    }

    /// Initialize Int/Nat conversion lemmas
    ///
    /// These lemmas connect Int.ofNat/Int.toNat with Nat arithmetic (all
    /// kernel-checked `Declaration::Theorem`s; the former #3551 axioms were
    /// promoted to constructive proofs):
    /// - `Int.toNat_ofNat` : ∀ n : Nat, Eq (Int.toNat (Int.ofNat n)) n
    /// - `Int.ofNat_add`  : ∀ m n : Nat, Eq (Int.ofNat (Nat.add m n)) (Int.add (Int.ofNat m) (Int.ofNat n))
    /// - `Int.ofNat_mul`  : ∀ m n : Nat, Eq (Int.ofNat (Nat.mul m n)) (Int.mul (Int.ofNat m) (Int.ofNat n))
    /// - `Nat.succ_eq_add_one` : ∀ n : Nat, Eq (Nat.succ n) (Nat.add n (Nat.succ Nat.zero))
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_nat_conv_lemmas_init == true`
    /// ENSURES: On success, required dependencies (`int_arith`, `nat`, `eq`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[allow(dead_code)]
    pub(crate) fn init_int_nat_conv_lemmas(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): the Int arithmetic
        // stub cluster is suppressed in import mode (see `init_int_arith`);
        // these lemmas state/prove properties of the suppressed stubs, so
        // they are suppressed with them (the genuine olean lemmas import).
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.int_nat_conv_lemmas_init {
            return Ok(());
        }

        // Ensure arithmetic primitives are available (required by each
        // per-theorem `register_*_proof` helper below).
        self.init_int_arith()?; // Provides Int.ofNat, Int.add, Int.mul, Int.toNat
        self.init_nat()?; // Provides Nat.add, Nat.mul, Nat.succ, Nat.zero
        self.init_eq()?; // Provides Eq

        // Int.toNat_ofNat : ∀ n : Nat, Eq (Int.toNat (Int.ofNat n)) n
        //
        // SOUNDNESS (#3551 Tier A Int batch): Real kernel-checked proof
        // with pure `@Eq.refl.{1} Nat n` body (see
        // `algebra_int_tonat_ofnat_proof.rs`). The kernel reduces
        // `Int.toNat (Int.ofNat n)` to `n` by iota on `Int.rec` (ofNat
        // case) + delta on the reducible `Int.toNat` definition +
        // beta on the `(λ n' => n') n` application. Demoting from
        // Declaration::Axiom to Declaration::Theorem; axiom count
        // decreases by 1.
        self.register_int_tonat_ofnat_proof()?;

        // Int.ofNat_add : ∀ m n : Nat, Eq (Int.ofNat (Nat.add m n)) (Int.add (Int.ofNat m) (Int.ofNat n))
        //
        // SOUNDNESS (#3551 Tier A Int batch): Real kernel-checked proof
        // with pure `@Eq.refl.{1} Int (Int.ofNat (Nat.add m n))` body
        // (see `algebra_int_ofnat_add_proof.rs`). The kernel reduces
        // `Int.add (Int.ofNat m) (Int.ofNat n)` to
        // `Int.ofNat (Nat.add m n)` by iota on `Int.rec` (ofNat case
        // on both arguments) + delta on the reducible `Int.add`
        // definition. Demoting from Declaration::Axiom to
        // Declaration::Theorem; axiom count decreases by 1.
        self.register_int_ofnat_add_proof()?;

        // Int.ofNat_mul : ∀ m n : Nat, Eq (Int.ofNat (Nat.mul m n)) (Int.mul (Int.ofNat m) (Int.ofNat n))
        // SOUNDNESS (#3551): Real kernel-checked proof with pure
        // `@Eq.refl.{1} Int (Int.ofNat (Nat.mul m n))` body (see
        // `algebra_int_ofnat_mul_proof.rs`). The kernel reduces
        // `Int.mul (Int.ofNat m) (Int.ofNat n)` to
        // `Int.ofNat (Nat.mul m n)` by iota on `Int.rec` (ofNat case on
        // both arguments) + delta on the reducible `Int.mul`
        // definition. Demoting from Declaration::Axiom to
        // Declaration::Theorem; axiom count decreases by 1.
        self.register_int_ofnat_mul_proof()?;

        // Nat.succ_eq_add_one : ∀ n : Nat, Eq (Nat.succ n) (Nat.add n (Nat.succ Nat.zero))
        //
        // SOUNDNESS (#3551 Tier A Int batch): Real kernel-checked proof
        // with pure `@Eq.refl.{1} Nat (Nat.succ n)` body (see
        // `algebra_nat_succ_eq_add_one_proof.rs`). The kernel reduces
        // `Nat.add n (Nat.succ Nat.zero)` to `Nat.succ n` by iota on
        // `Nat.rec` (succ case + zero case) + delta on the reducible
        // `Nat.add` definition. Demoting from Declaration::Axiom to
        // Declaration::Theorem; axiom count decreases by 1.
        self.register_nat_succ_eq_add_one_proof()?;

        self.int_nat_conv_lemmas_init = true;
        Ok(())
    }

    /// Check if Int/Nat conversion lemmas have been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_int_nat_conv_lemmas` has completed successfully
    /// ENSURES: Pure - no side effects
    #[allow(dead_code)]
    pub(crate) fn has_int_nat_conv_lemmas(&self) -> bool {
        self.int_nat_conv_lemmas_init
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};

    /// After the full `init_int_arith_lemmas` pass, the four Int
    /// multiplication-identity lemmas demoted in #3604 are registered as
    /// constructive `Declaration::Theorem`s (not `Axiom`s) with proof
    /// values retained. Mirrors the per-module
    /// `test_int_mul_*_registered_as_theorem` checks, but exercises the
    /// real `init_int_arith_lemmas` registration site (the literal target
    /// of the unit's verify command).
    #[test]
    fn test_init_int_arith_lemmas_mul_identities_registered_as_theorems() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("init_int_arith_lemmas should succeed");
        for lemma in ["Int.mul_one", "Int.one_mul", "Int.mul_zero", "Int.zero_mul"] {
            let info = env
                .get_const(&Name::from_string(lemma))
                .unwrap_or_else(|| panic!("{lemma} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{lemma} must be a constructive Theorem, not an Axiom"
            );
            assert!(
                info.value.is_some(),
                "{lemma} Theorem must retain its proof value"
            );
        }
    }

    /// Each demoted Int multiplication-identity lemma has an empty
    /// transitive domain-axiom closure (the #3604 soundness contract for a
    /// genuine constructive proof). Guards against the axiom-wrapping
    /// masquerade and against a feeder lemma silently reintroducing a
    /// domain axiom.
    #[test]
    fn test_init_int_arith_lemmas_mul_identities_axiom_deps_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("init_int_arith_lemmas should succeed");
        for lemma in ["Int.mul_one", "Int.one_mul", "Int.mul_zero", "Int.zero_mul"] {
            let deps = env
                .axiom_deps(&Name::from_string(lemma))
                .unwrap_or_else(|| panic!("{lemma} is registered, axiom_deps should be Some"));
            let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                domain_deps.is_empty(),
                "{lemma} must have empty domain-axiom closure (constructive proof), got {domain_deps:?}"
            );
            let quality = env
                .proof_quality(&Name::from_string(lemma))
                .unwrap_or_else(|| panic!("{lemma} proof_quality should be reported"));
            assert!(
                matches!(quality, ProofQuality::Constructive),
                "{lemma} must be ProofQuality::Constructive, got {quality:?}"
            );
        }
    }

    /// After the full `init_int_arith_lemmas` pass, the two Int identities
    /// demoted in this batch (`Int.neg_neg`, `Int.sub_eq_add_neg`) are
    /// registered as constructive `Declaration::Theorem`s (not `Axiom`s)
    /// with proof values retained. Exercises the real
    /// `init_int_arith_lemmas` registration site (the literal target of the
    /// unit's verify command).
    #[test]
    fn test_init_int_arith_lemmas_neg_sub_identities_registered_as_theorems() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("init_int_arith_lemmas should succeed");
        for lemma in ["Int.neg_neg", "Int.sub_eq_add_neg"] {
            let info = env
                .get_const(&Name::from_string(lemma))
                .unwrap_or_else(|| panic!("{lemma} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{lemma} must be a constructive Theorem, not an Axiom"
            );
            assert!(
                info.value.is_some(),
                "{lemma} Theorem must retain its proof value"
            );
        }
    }

    /// Each Int identity demoted in this batch has an empty transitive
    /// domain-axiom closure (the #3604 soundness contract for a genuine
    /// constructive proof). Guards against the axiom-wrapping masquerade
    /// and against a feeder lemma silently reintroducing a domain axiom.
    #[test]
    fn test_init_int_arith_lemmas_neg_sub_identities_axiom_deps_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("init_int_arith_lemmas should succeed");
        for lemma in ["Int.neg_neg", "Int.sub_eq_add_neg"] {
            let deps = env
                .axiom_deps(&Name::from_string(lemma))
                .unwrap_or_else(|| panic!("{lemma} is registered, axiom_deps should be Some"));
            let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                domain_deps.is_empty(),
                "{lemma} must have empty domain-axiom closure (constructive proof), got {domain_deps:?}"
            );
            let quality = env
                .proof_quality(&Name::from_string(lemma))
                .unwrap_or_else(|| panic!("{lemma} proof_quality should be reported"));
            assert!(
                matches!(quality, ProofQuality::Constructive),
                "{lemma} must be ProofQuality::Constructive, got {quality:?}"
            );
        }
    }

    /// After the full `init_int_arith_lemmas` pass, the two Int
    /// distributivity laws demoted in this batch (`Int.left_distrib`,
    /// `Int.right_distrib`) are registered as constructive
    /// `Declaration::Theorem`s (not `Axiom`s) with proof values retained.
    /// Exercises the real `init_int_arith_lemmas` registration site (the
    /// literal target of the unit's verify command).
    #[test]
    fn test_init_int_arith_lemmas_distrib_registered_as_theorems() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("init_int_arith_lemmas should succeed");
        for lemma in ["Int.left_distrib", "Int.right_distrib"] {
            let info = env
                .get_const(&Name::from_string(lemma))
                .unwrap_or_else(|| panic!("{lemma} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{lemma} must be a constructive Theorem, not an Axiom"
            );
            assert!(
                info.value.is_some(),
                "{lemma} Theorem must retain its proof value"
            );
        }
    }

    /// Each Int distributivity law demoted in this batch has an empty
    /// transitive domain-axiom closure (the #3604 soundness contract for a
    /// genuine constructive proof). Guards against the axiom-wrapping
    /// masquerade and against a feeder lemma (the
    /// multiplication-over-truncated-subtraction helpers, `Int.add_comm`,
    /// `Int.mul_comm`, `Nat.left_distrib`, ...) silently reintroducing a
    /// domain axiom.
    #[test]
    fn test_init_int_arith_lemmas_distrib_axiom_deps_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("init_int_arith_lemmas should succeed");
        for lemma in ["Int.left_distrib", "Int.right_distrib"] {
            let deps = env
                .axiom_deps(&Name::from_string(lemma))
                .unwrap_or_else(|| panic!("{lemma} is registered, axiom_deps should be Some"));
            let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                domain_deps.is_empty(),
                "{lemma} must have empty domain-axiom closure (constructive proof), got {domain_deps:?}"
            );
            let quality = env
                .proof_quality(&Name::from_string(lemma))
                .unwrap_or_else(|| panic!("{lemma} proof_quality should be reported"));
            assert!(
                matches!(quality, ProofQuality::Constructive),
                "{lemma} must be ProofQuality::Constructive, got {quality:?}"
            );
        }
    }

    /// After the full `init_int_arith_lemmas` pass, the three additive-inverse
    /// identities demoted in this batch (`Int.add_neg_self`,
    /// `Int.neg_add_self`, `Int.sub_self`) are registered as constructive
    /// `Declaration::Theorem`s (not `Axiom`s) with proof values retained.
    /// Exercises the real `init_int_arith_lemmas` registration site (the
    /// literal target of the unit's verify command).
    #[test]
    fn test_init_int_arith_lemmas_inverse_identities_registered_as_theorems() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("init_int_arith_lemmas should succeed");
        for lemma in ["Int.add_neg_self", "Int.neg_add_self", "Int.sub_self"] {
            let info = env
                .get_const(&Name::from_string(lemma))
                .unwrap_or_else(|| panic!("{lemma} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{lemma} must be a constructive Theorem, not an Axiom"
            );
            assert!(
                info.value.is_some(),
                "{lemma} Theorem must retain its proof value"
            );
        }
    }

    /// Each additive-inverse identity demoted in this batch has an empty
    /// transitive domain-axiom closure (the #3604 soundness contract for a
    /// genuine constructive proof). Guards against the axiom-wrapping
    /// masquerade and against a feeder lemma (`Int.subNatNat_self`,
    /// `Int.subNatNat_succ_succ`) silently reintroducing a domain axiom.
    #[test]
    fn test_init_int_arith_lemmas_inverse_identities_axiom_deps_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("init_int_arith_lemmas should succeed");
        for lemma in ["Int.add_neg_self", "Int.neg_add_self", "Int.sub_self"] {
            let deps = env
                .axiom_deps(&Name::from_string(lemma))
                .unwrap_or_else(|| panic!("{lemma} is registered, axiom_deps should be Some"));
            let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                domain_deps.is_empty(),
                "{lemma} must have empty domain-axiom closure (constructive proof), got {domain_deps:?}"
            );
            let quality = env
                .proof_quality(&Name::from_string(lemma))
                .unwrap_or_else(|| panic!("{lemma} proof_quality should be reported"));
            assert!(
                matches!(quality, ProofQuality::Constructive),
                "{lemma} must be ProofQuality::Constructive, got {quality:?}"
            );
        }
    }

    /// After the full `init_int_arith_lemmas` pass, the negation-distributes
    /// lemma `Int.neg_add` and its helper `Int.neg_subNatNat` demoted in this
    /// batch (#3604) are registered as constructive `Declaration::Theorem`s
    /// (not `Axiom`s) with proof values retained. Exercises the real
    /// `init_int_arith_lemmas` registration site (the literal target of the
    /// unit's verify command).
    #[test]
    fn test_init_int_arith_lemmas_neg_add_registered_as_theorems() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("init_int_arith_lemmas should succeed");
        for lemma in ["Int.neg_add", "Int.neg_subNatNat"] {
            let info = env
                .get_const(&Name::from_string(lemma))
                .unwrap_or_else(|| panic!("{lemma} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{lemma} must be a constructive Theorem, not an Axiom"
            );
            assert!(
                info.value.is_some(),
                "{lemma} Theorem must retain its proof value"
            );
        }
    }

    /// `Int.neg_add` and `Int.neg_subNatNat` each have an empty transitive
    /// domain-axiom closure (the #3604 soundness contract for a genuine
    /// constructive proof). Guards against the axiom-wrapping masquerade and
    /// against a feeder lemma silently reintroducing a domain axiom.
    #[test]
    fn test_init_int_arith_lemmas_neg_add_axiom_deps_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("init_int_arith_lemmas should succeed");
        for lemma in ["Int.neg_add", "Int.neg_subNatNat"] {
            let deps = env
                .axiom_deps(&Name::from_string(lemma))
                .unwrap_or_else(|| panic!("{lemma} is registered, axiom_deps should be Some"));
            let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                domain_deps.is_empty(),
                "{lemma} must have empty domain-axiom closure (constructive proof), got {domain_deps:?}"
            );
            let quality = env
                .proof_quality(&Name::from_string(lemma))
                .unwrap_or_else(|| panic!("{lemma} proof_quality should be reported"));
            assert!(
                matches!(quality, ProofQuality::Constructive),
                "{lemma} must be ProofQuality::Constructive, got {quality:?}"
            );
        }
    }
}
