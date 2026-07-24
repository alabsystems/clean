// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nat arithmetic lemmas initialization for Environment
//!
//! Split from data_types_arithmetic.rs (#307):
//! - data_types_arithmetic.rs: Int operations (init_int_arith, init_int_sign_abs)
//! - data_types_int_lemmas.rs: Int lemmas + Int/Nat conversion lemmas
//! - data_types_nat_lemmas.rs: Nat arithmetic lemmas (this file)

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Nat arithmetic lemmas (commutativity, associativity, identities, distributivity)
    ///
    /// These are the fundamental properties of Nat as a commutative semiring.
    /// Unlike Int (which is a ring with negation), Nat only has addition and multiplication,
    /// no subtraction inverse, so we don't have add_neg_self or similar.
    ///
    /// Lemmas added:
    /// - `Nat.add_comm` : ∀ a b : Nat, Eq (Nat.add a b) (Nat.add b a)
    /// - `Nat.add_assoc` : ∀ a b c : Nat, Eq (Nat.add (Nat.add a b) c) (Nat.add a (Nat.add b c))
    /// - `Nat.add_right_cancel` : ∀ {n m k : Nat}, Eq (Nat.add n m) (Nat.add k m) → Eq n k
    /// - `Nat.add_zero` : ∀ a : Nat, Eq (Nat.add a Nat.zero) a
    /// - `Nat.zero_add` : ∀ a : Nat, Eq (Nat.add Nat.zero a) a
    /// - `Nat.mul_comm` : ∀ a b : Nat, Eq (Nat.mul a b) (Nat.mul b a)
    /// - `Nat.mul_assoc` : ∀ a b c : Nat, Eq (Nat.mul (Nat.mul a b) c) (Nat.mul a (Nat.mul b c))
    /// - `Nat.mul_left_cancel_succ` : ∀ n a b : Nat, Eq (Nat.mul (Nat.succ n) a) (Nat.mul (Nat.succ n) b) → Eq a b
    /// - `Nat.mul_one` : ∀ a : Nat, Eq (Nat.mul a (Nat.succ Nat.zero)) a
    /// - `Nat.one_mul` : ∀ a : Nat, Eq (Nat.mul (Nat.succ Nat.zero) a) a
    /// - `Nat.mul_zero` : ∀ a : Nat, Eq (Nat.mul a Nat.zero) Nat.zero
    /// - `Nat.zero_mul` : ∀ a : Nat, Eq (Nat.mul Nat.zero a) Nat.zero
    /// - `Nat.left_distrib` : ∀ a b c : Nat, Eq (Nat.mul a (Nat.add b c)) (Nat.add (Nat.mul a b) (Nat.mul a c))
    /// - `Nat.right_distrib` : ∀ a b c : Nat, Eq (Nat.mul (Nat.add a b) c) (Nat.add (Nat.mul a c) (Nat.mul b c))
    /// - `Nat.succ_add` : ∀ a b : Nat, Eq (Nat.add (Nat.succ a) b) (Nat.succ (Nat.add a b))
    /// - `Nat.add_succ` : ∀ a b : Nat, Eq (Nat.add a (Nat.succ b)) (Nat.succ (Nat.add a b))
    /// - `Nat.succ_mul` : ∀ a b : Nat, Eq (Nat.mul (Nat.succ a) b) (Nat.add b (Nat.mul a b))
    /// - `Nat.mul_succ` : ∀ a b : Nat, Eq (Nat.mul a (Nat.succ b)) (Nat.add a (Nat.mul a b))
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_arith_lemmas_init == true`
    /// ENSURES: On success, required dependencies (`nat`, `eq`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_nat_arith_lemmas(&mut self) -> Result<(), EnvError> {
        // SOUNDNESS: import-mode Nat core arithmetic cluster gate — every lemma
        // here is stated over the import-gated Nat.add/Nat.mul seeds (see
        // data_types_nat.rs::init_nat); the genuine olean lemma web imports
        // through the checked path instead. Default lane byte-identical.
        if self.suppress_lossy_structure_stubs {
            self.nat_arith_lemmas_init = true;
            return Ok(());
        }
        if self.nat_arith_lemmas_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat()?; // Provides Nat.add, Nat.mul, Nat.zero, Nat.succ
        self.init_eq()?; // Provides Eq

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        // Helper: Nat 1 = Nat.succ Nat.zero
        // Retained for use by future Nat arithmetic axiom demotions
        // (#3551 follow-ups); the current Nat.mul_one / Nat.one_mul
        // proofs build their own `nat_one` inside the proof modules.
        let _nat_one = Expr::app(nat_succ.clone(), nat_zero.clone());

        // Helper: build Eq Nat lhs rhs
        let mk_nat_eq =
            |lhs: Expr, rhs: Expr| Expr::apps(eq_const.clone(), [nat_const.clone(), lhs, rhs]);

        // All Nat arithmetic lemmas built with EnvDeclBuilder (#1444)

        // Nat.add_comm : ∀ a b : Nat, Eq (a+b) (b+a)
        //
        // #3604: Converted from Declaration::Axiom to Declaration::Theorem.
        // Induction on the second argument `b` via `Nat.rec.{0}`. Base case
        // closed by `Eq.symm (Nat.zero_add a)` (motive at Nat.zero reduces
        // via iota zero-case + delta on Nat.add). Step case composes
        // `congrArg Nat.succ ih` with `Eq.symm (Nat.succ_add k a)` via
        // `Eq.trans`. See `algebra_nat_add_comm_proof.rs` for construction
        // details. Depends on `Nat.zero_add` and `Nat.succ_add` (both
        // constructive #3604); the resulting proof has empty domain-axiom
        // closure.
        // #35: skip if already registered (e.g. when init runs after a prelude
        // that already seeded `Nat.add_comm`) so the call is idempotent and does
        // not duplicate-abort before the mul/distrib lemmas below.
        if self.get_const(&Name::from_string("Nat.add_comm")).is_none() {
            self.register_nat_add_comm_proof()?;
        }

        // Nat.add_assoc : ∀ a b c : Nat, Eq ((a+b)+c) (a+(b+c))
        //
        // #3551 Tier A Batch 5: Converted from Declaration::Axiom to
        // Declaration::Theorem. Induction on the third argument `c` via
        // `Nat.rec.{0}`. Base case closed by `@Eq.refl.{1} Nat (Nat.add a b)`
        // (motive at Nat.zero reduces both sides to `Nat.add a b` via iota
        // zero-case + delta on Nat.add). Step case closed by
        // `congrArg Nat.succ ih`. See `algebra_nat_add_assoc_proof.rs` for
        // construction details. This is a genuine constructive proof with
        // empty axiom closure.
        // #35: idempotent (see add_comm above).
        if self
            .get_const(&Name::from_string("Nat.add_assoc"))
            .is_none()
        {
            self.register_nat_add_assoc_proof()?;
        }

        // Nat.add_right_cancel : ∀ n m k : Nat, Eq (n + m) (k + m) → Eq n k
        //
        // #3604: Converted from Declaration::Axiom to Declaration::Theorem.
        // Induction on the cancelled (second) argument `m` via `Nat.rec.{0}`
        // with an implication-valued motive. Base case is the identity
        // `λ h => h` (motive at Nat.zero iota-reduces to `Eq n k → Eq n k`).
        // Step case at `Nat.succ j` applies constructor injectivity
        // `Nat.succ_inj (Nat.add n j) (Nat.add k j) h` (the hypothesis
        // iota-reduces to an equality of `succ`s) and feeds the result to the
        // induction hypothesis. See `algebra_nat_add_right_cancel_proof.rs` for
        // construction details. Depends on `Nat.succ_inj` (constructive #3604,
        // built from `Nat.noConfusion`); the resulting proof has empty
        // domain-axiom closure.
        // #35: best-effort — a cancellation lemma whose deps (e.g. Nat.succ_inj)
        // may be absent in some env configurations must not abort registration
        // and starve the independent mul/distrib lemmas below.
        let _ = self.register_nat_add_right_cancel_proof();

        // Nat.add_left_cancel : ∀ a b c : Nat, Eq (a + b) (a + c) → Eq b c
        //
        // #3604: New constructive `Declaration::Theorem` (no prior axiom).
        // Derived from `Nat.add_comm` + `Nat.add_right_cancel` rather than by
        // induction on the first addend (which `Nat.add`'s right-recursion would
        // force through `Nat.succ_add`): the equality chain
        // `b + a = a + b = a + c = c + a` is built with `Eq.trans` / `Eq.symm`,
        // then `Nat.add_right_cancel b a c` strips the common `+ a`. See
        // `algebra_nat_add_left_cancel_proof.rs`. Both helpers are constructive
        // (#3604); the resulting proof has empty domain-axiom closure. Helper
        // toward demoting `Nat.mul_left_cancel_succ`.
        // #35: best-effort (depends on add_right_cancel).
        let _ = self.register_nat_add_left_cancel_proof();

        // Nat.mul_left_cancel_succ : ∀ n a b : Nat,
        //   Eq ((Nat.succ n) * a) ((Nat.succ n) * b) → Eq a b
        //
        // #3604: Converted from Declaration::Axiom to Declaration::Theorem. The
        // proof goes via multiplicative monotonicity: `Eq.subst` transports the
        // product equality into both product inequalities, the constructive
        // `Nat.le_of_mul_le_mul_left_succ` cancels the positive multiplier in
        // each direction, and `Nat.le_antisymm` concludes `a = b`. The supporting
        // helpers (`Nat.zero_le`, `Nat.le_add_right`, `Nat.mul_le_mul_left`,
        // `Nat.le_or_lt`, `Nat.mul_lt_mul_left_succ`,
        // `Nat.le_of_mul_le_mul_left_succ`) are all constructive theorems, so the
        // resulting proof has an empty domain-axiom closure. See
        // `algebra_nat_mul_cancel_proof.rs` for construction details.
        // #35: best-effort (cancellation lemma).
        let _ = self.register_nat_mul_left_cancel_succ_proof();

        // Nat.add_zero : ∀ a : Nat, Eq (a + 0) a
        //
        // #3604: Converted from Declaration::Axiom to Declaration::Theorem. The
        // proof term `λ a : Nat => @Eq.refl.{1} Nat a` type-checks because
        // `Nat.add a Nat.zero` reduces to `a` via iota on `Nat.rec` (zero case)
        // + delta on the reducible `Nat.add` definition. See
        // `algebra_nat_add_zero_proof.rs` for construction details. This is a
        // genuine constructive proof with empty axiom closure.
        self.register_nat_add_zero_proof()?;

        // Nat.zero_add : ∀ a : Nat, Eq (0 + a) a
        //
        // #3604: Converted from Declaration::Axiom to Declaration::Theorem. The
        // proof term inducts on `a` via `Nat.rec.{0}`:
        //   base: @Eq.refl.{1} Nat Nat.zero   (iota: add 0 0 -> 0)
        //   step: λ k ih => @congrArg.{1,1} Nat Nat (0 + k) k Nat.succ ih
        //         (iota: add 0 (succ k) -> succ (add 0 k))
        // See `algebra_nat_zero_add_proof.rs` for construction details. This is
        // a genuine constructive proof with empty domain-axiom closure.
        self.register_nat_zero_add_proof()?;

        // Nat.mul_comm : ∀ a b : Nat, Eq (a*b) (b*a)
        //
        // #3604: Converted from Declaration::Axiom to Declaration::Theorem.
        // Induction on the second argument `b` via `Nat.rec.{0}`. Base case
        // closed by `Eq.symm (Nat.zero_mul a)` (motive at Nat.zero reduces
        // via iota zero-case + delta on Nat.mul). Step case composes
        //   c1 := congrArg (λ x => Nat.add x a) ih
        //   c2 := Nat.add_comm (Nat.mul k a) a
        //   c3 := Eq.symm (Nat.succ_mul k a)
        // via `Eq.trans`. See `algebra_nat_mul_comm_proof.rs` for details.
        // Depends on `Nat.zero_mul`, `Nat.add_comm`, `Nat.succ_mul` (all
        // constructive #3604); the resulting proof has empty domain-axiom
        // closure.
        //
        // IMPORT MODE (`suppress_lossy_structure_stubs`): `Nat.mul_comm` is
        // BUILT FROM the orientation-divergent `Nat.succ_mul` leaf (below), so it
        // is part of the divergent dependency set and is suppressed in import
        // mode together with `Nat.succ_mul` / `Nat.mul_succ` / `Nat.right_distrib`
        // (see the leaf comments below for the full rationale). The genuine
        // canonical Mathlib `Nat.mul_comm` registers through the checked import
        // path. The NON-divergent helpers above/below (`Nat.add_comm`,
        // `Nat.zero_add`, `Nat.succ_add`, `Nat.mul_assoc`, `Nat.left_distrib`, …)
        // are kept — `init_list_ops`/etc. legitimately depend on them in import
        // mode and they do NOT collide with any olean orientation.
        if !self.suppress_lossy_structure_stubs {
            self.register_nat_mul_comm_proof()?;
        }

        // Nat.mul_assoc : ∀ a b c : Nat, Eq ((a*b)*c) (a*(b*c))
        //
        // #3604: Converted from Declaration::Axiom to Declaration::Theorem.
        // Induction on the third argument `c` via `Nat.rec.{0}`. Base case
        // closed by `@Eq.refl.{1} Nat Nat.zero` (motive at Nat.zero reduces
        // both sides to `Nat.zero` via iota zero-case + delta on Nat.mul).
        // Step case chains
        //   c1 := congrArg (λ x => Nat.add x (Nat.mul a b)) ih
        //   c2 := Eq.symm (Nat.left_distrib a (Nat.mul b k) b)
        // via Eq.trans. See `algebra_nat_mul_assoc_proof.rs`. Depends on
        // `Nat.left_distrib` (constructive #3604); empty domain-axiom closure.
        self.register_nat_mul_assoc_proof()?;

        // Nat.mul_one : ∀ a : Nat, Eq (a * 1) a
        //
        // #3551 Tier A Batch 5: Converted from Declaration::Axiom to
        // Declaration::Theorem. The proof term `λ a : Nat => Nat.zero_add a`
        // type-checks because `Nat.mul a (Nat.succ Nat.zero)` reduces to
        // `Nat.add Nat.zero a` by iota (succ-case on Nat.rec) + beta +
        // iota (zero-case on inner Nat.rec) + delta on the reducible
        // `Nat.mul` definition. See `algebra_nat_mul_one_proof.rs` for
        // construction details. Depends on `Nat.zero_add` (constructive
        // #3604); the resulting proof has empty domain-axiom closure.
        self.register_nat_mul_one_proof()?;

        // Nat.one_mul : ∀ a : Nat, Eq (1 * a) a
        //
        // #3551 Tier A Batch 5: Converted from Declaration::Axiom to
        // Declaration::Theorem. Induction on `a` via `Nat.rec.{0}`. Base
        // case closed by `@Eq.refl.{1} Nat Nat.zero` (motive at Nat.zero
        // reduces to `Eq Nat.zero Nat.zero` via iota zero-case + delta on
        // Nat.mul). Step case closed by `congrArg Nat.succ ih` (motive at
        // `Nat.succ k` reduces via iota+beta+delta to
        // `Eq (Nat.succ (Nat.mul 1 k)) (Nat.succ k)`). See
        // `algebra_nat_one_mul_proof.rs` for construction details. This is
        // a genuine constructive proof with empty axiom closure.
        self.register_nat_one_mul_proof()?;

        // Nat.mul_zero : ∀ a : Nat, Eq (a * 0) 0
        //
        // #3551 Tier-D: Converted from Declaration::Axiom to
        // Declaration::Theorem. The proof term
        // `λ a : Nat => @Eq.refl.{1} Nat Nat.zero` type-checks because
        // `Nat.mul a Nat.zero` reduces to `Nat.zero` via iota on
        // `Nat.rec` (zero case) + delta on the reducible `Nat.mul`
        // definition. See `algebra_nat_mul_zero_proof.rs` for
        // construction details. This is a genuine constructive proof
        // with empty axiom closure.
        self.register_nat_mul_zero_proof()?;

        // Nat.zero_mul : ∀ a : Nat, Eq (0 * a) 0
        //
        // #3604: Converted from Declaration::Axiom to Declaration::Theorem.
        // Induction on `a` via `Nat.rec.{0}`. Base case closed by
        // `@Eq.refl.{1} Nat Nat.zero` (motive at Nat.zero reduces to
        // `Eq Nat.zero Nat.zero` via iota zero-case + delta on Nat.mul).
        // Step case closed by `ih` directly (motive at `Nat.succ k` reduces
        // to the ih type via iota succ-case on mul's Nat.rec + iota
        // zero-case on the outer Nat.add: `Nat.add x 0 ≡ x`). See
        // `algebra_nat_zero_mul_proof.rs` for details. This is a genuine
        // constructive proof with empty axiom closure.
        self.register_nat_zero_mul_proof()?;

        // Nat.left_distrib : ∀ a b c : Nat, Eq (a*(b+c)) (a*b + a*c)
        //
        // #3604: Converted from Declaration::Axiom to Declaration::Theorem.
        // Induction on the third argument `c` via `Nat.rec.{0}`. Base case
        // closed by `@Eq.refl.{1} Nat (Nat.mul a b)` (motive at Nat.zero
        // reduces both sides to `Nat.mul a b` via iota zero-case + delta on
        // Nat.add / Nat.mul). Step case chains
        //   c1 := congrArg (λ x => Nat.add x a) ih
        //   c2 := Nat.add_assoc (Nat.mul a b) (Nat.mul a k) a
        // via Eq.trans. See `algebra_nat_left_distrib_proof.rs`. Depends on
        // `Nat.add_assoc` (constructive #3551); empty domain-axiom closure.
        self.register_nat_left_distrib_proof()?;

        // Nat.right_distrib : ∀ a b c : Nat, Eq ((a+b)*c) (a*c + b*c)
        //
        // #3604: Converted from Declaration::Axiom to Declaration::Theorem.
        // Reduces right-distributivity to constructive `Nat.left_distrib`
        // via `Nat.mul_comm`, threading four `Eq.trans` rewrites:
        //   s1  := Nat.mul_comm (a+b) c
        //   s2  := Nat.left_distrib c a b
        //   s3a := congrArg (λ x => Nat.add x (c*b)) (Nat.mul_comm c a)
        //   s3b := congrArg (λ x => Nat.add (a*c) x) (Nat.mul_comm c b)
        // See `algebra_nat_right_distrib_proof.rs`. Depends on `Nat.mul_comm`
        // and `Nat.left_distrib` (both constructive #3604); empty
        // domain-axiom closure.
        //
        // IMPORT MODE: built FROM `Nat.mul_comm` (which is built from the
        // divergent `Nat.succ_mul` leaf), so it is part of the divergent
        // dependency set and is suppressed in import mode. The genuine canonical
        // Mathlib `Nat.right_distrib` registers through the checked import path.
        if !self.suppress_lossy_structure_stubs {
            self.register_nat_right_distrib_proof()?;
        }

        // Nat.succ_add : ∀ a b : Nat, Eq (succ(a) + b) (succ(a + b))
        //
        // #3604: Converted from Declaration::Axiom to Declaration::Theorem.
        // The proof term is `λ (a b : Nat) => @Nat.rec.{0} motive base step b`
        // (induction on the second argument b, since Nat.add recurses on its
        // second argument). Base case: `@Eq.refl.{1} Nat (Nat.succ a)` —
        // motive at Nat.zero reduces to `Eq (Nat.succ a) (Nat.succ a)` via
        // iota zero-case + delta on the reducible Nat.add. Step case:
        // `congrArg Nat.succ ih` produces the required equality; motive at
        // `Nat.succ k` reduces via iota succ-case + delta on Nat.add to
        // match the congrArg result type. See
        // `algebra_nat_succ_add_proof.rs` for construction details. This is
        // a genuine constructive proof with empty axiom closure.
        self.register_nat_succ_add_proof()?;

        // Nat.add_succ : ∀ a b : Nat, Eq (a + succ(b)) (succ(a + b))
        //
        // #3604: Converted from Declaration::Axiom to Declaration::Theorem.
        // The proof term `λ (a b : Nat) => @Eq.refl.{1} Nat (Nat.succ (Nat.add a b))`
        // type-checks because `Nat.add a (Nat.succ b)` reduces to
        // `Nat.succ (Nat.add a b)` via iota on `Nat.rec` (succ case) + delta
        // on the reducible `Nat.add` definition (which recurses on the
        // second argument) + beta. See `algebra_nat_add_succ_proof.rs` for
        // construction details. This is a genuine constructive proof with
        // empty axiom closure.
        self.register_nat_add_succ_proof()?;

        // Nat.succ_mul : ∀ a b : Nat, Eq (succ(a) * b) (b + a*b)
        //
        // #3604: Converted from Declaration::Axiom to Declaration::Theorem.
        // Induction on `b` via `Nat.rec.{0}`. Base case: `@Eq.refl.{1} Nat Nat.zero`
        // (both sides iota-reduce to Nat.zero). Step case composes three
        // Eq.trans steps:
        //   c1 := congrArg (λ x => succ (add x a)) ih
        //   c2 := congrArg Nat.succ (Nat.add_assoc k (Nat.mul a k) a)
        //   c3 := Eq.symm (Nat.succ_add k (Nat.add (Nat.mul a k) a))
        // See `algebra_nat_succ_mul_proof.rs` for details. Depends on
        // `Nat.add_assoc` and `Nat.succ_add` (both constructive #3604); the
        // resulting proof has empty domain-axiom closure.
        //
        // IMPORT MODE (`suppress_lossy_structure_stubs`): `Nat.succ_mul` is the
        // orientation-divergent LEAF — Clean spells it `(succ n)*m = m + n*m`,
        // whereas Lean 4 v4.8.0 core spells it `(succ n)*m = (n*m) + m` (addends
        // SWAPPED; see the CORRECTED ROOT CAUSE in
        // `docs/plans/NAT_DEFS_CHECKMODE_APPARG_FVAR_DIVERGENCE_2026-06-29.md`).
        // It is a genuine kernel-checked theorem, just non-canonically oriented.
        // Because the `.olean` loader dedups by name and `register_*` helpers
        // early-return on an existing name, registering the commuted form first
        // SHADOWS the genuine canonical Mathlib `Nat.succ_mul` on import, so every
        // imported proof elaborated against the canonical orientation fails
        // `is_def_eq(arg_type, expected_arg_type)` (the kernel CORRECTLY rejects —
        // `Nat.add` is not commutative by whnf with free operands). The gate lives
        // INSIDE this init (not only at the prelude call site) because
        // `init_nat_arith_lemmas` is reached through MULTIPLE import-prelude paths
        // — directly from `init_prelude_algebra` AND transitively via
        // `init_list_happend_inst → init_list_ops` (which only needs
        // `Nat.zero_add`/`Nat.succ_add`, registered above, NOT the divergent
        // leaves). Withholding here lets the genuine canonical Mathlib
        // `Nat.succ_mul` register through the checked import path on EVERY path.
        // SOUNDNESS-NEUTRAL: only WITHHOLDS a Clean-native theorem in import mode;
        // nothing touches `is_def_eq`/`whnf`/`check_type`, no axiom is added. The
        // non-import lane (`clean check` + every Clean-native caller —
        // `algebra_nat_mul_comm_proof`, `boolean_analysis_*`, the nn-verify ulp
        // lane) is UNCHANGED: the commuted-orientation leaf still registers.
        if !self.suppress_lossy_structure_stubs {
            self.register_nat_succ_mul_proof()?;
        }

        // Nat.mul_succ : ∀ a b : Nat, Eq (a * succ(b)) (a + a*b)
        //
        // #3551 Tier A Batch 5: Converted from Declaration::Axiom to
        // Declaration::Theorem. The proof term
        // `λ a b : Nat => Nat.add_comm (Nat.mul a b) a` type-checks because
        // `Nat.mul a (Nat.succ b)` reduces to `Nat.add (Nat.mul a b) a` via
        // iota (succ-case on Nat.rec) + beta + delta on the reducible
        // `Nat.mul` definition. See `algebra_nat_mul_succ_proof.rs` for
        // construction details. Depends on `Nat.add_comm` (constructive
        // #3604); the resulting proof has empty domain-axiom closure.
        //
        // IMPORT MODE: the second orientation-divergent LEAF — Clean spells
        // `n*(succ m) = n + n*m`, Lean canonical is `n*(succ m) = n*m + n`
        // (addends SWAPPED). Suppressed in import mode for the same reason as
        // `Nat.succ_mul` above; the genuine canonical Mathlib `Nat.mul_succ`
        // registers through the checked import path.
        if !self.suppress_lossy_structure_stubs {
            self.register_nat_mul_succ_proof()?;
        }

        self.nat_arith_lemmas_init = true;
        Ok(())
    }

    /// Initialize the Nat ordering lemmas used by SMT bridge proof replay.
    ///
    /// Bridge-produced arithmetic proofs reference a focused subset of Nat
    /// ordering theorems:
    /// - `Nat.le_refl`, `Nat.le_trans`, `Nat.le_antisymm`
    /// - `Nat.lt_irrefl`, `Nat.lt_trans`
    /// - `Nat.lt_of_lt_of_le`, `Nat.lt_of_le_of_lt`, `Nat.le_of_lt`
    ///
    /// Minimal tactic environments often stop at `init_le()` / `init_lt()`,
    /// which provides the relation shells but not these supporting lemmas.
    /// This helper exposes the exact mutating initialization needed by the
    /// elab-layer SMT bridge without requiring a full `with_prelude()` rebuild.
    pub fn init_smt_bridge_nat_order_lemmas(&mut self) -> Result<(), EnvError> {
        self.init_nat_preorder()?;
        self.init_nat_partial_order()?;
        self.init_nat_lt_irrefl()?;
        self.init_nat_lt_trans()?;
        self.init_nat_trans_lt_le_lt()?;
        self.init_nat_trans_le_lt_lt()?;
        self.init_nat_trans_lt_lt_le()?;
        Ok(())
    }

    /// Check if Nat arithmetic lemmas have been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_nat_arith_lemmas` has completed successfully
    /// ENSURES: Pure - no side effects
    #[allow(dead_code)]
    pub(crate) fn has_nat_arith_lemmas(&self) -> bool {
        self.nat_arith_lemmas_init
    }
}
