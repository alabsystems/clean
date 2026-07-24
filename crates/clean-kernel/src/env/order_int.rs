// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Int ordering for Environment
//!
//! This module contains Int-specific ordering init_* and has_* functions:
//! - Int.NonNeg, Int.le, Int.lt, instLEInt, instLTInt
//! - Decidable instances for Int.lt, Int.le, and Int.decEq
//! - Int ordering lemmas (le_refl, le_trans, le_antisymm, lt_irrefl, etc.)
//! - Int LinearOrder instance chain (Preorder, PartialOrder, LinearOrder)

use super::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType,
    KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Int ordering (le, lt)
    ///
    /// This adds:
    /// - Int.NonNeg : Int → Prop (inductive predicate for non-negative integers)
    /// - Int.le : Int → Int → Prop (a ≤ b iff b - a is non-negative)
    /// - Int.lt : Int → Int → Prop (a < b iff a + 1 ≤ b)
    /// - instLEInt : LE Int
    /// - instLTInt : LT Int
    ///
    /// Following Lean 4 definitions:
    /// - NonNeg is an inductive with one constructor: NonNeg.mk : (n : Nat) → NonNeg (ofNat n)
    /// - le a b := NonNeg (b - a)
    /// - lt a b := le (a + 1) b
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_ord_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_ord(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, residual-to-zero
        // campaign 2026-07-03): part of the Clean-native Int cluster whose
        // definitions reference the suppressed Int arithmetic stubs
        // (`Int.le := NonNeg (b - a)`-shaped bodies use `Int.sub`). In import
        // mode the genuine olean declarations import instead. See
        // `init_int_arith` for the cluster rationale.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.int_ord_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_int_arith()?; // Provides Int.sub, Int.add
        self.init_le()?; // Provides LE typeclass
        self.init_lt()?; // Provides LT typeclass

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);

        // Int.NonNeg : Int → Prop
        // inductive Int.NonNeg : Int → Prop where
        //   | mk (n : Nat) : Int.NonNeg (ofNat n)
        let int_nonneg_type = Expr::pi(BinderInfo::Default, int_const.clone(), prop.clone());

        // Int.NonNeg.mk : (n : Nat) → Int.NonNeg (ofNat n)
        let int_nonneg_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let r = Expr::app(
                Expr::const_(Name::from_string("Int.NonNeg"), vec![]),
                Expr::app(int_of_nat.clone(), n),
            );
            let r = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        let int_nonneg_ind = InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("Int.NonNeg"),
                type_: int_nonneg_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Int.NonNeg.mk"),
                    type_: int_nonneg_mk_type,
                }],
            }],
        };

        self.add_inductive(int_nonneg_ind)?;

        // Int.le : Int → Int → Prop := λ a b => Int.NonNeg (Int.sub b a)
        let int_le_type = Expr::pi(
            BinderInfo::Default,
            int_const.clone(),
            Expr::pi(BinderInfo::Default, int_const.clone(), prop.clone()),
        );

        let int_sub = Expr::const_(Name::from_string("Int.sub"), vec![]);
        let int_nonneg = Expr::const_(Name::from_string("Int.NonNeg"), vec![]);

        // λ a : Int => λ b : Int => Int.NonNeg (Int.sub b a)
        let int_le_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(int_const.clone());
            let (b_id2, bv) = b.fresh_local(int_const.clone());
            let body = Expr::app(
                int_nonneg.clone(),
                Expr::app(Expr::app(int_sub.clone(), bv), a),
            );
            let r = b.mk_lam(b_id2, BinderInfo::Default, int_const.clone(), body);
            let r = b.mk_lam(a_id, BinderInfo::Default, int_const.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Int.le"),
            level_params: vec![],
            type_: int_le_type,
            value: int_le_value,
            is_reducible: true,
        })?;

        // Int.lt : Int → Int → Prop := λ a b => Int.le (Int.add a (ofNat 1)) b
        let int_lt_type = Expr::pi(
            BinderInfo::Default,
            int_const.clone(),
            Expr::pi(BinderInfo::Default, int_const.clone(), prop.clone()),
        );

        let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
        let int_le_const = Expr::const_(Name::from_string("Int.le"), vec![]);
        let nat_one = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        );

        // λ a : Int => λ b : Int => Int.le (Int.add a (ofNat 1)) b
        let int_lt_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(int_const.clone());
            let (b_id2, bv) = b.fresh_local(int_const.clone());
            let body = Expr::app(
                Expr::app(
                    int_le_const.clone(),
                    Expr::app(
                        Expr::app(int_add.clone(), a),
                        Expr::app(int_of_nat.clone(), nat_one.clone()),
                    ),
                ),
                bv,
            );
            let r = b.mk_lam(b_id2, BinderInfo::Default, int_const.clone(), body);
            let r = b.mk_lam(a_id, BinderInfo::Default, int_const.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Int.lt"),
            level_params: vec![],
            type_: int_lt_type,
            value: int_lt_value,
            is_reducible: true,
        })?;

        // instLEInt : LE Int := ⟨Int.le⟩
        // Int : Type 0, so LE.{0}
        let le_int_type = Expr::app(
            Expr::const_(Name::from_string("LE"), vec![Level::zero()]),
            int_const.clone(),
        );
        let int_le_def = Expr::const_(Name::from_string("Int.le"), vec![]);
        let le_int_value = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("LE.mk"), vec![Level::zero()]),
                int_const.clone(),
            ),
            int_le_def,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instLEInt"),
            level_params: vec![],
            type_: le_int_type,
            value: le_int_value,
            is_reducible: true,
        })?;

        // instLTInt : LT Int := ⟨Int.lt⟩
        // Int : Type 0, so LT.{0}
        let lt_int_type = Expr::app(
            Expr::const_(Name::from_string("LT"), vec![Level::zero()]),
            int_const.clone(),
        );
        let int_lt_def = Expr::const_(Name::from_string("Int.lt"), vec![]);
        let lt_int_value = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("LT.mk"), vec![Level::zero()]),
                int_const.clone(),
            ),
            int_lt_def,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instLTInt"),
            level_params: vec![],
            type_: lt_int_type,
            value: lt_int_value,
            is_reducible: true,
        })?;

        self.int_ord_init = true;
        Ok(())
    }

    /// Check if Int ordering has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.int_ord_init == true`
    pub(crate) fn has_int_ord(&self) -> bool {
        self.int_ord_init
    }

    /// Initialize Decidable instances for Int.lt and Int.le
    ///
    /// This adds:
    /// - instDecidableIntLt : Definition ∀ a b : Int, Decidable (Int.lt a b) := Int.decLt
    /// - instDecidableIntLe : Definition ∀ a b : Int, Decidable (Int.le a b) := Int.decLe
    /// - Int.decEq : axiom ∀ a b : Int, Decidable (Eq a b)
    ///
    /// These enable decision procedures for Int ordering and equality comparisons.
    ///
    /// SOUNDNESS: `instDecidableIntLt` / `instDecidableIntLe` are now
    /// `Declaration::Definition`s (not Axioms, trk-rr-intord). Their values are
    /// the constructive, empty-axiom-closure `Int.decLt` / `Int.decLe` kernel
    /// terms (`order_int_dec_le_lt_proof.rs`), each a thin `Int.decNonNeg`
    /// wrapper whose `Decidable (Int.NonNeg …)` result is def-eq to
    /// `Decidable (Int.lt a b)` / `Decidable (Int.le a b)`. Mirrors the wave-1
    /// `Nat` demotion (`instDecidableNatLe`/`Lt` → `Nat.decLe`/`Nat.decLt`). The
    /// `Int.decEq` axiom is unchanged (out of scope here).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_decidable_ord_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_decidable_ord(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, residual-to-zero
        // campaign 2026-07-03): part of the Clean-native Int cluster whose
        // definitions reference the suppressed Int arithmetic stubs
        // (`Int.le := NonNeg (b - a)`-shaped bodies use `Int.sub`). In import
        // mode the genuine olean declarations import instead. See
        // `init_int_arith` for the cluster rationale.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.int_decidable_ord_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_int_ord()?; // Provides Int.le, Int.lt, instLEInt, instLTInt
        self.init_decidable()?; // Provides Decidable
        self.init_eq()?; // Provides Eq
                         // Constructive Int.decLe / Int.decLt leaves (empty axiom closure).
        self.register_int_dec_le_lt_proof()?;

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let decidable_const = Expr::const_(Name::from_string("Decidable"), vec![]);

        // `@LE.le.{0} Int instLEInt a b` / `@LT.lt.{0} Int instLTInt a b` — the
        // typeclass-form comparisons the elaborator's `if (a ≤ b)` / `if (a < b)`
        // desugaring produces (matching the `instDecidableNatLe` shape, and the
        // wrapper `instDecidable<T>Le` shape). Each reducibly unfolds to
        // `Int.le a b` / `Int.lt a b` (the reducible `instLEInt`/`instLTInt`
        // projection), so the `Int.decLe`/`Int.decLt` values are def-eq to the
        // declared instance result and the definitions kernel-check.
        let le_le = Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]);
        let lt_lt = Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]);
        let inst_le_int = Expr::const_(Name::from_string("instLEInt"), vec![]);
        let inst_lt_int = Expr::const_(Name::from_string("instLTInt"), vec![]);
        let le_tc = |a: Expr, bv: Expr| {
            Expr::apps(
                le_le.clone(),
                [int_const.clone(), inst_le_int.clone(), a, bv],
            )
        };
        let lt_tc = |a: Expr, bv: Expr| {
            Expr::apps(
                lt_lt.clone(),
                [int_const.clone(), inst_lt_int.clone(), a, bv],
            )
        };

        // instDecidableIntLt : (a b : Int) → Decidable (@LT.lt Int instLTInt a b)
        //   := Int.decLt
        let decidable_lt_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(int_const.clone());
            let (b_id2, bv) = b.fresh_local(int_const.clone());
            let r = Expr::app(decidable_const.clone(), lt_tc(a, bv));
            let r = b.mk_pi(b_id2, BinderInfo::Default, int_const.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, int_const.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instDecidableIntLt"),
            level_params: vec![],
            type_: decidable_lt_type.clone(),
            value: Expr::const_(Name::from_string("Int.decLt"), vec![]),
            is_reducible: true,
        })?;

        // instDecidableIntLe : (a b : Int) → Decidable (@LE.le Int instLEInt a b)
        //   := Int.decLe
        let decidable_le_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(int_const.clone());
            let (b_id2, bv) = b.fresh_local(int_const.clone());
            let r = Expr::app(decidable_const.clone(), le_tc(a, bv));
            let r = b.mk_pi(b_id2, BinderInfo::Default, int_const.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, int_const.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instDecidableIntLe"),
            level_params: vec![],
            type_: decidable_le_type.clone(),
            value: Expr::const_(Name::from_string("Int.decLe"), vec![]),
            is_reducible: true,
        })?;

        // Register the foundational `LE Int` / `LT Int` instances so the
        // elaborator can resolve the `[inst : LE Int]` / `[inst : LT Int]`
        // argument of `LE.le` / `LT.lt` (mirrors `init_nat_decidable_ord`).
        // `instLEInt` / `instLTInt` are reducible Definitions registered by
        // `init_int_ord` above.
        if let Some(ty) = self
            .get_const(&Name::from_string("instLEInt"))
            .map(|c| c.type_.clone())
        {
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string("instLEInt"),
                class_name: Name::from_string("LE"),
                priority: DEFAULT_INSTANCE_PRIORITY,
                type_: Some(ty),
                value: Some(Expr::const_(Name::from_string("instLEInt"), vec![])),
            });
        }
        if let Some(ty) = self
            .get_const(&Name::from_string("instLTInt"))
            .map(|c| c.type_.clone())
        {
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string("instLTInt"),
                class_name: Name::from_string("LT"),
                priority: DEFAULT_INSTANCE_PRIORITY,
                type_: Some(ty),
                value: Some(Expr::const_(Name::from_string("instLTInt"), vec![])),
            });
        }

        // Register the two decision procedures under the `Decidable` class so
        // `if (a ≤ b)` / `if (a < b)` / `decide` over `Int` resolve them.
        // Stripping the two explicit `Int` binders leaves
        // `Decidable (@LE.le Int instLEInt ?a ?b)` (resp. `LT.lt`) — exactly the
        // goal the elaborator constructs.
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instDecidableIntLe"),
            class_name: Name::from_string("Decidable"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: Some(decidable_le_type),
            value: Some(Expr::const_(
                Name::from_string("instDecidableIntLe"),
                vec![],
            )),
        });
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instDecidableIntLt"),
            class_name: Name::from_string("Decidable"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: Some(decidable_lt_type),
            value: Some(Expr::const_(
                Name::from_string("instDecidableIntLt"),
                vec![],
            )),
        });

        // Register `Int.decNonNeg : (x : Int) → Decidable (Int.NonNeg x)` under the
        // `Decidable` class too. `Int.le`/`Int.lt` (and the `@LE.le Int instLEInt`
        // typeclass form) are *reducible* defs over `Int.NonNeg (Int.sub …)`, so
        // by the time the elaborator's `if`-condition Decidable goal reaches
        // instance resolution it has already whnf-reduced to
        // `Decidable (Int.NonNeg (Int.sub b a))` — the `LE.le`/`Int.le` head is
        // gone, so `instDecidableIntLe`/`Lt` above cannot match it. The
        // `Int.decNonNeg` instance matches this reduced shape directly (stripping
        // its `x` binder leaves `Decidable (Int.NonNeg ?x)`), and its value
        // reduces on ground numerals to a real `Decidable.isTrue`/`isFalse`
        // constructor for the kernel `ite` iota step. (`Nat.le` is inductive and
        // does NOT reduce, which is why `Nat` only needs the `LE.le`-shaped
        // instances.) `Int.decNonNeg` is the constructive, empty-axiom-closure
        // decision procedure from `order_int_dec_le_lt_proof.rs`.
        if let Some(ty) = self
            .get_const(&Name::from_string("Int.decNonNeg"))
            .map(|c| c.type_.clone())
        {
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string("Int.decNonNeg"),
                class_name: Name::from_string("Decidable"),
                priority: DEFAULT_INSTANCE_PRIORITY,
                type_: Some(ty),
                value: Some(Expr::const_(Name::from_string("Int.decNonNeg"), vec![])),
            });
        }

        // `Int.decEq : (a b : Int) → Decidable (Eq a b)` — registered as a
        // CONSTRUCTIVE, axiom-free `Declaration::Definition` (a 2×2
        // `Int.rec`/`Int.rec` split dispatching on `Nat.decEq` of the
        // `ofNat`/`negSucc` carriers; see `algebra_int_dec_eq_proof.rs`),
        // demoting the prior `Declaration::Axiom`. `register_int_dec_eq_proof`
        // is idempotent and guards on `Int.decEq` not already existing, so this
        // is safe regardless of whether `init_decidable_eq` (which also wires
        // the `instDecidableEqInt` bridge over this term) ran first.
        //
        // IMPORT MODE (`suppress_lossy_structure_stubs`): withheld — `Int.decEq`'s
        // body dispatches on the gated `Nat.decEq` overlay (see
        // `register_nat_dec_eq_proof` / `register_nat_succ_inj_proof`), so it
        // would reference an absent constant. The genuine Lean 4 `Int.decEq`
        // imports from the closure instead.
        if !self.suppress_lossy_structure_stubs {
            self.register_int_dec_eq_proof()?;
        }

        self.int_decidable_ord_init = true;
        Ok(())
    }

    /// Check if Int decidable ordering instances have been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.int_decidable_ord_init == true`
    pub(crate) fn has_int_decidable_ord(&self) -> bool {
        self.int_decidable_ord_init
    }

    /// Initialize Int ordering lemmas
    ///
    /// This adds fundamental ordering lemmas for Int (constructive Theorems
    /// where marked, axioms otherwise):
    /// - Int.le_refl : theorem ∀ a : Int, Int.le a a
    /// - Int.le_trans : theorem ∀ a b c : Int, Int.le a b → Int.le b c → Int.le a c
    /// - Int.le_antisymm : theorem ∀ a b : Int, Int.le a b → Int.le b a → Eq a b
    /// - Int.lt_irrefl : theorem ∀ a : Int, Not (Int.lt a a)
    /// - Int.lt_trans : theorem ∀ a b c : Int, Int.lt a b → Int.lt b c → Int.lt a c
    /// - Int.le_of_lt : theorem ∀ a b : Int, Int.lt a b → Int.le a b
    /// - Int.lt_of_le_of_lt : theorem ∀ a b c : Int, Int.le a b → Int.lt b c → Int.lt a c
    /// - Int.lt_of_lt_of_le : theorem ∀ a b c : Int, Int.lt a b → Int.le b c → Int.lt a c
    /// - Int.lt_trichotomy : theorem ∀ a b : Int, Or (Int.lt a b) (Or (Eq a b) (Int.lt b a))
    /// - Int.add_le_add_left : theorem ∀ a b : Int, Int.le a b → ∀ c, Int.le (c+a) (c+b)
    /// - Int.add_le_add_right : theorem ∀ a b : Int, Int.le a b → ∀ c, Int.le (a+c) (b+c)
    /// - Int.le_of_add_le_add_left : theorem ∀ a b c : Int, Int.le (a+b) (a+c) → Int.le b c
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_ord_lemmas_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_int_ord_lemmas(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, residual-to-zero
        // campaign 2026-07-03): part of the Clean-native Int cluster whose
        // definitions reference the suppressed Int arithmetic stubs
        // (`Int.le := NonNeg (b - a)`-shaped bodies use `Int.sub`). In import
        // mode the genuine olean declarations import instead. See
        // `init_int_arith` for the cluster rationale.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.int_ord_lemmas_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_int_ord()?; // Provides Int.le, Int.lt
        self.init_eq()?; // Provides Eq
        self.init_true_false()?; // Provides Not
        self.init_classical()?; // Provides Or

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let le_const = Expr::const_(Name::from_string("Int.le"), vec![]);
        let lt_const = Expr::const_(Name::from_string("Int.lt"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let not_const = Expr::const_(Name::from_string("Not"), vec![]);
        let or_const = Expr::const_(Name::from_string("Or"), vec![]);

        // Int.le_refl : ∀ a : Int, Int.le a a
        //
        // SOUNDNESS: Converted from Declaration::Axiom to Declaration::Theorem.
        // Proof transports `@Int.NonNeg.mk Nat.zero : NonNeg (ofNat 0)` along
        // `Eq.symm (Int.sub_self a)` via `@Eq.subst.{1}`, yielding
        // `Int.NonNeg (Int.sub a a)` ≡ `Int.le a a`. See
        // `algebra_int_le_refl_proof.rs`. Empty domain-axiom closure.
        self.register_int_le_refl_proof()?;

        // Int.le_trans : ∀ a b c : Int, Int.le a b → Int.le b c → Int.le a c
        //
        // SOUNDNESS: Converted from Declaration::Axiom to Declaration::Theorem.
        // Combines the two `Int.NonNeg` witnesses via the constructive
        // `Int.NonNeg.add`, then transports along `Int.sub_add_sub_cancel`
        // (`(c-b)+(b-a) = c-a`) with `@Eq.subst.{1}` to obtain
        // `Int.NonNeg (Int.sub c a)` ≡ `Int.le a c`. See
        // `algebra_int_le_trans_proof.rs`. Empty domain-axiom closure.
        self.register_int_le_trans_proof()?;

        // Int.le_antisymm : ∀ a b : Int, Int.le a b → Int.le b a → Eq a b
        //
        // SOUNDNESS: Converted from Declaration::Axiom to Declaration::Theorem.
        // The hypotheses `Int.le a b` / `Int.le b a` delta-reduce to
        // `NonNeg (Int.sub b a)` / `NonNeg (Int.sub a b)`. A closed helper
        // `core : ∀ x, NonNeg x → NonNeg (neg x) → x = ofNat 0` (built by
        // `@Int.NonNeg.rec.{0}` with an implication motive, an inner
        // `@Nat.rec.{0}`, and the `disc` discriminator discharging the
        // impossible `negSucc` branch via `@False.elim.{0}`) is applied to
        // `x := sub b a`, `h1`, and `h2` transported along the constructive
        // identity `-(b-a) = a-b` (`Int.neg_add` / `Int.neg_neg` /
        // `Int.add_comm`) by `@Eq.subst.{1}`. The resulting `sub b a = ofNat 0`
        // is turned into `Eq a b` by `Int.add_right_cancel a (neg a) b` over
        // `Eq.trans (Int.add_neg_self a) (Eq.symm hzero)`. See
        // `algebra_int_le_antisymm_proof.rs`. Empty domain-axiom closure.
        self.register_int_le_antisymm_proof()?;

        // Int.lt_irrefl : ∀ a : Int, Not (Int.lt a a)
        //
        // SOUNDNESS: Converted from Declaration::Axiom to Declaration::Theorem.
        // `Int.lt a a` ≡ `NonNeg (Int.sub a (a+1))`, which transports along
        // `Int.sub_add_one_self a : a - (a+1) = -1` to `NonNeg (Int.negSucc 0)`,
        // discharged to `False` by `@Int.NonNeg.rec.{0}` against a `True`/`False`
        // discriminator predicate. See `algebra_int_lt_irrefl_proof.rs`. Empty
        // domain-axiom closure.
        self.register_int_lt_irrefl_proof()?;

        // Int.lt_trans : ∀ a b c : Int, Int.lt a b → Int.lt b c → Int.lt a c
        //
        // SOUNDNESS: Converted from Declaration::Axiom to Declaration::Theorem.
        // Two `Int.le_trans` steps with the constructive `+1` bridge
        // `Int.le_self_add_one`: the hypotheses `Int.lt a b` / `Int.lt b c`
        // delta-reduce to `Int.le (a+1) b` / `Int.le (b+1) c`, and the result
        // `Int.le (a+1) c` matches the goal `Int.lt a c`. See
        // `algebra_int_lt_trans_proof.rs`. Empty domain-axiom closure.
        self.register_int_lt_trans_proof()?;

        // Int.le_of_lt : ∀ a b : Int, Int.lt a b → Int.le a b
        //
        // SOUNDNESS: Converted from Declaration::Axiom to Declaration::Theorem.
        // Chains the constructive bridge `Int.le_self_add_one a : Int.le a (a+1)`
        // with `Int.lt a b` (≡ `Int.le (a+1) b`) through `Int.le_trans`, yielding
        // `Int.le a b`. See `algebra_int_le_of_lt_proof.rs`. Empty domain-axiom
        // closure.
        self.register_int_le_of_lt_proof()?;

        // Int.lt_of_le_of_lt : ∀ a b c : Int, Int.le a b → Int.lt b c → Int.lt a c
        //
        // SOUNDNESS: Converted from Declaration::Axiom to Declaration::Theorem.
        // Adds `1` on the right of `Int.le a b` (constructive
        // `Int.add_le_add_right`) to get `Int.le (a+1) (b+1)`, then chains with
        // `Int.lt b c` (≡ `Int.le (b+1) c`) via `Int.le_trans` to yield
        // `Int.le (a+1) c` ≡ `Int.lt a c`. See `algebra_int_lt_of_le_of_lt_proof.rs`.
        // Empty domain-axiom closure.
        self.register_int_lt_of_le_of_lt_proof()?;

        // Int.lt_of_lt_of_le : ∀ a b c : Int, Int.lt a b → Int.le b c → Int.lt a c
        //
        // SOUNDNESS: Converted from Declaration::Axiom to Declaration::Theorem.
        // A single `Int.le_trans` step through the midpoint `b`:
        // `Int.lt a b` (≡ `Int.le (a+1) b`) chained with `Int.le b c` gives
        // `Int.le (a+1) c` ≡ `Int.lt a c`. See `algebra_int_lt_of_lt_of_le_proof.rs`.
        // Empty domain-axiom closure.
        self.register_int_lt_of_lt_of_le_proof()?;

        // Int.lt_trichotomy : ∀ a b : Int, Or (Int.lt a b) (Or (Eq a b) (Int.lt b a))
        //
        // SOUNDNESS: Converted from Declaration::Axiom to Declaration::Theorem.
        // A single `@Int.rec.{0}` case-analysis on `d := Int.sub b a` (with an
        // equation-carrying motive `λ i => Eq (Int.sub b a) i → Goal`, applied
        // to `Eq.refl (Int.sub b a)`) splits the sign of the difference: the
        // `ofNat`/`Nat.rec` `0` case yields `Eq a b`, the `ofNat`/`succ` case
        // yields `Int.lt a b`, and the `negSucc` case yields `Int.lt b a`. The
        // two strict cases transport `@Int.NonNeg.mk` along constructive Int
        // arithmetic equalities via `@Eq.subst.{1}`. See
        // `order_int_lt_trichotomy_proof.rs`. Empty domain-axiom closure.
        self.register_int_lt_trichotomy_proof()?;

        // Int.add_le_add_left : ∀ a b : Int, Int.le a b → ∀ c : Int,
        //   Int.le (Int.add c a) (Int.add c b)
        // Required by bridge LRA Farkas additive proof reconstruction (#2422).
        //
        // SOUNDNESS: Converted from Declaration::Axiom to Declaration::Theorem.
        // `(c+b) - (c+a) = b - a` (`Int.add_sub_add_left`), so the `Int.le a b`
        // witness `NonNeg (b-a)` transports via `@Eq.subst.{1}` to
        // `NonNeg ((c+b)-(c+a))` ≡ `Int.le (c+a) (c+b)`. See
        // `algebra_int_add_le_add_left_proof.rs`. Empty domain-axiom closure.
        self.register_int_add_le_add_left_proof()?;

        // Int.add_le_add_right : ∀ a b : Int, Int.le a b → ∀ c : Int,
        //   Int.le (Int.add a c) (Int.add b c)
        // Required by bridge LRA Farkas additive proof reconstruction (#302).
        //
        // SOUNDNESS: Converted from Declaration::Axiom to Declaration::Theorem.
        // `(b+c) - (a+c) = b - a` (`Int.add_sub_add_right`), so the `Int.le a b`
        // witness `NonNeg (b-a)` transports via `@Eq.subst.{1}` to
        // `NonNeg ((b+c)-(a+c))` ≡ `Int.le (a+c) (b+c)`. See
        // `algebra_int_add_le_add_right_proof.rs`. Empty domain-axiom closure.
        self.register_int_add_le_add_right_proof()?;

        // Int.add_lt_add_left : ∀ a b : Int, Int.lt a b → ∀ c : Int,
        //   Int.lt (Int.add c a) (Int.add c b)
        // Required by bridge LRA Farkas mixed Le/Lt additive proof reconstruction (#302).
        //
        // SOUNDNESS: Converted from Declaration::Axiom to Declaration::Theorem.
        // `Int.lt a b` ≡ `Int.le (a+1) b`, so applying the constructive
        // `Int.add_le_add_left (a+1) b h c : Int.le (c+(a+1)) (c+b)` then
        // transporting along `Int.add_assoc c a 1 : (c+a)+1 = c+(a+1)` via
        // `@Eq.subst.{1}` yields `Int.le ((c+a)+1) (c+b)` ≡ `Int.lt (c+a) (c+b)`.
        // See `algebra_int_add_lt_add_left_proof.rs`. Empty domain-axiom closure.
        self.register_int_add_lt_add_left_proof()?;

        // Int.add_lt_add_right : ∀ a b : Int, Int.lt a b → ∀ c : Int,
        //   Int.lt (Int.add a c) (Int.add b c)
        // Required by bridge LRA Farkas mixed Le/Lt additive proof reconstruction (#302).
        //
        // SOUNDNESS: Converted from Declaration::Axiom to Declaration::Theorem.
        // `Int.lt a b` ≡ `Int.le (a+1) b`, so applying the constructive
        // `Int.add_le_add_right (a+1) b h c : Int.le ((a+1)+c) (b+c)` then
        // transporting along the `Int.add_assoc` / `Int.add_comm` bridge
        // `(a+1)+c = a+(1+c) = a+(c+1) = (a+c)+1` via `@Eq.subst.{1}` yields
        // `Int.le ((a+c)+1) (b+c)` ≡ `Int.lt (a+c) (b+c)`. See
        // `algebra_int_add_lt_add_right_proof.rs`. Empty domain-axiom closure.
        self.register_int_add_lt_add_right_proof()?;

        // Int.le_of_add_le_add_left : ∀ a b c : Int,
        //   Int.le (Int.add a b) (Int.add a c) → Int.le b c
        // Cancellation lemma: cancel common left addend. Required by bridge
        // LRA symbolic additive closeout for shared-suffix peeling (#302).
        //
        // SOUNDNESS: Converted from Declaration::Axiom to Declaration::Theorem.
        // `(a+c) - (a+b) = c - b` (`Int.add_sub_add_left b c a`), so the premise
        // witness `NonNeg ((a+c)-(a+b))` transports forward via `@Eq.subst.{1}`
        // to `NonNeg (c-b)` ≡ `Int.le b c`. See
        // `algebra_int_le_of_add_le_add_left_proof.rs`. Empty domain-axiom closure.
        self.register_int_le_of_add_le_add_left_proof()?;

        // Int.le_of_add_le_add_right : ∀ a b c : Int,
        //   Int.le (Int.add a b) (Int.add c b) → Int.le a c
        // Cancellation lemma: cancel common right addend (#302).
        //
        // SOUNDNESS: Converted from Declaration::Axiom to Declaration::Theorem.
        // `(c+b) - (a+b) = c - a` (`Int.add_sub_add_right a c b`), so the premise
        // witness `NonNeg ((c+b)-(a+b))` transports forward via `@Eq.subst.{1}`
        // to `NonNeg (c-a)` ≡ `Int.le a c`. Mirror of the landed left version.
        // See `algebra_int_le_of_add_le_add_right_proof.rs`. Empty domain-axiom
        // closure.
        self.register_int_le_of_add_le_add_right_proof()?;

        // Int.lt_of_add_lt_add_left : ∀ a b c : Int,
        //   Int.lt (Int.add a b) (Int.add a c) → Int.lt b c
        // Cancellation lemma: cancel common left addend for strict (#302).
        //
        // SOUNDNESS: Converted from Declaration::Axiom to Declaration::Theorem.
        // Reassociates `h : Int.lt (a+b) (a+c)` (≡ `Int.le ((a+b)+1) (a+c)`)
        // along `Int.add_assoc a b 1 : (a+b)+1 = a+(b+1)` via `@Eq.subst.{1}` to
        // `Int.le (a+(b+1)) (a+c)`, then cancels `a` with the constructive
        // `Int.le_of_add_le_add_left a (b+1) c`, yielding `Int.le (b+1) c` ≡
        // `Int.lt b c`. See `algebra_int_lt_of_add_lt_add_left_proof.rs`. Empty
        // domain-axiom closure.
        self.register_int_lt_of_add_lt_add_left_proof()?;

        // Int.lt_of_add_lt_add_right : ∀ a b c : Int,
        //   Int.lt (Int.add a b) (Int.add c b) → Int.lt a c
        // Cancellation lemma: cancel common right addend for strict (#302).
        //
        // SOUNDNESS: Converted from Declaration::Axiom to Declaration::Theorem.
        // Commutes both addends of `h : Int.lt (a+b) (c+b)` to `Int.lt (b+a) (b+c)`
        // via two `@Eq.subst.{1}` rewrites over `Int.add_comm`, then cancels the
        // shared left addend `b` with the constructive
        // `Int.lt_of_add_lt_add_left b a c`, yielding `Int.lt a c`. See
        // `algebra_int_lt_of_add_lt_add_right_proof.rs`. Empty domain-axiom closure.
        self.register_int_lt_of_add_lt_add_right_proof()?;

        // Int.ofNat_zero_le : ∀ n : Nat, Int.le (Int.ofNat Nat.zero) (Int.ofNat n)
        // Nonneg witness for Int.ofNat of a natural number.
        // Required by compact Int multiplication scaling (#2630).
        //
        // SOUNDNESS: Converted from Declaration::Axiom to Declaration::Theorem.
        // The canonical constructor `@Int.NonNeg.mk n : Int.NonNeg (Int.ofNat n)`
        // inhabits the goal `Int.le (Int.ofNat 0) (Int.ofNat n)` ≡
        // `Int.NonNeg (Int.sub (Int.ofNat n) (Int.ofNat 0))` directly, since the
        // subtraction kernel-reduces to `Int.ofNat n`. See
        // `algebra_int_ofnat_zero_le_proof.rs`. Empty domain-axiom closure.
        self.register_int_ofnat_zero_le_proof()?;

        // Int.mul_nonneg : ∀ a b : Int,
        //   Int.le (Int.ofNat 0) a → Int.le (Int.ofNat 0) b →
        //   Int.le (Int.ofNat 0) (Int.mul a b)
        // Required by compact Int multiplication scaling (#2630).
        //
        // SOUNDNESS: Converted from Declaration::Axiom to Declaration::Theorem.
        // Double `@Int.NonNeg.rec.{0}` recursion on the two `Int.le 0 _`
        // hypotheses (each ≡ `Int.NonNeg _`) extracts the `Nat` witnesses `n`,
        // `m` and rebuilds `@Int.NonNeg.mk (Nat.mul n m)`, which inhabits the
        // goal `Int.le 0 (Int.mul (Int.ofNat n) (Int.ofNat m))` because
        // `Int.mul (Int.ofNat n) (Int.ofNat m)` reduces to
        // `Int.ofNat (Nat.mul n m)`. See `algebra_int_mul_nonneg_proof.rs`.
        // Empty domain-axiom closure.
        self.register_int_mul_nonneg_proof()?;

        // Int.mul_le_mul_of_nonneg_left : ∀ a b c : Int,
        //   Int.le a b → Int.le (Int.ofNat 0) c →
        //   Int.le (Int.mul c a) (Int.mul c b)
        // Core monotonicity lemma for compact Int scaling (#2630).
        //
        // SOUNDNESS: Converted from Declaration::Axiom to Declaration::Theorem.
        // Converts `Int.le 0 c` to `NonNeg c` (transport along `Int.add_zero`),
        // forms `Int.NonNeg.mul c (b-a) : NonNeg (c*(b-a))` (the `Int.le a b`
        // witness is `NonNeg (b-a)`), then transports along the constructive
        // distributivity bridge `c*(b-a) = c*b - c*a` to obtain
        // `NonNeg (c*b - c*a)` ≡ `Int.le (c*a) (c*b)`. See
        // `algebra_int_mul_le_mul_of_nonneg_left_proof.rs`. Empty domain-axiom
        // closure.
        self.register_int_mul_le_mul_of_nonneg_left_proof()?;

        // Int.mul_le_mul_of_nonneg_right : ∀ a b c : Int,
        //   Int.le a b → Int.le (Int.ofNat 0) c →
        //   Int.le (Int.mul a c) (Int.mul b c)
        // Right-multiplication mirror of the left monotonicity lemma (#3604).
        //
        // SOUNDNESS: Registered as Declaration::Theorem (not Axiom). Converts
        // `Int.le 0 c` to `NonNeg c` (transport along `Int.add_zero`), forms
        // `Int.NonNeg.mul (b-a) c : NonNeg ((b-a)*c)` (the `Int.le a b` witness
        // is `NonNeg (b-a)`), then transports along the constructive
        // distributivity bridge `(b-a)*c = b*c - a*c` to obtain
        // `NonNeg (b*c - a*c)` ≡ `Int.le (a*c) (b*c)`. See
        // `algebra_int_mul_le_mul_of_nonneg_right_proof.rs`. Empty domain-axiom
        // closure.
        self.register_int_mul_le_mul_of_nonneg_right_proof()?;

        // Int.mul_le_mul : ∀ a b c d : Int,
        //   Int.le a b → Int.le c d → Int.le (Int.ofNat 0) a →
        //   Int.le (Int.ofNat 0) c → Int.le (Int.mul a c) (Int.mul b d)
        // General ordered-ring product monotonicity (#3604).
        //
        // SOUNDNESS: Registered as Declaration::Theorem (not Axiom). Two
        // constructive monotonicity steps with a `Int.le_trans` midpoint at
        // `Int.mul b c`: `Int.mul_le_mul_of_nonneg_right a b c hab ha0`
        // (`a*c ≤ b*c`) and `Int.mul_le_mul_of_nonneg_left c d b hcd hb0`
        // (`b*c ≤ b*d`), where `hb0 : 0 ≤ b` is obtained from `0 ≤ a` and
        // `a ≤ b` by `Int.le_trans`. See `algebra_int_mul_le_mul_proof.rs`.
        // Empty domain-axiom closure.
        self.register_int_mul_le_mul_proof()?;

        // Int.mul_pos : ∀ a b : Int,
        //   Int.lt (Int.ofNat 0) a → Int.lt (Int.ofNat 0) b →
        //   Int.lt (Int.ofNat 0) (Int.mul a b)
        // Strict positivity of a product of positives (#3604).
        //
        // SOUNDNESS: Registered as Declaration::Theorem (not Axiom). From
        // `0 < a ≡ 1 ≤ a` and `0 < b ≡ 1 ≤ b` derives `1*1 ≤ a*b` via the
        // constructive `Int.mul_le_mul` (with `0 ≤ 1`), then transports along
        // `Int.one_mul 1 : 1*1 = 1` to obtain `1 ≤ a*b` ≡ `0 < a*b`. See
        // `algebra_int_mul_pos_proof.rs`. Empty domain-axiom closure.
        self.register_int_mul_pos_proof()?;

        self.int_ord_lemmas_init = true;
        Ok(())
    }

    /// Check if Int ordering lemmas have been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.int_ord_lemmas_init == true`
    pub(crate) fn has_int_ord_lemmas(&self) -> bool {
        self.int_ord_lemmas_init
    }

    /// Initialize LinearOrder instance for Int
    ///
    /// This adds:
    /// - instPreorderInt : Preorder Int — Declaration::Definition built from
    ///   `Preorder.mk @Int instLEInt instLTInt Int.le_refl Int.le_trans`
    /// - Int.lt_iff_le_not_le : axiom ∀ a b : Int, Iff (Int.lt a b) (And (Int.le a b) (Not (Int.le b a)))
    /// - instPartialOrderInt : PartialOrder Int — Declaration::Definition built from
    ///   `PartialOrder.mk @Int instPreorderInt Int.le_antisymm`
    /// - Int.le_total : theorem ∀ a b : Int, Or (Int.le a b) (Int.le b a)
    /// - instLinearOrderInt : axiom LinearOrder Int
    ///
    /// `instPreorderInt` is a `Declaration::Definition` (matching `instPreorderNat`
    /// #3553 and `instPreorderRat` #3222): a `Preorder` needs ONLY reflexivity and
    /// transitivity, and `Int.le_refl`/`Int.le_trans` are constructive empty-closure
    /// `Declaration::Theorem`s. The projection reduction `LE.le @Int instLEInt → Int.le`
    /// the value relies on is handled by the kernel (#3222), so no axiom is required.
    /// `instPartialOrderInt` is likewise a `Declaration::Definition` (matching
    /// `instPartialOrderRat` #3222): a `PartialOrder` extends a `Preorder` with only
    /// `le_antisymm`, and `Int.le_antisymm` is now itself a constructive empty-closure
    /// `Declaration::Theorem` (#2422, see `algebra_int_le_antisymm_proof.rs`). The
    /// `PartialOrder.mk` projection-reduction concern from #1526 was resolved by #3222
    /// (the same fix that demoted `instPreorderInt`), so no axiom is required.
    /// `Int.le_total` is now a constructive empty-closure `Declaration::Theorem`
    /// (#3599 follow-up, see `order_int_le_total_proof.rs`): an
    /// `@Int.rec`×`@Int.rec` case split routes the two same-sign branches through
    /// an inline `Int.subNatNat`-totality helper (double `Nat` induction) and
    /// closes the two mixed-sign branches definitionally with `@Int.NonNeg.mk`.
    /// `instLinearOrderInt` is now a `Declaration::Definition`
    /// (`LinearOrder.mk @Int instPartialOrderInt Int.le_total`, TCB-shrink
    /// Tier 1), mirroring the `instLinearOrderRat` sibling: the #1526
    /// projection-reduction gap was closed by #3222, and both `LinearOrder.mk`
    /// fields (`toPartialOrder`, `le_total`) are constructive empty-closure
    /// declarations, so no axiom is required.
    ///
    /// Requires: init_int_ord_lemmas() for le_refl, le_trans, le_antisymm
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_linear_order_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_linear_order(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, residual-to-zero
        // campaign 2026-07-03): part of the Clean-native Int cluster whose
        // definitions reference the suppressed Int arithmetic stubs
        // (`Int.le := NonNeg (b - a)`-shaped bodies use `Int.sub`). In import
        // mode the genuine olean declarations import instead. See
        // `init_int_arith` for the cluster rationale.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.int_linear_order_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_int_ord_lemmas()?; // Provides Int.le_refl, Int.le_trans, Int.le_antisymm
        self.init_preorder()?; // Provides Preorder typeclass
        self.init_partial_order()?; // Provides PartialOrder typeclass
        self.init_linear_order()?; // Provides LinearOrder typeclass
        self.init_iff()?; // Provides Iff (used by Int.lt_iff_le_not_le)
        self.init_and()?; // Provides And (used by lt_iff_le_not_le body)
        self.init_true_false()?; // Provides Not (used by lt_iff_le_not_le body)

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let le_const = Expr::const_(Name::from_string("Int.le"), vec![]);
        let lt_const = Expr::const_(Name::from_string("Int.lt"), vec![]);

        // ========================================
        // instPreorderInt : Preorder Int
        //   := Preorder.mk @Int instLEInt instLTInt Int.le_refl Int.le_trans
        // ========================================
        // SOUNDNESS: Declaration::Definition (not Axiom) carrying the real
        // instance value. A `Preorder` requires only reflexivity and
        // transitivity, both supplied by the constructive empty-closure
        // theorems `Int.le_refl` / `Int.le_trans` (registered above by
        // `init_int_ord_lemmas`, see `algebra_int_le_refl_proof.rs` /
        // `algebra_int_le_trans_proof.rs`). Those lemmas are stated in raw
        // `Int.le a b` form; `Preorder.mk`'s fields expect `LE.le @Int
        // instLEInt a b`, and the kernel reduces the latter to the former by
        // δ-unfolding the reducible `instLEInt = LE.mk Int.le` and projection
        // reduction (#3222 — the same fix that converted `instPreorderRat`
        // from Axiom to Definition). No domain-specific axiom enters the
        // value: neither `Int.le_antisymm` nor totality is needed for a
        // Preorder, so the #2422 boundary is not crossed.
        let inst_preorder_int_type = Expr::app(
            Expr::const_(Name::from_string("Preorder"), vec![Level::zero()]),
            int_const.clone(),
        );

        // Preorder.mk.{0} Int instLEInt instLTInt Int.le_refl Int.le_trans
        let inst_preorder_int_value = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Preorder.mk"), vec![Level::zero()]),
                            int_const.clone(), // α = Int
                        ),
                        Expr::const_(Name::from_string("instLEInt"), vec![]), // [LE Int]
                    ),
                    Expr::const_(Name::from_string("instLTInt"), vec![]), // [LT Int]
                ),
                Expr::const_(Name::from_string("Int.le_refl"), vec![]),
            ),
            Expr::const_(Name::from_string("Int.le_trans"), vec![]),
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instPreorderInt"),
            level_params: vec![],
            type_: inst_preorder_int_type,
            value: inst_preorder_int_value,
            is_reducible: true,
        })?;

        // ========================================
        // Int.lt_iff_le_not_le : ∀ a b : Int, Iff (Int.lt a b) (And (Int.le a b) (Not (Int.le b a)))
        // ========================================
        let iff_const = Expr::const_(Name::from_string("Iff"), vec![]);
        let and_const = Expr::const_(Name::from_string("And"), vec![]);
        let not_const = Expr::const_(Name::from_string("Not"), vec![]);

        let lt_iff_le_not_le_type = {
            let mut bld = EnvDeclBuilder::new();
            let (a_id, a) = bld.fresh_local(int_const.clone());
            let (b_id, bv) = bld.fresh_local(int_const.clone());
            let lt_ab = Expr::app(Expr::app(lt_const.clone(), a.clone()), bv.clone());
            let le_ab = Expr::app(Expr::app(le_const.clone(), a.clone()), bv.clone());
            let le_ba = Expr::app(Expr::app(le_const.clone(), bv), a);
            let r = Expr::app(
                Expr::app(iff_const.clone(), lt_ab),
                Expr::app(
                    Expr::app(and_const.clone(), le_ab),
                    Expr::app(not_const.clone(), le_ba),
                ),
            );
            let r = bld.mk_pi(b_id, BinderInfo::Default, int_const.clone(), r);
            let r = bld.mk_pi(a_id, BinderInfo::Default, int_const.clone(), r);
            bld.finish(r)
        };

        // ELIMINATION: `Int.lt_iff_le_not_le` is now a kernel-checked Constructive
        // Theorem (`algebra_int_lt_iff_le_not_le_proof.rs`). Registered here first
        // (its deps are below `init_int_linear_order`, no recursion); the axiom
        // block is guarded and skips. This also flips the downstream
        // `Rat.lt_iff_le_not_le` from AxiomDependent toward Constructive.
        self.register_int_lt_iff_le_not_le_proof()?;
        if self
            .get_const(&Name::from_string("Int.lt_iff_le_not_le"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Int.lt_iff_le_not_le"),
                level_params: vec![],
                type_: lt_iff_le_not_le_type,
            })?;
        }

        // ========================================
        // instPartialOrderInt : PartialOrder Int
        //   := PartialOrder.mk @Int instPreorderInt Int.le_antisymm
        // ========================================
        // SOUNDNESS: Declaration::Definition (not Axiom) carrying the real
        // instance value. A `PartialOrder` extends a `Preorder` with exactly one
        // additional field, `le_antisymm`. The base `Preorder` is supplied by the
        // constructive empty-closure `instPreorderInt` Definition (registered
        // above), and antisymmetry is supplied by `Int.le_antisymm` — now itself a
        // constructive empty-closure `Declaration::Theorem` (#2422, see
        // `algebra_int_le_antisymm_proof.rs`). `Int.le_antisymm` is stated in raw
        // `∀ a b, Int.le a b → Int.le b a → Eq Int a b` form; `PartialOrder.mk`'s
        // `le_antisymm` field expects `LE.le @Int (Preorder.toLE @Int
        // instPreorderInt) a b`, and the kernel reduces the latter to the former by
        // δ-unfolding the reducible `instPreorderInt = Preorder.mk @Int instLEInt
        // …` and `instLEInt = LE.mk Int.le`, then projection reduction (#3222 — the
        // same fix that converted `instPartialOrderRat` and `instPreorderInt` from
        // Axiom to Definition). No domain-specific axiom enters the value: neither
        // totality nor decidable Int comparison is needed for a PartialOrder, so the
        // axiom_deps closure stays empty (the soundness invariant).
        let inst_partial_order_int_type = Expr::app(
            Expr::const_(Name::from_string("PartialOrder"), vec![Level::zero()]),
            int_const.clone(),
        );

        // PartialOrder.mk.{0} Int instPreorderInt Int.le_antisymm
        let inst_partial_order_int_value = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("PartialOrder.mk"), vec![Level::zero()]),
                    int_const.clone(), // α = Int
                ),
                Expr::const_(Name::from_string("instPreorderInt"), vec![]), // [Preorder Int]
            ),
            Expr::const_(Name::from_string("Int.le_antisymm"), vec![]),
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instPartialOrderInt"),
            level_params: vec![],
            type_: inst_partial_order_int_type,
            value: inst_partial_order_int_value,
            is_reducible: true,
        })?;

        // ========================================
        // Int.le_total : ∀ a b : Int, Or (Int.le a b) (Int.le b a)
        // ========================================
        // SOUNDNESS: constructive `Declaration::Theorem` (#3599 follow-up),
        // NOT an Axiom. The proof is a `@Int.rec`×`@Int.rec` case split whose
        // two same-sign branches reduce to an inline `Int.subNatNat`-totality
        // helper (double `Nat` induction lifting through
        // `Int.subNatNat_succ_succ`, transported onto `Int.sub` via
        // `Int.subNatNat_eq_add`), and whose two mixed-sign branches close
        // definitionally with `@Int.NonNeg.mk`. Its transitive axiom closure is
        // empty (constructive). See `order_int_le_total_proof.rs`. Unblocked by
        // the constructive `Nat.le_total` (#3599) and `Int.le_antisymm` (#2422).
        self.register_int_le_total_proof()?;

        // ========================================
        // instLinearOrderInt : LinearOrder Int
        //   := LinearOrder.mk @Int instPartialOrderInt Int.le_total
        // ========================================
        // SOUNDNESS: Declaration::Definition (not Axiom) carrying the real
        // instance value (TCB-shrink Tier 1). A `LinearOrder` in THIS kernel is
        // `LinearOrder.mk : {α} → [PartialOrder α] → (le_total : ∀ a b, a ≤ b ∨ b
        // ≤ a) → LinearOrder α` — exactly two fields, `toPartialOrder` and
        // `le_total` (there are no decidable fields). Both are now available as
        // constructive empty-closure declarations registered above:
        // `instPartialOrderInt` is a `Declaration::Definition` and `Int.le_total`
        // is a constructive `Declaration::Theorem` (`order_int_le_total_proof.rs`).
        // `Int.le_total` is stated in raw `∀ a b, Or (Int.le a b) (Int.le b a)`
        // form; `LinearOrder.mk`'s `le_total` field expects the typeclass form
        // `LE.le @Int (Preorder.toLE @Int (PartialOrder.toPreorder @Int
        // instPartialOrderInt)) a b`, and the kernel reduces the latter to the
        // former by δ-unfolding the reducible instance chain `instPartialOrderInt
        // = PartialOrder.mk @Int instPreorderInt … → instPreorderInt =
        // Preorder.mk @Int instLEInt … → instLEInt = LE.mk Int.le` and projection
        // reduction (the same #3222 fix that converted `instLinearOrderRat` from
        // Axiom to Definition — this mirrors that sibling). No domain-specific
        // axiom enters the value: the previous projection-reduction-gap concern
        // (#1526) was resolved by #3222, so the axiom is no longer required and
        // the `axiom_deps` closure stays empty.
        let inst_linear_order_int_type = Expr::app(
            Expr::const_(Name::from_string("LinearOrder"), vec![Level::zero()]),
            int_const.clone(),
        );

        // LinearOrder.mk.{0} Int instPartialOrderInt Int.le_total
        let inst_linear_order_int_value = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LinearOrder.mk"), vec![Level::zero()]),
                    int_const.clone(), // α = Int
                ),
                Expr::const_(Name::from_string("instPartialOrderInt"), vec![]), // [PartialOrder Int]
            ),
            Expr::const_(Name::from_string("Int.le_total"), vec![]),
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instLinearOrderInt"),
            level_params: vec![],
            type_: inst_linear_order_int_type,
            value: inst_linear_order_int_value,
            is_reducible: true,
        })?;

        self.int_linear_order_init = true;
        Ok(())
    }

    /// Check if Int LinearOrder instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.int_linear_order_init == true`
    pub(crate) fn has_int_linear_order(&self) -> bool {
        self.int_linear_order_init
    }
}
