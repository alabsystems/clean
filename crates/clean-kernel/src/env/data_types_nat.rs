// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Numeric data type initialization: Bool, Nat, Int
//!
//! Split from `data_types.rs` for #307 (large file splitting).
//! Basic algebraic types (Option, Sum, etc.) remain in `data_types.rs`.
//! Collection types (ULift, Char, List, String) are in `data_types_collections.rs`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    pub(crate) fn bool_surface_missing_symbol(&self) -> Option<Name> {
        const BOOL_SURFACE_SYMBOLS: [&str; 9] = [
            "Bool",
            "Bool.false",
            "Bool.true",
            "Bool.not",
            "Bool.and",
            "Bool.or",
            "Bool.xor",
            "true",
            "false",
        ];

        BOOL_SURFACE_SYMBOLS
            .iter()
            // IMPORT MODE: `Bool.xor` is import-suppressed (drifted value —
            // see register_bool_surface); its absence is expected there.
            .filter(|symbol| !(self.suppress_lossy_structure_stubs && **symbol == "Bool.xor"))
            .map(|symbol| Name::from_string(symbol))
            .find(|name| self.get_const(name).is_none())
    }

    pub(crate) fn bool_surface_ready(&self) -> bool {
        self.bool_surface_missing_symbol().is_none()
    }

    pub(crate) fn register_bool_surface(&mut self) -> Result<(), EnvError> {
        let bool_type = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

        let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);

        // Bool.false : Bool
        let bool_false_type = bool_const.clone();

        // Bool.true : Bool
        let bool_true_type = bool_const.clone();

        // Skip the inductive registration if Bool already exists in the
        // environment (e.g., registered through the spec's add_inductive path).
        // Part of #3333.
        if self.get_inductive(&Name::from_string("Bool")).is_none() {
            let bool_decl = InductiveDecl {
                level_params: vec![],
                num_params: 0,
                types: vec![InductiveType {
                    name: Name::from_string("Bool"),
                    type_: bool_type,
                    constructors: vec![
                        Constructor {
                            name: Name::from_string("Bool.false"),
                            type_: bool_false_type,
                        },
                        Constructor {
                            name: Name::from_string("Bool.true"),
                            type_: bool_true_type,
                        },
                    ],
                }],
            };
            self.add_inductive(bool_decl)?;
        }

        // Add Bool.not : Bool → Bool
        // Bool.not b := Bool.rec Bool.true Bool.false b
        let bool_not_type = Expr::pi(BinderInfo::Default, bool_const.clone(), bool_const.clone());

        // Bool.rec : {motive : Bool → Sort u} → motive Bool.false → motive Bool.true → (t : Bool) → motive t
        // For Bool.not, motive is (λ _ : Bool => Bool), so:
        // Bool.rec Bool Bool.true Bool.false b : Bool
        let bool_rec = Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        );
        let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);

        // motive: λ _ : Bool => Bool
        let motive = Expr::lam(BinderInfo::Default, bool_const.clone(), bool_const.clone());

        // Bool.not := λ b : Bool => Bool.rec motive Bool.true Bool.false b
        let bool_not_value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(bool_const.clone());
            let body = Expr::apps(
                bool_rec.clone(),
                [motive.clone(), bool_true.clone(), bool_false.clone(), x],
            );
            let e = b.mk_lam(x_id, BinderInfo::Default, bool_const.clone(), body);
            b.finish(e)
        };

        // Use add_decl_if_absent for all surface definitions so that
        // register_bool_surface is idempotent when Bool was already registered
        // through a different code path (e.g., spec's add_inductive).
        // Part of #3333.
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string("Bool.not"),
            level_params: vec![],
            type_: bool_not_type,
            value: bool_not_value,
            is_reducible: true,
        })?;

        // Add Bool.and : Bool → Bool → Bool
        // Bool.and a b := Bool.rec Bool.false b a
        // (if a is false, result is false; if a is true, result is b)
        let bool_and_type = Expr::pi(
            BinderInfo::Default,
            bool_const.clone(),
            Expr::pi(BinderInfo::Default, bool_const.clone(), bool_const.clone()),
        );

        // Bool.and := λ a b : Bool => Bool.rec (λ _ => Bool) Bool.false b a
        let bool_and_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(bool_const.clone());
            let (bv_id, bv) = b.fresh_local(bool_const.clone());
            let body = Expr::apps(
                bool_rec.clone(),
                [motive.clone(), bool_false.clone(), bv, a],
            );
            let e = b.mk_lam(bv_id, BinderInfo::Default, bool_const.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, bool_const.clone(), e);
            b.finish(e)
        };

        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string("Bool.and"),
            level_params: vec![],
            type_: bool_and_type,
            value: bool_and_value,
            is_reducible: true,
        })?;

        // Add Bool.or : Bool → Bool → Bool
        // Bool.or a b := Bool.rec b Bool.true a
        // (if a is false, result is b; if a is true, result is true)
        let bool_or_type = Expr::pi(
            BinderInfo::Default,
            bool_const.clone(),
            Expr::pi(BinderInfo::Default, bool_const.clone(), bool_const.clone()),
        );

        // Bool.or := λ a b : Bool => Bool.rec (λ _ => Bool) b Bool.true a
        let bool_or_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(bool_const.clone());
            let (bv_id, bv) = b.fresh_local(bool_const.clone());
            let body = Expr::apps(bool_rec.clone(), [motive.clone(), bv, bool_true.clone(), a]);
            let e = b.mk_lam(bv_id, BinderInfo::Default, bool_const.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, bool_const.clone(), e);
            b.finish(e)
        };

        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string("Bool.or"),
            level_params: vec![],
            type_: bool_or_type,
            value: bool_or_value,
            is_reducible: true,
        })?;

        // Add Bool.xor : Bool → Bool → Bool
        // Bool.xor a b := Bool.rec b (Bool.not b) a
        // (if a is false, result is b; if a is true, result is not b)
        let bool_xor_type = Expr::pi(
            BinderInfo::Default,
            bool_const.clone(),
            Expr::pi(BinderInfo::Default, bool_const.clone(), bool_const.clone()),
        );

        let bool_not_const = Expr::const_(Name::from_string("Bool.not"), vec![]);

        // Bool.xor := λ a b : Bool => Bool.rec (λ _ => Bool) b (Bool.not b) a
        let bool_xor_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(bool_const.clone());
            let (bv_id, bv) = b.fresh_local(bool_const.clone());
            let body = Expr::apps(
                bool_rec.clone(),
                [
                    motive.clone(),
                    bv.clone(),
                    Expr::app(bool_not_const.clone(), bv),
                    a,
                ],
            );
            let e = b.mk_lam(bv_id, BinderInfo::Default, bool_const.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, bool_const.clone(), e);
            b.finish(e)
        };

        // IMPORT MODE (v4.31 retarget 2026-07-04): genuine v4.31 `Bool.xor`
        // is `@bne Bool (instBEqOfDecidableEq Bool instDecidableEqBool)` —
        // Clean's Bool.rec-based value is delta-incompatible (rfl-proofs of
        // `Bool.xor = bne` and the Nat/Int bitwise lemma family reject).
        // Import-suppressed so the genuine olean definition imports.
        if !self.suppress_lossy_structure_stubs {
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string("Bool.xor"),
                level_params: vec![],
                type_: bool_xor_type,
                value: bool_xor_value,
                is_reducible: true,
            })?;
        }

        // Add `true` and `false` aliases (Lean 4 compatibility)
        // These are abbreviations that unfold to Bool.true and Bool.false
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string("true"),
            level_params: vec![],
            type_: bool_const.clone(),
            value: bool_true.clone(),
            is_reducible: true,
        })?;

        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string("false"),
            level_params: vec![],
            type_: bool_const.clone(),
            value: bool_false.clone(),
            is_reducible: true,
        })?;

        // Bare `and`/`or` aliases for the Bool `&&`/`||` operators (Lean 4
        // compatibility). The surface parser lowers `a && b` to `and a b` and
        // `a || b` to `or a b`; these reducible defs unfold to Bool.and/Bool.or
        // so the operators elaborate and compute (Eq.refl). Part of Track N.
        let bool_binop_type = Expr::pi(
            BinderInfo::Default,
            bool_const.clone(),
            Expr::pi(BinderInfo::Default, bool_const.clone(), bool_const.clone()),
        );
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string("and"),
            level_params: vec![],
            type_: bool_binop_type.clone(),
            value: Expr::const_(Name::from_string("Bool.and"), vec![]),
            is_reducible: true,
        })?;
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string("or"),
            level_params: vec![],
            type_: bool_binop_type,
            value: Expr::const_(Name::from_string("Bool.or"), vec![]),
            is_reducible: true,
        })?;

        Ok(())
    }

    /// Initialize Bool (boolean type)
    ///
    /// Bool : Type
    /// inductive Bool where
    ///   | false : Bool
    ///   | true : Bool
    ///
    /// Also adds derived definitions:
    /// - Bool.not : Bool → Bool
    /// - Bool.and : Bool → Bool → Bool
    /// - Bool.or : Bool → Bool → Bool
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.bool_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_bool(&mut self) -> Result<(), EnvError> {
        if self.bool_init {
            return Ok(());
        }
        if !self.bool_surface_ready() {
            self.register_bool_surface()?;
        }

        self.init_sorry_ax()?;
        self.bool_init = true;
        Ok(())
    }

    /// Check if Bool has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_bool` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_bool(&self) -> bool {
        self.bool_init
    }

    /// Initialize Nat (natural numbers)
    ///
    /// Nat : Type
    /// inductive Nat where
    ///   | zero : Nat
    ///   | succ (n : Nat) : Nat
    ///
    /// Also adds derived definitions:
    /// - Nat.add : Nat → Nat → Nat
    /// - Nat.mul : Nat → Nat → Nat
    /// - Nat.pred : Nat → Nat
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_nat(&mut self) -> Result<(), EnvError> {
        if self.nat_init {
            return Ok(());
        }

        // Nat : Type
        let nat_type = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

        // Nat.zero : Nat
        let nat_zero_type = nat_const.clone();

        // Nat.succ : Nat → Nat
        let nat_succ_type = Expr::pi(BinderInfo::Default, nat_const.clone(), nat_const.clone());

        // Skip the inductive registration if Nat already exists in the
        // environment (e.g., registered through the spec's add_inductive path).
        // Part of #3333.
        if self.get_inductive(&Name::from_string("Nat")).is_none() {
            let nat_decl = InductiveDecl {
                level_params: vec![],
                num_params: 0,
                types: vec![InductiveType {
                    name: Name::from_string("Nat"),
                    type_: nat_type,
                    constructors: vec![
                        Constructor {
                            name: Name::from_string("Nat.zero"),
                            type_: nat_zero_type,
                        },
                        Constructor {
                            name: Name::from_string("Nat.succ"),
                            type_: nat_succ_type,
                        },
                    ],
                }],
            };
            self.add_inductive(nat_decl)?;
        }

        // Add Nat.pred : Nat → Nat
        // Nat.pred n := Nat.rec Nat.zero (λ m _ => m) n
        let nat_pred_type = Expr::pi(BinderInfo::Default, nat_const.clone(), nat_const.clone());

        // Nat.rec : {motive : Nat → Sort u} → motive Nat.zero → ((n : Nat) → motive n → motive (Nat.succ n)) → (t : Nat) → motive t
        let nat_rec = Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        );
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

        // motive: λ _ : Nat => Nat
        let motive = Expr::lam(BinderInfo::Default, nat_const.clone(), nat_const.clone());

        // Nat.pred := λ n : Nat => Nat.rec motive Nat.zero (λ m _ => m) n
        let nat_pred_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            // succ case: λ m : Nat => λ _ : Nat => m
            let (m_id, m) = b.fresh_local(nat_const.clone());
            let (ih_id, _ih) = b.fresh_local(nat_const.clone());
            let succ_case = b.mk_lam(ih_id, BinderInfo::Default, nat_const.clone(), m);
            let succ_case = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), succ_case);
            let body = Expr::apps(
                nat_rec.clone(),
                [motive.clone(), nat_zero.clone(), succ_case, n],
            );
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            b.finish(e)
        };

        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string("Nat.pred"),
            level_params: vec![],
            type_: nat_pred_type,
            value: nat_pred_value,
            is_reducible: true,
        })?;

        // Add Nat.add : Nat → Nat → Nat
        // Nat.add m n := Nat.rec m (λ _ ih => Nat.succ ih) n
        let nat_add_type = Expr::pi(
            BinderInfo::Default,
            nat_const.clone(),
            Expr::pi(BinderInfo::Default, nat_const.clone(), nat_const.clone()),
        );

        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);

        // Nat.add := λ m n : Nat => Nat.rec motive m (λ _ ih => Nat.succ ih) n
        let nat_add_value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat_const.clone());
            let (n_id, n) = b.fresh_local(nat_const.clone());
            // succ case: λ _ : Nat => λ ih : Nat => Nat.succ ih
            let (k_id, _k) = b.fresh_local(nat_const.clone());
            let (ih_id, ih) = b.fresh_local(nat_const.clone());
            let add_succ = b.mk_lam(
                ih_id,
                BinderInfo::Default,
                nat_const.clone(),
                Expr::app(nat_succ.clone(), ih),
            );
            let add_succ = b.mk_lam(k_id, BinderInfo::Default, nat_const.clone(), add_succ);
            let body = Expr::apps(nat_rec.clone(), [motive.clone(), m, add_succ, n]);
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            let e = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.30 census
        // 2026-07-06, pinpoint dcb769d4): the Nat CORE ARITHMETIC seed cluster
        // (Nat.add/mul/sub/divCore/div/modCore/mod/pow here; Nat.beq/ble/blt in
        // order_nat_cmp.rs) diverges from Lean v4.30's genuine bodies — Lean
        // stores brecOn towers (add/mul/sub/pow), structural Nat.modCore and
        // @[irreducible] WF div/mod, while Clean seeds direct Nat.rec
        // eliminations and a fuel-peeling div/mod dispatcher. On olean import
        // every seeded twin fails the incremental-verify value-defeq dedup
        // ("duplicate of seeded constant Nat.add/…"; Nat.modCore even at the
        // TYPE level — Clean's is fuel-arity 3, Lean's arity 2), blocking the
        // genuine defs and cascading the eq_def/lemma web; worse, whnf digging
        // into the seeded mod/div dispatcher unary-peels 2^32-scale literals
        // (Char.toUpper._proof_1 burned its whole 2M heartbeat budget on
        // 1,999,814 Nat.rec iota steps — the 91-row heartbeat census class).
        // SOUNDNESS: the gate only WITHHOLDS the Clean-native seeds in the
        // import-only prelude so the genuine olean definitions register through
        // the checked add_decl path; the default lane is byte-identical. The
        // Nat inductive, Nat.pred (defeq to Lean's match-compiled body — passes
        // the import dedup), and the value-less upgradeable axioms below stay
        // in both lanes.
        if !self.suppress_lossy_structure_stubs {
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string("Nat.add"),
                level_params: vec![],
                type_: nat_add_type,
                value: nat_add_value,
                is_reducible: true,
            })?;
        }

        // Add Nat.mul : Nat → Nat → Nat
        // Nat.mul m n := Nat.rec Nat.zero (λ _ ih => Nat.add ih m) n
        let nat_mul_type = Expr::pi(
            BinderInfo::Default,
            nat_const.clone(),
            Expr::pi(BinderInfo::Default, nat_const.clone(), nat_const.clone()),
        );

        let nat_add_const = Expr::const_(Name::from_string("Nat.add"), vec![]);

        // Nat.mul := λ m n : Nat => Nat.rec motive Nat.zero (λ _ ih => Nat.add ih m) n
        let nat_mul_value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat_const.clone());
            let (n_id, n) = b.fresh_local(nat_const.clone());
            // succ case: λ _ : Nat => λ ih : Nat => Nat.add ih m
            let (k_id, _k) = b.fresh_local(nat_const.clone());
            let (ih_id, ih) = b.fresh_local(nat_const.clone());
            let mul_succ = b.mk_lam(
                ih_id,
                BinderInfo::Default,
                nat_const.clone(),
                Expr::app(Expr::app(nat_add_const.clone(), ih), m.clone()),
            );
            let mul_succ = b.mk_lam(k_id, BinderInfo::Default, nat_const.clone(), mul_succ);
            let body = Expr::apps(
                nat_rec.clone(),
                [motive.clone(), nat_zero.clone(), mul_succ, n],
            );
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            let e = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: import-mode Nat core arithmetic cluster gate (see Nat.add above).
        if !self.suppress_lossy_structure_stubs {
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string("Nat.mul"),
                level_params: vec![],
                type_: nat_mul_type,
                value: nat_mul_value,
                is_reducible: true,
            })?;
        }

        // Add Nat.sub : Nat → Nat → Nat (truncated subtraction)
        // Nat.sub m n := Nat.rec m (λ _ ih => Nat.pred ih) n
        // This computes: sub m 0 = m, sub m (succ n) = pred (sub m n)
        let nat_sub_type = Expr::pi(
            BinderInfo::Default,
            nat_const.clone(),
            Expr::pi(BinderInfo::Default, nat_const.clone(), nat_const.clone()),
        );

        let nat_pred_const = Expr::const_(Name::from_string("Nat.pred"), vec![]);

        // Nat.sub := λ m n : Nat => Nat.rec motive m (λ _ ih => Nat.pred ih) n
        let nat_sub_value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat_const.clone());
            let (n_id, n) = b.fresh_local(nat_const.clone());
            // succ case: λ _ : Nat => λ ih : Nat => Nat.pred ih
            let (k_id, _k) = b.fresh_local(nat_const.clone());
            let (ih_id, ih) = b.fresh_local(nat_const.clone());
            let sub_succ = b.mk_lam(
                ih_id,
                BinderInfo::Default,
                nat_const.clone(),
                Expr::app(nat_pred_const.clone(), ih),
            );
            let sub_succ = b.mk_lam(k_id, BinderInfo::Default, nat_const.clone(), sub_succ);
            let body = Expr::apps(nat_rec.clone(), [motive.clone(), m, sub_succ, n]);
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            let e = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: import-mode Nat core arithmetic cluster gate (see Nat.add above).
        if !self.suppress_lossy_structure_stubs {
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string("Nat.sub"),
                level_params: vec![],
                type_: nat_sub_type,
                value: nat_sub_value,
                is_reducible: true,
            })?;
        }

        // Add Nat.div / Nat.mod : Nat → Nat → Nat
        //
        // These are well-founded-recursive in Lean 4 and have no closed
        // structural-recursion (`Nat.rec`) form, so unlike Nat.add/mul/sub they
        // cannot be given a computing structural body here. Ground-term
        // computation is handled by the native reducer in `reduce_nat`
        // (`Nat.div n 0 = 0`, `Nat.mod n 0 = n`, otherwise truncating div / rem).
        //
        // Previously they were registered ONLY as native-reducer names, so
        // `Nat.div` / `Nat.mod` did not exist as constants and dot-notation
        // (`Nat.mod`, `Nat.div`, and the `%` / `/` HMod/HDiv notations that
        // desugar to them) failed with "dot notation on type-valued
        // expression". Register them as `Opaque` declarations: opaque bodies are
        // kernel-checked (axiom-free, no `sorry`) but never delta-unfold, so the
        // honest placeholder body cannot be confused with the native reducer's
        // result on literals (a `Definition` body would let symbolic `Nat.div n 1`
        // delta-reduce to the placeholder while `Nat.div 6 1` natively reduces to
        // `6` — a `6 = <placeholder>` defeq hazard). Symbolic applications stay
        // stuck; only ground literals reduce, via the trusted native path. (Track TAC)
        let nat_binop_ty = Expr::pi(
            BinderInfo::Default,
            nat_const.clone(),
            Expr::pi(BinderInfo::Default, nat_const.clone(), nat_const.clone()),
        );
        // Trust: register `Nat.div` as a GENUINE structural definition too
        // (replacing the opaque placeholder), so div value-properties (e.g.
        // `Nat.div a n <= a`, the euclidean `n * (a/n) + a % n = a`) become
        // provable. SOUND for the same reason as `Nat.mod` below: the native
        // reducer preempts delta for ground terms, and symbolic `Nat.div a n`
        // unfolds to a `Nat.rec`-on-fuel term that stays stuck on the free fuel.
        //
        //   Nat.divCore fuel a n   (fuel-bounded, fuel = a)
        //     divCore 0        a n = 0
        //     divCore (succ f) a n = if n <= a then succ (divCore f (a - n) n) else 0
        //   Nat.div a 0        = 0                        -- guard: match native `div n 0 = 0`
        //   Nat.div a (succ k) = Nat.divCore a a (succ k)
        // `n <= a` is the inline `Nat.rec _ (n - a)` test (n - a = 0 iff n <= a),
        // so no Bool.rec / Nat.ble dependency at this init point.
        let nat_sub_const = Expr::const_(Name::from_string("Nat.sub"), vec![]);
        let nat_arrow_nat = Expr::pi(
            BinderInfo::Default,
            nat_const.clone(),
            Expr::pi(BinderInfo::Default, nat_const.clone(), nat_const.clone()),
        );
        let divcore_motive = Expr::lam(
            BinderInfo::Default,
            nat_const.clone(),
            nat_arrow_nat.clone(),
        );
        let nat_divcore_type = Expr::pi(
            BinderInfo::Default,
            nat_const.clone(),
            Expr::pi(
                BinderInfo::Default,
                nat_const.clone(),
                Expr::pi(BinderInfo::Default, nat_const.clone(), nat_const.clone()),
            ),
        );
        let nat_divcore_value = {
            let mut b = EnvDeclBuilder::new();
            // base (fuel 0): λ a n => 0
            let (ba_id, _ba) = b.fresh_local(nat_const.clone());
            let (bn_id, _bn) = b.fresh_local(nat_const.clone());
            let base = b.mk_lam(
                bn_id,
                BinderInfo::Default,
                nat_const.clone(),
                nat_zero.clone(),
            );
            let base = b.mk_lam(ba_id, BinderInfo::Default, nat_const.clone(), base);
            // step: λ f ih a n => Nat.rec (λ _=>Nat) (succ (ih (a-n) n)) (λ _ _ => 0) (n - a)
            let (sf_id, _sf) = b.fresh_local(nat_const.clone());
            let (ih_id, ih) = b.fresh_local(nat_arrow_nat.clone());
            let (sa_id, sa) = b.fresh_local(nat_const.clone());
            let (sn_id, sn) = b.fresh_local(nat_const.clone());
            let a_minus_n = Expr::apps(nat_sub_const.clone(), [sa.clone(), sn.clone()]);
            let n_minus_a = Expr::apps(nat_sub_const.clone(), [sn.clone(), sa.clone()]);
            let recurse = Expr::app(nat_succ.clone(), Expr::apps(ih, [a_minus_n, sn.clone()]));
            let (ik_id, _ik) = b.fresh_local(nat_const.clone());
            let (iih_id, _iih) = b.fresh_local(nat_const.clone());
            let inner_step = b.mk_lam(
                iih_id,
                BinderInfo::Default,
                nat_const.clone(),
                nat_zero.clone(),
            );
            let inner_step = b.mk_lam(ik_id, BinderInfo::Default, nat_const.clone(), inner_step);
            let cond = Expr::apps(
                nat_rec.clone(),
                [motive.clone(), recurse, inner_step, n_minus_a],
            );
            let step = b.mk_lam(sn_id, BinderInfo::Default, nat_const.clone(), cond);
            let step = b.mk_lam(sa_id, BinderInfo::Default, nat_const.clone(), step);
            let step = b.mk_lam(ih_id, BinderInfo::Default, nat_arrow_nat.clone(), step);
            let step = b.mk_lam(sf_id, BinderInfo::Default, nat_const.clone(), step);
            let (f_id, f) = b.fresh_local(nat_const.clone());
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let reccall = Expr::apps(nat_rec.clone(), [divcore_motive.clone(), base, step, f]);
            let body = Expr::apps(reccall, [a, n]);
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };
        // SOUNDNESS: import-mode Nat core arithmetic cluster gate (see Nat.add
        // above). Nat.divCore is Clean-only but its value references the gated
        // Nat.sub (absent at seed time in import mode), so it rides the gate.
        if !self.suppress_lossy_structure_stubs {
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string("Nat.divCore"),
                level_params: vec![],
                type_: nat_divcore_type,
                value: nat_divcore_value,
                is_reducible: true,
            })?;
        }
        // Nat.div := λ a n => Nat.rec (λ _ => Nat) 0 (λ nPred _ => Nat.divCore a a (succ nPred)) n
        let nat_divcore_const = Expr::const_(Name::from_string("Nat.divCore"), vec![]);
        let nat_div_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (n_id, n) = b.fresh_local(nat_const.clone());
            // guard step (n = succ nPred): λ nPred _ => Nat.divCore a a (succ nPred)
            let (np_id, np) = b.fresh_local(nat_const.clone());
            let (npih_id, _npih) = b.fresh_local(nat_const.clone());
            let succ_np = Expr::app(nat_succ.clone(), np);
            let dcall = Expr::apps(nat_divcore_const.clone(), [a.clone(), a.clone(), succ_np]);
            let gstep = b.mk_lam(npih_id, BinderInfo::Default, nat_const.clone(), dcall);
            let gstep = b.mk_lam(np_id, BinderInfo::Default, nat_const.clone(), gstep);
            let body = Expr::apps(
                nat_rec.clone(),
                [motive.clone(), nat_zero.clone(), gstep, n],
            );
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };
        // SOUNDNESS: import-mode Nat core arithmetic cluster gate (see Nat.add above).
        if !self.suppress_lossy_structure_stubs {
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string("Nat.div"),
                level_params: vec![],
                type_: nat_binop_ty.clone(),
                value: nat_div_value,
                is_reducible: true,
            })?;
        }

        // Trust: register `Nat.mod` as a GENUINE structural definition (replacing
        // the opaque placeholder) so `Nat.mod_lt` is provable on the surface and
        // value-range facts like `(a + b) % 2^w < 2^w` become reachable. SOUND:
        // the native reducer fires before delta in whnf, so ground `Nat.mod m k`
        // still uses the trusted native path (no `placeholder` defeq hazard), and
        // symbolic `Nat.mod a n` unfolds to a `Nat.rec`-on-fuel term that stays
        // STUCK on the free fuel argument. `Nat.div` stays Opaque (untouched).
        //
        //   Nat.modCore fuel a n  -- fuel-bounded; `fuel = a` guarantees enough
        //     modCore 0        a n = a
        //     modCore (succ f) a n = if n <= a then modCore f (a - n) n else a
        //   Nat.mod a n = Nat.modCore a a n
        //
        // The test `n <= a` is done inline as `Nat.rec _ (n - a)` (n - a = 0 iff
        // n <= a), so no Bool.rec / Nat.ble dependency is needed at this init
        // point. (mod by zero: `n - a = 0` is always true at n = 0, so it recurses
        // with `a - 0 = a` until fuel runs out, yielding `mod a 0 = a` -- matching
        // the native reducer.)
        let nat_sub_const = Expr::const_(Name::from_string("Nat.sub"), vec![]);
        let nat_arrow_nat = Expr::pi(
            BinderInfo::Default,
            nat_const.clone(),
            Expr::pi(BinderInfo::Default, nat_const.clone(), nat_const.clone()),
        );
        // outer fuel-recursion motive: λ _ : Nat => Nat → Nat → Nat
        let modcore_motive = Expr::lam(
            BinderInfo::Default,
            nat_const.clone(),
            nat_arrow_nat.clone(),
        );
        let nat_modcore_type = Expr::pi(
            BinderInfo::Default,
            nat_const.clone(),
            Expr::pi(
                BinderInfo::Default,
                nat_const.clone(),
                Expr::pi(BinderInfo::Default, nat_const.clone(), nat_const.clone()),
            ),
        );
        let nat_modcore_value = {
            let mut b = EnvDeclBuilder::new();
            // base (fuel 0): λ a n => a
            let (ba_id, ba) = b.fresh_local(nat_const.clone());
            let (bn_id, _bn) = b.fresh_local(nat_const.clone());
            let base = b.mk_lam(bn_id, BinderInfo::Default, nat_const.clone(), ba.clone());
            let base = b.mk_lam(ba_id, BinderInfo::Default, nat_const.clone(), base);
            // step (fuel succ f): λ f ih a n =>
            //   Nat.rec (λ _ => Nat) (ih (a - n) n) (λ _ _ => a) (n - a)
            let (sf_id, _sf) = b.fresh_local(nat_const.clone());
            let (ih_id, ih) = b.fresh_local(nat_arrow_nat.clone());
            let (sa_id, sa) = b.fresh_local(nat_const.clone());
            let (sn_id, sn) = b.fresh_local(nat_const.clone());
            let a_minus_n = Expr::apps(nat_sub_const.clone(), [sa.clone(), sn.clone()]);
            let n_minus_a = Expr::apps(nat_sub_const.clone(), [sn.clone(), sa.clone()]);
            let recurse = Expr::apps(ih, [a_minus_n, sn.clone()]);
            // inner step (n - a = succ _, i.e. n > a): λ _ _ => a
            let (ik_id, _ik) = b.fresh_local(nat_const.clone());
            let (iih_id, _iih) = b.fresh_local(nat_const.clone());
            let inner_step = b.mk_lam(iih_id, BinderInfo::Default, nat_const.clone(), sa.clone());
            let inner_step = b.mk_lam(ik_id, BinderInfo::Default, nat_const.clone(), inner_step);
            let cond = Expr::apps(
                nat_rec.clone(),
                [motive.clone(), recurse, inner_step, n_minus_a],
            );
            let step = b.mk_lam(sn_id, BinderInfo::Default, nat_const.clone(), cond);
            let step = b.mk_lam(sa_id, BinderInfo::Default, nat_const.clone(), step);
            let step = b.mk_lam(ih_id, BinderInfo::Default, nat_arrow_nat.clone(), step);
            let step = b.mk_lam(sf_id, BinderInfo::Default, nat_const.clone(), step);
            // λ fuel a n => (Nat.rec modcore_motive base step fuel) a n
            let (f_id, f) = b.fresh_local(nat_const.clone());
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let reccall = Expr::apps(nat_rec.clone(), [modcore_motive.clone(), base, step, f]);
            let body = Expr::apps(reccall, [a, n]);
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };
        // SOUNDNESS: import-mode Nat core arithmetic cluster gate (see Nat.add
        // above). Clean's fuel-arity-3 Nat.modCore diverges from Lean's
        // arity-2 structural modCore at the TYPE level.
        if !self.suppress_lossy_structure_stubs {
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string("Nat.modCore"),
                level_params: vec![],
                type_: nat_modcore_type,
                value: nat_modcore_value,
                is_reducible: true,
            })?;
        }

        // Nat.mod := λ a n => Nat.modCore a a n   (fuel = a)
        let nat_modcore_const = Expr::const_(Name::from_string("Nat.modCore"), vec![]);
        let nat_mod_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let body = Expr::apps(nat_modcore_const.clone(), [a.clone(), a, n]);
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };
        // SOUNDNESS: import-mode Nat core arithmetic cluster gate (see Nat.add above).
        if !self.suppress_lossy_structure_stubs {
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string("Nat.mod"),
                level_params: vec![],
                type_: nat_binop_ty,
                value: nat_mod_value,
                is_reducible: true,
            })?;
        }

        // Add Nat.pow : Nat → Nat → Nat (exponentiation)
        // Nat.pow m n := Nat.rec (Nat.succ Nat.zero) (λ _ ih => Nat.mul ih m) n
        // This computes: pow m 0 = 1, pow m (succ n) = mul (pow m n) m
        let nat_pow_type = Expr::pi(
            BinderInfo::Default,
            nat_const.clone(),
            Expr::pi(BinderInfo::Default, nat_const.clone(), nat_const.clone()),
        );

        // 1 = Nat.succ Nat.zero
        let nat_one = Expr::app(nat_succ.clone(), nat_zero.clone());

        let nat_mul_const = Expr::const_(Name::from_string("Nat.mul"), vec![]);

        // Nat.pow := λ m n : Nat => Nat.rec motive 1 (λ _ ih => Nat.mul ih m) n
        let nat_pow_value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat_const.clone());
            let (n_id, n) = b.fresh_local(nat_const.clone());
            // succ case: λ _ : Nat => λ ih : Nat => Nat.mul ih m
            let (k_id, _k) = b.fresh_local(nat_const.clone());
            let (ih_id, ih) = b.fresh_local(nat_const.clone());
            let pow_succ = b.mk_lam(
                ih_id,
                BinderInfo::Default,
                nat_const.clone(),
                Expr::app(Expr::app(nat_mul_const.clone(), ih), m.clone()),
            );
            let pow_succ = b.mk_lam(k_id, BinderInfo::Default, nat_const.clone(), pow_succ);
            let body = Expr::apps(
                nat_rec.clone(),
                [motive.clone(), nat_one.clone(), pow_succ, n],
            );
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            let e = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: import-mode Nat core arithmetic cluster gate (see Nat.add above).
        if !self.suppress_lossy_structure_stubs {
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string("Nat.pow"),
                level_params: vec![],
                type_: nat_pow_type,
                value: nat_pow_value,
                is_reducible: true,
            })?;
        }

        // Nat.land : Nat → Nat → Nat (bitwise AND)
        // Nat.lor  : Nat → Nat → Nat (bitwise OR)
        // Nat.xor  : Nat → Nat → Nat (bitwise XOR)
        // Nat.shiftRight : Nat → Nat → Nat
        //
        // These are registered as axioms here (the low-level `init_nat` path)
        // and their computation is handled by native reducers registered in
        // `init_arith_native_reducers`. Part of #3396.
        //
        // Track II: the FULL prelude (`init_prelude`) subsequently DISCHARGES
        // `Nat.land`/`Nat.lor`/`Nat.xor` to real reducible Definitions
        // `Nat.bitwise and/or/xor` via `register_nat_bitwise_def` (a total fuel
        // fold over `Nat.div2`/`Nat.testBit`). Only `Nat.shiftRight` stays an
        // axiom. A bare `Environment::new()` (not `with_prelude`) still sees the
        // admitted axiom forms registered below.
        let nat_binop_type = Expr::pi(
            BinderInfo::Default,
            nat_const.clone(),
            Expr::pi(BinderInfo::Default, nat_const.clone(), nat_const.clone()),
        );

        for name in &["Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftRight"] {
            self.add_decl_if_absent(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![],
                type_: nat_binop_type.clone(),
            })?;
        }

        // Nat.shiftLeft : Nat → Nat → Nat (left shift = multiply by 2^n)
        // Nat.shiftLeft m n := Nat.rec m (λ _ ih => Nat.mul ih 2) n
        // This computes: shiftLeft m 0 = m, shiftLeft m (succ n) = mul (shiftLeft m n) 2,
        // i.e. shiftLeft m n = m * 2^n. Mirrors the Nat.pow Definition (Nat.rec + Nat.mul).
        // Ground terms still compute via the native reducer in `reduce_nat`; symbolic
        // `Eq.refl` reductions now type-check against this body. Part of #3470 (was an axiom).
        //
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.30 census
        // 2026-07-06): Lean v4.30 stores a brecOn tower that recurses
        // multiply-FIRST (`shiftLeft m (n+1) = shiftLeft (2*m) n`) — Clean's
        // direct Nat.rec seed multiplies LAST, so the olean twin fails the
        // value-defeq dedup and Nat.shiftLeft_eq/_succ/_add/zero_shiftLeft
        // cascade. Import-suppressed (WS17 pattern) so the genuine olean
        // definition imports through the checked add_decl path; the native
        // reducer is name-keyed and still fires for the imported constant.
        if !self.suppress_lossy_structure_stubs {
            let nat_shift_left_type = nat_binop_type.clone();

            // 2 = Nat.succ (Nat.succ Nat.zero)
            let nat_two = Expr::app(
                nat_succ.clone(),
                Expr::app(nat_succ.clone(), nat_zero.clone()),
            );

            // Nat.shiftLeft := λ m n : Nat => Nat.rec motive m (λ _ ih => Nat.mul ih 2) n
            let nat_shift_left_value = {
                let mut b = EnvDeclBuilder::new();
                let (m_id, m) = b.fresh_local(nat_const.clone());
                let (n_id, n) = b.fresh_local(nat_const.clone());
                // succ case: λ _ : Nat => λ ih : Nat => Nat.mul ih 2
                let (k_id, _k) = b.fresh_local(nat_const.clone());
                let (ih_id, ih) = b.fresh_local(nat_const.clone());
                let shl_succ = b.mk_lam(
                    ih_id,
                    BinderInfo::Default,
                    nat_const.clone(),
                    Expr::app(Expr::app(nat_mul_const.clone(), ih), nat_two.clone()),
                );
                let shl_succ = b.mk_lam(k_id, BinderInfo::Default, nat_const.clone(), shl_succ);
                let body = Expr::apps(nat_rec.clone(), [motive.clone(), m, shl_succ, n]);
                let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
                let e = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), e);
                b.finish(e)
            };

            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string("Nat.shiftLeft"),
                level_params: vec![],
                type_: nat_shift_left_type,
                value: nat_shift_left_value,
                is_reducible: true,
            })?;
        }

        // Nat.testBit : Nat → Nat → Bool
        // Used in bitwise commutativity proofs.
        // Ensure Bool is initialized since testBit references it.
        self.init_bool()?;
        let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);
        let nat_testbit_type = Expr::pi(
            BinderInfo::Default,
            nat_const.clone(),
            Expr::pi(BinderInfo::Default, nat_const.clone(), bool_const),
        );
        self.add_decl_if_absent(Declaration::Axiom {
            name: Name::from_string("Nat.testBit"),
            level_params: vec![],
            type_: nat_testbit_type,
        })?;

        self.nat_init = true;
        Ok(())
    }

    /// Check if Nat has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_nat` has completed successfully
    /// ENSURES: Pure - no side effects
    pub fn has_nat(&self) -> bool {
        self.nat_init
    }

    /// Initialize Int type (integers)
    ///
    /// inductive Int where
    ///   | ofNat (n : Nat) : Int
    ///   | negSucc (n : Nat) : Int  -- represents -(n+1)
    ///
    /// Also adds:
    /// - Int.neg : Int → Int
    /// - Int.add : Int → Int → Int
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_init == true`
    /// ENSURES: On success, required dependencies (`nat`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_int(&mut self) -> Result<(), EnvError> {
        if self.int_init {
            return Ok(());
        }

        // Ensure Nat is initialized
        self.init_nat()?;

        // Int : Type
        let int_type = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

        // Int.ofNat : Nat → Int
        let int_of_nat_type = Expr::pi(BinderInfo::Default, nat_const.clone(), int_const.clone());

        // Int.negSucc : Nat → Int (represents -(n+1))
        let int_neg_succ_type = Expr::pi(BinderInfo::Default, nat_const.clone(), int_const.clone());

        let int_decl = InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("Int"),
                type_: int_type,
                constructors: vec![
                    Constructor {
                        name: Name::from_string("Int.ofNat"),
                        type_: int_of_nat_type,
                    },
                    Constructor {
                        name: Name::from_string("Int.negSucc"),
                        type_: int_neg_succ_type,
                    },
                ],
            }],
        };

        // Skip if Int already exists. Part of #3333.
        if self.get_inductive(&Name::from_string("Int")).is_none() {
            self.add_inductive(int_decl)?;
        }

        // Add Int.neg : Int → Int
        // Int.neg (ofNat n) = if n = 0 then ofNat 0 else negSucc (n - 1)
        // Int.neg (negSucc n) = ofNat (n + 1)
        //
        // For simplicity, we define:
        // Int.neg := λ i => Int.rec (λ n => negSucc (pred n)) (λ n => ofNat (succ n)) i
        // Note: This is simplified - neg 0 = negSucc (pred 0) = negSucc 0 = -1, which is wrong
        // Proper implementation would need decidable equality on Nat
        //
        // We'll add a correct version using Nat.rec for the ofNat case
        let int_rec = Expr::const_(
            Name::from_string("Int.rec"),
            vec![Level::succ(Level::zero())],
        );
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let int_neg_succ = Expr::const_(Name::from_string("Int.negSucc"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_rec = Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        );

        let int_neg_type = Expr::pi(BinderInfo::Default, int_const.clone(), int_const.clone());

        // motive: λ _ : Int => Int
        let motive = Expr::lam(BinderInfo::Default, int_const.clone(), int_const.clone());

        // ofNat case: λ n : Nat => Nat.rec (ofNat 0) (λ m _ => negSucc m) n
        // This gives: neg 0 = ofNat 0, neg (succ m) = negSucc m
        let nat_motive = Expr::lam(BinderInfo::Default, nat_const.clone(), int_const.clone());
        let int_neg_value = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(int_const.clone());

            // ofNat case: λ n => Nat.rec (ofNat 0) (λ m _ => negSucc m) n
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let (m_id, m) = b.fresh_local(nat_const.clone());
            let (ih_id, _ih) = b.fresh_local(int_const.clone());
            let succ_br = b.mk_lam(
                ih_id,
                BinderInfo::Default,
                int_const.clone(),
                Expr::app(int_neg_succ.clone(), m),
            );
            let succ_br = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), succ_br);
            let of_nat_case = Expr::apps(
                nat_rec.clone(),
                [
                    nat_motive.clone(),
                    Expr::app(int_of_nat.clone(), nat_zero.clone()),
                    succ_br,
                    n,
                ],
            );
            let of_nat_case = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), of_nat_case);

            // negSucc case: λ n : Nat => ofNat (succ n)
            let (n2_id, n2) = b.fresh_local(nat_const.clone());
            let neg_succ_case = b.mk_lam(
                n2_id,
                BinderInfo::Default,
                nat_const.clone(),
                Expr::app(int_of_nat.clone(), Expr::app(nat_succ.clone(), n2)),
            );

            let body = Expr::apps(
                int_rec.clone(),
                [motive.clone(), of_nat_case, neg_succ_case, i],
            );
            let e = b.mk_lam(i_id, BinderInfo::Default, int_const.clone(), body);
            b.finish(e)
        };

        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string("Int.neg"),
            level_params: vec![],
            type_: int_neg_type,
            value: int_neg_value,
            is_reducible: true,
        })?;

        // Add Int.toNat : Int → Nat (returns 0 for negative)
        let int_to_nat_type = Expr::pi(BinderInfo::Default, int_const.clone(), nat_const.clone());

        let to_nat_motive = Expr::lam(BinderInfo::Default, int_const.clone(), nat_const.clone());

        let int_to_nat_value = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(int_const.clone());
            // ofNat case: λ n : Nat => n
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let of_nat_case = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), n);
            // negSucc case: λ _ : Nat => 0
            let (k_id, _k) = b.fresh_local(nat_const.clone());
            let neg_succ_case = b.mk_lam(
                k_id,
                BinderInfo::Default,
                nat_const.clone(),
                nat_zero.clone(),
            );
            let body = Expr::apps(
                int_rec.clone(),
                [to_nat_motive.clone(), of_nat_case, neg_succ_case, i],
            );
            let e = b.mk_lam(i_id, BinderInfo::Default, int_const.clone(), body);
            b.finish(e)
        };

        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string("Int.toNat"),
            level_params: vec![],
            type_: int_to_nat_type,
            value: int_to_nat_value,
            is_reducible: true,
        })?;

        // Int.zero : Int := Int.ofNat Nat.zero
        // Abbreviation matching Lean 4 Init/Prelude.lean
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string("Int.zero"),
            level_params: vec![],
            type_: int_const.clone(),
            value: Expr::app(int_of_nat.clone(), nat_zero.clone()),
            is_reducible: true,
        })?;

        // NOTE: `Int.div` / `Int.mod` are intentionally NOT registered here.
        // They are provided (with their division-algorithm proof obligations)
        // by `init_int_euclidean_domain_inst`, which `add_decl`s them directly;
        // registering them here too would be a duplicate declaration and breaks
        // that initializer. Wiring full Int division into the default prelude is
        // a separate, larger prelude-completeness task — Int arithmetic
        // (Int.add/sub/mul and the HAdd/HSub/HMul/HDiv/HMod Int instances) is
        // not currently bootstrapped in `init_prelude_core` at all. (Track TAC
        // scoping note)

        self.int_init = true;
        Ok(())
    }

    /// Check if Int has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_int` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_int(&self) -> bool {
        self.int_init
    }
}
