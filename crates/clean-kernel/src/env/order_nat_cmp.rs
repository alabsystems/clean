// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ordering enum and Nat comparison operations for Environment
//!
//! This module contains:
//! - Ordering enum type (lt, eq, gt) with swap, isLt, isEq, isGt
//! - Nat.beq, Nat.ble, Nat.blt (decidable boolean comparisons)
//! - Nat.compare : Nat → Nat → Ordering

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Ordering enum type
    ///
    /// Ordering is a simple enum with three constructors:
    /// - Ordering.lt : Ordering (less than)
    /// - Ordering.eq : Ordering (equal)
    /// - Ordering.gt : Ordering (greater than)
    ///
    /// This is used for comparison operations.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.ordering_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_ordering(&mut self) -> Result<(), EnvError> {
        if self.ordering_init {
            return Ok(());
        }

        // Ordering : Type
        let ordering_type = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
        let ordering_const = Expr::const_(Name::from_string("Ordering"), vec![]);

        // All constructors have type Ordering
        let ordering_decl = InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("Ordering"),
                type_: ordering_type,
                constructors: vec![
                    Constructor {
                        name: Name::from_string("Ordering.lt"),
                        type_: ordering_const.clone(),
                    },
                    Constructor {
                        name: Name::from_string("Ordering.eq"),
                        type_: ordering_const.clone(),
                    },
                    Constructor {
                        name: Name::from_string("Ordering.gt"),
                        type_: ordering_const.clone(),
                    },
                ],
            }],
        };

        self.add_inductive(ordering_decl)?;

        // Add Ordering.swap : Ordering → Ordering
        // swap lt = gt, swap eq = eq, swap gt = lt
        let ordering_rec = Expr::const_(
            Name::from_string("Ordering.rec"),
            vec![Level::succ(Level::zero())],
        );
        let ordering_lt = Expr::const_(Name::from_string("Ordering.lt"), vec![]);
        let ordering_eq = Expr::const_(Name::from_string("Ordering.eq"), vec![]);
        let ordering_gt = Expr::const_(Name::from_string("Ordering.gt"), vec![]);

        let swap_type = {
            let mut b = EnvDeclBuilder::new();
            let (o_id, _o) = b.fresh_local(ordering_const.clone());
            let r = ordering_const.clone();
            let r = b.mk_pi(o_id, BinderInfo::Default, ordering_const.clone(), r);
            b.finish(r)
        };

        // motive: λ _ : Ordering => Ordering
        let swap_motive = {
            let mut b = EnvDeclBuilder::new();
            let (w_id, _w) = b.fresh_local(ordering_const.clone());
            let r = ordering_const.clone();
            let r = b.mk_lam(w_id, BinderInfo::Default, ordering_const.clone(), r);
            b.finish(r)
        };

        // Ordering.swap := λ o : Ordering => Ordering.rec motive gt eq lt o
        let swap_value = {
            let mut b = EnvDeclBuilder::new();
            let (o_id, o) = b.fresh_local(ordering_const.clone());
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(ordering_rec.clone(), swap_motive),
                            ordering_gt.clone(),
                        ),
                        ordering_eq.clone(),
                    ),
                    ordering_lt.clone(),
                ),
                o,
            );
            let r = b.mk_lam(o_id, BinderInfo::Default, ordering_const.clone(), body);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Ordering.swap"),
            level_params: vec![],
            type_: swap_type,
            value: swap_value,
            is_reducible: true,
        })?;

        // Add Ordering.isLt : Ordering → Bool
        self.init_bool()?;
        let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);
        let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);

        let is_lt_type = {
            let mut b = EnvDeclBuilder::new();
            let (o_id, _o) = b.fresh_local(ordering_const.clone());
            let r = bool_const.clone();
            let r = b.mk_pi(o_id, BinderInfo::Default, ordering_const.clone(), r);
            b.finish(r)
        };

        let is_lt_motive = {
            let mut b = EnvDeclBuilder::new();
            let (w_id, _w) = b.fresh_local(ordering_const.clone());
            let r = bool_const.clone();
            let r = b.mk_lam(w_id, BinderInfo::Default, ordering_const.clone(), r);
            b.finish(r)
        };

        // isLt lt = true, isLt eq = false, isLt gt = false
        let is_lt_value = {
            let mut b = EnvDeclBuilder::new();
            let (o_id, o) = b.fresh_local(ordering_const.clone());
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(ordering_rec.clone(), is_lt_motive),
                            bool_true.clone(),
                        ),
                        bool_false.clone(),
                    ),
                    bool_false.clone(),
                ),
                o,
            );
            let r = b.mk_lam(o_id, BinderInfo::Default, ordering_const.clone(), body);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Ordering.isLt"),
            level_params: vec![],
            type_: is_lt_type,
            value: is_lt_value,
            is_reducible: true,
        })?;

        // Add Ordering.isEq : Ordering → Bool
        //
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Clean's rec-based
        // spelling (`Ordering.rec (fun _ => Bool) false true false`) diverges
        // from Lean v4.30's wildcard-match compilation — `| .eq => true | _ =>
        // false` compiles through `Ordering.then.match_1` to
        // `Ordering.then._sparseCasesOn_1`, an `Ordering.rec` with the
        // higher-order continuation motive `fun t => (Nat.hasNotBit 2
        // (Ordering.ctorIdx t) → Bool) → Bool`. The two stuck forms are never
        // definitionally equal for a free scrutinee (kernel defeq cannot case
        // split), so the seeded twin blocks the genuine olean definition at
        // the value-defeq dedup (census root: Init.Data.Ord.Basic).
        // Suppressing the seed in import mode lets the genuine olean value
        // flow through the normal CHECKED `add_decl` import path.
        // SOUNDNESS-NEUTRAL: this only WITHHOLDS a Clean-native definition in
        // the import-only prelude; the constant the import then carries is the
        // genuine olean value, re-checked by the unmodified kernel. The
        // proof-execution lane (`Environment::new()`) keeps the rec spelling.
        // (isLt/isGt do not collide: v4.30 has no upstream constants with
        // those exact names.)
        if !self.suppress_lossy_structure_stubs {
            let is_eq_type = {
                let mut b = EnvDeclBuilder::new();
                let (o_id, _o) = b.fresh_local(ordering_const.clone());
                let r = bool_const.clone();
                let r = b.mk_pi(o_id, BinderInfo::Default, ordering_const.clone(), r);
                b.finish(r)
            };

            let is_eq_motive = {
                let mut b = EnvDeclBuilder::new();
                let (w_id, _w) = b.fresh_local(ordering_const.clone());
                let r = bool_const.clone();
                let r = b.mk_lam(w_id, BinderInfo::Default, ordering_const.clone(), r);
                b.finish(r)
            };

            // isEq lt = false, isEq eq = true, isEq gt = false
            let is_eq_value = {
                let mut b = EnvDeclBuilder::new();
                let (o_id, o) = b.fresh_local(ordering_const.clone());
                let body = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(ordering_rec.clone(), is_eq_motive),
                                bool_false.clone(),
                            ),
                            bool_true.clone(),
                        ),
                        bool_false.clone(),
                    ),
                    o,
                );
                let r = b.mk_lam(o_id, BinderInfo::Default, ordering_const.clone(), body);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: Name::from_string("Ordering.isEq"),
                level_params: vec![],
                type_: is_eq_type,
                value: is_eq_value,
                is_reducible: true,
            })?;
        }

        // Add Ordering.isGt : Ordering → Bool
        let is_gt_type = {
            let mut b = EnvDeclBuilder::new();
            let (o_id, _o) = b.fresh_local(ordering_const.clone());
            let r = bool_const.clone();
            let r = b.mk_pi(o_id, BinderInfo::Default, ordering_const.clone(), r);
            b.finish(r)
        };

        let is_gt_motive = {
            let mut b = EnvDeclBuilder::new();
            let (w_id, _w) = b.fresh_local(ordering_const.clone());
            let r = bool_const.clone();
            let r = b.mk_lam(w_id, BinderInfo::Default, ordering_const.clone(), r);
            b.finish(r)
        };

        // isGt lt = false, isGt eq = false, isGt gt = true
        let is_gt_value = {
            let mut b = EnvDeclBuilder::new();
            let (o_id, o) = b.fresh_local(ordering_const.clone());
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(ordering_rec.clone(), is_gt_motive),
                            bool_false.clone(),
                        ),
                        bool_false.clone(),
                    ),
                    bool_true.clone(),
                ),
                o,
            );
            let r = b.mk_lam(o_id, BinderInfo::Default, ordering_const.clone(), body);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Ordering.isGt"),
            level_params: vec![],
            type_: is_gt_type,
            value: is_gt_value,
            is_reducible: true,
        })?;

        self.ordering_init = true;
        Ok(())
    }

    /// Check if Ordering has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.ordering_init == true`
    pub(crate) fn has_ordering(&self) -> bool {
        self.ordering_init
    }

    /// Initialize Nat comparison operations
    ///
    /// Nat.beq : Nat → Nat → Bool (decidable equality)
    /// Nat.ble : Nat → Nat → Bool (decidable ≤)
    /// Nat.blt : Nat → Nat → Bool (decidable <)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_cmp_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_cmp(&mut self) -> Result<(), EnvError> {
        if self.nat_cmp_init {
            return Ok(());
        }

        // Ensure dependencies are initialized
        self.init_nat()?;
        self.init_bool()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_rec = Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        );

        let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);
        let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);

        // Nat.beq : Nat → Nat → Bool
        // beq 0 0 = true
        // beq 0 (succ _) = false
        // beq (succ _) 0 = false
        // beq (succ n) (succ m) = beq n m
        //
        // We implement this via double recursion:
        // beq m n := Nat.rec (λ n => Nat.rec true (λ _ _ => false) n)
        //                    (λ m beq_m n => Nat.rec false (λ n' _ => beq_m n') n) m n
        let beq_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, _m) = b.fresh_local(nat_const.clone());
            let (n_id, _n) = b.fresh_local(nat_const.clone());
            let r = bool_const.clone();
            let r = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        // Outer motive: λ _ : Nat => Nat → Bool
        let outer_motive = {
            let mut b = EnvDeclBuilder::new();
            let (w_id, _w) = b.fresh_local(nat_const.clone());
            let r = Expr::pi(BinderInfo::Default, nat_const.clone(), bool_const.clone());
            let r = b.mk_lam(w_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        // Zero case: λ n : Nat => Nat.rec true (λ _ _ => false) n
        let inner_zero_motive =
            Expr::lam(BinderInfo::Default, nat_const.clone(), bool_const.clone());
        let zero_case = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(nat_rec.clone(), inner_zero_motive.clone()),
                        bool_true.clone(),
                    ),
                    Expr::lam(
                        BinderInfo::Default,
                        nat_const.clone(),
                        Expr::lam(BinderInfo::Default, bool_const.clone(), bool_false.clone()),
                    ),
                ),
                n,
            );
            let r = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            b.finish(r)
        };

        // Succ case: λ m : Nat => λ beq_m : Nat → Bool => λ n : Nat =>
        //   Nat.rec false (λ n' _ => beq_m n') n
        let beq_m_ty = Expr::pi(BinderInfo::Default, nat_const.clone(), bool_const.clone());
        let succ_case = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, _m) = b.fresh_local(nat_const.clone()); // m
            let (beq_m_id, beq_m) = b.fresh_local(beq_m_ty.clone()); // beq_m
            let (n_id, n) = b.fresh_local(nat_const.clone()); // n

            // inner rec step: λ n' _ => beq_m n'
            let inner_step = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (np_id, np) = c.fresh_local(nat_const.clone()); // n'
                let (ih_id, _ih) = c.fresh_local(bool_const.clone()); // ih (unused)
                let body = Expr::app(beq_m.clone(), np);
                let r = c.mk_lam(ih_id, BinderInfo::Default, bool_const.clone(), body);
                let r = c.mk_lam(np_id, BinderInfo::Default, nat_const.clone(), r);
                c.finish_child(r)
            };

            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(nat_rec.clone(), inner_zero_motive.clone()),
                        bool_false.clone(),
                    ),
                    inner_step,
                ),
                n,
            );
            let r = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            let r = b.mk_lam(beq_m_id, BinderInfo::Default, beq_m_ty.clone(), r);
            let r = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        // beq returns a function Nat → Bool, we need to apply both arguments
        let beq_value_full = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat_const.clone());
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(nat_rec.clone(), outer_motive.clone()),
                            zero_case.clone(),
                        ),
                        succ_case.clone(),
                    ),
                    m,
                ),
                n,
            );
            let r = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            let r = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.30 census
        // 2026-07-06, pinpoint dcb769d4): Nat.beq/ble/blt belong to the Nat
        // CORE ARITHMETIC seed cluster (see data_types_nat.rs::init_nat).
        // Lean v4.30 stores brecOn towers for beq/ble; Clean's direct
        // double-Nat.rec seeds fail the import value-defeq dedup and block the
        // genuine olean definitions (11 Init.Prelude dup rows). SOUNDNESS: the
        // gate only WITHHOLDS the Clean-native seeds in the import-only
        // prelude; the genuine olean values import through the checked
        // add_decl path and the name-keyed native reducers still accelerate
        // them. Default lane byte-identical. Nat.compare is gated below with
        // the ring-2 Ord cluster (2026-07-15 closing census): the import
        // prelude DOES run this init — `init_ord` (order_ord.rs), wired
        // unconditionally in the prelude, calls it for its instOrdNat seed.
        if !self.suppress_lossy_structure_stubs {
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Nat.beq"),
                level_params: vec![],
                type_: beq_type,
                value: beq_value_full,
                is_reducible: true,
            })?;
        }

        // Nat.ble : Nat → Nat → Bool (m ≤ n)
        // ble 0 _ = true
        // ble (succ _) 0 = false
        // ble (succ m) (succ n) = ble m n
        let ble_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, _m) = b.fresh_local(nat_const.clone());
            let (n_id, _n) = b.fresh_local(nat_const.clone());
            let r = bool_const.clone();
            let r = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        // Zero case: λ n : Nat => true (0 ≤ n is always true)
        let ble_zero_case = Expr::lam(BinderInfo::Default, nat_const.clone(), bool_true.clone());

        // Succ case: λ m : Nat => λ ble_m : Nat → Bool => λ n : Nat =>
        //   Nat.rec false (λ n' _ => ble_m n') n
        let ble_succ_case = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, _m) = b.fresh_local(nat_const.clone()); // m
            let (ble_m_id, ble_m) = b.fresh_local(beq_m_ty.clone()); // ble_m : Nat → Bool
            let (n_id, n) = b.fresh_local(nat_const.clone()); // n

            let inner_step = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (np_id, np) = c.fresh_local(nat_const.clone()); // n'
                let (ih_id, _ih) = c.fresh_local(bool_const.clone()); // ih (unused)
                let body = Expr::app(ble_m.clone(), np);
                let r = c.mk_lam(ih_id, BinderInfo::Default, bool_const.clone(), body);
                let r = c.mk_lam(np_id, BinderInfo::Default, nat_const.clone(), r);
                c.finish_child(r)
            };

            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(nat_rec.clone(), inner_zero_motive.clone()),
                        bool_false.clone(),
                    ),
                    inner_step,
                ),
                n,
            );
            let r = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            let r = b.mk_lam(ble_m_id, BinderInfo::Default, beq_m_ty.clone(), r);
            let r = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        let ble_value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat_const.clone());
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(nat_rec.clone(), outer_motive.clone()),
                            ble_zero_case,
                        ),
                        ble_succ_case,
                    ),
                    m,
                ),
                n,
            );
            let r = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            let r = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        // SOUNDNESS: import-mode Nat core arithmetic cluster gate (see Nat.beq above).
        if !self.suppress_lossy_structure_stubs {
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Nat.ble"),
                level_params: vec![],
                type_: ble_type,
                value: ble_value,
                is_reducible: true,
            })?;
        }

        // Nat.blt : Nat → Nat → Bool (m < n ≡ succ m ≤ n)
        // blt m n := ble (succ m) n
        let blt_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, _m) = b.fresh_local(nat_const.clone());
            let (n_id, _n) = b.fresh_local(nat_const.clone());
            let r = bool_const.clone();
            let r = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        let nat_ble = Expr::const_(Name::from_string("Nat.ble"), vec![]);

        let blt_value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat_const.clone()); // m
            let (n_id, n) = b.fresh_local(nat_const.clone()); // n
            let body = Expr::app(Expr::app(nat_ble, Expr::app(nat_succ.clone(), m)), n);
            let r = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            let r = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        // SOUNDNESS: import-mode Nat core arithmetic cluster gate (see Nat.beq
        // above). Nat.blt's value references the gated Nat.ble.
        if !self.suppress_lossy_structure_stubs {
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Nat.blt"),
                level_params: vec![],
                type_: blt_type,
                value: blt_value,
                is_reducible: true,
            })?;
        }

        // Nat.compare : Nat → Nat → Ordering
        self.init_ordering()?;
        let ordering_const = Expr::const_(Name::from_string("Ordering"), vec![]);
        let ordering_lt = Expr::const_(Name::from_string("Ordering.lt"), vec![]);
        let ordering_eq = Expr::const_(Name::from_string("Ordering.eq"), vec![]);
        let ordering_gt = Expr::const_(Name::from_string("Ordering.gt"), vec![]);

        let compare_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, _m) = b.fresh_local(nat_const.clone());
            let (n_id, _n) = b.fresh_local(nat_const.clone());
            let r = ordering_const.clone();
            let r = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        // compare 0 0 = eq
        // compare 0 (succ _) = lt
        // compare (succ _) 0 = gt
        // compare (succ m) (succ n) = compare m n

        let cmp_outer_motive = {
            let mut b = EnvDeclBuilder::new();
            let (w_id, _w) = b.fresh_local(nat_const.clone());
            let r = Expr::pi(
                BinderInfo::Default,
                nat_const.clone(),
                ordering_const.clone(),
            );
            let r = b.mk_lam(w_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        let cmp_inner_motive = Expr::lam(
            BinderInfo::Default,
            nat_const.clone(),
            ordering_const.clone(),
        );

        // Zero case: λ n : Nat => Nat.rec eq (λ _ _ => lt) n
        let cmp_zero_case = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(nat_rec.clone(), cmp_inner_motive.clone()),
                        ordering_eq.clone(),
                    ),
                    Expr::lam(
                        BinderInfo::Default,
                        nat_const.clone(),
                        Expr::lam(
                            BinderInfo::Default,
                            ordering_const.clone(),
                            ordering_lt.clone(),
                        ),
                    ),
                ),
                n,
            );
            let r = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            b.finish(r)
        };

        // Succ case: λ m : Nat => λ cmp_m : Nat → Ordering => λ n : Nat =>
        //   Nat.rec gt (λ n' _ => cmp_m n') n
        let cmp_m_ty = Expr::pi(
            BinderInfo::Default,
            nat_const.clone(),
            ordering_const.clone(),
        );
        let cmp_succ_case = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, _m) = b.fresh_local(nat_const.clone()); // m
            let (cmp_m_id, cmp_m) = b.fresh_local(cmp_m_ty.clone()); // cmp_m
            let (n_id, n) = b.fresh_local(nat_const.clone()); // n

            let inner_step = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (np_id, np) = c.fresh_local(nat_const.clone()); // n'
                let (ih_id, _ih) = c.fresh_local(ordering_const.clone()); // ih (unused)
                let body = Expr::app(cmp_m.clone(), np);
                let r = c.mk_lam(ih_id, BinderInfo::Default, ordering_const.clone(), body);
                let r = c.mk_lam(np_id, BinderInfo::Default, nat_const.clone(), r);
                c.finish_child(r)
            };

            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(nat_rec.clone(), cmp_inner_motive.clone()),
                        ordering_gt.clone(),
                    ),
                    inner_step,
                ),
                n,
            );
            let r = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            let r = b.mk_lam(cmp_m_id, BinderInfo::Default, cmp_m_ty.clone(), r);
            let r = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        let compare_value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat_const.clone());
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(nat_rec.clone(), cmp_outer_motive), cmp_zero_case),
                        cmp_succ_case,
                    ),
                    m,
                ),
                n,
            );
            let r = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            let r = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        // SOUNDNESS: import-mode ring-2 Ord cluster gate (v4.30 closing census
        // 2026-07-15; see order_ord.rs::init_ord). Genuine v4.30 has NO
        // `Nat.compare` constant — `compare a b : Ordering` goes through
        // `instOrdNat` whose field is the anonymous
        // `fun x y => compareOfLessAndEq x y` over the now-genuine
        // `Nat.decLt`/`Nat.decEq`. Clean's double-`Nat.rec` seed is a
        // Clean-only spelling the genuine `Nat.compare_*` lemma web
        // (Init.Data.Nat.Compare) can never re-check against; the gate only
        // WITHHOLDS the Clean-native seed in the import-only prelude. Default
        // lane byte-identical.
        if !self.suppress_lossy_structure_stubs {
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Nat.compare"),
                level_params: vec![],
                type_: compare_type,
                value: compare_value,
                is_reducible: true,
            })?;
        }

        self.nat_cmp_init = true;
        Ok(())
    }

    /// Check if Nat comparison operations have been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_cmp_init == true`
    pub(crate) fn has_nat_cmp(&self) -> bool {
        self.nat_cmp_init
    }
}
