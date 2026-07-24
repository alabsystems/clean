// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nat ordering instances for Environment
//!
//! This module contains Nat ordering init_* and has_* functions:
//! - Nat preorder, partial order, linear order instances
//! - Nat ordering properties (reflexive, irrefl, asymm, trans, antisymm)
//!
//! See also:
//! - order_lemmas.rs: StrictOrder, mixed Trans, successor/trichotomy/decidable/minmax lemmas
//! - order_arith.rs: Arithmetic ordering (add/mul/sub/pow) and FATE-X stubs

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Build `@LE.le.{0} Nat instLENat lhs rhs` — the typeclass-based Nat ≤ comparison.
///
/// Uses `LE.le` instead of bare `Nat.le` so that ordering instance declarations
/// match the typeclass path expected by the type checker (#1488).
pub(crate) fn nat_le_tc(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                    Expr::const_(Name::from_string("Nat"), vec![]),
                ),
                Expr::const_(Name::from_string("instLENat"), vec![]),
            ),
            lhs,
        ),
        rhs,
    )
}

/// Build `@LT.lt.{0} Nat instLTNat lhs rhs` — the typeclass-based Nat < comparison.
///
/// Uses `LT.lt` instead of bare `Nat.lt` so that ordering instance declarations
/// match the typeclass path expected by the type checker (#1488).
pub(crate) fn nat_lt_tc(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                    Expr::const_(Name::from_string("Nat"), vec![]),
                ),
                Expr::const_(Name::from_string("instLTNat"), vec![]),
            ),
            lhs,
        ),
        rhs,
    )
}

/// Build `fun (a : Nat) (b : Nat) => @LE.le.{0} Nat instLENat a b` — the Nat ≤ relation
/// as a lambda suitable for typeclass relation arguments (Reflexive, Trans, etc.).
pub(crate) fn nat_le_relation() -> Expr {
    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nat_const.clone());
    let (b_id, b_var) = b.fresh_local(nat_const.clone());
    let body = nat_le_tc(a, b_var);
    let e = b.mk_lam(b_id, BinderInfo::Default, nat_const.clone(), body);
    let e = b.mk_lam(a_id, BinderInfo::Default, nat_const.clone(), e);
    b.finish(e)
}

/// Build `fun (a : Nat) (b : Nat) => @LT.lt.{0} Nat instLTNat a b` — the Nat < relation
/// as a lambda suitable for typeclass relation arguments (Irrefl, Asymm, Trans, etc.).
pub(crate) fn nat_lt_relation() -> Expr {
    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nat_const.clone());
    let (b_id, b_var) = b.fresh_local(nat_const.clone());
    let body = nat_lt_tc(a, b_var);
    let e = b.mk_lam(b_id, BinderInfo::Default, nat_const.clone(), body);
    let e = b.mk_lam(a_id, BinderInfo::Default, nat_const.clone(), e);
    b.finish(e)
}

impl Environment {
    /// Initialize Preorder instance for Nat
    ///
    /// This adds:
    /// - Nat.le_refl : ∀ n : Nat, Nat.le n n (wrapped from Nat.le.refl constructor)
    /// - Nat.le_trans : theorem ∀ a b c : Nat, Nat.le a b → Nat.le b c → Nat.le a c
    ///   (proved constructively from `Nat.le.rec` — see `order_nat_le_trans_proof.rs`, #3552)
    /// - instPreorderNat : Preorder Nat — Declaration::Definition built from
    ///   `Preorder.mk Nat instLENat instLTNat Nat.le_refl Nat.le_trans` (#3553).
    ///
    /// Note: `Nat.le_trans` is now a constructive theorem, not an axiom (#3552).
    /// The proof recurses on the second hypothesis via the kernel-generated
    /// `Nat.le.rec`. `instPreorderNat` is a Declaration::Definition as of
    /// #3553 (Preorder.mk applied to the Nat instances directly).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_preorder_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_preorder(&mut self) -> Result<(), EnvError> {
        if self.nat_preorder_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_preorder()?;
        self.init_le()?;
        self.init_lt()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        // `Nat.le_refl` is now a constructive `Declaration::Theorem`
        // registered by `init_nat_top_level_ordering` (#3599, proof term
        // `fun n => @Nat.le.refl n`). Previously this site registered
        // `Nat.le_refl` as a `Declaration::Axiom`; the Theorem form
        // supersedes that, and the Axiom registration has been removed.
        // Per the #3559 disjointness rule, `Nat.le_refl` has also been
        // removed from `FOUNDATIONAL_AXIOMS` in `axiom_audit.rs`.
        self.init_nat_top_level_ordering()?;

        // Nat.le_trans : constructive theorem proved via `Nat.le.rec` (#3552).
        // Type/value construction lives in `order_nat_le_trans_proof.rs` and
        // uses `nat_le_tc` (LE.le typeclass form) matching the signature
        // referenced by Preorder and callers.
        self.register_nat_le_trans_proof()?;

        // instPreorderNat : Preorder Nat := Preorder.mk instLENat instLTNat Nat.le_refl Nat.le_trans
        //
        // #3553: Converted from Declaration::Axiom to Declaration::Definition so the
        // kernel carries the actual instance value. The previous axiom form was a
        // workaround for the LE.le vs Nat.le projection reduction gap (#1526), but
        // Nat.le_refl and Nat.le_trans are already stated with LE.le @Nat instLENat
        // in their types, so no reduction is required to type-check the value.
        let inst_preorder_nat_type = Expr::app(
            Expr::const_(Name::from_string("Preorder"), vec![Level::zero()]),
            nat_const.clone(),
        );

        // Preorder.mk.{0} Nat instLENat instLTNat Nat.le_refl Nat.le_trans
        let inst_preorder_nat_value = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Preorder.mk"), vec![Level::zero()]),
                            nat_const.clone(), // α = Nat
                        ),
                        Expr::const_(Name::from_string("instLENat"), vec![]), // [LE Nat]
                    ),
                    Expr::const_(Name::from_string("instLTNat"), vec![]), // [LT Nat]
                ),
                Expr::const_(Name::from_string("Nat.le_refl"), vec![]),
            ),
            Expr::const_(Name::from_string("Nat.le_trans"), vec![]),
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instPreorderNat"),
            level_params: vec![],
            type_: inst_preorder_nat_type,
            value: inst_preorder_nat_value,
            is_reducible: false,
        })?;

        self.nat_preorder_init = true;
        Ok(())
    }

    /// Check if Nat Preorder instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_preorder_init == true`
    pub(crate) fn has_nat_preorder(&self) -> bool {
        self.nat_preorder_init
    }

    /// Initialize PartialOrder instance for Nat
    ///
    /// This adds:
    /// - Nat.le_antisymm : axiom ∀ a b : Nat, Nat.le a b → Nat.le b a → a = b
    /// - instPartialOrderNat : PartialOrder Nat
    ///
    /// Note: Nat.le_antisymm is added as an axiom. The actual proof would require
    /// induction on Nat.le.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_partial_order_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_partial_order(&mut self) -> Result<(), EnvError> {
        if self.nat_partial_order_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat_preorder()?;
        self.init_partial_order()?;
        self.init_eq()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

        // `Nat.le_antisymm` is now a constructive `Declaration::Theorem` proved
        // via `Nat.le.rec` (#3599). Construction lives in
        // `order_nat_le_antisymm_proof.rs`; it uses `nat_le_tc` (LE.le typeclass
        // form) so the registered signature matches the prior axiom and the
        // PartialOrder caller below. `register_*` is idempotent.
        self.register_nat_le_antisymm_proof()?;

        // instPartialOrderNat : PartialOrder Nat
        // Axiom — bypasses projection reduction gap (#1488, #1526).
        let inst_partial_order_nat_type = Expr::app(
            Expr::const_(Name::from_string("PartialOrder"), vec![Level::zero()]),
            nat_const.clone(),
        );

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("instPartialOrderNat"),
            level_params: vec![],
            type_: inst_partial_order_nat_type,
        })?;

        self.nat_partial_order_init = true;
        Ok(())
    }

    /// Check if Nat PartialOrder instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_partial_order_init == true`
    pub(crate) fn has_nat_partial_order(&self) -> bool {
        self.nat_partial_order_init
    }

    /// Initialize LinearOrder instance for Nat
    ///
    /// This adds:
    /// - Nat.le_total : ∀ a b : Nat, Or (Nat.le a b) (Nat.le b a)
    /// - instLinearOrderNat : LinearOrder Nat
    ///
    /// `Nat.le_total` is now a constructive `Declaration::Theorem` proved by
    /// double induction (`Nat.rec` on `a`, `Nat.casesOn` on `b`, `Or.rec` on
    /// the induction hypothesis), reusing the constructive `Nat.zero_le` and
    /// `Nat.succ_le_succ`. Construction lives in `order_nat_le_total_proof.rs`
    /// (#3599); it uses `nat_le_tc` (LE.le typeclass form) so the registered
    /// signature matches the prior axiom and the `LinearOrder` caller below.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_linear_order_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_linear_order(&mut self) -> Result<(), EnvError> {
        if self.nat_linear_order_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat_partial_order()?;
        self.init_linear_order()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

        // `Nat.le_total : ∀ a b : Nat, Or (Nat.le a b) (Nat.le b a)` is now a
        // constructive `Declaration::Theorem` proved via double induction
        // (#3599). Construction lives in `order_nat_le_total_proof.rs`; it uses
        // `nat_le_tc` (LE.le typeclass form) so the registered signature matches
        // the prior axiom and the `LinearOrder` caller below. `register_*` is
        // idempotent and a no-op if `Nat.le_total` is already present.
        self.register_nat_le_total_proof()?;

        // instLinearOrderNat : LinearOrder Nat
        // Axiom — bypasses projection reduction gap (#1488, #1526).
        let inst_linear_order_nat_type = Expr::app(
            Expr::const_(Name::from_string("LinearOrder"), vec![Level::zero()]),
            nat_const.clone(),
        );

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("instLinearOrderNat"),
            level_params: vec![],
            type_: inst_linear_order_nat_type,
        })?;

        self.nat_linear_order_init = true;
        Ok(())
    }

    /// Check if Nat LinearOrder instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_linear_order_init == true`
    pub(crate) fn has_nat_linear_order(&self) -> bool {
        self.nat_linear_order_init
    }

    /// Initialize Reflexive instance for Nat.le
    ///
    /// This adds:
    /// - instReflexiveNatLe : Reflexive Nat.le
    ///
    /// Uses Nat.le.refl as the reflexivity proof.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_le_reflexive_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_le_reflexive(&mut self) -> Result<(), EnvError> {
        if self.nat_le_reflexive_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat()?;
        self.init_le()?;
        self.init_reflexive()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

        let nat_le_rel = nat_le_relation();

        // instReflexiveNatLe : Reflexive (fun a b => LE.le @Nat instLENat a b)
        // Since Reflexive takes α implicitly, we can use Reflexive @{1} Nat (fun a b => Nat.le a b)
        let inst_reflexive_nat_le_type = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Reflexive"),
                    vec![Level::succ(Level::zero())],
                ),
                nat_const.clone(),
            ),
            nat_le_rel.clone(),
        );

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("instReflexiveNatLe"),
            level_params: vec![],
            type_: inst_reflexive_nat_le_type,
        })?;

        self.nat_le_reflexive_init = true;
        Ok(())
    }

    /// Check if Nat.le Reflexive instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_le_reflexive_init == true`
    pub(crate) fn has_nat_le_reflexive(&self) -> bool {
        self.nat_le_reflexive_init
    }

    /// Initialize Irrefl instance for Nat.lt
    ///
    /// This adds:
    /// - Nat.lt_irrefl : axiom ∀ a : Nat, Nat.lt a a → False
    /// - instIrreflNatLt : Irrefl Nat.lt
    ///
    /// Note: Nat.lt_irrefl is added as an axiom. The actual proof would use
    /// the definition Nat.lt a b = Nat.succ a ≤ b.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_lt_irrefl_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_lt_irrefl(&mut self) -> Result<(), EnvError> {
        if self.nat_lt_irrefl_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat()?;
        self.init_lt()?;
        self.init_true_false()?;
        self.init_irrefl()?;
        self.register_nat_lt_irrefl_theorem()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let false_const = Expr::const_(Name::from_string("False"), vec![]);

        if self
            .get_const(&Name::from_string("Nat.lt_irrefl"))
            .is_none()
        {
            // Nat.lt_irrefl : ∀ a : Nat, Nat.lt a a → False
            // Built with EnvDeclBuilder (#1444).
            let nat_lt_irrefl_type = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(nat_const.clone());
                let lt_aa = Expr::app(
                    Expr::app(Expr::const_(Name::from_string("Nat.lt"), vec![]), a.clone()),
                    a,
                );
                let (h_id, _h) = b.fresh_local(lt_aa.clone());
                let e = b.mk_pi(h_id, BinderInfo::Default, lt_aa, false_const.clone());
                let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
                b.finish(e)
            };

            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.lt_irrefl"),
                level_params: vec![],
                type_: nat_lt_irrefl_type,
            })?;
        }

        let nat_lt_relation = nat_lt_relation();

        // instIrreflNatLt : Irrefl (fun a b => Nat.lt a b)
        let inst_irrefl_nat_lt_type = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Irrefl"),
                    vec![Level::succ(Level::zero())],
                ),
                nat_const.clone(),
            ),
            nat_lt_relation.clone(),
        );

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("instIrreflNatLt"),
            level_params: vec![],
            type_: inst_irrefl_nat_lt_type,
        })?;

        self.nat_lt_irrefl_init = true;
        Ok(())
    }

    /// Check if Nat.lt Irrefl instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_lt_irrefl_init == true`
    pub(crate) fn has_nat_lt_irrefl(&self) -> bool {
        self.nat_lt_irrefl_init
    }

    /// Initialize Asymm instance for Nat.lt
    ///
    /// This adds:
    /// - Nat.lt_asymm : axiom ∀ a b : Nat, Nat.lt a b → Nat.lt b a → False
    /// - instAsymmNatLt : Asymm Nat.lt
    ///
    /// Note: Nat.lt_asymm is added as an axiom. The actual proof follows from
    /// transitivity and irreflexivity.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_lt_asymm_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_lt_asymm(&mut self) -> Result<(), EnvError> {
        if self.nat_lt_asymm_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat()?;
        self.init_lt()?;
        self.init_asymm()?;

        // Prefer the constructive `Declaration::Theorem` form of `Nat.lt_asymm`
        // (proved from `Nat.le_of_lt`, `Nat.le_trans`, `Nat.lt_irrefl` in
        // `nat_totality_proof.rs`). Idempotent; the legacy `Declaration::Axiom`
        // registration below is guarded so it becomes a no-op once present.
        self.init_nat_totality_proofs()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let false_const = Expr::const_(Name::from_string("False"), vec![]);

        // Nat.lt_asymm : ∀ a b : Nat, Nat.lt a b → Nat.lt b a → False
        // Built with EnvDeclBuilder (#1444).
        let nat_lt_asymm_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (bv_id, bv) = b.fresh_local(nat_const.clone());
            let hab_type = Expr::app(
                Expr::app(Expr::const_(Name::from_string("Nat.lt"), vec![]), a.clone()),
                bv.clone(),
            );
            let (hab_id, _hab) = b.fresh_local(hab_type.clone());
            let hba_type = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Nat.lt"), vec![]),
                    bv.clone(),
                ),
                a.clone(),
            );
            let (hba_id, _hba) = b.fresh_local(hba_type.clone());
            let e = b.mk_pi(hba_id, BinderInfo::Default, hba_type, false_const.clone());
            let e = b.mk_pi(hab_id, BinderInfo::Default, hab_type, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // Guarded: skip if the constructive Theorem form is already registered.
        if self.get_const(&Name::from_string("Nat.lt_asymm")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.lt_asymm"),
                level_params: vec![],
                type_: nat_lt_asymm_type,
            })?;
        }

        // Nat.lt : Nat → Nat → Prop (as a lambda)
        // Built with EnvDeclBuilder (#1444).
        let nat_lt_relation = nat_lt_relation();

        // instAsymmNatLt : Asymm (fun a b => LT.lt @Nat instLTNat a b)
        let inst_asymm_nat_lt_type = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Asymm"), vec![Level::succ(Level::zero())]),
                nat_const.clone(),
            ),
            nat_lt_relation.clone(),
        );

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("instAsymmNatLt"),
            level_params: vec![],
            type_: inst_asymm_nat_lt_type,
        })?;

        self.nat_lt_asymm_init = true;
        Ok(())
    }

    /// Check if Nat.lt Asymm instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_lt_asymm_init == true`
    pub(crate) fn has_nat_lt_asymm(&self) -> bool {
        self.nat_lt_asymm_init
    }

    /// Initialize Trans instance for Nat.lt
    ///
    /// This adds:
    /// - Nat.lt_trans : axiom ∀ a b c : Nat, Nat.lt a b → Nat.lt b c → Nat.lt a c
    /// - instTransNatLt : Trans Nat.lt Nat.lt Nat.lt
    ///
    /// Note: Nat.lt_trans is added as an axiom. The actual proof would use
    /// transitivity of ≤ combined with the definition of <.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_lt_trans_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_lt_trans(&mut self) -> Result<(), EnvError> {
        if self.nat_lt_trans_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat()?;
        self.init_lt()?;
        // `init_trans` only seeds the `Trans` typeclass needed to build the
        // `instTransNatLt` instance below. In import mode that stub is suppressed
        // (the genuine 6-universe Mathlib `Trans` comes from the olean closure),
        // so we skip both `init_trans` and the instance build — only the
        // standalone `Nat.lt_trans` theorem is registered.
        if !self.suppress_lossy_structure_stubs {
            self.init_trans()?;
        }

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

        // Nat.lt_trans : ∀ a b c : Nat, Nat.lt a b → Nat.lt b c → Nat.lt a c
        //
        // SOUNDNESS (#3604 kernel-order-soundness): Converted from
        // Declaration::Axiom to constructive Declaration::Theorem. The proof
        // body recurses on the second hypothesis via `Nat.le.rec` at parameter
        // `Nat.succ b` (since `Nat.lt n m` reduces to `Nat.le (Nat.succ n) m`),
        // lifting `hab` by `Nat.le.step` in the refl case. See
        // `order_nat_lt_trans_proof.rs`. Empty domain-axiom closure
        // (`ProofQuality::Constructive`). `register_nat_lt_trans_proof` is a
        // `get_const`-guarded no-op when already present.
        self.register_nat_lt_trans_proof()?;

        let nat_lt_relation = nat_lt_relation();

        // instTransNatLt : Trans.{1,1,1} Nat Nat Nat Nat.lt Nat.lt Nat.lt
        // Homogeneous Trans: α = β = γ = Nat, r = s = t = Nat.lt
        let level_one = Level::succ(Level::zero());
        let inst_trans_nat_lt_type = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::const_(
                                    Name::from_string("Trans"),
                                    vec![level_one.clone(), level_one.clone(), level_one.clone()],
                                ),
                                nat_const.clone(), // α = Nat
                            ),
                            nat_const.clone(), // β = Nat
                        ),
                        nat_const.clone(), // γ = Nat
                    ),
                    nat_lt_relation.clone(), // r = Nat.lt
                ),
                nat_lt_relation.clone(), // s = Nat.lt
            ),
            nat_lt_relation.clone(), // t = Nat.lt
        );

        // SOUNDNESS (KKL-finish TCB shrink): the `Trans Nat.lt Nat.lt Nat.lt`
        // instance is now a CONSTRUCTIVE `Declaration::Definition` built from the
        // already-proved `Nat.lt_trans` Theorem via `Trans.mk` — not an admitted
        // axiom. Value:
        //   @Trans.mk.{1,1,1} Nat Nat Nat Nat.lt Nat.lt Nat.lt
        //     (fun {a b c} hab hbc => Nat.lt_trans a b c hab hbc).
        if !self.suppress_lossy_structure_stubs
            && self
                .get_const(&Name::from_string("instTransNatLt"))
                .is_none_or(|info| {
                    !matches!(info.kind, crate::env::types::ConstantKind::Definition)
                })
        {
            let one = Level::succ(Level::zero());
            let nat_lt = |a: Expr, b: Expr| {
                Expr::apps(Expr::const_(Name::from_string("Nat.lt"), vec![]), [a, b])
            };
            let proof = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(nat_const.clone());
                let (bv_id, bv) = b.fresh_local(nat_const.clone());
                let (c_id, c) = b.fresh_local(nat_const.clone());
                let hab_ty = nat_lt(a.clone(), bv.clone());
                let (hab_id, hab) = b.fresh_local(hab_ty.clone());
                let hbc_ty = nat_lt(bv.clone(), c.clone());
                let (hbc_id, hbc) = b.fresh_local(hbc_ty.clone());
                let body = Expr::apps(
                    Expr::const_(Name::from_string("Nat.lt_trans"), vec![]),
                    [a.clone(), bv.clone(), c.clone(), hab, hbc],
                );
                let e = b.mk_lam(hbc_id, BinderInfo::Default, hbc_ty, body);
                let e = b.mk_lam(hab_id, BinderInfo::Default, hab_ty, e);
                let e = b.mk_lam(c_id, BinderInfo::Implicit, nat_const.clone(), e);
                let e = b.mk_lam(bv_id, BinderInfo::Implicit, nat_const.clone(), e);
                let e = b.mk_lam(a_id, BinderInfo::Implicit, nat_const.clone(), e);
                b.finish(e)
            };
            let value = Expr::apps(
                Expr::const_(
                    Name::from_string("Trans.mk"),
                    vec![one.clone(), one.clone(), one],
                ),
                [
                    nat_const.clone(),
                    nat_const.clone(),
                    nat_const.clone(),
                    nat_lt_relation.clone(),
                    nat_lt_relation.clone(),
                    nat_lt_relation.clone(),
                    proof,
                ],
            );
            self.discharge_axiom_for_redefinition(&Name::from_string("instTransNatLt"));
            self.add_decl(Declaration::Definition {
                name: Name::from_string("instTransNatLt"),
                level_params: vec![],
                type_: inst_trans_nat_lt_type,
                value,
                is_reducible: false,
            })?;
        }

        self.nat_lt_trans_init = true;
        Ok(())
    }

    /// Check if Nat.lt Trans instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_lt_trans_init == true`
    pub(crate) fn has_nat_lt_trans(&self) -> bool {
        self.nat_lt_trans_init
    }

    /// Initialize Antisymm instance for Nat.le
    ///
    /// This adds:
    /// - Nat.le_antisymm : axiom ∀ a b : Nat, Nat.le a b → Nat.le b a → a = b
    /// - instAntisymmNatLe : Antisymm Nat.le
    ///
    /// Note: Nat.le_antisymm is added as an axiom. The actual proof would use
    /// induction on the le relation.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_le_antisymm_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_le_antisymm(&mut self) -> Result<(), EnvError> {
        if self.nat_le_antisymm_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat()?;
        self.init_le()?;
        self.init_eq()?;
        self.init_antisymm()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

        // `Nat.le_antisymm` is now a constructive `Declaration::Theorem` proved
        // via `Nat.le.rec` (#3599). Construction lives in
        // `order_nat_le_antisymm_proof.rs`; it uses `nat_le_tc` (LE.le typeclass
        // form) so the registered signature matches the prior axiom and the
        // PartialOrder / Antisymm callers. `register_*` is idempotent, so it is
        // a no-op if `init_nat_partial_order` already registered the theorem.
        self.register_nat_le_antisymm_proof()?;

        let nat_le_relation = nat_le_relation();

        // instAntisymmNatLe : Antisymm (fun a b => Nat.le a b)
        let inst_antisymm_nat_le_type = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Antisymm"),
                    vec![Level::succ(Level::zero())],
                ),
                nat_const.clone(),
            ),
            nat_le_relation.clone(),
        );

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("instAntisymmNatLe"),
            level_params: vec![],
            type_: inst_antisymm_nat_le_type,
        })?;

        self.nat_le_antisymm_init = true;
        Ok(())
    }

    /// Check if Nat.le Antisymm instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_le_antisymm_init == true`
    pub(crate) fn has_nat_le_antisymm(&self) -> bool {
        self.nat_le_antisymm_init
    }

    /// Initialize Trans instance for Nat.le
    ///
    /// This adds:
    /// - Nat.le_trans : theorem ∀ a b c : Nat, Nat.le a b → Nat.le b c → Nat.le a c
    ///   (proved from `Nat.le.rec` — see `order_nat_le_trans_proof.rs`, #3552)
    /// - instTransNatLe : Trans Nat.le Nat.le Nat.le
    ///
    /// `Nat.le_trans` is now a constructive theorem (#3552). If it was
    /// already registered by `init_nat_preorder`, `register_nat_le_trans_proof`
    /// is idempotent and becomes a no-op.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_le_trans_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_le_trans(&mut self) -> Result<(), EnvError> {
        if self.nat_le_trans_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat()?;
        self.init_le()?;
        // `init_trans` only seeds the `Trans` typeclass needed to build the
        // `instTransNatLe` instance below. In import mode that stub is suppressed
        // (the genuine 6-universe Mathlib `Trans` comes from the olean closure),
        // so we skip both `init_trans` and the instance build — only the
        // standalone `Nat.le_trans` theorem is registered.
        if !self.suppress_lossy_structure_stubs {
            self.init_trans()?;
        }

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

        // Register `Nat.le_trans` as a constructive theorem (#3552).
        // No-op if already present from `init_nat_preorder`.
        self.register_nat_le_trans_proof()?;

        if !self.suppress_lossy_structure_stubs {
            let nat_le_relation = nat_le_relation();

            // instTransNatLe : Trans.{1,1,1} Nat Nat Nat Nat.le Nat.le Nat.le
            // Homogeneous Trans: α = β = γ = Nat, r = s = t = Nat.le
            let level_one = Level::succ(Level::zero());
            let inst_trans_nat_le_type = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::const_(
                                        Name::from_string("Trans"),
                                        vec![
                                            level_one.clone(),
                                            level_one.clone(),
                                            level_one.clone(),
                                        ],
                                    ),
                                    nat_const.clone(), // α = Nat
                                ),
                                nat_const.clone(), // β = Nat
                            ),
                            nat_const.clone(), // γ = Nat
                        ),
                        nat_le_relation.clone(), // r = Nat.le
                    ),
                    nat_le_relation.clone(), // s = Nat.le
                ),
                nat_le_relation.clone(), // t = Nat.le
            );

            self.add_decl(Declaration::Axiom {
                name: Name::from_string("instTransNatLe"),
                level_params: vec![],
                type_: inst_trans_nat_le_type,
            })?;
        }

        self.nat_le_trans_init = true;
        Ok(())
    }

    /// Check if Nat.le Trans instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_le_trans_init == true`
    pub(crate) fn has_nat_le_trans(&self) -> bool {
        self.nat_le_trans_init
    }
}
