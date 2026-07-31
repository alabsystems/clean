// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nat ordering lemmas for Environment
//!
//! Split from order.rs (#307). Contains:
//! - StrictOrder typeclass and Nat.lt instance
//! - Mixed Trans instances (lt/le combinations)
//! - Ordering lemmas (lt_or_eq_of_le, lt_of_le_of_ne, not_lt/not_le)
//!
//! Successor lemmas, trichotomy, decidable instances, and min/max lemmas
//! are in order_lemmas_succ.rs.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::order::{nat_le_relation, nat_le_tc, nat_lt_relation, nat_lt_tc};
#[cfg(test)]
use crate::env::{Constructor, InductiveDecl, InductiveType};
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Build `@Trans.{1,1,1} Nat Nat Nat r s t` — the `Trans` instance *type* for
/// three Nat-valued binary relations `r`, `s`, `t`.
fn nat_trans_app(nat: &Expr, r: &Expr, s: &Expr, t: &Expr) -> Expr {
    let one = Level::succ(Level::zero());
    let head = Expr::const_(
        Name::from_string("Trans"),
        vec![one.clone(), one.clone(), one],
    );
    Expr::apps(
        head,
        [
            nat.clone(),
            nat.clone(),
            nat.clone(),
            r.clone(),
            s.clone(),
            t.clone(),
        ],
    )
}

/// Build the `Trans.mk` proof field for a Nat mixed-transitivity instance:
/// `fun {a b c : Nat} (hab : <r a b>) (hbc : <s b c>) => <lemma> a b c hab hbc`,
/// where `<r a b>`, `<s b c>`, `<t a c>` are produced by the three closures and
/// `lemma : ∀ a b c : Nat, <r a b> → <s b c> → <t a c>` is an already-registered
/// constructive theorem. The `{a b c}` binders are `Implicit` to match the
/// `Trans.mk` proof-field signature `∀ {a b c}, r a b → s b c → t a c`.
fn nat_trans_proof_field(
    nat: &Expr,
    r_app: impl Fn(Expr, Expr) -> Expr,
    s_app: impl Fn(Expr, Expr) -> Expr,
    t_app: impl Fn(Expr, Expr) -> Expr,
    lemma: Name,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nat.clone());
    let (bv_id, bv) = b.fresh_local(nat.clone());
    let (c_id, c) = b.fresh_local(nat.clone());
    let hab_type = r_app(a.clone(), bv.clone());
    let (hab_id, hab) = b.fresh_local(hab_type.clone());
    let hbc_type = s_app(bv.clone(), c.clone());
    let (hbc_id, hbc) = b.fresh_local(hbc_type.clone());

    // `t a c` is the result type the proof field must produce (unused as an
    // explicit annotation — the kernel infers it — but evaluating the closure
    // documents intent and keeps the API symmetric).
    let _result_type = t_app(a.clone(), c.clone());

    let body = Expr::apps(
        Expr::const_(lemma, vec![]),
        [a.clone(), bv.clone(), c.clone(), hab, hbc],
    );
    let e = b.mk_lam(hbc_id, BinderInfo::Default, hbc_type, body);
    let e = b.mk_lam(hab_id, BinderInfo::Default, hab_type, e);
    let e = b.mk_lam(c_id, BinderInfo::Implicit, nat.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Implicit, nat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Implicit, nat.clone(), e);
    b.finish(e)
}

/// Build `@Trans.mk.{1,1,1} Nat Nat Nat r s t proof` — the constructive `Trans`
/// instance *value*.
fn nat_trans_mk_app(nat: &Expr, r: &Expr, s: &Expr, t: &Expr, proof: Expr) -> Expr {
    let one = Level::succ(Level::zero());
    let head = Expr::const_(
        Name::from_string("Trans.mk"),
        vec![one.clone(), one.clone(), one],
    );
    Expr::apps(
        head,
        [
            nat.clone(),
            nat.clone(),
            nat.clone(),
            r.clone(),
            s.clone(),
            t.clone(),
            proof,
        ],
    )
}

impl Environment {
    /// Initialize StrictOrder typeclass
    ///
    /// StrictOrder is a typeclass for strict orderings combining Irrefl and Trans:
    /// - StrictOrder : {α : Sort u} → (α → α → Prop) → Prop
    /// - StrictOrder.mk : {α : Sort u} → {r : α → α → Prop} →
    ///                    [Irrefl r] → [Trans r] → StrictOrder r
    ///
    /// StrictOrder.toIrrefl : {α : Sort u} → {r : α → α → Prop} → [StrictOrder r] → Irrefl r
    /// StrictOrder.toTrans : {α : Sort u} → {r : α → α → Prop} → [StrictOrder r] → Trans r
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.strict_order_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_strict_order(&mut self) -> Result<(), EnvError> {
        if self.strict_order_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_irrefl()?;
        self.init_trans()?;

        // u : Level variable
        let u_name = Name::from_string("u");
        let u_level = Level::param(u_name.clone());

        let sort_u = Expr::sort(u_level.clone());
        let relation_type = |carrier: Expr| {
            Expr::pi(
                BinderInfo::Default,
                carrier.clone(),
                Expr::pi(
                    BinderInfo::Default,
                    carrier,
                    Expr::sort(Level::zero()), // Prop
                ),
            )
        };

        // StrictOrder : {α : Sort u} → (α → α → Prop) → Prop
        // Built with EnvDeclBuilder (#1444).
        let strict_order_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let rel_type = relation_type(alpha.clone());
            let (r_id, _r) = b.fresh_local(rel_type.clone());
            let e = b.mk_pi(
                r_id,
                BinderInfo::Default,
                rel_type,
                Expr::sort(Level::zero()),
            );
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        // StrictOrder.mk : {α : Sort u} → {r : α → α → Prop} →
        //                  [Irrefl r] → [Trans r] → StrictOrder r
        // Built with EnvDeclBuilder (#1444).
        let strict_order_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let rel_type = relation_type(alpha.clone());
            let (r_id, r) = b.fresh_local(rel_type.clone());

            let irrefl_r = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Irrefl"), vec![u_level.clone()]),
                    alpha.clone(),
                ),
                r.clone(),
            );
            let (irrefl_id, _irrefl_inst) = b.fresh_local(irrefl_r.clone());

            // Trans.{u,u,u} α α α r r r — homogeneous Trans for StrictOrder
            let trans_r = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::const_(
                                        Name::from_string("Trans"),
                                        vec![u_level.clone(), u_level.clone(), u_level.clone()],
                                    ),
                                    alpha.clone(), // α
                                ),
                                alpha.clone(), // β = α
                            ),
                            alpha.clone(), // γ = α
                        ),
                        r.clone(), // r
                    ),
                    r.clone(), // s = r
                ),
                r.clone(), // t = r
            );
            let (trans_id, _trans_inst) = b.fresh_local(trans_r.clone());

            let strict_order_r = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("StrictOrder"), vec![u_level.clone()]),
                    alpha.clone(),
                ),
                r,
            );

            let e = b.mk_pi(trans_id, BinderInfo::InstImplicit, trans_r, strict_order_r);
            let e = b.mk_pi(irrefl_id, BinderInfo::InstImplicit, irrefl_r, e);
            let e = b.mk_pi(r_id, BinderInfo::Implicit, rel_type, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        // Define the inductive type StrictOrder as a structure with one constructor
        let strict_order_ind = InductiveDecl {
            level_params: vec![u_name.clone()],
            num_params: 2, // α and r are parameters
            types: vec![InductiveType {
                name: Name::from_string("StrictOrder"),
                type_: strict_order_type,
                constructors: vec![Constructor {
                    name: Name::from_string("StrictOrder.mk"),
                    type_: strict_order_mk_type,
                }],
            }],
        };

        self.add_inductive(strict_order_ind)?;

        self.strict_order_init = true;
        Ok(())
    }

    /// Check if StrictOrder typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.strict_order_init == true`
    #[cfg(test)]
    pub(crate) fn has_strict_order(&self) -> bool {
        self.strict_order_init
    }

    /// Initialize StrictOrder instance for Nat.lt
    ///
    /// This adds:
    /// - instStrictOrderNatLt : StrictOrder Nat.lt
    ///
    /// Uses instIrreflNatLt and instTransNatLt instances.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_lt_strict_order_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_nat_lt_strict_order(&mut self) -> Result<(), EnvError> {
        if self.nat_lt_strict_order_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat()?;
        self.init_lt()?;
        self.init_strict_order()?;
        self.init_nat_lt_irrefl()?;
        self.init_nat_lt_trans()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

        let nat_lt_relation = nat_lt_relation();

        // instStrictOrderNatLt : StrictOrder (fun a b => LT.lt @Nat instLTNat a b)
        let inst_strict_order_nat_lt_type = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("StrictOrder"),
                    vec![Level::succ(Level::zero())],
                ),
                nat_const.clone(),
            ),
            nat_lt_relation.clone(),
        );

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("instStrictOrderNatLt"),
            level_params: vec![],
            type_: inst_strict_order_nat_lt_type,
        })?;

        self.nat_lt_strict_order_init = true;
        Ok(())
    }

    /// Check if Nat.lt StrictOrder instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_lt_strict_order_init == true`
    #[cfg(test)]
    pub(crate) fn has_nat_lt_strict_order(&self) -> bool {
        self.nat_lt_strict_order_init
    }

    /// Initialize mixed Trans instance for Nat: (lt, le) → lt
    ///
    /// This adds:
    /// - Nat.lt_of_lt_of_le : theorem ∀ a b c : Nat, Nat.lt a b → Nat.le b c → Nat.lt a c
    ///   (proved constructively from `Nat.le_trans` — see
    ///   `register_nat_lt_of_lt_of_le_proof`, #3551)
    /// - instTransNatLtLeLt : Trans Nat.lt Nat.le Nat.lt
    ///
    /// This allows transitivity like: a < b ∧ b ≤ c → a < c
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_trans_lt_le_lt_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_trans_lt_le_lt(&mut self) -> Result<(), EnvError> {
        if self.nat_trans_lt_le_lt_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat()?;
        // The `Trans` stub is suppressed in import mode (genuine 6-universe
        // Mathlib `Trans` comes from the olean closure); skip both the stub and
        // the `instTransNatLtLeLt` build below — only the standalone
        // `Nat.lt_of_lt_of_le` theorem is registered.
        if !self.suppress_lossy_structure_stubs {
            self.init_trans()?;
        }
        self.init_le()?;
        self.init_lt()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

        // Nat.lt_of_lt_of_le : ∀ a b c : Nat, Nat.lt a b → Nat.le b c → Nat.lt a c
        // Promoted from Axiom to constructive Theorem (#3551). See
        // `register_nat_lt_of_lt_of_le_proof` below.
        self.register_nat_lt_of_lt_of_le_proof()?;

        if !self.suppress_lossy_structure_stubs {
            let nat_lt_relation = nat_lt_relation();
            let nat_le_relation = nat_le_relation();

            // instTransNatLtLeLt : Trans Nat.lt Nat.le Nat.lt
            let inst_type = nat_trans_app(
                &nat_const,
                &nat_lt_relation, // r = Nat.lt
                &nat_le_relation, // s = Nat.le
                &nat_lt_relation, // t = Nat.lt
            );

            // Constructive value (#3551 follow-up): build the Trans instance with
            // `Trans.mk`, discharging the proof field with the already-constructive
            // `Nat.lt_of_lt_of_le`. The proof field has type
            // `∀ {a b c : Nat}, r a b → s b c → t a c`; with r = Nat.lt relation,
            // s = Nat.le relation, t = Nat.lt relation, `r a b` is defeq to
            // `nat_lt_tc a b` and `s b c` to `nat_le_tc b c`, exactly the
            // hypothesis types of `Nat.lt_of_lt_of_le a b c`. No new axioms.
            let proof_field = nat_trans_proof_field(
                &nat_const,
                nat_lt_tc, // r a b
                nat_le_tc, // s b c
                nat_lt_tc, // t a c
                Name::from_string("Nat.lt_of_lt_of_le"),
            );

            let inst_value = nat_trans_mk_app(
                &nat_const,
                &nat_lt_relation,
                &nat_le_relation,
                &nat_lt_relation,
                proof_field,
            );

            self.add_decl(Declaration::Definition {
                name: Name::from_string("instTransNatLtLeLt"),
                level_params: vec![],
                type_: inst_type,
                value: inst_value,
                is_reducible: false,
            })?;
        }

        self.nat_trans_lt_le_lt_init = true;
        Ok(())
    }

    /// Check if mixed Trans (lt, le) -> lt instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_trans_lt_le_lt_init == true`
    #[cfg(test)]
    pub(crate) fn has_nat_trans_lt_le_lt(&self) -> bool {
        self.nat_trans_lt_le_lt_init
    }

    /// Initialize mixed Trans instance for Nat: (le, lt) → lt
    ///
    /// This adds:
    /// - Nat.lt_of_le_of_lt : theorem ∀ a b c : Nat, Nat.le a b → Nat.lt b c → Nat.lt a c
    ///   (proved constructively from `Nat.succ_le_succ` + `Nat.le_trans` — see
    ///   `register_nat_lt_of_le_of_lt_proof`, #3551)
    /// - instTransNatLeLtLt : Trans Nat.le Nat.lt Nat.lt
    ///
    /// This allows transitivity like: a ≤ b ∧ b < c → a < c
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_trans_le_lt_lt_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_trans_le_lt_lt(&mut self) -> Result<(), EnvError> {
        if self.nat_trans_le_lt_lt_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat()?;
        // The `Trans` stub is suppressed in import mode (genuine 6-universe
        // Mathlib `Trans` comes from the olean closure); skip both the stub and
        // the `instTransNatLeLtLt` build below — only the standalone
        // `Nat.lt_of_le_of_lt` theorem is registered.
        if !self.suppress_lossy_structure_stubs {
            self.init_trans()?;
        }
        self.init_le()?;
        self.init_lt()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

        // Nat.lt_of_le_of_lt : ∀ a b c : Nat, Nat.le a b → Nat.lt b c → Nat.lt a c
        // Promoted from Axiom to constructive Theorem (#3551). See
        // `register_nat_lt_of_le_of_lt_proof` below.
        self.register_nat_lt_of_le_of_lt_proof()?;

        if !self.suppress_lossy_structure_stubs {
            let nat_le_relation = nat_le_relation();
            let nat_lt_relation = nat_lt_relation();

            // instTransNatLeLtLt : Trans Nat.le Nat.lt Nat.lt
            let inst_type = nat_trans_app(
                &nat_const,
                &nat_le_relation, // r = Nat.le
                &nat_lt_relation, // s = Nat.lt
                &nat_lt_relation, // t = Nat.lt
            );

            // Constructive value (#3551 follow-up): discharge the Trans proof field
            // with the already-constructive `Nat.lt_of_le_of_lt`. The proof field
            // has type `∀ {a b c : Nat}, r a b → s b c → t a c`; with r = Nat.le
            // relation, s = Nat.lt relation, t = Nat.lt relation, `r a b` is defeq
            // to `nat_le_tc a b` and `s b c` to `nat_lt_tc b c`, exactly the
            // hypothesis types of `Nat.lt_of_le_of_lt a b c`. No new axioms.
            let proof_field = nat_trans_proof_field(
                &nat_const,
                nat_le_tc, // r a b
                nat_lt_tc, // s b c
                nat_lt_tc, // t a c
                Name::from_string("Nat.lt_of_le_of_lt"),
            );

            let inst_value = nat_trans_mk_app(
                &nat_const,
                &nat_le_relation,
                &nat_lt_relation,
                &nat_lt_relation,
                proof_field,
            );

            self.add_decl(Declaration::Definition {
                name: Name::from_string("instTransNatLeLtLt"),
                level_params: vec![],
                type_: inst_type,
                value: inst_value,
                is_reducible: false,
            })?;
        }

        self.nat_trans_le_lt_lt_init = true;
        Ok(())
    }

    /// Check if mixed Trans (le, lt) -> lt instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_trans_le_lt_lt_init == true`
    #[cfg(test)]
    pub(crate) fn has_nat_trans_le_lt_lt(&self) -> bool {
        self.nat_trans_le_lt_lt_init
    }

    /// Initialize mixed Trans instance for Nat: (lt, lt) → le
    ///
    /// This adds:
    /// - Nat.le_of_lt : axiom ∀ a b : Nat, Nat.lt a b → Nat.le a b
    /// - instTransNatLtLtLe : Trans Nat.lt Nat.lt Nat.le
    ///
    /// This allows transitivity like: a < b ∧ b < c → a ≤ c
    /// (since a < b < c implies a < c, and a < c implies a ≤ c)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_trans_lt_lt_le_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_trans_lt_lt_le(&mut self) -> Result<(), EnvError> {
        if self.nat_trans_lt_lt_le_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat()?;
        // The `Trans` stub is suppressed in import mode (genuine 6-universe
        // Mathlib `Trans` comes from the olean closure); skip both the stub and
        // the `instTransNatLtLtLe` build below — only the standalone
        // `Nat.le_of_lt` theorem is registered.
        if !self.suppress_lossy_structure_stubs {
            self.init_trans()?;
        }
        self.init_le()?;
        self.init_lt()?;
        self.init_nat_lt_trans()?; // We need Nat.lt_trans

        // #3599: Promote Nat.le_of_lt from Axiom to constructive Theorem.
        // init_nat_top_level_ordering must run before the
        // add_init_axiom_if_absent call below so the Theorem is registered
        // first; the axiom form is then skipped (no-op) per
        // add_init_axiom_if_absent's "already-present" return.
        self.init_nat_top_level_ordering()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_lt = nat_lt_tc;
        let nat_le = nat_le_tc;

        // First add Nat.le_of_lt : ∀ a b : Nat, Nat.lt a b → Nat.le a b
        // Built with EnvDeclBuilder (#1444).
        self.add_init_axiom_if_absent("Nat.le_of_lt", &[], || {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (bv_id, bv) = b.fresh_local(nat_const.clone());
            let h_type = nat_lt(a.clone(), bv.clone());
            let (h_id, _h) = b.fresh_local(h_type.clone());
            let body = nat_le(a.clone(), bv.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type, body);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        })?;

        // SOUNDNESS (KKL-finish TCB shrink): the `Trans Nat.lt Nat.lt Nat.le`
        // instance is now a CONSTRUCTIVE `Declaration::Definition` via `Trans.mk`,
        // its proof field `fun {a b c} hab hbc => Nat.le_of_lt a c
        // (Nat.lt_trans a b c hab hbc)` — both leaves are already-proved
        // constructive Theorems — not an admitted axiom.
        if !self.suppress_lossy_structure_stubs
            && self
                .get_const(&Name::from_string("instTransNatLtLtLe"))
                .is_none_or(|info| {
                    !matches!(info.kind, crate::env::types::ConstantKind::Definition)
                })
        {
            let nat_lt_relation = nat_lt_relation();
            let nat_le_relation = nat_le_relation();

            // instTransNatLtLtLe : Trans Nat.lt Nat.lt Nat.le
            let level_one = Level::succ(Level::zero());
            let inst_type = Expr::app(
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
                        nat_lt_relation.clone(), // r = Nat.lt
                    ),
                    nat_lt_relation.clone(), // s = Nat.lt
                ),
                nat_le_relation.clone(), // t = Nat.le
            );
            let one = Level::succ(Level::zero());
            let proof = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(nat_const.clone());
                let (bv_id, bv) = b.fresh_local(nat_const.clone());
                let (c_id, c) = b.fresh_local(nat_const.clone());
                let hab_ty = nat_lt(a.clone(), bv.clone());
                let (hab_id, hab) = b.fresh_local(hab_ty.clone());
                let hbc_ty = nat_lt(bv.clone(), c.clone());
                let (hbc_id, hbc) = b.fresh_local(hbc_ty.clone());
                // Nat.lt_trans a b c hab hbc : Nat.lt a c.
                let lt_ac = Expr::apps(
                    Expr::const_(Name::from_string("Nat.lt_trans"), vec![]),
                    [a.clone(), bv.clone(), c.clone(), hab, hbc],
                );
                // Nat.le_of_lt a c (…) : Nat.le a c.
                let body = Expr::apps(
                    Expr::const_(Name::from_string("Nat.le_of_lt"), vec![]),
                    [a.clone(), c.clone(), lt_ac],
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
                    nat_le_relation.clone(),
                    proof,
                ],
            );
            self.discharge_axiom_for_redefinition(&Name::from_string("instTransNatLtLtLe"));
            self.add_decl(Declaration::Definition {
                name: Name::from_string("instTransNatLtLtLe"),
                level_params: vec![],
                type_: inst_type,
                value,
                is_reducible: false,
            })?;
        }

        self.nat_trans_lt_lt_le_init = true;
        Ok(())
    }

    /// Check if mixed Trans (lt, lt) -> le instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_trans_lt_lt_le_init == true`
    #[cfg(test)]
    pub(crate) fn has_nat_trans_lt_lt_le(&self) -> bool {
        self.nat_trans_lt_lt_le_init
    }

    /// Initialize Nat.lt_or_eq_of_le lemma
    ///
    /// This adds:
    /// - Nat.lt_or_eq_of_le : axiom ∀ a b : Nat, Nat.le a b → Or (Nat.lt a b) (Eq a b)
    ///
    /// If a ≤ b, then either a < b or a = b.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_lt_or_eq_of_le_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn init_nat_lt_or_eq_of_le(&mut self) -> Result<(), EnvError> {
        if self.nat_lt_or_eq_of_le_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat()?;
        self.init_le()?;
        self.init_lt()?;
        self.init_eq()?;
        self.init_classical()?; // Or is defined in init_classical (#1488)

        // Prefer the constructive `Declaration::Theorem` form of
        // `Nat.lt_or_eq_of_le` (proved by `Nat.le.rec` in
        // `nat_totality_proof.rs`). Idempotent; the legacy axiom below is
        // guarded so it becomes a no-op once the Theorem is present.
        self.init_nat_totality_proofs()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let or_const = Expr::const_(Name::from_string("Or"), vec![]);

        // Nat.lt_or_eq_of_le : ∀ a b : Nat, Nat.le a b → Or (Nat.lt a b) (Eq a b)
        // Built with EnvDeclBuilder (#1444).
        let lemma_type = {
            let nat_le = nat_le_tc;
            let nat_lt = nat_lt_tc;
            let nat_eq = |lhs: Expr, rhs: Expr| {
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                            nat_const.clone(),
                        ),
                        lhs,
                    ),
                    rhs,
                )
            };
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (bv_id, bv) = b.fresh_local(nat_const.clone());
            let h_type = nat_le(a.clone(), bv.clone());
            let (h_id, _h) = b.fresh_local(h_type.clone());
            let body = Expr::app(
                Expr::app(or_const.clone(), nat_lt(a.clone(), bv.clone())),
                nat_eq(a.clone(), bv.clone()),
            );
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type, body);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // Guarded: skip if the constructive Theorem form is already registered.
        if self
            .get_const(&Name::from_string("Nat.lt_or_eq_of_le"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.lt_or_eq_of_le"),
                level_params: vec![],
                type_: lemma_type,
            })?;
        }

        self.nat_lt_or_eq_of_le_init = true;
        Ok(())
    }

    /// Check if Nat.lt_or_eq_of_le lemma has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_lt_or_eq_of_le_init == true`
    #[cfg(test)]
    pub(crate) fn has_nat_lt_or_eq_of_le(&self) -> bool {
        self.nat_lt_or_eq_of_le_init
    }

    /// Initialize Nat.lt_of_le_of_ne lemma
    ///
    /// This adds:
    /// - Nat.lt_of_le_of_ne : axiom ∀ a b : Nat, Nat.le a b → (Eq a b → False) → Nat.lt a b
    ///
    /// If a ≤ b and a ≠ b, then a < b.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_lt_of_le_of_ne_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_nat_lt_of_le_of_ne(&mut self) -> Result<(), EnvError> {
        if self.nat_lt_of_le_of_ne_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat()?;
        self.init_le()?;
        self.init_lt()?;
        self.init_eq()?;
        self.init_true_false()?; // False is defined in init_true_false (#1488)

        // Prefer the constructive `Declaration::Theorem` form of
        // `Nat.lt_of_le_of_ne` (proved via `Nat.lt_or_eq_of_le` + `False.elim`
        // in `nat_totality_proof.rs`). Idempotent; the legacy axiom below is
        // guarded so it becomes a no-op once the Theorem is present.
        self.init_nat_totality_proofs()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let false_const = Expr::const_(Name::from_string("False"), vec![]);

        // Nat.lt_of_le_of_ne : ∀ a b : Nat, Nat.le a b → (Eq a b → False) → Nat.lt a b
        // Built with EnvDeclBuilder (#1444).
        let lemma_type = {
            let nat_le = nat_le_tc;
            let nat_lt = nat_lt_tc;
            let nat_eq = |lhs: Expr, rhs: Expr| {
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                            nat_const.clone(),
                        ),
                        lhs,
                    ),
                    rhs,
                )
            };
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (bv_id, bv) = b.fresh_local(nat_const.clone());
            let hle_type = nat_le(a.clone(), bv.clone());
            let (hle_id, _hle) = b.fresh_local(hle_type.clone());
            // (Eq a b → False) as a pi type
            let eq_ab = nat_eq(a.clone(), bv.clone());
            let ne_type = Expr::pi(BinderInfo::Default, eq_ab, false_const.clone());
            let (hne_id, _hne) = b.fresh_local(ne_type.clone());
            let body = nat_lt(a.clone(), bv.clone());
            let e = b.mk_pi(hne_id, BinderInfo::Default, ne_type, body);
            let e = b.mk_pi(hle_id, BinderInfo::Default, hle_type, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // Guarded: skip if the constructive Theorem form is already registered.
        if self
            .get_const(&Name::from_string("Nat.lt_of_le_of_ne"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.lt_of_le_of_ne"),
                level_params: vec![],
                type_: lemma_type,
            })?;
        }

        self.nat_lt_of_le_of_ne_init = true;
        Ok(())
    }

    /// Check if Nat.lt_of_le_of_ne lemma has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_lt_of_le_of_ne_init == true`
    #[cfg(test)]
    pub(crate) fn has_nat_lt_of_le_of_ne(&self) -> bool {
        self.nat_lt_of_le_of_ne_init
    }

    /// Initialize Nat.not_lt and Nat.not_le lemmas
    ///
    /// This adds:
    /// - Nat.not_lt : axiom ∀ a b : Nat, (Nat.lt a b → False) ↔ Nat.le b a
    /// - Nat.not_le : axiom ∀ a b : Nat, (Nat.le a b → False) ↔ Nat.lt b a
    ///
    /// These are the negation equivalences for ordering.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_not_lt_le_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_not_lt_le(&mut self) -> Result<(), EnvError> {
        if self.nat_not_lt_le_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat()?;
        self.init_le()?;
        self.init_lt()?;
        self.init_iff()?;
        self.init_true_false()?; // False is defined in init_true_false (#1488)

        // Prefer the constructive `Declaration::Theorem` forms of `Nat.not_lt`
        // and `Nat.not_le` (proved via `Nat.le_or_lt` + `Nat.lt_irrefl` in
        // `nat_totality_proof.rs`). Idempotent; the legacy axioms below are
        // guarded so they become no-ops once the Theorems are present.
        self.init_nat_totality_proofs()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let false_const = Expr::const_(Name::from_string("False"), vec![]);
        let iff_const = Expr::const_(Name::from_string("Iff"), vec![]);
        let nat_lt = nat_lt_tc;
        let nat_le = nat_le_tc;

        // Nat.not_lt : ∀ a b : Nat, Iff (Nat.lt a b → False) (Nat.le b a)
        // Built with EnvDeclBuilder (#1444).
        let not_lt_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (bv_id, bv) = b.fresh_local(nat_const.clone());
            let not_lt_ab = Expr::pi(
                BinderInfo::Default,
                nat_lt(a.clone(), bv.clone()),
                false_const.clone(),
            );
            let le_ba = nat_le(bv.clone(), a.clone());
            let body = Expr::app(Expr::app(iff_const.clone(), not_lt_ab), le_ba);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nat_const.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // Guarded: skip if the constructive Theorem form is already registered.
        if self.get_const(&Name::from_string("Nat.not_lt")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.not_lt"),
                level_params: vec![],
                type_: not_lt_type,
            })?;
        }

        // Nat.not_le : ∀ a b : Nat, Iff (Nat.le a b → False) (Nat.lt b a)
        // Built with EnvDeclBuilder (#1444).
        let not_le_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (bv_id, bv) = b.fresh_local(nat_const.clone());
            let not_le_ab = Expr::pi(
                BinderInfo::Default,
                nat_le(a.clone(), bv.clone()),
                false_const.clone(),
            );
            let lt_ba = nat_lt(bv.clone(), a.clone());
            let body = Expr::app(Expr::app(iff_const.clone(), not_le_ab), lt_ba);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nat_const.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // Guarded: skip if the constructive Theorem form is already registered.
        if self.get_const(&Name::from_string("Nat.not_le")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.not_le"),
                level_params: vec![],
                type_: not_le_type,
            })?;
        }

        self.nat_not_lt_le_init = true;
        Ok(())
    }

    /// Check if Nat.not_lt and Nat.not_le lemmas have been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_not_lt_le_init == true`
    #[cfg(test)]
    pub(crate) fn has_nat_not_lt_le(&self) -> bool {
        self.nat_not_lt_le_init
    }

    /// Register `Nat.lt_of_lt_of_le` as a kernel-checked `Declaration::Theorem`
    /// (#3551), replacing the prior `Declaration::Axiom` stub.
    ///
    /// Stated type (typeclass form):
    /// `∀ a b c : Nat, LT.lt @Nat instLTNat a b → LE.le @Nat instLENat b c
    ///                 → LT.lt @Nat instLTNat a c`.
    ///
    /// `Nat.lt` is the reducible Definition `fun x y => Nat.le (Nat.succ x) y`
    /// and `instLTNat` / `instLENat` are reducible wrappers, so the hypothesis
    /// `LT.lt a b` reduces to `Nat.le (Nat.succ a) b`, `LE.le b c` to
    /// `Nat.le b c`, and the conclusion `LT.lt a c` to `Nat.le (Nat.succ a) c`.
    /// The reduced goal is therefore exactly `Nat.le_trans` instantiated at
    /// `(Nat.succ a) b c`:
    ///
    /// ```text
    /// theorem Nat.lt_of_lt_of_le (a b c : Nat) (hab : a < b) (hbc : b ≤ c) : a < c :=
    ///   @Nat.le_trans (Nat.succ a) b c hab hbc
    /// ```
    ///
    /// `Nat.le_trans` is itself a constructive `Declaration::Theorem` with an
    /// empty domain-axiom closure (`order_nat_le_trans_proof.rs`, #3552), so
    /// `env.axiom_deps("Nat.lt_of_lt_of_le")` is empty and the proof quality
    /// is `Constructive`. No new axioms are introduced.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance.
    /// ENSURES: On success, `Nat.lt_of_lt_of_le` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — a no-op if the constant is already registered.
    fn register_nat_lt_of_lt_of_le_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.lt_of_lt_of_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // `Nat.le_trans` must be a registered constructive Theorem.
        self.register_nat_le_trans_proof()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_le_trans = Expr::const_(Name::from_string("Nat.le_trans"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat_const.clone());
        let (bv_id, bv) = b.fresh_local(nat_const.clone());
        let (c_id, c) = b.fresh_local(nat_const.clone());
        let hab_type = nat_lt_tc(a.clone(), bv.clone());
        let (hab_id, hab) = b.fresh_local(hab_type.clone());
        let hbc_type = nat_le_tc(bv.clone(), c.clone());
        let (hbc_id, hbc) = b.fresh_local(hbc_type.clone());

        // Type: ∀ a b c, LT.lt a b → LE.le b c → LT.lt a c
        let ty = {
            let concl = nat_lt_tc(a.clone(), c.clone());
            let e = b.mk_pi(hbc_id, BinderInfo::Default, hbc_type.clone(), concl);
            let e = b.mk_pi(hab_id, BinderInfo::Default, hab_type.clone(), e);
            let e = b.mk_pi(c_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // Value: fun a b c hab hbc => @Nat.le_trans (Nat.succ a) b c hab hbc
        let value = {
            let succ_a = Expr::app(nat_succ.clone(), a.clone());
            let body = Expr::apps(
                nat_le_trans,
                [succ_a, bv.clone(), c.clone(), hab.clone(), hbc.clone()],
            );
            let e = b.mk_lam(hbc_id, BinderInfo::Default, hbc_type, body);
            let e = b.mk_lam(hab_id, BinderInfo::Default, hab_type, e);
            let e = b.mk_lam(c_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_lam(bv_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Register `Nat.lt_of_le_of_lt` as a kernel-checked `Declaration::Theorem`
    /// (#3551), replacing the prior `Declaration::Axiom` stub.
    ///
    /// Stated type (typeclass form):
    /// `∀ a b c : Nat, LE.le @Nat instLENat a b → LT.lt @Nat instLTNat b c
    ///                 → LT.lt @Nat instLTNat a c`.
    ///
    /// By reducibility of `Nat.lt` / `instLTNat` / `instLENat`, the hypotheses
    /// reduce to `hab : Nat.le a b` and `hbc : Nat.le (Nat.succ b) c`, and the
    /// conclusion to `Nat.le (Nat.succ a) c`. From `hab` we obtain
    /// `Nat.succ_le_succ a b hab : Nat.le (Nat.succ a) (Nat.succ b)`, then
    /// chain with `hbc` via `Nat.le_trans (Nat.succ a) (Nat.succ b) c`:
    ///
    /// ```text
    /// theorem Nat.lt_of_le_of_lt (a b c : Nat) (hab : a ≤ b) (hbc : b < c) : a < c :=
    ///   @Nat.le_trans (Nat.succ a) (Nat.succ b) c (@Nat.succ_le_succ a b hab) hbc
    /// ```
    ///
    /// Both `Nat.succ_le_succ` (raw `Nat.le` form, `nat_top_level_ordering_proof.rs`)
    /// and `Nat.le_trans` (`order_nat_le_trans_proof.rs`) are constructive
    /// `Declaration::Theorem`s with empty domain-axiom closures, so
    /// `env.axiom_deps("Nat.lt_of_le_of_lt")` is empty and the proof quality is
    /// `Constructive`. The `Nat.succ_le_succ` result (raw `Nat.le (Nat.succ a)
    /// (Nat.succ b)`) and the incoming `hab : LE.le a b` are accepted where the
    /// reducible `LE.le @Nat instLENat …` form is expected (defeq through
    /// `instLENat`). No new axioms are introduced.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance.
    /// ENSURES: On success, `Nat.lt_of_le_of_lt` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — a no-op if the constant is already registered.
    fn register_nat_lt_of_le_of_lt_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.lt_of_le_of_lt");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // `Nat.succ_le_succ` (raw Nat.le form) and `Nat.le_trans` must both be
        // registered as constructive Theorems.
        self.init_nat_top_level_ordering()?; // registers Nat.succ_le_succ
        self.register_nat_le_trans_proof()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_succ_le_succ = Expr::const_(Name::from_string("Nat.succ_le_succ"), vec![]);
        let nat_le_trans = Expr::const_(Name::from_string("Nat.le_trans"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat_const.clone());
        let (bv_id, bv) = b.fresh_local(nat_const.clone());
        let (c_id, c) = b.fresh_local(nat_const.clone());
        let hab_type = nat_le_tc(a.clone(), bv.clone());
        let (hab_id, hab) = b.fresh_local(hab_type.clone());
        let hbc_type = nat_lt_tc(bv.clone(), c.clone());
        let (hbc_id, hbc) = b.fresh_local(hbc_type.clone());

        // Type: ∀ a b c, LE.le a b → LT.lt b c → LT.lt a c
        let ty = {
            let concl = nat_lt_tc(a.clone(), c.clone());
            let e = b.mk_pi(hbc_id, BinderInfo::Default, hbc_type.clone(), concl);
            let e = b.mk_pi(hab_id, BinderInfo::Default, hab_type.clone(), e);
            let e = b.mk_pi(c_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // Value: fun a b c hab hbc =>
        //   @Nat.le_trans (Nat.succ a) (Nat.succ b) c (@Nat.succ_le_succ a b hab) hbc
        let value = {
            let succ_a = Expr::app(nat_succ.clone(), a.clone());
            let succ_b = Expr::app(nat_succ.clone(), bv.clone());
            // @Nat.succ_le_succ a b hab : Nat.le (Nat.succ a) (Nat.succ b)
            let succ_le = Expr::apps(nat_succ_le_succ, [a.clone(), bv.clone(), hab.clone()]);
            let body = Expr::apps(
                nat_le_trans,
                [succ_a, succ_b, c.clone(), succ_le, hbc.clone()],
            );
            let e = b.mk_lam(hbc_id, BinderInfo::Default, hbc_type, body);
            let e = b.mk_lam(hab_id, BinderInfo::Default, hab_type, e);
            let e = b.mk_lam(c_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_lam(bv_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
