// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nat successor ordering lemmas, trichotomy, and decidable instances
//!
//! Split from order_lemmas.rs (#307). Contains:
//! - Successor base lemmas (zero_lt_succ, not_succ_lt_zero, lt_succ_self)
//! - Successor comparison lemmas (lt_succ_iff, succ_lt_succ, succ_le_succ, etc.)
//! - Trichotomy (lt_trichotomy)
//! - Decidable ordering instances (instDecidableNatLt, instDecidableNatLe)
//!
//! MinMax lemmas are in order_lemmas_minmax.rs.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::order::{nat_le_tc, nat_lt_tc};
use crate::env::{
    Declaration, EnvError, Environment, KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize base successor ordering lemmas for Nat
    ///
    /// Adds: Nat.zero_lt_succ, Nat.not_succ_lt_zero, Nat.lt_succ_self
    pub(crate) fn init_nat_succ_base(&mut self) -> Result<(), EnvError> {
        if self.nat_succ_base_init {
            return Ok(());
        }
        self.init_nat()?;
        self.init_lt()?;
        self.init_true_false()?;

        // #3599: Promote successor base lemmas from Axiom to constructive
        // Theorem. These theorem registrations must run before the legacy
        // add_nat_* helpers so the checked forms win.
        self.init_nat_top_level_ordering()?;
        self.register_nat_not_succ_lt_zero_theorem()?;
        self.register_nat_lt_succ_self_theorem()?;

        self.add_nat_zero_lt_succ()?;
        self.add_nat_not_succ_lt_zero()?;
        self.add_nat_lt_succ_self()?;

        self.nat_succ_base_init = true;
        Ok(())
    }

    fn add_nat_zero_lt_succ(&mut self) -> Result<(), EnvError> {
        // #3599: `Nat.zero_lt_succ` is now registered as a constructive
        // `Declaration::Theorem` by `init_nat_top_level_ordering`. If the
        // Theorem is already present, skip the legacy Axiom registration
        // so the Theorem form wins.
        if self
            .get_const(&Name::from_string("Nat.zero_lt_succ"))
            .is_some()
        {
            return Ok(());
        }
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero_const = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let succ_const = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat_const.clone());
        let body = nat_lt_tc(zero_const, Expr::app(succ_const, n));
        let e = b.mk_pi(n_id, BinderInfo::Default, nat_const, body);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.zero_lt_succ"),
            level_params: vec![],
            type_: b.finish(e),
        })
    }

    fn add_nat_not_succ_lt_zero(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("Nat.not_succ_lt_zero"))
            .is_some()
        {
            return Ok(());
        }
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero_const = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let succ_const = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let false_const = Expr::const_(Name::from_string("False"), vec![]);
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat_const.clone());
        let succ_n_lt_zero = nat_lt_tc(Expr::app(succ_const, n), zero_const);
        let (h_id, _h) = b.fresh_local(succ_n_lt_zero.clone());
        let e = b.mk_pi(h_id, BinderInfo::Default, succ_n_lt_zero, false_const);
        let e = b.mk_pi(n_id, BinderInfo::Default, nat_const, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.not_succ_lt_zero"),
            level_params: vec![],
            type_: b.finish(e),
        })
    }

    fn add_nat_lt_succ_self(&mut self) -> Result<(), EnvError> {
        // #3599 follow-up: `Nat.lt_succ_self` is now registered as a
        // constructive `Declaration::Theorem` by
        // `register_nat_lt_succ_self_theorem`. If the Theorem is already
        // present, skip the legacy Axiom registration so the Theorem wins.
        if self
            .get_const(&Name::from_string("Nat.lt_succ_self"))
            .is_some()
        {
            return Ok(());
        }
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let succ_const = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat_const.clone());
        let body = nat_lt_tc(n.clone(), Expr::app(succ_const, n));
        let e = b.mk_pi(n_id, BinderInfo::Default, nat_const, body);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.lt_succ_self"),
            level_params: vec![],
            type_: b.finish(e),
        })
    }

    /// Register `Nat.lt_succ_self : forall (n : Nat), LT.lt @Nat instLTNat n (Nat.succ n)`
    /// as a constructive `Declaration::Theorem` (#3599 follow-up).
    ///
    /// `Nat.lt` is a reducible `Declaration::Definition`
    /// `Nat.lt n m := Nat.le (Nat.succ n) m`, and `instLTNat` is a reducible
    /// wrapper, so the typeclass goal `LT.lt @Nat instLTNat n (Nat.succ n)`
    /// reduces definitionally to `Nat.le (Nat.succ n) (Nat.succ n)`.
    ///
    /// Proof term: `fun (n : Nat) => @Nat.le.refl (Nat.succ n)`. The witness
    /// `Nat.le.refl (Nat.succ n) : Nat.le (Nat.succ n) (Nat.succ n)` therefore
    /// has the stated type up to definitional equality.
    ///
    /// Axiom closure: empty — `Nat.le.refl` is the canonical constructor of
    /// the inductive `Nat.le` (a kernel primitive, not a `Declaration::Axiom`).
    fn register_nat_lt_succ_self_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.lt_succ_self");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat_const.clone());

        // Type: forall (n : Nat), LT.lt @Nat instLTNat n (Nat.succ n)
        let ty = {
            let succ_n = Expr::app(nat_succ.clone(), n.clone());
            let body = nat_lt_tc(n.clone(), succ_n);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), body);
            b.finish(e)
        };

        // Value: fun (n : Nat) => @Nat.le.refl (Nat.succ n)
        // Reduces against the goal `Nat.le (Nat.succ n) (Nat.succ n)`.
        let value = {
            let succ_n = Expr::app(nat_succ.clone(), n.clone());
            let body = Expr::app(nat_le_refl, succ_n);
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    pub(crate) fn has_nat_succ_base(&self) -> bool {
        self.nat_succ_base_init
    }

    /// Initialize successor comparison lemmas for Nat
    ///
    /// Adds: lt_succ_iff, succ_lt_succ, lt_of_succ_lt_succ,
    ///       succ_le_succ, le_of_succ_le_succ
    pub(crate) fn init_nat_succ_lt(&mut self) -> Result<(), EnvError> {
        if self.nat_succ_lt_init {
            return Ok(());
        }
        self.init_nat()?;
        self.init_le()?;
        self.init_lt()?;
        self.init_iff()?;

        // #3599: Promote Nat.succ_lt_succ and Nat.succ_le_succ from Axiom to
        // constructive Theorem. init_nat_top_level_ordering must run before
        // add_nat_* so the Theorems are registered first; the add_nat_*
        // helpers become no-ops when the names are already present.
        self.init_nat_top_level_ordering()?;

        // #3599 follow-up: `Nat.le_of_succ_le_succ` must be registered as a
        // constructive Theorem before `Nat.lt_of_succ_lt_succ`, which is
        // proved from it. Both then win over the legacy add_nat_* axioms.
        self.register_nat_le_of_succ_le_succ_theorem()?;
        self.register_nat_lt_of_succ_lt_succ_theorem()?;

        self.add_nat_lt_succ_iff()?;
        self.add_nat_succ_lt_succ()?;
        self.add_nat_lt_of_succ_lt_succ()?;
        self.add_nat_succ_le_succ()?;
        self.add_nat_le_of_succ_le_succ()?;

        self.nat_succ_lt_init = true;
        Ok(())
    }

    fn add_nat_lt_succ_iff(&mut self) -> Result<(), EnvError> {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let iff = Expr::const_(Name::from_string("Iff"), vec![]);
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());
        let (m_id, m) = b.fresh_local(nat.clone());
        let lt_n_sm = Expr::app(Expr::app(lt, n.clone()), Expr::app(succ, m.clone()));
        let le_n_m = Expr::app(Expr::app(le, n), m);
        let body = Expr::app(Expr::app(iff, lt_n_sm), le_n_m);
        let e = b.mk_pi(m_id, BinderInfo::Default, nat.clone(), body);
        let e = b.mk_pi(n_id, BinderInfo::Default, nat, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.lt_succ_iff"),
            level_params: vec![],
            type_: b.finish(e),
        })
    }

    fn add_nat_succ_lt_succ(&mut self) -> Result<(), EnvError> {
        // #3599: `Nat.succ_lt_succ` is now registered as a constructive
        // `Declaration::Theorem` by `init_nat_top_level_ordering`. If the
        // Theorem is already present, skip the legacy Axiom registration
        // so the Theorem form wins.
        if self
            .get_const(&Name::from_string("Nat.succ_lt_succ"))
            .is_some()
        {
            return Ok(());
        }
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());
        let (m_id, m) = b.fresh_local(nat.clone());
        let lt_n_m = Expr::app(Expr::app(lt.clone(), n.clone()), m.clone());
        let (h_id, _h) = b.fresh_local(lt_n_m.clone());
        let body = Expr::app(
            Expr::app(lt, Expr::app(succ.clone(), n)),
            Expr::app(succ, m),
        );
        let e = b.mk_pi(h_id, BinderInfo::Default, lt_n_m, body);
        let e = b.mk_pi(m_id, BinderInfo::Default, nat.clone(), e);
        let e = b.mk_pi(n_id, BinderInfo::Default, nat, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.succ_lt_succ"),
            level_params: vec![],
            type_: b.finish(e),
        })
    }

    fn add_nat_lt_of_succ_lt_succ(&mut self) -> Result<(), EnvError> {
        // #3599 follow-up: `Nat.lt_of_succ_lt_succ` is now registered as a
        // constructive `Declaration::Theorem` by
        // `register_nat_lt_of_succ_lt_succ_theorem`. If the Theorem is already
        // present, skip the legacy Axiom registration so the Theorem wins.
        if self
            .get_const(&Name::from_string("Nat.lt_of_succ_lt_succ"))
            .is_some()
        {
            return Ok(());
        }
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());
        let (m_id, m) = b.fresh_local(nat.clone());
        let hyp = Expr::app(
            Expr::app(lt.clone(), Expr::app(succ.clone(), n.clone())),
            Expr::app(succ, m.clone()),
        );
        let (h_id, _h) = b.fresh_local(hyp.clone());
        let body = Expr::app(Expr::app(lt, n), m);
        let e = b.mk_pi(h_id, BinderInfo::Default, hyp, body);
        let e = b.mk_pi(m_id, BinderInfo::Default, nat.clone(), e);
        let e = b.mk_pi(n_id, BinderInfo::Default, nat, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.lt_of_succ_lt_succ"),
            level_params: vec![],
            type_: b.finish(e),
        })
    }

    /// Register `Nat.lt_of_succ_lt_succ : forall (n m : Nat), Nat.lt (Nat.succ n) (Nat.succ m) -> Nat.lt n m`
    /// (raw `Nat.lt` form, matching the legacy Axiom signature) as a
    /// constructive `Declaration::Theorem` (#3599 follow-up).
    ///
    /// `Nat.lt` is a reducible `Declaration::Definition`
    /// `Nat.lt a b := Nat.le (Nat.succ a) b`. So the hypothesis
    /// `Nat.lt (Nat.succ n) (Nat.succ m)` reduces to
    /// `Nat.le (Nat.succ (Nat.succ n)) (Nat.succ m)`, and the conclusion
    /// `Nat.lt n m` reduces to `Nat.le (Nat.succ n) m`.
    ///
    /// `Nat.le_of_succ_le_succ : forall (a b : Nat), Nat.le (Nat.succ a) (Nat.succ b) -> Nat.le a b`
    /// (an already-registered constructive Theorem proved from `Nat.le.rec`)
    /// applied at `a = Nat.succ n`, `b = m` yields exactly
    /// `Nat.le (Nat.succ (Nat.succ n)) (Nat.succ m) -> Nat.le (Nat.succ n) m`.
    ///
    /// Proof term: `fun n m h => @Nat.le_of_succ_le_succ (Nat.succ n) m h`.
    ///
    /// Axiom closure: empty — `Nat.le_of_succ_le_succ` has an empty domain
    /// axiom closure (proved via `Nat.le.rec` / `Nat.casesOn` / `Nat.noConfusion`,
    /// all kernel primitives), so this theorem inherits an empty closure.
    fn register_nat_lt_of_succ_lt_succ_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.lt_of_succ_lt_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let le_of_succ_le_succ = Expr::const_(Name::from_string("Nat.le_of_succ_le_succ"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());
        let (m_id, m) = b.fresh_local(nat.clone());
        let hyp = Expr::apps(
            lt.clone(),
            [
                Expr::app(succ.clone(), n.clone()),
                Expr::app(succ.clone(), m.clone()),
            ],
        );
        let (h_id, h) = b.fresh_local(hyp.clone());

        // Type: forall (n m : Nat), Nat.lt (Nat.succ n) (Nat.succ m) -> Nat.lt n m
        let ty = {
            let concl = Expr::apps(lt, [n.clone(), m.clone()]);
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp.clone(), concl);
            let e = b.mk_pi(m_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        // Value: fun n m h => @Nat.le_of_succ_le_succ (Nat.succ n) m h
        // Hypothesis `Nat.lt (Nat.succ n) (Nat.succ m)` reduces to
        // `Nat.le (Nat.succ (Nat.succ n)) (Nat.succ m)`, which is the
        // `Nat.le (Nat.succ a) (Nat.succ b)` argument at a = Nat.succ n, b = m.
        // The result `Nat.le (Nat.succ n) m` reduces to the goal `Nat.lt n m`.
        let value = {
            let succ_n = Expr::app(succ.clone(), n.clone());
            let body = Expr::apps(le_of_succ_le_succ, [succ_n, m.clone(), h.clone()]);
            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
            let e = b.mk_lam(m_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    fn add_nat_succ_le_succ(&mut self) -> Result<(), EnvError> {
        // #3599: `Nat.succ_le_succ` is now registered as a constructive
        // `Declaration::Theorem` by `init_nat_top_level_ordering`. If the
        // Theorem is already present, skip the legacy Axiom registration
        // so the Theorem form wins.
        if self
            .get_const(&Name::from_string("Nat.succ_le_succ"))
            .is_some()
        {
            return Ok(());
        }
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());
        let (m_id, m) = b.fresh_local(nat.clone());
        let le_n_m = Expr::app(Expr::app(le.clone(), n.clone()), m.clone());
        let (h_id, _h) = b.fresh_local(le_n_m.clone());
        let body = Expr::app(
            Expr::app(le, Expr::app(succ.clone(), n)),
            Expr::app(succ, m),
        );
        let e = b.mk_pi(h_id, BinderInfo::Default, le_n_m, body);
        let e = b.mk_pi(m_id, BinderInfo::Default, nat.clone(), e);
        let e = b.mk_pi(n_id, BinderInfo::Default, nat, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.succ_le_succ"),
            level_params: vec![],
            type_: b.finish(e),
        })
    }

    fn add_nat_le_of_succ_le_succ(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("Nat.le_of_succ_le_succ"))
            .is_some()
        {
            return Ok(());
        }
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());
        let (m_id, m) = b.fresh_local(nat.clone());
        let hyp = Expr::app(
            Expr::app(le.clone(), Expr::app(succ.clone(), n.clone())),
            Expr::app(succ, m.clone()),
        );
        let (h_id, _h) = b.fresh_local(hyp.clone());
        let body = Expr::app(Expr::app(le, n), m);
        let e = b.mk_pi(h_id, BinderInfo::Default, hyp, body);
        let e = b.mk_pi(m_id, BinderInfo::Default, nat.clone(), e);
        let e = b.mk_pi(n_id, BinderInfo::Default, nat, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.le_of_succ_le_succ"),
            level_params: vec![],
            type_: b.finish(e),
        })
    }

    pub(crate) fn has_nat_succ_lt(&self) -> bool {
        self.nat_succ_lt_init
    }

    /// Initialize Nat.lt_trichotomy lemma
    pub(crate) fn init_nat_lt_trichotomy(&mut self) -> Result<(), EnvError> {
        if self.nat_lt_trichotomy_init {
            return Ok(());
        }
        self.init_nat()?;
        self.init_lt()?;
        self.init_eq()?;
        self.init_classical()?;

        // Prefer the constructive `Declaration::Theorem` form of
        // `Nat.lt_trichotomy` (proved via `Nat.le_or_lt` + `Nat.lt_or_eq_of_le`
        // in `nat_totality_proof.rs`). Idempotent; the legacy axiom below is
        // guarded so it becomes a no-op once the Theorem is present.
        self.init_nat_totality_proofs()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let or = Expr::const_(Name::from_string("Or"), vec![]);
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat.clone());
        let (b_id, bv) = b.fresh_local(nat.clone());
        let lt_a_b = Expr::app(Expr::app(lt.clone(), a.clone()), bv.clone());
        let eq_a_b = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    nat.clone(),
                ),
                a.clone(),
            ),
            bv.clone(),
        );
        let lt_b_a = Expr::app(Expr::app(lt, bv), a);
        let body = Expr::app(
            Expr::app(or.clone(), lt_a_b),
            Expr::app(Expr::app(or, eq_a_b), lt_b_a),
        );
        let e = b.mk_pi(b_id, BinderInfo::Default, nat.clone(), body);
        let e = b.mk_pi(a_id, BinderInfo::Default, nat, e);
        // Guarded: skip if the constructive Theorem form is already registered.
        if self
            .get_const(&Name::from_string("Nat.lt_trichotomy"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.lt_trichotomy"),
                level_params: vec![],
                type_: b.finish(e),
            })?;
        }
        self.nat_lt_trichotomy_init = true;
        Ok(())
    }

    pub(crate) fn has_nat_lt_trichotomy(&self) -> bool {
        self.nat_lt_trichotomy_init
    }

    /// Initialize Decidable instances for Nat.lt and Nat.le.
    ///
    /// `instDecidableNatLe` / `instDecidableNatLt` are real, kernel-checked
    /// `Declaration::Definition`s — NO `Declaration::Axiom` (an axiom-backed
    /// decidability instance is a trust regression). Their bodies are the
    /// axiom-free `Nat.decLe` / `Nat.decLt` decision procedures
    /// (`algebra_nat_dec_le_proof.rs`), dispatched on `Nat.ble` via `Bool.rec` and
    /// witnessed by the `Nat.ble`↔`Nat.le` bridge lemmas.
    ///
    /// The instance type is the typeclass form `(a b : Nat) → Decidable
    /// (@LE.le Nat instLENat a b)` (resp. `LT.lt`), matching the goal shape the
    /// elaborator's `resolve_decidable` asks for. `@LE.le Nat instLENat a b`
    /// reducibly unfolds to `Nat.le a b` (the `instLENat` projection), so the
    /// `Nat.decLe : (a b) → Decidable (Nat.le a b)` value is def-eq to the
    /// declared type and the kernel accepts the `Definition`.
    ///
    /// Also registers the foundational `instLENat` / `instLTNat` under the
    /// `LE` / `LT` classes and the two decidability instances under `Decidable`,
    /// so `1 ≤ 2` / `1 < 2` resolve their `[LE Nat]` / `[Decidable …]` arguments
    /// instead of leaving an unresolved metavariable.
    pub(crate) fn init_nat_decidable_ord(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget
        // 2026-07-04): Clean's `Nat.decLe`/`Nat.decLt` values are Nat.rec
        // dispatcher bridges — genuine v4.31 uses `Nat.ble`-based `dite`
        // bodies, and `Decidable` is Type-valued (no proof irrelevance) so
        // conversion must genuinely unfold them (`Rat.instEncodable`'s
        // `Subtype.encodable` chain rejects against the stub). Suppressed in
        // import mode with their `instDecidableNat{Lt,Le}` wrappers so the
        // genuine olean definitions import (caller-graph closure + kernel
        // error oracle verified: nothing else in the import prelude
        // references these names).
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.nat_decidable_ord_init {
            return Ok(());
        }
        self.init_nat()?;
        self.init_le()?;
        self.init_lt()?;
        self.init_decidable()?;
        // The axiom-free decision procedures backing the two instances.
        self.register_nat_dec_le_lt_proof()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let decidable = Expr::const_(Name::from_string("Decidable"), vec![]);

        // instDecidableNatLt : (a b : Nat) → Decidable (@LT.lt Nat instLTNat a b)
        //   := Nat.decLt
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat.clone());
        let (bv_id, bv) = b.fresh_local(nat.clone());
        let body = Expr::app(decidable.clone(), nat_lt_tc(a, bv));
        let e = b.mk_pi(bv_id, BinderInfo::Default, nat.clone(), body);
        let lt_ty = b.finish(b.mk_pi(a_id, BinderInfo::Default, nat.clone(), e));
        self.add_decl(Declaration::Definition {
            name: Name::from_string("instDecidableNatLt"),
            level_params: vec![],
            type_: lt_ty.clone(),
            value: Expr::const_(Name::from_string("Nat.decLt"), vec![]),
            is_reducible: true,
        })?;

        // instDecidableNatLe : (a b : Nat) → Decidable (@LE.le Nat instLENat a b)
        //   := Nat.decLe
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat.clone());
        let (bv_id, bv) = b.fresh_local(nat.clone());
        let body = Expr::app(decidable, nat_le_tc(a, bv));
        let e = b.mk_pi(bv_id, BinderInfo::Default, nat.clone(), body);
        let le_ty = b.finish(b.mk_pi(a_id, BinderInfo::Default, nat.clone(), e));
        self.add_decl(Declaration::Definition {
            name: Name::from_string("instDecidableNatLe"),
            level_params: vec![],
            type_: le_ty.clone(),
            value: Expr::const_(Name::from_string("Nat.decLe"), vec![]),
            is_reducible: true,
        })?;

        // Register the foundational `LE Nat` / `LT Nat` instances so the
        // elaborator can resolve the `[inst : LE Nat]` / `[inst : LT Nat]`
        // argument of `LE.le` / `LT.lt` (previously left as a metavariable, so
        // `1 ≤ 2` never even produced a `Decidable` goal). `instLENat` /
        // `instLTNat` are reducible `Definition`s already registered by
        // `init_le` / `init_lt`.
        let inst_le_nat_ty = self
            .get_const(&Name::from_string("instLENat"))
            .map(|c| c.type_.clone());
        if let Some(ty) = inst_le_nat_ty {
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string("instLENat"),
                class_name: Name::from_string("LE"),
                priority: DEFAULT_INSTANCE_PRIORITY,
                type_: Some(ty),
                value: Some(Expr::const_(Name::from_string("instLENat"), vec![])),
            });
        }
        let inst_lt_nat_ty = self
            .get_const(&Name::from_string("instLTNat"))
            .map(|c| c.type_.clone());
        if let Some(ty) = inst_lt_nat_ty {
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string("instLTNat"),
                class_name: Name::from_string("LT"),
                priority: DEFAULT_INSTANCE_PRIORITY,
                type_: Some(ty),
                value: Some(Expr::const_(Name::from_string("instLTNat"), vec![])),
            });
        }

        // Register the two decision procedures under the `Decidable` class so
        // `if (a ≤ b)` / `if (a < b)` / `decide` resolve them. Stripping the two
        // explicit `Nat` binders leaves `Decidable (@LE.le Nat instLENat ?a ?b)`
        // (resp. `LT.lt`) — exactly the goal `resolve_decidable` constructs.
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instDecidableNatLe"),
            class_name: Name::from_string("Decidable"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: Some(le_ty),
            value: Some(Expr::const_(
                Name::from_string("instDecidableNatLe"),
                vec![],
            )),
        });
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instDecidableNatLt"),
            class_name: Name::from_string("Decidable"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: Some(lt_ty),
            value: Some(Expr::const_(
                Name::from_string("instDecidableNatLt"),
                vec![],
            )),
        });

        self.nat_decidable_ord_init = true;
        Ok(())
    }

    pub(crate) fn has_nat_decidable_ord(&self) -> bool {
        self.nat_decidable_ord_init
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    // #3599 follow-up: `Nat.lt_succ_self` and `Nat.lt_of_succ_lt_succ`
    // demoted from `Declaration::Axiom` to constructive `Declaration::Theorem`.
    const DEMOTED: &[&str] = &["Nat.lt_succ_self", "Nat.lt_of_succ_lt_succ"];

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_nat_succ_base()
            .expect("init_nat_succ_base should succeed");
        env.init_nat_succ_lt()
            .expect("init_nat_succ_lt should succeed");
        env
    }

    #[test]
    fn test_succ_lt_demotions_are_theorems_not_axioms() {
        let env = make_env();
        for target in DEMOTED {
            let info = env
                .get_const(&Name::from_string(target))
                .unwrap_or_else(|| panic!("{target} must be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{target} must be a Theorem, got {:?}",
                info.kind
            );
            assert!(
                info.value.is_some(),
                "{target} must carry a proof term (not a bare axiom)"
            );
        }
    }

    #[test]
    fn test_succ_lt_demotions_type_check() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for target in DEMOTED {
            let e = Expr::const_(Name::from_string(target), vec![]);
            let _ = tc
                .infer_type(&e)
                .unwrap_or_else(|err| panic!("{target} should type-check: {err:?}"));
        }
    }

    #[test]
    fn test_succ_lt_demotions_axiom_closures_empty() {
        let env = make_env();
        for target in DEMOTED {
            let deps = env
                .axiom_deps(&Name::from_string(target))
                .unwrap_or_else(|| panic!("axiom_deps must succeed for {target}"));
            let dep_names: std::collections::HashSet<String> =
                deps.iter().map(|n| n.to_string()).collect();
            assert!(
                !dep_names.contains("sorry") && !dep_names.contains("sorryAx"),
                "{target} must not depend on sorry/sorryAx; closure = {dep_names:?}"
            );
            assert!(
                dep_names.is_empty(),
                "{target} must have empty domain axiom closure; got {dep_names:?}"
            );
        }
    }

    #[test]
    fn test_succ_lt_demotions_are_constructive() {
        let env = make_env();
        for target in DEMOTED {
            assert_eq!(
                env.proof_quality(&Name::from_string(target))
                    .unwrap_or_else(|| panic!("proof quality should compute for {target}")),
                ProofQuality::Constructive,
                "{target} must be Constructive"
            );
        }
    }

    #[test]
    fn test_lt_succ_self_uses_le_refl() {
        // The proof term must reference `Nat.le.refl`, not be a bare axiom ref.
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("Nat.lt_succ_self"))
            .expect("Nat.lt_succ_self must be registered");
        let value = info
            .value
            .as_ref()
            .expect("Nat.lt_succ_self must carry a proof term");
        let text = format!("{value}");
        assert!(
            text.contains("Nat.le.refl"),
            "Nat.lt_succ_self proof must reference Nat.le.refl; got term = {text}"
        );
    }

    #[test]
    fn test_lt_of_succ_lt_succ_uses_le_of_succ_le_succ() {
        // The proof term must reference the constructive helper, not an axiom.
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("Nat.lt_of_succ_lt_succ"))
            .expect("Nat.lt_of_succ_lt_succ must be registered");
        let value = info
            .value
            .as_ref()
            .expect("Nat.lt_of_succ_lt_succ must carry a proof term");
        let text = format!("{value}");
        assert!(
            text.contains("Nat.le_of_succ_le_succ"),
            "Nat.lt_of_succ_lt_succ proof must reference Nat.le_of_succ_le_succ; got term = {text}"
        );
    }
}
