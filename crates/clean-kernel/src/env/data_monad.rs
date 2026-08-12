// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Monad and IO type initialization for Environment
//!
//! This module contains:
//! - IO monad type
//! - StateT monad transformer
//! - StateM monad
//! - Id monad
//! - Monad type classes (Functor, Pure, Bind, Monad)

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
impl Environment {
    /// Initialize IO monad type
    ///
    /// IO is Lean's built-in monad for effects. It's opaque - we model it as:
    /// def IO (α : Type) : Type := EIO Error α
    /// where EIO is the primitive exception monad
    ///
    /// For FATE-X compatibility, we just need the type signature:
    /// IO : Type → Type
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.io_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_io(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget
        // 2026-07-04): this Clean-native stub cluster is NOT v4.31-faithful —
        // the StateT member axioms are MISSING the `[Monad m]` instance binder
        // (arity drift: the incremental lane's CHECKED axiom upgrade fails
        // closed with UpgradeTypeMismatch), and `Id.mk`/`IO.pure`/`IO.bind`/
        // `StateM.pure` are phantom constants absent upstream (unhealable by
        // the axiom upgrade). In import mode skip the cluster so the genuine
        // olean declarations import through the checked path (caller-graph
        // closure verified: nothing else in the import prelude references
        // these names). The default proof-execution lane is byte-identical.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.io_init {
            return Ok(());
        }

        // IO : Type → Type
        let type_0 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
        let io_type = Expr::pi(BinderInfo::Default, type_0.clone(), type_0.clone());

        // Add IO as an opaque constant (axiom)
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("IO"),
            level_params: vec![],
            type_: io_type,
        })?;

        // Add IO.pure : {α : Type} → α → IO α
        let io_const = Expr::const_(Name::from_string("IO"), vec![]);
        let io_pure_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_0.clone());
            let (val_id, _val) = b.fresh_local(alpha.clone());
            let r = Expr::app(io_const.clone(), alpha.clone());
            let r = b.mk_pi(val_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_0.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("IO.pure"),
            level_params: vec![],
            type_: io_pure_type,
        })?;

        // Add IO.bind : {α β : Type} → IO α → (α → IO β) → IO β
        let io_bind_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_0.clone());
            let (beta_id, beta) = b.fresh_local(type_0.clone());
            let io_alpha = Expr::app(io_const.clone(), alpha.clone());
            let io_beta = Expr::app(io_const.clone(), beta.clone());
            let (ma_id, _ma) = b.fresh_local(io_alpha.clone());
            let f_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _x) = c.fresh_local(alpha.clone());
                let r = io_beta.clone();
                let r = c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };
            let (f_id, _f) = b.fresh_local(f_ty.clone());
            let r = io_beta;
            let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
            let r = b.mk_pi(ma_id, BinderInfo::Default, io_alpha, r);
            let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_0.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_0.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("IO.bind"),
            level_params: vec![],
            type_: io_bind_type,
        })?;

        self.io_init = true;
        Ok(())
    }

    /// Check if IO monad has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_io` has completed successfully
    /// ENSURES: Pure - no side effects
    pub(crate) fn has_io(&self) -> bool {
        self.io_init
    }

    /// Initialize StateT monad transformer
    ///
    /// StateT : Type → (Type → Type) → Type → Type
    /// def StateT (σ : Type) (m : Type → Type) (α : Type) : Type := σ → m (α × σ)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.state_t_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_state_t(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget
        // 2026-07-04): this Clean-native stub cluster is NOT v4.31-faithful —
        // the StateT member axioms are MISSING the `[Monad m]` instance binder
        // (arity drift: the incremental lane's CHECKED axiom upgrade fails
        // closed with UpgradeTypeMismatch), and `Id.mk`/`IO.pure`/`IO.bind`/
        // `StateM.pure` are phantom constants absent upstream (unhealable by
        // the axiom upgrade). In import mode skip the cluster so the genuine
        // olean declarations import through the checked path (caller-graph
        // closure verified: nothing else in the import prelude references
        // these names). The default proof-execution lane is byte-identical.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.state_t_init {
            return Ok(());
        }

        // StateT.set/get return types reference PUnit (via StateT σ m PUnit),
        // and StateT.run references Prod (via m (Prod α σ)).
        // Both must be initialized before adding StateT declarations.
        self.init_punit()?;
        self.init_prod()?;

        // Lean 4: StateT.{u, v} (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v)
        let u_name = Name::from_string("u");
        let v_name = Name::from_string("v");
        let u_level = Level::param(u_name.clone());
        let v_level = Level::param(v_name.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let type_v = Expr::from_kind(ExprKind::Sort(Level::succ(v_level.clone())));
        // Type (max u v) = Sort(max(u+1, v+1))
        let type_max_uv = Expr::from_kind(ExprKind::Sort(Level::max(
            Level::succ(u_level.clone()),
            Level::succ(v_level.clone()),
        )));

        // StateT : Sort (u+1) → (Sort (u+1) → Sort (v+1)) → Sort (u+1) → Sort (max(u+1, v+1))
        let state_t_type = Expr::pi(
            BinderInfo::Default,
            type_u.clone(), // σ : Type u
            Expr::pi(
                BinderInfo::Default,
                Expr::pi(BinderInfo::Default, type_u.clone(), type_v.clone()), // m : Type u → Type v
                Expr::pi(
                    BinderInfo::Default,
                    type_u.clone(), // α : Type u
                    type_max_uv,    // Type (max u v)
                ),
            ),
        );

        // StateT value: fun (σ : Type u) (m : Type u → Type v) (α : Type u) => σ → m (Prod α σ)
        // In Lean 4, StateT is a definition (not opaque), so it must unfold during whnf
        // to expose the Pi structure needed for lambda elaboration (#3395).
        //
        // De Bruijn indices inside the innermost lambda body (under 3 lambdas):
        //   BVar(0) = α, BVar(1) = m, BVar(2) = σ
        // Inside the Pi codomain (under 3 lambdas + 1 Pi binder):
        //   BVar(0) = Pi-bound var, BVar(1) = α, BVar(2) = m, BVar(3) = σ
        let prod_const = Expr::const_(
            Name::from_string("Prod"),
            vec![u_level.clone(), u_level.clone()],
        );
        // Prod α σ (under 3 lambdas): App(App(Prod.{u,u}, BVar(0)), BVar(2))
        let prod_alpha_sigma = Expr::app(Expr::app(prod_const, Expr::bvar(0)), Expr::bvar(2));
        // m (Prod α σ) (under 3 lambdas): App(BVar(1), prod_alpha_sigma)
        let _m_prod = Expr::app(Expr::bvar(1), prod_alpha_sigma);
        // σ → m (Prod α σ) (under 3 lambdas): Pi(Default, BVar(2), m_prod_shifted)
        // Inside the Pi codomain, indices shift by 1:
        //   BVar(1) = α, BVar(2) = m, BVar(3) = σ
        let prod_alpha_sigma_shifted = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Prod"),
                    vec![u_level.clone(), u_level.clone()],
                ),
                Expr::bvar(1),
            ),
            Expr::bvar(3),
        );
        let m_prod_shifted = Expr::app(Expr::bvar(2), prod_alpha_sigma_shifted);
        let body = Expr::pi(BinderInfo::Default, Expr::bvar(2), m_prod_shifted);
        // Wrap in 3 lambdas
        let state_t_val = Expr::lam(
            BinderInfo::Default,
            type_u.clone(), // σ : Type u
            Expr::lam(
                BinderInfo::Default,
                Expr::pi(BinderInfo::Default, type_u.clone(), type_v.clone()), // m : Type u → Type v
                Expr::lam(
                    BinderInfo::Default,
                    type_u.clone(), // α : Type u
                    body,
                ),
            ),
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("StateT"),
            level_params: vec![u_name.clone(), v_name.clone()],
            type_: state_t_type,
            value: state_t_val,
            is_reducible: true,
        })?;

        // StateT.pure : {σ : Type u} → {m : Type u → Type v} → {α : Type u} → α → StateT σ m α
        let state_t_const = Expr::const_(
            Name::from_string("StateT"),
            vec![u_level.clone(), v_level.clone()],
        );

        let state_t_pure_type = {
            let mut b = EnvDeclBuilder::new();
            let (sigma_id, sigma) = b.fresh_local(type_u.clone());
            let m_ty = Expr::pi(BinderInfo::Default, type_u.clone(), type_v.clone());
            let (m_id, m) = b.fresh_local(m_ty.clone());
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (val_id, _val) = b.fresh_local(alpha.clone());
            let state_t_sigma_m_alpha = Expr::app(
                Expr::app(Expr::app(state_t_const.clone(), sigma), m),
                alpha.clone(),
            );
            let r = state_t_sigma_m_alpha;
            let r = b.mk_pi(val_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Implicit, m_ty, r);
            let r = b.mk_pi(sigma_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("StateT.pure"),
            level_params: vec![u_name.clone(), v_name.clone()],
            type_: state_t_pure_type,
        })?;

        // StateT.set : {σ : Type u} → {m : Type u → Type v} → σ → StateT σ m PUnit
        // Sets the state to a new value.
        // Lean 4: `@[inline] def StateT.set [Monad m] (s : σ) : StateT σ m PUnit`
        let state_t_set_type = {
            let m_ty = Expr::pi(BinderInfo::Default, type_u.clone(), type_v.clone());
            let punit = Expr::const_(
                Name::from_string("PUnit"),
                vec![Level::succ(u_level.clone())],
            ); // PUnit.{succ(u)} : Type u
            let mut b = EnvDeclBuilder::new();
            let (sigma_id, sigma) = b.fresh_local(type_u.clone());
            let (m_id, m) = b.fresh_local(m_ty.clone());
            let (new_state_id, _new_state) = b.fresh_local(sigma.clone());
            // Return type: StateT σ m PUnit
            let st_smp = Expr::app(
                Expr::app(Expr::app(state_t_const.clone(), sigma.clone()), m),
                punit,
            );
            let r = st_smp;
            let r = b.mk_pi(new_state_id, BinderInfo::Default, sigma, r);
            let r = b.mk_pi(m_id, BinderInfo::Implicit, m_ty.clone(), r);
            let r = b.mk_pi(sigma_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("StateT.set"),
            level_params: vec![u_name.clone(), v_name.clone()],
            type_: state_t_set_type,
        })?;

        // StateT.get : {σ : Type u} → {m : Type u → Type v} → StateT σ m σ
        // Lean 4: `@[inline] def StateT.get [Monad m] : StateT σ m σ`
        let state_t_get_type = {
            let m_ty = Expr::pi(BinderInfo::Default, type_u.clone(), type_v.clone());
            let mut b = EnvDeclBuilder::new();
            let (sigma_id, sigma) = b.fresh_local(type_u.clone());
            let (m_id, m) = b.fresh_local(m_ty.clone());
            // Return type: StateT σ m σ
            let st_sms = Expr::app(
                Expr::app(Expr::app(state_t_const.clone(), sigma.clone()), m),
                sigma.clone(),
            );
            let r = st_sms;
            let r = b.mk_pi(m_id, BinderInfo::Implicit, m_ty.clone(), r);
            let r = b.mk_pi(sigma_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("StateT.get"),
            level_params: vec![u_name.clone(), v_name.clone()],
            type_: state_t_get_type,
        })?;

        // StateT.modify : {σ : Type u} → {m : Type u → Type v} → (σ → σ) → StateT σ m PUnit
        // Modifies the state by applying a function.
        // Lean 4: `@[inline] def StateT.modify [Monad m] (f : σ → σ) : StateT σ m PUnit`
        // Returns PUnit like StateT.set — critical for #3418 Unit/PUnit equivalence.
        let state_t_modify_type = {
            let m_ty = Expr::pi(BinderInfo::Default, type_u.clone(), type_v.clone());
            let punit = Expr::const_(
                Name::from_string("PUnit"),
                vec![Level::succ(u_level.clone())],
            );
            let mut b = EnvDeclBuilder::new();
            let (sigma_id, sigma) = b.fresh_local(type_u.clone());
            let (m_id, m) = b.fresh_local(m_ty.clone());
            // f : σ → σ
            let f_ty = Expr::pi(BinderInfo::Default, sigma.clone(), sigma.clone());
            let (f_id, _f) = b.fresh_local(f_ty.clone());
            // Return type: StateT σ m PUnit
            let st_smp = Expr::app(
                Expr::app(Expr::app(state_t_const.clone(), sigma.clone()), m),
                punit,
            );
            let r = st_smp;
            let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
            let r = b.mk_pi(m_id, BinderInfo::Implicit, m_ty.clone(), r);
            let r = b.mk_pi(sigma_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("StateT.modify"),
            level_params: vec![u_name.clone(), v_name.clone()],
            type_: state_t_modify_type,
        })?;

        // StateT.modifyGet : {σ : Type u} → {m : Type u → Type v} → {α : Type u}
        //                  → (σ → α × σ) → StateT σ m α
        // Modifies the state and returns a value.
        // Lean 4: `@[inline] def StateT.modifyGet [Monad m] (f : σ → α × σ) : StateT σ m α`
        let state_t_modify_get_type = {
            let m_ty = Expr::pi(BinderInfo::Default, type_u.clone(), type_v.clone());
            let mut b = EnvDeclBuilder::new();
            let (sigma_id, sigma) = b.fresh_local(type_u.clone());
            let (m_id, m) = b.fresh_local(m_ty.clone());
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            // f : σ → α × σ
            let prod = Expr::const_(
                Name::from_string("Prod"),
                vec![u_level.clone(), u_level.clone()],
            );
            let prod_a_s = Expr::app(Expr::app(prod, alpha.clone()), sigma.clone());
            let f_ty = Expr::pi(BinderInfo::Default, sigma.clone(), prod_a_s);
            let (f_id, _f) = b.fresh_local(f_ty.clone());
            // Return type: StateT σ m α
            let st_sma = Expr::app(
                Expr::app(Expr::app(state_t_const.clone(), sigma.clone()), m),
                alpha.clone(),
            );
            let r = st_sma;
            let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Implicit, m_ty.clone(), r);
            let r = b.mk_pi(sigma_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("StateT.modifyGet"),
            level_params: vec![u_name.clone(), v_name.clone()],
            type_: state_t_modify_get_type,
        })?;

        // StateT.run : {σ : Type u} → {m : Type u → Type v} → {α : Type u} → StateT σ m α → σ → m (α × σ)
        let state_t_run_type = {
            let m_ty = Expr::pi(BinderInfo::Default, type_u.clone(), type_v.clone());
            let mut b = EnvDeclBuilder::new();
            let (sigma_id, sigma) = b.fresh_local(type_u.clone());
            let (m_id, m) = b.fresh_local(m_ty.clone());
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let st_sma = Expr::app(
                Expr::app(Expr::app(state_t_const.clone(), sigma.clone()), m.clone()),
                alpha.clone(),
            );
            let (act_id, _act) = b.fresh_local(st_sma.clone());
            let (s_id, _s) = b.fresh_local(sigma.clone());
            // Prod α σ
            let prod = Expr::const_(
                Name::from_string("Prod"),
                vec![u_level.clone(), u_level.clone()],
            );
            let prod_a_s = Expr::app(Expr::app(prod, alpha.clone()), sigma.clone());
            let m_prod = Expr::app(m, prod_a_s);
            let r = m_prod;
            let r = b.mk_pi(s_id, BinderInfo::Default, sigma, r);
            let r = b.mk_pi(act_id, BinderInfo::Default, st_sma, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Implicit, m_ty, r);
            let r = b.mk_pi(sigma_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        // StateT.run value: `fun {σ} {m} {α} (act : StateT σ m α) (s : σ) => act s`.
        // Since `StateT σ m α` unfolds (reducibly) to `σ → m (α × σ)`, the bound
        // `act` is applicable to `s`, and `act s : m (α × σ)` matches the result
        // type. Making this a Definition (was Axiom) lets the kernel reduce
        // `StateT.run m s` to `m s`, which is what monad-law `rfl` proofs such as
        // `Sem.run_pure` / `Sem.run_bind` rely on. The kernel re-checks this
        // closed term, so it is axiom-free and sound. (Track W)
        let state_t_run_val = {
            let m_ty = Expr::pi(BinderInfo::Default, type_u.clone(), type_v.clone());
            let mut b = EnvDeclBuilder::new();
            let (sigma_id, sigma) = b.fresh_local(type_u.clone());
            let (m_id, m) = b.fresh_local(m_ty.clone());
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let st_sma = Expr::app(
                Expr::app(Expr::app(state_t_const, sigma.clone()), m.clone()),
                alpha.clone(),
            );
            let (act_id, act) = b.fresh_local(st_sma.clone());
            let (s_id, s) = b.fresh_local(sigma.clone());
            // body: act s
            let body = Expr::app(act, s);
            let r = b.mk_lam(s_id, BinderInfo::Default, sigma.clone(), body);
            let r = b.mk_lam(act_id, BinderInfo::Default, st_sma, r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            let r = b.mk_lam(m_id, BinderInfo::Implicit, m_ty, r);
            let r = b.mk_lam(sigma_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("StateT.run"),
            level_params: vec![u_name, v_name],
            type_: state_t_run_type,
            value: state_t_run_val,
            is_reducible: true,
        })?;

        self.state_t_init = true;
        Ok(())
    }

    /// Check if StateT has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_state_t` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_state_t(&self) -> bool {
        self.state_t_init
    }

    /// Initialize StateM type alias
    ///
    /// StateM is a specialized version of StateT with Id monad:
    /// def StateM (σ α : Type) : Type := StateT σ Id α
    /// For simplicity, we model it directly as:
    /// StateM : Type → Type → Type
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.state_m_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_state_m(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget
        // 2026-07-04): this Clean-native stub cluster is NOT v4.31-faithful —
        // the StateT member axioms are MISSING the `[Monad m]` instance binder
        // (arity drift: the incremental lane's CHECKED axiom upgrade fails
        // closed with UpgradeTypeMismatch), and `Id.mk`/`IO.pure`/`IO.bind`/
        // `StateM.pure` are phantom constants absent upstream (unhealable by
        // the axiom upgrade). In import mode skip the cluster so the genuine
        // olean declarations import through the checked path (caller-graph
        // closure verified: nothing else in the import prelude references
        // these names). The default proof-execution lane is byte-identical.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.state_m_init {
            return Ok(());
        }

        // Lean 4: StateM.{u} (σ : Type u) (α : Type u) : Type u
        let u_name = Name::from_string("u");
        let u_level = Level::param(u_name.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));

        let state_m_type = Expr::pi(
            BinderInfo::Default,
            type_u.clone(), // σ : Type u
            Expr::pi(
                BinderInfo::Default,
                type_u.clone(), // α : Type u
                type_u.clone(), // Type u
            ),
        );

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("StateM"),
            level_params: vec![u_name.clone()],
            type_: state_m_type,
        })?;

        // StateM.pure : {σ : Type u} → {α : Type u} → α → StateM σ α
        let state_m_const = Expr::const_(Name::from_string("StateM"), vec![u_level]);

        let state_m_pure_type = {
            let mut b = EnvDeclBuilder::new();
            let (sigma_id, sigma) = b.fresh_local(type_u.clone());
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (val_id, _val) = b.fresh_local(alpha.clone());
            let r = Expr::app(Expr::app(state_m_const.clone(), sigma), alpha.clone());
            let r = b.mk_pi(val_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            let r = b.mk_pi(sigma_id, BinderInfo::Implicit, type_u, r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("StateM.pure"),
            level_params: vec![u_name],
            type_: state_m_pure_type,
        })?;

        self.state_m_init = true;
        Ok(())
    }

    /// Check if StateM has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_state_m` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_state_m(&self) -> bool {
        self.state_m_init
    }

    /// Initialize Id monad (identity monad)
    ///
    /// In Lean 4, Id is the simplest monad - it's just the identity:
    /// ```text
    /// def Id (type : Type u) : Type u := type
    /// @[inline] def Id.run {α : Type u} (x : Id α) : α := x
    /// instance : Monad Id := { pure := fun x => x, bind := fun x f => f x }
    /// ```
    ///
    /// This adds (Brick B22 — Id-monad reduction, `docs/plans/GAP_SWEEP_2026-07-09.md`):
    /// - `Id : Type u → Type u := fun α => α`             (def; `Id α ≡ α`; semireducible)
    /// - `Id.mk : {α : Type u} → α → Id α := fun a => a`  (reducible identity)
    /// - `Id.run : {α : Type u} → Id α → α := fun x => x` (reducible identity)
    ///
    /// These were opaque **axioms** before B22, so a `rfl` value pin over an
    /// Id-monad computation (`Id.run (pure 5) = 5 := rfl`) could not close —
    /// `Id`/`Id.run`/`pure`/`bind` were all definitionally inert (a LOUD_GAP,
    /// do p13/p14; the wrong pin `= 6` was also correctly rejected, so this was
    /// never a soundness hole, just missing reduction). As genuine reducible
    /// definitions they now unfold through ORDINARY kernel delta/beta — no
    /// axiom, no special-casing — exactly as `Id` is a plain reducible alias in
    /// Lean's `Init/Prelude.lean`. The kernel re-checks each closed body, so
    /// the definitions are axiom-free and sound. The `Pure Id`/`Bind Id`
    /// instances that make `pure`/`bind` compute are registered separately by
    /// [`Environment::init_monad_id_insts`] (`data_monad_insts.rs`).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.id_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_id(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget
        // 2026-07-04): this Clean-native stub cluster is NOT v4.31-faithful —
        // the StateT member axioms are MISSING the `[Monad m]` instance binder
        // (arity drift: the incremental lane's CHECKED axiom upgrade fails
        // closed with UpgradeTypeMismatch), and `Id.mk`/`IO.pure`/`IO.bind`/
        // `StateM.pure` are phantom constants absent upstream (unhealable by
        // the axiom upgrade). In import mode skip the cluster so the genuine
        // olean declarations import through the checked path (caller-graph
        // closure verified: nothing else in the import prelude references
        // these names). The default proof-execution lane is byte-identical.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.id_init {
            return Ok(());
        }

        let u = Name::from_string("u");
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone()))));

        // Id : Type u → Type u := fun (α : Type u) => α
        // A definition (Lean: `def Id (type : Type u) : Type u := type`), so
        // `Id α` unfolds to `α` in kernel def-eq — the reduction a `rfl` pin
        // over an Id-monad value relies on. Deliberately **not** `is_reducible`
        // (semireducible, like Lean's un-annotated `Id`): the elaborator's
        // monad-instance inference must keep `Id` FOLDED as a constant head so
        // that `Id.run (pure 5)` resolves `Pure Id` and the materialization
        // pass fires. Were `Id` reducible, unifying the `pure` monad metavar
        // against `Id.run`'s domain `Id α` would eagerly unfold it to
        // `fun a => a`, leaving a lambda-headed `Pure.pure (fun a => a) …` stub
        // the pass cannot materialize. The KERNEL still unfolds `Id` in def-eq
        // regardless of the reducibility hint, so value pins reduce; the hint
        // only governs elaborator transparency.
        let id_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());
        let id_val = Expr::lam(BinderInfo::Default, type_u.clone(), Expr::bvar(0));

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Id"),
            level_params: vec![u.clone()],
            type_: id_type,
            value: id_val,
            is_reducible: false,
        })?;

        let id_const = Expr::const_(Name::from_string("Id"), vec![Level::param(u.clone())]);

        // Id.mk : {α : Type u} → α → Id α := fun {α} (a : α) => a
        // The body `a : α` checks against `Id α` because `Id α ≡ α` (Id is a
        // reducible def unfolded by the kernel's ordinary delta path).
        let id_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (val_id, _val) = b.fresh_local(alpha.clone());
            let r = Expr::app(id_const.clone(), alpha.clone());
            let r = b.mk_pi(val_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        let id_mk_val = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (val_id, val) = b.fresh_local(alpha.clone());
            let r = b.mk_lam(val_id, BinderInfo::Default, alpha.clone(), val);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Id.mk"),
            level_params: vec![u.clone()],
            type_: id_mk_type,
            value: id_mk_val,
            is_reducible: true,
        })?;

        // Id.run : {α : Type u} → Id α → α := fun {α} (x : Id α) => x
        // The extractor is the identity (Lean: `@[inline] def Id.run {α} (x :
        // Id α) : α := x`); `x : Id α ≡ α` matches the `α` result.
        let id_run_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let id_alpha = Expr::app(id_const.clone(), alpha.clone());
            let (x_id, _x) = b.fresh_local(id_alpha.clone());
            let r = alpha.clone();
            let r = b.mk_pi(x_id, BinderInfo::Default, id_alpha, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        let id_run_val = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let id_alpha = Expr::app(id_const.clone(), alpha.clone());
            let (x_id, x) = b.fresh_local(id_alpha.clone());
            let r = b.mk_lam(x_id, BinderInfo::Default, id_alpha, x);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Id.run"),
            level_params: vec![u.clone()],
            type_: id_run_type,
            value: id_run_val,
            is_reducible: true,
        })?;

        self.id_init = true;
        Ok(())
    }

    /// Check if Id monad has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_id` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_id(&self) -> bool {
        self.id_init
    }

    /// Initialize abstract monad type classes: `Bind`, `Pure`, `Bind.bind`, `Pure.pure`.
    ///
    /// In Lean 4, these are type classes:
    /// ```text
    /// class Pure (f : Type u → Type v) where pure : {α : Type u} → α → f α
    /// class Bind (m : Type u → Type v) where bind : {α β : Type u} → m α → (α → m β) → m β
    /// ```
    ///
    /// We model them as axioms for the elaborator's do-notation desugaring.
    /// The elaborator emits `Bind.bind action continuation` and `Pure.pure value`,
    /// and type class resolution fills in the monad and instance arguments.
    ///
    /// # Contract
    ///
    /// REQUIRES: `init_id` has been called (for universe parameter conventions)
    /// ENSURES: On success, `self.monad_classes_init == true`
    /// ENSURES: Constants `Pure.pure` and `Bind.bind` are defined
    /// ENSURES: Idempotent
    pub(crate) fn init_monad_classes(&mut self) -> Result<(), EnvError> {
        if self.monad_classes_init {
            return Ok(());
        }

        let u = Name::from_string("u");
        let v = Name::from_string("v");

        // Type u and Type v
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone()))));
        let type_v = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(v.clone()))));

        // m : Type u → Type v (the monad type constructor)
        let m_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_v.clone());

        // Pure.pure : {m : Type u → Type v} → [Pure m] → {α : Type u} → α → m α
        //
        // For initial do-notation support, we register the "uncurried" form that
        // the elaborator produces: Pure.pure : {α : Type u} → α → m α
        // with m implicit. The full type class version requires instance resolution
        // infrastructure that we build incrementally.
        //
        // Simplified type: Pure.pure : {m : Type u → Type v} → {α : Type u} → α → m α
        let pure_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(m_type.clone());
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let m_alpha = Expr::app(m.clone(), alpha.clone());
            let (val_id, _val) = b.fresh_local(alpha.clone());
            let r = m_alpha;
            let r = b.mk_pi(val_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Implicit, m_type.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Pure.pure"),
            level_params: vec![u.clone(), v.clone()],
            type_: pure_type,
        })?;

        // Bind.bind : {m : Type u → Type v} → {α β : Type u} → m α → (α → m β) → m β
        let bind_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(m_type.clone());
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_u.clone());
            let m_alpha = Expr::app(m.clone(), alpha.clone());
            let m_beta = Expr::app(m.clone(), beta.clone());
            let (ma_id, _ma) = b.fresh_local(m_alpha.clone());
            let f_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _x) = c.fresh_local(alpha.clone());
                let r = m_beta.clone();
                let r = c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };
            let (f_id, _f) = b.fresh_local(f_ty.clone());
            let r = m_beta;
            let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
            let r = b.mk_pi(ma_id, BinderInfo::Default, m_alpha, r);
            let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Implicit, m_type.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Bind.bind"),
            level_params: vec![u.clone(), v.clone()],
            type_: bind_type,
        })?;

        // `Monad (m : Type u → Type v) : Type (max (u+1) v)` — the carrier head.
        //
        // Registered as an opaque `Axiom` CARRIER (the same convention clean uses
        // for `Membership` / `Set` in `init_set`): clean's prelude resolves monad
        // instances by metavariable, not synthesis, so the carrier needs only the
        // right KIND for an `[Monad m]` instance binder to type-check (the `ForIn`
        // field telescope, A4). On a real `.olean` import the genuine `Monad`
        // structure of the same name discharges this stub via the
        // `is_axiom_carrier_stub` import path, so it carries no permanent domain
        // axiom. Universe matches Lean's `class Monad extends Applicative` (whose
        // `Functor.map` field over `Type u` forces the `u+1`):
        //   Monad.{u,v} : (Type u → Type v) → Type (max (u+1) v)
        //
        // NOTE: this is NOT registered in `Environment::soundness_certificate_env`
        // (which seeds only NN-verification overlays), so it does not enter the C2
        // trusted-axiom golden — exactly like the existing `Bind.bind` / `Pure.pure`
        // / `Membership` carriers.
        let monad_result_sort = Expr::from_kind(ExprKind::Sort(Level::succ(Level::max(
            Level::succ(Level::param(u.clone())),
            Level::param(v.clone()),
        ))));
        let monad_type = Expr::pi(BinderInfo::Default, m_type.clone(), monad_result_sort);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Monad"),
            level_params: vec![u.clone(), v.clone()],
            type_: monad_type,
        })?;

        self.monad_classes_init = true;
        Ok(())
    }

    /// Check if monad type classes have been initialized
    pub(crate) fn has_monad_classes(&self) -> bool {
        self.monad_classes_init
    }
}
