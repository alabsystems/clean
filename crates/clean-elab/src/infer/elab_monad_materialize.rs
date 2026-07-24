// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Monad instance materialization pass (Brick B07 —
//! `docs/plans/GAP_SWEEP_2026-07-09.md`, do-notation value certification).
//!
//! # What this pass does
//!
//! Clean's prelude models `Pure.pure` / `Bind.bind` as value-less,
//! instance-less axiom stubs (`data_monad.rs::init_monad_classes`):
//!
//! ```text
//! Pure.pure : {m : Type u → Type v} → {α : Type u} → α → m α          (axiom)
//! Bind.bind : {m : Type u → Type v} → {α β : Type u} → m α → (α → m β) → m β
//! ```
//!
//! Every do-notation lane (and the bare `pure`/`bind` prelude aliases) emits
//! applications of these stubs. An axiom has no body, so the kernel can NEVER
//! unfold them — which is why no do-block value was rfl-certifiable (GAP_SWEEP
//! do_notation rows p01–p07, p09, p10, p17, p18 — 11 SILENT_WRONG_SUSPECT
//! pins) while the raw `Option.bind` control probe reduced fine.
//!
//! This pass runs once per declaration, after elaboration and level
//! canonicalization, and rewrites every saturated stub application whose
//! monad argument `m` is a closed, constant-headed type with a registered
//! `Pure`/`Bind` instance into the instance-projected form:
//!
//! ```text
//! Pure.pure m α v        ↦  (Proj Pure 0 inst) α v
//! Bind.bind m α β ma f   ↦  (Proj Bind 0 inst) α β ma f
//! ```
//!
//! where `inst` is resolved through the ordinary elaborator instance table
//! (`instPureOption`/`instBindOption`, … — real, fully kernel-checked
//! definitions registered by `clean-kernel::env::data_monad_insts`).
//!
//! # Lean-parity argument (TCB discipline)
//!
//! The TRUSTED core is untouched: this is a pure elaborator (term-producing)
//! change, and the emitted term is re-checked by the kernel like any other.
//! The output shape is exactly what Lean's own elaborator produces for the
//! same source — `@Bind.bind Option (Monad.toBind Option instMonadOption) α β
//! ma f`, i.e. a *projection applied to an instance definition* — modulo
//! Clean's flat instance names and the primitive-`Proj` spelling (Lean
//! compiles structure projections to primitive `proj` at the kernel level
//! too). The kernel then certifies `rfl` pins through its ORDINARY reduction
//! sequence (delta on the instance definition → proj-of-mk iota → beta →
//! `Option.rec` iota), each step derivable from the registered environment —
//! precisely the `type_checker.cpp` whnf behavior on Lean's elaboration of
//! the same program. No reduction is special-cased anywhere.
//!
//! # Strict lean4-core gate (GAP_SWEEP OVER_ACCEPT-01, do_notation/p11)
//!
//! With `Environment::lean4_core_strict_monads()` set (the
//! `clean check --prelude lean4-core` lane), a saturated stub application over
//! a closed constant-headed monad that has NO registered instance and is not
//! one of the stub-modeled Lean-core monads ([`STUB_MODELED_CORE_MONADS`]) is
//! an elaboration error — mirroring real Lean core, which rejects `do` over
//! `List` with "failed to synthesize Monad List" (core `Init/` has no List
//! monad instance; verified against v4.30.0-rc2). The default builtin prelude
//! is not gated and additionally registers the List instances
//! (`init_monad_list_insts`), keeping the documented Clean-native extension.
//!
//! # Zero-movement guarantees
//!
//! - `m` not constant-headed (bound variable / metavariable / transformer
//!   lambda): application left verbatim — the generic prelude lanes
//!   (`List.forIn`, `List.mapM`, `Bind.kleisli*`, StateT/ExceptT control
//!   stacks) are untouched.
//! - No instance registered and not strict: application left verbatim.
//! - The rewrite target is definitionally equal to what the stub application
//!   *claims* to denote, and the kernel re-checks every emitted term, so
//!   accepts can only be added, never changed.

use clean_kernel::{BinderInfo, Expr, ExprKind, Name};

use super::{ElabCtx, ElabResult};
use crate::error::ElabError;

/// Concrete monads that Lean 4 core DOES provide `Monad` instances for but
/// which Clean still models through the instance-less stub lane (opaque
/// axioms / `monad_reduce` short-circuits). In the strict lean4-core gate
/// these stay accepted-as-stubs; everything else without a registered
/// instance is rejected, matching real Lean core's failed-to-synthesize.
const STUB_MODELED_CORE_MONADS: &[&str] = &[
    "Id",
    "IO",
    "EIO",
    "BaseIO",
    "Except",
    "ExceptT",
    "StateT",
    "StateM",
    "StateRefT'",
    "ReaderT",
    "ReaderM",
    "OptionT",
    "EStateM",
    "Task",
    "Thunk",
];

impl<'a> ElabCtx<'a> {
    /// Apply monad-instance materialization to the expressions of an
    /// [`ElabResult`].
    ///
    /// Scope is deliberately tight (zero-movement discipline): only
    /// `Definition`, `Theorem`, and `Example` results are rewritten — the
    /// decl kinds whose values/types carry do-notation output that the check
    /// lane value-certifies. All other variants pass through unchanged.
    pub(super) fn materialize_monad_instances_in_elab_result(
        &mut self,
        result: ElabResult,
    ) -> Result<ElabResult, ElabError> {
        Ok(match result {
            ElabResult::Definition {
                name,
                universe_params,
                ty,
                val,
                modifiers,
            } => ElabResult::Definition {
                name,
                universe_params,
                ty: self.materialize_monad_instances(&ty)?,
                val: self.materialize_monad_instances(&val)?,
                modifiers,
            },
            ElabResult::Theorem {
                name,
                universe_params,
                ty,
                proof,
                modifiers,
            } => ElabResult::Theorem {
                name,
                universe_params,
                ty: self.materialize_monad_instances(&ty)?,
                proof: self.materialize_monad_instances(&proof)?,
                modifiers,
            },
            ElabResult::Example { ty, val } => ElabResult::Example {
                ty: self.materialize_monad_instances(&ty)?,
                val: self.materialize_monad_instances(&val)?,
            },
            ElabResult::Multiple(results) => ElabResult::Multiple(
                results
                    .into_iter()
                    .map(|r| self.materialize_monad_instances_in_elab_result(r))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            other => other,
        })
    }

    /// Rewrite saturated `Pure.pure`/`Bind.bind` stub applications over
    /// instance-resolvable concrete monads into instance-projected form.
    /// See the module doc for the full contract.
    pub(crate) fn materialize_monad_instances(&mut self, e: &Expr) -> Result<Expr, ElabError> {
        // Fast path: nothing to do in environments without the real classes
        // (e.g. bare `Environment::new()` unit-test envs).
        if !self.instances.is_class(&Name::from_string("Bind"))
            && !self.instances.is_class(&Name::from_string("Pure"))
        {
            return Ok(e.clone());
        }
        self.materialize_monad_apps(e)
    }

    fn materialize_monad_apps(&mut self, e: &Expr) -> Result<Expr, ElabError> {
        crate::stack_safe(|| match e.kind() {
            ExprKind::App(..) => {
                let head = e.get_app_fn();
                let args = e.get_app_args();

                // Recurse into every argument first (bottom-up), and into a
                // non-constant head (e.g. a beta-redex lambda).
                let new_args: Vec<Expr> = args
                    .iter()
                    .map(|a| self.materialize_monad_apps(a))
                    .collect::<Result<_, _>>()?;
                let new_head = match head.kind() {
                    ExprKind::Const(..) => head.clone(),
                    _ => self.materialize_monad_apps(head)?,
                };

                if let ExprKind::Const(name, levels) = new_head.kind() {
                    let shape = match name.to_string().as_str() {
                        // stub: Pure.pure m α v (+tail)
                        "Pure.pure" => Some(("Pure", 3usize)),
                        // stub: Bind.bind m α β ma f (+tail)
                        "Bind.bind" => Some(("Bind", 5usize)),
                        _ => None,
                    };
                    if let Some((class_name, min_args)) = shape {
                        // The rewrite models Clean's INSTANCE-LESS prelude
                        // stubs (`data_monad.rs::init_monad_classes`):
                        // value-less axioms whose telescope carries no
                        // instance binder, so the spine is `[m, α, …]`. When
                        // the environment instead holds the REAL Lean-core
                        // class projection (a value-carrying definition with
                        // a `[self : <Class> m]` binder, machine-imported
                        // from `.olean`s), the spine is `[m, self, α, …]` —
                        // applying the stub rewrite there consumes `m` but
                        // keeps `self`, splicing the synthesized instance
                        // projection one argument slot too early and emitting
                        // an ill-typed term the kernel then rejects (observed
                        // on trust-clean's Lean↔Clean bridge DATALOOP lemmas:
                        // `@Bind.bind TrustIr.Sem self α β ma f` over the
                        // imported Init classes). The real form needs no
                        // materialization at all — its instance argument is
                        // already in the term, and the kernel's ordinary
                        // delta → proj-of-ctor → beta sequence certifies it.
                        // Fire only on the genuine stub registration.
                        if self.is_instanceless_monad_stub(name) && new_args.len() >= min_args {
                            if let Some(rewritten) = self.try_materialize_stub_app(
                                class_name,
                                levels.as_slice(),
                                &new_args,
                            )? {
                                return Ok(rewritten);
                            }
                        }
                    }
                }

                Ok(Expr::apps(new_head, new_args))
            }
            ExprKind::Lam(bd, ty, body) => Ok(Expr::lam(
                *bd,
                self.materialize_monad_apps(ty)?,
                self.materialize_monad_apps(body)?,
            )),
            ExprKind::Pi(bd, ty, body) => Ok(Expr::pi(
                *bd,
                self.materialize_monad_apps(ty)?,
                self.materialize_monad_apps(body)?,
            )),
            ExprKind::Let(name, ty, val, body, non_dep) => Ok(Expr::let_named(
                name.clone(),
                self.materialize_monad_apps(ty)?,
                self.materialize_monad_apps(val)?,
                self.materialize_monad_apps(body)?,
                *non_dep,
            )),
            ExprKind::Proj(struct_name, idx, inner) => Ok(Expr::proj(
                struct_name.clone(),
                *idx,
                self.materialize_monad_apps(inner)?,
            )),
            // Leaves (BVar/FVar/Sort/Const/Lit/…) and exotic mode-specific
            // nodes (cubical/impredicative extensions): no do-notation output
            // lives inside them — return verbatim.
            _ => Ok(e.clone()),
        })
    }

    /// Attempt the single-application rewrite. `args` are the already
    /// materialized stub arguments (`[m, α, v, tail…]` for `Pure`,
    /// `[m, α, β, ma, f, tail…]` for `Bind`).
    ///
    /// Returns `Ok(None)` when the application must stay a stub (monad not
    /// concrete / no instance in a non-strict environment), `Ok(Some(_))` on
    /// a successful rewrite, and `Err(FailedToSynthesize)` under the strict
    /// lean4-core gate.
    fn try_materialize_stub_app(
        &mut self,
        class_name: &str,
        levels: &[clean_kernel::Level],
        args: &[Expr],
    ) -> Result<Option<Expr>, ElabError> {
        let m = self.metas.instantiate(&args[0]);

        // Only closed, constant-headed monads are decidable here. Bound
        // variables (generic `{m}` telescopes), metavariables (FVar-encoded),
        // and transformer lambdas stay on the stub lane.
        if m.loose_bvar_range() > 0 || m.has_fvar_quick() {
            return Ok(None);
        }
        let ExprKind::Const(m_head, _) = m.get_app_fn().kind() else {
            return Ok(None);
        };

        // Goal `<Class>.{u,v} m` at the stub's own universe levels — the class
        // structures (data_monad_insts.rs) share the stub's `{u, v}` telescope.
        let class = Name::from_string(class_name);
        let goal = Expr::app(Expr::const_(class.clone(), levels.to_vec()), m.clone());
        if let Some(inst) = self.resolve_instance(&goal) {
            let inst = self.metas.instantiate(&inst);
            // The instance must be a closed term (a constant application);
            // anything metavariable- or fvar-laden would leak out of scope.
            if !self.has_metavars(&inst) && !inst.has_fvar_quick() && inst.loose_bvar_range() == 0 {
                let head = Expr::proj(class, 0, inst);
                return Ok(Some(Expr::apps_ref(head, &args[1..])));
            }
            return Ok(None);
        }

        // No instance. In the strict lean4-core lane, a concrete monad outside
        // the stub-modeled core set is a failed synthesis — Lean-core parity
        // (e.g. `do` over `List`: no Monad List instance in core Init/).
        if self.env.lean4_core_strict_monads() {
            let m_head_str = m_head.to_string();
            if !STUB_MODELED_CORE_MONADS
                .iter()
                .any(|known| *known == m_head_str)
            {
                return Err(ElabError::FailedToSynthesize {
                    class_name: Name::from_string("Monad"),
                    goal: format!("Monad {m_head_str}"),
                });
            }
        }

        Ok(None)
    }

    /// True iff `name` is registered in this environment as Clean's
    /// INSTANCE-LESS prelude monad stub (`data_monad.rs::init_monad_classes`):
    /// a value-less axiom whose Pi telescope carries no `[inst : …]` binder.
    ///
    /// The REAL Lean-core class projections (`Pure.pure`/`Bind.bind` imported
    /// from `.olean`s) are value-carrying definitions with a
    /// `[self : <Class> m]` instance binder — their application spines already
    /// carry the instance argument at position 1, so the stub rewrite's
    /// `[m, α, …]` arity assumption would misalign every argument (see the
    /// call-site comment). Those must never enter the materialization lane.
    ///
    /// An unregistered head also returns `false`: with no `ConstantInfo` we
    /// cannot know the telescope shape, and skipping is the fail-closed choice
    /// (the kernel re-checks the untouched term either way).
    fn is_instanceless_monad_stub(&self, name: &Name) -> bool {
        let Some(info) = self.env.get_const(name) else {
            return false;
        };
        if info.value.is_some() {
            return false;
        }
        let mut ty = &info.type_;
        loop {
            match ty.kind() {
                ExprKind::Pi(bd, _, body) => {
                    if bd.info == BinderInfo::InstImplicit {
                        return false;
                    }
                    ty = body.as_ref();
                }
                _ => return true,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::env::{Environment, TrustedEnvExt};
    use clean_kernel::ConstantInfo;

    use crate::infer::ElabCtx;

    fn register(env: &mut Environment, name: &str, ty: Expr, value: Option<Expr>) {
        // SOUNDNESS: test-only fixture registration. These synthetic constants
        // exercise the monad-stub shape discriminator and are compiled out of
        // every production build; no unchecked declaration can reach a stored
        // environment, kernel verdict, or exported artifact.
        env.extend_constants_unchecked(std::iter::once(ConstantInfo::new(
            Name::from_string(name),
            vec![],
            ty,
            value,
            false,
        )));
    }

    /// Stub telescope (no instance binder): `{m : Type → Type} → {α β : Type}
    /// → m α → (α → m β) → m β` is approximated shape-wise — the discriminator
    /// only inspects binder infos and value-presence, not the domains.
    fn stub_like_ty() -> Expr {
        Expr::pi(
            BinderInfo::Implicit,
            Expr::type_(),
            Expr::pi(
                BinderInfo::Implicit,
                Expr::type_(),
                Expr::arrow(Expr::bvar(0), Expr::bvar(1)),
            ),
        )
    }

    /// Real Lean-core class-projection telescope: same, plus a
    /// `[self : Bind m]` instance-implicit binder in second position.
    fn real_projection_ty() -> Expr {
        Expr::pi(
            BinderInfo::Implicit,
            Expr::type_(),
            Expr::pi(
                BinderInfo::InstImplicit,
                Expr::bvar(0),
                Expr::pi(
                    BinderInfo::Implicit,
                    Expr::type_(),
                    Expr::arrow(Expr::bvar(0), Expr::bvar(2)),
                ),
            ),
        )
    }

    /// The value-less, instance-binder-less prelude stub IS the stub lane.
    #[test]
    fn instanceless_axiom_stub_is_recognized() {
        let mut env = Environment::new();
        register(&mut env, "Bind.bind", stub_like_ty(), None);
        let ctx = ElabCtx::new(&env);
        assert!(ctx.is_instanceless_monad_stub(&Name::from_string("Bind.bind")));
    }

    /// A value-carrying `Bind.bind` (the REAL Lean-core class projection
    /// machine-imported from `.olean`s) must NOT enter the stub rewrite lane:
    /// its spine is `[m, self, α, β, ma, f]`, and the stub rewrite's
    /// `[m, α, β, ma, f]` arity assumption would splice the synthesized
    /// instance projection one slot too early (the trust-clean Lean↔Clean
    /// bridge DATALOOP regression, 2026-07-12).
    #[test]
    fn value_carrying_projection_is_not_stub() {
        let mut env = Environment::new();
        register(
            &mut env,
            "Bind.bind",
            real_projection_ty(),
            Some(Expr::type_()), // any body: value-presence alone must disqualify
        );
        let ctx = ElabCtx::new(&env);
        assert!(!ctx.is_instanceless_monad_stub(&Name::from_string("Bind.bind")));
    }

    /// Even a value-less constant is disqualified when its telescope carries
    /// an `[inst : …]` binder — the spine already has an instance argument.
    #[test]
    fn instance_binder_telescope_is_not_stub() {
        let mut env = Environment::new();
        register(&mut env, "Pure.pure", real_projection_ty(), None);
        let ctx = ElabCtx::new(&env);
        assert!(!ctx.is_instanceless_monad_stub(&Name::from_string("Pure.pure")));
    }

    /// An unregistered head is fail-closed: not a stub, no rewrite.
    #[test]
    fn unregistered_head_is_not_stub() {
        let env = Environment::new();
        let ctx = ElabCtx::new(&env);
        assert!(!ctx.is_instanceless_monad_stub(&Name::from_string("Bind.bind")));
    }
}
