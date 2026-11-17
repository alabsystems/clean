// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A `deriving` clause runs after its type is declared, and a class that fails
//! is an error about the clause, not about the type.
//!
//! Lean 4.8.0 elaborates `structure S … deriving C₁, C₂` (and the `inductive`
//! form) by adding `S` first and only then calling `applyDerivingHandlers`
//! once per class (`Lean/Elab/Structure.lean` `elabStructure`,
//! `Lean/Elab/Inductive.lean`, `Lean/Elab/Deriving/Basic.lean`). The `BEq`,
//! `Repr`, `Hashable`, `Ord` and `Nonempty` handlers, and `DecidableEq` on a
//! type that is not nested, elaborate their generated commands through
//! `elabCommand`, which is `withLogging`: a failure there is logged and the
//! next class still runs. `Inhabited` with no inhabited constructor, and
//! `DecidableEq` on a nested type (`mkDecEq` returns `false`, and the default
//! handler throws), THROW, which ends the clause; so does a class with no
//! handler. In neither case is `S` undone.
//!
//! A class NAME that does not resolve is different: Lean resolves every class
//! of the clause (`getOptDerivingClasses`, `realizeGlobalConstNoOverloadWithInfo`)
//! before it elaborates the type at all, so the whole declaration fails and
//! `S` is never added (pinned v4.8.0 on `structure Point where x : Nat
//! deriving Repr, UnknownClass`: `unknown constant 'UnknownClass'`, then
//! `unknown identifier 'Point'` at every use).
//! [`ElabCtx::resolve_deriving_clause`] is that up-front pass.
//!
//! Clean propagated a handler failure with `?` out of the whole declaration,
//! so `S` was never registered and every later mention of it failed for a
//! reason that said nothing about its own code. trust-ir's `FieldDef`
//! (`offset : Option Nat`, `deriving BEq, Repr`) took `StructDef`,
//! `RecordDef`, `TypingEnv` and every `{ … }` literal of them down that way
//! ("struct literal requires type annotation or expected type",
//! "expected structure type, got FVar").
//!
//! Here each class runs on its own, in clause order, with the elaborator
//! state rolled back when it fails; a failure is recorded on the context, the
//! dispatcher that holds the source declaration attaches it to the result as
//! an [`ElabResult::Failed`] leaf (so every checker counts and reports it),
//! and [`split_logged_deriving_failures`] keeps that leaf out of the
//! registration of the type. A failed class registers nothing: where Lean
//! adds the failed instance with `sorryAx` as error recovery, Clean adds no
//! instance at all.

use super::{DerivedInstance, ElabCtx, ElabResult};
use crate::ElabError;
use clean_kernel::name::Name;
use clean_parser::{SurfaceDecl, SurfaceName};

/// One class of a `deriving` clause that failed, waiting for the dispatcher
/// to attach it to the declaration's result.
#[derive(Debug)]
pub(crate) struct LoggedDerivingFailure {
    /// The report name of the failed leaf: the instance the class would have
    /// declared, so it never reads as a failure of the type itself.
    name: String,
    /// [`ElabError::DerivingHandlerFailed`] around the handler's error.
    error: ElabError,
}

/// Whether the type a `deriving` clause belongs to is a nested inductive — a
/// constructor field mentions it under another inductive (`List T`) — as
/// Lean's `InductiveVal.isNested` records it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum TypeNesting {
    /// No constructor field mentions the type under another inductive.
    Flat,
    /// Nested, or not known to be flat.
    Nested,
}

/// Whether Lean 4.8.0 lets the rest of a `deriving` clause run after this
/// class's handler fails: true exactly when the handler elaborates its
/// generated commands through the logging `elabCommand` — `BEq`, `Repr`,
/// `Hashable`, `Ord`, `Nonempty`, and `DecidableEq` on a flat type
/// (`Lean/Elab/Deriving/DecEq.lean` `mkDecEq`). `DecidableEq` on a nested type
/// returns `false` and the default handler throws ("default handlers have not
/// been implemented yet"); `Inhabited` throws when no constructor is
/// inhabited; any other class reaches the throwing default handler. Pinned
/// v4.8.0: `deriving DecidableEq, Repr` on a flat type whose `DecidableEq`
/// fails still derives `Repr`; on `inductive T | leaf | node (xs : List T)` it
/// derives neither.
///
/// Answering `false` where Lean logs only loses instances Lean would have;
/// answering `true` where Lean throws would invent them, so anything unknown
/// answers `false`.
fn lean_logs_handler_failure(class: &SurfaceName, nesting: TypeNesting) -> bool {
    match crate::derive::builtin_class(class.name()) {
        Some("BEq" | "Repr" | "Hashable" | "Ord" | "Nonempty") => true,
        Some("DecidableEq") => nesting == TypeNesting::Flat,
        _ => false,
    }
}

/// The report name of a failed class: the instance it would have declared.
fn failed_instance_name(type_name: &Name, class: &SurfaceName) -> String {
    match crate::derive::builtin_class(class.name()) {
        Some(label) => crate::derive::builtin_instance_name(type_name, label).to_string(),
        None => format!("{type_name}.deriving.{class}"),
    }
}

/// Lengths of the attribute lists an elaboration collects into, so a failed
/// handler's additions can be dropped. One list of field names, so the two
/// halves cannot disagree.
macro_rules! collected_attribute_lens {
    ($($field:ident),* $(,)?) => {
        /// How long each collected-attribute list was when a handler started.
        struct AttributeLens {
            $($field: usize,)*
        }

        impl AttributeLens {
            fn take(ctx: &ElabCtx<'_>) -> Self {
                Self { $($field: ctx.$field.len(),)* }
            }

            fn restore(self, ctx: &mut ElabCtx<'_>) {
                $(ctx.$field.truncate(self.$field);)*
            }
        }
    };
}

collected_attribute_lens!(
    collected_aesop_attrs,
    collected_simp_attrs,
    collected_local_simp,
    collected_local_csimp,
    collected_scoped_csimp,
    collected_reducibility,
    collected_extern,
    collected_export,
    collected_deprecated,
    collected_inline,
    collected_noinline,
    collected_always_inline,
    collected_specialize,
    collected_csimp,
    collected_definition_attrs,
    collected_congr,
    collected_ext,
    collected_grind,
    collected_refl,
    collected_symm,
    collected_macro_inline,
    collected_inline_if_reduce,
    collected_nospecialize,
    collected_implemented_by,
    collected_coe,
    collected_match_pattern,
    collected_init,
    collected_default_instance,
    collected_instance_attrs,
    collected_scoped_instance_attrs,
    collected_class_attrs,
    collected_derive_handler,
    collected_attribute_removals,
);

/// The elaborator state a failed handler or class validation may have left
/// half-changed, so the next declaration in the same context starts from the
/// prior local state. Class elaboration separately snapshots its class table.
///
/// The local-scope snapshot is the one every transactional elaboration uses
/// (`ElabCtx::with_local_scope_rollback`): locals with their `let` values,
/// local instances, the instance cache, raw local values, the expected type,
/// the recursion context, universe parameters with the rigid set, pending
/// level assignments and hole names; restoring it also drops the
/// type-checker caches. Beside it: every metavariable, the auto-bound
/// implicits, the postponed open-carrier instance goals, the structural
/// recursion sites and the collected attributes.
pub(super) struct DeclarationRollback {
    metas: crate::unify::MetaState,
    scope: super::elab_ctx::LocalScopeSnapshot,
    auto_implicits: Vec<(SurfaceName, clean_kernel::FVarId, clean_kernel::Expr)>,
    auto_implicit_lookup: std::collections::HashMap<SurfaceName, clean_kernel::FVarId>,
    postponed_open_carrier_instances: Vec<(clean_kernel::Expr, clean_kernel::Expr)>,
    structural_rec_sites: usize,
    attributes: AttributeLens,
}

impl DeclarationRollback {
    pub(super) fn take(ctx: &ElabCtx<'_>) -> Self {
        Self {
            metas: ctx.metas.clone(),
            scope: ctx.local_scope_snapshot(),
            auto_implicits: ctx.auto_implicits.clone(),
            auto_implicit_lookup: ctx.auto_implicit_lookup.clone(),
            postponed_open_carrier_instances: ctx.postponed_open_carrier_instances.clone(),
            structural_rec_sites: ctx.structural_rec_sites.len(),
            attributes: AttributeLens::take(ctx),
        }
    }

    pub(super) fn restore(self, ctx: &mut ElabCtx<'_>) {
        ctx.metas = self.metas;
        ctx.restore_local_scope(self.scope, true);
        ctx.auto_implicits = self.auto_implicits;
        ctx.auto_implicit_lookup = self.auto_implicit_lookup;
        ctx.postponed_open_carrier_instances = self.postponed_open_carrier_instances;
        ctx.structural_rec_sites.truncate(self.structural_rec_sites);
        self.attributes.restore(ctx);
    }
}

impl ElabCtx<'_> {
    /// Resolve every class of a `deriving` clause before its type is
    /// elaborated, as Lean's `getOptDerivingClasses` does, and fail the whole
    /// declaration on the first class that does not resolve. Only a check:
    /// the handlers resolve each class again when they run, and the
    /// elaborator state is restored whether resolution succeeds or fails.
    pub(super) fn resolve_deriving_clause<'s>(
        &mut self,
        deriving: impl IntoIterator<Item = &'s SurfaceName>,
    ) -> Result<(), ElabError> {
        let rollback = DeclarationRollback::take(self);
        let resolved = deriving
            .into_iter()
            .try_for_each(|class| self.resolve_derive_class(class).map(drop));
        rollback.restore(self);
        resolved
    }

    /// Run `deriving` for the type `type_name` one class at a time, in clause
    /// order, the way Lean's `applyDerivingHandlers` loop does after the type
    /// is added. `derive_one` derives one class.
    ///
    /// A class that fails contributes nothing (its state is rolled back) and
    /// is recorded on the context for the dispatcher; the clause then goes on
    /// only if Lean's handler for that class would have logged rather than
    /// thrown ([`lean_logs_handler_failure`], which needs the type's
    /// `nesting`). Never fails itself: every failure is a recorded one, and
    /// the type is declared regardless.
    pub(super) fn derive_clause_logged(
        &mut self,
        type_name: &Name,
        nesting: TypeNesting,
        deriving: &[SurfaceName],
        mut derive_one: impl FnMut(&mut Self, &SurfaceName) -> Result<Vec<DerivedInstance>, ElabError>,
    ) -> Vec<DerivedInstance> {
        let mut instances = Vec::new();
        for class in deriving {
            // Lean's `DecidableEq` handler declines a nested type (`mkDecEq`
            // returns `false` on `isNested`) and the default handler throws,
            // which ends the clause — whatever Clean's own handler could
            // derive for it (pinned v4.8.0: `inductive T | leaf | node (xs :
            // List T) deriving DecidableEq, Repr` derives neither).
            if nesting == TypeNesting::Nested
                && crate::derive::builtin_class(class.name()) == Some("DecidableEq")
            {
                self.logged_deriving_failures.push(LoggedDerivingFailure {
                    name: failed_instance_name(type_name, class),
                    error: ElabError::DerivingHandlerFailed {
                        class: class.to_string(),
                        type_name: type_name.to_string(),
                        error: Box::new(ElabError::Unsupported {
                            feature: format!(
                                "default handlers have not been implemented yet, class: \
                                 'DecidableEq' types: [{type_name}] (Lean 4.8.0 derives \
                                 `DecidableEq` for no nested inductive type)"
                            ),
                        }),
                    },
                });
                break;
            }
            let rollback = DeclarationRollback::take(self);
            match derive_one(self, class) {
                Ok(derived) => instances.extend(derived),
                Err(error) => {
                    rollback.restore(self);
                    self.logged_deriving_failures.push(LoggedDerivingFailure {
                        name: failed_instance_name(type_name, class),
                        error: ElabError::DerivingHandlerFailed {
                            class: class.to_string(),
                            type_name: type_name.to_string(),
                            error: Box::new(error),
                        },
                    });
                    if !lean_logs_handler_failure(class, nesting) {
                        break;
                    }
                }
            }
        }
        instances
    }

    /// Attach the `deriving` failures recorded while `decl` elaborated to its
    /// result, as [`ElabResult::Failed`] leaves beside it. A declaration that
    /// failed outright drops them: its own error is the one reported.
    pub(super) fn attach_logged_deriving_failures(
        &mut self,
        decl: &SurfaceDecl,
        result: Result<ElabResult, ElabError>,
    ) -> Result<ElabResult, ElabError> {
        let failures = std::mem::take(&mut self.logged_deriving_failures);
        let result = result?;
        if failures.is_empty() {
            return Ok(result);
        }
        let mut results = Vec::with_capacity(failures.len() + 1);
        results.push(result);
        // This is where a logged failure is reported (nothing catches it any
        // more), so a deferred "did you mean" scan inside it runs here.
        let env = self.env;
        results.extend(failures.into_iter().map(|failure| ElabResult::Failed {
            name: failure.name,
            decl: Box::new(decl.clone()),
            error: Box::new(failure.error.with_ident_suggestions(env)),
        }));
        Ok(ElabResult::Multiple(results))
    }

    /// Fail closed on a recorded `deriving` failure no dispatcher attached:
    /// it would otherwise vanish with the context, and the type would pass.
    pub(super) fn unattached_deriving_failure(&mut self) -> Option<ElabError> {
        let mut failures = std::mem::take(&mut self.logged_deriving_failures);
        if failures.is_empty() {
            None
        } else {
            Some(failures.swap_remove(0).error)
        }
    }
}

fn is_logged_deriving_failure(result: &ElabResult) -> bool {
    matches!(
        result,
        ElabResult::Failed { error, .. }
            if matches!(**error, ElabError::DerivingHandlerFailed { .. })
    )
}

/// Split `result` into what registers and the logged `deriving` failures
/// [`ElabCtx::attach_logged_deriving_failures`] put beside a type. The
/// `Multiple` that attachment made collapses back to the type itself, so the
/// type registers exactly as a clause without the failed classes would have.
/// Every other `Failed` leaf stays where it is, and keeps failing
/// registration.
pub(crate) fn split_logged_deriving_failures(result: ElabResult) -> (ElabResult, Vec<ElabResult>) {
    let mut logged = Vec::new();
    let registrable = split_into(result, &mut logged);
    (registrable, logged)
}

fn split_into(result: ElabResult, logged: &mut Vec<ElabResult>) -> ElabResult {
    let ElabResult::Multiple(results) = result else {
        return result;
    };
    let mut kept = Vec::with_capacity(results.len());
    let mut attached_here = false;
    for inner in results {
        if is_logged_deriving_failure(&inner) {
            attached_here = true;
            logged.push(inner);
        } else {
            kept.push(split_into(inner, logged));
        }
    }
    if attached_here && kept.len() == 1 {
        if let Some(only) = kept.pop() {
            return only;
        }
    }
    ElabResult::Multiple(kept)
}

#[cfg(test)]
#[path = "deriving_log_tests.rs"]
mod tests;
