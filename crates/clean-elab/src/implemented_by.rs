// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `@[implemented_by f]`: resolved where pinned Lean resolves it, refused
//! with Lean's text, and the order record of the command form.
//!
//! Lean's `getParam` (`Lean/Compiler/ImplementedByAttr.lean@v4.30.0-rc2`),
//! behind `registerParametricAttribute`'s imported-module check, in order:
//!
//! 1. the command form `attribute [implemented_by f] d` may not name a
//!    declaration of an imported module ("Cannot add attribute
//!    `[implemented_by]` to declaration `d` because it is in an imported
//!    module"): one this elaboration run did not add
//!    ([`crate::declared_here`]), whatever the driver;
//! 2. `f` resolves with `realizeGlobalConstNoOverload` in the declaration's
//!    scope ("Unknown constant", "ambiguous identifier"): where it is
//!    written, inside the namespace Lean's `expandDeclNamespace?` opens for
//!    the declaration (`ElabCtx::decl_site_namespace`). The attribute is
//!    applied after the declaration is added and before a LATER member of
//!    its `mutual` block is, so such a member is unknown;
//! 3. to 5. levels, structural type and self: [`crate::ffi_extern::validate_implemented_by`].
//!
//! The argument is captured where it is written ([`ImplementedByUse`]) and
//! resolved when the attributes are applied, against the environment the
//! declaration was registered into.
//!
//! The command form also records, in the environment, the code it comes too
//! late for ([`compiled_before_binding`], the kernel environment's
//! `record_compiled_before`), whatever the driver.

use std::collections::HashSet;
use std::sync::Arc;

use clean_kernel::env::CompiledBefore;
use clean_kernel::{Environment, Name};

use crate::declared_here::{declared_by, AttributeSite, ElabUnit};
use crate::name_resolution::{resolve_global_const_no_overload, GlobalConstResolution};
use crate::namespace::NamespaceState;
use crate::{ElabError, FileContext};

/// One `@[implemented_by f]` use, captured when it is collected with the
/// scope `f` must resolve in, and resolved when it is applied.
#[derive(Debug, Clone)]
pub(crate) struct ImplementedByUse {
    /// The declaration the attribute is on.
    pub(crate) decl: Name,
    /// The target as written.
    pub(crate) written: clean_parser::SurfaceName,
    pub(crate) site: AttributeSite,
    /// The namespace state at the use, with the namespace Lean's
    /// `expandDeclNamespace?` opens for the declaration entered
    /// (`ElabCtx::decl_site_namespace`).
    pub(crate) scope: NamespaceState,
    /// Other modules' `private` declarations, which never resolve.
    pub(crate) foreign_private: Arc<HashSet<Name>>,
    /// Constants registered with the declaration that Lean has not added yet
    /// when it applies the attribute: the LATER members of its `mutual`
    /// block. Resolving to one is "Unknown constant".
    pub(crate) not_yet_declared: Arc<[Name]>,
}

/// Why pinned Lean refuses an `@[implemented_by]` argument.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ImplementedByDefect {
    /// The target names no constant in scope ("Unknown constant").
    UnknownConstant,
    /// The target names several constants ("ambiguous identifier").
    Ambiguous(Vec<Name>),
    /// The command form names a declaration of another module.
    ImportedDeclaration,
    /// The level-parameter counts differ.
    LevelCount {
        target_levels: usize,
        decl_levels: usize,
    },
    /// The types differ structurally (rendered).
    TypeMismatch {
        target_type: String,
        decl_type: String,
    },
    /// The target is the declaration itself.
    SelfImplementation,
}

/// Lean's text for a refused `@[implemented_by]` argument. `target` is the
/// argument as written when it did not resolve, else the resolved name (Lean
/// prints `fnName` after `realizeGlobalConstNoOverload`).
pub(crate) fn render(decl: &Name, target: &str, defect: &ImplementedByDefect) -> String {
    let invalid = format!("Invalid `implemented_by` argument `{target}`");
    match defect {
        ImplementedByDefect::UnknownConstant => format!("Unknown constant `{target}`"),
        ImplementedByDefect::Ambiguous(candidates) => format!(
            "ambiguous identifier ``{target}`, possible interpretations: [{}]",
            candidates
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        ImplementedByDefect::ImportedDeclaration => format!(
            "Cannot add attribute `[implemented_by]` to declaration `{decl}` because it is in \
             an imported module"
        ),
        ImplementedByDefect::LevelCount {
            target_levels,
            decl_levels,
        } => format!(
            "{invalid}: `{target}` has {target_levels} universe level parameter(s), but \
             `{decl}` has {decl_levels}"
        ),
        ImplementedByDefect::TypeMismatch {
            target_type,
            decl_type,
        } => format!(
            "{invalid}: `{target}` has type\n  {target_type}\nbut `{decl}` has type\n  {decl_type}"
        ),
        ImplementedByDefect::SelfImplementation => {
            format!("{invalid}: Definition cannot be implemented by itself")
        }
    }
}

/// Resolve and validate one use in Lean's order (module doc), returning the
/// constant to register as the declaration's implementation.
///
/// `file_ctx` names the run step 1 asks about ([`ElabUnit::of`]).
pub(crate) fn resolve_implemented_by(
    env: &Environment,
    file_ctx: Option<&FileContext>,
    use_: &ImplementedByUse,
) -> Result<Name, ElabError> {
    let refuse = |defect| ElabError::InvalidImplementedBy {
        decl: use_.decl.clone(),
        target: use_.written.to_string(),
        defect,
    };
    if use_.site == AttributeSite::AttributeCommand
        && !declared_by(env, ElabUnit::of(file_ctx), &use_.decl)
    {
        return Err(refuse(ImplementedByDefect::ImportedDeclaration));
    }
    let target = match resolve_global_const_no_overload(
        &use_.written,
        &use_.scope,
        env,
        &use_.foreign_private,
    ) {
        Ok(target) if use_.not_yet_declared.contains(&target) => {
            return Err(refuse(ImplementedByDefect::UnknownConstant));
        }
        Ok(target) => target,
        Err(GlobalConstResolution::Unknown) => {
            return Err(refuse(ImplementedByDefect::UnknownConstant));
        }
        Err(GlobalConstResolution::Ambiguous(mut candidates)) => {
            // Lean prints the candidates in name order (both measured shapes).
            candidates.sort_by_key(ToString::to_string);
            return Err(refuse(ImplementedByDefect::Ambiguous(candidates)));
        }
    };
    crate::ffi_extern::validate_implemented_by(&use_.decl, &target, env)?;
    Ok(target)
}

/// The code an `attribute [implemented_by]` command binding the
/// declarations in `rebound` comes too late for, in `env` as it stands before
/// the binding: every constant of `env` is judged
/// ([`Environment::compiled_before_binding`], which states the rule and its
/// cost, and which `.olean` import uses for an imported module's own
/// constants; `implemented_by_tests` holds it to a per-round rescan).
pub(crate) fn compiled_before_binding(
    env: &Environment,
    rebound: &HashSet<Name>,
) -> Vec<(Name, CompiledBefore)> {
    env.compiled_before_binding(rebound, None)
}

/// The rebound declarations whose OWN compiled code an `attribute
/// [implemented_by]` command comes too late for, each recorded as reaching
/// itself (`referrer == rebound == via`): every value-bearing non-theorem in
/// `rebound` that is neither `@[noinline]` nor `@[macro_inline]`.
///
/// Pinned Lean compiled such a declaration when it was added, and its
/// inliner copies that pre-binding code into callers compiled AFTER the
/// command, in the file and in every importer, whenever the declaration is
/// an inline candidate: `@[inline]`, and any body of LCNF size at most 1
/// (`compiler.small`, `Lean/Compiler/LCNF/Simp/InlineCandidate.lean`).
/// Measured with `lean --run`, pinned v4.30.0-rc2, `fast n := Nat.add n 100`:
/// `def slow (n : Nat) : Nat := n` then `attribute [implemented_by fast]
/// slow`, a later `main` printing `slow 1` prints `1` (the old body), and so
/// does an importer; `@[inline] def slow n := Nat.add n 2` prints `3`; with
/// `@[noinline] def slow n := n` both print `101`. Clean cannot compute
/// Lean's LCNF size, so only `@[noinline]` exempts a declaration. A
/// `@[macro_inline]` declaration is never bound ([`binding_applies`]).
///
/// A structure projection is recorded whatever its inline attribute: Lean
/// compiles it as a field access and never runs an implementation bound to
/// it (`attribute [implemented_by pf] P.a`, then `P.a ⟨1⟩` prints `1` in a
/// later caller and in an importer, where `pf` gives `10`; measured with
/// `lean --run`, pinned v4.30.0-rc2).
pub(crate) fn own_code_before_binding(
    env: &Environment,
    rebound: &HashSet<Name>,
) -> Vec<(Name, CompiledBefore)> {
    let mut own: Vec<(Name, CompiledBefore)> = rebound
        .iter()
        .filter(|decl| {
            env.get_const(decl).is_some_and(|info| {
                info.value.is_some() && info.kind != clean_kernel::ConstantKind::Theorem
            }) && (!env.is_noinline(decl) || is_structure_projection(env, decl))
                && binding_applies(env, decl)
        })
        .map(|decl| {
            (
                decl.clone(),
                CompiledBefore {
                    rebound: decl.clone(),
                    via: decl.clone(),
                },
            )
        })
        .collect();
    own.sort_by_key(|(decl, _)| decl.to_string());
    own
}

/// Whether `decl` is a field projection `S.f` of a structure `S`.
fn is_structure_projection(env: &Environment, decl: &Name) -> bool {
    match decl.inner() {
        clean_kernel::name::NameInner::Str(parent, field) => env
            .get_structure_field_index(parent, &Name::anon().str(field))
            .is_some(),
        _ => false,
    }
}

/// Whether an `@[implemented_by]` binding of `decl` changes what compiled
/// code runs: not for a `@[macro_inline]` declaration, whose body pinned Lean
/// expands at every call site before the substitution could apply. Measured
/// with `lean --run`, `fast n := Nat.add n 1`: `@[macro_inline,
/// implemented_by fast] def slow (n : Nat) : Nat := Nat.add n 2` prints `3`
/// for `slow 1`, in the file, through a caller and in an importer, and so does
/// the late command form; Lean v4.8.0 prints the same. So the binding is
/// validated as Lean validates it and not registered: every reference
/// compiles the body, as Lean's does.
pub(crate) fn binding_applies(env: &Environment, decl: &Name) -> bool {
    !env.is_macro_inline(decl)
}

#[cfg(test)]
#[path = "implemented_by_tests.rs"]
mod tests;
