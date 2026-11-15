// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Name resolution helpers for the elaborator.

use crate::namespace::NamespaceState;
use clean_kernel::expr::ExprKind;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr};
use std::collections::BTreeSet;

/// Resolve an identifier against the environment and active namespace state.
///
/// Resolution order mirrors Lean's `resolveGlobalName`
/// (`Lean/ResolveName.lean`, gap sweep B03):
/// 1. `_root_.`-prefixed names force root resolution (marker stripped).
/// 2. Qualify with the current namespace, walking OUTWARD (`A.B.name`,
///    then `A.name`) — `resolveUsingNamespace`.
/// 3. Qualify with each open namespace, in order.
/// 4. Treat `name` as already fully qualified (root-level exact match).
/// 5. Fall back to an ALIAS of that name — `export Foo (x)`. Lean folds
///    aliases into the candidate set of every stage (`getAliases`); Clean
///    consults them after the constant lookup of the same stage, so an alias
///    can only resolve a name that resolved to nothing. There are TWO alias
///    tables and both are read: `NamespaceState` holds this file's own
///    `export`s, and the environment holds the `Lean.aliasExtension` rows
///    decoded from imported `.olean`s.
///
/// Returns the first matching constant name found in the environment.
#[must_use]
pub(crate) fn resolve_identifier(
    name: &clean_parser::SurfaceName,
    ns_state: &NamespaceState,
    env: &Environment,
) -> Option<Name> {
    if name.is_anonymous() || name.is_relative_constructor() {
        return None;
    }

    // A notation or macro template's free name (`rw [kq]`, `unfold kq`, `simp
    // [kq]` in a tactic template) denotes what it named where the template
    // was DECLARED — Lean pre-resolves a quotation's identifiers there — not
    // what the `open`s of the use make of its spelling. The term elaborator
    // reads the same record (`ElabCtx::template_resolution`).
    if let Some(site) = name.template_origin().and_then(|origin| origin.site) {
        if let Some(resolution) = ns_state.template_resolution(site, name.name()) {
            return match &resolution.ident {
                crate::namespace::TemplateGlobal::Global(global) => {
                    env.get_const(global).is_some().then(|| global.clone())
                }
                crate::namespace::TemplateGlobal::Redirect(target) => {
                    let target = Name::from_string(target);
                    env.get_const(&target).is_some().then_some(target)
                }
                crate::namespace::TemplateGlobal::BuiltinId
                | crate::namespace::TemplateGlobal::BuiltinCond
                | crate::namespace::TemplateGlobal::Unresolved
                | crate::namespace::TemplateGlobal::Ambiguous(_) => None,
            };
        }
    }

    let normalized = name.qualify_under(&clean_parser::SurfaceName::default());
    if normalized.name() != name.name() {
        if env.get_const(normalized.name()).is_some() {
            return Some(normalized.into_name());
        }
        return own_private(ns_state, env, normalized.name());
    }

    // Walk exact namespace ancestors; a quoted dotted component is indivisible.
    let mut prefix = ns_state.current_namespace().clone();
    while !prefix.is_anon() {
        let candidate = clean_parser::SurfaceName::from_name(prefix.clone())
            .append(name)
            .into_name();
        if env.get_const(&candidate).is_some() {
            return Some(candidate);
        }
        if let Some(private) = own_private(ns_state, env, &candidate) {
            return Some(private);
        }
        // `export Foo (x)` inside this namespace aliases `prefix.x` —
        // Lean's `resolveGlobalName` consults `getAliases` at every prefix
        // step, as the term elaborator does (`elab_core.rs`).
        if let Some(target) = unique_file_alias(ns_state, &candidate) {
            if env.get_const(target).is_some() {
                return Some(target.clone());
            }
        }
        // The IMPORTED half of the same table. `NamespaceState` only ever
        // holds THIS file's `export`s; a `Lean.aliasExtension` row decoded
        // from an `.olean` lands in the ENVIRONMENT's alias table instead
        // (`Environment::register_export_alias`). Both are aliases and Lean
        // reads them from one `getAliases` call, so both belong at every
        // prefix step.
        if let Some(target) = imported_alias_target(&candidate, ns_state, env) {
            return Some(target);
        }
        prefix = clean_parser::SurfaceName::from_name(prefix)
            .parent()
            .into_name();
    }

    for open_ns in ns_state.open_namespaces() {
        if let Some(candidate) = qualify_name(open_ns, name.name()) {
            if env.get_const(&candidate).is_some() {
                return Some(candidate);
            }
            if let Some(private) = own_private(ns_state, env, &candidate) {
                return Some(private);
            }
        }
    }

    if env.get_const(name.name()).is_some() {
        return Some(name.name().clone());
    }
    if let Some(private) = own_private(ns_state, env, name.name()) {
        return Some(private);
    }

    // A root-level alias (`export Classical (not_forall)` at the top level):
    // `rw [not_forall]` resolved nothing before (`forall_or_exists_not`,
    // measured 2026-09-12).
    if let Some(target) = unique_file_alias(ns_state, name.name()) {
        if env.get_const(target).is_some() {
            return Some(target.clone());
        }
    }

    // The IMPORTED half of the root-level rule, and the one that was missing
    // entirely. Until now the ONLY reader of the environment's decoded alias
    // table in the whole elaborator was the TERM path
    // (`infer/elab_core.rs`, step 2c); this resolver — which every TACTIC name
    // goes through (`tactic::core::resolve_global_name`, and through it
    // `simp`'s `resolve_extra_lemma_name`, `rw`, `unfold`) — consulted only
    // `NamespaceState`. So a lemma named through an imported alias resolved to
    // NOTHING and was dropped with no diagnostic: measured on
    // `Mathlib/Order/Basic.lean`'s `compl_lt`/`compl_le`/`compl_gt`/`compl_ge`,
    // where `compl` reaches the file through `export Compl (compl)` in
    // `Mathlib/Order/Notation.lean`, `simp [compl]` left the goal BYTE-
    // IDENTICAL to a bare `simp`, while the qualified `simp [Compl.compl]`
    // unfolded. The asymmetry is what made it silent: the statement
    // elaborates, because the term path does consult the table.
    //
    // PRECEDENCE, and the one place this deliberately differs from the term
    // path: `elab_core.rs` consults the imported table one step EARLIER, ahead
    // of the root-level constant; here it is consulted LAST, after every
    // `env.get_const` lookup above. AT THIS STAGE an alias may therefore only
    // make a name that resolved to NOTHING resolve. Lean folds constants and
    // aliases into ONE candidate set per stage and reports a collision as
    // `Ambiguous term` (ground-truthed against the pinned v4.30.0-rc2), so
    // NEITHER ordering is Lean-exact for a genuine collision; keeping the
    // constant is the narrow side of that divergence.
    //
    // THAT READING IS PER-STAGE AND DOES NOT EXTEND TO THE FUNCTION. The
    // prefix walk above consults the imported table BEFORE this root lookup is
    // ever reached, so an imported alias at a namespace prefix DOES retarget a
    // short name that used to fall through to a root constant — which is
    // Lean's own rule, not a side effect: with `theorem Foo.bar` , a root
    // `theorem bar` and `export Foo (bar)` inside `namespace N`, the pinned
    // v4.30.0-rc2 resolves `bar` inside `N` to `Foo.bar`. Pinned by
    // `tests/simp_proj_eta_adversarial_e2e.rs`,
    // `test_imported_alias_at_a_namespace_prefix_outranks_a_root_constant`,
    // with its no-alias control beside it.
    // …and the same alias arriving from an IMPORTED module.
    if let Some(target) = imported_alias_target(name.name(), ns_state, env) {
        return Some(target);
    }

    // Lean's `resolveOpenDecls` for an explicit open whose short name is a
    // proper prefix of the written one: after `open Foo (Bar)`, `Bar.a` is
    // `Foo.Bar.a`. Last, like the aliases above, and only when it names ONE
    // declaration: this first-match resolver must not pick among several.
    let prefixed: Vec<Name> = ns_state
        .explicit_open_prefix_targets(name.name())
        .into_iter()
        .filter(|target| env.get_const(target).is_some())
        .collect();
    if let [only] = prefixed.as_slice() {
        return Some(only.clone());
    }

    None
}

/// Lean's private step (`Lean/ResolveName.lean`): THIS module's private
/// declaration whose user-facing name is `candidate`, when the driver named
/// the module and the environment holds it. Another module's private name is
/// never built, so it is unreachable from here (G21: `rw [helper2]` and `simp
/// only [helper2]` reached a sibling's private theorem by its plain name).
pub(crate) fn own_private(
    ns_state: &NamespaceState,
    env: &Environment,
    candidate: &Name,
) -> Option<Name> {
    let private = ns_state.private_name(candidate)?;
    env.get_const(&private).is_some().then_some(private)
}

/// This file's alias `short` when it has one target: two opens or aliases
/// giving it different targets are ambiguous to Lean
/// ([`NamespaceState::resolve_all`]), and this first-match resolver must not
/// pick one of them.
fn unique_file_alias<'s>(ns_state: &'s NamespaceState, short: &Name) -> Option<&'s Name> {
    match ns_state.resolve_all(short).as_slice() {
        [only] => Some(*only),
        _ => None,
    }
}

/// The target of `alias` when it has exactly one (Lean's `getAliases` then
/// names one declaration); `None` when it has none or several — several
/// targets are ambiguous to Lean, and this first-match resolver must not
/// pick one of them.
fn unique_export_alias<'e>(env: &'e Environment, alias: &Name) -> Option<&'e Name> {
    let targets = env.export_alias_targets(alias);
    match targets.as_slice() {
        [only] => Some(*only),
        _ => None,
    }
}

/// How [`resolve_global_const_no_overload`] failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum GlobalConstResolution {
    /// No constant has the name in this scope.
    Unknown,
    /// Several constants have it at the same resolution stage; Lean refuses
    /// the command with `ambiguous identifier`.
    Ambiguous(Vec<Name>),
}

/// Resolve a GLOBAL CONSTANT the way Lean's `realizeGlobalConstNoOverload`
/// does — the resolution of an `attribute [..] ident` target — in THIS
/// module's own scope.
///
/// SIBLING-IMPORT LEAK (round-24 verification of ff6c33c2c). The attribute
/// command used to try the name as written at the ROOT first, and only then
/// the namespace/`open` forms. So inside `namespace N`, or after `open N`,
/// `attribute [instance] c` bound P's root `c` whenever a module P that
/// defines one happened to be in the environment — even when the module did
/// not import P — while Lean binds `N.c` (inside `namespace N`) or refuses
/// the command (`ambiguous identifier '`c', possible interpretations: [N.c,
/// c]`, measured on Lean 4.8.0 with both in scope after `open N`).
///
/// The stages are Lean 4.8.0's `resolveGlobalName` (`Lean/ResolveName.lean`):
/// 1. `_root_`-prefixed names resolve only at the root.
/// 2. The current namespace and each enclosing one, innermost first; the
///    first prefix with a match wins (Lean 4.8.0 binds `A.B.c` over `A.c`
///    inside `namespace A.B`).
/// 3. A dotted name that exists as written (`resolveExact`).
/// 4. Otherwise the root name, every `open` namespace and every alias are
///    collected TOGETHER, and more than one distinct constant is ambiguous.
///
/// VISIBILITY (round-25 verification of 3ee5ff78e). Two of Lean's filters
/// were missing, and each let the attribute bind a constant Lean never binds:
/// * `protected`: an ATOMIC name never reaches a protected declaration
///    through a namespace prefix, a simple `open` or an alias
///    (`resolveQualifiedName` / `getAliases (skipProtected := id.isAtomic)`).
///    Inside `namespace N` with a root `c : C := ⟨2⟩` and `protected def
///    N.c : C := ⟨3⟩`, `attribute [instance] c` bound `N.c`, and
///    `theorem m : C.v = 3 := rfl` passed where Lean binds the root `c` and
///    rejects it.
/// * `private`: another module's private declaration is unreachable (Lean
///    mangles it with its module). `foreign_private` is that set
///    (`FileContext::foreign_private_decls`); `attribute [instance] c` in M
///    bound P's `private def c`, which Lean reports as `unknown constant`.
pub(crate) fn resolve_global_const_no_overload(
    name: &clean_parser::SurfaceName,
    ns_state: &NamespaceState,
    env: &Environment,
    foreign_private: &std::collections::HashSet<Name>,
) -> Result<Name, GlobalConstResolution> {
    if name.is_anonymous() || name.is_relative_constructor() {
        return Err(GlobalConstResolution::Unknown);
    }
    let exists = |candidate: &Name| {
        env.get_const(candidate).is_some() && !foreign_private.contains(candidate)
    };
    // Lean's private step: this module's private `candidate`, where
    // `candidate` itself names nothing.
    let private_of = |candidate: &Name| {
        if exists(candidate) {
            None
        } else {
            own_private(ns_state, env, candidate)
        }
    };
    let normalized = name.qualify_under(&clean_parser::SurfaceName::default());
    if normalized.name() != name.name() {
        if exists(normalized.name()) {
            return Ok(normalized.into_name());
        }
        return private_of(normalized.name()).ok_or(GlobalConstResolution::Unknown);
    }
    let atomic = name.parent().is_anonymous();
    // Reached through a namespace prefix, a simple `open` or an export alias:
    // Lean skips a protected declaration there when the name is atomic.
    let reachable_qualified =
        |candidate: &Name| exists(candidate) && !(atomic && env.is_protected(candidate));

    let mut prefix = ns_state.current_namespace().clone();
    while !prefix.is_anon() {
        let candidate = clean_parser::SurfaceName::from_name(prefix.clone())
            .append(name)
            .into_name();
        let mut found = Vec::new();
        if reachable_qualified(&candidate) {
            found.push(candidate.clone());
        } else if let Some(private) = private_of(&candidate) {
            found.push(private);
        }
        // This file's `export`s inside the namespace (an explicit alias,
        // which may name a protected declaration) and the imported
        // `Lean.aliasExtension` rows (skipped when protected, as
        // `getAliases` does for an atomic name).
        for target in ns_state.resolve_all(&candidate) {
            if exists(target) && !found.contains(target) {
                found.push(target.clone());
            }
        }
        for target in env.export_alias_targets(&candidate) {
            if reachable_qualified(target) && !found.contains(target) {
                found.push(target.clone());
            }
        }
        match found.len() {
            0 => {}
            1 => return Ok(found.remove(0)),
            _ => return Err(GlobalConstResolution::Ambiguous(found)),
        }
        prefix = clean_parser::SurfaceName::from_name(prefix)
            .parent()
            .into_name();
    }

    // `resolveExact`: a dotted name that exists as written wins outright.
    if !atomic && exists(name.name()) {
        return Ok(name.name().clone());
    }
    if !atomic {
        if let Some(private) = private_of(name.name()) {
            return Ok(private);
        }
    }

    let mut found: Vec<Name> = Vec::new();
    let push = |candidate: &Name, found: &mut Vec<Name>| {
        if !found.contains(candidate) {
            found.push(candidate.clone());
        }
    };
    if let Some(private) = private_of(name.name()) {
        push(&private, &mut found);
    }
    if exists(name.name()) {
        push(name.name(), &mut found);
    }
    for (open_ns, hidden) in ns_state.open_namespaces_with_hidden() {
        if hidden.contains(name.name()) {
            continue;
        }
        if let Some(candidate) = qualify_name(open_ns, name.name()) {
            if reachable_qualified(&candidate) {
                push(&candidate, &mut found);
            } else if let Some(private) = private_of(&candidate) {
                push(&private, &mut found);
            }
            // Lean's `resolveQualifiedName` also takes the aliases of
            // `open_ns ++ name` (an `export` made inside that namespace).
            for target in ns_state.resolve_all(&candidate) {
                if reachable_qualified(target) {
                    push(target, &mut found);
                }
            }
            for target in env.export_alias_targets(&candidate) {
                if reachable_qualified(target) {
                    push(target, &mut found);
                }
            }
        }
    }
    // The file's alias table: `open N (x)` / `open N renaming` (Lean's
    // `OpenDecl.explicit`, which reaches a protected declaration) and the
    // simple-`open` snapshot, which `namespace_open.rs` already built without
    // protected names.
    for target in ns_state.resolve_all(name.name()) {
        if exists(target) {
            push(target, &mut found);
        }
    }
    for target in env.export_alias_targets(name.name()) {
        if reachable_qualified(target) {
            push(target, &mut found);
        }
    }
    match found.len() {
        0 => Err(GlobalConstResolution::Unknown),
        1 => Ok(found.remove(0)),
        _ => Err(GlobalConstResolution::Ambiguous(found)),
    }
}

/// An `export` alias decoded from an imported module's `Lean.aliasExtension`
/// (`Environment::get_export_alias`, filled by
/// `clean_olean::import::load_register`).
///
/// Lean keeps ONE alias table: `aliasExtension` (`Lean/ResolveName.lean:68`) is
/// a `SimplePersistentEnvExtension`, so an `export` persists into the `.olean`
/// and an importing module reads it back exactly as the declaring module saw
/// it. `getAliases` (:85) is the single accessor and `resolveGlobalName` (:194)
/// consults it at :211 for EVERY identifier — so `simp only [not_imp]`,
/// `rw [not_imp]` and the term `not_imp` all resolve through the same lookup.
///
/// Clean keeps two: the in-file table on `NamespaceState`, which this function's
/// callers already consult, and this imported one, which until now only the TERM
/// elaborator read (`ElabCtx::resolve_ident`, `elab_core.rs`). Every name-based
/// TACTIC — `simp`, `rw`, `cases`/`induction` registration — routes through
/// `resolve_identifier` and so could not see it: `not_forall` reaches
/// `Mathlib/Logic/Function/Basic.lean` only through `export Classical
/// (not_forall)` at `Mathlib/Logic/Basic.lean:492`, an imported module, and
/// `simp only [Injective, not_forall, exists_prop]` silently DROPPED that lemma
/// (`Function.not_injective_iff`).
///
/// The accessibility gate is the term path's: `elab_core.rs` gates its alias hit
/// on `is_const_accessible`, and without the same gate here a `private` target
/// would become reachable from a tactic that could not name it before.
fn imported_alias_target(
    alias: &Name,
    ns_state: &NamespaceState,
    env: &Environment,
) -> Option<Name> {
    // Several targets are ambiguous to Lean, and this first-match resolver
    // must not pick one of them (`unique_export_alias`).
    let target = unique_export_alias(env, alias)?;
    // An alias whose target no longer exists mints nothing.
    env.get_const(target)?;
    if !env.is_private(target) {
        return Some(target.clone());
    }
    let target_ns = crate::namespace::parent_name(target);
    let visible = if target_ns.is_anon() {
        ns_state.current_namespace().is_anon()
    } else {
        crate::namespace::name_has_prefix(ns_state.current_namespace(), &target_ns)
    };
    visible.then(|| target.clone())
}

#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn get_completions(
    prefix: &str,
    ns_state: &NamespaceState,
    env: &Environment,
) -> Vec<Name> {
    let mut matches = BTreeSet::new();

    collect_completions(ns_state.current_namespace(), prefix, env, &mut matches);

    for open_ns in ns_state.open_namespaces() {
        collect_completions(open_ns, prefix, env, &mut matches);
    }

    matches.into_iter().collect()
}

fn qualify_name(namespace: &Name, name: &Name) -> Option<Name> {
    if namespace.is_anon() || name.is_anon() {
        return None;
    }

    Some(
        clean_parser::SurfaceName::from_name(namespace.clone())
            .append(&clean_parser::SurfaceName::from_name(name.clone()))
            .into_name(),
    )
}

// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
fn collect_completions(
    namespace: &Name,
    prefix: &str,
    env: &Environment,
    matches: &mut BTreeSet<Name>,
) {
    let search_prefix = completion_search_prefix(namespace, prefix);

    for constant in env.constants() {
        if constant.name.is_anon() {
            continue;
        }

        if constant.name.to_string().starts_with(&search_prefix) {
            matches.insert(constant.name.clone());
        }
    }
}

// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
fn completion_search_prefix(namespace: &Name, prefix: &str) -> String {
    if namespace.is_anon() {
        prefix.to_string()
    } else if prefix.is_empty() {
        format!("{namespace}.")
    } else {
        format!("{namespace}.{prefix}")
    }
}

/// Is `qualified` one of the DERIVED projections Clean materializes for a
/// structure's INHERITED fields — a constant Lean 4 does not declare?
///
/// For `structure C extends P`, `elab_structure::build_inherited_projections`
/// registers `C.f := fun {params} (self : C params) => P.f … (C.toP … self)`
/// for every field `f` projectable on `P`. Lean 4 builds that composition
/// ON THE FLY at each use site (`mkBaseProjections`, `src/Lean/Elab/App.lean`)
/// and adds NO constant: measured against the real `Init` oleans (93,172
/// constants), `Monad.toApplicative` exists while `Monad.pure` and
/// `Applicative.pure` do not.
///
/// The difference is not cosmetic. A constant named `C.f` joins the
/// current-namespace-outward candidate set, so inside `namespace C` a bare `f`
/// resolves to it instead of the root/exported `f` the author wrote — and
/// because the derived projection takes an EXPLICIT `self` the user never
/// supplied, the term is left under-applied with a `Pi` type where the field
/// type was expected. That is the SRCELAB "rigid head clash" cluster: in
/// `Mathlib/Logic/Unique.lean`, `Unique extends Inhabited α` grows
/// `Unique.default : {α} → (self : Unique α) → α`, so `theorem eq_default
/// (a : α) : a = default` inside `namespace Unique` reports
/// `Type mismatch: expected FVar(FVarId(0)), got cannot unify expressions of
/// different shape: Discriminant(6) vs Discriminant(1)` — `Pi` vs `FVar`.
///
/// Recognized structurally rather than by a registry flag so the same verdict
/// holds for any environment that carries the shape, and conservatively: every
/// clause must hold, so a genuine declaration that happens to live in a
/// structure's namespace (`Unique.eq_default`) is never mistaken for one.
///
/// 1. the owner is a structure with recorded `extends` parents;
/// 2. the field is NOT one of the owner's own constructor fields (a direct
///    projection IS a real Lean declaration and must keep resolving);
/// 3. the constant's body is `<anything> (C.toParent … self)`, i.e. its
///    argument's spine head is one of the owner's own `toParent` projections.
#[must_use]
pub(crate) fn is_generated_inherited_projection(env: &Environment, qualified: &Name) -> bool {
    let owner = clean_parser::SurfaceName::from_name(qualified.clone())
        .parent()
        .into_name();
    if owner.is_anon() {
        return false;
    }
    let Some(parents) = env.get_structure_parents(&owner) else {
        return false;
    };
    let field = clean_parser::SurfaceName::from_name(qualified.clone())
        .last_component()
        .into_name();
    if env
        .get_structure_field_names(&owner)
        .is_some_and(|fields| fields.contains(&field))
    {
        return false;
    }
    let Some(body) = env
        .get_const(qualified)
        .and_then(|info| info.value.as_ref())
    else {
        return false;
    };
    let mut e = body;
    while let ExprKind::Lam(_, _, inner) | ExprKind::MData(_, inner) = e.kind() {
        e = inner;
    }
    let ExprKind::App(_, subobject_arg) = e.kind() else {
        return false;
    };
    let ExprKind::Const(inner_head, _) = subobject_arg.get_app_fn().kind() else {
        return false;
    };
    parents.iter().any(|(to_field, _)| {
        clean_parser::SurfaceName::from_name(owner.clone())
            .append(&clean_parser::SurfaceName::from_name(to_field.clone()))
            .into_name()
            == *inner_head
    })
}

/// Depth bound for the subobject walk. A structure's `extends` chain is a DAG
/// whose depth is tiny in practice (Lean's deepest core chain is under 10); the
/// bound only stops a cycle introduced by corrupt metadata from looping.
const SUBOBJECT_WALK_MAX_DEPTH: usize = 32;

/// Compose the kernel projection chain that reads `field` off a value of
/// structure `owner`, descending through `extends` parent SUBOBJECTS — Lean's
/// `mkBaseProjections` (`src/Lean/Elab/App.lean`), built ON THE FLY exactly as
/// Lean builds it, with NO constant of its own.
///
/// `receiver` must already be a value whose type's head is `owner` fully
/// applied (the same precondition the own-field arm of `elab_proj` has, since
/// it is reached from `resolve_projection_target`).
///
/// Returns `Proj(P, i, … Proj(owner, j, receiver) …)`: an own field of `owner`
/// is one `Proj`; an inherited field is the parent's chain wrapped around the
/// `Proj` that reads the `toParent` subobject slot. Multiple parents are tried
/// in constructor order, so a genuine DIAMOND resolves to the first parent that
/// carries the field — the same first-parent-wins rule
/// `elab_structure::build_inherited_projections` applies when it materializes
/// the same composition as a constant.
///
/// SOUNDNESS: this only NAMES a projection target. Every `Proj` it emits is
/// re-checked by the kernel (`infer_type` rejects an index that is not a field
/// of the projected structure, and rejects a receiver of the wrong type), so a
/// wrong walk fails closed rather than admitting a term.
///
/// Returns `None` when the field is not reachable — including for a structure
/// with no recorded `extends` metadata, which is every `.olean`-IMPORTED
/// structure today (`register_structure_parents` has exactly one caller,
/// `crate::register`, on the source-elaboration path). Imported structures are
/// therefore untouched by this walk, which is why it cannot change any verdict
/// on the import lane.
#[must_use]
pub(crate) fn compose_subobject_projection(
    env: &Environment,
    owner: &Name,
    field: &Name,
    receiver: Expr,
    depth: usize,
) -> Option<Expr> {
    if depth >= SUBOBJECT_WALK_MAX_DEPTH {
        return None;
    }
    if let Some(idx) = env.get_structure_field_index(owner, field) {
        return Some(Expr::proj(owner.clone(), idx, receiver));
    }
    // `to_vec` releases the borrow on `env` before the recursive call.
    let parents = env.get_structure_parents(owner)?.to_vec();
    for (to_field, parent_name) in parents {
        let Some(to_idx) = env.get_structure_field_index(owner, &to_field) else {
            continue;
        };
        let parent_receiver = Expr::proj(owner.clone(), to_idx, receiver.clone());
        if let Some(chain) =
            compose_subobject_projection(env, &parent_name, field, parent_receiver, depth + 1)
        {
            return Some(chain);
        }
    }
    None
}

/// The `toParent` subobject field of `owner` through which `field` is reached,
/// or `None` when `field` is an own field / unreachable.
///
/// Same walk as [`compose_subobject_projection`], but returning only the FIRST
/// hop — what a structure-UPDATE rewrite needs (`{ c with inheritedField := v }`
/// ⇝ `{ c with toParent := { c.toParent with inheritedField := v } }`).
#[must_use]
pub(crate) fn inherited_field_subobject_hop(
    env: &Environment,
    owner: &Name,
    field: &Name,
) -> Option<Name> {
    if env.get_structure_field_index(owner, field).is_some() {
        return None;
    }
    let parents = env.get_structure_parents(owner)?.to_vec();
    for (to_field, parent_name) in parents {
        if structure_reaches_field(env, &parent_name, field, 0) {
            return Some(to_field);
        }
    }
    None
}

/// Whether `field` is projectable on `owner`, directly or through a subobject.
#[must_use]
fn structure_reaches_field(env: &Environment, owner: &Name, field: &Name, depth: usize) -> bool {
    if depth >= SUBOBJECT_WALK_MAX_DEPTH {
        return false;
    }
    if env.get_structure_field_index(owner, field).is_some() {
        return true;
    }
    let Some(parents) = env.get_structure_parents(owner).map(<[_]>::to_vec) else {
        return false;
    };
    parents
        .iter()
        .any(|(_, parent)| structure_reaches_field(env, parent, field, depth + 1))
}

/// MEASUREMENT INSTRUMENT — `CLEAN_LEAN4_STRUCT_PARITY=1`.
///
/// OFF by default, and every gate in this repo runs with it off, so the shipped
/// behaviour is unchanged: `structure C extends P` still MATERIALIZES a constant
/// `C.f` for each inherited field `f`.
///
/// Turning it on suppresses that registration, putting Clean's environment on
/// the Lean 4 constant set for structures (measured: real Lean 4 `import Lean`
/// has 1,235 inherited (structure, field) pairs and `import Mathlib` has 9,185,
/// and Lean declares a constant for NONE of them; Clean's own `.olean` IMPORT
/// path likewise declares none). It exists so
/// the size of the remaining work can be MEASURED — run the suite with it on and
/// the failures are exactly the sites that still read an inherited projection as
/// a named constant rather than composing it. See
/// `designs/2026-08-24-inherited-projection-parity.md`.
///
/// It is NOT a supported elaboration mode: with it on, bare-name resolution of
/// an inherited field stops finding a candidate (which is what Lean does — it
/// reports `unknown identifier` — but Clean has not yet re-pointed every
/// consumer at [`compose_subobject_projection`]).
#[must_use]
pub(crate) fn lean4_struct_parity_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("CLEAN_LEAN4_STRUCT_PARITY").is_ok_and(|v| v == "1"))
}

/// CENSUS INSTRUMENT — `CLEAN_STRUCT_PARITY_CENSUS=1`.
///
/// Emits one machine-parsable stderr line per derived inherited projection the
/// `structure` elaborator would register:
///
/// ```text
/// [structparity] generated <Owner>.<field>
/// ```
///
/// `grep -c '^\[structparity\] generated '` over a `clean check` run is then the
/// exact size of the environment gap that run opens against Lean 4, which
/// declares no such constant. Zero cost when the variable is unset beyond one
/// cached boolean check.
pub(crate) fn note_generated_inherited_projection(name: &Name) {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if *ON.get_or_init(|| std::env::var("CLEAN_STRUCT_PARITY_CENSUS").is_ok_and(|v| v == "1")) {
        eprintln!("[structparity] generated {name}");
    }
}
