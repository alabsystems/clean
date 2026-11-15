// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What the native path does with a reached `@[extern]` or `@[implemented_by]`
//! declaration (`compiler-implemented-by-and-extern-fail-closed`,
//! docs/plans/LEAN4_UPSTREAM_DELTA_2026-10-16.md).
//!
//! Lean compiles neither body:
//!
//! * `@[implemented_by f] def g` — "the function is not compiled ... Calls to
//!   this function are replaced by calls to its implementation"
//!   (`src/Lean/Compiler/ImplementedByAttr.lean`, v4.30.0-rc2). Pinned Lean
//!   prints `2` for the battery row `attr_implemented_by`; compiling `g`'s
//!   logical body printed `3` at exit 0. The native path now compiles `f` in
//!   `g`'s place: `to_lcnf` rewrites every reference
//!   (`runtime_const_name`), and the dependency walk follows the same edge
//!   ([`FfiRoute::Redirect`]) so `g`'s body is never lowered.
//! * `@[extern "sym"] def g := body` — Lean calls `sym` and never the body;
//!   `lean --run` fails with "Could not find native implementation of external
//!   declaration" when there is no `sym`. Clean binds no user extern symbol,
//!   so a reached `@[extern]` declaration with a body is refused by name
//!   (`native-extern-body`) — never compiled from its body.
//!
//! A chain `slowest → middle → fastest` runs its END, as in Lean (battery row
//! `attr_implemented_by_chain`): each link is redirected in turn and none is
//! lowered. What the native path cannot substitute faithfully is refused by
//! name (`native-implemented-by`): the declaration is the root itself, or the
//! end of its chain is absent or `unsafe` (Lean runs an `unsafe` end; Clean
//! compiles no unsafe code). A bodiless `@[extern]` declaration is refused too
//! (`native-extern`): Lean calls its symbol, and Clean binds none.
//!
//! What the build promises ([`CodeMeaning`]) decides two more things:
//!
//! * `clean extract` promises the KERNEL value ([`CodeMeaning::KernelValue`]):
//!   no reference is substituted (`to_lcnf` lowers each constant's own
//!   value, `clean_compiler::constant_to_decl_with_meaning`), so a reached
//!   `@[implemented_by]` declaration is compiled from its logical body like
//!   any other constant, a root that carries one is too, and the order
//!   refusal below does not apply (`docs/DECISIONS.md` R149). Until R149 such
//!   a closure was refused (`extract-implemented-by`), and the order refusal
//!   was taken too: over-refusals.
//! * An `attribute [implemented_by f] d` command added AFTER code that
//!   reaches `d` (the environment's order record,
//!   `clean_compiler::implemented_by_order`): pinned Lean compiled that code
//!   before the binding, and which body it runs then is Lean's inliner's
//!   choice, which Clean does not model. Every root built from such an
//!   environment is refused (`native-implemented-by-order`) under
//!   [`CodeMeaning::LeanCompiled`]. The Rust ABI and every public lowering
//!   entry of clean-compiler (`constant_to_decl`, which Trust's island lane
//!   calls, `expr_to_code`, `compile_lcnf_decls`) refuse the same
//!   environments (`implemented-by-order`); this check comes first, so its
//!   tag is the one a native build reports.
//!
//! An `@[extern]` declaration is refused under both meanings.
//!
//! This audit sees what SOURCE elaboration registered and, since R149, what
//! `.olean` import registered: the loader reads `Lean.Compiler.implementedByAttr`
//! and `Lean.externAttr` rows into the same registries
//! (`clean_olean`'s `register_real_compiler_attr_entries`) for every
//! declaration the importing module itself added. A declaration the builtin
//! prelude holds keeps the prelude's meaning (the loader keeps the first
//! declaration of a name), and a runtime primitive the dependency walk keeps
//! as a shim (`is_primitive_denylisted`) is skipped before this audit routes
//! it. The `attribute [extern]` and `attribute [implemented_by]` commands
//! cannot bind a prelude constant: elaboration refuses either on one (Lean's
//! imported-module check, `clean_elab`'s `declared_here`).

use clean_compiler::ffi_bridge::ImplementedByMap;
use clean_compiler::CompiledBefore;
use clean_kernel::{ConstantInfo, Environment, Name};

/// The meaning a build promises for the code it compiles: clean-compiler's
/// own, which `to_lcnf` and the pipeline take too.
pub(crate) use clean_compiler::CodeMeaning;

/// How the dependency walk treats one reached constant.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum FfiRoute {
    /// Neither attribute applies: the ordinary #14 boundary decides.
    Ordinary,
    /// `@[implemented_by target]`: walk (and compile) `target` instead; the
    /// declaration's own body is never lowered.
    Redirect(Name),
}

/// A reached declaration the native path refuses because Lean would not run
/// its body.
#[derive(Debug, thiserror::Error)]
pub(crate) enum UncompilableFfi {
    /// A source `@[extern]` declaration with a body.
    #[error(
        "native build refuses `{name}` (reached from `{root}`): it is @[extern \"{symbol}\"] \
         with a body. Lean never compiles that body -- it calls the C symbol `{symbol}`, and \
         `lean --run` fails when there is none -- and Clean binds no user extern symbol, so \
         this build is refused (native-extern-body)."
    )]
    ExternWithBody {
        /// The refused declaration.
        name: String,
        /// The declaration being built.
        root: String,
        /// The `@[extern]` symbol.
        symbol: String,
    },
    /// The declaration being built is itself `@[implemented_by]`.
    #[error(
        "native build refuses `{name}`: it is @[implemented_by {target}], and Lean never \
         compiles such a declaration -- every call runs `{target}` -- so there is no code of \
         its own to emit; build a caller instead (native-implemented-by)."
    )]
    ImplementedByRoot {
        /// The refused declaration.
        name: String,
        /// Its implementation.
        target: String,
    },
    /// An `@[implemented_by]` pair the native path cannot substitute.
    #[error(
        "native build refuses `{name}` (reached from `{root}`): it is @[implemented_by \
         {target}], and {why}, so Lean's implementation cannot run and the logical body must \
         not run in its place (native-implemented-by)."
    )]
    ImplementedByUnsubstitutable {
        /// The refused declaration.
        name: String,
        /// The declaration being built.
        root: String,
        /// Its implementation.
        target: String,
        /// Why it cannot be substituted.
        why: &'static str,
    },
    /// A source `@[extern]` declaration without a body.
    #[error(
        "native build refuses `{name}` (reached from `{root}`): it is @[extern \"{symbol}\"]. \
         Compiled Lean calls the external symbol `{symbol}`, and Clean binds no user extern \
         symbol, so this build is refused (native-extern)."
    )]
    ExternWithoutBody {
        /// The refused declaration.
        name: String,
        /// The declaration being built.
        root: String,
        /// The `@[extern]` symbol.
        symbol: String,
    },
    /// The environment holds code added before an `attribute [implemented_by]`
    /// command that rebinds what it reaches.
    #[error(
        "native build refuses `{root}`: an `attribute [implemented_by]` command rebound \
         {rebound} after code that reaches it was added ({referrers}). Pinned Lean compiled \
         that code before the binding, and which body it runs is decided by Lean's inliner, \
         which Clean does not model, so no declaration of this program is compiled \
         (native-implemented-by-order)."
    )]
    CompiledBeforeBinding {
        /// The declaration being built.
        root: String,
        /// The rebound declarations, rendered.
        rebound: String,
        /// The recorded referrers, rendered.
        referrers: String,
    },
}

/// Most referrers a [`UncompilableFfi::CompiledBeforeBinding`] message names.
const MAX_NAMED_REFERRERS: usize = 8;

/// Refuse every root built from an environment that recorded code added
/// before an `attribute [implemented_by]` command that rebinds what it
/// reaches (module doc). An empty record refuses nothing.
pub(crate) fn refuse_compiled_before_binding(
    root: &Name,
    env: &Environment,
) -> Result<(), UncompilableFfi> {
    let Some(compiled_before) = clean_compiler::implemented_by_order(env) else {
        return Ok(());
    };
    let mut entries: Vec<(&Name, &CompiledBefore)> = compiled_before.iter().collect();
    entries.sort_by_cached_key(|(referrer, _)| referrer.to_string());
    let mut rebound: Vec<String> = entries
        .iter()
        .map(|(_, why)| format!("`{}`", why.rebound))
        .collect();
    rebound.sort();
    rebound.dedup();
    let mut referrers: Vec<String> = entries
        .iter()
        .take(MAX_NAMED_REFERRERS)
        .map(|(referrer, why)| clean_compiler::render_implemented_by_reach(referrer, why))
        .collect();
    if entries.len() > MAX_NAMED_REFERRERS {
        referrers.push(format!("and {} more", entries.len() - MAX_NAMED_REFERRERS));
    }
    Err(UncompilableFfi::CompiledBeforeBinding {
        root: root.to_string(),
        rebound: rebound.join(", "),
        referrers: referrers.join("; "),
    })
}

/// Refuse a ROOT the native path must not compile from its body. Under
/// [`CodeMeaning::KernelValue`] an `@[implemented_by]` root's body is what
/// the build promises, so only `@[extern]` is refused.
pub(crate) fn refuse_ffi_root(
    env: &Environment,
    info: &ConstantInfo,
    meaning: CodeMeaning,
) -> Result<(), UncompilableFfi> {
    if meaning == CodeMeaning::LeanCompiled {
        if let Some(target) = env.get_implemented_by(&info.name) {
            return Err(UncompilableFfi::ImplementedByRoot {
                name: info.name.to_string(),
                target: target.to_string(),
            });
        }
    }
    refuse_extern(env, info, &info.name)
}

/// Route a reached DEPENDENCY: redirect an `@[implemented_by]` declaration to
/// the next link of its chain, refuse a reached `@[extern]` one. Under
/// [`CodeMeaning::KernelValue`] an `@[implemented_by]` declaration is
/// ordinary: its own value is lowered, as every reference to it is
/// (`clean_compiler::constant_to_decl_with_meaning`).
///
/// One hop at a time: the walk pops the target and routes it again, so a
/// chain is followed to its end, no link is ever lowered, and the walk's
/// `seen` set ends a cycle (whose callers' lowering names it,
/// `clean_compiler`'s `implemented-by-cycle`).
pub(crate) fn route_ffi_dep(
    env: &Environment,
    implemented_by: &ImplementedByMap,
    info: &ConstantInfo,
    root: &Name,
    meaning: CodeMeaning,
) -> Result<FfiRoute, UncompilableFfi> {
    if meaning == CodeMeaning::KernelValue {
        refuse_extern(env, info, root)?;
        return Ok(FfiRoute::Ordinary);
    }
    if let Some(target) = implemented_by.resolve(&info.name) {
        // Only the END of a chain runs: an `unsafe` link before it is never
        // compiled, so it is no reason to refuse.
        let why = if env.get_const(target).is_none() {
            Some("the implementation is not in the environment")
        } else if env.is_unsafe(target) && !implemented_by.has_binding(target) {
            Some("the implementation is `unsafe`, and Clean compiles no unsafe code")
        } else {
            None
        };
        return match why {
            Some(why) => Err(UncompilableFfi::ImplementedByUnsubstitutable {
                name: info.name.to_string(),
                root: root.to_string(),
                target: target.to_string(),
                why,
            }),
            None => Ok(FfiRoute::Redirect(target.clone())),
        };
    }
    refuse_extern(env, info, root)?;
    Ok(FfiRoute::Ordinary)
}

/// Refuse a reached `@[extern]` declaration: with a body, Lean never runs the
/// body (`native-extern-body`); without one, Lean calls the symbol, which
/// Clean does not bind (`native-extern`).
fn refuse_extern(
    env: &Environment,
    info: &ConstantInfo,
    root: &Name,
) -> Result<(), UncompilableFfi> {
    let Some(symbol) = env.get_extern(&info.name) else {
        return Ok(());
    };
    let (name, root, symbol) = (info.name.to_string(), root.to_string(), symbol.clone());
    Err(match &info.value {
        Some(_) => UncompilableFfi::ExternWithBody { name, root, symbol },
        None => UncompilableFfi::ExternWithoutBody { name, root, symbol },
    })
}
