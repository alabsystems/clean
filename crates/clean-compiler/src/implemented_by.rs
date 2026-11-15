// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `@[implemented_by f]` in compiled code: a reference to the declaration is
//! compiled as a reference to the constant it RUNS, keeping its universe
//! levels and arguments (pinned Lean v4.30.0-rc2: `applyImplementedBy?` in
//! `Lean/Compiler/LCNF/Simp/SimpValue.lean`, run by the base-phase `simp`).
//!
//! The kernel keeps the declaration's own value, so this changes no kernel
//! verdict; it changes which body runs, exactly where Lean's compiled code
//! differs from the kernel's meaning. The elaborator checked each link the
//! way Lean's `getParam` does (equal universe-parameter counts, structurally
//! equal types at the declaration's universe parameters), so every constant
//! along a chain has the type its call site was elaborated against.
//!
//! Source elaboration registers a binding for its own file, and `.olean`
//! import registers the bindings an imported module carries for its own
//! declarations (`docs/DECISIONS.md` R149); the builtin prelude registers none.
//!
//! The ORDER record ([`clean_kernel::env::CompiledBefore`], kept by the
//! kernel environment because its writers, clean-elab and clean-olean, and
//! this crate, which reads it, meet only there) names the code an
//! `@[implemented_by]` binding came too late for. Every compiled lane reads
//! it from the environment it is handed, whatever driver built it, and while
//! it is not empty every legacy lowering entry refuses ([`refuse_order`]).
//! Explicit [`crate::RuntimeBindingClosure`] entries keep the full context and
//! record while rejecting every order participant their checked closure reaches.

use std::collections::HashSet;

use clean_kernel::env::ConstantInfo;
use clean_kernel::{Environment, Level, Name};

use crate::error::CompilerError;

pub use clean_kernel::env::CompiledBefore;

/// Add `found` (referrer, why) to `env`'s order record.
#[cfg(test)]
pub(crate) fn record_order(env: &mut Environment, found: Vec<(Name, CompiledBefore)>) {
    env.record_compiled_before(found);
}

/// `env`'s order record, `None` when it is empty.
pub(crate) fn order(env: &Environment) -> Option<&std::collections::HashMap<Name, CompiledBefore>> {
    env.compiled_before_record()
}

/// The refusal every legacy lowering entry returns while `env`'s order record
/// is not empty ([`CompilerError::ImplementedByOrder`], naming the least
/// recorded constant by name): `crate::to_lcnf::constant_to_decl`,
/// `crate::to_lcnf::expr_to_code` and the batch pipeline
/// (`crate::pass_manager::compile_lcnf_decls`, under every `compile_lcnf_*`
/// entry). Pinned Lean compiled the recorded code before the binding, and
/// which body it runs then is its inliner's choice, which Clean does not
/// model, so no declaration of the environment is lowered, as the native
/// lanes (`native-implemented-by-order`) and the Rust ABI refuse every root.
/// It is checked at the entries, so Trust's general (recording) lane, which
/// lowers each declaration with `constant_to_decl`, gets it too; Trust's MIR
/// planner, which inlines kernel values and lowers nothing here, does not
/// (`docs/DECISIONS.md` R80 item 4).
///
/// # Errors
///
/// [`CompilerError::ImplementedByOrder`] while the record is not empty.
pub(crate) fn refuse_order(env: &Environment) -> Result<(), CompilerError> {
    let Some(record) = order(env) else {
        return Ok(());
    };
    match record
        .iter()
        .min_by_key(|(referrer, _)| referrer.to_string())
    {
        Some((referrer, why)) => Err(CompilerError::ImplementedByOrder {
            referrer: referrer.clone(),
            rebound: why.rebound.clone(),
            via: why.via.clone(),
        }),
        None => Ok(()),
    }
}

/// How `referrer` reaches `rebound`, as the order refusals print it. A
/// declaration recorded for itself is one whose own code was compiled before
/// its binding and may be copied into callers compiled after it.
pub(crate) fn render_reach(referrer: &Name, rebound: &Name, via: &Name) -> String {
    if referrer == rebound {
        format!("`{rebound}` itself was compiled before the binding")
    } else if via == rebound {
        format!("`{referrer}` names `{rebound}`")
    } else {
        format!("`{referrer}` reaches `{rebound}` through `{via}`")
    }
}

/// The meaning a lowering promises for the code it produces.
///
/// Lean compiles neither body of an `@[implemented_by]` declaration: every
/// reference runs the end of its chain. That is what a build that runs
/// Lean's program compiles ([`CodeMeaning::LeanCompiled`], every lowering
/// entry's default). `clean extract` promises instead the KERNEL value of
/// what it extracts ([`CodeMeaning::KernelValue`]): no reference is
/// substituted, every constant lowers its own logical value, and the
/// environment's order record, which is about what Lean's compiled code
/// runs, does not apply (`docs/DECISIONS.md` R149).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum CodeMeaning {
    /// What compiled Lean runs: a reference to an `@[implemented_by]`
    /// declaration runs the end of its chain ([`runtime_const_name`]).
    #[default]
    LeanCompiled,
    /// The kernel value: every reference lowers to the constant it names.
    KernelValue,
}

/// [`runtime_const_name`] under `meaning`: under
/// [`CodeMeaning::KernelValue`] a reference runs the constant it names.
pub(crate) fn runtime_const_name_for(
    env: &Environment,
    name: &Name,
    meaning: CodeMeaning,
) -> Result<Name, CompilerError> {
    match meaning {
        CodeMeaning::LeanCompiled => runtime_const_name(env, name),
        CodeMeaning::KernelValue => Ok(name.clone()),
    }
}

/// [`refuse_order`] under `meaning`: the order record says which body
/// Lean's compiled code runs, which a kernel-value lowering does not
/// depend on, so under [`CodeMeaning::KernelValue`] nothing is refused.
pub(crate) fn refuse_order_for(
    env: &Environment,
    meaning: CodeMeaning,
) -> Result<(), CompilerError> {
    match meaning {
        CodeMeaning::LeanCompiled => refuse_order(env),
        CodeMeaning::KernelValue => Ok(()),
    }
}

/// The refusal a lowering of what compiled Lean runs returns for the body of
/// `name` when `name` is `@[extern]` ([`CompilerError::ExternWithBody`]):
/// Lean calls the symbol and never the body, and the extern registry holds,
/// since R149, imported bindings as well as source ones. Checked where a body
/// is lowered (`crate::to_lcnf::constant_to_decl_with_meaning`) and where a
/// lowered body is compiled (`crate::pass_manager::compile_lcnf_decls`):
/// before, Trust's island lane, which lowers each declaration with
/// `constant_to_decl`, compiled the body of `@[extern "sym"] def
/// externBody (n : Nat) : Nat := n + 3` and printed `4` where Lean fails
/// ("Could not find native implementation of external declaration"). A
/// reference to such a declaration lowers to a call of it, which links only
/// to a definition of the symbol. Under [`CodeMeaning::KernelValue`] the body
/// is the kernel value, so nothing is refused.
///
/// # Errors
///
/// [`CompilerError::ExternWithBody`] when `name` is `@[extern]` and
/// `meaning` is [`CodeMeaning::LeanCompiled`].
pub(crate) fn refuse_extern_body(
    env: &Environment,
    name: &Name,
    meaning: CodeMeaning,
) -> Result<(), CompilerError> {
    match (meaning, env.get_extern(name)) {
        (CodeMeaning::LeanCompiled, Some(symbol)) => Err(CompilerError::ExternWithBody {
            decl: name.clone(),
            symbol: symbol.clone(),
        }),
        (CodeMeaning::LeanCompiled | CodeMeaning::KernelValue, _) => Ok(()),
    }
}

/// The constant a reference to `name` RUNS: `name` itself when it carries no
/// `@[implemented_by]`, else the END of its chain. Lean's `simp` re-applies
/// the substitution to its own output, so `slowest → middle → fastest` runs
/// `fastest` (measured: battery row `attr_implemented_by_chain` prints `10`).
///
/// # Errors
///
/// - [`CompilerError::ImplementedByMissingTarget`]: a link names a constant
///   the environment does not hold (nothing to run).
/// - [`CompilerError::ImplementedByCycle`]: the chain returns to a constant
///   it already passed. Pinned Lean never finishes compiling a caller
///   (measured: `lean --run` times out), so there is no implementation.
/// - [`CompilerError::ImplementedByUnsafeTarget`]: the END is `unsafe`.
///   Lean runs it; Clean compiles no unsafe code. An `unsafe` link before
///   the end is never run, so it is not refused.
/// - [`CompilerError::ImplementedByTypeMismatch`]: a link's implementation
///   does not have its declaration's type ([`link_types_agree`]).
pub(crate) fn runtime_const_name(env: &Environment, name: &Name) -> Result<Name, CompilerError> {
    let Some(first) = env.get_implemented_by(name) else {
        return Ok(name.clone());
    };
    let mut passed: HashSet<&Name> = HashSet::from([name]);
    let mut from = name;
    let mut current = first;
    loop {
        let Some(target) = env.get_const(current) else {
            return Err(CompilerError::ImplementedByMissingTarget {
                decl: from.clone(),
                target: current.clone(),
            });
        };
        if !env
            .get_const(from)
            .is_some_and(|decl| link_types_agree(decl, target))
        {
            return Err(CompilerError::ImplementedByTypeMismatch {
                decl: from.clone(),
                target: current.clone(),
            });
        }
        if !passed.insert(current) {
            return Err(CompilerError::ImplementedByCycle {
                decl: name.clone(),
                repeated: current.clone(),
            });
        }
        match env.get_implemented_by(current) {
            Some(next) => {
                from = current;
                current = next;
            }
            None if env.is_unsafe(current) => {
                return Err(CompilerError::ImplementedByUnsafeTarget {
                    decl: name.clone(),
                    target: current.clone(),
                });
            }
            None => return Ok(current.clone()),
        }
    }
}

/// `true` iff `target` can implement `decl`: Lean's own check when the
/// attribute is applied (pinned v4.30.0-rc2 `Lean.Compiler.implementedByAttr`:
/// the same number of universe parameters, and `target`'s type, instantiated
/// at `decl`'s parameters, `Expr.eqv` to `decl`'s, which ignores binder
/// annotations). Source elaboration makes the same check
/// (`clean_elab::ffi_extern::validate_implemented_by`); an imported binding
/// was checked by Lean against the declarations Lean held, and its names may
/// resolve to other declarations here (the builtin prelude's), so it is
/// checked again where it is followed.
fn link_types_agree(decl: &ConstantInfo, target: &ConstantInfo) -> bool {
    if decl.level_params.len() != target.level_params.len() {
        return false;
    }
    let levels: Vec<Level> = decl
        .level_params
        .iter()
        .cloned()
        .map(Level::param)
        .collect();
    let target_type = target
        .type_
        .instantiate_level_params_direct(&target.level_params, &levels);
    clean_kernel::env::lean_expr_eqv(&decl.type_, &target_type)
}

/// Whether an optimizer must preserve a lowered call boundary: implemented_by,
/// extern, or a source constant with a csimp replacement. This is conservative
/// across body-specific csimp views and is not a predicate for refusing to
/// compile the original constant as an ABI root.
pub(crate) fn has_compiler_attr(env: &Environment, name: &Name) -> bool {
    env.has_implemented_by(name)
        || env.is_extern(name)
        || clean_kernel::env::csimp::has_replacement(env, name)
}

#[cfg(test)]
#[path = "implemented_by_tests.rs"]
mod tests;
