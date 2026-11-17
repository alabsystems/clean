// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Explicit Boxing Pass - Part of #1040
//!
//! Adds explicit box/unbox operations at type boundaries in L5IR.

pub(crate) mod boxed_version;
pub(crate) mod cast;
pub(crate) mod config;
pub(crate) mod context;
#[cfg(feature = "trust-ir-backend")]
pub(crate) mod entry_check;
mod native_signature;
#[cfg(test)]
mod native_signature_tests;
pub(crate) mod visit;

#[cfg(test)]
mod signature_data_tests;
#[cfg(test)]
mod tests;

pub use boxed_version::{
    mk_boxed_version, mk_boxed_version_from_signature, requires_boxed_version,
};
pub use cast::{
    box_args, cast_arg_if_needed, cast_args, cast_var_if_needed, mk_cast, wrap_with_prefix,
};
pub use config::BoxingConfig;
pub(crate) use config::CLOSURE_MAX_ARGS;
pub use context::BoxingContext;
pub use visit::{try_correct_vdecl_type, visit_body};

use crate::compiler_env::CompilerEnv;
use crate::ir::IRDecl;

/// Drop declarations that share a name with an earlier one, keeping the first.
///
/// The boxing pass can synthesize the SAME `_boxed` closure-adapter wrapper from
/// several partial-application sites (e.g. `Nat.ble` captured as a closure in two
/// different functions). Each site records the wrapper independently when
/// `generate_boxed_versions` is off, so the assembled module can carry
/// byte-identical duplicate wrapper decls; emitting both would be a C
/// redefinition. Declaration names are unique by construction otherwise (source
/// decls, per-function `_boxed_const_N` aux decls, per-callee wrappers), so
/// retaining the first occurrence drops only these true duplicates.
fn dedup_decls_by_name(decls: &mut Vec<IRDecl>) {
    let mut seen = std::collections::HashSet::new();
    decls.retain(|d| seen.insert(d.name.clone()));
}

/// Apply the explicit boxing pass to a single declaration.
///
/// Returns the transformed declaration plus any auxiliary declarations generated.
/// This is the single-decl variant for selective boxing.
///
/// # Arguments
///
/// * `decl` - The declaration to transform.
/// * `all_decls` - All declarations in the module (for resolving function calls).
/// * `config` - Configuration controlling boxing behavior.
///
/// # Returns
///
/// A vector containing:
/// 1. Any auxiliary declarations (e.g., boxed constants)
/// 2. The transformed declaration
/// 3. A boxed wrapper version (if `config.generate_boxed_versions` and needed)
pub fn explicit_boxing_decl(
    decl: &IRDecl,
    all_decls: &[IRDecl],
    config: &BoxingConfig,
) -> Vec<IRDecl> {
    let mut result = Vec::with_capacity(3);
    let mut ctx = BoxingContext::new(decl, all_decls, config);
    for (var, ty) in &decl.params {
        ctx.set_var_type(*var, ty.clone());
    }
    let transformed_body = visit_body(&decl.body, &mut ctx);
    result.extend(ctx.take_aux_decls());
    let transformed = IRDecl {
        name: decl.name.clone(),
        params: decl.params.clone(),
        return_type: decl.return_type.clone(),
        body: transformed_body,
    };
    if config.generate_boxed_versions && requires_boxed_version(&transformed) {
        let boxed = mk_boxed_version(&transformed);
        result.push(transformed);
        result.push(boxed);
    } else {
        result.push(transformed);
    }
    dedup_decls_by_name(&mut result);
    result
}

/// Apply the explicit boxing pass to a set of declarations.
///
/// # Arguments
///
/// * `decls` - The declarations to transform.
/// * `config` - Configuration controlling boxing behavior.
///
/// # Requirements
///
/// - `decls` contains well-typed IR with consistent parameter and return types.
/// - Every `IRBody` references only variables declared in its enclosing declaration.
/// - Any `IRExpr::PartialApply` callee appears in `decls` so PAP boxing decisions are complete.
/// - `mangle_boxed_name` will not collide with any existing declaration names.
///
/// # Guarantees
///
/// - The returned declarations are semantically equivalent to `decls`.
/// - All scalar/object mismatches introduced by boxing are resolved via `box`/`unbox`.
/// - Boxed versions are generated (if config enabled) for declarations satisfying `requires_boxed_version`.
/// - Auxiliary declarations created during boxing are included in the output.
pub fn explicit_boxing_with_config(decls: &[IRDecl], config: &BoxingConfig) -> Vec<IRDecl> {
    explicit_boxing_with_optional_kernel_env(decls, None, config)
}

/// Preserve an already scalar native call only when its original kernel
/// declaration confirms the complete ABI. This does not expose a synthetic
/// declaration to partial applications or change their boxed closure ABI.
pub(crate) fn explicit_boxing_with_kernel_env(
    decls: &[IRDecl],
    env: &clean_kernel::Environment,
    config: &BoxingConfig,
) -> Vec<IRDecl> {
    explicit_boxing_with_optional_kernel_env(decls, Some(env), config)
}

fn explicit_boxing_with_optional_kernel_env(
    decls: &[IRDecl],
    env: Option<&clean_kernel::Environment>,
    config: &BoxingConfig,
) -> Vec<IRDecl> {
    let mut result = Vec::with_capacity(decls.len() * 2);
    for decl in decls {
        let mut ctx = BoxingContext::new(decl, decls, config).with_kernel_env(env);
        for (var, ty) in &decl.params {
            ctx.set_var_type(*var, ty.clone());
        }
        let transformed_body = visit_body(&decl.body, &mut ctx);
        result.extend(ctx.take_aux_decls());
        result.push(IRDecl {
            name: decl.name.clone(),
            params: decl.params.clone(),
            return_type: decl.return_type.clone(),
            body: transformed_body,
        });
    }
    if config.generate_boxed_versions {
        let boxed_versions: Vec<_> = result
            .iter()
            .filter(|d| requires_boxed_version(d))
            .map(mk_boxed_version)
            .collect();
        result.extend(boxed_versions);
    }
    dedup_decls_by_name(&mut result);
    result
}

#[cfg(feature = "trust-ir-backend")]
/// [`explicit_boxing_with_config`], resolving call sites against
/// `signatures` as well as `decls` (Trust plan step 3.2).
///
/// `signatures` are signature-only declarations whose bodies are never
/// emitted — a Rust callee (a call to Rust at its carrier ABI) or a native
/// carrier primitive (one machine operation). Resolving against them is what
/// passes a scalar argument UNBOXED and types the result as the scalar it
/// is; an unknown callee would box both. Only `decls` are transformed and
/// returned.
pub(crate) fn explicit_boxing_with_signatures(
    decls: &[IRDecl],
    signatures: &[IRDecl],
    config: &BoxingConfig,
) -> Vec<IRDecl> {
    let lookup: Vec<IRDecl> = decls.iter().chain(signatures).cloned().collect();
    let mut result = Vec::with_capacity(decls.len());
    for decl in decls {
        let mut ctx = BoxingContext::new(decl, &lookup, config);
        for (var, ty) in &decl.params {
            ctx.set_var_type(*var, ty.clone());
        }
        let transformed_body = visit_body(&decl.body, &mut ctx);
        result.extend(ctx.take_aux_decls());
        result.push(IRDecl {
            name: decl.name.clone(),
            params: decl.params.clone(),
            return_type: decl.return_type.clone(),
            body: transformed_body,
        });
    }
    if config.generate_boxed_versions {
        let boxed_versions: Vec<_> = result
            .iter()
            .filter(|d| requires_boxed_version(d))
            .map(mk_boxed_version)
            .collect();
        result.extend(boxed_versions);
    }
    dedup_decls_by_name(&mut result);
    result
}

/// Apply the explicit boxing pass using a unified `CompilerEnv`.
///
/// Avoids per-declaration `decl_index` construction by delegating lookup
/// to the shared environment. Semantically identical to
/// `explicit_boxing_with_config`; this variant should be preferred when a
/// `CompilerEnv` is already available. Part of #1970.
///
/// See `explicit_boxing_with_config` for requirements and guarantees.
pub fn explicit_boxing_with_env(
    decls: &[IRDecl],
    env: &CompilerEnv,
    config: &BoxingConfig,
) -> Vec<IRDecl> {
    let mut result = Vec::with_capacity(decls.len() * 2);
    for decl in decls {
        let mut ctx = BoxingContext::new_with_env(decl, decls, env, config);
        for (var, ty) in &decl.params {
            ctx.set_var_type(*var, ty.clone());
        }
        let transformed_body = visit_body(&decl.body, &mut ctx);
        result.extend(ctx.take_aux_decls());
        result.push(IRDecl {
            name: decl.name.clone(),
            params: decl.params.clone(),
            return_type: decl.return_type.clone(),
            body: transformed_body,
        });
    }
    if config.generate_boxed_versions {
        let boxed_versions: Vec<_> = result
            .iter()
            .filter(|d| requires_boxed_version(d))
            .map(mk_boxed_version)
            .collect();
        result.extend(boxed_versions);
    }
    dedup_decls_by_name(&mut result);
    result
}

/// Apply the explicit boxing pass to a set of declarations with default config.
///
/// This is the legacy API for backward compatibility. Prefer `explicit_boxing_with_config`
/// for explicit control over boxing behavior.
///
/// See `explicit_boxing_with_config` for requirements and guarantees.
#[deprecated(
    since = "0.2.0",
    note = "Use explicit_boxing_with_config(&decls, &BoxingConfig::new()) instead"
)]
pub fn explicit_boxing(decls: Vec<IRDecl>) -> Vec<IRDecl> {
    explicit_boxing_with_config(&decls, &BoxingConfig::new())
}
