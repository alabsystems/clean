// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The Rust-ABI driver: kernel declarations → trust-ir at the carrier ABI,
//! with a determinism digest per function (Trust plan step 3.2).

use super::{
    carrier_signature, rust_callee_decl, Carrier, CarrierSignature, RustAbiError, RustCallee,
};
use crate::emit_trust_ir::carrier::emit_carrier_module;
use crate::emit_trust_ir::names::wire_name;
use crate::pass_manager::{compile_lcnf_decls_at_rust_abi, PipelineConfig};
use crate::to_lcnf::constant_to_decl;
use clean_kernel::{Environment, Name};
use std::collections::HashSet;
use trust_ir::proof::ProofDigest;
use trust_ir::ty::Ty;
use trust_ir::value::FuncId;
use trust_ir::{Module, TargetInfo};
use trust_ir_build::validate_module;
use trust_ir_conformance::subset::module_subset_violations;

/// Bumped whenever the Rust-ABI lowering changes what it emits for an
/// unchanged input, so the determinism key moves with it. The crate version
/// alone does not move between the commits of one release line.
const RUST_ABI_LOWERING_REVISION: u32 = 1;

/// One Rust-callable function the core emitted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RustAbiRow {
    /// The kernel declaration.
    pub declaration: Name,
    /// The emitted function's link-time symbol (`Function::name`).
    pub symbol: String,
    /// The emitted function's id in [`RustAbiOutput::module`].
    pub func_id: FuncId,
    /// Its carrier signature, which IS its emitted `FuncTy` (C3).
    pub signature: CarrierSignature,
    /// The determinism digest (C4).
    pub digest: CoreFunctionDigest,
    /// Whether the in-process kernel translation-validation self-check
    /// certified this function's body against its definition. Disclosure
    /// only: no certificate is attached and no grade is claimed; a kernel
    /// REFUSAL is a compile error, never a row.
    pub kernel_tv_self_check: bool,
}

/// The determinism key of one emitted function and the digest it maps to:
/// (environment, declaration, core version, target) → Function
/// (Clean `designs/2026-09-30-clean-trust-unified-vision.md` §2.2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoreFunctionDigest {
    /// SHA-256 of the whole kernel environment's content
    /// (`Environment::content_digest`).
    pub environment: String,
    /// The declaration's own content digest (name, universe parameters, type,
    /// value, kind) — its row in the environment digest.
    pub declaration: String,
    /// The core: crate version and Rust-ABI lowering revision.
    pub core_version: String,
    /// The target triple.
    pub target: String,
    /// SHA-256 over the four fields above, domain-separated.
    pub key: String,
    /// SHA-256 of the emitted Function's executable content: the function
    /// with every other function reduced to its declaration, every claim
    /// channel and the module name removed.
    pub function: String,
}

/// What [`compile_rust_abi`] produced.
#[derive(Clone, Debug)]
pub struct RustAbiOutput {
    /// The module: the roots, their lifted helpers, the Rust callees and the
    /// pinned `Nat` entry points they call. Validated; claim-free; every body
    /// `Ungated`.
    pub module: Module,
    /// One row per root, in root order.
    pub rows: Vec<RustAbiRow>,
    /// Whether a `Nat` handle occurs. trust-ir's lowering-target subset does
    /// not admit handles (trust-ir `bridge.rs`: "runtime-opaque ... outside
    /// the proven subset"), so a handle-bearing module is held to
    /// `validate_module` and its pinned-handle rules only; a module without
    /// one passes the subset gate as every `ExternCalls` module does.
    pub handle_bearing: bool,
}

/// Compile `roots` — Rust-callable Lean declarations of `env` — at the Rust
/// ABI, calling `rust_callees` at their symbols. See the module docs of
/// [`crate::rust_abi`] for C1–C4.
///
/// # Errors
///
/// Every refusal names the declaration and the reason ([`RustAbiError`]): a
/// non-carrier signature, a non-computational root, a name conflict, a root
/// whose compiled code is not its body (`@[implemented_by]`, `@[extern]`, or
/// any root of an environment with a non-empty `implemented_by` ORDER record,
/// [`crate::implemented_by_order`]), a body outside the carrier closure, a
/// module that does not validate, or an emitted signature that is not the
/// carrier signature.
pub fn compile_rust_abi(
    env: &Environment,
    roots: &[Name],
    rust_callees: &[RustCallee],
    pipeline: &PipelineConfig,
    module_name: &str,
    target: &TargetInfo,
) -> Result<RustAbiOutput, RustAbiError> {
    let conflict = |name: &Name, detail: &str| RustAbiError::Conflict {
        name: name.to_string(),
        detail: detail.to_string(),
    };
    // Code an `attribute [implemented_by]` command came too late for runs
    // whatever Lean's inliner left it (`crate::implemented_by::order`), as
    // the native lanes refuse it: no root of such an environment compiles.
    let late_binding = crate::implemented_by::order(env)
        .and_then(|record| {
            record
                .iter()
                .min_by_key(|(referrer, _)| referrer.to_string())
        })
        .map(|(referrer, why)| {
            let reach = crate::implemented_by::render_reach(referrer, &why.rebound, &why.via);
            format!(
                "is in an environment where an `attribute [implemented_by]` command rebound \
                 `{}` after code that reaches it was added ({reach}). Pinned Lean compiled that \
                 code before the binding, and which body it runs is decided by Lean's inliner, \
                 which Clean does not model, so no root of this environment is compiled \
                 (implemented-by-order). Options: write the attribute on the declaration, or \
                 before every use of it.",
                why.rebound
            )
        });
    let mut seen: HashSet<&Name> = HashSet::new();
    let mut signatures = Vec::with_capacity(roots.len());
    let mut batch = Vec::with_capacity(roots.len() + rust_callees.len());
    for root in roots {
        if !seen.insert(root) {
            return Err(conflict(
                root,
                "is named twice in the batch. Options: name it once.",
            ));
        }
        if let Some(detail) = &late_binding {
            return Err(conflict(root, detail));
        }
        if crate::carrier_prims::carrier_prim(root, true).is_some() {
            return Err(conflict(
                root,
                "is a native carrier primitive; it is one machine operation, never compiled \
                 from its Lean body. Options: call it from a root instead.",
            ));
        }
        // csimp rewrites references in other bodies; it does not replace
        // this root's own body. Only these attributes route the root itself.
        if env.has_implemented_by(root) || env.is_extern(root) {
            return Err(conflict(
                root,
                "carries `@[implemented_by]` or `@[extern]`: compiled Lean never runs its own \
                 body, and the Rust ABI compiles a root from its body. Options: call the \
                 implementation from Rust instead.",
            ));
        }
        signatures.push(carrier_signature(env, root)?);
        let info = env
            .get_const(root)
            .ok_or_else(|| RustAbiError::UnknownConstant {
                name: root.to_string(),
            })?;
        let decl = constant_to_decl(env, info)
            .map_err(|e| RustAbiError::Refused {
                detail: format!("`{root}` does not lower to L5CNF: {e}"),
            })?
            .ok_or_else(|| RustAbiError::NotComputational {
                name: root.to_string(),
            })?;
        batch.push(decl);
    }
    let mut symbols: HashSet<String> = roots.iter().map(wire_name).collect();
    for callee in rust_callees {
        if !seen.insert(&callee.constant) {
            return Err(conflict(
                &callee.constant,
                "is both a root and a Rust callee, or a Rust callee twice. Options: declare \
                 each Rust function once, under a name no island declaration uses.",
            ));
        }
        if !symbols.insert(callee.symbol.clone()) {
            return Err(conflict(
                &callee.constant,
                "has a link symbol another function of the module already has. Options: pass \
                 the Rust function's own mangled symbol.",
            ));
        }
        batch.push(rust_callee_decl(env, callee)?);
    }

    let refused = |detail: String| RustAbiError::Refused { detail };
    let artifacts = compile_lcnf_decls_at_rust_abi(&batch, env, pipeline, true)
        .map_err(|e| refused(e.to_string()))?;
    let carrier = emit_carrier_module(
        &artifacts.boxed_ir_decls,
        &artifacts.rust_externs,
        artifacts.nat_handles,
        module_name,
    )
    .map_err(|e| refused(e.to_string()))?;
    let mut module = carrier.module;
    // Claim-free: computational content only (Trust rulings 08-04 §2,
    // 08-27 §9). No obligation, certificate or summary leaves the core.
    strip_claims(&mut module);
    module.target_info = Some(target.clone());
    let errors = validate_module(&module);
    if !errors.is_empty() {
        return Err(refused(format!("the module does not validate: {errors:?}")));
    }
    if !carrier.handle_bearing {
        let violations = module_subset_violations(&module);
        if !violations.is_empty() {
            return Err(refused(format!(
                "the module is outside trust-ir's lowering-target subset: {violations:?}"
            )));
        }
    }

    let tv = kernel_tv_self_check(&module, env, roots)?;
    let env_digest = env.content_digest();
    let environment = format!("sha256:{}", env_digest.total);
    let declarations = env_digest
        .sections
        .iter()
        .find(|s| s.name == "constants")
        .map(|s| s.entries.clone())
        .unwrap_or_default();
    let core_version = format!(
        "clean-compiler {} rust-abi/{RUST_ABI_LOWERING_REVISION}",
        env!("CARGO_PKG_VERSION")
    );
    let mut rows = Vec::with_capacity(roots.len());
    for (root, signature) in roots.iter().zip(signatures) {
        let (_, id) = carrier
            .functions
            .iter()
            .find(|(n, _)| n == root)
            .ok_or_else(|| refused(format!("`{root}` was not emitted")))?;
        let function = module
            .functions
            .iter()
            .find(|f| f.id == *id)
            .ok_or_else(|| refused(format!("`{root}` has no function in the module")))?;
        check_signature(&module, function, root, &signature)?;
        let root_key = root.to_string();
        let declaration = declarations
            .iter()
            .find(|(k, _)| *k == root_key)
            .map(|(_, d)| d.clone())
            .ok_or_else(|| refused(format!("`{root}` has no environment digest row")))?;
        let key = key_digest(&environment, &declaration, &core_version, &target.triple);
        rows.push(RustAbiRow {
            declaration: root.clone(),
            symbol: function.name.clone(),
            func_id: *id,
            signature,
            digest: CoreFunctionDigest {
                environment: environment.clone(),
                declaration,
                core_version: core_version.clone(),
                target: target.triple.clone(),
                key,
                function: function_digest(&module, *id),
            },
            kernel_tv_self_check: tv.contains(&function.name),
        });
    }
    Ok(RustAbiOutput {
        module,
        rows,
        handle_bearing: carrier.handle_bearing,
    })
}

fn strip_claims(module: &mut Module) {
    module.proof_obligations.clear();
    module.proof_certificates.clear();
    module.obligation_diagnostics.clear();
    for f in &mut module.functions {
        f.proofs.clear();
        f.summary = None;
    }
}

/// The emitted `FuncTy` of `function` must be `signature` at the carrier
/// types (C3).
fn check_signature(
    module: &Module,
    function: &trust_ir::Function,
    root: &Name,
    signature: &CarrierSignature,
) -> Result<(), RustAbiError> {
    let ty = |c: Carrier| match c {
        Carrier::Bool => Ty::Bool,
        Carrier::UInt8 => Ty::U8,
        Carrier::UInt16 => Ty::U16,
        Carrier::UInt32 => Ty::U32,
        Carrier::UInt64 => Ty::U64,
        Carrier::Nat => Ty::handle("Nat", "trust_bignum::Nat"),
    };
    let expected = trust_ir::ty::FuncTy {
        params: signature.params.iter().map(|c| ty(*c)).collect(),
        returns: vec![ty(signature.result)],
        is_vararg: false,
        abi: None,
    };
    match module.func_type(function.ty) {
        Some(emitted) if *emitted == expected => Ok(()),
        emitted => Err(RustAbiError::SignatureMismatch {
            name: root.to_string(),
            expected: format!("{expected:?}"),
            emitted: format!("{emitted:?}"),
        }),
    }
}

/// The kernel translation-validation self-check, run on a COPY: the copy's
/// certificates are discarded (no CIC term enters the output), its verdict is
/// disclosed per row, and a kernel REFUSAL — emitted code that does not
/// denote its definition — fails the compile.
fn kernel_tv_self_check(
    module: &Module,
    env: &Environment,
    roots: &[Name],
) -> Result<HashSet<String>, RustAbiError> {
    let originals: Vec<(String, clean_kernel::Expr)> = roots
        .iter()
        .filter_map(|r| {
            env.get_const(r)
                .and_then(|ci| ci.value.clone())
                .map(|v| (wire_name(r), v))
        })
        .collect();
    let mut copy = module.clone();
    let report = crate::emit_trust_ir_tv::certify_backend_translation_in_environment(
        &mut copy, &originals, env,
    );
    if !report.refused.is_empty() {
        return Err(RustAbiError::Refused {
            detail: format!(
                "the kernel translation-validation self-check REFUSED: {:?}",
                report.refused
            ),
        });
    }
    Ok(report.certified.into_iter().collect())
}

fn key_digest(environment: &str, declaration: &str, core: &str, target: &str) -> String {
    let mut bytes = Vec::new();
    for field in [environment, declaration, core, target] {
        bytes.extend_from_slice(&(field.len() as u64).to_le_bytes());
        bytes.extend_from_slice(field.as_bytes());
    }
    ProofDigest::sha256_domain("clean.core.rust_abi.key.v1", &bytes).to_string()
}

/// The digest of function `id`'s executable content, independent of the
/// module's name, of its claim channels, and of every OTHER function's body
/// (each other function stays as its declaration: the callee identities and
/// signatures `id` calls through remain bound).
fn function_digest(module: &Module, id: FuncId) -> String {
    let mut image = module.clone();
    strip_claims(&mut image);
    image.name = "clean.core.rust_abi.function".to_string();
    for f in &mut image.functions {
        f.body_gate = None;
        if f.id != id {
            f.blocks.clear();
        }
    }
    let content = image.executable_content_digest_v1();
    let mut bytes = id.index().to_le_bytes().to_vec();
    bytes.extend_from_slice(&content.bytes);
    ProofDigest::sha256_domain("clean.core.rust_abi.function.v1", &bytes).to_string()
}
