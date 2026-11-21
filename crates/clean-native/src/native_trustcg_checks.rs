// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The trust-cg lane's module self-checks: the C lane's post-emission audits
//! (`native_build`'s shim selection and entry contract), read off the emitted
//! trust-ir module instead of off emitted C, and the witness that licenses.
//!
//! Each check is fail-closed and names its step in the refusal:
//!
//! * `string-carrier` — no source-lowered `String.*` body: the runtime
//!   `String` is a flat byte string, and a body lowered from the prelude's
//!   `List Char` model links and computes garbage (the C lane's
//!   `first_source_lowered_string_body`).
//! * `link-demand` — every bodyless `l_*` declaration is defined by a prelude
//!   shim (the C lane's `first_uncovered_prelude_call`), and at the arity and
//!   pointer slots the module calls it with: a shim defined at the wrong arity
//!   links cleanly and reads garbage registers (the WS6.14 census's shim-ABI
//!   check, applied to the build).
//! * `entry-contract` — the entry is defined in its own module under its link
//!   symbol with a boxed signature, and Lean's entry contract holds
//!   ([`entry_contract_from_parts`], the C lane's own function).

use std::collections::BTreeMap;

use crate::native_string_layout_policy::StringLayoutPolicy;
use clean_compiler::emit_trust_ir::{
    module_stable_digest_string, serialize_module_bytes, validate_module_bytes,
};
use clean_compiler::emit_trust_ir_lane::{
    bodyless_declarations, defined_signature, restamp_ungated_as_unvalidated, AbiSlot,
    LicenseCensus, LinkSignature, Module,
};
use clean_kernel::{Environment, Expr, Name};

use super::LaneError;
use crate::native_build::{
    entry_contract_from_parts, genuine_init_console_definition, prelude_shim_definitions,
    render_shim_translation_unit, EntryContract, EntryKind, IO_ENTRY_MARKERS,
};

type ShimDefinition = (&'static str, &'static str);

/// Witness that the object checks and program entry check accepted one module.
/// The shared object witness binds licensing to its checked stable digest.
#[derive(Debug)]
pub(crate) struct ModuleSelfChecks {
    object: ObjectSelfChecks,
    entry_symbol: String,
    contract: EntryContract,
    shims: Vec<ShimDefinition>,
}

impl ModuleSelfChecks {
    /// The entry's link symbol in the emitted module.
    pub(crate) fn entry_symbol(&self) -> &str {
        &self.entry_symbol
    }

    /// The entry contract the driver honours.
    pub(crate) fn contract(&self) -> EntryContract {
        self.contract
    }

    /// The exact C definitions checked against this program's extern declarations.
    pub(super) fn shim_translation_unit(&self) -> String {
        render_shim_translation_unit(self.shims.iter().map(|(_, definition)| *definition))
    }

    /// Mint the `clean-compiler-unvalidated` license on `module`, which must
    /// be the module the checks accepted, byte for byte.
    pub(crate) fn license(&self, module: &mut Module) -> Result<LicenseCensus, LaneError> {
        self.object.license(module)
    }
}

/// Checked object code need not have a program entry/driver. It retains the
/// same structural, string-layout and runtime-ABI checks and digest binding.
#[derive(Debug)]
pub(crate) struct ObjectSelfChecks {
    digest: String,
}

impl ObjectSelfChecks {
    pub(crate) fn license(&self, module: &mut Module) -> Result<LicenseCensus, LaneError> {
        let digest = module_stable_digest_string(module)
            .map_err(|e| LaneError::core("license")(e.into()))?;
        if digest != self.digest {
            return Err(LaneError::Core {
                step: "license",
                cause: format!(
                    "the module to license (digest {digest}) is not the module the self-checks \
                     accepted (digest {})",
                    self.digest
                ),
            });
        }
        restamp_ungated_as_unvalidated(module).map_err(|e| LaneError::core("license")(e.into()))
    }
}

/// Run every module self-check on `module` (the entry `decl`, parsed as
/// `root`, declared at `decl_type`).
pub(crate) fn module_self_checks(
    module: &Module,
    decl: &str,
    root: &Name,
    decl_type: Option<&Expr>,
) -> Result<ModuleSelfChecks, LaneError> {
    module_self_checks_with_policy(module, decl, root, decl_type, StringLayoutPolicy::default())
}

pub(crate) fn module_self_checks_for_env(
    env: &Environment,
    module: &Module,
    decl: &str,
    root: &Name,
    decl_type: Option<&Expr>,
) -> Result<ModuleSelfChecks, LaneError> {
    let policy = StringLayoutPolicy::from_env(env);
    if !policy.permits_byte_backed_bodies() {
        return module_self_checks(module, decl, root, decl_type);
    }
    module_self_checks_with_policy(module, decl, root, decl_type, policy)
}

fn module_self_checks_with_policy(
    module: &Module,
    decl: &str,
    root: &Name,
    decl_type: Option<&Expr>,
    policy: StringLayoutPolicy,
) -> Result<ModuleSelfChecks, LaneError> {
    let bodyless = bodyless_declarations(module);
    let shims = program_shim_definitions(&bodyless);
    let object = check_module(module, policy, &bodyless, &shims, None)?;
    let entry_symbol = root.to_string();
    let contract = entry_contract(module, decl, &entry_symbol, &bodyless, decl_type)?;
    Ok(ModuleSelfChecks {
        object,
        entry_symbol,
        contract,
        shims,
    })
}

#[cfg(test)]
pub(crate) fn object_self_checks_for_env(
    env: &Environment,
    module: &Module,
) -> Result<ObjectSelfChecks, LaneError> {
    object_self_checks_for_env_recording(env, module, None)
}

pub(crate) fn object_self_checks_for_env_recording(
    env: &Environment,
    module: &Module,
    observation: Option<&crate::primitive_uses::NativeRecorder>,
) -> Result<ObjectSelfChecks, LaneError> {
    // Standalone objects link against the public archive's fixed definitions.
    let shims = prelude_shim_definitions();
    check_module(
        module,
        StringLayoutPolicy::from_env(env),
        &bodyless_declarations(module),
        &shims,
        observation,
    )
}

fn check_module(
    module: &Module,
    policy: StringLayoutPolicy,
    bodyless: &[LinkSignature],
    shims: &[ShimDefinition],
    observation: Option<&crate::primitive_uses::NativeRecorder>,
) -> Result<ObjectSelfChecks, LaneError> {
    let bytes =
        serialize_module_bytes(module).map_err(|e| LaneError::core("serialize")(e.into()))?;
    let validation = validate_module_bytes(&bytes).map_err(|cause| LaneError::Core {
        step: "module-validation",
        cause,
    });
    let module_context = observation.and_then(|observer| {
        observer.bytes(
            "actual native module before license",
            "module supplied to native checks",
            std::path::Path::new("module-before-license.trustir"),
            bytes,
        )
    });
    validation?;
    if !policy.permits_byte_backed_bodies() {
        refuse_source_lowered_string_body(module)?;
    }
    check_link_demand_recording(bodyless, shims, observation, module_context.as_ref())?;
    let digest =
        module_stable_digest_string(module).map_err(|e| LaneError::core("digest")(e.into()))?;
    Ok(ObjectSelfChecks { digest })
}

fn refuse_source_lowered_string_body(module: &Module) -> Result<(), LaneError> {
    let lowered = module
        .functions
        .iter()
        .filter(|f| !f.blocks.is_empty())
        .map(|f| f.display_path.as_deref().unwrap_or(f.name.as_str()))
        .find(|name| name.starts_with("String."));
    match lowered {
        Some(op) => Err(LaneError::Core {
            step: "string-carrier",
            cause: format!(
                "native build refuses source-lowered String body `{op}`: the runtime `String` \
                 carrier is a flat byte string, but a body lowered from the prelude's \
                 `List Char` model reads it as a constructor cell"
            ),
        }),
        None => Ok(()),
    }
}

/// Executable links can compile a genuine Init console shim privately. The IR
/// arity selects the candidate. The link-demand check validates every argument,
/// return and variadic flag against the selected definition before licensing.
pub(super) fn program_shim_definitions(bodyless: &[LinkSignature]) -> Vec<ShimDefinition> {
    let mut shims = prelude_shim_definitions();
    for (symbol, definition) in &mut shims {
        let Some((arity, genuine)) = genuine_init_console_definition(symbol) else {
            continue;
        };
        if bodyless
            .iter()
            .any(|decl| decl.symbol == *symbol && decl.params.len() == arity)
        {
            *definition = genuine;
        }
    }
    shims
}

pub(super) fn check_link_demand_recording(
    bodyless: &[LinkSignature],
    shims: &[ShimDefinition],
    observation: Option<&crate::primitive_uses::NativeRecorder>,
    module_context: Option<&crate::primitive_uses::NativeArtifactId>,
) -> Result<(), LaneError> {
    let shims: BTreeMap<_, _> = shims.iter().copied().collect();
    for decl in bodyless.iter().filter(|d| d.symbol.starts_with("l_")) {
        let Some(definition) = shims.get(decl.symbol.as_str()) else {
            if let Some(observer) = observation {
                observer.shim_demand(module_context, decl, None, None);
            }
            return Err(LaneError::Core {
                step: "link-demand",
                cause: format!(
                    "native build cannot satisfy prelude extern `{}`: no prelude shim defines \
                     it (the trust-cg lane links the whole shim union)",
                    decl.symbol
                ),
            });
        };
        let mismatch = shim_abi_mismatch(definition, decl);
        if let Some(observer) = observation {
            observer.shim_demand(module_context, decl, Some(*definition), mismatch.as_deref());
        }
        if let Some(why) = mismatch {
            return Err(LaneError::Core {
                step: "link-demand",
                cause: format!("prelude shim ABI mismatch: {why}"),
            });
        }
    }
    Ok(())
}

/// The parameter C types and return C type a shim definition states for
/// `symbol`, read from its first declarator.
pub(crate) fn shim_c_signature(symbol: &str, definition: &str) -> Option<(Vec<String>, String)> {
    let at = definition.find(&format!("{symbol}("))?;
    let ret = definition[..at]
        .trim()
        .trim_start_matches("static ")
        .trim()
        .to_owned();
    let open = at + symbol.len() + 1;
    let close = open + definition[open..].find(')')?;
    let params: Vec<String> = definition[open..close]
        .split(',')
        .map(|p| p.split_whitespace().collect::<Vec<_>>().join(" "))
        .filter(|p| !p.is_empty() && p != "void")
        .collect();
    Some((params, ret))
}

/// Why the shim `definition` cannot be what a module declaring `decl` calls,
/// or `None` when it can: same arity, not variadic, every slot a pointer.
pub(crate) fn shim_abi_mismatch(definition: &str, decl: &LinkSignature) -> Option<String> {
    let symbol = decl.symbol.as_str();
    let Some((params, ret)) = shim_c_signature(symbol, definition) else {
        return Some(format!(
            "{symbol}: the shim definition has no `{symbol}(` declarator"
        ));
    };
    if decl.vararg {
        return Some(format!("{symbol}: declared variadic; no shim is"));
    }
    if params.len() != decl.params.len() {
        return Some(format!(
            "{symbol}: declared with {} parameter(s), the shim defines {}",
            decl.params.len(),
            params.len()
        ));
    }
    for (i, (slot, c)) in decl.params.iter().zip(&params).enumerate() {
        if *slot != AbiSlot::Ptr || !c.contains('*') {
            return Some(format!(
                "{symbol}: parameter {i} declared {slot:?}, the shim takes `{c}`"
            ));
        }
    }
    if decl.returns != [AbiSlot::Ptr] || !ret.contains('*') {
        return Some(format!(
            "{symbol}: declared returning {:?}, the shim returns `{ret}`",
            decl.returns
        ));
    }
    None
}

fn entry_contract(
    module: &Module,
    decl: &str,
    entry_symbol: &str,
    bodyless: &[LinkSignature],
    decl_type: Option<&Expr>,
) -> Result<EntryContract, LaneError> {
    let refuse = |cause: String| LaneError::Core {
        step: "entry-contract",
        cause,
    };
    let entry = defined_signature(module, entry_symbol).ok_or_else(|| {
        refuse(format!(
            "the entry `{decl}` is not defined in its own emitted module under the link symbol \
             `{entry_symbol}`"
        ))
    })?;
    if entry.vararg
        || entry.params.iter().any(|s| *s != AbiSlot::Ptr)
        || entry.returns != [AbiSlot::Ptr]
    {
        return Err(refuse(format!(
            "the entry `{decl}` is emitted as ({:?}) -> {:?}; the driver passes and reads boxed \
             objects only",
            entry.params, entry.returns
        )));
    }
    let io = bodyless
        .iter()
        .any(|d| IO_ENTRY_MARKERS.contains(&d.symbol.as_str()));
    let kind = if io { EntryKind::Io } else { EntryKind::Nat };
    let contract = entry_contract_from_parts(decl, kind, Some(entry.params.len()), decl_type)
        .map_err(|e| refuse(format!("{e:#}")))?;
    if contract.kind == EntryKind::Nat && !entry.params.is_empty() {
        return Err(refuse(format!(
            "native build entry must be a nullary declaration: the emitted module defines \
             `{entry_symbol}` with {} parameter(s)",
            entry.params.len()
        )));
    }
    Ok(contract)
}
