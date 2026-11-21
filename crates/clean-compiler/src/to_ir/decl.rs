// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Declaration-level conversion from L5CNF `Decl` to `IRDecl`.
//!
//! Contains the public API entry points: `lower_decl`, `lower_decls`,
//! `to_ir`, and `to_ir_with_env`.

use super::code::lower_code;
use super::ctor_env::{build_external_arities, build_source_ctor_env};
use super::lower::lower_param;
use super::state::{CtorMeta, ToIRState};
use super::types::expr_to_ir_type_return;
use crate::error::CompilerError;
use crate::ir::{IRDecl, IRType, VarId};
use crate::lcnf::{Decl, DeclValue};
use crate::opt::lambda_lift::{lambda_lift_decls, lambda_lift_default, LiftConfig};
use clean_kernel::{ConstructorVal, Name};
use std::collections::{HashMap, HashSet};

/// Result of IR lowering, including any diagnostic warnings.
///
/// Warnings indicate non-fatal compatibility fallbacks (e.g., constructor
/// metadata not found in environment, using hardcoded defaults). Part of #2012.
#[derive(Debug, Clone)]
pub struct ToIROutput {
    /// Lowered IR declarations.
    pub decls: Vec<IRDecl>,
    /// Accumulated diagnostic warnings from conversion.
    pub warnings: Vec<String>,
    /// Per lowered declaration, the IR variables bound from an LCNF binder
    /// whose type is a source scalar (`rc::insert::is_scalar_type`). LCNF RC
    /// inserted no `inc`/`dec` for them, so if boxing gives one an object
    /// representation it is unmanaged; `rc_repair::rc_repair_boxed` manages
    /// exactly these (plus the variables boxing introduces). WS6.2.
    pub rc_unmanaged: HashMap<Name, HashSet<VarId>>,
    #[cfg(feature = "trust-ir-backend")]
    /// The Rust callees of the batch (Trust plan step 3.2, C2): each
    /// `rust`-backend extern declaration's symbol and lowered signature. An
    /// extern declaration lowers to no `IRDecl`, so without this its call
    /// sites would see an unknown callee and box their scalar arguments.
    pub(crate) rust_externs: Vec<crate::rust_abi::RustExternSig>,
}

/// Convert an L5CNF Decl to IRDecl (no cross-declaration arity info).
///
/// Lambda-lifts the declaration first to eliminate `Code::Fun` nodes,
/// then lowers the result to IR. Use `lower_decl_with_arities` or
/// `lower_decls` for PartialApply support.
pub fn lower_decl(decl: &Decl) -> Result<Option<IRDecl>, CompilerError> {
    let lift_result = lambda_lift_default(decl);
    let (ir_decl, _warnings) = lower_decl_with_env(
        &lift_result.decl,
        &HashMap::new(),
        &HashMap::new(),
        &HashMap::new(),
    )?;
    Ok(ir_decl)
}

/// Convert an L5CNF Decl to IRDecl with cross-declaration arity information.
///
/// Lambda-lifts the declaration first to eliminate `Code::Fun` nodes,
/// then lowers with the provided arity map. When `arities` maps function
/// names to parameter counts, `LetValue::Const` with fewer args than the
/// function's arity produces `IRExpr::PartialApply` instead of
/// `IRExpr::Apply`. Part of #1936.
pub fn lower_decl_with_arities(
    decl: &Decl,
    arities: &HashMap<Name, u16>,
) -> Result<Option<IRDecl>, CompilerError> {
    let lift_result = lambda_lift_default(decl);
    let (ir_decl, _warnings) =
        lower_decl_with_env(&lift_result.decl, arities, &HashMap::new(), &HashMap::new())?;
    Ok(ir_decl)
}

/// Convert an L5CNF Decl to IRDecl with arity and constructor environment.
///
/// Returns the lowered declaration (if not extern) along with any diagnostic
/// warnings accumulated during conversion. Part of #1953, #1941, #2012.
pub fn lower_decl_with_env(
    decl: &Decl,
    arities: &HashMap<Name, u16>,
    ctor_env: &HashMap<Name, CtorMeta>,
    inductive_env: &HashMap<Name, CtorMeta>,
) -> Result<(Option<IRDecl>, Vec<String>), CompilerError> {
    lower_decl_tracking_rc(
        decl,
        arities,
        ctor_env,
        inductive_env,
        false,
        false,
        Default::default(),
    )
    .map(|(ir_decl, warnings, _)| (ir_decl, warnings))
}

/// [`lower_decl_with_env`], also returning the declaration's RC-unmanaged
/// variables (see [`ToIROutput::rc_unmanaged`]).
fn lower_decl_tracking_rc(
    decl: &Decl,
    arities: &HashMap<Name, u16>,
    ctor_env: &HashMap<Name, CtorMeta>,
    inductive_env: &HashMap<Name, CtorMeta>,
    byte_array_string: bool,
    checked_void_layout: bool,
    external_constructors: std::sync::Arc<HashSet<Name>>,
) -> Result<(Option<IRDecl>, Vec<String>, HashSet<VarId>), CompilerError> {
    let mut state =
        ToIRState::with_arities_and_ctors(arities.clone(), ctor_env.clone(), inductive_env.clone());
    state.set_byte_array_string(byte_array_string);
    state.set_checked_void_layout(checked_void_layout);
    state.external_constructors = external_constructors;

    // Convert parameters
    let params: Vec<(VarId, IRType)> = decl
        .params
        .iter()
        .map(|p| lower_param(p, &mut state))
        .collect::<Result<_, _>>()?;

    // Get return type. Return position uses the C4 uniform-boxed conversion:
    // dependent/uninferred result types (lifted casesOn/recOn motive lambdas,
    // `Array.data`-class field accessors) lower as `Object` — see
    // `expr_to_ir_type_return` for the calling-convention soundness argument.
    // Params above stay on the strict `expr_to_ir_type` (via `lower_param`).
    let return_type = expr_to_ir_type_return(&decl.ty)?;

    // Convert body
    let body = match &decl.body {
        DeclValue::Code(code) => lower_code(code, &mut state)?,
        DeclValue::Extern(_) => {
            return Ok((None, state.drain_warnings(), HashSet::new()));
        }
    };

    let warnings = state.drain_warnings();
    let rc_unmanaged = state.take_rc_unmanaged();
    Ok((
        Some(IRDecl {
            name: decl.name.clone(),
            params,
            return_type,
            body,
        }),
        warnings,
        rc_unmanaged,
    ))
}

/// Convert multiple L5CNF Decls to IRDecls.
///
/// Builds a cross-declaration arity map so that partial applications of
/// known functions emit `IRExpr::PartialApply` instead of `IRExpr::Apply`.
/// Part of #1936.
pub fn lower_decls(decls: &[Decl]) -> Result<Vec<IRDecl>, CompilerError> {
    let output = lower_decls_with_env(decls, &HashMap::new(), &HashMap::new())?;
    Ok(output.decls)
}

/// Convert multiple L5CNF Decls to IRDecls with constructor environment.
///
/// Returns a `ToIROutput` with both the lowered declarations and any
/// diagnostic warnings accumulated during conversion. Part of #1953, #1941, #2012.
pub fn lower_decls_with_env(
    decls: &[Decl],
    ctor_env: &HashMap<Name, CtorMeta>,
    inductive_env: &HashMap<Name, CtorMeta>,
) -> Result<ToIROutput, CompilerError> {
    lower_decls_with_env_and_arities(decls, ctor_env, inductive_env, &HashMap::new())
}

pub(crate) fn lower_decls_with_env_and_arities(
    decls: &[Decl],
    ctor_env: &HashMap<Name, CtorMeta>,
    inductive_env: &HashMap<Name, CtorMeta>,
    external_arities: &HashMap<Name, u16>,
) -> Result<ToIROutput, CompilerError> {
    lower_decls_with_source_layout(
        decls,
        ctor_env,
        inductive_env,
        external_arities,
        false,
        false,
        Default::default(),
    )
}

fn lower_decls_with_source_layout(
    decls: &[Decl],
    ctor_env: &HashMap<Name, CtorMeta>,
    inductive_env: &HashMap<Name, CtorMeta>,
    external_arities: &HashMap<Name, u16>,
    byte_array_string: bool,
    checked_void_layout: bool,
    external_constructors: std::sync::Arc<HashSet<Name>>,
) -> Result<ToIROutput, CompilerError> {
    // Lambda-lift all declarations to eliminate Code::Fun nodes before IR
    // lowering. Produces the original decls (with Code::Fun replaced by
    // references to lifted top-level functions) plus new decls for each
    // lifted function.
    let lifted_decls = lambda_lift_decls(decls, &LiftConfig::default());

    // Build arity map: external (env) arities first, in-batch decls layered
    // on top so locally-defined arities win on name collisions.
    let mut arities: HashMap<Name, u16> = external_arities.clone();
    arities.extend(
        lifted_decls
            .iter()
            .map(|d| (d.name.clone(), d.params.len() as u16)),
    );

    let mut lowered = Vec::new();
    let mut all_warnings = Vec::new();
    let mut rc_unmanaged = HashMap::new();
    #[cfg(feature = "trust-ir-backend")]
    let rust_externs = lifted_decls
        .iter()
        .filter_map(crate::rust_abi::RustExternSig::of_decl)
        .collect();
    for decl in &lifted_decls {
        let (ir_decl, warnings, unmanaged) = lower_decl_tracking_rc(
            decl,
            &arities,
            ctor_env,
            inductive_env,
            byte_array_string,
            checked_void_layout,
            external_constructors.clone(),
        )?;
        if let Some(ir_decl) = ir_decl {
            if !unmanaged.is_empty() {
                rc_unmanaged.insert(ir_decl.name.clone(), unmanaged);
            }
            lowered.push(ir_decl);
        }
        all_warnings.extend(warnings);
    }
    Ok(ToIROutput {
        decls: lowered,
        warnings: all_warnings,
        rc_unmanaged,
        #[cfg(feature = "trust-ir-backend")]
        rust_externs,
    })
}

// ════════════════════════════════════════════════════════════════════════════
// Public API
// ════════════════════════════════════════════════════════════════════════════

/// Convert L5CNF declarations to L5IR.
///
/// This is the main entry point for LCNF-to-IR conversion.
///
/// # Example
///
/// ```rust,no_run
/// use clean_compiler::lcnf::{Code, Decl, Param};
/// use clean_compiler::to_ir::to_ir;
/// use clean_kernel::{Expr, FVarId, Name};
///
/// fn fvar(n: u64) -> FVarId {
///     FVarId::new(n)
/// }
///
/// fn name(s: &str) -> Name {
///     Name::from_string(s)
/// }
///
/// let decl = Decl::new(
///     name("id"),
///     vec![],
///     Expr::const_str("Nat"),
///     vec![Param::new(fvar(0), name("x"), Expr::const_str("Nat"))],
///     Code::ret(fvar(0)),
///     false,
/// );
///
/// let ir_decls = to_ir(&[decl]).expect("LCNF should lower to IR");
/// assert_eq!(ir_decls.len(), 1);
/// ```
pub fn to_ir(decls: &[Decl]) -> Result<Vec<IRDecl>, CompilerError> {
    lower_decls(decls)
}

/// Convert L5CNF declarations to L5IR with constructor metadata from
/// the kernel `Environment`.
///
/// This is the preferred entry point when an `Environment` is available.
/// It extracts constructor metadata (tags, field types, scalar counts)
/// from all registered constructors, enabling correct `CtorInfo` generation
/// instead of the fallback `tag: 0, num_scalars: 0` defaults.
///
/// Returns a `ToIROutput` with lowered declarations and any diagnostic
/// warnings (e.g., constructors not found in the environment). Part of #1953, #2012.
pub fn to_ir_with_env(
    decls: &[Decl],
    env: &clean_kernel::Environment,
) -> Result<ToIROutput, CompilerError> {
    to_ir_with_bindings(decls, env, None)
}

pub(crate) fn to_ir_with_bindings(
    decls: &[Decl],
    env: &clean_kernel::Environment,
    closure: Option<&crate::RuntimeBindingClosure>,
) -> Result<ToIROutput, CompilerError> {
    let ctors: Vec<&ConstructorVal> = env.constructors().collect();
    let checked_void_layout = crate::world_token::has_checked_void_layout(env);
    let (ctor_env, inductive_env) = build_source_ctor_env(&ctors, checked_void_layout)?;
    let external_arities = build_external_arities(env);
    lower_decls_with_source_layout(
        decls,
        &ctor_env,
        &inductive_env,
        &external_arities,
        crate::string_layout::has_byte_array_string_layout(env),
        checked_void_layout,
        closure
            .map(|c| c.executable_extern_constructors(env))
            .unwrap_or_default()
            .into(),
    )
}
