// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core IR checker implementation.
//!
//! Contains `IRChecker` and the public `check_decl`/`check_decls` entry points.

use super::{is_object_type, IRError, LocalContext, MAX_CTOR_FIELDS, MAX_CTOR_TAG};
use crate::compiler_env::CompilerEnv;
use crate::ir::{CtorInfo, FnId, IRArg, IRBody, IRDecl, IRExpr, IRType, JoinPointId, VarId};
use clean_kernel::Name;
use std::collections::{HashMap, HashSet};

/// Checker state for duplicate detection.
#[derive(Debug, Default)]
struct CheckerState {
    /// Variable IDs that have been defined (for duplicate detection).
    found_var_ids: HashSet<u32>,
    /// Join point IDs that have been defined (for duplicate detection).
    found_jp_ids: HashSet<u32>,
}

/// IR validity checker context.
pub(crate) struct IRChecker<'a> {
    local_ctx: LocalContext,
    current_decl: &'a IRDecl,
    all_decls: &'a [IRDecl],
    /// Name → index lookup for O(1) `get_decl`. Built once per checker.
    /// Empty when `env` is `Some` (lookup delegates to CompilerEnv).
    decl_index: HashMap<&'a Name, usize>,
    /// Unified compiler environment. When present, `get_decl` delegates here
    /// instead of using the local `decl_index`. Part of #1970.
    env: Option<&'a CompilerEnv>,
    state: CheckerState,
}

impl<'a> IRChecker<'a> {
    pub(crate) fn new(decl: &'a IRDecl, all_decls: &'a [IRDecl]) -> Self {
        let decl_index = all_decls
            .iter()
            .enumerate()
            .map(|(i, d)| (&d.name, i))
            .collect();
        Self {
            local_ctx: LocalContext::default(),
            current_decl: decl,
            all_decls,
            decl_index,
            env: None,
            state: CheckerState::default(),
        }
    }

    /// Create a checker with a pre-built declaration index (avoids redundant
    /// index construction when checking multiple declarations in batch).
    pub(crate) fn new_with_index(
        decl: &'a IRDecl,
        all_decls: &'a [IRDecl],
        decl_index: HashMap<&'a Name, usize>,
    ) -> Self {
        Self {
            local_ctx: LocalContext::default(),
            current_decl: decl,
            all_decls,
            decl_index,
            env: None,
            state: CheckerState::default(),
        }
    }

    /// Create a checker backed by a unified `CompilerEnv`. Part of #1970.
    pub(crate) fn new_with_env(
        decl: &'a IRDecl,
        all_decls: &'a [IRDecl],
        env: &'a CompilerEnv,
    ) -> Self {
        Self {
            local_ctx: LocalContext::default(),
            current_decl: decl,
            all_decls,
            decl_index: HashMap::new(), // unused when env is present
            env: Some(env),
            state: CheckerState::default(),
        }
    }

    /// Check variable is in scope (Rule V1).
    fn check_var(&self, var: VarId) -> Result<(), IRError> {
        if !self.local_ctx.is_in_scope(var) {
            Err(IRError::UndefinedVariable(var))
        } else {
            Ok(())
        }
    }

    /// Check join point is defined (Rule J1).
    fn check_jp(&self, jp: JoinPointId) -> Result<(), IRError> {
        if !self.local_ctx.is_jp(jp) {
            Err(IRError::UndefinedJoinPoint(jp))
        } else {
            Ok(())
        }
    }

    /// Mark a new variable definition, checking for duplicates (Rule V2).
    fn mark_var(&mut self, var: VarId) -> Result<(), IRError> {
        if self.state.found_var_ids.contains(&var.0) {
            Err(IRError::DuplicateDefinition(var.0))
        } else {
            self.state.found_var_ids.insert(var.0);
            Ok(())
        }
    }

    /// Mark a new join point definition, checking for duplicates.
    fn mark_jp(&mut self, jp: JoinPointId) -> Result<(), IRError> {
        if self.state.found_jp_ids.contains(&jp.0) {
            Err(IRError::DuplicateDefinition(jp.0))
        } else {
            self.state.found_jp_ids.insert(jp.0);
            Ok(())
        }
    }

    /// Check an IR argument.
    fn check_arg(&self, arg: &IRArg) -> Result<(), IRError> {
        match arg {
            IRArg::Var(v) => self.check_var(*v),
            IRArg::Erased => Ok(()),
        }
    }

    /// Check multiple arguments.
    fn check_args(&self, args: &[IRArg]) -> Result<(), IRError> {
        for arg in args {
            self.check_arg(arg)?;
        }
        Ok(())
    }

    /// Check that a variable is in scope and has object type.
    fn check_object_var(&self, var: VarId, context: &'static str) -> Result<(), IRError> {
        self.check_var(var)?;
        if let Ok(ty) = self.get_type(var) {
            if !is_object_type(ty) {
                return Err(IRError::TypeMismatch {
                    expected: "object",
                    actual: ty.clone(),
                    context,
                });
            }
        }
        Ok(())
    }

    /// Get type of a variable, returning error if not found.
    fn get_type(&self, var: VarId) -> Result<&IRType, IRError> {
        self.local_ctx
            .get_type(var)
            .ok_or(IRError::UndefinedVariable(var))
    }

    /// Look up a function declaration by name (O(1) via index).
    ///
    /// Delegates to `CompilerEnv` when available (Part of #1970), otherwise
    /// falls back to the local `decl_index`.
    fn get_decl(&self, name: &Name) -> Result<&'a IRDecl, IRError> {
        if let Some(env) = self.env {
            env.get_decl(name, self.all_decls)
                .ok_or_else(|| IRError::UnknownFunction(name.clone()))
        } else {
            self.decl_index
                .get(name)
                .map(|&i| &self.all_decls[i])
                .ok_or_else(|| IRError::UnknownFunction(name.clone()))
        }
    }

    /// Check constructor limits and consistency (Rules C1, C2).
    fn check_ctor(&self, info: &CtorInfo) -> Result<(), IRError> {
        if info.tag > MAX_CTOR_TAG {
            return Err(IRError::CtorTagTooLarge {
                name: info.name.clone(),
                tag: info.tag,
                max: MAX_CTOR_TAG,
            });
        }

        let total_fields = info.num_scalars + info.num_objects;
        if total_fields > MAX_CTOR_FIELDS {
            return Err(IRError::CtorTooManyFields {
                name: info.name.clone(),
                count: total_fields,
                max: MAX_CTOR_FIELDS,
            });
        }

        // Rule C2: field_types length must match num_scalars + num_objects.
        // Part of #1963.
        if !info.field_types.is_empty() && info.field_types.len() != total_fields as usize {
            return Err(IRError::CtorFieldCountMismatch {
                name: info.name.clone(),
                num_scalars: info.num_scalars,
                num_objects: info.num_objects,
                field_types_len: info.field_types.len(),
            });
        }

        Ok(())
    }

    /// Rule C3: Constructor arg count must match object field count.
    ///
    /// Ctor/Reuse args are only the object-pointer fields. Scalar fields are
    /// written separately via SSet body instructions — they must NOT appear
    /// in args because the emitter passes args as `clean_obj*` varargs to
    /// `clean_alloc_ctor`. Part of #1953, self-audit W2-727 F1.
    fn check_ctor_arg_count(&self, info: &CtorInfo, args: &[IRArg]) -> Result<(), IRError> {
        let expected = info.num_objects;
        if args.len() != expected as usize {
            return Err(IRError::CtorArgCountMismatch {
                name: info.name.clone(),
                num_args: args.len(),
                num_scalars: info.num_scalars,
                num_objects: info.num_objects,
                expected,
            });
        }
        Ok(())
    }

    /// Check join point jump (Rule J2).
    fn check_jmp(&self, jp: JoinPointId, args: &[IRArg]) -> Result<(), IRError> {
        self.check_jp(jp)?;

        let params = self
            .local_ctx
            .get_jp_params(jp)
            .ok_or(IRError::UndefinedJoinPoint(jp))?;

        if args.len() != params.len() {
            return Err(IRError::JoinPointArityMismatch {
                jp,
                expected: params.len(),
                actual: args.len(),
            });
        }

        self.check_args(args)
    }

    /// Check full application (Rule F1).
    fn check_full_app(&self, fn_id: &FnId, args: &[IRArg]) -> Result<(), IRError> {
        // Try to find the declaration
        if let Ok(decl) = self.get_decl(&fn_id.0) {
            // OVER-application is legal IR when the callee returns a managed
            // object: L5IR `Apply` args are the full application spine, and
            // the emitters lower the extras onto the saturated call's result
            // closure via the runtime `clean_apply_N` chain (the same
            // discipline as `emit_trust_ir::emit_apply_user`). A callee
            // returning a SCALAR has nothing to apply the extras to, and
            // UNDER-application outside a `PartialApply` has no faithful
            // lowering — both stay refusals (Rule F1).
            let over_applied_closure_result =
                args.len() > decl.params.len() && decl.return_type.lowers_to_ptr();
            if args.len() != decl.params.len() && !over_applied_closure_result {
                return Err(IRError::ArityMismatch {
                    function: fn_id.0.clone(),
                    expected: decl.params.len(),
                    actual: args.len(),
                });
            }
        }
        // If function not found, we allow it (might be external)
        self.check_args(args)
    }

    /// Check partial application (Rule F2).
    fn check_partial_app(&self, fn_id: &FnId, arity: u16, args: &[IRArg]) -> Result<(), IRError> {
        // Rule F2a: arity must be at least as large as captured arg count
        if (arity as usize) < args.len() {
            return Err(IRError::PartialApplyArityTooSmall {
                function: fn_id.0.clone(),
                arity,
                num_captured: args.len(),
            });
        }

        // Rule F2b: when declaration available, arity must match function signature
        if let Ok(decl) = self.get_decl(&fn_id.0) {
            if arity as usize != decl.params.len() {
                return Err(IRError::PartialApplyArityMismatch {
                    function: fn_id.0.clone(),
                    arity,
                    expected: decl.params.len(),
                });
            }
            if args.len() >= decl.params.len() {
                return Err(IRError::TooManyArgs {
                    function: fn_id.0.clone(),
                    arity: decl.params.len(),
                    provided: args.len(),
                });
            }
        }
        self.check_args(args)
    }

    /// Check an IR expression.
    fn check_expr(&self, expr: &IRExpr) -> Result<(), IRError> {
        match expr {
            IRExpr::Ctor { info, args } => {
                self.check_ctor(info)?;
                self.check_ctor_arg_count(info, args)?;
                self.check_args(args)
            }

            IRExpr::Proj {
                idx,
                ty: proj_ty,
                arg,
            } => {
                self.check_arg(arg)?;
                // Type checking for projection index would require more context
                // For now, just check the arg is valid
                if let IRArg::Var(var) = arg {
                    if let Ok(ty) = self.get_type(*var) {
                        match ty {
                            IRType::Struct(fields) => {
                                if *idx as usize >= fields.len() {
                                    return Err(IRError::InvalidProjection {
                                        idx: *idx,
                                        ty: ty.clone(),
                                    });
                                }
                            }
                            IRType::Object | IRType::TObject | IRType::Union(_) => {
                                // Object/Union projection is always valid (runtime check)
                            }
                            // C2 carrier projection: a projection out of an
                            // UNBOXED SCALAR carrier (`Char` lowered to
                            // `UInt32`) is valid IR in exactly two shapes —
                            // a same-lowered-width scalar result (the
                            // identity, `Char.val`) or a pointer-class
                            // result (re-boxing the carrier,
                            // `UInt8.toBitVec`). Anything else has no
                            // faithful lowering in any backend (mirrors
                            // `emit_trust_ir`'s `scalar_carrier_mismatch`).
                            _ if ty.is_scalar()
                                && (ty.same_lowered_scalar(proj_ty) || proj_ty.lowers_to_ptr()) => {
                            }
                            _ => {
                                return Err(IRError::TypeMismatch {
                                    expected: "object/struct",
                                    actual: ty.clone(),
                                    context: "projection target",
                                });
                            }
                        }
                    }
                }
                Ok(())
            }

            IRExpr::Tag(arg) => self.check_arg(arg),

            IRExpr::Box { arg, .. } => self.check_arg(arg),

            IRExpr::Unbox { arg, .. } => self.check_arg(arg),

            IRExpr::Lit(_) => Ok(()),

            IRExpr::Apply { fn_id, args } => self.check_full_app(fn_id, args),

            IRExpr::PartialApply { fn_id, arity, args } => {
                self.check_partial_app(fn_id, *arity, args)
            }

            IRExpr::ClosureApply { closure, args } => {
                self.check_arg(closure)?;
                self.check_args(args)
            }

            // C2 carrier projections: `UProj`/`SProj` out of an unboxed
            // scalar carrier are valid IR only as the width-faithful
            // identity — `UProj` produces `USize`, so the carrier must be
            // `UInt64`/`USize`-class; `SProj` must match the carrier's
            // lowered width. Mirrors `emit_trust_ir`'s C2 arms so the C
            // backend can lower the same shapes instead of refusing modules
            // trust-ir accepts.
            IRExpr::UProj { var, .. } => {
                self.check_var(*var)?;
                match self.get_type(*var) {
                    Ok(ty) if ty.is_scalar() => {
                        if ty.same_lowered_scalar(&IRType::USize) {
                            Ok(())
                        } else {
                            Err(IRError::TypeMismatch {
                                expected: "object or UInt64/USize carrier",
                                actual: ty.clone(),
                                context: "uproj source",
                            })
                        }
                    }
                    _ => self.check_object_var(*var, "uproj source"),
                }
            }
            IRExpr::SProj { var, ty: sty, .. } => {
                self.check_var(*var)?;
                match self.get_type(*var) {
                    Ok(ty) if ty.is_scalar() => {
                        if ty.same_lowered_scalar(sty) {
                            Ok(())
                        } else {
                            Err(IRError::TypeMismatch {
                                expected: "object or same-width scalar carrier",
                                actual: ty.clone(),
                                context: "sproj source",
                            })
                        }
                    }
                    _ => self.check_object_var(*var, "sproj source"),
                }
            }
            IRExpr::IsShared(var) => self.check_object_var(*var, "isShared"),

            IRExpr::String(_) => Ok(()),

            IRExpr::Reset(var) => self.check_object_var(*var, "reset source"),

            IRExpr::Reuse { var, ctor, args } => {
                self.check_object_var(*var, "reuse slot")?;
                self.check_ctor(ctor)?;
                self.check_ctor_arg_count(ctor, args)?;
                self.check_args(args)
            }
        }
    }

    /// Check a join point declaration (scoped context save/restore).
    fn check_jdecl(
        &mut self,
        jp: JoinPointId,
        params: &[(VarId, IRType)],
        jp_body: &IRBody,
        rest: &IRBody,
    ) -> Result<(), IRError> {
        self.mark_jp(jp)?;
        let saved_ctx = self.local_ctx.clone();
        let saved_var_state = self.state.found_var_ids.clone();
        self.local_ctx.add_jp(jp, params.to_vec());
        for (var, ty) in params {
            self.mark_var(*var)?;
            self.local_ctx.add_local(*var, ty.clone());
        }
        self.check_body(jp_body)?;
        self.local_ctx = saved_ctx;
        self.state.found_var_ids = saved_var_state;
        self.local_ctx.add_jp(jp, params.to_vec());
        self.check_body(rest)
    }

    /// Check an IR body.
    fn check_body(&mut self, body: &IRBody) -> Result<(), IRError> {
        match body {
            IRBody::VDecl {
                var,
                ty,
                value,
                rest,
            } => {
                self.check_expr(value)?;
                self.mark_var(*var)?;
                self.local_ctx.add_local(*var, ty.clone());
                self.check_body(rest)
            }
            IRBody::JDecl {
                jp,
                params,
                body: jp_body,
                rest,
            } => self.check_jdecl(*jp, params, jp_body, rest),
            IRBody::Inc { var, rest, .. } => {
                self.check_object_var(*var, "inc requires object type")?;
                self.check_body(rest)
            }
            IRBody::Dec { var, rest } => {
                self.check_object_var(*var, "dec requires object type")?;
                self.check_body(rest)
            }
            IRBody::Set {
                var, value, rest, ..
            } => {
                self.check_object_var(*var, "set target")?;
                self.check_var(*value)?;
                self.check_body(rest)
            }
            IRBody::SetTag { var, rest, .. } => {
                self.check_object_var(*var, "setTag target")?;
                self.check_body(rest)
            }
            IRBody::USet {
                var, value, rest, ..
            } => {
                self.check_object_var(*var, "uset target")?;
                self.check_var(*value)?;
                self.check_body(rest)
            }
            IRBody::SSet {
                var, value, rest, ..
            } => {
                self.check_object_var(*var, "sset target")?;
                self.check_var(*value)?;
                self.check_body(rest)
            }
            IRBody::Case {
                scrutinee,
                alts,
                default,
            } => {
                self.check_var(*scrutinee)?;
                // Rule C3: tag uniqueness in case alternatives. Part of #1963.
                let mut seen_tags = HashSet::new();
                for alt in alts {
                    if !seen_tags.insert(alt.ctor.tag) {
                        return Err(IRError::DuplicateCaseTag { tag: alt.ctor.tag });
                    }
                    self.check_ctor(&alt.ctor)?;
                    self.check_body(&alt.body)?;
                }
                if let Some(def) = default {
                    self.check_body(def)?;
                }
                Ok(())
            }
            IRBody::Jmp { jp, args } => self.check_jmp(*jp, args),
            IRBody::Ret(arg) => self.check_arg(arg),
            IRBody::Unreachable => Ok(()),
        }
    }

    /// Run the full check.
    pub(crate) fn check(&mut self) -> Result<(), IRError> {
        // Add parameters to context
        for (var, ty) in &self.current_decl.params {
            self.mark_var(*var)?;
            self.local_ctx.add_param(*var, ty.clone());
        }

        // Check body
        self.check_body(&self.current_decl.body)
    }
}
