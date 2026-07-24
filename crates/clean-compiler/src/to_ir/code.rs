// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core code conversion from L5CNF `Code` to `IRBody`.
//!
//! Contains `lower_code` (the main dispatch), expression lowering
//! (`lower_let_value`, `lower_const_application`, `compute_proj_expr`),
//! and alternative lowering (`lower_alt`).

use super::lower::{lower_arg, lower_args, lower_ctor_args, lower_literal, lower_param};
use super::pseudo_ops::lower_let;
use super::state::ToIRState;
use super::types::expr_to_ir_type;
use crate::error::CompilerError;
use crate::ir::{CtorInfo, FnId, IRAlt, IRArg, IRBody, IRExpr, IRLiteral, IRType, VarId};
use crate::lcnf::{Alt, Arg, Code, LetValue};
use clean_kernel::{Literal, Name};

/// Convert L5CNF Code to IRBody.
pub fn lower_code(code: &Code, state: &mut ToIRState) -> Result<IRBody, CompilerError> {
    match code {
        Code::Return(fvar) => {
            let arg = state.get_var(*fvar)?;
            Ok(IRBody::Ret(arg))
        }

        Code::Let(decl, body) => lower_let(decl, body, state),

        // INVARIANT: lambda lifting (see `opt::lambda_lift`) runs before IR
        // lowering and rewrites every `Code::Fun` into a separate top-level
        // declaration plus, where the function escapes as a value, a
        // `LetValue::Const` closure binding at the original site. The public
        // entry points (`lower_decl`, `lower_decl_with_arities`, `lower_decls`)
        // and the `default_pipeline` all lift first, so a `Code::Fun` reaching
        // here means that invariant was violated upstream.
        //
        // We deliberately fail closed rather than attempt an inline lowering:
        // `lower_code` returns a single `IRBody`, and the IR model has no
        // `IRBody` variant for a nested first-class function (only `JDecl` for
        // non-escaping join points). A faithful lowering must emit an extra
        // top-level `IRDecl` and a closure at the binding site, which is exactly
        // what lambda lifting does and which `ToIRState` has no channel to
        // produce. Silently dropping `_body` (the continuation after the local
        // function) or the function body would be a miscompilation, so we
        // surface a typed error instead. See `pass_manager::defaults`.
        Code::Fun(fun_decl, _continuation) => Err(CompilerError::UnexpectedLocalFunction {
            name: fun_decl.name.clone(),
        }),

        Code::JoinPoint(jp_decl, body) => {
            let jp_id = state.bind_jp(jp_decl.fvar_id);

            // Convert join point parameters
            let params: Vec<(VarId, IRType)> = jp_decl
                .params
                .iter()
                .map(|p| lower_param(p, state))
                .collect::<Result<_, _>>()?;

            // Convert join point body
            let jp_body = lower_code(&jp_decl.body, state)?;

            // Convert continuation
            let rest = lower_code(body, state)?;

            Ok(IRBody::JDecl {
                jp: jp_id,
                params,
                body: Box::new(jp_body),
                rest: Box::new(rest),
            })
        }

        Code::Cases(cases) => {
            let scrutinee = match state.get_var(cases.scrutinee)? {
                IRArg::Var(v) => v,
                IRArg::Erased => {
                    return Err(CompilerError::InvalidErasedCaseScrutinee {
                        fvar: cases.scrutinee,
                    });
                }
            };

            // FAIL-CLOSED (C5b hygiene): a scrutinee VAR whose recorded type
            // is `Erased` is a proof-class value that survived erasure as a
            // placeholder (`let x := ◇; cases x …` — `Or.left_comm'`-class
            // lemmas casing on an erased `Or` proof). Branch selection on
            // erased data has no faithful lowering, and the alt bodies'
            // field projections out of the placeholder made the emitted
            // module invalid (`clean_ctor_get` on a `u64` — the exact
            // validate_module refusal that poisoned every Finset root's
            // closure). Refuse here so the per-decl probe demotes the decl
            // to an extern boundary instead of poisoning whole modules.
            if let Some(IRType::Erased) = state.get_var_type(scrutinee) {
                return Err(CompilerError::InvalidErasedCaseScrutinee {
                    fvar: cases.scrutinee,
                });
            }

            let mut alts = Vec::new();
            for alt in &cases.alts {
                if let Some(ir_alt) = lower_alt(alt, scrutinee, state)? {
                    alts.push(ir_alt);
                }
            }

            // Check for default
            let mut default = None;
            for alt in &cases.alts {
                if matches!(alt, Alt::Default(_)) {
                    default = Some(Box::new(lower_code(alt.body(), state)?));
                    break;
                }
            }

            Ok(IRBody::Case {
                scrutinee,
                alts,
                default,
            })
        }

        Code::Jmp { jp, args } => {
            let jp_id = state.get_jp(*jp)?;
            let ir_args = lower_args(args, state)?;
            Ok(IRBody::Jmp {
                jp: jp_id,
                args: ir_args,
            })
        }

        Code::Unreachable(_ty) => Ok(IRBody::Unreachable),
    }
}

/// Lower a `LetValue::Const` to either Apply or PartialApply (Part of #1936).
///
/// When the function's arity is known and `args.len() < arity`, emits
/// `IRExpr::PartialApply` (creates a closure). Otherwise emits `IRExpr::Apply`.
pub(super) fn lower_const_application(
    name: &Name,
    args: &[Arg],
    state: &ToIRState,
) -> Result<(IRExpr, IRType), CompilerError> {
    // A `Const` whose name is a constructor builds an inductive value: emit a
    // `lean_alloc_ctor` allocation rather than a call to an `l_<Ctor>` runtime
    // function. `to_mono::ctor_app_to_mono` spells constructor applications as
    // `LetValue::Const` (after erasing type params), so this is where genuine
    // tagged-constructor allocation happens for non-`Nat`/`Bool` inductives.
    // `Nat`/`Bool` constructors are already rewritten to literals / `Bool`
    // shims by `to_mono` and never reach here as constructor `Const`s.
    if state.lookup_ctor_meta(name).is_some() {
        let (ctor_info, ir_args) = lower_ctor_parts(name, args, state)?;
        return Ok((
            IRExpr::Ctor {
                info: ctor_info,
                args: ir_args,
            },
            IRType::Object,
        ));
    }

    let fn_id = FnId(name.clone());
    let ir_args = lower_args(args, state)?;

    if let Some(arity) = state.get_arity(name) {
        if (ir_args.len() as u16) < arity {
            return Ok((
                IRExpr::PartialApply {
                    fn_id,
                    arity,
                    args: ir_args,
                },
                IRType::Object,
            ));
        }
    }

    Ok((
        IRExpr::Apply {
            fn_id,
            args: ir_args,
        },
        IRType::Object,
    ))
}

/// Compute the correct IR projection expression for a field given its constructor's
/// field type layout.
///
/// The LCNF `idx` is the logical field index (0-based, counting all non-erased fields
/// in declaration order). The runtime memory layout places object pointers first,
/// followed by USize values (pointer-sized), followed by other scalar bytes:
///
/// ```text
/// [header] [obj_0..obj_{N-1}] [usize_0..usize_{M-1}] [scalar_bytes...]
/// ```
///
/// Different getter functions expect different index semantics:
///
/// - **Object fields** → `Proj` with object-slot index (count only preceding objects)
/// - **USize fields** → `UProj` with USize-slot index (count only preceding USize fields)
/// - **Other scalars** → `SProj` with `(n, offset)`: `n` = total pointer-sized slots
///   (objects + USize), `offset` = byte offset in scalar area
///
/// Part of #1982.
pub(crate) fn compute_proj_expr(
    type_name: &Name,
    field_types: &[IRType],
    idx: u32,
    arg: IRArg,
) -> Result<(IRExpr, IRType), CompilerError> {
    let idx_usize = idx as usize;

    let field_ty =
        field_types
            .get(idx_usize)
            .cloned()
            .ok_or(CompilerError::ProjectionIndexOutOfBounds {
                type_name: type_name.clone(),
                idx,
                field_count: field_types.len(),
            })?;

    let preceding = &field_types[..idx_usize];

    if field_ty == IRType::USize {
        // USize fields: pointer-sized slots after object pointers.
        // UProj idx = count of USize fields before this one.
        let usize_idx = preceding.iter().filter(|t| **t == IRType::USize).count() as u32;
        match arg {
            IRArg::Var(var) => Ok((
                IRExpr::UProj {
                    idx: usize_idx,
                    var,
                },
                field_ty,
            )),
            IRArg::Erased => Ok((
                IRExpr::Proj {
                    idx,
                    ty: field_ty.clone(),
                    arg,
                },
                field_ty,
            )),
        }
    } else if field_ty.is_scalar() {
        // Non-USize scalars: stored in the byte area after all pointer-sized slots.
        let num_objects = field_types.iter().filter(|t| t.is_rc_type()).count() as u32;
        let num_usizes = field_types.iter().filter(|t| **t == IRType::USize).count() as u32;
        let n = num_objects + num_usizes;
        let offset: u32 = preceding
            .iter()
            .filter(|t| t.is_scalar() && **t != IRType::USize)
            .map(|t| t.scalar_byte_size())
            .sum();
        match arg {
            IRArg::Var(var) => Ok((
                IRExpr::SProj {
                    n,
                    offset,
                    var,
                    ty: field_ty.clone(),
                },
                field_ty,
            )),
            IRArg::Erased => Ok((
                IRExpr::Proj {
                    idx,
                    ty: field_ty.clone(),
                    arg,
                },
                field_ty,
            )),
        }
    } else {
        // Object fields: first in the pointer array.
        // Proj idx = count of object fields before this one.
        let obj_idx = preceding.iter().filter(|t| t.is_rc_type()).count() as u32;
        Ok((
            IRExpr::Proj {
                idx: obj_idx,
                ty: field_ty.clone(),
                arg,
            },
            field_ty,
        ))
    }
}

/// Convert an L5CNF LetValue to IR expression and type.
pub(super) fn lower_let_value(
    value: &LetValue,
    state: &ToIRState,
) -> Result<(IRExpr, IRType), CompilerError> {
    match value {
        LetValue::Lit(lit) => match lit {
            Literal::String(s) => Ok((IRExpr::String(s.to_string()), IRType::Object)),
            _ => {
                let (ir_lit, ty) = lower_literal(lit)?;
                Ok((IRExpr::Lit(ir_lit), ty))
            }
        },

        LetValue::Erased => {
            // Erased values become unit
            Ok((IRExpr::Lit(IRLiteral::USize(0)), IRType::Erased))
        }

        LetValue::Proj {
            type_name,
            idx,
            structure,
        } => {
            let arg = state.get_var(*structure)?;
            // Prefer inductive-keyed metadata (single-ctor structures), then fall
            // back to per-constructor metadata. Generic `<Ind>.casesOn` lowering
            // (multi-constructor matches) emits field projections keyed by the
            // *constructor* name, because `inductive_env` only stores the tag-0
            // constructor's layout — see `to_lcnf::lower::lower_generic_cases` and
            // `to_ir::ctor_env::build_ctor_env`.
            let meta = state
                .lookup_proj_meta(type_name)
                .or_else(|| state.lookup_ctor_meta(type_name));
            match meta {
                Some(meta) => {
                    let field_types = meta.field_types.clone();
                    compute_proj_expr(type_name, &field_types, *idx, arg)
                }
                None => {
                    // No type info: fall back to Proj with Object type (backward compat).
                    Ok((
                        IRExpr::Proj {
                            idx: *idx,
                            ty: IRType::Object,
                            arg,
                        },
                        IRType::Object,
                    ))
                }
            }
        }

        LetValue::Const {
            name,
            levels: _,
            args,
        } => lower_const_application(name, args, state),

        LetValue::FVar { fvar, args } => {
            // Higher-order application: dynamic closure invocation (Lean 4 `ap`).
            let fn_arg = state.get_var(*fvar)?;
            let ir_args = lower_args(args, state)?;

            match fn_arg {
                IRArg::Var(fn_var) => Ok((
                    IRExpr::ClosureApply {
                        closure: IRArg::Var(fn_var),
                        args: ir_args,
                    },
                    IRType::Object,
                )),
                IRArg::Erased => Err(CompilerError::InvalidClosureCallee { fvar: *fvar }),
            }
        }

        LetValue::Ctor {
            name,
            levels: _,
            args,
        } => {
            let (ctor_info, ir_args) = lower_ctor_parts(name, args, state)?;
            Ok((
                IRExpr::Ctor {
                    info: ctor_info,
                    args: ir_args,
                },
                IRType::Object,
            ))
        }

        LetValue::Reuse {
            slot,
            ctor_name,
            levels: _,
            args,
        } => {
            // Reuse: allocate in a prior Reset slot if available, else fresh alloc.
            // The runtime checks ref count == 1 and either mutates or allocates.
            let (ctor_info, ir_args) = lower_ctor_parts(ctor_name, args, state)?;

            match state.get_var(*slot)? {
                IRArg::Var(slot_var) => Ok((
                    IRExpr::Reuse {
                        var: slot_var,
                        ctor: ctor_info,
                        args: ir_args,
                    },
                    IRType::Object,
                )),
                IRArg::Erased => Err(CompilerError::InvalidReuseSlot { slot: *slot }),
            }
        }
    }
}

/// Split a constructor application's LCNF arg spine into the leading
/// inductive-parameter args and the field args, fail-closed.
///
/// The kernel spelling of a constructor application passes the inductive's
/// `num_params` parameters first — `Arg::Type`/`Arg::Erased` for type-level
/// parameters, but a real `Arg::FVar` for VALUE-level ones (`Fin.mk`'s
/// `n : Nat`, `BitVec.ofFin`'s `w : Nat`), which type erasure does not
/// remove. `CtorMeta.field_types` deliberately excludes parameter binders
/// (`extract_field_ir_types` skips them), so alignment must drop exactly
/// `num_params` leading args; any spine that is not exactly
/// `num_params + field_types.len()` long (e.g. a partially applied
/// constructor used as a value) has no faithful field placement and is a
/// hard structured error in ALL profiles — the silent zip-truncation this
/// replaces stored `Fin.mk`'s bound `n` in `val`'s field slot.
pub(super) fn ctor_field_args<'a>(
    name: &Name,
    meta: &super::state::CtorMeta,
    args: &'a [Arg],
) -> Result<&'a [Arg], CompilerError> {
    let num_params = meta.num_params as usize;
    if args.len() != num_params + meta.field_types.len() {
        return Err(CompilerError::CtorSpineMisaligned {
            ctor: name.clone(),
            args: args.len(),
            num_params: meta.num_params,
            num_fields: meta.field_types.len(),
        });
    }
    Ok(&args[num_params..])
}

/// Lower a constructor application to its `CtorInfo` + runtime IR args.
///
/// With constructor metadata: drops the `num_params` leading parameter args
/// ([`ctor_field_args`], hard error on any misaligned spine), then walks the
/// field args POSITIONALLY against `field_types`, keeping only the pairs
/// whose arg survives erasure — so `CtorInfo.field_types[i]` is exactly the
/// type of `args[i]` and downstream layout partitioning
/// (`partition_ctor_fields`) can never pair a value with another field's
/// type. Erased fields (dropped proofs, type-valued fields) are absent from
/// both the runtime args and the layout, matching the historical behavior of
/// `lower_ctor_args` + the old best-effort alignment.
///
/// Without metadata: the historical fallback (`make_ctor_info` with
/// all-`Object` fields sized to the surviving args) is preserved for
/// hand-built IR.
fn lower_ctor_parts(
    name: &Name,
    lcnf_args: &[Arg],
    state: &ToIRState,
) -> Result<(CtorInfo, Vec<IRArg>), CompilerError> {
    let Some(meta) = state.lookup_ctor_meta(name) else {
        let ir_args = lower_ctor_args(lcnf_args, state)?;
        let ctor_info = state.make_ctor_info(name, ir_args.len());
        return Ok((ctor_info, ir_args));
    };

    let field_args = ctor_field_args(name, meta, lcnf_args)?;
    let mut ir_args = Vec::with_capacity(field_args.len());
    let mut field_types = Vec::with_capacity(meta.field_types.len());
    for (arg, ty) in field_args.iter().zip(meta.field_types.iter()) {
        match lower_arg(arg, state)? {
            IRArg::Erased => {}
            ir_arg => {
                ir_args.push(ir_arg);
                field_types.push(ty.clone());
            }
        }
    }
    let num_scalars = field_types.iter().filter(|t| t.is_scalar()).count() as u32;
    let num_objects = field_types.iter().filter(|t| t.is_rc_type()).count() as u32;
    Ok((
        CtorInfo {
            name: name.clone(),
            tag: meta.tag,
            num_scalars,
            num_objects,
            field_types,
        },
        ir_args,
    ))
}

/// Convert an L5CNF Alt to IRAlt.
fn lower_alt(
    alt: &Alt,
    _scrutinee: VarId,
    state: &mut ToIRState,
) -> Result<Option<IRAlt>, CompilerError> {
    match alt {
        Alt::Ctor {
            ctor_name,
            params,
            body,
        } => {
            // Bind constructor parameters as projections
            for param in params.iter() {
                let var_id = state.bind_var(param.fvar_id);
                // The actual projection is done when accessing the param.
                // Record the param's true IR type so a `_sset` in the branch
                // body that uses this param infers the correct scalar width
                // (Bool/UInt8/...) instead of the UInt64 fallback. Mirrors
                // `lower_param`. Part of #2123. If the type does not convert
                // to a runtime IR type (e.g. a synthetic placeholder), leave
                // it unrecorded — the `_sset` fallback then applies, which
                // preserves prior behavior.
                if let Ok(ty) = expr_to_ir_type(&param.ty) {
                    state.record_var_type(var_id, ty);
                }
            }

            let ir_body = lower_code(body, state)?;

            let ctor_info = state.make_ctor_info(ctor_name, params.len());

            Ok(Some(IRAlt {
                ctor: ctor_info,
                body: Box::new(ir_body),
            }))
        }
        Alt::Default(_) => {
            // Default is handled separately
            Ok(None)
        }
    }
}
