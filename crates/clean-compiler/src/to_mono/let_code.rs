// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Let-value and code transformation for monomorphization.

use crate::lcnf::{Arg, Code, FunDecl, LetDecl, LetValue};
use clean_kernel::{Environment, Expr, FVarId, Name};

use super::args::{
    arg_to_mono, args_to_mono, args_to_mono_red_arg, args_to_mono_with_fn_type, param_to_mono,
};
use super::names::special_names;
use super::names::{has_trivial_structure, prop_valued_const};
use super::{red_arg_name, to_mono_type, ToMonoState, MAX_TO_MONO_STACK_DEPTH};

/// Result of transforming a let value.
pub enum LetValueTransform {
    /// Simple replacement.
    Simple(LetValue),
    /// Nat.succ needs extra let binding: let _1 := 1; Nat.add arg _1
    NatSucc(Arg),
}

/// Transform a let value to monomorphic form.
///
/// Handles special cases like Decidable→Bool conversion and constructor
/// type parameter erasure.
///
/// # Arguments
/// * `value` - The let value to transform
/// * `state` - ToMono state for tracked type parameters
/// * `env` - Environment for looking up constructor info (num_params)
pub fn letvalue_to_mono(
    value: &LetValue,
    state: &ToMonoState,
    env: &Environment,
) -> LetValueTransform {
    match value {
        LetValue::Const { name, args, .. } => {
            // Decidable.isTrue → Bool.true
            if *name == special_names::decidable_is_true() {
                return LetValueTransform::Simple(LetValue::Const {
                    name: special_names::bool_true(),
                    levels: vec![],
                    args: vec![],
                });
            }

            // Decidable.isFalse → Bool.false
            if *name == special_names::decidable_is_false() {
                return LetValueTransform::Simple(LetValue::Const {
                    name: special_names::bool_false(),
                    levels: vec![],
                    args: vec![],
                });
            }

            // Decidable.decide → identity on arg[1]
            if *name == special_names::decidable_decide() {
                if let Some(Arg::FVar(fvar)) = args.get(1) {
                    return LetValueTransform::Simple(LetValue::FVar {
                        fvar: *fvar,
                        args: vec![],
                    });
                }
            }

            // Quot.mk → identity on arg[2]
            // Quot.mk takes 3 args: (α : Sort u), (r : α → α → Prop), (a : α)
            // Returns the wrapped value directly since Quot has same runtime repr as α
            if *name == special_names::quot_mk() {
                if let Some(Arg::FVar(fvar)) = args.get(2) {
                    return LetValueTransform::Simple(LetValue::FVar {
                        fvar: *fvar,
                        args: vec![],
                    });
                }
            }

            // Quot.lcInv → extract function and apply remaining args
            // Quot.lcInv takes: (α : Sort u), (r : α → α → Prop), (motive : Quot r → Prop),
            //                   (f : (a : α) → motive (Quot.mk r a)), (q : Quot r), (h : motive q)
            // At runtime, Lean 4 lowers this to direct application of args[2]
            // with args[3..] after erasing type/proof-only values.
            if *name == special_names::quot_lc_inv() {
                if let Some(primary_arg) = args.get(2) {
                    match primary_arg {
                        Arg::FVar(fvar) => {
                            let extra_args = args
                                .iter()
                                .skip(3)
                                .map(|arg| arg_to_mono(arg, state))
                                .collect();
                            return LetValueTransform::Simple(LetValue::FVar {
                                fvar: *fvar,
                                args: extra_args,
                            });
                        }
                        Arg::Type(_) | Arg::Erased => {
                            return LetValueTransform::Simple(LetValue::Erased);
                        }
                        Arg::Index(_) => {}
                    }
                }
            }

            if let Some(mono_decl) = state.get_mono_decl(name) {
                if args.len() >= mono_decl.params.len() {
                    if let Some(red_arg_call) = &mono_decl.red_arg_call {
                        let red_arg_callee = red_arg_name(name);
                        if red_arg_call.callee == red_arg_callee {
                            let mono_args = args_to_mono_red_arg(
                                args,
                                &mono_decl.params,
                                &red_arg_call.args,
                                state,
                            );
                            return LetValueTransform::Simple(LetValue::Const {
                                name: red_arg_callee,
                                levels: vec![],
                                args: mono_args,
                            });
                        }
                    }

                    let mono_args = args_to_mono_with_fn_type(args, &mono_decl.ty, state);
                    return LetValueTransform::Simple(LetValue::Const {
                        name: name.clone(),
                        levels: vec![],
                        args: mono_args,
                    });
                }
            }

            // Nat.succ n → Nat.add n 1
            if *name == special_names::nat_succ() {
                if let Some(arg) = args.first() {
                    let mono_arg = arg_to_mono(arg, state);
                    return LetValueTransform::NatSucc(mono_arg);
                }
            }

            // Nat.zero → Lit(Nat(0))
            if *name == special_names::nat_zero() {
                return LetValueTransform::Simple(LetValue::nat(0));
            }

            // PROOF-VALUED call: the callee's DECLARED (closed) kernel type
            // says the applied result lives in `Prop` — the binding is a
            // proof, erased at runtime (box 0). `to_lcnf` already erases
            // CLOSED proof arguments (`classify_expr_arg`), but proof
            // SUBTERMS inside peeled binders are open, whole-term inference
            // fails, and the fail-closed `Normal` verdict materialized the
            // computation: `Char.ofNat`'s invalid arm EXECUTED
            // `Nat.le_of_ble_eq_true 1 (2^32)` — a 2^32-deep synthesized
            // `Nat.ble` recursion — as a runtime stack overflow, and
            // `Fin.ofNat` allocated a live `Nat.mod_lt` proof cell into
            // every `Fin.mk` (R3). The callee's declared type needs no
            // inference on the open call site, so this is exact, not
            // heuristic. See [`prop_valued_const`].
            if prop_valued_const(name, args.len(), env) {
                return LetValueTransform::Simple(LetValue::Erased);
            }

            // FULL constructor application of a TRIVIAL STRUCTURE, spelled as
            // `Const` — the spelling `to_lcnf` actually emits (it never
            // produces `LetValue::Ctor`, so the twin elimination in the
            // `Ctor` arm below never fired on the real pipeline). Without
            // this, the two representations of a trivial structure DISAGREE:
            // the `Proj` arm eliminates (projection = identity on the bare
            // field) while construction allocates a real tagged cell —
            // `OfNat.ofNat inst` then ALIASES the 16-byte `OfNat.mk` cell as
            // if it were the field (the R3 single-method-typeclass
            // representation mismatch: `clean_apply_2` on an `instHPow` CTOR
            // cell was a heap-buffer-overflow, and every `instOfNatNat` cell
            // in the UIntN/Char `ofNat` decode chains stranded per call).
            // Eliminating construction restores the invariant the `Proj` and
            // `Cases` sides already assume: a trivial-structure value IS its
            // single relevant field. Partial applications (PAP closures) and
            // `Arg::Index` field values keep the allocation path, fail-closed.
            if let Some(ctor_val) = env.get_constructor(name) {
                let full_arity = (ctor_val.num_params + ctor_val.num_fields) as usize;
                if args.len() == full_arity {
                    if let Some(info) = has_trivial_structure(&ctor_val.inductive_name, env) {
                        let field_idx = (ctor_val.num_params as usize) + info.field_idx;
                        match args.get(field_idx) {
                            Some(Arg::FVar(fvar)) => {
                                return LetValueTransform::Simple(LetValue::FVar {
                                    fvar: *fvar,
                                    args: vec![],
                                });
                            }
                            Some(Arg::Type(_)) | Some(Arg::Erased) => {
                                return LetValueTransform::Simple(LetValue::Erased);
                            }
                            Some(Arg::Index(_)) | None => {
                                // Fall through to the normal allocation path.
                            }
                        }
                    }
                }
            }

            // Default: erase type arguments and universe levels
            let mono_args = if let Some(mono_decl) = state.get_mono_decl(name) {
                args_to_mono_with_fn_type(args, &mono_decl.ty, state)
            } else {
                args_to_mono(args, state)
            };
            LetValueTransform::Simple(LetValue::Const {
                name: name.clone(),
                levels: vec![],
                args: mono_args,
            })
        }

        LetValue::Ctor { name, args, .. } => {
            // Nat.zero → Lit(Nat(0)) - same as Const case
            if *name == special_names::nat_zero() {
                return LetValueTransform::Simple(LetValue::nat(0));
            }

            // Nat.succ n → Nat.add n 1 - same as Const case
            if *name == special_names::nat_succ() {
                if let Some(arg) = args.first() {
                    let mono_arg = arg_to_mono(arg, state);
                    return LetValueTransform::NatSucc(mono_arg);
                }
            }

            // Look up constructor info to get num_params for proper erasure.
            // Constructors have type parameters first, then field arguments.
            // Type params are erased (replaced with Arg::Erased), fields are transformed.
            if let Some(ctor_val) = env.get_constructor(name) {
                // Check for trivial structure: if the parent inductive is trivial,
                // the constructor call becomes just the single relevant field.
                if let Some(info) = has_trivial_structure(&ctor_val.inductive_name, env) {
                    // For trivial structures, extract the single relevant field.
                    // The field is at num_params + field_idx position in args.
                    let field_idx = (ctor_val.num_params as usize) + info.field_idx;
                    if let Some(arg) = args.get(field_idx) {
                        match arg {
                            Arg::FVar(fvar) => {
                                return LetValueTransform::Simple(LetValue::FVar {
                                    fvar: *fvar,
                                    args: vec![],
                                });
                            }
                            Arg::Type(_) | Arg::Erased => {
                                return LetValueTransform::Simple(LetValue::Erased);
                            }
                            Arg::Index(_) => {
                                // Index literals shouldn't appear as ctor field values
                                // Fall through to normal processing
                            }
                        }
                    }
                }

                // Use ctor_app_to_mono for precise type parameter erasure
                return LetValueTransform::Simple(super::args::ctor_app_to_mono(
                    name,
                    args,
                    ctor_val.num_params as usize,
                    state,
                ));
            }

            // Fallback if constructor not in environment: simple arg erasure
            let mono_args = args_to_mono(args, state);
            LetValueTransform::Simple(LetValue::Ctor {
                name: name.clone(),
                levels: vec![],
                args: mono_args,
            })
        }

        LetValue::FVar { fvar, args } => {
            // If FVar is a type param, the whole application is erased
            if state.is_type_param(*fvar) {
                return LetValueTransform::Simple(LetValue::Erased);
            }
            let mono_args = args_to_mono(args, state);
            LetValueTransform::Simple(LetValue::FVar {
                fvar: *fvar,
                args: mono_args,
            })
        }

        LetValue::Proj {
            type_name,
            idx,
            structure,
        } => {
            // If structure is a type param, projection is erased
            if state.is_type_param(*structure) {
                return LetValueTransform::Simple(LetValue::Erased);
            }

            // Trivial structure projection: if the structure is trivial and we're
            // projecting the relevant field, just return the structure fvar.
            // If projecting a non-relevant field (proof/type), return erased.
            // Based on Lean 4's LetValue.proj handling in ToMono.lean:133-142.
            //
            // `type_name` carries the INDUCTIVE name for kernel
            // `ExprKind::Proj` lowerings (`OfNat.0 x`), but the CONSTRUCTOR
            // name for `Proj`s materialized by `to_lcnf`'s generic-cases arm
            // (`Fin.mk.0 x`) — resolve the latter to its parent inductive so
            // both spellings take the same elimination (R3: `Fin.val`'s
            // ctor-name proj stayed a `clean_ctor_get` over a bare `Nat`).
            let proj_inductive = if env.get_inductive(type_name).is_some() {
                Some(type_name.clone())
            } else {
                env.get_constructor(type_name)
                    .map(|ctor| ctor.inductive_name.clone())
            };
            if let Some(info) = proj_inductive.and_then(|ind| has_trivial_structure(&ind, env)) {
                if info.field_idx == (*idx as usize) {
                    // Projecting the relevant field: identity
                    return LetValueTransform::Simple(LetValue::FVar {
                        fvar: *structure,
                        args: vec![],
                    });
                } else {
                    // Projecting a non-relevant field (proof/type): erased
                    return LetValueTransform::Simple(LetValue::Erased);
                }
            }

            LetValueTransform::Simple(LetValue::Proj {
                type_name: type_name.clone(),
                idx: *idx,
                structure: *structure,
            })
        }

        LetValue::Lit(lit) => LetValueTransform::Simple(LetValue::Lit(lit.clone())),

        LetValue::Erased => LetValueTransform::Simple(LetValue::Erased),

        // Reuse: erase type args and universe levels like Ctor
        LetValue::Reuse {
            slot,
            ctor_name,
            args,
            ..
        } => {
            // If slot is a type param, the whole reuse is erased
            if state.is_type_param(*slot) {
                return LetValueTransform::Simple(LetValue::Erased);
            }
            let mono_args = args_to_mono(args, state);
            LetValueTransform::Simple(LetValue::Reuse {
                slot: *slot,
                ctor_name: ctor_name.clone(),
                levels: vec![],
                args: mono_args,
            })
        }
    }
}

/// Transform code to monomorphic form.
///
/// # Arguments
/// * `code` - The code to transform
/// * `state` - Monomorphization state tracking type parameters
/// * `next_fvar` - Counter for generating fresh FVarIds
/// * `env` - Environment for type lookups (used by cases handlers)
pub fn code_to_mono(
    code: &Code,
    state: &mut ToMonoState,
    next_fvar: &mut u64,
    env: &Environment,
) -> Code {
    code_to_mono_with_depth(code, state, next_fvar, env, 0)
}

pub(super) fn code_to_mono_with_depth(
    code: &Code,
    state: &mut ToMonoState,
    next_fvar: &mut u64,
    env: &Environment,
    depth: usize,
) -> Code {
    if depth > MAX_TO_MONO_STACK_DEPTH {
        return code.clone();
    }

    match code {
        Code::Let(decl, body) => {
            let ty = to_mono_type(&decl.ty);

            match letvalue_to_mono(&decl.value, state, env) {
                LetValueTransform::Simple(value) => {
                    let mono_decl = LetDecl {
                        fvar_id: decl.fvar_id,
                        name: decl.name.clone(),
                        ty,
                        value,
                    };
                    Code::Let(
                        mono_decl,
                        Box::new(code_to_mono_with_depth(
                            body,
                            state,
                            next_fvar,
                            env,
                            depth + 1,
                        )),
                    )
                }

                LetValueTransform::NatSucc(arg) => {
                    // Transform: let x := Nat.succ n
                    // To: let _lit := 1; let x := Nat.add n _lit

                    let lit_fvar = FVarId::new(*next_fvar);
                    *next_fvar += 1;

                    let lit_decl = LetDecl {
                        fvar_id: lit_fvar,
                        name: Name::from_string("_lit"),
                        ty: Expr::const_(Name::from_string("Nat"), vec![]),
                        value: LetValue::nat(1),
                    };

                    let add_decl = LetDecl {
                        fvar_id: decl.fvar_id,
                        name: decl.name.clone(),
                        ty,
                        value: LetValue::Const {
                            name: special_names::nat_add(),
                            levels: vec![],
                            args: vec![arg, Arg::FVar(lit_fvar)],
                        },
                    };

                    Code::Let(
                        lit_decl,
                        Box::new(Code::Let(
                            add_decl,
                            Box::new(code_to_mono_with_depth(
                                body,
                                state,
                                next_fvar,
                                env,
                                depth + 1,
                            )),
                        )),
                    )
                }
            }
        }

        Code::Fun(decl, body) => {
            let fun_decl = fun_decl_to_mono(decl, state, next_fvar, env, depth + 1);
            Code::Fun(
                fun_decl,
                Box::new(code_to_mono_with_depth(
                    body,
                    state,
                    next_fvar,
                    env,
                    depth + 1,
                )),
            )
        }

        Code::JoinPoint(decl, body) => {
            let jp_decl = fun_decl_to_mono(decl, state, next_fvar, env, depth + 1);
            Code::JoinPoint(
                jp_decl,
                Box::new(code_to_mono_with_depth(
                    body,
                    state,
                    next_fvar,
                    env,
                    depth + 1,
                )),
            )
        }

        Code::Cases(cases) => {
            super::cases::cases_to_mono_with_depth(cases, state, next_fvar, env, depth + 1)
        }

        Code::Jmp { jp, args } => {
            let mono_args = args_to_mono(args, state);
            Code::Jmp {
                jp: *jp,
                args: mono_args,
            }
        }

        Code::Return(fvar) => Code::Return(*fvar),

        Code::Unreachable(ty) => Code::Unreachable(to_mono_type(ty)),
    }
}

/// Transform a function declaration to monomorphic form.
fn fun_decl_to_mono(
    decl: &FunDecl,
    state: &mut ToMonoState,
    next_fvar: &mut u64,
    env: &Environment,
    depth: usize,
) -> FunDecl {
    let params: Vec<_> = decl
        .params
        .iter()
        .map(|p| param_to_mono(p, state))
        .collect();
    let ty = to_mono_type(&decl.ty);
    let body = code_to_mono_with_depth(&decl.body, state, next_fvar, env, depth);

    FunDecl {
        fvar_id: decl.fvar_id,
        name: decl.name.clone(),
        params,
        ty,
        body: Box::new(body),
    }
}
