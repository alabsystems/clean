// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Lower boxed IR to the physical convention for direct calls and joins.
//! Boxing runs first so a partial application still has its logical arity.
//! Closure calls therefore keep their boxed world argument even when the
//! direct implementation has no physical slot for it.

use crate::ir::{IRArg, IRBody, IRDecl, IRExpr, IRType, JoinPointId, VarId};
use crate::ir_checker::{check_decls, IRError};
use clean_kernel::Name;
use std::collections::HashMap;

fn void_slots(params: &[(VarId, IRType)]) -> Option<Vec<usize>> {
    let slots: Vec<_> = params
        .iter()
        .enumerate()
        .filter(|(_, (_, ty))| ty.is_void())
        .map(|(index, _)| index)
        .collect();
    (!slots.is_empty()).then_some(slots)
}

fn collect_joins(mut body: &IRBody, layouts: &mut HashMap<JoinPointId, Vec<usize>>) {
    loop {
        body = match body {
            IRBody::JDecl {
                jp,
                params,
                body,
                rest,
            } => {
                if let Some(slots) = void_slots(params) {
                    layouts.insert(*jp, slots);
                }
                collect_joins(body, layouts);
                rest
            }
            IRBody::Case { alts, default, .. } => {
                for alt in alts {
                    collect_joins(&alt.body, layouts);
                }
                if let Some(default) = default {
                    collect_joins(default, layouts);
                }
                return;
            }
            IRBody::VDecl { rest, .. }
            | IRBody::Inc { rest, .. }
            | IRBody::Dec { rest, .. }
            | IRBody::Set { rest, .. }
            | IRBody::SetTag { rest, .. }
            | IRBody::USet { rest, .. }
            | IRBody::SSet { rest, .. } => rest,
            IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => return,
        };
    }
}

fn erase_arguments(args: &mut Vec<IRArg>, slots: &[usize]) -> Result<(), IRError> {
    for &slot in slots {
        // The argument has already been compiled as a ghost. Dropping a
        // variable here could lose ownership or a still-needed carrier.
        if !matches!(args.get(slot), Some(IRArg::Erased)) {
            return Err(IRError::UnexpectedBodyForm {
                context: "physical Void argument is not erased",
            });
        }
    }
    for &slot in slots.iter().rev() {
        args.remove(slot);
    }
    Ok(())
}

fn erase_body(
    mut body: &mut IRBody,
    functions: &HashMap<Name, Vec<usize>>,
    joins: &HashMap<JoinPointId, Vec<usize>>,
) -> Result<(), IRError> {
    loop {
        body = match body {
            IRBody::VDecl { value, rest, .. } => {
                match value {
                    IRExpr::Apply { fn_id, args } => {
                        if let Some(slots) = functions.get(&fn_id.0) {
                            erase_arguments(args, slots)?;
                        }
                    }
                    IRExpr::PartialApply { fn_id, .. } if functions.contains_key(&fn_id.0) => {
                        return Err(IRError::UnexpectedBodyForm {
                            context: "partial application of Void function lacks a boxed adapter",
                        });
                    }
                    _ => {}
                }
                rest
            }
            IRBody::JDecl {
                jp,
                params,
                body,
                rest,
            } => {
                if let Some(slots) = joins.get(jp) {
                    for &slot in slots.iter().rev() {
                        params.remove(slot);
                    }
                }
                erase_body(body, functions, joins)?;
                rest
            }
            IRBody::Case { alts, default, .. } => {
                for alt in alts {
                    erase_body(&mut alt.body, functions, joins)?;
                }
                if let Some(default) = default {
                    erase_body(default, functions, joins)?;
                }
                return Ok(());
            }
            IRBody::Jmp { jp, args } => {
                if let Some(slots) = joins.get(jp) {
                    erase_arguments(args, slots)?;
                }
                return Ok(());
            }
            IRBody::Inc { rest, .. }
            | IRBody::Dec { rest, .. }
            | IRBody::Set { rest, .. }
            | IRBody::SetTag { rest, .. }
            | IRBody::USet { rest, .. }
            | IRBody::SSet { rest, .. } => rest,
            IRBody::Ret(_) | IRBody::Unreachable => return Ok(()),
        };
    }
}

pub(crate) fn erase_void_parameters(decls: &mut [IRDecl]) -> Result<(), IRError> {
    let functions: HashMap<_, _> = decls
        .iter()
        .filter_map(|decl| void_slots(&decl.params).map(|slots| (decl.name.clone(), slots)))
        .collect();
    let joins: Vec<_> = decls
        .iter()
        .map(|decl| {
            let mut layouts = HashMap::new();
            collect_joins(&decl.body, &mut layouts);
            layouts
        })
        .collect();
    if functions.is_empty() && joins.iter().all(HashMap::is_empty) {
        return Ok(());
    }

    check_decls(decls)?;
    for (decl, joins) in decls.iter_mut().zip(&joins) {
        if let Some(slots) = functions.get(&decl.name) {
            for &slot in slots.iter().rev() {
                decl.params.remove(slot);
            }
        }
        erase_body(&mut decl.body, &functions, joins)?;
    }
    check_decls(decls)
}

#[cfg(test)]
mod tests;
