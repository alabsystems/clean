// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Sibling-call replacement (design §5.3 step 6, last two bullets).
//!
//! In a specialized minor — the owner's body with its major premise replaced
//! by `c params y⃗` — a call `F_g fixed… y rest…` whose major argument is a
//! field `y` of `c` in the slot `g` owns becomes `ih_y rest…`: the induction
//! hypothesis for `y`, whose type is `g`'s own type with the major premise
//! instantiated at `y` (the motive), so the replacement preserves the call's
//! type.
//!
//! When the slot is SHARED (several members own it, brick B2) the hypothesis
//! is a tuple and the call reads its callee's component; when the field is a
//! transparent intermediate (`hd : String × T`), a call on `hd.2` reads the
//! component of `hd`'s hypothesis that covers field 2.
//!
//! EVERY other occurrence of a forward local is refused — a major argument that
//! is not a field (the major premise itself, a compound term, a variable bound
//! inside the body), a field of a slot `g` does not own, a call missing its
//! major argument, an unapplied reference. That is the termination argument:
//! a surviving call is on a strict subterm of the major premise.

use clean_kernel::{Expr, ExprFolder, ExprKind, FVarId, Name};

use super::motives::SlotPlan;
use super::specialize::strip_mdata;
use super::tuple::TupleKind;

/// How a member is called: its forward local and its parameter layout.
#[derive(Debug, Clone)]
pub(super) struct CallShape {
    pub(super) name: Name,
    pub(super) fvar: FVarId,
    /// Number of opened parameters.
    pub(super) arity: usize,
    /// Index of the major premise among them.
    pub(super) major: usize,
    /// The recursor slot the member owns.
    pub(super) slot: usize,
    /// Its position among the slot's owners, and their number.
    pub(super) owner_index: usize,
    pub(super) owner_count: usize,
}

/// A recursive field of the current minor with its induction hypothesis.
#[derive(Debug, Clone, Copy)]
pub(super) struct FieldIh {
    pub(super) field: FVarId,
    pub(super) slot: usize,
    pub(super) ih: FVarId,
}

/// Why a call could not be replaced, with the offending call.
#[derive(Debug, Clone)]
pub(super) struct CallRefusal {
    pub(super) callee: Name,
    pub(super) call: Expr,
    pub(super) reason: String,
}

pub(super) struct IhReplacer<'a> {
    pub(super) members: &'a [CallShape],
    pub(super) fixed: &'a [FVarId],
    pub(super) fields: &'a [FieldIh],
    pub(super) plans: &'a [SlotPlan],
    pub(super) kind: &'a TupleKind,
    /// The constructor application that replaced the caller's major premise.
    pub(super) major_premise: &'a Expr,
    pub(super) refusal: Option<CallRefusal>,
}

impl IhReplacer<'_> {
    fn refuse(&mut self, callee: &CallShape, call: Expr, reason: String) -> Expr {
        if self.refusal.is_none() {
            self.refusal = Some(CallRefusal {
                callee: callee.name.clone(),
                call: call.clone(),
                reason,
            });
        }
        call
    }

    fn member_of(&self, id: FVarId) -> Option<&CallShape> {
        self.members.iter().find(|member| member.fvar == id)
    }

    /// The induction hypothesis covering `arg` and the slot it is for, or
    /// what `arg` is instead.
    fn resolve(&self, arg: &Expr) -> Result<(Expr, usize), String> {
        let arg = strip_mdata(arg);
        if arg == strip_mdata(self.major_premise) {
            return Err("the major premise itself, not a strict subterm of it".to_string());
        }
        match arg.kind() {
            ExprKind::FVar(id) => self
                .fields
                .iter()
                .find(|f| f.field == *id)
                .map(|f| (Expr::fvar(f.ih), f.slot))
                .ok_or_else(|| {
                    "a variable that is not a constructor field of the major premise".to_string()
                }),
            ExprKind::BVar(_) => Err(
                "a variable bound inside the body, not a constructor field of the major premise"
                    .to_string(),
            ),
            ExprKind::Proj(struct_name, idx, inner) => {
                let (base, slot) = self.resolve(inner).map_err(|_| {
                    "a compound term, not a constructor field of the major premise".to_string()
                })?;
                match &self.plans[slot] {
                    SlotPlan::Intermediate {
                        struct_name: s,
                        components,
                    } if s == struct_name => {
                        let Some(j) = components.iter().position(|(f, _)| *f == *idx as usize)
                        else {
                            return Err(format!(
                                "field {} of a `{struct_name}`, which holds no value the \
                                 recursion covers",
                                idx + 1
                            ));
                        };
                        Ok((
                            self.kind.project(base, j, components.len()),
                            components[j].1,
                        ))
                    }
                    SlotPlan::Unit {
                        reason: Some(reason),
                    } => Err(format!("a projection of a field, but {reason}")),
                    _ => Err(
                        "a projection of a field whose type is not a transparent intermediate"
                            .to_string(),
                    ),
                }
            }
            _ => Err("a compound term, not a constructor field of the major premise".to_string()),
        }
    }

    fn replace_call(&mut self, callee: &CallShape, args: Vec<Expr>) -> Expr {
        let call = Expr::apps(Expr::fvar(callee.fvar), args.iter().cloned());
        if args.len() <= callee.major {
            return self.refuse(
                callee,
                call,
                "the call does not supply the argument the recursion is on".to_string(),
            );
        }
        for (pos, fixed) in self.fixed.iter().enumerate() {
            if strip_mdata(&args[pos]) != &Expr::fvar(*fixed) {
                return self.refuse(
                    callee,
                    call,
                    format!(
                        "argument {} is not the block's fixed parameter passed unchanged",
                        pos + 1
                    ),
                );
            }
        }
        let major_arg = strip_mdata(&args[callee.major]);
        let (hypothesis, slot) = match self.resolve(major_arg) {
            Ok(found) => found,
            Err(what) => {
                return self.refuse(
                    callee,
                    call,
                    format!("the argument the recursion is on is {what}"),
                )
            }
        };
        if slot != callee.slot {
            return self.refuse(
                callee,
                call,
                "the argument the recursion is on is a field whose type the callee does not \
                 recurse on"
                    .to_string(),
            );
        }
        let mut out = self
            .kind
            .project(hypothesis, callee.owner_index, callee.owner_count);
        let opened = args.len().min(callee.arity);
        for (pos, arg) in args.iter().enumerate().take(opened) {
            if pos >= self.fixed.len() && pos != callee.major {
                out = Expr::app(out, arg.clone());
            }
        }
        Expr::apps(out, args[opened..].iter().cloned())
    }
}

impl ExprFolder for IhReplacer<'_> {
    fn fold_app(&mut self, f: &Expr, a: &Expr) -> Expr {
        let whole = Expr::app(f.clone(), a.clone());
        let head = strip_mdata(whole.get_app_fn()).clone();
        if let ExprKind::FVar(id) = head.kind() {
            if let Some(callee) = self.member_of(*id).cloned() {
                let args: Vec<Expr> = whole
                    .get_app_args()
                    .into_iter()
                    .map(|arg| self.fold_expr(arg))
                    .collect();
                return self.replace_call(&callee, args);
            }
        }
        Expr::app(self.fold_expr(f), self.fold_expr(a))
    }

    fn fold_fvar(&mut self, id: FVarId) -> Expr {
        if let Some(callee) = self.member_of(id).cloned() {
            return self.refuse(
                &callee,
                Expr::fvar(id),
                "the member is referenced without being applied".to_string(),
            );
        }
        Expr::fvar(id)
    }
}
