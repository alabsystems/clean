// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A self tail call becomes a jump back to the top of its function (X4, R2).
//!
//! Lean compiles a self tail call as `goto _start` (`EmitC.emitTailCall`), so
//! a structurally recursive head loop runs in constant stack. Clean's final
//! L5IR expresses the same thing with what every backend already has: the
//! body becomes the body of a join point `loop` whose parameters stand for the
//! function's, the function enters it once (`jmp loop(params)`), and each
//! self tail call becomes a jump to it. The C emitter prints `_jpN:` and
//! `goto`, the Rust emitter `loop`/`continue`, trust-ir a branch back to a
//! block. No backend optimisation is relied on.
//!
//! # What is a candidate
//!
//! In L5IR every `ret` returns from the function, so a call is in tail
//! position exactly when its result is returned unchanged. A candidate is
//!
//! ```text
//! let x := apply self(a₁ … aₙ)   -- n = the function's arity
//! S₁; …; Sₖ                      -- each `inc v` or `dec v`, v ≠ x
//! ret x
//! ```
//!
//! and is rewritten to `S₁; …; Sₖ; jmp loop(a₁ … aₙ)`. Never a partial or a
//! closure application, a call to another function, or a call followed by
//! anything else (a box, a store, another binding).
//!
//! # Reference counts
//!
//! The pipeline's ABI is all-owned, so `S` releases what the frame still
//! holds after the call. Running `S` before the jump instead of after the
//! call is sound on reference-count-correct input: a `dec y` with `y` among
//! the arguments means the frame held at least two references at the call
//! (one handed to the callee, one released after), so one remains for the
//! next iteration. A site is refused (left a call) when
//!
//! * some `Sᵢ` is an `inc` of an argument (the callee would see a count the
//!   source never gave it), or
//! * an argument is a projection, directly or through further projections,
//!   of a `y` that `S` releases, with no `inc` of that argument on the path
//!   (releasing `y` first could free the field the next iteration reads).
//!
//! The output is re-checked by `verify_rc_linearity`, whose loop model is in
//! `rc_repair_linearity_back_edge.rs`.
//!
//! The pass runs in `compile_lcnf_decls_inner` only, after boxing (so scalar
//! loop parameters stay unboxed) and RC repair. It does not run in the Rust
//! ABI pipeline (`compile_lcnf_decls_at_rust_abi`), whose carrier signatures
//! and handles have other drop semantics (docs/DECISIONS.md).

use std::collections::{HashMap, HashSet};

use crate::ir::{FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, JoinPointId, VarId};

#[path = "tail_loop_vars.rs"]
mod vars;
use vars::{map_vars, max_var_id};

/// Rewrite every self tail call of every declaration into a loop. Returns
/// the number of call sites rewritten.
pub(crate) fn loop_self_tail_calls(decls: &mut [IRDecl]) -> usize {
    decls.iter_mut().map(loop_decl).sum()
}

/// Facts that hold on the path from the function's entry to a statement.
#[derive(Clone, Default)]
struct PathFacts {
    /// `x := proj[i] y` bindings: `x` → `y`.
    proj_parent: HashMap<VarId, VarId>,
    /// Variables `inc`ed on the path.
    inced: HashSet<VarId>,
}

struct Rewriter {
    self_fn: FnId,
    arity: usize,
    loop_jp: JoinPointId,
    sites: usize,
}

fn loop_decl(decl: &mut IRDecl) -> usize {
    let max_var = decl
        .params
        .iter()
        .map(|(v, _)| v.0)
        .max()
        .unwrap_or(0)
        .max(max_var_id(&decl.body));
    let loop_jp = JoinPointId(max_jp_id(&decl.body).map_or(0, |m| m + 1));
    let mut rewriter = Rewriter {
        self_fn: FnId(decl.name.clone()),
        arity: decl.params.len(),
        loop_jp,
        sites: 0,
    };
    let body = rewriter.body(&decl.body, PathFacts::default());
    if rewriter.sites == 0 {
        return 0;
    }
    let loop_params: Vec<(VarId, IRType)> = decl
        .params
        .iter()
        .zip(max_var + 1..)
        .map(|((_, ty), id)| (VarId(id), ty.clone()))
        .collect();
    let rename: HashMap<VarId, VarId> = decl
        .params
        .iter()
        .zip(&loop_params)
        .map(|((p, _), (q, _))| (*p, *q))
        .collect();
    decl.body = IRBody::JDecl {
        jp: loop_jp,
        params: loop_params,
        body: Box::new(map_vars(&body, &|v| *rename.get(&v).unwrap_or(&v))),
        rest: Box::new(IRBody::Jmp {
            jp: loop_jp,
            args: decl.params.iter().map(|(v, _)| IRArg::Var(*v)).collect(),
        }),
    };
    rewriter.sites
}

impl Rewriter {
    fn body(&mut self, body: &IRBody, mut facts: PathFacts) -> IRBody {
        match body {
            IRBody::VDecl {
                var,
                ty,
                value,
                rest,
            } => {
                if let Some(jump) = self.tail_site(*var, value, rest, &facts) {
                    self.sites += 1;
                    return jump;
                }
                if let IRExpr::Proj {
                    arg: IRArg::Var(parent),
                    ..
                } = value
                {
                    facts.proj_parent.insert(*var, *parent);
                }
                IRBody::VDecl {
                    var: *var,
                    ty: ty.clone(),
                    value: value.clone(),
                    rest: Box::new(self.body(rest, facts)),
                }
            }
            IRBody::JDecl {
                jp,
                params,
                body: jp_body,
                rest,
            } => IRBody::JDecl {
                jp: *jp,
                params: params.clone(),
                body: Box::new(self.body(jp_body, facts.clone())),
                rest: Box::new(self.body(rest, facts)),
            },
            IRBody::Inc { var, n, rest } => {
                facts.inced.insert(*var);
                IRBody::Inc {
                    var: *var,
                    n: *n,
                    rest: Box::new(self.body(rest, facts)),
                }
            }
            IRBody::Dec { var, rest } => IRBody::Dec {
                var: *var,
                rest: Box::new(self.body(rest, facts)),
            },
            IRBody::Set {
                var,
                idx,
                value,
                rest,
            } => IRBody::Set {
                var: *var,
                idx: *idx,
                value: *value,
                rest: Box::new(self.body(rest, facts)),
            },
            IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
                var: *var,
                tag: *tag,
                rest: Box::new(self.body(rest, facts)),
            },
            IRBody::USet {
                var,
                idx,
                value,
                rest,
            } => IRBody::USet {
                var: *var,
                idx: *idx,
                value: *value,
                rest: Box::new(self.body(rest, facts)),
            },
            IRBody::SSet {
                var,
                n,
                offset,
                value,
                ty,
                rest,
            } => IRBody::SSet {
                var: *var,
                n: *n,
                offset: *offset,
                value: *value,
                ty: ty.clone(),
                rest: Box::new(self.body(rest, facts)),
            },
            IRBody::Case {
                scrutinee,
                alts,
                default,
            } => IRBody::Case {
                scrutinee: *scrutinee,
                alts: alts
                    .iter()
                    .map(|alt| IRAlt {
                        ctor: alt.ctor.clone(),
                        body: Box::new(self.body(&alt.body, facts.clone())),
                    })
                    .collect(),
                default: default.as_ref().map(|d| Box::new(self.body(d, facts))),
            },
            IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => body.clone(),
        }
    }

    /// `S…; jmp loop(args)` when `let var := value; rest` is a candidate (see
    /// the module documentation), else `None`.
    fn tail_site(
        &self,
        var: VarId,
        value: &IRExpr,
        rest: &IRBody,
        facts: &PathFacts,
    ) -> Option<IRBody> {
        let IRExpr::Apply { fn_id, args } = value else {
            return None;
        };
        if *fn_id != self.self_fn || args.len() != self.arity {
            return None;
        }
        let mut released: Vec<VarId> = Vec::new();
        let mut cur = rest;
        loop {
            match cur {
                IRBody::Ret(IRArg::Var(v)) if *v == var => break,
                IRBody::Inc { var: v, rest, .. } if *v != var => {
                    if args.contains(&IRArg::Var(*v)) {
                        return None;
                    }
                    cur = rest;
                }
                IRBody::Dec { var: v, rest } if *v != var => {
                    released.push(*v);
                    cur = rest;
                }
                _ => return None,
            }
        }
        for arg in args {
            let IRArg::Var(a) = arg else { continue };
            if facts.inced.contains(a) {
                continue;
            }
            let mut seen = HashSet::new();
            let mut cur = *a;
            while let Some(parent) = facts.proj_parent.get(&cur) {
                if released.contains(parent) || !seen.insert(*parent) {
                    return None;
                }
                cur = *parent;
            }
        }
        Some(rebuild_releases(
            rest,
            var,
            IRBody::Jmp {
                jp: self.loop_jp,
                args: args.clone(),
            },
        ))
    }
}

/// The `inc`/`dec` prefix of `rest` (up to `ret var`) followed by `terminal`.
fn rebuild_releases(rest: &IRBody, var: VarId, terminal: IRBody) -> IRBody {
    match rest {
        IRBody::Inc { var: v, n, rest } if *v != var => IRBody::Inc {
            var: *v,
            n: *n,
            rest: Box::new(rebuild_releases(rest, var, terminal)),
        },
        IRBody::Dec { var: v, rest } if *v != var => IRBody::Dec {
            var: *v,
            rest: Box::new(rebuild_releases(rest, var, terminal)),
        },
        _ => terminal,
    }
}

/// The largest join-point id `body` declares or jumps to.
fn max_jp_id(body: &IRBody) -> Option<u32> {
    match body {
        IRBody::JDecl { jp, body, rest, .. } => [Some(jp.0), max_jp_id(body), max_jp_id(rest)]
            .into_iter()
            .flatten()
            .max(),
        IRBody::Case { alts, default, .. } => alts
            .iter()
            .map(|a| max_jp_id(&a.body))
            .chain(default.iter().map(|d| max_jp_id(d)))
            .flatten()
            .max(),
        IRBody::Jmp { jp, .. } => Some(jp.0),
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => max_jp_id(rest),
        IRBody::Ret(_) | IRBody::Unreachable => None,
    }
}
