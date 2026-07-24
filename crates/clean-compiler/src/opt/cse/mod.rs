// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Common Subexpression Elimination (CSE) for L5CNF
//!
//! Identifies and eliminates redundant computations by reusing
//! previously computed values.
//!
//! # Algorithm
//!
//! 1. Walk the code, building a map of (normalized LetValue) -> FVarId
//! 2. When we encounter a let-binding with a value we've seen before,
//!    replace uses of the new binding with the previous one
//! 3. DCE will then remove the redundant binding
//!
//! # Normalization
//!
//! For CSE to be effective, we normalize let-values by converting them
//! to a hashable representation. Type arguments are skipped (prevent CSE)
//! since type-level computations may have different semantics.
//!
//! Note: Commutative operations are NOT currently normalized (e.g., `add x y`
//! won't match `add y x`). This could be added in the future by sorting
//! arguments for known commutative operations.
//!
//! Part of #963 - Compiler IR infrastructure.

mod subst;

use crate::lcnf::{Alt, Arg, Cases, Code, Decl, DeclValue, FunDecl, LetDecl, LetValue};
use crate::CodeFolder;
use clean_kernel::{Expr, FVarId, Level};
use std::collections::HashMap;

use subst::{
    apply_subst_to_args, apply_subst_to_expr, apply_subst_to_params, apply_subst_to_value,
};

/// A normalized let-value for CSE comparison.
///
/// We use a separate type because LetValue contains Expr which doesn't
/// implement Hash/Eq in a useful way.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum NormalizedValue {
    /// Literal Nat
    LitNat(u64),
    /// Literal String
    LitString(String),
    /// Erased
    Erased,
    /// Projection
    Proj {
        type_name: String,
        idx: u32,
        structure: FVarId,
    },
    /// Constant application (includes universe levels for correctness)
    /// Uses Level directly since it implements Hash/Eq (level.rs:44)
    Const {
        name: String,
        levels: Vec<Level>,
        args: Vec<NormalizedArg>,
    },
    /// FVar application
    FVar {
        fvar: FVarId,
        args: Vec<NormalizedArg>,
    },
    /// Constructor (includes universe levels for correctness)
    /// Uses Level directly since it implements Hash/Eq (level.rs:44)
    Ctor {
        name: String,
        levels: Vec<Level>,
        args: Vec<NormalizedArg>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum NormalizedArg {
    Erased,
    FVar(FVarId),
    // Type args are not CSE-able
}

/// Normalize a let-value for CSE comparison.
fn normalize_let_value(value: &LetValue) -> Option<NormalizedValue> {
    match value {
        LetValue::Lit(clean_kernel::Literal::Nat(n)) => Some(NormalizedValue::LitNat(n.to_u64()?)),
        LetValue::Lit(clean_kernel::Literal::String(s)) => {
            Some(NormalizedValue::LitString(s.to_string()))
        }
        LetValue::Erased => Some(NormalizedValue::Erased),
        LetValue::Proj {
            type_name,
            idx,
            structure,
        } => Some(NormalizedValue::Proj {
            type_name: type_name.to_string(),
            idx: *idx,
            structure: *structure,
        }),
        LetValue::Const { name, levels, args } => {
            let norm_args = normalize_args(args)?;
            Some(NormalizedValue::Const {
                name: name.to_string(),
                levels: levels.clone(),
                args: norm_args,
            })
        }
        LetValue::FVar { fvar, args } => {
            let norm_args = normalize_args(args)?;
            Some(NormalizedValue::FVar {
                fvar: *fvar,
                args: norm_args,
            })
        }
        LetValue::Ctor { name, levels, args } => {
            let norm_args = normalize_args(args)?;
            Some(NormalizedValue::Ctor {
                name: name.to_string(),
                levels: levels.clone(),
                args: norm_args,
            })
        }
        // Reuse is not CSE-able: it has side-effects (may mutate or allocate)
        LetValue::Reuse { .. } => None,
    }
}

/// Normalize arguments.
fn normalize_args(args: &[Arg]) -> Option<Vec<NormalizedArg>> {
    args.iter()
        .map(|arg| match arg {
            Arg::Erased => Some(NormalizedArg::Erased),
            Arg::FVar(id) => Some(NormalizedArg::FVar(*id)),
            Arg::Type(_) | Arg::Index(_) => None, // Type/Index args prevent CSE
        })
        .collect()
}

/// Context for CSE.
struct CseContext {
    /// Map from normalized value to the FVarId that holds it.
    available: HashMap<NormalizedValue, FVarId>,
    /// Substitution map: replace this FVarId with that one.
    subst: HashMap<FVarId, FVarId>,
    /// Undo trail for `available` inserts within a nested scope.
    available_trail: Vec<(NormalizedValue, Option<FVarId>)>,
    /// Undo trail for `subst` inserts within a nested scope.
    subst_trail: Vec<(FVarId, Option<FVarId>)>,
}

#[derive(Copy, Clone)]
struct CseCheckpoint {
    available_trail_len: usize,
    subst_trail_len: usize,
}

impl CseContext {
    fn new() -> Self {
        Self {
            available: HashMap::new(),
            subst: HashMap::new(),
            available_trail: Vec::new(),
            subst_trail: Vec::new(),
        }
    }

    /// Look up a value to see if it's already computed.
    fn lookup(&self, value: &LetValue) -> Option<FVarId> {
        let norm = normalize_let_value(value)?;
        self.available.get(&norm).copied()
    }

    /// Record that a value is available at a given FVarId.
    fn record(&mut self, fvar: FVarId, value: &LetValue) {
        if let Some(norm) = normalize_let_value(value) {
            let old = self.available.insert(norm.clone(), fvar);
            self.available_trail.push((norm, old));
        }
    }

    /// Get the canonical FVarId for a given FVarId (after substitutions).
    fn canonical(&self, fvar: FVarId) -> FVarId {
        let mut current = fvar;
        let mut steps = 0;
        while let Some(next) = self.subst.get(&current).copied() {
            if next == current {
                break;
            }
            current = next;
            steps += 1;
            if steps > self.subst.len() {
                break;
            }
        }
        current
    }

    /// Record an FVar substitution produced by a CSE hit.
    fn record_subst(&mut self, from: FVarId, to: FVarId) {
        let old = self.subst.insert(from, to);
        self.subst_trail.push((from, old));
    }

    /// Save the current scope so mutations can be reverted without cloning maps.
    fn checkpoint(&self) -> CseCheckpoint {
        CseCheckpoint {
            available_trail_len: self.available_trail.len(),
            subst_trail_len: self.subst_trail.len(),
        }
    }

    /// Restore the context to a previously saved scope.
    fn restore(&mut self, checkpoint: CseCheckpoint) {
        while self.available_trail.len() > checkpoint.available_trail_len {
            let (norm, old) = self
                .available_trail
                .pop()
                .expect("available trail length checked before pop");
            if let Some(prev) = old {
                self.available.insert(norm, prev);
            } else {
                self.available.remove(&norm);
            }
        }
        while self.subst_trail.len() > checkpoint.subst_trail_len {
            let (fvar, old) = self
                .subst_trail
                .pop()
                .expect("subst trail length checked before pop");
            if let Some(prev) = old {
                self.subst.insert(fvar, prev);
            } else {
                self.subst.remove(&fvar);
            }
        }
    }
}

/// Eliminate common subexpressions from a declaration.
pub fn eliminate_common_subexpressions(decl: &Decl) -> Decl {
    let body = match &decl.body {
        DeclValue::Code(code) => {
            let mut ctx = CseContext::new();
            DeclValue::Code(Box::new(CseFolder { ctx: &mut ctx }.fold_code(code)))
        }
        DeclValue::Extern(attr) => DeclValue::Extern(attr.clone()),
    };

    Decl {
        name: decl.name.clone(),
        level_params: decl.level_params.clone(),
        ty: decl.ty.clone(),
        params: decl.params.clone(),
        body,
        recursive: decl.recursive,
    }
}

/// Eliminate common subexpressions from a Code block directly.
///
/// Use this when applying CSE to code outside of a Decl context,
/// such as during pass composition or testing. For full declarations,
/// prefer [`eliminate_common_subexpressions`] which handles the full Decl.
pub fn eliminate_common_subexpressions_in_code(code: &Code) -> Code {
    let mut ctx = CseContext::new();
    CseFolder { ctx: &mut ctx }.fold_code(code)
}

/// CodeFolder implementation for common subexpression elimination.
struct CseFolder<'a> {
    ctx: &'a mut CseContext,
}

impl CseFolder<'_> {
    /// CSE for a scoped function body (Fun or JoinPoint).
    ///
    /// Saves and restores context so substitutions inside the function
    /// body don't leak into the surrounding scope.
    fn fold_scoped_fun(&mut self, fun_decl: FunDecl) -> FunDecl {
        let checkpoint = self.ctx.checkpoint();
        let new_fun_body = self.fold_code(&fun_decl.body);
        self.ctx.restore(checkpoint);

        FunDecl {
            fvar_id: fun_decl.fvar_id,
            name: fun_decl.name,
            params: apply_subst_to_params(&fun_decl.params, self.ctx),
            ty: apply_subst_to_expr(&fun_decl.ty, self.ctx),
            body: Box::new(new_fun_body),
        }
    }
}

impl CodeFolder for CseFolder<'_> {
    /// Iterative traversal of sequential Let chains to prevent stack overflow.
    ///
    /// LCNF represents function bodies as linked lists of `Code::Let(decl, body)`
    /// nodes. The default recursive `fold_code` creates O(N) stack depth for N
    /// let bindings, which overflows on large functions (e.g., 1600+ bindings).
    /// This override iterates through the Let chain and only recurses for
    /// non-sequential structures (Fun, JoinPoint, Cases) which are bounded by
    /// branching depth rather than function length.
    fn fold_code(&mut self, code: &Code) -> Code {
        let mut pending_lets: Vec<LetDecl> = Vec::new();
        let mut current = code;

        loop {
            match current {
                Code::Let(decl, body) => {
                    let new_value = apply_subst_to_value(&decl.value, self.ctx);

                    if let Some(existing) = self.ctx.lookup(&new_value) {
                        // CSE hit: record substitution, skip this let binding
                        self.ctx.record_subst(decl.fvar_id, existing);
                    } else {
                        // CSE miss: keep this let binding
                        self.ctx.record(decl.fvar_id, &new_value);
                        pending_lets.push(LetDecl {
                            fvar_id: decl.fvar_id,
                            name: decl.name.clone(),
                            ty: apply_subst_to_expr(&decl.ty, self.ctx),
                            value: new_value,
                        });
                    }
                    current = body;
                }
                // Non-Let nodes: dispatch to per-variant fold methods (bounded recursion)
                other => {
                    let mut result = match other {
                        Code::Fun(decl, body) => self.fold_fun(decl.clone(), *body.clone()),
                        Code::JoinPoint(decl, body) => {
                            self.fold_join_point(decl.clone(), *body.clone())
                        }
                        Code::Cases(cases) => self.fold_cases(cases.clone()),
                        Code::Jmp { jp, args } => self.fold_jmp(*jp, args.clone()),
                        Code::Return(fvar) => self.fold_return(*fvar),
                        Code::Unreachable(ty) => self.fold_unreachable(ty.clone()),
                        Code::Let(..) => unreachable!("Let nodes consumed by pending_lets above"),
                    };

                    // Rebuild the let chain from inside out
                    for decl in pending_lets.into_iter().rev() {
                        result = Code::Let(decl, Box::new(result));
                    }
                    return result;
                }
            }
        }
    }

    fn fold_fun(&mut self, decl: FunDecl, body: Code) -> Code {
        let new_decl = self.fold_scoped_fun(decl);
        Code::Fun(new_decl, Box::new(self.fold_code(&body)))
    }

    fn fold_join_point(&mut self, decl: FunDecl, body: Code) -> Code {
        let new_decl = self.fold_scoped_fun(decl);
        Code::JoinPoint(new_decl, Box::new(self.fold_code(&body)))
    }

    fn fold_cases(&mut self, cases: Cases) -> Code {
        let Cases {
            type_name,
            result_type,
            scrutinee,
            alts,
        } = cases;
        let new_scrutinee = self.ctx.canonical(scrutinee);
        let checkpoint = self.ctx.checkpoint();

        let mut new_alts = Vec::with_capacity(alts.len());
        for alt in &alts {
            self.ctx.restore(checkpoint);
            let result = match alt {
                Alt::Ctor {
                    ctor_name,
                    params,
                    body,
                } => Alt::Ctor {
                    ctor_name: ctor_name.clone(),
                    params: apply_subst_to_params(params, self.ctx),
                    body: Box::new(self.fold_code(body)),
                },
                Alt::Default(body) => Alt::Default(Box::new(self.fold_code(body))),
            };
            new_alts.push(result);
        }
        self.ctx.restore(checkpoint);

        Code::Cases(Cases {
            type_name,
            result_type: apply_subst_to_expr(&result_type, self.ctx),
            scrutinee: new_scrutinee,
            alts: new_alts,
        })
    }

    fn fold_jmp(&mut self, jp: FVarId, args: Vec<Arg>) -> Code {
        Code::Jmp {
            jp: self.ctx.canonical(jp),
            args: apply_subst_to_args(&args, self.ctx),
        }
    }

    fn fold_return(&mut self, fvar: FVarId) -> Code {
        Code::Return(self.ctx.canonical(fvar))
    }

    fn fold_unreachable(&mut self, ty: Expr) -> Code {
        Code::Unreachable(apply_subst_to_expr(&ty, self.ctx))
    }
}

#[cfg(test)]
mod tests;
