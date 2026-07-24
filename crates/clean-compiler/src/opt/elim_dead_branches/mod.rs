// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dead Branch Elimination for L5CNF (ElimDeadBranches).
//!
//! Uses abstract interpretation to determine which constructors can reach
//! each variable, then eliminates case alternatives that are provably
//! unreachable. Based on Lean 4's `Lean.Compiler.LCNF.ElimDeadBranches`.
//!
//! # Algorithm
//!
//! 1. **Analysis phase:** Walk the code collecting a map from each FVarId
//!    to its abstract `Value` — the set of constructors that can flow there.
//!    - `LetValue::Ctor { name, .. }` assigns `Value::Ctor(name)`.
//!    - `LetValue::Lit(Nat(n))` is modeled as the Nat constructor chain.
//!    - Unknown values (function calls, projections, etc.) become `Value::Top`.
//!    - Join points and function parameters are conservatively `Value::Top`.
//!
//! 2. **Rewrite phase:** Walk the code with a `CodeFolder`:
//!    - At each `Cases`, look up the scrutinee's abstract value.
//!    - Remove `Alt::Ctor` alternatives whose constructor is not in the
//!      scrutinee's possible set (replace body with `Unreachable`).
//!    - If exactly one alternative remains reachable, inline its body
//!      directly (eliminating the entire `Cases` node).
//!
//! # Widening
//!
//! To guarantee termination without a full fixpoint loop (which Lean 4
//! needs for mutual recursion), this pass uses a single forward sweep
//! with conservative widening: any variable assigned more than once
//! (e.g., from multiple join-point paths) widens to `Top`.
//!
//! # Example
//!
//! Before:
//! ```text
//! let _0 := Bool.true
//! cases _0 of
//! | Bool.true => return _1
//! | Bool.false => return _2
//! ```
//!
//! After:
//! ```text
//! let _0 := Bool.true
//! return _1
//! ```
//!
//! Part of #1048 - ElimDeadBranches pass.

use crate::lcnf::{Alt, Cases, Code, Decl, DeclValue, LetValue};
use crate::CodeFolder;
use clean_kernel::{FVarId, Name};
use std::collections::HashMap;

// ═══════════════════════════════════════════════════════════════════════
// Abstract domain
// ═══════════════════════════════════════════════════════════════════════

/// Abstract value representing the set of constructors a variable can hold.
///
/// Mirrors Lean 4's `UnreachableBranches.Value` but without recursive
/// constructor argument tracking (which requires a fixpoint loop). This
/// simplified domain is sufficient for the common case: a `let` binding
/// of a known constructor followed by a `cases` on that binding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Value {
    /// No information yet (uninitialized). Neutral element of merge.
    Bot,
    /// All constructors possible — nothing can be eliminated.
    Top,
    /// Exactly one known constructor.
    Ctor(Name),
    /// A known set of possible constructors (from merging branches).
    Choice(Vec<Name>),
}

impl Value {
    /// Merge two abstract values (lattice join).
    ///
    /// - `Bot` is the neutral element.
    /// - `Top` is the annihilator.
    /// - Two `Ctor` values merge into `Choice` (or stay `Ctor` if equal).
    pub(crate) fn merge(self, other: Value) -> Value {
        match (self, other) {
            (Value::Bot, v) | (v, Value::Bot) => v,
            (Value::Top, _) | (_, Value::Top) => Value::Top,
            (Value::Ctor(a), Value::Ctor(b)) => {
                if a == b {
                    Value::Ctor(a)
                } else {
                    Value::Choice(vec![a, b])
                }
            }
            (Value::Choice(mut vs), Value::Ctor(c)) | (Value::Ctor(c), Value::Choice(mut vs)) => {
                if !vs.contains(&c) {
                    vs.push(c);
                }
                Value::Choice(vs)
            }
            (Value::Choice(mut vs1), Value::Choice(vs2)) => {
                for c in vs2 {
                    if !vs1.contains(&c) {
                        vs1.push(c);
                    }
                }
                Value::Choice(vs1)
            }
        }
    }

    /// Check whether a given constructor name is possible under this value.
    ///
    /// `Top` and `Bot` conservatively return `true` — we cannot prove
    /// the constructor is absent, so we keep the branch.
    pub(crate) fn contains_ctor(&self, ctor_name: &Name) -> bool {
        match self {
            Value::Top | Value::Bot => true,
            Value::Ctor(name) => name == ctor_name,
            Value::Choice(names) => names.contains(ctor_name),
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Analysis phase — collect abstract values for each FVarId
// ═══════════════════════════════════════════════════════════════════════

/// Abstract environment mapping FVarIds to their abstract values.
struct AbstractEnv {
    values: HashMap<FVarId, Value>,
}

impl AbstractEnv {
    fn new() -> Self {
        Self {
            values: HashMap::new(),
        }
    }

    /// Assign a value, merging with any existing assignment (widening).
    fn assign(&mut self, fvar: FVarId, value: Value) {
        self.values
            .entry(fvar)
            .and_modify(|existing| {
                let old = std::mem::replace(existing, Value::Bot);
                *existing = old.merge(value.clone());
            })
            .or_insert(value);
    }

    /// Look up the abstract value for an FVarId.
    fn get(&self, fvar: &FVarId) -> &Value {
        self.values.get(fvar).unwrap_or(&Value::Top)
    }
}

/// Compute the abstract value for a LetValue.
fn abstract_let_value(value: &LetValue, env: &AbstractEnv) -> Value {
    match value {
        LetValue::Ctor { name, .. } => Value::Ctor(name.clone()),
        LetValue::Lit(clean_kernel::Literal::Nat(n)) => {
            // Model small Nat literals as their constructor form.
            match n.to_u64() {
                Some(0) => Value::Ctor(Name::from_string("Nat.zero")),
                _ => Value::Ctor(Name::from_string("Nat.succ")),
            }
        }
        // FVar with no args: propagate the abstract value of the source.
        LetValue::FVar { fvar, args } if args.is_empty() => env.get(fvar).clone(),
        // Everything else is unknown.
        _ => Value::Top,
    }
}

/// Walk the code tree and populate the abstract environment.
fn analyze_code(code: &Code, env: &mut AbstractEnv) {
    match code {
        Code::Let(decl, body) => {
            let val = abstract_let_value(&decl.value, env);
            env.assign(decl.fvar_id, val);
            analyze_code(body, env);
        }
        Code::Fun(decl, body) | Code::JoinPoint(decl, body) => {
            // Function params are unknown from the caller's perspective.
            for p in &decl.params {
                env.assign(p.fvar_id, Value::Top);
            }
            analyze_code(&decl.body, env);
            analyze_code(body, env);
        }
        Code::Cases(cases) => {
            for alt in &cases.alts {
                match alt {
                    Alt::Ctor {
                        ctor_name,
                        params,
                        body,
                    } => {
                        // Constructor pattern params are unknown.
                        for p in params {
                            env.assign(p.fvar_id, Value::Top);
                        }
                        // If the scrutinee was Bot, refine with ctor info.
                        let scrutinee_val = env.get(&cases.scrutinee).clone();
                        if scrutinee_val == Value::Bot {
                            env.assign(cases.scrutinee, Value::Ctor(ctor_name.clone()));
                        }
                        analyze_code(body, env);
                    }
                    Alt::Default(body) => {
                        analyze_code(body, env);
                    }
                }
            }
        }
        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => {}
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Rewrite phase — eliminate dead branches using collected abstract values
// ═══════════════════════════════════════════════════════════════════════

/// CodeFolder that eliminates dead branches based on abstract interpretation.
struct ElimDeadBranchesFolder<'a> {
    env: &'a AbstractEnv,
}

impl CodeFolder for ElimDeadBranchesFolder<'_> {
    fn fold_cases(&mut self, cases: Cases) -> Code {
        let scrutinee_val = self.env.get(&cases.scrutinee);

        // Partition alternatives into reachable and dead.
        let mut reachable_alts: Vec<Alt> = Vec::new();
        for alt in cases.alts {
            match &alt {
                Alt::Ctor { ctor_name, .. } => {
                    if scrutinee_val.contains_ctor(ctor_name) {
                        reachable_alts.push(self.fold_alt(alt));
                    }
                    // else: dead — drop it
                }
                Alt::Default(_) => {
                    // Default is always reachable unless all ctors are known.
                    reachable_alts.push(self.fold_alt(alt));
                }
            }
        }

        // If no alternatives survive, this is unreachable.
        if reachable_alts.is_empty() {
            return Code::Unreachable(cases.result_type);
        }

        // If exactly one alternative survives, inline its body directly.
        if reachable_alts.len() == 1 {
            return match reachable_alts.into_iter().next() {
                Some(Alt::Ctor { body, .. }) => *body,
                Some(Alt::Default(body)) => *body,
                None => Code::Unreachable(cases.result_type),
            };
        }

        Code::Cases(Cases {
            type_name: cases.type_name,
            result_type: cases.result_type,
            scrutinee: cases.scrutinee,
            alts: reachable_alts,
        })
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Public API
// ═══════════════════════════════════════════════════════════════════════

/// Eliminate dead branches in a Code block.
///
/// Runs abstract interpretation to determine which constructors can
/// flow to each variable, then removes case alternatives whose
/// constructors are provably absent from the scrutinee's value set.
#[must_use]
pub fn elim_dead_branches_in_code(code: &Code) -> Code {
    let mut env = AbstractEnv::new();
    analyze_code(code, &mut env);
    ElimDeadBranchesFolder { env: &env }.fold_code(code)
}

/// Eliminate dead branches in a declaration.
#[must_use]
pub fn elim_dead_branches(decl: &Decl) -> Decl {
    let body = match &decl.body {
        DeclValue::Code(code) => DeclValue::Code(Box::new(elim_dead_branches_in_code(code))),
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

#[cfg(test)]
mod tests;
