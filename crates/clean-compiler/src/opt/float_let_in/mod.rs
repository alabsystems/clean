// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! FloatLetIn — sink let-bindings closer to their use sites.
//!
//! Moves let-bindings that are defined before a `Cases` node into the specific
//! case arm where they are used, reducing live variable ranges and avoiding
//! unnecessary computation in arms that don't use the binding.
//!
//! Based on Lean 4's `src/Lean/Compiler/LCNF/FloatLetIn.lean` by Henrik Boving.
//!
//! # Algorithm
//!
//! 1. Walk the code top-down, collecting let/fun/join-point declarations as
//!    "candidates" for floating.
//! 2. When a `Cases` node is reached, classify each candidate:
//!    - `Dont`: used in multiple arms, or is the scrutinee — keep above the cases
//!    - `Arm(i)`: used only in arm `i` — float into that arm
//!    - `Unknown`: not used in any arm — dead code, drop it (DCE catches this too)
//! 3. For candidates classified into an arm, transitively pull their
//!    dependencies into the same arm (or escalate to `Dont` on conflict).
//! 4. Recursively process function/join-point bodies and case arms.
//!
//! # Example
//!
//! Before:
//! ```text
//! let _1 := expensive_computation
//! let _2 := 42
//! cases _0 of
//! | True  => return _1
//! | False => return _2
//! ```
//!
//! After:
//! ```text
//! cases _0 of
//! | True  =>
//!   let _1 := expensive_computation
//!   return _1
//! | False =>
//!   let _2 := 42
//!   return _2
//! ```
//!
//! Part of #1049 - FloatLetIn compiler pass.

use crate::lcnf::{Alt, Arg, Code, Decl, DeclValue, FunDecl, LetDecl, LetValue};
use clean_kernel::FVarId;
use std::collections::{HashMap, HashSet};

// ════════════════════════════════════════════════════════════════════════════
// Candidate Declarations
// ════════════════════════════════════════════════════════════════════════════

/// A declaration collected as a candidate for floating.
#[derive(Clone)]
enum Candidate {
    Let(LetDecl),
    Fun(FunDecl),
    JoinPoint(FunDecl),
}

impl Candidate {
    fn fvar_id(&self) -> FVarId {
        match self {
            Candidate::Let(d) => d.fvar_id,
            Candidate::Fun(d) | Candidate::JoinPoint(d) => d.fvar_id,
        }
    }

    /// Collect FVarIds referenced by this declaration's value/body.
    fn free_vars(&self) -> HashSet<FVarId> {
        match self {
            Candidate::Let(d) => {
                let mut out = HashSet::new();
                collect_fvars_in_let_value(&d.value, &mut out);
                out
            }
            Candidate::Fun(d) | Candidate::JoinPoint(d) => {
                let mut out = HashSet::new();
                collect_fvars_in_code(&d.body, &mut out);
                for p in &d.params {
                    out.remove(&p.fvar_id);
                }
                out.remove(&d.fvar_id);
                out
            }
        }
    }

    /// Wrap continuation code with this declaration.
    fn attach(self, body: Code) -> Code {
        match self {
            Candidate::Let(d) => Code::Let(d, Box::new(body)),
            Candidate::Fun(d) => Code::Fun(d, Box::new(body)),
            Candidate::JoinPoint(d) => Code::JoinPoint(d, Box::new(body)),
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Decision
// ════════════════════════════════════════════════════════════════════════════

/// Where to place a candidate declaration relative to a Cases node.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Decision {
    /// Float into case arm at index `i`.
    Arm(usize),
    /// Keep above the Cases (used in multiple arms or is the scrutinee).
    Dont,
    /// Not used in any arm — can be dropped.
    Unknown,
}

// ════════════════════════════════════════════════════════════════════════════
// FVar Collection Helpers
// ════════════════════════════════════════════════════════════════════════════

fn collect_fvars_in_let_value(value: &LetValue, out: &mut HashSet<FVarId>) {
    match value {
        LetValue::Lit(_) | LetValue::Erased => {}
        LetValue::Proj { structure, .. } => {
            out.insert(*structure);
        }
        LetValue::Const { args, .. } | LetValue::Ctor { args, .. } => {
            for arg in args {
                collect_fvar_in_arg(arg, out);
            }
        }
        LetValue::FVar { fvar, args } => {
            out.insert(*fvar);
            for arg in args {
                collect_fvar_in_arg(arg, out);
            }
        }
        LetValue::Reuse { slot, args, .. } => {
            out.insert(*slot);
            for arg in args {
                collect_fvar_in_arg(arg, out);
            }
        }
    }
}

fn collect_fvar_in_arg(arg: &Arg, out: &mut HashSet<FVarId>) {
    if let Arg::FVar(fvar) = arg {
        out.insert(*fvar);
    }
}

/// Collect all FVarIds referenced in a Code block.
fn collect_fvars_in_code(code: &Code, out: &mut HashSet<FVarId>) {
    match code {
        Code::Return(fvar) => {
            out.insert(*fvar);
        }
        Code::Let(decl, body) => {
            collect_fvars_in_let_value(&decl.value, out);
            collect_fvars_in_code(body, out);
        }
        Code::Fun(fun_decl, body) | Code::JoinPoint(fun_decl, body) => {
            collect_fvars_in_code(&fun_decl.body, out);
            collect_fvars_in_code(body, out);
        }
        Code::Cases(cases) => {
            out.insert(cases.scrutinee);
            for alt in &cases.alts {
                match alt {
                    Alt::Ctor { body, .. } => collect_fvars_in_code(body, out),
                    Alt::Default(body) => collect_fvars_in_code(body, out),
                }
            }
        }
        Code::Jmp { jp, args } => {
            out.insert(*jp);
            for arg in args {
                collect_fvar_in_arg(arg, out);
            }
        }
        Code::Unreachable(_) => {}
    }
}

/// Collect all FVarIds referenced in a single case alternative.
fn collect_fvars_in_alt(alt: &Alt) -> HashSet<FVarId> {
    let mut out = HashSet::new();
    match alt {
        Alt::Ctor { body, .. } => collect_fvars_in_code(body, &mut out),
        Alt::Default(body) => collect_fvars_in_code(body, &mut out),
    }
    out
}

// ════════════════════════════════════════════════════════════════════════════
// Initial Decision Computation
// ════════════════════════════════════════════════════════════════════════════

/// Compute initial decisions for each candidate based on which arms use them.
///
/// For each candidate FVarId, scan every arm. If the FVarId appears in exactly
/// one arm, mark it `Arm(i)`. If it appears in multiple arms, mark it `Dont`.
/// If it appears in no arm, mark it `Unknown`. The scrutinee is always `Dont`.
fn compute_initial_decisions(
    candidates: &[Candidate],
    arm_fvars: &[HashSet<FVarId>],
    scrutinee: FVarId,
) -> HashMap<FVarId, Decision> {
    let mut decisions = HashMap::with_capacity(candidates.len());

    for candidate in candidates {
        let fvar = candidate.fvar_id();
        if fvar == scrutinee {
            decisions.insert(fvar, Decision::Dont);
            continue;
        }

        let mut decision = Decision::Unknown;
        for (arm_idx, arm_set) in arm_fvars.iter().enumerate() {
            if arm_set.contains(&fvar) {
                match decision {
                    Decision::Unknown => decision = Decision::Arm(arm_idx),
                    Decision::Arm(prev) if prev == arm_idx => {}
                    _ => {
                        decision = Decision::Dont;
                        break;
                    }
                }
            }
        }

        decisions.insert(fvar, decision);
    }

    decisions
}

// ════════════════════════════════════════════════════════════════════════════
// Decision Refinement
// ════════════════════════════════════════════════════════════════════════════

/// Refine decisions: propagate constraints from candidate dependencies.
///
/// Process candidates bottom-up (reverse order). For each candidate assigned
/// to an arm, ensure all of its dependency candidates are also assigned to the
/// same arm or `Dont`. If a dependency is `Unknown`, assign it to the same arm.
/// If a dependency is assigned to a different arm, escalate it to `Dont`.
fn refine_decisions(candidates: &[Candidate], decisions: &mut HashMap<FVarId, Decision>) {
    let candidate_set: HashSet<FVarId> = candidates.iter().map(|c| c.fvar_id()).collect();

    // Iterate from bottom (last candidate) to top (first candidate).
    // This ensures that when we process a candidate, all candidates that
    // come after it (and might depend on it) have already been processed.
    let mut changed = true;
    // Fixed-point iteration for transitive dependency propagation.
    while changed {
        changed = false;
        for candidate in candidates.iter().rev() {
            let fvar = candidate.fvar_id();
            let current = match decisions.get(&fvar) {
                Some(d) => d.clone(),
                None => continue,
            };

            // Only propagate from candidates assigned to an arm.
            let arm_idx = match &current {
                Decision::Arm(i) => *i,
                Decision::Dont => {
                    // A `Dont` candidate forces its dependencies to `Dont` too.
                    propagate_dont(candidate, &candidate_set, decisions, &mut changed);
                    continue;
                }
                Decision::Unknown => continue,
            };

            // For each FVar this candidate depends on, if it's also a candidate,
            // ensure it's assigned to the same arm.
            let deps = candidate.free_vars();
            for dep_fvar in &deps {
                if !candidate_set.contains(dep_fvar) {
                    continue;
                }
                match decisions.get(dep_fvar) {
                    Some(Decision::Unknown) => {
                        decisions.insert(*dep_fvar, Decision::Arm(arm_idx));
                        changed = true;
                    }
                    Some(Decision::Arm(other)) if *other != arm_idx => {
                        decisions.insert(*dep_fvar, Decision::Dont);
                        changed = true;
                    }
                    _ => {}
                }
            }
        }
    }
}

/// When a candidate is `Dont`, force all its candidate-dependencies to `Dont` too.
fn propagate_dont(
    candidate: &Candidate,
    candidate_set: &HashSet<FVarId>,
    decisions: &mut HashMap<FVarId, Decision>,
    changed: &mut bool,
) {
    let deps = candidate.free_vars();
    for dep_fvar in &deps {
        if !candidate_set.contains(dep_fvar) {
            continue;
        }
        if let Some(d) = decisions.get(dep_fvar) {
            if *d != Decision::Dont {
                decisions.insert(*dep_fvar, Decision::Dont);
                *changed = true;
            }
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Rebuild Code
// ════════════════════════════════════════════════════════════════════════════

/// Attach a list of candidates (in order) before `code`.
fn attach_candidates(candidates: Vec<Candidate>, code: Code) -> Code {
    let mut result = code;
    for candidate in candidates.into_iter().rev() {
        result = candidate.attach(result);
    }
    result
}

/// Float candidates into a Cases node and rebuild.
///
/// Distributes candidates into their assigned arms, keeps `Dont` candidates
/// above the cases, and drops `Unknown` candidates (dead code).
fn float_into_cases(
    candidates: Vec<Candidate>,
    cases: &crate::lcnf::Cases,
    decisions: &HashMap<FVarId, Decision>,
) -> Code {
    let num_alts = cases.alts.len();

    // Partition candidates by decision.
    let mut dont_candidates: Vec<Candidate> = Vec::new();
    let mut arm_candidates: Vec<Vec<Candidate>> = vec![Vec::new(); num_alts];

    for candidate in candidates {
        match decisions.get(&candidate.fvar_id()) {
            Some(Decision::Dont) => dont_candidates.push(candidate),
            Some(Decision::Arm(i)) => arm_candidates[*i].push(candidate),
            Some(Decision::Unknown) | None => {
                // Dead code — drop it. DCE would also catch this.
            }
        }
    }

    // Build new alternatives with floated candidates prepended.
    let new_alts: Vec<Alt> = cases
        .alts
        .iter()
        .enumerate()
        .map(|(i, alt)| {
            let arm_decls = std::mem::take(&mut arm_candidates[i]);
            match alt {
                Alt::Ctor {
                    ctor_name,
                    params,
                    body,
                } => {
                    let new_body = float_let_in_code(body);
                    let new_body = attach_candidates(arm_decls, new_body);
                    Alt::Ctor {
                        ctor_name: ctor_name.clone(),
                        params: params.clone(),
                        body: Box::new(new_body),
                    }
                }
                Alt::Default(body) => {
                    let new_body = float_let_in_code(body);
                    let new_body = attach_candidates(arm_decls, new_body);
                    Alt::Default(Box::new(new_body))
                }
            }
        })
        .collect();

    let new_cases = Code::Cases(crate::lcnf::Cases {
        type_name: cases.type_name.clone(),
        result_type: cases.result_type.clone(),
        scrutinee: cases.scrutinee,
        alts: new_alts,
    });

    // Attach `Dont` candidates above the cases node.
    attach_candidates(dont_candidates, new_cases)
}

// ════════════════════════════════════════════════════════════════════════════
// Core Algorithm
// ════════════════════════════════════════════════════════════════════════════

/// Recursively process code, collecting candidates and floating them into
/// case arms when a Cases node is reached.
fn go(code: &Code, candidates: &mut Vec<Candidate>) -> Code {
    match code {
        Code::Let(decl, body) => {
            candidates.push(Candidate::Let(decl.clone()));
            go(body, candidates)
        }
        Code::Fun(fun_decl, body) => {
            // Recursively process the function's own body in a fresh scope.
            let new_fun_body = float_let_in_code(&fun_decl.body);
            let new_decl = FunDecl {
                body: Box::new(new_fun_body),
                ..fun_decl.clone()
            };
            candidates.push(Candidate::Fun(new_decl));
            go(body, candidates)
        }
        Code::JoinPoint(jp_decl, body) => {
            // Recursively process the join point's own body in a fresh scope.
            let new_jp_body = float_let_in_code(&jp_decl.body);
            let new_decl = FunDecl {
                body: Box::new(new_jp_body),
                ..jp_decl.clone()
            };
            candidates.push(Candidate::JoinPoint(new_decl));
            go(body, candidates)
        }
        Code::Cases(cases) => {
            // Compute which FVarIds each arm uses.
            let arm_fvars: Vec<HashSet<FVarId>> =
                cases.alts.iter().map(collect_fvars_in_alt).collect();

            // Compute and refine decisions.
            let collected = std::mem::take(candidates);
            let mut decisions = compute_initial_decisions(&collected, &arm_fvars, cases.scrutinee);
            refine_decisions(&collected, &mut decisions);

            // Float candidates into arms and rebuild.
            float_into_cases(collected, cases, &decisions)
        }
        // Terminal nodes: attach all remaining candidates here.
        Code::Return(_) | Code::Jmp { .. } | Code::Unreachable(_) => {
            let collected = std::mem::take(candidates);
            attach_candidates(collected, code.clone())
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Public API
// ════════════════════════════════════════════════════════════════════════════

/// Float let-bindings into case arms in a Code block.
///
/// Moves let-bindings that are only used in a single case arm into that arm,
/// reducing live variable ranges and avoiding unnecessary computation.
pub fn float_let_in_code(code: &Code) -> Code {
    let mut candidates = Vec::new();
    go(code, &mut candidates)
}

/// Float let-bindings in an LCNF declaration.
pub fn float_let_in(decl: &Decl) -> Decl {
    let new_body = match &decl.body {
        DeclValue::Code(code) => DeclValue::Code(Box::new(float_let_in_code(code))),
        DeclValue::Extern(attr) => DeclValue::Extern(attr.clone()),
    };

    Decl {
        name: decl.name.clone(),
        level_params: decl.level_params.clone(),
        ty: decl.ty.clone(),
        params: decl.params.clone(),
        body: new_body,
        recursive: decl.recursive,
    }
}

/// Float let-bindings in multiple LCNF declarations.
pub fn float_let_in_all(decls: &[Decl]) -> Vec<Decl> {
    decls.iter().map(float_let_in).collect()
}

#[cfg(test)]
mod tests;
