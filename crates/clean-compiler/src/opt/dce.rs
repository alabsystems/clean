// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dead Code Elimination (DCE) for L5CNF.
//!
//! Removes let-bindings that are never used in the rest of the code.
//! This is a simple but effective optimization that can remove 10-30%
//! of generated bindings in typical code.
//!
//! # Algorithm
//!
//! 1. Build a dependency graph: for each let-binding, record which FVarIds it uses
//! 2. Collect root FVarIds from terminals (Return, Jmp, Cases scrutinee)
//! 3. Compute transitive closure: mark all FVarIds reachable from roots as live
//! 4. Rebuild code, removing bindings not in the live set
//!
//! # Example
//!
//! Before:
//! ```text
//! let _1 := 42
//! let _2 := Nat.add _1 _1
//! let _3 := 10  // unused
//! return _2
//! ```
//!
//! After:
//! ```text
//! let _1 := 42
//! let _2 := Nat.add _1 _1
//! return _2
//! ```
//!
//! Part of #963 - Compiler IR infrastructure.

use crate::lcnf::{Alt, Arg, Code, Decl, DeclValue, FunDecl, LetDecl, LetValue};
use crate::CodeFolder;
use clean_kernel::FVarId;
use std::collections::{HashMap, HashSet};

/// Collect FVarIds used in an argument.
fn arg_deps(arg: &Arg) -> Vec<FVarId> {
    match arg {
        Arg::FVar(id) => vec![*id],
        _ => vec![],
    }
}

/// Collect FVarIds used in a let-value.
fn let_value_deps(value: &LetValue) -> Vec<FVarId> {
    match value {
        LetValue::Lit(_) | LetValue::Erased => vec![],
        LetValue::Proj { structure, .. } => vec![*structure],
        LetValue::Const { args, .. } | LetValue::Ctor { args, .. } => {
            args.iter().flat_map(arg_deps).collect()
        }
        LetValue::FVar { fvar, args } => {
            let mut deps = vec![*fvar];
            deps.extend(args.iter().flat_map(arg_deps));
            deps
        }
        LetValue::Reuse { slot, args, .. } => {
            let mut deps = vec![*slot];
            deps.extend(args.iter().flat_map(arg_deps));
            deps
        }
    }
}

/// Build a dependency graph from let bindings.
/// Returns a map from FVarId to the FVarIds it depends on.
fn build_dependency_graph(code: &Code, deps: &mut HashMap<FVarId, Vec<FVarId>>) {
    match code {
        Code::Let(decl, body) => {
            deps.insert(decl.fvar_id, let_value_deps(&decl.value));
            build_dependency_graph(body, deps);
        }
        Code::Fun(decl, body) | Code::JoinPoint(decl, body) => {
            // Recursively collect dependencies within the function body
            build_dependency_graph(&decl.body, deps);
            // The function itself depends on what's used in its body
            let mut func_deps = Vec::new();
            collect_terminal_fvars(&decl.body, &mut func_deps);
            deps.insert(decl.fvar_id, func_deps);
            build_dependency_graph(body, deps);
        }
        Code::Cases(cases) => {
            for alt in &cases.alts {
                match alt {
                    Alt::Ctor { body, .. } => build_dependency_graph(body, deps),
                    Alt::Default(body) => build_dependency_graph(body, deps),
                }
            }
        }
        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => {}
    }
}

/// Collect FVarIds directly used in code terminals (Return, Jmp, Cases scrutinee).
fn collect_terminal_fvars(code: &Code, fvars: &mut Vec<FVarId>) {
    match code {
        Code::Let(_, body) => collect_terminal_fvars(body, fvars),
        Code::Fun(_, body) | Code::JoinPoint(_, body) => {
            collect_terminal_fvars(body, fvars);
        }
        Code::Cases(cases) => {
            fvars.push(cases.scrutinee);
            for alt in &cases.alts {
                match alt {
                    Alt::Ctor { body, .. } => collect_terminal_fvars(body, fvars),
                    Alt::Default(body) => collect_terminal_fvars(body, fvars),
                }
            }
        }
        Code::Jmp { jp, args } => {
            fvars.push(*jp);
            fvars.extend(args.iter().flat_map(arg_deps));
        }
        Code::Return(fvar) => fvars.push(*fvar),
        Code::Unreachable(_) => {}
    }
}

/// Compute the transitive closure of used FVarIds.
fn compute_live_set(roots: &[FVarId], deps: &HashMap<FVarId, Vec<FVarId>>) -> HashSet<FVarId> {
    let mut live = HashSet::new();
    let mut worklist: Vec<FVarId> = roots.to_vec();

    while let Some(fvar) = worklist.pop() {
        if live.insert(fvar) {
            // Newly added - process its dependencies
            if let Some(fvar_deps) = deps.get(&fvar) {
                worklist.extend(fvar_deps.iter().copied());
            }
        }
    }

    live
}

/// Eliminate dead code from an LCNF Code block.
///
/// Returns a new Code block with unused let-bindings removed.
pub fn eliminate_dead_code_in_code(code: &Code) -> Code {
    // Build dependency graph
    let mut deps = HashMap::new();
    build_dependency_graph(code, &mut deps);

    // Collect root uses (from terminals)
    let mut roots = Vec::new();
    collect_terminal_fvars(code, &mut roots);

    // Compute live set via transitive closure
    let live = compute_live_set(&roots, &deps);

    // Rebuild code, removing dead bindings
    eliminate_dead_code_impl(code, &live)
}

/// CodeFolder that removes dead let/fun/join-point bindings.
///
/// Delegates structural recursion to the CodeFolder trait. Only overrides
/// fold_let, fold_fun, and fold_join_point to conditionally drop dead bindings.
struct DceFolder<'a> {
    live: &'a HashSet<FVarId>,
}

impl CodeFolder for DceFolder<'_> {
    fn fold_let(&mut self, decl: LetDecl, body: Code) -> Code {
        let new_body = self.fold_code(&body);
        if self.live.contains(&decl.fvar_id) {
            Code::Let(decl, Box::new(new_body))
        } else {
            new_body
        }
    }

    fn fold_fun(&mut self, decl: FunDecl, body: Code) -> Code {
        let new_fun_body = self.fold_code(&decl.body);
        let new_decl = FunDecl {
            body: Box::new(new_fun_body),
            ..decl
        };
        let new_body = self.fold_code(&body);
        if self.live.contains(&new_decl.fvar_id) {
            Code::Fun(new_decl, Box::new(new_body))
        } else {
            new_body
        }
    }

    fn fold_join_point(&mut self, decl: FunDecl, body: Code) -> Code {
        let new_jp_body = self.fold_code(&decl.body);
        let new_decl = FunDecl {
            body: Box::new(new_jp_body),
            ..decl
        };
        let new_body = self.fold_code(&body);
        if self.live.contains(&new_decl.fvar_id) {
            Code::JoinPoint(new_decl, Box::new(new_body))
        } else {
            new_body
        }
    }
}

fn eliminate_dead_code_impl(code: &Code, live: &HashSet<FVarId>) -> Code {
    DceFolder { live }.fold_code(code)
}

/// Eliminate dead code from an LCNF declaration.
pub fn eliminate_dead_code(decl: &Decl) -> Decl {
    let new_body = match &decl.body {
        DeclValue::Code(code) => DeclValue::Code(Box::new(eliminate_dead_code_in_code(code))),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lcnf::{Cases, LetDecl};
    use clean_kernel::{Expr, Name};

    fn fvar(n: u64) -> FVarId {
        FVarId::new(n)
    }

    fn name(s: &str) -> Name {
        Name::from_string(s)
    }

    #[test]
    fn test_eliminate_unused_let() {
        // let _1 := 42
        // let _2 := 10  // unused
        // return _1
        let code = Code::Let(
            LetDecl::new(
                fvar(1),
                name("_1"),
                Expr::const_str("Nat"),
                LetValue::nat(42),
            ),
            Box::new(Code::Let(
                LetDecl::new(
                    fvar(2),
                    name("_2"),
                    Expr::const_str("Nat"),
                    LetValue::nat(10),
                ),
                Box::new(Code::Return(fvar(1))),
            )),
        );

        let optimized = eliminate_dead_code_in_code(&code);

        // Should remove _2
        let s = optimized.to_string();
        assert!(s.contains("_x1 := 42"));
        assert!(!s.contains("_x2"));
        assert!(s.contains("return _x1"));
    }

    #[test]
    fn test_keep_used_let() {
        // let _1 := 42
        // let _2 := Nat.add _1 _1
        // return _2
        let code = Code::Let(
            LetDecl::new(
                fvar(1),
                name("_1"),
                Expr::const_str("Nat"),
                LetValue::nat(42),
            ),
            Box::new(Code::Let(
                LetDecl::new(
                    fvar(2),
                    name("_2"),
                    Expr::const_str("Nat"),
                    LetValue::Const {
                        name: name("Nat.add"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(1))],
                    },
                ),
                Box::new(Code::Return(fvar(2))),
            )),
        );

        let optimized = eliminate_dead_code_in_code(&code);

        // Both bindings should be kept
        let s = optimized.to_string();
        assert!(s.contains("_x1 := 42"));
        assert!(s.contains("_x2 := Nat.add"));
        assert!(s.contains("return _x2"));
    }

    #[test]
    fn test_chain_of_unused() {
        // let _1 := 42
        // let _2 := Nat.succ _1  // unused
        // let _3 := Nat.succ _2  // unused (even though _2 is used by it)
        // return _1
        let code = Code::Let(
            LetDecl::new(
                fvar(1),
                name("_1"),
                Expr::const_str("Nat"),
                LetValue::nat(42),
            ),
            Box::new(Code::Let(
                LetDecl::new(
                    fvar(2),
                    name("_2"),
                    Expr::const_str("Nat"),
                    LetValue::Const {
                        name: name("Nat.succ"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1))],
                    },
                ),
                Box::new(Code::Let(
                    LetDecl::new(
                        fvar(3),
                        name("_3"),
                        Expr::const_str("Nat"),
                        LetValue::Const {
                            name: name("Nat.succ"),
                            levels: vec![],
                            args: vec![Arg::FVar(fvar(2))],
                        },
                    ),
                    Box::new(Code::Return(fvar(1))),
                )),
            )),
        );

        let optimized = eliminate_dead_code_in_code(&code);

        // Only _1 should remain since _2 and _3 are not transitively reachable
        // from the return
        let s = optimized.to_string();
        assert!(s.contains("_x1 := 42"));
        assert!(!s.contains("_x2"));
        assert!(!s.contains("_x3"));
    }

    #[test]
    fn test_dce_in_case_arms() {
        // cases _0 of
        // | True =>
        //   let _1 := 42
        //   let _2 := 10  // unused
        //   return _1
        // | False =>
        //   return _0
        let code = Code::Cases(Cases {
            type_name: name("Bool"),
            result_type: Expr::const_str("Nat"),
            scrutinee: fvar(0),
            alts: vec![
                Alt::Ctor {
                    ctor_name: name("Bool.true"),
                    params: vec![],
                    body: Box::new(Code::Let(
                        LetDecl::new(
                            fvar(1),
                            name("_1"),
                            Expr::const_str("Nat"),
                            LetValue::nat(42),
                        ),
                        Box::new(Code::Let(
                            LetDecl::new(
                                fvar(2),
                                name("_2"),
                                Expr::const_str("Nat"),
                                LetValue::nat(10),
                            ),
                            Box::new(Code::Return(fvar(1))),
                        )),
                    )),
                },
                Alt::Ctor {
                    ctor_name: name("Bool.false"),
                    params: vec![],
                    body: Box::new(Code::Return(fvar(0))),
                },
            ],
        });

        let optimized = eliminate_dead_code_in_code(&code);

        let s = optimized.to_string();
        // _2 should be removed in the True arm
        assert!(s.contains("_x1 := 42"));
        assert!(!s.contains("_x2"));
    }
}
