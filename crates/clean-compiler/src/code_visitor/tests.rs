// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::lcnf::{Arg, Code, FunDecl, LetDecl, LetValue, Param};
use clean_kernel::{Expr, FVarId, Name};

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> Expr {
    Expr::const_str("Nat")
}

/// Build a simple code tree for testing:
/// let _x1 := 42; let _x2 := 100; return _x2
fn sample_let_chain() -> Code {
    Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(42)),
        Code::let_bind(
            LetDecl::new(fvar(2), name("_2"), nat_type(), LetValue::nat(100)),
            Code::ret(fvar(2)),
        ),
    )
}

/// Build a code tree with a join point:
/// jp _x10 () := return _x0; jmp _x10
fn sample_with_jp() -> Code {
    Code::JoinPoint(
        FunDecl {
            fvar_id: fvar(10),
            name: name("jp"),
            params: vec![],
            ty: nat_type(),
            body: Box::new(Code::ret(fvar(0))),
        },
        Box::new(Code::Jmp {
            jp: fvar(10),
            args: vec![],
        }),
    )
}

/// Build a code tree with a Fun:
/// fun _x20 (_x21) := return _x21; return _x0
fn sample_with_fun() -> Code {
    Code::Fun(
        FunDecl {
            fvar_id: fvar(20),
            name: name("f"),
            params: vec![Param::new(fvar(21), name("x"), nat_type())],
            ty: nat_type(),
            body: Box::new(Code::ret(fvar(21))),
        },
        Box::new(Code::ret(fvar(0))),
    )
}

/// Build a code tree with Cases:
/// cases Nat _x0 | Nat.zero => return _x0 | _ => return _x0
fn sample_with_cases() -> Code {
    Code::cases(
        name("Nat"),
        nat_type(),
        fvar(0),
        vec![
            Alt::ctor(name("Nat.zero"), vec![], Code::ret(fvar(0))),
            Alt::default(Code::ret(fvar(0))),
        ],
    )
}

// =============================================================================
// CodeVisitor tests
// =============================================================================

/// Count all nodes in a Code tree.
struct CodeSizeCounter;

impl CodeVisitor for CodeSizeCounter {
    type Result = usize;

    fn combine(&self, a: usize, b: usize) -> usize {
        a + b
    }

    fn visit_let(&mut self, _decl: &LetDecl, body: &Code) -> usize {
        1 + self.visit_code(body)
    }

    fn visit_fun(&mut self, decl: &FunDecl, body: &Code) -> usize {
        1 + self.visit_code(&decl.body) + self.visit_code(body)
    }

    fn visit_join_point(&mut self, decl: &FunDecl, body: &Code) -> usize {
        1 + self.visit_code(&decl.body) + self.visit_code(body)
    }

    fn visit_cases(&mut self, cases: &Cases) -> usize {
        1 + cases
            .alts
            .iter()
            .map(|alt| self.visit_alt(alt))
            .sum::<usize>()
    }

    fn visit_return(&mut self, _fvar: FVarId) -> usize {
        1
    }

    fn visit_jmp(&mut self, _jp: FVarId, _args: &[Arg]) -> usize {
        1
    }

    fn visit_unreachable(&mut self, _ty: &clean_kernel::Expr) -> usize {
        1
    }
}

#[test]
fn test_visitor_code_size_simple_return() {
    let code = Code::ret(fvar(0));
    assert_eq!(CodeSizeCounter.visit_code(&code), 1);
}

#[test]
fn test_visitor_code_size_let_chain() {
    // let + let + return = 3
    let code = sample_let_chain();
    assert_eq!(CodeSizeCounter.visit_code(&code), 3);
}

#[test]
fn test_visitor_code_size_with_jp() {
    // jp(body=return) + jmp = 1 + 1 + 1 = 3
    let code = sample_with_jp();
    assert_eq!(CodeSizeCounter.visit_code(&code), 3);
}

#[test]
fn test_visitor_code_size_with_fun() {
    // fun(body=return) + return = 1 + 1 + 1 = 3
    let code = sample_with_fun();
    assert_eq!(CodeSizeCounter.visit_code(&code), 3);
}

#[test]
fn test_visitor_code_size_with_cases() {
    // cases(2 alts: return + return) = 1 + 1 + 1 = 3
    let code = sample_with_cases();
    assert_eq!(CodeSizeCounter.visit_code(&code), 3);
}

/// Check if code contains a specific FVarId in a Return position.
struct HasReturn {
    target: FVarId,
}

impl CodeVisitor for HasReturn {
    type Result = bool;

    fn combine(&self, a: bool, b: bool) -> bool {
        a || b
    }

    fn visit_return(&mut self, fvar: FVarId) -> bool {
        fvar == self.target
    }
}

#[test]
fn test_visitor_has_return_true() {
    let code = sample_let_chain();
    let mut visitor = HasReturn { target: fvar(2) };
    assert!(visitor.visit_code(&code));
}

#[test]
fn test_visitor_has_return_false() {
    let code = sample_let_chain();
    let mut visitor = HasReturn { target: fvar(99) };
    assert!(!visitor.visit_code(&code));
}

#[test]
fn test_visitor_has_return_in_jp_body() {
    let code = sample_with_jp();
    let mut visitor = HasReturn { target: fvar(0) };
    assert!(visitor.visit_code(&code));
}

/// Collect all FVarIds used in Return positions.
struct ReturnCollector {
    returns: Vec<FVarId>,
}

impl CodeVisitor for ReturnCollector {
    type Result = ();

    fn combine(&self, _a: (), _b: ()) {}

    fn visit_return(&mut self, fvar: FVarId) {
        self.returns.push(fvar);
    }
}

#[test]
fn test_visitor_collect_returns() {
    let code = sample_with_cases();
    let mut visitor = ReturnCollector {
        returns: Vec::new(),
    };
    visitor.visit_code(&code);
    assert_eq!(visitor.returns.len(), 2);
    assert!(visitor.returns.iter().all(|&f| f == fvar(0)));
}

#[test]
fn test_visitor_collect_returns_in_fun() {
    let code = sample_with_fun();
    let mut visitor = ReturnCollector {
        returns: Vec::new(),
    };
    visitor.visit_code(&code);
    // fun body returns _x21, continuation returns _x0
    assert_eq!(visitor.returns.len(), 2);
    assert_eq!(visitor.returns[0], fvar(21));
    assert_eq!(visitor.returns[1], fvar(0));
}

// =============================================================================
// CodeFolder tests
// =============================================================================

/// Identity folder — fold_code should produce an equal clone.
struct IdentityFolder;

impl CodeFolder for IdentityFolder {}

#[test]
fn test_folder_identity_simple_return() {
    let code = Code::ret(fvar(0));
    let result = IdentityFolder.fold_code(&code);
    assert_eq!(result, code);
}

#[test]
fn test_folder_identity_let_chain() {
    let code = sample_let_chain();
    let result = IdentityFolder.fold_code(&code);
    assert_eq!(result, code);
}

#[test]
fn test_folder_identity_with_jp() {
    let code = sample_with_jp();
    let result = IdentityFolder.fold_code(&code);
    assert_eq!(result, code);
}

#[test]
fn test_folder_identity_with_fun() {
    let code = sample_with_fun();
    let result = IdentityFolder.fold_code(&code);
    assert_eq!(result, code);
}

#[test]
fn test_folder_identity_with_cases() {
    let code = sample_with_cases();
    let result = IdentityFolder.fold_code(&code);
    assert_eq!(result, code);
}

/// Folder that rewrites all Return(x) to Return(target).
struct ReturnRewriter {
    target: FVarId,
}

impl CodeFolder for ReturnRewriter {
    fn fold_return(&mut self, _fvar: FVarId) -> Code {
        Code::Return(self.target)
    }
}

#[test]
fn test_folder_rewrite_returns() {
    let code = sample_let_chain();
    let mut folder = ReturnRewriter { target: fvar(99) };
    let result = folder.fold_code(&code);

    // The return should now be fvar(99)
    let mut collector = ReturnCollector {
        returns: Vec::new(),
    };
    collector.visit_code(&result);
    assert_eq!(collector.returns, vec![fvar(99)]);
}

#[test]
fn test_folder_rewrite_returns_in_cases() {
    let code = sample_with_cases();
    let mut folder = ReturnRewriter { target: fvar(99) };
    let result = folder.fold_code(&code);

    let mut collector = ReturnCollector {
        returns: Vec::new(),
    };
    collector.visit_code(&result);
    assert_eq!(collector.returns.len(), 2);
    assert!(collector.returns.iter().all(|&f| f == fvar(99)));
}

#[test]
fn test_folder_rewrite_returns_in_fun_body() {
    let code = sample_with_fun();
    let mut folder = ReturnRewriter { target: fvar(99) };
    let result = folder.fold_code(&code);

    let mut collector = ReturnCollector {
        returns: Vec::new(),
    };
    collector.visit_code(&result);
    // Both returns (in fun body and continuation) should be rewritten
    assert_eq!(collector.returns.len(), 2);
    assert!(collector.returns.iter().all(|&f| f == fvar(99)));
}

#[test]
fn test_visitor_unreachable() {
    let code = Code::Unreachable(nat_type());
    assert_eq!(CodeSizeCounter.visit_code(&code), 1);
}

#[test]
fn test_folder_identity_unreachable() {
    let code = Code::Unreachable(nat_type());
    let result = IdentityFolder.fold_code(&code);
    assert_eq!(result, code);
}
