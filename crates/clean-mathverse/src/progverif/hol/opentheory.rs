// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! OpenTheory `.art` article file parser.
//!
//! OpenTheory is the standard exchange format for the HOL family. An article
//! file is a sequence of stack-machine commands that build up types, terms,
//! and theorems. The instruction set is small (~30 commands) and purely
//! functional (no mutation of previously-created objects).
//!
//! This parser implements the core OpenTheory virtual machine as specified in:
//! Hurd, "The OpenTheory Standard Theory Library" (2011).
//!
//! The VM implementation lives in [`super::ot_vm`]; this module provides the
//! public parse API and result types.

use super::ot_vm::OtVm;
use super::types::{HolAxiom, HolThm};
use super::HolError;

// ---------------------------------------------------------------------------
// Parser result
// ---------------------------------------------------------------------------

/// Result of parsing an OpenTheory article.
#[derive(Clone, Debug, Default)]
pub struct ArticleResult {
    /// Theorems produced by the article (via `thm` commands).
    pub theorems: Vec<HolThm>,
    /// Type operator names defined (via `defineTypeOp`).
    pub type_ops: Vec<String>,
    /// Constant names defined (via `defineConst`).
    pub constants: Vec<String>,
    /// Axioms assumed (via `axiom` commands).
    pub axioms_assumed: Vec<HolAxiom>,
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Parse an OpenTheory `.art` article and return the theorems it exports.
///
/// The article is a sequence of newline-delimited commands for the OpenTheory
/// virtual machine. Each exported `thm` command yields one theorem in the
/// result.
pub fn parse_article(article: &str) -> Result<ArticleResult, HolError> {
    let trimmed = article.trim();
    if trimmed.is_empty() {
        return Err(HolError::OpenTheoryError {
            message: "empty article".to_owned(),
        });
    }

    let mut vm = OtVm::new();

    for (line_no, line) in trimmed.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        vm.exec(line).map_err(|e| HolError::OpenTheoryError {
            message: format!("line {}: {e}", line_no + 1),
        })?;
    }

    Ok(vm.result)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::super::ot_vm::OtVm;
    use super::*;
    use crate::progverif::hol::types::{HolTerm, HolType};

    /// Minimal article: builds Const("=", bool), refl, then exports via thm.
    ///
    /// Stack before thm: [Thm, List(hyps), Term(concl)]
    /// thm pops: concl (TOS), hyps list, theorem.
    const TRUTH_ARTICLE: &str = "\
\"bool\"
nil
opType
0
def
\"=\"
0
ref
constTerm
refl
nil
\"T\"
0
ref
constTerm
thm
";

    #[test]
    fn test_parse_article_empty() {
        assert!(parse_article("").is_err());
    }

    #[test]
    fn test_parse_article_truth() {
        let result = parse_article(TRUTH_ARTICLE).unwrap();
        assert_eq!(
            result.theorems.len(),
            1,
            "should export one theorem (TRUTH)"
        );
    }

    #[test]
    fn test_vm_num_push() {
        let mut vm = OtVm::new();
        vm.exec("42").unwrap();
        let obj = vm.pop().unwrap();
        assert_eq!(obj.as_num().unwrap(), 42);
    }

    #[test]
    fn test_vm_name_push() {
        let mut vm = OtVm::new();
        vm.exec("\"foo.bar\"").unwrap();
        let obj = vm.pop().unwrap();
        assert_eq!(obj.into_name().unwrap(), vec!["foo", "bar"]);
    }

    #[test]
    fn test_vm_nil_cons() {
        let mut vm = OtVm::new();
        vm.exec("nil").unwrap();
        vm.exec("42").unwrap();
        vm.exec("cons").unwrap();
        let obj = vm.pop().unwrap();
        let list = obj.into_list().unwrap();
        assert_eq!(list.len(), 1);
    }

    #[test]
    fn test_vm_def_ref() {
        let mut vm = OtVm::new();
        vm.exec("42").unwrap();
        vm.exec("0").unwrap();
        vm.exec("def").unwrap();
        let val = vm.pop().unwrap().as_num().unwrap();
        assert_eq!(val, 42);
        vm.exec("0").unwrap();
        vm.exec("ref").unwrap();
        let val = vm.pop().unwrap().as_num().unwrap();
        assert_eq!(val, 42);
    }

    #[test]
    fn test_vm_var_type() {
        let mut vm = OtVm::new();
        vm.exec("\"alpha\"").unwrap();
        vm.exec("varType").unwrap();
        let obj = vm.pop().unwrap();
        let ty = obj.into_type().unwrap();
        assert_eq!(ty, HolType::TyVar("alpha".to_owned()));
    }

    #[test]
    fn test_vm_op_type_bool() {
        let mut vm = OtVm::new();
        vm.exec("\"bool\"").unwrap();
        vm.exec("nil").unwrap();
        vm.exec("opType").unwrap();
        let obj = vm.pop().unwrap();
        let ty = obj.into_type().unwrap();
        assert_eq!(ty, HolType::bool());
    }

    #[test]
    fn test_vm_var_term() {
        let mut vm = OtVm::new();
        vm.exec("\"x\"").unwrap();
        vm.exec("\"bool\"").unwrap();
        vm.exec("nil").unwrap();
        vm.exec("opType").unwrap();
        vm.exec("varTerm").unwrap();
        let obj = vm.pop().unwrap();
        let tm = obj.into_term().unwrap();
        assert_eq!(tm, HolTerm::Var("x".to_owned(), HolType::bool()));
    }

    #[test]
    fn test_vm_assume() {
        let mut vm = OtVm::new();
        vm.exec("\"x\"").unwrap();
        vm.exec("\"bool\"").unwrap();
        vm.exec("nil").unwrap();
        vm.exec("opType").unwrap();
        vm.exec("varTerm").unwrap();
        vm.exec("assume").unwrap();
        let obj = vm.pop().unwrap();
        let thm = obj.into_thm().unwrap();
        assert_eq!(thm.hyps.len(), 1);
        assert_eq!(thm.hyps[0], thm.concl);
    }

    #[test]
    fn test_vm_refl() {
        let mut vm = OtVm::new();
        vm.exec("\"T\"").unwrap();
        vm.exec("\"bool\"").unwrap();
        vm.exec("nil").unwrap();
        vm.exec("opType").unwrap();
        vm.exec("constTerm").unwrap();
        vm.exec("refl").unwrap();
        let obj = vm.pop().unwrap();
        let thm = obj.into_thm().unwrap();
        assert!(thm.hyps.is_empty(), "REFL should have no hypotheses");
    }

    #[test]
    fn test_vm_define_const() {
        let mut vm = OtVm::new();
        vm.exec("\"myConst\"").unwrap();
        vm.exec("\"T\"").unwrap();
        vm.exec("\"bool\"").unwrap();
        vm.exec("nil").unwrap();
        vm.exec("opType").unwrap();
        vm.exec("constTerm").unwrap();
        vm.exec("defineConst").unwrap();
        let thm = vm.pop().unwrap().into_thm().unwrap();
        assert!(thm.hyps.is_empty());
        let c = vm.pop().unwrap().into_term().unwrap();
        assert!(matches!(c, HolTerm::Const(name, _) if name == "myConst"));
        assert!(vm.result.constants.contains(&"myConst".to_owned()));
    }

    #[test]
    fn test_vm_unknown_command() {
        let mut vm = OtVm::new();
        assert!(vm.exec("foobar").is_err());
    }

    #[test]
    fn test_vm_stack_underflow() {
        let mut vm = OtVm::new();
        assert!(vm.exec("pop").is_err());
    }

    #[test]
    fn test_comment_lines_skipped() {
        let article = "# this is a comment\n42\n";
        let result = parse_article(article);
        assert!(result.is_ok());
    }
}
