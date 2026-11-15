// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Reject invalid certificates without expanding shared terms for diagnostics.
//!
//! The pinned checker's `Term::fmt` first renders the unshared expression into
//! an unbounded buffer. Even a bounded outer writer cannot contain that work:
//! a small multiplication DAG can expand exponentially on a rejected rule.
//! Keep the error's location and rule, and never invoke its term formatter.

use super::VerifyError;
use carcara::{checker::error::CheckerError, parser::ParserError, Error};

fn label(text: &str) -> String {
    let mut chars = text.chars();
    let mut result: String = chars.by_ref().take(160).collect();
    if chars.next().is_some() {
        result.push_str("...");
    }
    result
}

/// The refusal of a check stopped at its caller's deadline, `when` naming where.
pub(super) fn deadline_passed(when: &str) -> VerifyError {
    VerifyError::CarcaraDeadline(format!("the check reached its deadline {when}"))
}

pub(super) fn failure(error: Error) -> VerifyError {
    let deadline = matches!(
        error,
        Error::Checker {
            inner: CheckerError::DeadlineExceeded,
            ..
        } | Error::Parser(ParserError::DeadlineExceeded, _)
    );
    let message = match error {
        Error::Checker { inner, rule, step } => {
            let reason = match inner {
                CheckerError::Assume(_) => "assumption not present in the problem".to_owned(),
                CheckerError::ReflexivityFailed(..) => "reflexivity failed".to_owned(),
                // A refusal by the vendored checker's resource budget carries counts, never a
                // term (third-party/carcara/DOWNSTREAM.md, "Bit-vector expansion has a resource
                // budget"), so it is printed whole.
                budget @ CheckerError::ResourceBudgetExceeded(_) => budget.to_string(),
                // So does a check stopped at its caller's deadline.
                deadline @ CheckerError::DeadlineExceeded => deadline.to_string(),
                _ => "rule validation failed".to_owned(),
            };
            format!(
                "checking failed on step '{}' with rule '{}': {reason}; term details omitted",
                label(&step),
                label(&rule)
            )
        }
        // These refusals carry symbol, sort or command names, or a depth limit, never a term, and
        // say why a problem script is not read (third-party/carcara/DOWNSTREAM.md, fixes 36 to 40,
        // the tester check under "Also hardened", "Terms nest at most 2^18 deep", and a parse
        // stopped at its caller's deadline, "The checker stops at a deadline").
        Error::Parser(
            inner @ (ParserError::MacroCapture(..)
            | ParserError::NamedTermNotClosed(..)
            | ParserError::UnsupportedScriptCommand(_)
            | ParserError::CommandAfterQueryEnd(..)
            | ParserError::UnknownScriptCommand(_)
            | ParserError::RecursiveDefinitionRefused(_)
            | ParserError::SymbolReadAsNumber(_)
            | ParserError::InvalidTester(_)
            | ParserError::BuiltinNameDeclared(_)
            | ParserError::NameAlreadyInUse(_)
            | ParserError::BuiltinSortDeclared(_)
            | ParserError::SortRedeclared(_)
            | ParserError::WrittenTooDeep(_)
            | ParserError::TooDeep(_)
            | ParserError::DeadlineExceeded),
            position,
        ) => format!(
            "parser error on line {}, column {}: {}",
            position.0,
            position.1,
            label(&inner.to_string())
        ),
        Error::Parser(_, position) => format!(
            "parser error on line {}, column {}; term details omitted",
            position.0, position.1
        ),
        Error::Io(error) => format!("proof input error: {}", error.kind()),
        Error::DoesNotReachEmptyClause => "proof does not conclude empty clause".into(),
        Error::Elaborator { rule, step, .. } => format!(
            "elaboration failed on step '{}' with rule '{}'; term details omitted",
            label(&step),
            label(&rule)
        ),
    };
    if deadline {
        VerifyError::CarcaraDeadline(message)
    } else {
        VerifyError::CarcaraError(message)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejected_shared_terms_do_not_expand_during_error_reporting() {
        let problem = "(set-logic QF_UF)(declare-const p Bool)(assert p)";
        let mut proof = "(define-fun d0 () Bool p)\n".to_string();
        for i in 1..=40 {
            let previous = i - 1;
            proof.push_str(&format!(
                "(define-fun d{i} () Bool (and d{previous} d{previous}))\n"
            ));
        }
        proof.push_str("(step bad (cl (= d40 false)) :rule refl)\n");
        let error = super::super::verify_alethe_proof(problem, &proof)
            .expect_err("a shared non-identity must be rejected");
        let diagnostic = error.to_string();
        assert!(diagnostic.contains("step 'bad' with rule 'refl'"));
        assert!(diagnostic.contains("reflexivity failed"));
        assert!(diagnostic.len() < 512);
        assert!(super::super::verify_alethe_proof(
            "(set-logic QF_UF)(declare-const p Bool)(assert p)(assert (not p))",
            "(assume a p)(assume b (not p))(step done (cl) :rule resolution :premises (a b))"
        )
        .unwrap());
    }

    /// `bitblast_equal` read on a Boolean: the checker's own error names `d40`, whose text is 2^40
    /// copies of `p`, and building that error's message grew past 2 GB in 10 s before the vendored
    /// checker wrote terms abridged (third-party/carcara/DOWNSTREAM.md, "Diagnostics write a term
    /// abridged").
    #[test]
    fn an_error_about_a_shared_term_is_built_and_printed_bounded() {
        let problem = "(set-logic QF_BV)(declare-const p Bool)(assert p)(assert (not p))";
        let mut proof = "(define-fun d0 () Bool p)\n".to_string();
        for i in 1..=40 {
            let previous = i - 1;
            proof.push_str(&format!(
                "(define-fun d{i} () Bool (and d{previous} d{previous}))\n"
            ));
        }
        proof.push_str("(step t1 (cl (= (= d40 d40) true)) :rule bitblast_equal)\n");
        proof.push_str(
            "(assume h1 p)(assume h2 (not p))(step t2 (cl) :rule resolution :premises (h1 h2))\n",
        );
        let error = super::super::verify_alethe_proof(problem, &proof)
            .expect_err("a Boolean is not a bit-vector");
        assert_eq!(
            error.to_string(),
            "carcara error: checking failed on step 't1' with rule 'bitblast_equal': rule \
             validation failed; term details omitted"
        );
    }

    /// Terms nested a few thousand deep are checked on the checker's own thread, whose stack
    /// covers what the parser reads; past that, they are refused with the limit named
    /// (third-party/carcara/DOWNSTREAM.md, "Terms nest at most 2^18 deep"). On the caller's
    /// thread, each of the first two overflowed the stack, which ends the process: the parser takes
    /// about 2.3 KiB per level written and `poly_simp` about 1 KiB per level of the sum it walks, in
    /// a release build, and several times that unoptimized.
    #[test]
    fn deep_terms_are_checked_on_the_checkers_stack_or_refused() {
        let unsat =
            "(assume h1 p)(assume h2 (not p))(step t (cl) :rule resolution :premises (h1 h2))";
        let problem = "(set-logic ALL)(declare-const p Bool)(declare-const i Int)(assert p)\
                       (assert (not p))";
        let written = |depth: usize| format!("{}p{}", "(not ".repeat(depth), ")".repeat(depth));

        let deep = written(10_000);
        let proof = format!("(step t1 (cl (= {deep} {deep})) :rule refl){unsat}");
        assert!(super::super::verify_alethe_proof(problem, &proof).unwrap());

        let mut proof = "(define-fun g0 () Int i)\n".to_owned();
        for j in 1..=20_000 {
            proof.push_str(&format!("(define-fun g{j} () Int (+ 1 g{}))\n", j - 1));
        }
        proof.push_str(&format!(
            "(step t1 (cl (= g20000 g20000)) :rule poly_simp){unsat}"
        ));
        assert!(super::super::verify_alethe_proof(problem, &proof).unwrap());

        let proof = format!("(step t1 (cl {}) :rule hole){unsat}", written(100_000));
        let error = super::super::verify_alethe_proof(problem, &proof)
            .expect_err("written too deep")
            .to_string();
        assert!(
            error.contains(
                "terms and sorts written more than 16384 deep inside each other are not read"
            ),
            "{error}"
        );
        let built = failure(Error::Parser(ParserError::TooDeep(1 << 18), (3, 9))).to_string();
        assert!(
            built.contains(
                "parser error on line 3, column 9: a term or sort more than 262144 deep is not \
                 read"
            ),
            "{built}"
        );
    }

    #[test]
    fn a_step_past_the_resource_budget_says_so() {
        let error = super::super::verify_alethe_proof(
            "(set-logic QF_BV)(declare-const a Bool)(assert a)(assert (not a))",
            "(step t1 (cl (= (bvult ((_ zero_extend 4294967295) #b0) \
             ((_ zero_extend 4294967295) #b1)) false)) :rule bitblast_ult)\n\
             (assume h1 a)(assume h2 (not a))(step t2 (cl) :rule resolution :premises (h1 h2))",
        )
        .expect_err("refused by the budget");
        let diagnostic = error.to_string();
        assert!(
            diagnostic.contains(
                "step 't1' with rule 'bitblast_ult': resource budget exceeded: splitting a \
                 bit-vector into its bits would bring the step to 4294967296 expanded bits"
            ),
            "{diagnostic}"
        );
        assert!(diagnostic.len() < 512);
    }

    #[test]
    fn untrusted_step_and_rule_names_have_bounded_utf8_diagnostics() {
        let error = Error::Checker {
            inner: CheckerError::Unspecified,
            rule: "🙂".repeat(4096).into(),
            step: "α".repeat(4096).into(),
        };
        let diagnostic = failure(error).to_string();
        assert!(diagnostic.len() < 1200);
        assert!(diagnostic.contains("..."));
    }

    #[test]
    fn script_refusals_say_why_with_bounded_names() {
        let error = super::super::verify_alethe_proof(
            "(declare-const p Bool)(assert p)(reset-assertions)(assert (not p))",
            "(assume a p)(assume b (not p))(step done (cl) :rule resolution :premises (a b))",
        )
        .expect_err("a script with reset-assertions must be refused");
        assert!(error
            .to_string()
            .contains("'reset-assertions' is not supported"));

        let proof =
            "(assume a p)(assume b (not p))(step done (cl) :rule resolution :premises (a b))";
        for (problem, reason) in [
            (
                "(declare-const p Bool)(assert p)(check-sat-using smt)(assert (not p))",
                "'check-sat-using' is not a command this checker reads",
            ),
            (
                "(declare-const p Bool)(assert (= p (! true :named false)))(assert (not p))",
                "'false' is a built-in operator and cannot be declared or defined",
            ),
            (
                "(declare-const p Bool)(assert (! p :named p))(assert (not p))",
                "'p' is already declared or defined",
            ),
            (
                "(declare-const p Bool)(define-fun-rec q () Bool (not q))(assert p)\
                 (assert (not p))",
                "'define-fun-rec' is not supported: a recursive definition",
            ),
            (
                "(declare-const p Bool)(declare-const |-1| Int)(assert (= -1 3))(assert p)\
                 (assert (not p))",
                "'-1' is a declared or bound symbol, which this checker would read here",
            ),
            (
                "(declare-datatype D ((c) (d)))(declare-const p Bool)(assert ((_ is p) c))\
                 (assert p)(assert (not p))",
                "'(_ is p)' does not name a constructor",
            ),
        ] {
            let error = super::super::verify_alethe_proof(problem, proof)
                .expect_err("the script must be refused");
            assert!(error.to_string().contains(reason), "{problem}: {error}");
        }

        let long = "x".repeat(4096);
        for inner in [
            ParserError::MacroCapture(long.clone(), long.clone()),
            ParserError::UnknownScriptCommand(long.clone()),
            ParserError::NameAlreadyInUse(long.clone()),
            ParserError::SymbolReadAsNumber(long.clone()),
            ParserError::InvalidTester(long.clone()),
        ] {
            let diagnostic = failure(Error::Parser(inner, (1, 1))).to_string();
            assert!(diagnostic.len() < 512);
            assert!(diagnostic.contains("..."));
        }
    }

    #[test]
    fn malformed_input_still_reports_its_parse_location() {
        let error = super::super::verify_alethe_proof("(assert", "")
            .expect_err("malformed input must not be accepted");
        assert!(error.to_string().contains("parser error on line"));
    }
}
