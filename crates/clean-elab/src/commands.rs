// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Interactive command elaboration: `#eval`, `#check`, `#print`.
//!
//! These are standalone functions that operate on a kernel [`Environment`]
//! without requiring the full [`ElabCtx`] elaboration context. Each command
//! follows a simple pattern:
//!
//! - **`elab_check`**: Elaborate the expression, infer its type, format both.
//! - **`elab_eval`**: Elaborate the expression, reduce to WHNF, format the result.
//! - **`elab_print`**: Look up a name in the environment, format its definition.
//!
//! The functions accept already-elaborated kernel [`Expr`] values (for `#check`
//! and `#eval`) or a string name (for `#print`). The caller is responsible for
//! elaborating surface syntax to kernel expressions before calling these.
//!
//! # Design
//!
//! The `ElabCtx.env` field is private to the `infer` module, so these functions
//! are standalone rather than methods on `ElabCtx`. They take `&Environment`
//! directly, matching the pattern used by the top-level `elaborate()` function
//! in `lib.rs`.

use crate::error::ElabError;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, TypeChecker};

/// Result of a `#check` command.
///
/// Contains the original expression and its inferred type, both formatted
/// as strings for diagnostic output.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckResult {
    /// The expression that was checked (formatted).
    pub expr: String,
    /// The inferred type of the expression (formatted).
    pub ty: String,
}

impl std::fmt::Display for CheckResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} : {}", self.expr, self.ty)
    }
}

/// Result of a `#eval` command.
///
/// Contains the original expression and its WHNF-reduced form, both formatted
/// as strings for diagnostic output.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvalResult {
    /// The WHNF-reduced expression (formatted).
    pub value: String,
}

impl std::fmt::Display for EvalResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

/// Result of a `#print` command.
///
/// Contains formatted information about the looked-up declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrintResult {
    /// The full formatted output for the declaration.
    pub output: String,
}

impl std::fmt::Display for PrintResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.output)
    }
}

/// Elaborate `#check expr`: infer the type of an already-elaborated expression.
///
/// Creates a fresh [`TypeChecker`] to infer the type, then formats both the
/// expression and its type as strings.
///
/// # Errors
///
/// Returns [`ElabError::KernelCheckFailed`] if type inference fails (e.g.,
/// the expression contains unbound variables or ill-typed subexpressions).
///
/// # Example
///
/// ```text
/// #check Nat.zero   -- Nat.zero : Nat
/// ```
#[must_use = "check result contains the inferred type"]
pub fn elab_check(env: &Environment, expr: &Expr) -> Result<CheckResult, ElabError> {
    let tc = TypeChecker::new(env);
    let ty = tc
        .infer_type(expr)
        .map_err(|e| ElabError::KernelCheckFailed {
            name: Name::anon(),
            detail: e.to_string(),
        })?;
    Ok(CheckResult {
        expr: format!("{expr}"),
        ty: format!("{ty}"),
    })
}

/// Elaborate `#eval expr`: reduce an already-elaborated expression to WHNF.
///
/// Creates a fresh [`TypeChecker`] to reduce the expression to weak head
/// normal form (WHNF), which evaluates top-level redexes. For fully-reduced
/// output, the expression is also type-checked first to ensure validity.
///
/// If the expression has IO type (`IO α`), it is additionally executed
/// through the IO runtime, producing real side effects (console output,
/// file I/O, etc.) and returning the captured output.
///
/// # Errors
///
/// Returns [`ElabError::KernelCheckFailed`] if type inference fails before
/// reduction, or [`ElabError::NotImplemented`] if IO execution fails.
///
/// # Example
///
/// ```text
/// #eval 2 + 3              -- 5
/// #eval IO.println "hello"  -- prints "hello", returns ()
/// ```
pub fn elab_eval(env: &Environment, expr: &Expr) -> Result<EvalResult, ElabError> {
    let tc = TypeChecker::new(env);
    // Validate the expression is well-typed before reducing.
    let _ty = tc
        .infer_type(expr)
        .map_err(|e| ElabError::KernelCheckFailed {
            name: Name::anon(),
            detail: e.to_string(),
        })?;
    let reduced = tc.whnf(expr);

    // Check if the expression is IO-typed and execute it through the IO runtime.
    if crate::io_bridge::is_io_typed(env, expr) {
        let io_result = crate::io_bridge::eval_io_expr(&reduced)?;
        return Ok(EvalResult {
            value: format!("{io_result}"),
        });
    }

    Ok(EvalResult {
        value: format!("{reduced}"),
    })
}

/// Format a constant declaration (definition, theorem, axiom, opaque) for `#print`.
fn format_constant(name: &str, info: &clean_kernel::ConstantInfo) -> String {
    let kind_str = match info.kind {
        clean_kernel::env::ConstantKind::Definition => "def",
        clean_kernel::env::ConstantKind::Theorem => "theorem",
        clean_kernel::env::ConstantKind::Opaque => "opaque",
        clean_kernel::env::ConstantKind::Axiom => "axiom",
    };

    let mut output = String::new();

    // Header: kind + name + universe params
    output.push_str(kind_str);
    output.push(' ');
    output.push_str(name);

    if !info.level_params.is_empty() {
        output.push_str(".{");
        for (i, p) in info.level_params.iter().enumerate() {
            if i > 0 {
                output.push_str(", ");
            }
            output.push_str(&format!("{p}"));
        }
        output.push('}');
    }

    // Type
    output.push_str(" : ");
    output.push_str(&format!("{}", info.type_));

    // Value (if present)
    if let Some(ref val) = info.value {
        output.push_str(" :=\n  ");
        output.push_str(&format!("{val}"));
    }

    output
}

/// Format an inductive declaration for `#print`.
fn format_inductive(name: &str, ind: &clean_kernel::InductiveVal) -> String {
    let mut output = format!("inductive {name}");

    if !ind.level_params.is_empty() {
        output.push_str(".{");
        for (i, p) in ind.level_params.iter().enumerate() {
            if i > 0 {
                output.push_str(", ");
            }
            output.push_str(&format!("{p}"));
        }
        output.push('}');
    }

    output.push_str(" : ");
    output.push_str(&format!("{}", ind.type_));

    output.push_str("\nnumber of parameters: ");
    output.push_str(&ind.num_params.to_string());

    output.push_str("\nconstructors:");
    for ctor_name in &ind.constructor_names {
        output.push_str("\n  ");
        output.push_str(&format!("{ctor_name}"));
    }

    output
}

/// Elaborate `#print name`: look up a declaration by name and format it.
///
/// Searches the environment for a constant with the given name and produces
/// a human-readable summary including:
/// - Declaration kind (def, theorem, axiom, opaque)
/// - Universe parameters (if any)
/// - Type
/// - Value/proof (if available)
///
/// Also checks inductives, constructors, and recursors if no constant is found.
///
/// # Errors
///
/// Returns [`ElabError::UnknownIdent`] if no declaration with that name exists
/// in the environment.
///
/// # Example
///
/// ```text
/// #print Nat.add   -- def Nat.add : Nat → Nat → Nat := ...
/// ```
pub fn elab_print(env: &Environment, name: &str) -> Result<PrintResult, ElabError> {
    let n = Name::from_string(name);

    // Try constant lookup first (definitions, theorems, axioms, opaques).
    if let Some(info) = env.get_const(&n) {
        return Ok(PrintResult {
            output: format_constant(name, info),
        });
    }

    // Try inductive lookup.
    if let Some(ind) = env.get_inductive(&n) {
        return Ok(PrintResult {
            output: format_inductive(name, ind),
        });
    }

    // Try constructor lookup.
    if let Some(ctor) = env.get_constructor(&n) {
        let output = format!(
            "constructor {name} : (part of {})\n  num_fields: {}, num_params: {}",
            ctor.inductive_name, ctor.num_fields, ctor.num_params
        );
        return Ok(PrintResult { output });
    }

    // Try recursor lookup.
    if let Some(rec) = env.get_recursor(&n) {
        let output = format!(
            "recursor {name}\n  num_params: {}\n  num_indices: {}\n  num_motives: {}\n  num_minors: {}",
            rec.num_params, rec.num_indices, rec.num_motives, rec.num_minors
        );
        return Ok(PrintResult { output });
    }

    Err(ElabError::UnknownIdent(name.to_owned()))
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Expr, Level};

    // -- elab_check -----------------------------------------------------------

    #[test]
    fn test_check_sort_prop() {
        let env = Environment::new();
        // Prop = Sort 0; its type should be Type = Sort 1
        let prop = Expr::sort(Level::zero());
        let result = elab_check(&env, &prop).expect("should check Prop");
        assert!(!result.ty.is_empty(), "type string should not be empty");
        assert!(!result.expr.is_empty(), "expr string should not be empty");
        // Display format: "Sort(0) : Sort(1)" or similar
        let display = format!("{result}");
        assert!(
            display.contains(':'),
            "display should contain colon separator"
        );
    }

    #[test]
    fn test_check_sort_type() {
        let env = Environment::new();
        // Type 0 = Sort 1; its type should be Sort 2
        let type0 = Expr::sort(Level::succ(Level::zero()));
        let result = elab_check(&env, &type0).expect("should check Type");
        assert!(!result.ty.is_empty());
    }

    #[test]
    fn test_check_invalid_expr_returns_error() {
        let env = Environment::new();
        // A constant not in the environment should fail type inference
        let bad = Expr::const_(Name::from_string("nonexistent"), vec![]);
        let err = elab_check(&env, &bad);
        assert!(err.is_err(), "should fail for unknown constant");
    }

    // -- elab_eval ------------------------------------------------------------

    #[test]
    fn test_eval_sort_reduces_to_itself() {
        let env = Environment::new();
        // Sort 0 is already in WHNF
        let prop = Expr::sort(Level::zero());
        let result = elab_eval(&env, &prop).expect("should eval Prop");
        assert!(!result.value.is_empty(), "value should not be empty");
    }

    #[test]
    fn test_eval_invalid_expr_returns_error() {
        let env = Environment::new();
        let bad = Expr::const_(Name::from_string("nonexistent"), vec![]);
        let err = elab_eval(&env, &bad);
        assert!(err.is_err(), "should fail for unknown constant");
    }

    // -- elab_print -----------------------------------------------------------

    #[test]
    fn test_print_unknown_name_returns_error() {
        let env = Environment::new();
        let err = elab_print(&env, "nonexistent.name");
        assert!(err.is_err(), "should fail for unknown name");
        match err {
            Err(ElabError::UnknownIdent(name)) => {
                assert_eq!(name, "nonexistent.name");
            }
            other => panic!("expected UnknownIdent, got {other:?}"),
        }
    }

    #[test]
    fn test_print_registered_axiom() {
        let mut env = Environment::new();
        // Register a simple axiom: `axiom myAxiom : Prop`
        // Prop = Sort(0), its type is Type = Sort(1), which is valid.
        let decl = clean_kernel::Declaration::Axiom {
            name: Name::from_string("myAxiom"),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
        };
        env.add_decl(decl).expect("should register axiom");

        let result = elab_print(&env, "myAxiom").expect("should find registered axiom");
        assert!(
            result.output.contains("myAxiom"),
            "output should contain the name: {}",
            result.output
        );
        assert!(
            result.output.contains("axiom"),
            "output should identify as axiom: {}",
            result.output
        );
        assert!(
            result.output.contains(':'),
            "output should contain type separator: {}",
            result.output
        );
    }

    #[test]
    fn test_print_definition_with_value() {
        let mut env = Environment::new();
        // def myDef : Prop := Prop
        // Sort(0) : Sort(1), and Sort(0) : Sort(1), so type-checks.
        let decl = clean_kernel::Declaration::Definition {
            name: Name::from_string("myDef"),
            level_params: vec![],
            type_: Expr::sort(Level::succ(Level::zero())), // Type = Sort(1)
            value: Expr::sort(Level::zero()),              // Prop = Sort(0)
            is_reducible: true,
        };
        env.add_decl(decl).expect("should register definition");

        let result = elab_print(&env, "myDef").expect("should find registered def");
        assert!(
            result.output.contains(":="),
            "definition output should contain := for value: {}",
            result.output
        );
    }

    #[test]
    fn test_check_result_display() {
        let cr = CheckResult {
            expr: "Nat.zero".into(),
            ty: "Nat".into(),
        };
        assert_eq!(format!("{cr}"), "Nat.zero : Nat");
    }

    #[test]
    fn test_eval_result_display() {
        let er = EvalResult { value: "42".into() };
        assert_eq!(format!("{er}"), "42");
    }

    #[test]
    fn test_print_result_display() {
        let pr = PrintResult {
            output: "def foo : Nat := 0".into(),
        };
        assert_eq!(format!("{pr}"), "def foo : Nat := 0");
    }
}
