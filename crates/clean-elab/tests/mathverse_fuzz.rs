// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Property-test fuzzer for the mathverse tactic, with Lean 4's mathverse as oracle.
//!
//! Generates randomized small Presburger formulas, runs both clean's
//! `omega(&mut ProofState)` tactic and Lean 4's `mathverse` tactic (via the
//! subprocess oracle harness), and flags disagreements:
//!
//! ```text
//!   * clean says `Unsat`,     Lean 4 says `Maybe` → cross-check via
//!       exhaustive integer-witness search over `[-WITNESS_BOUND, WITNESS_BOUND]^k`:
//!         - witness FOUND          → CONFIRMED soundness bug (test fails)
//!         - no witness in range    → clean-stronger disagreement
//!                                    (Lean 4 mathverse is also incomplete;
//!                                    clean caught what it missed)
//!   * clean says not-`Unsat`,  Lean 4 says `Unsat` → incompleteness
//!   * Both say `Unsat` / both say not-`Unsat`      → agreement
//! ```
//!
//! We classify clean's verdict by combining the `omega(state)` return value
//! with an inspection of the error reason. The key insight: when the
//! certified decision procedure says Unsat but proof reconstruction fails,
//! `mathverse` returns an error whose reason starts with
//! `"certified arithmetic contradiction has no kernel proof"` (or the
//! modular analogue). That error case is still a "decision said Unsat" from
//! the soundness perspective — only the kernel-checked proof is missing.
//! For the purpose of fuzzing the decision procedure, both Ok and that
//! specific error are treated as clean-Unsat.
//!
//! Env-gated on `CLEAN_MATHVERSE_ORACLE=1` because each Lean subprocess takes
//! ~1s. Number of cases controlled by `CLEAN_MATHVERSE_FUZZ_CASES` (default 60).
//! See `docs/DESIGN_MATHVERSE_COMPLETION.md` §5 PR-4.

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;
use std::time::Duration;

use clean_elab::tactic::{omega, LocalDecl, ProofState, TacticError};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, FVarId};
use proptest::prelude::*;
use proptest::test_runner::{Config, TestRunner};

// =============================================================================
// Lean 4 oracle subprocess harness
// =============================================================================
//
// Inlined here (rather than imported from `mathverse_lean4_oracle.rs`) because Rust
// integration test files are independent compilation units. The logic mirrors
// the same harness; keep in sync.

#[derive(Debug, Clone, PartialEq, Eq)]
enum OracleAnswer {
    /// Lean 4 mathverse refuted the formula (it's ℤ-unsat).
    Unsat,
    /// Lean 4 mathverse couldn't refute (likely ℤ-sat or beyond its reach).
    Maybe,
    /// Harness error (no binary, timeout, parser error). Skip rather than fail.
    Unavailable(String),
}

fn lean4_binary() -> Option<PathBuf> {
    if let Ok(p) = std::env::var("CLEAN_LEAN4_BIN") {
        let p = PathBuf::from(p);
        if p.exists() {
            return Some(p);
        }
    }
    if let Some(home) = std::env::var_os("HOME") {
        let p = PathBuf::from(home).join(".elan/bin/lean");
        if p.exists() {
            return Some(p);
        }
    }
    let out = Command::new("which").arg("lean").output().ok()?;
    if !out.status.success() {
        return None;
    }
    let p = PathBuf::from(String::from_utf8_lossy(&out.stdout).trim());
    p.exists().then_some(p)
}

fn lean4_mathverse_decides_unsat(formula: &str, num_vars: usize) -> OracleAnswer {
    let Some(lean_bin) = lean4_binary() else {
        return OracleAnswer::Unavailable("no lean binary found".to_string());
    };

    let tmp = match tempfile::tempdir() {
        Ok(d) => d,
        Err(e) => return OracleAnswer::Unavailable(format!("tempdir: {e}")),
    };
    let lean_file = tmp.path().join("oracle.lean");

    let binders: String = (0..num_vars)
        .map(|i| format!("(x{i} : Int)"))
        .collect::<Vec<_>>()
        .join(" ");

    let source = if binders.is_empty() {
        format!("example : ¬ ({formula}) := by omega\n")
    } else {
        format!("example {binders} : ¬ ({formula}) := by omega\n")
    };

    if let Err(e) =
        std::fs::File::create(&lean_file).and_then(|mut f| f.write_all(source.as_bytes()))
    {
        return OracleAnswer::Unavailable(format!("write source: {e}"));
    }

    let mut cmd = Command::new(&lean_bin);
    cmd.arg(&lean_file);
    cmd.current_dir(tmp.path());

    let child = match cmd
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
    {
        Ok(c) => c,
        Err(e) => return OracleAnswer::Unavailable(format!("spawn lean: {e}")),
    };

    let output = match wait_with_timeout(child, Duration::from_secs(30)) {
        Ok(o) => o,
        Err(e) => return OracleAnswer::Unavailable(format!("lean run: {e}")),
    };

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let combined = format!("{stdout}{stderr}");

    if combined.contains("omega could not prove")
        || combined.contains("omega could not solve")
        || combined.contains("unsolved goals")
        || combined.contains("no progress")
    {
        return OracleAnswer::Maybe;
    }
    if combined.contains("error:") {
        return OracleAnswer::Unavailable(format!(
            "lean reported an error other than omega failure: {combined}"
        ));
    }
    if !output.status.success() {
        return OracleAnswer::Unavailable(format!(
            "lean exited non-zero (exit {}): {combined}",
            output.status
        ));
    }
    OracleAnswer::Unsat
}

fn wait_with_timeout(
    mut child: std::process::Child,
    timeout: Duration,
) -> std::io::Result<std::process::Output> {
    use std::sync::mpsc;
    use std::thread;

    let stdout = child.stdout.take();
    let stderr = child.stderr.take();

    let (tx, rx) = mpsc::channel();
    let stdout_thread = thread::spawn(move || -> Vec<u8> {
        use std::io::Read;
        let mut buf = Vec::new();
        if let Some(mut s) = stdout {
            let _ = s.read_to_end(&mut buf);
        }
        buf
    });
    let stderr_thread = thread::spawn(move || -> Vec<u8> {
        use std::io::Read;
        let mut buf = Vec::new();
        if let Some(mut s) = stderr {
            let _ = s.read_to_end(&mut buf);
        }
        buf
    });

    let id = child.id();
    thread::spawn(move || {
        let status = child.wait();
        let _ = tx.send(status);
    });

    match rx.recv_timeout(timeout) {
        Ok(status) => {
            let stdout_buf = stdout_thread.join().unwrap_or_default();
            let stderr_buf = stderr_thread.join().unwrap_or_default();
            Ok(std::process::Output {
                status: status?,
                stdout: stdout_buf,
                stderr: stderr_buf,
            })
        }
        Err(_) => {
            let _ = Command::new("kill").arg("-9").arg(id.to_string()).status();
            Err(std::io::Error::new(
                std::io::ErrorKind::TimedOut,
                "lean subprocess exceeded 30s",
            ))
        }
    }
}

// =============================================================================
// Random Presburger AST
// =============================================================================
//
// We generate formulas in a single `Constraint` AST and then translate twice:
//   1. To a Lean syntax string (for the Lean 4 oracle).
//   2. To a `ProofState` whose hypotheses are Int-typed comparison expressions
//      that clean's mathverse parser recognises (for `omega(&mut state)`).
// Both translations are mechanical and guarantee semantic equivalence.

/// A term `Σ coeff*x_i + constant` over the integers.
#[derive(Debug, Clone)]
struct LinTerm {
    /// `(var_index, coefficient)` pairs; coefficients may be negative.
    coeffs: Vec<(usize, i64)>,
    constant: i64,
}

/// Comparison relation between two `LinTerm`s.
#[derive(Debug, Clone, Copy)]
enum Rel {
    Le, // ≤
    Ge, // ≥
    Eq, // =
    Lt, // <
    Gt, // >
}

#[derive(Debug, Clone)]
struct Constraint {
    lhs: LinTerm,
    rel: Rel,
    rhs: LinTerm,
}

#[derive(Debug, Clone)]
struct Formula {
    num_vars: usize,
    constraints: Vec<Constraint>,
}

// -----------------------------------------------------------------------------
// proptest strategies
// -----------------------------------------------------------------------------

fn lin_term_strategy(num_vars: usize) -> impl Strategy<Value = LinTerm> {
    // Coefficient distribution: include ±1 (exact-projection path), small ±k
    // (dark-shadow gap zone). Constants in [-10, 10].
    let coeff_choices: Vec<i64> = vec![-5, -3, -2, -1, -1, 1, 1, 2, 2, 3, 4, 5];
    let len = num_vars;
    proptest::collection::vec(prop::sample::select(coeff_choices), len).prop_flat_map(
        move |coeffs| {
            (Just(coeffs), -10_i64..=10_i64).prop_map(|(coeffs, c)| {
                // Optionally drop some coefficients to vary support size.
                let entries: Vec<(usize, i64)> = coeffs
                    .into_iter()
                    .enumerate()
                    .filter(|&(i, k)| k != 0 && (i as i64).wrapping_add(k) % 7 != 0)
                    .collect();
                LinTerm {
                    coeffs: entries,
                    constant: c,
                }
            })
        },
    )
}

fn rel_strategy() -> impl Strategy<Value = Rel> {
    // Bias toward ≤/≥/= (the staple of Pugh-style cases); include some </>.
    prop_oneof![
        3 => Just(Rel::Le),
        3 => Just(Rel::Ge),
        2 => Just(Rel::Eq),
        1 => Just(Rel::Lt),
        1 => Just(Rel::Gt),
    ]
}

fn constraint_strategy(num_vars: usize) -> impl Strategy<Value = Constraint> {
    (
        lin_term_strategy(num_vars),
        rel_strategy(),
        lin_term_strategy(num_vars),
    )
        .prop_map(|(lhs, rel, rhs)| Constraint { lhs, rel, rhs })
}

fn formula_strategy() -> impl Strategy<Value = Formula> {
    (1_usize..=3, 2_usize..=6).prop_flat_map(|(nv, nc)| {
        proptest::collection::vec(constraint_strategy(nv), nc).prop_map(move |constraints| {
            Formula {
                num_vars: nv,
                constraints,
            }
        })
    })
}

// =============================================================================
// Render a Constraint to Lean source syntax (for the Lean 4 oracle)
// =============================================================================

fn render_lin_term_lean(t: &LinTerm) -> String {
    let mut parts: Vec<String> = Vec::new();
    for &(i, k) in &t.coeffs {
        let part = match k {
            1 => format!("x{i}"),
            -1 => format!("(-x{i})"),
            k if k > 0 => format!("{k} * x{i}"),
            k => format!("({k}) * x{i}"),
        };
        parts.push(part);
    }
    if t.constant != 0 || parts.is_empty() {
        let c = t.constant;
        if c >= 0 {
            parts.push(c.to_string());
        } else {
            parts.push(format!("({c})"));
        }
    }
    parts.join(" + ")
}

fn rel_symbol_lean(r: Rel) -> &'static str {
    match r {
        Rel::Le => "≤",
        Rel::Ge => "≥",
        Rel::Eq => "=",
        Rel::Lt => "<",
        Rel::Gt => ">",
    }
}

fn render_constraint_lean(c: &Constraint) -> String {
    format!(
        "({}) {} ({})",
        render_lin_term_lean(&c.lhs),
        rel_symbol_lean(c.rel),
        render_lin_term_lean(&c.rhs)
    )
}

fn render_formula_lean(f: &Formula) -> String {
    f.constraints
        .iter()
        .map(render_constraint_lean)
        .collect::<Vec<_>>()
        .join(" ∧ ")
}

// =============================================================================
// Build a clean Int Expr for a constraint (for the clean mathverse tactic)
// =============================================================================
//
// Variables are FVars whose index equals their var index (the mathverse parser
// uses `id.as_u64() as usize` directly). We use the `Int.le`/`Int.lt`/`Eq Int`
// comparison heads that the mathverse parser recognises, and `Int.add`/`Int.mul`/
// `Int.neg`/`Int.ofNat` for the linear-expression construction.

fn int_ty() -> Expr {
    Expr::const_(Name::from_string("Int"), vec![])
}

fn int_ofnat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

fn int_neg(inner: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Int.neg"), vec![]), inner)
}

fn int_lit(n: i64) -> Expr {
    if n >= 0 {
        int_ofnat(n as u64)
    } else {
        int_neg(int_ofnat((-n) as u64))
    }
}

fn int_add(a: Expr, b: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Int.add"), vec![]), a),
        b,
    )
}

fn int_mul(a: Expr, b: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Int.mul"), vec![]), a),
        b,
    )
}

fn build_lin_term_expr(t: &LinTerm) -> Expr {
    let mut acc: Option<Expr> = None;
    for &(i, k) in &t.coeffs {
        let var = Expr::fvar(FVarId::new(i as u64));
        let term = if k == 1 {
            var
        } else if k == -1 {
            int_neg(var)
        } else {
            int_mul(int_lit(k), var)
        };
        acc = Some(match acc {
            None => term,
            Some(a) => int_add(a, term),
        });
    }
    let c = int_lit(t.constant);
    match acc {
        None => c,
        Some(a) => {
            if t.constant == 0 {
                a
            } else {
                int_add(a, c)
            }
        }
    }
}

/// `Int.le lhs rhs` — 2-arg comparison form recognised by clean mathverse's
/// `parse_direct_binary_comparison`.
fn int_le_expr(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Int.le"), vec![]), lhs),
        rhs,
    )
}

fn int_lt_expr(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Int.lt"), vec![]), lhs),
        rhs,
    )
}

/// `@Eq Int lhs rhs` — 3-arg form matched by the general comparison parser.
fn int_eq_expr(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::zero()]),
                int_ty(),
            ),
            lhs,
        ),
        rhs,
    )
}

fn build_constraint_expr(c: &Constraint) -> Expr {
    let lhs = build_lin_term_expr(&c.lhs);
    let rhs = build_lin_term_expr(&c.rhs);
    match c.rel {
        Rel::Le => int_le_expr(lhs, rhs),
        Rel::Ge => int_le_expr(rhs, lhs), // a ≥ b ⟺ b ≤ a
        Rel::Eq => int_eq_expr(lhs, rhs),
        Rel::Lt => int_lt_expr(lhs, rhs),
        Rel::Gt => int_lt_expr(rhs, lhs), // a > b ⟺ b < a
    }
}

// =============================================================================
// Drive clean mathverse over a generated formula
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
enum CleanAnswer {
    /// `mathverse` closed the goal, OR returned a "certified … no kernel proof"
    /// error (meaning the decision procedure said Unsat but reconstruction
    /// failed). Both are "clean decided Unsat" from the soundness perspective.
    Unsat,
    /// Mathverse returned an error indicating the decision was not Unsat (e.g.
    /// "could not extract linear constraints" from the linarith fallback, or
    /// other non-decision-Unsat error reasons).
    NotUnsat,
}

/// Classify mathverse's verdict. The full mathverse pipeline returns:
///   - `Ok(())` + goal closed: decision Unsat AND a kernel proof was built
///   - `Err(ArithmeticFailed{tactic:"mathverse", reason:"certified arithmetic
///     contradiction has no kernel proof (...)"})`: decision Unsat but proof
///     reconstruction failed (test env may lack the necessary lemma)
///   - `Err(ArithmeticFailed{tactic:"mathverse", reason:"certified modular
///     contradiction has no kernel proof (...)"})`: ditto for modular path
///   - `Err(...)` for other reasons: decision was Sat/Unknown (mathverse fell
///     through to linarith which also failed)
fn classify_mathverse_result(result: &Result<(), TacticError>, complete: bool) -> CleanAnswer {
    if result.is_ok() && complete {
        return CleanAnswer::Unsat;
    }
    if let Err(TacticError::ArithmeticFailed { reason, .. }) = result {
        if reason.contains("certified arithmetic contradiction has no kernel proof")
            || reason.contains("certified modular contradiction has no kernel proof")
        {
            // Decision said Unsat; only the kernel proof step failed.
            return CleanAnswer::Unsat;
        }
    }
    CleanAnswer::NotUnsat
}

/// Build a `ProofState` with the formula's constraints as hypotheses and
/// target `False`, then run clean's `mathverse` tactic.
fn run_clean_mathverse(f: &Formula) -> CleanAnswer {
    let env = Environment::with_prelude();
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    let int_t = int_ty();

    // Declare the variables as Int-typed fvars (indices 0..num_vars). The
    // mathverse parser maps each `FVar(id)` to `LinearExpr::var(id.as_u64() as
    // usize)`. The kernel proof type-checker (invoked by `close_goal`) needs
    // each fvar referenced in a hypothesis type to also live in local_ctx.
    let mut local_ctx: Vec<LocalDecl> = (0..f.num_vars)
        .map(|i| LocalDecl {
            fvar: FVarId::new(i as u64),
            name: format!("x{i}"),
            ty: int_t.clone(),
            value: None,
        })
        .collect();

    // Then the constraint hypotheses (indices 1000..).
    for (i, c) in f.constraints.iter().enumerate() {
        local_ctx.push(LocalDecl {
            fvar: FVarId::new((1_000 + i) as u64),
            name: format!("h{i}"),
            ty: build_constraint_expr(c),
            value: None,
        });
    }

    let mut state = ProofState::with_context(env, false_ty, local_ctx);

    // Catch any panic from mathverse defensively so the fuzz driver continues.
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let r = omega(&mut state);
        let complete = state.is_complete();
        (r, complete)
    }));
    match outcome {
        Ok((result, complete)) => classify_mathverse_result(&result, complete),
        Err(_) => CleanAnswer::NotUnsat,
    }
}

// =============================================================================
// Disagreement classification
// =============================================================================

#[derive(Debug)]
enum Outcome {
    AgreeUnsat,
    AgreeNotUnsat,
    /// clean refutes, Lean 4 doesn't, AND an exhaustive bounded-range
    /// search FOUND an integer witness — clean is genuinely unsound on
    /// this case. The test hard-fails.
    SoundnessConfirmed {
        formula_lean: String,
        num_vars: usize,
        witness: Vec<i64>,
    },
    /// clean refutes, Lean 4 doesn't, AND no witness exists in the
    /// search range — clean caught what Lean 4 missed (or the witness
    /// is outside the bounded range, which would itself be a separate
    /// soundness review). Informational; doesn't fail the test.
    Disagreement {
        formula_lean: String,
        num_vars: usize,
    },
    Incompleteness {
        formula_lean: String,
        num_vars: usize,
    },
    Skipped(String),
}

/// Half-width of the exhaustive integer-witness search cube. With the
/// fuzz coefficient range `[-5, 5]` and constants `[-10, 10]`, real
/// solutions to the random Presburger formulas usually live near zero;
/// a cube of `±WITNESS_BOUND` per variable provides a strong soundness
/// check for the cases this fuzzer exercises. For 3 variables this is
/// `(2·30+1)^3 ≈ 226k` evaluations per case — sub-second.
const WITNESS_BOUND: i64 = 30;

/// Evaluate a `LinTerm` at the given integer assignment.
fn eval_lin_term(t: &LinTerm, assign: &[i64]) -> i64 {
    let mut acc = t.constant;
    for &(i, k) in &t.coeffs {
        acc += k * assign[i];
    }
    acc
}

fn eval_constraint(c: &Constraint, assign: &[i64]) -> bool {
    let l = eval_lin_term(&c.lhs, assign);
    let r = eval_lin_term(&c.rhs, assign);
    match c.rel {
        Rel::Le => l <= r,
        Rel::Ge => l >= r,
        Rel::Eq => l == r,
        Rel::Lt => l < r,
        Rel::Gt => l > r,
    }
}

fn eval_formula(f: &Formula, assign: &[i64]) -> bool {
    f.constraints.iter().all(|c| eval_constraint(c, assign))
}

/// Exhaustive bounded integer-witness search over `[-WITNESS_BOUND, WITNESS_BOUND]^num_vars`.
/// Returns the first satisfying assignment found, or `None` if none exists in the range.
fn find_witness(f: &Formula) -> Option<Vec<i64>> {
    let n = f.num_vars;
    let radius = WITNESS_BOUND;
    let side = (2 * radius + 1) as usize;
    let total = side.checked_pow(n as u32)?;
    let mut assign = vec![-radius; n];
    for idx in 0..total {
        // Mixed-radix decode: assign[k] = (-radius + (idx / side^k) mod side)
        let mut q = idx;
        for slot in assign.iter_mut() {
            *slot = -radius + (q % side) as i64;
            q /= side;
        }
        if eval_formula(f, &assign) {
            return Some(assign.clone());
        }
    }
    None
}

fn compare_one(f: &Formula) -> Outcome {
    let lean_str = render_formula_lean(f);
    let lean4 = lean4_mathverse_decides_unsat(&lean_str, f.num_vars);
    match lean4 {
        OracleAnswer::Unavailable(why) => Outcome::Skipped(why),
        OracleAnswer::Unsat => {
            let clean = run_clean_mathverse(f);
            if clean == CleanAnswer::Unsat {
                Outcome::AgreeUnsat
            } else {
                Outcome::Incompleteness {
                    formula_lean: lean_str,
                    num_vars: f.num_vars,
                }
            }
        }
        OracleAnswer::Maybe => {
            let clean = run_clean_mathverse(f);
            if clean == CleanAnswer::Unsat {
                // clean refutes, Lean 4 didn't. Cross-check with an
                // independent witness search: if some integer point in
                // [-WITNESS_BOUND, WITNESS_BOUND]^num_vars satisfies the
                // formula, clean is unsound. Otherwise clean caught what
                // Lean 4 (also incomplete) missed.
                if let Some(witness) = find_witness(f) {
                    Outcome::SoundnessConfirmed {
                        formula_lean: lean_str,
                        num_vars: f.num_vars,
                        witness,
                    }
                } else {
                    Outcome::Disagreement {
                        formula_lean: lean_str,
                        num_vars: f.num_vars,
                    }
                }
            } else {
                Outcome::AgreeNotUnsat
            }
        }
    }
}

fn skip_unless_enabled() -> bool {
    if std::env::var("CLEAN_MATHVERSE_ORACLE").is_ok() {
        return true;
    }
    eprintln!("skip: mathverse fuzz test gated on CLEAN_MATHVERSE_ORACLE=1");
    false
}

fn fuzz_case_count() -> u32 {
    std::env::var("CLEAN_MATHVERSE_FUZZ_CASES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(60)
}

// =============================================================================
// Sanity checks (cheap; do not call Lean)
// =============================================================================

#[test]
fn lin_term_rendering_basic() {
    let t = LinTerm {
        coeffs: vec![(0, 2), (1, -1)],
        constant: 3,
    };
    let s = render_lin_term_lean(&t);
    assert_eq!(s, "2 * x0 + (-x1) + 3");
}

#[test]
fn lin_term_rendering_negative_constant() {
    let t = LinTerm {
        coeffs: vec![(0, 1)],
        constant: -5,
    };
    let s = render_lin_term_lean(&t);
    assert_eq!(s, "x0 + (-5)");
}

#[test]
fn mathverse_recognises_x_le_0_and_x_ge_1_as_unsat() {
    // x0 ≤ 0 ∧ x0 ≥ 1 — clear ℤ-UNSAT.
    let f = Formula {
        num_vars: 1,
        constraints: vec![
            Constraint {
                lhs: LinTerm {
                    coeffs: vec![(0, 1)],
                    constant: 0,
                },
                rel: Rel::Le,
                rhs: LinTerm {
                    coeffs: vec![],
                    constant: 0,
                },
            },
            Constraint {
                lhs: LinTerm {
                    coeffs: vec![(0, 1)],
                    constant: 0,
                },
                rel: Rel::Ge,
                rhs: LinTerm {
                    coeffs: vec![],
                    constant: 1,
                },
            },
        ],
    };
    assert_eq!(run_clean_mathverse(&f), CleanAnswer::Unsat);
}

#[test]
fn mathverse_recognises_x_in_0_to_5_as_not_unsat() {
    // x0 ≤ 5 ∧ x0 ≥ 0 — clearly ℤ-SAT (e.g., x0 = 3).
    let f = Formula {
        num_vars: 1,
        constraints: vec![
            Constraint {
                lhs: LinTerm {
                    coeffs: vec![(0, 1)],
                    constant: 0,
                },
                rel: Rel::Le,
                rhs: LinTerm {
                    coeffs: vec![],
                    constant: 5,
                },
            },
            Constraint {
                lhs: LinTerm {
                    coeffs: vec![(0, 1)],
                    constant: 0,
                },
                rel: Rel::Ge,
                rhs: LinTerm {
                    coeffs: vec![],
                    constant: 0,
                },
            },
        ],
    };
    assert_eq!(run_clean_mathverse(&f), CleanAnswer::NotUnsat);
}

// =============================================================================
// The main fuzz driver
// =============================================================================

#[test]
fn mathverse_fuzz_against_lean4_oracle() {
    if !skip_unless_enabled() {
        return;
    }

    use std::cell::RefCell;

    let cases = fuzz_case_count();
    let mut runner = TestRunner::new(Config {
        cases,
        max_shrink_iters: 0, // shrinking is expensive (re-invokes Lean); print raw failure.
        failure_persistence: None,
        ..Config::default()
    });

    // total, agree_unsat, agree_not_unsat, confirmed_soundness, disagreement, incompleteness, skipped
    let stats = RefCell::new((
        0_u32,
        0_u32,
        0_u32,
        Vec::<(String, usize, Vec<i64>)>::new(),
        Vec::<(String, usize)>::new(),
        Vec::<(String, usize)>::new(),
        Vec::<String>::new(),
    ));

    let strat = formula_strategy();
    let _ = runner.run(&strat, |f| {
        let mut s = stats.borrow_mut();
        s.0 += 1;
        let total = s.0;
        eprintln!("[fuzz {total}/{cases}] {}", render_formula_lean(&f));
        match compare_one(&f) {
            Outcome::AgreeUnsat => {
                s.1 += 1;
                eprintln!("    agree: UNSAT");
            }
            Outcome::AgreeNotUnsat => {
                s.2 += 1;
                eprintln!("    agree: not-UNSAT");
            }
            Outcome::SoundnessConfirmed {
                formula_lean,
                num_vars,
                witness,
            } => {
                eprintln!(
                    "    *** SOUNDNESS BUG: clean refuted but witness assignment exists \
                     (num_vars={num_vars}, witness={witness:?}): {formula_lean}"
                );
                s.3.push((formula_lean, num_vars, witness));
            }
            Outcome::Disagreement {
                formula_lean,
                num_vars,
            } => {
                eprintln!(
                    "    [clean-stronger] clean refuted; Lean 4 gave up; no witness in \
                     ±{WITNESS_BOUND}^{num_vars} (num_vars={num_vars}): {formula_lean}"
                );
                s.4.push((formula_lean, num_vars));
            }
            Outcome::Incompleteness {
                formula_lean,
                num_vars,
            } => {
                eprintln!(
                    "    [incomplete] Lean 4 refuted; clean didn't (num_vars={num_vars}): {formula_lean}"
                );
                s.5.push((formula_lean, num_vars));
            }
            Outcome::Skipped(why) => {
                eprintln!("    [skip] {why}");
                s.6.push(why);
            }
        }
        Ok(())
    });

    let (total, agree_unsat, agree_not, confirmed_soundness, disagreement, incompleteness, skipped) =
        stats.into_inner();

    eprintln!("\n========== mathverse fuzz summary ==========");
    eprintln!("total cases run             : {total}");
    eprintln!("agreement (both UNSAT)      : {agree_unsat}");
    eprintln!("agreement (both not)        : {agree_not}");
    eprintln!(
        "CONFIRMED SOUNDNESS BUGS    : {} (clean wrongly refuted; witness found)",
        confirmed_soundness.len()
    );
    for (i, (s, nv, w)) in confirmed_soundness.iter().enumerate() {
        eprintln!("  [B{i}] (num_vars={nv}, witness={w:?}) {s}");
    }
    eprintln!(
        "clean-stronger disagreements: {} (clean refuted; Lean 4 gave up; no witness)",
        disagreement.len()
    );
    for (i, (s, nv)) in disagreement.iter().enumerate() {
        eprintln!("  [D{i}] (num_vars={nv}) {s}");
    }
    eprintln!(
        "incompleteness gaps         : {} (Lean 4 refutes; clean does not)",
        incompleteness.len()
    );
    for (i, (s, nv)) in incompleteness.iter().enumerate() {
        eprintln!("  [I{i}] (num_vars={nv}) {s}");
    }
    eprintln!("skipped (harness)           : {}", skipped.len());
    for (i, s) in skipped.iter().enumerate().take(5) {
        eprintln!("  [K{i}] {s}");
    }
    eprintln!("=========================================");

    // Hard-fail only on CONFIRMED soundness violations. Independent
    // witness search has SHOWN an integer assignment satisfies a formula
    // clean refuted — that's a real bug, not Lean-4-incompleteness.
    assert!(
        confirmed_soundness.is_empty(),
        "mathverse soundness bug(s) found with witnesses: see eprintln output above"
    );
}
