// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native-Rust execution for `native_decide`, with kernel reduction fallback.
//!
//! The native path lowers a ground goal to a Rust program and runs it. The
//! program is compiled only by the admitted Trust oracle compiler
//! ([`crate::oracle_compiler`]); without one, the Clean kernel decides. The
//! kernel is the authority for ACCEPTANCE either way: a native `true` is
//! re-derived by kernel reduction of the `Decidable` instance before any proof
//! is returned, and a native `false` only fails the tactic.

use std::collections::HashMap;
use std::path::PathBuf;
use std::process::Command;
use std::sync::{Arc, Mutex, OnceLock};

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};
use tempfile::tempdir;
use thiserror::Error;

use crate::oracle_compiler::{oracle_compiler, OracleCompiler};
use crate::tactic::core::{Goal, ProofState};
use crate::tactic::equality::match_equality;

/// Fixed protocol labels, never a rendered source Name. A single quoted
/// `Nat.add` component is distinct from the canonical qualified builtin.
fn builtin_label(name: &Name) -> Option<&'static str> {
    [
        "Bool.true",
        "Bool.false",
        "Int.ofNat",
        "Int.negSucc",
        "Int.neg",
        "Neg.neg",
        "Int.add",
        "Int.sub",
        "Int.mul",
        "Nat.zero",
        "Nat.one",
        "Nat.succ",
        "Nat.add",
        "Nat.mul",
        "Nat.sub",
        "Nat.pow",
        "HAdd.hAdd",
        "Add.add",
        "HMul.hMul",
        "Mul.mul",
        "HSub.hSub",
        "Sub.sub",
        "HPow.hPow",
        "Pow.pow",
        "Decidable.isTrue",
        "Decidable.isFalse",
    ]
    .into_iter()
    .find(|label| name == &Name::from_string(label))
}

#[derive(Debug, Clone)]
pub(crate) enum NativeDecideExecOutcome {
    Proved(Expr),
    Refuted,
}

#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub(crate) enum NativeDecideExecError {
    #[error("unsupported native_decide proposition: {detail}")]
    Unsupported { detail: String },
    #[error("failed to compile native_decide proposition: {detail}")]
    NativeCompileFailed { detail: String },
    #[error("failed to execute native_decide expression: {detail}")]
    ExecutionFailed { detail: String },
}

#[derive(Debug, Clone)]
pub(crate) struct NativeCompileResult {
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) rust_source: Arc<str>,
    pub(crate) bytecode: Arc<[u8]>,
}

/// A compiled oracle is keyed by the goal AND the compiler that built it.
type NativeDecideCacheKey = (PathBuf, Expr);

#[derive(Debug, Default)]
pub(crate) struct NativeDecideCache {
    entries: Mutex<HashMap<NativeDecideCacheKey, NativeCompileResult>>,
}

impl NativeDecideCache {
    fn get(&self, key: &NativeDecideCacheKey) -> Option<NativeCompileResult> {
        self.entries
            .lock()
            .expect("native_decide cache poisoned")
            .get(key)
            .cloned()
    }

    fn get_or_insert_with(
        &self,
        key: NativeDecideCacheKey,
        build: impl FnOnce() -> Result<NativeCompileResult, NativeDecideExecError>,
    ) -> Result<NativeCompileResult, NativeDecideExecError> {
        if let Some(cached) = self.get(&key) {
            return Ok(cached);
        }
        let compiled = build()?;
        let mut entries = self.entries.lock().expect("native_decide cache poisoned");
        Ok(entries
            .entry(key)
            .or_insert_with(|| compiled.clone())
            .clone())
    }

    #[cfg(test)]
    fn clear(&self) {
        self.entries
            .lock()
            .expect("native_decide cache poisoned")
            .clear();
    }

    #[cfg(test)]
    fn len(&self) -> usize {
        self.entries
            .lock()
            .expect("native_decide cache poisoned")
            .len()
    }
}

static NATIVE_DECIDE_CACHE: OnceLock<NativeDecideCache> = OnceLock::new();

fn native_decide_cache() -> &'static NativeDecideCache {
    NATIVE_DECIDE_CACHE.get_or_init(NativeDecideCache::default)
}

#[cfg(test)]
pub(crate) fn clear_native_decide_cache_for_tests() {
    native_decide_cache().clear();
}

#[cfg(test)]
pub(crate) fn native_decide_cache_len_for_tests() -> usize {
    native_decide_cache().len()
}

/// Lowers a goal to an oracle program and compiles it with an admitted Trust
/// compiler -- the only way a native program is built.
#[derive(Debug, Clone, Copy)]
pub(crate) struct NativeRunner<'a> {
    compiler: &'a OracleCompiler,
}

impl<'a> NativeRunner<'a> {
    pub(crate) fn new(compiler: &'a OracleCompiler) -> Self {
        Self { compiler }
    }

    pub(crate) fn compile(
        &self,
        target: &Expr,
    ) -> Result<NativeCompileResult, NativeDecideExecError> {
        let target = strip_metadata(target).clone();
        let key = (self.compiler.path().to_path_buf(), target.clone());
        native_decide_cache().get_or_insert_with(key, || {
            let rust_bool = lower_decidable_to_rust(&target)?;
            let rust_source = render_native_program(&rust_bool);
            let bytecode = compile_rust_program(self.compiler, &rust_source)?;
            Ok(NativeCompileResult {
                rust_source: Arc::<str>::from(rust_source),
                bytecode: Arc::<[u8]>::from(bytecode.into_boxed_slice()),
            })
        })
    }
}

pub(crate) fn native_eval_bool(
    compiled: &NativeCompileResult,
) -> Result<bool, NativeDecideExecError> {
    let dir = tempdir().map_err(|err| NativeDecideExecError::ExecutionFailed {
        detail: format!("failed to create temp dir for native_decide: {err}"),
    })?;
    let binary = dir.path().join(native_binary_name());
    std::fs::write(&binary, compiled.bytecode.as_ref()).map_err(|err| {
        NativeDecideExecError::ExecutionFailed {
            detail: format!("failed to materialize native_decide binary: {err}"),
        }
    })?;
    make_executable(&binary)?;
    let output =
        Command::new(&binary)
            .output()
            .map_err(|err| NativeDecideExecError::ExecutionFailed {
                detail: format!("failed to launch native_decide binary: {err}"),
            })?;
    if !output.status.success() {
        return Err(NativeDecideExecError::ExecutionFailed {
            detail: format!(
                "native_decide binary exited with {}: stderr={}",
                output.status,
                String::from_utf8_lossy(&output.stderr).trim(),
            ),
        });
    }
    match String::from_utf8_lossy(&output.stdout).trim() {
        "true" => Ok(true),
        "false" => Ok(false),
        other => Err(NativeDecideExecError::ExecutionFailed {
            detail: format!("native_decide binary returned unexpected output: {other:?}"),
        }),
    }
}

/// Decide `goal` natively through this process's admitted oracle compiler
/// ([`oracle_compiler`]), or by the kernel when there is none.
pub(crate) fn execute_native_decide(
    state: &ProofState,
    goal: &Goal,
) -> Result<NativeDecideExecOutcome, NativeDecideExecError> {
    execute_native_decide_with(state, goal, oracle_compiler().ok())
}

/// [`execute_native_decide`] with the oracle compiler given: `None` is the
/// kernel-only path, which is also where every native failure lands.
pub(crate) fn execute_native_decide_with(
    state: &ProofState,
    goal: &Goal,
    compiler: Option<&OracleCompiler>,
) -> Result<NativeDecideExecOutcome, NativeDecideExecError> {
    let target = state.metas().instantiate(&goal.target);
    let decidable_expr = synthesize_decidable_expr(state, goal, &target)?;
    if let Some(compiler) = compiler {
        let decided = |verdict: &str| {
            tracing::debug!(
                compiler = %compiler.path().display(),
                commit = compiler.commit(),
                verdict,
                "native_decide: the Trust oracle decided"
            );
        };
        match NativeRunner::new(compiler).compile(&target) {
            Ok(compiled) => match native_eval_bool(&compiled) {
                // The kernel re-derives the proof from the Decidable instance.
                Ok(true) => {
                    decided("true");
                    return classify_decidable_result(&state.whnf(goal, &decidable_expr));
                }
                Ok(false) => {
                    decided("false");
                    return Ok(NativeDecideExecOutcome::Refuted);
                }
                Err(err) => tracing::debug!(error = %err, "native_decide native execution failed"),
            },
            Err(err) => {
                tracing::debug!(error = %err, "native_decide native compilation unavailable")
            }
        }
    }
    tracing::debug!("native_decide: the Clean kernel decides");
    execute_kernel_native_decide(state, goal, &target, &decidable_expr)
}

fn execute_kernel_native_decide(
    state: &ProofState,
    goal: &Goal,
    target: &Expr,
    decidable_expr: &Expr,
) -> Result<NativeDecideExecOutcome, NativeDecideExecError> {
    match reduce_bool_result(state, goal, &mk_decidable_bool_expr(target, decidable_expr))? {
        true => classify_decidable_result(&state.whnf(goal, decidable_expr)),
        false => Ok(NativeDecideExecOutcome::Refuted),
    }
}

fn synthesize_decidable_expr(
    state: &ProofState,
    goal: &Goal,
    target: &Expr,
) -> Result<Expr, NativeDecideExecError> {
    if matches!(target.kind(), ExprKind::Const(name, _) if name == &Name::from_string("True")) {
        return Ok(Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Decidable.isTrue"), vec![]),
                target.clone(),
            ),
            Expr::const_(Name::from_string("True.intro"), vec![]),
        ));
    }
    if matches!(target.kind(), ExprKind::Const(name, _) if name == &Name::from_string("False")) {
        return Ok(Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Decidable.isFalse"), vec![]),
                target.clone(),
            ),
            Expr::lam(BinderInfo::Default, target.clone(), Expr::bvar(0)),
        ));
    }
    let (ty, lhs, rhs, _) =
        match_equality(target).map_err(|_| NativeDecideExecError::Unsupported {
            detail: format!("native_decide does not yet synthesize Decidable for: {target:?}"),
        })?;
    let ExprKind::Const(type_name, _) = ty.get_app_fn().kind() else {
        return Err(NativeDecideExecError::Unsupported {
            detail: format!("equality type is not a supported constant: {ty:?}"),
        });
    };
    let dec_eq_name = type_name.clone().str("decEq");
    // Wave 95: Gap 19. The original guard required a full `Declaration`
    // for `<Ty>.decEq`. In the prelude env, `Nat.decEq` / `Bool.decEq`
    // are wired as *native reducers* (no declaration body needed —
    // `reduce_native` fires inside `whnf`). Accept either source so
    // `native_decide` can drive the kernel fallback on `2+2=4 : Nat`
    // and `Bool.true = Bool.true`.
    let has_decl = state.env().get_const(&dec_eq_name).is_some();
    let has_native = state.env().get_native_reducer(&dec_eq_name).is_some();
    if !has_decl && !has_native {
        return Err(NativeDecideExecError::Unsupported {
            detail: format!("no DecidableEq synthesis hook for {type_name}"),
        });
    }
    Ok(Expr::apps(
        Expr::const_(dec_eq_name, vec![]),
        [state.whnf(goal, &lhs), state.whnf(goal, &rhs)],
    ))
}

fn lower_decidable_to_rust(target: &Expr) -> Result<String, NativeDecideExecError> {
    let target = strip_metadata(target);
    if matches!(target.kind(), ExprKind::Const(name, _) if name == &Name::from_string("True")) {
        return Ok("Ok(true)".to_owned());
    }
    if matches!(target.kind(), ExprKind::Const(name, _) if name == &Name::from_string("False")) {
        return Ok("Ok(false)".to_owned());
    }
    let (ty, lhs, rhs, _) =
        match_equality(target).map_err(|_| NativeDecideExecError::Unsupported {
            detail: format!(
                "native_decide native compiler only supports ground equalities: {target:?}"
            ),
        })?;
    match strip_metadata(&ty).kind() {
        ExprKind::Const(name, _) if name == &Name::from_string("Nat") => Ok(format!(
            "nat_eq({}, {})",
            lower_nat_expr(&lhs)?,
            lower_nat_expr(&rhs)?
        )),
        ExprKind::Const(name, _) if name == &Name::from_string("Bool") => Ok(format!(
            "bool_eq({}, {})",
            lower_bool_expr(&lhs)?,
            lower_bool_expr(&rhs)?
        )),
        ExprKind::Const(name, _) if name == &Name::from_string("Int") => Ok(format!(
            "int_eq({}, {})",
            lower_int_expr(&lhs)?,
            lower_int_expr(&rhs)?
        )),
        ExprKind::Const(name, _) if name == &Name::from_string("String") => Ok(format!(
            "string_eq({}, {})",
            lower_string_expr(&lhs)?,
            lower_string_expr(&rhs)?
        )),
        // SOUNDNESS: every other type (including `Float`, whose `==`
        // is NaN-unfaithful and therefore not Decidable-eq-faithful) is
        // rejected honestly so `execute_native_decide` falls back to the
        // trusted kernel reducer instead of emitting a native decision.
        _ => Err(NativeDecideExecError::Unsupported {
            detail: format!(
                "native_decide native compiler only supports Nat/Bool/Int/String equality: {target:?}"
            ),
        }),
    }
}

/// Lower a ground `Bool` term to its native Rust `Eval<bool>` form.
///
/// SOUNDNESS: only the two canonical constructors `Bool.true` / `Bool.false`
/// are accepted. These are exactly the values the kernel's `Bool.decEq` native
/// reducer compares (see `get_bool_val` in the kernel), so `==` on the lowered
/// `bool` faithfully models `Decidable (a = b)` for `Bool`.
fn lower_bool_expr(expr: &Expr) -> Result<String, NativeDecideExecError> {
    let expr = strip_metadata(expr);
    match expr.kind() {
        ExprKind::Const(name, _) => match builtin_label(name).unwrap_or("") {
            "Bool.true" => Ok("Ok(true)".to_owned()),
            "Bool.false" => Ok("Ok(false)".to_owned()),
            _ => Err(NativeDecideExecError::Unsupported {
                detail: format!("unsupported Bool constant in native_decide: {expr:?}"),
            }),
        },
        _ => Err(NativeDecideExecError::Unsupported {
            detail: format!("unsupported Bool expression in native_decide: {expr:?}"),
        }),
    }
}

/// Lower a ground `String` term to its native Rust `Eval<String>` form.
///
/// SOUNDNESS: only literal strings are accepted. The kernel's `String.decEq`
/// native reducer compares `Literal::String` payloads byte-for-byte, so Rust
/// `String` equality faithfully models `Decidable (a = b)` for `String`.
fn lower_string_expr(expr: &Expr) -> Result<String, NativeDecideExecError> {
    let expr = strip_metadata(expr);
    match expr.kind() {
        ExprKind::Lit(clean_kernel::expr::Literal::String(s)) => {
            Ok(format!("Ok({:?}.to_string())", s.as_ref()))
        }
        _ => Err(NativeDecideExecError::Unsupported {
            detail: format!("unsupported String expression in native_decide: {expr:?}"),
        }),
    }
}

/// Lower a ground `Int` term to its native Rust `Eval<i64>` form.
///
/// SOUNDNESS: Int is the Lean inductive `Int.ofNat n` / `Int.negSucc n`, which
/// is exactly the representation the kernel's `Int.decEq` native reducer decodes
/// (see `get_int_val`). We mirror that decode (and the `Int.add/sub/mul/neg`
/// reducers' checked-i64 semantics) and stay inside `i64` — rejecting any
/// out-of-range magnitude — so `==` on the lowered `i64` faithfully models
/// `Decidable (a = b)` for every value we accept. Operators we do not model
/// (e.g. `Int.div`/`Int.mod`, whose Lean semantics are subtle) are rejected
/// so the trusted kernel reducer handles them instead.
fn lower_int_expr(expr: &Expr) -> Result<String, NativeDecideExecError> {
    let expr = strip_metadata(expr);
    if let ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) = expr.kind() {
        // A bare Nat literal denotes `Int.ofNat n` before normalization.
        return lower_int_from_nat(n).map(|v| format!("Ok({v}i64)"));
    }
    let ExprKind::App(_, _) = expr.kind() else {
        return Err(NativeDecideExecError::Unsupported {
            detail: format!("unsupported Int expression in native_decide: {expr:?}"),
        });
    };
    let args = expr.get_app_args();
    let ExprKind::Const(head, _) = strip_metadata(expr.get_app_fn()).kind() else {
        return Err(NativeDecideExecError::Unsupported {
            detail: format!("unsupported Int application head in native_decide: {expr:?}"),
        });
    };
    match builtin_label(head).unwrap_or("") {
        "Int.ofNat" => {
            let n = int_nat_arg(args.last(), expr)?;
            lower_int_from_nat(n).map(|v| format!("Ok({v}i64)"))
        }
        "Int.negSucc" => {
            let n = int_nat_arg(args.last(), expr)?;
            lower_int_negsucc(n, expr).map(|v| format!("Ok({v}i64)"))
        }
        // Unary negation mirrors `reduce_int_neg` (checked_neg).
        "Int.neg" | "Neg.neg" => {
            let arg = args
                .last()
                .ok_or_else(|| NativeDecideExecError::Unsupported {
                    detail: format!("Int.neg missing argument in native_decide: {expr:?}"),
                })?;
            Ok(format!("int_neg({})", lower_int_expr(arg)?))
        }
        // Binary ops mirror `reduce_int_add/sub/mul` (checked_add/sub/mul).
        op @ ("Int.add" | "HAdd.hAdd" | "Add.add" | "Int.sub" | "HSub.hSub" | "Sub.sub"
        | "Int.mul" | "HMul.hMul" | "Mul.mul") => {
            if args.len() < 2 {
                return Err(NativeDecideExecError::Unsupported {
                    detail: format!("unsupported Int arity in native_decide: {expr:?}"),
                });
            }
            let helper = match op {
                "Int.add" | "HAdd.hAdd" | "Add.add" => "int_add",
                "Int.sub" | "HSub.hSub" | "Sub.sub" => "int_sub",
                _ => "int_mul",
            };
            Ok(format!(
                "{helper}({}, {})",
                lower_int_expr(args[args.len() - 2])?,
                lower_int_expr(args[args.len() - 1])?,
            ))
        }
        _ => Err(NativeDecideExecError::Unsupported {
            detail: format!("unsupported Int operator in native_decide: {expr:?}"),
        }),
    }
}

/// Extract the `Nat`-literal argument of an `Int` constructor.
fn int_nat_arg<'a>(
    arg: Option<&&'a Expr>,
    parent: &Expr,
) -> Result<&'a clean_kernel::expr::BigNat, NativeDecideExecError> {
    let arg = arg.ok_or_else(|| NativeDecideExecError::Unsupported {
        detail: format!("Int constructor missing argument in native_decide: {parent:?}"),
    })?;
    match strip_metadata(arg).kind() {
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) => Ok(n),
        _ => Err(NativeDecideExecError::Unsupported {
            detail: format!("Int constructor expects a Nat literal in native_decide: {parent:?}"),
        }),
    }
}

/// Decode a non-negative `Int.ofNat`/bare-Nat magnitude into an in-range `i64`.
fn lower_int_from_nat(n: &clean_kernel::expr::BigNat) -> Result<i64, NativeDecideExecError> {
    let raw = n
        .to_u64()
        .ok_or_else(|| NativeDecideExecError::Unsupported {
            detail: "Int.ofNat magnitude exceeds u64 native_decide subset".to_owned(),
        })?;
    i64::try_from(raw).map_err(|_| NativeDecideExecError::Unsupported {
        detail: "Int.ofNat magnitude exceeds i64 native_decide subset".to_owned(),
    })
}

/// Decode `Int.negSucc n` (which denotes `-(n+1)`) into an in-range `i64`,
/// mirroring the kernel's `get_int_val` range guard exactly.
fn lower_int_negsucc(
    n: &clean_kernel::expr::BigNat,
    parent: &Expr,
) -> Result<i64, NativeDecideExecError> {
    let raw = n
        .to_u64()
        .ok_or_else(|| NativeDecideExecError::Unsupported {
            detail: format!("Int.negSucc magnitude exceeds u64 native subset: {parent:?}"),
        })?;
    let n_plus_1 = raw
        .checked_add(1)
        .ok_or_else(|| NativeDecideExecError::Unsupported {
            detail: format!("Int.negSucc magnitude overflows native subset: {parent:?}"),
        })?;
    if n_plus_1 > i64::MIN.unsigned_abs() {
        return Err(NativeDecideExecError::Unsupported {
            detail: format!("Int.negSucc out of i64 range in native_decide: {parent:?}"),
        });
    }
    // n_plus_1 <= 2^63 so the wrapping negate reproduces -(n+1) exactly,
    // matching the kernel's get_int_val decode.
    Ok((n_plus_1 as i64).wrapping_neg())
}

fn lower_nat_expr(expr: &Expr) -> Result<String, NativeDecideExecError> {
    let expr = strip_metadata(expr);
    match expr.kind() {
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) => n
            .to_u64()
            .map(|n| format!("Ok({n}u64)"))
            .ok_or_else(|| NativeDecideExecError::Unsupported {
                detail: format!("Nat literal exceeds u64 native_decide subset: {expr:?}"),
            }),
        ExprKind::Const(name, _) => match builtin_label(name).unwrap_or("") {
            "Nat.zero" => Ok("Ok(0u64)".to_owned()),
            "Nat.one" => Ok("Ok(1u64)".to_owned()),
            _ => Err(NativeDecideExecError::Unsupported {
                detail: format!("unsupported Nat constant in native_decide: {expr:?}"),
            }),
        },
        ExprKind::App(_, _) => lower_nat_app(expr),
        _ => Err(NativeDecideExecError::Unsupported {
            detail: format!("unsupported Nat expression in native_decide: {expr:?}"),
        }),
    }
}

fn lower_nat_app(expr: &Expr) -> Result<String, NativeDecideExecError> {
    let args = expr.get_app_args();
    let ExprKind::Const(op_name, _) = strip_metadata(expr.get_app_fn()).kind() else {
        return Err(NativeDecideExecError::Unsupported {
            detail: format!("unsupported Nat application head in native_decide: {expr:?}"),
        });
    };
    let op = builtin_label(op_name).unwrap_or("");
    if op == "Nat.succ" {
        let arg = args
            .last()
            .ok_or_else(|| NativeDecideExecError::Unsupported {
                detail: format!("Nat.succ missing argument in native_decide: {expr:?}"),
            })?;
        return Ok(format!("nat_succ({})", lower_nat_expr(arg)?));
    }
    if args.len() < 2 {
        return Err(NativeDecideExecError::Unsupported {
            detail: format!("unsupported Nat arity in native_decide: {expr:?}"),
        });
    }
    let helper = match op {
        "Nat.add" | "HAdd.hAdd" | "Add.add" => "nat_add",
        "Nat.mul" | "HMul.hMul" | "Mul.mul" => "nat_mul",
        "Nat.sub" | "HSub.hSub" | "Sub.sub" => "nat_sub",
        "Nat.pow" | "HPow.hPow" | "Pow.pow" => "nat_pow",
        _ => {
            return Err(NativeDecideExecError::Unsupported {
                detail: format!("unsupported Nat operator in native_decide: {expr:?}"),
            });
        }
    };
    Ok(format!(
        "{helper}({}, {})",
        lower_nat_expr(args[args.len() - 2])?,
        lower_nat_expr(args[args.len() - 1])?,
    ))
}

fn render_native_program(bool_expr: &str) -> String {
    concat!(
        "type Eval<T> = Result<T, &'static str>;\n",
        "fn nat_succ(v: Eval<u64>) -> Eval<u64> { match v { Ok(v) => v.checked_add(1).ok_or(\"native_decide Nat overflow\"), Err(e) => Err(e) } }\n",
        "fn nat_add(l: Eval<u64>, r: Eval<u64>) -> Eval<u64> { match (l, r) { (Ok(l), Ok(r)) => l.checked_add(r).ok_or(\"native_decide Nat overflow\"), (Err(e), _) | (_, Err(e)) => Err(e) } }\n",
        "fn nat_mul(l: Eval<u64>, r: Eval<u64>) -> Eval<u64> { match (l, r) { (Ok(l), Ok(r)) => l.checked_mul(r).ok_or(\"native_decide Nat overflow\"), (Err(e), _) | (_, Err(e)) => Err(e) } }\n",
        "fn nat_sub(l: Eval<u64>, r: Eval<u64>) -> Eval<u64> { match (l, r) { (Ok(l), Ok(r)) => Ok(l.saturating_sub(r)), (Err(e), _) | (_, Err(e)) => Err(e) } }\n",
        "fn nat_pow(l: Eval<u64>, r: Eval<u64>) -> Eval<u64> { match (l, r) { (Ok(l), Ok(r)) => { let e = u32::try_from(r).map_err(|_| \"native_decide exponent too large\")?; l.checked_pow(e).ok_or(\"native_decide Nat overflow\") }, (Err(e), _) | (_, Err(e)) => Err(e) } }\n",
        "fn nat_eq(l: Eval<u64>, r: Eval<u64>) -> Eval<bool> { match (l, r) { (Ok(l), Ok(r)) => Ok(l == r), (Err(e), _) | (_, Err(e)) => Err(e) } }\n",
        "fn bool_eq(l: Eval<bool>, r: Eval<bool>) -> Eval<bool> { match (l, r) { (Ok(l), Ok(r)) => Ok(l == r), (Err(e), _) | (_, Err(e)) => Err(e) } }\n",
        "fn int_neg(v: Eval<i64>) -> Eval<i64> { match v { Ok(v) => v.checked_neg().ok_or(\"native_decide Int overflow\"), Err(e) => Err(e) } }\n",
        "fn int_add(l: Eval<i64>, r: Eval<i64>) -> Eval<i64> { match (l, r) { (Ok(l), Ok(r)) => l.checked_add(r).ok_or(\"native_decide Int overflow\"), (Err(e), _) | (_, Err(e)) => Err(e) } }\n",
        "fn int_sub(l: Eval<i64>, r: Eval<i64>) -> Eval<i64> { match (l, r) { (Ok(l), Ok(r)) => l.checked_sub(r).ok_or(\"native_decide Int overflow\"), (Err(e), _) | (_, Err(e)) => Err(e) } }\n",
        "fn int_mul(l: Eval<i64>, r: Eval<i64>) -> Eval<i64> { match (l, r) { (Ok(l), Ok(r)) => l.checked_mul(r).ok_or(\"native_decide Int overflow\"), (Err(e), _) | (_, Err(e)) => Err(e) } }\n",
        "fn int_eq(l: Eval<i64>, r: Eval<i64>) -> Eval<bool> { match (l, r) { (Ok(l), Ok(r)) => Ok(l == r), (Err(e), _) | (_, Err(e)) => Err(e) } }\n",
        "fn string_eq(l: Eval<String>, r: Eval<String>) -> Eval<bool> { match (l, r) { (Ok(l), Ok(r)) => Ok(l == r), (Err(e), _) | (_, Err(e)) => Err(e) } }\n",
        "fn eval_bool() -> Eval<bool> { __BOOL_EXPR__ }\n",
        "fn main() { match eval_bool() { Ok(r) => print!(\"{}\", if r { \"true\" } else { \"false\" }), Err(e) => { eprintln!(\"{e}\"); std::process::exit(2); } } }\n",
    )
    .replace("__BOOL_EXPR__", bool_expr)
}

/// Compile a generated oracle program with the admitted Trust compiler.
fn compile_rust_program(
    compiler: &OracleCompiler,
    source: &str,
) -> Result<Vec<u8>, NativeDecideExecError> {
    let compile_failed = |detail: String| NativeDecideExecError::NativeCompileFailed { detail };
    let dir = tempdir().map_err(|err| {
        compile_failed(format!(
            "failed to create temp dir for native_decide compile: {err}"
        ))
    })?;
    let source_path = dir.path().join("native_decide.rs");
    let binary_path = dir.path().join(native_binary_name());
    std::fs::write(&source_path, source)
        .map_err(|err| compile_failed(format!("failed to write native_decide source: {err}")))?;
    compiler
        .compile(&source_path, &binary_path)
        .map_err(|err| compile_failed(err.to_string()))?;
    std::fs::read(&binary_path).map_err(|err| {
        compile_failed(format!(
            "failed to read compiled native_decide binary: {err}"
        ))
    })
}

fn native_binary_name() -> &'static str {
    #[cfg(windows)]
    {
        "native_decide.exe"
    }
    #[cfg(not(windows))]
    {
        "native_decide"
    }
}

fn make_executable(path: &std::path::Path) -> Result<(), NativeDecideExecError> {
    let _ = path;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut perms = std::fs::metadata(path)
            .map_err(|err| NativeDecideExecError::ExecutionFailed {
                detail: format!("failed to inspect native_decide binary permissions: {err}"),
            })?
            .permissions();
        perms.set_mode(0o755);
        std::fs::set_permissions(path, perms).map_err(|err| {
            NativeDecideExecError::ExecutionFailed {
                detail: format!("failed to set native_decide binary executable bit: {err}"),
            }
        })?;
    }
    Ok(())
}

fn strip_metadata(mut expr: &Expr) -> &Expr {
    while let ExprKind::MData(_, inner) = expr.kind() {
        expr = inner;
    }
    expr
}

fn mk_decidable_bool_expr(target: &Expr, decidable_expr: &Expr) -> Expr {
    let decidable_target = Expr::app(
        Expr::const_(Name::from_string("Decidable"), vec![]),
        target.clone(),
    );
    let motive = Expr::lam(
        BinderInfo::Default,
        decidable_target,
        Expr::const_(Name::from_string("Bool"), vec![]),
    );
    let false_case = Expr::lam(
        BinderInfo::Default,
        Expr::pi(
            BinderInfo::Default,
            target.clone(),
            Expr::const_(Name::from_string("False"), vec![]),
        ),
        Expr::const_(Name::from_string("Bool.false"), vec![]),
    );
    let true_case = Expr::lam(
        BinderInfo::Default,
        target.clone(),
        Expr::const_(Name::from_string("Bool.true"), vec![]),
    );
    // Lean-faithful casesOn order: motive, major (the Decidable instance),
    // then minors.
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Decidable.casesOn"),
                            vec![Level::succ(Level::zero())],
                        ),
                        target.clone(),
                    ),
                    motive,
                ),
                decidable_expr.clone(),
            ),
            false_case,
        ),
        true_case,
    )
}

fn reduce_bool_result(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
) -> Result<bool, NativeDecideExecError> {
    let reduced = state.whnf(goal, expr);
    let ExprKind::Const(name, _) = reduced.get_app_fn().kind() else {
        return Err(NativeDecideExecError::ExecutionFailed {
            detail: format!(
                "native_decide Bool reduction did not reach a constructor: {reduced:?}"
            ),
        });
    };
    match builtin_label(name).unwrap_or("") {
        "Bool.true" => Ok(true),
        "Bool.false" => Ok(false),
        _ => Err(NativeDecideExecError::ExecutionFailed {
            detail: format!("native_decide Bool reduction is stuck: {reduced:?}"),
        }),
    }
}

fn classify_decidable_result(
    result: &Expr,
) -> Result<NativeDecideExecOutcome, NativeDecideExecError> {
    let ExprKind::Const(name, _) = result.get_app_fn().kind() else {
        return Err(NativeDecideExecError::ExecutionFailed {
            detail: format!("native_decide result is not a Decidable constructor: {result:?}"),
        });
    };
    match builtin_label(name).unwrap_or("") {
        "Decidable.isTrue" => {
            let args = result.get_app_args();
            let proof = args
                .last()
                .ok_or_else(|| NativeDecideExecError::ExecutionFailed {
                    detail: format!(
                        "Decidable.isTrue returned without a proof payload: {result:?}"
                    ),
                })?;
            Ok(NativeDecideExecOutcome::Proved((*proof).clone()))
        }
        "Decidable.isFalse" => Ok(NativeDecideExecOutcome::Refuted),
        _ => Err(NativeDecideExecError::ExecutionFailed {
            detail: format!("native_decide result did not reduce to isTrue/isFalse: {result:?}"),
        }),
    }
}

#[cfg(test)]
mod typed_builtin_tests {
    use super::*;

    #[test]
    fn native_values_and_operators_refuse_quoted_display_twins() {
        assert!(lower_bool_expr(&Expr::const_(Name::from_string("Bool.true"), vec![])).is_ok());
        assert!(lower_bool_expr(&Expr::const_(Name::anon().str("Bool.true"), vec![])).is_err());
        assert!(lower_nat_expr(&Expr::const_(Name::from_string("Nat.zero"), vec![])).is_ok());
        assert!(lower_nat_expr(&Expr::const_(Name::anon().str("Nat.zero"), vec![])).is_err());
        for label in ["Nat.add", "Nat.mul", "Nat.sub", "Nat.pow"] {
            let apply = |name| {
                Expr::apps(
                    Expr::const_(name, vec![]),
                    [Expr::nat_lit(2), Expr::nat_lit(1)],
                )
            };
            assert!(lower_nat_expr(&apply(Name::from_string(label))).is_ok());
            assert!(lower_nat_expr(&apply(Name::anon().str(label))).is_err());
        }
        for label in ["Int.ofNat", "Int.negSucc"] {
            let apply = |name| Expr::app(Expr::const_(name, vec![]), Expr::nat_lit(1));
            assert!(lower_int_expr(&apply(Name::from_string(label))).is_ok());
            assert!(lower_int_expr(&apply(Name::anon().str(label))).is_err());
        }
        for name in [Name::anon().str("1"), Name::anon().num(1)] {
            assert_eq!(builtin_label(&name), None);
            assert!(lower_nat_expr(&Expr::const_(name, vec![])).is_err());
        }
        assert!(lower_nat_expr(&Expr::nat_lit(1)).is_ok());
        assert!(lower_nat_expr(&Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        ))
        .is_ok());
    }

    #[test]
    fn decidable_classification_requires_exact_constructor_identity() {
        let proof = Expr::const_(Name::from_string("True.intro"), vec![]);
        let positive = |name| {
            Expr::apps(
                Expr::const_(name, vec![]),
                [
                    Expr::const_(Name::from_string("True"), vec![]),
                    proof.clone(),
                ],
            )
        };
        assert!(
            matches!(classify_decidable_result(&positive(Name::from_string("Decidable.isTrue"))), Ok(NativeDecideExecOutcome::Proved(p)) if p == proof)
        );
        assert!(
            classify_decidable_result(&positive(Name::anon().str("Decidable.isTrue"))).is_err()
        );
        let false_prop = Expr::const_(Name::from_string("False"), vec![]);
        let negative = |name| {
            Expr::apps(
                Expr::const_(name, vec![]),
                [
                    false_prop.clone(),
                    Expr::lam(BinderInfo::Default, false_prop.clone(), Expr::bvar(0)),
                ],
            )
        };
        assert!(matches!(
            classify_decidable_result(&negative(Name::from_string("Decidable.isFalse"))),
            Ok(NativeDecideExecOutcome::Refuted)
        ));
        assert!(
            classify_decidable_result(&negative(Name::anon().str("Decidable.isFalse"))).is_err()
        );
    }
}
