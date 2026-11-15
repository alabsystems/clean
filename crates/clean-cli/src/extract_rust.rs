// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean extract --backend rust` — readable, SAFE Rust emission for the same
//! v1 class the C backend already accepts
//! (`designs/2026-08-06-clean-extract-width1.md`, rung §C of the Rocq-features
//! program).
//!
//! # What this emitter is
//!
//! The C backend goes through the whole `clean compile --emit c` pipeline and
//! links against `clean-runtime`: every value is a `clean_obj*`, arithmetic is
//! shim dispatch, memory is Perceus reference counting. That is the right shape
//! for a runtime, and the wrong shape for the thing a Rocq user means by
//! "extract to a host language" — a module a human can read and drop into an
//! ordinary project.
//!
//! So this backend does not reuse [`crate::cmd_compile`]'s emitter. It
//! translates the KERNEL value of the declaration directly into plain Rust:
//!
//! * no `unsafe`, no runtime, no allocation — the emitted file is standalone;
//! * plain `u8`/`u16`/`u32`/`u64`/`bool` signatures, not boxed objects;
//! * Lean's `UIntW` arithmetic is modular, so it is spelled `wrapping_add` /
//!   `wrapping_sub` / `wrapping_mul` EXPLICITLY rather than left to Rust's
//!   overflow behaviour (which differs between debug and release);
//! * Lean's `Nat` is unbounded and is modelled as `u64`, so `Nat.add`/`Nat.mul`
//!   are spelled `checked_*` + `.expect(...)` — the model's range limit aborts
//!   loudly instead of silently wrapping. `Nat.sub` is truncated subtraction in
//!   Lean, which is exactly `saturating_sub`.
//!
//! # Fail-closed
//!
//! Every construct outside the table below REFUSES with a stable `E_RUST_*`
//! code. There is no "best effort" arm: an unrecognised constant is an error,
//! never a guess.
//!
//! # Honesty
//!
//! Emission is checked DIFFERENTIALLY: the caller compiles the emitted program
//! together with a synthesized battery driver, runs it, and compares every point
//! against kernel-side evaluation of the same application
//! ([`crate::cmd_extract`]). That is a check over a finite battery, not a proof
//! of translation correctness, and the manifest says so.

use std::process::Command;

use clean_elab::oracle_compiler::OracleCompiler;
use clean_kernel::{Environment, Expr, ExprKind, Literal, Name};

use crate::cmd_extract::{GateSig, ScalarTy};

mod extract_rust_control;
use extract_rust_control::{
    translate_beta_redex, translate_ite, translate_nat_cases, translate_nat_rec,
};

/// Stable refusal codes for the Rust backend. A refusal writes no artifacts.
#[derive(Debug, thiserror::Error)]
pub(crate) enum RustEmitError {
    #[error("E_RUST_NO_VALUE: {0} has no computational value to emit")]
    NoValue(Name),
    #[error(
        "E_RUST_BINDERS: {0} binds {1} lambda(s) but its type telescope has {2} parameter(s); \
         the v1 Rust backend needs a fully eta-expanded body"
    )]
    Binders(Name, usize, usize),
    #[error("E_RUST_NAME: `{0}` does not spell a Rust identifier")]
    BadName(String),
    #[error("E_RUST_UNSUPPORTED: {0}")]
    Unsupported(String),
    #[error("E_RUST_TOOLCHAIN: {0}")]
    Toolchain(String),
}

/// Rust spelling of a v1 scalar type.
pub(crate) fn rust_ty(t: ScalarTy) -> &'static str {
    match t {
        // Lean `Nat` is unbounded; `u64` is a MODEL of it, and the emitted
        // arithmetic aborts rather than wrapping when the model overflows.
        ScalarTy::Nat | ScalarTy::UInt64 => "u64",
        ScalarTy::Bool => "bool",
        ScalarTy::UInt8 => "u8",
        ScalarTy::UInt16 => "u16",
        ScalarTy::UInt32 => "u32",
    }
}

/// Rust spelling of a battery input value at type `t`.
pub(crate) fn rust_literal(t: ScalarTy, v: u64) -> String {
    match t {
        ScalarTy::Bool => (if v == 0 { "false" } else { "true" }).to_string(),
        _ => format!("{v}{}", rust_ty(t)),
    }
}

/// A rendered Rust expression plus whether it can be a method receiver without
/// parentheses (identifiers, suffixed literals and method calls can; `!x` and
/// `x && y` cannot).
#[derive(Debug)]
struct Rendered {
    text: String,
    postfix_safe: bool,
}

impl Rendered {
    fn atom(text: String) -> Self {
        Self {
            text,
            postfix_safe: true,
        }
    }

    /// Wrap in parentheses unless this is already a valid method receiver.
    fn as_receiver(&self) -> String {
        if self.postfix_safe {
            self.text.clone()
        } else {
            format!("({})", self.text)
        }
    }
}

/// Binary integer operators, keyed by the Lean constant's suffix.
///
/// `Nat` and `UIntW` deliberately differ: `UIntW` is modular in Lean, `Nat` is
/// not, so the emitted spelling is `wrapping_*` for the former and `checked_*`
/// for the latter. Getting that backwards is a silent miscompile at 2^w, which
/// The message every `Nat`-model overflow carries.
///
/// One constant so the `checked_*` sites cannot drift apart: `Nat` is unbounded
/// in Lean and `u64` is not, so this string is where that gap is disclosed to
/// whoever runs the extracted code.
const NAT_OVERFLOW_MSG: &str =
    "Nat overflow: clean extract models Lean Nat as u64 (see manifest.json)";

/// is exactly why the battery carries the wraparound points.
fn int_binop(head: &str, expected: ScalarTy) -> Option<(&'static str, Option<&'static str>)> {
    let (ty_name, op) = head.rsplit_once('.')?;
    let ty = match ty_name {
        "Nat" => ScalarTy::Nat,
        "UInt8" => ScalarTy::UInt8,
        "UInt16" => ScalarTy::UInt16,
        "UInt32" => ScalarTy::UInt32,
        "UInt64" => ScalarTy::UInt64,
        _ => return None,
    };
    if ty != expected {
        return None;
    }
    match (ty, op) {
        (ScalarTy::Nat, "add") => Some(("checked_add", Some(NAT_OVERFLOW_MSG))),
        (ScalarTy::Nat, "mul") => Some(("checked_mul", Some(NAT_OVERFLOW_MSG))),
        // Lean's `Nat.sub` is TRUNCATED subtraction: `3 - 5 = 0`.
        (ScalarTy::Nat, "sub") => Some(("saturating_sub", None)),
        (_, "add") => Some(("wrapping_add", None)),
        (_, "sub") => Some(("wrapping_sub", None)),
        (_, "mul") => Some(("wrapping_mul", None)),
        _ => None,
    }
}

fn strip_mdata(mut e: &Expr) -> &Expr {
    while let ExprKind::MData(_, inner) = e.kind() {
        e = inner;
    }
    e
}

/// Flatten `f a b c` into `(f, [a, b, c])`.
fn flatten_app(e: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args: Vec<&Expr> = Vec::new();
    let mut head = strip_mdata(e);
    while let ExprKind::App(f, a) = head.kind() {
        args.push(strip_mdata(a));
        head = strip_mdata(f);
    }
    args.reverse();
    (head, args)
}

/// Parameter spelling: `a`, `b`, … for the readable arities, `x{i}` past `z`.
fn param_name(i: usize) -> String {
    match u8::try_from(i) {
        Ok(k) if usize::from(k) < 26 => char::from(b'a' + k).to_string(),
        _ => format!("x{i}"),
    }
}

/// Translate a kernel expression of type `expected` into Rust.
///
/// `params` is outer-binder-first; de Bruijn index `i` therefore names
/// `params[params.len() - 1 - i]`.
fn translate(
    e: &Expr,
    expected: ScalarTy,
    params: &[(String, ScalarTy)],
) -> Result<Rendered, RustEmitError> {
    let e = strip_mdata(e);
    match e.kind() {
        ExprKind::BVar(i) => {
            let idx = usize::try_from(*i).ok().and_then(|i| {
                params
                    .len()
                    .checked_sub(1)
                    .and_then(|last| last.checked_sub(i))
            });
            let Some((name, ty)) = idx.and_then(|i| params.get(i)) else {
                return Err(RustEmitError::Unsupported(format!(
                    "loose de Bruijn index {i} in the body"
                )));
            };
            if *ty != expected {
                return Err(RustEmitError::Unsupported(format!(
                    "parameter `{name}` has type {} where {} is expected; the v1 Rust \
                     backend emits type-homogeneous bodies",
                    rust_ty(*ty),
                    rust_ty(expected)
                )));
            }
            Ok(Rendered::atom(name.clone()))
        }
        ExprKind::Lit(Literal::Nat(n)) => {
            let Some(v) = n.to_u64() else {
                return Err(RustEmitError::Unsupported(
                    "numeric literal exceeds the u64 model".to_string(),
                ));
            };
            if expected == ScalarTy::Bool {
                return Err(RustEmitError::Unsupported(
                    "numeric literal where a Bool is expected".to_string(),
                ));
            }
            Ok(Rendered::atom(rust_literal(expected, v)))
        }
        ExprKind::Const(_, _) | ExprKind::App(_, _) => translate_app(e, expected, params),
        other => Err(RustEmitError::Unsupported(format!(
            "expression form {} is outside the v1 straight-line fragment",
            form_name(other)
        ))),
    }
}

/// A short label for the refusal message. Deliberately a name, not a `Debug`
/// dump: a refusal should tell the reader WHICH construct fell outside the
/// fragment without pasting the whole term. Non-core forms (`SProp`, the
/// cubical family, …) share the catch-all — they are all equally out of scope.
fn form_name(kind: &ExprKind) -> &'static str {
    match kind {
        ExprKind::BVar(_) => "bvar",
        ExprKind::FVar(_) => "fvar",
        ExprKind::Sort(_) => "sort",
        ExprKind::Const(_, _) => "const",
        ExprKind::App(_, _) => "app",
        ExprKind::Lam(_, _, _) => "lambda",
        ExprKind::Pi(_, _, _) => "pi",
        ExprKind::Let(_, _, _, _, _) => "let",
        ExprKind::Lit(_) => "literal",
        ExprKind::MData(_, _) => "mdata",
        ExprKind::Proj(_, _, _) => "projection",
        _ => "non-core expression",
    }
}

fn translate_app(
    e: &Expr,
    expected: ScalarTy,
    params: &[(String, ScalarTy)],
) -> Result<Rendered, RustEmitError> {
    let (head, args) = flatten_app(e);
    // A lambda head is a beta-redex — match elaboration's shared-default-arm
    // shape — and gets its own translation rather than a refusal.
    if matches!(head.kind(), ExprKind::Lam(_, _, _)) {
        return translate_beta_redex(head, &args, expected, params);
    }
    let ExprKind::Const(name, levels) = head.kind() else {
        return Err(RustEmitError::Unsupported(format!(
            "application head is a {}, not a constant",
            form_name(head.kind())
        )));
    };
    let head_name = name.to_string();

    // CONTROL FLOW. `ite` is the one v1 constant allowed to carry a universe
    // level: it is `{α : Sort u} → (c : Prop) → [Decidable c] → α → α → α`, and
    // the level is instantiated at the scalar result type, so the emitted code
    // is still monomorphic. Everything else stays level-free.
    if head_name == "ite" {
        return translate_ite(&args, expected, params);
    }
    if head_name == "Nat.casesOn" {
        return translate_nat_cases(&args, expected, params);
    }
    if head_name == "Nat.rec" {
        return translate_nat_rec(&args, expected, params);
    }
    // `OfNat.ofNat α n inst` IS the numeral `n`. Lean wraps every literal in it
    // once a type is known, so a `0` written in source arrives here rather than
    // as a bare `Lit`. It carries a universe level like the other two.
    if head_name == "OfNat.ofNat" {
        let [_alpha, lit, _inst] = args.as_slice() else {
            return Err(RustEmitError::Unsupported(format!(
                "`OfNat.ofNat` applied to {} argument(s); expected 3",
                args.len()
            )));
        };
        return translate(lit, expected, params);
    }
    // `BEq.beq α inst x y` → `(x == y)` — for the CANONICAL instances only.
    //
    // Like `ite`/`OfNat.ofNat` it carries a universe level instantiated at the
    // scalar element type, so emission stays monomorphic. The operands are
    // translated at the ELEMENT type read off `α`, not at `expected` (which is
    // `Bool`).
    //
    // FAIL-CLOSED ON THE INSTANCE, and this is the load-bearing part: a user's
    // own `BEq` instance can implement ANY relation, and emitting Rust `==` for
    // it would be a silently wrong program — the exact class of defect the
    // differential battery only catches if a battery point happens to land on a
    // disagreement. So only the prelude's structural instances are accepted,
    // each faithful to Rust `==` on its model type (`Nat` as `u64` — values in
    // play are within the model, since overflow aborts earlier; `UIntW` wraps on
    // both sides; `Bool` is `Bool`). Anything else refuses, NAMING the instance
    // it saw.
    if head_name == "BEq.beq" {
        if expected != ScalarTy::Bool {
            return Err(RustEmitError::Unsupported(format!(
                "`BEq.beq` produces a Bool, but a {} is expected here",
                rust_ty(expected)
            )));
        }
        let [alpha, inst, lhs, rhs] = args.as_slice() else {
            return Err(RustEmitError::Unsupported(format!(
                "`BEq.beq` applied to {} argument(s); expected 4 (α, inst, x, y)",
                args.len()
            )));
        };
        let Some(elem_ty) = ScalarTy::of(strip_mdata(alpha)) else {
            return Err(RustEmitError::Unsupported(format!(
                "`BEq.beq` at element type {} — outside the v1 scalar class",
                form_name(strip_mdata(alpha).kind())
            )));
        };
        // Two canonical shapes, MEASURED from the elaborator's output:
        //   1. a direct structural instance (`instBEqNat`, `instBEqUInt32`, …)
        //   2. `instBEqOfDecidableEq α instDecidableEq<T>` — the decide-wrapper,
        //      whose `beq a b` is literally `decide (a = b)`: structural
        //      equality, PROVIDED the inner `DecidableEq` instance is itself the
        //      canonical one. This is what `a == b` on `Nat` actually elaborates
        //      to here (dumped: `instBEqOfDecidableEq Nat instDecidableEqNat`).
        // Anything else — including the wrapper over a NON-canonical
        // DecidableEq — refuses, naming what it saw.
        let direct_ok = |n: &str| {
            matches!(
                (elem_ty, n),
                (ScalarTy::Nat, "instBEqNat")
                    | (ScalarTy::Bool, "instBEqBool")
                    | (ScalarTy::UInt8, "instBEqUInt8")
                    | (ScalarTy::UInt16, "instBEqUInt16")
                    | (ScalarTy::UInt32, "instBEqUInt32")
                    | (ScalarTy::UInt64, "instBEqUInt64")
            )
        };
        let dec_ok = |n: &str| {
            matches!(
                (elem_ty, n),
                (ScalarTy::Nat, "instDecidableEqNat")
                    | (ScalarTy::Bool, "instDecidableEqBool")
                    | (ScalarTy::UInt8, "instDecidableEqUInt8")
                    | (ScalarTy::UInt16, "instDecidableEqUInt16")
                    | (ScalarTy::UInt32, "instDecidableEqUInt32")
                    | (ScalarTy::UInt64, "instDecidableEqUInt64")
            )
        };
        let inst_stripped = strip_mdata(inst);
        let canonical = match inst_stripped.kind() {
            ExprKind::Const(n, _) => direct_ok(&n.to_string()),
            ExprKind::App(_, _) => {
                let (ih, iargs) = flatten_app(inst_stripped);
                match (ih.kind(), iargs.as_slice()) {
                    (ExprKind::Const(wn, _), [_ty, inner])
                        if wn.to_string() == "instBEqOfDecidableEq" =>
                    {
                        matches!(
                            strip_mdata(inner).kind(),
                            ExprKind::Const(dn, _) if dec_ok(&dn.to_string())
                        )
                    }
                    _ => false,
                }
            }
            _ => false,
        };
        if !canonical {
            return Err(RustEmitError::Unsupported(format!(
                "`BEq.beq` through instance `{inst_stripped:?}` at {} — only the \
                 canonical structural instance (direct, or the decide-wrapper \
                 over the canonical DecidableEq) is emitted as `==`; a custom \
                 `BEq` can implement any relation, and `==` for it would be a \
                 silently wrong program",
                rust_ty(elem_ty)
            )));
        }
        let l = translate(lhs, elem_ty, params)?;
        let r = translate(rhs, elem_ty, params)?;
        return Ok(Rendered::atom(format!("({} == {})", l.text, r.text)));
    }

    if !levels.is_empty() {
        return Err(RustEmitError::Unsupported(format!(
            "`{name}` is applied at explicit universe levels; v1 is monomorphic"
        )));
    }

    // Nullary constants.
    if args.is_empty() {
        return match (head_name.as_str(), expected) {
            // Both spellings: the elaborator emits the SHORT `true`/`false` in
            // some positions (measured inside a `Nat.casesOn` branch) and the
            // qualified constructor in others.
            ("Bool.true" | "true", ScalarTy::Bool) => Ok(Rendered::atom("true".to_string())),
            ("Bool.false" | "false", ScalarTy::Bool) => Ok(Rendered::atom("false".to_string())),
            ("Nat.zero", ScalarTy::Nat) => Ok(Rendered::atom(rust_literal(ScalarTy::Nat, 0))),
            _ => Err(RustEmitError::Unsupported(format!(
                "constant `{head_name}` is not in the v1 Rust emission table"
            ))),
        };
    }

    // `Nat.succ n` is `n + 1` — and it is a MODEL boundary like every other Nat
    // addition here, so it goes through the checked form. `Nat` is unbounded in
    // Lean; the u64 model is not, and the successor of `u64::MAX` is exactly
    // where that gap shows.
    if head_name == "Nat.succ" && expected == ScalarTy::Nat {
        let [n] = args.as_slice() else {
            return Err(RustEmitError::Unsupported(format!(
                "`Nat.succ` applied to {} argument(s); expected 1",
                args.len()
            )));
        };
        let n = translate(n, ScalarTy::Nat, params)?;
        return Ok(Rendered::atom(format!(
            "{}.checked_add(1u64).expect(\"{NAT_OVERFLOW_MSG}\")",
            n.as_receiver()
        )));
    }

    // TOTAL division and remainder.
    //
    // Lean's `Nat.div`/`Nat.mod` are TOTAL: `n / 0 = 0` and `n % 0 = n`. Rust's
    // `/` and `%` PANIC on a zero divisor. Emitting them bare would therefore be
    // wrong in the one case the kernel defines most explicitly — so the guard is
    // part of the semantics, not defensive programming.
    //
    // The battery makes this a live check rather than a claim: for a two-Nat
    // signature it contains the crossed point `(63, 0)`, so a bare `/` does not
    // silently disagree — it CRASHES the battery binary, and the harness fails
    // the extraction. See `test_battery_divides_by_zero`.
    //
    // The divisor is bound once: it can be an arbitrary expression, and the
    // guard reads it twice.
    if let Some((op, zero_result)) = match (head_name.as_str(), expected) {
        ("Nat.div", ScalarTy::Nat) => Some(("/", None)),
        ("Nat.mod", ScalarTy::Nat) => Some(("%", Some(()))),
        _ => None,
    } {
        let [num, den] = args.as_slice() else {
            return Err(RustEmitError::Unsupported(format!(
                "`{head_name}` applied to {} argument(s); expected 2",
                args.len()
            )));
        };
        let n = translate(num, expected, params)?;
        let d = translate(den, expected, params)?;
        let depth = params.len();
        let nn = format!("__d{depth}n");
        let dd = format!("__d{depth}d");
        // `n % 0 = n` keeps the numerator; `n / 0 = 0`.
        let zero_case = if zero_result.is_some() {
            nn.clone()
        } else {
            rust_literal(expected, 0)
        };
        return Ok(Rendered::atom(format!(
            "{{ let {nn} = {}; let {dd} = {}; if {dd} == 0 {{ {zero_case} }} else \
             {{ {nn} {op} {dd} }} }}",
            n.text, d.text
        )));
    }

    // Homogeneous integer binary operators.
    if let Some((method, overflow_msg)) = int_binop(&head_name, expected) {
        let [lhs, rhs] = args.as_slice() else {
            return Err(RustEmitError::Unsupported(format!(
                "`{head_name}` applied to {} argument(s); expected 2",
                args.len()
            )));
        };
        let lhs = translate(lhs, expected, params)?;
        let rhs = translate(rhs, expected, params)?;
        let mut text = format!("{}.{method}({})", lhs.as_receiver(), rhs.text);
        if let Some(msg) = overflow_msg {
            text.push_str(&format!(".expect(\"{msg}\")"));
        }
        return Ok(Rendered::atom(text));
    }

    // Boolean operators.
    match (head_name.as_str(), expected) {
        ("Bool.not", ScalarTy::Bool) => {
            let [x] = args.as_slice() else {
                return Err(RustEmitError::Unsupported(format!(
                    "`Bool.not` applied to {} argument(s); expected 1",
                    args.len()
                )));
            };
            let x = translate(x, ScalarTy::Bool, params)?;
            Ok(Rendered {
                text: format!("!{}", x.as_receiver()),
                postfix_safe: false,
            })
        }
        (op @ ("Bool.and" | "Bool.or"), ScalarTy::Bool) => {
            let [lhs, rhs] = args.as_slice() else {
                return Err(RustEmitError::Unsupported(format!(
                    "`{op}` applied to {} argument(s); expected 2",
                    args.len()
                )));
            };
            let lhs = translate(lhs, ScalarTy::Bool, params)?;
            let rhs = translate(rhs, ScalarTy::Bool, params)?;
            // `&&`/`||` short-circuit where Lean's `Bool.and`/`Bool.or` are
            // strict; on pure `Bool` values (no effects, no divergence in this
            // fragment) the two agree pointwise.
            let sym = if op == "Bool.and" { "&&" } else { "||" };
            Ok(Rendered {
                text: format!("{} {sym} {}", lhs.as_receiver(), rhs.as_receiver()),
                postfix_safe: false,
            })
        }
        _ => Err(RustEmitError::Unsupported(format!(
            "constant `{head_name}` is not in the v1 Rust emission table \
             (at result type {})",
            rust_ty(expected)
        ))),
    }
}

/// Rust function name for a Lean declaration name: dots become underscores and
/// anything that is not an identifier character REFUSES.
pub(crate) fn rust_fn_name(decl: &str) -> Result<String, RustEmitError> {
    let candidate: String = decl
        .chars()
        .map(|c| if c == '.' { '_' } else { c })
        .collect();
    let ok = !candidate.is_empty()
        && candidate
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !candidate.starts_with(|c: char| c.is_ascii_digit());
    if ok {
        Ok(candidate)
    } else {
        Err(RustEmitError::BadName(decl.to_string()))
    }
}

/// Emit the shipped Rust module for `name`.
pub(crate) fn emit_rust_module(
    env: &Environment,
    name: &Name,
    sig: &GateSig,
) -> Result<String, RustEmitError> {
    let info = env
        .get_const(name)
        .ok_or_else(|| RustEmitError::NoValue(name.clone()))?;
    let value = info
        .value
        .as_ref()
        .ok_or_else(|| RustEmitError::NoValue(name.clone()))?;

    let fn_name = rust_fn_name(&name.to_string())?;

    // Peel exactly as many lambdas as the telescope has parameters.
    let mut params: Vec<(String, ScalarTy)> = Vec::new();
    let mut cursor = strip_mdata(value);
    while params.len() < sig.params.len() {
        let ExprKind::Lam(_, _, body) = cursor.kind() else {
            return Err(RustEmitError::Binders(
                name.clone(),
                params.len(),
                sig.params.len(),
            ));
        };
        params.push((param_name(params.len()), sig.params[params.len()]));
        cursor = strip_mdata(body);
    }
    if matches!(cursor.kind(), ExprKind::Lam(_, _, _)) {
        return Err(RustEmitError::Binders(
            name.clone(),
            sig.params.len() + 1,
            sig.params.len(),
        ));
    }

    let body = translate(cursor, sig.ret, &params)?;
    let signature: Vec<String> = params
        .iter()
        .map(|(n, t)| format!("{n}: {}", rust_ty(*t)))
        .collect();

    let models_nat = sig.ret == ScalarTy::Nat || sig.params.contains(&ScalarTy::Nat);
    let nat_note = if models_nat {
        "//   * Lean `Nat` is UNBOUNDED; this module models it as `u64`, so `Nat.add`/\n\
         //     `Nat.mul` are `checked_*` + `.expect(..)` — the model's range limit\n\
         //     aborts loudly instead of silently wrapping. `Nat.sub` is Lean's\n\
         //     truncated subtraction, i.e. `saturating_sub`.\n"
    } else {
        ""
    };

    Ok(format!(
        "// Generated by `clean extract --backend rust` from the Lean 4 declaration\n\
         // `{decl}`. Do not edit: regenerate instead.\n\
         //\n\
         // This module is SELF-CONTAINED and SAFE: no `unsafe`, no runtime, no\n\
         // allocation, plain scalar signatures.\n\
         //\n\
         // Semantics of the spelling:\n\
         //   * Lean `UInt8/16/32/64` arithmetic is MODULAR, so it is spelled\n\
         //     `wrapping_*` explicitly rather than left to Rust's overflow\n\
         //     behaviour (which differs between debug and release builds).\n\
         {nat_note}//\n\
         // Correspondence to the source declaration was checked DIFFERENTIALLY\n\
         // over a battery of inputs at extraction time (see manifest.json). That\n\
         // is a check, not a proof of translation correctness.\n\
         #![allow(non_snake_case)] // the function name mirrors the Lean declaration\n\
         \n\
         pub fn {fn_name}({args}) -> {ret} {{\n\
         \x20   {body}\n\
         }}\n",
        decl = name,
        args = signature.join(", "),
        ret = rust_ty(sig.ret),
        body = body.text,
    ))
}

/// Synthesized `main()`: calls the emitted function once per battery tuple and
/// prints each result as a decimal, matching the kernel leg's readback.
pub(crate) fn render_rust_battery_driver(
    fn_name: &str,
    sig: &GateSig,
    battery: &[Vec<u64>],
) -> String {
    let mut m = String::from(
        "\n// --- differential battery driver (appended at extraction time; not\n\
         // part of the shipped artifact) ---\n\
         fn main() {\n",
    );
    for tuple in battery {
        let call_args: Vec<String> = tuple
            .iter()
            .zip(&sig.params)
            .map(|(v, t)| rust_literal(*t, *v))
            .collect();
        let call = format!("{fn_name}({})", call_args.join(", "));
        if sig.ret == ScalarTy::Bool {
            m.push_str(&format!(
                "    println!(\"{{}}\", if {call} {{ 1u64 }} else {{ 0u64 }});\n"
            ));
        } else {
            m.push_str(&format!("    println!(\"{{}}\", u64::from({call}));\n"));
        }
    }
    m.push_str("}\n");
    m
}

/// Compile `source` (module + appended driver) with the admitted Trust oracle
/// compiler -- the same one, and the same rule, as `native_decide`'s
/// (`clean_elab::oracle_compiler`): one compile, no retry, no other compiler.
fn compile_rust_program(
    compiler: &OracleCompiler,
    source: &str,
    dir: &std::path::Path,
) -> Result<std::path::PathBuf, RustEmitError> {
    let source_path = dir.join("extracted.rs");
    let binary_path = dir.join(if cfg!(windows) {
        "extracted.exe"
    } else {
        "extracted"
    });
    std::fs::write(&source_path, source)
        .map_err(|e| RustEmitError::Toolchain(format!("failed to write emitted Rust: {e}")))?;
    compiler
        .compile(&source_path, &binary_path)
        .map_err(|e| RustEmitError::Toolchain(e.to_string()))?;
    Ok(binary_path)
}

/// Compile `module + driver` and run it, returning one trimmed stdout line per
/// battery point.
///
/// `module` is a parameter rather than a re-derivation so a test can hand this
/// a TAMPERED module and watch the differential reject it — the emitter's own
/// falsifiability probe (see
/// `test_rust_backend_differential_rejects_a_tampered_emission`).
pub(crate) fn run_rust_battery(
    compiler: &OracleCompiler,
    module: &str,
    driver: &str,
    dir: &std::path::Path,
) -> Result<Vec<String>, RustEmitError> {
    let program = format!("{module}{driver}");
    let exe = compile_rust_program(compiler, &program, dir)?;
    let out = Command::new(&exe)
        .output()
        .map_err(|e| RustEmitError::Toolchain(format!("failed to run battery binary: {e}")))?;
    if !out.status.success() {
        return Err(RustEmitError::Toolchain(format!(
            "battery binary exited with {}: {}",
            out.status,
            String::from_utf8_lossy(&out.stderr).trim()
        )));
    }
    Ok(String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(|l| l.trim().to_string())
        .filter(|l| !l.is_empty())
        .collect())
}

#[cfg(test)]
#[path = "extract_rust_tests.rs"]
mod tests;
