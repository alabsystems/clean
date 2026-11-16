// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Opt-in, env-gated** kernel-reject diagnostics for the closure-replay
//! driver. When (and only when) the `ISA_DUMP_REJECTS` environment variable
//! names a file, [`verify_one`](super::batch::verify_one) appends one
//! `reason\tname\tsignature` line per kernel-rejected theorem, where the
//! signature is a normalized cluster key: the kernel [`EnvError`] kind, the
//! expected-vs-got type *heads* for a `TypeCheckFailed`/`TypeMismatch`, and the
//! failing theorem's top-level proof-node kind.
//!
//! This path is **inert** when the var is unset — it is reached only on the
//! (rejection) cold path and does nothing without the file, so the default
//! verification counts and cost are bit-identical to the un-instrumented driver.
//! It touches no soundness logic: nothing here can cause a theorem to be stamped
//! `KernelVerified`; it only *describes* an already-decided rejection.

use std::io::Write as _;

use clean_kernel::env::EnvError;
use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::tc::TypeError;

use super::super::isabelle_pure::IsaProof;

/// Whether the opt-in kernel-reject dump is enabled, and to which file. Read
/// once per rejected theorem (cold path); `None` (the default) means no dump.
pub(super) fn dump_target() -> Option<String> {
    std::env::var("ISA_DUMP_REJECTS")
        .ok()
        .filter(|s| !s.is_empty())
}

/// The top-level proof-node kind of a theorem's proof, as a short stable tag.
/// This is the outermost constructor of the Isabelle proof term — a cheap,
/// high-signal cluster axis (e.g. `AppP` vs `Thm` vs `Axm`), since the reject
/// shape is largely determined by which reconstruction arm ran last.
pub(super) fn proof_node_kind(p: &IsaProof) -> &'static str {
    match p {
        IsaProof::Thm { .. } => "Thm",
        IsaProof::Axm { .. } => "Axm",
        IsaProof::AbsP { .. } => "AbsP",
        IsaProof::Abst { .. } => "Abst",
        IsaProof::AppP { .. } => "AppP",
        IsaProof::AppT { .. } => "AppT",
        IsaProof::Hyp { .. } => "Hyp",
        IsaProof::Bound { .. } => "Bound",
        IsaProof::OfClass { .. } => "OfClass",
        IsaProof::Min => "Min",
        IsaProof::Oracle { .. } => "Oracle",
        IsaProof::Nop => "Nop",
        IsaProof::Other => "Other",
    }
}

/// The **innermost axiom/thm head name** driving the last reconstruction arm:
/// walk the proof spine (through `AppP`/`AppT`, and past a single leading
/// `AbsP`/`Abst` binder chain) to the leaf `Axm`/`Thm`. This is the single most
/// discriminating cluster axis — it names *which bootstrap arm* built the
/// rejected term (`Pure.combination`, `Pure.equal_elim`, …). Falls back to the
/// node kind for non-leaf-headed shapes.
pub(super) fn spine_head(p: &IsaProof) -> String {
    fn go(p: &IsaProof) -> String {
        match p {
            IsaProof::Axm { name, .. } => format!("axm:{name}"),
            IsaProof::Thm { .. } => "thm".to_string(),
            IsaProof::AppP { f, .. } | IsaProof::AppT { f, .. } => go(f),
            IsaProof::AbsP { b, .. } | IsaProof::Abst { b, .. } => go(b),
            other => proof_node_kind(other).to_string(),
        }
    }
    go(p)
}

/// One-token summary of the head of an expression's application spine — mirrors
/// the kernel's private `head_summary` so the cluster key is stable and compact
/// (a full `{:?}` type dump can run to kilobytes; the head — `HOL.eq`, `Pi`,
/// `Sort`, … — is enough to orient).
fn head_summary(e: &Expr) -> String {
    match e.get_app_fn().kind() {
        ExprKind::Const(name, _) => name.to_string(),
        ExprKind::Sort(_) => "Sort".to_string(),
        ExprKind::Pi(_, _, _) => "Pi".to_string(),
        ExprKind::Lam(_, _, _) => "fun".to_string(),
        ExprKind::BVar(idx) => format!("BVar({idx})"),
        ExprKind::FVar(_) => "FVar".to_string(),
        ExprKind::Lit(_) => "Lit".to_string(),
        ExprKind::Proj(name, idx, _) => format!("Proj({name},{idx})"),
        ExprKind::App(_, _) => "App".to_string(),
        _ => "<expr>".to_string(),
    }
}

/// A deeper head-shape for a `Pi`/function type: report the arity (number of
/// leading `Pi` binders) alongside the ultimate codomain head. A function-typed
/// `Eq` operand mismatch shows up as `Pi[n]->head`, distinguishing it from an
/// atomic-operand mismatch.
fn type_shape(e: &Expr) -> String {
    let (depth, cur) = strip_pis(e);
    if depth == 0 {
        head_summary(e)
    } else {
        format!("Pi[{depth}]->{}", head_summary(cur))
    }
}

/// Strip leading `Pi` binders, returning the arity and the ultimate codomain.
fn strip_pis(e: &Expr) -> (u32, &Expr) {
    let mut depth = 0u32;
    let mut cur = e;
    while let ExprKind::Pi(_, _, cod) = cur.kind() {
        depth += 1;
        cur = cod;
    }
    (depth, cur)
}

/// Heads of an application's ARGUMENTS, bounded — the tie-breaker for when two
/// types share a shape.
///
/// [`head_summary`] reports only `get_app_fn()`, so `Eq α` and `Eq β` both
/// render `Eq` and a real mismatch between them prints as
/// `mismatch expected=Eq got=Eq`: a row that names nothing that differs and
/// cannot be acted on. 474 of the 2026-08-01 v32 kernel-rejects were exactly
/// that shape (`Eq`/`Eq`, `Pi[1]->Sort`/`Pi[1]->Sort`,
/// `Pi[2]->FVar`/`Pi[2]->FVar`), 39% of the run's kernel-rejects — the single
/// largest PRIMARY failure class, whose dependents cascade roughly 9.6:1 into
/// `unresolved-dep`.
///
/// Operand heads come from a small vocabulary, so this separates the buckets
/// without the cardinality blow-up that printing whole types would cause. Only
/// emitted when the shapes actually collide; every other signature is
/// byte-identical to before, so existing frequency rankings still line up.
fn arg_heads(e: &Expr, limit: usize) -> String {
    let args = e.get_app_args();
    if args.is_empty() {
        return String::new();
    }
    let mut heads: Vec<String> = args.iter().take(limit).map(|a| head_summary(a)).collect();
    if args.len() > limit {
        heads.push("..".to_string());
    }
    format!("<{}>", heads.join(","))
}

#[cfg(test)]
mod signature_tests {
    use super::{type_error_signature, Expr};
    use clean_kernel::name::Name;
    use clean_kernel::tc::TypeError;

    fn cst(n: &str) -> Expr {
        Expr::const_(Name::from_string(n), vec![])
    }

    fn mismatch(expected: Expr, inferred: Expr) -> TypeError {
        TypeError::TypeMismatch {
            expected: Box::new(expected),
            inferred: Box::new(inferred),
            location: None,
        }
    }

    /// Two types that SHARE a head must not both render as the bare head.
    ///
    /// `Eq Nat` vs `Eq Int` differ, but `head_summary` reports only
    /// `get_app_fn()`, so both printed `Eq` and the reject read
    /// `mismatch expected=Eq got=Eq` — 474 of the v32 run's kernel-rejects said
    /// exactly that and named nothing actionable.
    #[test]
    fn test_signature_distinguishes_operands_when_heads_collide() {
        let sig = type_error_signature(&mismatch(
            Expr::app(cst("Eq"), cst("Nat")),
            Expr::app(cst("Eq"), cst("Int")),
        ));
        assert!(
            sig.contains("Nat") && sig.contains("Int"),
            "operand heads must appear when the shapes collide, got: {sig}"
        );
        assert_ne!(
            sig, "mismatch expected=Eq got=Eq",
            "the uninformative form must be gone"
        );
    }

    /// Genuinely different shapes keep their EXACT previous signature, so
    /// existing frequency rankings and any saved baselines still line up.
    #[test]
    fn test_signature_unchanged_when_shapes_already_differ() {
        assert_eq!(
            type_error_signature(&mismatch(cst("Eq"), Expr::prop())),
            "mismatch expected=Eq got=Sort"
        );
    }

    /// Same shape and no operands at all: say so, rather than printing two
    /// identical sides and implying they looked different.
    #[test]
    fn test_signature_flags_shape_identical_with_no_operands() {
        let sig = type_error_signature(&mismatch(cst("Eq"), cst("Eq")));
        assert!(
            sig.contains("shape-identical"),
            "an opaque collision must be labelled, got: {sig}"
        );
    }
}

/// Normalize a kernel [`EnvError`] into a stable, frequency-rankable cluster
/// signature. For the dominant `TypeCheckFailed`/`TypeMismatch` case this is
/// `mismatch expected=<shape> got=<shape>`; other kinds get a bare tag.
pub(super) fn env_error_signature(err: &EnvError) -> String {
    match err {
        EnvError::TypeCheckFailed { source, .. } => type_error_signature(source),
        EnvError::DuplicateName(_) => "duplicate-name".to_string(),
        EnvError::TheoremTypeNotProp { .. } => "theorem-type-not-prop".to_string(),
        EnvError::ContainsFreeVar { .. } => "contains-free-var".to_string(),
        EnvError::ContainsMetavar { .. } => "contains-metavar".to_string(),
        EnvError::UndefinedLevelParam { .. } => "undefined-level-param".to_string(),
        EnvError::DuplicateLevelParam { .. } => "duplicate-level-param".to_string(),
        other => {
            // Fall back to the error's discriminant word (first token of Debug).
            let dbg = format!("{other:?}");
            let head = dbg.split([' ', '{', '(']).next();
            head.unwrap_or("env-error").to_lowercase()
        }
    }
}

/// Normalize a [`TypeError`] into a cluster signature. `TypeMismatch` is the
/// hot bucket — key it by the expected-vs-got *type shapes* (`Pi[n]->head`),
/// which distinguishes function-typed-equation mismatches from atomic ones.
fn type_error_signature(err: &TypeError) -> String {
    match err {
        TypeError::TypeMismatch {
            expected, inferred, ..
        } => {
            let (se, si) = (type_shape(expected), type_shape(inferred));
            if se != si {
                return format!("mismatch expected={se} got={si}");
            }
            // SHAPES COLLIDE — the difference is in the operands, which
            // `type_shape` discards. Without the operand heads this row reads
            // `expected=Eq got=Eq` and tells you nothing. Take the heads from
            // the same node the shape came from (the codomain after stripping
            // Pi binders), so `Pi[2]->Sort` reports the codomain's operands and
            // not the binder's.
            let (_, ce) = strip_pis(expected);
            let (_, ci) = strip_pis(inferred);
            let (ae, ai) = (arg_heads(ce, 3), arg_heads(ci, 3));
            if ae.is_empty() && ai.is_empty() {
                // Nothing further to say: same shape, no operands. Flag it as
                // opaque rather than implying the two sides looked different.
                return format!("mismatch expected={se} got={si} (shape-identical, no operands)");
            }
            format!("mismatch expected={se}{ae} got={si}{ai}")
        }
        TypeError::NotAFunction { ty, .. } => {
            format!("not-a-function ty={}", type_shape(ty))
        }
        TypeError::ExpectedSort { ty, .. } => {
            format!("expected-sort ty={}", type_shape(ty))
        }
        TypeError::UnknownConst(name) => format!("unknown-const {name}"),
        TypeError::UnboundVariable(_) => "unbound-variable".to_string(),
        TypeError::LevelCountMismatch { name, .. } => format!("level-count-mismatch {name}"),
        TypeError::HeartbeatExceeded { .. } => "heartbeat-exceeded".to_string(),
        TypeError::DeepRecursion => "deep-recursion".to_string(),
        other => {
            let dbg = format!("{other:?}");
            let head = dbg.split([' ', '{', '(']).next();
            format!("tc:{}", head.unwrap_or("type-error").to_lowercase())
        }
    }
}

/// Append one `reason\tname\tsignature` line to the dump file named by
/// `ISA_DUMP_REJECTS`. Best-effort: an I/O failure is silently ignored (this is
/// diagnostics, never a soundness or correctness gate). `signature` combines the
/// [`EnvError`] cluster key, the failing proof's spine-head axiom, and its
/// top-level node kind.
pub(super) fn append_reject(
    target: &str,
    reason: &str,
    name: &str,
    serial: i64,
    err: &EnvError,
    proof: &IsaProof,
) {
    let sig = format!(
        "{} | head={} | node={}",
        env_error_signature(err),
        spine_head(proof),
        proof_node_kind(proof),
    );
    let display_name = if name.is_empty() {
        format!("<anon.s{serial}>")
    } else {
        name.to_string()
    };
    if let Ok(mut f) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(target)
    {
        let _ = writeln!(f, "{reason}\t{display_name}\t{sig}");
    }
}

/// **Debug-only, opt-in** per-escalation-mode outcome trace for matched
/// theorems, gated on `ISA_DUMP_MODES` (a comma-separated list of name
/// substrings and/or serials). When any token matches the theorem's name
/// (substring) or serial, [`verify_one`](super::batch::verify_one) records each
/// mode's translate/kernel outcome and prints them on the reject path. Inert
/// (returns `false`, nothing recorded) unless set — reached only on the cold
/// path, no soundness surface.
pub(super) fn mode_trace_wanted(name: &str, serial: i64) -> bool {
    let Ok(want) = std::env::var("ISA_DUMP_MODES") else {
        return false;
    };
    let serial_s = serial.to_string();
    want.split(',')
        .map(str::trim)
        .filter(|t| !t.is_empty())
        .any(|t| name.contains(t) || serial_s == t)
}

/// Print a recorded per-mode outcome trace (see [`mode_trace_wanted`]).
pub(super) fn print_mode_trace(name: &str, serial: i64, lines: &[String]) {
    eprintln!("=== MODE TRACE name={name} serial={serial} ===");
    for l in lines {
        eprintln!("  {l}");
    }
}

/// **Debug-only, opt-in** full expected-vs-got dump for named/serial
/// theorems, gated on `ISA_DUMP_FULL` (a comma-separated list of name
/// substrings and/or exact serials). Inert unless set.
pub(super) fn maybe_dump_full(name: &str, serial: i64, err: &EnvError) {
    let Ok(want_list) = std::env::var("ISA_DUMP_FULL") else {
        return;
    };
    let matched = want_list
        .split(',')
        .map(str::trim)
        .filter(|w| !w.is_empty())
        .any(|want| (!name.is_empty() && name.contains(want)) || serial.to_string() == want);
    if !matched {
        return;
    }
    match err {
        EnvError::TypeCheckFailed {
            source: TypeError::TypeMismatch {
                expected, inferred, ..
            },
            ..
        } => {
            eprintln!("=== FULL MISMATCH name={name} serial={serial} ===");
            eprintln!("EXPECTED: {expected:?}");
            eprintln!("INFERRED: {inferred:?}");
        }
        EnvError::TypeCheckFailed {
            source: TypeError::NotAFunction { ty, location },
            ..
        } => {
            eprintln!("=== FULL NOT-A-FUNCTION name={name} serial={serial} ===");
            eprintln!("TY: {ty:?}");
            eprintln!("AT: {location:?}");
        }
        _ => {}
    }
}
