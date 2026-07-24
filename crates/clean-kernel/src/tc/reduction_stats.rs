// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-name reduction statistics (feature `reduction-stats`).
//!
//! Diagnostic instrumentation for kernel performance-parity work: counts
//! WHNF cache hits/misses, definition unfolds, and iota reductions per
//! constant so reduction blowups can be attributed to specific evaluation
//! shapes (e.g. the `Nat.Linear` decide-style proofs in `Lean.Omega.*`).
//!
//! Every hook call site is gated with `#[cfg(feature = "reduction-stats")]`
//! so production builds carry zero overhead. The `report`/`reset` API is
//! always present (returning an empty report when the feature is off) so
//! external diagnostic harnesses need no feature gates of their own.

#[cfg(feature = "reduction-stats")]
use crate::name::Name;
#[cfg(feature = "reduction-stats")]
use std::cell::RefCell;
#[cfg(feature = "reduction-stats")]
use std::collections::HashMap;

#[cfg(feature = "reduction-stats")]
#[derive(Default)]
struct Stats {
    whnf_hits: u64,
    whnf_misses: u64,
    defeq_hits: u64,
    defeq_misses: u64,
    delta_loop_iters: u64,
    unfold_real: u64,
    unfold_cached: u64,
    proof_irrel_true: u64,
    proof_irrel_none: u64,
    unfold_by_name: HashMap<Name, u64>,
    iota_by_rec: HashMap<Name, u64>,
    whnf_miss_by_head: HashMap<Name, u64>,
    /// (lhs head, rhs head) pairs at `is_def_eq_core` entry, with the
    /// max observed expression depth pair for that head pair.
    core_head_pairs: HashMap<(String, String), (u64, u32, u32)>,
    /// Concrete sampled comparisons (bounded; first + steady-state per shape).
    core_pair_samples: Vec<String>,
}

#[cfg(feature = "reduction-stats")]
fn head_label(e: &crate::expr::Expr) -> String {
    use crate::expr::ExprKind;
    match e.get_app_fn().kind() {
        ExprKind::Const(name, _) => name.to_string(),
        ExprKind::Sort(_) => "<sort>".to_string(),
        ExprKind::Lam(..) => "<lam>".to_string(),
        ExprKind::Pi(..) => "<pi>".to_string(),
        ExprKind::FVar(_) => "<fvar>".to_string(),
        ExprKind::BVar(_) => "<bvar>".to_string(),
        ExprKind::Lit(_) => "<lit>".to_string(),
        ExprKind::Proj(..) => "<proj>".to_string(),
        ExprKind::MData(..) => "<mdata>".to_string(),
        _ => "<other>".to_string(),
    }
}

#[cfg(feature = "reduction-stats")]
pub(crate) fn record_core_pair(a: &crate::expr::Expr, b: &crate::expr::Expr) {
    let key = (head_label(a), head_label(b));
    let (da, db) = (
        u32::from(a.meta().approx_depth()),
        u32::from(b.meta().approx_depth()),
    );
    STATS.with(|s| {
        let mut s = s.borrow_mut();
        let entry = s.core_head_pairs.entry(key.clone()).or_insert((0, 0, 0));
        entry.0 += 1;
        entry.1 = entry.1.max(da);
        entry.2 = entry.2.max(db);
        // Keep a few concrete samples per dominant pair shape: the 40,000th
        // occurrence shows the steady-state of a divergence, the 1st shows
        // its trigger.
        let count = entry.0;
        if count == 1 || count == 40_000 {
            let sample = format!(
                "[{}x] {} =?= {}\n  lhs: {:.600}\n  rhs: {:.600}",
                count,
                key.0,
                key.1,
                format!("{a}"),
                format!("{b}"),
            );
            s.core_pair_samples.push(sample);
        }
    });
}

#[cfg(feature = "reduction-stats")]
pub(crate) fn record_proof_irrel(result: Option<bool>) {
    STATS.with(|s| {
        let mut s = s.borrow_mut();
        if result == Some(true) {
            s.proof_irrel_true += 1;
        } else {
            s.proof_irrel_none += 1;
        }
    });
}

#[cfg(feature = "reduction-stats")]
thread_local! {
    static STATS: RefCell<Stats> = RefCell::new(Stats::default());
}

#[cfg(feature = "reduction-stats")]
pub(crate) fn record_whnf_cache(hit: bool, head: Option<&Name>) {
    STATS.with(|s| {
        let mut s = s.borrow_mut();
        if hit {
            s.whnf_hits += 1;
        } else {
            s.whnf_misses += 1;
            if let Some(name) = head {
                *s.whnf_miss_by_head.entry(name.clone()).or_insert(0) += 1;
            }
        }
    });
}

#[cfg(feature = "reduction-stats")]
pub(crate) fn record_defeq_cache(hit: bool) {
    STATS.with(|s| {
        let mut s = s.borrow_mut();
        if hit {
            s.defeq_hits += 1;
        } else {
            s.defeq_misses += 1;
        }
    });
}

#[cfg(feature = "reduction-stats")]
pub(crate) fn record_unfold(name: &Name, cached: bool) {
    STATS.with(|s| {
        let mut s = s.borrow_mut();
        if cached {
            s.unfold_cached += 1;
        } else {
            s.unfold_real += 1;
        }
        *s.unfold_by_name.entry(name.clone()).or_insert(0) += 1;
    });
}

#[cfg(feature = "reduction-stats")]
pub(crate) fn record_iota(rec_name: &Name) {
    STATS.with(|s| {
        let mut s = s.borrow_mut();
        *s.iota_by_rec.entry(rec_name.clone()).or_insert(0) += 1;
    });
}

/// One-shot deep-loop witness: when a single recursor's iota count crosses
/// the threshold, dump the live (already-reduced) application once so runaway
/// unary walks can be attributed to a concrete term shape. Diagnostic-only.
#[cfg(feature = "reduction-stats")]
pub(crate) fn record_iota_with_witness(rec_name: &Name, result: &crate::expr::Expr) {
    let dump = STATS.with(|s| {
        let mut s = s.borrow_mut();
        let c = s.iota_by_rec.entry(rec_name.clone()).or_insert(0);
        *c += 1;
        *c == 1_000_000
    });
    if dump {
        let txt = format!("{result:?}");
        let head: String = txt.chars().take(3000).collect();
        eprintln!("[reduction-stats] iota witness for {rec_name} at 1e6 steps:\n{head}");
    }
}

#[cfg(feature = "reduction-stats")]
pub(crate) fn record_delta_loop_iter() {
    STATS.with(|s| s.borrow_mut().delta_loop_iters += 1);
}

// ══════════════════════════════════════════════════════════════════════════
// GRIND TRACE  (task: SEE the operative carrier-tower def-eq pair)
//
// When a large-literal `Nat.rec` iota expansion is about to fire (major >= 512
// — the runaway carrier grind), log the ENCLOSING `is_def_eq_core` comparison
// (innermost + outermost live frame), the recursor+major, and a filtered call
// path (Rust backtrace). One log per def-eq frame, capped, gated on the
// `CLEAN_TRACE_GRIND` env var so ordinary `reduction-stats` runs are
// unperturbed. Diagnostic-only; verdict-neutral (reads term shapes, never
// mutates or reduces).
// ══════════════════════════════════════════════════════════════════════════

#[cfg(feature = "reduction-stats")]
use crate::expr::{BigNat, Expr, ExprKind, Literal};
#[cfg(feature = "reduction-stats")]
use std::cell::Cell;

#[cfg(feature = "reduction-stats")]
struct GrindState {
    /// (frame_id, a, b) for each live `is_def_eq_core` call — pushed at entry.
    stack: Vec<(u64, Expr, Expr)>,
    next_frame_id: u64,
    /// frame_ids already logged (dedup: one grind episode per frame).
    logged_frames: Vec<u64>,
    logs_emitted: u32,
    /// Cap on the binop guard/unfold probe lines.
    probe_logs: u32,
}

#[cfg(feature = "reduction-stats")]
impl Default for GrindState {
    fn default() -> Self {
        GrindState {
            stack: Vec::new(),
            next_frame_id: 1,
            logged_frames: Vec::new(),
            logs_emitted: 0,
            probe_logs: 0,
        }
    }
}

#[cfg(feature = "reduction-stats")]
thread_local! {
    static GRIND: RefCell<GrindState> = RefCell::new(GrindState::default());
}

/// Cap on grind-trace logs: keeps the trace readable and (with a small
/// heartbeat budget) bails the runaway grind promptly.
#[cfg(feature = "reduction-stats")]
const GRIND_LOG_CAP: u32 = 16;

#[cfg(feature = "reduction-stats")]
fn trace_grind_enabled() -> bool {
    thread_local! { static EN: Cell<i8> = const { Cell::new(-1) }; }
    EN.with(|c| {
        let v = c.get();
        if v >= 0 {
            return v == 1;
        }
        let on = std::env::var("CLEAN_TRACE_GRIND").is_ok();
        c.set(i8::from(on));
        on
    })
}

/// RAII guard pushed at `is_def_eq_core` entry so the innermost live comparison
/// is available when a grind fires deep inside that frame's WHNF.
#[cfg(feature = "reduction-stats")]
pub(crate) struct DefEqFrameGuard {
    active: bool,
}

#[cfg(feature = "reduction-stats")]
impl DefEqFrameGuard {
    pub(crate) fn enter(a: &Expr, b: &Expr) -> Self {
        if !trace_grind_enabled() {
            return DefEqFrameGuard { active: false };
        }
        GRIND.with(|g| {
            let mut g = g.borrow_mut();
            let id = g.next_frame_id;
            g.next_frame_id += 1;
            g.stack.push((id, a.clone(), b.clone()));
        });
        DefEqFrameGuard { active: true }
    }
}

#[cfg(feature = "reduction-stats")]
impl Drop for DefEqFrameGuard {
    fn drop(&mut self) {
        if !self.active {
            return;
        }
        GRIND.with(|g| {
            g.borrow_mut().stack.pop();
        });
    }
}

/// Called at the `Nat.rec` literal-major iota-expansion site. Logs the
/// enclosing def-eq pair when the major is large (>= 512) — the grind step.
/// `rec_app` is the full recursor application being iota'd (its minors reveal
/// the true operation: `Nat.add`/`Nat.sub` seed vs a `decLe`/`Nat.ble` body).
#[cfg(feature = "reduction-stats")]
pub(crate) fn record_iota_grind(rec_name: &Name, n: &BigNat, rec_app: &Expr) {
    // Cheap threshold gate first (the vast majority of iotas are small).
    let big = match n {
        BigNat::Small(v) => *v >= 512,
        BigNat::Big(_) => true,
    };
    if !big || !trace_grind_enabled() {
        return;
    }
    let val = format!("{n}");
    let app_shape = expr_shape(rec_app, 8, 900);
    GRIND.with(|g| {
        let mut g = g.borrow_mut();
        if g.logs_emitted >= GRIND_LOG_CAP {
            return;
        }
        let cur = g.stack.last().map_or(0, |(id, _, _)| *id);
        if g.logged_frames.contains(&cur) {
            return;
        }
        g.logged_frames.push(cur);
        g.logs_emitted += 1;
        let episode = g.logs_emitted;
        let depth = g.stack.len();
        let inner = g
            .stack
            .last()
            .map(|(_, a, b)| (expr_shape(a, 7, 1100), expr_shape(b, 7, 1100)));
        let outer = g
            .stack
            .first()
            .map(|(_, a, b)| (expr_shape(a, 5, 600), expr_shape(b, 5, 600)));
        eprintln!(
            "\n════════ GRIND #{episode}: {rec_name} iota, major={val}, def-eq depth={depth} ════════"
        );
        eprintln!("[recursor application being iota'd]\n  {app_shape}");
        if let Some((a, b)) = &inner {
            eprintln!("[innermost def-eq frame]\n  A =?= B\n  A: {a}\n  B: {b}");
        } else {
            eprintln!("[no live def-eq frame — grind is OUTSIDE is_def_eq (infer_type / check?)]");
        }
        if depth > 1 {
            if let Some((a, b)) = &outer {
                eprintln!("[outermost def-eq frame]\n  A: {a}\n  B: {b}");
            }
        }
        eprintln!("[call path]\n{}", filtered_backtrace(episode));
    });
}

/// Guard-decision probe: log how `native_nat_binop_grind_stuck` decided for a
/// `Nat.add/sub/mul/pow` head (did the 2nd operand whnf to a large literal?
/// did the guard fire → leave it stuck?). Answers "why the guard didn't fire".
#[cfg(feature = "reduction-stats")]
pub(crate) fn record_binop_guard(name: &Name, a2: &Expr, count: Option<&BigNat>, fired: bool) {
    if !trace_grind_enabled() {
        return;
    }
    // Only the grind-relevant consultations: fired (would leave a large-count op
    // stuck) OR a compound closed 2nd operand (e.g. `UInt32.toNat (HSub …)`),
    // which is exactly the operative pattern. Skips the trivial symbolic noise
    // (`a2 ∈ {fvar, Nat.zero, Nat.succ …}`) that otherwise floods the cap.
    if !fired && !a2_is_compound_closed_candidate(a2) {
        return;
    }
    let shape = expr_shape(a2, 6, 240);
    let count_str = match count {
        Some(v) => format!("{v}"),
        None => "<a2 did NOT whnf to a Nat literal/succ-tower>".to_string(),
    };
    GRIND.with(|g| {
        let mut g = g.borrow_mut();
        if g.probe_logs >= 40 {
            return;
        }
        g.probe_logs += 1;
        eprintln!("[GUARD {name}] fired(stuck)={fired}  whnf(a2)={count_str}  a2={shape}");
    });
}

/// The 2nd operand is the OPERATIVE carrier grind pattern: an `App` whose head
/// `Const` is NOT itself a `Nat.*` op — i.e. a `UInt32.toNat …` / `BitVec.toNat
/// …` / `HSub …` closed carrier expression that whnfs to a large literal. This
/// excludes the pervasive symbolic `Nat.add/mul fvar …` arithmetic noise.
#[cfg(feature = "reduction-stats")]
fn a2_is_compound_closed_candidate(a2: &Expr) -> bool {
    match a2.kind() {
        ExprKind::App(..) => match a2.get_app_fn().kind() {
            ExprKind::Const(n, _) => !n.to_string().starts_with("Nat."),
            _ => false,
        },
        _ => false,
    }
}

/// Unfold probe: log when a `Nat.add/sub/mul/pow` Const head falls through the
/// guard to `beta_or_iota_step` (i.e. is about to delta-unfold into its
/// `Nat.rec` seed) at the WHNF App pre-check site.
#[cfg(feature = "reduction-stats")]
pub(crate) fn record_binop_unfold(name: &Name, e: &Expr) {
    if !trace_grind_enabled() {
        return;
    }
    let is_binop = name.to_string();
    if !(is_binop == "Nat.add"
        || is_binop == "Nat.sub"
        || is_binop == "Nat.mul"
        || is_binop == "Nat.pow")
    {
        return;
    }
    // Same filter as the guard probe: only compound-closed 2nd operands (the
    // operative `UInt32.toNat (HSub …)` grind pattern), not the fvar/zero noise.
    let args = e.get_app_args();
    match args.get(1) {
        Some(a2) if a2_is_compound_closed_candidate(a2) => {}
        _ => return,
    }
    let shape = expr_shape(e, 5, 320);
    GRIND.with(|g| {
        let mut g = g.borrow_mut();
        if g.probe_logs >= 40 {
            return;
        }
        g.probe_logs += 1;
        eprintln!("[UNFOLD-WHNF {name}] guard declined → delta-unfolding: {shape}");
    });
}

/// Log every delta-unfold of a bare `Nat.add/sub/mul/pow` DEFINITION (→ its
/// `Nat.rec` seed). This is the guard-bypass: the `native_nat_binop_grind_stuck`
/// guard only inspects 2-arg `Nat.add …` apps at the WHNF App pre-check, but a
/// bare `Nat.add` Const reached as an application HEAD (e.g. via an instance
/// projection `(instHAdd …).hAdd`) is unfolded here with no operand in view.
#[cfg(feature = "reduction-stats")]
pub(crate) fn record_binop_def_unfold(name: &Name) {
    if !trace_grind_enabled() {
        return;
    }
    let s = name.to_string();
    if !(s == "Nat.add" || s == "Nat.sub" || s == "Nat.mul" || s == "Nat.pow") {
        return;
    }
    GRIND.with(|g| {
        let mut g = g.borrow_mut();
        if g.probe_logs >= 40 {
            return;
        }
        g.probe_logs += 1;
        let depth = g.stack.len();
        eprintln!("[BINOP-DEF-UNFOLD {s}]  (bare Const → Nat.rec seed; def-eq depth={depth})");
    });
}

/// Log every DECLINED bare-Const eager delta-unfold of a guarded
/// `Nat.add/sub/mul/pow` (the `try_unfold_definition` deferral) — the
/// non-vacuity witness that the bare-Const guard-bypass closure is firing.
#[cfg(feature = "reduction-stats")]
pub(crate) fn record_binop_bare_defer(name: &Name) {
    if !trace_grind_enabled() {
        return;
    }
    let s = name.to_string();
    GRIND.with(|g| {
        let mut g = g.borrow_mut();
        if g.probe_logs >= 40 {
            return;
        }
        g.probe_logs += 1;
        let depth = g.stack.len();
        eprintln!("[BINOP-BARE-DEFER {s}]  (bare Const kept folded; def-eq depth={depth})");
    });
}

/// Filtered Rust backtrace — clean-kernel `tc::` fn frames only, so the WHNF
/// driver (Phase-1 `whnf_core_no_delta`, `lazy_delta_reduction`, `infer_type`,
/// …) that reached this grind is visible. Needs `RUST_BACKTRACE=1`. On the
/// first episode, also dumps the FULL raw backtrace to `CLEAN_TRACE_GRIND_BT`
/// (if set) for ground truth.
#[cfg(feature = "reduction-stats")]
fn filtered_backtrace(episode: u32) -> String {
    const FN_MARKERS: &[&str] = &[
        "whnf_core_inner",
        "whnf_impl",
        "whnf_core",
        "whnf_with",
        "whnf_outer",
        "::whnf",
        "is_def_eq_impl",
        "is_def_eq_core",
        "is_def_eq_args",
        "is_def_eq_structural",
        "is_def_eq_proof_irrel",
        "lazy_delta",
        "try_iota_reduction",
        "try_branch_sharing",
        "try_unfold",
        "infer_type",
        "infer_impl",
        "check_type",
        "beta_or_iota",
        "reduce_nat",
        "reduce_native",
    ];
    let bt = std::backtrace::Backtrace::force_capture();
    let text = format!("{bt}");
    if episode == 1 {
        if let Ok(path) = std::env::var("CLEAN_TRACE_GRIND_BT") {
            let _ = std::fs::write(&path, &text);
        }
    }
    let mut out = String::new();
    let mut kept = 0usize;
    let mut last = String::new();
    for line in text.lines() {
        let l = line.trim();
        if l.contains("clean_kernel::")
            && !l.contains("reduction_stats")
            && FN_MARKERS.iter().any(|m| l.contains(m))
        {
            let shown = l.split("clean_kernel::").nth(1).unwrap_or(l).to_string();
            if shown == last {
                continue;
            }
            last = shown.clone();
            out.push_str("    ");
            out.push_str(&shown);
            out.push('\n');
            kept += 1;
            if kept >= 50 {
                out.push_str("    …(truncated)\n");
                break;
            }
        }
    }
    if out.is_empty() {
        out.push_str("    (no matching clean_kernel frames — run with RUST_BACKTRACE=1)\n");
    }
    out
}

/// Depth- and budget-limited structural shape printer (never reduces; never
/// materializes a full succ-tower). Used only by the grind trace.
#[cfg(feature = "reduction-stats")]
fn expr_shape(e: &Expr, depth: u32, budget: usize) -> String {
    let mut out = String::new();
    let mut remaining = budget;
    write_shape(e, depth, &mut out, &mut remaining);
    out
}

#[cfg(feature = "reduction-stats")]
fn push_budget(out: &mut String, s: &str, budget: &mut usize) {
    if *budget == 0 {
        return;
    }
    if s.len() <= *budget {
        out.push_str(s);
        *budget -= s.len();
    } else {
        // Truncate at the nearest char boundary at or below the budget —
        // byte-slicing mid-codepoint (e.g. inside a '…' produced by a nested
        // truncation) panics and aborts the traced run. Observed live: a
        // CLEAN_TRACE_EXTEQ probe on Init/GrindInstances/ToInt died at
        // "end byte index 1 is not a char boundary; it is inside '…'".
        let mut cut = *budget;
        while cut > 0 && !s.is_char_boundary(cut) {
            cut -= 1;
        }
        out.push_str(&s[..cut]);
        *budget = 0;
        out.push('…');
    }
}

#[cfg(feature = "reduction-stats")]
fn write_shape(e: &Expr, depth: u32, out: &mut String, budget: &mut usize) {
    if *budget == 0 {
        return;
    }
    if depth == 0 {
        push_budget(out, "…", budget);
        return;
    }
    match e.kind() {
        ExprKind::BVar(i) => push_budget(out, &format!("#{i}"), budget),
        ExprKind::FVar(_) => push_budget(out, "fvar", budget),
        ExprKind::Sort(_) => push_budget(out, "Sort", budget),
        ExprKind::Const(n, _) => push_budget(out, &n.to_string(), budget),
        ExprKind::Lit(Literal::Nat(v)) => push_budget(out, &format!("lit:{v}"), budget),
        ExprKind::Lit(Literal::String(_)) => push_budget(out, "lit:str", budget),
        ExprKind::App(..) => {
            let f = e.get_app_fn();
            let args = e.get_app_args();
            push_budget(out, "(", budget);
            write_shape(f, depth - 1, out, budget);
            for a in args {
                if *budget == 0 {
                    break;
                }
                push_budget(out, " ", budget);
                write_shape(a, depth - 1, out, budget);
            }
            push_budget(out, ")", budget);
        }
        ExprKind::Lam(_, ty, body) => {
            push_budget(out, "λ(", budget);
            write_shape(ty, depth - 1, out, budget);
            push_budget(out, ").", budget);
            write_shape(body, depth - 1, out, budget);
        }
        ExprKind::Pi(_, ty, body) => {
            push_budget(out, "Π(", budget);
            write_shape(ty, depth - 1, out, budget);
            push_budget(out, ").", budget);
            write_shape(body, depth - 1, out, budget);
        }
        ExprKind::Let(..) => push_budget(out, "<let>", budget),
        ExprKind::Proj(n, i, inner) => {
            push_budget(out, &format!("proj[{n}.{i}]("), budget);
            write_shape(inner, depth - 1, out, budget);
            push_budget(out, ")", budget);
        }
        ExprKind::MData(_, inner) => write_shape(inner, depth, out, budget),
        _ => push_budget(out, "<x>", budget),
    }
}

/// Reset all reduction statistics for the current thread.
///
/// No-op unless the `reduction-stats` feature is enabled.
pub fn reduction_stats_reset() {
    #[cfg(feature = "reduction-stats")]
    STATS.with(|s| *s.borrow_mut() = Stats::default());
    #[cfg(feature = "reduction-stats")]
    GRIND.with(|g| *g.borrow_mut() = GrindState::default());
}

/// Render the current thread's reduction statistics as a human-readable
/// report (top `top` entries per per-name table).
///
/// Returns an empty string unless the `reduction-stats` feature is enabled.
#[must_use]
pub fn reduction_stats_report(top: usize) -> String {
    #[cfg(feature = "reduction-stats")]
    {
        STATS.with(|s| {
            let s = s.borrow();
            let mut out = String::new();
            out.push_str(&format!(
                "whnf cache: {} hits / {} misses; def_eq cache: {} hits / {} misses\n\
                 unfolds: {} real / {} cached; lazy-delta loop iterations: {}\n\
                 proof-irrel: {} true / {} none\n",
                s.whnf_hits,
                s.whnf_misses,
                s.defeq_hits,
                s.defeq_misses,
                s.unfold_real,
                s.unfold_cached,
                s.delta_loop_iters,
                s.proof_irrel_true,
                s.proof_irrel_none,
            ));
            {
                let mut pairs: Vec<(&(String, String), &(u64, u32, u32))> =
                    s.core_head_pairs.iter().collect();
                pairs.sort_by_key(|entry| std::cmp::Reverse(entry.1 .0));
                out.push_str(&format!("def-eq core head pairs (top {top}):\n"));
                for ((ha, hb), (count, da, db)) in pairs.iter().take(top) {
                    out.push_str(&format!(
                        "  {count:>12}  {ha} =?= {hb}  (max depth {da}/{db})\n"
                    ));
                }
            }
            if !s.core_pair_samples.is_empty() {
                out.push_str("sampled comparisons:\n");
                for sample in s.core_pair_samples.iter().take(24) {
                    out.push_str(sample);
                    out.push('\n');
                }
            }
            let mut tables: [(&str, Vec<(&Name, &u64)>); 3] = [
                ("unfolds by name", s.unfold_by_name.iter().collect()),
                ("iota by recursor", s.iota_by_rec.iter().collect()),
                ("whnf misses by head", s.whnf_miss_by_head.iter().collect()),
            ];
            for (label, entries) in &mut tables {
                entries.sort_by(|a, b| b.1.cmp(a.1));
                out.push_str(&format!("{label} (top {top}):\n"));
                for (name, count) in entries.iter().take(top) {
                    out.push_str(&format!("  {count:>12}  {name}\n"));
                }
            }
            out
        })
    }
    #[cfg(not(feature = "reduction-stats"))]
    {
        let _ = top;
        String::new()
    }
}
