// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::expr::{Expr, ExprKind, FVarId};
use crate::name::Name;
use crate::tc::expr_location::ExprLocation;
use crate::tc::heartbeat_profiler::HeartbeatProfile;

/// One-token summary of the head of an expression's application spine.
///
/// Renderings of mismatching types can run to kilobytes; the head
/// (`Nat.add`, `Sort`, `Pi`, ...) is usually enough to orient. Used to append
/// a compact `heads:` suffix to the type-error displays — additive only, the
/// full rendering stays.
///
/// These strings reach editors: an `ElabError` wrapping one of these is what
/// the problems panel shows, so the type bodies below are rendered through
/// `Display for Expr` (Lean-ish notation), never through `{:?}` (which would
/// ship `Const(Name { … lean4_hash: … })` to a user).
fn head_summary(e: &Expr) -> String {
    match &e.get_app_fn().kind {
        ExprKind::Const(name, _) => name.to_string(),
        ExprKind::Sort(level) => format!("Sort({level})"),
        ExprKind::Pi(_, _, _) => "Pi".to_string(),
        ExprKind::Lam(_, _, _) => "fun".to_string(),
        ExprKind::BVar(idx) => format!("BVar({idx})"),
        // `{id:?}` would render `FVarId(0)` and `{lit:?}` would render
        // `Nat(Small(1))` — Rust type names in a message a user reads.
        ExprKind::FVar(id) => format!("FVar({})", id.as_u64()),
        ExprKind::Lit(lit) => lit.to_string(),
        ExprKind::Proj(name, idx, _) => format!("Proj({name}, {idx})"),
        _ => "<expr>".to_string(),
    }
}

/// Collect the universe levels appearing in `e`, in traversal order.
///
/// Used only to disambiguate a mismatch whose two sides print identically.
fn levels_in(e: &Expr) -> Vec<String> {
    fn go(e: &Expr, out: &mut Vec<String>) {
        match &e.kind {
            ExprKind::Const(_, levels) => out.extend(levels.iter().map(ToString::to_string)),
            ExprKind::Sort(level) => out.push(level.to_string()),
            ExprKind::App(f, a) => {
                go(f, out);
                go(a, out);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                go(ty, out);
                go(body, out);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                go(ty, out);
                go(val, out);
                go(body, out);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => go(inner, out),
            _ => {}
        }
    }
    let mut out = Vec::new();
    go(e, &mut out);
    out
}

/// Explain a mismatch whose two sides render to the SAME string.
///
/// `Display for Expr` deliberately omits universe levels — `LE2.{u} x` and
/// `LE2.{v} x` both print `LE2 x` — so a universe mismatch, which is the most
/// common kind of kernel rejection on Mathlib source, arrives as
/// `expected LE2 fvar#4, got LE2 fvar#4`. A message asserting that two
/// identical things differ is worse than no message: it reads as a checker bug
/// rather than as a fact about the term.
///
/// Rather than making every message noisier by always printing levels, this
/// fires only on the collision, where the extra words are the entire content.
/// If the levels agree too, it says so — "the difference is somewhere this
/// printer does not show" is still a true and actionable statement, and it
/// stops the reader re-reading two identical strings looking for the typo.
fn disambiguate(expected: &Expr, inferred: &Expr) -> String {
    if expected.to_string() != inferred.to_string() {
        return String::new();
    }
    let el = levels_in(expected);
    let il = levels_in(inferred);
    if el != il {
        return format!(
            "\n  both sides print identically; they differ in universe levels: \
             {{{}}} vs {{{}}}",
            el.join(", "),
            il.join(", ")
        );
    }
    "\n  both sides print identically and carry the same universe levels; the \
     difference is in a part this printer does not show (binder info, \
     metadata, or free-variable identity)"
        .to_string()
}

/// Type checking errors.
///
/// Note: Expr fields are boxed to reduce the size of the Result type on the success path.
/// This improves performance since errors are rare but Results are returned frequently.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum TypeError {
    /// De Bruijn index exceeds the local context depth
    #[error("Unbound variable index: {0}")]
    UnboundVariable(u32),
    /// Free variable ID not found in the environment
    #[error("Unknown free variable: {0:?}")]
    UnknownFVar(FVarId),
    /// Constant name not declared in the environment
    #[error("Unknown constant: {0}")]
    UnknownConst(Name),
    /// Application target is not a function type
    #[error("Expected function type, got: {ty} (head: {}){}", head_summary(ty), location.as_ref().map(|l| format!("\n  {l}")).unwrap_or_default())]
    NotAFunction {
        /// The type that was found instead of a function type
        ty: Box<Expr>,
        /// Expression location trail from the declaration root to the error site.
        /// `None` when location tracking is not active.
        /// Part of #3425.
        location: Option<Box<ExprLocation>>,
    },
    /// Argument type doesn't match parameter type
    #[error(
        "Type mismatch: expected {expected}, got {inferred} (heads: {} vs {}){}{}",
        head_summary(expected),
        head_summary(inferred),
        disambiguate(expected, inferred),
        location.as_ref().map(|l| format!("\n  {l}")).unwrap_or_default()
    )]
    TypeMismatch {
        /// The type expected by the context
        expected: Box<Expr>,
        /// The type that was actually inferred
        inferred: Box<Expr>,
        /// Expression location trail from the declaration root to the error site.
        /// `None` when location tracking is not active.
        /// Part of #3425.
        location: Option<Box<ExprLocation>>,
    },
    /// Universe-level inference exceeded the maximum Pi-nesting depth.
    /// Returning a fallback level (e.g. `Sort 0`) would be UNSOUND — it can
    /// under-report a large universe and defeat the theorem-is-Prop gate and
    /// per-field universe-consistency checks — so this is a hard error.
    #[error("Sort inference exceeded maximum Pi-nesting depth ({depth})")]
    SortDepthExceeded {
        /// The depth at which universe inference gave up.
        depth: u32,
    },
    /// Expected a Sort (Type or Prop) but got something else
    #[error("Expected sort, got: {ty} (head: {}){}", head_summary(ty), location.as_ref().map(|l| format!("\n  {l}")).unwrap_or_default())]
    ExpectedSort {
        /// The type that was found instead of a Sort
        ty: Box<Expr>,
        /// Expression location trail from the declaration root to the error site.
        /// `None` when location tracking is not active.
        /// Part of #3425.
        location: Option<Box<ExprLocation>>,
    },
    /// Projection target is not a structure type
    #[error("Invalid projection: type {0} is not a structure")]
    InvalidProjNotStruct(Box<Expr>),
    /// Projection target is an inductive with multiple constructors
    #[error("Invalid projection: inductive {0} does not have a unique constructor")]
    InvalidProjNotUniqueConstructor(Name),
    /// Projection index exceeds the number of fields
    #[error("Invalid projection: index {0} out of bounds for structure with {1} fields")]
    InvalidProjIndexOutOfBounds(u32, u32),
    /// Projection target type has wrong argument count (not exactly num_params + num_indices)
    #[error("Invalid projection: struct type has {got} type arguments, expected {expected} ({num_params} params + {num_indices} indices)")]
    InvalidProjWrongArgCount {
        /// Number of type arguments provided
        got: usize,
        /// Total expected arguments (num_params + num_indices)
        expected: usize,
        /// Number of parameters
        num_params: usize,
        /// Number of indices
        num_indices: usize,
    },
    /// Referenced inductive type not found in environment
    #[error("Unknown inductive type: {0}")]
    UnknownInductive(Name),

    /// Projection from Prop type yields non-Prop field (Lean 4 parity)
    ///
    /// Per Lean 4 type_checker.cpp:260-262, projections from Prop types must
    /// only yield Prop-typed fields to preserve proof irrelevance.
    #[error("Invalid projection: Prop-typed structure cannot project non-Prop field at index {field_idx}")]
    InvalidProjFromProp {
        /// Index of the field being projected
        field_idx: u32,
    },

    /// Operation requires a specific mode (Cubical, Classical, etc.)
    #[error("Feature '{feature}' requires {mode} mode")]
    ModeRequired {
        /// Name of the feature that requires the mode
        feature: String,
        /// Name of the required mode
        mode: String,
    },

    /// Constant applied with wrong number of universe levels (#1277)
    ///
    /// Lean 4 enforces this in both type_checker.cpp:92-114 (infer_constant)
    /// and instantiate.cpp:248-254 (instantiate_type_lparams).
    #[error("Level count mismatch for {name}: declared {expected} level params, got {got}")]
    LevelCountMismatch {
        /// Name of the constant
        name: Name,
        /// Number of declared level parameters
        expected: usize,
        /// Number of supplied levels
        got: usize,
    },

    /// Type checking exceeded the heartbeat limit (deterministic timeout).
    ///
    /// The heartbeat counter tracks major operations (whnf, is_def_eq,
    /// infer_type) and triggers this error when the limit is exceeded.
    /// This prevents runaway type checking on pathological inputs.
    ///
    /// Lean 4 reference: `check_system` in `src/runtime/interrupt.h`.
    /// Default limit: 200,000 (matching Lean 4). Limit of 0 means unlimited.
    ///
    /// Corresponds to Lean 4's `deterministic_timeout` in `kernel_exception.h:203`.
    #[error("(deterministic) heartbeat limit exceeded, current limit: {limit} (use `set_option maxHeartbeats <num>` to increase){}", profile.as_ref().map(|p| format!("\n\n{p}")).unwrap_or_default())]
    HeartbeatExceeded {
        /// The configured heartbeat limit that was exceeded.
        limit: u32,
        /// Optional profiler breakdown (present when profiling was enabled).
        /// Boxed to keep the common-case `TypeError` size small.
        ///
        /// Part of #3399.
        profile: Option<Box<HeartbeatProfile>>,
    },

    /// The AMBIENT, declaration-scoped cooperative budget ran out.
    ///
    /// Distinct from [`TypeError::HeartbeatExceeded`] on purpose, and the
    /// distinction is the point. `HeartbeatExceeded` says "one type checker
    /// spent its own fuel"; this says "the declaration this thread is working
    /// on has spent the whole budget its owner granted it, across every type
    /// checker it built". The owner is the declaration loop — `clean check` —
    /// not the kernel.
    ///
    /// **This is not a verdict on the declaration.** It reports that the work
    /// did not finish. A consumer must never fold it into a pass, and must not
    /// fold it into a failure-to-prove either: nothing was refuted. See
    /// [`crate::tc::set_declaration_budget`].
    #[error("declaration budget exhausted: the ambient per-declaration budget of {limit} kernel operations ran out before this declaration finished (raise it with `clean check --decl-budget <n>`, or `0` for unlimited). This is NOT a verdict on the declaration: nothing was proved and nothing was refuted.")]
    DeclarationBudgetExhausted {
        /// The configured ambient per-declaration budget that was exhausted.
        limit: u64,
    },

    /// Memory limit exceeded during type checking.
    ///
    /// Placeholder for future memory tracking. Currently not triggered by the
    /// kernel — reserved for elaborator-level memory budgets or external
    /// monitoring that needs to signal the kernel to abort.
    ///
    /// Lean 4 reference: `kernel_exception.h:207` (`excessive_memory`).
    #[error("excessive memory consumption detected")]
    ExcessiveMemory,

    /// Stack depth limit exceeded during type checking.
    ///
    /// Triggered when recursive type checking operations exceed the maximum
    /// allowed depth. Protects against stack overflow on deeply nested terms
    /// (e.g., tower-of-Pi types, deeply nested match expressions).
    ///
    /// Lean 4 reference: `kernel_exception.h:211` (`deep_recursion`).
    #[error("deep recursion detected during type checking")]
    DeepRecursion,

    /// Type checking was interrupted by an external signal.
    ///
    /// Allows clean cancellation of long-running type checking operations.
    /// The caller sets an interrupt flag, and the next heartbeat check
    /// (or explicit interrupt check) returns this error.
    ///
    /// Lean 4 reference: `kernel_exception.h:215` (`interrupted`).
    #[error("type checking interrupted")]
    Interrupted,

    /// Universe level parameter not in the declared level_params list.
    ///
    /// Lean 4 reference: `type_checker.cpp:63-73` (`check_level`).
    /// When `infer_only=false` (full checking mode), Sort expressions must
    /// only reference level parameters that are in the current declaration's
    /// `level_params` list. This catches undeclared universe parameters that
    /// would otherwise silently pass type inference.
    ///
    /// Part of #3225.
    #[error("Undefined level parameter '{param}' in Sort expression")]
    UndefinedLevelParam {
        /// The level parameter name that is not in the allowed list
        param: Name,
    },

    /// Reference to an unsafe declaration from a safe context.
    ///
    /// Lean 4 reference: `type_checker.cpp:100-104` (`infer_constant`).
    /// When `infer_only=false`, constants marked `unsafe` cannot be referenced
    /// unless the type checker is in an unsafe-allowed context.
    ///
    /// Part of #3226.
    #[error("Declaration '{name}' is unsafe and cannot be used in safe context")]
    UnsafeDeclaration {
        /// Name of the unsafe declaration
        name: Name,
    },

    /// Reference to a partial declaration from a non-partial context.
    ///
    /// Lean 4 reference: `type_checker.cpp:105-108` (`infer_constant`).
    /// When `infer_only=false`, constants marked `partial` cannot be referenced
    /// unless the type checker allows partial declarations.
    ///
    /// Part of #3226.
    #[error("Declaration '{name}' is partial and cannot be used in non-partial context")]
    PartialDeclaration {
        /// Name of the partial declaration
        name: Name,
    },

    /// Under [`crate::env::KernelTheory::Lean`] (and `LeanReference`),
    /// instantiating `name`'s universe parameters met a stored `max`/`imax`
    /// node that Lean's `instantiate` keeps when the `.olean` shares its level
    /// objects and rebuilds to a different level when it does not
    /// (`level/lean_kernel.rs`). Lean's own verdict on the declaration then
    /// depends on object sharing, which Clean cannot observe, so the check is
    /// refused (DECISIONS R150). No stored level in pinned `Init`, `Std` or
    /// `Lean` has such a node.
    #[error("universe instantiation of '{name}' depends on .olean object sharing (a stored max/imax that Lean's mk_max/mk_imax would rebuild differently); refused under the Lean kernel theory")]
    LevelSharingDependent {
        /// The constant whose type or value was being instantiated.
        name: Name,
    },
}

impl TypeError {
    /// Get the expression location trail, if present.
    ///
    /// Returns `None` for error variants that don't carry location info,
    /// or when location tracking was not active.
    ///
    /// Part of #3425.
    #[must_use]
    pub fn location(&self) -> Option<&ExprLocation> {
        match self {
            TypeError::NotAFunction { location, .. }
            | TypeError::TypeMismatch { location, .. }
            | TypeError::ExpectedSort { location, .. } => location.as_deref(),
            _ => None,
        }
    }

    /// Attach an expression location to this error.
    ///
    /// Only modifies variants that support location tracking (NotAFunction,
    /// TypeMismatch, ExpectedSort). Other variants are returned unchanged.
    ///
    /// Part of #3425.
    #[must_use]
    pub fn with_location(mut self, loc: Option<Box<ExprLocation>>) -> Self {
        match &mut self {
            TypeError::NotAFunction { location, .. }
            | TypeError::TypeMismatch { location, .. }
            | TypeError::ExpectedSort { location, .. } => {
                *location = loc;
            }
            _ => {}
        }
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_mismatch_display_appends_head_summary() {
        let nat = Expr::const_str("Nat");
        let arg = Expr::const_str("Nat.zero");
        let bool_ty = Expr::const_str("Bool");
        // `Nat Nat.zero` vs `Bool`: the heads suffix must name the spine
        // heads even though the Debug dump shows the full applications.
        let err = TypeError::TypeMismatch {
            expected: Box::new(Expr::app(nat, arg)),
            inferred: Box::new(bool_ty),
            location: None,
        };
        let msg = err.to_string();
        assert!(
            msg.starts_with("Type mismatch: expected"),
            "prefix must stay stable for downstream matchers, got: {msg}"
        );
        assert!(
            msg.contains("(heads: Nat vs Bool)"),
            "display must append the compact head summary, got: {msg}"
        );
    }

    #[test]
    fn test_not_a_function_display_appends_head() {
        let err = TypeError::NotAFunction {
            ty: Box::new(Expr::const_str("Nat")),
            location: None,
        };
        let msg = err.to_string();
        assert!(msg.contains("(head: Nat)"), "got: {msg}");
    }

    /// The defect this exists for: a mismatch whose two sides print the same.
    ///
    /// `Display for Expr` omits universe levels, so `LE2.{u} x` and `LE2.{v} x`
    /// both render `LE2 x`. Measured on real Mathlib source, the message read
    /// `Kernel check failed: expected LE2 fvar#4, got LE2 fvar#4` — a checker
    /// telling a user that two identical things differ.
    #[test]
    fn test_type_mismatch_that_prints_identically_names_the_universe_difference() {
        let u = crate::Level::param(Name::from_string("u"));
        let v = crate::Level::param(Name::from_string("v"));
        let expected = Expr::const_(Name::from_string("LE2"), vec![u]);
        let inferred = Expr::const_(Name::from_string("LE2"), vec![v]);

        // Precondition of the whole fix: the two sides ARE indistinguishable
        // through the ordinary printer. If this ever stops holding, the
        // disambiguation below is dead code and should be reconsidered.
        assert_eq!(
            expected.to_string(),
            inferred.to_string(),
            "the printer is expected to collide here; that collision is the defect"
        );

        let err = TypeError::TypeMismatch {
            expected: Box::new(expected),
            inferred: Box::new(inferred),
            location: None,
        };
        let msg = err.to_string();
        assert!(
            msg.contains("both sides print identically"),
            "the message must admit the collision, got: {msg}"
        );
        assert!(
            msg.contains("universe levels"),
            "and name what actually differs, got: {msg}"
        );
        assert!(msg.contains('u') && msg.contains('v'), "got: {msg}");
    }

    /// An ordinary mismatch gains NOTHING. The disambiguation is for the
    /// collision only; paying for it on every message would be the wrong trade.
    #[test]
    fn test_an_ordinary_type_mismatch_is_unchanged() {
        let err = TypeError::TypeMismatch {
            expected: Box::new(Expr::const_(Name::from_string("Nat"), vec![])),
            inferred: Box::new(Expr::const_(Name::from_string("Int"), vec![])),
            location: None,
        };
        let msg = err.to_string();
        assert!(msg.contains("expected Nat, got Int"), "got: {msg}");
        assert!(
            !msg.contains("both sides print identically"),
            "no disambiguation when the sides already differ, got: {msg}"
        );
    }

    /// Colliding sides with EQUAL levels still get an honest sentence rather
    /// than silence — the reader is told to stop looking for a typo.
    #[test]
    fn test_identical_print_with_equal_levels_says_where_the_difference_is_not() {
        let a = Expr::fvar(FVarId::new(4));
        let err = TypeError::TypeMismatch {
            expected: Box::new(a.clone()),
            inferred: Box::new(a),
            location: None,
        };
        let msg = err.to_string();
        assert!(msg.contains("same universe levels"), "got: {msg}");
    }
}
